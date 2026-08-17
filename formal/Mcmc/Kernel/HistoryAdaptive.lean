import Mcmc.Kernel.NonhomogeneousDoeblin

/-!
# General-state history-dependent adaptive paths

This module gives an Ionescu--Tulcea semantics to an adaptive kernel choice
that may inspect the entire finite history available at the current time.
Unlike the elementary finite adaptive layer, the memory is not encoded in a
fixed finite parameter type.  Correctness or convergence of a particular
adaptation rule still requires separate diminishing-adaptation and containment
arguments.
-/

open MeasureTheory
open scoped ProbabilityTheory

namespace Mcmc.Kernel

open ProbabilityTheory

variable {State Parameter : Type*}
  [MeasurableSpace State] [MeasurableSpace Parameter]

/-! ### Eventwise approximation of general-state laws -/

/-- Two finite measures are eventwise within `error` when each measurable-event
mass is bounded by the other plus `error`.  This is the form of total-variation
control needed by the Roberts--Rosenthal finite-window argument, without a
finite-state sum or a choice of density. -/
def EventwiseWithin (first second : Measure State) (error : ENNReal) : Prop :=
  ∀ event, MeasurableSet event →
    first event ≤ second event + error ∧
      second event ≤ first event + error

theorem eventwiseWithin_refl (law : Measure State) :
    EventwiseWithin law law 0 := by
  intro event _hevent
  simp

theorem EventwiseWithin.symm {first second : Measure State} {error : ENNReal}
    (h : EventwiseWithin first second error) :
    EventwiseWithin second first error := by
  intro event hevent
  exact (h event hevent).symm

/-- Eventwise errors compose additively. This is the measure-level triangle
step used to compare an adaptive window first with its frozen proxy and then
with the target. -/
theorem EventwiseWithin.trans {first second third : Measure State}
    {firstError secondError : ENNReal}
    (hfirst : EventwiseWithin first second firstError)
    (hsecond : EventwiseWithin second third secondError) :
    EventwiseWithin first third (firstError + secondError) := by
  intro event hevent
  constructor
  · calc
      first event ≤ second event + firstError := (hfirst event hevent).1
      _ ≤ (third event + secondError) + firstError := by
        gcongr
        exact (hsecond event hevent).1
      _ = third event + (firstError + secondError) := by
        ac_rfl
  · calc
      third event ≤ second event + secondError := (hsecond event hevent).2
      _ ≤ (first event + firstError) + secondError := by
        gcongr
        exact (hfirst event hevent).2
      _ = first event + (firstError + secondError) := by
        ac_rfl

/-- A vanishing uniform eventwise error implies setwise convergence.  This is
the general-state replacement for the final finite sum in the finite adaptive
proof. -/
theorem tendsto_apply_of_eventwiseWithin_tendsto_zero
    (laws : ℕ → Measure State) (target : Measure State)
    [IsFiniteMeasure target] (error : ℕ → ENNReal)
    (herror : Filter.Tendsto error Filter.atTop (nhds 0))
    (hwithin : ∀ n, EventwiseWithin (laws n) target (error n))
    {event : Set State} (hevent : MeasurableSet event) :
    Filter.Tendsto (fun n ↦ laws n event) Filter.atTop
      (nhds (target event)) := by
  have hlower : Filter.Tendsto (fun n ↦ target event - error n)
      Filter.atTop (nhds (target event)) := by
    have h := ENNReal.Tendsto.sub tendsto_const_nhds herror
      (Or.inl (measure_ne_top target event))
    simpa only [tsub_zero] using h
  have hupper : Filter.Tendsto (fun n ↦ target event + error n)
      Filter.atTop (nhds (target event)) := by
    simpa only [add_zero] using tendsto_const_nhds.add herror
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hupper
  · intro n
    rw [tsub_le_iff_right]
    exact (hwithin n event hevent).2
  · intro n
    exact (hwithin n event hevent).1

/-- A proxy-law certificate packages the two quantitative inputs in an
indefinite-adaptation proof: the actual marginal is close to a frozen-window
proxy, and that proxy is close to the target.  Both errors must vanish along
the selected sequence of windows. -/
structure ProxyConvergenceCertificate (laws : ℕ → Measure State)
    (target : Measure State) where
  proxy : ℕ → Measure State
  approximationError : ℕ → ENNReal
  containmentError : ℕ → ENNReal
  approximationError_tendsto :
    Filter.Tendsto approximationError Filter.atTop (nhds 0)
  containmentError_tendsto :
    Filter.Tendsto containmentError Filter.atTop (nhds 0)
  approximation : ∀ n,
    EventwiseWithin (laws n) (proxy n) (approximationError n)
  containment : ∀ n,
    EventwiseWithin (proxy n) target (containmentError n)

/-- Proxy convergence transfers to the actual laws by the eventwise triangle
inequality.  Algorithm-specific Diminishing Adaptation must construct
`approximation`; Containment must construct `containment`. -/
theorem ProxyConvergenceCertificate.tendsto_apply
    {laws : ℕ → Measure State} {target : Measure State}
    [IsFiniteMeasure target]
    (certificate : ProxyConvergenceCertificate laws target)
    {event : Set State} (hevent : MeasurableSet event) :
    Filter.Tendsto (fun n ↦ laws n event) Filter.atTop
      (nhds (target event)) := by
  refine tendsto_apply_of_eventwiseWithin_tendsto_zero laws target
    (fun n ↦ certificate.approximationError n +
      certificate.containmentError n) ?_ ?_ hevent
  · simpa only [zero_add] using
      certificate.approximationError_tendsto.add
        certificate.containmentError_tendsto
  · intro n
    exact (certificate.approximation n).trans (certificate.containment n)

/-- A Markov-kernel family together with a measurable parameter selection rule
that may depend on the complete history through time `n`. -/
structure HistoryAdaptiveFamily (State Parameter : Type*)
    [MeasurableSpace State] [MeasurableSpace Parameter] where
  family : ProbabilityTheory.Kernel (State × Parameter) State
  isMarkov : IsMarkovKernel family := by infer_instance
  select : ∀ n : ℕ, ((i : Finset.Iic n) → State) → Parameter
  measurable_select : ∀ n : ℕ, Measurable (select n)

attribute [instance] HistoryAdaptiveFamily.isMarkov

/-- The next-state kernel selected from the complete current history. -/
noncomputable def HistoryAdaptiveFamily.next
    (adaptive : HistoryAdaptiveFamily (State := State) (Parameter := Parameter))
    (n : ℕ) :
    ProbabilityTheory.Kernel ((i : Finset.Iic n) → State) State :=
  adaptive.family.comap
    (fun history => (terminalHistory n history, adaptive.select n history))
    ((measurable_terminalHistory n).prodMk (adaptive.measurable_select n))

instance HistoryAdaptiveFamily.next.instIsMarkovKernel
    (adaptive : HistoryAdaptiveFamily (State := State) (Parameter := Parameter))
    (n : ℕ) : IsMarkovKernel (adaptive.next n) := by
  unfold HistoryAdaptiveFamily.next
  infer_instance

/-- Infinite path kernel of a fully history-dependent adaptive rule,
conditional on its time-zero state. -/
noncomputable def HistoryAdaptiveFamily.pathKernel
    (adaptive : HistoryAdaptiveFamily (State := State) (Parameter := Parameter)) :
    ProbabilityTheory.Kernel State (ℕ → State) := by
  letI : ∀ n, IsMarkovKernel (adaptive.next n) := fun n =>
    HistoryAdaptiveFamily.next.instIsMarkovKernel adaptive n
  exact (ProbabilityTheory.Kernel.traj adaptive.next 0).comap
    initialHistory measurable_initialHistory

instance HistoryAdaptiveFamily.pathKernel.instIsMarkovKernel
    (adaptive : HistoryAdaptiveFamily (State := State) (Parameter := Parameter)) :
    IsMarkovKernel adaptive.pathKernel := by
  unfold HistoryAdaptiveFamily.pathKernel
  infer_instance

/-- Adaptive path law obtained from an initial state distribution. -/
noncomputable def HistoryAdaptiveFamily.pathLaw
    (adaptive : HistoryAdaptiveFamily (State := State) (Parameter := Parameter))
    (initial : Measure State) : Measure (ℕ → State) :=
  adaptive.pathKernel ∘ₘ initial

instance HistoryAdaptiveFamily.pathLaw.instIsProbabilityMeasure
    (adaptive : HistoryAdaptiveFamily (State := State) (Parameter := Parameter))
    (initial : Measure State) [IsProbabilityMeasure initial] :
    IsProbabilityMeasure (adaptive.pathLaw initial) := by
  unfold HistoryAdaptiveFamily.pathLaw
  infer_instance

/-- The finite-time adaptive state kernel, obtained by projecting the finite
Ionescu--Tulcea history onto its terminal coordinate. -/
noncomputable def HistoryAdaptiveFamily.stateKernel
    (adaptive : HistoryAdaptiveFamily (State := State) (Parameter := Parameter))
    (n : ℕ) : ProbabilityTheory.Kernel State State := by
  letI : ∀ k, IsMarkovKernel (adaptive.next k) := fun k =>
    HistoryAdaptiveFamily.next.instIsMarkovKernel adaptive k
  exact ((ProbabilityTheory.Kernel.partialTraj (X := fun _ => State)
        adaptive.next 0 n).map (terminalHistory (α := State) n)).comap
      (initialHistory (α := State)) measurable_initialHistory

instance HistoryAdaptiveFamily.stateKernel.instIsMarkovKernel
    (adaptive : HistoryAdaptiveFamily (State := State) (Parameter := Parameter))
    (n : ℕ) : IsMarkovKernel (adaptive.stateKernel n) := by
  letI : ∀ k, IsMarkovKernel (adaptive.next k) := fun k =>
    HistoryAdaptiveFamily.next.instIsMarkovKernel adaptive k
  unfold HistoryAdaptiveFamily.stateKernel
  let finitePath := ProbabilityTheory.Kernel.partialTraj
    (X := fun _ => State) adaptive.next 0 n
  haveI : IsMarkovKernel finitePath := by
    dsimp [finitePath]
    infer_instance
  haveI : IsMarkovKernel (finitePath.map (terminalHistory (α := State) n)) := by
    exact ProbabilityTheory.Kernel.IsMarkovKernel.map finitePath
      (measurable_terminalHistory n)
  infer_instance

/-- The sequence of actual state marginals of a history-adaptive process
started from a point.  This abbreviation prevents an adaptive convergence
certificate from being stated accidentally for an unrelated proxy chain. -/
noncomputable def HistoryAdaptiveFamily.stateLaws
    (adaptive : HistoryAdaptiveFamily (State := State) (Parameter := Parameter))
    (initial : State) : ℕ → Measure State :=
  fun n ↦ adaptive.stateKernel n initial

instance HistoryAdaptiveFamily.stateLaws.instIsProbabilityMeasure
    (adaptive : HistoryAdaptiveFamily (State := State) (Parameter := Parameter))
    (initial : State) (n : ℕ) :
    IsProbabilityMeasure (adaptive.stateLaws initial n) := by
  unfold HistoryAdaptiveFamily.stateLaws
  infer_instance

/-- A vanishing frozen-window approximation and containment certificate for
the *actual* history-adaptive marginals implies setwise convergence from the
specified initial state.  This is the general-state Roberts--Rosenthal closure
step; constructing the certificate remains algorithm-specific. -/
theorem HistoryAdaptiveFamily.stateKernel_apply_tendsto_of_proxyCertificate
    (adaptive : HistoryAdaptiveFamily (State := State) (Parameter := Parameter))
    (initial : State) (target : Measure State) [IsProbabilityMeasure target]
    (certificate : ProxyConvergenceCertificate
      (adaptive.stateLaws initial) target)
    {event : Set State} (hevent : MeasurableSet event) :
    Filter.Tendsto (fun n ↦ adaptive.stateKernel n initial event)
      Filter.atTop (nhds (target event)) := by
  exact certificate.tendsto_apply hevent

@[simp] theorem HistoryAdaptiveFamily.stateKernel_zero
    (adaptive : HistoryAdaptiveFamily (State := State) (Parameter := Parameter)) :
    adaptive.stateKernel 0 = ProbabilityTheory.Kernel.id := by
  rw [HistoryAdaptiveFamily.stateKernel,
    ProbabilityTheory.Kernel.partialTraj_zero]
  ext x s hs
  rw [ProbabilityTheory.Kernel.comap_apply,
    ProbabilityTheory.Kernel.map_apply _ (measurable_terminalHistory 0),
    ProbabilityTheory.Kernel.deterministic_apply,
    Measure.map_dirac' (measurable_terminalHistory 0),
    ProbabilityTheory.Kernel.id_apply]
  rfl

/-- The actual transition selected from the time-zero history. -/
noncomputable def HistoryAdaptiveFamily.initialKernel
    (adaptive : HistoryAdaptiveFamily (State := State) (Parameter := Parameter)) :
    ProbabilityTheory.Kernel State State :=
  (adaptive.next 0).comap initialHistory measurable_initialHistory

instance HistoryAdaptiveFamily.initialKernel.instIsMarkovKernel
    (adaptive : HistoryAdaptiveFamily (State := State) (Parameter := Parameter)) :
    IsMarkovKernel adaptive.initialKernel := by
  unfold HistoryAdaptiveFamily.initialKernel
  infer_instance

/-- Expanded form of the initial selected kernel: retain the current state and
pair it with the parameter chosen from its singleton history. -/
theorem HistoryAdaptiveFamily.initialKernel_eq_family_comap
    (adaptive : HistoryAdaptiveFamily (State := State) (Parameter := Parameter)) :
    adaptive.initialKernel = adaptive.family.comap
      (fun state => (state, adaptive.select 0 (initialHistory state)))
      (measurable_id.prodMk
        ((adaptive.measurable_select 0).comp measurable_initialHistory)) := by
  ext state event hevent
  simp [HistoryAdaptiveFamily.initialKernel, HistoryAdaptiveFamily.next,
    ProbabilityTheory.Kernel.comap_apply]
  rfl

/-- The first nontrivial adaptive marginal is exactly the kernel chosen from
the initial history; this checks the Ionescu--Tulcea stage indexing. -/
@[simp] theorem HistoryAdaptiveFamily.stateKernel_one
    (adaptive : HistoryAdaptiveFamily (State := State) (Parameter := Parameter)) :
    adaptive.stateKernel 1 = adaptive.initialKernel := by
  letI : ∀ k, IsMarkovKernel (adaptive.next k) := fun k =>
    HistoryAdaptiveFamily.next.instIsMarkovKernel adaptive k
  rw [HistoryAdaptiveFamily.stateKernel]
  change (((ProbabilityTheory.Kernel.partialTraj (X := fun _ => State)
    adaptive.next 0 (0 + 1)).map
    (fun history => history
      (⟨0 + 1, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic (0 + 1)))).comap
        initialHistory measurable_initialHistory) = adaptive.initialKernel
  rw [ProbabilityTheory.Kernel.map_partialTraj_succ_self]
  rfl

/-- If the transition selected at stage `n` depends only on the terminal state,
then the adaptive marginal obeys the ordinary one-step Markov recurrence at
that stage. This is deliberately a local statement: without `hnext`, a
history-dependent marginal does not have a state-only recurrence. -/
theorem HistoryAdaptiveFamily.stateKernel_succ_of_next_eq
    (adaptive : HistoryAdaptiveFamily (State := State) (Parameter := Parameter))
    (transition : ProbabilityTheory.Kernel State State)
    [IsMarkovKernel transition] (n : ℕ)
    (hnext : adaptive.next n = homogeneousNext transition n) :
    adaptive.stateKernel (n + 1) =
      transition ∘ₖ adaptive.stateKernel n := by
  letI : ∀ k, IsMarkovKernel (adaptive.next k) := fun k =>
    HistoryAdaptiveFamily.next.instIsMarkovKernel adaptive k
  rw [HistoryAdaptiveFamily.stateKernel,
    ProbabilityTheory.Kernel.partialTraj_succ_eq_comp (Nat.zero_le n),
    ProbabilityTheory.Kernel.map_comp]
  change
    (((ProbabilityTheory.Kernel.partialTraj (X := fun _ => State)
      adaptive.next n (n + 1)).map
        (fun x => x ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩) ∘ₖ
      ProbabilityTheory.Kernel.partialTraj (X := fun _ => State)
        adaptive.next 0 n).comap
        (initialHistory (α := State)) measurable_initialHistory) = _
  rw [ProbabilityTheory.Kernel.map_partialTraj_succ_self]
  ext state event hevent
  simp only [ProbabilityTheory.Kernel.comap_apply,
    ProbabilityTheory.Kernel.comp_apply' _ _ _ hevent]
  rw [HistoryAdaptiveFamily.stateKernel,
    ProbabilityTheory.Kernel.comap_apply,
    ProbabilityTheory.Kernel.map_apply _ (measurable_terminalHistory n),
    MeasureTheory.lintegral_map
      (ProbabilityTheory.Kernel.measurable_coe transition hevent)
      (measurable_terminalHistory n)]
  rw [hnext]
  simp only [homogeneousNext, ProbabilityTheory.Kernel.comap_apply,
    terminalHistory]

/-- If every selected transition is a predetermined state-only kernel, the
actual history-adaptive marginal is exactly the corresponding nonhomogeneous
scheduled law. The schedule may still change at every time. -/
theorem HistoryAdaptiveFamily.stateKernel_eq_scheduledLaw
    (adaptive : HistoryAdaptiveFamily (State := State) (Parameter := Parameter))
    (schedule : ℕ → ProbabilityTheory.Kernel State State)
    [∀ n, IsMarkovKernel (schedule n)]
    (hnext : ∀ n, adaptive.next n = homogeneousNext (schedule n) n)
    (initial : State) (n : ℕ) :
    adaptive.stateKernel n initial =
      scheduledLaw (Measure.dirac initial) schedule n := by
  induction n with
  | zero =>
      rw [adaptive.stateKernel_zero, scheduledLaw_zero,
        ProbabilityTheory.Kernel.id_apply]
  | succ n ih =>
      rw [adaptive.stateKernel_succ_of_next_eq (schedule n) n (hnext n),
        scheduledLaw_succ]
      change schedule n ∘ₘ adaptive.stateKernel n initial = _
      rw [ih]

/-- A predetermined but indefinitely changing history-adaptive schedule
converges setwise whenever all scheduled kernels preserve one probability
target and share one positive Doeblin component. This is a concrete
general-state indefinite-adaptation theorem; state- or history-dependent
parameter updates require the separate proxy-certificate route. -/
theorem HistoryAdaptiveFamily.stateKernel_apply_tendsto_of_predetermined_doeblin
    (adaptive : HistoryAdaptiveFamily (State := State) (Parameter := Parameter))
    (schedule : ℕ → ProbabilityTheory.Kernel State State)
    [∀ n, IsMarkovKernel (schedule n)]
    (hnext : ∀ n, adaptive.next n = homogeneousNext (schedule n) n)
    (target : Measure State) [IsProbabilityMeasure target]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1) (hεpos : 0 < ε.1)
    (hminor : ∀ n, UniformlyMinorizes (schedule n) ε.1 target)
    (hinvariant : ∀ n, (schedule n).Invariant target)
    (initial : State) {event : Set State} (hevent : MeasurableSet event) :
    Filter.Tendsto (fun n ↦ adaptive.stateKernel n initial event)
      Filter.atTop (nhds (target event)) := by
  have heq : (fun n ↦ adaptive.stateKernel n initial event) =
      fun n ↦ scheduledLaw (Measure.dirac initial) schedule n event := by
    funext n
    rw [adaptive.stateKernel_eq_scheduledLaw schedule hnext initial n]
  rw [heq]
  exact scheduledLaw_apply_tendsto_of_uniformMinorization
    (Measure.dirac initial) target schedule ε hε hεpos hminor hinvariant hevent

/-- The finite state kernel is exactly the corresponding coordinate marginal
of the infinite adaptive path kernel. No homogeneous Markov recurrence is
asserted: after marginalizing the history, the selected kernel generally
cannot be recovered from the current state alone. -/
theorem HistoryAdaptiveFamily.pathKernel_map_atTime
    (adaptive : HistoryAdaptiveFamily (State := State) (Parameter := Parameter))
    (n : ℕ) :
    adaptive.pathKernel.map (fun path => path n) = adaptive.stateKernel n := by
  letI : ∀ k, IsMarkovKernel (adaptive.next k) := fun k =>
    HistoryAdaptiveFamily.next.instIsMarkovKernel adaptive k
  rw [HistoryAdaptiveFamily.pathKernel]
  rw [← ProbabilityTheory.Kernel.comap_map_comm _ measurable_initialHistory
    (measurable_pi_apply n)]
  have heval : (fun path : ℕ → State => path n) =
      terminalHistory n ∘ Preorder.frestrictLe n := rfl
  rw [heval, ProbabilityTheory.Kernel.map_comp_right _
    (Preorder.measurable_frestrictLe n) (measurable_terminalHistory n),
    ProbabilityTheory.Kernel.traj_map_frestrictLe]
  rfl

/-! ### Conservativity for constant parameter selection -/

/-- Fixed-parameter section of a measurable parameterized kernel. -/
noncomputable def fixedParameterSection
    (family : ProbabilityTheory.Kernel (State × Parameter) State)
    (parameter : Parameter) : ProbabilityTheory.Kernel State State :=
  family.comap (fun state => (state, parameter))
    (measurable_id.prodMk measurable_const)

instance fixedParameterSection.instIsMarkovKernel
    (family : ProbabilityTheory.Kernel (State × Parameter) State)
    [IsMarkovKernel family] (parameter : Parameter) :
    IsMarkovKernel (fixedParameterSection family parameter) := by
  unfold fixedParameterSection
  infer_instance

/-- Regard constant parameter selection as a history-adaptive family. -/
noncomputable def HistoryAdaptiveFamily.constant
    (family : ProbabilityTheory.Kernel (State × Parameter) State)
    [IsMarkovKernel family] (parameter : Parameter) :
    HistoryAdaptiveFamily State Parameter where
  family := family
  select := fun _ _ => parameter
  measurable_select := fun _ => measurable_const

/-- Constant history selection gives exactly the homogeneous next-step adapter
for the corresponding fixed-parameter kernel. -/
theorem HistoryAdaptiveFamily.constant_next
    (family : ProbabilityTheory.Kernel (State × Parameter) State)
    [IsMarkovKernel family] (parameter : Parameter) (n : ℕ) :
    (HistoryAdaptiveFamily.constant family parameter).next n =
      homogeneousNext (fixedParameterSection family parameter) n := by
  ext history event hevent
  simp [HistoryAdaptiveFamily.next, HistoryAdaptiveFamily.constant,
    homogeneousNext, fixedParameterSection,
    ProbabilityTheory.Kernel.comap_apply]
  rfl

/-- Consequently the infinite adaptive path kernel conservatively extends the
existing homogeneous path-kernel semantics. -/
theorem HistoryAdaptiveFamily.constant_pathKernel
    (family : ProbabilityTheory.Kernel (State × Parameter) State)
    [IsMarkovKernel family] (parameter : Parameter) :
    (HistoryAdaptiveFamily.constant family parameter).pathKernel =
      Mcmc.Kernel.pathKernel (fixedParameterSection family parameter) := by
  have hnext : (HistoryAdaptiveFamily.constant family parameter).next =
      homogeneousNext (fixedParameterSection family parameter) := by
    funext n
    exact HistoryAdaptiveFamily.constant_next family parameter n
  unfold HistoryAdaptiveFamily.pathKernel Mcmc.Kernel.pathKernel
  cases hnext
  rfl

/-- Constant selection also reduces every finite-time adaptive marginal to
the ordinary power of the fixed-parameter transition kernel. -/
theorem HistoryAdaptiveFamily.constant_stateKernel
    (family : ProbabilityTheory.Kernel (State × Parameter) State)
    [IsMarkovKernel family] (parameter : Parameter) (n : ℕ) :
    (HistoryAdaptiveFamily.constant family parameter).stateKernel n =
      fixedParameterSection family parameter ^ n := by
  rw [← HistoryAdaptiveFamily.pathKernel_map_atTime,
    HistoryAdaptiveFamily.constant_pathKernel,
    Mcmc.Kernel.pathKernel_map_atTime]

/-! ### Eventually frozen adaptation -/

/-- A history-dependent rule freezes after `burnIn` when it selects one fixed
parameter at every later stage, for every possible history. -/
def HistoryAdaptiveFamily.FreezesAfter
    (adaptive : HistoryAdaptiveFamily (State := State) (Parameter := Parameter))
    (burnIn : ℕ) (parameter : Parameter) : Prop :=
  ∀ n, burnIn ≤ n → ∀ history, adaptive.select n history = parameter

/-- After freezing, the selected history kernel is exactly the homogeneous
fixed-parameter adapter. -/
theorem HistoryAdaptiveFamily.next_eq_homogeneous_of_freezesAfter
    (adaptive : HistoryAdaptiveFamily (State := State) (Parameter := Parameter))
    (burnIn : ℕ) (parameter : Parameter)
    (hfreeze : adaptive.FreezesAfter burnIn parameter)
    (n : ℕ) (hn : burnIn ≤ n) :
    adaptive.next n = homogeneousNext
      (fixedParameterSection adaptive.family parameter) n := by
  ext history event hevent
  simp [HistoryAdaptiveFamily.next, homogeneousNext, fixedParameterSection,
    terminalHistory,
    ProbabilityTheory.Kernel.comap_apply, hfreeze n hn history]

/-- Every post-freeze marginal obeys the fixed-parameter Markov recurrence. -/
theorem HistoryAdaptiveFamily.stateKernel_succ_of_freezesAfter
    (adaptive : HistoryAdaptiveFamily (State := State) (Parameter := Parameter))
    (burnIn : ℕ) (parameter : Parameter)
    (hfreeze : adaptive.FreezesAfter burnIn parameter)
    (n : ℕ) (hn : burnIn ≤ n) :
    adaptive.stateKernel (n + 1) =
      fixedParameterSection adaptive.family parameter ∘ₖ
        adaptive.stateKernel n := by
  apply adaptive.stateKernel_succ_of_next_eq
  exact adaptive.next_eq_homogeneous_of_freezesAfter burnIn parameter
    hfreeze n hn

/-- Exact frozen-tail factorization: after an arbitrary adaptive burn-in, the
next `steps` transitions are the ordinary power of the frozen kernel applied
to the burn-in marginal. This is the general-state bridge allowing any
homogeneous convergence theorem to be reused after finite adaptation. -/
theorem HistoryAdaptiveFamily.stateKernel_add_eq_pow_comp_of_freezesAfter
    (adaptive : HistoryAdaptiveFamily (State := State) (Parameter := Parameter))
    (burnIn : ℕ) (parameter : Parameter)
    (hfreeze : adaptive.FreezesAfter burnIn parameter)
    (steps : ℕ) :
    adaptive.stateKernel (burnIn + steps) =
      ((fixedParameterSection adaptive.family parameter) ^ steps) ∘ₖ
        adaptive.stateKernel burnIn := by
  induction steps with
  | zero =>
      rw [Nat.add_zero, pow_zero]
      exact (ProbabilityTheory.Kernel.id_comp _).symm
  | succ steps ih =>
      rw [Nat.add_succ,
        adaptive.stateKernel_succ_of_freezesAfter burnIn parameter hfreeze
          (burnIn + steps) (Nat.le_add_right burnIn steps),
        ih]
      change fixedParameterSection adaptive.family parameter *
          ((fixedParameterSection adaptive.family parameter) ^ steps *
            adaptive.stateKernel burnIn) = _
      rw [← mul_assoc, pow_succ']
      rfl

/-- A frozen adaptive tail inherits the upper eventwise Doeblin bound of its
fixed-parameter kernel. The initial law in the homogeneous theorem is exactly
the possibly complicated adaptive burn-in marginal. -/
theorem HistoryAdaptiveFamily.stateKernel_apply_le_target_add_geometric_of_freezesAfter
    (adaptive : HistoryAdaptiveFamily (State := State) (Parameter := Parameter))
    (burnIn : ℕ) (parameter : Parameter)
    (hfreeze : adaptive.FreezesAfter burnIn parameter)
    (target : Measure State) [IsProbabilityMeasure target]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hminor : UniformlyMinorizes
      (fixedParameterSection adaptive.family parameter) ε.1 target)
    (hinvariant : (fixedParameterSection adaptive.family parameter).Invariant
      target)
    (initial : State) (steps : ℕ) {event : Set State}
    (hevent : MeasurableSet event) :
    adaptive.stateKernel (burnIn + steps) initial event ≤
      target event + (((1 - ε.1) ^ steps : NNReal) : ENNReal) := by
  let transition := fixedParameterSection adaptive.family parameter
  have heq : adaptive.stateKernel (burnIn + steps) initial =
      lawAtTime (adaptive.stateKernel burnIn initial) transition steps := by
    rw [adaptive.stateKernel_add_eq_pow_comp_of_freezesAfter burnIn parameter
      hfreeze steps]
    rfl
  rw [heq]
  exact lawAtTime_apply_le_target_add_geometric transition target
    (adaptive.stateKernel burnIn initial) ε hε hminor hinvariant steps hevent

/-- Symmetric half of the frozen-tail eventwise Doeblin bound. Together with
the preceding theorem this is an explicit total-variation-style convergence
certificate after finite adaptation. -/
theorem HistoryAdaptiveFamily.target_apply_le_stateKernel_add_geometric_of_freezesAfter
    (adaptive : HistoryAdaptiveFamily (State := State) (Parameter := Parameter))
    (burnIn : ℕ) (parameter : Parameter)
    (hfreeze : adaptive.FreezesAfter burnIn parameter)
    (target : Measure State) [IsProbabilityMeasure target]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hminor : UniformlyMinorizes
      (fixedParameterSection adaptive.family parameter) ε.1 target)
    (hinvariant : (fixedParameterSection adaptive.family parameter).Invariant
      target)
    (initial : State) (steps : ℕ) {event : Set State}
    (hevent : MeasurableSet event) :
    target event ≤ adaptive.stateKernel (burnIn + steps) initial event +
      (((1 - ε.1) ^ steps : NNReal) : ENNReal) := by
  let transition := fixedParameterSection adaptive.family parameter
  have heq : adaptive.stateKernel (burnIn + steps) initial =
      lawAtTime (adaptive.stateKernel burnIn initial) transition steps := by
    rw [adaptive.stateKernel_add_eq_pow_comp_of_freezesAfter burnIn parameter
      hfreeze steps]
    rfl
  rw [heq]
  exact target_apply_le_lawAtTime_add_geometric transition target
    (adaptive.stateKernel burnIn initial) ε hε hminor hinvariant steps hevent

/-- Arbitrary history-dependent warmup followed by a uniformly minorized
frozen kernel canonically supplies the proxy/containment certificate used by
the general indefinite-adaptation interface. The proxy is the exact frozen
tail law, so its approximation error is zero; containment is the geometric
Doeblin bound. -/
noncomputable def HistoryAdaptiveFamily.proxyCertificate_of_freezesAfter
    (adaptive : HistoryAdaptiveFamily (State := State) (Parameter := Parameter))
    (burnIn : ℕ) (parameter : Parameter)
    (hfreeze : adaptive.FreezesAfter burnIn parameter)
    (target : Measure State) [IsProbabilityMeasure target]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1) (hεpos : 0 < ε.1)
    (hminor : UniformlyMinorizes
      (fixedParameterSection adaptive.family parameter) ε.1 target)
    (hinvariant : (fixedParameterSection adaptive.family parameter).Invariant
      target)
    (initial : State) :
    ProxyConvergenceCertificate
      (fun steps => adaptive.stateKernel (burnIn + steps) initial) target where
  proxy steps := adaptive.stateKernel (burnIn + steps) initial
  approximationError _ := 0
  containmentError steps := (((1 - ε.1) ^ steps : NNReal) : ENNReal)
  approximationError_tendsto := tendsto_const_nhds
  containmentError_tendsto := by
    have hrateNN : 1 - ε.1 < 1 := tsub_lt_self (by simp) hεpos
    have hrate : ((1 - ε.1 : NNReal) : ENNReal) < 1 := by
      exact_mod_cast hrateNN
    simpa only [ENNReal.coe_pow] using
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hrate
  approximation _ := eventwiseWithin_refl _
  containment steps event hevent := by
    exact ⟨
      adaptive.stateKernel_apply_le_target_add_geometric_of_freezesAfter
        burnIn parameter hfreeze target ε hε hminor hinvariant initial steps
        hevent,
      adaptive.target_apply_le_stateKernel_add_geometric_of_freezesAfter
        burnIn parameter hfreeze target ε hε hminor hinvariant initial steps
        hevent⟩

/-- Finite adaptation followed by a genuinely minorized frozen kernel
converges setwise to the frozen kernel's invariant target. This is a concrete
general-state adaptive convergence theorem, with arbitrary history dependence
allowed before `burnIn`. -/
theorem HistoryAdaptiveFamily.stateKernel_apply_tendsto_of_freezesAfter
    (adaptive : HistoryAdaptiveFamily (State := State) (Parameter := Parameter))
    (burnIn : ℕ) (parameter : Parameter)
    (hfreeze : adaptive.FreezesAfter burnIn parameter)
    (target : Measure State) [IsProbabilityMeasure target]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1) (hεpos : 0 < ε.1)
    (hminor : UniformlyMinorizes
      (fixedParameterSection adaptive.family parameter) ε.1 target)
    (hinvariant : (fixedParameterSection adaptive.family parameter).Invariant
      target)
    (initial : State) {event : Set State} (hevent : MeasurableSet event) :
    Filter.Tendsto
      (fun steps => adaptive.stateKernel (burnIn + steps) initial event)
      Filter.atTop (nhds (target event)) := by
  exact (adaptive.proxyCertificate_of_freezesAfter burnIn parameter hfreeze
    target ε hε hεpos hminor hinvariant initial).tendsto_apply hevent

end Mcmc.Kernel
