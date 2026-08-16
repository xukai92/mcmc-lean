import Mcmc.Kernel.CoupledChain

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

end Mcmc.Kernel
