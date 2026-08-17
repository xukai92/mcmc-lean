import Mcmc.PDMP.EventSimulation
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Independence.InfinitePi

/-!
# Exact inverse-integrated-hazard event construction

Unbounded PDMP rates cannot use one global homogeneous thinning clock. This
module gives the alternative exact event-skeleton interface: draw a unit
exponential hazard mark, invert the accumulated state-dependent rate along the
flow, move to that time, and apply the event kernel. Horizon stopping and
nonexplosion remain explicit additional obligations.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace Mcmc.PDMP

variable {State : Type*} [MeasurableSpace State]

/-- Canonical unit-exponential law for integrated hazard marks. -/
noncomputable def unitHazardMeasure : Measure NNReal :=
  (HomogeneousClock.mk 1 zero_lt_one).waitMeasure

instance unitHazardMeasure.instIsProbabilityMeasure :
    IsProbabilityMeasure unitHazardMeasure := by
  unfold unitHazardMeasure
  infer_instance

/-- Distribution function of the canonical unit-exponential hazard law. -/
theorem unitHazardMeasure_Iic (elapsed : NNReal) :
    unitHazardMeasure (Set.Iic elapsed) =
      ENNReal.ofReal (1 - Real.exp (-(elapsed : ℝ))) := by
  unfold unitHazardMeasure HomogeneousClock.waitMeasure
  change (Measure.map Real.toNNReal (expMeasure (1 : ℝ)))
    (Set.Iic elapsed) = _
  rw [Measure.map_apply measurable_real_toNNReal measurableSet_Iic]
  have hpre : Real.toNNReal ⁻¹' (Set.Iic elapsed : Set NNReal) =
      Set.Iic (elapsed : ℝ) := by
    ext value
    simp only [Set.mem_preimage, Set.mem_Iic,
      Real.toNNReal_le_iff_le_coe]
  rw [hpre]
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  have hcdf := cdf_expMeasure_eq (r := (1 : ℝ)) zero_lt_one (elapsed : ℝ)
  rw [cdf_eq_real] at hcdf
  simp only [NNReal.coe_nonneg, if_pos, one_mul] at hcdf
  apply (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal]
  · exact hcdf
  · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr elapsed.coe_nonneg))

/-- Survival function of the canonical unit-exponential hazard law. -/
theorem unitHazardMeasure_Ioi (elapsed : NNReal) :
    unitHazardMeasure (Set.Ioi elapsed) =
      ENNReal.ofReal (Real.exp (-(elapsed : ℝ))) := by
  rw [← Set.compl_Iic,
    measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ,
    unitHazardMeasure_Iic]
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _
    (sub_nonneg.mpr (Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr elapsed.coe_nonneg)))]
  congr 1
  ring

/-- Unnormalized memorylessness: condition by restriction to marks larger than
`elapsed`, subtract `elapsed`, and recover the original unit-hazard law scaled
by the survival probability. -/
theorem unitHazardMeasure_residual_memoryless (elapsed : NNReal) :
    Measure.map (fun hazard : NNReal => hazard - elapsed)
        (unitHazardMeasure.restrict (Set.Ioi elapsed)) =
      ENNReal.ofReal (Real.exp (-(elapsed : ℝ))) •
        unitHazardMeasure := by
  apply Measure.ext_of_Iic
  intro residual
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic,
    Measure.restrict_apply (measurableSet_Iic.preimage (by fun_prop))]
  have hpre :
      (fun hazard : NNReal => hazard - elapsed) ⁻¹' Set.Iic residual ∩
          Set.Ioi elapsed =
        Set.Ioc elapsed (elapsed + residual) := by
    ext hazard
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_Ioi,
      Set.mem_Ioc]
    rw [tsub_le_iff_right]
    simp [add_comm, and_comm]
  rw [hpre]
  have hsubset : Set.Iic elapsed ⊆ Set.Iic (elapsed + residual) :=
    Set.Iic_subset_Iic.mpr (le_add_right le_rfl)
  rw [show Set.Ioc elapsed (elapsed + residual) =
      Set.Iic (elapsed + residual) \ Set.Iic elapsed by
    ext hazard
    simp]
  rw [measure_sdiff hsubset nullMeasurableSet_Iic (measure_ne_top _ _),
    unitHazardMeasure_Iic, unitHazardMeasure_Iic]
  rw [Measure.smul_apply]
  simp only [smul_eq_mul]
  rw [unitHazardMeasure_Iic]
  have hexp :
      Real.exp (-((elapsed + residual : NNReal) : ℝ)) =
        Real.exp (-(elapsed : ℝ)) * Real.exp (-(residual : ℝ)) := by
    push_cast
    rw [neg_add_rev, Real.exp_add]
    ac_rfl
  have hnonneg : 0 ≤ 1 - Real.exp (-(elapsed : ℝ)) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr elapsed.coe_nonneg))
  rw [← ENNReal.ofReal_sub _ hnonneg, ← ENNReal.ofReal_mul
    (Real.exp_nonneg (-(elapsed : ℝ)))]
  congr 1
  rw [hexp]
  ring

/-- Normalized conditional form of unit-exponential memorylessness. -/
theorem unitHazardMeasure_conditional_residual (elapsed : NNReal) :
    (ENNReal.ofReal (Real.exp (-(elapsed : ℝ))))⁻¹ •
        Measure.map (fun hazard : NNReal => hazard - elapsed)
          (unitHazardMeasure.restrict (Set.Ioi elapsed)) =
      unitHazardMeasure := by
  rw [unitHazardMeasure_residual_memoryless, smul_smul]
  have hne : ENNReal.ofReal (Real.exp (-(elapsed : ℝ))) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  rw [ENNReal.inv_mul_cancel hne ENNReal.ofReal_ne_top, one_smul]

theorem unitHazardMeasure_singleton_zero :
    unitHazardMeasure {0} = 0 := by
  have hset : ({0} : Set NNReal) = Set.Iic 0 := by
    ext hazard
    simp
  rw [hset, unitHazardMeasure_Iic]
  norm_num

theorem unitHazardMeasure_singleton (hazard : NNReal) :
    unitHazardMeasure {hazard} = 0 := by
  by_cases hhazard : hazard = 0
  · subst hazard
    exact unitHazardMeasure_singleton_zero
  · unfold unitHazardMeasure HomogeneousClock.waitMeasure
    change (Measure.map Real.toNNReal (expMeasure (1 : ℝ))) {hazard} = 0
    rw [Measure.map_apply measurable_real_toNNReal
      (measurableSet_singleton hazard)]
    have hpre : Real.toNNReal ⁻¹' ({hazard} : Set NNReal) =
        {((hazard : NNReal) : ℝ)} := by
      ext value
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hvalue
        have hpositive : 0 < value := by
          by_contra hnonpos
          have : Real.toNNReal value = 0 := Real.toNNReal_of_nonpos
            (le_of_not_gt hnonpos)
          rw [hvalue] at this
          exact hhazard this
        have hcoe := congrArg (fun x : NNReal => (x : ℝ)) hvalue
        rw [Real.coe_toNNReal value hpositive.le] at hcoe
        exact hcoe
      · intro hvalue
        subst value
        simp
    rw [hpre]
    unfold expMeasure gammaMeasure
    rw [withDensity_apply _ (measurableSet_singleton _)]
    simp

instance unitHazardMeasure.instNullSingletonClass :
    NullSingletonClass unitHazardMeasure :=
  ⟨unitHazardMeasure_singleton⟩

theorem unitHazardMeasure_positive_ae :
    ∀ᵐ hazard ∂unitHazardMeasure, 0 < hazard := by
  rw [ae_iff]
  have hset : {hazard : NNReal | ¬0 < hazard} = {0} := by
    ext hazard
    simp [pos_iff_ne_zero]
  rw [hset]
  exact unitHazardMeasure_singleton_zero

/-- Proof-bearing inverse clock for a possibly unbounded state-dependent
intensity along a deterministic flow. -/
structure InverseHazardClock (State : Type*) [MeasurableSpace State] where
  semiflow : JointlyMeasurableSemiflow State
  accumulated : State → NNReal → ℝ
  waitingTime : State → NNReal → NNReal
  measurable_waitingTime : Measurable (fun input : State × NNReal =>
    waitingTime input.1 input.2)
  waitingTime_pos : ∀ state {hazard}, 0 < hazard → 0 < waitingTime state hazard
  inverse : ∀ state {hazard}, 0 < hazard →
    accumulated state (waitingTime state hazard) = (hazard : ℝ)

/-- State at the exact candidate event time determined by one hazard mark. -/
noncomputable def InverseHazardClock.eventLocation
    (clock : InverseHazardClock State) (input : State × NNReal) : State :=
  clock.semiflow.flow (clock.waitingTime input.1 input.2) input.1

theorem InverseHazardClock.measurable_eventLocation
    (clock : InverseHazardClock State) : Measurable clock.eventLocation := by
  exact clock.semiflow.jointly_measurable_flow.comp
    (clock.measurable_waitingTime.prodMk measurable_fst)

/-- Draw a unit exponential hazard and flow to its exact inverse-clock event
location. -/
noncomputable def InverseHazardClock.eventLocationKernel
    (clock : InverseHazardClock State) : Kernel State State :=
  Kernel.map
    (Kernel.prod Kernel.id (Kernel.const State unitHazardMeasure))
    (fun input : State × NNReal => clock.eventLocation input)

instance InverseHazardClock.eventLocationKernel.instIsMarkovKernel
    (clock : InverseHazardClock State) :
    IsMarkovKernel clock.eventLocationKernel := by
  unfold InverseHazardClock.eventLocationKernel
  apply Kernel.IsMarkovKernel.map
  exact clock.measurable_eventLocation

/-- One exact unbounded-rate event: invert one exponential hazard along the
flow, then apply the supplied event kernel. -/
noncomputable def InverseHazardClock.eventKernel
    (clock : InverseHazardClock State) (jump : Kernel State State) :
    Kernel State State :=
  jump ∘ₖ clock.eventLocationKernel

instance InverseHazardClock.eventKernel.instIsMarkovKernel
    (clock : InverseHazardClock State) (jump : Kernel State State)
    [IsMarkovKernel jump] : IsMarkovKernel (clock.eventKernel jump) := by
  unfold InverseHazardClock.eventKernel
  infer_instance

/-- A fixed number of exact inverse-clock events forms the ordinary power of
the event kernel. This is the event-skeleton construction; it makes no claim
that a fixed real horizon contains finitely many events. -/
noncomputable def InverseHazardClock.eventIterate
    (clock : InverseHazardClock State) (jump : Kernel State State)
    (events : ℕ) : Kernel State State :=
  (clock.eventKernel jump) ^ events

instance InverseHazardClock.eventIterate.instIsMarkovKernel
    (clock : InverseHazardClock State) (jump : Kernel State State)
    [IsMarkovKernel jump] (events : ℕ) :
    IsMarkovKernel (clock.eventIterate jump events) := by
  unfold InverseHazardClock.eventIterate
  infer_instance

theorem InverseHazardClock.eventIterate_add
    (clock : InverseHazardClock State) (jump : Kernel State State)
    (first second : ℕ) :
    clock.eventIterate jump (first + second) =
      clock.eventIterate jump first ∘ₖ clock.eventIterate jump second := by
  exact Kernel.pow_add (clock.eventKernel jump) first second

/-! ### Clocks with inactive no-event states -/

/-- Partial inverse clock for rates that may never accumulate a positive
hazard, such as BPS at exactly zero velocity. `active = false` is certified by
strict failure to reach the mark at every finite time. -/
structure PartialInverseHazardClock (State : Type*) [MeasurableSpace State] where
  semiflow : JointlyMeasurableSemiflow State
  accumulated : State → NNReal → ℝ
  active : State → NNReal → Bool
  waitingTime : State → NNReal → NNReal
  measurable_active : Measurable (fun input : State × NNReal =>
    active input.1 input.2)
  measurable_waitingTime : Measurable (fun input : State × NNReal =>
    waitingTime input.1 input.2)
  waitingTime_pos : ∀ state {hazard}, 0 < hazard → active state hazard = true →
    0 < waitingTime state hazard
  inverse : ∀ state {hazard}, 0 < hazard → active state hazard = true →
    accumulated state (waitingTime state hazard) = (hazard : ℝ)
  inactive : ∀ state {hazard}, active state hazard = false → ∀ time,
    accumulated state time < (hazard : ℝ)

/-- Execute one partial inverse clock up to a finite horizon. If the mark is
inactive or its event lies beyond the horizon, only the residual deterministic
flow is applied. Otherwise the event map is applied at the exact event time. -/
noncomputable def PartialInverseHazardClock.firstEventUpdate
    (clock : PartialInverseHazardClock State)
    (jump : State → State) (horizon : NNReal)
    (input : State × NNReal) : State :=
  if clock.active input.1 input.2 = true ∧
      clock.waitingTime input.1 input.2 ≤ horizon then
    jump (clock.semiflow.flow (clock.waitingTime input.1 input.2) input.1)
  else
    clock.semiflow.flow horizon input.1

theorem PartialInverseHazardClock.measurable_firstEventUpdate
    (clock : PartialInverseHazardClock State)
    {jump : State → State} (hjump : Measurable jump) (horizon : NNReal) :
    Measurable (clock.firstEventUpdate jump horizon) := by
  unfold PartialInverseHazardClock.firstEventUpdate
  apply Measurable.ite
  · exact (measurableSet_singleton true).preimage clock.measurable_active |>.inter
      (measurableSet_le clock.measurable_waitingTime.coe_nnreal_real
        measurable_const)
  · exact hjump.comp <| clock.semiflow.jointly_measurable_flow.comp
      (clock.measurable_waitingTime.prodMk measurable_fst)
  · exact clock.semiflow.measurable_flow horizon |>.comp measurable_fst

/-- Markov transition driven by one unit-exponential mark and stopped at a
finite horizon, including the certified inactive/no-event branch. -/
noncomputable def PartialInverseHazardClock.firstEventKernel
    (clock : PartialInverseHazardClock State)
    (jump : State → State) (_hjump : Measurable jump) (horizon : NNReal) :
    Kernel State State :=
  Kernel.map
    (Kernel.prod Kernel.id (Kernel.const State unitHazardMeasure))
    (clock.firstEventUpdate jump horizon)

instance PartialInverseHazardClock.firstEventKernel.instIsMarkovKernel
    (clock : PartialInverseHazardClock State)
    (jump : State → State) (hjump : Measurable jump) (horizon : NNReal) :
    IsMarkovKernel (clock.firstEventKernel jump hjump horizon) := by
  unfold PartialInverseHazardClock.firstEventKernel
  apply Kernel.IsMarkovKernel.map
  exact clock.measurable_firstEventUpdate hjump horizon

/-! ### Repeated finite-horizon restart -/

/-- One capped restart step on `(remaining time, current state)`. A reachable
event inside the remaining horizon consumes its exact wait and jumps. An
inactive or beyond-horizon mark finishes the residual flow and sets remaining
time to zero, making all later capped steps inert. -/
noncomputable def PartialInverseHazardClock.cappedStepUpdate
    (clock : PartialInverseHazardClock State) (jump : State → State)
    (input : (NNReal × State) × NNReal) : NNReal × State :=
  let remaining := input.1.1
  let state := input.1.2
  let hazard := input.2
  if 0 < remaining ∧ clock.active state hazard = true ∧
      clock.waitingTime state hazard ≤ remaining then
    (remaining - clock.waitingTime state hazard,
      jump (clock.semiflow.flow (clock.waitingTime state hazard) state))
  else
    (0, clock.semiflow.flow remaining state)

theorem PartialInverseHazardClock.measurable_cappedStepUpdate
    (clock : PartialInverseHazardClock State)
    {jump : State → State} (hjump : Measurable jump) :
    Measurable (clock.cappedStepUpdate jump) := by
  let remaining : ((NNReal × State) × NNReal) → NNReal := fun input => input.1.1
  let state : ((NNReal × State) × NNReal) → State := fun input => input.1.2
  let hazard : ((NNReal × State) × NNReal) → NNReal := fun input => input.2
  have hremaining : Measurable remaining := measurable_fst.comp measurable_fst
  have hstate : Measurable state := measurable_snd.comp measurable_fst
  have hhazard : Measurable hazard := measurable_snd
  have hactive : Measurable (fun input => clock.active (state input) (hazard input)) :=
    clock.measurable_active.comp (hstate.prodMk hhazard)
  have hwait : Measurable (fun input =>
      clock.waitingTime (state input) (hazard input)) :=
    clock.measurable_waitingTime.comp (hstate.prodMk hhazard)
  unfold PartialInverseHazardClock.cappedStepUpdate
  apply Measurable.ite
  · exact (measurableSet_lt measurable_const hremaining).inter
      ((measurableSet_singleton true).preimage hactive |>.inter
        (measurableSet_le hwait.coe_nnreal_real hremaining.coe_nnreal_real))
  · exact (hremaining.sub hwait).prodMk <| hjump.comp <|
      clock.semiflow.jointly_measurable_flow.comp (hwait.prodMk hstate)
  · exact measurable_const.prodMk <|
      clock.semiflow.jointly_measurable_flow.comp (hremaining.prodMk hstate)

@[simp] theorem PartialInverseHazardClock.cappedStepUpdate_zero
    (clock : PartialInverseHazardClock State) (jump : State → State)
    (state : State) (hazard : NNReal) :
    clock.cappedStepUpdate jump ((0, state), hazard) = (0, state) := by
  simp [PartialInverseHazardClock.cappedStepUpdate,
    clock.semiflow.flow_zero]

theorem PartialInverseHazardClock.cappedStepUpdate_of_event
    (clock : PartialInverseHazardClock State) (jump : State → State)
    {remaining : NNReal} {state : State} {hazard : NNReal}
    (hremaining : 0 < remaining) (hactive : clock.active state hazard = true)
    (hwait : clock.waitingTime state hazard ≤ remaining) :
    clock.cappedStepUpdate jump ((remaining, state), hazard) =
      (remaining - clock.waitingTime state hazard,
        jump (clock.semiflow.flow (clock.waitingTime state hazard) state)) := by
  simp [PartialInverseHazardClock.cappedStepUpdate, hremaining, hactive, hwait]

theorem PartialInverseHazardClock.cappedStepUpdate_of_no_event
    (clock : PartialInverseHazardClock State) (jump : State → State)
    {remaining : NNReal} {state : State} {hazard : NNReal}
    (hnoevent : ¬(0 < remaining ∧ clock.active state hazard = true ∧
      clock.waitingTime state hazard ≤ remaining)) :
    clock.cappedStepUpdate jump ((remaining, state), hazard) =
      (0, clock.semiflow.flow remaining state) := by
  simp [PartialInverseHazardClock.cappedStepUpdate, hnoevent]

/-- Deterministic replay of a supplied finite hazard prefix on remaining-time
state. This is the pathwise object whose almost-sure eventual stabilization is
the nonexplosion/finite-horizon obligation for the infinite process. -/
noncomputable def PartialInverseHazardClock.executeHazards
    (clock : PartialInverseHazardClock State) (jump : State → State) :
    List NNReal → NNReal × State → NNReal × State
  | [], remainingState => remainingState
  | hazard :: hazards, remainingState =>
      clock.executeHazards jump hazards
        (clock.cappedStepUpdate jump (remainingState, hazard))

theorem PartialInverseHazardClock.executeHazards_append
    (clock : PartialInverseHazardClock State) (jump : State → State)
    (first second : List NNReal) (remainingState : NNReal × State) :
    clock.executeHazards jump (first ++ second) remainingState =
      clock.executeHazards jump second
        (clock.executeHazards jump first remainingState) := by
  induction first generalizing remainingState with
  | nil => rfl
  | cons hazard hazards ih =>
      simp only [List.cons_append,
        PartialInverseHazardClock.executeHazards]
      exact ih _

@[simp] theorem PartialInverseHazardClock.executeHazards_zero
    (clock : PartialInverseHazardClock State) (jump : State → State)
    (hazards : List NNReal) (state : State) :
    clock.executeHazards jump hazards (0, state) = (0, state) := by
  induction hazards with
  | nil => rfl
  | cons hazard hazards ih =>
      simp only [PartialInverseHazardClock.executeHazards,
        clock.cappedStepUpdate_zero, ih]

/-- Once a finite hazard prefix has finished the horizon, every longer prefix
has exactly the same endpoint. -/
theorem PartialInverseHazardClock.executeHazards_stable_of_zero
    (clock : PartialInverseHazardClock State) (jump : State → State)
    (first second : List NNReal) (remainingState : NNReal × State)
    (state : State)
    (hfinished : clock.executeHazards jump first remainingState = (0, state)) :
    clock.executeHazards jump (first ++ second) remainingState = (0, state) := by
  rw [clock.executeHazards_append, hfinished,
    clock.executeHazards_zero]

/-- If replaying a nonempty prefix is still active at the end, its first
candidate must also have left positive remaining time. -/
theorem PartialInverseHazardClock.cappedStep_fst_ne_zero_of_execute_cons
    (clock : PartialInverseHazardClock State) (jump : State → State)
    (hazard : NNReal) (hazards : List NNReal)
    (remainingState : NNReal × State)
    (hactive : (clock.executeHazards jump (hazard :: hazards)
      remainingState).1 ≠ 0) :
    (clock.cappedStepUpdate jump (remainingState, hazard)).1 ≠ 0 := by
  intro hzero
  have hstep : clock.cappedStepUpdate jump (remainingState, hazard) =
      (0, (clock.cappedStepUpdate jump (remainingState, hazard)).2) :=
    Prod.ext hzero rfl
  change (clock.executeHazards jump hazards
    (clock.cappedStepUpdate jump (remainingState, hazard))).1 ≠ 0 at hactive
  rw [hstep, clock.executeHazards_zero] at hactive
  exact hactive rfl

/-- Consequently every candidate preceding a still-active replay endpoint
satisfied the exact-event branch condition. -/
theorem PartialInverseHazardClock.event_condition_of_execute_cons_fst_ne_zero
    (clock : PartialInverseHazardClock State) (jump : State → State)
    (hazard : NNReal) (hazards : List NNReal)
    (remainingState : NNReal × State)
    (hactive : (clock.executeHazards jump (hazard :: hazards)
      remainingState).1 ≠ 0) :
    0 < remainingState.1 ∧
      clock.active remainingState.2 hazard = true ∧
      clock.waitingTime remainingState.2 hazard ≤ remainingState.1 := by
  have hstep := clock.cappedStep_fst_ne_zero_of_execute_cons jump hazard
    hazards remainingState hactive
  by_contra hcondition
  rw [clock.cappedStepUpdate_of_no_event jump hcondition] at hstep
  exact hstep rfl

/-- Infinite iid unit-exponential hazard stream for repeated inverse-clock
restart. -/
noncomputable def unitHazardSequenceMeasure : Measure (ℕ → NNReal) :=
  Measure.infinitePi (fun _ : ℕ => unitHazardMeasure)

instance unitHazardSequenceMeasure.instIsProbabilityMeasure :
    IsProbabilityMeasure unitHazardSequenceMeasure := by
  unfold unitHazardSequenceMeasure
  infer_instance

/-- An independent unit-exponential head almost surely avoids every measurable
threshold determined by the iid tail. -/
theorem unitHazard_head_ne_measurable_tail_ae
    (threshold : (ℕ → NNReal) → NNReal) (hthreshold : Measurable threshold) :
    ∀ᵐ headTail ∂unitHazardMeasure.prod unitHazardSequenceMeasure,
      headTail.1 ≠ threshold headTail.2 := by
  have hmeasurable : MeasurableSet
      {headTail : NNReal × (ℕ → NNReal) |
        headTail.1 ≠ threshold headTail.2} := by
    change MeasurableSet
      ({headTail : NNReal × (ℕ → NNReal) |
        headTail.1 = threshold headTail.2}ᶜ)
    exact (measurableSet_eq_fun measurable_fst
      (hthreshold.comp measurable_snd)).compl
  have htailHead : ∀ᵐ tail ∂unitHazardSequenceMeasure,
      ∀ᵐ head ∂unitHazardMeasure, head ≠ threshold tail := by
    filter_upwards [] with tail
    rw [ae_iff]
    have hset : {head : NNReal | ¬head ≠ threshold tail} =
        {threshold tail} := by
      ext head
      simp
    rw [hset]
    exact unitHazardMeasure_singleton _
  apply (Measure.ae_prod_iff_ae_ae hmeasurable).2
  exact (Measure.ae_ae_comm hmeasurable).mpr htailHead

/-- Removing the first coordinate from an iid unit-hazard stream leaves the
same infinite-product law. -/
theorem unitHazardSequenceMeasure_map_tail :
    unitHazardSequenceMeasure.map
        (fun hazards index => hazards (index + 1)) =
      unitHazardSequenceMeasure := by
  unfold unitHazardSequenceMeasure
  simpa using Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ => unitHazardMeasure)
    (f := fun index : ℕ => index + 1) (by
      intro left right heq
      exact Nat.add_right_cancel heq)

theorem unitHazardSequenceMeasure_preserving_tail :
    MeasurePreserving (fun hazards : ℕ → NNReal =>
      fun index => hazards (index + 1))
      unitHazardSequenceMeasure unitHazardSequenceMeasure where
  measurable := by fun_prop
  map_eq := unitHazardSequenceMeasure_map_tail

/-- Split an infinite hazard stream into its first mark and strict tail. -/
def unitHazardHeadTail
    (hazards : ℕ → NNReal) : NNReal × (ℕ → NNReal) :=
  (hazards 0, fun index => hazards (index + 1))

/-- Reconstruct an infinite hazard stream from an explicit head and tail. -/
def unitHazardCons
    (headTail : NNReal × (ℕ → NNReal)) : ℕ → NNReal
  | 0 => headTail.1
  | index + 1 => headTail.2 index

theorem measurable_unitHazardHeadTail : Measurable unitHazardHeadTail := by
  unfold unitHazardHeadTail
  fun_prop

theorem measurable_unitHazardCons : Measurable unitHazardCons := by
  rw [measurable_pi_iff]
  intro index
  cases index with
  | zero => exact measurable_fst
  | succ index => exact (measurable_pi_apply index).comp measurable_snd

@[simp] theorem unitHazardCons_headTail (hazards : ℕ → NNReal) :
    unitHazardCons (unitHazardHeadTail hazards) = hazards := by
  funext index
  cases index <;> rfl

@[simp] theorem unitHazardHeadTail_cons
    (headTail : NNReal × (ℕ → NNReal)) :
    unitHazardHeadTail (unitHazardCons headTail) = headTail := by
  apply Prod.ext
  · rfl
  · funext index
    rfl

/-- Two-block index separating coordinate zero from the strict tail. -/
abbrev UnitHazardHeadTailIndex : Bool → Type
  | false => PUnit
  | true => ℕ

private def unitHazardHeadTailIndexToNat :
    (block : Bool) → UnitHazardHeadTailIndex block → ℕ
  | false, _ => 0
  | true, index => index + 1

def unitHazardHeadTailIndexEquiv :
    (Σ block, UnitHazardHeadTailIndex block) ≃ ℕ where
  toFun value := unitHazardHeadTailIndexToNat value.1 value.2
  invFun
    | 0 => ⟨false, PUnit.unit⟩
    | index + 1 => ⟨true, index⟩
  left_inv value := by
    rcases value with ⟨block, index⟩
    cases block
    · change (⟨false, PUnit.unit⟩ :
        Σ block, UnitHazardHeadTailIndex block) = ⟨false, index⟩
      cases index
      rfl
    · simp [unitHazardHeadTailIndexToNat]
  right_inv index := by
    cases index <;> simp [unitHazardHeadTailIndexToNat]

/-- Reindexing and currying group the iid product into its singleton head and
infinite tail blocks. -/
theorem unitHazardSequenceMeasure_map_grouped :
    unitHazardSequenceMeasure.map
        (fun hazards block index => hazards
          (unitHazardHeadTailIndexEquiv ⟨block, index⟩)) =
      Measure.infinitePi (fun block : Bool =>
        Measure.infinitePi (fun _ : UnitHazardHeadTailIndex block =>
          unitHazardMeasure)) := by
  let reindex := MeasurableEquiv.piCongrLeft
    (fun _ : (Σ block, UnitHazardHeadTailIndex block) => NNReal)
    unitHazardHeadTailIndexEquiv.symm
  let regroup := MeasurableEquiv.piCurry
    (fun block (index : UnitHazardHeadTailIndex block) => NNReal)
  rw [show (fun hazards block index => hazards
      (unitHazardHeadTailIndexEquiv ⟨block, index⟩)) =
      regroup ∘ reindex by
    funext hazards block index
    have h := MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : (Σ block, UnitHazardHeadTailIndex block) => NNReal)
      unitHazardHeadTailIndexEquiv.symm hazards
      (unitHazardHeadTailIndexEquiv ⟨block, index⟩)
    change hazards (unitHazardHeadTailIndexEquiv ⟨block, index⟩) =
      reindex hazards ⟨block, index⟩
    simpa [reindex] using h.symm]
  rw [← Measure.map_map regroup.measurable reindex.measurable]
  unfold unitHazardSequenceMeasure
  dsimp [reindex]
  rw [Measure.infinitePi_map_piCongrLeft
    (μ := fun _ : (Σ block, UnitHazardHeadTailIndex block) =>
      unitHazardMeasure)
    unitHazardHeadTailIndexEquiv.symm]
  dsimp [regroup]
  convert Measure.infinitePi_map_piCurry
    (fun block (index : UnitHazardHeadTailIndex block) =>
      unitHazardMeasure) using 1

/-- The first unit-exponential hazard and the strict iid tail have the exact
product law. -/
theorem unitHazardSequenceMeasure_map_headTail :
    unitHazardSequenceMeasure.map unitHazardHeadTail =
      unitHazardMeasure.prod unitHazardSequenceMeasure := by
  let groupedMeasure := Measure.infinitePi (fun block : Bool =>
    Measure.infinitePi (fun _ : UnitHazardHeadTailIndex block =>
      unitHazardMeasure))
  let ungroup := fun grouped :
      (block : Bool) → UnitHazardHeadTailIndex block → NNReal =>
    (grouped false PUnit.unit, grouped true)
  have hungroup : Measurable ungroup := by
    unfold ungroup
    fun_prop
  have hfactor : Measure.map ungroup groupedMeasure =
      unitHazardMeasure.prod unitHazardSequenceMeasure := by
    symm
    apply Measure.prod_eq
    intro headSet tailSet hhead htail
    rw [Measure.map_apply hungroup (hhead.prod htail)]
    let coordinateSet : (block : Bool) →
        Set (UnitHazardHeadTailIndex block → NNReal)
      | false => (fun head => head PUnit.unit) ⁻¹' headSet
      | true => tailSet
    have hpre : ungroup ⁻¹' (headSet ×ˢ tailSet) =
        Set.pi (↑(Finset.univ : Finset Bool)) coordinateSet := by
      ext grouped
      simp [ungroup, coordinateSet, and_comm]
    rw [hpre]
    have hcoordinate : ∀ block, MeasurableSet (coordinateSet block) := by
      intro block
      cases block
      · exact hhead.preimage (measurable_pi_apply PUnit.unit)
      · exact htail
    rw [Measure.infinitePi_pi _ (fun block _ => hcoordinate block)]
    have hheadMeasure :
        Measure.infinitePi (fun _ : PUnit => unitHazardMeasure)
            ((fun head => head PUnit.unit) ⁻¹' headSet) =
          unitHazardMeasure headSet := by
      rw [← Measure.map_apply (measurable_pi_apply PUnit.unit) hhead,
        Measure.infinitePi_map_eval]
    rw [Fintype.prod_bool]
    change unitHazardSequenceMeasure tailSet *
        Measure.infinitePi (fun _ : PUnit => unitHazardMeasure)
          ((fun head => head PUnit.unit) ⁻¹' headSet) = _
    rw [hheadMeasure]
    ac_rfl
  rw [show unitHazardHeadTail = ungroup ∘
      (fun hazards block index => hazards
        (unitHazardHeadTailIndexEquiv ⟨block, index⟩)) by
    funext hazards
    rfl]
  rw [← Measure.map_map hungroup (by fun_prop),
    unitHazardSequenceMeasure_map_grouped]
  exact hfactor

/-- Consing an independent unit-exponential head onto an iid tail reconstructs
the iid hazard-stream law. -/
theorem unitHazardMeasure_prod_sequence_map_cons :
    Measure.map unitHazardCons
        (unitHazardMeasure.prod unitHazardSequenceMeasure) =
      unitHazardSequenceMeasure := by
  rw [← unitHazardSequenceMeasure_map_headTail,
    Measure.map_map measurable_unitHazardCons measurable_unitHazardHeadTail]
  rw [show unitHazardCons ∘ unitHazardHeadTail = id by
    funext hazards
    exact unitHazardCons_headTail hazards,
    Measure.map_id]

/-- Coordinate event on which a unit-exponential mark exceeds one. -/
def unitLargeHazardEvent (index : ℕ) : Set (ℕ → NNReal) :=
  (fun hazards => hazards index) ⁻¹' Set.Ioi (1 : NNReal)

theorem measurableSet_unitLargeHazardEvent (index : ℕ) :
    MeasurableSet (unitLargeHazardEvent index) :=
  measurableSet_Ioi.preimage (measurable_pi_apply index)

theorem unitHazardSequenceMeasure_largeHazardEvent (index : ℕ) :
    unitHazardSequenceMeasure (unitLargeHazardEvent index) =
      unitHazardMeasure (Set.Ioi 1) := by
  unfold unitHazardSequenceMeasure unitLargeHazardEvent
  have hmap := Measure.infinitePi_map_eval
    (μ := fun _ : ℕ => unitHazardMeasure) index
  calc
    _ = (Measure.map (fun hazards : ℕ → NNReal => hazards index)
        (Measure.infinitePi fun _ : ℕ => unitHazardMeasure))
        (Set.Ioi 1) := by
      rw [Measure.map_apply (by fun_prop) measurableSet_Ioi]
    _ = _ := congrArg (fun measure : Measure NNReal => measure (Set.Ioi 1)) hmap

theorem unitLargeHazardEvent_iIndepSet :
    iIndepSet unitLargeHazardEvent unitHazardSequenceMeasure := by
  apply (iIndepSet_iff_meas_biInter
    measurableSet_unitLargeHazardEvent).2
  intro indices
  have hset : (⋂ index ∈ indices, unitLargeHazardEvent index) =
      Set.pi (indices : Set ℕ) (fun _ => Set.Ioi (1 : NNReal)) := by
    ext hazards
    simp [unitLargeHazardEvent]
  rw [hset]
  change (Measure.infinitePi fun _ : ℕ => unitHazardMeasure)
      (Set.pi (indices : Set ℕ) (fun _ => Set.Ioi (1 : NNReal))) = _
  rw [Measure.infinitePi_pi
    (μ := fun _ : ℕ => unitHazardMeasure)
    (s := indices) (t := fun _ => Set.Ioi (1 : NNReal))
    (fun _ _ => measurableSet_Ioi)]
  simp_rw [unitHazardSequenceMeasure_largeHazardEvent]

/-- An iid unit-exponential stream contains infinitely many marks larger than
one, almost surely. -/
theorem unitLargeHazardEvent_limsup_measure_eq_one :
    unitHazardSequenceMeasure
      (Filter.limsup unitLargeHazardEvent Filter.atTop) = 1 := by
  apply measure_limsup_eq_one
    measurableSet_unitLargeHazardEvent unitLargeHazardEvent_iIndepSet
  simp_rw [unitHazardSequenceMeasure_largeHazardEvent,
    unitHazardMeasure_Ioi]
  exact ENNReal.tsum_const_eq_top_of_ne_zero
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

theorem unitLargeHazardEvent_mem_limsup_ae :
    ∀ᵐ hazards ∂unitHazardSequenceMeasure,
      hazards ∈ Filter.limsup unitLargeHazardEvent Filter.atTop := by
  rw [ae_iff]
  have hmeasurable : MeasurableSet
      (Filter.limsup unitLargeHazardEvent Filter.atTop) :=
    MeasurableSet.measurableSet_limsup measurableSet_unitLargeHazardEvent
  have hset : {hazards | ¬hazards ∈
      Filter.limsup unitLargeHazardEvent Filter.atTop} =
      (Filter.limsup unitLargeHazardEvent Filter.atTop)ᶜ := rfl
  rw [hset, measure_compl hmeasurable (measure_ne_top _ _),
    unitLargeHazardEvent_limsup_measure_eq_one, measure_univ, tsub_self]

/-- The sum of iid unit-exponential hazard marks is infinite almost surely.
This reusable fact is the probabilistic half of bounded-on-finite-horizons
nonexplosion arguments. -/
theorem unitHazard_tsum_eq_top_ae :
    ∀ᵐ hazards ∂unitHazardSequenceMeasure,
      (∑' index, (hazards index : ENNReal)) = ∞ := by
  filter_upwards [unitLargeHazardEvent_mem_limsup_ae] with hazards hlimsup
  have hfrequent : ∃ᶠ index in Filter.atTop,
      hazards ∈ unitLargeHazardEvent index :=
    Filter.mem_limsup_iff_frequently_mem.mp hlimsup
  have hinfiniteLarge : Set.Infinite
      {index | hazards ∈ unitLargeHazardEvent index} :=
    Nat.frequently_atTop_iff_infinite.mp hfrequent
  have hinfiniteTerm : Set.Infinite
      {index | 1 ≤ (hazards index : ENNReal)} :=
    hinfiniteLarge.mono fun index hindex => by
      exact_mod_cast (show (1 : NNReal) < hazards index from hindex).le
  by_contra hfiniteSum
  exact hinfiniteTerm
    (ENNReal.finite_const_le_of_tsum_ne_top hfiniteSum one_ne_zero)

/-- Almost every iid hazard stream has a finite prefix whose accumulated mark
exceeds any prescribed finite bound. -/
theorem unitHazard_prefix_sum_unbounded_ae :
    ∀ᵐ hazards ∂unitHazardSequenceMeasure,
      ∀ bound : NNReal, ∃ count : ℕ,
        (bound : ENNReal) <
          ∑ index ∈ Finset.range count, (hazards index : ENNReal) := by
  filter_upwards [unitHazard_tsum_eq_top_ae] with hazards hsum
  intro bound
  have hlt : (bound : ENNReal) <
      ⨆ count : ℕ,
        ∑ index ∈ Finset.range count, (hazards index : ENNReal) := by
    rw [← ENNReal.tsum_eq_iSup_nat, hsum]
    exact ENNReal.coe_lt_top
  exact lt_iSup_iff.mp hlt

/-- First `count` marks of an infinite hazard stream, in execution order. -/
def hazardPrefix (count : ℕ) (hazards : ℕ → NNReal) : List NNReal :=
  List.ofFn fun index : Fin count => hazards index

@[simp] theorem hazardPrefix_zero (hazards : ℕ → NNReal) :
    hazardPrefix 0 hazards = [] := by
  simp [hazardPrefix]

theorem hazardPrefix_succ (count : ℕ) (hazards : ℕ → NNReal) :
    hazardPrefix (count + 1) hazards =
      hazardPrefix count hazards ++ [hazards count] := by
  simpa [hazardPrefix] using
    (List.ofFn_succ_last (f := fun index : Fin (count + 1) => hazards index))

/-- Joint replay of the first `count` coordinates of a hazard stream. The
recursive presentation makes measurability transparent; the theorem below
identifies it with `executeHazards (hazardPrefix count hazards)`. -/
noncomputable def PartialInverseHazardClock.replayPrefix
    (clock : PartialInverseHazardClock State) (jump : State → State) :
    ℕ → ((NNReal × State) × (ℕ → NNReal)) → NNReal × State
  | 0, input => input.1
  | count + 1, input => clock.cappedStepUpdate jump
      (clock.replayPrefix jump count input, input.2 count)

theorem PartialInverseHazardClock.measurable_replayPrefix
    (clock : PartialInverseHazardClock State) {jump : State → State}
    (hjump : Measurable jump) (count : ℕ) :
    Measurable (clock.replayPrefix jump count) := by
  induction count with
  | zero => exact measurable_fst
  | succ count ih =>
      exact clock.measurable_cappedStepUpdate hjump |>.comp
        (ih.prodMk (measurable_pi_apply count |>.comp measurable_snd))

theorem PartialInverseHazardClock.replayPrefix_eq_executeHazards
    (clock : PartialInverseHazardClock State) (jump : State → State)
    (count : ℕ) (input : (NNReal × State) × (ℕ → NNReal)) :
    clock.replayPrefix jump count input =
      clock.executeHazards jump (hazardPrefix count input.2) input.1 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [show count + 1 = Nat.succ count from rfl,
        hazardPrefix_succ, clock.executeHazards_append]
      simp only [PartialInverseHazardClock.replayPrefix, ih,
        PartialInverseHazardClock.executeHazards]

/-- Once a replay prefix has finished, every longer prefix is exactly the same
remaining-time state. -/
theorem PartialInverseHazardClock.replayPrefix_stable_of_finished
    (clock : PartialInverseHazardClock State) (jump : State → State)
    (input : (NNReal × State) × (ℕ → NNReal))
    {first second : ℕ}
    (hfinished : (clock.replayPrefix jump first input).1 = 0)
    (hle : first ≤ second) :
    clock.replayPrefix jump second input =
      clock.replayPrefix jump first input := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction extra with
  | zero => simp
  | succ extra ih =>
      rw [Nat.add_succ, PartialInverseHazardClock.replayPrefix,
        ih (Nat.le_add_right first extra)]
      have hpair : clock.replayPrefix jump first input =
          (0, (clock.replayPrefix jump first input).2) :=
        Prod.ext hfinished rfl
      rw [hpair, clock.cappedStepUpdate_zero]

/-- Prefix replay on a cons stream is replay of the tail after applying the
head candidate once. -/
theorem PartialInverseHazardClock.replayPrefix_succ_cons
    (clock : PartialInverseHazardClock State) (jump : State → State)
    (count : ℕ) (remainingState : NNReal × State)
    (headTail : NNReal × (ℕ → NNReal)) :
    clock.replayPrefix jump (count + 1)
        (remainingState, unitHazardCons headTail) =
      clock.replayPrefix jump count
        (clock.cappedStepUpdate jump (remainingState, headTail.1),
          headTail.2) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change clock.cappedStepUpdate jump
          (clock.replayPrefix jump (count + 1)
              (remainingState, unitHazardCons headTail),
            unitHazardCons headTail (count + 1)) =
        clock.cappedStepUpdate jump
          (clock.replayPrefix jump count
              (clock.cappedStepUpdate jump (remainingState, headTail.1),
                headTail.2),
            headTail.2 count)
      rw [ih]
      rfl

/-- Exact nonexplosion/completion obligation for a partial inverse clock: at
every finite horizon and initial state, almost every iid hazard stream has a
finite prefix after which no time remains. Stability then makes every longer
prefix return the same endpoint. -/
def PartialInverseHazardClock.CompletesFiniteHorizons
    (clock : PartialInverseHazardClock State) (jump : State → State) : Prop :=
  ∀ (horizon : NNReal) (initial : State),
    ∀ᵐ hazards ∂unitHazardSequenceMeasure,
      ∃ count terminal,
        clock.executeHazards jump (hazardPrefix count hazards)
          (horizon, initial) = (0, terminal)

/-- Deterministic bounded-hazard criterion for finite-horizon completion.
For each horizon and initial state, every finite prefix that has not yet
finished must have consumed at most one common finite amount of integrated
hazard. -/
def PartialInverseHazardClock.HasBoundedActivePrefixHazard
    (clock : PartialInverseHazardClock State) (jump : State → State) : Prop :=
  ∀ (horizon : NNReal) (initial : State), ∃ bound : NNReal,
    ∀ (hazards : ℕ → NNReal) (count : ℕ),
      (clock.executeHazards jump (hazardPrefix count hazards)
          (horizon, initial)).1 ≠ 0 →
        (∑ index ∈ Finset.range count,
          (hazards index : ENNReal)) ≤ (bound : ENNReal)

/-- A deterministic bound on every still-active prefix, combined with the
almost-sure divergence of iid unit-exponential marks, proves exact
finite-horizon completion. -/
theorem PartialInverseHazardClock.completesFiniteHorizons_of_boundedActivePrefixHazard
    (clock : PartialInverseHazardClock State) (jump : State → State)
    (hbounded : clock.HasBoundedActivePrefixHazard jump) :
    clock.CompletesFiniteHorizons jump := by
  intro horizon initial
  obtain ⟨bound, hbound⟩ := hbounded horizon initial
  filter_upwards [unitHazard_prefix_sum_unbounded_ae] with hazards hunbounded
  obtain ⟨count, hcount⟩ := hunbounded bound
  let result := clock.executeHazards jump (hazardPrefix count hazards)
    (horizon, initial)
  have hfinished : result.1 = 0 := by
    by_contra hne
    exact (not_lt_of_ge (hbound hazards count hne)) hcount
  exact ⟨count, result.2, Prod.ext hfinished rfl⟩

/-- A one-step potential that pays for every accepted hazard bounds the sum of
all marks in any replay prefix that remains active. -/
theorem PartialInverseHazardClock.executeHazards_sum_le_potential
    (clock : PartialInverseHazardClock State) (jump : State → State)
    (potential : NNReal × State → NNReal)
    (hstep : ∀ (remainingState : NNReal × State) (hazard : NNReal),
      0 < remainingState.1 ∧
          clock.active remainingState.2 hazard = true ∧
          clock.waitingTime remainingState.2 hazard ≤ remainingState.1 →
        hazard + potential (clock.cappedStepUpdate jump
          (remainingState, hazard)) ≤ potential remainingState)
    (hazards : List NNReal) (remainingState : NNReal × State)
    (hactive : (clock.executeHazards jump hazards remainingState).1 ≠ 0) :
    hazards.sum + potential (clock.executeHazards jump hazards remainingState) ≤
      potential remainingState := by
  induction hazards generalizing remainingState with
  | nil => simp [PartialInverseHazardClock.executeHazards]
  | cons hazard hazards ih =>
      let next := clock.cappedStepUpdate jump (remainingState, hazard)
      have hcondition := clock.event_condition_of_execute_cons_fst_ne_zero
        jump hazard hazards remainingState hactive
      have htail : (clock.executeHazards jump hazards next).1 ≠ 0 := by
        exact hactive
      have htailBound := ih next htail
      simp only [List.sum_cons, PartialInverseHazardClock.executeHazards]
      calc
        hazard + hazards.sum + potential
            (clock.executeHazards jump hazards
              (clock.cappedStepUpdate jump (remainingState, hazard))) =
            hazard + (hazards.sum + potential
              (clock.executeHazards jump hazards next)) := by
                simp [next, add_assoc]
        _ ≤
            hazard + potential next := by gcongr
        _ ≤ potential remainingState := hstep remainingState hazard hcondition

/-- A finite NNReal potential satisfying the accepted-step payment inequality
discharges the generic bounded-active-prefix criterion. -/
theorem PartialInverseHazardClock.hasBoundedActivePrefixHazard_of_potential
    (clock : PartialInverseHazardClock State) (jump : State → State)
    (potential : NNReal × State → NNReal)
    (hstep : ∀ (remainingState : NNReal × State) (hazard : NNReal),
      0 < remainingState.1 ∧
          clock.active remainingState.2 hazard = true ∧
          clock.waitingTime remainingState.2 hazard ≤ remainingState.1 →
        hazard + potential (clock.cappedStepUpdate jump
          (remainingState, hazard)) ≤ potential remainingState) :
    clock.HasBoundedActivePrefixHazard jump := by
  intro horizon initial
  refine ⟨potential (horizon, initial), ?_⟩
  intro hazards count hactive
  have hlist := clock.executeHazards_sum_le_potential jump potential hstep
    (hazardPrefix count hazards) (horizon, initial) hactive
  have hsum : (hazardPrefix count hazards).sum ≤
      potential (horizon, initial) :=
    (le_add_right le_rfl).trans hlist
  have hprefix : (hazardPrefix count hazards).sum =
      ∑ index ∈ Finset.range count, hazards index := by
    simpa [hazardPrefix, List.sum_ofFn] using
      (Fin.sum_univ_eq_sum_range hazards count)
  rw [hprefix] at hsum
  exact_mod_cast hsum

/-! ### Measurable completed-horizon endpoint -/

def PartialInverseHazardClock.replayFinished
    (clock : PartialInverseHazardClock State) (jump : State → State)
    (input : (NNReal × State) × (ℕ → NNReal)) (count : ℕ) : Prop :=
  (clock.replayPrefix jump count input).1 = 0

theorem PartialInverseHazardClock.measurableSet_replayFinished
    (clock : PartialInverseHazardClock State) {jump : State → State}
    (hjump : Measurable jump) (count : ℕ) :
    MeasurableSet {input | clock.replayFinished jump input count} := by
  exact (measurableSet_singleton (0 : NNReal)).preimage
    (clock.measurable_replayPrefix hjump count).fst

/-- Total search predicate: use genuine completion when it exists, and index
zero only as a measurable fallback on explosive streams. -/
def PartialInverseHazardClock.completionSearch
    (clock : PartialInverseHazardClock State) (jump : State → State)
    (input : (NNReal × State) × (ℕ → NNReal)) (count : ℕ) : Prop :=
  clock.replayFinished jump input count ∨
    (count = 0 ∧ ¬∃ candidate, clock.replayFinished jump input candidate)

theorem PartialInverseHazardClock.completionSearch_exists
    (clock : PartialInverseHazardClock State) (jump : State → State)
    (input : (NNReal × State) × (ℕ → NNReal)) :
    ∃ count, clock.completionSearch jump input count := by
  by_cases hcomplete : ∃ count, clock.replayFinished jump input count
  · obtain ⟨count, hcount⟩ := hcomplete
    exact ⟨count, Or.inl hcount⟩
  · exact ⟨0, Or.inr ⟨rfl, hcomplete⟩⟩

theorem PartialInverseHazardClock.measurableSet_completionSearch
    (clock : PartialInverseHazardClock State) {jump : State → State}
    (hjump : Measurable jump) (count : ℕ) :
    MeasurableSet {input | clock.completionSearch jump input count} := by
  have hexists : MeasurableSet {input |
      ∃ candidate, clock.replayFinished jump input candidate} := by
    simp only [Set.setOf_exists]
    exact MeasurableSet.iUnion fun candidate =>
      clock.measurableSet_replayFinished hjump candidate
  by_cases hcount : count = 0
  · subst count
    have hfinished := clock.measurableSet_replayFinished hjump 0
    have hset : {input | clock.completionSearch jump input 0} =
        {input | clock.replayFinished jump input 0} ∪
          {input | ¬∃ candidate,
            clock.replayFinished jump input candidate} := by
      ext input
      simp [PartialInverseHazardClock.completionSearch]
    rw [hset]
    exact hfinished.union hexists.compl
  · simpa [PartialInverseHazardClock.completionSearch, hcount] using
      clock.measurableSet_replayFinished hjump count

/-- First completed replay prefix, with the total fallback predicate above on
streams for which no finite prefix completes. -/
noncomputable def PartialInverseHazardClock.completionCount
    (clock : PartialInverseHazardClock State) (jump : State → State)
    (input : (NNReal × State) × (ℕ → NNReal)) : ℕ := by
  classical
  exact Nat.find (clock.completionSearch_exists jump input)

theorem PartialInverseHazardClock.measurable_completionCount
    (clock : PartialInverseHazardClock State) {jump : State → State}
    (hjump : Measurable jump) :
    Measurable (clock.completionCount jump) := by
  classical
  exact measurable_find (clock.completionSearch_exists jump)
    (clock.measurableSet_completionSearch hjump)

theorem PartialInverseHazardClock.completionCount_spec
    (clock : PartialInverseHazardClock State) (jump : State → State)
    (input : (NNReal × State) × (ℕ → NNReal)) :
    clock.completionSearch jump input (clock.completionCount jump input) :=
  by
    classical
    exact Nat.find_spec (clock.completionSearch_exists jump input)

theorem PartialInverseHazardClock.replayFinished_completionCount
    (clock : PartialInverseHazardClock State) (jump : State → State)
    (input : (NNReal × State) × (ℕ → NNReal))
    (hcomplete : ∃ count, clock.replayFinished jump input count) :
    clock.replayFinished jump input (clock.completionCount jump input) := by
  classical
  rcases clock.completionCount_spec jump input with hfinished | hfallback
  · exact hfinished
  · exact (hfallback.2 hcomplete).elim

/-- Under the nonexplosion obligation, the selected completion count is a
genuine finished prefix almost surely; the total fallback is therefore null. -/
theorem PartialInverseHazardClock.replayFinished_completionCount_ae
    (clock : PartialInverseHazardClock State) (jump : State → State)
    (hcomplete : clock.CompletesFiniteHorizons jump)
    (horizon : NNReal) (initial : State) :
    ∀ᵐ hazards ∂unitHazardSequenceMeasure,
      clock.replayFinished jump ((horizon, initial), hazards)
        (clock.completionCount jump ((horizon, initial), hazards)) := by
  filter_upwards [hcomplete horizon initial] with hazards hhazards
  apply clock.replayFinished_completionCount jump
  obtain ⟨count, terminal, hcount⟩ := hhazards
  refine ⟨count, ?_⟩
  unfold PartialInverseHazardClock.replayFinished
  rw [clock.replayPrefix_eq_executeHazards]
  rw [hcount]

/-- Measurable stratum on which the selected completion count is a specified
finite index and is a genuine completed prefix rather than the total fallback. -/
def PartialInverseHazardClock.genuineCompletionStratum
    (clock : PartialInverseHazardClock State) (jump : State → State)
    (horizon : NNReal) (initial : State) (count : ℕ) : Set (ℕ → NNReal) :=
  {hazards | clock.completionCount jump ((horizon, initial), hazards) = count ∧
    clock.replayFinished jump ((horizon, initial), hazards) count}

theorem PartialInverseHazardClock.measurableSet_genuineCompletionStratum
    (clock : PartialInverseHazardClock State) {jump : State → State}
    (hjump : Measurable jump) (horizon : NNReal) (initial : State)
    (count : ℕ) :
    MeasurableSet (clock.genuineCompletionStratum jump horizon initial count) := by
  apply MeasurableSet.inter
  · exact (measurableSet_singleton count).preimage
      (clock.measurable_completionCount hjump |>.comp
        ((measurable_const.prodMk measurable_const).prodMk measurable_id))
  · exact (clock.measurableSet_replayFinished hjump count).preimage
      ((measurable_const.prodMk measurable_const).prodMk measurable_id)

theorem PartialInverseHazardClock.genuineCompletionStratum_pairwiseDisjoint
    (clock : PartialInverseHazardClock State) (jump : State → State)
    (horizon : NNReal) (initial : State) :
    Pairwise fun left right => Disjoint
      (clock.genuineCompletionStratum jump horizon initial left)
      (clock.genuineCompletionStratum jump horizon initial right) := by
  intro left right hne
  rw [Set.disjoint_left]
  intro hazards hleft hright
  exact hne (hleft.1.symm.trans hright.1)

/-- Under finite-horizon completion, the genuine count strata cover almost
every hazard stream. -/
theorem PartialInverseHazardClock.ae_mem_iUnion_genuineCompletionStratum
    (clock : PartialInverseHazardClock State) (jump : State → State)
    (hcomplete : clock.CompletesFiniteHorizons jump)
    (horizon : NNReal) (initial : State) :
    ∀ᵐ hazards ∂unitHazardSequenceMeasure,
      hazards ∈ ⋃ count,
        clock.genuineCompletionStratum jump horizon initial count := by
  filter_upwards [clock.replayFinished_completionCount_ae jump hcomplete
    horizon initial] with hazards hfinished
  apply Set.mem_iUnion.mpr
  refine ⟨clock.completionCount jump ((horizon, initial), hazards), ?_⟩
  exact ⟨rfl, hfinished⟩

/-- A positive horizon cannot genuinely complete at the zero prefix. -/
theorem PartialInverseHazardClock.genuineCompletionStratum_zero_eq_empty
    (clock : PartialInverseHazardClock State) (jump : State → State)
    {horizon : NNReal} (hhorizon : 0 < horizon) (initial : State) :
    clock.genuineCompletionStratum jump horizon initial 0 = ∅ := by
  ext hazards
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hmem
  exact hhorizon.ne' hmem.2

/-- On the `(count+1)` stratum, the prefix before the terminal candidate is
still active. -/
theorem PartialInverseHazardClock.replayPrefix_fst_ne_zero_on_succ_stratum
    (clock : PartialInverseHazardClock State) (jump : State → State)
    (horizon : NNReal) (initial : State) (count : ℕ)
    {hazards : ℕ → NNReal}
    (hmem : hazards ∈
      clock.genuineCompletionStratum jump horizon initial (count + 1)) :
    (clock.replayPrefix jump count ((horizon, initial), hazards)).1 ≠ 0 := by
  classical
  intro hzero
  have hp : clock.completionSearch jump ((horizon, initial), hazards) count :=
    Or.inl hzero
  have hle := Nat.find_min'
    (clock.completionSearch_exists jump ((horizon, initial), hazards)) hp
  change clock.completionCount jump ((horizon, initial), hazards) ≤ count at hle
  rw [hmem.1] at hle
  omega

/-- The candidate at the end of a `(count+1)` stratum sets remaining time to
zero. -/
theorem PartialInverseHazardClock.cappedStep_fst_eq_zero_on_succ_stratum
    (clock : PartialInverseHazardClock State) (jump : State → State)
    (horizon : NNReal) (initial : State) (count : ℕ)
    {hazards : ℕ → NNReal}
    (hmem : hazards ∈
      clock.genuineCompletionStratum jump horizon initial (count + 1)) :
    (clock.cappedStepUpdate jump
      (clock.replayPrefix jump count ((horizon, initial), hazards),
        hazards count)).1 = 0 := by
  exact hmem.2

/-- A terminal candidate either takes the no-event branch or rings exactly at
the remaining-horizon boundary. The latter equality is a null case for a
continuous hazard law and is isolated for the stratum-wise splice proof. -/
theorem PartialInverseHazardClock.terminal_noEvent_or_wait_eq_remaining
    (clock : PartialInverseHazardClock State) (jump : State → State)
    (horizon : NNReal) (initial : State) (count : ℕ)
    {hazards : ℕ → NNReal}
    (hmem : hazards ∈
      clock.genuineCompletionStratum jump horizon initial (count + 1)) :
    (¬(0 < (clock.replayPrefix jump count
            ((horizon, initial), hazards)).1 ∧
        clock.active
            (clock.replayPrefix jump count
              ((horizon, initial), hazards)).2
            (hazards count) = true ∧
        clock.waitingTime
            (clock.replayPrefix jump count
              ((horizon, initial), hazards)).2
            (hazards count) ≤
          (clock.replayPrefix jump count
            ((horizon, initial), hazards)).1)) ∨
      clock.waitingTime
          (clock.replayPrefix jump count
            ((horizon, initial), hazards)).2
          (hazards count) =
        (clock.replayPrefix jump count
          ((horizon, initial), hazards)).1 := by
  let before := clock.replayPrefix jump count ((horizon, initial), hazards)
  let hazard := hazards count
  by_cases hcondition : 0 < before.1 ∧
      clock.active before.2 hazard = true ∧
      clock.waitingTime before.2 hazard ≤ before.1
  · right
    have hzero := clock.cappedStep_fst_eq_zero_on_succ_stratum jump
      horizon initial count hmem
    rw [clock.cappedStepUpdate_of_event jump hcondition.1
      hcondition.2.1 hcondition.2.2] at hzero
    change before.1 - clock.waitingTime before.2 hazard = 0 at hzero
    exact le_antisymm hcondition.2.2 (tsub_eq_zero_iff_le.mp hzero)
  · exact Or.inl hcondition

/-- Totalized endpoint selected at the first completed prefix. On the null
explosive set it returns the zero-prefix state. -/
noncomputable def PartialInverseHazardClock.completedReplayEndpoint
    (clock : PartialInverseHazardClock State) (jump : State → State)
    (input : (NNReal × State) × (ℕ → NNReal)) : State :=
  (clock.replayPrefix jump (clock.completionCount jump input) input).2

theorem PartialInverseHazardClock.completionCount_zero_remaining
    (clock : PartialInverseHazardClock State) (jump : State → State)
    (state : State) (hazards : ℕ → NNReal) :
    clock.completionCount jump ((0, state), hazards) = 0 := by
  classical
  apply (Nat.find_eq_zero
    (clock.completionSearch_exists jump ((0, state), hazards))).2
  apply Or.inl
  rfl

@[simp] theorem PartialInverseHazardClock.completedReplayEndpoint_zero
    (clock : PartialInverseHazardClock State) (jump : State → State)
    (state : State) (hazards : ℕ → NNReal) :
    clock.completedReplayEndpoint jump ((0, state), hazards) = state := by
  unfold PartialInverseHazardClock.completedReplayEndpoint
  rw [clock.completionCount_zero_remaining]
  rfl

/-- The selected endpoint agrees with every completed finite prefix, not only
with the least one chosen by `completionCount`. -/
theorem PartialInverseHazardClock.completedReplayEndpoint_eq_replayPrefix
    (clock : PartialInverseHazardClock State) (jump : State → State)
    (input : (NNReal × State) × (ℕ → NNReal)) (count : ℕ)
    (hfinished : clock.replayFinished jump input count) :
    clock.completedReplayEndpoint jump input =
      (clock.replayPrefix jump count input).2 := by
  have hexists : ∃ candidate, clock.replayFinished jump input candidate :=
    ⟨count, hfinished⟩
  have hselected := clock.replayFinished_completionCount jump input hexists
  let selected := clock.completionCount jump input
  let common := max selected count
  have hselectedStable := clock.replayPrefix_stable_of_finished jump input
    hselected (le_max_left selected count)
  have hcountStable := clock.replayPrefix_stable_of_finished jump input
    hfinished (le_max_right selected count)
  unfold PartialInverseHazardClock.completedReplayEndpoint
  exact congrArg Prod.snd (hselectedStable.symm.trans hcountStable)

/-- On a genuine stratum, the totalized endpoint is exactly the corresponding
finite replay prefix. -/
theorem PartialInverseHazardClock.completedReplayEndpoint_eq_on_stratum
    (clock : PartialInverseHazardClock State) (jump : State → State)
    (horizon : NNReal) (initial : State) (count : ℕ)
    {hazards : ℕ → NNReal}
    (hmem : hazards ∈
      clock.genuineCompletionStratum jump horizon initial count) :
    clock.completedReplayEndpoint jump ((horizon, initial), hazards) =
      (clock.replayPrefix jump count ((horizon, initial), hazards)).2 :=
  clock.completedReplayEndpoint_eq_replayPrefix jump _ count hmem.2

/-- Pointwise head/tail recursion on every tail stream that completes: direct
execution on `cons(head, tail)` has the same endpoint as execution from the
one-step updated state using the fresh tail. -/
theorem PartialInverseHazardClock.completedReplayEndpoint_cons
    (clock : PartialInverseHazardClock State) (jump : State → State)
    (remainingState : NNReal × State)
    (headTail : NNReal × (ℕ → NNReal))
    (htail : ∃ count, clock.replayFinished jump
      (clock.cappedStepUpdate jump (remainingState, headTail.1), headTail.2)
      count) :
    clock.completedReplayEndpoint jump
        (remainingState, unitHazardCons headTail) =
      clock.completedReplayEndpoint jump
        (clock.cappedStepUpdate jump (remainingState, headTail.1),
          headTail.2) := by
  obtain ⟨count, hcount⟩ := htail
  have hrecursion := clock.replayPrefix_succ_cons jump count
    remainingState headTail
  have hdirect : clock.replayFinished jump
      (remainingState, unitHazardCons headTail) (count + 1) := by
    unfold PartialInverseHazardClock.replayFinished at hcount ⊢
    rw [hrecursion]
    exact hcount
  calc
    clock.completedReplayEndpoint jump
        (remainingState, unitHazardCons headTail) =
      (clock.replayPrefix jump (count + 1)
        (remainingState, unitHazardCons headTail)).2 :=
      clock.completedReplayEndpoint_eq_replayPrefix jump _ _ hdirect
    _ = (clock.replayPrefix jump count
        (clock.cappedStepUpdate jump (remainingState, headTail.1),
          headTail.2)).2 := congrArg Prod.snd hrecursion
    _ = clock.completedReplayEndpoint jump
        (clock.cappedStepUpdate jump (remainingState, headTail.1),
          headTail.2) :=
      (clock.completedReplayEndpoint_eq_replayPrefix jump _ _ hcount).symm

/-- Under finite-horizon completion, the head/tail endpoint recursion holds
almost surely under an independent unit-exponential head and iid tail. -/
theorem PartialInverseHazardClock.completedReplayEndpoint_cons_ae
    (clock : PartialInverseHazardClock State) {jump : State → State}
    (hjump : Measurable jump) (hcomplete : clock.CompletesFiniteHorizons jump)
    (remainingState : NNReal × State) :
    (fun headTail => clock.completedReplayEndpoint jump
        (remainingState, unitHazardCons headTail)) =ᵐ[
      unitHazardMeasure.prod unitHazardSequenceMeasure]
      (fun headTail => clock.completedReplayEndpoint jump
        (clock.cappedStepUpdate jump (remainingState, headTail.1),
          headTail.2)) := by
  let tailCompletes := fun headTail : NNReal × (ℕ → NNReal) =>
    ∃ count, clock.replayFinished jump
      (clock.cappedStepUpdate jump (remainingState, headTail.1), headTail.2)
      count
  have hmeasurable : MeasurableSet {headTail | tailCompletes headTail} := by
    simp only [tailCompletes, Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro count
    apply (measurableSet_singleton (0 : NNReal)).preimage
    exact (clock.measurable_replayPrefix hjump count).fst.comp
      ((clock.measurable_cappedStepUpdate hjump |>.comp
        ((measurable_const.prodMk measurable_fst))).prodMk measurable_snd)
  have htailCompletes : ∀ᵐ headTail ∂
      unitHazardMeasure.prod unitHazardSequenceMeasure,
      tailCompletes headTail := by
    apply (Measure.ae_prod_iff_ae_ae hmeasurable).2
    filter_upwards [] with head
    let next := clock.cappedStepUpdate jump (remainingState, head)
    filter_upwards [hcomplete next.1 next.2] with tail htail
    obtain ⟨count, terminal, hcount⟩ := htail
    refine ⟨count, ?_⟩
    unfold PartialInverseHazardClock.replayFinished
    rw [clock.replayPrefix_eq_executeHazards]
    rw [hcount]
  filter_upwards [htailCompletes] with headTail htail
  exact clock.completedReplayEndpoint_cons jump remainingState headTail htail

theorem PartialInverseHazardClock.measurable_completedReplayEndpoint
    (clock : PartialInverseHazardClock State) {jump : State → State}
    (hjump : Measurable jump) :
    Measurable (clock.completedReplayEndpoint jump) := by
  classical
  exact Measurable.find
    (fun count => (clock.measurable_replayPrefix hjump count).snd)
    (clock.measurableSet_completionSearch hjump)
    (clock.completionSearch_exists jump)

/-- Law-level first-step renewal equation for every completing partial inverse
clock: split the iid stream into an independent head and fresh tail, apply one
capped candidate, and continue from the updated remaining-time state. -/
theorem PartialInverseHazardClock.completedReplayEndpoint_firstStepLaw
    (clock : PartialInverseHazardClock State) {jump : State → State}
    (hjump : Measurable jump) (hcomplete : clock.CompletesFiniteHorizons jump)
    (remainingState : NNReal × State) :
    Measure.map
        (fun hazards => clock.completedReplayEndpoint jump
          (remainingState, hazards))
        unitHazardSequenceMeasure =
      Measure.map
        (fun headTail => clock.completedReplayEndpoint jump
          (clock.cappedStepUpdate jump (remainingState, headTail.1),
            headTail.2))
        (unitHazardMeasure.prod unitHazardSequenceMeasure) := by
  have hdirect : Measurable (fun hazards =>
      clock.completedReplayEndpoint jump (remainingState, hazards)) :=
    clock.measurable_completedReplayEndpoint hjump |>.comp
      (measurable_const.prodMk measurable_id)
  calc
    Measure.map
        (fun hazards => clock.completedReplayEndpoint jump
          (remainingState, hazards))
        unitHazardSequenceMeasure =
      Measure.map
        (fun headTail => clock.completedReplayEndpoint jump
          (remainingState, unitHazardCons headTail))
        (unitHazardMeasure.prod unitHazardSequenceMeasure) := by
      conv_lhs => rw [← unitHazardMeasure_prod_sequence_map_cons]
      rw [Measure.map_map hdirect measurable_unitHazardCons]
      rfl
    _ = _ := Measure.map_congr
      (clock.completedReplayEndpoint_cons_ae hjump hcomplete remainingState)

/-- Exact totalized finite-horizon kernel driven by an infinite iid hazard
stream. `CompletesFiniteHorizons` proves that its fallback branch is null. -/
noncomputable def PartialInverseHazardClock.completedHorizonKernel
    (clock : PartialInverseHazardClock State)
    (jump : State → State) (_hjump : Measurable jump)
    (horizon : NNReal) : Kernel State State :=
  Kernel.map
    (Kernel.prod Kernel.id
      (Kernel.const State unitHazardSequenceMeasure))
    (fun input => clock.completedReplayEndpoint jump
      ((horizon, input.1), input.2))

instance PartialInverseHazardClock.completedHorizonKernel.instIsMarkovKernel
    (clock : PartialInverseHazardClock State)
    (jump : State → State) (hjump : Measurable jump)
    (horizon : NNReal) :
    IsMarkovKernel (clock.completedHorizonKernel jump hjump horizon) := by
  unfold PartialInverseHazardClock.completedHorizonKernel
  apply Kernel.IsMarkovKernel.map
  exact clock.measurable_completedReplayEndpoint hjump |>.comp
    ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)

/-- Kernel-level first-step renewal equation. -/
theorem PartialInverseHazardClock.completedHorizonKernel_apply_firstStep
    (clock : PartialInverseHazardClock State) {jump : State → State}
    (hjump : Measurable jump) (hcomplete : clock.CompletesFiniteHorizons jump)
    (horizon : NNReal) (initial : State) :
    clock.completedHorizonKernel jump hjump horizon initial =
      Measure.map
        (fun headTail => clock.completedReplayEndpoint jump
          (clock.cappedStepUpdate jump
            ((horizon, initial), headTail.1), headTail.2))
        (unitHazardMeasure.prod unitHazardSequenceMeasure) := by
  unfold PartialInverseHazardClock.completedHorizonKernel
  have hendpoint : Measurable (fun input : State × (ℕ → NNReal) =>
      clock.completedReplayEndpoint jump
        ((horizon, input.1), input.2)) :=
    clock.measurable_completedReplayEndpoint hjump |>.comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  rw [Kernel.map_apply (f := fun input : State × (ℕ → NNReal) =>
      clock.completedReplayEndpoint jump
        ((horizon, input.1), input.2)) _ hendpoint,
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
    Measure.dirac_prod, Measure.map_map hendpoint (by fun_prop)]
  change Measure.map
      (fun hazards => clock.completedReplayEndpoint jump
        ((horizon, initial), hazards)) unitHazardSequenceMeasure = _
  exact clock.completedReplayEndpoint_firstStepLaw hjump hcomplete
    (horizon, initial)

/-- At zero horizon the completed inverse-clock kernel is exactly identity. -/
@[simp] theorem PartialInverseHazardClock.completedHorizonKernel_zero
    (clock : PartialInverseHazardClock State)
    (jump : State → State) (hjump : Measurable jump) :
    clock.completedHorizonKernel jump hjump 0 = Kernel.id := by
  ext initial event hevent
  unfold PartialInverseHazardClock.completedHorizonKernel
  have hendpoint : Measurable (fun input : State × (ℕ → NNReal) =>
      clock.completedReplayEndpoint jump ((0, input.1), input.2)) :=
    clock.measurable_completedReplayEndpoint hjump |>.comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  rw [Kernel.map_apply (f := fun input : State × (ℕ → NNReal) =>
      clock.completedReplayEndpoint jump ((0, input.1), input.2)) _ hendpoint,
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
    Measure.dirac_prod, Measure.map_map
      hendpoint
      (by fun_prop)]
  have hfun :
      (fun input : State × (ℕ → NNReal) =>
        clock.completedReplayEndpoint jump ((0, input.1), input.2)) ∘
          Prod.mk initial = fun _ => initial := by
    funext hazards
    exact clock.completedReplayEndpoint_zero jump initial hazards
  rw [hfun]
  rw [Measure.map_const, measure_univ, one_smul,
    Measure.dirac_apply' _ hevent]

/-- One restart candidate with a fresh unit-exponential hazard mark. -/
noncomputable def PartialInverseHazardClock.cappedStepKernel
    (clock : PartialInverseHazardClock State)
    (jump : State → State) (_hjump : Measurable jump) :
    Kernel (NNReal × State) (NNReal × State) :=
  Kernel.map
    (Kernel.prod Kernel.id (Kernel.const (NNReal × State) unitHazardMeasure))
    (clock.cappedStepUpdate jump)

instance PartialInverseHazardClock.cappedStepKernel.instIsMarkovKernel
    (clock : PartialInverseHazardClock State)
    (jump : State → State) (hjump : Measurable jump) :
    IsMarkovKernel (clock.cappedStepKernel jump hjump) := by
  unfold PartialInverseHazardClock.cappedStepKernel
  apply Kernel.IsMarkovKernel.map
  exact clock.measurable_cappedStepUpdate hjump

/-- Exact process truncated after at most `eventBudget` reachable events. Any
unused residual horizon is filled by deterministic flow after the final
candidate. -/
noncomputable def PartialInverseHazardClock.truncatedHorizonKernel
    (clock : PartialInverseHazardClock State)
    (jump : State → State) (hjump : Measurable jump)
    (horizon : NNReal) (eventBudget : ℕ) : Kernel State State :=
  Kernel.map
    (((clock.cappedStepKernel jump hjump) ^ eventBudget) ∘ₖ
      Kernel.deterministic (fun state => (horizon, state))
        (measurable_const.prodMk measurable_id))
    (fun remainingState =>
      clock.semiflow.flow remainingState.1 remainingState.2)

instance PartialInverseHazardClock.truncatedHorizonKernel.instIsMarkovKernel
    (clock : PartialInverseHazardClock State)
    (jump : State → State) (hjump : Measurable jump)
    (horizon : NNReal) (eventBudget : ℕ) :
    IsMarkovKernel
      (clock.truncatedHorizonKernel jump hjump horizon eventBudget) := by
  unfold PartialInverseHazardClock.truncatedHorizonKernel
  apply Kernel.IsMarkovKernel.map
  exact clock.semiflow.jointly_measurable_flow

/-- With zero event budget, truncation is exactly deterministic flow over the
whole horizon. -/
@[simp] theorem PartialInverseHazardClock.truncatedHorizonKernel_zero
    (clock : PartialInverseHazardClock State)
    (jump : State → State) (hjump : Measurable jump) (horizon : NNReal) :
    clock.truncatedHorizonKernel jump hjump horizon 0 =
      clock.semiflow.kernel horizon := by
  rw [PartialInverseHazardClock.truncatedHorizonKernel, pow_zero]
  change Kernel.map
      (Kernel.id ∘ₖ Kernel.deterministic (fun state => (horizon, state))
        (measurable_const.prodMk measurable_id))
      (fun remainingState =>
        clock.semiflow.flow remainingState.1 remainingState.2) = _
  rw [Kernel.id_comp]
  calc
    Kernel.map
        (Kernel.deterministic (fun state => (horizon, state))
          (measurable_const.prodMk measurable_id))
        (fun remainingState =>
          clock.semiflow.flow remainingState.1 remainingState.2) =
      Kernel.deterministic
        ((fun remainingState =>
          clock.semiflow.flow remainingState.1 remainingState.2) ∘
            fun state => (horizon, state))
        (clock.semiflow.jointly_measurable_flow.comp
          (measurable_const.prodMk measurable_id)) := by
            exact Kernel.deterministic_map
              (measurable_const.prodMk measurable_id)
              clock.semiflow.jointly_measurable_flow
    _ = clock.semiflow.kernel horizon := rfl

end Mcmc.PDMP
