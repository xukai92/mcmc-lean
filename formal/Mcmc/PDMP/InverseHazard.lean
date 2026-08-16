import Mcmc.PDMP.EventSimulation
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
open scoped NNReal ProbabilityTheory

namespace Mcmc.PDMP

variable {State : Type*} [MeasurableSpace State]

/-- Canonical unit-exponential law for integrated hazard marks. -/
noncomputable def unitHazardMeasure : Measure NNReal :=
  (HomogeneousClock.mk 1 zero_lt_one).waitMeasure

instance unitHazardMeasure.instIsProbabilityMeasure :
    IsProbabilityMeasure unitHazardMeasure := by
  unfold unitHazardMeasure
  infer_instance

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

/-- Infinite iid unit-exponential hazard stream for repeated inverse-clock
restart. -/
noncomputable def unitHazardSequenceMeasure : Measure (ℕ → NNReal) :=
  Measure.infinitePi (fun _ : ℕ => unitHazardMeasure)

instance unitHazardSequenceMeasure.instIsProbabilityMeasure :
    IsProbabilityMeasure unitHazardSequenceMeasure := by
  unfold unitHazardSequenceMeasure
  infer_instance

/-- First `count` marks of an infinite hazard stream, in execution order. -/
def hazardPrefix (count : ℕ) (hazards : ℕ → NNReal) : List NNReal :=
  List.ofFn fun index : Fin count => hazards index

@[simp] theorem hazardPrefix_zero (hazards : ℕ → NNReal) :
    hazardPrefix 0 hazards = [] := by
  simp [hazardPrefix]

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
