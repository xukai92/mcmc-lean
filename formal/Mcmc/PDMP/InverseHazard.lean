import Mcmc.PDMP.EventSimulation

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

end Mcmc.PDMP
