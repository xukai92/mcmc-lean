import Mcmc.PDMP.EventExecution
import Mcmc.PDMP.GeneralUniformization
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Tactic

/-!
# Bounded state-dependent PDMP event simulation

This module gives an exact one-candidate thinning construction. A homogeneous
positive-rate clock supplies an exponential wait; the process follows a
jointly measurable semiflow for that wait and then accepts the supplied jump
with probability `rate/clockRate`, otherwise recording a virtual self-event.

Iteration gives any fixed finite number of clock candidates. Stopping at a
fixed real horizon and proving nonexplosion for unbounded intensities remain
separate obligations.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace Mcmc.PDMP

variable {State : Type*} [MeasurableSpace State]

/-- A semiflow whose time and state arguments are jointly measurable. This is
the extra condition needed when the elapsed time is itself random. -/
structure JointlyMeasurableSemiflow (State : Type*) [MeasurableSpace State]
    extends MeasurableSemiflow State where
  jointly_measurable_flow : Measurable (fun p : NNReal × State => flow p.1 p.2)

/-- A strictly positive homogeneous proposal clock. -/
structure HomogeneousClock where
  rate : NNReal
  positive : 0 < rate

/-- Probability law of a nonnegative exponential waiting time. -/
noncomputable def HomogeneousClock.waitMeasure (clock : HomogeneousClock) :
    Measure NNReal :=
  Measure.map Real.toNNReal (expMeasure (clock.rate : ℝ))

instance HomogeneousClock.waitMeasure.instIsProbabilityMeasure
    (clock : HomogeneousClock) : IsProbabilityMeasure clock.waitMeasure := by
  letI : IsProbabilityMeasure (expMeasure (clock.rate : ℝ)) :=
    isProbabilityMeasure_expMeasure (by exact_mod_cast clock.positive)
  unfold HomogeneousClock.waitMeasure
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- Draw an exponential wait and follow the deterministic flow for that
duration. -/
noncomputable def JointlyMeasurableSemiflow.randomFlowKernel
    (semiflow : JointlyMeasurableSemiflow State)
    (clock : HomogeneousClock) : Kernel State State :=
  Kernel.map
    (Kernel.prod Kernel.id (Kernel.const State clock.waitMeasure))
    (fun p : State × NNReal => semiflow.flow p.2 p.1)

instance JointlyMeasurableSemiflow.randomFlowKernel.instIsMarkovKernel
    (semiflow : JointlyMeasurableSemiflow State)
    (clock : HomogeneousClock) :
    IsMarkovKernel (semiflow.randomFlowKernel clock) := by
  unfold JointlyMeasurableSemiflow.randomFlowKernel
  apply Kernel.IsMarkovKernel.map
  exact semiflow.jointly_measurable_flow.comp
    (measurable_snd.prodMk measurable_fst)

/-- Data for exact bounded-rate thinning along a deterministic semiflow. -/
structure ThinnedFlowSimulator (State : Type*) [MeasurableSpace State] where
  semiflow : JointlyMeasurableSemiflow State
  mechanism : JumpMechanism State
  clock : HomogeneousClock
  rate_le_clock : ∀ x, mechanism.rate x ≤ clock.rate

/-- One clock candidate: draw its wait, flow to the candidate location, then
accept the genuine event or take the virtual self-event. -/
noncomputable def ThinnedFlowSimulator.candidateKernel
    (simulator : ThinnedFlowSimulator State) : Kernel State State :=
  simulator.mechanism.uniformizedKernel simulator.clock.rate ∘ₖ
    simulator.semiflow.randomFlowKernel simulator.clock

instance ThinnedFlowSimulator.candidateKernel.instIsMarkovKernel
    (simulator : ThinnedFlowSimulator State) :
    IsMarkovKernel simulator.candidateKernel := by
  letI : IsMarkovKernel
      (simulator.mechanism.uniformizedKernel simulator.clock.rate) :=
    simulator.mechanism.uniformizedKernel_isMarkov simulator.clock.rate
      simulator.clock.positive simulator.rate_le_clock
  unfold ThinnedFlowSimulator.candidateKernel
  infer_instance

/-- Kernel after a fixed finite number of homogeneous clock candidates. -/
noncomputable def ThinnedFlowSimulator.iterate
    (simulator : ThinnedFlowSimulator State) (candidateCount : ℕ) :
    Kernel State State :=
  simulator.candidateKernel ^ candidateCount

instance ThinnedFlowSimulator.iterate.instIsMarkovKernel
    (simulator : ThinnedFlowSimulator State) (candidateCount : ℕ) :
    IsMarkovKernel (simulator.iterate candidateCount) := by
  unfold ThinnedFlowSimulator.iterate
  infer_instance

@[simp] theorem ThinnedFlowSimulator.iterate_zero
    (simulator : ThinnedFlowSimulator State) :
    simulator.iterate 0 = Kernel.id := rfl

/-- Fixed candidate counts compose by addition. -/
theorem ThinnedFlowSimulator.iterate_add
    (simulator : ThinnedFlowSimulator State) (m n : ℕ) :
    simulator.iterate (m + n) =
      simulator.iterate m ∘ₖ simulator.iterate n := by
  exact Kernel.pow_add simulator.candidateKernel m n

end Mcmc.PDMP
