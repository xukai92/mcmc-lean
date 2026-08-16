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

/-- Execute a supplied finite candidate-wait list up to a fixed horizon. A
candidate whose wait exceeds the remaining horizon is ignored and the process
flows exactly to the horizon; after the list is exhausted, the residual time
is also filled by deterministic flow. -/
noncomputable def ThinnedFlowSimulator.executeUntil
    (simulator : ThinnedFlowSimulator State) :
    NNReal → List NNReal → Kernel State State
  | horizon, [] => simulator.semiflow.kernel horizon
  | horizon, wait :: waits =>
      if wait ≤ horizon then
        simulator.executeUntil (horizon - wait) waits ∘ₖ
          (simulator.mechanism.uniformizedKernel simulator.clock.rate ∘ₖ
            simulator.semiflow.kernel wait)
      else
        simulator.semiflow.kernel horizon

instance ThinnedFlowSimulator.executeUntil.instIsMarkovKernel
    (simulator : ThinnedFlowSimulator State)
    (horizon : NNReal) (waits : List NNReal) :
    IsMarkovKernel (simulator.executeUntil horizon waits) := by
  letI : IsMarkovKernel
      (simulator.mechanism.uniformizedKernel simulator.clock.rate) :=
    simulator.mechanism.uniformizedKernel_isMarkov simulator.clock.rate
      simulator.clock.positive simulator.rate_le_clock
  induction waits generalizing horizon with
  | nil =>
      simp only [ThinnedFlowSimulator.executeUntil]
      infer_instance
  | cons wait waits ih =>
      rw [ThinnedFlowSimulator.executeUntil]
      split
      · letI : IsMarkovKernel
            (simulator.executeUntil (horizon - wait) waits) :=
          ih (horizon - wait)
        infer_instance
      · infer_instance

@[simp] theorem ThinnedFlowSimulator.executeUntil_nil
    (simulator : ThinnedFlowSimulator State) (horizon : NNReal) :
    simulator.executeUntil horizon [] = simulator.semiflow.kernel horizon := rfl

/-- A first candidate beyond the horizon has no effect; the result is exactly
the deterministic flow to the horizon. -/
theorem ThinnedFlowSimulator.executeUntil_of_horizon_lt
    (simulator : ThinnedFlowSimulator State) (horizon wait : NNReal)
    (waits : List NNReal) (h : horizon < wait) :
    simulator.executeUntil horizon (wait :: waits) =
      simulator.semiflow.kernel horizon := by
  rw [ThinnedFlowSimulator.executeUntil, if_neg (not_le.mpr h)]

/-- If the first candidate occurs within the horizon, execution factors into
that flow/thinning event followed by execution over the residual horizon. -/
theorem ThinnedFlowSimulator.executeUntil_of_le
    (simulator : ThinnedFlowSimulator State) (horizon wait : NNReal)
    (waits : List NNReal) (h : wait ≤ horizon) :
    simulator.executeUntil horizon (wait :: waits) =
      simulator.executeUntil (horizon - wait) waits ∘ₖ
        (simulator.mechanism.uniformizedKernel simulator.clock.rate ∘ₖ
          simulator.semiflow.kernel wait) := by
  rw [ThinnedFlowSimulator.executeUntil, if_pos h]

/-- Conditional finite-candidate execution preserves a target whenever every
flow segment and the embedded uniformized event kernel preserve it. This
applies to arbitrary supplied waits, including candidates beyond the horizon;
it is distinct from proving that a state-dependent Poisson schedule has the
required target law. -/
theorem ThinnedFlowSimulator.executeUntil_invariant
    (simulator : ThinnedFlowSimulator State) (target : Measure State)
    (hflow : ∀ time, (simulator.semiflow.kernel time).Invariant target)
    (hevent : (simulator.mechanism.uniformizedKernel
      simulator.clock.rate).Invariant target) :
    ∀ (horizon : NNReal) (waits : List NNReal),
      (simulator.executeUntil horizon waits).Invariant target := by
  intro horizon waits
  induction waits generalizing horizon with
  | nil =>
      exact hflow horizon
  | cons wait waits ih =>
      rw [ThinnedFlowSimulator.executeUntil]
      split
      · exact (ih (horizon - wait)).comp (hevent.comp (hflow wait))
      · exact hflow horizon

/-- Poisson law of the number of homogeneous clock candidates on a fixed
horizon. -/
noncomputable def ThinnedFlowSimulator.candidateCountMeasure
    (simulator : ThinnedFlowSimulator State) (horizon : NNReal) : Measure ℕ :=
  poissonMeasure (simulator.clock.rate * horizon)

instance ThinnedFlowSimulator.candidateCountMeasure.instIsProbabilityMeasure
    (simulator : ThinnedFlowSimulator State) (horizon : NNReal) :
    IsProbabilityMeasure (simulator.candidateCountMeasure horizon) := by
  unfold ThinnedFlowSimulator.candidateCountMeasure
  infer_instance

/-- A bounded homogeneous proposal clock has only finitely many candidates on
every finite horizon. -/
theorem ThinnedFlowSimulator.candidateCount_finite_ae
    (simulator : ThinnedFlowSimulator State) (horizon : NNReal) :
    ∀ᵐ n ∂simulator.candidateCountMeasure horizon,
      ∃ bound : ℕ, n ≤ bound := by
  unfold ThinnedFlowSimulator.candidateCountMeasure
  exact poisson_count_finite_ae (simulator.clock.rate * horizon)

end Mcmc.PDMP
