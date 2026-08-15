import Mcmc.PDMP.GeneralUniformization
import Mcmc.Kernel.LiftEvolveProject
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompMap
import Mathlib.Tactic

/-!
# Deterministic semiflows between PDMP events

This module represents the deterministic part of a piecewise-deterministic
process independently of its jump clock. A measurable semiflow produces a
Markov deterministic kernel at every elapsed time and satisfies the exact
kernel semigroup law. A supplied measure-preservation certificate yields
invariance, but no such certificate is assumed for BPS or Zig-Zag: in those
algorithms flow and jump generator terms generally cancel only in combination.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory

namespace Mcmc.PDMP

variable {State : Type*} [MeasurableSpace State]

/-- A measurable action of nonnegative elapsed time on a state space. -/
structure MeasurableSemiflow (State : Type*) [MeasurableSpace State] where
  flow : NNReal → State → State
  measurable_flow : ∀ t, Measurable (flow t)
  flow_zero : flow 0 = id
  flow_add : ∀ t u, flow (t + u) = flow u ∘ flow t

/-- Deterministic Markov kernel obtained by evolving for time `t`. -/
noncomputable def MeasurableSemiflow.kernel
    (semiflow : MeasurableSemiflow State) (t : NNReal) : Kernel State State :=
  Kernel.deterministic (semiflow.flow t) (semiflow.measurable_flow t)

instance MeasurableSemiflow.kernel.instIsMarkovKernel
    (semiflow : MeasurableSemiflow State) (t : NNReal) :
    IsMarkovKernel (semiflow.kernel t) := by
  unfold MeasurableSemiflow.kernel
  infer_instance

/-- At zero elapsed time the semiflow kernel is the identity kernel. -/
@[simp] theorem MeasurableSemiflow.kernel_zero
    (semiflow : MeasurableSemiflow State) :
    semiflow.kernel 0 = Kernel.id := by
  unfold MeasurableSemiflow.kernel Kernel.id
  exact Kernel.deterministic_congr semiflow.flow_zero

/-- Exact Chapman--Kolmogorov law for deterministic flow kernels. -/
theorem MeasurableSemiflow.kernel_add
    (semiflow : MeasurableSemiflow State) (t u : NNReal) :
    semiflow.kernel (t + u) = semiflow.kernel u ∘ₖ semiflow.kernel t := by
  unfold MeasurableSemiflow.kernel
  rw [Kernel.deterministic_comp_deterministic]
  exact Kernel.deterministic_congr (semiflow.flow_add t u)

/-- A target preserved by every deterministic flow map is invariant under
every flow kernel. -/
theorem MeasurableSemiflow.kernel_invariant
    (semiflow : MeasurableSemiflow State) (target : Measure State)
    (hpreserving : ∀ t, MeasurePreserving (semiflow.flow t) target target)
    (t : NNReal) : (semiflow.kernel t).Invariant target :=
  Mcmc.Kernel.deterministic_invariant_of_measurePreserving target
    (semiflow.measurable_flow t) (hpreserving t)

/-- Evolve deterministically for one waiting time and then apply the event
jump kernel. -/
noncomputable def MeasurableSemiflow.flowThenJump
    (semiflow : MeasurableSemiflow State) (jump : Kernel State State)
    (wait : NNReal) : Kernel State State :=
  jump ∘ₖ semiflow.kernel wait

instance MeasurableSemiflow.flowThenJump.instIsMarkovKernel
    (semiflow : MeasurableSemiflow State) (jump : Kernel State State)
    [IsMarkovKernel jump] (wait : NNReal) :
    IsMarkovKernel (semiflow.flowThenJump jump wait) := by
  unfold MeasurableSemiflow.flowThenJump
  infer_instance

/-- If flow and jump separately preserve a target, one event segment does as
well. This theorem is useful for constant-rate pure transport models; it is
not the generator-cancellation argument required by general BPS/Zig-Zag. -/
theorem MeasurableSemiflow.flowThenJump_invariant
    (semiflow : MeasurableSemiflow State) (jump : Kernel State State)
    (target : Measure State)
    (hflow : ∀ t, (semiflow.kernel t).Invariant target)
    (hjump : jump.Invariant target) (wait : NNReal) :
    (semiflow.flowThenJump jump wait).Invariant target :=
  hjump.comp (hflow wait)

end Mcmc.PDMP
