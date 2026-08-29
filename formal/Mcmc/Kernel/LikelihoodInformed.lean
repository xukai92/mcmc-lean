import Mcmc.Kernel.Invariant
import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# Fixed likelihood-informed split kernels

A likelihood-informed transition alternates a target-invariant update in an
active subspace with a target-invariant reference-aware update in its
complement.  This module records the exact compositional theorem.  Concrete
clients must separately establish invariance of the conditional active HMC
step and of the complement pCN Metropolis step.
-/

open MeasureTheory
open scoped ProbabilityTheory

namespace Mcmc.Kernel

open ProbabilityTheory

variable {State : Type*} [MeasurableSpace State]

/-- Apply the active transition and then the Gaussian-reference complement
transition. -/
noncomputable def likelihoodInformedSplit
    (active complement : Kernel State State) : Kernel State State :=
  complement ∘ₖ active

instance likelihoodInformedSplit_isMarkovKernel
    (active complement : Kernel State State)
    [IsMarkovKernel active] [IsMarkovKernel complement] :
    IsMarkovKernel (likelihoodInformedSplit active complement) := by
  unfold likelihoodInformedSplit
  infer_instance

/-- Two exact component updates with the same invariant target compose into
an exact likelihood-informed split transition. -/
theorem likelihoodInformedSplit_invariant
    (target : Measure State) (active complement : Kernel State State)
    (hactive : active.Invariant target)
    (hcomplement : complement.Invariant target) :
    (likelihoodInformedSplit active complement).Invariant target := by
  exact hcomplement.comp hactive

end Mcmc.Kernel
