import Mcmc.Kernel.LiftEvolveProject
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exact constrained-coordinate transforms

Inference may run in unconstrained coordinates only after the target measure
has been pushed through the same measurable equivalence. This module conjugates
a kernel by that equivalence and transports invariance back. Any density-level
Jacobian is therefore an obligation in identifying the pushed target, not a
factor that can be silently omitted from the transition.
-/

open MeasureTheory
open scoped ProbabilityTheory

namespace Mcmc.Kernel

open ProbabilityTheory

variable {Constrained Unconstrained : Type*}
  [MeasurableSpace Constrained] [MeasurableSpace Unconstrained]

/-- Positive scalar parameters, used by scale/rate/variance constraints. -/
abbrev PositiveReal := { value : ℝ // 0 < value }

/-- The standard log/exp unconstraining equivalence for a positive scalar. -/
noncomputable def positiveRealEquivReal : PositiveReal ≃ ℝ where
  toFun value := Real.log value.1
  invFun value := ⟨Real.exp value, Real.exp_pos value⟩
  left_inv value := by
    apply Subtype.ext
    exact Real.exp_log value.2
  right_inv value := Real.log_exp value

theorem measurable_positiveRealEquivReal :
    Measurable positiveRealEquivReal := by
  simpa [positiveRealEquivReal] using Real.continuous_log'.measurable

theorem measurable_positiveRealEquivReal_symm :
    Measurable positiveRealEquivReal.symm := by
  simpa [positiveRealEquivReal] using Real.continuous_exp.measurable.subtype_mk

/-- Lift through `transform`, evolve in unconstrained coordinates, and map
back through the exact inverse. -/
noncomputable def transformedKernel
    (transform : Constrained ≃ Unconstrained)
    (htransform : Measurable transform)
    (hinverse : Measurable transform.symm)
    (transition : Kernel Unconstrained Unconstrained) :
    Kernel Constrained Constrained :=
  liftEvolveProject
    (ProbabilityTheory.Kernel.deterministic transform htransform)
    transition transform.symm hinverse

instance transformedKernel_isMarkovKernel
    (transform : Constrained ≃ Unconstrained)
    (htransform : Measurable transform)
    (hinverse : Measurable transform.symm)
    (transition : Kernel Unconstrained Unconstrained)
    [IsMarkovKernel transition] :
    IsMarkovKernel (transformedKernel transform htransform hinverse transition) :=
  by
    unfold transformedKernel
    infer_instance

/-- Invariance transports exactly through a measurable coordinate
equivalence. The unconstrained target is `target.map transform`, including any
Jacobian required by a density representation. -/
theorem transformedKernel_invariant
    (target : Measure Constrained)
    (transform : Constrained ≃ Unconstrained)
    (htransform : Measurable transform)
    (hinverse : Measurable transform.symm)
    (transition : Kernel Unconstrained Unconstrained)
    (hinvariant : transition.Invariant (target.map transform)) :
    (transformedKernel transform htransform hinverse transition).Invariant
      target := by
  apply liftEvolveProject_invariant target (target.map transform)
  · exact Measure.deterministic_comp_eq_map htransform
  · exact hinvariant
  · rw [Measure.map_map hinverse htransform]
    simp

end Mcmc.Kernel
