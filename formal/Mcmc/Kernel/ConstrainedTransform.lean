import Mcmc.Kernel.LiftEvolveProject
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

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

/-- Scalar parameters strictly inside the unit interval. -/
abbrev OpenUnitInterval := { value : ℝ // value ∈ Set.Ioo 0 1 }

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

/-- Smooth unconstraining equivalence from `(0,1)` to `ℝ`. We use the
affine-artanh convention `y = artanh (2x-1)`; its inverse is
`x = (tanh y + 1)/2`. This differs from the usual logit only by a factor two
in unconstrained coordinates. -/
noncomputable def openUnitIntervalEquivReal : OpenUnitInterval ≃ ℝ where
  toFun value := Real.artanh (2 * value.1 - 1)
  invFun value := ⟨(Real.tanh value + 1) / 2, by
    constructor
    · have := Real.neg_one_lt_tanh value
      linarith
    · have := Real.tanh_lt_one value
      linarith⟩
  left_inv value := by
    apply Subtype.ext
    have hmem : 2 * value.1 - 1 ∈ Set.Ioo (-1 : ℝ) 1 := by
      constructor
      · linarith [value.2.1]
      · linarith [value.2.2]
    change (Real.tanh (Real.artanh (2 * value.1 - 1)) + 1) / 2 = value.1
    rw [Real.tanh_artanh hmem]
    ring
  right_inv value := by
    change Real.artanh (2 * ((Real.tanh value + 1) / 2) - 1) = value
    have harg : 2 * ((Real.tanh value + 1) / 2) - 1 = Real.tanh value := by
      ring
    rw [harg, Real.artanh_tanh]

theorem measurable_openUnitIntervalEquivReal :
    Measurable openUnitIntervalEquivReal := by
  change Measurable (fun value : OpenUnitInterval =>
    Real.artanh (2 * value.1 - 1))
  unfold Real.artanh
  fun_prop

theorem measurable_openUnitIntervalEquivReal_symm :
    Measurable openUnitIntervalEquivReal.symm := by
  change Measurable (fun value : ℝ =>
    (⟨(Real.tanh value + 1) / 2, by
      constructor
      · linarith [Real.neg_one_lt_tanh value]
      · linarith [Real.tanh_lt_one value]⟩ : OpenUnitInterval))
  have htanh : Measurable Real.tanh := by
    have heq : Real.tanh = fun x => Real.sinh x / Real.cosh x := by
      funext x
      exact Real.tanh_eq_sinh_div_cosh x
    rw [heq]
    exact Real.measurable_sinh.div Real.measurable_cosh
  apply Measurable.subtype_mk
  exact (htanh.add measurable_const).div_const 2

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

/-- Convenience specialization for open-unit parameters using the generated
artanh-affine convention. -/
noncomputable def openUnitTransformedKernel
    (transition : Kernel ℝ ℝ) : Kernel OpenUnitInterval OpenUnitInterval :=
  transformedKernel openUnitIntervalEquivReal
    measurable_openUnitIntervalEquivReal
    measurable_openUnitIntervalEquivReal_symm transition

instance openUnitTransformedKernel.instIsMarkovKernel
    (transition : Kernel ℝ ℝ) [IsMarkovKernel transition] :
    IsMarkovKernel (openUnitTransformedKernel transition) := by
  unfold openUnitTransformedKernel
  infer_instance

/-- An unconstrained kernel preserving the correctly pushed open-unit target
pulls back to an invariant constrained kernel. Any inverse Jacobian belongs in
the identification of `target.map openUnitIntervalEquivReal`. -/
theorem openUnitTransformedKernel_invariant
    (target : Measure OpenUnitInterval)
    (transition : Kernel ℝ ℝ)
    (hinvariant : transition.Invariant
      (target.map openUnitIntervalEquivReal)) :
    (openUnitTransformedKernel transition).Invariant target := by
  exact transformedKernel_invariant target openUnitIntervalEquivReal
    measurable_openUnitIntervalEquivReal
    measurable_openUnitIntervalEquivReal_symm transition hinvariant

end Mcmc.Kernel
