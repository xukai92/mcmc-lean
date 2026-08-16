import Mcmc.Kernel.Slice

/-!
# A continuous bounded-uniform slice sampler

This example instantiates the exact general-state slice construction on the
uniform probability measure over `(-2,2]`. The height weight is constant, so
the ideal horizontal conditional redraws from the whole bounded support. This
is the mathematical client exercised by the Julia bounded-slice uniform tests;
no Float64 or finite-retry refinement is asserted here.
-/

open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

namespace Mcmc.Examples.BoundedUniformSlice

open ProbabilityTheory Mcmc.Kernel

/-- Uniform probability measure on `(-2,2]`. -/
noncomputable def target : Measure ℝ :=
  (4 : ENNReal)⁻¹ • volume.restrict (Ioc (-2) 2)

instance target.instIsProbabilityMeasure : IsProbabilityMeasure target := by
  constructor
  unfold target
  rw [Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Ioc]
  norm_num [ENNReal.smul_def]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

/-- Constant vertical extent for the bounded-uniform target. -/
def weight (_ : ℝ) : ℝ := 1

theorem measurable_weight : Measurable weight := measurable_const

theorem weight_pos (x : ℝ) : 0 < weight x := by simp [weight]

/-- Exact disintegrated continuous slice transition. -/
noncomputable def sampler : Kernel ℝ ℝ :=
  targetDisintegratedSliceSampler target weight measurable_weight weight_pos

/-- The exact continuous sampler preserves the bounded-uniform target. -/
theorem sampler_invariant : sampler.Invariant target :=
  targetDisintegratedSliceSampler_invariant target weight measurable_weight
    weight_pos

end Mcmc.Examples.BoundedUniformSlice
