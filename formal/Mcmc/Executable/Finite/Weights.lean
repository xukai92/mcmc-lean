import Mcmc.Finite.MeasureKernel
import Mathlib.Probability.Distributions.Uniform

/-!
# Exact natural weights for executable finite samplers

This module supplies the exact, executable input representation for the first
sampler milestone.  Natural weights are normalized only in their mathematical
semantics; execution can operate entirely with natural-number totals and a
uniform draw below a positive bound.
-/

open scoped BigOperators ENNReal

namespace Mcmc.Executable.Finite

/-- Natural weights on `Fin n` with strictly positive total mass. -/
structure NatWeights (n : ℕ) where
  weight : Fin n → ℕ
  total_pos : 0 < ∑ i, weight i

namespace NatWeights

variable {n : ℕ}

/-- Total unnormalized mass. -/
def total (w : NatWeights n) : ℕ :=
  ∑ i, w.weight i

theorem total_positive (w : NatWeights n) : 0 < w.total :=
  w.total_pos

theorem total_ne_zero (w : NatWeights n) : w.total ≠ 0 :=
  Nat.ne_of_gt w.total_pos

/-- Exact normalized probability mass associated with natural weights. -/
noncomputable def toPMF (w : NatWeights n) : PMF (Fin n) :=
  PMF.ofFintype
    (fun i ↦ (w.weight i : ℝ≥0∞) / (w.total : ℝ≥0∞)) (by
      change (∑ i ∈ Finset.univ,
        (w.weight i : ℝ≥0∞) / (w.total : ℝ≥0∞)) = 1
      simp_rw [ENNReal.div_eq_inv_mul]
      rw [← Finset.mul_sum]
      simp only [← Nat.cast_sum, total]
      exact ENNReal.inv_mul_cancel (by exact_mod_cast w.total_ne_zero)
        ENNReal.coe_ne_top)

@[simp]
theorem toPMF_apply (w : NatWeights n) (i : Fin n) :
    w.toPMF i = (w.weight i : ℝ≥0∞) / (w.total : ℝ≥0∞) :=
  rfl

/-- Real-valued distribution used by the existing elementary finite theory. -/
noncomputable def toDistribution (w : NatWeights n) :
    Mcmc.Finite.MarkovKernel.Distribution (Fin n) where
  mass i := (w.weight i : ℝ) / w.total
  nonneg i := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  sum_mass := by
    rw [← Finset.sum_div, ← Nat.cast_sum]
    exact div_self (by exact_mod_cast w.total_ne_zero)

@[simp]
theorem toDistribution_mass (w : NatWeights n) (i : Fin n) :
    w.toDistribution.mass i = (w.weight i : ℝ) / w.total :=
  rfl

/-- The new executable representation has exactly the same PMF semantics as
the existing finite distribution embedding. -/
theorem toDistribution_toPMF (w : NatWeights n) :
    w.toDistribution.toPMF = w.toPMF := by
  ext i
  rw [Mcmc.Finite.MarkovKernel.Distribution.toPMF_apply, toPMF_apply]
  rw [toDistribution_mass, ENNReal.ofReal_div_of_pos]
  · simp only [ENNReal.ofReal_natCast]
  · exact_mod_cast w.total_pos

/-- A positive natural bound for the primitive uniform draw. -/
structure DrawBound where
  upper : ℕ
  upper_pos : 0 < upper

namespace DrawBound

/-- Exact semantics of drawing a natural number uniformly below the bound. -/
noncomputable def pmf (bound : DrawBound) : PMF (Fin bound.upper) :=
  letI : Nonempty (Fin bound.upper) := Fin.pos_iff_nonempty.mp bound.upper_pos
  PMF.uniformOfFintype (Fin bound.upper)

@[simp]
theorem pmf_apply (bound : DrawBound) (i : Fin bound.upper) :
    bound.pmf i = (bound.upper : ℝ≥0∞)⁻¹ := by
  letI : Nonempty (Fin bound.upper) := Fin.pos_iff_nonempty.mp bound.upper_pos
  rw [pmf, PMF.uniformOfFintype_apply]
  simp

end DrawBound
end NatWeights
end Mcmc.Executable.Finite
