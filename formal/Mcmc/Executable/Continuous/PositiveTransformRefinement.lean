import Mcmc.Executable.Continuous.RestrictedRefinement
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Bounded numerical refinement for the positive-real log transform

The exact constrained-kernel theorem uses the measurable equivalence between
`(0,∞)` and `ℝ`.  This module supplies the local numerical statements needed
by the Julia `PositiveTransformedRWMH` client: guarded transport through `log`,
the explicit log-Jacobian, and transport back through `exp`.
-/

namespace Mcmc.Executable.Continuous

/-- On a domain bounded away from zero, the real logarithm is
`1/lower`-Lipschitz. -/
theorem log_approximates_log_of_lower
    {computed ideal error lower : ℝ}
    (hinput : Approximates computed ideal error)
    (hlower : 0 < lower)
    (hcomputed : lower ≤ computed) (hideal : lower ≤ ideal) :
    Approximates (Real.log computed) (Real.log ideal) (error / lower) := by
  rw [Approximates] at hinput ⊢
  have hlipschitz :
      |Real.log computed - Real.log ideal| ≤
        lower⁻¹ * |computed - ideal| := by
    have hmean := Convex.norm_image_sub_le_of_norm_deriv_le
      (s := Set.Ici lower) (f := Real.log)
      (fun x hx => (Real.hasDerivAt_log
        (ne_of_gt (lt_of_lt_of_le hlower hx))).differentiableAt)
      (fun x hx => by
        rw [Real.deriv_log, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr (lt_of_lt_of_le hlower hx))]
        exact (inv_le_inv₀ (lt_of_lt_of_le hlower hx) hlower).2 hx)
      (convex_Ici lower) hideal hcomputed
    simpa [Real.norm_eq_abs, abs_sub_comm] using hmean
  calc
    |Real.log computed - Real.log ideal| ≤
        lower⁻¹ * |computed - ideal| := hlipschitz
    _ ≤ lower⁻¹ * error :=
      mul_le_mul_of_nonneg_left hinput (inv_nonneg.mpr hlower.le)
    _ = error / lower := by
      rw [div_eq_mul_inv]
      ring

/-- Backend-local `log` error composed with argument transport on a positive
domain. -/
theorem log_backend_approximates_of_lower
    {computedLog computed ideal localError inputError lower : ℝ}
    (hlocal : Approximates computedLog (Real.log computed) localError)
    (hinput : Approximates computed ideal inputError)
    (hlower : 0 < lower)
    (hcomputed : lower ≤ computed) (hideal : lower ≤ ideal) :
    Approximates computedLog (Real.log ideal)
      (localError + inputError / lower) :=
  hlocal.trans
    (log_approximates_log_of_lower hinput hlower hcomputed hideal)

/-- Adding the unconstrained coordinate is exactly the Jacobian correction
for `x = exp(y)`. Callback error and coordinate error add. -/
theorem positiveTransformedLogDensity_approximates
    {computedLogDensity idealLogDensity computedLogCoordinate
      idealLogCoordinate callbackError coordinateError : ℝ}
    (hcallback : Approximates computedLogDensity idealLogDensity callbackError)
    (hcoordinate : Approximates computedLogCoordinate idealLogCoordinate
      coordinateError) :
    Approximates
      (computedLogDensity + computedLogCoordinate)
      (idealLogDensity + idealLogCoordinate)
      (callbackError + coordinateError) :=
  hcallback.add hcoordinate

/-- Back-transform a certified log-coordinate through a backend exponential
on an explicit upper-bounded region. -/
theorem positiveInverseTransform_approximates
    {computedPositive computedLog idealLog localError logError upper : ℝ}
    (hlocal : Approximates computedPositive (Real.exp computedLog) localError)
    (hlog : Approximates computedLog idealLog logError)
    (hcomputed : computedLog ≤ upper) (hideal : idealLog ≤ upper) :
    Approximates computedPositive (Real.exp idealLog)
      (localError + Real.exp upper * logError) :=
  exp_backend_approximates_of_le hlocal hlog hcomputed hideal

end Mcmc.Executable.Continuous
