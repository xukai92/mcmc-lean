import Mcmc.Executable.Continuous.PositiveTransformRefinement
import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
# Bounded numerical refinement for the open-unit transform

These lemmas compose backend certificates for the exact convention
`y = artanh (2x-1)`, `x = (tanh y+1)/2`, and inverse log-Jacobian
`log (1-tanh(y)^2)-log 2`.  Primitive `artanh`, `tanh`, and `log` error
certificates remain properties of the concrete numerical backend.
-/

namespace Mcmc.Executable.Continuous

/-- Affine preprocessing of an approximate constrained coordinate doubles
its absolute error. -/
theorem openUnitForwardArgument_approximates
    {computed ideal error : ℝ}
    (hinput : Approximates computed ideal error) :
    Approximates (2 * computed - 1) (2 * ideal - 1) (2 * error) := by
  rw [Approximates] at hinput ⊢
  rw [show 2 * computed - 1 - (2 * ideal - 1) =
      2 * (computed - ideal) by ring, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left hinput (by norm_num)

/-- Compose local backend `artanh` error with a certified transport error
between the computed and ideal affine arguments. -/
theorem openUnitForwardTransform_approximates
    {computedArtanh computedArgument idealArgument localError transportError : ℝ}
    (hlocal : Approximates computedArtanh
      (Real.artanh computedArgument) localError)
    (htransport : Approximates (Real.artanh computedArgument)
      (Real.artanh idealArgument) transportError) :
    Approximates computedArtanh (Real.artanh idealArgument)
      (localError + transportError) :=
  hlocal.trans htransport

/-- Once a backend `tanh` result is certified, the affine inverse transform
divides its error by two. -/
theorem openUnitInverseTransform_approximates
    {computedTanh idealTanh error : ℝ}
    (htanh : Approximates computedTanh idealTanh error) :
    Approximates ((computedTanh + 1) / 2) ((idealTanh + 1) / 2)
      (error / 2) := by
  rw [Approximates] at htanh ⊢
  rw [show (computedTanh + 1) / 2 - (idealTanh + 1) / 2 =
      (computedTanh - idealTanh) / 2 by ring, abs_div,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact div_le_div_of_nonneg_right htanh (by norm_num)

/-- Squaring two certified `tanh` values propagates error with the usual
sum-of-magnitudes factor. -/
theorem oneSubSquare_approximates
    {computed ideal error computedBound idealBound : ℝ}
    (hvalue : Approximates computed ideal error)
    (hcomputed : |computed| ≤ computedBound)
    (hideal : |ideal| ≤ idealBound) :
    Approximates (1 - computed ^ 2) (1 - ideal ^ 2)
      ((computedBound + idealBound) * error) := by
  rw [Approximates] at hvalue ⊢
  rw [show 1 - computed ^ 2 - (1 - ideal ^ 2) =
      (ideal - computed) * (ideal + computed) by ring, abs_mul, abs_sub_comm]
  calc
    |computed - ideal| * |ideal + computed| ≤
        |computed - ideal| * (|ideal| + |computed|) :=
      mul_le_mul_of_nonneg_left (abs_add_le ideal computed) (abs_nonneg _)
    _ ≤ error * (idealBound + computedBound) :=
      mul_le_mul hvalue (add_le_add hideal hcomputed)
        (add_nonneg (abs_nonneg _) (abs_nonneg _))
        ((abs_nonneg (computed - ideal)).trans hvalue)
    _ = (computedBound + idealBound) * error := by ring

/-- Compose a backend logarithm certificate with the transported positive
`1-tanh²` argument. The lower guard makes the logarithm conditioning
explicit. -/
theorem openUnitLogJacobianCore_approximates
    {computedLog computedGap idealGap localError gapError lower : ℝ}
    (hlocal : Approximates computedLog (Real.log computedGap) localError)
    (hgap : Approximates computedGap idealGap gapError)
    (hlower : 0 < lower)
    (hcomputed : lower ≤ computedGap) (hideal : lower ≤ idealGap) :
    Approximates computedLog (Real.log idealGap)
      (localError + gapError / lower) :=
  log_backend_approximates_of_lower hlocal hgap hlower hcomputed hideal

/-- Subtracting a certified backend value for `log 2` completes the inverse
log-Jacobian certificate. -/
theorem openUnitLogJacobian_approximates
    {computedCore idealCore computedLogTwo logTwoError coreError : ℝ}
    (hcore : Approximates computedCore idealCore coreError)
    (hlogTwo : Approximates computedLogTwo (Real.log 2) logTwoError) :
    Approximates (computedCore - computedLogTwo)
      (idealCore - Real.log 2) (coreError + logTwoError) :=
  hcore.sub hlogTwo

end Mcmc.Executable.Continuous
