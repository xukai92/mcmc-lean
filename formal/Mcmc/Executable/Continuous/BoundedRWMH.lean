import Mcmc.Executable.Continuous.NumericalRefinement
import Mcmc.Executable.Continuous.RWMH
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Bounded numerical refinement for scalar RWMH

This module gives a backend-independent, finite-error refinement theorem.  It
separates arithmetic and callback error bounds from the discontinuous
accept/reject comparison. Exact branch agreement is obtained whenever the
ideal uniform/threshold margin is larger than the accumulated numerical error.
-/

namespace Mcmc.Executable.Continuous

/-- `computed` represents `ideal` with absolute error at most `error`. -/
def Approximates (computed ideal error : ℝ) : Prop :=
  |computed - ideal| ≤ error

theorem Approximates.nonneg {computed ideal error : ℝ}
    (h : Approximates computed ideal error) : 0 ≤ error :=
  (abs_nonneg _).trans h

theorem Approximates.refl (value : ℝ) : Approximates value value 0 := by
  simp [Approximates]

theorem Approximates.add {aHat a bHat b ea eb : ℝ}
    (ha : Approximates aHat a ea) (hb : Approximates bHat b eb) :
    Approximates (aHat + bHat) (a + b) (ea + eb) := by
  rw [Approximates, add_sub_add_comm]
  exact (abs_add_le _ _).trans (add_le_add ha hb)

theorem Approximates.sub {aHat a bHat b ea eb : ℝ}
    (ha : Approximates aHat a ea) (hb : Approximates bHat b eb) :
    Approximates (aHat - bHat) (a - b) (ea + eb) := by
  rw [Approximates]
  have hid : aHat - bHat - (a - b) = (aHat - a) - (bHat - b) := by ring
  rw [hid]
  exact (abs_sub _ _).trans (add_le_add ha hb)

/-- Affine proposal rounding decomposes into current, scale, and noise errors.
The computed noise and ideal scale appear only through explicit magnitudes. -/
theorem affineProposal_approximates
    {computedCurrent idealCurrent currentError
      computedScale idealScale scaleError
      computedNoise idealNoise noiseError : ℝ}
    (hcurrent : Approximates computedCurrent idealCurrent currentError)
    (hscale : Approximates computedScale idealScale scaleError)
    (hnoise : Approximates computedNoise idealNoise noiseError) :
    Approximates
      (computedCurrent + computedScale * computedNoise)
      (idealCurrent + idealScale * idealNoise)
      (currentError + scaleError * |computedNoise| + |idealScale| * noiseError) := by
  rw [Approximates]
  have hid :
      computedCurrent + computedScale * computedNoise -
          (idealCurrent + idealScale * idealNoise) =
        (computedCurrent - idealCurrent) +
          (computedScale - idealScale) * computedNoise +
          idealScale * (computedNoise - idealNoise) := by ring
  rw [hid]
  calc
    |(computedCurrent - idealCurrent) +
        (computedScale - idealScale) * computedNoise +
        idealScale * (computedNoise - idealNoise)| ≤
        |computedCurrent - idealCurrent| +
          |(computedScale - idealScale) * computedNoise| +
          |idealScale * (computedNoise - idealNoise)| := by
            exact (abs_add_le _ _).trans
              (add_le_add (abs_add_le _ _) le_rfl)
    _ = |computedCurrent - idealCurrent| +
          |computedScale - idealScale| * |computedNoise| +
          |idealScale| * |computedNoise - idealNoise| := by rw [abs_mul, abs_mul]
    _ ≤ currentError + scaleError * |computedNoise| +
          |idealScale| * noiseError := by
      change |computedCurrent - idealCurrent| ≤ currentError at hcurrent
      change |computedScale - idealScale| ≤ scaleError at hscale
      change |computedNoise - idealNoise| ≤ noiseError at hnoise
      gcongr

theorem Approximates.minZero {aHat a error : ℝ}
    (ha : Approximates aHat a error) :
    Approximates (min 0 aHat) (min 0 a) error := by
  rw [Approximates]
  exact (abs_min_sub_min_le_max 0 aHat 0 a).trans <| by
    simpa [Approximates] using ha

/-- A concrete finite-error record for one RWMH execution. Errors may come
from rounding, callback approximation, or bounded transcendental error. -/
structure RwmhErrorCertificate where
  idealCurrent : ℝ
  computedCurrent : ℝ
  idealProposal : ℝ
  computedProposal : ℝ
  idealLogRatio : ℝ
  computedLogRatio : ℝ
  idealThreshold : ℝ
  computedThreshold : ℝ
  idealUniform : ℝ
  computedUniform : ℝ
  currentError : ℝ
  proposalError : ℝ
  logRatioError : ℝ
  thresholdError : ℝ
  uniformError : ℝ
  current_bound : Approximates computedCurrent idealCurrent currentError
  proposal_bound : Approximates computedProposal idealProposal proposalError
  logRatio_bound : Approximates computedLogRatio idealLogRatio logRatioError
  threshold_bound : Approximates computedThreshold idealThreshold thresholdError
  uniform_bound : Approximates computedUniform idealUniform uniformError

/-- The ideal branch is stable when its comparison margin exceeds both input
errors. This condition is necessary in some form for a discontinuous branch. -/
def RwmhErrorCertificate.DecisionStable (certificate : RwmhErrorCertificate) : Prop :=
  certificate.uniformError + certificate.thresholdError <
    |certificate.idealUniform - certificate.idealThreshold|

theorem comparison_eq_of_approximates
    {computedLeft idealLeft leftError computedRight idealRight rightError : ℝ}
    (hleft : Approximates computedLeft idealLeft leftError)
    (hright : Approximates computedRight idealRight rightError)
    (hmargin : leftError + rightError < |idealLeft - idealRight|) :
    (computedLeft < computedRight) = (idealLeft < idealRight) := by
  have hl := abs_le.mp hleft
  have hr := abs_le.mp hright
  by_cases horder : idealLeft < idealRight
  · apply propext
    simp only [horder, iff_true]
    rw [abs_of_neg (sub_neg.mpr horder)] at hmargin
    linarith
  · have hreverse : idealRight ≤ idealLeft := le_of_not_gt horder
    apply propext
    simp only [horder, iff_false]
    intro hcomputed
    rw [abs_of_nonneg (sub_nonneg.mpr hreverse)] at hmargin
    linarith

/-- Conversely, a changed branch can occur only inside the accumulated-error
band around the ideal comparison boundary. -/
theorem margin_le_of_comparison_ne
    {computedLeft idealLeft leftError computedRight idealRight rightError : ℝ}
    (hleft : Approximates computedLeft idealLeft leftError)
    (hright : Approximates computedRight idealRight rightError)
    (hdifferent :
      (computedLeft < computedRight) ≠ (idealLeft < idealRight)) :
    |idealLeft - idealRight| ≤ leftError + rightError := by
  by_contra hle
  exact hdifferent (comparison_eq_of_approximates hleft hright (lt_of_not_ge hle))

theorem RwmhErrorCertificate.comparison_eq
    (certificate : RwmhErrorCertificate) (hstable : certificate.DecisionStable) :
    (certificate.computedUniform < certificate.computedThreshold) =
      (certificate.idealUniform < certificate.idealThreshold) :=
  comparison_eq_of_approximates certificate.uniform_bound
    certificate.threshold_bound hstable

/-- Under a stable decision, the returned backend value approximates the
ideal RWMH result by the error of the selected branch. -/
theorem RwmhErrorCertificate.result_approximates
    (certificate : RwmhErrorCertificate) (hstable : certificate.DecisionStable) :
    Approximates
      (if certificate.computedUniform < certificate.computedThreshold then
        certificate.computedProposal else certificate.computedCurrent)
      (if certificate.idealUniform < certificate.idealThreshold then
        certificate.idealProposal else certificate.idealCurrent)
      (max certificate.proposalError certificate.currentError) := by
  have hcomparison := certificate.comparison_eq hstable
  by_cases hideal : certificate.idealUniform < certificate.idealThreshold
  · have hcomputed : certificate.computedUniform < certificate.computedThreshold := by
      simpa [hideal] using hcomparison
    simp only [hideal, hcomputed, if_true]
    exact certificate.proposal_bound.trans (le_max_left _ _)
  · have hcomputed : ¬certificate.computedUniform < certificate.computedThreshold := by
      simpa [hideal] using hcomparison
    simp only [hideal, hcomputed, if_false]
    exact certificate.current_bound.trans (le_max_right _ _)

/-- Callback errors at current and proposed states add in the log ratio. -/
theorem logRatio_approximates
    {computedProposed idealProposed computedCurrent idealCurrent
      proposedError currentError : ℝ}
    (hproposed : Approximates computedProposed idealProposed proposedError)
    (hcurrent : Approximates computedCurrent idealCurrent currentError) :
    Approximates (computedProposed - computedCurrent)
      (idealProposed - idealCurrent) (proposedError + currentError) :=
  hproposed.sub hcurrent

/-- Clamping a computed log ratio at zero does not amplify its error. -/
theorem clampedLogRatio_approximates
    {computed ideal error : ℝ} (h : Approximates computed ideal error) :
    Approximates (min 0 computed) (min 0 ideal) error :=
  h.minZero

/-- The real exponential is one-Lipschitz on the nonpositive half-line. -/
theorem abs_exp_sub_exp_le_abs {x y : ℝ} (hx : x ≤ 0) (hy : y ≤ 0) :
    |Real.exp x - Real.exp y| ≤ |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (𝕜 := ℝ) (f := Real.exp) (s := Set.Iic (0 : ℝ)) (x := y) (y := x)
    (fun _ _ => Real.differentiableAt_exp)
    (fun z hz => by
      rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos z)]
      simpa only [one_mul, Real.exp_zero] using Real.exp_le_exp.mpr hz)
    (convex_Iic (𝕜 := ℝ) (0 : ℝ)) hy hx
  simpa only [Real.norm_eq_abs, one_mul] using h

/-- Clamping before exponentiation makes threshold transport nonexpansive. -/
theorem expClamped_approximates
    {computed ideal error : ℝ} (h : Approximates computed ideal error) :
    Approximates (Real.exp (min 0 computed)) (Real.exp (min 0 ideal)) error := by
  rw [Approximates]
  exact (abs_exp_sub_exp_le_abs (min_le_left _ _) (min_le_left _ _)).trans
    h.minZero

/-- Error budget used after applying a backend exponential implementation.
The exponential implementation's own bound is kept explicit. -/
theorem threshold_approximates_of_exp_error
    {computedExp computedLogRatio idealLogRatio ratioError expError : ℝ}
    (_hratio : Approximates computedLogRatio idealLogRatio ratioError)
    (hexp : Approximates computedExp (Real.exp (min 0 computedLogRatio)) expError) :
    Approximates computedExp (Real.exp (min 0 idealLogRatio))
      (expError + ratioError) := by
  rw [Approximates] at hexp ⊢
  have hid : computedExp - Real.exp (min 0 idealLogRatio) =
      (computedExp - Real.exp (min 0 computedLogRatio)) +
        (Real.exp (min 0 computedLogRatio) -
          Real.exp (min 0 idealLogRatio)) := by ring
  rw [hid]
  exact (abs_add_le _ _).trans
    (add_le_add hexp (expClamped_approximates _hratio))

/-- End-to-end bounded refinement to the exact command interpreter for one
valid ideal trace. It guarantees the identical accept/reject branch away from
the comparison boundary and a quantitative returned-value error. -/
theorem boundedRwmh_refines_runGaussianRwmh
    (certificate : RwmhErrorCertificate)
    (logDensity : ℝ → ℝ) (scale noise : ℝ) (rest : List IR.Event)
    (hproposal : certificate.idealProposal =
      certificate.idealCurrent + scale * noise)
    (hratio : certificate.idealLogRatio =
      logDensity certificate.idealProposal - logDensity certificate.idealCurrent)
    (hthreshold : certificate.idealThreshold =
      Real.exp (min 0 certificate.idealLogRatio))
    (hunit : 0 ≤ certificate.idealUniform ∧ certificate.idealUniform < 1)
    (hstable : certificate.DecisionStable) :
    CompilerIR.runGaussianRwmh logDensity scale certificate.idealCurrent
        (.standardNormal noise :: .uniformUnit certificate.idealUniform :: rest) =
      .ok ⟨if certificate.idealUniform < certificate.idealThreshold then
          certificate.idealProposal else certificate.idealCurrent, rest⟩ ∧
    Approximates
      (if certificate.computedUniform < certificate.computedThreshold then
        certificate.computedProposal else certificate.computedCurrent)
      (if certificate.idealUniform < certificate.idealThreshold then
        certificate.idealProposal else certificate.idealCurrent)
      (max certificate.proposalError certificate.currentError) := by
  constructor
  · rw [CompilerIR.runGaussianRwmh_refines logDensity scale
      certificate.idealCurrent noise certificate.idealUniform hunit rest]
    rw [← hproposal, ← hratio, ← hthreshold]
  · exact certificate.result_approximates hstable

end Mcmc.Executable.Continuous
