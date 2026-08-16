import Mcmc.PDMP.Flow
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

/-!
# One-dimensional Zig-Zag generator balance

This module formalizes the algebraic cancellation at the heart of the
one-dimensional Zig-Zag process. Velocity is `Bool`, interpreted as `-1` and
`+1`, and the canonical switching rate is `max 0 (v * U'(q))`.

The final mean-zero theorem takes the required integration-by-parts identity
and integrability as explicit premises. It is a generator-invariance result,
not yet a process-existence or convergence theorem.
-/

open MeasureTheory
open scoped BigOperators

namespace Mcmc.PDMP

/-- Numeric velocity represented by a Boolean sign. -/
def zigZagVelocity : Bool → ℝ
  | false => -1
  | true => 1

/-- Canonical one-dimensional Zig-Zag switching rate. -/
def zigZagRate (potentialGradient : ℝ → ℝ) (q : ℝ) (v : Bool) : ℝ :=
  max 0 (zigZagVelocity v * potentialGradient q)

theorem zigZagRate_nonneg (potentialGradient : ℝ → ℝ) (q : ℝ) (v : Bool) :
    0 ≤ zigZagRate potentialGradient q v :=
  le_max_left _ _

/-- Zig-Zag generator for a supplied position derivative of the observable. -/
def zigZagGenerator (potentialGradient : ℝ → ℝ)
    (derivative observable : ℝ → Bool → ℝ) (q : ℝ) (v : Bool) : ℝ :=
  zigZagVelocity v * derivative q v +
    zigZagRate potentialGradient q v *
      (observable q (!v) - observable q v)

private theorem max_zero_sub_max_zero_neg (a : ℝ) :
    max 0 a - max 0 (-a) = a := by
  by_cases ha : 0 ≤ a
  · rw [max_eq_right ha, max_eq_left (neg_nonpos.mpr ha)]
    ring
  · have hneg : a ≤ 0 := le_of_not_ge ha
    rw [max_eq_left hneg, max_eq_right (neg_nonneg.mpr hneg)]
    ring

/-- Summing over both velocities turns the switching term into exactly the
negative potential-gradient term needed for integration by parts. -/
theorem sum_bool_zigZagGenerator (potentialGradient : ℝ → ℝ)
    (derivative observable : ℝ → Bool → ℝ) (q : ℝ) :
    ∑ v : Bool, zigZagGenerator potentialGradient derivative observable q v =
      (derivative q true - derivative q false) -
        potentialGradient q * (observable q true - observable q false) := by
  rw [Fintype.sum_bool]
  simp only [zigZagGenerator, zigZagVelocity, zigZagRate, Bool.not_false,
    Bool.not_true, one_mul, neg_one_mul]
  have hmax := max_zero_sub_max_zero_neg (potentialGradient q)
  have hrewrite : max 0 (-potentialGradient q) =
      max 0 (potentialGradient q) - potentialGradient q := by
    linarith
  rw [hrewrite]
  ring

/-- The one-dimensional Zig-Zag generator has target mean zero whenever the
corresponding weighted integration-by-parts identity holds. -/
theorem zigZagGenerator_mean_zero
    (positionMeasure : Measure ℝ) (density potentialGradient : ℝ → ℝ)
    (derivative observable : ℝ → Bool → ℝ)
    (hdrift : Integrable (fun q => density q *
      (derivative q true - derivative q false)) positionMeasure)
    (hpotential : Integrable (fun q => density q * potentialGradient q *
      (observable q true - observable q false)) positionMeasure)
    (hibp : (∫ q, density q *
        (derivative q true - derivative q false) ∂positionMeasure) =
      ∫ q, density q * potentialGradient q *
        (observable q true - observable q false) ∂positionMeasure) :
    (∫ q, density q *
      (∑ v : Bool, zigZagGenerator potentialGradient derivative observable q v)
      ∂positionMeasure) = 0 := by
  simp_rw [sum_bool_zigZagGenerator]
  have heq : (fun q => density q *
      ((derivative q true - derivative q false) - potentialGradient q *
        (observable q true - observable q false))) =
      (fun q => density q * (derivative q true - derivative q false) -
        density q * potentialGradient q *
          (observable q true - observable q false)) := by
    funext q
    ring
  rw [heq, integral_sub hdrift hpotential, hibp, sub_self]

/-! ### Gaussian Stein test class -/

/-- A velocity-dependent observable and its supplied position derivative form
a Gaussian Stein test when their velocity differences obey the standard
Gaussian integration-by-parts identity.  The two integrability fields make
the cancellation theorem valid for the Bochner integral; `stein` is the
remaining analytic obligation that clients may discharge from smoothness and
decay assumptions.

This certificate is deliberately about a test function, not about invariance
of the Zig-Zag process. -/
structure GaussianSteinTest
    (derivative observable : ℝ → Bool → ℝ) : Prop where
  derivative_integrable : Integrable
    (fun q => derivative q true - derivative q false)
    (ProbabilityTheory.gaussianReal 0 1)
  position_integrable : Integrable
    (fun q => q * (observable q true - observable q false))
    (ProbabilityTheory.gaussianReal 0 1)
  stein :
    (∫ q, derivative q true - derivative q false
      ∂ProbabilityTheory.gaussianReal 0 1) =
    ∫ q, q * (observable q true - observable q false)
      ∂ProbabilityTheory.gaussianReal 0 1

/-- Derivative of the standard-Gaussian Lebesgue density. -/
theorem hasDerivAt_standardGaussianPDF (q : ℝ) :
    HasDerivAt (ProbabilityTheory.gaussianPDFReal 0 1)
      (-q * ProbabilityTheory.gaussianPDFReal 0 1 q) q := by
  rw [ProbabilityTheory.gaussianPDFReal_def]
  simp only [NNReal.coe_one, sub_zero,
    mul_one]
  convert (hasDerivAt_const q (Real.sqrt (2 * Real.pi))⁻¹).mul
    ((((hasDerivAt_id q).pow 2).neg.div_const 2).exp) using 1
  · rfl
  · rfl
  · funext x
    simp [Pi.pow_apply]
  · simp [Pi.pow_apply]
    ring

/-- Standard-Gaussian integration by parts, stated with the exact analytic
hypotheses used by mathlib's improper-integral theorem. -/
theorem standardGaussian_integral_deriv_eq_integral_mul
    (g g' : ℝ → ℝ)
    (hg : ∀ q, HasDerivAt g (g' q) q)
    (hderiv : Integrable (fun q => g' q *
      ProbabilityTheory.gaussianPDFReal 0 1 q))
    (hposition : Integrable (fun q => g q *
      (-q * ProbabilityTheory.gaussianPDFReal 0 1 q)))
    (hbot : Filter.Tendsto (fun q => g q *
      ProbabilityTheory.gaussianPDFReal 0 1 q)
      Filter.atBot (nhds 0))
    (htop : Filter.Tendsto (fun q => g q *
      ProbabilityTheory.gaussianPDFReal 0 1 q)
      Filter.atTop (nhds 0)) :
    (∫ q, g' q ∂ProbabilityTheory.gaussianReal 0 1) =
      ∫ q, q * g q ∂ProbabilityTheory.gaussianReal 0 1 := by
  have hibp := integral_mul_deriv_eq_deriv_mul
    (u := g) (v := ProbabilityTheory.gaussianPDFReal 0 1)
    (u' := g')
    (v' := fun q => -q * ProbabilityTheory.gaussianPDFReal 0 1 q)
    (a' := 0) (b' := 0)
    (fun q _ => hg q) (fun q _ => hasDerivAt_standardGaussianPDF q)
    hposition hderiv hbot htop
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul
      (show (1 : NNReal) ≠ 0 by norm_num),
    ProbabilityTheory.integral_gaussianReal_eq_integral_smul
      (show (1 : NNReal) ≠ 0 by norm_num)]
  simp only [smul_eq_mul]
  have hleft :
      (∫ q, ProbabilityTheory.gaussianPDFReal 0 1 q * g' q) =
        ∫ q, g' q * ProbabilityTheory.gaussianPDFReal 0 1 q := by
    apply integral_congr_ae
    filter_upwards [] with q
    ring
  have hright :
      (∫ q, ProbabilityTheory.gaussianPDFReal 0 1 q * (q * g q)) =
        -(∫ q, g q *
          (-q * ProbabilityTheory.gaussianPDFReal 0 1 q)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with q
    ring
  rw [hleft, hright]
  linarith

/-- Construct a Gaussian Stein test from ordinary differentiability, weighted
Lebesgue integrability, and decay against the Gaussian density. This discharges
the `stein` field rather than asking a client to postulate integration by
parts. -/
theorem gaussianSteinTest_of_hasDerivAt
    (derivative observable : ℝ → Bool → ℝ)
    (hderivativeIntegrable : Integrable
      (fun q => derivative q true - derivative q false)
      (ProbabilityTheory.gaussianReal 0 1))
    (hpositionIntegrable : Integrable
      (fun q => q * (observable q true - observable q false))
      (ProbabilityTheory.gaussianReal 0 1))
    (hhasDeriv : ∀ q, HasDerivAt
      (fun x => observable x true - observable x false)
      (derivative q true - derivative q false) q)
    (hweightedDerivative : Integrable (fun q =>
      (derivative q true - derivative q false) *
        ProbabilityTheory.gaussianPDFReal 0 1 q))
    (hweightedPosition : Integrable (fun q =>
      (observable q true - observable q false) *
        (-q * ProbabilityTheory.gaussianPDFReal 0 1 q)))
    (hbot : Filter.Tendsto (fun q =>
      (observable q true - observable q false) *
        ProbabilityTheory.gaussianPDFReal 0 1 q)
      Filter.atBot (nhds 0))
    (htop : Filter.Tendsto (fun q =>
      (observable q true - observable q false) *
        ProbabilityTheory.gaussianPDFReal 0 1 q)
      Filter.atTop (nhds 0)) :
    GaussianSteinTest derivative observable where
  derivative_integrable := hderivativeIntegrable
  position_integrable := hpositionIntegrable
  stein := standardGaussian_integral_deriv_eq_integral_mul
    (fun q => observable q true - observable q false)
    (fun q => derivative q true - derivative q false)
    hhasDeriv hweightedDerivative hweightedPosition hbot htop

/-- Every Gaussian Stein test has mean-zero standard-Gaussian Zig-Zag
generator.  Unlike the earlier generic weighted theorem, this statement is
directly phrased over the actual Gaussian target and an arbitrary observable
class. -/
theorem gaussian_zigZagGenerator_mean_zero_of_stein
    (derivative observable : ℝ → Bool → ℝ)
    (h : GaussianSteinTest derivative observable) :
    (∫ q, (∑ v : Bool, zigZagGenerator id derivative observable q v)
      ∂ProbabilityTheory.gaussianReal 0 1) = 0 := by
  have hdrift : Integrable
      (fun q => (1 : ℝ) * (derivative q true - derivative q false))
      (ProbabilityTheory.gaussianReal 0 1) := by
    simpa using h.derivative_integrable
  have hposition : Integrable
      (fun q => (1 : ℝ) * id q *
        (observable q true - observable q false))
      (ProbabilityTheory.gaussianReal 0 1) := by
    simpa using h.position_integrable
  have hstein :
      (∫ q, (1 : ℝ) * (derivative q true - derivative q false)
        ∂ProbabilityTheory.gaussianReal 0 1) =
      ∫ q, (1 : ℝ) * id q *
        (observable q true - observable q false)
        ∂ProbabilityTheory.gaussianReal 0 1 := by
    simpa using h.stein
  simpa only [one_mul, id_eq] using
    zigZagGenerator_mean_zero
      (ProbabilityTheory.gaussianReal 0 1) (fun _ => 1) id
      derivative observable hdrift hposition hstein

/-- Velocity itself as a concrete Zig-Zag test observable. -/
def zigZagVelocityObservable (_q : ℝ) (v : Bool) : ℝ := zigZagVelocity v

/-- Its position derivative is identically zero. -/
def zigZagVelocityDerivative (_q : ℝ) (_v : Bool) : ℝ := 0

/-- For the standard Gaussian potential `U(q)=q²/2`, the two-velocity
generator applied to velocity is the odd function `-2q`. -/
theorem sum_bool_gaussian_zigZagGenerator_velocity (q : ℝ) :
    ∑ v : Bool, zigZagGenerator id zigZagVelocityDerivative
      zigZagVelocityObservable q v = -2 * q := by
  rw [sum_bool_zigZagGenerator]
  simp [zigZagVelocityDerivative, zigZagVelocityObservable,
    zigZagVelocity]
  ring

/-- The concrete standard-Gaussian Zig-Zag generator balances the velocity
observable exactly. This is a genuine target/test-function instance of the
generator identity, not yet a full process-invariance theorem. -/
theorem gaussian_zigZagGenerator_velocity_mean_zero :
    (∫ q, (∑ v : Bool, zigZagGenerator id zigZagVelocityDerivative
      zigZagVelocityObservable q v) ∂ProbabilityTheory.gaussianReal 0 1) = 0 := by
  simp_rw [sum_bool_gaussian_zigZagGenerator_velocity]
  rw [integral_const_mul, ProbabilityTheory.integral_id_gaussianReal]
  norm_num

/-- Position times velocity is a second concrete test observable. -/
def zigZagPositionVelocityObservable (q : ℝ) (v : Bool) : ℝ :=
  q * zigZagVelocity v

/-- Exact position derivative of `zigZagPositionVelocityObservable`. -/
def zigZagPositionVelocityDerivative (_q : ℝ) (v : Bool) : ℝ :=
  zigZagVelocity v

theorem sum_bool_gaussian_zigZagGenerator_positionVelocity (q : ℝ) :
    ∑ v : Bool, zigZagGenerator id zigZagPositionVelocityDerivative
      zigZagPositionVelocityObservable q v = 2 - 2 * q ^ 2 := by
  rw [sum_bool_zigZagGenerator]
  simp [zigZagPositionVelocityDerivative,
    zigZagPositionVelocityObservable, zigZagVelocity]
  ring

/-- Gaussian unit variance supplies the nontrivial second-moment cancellation
for the position-times-velocity observable. -/
theorem gaussian_zigZagGenerator_positionVelocity_mean_zero :
    (∫ q, (∑ v : Bool, zigZagGenerator id
      zigZagPositionVelocityDerivative zigZagPositionVelocityObservable q v)
      ∂ProbabilityTheory.gaussianReal 0 1) = 0 := by
  let gaussian := ProbabilityTheory.gaussianReal 0 1
  have hid : MemLp id 2 gaussian :=
    ProbabilityTheory.memLp_id_gaussianReal 2
  have hsquare : (∫ q, q ^ 2 ∂gaussian) = 1 := by
    have hvariance := ProbabilityTheory.variance_eq_sub hid
    dsimp [gaussian] at hvariance
    rw [ProbabilityTheory.variance_id_gaussianReal,
      ProbabilityTheory.integral_id_gaussianReal] at hvariance
    simpa [Pi.pow_apply] using hvariance.symm
  simp_rw [sum_bool_gaussian_zigZagGenerator_positionVelocity]
  change (∫ q, 2 - 2 * q ^ 2 ∂gaussian) = 0
  have hsqint : Integrable (fun q : ℝ => 2 * q ^ 2) gaussian := by
    simpa [Pi.pow_apply] using hid.integrable_sq.const_mul 2
  calc
    _ = (∫ _q : ℝ, 2 ∂gaussian) -
        ∫ q : ℝ, 2 * q ^ 2 ∂gaussian := by
      simpa only [Pi.sub_apply] using
        integral_sub (integrable_const 2) hsqint
    _ = 0 := by
      rw [integral_const_mul, hsquare]
      simp

/-- The two-dimensional affine velocity-odd test class contains both concrete
Gaussian clients above. -/
def zigZagAffineVelocityObservable (a b q : ℝ) (v : Bool) : ℝ :=
  (a + b * q) * zigZagVelocity v

/-- Exact position derivative for the affine velocity-odd test class. -/
def zigZagAffineVelocityDerivative (_a b _q : ℝ) (v : Bool) : ℝ :=
  b * zigZagVelocity v

theorem sum_bool_gaussian_zigZagGenerator_affineVelocity
    (a b q : ℝ) :
    ∑ v : Bool, zigZagGenerator id (zigZagAffineVelocityDerivative a b)
      (zigZagAffineVelocityObservable a b) q v =
        2 * b - 2 * a * q - 2 * b * q ^ 2 := by
  rw [sum_bool_zigZagGenerator]
  simp [zigZagAffineVelocityDerivative, zigZagAffineVelocityObservable,
    zigZagVelocity]
  ring

/-- Generator balance holds simultaneously for every affine velocity-odd
observable, rather than only for two isolated test functions. -/
theorem gaussian_zigZagGenerator_affineVelocity_mean_zero (a b : ℝ) :
    (∫ q, (∑ v : Bool, zigZagGenerator id
      (zigZagAffineVelocityDerivative a b)
      (zigZagAffineVelocityObservable a b) q v)
      ∂ProbabilityTheory.gaussianReal 0 1) = 0 := by
  let gaussian := ProbabilityTheory.gaussianReal 0 1
  have hid : MemLp id 2 gaussian :=
    ProbabilityTheory.memLp_id_gaussianReal 2
  have hsquare : (∫ q, q ^ 2 ∂gaussian) = 1 := by
    have hvariance := ProbabilityTheory.variance_eq_sub hid
    dsimp [gaussian] at hvariance
    rw [ProbabilityTheory.variance_id_gaussianReal,
      ProbabilityTheory.integral_id_gaussianReal] at hvariance
    simpa [Pi.pow_apply] using hvariance.symm
  simp_rw [sum_bool_gaussian_zigZagGenerator_affineVelocity]
  change (∫ q, 2 * b - 2 * a * q - 2 * b * q ^ 2 ∂gaussian) = 0
  have hlinear : Integrable (fun q : ℝ => 2 * a * q) gaussian := by
    have hidIntegrable : Integrable (fun q : ℝ => q) gaussian :=
      hid.integrable (by norm_num)
    exact hidIntegrable.const_mul (2 * a)
  have hsquareInt : Integrable (fun q : ℝ => 2 * b * q ^ 2) gaussian := by
    simpa [Pi.pow_apply] using hid.integrable_sq.const_mul (2 * b)
  have hinner : (∫ q : ℝ, 2 * b - 2 * a * q ∂gaussian) =
      (∫ _q : ℝ, 2 * b ∂gaussian) -
        ∫ q : ℝ, 2 * a * q ∂gaussian := by
    simpa only [Pi.sub_apply] using
      integral_sub (integrable_const (2 * b)) hlinear
  have houter : (∫ q : ℝ, (2 * b - 2 * a * q) - 2 * b * q ^ 2
      ∂gaussian) =
      (∫ q : ℝ, 2 * b - 2 * a * q ∂gaussian) -
        ∫ q : ℝ, 2 * b * q ^ 2 ∂gaussian := by
    simpa only [Pi.sub_apply] using
      integral_sub ((integrable_const (2 * b)).sub hlinear) hsquareInt
  calc
    _ = ((∫ _q : ℝ, 2 * b ∂gaussian) -
          ∫ q : ℝ, 2 * a * q ∂gaussian) -
          ∫ q : ℝ, 2 * b * q ^ 2 ∂gaussian := by
      rw [houter, hinner]
    _ = 0 := by
      have hconst : (∫ _q : ℝ, 2 * b ∂gaussian) = 2 * b := by simp
      have hlinearIntegral : (∫ q : ℝ, 2 * a * q ∂gaussian) = 0 := by
        rw [integral_const_mul,
          ProbabilityTheory.integral_id_gaussianReal]
        ring
      have hsquareIntegral : (∫ q : ℝ, 2 * b * q ^ 2 ∂gaussian) =
          2 * b := by
        rw [integral_const_mul, hsquare]
        ring
      rw [hconst, hlinearIntegral, hsquareIntegral]
      ring

/-- Every affine velocity-odd observable satisfies the reusable Gaussian Stein
test interface.  This is the first nontrivial family-level client of
`GaussianSteinTest`; in particular, the certificate is available to later
analytic arguments without unfolding the Zig-Zag generator. -/
theorem gaussianSteinTest_affineVelocity (a b : ℝ) :
    GaussianSteinTest (zigZagAffineVelocityDerivative a b)
      (zigZagAffineVelocityObservable a b) := by
  let gaussian := ProbabilityTheory.gaussianReal 0 1
  have hid : MemLp id 2 gaussian :=
    ProbabilityTheory.memLp_id_gaussianReal 2
  have hidIntegrable : Integrable (fun q : ℝ => q) gaussian :=
    hid.integrable (by norm_num)
  have hsquareIntegrable : Integrable (fun q : ℝ => q ^ 2) gaussian := by
    simpa [Pi.pow_apply] using hid.integrable_sq
  have hsquare : (∫ q, q ^ 2 ∂gaussian) = 1 := by
    have hvariance := ProbabilityTheory.variance_eq_sub hid
    dsimp [gaussian] at hvariance
    rw [ProbabilityTheory.variance_id_gaussianReal,
      ProbabilityTheory.integral_id_gaussianReal] at hvariance
    simpa [Pi.pow_apply] using hvariance.symm
  refine ⟨?_, ?_, ?_⟩
  · convert (integrable_const (2 * b) :
        Integrable (fun _q : ℝ => 2 * b) gaussian) using 1
    funext q
    simp [zigZagAffineVelocityDerivative, zigZagVelocity, two_mul]
  · have hlinear := hidIntegrable.const_mul (2 * a)
    have hquadratic := hsquareIntegrable.const_mul (2 * b)
    have hsum := hlinear.add hquadratic
    apply hsum.congr
    filter_upwards [] with q
    simp [zigZagAffineVelocityObservable, zigZagVelocity]
    ring
  · simp only [zigZagAffineVelocityDerivative,
      zigZagAffineVelocityObservable, zigZagVelocity, mul_one, mul_neg,
      mul_one, sub_neg_eq_add]
    simp_rw [← two_mul]
    change (∫ _q : ℝ, 2 * b ∂gaussian) =
      ∫ q : ℝ, q * (2 * (a + b * q)) ∂gaussian
    have hright : (∫ q : ℝ, q * (2 * (a + b * q)) ∂gaussian) =
        (∫ q : ℝ, 2 * a * q ∂gaussian) +
          ∫ q : ℝ, 2 * b * q ^ 2 ∂gaussian := by
      rw [← integral_add (hidIntegrable.const_mul (2 * a))
        (hsquareIntegrable.const_mul (2 * b))]
      apply integral_congr_ae
      filter_upwards [] with q
      ring
    rw [hright]
    have hlinearIntegral :
        (∫ q : ℝ, 2 * a * q ∂gaussian) = 0 := by
      rw [integral_const_mul,
        ProbabilityTheory.integral_id_gaussianReal]
      ring
    have hquadraticIntegral :
        (∫ q : ℝ, 2 * b * q ^ 2 ∂gaussian) = 2 * b := by
      rw [integral_const_mul, hsquare]
      ring
    rw [hlinearIntegral, hquadraticIntegral]
    simp

/-! ### Exact Gaussian event clock -/

/-- Integrated switching rate along the linear Gaussian Zig-Zag flow.  With
`a = vq`, the rate is `max 0 (a+t)`. -/
noncomputable def gaussianZigZagIntegratedRate
    (q : ℝ) (v : Bool) (t : ℝ) : ℝ :=
  let a := zigZagVelocity v * q
  if 0 ≤ a then a * t + t ^ 2 / 2
  else if t ≤ -a then 0 else (a + t) ^ 2 / 2

/-- Closed-form inverse clock for a positive exponential hazard draw. -/
noncomputable def gaussianZigZagWaitingTime
    (q : ℝ) (v : Bool) (exponentialDraw : ℝ) : ℝ :=
  let a := zigZagVelocity v * q
  if 0 ≤ a then Real.sqrt (a ^ 2 + 2 * exponentialDraw) - a
  else -a + Real.sqrt (2 * exponentialDraw)

theorem gaussianZigZagWaitingTime_nonneg
    (q : ℝ) (v : Bool) {exponentialDraw : ℝ}
    (hdraw : 0 ≤ exponentialDraw) :
    0 ≤ gaussianZigZagWaitingTime q v exponentialDraw := by
  let a := zigZagVelocity v * q
  change 0 ≤ if 0 ≤ a then Real.sqrt (a ^ 2 + 2 * exponentialDraw) - a
    else -a + Real.sqrt (2 * exponentialDraw)
  split_ifs with ha
  · have hsquare : a ^ 2 ≤ a ^ 2 + 2 * exponentialDraw := by linarith
    have ha' : 0 ≤ a := ha
    have hsqrtA : Real.sqrt (a ^ 2) = a := Real.sqrt_sq ha'
    linarith [Real.sqrt_le_sqrt hsquare]
  · exact add_nonneg (neg_nonneg.mpr (le_of_not_ge ha)) (Real.sqrt_nonneg _)

/-- Cancellation-free form of the inverse clock when the signed position is
nonnegative. This is the algebraic identity used by the Float64 runtime for
large positive signed positions. -/
theorem gaussianZigZagWaitingTime_eq_stable_of_nonneg
    (q : ℝ) (v : Bool) {exponentialDraw : ℝ}
    (hdraw : 0 < exponentialDraw)
    (ha : 0 ≤ zigZagVelocity v * q) :
    gaussianZigZagWaitingTime q v exponentialDraw =
      (2 * exponentialDraw) /
        (Real.sqrt ((zigZagVelocity v * q) ^ 2 + 2 * exponentialDraw) +
          zigZagVelocity v * q) := by
  let a := zigZagVelocity v * q
  change (if 0 ≤ a then Real.sqrt (a ^ 2 + 2 * exponentialDraw) - a
    else -a + Real.sqrt (2 * exponentialDraw)) =
      (2 * exponentialDraw) /
        (Real.sqrt (a ^ 2 + 2 * exponentialDraw) + a)
  rw [if_pos ha]
  have hrad : 0 ≤ a ^ 2 + 2 * exponentialDraw := by positivity
  have hsqrtPos : 0 < Real.sqrt (a ^ 2 + 2 * exponentialDraw) :=
    Real.sqrt_pos.2 (by nlinarith [sq_nonneg a])
  have hdenom : Real.sqrt (a ^ 2 + 2 * exponentialDraw) + a ≠ 0 := by
    positivity
  field_simp
  nlinarith [Real.sq_sqrt hrad]

/-- The closed-form waiting time inverts the integrated Gaussian Zig-Zag
hazard exactly. -/
theorem gaussianZigZagIntegratedRate_waitingTime
    (q : ℝ) (v : Bool) {exponentialDraw : ℝ}
    (hdraw : 0 < exponentialDraw) :
    gaussianZigZagIntegratedRate q v
      (gaussianZigZagWaitingTime q v exponentialDraw) = exponentialDraw := by
  let a := zigZagVelocity v * q
  by_cases ha : 0 ≤ a
  · change (if 0 ≤ a then
        a * (if 0 ≤ a then Real.sqrt (a ^ 2 + 2 * exponentialDraw) - a
          else -a + Real.sqrt (2 * exponentialDraw)) +
          (if 0 ≤ a then Real.sqrt (a ^ 2 + 2 * exponentialDraw) - a
            else -a + Real.sqrt (2 * exponentialDraw)) ^ 2 / 2
      else if (if 0 ≤ a then Real.sqrt (a ^ 2 + 2 * exponentialDraw) - a
          else -a + Real.sqrt (2 * exponentialDraw)) ≤ -a then 0
      else (a + (if 0 ≤ a then Real.sqrt (a ^ 2 + 2 * exponentialDraw) - a
        else -a + Real.sqrt (2 * exponentialDraw))) ^ 2 / 2) = exponentialDraw
    simp only [ha, if_true]
    have hrad : 0 ≤ a ^ 2 + 2 * exponentialDraw := by positivity
    have hsqrt := Real.sq_sqrt hrad
    nlinarith
  · have hsqrtPos : 0 < Real.sqrt (2 * exponentialDraw) :=
      Real.sqrt_pos.2 (by positivity)
    have hwait : ¬(-a + Real.sqrt (2 * exponentialDraw) ≤ -a) := by linarith
    change (if 0 ≤ a then
        a * (if 0 ≤ a then Real.sqrt (a ^ 2 + 2 * exponentialDraw) - a
          else -a + Real.sqrt (2 * exponentialDraw)) +
          (if 0 ≤ a then Real.sqrt (a ^ 2 + 2 * exponentialDraw) - a
            else -a + Real.sqrt (2 * exponentialDraw)) ^ 2 / 2
      else if (if 0 ≤ a then Real.sqrt (a ^ 2 + 2 * exponentialDraw) - a
          else -a + Real.sqrt (2 * exponentialDraw)) ≤ -a then 0
      else (a + (if 0 ≤ a then Real.sqrt (a ^ 2 + 2 * exponentialDraw) - a
        else -a + Real.sqrt (2 * exponentialDraw))) ^ 2 / 2) = exponentialDraw
    simp only [ha, if_false, hwait]
    have hrad : 0 ≤ 2 * exponentialDraw := by positivity
    have hsqrt := Real.sq_sqrt hrad
    nlinarith

end Mcmc.PDMP
