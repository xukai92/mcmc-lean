import Mcmc.PDMP.Flow
import Mathlib.MeasureTheory.Integral.Bochner.Basic
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

end Mcmc.PDMP
