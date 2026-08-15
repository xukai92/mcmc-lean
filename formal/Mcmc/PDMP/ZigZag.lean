import Mcmc.PDMP.Flow
import Mathlib.MeasureTheory.Integral.Bochner.Basic
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

end Mcmc.PDMP
