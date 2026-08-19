import Mcmc.Executable.Continuous.RestrictedCertificate
import Mcmc.Executable.Continuous.BoundedMultinomial
import Mcmc.Relativistic.SoftAbs
import Mcmc.Relativistic.FixedPointIteration
import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
# Guarded numerical refinement for diagonal SoftAbs metrics

The target expression language stays total. SoftAbs metric evaluation uses
positive-domain operations (`sqrt`, reciprocal, and `log`), so this module
keeps their local backend guarantees and positivity guards explicit and
composes them into the three quantities consumed by GR-HMC.
-/

namespace Mcmc.Executable.Continuous

open Mcmc.Relativistic

/-- Exact-rational platform record for the algebraically special SoftAbs entry
`α = 1`, Hessian zero. The ideal eigenvalue, square root, reciprocal factor,
and logarithm are respectively `1`, `1`, `1`, and `0`; consequently this point
can be checked without any libm approximation premise. -/
structure UnitZeroSoftAbsRationalCertificate where
  computedHessian : ℚ
  computedEigenvalue : ℚ
  computedSqrt : ℚ
  computedFactor : ℚ
  computedLogDet : ℚ
deriving DecidableEq, Repr

def UnitZeroSoftAbsRationalCertificate.Valid
    (certificate : UnitZeroSoftAbsRationalCertificate) : Prop :=
  certificate.computedHessian = 0 ∧
    certificate.computedEigenvalue = 1 ∧
    certificate.computedSqrt = 1 ∧
    certificate.computedFactor = 1 ∧
    certificate.computedLogDet = 0

def UnitZeroSoftAbsRationalCertificate.check
    (certificate : UnitZeroSoftAbsRationalCertificate) : Bool :=
  certificate.computedHessian == 0 &&
    (certificate.computedEigenvalue == 1 &&
      (certificate.computedSqrt == 1 &&
        (certificate.computedFactor == 1 && certificate.computedLogDet == 0)))

@[simp] theorem UnitZeroSoftAbsRationalCertificate.check_eq_true_iff
    (certificate : UnitZeroSoftAbsRationalCertificate) :
    certificate.check = true ↔ certificate.Valid := by
  simp [UnitZeroSoftAbsRationalCertificate.check,
    UnitZeroSoftAbsRationalCertificate.Valid]

/-- Exact rational enclosure for a possibly irrational square root. The
foreign runtime supplies a rational center and radius; Lean checks the two
squared endpoint inequalities. -/
structure SqrtRationalIntervalCertificate where
  input : ℚ
  computed : ℚ
  error : ℚ
deriving DecidableEq, Repr

def SqrtRationalIntervalCertificate.Valid
    (certificate : SqrtRationalIntervalCertificate) : Prop :=
  0 ≤ certificate.input ∧ 0 ≤ certificate.error ∧
    0 ≤ certificate.computed - certificate.error ∧
    (certificate.computed - certificate.error) ^ 2 ≤ certificate.input ∧
    certificate.input ≤ (certificate.computed + certificate.error) ^ 2

instance (certificate : SqrtRationalIntervalCertificate) :
    Decidable certificate.Valid := by
  unfold SqrtRationalIntervalCertificate.Valid
  infer_instance

def SqrtRationalIntervalCertificate.check
    (certificate : SqrtRationalIntervalCertificate) : Bool :=
  decide certificate.Valid

theorem SqrtRationalIntervalCertificate.approximates
    (certificate : SqrtRationalIntervalCertificate)
    (hvalid : certificate.Valid) :
    Approximates (certificate.computed : ℝ)
      (Real.sqrt (certificate.input : ℝ)) (certificate.error : ℝ) := by
  have hinput : (0 : ℝ) ≤ certificate.input := by exact_mod_cast hvalid.1
  have herror : (0 : ℝ) ≤ certificate.error := by exact_mod_cast hvalid.2.1
  have hlower0 : (0 : ℝ) ≤ certificate.computed - certificate.error := by
    exact_mod_cast hvalid.2.2.1
  have hlowerSq :
      ((certificate.computed : ℝ) - certificate.error) ^ 2 ≤ certificate.input := by
    exact_mod_cast hvalid.2.2.2.1
  have hupperSq : (certificate.input : ℝ) ≤
      ((certificate.computed : ℝ) + certificate.error) ^ 2 := by
    exact_mod_cast hvalid.2.2.2.2
  have hlower : (certificate.computed : ℝ) - certificate.error ≤
      Real.sqrt certificate.input :=
    (Real.le_sqrt hlower0 hinput).2 hlowerSq
  have hupper0 : (0 : ℝ) ≤ certificate.computed + certificate.error := by
    linarith
  have hupper : Real.sqrt (certificate.input : ℝ) ≤
      certificate.computed + certificate.error :=
    (Real.sqrt_le_iff).2 ⟨hupper0, hupperSq⟩
  rw [Approximates, abs_le]
  constructor <;> linarith

/-- Exact-rational residual certificate for one reciprocal execution. Unlike a
uniform floating-point model, this record proves only the observed call. -/
structure ReciprocalRationalResidualCertificate where
  input : ℚ
  computed : ℚ
  error : ℚ
deriving DecidableEq, Repr

def ReciprocalRationalResidualCertificate.Valid
    (certificate : ReciprocalRationalResidualCertificate) : Prop :=
  certificate.input ≠ 0 ∧ 0 ≤ certificate.error ∧
    |certificate.computed - certificate.input⁻¹| ≤ certificate.error

instance (certificate : ReciprocalRationalResidualCertificate) :
    Decidable certificate.Valid := by
  unfold ReciprocalRationalResidualCertificate.Valid
  infer_instance

def ReciprocalRationalResidualCertificate.check
    (certificate : ReciprocalRationalResidualCertificate) : Bool :=
  decide certificate.Valid

theorem ReciprocalRationalResidualCertificate.approximates
    (certificate : ReciprocalRationalResidualCertificate)
    (hvalid : certificate.Valid) :
    Approximates (certificate.computed : ℝ)
      (certificate.input : ℝ)⁻¹ (certificate.error : ℝ) := by
  rw [Approximates]
  exact_mod_cast hvalid.2.2

/-- Rational enclosure of one logarithm execution. -/
structure LogRationalIntervalCertificate where
  input : ℚ
  computed : ℚ
  error : ℚ
deriving DecidableEq, Repr

/-- Fixed depth of the rational `artanh` expansion used to enclose `log`. -/
def logRationalSeriesTerms : ℕ := 32

def LogRationalIntervalCertificate.seriesArgument
    (certificate : LogRationalIntervalCertificate) : ℚ :=
  (certificate.input - 1) / (certificate.input + 1)

def LogRationalIntervalCertificate.seriesCenter
    (certificate : LogRationalIntervalCertificate) : ℚ :=
  2 * ∑ i ∈ Finset.range logRationalSeriesTerms,
    certificate.seriesArgument ^ (2 * i + 1) / (2 * i + 1)

def LogRationalIntervalCertificate.seriesRemainder
    (certificate : LogRationalIntervalCertificate) : ℚ :=
  2 * |certificate.seriesArgument| ^ (2 * logRationalSeriesTerms + 1) /
    (1 - certificate.seriesArgument ^ 2)

def LogRationalIntervalCertificate.Valid
    (certificate : LogRationalIntervalCertificate) : Prop :=
  0 < certificate.input ∧ 0 ≤ certificate.error ∧
    |certificate.computed - certificate.seriesCenter| +
      certificate.seriesRemainder ≤ certificate.error

instance (certificate : LogRationalIntervalCertificate) :
    Decidable certificate.Valid := by
  unfold LogRationalIntervalCertificate.Valid
  infer_instance

def LogRationalIntervalCertificate.check
    (certificate : LogRationalIntervalCertificate) : Bool :=
  decide certificate.Valid

theorem LogRationalIntervalCertificate.approximates
    (certificate : LogRationalIntervalCertificate)
    (hvalid : certificate.Valid) :
    Approximates (certificate.computed : ℝ)
      (Real.log (certificate.input : ℝ)) (certificate.error : ℝ) := by
  have hinput : (0 : ℝ) < certificate.input := by exact_mod_cast hvalid.1
  let z : ℝ := ((certificate.input : ℝ) - 1) / (certificate.input + 1)
  have hz : |z| < 1 := by
    rw [abs_lt]
    constructor
    · dsimp only [z]
      apply (lt_div_iff₀ (by linarith)).2
      linarith
    · dsimp only [z]
      apply (div_lt_iff₀ (by linarith)).2
      linarith
  have hratio : (1 + z) / (1 - z) = (certificate.input : ℝ) := by
    dsimp only [z]
    field_simp
    ring
  have hseries := Real.sum_range_sub_log_div_le hz logRationalSeriesTerms
  rw [hratio] at hseries
  let center : ℝ := 2 * ∑ i ∈ Finset.range logRationalSeriesTerms,
    z ^ (2 * i + 1) / (2 * i + 1)
  let remainder : ℝ :=
    2 * |z| ^ (2 * logRationalSeriesTerms + 1) / (1 - z ^ 2)
  have hlog : |center - Real.log (certificate.input : ℝ)| ≤ remainder := by
    dsimp only [center, remainder]
    have htwo : (0 : ℝ) ≤ 2 := by norm_num
    have := mul_le_mul_of_nonneg_left hseries htwo
    calc
      _ = 2 * |1 / 2 * Real.log (certificate.input : ℝ) -
          ∑ i ∈ Finset.range logRationalSeriesTerms,
            z ^ (2 * i + 1) / (2 * i + 1)| := by
        rw [show center - Real.log (certificate.input : ℝ) =
          -2 * (1 / 2 * Real.log certificate.input -
            ∑ i ∈ Finset.range logRationalSeriesTerms,
              z ^ (2 * i + 1) / (2 * i + 1)) by simp [center]; ring,
          abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2 * (|z| ^ (2 * logRationalSeriesTerms + 1) /
          (1 - z ^ 2)) := this
      _ = _ := by ring
  have hcenter : (certificate.seriesCenter : ℝ) = center := by
    norm_num [LogRationalIntervalCertificate.seriesCenter,
      LogRationalIntervalCertificate.seriesArgument, center, z]
  have hremainder : (certificate.seriesRemainder : ℝ) = remainder := by
    norm_num [LogRationalIntervalCertificate.seriesRemainder,
      LogRationalIntervalCertificate.seriesArgument, remainder, z]
  have hsubmitted :
      |(certificate.computed : ℝ) - certificate.seriesCenter| +
        certificate.seriesRemainder ≤ certificate.error := by
    exact_mod_cast hvalid.2.2
  rw [← hcenter, ← hremainder] at hlog
  rw [Approximates]
  calc
    _ ≤ |(certificate.computed : ℝ) - certificate.seriesCenter| +
        |(certificate.seriesCenter : ℝ) - Real.log certificate.input| := by
      rw [show (certificate.computed : ℝ) - Real.log certificate.input =
        (certificate.computed - certificate.seriesCenter) +
          (certificate.seriesCenter - Real.log certificate.input) by ring]
      exact abs_add_le _ _
    _ ≤ |(certificate.computed : ℝ) - certificate.seriesCenter| +
        certificate.seriesRemainder := add_le_add le_rfl hlog
    _ ≤ certificate.error := hsubmitted

/-- A rational upper bound for the exponential on the nonpositive half-line.
It follows by applying `1 + y ≤ exp y` at `y = -x` and taking positive
reciprocals. -/
theorem exp_le_one_div_one_sub {x : ℝ} (hx : x ≤ 0) :
    Real.exp x ≤ 1 / (1 - x) := by
  have hden : 0 < 1 - x := by linarith
  have hexp : 1 - x ≤ Real.exp (-x) := by
    nlinarith [Real.add_one_le_exp (-x)]
  have hrewrite : Real.exp x = (Real.exp (-x))⁻¹ := by
    simpa only [neg_neg] using Real.exp_neg (-x)
  rw [hrewrite, one_div]
  exact (inv_le_inv₀ (Real.exp_pos (-x)) hden).2 hexp

/-- Rational enclosure for one observed nonpositive-input exponential call.
The interval uses only `max(0,1+x)` and `1/(1-x)`, so validity is decidable
over exact rationals and does not trust platform libm semantics. -/
structure ExpNonpositiveRationalIntervalCertificate where
  input : ℚ
  computed : ℚ
  error : ℚ
deriving DecidableEq, Repr

def ExpNonpositiveRationalIntervalCertificate.Valid
    (certificate : ExpNonpositiveRationalIntervalCertificate) : Prop :=
  certificate.input ≤ 0 ∧ 0 ≤ certificate.error ∧
    certificate.computed - certificate.error ≤
      max 0 (1 + certificate.input) ∧
    1 / (1 - certificate.input) ≤
      certificate.computed + certificate.error

instance (certificate : ExpNonpositiveRationalIntervalCertificate) :
    Decidable certificate.Valid := by
  unfold ExpNonpositiveRationalIntervalCertificate.Valid
  infer_instance

def ExpNonpositiveRationalIntervalCertificate.check
    (certificate : ExpNonpositiveRationalIntervalCertificate) : Bool :=
  decide certificate.Valid

theorem ExpNonpositiveRationalIntervalCertificate.approximates
    (certificate : ExpNonpositiveRationalIntervalCertificate)
    (hvalid : certificate.Valid) :
    Approximates (certificate.computed : ℝ)
      (Real.exp (certificate.input : ℝ)) (certificate.error : ℝ) := by
  have hinput : (certificate.input : ℝ) ≤ 0 := by exact_mod_cast hvalid.1
  have hlowerCertificate :
      (certificate.computed : ℝ) - certificate.error ≤
        max (0 : ℝ) (1 + (certificate.input : ℝ)) := by
    exact_mod_cast hvalid.2.2.1
  have hupperCertificate :
      (1 : ℝ) / (1 - certificate.input) ≤
        certificate.computed + certificate.error := by
    exact_mod_cast hvalid.2.2.2
  have hone : 1 + (certificate.input : ℝ) ≤
      Real.exp certificate.input := by
    nlinarith [Real.add_one_le_exp (certificate.input : ℝ)]
  have hlower : max 0 (1 + (certificate.input : ℝ)) ≤
      Real.exp certificate.input := max_le (Real.exp_pos _).le hone
  have hupper := exp_le_one_div_one_sub hinput
  rw [Approximates, abs_le]
  constructor <;> linarith

/-- Link the observed nonpositive exponential argument to a separate ideal
nonpositive stabilized log weight. Input rounding is transported with the
proved unit Lipschitz constant of `exp` on this half-line. -/
structure ExpNonpositiveTransportRationalCertificate where
  localCertificate : ExpNonpositiveRationalIntervalCertificate
  idealInput : ℚ
  inputError : ℚ
deriving DecidableEq, Repr

def ExpNonpositiveTransportRationalCertificate.Valid
    (certificate : ExpNonpositiveTransportRationalCertificate) : Prop :=
  certificate.localCertificate.Valid ∧ certificate.idealInput ≤ 0 ∧
    0 ≤ certificate.inputError ∧
    |certificate.localCertificate.input - certificate.idealInput| ≤
      certificate.inputError

instance (certificate : ExpNonpositiveTransportRationalCertificate) :
    Decidable certificate.Valid := by
  unfold ExpNonpositiveTransportRationalCertificate.Valid
  infer_instance

def ExpNonpositiveTransportRationalCertificate.check
    (certificate : ExpNonpositiveTransportRationalCertificate) : Bool :=
  decide certificate.Valid

theorem ExpNonpositiveTransportRationalCertificate.approximates
    (certificate : ExpNonpositiveTransportRationalCertificate)
    (hvalid : certificate.Valid) :
    Approximates (certificate.localCertificate.computed : ℝ)
      (Real.exp (certificate.idealInput : ℝ))
      ((certificate.localCertificate.error : ℝ) + certificate.inputError) := by
  have hinput : Approximates (certificate.localCertificate.input : ℝ)
      (certificate.idealInput : ℝ) certificate.inputError := by
    rw [Approximates]
    exact_mod_cast hvalid.2.2.2
  exact expNonpositive_approximates_of_exp_error
    (by exact_mod_cast hvalid.1.1) (by exact_mod_cast hvalid.2.1) hinput
    (certificate.localCertificate.approximates hvalid.1)

/-- Adapter to the exact maximum-stabilized weight expected by the multinomial
selection layer. -/
theorem ExpNonpositiveTransportRationalCertificate.stabilizedBoltzmannWeight_approximates
    {n : ℕ} [Nonempty (Fin n)]
    (certificate : ExpNonpositiveTransportRationalCertificate)
    (energy : Fin n → ℝ) (i : Fin n) (hvalid : certificate.Valid)
    (hlink : (certificate.idealInput : ℝ) =
      -energy i - finiteMaximum (fun j => -energy j)) :
    Approximates (certificate.localCertificate.computed : ℝ)
      (stabilizedBoltzmannWeight energy i)
      ((certificate.localCertificate.error : ℝ) + certificate.inputError) := by
  rw [stabilizedBoltzmannWeight, ← hlink]
  exact certificate.approximates hvalid

/-- A rational positive lower bound for hyperbolic tangent. It follows by
mapping `x / (1+x)` through `artanh`, using
`log (1+2x) ≤ 2x`, and applying the inverse relation with `tanh`. -/
theorem div_one_add_le_tanh {x : ℝ} (hx : 0 ≤ x) :
    x / (1 + x) ≤ Real.tanh x := by
  by_cases hxzero : x = 0
  · simp [hxzero]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
  let y := x / (1 + x)
  have hone : 0 < 1 + x := by positivity
  have hypos : 0 < y := div_pos hxpos hone
  have hylt : y < 1 := by
    rw [div_lt_one hone]
    linarith
  have hratio : (1 + y) / (1 - y) = 1 + 2 * x := by
    dsimp [y]
    field_simp
    ring
  have hartanh : Real.artanh y ≤ x := by
    rw [Real.artanh_eq_half_log (Set.mem_Icc.mpr ⟨by linarith, hylt.le⟩), hratio]
    nlinarith [Real.log_le_sub_one_of_pos (show 0 < 1 + 2 * x by positivity)]
  apply (Real.artanh_le_artanh_iff
    (Set.mem_Ioo.mpr ⟨by linarith, hylt⟩)
    (Set.mem_Ioo.mpr ⟨Real.neg_one_lt_tanh x, Real.tanh_lt_one x⟩)).mp
  rw [Real.artanh_tanh]
  exact hartanh

/-- Hyperbolic tangent lies below the identity on the nonnegative half-line. -/
theorem tanh_le_self {x : ℝ} (hx : 0 ≤ x) : Real.tanh x ≤ x := by
  let f : ℝ → ℝ := (fun y : ℝ => y) * Real.cosh - Real.sinh
  have hf (y : ℝ) : HasDerivAt (𝕜 := ℝ) f (y * Real.sinh y) y := by
    have hid : HasDerivAt (𝕜 := ℝ) (fun z : ℝ => z) 1 y :=
      hasDerivAt_id' y
    dsimp only [f]
    simpa only [one_mul, add_sub_cancel_left] using
      (hid.mul (Real.hasDerivAt_cosh y)).sub (Real.hasDerivAt_sinh y)
  have hderiv (y : ℝ) : 0 ≤ deriv f y := by
    rw [(hf y).deriv]
    rcases le_total 0 y with hy | hy
    · exact mul_nonneg hy (Real.sinh_nonneg_iff.mpr hy)
    · exact mul_nonneg_of_nonpos_of_nonpos hy
        (Real.sinh_nonpos_iff.mpr hy)
  have hmono : Monotone f := monotone_of_deriv_nonneg
    (fun y => (hf y).differentiableAt) hderiv
  have hnonneg : 0 ≤ f x := by
    simpa [f] using hmono hx
  rw [Real.tanh_eq_sinh_div_cosh]
  exact (div_le_iff₀ (Real.cosh_pos x)).2 (by
    dsimp [f] at hnonneg
    linarith)

/-- Hyperbolic tangent is globally one-Lipschitz. -/
theorem tanh_approximates_tanh {computed ideal error : ℝ}
    (hinput : Approximates computed ideal error) :
    Approximates (Real.tanh computed) (Real.tanh ideal) error := by
  let quotient : ℝ → ℝ := Real.sinh / Real.cosh
  let quotientDeriv : ℝ → ℝ := fun x =>
    (Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) /
      Real.cosh x ^ 2
  have hderiv (x : ℝ) : HasDerivAt (𝕜 := ℝ) quotient (quotientDeriv x) x := by
    dsimp only [quotient, quotientDeriv]
    exact (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x)
      (Real.cosh_pos x).ne'
  have hderivBound (x : ℝ) : ‖quotientDeriv x‖ ≤ (1 : ℝ) := by
    have hderivEq : quotientDeriv x = (Real.cosh x ^ 2)⁻¹ := by
      dsimp only [quotientDeriv]
      rw [show Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x = 1 by
        nlinarith [Real.cosh_sq_sub_sinh_sq x]]
      simp [div_eq_mul_inv]
    rw [hderivEq, Real.norm_eq_abs, abs_inv, abs_pow,
      abs_of_pos (Real.cosh_pos x)]
    have hcosh : 1 ≤ Real.cosh x := Real.one_le_cosh x
    have hsquare : 1 ≤ Real.cosh x ^ 2 := by nlinarith
    exact inv_le_one_of_one_le₀ hsquare
  have hbound := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (f := quotient) (f' := quotientDeriv)
    (x := ideal) (y := computed)
    (fun x _ => (hderiv x).hasDerivWithinAt)
    (fun x _ => hderivBound x) (Set.mem_univ _) (Set.mem_univ _)
  rw [Approximates] at hinput ⊢
  calc
    |Real.tanh computed - Real.tanh ideal| ≤
        1 * |computed - ideal| := by
      simpa [quotient, Real.tanh_eq_sinh_div_cosh, Real.norm_eq_abs] using hbound
    _ = |computed - ideal| := one_mul _
    _ ≤ error := hinput

/-- Rational enclosure of one positive-input hyperbolic-tangent execution.
The lower endpoint `x/(1+x)` is strictly positive and the upper endpoint is
one, so an accepted record remains usable as a denominator certificate. -/
structure TanhPositiveRationalIntervalCertificate where
  input : ℚ
  computed : ℚ
  error : ℚ
deriving DecidableEq, Repr

def TanhPositiveRationalIntervalCertificate.Valid
    (certificate : TanhPositiveRationalIntervalCertificate) : Prop :=
  0 < certificate.input ∧ 0 ≤ certificate.error ∧
    0 < certificate.computed - certificate.error ∧
    certificate.computed - certificate.error ≤
      certificate.input / (1 + certificate.input) ∧
    min certificate.input 1 ≤ certificate.computed + certificate.error

instance (certificate : TanhPositiveRationalIntervalCertificate) :
    Decidable certificate.Valid := by
  unfold TanhPositiveRationalIntervalCertificate.Valid
  infer_instance

def TanhPositiveRationalIntervalCertificate.check
    (certificate : TanhPositiveRationalIntervalCertificate) : Bool :=
  decide certificate.Valid

theorem TanhPositiveRationalIntervalCertificate.approximates
    (certificate : TanhPositiveRationalIntervalCertificate)
    (hvalid : certificate.Valid) :
    Approximates (certificate.computed : ℝ)
      (Real.tanh (certificate.input : ℝ)) (certificate.error : ℝ) := by
  have hinput : (0 : ℝ) < certificate.input := by exact_mod_cast hvalid.1
  have hlowerCertificate :
      (certificate.computed : ℝ) - certificate.error ≤
        certificate.input / (1 + certificate.input) := by
    exact_mod_cast hvalid.2.2.2.1
  have hupperCertificate :
      min (certificate.input : ℝ) 1 ≤
        certificate.computed + certificate.error := by
    exact_mod_cast hvalid.2.2.2.2
  have hlower := div_one_add_le_tanh hinput.le
  have hupper : Real.tanh (certificate.input : ℝ) ≤
      min (certificate.input : ℝ) 1 :=
    le_min (tanh_le_self hinput.le)
      (Real.tanh_lt_one (certificate.input : ℝ)).le
  rw [Approximates, abs_le]
  constructor <;> linarith

/-- Acceptance also proves a strictly positive lower endpoint for the
computed denominator. -/
theorem TanhPositiveRationalIntervalCertificate.computed_sub_error_pos
    (certificate : TanhPositiveRationalIntervalCertificate)
    (hvalid : certificate.Valid) :
    (0 : ℝ) < certificate.computed - certificate.error := by
  exact_mod_cast hvalid.2.2.1

/-- Reciprocal transport has an exact condition-number factor. This removes
the analytic part of a backend reciprocal certificate; only local rounding at
the computed input remains backend-specific. -/
theorem inv_approximates_inv
    {computed ideal error : ℝ}
    (hcomputed : computed ≠ 0) (hideal : ideal ≠ 0)
    (hinput : Approximates computed ideal error) :
    Approximates computed⁻¹ ideal⁻¹
      (error / (|computed| * |ideal|)) := by
  rw [Approximates] at hinput ⊢
  rw [inv_sub_inv hcomputed hideal, abs_div, abs_mul, abs_sub_comm]
  exact div_le_div_of_nonneg_right hinput
    (mul_nonneg (abs_nonneg computed) (abs_nonneg ideal))

/-- Compose checked square-root and reciprocal executions. The resulting
factor bound targets the inverse square root of the original rational input,
which is the derived primitive used by a diagonal SoftAbs metric. -/
theorem SqrtRationalIntervalCertificate.reciprocal_approximates
    (sqrtCertificate : SqrtRationalIntervalCertificate)
    (reciprocalCertificate : ReciprocalRationalResidualCertificate)
    (hsqrt : sqrtCertificate.Valid)
    (hreciprocal : reciprocalCertificate.Valid)
    (hinput : 0 < sqrtCertificate.input)
    (hlink : reciprocalCertificate.input = sqrtCertificate.computed) :
    Approximates (reciprocalCertificate.computed : ℝ)
      (Real.sqrt (sqrtCertificate.input : ℝ))⁻¹
      ((reciprocalCertificate.error : ℝ) +
        (sqrtCertificate.error : ℝ) /
          (|(sqrtCertificate.computed : ℝ)| *
            |Real.sqrt (sqrtCertificate.input : ℝ)|)) := by
  have hcomputed : sqrtCertificate.computed ≠ 0 := by
    intro hzero
    have herror : sqrtCertificate.error = 0 := by
      have := hsqrt.2.2.1
      rw [hzero] at this
      exact le_antisymm (by linarith) hsqrt.2.1
    have hupper := hsqrt.2.2.2.2
    rw [hzero, herror] at hupper
    norm_num at hupper
    linarith
  have hideal : Real.sqrt (sqrtCertificate.input : ℝ) ≠ 0 := by
    apply (Real.sqrt_pos.2 ?_).ne'
    exact_mod_cast hinput
  have hlocal : Approximates (reciprocalCertificate.computed : ℝ)
      (sqrtCertificate.computed : ℝ)⁻¹
      (reciprocalCertificate.error : ℝ) := by
    simpa [hlink] using reciprocalCertificate.approximates hreciprocal
  exact hlocal.trans (inv_approximates_inv
    (by exact_mod_cast hcomputed) hideal (sqrtCertificate.approximates hsqrt))

/-- Compose a backend's local reciprocal-rounding error with the exact
transport factor from an already approximate nonzero input. -/
theorem inv_backend_approximates
    {computedInv computed ideal localError inputError : ℝ}
    (hlocal : Approximates computedInv computed⁻¹ localError)
    (hinput : Approximates computed ideal inputError)
    (hcomputed : computed ≠ 0) (hideal : ideal ≠ 0) :
    Approximates computedInv ideal⁻¹
      (localError + inputError / (|computed| * |ideal|)) :=
  hlocal.trans (inv_approximates_inv hcomputed hideal hinput)

/-- Exact-rational record for the positive branch of one SoftAbs transform.
It combines a positive `tanh` enclosure with the observed rounded division. -/
structure PositiveSoftAbsRationalCertificate where
  smoothing : ℚ
  hessian : ℚ
  computedArgument : ℚ
  argumentError : ℚ
  computedTanh : ℚ
  tanhError : ℚ
  computedEigenvalue : ℚ
  divisionError : ℚ
deriving DecidableEq, Repr

def PositiveSoftAbsRationalCertificate.tanhCertificate
    (certificate : PositiveSoftAbsRationalCertificate) :
    TanhPositiveRationalIntervalCertificate where
  input := certificate.computedArgument
  computed := certificate.computedTanh
  error := certificate.tanhError

def PositiveSoftAbsRationalCertificate.Valid
    (certificate : PositiveSoftAbsRationalCertificate) : Prop :=
  0 < certificate.smoothing ∧ 0 < certificate.hessian ∧
    0 ≤ certificate.argumentError ∧
    |certificate.computedArgument -
      certificate.smoothing * certificate.hessian| ≤ certificate.argumentError ∧
    certificate.tanhCertificate.Valid ∧ 0 < certificate.computedEigenvalue ∧
    0 ≤ certificate.divisionError ∧
    |certificate.computedEigenvalue -
      certificate.hessian / certificate.computedTanh| ≤
        certificate.divisionError

instance (certificate : PositiveSoftAbsRationalCertificate) :
    Decidable certificate.Valid := by
  unfold PositiveSoftAbsRationalCertificate.Valid
  infer_instance

def PositiveSoftAbsRationalCertificate.check
    (certificate : PositiveSoftAbsRationalCertificate) : Bool :=
  decide certificate.Valid

/-- An accepted positive-branch record proves the complete observed SoftAbs
eigenvalue bound. The first summand is division rounding; the second transports
the certified `tanh` error through reciprocal and multiplication by Hessian. -/
theorem PositiveSoftAbsRationalCertificate.eigenvalue_approximates
    (certificate : PositiveSoftAbsRationalCertificate)
    (hvalid : certificate.Valid) :
    Approximates (certificate.computedEigenvalue : ℝ)
      (Mcmc.Relativistic.softAbs (certificate.smoothing : ℝ)
        (certificate.hessian : ℝ))
      ((certificate.divisionError : ℝ) +
        |(certificate.hessian : ℝ)| *
          (((certificate.tanhError : ℝ) + certificate.argumentError) /
            (|(certificate.computedTanh : ℝ)| *
              |Real.tanh ((certificate.smoothing : ℝ) *
                certificate.hessian)|))) := by
  rcases hvalid with ⟨hsmoothing, hhessian, hargumentError, hargumentBound,
    htanhValid, heigenvaluePositive, hdivisionError, hdivisionBound⟩
  have htanhLocal : Approximates (certificate.computedTanh : ℝ)
      (Real.tanh (certificate.computedArgument : ℝ))
      (certificate.tanhError : ℝ) := by
    simpa [PositiveSoftAbsRationalCertificate.tanhCertificate] using
      certificate.tanhCertificate.approximates htanhValid
  have hargument : Approximates (certificate.computedArgument : ℝ)
      ((certificate.smoothing : ℝ) * certificate.hessian)
      (certificate.argumentError : ℝ) := by
    rw [Approximates]
    exact_mod_cast hargumentBound
  have htanh : Approximates (certificate.computedTanh : ℝ)
      (Real.tanh ((certificate.smoothing : ℝ) * certificate.hessian))
      ((certificate.tanhError : ℝ) + certificate.argumentError) :=
    htanhLocal.trans (tanh_approximates_tanh hargument)
  have hcomputedTanh : (certificate.computedTanh : ℝ) ≠ 0 := by
    have hpositive : (0 : ℝ) <
        certificate.computedTanh - certificate.tanhError := by
      simpa [PositiveSoftAbsRationalCertificate.tanhCertificate] using
        certificate.tanhCertificate.computed_sub_error_pos htanhValid
    have herror : (0 : ℝ) ≤ certificate.tanhError := by
      exact_mod_cast htanhValid.2.1
    linarith
  have hidealTanh : Real.tanh ((certificate.smoothing : ℝ) *
      certificate.hessian) ≠ 0 := by
    apply (Mcmc.Relativistic.real_tanh_pos ?_).ne'
    exact mul_pos (by exact_mod_cast hsmoothing) (by exact_mod_cast hhessian)
  have hinv := inv_approximates_inv hcomputedTanh hidealTanh htanh
  have hscaled := (Approximates.refl (certificate.hessian : ℝ)).mul hinv
  have htransport : Approximates
      ((certificate.hessian : ℝ) * (certificate.computedTanh : ℝ)⁻¹)
      ((certificate.hessian : ℝ) *
        (Real.tanh ((certificate.smoothing : ℝ) * certificate.hessian))⁻¹)
      (|(certificate.hessian : ℝ)| *
        (((certificate.tanhError : ℝ) + certificate.argumentError) /
          (|(certificate.computedTanh : ℝ)| *
            |Real.tanh ((certificate.smoothing : ℝ) *
              certificate.hessian)|))) := by
    simpa using hscaled
  have hlocal : Approximates (certificate.computedEigenvalue : ℝ)
      ((certificate.hessian : ℝ) * (certificate.computedTanh : ℝ)⁻¹)
      (certificate.divisionError : ℝ) := by
    rw [Approximates]
    exact_mod_cast hdivisionBound
  rw [Mcmc.Relativistic.softAbs, if_neg (by
    exact_mod_cast hhessian.ne')]
  simpa [div_eq_mul_inv] using hlocal.trans htransport

/-- A rational lower bound below the observed `tanh` minus both the local and
argument-transport radii is also a lower bound for the ideal `tanh(αh)`.
This is the denominator witness needed to turn the exact SoftAbs conditioning
factor into a rational upper error bound. -/
theorem PositiveSoftAbsRationalCertificate.le_idealTanh
    (certificate : PositiveSoftAbsRationalCertificate)
    (hvalid : certificate.Valid) {lower : ℚ}
    (hlower : lower ≤ certificate.computedTanh -
      (certificate.tanhError + certificate.argumentError)) :
    (lower : ℝ) ≤ Real.tanh
      ((certificate.smoothing : ℝ) * certificate.hessian) := by
  have htanhLocal : Approximates (certificate.computedTanh : ℝ)
      (Real.tanh (certificate.computedArgument : ℝ))
      (certificate.tanhError : ℝ) := by
    simpa [PositiveSoftAbsRationalCertificate.tanhCertificate] using
      certificate.tanhCertificate.approximates hvalid.2.2.2.2.1
  have hargument : Approximates (certificate.computedArgument : ℝ)
      ((certificate.smoothing : ℝ) * certificate.hessian)
      (certificate.argumentError : ℝ) := by
    rw [Approximates]
    exact_mod_cast hvalid.2.2.2.1
  have htanh := htanhLocal.trans (tanh_approximates_tanh hargument)
  have htanhUpper := (abs_le.mp htanh).2
  have hlowerReal : (lower : ℝ) ≤ certificate.computedTanh -
      (certificate.tanhError + certificate.argumentError) := by
    exact_mod_cast hlower
  linarith

/-- On the positive domain, square-root transport has the exact secant factor
`1 / (sqrt computed + sqrt ideal)`. -/
theorem sqrt_approximates_sqrt
    {computed ideal error : ℝ}
    (hcomputed : 0 < computed) (hideal : 0 < ideal)
    (hinput : Approximates computed ideal error) :
    Approximates (Real.sqrt computed) (Real.sqrt ideal)
      (error / (Real.sqrt computed + Real.sqrt ideal)) := by
  rw [Approximates] at hinput ⊢
  have hsum : 0 < Real.sqrt computed + Real.sqrt ideal := by positivity
  have hidentity :
      Real.sqrt computed - Real.sqrt ideal =
        (computed - ideal) /
          (Real.sqrt computed + Real.sqrt ideal) := by
    apply (eq_div_iff hsum.ne').2
    nlinarith [Real.sq_sqrt hcomputed.le, Real.sq_sqrt hideal.le]
  rw [hidentity, abs_div, abs_of_pos hsum]
  exact div_le_div_of_nonneg_right hinput hsum.le

/-- Compose local square-root rounding with positive-domain input transport. -/
theorem sqrt_backend_approximates
    {computedSqrt computed ideal localError inputError : ℝ}
    (hlocal : Approximates computedSqrt (Real.sqrt computed) localError)
    (hinput : Approximates computed ideal inputError)
    (hcomputed : 0 < computed) (hideal : 0 < ideal) :
    Approximates computedSqrt (Real.sqrt ideal)
      (localError + inputError /
        (Real.sqrt computed + Real.sqrt ideal)) :=
  hlocal.trans (sqrt_approximates_sqrt hcomputed hideal hinput)

/-- Positive-domain logarithm transport is Lipschitz on the interval between
the two arguments, with factor `1 / min computed ideal`. -/
theorem log_approximates_log
    {computed ideal error : ℝ}
    (hcomputed : 0 < computed) (hideal : 0 < ideal)
    (hinput : Approximates computed ideal error) :
    Approximates (Real.log computed) (Real.log ideal)
      ((min computed ideal)⁻¹ * error) := by
  rw [Approximates] at hinput ⊢
  have hlower : 0 < min computed ideal := lt_min hcomputed hideal
  have hmean :
      |Real.log computed - Real.log ideal| ≤
        (min computed ideal)⁻¹ * |computed - ideal| := by
    have hbound := Convex.norm_image_sub_le_of_norm_deriv_le
      (s := Set.Ici (min computed ideal)) (f := Real.log)
      (fun x hx => Real.differentiableAt_log (ne_of_gt (hlower.trans_le hx)))
      (fun x hx => by
        rw [Real.deriv_log, Real.norm_eq_abs, abs_of_pos
          (inv_pos.mpr (hlower.trans_le hx))]
        exact (inv_le_inv₀ (hlower.trans_le hx) hlower).2 hx)
      (convex_Ici (min computed ideal))
      (show ideal ∈ Set.Ici (min computed ideal) from min_le_right computed ideal)
      (show computed ∈ Set.Ici (min computed ideal) from min_le_left computed ideal)
    simpa [Real.norm_eq_abs, abs_sub_comm] using hbound
  exact hmean.trans
    (mul_le_mul_of_nonneg_left hinput (inv_nonneg.mpr hlower.le))

/-- Compose local logarithm error with its analytic positive-domain transport
factor. -/
theorem log_backend_approximates
    {computedLog computed ideal localError inputError : ℝ}
    (hlocal : Approximates computedLog (Real.log computed) localError)
    (hinput : Approximates computed ideal inputError)
    (hcomputed : 0 < computed) (hideal : 0 < ideal) :
    Approximates computedLog (Real.log ideal)
      (localError + (min computed ideal)⁻¹ * inputError) :=
  hlocal.trans (log_approximates_log hcomputed hideal hinput)

/-- Transport a checked execution-specific logarithm enclosure from its
rational computed input to an approximate positive ideal input. -/
theorem LogRationalIntervalCertificate.transport_approximates
    (certificate : LogRationalIntervalCertificate)
    (hvalid : certificate.Valid) {ideal inputError : ℝ}
    (hideal : 0 < ideal)
    (hinput : Approximates (certificate.input : ℝ) ideal inputError) :
    Approximates (certificate.computed : ℝ) (Real.log ideal)
      ((certificate.error : ℝ) +
        (min (certificate.input : ℝ) ideal)⁻¹ * inputError) :=
  log_backend_approximates (certificate.approximates hvalid) hinput
    (by exact_mod_cast hvalid.1) hideal

/-- Operation-local numerical contract for one scalar SoftAbs metric entry.
Each transport theorem includes both local backend error and argument error;
the backend or a platform-specific refinement layer supplies those facts. -/
structure SoftAbsPrimitiveBackend where
  softAbs : ℝ → ℝ → ℝ
  sqrt : ℝ → ℝ
  inv : ℝ → ℝ
  log : ℝ → ℝ
  softAbsError : ℝ → ℝ → ℝ → ℝ → ℝ
  sqrtError : ℝ → ℝ → ℝ → ℝ
  invError : ℝ → ℝ → ℝ → ℝ
  logError : ℝ → ℝ → ℝ → ℝ
  softAbs_bound : ∀ α computed ideal error,
    0 < α → Approximates computed ideal error →
      Approximates (softAbs α computed) (Mcmc.Relativistic.softAbs α ideal)
        (softAbsError α computed ideal error)
  sqrt_bound : ∀ computed ideal error,
    0 < computed → 0 < ideal → Approximates computed ideal error →
      Approximates (sqrt computed) (Real.sqrt ideal)
        (sqrtError computed ideal error)
  inv_bound : ∀ computed ideal error,
    computed ≠ 0 → ideal ≠ 0 → Approximates computed ideal error →
      Approximates (inv computed) ideal⁻¹ (invError computed ideal error)
  log_bound : ∀ computed ideal error,
    0 < computed → 0 < ideal → Approximates computed ideal error →
      Approximates (log computed) (Real.log ideal)
        (logError computed ideal error)

/-- Easier platform contract: SoftAbs still carries its complete transport
bound, while square root, reciprocal, and logarithm require only local error
at the computed argument. Lean supplies their analytic input transport. -/
structure SoftAbsLocalPrimitiveBackend where
  softAbs : ℝ → ℝ → ℝ
  sqrt : ℝ → ℝ
  inv : ℝ → ℝ
  log : ℝ → ℝ
  softAbsError : ℝ → ℝ → ℝ → ℝ → ℝ
  sqrtLocalError : ℝ → ℝ
  invLocalError : ℝ → ℝ
  logLocalError : ℝ → ℝ
  softAbs_bound : ∀ α computed ideal error,
    0 < α → Approximates computed ideal error →
      Approximates (softAbs α computed) (Mcmc.Relativistic.softAbs α ideal)
        (softAbsError α computed ideal error)
  sqrt_local_bound : ∀ value, 0 < value →
    Approximates (sqrt value) (Real.sqrt value) (sqrtLocalError value)
  inv_local_bound : ∀ value, value ≠ 0 →
    Approximates (inv value) value⁻¹ (invLocalError value)
  log_local_bound : ∀ value, 0 < value →
    Approximates (log value) (Real.log value) (logLocalError value)

/-- Upgrade local positive-domain primitive bounds to the complete
transport-aware metric backend. -/
noncomputable def SoftAbsLocalPrimitiveBackend.toSoftAbsPrimitiveBackend
    (backend : SoftAbsLocalPrimitiveBackend) : SoftAbsPrimitiveBackend where
  softAbs := backend.softAbs
  sqrt := backend.sqrt
  inv := backend.inv
  log := backend.log
  softAbsError := backend.softAbsError
  sqrtError computed ideal error :=
    backend.sqrtLocalError computed +
      error / (Real.sqrt computed + Real.sqrt ideal)
  invError computed ideal error :=
    backend.invLocalError computed + error / (|computed| * |ideal|)
  logError computed ideal error :=
    backend.logLocalError computed + (min computed ideal)⁻¹ * error
  softAbs_bound := backend.softAbs_bound
  sqrt_bound computed _ideal _error hcomputed hideal hinput :=
    sqrt_backend_approximates (backend.sqrt_local_bound computed hcomputed)
      hinput hcomputed hideal
  inv_bound computed _ideal _error hcomputed hideal hinput :=
    inv_backend_approximates (backend.inv_local_bound computed hcomputed)
      hinput hcomputed hideal
  log_bound computed _ideal _error hcomputed hideal hinput :=
    log_backend_approximates (backend.log_local_bound computed hcomputed)
      hinput hcomputed hideal

/-- End-to-end numerical witness for one diagonal SoftAbs eigenvalue, its
inverse-square-root factor, and its log-determinant contribution. -/
structure SoftAbsMetricEntryCertificate (α idealHessian : ℝ) where
  computedHessian : ℝ
  computedEigenvalue : ℝ
  computedSqrt : ℝ
  computedFactor : ℝ
  computedLogDet : ℝ
  hessianError : ℝ
  eigenvalueError : ℝ
  sqrtError : ℝ
  factorError : ℝ
  logDetError : ℝ
  hessian_bound : Approximates computedHessian idealHessian hessianError
  eigenvalue_bound : Approximates computedEigenvalue
    (Mcmc.Relativistic.softAbs α idealHessian) eigenvalueError
  factor_bound : Approximates computedFactor
    (Real.sqrt (Mcmc.Relativistic.softAbs α idealHessian))⁻¹ factorError
  logDet_bound : Approximates computedLogDet
    (Real.log (Mcmc.Relativistic.softAbs α idealHessian)) logDetError

/-- A checked runtime record at the unit/zero SoftAbs point produces the full
metric-entry certificate with zero error, including the ordinarily
transcendental square-root and logarithm fields. -/
noncomputable def UnitZeroSoftAbsRationalCertificate.metricEntryCertificate
    (certificate : UnitZeroSoftAbsRationalCertificate)
    (hvalid : certificate.Valid) : SoftAbsMetricEntryCertificate 1 0 where
  computedHessian := certificate.computedHessian
  computedEigenvalue := certificate.computedEigenvalue
  computedSqrt := certificate.computedSqrt
  computedFactor := certificate.computedFactor
  computedLogDet := certificate.computedLogDet
  hessianError := 0
  eigenvalueError := 0
  sqrtError := 0
  factorError := 0
  logDetError := 0
  hessian_bound := by
    norm_num [Approximates, hvalid.1]
  eigenvalue_bound := by
    rw [hvalid.2.1, softAbs_zero]
    norm_num [Approximates]
  factor_bound := by
    rw [hvalid.2.2.2.1, softAbs_zero]
    norm_num [Approximates]
  logDet_bound := by
    rw [hvalid.2.2.2.2, softAbs_zero]
    norm_num [Approximates]

/-- Linked rational witnesses for every primitive in one positive-branch
SoftAbs metric entry. Field equalities ensure that each observed output is the
next primitive's actual input. -/
structure PositiveSoftAbsMetricRationalCertificate where
  eigenvalue : PositiveSoftAbsRationalCertificate
  sqrt : SqrtRationalIntervalCertificate
  factor : ReciprocalRationalResidualCertificate
  logDet : LogRationalIntervalCertificate
  sqrtInput : sqrt.input = eigenvalue.computedEigenvalue
  factorInput : factor.input = sqrt.computed
  logInput : logDet.input = eigenvalue.computedEigenvalue
deriving DecidableEq, Repr

def PositiveSoftAbsMetricRationalCertificate.Valid
    (certificate : PositiveSoftAbsMetricRationalCertificate) : Prop :=
  certificate.eigenvalue.Valid ∧ certificate.sqrt.Valid ∧
    certificate.factor.Valid ∧ certificate.logDet.Valid

instance (certificate : PositiveSoftAbsMetricRationalCertificate) :
    Decidable certificate.Valid := by
  unfold PositiveSoftAbsMetricRationalCertificate.Valid
  infer_instance

def PositiveSoftAbsMetricRationalCertificate.check
    (certificate : PositiveSoftAbsMetricRationalCertificate) : Bool :=
  decide certificate.Valid

/-- A linked accepted record constructs the complete guarded metric-entry
certificate, with all transport terms generated by Lean. -/
noncomputable def PositiveSoftAbsMetricRationalCertificate.metricEntryCertificate
    (certificate : PositiveSoftAbsMetricRationalCertificate)
    (hvalid : certificate.Valid) :
    SoftAbsMetricEntryCertificate certificate.eigenvalue.smoothing
      certificate.eigenvalue.hessian := by
  rcases hvalid with ⟨heigenValid, hsqrtValid, hfactorValid, hlogValid⟩
  let idealEigenvalue := Mcmc.Relativistic.softAbs
    (certificate.eigenvalue.smoothing : ℝ) certificate.eigenvalue.hessian
  let eigenvalueError : ℝ :=
    certificate.eigenvalue.divisionError +
      |(certificate.eigenvalue.hessian : ℝ)| *
        ((certificate.eigenvalue.tanhError +
            certificate.eigenvalue.argumentError) /
          (|(certificate.eigenvalue.computedTanh : ℝ)| *
            |Real.tanh ((certificate.eigenvalue.smoothing : ℝ) *
              certificate.eigenvalue.hessian)|))
  have heigen : Approximates (certificate.eigenvalue.computedEigenvalue : ℝ)
      idealEigenvalue eigenvalueError :=
    certificate.eigenvalue.eigenvalue_approximates heigenValid
  have hcomputedEigenvalue :
      (0 : ℝ) < certificate.eigenvalue.computedEigenvalue := by
    exact_mod_cast heigenValid.2.2.2.2.2.1
  have hidealEigenvalue : 0 < idealEigenvalue :=
    Mcmc.Relativistic.softAbs_pos _ (by exact_mod_cast heigenValid.1) _
  have hsqrtLocal : Approximates (certificate.sqrt.computed : ℝ)
      (Real.sqrt (certificate.eigenvalue.computedEigenvalue : ℝ))
      certificate.sqrt.error := by
    simpa [certificate.sqrtInput] using certificate.sqrt.approximates hsqrtValid
  let sqrtError : ℝ := certificate.sqrt.error +
    eigenvalueError /
      (Real.sqrt certificate.eigenvalue.computedEigenvalue +
        Real.sqrt idealEigenvalue)
  have hsqrt : Approximates (certificate.sqrt.computed : ℝ)
      (Real.sqrt idealEigenvalue) sqrtError :=
    sqrt_backend_approximates hsqrtLocal heigen hcomputedEigenvalue
      hidealEigenvalue
  have hcomputedSqrt : (certificate.sqrt.computed : ℝ) ≠ 0 := by
    exact_mod_cast (certificate.factorInput ▸ hfactorValid.1)
  have hidealSqrt : Real.sqrt idealEigenvalue ≠ 0 :=
    (Real.sqrt_pos.2 hidealEigenvalue).ne'
  have hfactorLocal : Approximates (certificate.factor.computed : ℝ)
      (certificate.sqrt.computed : ℝ)⁻¹ certificate.factor.error := by
    simpa [certificate.factorInput] using
      certificate.factor.approximates hfactorValid
  let factorError : ℝ := certificate.factor.error +
    sqrtError /
      (|(certificate.sqrt.computed : ℝ)| * |Real.sqrt idealEigenvalue|)
  have hfactor : Approximates (certificate.factor.computed : ℝ)
      (Real.sqrt idealEigenvalue)⁻¹ factorError :=
    inv_backend_approximates hfactorLocal hsqrt hcomputedSqrt hidealSqrt
  have hlogLocal : Approximates (certificate.logDet.computed : ℝ)
      (Real.log (certificate.eigenvalue.computedEigenvalue : ℝ))
      certificate.logDet.error := by
    simpa [certificate.logInput] using certificate.logDet.approximates hlogValid
  let logDetError : ℝ := certificate.logDet.error +
    (min (certificate.eigenvalue.computedEigenvalue : ℝ) idealEigenvalue)⁻¹ *
      eigenvalueError
  have hlog : Approximates (certificate.logDet.computed : ℝ)
      (Real.log idealEigenvalue) logDetError :=
    log_backend_approximates hlogLocal heigen hcomputedEigenvalue hidealEigenvalue
  exact {
    computedHessian := certificate.eigenvalue.hessian
    computedEigenvalue := certificate.eigenvalue.computedEigenvalue
    computedSqrt := certificate.sqrt.computed
    computedFactor := certificate.factor.computed
    computedLogDet := certificate.logDet.computed
    hessianError := 0
    eigenvalueError := eigenvalueError
    sqrtError := sqrtError
    factorError := factorError
    logDetError := logDetError
    hessian_bound := Approximates.refl _
    eigenvalue_bound := heigen
    factor_bound := hfactor
    logDet_bound := hlog }

@[simp] theorem PositiveSoftAbsMetricRationalCertificate.metricEntryCertificate_computedFactor
    (certificate : PositiveSoftAbsMetricRationalCertificate)
    (hvalid : certificate.Valid) :
    (certificate.metricEntryCertificate hvalid).computedFactor =
      certificate.factor.computed := by
  rcases hvalid with ⟨heigenValid, hsqrtValid, hfactorValid, hlogValid⟩
  unfold PositiveSoftAbsMetricRationalCertificate.metricEntryCertificate
  rfl

@[simp] theorem PositiveSoftAbsMetricRationalCertificate.metricEntryCertificate_computedEigenvalue
    (certificate : PositiveSoftAbsMetricRationalCertificate)
    (hvalid : certificate.Valid) :
    (certificate.metricEntryCertificate hvalid).computedEigenvalue =
      certificate.eigenvalue.computedEigenvalue := by
  rcases hvalid with ⟨heigenValid, hsqrtValid, hfactorValid, hlogValid⟩
  unfold PositiveSoftAbsMetricRationalCertificate.metricEntryCertificate
  rfl

@[simp] theorem PositiveSoftAbsMetricRationalCertificate.metricEntryCertificate_computedLogDet
    (certificate : PositiveSoftAbsMetricRationalCertificate)
    (hvalid : certificate.Valid) :
    (certificate.metricEntryCertificate hvalid).computedLogDet =
      certificate.logDet.computed := by
  rcases hvalid with ⟨heigenValid, hsqrtValid, hfactorValid, hlogValid⟩
  unfold PositiveSoftAbsMetricRationalCertificate.metricEntryCertificate
  rfl

@[simp] theorem PositiveSoftAbsMetricRationalCertificate.metricEntryCertificate_sqrtError
    (certificate : PositiveSoftAbsMetricRationalCertificate)
    (hvalid : certificate.Valid) :
    (certificate.metricEntryCertificate hvalid).sqrtError =
      (certificate.sqrt.error : ℝ) +
        (certificate.metricEntryCertificate hvalid).eigenvalueError /
          (Real.sqrt (certificate.eigenvalue.computedEigenvalue : ℝ) +
            Real.sqrt (Mcmc.Relativistic.softAbs
              (certificate.eigenvalue.smoothing : ℝ)
              certificate.eigenvalue.hessian)) := by
  rcases hvalid with ⟨heigenValid, hsqrtValid, hfactorValid, hlogValid⟩
  unfold PositiveSoftAbsMetricRationalCertificate.metricEntryCertificate
  rfl

@[simp] theorem PositiveSoftAbsMetricRationalCertificate.metricEntryCertificate_factorError
    (certificate : PositiveSoftAbsMetricRationalCertificate)
    (hvalid : certificate.Valid) :
    (certificate.metricEntryCertificate hvalid).factorError =
      (certificate.factor.error : ℝ) +
        (certificate.metricEntryCertificate hvalid).sqrtError /
          (|(certificate.sqrt.computed : ℝ)| *
            |Real.sqrt (Mcmc.Relativistic.softAbs
              (certificate.eigenvalue.smoothing : ℝ)
              certificate.eigenvalue.hessian)|) := by
  rcases hvalid with ⟨heigenValid, hsqrtValid, hfactorValid, hlogValid⟩
  unfold PositiveSoftAbsMetricRationalCertificate.metricEntryCertificate
  rfl

@[simp] theorem PositiveSoftAbsMetricRationalCertificate.metricEntryCertificate_logDetError
    (certificate : PositiveSoftAbsMetricRationalCertificate)
    (hvalid : certificate.Valid) :
    (certificate.metricEntryCertificate hvalid).logDetError =
      (certificate.logDet.error : ℝ) +
        (min (certificate.eigenvalue.computedEigenvalue : ℝ)
          (Mcmc.Relativistic.softAbs
            (certificate.eigenvalue.smoothing : ℝ)
            certificate.eigenvalue.hessian))⁻¹ *
          (certificate.metricEntryCertificate hvalid).eigenvalueError := by
  rcases hvalid with ⟨heigenValid, hsqrtValid, hfactorValid, hlogValid⟩
  unfold PositiveSoftAbsMetricRationalCertificate.metricEntryCertificate
  rfl

/-- Rational lower-denominator witnesses for converting the exact analytical
errors of a positive SoftAbs metric entry into serializable rational upper
bounds. -/
structure PositiveSoftAbsMetricErrorUpperCertificate where
  metric : PositiveSoftAbsMetricRationalCertificate
  idealTanhLower : ℚ
  computedSqrtLower : ℚ
  idealSqrtLower : ℚ
deriving DecidableEq, Repr

namespace PositiveSoftAbsMetricErrorUpperCertificate

def eigenvalueError
    (certificate : PositiveSoftAbsMetricErrorUpperCertificate) : ℚ :=
  certificate.metric.eigenvalue.divisionError +
    |certificate.metric.eigenvalue.hessian| *
      ((certificate.metric.eigenvalue.tanhError +
        certificate.metric.eigenvalue.argumentError) /
        (|certificate.metric.eigenvalue.computedTanh| *
          certificate.idealTanhLower))

def sqrtError
    (certificate : PositiveSoftAbsMetricErrorUpperCertificate) : ℚ :=
  certificate.metric.sqrt.error + certificate.eigenvalueError /
    (certificate.computedSqrtLower + certificate.idealSqrtLower)

def factorError
    (certificate : PositiveSoftAbsMetricErrorUpperCertificate) : ℚ :=
  certificate.metric.factor.error + certificate.sqrtError /
    (|certificate.metric.sqrt.computed| * certificate.idealSqrtLower)

def logDetError
    (certificate : PositiveSoftAbsMetricErrorUpperCertificate) : ℚ :=
  certificate.metric.logDet.error + certificate.eigenvalueError /
    min certificate.metric.eigenvalue.computedEigenvalue
      (certificate.idealSqrtLower ^ 2)

def Valid (certificate : PositiveSoftAbsMetricErrorUpperCertificate) : Prop :=
  certificate.metric.Valid ∧
    0 < certificate.idealTanhLower ∧
    certificate.idealTanhLower ≤
      certificate.metric.eigenvalue.computedTanh -
        (certificate.metric.eigenvalue.tanhError +
          certificate.metric.eigenvalue.argumentError) ∧
    0 < certificate.computedSqrtLower ∧
    certificate.computedSqrtLower ≤
      certificate.metric.sqrt.computed - certificate.metric.sqrt.error ∧
    0 < certificate.idealSqrtLower ∧
    certificate.idealSqrtLower ^ 2 ≤
      certificate.metric.eigenvalue.computedEigenvalue -
        certificate.eigenvalueError

instance (certificate : PositiveSoftAbsMetricErrorUpperCertificate) :
    Decidable certificate.Valid := by
  unfold Valid eigenvalueError
  infer_instance

def check (certificate : PositiveSoftAbsMetricErrorUpperCertificate) : Bool :=
  decide certificate.Valid

theorem eigenvalueError_nonneg
    (certificate : PositiveSoftAbsMetricErrorUpperCertificate)
    (hvalid : certificate.Valid) : 0 ≤ certificate.eigenvalueError := by
  rcases hvalid.1.1 with
    ⟨_, _, hargumentError, _, htanhValid, _, hdivisionError, _⟩
  have htanhError : 0 ≤ certificate.metric.eigenvalue.tanhError :=
    htanhValid.2.1
  have hcomputedTanh : 0 < certificate.metric.eigenvalue.computedTanh := by
    linarith [hvalid.2.1, hvalid.2.2.1]
  have hdenominator : 0 <
      |certificate.metric.eigenvalue.computedTanh| *
        certificate.idealTanhLower := by
    rw [abs_of_pos hcomputedTanh]
    exact mul_pos hcomputedTanh hvalid.2.1
  unfold eigenvalueError
  positivity

theorem sqrtError_nonneg
    (certificate : PositiveSoftAbsMetricErrorUpperCertificate)
    (hvalid : certificate.Valid) : 0 ≤ certificate.sqrtError := by
  have heigen := certificate.eigenvalueError_nonneg hvalid
  have hdenominator : 0 <
      certificate.computedSqrtLower + certificate.idealSqrtLower :=
    add_pos hvalid.2.2.2.1 hvalid.2.2.2.2.2.1
  have hsqrtLocal : 0 ≤ certificate.metric.sqrt.error := hvalid.1.2.1.2.1
  unfold sqrtError
  positivity

theorem metricEntry_eigenvalueError_le
    (certificate : PositiveSoftAbsMetricErrorUpperCertificate)
    (hvalid : certificate.Valid) :
    (certificate.metric.metricEntryCertificate hvalid.1).eigenvalueError ≤
      (certificate.eigenvalueError : ℝ) := by
  have htanhLower := certificate.metric.eigenvalue.le_idealTanh hvalid.1.1
    hvalid.2.2.1
  have htanhPositive : 0 < Real.tanh
      ((certificate.metric.eigenvalue.smoothing : ℝ) *
        certificate.metric.eigenvalue.hessian) :=
    Mcmc.Relativistic.real_tanh_pos (mul_pos
      (by exact_mod_cast hvalid.1.1.1)
      (by exact_mod_cast hvalid.1.1.2.1))
  have hcomputedTanh : 0 <
      (certificate.metric.eigenvalue.computedTanh : ℝ) := by
    have hlower : (0 : ℝ) < certificate.idealTanhLower := by
      exact_mod_cast hvalid.2.1
    have hle : (certificate.idealTanhLower : ℝ) ≤
        certificate.metric.eigenvalue.computedTanh -
          (certificate.metric.eigenvalue.tanhError +
            certificate.metric.eigenvalue.argumentError) := by
      exact_mod_cast hvalid.2.2.1
    have harg : (0 : ℝ) ≤ certificate.metric.eigenvalue.argumentError := by
      exact_mod_cast hvalid.1.1.2.2.1
    have htanh : (0 : ℝ) ≤ certificate.metric.eigenvalue.tanhError := by
      exact_mod_cast hvalid.1.1.2.2.2.2.1.2.1
    linarith
  rcases hvalid.1 with ⟨heigen, hsqrt, hfactor, hlog⟩
  unfold PositiveSoftAbsMetricRationalCertificate.metricEntryCertificate
  dsimp only
  norm_num [eigenvalueError]
  rw [abs_of_pos hcomputedTanh, abs_of_pos htanhPositive]
  have herror : 0 ≤
      (certificate.metric.eigenvalue.tanhError : ℝ) +
        certificate.metric.eigenvalue.argumentError := by
    have hargument : (0 : ℝ) ≤
        certificate.metric.eigenvalue.argumentError := by
      exact_mod_cast heigen.2.2.1
    have htanh : (0 : ℝ) ≤ certificate.metric.eigenvalue.tanhError := by
      exact_mod_cast heigen.2.2.2.2.1.2.1
    linarith
  have hlowerPositive : (0 : ℝ) < certificate.idealTanhLower := by
    exact_mod_cast hvalid.2.1
  gcongr

theorem idealEigenvalue_lower
    (certificate : PositiveSoftAbsMetricErrorUpperCertificate)
    (hvalid : certificate.Valid) :
    (certificate.idealSqrtLower : ℝ) ^ 2 ≤
      Mcmc.Relativistic.softAbs
        (certificate.metric.eigenvalue.smoothing : ℝ)
        certificate.metric.eigenvalue.hessian := by
  let entry := certificate.metric.metricEntryCertificate hvalid.1
  have heigen := entry.eigenvalue_bound.mono
    (certificate.metricEntry_eigenvalueError_le hvalid)
  have hlower : (certificate.idealSqrtLower : ℝ) ^ 2 ≤
      (certificate.metric.eigenvalue.computedEigenvalue : ℝ) -
        certificate.eigenvalueError := by
    exact_mod_cast hvalid.2.2.2.2.2.2
  have habs := (abs_le.mp heigen).2
  dsimp only [entry] at habs
  simp only [PositiveSoftAbsMetricRationalCertificate.metricEntryCertificate_computedEigenvalue]
    at habs
  linarith

theorem le_idealSqrt
    (certificate : PositiveSoftAbsMetricErrorUpperCertificate)
    (hvalid : certificate.Valid) :
    (certificate.idealSqrtLower : ℝ) ≤ Real.sqrt
      (Mcmc.Relativistic.softAbs
        (certificate.metric.eigenvalue.smoothing : ℝ)
        certificate.metric.eigenvalue.hessian) := by
  exact (Real.le_sqrt
    (by exact_mod_cast (le_of_lt hvalid.2.2.2.2.2.1))
    (le_of_lt (Mcmc.Relativistic.softAbs_pos _
      (by exact_mod_cast hvalid.1.1.1) _))).2
    (certificate.idealEigenvalue_lower hvalid)

theorem computedSqrtLower_le
    (certificate : PositiveSoftAbsMetricErrorUpperCertificate)
    (hvalid : certificate.Valid) :
    (certificate.computedSqrtLower : ℝ) ≤ Real.sqrt
      (certificate.metric.eigenvalue.computedEigenvalue : ℝ) := by
  have hsqrt : Approximates (certificate.metric.sqrt.computed : ℝ)
      (Real.sqrt (certificate.metric.eigenvalue.computedEigenvalue : ℝ))
      certificate.metric.sqrt.error := by
    simpa [certificate.metric.sqrtInput] using
      certificate.metric.sqrt.approximates hvalid.1.2.1
  have hlower := (abs_le.mp hsqrt).2
  have hsubmitted : (certificate.computedSqrtLower : ℝ) ≤
      certificate.metric.sqrt.computed - certificate.metric.sqrt.error := by
    exact_mod_cast hvalid.2.2.2.2.1
  linarith

theorem metricEntry_sqrtError_le
    (certificate : PositiveSoftAbsMetricErrorUpperCertificate)
    (hvalid : certificate.Valid) :
    (certificate.metric.metricEntryCertificate hvalid.1).sqrtError ≤
      (certificate.sqrtError : ℝ) := by
  let entry := certificate.metric.metricEntryCertificate hvalid.1
  have heigenError := certificate.metricEntry_eigenvalueError_le hvalid
  have heigenErrorNonneg : 0 ≤ entry.eigenvalueError :=
    entry.eigenvalue_bound.nonneg
  have hupperNonneg : (0 : ℝ) ≤ certificate.eigenvalueError := by
    exact_mod_cast certificate.eigenvalueError_nonneg hvalid
  have hdenominator :
      (certificate.computedSqrtLower : ℝ) + certificate.idealSqrtLower ≤
        Real.sqrt (certificate.metric.eigenvalue.computedEigenvalue : ℝ) +
          Real.sqrt (Mcmc.Relativistic.softAbs
            (certificate.metric.eigenvalue.smoothing : ℝ)
            certificate.metric.eigenvalue.hessian) :=
    add_le_add (certificate.computedSqrtLower_le hvalid)
      (certificate.le_idealSqrt hvalid)
  have hdenominatorPositive : 0 <
      (certificate.computedSqrtLower : ℝ) + certificate.idealSqrtLower := by
    exact add_pos (by exact_mod_cast hvalid.2.2.2.1)
      (by exact_mod_cast hvalid.2.2.2.2.2.1)
  have hquotient := div_le_div₀ hupperNonneg heigenError
    hdenominatorPositive hdenominator
  dsimp only [entry] at heigenErrorNonneg hquotient ⊢
  rw [PositiveSoftAbsMetricRationalCertificate.metricEntryCertificate_sqrtError]
  norm_num [sqrtError]
  exact hquotient

theorem metricEntry_factorError_le
    (certificate : PositiveSoftAbsMetricErrorUpperCertificate)
    (hvalid : certificate.Valid) :
    (certificate.metric.metricEntryCertificate hvalid.1).factorError ≤
      (certificate.factorError : ℝ) := by
  have hsqrtError := certificate.metricEntry_sqrtError_le hvalid
  have hupperNonneg : (0 : ℝ) ≤ certificate.sqrtError := by
    exact_mod_cast certificate.sqrtError_nonneg hvalid
  have hcomputedSqrt : 0 < (certificate.metric.sqrt.computed : ℝ) := by
    have hlower : (0 : ℝ) < certificate.computedSqrtLower := by
      exact_mod_cast hvalid.2.2.2.1
    have hsubmitted : (certificate.computedSqrtLower : ℝ) ≤
        certificate.metric.sqrt.computed - certificate.metric.sqrt.error := by
      exact_mod_cast hvalid.2.2.2.2.1
    have herror : (0 : ℝ) ≤ certificate.metric.sqrt.error := by
      exact_mod_cast hvalid.1.2.1.2.1
    linarith
  have hidealSqrtPositive : 0 < Real.sqrt
      (Mcmc.Relativistic.softAbs
        (certificate.metric.eigenvalue.smoothing : ℝ)
        certificate.metric.eigenvalue.hessian) := by
    exact Real.sqrt_pos.2 (Mcmc.Relativistic.softAbs_pos _
      (by exact_mod_cast hvalid.1.1.1) _)
  have hdenominator :
      |(certificate.metric.sqrt.computed : ℝ)| * certificate.idealSqrtLower ≤
        |(certificate.metric.sqrt.computed : ℝ)| *
          |Real.sqrt (Mcmc.Relativistic.softAbs
            (certificate.metric.eigenvalue.smoothing : ℝ)
            certificate.metric.eigenvalue.hessian)| := by
    gcongr
    simpa [abs_of_pos hidealSqrtPositive] using certificate.le_idealSqrt hvalid
  have hdenominatorPositive : 0 <
      |(certificate.metric.sqrt.computed : ℝ)| * certificate.idealSqrtLower := by
    exact mul_pos (abs_pos.2 hcomputedSqrt.ne')
      (by exact_mod_cast hvalid.2.2.2.2.2.1)
  have hquotient := div_le_div₀ hupperNonneg hsqrtError
    hdenominatorPositive hdenominator
  rw [PositiveSoftAbsMetricRationalCertificate.metricEntryCertificate_factorError]
  norm_num [factorError]
  simpa only [PositiveSoftAbsMetricRationalCertificate.metricEntryCertificate_sqrtError]
    using hquotient

theorem metricEntry_logDetError_le
    (certificate : PositiveSoftAbsMetricErrorUpperCertificate)
    (hvalid : certificate.Valid) :
    (certificate.metric.metricEntryCertificate hvalid.1).logDetError ≤
      (certificate.logDetError : ℝ) := by
  have heigenError := certificate.metricEntry_eigenvalueError_le hvalid
  have hupperNonneg : (0 : ℝ) ≤ certificate.eigenvalueError := by
    exact_mod_cast certificate.eigenvalueError_nonneg hvalid
  have hcomputedEigen : 0 <
      (certificate.metric.eigenvalue.computedEigenvalue : ℝ) := by
    exact_mod_cast hvalid.1.1.2.2.2.2.2.1
  have hlowerSqPositive : 0 < (certificate.idealSqrtLower : ℝ) ^ 2 := by
    exact sq_pos_of_pos (by exact_mod_cast hvalid.2.2.2.2.2.1)
  have hdenominator :
      min (certificate.metric.eigenvalue.computedEigenvalue : ℝ)
          ((certificate.idealSqrtLower : ℝ) ^ 2) ≤
        min (certificate.metric.eigenvalue.computedEigenvalue : ℝ)
          (Mcmc.Relativistic.softAbs
            (certificate.metric.eigenvalue.smoothing : ℝ)
            certificate.metric.eigenvalue.hessian) :=
    min_le_min le_rfl (certificate.idealEigenvalue_lower hvalid)
  have hdenominatorPositive : 0 <
      min (certificate.metric.eigenvalue.computedEigenvalue : ℝ)
        ((certificate.idealSqrtLower : ℝ) ^ 2) := by
    simp only [lt_min_iff]
    exact ⟨hcomputedEigen, hlowerSqPositive⟩
  have hquotient := div_le_div₀ hupperNonneg heigenError
    hdenominatorPositive hdenominator
  change (certificate.metric.metricEntryCertificate hvalid.1).logDetError ≤
    (certificate.logDetError : ℝ)
  rw [PositiveSoftAbsMetricRationalCertificate.metricEntryCertificate_logDetError]
  norm_num [logDetError, inv_mul_eq_div]
  exact hquotient

end PositiveSoftAbsMetricErrorUpperCertificate

/-- Compose guarded operation certificates into the metric-entry witness. -/
noncomputable def SoftAbsPrimitiveBackend.metricEntryCertificate
    (backend : SoftAbsPrimitiveBackend) {α computedHessian idealHessian hessianError : ℝ}
    (hα : 0 < α)
    (hhessian : Approximates computedHessian idealHessian hessianError)
    (heigenComputed : 0 < backend.softAbs α computedHessian)
    (hsqrtComputed : 0 < backend.sqrt (backend.softAbs α computedHessian)) :
    SoftAbsMetricEntryCertificate α idealHessian := by
  let idealEigenvalue := Mcmc.Relativistic.softAbs α idealHessian
  let computedEigenvalue := backend.softAbs α computedHessian
  let eigenvalueError := backend.softAbsError α computedHessian
    idealHessian hessianError
  have hidealEigenvalue : 0 < idealEigenvalue := softAbs_pos α hα idealHessian
  have heigen : Approximates computedEigenvalue idealEigenvalue eigenvalueError :=
    backend.softAbs_bound α computedHessian idealHessian hessianError hα hhessian
  let computedSqrt := backend.sqrt computedEigenvalue
  let sqrtError := backend.sqrtError computedEigenvalue idealEigenvalue eigenvalueError
  have hsqrt : Approximates computedSqrt (Real.sqrt idealEigenvalue) sqrtError :=
    backend.sqrt_bound computedEigenvalue idealEigenvalue eigenvalueError
      heigenComputed hidealEigenvalue heigen
  let computedFactor := backend.inv computedSqrt
  let factorError := backend.invError computedSqrt
    (Real.sqrt idealEigenvalue) sqrtError
  have hidealSqrt : Real.sqrt idealEigenvalue ≠ 0 :=
    (Real.sqrt_pos.2 hidealEigenvalue).ne'
  have hfactor : Approximates computedFactor (Real.sqrt idealEigenvalue)⁻¹
      factorError :=
    backend.inv_bound computedSqrt (Real.sqrt idealEigenvalue) sqrtError
      hsqrtComputed.ne' hidealSqrt hsqrt
  let computedLogDet := backend.log computedEigenvalue
  let logDetError := backend.logError computedEigenvalue idealEigenvalue eigenvalueError
  have hlog : Approximates computedLogDet (Real.log idealEigenvalue) logDetError :=
    backend.log_bound computedEigenvalue idealEigenvalue eigenvalueError
      heigenComputed hidealEigenvalue heigen
  exact {
    computedHessian := computedHessian
    computedEigenvalue := computedEigenvalue
    computedSqrt := computedSqrt
    computedFactor := computedFactor
    computedLogDet := computedLogDet
    hessianError := hessianError
    eigenvalueError := eigenvalueError
    sqrtError := sqrtError
    factorError := factorError
    logDetError := logDetError
    hessian_bound := hhessian
    eigenvalue_bound := heigen
    factor_bound := hfactor
    logDet_bound := hlog }

/-- End-to-end generated-target bridge for the scalar sinusoidal SoftAbs
client. The restricted backend evaluates the generated second derivative;
the metric backend then transports that Hessian bound through SoftAbs and its
derived positive-domain operations. -/
noncomputable def restrictedSinusoidalSoftAbsMetricEntryCertificate
    (targetBackend : RestrictedBackend)
    (metricBackend : SoftAbsPrimitiveBackend)
    {computedInput idealInput inputError : ℝ}
    (hinput : Approximates computedInput idealInput inputError)
    (heigenComputed : 0 < metricBackend.softAbs 1
      (restrictedSinusoidalPotentialArtifact.derivative.derivative.backendEval
        targetBackend computedInput))
    (hsqrtComputed : 0 < metricBackend.sqrt (metricBackend.softAbs 1
      (restrictedSinusoidalPotentialArtifact.derivative.derivative.backendEval
        targetBackend computedInput))) :
    SoftAbsMetricEntryCertificate 1 (1 + Real.sin idealInput) := by
  let hessianExpression :=
    restrictedSinusoidalPotentialArtifact.derivative.derivative
  have hhessian : Approximates
      (hessianExpression.backendEval targetBackend computedInput)
      (1 + Real.sin idealInput)
      (hessianExpression.accumulatedError targetBackend computedInput
        idealInput inputError) := by
    have h := hessianExpression.backendEval_approximates targetBackend hinput
    rw [restrictedSinusoidalPotentialArtifact_secondDerivative_eval] at h
    exact h
  exact metricBackend.metricEntryCertificate (α := 1)
    (computedHessian := hessianExpression.backendEval targetBackend computedInput)
    (idealHessian := 1 + Real.sin idealInput)
    (hessianError := hessianExpression.accumulatedError targetBackend
      computedInput idealInput inputError)
    (by norm_num) hhessian heigenComputed hsqrtComputed

/-- Generated-target bridge for the strongly convex quartic client. This form
starts from any certified restricted-expression backend evaluation. -/
noncomputable def restrictedQuarticSoftAbsMetricEntryCertificate
    (targetBackend : RestrictedBackend)
    (metricBackend : SoftAbsPrimitiveBackend)
    {computedInput idealInput inputError : ℝ}
    (hinput : Approximates computedInput idealInput inputError)
    (heigenComputed : 0 < metricBackend.softAbs 1
      (restrictedQuarticPotentialArtifact.derivative.derivative.backendEval
        targetBackend computedInput))
    (hsqrtComputed : 0 < metricBackend.sqrt (metricBackend.softAbs 1
      (restrictedQuarticPotentialArtifact.derivative.derivative.backendEval
        targetBackend computedInput))) :
    SoftAbsMetricEntryCertificate 1 (3 * idealInput ^ 2 + 1) := by
  let hessianExpression :=
    restrictedQuarticPotentialArtifact.derivative.derivative
  have hhessian : Approximates
      (hessianExpression.backendEval targetBackend computedInput)
      (3 * idealInput ^ 2 + 1)
      (hessianExpression.accumulatedError targetBackend computedInput
        idealInput inputError) := by
    have h := hessianExpression.backendEval_approximates targetBackend hinput
    rw [restrictedQuarticPotentialArtifact_secondDerivative_eval] at h
    exact h
  exact metricBackend.metricEntryCertificate (α := 1)
    (computedHessian := hessianExpression.backendEval targetBackend computedInput)
    (idealHessian := 3 * idealInput ^ 2 + 1)
    (hessianError := hessianExpression.accumulatedError targetBackend
      computedInput idealInput inputError)
    (by norm_num) hhessian heigenComputed hsqrtComputed

/-- A Lean-checked exact-rational quartic callback record feeds directly into
the guarded SoftAbs metric certificate. Only the subsequent SoftAbs, square
root, reciprocal, and logarithm backend premises remain. -/
noncomputable def RestrictedQuarticRationalCertificate.softAbsMetricEntryCertificate
    (certificate : RestrictedQuarticRationalCertificate)
    (hvalid : certificate.Valid)
    (metricBackend : SoftAbsPrimitiveBackend)
    (heigenComputed : 0 < metricBackend.softAbs 1
      (certificate.computedSecondDerivative : ℝ))
    (hsqrtComputed : 0 < metricBackend.sqrt (metricBackend.softAbs 1
      (certificate.computedSecondDerivative : ℝ))) :
    SoftAbsMetricEntryCertificate 1
      (3 * (certificate.input : ℝ) ^ 2 + 1) := by
  have hhessian : Approximates
      (certificate.computedSecondDerivative : ℝ)
      (3 * (certificate.input : ℝ) ^ 2 + 1)
      (certificate.secondDerivativeError : ℝ) := by
    simpa using certificate.secondDerivative_approximates hvalid
  exact metricBackend.metricEntryCertificate (α := 1)
    (computedHessian := (certificate.computedSecondDerivative : ℝ))
    (idealHessian := 3 * (certificate.input : ℝ) ^ 2 + 1)
    (hessianError := (certificate.secondDerivativeError : ℝ))
    (by norm_num) hhessian
    heigenComputed hsqrtComputed

/-- Coordinatewise guarded certificates for a finite diagonal SoftAbs metric.
The aggregate log determinant is the sum of the certified scalar entries. -/
structure SoftAbsDiagonalMetricCertificate (ι : Type*) [Fintype ι]
    (α : ℝ) (idealHessian : ι → ℝ) where
  entry : ∀ i, SoftAbsMetricEntryCertificate α (idealHessian i)

namespace SoftAbsDiagonalMetricCertificate

variable {ι : Type*} [Fintype ι] {α : ℝ} {idealHessian : ι → ℝ}

noncomputable def computedLogDet
    (certificate : SoftAbsDiagonalMetricCertificate ι α idealHessian) : ℝ :=
  ∑ i, (certificate.entry i).computedLogDet

noncomputable def idealLogDet
    (_certificate : SoftAbsDiagonalMetricCertificate ι α idealHessian) : ℝ :=
  ∑ i, Real.log (Mcmc.Relativistic.softAbs α (idealHessian i))

noncomputable def logDetError
    (certificate : SoftAbsDiagonalMetricCertificate ι α idealHessian) : ℝ :=
  ∑ i, (certificate.entry i).logDetError

/-- Scalar log-determinant errors compose into the diagonal metric's complete
log-determinant error bound. -/
theorem logDet_bound
    (certificate : SoftAbsDiagonalMetricCertificate ι α idealHessian) :
    Approximates certificate.computedLogDet certificate.idealLogDet
      certificate.logDetError := by
  classical
  unfold computedLogDet idealLogDet logDetError
  exact Approximates.sum Finset.univ
    (fun i => (certificate.entry i).computedLogDet)
    (fun i => Real.log (Mcmc.Relativistic.softAbs α (idealHessian i)))
    (fun i => (certificate.entry i).logDetError)
    (fun i _ => (certificate.entry i).logDet_bound)

end SoftAbsDiagonalMetricCertificate

section ScalarHamiltonian

/-- A certified diagonal factor entry transports a certified scalar momentum.
This is the first missing connection from metric evaluation to the kinetic
energy actually used by GR-HMC. -/
theorem SoftAbsMetricEntryCertificate.factorMomentum_bound
    {α idealHessian computedMomentum idealMomentum momentumError : ℝ}
    (certificate : SoftAbsMetricEntryCertificate α idealHessian)
    (hmomentum : Approximates computedMomentum idealMomentum momentumError) :
    Approximates
      (certificate.computedFactor * computedMomentum)
      ((Real.sqrt (Mcmc.Relativistic.softAbs α idealHessian))⁻¹ *
        idealMomentum)
      (certificate.factorError * |computedMomentum| +
        |(Real.sqrt
          (Mcmc.Relativistic.softAbs α idealHessian))⁻¹| * momentumError) :=
  certificate.factor_bound.mul hmomentum

/-- Squaring the transformed momentum preserves a fully explicit absolute
error bound. -/
theorem SoftAbsMetricEntryCertificate.transformedMomentumSq_bound
    {α idealHessian computedMomentum idealMomentum momentumError : ℝ}
    (certificate : SoftAbsMetricEntryCertificate α idealHessian)
    (hmomentum : Approximates computedMomentum idealMomentum momentumError) :
    let computed := certificate.computedFactor * computedMomentum
    let ideal := (Real.sqrt
      (Mcmc.Relativistic.softAbs α idealHessian))⁻¹ * idealMomentum
    let error := certificate.factorError * |computedMomentum| +
      |(Real.sqrt
        (Mcmc.Relativistic.softAbs α idealHessian))⁻¹| * momentumError
    Approximates (computed * computed) (ideal * ideal)
      (error * |computed| + |ideal| * error) := by
  dsimp only
  let h := certificate.factorMomentum_bound hmomentum
  exact h.mul h

/-- For unit rest mass and unit speed, the scalar relativistic radicand is
`1 + (A(q)p)²`.  A guarded backend square root therefore yields a certified
kinetic term. -/
theorem SoftAbsPrimitiveBackend.scalarUnitKinetic_bound
    (backend : SoftAbsPrimitiveBackend)
    {α idealHessian computedMomentum idealMomentum momentumError : ℝ}
    (certificate : SoftAbsMetricEntryCertificate α idealHessian)
    (hmomentum : Approximates computedMomentum idealMomentum momentumError)
    (hcomputedRadicand : 0 <
      (certificate.computedFactor * computedMomentum) ^ 2 + 1) :
    let computedTransformed := certificate.computedFactor * computedMomentum
    let idealTransformed := (Real.sqrt
      (Mcmc.Relativistic.softAbs α idealHessian))⁻¹ * idealMomentum
    let transformedError := certificate.factorError * |computedMomentum| +
      |(Real.sqrt
        (Mcmc.Relativistic.softAbs α idealHessian))⁻¹| * momentumError
    let radicandError := transformedError * |computedTransformed| +
      |idealTransformed| * transformedError
    Approximates
      (backend.sqrt (computedTransformed ^ 2 + 1))
      (Real.sqrt (idealTransformed ^ 2 + 1))
      (backend.sqrtError (computedTransformed ^ 2 + 1)
        (idealTransformed ^ 2 + 1) radicandError) := by
  dsimp only
  have hsquare := certificate.transformedMomentumSq_bound hmomentum
  simp only [pow_two]
  have hradicand : Approximates
      ((certificate.computedFactor * computedMomentum) *
          (certificate.computedFactor * computedMomentum) + 1)
      (((Real.sqrt (Mcmc.Relativistic.softAbs α idealHessian))⁻¹ *
          idealMomentum) *
        ((Real.sqrt (Mcmc.Relativistic.softAbs α idealHessian))⁻¹ *
          idealMomentum) + 1)
      ((certificate.factorError * |computedMomentum| +
          |(Real.sqrt
            (Mcmc.Relativistic.softAbs α idealHessian))⁻¹| * momentumError) *
          |certificate.computedFactor * computedMomentum| +
        |(Real.sqrt (Mcmc.Relativistic.softAbs α idealHessian))⁻¹ *
          idealMomentum| *
          (certificate.factorError * |computedMomentum| +
            |(Real.sqrt
              (Mcmc.Relativistic.softAbs α idealHessian))⁻¹| *
                momentumError)) := by
    simpa using hsquare.add (Approximates.refl 1)
  have hcomputed : 0 <
      (certificate.computedFactor * computedMomentum) *
          (certificate.computedFactor * computedMomentum) + 1 := by
    simpa [pow_two] using hcomputedRadicand
  have hideal : 0 <
      ((Real.sqrt (Mcmc.Relativistic.softAbs α idealHessian))⁻¹ *
          idealMomentum) *
        ((Real.sqrt (Mcmc.Relativistic.softAbs α idealHessian))⁻¹ *
          idealMomentum) + 1 := by
    nlinarith [sq_nonneg
      ((Real.sqrt (Mcmc.Relativistic.softAbs α idealHessian))⁻¹ *
        idealMomentum)]
  exact backend.sqrt_bound _ _ _ hcomputed hideal hradicand

/-- Compose potential, unit-parameter relativistic kinetic energy, and the
SoftAbs log-determinant contribution into the scalar GR Hamiltonian value.
The square-root approximation may come from
`SoftAbsPrimitiveBackend.scalarUnitKinetic_bound`. -/
theorem scalarUnitSoftAbsHamiltonian_bound
    {α idealHessian computedPotential idealPotential potentialError
      computedKinetic idealKinetic kineticError : ℝ}
    (certificate : SoftAbsMetricEntryCertificate α idealHessian)
    (hpotential : Approximates computedPotential idealPotential potentialError)
    (hkinetic : Approximates computedKinetic idealKinetic kineticError) :
    Approximates
      (computedPotential + computedKinetic +
        (1 / 2 : ℝ) * certificate.computedLogDet)
      (idealPotential + idealKinetic +
        (1 / 2 : ℝ) *
          Real.log (Mcmc.Relativistic.softAbs α idealHessian))
      (potentialError + kineticError +
        (0 * |certificate.computedLogDet| +
          |(1 / 2 : ℝ)| * certificate.logDetError)) := by
  exact (hpotential.add hkinetic).add
    ((Approximates.refl (1 / 2 : ℝ)).mul certificate.logDet_bound)

/-- Exact-rational witnesses linking a complete positive SoftAbs metric entry
to the scalar unit-parameter relativistic Hamiltonian evaluated at one
potential and momentum. The kinetic square root is checked at the observed
metric factor; Lean transports it to the ideal SoftAbs factor. -/
structure PositiveSoftAbsHamiltonianRationalCertificate where
  metric : PositiveSoftAbsMetricRationalCertificate
  potential : ℚ
  momentum : ℚ
  kinetic : SqrtRationalIntervalCertificate
  kineticInputError : ℚ
  computedEnergy : ℚ
  energyArithmeticError : ℚ
deriving DecidableEq, Repr

def PositiveSoftAbsHamiltonianRationalCertificate.Valid
    (certificate : PositiveSoftAbsHamiltonianRationalCertificate) : Prop :=
  certificate.metric.Valid ∧ certificate.kinetic.Valid ∧
    0 < certificate.kinetic.input ∧ 0 ≤ certificate.kineticInputError ∧
    |certificate.kinetic.input -
      ((certificate.metric.factor.computed * certificate.momentum) ^ 2 + 1)| ≤
        certificate.kineticInputError ∧
    0 ≤ certificate.energyArithmeticError ∧
    |certificate.computedEnergy -
      (certificate.potential + certificate.kinetic.computed +
        (1 / 2 : ℚ) * certificate.metric.logDet.computed)| ≤
      certificate.energyArithmeticError

instance (certificate : PositiveSoftAbsHamiltonianRationalCertificate) :
    Decidable certificate.Valid := by
  unfold PositiveSoftAbsHamiltonianRationalCertificate.Valid
  infer_instance

def PositiveSoftAbsHamiltonianRationalCertificate.check
    (certificate : PositiveSoftAbsHamiltonianRationalCertificate) : Bool :=
  decide certificate.Valid

/-- An accepted linked record proves a complete endpoint-Hamiltonian error
bound. The displayed `let` bindings expose every contribution used by later
trajectory-weight and stable-selection certificates. -/
theorem PositiveSoftAbsHamiltonianRationalCertificate.energy_approximates
    (certificate : PositiveSoftAbsHamiltonianRationalCertificate)
    (hvalid : certificate.Valid) :
    let entry := certificate.metric.metricEntryCertificate hvalid.1
    let idealFactor :=
      (Real.sqrt (Mcmc.Relativistic.softAbs
        (certificate.metric.eigenvalue.smoothing : ℝ)
        certificate.metric.eigenvalue.hessian))⁻¹
    let transformedError := entry.factorError * |(certificate.momentum : ℝ)|
    let computedTransformed :=
      entry.computedFactor * (certificate.momentum : ℝ)
    let idealTransformed := idealFactor * (certificate.momentum : ℝ)
    let radicandError := (certificate.kineticInputError : ℝ) +
      (transformedError * |computedTransformed| +
        |idealTransformed| * transformedError)
    let kineticError := (certificate.kinetic.error : ℝ) +
      radicandError /
        (Real.sqrt (certificate.kinetic.input : ℝ) +
          Real.sqrt (idealTransformed ^ 2 + 1))
    Approximates (certificate.computedEnergy : ℝ)
      ((certificate.potential : ℝ) +
        Real.sqrt (idealTransformed ^ 2 + 1) +
        (1 / 2 : ℝ) * Real.log (Mcmc.Relativistic.softAbs
          (certificate.metric.eigenvalue.smoothing : ℝ)
          certificate.metric.eigenvalue.hessian))
      ((certificate.energyArithmeticError : ℝ) +
        kineticError + (1 / 2 : ℝ) * entry.logDetError) := by
  dsimp only
  rcases hvalid with ⟨hmetric, hkinetic, hkineticInputPositive,
    hkineticInputError, hkineticInputBound, henergyError, henergyBound⟩
  let entry := certificate.metric.metricEntryCertificate hmetric
  let idealFactor :=
    (Real.sqrt (Mcmc.Relativistic.softAbs
      (certificate.metric.eigenvalue.smoothing : ℝ)
      certificate.metric.eigenvalue.hessian))⁻¹
  let transformedError := entry.factorError * |(certificate.momentum : ℝ)|
  let computedTransformed := entry.computedFactor * (certificate.momentum : ℝ)
  let idealTransformed := idealFactor * (certificate.momentum : ℝ)
  let radicandError := (certificate.kineticInputError : ℝ) +
    (transformedError * |computedTransformed| +
      |idealTransformed| * transformedError)
  let kineticError := (certificate.kinetic.error : ℝ) +
    radicandError /
      (Real.sqrt (certificate.kinetic.input : ℝ) +
        Real.sqrt (idealTransformed ^ 2 + 1))
  have hmomentum := Approximates.refl (certificate.momentum : ℝ)
  have hsquare := entry.transformedMomentumSq_bound hmomentum
  have hradicandTransport : Approximates
      (computedTransformed ^ 2 + 1) (idealTransformed ^ 2 + 1)
      (transformedError * |computedTransformed| +
        |idealTransformed| * transformedError) := by
    simpa [entry, idealFactor, transformedError, computedTransformed,
      idealTransformed, pow_two] using
      hsquare.add (Approximates.refl 1)
  have hradicandLocal : Approximates (certificate.kinetic.input : ℝ)
      (computedTransformed ^ 2 + 1) certificate.kineticInputError := by
    rw [Approximates]
    simp only [computedTransformed, entry,
      PositiveSoftAbsMetricRationalCertificate.metricEntryCertificate_computedFactor]
    exact_mod_cast hkineticInputBound
  have hradicand : Approximates (certificate.kinetic.input : ℝ)
      (idealTransformed ^ 2 + 1) radicandError := by
    simpa [radicandError] using hradicandLocal.trans hradicandTransport
  have hcomputedRadicand : 0 < (certificate.kinetic.input : ℝ) := by
    exact_mod_cast hkineticInputPositive
  have hidealRadicand : 0 < idealTransformed ^ 2 + 1 := by positivity
  have hkineticLocal : Approximates (certificate.kinetic.computed : ℝ)
      (Real.sqrt (certificate.kinetic.input : ℝ)) certificate.kinetic.error :=
    certificate.kinetic.approximates hkinetic
  have hkineticIdeal : Approximates (certificate.kinetic.computed : ℝ)
      (Real.sqrt (idealTransformed ^ 2 + 1)) kineticError := by
    simpa [kineticError]
      using sqrt_backend_approximates hkineticLocal hradicand
        hcomputedRadicand hidealRadicand
  have hhamiltonian := scalarUnitSoftAbsHamiltonian_bound entry
    (Approximates.refl (certificate.potential : ℝ)) hkineticIdeal
  have hlocal : Approximates (certificate.computedEnergy : ℝ)
      ((certificate.potential : ℝ) + certificate.kinetic.computed +
        (1 / 2 : ℝ) * entry.computedLogDet)
      certificate.energyArithmeticError := by
    rw [Approximates]
    simp only [entry,
      PositiveSoftAbsMetricRationalCertificate.metricEntryCertificate_computedLogDet]
    have hcast :
        (((certificate.potential + certificate.kinetic.computed +
          (1 / 2 : ℚ) * certificate.metric.logDet.computed : ℚ) : ℝ)) =
          (certificate.potential : ℝ) + certificate.kinetic.computed +
            (1 / 2 : ℝ) * certificate.metric.logDet.computed := by
      norm_num
    rw [← hcast]
    exact_mod_cast henergyBound
  change Approximates (certificate.computedEnergy : ℝ)
    ((certificate.potential : ℝ) + Real.sqrt (idealTransformed ^ 2 + 1) +
      (1 / 2 : ℝ) * Real.log (Mcmc.Relativistic.softAbs
        (certificate.metric.eigenvalue.smoothing : ℝ)
        certificate.metric.eigenvalue.hessian))
    ((certificate.energyArithmeticError : ℝ) + kineticError +
      (1 / 2 : ℝ) * entry.logDetError)
  convert hlocal.trans hhamiltonian using 1
  all_goals simp only [zero_add, zero_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  all_goals ring

/-- Named ideal endpoint energy exposed for finite-trajectory composition. -/
noncomputable def PositiveSoftAbsHamiltonianRationalCertificate.idealEnergy
    (certificate : PositiveSoftAbsHamiltonianRationalCertificate) : ℝ :=
  let idealFactor :=
    (Real.sqrt (Mcmc.Relativistic.softAbs
      (certificate.metric.eigenvalue.smoothing : ℝ)
      certificate.metric.eigenvalue.hessian))⁻¹
  let idealTransformed := idealFactor * (certificate.momentum : ℝ)
  (certificate.potential : ℝ) + Real.sqrt (idealTransformed ^ 2 + 1) +
    (1 / 2 : ℝ) * Real.log (Mcmc.Relativistic.softAbs
      (certificate.metric.eigenvalue.smoothing : ℝ)
      certificate.metric.eigenvalue.hessian)

/-- Complete endpoint error generated from the checked rational witnesses. -/
noncomputable def PositiveSoftAbsHamiltonianRationalCertificate.energyError
    (certificate : PositiveSoftAbsHamiltonianRationalCertificate)
    (hvalid : certificate.Valid) : ℝ :=
  let entry := certificate.metric.metricEntryCertificate hvalid.1
  let idealFactor :=
    (Real.sqrt (Mcmc.Relativistic.softAbs
      (certificate.metric.eigenvalue.smoothing : ℝ)
      certificate.metric.eigenvalue.hessian))⁻¹
  let transformedError := entry.factorError * |(certificate.momentum : ℝ)|
  let computedTransformed := entry.computedFactor * (certificate.momentum : ℝ)
  let idealTransformed := idealFactor * (certificate.momentum : ℝ)
  let radicandError := (certificate.kineticInputError : ℝ) +
    (transformedError * |computedTransformed| +
      |idealTransformed| * transformedError)
  let kineticError := (certificate.kinetic.error : ℝ) +
    radicandError /
      (Real.sqrt (certificate.kinetic.input : ℝ) +
        Real.sqrt (idealTransformed ^ 2 + 1))
  (certificate.energyArithmeticError : ℝ) + kineticError +
    (1 / 2 : ℝ) * entry.logDetError

/-- Fully rational upper bound for the exact endpoint error. The extra
denominator witnesses are checked against the primitive metric and kinetic
records, so no irrational conditioning term is serialized. -/
structure PositiveSoftAbsHamiltonianErrorUpperCertificate where
  endpoint : PositiveSoftAbsHamiltonianRationalCertificate
  idealTanhLower : ℚ
  computedSqrtLower : ℚ
  idealSqrtLower : ℚ
  kineticSqrtLower : ℚ
deriving DecidableEq, Repr

namespace PositiveSoftAbsHamiltonianErrorUpperCertificate

def metricUpper
    (certificate : PositiveSoftAbsHamiltonianErrorUpperCertificate) :
    PositiveSoftAbsMetricErrorUpperCertificate where
  metric := certificate.endpoint.metric
  idealTanhLower := certificate.idealTanhLower
  computedSqrtLower := certificate.computedSqrtLower
  idealSqrtLower := certificate.idealSqrtLower

def transformedError
    (certificate : PositiveSoftAbsHamiltonianErrorUpperCertificate) : ℚ :=
  certificate.metricUpper.factorError * |certificate.endpoint.momentum|

def computedTransformed
    (certificate : PositiveSoftAbsHamiltonianErrorUpperCertificate) : ℚ :=
  certificate.endpoint.metric.factor.computed * certificate.endpoint.momentum

def idealTransformedAbsUpper
    (certificate : PositiveSoftAbsHamiltonianErrorUpperCertificate) : ℚ :=
  (|certificate.endpoint.metric.factor.computed| +
    certificate.metricUpper.factorError) * |certificate.endpoint.momentum|

def radicandError
    (certificate : PositiveSoftAbsHamiltonianErrorUpperCertificate) : ℚ :=
  certificate.endpoint.kineticInputError +
    (certificate.transformedError * |certificate.computedTransformed| +
      certificate.idealTransformedAbsUpper * certificate.transformedError)

def kineticError
    (certificate : PositiveSoftAbsHamiltonianErrorUpperCertificate) : ℚ :=
  certificate.endpoint.kinetic.error + certificate.radicandError /
    (certificate.kineticSqrtLower + 1)

def energyError
    (certificate : PositiveSoftAbsHamiltonianErrorUpperCertificate) : ℚ :=
  certificate.endpoint.energyArithmeticError + certificate.kineticError +
    (1 / 2 : ℚ) * certificate.metricUpper.logDetError

def Valid
    (certificate : PositiveSoftAbsHamiltonianErrorUpperCertificate) : Prop :=
  certificate.endpoint.Valid ∧ certificate.metricUpper.Valid ∧
    0 < certificate.kineticSqrtLower ∧
    certificate.kineticSqrtLower ≤
      certificate.endpoint.kinetic.computed - certificate.endpoint.kinetic.error

instance (certificate : PositiveSoftAbsHamiltonianErrorUpperCertificate) :
    Decidable certificate.Valid := by
  unfold Valid
  infer_instance

def check
    (certificate : PositiveSoftAbsHamiltonianErrorUpperCertificate) : Bool :=
  decide certificate.Valid

theorem metric_factorError_le
    (certificate : PositiveSoftAbsHamiltonianErrorUpperCertificate)
    (hvalid : certificate.Valid) :
    (certificate.endpoint.metric.metricEntryCertificate hvalid.1.1).factorError ≤
      (certificate.metricUpper.factorError : ℝ) := by
  exact certificate.metricUpper.metricEntry_factorError_le hvalid.2.1

theorem metric_logDetError_le
    (certificate : PositiveSoftAbsHamiltonianErrorUpperCertificate)
    (hvalid : certificate.Valid) :
    (certificate.endpoint.metric.metricEntryCertificate hvalid.1.1).logDetError ≤
      (certificate.metricUpper.logDetError : ℝ) := by
  exact certificate.metricUpper.metricEntry_logDetError_le hvalid.2.1

theorem idealFactor_abs_le
    (certificate : PositiveSoftAbsHamiltonianErrorUpperCertificate)
    (hvalid : certificate.Valid) :
    |(Real.sqrt (Mcmc.Relativistic.softAbs
        (certificate.endpoint.metric.eigenvalue.smoothing : ℝ)
        certificate.endpoint.metric.eigenvalue.hessian))⁻¹| ≤
      |(certificate.endpoint.metric.factor.computed : ℝ)| +
        certificate.metricUpper.factorError := by
  let entry := certificate.endpoint.metric.metricEntryCertificate hvalid.1.1
  have hfactor := entry.factor_bound.mono (certificate.metric_factorError_le hvalid)
  have htriangle :
      |(Real.sqrt (Mcmc.Relativistic.softAbs
          (certificate.endpoint.metric.eigenvalue.smoothing : ℝ)
          certificate.endpoint.metric.eigenvalue.hessian))⁻¹| ≤
        |entry.computedFactor| +
          |(Real.sqrt (Mcmc.Relativistic.softAbs
            (certificate.endpoint.metric.eigenvalue.smoothing : ℝ)
            certificate.endpoint.metric.eigenvalue.hessian))⁻¹ -
              entry.computedFactor| := by
    calc
      _ = |entry.computedFactor +
          ((Real.sqrt (Mcmc.Relativistic.softAbs
            (certificate.endpoint.metric.eigenvalue.smoothing : ℝ)
            certificate.endpoint.metric.eigenvalue.hessian))⁻¹ -
              entry.computedFactor)| := by
        congr 1
        ring
      _ ≤ _ := abs_add_le _ _
  have herror :
      |(Real.sqrt (Mcmc.Relativistic.softAbs
          (certificate.endpoint.metric.eigenvalue.smoothing : ℝ)
          certificate.endpoint.metric.eigenvalue.hessian))⁻¹ -
            entry.computedFactor| ≤ certificate.metricUpper.factorError := by
    rw [abs_sub_comm]
    exact hfactor
  calc
    _ ≤ |entry.computedFactor| +
        |(Real.sqrt (Mcmc.Relativistic.softAbs
          (certificate.endpoint.metric.eigenvalue.smoothing : ℝ)
          certificate.endpoint.metric.eigenvalue.hessian))⁻¹ -
            entry.computedFactor| := htriangle
    _ ≤ |entry.computedFactor| + certificate.metricUpper.factorError :=
      add_le_add le_rfl herror
    _ = _ := by simp [entry]

theorem kineticSqrtLower_le
    (certificate : PositiveSoftAbsHamiltonianErrorUpperCertificate)
    (hvalid : certificate.Valid) :
    (certificate.kineticSqrtLower : ℝ) ≤
      Real.sqrt (certificate.endpoint.kinetic.input : ℝ) := by
  have hkinetic := certificate.endpoint.kinetic.approximates hvalid.1.2.1
  have hlower := (abs_le.mp hkinetic).2
  have hsubmitted : (certificate.kineticSqrtLower : ℝ) ≤
      certificate.endpoint.kinetic.computed - certificate.endpoint.kinetic.error := by
    exact_mod_cast hvalid.2.2.2
  linarith

theorem transformedError_le
    (certificate : PositiveSoftAbsHamiltonianErrorUpperCertificate)
    (hvalid : certificate.Valid) :
    (certificate.endpoint.metric.metricEntryCertificate hvalid.1.1).factorError *
        |(certificate.endpoint.momentum : ℝ)| ≤
      (certificate.transformedError : ℝ) := by
  have hcast : (certificate.transformedError : ℝ) =
      (certificate.metricUpper.factorError : ℝ) *
        |(certificate.endpoint.momentum : ℝ)| := by
    norm_num [transformedError]
  rw [hcast]
  exact mul_le_mul_of_nonneg_right (certificate.metric_factorError_le hvalid)
    (abs_nonneg _)

theorem idealTransformed_abs_le
    (certificate : PositiveSoftAbsHamiltonianErrorUpperCertificate)
    (hvalid : certificate.Valid) :
    |(Real.sqrt (Mcmc.Relativistic.softAbs
        (certificate.endpoint.metric.eigenvalue.smoothing : ℝ)
        certificate.endpoint.metric.eigenvalue.hessian))⁻¹ *
          (certificate.endpoint.momentum : ℝ)| ≤
      (certificate.idealTransformedAbsUpper : ℝ) := by
  have hcast : (certificate.idealTransformedAbsUpper : ℝ) =
      (|(certificate.endpoint.metric.factor.computed : ℝ)| +
        certificate.metricUpper.factorError) *
          |(certificate.endpoint.momentum : ℝ)| := by
    norm_num [idealTransformedAbsUpper]
  rw [abs_mul, hcast]
  exact mul_le_mul_of_nonneg_right
    (by simpa [abs_inv] using certificate.idealFactor_abs_le hvalid)
    (abs_nonneg _)

theorem radicandError_le
    (certificate : PositiveSoftAbsHamiltonianErrorUpperCertificate)
    (hvalid : certificate.Valid) :
    let entry := certificate.endpoint.metric.metricEntryCertificate hvalid.1.1
    let idealFactor := (Real.sqrt (Mcmc.Relativistic.softAbs
      (certificate.endpoint.metric.eigenvalue.smoothing : ℝ)
      certificate.endpoint.metric.eigenvalue.hessian))⁻¹
    let exactTransformedError := entry.factorError *
      |(certificate.endpoint.momentum : ℝ)|
    (certificate.endpoint.kineticInputError : ℝ) +
      (exactTransformedError *
          |entry.computedFactor * (certificate.endpoint.momentum : ℝ)| +
        |idealFactor * (certificate.endpoint.momentum : ℝ)| *
          exactTransformedError) ≤
      (certificate.radicandError : ℝ) := by
  dsimp only
  have htransformed := certificate.transformedError_le hvalid
  have hideal := certificate.idealTransformed_abs_le hvalid
  have htransformedNonneg : 0 ≤
      (certificate.endpoint.metric.metricEntryCertificate hvalid.1.1).factorError *
        |(certificate.endpoint.momentum : ℝ)| := by
    exact mul_nonneg
      (certificate.endpoint.metric.metricEntryCertificate hvalid.1.1).factor_bound.nonneg
      (abs_nonneg _)
  have hupperNonneg : (0 : ℝ) ≤ certificate.transformedError :=
    htransformedNonneg.trans htransformed
  have hcomputed :
      |(certificate.endpoint.metric.metricEntryCertificate hvalid.1.1).computedFactor *
          (certificate.endpoint.momentum : ℝ)| =
        |(certificate.computedTransformed : ℚ)| := by
    simp [computedTransformed]
  have hcast : (certificate.radicandError : ℝ) =
      (certificate.endpoint.kineticInputError : ℝ) +
        ((certificate.transformedError : ℝ) *
          |(certificate.computedTransformed : ℚ)| +
        (certificate.idealTransformedAbsUpper : ℝ) *
          certificate.transformedError) := by
    norm_num [radicandError]
  rw [hcast, hcomputed]
  have hidealUpperNonneg : (0 : ℝ) ≤ certificate.idealTransformedAbsUpper :=
    (abs_nonneg _).trans hideal
  have hfirst :
      (certificate.endpoint.metric.metricEntryCertificate hvalid.1.1).factorError *
          |(certificate.endpoint.momentum : ℝ)| *
          ((|certificate.computedTransformed| : ℚ) : ℝ) ≤
        (certificate.transformedError : ℝ) *
          ((|certificate.computedTransformed| : ℚ) : ℝ) :=
    mul_le_mul_of_nonneg_right htransformed (by positivity)
  have hsecond :=
    mul_le_mul hideal htransformed htransformedNonneg hidealUpperNonneg
  exact add_le_add le_rfl (add_le_add hfirst hsecond)

theorem energyError_le
    (certificate : PositiveSoftAbsHamiltonianErrorUpperCertificate)
    (hvalid : certificate.Valid) :
    certificate.endpoint.energyError hvalid.1 ≤
      (certificate.energyError : ℝ) := by
  let entry := certificate.endpoint.metric.metricEntryCertificate hvalid.1.1
  let idealFactor := (Real.sqrt (Mcmc.Relativistic.softAbs
    (certificate.endpoint.metric.eigenvalue.smoothing : ℝ)
    certificate.endpoint.metric.eigenvalue.hessian))⁻¹
  let exactTransformedError := entry.factorError *
    |(certificate.endpoint.momentum : ℝ)|
  let computedTransformed := entry.computedFactor *
    (certificate.endpoint.momentum : ℝ)
  let idealTransformed := idealFactor * (certificate.endpoint.momentum : ℝ)
  let exactRadicandError := (certificate.endpoint.kineticInputError : ℝ) +
    (exactTransformedError * |computedTransformed| +
      |idealTransformed| * exactTransformedError)
  have hradicand : exactRadicandError ≤ certificate.radicandError := by
    exact certificate.radicandError_le hvalid
  have hradicandNonneg : 0 ≤ exactRadicandError := by
    dsimp only [exactRadicandError, exactTransformedError]
    have hkineticInput : (0 : ℝ) ≤ certificate.endpoint.kineticInputError := by
      exact_mod_cast hvalid.1.2.2.2.1
    have hfactorError : 0 ≤ entry.factorError := entry.factor_bound.nonneg
    positivity
  have hradicandUpperNonneg : (0 : ℝ) ≤ certificate.radicandError :=
    hradicandNonneg.trans hradicand
  have hidealKineticLower : (1 : ℝ) ≤
      Real.sqrt (idealTransformed ^ 2 + 1) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith [sq_nonneg idealTransformed]
  have hdenominator :
      (certificate.kineticSqrtLower : ℝ) + 1 ≤
        Real.sqrt (certificate.endpoint.kinetic.input : ℝ) +
          Real.sqrt (idealTransformed ^ 2 + 1) :=
    add_le_add (certificate.kineticSqrtLower_le hvalid) hidealKineticLower
  have hdenominatorPositive : 0 <
      (certificate.kineticSqrtLower : ℝ) + 1 := by
    have : (0 : ℝ) < certificate.kineticSqrtLower := by
      exact_mod_cast hvalid.2.2.1
    linarith
  have hkineticTransport := div_le_div₀ hradicandUpperNonneg hradicand
    hdenominatorPositive hdenominator
  have hlog := certificate.metric_logDetError_le hvalid
  dsimp only [exactRadicandError, exactTransformedError, computedTransformed,
    idealTransformed, idealFactor, entry] at hkineticTransport
  have hcast : (certificate.energyError : ℝ) =
      (certificate.endpoint.energyArithmeticError : ℝ) +
        ((certificate.endpoint.kinetic.error : ℝ) +
          (certificate.radicandError : ℝ) /
            (certificate.kineticSqrtLower + 1)) +
        (1 / 2 : ℝ) * certificate.metricUpper.logDetError := by
    norm_num [energyError, kineticError]
  rw [hcast]
  unfold PositiveSoftAbsHamiltonianRationalCertificate.energyError
  dsimp only
  exact add_le_add
    (add_le_add le_rfl (add_le_add le_rfl hkineticTransport))
    (mul_le_mul_of_nonneg_left hlog (by norm_num))

/-- The fully rational radius is a valid endpoint approximation budget. -/
theorem energy_approximates
    (certificate : PositiveSoftAbsHamiltonianErrorUpperCertificate)
    (hvalid : certificate.Valid) :
    Approximates (certificate.endpoint.computedEnergy : ℝ)
      certificate.endpoint.idealEnergy certificate.energyError :=
  by
    apply (certificate.endpoint.energy_approximates hvalid.1).mono
    exact certificate.energyError_le hvalid

end PositiveSoftAbsHamiltonianErrorUpperCertificate

/-- Rational transport from an endpoint evaluated at a rounded solver state
to the corresponding exact implicit state. The Lipschitz constant and solver
distance are explicit checked inputs; target-specific clients must prove the
Lipschitz and region premises. -/
structure PositiveSoftAbsEndpointStateTransportCertificate where
  endpoint : PositiveSoftAbsHamiltonianErrorUpperCertificate
  solverStateError : ℚ
  energyLipschitz : ℚ
  totalEnergyError : ℚ
deriving DecidableEq, Repr

namespace PositiveSoftAbsEndpointStateTransportCertificate

def Valid (certificate : PositiveSoftAbsEndpointStateTransportCertificate) : Prop :=
  certificate.endpoint.Valid ∧
    0 ≤ certificate.solverStateError ∧
    0 ≤ certificate.energyLipschitz ∧
    certificate.totalEnergyError = certificate.endpoint.energyError +
      certificate.energyLipschitz * certificate.solverStateError

instance (certificate : PositiveSoftAbsEndpointStateTransportCertificate) :
    Decidable certificate.Valid := by
  unfold Valid
  infer_instance

def check (certificate : PositiveSoftAbsEndpointStateTransportCertificate) : Bool :=
  decide certificate.Valid

@[simp] theorem check_eq_true_iff
    (certificate : PositiveSoftAbsEndpointStateTransportCertificate) :
    certificate.check = true ↔ certificate.Valid := by
  simp [check]

/-- The transported rational budget covers both endpoint evaluation and the
movement from the rounded solver state to its exact implicit counterpart. -/
theorem energy_approximates_exactState
    {α : Type*} [PseudoMetricSpace α]
    (certificate : PositiveSoftAbsEndpointStateTransportCertificate)
    (hvalid : certificate.Valid) (energy : α → ℝ) (region : Set α)
    (computedState exactState : α)
    (hcomputed : computedState ∈ region) (hexact : exactState ∈ region)
    (hlip : LipschitzOnWith
      ⟨(certificate.energyLipschitz : ℝ), by exact_mod_cast hvalid.2.2.1⟩
      energy region)
    (hstate : dist computedState exactState ≤
      (certificate.solverStateError : ℝ))
    (henergy : certificate.endpoint.endpoint.idealEnergy =
      energy computedState) :
    Approximates (certificate.endpoint.endpoint.computedEnergy : ℝ)
      (energy exactState) certificate.totalEnergyError := by
  have hevaluation := certificate.endpoint.energy_approximates hvalid.1
  rw [henergy] at hevaluation
  unfold Approximates at hevaluation ⊢
  have htransport := hlip.dist_le_mul computedState hcomputed exactState hexact
  rw [Real.dist_eq] at htransport
  calc
    |(certificate.endpoint.endpoint.computedEnergy : ℝ) - energy exactState| ≤
        |(certificate.endpoint.endpoint.computedEnergy : ℝ) -
          energy computedState| + |energy computedState - energy exactState| := by
      rw [show (certificate.endpoint.endpoint.computedEnergy : ℝ) -
          energy exactState =
          (certificate.endpoint.endpoint.computedEnergy - energy computedState) +
            (energy computedState - energy exactState) by ring]
      exact abs_add_le _ _
    _ ≤ (certificate.endpoint.energyError : ℝ) +
        certificate.energyLipschitz * dist computedState exactState :=
      add_le_add hevaluation htransport
    _ ≤ (certificate.endpoint.energyError : ℝ) +
        certificate.energyLipschitz * certificate.solverStateError := by
      gcongr
      exact_mod_cast hvalid.2.2.1
    _ = (certificate.totalEnergyError : ℝ) := by
      exact_mod_cast hvalid.2.2.2.symm

/-- End-to-end scalar composition from a rounded fixed-point update to the
SoftAbs energy at the exact contraction-selected implicit solution. -/
theorem energy_approximates_fixedPoint
    (certificate : PositiveSoftAbsEndpointStateTransportCertificate)
    (hvalid : certificate.Valid)
    (residual : RoundedContractionResidualRationalCertificate)
    (hresidual : residual.Valid)
    (contraction : AposterioriContractionRationalCertificate)
    (hcontraction : contraction.Valid)
    (f energy : ℝ → ℝ) (region : Set ℝ) (K : NNReal)
    (hcontract : ContractingWith K f)
    (hrate : (K : ℝ) = (contraction.rate : ℝ))
    (hresidualLink : contraction.residualUpper = residual.residualUpper)
    (hstateLink : certificate.solverStateError = contraction.distanceUpper)
    (hupdate : |(residual.computedUpdate : ℝ) - f residual.iterate| ≤
      (residual.updateError : ℝ))
    (hcomputed : (residual.iterate : ℝ) ∈ region)
    (hexact : hcontract.fixedPoint f ∈ region)
    (hlip : LipschitzOnWith
      ⟨(certificate.energyLipschitz : ℝ), by exact_mod_cast hvalid.2.2.1⟩
      energy region)
    (henergy : certificate.endpoint.endpoint.idealEnergy =
      energy residual.iterate) :
    Approximates (certificate.endpoint.endpoint.computedEnergy : ℝ)
      (energy (hcontract.fixedPoint f)) certificate.totalEnergyError := by
  apply certificate.energy_approximates_exactState hvalid energy region
    residual.iterate (hcontract.fixedPoint f) hcomputed hexact hlip
  · rw [hstateLink]
    exact roundedContraction_dist_fixedPoint_le residual hresidual contraction
      hcontraction f K hcontract hrate hresidualLink hupdate
  · exact henergy

end PositiveSoftAbsEndpointStateTransportCertificate

theorem PositiveSoftAbsHamiltonianRationalCertificate.energy_approximates_named
    (certificate : PositiveSoftAbsHamiltonianRationalCertificate)
    (hvalid : certificate.Valid) :
    Approximates (certificate.computedEnergy : ℝ) certificate.idealEnergy
      (certificate.energyError hvalid) := by
  simpa [PositiveSoftAbsHamiltonianRationalCertificate.idealEnergy,
    PositiveSoftAbsHamiltonianRationalCertificate.energyError] using
    certificate.energy_approximates hvalid

/-- A finite family of checked endpoint energies with one conservative common
budget. This is exactly the input shape required by stabilized multinomial
trajectory selection. -/
structure PositiveSoftAbsHamiltonianTrajectoryCertificate (n : ℕ) where
  endpoint : Fin n → PositiveSoftAbsHamiltonianRationalCertificate
  valid : ∀ i, (endpoint i).Valid
  commonError : ℝ
  commonError_nonneg : 0 ≤ commonError
  endpointError_le : ∀ i, (endpoint i).energyError (valid i) ≤ commonError

namespace PositiveSoftAbsHamiltonianTrajectoryCertificate

variable {n : ℕ}

/-- The least convenient canonical common budget: the maximum of the complete
endpoint errors. Nonemptiness is exactly what makes this finite maximum
available. -/
noncomputable def commonEnergyError [Nonempty (Fin n)]
    (endpoint : Fin n → PositiveSoftAbsHamiltonianRationalCertificate)
    (valid : ∀ i, (endpoint i).Valid) : ℝ :=
  finiteMaximum (fun i => (endpoint i).energyError (valid i))

theorem endpointEnergyError_le_common [Nonempty (Fin n)]
    (endpoint : Fin n → PositiveSoftAbsHamiltonianRationalCertificate)
    (valid : ∀ i, (endpoint i).Valid) (i : Fin n) :
    (endpoint i).energyError (valid i) ≤ commonEnergyError endpoint valid := by
  exact Finset.le_sup' (fun j => (endpoint j).energyError (valid j))
    (Finset.mem_univ i)

theorem commonEnergyError_nonneg [Nonempty (Fin n)]
    (endpoint : Fin n → PositiveSoftAbsHamiltonianRationalCertificate)
    (valid : ∀ i, (endpoint i).Valid) :
    0 ≤ commonEnergyError endpoint valid := by
  let i : Fin n := Classical.choice (inferInstance : Nonempty (Fin n))
  exact ((endpoint i).energy_approximates_named (valid i)).nonneg.trans
    (endpointEnergyError_le_common endpoint valid i)

/-- Any nonempty family of valid endpoint records therefore constructs the
uniform trajectory certificate without a hand-supplied analytic bound. -/
noncomputable def ofEndpoints [Nonempty (Fin n)]
    (endpoint : Fin n → PositiveSoftAbsHamiltonianRationalCertificate)
    (valid : ∀ i, (endpoint i).Valid) :
    PositiveSoftAbsHamiltonianTrajectoryCertificate n where
  endpoint := endpoint
  valid := valid
  commonError := commonEnergyError endpoint valid
  commonError_nonneg := commonEnergyError_nonneg endpoint valid
  endpointError_le := endpointEnergyError_le_common endpoint valid

/-- Construct a trajectory with a rational common error radius from endpoint
upper certificates. This avoids reintroducing the irrational canonical
maximum when a backend needs a serializable selection budget. -/
noncomputable def ofErrorUpperEndpoints
    (upper : Fin n → PositiveSoftAbsHamiltonianErrorUpperCertificate)
    (valid : ∀ i, (upper i).Valid) (commonError : ℚ)
    (hcommonNonneg : 0 ≤ commonError)
    (hle : ∀ i, (upper i).energyError ≤ commonError) :
    PositiveSoftAbsHamiltonianTrajectoryCertificate n where
  endpoint := fun i => (upper i).endpoint
  valid := fun i => (valid i).1
  commonError := commonError
  commonError_nonneg := by exact_mod_cast hcommonNonneg
  endpointError_le := fun i =>
    ((upper i).energyError_le (valid i)).trans (by exact_mod_cast hle i)

noncomputable def computedEnergy
    (certificate : PositiveSoftAbsHamiltonianTrajectoryCertificate n) :
    Fin n → ℝ := fun i => certificate.endpoint i |>.computedEnergy

noncomputable def idealEnergy
    (certificate : PositiveSoftAbsHamiltonianTrajectoryCertificate n) :
    Fin n → ℝ := fun i => (certificate.endpoint i).idealEnergy

theorem energy_approximates
    (certificate : PositiveSoftAbsHamiltonianTrajectoryCertificate n)
    (i : Fin n) :
    Approximates (certificate.computedEnergy i) (certificate.idealEnergy i)
      certificate.commonError :=
  ((certificate.endpoint i).energy_approximates_named (certificate.valid i)).mono
    (certificate.endpointError_le i)

/-- Feed all certified SoftAbs endpoint energies directly into the existing
maximum-stabilized multinomial boundary and draw certificate. -/
noncomputable def selectionCertificate [Nonempty (Fin n)]
    (certificate : PositiveSoftAbsHamiltonianTrajectoryCertificate n)
    (computedWeight : Fin n → ℝ)
    (computedDraw computedUnit idealUnit : ℝ)
    (expError multiplicationError unitError : ℝ)
    (hexpNonneg : 0 ≤ expError)
    (hexp : ∀ i, Approximates (computedWeight i)
      (stabilizedBoltzmannWeight certificate.computedEnergy i) expError)
    (hmul : Approximates computedDraw
      (computedUnit * totalWeight computedWeight) multiplicationError)
    (hunit : Approximates computedUnit idealUnit unitError) :
    MultinomialSelectionCertificate :=
  stabilizedMultinomialSelectionCertificate certificate.computedEnergy
    certificate.idealEnergy computedWeight computedDraw computedUnit idealUnit
    certificate.commonError expError multiplicationError unitError
    certificate.commonError_nonneg hexpNonneg certificate.energy_approximates
    hexp hmul hunit

/-- Direct constructor from a nonempty checked endpoint family to the
stabilized selection certificate. The common energy budget is inferred as the
finite maximum; only backend exponential, multiplication, and RNG premises
remain client inputs. -/
noncomputable def selectionCertificateOfEndpoints [Nonempty (Fin n)]
    (endpoint : Fin n → PositiveSoftAbsHamiltonianRationalCertificate)
    (valid : ∀ i, (endpoint i).Valid)
    (computedWeight : Fin n → ℝ)
    (computedDraw computedUnit idealUnit : ℝ)
    (expError multiplicationError unitError : ℝ)
    (hexpNonneg : 0 ≤ expError)
    (hexp : ∀ i, Approximates (computedWeight i)
      (stabilizedBoltzmannWeight (ofEndpoints endpoint valid).computedEnergy i)
      expError)
    (hmul : Approximates computedDraw
      (computedUnit * totalWeight computedWeight) multiplicationError)
    (hunit : Approximates computedUnit idealUnit unitError) :
    MultinomialSelectionCertificate :=
  (ofEndpoints endpoint valid).selectionCertificate computedWeight
    computedDraw computedUnit idealUnit expError multiplicationError unitError
    hexpNonneg hexp hmul hunit

/-- Exact-real specialization of the complete endpoint-to-selection chain.
This establishes that no mathematical composition is missing: nonzero
runtime budgets enter only when replacing exact `exp`, summation,
multiplication, or the uniform draw by a concrete backend. -/
noncomputable def exactSelectionCertificateOfEndpoints [Nonempty (Fin n)]
    (endpoint : Fin n → PositiveSoftAbsHamiltonianRationalCertificate)
    (valid : ∀ i, (endpoint i).Valid) (unit : ℝ) :
    MultinomialSelectionCertificate := by
  let trajectory := ofEndpoints endpoint valid
  let weight := stabilizedBoltzmannWeight trajectory.computedEnergy
  let draw := unit * totalWeight weight
  exact trajectory.selectionCertificate weight draw unit unit 0 0 0
    (by norm_num) (fun _ => Approximates.refl _)
    (Approximates.refl _) (Approximates.refl _)

end PositiveSoftAbsHamiltonianTrajectoryCertificate

/-- A finite SoftAbs energy trajectory together with one checked, rounded
maximum-stabilized exponential at every endpoint. -/
structure PositiveSoftAbsStabilizedWeightTrajectoryCertificate (n : ℕ)
    [Nonempty (Fin n)] where
  energy : PositiveSoftAbsHamiltonianTrajectoryCertificate n
  weight : Fin n → ExpNonpositiveTransportRationalCertificate
  weightValid : ∀ i, (weight i).Valid
  idealInput_eq : ∀ i, ((weight i).idealInput : ℝ) =
    -energy.computedEnergy i -
      finiteMaximum (fun j => -energy.computedEnergy j)

namespace PositiveSoftAbsStabilizedWeightTrajectoryCertificate

variable {n : ℕ} [Nonempty (Fin n)]

noncomputable def computedWeight
    (certificate : PositiveSoftAbsStabilizedWeightTrajectoryCertificate n) :
    Fin n → ℝ := fun i => (certificate.weight i).localCertificate.computed

noncomputable def endpointWeightError
    (certificate : PositiveSoftAbsStabilizedWeightTrajectoryCertificate n)
    (i : Fin n) : ℝ :=
  ((certificate.weight i).localCertificate.error : ℝ) +
    (certificate.weight i).inputError

noncomputable def commonWeightError
    (certificate : PositiveSoftAbsStabilizedWeightTrajectoryCertificate n) : ℝ :=
  finiteMaximum certificate.endpointWeightError

theorem endpointWeightError_le_common
    (certificate : PositiveSoftAbsStabilizedWeightTrajectoryCertificate n)
    (i : Fin n) :
    certificate.endpointWeightError i ≤ certificate.commonWeightError := by
  exact Finset.le_sup' certificate.endpointWeightError (Finset.mem_univ i)

theorem commonWeightError_nonneg
    (certificate : PositiveSoftAbsStabilizedWeightTrajectoryCertificate n) :
    0 ≤ certificate.commonWeightError := by
  let i : Fin n := Classical.choice (inferInstance : Nonempty (Fin n))
  exact ((certificate.weight i).approximates
    (certificate.weightValid i)).nonneg.trans
      (certificate.endpointWeightError_le_common i)

/-- Every checked runtime exponential approximates the exact stabilized
weight formed from the already computed endpoint energies, under one
automatically inferred common budget. -/
theorem weight_approximates
    (certificate : PositiveSoftAbsStabilizedWeightTrajectoryCertificate n)
    (i : Fin n) :
    Approximates (certificate.computedWeight i)
      (stabilizedBoltzmannWeight certificate.energy.computedEnergy i)
      certificate.commonWeightError := by
  apply ((certificate.weight i).stabilizedBoltzmannWeight_approximates
    certificate.energy.computedEnergy i (certificate.weightValid i)
    (certificate.idealInput_eq i)).mono
  exact certificate.endpointWeightError_le_common i

/-- Endpoint and exponential certificates now feed multinomial selection
without a separate libm premise. Only the final scaled-draw multiplication and
uniform-source approximation remain backend inputs. -/
noncomputable def selectionCertificate
    (certificate : PositiveSoftAbsStabilizedWeightTrajectoryCertificate n)
    (computedDraw computedUnit idealUnit : ℝ)
    (multiplicationError unitError : ℝ)
    (hmul : Approximates computedDraw
      (computedUnit * totalWeight certificate.computedWeight)
      multiplicationError)
    (hunit : Approximates computedUnit idealUnit unitError) :
    MultinomialSelectionCertificate :=
  certificate.energy.selectionCertificate certificate.computedWeight
    computedDraw computedUnit idealUnit certificate.commonWeightError
    multiplicationError unitError certificate.commonWeightError_nonneg
    certificate.weight_approximates hmul hunit

/-- Arithmetic-aware endpoint-to-selection chain using the actual rounded
prefix sums and final total produced by the runtime. -/
noncomputable def selectionCertificateWithArithmetic
    (certificate : PositiveSoftAbsStabilizedWeightTrajectoryCertificate n)
    (arithmetic : MultinomialCumulativeArithmeticCertificate
      certificate.computedWeight)
    (computedDraw computedUnit idealUnit : ℝ)
    (multiplicationError unitError : ℝ)
    (hmul : Approximates computedDraw
      (computedUnit * arithmetic.computedTotal) multiplicationError)
    (hunit : Approximates computedUnit idealUnit unitError) :
    MultinomialSelectionCertificate :=
  stabilizedMultinomialSelectionCertificateWithArithmetic
    certificate.energy.computedEnergy certificate.energy.idealEnergy
    certificate.computedWeight arithmetic computedDraw computedUnit idealUnit
    certificate.energy.commonError certificate.commonWeightError
    multiplicationError unitError certificate.energy.commonError_nonneg
    certificate.commonWeightError_nonneg certificate.energy.energy_approximates
    certificate.weight_approximates hmul hunit

end PositiveSoftAbsStabilizedWeightTrajectoryCertificate

end ScalarHamiltonian

end Mcmc.Executable.Continuous
