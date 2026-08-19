import Mcmc.Executable.Continuous.RestrictedCertificate
import Mathlib.Tactic

/-!
# Exact-dyadic Gaussian leapfrog certificates

Every finite IEEE binary floating-point value denotes a rational number.  This
module checks a restricted but assumption-free platform boundary: a foreign
runtime serializes the exact rationals observed during one unit-mass Gaussian
leapfrog step, and Lean checks the three kick--drift--kick equations exactly.
No transcendental function, approximate decimal parsing, or floating-point
rounding model is used by the checker.
-/

namespace Mcmc.Executable.Continuous

/-- Exact-rational execution record for one scalar Gaussian leapfrog step. -/
structure GaussianDyadicLeapfrogStepCertificate where
  stepSize : ℚ
  position : ℚ
  momentum : ℚ
  computedHalfMomentum : ℚ
  computedNextPosition : ℚ
  computedNextMomentum : ℚ
deriving DecidableEq, Repr

/-- The three exact equations of velocity Verlet for the Gaussian potential
`U(q) = q²/2`, whose gradient is `q`. -/
def GaussianDyadicLeapfrogStepCertificate.Valid
    (certificate : GaussianDyadicLeapfrogStepCertificate) : Prop :=
  certificate.computedHalfMomentum =
      certificate.momentum - certificate.stepSize / 2 * certificate.position ∧
    certificate.computedNextPosition =
      certificate.position +
        certificate.stepSize * certificate.computedHalfMomentum ∧
    certificate.computedNextMomentum =
      certificate.computedHalfMomentum - certificate.stepSize / 2 *
        certificate.computedNextPosition

/-- Executable Boolean checker used by the compiled cross-language oracle. -/
def GaussianDyadicLeapfrogStepCertificate.check
    (certificate : GaussianDyadicLeapfrogStepCertificate) : Bool :=
  certificate.computedHalfMomentum ==
      certificate.momentum - certificate.stepSize / 2 * certificate.position &&
    (certificate.computedNextPosition ==
        certificate.position +
          certificate.stepSize * certificate.computedHalfMomentum &&
      certificate.computedNextMomentum ==
        certificate.computedHalfMomentum - certificate.stepSize / 2 *
          certificate.computedNextPosition)

@[simp] theorem GaussianDyadicLeapfrogStepCertificate.check_eq_true_iff
    (certificate : GaussianDyadicLeapfrogStepCertificate) :
    certificate.check = true ↔ certificate.Valid := by
  simp [GaussianDyadicLeapfrogStepCertificate.check,
    GaussianDyadicLeapfrogStepCertificate.Valid]

/-- A successful exact-rational check gives the corresponding mathematical
real kick equation. -/
theorem GaussianDyadicLeapfrogStepCertificate.halfMomentum_real_eq
    (certificate : GaussianDyadicLeapfrogStepCertificate)
    (hvalid : certificate.Valid) :
    (certificate.computedHalfMomentum : ℝ) =
      certificate.momentum - certificate.stepSize / 2 * certificate.position := by
  exact_mod_cast hvalid.1

/-- A successful check gives the mathematical real drift equation. -/
theorem GaussianDyadicLeapfrogStepCertificate.nextPosition_real_eq
    (certificate : GaussianDyadicLeapfrogStepCertificate)
    (hvalid : certificate.Valid) :
    (certificate.computedNextPosition : ℝ) =
      certificate.position +
        certificate.stepSize * certificate.computedHalfMomentum := by
  exact_mod_cast hvalid.2.1

/-- A successful check gives the mathematical real final-kick equation. -/
theorem GaussianDyadicLeapfrogStepCertificate.nextMomentum_real_eq
    (certificate : GaussianDyadicLeapfrogStepCertificate)
    (hvalid : certificate.Valid) :
    (certificate.computedNextMomentum : ℝ) =
      certificate.computedHalfMomentum - certificate.stepSize / 2 *
        certificate.computedNextPosition := by
  exact_mod_cast hvalid.2.2

/-- Exact-rational residual record for a rounded Gaussian leapfrog step. Unlike
the exact-dyadic checker, this accepts rounding but requires the foreign runtime
to serialize each actual absolute residual exactly. -/
structure GaussianRoundedLeapfrogStepCertificate extends
    GaussianDyadicLeapfrogStepCertificate where
  halfMomentumError : ℚ
  nextPositionError : ℚ
  nextMomentumError : ℚ
deriving DecidableEq, Repr

def GaussianRoundedLeapfrogStepCertificate.Valid
    (certificate : GaussianRoundedLeapfrogStepCertificate) : Prop :=
  certificate.halfMomentumError =
      |certificate.computedHalfMomentum -
        (certificate.momentum - certificate.stepSize / 2 * certificate.position)| ∧
    certificate.nextPositionError =
      |certificate.computedNextPosition -
        (certificate.position +
          certificate.stepSize * certificate.computedHalfMomentum)| ∧
    certificate.nextMomentumError =
      |certificate.computedNextMomentum -
        (certificate.computedHalfMomentum - certificate.stepSize / 2 *
          certificate.computedNextPosition)|

def GaussianRoundedLeapfrogStepCertificate.check
    (certificate : GaussianRoundedLeapfrogStepCertificate) : Bool :=
  certificate.halfMomentumError ==
      |certificate.computedHalfMomentum -
        (certificate.momentum - certificate.stepSize / 2 * certificate.position)| &&
    (certificate.nextPositionError ==
        |certificate.computedNextPosition -
          (certificate.position +
            certificate.stepSize * certificate.computedHalfMomentum)| &&
      certificate.nextMomentumError ==
        |certificate.computedNextMomentum -
          (certificate.computedHalfMomentum - certificate.stepSize / 2 *
            certificate.computedNextPosition)|)

@[simp] theorem GaussianRoundedLeapfrogStepCertificate.check_eq_true_iff
    (certificate : GaussianRoundedLeapfrogStepCertificate) :
    certificate.check = true ↔ certificate.Valid := by
  simp [GaussianRoundedLeapfrogStepCertificate.check,
    GaussianRoundedLeapfrogStepCertificate.Valid]

/-- The checked half-kick residual is an exact real absolute-error bound. -/
theorem GaussianRoundedLeapfrogStepCertificate.halfMomentum_bound
    (certificate : GaussianRoundedLeapfrogStepCertificate)
    (hvalid : certificate.Valid) :
    |(certificate.computedHalfMomentum : ℝ) -
      (certificate.momentum - certificate.stepSize / 2 * certificate.position)| ≤
        certificate.halfMomentumError := by
  have h := hvalid.1
  exact_mod_cast h.ge

/-- The checked drift residual is an exact real absolute-error bound. -/
theorem GaussianRoundedLeapfrogStepCertificate.nextPosition_bound
    (certificate : GaussianRoundedLeapfrogStepCertificate)
    (hvalid : certificate.Valid) :
    |(certificate.computedNextPosition : ℝ) -
      (certificate.position +
        certificate.stepSize * certificate.computedHalfMomentum)| ≤
          certificate.nextPositionError := by
  have h := hvalid.2.1
  exact_mod_cast h.ge

/-- The checked final-kick residual is an exact real absolute-error bound. -/
theorem GaussianRoundedLeapfrogStepCertificate.nextMomentum_bound
    (certificate : GaussianRoundedLeapfrogStepCertificate)
    (hvalid : certificate.Valid) :
    |(certificate.computedNextMomentum : ℝ) -
      (certificate.computedHalfMomentum - certificate.stepSize / 2 *
        certificate.computedNextPosition)| ≤ certificate.nextMomentumError := by
  have h := hvalid.2.2
  exact_mod_cast h.ge

/-- Target-independent rounded leapfrog arithmetic. Callback values are
explicit fields, allowing separate generated-target certificates to justify
them (for example the quartic certificates in `RestrictedCertificate`). -/
structure RoundedLeapfrogRationalCertificate where
  stepSize : ℚ
  position : ℚ
  momentum : ℚ
  currentGradient : ℚ
  computedHalfMomentum : ℚ
  computedNextPosition : ℚ
  nextGradient : ℚ
  computedNextMomentum : ℚ
  halfMomentumError : ℚ
  nextPositionError : ℚ
  nextMomentumError : ℚ
deriving DecidableEq, Repr

def RoundedLeapfrogRationalCertificate.Valid
    (certificate : RoundedLeapfrogRationalCertificate) : Prop :=
  certificate.halfMomentumError =
      |certificate.computedHalfMomentum -
        (certificate.momentum - certificate.stepSize / 2 *
          certificate.currentGradient)| ∧
    certificate.nextPositionError =
      |certificate.computedNextPosition -
        (certificate.position +
          certificate.stepSize * certificate.computedHalfMomentum)| ∧
    certificate.nextMomentumError =
      |certificate.computedNextMomentum -
        (certificate.computedHalfMomentum - certificate.stepSize / 2 *
          certificate.nextGradient)|

def RoundedLeapfrogRationalCertificate.check
    (certificate : RoundedLeapfrogRationalCertificate) : Bool :=
  certificate.halfMomentumError ==
      |certificate.computedHalfMomentum -
        (certificate.momentum - certificate.stepSize / 2 *
          certificate.currentGradient)| &&
    (certificate.nextPositionError ==
        |certificate.computedNextPosition -
          (certificate.position +
            certificate.stepSize * certificate.computedHalfMomentum)| &&
      certificate.nextMomentumError ==
        |certificate.computedNextMomentum -
          (certificate.computedHalfMomentum - certificate.stepSize / 2 *
            certificate.nextGradient)|)

@[simp] theorem RoundedLeapfrogRationalCertificate.check_eq_true_iff
    (certificate : RoundedLeapfrogRationalCertificate) :
    certificate.check = true ↔ certificate.Valid := by
  simp [RoundedLeapfrogRationalCertificate.check,
    RoundedLeapfrogRationalCertificate.Valid]

/-- Generated quartic callback records plus matching fields justify the two
gradient values consumed by a generic rounded leapfrog record. -/
structure QuarticRoundedLeapfrogCertificate where
  arithmetic : RoundedLeapfrogRationalCertificate
  currentCallback : RestrictedQuarticRationalCertificate
  nextCallback : RestrictedQuarticRationalCertificate
  currentInput_eq : currentCallback.input = arithmetic.position
  nextInput_eq : nextCallback.input = arithmetic.computedNextPosition
  currentGradient_eq :
    currentCallback.computedDerivative = arithmetic.currentGradient
  nextGradient_eq : nextCallback.computedDerivative = arithmetic.nextGradient

def QuarticRoundedLeapfrogCertificate.Valid
    (certificate : QuarticRoundedLeapfrogCertificate) : Prop :=
  certificate.arithmetic.Valid ∧ certificate.currentCallback.Valid ∧
    certificate.nextCallback.Valid

/-- A valid composite record simultaneously checks rounded arithmetic and both
generated quartic callback evaluations. -/
theorem QuarticRoundedLeapfrogCertificate.valid_of_checks
    (certificate : QuarticRoundedLeapfrogCertificate)
    (harithmetic : certificate.arithmetic.check = true)
    (hcurrent : certificate.currentCallback.check = true)
    (hnext : certificate.nextCallback.check = true) : certificate.Valid := by
  exact ⟨(RoundedLeapfrogRationalCertificate.check_eq_true_iff
      certificate.arithmetic).mp harithmetic,
    certificate.currentCallback.valid_of_check hcurrent,
    certificate.nextCallback.valid_of_check hnext⟩

end Mcmc.Executable.Continuous
