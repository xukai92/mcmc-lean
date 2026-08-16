import Mcmc.Executable.Continuous.RestrictedRefinement

/-!
# Exact-rational restricted Gaussian execution certificates

Finite IEEE values are dyadic rationals. A foreign runtime can therefore
serialize its input, value, derivative, and observed errors exactly as `ℚ`.
This module checks that record against the generated Gaussian target's proved
ideal-real semantics and turns successful checks into `Approximates` theorems.
-/

namespace Mcmc.Executable.Continuous

/-- Cross-language certificate payload for one generated Gaussian target
evaluation. All fields denote exact rationals, not decimal approximations. -/
structure RestrictedGaussianRationalCertificate where
  input : ℚ
  computedValue : ℚ
  computedDerivative : ℚ
  computedSecondDerivative : ℚ
  valueError : ℚ
  derivativeError : ℚ
  secondDerivativeError : ℚ
  deriving DecidableEq, Repr

/-- Exact checker predicate. Error fields must be the actual absolute rational
differences from `x²/2` and `x`. -/
def RestrictedGaussianRationalCertificate.Valid
    (certificate : RestrictedGaussianRationalCertificate) : Prop :=
  certificate.valueError =
      |certificate.computedValue - certificate.input ^ 2 / 2| ∧
    certificate.derivativeError =
      |certificate.computedDerivative - certificate.input| ∧
    certificate.secondDerivativeError =
      |certificate.computedSecondDerivative - 1|

instance (certificate : RestrictedGaussianRationalCertificate) :
    Decidable certificate.Valid := by
  unfold RestrictedGaussianRationalCertificate.Valid
  infer_instance

/-- Executable Boolean form used by the compiled oracle. -/
def RestrictedGaussianRationalCertificate.check
    (certificate : RestrictedGaussianRationalCertificate) : Bool :=
  decide certificate.Valid

theorem RestrictedGaussianRationalCertificate.valid_of_check
    {certificate : RestrictedGaussianRationalCertificate}
    (hcheck : certificate.check = true) : certificate.Valid := by
  exact of_decide_eq_true hcheck

/-- A valid exact-rational record certifies the generated target value after
embedding its dyadic data into the mathematical reals. -/
theorem RestrictedGaussianRationalCertificate.value_approximates
    (certificate : RestrictedGaussianRationalCertificate)
    (hvalid : certificate.Valid) :
    Approximates (certificate.computedValue : ℝ)
      (restrictedGaussianPotential.eval (certificate.input : ℝ))
      (certificate.valueError : ℝ) := by
  rw [restrictedGaussianPotential_eval]
  rw [Approximates]
  norm_cast
  rw [hvalid.1]

/-- The same record certifies the generated symbolic derivative. -/
theorem RestrictedGaussianRationalCertificate.derivative_approximates
    (certificate : RestrictedGaussianRationalCertificate)
    (hvalid : certificate.Valid) :
    Approximates (certificate.computedDerivative : ℝ)
      (restrictedGaussianPotential.derivative.eval (certificate.input : ℝ))
      (certificate.derivativeError : ℝ) := by
  rw [restrictedGaussianPotential_derivative_eval]
  rw [Approximates]
  norm_cast
  rw [hvalid.2.1]

/-- The same exact record reaches the Hessian consumed by diagonal SoftAbs. -/
theorem RestrictedGaussianRationalCertificate.secondDerivative_approximates
    (certificate : RestrictedGaussianRationalCertificate)
    (hvalid : certificate.Valid) :
    Approximates (certificate.computedSecondDerivative : ℝ)
      (restrictedGaussianPotential.derivative.derivative.eval
        (certificate.input : ℝ))
      (certificate.secondDerivativeError : ℝ) := by
  rw [restrictedGaussianPotential_secondDerivative_eval]
  rw [Approximates]
  norm_cast
  rw [hvalid.2.2]

end Mcmc.Executable.Continuous
