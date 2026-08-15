import Mcmc.Executable.Continuous.BoundedRWMH
import Mcmc.Relativistic.FixedPointIteration

/-!
# Backend residual certificates for implicit GR-HMC solves

A positive tolerance certifies approximation only. Exact generalized-leapfrog
validity can consume this layer only when the certified residual-error budgets
are zero; uniqueness, reversal, and volume preservation remain independent
global obligations in `FiniteFixedPointIsValid`.
-/

namespace Mcmc.Executable.Continuous

/-- Backend-facing bounds for the two implicit fixed-point residual norms. -/
structure BackendImplicitResidualCertificate where
  computedHalfResidual : ℝ
  computedPositionResidual : ℝ
  halfResidualError : ℝ
  positionResidualError : ℝ
  half_bound : Approximates computedHalfResidual 0 halfResidualError
  position_bound : Approximates computedPositionResidual 0 positionResidualError
  half_error_zero : halfResidualError = 0
  position_error_zero : positionResidualError = 0

theorem BackendImplicitResidualCertificate.halfResidual_eq_zero
    (certificate : BackendImplicitResidualCertificate) :
    certificate.computedHalfResidual = 0 := by
  have hbound := certificate.half_bound
  rw [certificate.half_error_zero] at hbound
  unfold Approximates at hbound
  simp only [sub_zero] at hbound
  exact abs_eq_zero.mp (le_antisymm hbound
    (abs_nonneg certificate.computedHalfResidual))

theorem BackendImplicitResidualCertificate.positionResidual_eq_zero
    (certificate : BackendImplicitResidualCertificate) :
    certificate.computedPositionResidual = 0 := by
  have hbound := certificate.position_bound
  rw [certificate.position_error_zero] at hbound
  unfold Approximates at hbound
  simp only [sub_zero] at hbound
  exact abs_eq_zero.mp (le_antisymm hbound
    (abs_nonneg certificate.computedPositionResidual))

/-- A strictly positive residual budget is not a zero exactness budget. -/
theorem positive_tolerance_not_zero_budget {ε : ℝ} (hε : 0 < ε) : ε ≠ 0 :=
  ne_of_gt hε

open Mcmc.Hamiltonian
open Mcmc.Relativistic

/-- A family of zero-budget backend residual certificates discharges the exact
finite fixed-point premise when its reported values are identified with the
two actual metric residuals. Global uniqueness, reversal, and volume
preservation are then supplied through `FiniteFixedPointIsValid`. -/
theorem finiteFixedPointIsExact_of_backendCertificates
    {ι : Type*} [Fintype ι]
    (positionDerivative momentumDerivative : PhaseSpace ι → Position ι)
    (iterations : ℕ)
    (certificate : ∀ (_ε : ℝ) (_z : PhaseSpace ι),
      BackendImplicitResidualCertificate)
    (hhalf : ∀ ε z,
      (certificate ε z).computedHalfResidual =
        let result := finiteFixedPointGeneralizedLeapfrog positionDerivative
          momentumDerivative iterations ε z
        dist result.1
          (halfMomentumFixedPointUpdate positionDerivative ε z result.1))
    (hposition : ∀ ε z,
      (certificate ε z).computedPositionResidual =
        let result := finiteFixedPointGeneralizedLeapfrog positionDerivative
          momentumDerivative iterations ε z
        dist result.2.1
          (positionFixedPointUpdate momentumDerivative ε z.1 result.1
            result.2.1)) :
    FiniteFixedPointIsExact positionDerivative momentumDerivative iterations := by
  apply finiteFixedPointIsExact_of_dist_eq_zero
  · intro ε z
    simpa only using (hhalf ε z).symm.trans
      (certificate ε z).halfResidual_eq_zero
  · intro ε z
    simpa only using (hposition ε z).symm.trans
      (certificate ε z).positionResidual_eq_zero

end Mcmc.Executable.Continuous
