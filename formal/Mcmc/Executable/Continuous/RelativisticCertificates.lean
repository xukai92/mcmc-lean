import Mcmc.Executable.Continuous.BoundedRWMH
import Mcmc.Relativistic.FixedPointIteration
import Mcmc.Relativistic.ShiftedSinusoidalSoftAbs

/-!
# Backend residual certificates for implicit GR-HMC solves

A positive tolerance certifies approximation only. Exact generalized-leapfrog
validity can consume this layer only when the certified residual-error budgets
are zero; uniqueness, reversal, and volume preservation remain independent
global obligations in `FiniteFixedPointIsValid`.
-/

namespace Mcmc.Executable.Continuous

open Mcmc.Hamiltonian
open Mcmc.Relativistic

/-- A computed fixed-point residual plus its absolute error controls distance
to the exact contraction-selected solution. This is the useful positive-error
counterpart of the zero-budget exactness bridge below. -/
theorem dist_fixedPoint_le_of_computedResidual
    {α : Type*} [MetricSpace α] [CompleteSpace α] [Nonempty α]
    {f : α → α} {K : NNReal}
    (hcontract : ContractingWith K f) (x : α)
    {computedResidual residualError : ℝ}
    (hresidual : Approximates computedResidual (dist x (f x)) residualError) :
    dist x (hcontract.fixedPoint f) ≤
      (|computedResidual| + residualError) / (1 - K) := by
  have herror : |computedResidual - dist x (f x)| ≤ residualError := hresidual
  have hdist : dist x (f x) ≤ |computedResidual| + residualError := by
    calc
      dist x (f x) = |dist x (f x)| := (abs_of_nonneg dist_nonneg).symm
      _ = |computedResidual - (computedResidual - dist x (f x))| := by ring_nf
      _ ≤ |computedResidual| + |computedResidual - dist x (f x)| :=
        abs_sub _ _
      _ ≤ |computedResidual| + residualError := add_le_add (le_refl _) herror
  exact (hcontract.dist_fixedPoint_le x).trans
    (div_le_div_of_nonneg_right hdist (sub_nonneg.mpr hcontract.1.le))

/-- A backend residual bound for a finite half-momentum iteration yields an
explicit distance to the exact contraction-selected half momentum. -/
theorem dist_finiteHalfMomentum_fixedPoint_le_of_computedResidual
    {ι : Type*} [Fintype ι]
    (positionDerivative : PhaseSpace ι → Position ι)
    (K : NNReal) (iterations : ℕ) (ε : ℝ) (z : PhaseSpace ι)
    (hcontract : ContractingWith K
      (halfMomentumFixedPointUpdate positionDerivative ε z))
    {computedResidual residualError : ℝ}
    (hresidual : Approximates computedResidual
      (dist (finiteHalfMomentum positionDerivative iterations ε z)
        (halfMomentumFixedPointUpdate positionDerivative ε z
          (finiteHalfMomentum positionDerivative iterations ε z)))
      residualError) :
    dist (finiteHalfMomentum positionDerivative iterations ε z)
        (hcontract.fixedPoint
          (halfMomentumFixedPointUpdate positionDerivative ε z)) ≤
      (|computedResidual| + residualError) / (1 - K) :=
  dist_fixedPoint_le_of_computedResidual hcontract _ hresidual

/-- The analogous a posteriori error bound for the finite implicit position
iteration. -/
theorem dist_finiteNextPosition_fixedPoint_le_of_computedResidual
    {ι : Type*} [Fintype ι]
    (momentumDerivative : PhaseSpace ι → Position ι)
    (K : NNReal) (iterations : ℕ) (ε : ℝ)
    (q : Position ι) (pHalf : Momentum ι)
    (hcontract : ContractingWith K
      (positionFixedPointUpdate momentumDerivative ε q pHalf))
    {computedResidual residualError : ℝ}
    (hresidual : Approximates computedResidual
      (dist (finiteNextPosition momentumDerivative iterations ε q pHalf)
        (positionFixedPointUpdate momentumDerivative ε q pHalf
          (finiteNextPosition momentumDerivative iterations ε q pHalf)))
      residualError) :
    dist (finiteNextPosition momentumDerivative iterations ε q pHalf)
        (hcontract.fixedPoint
          (positionFixedPointUpdate momentumDerivative ε q pHalf)) ≤
      (|computedResidual| + residualError) / (1 - K) :=
  dist_fixedPoint_le_of_computedResidual hcontract _ hresidual

/-- A reported residual for a finite half-momentum loop on the concrete
nonconstant actual-Hessian SoftAbs target bounds its distance to the exact
certified solver's half momentum. -/
theorem shiftedSinusoidalSoftAbs_finiteHalfMomentum_error_le
    (iterations : ℕ) (z : PhaseSpace Unit)
    {computedResidual residualError : ℝ}
    (hresidual : Approximates computedResidual
      (dist
        (finiteHalfMomentum shiftedSinusoidalSoftAbsPositionDerivative
          iterations shiftedSinusoidalSoftAbsCertifiedStep z)
        (halfMomentumFixedPointUpdate
          shiftedSinusoidalSoftAbsPositionDerivative
          shiftedSinusoidalSoftAbsCertifiedStep z
          (finiteHalfMomentum shiftedSinusoidalSoftAbsPositionDerivative
            iterations shiftedSinusoidalSoftAbsCertifiedStep z)))
      residualError) :
    dist
        (finiteHalfMomentum shiftedSinusoidalSoftAbsPositionDerivative
          iterations shiftedSinusoidalSoftAbsCertifiedStep z)
        (shiftedSinusoidalSoftAbsCertifiedSolver.halfMomentum z) ≤
      (|computedResidual| + residualError) /
        (1 - shiftedSinusoidalSoftAbsCertifiedSolver.halfRate z) := by
  exact dist_finiteHalfMomentum_fixedPoint_le_of_computedResidual
    shiftedSinusoidalSoftAbsPositionDerivative
    (shiftedSinusoidalSoftAbsCertifiedSolver.halfRate z)
    iterations shiftedSinusoidalSoftAbsCertifiedStep z
    (shiftedSinusoidalSoftAbsCertifiedSolver.halfContracting z) hresidual

/-- With the exact half momentum fixed, a reported finite position-loop
residual bounds distance to the exact next position of the same certified
SoftAbs solver. The separate perturbation from an approximate half momentum
remains visible rather than being hidden in this theorem. -/
theorem shiftedSinusoidalSoftAbs_finiteNextPosition_error_le
    (iterations : ℕ) (z : PhaseSpace Unit)
    {computedResidual residualError : ℝ}
    (hresidual : Approximates computedResidual
      (dist
        (finiteNextPosition shiftedSinusoidalSoftAbsMomentumDerivative
          iterations shiftedSinusoidalSoftAbsCertifiedStep z.1
          (shiftedSinusoidalSoftAbsCertifiedSolver.halfMomentum z))
        (positionFixedPointUpdate
          shiftedSinusoidalSoftAbsMomentumDerivative
          shiftedSinusoidalSoftAbsCertifiedStep z.1
          (shiftedSinusoidalSoftAbsCertifiedSolver.halfMomentum z)
          (finiteNextPosition shiftedSinusoidalSoftAbsMomentumDerivative
            iterations shiftedSinusoidalSoftAbsCertifiedStep z.1
            (shiftedSinusoidalSoftAbsCertifiedSolver.halfMomentum z))))
      residualError) :
    dist
        (finiteNextPosition shiftedSinusoidalSoftAbsMomentumDerivative
          iterations shiftedSinusoidalSoftAbsCertifiedStep z.1
          (shiftedSinusoidalSoftAbsCertifiedSolver.halfMomentum z))
        (shiftedSinusoidalSoftAbsCertifiedSolver.nextPosition z) ≤
      (|computedResidual| + residualError) /
        (1 - shiftedSinusoidalSoftAbsCertifiedSolver.positionRate z.1
          (shiftedSinusoidalSoftAbsCertifiedSolver.halfMomentum z)) := by
  exact dist_finiteNextPosition_fixedPoint_le_of_computedResidual
    shiftedSinusoidalSoftAbsMomentumDerivative
    (shiftedSinusoidalSoftAbsCertifiedSolver.positionRate z.1
      (shiftedSinusoidalSoftAbsCertifiedSolver.halfMomentum z))
    iterations shiftedSinusoidalSoftAbsCertifiedStep z.1
    (shiftedSinusoidalSoftAbsCertifiedSolver.halfMomentum z)
    (shiftedSinusoidalSoftAbsCertifiedSolver.positionContracting z.1
      (shiftedSinusoidalSoftAbsCertifiedSolver.halfMomentum z)) hresidual

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
