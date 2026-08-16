import Mcmc.Executable.Continuous.BoundedRWMH
import Mcmc.Executable.Continuous.BoundedHMC
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

/-- Propagate an approximate half-momentum error into the implicit position
solve for the concrete nonconstant SoftAbs target. The first term is the
reported position residual budget; the second is fixed-point sensitivity to
the supplied half momentum. -/
theorem shiftedSinusoidalSoftAbs_nextPosition_error_le_of_half_error
    (z : PhaseSpace Unit) (pApprox qApprox : Position Unit)
    {halfError computedPositionResidual positionResidualError : ℝ}
    (hhalfError : dist pApprox
      (shiftedSinusoidalSoftAbsCertifiedSolver.halfMomentum z) ≤ halfError)
    (hpositionResidual : Approximates computedPositionResidual
      (dist qApprox
        (positionFixedPointUpdate
          shiftedSinusoidalSoftAbsMomentumDerivative
          shiftedSinusoidalSoftAbsCertifiedStep z.1 pApprox qApprox))
      positionResidualError) :
    dist qApprox (shiftedSinusoidalSoftAbsCertifiedSolver.nextPosition z) ≤
      (|computedPositionResidual| + positionResidualError) /
          (1 - generalizedLeapfrogSliceRate
            shiftedSinusoidalSoftAbsCertifiedStep
            (2 * shiftedSinusoidalSoftAbsScaleLipschitzConstant)) +
        (2 * |shiftedSinusoidalSoftAbsCertifiedStep / 2| * halfError) /
          (1 - generalizedLeapfrogSliceRate
            shiftedSinusoidalSoftAbsCertifiedStep
            (2 * shiftedSinusoidalSoftAbsScaleLipschitzConstant)) := by
  let K := generalizedLeapfrogSliceRate
    shiftedSinusoidalSoftAbsCertifiedStep
    (2 * shiftedSinusoidalSoftAbsScaleLipschitzConstant)
  have hslice : ∀ p, LipschitzWith
      (2 * shiftedSinusoidalSoftAbsScaleLipschitzConstant)
      (fun q => shiftedSinusoidalSoftAbsMomentumDerivative (q, p)) := by
    intro p
    exact scalarGRMomentumCallbackUnit_lipschitz_position
      shiftedSinusoidalSoftAbsScaleReal p
      shiftedSinusoidalSoftAbsScaleLipschitzConstant
      shiftedSinusoidalSoftAbsScaleReal_lipschitz
  have hpApprox : ContractingWith K
      (positionFixedPointUpdate shiftedSinusoidalSoftAbsMomentumDerivative
        shiftedSinusoidalSoftAbsCertifiedStep z.1 pApprox) := by
    exact nextPosition_contracting_of_lipschitz
      shiftedSinusoidalSoftAbsMomentumDerivative
      shiftedSinusoidalSoftAbsCertifiedStep
      (2 * shiftedSinusoidalSoftAbsScaleLipschitzConstant) hslice
      shiftedSinusoidalSoftAbsCertifiedStep_momentum_bound z.1 pApprox
  have hpExact : ContractingWith K
      (positionFixedPointUpdate shiftedSinusoidalSoftAbsMomentumDerivative
        shiftedSinusoidalSoftAbsCertifiedStep z.1
        (shiftedSinusoidalSoftAbsCertifiedSolver.halfMomentum z)) := by
    exact nextPosition_contracting_of_lipschitz
      shiftedSinusoidalSoftAbsMomentumDerivative
      shiftedSinusoidalSoftAbsCertifiedStep
      (2 * shiftedSinusoidalSoftAbsScaleLipschitzConstant) hslice
      shiftedSinusoidalSoftAbsCertifiedStep_momentum_bound z.1
      (shiftedSinusoidalSoftAbsCertifiedSolver.halfMomentum z)
  have hresidual : dist qApprox
      (hpApprox.fixedPoint
        (positionFixedPointUpdate shiftedSinusoidalSoftAbsMomentumDerivative
          shiftedSinusoidalSoftAbsCertifiedStep z.1 pApprox)) ≤
      (|computedPositionResidual| + positionResidualError) / (1 - K) :=
    dist_fixedPoint_le_of_computedResidual hpApprox qApprox hpositionResidual
  have hsensitivity := dist_positionFixedPoints_le_of_momentum_lipschitz
    shiftedSinusoidalSoftAbsMomentumDerivative 1 K
    shiftedSinusoidalSoftAbsMomentumDerivative_lipschitz_momentum
    shiftedSinusoidalSoftAbsCertifiedStep z.1 pApprox
    (shiftedSinusoidalSoftAbsCertifiedSolver.halfMomentum z)
    hpApprox hpExact
  have hsensitivity' : dist
      (hpApprox.fixedPoint
        (positionFixedPointUpdate shiftedSinusoidalSoftAbsMomentumDerivative
          shiftedSinusoidalSoftAbsCertifiedStep z.1 pApprox))
      (shiftedSinusoidalSoftAbsCertifiedSolver.nextPosition z) ≤
      (2 * |shiftedSinusoidalSoftAbsCertifiedStep / 2| * halfError) /
        (1 - K) := by
    change _ ≤ _ at hsensitivity ⊢
    calc
      _ ≤ (2 * |shiftedSinusoidalSoftAbsCertifiedStep / 2| *
          (1 : ℝ) * dist pApprox
            (shiftedSinusoidalSoftAbsCertifiedSolver.halfMomentum z)) /
            (1 - K) := hsensitivity
      _ ≤ (2 * |shiftedSinusoidalSoftAbsCertifiedStep / 2| * halfError) /
            (1 - K) := by
        have hden : 0 ≤ (1 - K : ℝ) := sub_nonneg.mpr hpApprox.1.le
        apply div_le_div_of_nonneg_right _ hden
        simpa only [NNReal.coe_one, mul_one] using
          mul_le_mul_of_nonneg_left hhalfError
            (mul_nonneg (by norm_num) (abs_nonneg _))
  exact (dist_triangle _ _ _).trans (add_le_add hresidual hsensitivity')

/-- Generic final-kick error propagation. Separate slice constants make the
source of error explicit: half-momentum error enters both directly and through
the callback, while next-position error enters through the position slice. -/
theorem generalizedLeapfrogFinalMomentum_error_le
    {ι : Type*} [Fintype ι]
    (positionDerivative : PhaseSpace ι → Position ι)
    (P Q : NNReal)
    (hlipMomentum : ∀ q, LipschitzWith P
      (fun p => positionDerivative (q, p)))
    (hlipPosition : ∀ p, LipschitzWith Q
      (fun q => positionDerivative (q, p)))
    (ε : ℝ) (pApprox pExact : Momentum ι)
    (qApprox qExact : Position ι) :
    dist (pApprox - (ε / 2) • positionDerivative (qApprox, pApprox))
        (pExact - (ε / 2) • positionDerivative (qExact, pExact)) ≤
      (1 + |ε / 2| * P) * dist pApprox pExact +
        |ε / 2| * Q * dist qApprox qExact := by
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
  have hp := (hlipMomentum qApprox).dist_le_mul pApprox pExact
  have hq := (hlipPosition pExact).dist_le_mul qApprox qExact
  have hcallback :
      ‖positionDerivative (qApprox, pApprox) -
          positionDerivative (qExact, pExact)‖ ≤
        P * ‖pApprox - pExact‖ + Q * ‖qApprox - qExact‖ := by
    calc
      _ ≤ ‖positionDerivative (qApprox, pApprox) -
            positionDerivative (qApprox, pExact)‖ +
          ‖positionDerivative (qApprox, pExact) -
            positionDerivative (qExact, pExact)‖ := by
        rw [show positionDerivative (qApprox, pApprox) -
              positionDerivative (qExact, pExact) =
            (positionDerivative (qApprox, pApprox) -
              positionDerivative (qApprox, pExact)) +
            (positionDerivative (qApprox, pExact) -
              positionDerivative (qExact, pExact)) by module]
        exact norm_add_le _ _
      _ ≤ P * ‖pApprox - pExact‖ + Q * ‖qApprox - qExact‖ := by
        exact add_le_add (by simpa [dist_eq_norm] using hp)
          (by simpa [dist_eq_norm] using hq)
  rw [show (pApprox - (ε / 2) • positionDerivative (qApprox, pApprox)) -
        (pExact - (ε / 2) • positionDerivative (qExact, pExact)) =
      (pApprox - pExact) - (ε / 2) •
        (positionDerivative (qApprox, pApprox) -
          positionDerivative (qExact, pExact)) by module]
  calc
    _ ≤ ‖pApprox - pExact‖ +
        ‖(ε / 2) • (positionDerivative (qApprox, pApprox) -
          positionDerivative (qExact, pExact))‖ := norm_sub_le _ _
    _ = ‖pApprox - pExact‖ + |ε / 2| *
        ‖positionDerivative (qApprox, pApprox) -
          positionDerivative (qExact, pExact)‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖pApprox - pExact‖ + |ε / 2| *
        (P * ‖pApprox - pExact‖ + Q * ‖qApprox - qExact‖) := by
      gcongr
    _ = (1 + |ε / 2| * P) * ‖pApprox - pExact‖ +
        |ε / 2| * Q * ‖qApprox - qExact‖ := by ring

/-- Scalar final-kick propagation from a compact-region Lipschitz certificate
on the complete position callback. -/
theorem scalarGeneralizedLeapfrogFinalMomentum_error_le_of_lipschitzOn
    (positionCallback : ℝ × ℝ → ℝ) (region : Set (ℝ × ℝ))
    (Q : NNReal) (hlip : LipschitzOnWith Q positionCallback region)
    (ε pApprox pExact : ℝ) (zApprox zExact : ℝ × ℝ)
    (hzApprox : zApprox ∈ region) (hzExact : zExact ∈ region)
    {momentumError phaseError : ℝ}
    (hmomentum : |pApprox - pExact| ≤ momentumError)
    (hphase : dist zApprox zExact ≤ phaseError) :
    |(pApprox - (ε / 2) * positionCallback zApprox) -
        (pExact - (ε / 2) * positionCallback zExact)| ≤
      momentumError + |ε / 2| * Q * phaseError := by
  have hcallback := hlip.dist_le_mul zApprox hzApprox zExact hzExact
  rw [Real.dist_eq] at hcallback
  rw [show (pApprox - (ε / 2) * positionCallback zApprox) -
        (pExact - (ε / 2) * positionCallback zExact) =
      (pApprox - pExact) - (ε / 2) *
        (positionCallback zApprox - positionCallback zExact) by ring]
  calc
    _ ≤ |pApprox - pExact| +
        |(ε / 2) * (positionCallback zApprox - positionCallback zExact)| :=
      abs_sub _ _
    _ = |pApprox - pExact| + |ε / 2| *
        |positionCallback zApprox - positionCallback zExact| := by
      rw [abs_mul]
    _ ≤ momentumError + |ε / 2| * (Q * dist zApprox zExact) := by
      exact add_le_add hmomentum
        (mul_le_mul_of_nonneg_left hcallback (abs_nonneg _))
    _ ≤ momentumError + |ε / 2| * Q * phaseError := by
      have hcoef : 0 ≤ |ε / 2| * (Q : ℝ) := mul_nonneg (abs_nonneg _) NNReal.zero_le_coe
      have hmul := mul_le_mul_of_nonneg_left hphase hcoef
      simpa only [mul_assoc, add_comm] using
        add_le_add_left hmul momentumError

/-- Target-specific endpoint-energy transport on a certified compact scalar
phase ball. This is the direct input to `energyDifference_approximates` and
the existing HMC/multinomial stable-decision certificates. -/
theorem shiftedSinusoidalSoftAbs_endpointEnergy_approximates
    (center : ℝ × ℝ) (radius : ℝ) (hradius : 0 ≤ radius)
    {computedState idealState : ℝ × ℝ}
    (hcomputedRegion : computedState ∈ Metric.closedBall center radius)
    (hidealRegion : idealState ∈ Metric.closedBall center radius)
    {computedEnergy evaluationError stateError : ℝ}
    (hevaluation : Approximates computedEnergy
      (scalarGRHamiltonianReal shiftedSinusoidalSoftAbsBaseReal
        shiftedSinusoidalSoftAbsScaleReal computedState) evaluationError)
    (hstate : dist computedState idealState ≤ stateError) :
    Approximates computedEnergy
      (scalarGRHamiltonianReal shiftedSinusoidalSoftAbsBaseReal
        shiftedSinusoidalSoftAbsScaleReal idealState)
      (evaluationError +
        shiftedSinusoidalSoftAbsHamiltonianLipschitzConstant
          center radius hradius * stateError) := by
  exact endpointEnergy_approximates_of_lipschitzOn
    (scalarGRHamiltonianReal shiftedSinusoidalSoftAbsBaseReal
      shiftedSinusoidalSoftAbsScaleReal)
    (Metric.closedBall center radius)
    (shiftedSinusoidalSoftAbsHamiltonianLipschitzConstant
      center radius hradius)
    (shiftedSinusoidalSoftAbsHamiltonian_lipschitzOn_closedBall
      center radius hradius)
    hcomputedRegion hidealRegion hevaluation hstate

/-- A canonical compact ball containing a computed/ideal scalar phase pair. -/
def scalarPhasePairRadius (computed ideal : ℝ × ℝ) : ℝ :=
  max ‖computed‖ ‖ideal‖

theorem scalarPhasePairRadius_nonneg (computed ideal : ℝ × ℝ) :
    0 ≤ scalarPhasePairRadius computed ideal := by
  exact (norm_nonneg computed).trans (le_max_left _ _)

theorem mem_closedBall_zero_scalarPhasePairRadius_left
    (computed ideal : ℝ × ℝ) :
    computed ∈ Metric.closedBall (0 : ℝ × ℝ)
      (scalarPhasePairRadius computed ideal) := by
  rw [Metric.mem_closedBall, dist_zero_right]
  exact le_max_left _ _

theorem mem_closedBall_zero_scalarPhasePairRadius_right
    (computed ideal : ℝ × ℝ) :
    ideal ∈ Metric.closedBall (0 : ℝ × ℝ)
      (scalarPhasePairRadius computed ideal) := by
  rw [Metric.mem_closedBall, dist_zero_right]
  exact le_max_right _ _

/-- Automatic compact-region final-kick certificate for the actual SoftAbs
callback at a concrete approximate/ideal phase pair. -/
theorem shiftedSinusoidalSoftAbs_finalMomentum_error_le_pair
    (ε pApprox pExact qApprox qExact : ℝ)
    {momentumError phaseError : ℝ}
    (hmomentum : |pApprox - pExact| ≤ momentumError)
    (hphase : dist (qApprox, pApprox) (qExact, pExact) ≤ phaseError) :
    |(pApprox - (ε / 2) * shiftedSinusoidalSoftAbsPositionCallbackReal
          (qApprox, pApprox)) -
        (pExact - (ε / 2) * shiftedSinusoidalSoftAbsPositionCallbackReal
          (qExact, pExact))| ≤
      momentumError + |ε / 2| *
        shiftedSinusoidalSoftAbsPositionCallbackLipschitzConstant 0
          (scalarPhasePairRadius (qApprox, pApprox) (qExact, pExact))
          (scalarPhasePairRadius_nonneg (qApprox, pApprox) (qExact, pExact)) *
        phaseError := by
  exact scalarGeneralizedLeapfrogFinalMomentum_error_le_of_lipschitzOn
    shiftedSinusoidalSoftAbsPositionCallbackReal
    (Metric.closedBall (0 : ℝ × ℝ)
      (scalarPhasePairRadius (qApprox, pApprox) (qExact, pExact)))
    (shiftedSinusoidalSoftAbsPositionCallbackLipschitzConstant 0
      (scalarPhasePairRadius (qApprox, pApprox) (qExact, pExact))
      (scalarPhasePairRadius_nonneg (qApprox, pApprox) (qExact, pExact)))
    (shiftedSinusoidalSoftAbsPositionCallback_lipschitzOn_closedBall 0
      (scalarPhasePairRadius (qApprox, pApprox) (qExact, pExact))
      (scalarPhasePairRadius_nonneg (qApprox, pApprox) (qExact, pExact)))
    ε pApprox pExact (qApprox, pApprox) (qExact, pExact)
    (mem_closedBall_zero_scalarPhasePairRadius_left
      (qApprox, pApprox) (qExact, pExact))
    (mem_closedBall_zero_scalarPhasePairRadius_right
      (qApprox, pApprox) (qExact, pExact))
    hmomentum hphase

/-- Every concrete computed/ideal endpoint pair therefore receives an
automatic compact-region SoftAbs energy certificate; callers need only bound
their state distance and backend energy evaluation. -/
theorem shiftedSinusoidalSoftAbs_endpointEnergy_approximates_pair
    {computedState idealState : ℝ × ℝ}
    {computedEnergy evaluationError stateError : ℝ}
    (hevaluation : Approximates computedEnergy
      (scalarGRHamiltonianReal shiftedSinusoidalSoftAbsBaseReal
        shiftedSinusoidalSoftAbsScaleReal computedState) evaluationError)
    (hstate : dist computedState idealState ≤ stateError) :
    Approximates computedEnergy
      (scalarGRHamiltonianReal shiftedSinusoidalSoftAbsBaseReal
        shiftedSinusoidalSoftAbsScaleReal idealState)
      (evaluationError +
        shiftedSinusoidalSoftAbsHamiltonianLipschitzConstant 0
          (scalarPhasePairRadius computedState idealState)
          (scalarPhasePairRadius_nonneg computedState idealState) *
            stateError) := by
  exact shiftedSinusoidalSoftAbs_endpointEnergy_approximates 0
    (scalarPhasePairRadius computedState idealState)
    (scalarPhasePairRadius_nonneg computedState idealState)
    (mem_closedBall_zero_scalarPhasePairRadius_left computedState idealState)
    (mem_closedBall_zero_scalarPhasePairRadius_right computedState idealState)
    hevaluation hstate

/-- Coordinate budgets combine into the product-metric phase budget used by
the endpoint-energy certificate. -/
theorem scalarPhase_dist_le_max
    {qApprox qExact pApprox pExact qError pError : ℝ}
    (hq : dist qApprox qExact ≤ qError)
    (hp : dist pApprox pExact ≤ pError) :
    dist (qApprox, pApprox) (qExact, pExact) ≤ max qError pError := by
  rw [Prod.dist_eq, max_le_iff]
  exact ⟨hq.trans (le_max_left _ _), hp.trans (le_max_right _ _)⟩

/-- Final scalar phase-coordinate errors plus a backend Hamiltonian evaluation
bound produce the complete actual-target endpoint-energy certificate. -/
theorem shiftedSinusoidalSoftAbs_endpointEnergy_approximates_of_coordinateErrors
    {qApprox qExact pApprox pExact : ℝ}
    {qError pError computedEnergy evaluationError : ℝ}
    (hq : dist qApprox qExact ≤ qError)
    (hp : dist pApprox pExact ≤ pError)
    (hevaluation : Approximates computedEnergy
      (scalarGRHamiltonianReal shiftedSinusoidalSoftAbsBaseReal
        shiftedSinusoidalSoftAbsScaleReal (qApprox, pApprox))
      evaluationError) :
    Approximates computedEnergy
      (scalarGRHamiltonianReal shiftedSinusoidalSoftAbsBaseReal
        shiftedSinusoidalSoftAbsScaleReal (qExact, pExact))
      (evaluationError +
        shiftedSinusoidalSoftAbsHamiltonianLipschitzConstant 0
          (scalarPhasePairRadius (qApprox, pApprox) (qExact, pExact))
          (scalarPhasePairRadius_nonneg (qApprox, pApprox) (qExact, pExact)) *
            max qError pError) := by
  exact shiftedSinusoidalSoftAbs_endpointEnergy_approximates_pair hevaluation
    (scalarPhase_dist_le_max hq hp)

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
