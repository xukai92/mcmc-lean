import Mcmc.Executable.Continuous.BoundedRWMH
import Mcmc.Executable.Continuous.BoundedHMC
import Mcmc.Executable.Continuous.RestrictedRefinement
import Mcmc.Executable.Continuous.SoftAbsRefinement
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

/-- Error accumulated by a rounded trajectory whose one-step exact map is
`K`-Lipschitz. `localError n` is the error of the rounded step when both the
rounded and exact local solves start from the rounded state at time `n`. -/
noncomputable def propagatedLocalError (K : NNReal) (localError : ℕ → ℝ) :
    ℕ → ℝ
  | 0 => 0
  | n + 1 => localError n + K * propagatedLocalError K localError n

/-- Sequential local endpoint certificates become a certificate against one
genuine exact trajectory once input error is propagated through a Lipschitz
exact step. This explicitly rules out the unsound shortcut of viewing exact
endpoints constructed from independently rounded inputs as a single orbit. -/
theorem dist_iterate_le_propagatedLocalError
    {α : Type*} [PseudoMetricSpace α]
    (step : α → α) (K : NNReal) (hstep : LipschitzWith K step)
    (computed : ℕ → α) (localError : ℕ → ℝ)
    (hlocal : ∀ n, dist (computed (n + 1)) (step (computed n)) ≤ localError n) :
    ∀ n, dist (computed n) ((step^[n]) (computed 0)) ≤
      propagatedLocalError K localError n := by
  intro n
  induction n with
  | zero => simp [propagatedLocalError]
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc
        dist (computed (n + 1)) (step ((step^[n]) (computed 0))) ≤
            dist (computed (n + 1)) (step (computed n)) +
              dist (step (computed n)) (step ((step^[n]) (computed 0))) :=
          dist_triangle _ _ _
        _ ≤ localError n + K * dist (computed n) ((step^[n]) (computed 0)) :=
          add_le_add (hlocal n) (hstep.dist_le_mul _ _)
        _ ≤ localError n + K * propagatedLocalError K localError n := by
          gcongr
        _ = propagatedLocalError K localError (n + 1) := rfl

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

/-- Explicit scalar final-kick propagation for the bounded `2+sin(q)` client.
The position-slice constant is evaluated conservatively from the rounded half
momentum and its certified error. -/
theorem boundedScalarFinalMomentum_error_le
    (ε pApprox pExact qApprox qExact computedMomentum : ℝ)
    {pError qError updateError : ℝ}
    (hpErrorNonneg : 0 ≤ pError)
    (hp : dist pApprox pExact ≤ pError)
    (hq : dist qApprox qExact ≤ qError)
    (hupdate : |computedMomentum -
        (pApprox - (ε / 2) *
          boundedScalarPositionDerivativeReal (qApprox, pApprox))| ≤
      updateError) :
    |computedMomentum -
        (pExact - (ε / 2) *
          boundedScalarPositionDerivativeReal (qExact, pExact))| ≤
      updateError + (1 + |ε / 2| * 3) * pError +
        |ε / 2| *
          (18 * (|pApprox| + pError) ^ 2 +
            3 * (|pApprox| + pError)) * qError := by
  have hpabs : |pExact| ≤ |pApprox| + pError := by
    calc
      |pExact| = |pApprox + (pExact - pApprox)| :=
        congrArg abs (by ring)
      _ ≤ |pApprox| + |pExact - pApprox| :=
        abs_add_le (pApprox : ℝ) (pExact - pApprox)
      _ ≤ |pApprox| + pError := by
        have hd : |pExact - pApprox| ≤ pError := by
          simpa [Real.dist_eq, abs_sub_comm] using hp
        linarith
  have hrate : (boundedScalarPositionDerivativePositionRate pExact : ℝ) ≤
      18 * (|pApprox| + pError) ^ 2 + 3 * (|pApprox| + pError) := by
    change 18 * pExact ^ 2 + 3 * |pExact| ≤ _
    have hboundNonneg : 0 ≤ |pApprox| + pError :=
      add_nonneg (abs_nonneg _) hpErrorNonneg
    have hsquare : pExact ^ 2 ≤ (|pApprox| + pError) ^ 2 := by
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg pExact) hboundNonneg).2 hpabs
    linarith
  have hpCallback :=
    (boundedScalarPositionDerivativeReal_lipschitz_snd qApprox).dist_le_mul
      pApprox pExact
  rw [Real.dist_eq] at hpCallback
  have hqCallback :=
    (boundedScalarPositionDerivativeReal_lipschitz_fst pExact).dist_le_mul
      qApprox qExact
  rw [Real.dist_eq] at hqCallback
  have hcallback :
      |boundedScalarPositionDerivativeReal (qApprox, pApprox) -
        boundedScalarPositionDerivativeReal (qExact, pExact)| ≤
      3 * |pApprox - pExact| +
        (boundedScalarPositionDerivativePositionRate pExact : ℝ) *
          |qApprox - qExact| := by
    calc
      _ ≤ |boundedScalarPositionDerivativeReal (qApprox, pApprox) -
            boundedScalarPositionDerivativeReal (qApprox, pExact)| +
          |boundedScalarPositionDerivativeReal (qApprox, pExact) -
            boundedScalarPositionDerivativeReal (qExact, pExact)| := by
        rw [show boundedScalarPositionDerivativeReal (qApprox, pApprox) -
              boundedScalarPositionDerivativeReal (qExact, pExact) =
            (boundedScalarPositionDerivativeReal (qApprox, pApprox) -
              boundedScalarPositionDerivativeReal (qApprox, pExact)) +
            (boundedScalarPositionDerivativeReal (qApprox, pExact) -
              boundedScalarPositionDerivativeReal (qExact, pExact)) by ring]
        exact abs_add_le _ _
      _ ≤ _ := add_le_add (by
          exact hpCallback) hqCallback
  have hkick : |(pApprox - (ε / 2) *
        boundedScalarPositionDerivativeReal (qApprox, pApprox)) -
      (pExact - (ε / 2) *
        boundedScalarPositionDerivativeReal (qExact, pExact))| ≤
      (1 + |ε / 2| * 3) * pError +
        |ε / 2| *
          (18 * (|pApprox| + pError) ^ 2 +
            3 * (|pApprox| + pError)) * qError := by
    rw [show (pApprox - (ε / 2) *
          boundedScalarPositionDerivativeReal (qApprox, pApprox)) -
        (pExact - (ε / 2) *
          boundedScalarPositionDerivativeReal (qExact, pExact)) =
      (pApprox - pExact) - (ε / 2) *
        (boundedScalarPositionDerivativeReal (qApprox, pApprox) -
          boundedScalarPositionDerivativeReal (qExact, pExact)) by ring]
    calc
      _ ≤ |pApprox - pExact| + |ε / 2| *
          |boundedScalarPositionDerivativeReal (qApprox, pApprox) -
            boundedScalarPositionDerivativeReal (qExact, pExact)| := by
        simpa [abs_mul] using abs_sub
          (pApprox - pExact)
          ((ε / 2) * (boundedScalarPositionDerivativeReal (qApprox, pApprox) -
            boundedScalarPositionDerivativeReal (qExact, pExact)))
      _ ≤ |pApprox - pExact| + |ε / 2| *
          (3 * |pApprox - pExact| +
            (boundedScalarPositionDerivativePositionRate pExact : ℝ) *
              |qApprox - qExact|) := by gcongr
      _ ≤ pError + |ε / 2| *
          (3 * pError +
            (18 * (|pApprox| + pError) ^ 2 +
              3 * (|pApprox| + pError)) * qError) := by
        apply add_le_add
        · simpa [Real.dist_eq] using hp
        · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left
              (by simpa [Real.dist_eq] using hp) (by norm_num)
          · exact mul_le_mul hrate (by simpa [Real.dist_eq] using hq)
              (by positivity) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ |computedMomentum -
          (pApprox - (ε / 2) *
            boundedScalarPositionDerivativeReal (qApprox, pApprox))| +
        |(pApprox - (ε / 2) *
            boundedScalarPositionDerivativeReal (qApprox, pApprox)) -
          (pExact - (ε / 2) *
            boundedScalarPositionDerivativeReal (qExact, pExact))| := by
      rw [show computedMomentum -
          (pExact - (ε / 2) *
            boundedScalarPositionDerivativeReal (qExact, pExact)) =
        (computedMomentum - (pApprox - (ε / 2) *
          boundedScalarPositionDerivativeReal (qApprox, pApprox))) +
        ((pApprox - (ε / 2) *
          boundedScalarPositionDerivativeReal (qApprox, pApprox)) -
        (pExact - (ε / 2) *
          boundedScalarPositionDerivativeReal (qExact, pExact))) by ring]
      exact abs_add_le _ _
    _ ≤ _ := by
      have := add_le_add hupdate hkick
      linarith

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

/-- The rational sine enclosure certifies the actual bounded-client scale at
the represented input. -/
theorem SinCosRationalIntervalCertificate.boundedScalarScale_approximates
    (certificate : SinCosRationalIntervalCertificate)
    (hvalid : certificate.Valid) :
    Approximates (2 + certificate.computedSin : ℝ)
      (boundedScalarScale (fun _ => (certificate.input : ℝ)))
      certificate.sinError := by
  simpa [boundedScalarScale] using
    (Approximates.refl (2 : ℝ)).add (certificate.sin_approximates hvalid)

/-- A purely rational error radius for the scale-times-cosine factor appearing
in the bounded client's position callback. -/
theorem SinCosRationalIntervalCertificate.boundedScalarScaleCos_approximates
    (certificate : SinCosRationalIntervalCertificate)
    (hvalid : certificate.Valid) :
    Approximates
      ((2 + certificate.computedSin : ℝ) * certificate.computedCos)
      (boundedScalarScale (fun _ => (certificate.input : ℝ)) *
        Real.cos certificate.input)
      ((certificate.sinError : ℝ) * |(certificate.computedCos : ℝ)| +
        3 * (certificate.cosError : ℝ)) := by
  have hscale := certificate.boundedScalarScale_approximates hvalid
  have hcos := certificate.cos_approximates hvalid
  apply (hscale.mul hcos).mono
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
    (by
      rw [abs_of_pos (boundedScalarScale_pos fun _ => (certificate.input : ℝ))]
      exact boundedScalarScale_le_three _)
    (by exact_mod_cast hvalid.2.2.2.1))

def SinCosRationalIntervalCertificate.boundedScalarScaledMomentum
    (certificate : SinCosRationalIntervalCertificate) (momentum : ℚ) : ℚ :=
  (2 + certificate.computedSin) * momentum

def SinCosRationalIntervalCertificate.boundedScalarScaledMomentumError
    (certificate : SinCosRationalIntervalCertificate) (momentum : ℚ) : ℚ :=
  certificate.sinError * |momentum|

/-- The checked sine radius propagates through multiplication by an exactly
represented momentum. -/
theorem SinCosRationalIntervalCertificate.boundedScalarScaledMomentum_approximates
    (certificate : SinCosRationalIntervalCertificate)
    (hvalid : certificate.Valid) (momentum : ℚ) :
    Approximates
      (certificate.boundedScalarScaledMomentum momentum : ℝ)
      (boundedScalarScale (fun _ => (certificate.input : ℝ)) * momentum)
      (certificate.boundedScalarScaledMomentumError momentum : ℝ) := by
  have hscale := certificate.boundedScalarScale_approximates hvalid
  have hmomentum : Approximates (momentum : ℝ) (momentum : ℝ) 0 :=
    Approximates.refl _
  simpa [boundedScalarScaledMomentum, boundedScalarScaledMomentumError,
    mul_comm] using hscale.mul hmomentum

def SinCosRationalIntervalCertificate.boundedScalarRadicandError
    (certificate : SinCosRationalIntervalCertificate) (momentum : ℚ) : ℚ :=
  let error := certificate.boundedScalarScaledMomentumError momentum
  error * (2 * |certificate.boundedScalarScaledMomentum momentum| + error)

/-- The checked sine radius propagates through scaled momentum, squaring, and
addition of one to give a fully rational radicand error. -/
theorem SinCosRationalIntervalCertificate.boundedScalarRadicand_approximates
    (certificate : SinCosRationalIntervalCertificate)
    (hvalid : certificate.Valid) (momentum : ℚ) :
    Approximates
      (1 + (certificate.boundedScalarScaledMomentum momentum : ℝ) ^ 2)
      (1 + (boundedScalarScale (fun _ => (certificate.input : ℝ)) *
        (momentum : ℝ)) ^ 2)
      (certificate.boundedScalarRadicandError momentum : ℝ) := by
  have hscaled' : Approximates
      (certificate.boundedScalarScaledMomentum momentum : ℝ)
      (boundedScalarScale (fun _ => (certificate.input : ℝ)) * momentum)
      (certificate.boundedScalarScaledMomentumError momentum : ℝ) :=
    certificate.boundedScalarScaledMomentum_approximates hvalid momentum
  have hsquare := hscaled'.mul hscaled'
  simp only [pow_two]
  apply ((Approximates.refl (1 : ℝ)).add hsquare).mono
  have hidealAbs :
      |boundedScalarScale (fun _ => (certificate.input : ℝ)) * (momentum : ℝ)| ≤
        |(certificate.boundedScalarScaledMomentum momentum : ℝ)| +
          certificate.boundedScalarScaledMomentumError momentum := by
    have := hscaled'
    unfold Approximates at this
    calc
      _ = |(certificate.boundedScalarScaledMomentum momentum : ℝ) +
          (boundedScalarScale (fun _ => (certificate.input : ℝ)) * momentum -
            certificate.boundedScalarScaledMomentum momentum)| := by
        congr 1
        ring
      _ ≤ |(certificate.boundedScalarScaledMomentum momentum : ℝ)| +
          |boundedScalarScale (fun _ => (certificate.input : ℝ)) * momentum -
            certificate.boundedScalarScaledMomentum momentum| := abs_add_le _ _
      _ = |(certificate.boundedScalarScaledMomentum momentum : ℝ)| +
          |(certificate.boundedScalarScaledMomentum momentum : ℝ) -
            boundedScalarScale (fun _ => (certificate.input : ℝ)) * momentum| := by
        rw [abs_sub_comm]
      _ ≤ _ := add_le_add (le_refl _) this
  have herrorNonneg : (0 : ℝ) ≤
      certificate.boundedScalarScaledMomentumError momentum := by
    exact_mod_cast mul_nonneg hvalid.2.1 (abs_nonneg momentum)
  rw [show (certificate.boundedScalarRadicandError momentum : ℝ) =
      (certificate.boundedScalarScaledMomentumError momentum : ℝ) *
        (2 * |(certificate.boundedScalarScaledMomentum momentum : ℝ)| +
          certificate.boundedScalarScaledMomentumError momentum) by
    norm_num [boundedScalarRadicandError, Rat.cast_abs]]
  calc
    (0 + ((certificate.boundedScalarScaledMomentumError momentum : ℝ) *
        |(certificate.boundedScalarScaledMomentum momentum : ℝ)| +
      |boundedScalarScale (fun _ => (certificate.input : ℝ)) * momentum| *
        certificate.boundedScalarScaledMomentumError momentum)) ≤
      certificate.boundedScalarScaledMomentumError momentum *
        |(certificate.boundedScalarScaledMomentum momentum : ℝ)| +
      (|(certificate.boundedScalarScaledMomentum momentum : ℝ)| +
        certificate.boundedScalarScaledMomentumError momentum) *
        certificate.boundedScalarScaledMomentumError momentum := by
          have hmul := mul_le_mul_of_nonneg_right hidealAbs herrorNonneg
          nlinarith
    _ = (certificate.boundedScalarScaledMomentumError momentum : ℝ) *
        (2 * |(certificate.boundedScalarScaledMomentum momentum : ℝ)| +
          certificate.boundedScalarScaledMomentumError momentum) := by ring

/-- One observed evaluation of the nonlinear primitives shared by both
bounded-scalar generalized-leapfrog callbacks. Every field is rational, so
the checker validates the actual rounded radicand, square root, and reciprocal
without assuming a platform-wide floating-point or `libm` model. -/
structure BoundedScalarPrimitiveRationalCertificate where
  sincos : SinCosRationalIntervalCertificate
  momentum : ℚ
  computedRadicand : ℚ
  radicandArithmeticError : ℚ
  sqrtCertificate : SqrtRationalIntervalCertificate
  reciprocalCertificate : ReciprocalRationalResidualCertificate
  computedSqrtLower : ℚ
deriving DecidableEq, Repr

namespace BoundedScalarPrimitiveRationalCertificate

def radicandError (certificate : BoundedScalarPrimitiveRationalCertificate) : ℚ :=
  certificate.radicandArithmeticError +
    certificate.sincos.boundedScalarRadicandError certificate.momentum

def sqrtError (certificate : BoundedScalarPrimitiveRationalCertificate) : ℚ :=
  certificate.sqrtCertificate.error + certificate.radicandError / 2

def reciprocalError
    (certificate : BoundedScalarPrimitiveRationalCertificate) : ℚ :=
  certificate.reciprocalCertificate.error +
    certificate.sqrtError / certificate.computedSqrtLower

def Valid (certificate : BoundedScalarPrimitiveRationalCertificate) : Prop :=
  certificate.sincos.Valid ∧
    0 ≤ certificate.radicandArithmeticError ∧
    certificate.radicandArithmeticError =
      |certificate.computedRadicand -
        (1 + certificate.sincos.boundedScalarScaledMomentum
          certificate.momentum ^ 2)| ∧
    1 ≤ certificate.computedRadicand ∧
    certificate.sqrtCertificate.Valid ∧
    certificate.sqrtCertificate.input = certificate.computedRadicand ∧
    certificate.reciprocalCertificate.Valid ∧
    certificate.reciprocalCertificate.input = certificate.sqrtCertificate.computed ∧
    0 < certificate.computedSqrtLower ∧
    certificate.computedSqrtLower ≤
      certificate.sqrtCertificate.computed - certificate.sqrtCertificate.error

instance (certificate : BoundedScalarPrimitiveRationalCertificate) :
    Decidable certificate.Valid := by
  unfold Valid
  infer_instance

def check (certificate : BoundedScalarPrimitiveRationalCertificate) : Bool :=
  decide certificate.Valid

@[simp] theorem check_eq_true_iff
    (certificate : BoundedScalarPrimitiveRationalCertificate) :
    certificate.check = true ↔ certificate.Valid := by
  simp [check]

theorem computedRadicand_approximates
    (certificate : BoundedScalarPrimitiveRationalCertificate)
    (hvalid : certificate.Valid) :
    Approximates (certificate.computedRadicand : ℝ)
      (1 + (boundedScalarScale
        (fun _ => (certificate.sincos.input : ℝ)) *
          (certificate.momentum : ℝ)) ^ 2)
      (certificate.radicandError : ℝ) := by
  have harithmetic : Approximates (certificate.computedRadicand : ℝ)
      (1 + (certificate.sincos.boundedScalarScaledMomentum
        certificate.momentum : ℝ) ^ 2)
      (certificate.radicandArithmeticError : ℝ) := by
    rw [Approximates]
    exact_mod_cast hvalid.2.2.1.symm.le
  simpa [radicandError] using harithmetic.trans
    (certificate.sincos.boundedScalarRadicand_approximates hvalid.1
      certificate.momentum)

theorem computedSqrt_approximates
    (certificate : BoundedScalarPrimitiveRationalCertificate)
    (hvalid : certificate.Valid) :
    Approximates (certificate.sqrtCertificate.computed : ℝ)
      (Real.sqrt (1 + (boundedScalarScale
        (fun _ => (certificate.sincos.input : ℝ)) *
          (certificate.momentum : ℝ)) ^ 2))
      (certificate.sqrtError : ℝ) := by
  have hlocal : Approximates (certificate.sqrtCertificate.computed : ℝ)
      (Real.sqrt (certificate.computedRadicand : ℝ))
      (certificate.sqrtCertificate.error : ℝ) := by
    simpa [hvalid.2.2.2.2.2.1] using
      certificate.sqrtCertificate.approximates hvalid.2.2.2.2.1
  have hradicand := certificate.computedRadicand_approximates hvalid
  have hcomputed : (0 : ℝ) < certificate.computedRadicand := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1) hvalid.2.2.2.1
  have hideal : (0 : ℝ) < 1 +
      (boundedScalarScale (fun _ => (certificate.sincos.input : ℝ)) *
        (certificate.momentum : ℝ)) ^ 2 := by positivity
  have hraw := sqrt_backend_approximates hlocal hradicand hcomputed hideal
  apply hraw.mono
  have hcomputedRoot : (1 : ℝ) ≤
      Real.sqrt certificate.computedRadicand := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    exact_mod_cast hvalid.2.2.2.1
  have hidealRoot : (1 : ℝ) ≤ Real.sqrt
      (1 + (boundedScalarScale
        (fun _ => (certificate.sincos.input : ℝ)) *
          (certificate.momentum : ℝ)) ^ 2) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith [sq_nonneg (boundedScalarScale
      (fun _ => (certificate.sincos.input : ℝ)) * certificate.momentum)]
  have hdenom : (2 : ℝ) ≤
      Real.sqrt certificate.computedRadicand +
        Real.sqrt (1 + (boundedScalarScale
          (fun _ => (certificate.sincos.input : ℝ)) *
            (certificate.momentum : ℝ)) ^ 2) := by
    linarith
  have herror : (0 : ℝ) ≤ certificate.radicandError := by
    exact (certificate.computedRadicand_approximates hvalid).nonneg
  rw [show (certificate.sqrtError : ℝ) =
      (certificate.sqrtCertificate.error : ℝ) + certificate.radicandError / 2 by
    norm_num [sqrtError]]
  gcongr

theorem reciprocal_approximates
    (certificate : BoundedScalarPrimitiveRationalCertificate)
    (hvalid : certificate.Valid) :
    Approximates (certificate.reciprocalCertificate.computed : ℝ)
      (Real.sqrt (1 + (boundedScalarScale
        (fun _ => (certificate.sincos.input : ℝ)) *
          (certificate.momentum : ℝ)) ^ 2))⁻¹
      (certificate.reciprocalError : ℝ) := by
  have hsqrt := certificate.computedSqrt_approximates hvalid
  have hlocal : Approximates (certificate.reciprocalCertificate.computed : ℝ)
      (certificate.sqrtCertificate.computed : ℝ)⁻¹
      (certificate.reciprocalCertificate.error : ℝ) := by
    simpa [hvalid.2.2.2.2.2.2.2.1] using
      certificate.reciprocalCertificate.approximates hvalid.2.2.2.2.2.2.1
  have hlower : (0 : ℝ) < certificate.computedSqrtLower := by
    exact_mod_cast hvalid.2.2.2.2.2.2.2.2.1
  have hcomputedPositive : (0 : ℝ) < certificate.sqrtCertificate.computed := by
    have hle : (certificate.computedSqrtLower : ℝ) ≤
        certificate.sqrtCertificate.computed - certificate.sqrtCertificate.error := by
      exact_mod_cast hvalid.2.2.2.2.2.2.2.2.2
    have herror : (0 : ℝ) ≤ certificate.sqrtCertificate.error := by
      exact_mod_cast hvalid.2.2.2.2.1.2.1
    linarith
  have hidealPositive : (0 : ℝ) < Real.sqrt
      (1 + (boundedScalarScale
        (fun _ => (certificate.sincos.input : ℝ)) *
          (certificate.momentum : ℝ)) ^ 2) := by
    positivity
  have hraw := hlocal.trans (inv_approximates_inv hcomputedPositive.ne'
    hidealPositive.ne' hsqrt)
  apply hraw.mono
  have hidealLower : (1 : ℝ) ≤ Real.sqrt
      (1 + (boundedScalarScale
        (fun _ => (certificate.sincos.input : ℝ)) *
          (certificate.momentum : ℝ)) ^ 2) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith [sq_nonneg (boundedScalarScale
      (fun _ => (certificate.sincos.input : ℝ)) * certificate.momentum)]
  have hcomputedLower : (certificate.computedSqrtLower : ℝ) ≤
      |(certificate.sqrtCertificate.computed : ℝ)| := by
    rw [abs_of_pos hcomputedPositive]
    have hle : (certificate.computedSqrtLower : ℝ) ≤
        certificate.sqrtCertificate.computed - certificate.sqrtCertificate.error := by
      exact_mod_cast hvalid.2.2.2.2.2.2.2.2.2
    have herror : (0 : ℝ) ≤ certificate.sqrtCertificate.error := by
      exact_mod_cast hvalid.2.2.2.2.1.2.1
    linarith
  have hdenom : (certificate.computedSqrtLower : ℝ) ≤
      |(certificate.sqrtCertificate.computed : ℝ)| *
        |Real.sqrt (1 + (boundedScalarScale
          (fun _ => (certificate.sincos.input : ℝ)) *
            (certificate.momentum : ℝ)) ^ 2)| := by
    rw [abs_of_pos hidealPositive]
    nlinarith
  have hsqrtError : (0 : ℝ) ≤ certificate.sqrtError := hsqrt.nonneg
  rw [show (certificate.reciprocalError : ℝ) =
      (certificate.reciprocalCertificate.error : ℝ) +
        certificate.sqrtError / certificate.computedSqrtLower by
    norm_num [reciprocalError]]
  gcongr

end BoundedScalarPrimitiveRationalCertificate

/-- Complete checked records for one evaluation of both scalar callbacks used
by the bounded position-dependent generalized-leapfrog solver. The final two
residuals cover the concrete rounded multiplication/division order; all
analytic primitive error is derived from the nested certificate. -/
structure BoundedScalarCallbackRationalCertificate where
  primitive : BoundedScalarPrimitiveRationalCertificate
  computedMomentumCallback : ℚ
  momentumArithmeticError : ℚ
  computedPositionCallback : ℚ
  positionArithmeticError : ℚ
deriving DecidableEq, Repr

namespace BoundedScalarCallbackRationalCertificate

def scaleMomentumError
    (certificate : BoundedScalarCallbackRationalCertificate) : ℚ :=
  certificate.primitive.sincos.sinError *
      |certificate.primitive.sincos.boundedScalarScaledMomentum
        certificate.primitive.momentum| +
    3 * certificate.primitive.sincos.boundedScalarScaledMomentumError
      certificate.primitive.momentum

def momentumSemanticError
    (certificate : BoundedScalarCallbackRationalCertificate) : ℚ :=
  certificate.scaleMomentumError *
      |certificate.primitive.reciprocalCertificate.computed| +
    3 * (|certificate.primitive.sincos.boundedScalarScaledMomentum
      certificate.primitive.momentum| +
        certificate.primitive.sincos.boundedScalarScaledMomentumError
          certificate.primitive.momentum) *
      certificate.primitive.reciprocalError

def momentumError
    (certificate : BoundedScalarCallbackRationalCertificate) : ℚ :=
  certificate.momentumArithmeticError + certificate.momentumSemanticError

def scaleCosError
    (certificate : BoundedScalarCallbackRationalCertificate) : ℚ :=
  certificate.primitive.sincos.sinError *
      |certificate.primitive.sincos.computedCos| +
    3 * certificate.primitive.sincos.cosError

def positionSemanticError
    (certificate : BoundedScalarCallbackRationalCertificate) : ℚ :=
  certificate.scaleCosError * |certificate.primitive.momentum ^ 2| *
      |certificate.primitive.reciprocalCertificate.computed| +
    3 * |certificate.primitive.momentum ^ 2| *
      certificate.primitive.reciprocalError

def positionError
    (certificate : BoundedScalarCallbackRationalCertificate) : ℚ :=
  certificate.positionArithmeticError + certificate.positionSemanticError

def Valid (certificate : BoundedScalarCallbackRationalCertificate) : Prop :=
  certificate.primitive.Valid ∧
    0 ≤ certificate.momentumArithmeticError ∧
    certificate.momentumArithmeticError =
      |certificate.computedMomentumCallback -
        ((2 + certificate.primitive.sincos.computedSin) *
          certificate.primitive.sincos.boundedScalarScaledMomentum
            certificate.primitive.momentum *
          certificate.primitive.reciprocalCertificate.computed)| ∧
    0 ≤ certificate.positionArithmeticError ∧
    certificate.positionArithmeticError =
      |certificate.computedPositionCallback -
        ((2 + certificate.primitive.sincos.computedSin) *
          certificate.primitive.sincos.computedCos *
          certificate.primitive.momentum ^ 2 *
          certificate.primitive.reciprocalCertificate.computed)|

instance (certificate : BoundedScalarCallbackRationalCertificate) :
    Decidable certificate.Valid := by
  unfold Valid
  infer_instance

def check (certificate : BoundedScalarCallbackRationalCertificate) : Bool :=
  decide certificate.Valid

@[simp] theorem check_eq_true_iff
    (certificate : BoundedScalarCallbackRationalCertificate) :
    certificate.check = true ↔ certificate.Valid := by
  simp [check]

theorem momentum_approximates
    (certificate : BoundedScalarCallbackRationalCertificate)
    (hvalid : certificate.Valid) :
    Approximates (certificate.computedMomentumCallback : ℝ)
      (boundedScalarMomentumDerivativeReal
        (certificate.primitive.sincos.input, certificate.primitive.momentum))
      (certificate.momentumError : ℝ) := by
  let scaleHat : ℝ := 2 + certificate.primitive.sincos.computedSin
  let transformedHat : ℝ :=
    certificate.primitive.sincos.boundedScalarScaledMomentum
      certificate.primitive.momentum
  let inverseHat : ℝ := certificate.primitive.reciprocalCertificate.computed
  let scale : ℝ := boundedScalarScale
    (fun _ => (certificate.primitive.sincos.input : ℝ))
  let transformed : ℝ := scale * certificate.primitive.momentum
  let inverse : ℝ := (Real.sqrt (1 + transformed ^ 2))⁻¹
  have hscale := certificate.primitive.sincos.boundedScalarScale_approximates
    hvalid.1.1
  have htransformed :=
    certificate.primitive.sincos.boundedScalarScaledMomentum_approximates
      hvalid.1.1 certificate.primitive.momentum
  have hinverse := certificate.primitive.reciprocal_approximates hvalid.1
  have hscaleTransformedRaw := hscale.mul htransformed
  have hscaleTransformed : Approximates (scaleHat * transformedHat)
      (scale * transformed) (certificate.scaleMomentumError : ℝ) := by
    apply hscaleTransformedRaw.mono
    have hscaleAbs : |scale| ≤ 3 := by
      rw [abs_of_pos (boundedScalarScale_pos _)]
      exact boundedScalarScale_le_three _
    rw [show (certificate.scaleMomentumError : ℝ) =
        (certificate.primitive.sincos.sinError : ℝ) *
            |(certificate.primitive.sincos.boundedScalarScaledMomentum
              certificate.primitive.momentum : ℝ)| +
          3 * certificate.primitive.sincos.boundedScalarScaledMomentumError
            certificate.primitive.momentum by
      norm_num [scaleMomentumError]]
    have htransformedError : (0 : ℝ) ≤
        certificate.primitive.sincos.boundedScalarScaledMomentumError
          certificate.primitive.momentum := htransformed.nonneg
    gcongr
  have htransformedAbs : |transformed| ≤ |transformedHat| +
      certificate.primitive.sincos.boundedScalarScaledMomentumError
        certificate.primitive.momentum := by
    have h := htransformed
    unfold Approximates at h
    calc
      |transformed| = |transformedHat + (transformed - transformedHat)| := by
        congr 1
        ring
      _ ≤ |transformedHat| + |transformed - transformedHat| := abs_add_le _ _
      _ = |transformedHat| + |transformedHat - transformed| := by
        rw [abs_sub_comm]
      _ ≤ _ := add_le_add le_rfl h
  have hscaleTransformedAbs : |scale * transformed| ≤
      3 * (|transformedHat| +
        certificate.primitive.sincos.boundedScalarScaledMomentumError
          certificate.primitive.momentum) := by
    rw [abs_mul, abs_of_pos (boundedScalarScale_pos _)]
    exact mul_le_mul (boundedScalarScale_le_three _) htransformedAbs
      (abs_nonneg _) (by norm_num)
  have hsemanticRaw := hscaleTransformed.mul hinverse
  have hsemantic : Approximates
      (scaleHat * transformedHat * inverseHat)
      (scale * transformed * inverse)
      (certificate.momentumSemanticError : ℝ) := by
    apply hsemanticRaw.mono
    rw [show (certificate.momentumSemanticError : ℝ) =
        (certificate.scaleMomentumError : ℝ) *
            |(certificate.primitive.reciprocalCertificate.computed : ℝ)| +
          3 * (|(certificate.primitive.sincos.boundedScalarScaledMomentum
            certificate.primitive.momentum : ℝ)| +
              certificate.primitive.sincos.boundedScalarScaledMomentumError
                certificate.primitive.momentum) *
            certificate.primitive.reciprocalError by
      norm_num [momentumSemanticError]]
    exact add_le_add le_rfl
      (mul_le_mul_of_nonneg_right hscaleTransformedAbs hinverse.nonneg)
  have harithmetic : Approximates
      (certificate.computedMomentumCallback : ℝ)
      (scaleHat * transformedHat * inverseHat)
      (certificate.momentumArithmeticError : ℝ) := by
    rw [Approximates]
    simpa [scaleHat, transformedHat, inverseHat] using
      (show |(certificate.computedMomentumCallback : ℝ) -
          (((2 + certificate.primitive.sincos.computedSin : ℚ) : ℝ) *
            (certificate.primitive.sincos.boundedScalarScaledMomentum
              certificate.primitive.momentum : ℝ) *
            (certificate.primitive.reciprocalCertificate.computed : ℝ))| ≤
          (certificate.momentumArithmeticError : ℝ) by
        exact_mod_cast hvalid.2.2.1.symm.le)
  have htotal := harithmetic.trans hsemantic
  have hideal : scale * transformed * inverse =
      boundedScalarMomentumDerivativeReal
        (certificate.primitive.sincos.input, certificate.primitive.momentum) := by
    simp only [scale, transformed, inverse, boundedScalarMomentumDerivativeReal,
      scaledVelocityProfile, scalarVelocityProfile, scalarRelativisticProfile,
      boundedScalarScale, div_eq_mul_inv]
    ring
  rw [hideal] at htotal
  simpa only [momentumError, Rat.cast_add] using htotal

theorem position_approximates
    (certificate : BoundedScalarCallbackRationalCertificate)
    (hvalid : certificate.Valid) :
    Approximates (certificate.computedPositionCallback : ℝ)
      (boundedScalarPositionDerivativeReal
        (certificate.primitive.sincos.input, certificate.primitive.momentum))
      (certificate.positionError : ℝ) := by
  let scaleCosHat : ℝ :=
    (2 + certificate.primitive.sincos.computedSin) *
      certificate.primitive.sincos.computedCos
  let momentumSquare : ℝ := (certificate.primitive.momentum : ℝ) ^ 2
  let inverseHat : ℝ := certificate.primitive.reciprocalCertificate.computed
  let scale : ℝ := boundedScalarScale
    (fun _ => (certificate.primitive.sincos.input : ℝ))
  let scaleCos : ℝ := scale * Real.cos certificate.primitive.sincos.input
  let inverse : ℝ := (Real.sqrt
    (1 + (scale * (certificate.primitive.momentum : ℝ)) ^ 2))⁻¹
  have hscaleCos :=
    certificate.primitive.sincos.boundedScalarScaleCos_approximates hvalid.1.1
  have hmomentumSquare : Approximates momentumSquare momentumSquare 0 :=
    Approximates.refl _
  have hinverse := certificate.primitive.reciprocal_approximates hvalid.1
  have hscaleCosMomentumRaw := hscaleCos.mul hmomentumSquare
  have hscaleCosMomentum : Approximates
      (scaleCosHat * momentumSquare) (scaleCos * momentumSquare)
      ((certificate.scaleCosError : ℝ) * |momentumSquare|) := by
    simpa [scaleCosHat, scaleCos, scale, scaleCosError] using
      hscaleCosMomentumRaw
  have hscaleCosAbs : |scaleCos| ≤ 3 := by
    dsimp only [scaleCos, scale]
    rw [abs_mul, abs_of_pos (boundedScalarScale_pos _)]
    calc
      boundedScalarScale (fun _ => (certificate.primitive.sincos.input : ℝ)) *
          |Real.cos certificate.primitive.sincos.input| ≤
          boundedScalarScale (fun _ => (certificate.primitive.sincos.input : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
          (boundedScalarScale_pos _).le
      _ ≤ 3 := by
        simpa using (boundedScalarScale_le_three
          (fun _ => (certificate.primitive.sincos.input : ℝ)))
  have hscaleCosMomentumAbs : |scaleCos * momentumSquare| ≤
      3 * |momentumSquare| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hscaleCosAbs (abs_nonneg _)
  have hsemanticRaw : Approximates
      (scaleCosHat * momentumSquare * inverseHat)
      (scaleCos * momentumSquare * inverse)
      ((certificate.scaleCosError : ℝ) * |momentumSquare| * |inverseHat| +
        |scaleCos * momentumSquare| * certificate.primitive.reciprocalError) := by
    simpa only [inverseHat, inverse, scale] using hscaleCosMomentum.mul hinverse
  have hsemantic : Approximates
      (scaleCosHat * momentumSquare * inverseHat)
      (scaleCos * momentumSquare * inverse)
      (certificate.positionSemanticError : ℝ) := by
    apply hsemanticRaw.mono
    rw [show (certificate.positionSemanticError : ℝ) =
        (certificate.scaleCosError : ℝ) * |momentumSquare| *
            |(certificate.primitive.reciprocalCertificate.computed : ℝ)| +
          3 * |momentumSquare| * certificate.primitive.reciprocalError by
      norm_num [positionSemanticError, momentumSquare]]
    exact add_le_add le_rfl
      (mul_le_mul_of_nonneg_right hscaleCosMomentumAbs hinverse.nonneg)
  have harithmetic : Approximates
      (certificate.computedPositionCallback : ℝ)
      (scaleCosHat * momentumSquare * inverseHat)
      (certificate.positionArithmeticError : ℝ) := by
    rw [Approximates]
    simpa [scaleCosHat, momentumSquare, inverseHat] using
      (show |(certificate.computedPositionCallback : ℝ) -
          (((2 + certificate.primitive.sincos.computedSin : ℚ) : ℝ) *
            (certificate.primitive.sincos.computedCos : ℝ) *
            ((certificate.primitive.momentum ^ 2 : ℚ) : ℝ) *
            (certificate.primitive.reciprocalCertificate.computed : ℝ))| ≤
          (certificate.positionArithmeticError : ℝ) by
        exact_mod_cast hvalid.2.2.2.2.symm.le)
  have htotal := harithmetic.trans hsemantic
  have hideal : scaleCos * momentumSquare * inverse =
      boundedScalarPositionDerivativeReal
        (certificate.primitive.sincos.input, certificate.primitive.momentum) := by
    have hscaleNe : (2 + Real.sin (certificate.primitive.sincos.input : ℝ)) ≠ 0 := by
      have := Real.neg_one_le_sin (certificate.primitive.sincos.input : ℝ)
      linarith
    have hrootNe : Real.sqrt (1 +
        ((2 + Real.sin (certificate.primitive.sincos.input : ℝ)) *
          (certificate.primitive.momentum : ℝ)) ^ 2) ≠ 0 := by
      positivity
    simp only [scaleCos, momentumSquare, inverse, scale,
      boundedScalarPositionDerivativeReal, scalarPositionProfile,
      scalarRelativisticProfile, boundedScalarScale, div_eq_mul_inv]
    field_simp [hscaleNe, hrootNe]
  rw [hideal] at htotal
  simpa only [positionError, Rat.cast_add] using htotal

end BoundedScalarCallbackRationalCertificate

/-- Which exact derivative is represented by one ordered runtime callback
entry. -/
inductive BoundedScalarCallbackKind where
  | position
  | momentum
deriving DecidableEq, Repr

/-- One ordered callback entry. The nested certificate contains both derived
values, while `kind` selects the value that the runtime actually consumed. -/
structure BoundedScalarCallbackTraceEntry where
  kind : BoundedScalarCallbackKind
  certificate : BoundedScalarCallbackRationalCertificate
deriving DecidableEq, Repr

namespace BoundedScalarCallbackTraceEntry

def Valid (entry : BoundedScalarCallbackTraceEntry) : Prop :=
  entry.certificate.Valid

instance (entry : BoundedScalarCallbackTraceEntry) : Decidable entry.Valid :=
  inferInstanceAs (Decidable entry.certificate.Valid)

def computedRat (entry : BoundedScalarCallbackTraceEntry) : ℚ :=
  match entry.kind with
  | .position => entry.certificate.computedPositionCallback
  | .momentum => entry.certificate.computedMomentumCallback

def computed (entry : BoundedScalarCallbackTraceEntry) : ℝ :=
  entry.computedRat

noncomputable def ideal (entry : BoundedScalarCallbackTraceEntry) : ℝ :=
  match entry.kind with
  | .position => boundedScalarPositionDerivativeReal
      (entry.certificate.primitive.sincos.input,
        entry.certificate.primitive.momentum)
  | .momentum => boundedScalarMomentumDerivativeReal
      (entry.certificate.primitive.sincos.input,
        entry.certificate.primitive.momentum)

def errorRat (entry : BoundedScalarCallbackTraceEntry) : ℚ :=
  match entry.kind with
  | .position => entry.certificate.positionError
  | .momentum => entry.certificate.momentumError

def error (entry : BoundedScalarCallbackTraceEntry) : ℝ :=
  entry.errorRat

theorem approximates (entry : BoundedScalarCallbackTraceEntry)
    (hvalid : entry.Valid) :
    Approximates entry.computed entry.ideal entry.error := by
  rcases entry with ⟨kind, certificate⟩
  cases kind with
  | position =>
      exact certificate.position_approximates hvalid
  | momentum =>
      exact certificate.momentum_approximates hvalid

/-- A one-callback momentum update inherits the callback entry's proved error
and the rounded affine certificate's exact arithmetic residual. -/
theorem affineUpdate_le
    (entry : BoundedScalarCallbackTraceEntry) (hentry : entry.Valid)
    (affine : RoundedAffineUpdateRationalCertificate)
    (haffine : affine.Valid)
    (hcomputed : (affine.computedCallback : ℝ) = entry.computed)
    (herror : (affine.callbackError : ℝ) = entry.error) :
    |(affine.computedUpdate : ℝ) -
      (affine.base + affine.scale * entry.ideal)| ≤ affine.updateError := by
  apply affine.exactUpdate_le haffine entry.ideal
  rw [hcomputed, herror]
  exact entry.approximates hentry

/-- The implicit position update consumes the sum of its initial and terminal
momentum callbacks; their independently checked radii add. -/
theorem affineUpdatePair_le
    (first second : BoundedScalarCallbackTraceEntry)
    (hfirst : first.Valid) (hsecond : second.Valid)
    (affine : RoundedAffineUpdateRationalCertificate)
    (haffine : affine.Valid)
    (hcomputed : (affine.computedCallback : ℝ) =
      first.computed + second.computed)
    (herror : (affine.callbackError : ℝ) = first.error + second.error) :
    |(affine.computedUpdate : ℝ) -
      (affine.base + affine.scale * (first.ideal + second.ideal))| ≤
        affine.updateError := by
  apply affine.exactUpdate_le haffine (first.ideal + second.ideal)
  rw [hcomputed, herror]
  exact (first.approximates hfirst).add (second.approximates hsecond)

end BoundedScalarCallbackTraceEntry

/-- Callback provenance for one scalar affine update. Momentum kicks consume
one derivative; implicit position updates consume the sum of two velocities. -/
inductive BoundedScalarAffineCallbackSources where
  | one (entry : BoundedScalarCallbackTraceEntry)
  | pair (first second : BoundedScalarCallbackTraceEntry)
deriving DecidableEq, Repr

namespace BoundedScalarAffineCallbackSources

def Valid (sources : BoundedScalarAffineCallbackSources) : Prop :=
  match sources with
  | .one entry => entry.Valid
  | .pair first second => first.Valid ∧ second.Valid

instance (sources : BoundedScalarAffineCallbackSources) :
    Decidable sources.Valid := by
  cases sources <;> simp only [Valid] <;> infer_instance

def computed (sources : BoundedScalarAffineCallbackSources) : ℚ :=
  match sources with
  | .one entry => entry.computedRat
  | .pair first second => first.computedRat + second.computedRat

def error (sources : BoundedScalarAffineCallbackSources) : ℚ :=
  match sources with
  | .one entry => entry.errorRat
  | .pair first second => first.errorRat + second.errorRat

noncomputable def ideal (sources : BoundedScalarAffineCallbackSources) : ℝ :=
  match sources with
  | .one entry => entry.ideal
  | .pair first second => first.ideal + second.ideal

theorem approximates (sources : BoundedScalarAffineCallbackSources)
    (hvalid : sources.Valid) :
    Approximates (sources.computed : ℝ) sources.ideal sources.error := by
  cases sources with
  | one entry => exact entry.approximates hvalid
  | pair first second =>
      simpa [computed, error, ideal, BoundedScalarCallbackTraceEntry.computed,
        BoundedScalarCallbackTraceEntry.error] using
        (first.approximates hvalid.1).add
          (second.approximates hvalid.2)

end BoundedScalarAffineCallbackSources

/-- Fully linked checker for one runtime affine update. Besides validating the
arithmetic residual, it requires the submitted callback center and radius to
be exactly those derived from the checked callback source(s). -/
structure BoundedScalarAffineUpdateRationalCertificate where
  sources : BoundedScalarAffineCallbackSources
  callbackArithmeticError : ℚ
  affine : RoundedAffineUpdateRationalCertificate
deriving DecidableEq, Repr

namespace BoundedScalarAffineUpdateRationalCertificate

def Valid (certificate : BoundedScalarAffineUpdateRationalCertificate) : Prop :=
  certificate.sources.Valid ∧ certificate.affine.Valid ∧
    0 ≤ certificate.callbackArithmeticError ∧
    certificate.callbackArithmeticError =
      |certificate.affine.computedCallback - certificate.sources.computed| ∧
    certificate.affine.callbackError =
      certificate.callbackArithmeticError + certificate.sources.error

instance (certificate : BoundedScalarAffineUpdateRationalCertificate) :
    Decidable certificate.Valid := by
  unfold Valid
  infer_instance

def check (certificate : BoundedScalarAffineUpdateRationalCertificate) : Bool :=
  decide certificate.Valid

@[simp] theorem check_eq_true_iff
    (certificate : BoundedScalarAffineUpdateRationalCertificate) :
    certificate.check = true ↔ certificate.Valid := by
  simp [check]

theorem exactUpdate_le
    (certificate : BoundedScalarAffineUpdateRationalCertificate)
    (hvalid : certificate.Valid) :
    |(certificate.affine.computedUpdate : ℝ) -
      (certificate.affine.base + certificate.affine.scale *
        certificate.sources.ideal)| ≤ certificate.affine.updateError := by
  apply certificate.affine.exactUpdate_le hvalid.2.1
    certificate.sources.ideal
  have hsources := certificate.sources.approximates hvalid.1
  have harithmetic : Approximates
      (certificate.affine.computedCallback : ℝ)
      (certificate.sources.computed : ℝ)
      (certificate.callbackArithmeticError : ℝ) := by
    rw [Approximates]
    exact_mod_cast hvalid.2.2.2.1.symm.le
  have htotal := harithmetic.trans hsources
  rw [Approximates] at htotal
  simpa [hvalid.2.2.2.2] using htotal

end BoundedScalarAffineUpdateRationalCertificate

/-- Scalar-coordinate half-momentum fixed-point map used by the maintained
bounded solver. -/
noncomputable def boundedScalarHalfUpdateReal
    (ε q p x : ℝ) : ℝ :=
  p - (ε / 2) * boundedScalarPositionDerivativeReal (q, x)

/-- Scalar-coordinate implicit-position fixed-point map. -/
noncomputable def boundedScalarPositionUpdateReal
    (ε q pHalf x : ℝ) : ℝ :=
  q + (ε / 2) *
    (boundedScalarMomentumDerivativeReal (q, pHalf) +
      boundedScalarMomentumDerivativeReal (x, pHalf))

theorem boundedScalarHalfUpdateReal_contracting
    (ε q p : ℝ) (hstep : |ε / 2| * 3 < 1) :
    ContractingWith (boundedScalarHalfRate ε)
      (boundedScalarHalfUpdateReal ε q p) := by
  constructor
  · exact hstep
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have hcallback :=
      (boundedScalarPositionDerivative_lipschitz_momentum (fun _ => q)).dist_le_mul
        (fun _ => x) (fun _ => y)
    rw [dist_eq_norm, norm_pi_unit, dist_eq_norm, norm_pi_unit] at hcallback
    change |boundedScalarPositionDerivativeReal (q, x) -
      boundedScalarPositionDerivativeReal (q, y)| ≤ 3 * |x - y| at hcallback
    rw [Real.dist_eq]
    change |(p - (ε / 2) * boundedScalarPositionDerivativeReal (q, x)) -
      (p - (ε / 2) * boundedScalarPositionDerivativeReal (q, y))| ≤
        |ε / 2| * 3 * |x - y|
    rw [show (p - (ε / 2) * boundedScalarPositionDerivativeReal (q, x)) -
        (p - (ε / 2) * boundedScalarPositionDerivativeReal (q, y)) =
      -(ε / 2) * (boundedScalarPositionDerivativeReal (q, x) -
        boundedScalarPositionDerivativeReal (q, y)) by ring,
      abs_mul, abs_neg]
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hcallback (abs_nonneg (ε / 2))

theorem boundedScalarPositionUpdateReal_contracting
    (ε q pHalf : ℝ) (hstep : |ε / 2| * 3 < 1) :
    ContractingWith (boundedScalarPositionRate ε)
      (boundedScalarPositionUpdateReal ε q pHalf) := by
  constructor
  · change |ε / 2| * 2 < 1
    nlinarith [abs_nonneg (ε / 2)]
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have hcallback :=
      (boundedScalarMomentumDerivative_lipschitz_position
        (fun _ => pHalf)).dist_le_mul (fun _ => x) (fun _ => y)
    rw [dist_eq_norm, norm_pi_unit, dist_eq_norm, norm_pi_unit] at hcallback
    change |boundedScalarMomentumDerivativeReal (x, pHalf) -
      boundedScalarMomentumDerivativeReal (y, pHalf)| ≤ 2 * |x - y| at hcallback
    rw [Real.dist_eq]
    change |(q + (ε / 2) *
        (boundedScalarMomentumDerivativeReal (q, pHalf) +
          boundedScalarMomentumDerivativeReal (x, pHalf))) -
      (q + (ε / 2) *
        (boundedScalarMomentumDerivativeReal (q, pHalf) +
          boundedScalarMomentumDerivativeReal (y, pHalf)))| ≤
        |ε / 2| * 2 * |x - y|
    rw [show (q + (ε / 2) *
          (boundedScalarMomentumDerivativeReal (q, pHalf) +
            boundedScalarMomentumDerivativeReal (x, pHalf))) -
        (q + (ε / 2) *
          (boundedScalarMomentumDerivativeReal (q, pHalf) +
            boundedScalarMomentumDerivativeReal (y, pHalf))) =
      (ε / 2) * (boundedScalarMomentumDerivativeReal (x, pHalf) -
        boundedScalarMomentumDerivativeReal (y, pHalf)) by ring,
      abs_mul]
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hcallback (abs_nonneg (ε / 2))

/-- Scalar-coordinate exact step selected by the same two Banach fixed points
used in the bounded solver certificate. This form makes sequential numerical
refinement independent of the `Unit → ℝ` phase-space encoding. -/
noncomputable def boundedScalarCertificateStepReal
    (ε : ℝ) (hstep : |ε / 2| * 3 < 1) (z : ℝ × ℝ) : ℝ × ℝ :=
  let pHalf := (boundedScalarHalfUpdateReal_contracting ε z.1 z.2 hstep).fixedPoint
    (boundedScalarHalfUpdateReal ε z.1 z.2)
  let qNext := (boundedScalarPositionUpdateReal_contracting ε z.1 pHalf hstep).fixedPoint
    (boundedScalarPositionUpdateReal ε z.1 pHalf)
  (qNext, pHalf - (ε / 2) *
    boundedScalarPositionDerivativeReal (qNext, pHalf))

/-- The scalar certificate map is the established exact bounded GR-HMC step,
not a parallel numerical semantics. -/
theorem boundedScalarCertificateStepReal_eq_boundedScalarStepReal
    (ε : ℝ) (hstep : |ε / 2| * 3 < 1) :
    boundedScalarCertificateStepReal ε hstep =
      boundedScalarStepReal ε hstep := by
  funext z
  let solver := boundedScalarContractiveSolverAt ε hstep
  have hp := (solver.satisfies (boundedScalarPhaseOfReal z)).1
  have hq := (solver.satisfies (boundedScalarPhaseOfReal z)).2.1
  have hpFixed : Function.IsFixedPt (boundedScalarHalfUpdateReal ε z.1 z.2)
      (solver.halfMomentum (boundedScalarPhaseOfReal z) Unit.unit) := by
    simpa [Function.IsFixedPt, boundedScalarHalfUpdateReal,
      boundedScalarPositionDerivativeReal, boundedScalarPositionDerivative,
      boundedScalarPhaseOfReal, boundedScalarScale, scalarPositionProfile] using
        (congrFun hp Unit.unit).symm
  have hpEq := (boundedScalarHalfUpdateReal_contracting ε z.1 z.2 hstep).fixedPoint_unique
    hpFixed
  let pSelected :=
    (boundedScalarHalfUpdateReal_contracting ε z.1 z.2 hstep).fixedPoint
      (boundedScalarHalfUpdateReal ε z.1 z.2)
  have hqFixed : Function.IsFixedPt
      (boundedScalarPositionUpdateReal ε z.1 pSelected)
      ((solver.step (boundedScalarPhaseOfReal z)).1 Unit.unit) := by
    simpa [Function.IsFixedPt, boundedScalarPositionUpdateReal,
      boundedScalarMomentumDerivativeReal, boundedScalarMomentumDerivative,
      boundedScalarPhaseOfReal, boundedScalarScale, scaledVelocityProfile,
      pSelected, ← hpEq, mul_add] using (congrFun hq Unit.unit).symm
  let qSelected := (boundedScalarPositionUpdateReal_contracting ε z.1 pSelected
    hstep).fixedPoint (boundedScalarPositionUpdateReal ε z.1 pSelected)
  have hqEq : (solver.step (boundedScalarPhaseOfReal z)).1 Unit.unit =
      qSelected := (boundedScalarPositionUpdateReal_contracting ε z.1 pSelected
    hstep).fixedPoint_unique hqFixed
  apply Prod.ext
  · change qSelected = solver.nextPosition (boundedScalarPhaseOfReal z) Unit.unit
    change qSelected = (solver.step (boundedScalarPhaseOfReal z)).1 Unit.unit
    exact hqEq.symm
  · change pSelected - (ε / 2) *
        boundedScalarPositionDerivativeReal (qSelected, pSelected) =
      solver.halfMomentum (boundedScalarPhaseOfReal z) Unit.unit -
        (ε / 2) * boundedScalarPositionDerivativeReal
          (solver.nextPosition (boundedScalarPhaseOfReal z) Unit.unit,
            solver.halfMomentum (boundedScalarPhaseOfReal z) Unit.unit)
    rw [show pSelected = solver.halfMomentum (boundedScalarPhaseOfReal z)
      Unit.unit from hpEq.symm]
    rw [show qSelected = solver.nextPosition (boundedScalarPhaseOfReal z)
      Unit.unit by
        change qSelected = (solver.step (boundedScalarPhaseOfReal z)).1 Unit.unit
        exact hqEq.symm]

/-- Explicit input sensitivity of the first implicit solve. The position
coefficient is evaluated at the second exact half momentum; a later bounded-
region certificate can replace it by a rational upper bound. -/
theorem boundedScalarHalfFixedPoints_dist_le
    (ε q₁ p₁ q₂ p₂ : ℝ) (hstep : |ε / 2| * 3 < 1) :
    let x := (boundedScalarHalfUpdateReal_contracting ε q₁ p₁ hstep).fixedPoint
      (boundedScalarHalfUpdateReal ε q₁ p₁)
    let y := (boundedScalarHalfUpdateReal_contracting ε q₂ p₂ hstep).fixedPoint
      (boundedScalarHalfUpdateReal ε q₂ p₂)
    dist x y ≤
      (dist p₁ p₂ + |ε / 2| *
        (boundedScalarPositionDerivativePositionRate y : ℝ) * dist q₁ q₂) /
          (1 - |ε / 2| * 3) := by
  dsimp only
  let x := (boundedScalarHalfUpdateReal_contracting ε q₁ p₁ hstep).fixedPoint
    (boundedScalarHalfUpdateReal ε q₁ p₁)
  let y := (boundedScalarHalfUpdateReal_contracting ε q₂ p₂ hstep).fixedPoint
    (boundedScalarHalfUpdateReal ε q₂ p₂)
  change dist x y ≤ (dist p₁ p₂ + |ε / 2| *
    (boundedScalarPositionDerivativePositionRate y : ℝ) * dist q₁ q₂) /
      (1 - |ε / 2| * 3)
  have hx := (boundedScalarHalfUpdateReal_contracting ε q₁ p₁ hstep).fixedPoint_isFixedPt
  have hy := (boundedScalarHalfUpdateReal_contracting ε q₂ p₂ hstep).fixedPoint_isFixedPt
  have hmomentum := (boundedScalarPositionDerivativeReal_lipschitz_snd q₁).dist_le_mul
    x y
  have hposition := (boundedScalarPositionDerivativeReal_lipschitz_fst y).dist_le_mul
    q₁ q₂
  simp only [Real.dist_eq] at hmomentum hposition ⊢
  change |x - y| ≤ _
  have hraw : |x - y| ≤ |ε / 2| * 3 * |x - y| +
      (|p₁ - p₂| + |ε / 2| *
        (boundedScalarPositionDerivativePositionRate y : ℝ) * |q₁ - q₂|) := by
    have hxy : x - y =
        (boundedScalarHalfUpdateReal ε q₁ p₁ x -
          boundedScalarHalfUpdateReal ε q₁ p₁ y) +
        (boundedScalarHalfUpdateReal ε q₁ p₁ y -
          boundedScalarHalfUpdateReal ε q₂ p₂ y) := by rw [hx, hy]; ring
    calc
      _ = |boundedScalarHalfUpdateReal ε q₁ p₁ x -
            boundedScalarHalfUpdateReal ε q₁ p₁ y +
          (boundedScalarHalfUpdateReal ε q₁ p₁ y -
            boundedScalarHalfUpdateReal ε q₂ p₂ y)| := congrArg abs hxy
      _ ≤ |boundedScalarHalfUpdateReal ε q₁ p₁ x -
            boundedScalarHalfUpdateReal ε q₁ p₁ y| +
          |boundedScalarHalfUpdateReal ε q₁ p₁ y -
            boundedScalarHalfUpdateReal ε q₂ p₂ y| := abs_add_le _ _
      _ ≤ |ε / 2| * 3 * |x - y| +
          (|p₁ - p₂| + |ε / 2| *
            (boundedScalarPositionDerivativePositionRate y : ℝ) *
              |q₁ - q₂|) := by
        apply add_le_add
        · simp only [boundedScalarHalfUpdateReal]
          rw [show (p₁ - ε / 2 * boundedScalarPositionDerivativeReal (q₁, x)) -
                (p₁ - ε / 2 * boundedScalarPositionDerivativeReal (q₁, y)) =
              -(ε / 2) * (boundedScalarPositionDerivativeReal (q₁, x) -
                boundedScalarPositionDerivativeReal (q₁, y)) by ring,
            abs_mul, abs_neg]
          simpa [mul_assoc] using
            mul_le_mul_of_nonneg_left hmomentum (abs_nonneg (ε / 2))
        · rw [show boundedScalarHalfUpdateReal ε q₁ p₁ y -
              boundedScalarHalfUpdateReal ε q₂ p₂ y =
            (p₁ - p₂) - (ε / 2) *
              (boundedScalarPositionDerivativeReal (q₁, y) -
                boundedScalarPositionDerivativeReal (q₂, y)) by
              simp [boundedScalarHalfUpdateReal]; ring]
          calc
            _ ≤ |p₁ - p₂| + |ε / 2| *
                |boundedScalarPositionDerivativeReal (q₁, y) -
                  boundedScalarPositionDerivativeReal (q₂, y)| := by
              rw [show (p₁ - p₂) - (ε / 2) *
                    (boundedScalarPositionDerivativeReal (q₁, y) -
                      boundedScalarPositionDerivativeReal (q₂, y)) =
                  (p₁ - p₂) + (-(ε / 2) *
                    (boundedScalarPositionDerivativeReal (q₁, y) -
                      boundedScalarPositionDerivativeReal (q₂, y))) by ring]
              simpa [abs_mul] using abs_add_le (p₁ - p₂)
                (-(ε / 2) * (boundedScalarPositionDerivativeReal (q₁, y) -
                  boundedScalarPositionDerivativeReal (q₂, y)))
            _ ≤ _ := by
              apply add_le_add (le_refl _)
              simpa [mul_assoc] using
                mul_le_mul_of_nonneg_left hposition (abs_nonneg (ε / 2))
  have hden : 0 < 1 - |ε / 2| * 3 := sub_pos.mpr hstep
  apply (le_div_iff₀ hden).2
  nlinarith [abs_nonneg (x - y)]

/-- Stability of the exact implicit-position solution under an approximate
half momentum. The bounded velocity callback is globally nine-Lipschitz in
momentum, while both position maps share the same contraction rate. -/
theorem boundedScalarPositionFixedPoints_dist_le
    (ε q pApprox pExact : ℝ) (hstep : |ε / 2| * 3 < 1) :
    dist
        ((boundedScalarPositionUpdateReal_contracting ε q pApprox hstep).fixedPoint
          (boundedScalarPositionUpdateReal ε q pApprox))
        ((boundedScalarPositionUpdateReal_contracting ε q pExact hstep).fixedPoint
          (boundedScalarPositionUpdateReal ε q pExact)) ≤
      (2 * |ε / 2| * 9 * dist pApprox pExact) /
        (1 - boundedScalarPositionRate ε) := by
  apply (boundedScalarPositionUpdateReal_contracting ε q pApprox hstep).fixedPoint_lipschitz_in_map
    (boundedScalarPositionUpdateReal_contracting ε q pExact hstep)
  intro x
  have hq := (boundedScalarMomentumDerivativeReal_lipschitz_snd q).dist_le_mul
    pApprox pExact
  have hx := (boundedScalarMomentumDerivativeReal_lipschitz_snd x).dist_le_mul
    pApprox pExact
  rw [Real.dist_eq] at hq hx ⊢
  simp only [boundedScalarPositionUpdateReal]
  rw [show (q + (ε / 2) *
          (boundedScalarMomentumDerivativeReal (q, pApprox) +
            boundedScalarMomentumDerivativeReal (x, pApprox))) -
        (q + (ε / 2) *
          (boundedScalarMomentumDerivativeReal (q, pExact) +
            boundedScalarMomentumDerivativeReal (x, pExact))) =
      (ε / 2) *
        ((boundedScalarMomentumDerivativeReal (q, pApprox) -
            boundedScalarMomentumDerivativeReal (q, pExact)) +
          (boundedScalarMomentumDerivativeReal (x, pApprox) -
            boundedScalarMomentumDerivativeReal (x, pExact))) by ring,
      abs_mul]
  calc
    _ ≤ |ε / 2| *
        (|boundedScalarMomentumDerivativeReal (q, pApprox) -
            boundedScalarMomentumDerivativeReal (q, pExact)| +
          |boundedScalarMomentumDerivativeReal (x, pApprox) -
            boundedScalarMomentumDerivativeReal (x, pExact)|) := by
      gcongr
      exact abs_add_le _ _
    _ ≤ |ε / 2| * (9 * |pApprox - pExact| + 9 * |pApprox - pExact|) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact add_le_add (by simpa [Real.dist_eq] using hq)
        (by simpa [Real.dist_eq] using hx)
    _ = 2 * |ε / 2| * 9 * |pApprox - pExact| := by ring

/-- Stability of the implicit-position solution under its represented initial
position, at fixed half momentum. -/
theorem boundedScalarPositionFixedPoints_position_dist_le
    (ε q₁ q₂ pHalf : ℝ) (hstep : |ε / 2| * 3 < 1) :
    dist
        ((boundedScalarPositionUpdateReal_contracting ε q₁ pHalf hstep).fixedPoint
          (boundedScalarPositionUpdateReal ε q₁ pHalf))
        ((boundedScalarPositionUpdateReal_contracting ε q₂ pHalf hstep).fixedPoint
          (boundedScalarPositionUpdateReal ε q₂ pHalf)) ≤
      ((1 + 2 * |ε / 2|) * dist q₁ q₂) /
        (1 - boundedScalarPositionRate ε) := by
  apply (boundedScalarPositionUpdateReal_contracting ε q₁ pHalf hstep).fixedPoint_lipschitz_in_map
      (boundedScalarPositionUpdateReal_contracting ε q₂ pHalf hstep)
  intro x
  have hv := (boundedScalarMomentumDerivativeReal_lipschitz_fst pHalf).dist_le_mul
    q₁ q₂
  simp only [Real.dist_eq] at hv ⊢
  rw [show boundedScalarPositionUpdateReal ε q₁ pHalf x -
        boundedScalarPositionUpdateReal ε q₂ pHalf x =
      (q₁ - q₂) + (ε / 2) *
        (boundedScalarMomentumDerivativeReal (q₁, pHalf) -
          boundedScalarMomentumDerivativeReal (q₂, pHalf)) by
      simp [boundedScalarPositionUpdateReal]; ring]
  calc
    _ ≤ |q₁ - q₂| + |ε / 2| *
        |boundedScalarMomentumDerivativeReal (q₁, pHalf) -
          boundedScalarMomentumDerivativeReal (q₂, pHalf)| := by
      simpa [abs_mul] using abs_add_le (q₁ - q₂)
        ((ε / 2) * (boundedScalarMomentumDerivativeReal (q₁, pHalf) -
          boundedScalarMomentumDerivativeReal (q₂, pHalf)))
    _ ≤ |q₁ - q₂| + |ε / 2| * (2 * |q₁ - q₂|) := by
      apply add_le_add (le_refl _)
      exact mul_le_mul_of_nonneg_left hv (abs_nonneg (ε / 2))
    _ = (1 + 2 * |ε / 2|) * |q₁ - q₂| := by ring

/-- Joint input sensitivity of the implicit-position solve after the half
momentum has changed. -/
theorem boundedScalarPositionFixedPoints_input_dist_le
    (ε q₁ q₂ p₁ p₂ : ℝ) (hstep : |ε / 2| * 3 < 1) :
    dist
        ((boundedScalarPositionUpdateReal_contracting ε q₁ p₁ hstep).fixedPoint
          (boundedScalarPositionUpdateReal ε q₁ p₁))
        ((boundedScalarPositionUpdateReal_contracting ε q₂ p₂ hstep).fixedPoint
          (boundedScalarPositionUpdateReal ε q₂ p₂)) ≤
      ((1 + 2 * |ε / 2|) * dist q₁ q₂ +
        2 * |ε / 2| * 9 * dist p₁ p₂) /
          (1 - boundedScalarPositionRate ε) := by
  let middle :=
    (boundedScalarPositionUpdateReal_contracting ε q₁ p₂ hstep).fixedPoint
      (boundedScalarPositionUpdateReal ε q₁ p₂)
  calc
    _ ≤ dist
          ((boundedScalarPositionUpdateReal_contracting ε q₁ p₁ hstep).fixedPoint
            (boundedScalarPositionUpdateReal ε q₁ p₁)) middle +
        dist middle
          ((boundedScalarPositionUpdateReal_contracting ε q₂ p₂ hstep).fixedPoint
            (boundedScalarPositionUpdateReal ε q₂ p₂)) := dist_triangle _ _ _
    _ ≤ (2 * |ε / 2| * 9 * dist p₁ p₂) /
          (1 - boundedScalarPositionRate ε) +
        ((1 + 2 * |ε / 2|) * dist q₁ q₂) /
          (1 - boundedScalarPositionRate ε) := add_le_add
      (boundedScalarPositionFixedPoints_dist_le ε q₁ p₁ p₂ hstep)
      (boundedScalarPositionFixedPoints_position_dist_le ε q₁ q₂ p₂ hstep)
    _ = _ := by ring

/-- Complete exact-step sensitivity expressed through the two exact half
momenta. This is the analytic core from which a bounded-region rational
Lipschitz certificate is obtained. -/
theorem boundedScalarStepReal_dist_le_explicit
    (ε : ℝ) (hstep : |ε / 2| * 3 < 1) (z₁ z₂ : ℝ × ℝ) :
    let h₂ := (boundedScalarHalfUpdateReal_contracting ε z₂.1 z₂.2 hstep).fixedPoint
      (boundedScalarHalfUpdateReal ε z₂.1 z₂.2)
    let halfError :=
      (dist z₁.2 z₂.2 + |ε / 2| *
        (boundedScalarPositionDerivativePositionRate h₂ : ℝ) *
          dist z₁.1 z₂.1) / (1 - |ε / 2| * 3)
    let positionError :=
      ((1 + 2 * |ε / 2|) * dist z₁.1 z₂.1 +
        2 * |ε / 2| * 9 * halfError) /
          (1 - boundedScalarPositionRate ε)
    dist (boundedScalarStepReal ε hstep z₁)
      (boundedScalarStepReal ε hstep z₂) ≤
        max positionError
          ((1 + 3 * |ε / 2|) * halfError + |ε / 2| *
            (boundedScalarPositionDerivativePositionRate h₂ : ℝ) *
              positionError) := by
  dsimp only
  let h₁ := (boundedScalarHalfUpdateReal_contracting ε z₁.1 z₁.2 hstep).fixedPoint
    (boundedScalarHalfUpdateReal ε z₁.1 z₁.2)
  let h₂ := (boundedScalarHalfUpdateReal_contracting ε z₂.1 z₂.2 hstep).fixedPoint
    (boundedScalarHalfUpdateReal ε z₂.1 z₂.2)
  let q₁ := (boundedScalarPositionUpdateReal_contracting ε z₁.1 h₁ hstep).fixedPoint
    (boundedScalarPositionUpdateReal ε z₁.1 h₁)
  let q₂ := (boundedScalarPositionUpdateReal_contracting ε z₂.1 h₂ hstep).fixedPoint
    (boundedScalarPositionUpdateReal ε z₂.1 h₂)
  let halfError :=
    (dist z₁.2 z₂.2 + |ε / 2| *
      (boundedScalarPositionDerivativePositionRate h₂ : ℝ) *
        dist z₁.1 z₂.1) / (1 - |ε / 2| * 3)
  let positionError :=
    ((1 + 2 * |ε / 2|) * dist z₁.1 z₂.1 +
      2 * |ε / 2| * 9 * halfError) /
        (1 - boundedScalarPositionRate ε)
  rw [← congrFun (boundedScalarCertificateStepReal_eq_boundedScalarStepReal
    ε hstep) z₁, ← congrFun
      (boundedScalarCertificateStepReal_eq_boundedScalarStepReal ε hstep) z₂]
  change dist (q₁, h₁ - (ε / 2) *
      boundedScalarPositionDerivativeReal (q₁, h₁))
    (q₂, h₂ - (ε / 2) * boundedScalarPositionDerivativeReal (q₂, h₂)) ≤ _
  have hhalf : dist h₁ h₂ ≤ halfError := by
    exact boundedScalarHalfFixedPoints_dist_le ε z₁.1 z₁.2 z₂.1 z₂.2 hstep
  have hposition : dist q₁ q₂ ≤ positionError := by
    apply (boundedScalarPositionFixedPoints_input_dist_le ε z₁.1 z₂.1 h₁ h₂
      hstep).trans
    unfold positionError
    have hden : (0 : ℝ) < 1 - (boundedScalarPositionRate ε : ℝ) := by
      change 0 < 1 - |ε / 2| * 2
      nlinarith [abs_nonneg (ε / 2)]
    apply (div_le_div_iff_of_pos_right hden).2
    gcongr
  have hforceMomentum :=
    (boundedScalarPositionDerivativeReal_lipschitz_snd q₁).dist_le_mul h₁ h₂
  have hforcePosition :=
    (boundedScalarPositionDerivativeReal_lipschitz_fst h₂).dist_le_mul q₁ q₂
  simp only [Real.dist_eq] at hforceMomentum hforcePosition
  have hforce : |boundedScalarPositionDerivativeReal (q₁, h₁) -
      boundedScalarPositionDerivativeReal (q₂, h₂)| ≤
      3 * |h₁ - h₂| +
        (boundedScalarPositionDerivativePositionRate h₂ : ℝ) * |q₁ - q₂| := by
    calc
      _ ≤ |boundedScalarPositionDerivativeReal (q₁, h₁) -
            boundedScalarPositionDerivativeReal (q₁, h₂)| +
          |boundedScalarPositionDerivativeReal (q₁, h₂) -
            boundedScalarPositionDerivativeReal (q₂, h₂)| := by
        rw [show boundedScalarPositionDerivativeReal (q₁, h₁) -
            boundedScalarPositionDerivativeReal (q₂, h₂) =
          (boundedScalarPositionDerivativeReal (q₁, h₁) -
            boundedScalarPositionDerivativeReal (q₁, h₂)) +
          (boundedScalarPositionDerivativeReal (q₁, h₂) -
            boundedScalarPositionDerivativeReal (q₂, h₂)) by ring]
        exact abs_add_le _ _
      _ ≤ _ := add_le_add hforceMomentum hforcePosition
  have hmomentum : dist
      (h₁ - (ε / 2) * boundedScalarPositionDerivativeReal (q₁, h₁))
      (h₂ - (ε / 2) * boundedScalarPositionDerivativeReal (q₂, h₂)) ≤
      (1 + 3 * |ε / 2|) * halfError + |ε / 2| *
        (boundedScalarPositionDerivativePositionRate h₂ : ℝ) *
          positionError := by
    rw [Real.dist_eq]
    calc
      _ = |(h₁ - h₂) - (ε / 2) *
          (boundedScalarPositionDerivativeReal (q₁, h₁) -
            boundedScalarPositionDerivativeReal (q₂, h₂))| := by
        congr 1
        ring
      _ ≤ |h₁ - h₂| + |ε / 2| *
          |boundedScalarPositionDerivativeReal (q₁, h₁) -
            boundedScalarPositionDerivativeReal (q₂, h₂)| := by
        rw [show (h₁ - h₂) - (ε / 2) *
              (boundedScalarPositionDerivativeReal (q₁, h₁) -
                boundedScalarPositionDerivativeReal (q₂, h₂)) =
            (h₁ - h₂) + (-(ε / 2) *
              (boundedScalarPositionDerivativeReal (q₁, h₁) -
                boundedScalarPositionDerivativeReal (q₂, h₂))) by ring]
        simpa [abs_mul] using abs_add_le (h₁ - h₂)
          (-(ε / 2) * (boundedScalarPositionDerivativeReal (q₁, h₁) -
            boundedScalarPositionDerivativeReal (q₂, h₂)))
      _ ≤ |h₁ - h₂| + |ε / 2| *
          (3 * |h₁ - h₂| +
            (boundedScalarPositionDerivativePositionRate h₂ : ℝ) *
              |q₁ - q₂|) := by
        apply add_le_add (le_refl _)
        exact mul_le_mul_of_nonneg_left hforce (abs_nonneg (ε / 2))
      _ ≤ (1 + 3 * |ε / 2|) * halfError + |ε / 2| *
          (boundedScalarPositionDerivativePositionRate h₂ : ℝ) *
            positionError := by
        have hh : |h₁ - h₂| ≤ halfError := by simpa [Real.dist_eq] using hhalf
        have hq : |q₁ - q₂| ≤ positionError := by
          simpa [Real.dist_eq] using hposition
        have hrate : 0 ≤
            (boundedScalarPositionDerivativePositionRate h₂ : ℝ) := by positivity
        rw [show |h₁ - h₂| + |ε / 2| *
              (3 * |h₁ - h₂| +
                (boundedScalarPositionDerivativePositionRate h₂ : ℝ) *
                  |q₁ - q₂|) =
            (1 + 3 * |ε / 2|) * |h₁ - h₂| + |ε / 2| *
              (boundedScalarPositionDerivativePositionRate h₂ : ℝ) *
                |q₁ - q₂| by ring]
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hh (by positivity)
        · exact mul_le_mul_of_nonneg_left hq
            (mul_nonneg (abs_nonneg _) hrate)
  exact scalarPhase_dist_le_max hposition hmomentum

/-- Rational bounded-region coefficients for the exact nonlinear bounded GR
step. The region premise needed by soundness is only a bound on the second
exact half momentum; all remaining coefficients are derived arithmetically. -/
structure BoundedScalarStepRegionalRationalCertificate where
  epsilon : ℚ
  halfMomentumBound : ℚ
  forcePositionRate : ℚ
  halfCoefficient : ℚ
  positionCoefficient : ℚ
  momentumCoefficient : ℚ
  lipschitzUpper : ℚ
deriving DecidableEq, Repr

namespace BoundedScalarStepRegionalRationalCertificate

def Valid (certificate : BoundedScalarStepRegionalRationalCertificate) : Prop :=
  0 ≤ certificate.halfMomentumBound ∧
    |certificate.epsilon / 2| * 3 < 1 ∧
    certificate.forcePositionRate =
      18 * certificate.halfMomentumBound ^ 2 +
        3 * certificate.halfMomentumBound ∧
    certificate.halfCoefficient =
      (1 + |certificate.epsilon / 2| * certificate.forcePositionRate) /
        (1 - |certificate.epsilon / 2| * 3) ∧
    certificate.positionCoefficient =
      ((1 + 2 * |certificate.epsilon / 2|) +
        2 * |certificate.epsilon / 2| * 9 *
          certificate.halfCoefficient) /
        (1 - |certificate.epsilon / 2| * 2) ∧
    certificate.momentumCoefficient =
      (1 + 3 * |certificate.epsilon / 2|) *
          certificate.halfCoefficient +
        |certificate.epsilon / 2| * certificate.forcePositionRate *
          certificate.positionCoefficient ∧
    certificate.lipschitzUpper = max certificate.positionCoefficient
      certificate.momentumCoefficient

instance (certificate : BoundedScalarStepRegionalRationalCertificate) :
    Decidable certificate.Valid := by
  unfold Valid
  infer_instance

def check (certificate : BoundedScalarStepRegionalRationalCertificate) : Bool :=
  decide certificate.Valid

@[simp] theorem check_eq_true_iff
    (certificate : BoundedScalarStepRegionalRationalCertificate) :
    certificate.check = true ↔ certificate.Valid := by
  simp [check]

theorem forcePositionRate_upper
    (certificate : BoundedScalarStepRegionalRationalCertificate)
    (hvalid : certificate.Valid) (p : ℝ)
    (hp : |p| ≤ (certificate.halfMomentumBound : ℝ)) :
    (boundedScalarPositionDerivativePositionRate p : ℝ) ≤
      certificate.forcePositionRate := by
  rcases hvalid with ⟨hbound, _, hrate, _⟩
  have hboundReal : (0 : ℝ) ≤ certificate.halfMomentumBound := by
    exact_mod_cast hbound
  have hpNonneg := abs_nonneg p
  have hsquare : p ^ 2 ≤ (certificate.halfMomentumBound : ℝ) ^ 2 := by
    rw [← sq_abs]
    nlinarith [sq_nonneg ((certificate.halfMomentumBound : ℝ) - |p|)]
  change 18 * p ^ 2 + 3 * |p| ≤ (certificate.forcePositionRate : ℚ)
  rw [hrate]
  exact_mod_cast (show
    18 * (p : ℝ) ^ 2 + 3 * |p| ≤
      18 * (certificate.halfMomentumBound : ℝ) ^ 2 +
        3 * certificate.halfMomentumBound by nlinarith)

/-- The checked rational upper is a genuine Lipschitz bound for any pair whose
second exact half momentum lies in the submitted region. -/
theorem step_dist_le
    (certificate : BoundedScalarStepRegionalRationalCertificate)
    (hvalid : certificate.Valid) (z₁ z₂ : ℝ × ℝ)
    (hhalf :
      |(boundedScalarHalfUpdateReal_contracting
          (certificate.epsilon : ℝ) z₂.1 z₂.2
          (by exact_mod_cast hvalid.2.1)).fixedPoint
        (boundedScalarHalfUpdateReal certificate.epsilon z₂.1 z₂.2)| ≤
        (certificate.halfMomentumBound : ℝ)) :
    dist
      (boundedScalarStepReal (certificate.epsilon : ℝ)
        (by exact_mod_cast hvalid.2.1) z₁)
      (boundedScalarStepReal (certificate.epsilon : ℝ)
        (by exact_mod_cast hvalid.2.1) z₂) ≤
      (certificate.lipschitzUpper : ℝ) * dist z₁ z₂ := by
  let ε : ℝ := certificate.epsilon
  let a : ℝ := |ε / 2|
  let h₂ := (boundedScalarHalfUpdateReal_contracting ε z₂.1 z₂.2
    (by
      change |(certificate.epsilon : ℝ) / 2| * 3 < 1
      exact_mod_cast hvalid.2.1)).fixedPoint
      (boundedScalarHalfUpdateReal ε z₂.1 z₂.2)
  let d := dist z₁ z₂
  let L : ℝ := certificate.forcePositionRate
  let H : ℝ := certificate.halfCoefficient
  let Q : ℝ := certificate.positionCoefficient
  let M : ℝ := certificate.momentumCoefficient
  have hstep : a * 3 < 1 := by
    dsimp [a, ε]
    exact_mod_cast hvalid.2.1
  have hpositionStep : a * 2 < 1 := by
    nlinarith [abs_nonneg (ε / 2)]
  have hL : (boundedScalarPositionDerivativePositionRate h₂ : ℝ) ≤ L := by
    exact certificate.forcePositionRate_upper hvalid h₂ (by simpa [h₂, ε] using hhalf)
  have hLnonneg : 0 ≤ L := by
    dsimp [L]
    rw [hvalid.2.2.1]
    have hb : (0 : ℝ) ≤ certificate.halfMomentumBound := by
      exact_mod_cast hvalid.1
    have hbq : (0 : ℚ) ≤ certificate.halfMomentumBound := hvalid.1
    exact_mod_cast (add_nonneg
      (mul_nonneg (by norm_num : (0 : ℚ) ≤ 18)
        (sq_nonneg certificate.halfMomentumBound))
      (mul_nonneg (by norm_num : (0 : ℚ) ≤ 3) hbq))
  have hdq : dist z₁.1 z₂.1 ≤ d := by
    dsimp [d]
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have hdp : dist z₁.2 z₂.2 ≤ d := by
    dsimp [d]
    rw [Prod.dist_eq]
    exact le_max_right _ _
  have hdnonneg : 0 ≤ d := dist_nonneg
  have hH : H = (1 + a * L) / (1 - a * 3) := by
    dsimp [H, L, a, ε]
    exact_mod_cast hvalid.2.2.2.1
  have hQ : Q = ((1 + 2 * a) + 2 * a * 9 * H) /
      (1 - a * 2) := by
    dsimp [Q, H, a, ε]
    exact_mod_cast hvalid.2.2.2.2.1
  have hM : M = (1 + 3 * a) * H + a * L * Q := by
    dsimp [M, H, L, Q, a, ε]
    exact_mod_cast hvalid.2.2.2.2.2.1
  have hLip : (certificate.lipschitzUpper : ℝ) = max Q M := by
    dsimp [Q, M]
    exact_mod_cast hvalid.2.2.2.2.2.2
  have hHnonneg : 0 ≤ H := by rw [hH]; positivity
  have hQnonneg : 0 ≤ Q := by rw [hQ]; positivity
  have hMnonneg : 0 ≤ M := by rw [hM]; positivity
  let halfError :=
    (dist z₁.2 z₂.2 + a *
      (boundedScalarPositionDerivativePositionRate h₂ : ℝ) *
        dist z₁.1 z₂.1) / (1 - a * 3)
  let positionError :=
    ((1 + 2 * a) * dist z₁.1 z₂.1 +
      2 * a * 9 * halfError) / (1 - a * 2)
  have hhalfError : halfError ≤ H * d := by
    rw [hH]
    dsimp [halfError]
    have hden : 0 < 1 - a * 3 := sub_pos.mpr hstep
    rw [div_mul_eq_mul_div]
    apply (div_le_div_iff_of_pos_right hden).2
    calc
      dist z₁.2 z₂.2 + a *
          (boundedScalarPositionDerivativePositionRate h₂ : ℝ) *
            dist z₁.1 z₂.1 ≤ d + a * L * d := by
        apply add_le_add hdp
        exact mul_le_mul (mul_le_mul_of_nonneg_left hL (abs_nonneg _)) hdq
          dist_nonneg (mul_nonneg (abs_nonneg _) hLnonneg)
      _ = (1 + a * L) * d := by ring
  have hpositionError : positionError ≤ Q * d := by
    rw [hQ]
    dsimp [positionError]
    have hden : 0 < 1 - a * 2 := sub_pos.mpr hpositionStep
    rw [div_mul_eq_mul_div]
    apply (div_le_div_iff_of_pos_right hden).2
    calc
      (1 + 2 * a) * dist z₁.1 z₂.1 + 2 * a * 9 * halfError ≤
          (1 + 2 * a) * d + 2 * a * 9 * (H * d) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hdq (by positivity)
        · exact mul_le_mul_of_nonneg_left hhalfError (by positivity)
      _ = ((1 + 2 * a) + 2 * a * 9 * H) * d := by ring
  have hmomentumError :
      (1 + 3 * a) * halfError + a *
          (boundedScalarPositionDerivativePositionRate h₂ : ℝ) *
            positionError ≤ M * d := by
    rw [hM]
    calc
      _ ≤ (1 + 3 * a) * (H * d) + a * L * (Q * d) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hhalfError (by positivity)
        · exact mul_le_mul
            (mul_le_mul_of_nonneg_left hL (abs_nonneg _)) hpositionError
            (by positivity) (mul_nonneg (abs_nonneg _) hLnonneg)
      _ = ((1 + 3 * a) * H + a * L * Q) * d := by ring
  have hexplicit := boundedScalarStepReal_dist_le_explicit ε
    (by simpa [a] using hstep) z₁ z₂
  change dist (boundedScalarStepReal ε _ z₁)
      (boundedScalarStepReal ε _ z₂) ≤ _
  apply hexplicit.trans
  rw [hLip, max_mul_of_nonneg _ _ hdnonneg]
  exact max_le_max hpositionError hmomentumError

end BoundedScalarStepRegionalRationalCertificate

/-- Generic closure from a fully linked callback/arithmetic update through its
rounded residual and an exact contraction theorem. -/
theorem BoundedScalarAffineUpdateRationalCertificate.dist_fixedPoint_le
    (update : BoundedScalarAffineUpdateRationalCertificate)
    (hupdate : update.Valid)
    (residual : RoundedContractionResidualRationalCertificate)
    (hresidual : residual.Valid)
    (contraction : AposterioriContractionRationalCertificate)
    (hcontraction : contraction.Valid) (f : ℝ → ℝ) (K : NNReal)
    (hcontract : ContractingWith K f)
    (hrate : (K : ℝ) = (contraction.rate : ℝ))
    (hresidualUpper : contraction.residualUpper = residual.residualUpper)
    (hcomputed : residual.computedUpdate = update.affine.computedUpdate)
    (herror : residual.updateError = update.affine.updateError)
    (hfunction : f residual.iterate = update.affine.base +
      update.affine.scale * update.sources.ideal) :
    dist (residual.iterate : ℝ) (hcontract.fixedPoint f) ≤
      (contraction.distanceUpper : ℝ) := by
  apply roundedContraction_dist_fixedPoint_le residual hresidual contraction
    hcontraction f K hcontract hrate hresidualUpper
  rw [hcomputed, herror, hfunction]
  exact update.exactUpdate_le hupdate

/-- Fully instantiated half-momentum distance certificate for the maintained
bounded solver's scalar-coordinate contraction. -/
theorem boundedScalarHalfUpdate_dist_fixedPoint_le
    (ε q p : ℝ) (hstep : |ε / 2| * 3 < 1)
    (update : BoundedScalarAffineUpdateRationalCertificate)
    (hupdate : update.Valid)
    (residual : RoundedContractionResidualRationalCertificate)
    (hresidual : residual.Valid)
    (contraction : AposterioriContractionRationalCertificate)
    (hcontraction : contraction.Valid)
    (hrate : ((boundedScalarHalfRate ε : NNReal) : ℝ) = contraction.rate)
    (hresidualUpper : contraction.residualUpper = residual.residualUpper)
    (hcomputed : residual.computedUpdate = update.affine.computedUpdate)
    (herror : residual.updateError = update.affine.updateError)
    (hbase : (update.affine.base : ℝ) = p)
    (hscale : (update.affine.scale : ℝ) = -(ε / 2))
    (hsources : update.sources.ideal =
      boundedScalarPositionDerivativeReal (q, residual.iterate)) :
    dist (residual.iterate : ℝ)
        ((boundedScalarHalfUpdateReal_contracting ε q p hstep).fixedPoint
          (boundedScalarHalfUpdateReal ε q p)) ≤
      (contraction.distanceUpper : ℝ) := by
  apply update.dist_fixedPoint_le hupdate residual hresidual contraction
    hcontraction (boundedScalarHalfUpdateReal ε q p)
    (boundedScalarHalfRate ε)
    (boundedScalarHalfUpdateReal_contracting ε q p hstep) hrate
    hresidualUpper hcomputed herror
  simp only [boundedScalarHalfUpdateReal, hbase, hscale, hsources]
  ring

/-- Fully instantiated implicit-position distance certificate. -/
theorem boundedScalarPositionUpdate_dist_fixedPoint_le
    (ε q pHalf : ℝ) (hstep : |ε / 2| * 3 < 1)
    (update : BoundedScalarAffineUpdateRationalCertificate)
    (hupdate : update.Valid)
    (residual : RoundedContractionResidualRationalCertificate)
    (hresidual : residual.Valid)
    (contraction : AposterioriContractionRationalCertificate)
    (hcontraction : contraction.Valid)
    (hrate : ((boundedScalarPositionRate ε : NNReal) : ℝ) = contraction.rate)
    (hresidualUpper : contraction.residualUpper = residual.residualUpper)
    (hcomputed : residual.computedUpdate = update.affine.computedUpdate)
    (herror : residual.updateError = update.affine.updateError)
    (hbase : (update.affine.base : ℝ) = q)
    (hscale : (update.affine.scale : ℝ) = ε / 2)
    (hsources : update.sources.ideal =
      boundedScalarMomentumDerivativeReal (q, pHalf) +
        boundedScalarMomentumDerivativeReal (residual.iterate, pHalf)) :
    dist (residual.iterate : ℝ)
        ((boundedScalarPositionUpdateReal_contracting ε q pHalf hstep).fixedPoint
          (boundedScalarPositionUpdateReal ε q pHalf)) ≤
      (contraction.distanceUpper : ℝ) := by
  apply update.dist_fixedPoint_le hupdate residual hresidual contraction
    hcontraction (boundedScalarPositionUpdateReal ε q pHalf)
    (boundedScalarPositionRate ε)
    (boundedScalarPositionUpdateReal_contracting ε q pHalf hstep) hrate
    hresidualUpper hcomputed herror
  simp only [boundedScalarPositionUpdateReal, hbase, hscale, hsources]

/-- Which implicit scalar solve is certified by a final contraction record. -/
inductive BoundedScalarSolverContractionKind where
  | halfMomentum
  | position
deriving DecidableEq, Repr

/-- End-to-end rational certificate linking the final recorded affine update
to the exact contraction map used by the bounded scalar solver. -/
structure BoundedScalarSolverContractionRationalCertificate where
  kind : BoundedScalarSolverContractionKind
  epsilon : ℚ
  update : BoundedScalarAffineUpdateRationalCertificate
  residual : RoundedContractionResidualRationalCertificate
  contraction : AposterioriContractionRationalCertificate
deriving DecidableEq, Repr

namespace BoundedScalarSolverContractionRationalCertificate

def LinkValid (kind : BoundedScalarSolverContractionKind) (epsilon : ℚ)
    (update : BoundedScalarAffineUpdateRationalCertificate)
    (residual : RoundedContractionResidualRationalCertificate)
    (contraction : AposterioriContractionRationalCertificate) : Prop :=
  match kind, update.sources with
  | .halfMomentum, .one entry =>
      entry.kind = .position ∧
      update.affine.scale = -(epsilon / 2) ∧
      entry.certificate.primitive.momentum = residual.iterate ∧
      contraction.rate = |epsilon / 2| * 3
  | .position, .pair first second =>
      first.kind = .momentum ∧ second.kind = .momentum ∧
      update.affine.base = first.certificate.primitive.sincos.input ∧
      update.affine.scale = epsilon / 2 ∧
      first.certificate.primitive.sincos.input = update.affine.base ∧
      second.certificate.primitive.sincos.input = residual.iterate ∧
      first.certificate.primitive.momentum = second.certificate.primitive.momentum ∧
      contraction.rate = |epsilon / 2| * 2
  | _, _ => False

instance (kind : BoundedScalarSolverContractionKind) (epsilon : ℚ)
    (update : BoundedScalarAffineUpdateRationalCertificate)
    (residual : RoundedContractionResidualRationalCertificate)
    (contraction : AposterioriContractionRationalCertificate) :
    Decidable (LinkValid kind epsilon update residual contraction) := by
  cases hkind : kind <;>
    cases hsources : update.sources <;>
      simp only [LinkValid, hsources] <;> infer_instance

def Valid (certificate : BoundedScalarSolverContractionRationalCertificate) : Prop :=
  certificate.update.Valid ∧ certificate.residual.Valid ∧
    certificate.contraction.Valid ∧
    certificate.residual.computedUpdate = certificate.update.affine.computedUpdate ∧
    certificate.residual.updateError = certificate.update.affine.updateError ∧
    certificate.contraction.residualUpper = certificate.residual.residualUpper ∧
    |certificate.epsilon / 2| * 3 < 1 ∧
    LinkValid certificate.kind certificate.epsilon certificate.update
      certificate.residual certificate.contraction

instance (certificate : BoundedScalarSolverContractionRationalCertificate) :
    Decidable certificate.Valid := by
  unfold Valid
  infer_instance

def check (certificate : BoundedScalarSolverContractionRationalCertificate) : Bool :=
  decide certificate.Valid

@[simp] theorem check_eq_true_iff
    (certificate : BoundedScalarSolverContractionRationalCertificate) :
    certificate.check = true ↔ certificate.Valid := by
  simp [check]

/-- Soundness of an accepted final half-momentum record. The exact fixed point
uses the recorded position input and affine base; the returned iterate is the
runtime value whose residual was checked. -/
theorem halfMomentum_dist_fixedPoint_le
    (certificate : BoundedScalarSolverContractionRationalCertificate)
    (entry : BoundedScalarCallbackTraceEntry)
    (hvalid : certificate.Valid)
    (hkind : certificate.kind = .halfMomentum)
    (hsources : certificate.update.sources = .one entry) :
    dist (certificate.residual.iterate : ℝ)
        ((boundedScalarHalfUpdateReal_contracting
          (certificate.epsilon : ℝ)
          (entry.certificate.primitive.sincos.input : ℝ)
          (certificate.update.affine.base : ℝ)
          (by
            have hrate : |(certificate.epsilon : ℝ) / 2| * 3 =
                (certificate.contraction.rate : ℝ) := by
              rcases hvalid with ⟨_, _, _, _, _, _, _, hlink⟩
              simp only [LinkValid, hkind, hsources] at hlink
              exact_mod_cast hlink.2.2.2.symm
            rw [hrate]
            rcases hvalid with ⟨_, _, hcontraction, _, _, _, _, _⟩
            exact_mod_cast hcontraction.2.2.1)).fixedPoint
          (boundedScalarHalfUpdateReal (certificate.epsilon : ℝ)
            (entry.certificate.primitive.sincos.input : ℝ)
            (certificate.update.affine.base : ℝ))) ≤
      (certificate.contraction.distanceUpper : ℝ) := by
  rcases hvalid with ⟨hupdate, hresidual, hcontraction, hcomputed, herror,
    hresidualUpper, hstepRat, hlink⟩
  simp only [LinkValid, hkind, hsources] at hlink
  have hstep : |(certificate.epsilon : ℝ) / 2| * 3 < 1 := by
    rw [show |(certificate.epsilon : ℝ) / 2| * 3 =
      (certificate.contraction.rate : ℝ) by exact_mod_cast hlink.2.2.2.symm]
    exact_mod_cast hcontraction.2.2.1
  apply boundedScalarHalfUpdate_dist_fixedPoint_le
    (certificate.epsilon : ℝ)
    (entry.certificate.primitive.sincos.input : ℝ)
    (certificate.update.affine.base : ℝ) hstep certificate.update hupdate
    certificate.residual hresidual certificate.contraction hcontraction
  · change |(certificate.epsilon : ℝ) / 2| * 3 =
      (certificate.contraction.rate : ℝ)
    exact_mod_cast hlink.2.2.2.symm
  · exact hresidualUpper
  · exact hcomputed
  · exact herror
  · rfl
  · exact_mod_cast hlink.2.1
  · rw [hsources]
    simp only [BoundedScalarAffineCallbackSources.ideal,
      BoundedScalarCallbackTraceEntry.ideal, hlink.1, hlink.2.2.1]

/-- Soundness of an accepted final implicit-position record. The two linked
momentum callbacks are evaluated at the original and returned positions with
the same recorded half momentum. -/
theorem position_dist_fixedPoint_le
    (certificate : BoundedScalarSolverContractionRationalCertificate)
    (first second : BoundedScalarCallbackTraceEntry)
    (hvalid : certificate.Valid)
    (hkind : certificate.kind = .position)
    (hsources : certificate.update.sources = .pair first second) :
    dist (certificate.residual.iterate : ℝ)
        ((boundedScalarPositionUpdateReal_contracting
          (certificate.epsilon : ℝ)
          (certificate.update.affine.base : ℝ)
          (first.certificate.primitive.momentum : ℝ)
          (by
            rcases hvalid with ⟨_, _, _, _, _, _, hstepRat, _⟩
            exact_mod_cast hstepRat)).fixedPoint
          (boundedScalarPositionUpdateReal (certificate.epsilon : ℝ)
            (certificate.update.affine.base : ℝ)
            (first.certificate.primitive.momentum : ℝ))) ≤
      (certificate.contraction.distanceUpper : ℝ) := by
  rcases hvalid with ⟨hupdate, hresidual, hcontraction, hcomputed, herror,
    hresidualUpper, hstepRat, hlink⟩
  simp only [LinkValid, hkind, hsources] at hlink
  have hstep : |(certificate.epsilon : ℝ) / 2| * 3 < 1 := by
    exact_mod_cast hstepRat
  apply boundedScalarPositionUpdate_dist_fixedPoint_le
    (certificate.epsilon : ℝ) (certificate.update.affine.base : ℝ)
    (first.certificate.primitive.momentum : ℝ) hstep certificate.update hupdate
    certificate.residual hresidual certificate.contraction hcontraction
  · change |(certificate.epsilon : ℝ) / 2| * 2 =
      (certificate.contraction.rate : ℝ)
    exact_mod_cast hlink.2.2.2.2.2.2.2.symm
  · exact hresidualUpper
  · exact hcomputed
  · exact herror
  · rfl
  · exact_mod_cast hlink.2.2.2.1
  · rw [hsources]
    simp only [BoundedScalarAffineCallbackSources.ideal,
      BoundedScalarCallbackTraceEntry.ideal, hlink.1, hlink.2.1,
      hlink.2.2.2.2.1, hlink.2.2.2.2.2.1, hlink.2.2.2.2.2.2.1]

end BoundedScalarSolverContractionRationalCertificate

/-- The two implicit-loop certificates, linked into one phase-position error
budget. The position budget includes both its own residual and sensitivity to
the rounded half momentum. -/
structure BoundedScalarSolverPhaseRationalCertificate where
  half : BoundedScalarSolverContractionRationalCertificate
  position : BoundedScalarSolverContractionRationalCertificate
  positionError : ℚ
deriving DecidableEq, Repr

namespace BoundedScalarSolverPhaseRationalCertificate

def SourcesLinkValid
    (halfSources positionSources : BoundedScalarAffineCallbackSources)
    (halfEpsilon halfIterate halfDistance positionBase positionDistance
      positionError : ℚ) : Prop :=
  match halfSources, positionSources with
  | .one halfEntry, .pair first _ =>
      positionBase = halfEntry.certificate.primitive.sincos.input ∧
        first.certificate.primitive.momentum = halfIterate ∧
        positionError = positionDistance +
          (2 * |halfEpsilon / 2| * 9 * halfDistance) /
            (1 - |halfEpsilon / 2| * 2)
  | _, _ => False

instance (halfSources positionSources : BoundedScalarAffineCallbackSources)
    (halfEpsilon halfIterate halfDistance positionBase positionDistance
      positionError : ℚ) :
    Decidable (SourcesLinkValid halfSources positionSources halfEpsilon
      halfIterate halfDistance positionBase positionDistance positionError) := by
  cases halfSources <;> cases positionSources <;>
    unfold SourcesLinkValid <;> infer_instance

def LinkValid (certificate : BoundedScalarSolverPhaseRationalCertificate) : Prop :=
  certificate.half.kind = .halfMomentum ∧
    certificate.position.kind = .position ∧
    certificate.position.epsilon = certificate.half.epsilon ∧
    SourcesLinkValid certificate.half.update.sources
      certificate.position.update.sources certificate.half.epsilon
      certificate.half.residual.iterate
      certificate.half.contraction.distanceUpper
      certificate.position.update.affine.base
      certificate.position.contraction.distanceUpper certificate.positionError

instance (certificate : BoundedScalarSolverPhaseRationalCertificate) :
    Decidable certificate.LinkValid := by
  unfold LinkValid
  infer_instance

def Valid (certificate : BoundedScalarSolverPhaseRationalCertificate) : Prop :=
  certificate.half.Valid ∧ certificate.position.Valid ∧ certificate.LinkValid

instance (certificate : BoundedScalarSolverPhaseRationalCertificate) :
    Decidable certificate.Valid := by
  unfold Valid
  infer_instance

def check (certificate : BoundedScalarSolverPhaseRationalCertificate) : Bool :=
  decide certificate.Valid

@[simp] theorem check_eq_true_iff
    (certificate : BoundedScalarSolverPhaseRationalCertificate) :
    certificate.check = true ↔ certificate.Valid := by
  simp [check]

/-- A valid paired record constructs exact half-momentum and next-position
fixed points and bounds both returned runtime coordinates. The position error
includes sensitivity to the approximate half momentum. -/
theorem exists_exactPhase
    (certificate : BoundedScalarSolverPhaseRationalCertificate)
    (halfEntry first second : BoundedScalarCallbackTraceEntry)
    (hvalid : certificate.Valid)
    (hhalfSources : certificate.half.update.sources = .one halfEntry)
    (hpositionSources : certificate.position.update.sources = .pair first second) :
    ∃ pExact qExact : ℝ,
      Function.IsFixedPt
          (boundedScalarHalfUpdateReal (certificate.half.epsilon : ℝ)
            (halfEntry.certificate.primitive.sincos.input : ℝ)
            (certificate.half.update.affine.base : ℝ)) pExact ∧
        Function.IsFixedPt
          (boundedScalarPositionUpdateReal (certificate.position.epsilon : ℝ)
            (certificate.position.update.affine.base : ℝ) pExact) qExact ∧
        dist (certificate.half.residual.iterate : ℝ) pExact ≤
          (certificate.half.contraction.distanceUpper : ℝ) ∧
        dist (certificate.position.residual.iterate : ℝ) qExact ≤
          (certificate.positionError : ℝ) := by
  rcases hvalid with ⟨hhalf, hposition, hlink⟩
  rcases hlink with ⟨hhalfKind, hpositionKind, hepsilon, hsourcesLink⟩
  simp only [SourcesLinkValid, hhalfSources, hpositionSources] at hsourcesLink
  rcases hsourcesLink with ⟨hbase, hmomentum, hpositionError⟩
  have hhalfStep : |(certificate.half.epsilon : ℝ) / 2| * 3 < 1 := by
    exact_mod_cast hhalf.2.2.2.2.2.2.1
  let halfContract := boundedScalarHalfUpdateReal_contracting
    (certificate.half.epsilon : ℝ)
    (halfEntry.certificate.primitive.sincos.input : ℝ)
    (certificate.half.update.affine.base : ℝ) hhalfStep
  let pExact := halfContract.fixedPoint
    (boundedScalarHalfUpdateReal (certificate.half.epsilon : ℝ)
      (halfEntry.certificate.primitive.sincos.input : ℝ)
      (certificate.half.update.affine.base : ℝ))
  have hpExact : Function.IsFixedPt
      (boundedScalarHalfUpdateReal (certificate.half.epsilon : ℝ)
        (halfEntry.certificate.primitive.sincos.input : ℝ)
        (certificate.half.update.affine.base : ℝ)) pExact := by
    exact halfContract.fixedPoint_isFixedPt
  have hpError : dist (certificate.half.residual.iterate : ℝ) pExact ≤
      (certificate.half.contraction.distanceUpper : ℝ) := by
    simpa [halfContract, pExact] using
      certificate.half.halfMomentum_dist_fixedPoint_le halfEntry hhalf
        hhalfKind hhalfSources
  have hpositionStep : |(certificate.position.epsilon : ℝ) / 2| * 3 < 1 := by
    exact_mod_cast hposition.2.2.2.2.2.2.1
  let positionContract := boundedScalarPositionUpdateReal_contracting
    (certificate.position.epsilon : ℝ)
    (certificate.position.update.affine.base : ℝ) pExact hpositionStep
  let qExact := positionContract.fixedPoint
    (boundedScalarPositionUpdateReal (certificate.position.epsilon : ℝ)
      (certificate.position.update.affine.base : ℝ) pExact)
  have hqExact : Function.IsFixedPt
      (boundedScalarPositionUpdateReal (certificate.position.epsilon : ℝ)
        (certificate.position.update.affine.base : ℝ) pExact) qExact := by
    exact positionContract.fixedPoint_isFixedPt
  let approximatePositionContract := boundedScalarPositionUpdateReal_contracting
    (certificate.position.epsilon : ℝ)
    (certificate.position.update.affine.base : ℝ)
    (first.certificate.primitive.momentum : ℝ) hpositionStep
  let qIntermediate := approximatePositionContract.fixedPoint
    (boundedScalarPositionUpdateReal (certificate.position.epsilon : ℝ)
      (certificate.position.update.affine.base : ℝ)
      (first.certificate.primitive.momentum : ℝ))
  have hqResidual : dist (certificate.position.residual.iterate : ℝ)
      qIntermediate ≤ (certificate.position.contraction.distanceUpper : ℝ) := by
    simpa [approximatePositionContract, qIntermediate] using
      certificate.position.position_dist_fixedPoint_le first second hposition
        hpositionKind hpositionSources
  have hqSensitivity : dist qIntermediate qExact ≤
      (2 * |(certificate.position.epsilon : ℝ) / 2| * 9 *
        dist (first.certificate.primitive.momentum : ℝ) pExact) /
          (1 - boundedScalarPositionRate (certificate.position.epsilon : ℝ)) := by
    simpa [approximatePositionContract, positionContract, qIntermediate, qExact]
      using boundedScalarPositionFixedPoints_dist_le
        (certificate.position.epsilon : ℝ)
        (certificate.position.update.affine.base : ℝ)
        (first.certificate.primitive.momentum : ℝ) pExact hpositionStep
  refine ⟨pExact, qExact, hpExact, hqExact, hpError, ?_⟩
  calc
    dist (certificate.position.residual.iterate : ℝ) qExact ≤
        dist (certificate.position.residual.iterate : ℝ) qIntermediate +
          dist qIntermediate qExact := dist_triangle _ _ _
    _ ≤ (certificate.position.contraction.distanceUpper : ℝ) +
        (2 * |(certificate.position.epsilon : ℝ) / 2| * 9 *
          dist (first.certificate.primitive.momentum : ℝ) pExact) /
            (1 - boundedScalarPositionRate (certificate.position.epsilon : ℝ)) :=
      add_le_add hqResidual hqSensitivity
    _ ≤ (certificate.position.contraction.distanceUpper : ℝ) +
        (2 * |(certificate.position.epsilon : ℝ) / 2| * 9 *
          certificate.half.contraction.distanceUpper) /
            (1 - boundedScalarPositionRate (certificate.position.epsilon : ℝ)) := by
      apply add_le_add le_rfl
      apply div_le_div_of_nonneg_right _
        (sub_nonneg.mpr (by
          exact_mod_cast
            (boundedScalarPositionUpdateReal_contracting
              (certificate.position.epsilon : ℝ)
              (certificate.position.update.affine.base : ℝ) pExact
              hpositionStep).1.le))
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) (by norm_num))
      simpa [hmomentum] using hpError
    _ = (certificate.positionError : ℝ) := by
      rw [show (certificate.position.epsilon : ℝ) =
        (certificate.half.epsilon : ℝ) by exact_mod_cast hepsilon]
      change (certificate.position.contraction.distanceUpper : ℝ) +
        (2 * |(certificate.half.epsilon : ℝ) / 2| * 9 *
          (certificate.half.contraction.distanceUpper : ℝ)) /
            (1 - |(certificate.half.epsilon : ℝ) / 2| * 2) =
          (certificate.positionError : ℝ)
      exact_mod_cast hpositionError.symm

end BoundedScalarSolverPhaseRationalCertificate

/-- Complete bounded-solver endpoint certificate, adding the final explicit
momentum kick to the paired implicit-loop error budget. -/
structure BoundedScalarSolverEndpointRationalCertificate where
  phase : BoundedScalarSolverPhaseRationalCertificate
  finalUpdate : BoundedScalarAffineUpdateRationalCertificate
  finalMomentumError : ℚ
  phaseError : ℚ
deriving DecidableEq, Repr

namespace BoundedScalarSolverEndpointRationalCertificate

def FinalLinkValid (certificate : BoundedScalarSolverEndpointRationalCertificate) : Prop :=
  match certificate.finalUpdate.sources with
  | .one entry =>
      entry.kind = .position ∧
        entry.certificate.primitive.sincos.input =
          certificate.phase.position.residual.iterate ∧
        entry.certificate.primitive.momentum =
          certificate.phase.half.residual.iterate ∧
        certificate.finalUpdate.affine.base =
          certificate.phase.half.residual.iterate ∧
        certificate.finalUpdate.affine.scale =
          -(certificate.phase.half.epsilon / 2) ∧
        certificate.finalMomentumError =
          certificate.finalUpdate.affine.updateError +
            (1 + |certificate.phase.half.epsilon / 2| * 3) *
              certificate.phase.half.contraction.distanceUpper +
            |certificate.phase.half.epsilon / 2| *
              (18 * (|certificate.phase.half.residual.iterate| +
                certificate.phase.half.contraction.distanceUpper) ^ 2 +
               3 * (|certificate.phase.half.residual.iterate| +
                certificate.phase.half.contraction.distanceUpper)) *
              certificate.phase.positionError ∧
        certificate.phaseError = max certificate.phase.positionError
          certificate.finalMomentumError
  | _ => False

instance (certificate : BoundedScalarSolverEndpointRationalCertificate) :
    Decidable certificate.FinalLinkValid := by
  cases hsources : certificate.finalUpdate.sources <;>
    simp only [FinalLinkValid, hsources] <;> infer_instance

def Valid (certificate : BoundedScalarSolverEndpointRationalCertificate) : Prop :=
  certificate.phase.Valid ∧ certificate.finalUpdate.Valid ∧
    certificate.FinalLinkValid

instance (certificate : BoundedScalarSolverEndpointRationalCertificate) :
    Decidable certificate.Valid := by
  unfold Valid
  infer_instance

def check (certificate : BoundedScalarSolverEndpointRationalCertificate) : Bool :=
  decide certificate.Valid

@[simp] theorem check_eq_true_iff
    (certificate : BoundedScalarSolverEndpointRationalCertificate) :
    certificate.check = true ↔ certificate.Valid := by
  simp [check]

/-- Soundness of the complete endpoint record. It constructs the exact two
implicit fixed points and exact final kick and bounds the returned runtime
phase state in the product max metric. -/
theorem exists_exactEndpoint
    (certificate : BoundedScalarSolverEndpointRationalCertificate)
    (halfEntry first second finalEntry : BoundedScalarCallbackTraceEntry)
    (hvalid : certificate.Valid)
    (hhalfSources : certificate.phase.half.update.sources = .one halfEntry)
    (hpositionSources : certificate.phase.position.update.sources =
      .pair first second)
    (hfinalSources : certificate.finalUpdate.sources = .one finalEntry) :
    ∃ pExact qExact pFinalExact : ℝ,
      Function.IsFixedPt
          (boundedScalarHalfUpdateReal (certificate.phase.half.epsilon : ℝ)
            (halfEntry.certificate.primitive.sincos.input : ℝ)
            (certificate.phase.half.update.affine.base : ℝ)) pExact ∧
        Function.IsFixedPt
          (boundedScalarPositionUpdateReal
            (certificate.phase.position.epsilon : ℝ)
            (certificate.phase.position.update.affine.base : ℝ) pExact) qExact ∧
        pFinalExact = pExact - ((certificate.phase.half.epsilon : ℝ) / 2) *
          boundedScalarPositionDerivativeReal (qExact, pExact) ∧
        dist (certificate.phase.position.residual.iterate : ℝ) qExact ≤
          (certificate.phase.positionError : ℝ) ∧
        dist (certificate.finalUpdate.affine.computedUpdate : ℝ) pFinalExact ≤
          (certificate.finalMomentumError : ℝ) ∧
        dist
          ((certificate.phase.position.residual.iterate : ℝ),
            (certificate.finalUpdate.affine.computedUpdate : ℝ))
          (qExact, pFinalExact) ≤ (certificate.phaseError : ℝ) := by
  rcases hvalid with ⟨hphase, hfinal, hlink⟩
  simp only [FinalLinkValid, hfinalSources] at hlink
  rcases hlink with ⟨hkind, hqLink, hpLink, hbase, hscale,
    hfinalError, hphaseError⟩
  obtain ⟨pExact, qExact, hpFixed, hqFixed, hpError, hqError⟩ :=
    certificate.phase.exists_exactPhase halfEntry first second hphase
      hhalfSources hpositionSources
  let pFinalExact := pExact - ((certificate.phase.half.epsilon : ℝ) / 2) *
    boundedScalarPositionDerivativeReal (qExact, pExact)
  have hupdate : |(certificate.finalUpdate.affine.computedUpdate : ℝ) -
      ((certificate.phase.half.residual.iterate : ℝ) -
        ((certificate.phase.half.epsilon : ℝ) / 2) *
          boundedScalarPositionDerivativeReal
            (certificate.phase.position.residual.iterate,
              certificate.phase.half.residual.iterate))| ≤
      (certificate.finalUpdate.affine.updateError : ℝ) := by
    have := certificate.finalUpdate.exactUpdate_le hfinal
    rw [hfinalSources] at this
    simp only [BoundedScalarAffineCallbackSources.ideal,
      BoundedScalarCallbackTraceEntry.ideal, hkind, hqLink, hpLink] at this
    rw [hbase, hscale] at this
    norm_num at this ⊢
    simpa [sub_eq_add_neg] using this
  have hpNonneg : 0 ≤ (certificate.phase.half.contraction.distanceUpper : ℝ) := by
    exact dist_nonneg.trans hpError
  have hpFinal : dist (certificate.finalUpdate.affine.computedUpdate : ℝ)
      pFinalExact ≤ (certificate.finalMomentumError : ℝ) := by
    rw [Real.dist_eq]
    dsimp only [pFinalExact]
    calc
      _ ≤ (certificate.finalUpdate.affine.updateError : ℝ) +
          (1 + |(certificate.phase.half.epsilon : ℝ) / 2| * 3) *
            certificate.phase.half.contraction.distanceUpper +
          |(certificate.phase.half.epsilon : ℝ) / 2| *
            (18 * (|(certificate.phase.half.residual.iterate : ℝ)| +
              certificate.phase.half.contraction.distanceUpper) ^ 2 +
             3 * (|(certificate.phase.half.residual.iterate : ℝ)| +
              certificate.phase.half.contraction.distanceUpper)) *
            certificate.phase.positionError := by
        exact boundedScalarFinalMomentum_error_le
          (certificate.phase.half.epsilon : ℝ)
          (certificate.phase.half.residual.iterate : ℝ) pExact
          (certificate.phase.position.residual.iterate : ℝ) qExact
          (certificate.finalUpdate.affine.computedUpdate : ℝ)
          hpNonneg hpError hqError hupdate
      _ = (certificate.finalMomentumError : ℝ) := by
        exact_mod_cast hfinalError.symm
  refine ⟨pExact, qExact, pFinalExact, hpFixed, hqFixed, rfl, hqError, hpFinal, ?_⟩
  apply (scalarPhase_dist_le_max hqError hpFinal).trans
  exact_mod_cast hphaseError.symm.le

/-- The endpoint radius is local error against the exact bounded step started
from this record's represented input. This is the form consumed by sequential
trajectory-error propagation. -/
theorem computedEndpoint_dist_certificateStep_le
    (certificate : BoundedScalarSolverEndpointRationalCertificate)
    (halfEntry first second finalEntry : BoundedScalarCallbackTraceEntry)
    (hvalid : certificate.Valid)
    (hhalfSources : certificate.phase.half.update.sources = .one halfEntry)
    (hpositionSources : certificate.phase.position.update.sources =
      .pair first second)
    (hfinalSources : certificate.finalUpdate.sources = .one finalEntry) :
    dist
      ((certificate.phase.position.residual.iterate : ℝ),
        (certificate.finalUpdate.affine.computedUpdate : ℝ))
      (boundedScalarCertificateStepReal
        (certificate.phase.half.epsilon : ℝ)
        (by
          rcases hvalid.1.1 with ⟨_, _, _, _, _, _, hstep, _⟩
          exact_mod_cast hstep)
        ((halfEntry.certificate.primitive.sincos.input : ℝ),
          (certificate.phase.half.update.affine.base : ℝ))) ≤
      (certificate.phaseError : ℝ) := by
  obtain ⟨pExact, qExact, pFinalExact, hpFixed, hqFixed, hpFinalDef, _, _,
      hphase⟩ := certificate.exists_exactEndpoint halfEntry first second
    finalEntry hvalid hhalfSources hpositionSources hfinalSources
  let hstep : |(certificate.phase.half.epsilon : ℝ) / 2| * 3 < 1 := by
    rcases hvalid.1.1 with ⟨_, _, _, _, _, _, hstep, _⟩
    exact_mod_cast hstep
  have hepsilonRat : certificate.phase.position.epsilon =
      certificate.phase.half.epsilon := hvalid.1.2.2.2.2.1
  have hepsilon : (certificate.phase.position.epsilon : ℝ) =
      certificate.phase.half.epsilon := by exact_mod_cast hepsilonRat
  let pSelected :=
      (boundedScalarHalfUpdateReal_contracting
        (certificate.phase.half.epsilon : ℝ)
        (halfEntry.certificate.primitive.sincos.input : ℝ)
        (certificate.phase.half.update.affine.base : ℝ) hstep).fixedPoint
          (boundedScalarHalfUpdateReal
            (certificate.phase.half.epsilon : ℝ)
            (halfEntry.certificate.primitive.sincos.input : ℝ)
            (certificate.phase.half.update.affine.base : ℝ))
  have hpEq : pExact = pSelected :=
    (boundedScalarHalfUpdateReal_contracting
      (certificate.phase.half.epsilon : ℝ)
      (halfEntry.certificate.primitive.sincos.input : ℝ)
      (certificate.phase.half.update.affine.base : ℝ) hstep).fixedPoint_unique
        hpFixed
  rw [hpEq] at hqFixed hpFinalDef
  have hqEq : qExact =
      (boundedScalarPositionUpdateReal_contracting
        (certificate.phase.position.epsilon : ℝ)
        (certificate.phase.position.update.affine.base : ℝ) pSelected
        (by simpa [hepsilon] using hstep)).fixedPoint
          (boundedScalarPositionUpdateReal
            (certificate.phase.position.epsilon : ℝ)
            (certificate.phase.position.update.affine.base : ℝ) pSelected) :=
    (boundedScalarPositionUpdateReal_contracting
      (certificate.phase.position.epsilon : ℝ)
      (certificate.phase.position.update.affine.base : ℝ) pSelected
      (by simpa [hepsilon] using hstep)).fixedPoint_unique hqFixed
  have hinputQ : certificate.phase.position.update.affine.base =
      halfEntry.certificate.primitive.sincos.input := by
    have hsources := hvalid.1.2.2.2.2.2
    simp [BoundedScalarSolverPhaseRationalCertificate.SourcesLinkValid,
      hhalfSources, hpositionSources] at hsources
    exact hsources.1
  have hexact : (qExact, pFinalExact) =
      boundedScalarCertificateStepReal
        (certificate.phase.half.epsilon : ℝ) hstep
        ((halfEntry.certificate.primitive.sincos.input : ℝ),
          (certificate.phase.half.update.affine.base : ℝ)) := by
    apply Prod.ext
    · simpa [boundedScalarCertificateStepReal, pSelected, hinputQ, hepsilon]
        using hqEq
    · simpa [boundedScalarCertificateStepReal, pSelected, hinputQ, hepsilon,
        hqEq] using hpFinalDef
  rwa [← hexact]

/-- Public exact-step form of the local endpoint radius. -/
theorem computedEndpoint_dist_boundedScalarStepReal_le
    (certificate : BoundedScalarSolverEndpointRationalCertificate)
    (halfEntry first second finalEntry : BoundedScalarCallbackTraceEntry)
    (hvalid : certificate.Valid)
    (hhalfSources : certificate.phase.half.update.sources = .one halfEntry)
    (hpositionSources : certificate.phase.position.update.sources =
      .pair first second)
    (hfinalSources : certificate.finalUpdate.sources = .one finalEntry) :
    dist
      ((certificate.phase.position.residual.iterate : ℝ),
        (certificate.finalUpdate.affine.computedUpdate : ℝ))
      (boundedScalarStepReal
        (certificate.phase.half.epsilon : ℝ)
        (by
          rcases hvalid.1.1 with ⟨_, _, _, _, _, _, hstep, _⟩
          exact_mod_cast hstep)
        ((halfEntry.certificate.primitive.sincos.input : ℝ),
          (certificate.phase.half.update.affine.base : ℝ))) ≤
      (certificate.phaseError : ℝ) := by
  simpa only [boundedScalarCertificateStepReal_eq_boundedScalarStepReal] using
    certificate.computedEndpoint_dist_certificateStep_le halfEntry first second
      finalEntry hvalid hhalfSources hpositionSources hfinalSources

/-- Source-independent adapter for sequential records: validity determines all
three callback-source shapes, while the caller supplies only the represented
input state. -/
theorem computedEndpoint_dist_boundedScalarStepReal_le_of_input
    (certificate : BoundedScalarSolverEndpointRationalCertificate)
    (position momentum : ℚ) (hvalid : certificate.Valid)
    (hinput : match certificate.phase.half.update.sources with
      | .one entry =>
          entry.certificate.primitive.sincos.input = position ∧
            certificate.phase.half.update.affine.base = momentum
      | _ => False) :
    dist
      ((certificate.phase.position.residual.iterate : ℝ),
        (certificate.finalUpdate.affine.computedUpdate : ℝ))
      (boundedScalarStepReal
        (certificate.phase.half.epsilon : ℝ)
        (by
          rcases hvalid.1.1 with ⟨_, _, _, _, _, _, hstep, _⟩
          exact_mod_cast hstep)
        ((position : ℝ), (momentum : ℝ))) ≤
      (certificate.phaseError : ℝ) := by
  cases hhalf : certificate.phase.half.update.sources with
  | pair first second => simp [hhalf] at hinput
  | one halfEntry =>
      simp [hhalf] at hinput
      cases hposition : certificate.phase.position.update.sources with
      | one entry =>
          have hpositionValid := hvalid.1.2.1
          have hpositionKind := hvalid.1.2.2.2.1
          rw [BoundedScalarSolverContractionRationalCertificate.Valid] at hpositionValid
          simp [BoundedScalarSolverContractionRationalCertificate.LinkValid,
            hpositionKind, hposition] at hpositionValid
      | pair first second =>
          cases hfinal : certificate.finalUpdate.sources with
          | pair a b => simp [BoundedScalarSolverEndpointRationalCertificate.Valid,
              BoundedScalarSolverEndpointRationalCertificate.FinalLinkValid,
              hfinal] at hvalid
          | one finalEntry =>
              rw [← hinput.1, ← hinput.2]
              exact certificate.computedEndpoint_dist_boundedScalarStepReal_le
                halfEntry first second finalEntry hvalid hhalf hposition hfinal

end BoundedScalarSolverEndpointRationalCertificate

/-- A nonempty sequence of bounded solver records whose rounded output is
the represented input of the next record. This is deliberately stronger than
a list of independently valid endpoint certificates. -/
structure BoundedScalarLinkedSolverTrajectoryRationalCertificate where
  epsilon : ℚ
  initialPosition : ℚ
  initialMomentum : ℚ
  steps : List BoundedScalarSolverEndpointRationalCertificate
deriving DecidableEq, Repr

namespace BoundedScalarLinkedSolverTrajectoryRationalCertificate

def StepInputValid (position momentum : ℚ)
    (step : BoundedScalarSolverEndpointRationalCertificate) : Prop :=
  match step.phase.half.update.sources with
  | .one entry =>
      entry.certificate.primitive.sincos.input = position ∧
        step.phase.half.update.affine.base = momentum
  | _ => False

instance (position momentum : ℚ)
    (step : BoundedScalarSolverEndpointRationalCertificate) :
    Decidable (StepInputValid position momentum step) := by
  cases hsources : step.phase.half.update.sources <;>
    simp only [StepInputValid, hsources] <;> infer_instance

def ValidFrom : ℚ → ℚ → ℚ →
    List BoundedScalarSolverEndpointRationalCertificate → Prop
  | _, _, _, [] => True
  | epsilon, position, momentum, step :: rest =>
      step.Valid ∧ step.phase.half.epsilon = epsilon ∧
        StepInputValid position momentum step ∧
        ValidFrom epsilon step.phase.position.residual.iterate
          step.finalUpdate.affine.computedUpdate rest

instance validFromDecidable (epsilon position momentum : ℚ)
    (steps : List BoundedScalarSolverEndpointRationalCertificate) :
    Decidable (ValidFrom epsilon position momentum steps) := by
  induction steps generalizing position momentum with
  | nil => exact isTrue trivial
  | cons step rest ih =>
      simp only [ValidFrom]
      infer_instance

def Valid
    (certificate : BoundedScalarLinkedSolverTrajectoryRationalCertificate) : Prop :=
  certificate.steps ≠ [] ∧ ValidFrom certificate.epsilon
    certificate.initialPosition certificate.initialMomentum certificate.steps

instance
    (certificate : BoundedScalarLinkedSolverTrajectoryRationalCertificate) :
    Decidable certificate.Valid := by
  unfold Valid
  infer_instance

def check
    (certificate : BoundedScalarLinkedSolverTrajectoryRationalCertificate) : Bool :=
  decide certificate.Valid

@[simp] theorem check_eq_true_iff
    (certificate : BoundedScalarLinkedSolverTrajectoryRationalCertificate) :
    certificate.check = true ↔ certificate.Valid := by
  simp [check]

theorem validFrom_tail
    {epsilon position momentum : ℚ}
    {step : BoundedScalarSolverEndpointRationalCertificate} {rest}
    (hvalid : ValidFrom epsilon position momentum (step :: rest)) :
    ValidFrom epsilon step.phase.position.residual.iterate
      step.finalUpdate.affine.computedUpdate rest := hvalid.2.2.2

theorem validFrom_input
    {epsilon position momentum : ℚ}
    {step : BoundedScalarSolverEndpointRationalCertificate} {rest}
    (hvalid : ValidFrom epsilon position momentum (step :: rest)) :
    StepInputValid position momentum step := hvalid.2.2.1

noncomputable def finalState : ℚ → ℚ →
    List BoundedScalarSolverEndpointRationalCertificate → ℝ × ℝ
  | position, momentum, [] => (position, momentum)
  | _, _, step :: rest => finalState step.phase.position.residual.iterate
      step.finalUpdate.affine.computedUpdate rest

noncomputable def propagatedError (K : NNReal) : ℝ →
    List BoundedScalarSolverEndpointRationalCertificate → ℝ
  | error, [] => error
  | error, step :: rest =>
      propagatedError K ((step.phaseError : ℝ) + K * error) rest

/-- Conditional multi-step closure. Once the exact bounded step has a valid
Lipschitz constant on the trajectory region, a linked list of local solver
certificates bounds its rounded final state against one genuine exact orbit.
The initial error parameter also supports chaining from an already uncertain
trajectory point. -/
theorem finalState_dist_iterate_le
    (epsilon position momentum : ℚ) (steps)
    (hvalid : ValidFrom epsilon position momentum steps)
    (hstep : |(epsilon : ℝ) / 2| * 3 < 1)
    (K : NNReal) (hLipschitz : LipschitzWith K
      (boundedScalarStepReal (epsilon : ℝ) hstep))
    (ideal : ℝ × ℝ) (initialError : ℝ)
    (hinitial : dist ((position : ℝ), (momentum : ℝ)) ideal ≤ initialError) :
    dist (finalState position momentum steps)
      (((boundedScalarStepReal (epsilon : ℝ) hstep)^[steps.length]) ideal) ≤
        propagatedError K initialError steps := by
  induction steps generalizing position momentum ideal initialError with
  | nil => simpa [finalState, propagatedError] using hinitial
  | cons current rest ih =>
      have hcurrent := hvalid.1
      have hepsilon := hvalid.2.1
      have hinput := hvalid.2.2.1
      have htail := hvalid.2.2.2
      let roundedNext : ℝ × ℝ :=
        ((current.phase.position.residual.iterate : ℝ),
          (current.finalUpdate.affine.computedUpdate : ℝ))
      have hlocal : dist roundedNext
          (boundedScalarStepReal (epsilon : ℝ) hstep
            ((position : ℝ), (momentum : ℝ))) ≤
          (current.phaseError : ℝ) := by
        have h := current.computedEndpoint_dist_boundedScalarStepReal_le_of_input
          position momentum hcurrent hinput
        simpa only [hepsilon, Subsingleton.elim] using h
      have hnext : dist roundedNext
          (boundedScalarStepReal (epsilon : ℝ) hstep ideal) ≤
          (current.phaseError : ℝ) + K * initialError := by
        calc
          _ ≤ dist roundedNext
                (boundedScalarStepReal (epsilon : ℝ) hstep
                  ((position : ℝ), (momentum : ℝ))) +
              dist
                (boundedScalarStepReal (epsilon : ℝ) hstep
                  ((position : ℝ), (momentum : ℝ)))
                (boundedScalarStepReal (epsilon : ℝ) hstep ideal) :=
            dist_triangle _ _ _
          _ ≤ (current.phaseError : ℝ) +
              K * dist ((position : ℝ), (momentum : ℝ)) ideal :=
            add_le_add hlocal (hLipschitz.dist_le_mul _ _)
          _ ≤ _ := by gcongr
      have hrest := ih
        (position := current.phase.position.residual.iterate)
        (momentum := current.finalUpdate.affine.computedUpdate)
        (ideal := boundedScalarStepReal (epsilon : ℝ) hstep ideal)
        (initialError := (current.phaseError : ℝ) + (K : ℝ) * initialError)
        htail hnext
      simpa only [finalState, propagatedError, List.length_cons,
        Function.iterate_succ_apply] using hrest

end BoundedScalarLinkedSolverTrajectoryRationalCertificate

/-- A checked bounded-Hamiltonian evaluation at the rounded endpoint, composed
with the complete solver endpoint radius. -/
structure BoundedScalarEndpointEnergyRationalCertificate where
  solver : BoundedScalarSolverEndpointRationalCertificate
  evaluation : BoundedScalarCallbackRationalCertificate
  totalEnergyError : ℚ
deriving DecidableEq, Repr

namespace BoundedScalarEndpointEnergyRationalCertificate

def Valid (certificate : BoundedScalarEndpointEnergyRationalCertificate) : Prop :=
  certificate.solver.Valid ∧ certificate.evaluation.Valid ∧
    certificate.evaluation.primitive.sincos.input =
      certificate.solver.phase.position.residual.iterate ∧
    certificate.evaluation.primitive.momentum =
      certificate.solver.finalUpdate.affine.computedUpdate ∧
    certificate.totalEnergyError = certificate.evaluation.primitive.sqrtError +
      3 * certificate.solver.finalMomentumError +
      (|certificate.solver.finalUpdate.affine.computedUpdate| +
        certificate.solver.finalMomentumError) *
          certificate.solver.phase.positionError

instance (certificate : BoundedScalarEndpointEnergyRationalCertificate) :
    Decidable certificate.Valid := by
  unfold Valid
  infer_instance

def check (certificate : BoundedScalarEndpointEnergyRationalCertificate) : Bool :=
  decide certificate.Valid

@[simp] theorem check_eq_true_iff
    (certificate : BoundedScalarEndpointEnergyRationalCertificate) :
    certificate.check = true ↔ certificate.Valid := by
  simp [check]

/-- The maintained endpoint evaluation approximates the bounded Hamiltonian
at the exact generalized-leapfrog endpoint constructed by the solver record. -/
theorem exists_exactEndpoint_energy_approximates
    (certificate : BoundedScalarEndpointEnergyRationalCertificate)
    (halfEntry first second finalEntry : BoundedScalarCallbackTraceEntry)
    (hvalid : certificate.Valid)
    (hhalfSources : certificate.solver.phase.half.update.sources = .one halfEntry)
    (hpositionSources : certificate.solver.phase.position.update.sources =
      .pair first second)
    (hfinalSources : certificate.solver.finalUpdate.sources = .one finalEntry) :
    ∃ pExact qExact pFinalExact : ℝ,
      Function.IsFixedPt
          (boundedScalarHalfUpdateReal
            (certificate.solver.phase.half.epsilon : ℝ)
            (halfEntry.certificate.primitive.sincos.input : ℝ)
            (certificate.solver.phase.half.update.affine.base : ℝ)) pExact ∧
        Function.IsFixedPt
          (boundedScalarPositionUpdateReal
            (certificate.solver.phase.position.epsilon : ℝ)
            (certificate.solver.phase.position.update.affine.base : ℝ) pExact)
          qExact ∧
        pFinalExact = pExact -
          ((certificate.solver.phase.half.epsilon : ℝ) / 2) *
            boundedScalarPositionDerivativeReal (qExact, pExact) ∧
        Approximates
          (certificate.evaluation.primitive.sqrtCertificate.computed : ℝ)
          (Real.sqrt (1 + ((2 + Real.sin qExact) * pFinalExact) ^ 2))
          (certificate.totalEnergyError : ℝ) := by
  rcases hvalid with ⟨hsolver, hevaluation, hqLink, hpLink, htotal⟩
  obtain ⟨pExact, qExact, pFinalExact, hpFixed, hqFixed, hpFinalDef,
      hqError, hpError, hphase⟩ :=
    certificate.solver.exists_exactEndpoint halfEntry first second
    finalEntry hsolver hhalfSources hpositionSources hfinalSources
  have heval := certificate.evaluation.primitive.computedSqrt_approximates
    hevaluation.1
  rw [hqLink, hpLink] at heval
  have hpExactAbs : |pFinalExact| ≤
      |(certificate.solver.finalUpdate.affine.computedUpdate : ℝ)| +
        certificate.solver.finalMomentumError := by
    calc
      |pFinalExact| =
          |(certificate.solver.finalUpdate.affine.computedUpdate : ℝ) +
            (pFinalExact - certificate.solver.finalUpdate.affine.computedUpdate)| :=
        congrArg abs (by ring)
      _ ≤ |(certificate.solver.finalUpdate.affine.computedUpdate : ℝ)| +
            |pFinalExact - certificate.solver.finalUpdate.affine.computedUpdate| :=
        abs_add_le _ _
      _ ≤ _ := by
        have := hpError
        rw [Real.dist_eq] at this
        linarith [abs_sub_comm pFinalExact
          (certificate.solver.finalUpdate.affine.computedUpdate : ℝ)]
  have hmomentum := (boundedScalarHamiltonian_lipschitz_momentum
    (fun _ => (certificate.solver.phase.position.residual.iterate : ℝ))).dist_le_mul
      (fun _ => (certificate.solver.finalUpdate.affine.computedUpdate : ℝ))
      (fun _ => pFinalExact)
  rw [Real.dist_eq, dist_eq_norm, norm_pi_unit] at hmomentum
  have hposition := (boundedScalarHamiltonian_lipschitz_position
    (fun _ => pFinalExact)).dist_le_mul
      (fun _ => (certificate.solver.phase.position.residual.iterate : ℝ))
      (fun _ => qExact)
  rw [Real.dist_eq, dist_eq_norm, norm_pi_unit] at hposition
  have htransport :
      |Real.sqrt (1 + ((2 + Real.sin
          (certificate.solver.phase.position.residual.iterate : ℝ)) *
            (certificate.solver.finalUpdate.affine.computedUpdate : ℝ)) ^ 2) -
        Real.sqrt (1 + ((2 + Real.sin qExact) * pFinalExact) ^ 2)| ≤
      3 * certificate.solver.finalMomentumError +
        (|(certificate.solver.finalUpdate.affine.computedUpdate : ℝ)| +
          certificate.solver.finalMomentumError) *
            certificate.solver.phase.positionError := by
    calc
      _ ≤ |Real.sqrt (1 + ((2 + Real.sin
              (certificate.solver.phase.position.residual.iterate : ℝ)) *
                (certificate.solver.finalUpdate.affine.computedUpdate : ℝ)) ^ 2) -
            Real.sqrt (1 + ((2 + Real.sin
              (certificate.solver.phase.position.residual.iterate : ℝ)) *
                pFinalExact) ^ 2)| +
          |Real.sqrt (1 + ((2 + Real.sin
              (certificate.solver.phase.position.residual.iterate : ℝ)) *
                pFinalExact) ^ 2) -
            Real.sqrt (1 + ((2 + Real.sin qExact) * pFinalExact) ^ 2)| := by
        rw [show _ - Real.sqrt (1 + ((2 + Real.sin qExact) * pFinalExact) ^ 2) =
          (_ - Real.sqrt (1 + ((2 + Real.sin
            (certificate.solver.phase.position.residual.iterate : ℝ)) *
              pFinalExact) ^ 2)) +
          (Real.sqrt (1 + ((2 + Real.sin
            (certificate.solver.phase.position.residual.iterate : ℝ)) *
              pFinalExact) ^ 2) -
            Real.sqrt (1 + ((2 + Real.sin qExact) * pFinalExact) ^ 2)) by ring]
        exact abs_add_le _ _
      _ ≤ 3 * dist
            (certificate.solver.finalUpdate.affine.computedUpdate : ℝ)
            pFinalExact + |pFinalExact| * dist
              (certificate.solver.phase.position.residual.iterate : ℝ) qExact :=
        add_le_add hmomentum hposition
      _ ≤ _ := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hpError (by norm_num)
        · calc
            |pFinalExact| * dist
                (certificate.solver.phase.position.residual.iterate : ℝ) qExact ≤
              (|(certificate.solver.finalUpdate.affine.computedUpdate : ℝ)| +
                certificate.solver.finalMomentumError) *
                dist (certificate.solver.phase.position.residual.iterate : ℝ)
                  qExact := mul_le_mul_of_nonneg_right hpExactAbs dist_nonneg
            _ ≤ _ := mul_le_mul_of_nonneg_left hqError
              (add_nonneg (abs_nonneg _)
                (dist_nonneg.trans hpError))
  refine ⟨pExact, qExact, pFinalExact, hpFixed, hqFixed, hpFinalDef, ?_⟩
  have heval' : Approximates
      (certificate.evaluation.primitive.sqrtCertificate.computed : ℝ)
      (Real.sqrt (1 + ((2 + Real.sin
        (certificate.solver.phase.position.residual.iterate : ℝ)) *
          (certificate.solver.finalUpdate.affine.computedUpdate : ℝ)) ^ 2))
      (certificate.evaluation.primitive.sqrtError : ℝ) := by
    simpa [boundedScalarScale] using heval
  have htransport' : Approximates
      (Real.sqrt (1 + ((2 + Real.sin
        (certificate.solver.phase.position.residual.iterate : ℝ)) *
          (certificate.solver.finalUpdate.affine.computedUpdate : ℝ)) ^ 2))
      (Real.sqrt (1 + ((2 + Real.sin qExact) * pFinalExact) ^ 2))
      ((3 * certificate.solver.finalMomentumError +
        (|certificate.solver.finalUpdate.affine.computedUpdate| +
          certificate.solver.finalMomentumError) *
            certificate.solver.phase.positionError : ℚ) : ℝ) := by
    rw [Approximates]
    exact_mod_cast htransport
  have hcombined := heval'.trans htransport'
  rw [show (certificate.totalEnergyError : ℝ) =
      (certificate.evaluation.primitive.sqrtError : ℝ) +
        ((3 * certificate.solver.finalMomentumError +
          (|certificate.solver.finalUpdate.affine.computedUpdate| +
            certificate.solver.finalMomentumError) *
              certificate.solver.phase.positionError : ℚ) : ℝ) by
    exact_mod_cast (show certificate.totalEnergyError =
      certificate.evaluation.primitive.sqrtError +
        (3 * certificate.solver.finalMomentumError +
          (|certificate.solver.finalUpdate.affine.computedUpdate| +
            certificate.solver.finalMomentumError) *
              certificate.solver.phase.positionError) by
      rw [htotal]
      ring)]
  exact hcombined

end BoundedScalarEndpointEnergyRationalCertificate

/-- The two energies used by a one-step bounded multinomial trajectory.  The
initial callback is linked to the exact input of the generalized-leapfrog
record, while the final callback is transported to the exact endpoint by the
complete solver certificate. -/
structure BoundedScalarTwoEndpointEnergyRationalCertificate where
  initial : BoundedScalarCallbackRationalCertificate
  final : BoundedScalarEndpointEnergyRationalCertificate
  commonError : ℚ
deriving DecidableEq, Repr

namespace BoundedScalarTwoEndpointEnergyRationalCertificate

def InitialLinkValid
    (certificate : BoundedScalarTwoEndpointEnergyRationalCertificate) : Prop :=
  match certificate.final.solver.phase.half.update.sources with
  | .one entry =>
      certificate.initial.primitive.sincos.input =
          entry.certificate.primitive.sincos.input ∧
        certificate.initial.primitive.momentum =
          certificate.final.solver.phase.half.update.affine.base
  | _ => False

instance (certificate : BoundedScalarTwoEndpointEnergyRationalCertificate) :
    Decidable certificate.InitialLinkValid := by
  cases hsources : certificate.final.solver.phase.half.update.sources <;>
    simp only [InitialLinkValid, hsources] <;> infer_instance

def Valid
    (certificate : BoundedScalarTwoEndpointEnergyRationalCertificate) : Prop :=
  certificate.initial.Valid ∧ certificate.final.Valid ∧
    certificate.InitialLinkValid ∧
    certificate.commonError = max certificate.initial.primitive.sqrtError
      certificate.final.totalEnergyError

instance (certificate : BoundedScalarTwoEndpointEnergyRationalCertificate) :
    Decidable certificate.Valid := by
  unfold Valid
  infer_instance

def check
    (certificate : BoundedScalarTwoEndpointEnergyRationalCertificate) : Bool :=
  decide certificate.Valid

@[simp] theorem check_eq_true_iff
    (certificate : BoundedScalarTwoEndpointEnergyRationalCertificate) :
    certificate.check = true ↔ certificate.Valid := by
  simp [check]

def computedEnergy
    (certificate : BoundedScalarTwoEndpointEnergyRationalCertificate) :
    Fin 2 → ℝ
  | ⟨0, _⟩ => certificate.initial.primitive.sqrtCertificate.computed
  | ⟨1, _⟩ => certificate.final.evaluation.primitive.sqrtCertificate.computed

noncomputable def idealEnergy (initialQ initialP finalQ finalP : ℝ) : Fin 2 → ℝ
  | ⟨0, _⟩ => Real.sqrt (1 + ((2 + Real.sin initialQ) * initialP) ^ 2)
  | ⟨1, _⟩ => Real.sqrt (1 + ((2 + Real.sin finalQ) * finalP) ^ 2)

/-- A valid record constructs one exact generalized-leapfrog endpoint and a
single common error radius for both energies in the actual two-point orbit.
This is the missing trajectory link needed before stabilized multinomial
selection can be applied. -/
theorem exists_exactEndpoint_energy_approximates
    (certificate : BoundedScalarTwoEndpointEnergyRationalCertificate)
    (halfEntry first second finalEntry : BoundedScalarCallbackTraceEntry)
    (hvalid : certificate.Valid)
    (hhalfSources : certificate.final.solver.phase.half.update.sources =
      .one halfEntry)
    (hpositionSources : certificate.final.solver.phase.position.update.sources =
      .pair first second)
    (hfinalSources : certificate.final.solver.finalUpdate.sources =
      .one finalEntry) :
    ∃ pExact qExact pFinalExact : ℝ,
      Function.IsFixedPt
          (boundedScalarHalfUpdateReal
            (certificate.final.solver.phase.half.epsilon : ℝ)
            (halfEntry.certificate.primitive.sincos.input : ℝ)
            (certificate.final.solver.phase.half.update.affine.base : ℝ))
          pExact ∧
        Function.IsFixedPt
          (boundedScalarPositionUpdateReal
            (certificate.final.solver.phase.position.epsilon : ℝ)
            (certificate.final.solver.phase.position.update.affine.base : ℝ)
            pExact) qExact ∧
        pFinalExact = pExact -
          ((certificate.final.solver.phase.half.epsilon : ℝ) / 2) *
            boundedScalarPositionDerivativeReal (qExact, pExact) ∧
        ∀ i, Approximates (certificate.computedEnergy i)
          (idealEnergy
            (halfEntry.certificate.primitive.sincos.input : ℝ)
            (certificate.final.solver.phase.half.update.affine.base : ℝ)
            qExact pFinalExact i)
          (certificate.commonError : ℝ) := by
  rcases hvalid with ⟨hinitial, hfinal, hlink, hcommon⟩
  obtain ⟨pExact, qExact, pFinalExact, hpFixed, hqFixed, hpFinal,
      hfinalEnergy⟩ :=
    certificate.final.exists_exactEndpoint_energy_approximates halfEntry first
      second finalEntry hfinal hhalfSources hpositionSources hfinalSources
  have hinitialLink :
      certificate.initial.primitive.sincos.input =
          halfEntry.certificate.primitive.sincos.input ∧
        certificate.initial.primitive.momentum =
          certificate.final.solver.phase.half.update.affine.base := by
    simpa [InitialLinkValid, hhalfSources] using hlink
  have hinitialEnergy :=
    certificate.initial.primitive.computedSqrt_approximates hinitial.1
  refine ⟨pExact, qExact, pFinalExact, hpFixed, hqFixed, hpFinal, ?_⟩
  intro i
  fin_cases i
  · apply (show Approximates
        (certificate.initial.primitive.sqrtCertificate.computed : ℝ)
        (Real.sqrt (1 + ((2 + Real.sin
          (halfEntry.certificate.primitive.sincos.input : ℝ)) *
            (certificate.final.solver.phase.half.update.affine.base : ℝ)) ^ 2))
        (certificate.initial.primitive.sqrtError : ℝ) by
      simpa [boundedScalarScale, hinitialLink.1, hinitialLink.2] using
        hinitialEnergy).mono
    exact_mod_cast (show certificate.initial.primitive.sqrtError ≤
        certificate.commonError by rw [hcommon]; exact le_max_left _ _)
  · apply hfinalEnergy.mono
    exact_mod_cast (show certificate.final.totalEnergyError ≤
        certificate.commonError by rw [hcommon]; exact le_max_right _ _)

/-- Once concrete exponential, prefix-sum, scaled-draw, and RNG records are
supplied, the linked two-endpoint energy theorem feeds the same generic
arithmetic-aware multinomial-selection certificate as the SoftAbs trajectory
layer. -/
noncomputable def selectionCertificateWithArithmetic
    (certificate : BoundedScalarTwoEndpointEnergyRationalCertificate)
    (initialQ initialP finalQ finalP : ℝ)
    (computedWeight : Fin 2 → ℝ)
    (arithmetic : MultinomialCumulativeArithmeticCertificate computedWeight)
    (computedDraw computedUnit idealUnit : ℝ)
    (expError multiplicationError unitError : ℝ)
    (hexpNonneg : 0 ≤ expError)
    (henergy : ∀ i, Approximates (certificate.computedEnergy i)
      (idealEnergy initialQ initialP finalQ finalP i)
      (certificate.commonError : ℝ))
    (hexp : ∀ i, Approximates (computedWeight i)
      (stabilizedBoltzmannWeight certificate.computedEnergy i) expError)
    (hmul : Approximates computedDraw
      (computedUnit * arithmetic.computedTotal) multiplicationError)
    (hunit : Approximates computedUnit idealUnit unitError) :
    MultinomialSelectionCertificate :=
  stabilizedMultinomialSelectionCertificateWithArithmetic
    certificate.computedEnergy
    (idealEnergy initialQ initialP finalQ finalP) computedWeight arithmetic
    computedDraw computedUnit idealUnit certificate.commonError expError
    multiplicationError unitError (henergy 0).nonneg hexpNonneg henergy hexp
    hmul hunit

theorem finiteMaximum_fin_two (values : Fin 2 → ℝ) :
    finiteMaximum values = max (values 0) (values 1) := by
  apply le_antisymm
  · unfold finiteMaximum
    apply Finset.sup'_le
    intro i _
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  · apply max_le
    · exact Finset.le_sup' values (Finset.mem_univ 0)
    · exact Finset.le_sup' values (Finset.mem_univ 1)

end BoundedScalarTwoEndpointEnergyRationalCertificate

/-- The two checked maximum-stabilized exponentials attached to a linked
bounded one-step trajectory.  Validity checks their arguments against the
actual two computed endpoint energies, closing a linkage that separate local
`exp` records would not establish. -/
structure BoundedScalarTwoEndpointWeightRationalCertificate where
  energy : BoundedScalarTwoEndpointEnergyRationalCertificate
  first : ExpNonpositiveTransportRationalCertificate
  second : ExpNonpositiveTransportRationalCertificate
deriving DecidableEq, Repr

namespace BoundedScalarTwoEndpointWeightRationalCertificate

def computedEnergyRat
    (certificate : BoundedScalarTwoEndpointWeightRationalCertificate) :
    Fin 2 → ℚ
  | ⟨0, _⟩ => certificate.energy.initial.primitive.sqrtCertificate.computed
  | ⟨1, _⟩ =>
      certificate.energy.final.evaluation.primitive.sqrtCertificate.computed

def stabilizedInput
    (certificate : BoundedScalarTwoEndpointWeightRationalCertificate)
    (i : Fin 2) : ℚ :=
  -certificate.computedEnergyRat i -
    max (-certificate.computedEnergyRat 0) (-certificate.computedEnergyRat 1)

def Valid
    (certificate : BoundedScalarTwoEndpointWeightRationalCertificate) : Prop :=
  certificate.energy.Valid ∧ certificate.first.Valid ∧
    certificate.second.Valid ∧
    certificate.first.idealInput = certificate.stabilizedInput 0 ∧
    certificate.second.idealInput = certificate.stabilizedInput 1

instance (certificate : BoundedScalarTwoEndpointWeightRationalCertificate) :
    Decidable certificate.Valid := by
  unfold Valid
  infer_instance

def check
    (certificate : BoundedScalarTwoEndpointWeightRationalCertificate) : Bool :=
  decide certificate.Valid

@[simp] theorem check_eq_true_iff
    (certificate : BoundedScalarTwoEndpointWeightRationalCertificate) :
    certificate.check = true ↔ certificate.Valid := by
  simp [check]

def weight
    (certificate : BoundedScalarTwoEndpointWeightRationalCertificate) :
    Fin 2 → ExpNonpositiveTransportRationalCertificate
  | ⟨0, _⟩ => certificate.first
  | ⟨1, _⟩ => certificate.second

noncomputable def computedWeight
    (certificate : BoundedScalarTwoEndpointWeightRationalCertificate) :
    Fin 2 → ℝ := fun i => (certificate.weight i).localCertificate.computed

noncomputable def commonWeightError
    (certificate : BoundedScalarTwoEndpointWeightRationalCertificate) : ℝ :=
  max ((certificate.first.localCertificate.error : ℝ) +
      certificate.first.inputError)
    ((certificate.second.localCertificate.error : ℝ) +
      certificate.second.inputError)

theorem weight_approximates
    (certificate : BoundedScalarTwoEndpointWeightRationalCertificate)
    (hvalid : certificate.Valid) (i : Fin 2) :
    Approximates (certificate.computedWeight i)
      (stabilizedBoltzmannWeight certificate.energy.computedEnergy i)
      certificate.commonWeightError := by
  have hmaximum : finiteMaximum (fun j =>
      -certificate.energy.computedEnergy j) =
      max (-certificate.energy.computedEnergy 0)
        (-certificate.energy.computedEnergy 1) :=
    BoundedScalarTwoEndpointEnergyRationalCertificate.finiteMaximum_fin_two _
  fin_cases i
  · have hlink : (certificate.first.idealInput : ℝ) =
        -certificate.energy.computedEnergy 0 -
          finiteMaximum (fun j => -certificate.energy.computedEnergy j) := by
      rw [hvalid.2.2.2.1, stabilizedInput, hmaximum]
      norm_num [computedEnergyRat,
        BoundedScalarTwoEndpointEnergyRationalCertificate.computedEnergy]
    exact (certificate.first.stabilizedBoltzmannWeight_approximates
      certificate.energy.computedEnergy 0 hvalid.2.1 hlink).mono
        (le_max_left _ _)
  · have hlink : (certificate.second.idealInput : ℝ) =
        -certificate.energy.computedEnergy 1 -
          finiteMaximum (fun j => -certificate.energy.computedEnergy j) := by
      rw [hvalid.2.2.2.2, stabilizedInput, hmaximum]
      norm_num [computedEnergyRat,
        BoundedScalarTwoEndpointEnergyRationalCertificate.computedEnergy]
    exact (certificate.second.stabilizedBoltzmannWeight_approximates
      certificate.energy.computedEnergy 1 hvalid.2.2.1 hlink).mono
        (le_max_right _ _)

theorem commonWeightError_nonneg
    (certificate : BoundedScalarTwoEndpointWeightRationalCertificate)
    (hvalid : certificate.Valid) : 0 ≤ certificate.commonWeightError :=
  (certificate.weight_approximates hvalid 0).nonneg

/-- Complete arithmetic-aware selection certificate for the linked bounded
trajectory. Only the already explicit endpoint-energy soundness premise and
the final RNG approximation remain outside this checked weight record. -/
noncomputable def selectionCertificateWithArithmetic
    (certificate : BoundedScalarTwoEndpointWeightRationalCertificate)
    (hvalid : certificate.Valid) (initialQ initialP finalQ finalP : ℝ)
    (arithmetic : MultinomialCumulativeArithmeticCertificate
      certificate.computedWeight)
    (computedDraw computedUnit idealUnit : ℝ)
    (multiplicationError unitError : ℝ)
    (henergy : ∀ i, Approximates (certificate.energy.computedEnergy i)
      (BoundedScalarTwoEndpointEnergyRationalCertificate.idealEnergy
        initialQ initialP finalQ finalP i)
      (certificate.energy.commonError : ℝ))
    (hmul : Approximates computedDraw
      (computedUnit * arithmetic.computedTotal) multiplicationError)
    (hunit : Approximates computedUnit idealUnit unitError) :
    MultinomialSelectionCertificate :=
  certificate.energy.selectionCertificateWithArithmetic initialQ initialP
    finalQ finalP certificate.computedWeight arithmetic computedDraw
    computedUnit idealUnit certificate.commonWeightError multiplicationError
    unitError (certificate.commonWeightError_nonneg hvalid) henergy
    (certificate.weight_approximates hvalid) hmul hunit

end BoundedScalarTwoEndpointWeightRationalCertificate

/-- Ordered proof-bearing callback coverage for an entire scalar reference
solve. Validity requires every recorded invocation to carry a sound
per-execution certificate. -/
structure BoundedScalarCallbackTraceRationalCertificate where
  halfIterations : ℕ
  positionIterations : ℕ
  entries : List BoundedScalarCallbackTraceEntry
deriving DecidableEq, Repr

namespace BoundedScalarCallbackTraceRationalCertificate

def expectedKinds (trace : BoundedScalarCallbackTraceRationalCertificate) :
    List BoundedScalarCallbackKind :=
  List.replicate trace.halfIterations .position ++
    [.momentum] ++ List.replicate trace.positionIterations .momentum ++
    [.position, .momentum, .position]

def Valid (trace : BoundedScalarCallbackTraceRationalCertificate) : Prop :=
  (∀ entry ∈ trace.entries, entry.Valid) ∧
    trace.entries.map (·.kind) = trace.expectedKinds

instance (trace : BoundedScalarCallbackTraceRationalCertificate) :
    Decidable trace.Valid := by
  unfold Valid
  infer_instance

def check (trace : BoundedScalarCallbackTraceRationalCertificate) : Bool :=
  decide trace.Valid

@[simp] theorem check_eq_true_iff
    (trace : BoundedScalarCallbackTraceRationalCertificate) :
    trace.check = true ↔ trace.Valid := by
  simp [check]

theorem entry_approximates
    (trace : BoundedScalarCallbackTraceRationalCertificate)
    (hvalid : trace.Valid) {entry : BoundedScalarCallbackTraceEntry}
    (hentry : entry ∈ trace.entries) :
    Approximates entry.computed entry.ideal entry.error :=
  entry.approximates (hvalid.1 entry hentry)

theorem entry_count
    (trace : BoundedScalarCallbackTraceRationalCertificate)
    (hvalid : trace.Valid) :
    trace.entries.length = trace.halfIterations + trace.positionIterations + 4 := by
  have hlength := congrArg List.length hvalid.2
  simpa [expectedKinds, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlength

end BoundedScalarCallbackTraceRationalCertificate

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
