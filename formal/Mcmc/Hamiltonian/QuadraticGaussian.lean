import Mcmc.Hamiltonian.Assumptions
import Mcmc.Hamiltonian.LeapfrogContraction
import Mcmc.Hamiltonian.LocalContractivity
import Mcmc.Hamiltonian.TrajectoryWeightBounds
import Mcmc.Kernel.GaussianRandomWalk
import Mcmc.Kernel.MeetingDrift
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Int.NatAbs
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Order.Filter.Finite

/-!
# Quadratic Gaussian specialization

This module specializes the leapfrog algebra to the standard Gaussian
potential `U(q) = ‖q‖₂² / 2`, whose gradient is the identity. The resulting
exact one-step energy-error formula is a validated numerical-analysis test
case for the general multinomial-HMC trajectory bounds.
-/

open scoped BigOperators
open MeasureTheory

namespace Mcmc.Hamiltonian

variable {ι : Type*} [Fintype ι]

/-- The standard centered Gaussian potential `U(q) = ‖q‖₂² / 2`. -/
noncomputable def standardQuadraticPotential (q : Position ι) : ℝ :=
  kineticEnergy q

/-- The gradient of `standardQuadraticPotential`. -/
def standardQuadraticGradient (q : Position ι) : Position ι := q

omit [Fintype ι] in
/-- The position component of one leapfrog step for the standard quadratic
potential is the exact linear harmonic-oscillator update. -/
theorem standardQuadratic_leapfrog_fst (ε : ℝ)
    (q : Position ι) (p : Momentum ι) :
    (leapfrog standardQuadraticGradient ε (q, p)).1 =
      (1 - ε ^ 2 / 2) • q + ε • p := by
  funext i
  simp [leapfrog, halfKick, drift, standardQuadraticGradient]
  ring

omit [Fintype ι] in
/-- At step size `sqrt 2`, the standard-quadratic leapfrog position forgets
the incoming position and is exactly the rescaled momentum. -/
theorem standardQuadratic_leapfrog_sqrtTwo_fst
    (q : Position ι) (p : Momentum ι) :
    (leapfrog standardQuadraticGradient (Real.sqrt 2) (q, p)).1 =
      Real.sqrt 2 • p := by
  rw [standardQuadratic_leapfrog_fst]
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  rw [hsqrt]
  norm_num

omit [Fintype ι] in
/-- The corresponding one-step negative-time position at step size `sqrt 2`
is the oppositely rescaled momentum. -/
theorem standardQuadratic_leapfrog_negSqrtTwo_fst
    (q : Position ι) (p : Momentum ι) :
    (leapfrog standardQuadraticGradient (-(Real.sqrt 2)) (q, p)).1 =
      -(Real.sqrt 2) • p := by
  rw [standardQuadratic_leapfrog_fst]
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  rw [neg_sq, hsqrt]
  norm_num

omit [Fintype ι] in
/-- Every position in a two-point, randomly rooted trajectory at step size
`sqrt 2` is exactly either the current position or one of the two rescaled
momentum positions. -/
theorem standardQuadratic_offsetLeapfrogTrajectory_sqrtTwo_fst
    (origin selected : Fin 2) (q : Position ι) (p : Momentum ι) :
    (offsetLeapfrogTrajectory standardQuadraticGradient (Real.sqrt 2)
      origin (q, p) selected).1 = q ∨
      (offsetLeapfrogTrajectory standardQuadraticGradient (Real.sqrt 2)
        origin (q, p) selected).1 = Real.sqrt 2 • p ∨
      (offsetLeapfrogTrajectory standardQuadraticGradient (Real.sqrt 2)
        origin (q, p) selected).1 = -(Real.sqrt 2) • p := by
  fin_cases origin <;> fin_cases selected
  · simp [offsetLeapfrogTrajectory]
  · right
    left
    simpa [offsetLeapfrogTrajectory] using
      standardQuadratic_leapfrog_sqrtTwo_fst q p
  · right
    right
    simpa [offsetLeapfrogTrajectory] using
      standardQuadratic_leapfrog_negSqrtTwo_fst q p
  · simp [offsetLeapfrogTrajectory]

/-- A proper, everywhere-finite Lyapunov candidate on finite-dimensional
position space.  The additive constant matches the paper's convention
`V ≥ 1`, while metric distance makes compactness of paired sublevels direct. -/
noncomputable def standardDistanceLyapunov (q : Position ι) : ENNReal :=
  ENNReal.ofReal (1 + dist q 0)

theorem continuous_standardDistanceLyapunov :
    Continuous (standardDistanceLyapunov : Position ι → ENNReal) := by
  unfold standardDistanceLyapunov
  exact ENNReal.continuous_ofReal.comp
    (continuous_const.add (continuous_id.dist continuous_const))

theorem measurable_standardDistanceLyapunov :
    Measurable (standardDistanceLyapunov : Position ι → ENNReal) :=
  continuous_standardDistanceLyapunov.measurable

theorem one_le_standardDistanceLyapunov (q : Position ι) :
    1 ≤ standardDistanceLyapunov q := by
  rw [standardDistanceLyapunov, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal
    (by linarith [show 0 ≤ dist q 0 from dist_nonneg])

theorem standardDistanceLyapunov_ne_top (q : Position ι) :
    standardDistanceLyapunov q ≠ ⊤ := by
  exact ENNReal.ofReal_ne_top

/-- Every deterministic initialization has the finite moment required by
Xu et al.'s Theorem 4.1. -/
theorem lintegral_standardDistanceLyapunov_dirac_ne_top
    (q₀ : Position ι) :
    (∫⁻ q, standardDistanceLyapunov q ∂Measure.dirac q₀) ≠ ⊤ := by
  rw [lintegral_dirac' q₀ measurable_standardDistanceLyapunov]
  exact standardDistanceLyapunov_ne_top q₀

/-- The canonical Lyapunov function changes by at most the norm of an
additive proposal increment. -/
theorem standardDistanceLyapunov_le_add_norm_sub (x y : Position ι) :
    standardDistanceLyapunov y ≤ standardDistanceLyapunov x +
      ENNReal.ofReal ‖y - x‖ := by
  rw [standardDistanceLyapunov, standardDistanceLyapunov]
  calc
    ENNReal.ofReal (1 + dist y 0) ≤
        ENNReal.ofReal ((1 + dist x 0) + ‖y - x‖) := by
      apply ENNReal.ofReal_le_ofReal
      have htriangle : dist y 0 ≤ dist x 0 + ‖y - x‖ := by
        simpa only [dist_eq_norm, sub_zero, add_comm] using
          dist_triangle y x 0
      linarith
    _ = ENNReal.ofReal (1 + dist x 0) + ENNReal.ofReal ‖y - x‖ := by
      rw [ENNReal.ofReal_add]
      · positivity
      · positivity

/-- Concrete Xu-style growth bound for the verified Gaussian RWMH kernel and
the canonical distance Lyapunov function.  The coefficient is finite for
every nondegenerate proposal variance and the proof is independent of the
target beyond measurability. -/
theorem standardDistanceLyapunov_gaussianRwmh_growth
    (weight : Position ι → ENNReal) (hweight : Measurable weight)
    (variance : NNReal) (hvariance : variance ≠ 0) (x : Position ι) :
    (∫⁻ y, standardDistanceLyapunov y
      ∂Mcmc.Kernel.euclideanGaussianRandomWalkMetropolisHastings
        weight variance hvariance x) ≤
      (2 + Mcmc.Kernel.isotropicGaussianFirstNormMoment
        (ι := ι) variance) * (standardDistanceLyapunov x + 1) := by
  have hbase :=
    Mcmc.Kernel.lintegral_euclideanGaussianRandomWalkMetropolisHastings_le
      weight variance hvariance hweight measurable_standardDistanceLyapunov
      standardDistanceLyapunov_le_add_norm_sub x
  calc
    (∫⁻ y, standardDistanceLyapunov y
      ∂Mcmc.Kernel.euclideanGaussianRandomWalkMetropolisHastings
        weight variance hvariance x) ≤
        2 * standardDistanceLyapunov x +
          Mcmc.Kernel.isotropicGaussianFirstNormMoment
            (ι := ι) variance := hbase
    _ ≤ 2 * standardDistanceLyapunov x +
          Mcmc.Kernel.isotropicGaussianFirstNormMoment
            (ι := ι) variance +
        (2 + Mcmc.Kernel.isotropicGaussianFirstNormMoment
          (ι := ι) variance * standardDistanceLyapunov x) :=
      le_add_right le_rfl
    _ = (2 + Mcmc.Kernel.isotropicGaussianFirstNormMoment
          (ι := ι) variance) * (standardDistanceLyapunov x + 1) := by
      ring

theorem standardDistanceLyapunov_gaussianRwmh_growthCoefficient_pos
    (variance : NNReal) :
    0 < 2 + Mcmc.Kernel.isotropicGaussianFirstNormMoment
      (ι := ι) variance := by positivity

theorem standardDistanceLyapunov_gaussianRwmh_growthCoefficient_ne_top
    (variance : NNReal) (hvariance : variance ≠ 0) :
    2 + Mcmc.Kernel.isotropicGaussianFirstNormMoment
      (ι := ι) variance ≠ ⊤ :=
  ENNReal.add_ne_top.2 ⟨by norm_num,
    Mcmc.Kernel.isotropicGaussianFirstNormMoment_ne_top
      variance hvariance⟩

/-- Every finite paired sublevel of the canonical distance Lyapunov function
is compact.  This discharges the topological premise of the concrete exact
lag-one theorem once its drift inequalities are established. -/
theorem isCompact_lyapunovSublevel_pairedAdd_standardDistanceLyapunov
    {R : ENNReal} (hR : R ≠ ⊤) :
    IsCompact (Mcmc.Kernel.lyapunovSublevel
      (Mcmc.Kernel.IsCoupling.pairedAdd
        (standardDistanceLyapunov : Position ι → ENNReal)) R) := by
  let Vpair := Mcmc.Kernel.IsCoupling.pairedAdd
    (standardDistanceLyapunov : Position ι → ENNReal)
  have hcontinuous : Continuous Vpair := by
    dsimp only [Vpair, Mcmc.Kernel.IsCoupling.pairedAdd]
    exact (continuous_standardDistanceLyapunov.comp continuous_fst).add
      (continuous_standardDistanceLyapunov.comp continuous_snd)
  have hclosed : IsClosed (Mcmc.Kernel.lyapunovSublevel Vpair R) := by
    exact isClosed_le hcontinuous continuous_const
  have hsubset : Mcmc.Kernel.lyapunovSublevel Vpair R ⊆
      Metric.closedBall (0 : Position ι) R.toReal ×ˢ
        Metric.closedBall (0 : Position ι) R.toReal := by
    intro q hq
    have hleft : standardDistanceLyapunov q.1 ≤ R :=
      (le_add_right le_rfl).trans hq
    have hright : standardDistanceLyapunov q.2 ≤ R :=
      (le_add_left le_rfl).trans hq
    have hleftReal := ENNReal.toReal_mono hR hleft
    have hrightReal := ENNReal.toReal_mono hR hright
    have htoReal (x : Position ι) :
        (standardDistanceLyapunov x).toReal = 1 + dist x 0 := by
      rw [standardDistanceLyapunov, ENNReal.toReal_ofReal]
      positivity
    rw [htoReal] at hleftReal hrightReal
    constructor
    · rw [Metric.mem_closedBall]
      exact (show dist q.1 0 ≤ R.toReal by linarith)
    · rw [Metric.mem_closedBall]
      exact (show dist q.2 0 ≤ R.toReal by linarith)
  exact ((isCompact_closedBall (0 : Position ι) R.toReal).prod
    (isCompact_closedBall (0 : Position ι) R.toReal)).of_isClosed_subset
      hclosed hsubset

/-- Every paired sublevel at height at least two is nonempty: it contains the
pair of origins.  Together with compactness, this removes the two topological
side conditions in the exact lag-one meeting theorem for this candidate. -/
theorem nonempty_lyapunovSublevel_pairedAdd_standardDistanceLyapunov
    {R : ENNReal} (hR : 2 ≤ R) :
    (Mcmc.Kernel.lyapunovSublevel
      (Mcmc.Kernel.IsCoupling.pairedAdd
        (standardDistanceLyapunov : Position ι → ENNReal)) R).Nonempty := by
  refine ⟨((0 : Position ι), (0 : Position ι)), ?_⟩
  change standardDistanceLyapunov (0 : Position ι) +
      standardDistanceLyapunov (0 : Position ι) ≤ R
  calc
    standardDistanceLyapunov (0 : Position ι) +
        standardDistanceLyapunov (0 : Position ι) = 2 := by
      simp [standardDistanceLyapunov]
      norm_num
    _ ≤ R := hR

/-- One-dimensional phase point used to audit the two-index Gaussian
transport claim. -/
def standardQuadraticUnitPhase (q p : ℝ) : PhaseSpace Unit :=
  (fun _ => q, fun _ => p)

/-- Scalar form of the canonical distance Lyapunov function. -/
theorem standardDistanceLyapunov_unit (q : ℝ) :
    standardDistanceLyapunov (fun _ : Unit ↦ q) =
      ENNReal.ofReal (1 + |q|) := by
  simp [standardDistanceLyapunov]

/-- Energy defect of one unit-step leapfrog update started at position `q`
and momentum one in one dimension. -/
noncomputable def standardQuadraticUnitOneStepDefect (q : ℝ) : ℝ :=
  (1 / 8 : ℝ) + (-(3 / 32 : ℝ) * q ^ 2 + (1 / 8 : ℝ) * q)

/-- Endpoint-selection probability of the corresponding two-point trajectory,
written as an ordinary real logistic function of the energy defect. -/
noncomputable def standardQuadraticUnitEndpointProbability (q : ℝ) : ℝ :=
  (Real.exp (standardQuadraticUnitOneStepDefect q) + 1)⁻¹

/-- Arbitrary-step version of the one-dimensional, unit-momentum leapfrog
energy defect. -/
noncomputable def standardQuadraticOneStepDefect (ε q : ℝ) : ℝ :=
  ε ^ 4 / 8 +
    (ε ^ 4 * (ε ^ 2 - 4) / 32 * q ^ 2 +
      (ε ^ 3 / 4 * (1 - ε ^ 2 / 2)) * q)

/-- Endpoint probability for the arbitrary-step two-index trajectory. -/
noncomputable def standardQuadraticEndpointProbability (ε q : ℝ) : ℝ :=
  (Real.exp (standardQuadraticOneStepDefect ε q) + 1)⁻¹

/-- First derivative of the arbitrary-step defect at coincident position. -/
theorem hasDerivAt_standardQuadraticOneStepDefect_zero (ε : ℝ) :
    HasDerivAt (standardQuadraticOneStepDefect ε)
      (ε ^ 3 / 4 * (1 - ε ^ 2 / 2)) 0 := by
  let a := ε ^ 4 * (ε ^ 2 - 4) / 32
  let c := ε ^ 3 / 4 * (1 - ε ^ 2 / 2)
  change HasDerivAt (fun q : ℝ =>
    ε ^ 4 / 8 + (a * q ^ 2 + c * q)) c 0
  have hquad : HasDerivAt (fun q : ℝ => q ^ 2) 0 0 := by
    simpa using hasDerivAt_pow 2 (0 : ℝ)
  have hlinear : HasDerivAt (fun q : ℝ => q) 1 0 :=
    hasDerivAt_id (0 : ℝ)
  have hsum :=
    (hquad.const_mul a |>.add (hlinear.const_mul c)).const_add (ε ^ 4 / 8)
  simpa only [Pi.add_apply, zero_mul, mul_zero, add_zero, zero_add, mul_one] using hsum

/-- The arbitrary-step endpoint probability has the explicit logistic
derivative induced by the energy defect. -/
theorem hasDerivAt_standardQuadraticEndpointProbability_zero (ε : ℝ) :
    HasDerivAt (standardQuadraticEndpointProbability ε)
      (-((ε ^ 3 / 4 * (1 - ε ^ 2 / 2)) * Real.exp (ε ^ 4 / 8)) /
        (Real.exp (ε ^ 4 / 8) + 1) ^ 2) 0 := by
  let c := ε ^ 3 / 4 * (1 - ε ^ 2 / 2)
  have hdefect := hasDerivAt_standardQuadraticOneStepDefect_zero ε
  have hdenom : HasDerivAt
      (fun q => Real.exp (standardQuadraticOneStepDefect ε q) + 1)
      (c * Real.exp (ε ^ 4 / 8)) 0 := by
    apply (hdefect.exp.add_const 1).congr_deriv
    dsimp only [c]
    simp [standardQuadraticOneStepDefect]
    ring
  have hinv := hdenom.inv (by positivity)
  change HasDerivAt
    (fun q => (Real.exp (standardQuadraticOneStepDefect ε q) + 1)⁻¹) _ 0
  apply hinv.congr_deriv
  dsimp only [c]
  simp [standardQuadraticOneStepDefect]

/-- For every positive step size at most one, the endpoint probability has a
nonzero first derivative at the diagonal. -/
theorem deriv_standardQuadraticEndpointProbability_zero_ne_zero
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    deriv (standardQuadraticEndpointProbability ε) 0 ≠ 0 := by
  rw [(hasDerivAt_standardQuadraticEndpointProbability_zero ε).deriv]
  apply div_ne_zero
  · apply neg_ne_zero.mpr
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact div_ne_zero (pow_ne_zero _ hε0.ne') (by norm_num)
      · have hsq : ε ^ 2 ≤ 1 := by nlinarith
        nlinarith
    · exact Real.exp_ne_zero _
  · exact pow_ne_zero 2 (ne_of_gt (by positivity))

/-- The one-dimensional standard-quadratic energy has the expected scalar
formula. -/
theorem energy_standardQuadraticUnitPhase (q p : ℝ) :
    energy standardQuadraticPotential (standardQuadraticUnitPhase q p) =
      (q ^ 2 + p ^ 2) / 2 := by
  simp [energy, standardQuadraticPotential, standardQuadraticUnitPhase,
    kineticEnergy]
  ring

/-- At step size `sqrt 2`, the exact one-step Hamiltonian defect is negative
quadratic in the current position and positive quadratic in the refreshed
momentum. This is the scalar logistic exponent governing whether multinomial
HMC retains the current point. -/
theorem standardQuadraticUnit_leapfrog_sqrtTwo_energy_defect (q p : ℝ) :
    energy standardQuadraticPotential
        (leapfrog standardQuadraticGradient (Real.sqrt 2)
          (standardQuadraticUnitPhase q p)) -
      energy standardQuadraticPotential (standardQuadraticUnitPhase q p) =
        p ^ 2 / 2 - q ^ 2 / 4 := by
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt3 : (Real.sqrt 2) ^ 3 = 2 * Real.sqrt 2 := by
    calc
      (Real.sqrt 2) ^ 3 = (Real.sqrt 2) ^ 2 * Real.sqrt 2 := by ring
      _ = 2 * Real.sqrt 2 := by rw [hsqrt]
  have hsqrt4 : (Real.sqrt 2) ^ 4 = (4 : ℝ) := by
    calc
      (Real.sqrt 2) ^ 4 = ((Real.sqrt 2) ^ 2) ^ 2 := by ring
      _ = 4 := by rw [hsqrt]; norm_num
  have hsqrt5 : (Real.sqrt 2) ^ 5 = 4 * Real.sqrt 2 := by
    calc
      (Real.sqrt 2) ^ 5 = (Real.sqrt 2) ^ 4 * Real.sqrt 2 := by ring
      _ = 4 * Real.sqrt 2 := by rw [hsqrt4]
  have hsqrt6 : (Real.sqrt 2) ^ 6 = (8 : ℝ) := by
    calc
      (Real.sqrt 2) ^ 6 = ((Real.sqrt 2) ^ 2) ^ 3 := by ring
      _ = 8 := by rw [hsqrt]; norm_num
  simp [energy, standardQuadraticPotential, standardQuadraticUnitPhase,
    kineticEnergy, leapfrog, halfKick, drift, standardQuadraticGradient]
  ring_nf
  rw [hsqrt3, hsqrt4, hsqrt5, hsqrt6]
  ring

/-- The negative-time endpoint has the same defect because leapfrog is
conjugated by momentum reversal and the Hamiltonian is even in momentum. -/
theorem standardQuadraticUnit_leapfrog_negSqrtTwo_energy_defect (q p : ℝ) :
    energy standardQuadraticPotential
        (leapfrog standardQuadraticGradient (-(Real.sqrt 2))
          (standardQuadraticUnitPhase q p)) -
      energy standardQuadraticPotential (standardQuadraticUnitPhase q p) =
        p ^ 2 / 2 - q ^ 2 / 4 := by
  rw [← momentumFlip_leapfrog_momentumFlip standardQuadraticGradient
    (Real.sqrt 2) (standardQuadraticUnitPhase q p), energy_momentumFlip]
  have h := standardQuadraticUnit_leapfrog_sqrtTwo_energy_defect q (-p)
  have hflip : momentumFlip (standardQuadraticUnitPhase q p) =
      standardQuadraticUnitPhase q (-p) := by
    ext i <;> simp [standardQuadraticUnitPhase, momentumFlip]
  rw [hflip]
  calc
    energy standardQuadraticPotential
          (leapfrog standardQuadraticGradient (Real.sqrt 2)
            (standardQuadraticUnitPhase q (-p))) -
        energy standardQuadraticPotential (standardQuadraticUnitPhase q p) =
      energy standardQuadraticPotential
          (leapfrog standardQuadraticGradient (Real.sqrt 2)
            (standardQuadraticUnitPhase q (-p))) -
        energy standardQuadraticPotential
          (standardQuadraticUnitPhase q (-p)) := by
            rw [energy_standardQuadraticUnitPhase,
              energy_standardQuadraticUnitPhase]
            ring
    _ = p ^ 2 / 2 - q ^ 2 / 4 := by simpa using h

/-- For either randomized root of the two-point trajectory, the categorical
probability of retaining the current index has the same exponential bound.
The exponent is the exact endpoint-minus-current Hamiltonian defect. -/
theorem standardQuadraticUnit_sqrtTwo_currentIndexProbability_le
    (origin : Fin 2) (q p : ℝ) :
    trajectoryIndexPMF standardQuadraticPotential
        (offsetLeapfrogTrajectory standardQuadraticGradient (Real.sqrt 2)
          origin (standardQuadraticUnitPhase q p)) origin ≤
      ENNReal.ofReal (Real.exp (p ^ 2 / 2 - q ^ 2 / 4)) := by
  fin_cases origin
  · let current : Fin 2 := ⟨0, by omega⟩
    let endpoint : Fin 2 := ⟨1, by omega⟩
    have h := trajectoryIndexPMF_le_exp_energy_sub
      standardQuadraticPotential
      (offsetLeapfrogTrajectory standardQuadraticGradient (Real.sqrt 2)
        current (standardQuadraticUnitPhase q p)) current endpoint
    dsimp only [current, endpoint] at h ⊢
    rw [offsetLeapfrogTrajectory_origin] at h
    change _ ≤ ENNReal.ofReal (Real.exp
      (energy standardQuadraticPotential
          (leapfrog standardQuadraticGradient (Real.sqrt 2)
            (standardQuadraticUnitPhase q p)) -
        energy standardQuadraticPotential
          (standardQuadraticUnitPhase q p))) at h
    simpa [standardQuadraticUnit_leapfrog_sqrtTwo_energy_defect] using h
  · let endpoint : Fin 2 := ⟨0, by omega⟩
    let current : Fin 2 := ⟨1, by omega⟩
    have h := trajectoryIndexPMF_le_exp_energy_sub
      standardQuadraticPotential
      (offsetLeapfrogTrajectory standardQuadraticGradient (Real.sqrt 2)
        current (standardQuadraticUnitPhase q p)) current endpoint
    dsimp only [current, endpoint] at h ⊢
    rw [offsetLeapfrogTrajectory_origin] at h
    change _ ≤ ENNReal.ofReal (Real.exp
      (energy standardQuadraticPotential
          (leapfrog standardQuadraticGradient (-(Real.sqrt 2))
            (standardQuadraticUnitPhase q p)) -
        energy standardQuadraticPotential
          (standardQuadraticUnitPhase q p))) at h
    simpa [standardQuadraticUnit_leapfrog_negSqrtTwo_energy_defect] using h

/-- For a fixed refreshed momentum, the two-point multinomial expectation of
the canonical Lyapunov function is bounded by a retention term plus the
Lyapunov cost of the rescaled-momentum endpoint. This is uniform in the
randomized trajectory root. -/
theorem standardQuadraticUnit_sqrtTwo_indexExpectation_le
    (origin : Fin 2) (q p : ℝ) :
    (∑ selected : Fin 2,
      trajectoryIndexPMF standardQuadraticPotential
          (offsetLeapfrogTrajectory standardQuadraticGradient (Real.sqrt 2)
            origin (standardQuadraticUnitPhase q p)) selected *
        standardDistanceLyapunov
          (offsetLeapfrogTrajectory standardQuadraticGradient (Real.sqrt 2)
            origin (standardQuadraticUnitPhase q p) selected).1) ≤
      min 1 (ENNReal.ofReal (Real.exp (p ^ 2 / 2 - q ^ 2 / 4))) *
          standardDistanceLyapunov (standardQuadraticUnitPhase q p).1 +
        standardDistanceLyapunov (fun _ : Unit ↦ Real.sqrt 2 * p) := by
  let trajectory := offsetLeapfrogTrajectory standardQuadraticGradient
    (Real.sqrt 2) origin (standardQuadraticUnitPhase q p)
  let retention := ENNReal.ofReal (Real.exp (p ^ 2 / 2 - q ^ 2 / 4))
  have hretain : trajectoryIndexPMF standardQuadraticPotential trajectory origin ≤
      min 1 retention := by
    apply le_min
    · exact (trajectoryIndexPMF standardQuadraticPotential trajectory).coe_le_one origin
    · exact standardQuadraticUnit_sqrtTwo_currentIndexProbability_le origin q p
  fin_cases origin
  · rw [Fin.sum_univ_two]
    have hretain0 :
        trajectoryIndexPMF standardQuadraticPotential trajectory (0 : Fin 2) ≤
          min 1 retention := by simpa using hretain
    have hcurrent :
        trajectoryIndexPMF standardQuadraticPotential trajectory (0 : Fin 2) *
            standardDistanceLyapunov (trajectory (0 : Fin 2)).1 ≤
          min 1 retention *
            standardDistanceLyapunov (standardQuadraticUnitPhase q p).1 := by
      rw [show trajectory (0 : Fin 2) = standardQuadraticUnitPhase q p by
        simp [trajectory]]
      simpa only [mul_comm] using
        mul_le_mul_right hretain0
          (standardDistanceLyapunov (standardQuadraticUnitPhase q p).1)
    have hendpoint :
        trajectoryIndexPMF standardQuadraticPotential trajectory (1 : Fin 2) *
            standardDistanceLyapunov (trajectory (1 : Fin 2)).1 ≤
          standardDistanceLyapunov (fun _ : Unit ↦ Real.sqrt 2 * p) := by
      rw [show (trajectory (1 : Fin 2)).1 =
          (fun _ : Unit ↦ Real.sqrt 2 * p) by
        change (leapfrog standardQuadraticGradient (Real.sqrt 2)
          (standardQuadraticUnitPhase q p)).1 = _
        rw [standardQuadratic_leapfrog_sqrtTwo_fst]
        funext i
        simp [standardQuadraticUnitPhase]]
      calc
        _ ≤ 1 * standardDistanceLyapunov
            (fun _ : Unit ↦ Real.sqrt 2 * p) := by
              gcongr
              exact (trajectoryIndexPMF standardQuadraticPotential trajectory).coe_le_one _
        _ = _ := one_mul _
    exact add_le_add hcurrent hendpoint
  · rw [Fin.sum_univ_two]
    have hretain1 :
        trajectoryIndexPMF standardQuadraticPotential trajectory (1 : Fin 2) ≤
          min 1 retention := by simpa using hretain
    have hendpoint :
        trajectoryIndexPMF standardQuadraticPotential trajectory (0 : Fin 2) *
            standardDistanceLyapunov (trajectory (0 : Fin 2)).1 ≤
          standardDistanceLyapunov (fun _ : Unit ↦ Real.sqrt 2 * p) := by
      rw [show (trajectory (0 : Fin 2)).1 =
          (fun _ : Unit ↦ -(Real.sqrt 2) * p) by
        change (leapfrog standardQuadraticGradient (-(Real.sqrt 2))
          (standardQuadraticUnitPhase q p)).1 = _
        rw [standardQuadratic_leapfrog_negSqrtTwo_fst]
        funext i
        simp [standardQuadraticUnitPhase]]
      rw [standardDistanceLyapunov_unit, standardDistanceLyapunov_unit,
        show -(Real.sqrt 2) * p = -(Real.sqrt 2 * p) by ring, abs_neg]
      calc
        _ ≤ 1 * ENNReal.ofReal (1 + |Real.sqrt 2 * p|) := by
              gcongr
              exact (trajectoryIndexPMF standardQuadraticPotential trajectory).coe_le_one _
        _ = _ := one_mul _
    have hcurrent :
        trajectoryIndexPMF standardQuadraticPotential trajectory (1 : Fin 2) *
            standardDistanceLyapunov (trajectory (1 : Fin 2)).1 ≤
          min 1 retention *
            standardDistanceLyapunov (standardQuadraticUnitPhase q p).1 := by
      rw [show trajectory (1 : Fin 2) = standardQuadraticUnitPhase q p by
        simp [trajectory]]
      simpa only [mul_comm] using
        mul_le_mul_right hretain1
          (standardDistanceLyapunov (standardQuadraticUnitPhase q p).1)
    exact add_le_add hendpoint hcurrent |>.trans_eq (add_comm _ _)

/-- Averaging over the uniformly randomized trajectory root preserves the
same scalar retention-plus-endpoint bound. -/
theorem standardQuadraticUnit_sqrtTwo_originIndexExpectation_le (q p : ℝ) :
    (∑ origin : Fin 2, PMF.uniformOfFintype (Fin 2) origin *
      ∑ selected : Fin 2,
        trajectoryIndexPMF standardQuadraticPotential
            (offsetLeapfrogTrajectory standardQuadraticGradient (Real.sqrt 2)
              origin (standardQuadraticUnitPhase q p)) selected *
          standardDistanceLyapunov
            (offsetLeapfrogTrajectory standardQuadraticGradient (Real.sqrt 2)
              origin (standardQuadraticUnitPhase q p) selected).1) ≤
      min 1 (ENNReal.ofReal (Real.exp (p ^ 2 / 2 - q ^ 2 / 4))) *
          standardDistanceLyapunov (standardQuadraticUnitPhase q p).1 +
        standardDistanceLyapunov (fun _ : Unit ↦ Real.sqrt 2 * p) := by
  let bound :=
    min 1 (ENNReal.ofReal (Real.exp (p ^ 2 / 2 - q ^ 2 / 4))) *
        standardDistanceLyapunov (standardQuadraticUnitPhase q p).1 +
      standardDistanceLyapunov (fun _ : Unit ↦ Real.sqrt 2 * p)
  calc
    _ ≤ ∑ origin : Fin 2,
        PMF.uniformOfFintype (Fin 2) origin * bound := by
      apply Finset.sum_le_sum
      intro origin _
      dsimp only [bound]
      exact mul_le_mul_right
        (standardQuadraticUnit_sqrtTwo_indexExpectation_le origin q p)
          (PMF.uniformOfFintype (Fin 2) origin)
    _ = (∑ origin : Fin 2, PMF.uniformOfFintype (Fin 2) origin) * bound := by
      rw [Finset.sum_mul]
    _ = bound := by
      rw [show ∑ origin : Fin 2, PMF.uniformOfFintype (Fin 2) origin = 1 by
        rw [show ∑ origin : Fin 2, PMF.uniformOfFintype (Fin 2) origin =
          ∑' origin : Fin 2, PMF.uniformOfFintype (Fin 2) origin by
            rw [tsum_fintype], PMF.tsum_coe], one_mul]

/-- Drift-ready expectation bound for the actual scalar standard-quadratic
position-space multinomial HMC kernel at `ε=√2`, `L=1`. The only remaining
analytic work is to integrate the displayed capped retention factor and the
rescaled Gaussian endpoint cost. -/
theorem lintegral_standardQuadraticUnit_sqrtTwo_hmc_le (q : ℝ) :
    (∫⁻ y, standardDistanceLyapunov y
      ∂standardPositionMultinomialHMC standardQuadraticPotential
        standardQuadraticGradient (Real.sqrt 2) 1
        (by unfold standardQuadraticPotential kineticEnergy; fun_prop)
        (by unfold standardQuadraticGradient; fun_prop)
        (fun _ : Unit ↦ q)) ≤
      ∫⁻ p : Momentum Unit,
        min 1 (ENNReal.ofReal
          (Real.exp ((p ()) ^ 2 / 2 - q ^ 2 / 4))) *
            standardDistanceLyapunov (fun _ : Unit ↦ q) +
          standardDistanceLyapunov (Real.sqrt 2 • p)
        ∂standardMomentumMeasure := by
  rw [standardPositionMultinomialHMC]
  rw [lintegral_positionMultinomialHMC standardQuadraticPotential
    standardQuadraticGradient (Real.sqrt 2) 1
    (by unfold standardQuadraticPotential kineticEnergy; fun_prop)
    (by unfold standardQuadraticGradient; fun_prop)
    standardMomentumMeasure standardDistanceLyapunov
    measurable_standardDistanceLyapunov]
  apply lintegral_mono
  intro p
  let r : ℝ := p ()
  have hp : p = (fun _ : Unit ↦ r) := by
    funext i
    cases i
    rfl
  have h := standardQuadraticUnit_sqrtTwo_originIndexExpectation_le q r
  have hphase : ((fun _ : Unit ↦ q), p) =
      standardQuadraticUnitPhase q r := by
    rw [hp]
    rfl
  have hendpoint : Real.sqrt 2 • p =
      (fun _ : Unit ↦ Real.sqrt 2 * r) := by
    rw [hp]
    funext i
    simp
  change (∑ origin : Fin 2, PMF.uniformOfFintype (Fin 2) origin *
      ∑ selected : Fin 2,
        trajectoryIndexPMF standardQuadraticPotential
            (offsetLeapfrogTrajectory standardQuadraticGradient (Real.sqrt 2)
              origin ((fun _ : Unit ↦ q), p)) selected *
          standardDistanceLyapunov
            (offsetLeapfrogTrajectory standardQuadraticGradient (Real.sqrt 2)
              origin ((fun _ : Unit ↦ q), p) selected).1) ≤
    min 1 (ENNReal.ofReal (Real.exp ((p ()) ^ 2 / 2 - q ^ 2 / 4))) *
        standardDistanceLyapunov (fun _ : Unit ↦ q) +
      standardDistanceLyapunov (Real.sqrt 2 • p)
  rw [hphase, hendpoint, show p () = r by rfl]
  exact h

/-- A scalar bound on the explicit Gaussian envelope supplies the ordinary
affine drift inequality for every point of `Position Unit`. This reduces the
remaining HMC premise of the end-to-end Xu theorem to a one-dimensional
Gaussian integral, with no kernel or trajectory construction left hidden. -/
theorem standardQuadraticUnit_sqrtTwo_hmc_drift_of_envelope
    (driftCoefficient driftAllowance : ENNReal)
    (henvelope : ∀ q : ℝ,
      (∫⁻ p : Momentum Unit,
        min 1 (ENNReal.ofReal
          (Real.exp ((p ()) ^ 2 / 2 - q ^ 2 / 4))) *
            standardDistanceLyapunov (fun _ : Unit ↦ q) +
          standardDistanceLyapunov (Real.sqrt 2 • p)
        ∂standardMomentumMeasure) ≤
      driftCoefficient * standardDistanceLyapunov (fun _ : Unit ↦ q) +
        driftAllowance) :
    ∀ x : Position Unit,
      (∫⁻ y, standardDistanceLyapunov y
        ∂standardPositionMultinomialHMC standardQuadraticPotential
          standardQuadraticGradient (Real.sqrt 2) 1
          (by unfold standardQuadraticPotential kineticEnergy; fun_prop)
          (by unfold standardQuadraticGradient; fun_prop) x) ≤
        driftCoefficient * standardDistanceLyapunov x + driftAllowance := by
  intro x
  let q : ℝ := x ()
  have hx : x = (fun _ : Unit ↦ q) := by
    funext i
    cases i
    rfl
  rw [hx]
  exact (lintegral_standardQuadraticUnit_sqrtTwo_hmc_le q).trans
    (henvelope q)

/-- Elementary scalar estimate behind the Gaussian drift bound. If momentum
is large relative to position, the right side pays for it linearly. Otherwise
the negative quadratic energy defect makes retention exponentially small. -/
theorem min_one_exp_standardQuadratic_defect_mul_one_add_abs_le
    (q p : ℝ) :
    min 1 (Real.exp (p ^ 2 / 2 - q ^ 2 / 4)) * (1 + |q|) ≤
      16 + 2 * |p| := by
  have hq0 : 0 ≤ |q| := abs_nonneg q
  have hp0 : 0 ≤ |p| := abs_nonneg p
  by_cases hrelative : |q| ≤ 2 * |p|
  · have hmin : min 1 (Real.exp (p ^ 2 / 2 - q ^ 2 / 4)) ≤ 1 := min_le_left _ _
    have hnonneg : 0 ≤ min 1 (Real.exp (p ^ 2 / 2 - q ^ 2 / 4)) := by positivity
    nlinarith

  · have hrelative' : 2 * |p| < |q| := lt_of_not_ge hrelative
    have hpq : p ^ 2 ≤ q ^ 2 / 4 := by
      rw [← sq_abs p, ← sq_abs q]
      nlinarith
    have hdefect : p ^ 2 / 2 - q ^ 2 / 4 ≤ -(q ^ 2 / 8) := by
      nlinarith
    have hexp : Real.exp (p ^ 2 / 2 - q ^ 2 / 4) ≤
        Real.exp (-(q ^ 2 / 8)) := Real.exp_le_exp.mpr hdefect
    have hminexp : min 1 (Real.exp (p ^ 2 / 2 - q ^ 2 / 4)) ≤
        Real.exp (-(q ^ 2 / 8)) := (min_le_right _ _).trans hexp
    have hfactor : 0 ≤ 1 + |q| := by positivity
    apply le_trans (mul_le_mul_of_nonneg_right hminexp hfactor)
    have hcore : Real.exp (-(q ^ 2 / 8)) * (1 + |q|) ≤ 16 := by
      by_cases hsmall : |q| ≤ 1
      · have hexpOne : Real.exp (-(q ^ 2 / 8)) ≤ 1 := by
          rw [← Real.exp_zero]
          apply Real.exp_le_exp.mpr
          nlinarith [sq_nonneg q]
        nlinarith [Real.exp_pos (-(q ^ 2 / 8))]
      · have hqOne : 1 < |q| := lt_of_not_ge hsmall
        have hx : q ^ 2 / 8 ≤ Real.exp (q ^ 2 / 8) := by
          have := Real.add_one_le_exp (q ^ 2 / 8)
          linarith
        rw [Real.exp_neg]
        rw [inv_mul_eq_div]
        apply (div_le_iff₀ (Real.exp_pos (q ^ 2 / 8))).2
        have hpoly : 1 + |q| ≤ 2 * q ^ 2 := by
          rw [← sq_abs q]
          nlinarith
        nlinarith
    nlinarith

/-- ENNReal form of the scalar retention estimate, combined with the
`sqrt 2` endpoint cost. The full conditional drift integrand grows at most
linearly in the refreshed momentum. -/
theorem standardQuadraticUnit_sqrtTwo_driftIntegrand_le (q p : ℝ) :
    min 1 (ENNReal.ofReal (Real.exp (p ^ 2 / 2 - q ^ 2 / 4))) *
          standardDistanceLyapunov (fun _ : Unit ↦ q) +
        standardDistanceLyapunov (fun _ : Unit ↦ Real.sqrt 2 * p) ≤
      17 + 4 * ENNReal.ofReal |p| := by
  have hretention :
      min 1 (ENNReal.ofReal (Real.exp (p ^ 2 / 2 - q ^ 2 / 4))) *
          standardDistanceLyapunov (fun _ : Unit ↦ q) ≤
        16 + 2 * ENNReal.ofReal |p| := by
    rw [standardDistanceLyapunov_unit, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_min, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 16)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg p))]
    exact ENNReal.ofReal_le_ofReal
      (min_one_exp_standardQuadratic_defect_mul_one_add_abs_le q p)
  have hsqrt : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_nonneg 2]
  have hendpoint :
      standardDistanceLyapunov (fun _ : Unit ↦ Real.sqrt 2 * p) ≤
        1 + 2 * ENNReal.ofReal |p| := by
    rw [standardDistanceLyapunov_unit, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg p))]
    apply ENNReal.ofReal_le_ofReal
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]
    nlinarith [abs_nonneg p]
  calc
    _ ≤ (16 + 2 * ENNReal.ofReal |p|) +
        (1 + 2 * ENNReal.ofReal |p|) := add_le_add hretention hendpoint
    _ = 17 + 4 * ENNReal.ofReal |p| := by ring

/-- Explicit finite allowance for the uniformly bounded scalar HMC drift. -/
noncomputable def standardQuadraticUnitSqrtTwoDriftAllowance : ENNReal :=
  17 + 4 *
    (∫⁻ p : Momentum Unit, ENNReal.ofReal ‖p‖ ∂standardMomentumMeasure)

theorem standardQuadraticUnitSqrtTwoDriftAllowance_ne_top :
    standardQuadraticUnitSqrtTwoDriftAllowance ≠ ⊤ := by
  unfold standardQuadraticUnitSqrtTwoDriftAllowance
  exact ENNReal.add_ne_top.2 ⟨by norm_num,
    ENNReal.mul_ne_top (by norm_num)
      lintegral_norm_standardMomentumMeasure_ne_top⟩

/-- The explicit capped-retention envelope is uniformly bounded by the
finite Gaussian first-moment allowance. -/
theorem standardQuadraticUnit_sqrtTwo_envelope_le_allowance (q : ℝ) :
    (∫⁻ p : Momentum Unit,
      min 1 (ENNReal.ofReal
        (Real.exp ((p ()) ^ 2 / 2 - q ^ 2 / 4))) *
          standardDistanceLyapunov (fun _ : Unit ↦ q) +
        standardDistanceLyapunov (Real.sqrt 2 • p)
      ∂standardMomentumMeasure) ≤
        standardQuadraticUnitSqrtTwoDriftAllowance := by
  calc
    _ ≤ ∫⁻ p : Momentum Unit,
        17 + 4 * ENNReal.ofReal ‖p‖ ∂standardMomentumMeasure := by
      apply lintegral_mono
      intro p
      let r : ℝ := p ()
      have hp : p = (fun _ : Unit ↦ r) := by
        funext i
        cases i
        rfl
      have hbase := standardQuadraticUnit_sqrtTwo_driftIntegrand_le q r
      have hrewrite : standardDistanceLyapunov (Real.sqrt 2 • p) =
          standardDistanceLyapunov (fun _ : Unit ↦ Real.sqrt 2 * r) := by
        rw [hp]
        congr 1
      change min 1 (ENNReal.ofReal
          (Real.exp ((p ()) ^ 2 / 2 - q ^ 2 / 4))) *
            standardDistanceLyapunov (fun _ : Unit ↦ q) +
          standardDistanceLyapunov (Real.sqrt 2 • p) ≤
        17 + 4 * ENNReal.ofReal ‖p‖
      rw [hrewrite, show p () = r by rfl]
      apply hbase.trans
      gcongr
      simpa only [r, Real.norm_eq_abs] using
        (show |p ()| ≤ ‖p‖ by
          simpa [Real.dist_eq, dist_eq_norm] using
            dist_le_pi_dist p 0 ())
    _ = standardQuadraticUnitSqrtTwoDriftAllowance := by
      rw [lintegral_add_left measurable_const,
        lintegral_const, measure_univ, mul_one]
      have heq :
          (∫⁻ p : Momentum Unit, 4 * ENNReal.ofReal ‖p‖
            ∂standardMomentumMeasure) =
            4 * (∫⁻ p : Momentum Unit, ENNReal.ofReal ‖p‖
              ∂standardMomentumMeasure) := by
        exact lintegral_const_mul 4
          (show Measurable (fun p : Momentum Unit ↦ ENNReal.ofReal ‖p‖) from
            (ENNReal.continuous_ofReal.comp continuous_norm).measurable)
      rw [heq]
      rfl

/-- Verified strict affine drift for the actual scalar standard-quadratic
multinomial-HMC kernel with step size `sqrt 2` and one leapfrog step. The
coefficient `1/2` is deliberately conservative; the preceding argument in
fact proves a uniform bound independent of the current position. -/
theorem standardQuadraticUnit_sqrtTwo_hmc_drift (x : Position Unit) :
    (∫⁻ y, standardDistanceLyapunov y
      ∂standardPositionMultinomialHMC standardQuadraticPotential
        standardQuadraticGradient (Real.sqrt 2) 1
        (by unfold standardQuadraticPotential kineticEnergy; fun_prop)
        (by unfold standardQuadraticGradient; fun_prop) x) ≤
      (1 / 2 : ENNReal) * standardDistanceLyapunov x +
        standardQuadraticUnitSqrtTwoDriftAllowance := by
  have huniform := standardQuadraticUnit_sqrtTwo_hmc_drift_of_envelope
    0 standardQuadraticUnitSqrtTwoDriftAllowance
    (fun q ↦ by simpa using
      standardQuadraticUnit_sqrtTwo_envelope_le_allowance q) x
  have huniform' :
      (∫⁻ y, standardDistanceLyapunov y
        ∂standardPositionMultinomialHMC standardQuadraticPotential
          standardQuadraticGradient (Real.sqrt 2) 1
          (by unfold standardQuadraticPotential kineticEnergy; fun_prop)
          (by unfold standardQuadraticGradient; fun_prop) x) ≤
        standardQuadraticUnitSqrtTwoDriftAllowance := by
    simpa using huniform
  exact huniform'.trans (le_add_left le_rfl)

/-- The endpoint categorical probability varies to first order at coincident
position zero when the shared momentum is nonzero. -/
theorem hasDerivAt_standardQuadraticUnitEndpointProbability_zero :
    HasDerivAt standardQuadraticUnitEndpointProbability
      (-((1 / 8 : ℝ) * Real.exp (1 / 8)) /
        (Real.exp (1 / 8) + 1) ^ 2) 0 := by
  have hdefect : HasDerivAt standardQuadraticUnitOneStepDefect (1 / 8) 0 := by
    change HasDerivAt (fun q : ℝ =>
      (1 / 8 : ℝ) + (-(3 / 32 : ℝ) * q ^ 2 + (1 / 8 : ℝ) * q))
        (1 / 8) 0
    simpa [id_eq] using
      ((((hasDerivAt_id 0).pow 2).const_mul (-(3 / 32 : ℝ))).add
      ((hasDerivAt_id 0).const_mul (1 / 8 : ℝ))).const_add
        (1 / 8 : ℝ)
  have hdenom : HasDerivAt
      (fun q => Real.exp (standardQuadraticUnitOneStepDefect q) + 1)
      ((1 / 8 : ℝ) * Real.exp (1 / 8)) 0 := by
    apply (hdefect.exp.add_const 1).congr_deriv
    norm_num [standardQuadraticUnitOneStepDefect]
    ring
  have hinv := hdenom.inv (by positivity)
  change HasDerivAt
    (fun q => (Real.exp (standardQuadraticUnitOneStepDefect q) + 1)⁻¹) _ 0
  apply hinv.congr_deriv
  norm_num [standardQuadraticUnitOneStepDefect]

/-- In particular, the first-order variation just exhibited is nonzero. -/
theorem deriv_standardQuadraticUnitEndpointProbability_zero_ne_zero :
    deriv standardQuadraticUnitEndpointProbability 0 ≠ 0 := by
  rw [hasDerivAt_standardQuadraticUnitEndpointProbability_zero.deriv]
  apply div_ne_zero
  · exact neg_ne_zero.mpr
      (mul_ne_zero (by norm_num) (Real.exp_ne_zero (1 / 8 : ℝ)))
  · exact pow_ne_zero 2
      (ne_of_gt (by positivity : 0 < Real.exp (1 / 8 : ℝ) + 1))

/-- Equivalently, the secant slopes of the actual endpoint probability tend
to this nonzero first-order coefficient. -/
theorem tendsto_slope_standardQuadraticUnitEndpointProbability_zero :
    Filter.Tendsto
      (slope standardQuadraticUnitEndpointProbability 0)
      (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ)
      (nhds (-((1 / 8 : ℝ) * Real.exp (1 / 8)) /
        (Real.exp (1 / 8) + 1) ^ 2)) :=
  hasDerivAt_standardQuadraticUnitEndpointProbability_zero.tendsto_slope

/-- Hence the endpoint probability has a uniform nonzero secant-slope floor
on a deleted neighborhood of the coincident position. -/
theorem eventually_half_abs_deriv_lt_abs_slope_endpointProbability :
    ∀ᶠ q in nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ,
      |deriv standardQuadraticUnitEndpointProbability 0| / 2 <
        |slope standardQuadraticUnitEndpointProbability 0 q| := by
  have ht : Filter.Tendsto
      (slope standardQuadraticUnitEndpointProbability 0)
      (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ)
      (nhds (deriv standardQuadraticUnitEndpointProbability 0)) := by
    simpa only [hasDerivAt_standardQuadraticUnitEndpointProbability_zero.deriv]
      using tendsto_slope_standardQuadraticUnitEndpointProbability_zero
  have habs : Filter.Tendsto
      (fun q => |slope standardQuadraticUnitEndpointProbability 0 q|)
      (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ)
      (nhds |deriv standardQuadraticUnitEndpointProbability 0|) :=
    (continuous_abs.tendsto _).comp ht
  apply (tendsto_order.1 habs).1
  exact (div_lt_self
    (abs_pos.mpr deriv_standardQuadraticUnitEndpointProbability_zero_ne_zero)
    (by norm_num : (1 : ℝ) < 2))

omit [Fintype ι] in
/-- The identity gradient of the standard quadratic potential is measurable. -/
theorem measurable_standardQuadraticGradient :
    Measurable (standardQuadraticGradient : Position ι → Position ι) := by
  change Measurable (fun q : Position ι => q)
  exact measurable_id

omit [Fintype ι] in
@[simp]
theorem standardQuadraticGradient_apply (q : Position ι) (i : ι) :
    standardQuadraticGradient q i = q i := rfl

/-- The standard quadratic potential is smooth. -/
theorem contDiff_standardQuadraticPotential :
    ContDiff ℝ 2 (standardQuadraticPotential : Position ι → ℝ) := by
  unfold standardQuadraticPotential kineticEnergy
  exact contDiff_const.mul
    (ContDiff.sum fun i hi => (contDiff_apply ℝ ℝ i).pow 2)

/-- The preceding RWMH growth certificate instantiated on the actual
Boltzmann target of the standard quadratic potential. -/
theorem standardQuadraticGaussianRwmh_growth
    (variance : NNReal) (hvariance : variance ≠ 0) (x : Position ι) :
    (∫⁻ y, standardDistanceLyapunov y
      ∂Mcmc.Kernel.euclideanGaussianRandomWalkMetropolisHastings
        (positionBoltzmannWeight standardQuadraticPotential)
        variance hvariance x) ≤
      (2 + Mcmc.Kernel.isotropicGaussianFirstNormMoment
        (ι := ι) variance) * (standardDistanceLyapunov x + 1) := by
  exact standardDistanceLyapunov_gaussianRwmh_growth
    (positionBoltzmannWeight standardQuadraticPotential)
    (measurable_positionBoltzmannWeight
      contDiff_standardQuadraticPotential.continuous.measurable)
    variance hvariance x

/-- The Fréchet derivative of the standard quadratic potential is Euclidean
inner product with the base point. -/
theorem fderiv_standardQuadraticPotential_apply
    (q h : Position ι) :
    fderiv ℝ standardQuadraticPotential q h = euclideanInner q h := by
  let line : ℝ → Position ι := fun t => q + t • h
  have hline : HasDerivAt line h 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    change HasDerivAt (fun t : ℝ => q i + t * h i) (h i) 0
    simpa only [id_eq, one_mul] using
      ((hasDerivAt_id 0).mul_const (h i)).const_add (q i)
  have hfromFDeriv : HasDerivAt
      (fun t => standardQuadraticPotential (line t))
      (fderiv ℝ standardQuadraticPotential q h) 0 := by
    have hdifferentiable : DifferentiableAt ℝ
        (standardQuadraticPotential : Position ι → ℝ) q :=
      ((contDiff_standardQuadraticPotential (ι := ι)).differentiable
        (by norm_num)).differentiableAt
    have hlinezero : line 0 = q := by simp [line]
    have houter := hdifferentiable.hasFDerivAt
    rw [← hlinezero] at houter
    have hcomp := houter.comp_hasDerivAt 0 hline
    rw [hlinezero] at hcomp
    change HasDerivAt (standardQuadraticPotential ∘ line)
      (fderiv ℝ standardQuadraticPotential q h) 0
    exact hcomp
  have hdirect : HasDerivAt
      (fun t => standardQuadraticPotential (line t))
      (euclideanInner q h) 0 := by
    unfold standardQuadraticPotential kineticEnergy
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun i hi =>
      (((hasDerivAt_const (x := 0) (c := q i)).add
        ((hasDerivAt_id 0).mul_const (h i))).pow 2)
    have hhalf := hsum.const_mul (1 / 2 : ℝ)
    have hderiv :
        (1 / 2 : ℝ) * ∑ i,
          (2 : ℝ) * (q i + 0 * h i) ^ (2 - 1) * (0 + 1 * h i) =
        euclideanInner q h := by
      simp only [euclideanInner]
      norm_num
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hh := hhalf.congr_deriv hderiv
    simpa [line] using hh
  exact hfromFDeriv.unique hdirect

/-- The standard Gaussian potential satisfies `RegularPotential` with the
positive global gradient-Lipschitz constant one. -/
theorem regularPotential_standardQuadratic :
    RegularPotential
      (standardQuadraticPotential : Position ι → ℝ)
      standardQuadraticGradient 1 where
  beta_pos := by norm_num
  contDiff_two := contDiff_standardQuadraticPotential
  fderiv_apply := fderiv_standardQuadraticPotential_apply
  gradient_lipschitz := by
    intro q₁ q₂
    simp [standardQuadraticGradient]

/-- Every positive-radius closed ball is a compact, measurable,
positive-volume region on which the standard quadratic gradient is strongly
monotone with modulus one. -/
theorem localStrongConvexity_standardQuadratic_closedBall
    {r : ℝ} (hr : 0 < r) :
    LocalStrongConvexity standardQuadraticGradient
      (Metric.closedBall (0 : Position ι) r) 1 where
  alpha_pos := by norm_num
  compact := isCompact_closedBall 0 r
  measurableSet := measurableSet_closedBall
  volume_pos := Metric.measure_closedBall_pos volume 0 hr
  strongMonotone := by
    intro q₁ hq₁ q₂ hq₂
    simp only [standardQuadraticGradient, one_mul]
    exact le_rfl

/-- Membership in a metric closed ball gives an explicit bound for the
coordinate Euclidean norm used by the leapfrog estimates. -/
theorem euclideanNorm_le_card_succ_mul_of_mem_closedBall
    {r : ℝ} {q : Position ι} (hq : q ∈ Metric.closedBall 0 r) :
    euclideanNorm q ≤ ((Fintype.card ι : ℝ) + 1) * r := by
  have hdist : dist q 0 ≤ r := by
    simpa [dist_comm] using (Metric.mem_closedBall.mp hq)
  have hnorm := euclideanNorm_sub_le_card_succ_mul_dist q 0
  simpa using hnorm.trans
    (mul_le_mul_of_nonneg_left hdist (by positivity))

/-- Shared-momentum Gaussian leapfrog has the explicit one-step contraction
factor `1 - ε² + ε⁴/4` on every positive-radius closed ball. -/
theorem standardQuadratic_leapfrog_sharedMomentum_squaredDistance_le
    {r : ℝ} (hr : 0 < r) (ε : ℝ)
    {q₁ q₂ : Position ι}
    (hq₁ : q₁ ∈ Metric.closedBall (0 : Position ι) r)
    (hq₂ : q₂ ∈ Metric.closedBall (0 : Position ι) r)
    (p : Momentum ι) :
    squaredEuclideanNorm
        ((leapfrog standardQuadraticGradient ε (q₁, p)).1 -
          (leapfrog standardQuadraticGradient ε (q₂, p)).1) ≤
      (1 - ε ^ 2 + ε ^ 4 / 4) *
        squaredEuclideanNorm (q₁ - q₂) := by
  simpa using leapfrog_sharedMomentum_squaredDistance_le
    regularPotential_standardQuadratic
    (localStrongConvexity_standardQuadratic_closedBall hr)
    ε hq₁ hq₂ p

/-- Every nonzero Gaussian leapfrog step with `ε² < 4` strictly contracts
distinct shared-momentum positions in the chosen closed ball. -/
theorem standardQuadratic_leapfrog_sharedMomentum_squaredDistance_lt
    {r : ℝ} (hr : 0 < r) {ε : ℝ} (hε : ε ≠ 0)
    (hsmall : ε ^ 2 < 4) {q₁ q₂ : Position ι}
    (hq₁ : q₁ ∈ Metric.closedBall (0 : Position ι) r)
    (hq₂ : q₂ ∈ Metric.closedBall (0 : Position ι) r)
    (hne : q₁ ≠ q₂) (p : Momentum ι) :
    squaredEuclideanNorm
        ((leapfrog standardQuadraticGradient ε (q₁, p)).1 -
          (leapfrog standardQuadraticGradient ε (q₂, p)).1) <
      squaredEuclideanNorm (q₁ - q₂) := by
  apply leapfrog_sharedMomentum_squaredDistance_lt
    regularPotential_standardQuadratic
    (localStrongConvexity_standardQuadratic_closedBall hr)
    hε
  · simpa using hsmall
  · exact hq₁
  · exact hq₂
  · exact hne

/-- Uniform fixed-integration-time phase-size stability for the standard
quadratic Gaussian leapfrog trajectory. The forcing term vanishes because its
gradient is zero at the origin. -/
theorem standardQuadratic_leapfrogN_euclideanPhaseSize_le_exp
    {ε : ℝ} (hε : |ε| ≤ 1) (n : ℕ) {T : ℝ}
    (horizon : (n : ℝ) * |ε| ≤ T) (z : PhaseSpace ι) :
    euclideanPhaseSize
        (leapfrogN standardQuadraticGradient ε n z) ≤
      Real.exp ((13 / 4 : ℝ) * T) * euclideanPhaseSize z := by
  have h := leapfrogN_euclideanPhaseSize_le_exp
    regularPotential_standardQuadratic hε n horizon z
  norm_num [leapfrogNormStabilityRate, standardQuadraticGradient] at h ⊢
  exact h

/-- The same standard-quadratic phase-size stability bound holds uniformly
at every positive or negative offset of a randomized trajectory. -/
theorem standardQuadratic_offsetLeapfrogTrajectory_euclideanPhaseSize_le_exp
    {ε : ℝ} (hε : |ε| ≤ 1) {L : ℕ} (origin i : Fin (L + 1))
    {T : ℝ} (horizon : (L : ℝ) * |ε| ≤ T) (z : PhaseSpace ι) :
    euclideanPhaseSize
        (offsetLeapfrogTrajectory standardQuadraticGradient ε origin z i) ≤
      Real.exp ((13 / 4 : ℝ) * T) * euclideanPhaseSize z := by
  have h := offsetLeapfrogTrajectory_euclideanPhaseSize_le_exp
    regularPotential_standardQuadratic hε origin i horizon z
  norm_num [leapfrogNormStabilityRate, standardQuadraticGradient] at h ⊢
  exact h

/-- Scalar coefficient in the one-step standard-quadratic energy-error
bound. -/
noncomputable def standardQuadraticEnergyErrorRate (ε : ℝ) : ℝ :=
  |ε| ^ 4 / 8 + |ε| ^ 6 / 32 +
    |ε| ^ 3 / 8 * |1 - ε ^ 2 / 2|

/-- On unit-size steps, the Gaussian one-step error rate is at most cubic. -/
theorem standardQuadraticEnergyErrorRate_le_abs_cube
    {ε : ℝ} (hε : |ε| ≤ 1) :
    standardQuadraticEnergyErrorRate ε ≤ |ε| ^ 3 := by
  have ha : 0 ≤ |ε| := abs_nonneg ε
  have he2 : ε ^ 2 ≤ 1 := by
    nlinarith [sq_abs ε]
  have hfactor : |1 - ε ^ 2 / 2| ≤ 1 := by
    rw [abs_of_nonneg]
    · nlinarith
    · nlinarith [sq_nonneg ε]
  have h4 : |ε| ^ 4 ≤ |ε| ^ 3 := by
    nlinarith [mul_nonneg (pow_nonneg ha 3) (sub_nonneg.mpr hε)]
  have ha3 : |ε| ^ 3 ≤ 1 := pow_le_one₀ ha hε
  have h6 : |ε| ^ 6 ≤ |ε| ^ 3 := by
    nlinarith [mul_nonneg (pow_nonneg ha 3) (sub_nonneg.mpr ha3)]
  unfold standardQuadraticEnergyErrorRate
  nlinarith [pow_nonneg ha 3]

/-- A single positive step-size threshold can satisfy any three scalar
quadratic error budgets, including one with an arbitrary positive allowance.
This elementary selector is used to make the Gaussian coupling constants
uniform over a bounded phase region. -/
theorem exists_pos_stepSize_threshold_three
    {A B C m : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hm : 0 < m) :
    ∃ εbar : ℝ, 0 < εbar ∧ ∀ ε : ℝ, 0 < ε → ε < εbar →
      ε ≤ 1 ∧ ε ^ 2 * A ≤ 1 / 2 ∧
        ε ^ 2 * B ≤ 1 / 2 ∧ ε ^ 2 * C ≤ m := by
  let εbar := min 1
    (min (1 / (2 * (A + 1)))
      (min (1 / (2 * (B + 1))) (m / (C + m))))
  have hAden : 0 < 2 * (A + 1) := by positivity
  have hBden : 0 < 2 * (B + 1) := by positivity
  have hCm : 0 < C + m := by positivity
  have hεbar : 0 < εbar := by
    dsimp [εbar]
    positivity
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hε0 hε
  have hε1 : ε < 1 := hε.trans_le (min_le_left _ _)
  have hεA : ε < 1 / (2 * (A + 1)) :=
    hε.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεB : ε < 1 / (2 * (B + 1)) :=
    hε.trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hεC : ε < m / (C + m) :=
    hε.trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hεsq : ε ^ 2 ≤ ε := by
    nlinarith [mul_nonneg hε0.le (sub_nonneg.mpr hε1.le)]
  have hAmul : ε * (2 * (A + 1)) < 1 := by
    exact (lt_div_iff₀ hAden).mp (by simpa only [one_div] using hεA)
  have hBmul : ε * (2 * (B + 1)) < 1 := by
    exact (lt_div_iff₀ hBden).mp (by simpa only [one_div] using hεB)
  have hCmul : ε * (C + m) < m := (lt_div_iff₀ hCm).mp hεC
  refine ⟨hε1.le, ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg (sub_nonneg.mpr hεsq) hA]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hεsq) hB]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hεsq) hC]

theorem abs_standardQuadraticEnergyDefectTerm_le
    (ε q p : ℝ) :
    |(ε ^ 4 / 8) * (p ^ 2 - q ^ 2) +
        (ε ^ 6 / 32) * q ^ 2 +
        (ε ^ 3 / 4) * (1 - ε ^ 2 / 2) * (q * p)| ≤
      standardQuadraticEnergyErrorRate ε * (q ^ 2 + p ^ 2) := by
  have hsub : |p ^ 2 - q ^ 2| ≤ q ^ 2 + p ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg q, sq_nonneg p]
  have hmul : |q * p| ≤ (q ^ 2 + p ^ 2) / 2 := by
    rw [abs_le]
    constructor
    · nlinarith [sq_nonneg (q + p)]
    · nlinarith [sq_nonneg (q - p)]
  apply le_trans (abs_add_le _ _)
  apply le_trans (add_le_add (abs_add_le _ _) le_rfl)
  norm_num [abs_div, abs_pow, abs_sq]
  rw [← abs_mul q p]
  have h4 : 0 ≤ |ε| ^ 4 / 8 := by positivity
  have h6 : 0 ≤ |ε| ^ 6 / 32 := by positivity
  have h3 : 0 ≤ |ε| ^ 3 / 4 * |1 - ε ^ 2 / 2| := by positivity
  calc
    |ε| ^ 4 / 8 * |p ^ 2 - q ^ 2| +
          |ε| ^ 6 / 32 * q ^ 2 +
          |ε| ^ 3 / 4 * |1 - ε ^ 2 / 2| * |q * p| ≤
        |ε| ^ 4 / 8 * (q ^ 2 + p ^ 2) +
          |ε| ^ 6 / 32 * q ^ 2 +
          |ε| ^ 3 / 4 * |1 - ε ^ 2 / 2| *
            ((q ^ 2 + p ^ 2) / 2) := by gcongr
    _ ≤ standardQuadraticEnergyErrorRate ε * (q ^ 2 + p ^ 2) := by
      unfold standardQuadraticEnergyErrorRate
      nlinarith [sq_nonneg q, sq_nonneg p]

/-- The scalar Gaussian one-step defect is Lipschitz in the phase variables,
with the same cubic error rate and the natural product of phase difference
and phase size. -/
theorem abs_standardQuadraticEnergyDefectTerm_sub_le
    (ε q₁ p₁ q₂ p₂ : ℝ) :
    |((ε ^ 4 / 8) * (p₁ ^ 2 - q₁ ^ 2) +
        (ε ^ 6 / 32) * q₁ ^ 2 +
        (ε ^ 3 / 4) * (1 - ε ^ 2 / 2) * (q₁ * p₁)) -
      ((ε ^ 4 / 8) * (p₂ ^ 2 - q₂ ^ 2) +
        (ε ^ 6 / 32) * q₂ ^ 2 +
        (ε ^ 3 / 4) * (1 - ε ^ 2 / 2) * (q₂ * p₂))| ≤
      2 * standardQuadraticEnergyErrorRate ε *
        (|q₁ - q₂| + |p₁ - p₂|) *
        (|q₁| + |p₁| + |q₂| + |p₂|) := by
  let D := |q₁ - q₂| + |p₁ - p₂|
  let S := |q₁| + |p₁| + |q₂| + |p₂|
  have hD : 0 ≤ D := by positivity
  have hS : 0 ≤ S := by positivity
  have hq : |q₁ ^ 2 - q₂ ^ 2| ≤ D * S := by
    rw [show q₁ ^ 2 - q₂ ^ 2 = (q₁ - q₂) * (q₁ + q₂) by ring,
      abs_mul]
    have hsum : |q₁ + q₂| ≤ |q₁| + |q₂| := abs_add_le _ _
    apply mul_le_mul
    · dsimp [D]; linarith [abs_nonneg (p₁ - p₂)]
    · dsimp [S]; linarith [abs_nonneg p₁, abs_nonneg p₂]
    · exact abs_nonneg _
    · exact hD
  have hp : |p₁ ^ 2 - p₂ ^ 2| ≤ D * S := by
    rw [show p₁ ^ 2 - p₂ ^ 2 = (p₁ - p₂) * (p₁ + p₂) by ring,
      abs_mul]
    have hsum : |p₁ + p₂| ≤ |p₁| + |p₂| := abs_add_le _ _
    apply mul_le_mul
    · dsimp [D]; linarith [abs_nonneg (q₁ - q₂)]
    · dsimp [S]; linarith [abs_nonneg q₁, abs_nonneg q₂]
    · exact abs_nonneg _
    · exact hD
  have hcross : |q₁ * p₁ - q₂ * p₂| ≤ D * S := by
    rw [show q₁ * p₁ - q₂ * p₂ = (q₁ - q₂) * p₁ + q₂ * (p₁ - p₂) by ring]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul]
    dsimp [D, S]
    nlinarith [abs_nonneg (q₁ - q₂), abs_nonneg (p₁ - p₂),
      abs_nonneg q₁, abs_nonneg p₁, abs_nonneg q₂, abs_nonneg p₂]
  have hmain : |(p₁ ^ 2 - q₁ ^ 2) - (p₂ ^ 2 - q₂ ^ 2)| ≤
      2 * (D * S) := by
    rw [show (p₁ ^ 2 - q₁ ^ 2) - (p₂ ^ 2 - q₂ ^ 2) =
      (p₁ ^ 2 - p₂ ^ 2) - (q₁ ^ 2 - q₂ ^ 2) by ring]
    exact (abs_sub _ _).trans (by linarith)
  rw [show
    ((ε ^ 4 / 8) * (p₁ ^ 2 - q₁ ^ 2) +
        (ε ^ 6 / 32) * q₁ ^ 2 +
        (ε ^ 3 / 4) * (1 - ε ^ 2 / 2) * (q₁ * p₁)) -
      ((ε ^ 4 / 8) * (p₂ ^ 2 - q₂ ^ 2) +
        (ε ^ 6 / 32) * q₂ ^ 2 +
        (ε ^ 3 / 4) * (1 - ε ^ 2 / 2) * (q₂ * p₂)) =
      (ε ^ 4 / 8) * ((p₁ ^ 2 - q₁ ^ 2) - (p₂ ^ 2 - q₂ ^ 2)) +
        (ε ^ 6 / 32) * (q₁ ^ 2 - q₂ ^ 2) +
        ((ε ^ 3 / 4) * (1 - ε ^ 2 / 2)) *
          (q₁ * p₁ - q₂ * p₂) by ring]
  apply (abs_add_le _ _).trans
  apply le_trans (add_le_add (abs_add_le _ _) le_rfl)
  simp only [abs_mul]
  have hA : 0 ≤ |ε ^ 4 / 8| := abs_nonneg _
  have hB : 0 ≤ |ε ^ 6 / 32| := abs_nonneg _
  have hC : 0 ≤ |ε ^ 3 / 4| * |1 - ε ^ 2 / 2| := by positivity
  apply le_trans (add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left hmain hA)
      (mul_le_mul_of_nonneg_left hq hB))
    (mul_le_mul_of_nonneg_left hcross hC))
  have hrate :
      2 * |ε ^ 4 / 8| + |ε ^ 6 / 32| +
          |ε ^ 3 / 4| * |1 - ε ^ 2 / 2| ≤
        2 * standardQuadraticEnergyErrorRate ε := by
    unfold standardQuadraticEnergyErrorRate
    norm_num [abs_div, abs_pow]
    nlinarith [pow_nonneg (abs_nonneg ε) 6]
  calc
    |ε ^ 4 / 8| * (2 * (D * S)) + |ε ^ 6 / 32| * (D * S) +
        (|ε ^ 3 / 4| * |1 - ε ^ 2 / 2|) * (D * S) =
      (2 * |ε ^ 4 / 8| + |ε ^ 6 / 32| +
        |ε ^ 3 / 4| * |1 - ε ^ 2 / 2|) * D * S := by ring
    _ ≤ 2 * standardQuadraticEnergyErrorRate ε * D * S := by
      gcongr

omit [Fintype ι] in
/-- Position coordinate of one leapfrog step for the standard quadratic
potential. -/
theorem leapfrog_standardQuadratic_fst_apply
    (ε : ℝ) (z : PhaseSpace ι) (i : ι) :
    (leapfrog standardQuadraticGradient ε z).1 i =
      (1 - ε ^ 2 / 2) * z.1 i + ε * z.2 i := by
  simp [leapfrog, halfKick, drift, standardQuadraticGradient]
  ring

omit [Fintype ι] in
/-- Momentum coordinate of one leapfrog step for the standard quadratic
potential. -/
theorem leapfrog_standardQuadratic_snd_apply
    (ε : ℝ) (z : PhaseSpace ι) (i : ι) :
    (leapfrog standardQuadraticGradient ε z).2 i =
      (1 - ε ^ 2 / 2) * z.2 i + (-ε + ε ^ 3 / 4) * z.1 i := by
  simp [leapfrog, halfKick, drift, standardQuadraticGradient]
  ring

/-- Explicit arbitrary-step update from one-dimensional position `q` and
unit momentum. -/
theorem leapfrog_standardQuadratic_phase_one (ε q : ℝ) :
    leapfrog standardQuadraticGradient ε
        (standardQuadraticUnitPhase q 1) =
      standardQuadraticUnitPhase
        ((1 - ε ^ 2 / 2) * q + ε)
        ((1 - ε ^ 2 / 2) + (-ε + ε ^ 3 / 4) * q) := by
  apply Prod.ext <;> funext i
  · rw [leapfrog_standardQuadratic_fst_apply]
    simp [standardQuadraticUnitPhase]
  · rw [leapfrog_standardQuadratic_snd_apply]
    simp [standardQuadraticUnitPhase]

/-- The arbitrary-step polynomial is exactly the leapfrog energy defect. -/
theorem standardQuadraticOneStepDefect_eq_energy_sub (ε q : ℝ) :
    standardQuadraticOneStepDefect ε q =
      energy standardQuadraticPotential
          (leapfrog standardQuadraticGradient ε
            (standardQuadraticUnitPhase q 1)) -
        energy standardQuadraticPotential (standardQuadraticUnitPhase q 1) := by
  rw [leapfrog_standardQuadratic_phase_one,
    energy_standardQuadraticUnitPhase, energy_standardQuadraticUnitPhase]
  unfold standardQuadraticOneStepDefect
  ring

/-- The arbitrary-step logistic function is the actual two-point Boltzmann
endpoint probability. -/
theorem standardQuadraticEndpointProbability_eq_boltzmann (ε q : ℝ) :
    standardQuadraticEndpointProbability ε q =
      Real.exp (-energy standardQuadraticPotential
          (leapfrog standardQuadraticGradient ε
            (standardQuadraticUnitPhase q 1))) /
        (Real.exp (-energy standardQuadraticPotential
            (standardQuadraticUnitPhase q 1)) +
          Real.exp (-energy standardQuadraticPotential
            (leapfrog standardQuadraticGradient ε
              (standardQuadraticUnitPhase q 1)))) := by
  let E₀ := energy standardQuadraticPotential (standardQuadraticUnitPhase q 1)
  let E₁ := energy standardQuadraticPotential
    (leapfrog standardQuadraticGradient ε (standardQuadraticUnitPhase q 1))
  have hdefect : standardQuadraticOneStepDefect ε q = E₁ - E₀ :=
    standardQuadraticOneStepDefect_eq_energy_sub ε q
  unfold standardQuadraticEndpointProbability
  rw [hdefect, Real.exp_sub, Real.exp_neg, Real.exp_neg]
  dsimp only [E₀, E₁]
  field_simp [Real.exp_ne_zero]

/-- Both cross-index squared costs are explicit and converge to `ε²`. -/
theorem standardQuadratic_anchor_endpoint_squaredDistance (ε q : ℝ) :
    squaredEuclideanNorm
        ((standardQuadraticUnitPhase 0 1).1 -
          (leapfrog standardQuadraticGradient ε
            (standardQuadraticUnitPhase q 1)).1) =
      ((1 - ε ^ 2 / 2) * q + ε) ^ 2 := by
  rw [leapfrog_standardQuadratic_phase_one]
  simp [squaredEuclideanNorm, euclideanInner, standardQuadraticUnitPhase]
  ring

theorem standardQuadratic_endpoint_anchor_squaredDistance (ε q : ℝ) :
    squaredEuclideanNorm
        ((leapfrog standardQuadraticGradient ε
            (standardQuadraticUnitPhase 0 1)).1 -
          (standardQuadraticUnitPhase q 1).1) =
      (ε - q) ^ 2 := by
  rw [leapfrog_standardQuadratic_phase_one]
  simp [squaredEuclideanNorm, euclideanInner, standardQuadraticUnitPhase]
  ring

/-- At every positive step size at most one, the endpoint probability has a
uniform nonzero secant-slope floor near the diagonal. -/
theorem eventually_half_abs_deriv_lt_abs_slope_endpointProbability_of_step
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᶠ q in nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ,
      |deriv (standardQuadraticEndpointProbability ε) 0| / 2 <
        |slope (standardQuadraticEndpointProbability ε) 0 q| := by
  have ht : Filter.Tendsto
      (slope (standardQuadraticEndpointProbability ε) 0)
      (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ)
      (nhds (deriv (standardQuadraticEndpointProbability ε) 0)) := by
    simpa only [(hasDerivAt_standardQuadraticEndpointProbability_zero ε).deriv]
      using (hasDerivAt_standardQuadraticEndpointProbability_zero ε).tendsto_slope
  have habs : Filter.Tendsto
      (fun q => |slope (standardQuadraticEndpointProbability ε) 0 q|)
      (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ)
      (nhds |deriv (standardQuadraticEndpointProbability ε) 0|) :=
    (continuous_abs.tendsto _).comp ht
  apply (tendsto_order.1 habs).1
  exact div_lt_self
    (abs_pos.mpr (deriv_standardQuadraticEndpointProbability_zero_ne_zero
      hε0 hε1)) (by norm_num)

/-- For each fixed positive step size, both unequal-index costs retain the
positive local floor `ε²/2`. -/
theorem eventually_half_step_sq_lt_standardQuadratic_crossSquaredDistances
    {ε : ℝ} (hε0 : 0 < ε) :
    ∀ᶠ q in nhds (0 : ℝ),
      ε ^ 2 / 2 < squaredEuclideanNorm
        ((standardQuadraticUnitPhase 0 1).1 -
          (leapfrog standardQuadraticGradient ε
            (standardQuadraticUnitPhase q 1)).1) ∧
      ε ^ 2 / 2 < squaredEuclideanNorm
        ((leapfrog standardQuadraticGradient ε
          (standardQuadraticUnitPhase 0 1)).1 -
          (standardQuadraticUnitPhase q 1).1) := by
  have hfst : Filter.Tendsto
      (fun q : ℝ => ((1 - ε ^ 2 / 2) * q + ε) ^ 2)
      (nhds 0) (nhds (ε ^ 2)) := by
    have hc : ContinuousAt
        (fun q : ℝ => ((1 - ε ^ 2 / 2) * q + ε) ^ 2) 0 := by
      fun_prop
    change Filter.Tendsto
      (fun q : ℝ => ((1 - ε ^ 2 / 2) * q + ε) ^ 2) (nhds 0)
      (nhds (((1 - ε ^ 2 / 2) * 0 + ε) ^ 2)) at hc
    simpa using hc
  have hsnd : Filter.Tendsto (fun q : ℝ => (ε - q) ^ 2)
      (nhds 0) (nhds (ε ^ 2)) := by
    have hc : ContinuousAt (fun q : ℝ => (ε - q) ^ 2) 0 := by fun_prop
    change Filter.Tendsto (fun q : ℝ => (ε - q) ^ 2) (nhds 0)
      (nhds ((ε - 0) ^ 2)) at hc
    simpa using hc
  have hhalf : ε ^ 2 / 2 < ε ^ 2 := by nlinarith [sq_pos_of_pos hε0]
  filter_upwards [((tendsto_order.1 hfst).1 _ hhalf),
    ((tendsto_order.1 hsnd).1 _ hhalf)] with q hq₁ hq₂
  rw [standardQuadratic_anchor_endpoint_squaredDistance]
  rw [standardQuadratic_endpoint_anchor_squaredDistance]
  exact ⟨hq₁, hq₂⟩

/-- Explicit unit-step leapfrog update used by the two-index audit. -/
theorem leapfrog_standardQuadratic_unitPhase (q : ℝ) :
    leapfrog standardQuadraticGradient 1
        (standardQuadraticUnitPhase q 1) =
      standardQuadraticUnitPhase (q / 2 + 1) (1 / 2 - 3 * q / 4) := by
  apply Prod.ext <;> funext i
  · rw [leapfrog_standardQuadratic_fst_apply]
    simp [standardQuadraticUnitPhase]
    ring
  · rw [leapfrog_standardQuadratic_snd_apply]
    simp [standardQuadraticUnitPhase]
    ring

/-- The anchor of the first trajectory and endpoint of the second stay a
nonzero squared distance apart as the starting positions merge. -/
theorem standardQuadraticUnit_anchor_endpoint_squaredDistance (q : ℝ) :
    squaredEuclideanNorm
        ((standardQuadraticUnitPhase 0 1).1 -
          (leapfrog standardQuadraticGradient 1
            (standardQuadraticUnitPhase q 1)).1) =
      (q / 2 + 1) ^ 2 := by
  rw [leapfrog_standardQuadratic_unitPhase]
  simp [squaredEuclideanNorm, euclideanInner, standardQuadraticUnitPhase]
  ring

/-- The reverse unequal-index pairing has the same nonvanishing limiting
geometry. -/
theorem standardQuadraticUnit_endpoint_anchor_squaredDistance (q : ℝ) :
    squaredEuclideanNorm
        ((leapfrog standardQuadraticGradient 1
            (standardQuadraticUnitPhase 0 1)).1 -
          (standardQuadraticUnitPhase q 1).1) =
      (1 - q) ^ 2 := by
  rw [leapfrog_standardQuadratic_unitPhase]
  simp [squaredEuclideanNorm, euclideanInner, standardQuadraticUnitPhase]
  ring

/-- Both cross-index squared distances converge to one at coincident initial
positions, so the discrete support does not collapse in this nonzero-momentum
audit. -/
theorem tendsto_standardQuadraticUnit_crossSquaredDistances :
    Filter.Tendsto
        (fun q : ℝ =>
          (squaredEuclideanNorm
              ((standardQuadraticUnitPhase 0 1).1 -
                (leapfrog standardQuadraticGradient 1
                  (standardQuadraticUnitPhase q 1)).1),
            squaredEuclideanNorm
              ((leapfrog standardQuadraticGradient 1
                (standardQuadraticUnitPhase 0 1)).1 -
                (standardQuadraticUnitPhase q 1).1)))
        (nhds 0) (nhds (1, 1)) := by
  simp_rw [standardQuadraticUnit_anchor_endpoint_squaredDistance,
    standardQuadraticUnit_endpoint_anchor_squaredDistance]
  have hcontinuous : ContinuousAt
      (fun q : ℝ => ((q / 2 + 1) ^ 2, (1 - q) ^ 2)) 0 := by
    fun_prop
  change Filter.Tendsto (fun q : ℝ => ((q / 2 + 1) ^ 2, (1 - q) ^ 2))
    (nhds 0) (nhds (((0 : ℝ) / 2 + 1) ^ 2, (1 - (0 : ℝ)) ^ 2)) at hcontinuous
  norm_num at hcontinuous
  exact hcontinuous

/-- Consequently both unequal-index squared costs have the common positive
floor `1/2` throughout some neighborhood of coincident starting positions. -/
theorem eventually_half_lt_standardQuadraticUnit_crossSquaredDistances :
    ∀ᶠ q in nhds (0 : ℝ),
      1 / 2 < squaredEuclideanNorm
        ((standardQuadraticUnitPhase 0 1).1 -
          (leapfrog standardQuadraticGradient 1
            (standardQuadraticUnitPhase q 1)).1) ∧
      1 / 2 < squaredEuclideanNorm
        ((leapfrog standardQuadraticGradient 1
          (standardQuadraticUnitPhase 0 1)).1 -
          (standardQuadraticUnitPhase q 1).1) := by
  have ht := tendsto_standardQuadraticUnit_crossSquaredDistances
  have hfst : Filter.Tendsto
      (fun q : ℝ => squaredEuclideanNorm
        ((standardQuadraticUnitPhase 0 1).1 -
          (leapfrog standardQuadraticGradient 1
            (standardQuadraticUnitPhase q 1)).1))
      (nhds 0) (nhds 1) := (continuous_fst.tendsto (1, 1)).comp ht
  have hsnd : Filter.Tendsto
      (fun q : ℝ => squaredEuclideanNorm
        ((leapfrog standardQuadraticGradient 1
          (standardQuadraticUnitPhase 0 1)).1 -
          (standardQuadraticUnitPhase q 1).1))
      (nhds 0) (nhds 1) := (continuous_snd.tendsto (1, 1)).comp ht
  filter_upwards [((tendsto_order.1 hfst).1 (1 / 2) (by norm_num)),
    ((tendsto_order.1 hsnd).1 (1 / 2) (by norm_num))] with q hq₁ hq₂
  exact ⟨hq₁, hq₂⟩

/-- Combined local obstruction data for the actual two-point Gaussian
trajectory: its categorical endpoint probability separates linearly, while
both possible unequal-index squared costs stay uniformly positive. -/
theorem eventually_standardQuadraticUnit_linearWeight_positiveCrossCost :
    ∀ᶠ q in nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ,
      |deriv standardQuadraticUnitEndpointProbability 0| / 2 * |q| <
          |standardQuadraticUnitEndpointProbability q -
            standardQuadraticUnitEndpointProbability 0| ∧
        1 / 2 < squaredEuclideanNorm
          ((standardQuadraticUnitPhase 0 1).1 -
            (leapfrog standardQuadraticGradient 1
              (standardQuadraticUnitPhase q 1)).1) ∧
        1 / 2 < squaredEuclideanNorm
          ((leapfrog standardQuadraticGradient 1
            (standardQuadraticUnitPhase 0 1)).1 -
            (standardQuadraticUnitPhase q 1).1) := by
  have hfilter : nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ ≤ nhds 0 :=
    inf_le_left
  have hcross :=
    eventually_half_lt_standardQuadraticUnit_crossSquaredDistances.filter_mono
      hfilter
  filter_upwards
    [eventually_half_abs_deriv_lt_abs_slope_endpointProbability,
      hcross, self_mem_nhdsWithin] with q hslope hcross hq
  have hq0 : q ≠ 0 := by simpa using hq
  have hslopeEq : slope standardQuadraticUnitEndpointProbability 0 q =
      (standardQuadraticUnitEndpointProbability q -
        standardQuadraticUnitEndpointProbability 0) / q := by
    rw [slope_def_field]
    simp
  have hdiff :
      |slope standardQuadraticUnitEndpointProbability 0 q| * |q| =
        |standardQuadraticUnitEndpointProbability q -
          standardQuadraticUnitEndpointProbability 0| := by
    rw [hslopeEq, abs_div]
    exact div_mul_cancel₀ _ (abs_ne_zero.mpr hq0)
  refine ⟨?_, hcross⟩
  rw [← hdiff]
  exact mul_lt_mul_of_pos_right hslope (abs_pos.mpr hq0)

/-- The explicit polynomial really is the leapfrog energy defect. -/
theorem standardQuadraticUnitOneStepDefect_eq_energy_sub (q : ℝ) :
    standardQuadraticUnitOneStepDefect q =
      energy standardQuadraticPotential
          (leapfrog standardQuadraticGradient 1
            (standardQuadraticUnitPhase q 1)) -
        energy standardQuadraticPotential (standardQuadraticUnitPhase q 1) := by
  rw [leapfrog_standardQuadratic_unitPhase,
    energy_standardQuadraticUnitPhase, energy_standardQuadraticUnitPhase]
  unfold standardQuadraticUnitOneStepDefect
  ring

/-- The logistic audit function is exactly the Boltzmann probability of
selecting the leapfrog endpoint from the anchor/endpoint trajectory. -/
theorem standardQuadraticUnitEndpointProbability_eq_boltzmann (q : ℝ) :
    standardQuadraticUnitEndpointProbability q =
      Real.exp (-energy standardQuadraticPotential
          (leapfrog standardQuadraticGradient 1
            (standardQuadraticUnitPhase q 1))) /
        (Real.exp (-energy standardQuadraticPotential
            (standardQuadraticUnitPhase q 1)) +
          Real.exp (-energy standardQuadraticPotential
            (leapfrog standardQuadraticGradient 1
              (standardQuadraticUnitPhase q 1)))) := by
  let E₀ := energy standardQuadraticPotential (standardQuadraticUnitPhase q 1)
  let E₁ := energy standardQuadraticPotential
    (leapfrog standardQuadraticGradient 1 (standardQuadraticUnitPhase q 1))
  have hdefect : standardQuadraticUnitOneStepDefect q = E₁ - E₀ := by
    exact standardQuadraticUnitOneStepDefect_eq_energy_sub q
  unfold standardQuadraticUnitEndpointProbability
  rw [hdefect, Real.exp_sub, Real.exp_neg, Real.exp_neg]
  dsimp only [E₀, E₁]
  field_simp [Real.exp_ne_zero]

/-- With origin zero, the two-index offset trajectory consists exactly of the
anchor and one forward leapfrog endpoint. -/
theorem standardQuadratic_offsetTrajectory_zero (ε q : ℝ) :
    offsetLeapfrogTrajectory standardQuadraticGradient ε
        (0 : Fin 2) (standardQuadraticUnitPhase q 1) (0 : Fin 2) =
      standardQuadraticUnitPhase q 1 := by
  simp [offsetLeapfrogTrajectory]

theorem standardQuadratic_offsetTrajectory_one (ε q : ℝ) :
    offsetLeapfrogTrajectory standardQuadraticGradient ε
        (0 : Fin 2) (standardQuadraticUnitPhase q 1) (1 : Fin 2) =
      leapfrog standardQuadraticGradient ε
        (standardQuadraticUnitPhase q 1) := by
  change signedLeapfrog standardQuadraticGradient ε 1
    (standardQuadraticUnitPhase q 1) = _
  simp [signedLeapfrog]

theorem standardQuadraticUnit_offsetTrajectory_zero (q : ℝ) :
    offsetLeapfrogTrajectory standardQuadraticGradient 1
        (0 : Fin 2) (standardQuadraticUnitPhase q 1) (0 : Fin 2) =
      standardQuadraticUnitPhase q 1 := by
  simp [offsetLeapfrogTrajectory]

theorem standardQuadraticUnit_offsetTrajectory_one (q : ℝ) :
    offsetLeapfrogTrajectory standardQuadraticGradient 1
        (0 : Fin 2) (standardQuadraticUnitPhase q 1) (1 : Fin 2) =
      leapfrog standardQuadraticGradient 1
        (standardQuadraticUnitPhase q 1) := by
  change signedLeapfrog standardQuadraticGradient 1 1
    (standardQuadraticUnitPhase q 1) = _
  simp [signedLeapfrog]

/-- The real value of the actual categorical endpoint atom is the explicit
logistic probability differentiated above. -/
theorem toReal_standardQuadraticUnit_trajectoryIndexPMF_one (q : ℝ) :
    (trajectoryIndexPMF standardQuadraticPotential
      (offsetLeapfrogTrajectory standardQuadraticGradient 1
        (0 : Fin 2) (standardQuadraticUnitPhase q 1)) (1 : Fin 2)).toReal =
      standardQuadraticUnitEndpointProbability q := by
  let trajectory := offsetLeapfrogTrajectory standardQuadraticGradient 1
    (0 : Fin 2) (standardQuadraticUnitPhase q 1)
  have hnormalizer : trajectoryNormalizer standardQuadraticPotential trajectory =
      boltzmannWeight standardQuadraticPotential (standardQuadraticUnitPhase q 1) +
        boltzmannWeight standardQuadraticPotential
          (leapfrog standardQuadraticGradient 1
            (standardQuadraticUnitPhase q 1)) := by
    rw [trajectoryNormalizer, Fin.sum_univ_two]
    dsimp only [trajectory]
    rw [standardQuadraticUnit_offsetTrajectory_zero,
      standardQuadraticUnit_offsetTrajectory_one]
  change (trajectoryIndexPMF standardQuadraticPotential trajectory
    (1 : Fin 2)).toReal = _
  rw [trajectoryIndexPMF_apply]
  rw [hnormalizer]
  dsimp only [trajectory]
  rw [standardQuadraticUnit_offsetTrajectory_one]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
  rw [ENNReal.toReal_add
    (boltzmannWeight_ne_top standardQuadraticPotential
      (standardQuadraticUnitPhase q 1))
    (boltzmannWeight_ne_top standardQuadraticPotential
      (leapfrog standardQuadraticGradient 1
        (standardQuadraticUnitPhase q 1)))]
  simp only [boltzmannWeight, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  rw [standardQuadraticUnitEndpointProbability_eq_boltzmann]
  field_simp [Real.exp_ne_zero]

/-- Arbitrary-step version of the actual endpoint-atom formula. -/
theorem toReal_standardQuadratic_trajectoryIndexPMF_one (ε q : ℝ) :
    (trajectoryIndexPMF standardQuadraticPotential
      (offsetLeapfrogTrajectory standardQuadraticGradient ε
        (0 : Fin 2) (standardQuadraticUnitPhase q 1)) (1 : Fin 2)).toReal =
      standardQuadraticEndpointProbability ε q := by
  let trajectory := offsetLeapfrogTrajectory standardQuadraticGradient ε
    (0 : Fin 2) (standardQuadraticUnitPhase q 1)
  have hnormalizer : trajectoryNormalizer standardQuadraticPotential trajectory =
      boltzmannWeight standardQuadraticPotential (standardQuadraticUnitPhase q 1) +
        boltzmannWeight standardQuadraticPotential
          (leapfrog standardQuadraticGradient ε
            (standardQuadraticUnitPhase q 1)) := by
    rw [trajectoryNormalizer, Fin.sum_univ_two]
    dsimp only [trajectory]
    rw [standardQuadratic_offsetTrajectory_zero,
      standardQuadratic_offsetTrajectory_one]
  change (trajectoryIndexPMF standardQuadraticPotential trajectory
    (1 : Fin 2)).toReal = _
  rw [trajectoryIndexPMF_apply, hnormalizer]
  dsimp only [trajectory]
  rw [standardQuadratic_offsetTrajectory_one]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
  rw [ENNReal.toReal_add
    (boltzmannWeight_ne_top standardQuadraticPotential
      (standardQuadraticUnitPhase q 1))
    (boltzmannWeight_ne_top standardQuadraticPotential
      (leapfrog standardQuadraticGradient ε
        (standardQuadraticUnitPhase q 1)))]
  simp only [boltzmannWeight, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  rw [standardQuadraticEndpointProbability_eq_boltzmann]
  field_simp [Real.exp_ne_zero]

/-- For every fixed positive step size at most one, the actual two-index laws
separate at least linearly in total variation near the diagonal. -/
theorem eventually_standardQuadratic_linear_totalVariation
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᶠ q in nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ,
      |deriv (standardQuadraticEndpointProbability ε) 0| / 2 * |q| <
        (Mcmc.Finite.totalVariation
          (trajectoryIndexPMF standardQuadraticPotential
            (offsetLeapfrogTrajectory standardQuadraticGradient ε
              (0 : Fin 2) (standardQuadraticUnitPhase 0 1)))
          (trajectoryIndexPMF standardQuadraticPotential
            (offsetLeapfrogTrajectory standardQuadraticGradient ε
              (0 : Fin 2) (standardQuadraticUnitPhase q 1)))).toReal := by
  filter_upwards
    [eventually_half_abs_deriv_lt_abs_slope_endpointProbability_of_step
      hε0 hε1, self_mem_nhdsWithin] with q hslope hq
  have hq0 : q ≠ 0 := by simpa using hq
  have hslopeEq : slope (standardQuadraticEndpointProbability ε) 0 q =
      (standardQuadraticEndpointProbability ε q -
        standardQuadraticEndpointProbability ε 0) / q := by
    rw [slope_def_field]
    simp
  have hdiff :
      |slope (standardQuadraticEndpointProbability ε) 0 q| * |q| =
        |standardQuadraticEndpointProbability ε q -
          standardQuadraticEndpointProbability ε 0| := by
    rw [hslopeEq, abs_div]
    exact div_mul_cancel₀ _ (abs_ne_zero.mpr hq0)
  let p₀ := trajectoryIndexPMF standardQuadraticPotential
    (offsetLeapfrogTrajectory standardQuadraticGradient ε
      (0 : Fin 2) (standardQuadraticUnitPhase 0 1))
  let pq := trajectoryIndexPMF standardQuadraticPotential
    (offsetLeapfrogTrajectory standardQuadraticGradient ε
      (0 : Fin 2) (standardQuadraticUnitPhase q 1))
  calc
    |deriv (standardQuadraticEndpointProbability ε) 0| / 2 * |q| <
        |slope (standardQuadraticEndpointProbability ε) 0 q| * |q| :=
      mul_lt_mul_of_pos_right hslope (abs_pos.mpr hq0)
    _ = |standardQuadraticEndpointProbability ε q -
          standardQuadraticEndpointProbability ε 0| := hdiff
    _ = |(p₀ (1 : Fin 2)).toReal - (pq (1 : Fin 2)).toReal| := by
      rw [show (p₀ (1 : Fin 2)).toReal =
          standardQuadraticEndpointProbability ε 0 by
        exact toReal_standardQuadratic_trajectoryIndexPMF_one ε 0,
        show (pq (1 : Fin 2)).toReal =
          standardQuadraticEndpointProbability ε q by
        exact toReal_standardQuadratic_trajectoryIndexPMF_one ε q,
        abs_sub_comm]
    _ ≤ (Mcmc.Finite.totalVariation p₀ pq).toReal :=
      Mcmc.Finite.abs_toReal_sub_toReal_le_totalVariation_toReal
        p₀ pq (1 : Fin 2)

/-- The arbitrary-step cross-cost floor in the actual trajectory cost table. -/
theorem standardQuadratic_half_step_sq_le_trajectorySquaredPositionCost
    {ε q : ℝ}
    (hcross :
      ε ^ 2 / 2 < squaredEuclideanNorm
        ((standardQuadraticUnitPhase 0 1).1 -
          (leapfrog standardQuadraticGradient ε
            (standardQuadraticUnitPhase q 1)).1) ∧
      ε ^ 2 / 2 < squaredEuclideanNorm
        ((leapfrog standardQuadraticGradient ε
          (standardQuadraticUnitPhase 0 1)).1 -
          (standardQuadraticUnitPhase q 1).1))
    (i j : Fin 2) (hij : i ≠ j) :
    (⟨ε ^ 2 / 2, div_nonneg (sq_nonneg ε) (by norm_num)⟩ : NNReal) ≤
      trajectorySquaredPositionCost standardQuadraticGradient ε
        ((standardQuadraticUnitPhase 0 1,
          standardQuadraticUnitPhase q 1)) (0 : Fin 2) i j := by
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · apply NNReal.coe_le_coe.mp
    change ε ^ 2 / 2 ≤ squaredEuclideanNorm
      ((offsetLeapfrogTrajectory standardQuadraticGradient ε
          (0 : Fin 2) (standardQuadraticUnitPhase 0 1) (0 : Fin 2)).1 -
        (offsetLeapfrogTrajectory standardQuadraticGradient ε
          (0 : Fin 2) (standardQuadraticUnitPhase q 1) (1 : Fin 2)).1)
    rw [standardQuadratic_offsetTrajectory_zero,
      standardQuadratic_offsetTrajectory_one]
    exact hcross.1.le
  · apply NNReal.coe_le_coe.mp
    change ε ^ 2 / 2 ≤ squaredEuclideanNorm
      ((offsetLeapfrogTrajectory standardQuadraticGradient ε
          (0 : Fin 2) (standardQuadraticUnitPhase 0 1) (1 : Fin 2)).1 -
        (offsetLeapfrogTrajectory standardQuadraticGradient ε
          (0 : Fin 2) (standardQuadraticUnitPhase q 1) (0 : Fin 2)).1)
    rw [standardQuadratic_offsetTrajectory_one,
      standardQuadratic_offsetTrajectory_zero]
    exact hcross.2.le
  · exact False.elim (hij rfl)

/-- For every fixed `0 < ε ≤ 1`, even the optimal two-index transport cost
has a first-order lower bound near the diagonal: it is at least the linearly
varying TV distance times the positive floor `ε²/2`. -/
theorem eventually_standardQuadratic_optimalTransport_linearLowerBound
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᶠ q in nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ,
      let p₀ := trajectoryIndexPMF standardQuadraticPotential
        (offsetLeapfrogTrajectory standardQuadraticGradient ε
          (0 : Fin 2) (standardQuadraticUnitPhase 0 1))
      let pq := trajectoryIndexPMF standardQuadraticPotential
        (offsetLeapfrogTrajectory standardQuadraticGradient ε
          (0 : Fin 2) (standardQuadraticUnitPhase q 1))
      let cost := trajectorySquaredPositionCost standardQuadraticGradient ε
        ((standardQuadraticUnitPhase 0 1, standardQuadraticUnitPhase q 1))
        (0 : Fin 2)
      |deriv (standardQuadraticEndpointProbability ε) 0| / 2 * |q| <
          (Mcmc.Finite.totalVariation p₀ pq).toReal ∧
        Mcmc.Finite.totalVariation p₀ pq *
            ENNReal.ofNNReal
              (⟨ε ^ 2 / 2, div_nonneg (sq_nonneg ε) (by norm_num)⟩ : NNReal) ≤
          Mcmc.Finite.transportCost cost
            (Mcmc.Finite.optimalTransportCoupling p₀ pq cost) := by
  have hfilter : nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ ≤ nhds 0 :=
    inf_le_left
  have hcross :=
    (eventually_half_step_sq_lt_standardQuadratic_crossSquaredDistances hε0).filter_mono
      hfilter
  filter_upwards [eventually_standardQuadratic_linear_totalVariation hε0 hε1,
    hcross] with q htv hlocal
  dsimp only
  refine ⟨htv, ?_⟩
  exact Mcmc.Finite.totalVariation_mul_le_optimalTransportCost
    (trajectoryIndexPMF standardQuadraticPotential
      (offsetLeapfrogTrajectory standardQuadraticGradient ε
        (0 : Fin 2) (standardQuadraticUnitPhase 0 1)))
    (trajectoryIndexPMF standardQuadraticPotential
      (offsetLeapfrogTrajectory standardQuadraticGradient ε
        (0 : Fin 2) (standardQuadraticUnitPhase q 1)))
    (trajectorySquaredPositionCost standardQuadraticGradient ε
      ((standardQuadraticUnitPhase 0 1, standardQuadraticUnitPhase q 1))
      (0 : Fin 2))
    (⟨ε ^ 2 / 2, div_nonneg (sq_nonneg ε) (by norm_num)⟩ : NNReal)
    (fun i j hij =>
      standardQuadratic_half_step_sq_le_trajectorySquaredPositionCost
        ⟨hlocal.1, hlocal.2⟩ i j hij)

/-- Consequently, at every fixed two-index grid with `0 < ε ≤ 1`, optimal
transport cost eventually exceeds *every* prescribed quadratic rate in the
initial separation. -/
theorem eventually_rate_mul_sq_lt_standardQuadratic_optimalTransportCost
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (rate : ℝ) :
    ∀ᶠ q in nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ,
      rate * q ^ 2 <
        (Mcmc.Finite.transportCost
          (trajectorySquaredPositionCost standardQuadraticGradient ε
            ((standardQuadraticUnitPhase 0 1,
              standardQuadraticUnitPhase q 1)) (0 : Fin 2))
          (Mcmc.Finite.optimalTransportCoupling
            (trajectoryIndexPMF standardQuadraticPotential
              (offsetLeapfrogTrajectory standardQuadraticGradient ε
                (0 : Fin 2) (standardQuadraticUnitPhase 0 1)))
            (trajectoryIndexPMF standardQuadraticPotential
              (offsetLeapfrogTrajectory standardQuadraticGradient ε
                (0 : Fin 2) (standardQuadraticUnitPhase q 1)))
            (trajectorySquaredPositionCost standardQuadraticGradient ε
              ((standardQuadraticUnitPhase 0 1,
                standardQuadraticUnitPhase q 1)) (0 : Fin 2)))).toReal := by
  let left : ℝ → PMF (Fin 2) := fun _ =>
    trajectoryIndexPMF standardQuadraticPotential
      (offsetLeapfrogTrajectory standardQuadraticGradient ε
        (0 : Fin 2) (standardQuadraticUnitPhase 0 1))
  let right : ℝ → PMF (Fin 2) := fun q =>
    trajectoryIndexPMF standardQuadraticPotential
      (offsetLeapfrogTrajectory standardQuadraticGradient ε
        (0 : Fin 2) (standardQuadraticUnitPhase q 1))
  let cost : ℝ → Fin 2 → Fin 2 → NNReal := fun q =>
    trajectorySquaredPositionCost standardQuadraticGradient ε
      ((standardQuadraticUnitPhase 0 1, standardQuadraticUnitPhase q 1))
      (0 : Fin 2)
  let linearRate := |deriv (standardQuadraticEndpointProbability ε) 0| / 2
  let mismatchLower : NNReal :=
    ⟨ε ^ 2 / 2, div_nonneg (sq_nonneg ε) (by norm_num)⟩
  have hlinearRate : 0 < linearRate := by
    dsimp only [linearRate]
    positivity [deriv_standardQuadraticEndpointProbability_zero_ne_zero hε0 hε1]
  have hmismatchLower : 0 < mismatchLower := by
    apply NNReal.coe_pos.mp
    dsimp only [mismatchLower]
    exact div_pos (sq_pos_of_pos hε0) (by norm_num)
  have hTV : ∀ᶠ q in nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ,
      linearRate * |q| <
        (Mcmc.Finite.totalVariation (left q) (right q)).toReal := by
    simpa only [linearRate, left, right] using
      eventually_standardQuadratic_linear_totalVariation hε0 hε1
  have hfilter : nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ ≤ nhds 0 :=
    inf_le_left
  have hcross :=
    (eventually_half_step_sq_lt_standardQuadratic_crossSquaredDistances hε0).filter_mono
      hfilter
  have hcost : ∀ᶠ q in nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ,
      ∀ i j, i ≠ j → mismatchLower ≤ cost q i j := by
    filter_upwards [hcross] with q hq
    intro i j hij
    exact standardQuadratic_half_step_sq_le_trajectorySquaredPositionCost
      ⟨hq.1, hq.2⟩ i j hij
  simpa only [left, right, cost] using
    Mcmc.Finite.eventually_rate_mul_sq_lt_optimalTransportCost_toReal
      left right cost linearRate mismatchLower rate hlinearRate
      hmismatchLower hTV hcost

/-- The actual two-index trajectory laws therefore separate at least linearly
in total variation on a deleted neighborhood of coincident positions. -/
theorem eventually_standardQuadraticUnit_linear_totalVariation :
    ∀ᶠ q in nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ,
      |deriv standardQuadraticUnitEndpointProbability 0| / 2 * |q| <
        (Mcmc.Finite.totalVariation
          (trajectoryIndexPMF standardQuadraticPotential
            (offsetLeapfrogTrajectory standardQuadraticGradient 1
              (0 : Fin 2) (standardQuadraticUnitPhase 0 1)))
          (trajectoryIndexPMF standardQuadraticPotential
            (offsetLeapfrogTrajectory standardQuadraticGradient 1
              (0 : Fin 2) (standardQuadraticUnitPhase q 1)))).toReal := by
  filter_upwards
    [eventually_standardQuadraticUnit_linearWeight_positiveCrossCost] with q hq
  let p₀ := trajectoryIndexPMF standardQuadraticPotential
    (offsetLeapfrogTrajectory standardQuadraticGradient 1
      (0 : Fin 2) (standardQuadraticUnitPhase 0 1))
  let pq := trajectoryIndexPMF standardQuadraticPotential
    (offsetLeapfrogTrajectory standardQuadraticGradient 1
      (0 : Fin 2) (standardQuadraticUnitPhase q 1))
  calc
    |deriv standardQuadraticUnitEndpointProbability 0| / 2 * |q| <
        |standardQuadraticUnitEndpointProbability q -
          standardQuadraticUnitEndpointProbability 0| := hq.1
    _ = |(p₀ (1 : Fin 2)).toReal - (pq (1 : Fin 2)).toReal| := by
      rw [show (p₀ (1 : Fin 2)).toReal =
          standardQuadraticUnitEndpointProbability 0 by
        exact toReal_standardQuadraticUnit_trajectoryIndexPMF_one 0,
        show (pq (1 : Fin 2)).toReal =
          standardQuadraticUnitEndpointProbability q by
        exact toReal_standardQuadraticUnit_trajectoryIndexPMF_one q,
        abs_sub_comm]
    _ ≤ (Mcmc.Finite.totalVariation p₀ pq).toReal :=
      Mcmc.Finite.abs_toReal_sub_toReal_le_totalVariation_toReal
        p₀ pq (1 : Fin 2)

/-- The two explicit cross-distance estimates give a common `NNReal` floor
for every unequal pair of the actual two-index squared-position cost. -/
theorem standardQuadraticUnit_half_le_trajectorySquaredPositionCost
    {q : ℝ}
    (hcross :
      1 / 2 < squaredEuclideanNorm
        ((standardQuadraticUnitPhase 0 1).1 -
          (leapfrog standardQuadraticGradient 1
            (standardQuadraticUnitPhase q 1)).1) ∧
      1 / 2 < squaredEuclideanNorm
        ((leapfrog standardQuadraticGradient 1
          (standardQuadraticUnitPhase 0 1)).1 -
          (standardQuadraticUnitPhase q 1).1))
    (i j : Fin 2) (hij : i ≠ j) :
    (⟨1 / 2, by norm_num⟩ : NNReal) ≤
      trajectorySquaredPositionCost standardQuadraticGradient 1
        ((standardQuadraticUnitPhase 0 1,
          standardQuadraticUnitPhase q 1)) (0 : Fin 2) i j := by
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · apply NNReal.coe_le_coe.mp
    change (1 / 2 : ℝ) ≤ squaredEuclideanNorm
      ((offsetLeapfrogTrajectory standardQuadraticGradient 1
          (0 : Fin 2) (standardQuadraticUnitPhase 0 1) (0 : Fin 2)).1 -
        (offsetLeapfrogTrajectory standardQuadraticGradient 1
          (0 : Fin 2) (standardQuadraticUnitPhase q 1) (1 : Fin 2)).1)
    rw [standardQuadraticUnit_offsetTrajectory_zero,
      standardQuadraticUnit_offsetTrajectory_one]
    exact hcross.1.le
  · apply NNReal.coe_le_coe.mp
    change (1 / 2 : ℝ) ≤ squaredEuclideanNorm
      ((offsetLeapfrogTrajectory standardQuadraticGradient 1
          (0 : Fin 2) (standardQuadraticUnitPhase 0 1) (1 : Fin 2)).1 -
        (offsetLeapfrogTrajectory standardQuadraticGradient 1
          (0 : Fin 2) (standardQuadraticUnitPhase q 1) (0 : Fin 2)).1)
    rw [standardQuadraticUnit_offsetTrajectory_one,
      standardQuadraticUnit_offsetTrajectory_zero]
    exact hcross.2.le
  · exact False.elim (hij rfl)

/-- End-to-end lower bound for the actual optimal trajectory-index coupling.
Near coincident positions its marginal TV discrepancy is first order, and the
optimal squared cost must pay at least half of that discrepancy. -/
theorem eventually_standardQuadraticUnit_optimalTransport_linearLowerBound :
    ∀ᶠ q in nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ,
      let p₀ := trajectoryIndexPMF standardQuadraticPotential
        (offsetLeapfrogTrajectory standardQuadraticGradient 1
          (0 : Fin 2) (standardQuadraticUnitPhase 0 1))
      let pq := trajectoryIndexPMF standardQuadraticPotential
        (offsetLeapfrogTrajectory standardQuadraticGradient 1
          (0 : Fin 2) (standardQuadraticUnitPhase q 1))
      let cost := trajectorySquaredPositionCost standardQuadraticGradient 1
        ((standardQuadraticUnitPhase 0 1, standardQuadraticUnitPhase q 1))
        (0 : Fin 2)
      |deriv standardQuadraticUnitEndpointProbability 0| / 2 * |q| <
          (Mcmc.Finite.totalVariation p₀ pq).toReal ∧
        Mcmc.Finite.totalVariation p₀ pq *
            ENNReal.ofNNReal (⟨1 / 2, by norm_num⟩ : NNReal) ≤
          Mcmc.Finite.transportCost cost
            (Mcmc.Finite.optimalTransportCoupling p₀ pq cost) := by
  filter_upwards [eventually_standardQuadraticUnit_linear_totalVariation,
    eventually_standardQuadraticUnit_linearWeight_positiveCrossCost] with q htv hlocal
  dsimp only
  refine ⟨htv, ?_⟩
  have hlower := Mcmc.Finite.totalVariation_mul_le_optimalTransportCost
    (trajectoryIndexPMF standardQuadraticPotential
      (offsetLeapfrogTrajectory standardQuadraticGradient 1
        (0 : Fin 2) (standardQuadraticUnitPhase 0 1)))
    (trajectoryIndexPMF standardQuadraticPotential
      (offsetLeapfrogTrajectory standardQuadraticGradient 1
        (0 : Fin 2) (standardQuadraticUnitPhase q 1)))
    (trajectorySquaredPositionCost standardQuadraticGradient 1
      ((standardQuadraticUnitPhase 0 1, standardQuadraticUnitPhase q 1))
      (0 : Fin 2))
    (⟨1 / 2, by norm_num⟩ : NNReal)
    (fun i j hij =>
      standardQuadraticUnit_half_le_trajectorySquaredPositionCost
        ⟨hlocal.2.1, hlocal.2.2⟩ i j hij)
  exact hlower

/-- Scalar relative-state update induced by one standard-quadratic leapfrog
step. The first component multiplies an initial position difference and the
second component multiplies the corresponding momentum difference. -/
noncomputable def standardQuadraticDifferenceStep (ε : ℝ)
    (a : ℝ × ℝ) : ℝ × ℝ :=
  ((1 - ε ^ 2 / 2) * a.1 + ε * a.2,
    (-ε + ε ^ 3 / 4) * a.1 + (1 - ε ^ 2 / 2) * a.2)

/-- Relative-state coefficients after `n` aligned steps, initialized by a
unit position difference and zero momentum difference. -/
noncomputable def standardQuadraticDifferenceCoefficients
    (ε : ℝ) (n : ℕ) : ℝ × ℝ :=
  (standardQuadraticDifferenceStep ε)^[n] (1, 0)

@[simp]
theorem standardQuadraticDifferenceCoefficients_zero (ε : ℝ) :
    standardQuadraticDifferenceCoefficients ε 0 = (1, 0) := by
  simp [standardQuadraticDifferenceCoefficients]

theorem standardQuadraticDifferenceCoefficients_succ (ε : ℝ) (n : ℕ) :
    standardQuadraticDifferenceCoefficients ε (n + 1) =
      standardQuadraticDifferenceStep ε
        (standardQuadraticDifferenceCoefficients ε n) := by
  simp [standardQuadraticDifferenceCoefficients,
    Function.iterate_succ_apply']

/-- The Gaussian leapfrog position coefficient obeys the Chebyshev
second-order recurrence. -/
theorem standardQuadraticDifferenceCoefficients_fst_add_two
    (ε : ℝ) (n : ℕ) :
    (standardQuadraticDifferenceCoefficients ε (n + 2)).1 =
      2 * (1 - ε ^ 2 / 2) *
          (standardQuadraticDifferenceCoefficients ε (n + 1)).1 -
        (standardQuadraticDifferenceCoefficients ε n).1 := by
  rw [show n + 2 = (n + 1) + 1 by omega,
    standardQuadraticDifferenceCoefficients_succ,
    standardQuadraticDifferenceCoefficients_succ]
  simp only [standardQuadraticDifferenceStep]
  ring

/-- Closed polynomial form of the Gaussian leapfrog position coefficient. -/
theorem standardQuadraticDifferenceCoefficients_fst_eq_chebyshev
    (ε : ℝ) (n : ℕ) :
    (standardQuadraticDifferenceCoefficients ε n).1 =
      (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (1 - ε ^ 2 / 2) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [standardQuadraticDifferenceCoefficients]
  | one =>
      rw [standardQuadraticDifferenceCoefficients_succ]
      simp [standardQuadraticDifferenceCoefficients,
        standardQuadraticDifferenceStep]
  | more n ih0 ih1 =>
      rw [standardQuadraticDifferenceCoefficients_fst_add_two, ih0, ih1]
      push_cast
      rw [Polynomial.Chebyshev.T_add_two]
      simp

/-- In the stable regime `|ε| ≤ 2`, the Gaussian leapfrog position
coefficient is an exact cosine with modified angle
`arccos (1 - ε²/2)`. -/
theorem standardQuadraticDifferenceCoefficients_fst_eq_cos
    {ε : ℝ} (hε : |ε| ≤ 2) (n : ℕ) :
    (standardQuadraticDifferenceCoefficients ε n).1 =
      Real.cos ((n : ℝ) * Real.arccos (1 - ε ^ 2 / 2)) := by
  have hεsq : ε ^ 2 ≤ 4 := by
    have := (sq_le_sq₀ (abs_nonneg ε) (by norm_num : (0 : ℝ) ≤ 2)).mpr hε
    rw [sq_abs] at this
    norm_num at this ⊢
    exact this
  have haLower : -1 ≤ 1 - ε ^ 2 / 2 := by nlinarith
  have haUpper : 1 - ε ^ 2 / 2 ≤ 1 := by nlinarith [sq_nonneg ε]
  rw [standardQuadraticDifferenceCoefficients_fst_eq_chebyshev]
  conv_lhs =>
    rw [← Real.cos_arccos haLower haUpper]
  rw [Polynomial.Chebyshev.T_real_cos]
  norm_num

/-- Relative-state coefficients after `n` aligned steps, initialized by zero
position and unit momentum.  Its first component describes the Gaussian
leapfrog trajectory started from the origin with unit momentum. -/
noncomputable def standardQuadraticMomentumCoefficients
    (ε : ℝ) (n : ℕ) : ℝ × ℝ :=
  (standardQuadraticDifferenceStep ε)^[n] (0, 1)

@[simp]
theorem standardQuadraticMomentumCoefficients_zero (ε : ℝ) :
    standardQuadraticMomentumCoefficients ε 0 = (0, 1) := by
  simp [standardQuadraticMomentumCoefficients]

theorem standardQuadraticMomentumCoefficients_succ (ε : ℝ) (n : ℕ) :
    standardQuadraticMomentumCoefficients ε (n + 1) =
      standardQuadraticDifferenceStep ε
        (standardQuadraticMomentumCoefficients ε n) := by
  simp [standardQuadraticMomentumCoefficients,
    Function.iterate_succ_apply']

/-- The momentum-to-position coefficient obeys the same Chebyshev recurrence
as the position-difference coefficient. -/
theorem standardQuadraticMomentumCoefficients_fst_add_two
    (ε : ℝ) (n : ℕ) :
    (standardQuadraticMomentumCoefficients ε (n + 2)).1 =
      2 * (1 - ε ^ 2 / 2) *
          (standardQuadraticMomentumCoefficients ε (n + 1)).1 -
        (standardQuadraticMomentumCoefficients ε n).1 := by
  rw [show n + 2 = (n + 1) + 1 by omega,
    standardQuadraticMomentumCoefficients_succ,
    standardQuadraticMomentumCoefficients_succ]
  simp only [standardQuadraticDifferenceStep]
  ring

/-- Closed Chebyshev form of the momentum-to-position coefficient. -/
theorem standardQuadraticMomentumCoefficients_fst_eq_chebyshev
    (ε : ℝ) (n : ℕ) :
    (standardQuadraticMomentumCoefficients ε (n + 1)).1 =
      ε * (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval
        (1 - ε ^ 2 / 2) := by
  induction n using Nat.twoStepInduction with
  | zero =>
      rw [standardQuadraticMomentumCoefficients_succ]
      simp [standardQuadraticMomentumCoefficients,
        standardQuadraticDifferenceStep]
  | one =>
      rw [show 1 + 1 = 0 + 2 by omega,
        standardQuadraticMomentumCoefficients_fst_add_two]
      simp [standardQuadraticMomentumCoefficients,
        standardQuadraticDifferenceStep]
      ring
  | more n ih0 ih1 =>
      rw [show n + 2 + 1 = (n + 1) + 2 by omega,
        standardQuadraticMomentumCoefficients_fst_add_two, ih0, ih1]
      push_cast
      rw [Polynomial.Chebyshev.U_add_two]
      simp
      ring

/-- Sine form of the momentum-to-position coefficient, stated without a
division by `sin θ`. -/
theorem standardQuadraticMomentumCoefficients_fst_mul_sin
    {ε : ℝ} (hε : |ε| ≤ 2) (n : ℕ) :
    (standardQuadraticMomentumCoefficients ε n).1 *
        Real.sin (Real.arccos (1 - ε ^ 2 / 2)) =
      ε * Real.sin ((n : ℝ) * Real.arccos (1 - ε ^ 2 / 2)) := by
  cases n with
  | zero => simp
  | succ n =>
      have hεsq : ε ^ 2 ≤ 4 := by
        have := (sq_le_sq₀ (abs_nonneg ε) (by norm_num : (0 : ℝ) ≤ 2)).mpr hε
        rw [sq_abs] at this
        norm_num at this ⊢
        exact this
      have haLower : -1 ≤ 1 - ε ^ 2 / 2 := by nlinarith
      have haUpper : 1 - ε ^ 2 / 2 ≤ 1 := by nlinarith [sq_nonneg ε]
      let θ := Real.arccos (1 - ε ^ 2 / 2)
      have hcos : Real.cos θ = 1 - ε ^ 2 / 2 := by
        exact Real.cos_arccos haLower haUpper
      change (standardQuadraticMomentumCoefficients ε (n + 1)).1 *
          Real.sin θ = ε * Real.sin (((n + 1 : ℕ) : ℝ) * θ)
      rw [standardQuadraticMomentumCoefficients_fst_eq_chebyshev]
      rw [← hcos]
      rw [mul_assoc, Polynomial.Chebyshev.U_real_cos]
      push_cast
      ring_nf

/-- The coefficients initialized by `(0,1)` are the actual scalar standard-
Gaussian leapfrog trajectory from the origin with unit momentum. -/
theorem standardQuadratic_leapfrogN_origin_unitMomentum
    (ε : ℝ) (n : ℕ) :
    leapfrogN standardQuadraticGradient ε n
        (standardQuadraticUnitPhase 0 1) =
      standardQuadraticUnitPhase
        (standardQuadraticMomentumCoefficients ε n).1
        (standardQuadraticMomentumCoefficients ε n).2 := by
  induction n with
  | zero => simp [standardQuadraticUnitPhase]
  | succ n ih =>
      rw [leapfrogN_succ, ih]
      apply Prod.ext <;> funext i
      · rw [leapfrog_standardQuadratic_fst_apply]
        rw [show n + 1 = n + 1 by rfl,
          standardQuadraticMomentumCoefficients_succ]
        simp [standardQuadraticUnitPhase,
          standardQuadraticDifferenceStep]
      · rw [leapfrog_standardQuadratic_snd_apply]
        rw [show n + 1 = n + 1 by rfl,
          standardQuadraticMomentumCoefficients_succ]
        simp [standardQuadraticUnitPhase,
          standardQuadraticDifferenceStep]
        ring

omit [Fintype ι] in
/-- With trajectory origin zero, an offset trajectory index is ordinary
forward leapfrog iteration. -/
theorem offsetLeapfrogTrajectory_zero_eq_leapfrogN
    (gradient : Position ι → Position ι) (ε : ℝ) {L : ℕ}
    (z : PhaseSpace ι) (i : Fin (L + 1)) :
    offsetLeapfrogTrajectory gradient ε (0 : Fin (L + 1)) z i =
      leapfrogN gradient ε i.val z := by
  rw [offsetLeapfrogTrajectory]
  have horigin : (((0 : Fin (L + 1)).val : ℤ)) = 0 := rfl
  rw [horigin, sub_zero]
  simp only [signedLeapfrog, zpow_natCast, leapfrogN,
    Equiv.Perm.coe_pow, coe_leapfrogPerm]

/-- The modified leapfrog angle is at least the physical step size for a
positive stable step. -/
theorem le_standardQuadraticModifiedAngle
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε2 : ε ≤ 2) :
    ε ≤ Real.arccos (1 - ε ^ 2 / 2) := by
  have hεπ : ε ≤ Real.pi := hε2.trans Real.two_le_pi
  have hcos : 1 - ε ^ 2 / 2 ≤ Real.cos ε :=
    Real.one_sub_sq_div_two_le_cos
  have harccos := Real.arccos_le_arccos hcos
  rw [Real.arccos_cos hε0 hεπ] at harccos
  exact harccos

/-- The modified leapfrog angle is at most `(π/2)ε` on the positive stable
range. Together with the lower bound above, this controls discrete times
uniformly as the step size tends to zero. -/
theorem standardQuadraticModifiedAngle_le
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε2 : ε ≤ 2) :
    Real.arccos (1 - ε ^ 2 / 2) ≤ (Real.pi / 2) * ε := by
  let θ := Real.arccos (1 - ε ^ 2 / 2)
  have hεsq : ε ^ 2 ≤ 4 := by nlinarith
  have haLower : -1 ≤ 1 - ε ^ 2 / 2 := by nlinarith
  have haUpper : 1 - ε ^ 2 / 2 ≤ 1 := by nlinarith [sq_nonneg ε]
  have hθ0 : 0 ≤ θ := Real.arccos_nonneg _
  have hθπ : θ ≤ Real.pi := Real.arccos_le_pi _
  have habsθ : |θ| ≤ Real.pi := by rw [abs_of_nonneg hθ0]; exact hθπ
  have hcos := Real.cos_le_one_sub_mul_cos_sq habsθ
  rw [Real.cos_arccos haLower haUpper] at hcos
  have hπ0 : 0 < Real.pi := Real.pi_pos
  have hsquares : θ ^ 2 ≤ (Real.pi / 2 * ε) ^ 2 := by
    have hπsq : 0 < Real.pi ^ 2 := sq_pos_of_pos hπ0
    have hcpos : 0 < 2 / Real.pi ^ 2 := div_pos (by norm_num) hπsq
    have hcore : (2 / Real.pi ^ 2) * θ ^ 2 ≤ ε ^ 2 / 2 := by
      linarith
    calc
      θ ^ 2 ≤ (ε ^ 2 / 2) / (2 / Real.pi ^ 2) := by
        apply (le_div_iff₀ hcpos).2
        simpa only [mul_comm] using hcore
      _ = (Real.pi / 2 * ε) ^ 2 := by
        field_simp [ne_of_gt hπ0]
  exact (sq_le_sq₀ hθ0
    (mul_nonneg (div_nonneg hπ0.le (by norm_num)) hε0)).mp hsquares

/-- Before physical time one, the scalar standard-Gaussian leapfrog positions
started from the origin with positive unit momentum are strictly ordered by
their step indices. -/
theorem standardQuadraticMomentumCoefficients_fst_strictMono_before_one
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {i j : ℕ}
    (hij : i < j) (hj : (j : ℝ) * ε ≤ 1) :
    (standardQuadraticMomentumCoefficients ε i).1 <
      (standardQuadraticMomentumCoefficients ε j).1 := by
  let θ := Real.arccos (1 - ε ^ 2 / 2)
  have hε2 : ε ≤ 2 := hε1.trans (by norm_num)
  have habsε : |ε| ≤ 2 := by
    rw [abs_of_pos hε0]
    exact hε2
  have hθLower : ε ≤ θ :=
    le_standardQuadraticModifiedAngle hε0.le hε2
  have hθ0 : 0 < θ := hε0.trans_le hθLower
  have hθUpper : θ ≤ (Real.pi / 2) * ε :=
    standardQuadraticModifiedAngle_le hε0.le hε2
  have hi0 : 0 ≤ (i : ℝ) * θ := mul_nonneg (Nat.cast_nonneg _) hθ0.le
  have hijReal : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
  have hijθ : (i : ℝ) * θ < (j : ℝ) * θ :=
    mul_lt_mul_of_pos_right hijReal hθ0
  have hjθ : (j : ℝ) * θ ≤ Real.pi / 2 := by
    calc
      (j : ℝ) * θ ≤ (j : ℝ) * ((Real.pi / 2) * ε) := by
        exact mul_le_mul_of_nonneg_left hθUpper (Nat.cast_nonneg _)
      _ = (Real.pi / 2) * ((j : ℝ) * ε) := by ring
      _ ≤ Real.pi / 2 := by
        have hπhalf : 0 ≤ Real.pi / 2 := by positivity
        simpa using mul_le_mul_of_nonneg_left hj hπhalf
  have hsinLt : Real.sin ((i : ℝ) * θ) < Real.sin ((j : ℝ) * θ) :=
    Real.strictMonoOn_sin
      ⟨by linarith [Real.pi_pos], hijθ.le.trans hjθ⟩
      ⟨by linarith [Real.pi_pos], hjθ⟩ hijθ
  have hjOne : (1 : ℝ) ≤ (j : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega : j ≠ 0))
  have hθ_le_jθ : θ ≤ (j : ℝ) * θ := by
    nlinarith
  have hθπ : θ < Real.pi :=
    (hθ_le_jθ.trans hjθ).trans_lt (by linarith [Real.pi_pos])
  have hsinθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have hiFormula := standardQuadraticMomentumCoefficients_fst_mul_sin
    habsε i
  have hjFormula := standardQuadraticMomentumCoefficients_fst_mul_sin
    habsε j
  change (standardQuadraticMomentumCoefficients ε i).1 * Real.sin θ =
      ε * Real.sin ((i : ℝ) * θ) at hiFormula
  change (standardQuadraticMomentumCoefficients ε j).1 * Real.sin θ =
      ε * Real.sin ((j : ℝ) * θ) at hjFormula
  have hprod :
      (standardQuadraticMomentumCoefficients ε i).1 * Real.sin θ <
        (standardQuadraticMomentumCoefficients ε j).1 * Real.sin θ := by
    rw [hiFormula, hjFormula]
    exact mul_lt_mul_of_pos_left hsinLt hε0
  exact lt_of_mul_lt_mul_right hprod hsinθ.le

/-- Every off-diagonal squared-position cost of the origin-rooted scalar
Gaussian trajectory is positive while its physical horizon is at most one. -/
theorem standardQuadratic_trajectorySquaredPositionCost_pos_before_one
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {L : ℕ}
    (hL : (L : ℝ) * ε ≤ 1) (i j : Fin (L + 1)) (hij : i ≠ j) :
    0 < trajectorySquaredPositionCost standardQuadraticGradient ε
      ((standardQuadraticUnitPhase 0 1,
        standardQuadraticUnitPhase 0 1)) (0 : Fin (L + 1)) i j := by
  have indexHorizon (k : Fin (L + 1)) : (k.val : ℝ) * ε ≤ 1 := by
    have hkNat : k.val ≤ L := by omega
    have hkReal : (k.val : ℝ) ≤ (L : ℝ) := by exact_mod_cast hkNat
    exact (mul_le_mul_of_nonneg_right hkReal hε0.le).trans hL
  have hval : i.val ≠ j.val := Fin.val_ne_of_ne hij
  have hcoeff :
      (standardQuadraticMomentumCoefficients ε i.val).1 ≠
        (standardQuadraticMomentumCoefficients ε j.val).1 := by
    rcases lt_or_gt_of_ne hval with hlt | hgt
    · exact ne_of_lt
        (standardQuadraticMomentumCoefficients_fst_strictMono_before_one
          hε0 hε1 hlt (indexHorizon j))
    · exact ne_of_gt
        (standardQuadraticMomentumCoefficients_fst_strictMono_before_one
          hε0 hε1 hgt (indexHorizon i))
  apply NNReal.coe_pos.mp
  change 0 < squaredEuclideanNorm
    ((offsetLeapfrogTrajectory standardQuadraticGradient ε
        (0 : Fin (L + 1)) (standardQuadraticUnitPhase 0 1) i).1 -
      (offsetLeapfrogTrajectory standardQuadraticGradient ε
        (0 : Fin (L + 1)) (standardQuadraticUnitPhase 0 1) j).1)
  apply squaredEuclideanNorm_pos
  apply sub_ne_zero.mpr
  rw [offsetLeapfrogTrajectory_zero_eq_leapfrogN,
    offsetLeapfrogTrajectory_zero_eq_leapfrogN,
    standardQuadratic_leapfrogN_origin_unitMomentum,
    standardQuadratic_leapfrogN_origin_unitMomentum]
  intro heq
  have heqAt := congrFun heq Unit.unit
  simp only [standardQuadraticUnitPhase] at heqAt
  exact hcoeff heqAt

/-- Finiteness upgrades pointwise trajectory separation to one common
positive off-diagonal squared-cost floor. -/
theorem exists_standardQuadratic_pos_trajectoryCostFloor_before_one
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {L : ℕ} (hLpos : 0 < L)
    (hL : (L : ℝ) * ε ≤ 1) :
    ∃ floor : NNReal, 0 < floor ∧
      ∀ i j : Fin (L + 1), i ≠ j →
        floor ≤ trajectorySquaredPositionCost standardQuadraticGradient ε
          ((standardQuadraticUnitPhase 0 1,
            standardQuadraticUnitPhase 0 1)) (0 : Fin (L + 1)) i j := by
  letI : Nontrivial (Fin (L + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  exact Mcmc.Finite.exists_pos_mismatchCostFloor _
    (standardQuadratic_trajectorySquaredPositionCost_pos_before_one
      hε0 hε1 hL)

/-- Real Boltzmann weight of a forward scalar Gaussian leapfrog point. -/
noncomputable def standardQuadraticForwardWeight
    (ε : ℝ) (n : ℕ) (q : ℝ) : ℝ :=
  Real.exp (-energy standardQuadraticPotential
    (leapfrogN standardQuadraticGradient ε n
      (standardQuadraticUnitPhase q 1)))

/-- Real normalizer of the first `L+1` forward scalar Gaussian trajectory
weights. -/
noncomputable def standardQuadraticForwardNormalizer
    (ε : ℝ) (L : ℕ) (q : ℝ) : ℝ :=
  ∑ i : Fin (L + 1), standardQuadraticForwardWeight ε i.val q

/-- A normalized real atom of the forward scalar Gaussian trajectory law. -/
noncomputable def standardQuadraticForwardAtom
    (ε : ℝ) (L : ℕ) (i : Fin (L + 1)) (q : ℝ) : ℝ :=
  standardQuadraticForwardWeight ε i.val q /
    standardQuadraticForwardNormalizer ε L q

/-- Every forward scalar Gaussian trajectory weight is differentiable in its
initial position. -/
theorem differentiable_standardQuadratic_leapfrogN_unitPhase
    (ε : ℝ) (n : ℕ) :
    Differentiable ℝ (fun q => leapfrogN standardQuadraticGradient ε n
      (standardQuadraticUnitPhase q 1)) := by
  induction n with
  | zero =>
      simp only [leapfrogN_zero]
      unfold standardQuadraticUnitPhase
      fun_prop
  | succ n ih =>
      have ihfst : Differentiable ℝ (fun q =>
          (leapfrogN standardQuadraticGradient ε n
            (standardQuadraticUnitPhase q 1)).1) := ih.fst
      have ihsnd : Differentiable ℝ (fun q =>
          (leapfrogN standardQuadraticGradient ε n
            (standardQuadraticUnitPhase q 1)).2) := ih.snd
      simp_rw [leapfrogN_succ]
      simp only [leapfrog, halfKick, drift, standardQuadraticGradient]
      fun_prop (disch := assumption)

theorem differentiable_standardQuadraticForwardWeight
    (ε : ℝ) (n : ℕ) :
    Differentiable ℝ (standardQuadraticForwardWeight ε n) := by
  have htrajectory :=
    differentiable_standardQuadratic_leapfrogN_unitPhase ε n
  have hposition : Differentiable ℝ (fun q =>
      (leapfrogN standardQuadraticGradient ε n
        (standardQuadraticUnitPhase q 1)).1) := htrajectory.fst
  have hmomentum : Differentiable ℝ (fun q =>
      (leapfrogN standardQuadraticGradient ε n
        (standardQuadraticUnitPhase q 1)).2) := htrajectory.snd
  unfold standardQuadraticForwardWeight energy standardQuadraticPotential
    kineticEnergy
  fun_prop (disch := assumption)

theorem standardQuadraticForwardWeight_pos (ε : ℝ) (n : ℕ) (q : ℝ) :
    0 < standardQuadraticForwardWeight ε n q := by
  exact Real.exp_pos _

theorem standardQuadraticForwardNormalizer_pos (ε : ℝ) (L : ℕ) (q : ℝ) :
    0 < standardQuadraticForwardNormalizer ε L q := by
  unfold standardQuadraticForwardNormalizer
  refine (standardQuadraticForwardWeight_pos ε 0 q).trans_le ?_
  exact Finset.single_le_sum
    (fun i _ => (standardQuadraticForwardWeight_pos ε i.val q).le)
    (Finset.mem_univ (0 : Fin (L + 1)))

theorem differentiable_standardQuadraticForwardNormalizer
    (ε : ℝ) (L : ℕ) :
    Differentiable ℝ (standardQuadraticForwardNormalizer ε L) := by
  unfold standardQuadraticForwardNormalizer
  exact Differentiable.fun_sum (u := Finset.univ)
    (fun (i : Fin (L + 1)) _ =>
      differentiable_standardQuadraticForwardWeight ε i.val)

theorem differentiable_standardQuadraticForwardAtom
    (ε : ℝ) (L : ℕ) (i : Fin (L + 1)) :
    Differentiable ℝ (standardQuadraticForwardAtom ε L i) := by
  unfold standardQuadraticForwardAtom
  exact (differentiable_standardQuadraticForwardWeight ε i.val).div
    (differentiable_standardQuadraticForwardNormalizer ε L)
    (fun q => ne_of_gt (standardQuadraticForwardNormalizer_pos ε L q))

theorem standardQuadraticForwardAtom_pos
    (ε : ℝ) (L : ℕ) (i : Fin (L + 1)) (q : ℝ) :
    0 < standardQuadraticForwardAtom ε L i q := by
  exact div_pos (standardQuadraticForwardWeight_pos ε i.val q)
    (standardQuadraticForwardNormalizer_pos ε L q)

/-- The real-valued atom above is exactly the corresponding atom of the
mathlib-native `PMF` used by multinomial HMC. -/
theorem toReal_standardQuadratic_forwardTrajectoryIndexPMF
    (ε : ℝ) (L : ℕ) (i : Fin (L + 1)) (q : ℝ) :
    (trajectoryIndexPMF standardQuadraticPotential
      (offsetLeapfrogTrajectory standardQuadraticGradient ε
        (0 : Fin (L + 1)) (standardQuadraticUnitPhase q 1)) i).toReal =
      standardQuadraticForwardAtom ε L i q := by
  let trajectory := offsetLeapfrogTrajectory standardQuadraticGradient ε
    (0 : Fin (L + 1)) (standardQuadraticUnitPhase q 1)
  change (trajectoryIndexPMF standardQuadraticPotential trajectory i).toReal = _
  rw [trajectoryIndexPMF_apply, ENNReal.toReal_mul, ENNReal.toReal_inv]
  rw [show (trajectoryNormalizer standardQuadraticPotential trajectory).toReal =
      standardQuadraticForwardNormalizer ε L q by
    rw [trajectoryNormalizer, ENNReal.toReal_sum
      (fun k _ => boltzmannWeight_ne_top standardQuadraticPotential
        (trajectory k))]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [boltzmannWeight,
      ENNReal.toReal_ofReal (Real.exp_pos _).le]
    rw [show trajectory k = leapfrogN standardQuadraticGradient ε k.val
        (standardQuadraticUnitPhase q 1) by
      exact offsetLeapfrogTrajectory_zero_eq_leapfrogN _ _ _ _]
    rfl]
  rw [show (boltzmannWeight standardQuadraticPotential (trajectory i)).toReal =
      standardQuadraticForwardWeight ε i.val q by
    simp only [boltzmannWeight,
      ENNReal.toReal_ofReal (Real.exp_pos _).le]
    rw [show trajectory i = leapfrogN standardQuadraticGradient ε i.val
        (standardQuadraticUnitPhase q 1) by
      exact offsetLeapfrogTrajectory_zero_eq_leapfrogN _ _ _ _]
    rfl]
  exact (div_eq_mul_inv _ _).symm

/-- Normalization cancels from the ratio of any two forward trajectory
atoms. -/
theorem standardQuadraticForwardAtom_div
    (ε : ℝ) (L : ℕ) (i j : Fin (L + 1)) (q : ℝ) :
    standardQuadraticForwardAtom ε L i q /
        standardQuadraticForwardAtom ε L j q =
      standardQuadraticForwardWeight ε i.val q /
        standardQuadraticForwardWeight ε j.val q := by
  unfold standardQuadraticForwardAtom
  field_simp [ne_of_gt (standardQuadraticForwardNormalizer_pos ε L q)]

/-- The ratio of the first endpoint weight to the initial weight is the
exponential of the negative one-step energy defect. -/
theorem standardQuadraticForwardWeight_one_div_zero
    (ε q : ℝ) :
    standardQuadraticForwardWeight ε 1 q /
        standardQuadraticForwardWeight ε 0 q =
      Real.exp (-standardQuadraticOneStepDefect ε q) := by
  rw [standardQuadraticOneStepDefect_eq_energy_sub]
  simp only [standardQuadraticForwardWeight, leapfrogN_zero]
  rw [show leapfrogN standardQuadraticGradient ε 1
      (standardQuadraticUnitPhase q 1) =
        leapfrog standardQuadraticGradient ε
          (standardQuadraticUnitPhase q 1) by
      rw [show 1 = 0 + 1 by omega, leapfrogN_succ, leapfrogN_zero]]
  apply (div_eq_iff (Real.exp_ne_zero _)).2
  rw [← Real.exp_add]
  congr 1
  ring

/-- For any trajectory containing the first step, the ratio of its first two
normalized atoms is independent of all later normalization terms. -/
theorem standardQuadraticForwardAtom_one_div_zero
    (ε : ℝ) {L : ℕ} (hL : 0 < L) (q : ℝ) :
    standardQuadraticForwardAtom ε L ⟨1, by omega⟩ q /
        standardQuadraticForwardAtom ε L 0 q =
      Real.exp (-standardQuadraticOneStepDefect ε q) := by
  rw [standardQuadraticForwardAtom_div]
  simpa using standardQuadraticForwardWeight_one_div_zero ε q

/-- At every positive stable step, at least one of the first two normalized
multinomial atoms has nonzero first variation.  This conclusion is uniform in
the number of later trajectory points because it is detected by their ratio. -/
theorem standardQuadraticForwardAtom_deriv_zero_or_one_ne_zero
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {L : ℕ} (hL : 0 < L) :
    deriv (standardQuadraticForwardAtom ε L 0) 0 ≠ 0 ∨
      deriv (standardQuadraticForwardAtom ε L ⟨1, by omega⟩) 0 ≠ 0 := by
  let first : Fin (L + 1) := ⟨1, by omega⟩
  let initial : Fin (L + 1) := 0
  by_contra h
  push Not at h
  change deriv (standardQuadraticForwardAtom ε L initial) 0 = 0 ∧
    deriv (standardQuadraticForwardAtom ε L first) 0 = 0 at h
  have hInitialDiff : DifferentiableAt ℝ
      (standardQuadraticForwardAtom ε L initial) 0 :=
    (differentiable_standardQuadraticForwardAtom ε L initial).differentiableAt
  have hFirstDiff : DifferentiableAt ℝ
      (standardQuadraticForwardAtom ε L first) 0 :=
    (differentiable_standardQuadraticForwardAtom ε L first).differentiableAt
  have hquotientZero : HasDerivAt
      (standardQuadraticForwardAtom ε L first /
        standardQuadraticForwardAtom ε L initial) 0 0 := by
    have hdiv := hFirstDiff.hasDerivAt.div hInitialDiff.hasDerivAt
      (ne_of_gt (standardQuadraticForwardAtom_pos ε L initial 0))
    simpa only [Pi.div_apply, h.1, h.2, zero_mul, mul_zero, sub_zero,
      zero_div] using hdiv
  have hdefect := hasDerivAt_standardQuadraticOneStepDefect_zero ε
  have hexp := hdefect.neg.exp
  have hcoefficient :
      Real.exp (-standardQuadraticOneStepDefect ε 0) *
          (-(ε ^ 3 / 4 * (1 - ε ^ 2 / 2))) ≠ 0 := by
    apply mul_ne_zero (Real.exp_ne_zero _)
    have hfactor : ε ^ 3 / 4 * (1 - ε ^ 2 / 2) ≠ 0 := by
      have hεsq : ε ^ 2 ≤ 1 := by nlinarith
      have hright : 0 < 1 - ε ^ 2 / 2 := by nlinarith
      exact mul_ne_zero (div_ne_zero (pow_ne_zero 3 hε0.ne') (by norm_num))
        hright.ne'
    exact neg_ne_zero.mpr hfactor
  have hratio :
      (standardQuadraticForwardAtom ε L first /
        standardQuadraticForwardAtom ε L initial) =
      (fun q => Real.exp (-standardQuadraticOneStepDefect ε q)) := by
    funext q
    exact standardQuadraticForwardAtom_one_div_zero ε hL q
  rw [hratio] at hquotientZero
  have hunique := hexp.unique hquotientZero
  exact hcoefficient hunique

/-- The nonzero normalized first variation occurs in an atom of the actual
multinomial-HMC trajectory-index `PMF`, not merely in an auxiliary real
normalization. -/
theorem exists_standardQuadratic_forwardTrajectoryIndexPMF_deriv_ne_zero
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {L : ℕ} (hL : 0 < L) :
    ∃ i : Fin (L + 1),
      deriv (fun q =>
        (trajectoryIndexPMF standardQuadraticPotential
          (offsetLeapfrogTrajectory standardQuadraticGradient ε
            (0 : Fin (L + 1)) (standardQuadraticUnitPhase q 1)) i).toReal)
        0 ≠ 0 := by
  rcases standardQuadraticForwardAtom_deriv_zero_or_one_ne_zero
      hε0 hε1 hL with hzero | hone
  · refine ⟨0, ?_⟩
    have hfun : (fun q =>
        (trajectoryIndexPMF standardQuadraticPotential
          (offsetLeapfrogTrajectory standardQuadraticGradient ε
            (0 : Fin (L + 1)) (standardQuadraticUnitPhase q 1))
          (0 : Fin (L + 1))).toReal) =
        standardQuadraticForwardAtom ε L 0 := by
      funext q
      exact toReal_standardQuadratic_forwardTrajectoryIndexPMF ε L 0 q
    rw [hfun]
    exact hzero
  · refine ⟨⟨1, by omega⟩, ?_⟩
    have hfun : (fun q =>
        (trajectoryIndexPMF standardQuadraticPotential
          (offsetLeapfrogTrajectory standardQuadraticGradient ε
            (0 : Fin (L + 1)) (standardQuadraticUnitPhase q 1))
          (⟨1, by omega⟩ : Fin (L + 1))).toReal) =
        standardQuadraticForwardAtom ε L ⟨1, by omega⟩ := by
      funext q
      exact toReal_standardQuadratic_forwardTrajectoryIndexPMF ε L _ q
    rw [hfun]
    exact hone

/-- For every finite forward Gaussian trajectory containing one leapfrog
step, its actual categorical law separates linearly in total variation under
an infinitesimal displacement of the initial position. -/
theorem exists_standardQuadratic_forwardTrajectory_linearTotalVariation
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {L : ℕ} (hL : 0 < L) :
    ∃ linearRate : ℝ, 0 < linearRate ∧
      ∀ᶠ q in nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ,
        linearRate * |q| <
          (Mcmc.Finite.totalVariation
            (trajectoryIndexPMF standardQuadraticPotential
              (offsetLeapfrogTrajectory standardQuadraticGradient ε
                (0 : Fin (L + 1)) (standardQuadraticUnitPhase 0 1)))
            (trajectoryIndexPMF standardQuadraticPotential
              (offsetLeapfrogTrajectory standardQuadraticGradient ε
                (0 : Fin (L + 1))
                (standardQuadraticUnitPhase q 1)))).toReal := by
  obtain ⟨i, hi⟩ :=
    exists_standardQuadratic_forwardTrajectoryIndexPMF_deriv_ne_zero
      hε0 hε1 hL
  let f : ℝ → ℝ := fun q =>
    (trajectoryIndexPMF standardQuadraticPotential
      (offsetLeapfrogTrajectory standardQuadraticGradient ε
        (0 : Fin (L + 1)) (standardQuadraticUnitPhase q 1)) i).toReal
  have hfEq : f = standardQuadraticForwardAtom ε L i := by
    funext q
    exact toReal_standardQuadratic_forwardTrajectoryIndexPMF ε L i q
  have hfDiff : Differentiable ℝ f := by
    rw [hfEq]
    exact differentiable_standardQuadraticForwardAtom ε L i
  have hfDeriv : deriv f 0 ≠ 0 := by
    exact hi
  let linearRate := |deriv f 0| / 2
  refine ⟨linearRate, ?_, ?_⟩
  · exact div_pos (abs_pos.mpr hfDeriv) (by norm_num)
  have ht : Filter.Tendsto (slope f 0)
      (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ) (nhds (deriv f 0)) := by
    exact hfDiff.differentiableAt.hasDerivAt.tendsto_slope
  have habs : Filter.Tendsto (fun q => |slope f 0 q|)
      (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ) (nhds |deriv f 0|) :=
    (continuous_abs.tendsto _).comp ht
  have hslope : ∀ᶠ q in nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ,
      linearRate < |slope f 0 q| := by
    apply (tendsto_order.1 habs).1
    exact div_lt_self (abs_pos.mpr hfDeriv) (by norm_num)
  filter_upwards [hslope, self_mem_nhdsWithin] with q hqSlope hq
  have hq0 : q ≠ 0 := by simpa using hq
  have hslopeEq : slope f 0 q = (f q - f 0) / q := by
    rw [slope_def_field]
    simp
  have hdiff : |slope f 0 q| * |q| = |f q - f 0| := by
    rw [hslopeEq, abs_div]
    exact div_mul_cancel₀ _ (abs_ne_zero.mpr hq0)
  let p₀ := trajectoryIndexPMF standardQuadraticPotential
    (offsetLeapfrogTrajectory standardQuadraticGradient ε
      (0 : Fin (L + 1)) (standardQuadraticUnitPhase 0 1))
  let pq := trajectoryIndexPMF standardQuadraticPotential
    (offsetLeapfrogTrajectory standardQuadraticGradient ε
      (0 : Fin (L + 1)) (standardQuadraticUnitPhase q 1))
  calc
    linearRate * |q| < |slope f 0 q| * |q| :=
      mul_lt_mul_of_pos_right hqSlope (abs_pos.mpr hq0)
    _ = |f q - f 0| := hdiff
    _ = |(p₀ i).toReal - (pq i).toReal| := by
      change |(pq i).toReal - (p₀ i).toReal| = _
      rw [abs_sub_comm]
    _ ≤ (Mcmc.Finite.totalVariation p₀ pq).toReal :=
      Mcmc.Finite.abs_toReal_sub_toReal_le_totalVariation_toReal p₀ pq i

/-- Each scalar Gaussian cross-trajectory squared cost varies continuously
with the second initial position. -/
theorem continuous_standardQuadratic_trajectorySquaredPositionCost
    (ε : ℝ) {L : ℕ} (i j : Fin (L + 1)) :
    Continuous (fun q : ℝ =>
      ((trajectorySquaredPositionCost standardQuadraticGradient ε
        ((standardQuadraticUnitPhase 0 1,
          standardQuadraticUnitPhase q 1)) (0 : Fin (L + 1)) i j : NNReal) :
        ℝ)) := by
  change Continuous (fun q : ℝ => squaredEuclideanNorm
    ((offsetLeapfrogTrajectory standardQuadraticGradient ε
        (0 : Fin (L + 1)) (standardQuadraticUnitPhase 0 1) i).1 -
      (offsetLeapfrogTrajectory standardQuadraticGradient ε
        (0 : Fin (L + 1)) (standardQuadraticUnitPhase q 1) j).1))
  simp_rw [offsetLeapfrogTrajectory_zero_eq_leapfrogN]
  have hj :=
    (differentiable_standardQuadratic_leapfrogN_unitPhase ε j.val).continuous
  have hjpos : Continuous (fun q =>
      (leapfrogN standardQuadraticGradient ε j.val
        (standardQuadraticUnitPhase q 1)).1) := hj.fst
  unfold squaredEuclideanNorm euclideanInner
  fun_prop (disch := assumption)

/-- The positive off-diagonal floor at the coincident trajectory persists on
a neighborhood of the diagonal, uniformly over the finite cost table. -/
theorem exists_eventually_standardQuadratic_trajectoryCostFloor_before_one
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {L : ℕ} (hLpos : 0 < L)
    (hL : (L : ℝ) * ε ≤ 1) :
    ∃ floor : NNReal, 0 < floor ∧
      ∀ᶠ q in nhds (0 : ℝ), ∀ i j : Fin (L + 1), i ≠ j →
        floor ≤ trajectorySquaredPositionCost standardQuadraticGradient ε
          ((standardQuadraticUnitPhase 0 1,
            standardQuadraticUnitPhase q 1)) (0 : Fin (L + 1)) i j := by
  obtain ⟨baseFloor, hbaseFloor, hbase⟩ :=
    exists_standardQuadratic_pos_trajectoryCostFloor_before_one
      hε0 hε1 hLpos hL
  let floor : NNReal := baseFloor / 2
  have hfloor : 0 < floor := by
    exact div_pos hbaseFloor (by norm_num)
  refine ⟨floor, hfloor, ?_⟩
  rw [Filter.eventually_all]
  intro i
  rw [Filter.eventually_all]
  intro j
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall (fun q hne => False.elim (hne hij))
  · let cost : ℝ → ℝ := fun q =>
      ((trajectorySquaredPositionCost standardQuadraticGradient ε
        ((standardQuadraticUnitPhase 0 1,
          standardQuadraticUnitPhase q 1)) (0 : Fin (L + 1)) i j : NNReal) : ℝ)
    have hcont : Continuous cost :=
      continuous_standardQuadratic_trajectorySquaredPositionCost ε i j
    have hstrict : (floor : ℝ) < cost 0 := by
      have hhalf : (floor : ℝ) < (baseFloor : ℝ) := by
        dsimp only [floor]
        exact div_lt_self (by exact_mod_cast hbaseFloor) (by norm_num)
      exact hhalf.trans_le (by exact_mod_cast hbase i j hij)
    have hevent : ∀ᶠ q in nhds (0 : ℝ), (floor : ℝ) < cost q :=
      (tendsto_order.1 hcont.continuousAt).1 (floor : ℝ) hstrict
    filter_upwards [hevent] with q hq hne
    exact NNReal.coe_le_coe.mp hq.le

/-- On every fixed positive-step trajectory grid lying before physical time
one, optimal squared transport between nearby Gaussian multinomial laws
eventually exceeds every prescribed quadratic rate.  This is the complete
positive-window version of the earlier two-index obstruction. -/
theorem eventually_rate_mul_sq_lt_standardQuadratic_forwardOptimalTransportCost
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {L : ℕ} (hLpos : 0 < L)
    (hL : (L : ℝ) * ε ≤ 1) (rate : ℝ) :
    ∀ᶠ q in nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ,
      rate * q ^ 2 <
        (Mcmc.Finite.transportCost
          (trajectorySquaredPositionCost standardQuadraticGradient ε
            ((standardQuadraticUnitPhase 0 1,
              standardQuadraticUnitPhase q 1)) (0 : Fin (L + 1)))
          (Mcmc.Finite.optimalTransportCoupling
            (trajectoryIndexPMF standardQuadraticPotential
              (offsetLeapfrogTrajectory standardQuadraticGradient ε
                (0 : Fin (L + 1)) (standardQuadraticUnitPhase 0 1)))
            (trajectoryIndexPMF standardQuadraticPotential
              (offsetLeapfrogTrajectory standardQuadraticGradient ε
                (0 : Fin (L + 1))
                (standardQuadraticUnitPhase q 1)))
            (trajectorySquaredPositionCost standardQuadraticGradient ε
              ((standardQuadraticUnitPhase 0 1,
                standardQuadraticUnitPhase q 1))
              (0 : Fin (L + 1))))).toReal := by
  let left : ℝ → PMF (Fin (L + 1)) := fun _ =>
    trajectoryIndexPMF standardQuadraticPotential
      (offsetLeapfrogTrajectory standardQuadraticGradient ε
        (0 : Fin (L + 1)) (standardQuadraticUnitPhase 0 1))
  let right : ℝ → PMF (Fin (L + 1)) := fun q =>
    trajectoryIndexPMF standardQuadraticPotential
      (offsetLeapfrogTrajectory standardQuadraticGradient ε
        (0 : Fin (L + 1)) (standardQuadraticUnitPhase q 1))
  let cost : ℝ → Fin (L + 1) → Fin (L + 1) → NNReal := fun q =>
    trajectorySquaredPositionCost standardQuadraticGradient ε
      ((standardQuadraticUnitPhase 0 1,
        standardQuadraticUnitPhase q 1)) (0 : Fin (L + 1))
  obtain ⟨linearRate, hlinearRate, hTV⟩ :=
    exists_standardQuadratic_forwardTrajectory_linearTotalVariation
      hε0 hε1 hLpos
  obtain ⟨mismatchLower, hmismatchLower, hcostNhds⟩ :=
    exists_eventually_standardQuadratic_trajectoryCostFloor_before_one
      hε0 hε1 hLpos hL
  have hcost : ∀ᶠ q in nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ,
      ∀ i j, i ≠ j → mismatchLower ≤ cost q i j := by
    exact hcostNhds.filter_mono inf_le_left
  exact Mcmc.Finite.eventually_rate_mul_sq_lt_optimalTransportCost_toReal
    left right cost linearRate mismatchLower rate hlinearRate hmismatchLower
    (by simpa only [left, right] using hTV)
    (by simpa only [cost] using hcost)

/-- No fixed scalar Gaussian trajectory grid in the controlled horizon admits
an exponent-two transport-family bound uniformly over all nearby initial
positions.  This is stated directly in the cost language of Condition 1. -/
theorem not_forall_transportTrajectoryIndexCouplingFamily_moment_two_le
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {L : ℕ} (hLpos : 0 < L)
    (hL : (L : ℝ) * ε ≤ 1) (rate : NNReal) :
    ¬ ∀ q : ℝ,
      Mcmc.Finite.transportCost
          (trajectoryPositionMomentCost standardQuadraticGradient 2 ε
            ((standardQuadraticUnitPhase 0 1,
              standardQuadraticUnitPhase q 1)) (0 : Fin (L + 1)))
          (transportTrajectoryIndexCouplingFamily
            standardQuadraticPotential standardQuadraticGradient ε L
            ((standardQuadraticUnitPhase 0 1,
              standardQuadraticUnitPhase q 1)) (0 : Fin (L + 1))) ≤
        (rate : ENNReal) * ENNReal.ofReal
          (euclideanNorm
            ((standardQuadraticUnitPhase 0 1).1 -
              (standardQuadraticUnitPhase q 1).1) ^ 2) := by
  intro hbound
  have hevent :=
    eventually_rate_mul_sq_lt_standardQuadratic_forwardOptimalTransportCost
      hε0 hε1 hLpos hL (rate : ℝ)
  obtain ⟨q, hq⟩ := hevent.exists
  have hupper := hbound q
  rw [transportCost_trajectoryPositionMomentCost_two] at hupper
  change Mcmc.Finite.transportCost
      (trajectorySquaredPositionCost standardQuadraticGradient ε
        ((standardQuadraticUnitPhase 0 1,
          standardQuadraticUnitPhase q 1)) (0 : Fin (L + 1)))
      (Mcmc.Finite.optimalTransportCoupling
        (trajectoryIndexPMF standardQuadraticPotential
          (offsetLeapfrogTrajectory standardQuadraticGradient ε
            (0 : Fin (L + 1)) (standardQuadraticUnitPhase 0 1)))
        (trajectoryIndexPMF standardQuadraticPotential
          (offsetLeapfrogTrajectory standardQuadraticGradient ε
            (0 : Fin (L + 1)) (standardQuadraticUnitPhase q 1)))
        (trajectorySquaredPositionCost standardQuadraticGradient ε
          ((standardQuadraticUnitPhase 0 1,
            standardQuadraticUnitPhase q 1)) (0 : Fin (L + 1)))) ≤ _ at hupper
  have hrightTop : (rate : ENNReal) * ENNReal.ofReal
      (euclideanNorm
        ((standardQuadraticUnitPhase 0 1).1 -
          (standardQuadraticUnitPhase q 1).1) ^ 2) ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  have hupperReal := ENNReal.toReal_mono hrightTop hupper
  have hnorm : euclideanNorm
      ((standardQuadraticUnitPhase 0 1).1 -
        (standardQuadraticUnitPhase q 1).1) ^ 2 = q ^ 2 := by
    rw [euclideanNorm_sq]
    simp [squaredEuclideanNorm, euclideanInner,
      standardQuadraticUnitPhase]
    ring
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _), hnorm] at hupperReal
  simp only [ENNReal.coe_toReal] at hupperReal
  exact (not_lt_of_ge hupperReal) hq

/-- The fixed-grid obstruction propagates through all outer numerical
quantifiers of the repaired exponent-two Condition 1 on every positive
integration window whose lower endpoint is at most one.  Taking
`ε = Tmin / n` and `L = n` meets the window exactly while making `ε`
arbitrarily small. -/
theorem not_xuCondition1AtExponentOnIntegrationWindow_transport_two
    (rate : NNReal) {Tmin Tmax : ℝ} (hTminLeOne : Tmin ≤ 1) :
    ¬ XuCondition1AtExponentOnIntegrationWindow
      (transportTrajectoryIndexCouplingFamily
        standardQuadraticPotential standardQuadraticGradient)
      standardQuadraticGradient (Set.univ : Set (Position Unit))
      2 rate Tmin Tmax := by
  intro hcondition
  rcases hcondition with ⟨hm, hTmin0, hwindow, hquant⟩
  rcases hquant 1 zero_lt_one with ⟨εbar, hεbar, hbound⟩
  let δ : ℝ := min εbar 1
  have hδ : 0 < δ := lt_min hεbar zero_lt_one
  obtain ⟨n, hn⟩ := exists_nat_gt (Tmin / δ)
  have hratio0 : 0 < Tmin / δ := div_pos hTmin0 hδ
  have hnReal0 : 0 < (n : ℝ) := hratio0.trans hn
  have hn0 : 0 < n := by exact_mod_cast hnReal0
  let ε : ℝ := Tmin / (n : ℝ)
  have hε0 : 0 < ε := div_pos hTmin0 hnReal0
  have hTmin_lt_nδ : Tmin < (n : ℝ) * δ := by
    have := (div_lt_iff₀ hδ).mp hn
    nlinarith
  have hεltδ : ε < δ := by
    rw [div_lt_iff₀ hnReal0]
    nlinarith
  have hεlt : ε < εbar := hεltδ.trans_le (min_le_left _ _)
  have hε1 : ε ≤ 1 :=
    (hεltδ.trans_le (min_le_right _ _)).le
  have htime : ε * (n : ℝ) = Tmin := by
    dsimp only [ε]
    field_simp
  have hhorizon : (n : ℝ) * ε ≤ 1 := by
    rw [mul_comm, htime]
    exact hTminLeOne
  have hkinetic : kineticEnergy (standardQuadraticUnitPhase 0 1).2 ≤ 1 := by
    simp [kineticEnergy, standardQuadraticUnitPhase]
    norm_num
  have hall : ∀ q : ℝ,
      Mcmc.Finite.transportCost
          (trajectoryPositionMomentCost standardQuadraticGradient 2 ε
            ((standardQuadraticUnitPhase 0 1,
              standardQuadraticUnitPhase q 1)) (0 : Fin (n + 1)))
          (transportTrajectoryIndexCouplingFamily
            standardQuadraticPotential standardQuadraticGradient ε n
            ((standardQuadraticUnitPhase 0 1,
              standardQuadraticUnitPhase q 1)) (0 : Fin (n + 1))) ≤
        (rate : ENNReal) * ENNReal.ofReal
          (euclideanNorm
            ((standardQuadraticUnitPhase 0 1).1 -
              (standardQuadraticUnitPhase q 1).1) ^ 2) := by
    intro q
    have hq := hbound ε hε0 hεlt n
      (by rw [htime]) (by rw [htime]; exact hwindow)
      (0 : Fin (n + 1))
      (standardQuadraticUnitPhase 0 1).1 (Set.mem_univ _)
      (standardQuadraticUnitPhase q 1).1 (Set.mem_univ _)
      (standardQuadraticUnitPhase 0 1).2 hkinetic
    simpa [standardQuadraticUnitPhase] using hq
  exact (not_forall_transportTrajectoryIndexCouplingFamily_moment_two_le
    hε0 hε1 hn0 hhorizon rate) hall

/-- Consequently the sharp overlap-weighted exponent-two budget cannot be
instantiated by the scalar standard Gaussian on a controlled positive window.
Its abstract implication theorem remains valid; this theorem records that its
hypothesis is false in this specialization. -/
theorem not_standardQuadratic_xuSharpRelativeMomentTwoBudgetOnIntegrationWindow
    {Tmin Tmax : ℝ} (hTminLeOne : Tmin ≤ 1)
    (alignedRate mismatchRate : NNReal) :
    ¬ XuSharpRelativeMomentTwoBudgetOnIntegrationWindow
      standardQuadraticPotential standardQuadraticGradient
      (Set.univ : Set (Position Unit)) Tmin Tmax alignedRate mismatchRate := by
  intro hbudget
  exact not_xuCondition1AtExponentOnIntegrationWindow_transport_two
    (alignedRate + mismatchRate) hTminLeOne
    (hbudget.transportCondition standardQuadraticPotential
      standardQuadraticGradient Set.univ Tmin Tmax)

/-- The older per-index exponent-two budget is likewise impossible for this
Gaussian specialization on the same controlled windows. -/
theorem not_standardQuadratic_xuRelativeMomentTwoBudgetOnIntegrationWindow
    {Tmin Tmax : ℝ} (hTminLeOne : Tmin ≤ 1)
    (alignedRate mismatchRate : NNReal) :
    ¬ XuRelativeMomentTwoBudgetOnIntegrationWindow
      standardQuadraticPotential standardQuadraticGradient
      (Set.univ : Set (Position Unit)) Tmin Tmax alignedRate mismatchRate := by
  intro hbudget
  exact not_xuCondition1AtExponentOnIntegrationWindow_transport_two
    (alignedRate + mismatchRate) hTminLeOne
    (hbudget.transportCondition standardQuadraticPotential
      standardQuadraticGradient Set.univ Tmin Tmax)

omit [Fintype ι] in
/-- Exact aligned multi-step relative-state formula for two standard-
quadratic leapfrog trajectories started with shared momentum. -/
theorem standardQuadratic_leapfrogN_sharedMomentum_sub
    (ε : ℝ) (n : ℕ) (q₁ q₂ : Position ι) (p : Momentum ι) :
    (leapfrogN standardQuadraticGradient ε n (q₁, p)).1 -
        (leapfrogN standardQuadraticGradient ε n (q₂, p)).1 =
      (standardQuadraticDifferenceCoefficients ε n).1 • (q₁ - q₂) ∧
    (leapfrogN standardQuadraticGradient ε n (q₁, p)).2 -
        (leapfrogN standardQuadraticGradient ε n (q₂, p)).2 =
      (standardQuadraticDifferenceCoefficients ε n).2 • (q₁ - q₂) := by
  induction n with
  | zero =>
      constructor <;> ext i <;>
        simp [standardQuadraticDifferenceCoefficients]
  | succ n ih =>
      simp only [leapfrogN_succ,
        standardQuadraticDifferenceCoefficients_succ]
      rcases ih with ⟨ihq, ihp⟩
      constructor
      · ext i
        change
          (leapfrog standardQuadraticGradient ε
              (leapfrogN standardQuadraticGradient ε n (q₁, p))).1 i -
            (leapfrog standardQuadraticGradient ε
              (leapfrogN standardQuadraticGradient ε n (q₂, p))).1 i = _
        rw [leapfrog_standardQuadratic_fst_apply,
          leapfrog_standardQuadratic_fst_apply]
        have hiq := congrFun ihq i
        have hip := congrFun ihp i
        dsimp [standardQuadraticDifferenceStep]
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hiq hip ⊢
        linear_combination (1 - ε ^ 2 / 2) * hiq + ε * hip
      · ext i
        change
          (leapfrog standardQuadraticGradient ε
              (leapfrogN standardQuadraticGradient ε n (q₁, p))).2 i -
            (leapfrog standardQuadraticGradient ε
              (leapfrogN standardQuadraticGradient ε n (q₂, p))).2 i = _
        rw [leapfrog_standardQuadratic_snd_apply,
          leapfrog_standardQuadratic_snd_apply]
        have hiq := congrFun ihq i
        have hip := congrFun ihp i
        dsimp [standardQuadraticDifferenceStep]
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hiq hip ⊢
        linear_combination
          (-ε + ε ^ 3 / 4) * hiq + (1 - ε ^ 2 / 2) * hip

/-- Shared-momentum standard-quadratic trajectories have phase separation
bounded by the same fixed-horizon stability factor as a single trajectory.
Their initial phase separation is purely positional. -/
theorem standardQuadratic_leapfrogN_sharedMomentum_phaseSeparation_le_exp
    {ε : ℝ} (hε : |ε| ≤ 1) (n : ℕ) {T : ℝ}
    (horizon : (n : ℝ) * |ε| ≤ T)
    (q₁ q₂ : Position ι) (p : Momentum ι) :
    euclideanNorm
          ((leapfrogN standardQuadraticGradient ε n (q₁, p)).1 -
            (leapfrogN standardQuadraticGradient ε n (q₂, p)).1) +
        euclideanNorm
          ((leapfrogN standardQuadraticGradient ε n (q₁, p)).2 -
            (leapfrogN standardQuadraticGradient ε n (q₂, p)).2) ≤
      Real.exp ((13 / 4 : ℝ) * T) * euclideanNorm (q₁ - q₂) := by
  let d : PhaseSpace ι := (q₁ - q₂, 0)
  have hpair :
      ((leapfrogN standardQuadraticGradient ε n (q₁, p)).1 -
          (leapfrogN standardQuadraticGradient ε n (q₂, p)).1,
        (leapfrogN standardQuadraticGradient ε n (q₁, p)).2 -
          (leapfrogN standardQuadraticGradient ε n (q₂, p)).2) =
        leapfrogN standardQuadraticGradient ε n d := by
    rcases standardQuadratic_leapfrogN_sharedMomentum_sub
      ε n q₁ q₂ p with ⟨hq, hp⟩
    rcases standardQuadratic_leapfrogN_sharedMomentum_sub
      ε n (q₁ - q₂) 0 0 with ⟨hdq, hdp⟩
    have hzero_all : ∀ m : ℕ,
        leapfrogN standardQuadraticGradient ε m ((0, 0) : PhaseSpace ι) =
          ((0, 0) : PhaseSpace ι) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          rw [leapfrogN_succ, ih]
          apply Prod.ext <;> ext i
          · rw [leapfrog_standardQuadratic_fst_apply]
            simp
          · rw [leapfrog_standardQuadratic_snd_apply]
            simp
    have hzero := hzero_all n
    have hdq' :
        (leapfrogN standardQuadraticGradient ε n (q₁ - q₂, 0)).1 =
          (standardQuadraticDifferenceCoefficients ε n).1 • (q₁ - q₂) := by
      rw [hzero] at hdq
      simpa using hdq
    have hdp' :
        (leapfrogN standardQuadraticGradient ε n (q₁ - q₂, 0)).2 =
          (standardQuadraticDifferenceCoefficients ε n).2 • (q₁ - q₂) := by
      rw [hzero] at hdp
      simpa using hdp
    apply Prod.ext
    · dsimp [d]
      exact hq.trans hdq'.symm
    · dsimp [d]
      exact hp.trans hdp'.symm
  have hsize := standardQuadratic_leapfrogN_euclideanPhaseSize_le_exp
    hε n horizon d
  rw [← hpair] at hsize
  dsimp [euclideanPhaseSize, d] at hsize ⊢
  simpa using hsize

/-- Aligned Gaussian squared position distance is exactly the square of the
scalar position coefficient times the initial squared distance. -/
theorem standardQuadratic_leapfrogN_sharedMomentum_squaredDistance_eq
    (ε : ℝ) (n : ℕ) (q₁ q₂ : Position ι) (p : Momentum ι) :
    squaredEuclideanNorm
        ((leapfrogN standardQuadraticGradient ε n (q₁, p)).1 -
          (leapfrogN standardQuadraticGradient ε n (q₂, p)).1) =
      (standardQuadraticDifferenceCoefficients ε n).1 ^ 2 *
        squaredEuclideanNorm (q₁ - q₂) := by
  rw [(standardQuadratic_leapfrogN_sharedMomentum_sub
    ε n q₁ q₂ p).1, squaredEuclideanNorm_smul]

/-- Any aligned step whose scalar position coefficient has modulus below one
strictly contracts distinct shared-momentum Gaussian positions. -/
theorem standardQuadratic_leapfrogN_sharedMomentum_squaredDistance_lt
    (ε : ℝ) (n : ℕ) {q₁ q₂ : Position ι} (hne : q₁ ≠ q₂)
    (p : Momentum ι)
    (hcoeff : |(standardQuadraticDifferenceCoefficients ε n).1| < 1) :
    squaredEuclideanNorm
        ((leapfrogN standardQuadraticGradient ε n (q₁, p)).1 -
          (leapfrogN standardQuadraticGradient ε n (q₂, p)).1) <
      squaredEuclideanNorm (q₁ - q₂) := by
  rw [standardQuadratic_leapfrogN_sharedMomentum_squaredDistance_eq]
  have hcoeffSq :
      (standardQuadraticDifferenceCoefficients ε n).1 ^ 2 < 1 := by
    have hsquare := (sq_lt_sq₀
      (abs_nonneg (standardQuadraticDifferenceCoefficients ε n).1)
      zero_le_one).mpr hcoeff
    simpa only [sq_abs, one_pow] using hsquare
  have hdist : 0 < squaredEuclideanNorm (q₁ - q₂) :=
    squaredEuclideanNorm_pos (sub_ne_zero.mpr hne)
  nlinarith

/-- Position coefficient for a signed Gaussian leapfrog offset. Negative
offsets use the inverse step, equivalently leapfrog with step size `-ε`. -/
noncomputable def standardQuadraticSignedPositionCoefficient
    (ε : ℝ) : ℤ → ℝ
  | .ofNat n => (standardQuadraticDifferenceCoefficients ε n).1
  | .negSucc n =>
      (standardQuadraticDifferenceCoefficients (-ε) (n + 1)).1

/-- Absolute signed Gaussian position coefficients have the same cosine form
for forward and backward offsets. -/
theorem abs_standardQuadraticSignedPositionCoefficient_eq_cos
    {ε : ℝ} (hε : |ε| ≤ 2) (k : ℤ) :
    |standardQuadraticSignedPositionCoefficient ε k| =
      |Real.cos ((Int.natAbs k : ℝ) *
        Real.arccos (1 - ε ^ 2 / 2))| := by
  cases k with
  | ofNat n =>
      rw [standardQuadraticSignedPositionCoefficient,
        standardQuadraticDifferenceCoefficients_fst_eq_cos hε]
      simp
  | negSucc n =>
      have hneg : |-ε| ≤ 2 := by simpa only [abs_neg] using hε
      rw [standardQuadraticSignedPositionCoefficient,
        standardQuadraticDifferenceCoefficients_fst_eq_cos hneg]
      simp only [Int.natAbs_negSucc, Nat.cast_add, Nat.cast_one, neg_sq]
      rw [Nat.cast_succ]

/-- Every signed offset whose physical time lies in `[τ,1]` has coefficient
at most `cos τ`.  The upper endpoint keeps the modified angle in
`[0,π/2]`, where cosine is nonnegative and decreasing. -/
theorem abs_standardQuadraticSignedPositionCoefficient_le_cos
    {ε τ : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hτ0 : 0 ≤ τ) (k : ℤ)
    (hlow : τ ≤ (Int.natAbs k : ℝ) * ε)
    (hhigh : (Int.natAbs k : ℝ) * ε ≤ 1) :
    |standardQuadraticSignedPositionCoefficient ε k| ≤ Real.cos τ := by
  have hε2 : ε ≤ 2 := hε1.trans (by norm_num)
  let θ := Real.arccos (1 - ε ^ 2 / 2)
  have hθ0 : 0 ≤ θ := Real.arccos_nonneg _
  have hθlower : ε ≤ θ := le_standardQuadraticModifiedAngle hε0 hε2
  have hθupper : θ ≤ (Real.pi / 2) * ε :=
    standardQuadraticModifiedAngle_le hε0 hε2
  let x := (Int.natAbs k : ℝ) * θ
  have hk0 : 0 ≤ (Int.natAbs k : ℝ) := by positivity
  have hx0 : 0 ≤ x := mul_nonneg hk0 hθ0
  have hτx : τ ≤ x := by
    apply hlow.trans
    exact mul_le_mul_of_nonneg_left hθlower hk0
  have hxhalf : x ≤ Real.pi / 2 := by
    calc
      x ≤ (Int.natAbs k : ℝ) * ((Real.pi / 2) * ε) :=
        mul_le_mul_of_nonneg_left hθupper hk0
      _ = (Real.pi / 2) * ((Int.natAbs k : ℝ) * ε) := by ring
      _ ≤ Real.pi / 2 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hhigh
          (show 0 ≤ Real.pi / 2 by positivity)
  rw [abs_standardQuadraticSignedPositionCoefficient_eq_cos
    (by rw [abs_of_nonneg hε0]; linarith)]
  change |Real.cos x| ≤ Real.cos τ
  rw [abs_of_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith, hxhalf⟩)]
  exact Real.cos_le_cos_of_nonneg_of_le_pi hτ0
    (hxhalf.trans (by linarith [Real.pi_pos])) hτx

/-- The band coefficient `cos τ` is strictly subunit for positive
`τ ≤ π`. -/
theorem cos_lt_one_of_pos_of_le_pi {τ : ℝ} (hτ0 : 0 < τ)
    (hτπ : τ ≤ Real.pi) : Real.cos τ < 1 := by
  simpa using Real.strictAntiOn_cos
    (show (0 : ℝ) ∈ Set.Icc 0 Real.pi by simp [Real.pi_pos.le])
    (show τ ∈ Set.Icc 0 Real.pi from ⟨hτ0.le, hτπ⟩) hτ0

/-- An endpoint-band index chosen on the longer side of an arbitrary
trajectory split. The parameter `j` ranges over `L/4 + 1` indices. -/
def standardQuadraticInteriorBandIndex
    (L : ℕ) (origin : Fin (L + 1)) (j : Fin (L / 4 + 1)) : Fin (L + 1) :=
  if origin.val ≤ L / 2 then
    ⟨L - j.val, by omega⟩
  else
    ⟨j.val, by omega⟩

/-- The endpoint-band parametrization is injective. -/
theorem standardQuadraticInteriorBandIndex_injective
    (L : ℕ) (origin : Fin (L + 1)) :
    Function.Injective (standardQuadraticInteriorBandIndex L origin) := by
  intro i j hij
  unfold standardQuadraticInteriorBandIndex at hij
  split at hij
  · apply Fin.ext
    simp only [Fin.mk.injEq] at hij ⊢
    omega
  · exact Fin.ext (Fin.mk.inj_iff.mp hij)

/-- A canonical band containing the far endpoint of the longer side of the
offset trajectory. -/
def standardQuadraticInteriorIndexBand
    (L : ℕ) (origin : Fin (L + 1)) : Finset (Fin (L + 1)) :=
  Finset.univ.image (standardQuadraticInteriorBandIndex L origin)

/-- The canonical interior band contains exactly `L/4 + 1` indices. -/
theorem card_standardQuadraticInteriorIndexBand
    (L : ℕ) (origin : Fin (L + 1)) :
    (standardQuadraticInteriorIndexBand L origin).card = L / 4 + 1 := by
  unfold standardQuadraticInteriorIndexBand
  rw [Finset.card_image_of_injective _
    (standardQuadraticInteriorBandIndex_injective L origin)]
  simp

/-- Every canonical band index is at least one-quarter of the total trajectory
length away from the current-state origin, and never more than `L` away. -/
theorem standardQuadraticInteriorIndexBand_offset_bounds
    {L : ℕ} (origin : Fin (L + 1))
    {i : Fin (L + 1)} (hi : i ∈ standardQuadraticInteriorIndexBand L origin) :
    L ≤ 4 * Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) ∧
      Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) ≤ L := by
  rw [standardQuadraticInteriorIndexBand, Finset.mem_image] at hi
  rcases hi with ⟨j, hj, rfl⟩
  unfold standardQuadraticInteriorBandIndex
  split <;> rename_i h
  · change L ≤ 4 * Int.natAbs
        (((L - j.val : ℕ) : ℤ) - (origin.val : ℤ)) ∧
      Int.natAbs (((L - j.val : ℕ) : ℤ) - (origin.val : ℤ)) ≤ L
    rw [Int.natAbs_natCast_sub_natCast_of_ge (by omega)]
    omega
  · change L ≤ 4 * Int.natAbs
        ((j.val : ℤ) - (origin.val : ℤ)) ∧
      Int.natAbs ((j.val : ℤ) - (origin.val : ℤ)) ≤ L
    rw [Int.natAbs_natCast_sub_natCast_of_le (by omega)]
    omega

/-- The canonical band occupies at least one quarter of all trajectory
indices. -/
theorem quarter_card_le_standardQuadraticInteriorIndexBand
    (L : ℕ) (origin : Fin (L + 1)) :
    L + 1 ≤ 4 * (standardQuadraticInteriorIndexBand L origin).card := by
  rw [card_standardQuadraticInteriorIndexBand]
  omega

/-- Quarter-cardinality cancels the varying trajectory length in a uniform
atom floor. This elementary estimate is stated over `NNReal` so all later
quantities embed into `ENNReal` without top-value side conditions. -/
theorem quarterInverse_le_bandCard_mul_inverse
    (L : ℕ) (origin : Fin (L + 1)) (c : NNReal) (hc : 0 < c) :
    ((4 : NNReal) * c)⁻¹ ≤
      (standardQuadraticInteriorIndexBand L origin).card *
        (((L + 1 : ℕ) : NNReal) * c)⁻¹ := by
  apply NNReal.coe_le_coe.mp
  push_cast
  have hcard := quarter_card_le_standardQuadraticInteriorIndexBand L origin
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  have hnR : 0 < ((L + 1 : ℕ) : ℝ) := by positivity
  field_simp
  exact_mod_cast hcard

/-- Centered energies on two Gaussian trajectories give the canonical
quarter-band an overlap mass floor independent of `L` and the trajectory
origin. -/
theorem standardQuadraticInteriorIndexBand_overlapMass_ge
    (potential : Position ι → ℝ) {L : ℕ}
    (trajectory₁ trajectory₂ : Fin (L + 1) → PhaseSpace ι)
    (center₁ center₂ δ : ℝ)
    (henergy₁ : ∀ i, |energy potential (trajectory₁ i) - center₁| ≤ δ)
    (henergy₂ : ∀ i, |energy potential (trajectory₂ i) - center₂| ≤ δ)
    (origin : Fin (L + 1)) :
    ENNReal.ofReal ((4 * Real.exp (2 * δ))⁻¹) ≤
      ∑ i ∈ standardQuadraticInteriorIndexBand L origin,
        min (trajectoryIndexPMF potential trajectory₁ i)
          (trajectoryIndexPMF potential trajectory₂ i) := by
  have hband := trajectoryIndexPMF_overlap_bandMass_ge_of_centered_energy
    potential trajectory₁ trajectory₂ center₁ center₂ δ
      henergy₁ henergy₂ (standardQuadraticInteriorIndexBand L origin)
  apply le_trans ?_ hband
  rw [← ENNReal.ofReal_natCast
      (standardQuadraticInteriorIndexBand L origin).card,
    ← ENNReal.ofReal_natCast (L + 1),
    ← ENNReal.ofReal_mul (Nat.cast_nonneg (L + 1)),
    ← ENNReal.ofReal_inv_of_pos
      (x := (((L + 1 : ℕ) : ℝ) * Real.exp (2 * δ)))
      (mul_pos (by positivity) (Real.exp_pos _)),
    ← ENNReal.ofReal_mul
      (Nat.cast_nonneg (standardQuadraticInteriorIndexBand L origin).card)]
  apply ENNReal.ofReal_le_ofReal
  have hcard := quarter_card_le_standardQuadraticInteriorIndexBand L origin
  have hexp : 0 < Real.exp (2 * δ) := Real.exp_pos _
  field_simp
  exact_mod_cast hcard

/-- Under a total physical horizon in `[Tmin,1]`, every canonical band index
has offset time in `[Tmin/4,1]`. -/
theorem standardQuadraticInteriorIndexBand_physicalTime_bounds
    {L : ℕ} (origin : Fin (L + 1)) {i : Fin (L + 1)}
    (hi : i ∈ standardQuadraticInteriorIndexBand L origin)
    {ε Tmin : ℝ} (hε0 : 0 ≤ ε)
    (hTmin : Tmin ≤ ε * (L : ℝ))
    (hTmax : ε * (L : ℝ) ≤ 1) :
    Tmin / 4 ≤
        (Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) : ℝ) * ε ∧
      (Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) : ℝ) * ε ≤ 1 := by
  rcases standardQuadraticInteriorIndexBand_offset_bounds origin hi with
    ⟨hlow, hhigh⟩
  have hlowR : (L : ℝ) ≤
      4 * (Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) : ℝ) := by
    exact_mod_cast hlow
  have hhighR :
      (Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) : ℝ) ≤ L := by
    exact_mod_cast hhigh
  constructor
  · have := mul_le_mul_of_nonneg_right hlowR hε0
    nlinarith
  · exact (mul_le_mul_of_nonneg_right hhighR hε0).trans
      (by simpa only [mul_comm] using hTmax)

/-- Hence every canonical band index has a common strictly contractive
Gaussian coefficient `cos(Tmin/4)` whenever `0<Tmin` and the total horizon is
at most one. -/
theorem standardQuadraticInteriorIndexBand_coefficient_le
    {L : ℕ} (origin : Fin (L + 1)) {i : Fin (L + 1)}
    (hi : i ∈ standardQuadraticInteriorIndexBand L origin)
    {ε Tmin : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hTmin0 : 0 < Tmin)
    (hTmin : Tmin ≤ ε * (L : ℝ))
    (hTmax : ε * (L : ℝ) ≤ 1) :
    |standardQuadraticSignedPositionCoefficient ε
      ((i.val : ℤ) - (origin.val : ℤ))| ≤ Real.cos (Tmin / 4) := by
  rcases standardQuadraticInteriorIndexBand_physicalTime_bounds origin hi
    hε0 hTmin hTmax with ⟨hlow, hhigh⟩
  exact abs_standardQuadraticSignedPositionCoefficient_le_cos
    hε0 hε1 (by positivity) _ hlow hhigh

/-- Centered energy control and the canonical quarter-band give the Gaussian
overlap-weighted scalar coefficient a uniform positive loss from one. -/
theorem standardQuadratic_alignedScalarSum_add_uniformLoss_le_one
    {L : ℕ} (origin : Fin (L + 1))
    (trajectory₁ trajectory₂ : Fin (L + 1) → PhaseSpace ι)
    (center₁ center₂ δ : ℝ)
    (henergy₁ : ∀ i,
      |energy standardQuadraticPotential (trajectory₁ i) - center₁| ≤ δ)
    (henergy₂ : ∀ i,
      |energy standardQuadraticPotential (trajectory₂ i) - center₂| ≤ δ)
    {ε Tmin : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hTmin0 : 0 < Tmin)
    (hTmin : Tmin ≤ ε * (L : ℝ))
    (hTmax : ε * (L : ℝ) ≤ 1) :
    (∑ i, min (trajectoryIndexPMF standardQuadraticPotential trajectory₁ i)
          (trajectoryIndexPMF standardQuadraticPotential trajectory₂ i) *
        ENNReal.ofReal |standardQuadraticSignedPositionCoefficient ε
          ((i.val : ℤ) - (origin.val : ℤ))|) +
      ENNReal.ofReal ((4 * Real.exp (2 * δ))⁻¹) *
        (1 - ENNReal.ofReal (Real.cos (Tmin / 4))) ≤ 1 := by
  classical
  let weight : Fin (L + 1) → ENNReal := fun i =>
    min (trajectoryIndexPMF standardQuadraticPotential trajectory₁ i)
      (trajectoryIndexPMF standardQuadraticPotential trajectory₂ i)
  let scalar : Fin (L + 1) → ENNReal := fun i =>
    ENNReal.ofReal |standardQuadraticSignedPositionCoefficient ε
      ((i.val : ℤ) - (origin.val : ℤ))|
  let band := standardQuadraticInteriorIndexBand L origin
  let ρ := ENNReal.ofReal (Real.cos (Tmin / 4))
  let η := ENNReal.ofReal ((4 * Real.exp (2 * δ))⁻¹)
  apply Mcmc.Finite.weightedCost_add_bandLoss_le_one
    weight scalar (fun i => i ∈ band) ρ (η * (1 - ρ))
  · dsimp [weight]
    calc
      (∑ i, min (trajectoryIndexPMF standardQuadraticPotential trajectory₁ i)
          (trajectoryIndexPMF standardQuadraticPotential trajectory₂ i)) ≤
          ∑ i, trajectoryIndexPMF standardQuadraticPotential trajectory₁ i :=
        Finset.sum_le_sum fun i hi => min_le_left _ _
      _ = 1 := by
        rw [show ∑ i, trajectoryIndexPMF standardQuadraticPotential trajectory₁ i =
            ∑' i, trajectoryIndexPMF standardQuadraticPotential trajectory₁ i by
              rw [tsum_fintype], PMF.tsum_coe]
  · intro i
    dsimp [scalar]
    apply ENNReal.ofReal_le_one.mpr
    rw [abs_standardQuadraticSignedPositionCoefficient_eq_cos
      (by rw [abs_of_nonneg hε0]; linarith)]
    exact Real.abs_cos_le_one _
  · intro i hi
    dsimp [scalar, ρ, band] at hi ⊢
    apply ENNReal.ofReal_le_ofReal
    exact standardQuadraticInteriorIndexBand_coefficient_le origin hi
      hε0 hε1 hTmin0 hTmin hTmax
  · dsimp [ρ]
    apply ENNReal.ofReal_le_one.mpr
    exact Real.cos_le_one _
  · have hmass := standardQuadraticInteriorIndexBand_overlapMass_ge
      standardQuadraticPotential trajectory₁ trajectory₂ center₁ center₂ δ
        henergy₁ henergy₂ origin
    have hmul := mul_le_mul_right hmass (1 - ρ)
    dsimp [η, weight, band]
    apply le_trans (by simpa only [mul_comm] using hmul)
    rw [Finset.mul_sum]
    calc
      (∑ i ∈ standardQuadraticInteriorIndexBand L origin,
          (1 - ρ) * weight i) =
          ∑ i, if i ∈ standardQuadraticInteriorIndexBand L origin then
            weight i * (1 - ρ) else 0 := by
        rw [← Finset.sum_filter]
        rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
        simp only [mul_comm]
      _ ≤ _ := le_rfl

/-- Explicit `L`-independent loss in the Gaussian aligned overlap estimate. -/
noncomputable def standardQuadraticAlignedLoss (Tmin δ : ℝ) : ENNReal :=
  ENNReal.ofReal ((4 * Real.exp (2 * δ))⁻¹) *
    (1 - ENNReal.ofReal (Real.cos (Tmin / 4)))

/-- Explicit finite aligned contraction rate obtained by subtracting the
uniform band loss from one. -/
noncomputable def standardQuadraticAlignedRate (Tmin δ : ℝ) : NNReal :=
  (1 - standardQuadraticAlignedLoss Tmin δ).toNNReal

/-- The explicit Gaussian aligned rate is strictly below one on every
positive lower integration-time bound `Tmin ≤ 1`. -/
theorem standardQuadraticAlignedRate_lt_one
    {Tmin δ : ℝ} (hTmin0 : 0 < Tmin) (hTminOne : Tmin ≤ 1) :
    standardQuadraticAlignedRate Tmin δ < 1 := by
  let ρ : ENNReal := ENNReal.ofReal (Real.cos (Tmin / 4))
  let η : ENNReal := ENNReal.ofReal ((4 * Real.exp (2 * δ))⁻¹)
  have hρlt : ρ < 1 := by
    apply ENNReal.ofReal_lt_one.mpr
    apply cos_lt_one_of_pos_of_le_pi (by positivity)
    have hOnePi : (1 : ℝ) ≤ Real.pi := (by norm_num : (1 : ℝ) ≤ 2).trans
      Real.two_le_pi
    linarith
  have hηpos : 0 < η := by
    apply ENNReal.ofReal_pos.mpr
    exact inv_pos.mpr (mul_pos (by norm_num) (Real.exp_pos _))
  have hlosspos : 0 < standardQuadraticAlignedLoss Tmin δ := by
    exact ENNReal.mul_pos hηpos.ne' (tsub_pos_iff_lt.mpr hρlt).ne'
  apply ENNReal.coe_lt_coe.mp
  rw [standardQuadraticAlignedRate, ENNReal.coe_toNNReal
    (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)]
  exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hlosspos.ne'

/-- The overlap-weighted scalar coefficient is bounded by the same explicit
rate for every admissible trajectory length and origin. -/
theorem standardQuadratic_alignedScalarSum_le_rate
    {L : ℕ} (origin : Fin (L + 1))
    (trajectory₁ trajectory₂ : Fin (L + 1) → PhaseSpace ι)
    (center₁ center₂ δ : ℝ)
    (henergy₁ : ∀ i,
      |energy standardQuadraticPotential (trajectory₁ i) - center₁| ≤ δ)
    (henergy₂ : ∀ i,
      |energy standardQuadraticPotential (trajectory₂ i) - center₂| ≤ δ)
    {ε Tmin : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hTmin0 : 0 < Tmin)
    (hTmin : Tmin ≤ ε * (L : ℝ))
    (hTmax : ε * (L : ℝ) ≤ 1) :
    (∑ i, min (trajectoryIndexPMF standardQuadraticPotential trajectory₁ i)
          (trajectoryIndexPMF standardQuadraticPotential trajectory₂ i) *
        ENNReal.ofReal |standardQuadraticSignedPositionCoefficient ε
          ((i.val : ℤ) - (origin.val : ℤ))|) ≤
      (standardQuadraticAlignedRate Tmin δ : ENNReal) := by
  have hadd := standardQuadratic_alignedScalarSum_add_uniformLoss_le_one
    origin trajectory₁ trajectory₂ center₁ center₂ δ henergy₁ henergy₂
      hε0 hε1 hTmin0 hTmin hTmax
  rw [standardQuadraticAlignedRate, ENNReal.coe_toNNReal
    (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)]
  apply ENNReal.le_sub_of_add_le_right
  · unfold standardQuadraticAlignedLoss
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
  · exact hadd

/-- Squaring the Gaussian aligned coefficient preserves the same uniform
overlap-weighted subunit rate. This is the aligned part of the paper's
squared-cost transport argument. -/
theorem standardQuadratic_alignedScalarSquareSum_le_rate
    {L : ℕ} (origin : Fin (L + 1))
    (trajectory₁ trajectory₂ : Fin (L + 1) → PhaseSpace ι)
    (center₁ center₂ δ : ℝ)
    (henergy₁ : ∀ i,
      |energy standardQuadraticPotential (trajectory₁ i) - center₁| ≤ δ)
    (henergy₂ : ∀ i,
      |energy standardQuadraticPotential (trajectory₂ i) - center₂| ≤ δ)
    {ε Tmin : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hTmin0 : 0 < Tmin)
    (hTmin : Tmin ≤ ε * (L : ℝ))
    (hTmax : ε * (L : ℝ) ≤ 1) :
    (∑ i, min (trajectoryIndexPMF standardQuadraticPotential trajectory₁ i)
          (trajectoryIndexPMF standardQuadraticPotential trajectory₂ i) *
        (ENNReal.ofReal |standardQuadraticSignedPositionCoefficient ε
          ((i.val : ℤ) - (origin.val : ℤ))|) ^ 2) ≤
      (standardQuadraticAlignedRate Tmin δ : ENNReal) := by
  calc
    (∑ i, min (trajectoryIndexPMF standardQuadraticPotential trajectory₁ i)
          (trajectoryIndexPMF standardQuadraticPotential trajectory₂ i) *
        (ENNReal.ofReal |standardQuadraticSignedPositionCoefficient ε
          ((i.val : ℤ) - (origin.val : ℤ))|) ^ 2) ≤
        ∑ i, min (trajectoryIndexPMF standardQuadraticPotential trajectory₁ i)
          (trajectoryIndexPMF standardQuadraticPotential trajectory₂ i) *
        ENNReal.ofReal |standardQuadraticSignedPositionCoefficient ε
          ((i.val : ℤ) - (origin.val : ℤ))| := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_right
      rw [pow_two]
      have hcoeff : ENNReal.ofReal
          |standardQuadraticSignedPositionCoefficient ε
            ((i.val : ℤ) - (origin.val : ℤ))| ≤ 1 := by
        apply ENNReal.ofReal_le_one.mpr
        rw [abs_standardQuadraticSignedPositionCoefficient_eq_cos
          (by rw [abs_of_nonneg hε0]; linarith)]
        exact Real.abs_cos_le_one _
      exact mul_le_of_le_one_left (by positivity) hcoeff
    _ ≤ _ := standardQuadratic_alignedScalarSum_le_rate origin trajectory₁
      trajectory₂ center₁ center₂ δ henergy₁ henergy₂ hε0 hε1 hTmin0
      hTmin hTmax

/-- The preceding explicit loss can be packaged as one fixed finite
`NNReal` rate strictly below one. -/
theorem exists_standardQuadratic_alignedScalarRate_lt_one
    {L : ℕ} (origin : Fin (L + 1))
    (trajectory₁ trajectory₂ : Fin (L + 1) → PhaseSpace ι)
    (center₁ center₂ δ : ℝ)
    (henergy₁ : ∀ i,
      |energy standardQuadraticPotential (trajectory₁ i) - center₁| ≤ δ)
    (henergy₂ : ∀ i,
      |energy standardQuadraticPotential (trajectory₂ i) - center₂| ≤ δ)
    {ε Tmin : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hTmin0 : 0 < Tmin)
    (hTmin : Tmin ≤ ε * (L : ℝ))
    (hTmax : ε * (L : ℝ) ≤ 1) :
    ∃ rate : NNReal, rate < 1 ∧
      (∑ i, min (trajectoryIndexPMF standardQuadraticPotential trajectory₁ i)
            (trajectoryIndexPMF standardQuadraticPotential trajectory₂ i) *
          ENNReal.ofReal |standardQuadraticSignedPositionCoefficient ε
            ((i.val : ℤ) - (origin.val : ℤ))|) ≤ (rate : ENNReal) := by
  let ρ : ENNReal := ENNReal.ofReal (Real.cos (Tmin / 4))
  let η : ENNReal := ENNReal.ofReal ((4 * Real.exp (2 * δ))⁻¹)
  let loss := η * (1 - ρ)
  have hTminOne : Tmin ≤ 1 := hTmin.trans hTmax
  have hρlt : ρ < 1 := by
    apply ENNReal.ofReal_lt_one.mpr
    apply cos_lt_one_of_pos_of_le_pi (by positivity)
    have hOnePi : (1 : ℝ) ≤ Real.pi := (by norm_num : (1 : ℝ) ≤ 2).trans
      Real.two_le_pi
    linarith
  have hηpos : 0 < η := by
    apply ENNReal.ofReal_pos.mpr
    exact inv_pos.mpr (mul_pos (by norm_num) (Real.exp_pos _))
  have hlosspos : 0 < loss :=
    ENNReal.mul_pos hηpos.ne' (tsub_pos_iff_lt.mpr hρlt).ne'
  have hlossTop : loss ≠ ⊤ := by
    dsimp [loss, η, ρ]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
  have hadd := standardQuadratic_alignedScalarSum_add_uniformLoss_le_one
    origin trajectory₁ trajectory₂ center₁ center₂ δ henergy₁ henergy₂
      hε0 hε1 hTmin0 hTmin hTmax
  let rate : NNReal := (1 - loss).toNNReal
  refine ⟨rate, ?_, ?_⟩
  · apply ENNReal.coe_lt_coe.mp
    rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.one_ne_top
      tsub_le_self)]
    exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hlosspos.ne'
  · rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.one_ne_top
      tsub_le_self)]
    exact ENNReal.le_sub_of_add_le_right hlossTop hadd

omit [Fintype ι] in
/-- Exact shared-momentum position difference at every signed Gaussian
leapfrog offset. -/
theorem standardQuadratic_signedLeapfrog_sharedMomentum_position_sub
    (ε : ℝ) (k : ℤ) (q₁ q₂ : Position ι) (p : Momentum ι) :
    (signedLeapfrog standardQuadraticGradient ε k (q₁, p)).1 -
        (signedLeapfrog standardQuadraticGradient ε k (q₂, p)).1 =
      standardQuadraticSignedPositionCoefficient ε k • (q₁ - q₂) := by
  cases k with
  | ofNat n =>
      change
        (leapfrogN standardQuadraticGradient ε n (q₁, p)).1 -
            (leapfrogN standardQuadraticGradient ε n (q₂, p)).1 = _
      exact (standardQuadratic_leapfrogN_sharedMomentum_sub
        ε n q₁ q₂ p).1
  | negSucc n =>
      change
        (leapfrogN standardQuadraticGradient (-ε) (n + 1) (q₁, p)).1 -
            (leapfrogN standardQuadraticGradient (-ε) (n + 1) (q₂, p)).1 = _
      exact (standardQuadratic_leapfrogN_sharedMomentum_sub
        (-ε) (n + 1) q₁ q₂ p).1

/-- Every diagonal cost in an offset Gaussian trajectory is an exact scalar
multiple of the initial squared separation. This is the aligned-cost input to
the maximal and transport coupling bounds. -/
theorem standardQuadratic_trajectorySquaredPositionCost_diagonal_eq
    {L : ℕ} (ε : ℝ) (origin i : Fin (L + 1))
    (q₁ q₂ : Position ι) (p : Momentum ι) :
    trajectorySquaredPositionCost standardQuadraticGradient ε
        ((q₁, p), (q₂, p)) origin i i =
      ⟨(standardQuadraticSignedPositionCoefficient ε
          ((i.val : ℤ) - (origin.val : ℤ))) ^ 2 *
          squaredEuclideanNorm (q₁ - q₂),
        mul_nonneg (sq_nonneg _)
          (squaredEuclideanNorm_nonneg _)⟩ := by
  apply NNReal.eq
  change squaredEuclideanNorm
      ((signedLeapfrog standardQuadraticGradient ε
          ((i.val : ℤ) - (origin.val : ℤ)) (q₁, p)).1 -
        (signedLeapfrog standardQuadraticGradient ε
          ((i.val : ℤ) - (origin.val : ℤ)) (q₂, p)).1) = _
  rw [standardQuadratic_signedLeapfrog_sharedMomentum_position_sub,
    squaredEuclideanNorm_smul]
  rfl

/-- The Gaussian overlap-weighted aligned squared trajectory cost factors
into the squared scalar coefficient and the initial squared separation. -/
theorem standardQuadratic_alignedOverlapMomentTwo_eq
    {L : ℕ} (ε : ℝ) (origin : Fin (L + 1))
    (q₁ q₂ : Position ι) (p : Momentum ι) :
    (∑ i, min
        (trajectoryIndexPMF standardQuadraticPotential
          (offsetLeapfrogTrajectory standardQuadraticGradient ε origin
            (q₁, p)) i)
        (trajectoryIndexPMF standardQuadraticPotential
          (offsetLeapfrogTrajectory standardQuadraticGradient ε origin
            (q₂, p)) i) *
        (trajectorySquaredPositionCost standardQuadraticGradient ε
          (((q₁, p), (q₂, p))) origin i i : ENNReal)) =
      (∑ i, min
          (trajectoryIndexPMF standardQuadraticPotential
            (offsetLeapfrogTrajectory standardQuadraticGradient ε origin
              (q₁, p)) i)
          (trajectoryIndexPMF standardQuadraticPotential
            (offsetLeapfrogTrajectory standardQuadraticGradient ε origin
              (q₂, p)) i) *
          (ENNReal.ofReal |standardQuadraticSignedPositionCoefficient ε
            ((i.val : ℤ) - (origin.val : ℤ))|) ^ 2) *
        (initialSquaredPositionDistance q₁ q₂ : ENNReal) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [standardQuadratic_trajectorySquaredPositionCost_diagonal_eq,
    ENNReal.coe_nnreal_eq]
  change _ * ENNReal.ofReal
      ((standardQuadraticSignedPositionCoefficient ε
          ((i.val : ℤ) - (origin.val : ℤ))) ^ 2 *
        squaredEuclideanNorm (q₁ - q₂)) = _
  rw [ENNReal.ofReal_mul (sq_nonneg _),
    ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs,
    ← euclideanNorm_sq, ← coe_initialSquaredPositionDistance]
  ring

/-- The actual Gaussian overlap-weighted aligned exponent-two cost obeys the
same explicit uniform subunit rate as the exponent-one aligned cost. -/
theorem standardQuadratic_alignedOverlapMomentTwo_le_rate
    {L : ℕ} (ε : ℝ) (origin : Fin (L + 1))
    (q₁ q₂ : Position ι) (p : Momentum ι)
    (center₁ center₂ δ : ℝ)
    (henergy₁ : ∀ i,
      |energy standardQuadraticPotential
          (offsetLeapfrogTrajectory standardQuadraticGradient ε origin
            (q₁, p) i) - center₁| ≤ δ)
    (henergy₂ : ∀ i,
      |energy standardQuadraticPotential
          (offsetLeapfrogTrajectory standardQuadraticGradient ε origin
            (q₂, p) i) - center₂| ≤ δ)
    {Tmin : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hTmin0 : 0 < Tmin)
    (hTmin : Tmin ≤ ε * (L : ℝ))
    (hTmax : ε * (L : ℝ) ≤ 1) :
    (∑ i, min
        (trajectoryIndexPMF standardQuadraticPotential
          (offsetLeapfrogTrajectory standardQuadraticGradient ε origin
            (q₁, p)) i)
        (trajectoryIndexPMF standardQuadraticPotential
          (offsetLeapfrogTrajectory standardQuadraticGradient ε origin
            (q₂, p)) i) *
        (trajectorySquaredPositionCost standardQuadraticGradient ε
          (((q₁, p), (q₂, p))) origin i i : ENNReal)) ≤
      (standardQuadraticAlignedRate Tmin δ : ENNReal) *
        (initialSquaredPositionDistance q₁ q₂ : ENNReal) := by
  rw [standardQuadratic_alignedOverlapMomentTwo_eq]
  simpa only [mul_comm] using mul_le_mul_right
    (standardQuadratic_alignedScalarSquareSum_le_rate origin
      (offsetLeapfrogTrajectory standardQuadraticGradient ε origin (q₁, p))
      (offsetLeapfrogTrajectory standardQuadraticGradient ε origin (q₂, p))
      center₁ center₂ δ henergy₁ henergy₂ hε0 hε1 hTmin0 hTmin hTmax)
    (initialSquaredPositionDistance q₁ q₂ : ENNReal)

/-- Exponent-one aligned cost for the standard Gaussian is the absolute
signed position coefficient times the initial distance.  This is the exact
input to the sharp overlap-weighted maximal-coupling budget. -/
theorem standardQuadratic_trajectoryPositionMomentCost_one_diagonal_eq
    {L : ℕ} (ε : ℝ) (origin i : Fin (L + 1))
    (q₁ q₂ : Position ι) (p : Momentum ι) :
    trajectoryPositionMomentCost standardQuadraticGradient 1 ε
        ((q₁, p), (q₂, p)) origin i i =
      ⟨|standardQuadraticSignedPositionCoefficient ε
          ((i.val : ℤ) - (origin.val : ℤ))| * euclideanNorm (q₁ - q₂),
        mul_nonneg (abs_nonneg _) (euclideanNorm_nonneg _)⟩ := by
  apply NNReal.eq
  change euclideanNorm
      ((signedLeapfrog standardQuadraticGradient ε
          ((i.val : ℤ) - (origin.val : ℤ)) (q₁, p)).1 -
        (signedLeapfrog standardQuadraticGradient ε
          ((i.val : ℤ) - (origin.val : ℤ)) (q₂, p)).1) ^ 1 = _
  rw [standardQuadratic_signedLeapfrog_sharedMomentum_position_sub,
    pow_one, euclideanNorm_smul]
  rfl

/-- The sharp aligned term for Gaussian maximal coupling factors into a
dimensionless overlap-weighted scalar coefficient and the initial position
distance.  Thus proving a subunit aligned rate reduces to a finite scalar
inequality rather than further trajectory algebra. -/
theorem standardQuadratic_alignedOverlapMomentOne_eq
    {L : ℕ} (ε : ℝ) (origin : Fin (L + 1))
    (q₁ q₂ : Position ι) (p : Momentum ι) :
    (∑ i, min
        (trajectoryIndexPMF standardQuadraticPotential
          (offsetLeapfrogTrajectory standardQuadraticGradient ε origin
            (q₁, p)) i)
        (trajectoryIndexPMF standardQuadraticPotential
          (offsetLeapfrogTrajectory standardQuadraticGradient ε origin
            (q₂, p)) i) *
        (trajectoryPositionMomentCost standardQuadraticGradient 1 ε
          (((q₁, p), (q₂, p))) origin i i : ENNReal)) =
      (∑ i, min
          (trajectoryIndexPMF standardQuadraticPotential
            (offsetLeapfrogTrajectory standardQuadraticGradient ε origin
              (q₁, p)) i)
          (trajectoryIndexPMF standardQuadraticPotential
            (offsetLeapfrogTrajectory standardQuadraticGradient ε origin
              (q₂, p)) i) *
          ENNReal.ofReal |standardQuadraticSignedPositionCoefficient ε
            ((i.val : ℤ) - (origin.val : ℤ))|) *
        (initialPositionDistance q₁ q₂ : ENNReal) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [standardQuadratic_trajectoryPositionMomentCost_one_diagonal_eq]
  rw [ENNReal.coe_nnreal_eq]
  change _ * ENNReal.ofReal
      (|standardQuadraticSignedPositionCoefficient ε
          ((i.val : ℤ) - (origin.val : ℤ))| * euclideanNorm (q₁ - q₂)) = _
  rw [ENNReal.ofReal_mul (abs_nonneg _), ← coe_initialPositionDistance]
  ring

/-- The actual overlap-weighted aligned exponent-one trajectory cost obeys
the explicit uniform Gaussian rate. -/
theorem standardQuadratic_alignedOverlapMomentOne_le_rate
    {L : ℕ} (ε : ℝ) (origin : Fin (L + 1))
    (q₁ q₂ : Position ι) (p : Momentum ι)
    (center₁ center₂ δ : ℝ)
    (henergy₁ : ∀ i,
      |energy standardQuadraticPotential
          (offsetLeapfrogTrajectory standardQuadraticGradient ε origin
            (q₁, p) i) - center₁| ≤ δ)
    (henergy₂ : ∀ i,
      |energy standardQuadraticPotential
          (offsetLeapfrogTrajectory standardQuadraticGradient ε origin
            (q₂, p) i) - center₂| ≤ δ)
    {Tmin : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hTmin0 : 0 < Tmin)
    (hTmin : Tmin ≤ ε * (L : ℝ))
    (hTmax : ε * (L : ℝ) ≤ 1) :
    (∑ i, min
        (trajectoryIndexPMF standardQuadraticPotential
          (offsetLeapfrogTrajectory standardQuadraticGradient ε origin
            (q₁, p)) i)
        (trajectoryIndexPMF standardQuadraticPotential
          (offsetLeapfrogTrajectory standardQuadraticGradient ε origin
            (q₂, p)) i) *
        (trajectoryPositionMomentCost standardQuadraticGradient 1 ε
          (((q₁, p), (q₂, p))) origin i i : ENNReal)) ≤
      (standardQuadraticAlignedRate Tmin δ : ENNReal) *
        (initialPositionDistance q₁ q₂ : ENNReal) := by
  rw [standardQuadratic_alignedOverlapMomentOne_eq]
  have hscalar := standardQuadratic_alignedScalarSum_le_rate
    origin
    (offsetLeapfrogTrajectory standardQuadraticGradient ε origin (q₁, p))
    (offsetLeapfrogTrajectory standardQuadraticGradient ε origin (q₂, p))
    center₁ center₂ δ henergy₁ henergy₂ hε0 hε1 hTmin0 hTmin hTmax
  simpa only [mul_comm] using mul_le_mul_right hscalar
    (initialPositionDistance q₁ q₂ : ENNReal)

/-- Exact one-step Hamiltonian error for leapfrog on the standard Gaussian
target. In particular, every term is of order at least `ε³`; later bounds can
sum this identity over a fixed integration horizon. -/
theorem standardQuadratic_energy_leapfrog_sub_eq
    (ε : ℝ) (z : PhaseSpace ι) :
    energy standardQuadraticPotential
        (leapfrog standardQuadraticGradient ε z) -
      energy standardQuadraticPotential z =
    ∑ i, (
      (ε ^ 4 / 8) * (z.2 i ^ 2 - z.1 i ^ 2) +
      (ε ^ 6 / 32) * z.1 i ^ 2 +
      (ε ^ 3 / 4) * (1 - ε ^ 2 / 2) * (z.1 i * z.2 i)) := by
  unfold energy standardQuadraticPotential kineticEnergy
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply congrArg (fun f : ι → ℝ => ∑ i, f i)
  funext i
  rw [leapfrog_standardQuadratic_fst_apply,
    leapfrog_standardQuadratic_snd_apply]
  ring

/-- At step size `sqrt 2`, the standard-quadratic one-step energy defect has
the same radial formula in every finite dimension: refreshed kinetic energy
minus half the incoming quadratic potential.  This is the dimension-free
replacement for the scalar logistic exponent used by the existing HMC drift
proof. -/
theorem standardQuadratic_leapfrog_sqrtTwo_energy_defect
    (q : Position ι) (p : Momentum ι) :
    energy standardQuadraticPotential
        (leapfrog standardQuadraticGradient (Real.sqrt 2) (q, p)) -
      energy standardQuadraticPotential (q, p) =
        kineticEnergy p - standardQuadraticPotential q / 2 := by
  rw [standardQuadratic_energy_leapfrog_sub_eq]
  have hsqrt2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt3 : (Real.sqrt 2) ^ 3 = 2 * Real.sqrt 2 := by
    calc
      (Real.sqrt 2) ^ 3 = (Real.sqrt 2) ^ 2 * Real.sqrt 2 := by ring
      _ = 2 * Real.sqrt 2 := by rw [hsqrt2]
  have hsqrt4 : (Real.sqrt 2) ^ 4 = (4 : ℝ) := by
    calc
      (Real.sqrt 2) ^ 4 = ((Real.sqrt 2) ^ 2) ^ 2 := by ring
      _ = 4 := by rw [hsqrt2]; norm_num
  have hsqrt6 : (Real.sqrt 2) ^ 6 = (8 : ℝ) := by
    calc
      (Real.sqrt 2) ^ 6 = ((Real.sqrt 2) ^ 2) ^ 3 := by ring
      _ = 8 := by rw [hsqrt2]; norm_num
  rw [hsqrt2, hsqrt3, hsqrt4, hsqrt6]
  unfold standardQuadraticPotential kineticEnergy
  simp only [Finset.mul_sum]
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  apply congrArg (fun f : ι → ℝ => ∑ i, f i)
  funext i
  ring

/-- The negative-time `sqrt 2` step has the same radial energy defect. -/
theorem standardQuadratic_leapfrog_negSqrtTwo_energy_defect
    (q : Position ι) (p : Momentum ι) :
    energy standardQuadraticPotential
        (leapfrog standardQuadraticGradient (-(Real.sqrt 2)) (q, p)) -
      energy standardQuadraticPotential (q, p) =
        kineticEnergy p - standardQuadraticPotential q / 2 := by
  rw [← momentumFlip_leapfrog_momentumFlip standardQuadraticGradient
    (Real.sqrt 2) (q, p), energy_momentumFlip]
  have h := standardQuadratic_leapfrog_sqrtTwo_energy_defect q (-p)
  have hflip : momentumFlip (q, p) = (q, -p) := by
    ext i <;> simp [momentumFlip]
  rw [hflip]
  calc
    energy standardQuadraticPotential
          (leapfrog standardQuadraticGradient (Real.sqrt 2) (q, -p)) -
        energy standardQuadraticPotential (q, p) =
      energy standardQuadraticPotential
          (leapfrog standardQuadraticGradient (Real.sqrt 2) (q, -p)) -
        energy standardQuadraticPotential (q, -p) := by
          congr 1
          simp [energy, kineticEnergy]
    _ = kineticEnergy p - standardQuadraticPotential q / 2 := by
      simpa [kineticEnergy] using h

/-- In arbitrary finite dimension, the probability of retaining the current
index in the two-point `sqrt 2` trajectory is bounded by the exponential of
the radial energy defect. -/
theorem standardQuadratic_sqrtTwo_currentIndexProbability_le
    (origin : Fin 2) (q : Position ι) (p : Momentum ι) :
    trajectoryIndexPMF standardQuadraticPotential
        (offsetLeapfrogTrajectory standardQuadraticGradient (Real.sqrt 2)
          origin (q, p)) origin ≤
      ENNReal.ofReal (Real.exp
        (kineticEnergy p - standardQuadraticPotential q / 2)) := by
  fin_cases origin
  · let current : Fin 2 := ⟨0, by omega⟩
    let endpoint : Fin 2 := ⟨1, by omega⟩
    have h := trajectoryIndexPMF_le_exp_energy_sub
      standardQuadraticPotential
      (offsetLeapfrogTrajectory standardQuadraticGradient (Real.sqrt 2)
        current (q, p)) current endpoint
    dsimp only [current, endpoint] at h ⊢
    rw [offsetLeapfrogTrajectory_origin] at h
    change _ ≤ ENNReal.ofReal (Real.exp
      (energy standardQuadraticPotential
          (leapfrog standardQuadraticGradient (Real.sqrt 2) (q, p)) -
        energy standardQuadraticPotential (q, p))) at h
    simpa [standardQuadratic_leapfrog_sqrtTwo_energy_defect] using h
  · let endpoint : Fin 2 := ⟨0, by omega⟩
    let current : Fin 2 := ⟨1, by omega⟩
    have h := trajectoryIndexPMF_le_exp_energy_sub
      standardQuadraticPotential
      (offsetLeapfrogTrajectory standardQuadraticGradient (Real.sqrt 2)
        current (q, p)) current endpoint
    dsimp only [current, endpoint] at h ⊢
    rw [offsetLeapfrogTrajectory_origin] at h
    change _ ≤ ENNReal.ofReal (Real.exp
      (energy standardQuadraticPotential
          (leapfrog standardQuadraticGradient (-(Real.sqrt 2)) (q, p)) -
        energy standardQuadraticPotential (q, p))) at h
    simpa [standardQuadratic_leapfrog_negSqrtTwo_energy_defect] using h

@[simp]
theorem standardDistanceLyapunov_neg (q : Position ι) :
    standardDistanceLyapunov (-q) = standardDistanceLyapunov q := by
  simp [standardDistanceLyapunov, dist_eq_norm]

/-- The dimension-free two-point multinomial expectation is controlled by a
capped retention term and the Lyapunov cost of the rescaled refreshed
momentum, uniformly over the randomized trajectory root. -/
theorem standardQuadratic_sqrtTwo_indexExpectation_le
    (origin : Fin 2) (q : Position ι) (p : Momentum ι) :
    (∑ selected : Fin 2,
      trajectoryIndexPMF standardQuadraticPotential
          (offsetLeapfrogTrajectory standardQuadraticGradient (Real.sqrt 2)
            origin (q, p)) selected *
        standardDistanceLyapunov
          (offsetLeapfrogTrajectory standardQuadraticGradient (Real.sqrt 2)
            origin (q, p) selected).1) ≤
      min 1 (ENNReal.ofReal (Real.exp
          (kineticEnergy p - standardQuadraticPotential q / 2))) *
          standardDistanceLyapunov q +
        standardDistanceLyapunov (Real.sqrt 2 • p) := by
  let trajectory := offsetLeapfrogTrajectory standardQuadraticGradient
    (Real.sqrt 2) origin (q, p)
  let retention := ENNReal.ofReal (Real.exp
    (kineticEnergy p - standardQuadraticPotential q / 2))
  have hretain : trajectoryIndexPMF standardQuadraticPotential trajectory origin ≤
      min 1 retention := by
    apply le_min
    · exact (trajectoryIndexPMF standardQuadraticPotential trajectory).coe_le_one origin
    · exact standardQuadratic_sqrtTwo_currentIndexProbability_le origin q p
  fin_cases origin
  · rw [Fin.sum_univ_two]
    have hretain0 :
        trajectoryIndexPMF standardQuadraticPotential trajectory (0 : Fin 2) ≤
          min 1 retention := by simpa using hretain
    have hcurrent :
        trajectoryIndexPMF standardQuadraticPotential trajectory (0 : Fin 2) *
            standardDistanceLyapunov (trajectory (0 : Fin 2)).1 ≤
          min 1 retention * standardDistanceLyapunov q := by
      rw [show trajectory (0 : Fin 2) = (q, p) by simp [trajectory]]
      simpa only [mul_comm] using
        mul_le_mul_right hretain0 (standardDistanceLyapunov q)
    have hendpoint :
        trajectoryIndexPMF standardQuadraticPotential trajectory (1 : Fin 2) *
            standardDistanceLyapunov (trajectory (1 : Fin 2)).1 ≤
          standardDistanceLyapunov (Real.sqrt 2 • p) := by
      rw [show (trajectory (1 : Fin 2)).1 = Real.sqrt 2 • p by
        change (leapfrog standardQuadraticGradient (Real.sqrt 2) (q, p)).1 = _
        exact standardQuadratic_leapfrog_sqrtTwo_fst q p]
      calc
        _ ≤ 1 * standardDistanceLyapunov (Real.sqrt 2 • p) := by
          gcongr
          exact (trajectoryIndexPMF standardQuadraticPotential trajectory).coe_le_one _
        _ = _ := one_mul _
    exact add_le_add hcurrent hendpoint
  · rw [Fin.sum_univ_two]
    have hretain1 :
        trajectoryIndexPMF standardQuadraticPotential trajectory (1 : Fin 2) ≤
          min 1 retention := by simpa using hretain
    have hendpoint :
        trajectoryIndexPMF standardQuadraticPotential trajectory (0 : Fin 2) *
            standardDistanceLyapunov (trajectory (0 : Fin 2)).1 ≤
          standardDistanceLyapunov (Real.sqrt 2 • p) := by
      rw [show (trajectory (0 : Fin 2)).1 = -(Real.sqrt 2 • p) by
        change (leapfrog standardQuadraticGradient (-(Real.sqrt 2)) (q, p)).1 = _
        rw [standardQuadratic_leapfrog_negSqrtTwo_fst]
        simp]
      rw [standardDistanceLyapunov_neg]
      calc
        _ ≤ 1 * standardDistanceLyapunov (Real.sqrt 2 • p) := by
          gcongr
          exact (trajectoryIndexPMF standardQuadraticPotential trajectory).coe_le_one _
        _ = _ := one_mul _
    have hcurrent :
        trajectoryIndexPMF standardQuadraticPotential trajectory (1 : Fin 2) *
            standardDistanceLyapunov (trajectory (1 : Fin 2)).1 ≤
          min 1 retention * standardDistanceLyapunov q := by
      rw [show trajectory (1 : Fin 2) = (q, p) by simp [trajectory]]
      simpa only [mul_comm] using
        mul_le_mul_right hretain1 (standardDistanceLyapunov q)
    exact (add_le_add hendpoint hcurrent).trans_eq (add_comm _ _)

/-- Uniformly averaging the trajectory root preserves the dimension-free
retention-plus-endpoint bound. -/
theorem standardQuadratic_sqrtTwo_originIndexExpectation_le
    (q : Position ι) (p : Momentum ι) :
    (∑ origin : Fin 2, PMF.uniformOfFintype (Fin 2) origin *
      ∑ selected : Fin 2,
        trajectoryIndexPMF standardQuadraticPotential
            (offsetLeapfrogTrajectory standardQuadraticGradient (Real.sqrt 2)
              origin (q, p)) selected *
          standardDistanceLyapunov
            (offsetLeapfrogTrajectory standardQuadraticGradient (Real.sqrt 2)
              origin (q, p) selected).1) ≤
      min 1 (ENNReal.ofReal (Real.exp
          (kineticEnergy p - standardQuadraticPotential q / 2))) *
          standardDistanceLyapunov q +
        standardDistanceLyapunov (Real.sqrt 2 • p) := by
  let bound :=
    min 1 (ENNReal.ofReal (Real.exp
        (kineticEnergy p - standardQuadraticPotential q / 2))) *
        standardDistanceLyapunov q +
      standardDistanceLyapunov (Real.sqrt 2 • p)
  calc
    _ ≤ ∑ origin : Fin 2,
        PMF.uniformOfFintype (Fin 2) origin * bound := by
      apply Finset.sum_le_sum
      intro origin _
      dsimp only [bound]
      exact mul_le_mul_right
        (standardQuadratic_sqrtTwo_indexExpectation_le origin q p)
        (PMF.uniformOfFintype (Fin 2) origin)
    _ = (∑ origin : Fin 2, PMF.uniformOfFintype (Fin 2) origin) * bound := by
      rw [Finset.sum_mul]
    _ = bound := by
      rw [show ∑ origin : Fin 2, PMF.uniformOfFintype (Fin 2) origin = 1 by
        rw [show ∑ origin : Fin 2, PMF.uniformOfFintype (Fin 2) origin =
          ∑' origin : Fin 2, PMF.uniformOfFintype (Fin 2) origin by
            rw [tsum_fintype], PMF.tsum_coe], one_mul]

/-- Drift-ready expectation bound for the actual finite-dimensional
standard-quadratic multinomial-HMC kernel at `ε = √2`, `L = 1`. -/
theorem lintegral_standardQuadratic_sqrtTwo_hmc_le (q : Position ι) :
    (∫⁻ y, standardDistanceLyapunov y
      ∂standardPositionMultinomialHMC standardQuadraticPotential
        standardQuadraticGradient (Real.sqrt 2) 1
        contDiff_standardQuadraticPotential.continuous.measurable
        measurable_standardQuadraticGradient q) ≤
      ∫⁻ p : Momentum ι,
        min 1 (ENNReal.ofReal (Real.exp
          (kineticEnergy p - standardQuadraticPotential q / 2))) *
            standardDistanceLyapunov q +
          standardDistanceLyapunov (Real.sqrt 2 • p)
        ∂standardMomentumMeasure := by
  rw [standardPositionMultinomialHMC]
  rw [lintegral_positionMultinomialHMC standardQuadraticPotential
    standardQuadraticGradient (Real.sqrt 2) 1
    contDiff_standardQuadraticPotential.continuous.measurable
    measurable_standardQuadraticGradient standardMomentumMeasure
    standardDistanceLyapunov measurable_standardDistanceLyapunov]
  exact lintegral_mono fun p =>
    standardQuadratic_sqrtTwo_originIndexExpectation_le q p

/-- The canonical sup-norm Lyapunov function is bounded by the corresponding
Euclidean radial function. -/
theorem standardDistanceLyapunov_le_ofReal_one_add_euclideanNorm
    (q : Position ι) :
    standardDistanceLyapunov q ≤ ENNReal.ofReal (1 + euclideanNorm q) := by
  unfold standardDistanceLyapunov
  apply ENNReal.ofReal_le_ofReal
  have hdist : dist q 0 ≤ euclideanNorm q := by
    simpa only [sub_zero] using dist_le_euclideanNorm_sub q 0
  linarith

/-- The standard quadratic potential is half the squared Euclidean radius. -/
theorem standardQuadraticPotential_eq_half_euclideanNorm_sq
    (q : Position ι) :
    standardQuadraticPotential q = (1 / 2 : ℝ) * euclideanNorm q ^ 2 := by
  exact kineticEnergy_eq_half_euclideanNorm_sq q

/-- Radial finite-dimensional version of the scalar capped-retention bound.
The constants are deliberately coarse but independent of dimension. -/
theorem standardQuadratic_sqrtTwo_driftIntegrand_le
    (q : Position ι) (p : Momentum ι) :
    min 1 (ENNReal.ofReal (Real.exp
          (kineticEnergy p - standardQuadraticPotential q / 2))) *
          standardDistanceLyapunov q +
        standardDistanceLyapunov (Real.sqrt 2 • p) ≤
      17 + 4 * ENNReal.ofReal (euclideanNorm p) := by
  let qr := euclideanNorm q
  let pr := euclideanNorm p
  have hq0 : 0 ≤ qr := euclideanNorm_nonneg q
  have hp0 : 0 ≤ pr := euclideanNorm_nonneg p
  have hdefect :
      kineticEnergy p - standardQuadraticPotential q / 2 =
        pr ^ 2 / 2 - qr ^ 2 / 4 := by
    rw [kineticEnergy_eq_half_euclideanNorm_sq,
      standardQuadraticPotential_eq_half_euclideanNorm_sq]
    dsimp only [pr, qr]
    ring
  have hretentionReal :=
    min_one_exp_standardQuadratic_defect_mul_one_add_abs_le qr pr
  rw [abs_of_nonneg hq0, abs_of_nonneg hp0] at hretentionReal
  have hretention :
      min 1 (ENNReal.ofReal (Real.exp
          (kineticEnergy p - standardQuadraticPotential q / 2))) *
          standardDistanceLyapunov q ≤
        16 + 2 * ENNReal.ofReal pr := by
    apply le_trans (by
      simpa only [mul_comm] using mul_le_mul_right
        (standardDistanceLyapunov_le_ofReal_one_add_euclideanNorm q)
        (min 1 (ENNReal.ofReal (Real.exp
          (kineticEnergy p - standardQuadraticPotential q / 2)))))
    rw [hdefect, ← ENNReal.ofReal_one, ← ENNReal.ofReal_min,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 16)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hp0)]
    exact ENNReal.ofReal_le_ofReal (by
      simpa only [mul_comm, qr] using hretentionReal)
  have hsqrt : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_nonneg 2]
  have hendpoint :
      standardDistanceLyapunov (Real.sqrt 2 • p) ≤
        1 + 2 * ENNReal.ofReal pr := by
    apply (standardDistanceLyapunov_le_ofReal_one_add_euclideanNorm
      (Real.sqrt 2 • p)).trans
    rw [euclideanNorm_smul, abs_of_nonneg (Real.sqrt_nonneg 2),
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hp0)]
    apply ENNReal.ofReal_le_ofReal
    dsimp only [pr]
    nlinarith
  calc
    _ ≤ (16 + 2 * ENNReal.ofReal pr) +
        (1 + 2 * ENNReal.ofReal pr) := add_le_add hretention hendpoint
    _ = 17 + 4 * ENNReal.ofReal (euclideanNorm p) := by
      dsimp only [pr]
      ring

/-- The standard Gaussian has a finite first Euclidean-norm moment in every
finite coordinate dimension. -/
theorem lintegral_euclideanNorm_standardMomentumMeasure_ne_top :
    (∫⁻ p : Momentum ι, ENNReal.ofReal (euclideanNorm p)
      ∂standardMomentumMeasure) ≠ ⊤ := by
  let c : ℝ := (Fintype.card ι : ℝ) + 1
  have hc0 : 0 ≤ c := by dsimp only [c]; positivity
  have hpoint : ∀ p : Momentum ι,
      ENNReal.ofReal (euclideanNorm p) ≤
        ENNReal.ofReal c * ENNReal.ofReal ‖p‖ := by
    intro p
    rw [← ENNReal.ofReal_mul hc0]
    apply ENNReal.ofReal_le_ofReal
    have h := euclideanNorm_sub_le_card_succ_mul_dist p 0
    simpa only [sub_zero, dist_zero_right, c] using h
  have hbound :
      (∫⁻ p : Momentum ι, ENNReal.ofReal (euclideanNorm p)
        ∂standardMomentumMeasure) ≤
      ENNReal.ofReal c *
        (∫⁻ p : Momentum ι, ENNReal.ofReal ‖p‖
          ∂standardMomentumMeasure) := by
    calc
      _ ≤ ∫⁻ p : Momentum ι,
          ENNReal.ofReal c * ENNReal.ofReal ‖p‖
          ∂standardMomentumMeasure := lintegral_mono hpoint
      _ = ENNReal.ofReal c *
          (∫⁻ p : Momentum ι, ENNReal.ofReal ‖p‖
            ∂standardMomentumMeasure) := by
        exact lintegral_const_mul _
          ((ENNReal.continuous_ofReal.comp continuous_norm).measurable)
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      lintegral_norm_standardMomentumMeasure_ne_top) hbound

/-- Dimension-dependent but finite allowance for the standard-quadratic HMC
drift estimate. -/
noncomputable def standardQuadraticSqrtTwoDriftAllowance : ENNReal :=
  17 + 4 *
    (∫⁻ p : Momentum ι, ENNReal.ofReal (euclideanNorm p)
      ∂standardMomentumMeasure)

theorem standardQuadraticSqrtTwoDriftAllowance_ne_top :
    standardQuadraticSqrtTwoDriftAllowance (ι := ι) ≠ ⊤ := by
  unfold standardQuadraticSqrtTwoDriftAllowance
  exact ENNReal.add_ne_top.2 ⟨by norm_num,
    ENNReal.mul_ne_top (by norm_num)
      lintegral_euclideanNorm_standardMomentumMeasure_ne_top⟩

/-- The dimension-free radial envelope integrates to the explicit finite
Gaussian allowance. -/
theorem standardQuadratic_sqrtTwo_envelope_le_allowance (q : Position ι) :
    (∫⁻ p : Momentum ι,
      min 1 (ENNReal.ofReal (Real.exp
        (kineticEnergy p - standardQuadraticPotential q / 2))) *
          standardDistanceLyapunov q +
        standardDistanceLyapunov (Real.sqrt 2 • p)
      ∂standardMomentumMeasure) ≤
        standardQuadraticSqrtTwoDriftAllowance (ι := ι) := by
  calc
    _ ≤ ∫⁻ p : Momentum ι,
        17 + 4 * ENNReal.ofReal (euclideanNorm p)
        ∂standardMomentumMeasure := by
      exact lintegral_mono fun p =>
        standardQuadratic_sqrtTwo_driftIntegrand_le q p
    _ = standardQuadraticSqrtTwoDriftAllowance (ι := ι) := by
      rw [lintegral_add_left measurable_const, lintegral_const,
        measure_univ, mul_one]
      have heq :
          (∫⁻ p : Momentum ι, 4 * ENNReal.ofReal (euclideanNorm p)
            ∂standardMomentumMeasure) =
            4 * (∫⁻ p : Momentum ι, ENNReal.ofReal (euclideanNorm p)
              ∂standardMomentumMeasure) := by
        exact lintegral_const_mul 4
          (ENNReal.continuous_ofReal.comp
            continuous_euclideanNorm).measurable
      rw [heq]
      rfl

/-- Strict affine drift for the actual standard-quadratic multinomial-HMC
kernel in every finite dimension, at the explicit `ε = √2`, `L = 1`
parameter choice. -/
theorem standardQuadratic_sqrtTwo_hmc_drift (x : Position ι) :
    (∫⁻ y, standardDistanceLyapunov y
      ∂standardPositionMultinomialHMC standardQuadraticPotential
        standardQuadraticGradient (Real.sqrt 2) 1
        contDiff_standardQuadraticPotential.continuous.measurable
        measurable_standardQuadraticGradient x) ≤
      (1 / 2 : ENNReal) * standardDistanceLyapunov x +
        standardQuadraticSqrtTwoDriftAllowance (ι := ι) := by
  have huniform := (lintegral_standardQuadratic_sqrtTwo_hmc_le x).trans
    (standardQuadratic_sqrtTwo_envelope_le_allowance x)
  exact huniform.trans (le_add_left le_rfl)

/-- The difference between two one-step standard-quadratic Hamiltonian
defects is Lipschitz in the phase separation.  The explicit factor
`standardQuadraticEnergyErrorRate ε` retains the cubic dependence on the
step size needed when this estimate is telescoped over a fixed horizon. -/
theorem abs_standardQuadratic_oneStepEnergyDefect_sub_le
    (ε : ℝ) (z₁ z₂ : PhaseSpace ι) :
    |(energy standardQuadraticPotential
          (leapfrog standardQuadraticGradient ε z₁) -
        energy standardQuadraticPotential z₁) -
      (energy standardQuadraticPotential
          (leapfrog standardQuadraticGradient ε z₂) -
        energy standardQuadraticPotential z₂)| ≤
      (Fintype.card ι : ℝ) * 2 * standardQuadraticEnergyErrorRate ε *
        (euclideanNorm (z₁.1 - z₂.1) + euclideanNorm (z₁.2 - z₂.2)) *
        (euclideanPhaseSize z₁ + euclideanPhaseSize z₂) := by
  rw [standardQuadratic_energy_leapfrog_sub_eq,
    standardQuadratic_energy_leapfrog_sub_eq,
    ← Finset.sum_sub_distrib]
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  let D := euclideanNorm (z₁.1 - z₂.1) + euclideanNorm (z₁.2 - z₂.2)
  let S := euclideanPhaseSize z₁ + euclideanPhaseSize z₂
  have hD : 0 ≤ D := by
    dsimp [D]
    exact add_nonneg (euclideanNorm_nonneg _) (euclideanNorm_nonneg _)
  have hS : 0 ≤ S := by
    dsimp [S]
    exact add_nonneg (euclideanPhaseSize_nonneg _) (euclideanPhaseSize_nonneg _)
  have hterm : ∀ i ∈ Finset.univ,
      |((ε ^ 4 / 8) * (z₁.2 i ^ 2 - z₁.1 i ^ 2) +
          (ε ^ 6 / 32) * z₁.1 i ^ 2 +
          (ε ^ 3 / 4) * (1 - ε ^ 2 / 2) * (z₁.1 i * z₁.2 i)) -
        ((ε ^ 4 / 8) * (z₂.2 i ^ 2 - z₂.1 i ^ 2) +
          (ε ^ 6 / 32) * z₂.1 i ^ 2 +
          (ε ^ 3 / 4) * (1 - ε ^ 2 / 2) * (z₂.1 i * z₂.2 i))| ≤
        2 * standardQuadraticEnergyErrorRate ε * D * S := by
    intro i hi
    apply (abs_standardQuadraticEnergyDefectTerm_sub_le ε
      (z₁.1 i) (z₁.2 i) (z₂.1 i) (z₂.2 i)).trans
    have hq : |z₁.1 i - z₂.1 i| ≤ euclideanNorm (z₁.1 - z₂.1) := by
      simpa only [Pi.sub_apply] using abs_apply_le_euclideanNorm (z₁.1 - z₂.1) i
    have hp : |z₁.2 i - z₂.2 i| ≤ euclideanNorm (z₁.2 - z₂.2) := by
      simpa only [Pi.sub_apply] using abs_apply_le_euclideanNorm (z₁.2 - z₂.2) i
    have hz₁q : |z₁.1 i| ≤ euclideanNorm z₁.1 :=
      abs_apply_le_euclideanNorm z₁.1 i
    have hz₁p : |z₁.2 i| ≤ euclideanNorm z₁.2 :=
      abs_apply_le_euclideanNorm z₁.2 i
    have hz₂q : |z₂.1 i| ≤ euclideanNorm z₂.1 :=
      abs_apply_le_euclideanNorm z₂.1 i
    have hz₂p : |z₂.2 i| ≤ euclideanNorm z₂.2 :=
      abs_apply_le_euclideanNorm z₂.2 i
    have hcoordD : |z₁.1 i - z₂.1 i| + |z₁.2 i - z₂.2 i| ≤ D := by
      dsimp [D]
      linarith
    have hcoordS :
        |z₁.1 i| + |z₁.2 i| + |z₂.1 i| + |z₂.2 i| ≤ S := by
      dsimp [S, euclideanPhaseSize]
      linarith
    have hrate : 0 ≤ 2 * standardQuadraticEnergyErrorRate ε := by
      unfold standardQuadraticEnergyErrorRate
      positivity
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (mul_le_mul hcoordD hcoordS (by positivity) hD) hrate
  apply le_trans (Finset.sum_le_sum hterm)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  dsimp [D, S]
  ring_nf
  exact le_rfl

/-- The explicit Gaussian one-step defect satisfies the vanishing per-time
paired Lipschitz criterion on every bounded phase family. -/
theorem standardQuadratic_locallyUniformVanishingPerTimePairedOneStepEnergyError :
    LocallyUniformVanishingPerTimePairedOneStepEnergyError
      (standardQuadraticPotential (ι := ι))
      (standardQuadraticGradient (ι := ι)) := by
  intro R relativeRate hrelativeRate
  let S := max R 0
  let C := (Fintype.card ι : ℝ) * 2 * (2 * S)
  have hS : 0 ≤ S := le_max_right _ _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let εbar := min 1 (relativeRate / (C + 1))
  have hden : 0 < C + 1 := by linarith
  have hεbar : 0 < εbar :=
    lt_min zero_lt_one (div_pos hrelativeRate hden)
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hεone hε z₁ z₂ hz₁ hz₂
  have hzsum : euclideanPhaseSize z₁ + euclideanPhaseSize z₂ ≤ 2 * S := by
    have hRS : R ≤ S := le_max_left _ _
    linarith
  have hrate := standardQuadraticEnergyErrorRate_le_abs_cube hεone
  have habs : 0 ≤ |ε| := abs_nonneg ε
  have habsSq : |ε| ^ 2 ≤ |ε| := by nlinarith
  have hεquot : |ε| < relativeRate / (C + 1) :=
    hε.trans_le (min_le_right _ _)
  have hCeps : C * |ε| ≤ relativeRate := by
    have hmul : |ε| * (C + 1) < relativeRate :=
      (lt_div_iff₀ hden).mp hεquot
    nlinarith
  have hCepsSq : C * |ε| ^ 2 ≤ relativeRate :=
    (mul_le_mul_of_nonneg_left habsSq hC).trans hCeps
  apply (abs_standardQuadratic_oneStepEnergyDefect_sub_le ε z₁ z₂).trans
  let D := euclideanNorm (z₁.1 - z₂.1) +
    euclideanNorm (z₁.2 - z₂.2)
  have hD : 0 ≤ D := by
    dsimp [D]
    exact add_nonneg (euclideanNorm_nonneg _) (euclideanNorm_nonneg _)
  have hsizeSum' : 0 ≤ euclideanPhaseSize z₁ + euclideanPhaseSize z₂ :=
    add_nonneg (euclideanPhaseSize_nonneg _) (euclideanPhaseSize_nonneg _)
  have hcoefficient : (Fintype.card ι : ℝ) * 2 *
      standardQuadraticEnergyErrorRate ε *
      (euclideanPhaseSize z₁ + euclideanPhaseSize z₂) ≤
      relativeRate * |ε| := by
    calc
      (Fintype.card ι : ℝ) * 2 * standardQuadraticEnergyErrorRate ε *
          (euclideanPhaseSize z₁ + euclideanPhaseSize z₂) ≤
        (Fintype.card ι : ℝ) * 2 * |ε| ^ 3 * (2 * S) := by
          gcongr
      _ = C * |ε| ^ 2 * |ε| := by dsimp [C]; ring
      _ ≤ relativeRate * |ε| :=
        mul_le_mul_of_nonneg_right hCepsSq habs
  calc
    (Fintype.card ι : ℝ) * 2 * standardQuadraticEnergyErrorRate ε * D *
        (euclideanPhaseSize z₁ + euclideanPhaseSize z₂) =
      ((Fintype.card ι : ℝ) * 2 * standardQuadraticEnergyErrorRate ε *
        (euclideanPhaseSize z₁ + euclideanPhaseSize z₂)) * D := by ring
    _ ≤ (relativeRate * |ε|) * D :=
      mul_le_mul_of_nonneg_right hcoefficient hD
    _ = relativeRate * |ε| * D := rfl

/-- The equivalent derivative-level one-step criterion also holds for the
standard quadratic target. -/
theorem standardQuadratic_locallyUniformVanishingPerTimeOneStepEnergyDefectFDeriv :
    LocallyUniformVanishingPerTimeOneStepEnergyDefectFDeriv
      (standardQuadraticPotential (ι := ι))
      (standardQuadraticGradient (ι := ι)) :=
  LocallyUniformVanishingPerTimePairedOneStepEnergyError.toFDeriv
    standardQuadratic_locallyUniformVanishingPerTimePairedOneStepEnergyError

/-- Along arbitrary bounded standard-quadratic leapfrog paths, accumulated
centered energy defects remain Lipschitz in the full initial phase
separation. -/
theorem abs_standardQuadratic_energy_leapfrogN_defect_sub_le_general
    {ε : ℝ} (hε : |ε| ≤ 1) (n : ℕ) {T : ℝ}
    (horizon : (n : ℝ) * |ε| ≤ T) (z₁ z₂ : PhaseSpace ι) :
    |(energy standardQuadraticPotential
          (leapfrogN standardQuadraticGradient ε n z₁) -
        energy standardQuadraticPotential z₁) -
      (energy standardQuadraticPotential
          (leapfrogN standardQuadraticGradient ε n z₂) -
        energy standardQuadraticPotential z₂)| ≤
      (n : ℝ) * (Fintype.card ι : ℝ) * 2 *
        standardQuadraticEnergyErrorRate ε *
        (Real.exp ((13 / 4 : ℝ) * T) *
          (euclideanNorm (z₁.1 - z₂.1) +
            euclideanNorm (z₁.2 - z₂.2))) *
        (Real.exp ((13 / 4 : ℝ) * T) *
          (euclideanPhaseSize z₁ + euclideanPhaseSize z₂)) := by
  rw [energy_leapfrogN_sub_eq_sum_step_errors,
    energy_leapfrogN_sub_eq_sum_step_errors,
    ← Finset.sum_sub_distrib]
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  let A := Real.exp ((13 / 4 : ℝ) * T)
  let D := euclideanNorm (z₁.1 - z₂.1) +
    euclideanNorm (z₁.2 - z₂.2)
  let S := euclideanPhaseSize z₁ + euclideanPhaseSize z₂
  have hA : 0 ≤ A := (Real.exp_pos _).le
  have hD : 0 ≤ D := by
    dsimp [D]
    exact add_nonneg (euclideanNorm_nonneg _) (euclideanNorm_nonneg _)
  have hS : 0 ≤ S := by
    dsimp [S]
    exact add_nonneg (euclideanPhaseSize_nonneg _) (euclideanPhaseSize_nonneg _)
  have hterm : ∀ k ∈ Finset.range n,
      |(energy standardQuadraticPotential
            (leapfrog standardQuadraticGradient ε
              (leapfrogN standardQuadraticGradient ε k z₁)) -
          energy standardQuadraticPotential
            (leapfrogN standardQuadraticGradient ε k z₁)) -
        (energy standardQuadraticPotential
            (leapfrog standardQuadraticGradient ε
              (leapfrogN standardQuadraticGradient ε k z₂)) -
          energy standardQuadraticPotential
            (leapfrogN standardQuadraticGradient ε k z₂))| ≤
        (Fintype.card ι : ℝ) * 2 * standardQuadraticEnergyErrorRate ε *
          (A * D) * (A * S) := by
    intro k hk
    apply (abs_standardQuadratic_oneStepEnergyDefect_sub_le ε
      (leapfrogN standardQuadraticGradient ε k z₁)
      (leapfrogN standardQuadraticGradient ε k z₂)).trans
    have hkn : k ≤ n := Nat.le_of_lt (Finset.mem_range.mp hk)
    have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
    have hkhorizon : (k : ℝ) * |ε| ≤ T :=
      (mul_le_mul_of_nonneg_right hknR (abs_nonneg ε)).trans horizon
    have hsep := leapfrogN_euclideanNorm_phaseSub_le_exp
      regularPotential_standardQuadratic hε k hkhorizon z₁ z₂
    have hsize₁ := standardQuadratic_leapfrogN_euclideanPhaseSize_le_exp
      hε k hkhorizon z₁
    have hsize₂ := standardQuadratic_leapfrogN_euclideanPhaseSize_le_exp
      hε k hkhorizon z₂
    norm_num [leapfrogNormStabilityRate] at hsep
    have hsizes :
        euclideanPhaseSize
            (leapfrogN standardQuadraticGradient ε k z₁) +
          euclideanPhaseSize
            (leapfrogN standardQuadraticGradient ε k z₂) ≤ A * S := by
      dsimp [A, S]
      linarith
    have hcoeff : 0 ≤ (Fintype.card ι : ℝ) * 2 *
        standardQuadraticEnergyErrorRate ε := by
      unfold standardQuadraticEnergyErrorRate
      positivity
    have hprod := mul_le_mul hsep hsizes
      (add_nonneg (euclideanPhaseSize_nonneg _) (euclideanPhaseSize_nonneg _))
      (mul_nonneg hA hD)
    simpa only [D, A, mul_assoc] using
      mul_le_mul_of_nonneg_left hprod hcoeff
  apply le_trans (Finset.sum_le_sum hterm)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  dsimp [A, D, S]
  ring_nf
  exact le_rfl

/-- The standard quadratic target satisfies quantitative local relative
consistency for arbitrary signed leapfrog trajectories and bounded phase
pairs. -/
theorem standardQuadratic_locallyUniformLinearRelativeCenteredSignedEnergyError :
    LocallyUniformLinearRelativeCenteredSignedLeapfrogEnergyError
      (standardQuadraticPotential (ι := ι))
      (standardQuadraticGradient (ι := ι)) := by
  intro R T hT
  let S := max R 0
  let A := Real.exp ((13 / 4 : ℝ) * T)
  let C := T * (Fintype.card ι : ℝ) * 2 * A ^ 2 * (2 * S)
  have hS : 0 ≤ S := le_max_right _ _
  have hA : 0 ≤ A := (Real.exp_pos _).le
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro ε hε k horizon z₁ z₂ hz₁ hz₂
  have hzsum : euclideanPhaseSize z₁ + euclideanPhaseSize z₂ ≤ 2 * S := by
    have hRS : R ≤ S := le_max_left _ _
    linarith
  have hD : 0 ≤ euclideanNorm (z₁.1 - z₂.1) +
      euclideanNorm (z₁.2 - z₂.2) :=
    add_nonneg (euclideanNorm_nonneg _) (euclideanNorm_nonneg _)
  have hrate := standardQuadraticEnergyErrorRate_le_abs_cube hε
  have habsSq : |ε| ^ 2 ≤ |ε| := by
    have := abs_nonneg ε
    nlinarith
  cases k with
  | ofNat n =>
      have hraw := abs_standardQuadratic_energy_leapfrogN_defect_sub_le_general
        hε n horizon z₁ z₂
      apply hraw.trans
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hnrate : (n : ℝ) * standardQuadraticEnergyErrorRate ε ≤
          T * |ε| ^ 2 := by
        calc
          (n : ℝ) * standardQuadraticEnergyErrorRate ε ≤
              (n : ℝ) * |ε| ^ 3 :=
            mul_le_mul_of_nonneg_left hrate hn
          _ = ((n : ℝ) * |ε|) * |ε| ^ 2 := by ring
          _ ≤ T * |ε| ^ 2 :=
            mul_le_mul_of_nonneg_right horizon (sq_nonneg |ε|)
      have hmain := mul_le_mul hnrate hzsum
        (add_nonneg (euclideanPhaseSize_nonneg _) (euclideanPhaseSize_nonneg _))
        (mul_nonneg hT (sq_nonneg |ε|))
      dsimp [C, A]
      calc
        (n : ℝ) * (Fintype.card ι : ℝ) * 2 *
              standardQuadraticEnergyErrorRate ε *
              (Real.exp ((13 / 4 : ℝ) * T) *
                (euclideanNorm (z₁.1 - z₂.1) +
                  euclideanNorm (z₁.2 - z₂.2))) *
              (Real.exp ((13 / 4 : ℝ) * T) *
                (euclideanPhaseSize z₁ + euclideanPhaseSize z₂)) =
            ((n : ℝ) * standardQuadraticEnergyErrorRate ε) *
              (euclideanPhaseSize z₁ + euclideanPhaseSize z₂) *
              ((Fintype.card ι : ℝ) * 2 *
                Real.exp ((13 / 4 : ℝ) * T) ^ 2 *
                (euclideanNorm (z₁.1 - z₂.1) +
                  euclideanNorm (z₁.2 - z₂.2))) := by ring
        _ ≤ (T * |ε| ^ 2) * (2 * S) *
              ((Fintype.card ι : ℝ) * 2 *
                Real.exp ((13 / 4 : ℝ) * T) ^ 2 *
                (euclideanNorm (z₁.1 - z₂.1) +
                  euclideanNorm (z₁.2 - z₂.2))) := by
            exact mul_le_mul_of_nonneg_right hmain (by positivity)
        _ ≤ T * (Fintype.card ι : ℝ) * 2 *
              Real.exp ((13 / 4 : ℝ) * T) ^ 2 * (2 * S) * |ε| *
              (euclideanNorm (z₁.1 - z₂.1) +
                euclideanNorm (z₁.2 - z₂.2)) := by
            have hscale : 0 ≤ T * (2 * S) *
                ((Fintype.card ι : ℝ) * 2 *
                  Real.exp ((13 / 4 : ℝ) * T) ^ 2) := by positivity
            have hsquareScaled :=
              mul_le_mul_of_nonneg_left habsSq hscale
            have hfinal := mul_le_mul_of_nonneg_right hsquareScaled hD
            simpa only [mul_assoc, mul_comm, mul_left_comm] using hfinal
  | negSucc n =>
      change |(energy standardQuadraticPotential
            (leapfrogN standardQuadraticGradient (-ε) (n + 1) z₁) -
          energy standardQuadraticPotential z₁) -
        (energy standardQuadraticPotential
            (leapfrogN standardQuadraticGradient (-ε) (n + 1) z₂) -
          energy standardQuadraticPotential z₂)| ≤ _
      have hεneg : |-ε| ≤ 1 := by simpa only [abs_neg] using hε
      have hhor : ((n + 1 : ℕ) : ℝ) * |-ε| ≤ T := by
        simpa only [Int.natAbs_negSucc, abs_neg] using horizon
      simpa only [abs_neg] using
        (show |(energy standardQuadraticPotential
                (leapfrogN standardQuadraticGradient (-ε) (n + 1) z₁) -
              energy standardQuadraticPotential z₁) -
            (energy standardQuadraticPotential
                (leapfrogN standardQuadraticGradient (-ε) (n + 1) z₂) -
              energy standardQuadraticPotential z₂)| ≤
            C * |-ε| *
              (euclideanNorm (z₁.1 - z₂.1) +
                euclideanNorm (z₁.2 - z₂.2)) by
          have hbound := abs_standardQuadratic_energy_leapfrogN_defect_sub_le_general
            hεneg (n + 1) hhor z₁ z₂
          apply hbound.trans
          have hn : 0 ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
          have hrateNeg := standardQuadraticEnergyErrorRate_le_abs_cube hεneg
          have hnrate : ((n + 1 : ℕ) : ℝ) *
                standardQuadraticEnergyErrorRate (-ε) ≤ T * |-ε| ^ 2 := by
            calc
              ((n + 1 : ℕ) : ℝ) * standardQuadraticEnergyErrorRate (-ε) ≤
                  ((n + 1 : ℕ) : ℝ) * |-ε| ^ 3 :=
                mul_le_mul_of_nonneg_left hrateNeg hn
              _ = (((n + 1 : ℕ) : ℝ) * |-ε|) * |-ε| ^ 2 := by ring
              _ ≤ T * |-ε| ^ 2 :=
                mul_le_mul_of_nonneg_right hhor (sq_nonneg |-ε|)
          have hmain := mul_le_mul hnrate hzsum
            (add_nonneg (euclideanPhaseSize_nonneg _)
              (euclideanPhaseSize_nonneg _))
            (mul_nonneg hT (sq_nonneg |-ε|))
          have habsSqNeg : |-ε| ^ 2 ≤ |-ε| := by simpa only [abs_neg] using habsSq
          dsimp [C, A]
          calc
            ((n + 1 : ℕ) : ℝ) * (Fintype.card ι : ℝ) * 2 *
                  standardQuadraticEnergyErrorRate (-ε) *
                  (Real.exp ((13 / 4 : ℝ) * T) *
                    (euclideanNorm (z₁.1 - z₂.1) +
                      euclideanNorm (z₁.2 - z₂.2))) *
                  (Real.exp ((13 / 4 : ℝ) * T) *
                    (euclideanPhaseSize z₁ + euclideanPhaseSize z₂)) =
                (((n + 1 : ℕ) : ℝ) *
                    standardQuadraticEnergyErrorRate (-ε)) *
                  (euclideanPhaseSize z₁ + euclideanPhaseSize z₂) *
                  ((Fintype.card ι : ℝ) * 2 *
                    Real.exp ((13 / 4 : ℝ) * T) ^ 2 *
                    (euclideanNorm (z₁.1 - z₂.1) +
                      euclideanNorm (z₁.2 - z₂.2))) := by ring
            _ ≤ (T * |-ε| ^ 2) * (2 * S) *
                  ((Fintype.card ι : ℝ) * 2 *
                    Real.exp ((13 / 4 : ℝ) * T) ^ 2 *
                    (euclideanNorm (z₁.1 - z₂.1) +
                      euclideanNorm (z₁.2 - z₂.2))) := by
                exact mul_le_mul_of_nonneg_right hmain (by positivity)
            _ ≤ T * (Fintype.card ι : ℝ) * 2 *
                  Real.exp ((13 / 4 : ℝ) * T) ^ 2 * (2 * S) * |-ε| *
                  (euclideanNorm (z₁.1 - z₂.1) +
                    euclideanNorm (z₁.2 - z₂.2)) := by
                have hscale : 0 ≤ T * (2 * S) *
                    ((Fintype.card ι : ℝ) * 2 *
                      Real.exp ((13 / 4 : ℝ) * T) ^ 2) := by positivity
                have hsquareScaled :=
                  mul_le_mul_of_nonneg_left habsSqNeg hscale
                have hfinal := mul_le_mul_of_nonneg_right hsquareScaled hD
                simpa only [mul_assoc, mul_comm, mul_left_comm] using hfinal)

/-- Consequently, the standard quadratic target satisfies the compact-window
relative centered-energy property for every nonnegative integration horizon,
compact position core, and finite kinetic cutoff. -/
theorem standardQuadratic_uniformRelativeCenteredEnergyErrorOnCompactWindow
    {K : Set (Position ι)} (hK : IsCompact K)
    {k0 T : ℝ} (hk0 : 0 ≤ k0) (hT : 0 ≤ T) :
    UniformRelativeCenteredLeapfrogEnergyErrorOnCompactWindow
      (standardQuadraticPotential (ι := ι))
      (standardQuadraticGradient (ι := ι)) K k0 T :=
  standardQuadratic_locallyUniformLinearRelativeCenteredSignedEnergyError
    |>.onCompactWindow hK hk0 hT

/-- Along two standard-quadratic leapfrog paths with shared initial momentum,
the difference of accumulated Hamiltonian defects is controlled by the
initial position separation. -/
theorem abs_standardQuadratic_energy_leapfrogN_defect_sub_le_of_horizon
    {ε : ℝ} (hε : |ε| ≤ 1) (n : ℕ) {T : ℝ}
    (horizon : (n : ℝ) * |ε| ≤ T)
    (q₁ q₂ : Position ι) (p : Momentum ι) :
    |(energy standardQuadraticPotential
          (leapfrogN standardQuadraticGradient ε n (q₁, p)) -
        energy standardQuadraticPotential (q₁, p)) -
      (energy standardQuadraticPotential
          (leapfrogN standardQuadraticGradient ε n (q₂, p)) -
        energy standardQuadraticPotential (q₂, p))| ≤
      (n : ℝ) * (Fintype.card ι : ℝ) * 2 *
        standardQuadraticEnergyErrorRate ε *
        (Real.exp ((13 / 4 : ℝ) * T) * euclideanNorm (q₁ - q₂)) *
        (Real.exp ((13 / 4 : ℝ) * T) *
          (euclideanPhaseSize (q₁, p) + euclideanPhaseSize (q₂, p))) := by
  rw [energy_leapfrogN_sub_eq_sum_step_errors,
    energy_leapfrogN_sub_eq_sum_step_errors,
    ← Finset.sum_sub_distrib]
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  let A := Real.exp ((13 / 4 : ℝ) * T)
  let D := euclideanNorm (q₁ - q₂)
  let S := euclideanPhaseSize (q₁, p) + euclideanPhaseSize (q₂, p)
  have hA : 0 ≤ A := (Real.exp_pos _).le
  have hD : 0 ≤ D := euclideanNorm_nonneg _
  have hS : 0 ≤ S := by
    dsimp [S]
    exact add_nonneg (euclideanPhaseSize_nonneg _) (euclideanPhaseSize_nonneg _)
  have hrate : 0 ≤ standardQuadraticEnergyErrorRate ε := by
    unfold standardQuadraticEnergyErrorRate
    positivity
  have hterm : ∀ k ∈ Finset.range n,
      |(energy standardQuadraticPotential
            (leapfrog standardQuadraticGradient ε
              (leapfrogN standardQuadraticGradient ε k (q₁, p))) -
          energy standardQuadraticPotential
            (leapfrogN standardQuadraticGradient ε k (q₁, p))) -
        (energy standardQuadraticPotential
            (leapfrog standardQuadraticGradient ε
              (leapfrogN standardQuadraticGradient ε k (q₂, p))) -
          energy standardQuadraticPotential
            (leapfrogN standardQuadraticGradient ε k (q₂, p)))| ≤
        (Fintype.card ι : ℝ) * 2 * standardQuadraticEnergyErrorRate ε *
          (A * D) * (A * S) := by
    intro k hk
    apply (abs_standardQuadratic_oneStepEnergyDefect_sub_le ε
      (leapfrogN standardQuadraticGradient ε k (q₁, p))
      (leapfrogN standardQuadraticGradient ε k (q₂, p))).trans
    have hkn : k ≤ n := Nat.le_of_lt (Finset.mem_range.mp hk)
    have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
    have hkhorizon : (k : ℝ) * |ε| ≤ T :=
      (mul_le_mul_of_nonneg_right hknR (abs_nonneg ε)).trans horizon
    have hsep :=
      standardQuadratic_leapfrogN_sharedMomentum_phaseSeparation_le_exp
        hε k hkhorizon q₁ q₂ p
    have hsize₁ := standardQuadratic_leapfrogN_euclideanPhaseSize_le_exp
      hε k hkhorizon (q₁, p)
    have hsize₂ := standardQuadratic_leapfrogN_euclideanPhaseSize_le_exp
      hε k hkhorizon (q₂, p)
    have hsizes :
        euclideanPhaseSize
            (leapfrogN standardQuadraticGradient ε k (q₁, p)) +
          euclideanPhaseSize
            (leapfrogN standardQuadraticGradient ε k (q₂, p)) ≤ A * S := by
      dsimp [A, S]
      linarith
    have hcoeff : 0 ≤ (Fintype.card ι : ℝ) * 2 *
        standardQuadraticEnergyErrorRate ε := by positivity
    have hprod := mul_le_mul hsep hsizes
      (add_nonneg (euclideanPhaseSize_nonneg _) (euclideanPhaseSize_nonneg _))
      (mul_nonneg hA hD)
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hprod hcoeff
  apply le_trans (Finset.sum_le_sum hterm)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  dsimp [A, D, S]
  ring_nf
  exact le_rfl

/-- On a fixed integration horizon, the relative accumulated Gaussian energy
defect is `O(|ε|²)` times the initial position separation. -/
theorem abs_standardQuadratic_energy_leapfrogN_defect_sub_le_abs_sq
    {ε : ℝ} (hε : |ε| ≤ 1) (n : ℕ) {T : ℝ}
    (horizon : (n : ℝ) * |ε| ≤ T)
    (q₁ q₂ : Position ι) (p : Momentum ι) :
    |(energy standardQuadraticPotential
          (leapfrogN standardQuadraticGradient ε n (q₁, p)) -
        energy standardQuadraticPotential (q₁, p)) -
      (energy standardQuadraticPotential
          (leapfrogN standardQuadraticGradient ε n (q₂, p)) -
        energy standardQuadraticPotential (q₂, p))| ≤
      T * (Fintype.card ι : ℝ) * 2 * |ε| ^ 2 *
        (Real.exp ((13 / 4 : ℝ) * T) * euclideanNorm (q₁ - q₂)) *
        (Real.exp ((13 / 4 : ℝ) * T) *
          (euclideanPhaseSize (q₁, p) + euclideanPhaseSize (q₂, p))) := by
  apply (abs_standardQuadratic_energy_leapfrogN_defect_sub_le_of_horizon
    hε n horizon q₁ q₂ p).trans
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hrate := standardQuadraticEnergyErrorRate_le_abs_cube hε
  have hcoeff :
      (n : ℝ) * standardQuadraticEnergyErrorRate ε ≤ T * |ε| ^ 2 := by
    calc
      (n : ℝ) * standardQuadraticEnergyErrorRate ε ≤
          (n : ℝ) * |ε| ^ 3 :=
        mul_le_mul_of_nonneg_left hrate hn
      _ = ((n : ℝ) * |ε|) * |ε| ^ 2 := by ring
      _ ≤ T * |ε| ^ 2 :=
        mul_le_mul_of_nonneg_right horizon (sq_nonneg |ε|)
  have hcard : 0 ≤ (Fintype.card ι : ℝ) := by positivity
  have hsep : 0 ≤
      Real.exp ((13 / 4 : ℝ) * T) * euclideanNorm (q₁ - q₂) :=
    mul_nonneg (Real.exp_pos _).le (euclideanNorm_nonneg _)
  have hsize : 0 ≤ Real.exp ((13 / 4 : ℝ) * T) *
      (euclideanPhaseSize (q₁, p) + euclideanPhaseSize (q₂, p)) :=
    mul_nonneg (Real.exp_pos _).le
      (add_nonneg (euclideanPhaseSize_nonneg _) (euclideanPhaseSize_nonneg _))
  calc
    (n : ℝ) * (Fintype.card ι : ℝ) * 2 *
          standardQuadraticEnergyErrorRate ε *
          (Real.exp ((13 / 4 : ℝ) * T) * euclideanNorm (q₁ - q₂)) *
          (Real.exp ((13 / 4 : ℝ) * T) *
            (euclideanPhaseSize (q₁, p) + euclideanPhaseSize (q₂, p))) =
        ((n : ℝ) * standardQuadraticEnergyErrorRate ε) *
          (((Fintype.card ι : ℝ) * 2) *
            (Real.exp ((13 / 4 : ℝ) * T) * euclideanNorm (q₁ - q₂)) *
            (Real.exp ((13 / 4 : ℝ) * T) *
              (euclideanPhaseSize (q₁, p) + euclideanPhaseSize (q₂, p)))) := by
      ring
    _ ≤ (T * |ε| ^ 2) *
          (((Fintype.card ι : ℝ) * 2) *
            (Real.exp ((13 / 4 : ℝ) * T) * euclideanNorm (q₁ - q₂)) *
            (Real.exp ((13 / 4 : ℝ) * T) *
              (euclideanPhaseSize (q₁, p) + euclideanPhaseSize (q₂, p)))) := by
      apply mul_le_mul_of_nonneg_right hcoeff
      positivity
    _ = T * (Fintype.card ι : ℝ) * 2 * |ε| ^ 2 *
          (Real.exp ((13 / 4 : ℝ) * T) * euclideanNorm (q₁ - q₂)) *
          (Real.exp ((13 / 4 : ℝ) * T) *
            (euclideanPhaseSize (q₁, p) + euclideanPhaseSize (q₂, p))) := by
      ring

/-- The relative `O(|ε|²)` defect estimate also holds at every signed
trajectory offset. -/
theorem abs_standardQuadratic_energy_signedLeapfrog_defect_sub_le_abs_sq
    {ε : ℝ} (hε : |ε| ≤ 1) (k : ℤ) {T : ℝ}
    (horizon : (Int.natAbs k : ℝ) * |ε| ≤ T)
    (q₁ q₂ : Position ι) (p : Momentum ι) :
    |(energy standardQuadraticPotential
          (signedLeapfrog standardQuadraticGradient ε k (q₁, p)) -
        energy standardQuadraticPotential (q₁, p)) -
      (energy standardQuadraticPotential
          (signedLeapfrog standardQuadraticGradient ε k (q₂, p)) -
        energy standardQuadraticPotential (q₂, p))| ≤
      T * (Fintype.card ι : ℝ) * 2 * |ε| ^ 2 *
        (Real.exp ((13 / 4 : ℝ) * T) * euclideanNorm (q₁ - q₂)) *
        (Real.exp ((13 / 4 : ℝ) * T) *
          (euclideanPhaseSize (q₁, p) + euclideanPhaseSize (q₂, p))) := by
  cases k with
  | ofNat n =>
      change
        |(energy standardQuadraticPotential
              (leapfrogN standardQuadraticGradient ε n (q₁, p)) -
            energy standardQuadraticPotential (q₁, p)) -
          (energy standardQuadraticPotential
              (leapfrogN standardQuadraticGradient ε n (q₂, p)) -
            energy standardQuadraticPotential (q₂, p))| ≤ _
      exact abs_standardQuadratic_energy_leapfrogN_defect_sub_le_abs_sq
        hε n horizon q₁ q₂ p
  | negSucc n =>
      change
        |(energy standardQuadraticPotential
              (leapfrogN standardQuadraticGradient (-ε) (n + 1) (q₁, p)) -
            energy standardQuadraticPotential (q₁, p)) -
          (energy standardQuadraticPotential
              (leapfrogN standardQuadraticGradient (-ε) (n + 1) (q₂, p)) -
            energy standardQuadraticPotential (q₂, p))| ≤ _
      have hεneg : |-ε| ≤ 1 := by simpa only [abs_neg] using hε
      have hhorizon : ((n + 1 : ℕ) : ℝ) * |-ε| ≤ T := by
        simpa only [Int.natAbs_negSucc, abs_neg] using horizon
      simpa only [abs_neg] using
        abs_standardQuadratic_energy_leapfrogN_defect_sub_le_abs_sq
          hεneg (n + 1) hhorizon q₁ q₂ p

/-- Uniform relative centered-energy estimate over every index of a
length-`L + 1` standard-quadratic offset trajectory. -/
theorem abs_standardQuadratic_offsetLeapfrog_centeredDefect_sub_le_abs_sq
    {ε : ℝ} (hε : |ε| ≤ 1) {L : ℕ} (origin i : Fin (L + 1)) {T : ℝ}
    (horizon : (L : ℝ) * |ε| ≤ T)
    (q₁ q₂ : Position ι) (p : Momentum ι) :
    |(energy standardQuadraticPotential
          (offsetLeapfrogTrajectory standardQuadraticGradient ε origin
            (q₁, p) i) -
        energy standardQuadraticPotential (q₁, p)) -
      (energy standardQuadraticPotential
          (offsetLeapfrogTrajectory standardQuadraticGradient ε origin
            (q₂, p) i) -
        energy standardQuadraticPotential (q₂, p))| ≤
      T * (Fintype.card ι : ℝ) * 2 * |ε| ^ 2 *
        (Real.exp ((13 / 4 : ℝ) * T) * euclideanNorm (q₁ - q₂)) *
        (Real.exp ((13 / 4 : ℝ) * T) *
          (euclideanPhaseSize (q₁, p) + euclideanPhaseSize (q₂, p))) := by
  apply abs_standardQuadratic_energy_signedLeapfrog_defect_sub_le_abs_sq hε
  have hindex :
      Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) ≤ L := by omega
  have hcast :
      (Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) : ℝ) ≤ L := by
    exact_mod_cast hindex
  exact (mul_le_mul_of_nonneg_right hcast (abs_nonneg ε)).trans horizon

/-- Budget-facing form of the relative centered-energy estimate on the unit
integration horizon. A common bound on the two initial phase sizes leaves an
explicit coefficient multiplying only the initial position distance. -/
theorem abs_standardQuadratic_offsetLeapfrog_centeredDefect_sub_le_relative
    {ε : ℝ} (hε : |ε| ≤ 1) {L : ℕ} (origin i : Fin (L + 1))
    (horizon : (L : ℝ) * |ε| ≤ 1)
    (q₁ q₂ : Position ι) (p : Momentum ι) {M : ℝ}
    (hM : euclideanPhaseSize (q₁, p) +
      euclideanPhaseSize (q₂, p) ≤ M) :
    |(energy standardQuadraticPotential
          (offsetLeapfrogTrajectory standardQuadraticGradient ε origin
            (q₁, p) i) -
        energy standardQuadraticPotential (q₁, p)) -
      (energy standardQuadraticPotential
          (offsetLeapfrogTrajectory standardQuadraticGradient ε origin
            (q₂, p) i) -
        energy standardQuadraticPotential (q₂, p))| ≤
      ((Fintype.card ι : ℝ) * 2 * |ε| ^ 2 *
        Real.exp (13 / 2 : ℝ) * M) * euclideanNorm (q₁ - q₂) := by
  apply (abs_standardQuadratic_offsetLeapfrog_centeredDefect_sub_le_abs_sq
    hε origin i horizon q₁ q₂ p).trans
  have hM0 : 0 ≤ M :=
    (add_nonneg (euclideanPhaseSize_nonneg _) (euclideanPhaseSize_nonneg _)).trans hM
  have hprefix : 0 ≤
      1 * (Fintype.card ι : ℝ) * 2 * |ε| ^ 2 *
        (Real.exp ((13 / 4 : ℝ) * 1) * euclideanNorm (q₁ - q₂)) := by
    exact mul_nonneg (by positivity)
      (mul_nonneg (Real.exp_pos _).le (euclideanNorm_nonneg _))
  calc
    1 * (Fintype.card ι : ℝ) * 2 * |ε| ^ 2 *
          (Real.exp ((13 / 4 : ℝ) * 1) * euclideanNorm (q₁ - q₂)) *
          (Real.exp ((13 / 4 : ℝ) * 1) *
            (euclideanPhaseSize (q₁, p) + euclideanPhaseSize (q₂, p))) ≤
        1 * (Fintype.card ι : ℝ) * 2 * |ε| ^ 2 *
          (Real.exp ((13 / 4 : ℝ) * 1) * euclideanNorm (q₁ - q₂)) *
          (Real.exp ((13 / 4 : ℝ) * 1) * M) := by
      apply mul_le_mul_of_nonneg_left _ hprefix
      exact mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le
    _ = ((Fintype.card ι : ℝ) * 2 * |ε| ^ 2 *
          Real.exp (13 / 2 : ℝ) * M) * euclideanNorm (q₁ - q₂) := by
      have hexp : Real.exp (13 / 2 : ℝ) =
          Real.exp (13 / 4 : ℝ) * Real.exp (13 / 4 : ℝ) := by
        rw [← Real.exp_add]
        norm_num
      rw [hexp]
      ring_nf

/-- The standard quadratic target satisfies the compact-window relative
centered-energy property on the unit integration horizon. This validates the
new general mismatch interface on every compact position set and finite
kinetic-energy cutoff. -/
theorem standardQuadratic_uniformRelativeCenteredEnergyError
    {K : Set (Position ι)} (hK : IsCompact K)
    {k0 : ℝ} (hk0 : 0 ≤ k0) :
    UniformRelativeCenteredLeapfrogEnergyErrorOnCompactWindow
      standardQuadraticPotential standardQuadraticGradient K k0 1 := by
  obtain ⟨M, hM, hphase⟩ :=
    Mcmc.Hamiltonian.IsCompact.exists_euclideanPhaseSize_bound_of_kineticEnergy_le
      hK hk0
  intro energyRate henergyRate
  let A : ℝ := (Fintype.card ι : ℝ) * 2 *
    Real.exp (13 / 2 : ℝ) * (2 * M)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hden : 0 < A + 1 := by linarith
  let εbar := min 1 ((energyRate : ℝ) / (A + 1))
  have hεbar : 0 < εbar := by
    dsimp [εbar]
    exact lt_min zero_lt_one (div_pos (by exact_mod_cast henergyRate) hden)
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hεpos hε L horizon origin q₁ hq₁ q₂ hq₂ p hp i
  have hεone : |ε| ≤ 1 := by
    rw [abs_of_pos hεpos]
    exact hε.le.trans (min_le_left _ _)
  have hhor : (L : ℝ) * |ε| ≤ 1 := by
    rw [abs_of_pos hεpos]
    simpa only [mul_comm] using horizon
  have hsize : euclideanPhaseSize (q₁, p) +
      euclideanPhaseSize (q₂, p) ≤ 2 * M := by
    have h₁ := hphase q₁ hq₁ p hp
    have h₂ := hphase q₂ hq₂ p hp
    linarith
  apply (abs_standardQuadratic_offsetLeapfrog_centeredDefect_sub_le_relative
    hεone origin i hhor q₁ q₂ p hsize).trans
  have hsmall : ε < (energyRate : ℝ) / (A + 1) :=
    hε.trans_le (min_le_right _ _)
  have hproduct : ε * (A + 1) < (energyRate : ℝ) :=
    (lt_div_iff₀ hden).mp hsmall
  have hεle : ε ≤ 1 := hε.le.trans (min_le_left _ _)
  have hcoeff : A * ε ^ 2 ≤ (energyRate : ℝ) := by
    have hepsSq : ε ^ 2 ≤ ε := by nlinarith
    have hAe : A * ε ^ 2 ≤ A * ε :=
      mul_le_mul_of_nonneg_left hepsSq hA
    nlinarith
  have hnorm : 0 ≤ euclideanNorm (q₁ - q₂) := euclideanNorm_nonneg _
  rw [abs_of_pos hεpos]
  calc
    (Fintype.card ι : ℝ) * 2 * ε ^ 2 * Real.exp (13 / 2 : ℝ) *
          (2 * M) * euclideanNorm (q₁ - q₂) =
        A * ε ^ 2 * euclideanNorm (q₁ - q₂) := by
      dsimp [A]
      ring
    _ ≤ (energyRate : ℝ) * euclideanNorm (q₁ - q₂) :=
      mul_le_mul_of_nonneg_right hcoeff hnorm

/-- One standard-quadratic leapfrog step has energy defect bounded by the
explicit vanishing scalar rate times squared phase size. -/
theorem abs_standardQuadratic_energy_leapfrog_sub_le
    (ε : ℝ) (z : PhaseSpace ι) :
    |energy standardQuadraticPotential
          (leapfrog standardQuadraticGradient ε z) -
        energy standardQuadraticPotential z| ≤
      standardQuadraticEnergyErrorRate ε * euclideanPhaseSize z ^ 2 := by
  rw [standardQuadratic_energy_leapfrog_sub_eq]
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  apply le_trans (Finset.sum_le_sum fun i hi =>
    abs_standardQuadraticEnergyDefectTerm_le ε (z.1 i) (z.2 i))
  have hrate : 0 ≤ standardQuadraticEnergyErrorRate ε := by
    unfold standardQuadraticEnergyErrorRate
    positivity
  have hsquare :
      squaredEuclideanNorm z.1 + squaredEuclideanNorm z.2 ≤
        euclideanPhaseSize z ^ 2 := by
    rw [← euclideanNorm_sq, ← euclideanNorm_sq]
    unfold euclideanPhaseSize
    nlinarith [euclideanNorm_nonneg z.1, euclideanNorm_nonneg z.2]
  rw [show
      ∑ i, standardQuadraticEnergyErrorRate ε *
          (z.1 i ^ 2 + z.2 i ^ 2) =
        standardQuadraticEnergyErrorRate ε *
          (squaredEuclideanNorm z.1 + squaredEuclideanNorm z.2) by
      unfold squaredEuclideanNorm euclideanInner
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro i hi
        ring
      · apply Finset.sum_congr rfl
        intro i hi
        ring]
  exact mul_le_mul_of_nonneg_left hsquare hrate

/-- The explicit Gaussian cubic one-step defect instantiates the general
locally uniform quadratic numerical-error interface used by Proposition 4.2. -/
theorem locallyUniformQuadraticLeapfrogEnergyError_standardQuadratic :
    LocallyUniformQuadraticLeapfrogEnergyError
      (standardQuadraticPotential : Position ι → ℝ)
      standardQuadraticGradient := by
  intro R
  refine ⟨R ^ 2, sq_nonneg R, ?_⟩
  intro ε z hε hz
  apply (abs_standardQuadratic_energy_leapfrog_sub_le ε z).trans
  have hrate := standardQuadraticEnergyErrorRate_le_abs_cube hε
  have habs : 0 ≤ |ε| := abs_nonneg ε
  have hR : 0 ≤ R := (euclideanPhaseSize_nonneg z).trans hz
  have hsize : euclideanPhaseSize z ^ 2 ≤ R ^ 2 :=
    (sq_le_sq₀ (euclideanPhaseSize_nonneg z) hR).mpr hz
  have hcubic : |ε| ^ 3 ≤ |ε| ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg |ε|) (sub_nonneg.mpr hε)]
  calc
    standardQuadraticEnergyErrorRate ε * euclideanPhaseSize z ^ 2 ≤
        |ε| ^ 3 * euclideanPhaseSize z ^ 2 :=
      mul_le_mul_of_nonneg_right hrate (sq_nonneg _)
    _ ≤ |ε| ^ 3 * R ^ 2 :=
      mul_le_mul_of_nonneg_left hsize (pow_nonneg habs 3)
    _ ≤ R ^ 2 * |ε| ^ 2 := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hcubic (sq_nonneg R)

/-- Uniform accumulated energy error over the fixed-integration-time regime.
Unlike the earlier fixed-step-count limit, this estimate allows `n` to grow as
`ε` shrinks while `n |ε| ≤ T`. -/
theorem abs_standardQuadratic_energy_leapfrogN_sub_le_of_horizon
    {ε : ℝ} (hε : |ε| ≤ 1) (n : ℕ) {T : ℝ}
    (horizon : (n : ℝ) * |ε| ≤ T) (z : PhaseSpace ι) :
    |energy standardQuadraticPotential
          (leapfrogN standardQuadraticGradient ε n z) -
        energy standardQuadraticPotential z| ≤
      (n : ℝ) * standardQuadraticEnergyErrorRate ε *
        (Real.exp ((13 / 4 : ℝ) * T) * euclideanPhaseSize z) ^ 2 := by
  rw [energy_leapfrogN_sub_eq_sum_step_errors]
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  apply le_trans (Finset.sum_le_sum fun k hk =>
    abs_standardQuadratic_energy_leapfrog_sub_le ε
      (leapfrogN standardQuadraticGradient ε k z))
  have hrate : 0 ≤ standardQuadraticEnergyErrorRate ε := by
    unfold standardQuadraticEnergyErrorRate
    positivity
  have hR : 0 ≤ Real.exp ((13 / 4 : ℝ) * T) * euclideanPhaseSize z :=
    mul_nonneg (Real.exp_pos _).le (euclideanPhaseSize_nonneg z)
  have hterm : ∀ k ∈ Finset.range n,
      standardQuadraticEnergyErrorRate ε *
          euclideanPhaseSize
            (leapfrogN standardQuadraticGradient ε k z) ^ 2 ≤
        standardQuadraticEnergyErrorRate ε *
          (Real.exp ((13 / 4 : ℝ) * T) * euclideanPhaseSize z) ^ 2 := by
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt (Finset.mem_range.mp hk)
    have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
    have hkhorizon : (k : ℝ) * |ε| ≤ T :=
      (mul_le_mul_of_nonneg_right hknR (abs_nonneg ε)).trans horizon
    have hsize := standardQuadratic_leapfrogN_euclideanPhaseSize_le_exp
      hε k hkhorizon z
    have hsquare :
        euclideanPhaseSize
            (leapfrogN standardQuadraticGradient ε k z) ^ 2 ≤
          (Real.exp ((13 / 4 : ℝ) * T) * euclideanPhaseSize z) ^ 2 := by
      nlinarith [euclideanPhaseSize_nonneg
        (leapfrogN standardQuadraticGradient ε k z)]
    exact mul_le_mul_of_nonneg_left hsquare hrate
  apply le_trans (Finset.sum_le_sum hterm)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring_nf
  exact le_rfl

/-- The fixed-horizon Gaussian energy error is explicitly `O(|ε|²)`, uniformly
over every step count satisfying `n |ε| ≤ T`. -/
theorem abs_standardQuadratic_energy_leapfrogN_sub_le_abs_sq
    {ε : ℝ} (hε : |ε| ≤ 1) (n : ℕ) {T : ℝ}
    (horizon : (n : ℝ) * |ε| ≤ T) (z : PhaseSpace ι) :
    |energy standardQuadraticPotential
          (leapfrogN standardQuadraticGradient ε n z) -
        energy standardQuadraticPotential z| ≤
      T * |ε| ^ 2 *
        (Real.exp ((13 / 4 : ℝ) * T) * euclideanPhaseSize z) ^ 2 := by
  apply le_trans
    (abs_standardQuadratic_energy_leapfrogN_sub_le_of_horizon
      hε n horizon z)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have ha : 0 ≤ |ε| := abs_nonneg ε
  have hrate := standardQuadraticEnergyErrorRate_le_abs_cube hε
  have hcoeff :
      (n : ℝ) * standardQuadraticEnergyErrorRate ε ≤ T * |ε| ^ 2 := by
    calc
      (n : ℝ) * standardQuadraticEnergyErrorRate ε ≤
          (n : ℝ) * |ε| ^ 3 :=
        mul_le_mul_of_nonneg_left hrate hn
      _ = ((n : ℝ) * |ε|) * |ε| ^ 2 := by ring
      _ ≤ T * |ε| ^ 2 :=
        mul_le_mul_of_nonneg_right horizon (sq_nonneg |ε|)
  have hR2 : 0 ≤
      (Real.exp ((13 / 4 : ℝ) * T) * euclideanPhaseSize z) ^ 2 :=
    sq_nonneg _
  nlinarith

/-- The same fixed-horizon energy bound holds for signed leapfrog offsets;
negative offsets use the inverse step, equivalently step size `-ε`. -/
theorem abs_standardQuadratic_energy_signedLeapfrog_sub_le_abs_sq
    {ε : ℝ} (hε : |ε| ≤ 1) (k : ℤ) {T : ℝ}
    (horizon : (Int.natAbs k : ℝ) * |ε| ≤ T) (z : PhaseSpace ι) :
    |energy standardQuadraticPotential
          (signedLeapfrog standardQuadraticGradient ε k z) -
        energy standardQuadraticPotential z| ≤
      T * |ε| ^ 2 *
        (Real.exp ((13 / 4 : ℝ) * T) * euclideanPhaseSize z) ^ 2 := by
  cases k with
  | ofNat n =>
      exact abs_standardQuadratic_energy_leapfrogN_sub_le_abs_sq
        hε n horizon z
  | negSucc n =>
      change
        |energy standardQuadraticPotential
              (leapfrogN standardQuadraticGradient (-ε) (n + 1) z) -
            energy standardQuadraticPotential z| ≤ _
      have hεneg : |-ε| ≤ 1 := by simpa only [abs_neg] using hε
      have hhorizon : ((n + 1 : ℕ) : ℝ) * |-ε| ≤ T := by
        simpa only [Int.natAbs_negSucc, abs_neg] using horizon
      simpa only [abs_neg] using
        abs_standardQuadratic_energy_leapfrogN_sub_le_abs_sq
          hεneg (n + 1) hhorizon z

/-- Every point of an offset standard-quadratic trajectory obeys the common
fixed-horizon centered-energy error bound. -/
theorem abs_standardQuadratic_energy_offsetLeapfrogTrajectory_sub_le_abs_sq
    {ε : ℝ} (hε : |ε| ≤ 1) {L : ℕ}
    (origin i : Fin (L + 1)) {T : ℝ}
    (horizon : (L : ℝ) * |ε| ≤ T) (z : PhaseSpace ι) :
    |energy standardQuadraticPotential
          (offsetLeapfrogTrajectory standardQuadraticGradient ε origin z i) -
        energy standardQuadraticPotential z| ≤
      T * |ε| ^ 2 *
        (Real.exp ((13 / 4 : ℝ) * T) * euclideanPhaseSize z) ^ 2 := by
  apply abs_standardQuadratic_energy_signedLeapfrog_sub_le_abs_sq hε
  have hindex : Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) ≤ L := by
    omega
  have hindexR :
      (Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) : ℝ) ≤ L := by
    exact_mod_cast hindex
  exact (mul_le_mul_of_nonneg_right hindexR (abs_nonneg ε)).trans horizon

/-- Pointwise assembly of the sharp Gaussian maximal-coupling budget.  The
remaining hypotheses are scalar inequalities: a phase-size bound, a small
absolute energy radius, and enough rate allowance for the TV-weighted
off-diagonal contribution. -/
theorem standardQuadratic_sharpRelativeMomentOne_pointwise
    {Tmin ε : ℝ} (hTmin0 : 0 < Tmin) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {L : ℕ} (hTmin : Tmin ≤ ε * (L : ℝ))
    (hTmax : ε * (L : ℝ) ≤ 1) (origin : Fin (L + 1))
    (q₁ q₂ : Position ι) (p : Momentum ι) {M : ℝ}
    (hM : euclideanPhaseSize (q₁, p) +
      euclideanPhaseSize (q₂, p) ≤ M)
    (energyRate mismatchRate : NNReal)
    (henergySmall : ε ^ 2 *
      (Real.exp (13 / 4 : ℝ) * M) ^ 2 ≤ 1 / 2)
    (henergyRate :
      (Fintype.card ι : ℝ) * 2 * ε ^ 2 *
        Real.exp (13 / 2 : ℝ) * M ≤ energyRate)
    (hradiusSmall : energyRate * initialPositionDistance q₁ q₂ ≤ 1 / 2)
    (hmismatchRate :
      4 * energyRate *
        ⟨2 * (Real.exp (13 / 4 : ℝ) * M), by
          have hM0 : 0 ≤ M :=
            (add_nonneg (euclideanPhaseSize_nonneg _)
              (euclideanPhaseSize_nonneg _)).trans hM
          positivity⟩ ≤ mismatchRate) :
    ∃ mismatchBound : NNReal,
      (∑ i, min
          (trajectoryIndexPMF standardQuadraticPotential
            (offsetLeapfrogTrajectory standardQuadraticGradient ε origin
              (q₁, p)) i)
          (trajectoryIndexPMF standardQuadraticPotential
            (offsetLeapfrogTrajectory standardQuadraticGradient ε origin
              (q₂, p)) i) *
          (trajectoryPositionMomentCost standardQuadraticGradient 1 ε
            (((q₁, p), (q₂, p))) origin i i : ENNReal)) ≤
        (standardQuadraticAlignedRate Tmin (1 / 2) : ENNReal) *
          (initialPositionDistance q₁ q₂ : ENNReal) ∧
      (∀ i j, i ≠ j →
        trajectoryPositionMomentCost standardQuadraticGradient 1 ε
          (((q₁, p), (q₂, p))) origin i j ≤ mismatchBound) ∧
      Mcmc.Finite.totalVariation
          (trajectoryIndexPMF standardQuadraticPotential
            (offsetLeapfrogTrajectory standardQuadraticGradient ε origin
              (q₁, p)))
          (trajectoryIndexPMF standardQuadraticPotential
            (offsetLeapfrogTrajectory standardQuadraticGradient ε origin
              (q₂, p))) *
          (mismatchBound : ENNReal) ≤
        (mismatchRate : ENNReal) *
          (initialPositionDistance q₁ q₂ : ENNReal) := by
  have hεabs : |ε| ≤ 1 := by rw [abs_of_pos hε0]; exact hε1
  have hhorAbs : (L : ℝ) * |ε| ≤ 1 := by
    rw [abs_of_pos hε0]
    simpa only [mul_comm] using hTmax
  have hM0 : 0 ≤ M :=
    (add_nonneg (euclideanPhaseSize_nonneg _)
      (euclideanPhaseSize_nonneg _)).trans hM
  let mismatchBound : NNReal :=
    ⟨2 * (Real.exp (13 / 4 : ℝ) * M), by positivity⟩
  refine ⟨mismatchBound, ?_, ?_, ?_⟩
  · apply standardQuadratic_alignedOverlapMomentOne_le_rate
      ε origin q₁ q₂ p
      (energy standardQuadraticPotential (q₁, p))
      (energy standardQuadraticPotential (q₂, p)) (1 / 2)
      (fun i => ?_) (fun i => ?_) hε0.le hε1 hTmin0 hTmin hTmax
    · apply (abs_standardQuadratic_energy_offsetLeapfrogTrajectory_sub_le_abs_sq
        hεabs origin i hhorAbs (q₁, p)).trans
      have hqM : euclideanPhaseSize (q₁, p) ≤ M :=
        (le_add_of_nonneg_right (euclideanPhaseSize_nonneg (q₂, p))).trans hM
      have hsq :
          (Real.exp (13 / 4 : ℝ) * euclideanPhaseSize (q₁, p)) ^ 2 ≤
            (Real.exp (13 / 4 : ℝ) * M) ^ 2 := by
        apply (sq_le_sq₀
          (mul_nonneg (Real.exp_pos _).le (euclideanPhaseSize_nonneg _))
          (mul_nonneg (Real.exp_pos _).le hM0)).2
        exact mul_le_mul_of_nonneg_left hqM (Real.exp_pos _).le
      calc
        1 * |ε| ^ 2 *
            (Real.exp ((13 / 4 : ℝ) * 1) * euclideanPhaseSize (q₁, p)) ^ 2 =
          ε ^ 2 * (Real.exp (13 / 4 : ℝ) *
            euclideanPhaseSize (q₁, p)) ^ 2 := by
            rw [abs_of_pos hε0]
            ring_nf
        _ ≤ ε ^ 2 * (Real.exp (13 / 4 : ℝ) * M) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (sq_nonneg ε)
        _ ≤ 1 / 2 := henergySmall
    · apply (abs_standardQuadratic_energy_offsetLeapfrogTrajectory_sub_le_abs_sq
        hεabs origin i hhorAbs (q₂, p)).trans
      have hqM : euclideanPhaseSize (q₂, p) ≤ M :=
        (le_add_of_nonneg_left (euclideanPhaseSize_nonneg (q₁, p))).trans hM
      have hsq :
          (Real.exp (13 / 4 : ℝ) * euclideanPhaseSize (q₂, p)) ^ 2 ≤
            (Real.exp (13 / 4 : ℝ) * M) ^ 2 := by
        apply (sq_le_sq₀
          (mul_nonneg (Real.exp_pos _).le (euclideanPhaseSize_nonneg _))
          (mul_nonneg (Real.exp_pos _).le hM0)).2
        exact mul_le_mul_of_nonneg_left hqM (Real.exp_pos _).le
      calc
        1 * |ε| ^ 2 *
            (Real.exp ((13 / 4 : ℝ) * 1) * euclideanPhaseSize (q₂, p)) ^ 2 =
          ε ^ 2 * (Real.exp (13 / 4 : ℝ) *
            euclideanPhaseSize (q₂, p)) ^ 2 := by
            rw [abs_of_pos hε0]
            ring_nf
        _ ≤ ε ^ 2 * (Real.exp (13 / 4 : ℝ) * M) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (sq_nonneg ε)
        _ ≤ 1 / 2 := henergySmall
  · intro i j hij
    dsimp [mismatchBound]
    apply trajectoryPositionMomentCost_one_le_of_positionNorm_le
      standardQuadraticGradient ε (((q₁, p), (q₂, p))) origin
      (R := Real.exp (13 / 4 : ℝ) * M) (by positivity)
    · intro k
      apply (euclideanNorm_fst_le_phaseSize _).trans
      have hphase :=
        standardQuadratic_offsetLeapfrogTrajectory_euclideanPhaseSize_le_exp
          hεabs origin k hhorAbs (q₁, p)
      norm_num at hphase
      have hqM : euclideanPhaseSize (q₁, p) ≤ M :=
        (le_add_of_nonneg_right (euclideanPhaseSize_nonneg (q₂, p))).trans hM
      exact hphase.trans
        (mul_le_mul_of_nonneg_left hqM (Real.exp_pos _).le)
    · intro k
      apply (euclideanNorm_fst_le_phaseSize _).trans
      have hphase :=
        standardQuadratic_offsetLeapfrogTrajectory_euclideanPhaseSize_le_exp
          hεabs origin k hhorAbs (q₂, p)
      norm_num at hphase
      have hqM : euclideanPhaseSize (q₂, p) ≤ M :=
        (le_add_of_nonneg_left (euclideanPhaseSize_nonneg (q₁, p))).trans hM
      exact hphase.trans
        (mul_le_mul_of_nonneg_left hqM (Real.exp_pos _).le)
  · let radius := energyRate * initialPositionDistance q₁ q₂
    apply trajectoryIndexPMF_totalVariation_mul_le_of_relative_centeredEnergy
      standardQuadraticPotential standardQuadraticGradient ε
      (((q₁, p), (q₂, p))) origin q₁ q₂
      (energy standardQuadraticPotential (q₁, p))
      (energy standardQuadraticPotential (q₂, p))
      radius energyRate mismatchBound mismatchRate
    · exact_mod_cast hradiusSmall
    · intro i
      apply (abs_standardQuadratic_offsetLeapfrog_centeredDefect_sub_le_relative
        hεabs origin i hhorAbs q₁ q₂ p hM).trans
      change _ ≤ ((radius : NNReal) : ℝ)
      dsimp [radius]
      rw [abs_of_pos hε0]
      change _ ≤ (energyRate : ℝ) * euclideanNorm (q₁ - q₂)
      exact mul_le_mul_of_nonneg_right henergyRate (euclideanNorm_nonneg _)
    · exact le_rfl
    · simpa only [mismatchBound] using hmismatchRate

/-- The standard Gaussian aligned overlap estimate has the cutoff-uniform
quantifier order required by the repaired Condition 1 interface.  Momentum
cutoffs affect only the admissible step-size threshold, not the integration
window or aligned rate. -/
theorem standardQuadratic_uniformOverlapWeightedMomentOneContraction
    {r Tmin : ℝ} (hr : 0 < r) (hTmin0 : 0 < Tmin)
    (hTminOne : Tmin ≤ 1) :
    UniformOverlapWeightedMomentOneContractionOnIntegrationWindow
      (standardQuadraticPotential (ι := ι))
      (standardQuadraticGradient (ι := ι))
      (Metric.closedBall (0 : Position ι) r) Tmin 1
      (standardQuadraticAlignedRate Tmin (1 / 2)) := by
  refine ⟨hTmin0, hTminOne,
    standardQuadraticAlignedRate_lt_one hTmin0 hTminOne, ?_⟩
  intro k0 hk0
  let Q := ((Fintype.card ι : ℝ) + 1) * r
  let P := Real.sqrt (2 * k0)
  let M := Q + P
  let A := (Real.exp (13 / 4 : ℝ) * M) ^ 2
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hP : 0 ≤ P := Real.sqrt_nonneg _
  have hM : 0 ≤ M := add_nonneg hQ hP
  have hA : 0 ≤ A := sq_nonneg _
  obtain ⟨εbar, hεbar, hthreshold⟩ :=
    exists_pos_stepSize_threshold_three (B := 0) (C := 0)
      hA (by norm_num) (by norm_num)
      (by norm_num : (0 : ℝ) < 1)
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hεpos hε L hwindowMin hwindowMax origin
    q₁ hq₁ q₂ hq₂ p hp
  obtain ⟨hε1, henergySmall, _, _⟩ := hthreshold ε hεpos hε
  have hq₁norm : euclideanNorm q₁ ≤ Q :=
    euclideanNorm_le_card_succ_mul_of_mem_closedBall hq₁
  have hq₂norm : euclideanNorm q₂ ≤ Q :=
    euclideanNorm_le_card_succ_mul_of_mem_closedBall hq₂
  have hpnorm : euclideanNorm p ≤ P :=
    euclideanNorm_le_sqrt_two_mul_of_kineticEnergy_le hk0.le hp
  have hphase₁ : euclideanPhaseSize (q₁, p) ≤ M := by
    dsimp [M, euclideanPhaseSize]
    linarith
  have hphase₂ : euclideanPhaseSize (q₂, p) ≤ M := by
    dsimp [M, euclideanPhaseSize]
    linarith
  have hεabs : |ε| ≤ 1 := by
    rw [abs_of_pos hεpos]
    exact hε1
  have hhorAbs : (L : ℝ) * |ε| ≤ 1 := by
    rw [abs_of_pos hεpos]
    simpa only [mul_comm] using hwindowMax
  apply standardQuadratic_alignedOverlapMomentOne_le_rate
    ε origin q₁ q₂ p
    (energy standardQuadraticPotential (q₁, p))
    (energy standardQuadraticPotential (q₂, p)) (1 / 2)
    (fun i => ?_) (fun i => ?_) hεpos.le hε1 hTmin0
    hwindowMin hwindowMax
  · apply (abs_standardQuadratic_energy_offsetLeapfrogTrajectory_sub_le_abs_sq
      hεabs origin i hhorAbs (q₁, p)).trans
    have hsq :
        (Real.exp (13 / 4 : ℝ) * euclideanPhaseSize (q₁, p)) ^ 2 ≤ A := by
      dsimp [A]
      apply (sq_le_sq₀
        (mul_nonneg (Real.exp_pos _).le (euclideanPhaseSize_nonneg _))
        (mul_nonneg (Real.exp_pos _).le hM)).2
      exact mul_le_mul_of_nonneg_left hphase₁ (Real.exp_pos _).le
    calc
      1 * |ε| ^ 2 *
          (Real.exp ((13 / 4 : ℝ) * 1) *
            euclideanPhaseSize (q₁, p)) ^ 2 ≤ ε ^ 2 * A := by
        rw [abs_of_pos hεpos]
        norm_num
        exact mul_le_mul_of_nonneg_left hsq (sq_nonneg ε)
      _ ≤ 1 / 2 := by simpa only [A] using henergySmall
  · apply (abs_standardQuadratic_energy_offsetLeapfrogTrajectory_sub_le_abs_sq
      hεabs origin i hhorAbs (q₂, p)).trans
    have hsq :
        (Real.exp (13 / 4 : ℝ) * euclideanPhaseSize (q₂, p)) ^ 2 ≤ A := by
      dsimp [A]
      apply (sq_le_sq₀
        (mul_nonneg (Real.exp_pos _).le (euclideanPhaseSize_nonneg _))
        (mul_nonneg (Real.exp_pos _).le hM)).2
      exact mul_le_mul_of_nonneg_left hphase₂ (Real.exp_pos _).le
    calc
      1 * |ε| ^ 2 *
          (Real.exp ((13 / 4 : ℝ) * 1) *
            euclideanPhaseSize (q₂, p)) ^ 2 ≤ ε ^ 2 * A := by
        rw [abs_of_pos hεpos]
        norm_num
        exact mul_le_mul_of_nonneg_left hsq (sq_nonneg ε)
      _ ≤ 1 / 2 := by simpa only [A] using henergySmall

/-- End-to-end Gaussian repaired Condition 1 through the generic analytic
architecture: the independently proved cutoff-uniform aligned certificate is
combined with the independently proved signed relative energy-error theorem. -/
theorem standardQuadratic_exists_maximalCondition_via_signedEnergyError
    {r Tmin : ℝ} (hr : 0 < r) (hTmin0 : 0 < Tmin)
    (hTminOne : Tmin ≤ 1) :
    ∃ mismatchRate : NNReal, 0 < mismatchRate ∧
      standardQuadraticAlignedRate Tmin (1 / 2) + mismatchRate < 1 ∧
      XuCondition1OnIntegrationWindow
        (maximalTrajectoryIndexCouplingFamily
          (standardQuadraticPotential (ι := ι))
          (standardQuadraticGradient (ι := ι)))
        (standardQuadraticGradient (ι := ι))
        (Metric.closedBall (0 : Position ι) r)
        (standardQuadraticAlignedRate Tmin (1 / 2) + mismatchRate) :=
  (standardQuadratic_uniformOverlapWeightedMomentOneContraction
      hr hTmin0 hTminOne).exists_maximalCondition_of_signedEnergyError
    regularPotential_standardQuadratic (isCompact_closedBall 0 r)
    standardQuadratic_locallyUniformLinearRelativeCenteredSignedEnergyError

/-- The standard Gaussian target on any positive closed ball instantiates the
sharp positive-integration-window maximal-coupling budget.  The aligned rate
is the explicit overlap-band rate; the remaining half of its gap to one is
reserved for multinomial-index mismatch. -/
theorem standardQuadratic_exists_sharpRelativeMomentOneMaximalBudget
    {r Tmin : ℝ} (hr : 0 < r) (hTmin0 : 0 < Tmin)
    (hTminOne : Tmin ≤ 1) :
    ∃ mismatchRate : NNReal,
      0 < mismatchRate ∧
      standardQuadraticAlignedRate Tmin (1 / 2) + mismatchRate < 1 ∧
      XuSharpRelativeMomentOneMaximalBudgetOnIntegrationWindow
        standardQuadraticPotential standardQuadraticGradient
        (Metric.closedBall (0 : Position ι) r) Tmin 1
        (standardQuadraticAlignedRate Tmin (1 / 2)) mismatchRate := by
  let alignedRate := standardQuadraticAlignedRate Tmin (1 / 2)
  have halignedLt : alignedRate < 1 :=
    standardQuadraticAlignedRate_lt_one hTmin0 hTminOne
  let mismatchRate : NNReal := (1 - alignedRate) / 2
  have hmismatchPos : 0 < mismatchRate := by
    dsimp [mismatchRate]
    exact div_pos (tsub_pos_iff_lt.mpr halignedLt) (by norm_num)
  have hrates : alignedRate + mismatchRate < 1 := by
    have hcancel : alignedRate + (1 - alignedRate) = 1 :=
      add_tsub_cancel_of_le halignedLt.le
    dsimp [mismatchRate]
    calc
      alignedRate + (1 - alignedRate) / 2 <
          alignedRate + (1 - alignedRate) := by
        simpa only [add_comm] using add_lt_add_left
          (div_lt_self (tsub_pos_iff_lt.mpr halignedLt)
            (by norm_num : (1 : NNReal) < 2)) alignedRate
      _ = 1 := hcancel
  refine ⟨mismatchRate, hmismatchPos,
    by simpa only [alignedRate] using hrates,
    hTmin0, hTminOne, ?_⟩
  intro k0 hk0
  let Q := ((Fintype.card ι : ℝ) + 1) * r
  let P := Real.sqrt (2 * k0)
  let M := 2 * (Q + P)
  let energyCoefficient :=
    (Fintype.card ι : ℝ) * 2 * Real.exp (13 / 2 : ℝ) * M
  let mismatchBound := 2 * (Real.exp (13 / 4 : ℝ) * M)
  let distanceBound := 2 * Q
  let A := (Real.exp (13 / 4 : ℝ) * M) ^ 2
  let B := energyCoefficient * distanceBound
  let C := 4 * energyCoefficient * mismatchBound
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hP : 0 ≤ P := Real.sqrt_nonneg _
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have henergyCoefficient : 0 ≤ energyCoefficient := by
    dsimp [energyCoefficient]
    positivity
  have hmismatchBound : 0 ≤ mismatchBound := by
    dsimp [mismatchBound]
    positivity
  have hdistanceBound : 0 ≤ distanceBound := by
    dsimp [distanceBound]
    positivity
  have hA : 0 ≤ A := sq_nonneg _
  have hB : 0 ≤ B := mul_nonneg henergyCoefficient hdistanceBound
  have hC : 0 ≤ C := by dsimp [C]; positivity
  rcases exists_pos_stepSize_threshold_three hA hB hC
      (show 0 < (mismatchRate : ℝ) by exact_mod_cast hmismatchPos) with
    ⟨εbar, hεbar, hthreshold⟩
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hε0 hε L hwindowMin hwindowMax origin
    q₁ hq₁ q₂ hq₂ p hp
  rcases hthreshold ε hε0 hε with
    ⟨hε1, henergySmall, hradiusBudget, hmismatchBudget⟩
  have hq₁norm : euclideanNorm q₁ ≤ Q := by
    exact euclideanNorm_le_card_succ_mul_of_mem_closedBall hq₁
  have hq₂norm : euclideanNorm q₂ ≤ Q := by
    exact euclideanNorm_le_card_succ_mul_of_mem_closedBall hq₂
  have hpnorm : euclideanNorm p ≤ P := by
    exact euclideanNorm_le_sqrt_two_mul_of_kineticEnergy_le hk0.le hp
  have hphase :
      euclideanPhaseSize (q₁, p) + euclideanPhaseSize (q₂, p) ≤ M := by
    dsimp [M, euclideanPhaseSize]
    linarith
  have hdistance : euclideanNorm (q₁ - q₂) ≤ distanceBound := by
    apply (euclideanNorm_sub_le q₁ q₂).trans
    dsimp [distanceBound]
    linarith
  let energyRate : NNReal :=
    ⟨energyCoefficient * ε ^ 2, mul_nonneg henergyCoefficient (sq_nonneg ε)⟩
  apply standardQuadratic_sharpRelativeMomentOne_pointwise
    hTmin0 hε0 hε1 hwindowMin hwindowMax origin q₁ q₂ p
    hphase energyRate mismatchRate
  · simpa only [A] using henergySmall
  · dsimp [energyRate, energyCoefficient]
    norm_num
    ring_nf
    exact le_rfl
  · apply NNReal.coe_le_coe.mp
    change (energyCoefficient * ε ^ 2) * euclideanNorm (q₁ - q₂) ≤ 1 / 2
    apply le_trans
      (mul_le_mul_of_nonneg_left hdistance
        (mul_nonneg henergyCoefficient (sq_nonneg ε)))
    dsimp [B] at hradiusBudget
    nlinarith
  · apply NNReal.coe_le_coe.mp
    change 4 * (energyCoefficient * ε ^ 2) *
        (2 * (Real.exp (13 / 4 : ℝ) * M)) ≤ (mismatchRate : ℝ)
    dsimp [C, mismatchBound] at hmismatchBudget
    nlinarith

/-- End-to-end Gaussian specialization of the repaired positive-window
Condition 1 for the paper's maximal multinomial-index coupling. -/
theorem standardQuadratic_exists_maximal_xuCondition1OnIntegrationWindow
    {r Tmin : ℝ} (hr : 0 < r) (hTmin0 : 0 < Tmin)
    (hTminOne : Tmin ≤ 1) :
    ∃ rate : NNReal, rate < 1 ∧
      XuCondition1OnIntegrationWindow
        (maximalTrajectoryIndexCouplingFamily
          standardQuadraticPotential standardQuadraticGradient)
        standardQuadraticGradient
        (Metric.closedBall (0 : Position ι) r) rate := by
  rcases standardQuadratic_exists_sharpRelativeMomentOneMaximalBudget
      (ι := ι) hr hTmin0 hTminOne with
    ⟨mismatchRate, hmismatchPos, hrates, hbudget⟩
  let rate := standardQuadraticAlignedRate Tmin (1 / 2) + mismatchRate
  refine ⟨rate, by simpa only [rate] using hrates, ?_⟩
  have hratePos : 0 < rate := by
    dsimp [rate]
    exact hmismatchPos.trans_le (le_add_left le_rfl)
  exact (hbudget.maximalCondition
      standardQuadraticPotential standardQuadraticGradient
      (Metric.closedBall (0 : Position ι) r) Tmin 1).xuCondition1OnIntegrationWindow
    hratePos (by simpa only [rate] using hrates)

/-- Kernel-level form of the Gaussian result: conditional on any shared
momentum below a prescribed kinetic cutoff, the actual randomized-origin
maximal coupled trajectory kernel contracts expected Euclidean position
distance at one common subunit rate. -/
theorem standardQuadratic_exists_maximalCoupledRandomized_expectedDistance
    {r Tmin : ℝ} (hr : 0 < r) (hTmin0 : 0 < Tmin)
    (hTminOne : Tmin ≤ 1) :
    ∃ rate : NNReal, rate < 1 ∧
      ∀ k0 : ℝ, 0 < k0 →
        ∃ εbar : ℝ, 0 < εbar ∧
          ∀ ε : ℝ, 0 < ε → ε < εbar →
            ∀ L : ℕ, Tmin ≤ ε * (L : ℝ) → ε * (L : ℝ) ≤ 1 →
              ∀ q₁ ∈ Metric.closedBall (0 : Position ι) r,
                ∀ q₂ ∈ Metric.closedBall (0 : Position ι) r,
                  ∀ p : Momentum ι, kineticEnergy p ≤ k0 →
                    (∫⁻ y, ENNReal.ofReal
                        (euclideanNorm (y.1.1 - y.2.1))
                      ∂maximalCoupledRandomizedMultinomialLeapfrogKernel
                        standardQuadraticPotential standardQuadraticGradient
                        ε L
                        contDiff_standardQuadraticPotential.continuous.measurable
                        measurable_standardQuadraticGradient
                        (((q₁, p), (q₂, p)))) ≤
                      (rate : ENNReal) *
                        ENNReal.ofReal (euclideanNorm (q₁ - q₂)) := by
  rcases standardQuadratic_exists_sharpRelativeMomentOneMaximalBudget
      (ι := ι) hr hTmin0 hTminOne with
    ⟨mismatchRate, hmismatchPos, hrates, hbudget⟩
  let rate := standardQuadraticAlignedRate Tmin (1 / 2) + mismatchRate
  refine ⟨rate, by simpa only [rate] using hrates, ?_⟩
  have hcondition := hbudget.maximalCondition
    standardQuadraticPotential standardQuadraticGradient
    (Metric.closedBall (0 : Position ι) r) Tmin 1
  exact hcondition.maximalCoupledRandomizedMultinomialLeapfrogKernel_expectedDistance
    standardQuadraticPotential standardQuadraticGradient
    (Metric.closedBall (0 : Position ι) r) rate Tmin 1
    contDiff_standardQuadraticPotential.continuous.measurable
    measurable_standardQuadraticGradient

/-- The complete shared-momentum maximal Gaussian HMC kernel has a uniform
positive chance of entering one relaxed Euclidean diagonal from every pair of
positions in a fixed positive-radius ball. This integrates the conditional
contraction over a positive-mass kinetic-energy cutoff. -/
theorem standardQuadratic_maximalSharedMomentum_uniform_relaxedEntry
    {r Tmin : ℝ} (hr : 0 < r) (hTmin0 : 0 < Tmin)
    (hTminOne : Tmin ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ entry : ENNReal, 0 < entry ∧
      ∃ εbar : ℝ, 0 < εbar ∧
        ∀ ε : ℝ, 0 < ε → ε < εbar →
          ∀ L : ℕ, Tmin ≤ ε * (L : ℝ) → ε * (L : ℝ) ≤ 1 →
            ∀ q₁ ∈ Metric.closedBall (0 : Position ι) r,
              ∀ q₂ ∈ Metric.closedBall (0 : Position ι) r,
                entry ≤
                  maximalSharedMomentumCoupledPositionMultinomialHMC
                    standardQuadraticPotential standardQuadraticGradient ε L
                    contDiff_standardQuadraticPotential.continuous.measurable
                    measurable_standardQuadraticGradient
                    (q₁, q₂) (positionEuclideanRelaxedDiagonal δ) := by
  rcases standardQuadratic_exists_maximalCoupledRandomized_expectedDistance
      (ι := ι) hr hTmin0 hTminOne with ⟨rate, hrate, hcontract⟩
  rcases hcontract 1 (by norm_num) with ⟨εbar, hεbar, hbound⟩
  let Q := ((Fintype.card ι : ℝ) + 1) * r
  let D := 2 * Q
  let δ := 2 * D
  let cutoff : Set (Momentum ι) := {p | kineticEnergy p ≤ 1}
  let mass := standardMomentumMeasure (ι := ι) cutoff
  let entry := mass * (1 / 2 : ENNReal)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hcutoff : MeasurableSet cutoff := by
    dsimp [cutoff]
    exact measurable_kineticEnergy measurableSet_Iic
  have hmass : 0 < mass := by
    dsimp [mass, cutoff]
    exact standardMomentumMeasure_kineticEnergy_le_pos (by norm_num)
  have hentry : 0 < entry := by
    dsimp [entry]
    exact ENNReal.mul_pos hmass.ne' (by norm_num)
  refine ⟨δ, hδ, entry, hentry, εbar, hεbar, ?_⟩
  intro ε hε0 hε L hTmin hTmax q₁ hq₁ q₂ hq₂
  dsimp [entry, mass]
  unfold maximalSharedMomentumCoupledPositionMultinomialHMC
  apply coupledPositionMultinomialHMC_positionRelaxedDiagonal_ge_of_sharedMomentum
    (coupledTrajectory :=
      maximalCoupledRandomizedMultinomialLeapfrogKernel
        standardQuadraticPotential standardQuadraticGradient ε L
        contDiff_standardQuadraticPotential.continuous.measurable
        measurable_standardQuadraticGradient)
    (momentumTarget := standardMomentumMeasure)
    (q := (q₁, q₂)) (cutoff := cutoff) hcutoff (δ := δ)
    (c := (1 / 2 : ENNReal))
  intro p hp
  have hpEnergy : kineticEnergy p ≤ 1 := hp
  have hq₁norm : euclideanNorm q₁ ≤ Q :=
    euclideanNorm_le_card_succ_mul_of_mem_closedBall hq₁
  have hq₂norm : euclideanNorm q₂ ≤ Q :=
    euclideanNorm_le_card_succ_mul_of_mem_closedBall hq₂
  have hdist : euclideanNorm (q₁ - q₂) ≤ D := by
    apply (euclideanNorm_sub_le q₁ q₂).trans
    dsimp [D]
    linarith
  have hexpect := hbound ε hε0 hε L hTmin hTmax
    q₁ hq₁ q₂ hq₂ p hpEnergy
  have hexpectD :
      (∫⁻ y, ENNReal.ofReal (euclideanNorm (y.1.1 - y.2.1))
        ∂maximalCoupledRandomizedMultinomialLeapfrogKernel
          standardQuadraticPotential standardQuadraticGradient ε L
          contDiff_standardQuadraticPotential.continuous.measurable
          measurable_standardQuadraticGradient (((q₁, p), (q₂, p)))) ≤
        ENNReal.ofReal D := by
    apply hexpect.trans
    calc
      (rate : ENNReal) * ENNReal.ofReal (euclideanNorm (q₁ - q₂)) ≤
          ENNReal.ofReal (euclideanNorm (q₁ - q₂)) := by
        exact mul_le_of_le_one_left (by positivity)
          (ENNReal.coe_le_coe.mpr hrate.le)
      _ ≤ ENNReal.ofReal D := ENNReal.ofReal_le_ofReal hdist
  have hhalf : (1 / 2 : ENNReal) ≤
      1 - ENNReal.ofReal D / ENNReal.ofReal δ := by
    have hδeq : ENNReal.ofReal δ =
        2 * ENNReal.ofReal D := by
      dsimp [δ]
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hD0 : ENNReal.ofReal D ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr hD
    have hDtop : ENNReal.ofReal D ≠ ⊤ := ENNReal.ofReal_ne_top
    have hden0 : (2 : ENNReal) * ENNReal.ofReal D ≠ 0 :=
      mul_ne_zero (by norm_num) hD0
    have hdenTop : (2 : ENNReal) * ENNReal.ofReal D ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) hDtop
    have hratio : ENNReal.ofReal D /
        (2 * ENNReal.ofReal D) = (1 / 2 : ENNReal) := by
      symm
      apply (ENNReal.eq_div_iff hden0 hdenTop).2
      simpa only [one_div, mul_comm] using
        (ENNReal.mul_inv_cancel_right
          (a := ENNReal.ofReal D) (b := (2 : ENNReal))
          (by norm_num) (by norm_num))
    rw [hδeq, hratio]
    norm_num
  apply hhalf.trans
  apply measure_phasePositionRelaxedDiagonal_ge_of_lintegral_le
    _ _ hexpectD hδ

/-- Kernel-interface form of
`standardQuadratic_maximalSharedMomentum_uniform_relaxedEntry`: on every
positive-radius position ball, the full shared-momentum maximal Gaussian HMC
coupling reaches the ambient-metric relaxed diagonal in one step with a
uniform positive probability. -/
theorem standardQuadratic_maximalSharedMomentum_isRelaxedMeetingAccessible
    {r Tmin : ℝ} (hr : 0 < r) (hTmin0 : 0 < Tmin)
    (hTminOne : Tmin ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ entry : ENNReal, 0 < entry ∧
      ∃ εbar : ℝ, 0 < εbar ∧
        ∀ ε : ℝ, 0 < ε → ε < εbar →
          ∀ L : ℕ, Tmin ≤ ε * (L : ℝ) → ε * (L : ℝ) ≤ 1 →
            Mcmc.Kernel.IsRelaxedMeetingAccessibleFrom
              (maximalSharedMomentumCoupledPositionMultinomialHMC
                standardQuadraticPotential standardQuadraticGradient ε L
                contDiff_standardQuadraticPotential.continuous.measurable
                measurable_standardQuadraticGradient)
              (Metric.closedBall (0 : Position ι) r) δ 1 entry := by
  rcases standardQuadratic_maximalSharedMomentum_uniform_relaxedEntry
      (ι := ι) hr hTmin0 hTminOne with
    ⟨δ, hδ, entry, hentry, εbar, hεbar, hbound⟩
  refine ⟨δ, hδ, entry, hentry, εbar, hεbar, ?_⟩
  intro ε hε0 hε L hTmin hTmax
  unfold Mcmc.Kernel.IsRelaxedMeetingAccessibleFrom
    Mcmc.Kernel.IsUniformlyAccessibleFrom
  intro q hq
  rw [pow_one]
  apply (hbound ε hε0 hε L hTmin hTmax
    q.1 hq.1 q.2 hq.2).trans
  apply measure_mono
  intro y hy
  have hy' : euclideanNorm (y.1 - y.2) < δ := by
    simpa only [positionEuclideanRelaxedDiagonal, Set.mem_setOf_eq] using hy
  exact (dist_le_euclideanNorm_sub y.1 y.2).trans hy'.le

/-- Path-law consequence of the Gaussian relaxed-accessibility theorem. When
the paired Markov state is read as `(Xₙ,Yₙ₋₁)`, every deterministic start in
the position ball has relaxed meeting failure probability at most
`1 - entry` after one coupled HMC step. -/
theorem standardQuadratic_maximalSharedMomentum_relaxedPairMeetingTail_le
    {r Tmin : ℝ} (hr : 0 < r) (hTmin0 : 0 < Tmin)
    (hTminOne : Tmin ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ entry : ENNReal, 0 < entry ∧
      ∃ εbar : ℝ, 0 < εbar ∧
        ∀ ε : ℝ, 0 < ε → ε < εbar →
          ∀ L : ℕ, Tmin ≤ ε * (L : ℝ) → ε * (L : ℝ) ≤ 1 →
            ∀ q ∈ Metric.closedBall (0 : Position ι) r ×ˢ
                Metric.closedBall (0 : Position ι) r,
              Mcmc.Kernel.relaxedPairMeetingTail
                (Mcmc.Kernel.pathLaw (Measure.dirac q)
                  (maximalSharedMomentumCoupledPositionMultinomialHMC
                    standardQuadraticPotential standardQuadraticGradient ε L
                    contDiff_standardQuadraticPotential.continuous.measurable
                    measurable_standardQuadraticGradient)) δ 1 ≤
                1 - entry := by
  rcases standardQuadratic_maximalSharedMomentum_isRelaxedMeetingAccessible
      (ι := ι) hr hTmin0 hTminOne with
    ⟨δ, hδ, entry, hentry, εbar, hεbar, haccess⟩
  refine ⟨δ, hδ, entry, hentry, εbar, hεbar, ?_⟩
  intro ε hε0 hε L hTmin hTmax q hq
  exact (haccess ε hε0 hε L hTmin hTmax).relaxedPairMeetingTail_pathLaw_le
    _ hq

/-- Uniform fixed-integration-time convergence for the standard Gaussian:
the number of leapfrog steps may vary arbitrarily with `ε`, provided the total
horizon remains bounded by `T`. -/
theorem standardQuadratic_energy_leapfrogN_variableSteps_tendsto_zero
    (steps : ℝ → ℕ) {T : ℝ} (z : PhaseSpace ι)
    (horizon : ∀ᶠ ε in nhds 0, (steps ε : ℝ) * |ε| ≤ T) :
    Filter.Tendsto
      (fun ε : ℝ =>
        |energy standardQuadraticPotential
              (leapfrogN standardQuadraticGradient ε (steps ε) z) -
          energy standardQuadraticPotential z|)
      (nhds 0) (nhds 0) := by
  let C := T *
    (Real.exp ((13 / 4 : ℝ) * T) * euclideanPhaseSize z) ^ 2
  have hupper : Filter.Tendsto (fun ε : ℝ => C * |ε| ^ 2)
      (nhds 0) (nhds 0) := by
    have hc : Continuous fun ε : ℝ => C * |ε| ^ 2 := by fun_prop
    have hc0 : ContinuousAt (fun ε : ℝ => C * |ε| ^ 2) 0 :=
      hc.continuousAt
    simpa using hc0.tendsto
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
  · exact Filter.Eventually.of_forall fun ε => abs_nonneg _
  · have hsmall : ∀ᶠ ε : ℝ in nhds 0, |ε| ≤ 1 := by
      have habs : Filter.Tendsto (fun ε : ℝ => |ε|) (nhds 0) (nhds 0) := by
        have hc : ContinuousAt (fun ε : ℝ => |ε|) 0 := by fun_prop
        simpa using hc.tendsto
      exact ((tendsto_order.1 habs).2 1 zero_lt_one).mono fun ε hε => hε.le
    filter_upwards [hsmall, horizon] with ε hε hhor
    dsimp [C]
    apply le_trans (abs_standardQuadratic_energy_leapfrogN_sub_le_abs_sq
      hε (steps ε) hhor z)
    ring_nf
    exact le_rfl

/-- Gaussian specialization of the deterministic core of Proposition 4.2.
For two forward leapfrog trajectories started with shared momentum, the
multinomial index-law discrepancy is controlled by the initial potential gap
plus the two uniform fixed-horizon integration errors. -/
theorem standardQuadratic_trajectoryIndexPMF_totalVariation_le
    {ε : ℝ} (hε : |ε| ≤ 1) (L : ℕ) {T : ℝ}
    (horizon : (L : ℝ) * |ε| ≤ T)
    (q₁ q₂ : Position ι) (p : Momentum ι) :
    Mcmc.Finite.totalVariation
        (trajectoryIndexPMF standardQuadraticPotential
          (fun i : Fin (L + 1) =>
            leapfrogN standardQuadraticGradient ε i.val (q₁, p)))
        (trajectoryIndexPMF standardQuadraticPotential
          (fun i : Fin (L + 1) =>
            leapfrogN standardQuadraticGradient ε i.val (q₂, p))) ≤
      (ENNReal.ofReal (Real.exp
        (|standardQuadraticPotential q₁ - standardQuadraticPotential q₂| +
          T * |ε| ^ 2 *
            (Real.exp ((13 / 4 : ℝ) * T) *
              euclideanPhaseSize (q₁, p)) ^ 2 +
          T * |ε| ^ 2 *
            (Real.exp ((13 / 4 : ℝ) * T) *
              euclideanPhaseSize (q₂, p)) ^ 2))) ^ 2 - 1 := by
  let error : PhaseSpace ι → ℝ := fun z =>
    T * |ε| ^ 2 *
      (Real.exp ((13 / 4 : ℝ) * T) * euclideanPhaseSize z) ^ 2
  have hindexHorizon : ∀ i : Fin (L + 1), (i.val : ℝ) * |ε| ≤ T := by
    intro i
    have hi : i.val ≤ L := Nat.le_of_lt_succ i.isLt
    have hiR : (i.val : ℝ) ≤ L := by exact_mod_cast hi
    exact (mul_le_mul_of_nonneg_right hiR (abs_nonneg ε)).trans horizon
  have herr : ∀ z : PhaseSpace ι, ∀ i : Fin (L + 1),
      |energy standardQuadraticPotential
            (leapfrogN standardQuadraticGradient ε i.val z) -
          energy standardQuadraticPotential z| ≤ error z := by
    intro z i
    exact abs_standardQuadratic_energy_leapfrogN_sub_le_abs_sq
      hε i.val (hindexHorizon i) z
  have hinitial :
      |energy standardQuadraticPotential (q₁, p) -
          energy standardQuadraticPotential (q₂, p)| =
        |standardQuadraticPotential q₁ - standardQuadraticPotential q₂| := by
    unfold energy
    congr 1
    ring
  have hT : 0 ≤ T :=
    (mul_nonneg (Nat.cast_nonneg L) (abs_nonneg ε)).trans horizon
  apply trajectoryIndexPMF_totalVariation_le_of_abs_energy_sub_le
  · positivity
  · intro i
    rw [show
      energy standardQuadraticPotential
            (leapfrogN standardQuadraticGradient ε i.val (q₁, p)) -
          energy standardQuadraticPotential
            (leapfrogN standardQuadraticGradient ε i.val (q₂, p)) =
        (energy standardQuadraticPotential
            (leapfrogN standardQuadraticGradient ε i.val (q₁, p)) -
          energy standardQuadraticPotential (q₁, p)) +
        (energy standardQuadraticPotential (q₁, p) -
          energy standardQuadraticPotential (q₂, p)) +
        (energy standardQuadraticPotential (q₂, p) -
          energy standardQuadraticPotential
            (leapfrogN standardQuadraticGradient ε i.val (q₂, p))) by ring]
    apply le_trans (abs_add_le _ _)
    apply le_trans (add_le_add (abs_add_le _ _) le_rfl)
    rw [hinitial, abs_sub_comm
      (energy standardQuadraticPotential (q₂, p))]
    dsimp [error] at herr ⊢
    nlinarith [herr (q₁, p) i, herr (q₂, p) i]

/-- Forward standard-quadratic leapfrog trajectories parameterized as required
by Proposition 4.2. -/
noncomputable def standardQuadraticForwardTrajectoryFamily
    (q : Position ι) (p : Momentum ι) : ParameterizedTrajectoryFamily ι :=
  fun ε _L i =>
    leapfrogN standardQuadraticGradient ε i.val (q, p)

/-- On every fixed pair of initial phase points, standard-quadratic forward
leapfrog trajectories conserve their own baseline energies uniformly over the
fixed-integration-time regime. -/
theorem standardQuadraticForwardTrajectory_uniformCenteredEnergyError
    (q₁ q₂ : Position ι) (p : Momentum ι) :
    XuProposition42UniformCenteredEnergyError standardQuadraticPotential
      (standardQuadraticForwardTrajectoryFamily q₁ p)
      (standardQuadraticForwardTrajectoryFamily q₂ p) := by
  intro radius hradius
  let M := max (euclideanPhaseSize (q₁, p)) (euclideanPhaseSize (q₂, p))
  let C := (Real.exp (13 / 4 : ℝ) * M) ^ 2
  have hC : 0 ≤ C := sq_nonneg _
  have htend : Filter.Tendsto (fun ε : ℝ => C * |ε| ^ 2)
      (nhds 0) (nhds 0) := by
    have hcontinuous : Continuous fun ε : ℝ => C * |ε| ^ 2 := by fun_prop
    simpa using
      (hcontinuous.continuousAt : ContinuousAt (fun ε : ℝ => C * |ε| ^ 2) 0).tendsto
  have heventually : ∀ᶠ ε : ℝ in nhds 0, C * |ε| ^ 2 < radius :=
    htend.eventually (Iio_mem_nhds hradius)
  rcases Metric.mem_nhds_iff.mp heventually with ⟨η, hη, hηball⟩
  let ε0 := min (η / 2) (1 / 2 : ℝ)
  have hε0 : 0 < ε0 := lt_min (half_pos hη) (by norm_num)
  refine ⟨ε0, hε0, 1, by norm_num, ?_⟩
  intro ε hεpos hε L hlength
  have hεhalf : ε < 1 / 2 := hε.trans_le (min_le_right _ _)
  have hεone : |ε| ≤ 1 := by
    rw [abs_of_pos hεpos]
    linarith
  have hεη : |ε| < η := by
    rw [abs_of_pos hεpos]
    have := hε.trans_le (min_le_left _ _)
    linarith
  have hsmall : C * |ε| ^ 2 < radius := by
    apply hηball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact hεη
  refine ⟨energy standardQuadraticPotential (q₁, p),
    energy standardQuadraticPotential (q₂, p), ?_, ?_⟩
  · intro i
    have hi : i.val ≤ L := Nat.le_of_lt_succ i.isLt
    have hiR : (i.val : ℝ) ≤ L := by exact_mod_cast hi
    have hhorizon : (i.val : ℝ) * |ε| ≤ 1 := by
      rw [abs_of_pos hεpos]
      apply le_of_lt
      calc
        (i.val : ℝ) * ε ≤ (L : ℝ) * ε :=
          mul_le_mul_of_nonneg_right hiR hεpos.le
        _ = ε * (L : ℝ) := mul_comm _ _
        _ < ε0 * (1 : ℝ) := by simpa using hlength
        _ ≤ 1 := by dsimp [ε0]; linarith [min_le_right (η / 2) (1 / 2 : ℝ)]
    have herr := abs_standardQuadratic_energy_leapfrogN_sub_le_abs_sq
      hεone i.val hhorizon (q₁, p)
    norm_num at herr
    apply herr.trans
    apply le_of_lt
    apply lt_of_le_of_lt _ hsmall
    have hsize : euclideanPhaseSize (q₁, p) ≤ M := by
      dsimp [M]
      exact le_max_left _ _
    have hsquare :
        (Real.exp (13 / 4 : ℝ) * euclideanPhaseSize (q₁, p)) ^ 2 ≤
          (Real.exp (13 / 4 : ℝ) * M) ^ 2 := by
      apply (sq_le_sq₀
        (mul_nonneg (Real.exp_pos _).le (euclideanPhaseSize_nonneg _))
        (mul_nonneg (Real.exp_pos _).le
          ((euclideanPhaseSize_nonneg (q₁, p)).trans hsize))).mpr
      exact mul_le_mul_of_nonneg_left hsize (Real.exp_pos _).le
    calc
      ε ^ 2 *
          (Real.exp (13 / 4 : ℝ) * euclideanPhaseSize (q₁, p)) ^ 2 ≤
        ε ^ 2 * (Real.exp (13 / 4 : ℝ) * M) ^ 2 :=
          mul_le_mul_of_nonneg_left hsquare (sq_nonneg _)
      _ = C * |ε| ^ 2 := by
        rw [abs_of_pos hεpos]
        dsimp [C]
        ring
  · intro i
    have hi : i.val ≤ L := Nat.le_of_lt_succ i.isLt
    have hiR : (i.val : ℝ) ≤ L := by exact_mod_cast hi
    have hhorizon : (i.val : ℝ) * |ε| ≤ 1 := by
      rw [abs_of_pos hεpos]
      apply le_of_lt
      calc
        (i.val : ℝ) * ε ≤ (L : ℝ) * ε :=
          mul_le_mul_of_nonneg_right hiR hεpos.le
        _ = ε * (L : ℝ) := mul_comm _ _
        _ < ε0 * (1 : ℝ) := by simpa using hlength
        _ ≤ 1 := by dsimp [ε0]; linarith [min_le_right (η / 2) (1 / 2 : ℝ)]
    have herr := abs_standardQuadratic_energy_leapfrogN_sub_le_abs_sq
      hεone i.val hhorizon (q₂, p)
    norm_num at herr
    apply herr.trans
    apply le_of_lt
    apply lt_of_le_of_lt _ hsmall
    have hsize : euclideanPhaseSize (q₂, p) ≤ M := by
      dsimp [M]
      exact le_max_right _ _
    have hsquare :
        (Real.exp (13 / 4 : ℝ) * euclideanPhaseSize (q₂, p)) ^ 2 ≤
          (Real.exp (13 / 4 : ℝ) * M) ^ 2 := by
      apply (sq_le_sq₀
        (mul_nonneg (Real.exp_pos _).le (euclideanPhaseSize_nonneg _))
        (mul_nonneg (Real.exp_pos _).le
          ((euclideanPhaseSize_nonneg (q₂, p)).trans hsize))).mpr
      exact mul_le_mul_of_nonneg_left hsize (Real.exp_pos _).le
    calc
      ε ^ 2 *
          (Real.exp (13 / 4 : ℝ) * euclideanPhaseSize (q₂, p)) ^ 2 ≤
        ε ^ 2 * (Real.exp (13 / 4 : ℝ) * M) ^ 2 :=
          mul_le_mul_of_nonneg_left hsquare (sq_nonneg _)
      _ = C * |ε| ^ 2 := by
        rw [abs_of_pos hεpos]
        dsimp [C]
        ring

/-- Validated Proposition 4.2 specialization for standard-quadratic forward
leapfrog trajectories from arbitrary fixed positions and shared momentum. -/
theorem standardQuadraticForwardTrajectory_xuProposition42
    (q₁ q₂ : Position ι) (p : Momentum ι) :
    XuProposition42TVConclusion standardQuadraticPotential
      (standardQuadraticForwardTrajectoryFamily q₁ p)
      (standardQuadraticForwardTrajectoryFamily q₂ p) :=
  XuProposition42UniformCenteredEnergyError.tvConclusion _ _ _
    (standardQuadraticForwardTrajectory_uniformCenteredEnergyError q₁ q₂ p)

/-- Offset standard-quadratic trajectories with an arbitrary shared origin
chosen at each trajectory length. -/
noncomputable def standardQuadraticOffsetTrajectoryFamily
    (origin : (L : ℕ) → Fin (L + 1))
    (q : Position ι) (p : Momentum ι) : ParameterizedTrajectoryFamily ι :=
  fun ε L i =>
    offsetLeapfrogTrajectory standardQuadraticGradient ε (origin L) (q, p) i

/-- Offset trajectories with the origin retained explicitly for uniform
conditioning and averaging. -/
noncomputable def standardQuadraticOriginTrajectoryFamily
    (q : Position ι) (p : Momentum ι) :
    ParameterizedOriginTrajectoryFamily ι :=
  fun ε _L origin i =>
    offsetLeapfrogTrajectory standardQuadraticGradient ε origin (q, p) i

/-- The centered-energy estimate is uniform over every possible randomized
backward/forward trajectory split. -/
theorem standardQuadraticOffsetTrajectory_uniformCenteredEnergyError_allOrigins
    (q₁ q₂ : Position ι) (p : Momentum ι) :
    ∀ radius : ℝ, 0 < radius →
      ∃ ε0 : ℝ, 0 < ε0 ∧
        ∃ L0 : ℕ, 1 ≤ L0 ∧
          ∀ ε : ℝ, 0 < ε → ε < ε0 →
            ∀ L : ℕ, ε * (L : ℝ) < ε0 * (L0 : ℝ) →
              ∀ origin : Fin (L + 1),
                ∃ center₁ center₂ : ℝ,
                  (∀ i, |energy standardQuadraticPotential
                      (offsetLeapfrogTrajectory standardQuadraticGradient ε
                        origin (q₁, p) i) - center₁| ≤ radius) ∧
                  (∀ i, |energy standardQuadraticPotential
                      (offsetLeapfrogTrajectory standardQuadraticGradient ε
                        origin (q₂, p) i) - center₂| ≤ radius) := by
  intro radius hradius
  let M := max (euclideanPhaseSize (q₁, p)) (euclideanPhaseSize (q₂, p))
  let C := (Real.exp (13 / 4 : ℝ) * M) ^ 2
  have htend : Filter.Tendsto (fun ε : ℝ => C * |ε| ^ 2)
      (nhds 0) (nhds 0) := by
    have hcontinuous : Continuous fun ε : ℝ => C * |ε| ^ 2 := by fun_prop
    simpa using
      (hcontinuous.continuousAt : ContinuousAt (fun ε : ℝ => C * |ε| ^ 2) 0).tendsto
  have heventually : ∀ᶠ ε : ℝ in nhds 0, C * |ε| ^ 2 < radius :=
    htend.eventually (Iio_mem_nhds hradius)
  rcases Metric.mem_nhds_iff.mp heventually with ⟨η, hη, hηball⟩
  let ε0 := min (η / 2) (1 / 2 : ℝ)
  have hε0 : 0 < ε0 := lt_min (half_pos hη) (by norm_num)
  refine ⟨ε0, hε0, 1, by norm_num, ?_⟩
  intro ε hεpos hε L hlength origin
  have hεone : |ε| ≤ 1 := by
    rw [abs_of_pos hεpos]
    have := hε.trans_le (min_le_right (η / 2) (1 / 2 : ℝ))
    linarith
  have hεη : |ε| < η := by
    rw [abs_of_pos hεpos]
    have := hε.trans_le (min_le_left (η / 2) (1 / 2 : ℝ))
    linarith
  have hsmall : C * |ε| ^ 2 < radius := by
    apply hηball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact hεη
  have hhorizon : (L : ℝ) * |ε| ≤ 1 := by
    rw [abs_of_pos hεpos, mul_comm]
    apply le_of_lt
    exact hlength.trans_le (by
      norm_num
      dsimp [ε0]
      linarith [min_le_right (η / 2) (1 / 2 : ℝ)])
  refine ⟨energy standardQuadraticPotential (q₁, p),
    energy standardQuadraticPotential (q₂, p), ?_, ?_⟩
  · intro i
    have herr :=
      abs_standardQuadratic_energy_offsetLeapfrogTrajectory_sub_le_abs_sq
        hεone origin i hhorizon (q₁, p)
    norm_num at herr
    apply herr.trans
    apply le_of_lt
    apply lt_of_le_of_lt _ hsmall
    have hsize : euclideanPhaseSize (q₁, p) ≤ M := by
      dsimp [M]
      exact le_max_left _ _
    have hsquare :
        (Real.exp (13 / 4 : ℝ) * euclideanPhaseSize (q₁, p)) ^ 2 ≤
          (Real.exp (13 / 4 : ℝ) * M) ^ 2 := by
      apply (sq_le_sq₀
        (mul_nonneg (Real.exp_pos _).le (euclideanPhaseSize_nonneg _))
        (mul_nonneg (Real.exp_pos _).le
          ((euclideanPhaseSize_nonneg (q₁, p)).trans hsize))).mpr
      exact mul_le_mul_of_nonneg_left hsize (Real.exp_pos _).le
    calc
      ε ^ 2 *
          (Real.exp (13 / 4 : ℝ) * euclideanPhaseSize (q₁, p)) ^ 2 ≤
        ε ^ 2 * (Real.exp (13 / 4 : ℝ) * M) ^ 2 :=
          mul_le_mul_of_nonneg_left hsquare (sq_nonneg _)
      _ = C * |ε| ^ 2 := by
        rw [abs_of_pos hεpos]
        dsimp [C]
        ring
  · intro i
    have herr :=
      abs_standardQuadratic_energy_offsetLeapfrogTrajectory_sub_le_abs_sq
        hεone origin i hhorizon (q₂, p)
    norm_num at herr
    apply herr.trans
    apply le_of_lt
    apply lt_of_le_of_lt _ hsmall
    have hsize : euclideanPhaseSize (q₂, p) ≤ M := by
      dsimp [M]
      exact le_max_right _ _
    have hsquare :
        (Real.exp (13 / 4 : ℝ) * euclideanPhaseSize (q₂, p)) ^ 2 ≤
          (Real.exp (13 / 4 : ℝ) * M) ^ 2 := by
      apply (sq_le_sq₀
        (mul_nonneg (Real.exp_pos _).le (euclideanPhaseSize_nonneg _))
        (mul_nonneg (Real.exp_pos _).le
          ((euclideanPhaseSize_nonneg (q₂, p)).trans hsize))).mpr
      exact mul_le_mul_of_nonneg_left hsize (Real.exp_pos _).le
    calc
      ε ^ 2 *
          (Real.exp (13 / 4 : ℝ) * euclideanPhaseSize (q₂, p)) ^ 2 ≤
        ε ^ 2 * (Real.exp (13 / 4 : ℝ) * M) ^ 2 :=
          mul_le_mul_of_nonneg_left hsquare (sq_nonneg _)
      _ = C * |ε| ^ 2 := by
        rw [abs_of_pos hεpos]
        dsimp [C]
        ring

/-- Every deterministic origin-selection rule inherits the uniform centered-
energy property. -/
theorem standardQuadraticOffsetTrajectory_uniformCenteredEnergyError
    (origin : (L : ℕ) → Fin (L + 1))
    (q₁ q₂ : Position ι) (p : Momentum ι) :
    XuProposition42UniformCenteredEnergyError standardQuadraticPotential
      (standardQuadraticOffsetTrajectoryFamily origin q₁ p)
      (standardQuadraticOffsetTrajectoryFamily origin q₂ p) := by
  intro radius hradius
  rcases standardQuadraticOffsetTrajectory_uniformCenteredEnergyError_allOrigins
    q₁ q₂ p radius hradius with ⟨ε0, hε0, L0, hL0, hbound⟩
  refine ⟨ε0, hε0, L0, hL0, ?_⟩
  intro ε hεpos hε L hlength
  exact hbound ε hεpos hε L hlength (origin L)

/-- Proposition 4.2 holds uniformly conditional on every shared randomized
origin for standard-quadratic trajectories. -/
theorem standardQuadraticOriginTrajectory_allOrigins_xuProposition42
    (q₁ q₂ : Position ι) (p : Momentum ι) :
    XuProposition42AllOriginsTVConclusion standardQuadraticPotential
      (standardQuadraticOriginTrajectoryFamily q₁ p)
      (standardQuadraticOriginTrajectoryFamily q₂ p) := by
  intro δ hδ
  rcases exists_pos_expSqTotalVariationBound_lt hδ with
    ⟨envelopeRadius, henvelopeRadius, henvelope⟩
  have hhalf : 0 < envelopeRadius / 2 := half_pos henvelopeRadius
  rcases standardQuadraticOffsetTrajectory_uniformCenteredEnergyError_allOrigins
    q₁ q₂ p (envelopeRadius / 2) hhalf with
    ⟨ε0, hε0, L0, hL0, herror⟩
  refine ⟨ε0, hε0, L0, hL0, ?_⟩
  intro ε hεpos hε L hlength origin
  rcases herror ε hεpos hε L hlength origin with
    ⟨center₁, center₂, herror₁, herror₂⟩
  apply (trajectoryIndexPMF_totalVariation_le_of_centered_energy
    standardQuadraticPotential
    (standardQuadraticOriginTrajectoryFamily q₁ p ε L origin)
    (standardQuadraticOriginTrajectoryFamily q₂ p ε L origin)
    center₁ center₂ (envelopeRadius / 2) (envelopeRadius / 2)
    hhalf.le hhalf.le herror₁ herror₂).trans_lt
  simpa only [add_halves] using henvelope

/-- Averaging over the actual uniform trajectory-origin draw preserves the
standard-quadratic Proposition 4.2 tolerance. -/
theorem standardQuadraticOriginTrajectory_averaged_xuProposition42
    (q₁ q₂ : Position ι) (p : Momentum ι) :
    XuProposition42AveragedOriginTVConclusion standardQuadraticPotential
      (standardQuadraticOriginTrajectoryFamily q₁ p)
      (standardQuadraticOriginTrajectoryFamily q₂ p) :=
  XuProposition42AllOriginsTVConclusion.averagedOrigin _ _ _
    (standardQuadraticOriginTrajectory_allOrigins_xuProposition42 q₁ q₂ p)

/-- Validated Proposition 4.2 for the actual standard-Gaussian randomized-HMC
categorical experiment: sample the trajectory origin uniformly, maximally
couple the two conditional multinomial index laws, and ask whether the two
selected indices differ. -/
theorem standardQuadraticOriginTrajectory_randomizedMaximalMismatch_xuProposition42
    (q₁ q₂ : Position ι) (p : Momentum ι) :
    XuProposition42RandomizedMaximalMismatchConclusion
      standardQuadraticPotential
      (standardQuadraticOriginTrajectoryFamily q₁ p)
      (standardQuadraticOriginTrajectoryFamily q₂ p) :=
  (xuProposition42AveragedOriginTVConclusion_iff_randomizedMaximalMismatch
    standardQuadraticPotential
    (standardQuadraticOriginTrajectoryFamily q₁ p)
    (standardQuadraticOriginTrajectoryFamily q₂ p)).mp
      (standardQuadraticOriginTrajectory_averaged_xuProposition42 q₁ q₂ p)

/-- Validated Proposition 4.2 specialization for every shared randomized
backward/forward origin-selection rule on the standard Gaussian target. -/
theorem standardQuadraticOffsetTrajectory_xuProposition42
    (origin : (L : ℕ) → Fin (L + 1))
    (q₁ q₂ : Position ι) (p : Momentum ι) :
    XuProposition42TVConclusion standardQuadraticPotential
      (standardQuadraticOffsetTrajectoryFamily origin q₁ p)
      (standardQuadraticOffsetTrajectoryFamily origin q₂ p) :=
  XuProposition42UniformCenteredEnergyError.tvConclusion _ _ _
    (standardQuadraticOffsetTrajectory_uniformCenteredEnergyError
      origin q₁ q₂ p)

/-- Exact accumulated energy error after `n` standard-Gaussian leapfrog
steps, obtained by telescoping the one-step cubic-order defects. -/
theorem standardQuadratic_energy_leapfrogN_sub_eq
    (ε : ℝ) (n : ℕ) (z : PhaseSpace ι) :
    energy standardQuadraticPotential
        (leapfrogN standardQuadraticGradient ε n z) -
      energy standardQuadraticPotential z =
    ∑ k ∈ Finset.range n, ∑ i, (
      (ε ^ 4 / 8) *
        ((leapfrogN standardQuadraticGradient ε k z).2 i ^ 2 -
          (leapfrogN standardQuadraticGradient ε k z).1 i ^ 2) +
      (ε ^ 6 / 32) *
        (leapfrogN standardQuadraticGradient ε k z).1 i ^ 2 +
      (ε ^ 3 / 4) * (1 - ε ^ 2 / 2) *
        ((leapfrogN standardQuadraticGradient ε k z).1 i *
          (leapfrogN standardQuadraticGradient ε k z).2 i)) := by
  rw [energy_leapfrogN_sub_eq_sum_step_errors]
  apply Finset.sum_congr rfl
  intro k hk
  exact standardQuadratic_energy_leapfrog_sub_eq ε
    (leapfrogN standardQuadraticGradient ε k z)

omit [Fintype ι] in
/-- For a fixed number of steps, the standard-quadratic leapfrog endpoint is
continuous as a function of the step size. -/
theorem continuous_standardQuadratic_leapfrogN_stepSize
    (n : ℕ) (z : PhaseSpace ι) :
    Continuous fun ε : ℝ => leapfrogN standardQuadraticGradient ε n z := by
  induction n with
  | zero =>
      simp only [leapfrogN_zero]
      fun_prop
  | succ n ih =>
      simp_rw [leapfrogN_succ]
      unfold leapfrog halfKick drift standardQuadraticGradient
      fun_prop

/-- At every fixed step count and initial phase point, the standard-Gaussian
leapfrog Hamiltonian error tends to zero with the step size. -/
theorem standardQuadratic_energy_leapfrogN_sub_tendsto_zero
    (n : ℕ) (z : PhaseSpace ι) :
    Filter.Tendsto
      (fun ε : ℝ =>
        energy standardQuadraticPotential
            (leapfrogN standardQuadraticGradient ε n z) -
          energy standardQuadraticPotential z)
      (nhds 0) (nhds 0) := by
  have henergy : Continuous
      (energy (standardQuadraticPotential (ι := ι))) := by
    unfold energy standardQuadraticPotential kineticEnergy
    fun_prop
  have hcontinuous : Continuous fun ε : ℝ =>
      energy standardQuadraticPotential
          (leapfrogN standardQuadraticGradient ε n z) -
        energy standardQuadraticPotential z :=
    (henergy.comp
      (continuous_standardQuadratic_leapfrogN_stepSize n z)).sub continuous_const
  have hzero : leapfrogN standardQuadraticGradient 0 n z = z := by
    have hstep :
        leapfrog (standardQuadraticGradient (ι := ι)) 0 =
          (id : PhaseSpace ι → PhaseSpace ι) := by
      funext w
      ext i <;> simp [leapfrog, halfKick, drift]
    simp [leapfrogN, hstep]
  convert hcontinuous.continuousAt.tendsto using 1
  simp [hzero]

end Mcmc.Hamiltonian
