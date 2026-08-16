import Mcmc.Hamiltonian.CoupledMixture
import Mcmc.Hamiltonian.QuadraticGaussian
import Mcmc.Kernel.UnbiasedEstimator

/-!
# Standard-Gaussian specialization of Xu et al.'s drift interface

This module packages the side conditions already proved for the canonical
Lyapunov function `V(q)=1+dist(q,0)` and the verified standard-quadratic
multinomial-HMC/Gaussian-RWMH kernels.  Its constructor leaves precisely the
HMC affine drift and geometric sublevel facts explicit; accompanying selector
theorems construct parameters satisfying the two scalar conditions.
-/

open MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace Mcmc.Hamiltonian

open ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- One-dimensional quadratic-potential sublevel used as Xu's local region. -/
def standardQuadraticEnergyRegion (E : ℝ) : Set (Position Unit) :=
  {q | standardQuadraticPotential q ≤ E}

@[simp]
theorem standardQuadraticPotential_unit (q : Position Unit) :
    standardQuadraticPotential q = (q () ^ 2) / 2 := by
  simp [standardQuadraticPotential, kineticEnergy, div_eq_mul_inv]
  ring

/-- In one dimension, the quadratic potential takes exactly all values from
zero to `E` on its `E`-sublevel. -/
theorem standardQuadraticPotential_image_energyRegion
    (E : ℝ) :
    standardQuadraticPotential '' standardQuadraticEnergyRegion E =
      Set.Icc 0 E := by
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    constructor
    · rw [standardQuadraticPotential_unit]
      positivity
    · exact hq
  · intro hy
    let q : Position Unit := fun _ => Real.sqrt (2 * y)
    have h2y : 0 ≤ 2 * y := mul_nonneg (by norm_num) hy.1
    have hpotential : standardQuadraticPotential q = y := by
      rw [standardQuadraticPotential_unit]
      dsimp only [q]
      rw [Real.sq_sqrt h2y]
      ring
    exact ⟨q, by simpa only [standardQuadraticEnergyRegion, Set.mem_setOf_eq,
      hpotential] using hy.2, hpotential⟩

theorem sInf_standardQuadraticPotential_image_energyRegion
    {E : ℝ} (hE : 0 ≤ E) :
    sInf (standardQuadraticPotential '' standardQuadraticEnergyRegion E) = 0 := by
  rw [standardQuadraticPotential_image_energyRegion E, csInf_Icc hE]

theorem sSup_standardQuadraticPotential_image_energyRegion
    {E : ℝ} (hE : 0 ≤ E) :
    sSup (standardQuadraticPotential '' standardQuadraticEnergyRegion E) = E := by
  rw [standardQuadraticPotential_image_energyRegion E, csSup_Icc hE]

/-- The quadratic energy sublevel in an arbitrary finite coordinate
dimension. The separate name preserves the original scalar API. -/
def standardQuadraticEnergyRegionFinite (E : ℝ) : Set (Position ι) :=
  {q | standardQuadraticPotential q ≤ E}

/-- In every nonempty finite dimension, the quadratic potential realizes
exactly the interval `[0,E]` on its `E`-sublevel. -/
theorem standardQuadraticPotential_image_energyRegionFinite
    [Nonempty ι] (E : ℝ) :
    standardQuadraticPotential ''
        (standardQuadraticEnergyRegionFinite (ι := ι) E) = Set.Icc 0 E := by
  classical
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    constructor
    · unfold standardQuadraticPotential kineticEnergy
      positivity
    · exact hq
  · intro hy
    let i0 : ι := Classical.choice inferInstance
    let q : Position ι := fun i => if i = i0 then Real.sqrt (2 * y) else 0
    have h2y : 0 ≤ 2 * y := mul_nonneg (by norm_num) hy.1
    have hpotential : standardQuadraticPotential q = y := by
      unfold standardQuadraticPotential kineticEnergy
      dsimp only [q]
      have hsum :
          ∑ i : ι, (if i = i0 then Real.sqrt (2 * y) else 0) ^ 2 =
            (Real.sqrt (2 * y)) ^ 2 := by simp
      rw [hsum, Real.sq_sqrt h2y]
      ring
    exact ⟨q, by
      simpa only [standardQuadraticEnergyRegionFinite, Set.mem_setOf_eq,
        hpotential] using hy.2, hpotential⟩

theorem sInf_standardQuadraticPotential_image_energyRegionFinite
    [Nonempty ι] {E : ℝ} (hE : 0 ≤ E) :
    sInf (standardQuadraticPotential ''
      (standardQuadraticEnergyRegionFinite (ι := ι) E)) = 0 := by
  rw [standardQuadraticPotential_image_energyRegionFinite E, csInf_Icc hE]

theorem sSup_standardQuadraticPotential_image_energyRegionFinite
    [Nonempty ι] {E : ℝ} (hE : 0 ≤ E) :
    sSup (standardQuadraticPotential ''
      (standardQuadraticEnergyRegionFinite (ι := ι) E)) = E := by
  rw [standardQuadraticPotential_image_energyRegionFinite E, csSup_Icc hE]

/-- Energy level chosen from a finite Xu Lyapunov threshold. -/
noncomputable def standardQuadraticXuEll0 (ell1 : ENNReal) : ℝ :=
  ell1.toReal ^ 2

/-- A slightly larger one-dimensional quadratic energy sublevel. -/
noncomputable def standardQuadraticXuRegion (ell1 : ENNReal) :
    Set (Position Unit) :=
  standardQuadraticEnergyRegion (standardQuadraticXuEll0 ell1 + 1)

/-- Every finite `ell1>1` has concrete one-dimensional geometry satisfying
the three sublevel/energy-range premises in Xu's drift assumptions. -/
theorem standardQuadratic_xuSublevelGeometry
    {ell1 : ENNReal} (hell1 : 1 < ell1) (hell1Top : ell1 ≠ ⊤) :
    {q : Position Unit | standardDistanceLyapunov q ≤ ell1} ⊆
        standardQuadraticXuRegion ell1 ∩
          {q | standardQuadraticPotential q ≤ standardQuadraticXuEll0 ell1} ∧
      sInf (standardQuadraticPotential '' standardQuadraticXuRegion ell1) <
        standardQuadraticXuEll0 ell1 ∧
      standardQuadraticXuEll0 ell1 <
        sSup (standardQuadraticPotential '' standardQuadraticXuRegion ell1) := by
  have hellReal : 1 < ell1.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hell1Top).2 hell1
  have hellRealNonneg : 0 ≤ ell1.toReal := le_trans (by norm_num) hellReal.le
  have hell0Pos : 0 < standardQuadraticXuEll0 ell1 := by
    dsimp only [standardQuadraticXuEll0]
    positivity
  have henergyNonneg : 0 ≤ standardQuadraticXuEll0 ell1 + 1 := by
    positivity
  constructor
  · intro q hq
    have hqReal := ENNReal.toReal_mono hell1Top hq
    have hVReal : (standardDistanceLyapunov q).toReal = 1 + dist q 0 := by
      rw [standardDistanceLyapunov, ENNReal.toReal_ofReal]
      positivity
    rw [hVReal] at hqReal
    have hdist : dist q 0 ≤ ell1.toReal := by linarith
    have hcoordDist :=
      (dist_pi_le_iff hellRealNonneg).mp hdist ()
    have hcoord : |q ()| ≤ ell1.toReal := by
      simpa only [Pi.zero_apply, Real.dist_eq, sub_zero] using hcoordDist
    have hsquare : q () ^ 2 ≤ ell1.toReal ^ 2 := by
      rw [← sq_abs (q ())]
      exact (sq_le_sq₀ (abs_nonneg _) hellRealNonneg).2 hcoord
    have hpotential :
        standardQuadraticPotential q ≤ standardQuadraticXuEll0 ell1 := by
      rw [standardQuadraticPotential_unit]
      dsimp only [standardQuadraticXuEll0]
      nlinarith [sq_nonneg (q ())]
    exact ⟨by
      change standardQuadraticPotential q ≤ standardQuadraticXuEll0 ell1 + 1
      linarith, hpotential⟩
  constructor
  · rw [standardQuadraticXuRegion,
      sInf_standardQuadraticPotential_image_energyRegion henergyNonneg]
    exact hell0Pos
  · rw [standardQuadraticXuRegion,
      sSup_standardQuadraticPotential_image_energyRegion henergyNonneg]
    linarith

/-- A conservative energy threshold large enough to contain the canonical
Lyapunov sublevel in any fixed finite dimension. -/
noncomputable def standardQuadraticFiniteXuEll0 (ell1 : ENNReal) : ℝ :=
  (((Fintype.card ι : ℝ) + 1) * ell1.toReal) ^ 2

/-- The corresponding finite-dimensional local energy region. -/
noncomputable def standardQuadraticFiniteXuRegion (ell1 : ENNReal) :
    Set (Position ι) :=
  standardQuadraticEnergyRegionFinite
    (standardQuadraticFiniteXuEll0 (ι := ι) ell1 + 1)

/-- Every finite `ell1 > 1` has explicit energy-range geometry in every
nonempty finite dimension. -/
theorem standardQuadratic_finite_xuSublevelGeometry [Nonempty ι]
    {ell1 : ENNReal} (hell1 : 1 < ell1) (hell1Top : ell1 ≠ ⊤) :
    {q : Position ι | standardDistanceLyapunov q ≤ ell1} ⊆
        standardQuadraticFiniteXuRegion (ι := ι) ell1 ∩
          {q | standardQuadraticPotential q ≤
            standardQuadraticFiniteXuEll0 (ι := ι) ell1} ∧
      sInf (standardQuadraticPotential ''
          standardQuadraticFiniteXuRegion (ι := ι) ell1) <
        standardQuadraticFiniteXuEll0 (ι := ι) ell1 ∧
      standardQuadraticFiniteXuEll0 (ι := ι) ell1 <
        sSup (standardQuadraticPotential ''
          standardQuadraticFiniteXuRegion (ι := ι) ell1) := by
  have hellReal : 1 < ell1.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hell1Top).2 hell1
  let c : ℝ := (Fintype.card ι : ℝ) + 1
  have hc : 0 < c := by dsimp only [c]; positivity
  have hellRealNonneg : 0 ≤ ell1.toReal := le_trans (by norm_num) hellReal.le
  have hell0Pos : 0 < standardQuadraticFiniteXuEll0 (ι := ι) ell1 := by
    dsimp only [standardQuadraticFiniteXuEll0, c]
    positivity
  have henergyNonneg :
      0 ≤ standardQuadraticFiniteXuEll0 (ι := ι) ell1 + 1 := by
    positivity
  constructor
  · intro q hq
    have hqReal := ENNReal.toReal_mono hell1Top hq
    have hVReal : (standardDistanceLyapunov q).toReal = 1 + dist q 0 := by
      rw [standardDistanceLyapunov, ENNReal.toReal_ofReal]
      positivity
    rw [hVReal] at hqReal
    have hdist : dist q 0 ≤ ell1.toReal := by linarith
    have hnormBase := euclideanNorm_sub_le_card_succ_mul_dist q 0
    have hnorm : euclideanNorm q ≤ c * ell1.toReal := by
      calc
        euclideanNorm q ≤ c * dist q 0 := by
          simpa only [sub_zero, c] using hnormBase
        _ ≤ c * ell1.toReal := mul_le_mul_of_nonneg_left hdist hc.le
    have hnormNonneg := euclideanNorm_nonneg q
    have hpotential : standardQuadraticPotential q ≤
        standardQuadraticFiniteXuEll0 (ι := ι) ell1 := by
      rw [standardQuadraticPotential_eq_half_euclideanNorm_sq]
      dsimp only [standardQuadraticFiniteXuEll0, c]
      nlinarith [sq_nonneg (c * ell1.toReal - euclideanNorm q)]
    exact ⟨by
      change standardQuadraticPotential q ≤
        standardQuadraticFiniteXuEll0 (ι := ι) ell1 + 1
      linarith, hpotential⟩
  constructor
  · rw [standardQuadraticFiniteXuRegion,
      sInf_standardQuadraticPotential_image_energyRegionFinite henergyNonneg]
    exact hell0Pos
  · rw [standardQuadraticFiniteXuRegion,
      sSup_standardQuadraticPotential_image_energyRegionFinite henergyNonneg]
    linarith

/-- For the proved Gaussian-RWMH growth coefficient, every subunit mixture
rate admits a sufficiently large finite threshold satisfying Xu's final
paired scalar inequality. -/
theorem exists_standardQuadratic_xuEll1
    (γ : Set.Ioo (0 : NNReal) 1)
    (driftCoefficient driftAllowance : ENNReal)
    (variance : NNReal) (hvariance : variance ≠ 0)
    (hlambda : xuTheorem41Lambda0 γ driftCoefficient
      (2 + Mcmc.Kernel.isotropicGaussianFirstNormMoment
        (ι := ι) variance) < 1)
    (hallowanceTop : driftAllowance ≠ ⊤) :
    ∃ ell1 : ENNReal, 1 < ell1 ∧ ell1 ≠ ⊤ ∧
      xuTheorem41PairedRate γ driftCoefficient driftAllowance
        (2 + Mcmc.Kernel.isotropicGaussianFirstNormMoment
          (ι := ι) variance) ell1 < 1 := by
  exact exists_ell1_xuTheorem41PairedRate_lt_one γ driftCoefficient
    driftAllowance
    (2 + Mcmc.Kernel.isotropicGaussianFirstNormMoment
      (ι := ι) variance)
    hlambda hallowanceTop
    (standardDistanceLyapunov_gaussianRwmh_growthCoefficient_ne_top
      variance hvariance)

/-- The two scalar hypotheses of Xu et al.'s Theorem 4.1 can be selected
jointly for the standard-Gaussian RWMH branch from any strict HMC drift rate
and finite HMC allowance. -/
theorem exists_standardQuadratic_xuScalarParameters
    (driftCoefficient driftAllowance : ENNReal)
    (hdriftLt : driftCoefficient < 1)
    (hallowanceTop : driftAllowance ≠ ⊤)
    (variance : NNReal) (hvariance : variance ≠ 0) :
    ∃ (γ : Set.Ioo (0 : NNReal) 1) (ell1 : ENNReal),
      xuTheorem41Lambda0 γ driftCoefficient
          (2 + Mcmc.Kernel.isotropicGaussianFirstNormMoment
            (ι := ι) variance) < 1 ∧
        1 < ell1 ∧ ell1 ≠ ⊤ ∧
        xuTheorem41PairedRate γ driftCoefficient driftAllowance
          (2 + Mcmc.Kernel.isotropicGaussianFirstNormMoment
            (ι := ι) variance) ell1 < 1 := by
  let growth := 2 + Mcmc.Kernel.isotropicGaussianFirstNormMoment
    (ι := ι) variance
  have hgrowthTop : growth ≠ ⊤ := by
    dsimp only [growth]
    exact standardDistanceLyapunov_gaussianRwmh_growthCoefficient_ne_top
      variance hvariance
  obtain ⟨γ, hlambda⟩ := exists_gamma_xuTheorem41Lambda0_lt_one
    driftCoefficient growth hdriftLt hgrowthTop
  obtain ⟨ell1, hell1, hell1Top, hscalar⟩ :=
    exists_ell1_xuTheorem41PairedRate_lt_one γ driftCoefficient
      driftAllowance growth hlambda hallowanceTop hgrowthTop
  exact ⟨γ, ell1, hlambda, hell1, hell1Top, hscalar⟩

/-- Assemble Xu et al.'s Theorem 4.1 hypotheses for a deterministic initial
state and the standard quadratic target.  Measurability, `V≥1`, the finite
initial moment, and the Gaussian-RWMH growth field are discharged
automatically by the verified kernel theory. -/
noncomputable def standardQuadratic_xuTheorem41DriftAssumptions_of_hmc
    (γ : Set.Ioo (0 : NNReal) 1) (ε : ℝ) (L : ℕ)
    (variance : NNReal) (hvariance : variance ≠ 0)
    (q₀ : Position ι) (S : Set (Position ι))
    (driftCoefficient driftAllowance : ENNReal)
    (ell0 : ℝ) (ell1 : ENNReal)
    (hdriftPos : 0 < driftCoefficient)
    (hdriftLt : driftCoefficient < 1)
    (hallowanceTop : driftAllowance ≠ ⊤)
    (hhmc : ∀ x : Position ι,
      (∫⁻ y, standardDistanceLyapunov (ι := ι) y
        ∂standardPositionMultinomialHMC
          (standardQuadraticPotential (ι := ι))
          (standardQuadraticGradient (ι := ι)) ε L
          contDiff_standardQuadraticPotential.continuous.measurable
          measurable_standardQuadraticGradient x) ≤
        driftCoefficient * standardDistanceLyapunov (ι := ι) x + driftAllowance)
    (hell1 : 1 < ell1) (hell1Top : ell1 ≠ ⊤)
    (hsublevel : {x | standardDistanceLyapunov x ≤ ell1} ⊆
      S ∩ {x | standardQuadraticPotential x ≤ ell0})
    (hell0Inf : sInf (standardQuadraticPotential '' S) < ell0)
    (hell0Sup : ell0 < sSup (standardQuadraticPotential '' S))
    (hlambda : xuTheorem41Lambda0 γ driftCoefficient
      (2 + Mcmc.Kernel.isotropicGaussianFirstNormMoment
        (ι := ι) variance) < 1)
    (hscalar : xuTheorem41PairedRate γ driftCoefficient driftAllowance
      (2 + Mcmc.Kernel.isotropicGaussianFirstNormMoment
        (ι := ι) variance) ell1 < 1) :
    XuTheorem41DriftAssumptions γ
      (standardPositionMultinomialHMC standardQuadraticPotential
        standardQuadraticGradient ε L
        contDiff_standardQuadraticPotential.continuous.measurable
        measurable_standardQuadraticGradient)
      (Mcmc.Kernel.euclideanGaussianRandomWalkMetropolisHastings
        (positionBoltzmannWeight standardQuadraticPotential)
        variance hvariance)
      (Measure.dirac q₀) standardQuadraticPotential S := by
  refine
    { V := standardDistanceLyapunov
      driftCoefficient := driftCoefficient
      driftAllowance := driftAllowance
      growthCoefficient := 2 +
        Mcmc.Kernel.isotropicGaussianFirstNormMoment (ι := ι) variance
      ell0 := ell0
      ell1 := ell1
      measurable_V := measurable_standardDistanceLyapunov
      one_le_V := one_le_standardDistanceLyapunov
      driftCoefficient_pos := hdriftPos
      driftCoefficient_lt_one := hdriftLt
      driftAllowance_ne_top := hallowanceTop
      growthCoefficient_pos :=
        standardDistanceLyapunov_gaussianRwmh_growthCoefficient_pos variance
      hmc_drift := hhmc
      rwmh_growth := ?_
      initial_moment := lintegral_standardDistanceLyapunov_dirac_ne_top q₀
      ell1_gt_one := hell1
      ell1_ne_top := hell1Top
      sublevel_subset := hsublevel
      ell0_above_inf := hell0Inf
      ell0_below_sup := hell0Sup
      lambda0_lt_one := hlambda
      scalar_condition := hscalar }
  intro x
  exact standardQuadraticGaussianRwmh_growth variance hvariance x

/-- In one dimension, a strict affine drift certificate for the verified
multinomial-HMC kernel is now the only remaining input needed to construct all
of Xu et al.'s Theorem 4.1 drift assumptions for deterministic initialization.
The RWMH growth, mixture weight, threshold, geometry, and moments are selected
or proved internally. -/
theorem exists_standardQuadratic_xuTheorem41DriftAssumptions_of_hmc_drift
    (ε : ℝ) (L : ℕ) (variance : NNReal) (hvariance : variance ≠ 0)
    (q₀ : Position Unit) (driftCoefficient driftAllowance : ENNReal)
    (hdriftPos : 0 < driftCoefficient)
    (hdriftLt : driftCoefficient < 1)
    (hallowanceTop : driftAllowance ≠ ⊤)
    (hhmc : ∀ x : Position Unit,
      (∫⁻ y, standardDistanceLyapunov y
        ∂standardPositionMultinomialHMC standardQuadraticPotential
          standardQuadraticGradient ε L
          contDiff_standardQuadraticPotential.continuous.measurable
          measurable_standardQuadraticGradient x) ≤
        driftCoefficient * standardDistanceLyapunov x + driftAllowance) :
    ∃ (γ : Set.Ioo (0 : NNReal) 1) (ell1 : ENNReal),
      Nonempty {h : XuTheorem41DriftAssumptions γ
        (standardPositionMultinomialHMC standardQuadraticPotential
          standardQuadraticGradient ε L
          contDiff_standardQuadraticPotential.continuous.measurable
          measurable_standardQuadraticGradient)
        (Mcmc.Kernel.euclideanGaussianRandomWalkMetropolisHastings
          (positionBoltzmannWeight standardQuadraticPotential)
          variance hvariance)
        (Measure.dirac q₀) standardQuadraticPotential
        (standardQuadraticXuRegion ell1) //
          h.V = standardDistanceLyapunov} := by
  obtain ⟨γ, ell1, hlambda, hell1, hell1Top, hscalar⟩ :=
    exists_standardQuadratic_xuScalarParameters
      (ι := Unit) driftCoefficient driftAllowance hdriftLt hallowanceTop
      variance hvariance
  obtain ⟨hsublevel, hell0Inf, hell0Sup⟩ :=
    standardQuadratic_xuSublevelGeometry hell1 hell1Top
  let h := standardQuadratic_xuTheorem41DriftAssumptions_of_hmc γ ε L
    variance hvariance q₀ (standardQuadraticXuRegion ell1)
    driftCoefficient driftAllowance (standardQuadraticXuEll0 ell1) ell1
    hdriftPos hdriftLt hallowanceTop hhmc hell1 hell1Top hsublevel
    hell0Inf hell0Sup hlambda hscalar
  refine ⟨γ, ell1, ⟨⟨h, ?_⟩⟩⟩
  rfl

/-- In every nonempty finite dimension, the verified `ε = √2`, `L = 1`
multinomial-HMC drift theorem supplies all target-specific assumptions of Xu
et al.'s Theorem 4.1 for deterministic initialization. -/
theorem exists_standardQuadratic_finite_xuTheorem41DriftAssumptions_sqrtTwo
    [Nonempty ι] (variance : NNReal) (hvariance : variance ≠ 0)
    (q₀ : Position ι) :
    ∃ (γ : Set.Ioo (0 : NNReal) 1) (ell1 : ENNReal),
      Nonempty {h : XuTheorem41DriftAssumptions γ
        (standardPositionMultinomialHMC standardQuadraticPotential
          standardQuadraticGradient (Real.sqrt 2) 1
          contDiff_standardQuadraticPotential.continuous.measurable
          measurable_standardQuadraticGradient)
        (Mcmc.Kernel.euclideanGaussianRandomWalkMetropolisHastings
          (positionBoltzmannWeight standardQuadraticPotential)
          variance hvariance)
        (Measure.dirac q₀) standardQuadraticPotential
        (standardQuadraticFiniteXuRegion (ι := ι) ell1) //
          h.V = standardDistanceLyapunov} := by
  obtain ⟨γ, ell1, hlambda, hell1, hell1Top, hscalar⟩ :=
    exists_standardQuadratic_xuScalarParameters
      (ι := ι) (1 / 2) (standardQuadraticSqrtTwoDriftAllowance (ι := ι))
      (by norm_num) standardQuadraticSqrtTwoDriftAllowance_ne_top
      variance hvariance
  obtain ⟨hsublevel, hell0Inf, hell0Sup⟩ :=
    standardQuadratic_finite_xuSublevelGeometry
      (ι := ι) hell1 hell1Top
  let h := standardQuadratic_xuTheorem41DriftAssumptions_of_hmc γ
    (Real.sqrt 2) 1 variance hvariance q₀
    (standardQuadraticFiniteXuRegion (ι := ι) ell1)
    (1 / 2) (standardQuadraticSqrtTwoDriftAllowance (ι := ι))
    (standardQuadraticFiniteXuEll0 (ι := ι) ell1) ell1
    (by norm_num) (by norm_num)
    standardQuadraticSqrtTwoDriftAllowance_ne_top
    standardQuadratic_sqrtTwo_hmc_drift hell1 hell1Top hsublevel
    hell0Inf hell0Sup hlambda hscalar
  refine ⟨γ, ell1, ⟨⟨h, ?_⟩⟩⟩
  rfl

/-- Xu's paired sublevel is automatically compact when its Lyapunov function
is the canonical distance candidate. -/
theorem XuTheorem41DriftAssumptions.isCompact_pairedSublevel_of_V_eq_standardDistance
    {γ : Set.Ioo (0 : NNReal) 1}
    {hmc rwmh : Kernel (Position ι) (Position ι)}
    {initial : Measure (Position ι)}
    {potential : Position ι → ℝ} {S : Set (Position ι)}
    (h : XuTheorem41DriftAssumptions γ hmc rwmh initial potential S)
    (hV : h.V = standardDistanceLyapunov) :
    IsCompact (Mcmc.Kernel.lyapunovSublevel
      (Mcmc.Kernel.IsCoupling.pairedAdd h.V) (1 + h.ell1)) := by
  simpa only [hV] using
    isCompact_lyapunovSublevel_pairedAdd_standardDistanceLyapunov
      (ι := ι) (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, h.ell1_ne_top⟩)

/-- The same paired sublevel contains the pair of origins because Xu assumes
`ℓ₁>1`. -/
theorem XuTheorem41DriftAssumptions.nonempty_pairedSublevel_of_V_eq_standardDistance
    {γ : Set.Ioo (0 : NNReal) 1}
    {hmc rwmh : Kernel (Position ι) (Position ι)}
    {initial : Measure (Position ι)}
    {potential : Position ι → ℝ} {S : Set (Position ι)}
    (h : XuTheorem41DriftAssumptions γ hmc rwmh initial potential S)
    (hV : h.V = standardDistanceLyapunov) :
    (Mcmc.Kernel.lyapunovSublevel
      (Mcmc.Kernel.IsCoupling.pairedAdd h.V) (1 + h.ell1)).Nonempty := by
  have htwo : (2 : ENNReal) ≤ 1 + h.ell1 := by
    calc
      (2 : ENNReal) = 1 + 1 := by norm_num
      _ ≤ 1 + h.ell1 := by
        simpa only [add_comm] using add_le_add_left h.ell1_gt_one.le 1
  simpa only [hV] using
    nonempty_lyapunovSublevel_pairedAdd_standardDistanceLyapunov
      (ι := ι) htwo

/-- End-to-end one-dimensional exact lag-one meeting theorem, conditional
only on the remaining strict affine drift inequality for the implemented
multinomial-HMC kernel. All RWMH, scalar, geometric, initialization, coupling,
and compact-meeting obligations are discharged internally. -/
theorem exists_geometric_exactLagOneMeetingTail_standardQuadratic_of_hmc_drift
    (ε : ℝ) (L : ℕ) (variance : NNReal) (hvariance : variance ≠ 0)
    (q₀ : Position Unit) (driftCoefficient driftAllowance : ENNReal)
    (hdriftPos : 0 < driftCoefficient)
    (hdriftLt : driftCoefficient < 1)
    (hallowanceTop : driftAllowance ≠ ⊤)
    (hhmc : ∀ x : Position Unit,
      (∫⁻ y, standardDistanceLyapunov y
        ∂standardPositionMultinomialHMC standardQuadraticPotential
          standardQuadraticGradient ε L
          contDiff_standardQuadraticPotential.continuous.measurable
          measurable_standardQuadraticGradient x) ≤
        driftCoefficient * standardDistanceLyapunov x + driftAllowance) :
    ∃ (γ : Set.Ioo (0 : NNReal) 1) (C₀ contractionRate : ENNReal),
      C₀ ≠ ⊤ ∧ contractionRate < 1 ∧
        ∀ n : ℕ,
          Mcmc.Kernel.exactMeetingTail
            (Mcmc.Kernel.pathLaw
              (Mcmc.Kernel.laggedInitialMeasure
                ((Measure.dirac q₀).prod (Measure.dirac q₀))
                (hmcRwmhMixture (xuTheorem41HmcWeight γ)
                  standardQuadraticPotential standardQuadraticGradient ε L
                  contDiff_standardQuadraticPotential.continuous.measurable
                  measurable_standardQuadraticGradient variance hvariance))
              (stickyCoupledHmcRwmhMixture (xuTheorem41HmcWeight γ)
                standardQuadraticPotential standardQuadraticGradient ε L
                contDiff_standardQuadraticPotential.continuous.measurable
                measurable_standardQuadraticGradient variance hvariance)) n ≤
            C₀ * contractionRate ^ n := by
  obtain ⟨γ, ell1, ⟨hspecial⟩⟩ :=
    exists_standardQuadratic_xuTheorem41DriftAssumptions_of_hmc_drift
      ε L variance hvariance q₀ driftCoefficient driftAllowance
      hdriftPos hdriftLt hallowanceTop hhmc
  let h := hspecial.1
  have hV : h.V = standardDistanceLyapunov := hspecial.2
  have hinitial : IsMeasureCoupling
      ((Measure.dirac q₀).prod (Measure.dirac q₀))
      (Measure.dirac q₀) (Measure.dirac q₀) :=
    isMeasureCoupling_prod _ _
  have hcompact :=
    h.isCompact_pairedSublevel_of_V_eq_standardDistance hV
  have hnonempty :=
    h.nonempty_pairedSublevel_of_V_eq_standardDistance hV
  let A : Set (Position Unit) := Metric.closedBall 0 1
  have hAcompact : IsCompact A := by
    dsimp only [A]
    exact isCompact_closedBall 0 1
  have hAnonempty : A.Nonempty := by
    refine ⟨0, ?_⟩
    simp [A]
  have hAmeas : MeasurableSet A := hAcompact.measurableSet
  have hAvolume : 0 < volume A := by
    dsimp only [A]
    exact Metric.measure_closedBall_pos volume 0 (by norm_num)
  obtain ⟨C₀, contractionRate, hC₀, hrate, htail⟩ :=
    h.exists_geometric_exactLagOneMeetingTail_stickyHmcRwmh γ
      standardQuadraticPotential standardQuadraticGradient ε L
      contDiff_standardQuadraticPotential.continuous
      measurable_standardQuadraticGradient variance hvariance
      (Measure.dirac q₀) (standardQuadraticXuRegion ell1)
      ((Measure.dirac q₀).prod (Measure.dirac q₀)) hinitial
      hcompact hnonempty hAcompact hAnonempty hAmeas hAvolume
  exact ⟨γ, C₀, contractionRate, hC₀, hrate, htail⟩

/-- Fully instantiated continuous-state scalar Gaussian case of the exact
lag-one geometric meeting theorem. Unlike the preceding conditional theorem,
this result supplies the multinomial-HMC drift certificate internally using
the verified `ε = sqrt 2`, `L = 1` transition. -/
theorem exists_geometric_exactLagOneMeetingTail_standardQuadratic_sqrtTwo
    (variance : NNReal) (hvariance : variance ≠ 0)
    (q₀ : Position Unit) :
    ∃ (γ : Set.Ioo (0 : NNReal) 1) (C₀ contractionRate : ENNReal),
      C₀ ≠ ⊤ ∧ contractionRate < 1 ∧
        ∀ n : ℕ,
          Mcmc.Kernel.exactMeetingTail
            (Mcmc.Kernel.pathLaw
              (Mcmc.Kernel.laggedInitialMeasure
                ((Measure.dirac q₀).prod (Measure.dirac q₀))
                (hmcRwmhMixture (xuTheorem41HmcWeight γ)
                  standardQuadraticPotential standardQuadraticGradient
                  (Real.sqrt 2) 1
                  contDiff_standardQuadraticPotential.continuous.measurable
                  measurable_standardQuadraticGradient variance hvariance))
              (stickyCoupledHmcRwmhMixture (xuTheorem41HmcWeight γ)
                standardQuadraticPotential standardQuadraticGradient
                (Real.sqrt 2) 1
                contDiff_standardQuadraticPotential.continuous.measurable
                measurable_standardQuadraticGradient variance hvariance)) n ≤
            C₀ * contractionRate ^ n := by
  apply exists_geometric_exactLagOneMeetingTail_standardQuadratic_of_hmc_drift
    (Real.sqrt 2) 1 variance hvariance q₀ (1 / 2)
      standardQuadraticUnitSqrtTwoDriftAllowance
  · norm_num
  · norm_num
  · exact standardQuadraticUnitSqrtTwoDriftAllowance_ne_top
  · intro x
    simpa only using standardQuadraticUnit_sqrtTwo_hmc_drift x

/-- Fully instantiated standard-Gaussian exact lag-one meeting theorem in
every nonempty finite dimension. Both the multinomial-HMC and Gaussian-RWMH
transitions, their couplings, the HMC drift certificate, the level-set
geometry, and the exact-meeting small set are discharged internally. -/
theorem exists_geometric_exactLagOneMeetingTail_standardQuadratic_finite_sqrtTwo
    [Nonempty ι] (variance : NNReal) (hvariance : variance ≠ 0)
    (q₀ : Position ι) :
    ∃ (γ : Set.Ioo (0 : NNReal) 1) (C₀ contractionRate : ENNReal),
      C₀ ≠ ⊤ ∧ contractionRate < 1 ∧
        ∀ n : ℕ,
          Mcmc.Kernel.exactMeetingTail
            (Mcmc.Kernel.pathLaw
              (Mcmc.Kernel.laggedInitialMeasure
                ((Measure.dirac q₀).prod (Measure.dirac q₀))
                (hmcRwmhMixture (xuTheorem41HmcWeight γ)
                  standardQuadraticPotential standardQuadraticGradient
                  (Real.sqrt 2) 1
                  contDiff_standardQuadraticPotential.continuous.measurable
                  measurable_standardQuadraticGradient variance hvariance))
              (stickyCoupledHmcRwmhMixture (xuTheorem41HmcWeight γ)
                standardQuadraticPotential standardQuadraticGradient
                (Real.sqrt 2) 1
                contDiff_standardQuadraticPotential.continuous.measurable
                measurable_standardQuadraticGradient variance hvariance)) n ≤
            C₀ * contractionRate ^ n := by
  obtain ⟨γ, ell1, ⟨hspecial⟩⟩ :=
    exists_standardQuadratic_finite_xuTheorem41DriftAssumptions_sqrtTwo
      (ι := ι) variance hvariance q₀
  let h := hspecial.1
  have hV : h.V = standardDistanceLyapunov := hspecial.2
  have hinitial : IsMeasureCoupling
      ((Measure.dirac q₀).prod (Measure.dirac q₀))
      (Measure.dirac q₀) (Measure.dirac q₀) :=
    isMeasureCoupling_prod _ _
  have hcompact :=
    h.isCompact_pairedSublevel_of_V_eq_standardDistance hV
  have hnonempty :=
    h.nonempty_pairedSublevel_of_V_eq_standardDistance hV
  let A : Set (Position ι) := Metric.closedBall 0 1
  have hAcompact : IsCompact A := by
    dsimp only [A]
    exact isCompact_closedBall 0 1
  have hAnonempty : A.Nonempty := by
    refine ⟨0, ?_⟩
    simp [A]
  have hAmeas : MeasurableSet A := hAcompact.measurableSet
  have hAvolume : 0 < volume A := by
    dsimp only [A]
    exact Metric.measure_closedBall_pos volume 0 (by norm_num)
  obtain ⟨C₀, contractionRate, hC₀, hrate, htail⟩ :=
    h.exists_geometric_exactLagOneMeetingTail_stickyHmcRwmh γ
      standardQuadraticPotential standardQuadraticGradient (Real.sqrt 2) 1
      contDiff_standardQuadraticPotential.continuous
      measurable_standardQuadraticGradient variance hvariance
      (Measure.dirac q₀) (standardQuadraticFiniteXuRegion (ι := ι) ell1)
      ((Measure.dirac q₀).prod (Measure.dirac q₀)) hinitial
      hcompact hnonempty hAcompact hAnonempty hAmeas hAvolume
  exact ⟨γ, C₀, contractionRate, hC₀, hrate, htail⟩

/-- Concrete standard-Gaussian bounded-observable estimator endpoint. All
algorithmic and meeting hypotheses are discharged; marginal expectation
convergence from the selected Dirac start remains as an explicit implication. -/
theorem exists_standardQuadratic_boundedEstimator_of_marginal_convergence
    [Nonempty ι] (variance : NNReal) (hvariance : variance ≠ 0)
    (q₀ : Position ι) (observable : Position ι → ℝ)
    (hmeasurable : Measurable observable) {B : ℝ} (hB : 0 ≤ B)
    (hbounded : ∀ q, ‖observable q‖ ≤ B) (targetMean : ℝ) :
    ∃ (γ : Set.Ioo (0 : NNReal) 1) (C₀ contractionRate : ENNReal),
      C₀ ≠ ⊤ ∧ contractionRate < 1 ∧
      let transition := hmcRwmhMixture (xuTheorem41HmcWeight γ)
        standardQuadraticPotential standardQuadraticGradient
        (Real.sqrt 2) 1
        contDiff_standardQuadraticPotential.continuous.measurable
        measurable_standardQuadraticGradient variance hvariance
      let coupled := stickyCoupledHmcRwmhMixture (xuTheorem41HmcWeight γ)
        standardQuadraticPotential standardQuadraticGradient
        (Real.sqrt 2) 1
        contDiff_standardQuadraticPotential.continuous.measurable
        measurable_standardQuadraticGradient variance hvariance
      Filter.Tendsto
          (fun n => ∫ q, observable q
            ∂Mcmc.Kernel.lawAtTime (Measure.dirac q₀) transition n)
          Filter.atTop (nhds targetMean) →
        (∫ path, Mcmc.Kernel.stoppedLaggedUnbiasedEstimator observable path
          ∂Mcmc.Kernel.pathLaw
            (Mcmc.Kernel.laggedInitialMeasure
              ((Measure.dirac q₀).prod (Measure.dirac q₀)) transition)
            coupled) = targetMean ∧
          MemLp (Mcmc.Kernel.stoppedLaggedUnbiasedEstimator observable) 2
            (Mcmc.Kernel.pathLaw
              (Mcmc.Kernel.laggedInitialMeasure
                ((Measure.dirac q₀).prod (Measure.dirac q₀)) transition)
              coupled) := by
  obtain ⟨γ, C₀, contractionRate, hC₀, hrate, htail⟩ :=
    exists_geometric_exactLagOneMeetingTail_standardQuadratic_finite_sqrtTwo
      variance hvariance q₀
  refine ⟨γ, C₀, contractionRate, hC₀, hrate, ?_⟩
  dsimp only
  intro hmarginal
  apply Mcmc.Kernel.integral_eq_and_memLp_two_stoppedLaggedUnbiasedEstimator_of_bounded_geometric
      ((Measure.dirac q₀).prod (Measure.dirac q₀)) (Measure.dirac q₀)
      (hmcRwmhMixture (xuTheorem41HmcWeight γ)
        standardQuadraticPotential standardQuadraticGradient
        (Real.sqrt 2) 1
        contDiff_standardQuadraticPotential.continuous.measurable
        measurable_standardQuadraticGradient variance hvariance)
      (stickyCoupledHmcRwmhMixture (xuTheorem41HmcWeight γ)
        standardQuadraticPotential standardQuadraticGradient
        (Real.sqrt 2) 1
        contDiff_standardQuadraticPotential.continuous.measurable
        measurable_standardQuadraticGradient variance hvariance)
      (isMeasureCoupling_prod _ _)
      (stickyCoupledHmcRwmhMixture_isCoupling _ _ _ _ _ _ _ _ _)
      observable hmeasurable hB hbounded targetMean hmarginal
      C₀ contractionRate hC₀ hrate htail
      (stickyCoupledHmcRwmhMixture_isFaithful _ _ _ _ _ _ _ _ _)

/-- Unconditional bounded-observable endpoint for the concrete
standard-Gaussian construction. Geometric faithful meeting now supplies the
previously external marginal-expectation convergence premise. The theorem
constructs the limiting mean; identifying it with an independently
normalized Gaussian target integral is a separate normalization result. -/
theorem exists_standardQuadratic_boundedEstimator
    [Nonempty ι] (variance : NNReal) (hvariance : variance ≠ 0)
    (q₀ : Position ι) (observable : Position ι → ℝ)
    (hmeasurable : Measurable observable) {B : ℝ} (hB : 0 ≤ B)
    (hbounded : ∀ q, ‖observable q‖ ≤ B) :
    ∃ (gamma : Set.Ioo (0 : NNReal) 1) (C₀ contractionRate : ENNReal)
        (targetMean : ℝ),
      C₀ ≠ ⊤ ∧ contractionRate < 1 ∧
      let transition := hmcRwmhMixture (xuTheorem41HmcWeight gamma)
        standardQuadraticPotential standardQuadraticGradient
        (Real.sqrt 2) 1
        contDiff_standardQuadraticPotential.continuous.measurable
        measurable_standardQuadraticGradient variance hvariance
      let coupled := stickyCoupledHmcRwmhMixture (xuTheorem41HmcWeight gamma)
        standardQuadraticPotential standardQuadraticGradient
        (Real.sqrt 2) 1
        contDiff_standardQuadraticPotential.continuous.measurable
        measurable_standardQuadraticGradient variance hvariance
      Filter.Tendsto
          (fun n => ∫ q, observable q
            ∂Mcmc.Kernel.lawAtTime (Measure.dirac q₀) transition n)
          Filter.atTop (nhds targetMean) ∧
        (∫ path, Mcmc.Kernel.stoppedLaggedUnbiasedEstimator observable path
          ∂Mcmc.Kernel.pathLaw
            (Mcmc.Kernel.laggedInitialMeasure
              ((Measure.dirac q₀).prod (Measure.dirac q₀)) transition)
            coupled) = targetMean ∧
          MemLp (Mcmc.Kernel.stoppedLaggedUnbiasedEstimator observable) 2
            (Mcmc.Kernel.pathLaw
              (Mcmc.Kernel.laggedInitialMeasure
                ((Measure.dirac q₀).prod (Measure.dirac q₀)) transition)
              coupled) := by
  obtain ⟨gamma, C₀, contractionRate, hC₀, hrate, htail⟩ :=
    exists_geometric_exactLagOneMeetingTail_standardQuadratic_finite_sqrtTwo
      variance hvariance q₀
  let transition := hmcRwmhMixture (xuTheorem41HmcWeight gamma)
    (standardQuadraticPotential : Position ι → ℝ)
    (standardQuadraticGradient : Position ι → Position ι) (Real.sqrt 2) 1
    contDiff_standardQuadraticPotential.continuous.measurable
    measurable_standardQuadraticGradient variance hvariance
  let coupled := stickyCoupledHmcRwmhMixture (xuTheorem41HmcWeight gamma)
    (standardQuadraticPotential : Position ι → ℝ)
    (standardQuadraticGradient : Position ι → Position ι) (Real.sqrt 2) 1
    contDiff_standardQuadraticPotential.continuous.measurable
    measurable_standardQuadraticGradient variance hvariance
  let pathMeasure := Mcmc.Kernel.pathLaw
    (Mcmc.Kernel.laggedInitialMeasure
      ((Measure.dirac q₀).prod (Measure.dirac q₀)) transition) coupled
  let targetMean := ∫ path,
    Mcmc.Kernel.stoppedLaggedUnbiasedEstimator observable path ∂pathMeasure
  have hmarginal : Filter.Tendsto
      (fun n => ∫ q, observable q
        ∂Mcmc.Kernel.lawAtTime (Measure.dirac q₀) transition n)
      Filter.atTop (nhds targetMean) := by
    exact Mcmc.Kernel.tendsto_marginalExpectation_to_stoppedEstimator_of_bounded_geometric
      ((Measure.dirac q₀).prod (Measure.dirac q₀)) (Measure.dirac q₀)
      transition coupled (isMeasureCoupling_prod _ _)
      (stickyCoupledHmcRwmhMixture_isCoupling _ _ _ _ _ _ _ _ _)
      observable hmeasurable hbounded C₀ contractionRate hC₀ hrate
      htail (stickyCoupledHmcRwmhMixture_isFaithful _ _ _ _ _ _ _ _ _)
  have hend :=
    Mcmc.Kernel.integral_eq_and_memLp_two_stoppedLaggedUnbiasedEstimator_of_bounded_geometric
      ((Measure.dirac q₀).prod (Measure.dirac q₀)) (Measure.dirac q₀)
      transition coupled (isMeasureCoupling_prod _ _)
      (stickyCoupledHmcRwmhMixture_isCoupling _ _ _ _ _ _ _ _ _)
      observable hmeasurable hB hbounded targetMean hmarginal C₀
      contractionRate hC₀ hrate htail
      (stickyCoupledHmcRwmhMixture_isFaithful _ _ _ _ _ _ _ _ _)
  exact ⟨gamma, C₀, contractionRate, targetMean, hC₀, hrate,
    hmarginal, hend⟩

end Mcmc.Hamiltonian
