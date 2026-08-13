import McmcLean.Hamiltonian.LogisticRegression
import McmcLean.Hamiltonian.QuadraticGaussianXu

/-!
# Xu-theorem packaging for regularized logistic regression

This module supplies the compact energy geometry and theorem-level packaging
which connect the concrete regularized-logistic HMC drift result to the Xu et
al. HMC/RWMH mixture theorem.
-/

open MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace McmcLean.Hamiltonian

open ProbabilityTheory

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Euclidean radius containing the canonical distance-Lyapunov sublevel. -/
noncomputable def regularizedLogisticXuInnerRadius (ell1 : ENNReal) : ℝ :=
  ((Fintype.card ι : ℝ) + 1) * ell1.toReal

/-- Energy threshold strictly above the explicit upper bound on the selected
Lyapunov sublevel. -/
noncomputable def regularizedLogisticXuEll0
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : ℝ) (ell1 : ENNReal) : ℝ :=
  let D := regularizedLogisticXuInnerRadius (ι := ι) ell1
  logisticNegativeLogLikelihood feature label 0 +
    logisticForceBound feature label * D +
    (regularization / 2) * D ^ 2 + 1

/-- A coordinate radius whose quadratic regularization energy lies strictly
above the selected Xu energy threshold. -/
noncomputable def regularizedLogisticXuWitnessRadius
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : ℝ) (ell1 : ENNReal) : ℝ :=
  Real.sqrt
    (2 * (regularizedLogisticXuEll0 feature label regularization ell1 + 1) /
      regularization)

/-- Compact Euclidean region containing both the Lyapunov sublevel and a
point whose regularized-logistic potential exceeds `ell0`. -/
noncomputable def regularizedLogisticXuRegion
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : ℝ) (ell1 : ENNReal) : Set (Position ι) :=
  {q | euclideanNorm q ≤
    regularizedLogisticXuWitnessRadius feature label regularization ell1 + 1}

theorem regularizedLogisticPotential_nonneg
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : ℝ) (hregularization : 0 ≤ regularization)
    (q : Position ι) :
    0 ≤ regularizedLogisticPotential feature label regularization q := by
  unfold regularizedLogisticPotential kineticEnergy
  exact add_nonneg (logisticNegativeLogLikelihood_nonneg feature label q)
    (mul_nonneg hregularization (by positivity))

theorem regularizedLogisticXuEll0_gt_origin
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : ℝ) (hregularization : 0 ≤ regularization)
    (ell1 : ENNReal) :
    regularizedLogisticPotential feature label regularization 0 <
      regularizedLogisticXuEll0 feature label regularization ell1 := by
  let D := regularizedLogisticXuInnerRadius (ι := ι) ell1
  have hD : 0 ≤ D := by
    dsimp only [D, regularizedLogisticXuInnerRadius]
    positivity
  have hB := logisticForceBound_nonneg feature label
  unfold regularizedLogisticPotential
  rw [show kineticEnergy (0 : Position ι) = 0 by simp [kineticEnergy]]
  simp only [mul_zero, add_zero]
  unfold regularizedLogisticXuEll0
  dsimp only
  have hD' : 0 ≤ regularizedLogisticXuInnerRadius (ι := ι) ell1 := by
    unfold regularizedLogisticXuInnerRadius
    positivity
  nlinarith [mul_nonneg hB hD',
    mul_nonneg hregularization (sq_nonneg
      (regularizedLogisticXuInnerRadius (ι := ι) ell1))]

theorem regularizedLogisticXuWitnessRadius_pos
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : ℝ) (hregularization : 0 < regularization)
    (ell1 : ENNReal) :
    0 < regularizedLogisticXuWitnessRadius feature label regularization ell1 := by
  unfold regularizedLogisticXuWitnessRadius
  apply Real.sqrt_pos.2
  apply div_pos
  · have hell := regularizedLogisticXuEll0_gt_origin feature label
      regularization hregularization.le ell1
    have horigin := regularizedLogisticPotential_nonneg feature label
      regularization hregularization.le 0
    nlinarith
  · exact hregularization

theorem regularizedLogisticXuInnerRadius_lt_witnessRadius
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : ℝ) (hregularization : 0 < regularization)
    (ell1 : ENNReal) :
    regularizedLogisticXuInnerRadius (ι := ι) ell1 <
      regularizedLogisticXuWitnessRadius feature label regularization ell1 := by
  let D := regularizedLogisticXuInnerRadius (ι := ι) ell1
  let E := regularizedLogisticXuEll0 feature label regularization ell1
  have hD : 0 ≤ D := by dsimp only [D, regularizedLogisticXuInnerRadius]; positivity
  have hEorigin := regularizedLogisticXuEll0_gt_origin feature label
    regularization hregularization.le ell1
  have harg : 0 ≤ 2 * (E + 1) / regularization := by
    have horigin := regularizedLogisticPotential_nonneg feature label
      regularization hregularization.le 0
    apply div_nonneg
    · dsimp only [E]
      nlinarith
    · exact hregularization.le
  apply (sq_lt_sq₀ hD (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt harg]
  dsimp only [E, regularizedLogisticXuEll0, D]
  have hB := logisticForceBound_nonneg feature label
  have hnll := logisticNegativeLogLikelihood_nonneg feature label 0
  apply (lt_div_iff₀ hregularization).2
  nlinarith [mul_nonneg hB hD]

/-- The selected canonical Lyapunov sublevel lies in the explicit compact
logistic region and below its selected energy threshold. -/
theorem regularizedLogistic_xuSublevel_subset
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : ℝ) (hregularization : 0 < regularization)
    {ell1 : ENNReal} (hell1Top : ell1 ≠ ⊤) :
    {q : Position ι | standardDistanceLyapunov q ≤ ell1} ⊆
      regularizedLogisticXuRegion feature label regularization ell1 ∩
        {q | regularizedLogisticPotential feature label regularization q ≤
          regularizedLogisticXuEll0 feature label regularization ell1} := by
  intro q hq
  let D := regularizedLogisticXuInnerRadius (ι := ι) ell1
  have hellNonneg : 0 ≤ ell1.toReal := ENNReal.toReal_nonneg
  have hqReal := ENNReal.toReal_mono hell1Top hq
  have hVReal : (standardDistanceLyapunov q).toReal = 1 + dist q 0 := by
    rw [standardDistanceLyapunov, ENNReal.toReal_ofReal]
    positivity
  rw [hVReal] at hqReal
  have hdist : dist q 0 ≤ ell1.toReal := by linarith
  have hnormBase := euclideanNorm_sub_le_card_succ_mul_dist q 0
  have hnorm : euclideanNorm q ≤ D := by
    calc
      euclideanNorm q ≤ ((Fintype.card ι : ℝ) + 1) * dist q 0 := by
        simpa only [sub_zero] using hnormBase
      _ ≤ ((Fintype.card ι : ℝ) + 1) * ell1.toReal := by gcongr
      _ = D := rfl
  have hD : 0 ≤ D := le_trans (euclideanNorm_nonneg q) hnorm
  constructor
  · change euclideanNorm q ≤
      regularizedLogisticXuWitnessRadius feature label regularization ell1 + 1
    exact hnorm.trans (by
      have hw := regularizedLogisticXuInnerRadius_lt_witnessRadius feature label
        regularization hregularization ell1
      linarith)
  · have hnll := logisticNegativeLogLikelihood_le_origin_add feature label q
    have hsq : squaredEuclideanNorm q ≤ D ^ 2 := by
      rw [← euclideanNorm_sq]
      exact (sq_le_sq₀ (euclideanNorm_nonneg q) hD).2 hnorm
    change regularizedLogisticPotential feature label regularization q ≤ _
    unfold regularizedLogisticPotential
    have hkinetic : kineticEnergy q = (1 / 2 : ℝ) * squaredEuclideanNorm q := by
      unfold kineticEnergy squaredEuclideanNorm euclideanInner
      simp only [pow_two]
    rw [hkinetic]
    dsimp only [regularizedLogisticXuEll0, D]
    have hforceMul := mul_le_mul_of_nonneg_left hnorm
      (logisticForceBound_nonneg feature label)
    have hregMul := mul_le_mul_of_nonneg_left hsq hregularization.le
    nlinarith

theorem isCompact_regularizedLogisticXuRegion
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : ℝ) (ell1 : ENNReal) :
    IsCompact (regularizedLogisticXuRegion feature label regularization ell1) := by
  let R := regularizedLogisticXuWitnessRadius feature label regularization ell1 + 1
  have hclosed : IsClosed {q : Position ι | euclideanNorm q ≤ R} :=
    isClosed_le continuous_euclideanNorm continuous_const
  have hsubset : {q : Position ι | euclideanNorm q ≤ R} ⊆
      Metric.closedBall (0 : Position ι) R := by
    intro q hq
    rw [Metric.mem_closedBall]
    have hd : dist q 0 ≤ euclideanNorm q := by
      simpa only [sub_zero] using dist_le_euclideanNorm_sub q 0
    exact hd.trans hq
  exact (isCompact_closedBall (0 : Position ι) R).of_isClosed_subset
    hclosed hsubset

theorem zero_mem_regularizedLogisticXuRegion
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : ℝ) (hregularization : 0 < regularization)
    (ell1 : ENNReal) :
    (0 : Position ι) ∈
      regularizedLogisticXuRegion feature label regularization ell1 := by
  change euclideanNorm (0 : Position ι) ≤
    regularizedLogisticXuWitnessRadius feature label regularization ell1 + 1
  rw [euclideanNorm_zero]
  have hw := regularizedLogisticXuWitnessRadius_pos feature label regularization
    hregularization ell1
  linarith

section NonemptyDimension

variable [Nonempty ι]

/-- A concrete one-coordinate point above the selected logistic energy. -/
noncomputable def regularizedLogisticXuWitness
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : ℝ) (ell1 : ENNReal) : Position ι := by
  classical
  let i0 : ι := Classical.choice inferInstance
  exact fun i => if i = i0 then
    regularizedLogisticXuWitnessRadius feature label regularization ell1 else 0

theorem kineticEnergy_regularizedLogisticXuWitness
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : ℝ) (ell1 : ENNReal) :
    kineticEnergy
        (regularizedLogisticXuWitness feature label regularization ell1) =
      (1 / 2 : ℝ) *
        regularizedLogisticXuWitnessRadius feature label regularization ell1 ^ 2 := by
  classical
  unfold kineticEnergy regularizedLogisticXuWitness
  simp

theorem euclideanNorm_regularizedLogisticXuWitness
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : ℝ) (hregularization : 0 < regularization)
    (ell1 : ENNReal) :
    euclideanNorm
        (regularizedLogisticXuWitness feature label regularization ell1) =
      regularizedLogisticXuWitnessRadius feature label regularization ell1 := by
  have hw := regularizedLogisticXuWitnessRadius_pos feature label regularization
    hregularization ell1
  apply (sq_eq_sq₀ (euclideanNorm_nonneg _) hw.le).mp
  rw [euclideanNorm_sq]
  unfold squaredEuclideanNorm euclideanInner regularizedLogisticXuWitness
  classical
  simp
  ring

theorem regularizedLogisticXuWitness_mem_region
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : ℝ) (hregularization : 0 < regularization)
    (ell1 : ENNReal) :
    regularizedLogisticXuWitness feature label regularization ell1 ∈
      regularizedLogisticXuRegion feature label regularization ell1 := by
  change euclideanNorm
      (regularizedLogisticXuWitness feature label regularization ell1) ≤
    regularizedLogisticXuWitnessRadius feature label regularization ell1 + 1
  rw [euclideanNorm_regularizedLogisticXuWitness feature label regularization
    hregularization ell1]
  linarith

theorem regularizedLogisticPotential_witness_gt_ell0
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : ℝ) (hregularization : 0 < regularization)
    (ell1 : ENNReal) :
    regularizedLogisticXuEll0 feature label regularization ell1 <
      regularizedLogisticPotential feature label regularization
        (regularizedLogisticXuWitness feature label regularization ell1) := by
  let E := regularizedLogisticXuEll0 feature label regularization ell1
  let t := regularizedLogisticXuWitnessRadius feature label regularization ell1
  have harg : 0 ≤ 2 * (E + 1) / regularization := by
    have hEorigin := regularizedLogisticXuEll0_gt_origin feature label
      regularization hregularization.le ell1
    have horigin := regularizedLogisticPotential_nonneg feature label
      regularization hregularization.le 0
    apply div_nonneg
    · dsimp only [E]
      nlinarith
    · exact hregularization.le
  have htSq : t ^ 2 = 2 * (E + 1) / regularization := by
    dsimp only [t, regularizedLogisticXuWitnessRadius]
    exact Real.sq_sqrt harg
  have hnll := logisticNegativeLogLikelihood_nonneg feature label
    (regularizedLogisticXuWitness feature label regularization ell1)
  unfold regularizedLogisticPotential
  rw [kineticEnergy_regularizedLogisticXuWitness]
  dsimp only [E, t] at htSq ⊢
  have hmul := congrArg (fun x : ℝ => regularization / 2 * x) htSq
  field_simp at hmul
  nlinarith

/-- The explicit compact region has potential values strictly below and
strictly above the selected Xu energy level. -/
theorem regularizedLogistic_xuEnergyRange
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : ℝ) (hregularization : 0 < regularization)
    (ell1 : ENNReal) :
    sInf (regularizedLogisticPotential feature label regularization ''
        regularizedLogisticXuRegion feature label regularization ell1) <
      regularizedLogisticXuEll0 feature label regularization ell1 ∧
    regularizedLogisticXuEll0 feature label regularization ell1 <
      sSup (regularizedLogisticPotential feature label regularization ''
        regularizedLogisticXuRegion feature label regularization ell1) := by
  let potential := regularizedLogisticPotential feature label regularization
  let S := regularizedLogisticXuRegion feature label regularization ell1
  have hcompact : IsCompact S :=
    isCompact_regularizedLogisticXuRegion feature label regularization ell1
  have hcontinuous : Continuous potential :=
    (contDiff_regularizedLogisticPotential feature label regularization).continuous
  have himageCompact : IsCompact (potential '' S) := hcompact.image hcontinuous
  have hbddBelow : BddBelow (potential '' S) := by
    refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨q, _hq, rfl⟩
    exact regularizedLogisticPotential_nonneg feature label regularization
      hregularization.le q
  have hzero : potential 0 ∈ potential '' S :=
    ⟨0, zero_mem_regularizedLogisticXuRegion feature label regularization
      hregularization ell1, rfl⟩
  have hwitness : potential
      (regularizedLogisticXuWitness feature label regularization ell1) ∈
      potential '' S :=
    ⟨regularizedLogisticXuWitness feature label regularization ell1,
      regularizedLogisticXuWitness_mem_region feature label regularization
        hregularization ell1, rfl⟩
  constructor
  · exact (csInf_le hbddBelow hzero).trans_lt
      (regularizedLogisticXuEll0_gt_origin feature label regularization
        hregularization.le ell1)
  · exact (regularizedLogisticPotential_witness_gt_ell0 feature label
      regularization hregularization ell1).trans_le
        (le_csSup himageCompact.bddAbove hwitness)

/-- Complete compact energy geometry required by Xu's drift structure. -/
theorem regularizedLogistic_xuSublevelGeometry
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : ℝ) (hregularization : 0 < regularization)
    {ell1 : ENNReal} (hell1Top : ell1 ≠ ⊤) :
    {q : Position ι | standardDistanceLyapunov q ≤ ell1} ⊆
        regularizedLogisticXuRegion feature label regularization ell1 ∩
          {q | regularizedLogisticPotential feature label regularization q ≤
            regularizedLogisticXuEll0 feature label regularization ell1} ∧
      sInf (regularizedLogisticPotential feature label regularization ''
          regularizedLogisticXuRegion feature label regularization ell1) <
        regularizedLogisticXuEll0 feature label regularization ell1 ∧
      regularizedLogisticXuEll0 feature label regularization ell1 <
        sSup (regularizedLogisticPotential feature label regularization ''
          regularizedLogisticXuRegion feature label regularization ell1) := by
  exact ⟨regularizedLogistic_xuSublevel_subset feature label regularization
      hregularization hell1Top,
    regularizedLogistic_xuEnergyRange feature label regularization
      hregularization ell1⟩

/-- Assemble Xu's drift assumptions for the concrete regularized-logistic
HMC and Gaussian-RWMH branches from already selected scalar and geometric
parameters. -/
noncomputable def regularizedLogistic_xuTheorem41DriftAssumptions
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : NNReal) (hregularization : 0 < regularization)
    (ε : ℝ) (hcancel : ε ^ 2 * (regularization : ℝ) = 2)
    (variance : NNReal) (hvariance : variance ≠ 0)
    (q₀ : Position ι)
    (γ : Set.Ioo (0 : NNReal) 1) (ell1 : ENNReal)
    (hell1 : 1 < ell1) (hell1Top : ell1 ≠ ⊤)
    (hlambda : xuTheorem41Lambda0 γ (1 / 2)
      (2 + McmcLean.Kernel.isotropicGaussianFirstNormMoment
        (ι := ι) variance) < 1)
    (hscalar : xuTheorem41PairedRate γ (1 / 2)
      (regularizedLogisticDriftAllowance feature label regularization ε)
      (2 + McmcLean.Kernel.isotropicGaussianFirstNormMoment
        (ι := ι) variance) ell1 < 1)
    (hsublevel : {q : Position ι | standardDistanceLyapunov q ≤ ell1} ⊆
      regularizedLogisticXuRegion feature label regularization ell1 ∩
        {q | regularizedLogisticPotential feature label regularization q ≤
          regularizedLogisticXuEll0 feature label regularization ell1})
    (hell0Inf : sInf (regularizedLogisticPotential feature label regularization ''
        regularizedLogisticXuRegion feature label regularization ell1) <
      regularizedLogisticXuEll0 feature label regularization ell1)
    (hell0Sup : regularizedLogisticXuEll0 feature label regularization ell1 <
      sSup (regularizedLogisticPotential feature label regularization ''
        regularizedLogisticXuRegion feature label regularization ell1)) :
    XuTheorem41DriftAssumptions γ
      (standardPositionMultinomialHMC
        (regularizedLogisticPotential feature label regularization)
        (regularizedLogisticGradient feature label regularization) ε 1
        (contDiff_regularizedLogisticPotential feature label
          regularization).continuous.measurable
        (regularPotential_regularizedLogistic feature label regularization
          hregularization).contDiff_one_gradient.continuous.measurable)
      (McmcLean.Kernel.euclideanGaussianRandomWalkMetropolisHastings
        (positionBoltzmannWeight
          (regularizedLogisticPotential feature label regularization))
        variance hvariance)
      (Measure.dirac q₀)
      (regularizedLogisticPotential feature label regularization)
      (regularizedLogisticXuRegion feature label regularization ell1) := by
  refine
    { V := standardDistanceLyapunov
      driftCoefficient := 1 / 2
      driftAllowance :=
        regularizedLogisticDriftAllowance feature label regularization ε
      growthCoefficient := 2 +
        McmcLean.Kernel.isotropicGaussianFirstNormMoment (ι := ι) variance
      ell0 := regularizedLogisticXuEll0 feature label regularization ell1
      ell1 := ell1
      measurable_V := measurable_standardDistanceLyapunov
      one_le_V := one_le_standardDistanceLyapunov
      driftCoefficient_pos := by norm_num
      driftCoefficient_lt_one := by norm_num
      driftAllowance_ne_top :=
        regularizedLogisticDriftAllowance_ne_top feature label regularization ε
      growthCoefficient_pos :=
        standardDistanceLyapunov_gaussianRwmh_growthCoefficient_pos variance
      hmc_drift := regularizedLogistic_hmc_drift feature label regularization
        hregularization ε hcancel
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
  exact standardDistanceLyapunov_gaussianRwmh_growth
    (positionBoltzmannWeight
      (regularizedLogisticPotential feature label regularization))
    (measurable_positionBoltzmannWeight
      (contDiff_regularizedLogisticPotential feature label
        regularization).continuous.measurable)
    variance hvariance x

/-- Every nonempty finite-dimensional regularized-logistic target admits
selected mixture and threshold parameters satisfying all fields of Xu's
Theorem 4.1 drift structure at a cancellation step. -/
theorem exists_regularizedLogistic_xuTheorem41DriftAssumptions
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : NNReal) (hregularization : 0 < regularization)
    (ε : ℝ) (hcancel : ε ^ 2 * (regularization : ℝ) = 2)
    (variance : NNReal) (hvariance : variance ≠ 0)
    (q₀ : Position ι) :
    ∃ (γ : Set.Ioo (0 : NNReal) 1) (ell1 : ENNReal),
      Nonempty {h : XuTheorem41DriftAssumptions γ
        (standardPositionMultinomialHMC
          (regularizedLogisticPotential feature label regularization)
          (regularizedLogisticGradient feature label regularization) ε 1
          (contDiff_regularizedLogisticPotential feature label
            regularization).continuous.measurable
          (regularPotential_regularizedLogistic feature label regularization
            hregularization).contDiff_one_gradient.continuous.measurable)
        (McmcLean.Kernel.euclideanGaussianRandomWalkMetropolisHastings
          (positionBoltzmannWeight
            (regularizedLogisticPotential feature label regularization))
          variance hvariance)
        (Measure.dirac q₀)
        (regularizedLogisticPotential feature label regularization)
        (regularizedLogisticXuRegion feature label regularization ell1) //
          h.V = standardDistanceLyapunov} := by
  obtain ⟨γ, ell1, hlambda, hell1, hell1Top, hscalar⟩ :=
    exists_standardQuadratic_xuScalarParameters
      (ι := ι) (1 / 2)
      (regularizedLogisticDriftAllowance feature label regularization ε)
      (by norm_num)
      (regularizedLogisticDriftAllowance_ne_top feature label regularization ε)
      variance hvariance
  obtain ⟨hsublevel, hell0Inf, hell0Sup⟩ :=
    regularizedLogistic_xuSublevelGeometry feature label regularization
      hregularization hell1Top
  let h := regularizedLogistic_xuTheorem41DriftAssumptions feature label
    regularization hregularization ε hcancel variance hvariance q₀ γ ell1
    hell1 hell1Top hlambda hscalar hsublevel hell0Inf hell0Sup
  refine ⟨γ, ell1, ⟨⟨h, ?_⟩⟩⟩
  rfl

/-- Fully instantiated exact lag-one geometric meeting tail for the concrete
finite-data regularized-logistic multinomial-HMC/Gaussian-RWMH mixture. Both
algorithms, their faithful coupling, drift, energy geometry, and compact
exact-meeting small set are supplied internally. -/
theorem exists_geometric_exactLagOneMeetingTail_regularizedLogistic
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : NNReal) (hregularization : 0 < regularization)
    (ε : ℝ) (hcancel : ε ^ 2 * (regularization : ℝ) = 2)
    (variance : NNReal) (hvariance : variance ≠ 0)
    (q₀ : Position ι) :
    ∃ (γ : Set.Ioo (0 : NNReal) 1) (C₀ contractionRate : ENNReal),
      C₀ ≠ ⊤ ∧ contractionRate < 1 ∧
        ∀ n : ℕ,
          McmcLean.Kernel.exactMeetingTail
            (McmcLean.Kernel.pathLaw
              (McmcLean.Kernel.laggedInitialMeasure
                ((Measure.dirac q₀).prod (Measure.dirac q₀))
                (hmcRwmhMixture (xuTheorem41HmcWeight γ)
                  (regularizedLogisticPotential feature label regularization)
                  (regularizedLogisticGradient feature label regularization)
                  ε 1
                  (contDiff_regularizedLogisticPotential feature label
                    regularization).continuous.measurable
                  (regularPotential_regularizedLogistic feature label
                    regularization hregularization).contDiff_one_gradient.continuous.measurable
                  variance hvariance))
              (stickyCoupledHmcRwmhMixture (xuTheorem41HmcWeight γ)
                (regularizedLogisticPotential feature label regularization)
                (regularizedLogisticGradient feature label regularization)
                ε 1
                (contDiff_regularizedLogisticPotential feature label
                  regularization).continuous.measurable
                (regularPotential_regularizedLogistic feature label
                  regularization hregularization).contDiff_one_gradient.continuous.measurable
                variance hvariance)) n ≤
            C₀ * contractionRate ^ n := by
  obtain ⟨γ, ell1, ⟨hspecial⟩⟩ :=
    exists_regularizedLogistic_xuTheorem41DriftAssumptions feature label
      regularization hregularization ε hcancel variance hvariance q₀
  let h := hspecial.1
  have hV : h.V = standardDistanceLyapunov := hspecial.2
  have hinitial : IsMeasureCoupling
      ((Measure.dirac q₀).prod (Measure.dirac q₀))
      (Measure.dirac q₀) (Measure.dirac q₀) :=
    isMeasureCoupling_prod _ _
  have hcompact := h.isCompact_pairedSublevel_of_V_eq_standardDistance hV
  have hnonempty := h.nonempty_pairedSublevel_of_V_eq_standardDistance hV
  let A : Set (Position ι) := Metric.closedBall 0 1
  have hAcompact : IsCompact A := by
    dsimp only [A]
    exact isCompact_closedBall 0 1
  have hAnonempty : A.Nonempty := ⟨0, by simp [A]⟩
  have hAmeas : MeasurableSet A := hAcompact.measurableSet
  have hAvolume : 0 < volume A := by
    dsimp only [A]
    exact Metric.measure_closedBall_pos volume 0 (by norm_num)
  obtain ⟨C₀, contractionRate, hC₀, hrate, htail⟩ :=
    h.exists_geometric_exactLagOneMeetingTail_stickyHmcRwmh γ
      (regularizedLogisticPotential feature label regularization)
      (regularizedLogisticGradient feature label regularization) ε 1
      (contDiff_regularizedLogisticPotential feature label
        regularization).continuous
      (regularPotential_regularizedLogistic feature label regularization
        hregularization).contDiff_one_gradient.continuous.measurable
      variance hvariance (Measure.dirac q₀)
      (regularizedLogisticXuRegion feature label regularization ell1)
      ((Measure.dirac q₀).prod (Measure.dirac q₀)) hinitial
      hcompact hnonempty hAcompact hAnonempty hAmeas hAvolume
  exact ⟨γ, C₀, contractionRate, hC₀, hrate, htail⟩

/-- Concrete regularized-logistic bounded-observable estimator endpoint. The
actual HMC/RWMH mixture, sticky coupling, meeting tail, and finite variance
are discharged; only marginal expectation convergence from `q₀` is exposed. -/
theorem exists_regularizedLogistic_boundedEstimator_of_marginal_convergence
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : NNReal) (hregularization : 0 < regularization)
    (ε : ℝ) (hcancel : ε ^ 2 * (regularization : ℝ) = 2)
    (variance : NNReal) (hvariance : variance ≠ 0)
    (q₀ : Position ι) (observable : Position ι → ℝ)
    (hmeasurable : Measurable observable) {B : ℝ} (hB : 0 ≤ B)
    (hbounded : ∀ q, ‖observable q‖ ≤ B) (targetMean : ℝ) :
    ∃ (γ : Set.Ioo (0 : NNReal) 1) (C₀ contractionRate : ENNReal),
      C₀ ≠ ⊤ ∧ contractionRate < 1 ∧
      let transition := hmcRwmhMixture (xuTheorem41HmcWeight γ)
        (regularizedLogisticPotential feature label regularization)
        (regularizedLogisticGradient feature label regularization) ε 1
        (contDiff_regularizedLogisticPotential feature label
          regularization).continuous.measurable
        (regularPotential_regularizedLogistic feature label regularization
          hregularization).contDiff_one_gradient.continuous.measurable
        variance hvariance
      let coupled := stickyCoupledHmcRwmhMixture (xuTheorem41HmcWeight γ)
        (regularizedLogisticPotential feature label regularization)
        (regularizedLogisticGradient feature label regularization) ε 1
        (contDiff_regularizedLogisticPotential feature label
          regularization).continuous.measurable
        (regularPotential_regularizedLogistic feature label regularization
          hregularization).contDiff_one_gradient.continuous.measurable
        variance hvariance
      Filter.Tendsto
          (fun n => ∫ q, observable q
            ∂McmcLean.Kernel.lawAtTime (Measure.dirac q₀) transition n)
          Filter.atTop (nhds targetMean) →
        (∫ path, McmcLean.Kernel.stoppedLaggedUnbiasedEstimator observable path
          ∂McmcLean.Kernel.pathLaw
            (McmcLean.Kernel.laggedInitialMeasure
              ((Measure.dirac q₀).prod (Measure.dirac q₀)) transition)
            coupled) = targetMean ∧
          MemLp (McmcLean.Kernel.stoppedLaggedUnbiasedEstimator observable) 2
            (McmcLean.Kernel.pathLaw
              (McmcLean.Kernel.laggedInitialMeasure
                ((Measure.dirac q₀).prod (Measure.dirac q₀)) transition)
              coupled) := by
  obtain ⟨γ, C₀, contractionRate, hC₀, hrate, htail⟩ :=
    exists_geometric_exactLagOneMeetingTail_regularizedLogistic feature label
      regularization hregularization ε hcancel variance hvariance q₀
  refine ⟨γ, C₀, contractionRate, hC₀, hrate, ?_⟩
  dsimp only
  intro hmarginal
  apply McmcLean.Kernel.integral_eq_and_memLp_two_stoppedLaggedUnbiasedEstimator_of_bounded_geometric
      ((Measure.dirac q₀).prod (Measure.dirac q₀)) (Measure.dirac q₀)
      (hmcRwmhMixture (xuTheorem41HmcWeight γ)
        (regularizedLogisticPotential feature label regularization)
        (regularizedLogisticGradient feature label regularization) ε 1
        (contDiff_regularizedLogisticPotential feature label
          regularization).continuous.measurable
        (regularPotential_regularizedLogistic feature label regularization
          hregularization).contDiff_one_gradient.continuous.measurable
        variance hvariance)
      (stickyCoupledHmcRwmhMixture (xuTheorem41HmcWeight γ)
        (regularizedLogisticPotential feature label regularization)
        (regularizedLogisticGradient feature label regularization) ε 1
        (contDiff_regularizedLogisticPotential feature label
          regularization).continuous.measurable
        (regularPotential_regularizedLogistic feature label regularization
          hregularization).contDiff_one_gradient.continuous.measurable
        variance hvariance)
      (isMeasureCoupling_prod _ _)
      (stickyCoupledHmcRwmhMixture_isCoupling _ _ _ _ _ _ _ _ _)
      observable hmeasurable hB hbounded targetMean hmarginal
      C₀ contractionRate hC₀ hrate htail
      (stickyCoupledHmcRwmhMixture_isFaithful _ _ _ _ _ _ _ _ _)

end NonemptyDimension

end McmcLean.Hamiltonian
