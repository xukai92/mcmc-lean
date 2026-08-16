import Mcmc.Executable.Continuous.GaussianSoftAbs
import Mcmc.Kernel.RefreshAugmented

/-!
# Geometric convergence for refresh-augmented Gaussian SoftAbs GR-HMC

This module turns the exact invariance theorem for the concrete Gaussian
diagonal-SoftAbs multinomial GR-HMC transition into an eventwise geometric
convergence theorem by adding an independent draw from the normalized target.
The theorem concerns this explicitly augmented algorithm; it does not assert
a convergence rate for the unrefreshed GR-HMC transition.
-/

namespace Mcmc.Executable.Continuous

open Mcmc.Hamiltonian Mcmc.Relativistic MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- The unnormalized position target of the Gaussian SoftAbs client. -/
noncomputable abbrev gaussianSoftAbsPositionTarget : Measure (Position ι) :=
  generalRelativisticPositionTarget (gaussianSoftAbsPotential (ι := ι))
    1 1 (by norm_num) (by norm_num)

omit [Nonempty ι] [DecidableEq ι] in
/-- The Gaussian position Boltzmann measure is the same unnormalized
quadratic measure as the standard kinetic Boltzmann measure. -/
theorem gaussianSoftAbs_positionBoltzmannTarget_eq_kinetic :
    positionBoltzmannTarget (gaussianSoftAbsPotential (ι := ι)) =
      (kineticBoltzmannTarget : Measure (Momentum ι)) := by
  unfold positionBoltzmannTarget kineticBoltzmannTarget
  congr 1
  funext q
  unfold positionBoltzmannWeight kineticBoltzmannWeight
    gaussianSoftAbsPotential kineticEnergy squaredEuclideanNorm euclideanInner
  congr 2
  ring_nf

omit [Nonempty ι] [DecidableEq ι] in
/-- The quadratic Boltzmann measure has finite total mass, derived from the
already normalized standard product Gaussian. -/
theorem gaussianSoftAbs_positionBoltzmannTarget_lt_top :
    positionBoltzmannTarget (gaussianSoftAbsPotential (ι := ι)) Set.univ < ∞ := by
  rw [gaussianSoftAbs_positionBoltzmannTarget_eq_kinetic]
  rw [lt_top_iff_ne_top]
  intro htop
  have hprefactor : standardMomentumPrefactor (ι := ι) ≠ 0 := by
    unfold standardMomentumPrefactor standardGaussianPrefactor
    apply Finset.prod_ne_zero_iff.mpr
    intro i _hi
    rw [ENNReal.ofReal_ne_zero_iff]
    positivity
  have huniv := congrArg (fun μ : Measure (Momentum ι) => μ Set.univ)
    (standardMomentumMeasure_eq_smul_kinetic (ι := ι))
  have hscaled : standardMomentumPrefactor (ι := ι) • (∞ : ENNReal) = ∞ := by
    simp [hprefactor]
  rw [measure_univ, Measure.smul_apply, htop, hscaled] at huniv
  exact ENNReal.one_ne_top huniv

instance gaussianSoftAbsPositionTarget.instIsFiniteMeasure :
    IsFiniteMeasure (gaussianSoftAbsPositionTarget (ι := ι)) := by
  unfold gaussianSoftAbsPositionTarget generalRelativisticPositionTarget
  constructor
  rw [Measure.coe_nnreal_smul_apply]
  exact ENNReal.mul_lt_top
    ENNReal.coe_lt_top
    gaussianSoftAbs_positionBoltzmannTarget_lt_top

omit [DecidableEq ι] in
/-- The Gaussian SoftAbs target has positive mass. -/
theorem gaussianSoftAbsPositionTarget_ne_zero :
    gaussianSoftAbsPositionTarget (ι := ι) ≠ 0 := by
  unfold gaussianSoftAbsPositionTarget generalRelativisticPositionTarget
    positionBoltzmannTarget
  rw [← Measure.coe_nnreal_smul]
  intro hsmul
  rcases Measure.ennreal_smul_eq_zero.mp hsmul with hpartition | hzero
  · have hpartition_ne :
        ((euclideanRelativisticMomentumPartition ι 1 1
          (by norm_num) (by norm_num) : NNReal) : ENNReal) ≠ 0 := by
      exact_mod_cast euclideanRelativisticMomentumPartition_ne_zero ι 1 1
        (by norm_num) (by norm_num)
    exact hpartition_ne hpartition
  ·
    have hweight := (withDensity_eq_zero_iff
      (measurable_positionBoltzmannWeight
        (measurable_gaussianSoftAbsPotential (ι := ι))).aemeasurable).mp hzero
    haveI : (ae (volume : Measure (Position ι))).NeBot := inferInstance
    obtain ⟨q, hq⟩ := hweight.exists
    exact (positionBoltzmannWeight_pos
      (gaussianSoftAbsPotential (ι := ι)) q).ne' hq

/-- The concrete multinomial Gaussian SoftAbs GR-HMC transition. -/
noncomputable abbrev gaussianSoftAbsMultinomialTransition (ε : ℝ) (L : ℕ) :=
  positionMultinomialGRHMC (gaussianSoftAbsPotential (ι := ι))
    (gaussianSoftAbsMetric (ι := ι)) 1 1 (by norm_num) (by norm_num)
    (gaussianSoftAbsSelection (ι := ι)) gaussianSoftAbsSelection_valid
    (measurable_diagonalSoftAbs_generalRelativisticHamiltonian
      (gaussianSoftAbsPotential (ι := ι))
      (measurable_gaussianSoftAbsPotential (ι := ι))
      1 (by norm_num) (gaussianHessianDiagonal (ι := ι))
      (measurable_gaussianHessianDiagonal (ι := ι)) 1 1)
    (diagonalSoftAbs_isMeasurableRiemannianMomentumFamily
      1 (by norm_num) (gaussianHessianDiagonal (ι := ι)) 1 1
      (by norm_num) (by norm_num)
      (measurable_gaussianHessianDiagonal (ι := ι))) ε L

/-- Common refreshed-momentum probability of the one-sided interval `(0,1)`
used by the positive Gaussian tail certificate. -/
noncomputable def gaussianSoftAbsPositiveMomentumMass : ENNReal :=
  (riemannianRelativisticMomentumProbability
    (gaussianSoftAbsMetric (ι := Unit)) 1 1 (by norm_num) (by norm_num) 0 :
      Measure (Momentum Unit))
    {p | 0 < p Unit.unit ∧ p Unit.unit < 1}

theorem gaussianSoftAbsPositiveMomentumMass_pos :
    0 < gaussianSoftAbsPositiveMomentumMass := by
  exact gaussianSoftAbsMomentumProbability_unit_Ioo_pos (by norm_num)

/-- Common refreshed-momentum probability of the symmetric one-sided
interval `(-1,0)`. -/
noncomputable def gaussianSoftAbsNegativeMomentumMass : ENNReal :=
  (riemannianRelativisticMomentumProbability
    (gaussianSoftAbsMetric (ι := Unit)) 1 1 (by norm_num) (by norm_num) 0 :
      Measure (Momentum Unit))
    {p | -1 < p Unit.unit ∧ p Unit.unit < 0}

theorem gaussianSoftAbsNegativeMomentumMass_pos :
    0 < gaussianSoftAbsNegativeMomentumMass := by
  exact gaussianSoftAbsMomentumProbability_unit_Ioo_pos (by norm_num)

/-- The refreshed Gaussian SoftAbs momentum lies in expanding symmetric
coordinate intervals with probability tending to one. -/
theorem gaussianSoftAbsMomentumProbability_abs_le_tendsto_one :
    Filter.Tendsto
      (fun R : ℝ =>
        (riemannianRelativisticMomentumProbability
          (gaussianSoftAbsMetric (ι := Unit)) 1 1
          (by norm_num) (by norm_num) 0 : Measure (Momentum Unit))
          {p | |p Unit.unit| ≤ R})
      Filter.atTop (nhds 1) := by
  let μ : Measure (Momentum Unit) :=
    riemannianRelativisticMomentumProbability
      (gaussianSoftAbsMetric (ι := Unit)) 1 1
      (by norm_num) (by norm_num) 0
  let absoluteCoordinate : Momentum Unit → ℝ := fun p => |p Unit.unit|
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have habsolute : Measurable absoluteCoordinate :=
    (measurable_pi_apply Unit.unit).abs
  have ht := tendsto_measure_Iic_atTop (Measure.map absoluteCoordinate μ)
  have hmap (R : ℝ) :
      Measure.map absoluteCoordinate μ (Set.Iic R) =
        μ {p | |p Unit.unit| ≤ R} := by
    rw [Measure.map_apply habsolute measurableSet_Iic]
    rfl
  have huniv : Measure.map absoluteCoordinate μ Set.univ = 1 := by
    rw [Measure.map_apply habsolute MeasurableSet.univ]
    simp
  simpa only [hmap, huniv] using ht

/-- Along the positive position tail, the expanding band used by the exact
energy argument has refreshed-momentum probability tending to one. -/
theorem gaussianSoftAbsMomentumProbability_tail_band_tendsto_one :
    Filter.Tendsto
      (fun q : ℝ =>
        (riemannianRelativisticMomentumProbability
          (gaussianSoftAbsMetric (ι := Unit)) 1 1
          (by norm_num) (by norm_num) 0 : Measure (Momentum Unit))
          {p | |p Unit.unit| ≤ q / 2 - 2})
      Filter.atTop (nhds 1) := by
  apply gaussianSoftAbsMomentumProbability_abs_le_tendsto_one.comp
  simpa [sub_eq_add_neg] using
    (Filter.tendsto_atTop_add_const_right Filter.atTop (-2 : ℝ)
      (Filter.tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2)))

/-- Refreshed-momentum mass of the position-indexed central band used by the
bare-kernel drift argument. -/
noncomputable def gaussianSoftAbsTailBandMass (q : ℝ) : ENNReal :=
  (riemannianRelativisticMomentumProbability
    (gaussianSoftAbsMetric (ι := Unit)) 1 1 (by norm_num) (by norm_num) 0 :
      Measure (Momentum Unit))
    {p | |p Unit.unit| ≤ q / 2 - 2}

theorem gaussianSoftAbsTailBandMass_tendsto_one :
    Filter.Tendsto gaussianSoftAbsTailBandMass Filter.atTop (nhds 1) :=
  gaussianSoftAbsMomentumProbability_tail_band_tendsto_one

/-- The actual position transition inherits the expanding-band inward floor.
-/
theorem gaussianSoftAbsTailBandMass_mul_quarter_le_inward
    (q : Position Unit) :
    gaussianSoftAbsTailBandMass (q Unit.unit) * (4 : ENNReal)⁻¹ ≤
      gaussianSoftAbsMultinomialTransition 1 1 q
        {y | y Unit.unit ≤
          q Unit.unit - gaussianSoftAbsUnitMinSpeed} := by
  let momentumSet : Set (Momentum Unit) :=
    {p | |p Unit.unit| ≤ q Unit.unit / 2 - 2}
  let inward : Set (Position Unit) :=
    {y | y Unit.unit ≤ q Unit.unit - gaussianSoftAbsUnitMinSpeed}
  have hmomentumSet : MeasurableSet momentumSet :=
    measurableSet_le (measurable_pi_apply _).abs measurable_const
  have hinward : MeasurableSet inward :=
    measurableSet_le (measurable_pi_apply _) measurable_const
  have h := momentumMeasure_mul_le_positionMultinomialGRHMC_apply
    gaussianSoftAbsPotential gaussianSoftAbsMetric 1 1
    (by norm_num) (by norm_num) gaussianSoftAbsSelection
    gaussianSoftAbsSelection_valid
    (measurable_diagonalSoftAbs_generalRelativisticHamiltonian
      gaussianSoftAbsPotential measurable_gaussianSoftAbsPotential
      1 (by norm_num) gaussianHessianDiagonal
      measurable_gaussianHessianDiagonal 1 1)
    (diagonalSoftAbs_isMeasurableRiemannianMomentumFamily
      1 (by norm_num) gaussianHessianDiagonal 1 1
      (by norm_num) (by norm_num) measurable_gaussianHessianDiagonal)
    1 1 q hmomentumSet hinward (4 : ENNReal)⁻¹ (by
      intro p hp
      exact quarter_le_gaussianSoftAbsPhaseTransition_inward_of_abs_momentum
        q p hp)
  simpa [momentumSet, inward, gaussianSoftAbsTailBandMass,
    gaussianSoftAbsMultinomialTransition, riemannianMomentumKernel,
    gaussianSoftAbsMomentumProbability_eq_zero] using h

/-- On the expanding central band the actual position transition is
non-outward with probability one, so its unconditional non-outward
probability is at least the band mass. -/
theorem gaussianSoftAbsTailBandMass_le_nonoutward
    (q : Position Unit) :
    gaussianSoftAbsTailBandMass (q Unit.unit) ≤
      gaussianSoftAbsMultinomialTransition 1 1 q
        {y | y Unit.unit ≤ q Unit.unit} := by
  let momentumSet : Set (Momentum Unit) :=
    {p | |p Unit.unit| ≤ q Unit.unit / 2 - 2}
  let nonoutward : Set (Position Unit) :=
    {y | y Unit.unit ≤ q Unit.unit}
  have hmomentumSet : MeasurableSet momentumSet :=
    measurableSet_le (measurable_pi_apply _).abs measurable_const
  have hnonoutward : MeasurableSet nonoutward :=
    measurableSet_le (measurable_pi_apply _) measurable_const
  have h := momentumMeasure_mul_le_positionMultinomialGRHMC_apply
    gaussianSoftAbsPotential gaussianSoftAbsMetric 1 1
    (by norm_num) (by norm_num) gaussianSoftAbsSelection
    gaussianSoftAbsSelection_valid
    (measurable_diagonalSoftAbs_generalRelativisticHamiltonian
      gaussianSoftAbsPotential measurable_gaussianSoftAbsPotential
      1 (by norm_num) gaussianHessianDiagonal
      measurable_gaussianHessianDiagonal 1 1)
    (diagonalSoftAbs_isMeasurableRiemannianMomentumFamily
      1 (by norm_num) gaussianHessianDiagonal 1 1
      (by norm_num) (by norm_num) measurable_gaussianHessianDiagonal)
    1 1 q hmomentumSet hnonoutward 1 (by
      intro p hp
      simpa [nonoutward] using
        gaussianSoftAbsPhaseTransition_nonoutward_of_abs_momentum q p hp)
  simpa [momentumSet, nonoutward, gaussianSoftAbsTailBandMass,
    gaussianSoftAbsMultinomialTransition, riemannianMomentumKernel,
    gaussianSoftAbsMomentumProbability_eq_zero] using h

/-- The actual refreshed, random-origin, two-point position transition has a
uniform positive probability of moving inward by the certified distance on
the positive Gaussian tail. -/
theorem gaussianSoftAbsPositiveMomentumMass_mul_quarter_le_inward
    (q : Position Unit) (hq : 6 ≤ q Unit.unit) :
    gaussianSoftAbsPositiveMomentumMass * (4 : ENNReal)⁻¹ ≤
      gaussianSoftAbsMultinomialTransition 1 1 q
        {y | y Unit.unit ≤
          q Unit.unit - gaussianSoftAbsUnitMinSpeed} := by
  let momentumSet : Set (Momentum Unit) :=
    {p | 0 < p Unit.unit ∧ p Unit.unit < 1}
  let inward : Set (Position Unit) :=
    {y | y Unit.unit ≤ q Unit.unit - gaussianSoftAbsUnitMinSpeed}
  let momentumKernel := riemannianMomentumKernel
    (gaussianSoftAbsMetric (ι := Unit)) 1 1 (by norm_num) (by norm_num)
    (diagonalSoftAbs_isMeasurableRiemannianMomentumFamily
      1 (by norm_num) (gaussianHessianDiagonal (ι := Unit)) 1 1
      (by norm_num) (by norm_num)
      (measurable_gaussianHessianDiagonal (ι := Unit)))
  have hmomentumSet : MeasurableSet momentumSet :=
    (measurableSet_lt measurable_const (measurable_pi_apply _)).inter
      (measurableSet_lt (measurable_pi_apply _) measurable_const)
  have hinward : MeasurableSet inward :=
    measurableSet_le (measurable_pi_apply _) measurable_const
  have hmomentum : momentumKernel q momentumSet =
      gaussianSoftAbsPositiveMomentumMass := by
    dsimp [momentumKernel, gaussianSoftAbsPositiveMomentumMass,
      riemannianMomentumKernel]
    rw [gaussianSoftAbsMomentumProbability_eq_zero]
  rw [← lintegral_indicator_one hinward]
  change gaussianSoftAbsPositiveMomentumMass * (4 : ENNReal)⁻¹ ≤
    ∫⁻ y, inward.indicator (fun _ => (1 : ENNReal)) y
      ∂positionMultinomialGRHMC gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1 (by norm_num) (by norm_num)
        gaussianSoftAbsSelection gaussianSoftAbsSelection_valid
        (measurable_diagonalSoftAbs_generalRelativisticHamiltonian
          gaussianSoftAbsPotential measurable_gaussianSoftAbsPotential
          1 (by norm_num) gaussianHessianDiagonal
          measurable_gaussianHessianDiagonal 1 1)
        (diagonalSoftAbs_isMeasurableRiemannianMomentumFamily
          1 (by norm_num) gaussianHessianDiagonal 1 1
          (by norm_num) (by norm_num) measurable_gaussianHessianDiagonal)
        1 1 q
  rw [lintegral_positionMultinomialGRHMC
    gaussianSoftAbsPotential gaussianSoftAbsMetric 1 1
    (by norm_num) (by norm_num) gaussianSoftAbsSelection
    gaussianSoftAbsSelection_valid
    (measurable_diagonalSoftAbs_generalRelativisticHamiltonian
      gaussianSoftAbsPotential measurable_gaussianSoftAbsPotential
      1 (by norm_num) gaussianHessianDiagonal
      measurable_gaussianHessianDiagonal 1 1)
    (diagonalSoftAbs_isMeasurableRiemannianMomentumFamily
      1 (by norm_num) gaussianHessianDiagonal 1 1
      (by norm_num) (by norm_num) measurable_gaussianHessianDiagonal)
    1 1 (inward.indicator fun _ => (1 : ENNReal))
    (measurable_const.indicator hinward) q]
  change gaussianSoftAbsPositiveMomentumMass * (4 : ENNReal)⁻¹ ≤
    ∫⁻ p, ∫⁻ z, inward.indicator (fun _ => (1 : ENNReal)) z.1
      ∂gaussianSoftAbsPhaseTransition 1 1 (q, p) ∂momentumKernel q
  calc
    gaussianSoftAbsPositiveMomentumMass * (4 : ENNReal)⁻¹ =
        ∫⁻ p, momentumSet.indicator (fun _ => (4 : ENNReal)⁻¹) p
          ∂momentumKernel q := by
      rw [lintegral_indicator_const hmomentumSet, hmomentum]
      ac_rfl
    _ ≤ _ := by
      apply lintegral_mono
      intro p
      by_cases hp : p ∈ momentumSet
      · rw [Set.indicator_of_mem hp]
        change (4 : ENNReal)⁻¹ ≤
          ∫⁻ z, (Prod.fst ⁻¹' inward).indicator
            (1 : PhaseSpace Unit → ENNReal) z
            ∂gaussianSoftAbsPhaseTransition 1 1 (q, p)
        rw [lintegral_indicator_one (measurable_fst hinward)]
        exact quarter_le_gaussianSoftAbsPhaseTransition_inward_of_pos
          q p hq hp.1.le hp.2.le
      · simp [Set.indicator, hp]

/-- Symmetric refreshed position-transition inward probability on the
negative Gaussian tail. -/
theorem gaussianSoftAbsNegativeMomentumMass_mul_quarter_le_inward
    (q : Position Unit) (hq : q Unit.unit ≤ -6) :
    gaussianSoftAbsNegativeMomentumMass * (4 : ENNReal)⁻¹ ≤
      gaussianSoftAbsMultinomialTransition 1 1 q
        {y | q Unit.unit + gaussianSoftAbsUnitMinSpeed ≤ y Unit.unit} := by
  let momentumSet : Set (Momentum Unit) :=
    {p | -1 < p Unit.unit ∧ p Unit.unit < 0}
  let inward : Set (Position Unit) :=
    {y | q Unit.unit + gaussianSoftAbsUnitMinSpeed ≤ y Unit.unit}
  let momentumKernel := riemannianMomentumKernel
    (gaussianSoftAbsMetric (ι := Unit)) 1 1 (by norm_num) (by norm_num)
    (diagonalSoftAbs_isMeasurableRiemannianMomentumFamily
      1 (by norm_num) (gaussianHessianDiagonal (ι := Unit)) 1 1
      (by norm_num) (by norm_num)
      (measurable_gaussianHessianDiagonal (ι := Unit)))
  have hmomentumSet : MeasurableSet momentumSet :=
    (measurableSet_lt measurable_const (measurable_pi_apply _)).inter
      (measurableSet_lt (measurable_pi_apply _) measurable_const)
  have hinward : MeasurableSet inward :=
    measurableSet_le measurable_const (measurable_pi_apply _)
  have hmomentum : momentumKernel q momentumSet =
      gaussianSoftAbsNegativeMomentumMass := by
    dsimp [momentumKernel, gaussianSoftAbsNegativeMomentumMass,
      riemannianMomentumKernel]
    rw [gaussianSoftAbsMomentumProbability_eq_zero]
  rw [← lintegral_indicator_one hinward]
  change gaussianSoftAbsNegativeMomentumMass * (4 : ENNReal)⁻¹ ≤
    ∫⁻ y, inward.indicator (fun _ => (1 : ENNReal)) y
      ∂positionMultinomialGRHMC gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1 (by norm_num) (by norm_num)
        gaussianSoftAbsSelection gaussianSoftAbsSelection_valid
        (measurable_diagonalSoftAbs_generalRelativisticHamiltonian
          gaussianSoftAbsPotential measurable_gaussianSoftAbsPotential
          1 (by norm_num) gaussianHessianDiagonal
          measurable_gaussianHessianDiagonal 1 1)
        (diagonalSoftAbs_isMeasurableRiemannianMomentumFamily
          1 (by norm_num) gaussianHessianDiagonal 1 1
          (by norm_num) (by norm_num) measurable_gaussianHessianDiagonal)
        1 1 q
  rw [lintegral_positionMultinomialGRHMC
    gaussianSoftAbsPotential gaussianSoftAbsMetric 1 1
    (by norm_num) (by norm_num) gaussianSoftAbsSelection
    gaussianSoftAbsSelection_valid
    (measurable_diagonalSoftAbs_generalRelativisticHamiltonian
      gaussianSoftAbsPotential measurable_gaussianSoftAbsPotential
      1 (by norm_num) gaussianHessianDiagonal
      measurable_gaussianHessianDiagonal 1 1)
    (diagonalSoftAbs_isMeasurableRiemannianMomentumFamily
      1 (by norm_num) gaussianHessianDiagonal 1 1
      (by norm_num) (by norm_num) measurable_gaussianHessianDiagonal)
    1 1 (inward.indicator fun _ => (1 : ENNReal))
    (measurable_const.indicator hinward) q]
  change gaussianSoftAbsNegativeMomentumMass * (4 : ENNReal)⁻¹ ≤
    ∫⁻ p, ∫⁻ z, inward.indicator (fun _ => (1 : ENNReal)) z.1
      ∂gaussianSoftAbsPhaseTransition 1 1 (q, p) ∂momentumKernel q
  calc
    gaussianSoftAbsNegativeMomentumMass * (4 : ENNReal)⁻¹ =
        ∫⁻ p, momentumSet.indicator (fun _ => (4 : ENNReal)⁻¹) p
          ∂momentumKernel q := by
      rw [lintegral_indicator_const hmomentumSet, hmomentum]
      ac_rfl
    _ ≤ _ := by
      apply lintegral_mono
      intro p
      by_cases hp : p ∈ momentumSet
      · rw [Set.indicator_of_mem hp]
        change (4 : ENNReal)⁻¹ ≤
          ∫⁻ z, (Prod.fst ⁻¹' inward).indicator
            (1 : PhaseSpace Unit → ENNReal) z
            ∂gaussianSoftAbsPhaseTransition 1 1 (q, p)
        rw [lintegral_indicator_one (measurable_fst hinward)]
        exact quarter_le_gaussianSoftAbsPhaseTransition_inward_of_neg
          q p hq hp.2.le hp.1.le
      · simp [Set.indicator, hp]

/-- Momentum refresh and multinomial selection preserve the relativistic
finite-speed support bound: the user-facing position kernel moves by less
than one almost surely. -/
theorem gaussianSoftAbsMultinomialTransition_unit_position_support
    (q : Position Unit) :
    gaussianSoftAbsMultinomialTransition 1 1 q
      {y | |y Unit.unit - q Unit.unit| < 1} = 1 := by
  let support : Set (Position Unit) :=
    {y | |y Unit.unit - q Unit.unit| < 1}
  have hsupport : MeasurableSet support := by
    exact measurableSet_lt
      (((measurable_pi_apply Unit.unit).sub measurable_const).abs)
      measurable_const
  rw [← lintegral_indicator_one hsupport]
  change (∫⁻ y, support.indicator (fun _ => (1 : ENNReal)) y
      ∂positionMultinomialGRHMC gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1 (by norm_num) (by norm_num)
        gaussianSoftAbsSelection gaussianSoftAbsSelection_valid
        (measurable_diagonalSoftAbs_generalRelativisticHamiltonian
          gaussianSoftAbsPotential measurable_gaussianSoftAbsPotential
          1 (by norm_num) gaussianHessianDiagonal
          measurable_gaussianHessianDiagonal 1 1)
        (diagonalSoftAbs_isMeasurableRiemannianMomentumFamily
          1 (by norm_num) gaussianHessianDiagonal 1 1
          (by norm_num) (by norm_num) measurable_gaussianHessianDiagonal)
        1 1 q) = 1
  rw [lintegral_positionMultinomialGRHMC
    gaussianSoftAbsPotential gaussianSoftAbsMetric 1 1
    (by norm_num) (by norm_num) gaussianSoftAbsSelection
    gaussianSoftAbsSelection_valid
    (measurable_diagonalSoftAbs_generalRelativisticHamiltonian
      gaussianSoftAbsPotential measurable_gaussianSoftAbsPotential
      1 (by norm_num) gaussianHessianDiagonal
      measurable_gaussianHessianDiagonal 1 1)
    (diagonalSoftAbs_isMeasurableRiemannianMomentumFamily
      1 (by norm_num) gaussianHessianDiagonal 1 1
      (by norm_num) (by norm_num) measurable_gaussianHessianDiagonal)
    1 1 (support.indicator fun _ => (1 : ENNReal))
    (measurable_const.indicator hsupport) q]
  simp_rw [show (fun z : PhaseSpace Unit =>
      support.indicator (fun _ => (1 : ENNReal)) z.1) =
      (Prod.fst ⁻¹' support).indicator (1 : PhaseSpace Unit → ENNReal) by rfl]
  simp_rw [lintegral_indicator_one (measurable_fst hsupport)]
  have hphase (p : Momentum Unit) :
      gaussianSoftAbsPhaseTransition 1 1 (q, p)
        (Prod.fst ⁻¹' support) = 1 := by
    simpa [support] using
      gaussianSoftAbsPhaseTransition_unit_position_support q p
  simp_rw [hphase]
  simp

/-- The bare Gaussian SoftAbs transition is identity at trajectory length
zero. Consequently any convergence theorem for the unaugmented sampler must
assume a genuinely positive, nondegenerate trajectory regime. -/
theorem gaussianSoftAbsMultinomialTransition_zero (ε : ℝ) :
    gaussianSoftAbsMultinomialTransition (ι := ι) ε 0 = Kernel.id := by
  exact positionMultinomialGRHMC_zero _ _ _ _ _ _ _ _ _ _ ε

/-- Zero step size is the second exact degeneracy: the Gaussian SoftAbs
position transition is identity for every nominal trajectory length. -/
theorem gaussianSoftAbsMultinomialTransition_step_zero (L : ℕ) :
    gaussianSoftAbsMultinomialTransition (ι := ι) 0 L = Kernel.id := by
  exact positionMultinomialGRHMC_step_zero _ _ _ _ _ _ _ _ _ _ L

/-- Mix GR-HMC (weight `p`) with an exact independent normalized-target draw
(weight `1-p`). -/
noncomputable def gaussianSoftAbsRefreshAugmented
    (p : Set.Icc (0 : NNReal) 1) (ε : ℝ) (L : ℕ) :=
  Mcmc.Kernel.refreshAugmented p
    (gaussianSoftAbsMultinomialTransition (ι := ι) ε L)
    (Mcmc.Kernel.finiteNormalize
      (gaussianSoftAbsPositionTarget (ι := ι)))

instance gaussianSoftAbsRefreshAugmented.instIsMarkovKernel
    (p : Set.Icc (0 : NNReal) 1) (ε : ℝ) (L : ℕ) :
    IsMarkovKernel (gaussianSoftAbsRefreshAugmented (ι := ι) p ε L) := by
  unfold gaussianSoftAbsRefreshAugmented
  infer_instance

/-- The refresh-augmented transition preserves the normalized Gaussian
SoftAbs position target. -/
theorem gaussianSoftAbsRefreshAugmented_invariant
    (p : Set.Icc (0 : NNReal) 1) (ε : ℝ) (L : ℕ) :
    (gaussianSoftAbsRefreshAugmented (ι := ι) p ε L).Invariant
      (Mcmc.Kernel.finiteNormalize
        (gaussianSoftAbsPositionTarget (ι := ι))) := by
  apply Mcmc.Kernel.refreshAugmented_invariant
  apply Mcmc.Kernel.invariant_finiteNormalize _ _
    gaussianSoftAbsPositionTarget_ne_zero
  exact gaussianSoftAbs_multinomialGRHMC_invariant ε L

/-- Upper half of the eventwise geometric convergence certificate. -/
theorem gaussianSoftAbsRefreshAugmented_lawAtTime_apply_le
    (p : Set.Icc (0 : NNReal) 1) (hp0 : 0 < p.1)
    (ε : ℝ) (L n : ℕ) (initial : Measure (Position ι))
    [IsProbabilityMeasure initial] {s : Set (Position ι)}
    (hs : MeasurableSet s) :
    Mcmc.Kernel.lawAtTime initial
        (gaussianSoftAbsRefreshAugmented (ι := ι) p ε L) n s ≤
      Mcmc.Kernel.finiteNormalize
          (gaussianSoftAbsPositionTarget (ι := ι)) s +
        ((p.1 ^ n : NNReal) : ENNReal) := by
  apply Mcmc.Kernel.refreshAugmented_lawAtTime_apply_le
    p hp0 (gaussianSoftAbsMultinomialTransition (ι := ι) ε L)
    (Mcmc.Kernel.finiteNormalize
      (gaussianSoftAbsPositionTarget (ι := ι))) initial
  · apply Mcmc.Kernel.invariant_finiteNormalize _ _
      gaussianSoftAbsPositionTarget_ne_zero
    exact gaussianSoftAbs_multinomialGRHMC_invariant ε L
  · exact hs

/-- Lower half of the eventwise geometric convergence certificate. -/
theorem gaussianSoftAbsRefreshAugmented_target_apply_le_lawAtTime
    (p : Set.Icc (0 : NNReal) 1) (hp0 : 0 < p.1)
    (ε : ℝ) (L n : ℕ) (initial : Measure (Position ι))
    [IsProbabilityMeasure initial] {s : Set (Position ι)}
    (hs : MeasurableSet s) :
    Mcmc.Kernel.finiteNormalize
        (gaussianSoftAbsPositionTarget (ι := ι)) s ≤
      Mcmc.Kernel.lawAtTime initial
          (gaussianSoftAbsRefreshAugmented (ι := ι) p ε L) n s +
        ((p.1 ^ n : NNReal) : ENNReal) := by
  apply Mcmc.Kernel.refreshAugmented_target_apply_le_lawAtTime
    p hp0 (gaussianSoftAbsMultinomialTransition (ι := ι) ε L)
    (Mcmc.Kernel.finiteNormalize
      (gaussianSoftAbsPositionTarget (ι := ι))) initial
  · apply Mcmc.Kernel.invariant_finiteNormalize _ _
      gaussianSoftAbsPositionTarget_ne_zero
    exact gaussianSoftAbs_multinomialGRHMC_invariant ε L
  · exact hs

/-- When the refresh branch has positive weight (`p < 1`), the explicit
remainder in both eventwise bounds tends to zero. -/
theorem gaussianSoftAbsRefreshAugmented_rate_tendsto_zero
    (p : Set.Icc (0 : NNReal) 1) (hp : p.1 < 1) :
    Filter.Tendsto (fun n : ℕ => (((p.1 : NNReal) : ENNReal) ^ n))
      Filter.atTop (nhds 0) :=
  Mcmc.Kernel.refreshAugmented_rate_tendsto_zero p hp

/-- The refresh-augmented Gaussian SoftAbs GR-HMC chain converges setwise to
its normalized position target from every initial probability law. The
assumptions `0 < p < 1` keep both the GR-HMC and exact-refresh branches active;
this theorem does not make a convergence claim for bare GR-HMC (`p = 1`). -/
theorem gaussianSoftAbsRefreshAugmented_lawAtTime_apply_tendsto
    (p : Set.Icc (0 : NNReal) 1) (hp0 : 0 < p.1) (hp1 : p.1 < 1)
    (ε : ℝ) (L : ℕ) (initial : Measure (Position ι))
    [IsProbabilityMeasure initial] {s : Set (Position ι)}
    (hs : MeasurableSet s) :
    Filter.Tendsto
      (fun n => Mcmc.Kernel.lawAtTime initial
        (gaussianSoftAbsRefreshAugmented (ι := ι) p ε L) n s)
      Filter.atTop
      (nhds (Mcmc.Kernel.finiteNormalize
        (gaussianSoftAbsPositionTarget (ι := ι)) s)) := by
  apply Mcmc.Kernel.refreshAugmented_lawAtTime_apply_tendsto
    p hp0 hp1 (gaussianSoftAbsMultinomialTransition (ι := ι) ε L)
    (Mcmc.Kernel.finiteNormalize
      (gaussianSoftAbsPositionTarget (ι := ι))) initial
  · apply Mcmc.Kernel.invariant_finiteNormalize _ _
      gaussianSoftAbsPositionTarget_ne_zero
    exact gaussianSoftAbs_multinomialGRHMC_invariant ε L
  · exact hs

end Mcmc.Executable.Continuous
