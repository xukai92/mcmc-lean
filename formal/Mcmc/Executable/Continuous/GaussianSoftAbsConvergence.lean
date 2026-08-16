import Mcmc.Executable.Continuous.GaussianSoftAbs
import Mcmc.Kernel.RefreshAugmented
import Mcmc.Kernel.LocalMinorizationCoupling

/-!
# Geometric convergence for refresh-augmented Gaussian SoftAbs GR-HMC

This module turns the exact invariance theorem for the concrete Gaussian
diagonal-SoftAbs multinomial GR-HMC transition into an eventwise geometric
convergence theorem by adding an independent draw from the normalized target.
The theorem concerns this explicitly augmented algorithm; it does not assert
a convergence rate for the unrefreshed GR-HMC transition.
-/

namespace Mcmc.Executable.Continuous

open Mcmc.Hamiltonian Mcmc.Kernel Mcmc.Relativistic MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

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

/-- A coordinate momentum-density floor propagates through the actual
SoftAbs moved-position map. This is the sampler-specific change-of-variables
bridge used by the compact minorization argument. -/
theorem mul_volume_le_map_gaussianSoftAbsUnitMovedPosition
    (source : Measure ℝ) (q : ℝ) {P S : Set ℝ}
    (hS : MeasurableSet S)
    (hSP : S ⊆ gaussianSoftAbsUnitMovedPosition q '' P)
    (sourceFloor outputFloor : ENNReal)
    (hsource : ∀ T, MeasurableSet T → T ⊆ P →
      sourceFloor * volume T ≤ source T)
    (hcoefficient : outputFloor *
      ENNReal.ofReal ((softAbs 1 1)⁻¹) ≤ sourceFloor) :
    outputFloor * volume S ≤
      Measure.map (gaussianSoftAbsUnitMovedPosition q) source S := by
  apply Mcmc.Kernel.mul_volume_le_map_of_sourceFloor_of_image_le
    source (gaussianSoftAbsUnitMovedPosition q)
    (measurableEmbedding_gaussianSoftAbsUnitMovedPosition q)
    hS hSP sourceFloor (ENNReal.ofReal ((softAbs 1 1)⁻¹)) outputFloor
    hsource _ hcoefficient
  intro T hT
  exact volume_image_gaussianSoftAbsUnitMovedPosition_le q T hT

/-- Lebesgue density of the refreshed one-dimensional Gaussian SoftAbs
momentum coordinate. -/
noncomputable def gaussianSoftAbsMomentumCoordinateDensity (x : ℝ) : ENNReal :=
  (euclideanRelativisticMomentumPartition Unit 1 1
      (by norm_num) (by norm_num) : ENNReal)⁻¹ *
    riemannianRelativisticMomentumWeight
      (gaussianSoftAbsMetric (ι := Unit)) 1 1 0 (fun _ => x)

theorem continuous_gaussianSoftAbsMomentumCoordinateDensity :
    Continuous gaussianSoftAbsMomentumCoordinateDensity := by
  unfold gaussianSoftAbsMomentumCoordinateDensity
    riemannianRelativisticMomentumWeight
    riemannianRelativisticKineticEnergy
  apply (ENNReal.continuous_const_mul (ENNReal.inv_ne_top.mpr (by
    exact_mod_cast euclideanRelativisticMomentumPartition_ne_zero
      Unit 1 1 (by norm_num) (by norm_num)))).comp
  apply ENNReal.continuous_ofReal.comp
  unfold relativisticKineticEnergy gaussianSoftAbsMetric
    gaussianHessianDiagonal diagonalSoftAbsMetric diagonalSoftAbsFactor
    diagonalSoftAbsEigenvalue squaredEuclideanNorm euclideanInner
  fun_prop

theorem gaussianSoftAbsMomentumCoordinateDensity_pos (x : ℝ) :
    0 < gaussianSoftAbsMomentumCoordinateDensity x := by
  unfold gaussianSoftAbsMomentumCoordinateDensity
  apply ENNReal.mul_pos
  · rw [ENNReal.inv_ne_zero]
    exact ENNReal.coe_ne_top
  · unfold riemannianRelativisticMomentumWeight
    positivity

/-- Every bounded momentum coordinate interval has one common strictly
positive refreshed-density floor. -/
theorem exists_pos_gaussianSoftAbsMomentumCoordinateDensity_floor
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ floor : ENNReal, 0 < floor ∧
      ∀ x ∈ Set.Icc (-R) R,
        floor ≤ gaussianSoftAbsMomentumCoordinateDensity x := by
  apply Mcmc.Kernel.exists_pos_le_on_compact
  · exact isCompact_Icc
  · exact ⟨0, by simp [hR]⟩
  · exact continuous_gaussianSoftAbsMomentumCoordinateDensity
  · intro x _hx
    exact gaussianSoftAbsMomentumCoordinateDensity_pos x

/-- Distribution of the refreshed momentum's unique scalar coordinate. -/
noncomputable def gaussianSoftAbsMomentumCoordinateProbability : Measure ℝ :=
  Measure.map (fun p : Momentum Unit => p Unit.unit)
    (riemannianRelativisticMomentumProbability
      (gaussianSoftAbsMetric (ι := Unit)) 1 1
      (by norm_num) (by norm_num) 0 : Measure (Momentum Unit))

instance gaussianSoftAbsMomentumCoordinateProbability.instIsProbabilityMeasure :
    IsProbabilityMeasure gaussianSoftAbsMomentumCoordinateProbability := by
  unfold gaussianSoftAbsMomentumCoordinateProbability
  apply Measure.isProbabilityMeasure_map
  exact (measurable_pi_apply Unit.unit).aemeasurable

/-- The coordinate law has exactly the continuous density defined above. -/
theorem gaussianSoftAbsMomentumCoordinateProbability_apply
    {T : Set ℝ} (hT : MeasurableSet T) :
    gaussianSoftAbsMomentumCoordinateProbability T =
      ∫⁻ x in T, gaussianSoftAbsMomentumCoordinateDensity x := by
  let eval : Momentum Unit → ℝ := fun p => p Unit.unit
  have heval : Measurable eval := measurable_pi_apply Unit.unit
  have hweight : Measurable (Function.uncurry
      (riemannianRelativisticMomentumWeight
        (gaussianSoftAbsMetric (ι := Unit)) 1 1)) :=
    measurable_riemannianRelativisticMomentumWeight
      measurable_gaussianSoftAbsPotential
      (gaussianSoftAbsMetric (ι := Unit)) 1 1
      (measurable_diagonalSoftAbs_generalRelativisticHamiltonian
        gaussianSoftAbsPotential measurable_gaussianSoftAbsPotential
        1 (by norm_num) gaussianHessianDiagonal
        measurable_gaussianHessianDiagonal 1 1)
  have hvolumeMap : Measure.map eval
      (volume : Measure (Momentum Unit)) = (volume : Measure ℝ) := by
    rw [volume_pi]
    simpa [eval] using
      (Measure.pi_map_eval
        (μ := fun _ : Unit => (volume : Measure ℝ)) Unit.unit)
  rw [gaussianSoftAbsMomentumCoordinateProbability,
    Measure.map_apply heval hT,
    riemannianRelativisticMomentumProbability_eq_withDensity
      (gaussianSoftAbsMetric (ι := Unit))
      (diagonalSoftAbsMetric_hasCompatibleFactorVolume
        1 (by norm_num) gaussianHessianDiagonal)
      1 1 (by norm_num) (by norm_num) hweight 0,
    withDensity_apply _ (hT.preimage heval)]
  rw [← lintegral_indicator hT]
  have hdensity : Measurable gaussianSoftAbsMomentumCoordinateDensity :=
    continuous_gaussianSoftAbsMomentumCoordinateDensity.measurable
  rw [← hvolumeMap, lintegral_map (hdensity.indicator hT) heval]
  rw [← lintegral_indicator (hT.preimage heval)]
  apply lintegral_congr
  intro p
  by_cases hp : eval p ∈ T
  · rw [Set.indicator_of_mem (show p ∈ eval ⁻¹' T from hp),
      Set.indicator_of_mem hp]
    unfold gaussianSoftAbsMomentumCoordinateDensity eval
    congr 2
  · rw [Set.indicator_of_notMem (show p ∉ eval ⁻¹' T from hp),
      Set.indicator_of_notMem hp]

/-- On every bounded momentum interval, the actual refreshed coordinate law
dominates Lebesgue measure by one strictly positive constant. -/
theorem exists_pos_gaussianSoftAbsMomentumCoordinateProbability_volume_floor
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ floor : ENNReal, 0 < floor ∧
      ∀ T, MeasurableSet T → T ⊆ Set.Icc (-R) R →
        floor * volume T ≤ gaussianSoftAbsMomentumCoordinateProbability T := by
  obtain ⟨floor, hfloorPos, hfloor⟩ :=
    exists_pos_gaussianSoftAbsMomentumCoordinateDensity_floor R hR
  refine ⟨floor, hfloorPos, ?_⟩
  intro T hT hTR
  rw [gaussianSoftAbsMomentumCoordinateProbability_apply hT,
    ← setLIntegral_const]
  apply setLIntegral_mono' hT
  intro x hx
  exact hfloor x (hTR hx)

/-- The actual refreshed-momentum moved-position law has a positive Lebesgue
density floor on every output region reached from a bounded momentum band.
The floor is uniform in the current position. -/
theorem exists_pos_gaussianSoftAbsMovedPosition_volume_floor
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ floor : ENNReal, 0 < floor ∧
      ∀ q : ℝ, ∀ S, MeasurableSet S →
        S ⊆ gaussianSoftAbsUnitMovedPosition q '' Set.Icc (-R) R →
        floor * volume S ≤
          Measure.map (gaussianSoftAbsUnitMovedPosition q)
            gaussianSoftAbsMomentumCoordinateProbability S := by
  obtain ⟨sourceFloor, hsourceFloorPos, hsource⟩ :=
    exists_pos_gaussianSoftAbsMomentumCoordinateProbability_volume_floor R hR
  let J : ENNReal := ENNReal.ofReal ((softAbs 1 1)⁻¹)
  have hk : 0 < softAbs 1 1 := softAbs_pos 1 (by norm_num) 1
  have hJPos : 0 < J := ENNReal.ofReal_pos.mpr (inv_pos.mpr hk)
  have hJTop : J ≠ ∞ := ENNReal.ofReal_ne_top
  let floor := sourceFloor / J
  have hfloorPos : 0 < floor := ENNReal.div_pos hsourceFloorPos.ne' hJTop
  refine ⟨floor, hfloorPos, ?_⟩
  intro q S hS hSimage
  apply mul_volume_le_map_gaussianSoftAbsUnitMovedPosition
    gaussianSoftAbsMomentumCoordinateProbability q hS hSimage
    sourceFloor floor hsource
  dsimp [floor]
  rw [ENNReal.div_mul_cancel hJPos.ne' hJTop]

/-- Energy error of the actual forward unit SoftAbs leapfrog branch. -/
noncomputable def gaussianSoftAbsForwardEnergyError
    (z : PhaseSpace Unit) : ℝ :=
  generalRelativisticHamiltonian gaussianSoftAbsPotential
      gaussianSoftAbsMetric 1 1
      (gaussianSoftAbsSelection.step 1 z) -
    generalRelativisticHamiltonian gaussianSoftAbsPotential
      gaussianSoftAbsMetric 1 1 z

theorem continuous_gaussianSoftAbsForwardEnergyError :
    Continuous gaussianSoftAbsForwardEnergyError := by
  unfold gaussianSoftAbsForwardEnergyError
  exact
    (continuous_gaussianSoftAbsUnit_hamiltonian.comp
      continuous_gaussianSoftAbsSelection_step_one_unit).sub
        continuous_gaussianSoftAbsUnit_hamiltonian

/-- Compactness supplies a finite upper bound for the actual leapfrog energy
error; no global energy-error estimate is assumed. -/
theorem exists_gaussianSoftAbsForwardEnergyError_le_on_compact
    {C : Set (PhaseSpace Unit)} (hC : IsCompact C) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ z ∈ C, gaussianSoftAbsForwardEnergyError z ≤ D := by
  have himage : IsCompact (gaussianSoftAbsForwardEnergyError '' C) :=
    hC.image continuous_gaussianSoftAbsForwardEnergyError
  obtain ⟨D, hD⟩ := himage.isBounded.bddAbove
  refine ⟨max D 0, le_max_right _ _, ?_⟩
  intro z hz
  exact (hD ⟨z, hz, rfl⟩).trans (le_max_left _ _)

/-- On every compact phase-space set, the forward candidate of the actual
two-point multinomial transition has one common strictly positive selection
probability. -/
theorem exists_pos_gaussianSoftAbs_forward_indexProbability_floor_on_compact
    {C : Set (PhaseSpace Unit)} (hC : IsCompact C) :
    ∃ floor : ENNReal, 0 < floor ∧ ∀ z ∈ C,
      floor ≤ orbitIndexProbability
        (generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
          gaussianSoftAbsMetric 1 1)
        (generalizedLeapfrogPerm gaussianSoftAbsSelection
          gaussianSoftAbsSelection_valid.unique 1)
        (0 : Fin 2) (1 : Fin 2) z := by
  obtain ⟨D, hD0, hD⟩ :=
    exists_gaussianSoftAbsForwardEnergyError_le_on_compact hC
  let floor : ENNReal :=
    ((2 : ENNReal) * ENNReal.ofReal (Real.exp D))⁻¹
  have hfloorPos : 0 < floor := by
    apply ENNReal.inv_pos.mpr
    exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  refine ⟨floor, hfloorPos, ?_⟩
  intro z hz
  have hbound :=
    inv_card_exp_le_multinomialGRHMCPhase_indexProbability
      gaussianSoftAbsPotential gaussianSoftAbsMetric 1 1
      gaussianSoftAbsSelection gaussianSoftAbsSelection_valid
      1 (0 : Fin 2) (1 : Fin 2) z D (by
        intro i
        fin_cases i
        · simpa [orbitPoint, gaussianSoftAbsForwardEnergyError] using hD z hz
        · simpa [orbitPoint] using hD0)
  simpa [floor] using hbound

/-- The selected forward endpoint under the actual refreshed momentum law is
exactly the scalar moved-position pushforward when observed through the unique
position coordinate. -/
theorem gaussianSoftAbs_selectedEndpoint_map_coordinate_apply
    (q : Position Unit) {S : Set ℝ} (hS : MeasurableSet S) :
    Measure.map (fun p : Momentum Unit =>
        (orbitPoint
          (generalizedLeapfrogPerm gaussianSoftAbsSelection
            gaussianSoftAbsSelection_valid.unique 1)
          (0 : Fin 2) (q, p) (1 : Fin 2)).1)
        (riemannianMomentumKernel gaussianSoftAbsMetric 1 1
          (by norm_num) (by norm_num)
          (diagonalSoftAbs_isMeasurableRiemannianMomentumFamily
            1 (by norm_num) gaussianHessianDiagonal 1 1
            (by norm_num) (by norm_num)
            measurable_gaussianHessianDiagonal) q)
        {y | y Unit.unit ∈ S} =
      Measure.map (gaussianSoftAbsUnitMovedPosition (q Unit.unit))
        gaussianSoftAbsMomentumCoordinateProbability S := by
  have hposition : MeasurableSet {y : Position Unit | y Unit.unit ∈ S} :=
    hS.preimage (measurable_pi_apply Unit.unit)
  have hcandidate : Measurable (fun p : Momentum Unit =>
      (orbitPoint
        (generalizedLeapfrogPerm gaussianSoftAbsSelection
          gaussianSoftAbsSelection_valid.unique 1)
        (0 : Fin 2) (q, p) (1 : Fin 2)).1) := by
    simp only [orbitPoint]
    exact (continuous_fst.comp
      (continuous_gaussianSoftAbsSelection_step_one_unit.comp
        (continuous_const.prodMk continuous_id))).measurable
  rw [Measure.map_apply hcandidate hposition,
    Measure.map_apply
      (measurableEmbedding_gaussianSoftAbsUnitMovedPosition
        (q Unit.unit)).measurable hS]
  rw [gaussianSoftAbsMomentumCoordinateProbability,
    Measure.map_apply (measurable_pi_apply Unit.unit) (hS.preimage
      (measurableEmbedding_gaussianSoftAbsUnitMovedPosition
        (q Unit.unit)).measurable)]
  rw [show (riemannianMomentumKernel gaussianSoftAbsMetric 1 1
      (by norm_num) (by norm_num)
      (diagonalSoftAbs_isMeasurableRiemannianMomentumFamily
        1 (by norm_num) gaussianHessianDiagonal 1 1
        (by norm_num) (by norm_num)
        measurable_gaussianHessianDiagonal) q) =
      (riemannianRelativisticMomentumProbability gaussianSoftAbsMetric 1 1
        (by norm_num) (by norm_num) q : Measure (Momentum Unit)) by rfl]
  rw [gaussianSoftAbsMomentumProbability_eq_zero]
  congr 1
  ext p
  change ((gaussianSoftAbsSelection.step 1 (q, p)).1 Unit.unit ∈ S) ↔
    gaussianSoftAbsUnitMovedPosition (q Unit.unit) (p Unit.unit) ∈ S
  rw [gaussianSoftAbsSelection_step_one_fst_eq_movedPosition]

/-- Compact phase-space control, the selected-index floor, and the actual
refreshed-momentum Jacobian bound combine into a one-step Lebesgue
minorization for coordinate events. -/
theorem exists_pos_gaussianSoftAbs_oneStep_coordinate_volume_floor
    {C : Set (PhaseSpace Unit)} (hC : IsCompact C)
    (D : Set (Position Unit)) (R : ℝ) (hR : 0 ≤ R)
    (hphase : ∀ q ∈ D, ∀ p : Momentum Unit,
      p Unit.unit ∈ Set.Icc (-R) R → (q, p) ∈ C) :
    ∃ floor : ENNReal, 0 < floor ∧ ∀ q ∈ D, ∀ S : Set ℝ,
      MeasurableSet S →
      S ⊆ gaussianSoftAbsUnitMovedPosition (q Unit.unit) '' Set.Icc (-R) R →
      floor * volume S ≤
        gaussianSoftAbsMultinomialTransition 1 1 q
          {y | y Unit.unit ∈ S} := by
  obtain ⟨densityFloor, hdensityPos, hdensity⟩ :=
    exists_pos_gaussianSoftAbsMovedPosition_volume_floor R hR
  obtain ⟨indexFloor, hindexPos, hindex⟩ :=
    exists_pos_gaussianSoftAbs_forward_indexProbability_floor_on_compact hC
  let originMass : ENNReal := PMF.uniformOfFintype (Fin 2) (0 : Fin 2)
  let floor := densityFloor * (originMass * indexFloor)
  have horiginPos : 0 < originMass := by
    simp [originMass]
  have hfloorPos : 0 < floor :=
    ENNReal.mul_pos hdensityPos.ne'
      (ENNReal.mul_pos horiginPos.ne' hindexPos.ne').ne'
  refine ⟨floor, hfloorPos, ?_⟩
  intro q hq S hS hSimage
  let momentumSet : Set (Momentum Unit) :=
    {p | p Unit.unit ∈ Set.Icc (-R) R}
  let positionSet : Set (Position Unit) := {y | y Unit.unit ∈ S}
  have hmomentumSet : MeasurableSet momentumSet :=
    isClosed_Icc.measurableSet.preimage (continuous_apply Unit.unit).measurable
  have hpositionSet : MeasurableSet positionSet :=
    hS.preimage (measurable_pi_apply Unit.unit)
  have hcandidate : Measurable (fun p : Momentum Unit =>
      (orbitPoint
        (generalizedLeapfrogPerm gaussianSoftAbsSelection
          gaussianSoftAbsSelection_valid.unique 1)
        (0 : Fin 2) (q, p) (1 : Fin 2)).1) := by
    simp only [orbitPoint]
    exact (continuous_fst.comp
      (continuous_gaussianSoftAbsSelection_step_one_unit.comp
        (continuous_const.prodMk continuous_id))).measurable
  have hbranch :=
    map_selectedEndpoint_mul_uniform_mul_floor_le_positionMultinomialGRHMC_apply
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
      1 (0 : Fin 2) (1 : Fin 2) q hmomentumSet hcandidate
      hpositionSet indexFloor
      (fun p hp => hindex (q, p) (hphase q hq p hp)) (by
        intro p hp
        obtain ⟨x, hx, hxeq⟩ := hSimage hp
        have heq : p Unit.unit = x := by
          apply (strictMono_gaussianSoftAbsUnitMovedPosition
            (q Unit.unit)).injective
          simpa [positionSet, orbitPoint,
            gaussianSoftAbsSelection_step_one_fst_eq_movedPosition] using hxeq.symm
        show p Unit.unit ∈ Set.Icc (-R) R
        rw [heq]
        exact hx)
  have hdensityS := hdensity (q Unit.unit) S hS hSimage
  rw [gaussianSoftAbs_selectedEndpoint_map_coordinate_apply q hS] at hbranch
  change Measure.map (gaussianSoftAbsUnitMovedPosition (q Unit.unit))
      gaussianSoftAbsMomentumCoordinateProbability S *
        (originMass * indexFloor) ≤
      gaussianSoftAbsMultinomialTransition 1 1 q positionSet at hbranch
  calc
    floor * volume S =
        (densityFloor * volume S) * (originMass * indexFloor) := by
      simp only [floor]
      ac_rfl
    _ ≤ Measure.map (gaussianSoftAbsUnitMovedPosition (q Unit.unit))
          gaussianSoftAbsMomentumCoordinateProbability S *
            (originMass * indexFloor) := by gcongr
    _ ≤ gaussianSoftAbsMultinomialTransition 1 1 q positionSet := hbranch

/-- Concrete compact phase box, expressed through the two scalar coordinates
so compactness does not depend on an opaque finite-dimensional-space
instance. -/
def gaussianSoftAbsPhaseBox (Q R : ℝ) : Set (PhaseSpace Unit) :=
  (fun z : ℝ × ℝ =>
    ((fun _ : Unit => z.1), (fun _ : Unit => z.2))) ''
      (Set.Icc (-Q) Q ×ˢ Set.Icc (-R) R)

theorem isCompact_gaussianSoftAbsPhaseBox (Q R : ℝ) :
    IsCompact (gaussianSoftAbsPhaseBox Q R) := by
  apply (isCompact_Icc.prod isCompact_Icc).image
  fun_prop

theorem mem_gaussianSoftAbsPhaseBox
    (Q R : ℝ) (q : Position Unit) (p : Momentum Unit)
    (hq : q Unit.unit ∈ Set.Icc (-Q) Q)
    (hp : p Unit.unit ∈ Set.Icc (-R) R) :
    (q, p) ∈ gaussianSoftAbsPhaseBox Q R := by
  refine ⟨(q Unit.unit, p Unit.unit), ⟨hq, hp⟩, ?_⟩
  apply Prod.ext
  · funext i
    fin_cases i
    rfl
  · funext i
    fin_cases i
    rfl

/-- Fully concrete uniform one-step coordinate density floor over a bounded
position band and bounded refreshed-momentum band. The reachable output
region is allowed to translate with the current position; a common output
set is deliberately deferred to the finite-step corridor construction. -/
theorem exists_pos_gaussianSoftAbs_oneStep_coordinate_volume_floor_on_box
    (Q R : ℝ) (hR : 0 ≤ R) :
    ∃ floor : ENNReal, 0 < floor ∧
      ∀ q : Position Unit, q Unit.unit ∈ Set.Icc (-Q) Q →
      ∀ S : Set ℝ, MeasurableSet S →
      S ⊆ gaussianSoftAbsUnitMovedPosition (q Unit.unit) '' Set.Icc (-R) R →
      floor * volume S ≤
        gaussianSoftAbsMultinomialTransition 1 1 q
          {y | y Unit.unit ∈ S} := by
  apply exists_pos_gaussianSoftAbs_oneStep_coordinate_volume_floor
    (isCompact_gaussianSoftAbsPhaseBox Q R)
    {q : Position Unit | q Unit.unit ∈ Set.Icc (-Q) Q} R hR
  intro q hq p hp
  exact mem_gaussianSoftAbsPhaseBox Q R q p hq hp

@[simp]
theorem gaussianSoftAbsUnitScalarVelocity_zero :
    gaussianSoftAbsUnitScalarVelocity 0 = 0 := by
  rw [gaussianSoftAbsUnitScalarVelocity_eq]
  simp

/-- A bounded position band has a common nontrivial local interval inside
the moved-position image. Choosing momentum radius `Q/2+1` guarantees that
the half-kicked momentum spans at least `[-1,1]` for every `q ∈ [-Q,Q]`. -/
theorem gaussianSoftAbs_localInterval_subset_movedPosition_image
    (Q q : ℝ) (hq : q ∈ Set.Icc (-Q) Q) :
    Set.Icc
        (q - gaussianSoftAbsUnitScalarVelocity 1)
        (q + gaussianSoftAbsUnitScalarVelocity 1) ⊆
      gaussianSoftAbsUnitMovedPosition q ''
        Set.Icc (-(Q / 2 + 1)) (Q / 2 + 1) := by
  have hcontinuous : Continuous (gaussianSoftAbsUnitMovedPosition q) := by
    rw [continuous_iff_continuousAt]
    intro p
    exact (hasDerivAt_gaussianSoftAbsUnitMovedPosition q p).continuousAt
  rw [hcontinuous.image_Icc_of_strictMono
    (strictMono_gaussianSoftAbsUnitMovedPosition q)]
  intro y hy
  refine ⟨?_, ?_⟩
  · calc
      gaussianSoftAbsUnitMovedPosition q (-(Q / 2 + 1)) =
          q + gaussianSoftAbsUnitScalarVelocity
            (-(Q / 2 + 1) - q / 2) := rfl
      _ ≤ q + gaussianSoftAbsUnitScalarVelocity (-1) := by
        apply add_le_add_right
        apply strictMono_gaussianSoftAbsUnitScalarVelocity.monotone
        linarith [hq.1]
      _ = q - gaussianSoftAbsUnitScalarVelocity 1 := by
        rw [gaussianSoftAbsUnitScalarVelocity_neg]
        ring
      _ ≤ y := hy.1
  · calc
      y ≤ q + gaussianSoftAbsUnitScalarVelocity 1 := hy.2
      _ ≤ q + gaussianSoftAbsUnitScalarVelocity
          (Q / 2 + 1 - q / 2) := by
        apply add_le_add_right
        apply strictMono_gaussianSoftAbsUnitScalarVelocity.monotone
        linarith [hq.2]
      _ = gaussianSoftAbsUnitMovedPosition q (Q / 2 + 1) := rfl

/-- The common local interval above has positive radius. -/
theorem gaussianSoftAbsUnitScalarVelocity_one_pos :
    0 < gaussianSoftAbsUnitScalarVelocity 1 := by
  simpa using strictMono_gaussianSoftAbsUnitScalarVelocity
    (show (0 : ℝ) < 1 by norm_num)

/-- Uniform local Lebesgue minorization over a bounded position band. Every
row dominates the same density constant on a fixed-radius interval centered
at its current coordinate. -/
theorem exists_pos_gaussianSoftAbs_localInterval_volume_floor_on_box
    (Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ floor : ENNReal, 0 < floor ∧
      ∀ q : Position Unit, q Unit.unit ∈ Set.Icc (-Q) Q →
      ∀ S : Set ℝ, MeasurableSet S →
      S ⊆ Set.Icc
        (q Unit.unit - gaussianSoftAbsUnitScalarVelocity 1)
        (q Unit.unit + gaussianSoftAbsUnitScalarVelocity 1) →
      floor * volume S ≤
        gaussianSoftAbsMultinomialTransition 1 1 q
          {y | y Unit.unit ∈ S} := by
  obtain ⟨floor, hfloorPos, hfloor⟩ :=
    exists_pos_gaussianSoftAbs_oneStep_coordinate_volume_floor_on_box
      Q (Q / 2 + 1) (by linarith)
  refine ⟨floor, hfloorPos, ?_⟩
  intro q hq S hS hSloc
  apply hfloor q hq S hS
  exact hSloc.trans
    (gaussianSoftAbs_localInterval_subset_movedPosition_image
      Q (q Unit.unit) hq)

/-- Any measurable scalar corridor whose successive sections fit inside the
certified local intervals inherits an explicit power-kernel lower bound. This
separates the probabilistic composition from the remaining elementary
construction of interval centers. -/
theorem exists_pos_gaussianSoftAbs_corridor_power_lower_bound
    (Q : ℝ) (hQ : 0 ≤ Q) (sections : ℕ → Set ℝ)
    (hsections : ∀ i, MeasurableSet (sections i))
    (mass : ENNReal) (n : ℕ)
    (hband : ∀ i < n, ∀ y ∈ sections i, y ∈ Set.Icc (-Q) Q)
    (hmass : ∀ i < n, mass ≤ volume (sections (i + 1)))
    (hlocal : ∀ i < n, ∀ y ∈ sections i,
      sections (i + 1) ⊆ Set.Icc
        (y - gaussianSoftAbsUnitScalarVelocity 1)
        (y + gaussianSoftAbsUnitScalarVelocity 1)) :
    ∃ floor : ENNReal, 0 < floor ∧
      ∀ q : Position Unit, q Unit.unit ∈ sections 0 →
      (floor * mass) ^ n ≤
        (gaussianSoftAbsMultinomialTransition 1 1 ^ n) q
          {y | y Unit.unit ∈ sections n} := by
  obtain ⟨floor, hfloorPos, hfloor⟩ :=
    exists_pos_gaussianSoftAbs_localInterval_volume_floor_on_box Q hQ
  refine ⟨floor, hfloorPos, ?_⟩
  intro q hq
  let positionSections : ℕ → Set (Position Unit) := fun i =>
    {y | y Unit.unit ∈ sections i}
  have hpositionSections : ∀ i, MeasurableSet (positionSections i) := by
    intro i
    exact (hsections i).preimage (measurable_pi_apply Unit.unit)
  apply Mcmc.Kernel.bound_pow_le_apply_of_measurable_corridor
    (gaussianSoftAbsMultinomialTransition 1 1)
    positionSections hpositionSections (floor * mass) q hq n
  intro i hi y hy
  calc
    floor * mass ≤ floor * volume (sections (i + 1)) := by
      gcongr
      exact hmass i hi
    _ ≤ gaussianSoftAbsMultinomialTransition 1 1 y
          {z | z Unit.unit ∈ sections (i + 1)} := by
      apply hfloor y (hband i hi (y Unit.unit) hy)
        (sections (i + 1)) (hsections (i + 1))
      exact hlocal i hi (y Unit.unit) hy

/-- Exponential coordinate Lyapunov weight used for the bare one-dimensional
Gaussian SoftAbs drift argument. -/
noncomputable def gaussianSoftAbsExpWeight (t x : ℝ) : ENNReal :=
  ENNReal.ofReal (Real.exp (t * |x|))

noncomputable def gaussianSoftAbsExpLyapunov
    (t : ℝ) (q : Position Unit) : ENNReal :=
  gaussianSoftAbsExpWeight t (q Unit.unit)

theorem measurable_gaussianSoftAbsExpLyapunov (t : ℝ) :
    Measurable (gaussianSoftAbsExpLyapunov t) := by
  unfold gaussianSoftAbsExpLyapunov gaussianSoftAbsExpWeight
  fun_prop

/-- Bound a nonnegative expectation by splitting into a favorable event, the
remainder of a containing event, and its complement. -/
theorem lintegral_le_of_nested_event_bounds
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : A ⊆ B) (f : α → ENNReal)
    (a b c : ENNReal)
    (ha : ∀ x ∈ A, f x ≤ a)
    (hb : ∀ x ∈ B \ A, f x ≤ b)
    (hc : ∀ x ∈ Bᶜ, f x ≤ c) :
    (∫⁻ x, f x ∂μ) ≤
      a * μ A + b * μ (B \ A) + c * μ Bᶜ := by
  let g : α → ENNReal := fun x =>
    A.indicator (fun _ => a) x +
      (B \ A).indicator (fun _ => b) x +
        Bᶜ.indicator (fun _ => c) x
  have hg : Measurable g := by
    exact ((measurable_const.indicator hA).add
      (measurable_const.indicator (hB.diff hA))).add
      (measurable_const.indicator hB.compl)
  have hpoint : ∀ x, f x ≤ g x := by
    intro x
    by_cases hxA : x ∈ A
    · have hxB : x ∈ B := hAB hxA
      simp [g, hxA, hxB, ha x hxA]
    · by_cases hxB : x ∈ B
      · have hxDiff : x ∈ B \ A := ⟨hxB, hxA⟩
        simp [g, hxA, hxB, hxDiff, hb x hxDiff]
      · have hxCompl : x ∈ Bᶜ := hxB
        simp [g, hxA, hxB, hxCompl, hc x hxCompl]
  calc
    (∫⁻ x, f x ∂μ) ≤ ∫⁻ x, g x ∂μ := lintegral_mono hpoint
    _ = a * μ A + b * μ (B \ A) + c * μ Bᶜ := by
      dsimp [g]
      calc
        (∫⁻ x, A.indicator (fun _ => a) x +
            (B \ A).indicator (fun _ => b) x +
              Bᶜ.indicator (fun _ => c) x ∂μ) =
          (∫⁻ x, A.indicator (fun _ => a) x ∂μ) +
            (∫⁻ x, (B \ A).indicator (fun _ => b) x ∂μ) +
              ∫⁻ x, Bᶜ.indicator (fun _ => c) x ∂μ := by
                have houter := lintegral_add_left (μ := μ)
                  (((measurable_const : Measurable (fun _ : α => a)).indicator hA).add
                    ((measurable_const : Measurable (fun _ : α => b)).indicator
                      (hB.diff hA)))
                  (Bᶜ.indicator fun _ : α => c)
                have hinner := lintegral_add_left (μ := μ)
                  ((measurable_const : Measurable (fun _ : α => a)).indicator hA)
                  ((B \ A).indicator fun _ : α => b)
                rw [show (∫⁻ x, A.indicator (fun _ => a) x +
                    (B \ A).indicator (fun _ => b) x +
                      Bᶜ.indicator (fun _ => c) x ∂μ) =
                    (∫⁻ x, A.indicator (fun _ => a) x +
                      (B \ A).indicator (fun _ => b) x ∂μ) +
                        ∫⁻ x, Bᶜ.indicator (fun _ => c) x ∂μ by
                      simpa only [Pi.add_apply] using houter]
                rw [show (∫⁻ x, A.indicator (fun _ => a) x +
                    (B \ A).indicator (fun _ => b) x ∂μ) =
                    (∫⁻ x, A.indicator (fun _ => a) x ∂μ) +
                      ∫⁻ x, (B \ A).indicator (fun _ => b) x ∂μ by
                        simpa only [Pi.add_apply] using hinner]
        _ = a * μ A + b * μ (B \ A) + c * μ Bᶜ := by
          rw [lintegral_indicator_const hA,
            lintegral_indicator_const (hB.diff hA),
            lintegral_indicator_const hB.compl]

/-- Algebraic form of the three-region estimate. A favorable region of mass
at least `r`, together with a bad region of mass at most `s`, gives a bound
whose limiting coefficient is the convex combination `a*r + b*(1-r)`.
The additional `c*s` term is deliberately conservative. -/
theorem threeRegionWeightedSum_le
    {a b c r s x d e : ENNReal}
    (hab : a ≤ b) (hr : r ≤ x) (he : e ≤ s)
    (hsum : x + d + e = 1) :
    a * x + b * d + c * e ≤
      a * r + b * (1 - r) + c * s := by
  obtain ⟨z, rfl⟩ := exists_add_of_le hr
  have hone : 1 = r + (z + d + e) := by
    rw [← hsum]
    ac_rfl
  have hrTop : r ≠ ∞ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    calc
      r ≤ r + (z + d + e) := le_add_right le_rfl
      _ = 1 := hone.symm
  have hzd : z + d ≤ 1 - r := by
    rw [hone, ENNReal.add_sub_cancel_left hrTop]
    exact le_add_right le_rfl
  calc
    a * (r + z) + b * d + c * e =
        a * r + a * z + b * d + c * e := by ring
    _ ≤ a * r + b * z + b * d + c * e := by gcongr
    _ = a * r + b * (z + d) + c * e := by ring
    _ ≤ a * r + b * (1 - r) + c * s := by gcongr

/-- The favorable, intermediate, and complementary regions associated with
nested measurable sets partition a probability measure's mass. -/
theorem measure_nested_partition
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {A B : Set α}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B) :
    μ A + μ (B \ A) + μ Bᶜ = 1 := by
  have hBsplit : μ B = μ A + μ (B \ A) := by
    rw [← measure_union Set.disjoint_sdiff_right (hB.diff hA),
      Set.union_sdiff_cancel hAB]
  rw [← hBsplit, ← measure_union disjoint_compl_right hB.compl,
    Set.union_compl_self, measure_univ]

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

/-- Eventually the probability of leaving the expanding momentum band is
smaller than a fixed fraction of the certified inward displacement. This is
the strict scalar budget underlying the forthcoming Lyapunov drift. -/
theorem eventually_gaussianSoftAbs_tail_drift_budget :
    ∀ᶠ q : ℝ in Filter.atTop,
      1 - (gaussianSoftAbsTailBandMass q).toReal <
        (gaussianSoftAbsTailBandMass q).toReal *
          gaussianSoftAbsUnitMinSpeed / 8 := by
  have hmass : Filter.Tendsto
      (fun q : ℝ => (gaussianSoftAbsTailBandMass q).toReal)
      Filter.atTop (nhds 1) := by
    simpa [Function.comp_def] using
      (ENNReal.tendsto_toReal (by norm_num : (1 : ENNReal) ≠ ∞)).comp
        gaussianSoftAbsTailBandMass_tendsto_one
  have hbudget : Filter.Tendsto
      (fun q : ℝ => 1 - (gaussianSoftAbsTailBandMass q).toReal -
        (gaussianSoftAbsTailBandMass q).toReal *
          gaussianSoftAbsUnitMinSpeed / 8)
      Filter.atTop
      (nhds (1 - 1 - 1 * gaussianSoftAbsUnitMinSpeed / 8)) := by
    exact (tendsto_const_nhds.sub hmass).sub
      ((hmass.mul_const gaussianSoftAbsUnitMinSpeed).div_const 8)
  have hlimit :
      1 - 1 - 1 * gaussianSoftAbsUnitMinSpeed / 8 < 0 := by
    have := gaussianSoftAbsUnitMinSpeed_pos
    linarith
  filter_upwards [hbudget.eventually (Iio_mem_nhds hlimit)] with q hq
  linarith

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

/-- Symmetric expanding-band inward floor for the actual negative-tail
position transition. -/
theorem gaussianSoftAbsTailBandMass_neg_mul_quarter_le_inward
    (q : Position Unit) :
    gaussianSoftAbsTailBandMass (-q Unit.unit) * (4 : ENNReal)⁻¹ ≤
      gaussianSoftAbsMultinomialTransition 1 1 q
        {y | q Unit.unit + gaussianSoftAbsUnitMinSpeed ≤ y Unit.unit} := by
  let momentumSet : Set (Momentum Unit) :=
    {p | |p Unit.unit| ≤ -q Unit.unit / 2 - 2}
  let inward : Set (Position Unit) :=
    {y | q Unit.unit + gaussianSoftAbsUnitMinSpeed ≤ y Unit.unit}
  have hmomentumSet : MeasurableSet momentumSet :=
    measurableSet_le (measurable_pi_apply _).abs measurable_const
  have hinward : MeasurableSet inward :=
    measurableSet_le measurable_const (measurable_pi_apply _)
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
      exact
        quarter_le_gaussianSoftAbsPhaseTransition_inward_of_neg_abs_momentum
          q p hp)
  simpa [momentumSet, inward, gaussianSoftAbsTailBandMass,
    gaussianSoftAbsMultinomialTransition, riemannianMomentumKernel,
    gaussianSoftAbsMomentumProbability_eq_zero] using h

/-- Symmetric expanding-band non-outward mass on the negative tail. -/
theorem gaussianSoftAbsTailBandMass_neg_le_nonoutward
    (q : Position Unit) :
    gaussianSoftAbsTailBandMass (-q Unit.unit) ≤
      gaussianSoftAbsMultinomialTransition 1 1 q
        {y | q Unit.unit ≤ y Unit.unit} := by
  let momentumSet : Set (Momentum Unit) :=
    {p | |p Unit.unit| ≤ -q Unit.unit / 2 - 2}
  let nonoutward : Set (Position Unit) :=
    {y | q Unit.unit ≤ y Unit.unit}
  have hmomentumSet : MeasurableSet momentumSet :=
    measurableSet_le (measurable_pi_apply _).abs measurable_const
  have hnonoutward : MeasurableSet nonoutward :=
    measurableSet_le measurable_const (measurable_pi_apply _)
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
        gaussianSoftAbsPhaseTransition_nonoutward_of_neg_abs_momentum q p hp)
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

/-- Finite relativistic speed gives a global exponential-moment growth
bound, independent of the current position. -/
theorem lintegral_gaussianSoftAbsExpLyapunov_le_global
    (t : ℝ) (ht : 0 ≤ t) (q : Position Unit) :
    (∫⁻ y, gaussianSoftAbsExpLyapunov t y
        ∂gaussianSoftAbsMultinomialTransition 1 1 q) ≤
      ENNReal.ofReal (Real.exp t) * gaussianSoftAbsExpLyapunov t q := by
  let μ := gaussianSoftAbsMultinomialTransition 1 1 q
  let C : Set (Position Unit) := {y | |y Unit.unit - q Unit.unit| < 1}
  have hC : MeasurableSet C := by
    exact measurableSet_lt
      (((measurable_pi_apply Unit.unit).sub measurable_const).abs)
      measurable_const
  have hCmass : μ C = 1 :=
    gaussianSoftAbsMultinomialTransition_unit_position_support q
  have hCcompl : μ Cᶜ = 0 := by
    rw [measure_compl hC (by rw [hCmass]; norm_num), hCmass]
    simp
  have hCae : ∀ᵐ y ∂μ, y ∈ C := by
    rw [ae_iff]
    simpa [Set.compl_def] using hCcompl
  calc
    (∫⁻ y, gaussianSoftAbsExpLyapunov t y ∂μ) ≤
        ∫⁻ _y, gaussianSoftAbsExpWeight t (|q Unit.unit| + 1) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hCae] with y hy
      unfold gaussianSoftAbsExpLyapunov gaussianSoftAbsExpWeight
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      rw [abs_of_nonneg (by positivity : 0 ≤ |q Unit.unit| + 1)]
      apply mul_le_mul_of_nonneg_left _ ht
      dsimp [C] at hy
      have habs := abs_add_le (y Unit.unit - q Unit.unit) (q Unit.unit)
      rw [sub_add_cancel] at habs
      linarith
    _ = gaussianSoftAbsExpWeight t (|q Unit.unit| + 1) := by simp
    _ = ENNReal.ofReal (Real.exp t) * gaussianSoftAbsExpLyapunov t q := by
      unfold gaussianSoftAbsExpLyapunov gaussianSoftAbsExpWeight
      rw [abs_of_nonneg (by positivity : 0 ≤ |q Unit.unit| + 1)]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring

/-- Exact three-region exponential expectation bound on the positive tail.
The three coefficients correspond to a certified inward move, a non-outward
move, and the globally bounded outward displacement. -/
theorem lintegral_gaussianSoftAbsExpLyapunov_le_of_pos
    (t : ℝ) (ht : 0 ≤ t) (q : Position Unit) (hq : 2 ≤ q Unit.unit) :
    (∫⁻ y, gaussianSoftAbsExpLyapunov t y
        ∂gaussianSoftAbsMultinomialTransition 1 1 q) ≤
      gaussianSoftAbsExpWeight t
          (q Unit.unit - gaussianSoftAbsUnitMinSpeed) *
          gaussianSoftAbsMultinomialTransition 1 1 q
            {y | y Unit.unit ≤
              q Unit.unit - gaussianSoftAbsUnitMinSpeed} +
        gaussianSoftAbsExpWeight t (q Unit.unit) *
          gaussianSoftAbsMultinomialTransition 1 1 q
            ({y | y Unit.unit ≤ q Unit.unit} \
              {y | y Unit.unit ≤
                q Unit.unit - gaussianSoftAbsUnitMinSpeed}) +
        gaussianSoftAbsExpWeight t (q Unit.unit + 1) *
          gaussianSoftAbsMultinomialTransition 1 1 q
            {y | y Unit.unit ≤ q Unit.unit}ᶜ := by
  let μ := gaussianSoftAbsMultinomialTransition 1 1 q
  let A : Set (Position Unit) :=
    {y | y Unit.unit ≤ q Unit.unit - gaussianSoftAbsUnitMinSpeed}
  let B : Set (Position Unit) := {y | y Unit.unit ≤ q Unit.unit}
  let C : Set (Position Unit) := {y | |y Unit.unit - q Unit.unit| < 1}
  let f : Position Unit → ENNReal := fun y =>
    C.indicator (gaussianSoftAbsExpLyapunov t) y
  have hA : MeasurableSet A :=
    measurableSet_le (measurable_pi_apply _) measurable_const
  have hB : MeasurableSet B :=
    measurableSet_le (measurable_pi_apply _) measurable_const
  have hC : MeasurableSet C := by
    exact measurableSet_lt
      (((measurable_pi_apply Unit.unit).sub measurable_const).abs)
      measurable_const
  have hAB : A ⊆ B := by
    intro y hy
    have hδ := gaussianSoftAbsUnitMinSpeed_pos
    dsimp [A, B] at hy ⊢
    linarith
  have hCmass : μ C = 1 := by
    exact gaussianSoftAbsMultinomialTransition_unit_position_support q
  have hCcompl : μ Cᶜ = 0 := by
    rw [measure_compl hC (by rw [hCmass]; norm_num), hCmass]
    simp
  have hCae : ∀ᵐ y ∂μ, y ∈ C := by
    rw [ae_iff]
    simpa [Set.compl_def] using hCcompl
  have hIntegral :
      (∫⁻ y, f y ∂μ) = ∫⁻ y, gaussianSoftAbsExpLyapunov t y ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hCae] with y hy
    simp [f, hy]
  have hqδ : 0 ≤ q Unit.unit - gaussianSoftAbsUnitMinSpeed := by
    have hδ := gaussianSoftAbsUnitMinSpeed_lt_one
    linarith
  have ha : ∀ y ∈ A, f y ≤
      gaussianSoftAbsExpWeight t
        (q Unit.unit - gaussianSoftAbsUnitMinSpeed) := by
    intro y hyA
    by_cases hyC : y ∈ C
    · rw [show f y = gaussianSoftAbsExpLyapunov t y by simp [f, hyC]]
      unfold gaussianSoftAbsExpLyapunov gaussianSoftAbsExpWeight
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hy0 : 0 ≤ y Unit.unit := by
        dsimp [C] at hyC
        rw [abs_lt] at hyC
        linarith
      rw [abs_of_nonneg hy0, abs_of_nonneg hqδ]
      apply mul_le_mul_of_nonneg_left _ ht
      exact hyA
    · simp [f, hyC]
  have hb : ∀ y ∈ B \ A, f y ≤
      gaussianSoftAbsExpWeight t (q Unit.unit) := by
    intro y hyBA
    by_cases hyC : y ∈ C
    · rw [show f y = gaussianSoftAbsExpLyapunov t y by simp [f, hyC]]
      unfold gaussianSoftAbsExpLyapunov gaussianSoftAbsExpWeight
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hy0 : 0 ≤ y Unit.unit := by
        dsimp [C] at hyC
        rw [abs_lt] at hyC
        linarith
      rw [abs_of_nonneg hy0, abs_of_nonneg (by linarith : 0 ≤ q Unit.unit)]
      exact mul_le_mul_of_nonneg_left hyBA.1 ht
    · simp [f, hyC]
  have hc : ∀ y ∈ Bᶜ, f y ≤
      gaussianSoftAbsExpWeight t (q Unit.unit + 1) := by
    intro y hyB
    by_cases hyC : y ∈ C
    · rw [show f y = gaussianSoftAbsExpLyapunov t y by simp [f, hyC]]
      unfold gaussianSoftAbsExpLyapunov gaussianSoftAbsExpWeight
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hy0 : 0 ≤ y Unit.unit := by
        change ¬y Unit.unit ≤ q Unit.unit at hyB
        have hyB' : q Unit.unit < y Unit.unit := lt_of_not_ge hyB
        linarith
      have hyUpper : y Unit.unit ≤ q Unit.unit + 1 := by
        dsimp [C] at hyC
        rw [abs_lt] at hyC
        linarith
      rw [abs_of_nonneg hy0,
        abs_of_nonneg (by linarith : 0 ≤ q Unit.unit + 1)]
      exact mul_le_mul_of_nonneg_left hyUpper ht
    · simp [f, hyC]
  rw [← hIntegral]
  exact lintegral_le_of_nested_event_bounds μ hA hB hAB f
    (gaussianSoftAbsExpWeight t
      (q Unit.unit - gaussianSoftAbsUnitMinSpeed))
    (gaussianSoftAbsExpWeight t (q Unit.unit))
    (gaussianSoftAbsExpWeight t (q Unit.unit + 1)) ha hb hc

/-- Symmetric three-region exponential expectation bound on the negative
tail. -/
theorem lintegral_gaussianSoftAbsExpLyapunov_le_of_neg
    (t : ℝ) (ht : 0 ≤ t) (q : Position Unit) (hq : q Unit.unit ≤ -2) :
    (∫⁻ y, gaussianSoftAbsExpLyapunov t y
        ∂gaussianSoftAbsMultinomialTransition 1 1 q) ≤
      gaussianSoftAbsExpWeight t
          (-q Unit.unit - gaussianSoftAbsUnitMinSpeed) *
          gaussianSoftAbsMultinomialTransition 1 1 q
            {y | q Unit.unit + gaussianSoftAbsUnitMinSpeed ≤ y Unit.unit} +
        gaussianSoftAbsExpWeight t (-q Unit.unit) *
          gaussianSoftAbsMultinomialTransition 1 1 q
            ({y | q Unit.unit ≤ y Unit.unit} \
              {y | q Unit.unit + gaussianSoftAbsUnitMinSpeed ≤ y Unit.unit}) +
        gaussianSoftAbsExpWeight t (-q Unit.unit + 1) *
          gaussianSoftAbsMultinomialTransition 1 1 q
            {y | q Unit.unit ≤ y Unit.unit}ᶜ := by
  let μ := gaussianSoftAbsMultinomialTransition 1 1 q
  let A : Set (Position Unit) :=
    {y | q Unit.unit + gaussianSoftAbsUnitMinSpeed ≤ y Unit.unit}
  let B : Set (Position Unit) := {y | q Unit.unit ≤ y Unit.unit}
  let C : Set (Position Unit) := {y | |y Unit.unit - q Unit.unit| < 1}
  let f : Position Unit → ENNReal := fun y =>
    C.indicator (gaussianSoftAbsExpLyapunov t) y
  have hA : MeasurableSet A :=
    measurableSet_le measurable_const (measurable_pi_apply _)
  have hB : MeasurableSet B :=
    measurableSet_le measurable_const (measurable_pi_apply _)
  have hC : MeasurableSet C := by
    exact measurableSet_lt
      (((measurable_pi_apply Unit.unit).sub measurable_const).abs)
      measurable_const
  have hAB : A ⊆ B := by
    intro y hy
    have hδ := gaussianSoftAbsUnitMinSpeed_pos
    dsimp [A, B] at hy ⊢
    linarith
  have hCmass : μ C = 1 :=
    gaussianSoftAbsMultinomialTransition_unit_position_support q
  have hCcompl : μ Cᶜ = 0 := by
    rw [measure_compl hC (by rw [hCmass]; norm_num), hCmass]
    simp
  have hCae : ∀ᵐ y ∂μ, y ∈ C := by
    rw [ae_iff]
    simpa [Set.compl_def] using hCcompl
  have hIntegral :
      (∫⁻ y, f y ∂μ) = ∫⁻ y, gaussianSoftAbsExpLyapunov t y ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hCae] with y hy
    simp [f, hy]
  have hqδ : 0 ≤ -q Unit.unit - gaussianSoftAbsUnitMinSpeed := by
    have hδ := gaussianSoftAbsUnitMinSpeed_lt_one
    linarith
  have ha : ∀ y ∈ A, f y ≤
      gaussianSoftAbsExpWeight t
        (-q Unit.unit - gaussianSoftAbsUnitMinSpeed) := by
    intro y hyA
    by_cases hyC : y ∈ C
    · rw [show f y = gaussianSoftAbsExpLyapunov t y by simp [f, hyC]]
      unfold gaussianSoftAbsExpLyapunov gaussianSoftAbsExpWeight
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hy0 : y Unit.unit ≤ 0 := by
        dsimp [C] at hyC
        rw [abs_lt] at hyC
        linarith
      rw [abs_of_nonpos hy0, abs_of_nonneg hqδ]
      apply mul_le_mul_of_nonneg_left _ ht
      change q Unit.unit + gaussianSoftAbsUnitMinSpeed ≤ y Unit.unit at hyA
      linarith
    · simp [f, hyC]
  have hb : ∀ y ∈ B \ A, f y ≤
      gaussianSoftAbsExpWeight t (-q Unit.unit) := by
    intro y hyBA
    by_cases hyC : y ∈ C
    · rw [show f y = gaussianSoftAbsExpLyapunov t y by simp [f, hyC]]
      unfold gaussianSoftAbsExpLyapunov gaussianSoftAbsExpWeight
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hy0 : y Unit.unit ≤ 0 := by
        dsimp [C] at hyC
        rw [abs_lt] at hyC
        linarith
      rw [abs_of_nonpos hy0,
        abs_of_nonneg (by linarith : 0 ≤ -q Unit.unit)]
      have hyB : q Unit.unit ≤ y Unit.unit := hyBA.1
      exact mul_le_mul_of_nonneg_left (neg_le_neg hyB) ht
    · simp [f, hyC]
  have hc : ∀ y ∈ Bᶜ, f y ≤
      gaussianSoftAbsExpWeight t (-q Unit.unit + 1) := by
    intro y hyB
    by_cases hyC : y ∈ C
    · rw [show f y = gaussianSoftAbsExpLyapunov t y by simp [f, hyC]]
      unfold gaussianSoftAbsExpLyapunov gaussianSoftAbsExpWeight
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hy0 : y Unit.unit ≤ 0 := by
        change ¬q Unit.unit ≤ y Unit.unit at hyB
        have hyB' : y Unit.unit < q Unit.unit := lt_of_not_ge hyB
        linarith
      have hyLower : q Unit.unit - 1 ≤ y Unit.unit := by
        dsimp [C] at hyC
        rw [abs_lt] at hyC
        linarith
      rw [abs_of_nonpos hy0,
        abs_of_nonneg (by linarith : 0 ≤ -q Unit.unit + 1)]
      exact mul_le_mul_of_nonneg_left (by linarith) ht
    · simp [f, hyC]
  rw [← hIntegral]
  exact lintegral_le_of_nested_event_bounds μ hA hB hAB f
    (gaussianSoftAbsExpWeight t
      (-q Unit.unit - gaussianSoftAbsUnitMinSpeed))
    (gaussianSoftAbsExpWeight t (-q Unit.unit))
    (gaussianSoftAbsExpWeight t (-q Unit.unit + 1)) ha hb hc

/-- Probability-free coefficient form of the positive-tail expectation
bound. The first term records the expanding-band inward floor; the last term
charges the worst possible outward weight only to the band-complement mass.
-/
theorem lintegral_gaussianSoftAbsExpLyapunov_le_tailCoefficient_of_pos
    (t : ℝ) (ht : 0 ≤ t) (q : Position Unit) (hq : 2 ≤ q Unit.unit) :
    (∫⁻ y, gaussianSoftAbsExpLyapunov t y
        ∂gaussianSoftAbsMultinomialTransition 1 1 q) ≤
      gaussianSoftAbsExpWeight t
          (q Unit.unit - gaussianSoftAbsUnitMinSpeed) *
          (gaussianSoftAbsTailBandMass (q Unit.unit) * (4 : ENNReal)⁻¹) +
        gaussianSoftAbsExpWeight t (q Unit.unit) *
          (1 - gaussianSoftAbsTailBandMass (q Unit.unit) *
            (4 : ENNReal)⁻¹) +
        gaussianSoftAbsExpWeight t (q Unit.unit + 1) *
          (1 - gaussianSoftAbsTailBandMass (q Unit.unit)) := by
  let μ := gaussianSoftAbsMultinomialTransition 1 1 q
  let A : Set (Position Unit) :=
    {y | y Unit.unit ≤ q Unit.unit - gaussianSoftAbsUnitMinSpeed}
  let B : Set (Position Unit) := {y | y Unit.unit ≤ q Unit.unit}
  let a := gaussianSoftAbsExpWeight t
    (q Unit.unit - gaussianSoftAbsUnitMinSpeed)
  let b := gaussianSoftAbsExpWeight t (q Unit.unit)
  let c := gaussianSoftAbsExpWeight t (q Unit.unit + 1)
  let r := gaussianSoftAbsTailBandMass (q Unit.unit) * (4 : ENNReal)⁻¹
  let s := 1 - gaussianSoftAbsTailBandMass (q Unit.unit)
  have hA : MeasurableSet A :=
    measurableSet_le (measurable_pi_apply _) measurable_const
  have hB : MeasurableSet B :=
    measurableSet_le (measurable_pi_apply _) measurable_const
  have hAB : A ⊆ B := by
    intro y hy
    have hδ := gaussianSoftAbsUnitMinSpeed_pos
    dsimp [A, B] at hy ⊢
    linarith
  have hab : a ≤ b := by
    unfold a b gaussianSoftAbsExpWeight
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hqδ : 0 ≤ q Unit.unit - gaussianSoftAbsUnitMinSpeed := by
      have hδ := gaussianSoftAbsUnitMinSpeed_lt_one
      linarith
    rw [abs_of_nonneg hqδ, abs_of_nonneg (by linarith : 0 ≤ q Unit.unit)]
    exact mul_le_mul_of_nonneg_left (sub_le_self _
      gaussianSoftAbsUnitMinSpeed_pos.le) ht
  have hr : r ≤ μ A := by
    exact gaussianSoftAbsTailBandMass_mul_quarter_le_inward q
  have hmassB : gaussianSoftAbsTailBandMass (q Unit.unit) ≤ μ B := by
    exact gaussianSoftAbsTailBandMass_le_nonoutward q
  have he : μ Bᶜ ≤ s := by
    rw [measure_compl hB (measure_ne_top μ B), measure_univ]
    exact tsub_le_tsub_left hmassB 1
  have hsum : μ A + μ (B \ A) + μ Bᶜ = 1 :=
    measure_nested_partition μ hA hB hAB
  exact (lintegral_gaussianSoftAbsExpLyapunov_le_of_pos t ht q hq).trans
    (threeRegionWeightedSum_le hab hr he hsum)

/-- Coefficient form of the symmetric negative-tail estimate. -/
theorem lintegral_gaussianSoftAbsExpLyapunov_le_tailCoefficient_of_neg
    (t : ℝ) (ht : 0 ≤ t) (q : Position Unit) (hq : q Unit.unit ≤ -2) :
    (∫⁻ y, gaussianSoftAbsExpLyapunov t y
        ∂gaussianSoftAbsMultinomialTransition 1 1 q) ≤
      gaussianSoftAbsExpWeight t
          (-q Unit.unit - gaussianSoftAbsUnitMinSpeed) *
          (gaussianSoftAbsTailBandMass (-q Unit.unit) * (4 : ENNReal)⁻¹) +
        gaussianSoftAbsExpWeight t (-q Unit.unit) *
          (1 - gaussianSoftAbsTailBandMass (-q Unit.unit) *
            (4 : ENNReal)⁻¹) +
        gaussianSoftAbsExpWeight t (-q Unit.unit + 1) *
          (1 - gaussianSoftAbsTailBandMass (-q Unit.unit)) := by
  let μ := gaussianSoftAbsMultinomialTransition 1 1 q
  let A : Set (Position Unit) :=
    {y | q Unit.unit + gaussianSoftAbsUnitMinSpeed ≤ y Unit.unit}
  let B : Set (Position Unit) := {y | q Unit.unit ≤ y Unit.unit}
  let a := gaussianSoftAbsExpWeight t
    (-q Unit.unit - gaussianSoftAbsUnitMinSpeed)
  let b := gaussianSoftAbsExpWeight t (-q Unit.unit)
  let c := gaussianSoftAbsExpWeight t (-q Unit.unit + 1)
  let r := gaussianSoftAbsTailBandMass (-q Unit.unit) * (4 : ENNReal)⁻¹
  let s := 1 - gaussianSoftAbsTailBandMass (-q Unit.unit)
  have hA : MeasurableSet A :=
    measurableSet_le measurable_const (measurable_pi_apply _)
  have hB : MeasurableSet B :=
    measurableSet_le measurable_const (measurable_pi_apply _)
  have hAB : A ⊆ B := by
    intro y hy
    have hδ := gaussianSoftAbsUnitMinSpeed_pos
    dsimp [A, B] at hy ⊢
    linarith
  have hab : a ≤ b := by
    unfold a b gaussianSoftAbsExpWeight
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hqδ : 0 ≤ -q Unit.unit - gaussianSoftAbsUnitMinSpeed := by
      have hδ := gaussianSoftAbsUnitMinSpeed_lt_one
      linarith
    rw [abs_of_nonneg hqδ,
      abs_of_nonneg (by linarith : 0 ≤ -q Unit.unit)]
    exact mul_le_mul_of_nonneg_left (sub_le_self _
      gaussianSoftAbsUnitMinSpeed_pos.le) ht
  have hr : r ≤ μ A := by
    exact gaussianSoftAbsTailBandMass_neg_mul_quarter_le_inward q
  have hmassB : gaussianSoftAbsTailBandMass (-q Unit.unit) ≤ μ B := by
    exact gaussianSoftAbsTailBandMass_neg_le_nonoutward q
  have he : μ Bᶜ ≤ s := by
    rw [measure_compl hB (measure_ne_top μ B), measure_univ]
    exact tsub_le_tsub_left hmassB 1
  have hsum : μ A + μ (B \ A) + μ Bᶜ = 1 :=
    measure_nested_partition μ hA hB hAB
  exact (lintegral_gaussianSoftAbsExpLyapunov_le_of_neg t ht q hq).trans
    (threeRegionWeightedSum_le hab hr he hsum)

/-- Dimensionless coefficient obtained after factoring the current
exponential Lyapunov value out of the positive-tail estimate. -/
noncomputable def gaussianSoftAbsTailDriftCoefficient (t q : ℝ) : ENNReal :=
  ENNReal.ofReal (Real.exp (-t * gaussianSoftAbsUnitMinSpeed)) *
      (gaussianSoftAbsTailBandMass q * (4 : ENNReal)⁻¹) +
    (1 - gaussianSoftAbsTailBandMass q * (4 : ENNReal)⁻¹) +
    ENNReal.ofReal (Real.exp t) *
      (1 - gaussianSoftAbsTailBandMass q)

theorem gaussianSoftAbsExpWeight_sub_minSpeed
    (t : ℝ) (q : ℝ) (hq : 2 ≤ q) :
    gaussianSoftAbsExpWeight t (q - gaussianSoftAbsUnitMinSpeed) =
      ENNReal.ofReal (Real.exp (-t * gaussianSoftAbsUnitMinSpeed)) *
        gaussianSoftAbsExpWeight t q := by
  have hδ := gaussianSoftAbsUnitMinSpeed_lt_one
  unfold gaussianSoftAbsExpWeight
  rw [abs_of_nonneg (by linarith : 0 ≤ q - gaussianSoftAbsUnitMinSpeed),
    abs_of_nonneg (by linarith : 0 ≤ q)]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

theorem gaussianSoftAbsExpWeight_add_one
    (t : ℝ) (q : ℝ) (hq : 0 ≤ q) :
    gaussianSoftAbsExpWeight t (q + 1) =
      ENNReal.ofReal (Real.exp t) * gaussianSoftAbsExpWeight t q := by
  unfold gaussianSoftAbsExpWeight
  rw [abs_of_nonneg (by linarith : 0 ≤ q + 1), abs_of_nonneg hq]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

theorem gaussianSoftAbsExpWeight_neg (t x : ℝ) :
    gaussianSoftAbsExpWeight t (-x) = gaussianSoftAbsExpWeight t x := by
  simp [gaussianSoftAbsExpWeight]

/-- The positive-tail transition contracts the current Lyapunov value by the
explicit dimensionless tail coefficient. -/
theorem lintegral_gaussianSoftAbsExpLyapunov_le_mul_tailDriftCoefficient_of_pos
    (t : ℝ) (ht : 0 ≤ t) (q : Position Unit) (hq : 2 ≤ q Unit.unit) :
    (∫⁻ y, gaussianSoftAbsExpLyapunov t y
        ∂gaussianSoftAbsMultinomialTransition 1 1 q) ≤
      gaussianSoftAbsTailDriftCoefficient t (q Unit.unit) *
        gaussianSoftAbsExpLyapunov t q := by
  refine (lintegral_gaussianSoftAbsExpLyapunov_le_tailCoefficient_of_pos
    t ht q hq).trans_eq ?_
  rw [gaussianSoftAbsExpWeight_sub_minSpeed t (q Unit.unit) hq,
    gaussianSoftAbsExpWeight_add_one t (q Unit.unit) (by linarith)]
  unfold gaussianSoftAbsExpLyapunov gaussianSoftAbsTailDriftCoefficient
  ring

/-- Symmetric negative-tail contraction by the same coefficient evaluated at
the absolute tail coordinate. -/
theorem lintegral_gaussianSoftAbsExpLyapunov_le_mul_tailDriftCoefficient_of_neg
    (t : ℝ) (ht : 0 ≤ t) (q : Position Unit) (hq : q Unit.unit ≤ -2) :
    (∫⁻ y, gaussianSoftAbsExpLyapunov t y
        ∂gaussianSoftAbsMultinomialTransition 1 1 q) ≤
      gaussianSoftAbsTailDriftCoefficient t (-q Unit.unit) *
        gaussianSoftAbsExpLyapunov t q := by
  refine (lintegral_gaussianSoftAbsExpLyapunov_le_tailCoefficient_of_neg
    t ht q hq).trans_eq ?_
  rw [gaussianSoftAbsExpWeight_sub_minSpeed t (-q Unit.unit) (by linarith),
    gaussianSoftAbsExpWeight_add_one t (-q Unit.unit) (by linarith),
    gaussianSoftAbsExpWeight_neg t (q Unit.unit)]
  unfold gaussianSoftAbsExpLyapunov gaussianSoftAbsTailDriftCoefficient
  ring

theorem gaussianSoftAbsTailDriftCoefficient_tendsto
    (t : ℝ) :
    Filter.Tendsto (gaussianSoftAbsTailDriftCoefficient t)
      Filter.atTop
      (nhds
        (ENNReal.ofReal (Real.exp (-t * gaussianSoftAbsUnitMinSpeed)) *
            (1 * (4 : ENNReal)⁻¹) +
          (1 - 1 * (4 : ENNReal)⁻¹) +
          ENNReal.ofReal (Real.exp t) * (1 - 1))) := by
  have hm := gaussianSoftAbsTailBandMass_tendsto_one
  have hr : Filter.Tendsto
      (fun q => gaussianSoftAbsTailBandMass q * (4 : ENNReal)⁻¹)
      Filter.atTop (nhds (1 * (4 : ENNReal)⁻¹)) :=
    ENNReal.Tendsto.mul_const (b := (4 : ENNReal)⁻¹) hm
      (Or.inr (by norm_num : (4 : ENNReal)⁻¹ ≠ ∞))
  have hremR : Filter.Tendsto
      (fun q => 1 - gaussianSoftAbsTailBandMass q * (4 : ENNReal)⁻¹)
      Filter.atTop (nhds (1 - 1 * (4 : ENNReal)⁻¹)) :=
    ENNReal.Tendsto.sub tendsto_const_nhds hr
      (Or.inl ENNReal.one_ne_top)
  have hremM : Filter.Tendsto
      (fun q => 1 - gaussianSoftAbsTailBandMass q)
      Filter.atTop (nhds (1 - 1)) :=
    ENNReal.Tendsto.sub tendsto_const_nhds hm
      (Or.inl ENNReal.one_ne_top)
  have hfirst := ENNReal.Tendsto.const_mul
    (a := ENNReal.ofReal (Real.exp (-t * gaussianSoftAbsUnitMinSpeed))) hr
    (Or.inr (ENNReal.ofReal_ne_top : ENNReal.ofReal
      (Real.exp (-t * gaussianSoftAbsUnitMinSpeed)) ≠ ∞))
  have hlast := ENNReal.Tendsto.const_mul
    (a := ENNReal.ofReal (Real.exp t)) hremM
    (Or.inr (ENNReal.ofReal_ne_top : ENNReal.ofReal (Real.exp t) ≠ ∞))
  exact (hfirst.add hremR).add hlast

theorem gaussianSoftAbsTailDriftCoefficient_limit_lt_one
    (t : ℝ) (ht : 0 < t) :
    ENNReal.ofReal (Real.exp (-t * gaussianSoftAbsUnitMinSpeed)) *
          (1 * (4 : ENNReal)⁻¹) +
        (1 - 1 * (4 : ENNReal)⁻¹) +
        ENNReal.ofReal (Real.exp t) * (1 - 1) < 1 := by
  have hneg : -t * gaussianSoftAbsUnitMinSpeed < 0 := by
    have hδ := gaussianSoftAbsUnitMinSpeed_pos
    nlinarith
  have hexp : ENNReal.ofReal
      (Real.exp (-t * gaussianSoftAbsUnitMinSpeed)) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    exact (Real.exp_lt_one_iff.mpr hneg)
  have hr0 : (4 : ENNReal)⁻¹ ≠ 0 := by norm_num
  have hrTop : (4 : ENNReal)⁻¹ ≠ ∞ := by norm_num
  have hmul := ENNReal.mul_lt_mul_right hr0 hrTop hexp
  simp only [one_mul, tsub_self, mul_zero, add_zero]
  calc
    ENNReal.ofReal (Real.exp (-t * gaussianSoftAbsUnitMinSpeed)) *
          (4 : ENNReal)⁻¹ + (1 - (4 : ENNReal)⁻¹) <
        1 * (4 : ENNReal)⁻¹ + (1 - (4 : ENNReal)⁻¹) := by
      have hadd := ENNReal.add_lt_add_right
        (by norm_num : 1 - (4 : ENNReal)⁻¹ ≠ ∞) hmul
      simpa [mul_comm, add_comm] using hadd
    _ = 1 := by
      rw [one_mul]
      rw [add_comm]
      exact tsub_add_cancel_of_le (by norm_num : (4 : ENNReal)⁻¹ ≤ 1)

/-- For every positive exponential scale, the explicit tail coefficient is
eventually uniformly subunit. -/
theorem eventually_gaussianSoftAbsTailDriftCoefficient_lt_one
    (t : ℝ) (ht : 0 < t) :
    ∀ᶠ q : ℝ in Filter.atTop,
      gaussianSoftAbsTailDriftCoefficient t q < 1 := by
  exact (gaussianSoftAbsTailDriftCoefficient_tendsto t).eventually
    (Iio_mem_nhds (gaussianSoftAbsTailDriftCoefficient_limit_lt_one t ht))

theorem exists_gaussianSoftAbsTailDriftCoefficient_le_rate
    (t : ℝ) (ht : 0 < t) :
    ∃ R : ℝ, ∃ rate : ENNReal, rate < 1 ∧
      ∀ x : ℝ, R ≤ x →
        gaussianSoftAbsTailDriftCoefficient t x ≤ rate := by
  let limit : ENNReal :=
    ENNReal.ofReal (Real.exp (-t * gaussianSoftAbsUnitMinSpeed)) *
          (1 * (4 : ENNReal)⁻¹) +
        (1 - 1 * (4 : ENNReal)⁻¹) +
        ENNReal.ofReal (Real.exp t) * (1 - 1)
  have hlimit : limit < 1 :=
    gaussianSoftAbsTailDriftCoefficient_limit_lt_one t ht
  obtain ⟨rate, hlimitRate, hrate⟩ := exists_between hlimit
  have heventually : ∀ᶠ x : ℝ in Filter.atTop,
      gaussianSoftAbsTailDriftCoefficient t x < rate :=
    (gaussianSoftAbsTailDriftCoefficient_tendsto t).eventually
      (Iio_mem_nhds hlimitRate)
  rw [Filter.eventually_atTop] at heventually
  obtain ⟨R, hR⟩ := heventually
  exact ⟨R, rate, hrate, fun x hx => (hR x hx).le⟩

/-- The bare one-dimensional Gaussian SoftAbs multinomial transition has a
strict exponential Lyapunov contraction outside a compact interval. -/
theorem exists_gaussianSoftAbs_outsideCompact_strict_drift
    (t : ℝ) (ht : 0 < t) :
    ∃ R : ℝ, ∃ rate : ENNReal, rate < 1 ∧
      ∀ q : Position Unit, R ≤ |q Unit.unit| →
        (∫⁻ y, gaussianSoftAbsExpLyapunov t y
            ∂gaussianSoftAbsMultinomialTransition 1 1 q) ≤
          rate * gaussianSoftAbsExpLyapunov t q := by
  obtain ⟨R₀, rate, hrate, hcoefficient⟩ :=
    exists_gaussianSoftAbsTailDriftCoefficient_le_rate t ht
  refine ⟨max R₀ 2, rate, hrate, ?_⟩
  intro q hq
  by_cases hq0 : 0 ≤ q Unit.unit
  · rw [abs_of_nonneg hq0] at hq
    have hqR₀ : R₀ ≤ q Unit.unit := le_trans (le_max_left _ _) hq
    have hq2 : 2 ≤ q Unit.unit := le_trans (le_max_right _ _) hq
    refine (lintegral_gaussianSoftAbsExpLyapunov_le_mul_tailDriftCoefficient_of_pos
      t ht.le q hq2).trans ?_
    simpa [mul_comm] using (mul_le_mul_right
      (hcoefficient _ hqR₀) (gaussianSoftAbsExpLyapunov t q))
  · have hq0' : q Unit.unit ≤ 0 := le_of_not_ge hq0
    rw [abs_of_nonpos hq0'] at hq
    have hqR₀ : R₀ ≤ -q Unit.unit := le_trans (le_max_left _ _) hq
    have hq2 : q Unit.unit ≤ -2 := by
      have := le_trans (le_max_right R₀ 2) hq
      linarith
    refine (lintegral_gaussianSoftAbsExpLyapunov_le_mul_tailDriftCoefficient_of_neg
      t ht.le q hq2).trans ?_
    simpa [mul_comm] using (mul_le_mul_right
      (hcoefficient _ hqR₀) (gaussianSoftAbsExpLyapunov t q))

/-- The outside-compact contraction and finite-speed bound combine into an
ordinary affine Foster--Lyapunov certificate for the actual bare sampler. -/
theorem exists_gaussianSoftAbs_hasAffineDrift
    (t : ℝ) (ht : 0 < t) :
    ∃ rate allowance : ENNReal,
      rate < 1 ∧ rate ≠ ∞ ∧ allowance ≠ ∞ ∧
        Mcmc.Kernel.HasAffineDrift
          (gaussianSoftAbsMultinomialTransition 1 1)
          (gaussianSoftAbsExpLyapunov t) rate allowance := by
  obtain ⟨R₀, rate, hrate, houtside⟩ :=
    exists_gaussianSoftAbs_outsideCompact_strict_drift t ht
  let R := max R₀ 0
  let allowance := ENNReal.ofReal (Real.exp t) *
    gaussianSoftAbsExpWeight t R
  have hR0 : 0 ≤ R := le_max_right _ _
  have hallowanceTop : allowance ≠ ∞ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  refine ⟨rate, allowance, hrate, ne_top_of_lt (hrate.trans_le le_top),
    hallowanceTop, measurable_gaussianSoftAbsExpLyapunov t, ?_⟩
  intro q
  by_cases hq : R ≤ |q Unit.unit|
  · have hR₀q : R₀ ≤ |q Unit.unit| := le_trans (le_max_left _ _) hq
    exact (houtside q hR₀q).trans (le_add_right le_rfl)
  · have hV : gaussianSoftAbsExpLyapunov t q ≤
        gaussianSoftAbsExpWeight t R := by
      unfold gaussianSoftAbsExpLyapunov gaussianSoftAbsExpWeight
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      rw [abs_of_nonneg hR0]
      exact mul_le_mul_of_nonneg_left (le_of_not_ge hq) ht.le
    calc
      (∫⁻ y, gaussianSoftAbsExpLyapunov t y
          ∂gaussianSoftAbsMultinomialTransition 1 1 q) ≤
          ENNReal.ofReal (Real.exp t) *
            gaussianSoftAbsExpLyapunov t q :=
        lintegral_gaussianSoftAbsExpLyapunov_le_global t ht.le q
      _ ≤ allowance := by
        simpa [mul_comm] using
          (mul_le_mul_right hV (ENNReal.ofReal (Real.exp t)))
      _ ≤ rate * gaussianSoftAbsExpLyapunov t q + allowance :=
        le_add_left le_rfl

/-- A positive exponential scale admits one fixed strict drift rate beyond a
finite positive-tail threshold. -/
theorem exists_gaussianSoftAbs_positiveTail_strict_drift
    (t : ℝ) (ht : 0 < t) :
    ∃ R : ℝ, ∃ rate : ENNReal, rate < 1 ∧
      ∀ q : Position Unit, R ≤ q Unit.unit →
        (∫⁻ y, gaussianSoftAbsExpLyapunov t y
            ∂gaussianSoftAbsMultinomialTransition 1 1 q) ≤
          rate * gaussianSoftAbsExpLyapunov t q := by
  let limit : ENNReal :=
    ENNReal.ofReal (Real.exp (-t * gaussianSoftAbsUnitMinSpeed)) *
          (1 * (4 : ENNReal)⁻¹) +
        (1 - 1 * (4 : ENNReal)⁻¹) +
        ENNReal.ofReal (Real.exp t) * (1 - 1)
  have hlimit : limit < 1 :=
    gaussianSoftAbsTailDriftCoefficient_limit_lt_one t ht
  obtain ⟨rate, hlimitRate, hrate⟩ := exists_between hlimit
  have heventually : ∀ᶠ q : ℝ in Filter.atTop,
      gaussianSoftAbsTailDriftCoefficient t q < rate :=
    (gaussianSoftAbsTailDriftCoefficient_tendsto t).eventually
      (Iio_mem_nhds hlimitRate)
  rw [Filter.eventually_atTop] at heventually
  obtain ⟨R₀, hR₀⟩ := heventually
  refine ⟨max R₀ 2, rate, hrate, ?_⟩
  intro q hq
  have hqR₀ : R₀ ≤ q Unit.unit := le_trans (le_max_left _ _) hq
  have hq2 : 2 ≤ q Unit.unit := le_trans (le_max_right _ _) hq
  refine (lintegral_gaussianSoftAbsExpLyapunov_le_mul_tailDriftCoefficient_of_pos
    t ht.le q hq2).trans ?_
  simpa [mul_comm] using (mul_le_mul_right
    (hR₀ _ hqR₀).le (gaussianSoftAbsExpLyapunov t q))

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
