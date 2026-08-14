import Mcmc.Hamiltonian.MultinomialHMC
import Mcmc.Hamiltonian.VolumePreservation
import Mathlib.Probability.Kernel.Invariance

/-!
# Invariance of the randomized multinomial trajectory transition

This module lifts trajectory re-rooting and leapfrog volume preservation to
the measure-level balance argument for multinomial HMC. The proof is organized
around the flow associated with an ordered pair of trajectory indices. Swapping
the indices and changing variables by the corresponding signed leapfrog map
leaves that flow integral unchanged.
-/

open MeasureTheory
open scoped BigOperators ENNReal ProbabilityTheory

namespace Mcmc.Hamiltonian

open ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- The (possibly unnormalized) Boltzmann measure on phase space. -/
noncomputable def phaseBoltzmannTarget (potential : Position ι → ℝ) :
    Measure (PhaseSpace ι) :=
  phaseVolume.withDensity (boltzmannWeight potential)

/-- Target-weighted probability flow from `origin` to `selected`. -/
noncomputable def trajectorySelectionFlow
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (origin selected : Fin (L + 1))
    (z : PhaseSpace ι) : ℝ≥0∞ :=
  boltzmannWeight potential z *
    trajectoryIndexPMF potential
      (offsetLeapfrogTrajectory gradient ε origin z) selected

theorem measurable_trajectorySelectionFlow
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) {L : ℕ} (origin selected : Fin (L + 1)) :
    Measurable (trajectorySelectionFlow potential gradient ε origin selected) := by
  unfold trajectorySelectionFlow
  simp only [trajectoryIndexPMF_apply, trajectoryNormalizer]
  apply Measurable.mul (measurable_boltzmannWeight hpotential)
  apply Measurable.mul
  · exact (measurable_boltzmannWeight hpotential).comp
      (measurable_offsetLeapfrogTrajectory hgradient ε origin selected)
  · apply Measurable.inv
    apply Finset.measurable_sum
    intro i hi
    exact (measurable_boltzmannWeight hpotential).comp
      (measurable_offsetLeapfrogTrajectory hgradient ε origin i)

theorem measurable_trajectoryIndexProbability
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) {L : ℕ} (origin selected : Fin (L + 1)) :
    Measurable fun z => trajectoryIndexPMF potential
      (offsetLeapfrogTrajectory gradient ε origin z) selected := by
  simp only [trajectoryIndexPMF_apply, trajectoryNormalizer]
  apply Measurable.mul
  · exact (measurable_boltzmannWeight hpotential).comp
      (measurable_offsetLeapfrogTrajectory hgradient ε origin selected)
  · apply Measurable.inv
    apply Finset.measurable_sum
    intro i hi
    exact (measurable_boltzmannWeight hpotential).comp
      (measurable_offsetLeapfrogTrajectory hgradient ε origin i)

/-- Subkernel corresponding to one ordered origin/selected index pair. -/
noncomputable def trajectoryIndexComponentKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (origin selected : Fin (L + 1))
    (hpotential : Measurable potential) (hgradient : Measurable gradient) :
    Kernel (PhaseSpace ι) (PhaseSpace ι) where
  toFun z := (trajectoryIndexPMF potential
      (offsetLeapfrogTrajectory gradient ε origin z) selected) •
    Measure.dirac (offsetLeapfrogTrajectory gradient ε origin z selected)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp only [Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul]
    exact (measurable_trajectoryIndexProbability hpotential hgradient ε origin selected).mul
      (measurable_const.indicator
        (measurable_offsetLeapfrogTrajectory hgradient ε origin selected hs))

theorem trajectoryIndexComponentKernel_apply
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (origin selected : Fin (L + 1))
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (z : PhaseSpace ι) (s : Set (PhaseSpace ι)) (hs : MeasurableSet s) :
    trajectoryIndexComponentKernel potential gradient ε origin selected
        hpotential hgradient z s =
      trajectoryIndexPMF potential
          (offsetLeapfrogTrajectory gradient ε origin z) selected *
        s.indicator (fun _ => 1) (offsetLeapfrogTrajectory gradient ε origin z selected) := by
  simp [trajectoryIndexComponentKernel, Measure.dirac_apply' _ hs]
  rfl

theorem trajectorySelectionFlow_reroot
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (origin selected : Fin (L + 1))
    (z : PhaseSpace ι) :
    trajectorySelectionFlow potential gradient ε origin selected z =
      trajectorySelectionFlow potential gradient ε selected origin
        (offsetLeapfrogTrajectory gradient ε origin z selected) :=
  Mcmc.Hamiltonian.boltzmann_trajectoryIndexPMF_flow_reroot
    potential gradient ε origin selected z

/-- The ordered-index flow integral is unchanged when its indices and event
coordinates are swapped. -/
theorem trajectorySelectionFlow_integral_swap
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) {L : ℕ} (origin selected : Fin (L + 1))
    (A B : Set (PhaseSpace ι)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫⁻ z, (A ∩ (fun z =>
        offsetLeapfrogTrajectory gradient ε origin z selected) ⁻¹' B).indicator
          (trajectorySelectionFlow potential gradient ε origin selected) z
        ∂phaseVolume =
      ∫⁻ z, (B ∩ (fun z =>
        offsetLeapfrogTrajectory gradient ε selected z origin) ⁻¹' A).indicator
          (trajectorySelectionFlow potential gradient ε selected origin) z
        ∂phaseVolume := by
  let T : PhaseSpace ι → PhaseSpace ι :=
    fun z => offsetLeapfrogTrajectory gradient ε origin z selected
  let reverseIntegrand : PhaseSpace ι → ℝ≥0∞ := fun z =>
    (B ∩ (fun z => offsetLeapfrogTrajectory gradient ε selected z origin) ⁻¹' A).indicator
      (trajectorySelectionFlow potential gradient ε selected origin) z
  have hreverse : Measurable reverseIntegrand := by
    unfold reverseIntegrand
    apply Measurable.indicator
    · exact measurable_trajectorySelectionFlow hpotential hgradient ε selected origin
    · exact hB.inter
        (measurable_offsetLeapfrogTrajectory hgradient ε selected origin hA)
  rw [← (measurePreserving_offsetLeapfrogTrajectory hgradient ε origin selected).lintegral_comp
    hreverse]
  apply lintegral_congr
  intro z
  unfold reverseIntegrand
  have hback : offsetLeapfrogTrajectory gradient ε selected
      (offsetLeapfrogTrajectory gradient ε origin z selected) origin = z := by
    rw [offsetLeapfrogTrajectory_reroot]
    rw [offsetLeapfrogTrajectory_origin]
  have hflow := trajectorySelectionFlow_reroot potential gradient ε origin selected z
  by_cases hzA : z ∈ A <;>
    by_cases hzB : offsetLeapfrogTrajectory gradient ε origin z selected ∈ B <;>
      simp [Set.indicator, hzA, hzB, hback, ← hflow]

/-- Paired ordered-index components satisfy the setwise balance identity. -/
theorem trajectoryIndexComponentKernel_balance
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) {L : ℕ} (origin selected : Fin (L + 1))
    {A B : Set (PhaseSpace ι)} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫⁻ z in A,
        trajectoryIndexComponentKernel potential gradient ε origin selected
          hpotential hgradient z B ∂phaseBoltzmannTarget potential =
      ∫⁻ z in B,
        trajectoryIndexComponentKernel potential gradient ε selected origin
          hpotential hgradient z A ∂phaseBoltzmannTarget potential := by
  unfold phaseBoltzmannTarget
  rw [setLIntegral_withDensity_eq_setLIntegral_mul phaseVolume
      (measurable_boltzmannWeight hpotential)
      ((trajectoryIndexComponentKernel potential gradient ε origin selected
        hpotential hgradient).measurable_coe hB) hA]
  rw [setLIntegral_withDensity_eq_setLIntegral_mul phaseVolume
      (measurable_boltzmannWeight hpotential)
      ((trajectoryIndexComponentKernel potential gradient ε selected origin
        hpotential hgradient).measurable_coe hA) hB]
  rw [← lintegral_indicator hA, ← lintegral_indicator hB]
  calc
    _ = ∫⁻ z, (A ∩ (fun z =>
          offsetLeapfrogTrajectory gradient ε origin z selected) ⁻¹' B).indicator
            (trajectorySelectionFlow potential gradient ε origin selected) z
          ∂phaseVolume := by
        apply lintegral_congr
        intro z
        change A.indicator (fun z => boltzmannWeight potential z *
          trajectoryIndexComponentKernel potential gradient ε origin selected
            hpotential hgradient z B) z = _
        by_cases hzA : z ∈ A <;>
          by_cases hzB : offsetLeapfrogTrajectory gradient ε origin z selected ∈ B <;>
            simp [Set.indicator, hzA, hzB, trajectorySelectionFlow,
              trajectoryIndexComponentKernel_apply potential gradient ε origin selected
                hpotential hgradient z B hB]
    _ = ∫⁻ z, (B ∩ (fun z =>
          offsetLeapfrogTrajectory gradient ε selected z origin) ⁻¹' A).indicator
            (trajectorySelectionFlow potential gradient ε selected origin) z
          ∂phaseVolume :=
      trajectorySelectionFlow_integral_swap hpotential hgradient ε origin selected
        A B hA hB
    _ = _ := by
        apply lintegral_congr
        intro z
        change _ = B.indicator (fun z => boltzmannWeight potential z *
          trajectoryIndexComponentKernel potential gradient ε selected origin
            hpotential hgradient z A) z
        by_cases hzB : z ∈ B <;>
          by_cases hzA : offsetLeapfrogTrajectory gradient ε selected z origin ∈ A <;>
            simp [Set.indicator, hzA, hzB, trajectorySelectionFlow,
              trajectoryIndexComponentKernel_apply potential gradient ε selected origin
                hpotential hgradient z A hA]

/-- The randomized transition row is the uniform sum of all ordered-index
component subkernels. -/
theorem randomizedMultinomialLeapfrogKernel_apply_set_eq_components
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) (z : PhaseSpace ι)
    (s : Set (PhaseSpace ι)) (hs : MeasurableSet s) :
    randomizedMultinomialLeapfrogKernel potential gradient ε L
        hpotential hgradient z s =
      ∑ origin : Fin (L + 1),
        PMF.uniformOfFintype (Fin (L + 1)) origin *
          ∑ selected : Fin (L + 1),
            trajectoryIndexComponentKernel potential gradient ε origin selected
              hpotential hgradient z s := by
  rw [randomizedMultinomialLeapfrogKernel_apply_set potential gradient ε L
    hpotential hgradient z s hs]
  apply Finset.sum_congr rfl
  intro origin horigin
  congr 1
  apply Finset.sum_congr rfl
  intro selected hselected
  rw [trajectoryIndexComponentKernel_apply potential gradient ε origin selected
    hpotential hgradient z s hs]
  by_cases hmem : offsetLeapfrogTrajectory gradient ε origin z selected ∈ s <;>
    simp [Set.indicator, hmem]

private theorem randomizedMultinomialLeapfrogKernel_flow_sum
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) (L : ℕ) {A B : Set (PhaseSpace ι)}
    (_hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫⁻ z in A, randomizedMultinomialLeapfrogKernel potential gradient ε L
        hpotential hgradient z B ∂phaseBoltzmannTarget potential =
      ∑ origin : Fin (L + 1),
        PMF.uniformOfFintype (Fin (L + 1)) origin *
          ∑ selected : Fin (L + 1),
            ∫⁻ z in A,
              trajectoryIndexComponentKernel potential gradient ε origin selected
                hpotential hgradient z B ∂phaseBoltzmannTarget potential := by
  simp_rw [randomizedMultinomialLeapfrogKernel_apply_set_eq_components
    potential gradient ε L hpotential hgradient _ B hB]
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro origin horigin
    rw [lintegral_const_mul _ (Finset.measurable_sum _ fun selected hselected =>
      (trajectoryIndexComponentKernel potential gradient ε origin selected
        hpotential hgradient).measurable_coe hB)]
    rw [lintegral_finsetSum _ fun selected hselected =>
      (trajectoryIndexComponentKernel potential gradient ε origin selected
        hpotential hgradient).measurable_coe hB]
  · intro origin horigin
    exact measurable_const.mul (Finset.measurable_sum _ fun selected hselected =>
      (trajectoryIndexComponentKernel potential gradient ε origin selected
        hpotential hgradient).measurable_coe hB)

/-- The randomized multinomial leapfrog transition satisfies detailed balance
with respect to the phase-space Boltzmann measure. -/
theorem randomizedMultinomialLeapfrogKernel_isReversible
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) (L : ℕ) :
    (randomizedMultinomialLeapfrogKernel potential gradient ε L
      hpotential hgradient).IsReversible (phaseBoltzmannTarget potential) := by
  intro A B hA hB
  rw [randomizedMultinomialLeapfrogKernel_flow_sum hpotential hgradient ε L hA hB]
  rw [randomizedMultinomialLeapfrogKernel_flow_sum hpotential hgradient ε L hB hA]
  trans ∑ origin : Fin (L + 1),
      PMF.uniformOfFintype (Fin (L + 1)) origin *
        ∑ selected : Fin (L + 1),
          ∫⁻ z in B,
            trajectoryIndexComponentKernel potential gradient ε selected origin
              hpotential hgradient z A ∂phaseBoltzmannTarget potential
  · apply Finset.sum_congr rfl
    intro origin horigin
    congr 1
    apply Finset.sum_congr rfl
    intro selected hselected
    exact trajectoryIndexComponentKernel_balance hpotential hgradient ε
      origin selected hA hB
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]

/-- The randomized multinomial leapfrog transition preserves the phase-space
Boltzmann measure. -/
theorem randomizedMultinomialLeapfrogKernel_invariant
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) (L : ℕ) :
    (randomizedMultinomialLeapfrogKernel potential gradient ε L
      hpotential hgradient).Invariant (phaseBoltzmannTarget potential) :=
  (randomizedMultinomialLeapfrogKernel_isReversible hpotential hgradient ε L).invariant

end Mcmc.Hamiltonian
