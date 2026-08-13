import McmcLean.Hamiltonian.Multinomial
import McmcLean.Hamiltonian.RandomizedTrajectory
import Mathlib.Probability.Distributions.Uniform

/-!
# Randomized multinomial leapfrog transition

This module combines uniform selection of a trajectory origin with the
forward/backward leapfrog trajectory and Boltzmann-weighted index selection.
It is the phase-space trajectory transition used by multinomial HMC, before
composition with Gaussian momentum refresh.

The construction is a measurable Markov kernel. Its finite-sum row formula is
exposed for the later balance proof, whose remaining analytic input is
volume preservation of leapfrog.
-/

open MeasureTheory
open scoped BigOperators ENNReal ProbabilityTheory

namespace McmcLean.Hamiltonian

open ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- Joint law of the uniformly chosen trajectory origin and the subsequently
Boltzmann-selected trajectory index. -/
noncomputable def originSelectedIndexPMF
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (z : PhaseSpace ι) :
    PMF (Fin (L + 1) × Fin (L + 1)) :=
  (PMF.uniformOfFintype (Fin (L + 1))).bind fun origin =>
    (trajectoryIndexPMF potential
      (offsetLeapfrogTrajectory gradient ε origin z)).map fun selected =>
        (origin, selected)

/-- Output law of the finite probabilistic program: choose an origin, choose a
Boltzmann index on its trajectory, and return the corresponding phase point. -/
noncomputable def randomizedMultinomialLeapfrogPMF
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (z : PhaseSpace ι) : PMF (PhaseSpace ι) :=
  (PMF.uniformOfFintype (Fin (L + 1))).bind fun origin =>
    (trajectoryIndexPMF potential
      (offsetLeapfrogTrajectory gradient ε origin z)).map
        (offsetLeapfrogTrajectory gradient ε origin z)

/-- Conditional multinomial selection for one fixed trajectory origin. -/
noncomputable def offsetMultinomialKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (origin : Fin (L + 1))
    (hpotential : Measurable potential) (hgradient : Measurable gradient) :
    Kernel (PhaseSpace ι) (PhaseSpace ι) :=
  trajectorySelectionKernel potential
    (offsetLeapfrogTrajectory gradient ε origin) hpotential
    (measurable_offsetLeapfrogTrajectory hgradient ε origin)

instance offsetMultinomialKernel_isMarkovKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (origin : Fin (L + 1))
    (hpotential : Measurable potential) (hgradient : Measurable gradient) :
    IsMarkovKernel
      (offsetMultinomialKernel potential gradient ε L origin
        hpotential hgradient) :=
  trajectorySelectionKernel_isMarkovKernel potential
    (offsetLeapfrogTrajectory gradient ε origin) hpotential
    (measurable_offsetLeapfrogTrajectory hgradient ε origin)

/-- Average the fixed-origin multinomial transitions over a uniform origin. -/
noncomputable def randomizedMultinomialLeapfrogKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    Kernel (PhaseSpace ι) (PhaseSpace ι) where
  toFun z := ∑ origin : Fin (L + 1),
    (PMF.uniformOfFintype (Fin (L + 1)) origin) •
      offsetMultinomialKernel potential gradient ε L origin
        hpotential hgradient z
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    apply Finset.measurable_sum
    intro origin horigin
    exact measurable_const.mul
      ((offsetMultinomialKernel potential gradient ε L origin
        hpotential hgradient).measurable_coe hs)

instance randomizedMultinomialLeapfrogKernel_isMarkovKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    IsMarkovKernel
      (randomizedMultinomialLeapfrogKernel potential gradient ε L
        hpotential hgradient) where
  isProbabilityMeasure z := by
    constructor
    rw [randomizedMultinomialLeapfrogKernel]
    change (∑ origin : Fin (L + 1),
      (PMF.uniformOfFintype (Fin (L + 1)) origin) •
        offsetMultinomialKernel potential gradient ε L origin
          hpotential hgradient z) Set.univ = 1
    rw [Measure.finsetSum_apply]
    simp only [Measure.smul_apply, smul_eq_mul]
    change (∑ origin : Fin (L + 1),
      PMF.uniformOfFintype (Fin (L + 1)) origin *
        offsetMultinomialKernel potential gradient ε L origin
          hpotential hgradient z Set.univ) = 1
    simp only [measure_univ, mul_one]
    exact (tsum_fintype _).symm.trans (PMF.tsum_coe _)

@[simp]
theorem randomizedMultinomialLeapfrogKernel_apply
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) (z : PhaseSpace ι) :
    randomizedMultinomialLeapfrogKernel potential gradient ε L
        hpotential hgradient z =
      ∑ origin : Fin (L + 1),
        (PMF.uniformOfFintype (Fin (L + 1)) origin) •
          offsetMultinomialKernel potential gradient ε L origin
            hpotential hgradient z :=
  rfl

/-- Explicit two-stage finite-sum law: first average uniformly over origins,
then sum the Boltzmann selection probabilities of points in the event. -/
theorem randomizedMultinomialLeapfrogKernel_apply_set
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) (z : PhaseSpace ι)
    (s : Set (PhaseSpace ι)) (hs : MeasurableSet s) :
    randomizedMultinomialLeapfrogKernel potential gradient ε L
        hpotential hgradient z s =
      ∑ origin : Fin (L + 1),
        PMF.uniformOfFintype (Fin (L + 1)) origin *
          ∑ selected : Fin (L + 1),
            (offsetLeapfrogTrajectory gradient ε origin z ⁻¹' s).indicator
              (trajectoryIndexPMF potential
                (offsetLeapfrogTrajectory gradient ε origin z)) selected := by
  simp only [randomizedMultinomialLeapfrogKernel_apply,
    Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro origin horigin
  unfold offsetMultinomialKernel
  rw [trajectorySelectionKernel_apply potential
    (offsetLeapfrogTrajectory gradient ε origin) hpotential
    (measurable_offsetLeapfrogTrajectory hgradient ε origin) z s hs]

/-- The measure-kernel row agrees exactly with the finite PMF sampling
program. -/
theorem randomizedMultinomialLeapfrogKernel_apply_eq_toMeasure
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) (z : PhaseSpace ι) :
    randomizedMultinomialLeapfrogKernel potential gradient ε L
        hpotential hgradient z =
      (randomizedMultinomialLeapfrogPMF potential gradient ε L z).toMeasure := by
  ext s hs
  rw [randomizedMultinomialLeapfrogKernel_apply]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  rw [randomizedMultinomialLeapfrogPMF, PMF.toMeasure_bind_apply _ _ _ hs,
    tsum_fintype]
  apply Finset.sum_congr rfl
  intro origin horigin
  congr 1
  unfold offsetMultinomialKernel trajectorySelectionKernel
  change ((trajectoryIndexPMF potential
    (offsetLeapfrogTrajectory gradient ε origin z)).toMeasure.map
      (offsetLeapfrogTrajectory gradient ε origin z)) s = _
  rw [PMF.toMeasure_map _ _ (measurable_of_countable _)]

/-- Exact finite-sum expectation for one fixed randomized-trajectory origin. -/
theorem lintegral_offsetMultinomialKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (origin : Fin (L + 1))
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (f : PhaseSpace ι → ENNReal) (hf : Measurable f) (z : PhaseSpace ι) :
    (∫⁻ w, f w ∂offsetMultinomialKernel potential gradient ε L origin
      hpotential hgradient z) =
      ∑ selected, trajectoryIndexPMF potential
          (offsetLeapfrogTrajectory gradient ε origin z) selected *
        f (offsetLeapfrogTrajectory gradient ε origin z selected) := by
  unfold offsetMultinomialKernel
  exact lintegral_trajectorySelectionKernel potential
    (offsetLeapfrogTrajectory gradient ε origin) hpotential
    (measurable_offsetLeapfrogTrajectory hgradient ε origin) f hf z

/-- Exact origin-and-index finite-sum expectation for the implemented
randomized multinomial leapfrog kernel. -/
theorem lintegral_randomizedMultinomialLeapfrogKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient)
    (f : PhaseSpace ι → ENNReal) (hf : Measurable f) (z : PhaseSpace ι) :
    (∫⁻ w, f w ∂randomizedMultinomialLeapfrogKernel potential gradient ε L
      hpotential hgradient z) =
      ∑ origin : Fin (L + 1),
        PMF.uniformOfFintype (Fin (L + 1)) origin *
          ∑ selected : Fin (L + 1),
            trajectoryIndexPMF potential
                (offsetLeapfrogTrajectory gradient ε origin z) selected *
              f (offsetLeapfrogTrajectory gradient ε origin z selected) := by
  rw [randomizedMultinomialLeapfrogKernel_apply,
    lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro origin _horigin
  rw [lintegral_smul_measure,
    lintegral_offsetMultinomialKernel potential gradient ε L origin
      hpotential hgradient f hf z]
  rfl

/-- Re-rooting leaves the full Boltzmann normalizer unchanged because it
leaves every indexed trajectory point unchanged. -/
theorem trajectoryNormalizer_offset_reroot
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (origin selected : Fin (L + 1))
    (z : PhaseSpace ι) :
    trajectoryNormalizer potential
        (offsetLeapfrogTrajectory gradient ε selected
          (offsetLeapfrogTrajectory gradient ε origin z selected)) =
      trajectoryNormalizer potential
        (offsetLeapfrogTrajectory gradient ε origin z) := by
  unfold trajectoryNormalizer
  apply Finset.sum_congr rfl
  intro i hi
  rw [offsetLeapfrogTrajectory_reroot]

/-- The weighted probability flow associated with an ordered pair of
trajectory indices is symmetric after re-rooting at the selected point. -/
theorem boltzmann_trajectoryIndexPMF_flow_reroot
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (origin selected : Fin (L + 1))
    (z : PhaseSpace ι) :
    boltzmannWeight potential z *
        trajectoryIndexPMF potential
          (offsetLeapfrogTrajectory gradient ε origin z) selected =
      boltzmannWeight potential
          (offsetLeapfrogTrajectory gradient ε origin z selected) *
        trajectoryIndexPMF potential
          (offsetLeapfrogTrajectory gradient ε selected
            (offsetLeapfrogTrajectory gradient ε origin z selected)) origin := by
  rw [trajectoryIndexPMF_apply, trajectoryIndexPMF_apply]
  rw [trajectoryNormalizer_offset_reroot]
  rw [offsetLeapfrogTrajectory_reroot]
  rw [offsetLeapfrogTrajectory_origin]
  ac_rfl

end McmcLean.Hamiltonian
