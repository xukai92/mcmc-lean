import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Probability.Distributions.Gaussian.Real
import Mcmc.Kernel.MetropolisHastings

/-!
# Random-walk Metropolis--Hastings

This module specializes the general density-based Metropolis--Hastings theorem
to additive random-walk proposals.  An increment density `noise` induces the
proposal density `q(x,y) = noise (y - x)`. Translation invariance of the
reference measure proves normalization at every current state. If `noise` is
even, the proposal density is symmetric.

The resulting RWMH kernel is proved Markov, reversible, and target-invariant.
This is the single-chain RWMH component later used in the paper's exact-meeting
mixture.
-/

open MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace Mcmc.Kernel

open ProbabilityTheory

variable {State : Type*} [AddCommGroup State] [MeasurableSpace State]
  [MeasurableSub₂ State]

/-- Transition density obtained by adding an increment with density `noise`. -/
noncomputable def randomWalkProposalDensity (noise : State → ENNReal)
    (x y : State) : ENNReal :=
  noise (y - x)

theorem measurable_uncurry_randomWalkProposalDensity
    {noise : State → ENNReal} (hnoise : Measurable noise) :
    Measurable (Function.uncurry (randomWalkProposalDensity noise)) := by
  exact hnoise.comp (measurable_sub.comp measurable_swap)

/-- Translation invariance turns normalization of the increment density into
normalization of every row of the random-walk proposal. -/
theorem randomWalkProposalDensity_lintegral
    (reference : Measure State) [Measure.IsAddRightInvariant reference]
    {noise : State → ENNReal} (hnoise : Measurable noise) (x : State) :
    ∫⁻ y, randomWalkProposalDensity noise x y ∂reference =
      ∫⁻ z, noise z ∂reference := by
  simp only [randomWalkProposalDensity]
  calc
    (∫⁻ y, noise (y - x) ∂reference) =
        ∫⁻ z, noise z ∂reference.map (fun y => y - x) := by
      exact (lintegral_map' hnoise.aemeasurable
        (Measurable.of_uncurry_right measurable_sub).aemeasurable).symm
    _ = ∫⁻ z, noise z ∂reference := by
      have hmap : reference.map (fun y => y - x) = reference := by
        calc
          reference.map (fun y => y - x) =
              reference.map (fun y => y + (-x)) := by
            congr 1
            funext y
            rw [sub_eq_add_neg]
          _ = reference := Measure.IsAddRightInvariant.map_add_right_eq_self (-x)
      rw [hmap]

/-- Translation invariance also identifies moments of the proposal increment:
an observable of `y-x` under the proposal row has the corresponding moment
under the centered noise density. -/
theorem randomWalkProposalDensity_lintegral_cost
    (reference : Measure State) [Measure.IsAddRightInvariant reference]
    {noise cost : State → ENNReal} (hnoise : Measurable noise)
    (hcost : Measurable cost) (x : State) :
    (∫⁻ y, cost (y - x) * randomWalkProposalDensity noise x y ∂reference) =
      ∫⁻ z, cost z * noise z ∂reference := by
  simp only [randomWalkProposalDensity]
  let weighted : State → ENNReal := fun z => cost z * noise z
  have hweighted : Measurable weighted := hcost.mul hnoise
  calc
    (∫⁻ y, cost (y - x) * noise (y - x) ∂reference) =
        ∫⁻ z, weighted z ∂reference.map (fun y => y - x) := by
      exact (lintegral_map' hweighted.aemeasurable
        (Measurable.of_uncurry_right measurable_sub).aemeasurable).symm
    _ = ∫⁻ z, weighted z ∂reference := by
      have hmap : reference.map (fun y => y - x) = reference := by
        calc
          reference.map (fun y => y - x) =
              reference.map (fun y => y + (-x)) := by
            congr 1
            funext y
            rw [sub_eq_add_neg]
          _ = reference := Measure.IsAddRightInvariant.map_add_right_eq_self (-x)
      rw [hmap]
    _ = ∫⁻ z, cost z * noise z ∂reference := rfl

theorem randomWalkProposalDensity_normalized
    (reference : Measure State) [Measure.IsAddRightInvariant reference]
    {noise : State → ENNReal} (hnoise : Measurable noise)
    (hnorm : ∫⁻ z, noise z ∂reference = 1) (x : State) :
    ∫⁻ y, randomWalkProposalDensity noise x y ∂reference = 1 := by
  rw [randomWalkProposalDensity_lintegral reference hnoise x, hnorm]

omit [MeasurableSpace State] [MeasurableSub₂ State] in
/-- An even increment density gives a symmetric random-walk proposal. -/
theorem randomWalkProposalDensity_swap
    (noise : State → ENNReal) (heven : ∀ z, noise (-z) = noise z)
    (x y : State) :
    randomWalkProposalDensity noise y x =
      randomWalkProposalDensity noise x y := by
  rw [randomWalkProposalDensity, randomWalkProposalDensity]
  have hxy : x - y = -(y - x) := by abel
  rw [hxy, heven]

omit [MeasurableSpace State] [MeasurableSub₂ State] in
/-- The symmetric accepted-flow formula for an even random-walk increment
density. -/
theorem randomWalk_symmetricAcceptedFlow
    (weight noise : State → ENNReal)
    (heven : ∀ z, noise (-z) = noise z) (x y : State) :
    symmetricAcceptedFlow weight (randomWalkProposalDensity noise) x y =
      min (weight x * noise (y - x)) (weight y * noise (y - x)) := by
  rw [symmetricAcceptedFlow, forwardDensityFlow, forwardDensityFlow]
  simp only [randomWalkProposalDensity]
  have hxy : x - y = -(y - x) := by abel
  rw [hxy, heven]

omit [MeasurableSpace State] [MeasurableSub₂ State] in
/-- For a positive finite even proposal density, random-walk MH acceptance is
the target-weight ratio `min (w x) (w y) / w x`; the symmetric proposal
density cancels exactly. -/
theorem randomWalk_densityAcceptance_eq_min_weight_div
    (weight noise : State → ENNReal)
    (heven : ∀ z, noise (-z) = noise z)
    (hweightPos : ∀ x, weight x ≠ 0)
    (hnoisePos : ∀ z, noise z ≠ 0)
    (hnoiseFinite : ∀ z, noise z ≠ ∞)
    (x y : State) :
    densityAcceptance weight (randomWalkProposalDensity noise) x y =
      min (weight x) (weight y) / weight x := by
  rw [densityAcceptance]
  have hflow : forwardDensityFlow weight
      (randomWalkProposalDensity noise) x y ≠ 0 := by
    rw [forwardDensityFlow, randomWalkProposalDensity]
    exact mul_ne_zero (hweightPos x) (hnoisePos (y - x))
  rw [if_neg hflow, randomWalk_symmetricAcceptedFlow weight noise heven]
  rw [← min_mul]
  exact ENNReal.mul_div_mul_right _ _
    (hnoisePos (y - x)) (hnoiseFinite (y - x))

/-- Random-walk Metropolis--Hastings with increment density `noise`. -/
noncomputable def randomWalkMetropolisHastings
    (reference : Measure State) [SFinite reference]
    [Measure.IsAddRightInvariant reference]
    (weight noise : State → ENNReal)
    (hnoise : Measurable noise)
    (hnoiseNorm : ∫⁻ z, noise z ∂reference = 1) :
    ProbabilityTheory.Kernel State State :=
  densityMetropolisHastings reference weight (randomWalkProposalDensity noise)
    (measurable_uncurry_randomWalkProposalDensity hnoise)
    (randomWalkProposalDensity_normalized reference hnoise hnoiseNorm)

/-- RWMH is a Markov kernel. -/
theorem randomWalkMetropolisHastings_isMarkov
    (reference : Measure State) [SFinite reference]
    [Measure.IsAddRightInvariant reference]
    (weight noise : State → ENNReal)
    (hweight : Measurable weight) (hnoise : Measurable noise)
    (hnoiseNorm : ∫⁻ z, noise z ∂reference = 1) :
    IsMarkovKernel
      (randomWalkMetropolisHastings reference weight noise hnoise hnoiseNorm) :=
  densityMetropolisHastings_isMarkov reference weight
    (randomWalkProposalDensity noise) hweight
    (measurable_uncurry_randomWalkProposalDensity hnoise)
    (randomWalkProposalDensity_normalized reference hnoise hnoiseNorm)

/-- A translation-controlled observable has an explicit coarse RWMH growth
bound. The target affects acceptance probabilities but not this estimate:
accepted moves are dominated by the full noise proposal and rejection retains
one additional copy of the current value. -/
theorem lintegral_randomWalkMetropolisHastings_le_two_mul_add_cost
    (reference : Measure State) [SFinite reference]
    [Measure.IsAddRightInvariant reference]
    (weight noise : State → ENNReal)
    (hweight : Measurable weight) (hnoise : Measurable noise)
    (hnoiseNorm : ∫⁻ z, noise z ∂reference = 1)
    {f cost : State → ENNReal} (hf : Measurable f)
    (hcost : Measurable cost)
    (htranslate : ∀ x y, f y ≤ f x + cost (y - x)) (x : State) :
    (∫⁻ y, f y ∂randomWalkMetropolisHastings reference weight noise
        hnoise hnoiseNorm x) ≤
      2 * f x + ∫⁻ z, cost z * noise z ∂reference := by
  have hmh := lintegral_densityMetropolisHastings_le_proposal_add
    reference weight (randomWalkProposalDensity noise) hweight
    (measurable_uncurry_randomWalkProposalDensity hnoise)
    (randomWalkProposalDensity_normalized reference hnoise hnoiseNorm) hf x
  have hproposal :
      (∫⁻ y, randomWalkProposalDensity noise x y * f y ∂reference) ≤
        f x + ∫⁻ z, cost z * noise z ∂reference := by
    calc
      (∫⁻ y, randomWalkProposalDensity noise x y * f y ∂reference) ≤
          ∫⁻ y, randomWalkProposalDensity noise x y *
            (f x + cost (y - x)) ∂reference := by
        apply lintegral_mono
        intro y
        exact mul_le_mul_right (htranslate x y) _
      _ = (∫⁻ y, f x * randomWalkProposalDensity noise x y ∂reference) +
          ∫⁻ y, cost (y - x) * randomWalkProposalDensity noise x y
            ∂reference := by
        rw [show (fun y => randomWalkProposalDensity noise x y *
              (f x + cost (y - x))) =
            fun y => f x * randomWalkProposalDensity noise x y +
              cost (y - x) * randomWalkProposalDensity noise x y by
          funext y
          ring]
        exact lintegral_add_left
          (measurable_const.mul
            (Measurable.of_uncurry_left
              (measurable_uncurry_randomWalkProposalDensity hnoise))) _
      _ = f x + ∫⁻ z, cost z * noise z ∂reference := by
        rw [lintegral_const_mul _
          (Measurable.of_uncurry_left
            (measurable_uncurry_randomWalkProposalDensity hnoise)),
          randomWalkProposalDensity_lintegral reference hnoise x, hnoiseNorm,
          mul_one,
          randomWalkProposalDensity_lintegral_cost reference hnoise hcost x]
  calc
    (∫⁻ y, f y ∂randomWalkMetropolisHastings reference weight noise
        hnoise hnoiseNorm x) ≤
        (∫⁻ y, randomWalkProposalDensity noise x y * f y ∂reference) + f x := by
      simpa only [randomWalkMetropolisHastings] using hmh
    _ ≤ (f x + ∫⁻ z, cost z * noise z ∂reference) + f x :=
      add_le_add hproposal le_rfl
    _ = 2 * f x + ∫⁻ z, cost z * noise z ∂reference := by ring

/-- RWMH satisfies detailed balance with respect to the target density. -/
theorem randomWalkMetropolisHastings_isReversible
    (reference : Measure State) [SFinite reference]
    [Measure.IsAddRightInvariant reference]
    (weight noise : State → ENNReal)
    (hweight : Measurable weight) (hnoise : Measurable noise)
    (hnoiseNorm : ∫⁻ z, noise z ∂reference = 1)
    (hfinite : ∀ x y,
      forwardDensityFlow weight (randomWalkProposalDensity noise) x y ≠ ∞) :
    (randomWalkMetropolisHastings reference weight noise hnoise
      hnoiseNorm).IsReversible (densityTarget reference weight) :=
  densityMetropolisHastings_isReversible reference weight
    (randomWalkProposalDensity noise) hweight
    (measurable_uncurry_randomWalkProposalDensity hnoise)
    (randomWalkProposalDensity_normalized reference hnoise hnoiseNorm) hfinite

/-- RWMH preserves the target measure. -/
theorem randomWalkMetropolisHastings_invariant
    (reference : Measure State) [SFinite reference]
    [Measure.IsAddRightInvariant reference]
    (weight noise : State → ENNReal)
    (hweight : Measurable weight) (hnoise : Measurable noise)
    (hnoiseNorm : ∫⁻ z, noise z ∂reference = 1)
    (hfinite : ∀ x y,
      forwardDensityFlow weight (randomWalkProposalDensity noise) x y ≠ ∞) :
    (randomWalkMetropolisHastings reference weight noise hnoise
      hnoiseNorm).Invariant (densityTarget reference weight) :=
  densityMetropolisHastings_invariant reference weight
    (randomWalkProposalDensity noise) hweight
    (measurable_uncurry_randomWalkProposalDensity hnoise)
    (randomWalkProposalDensity_normalized reference hnoise hnoiseNorm) hfinite

section GaussianReal

/-- The centered real Gaussian density is even. -/
theorem gaussianPDF_zero_even (variance : ℝ≥0) (z : ℝ) :
    ProbabilityTheory.gaussianPDF 0 variance (-z) =
      ProbabilityTheory.gaussianPDF 0 variance z := by
  simp [ProbabilityTheory.gaussianPDF, ProbabilityTheory.gaussianPDFReal]

/-- One-dimensional RWMH with centered Gaussian increments of nonzero
variance. -/
noncomputable def gaussianRandomWalkMetropolisHastings
    (weight : ℝ → ENNReal) (variance : ℝ≥0) (hvariance : variance ≠ 0) :
    ProbabilityTheory.Kernel ℝ ℝ :=
  randomWalkMetropolisHastings volume weight
    (ProbabilityTheory.gaussianPDF 0 variance)
    (ProbabilityTheory.measurable_gaussianPDF 0 variance)
    (ProbabilityTheory.lintegral_gaussianPDF_eq_one 0 hvariance)

/-- Gaussian RWMH is a Markov kernel. -/
theorem gaussianRandomWalkMetropolisHastings_isMarkov
    (weight : ℝ → ENNReal) (variance : ℝ≥0) (hvariance : variance ≠ 0)
    (hweight : Measurable weight) :
    IsMarkovKernel
      (gaussianRandomWalkMetropolisHastings weight variance hvariance) :=
  randomWalkMetropolisHastings_isMarkov volume weight
    (ProbabilityTheory.gaussianPDF 0 variance) hweight
    (ProbabilityTheory.measurable_gaussianPDF 0 variance)
    (ProbabilityTheory.lintegral_gaussianPDF_eq_one 0 hvariance)

/-- Gaussian RWMH satisfies detailed balance for every measurable finite
target density. -/
theorem gaussianRandomWalkMetropolisHastings_isReversible
    (weight : ℝ → ENNReal) (variance : ℝ≥0) (hvariance : variance ≠ 0)
    (hweight : Measurable weight) (hweightFinite : ∀ x, weight x ≠ ∞) :
    (gaussianRandomWalkMetropolisHastings weight variance hvariance).IsReversible
      (densityTarget volume weight) := by
  apply randomWalkMetropolisHastings_isReversible volume weight
    (ProbabilityTheory.gaussianPDF 0 variance) hweight
    (ProbabilityTheory.measurable_gaussianPDF 0 variance)
    (ProbabilityTheory.lintegral_gaussianPDF_eq_one 0 hvariance)
  intro x y
  exact ENNReal.mul_ne_top (hweightFinite x)
    ProbabilityTheory.gaussianPDF_ne_top

/-- Gaussian RWMH preserves its target measure. -/
theorem gaussianRandomWalkMetropolisHastings_invariant
    (weight : ℝ → ENNReal) (variance : ℝ≥0) (hvariance : variance ≠ 0)
    (hweight : Measurable weight) (hweightFinite : ∀ x, weight x ≠ ∞) :
    (gaussianRandomWalkMetropolisHastings weight variance hvariance).Invariant
      (densityTarget volume weight) := by
  apply randomWalkMetropolisHastings_invariant volume weight
    (ProbabilityTheory.gaussianPDF 0 variance) hweight
    (ProbabilityTheory.measurable_gaussianPDF 0 variance)
    (ProbabilityTheory.lintegral_gaussianPDF_eq_one 0 hvariance)
  intro x y
  exact ENNReal.mul_ne_top (hweightFinite x)
    ProbabilityTheory.gaussianPDF_ne_top

end GaussianReal

end Mcmc.Kernel
