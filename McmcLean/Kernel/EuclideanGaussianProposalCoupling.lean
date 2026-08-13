import McmcLean.Kernel.ParameterizedDensityCoupling
import McmcLean.Kernel.GaussianRandomWalk
import McmcLean.Kernel.CoupledMetropolisHastings
import McmcLean.Kernel.MeetingDrift

/-!
# Finite-dimensional exact-meeting Gaussian RWMH couplings

This module instantiates the measurable parameterized maximal-density
coupling with isotropic Gaussian random-walk proposals on `ι → ℝ`.  The
resulting shared-uniform coupled RWMH transition has the verified
finite-dimensional Gaussian RWMH kernel on both marginals and positive
one-step exact-meeting probability from every state pair when the target
density is everywhere positive and finite.
-/

open MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace McmcLean.Kernel

open ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- Jointly measurable finite-dimensional Gaussian random-walk proposal
density. -/
theorem measurable_uncurry_euclideanGaussianProposalDensity
    (variance : ℝ≥0) :
    Measurable (Function.uncurry
      (randomWalkProposalDensity
        (isotropicGaussianPDF (ι := ι) variance))) :=
  measurable_uncurry_randomWalkProposalDensity
    (measurable_isotropicGaussianPDF variance)

/-- The finite-dimensional Gaussian random-walk proposal density is jointly
continuous in its current and proposed positions. -/
theorem continuous_uncurry_euclideanGaussianProposalDensity
    (variance : ℝ≥0) :
    Continuous (Function.uncurry
      (randomWalkProposalDensity
        (isotropicGaussianPDF (ι := ι) variance))) := by
  exact (continuous_isotropicGaussianPDF variance).comp
    (continuous_snd.sub continuous_fst)

/-- Measurable maximal coupling of finite-dimensional isotropic Gaussian
proposal rows. -/
noncomputable def euclideanMaximalGaussianProposalKernel
    (variance : ℝ≥0) :
    Kernel ((ι → ℝ) × (ι → ℝ)) ((ι → ℝ) × (ι → ℝ)) :=
  parameterizedMaximalCouplingKernel volume
    (randomWalkProposalDensity (isotropicGaussianPDF variance))
    (measurable_uncurry_euclideanGaussianProposalDensity variance)
    (fun x z => isotropicGaussianPDF_ne_top variance (z - x))

theorem euclideanGaussianProposalDensity_normalized
    (variance : ℝ≥0) (hvariance : variance ≠ 0) (x : ι → ℝ) :
    ∫⁻ z, randomWalkProposalDensity (isotropicGaussianPDF variance) x z = 1 :=
  randomWalkProposalDensity_normalized volume
    (measurable_isotropicGaussianPDF variance)
    (lintegral_isotropicGaussianPDF_eq_one variance hvariance) x

/-- The finite-dimensional maximal Gaussian proposal construction is a
Markov kernel. -/
theorem euclideanMaximalGaussianProposalKernel_isMarkov
    (variance : ℝ≥0) (hvariance : variance ≠ 0) :
    IsMarkovKernel
      (euclideanMaximalGaussianProposalKernel (ι := ι) variance) := by
  apply parameterizedMaximalCouplingKernel_isMarkov volume
    (randomWalkProposalDensity (isotropicGaussianPDF variance))
    (measurable_uncurry_euclideanGaussianProposalDensity variance)
    (fun x z => isotropicGaussianPDF_ne_top variance (z - x))
  exact euclideanGaussianProposalDensity_normalized variance hvariance

/-- The finite-dimensional maximal proposal kernel has exactly the two
Gaussian proposal rows as marginals. -/
theorem euclideanMaximalGaussianProposalKernel_isCoupling
    (variance : ℝ≥0) (hvariance : variance ≠ 0) :
    IsCoupling (euclideanMaximalGaussianProposalKernel (ι := ι) variance)
      (densityProposal volume
        (randomWalkProposalDensity (isotropicGaussianPDF variance)))
      (densityProposal volume
        (randomWalkProposalDensity (isotropicGaussianPDF variance))) := by
  apply parameterizedMaximalCouplingKernel_isCoupling volume
    (randomWalkProposalDensity (isotropicGaussianPDF variance))
    (measurable_uncurry_euclideanGaussianProposalDensity variance)
    (fun x z => isotropicGaussianPDF_ne_top variance (z - x))
  exact euclideanGaussianProposalDensity_normalized variance hvariance

/-- Every two finite-dimensional nondegenerate Gaussian proposal rows have
positive exact-agreement probability under their maximal coupling. -/
theorem euclideanMaximalGaussianProposalKernel_diagonal_pos
    (variance : ℝ≥0) (hvariance : variance ≠ 0)
    (current : (ι → ℝ) × (ι → ℝ)) :
    0 < euclideanMaximalGaussianProposalKernel variance current
      (Set.diagonal (ι → ℝ)) := by
  apply parameterizedMaximalCouplingKernel_diagonal_pos volume
    (randomWalkProposalDensity (isotropicGaussianPDF variance))
    (measurable_uncurry_euclideanGaussianProposalDensity variance)
    (fun x z => isotropicGaussianPDF_ne_top variance (z - x))
    (euclideanGaussianProposalDensity_normalized variance hvariance)
  · rw [Measure.measure_univ_pos]
    intro hzero
    have hnorm := lintegral_isotropicGaussianPDF_eq_one
      (ι := ι) variance hvariance
    rw [hzero] at hnorm
    simp at hnorm
  · intro x z
    exact isotropicGaussianPDF_pos variance hvariance (z - x)

/-- Coupled finite-dimensional Gaussian RWMH using maximal proposal coupling
and a shared accept/reject uniform. -/
noncomputable def coupledEuclideanGaussianRandomWalkMetropolisHastings
    (weight : (ι → ℝ) → ENNReal) (variance : ℝ≥0)
    (hvariance : variance ≠ 0) :
    Kernel ((ι → ℝ) × (ι → ℝ)) ((ι → ℝ) × (ι → ℝ)) := by
  letI := euclideanMaximalGaussianProposalKernel_isMarkov
    (ι := ι) variance hvariance
  exact coupledAcceptRejectKernel
    (euclideanMaximalGaussianProposalKernel variance)
    (densityAcceptance weight
      (randomWalkProposalDensity (isotropicGaussianPDF variance)))
    (densityAcceptance_le_one weight
      (randomWalkProposalDensity (isotropicGaussianPDF variance)))

theorem coupledEuclideanGaussianRandomWalkMetropolisHastings_isMarkov
    (weight : (ι → ℝ) → ENNReal) (variance : ℝ≥0)
    (hvariance : variance ≠ 0) (hweight : Measurable weight) :
    IsMarkovKernel
      (coupledEuclideanGaussianRandomWalkMetropolisHastings
        weight variance hvariance) := by
  letI := euclideanMaximalGaussianProposalKernel_isMarkov
    (ι := ι) variance hvariance
  rw [coupledEuclideanGaussianRandomWalkMetropolisHastings]
  apply coupledAcceptRejectKernel_isMarkov
  exact measurable_uncurry_densityAcceptance hweight
    (measurable_uncurry_euclideanGaussianProposalDensity variance)

/-- Both marginals of coupled finite-dimensional Gaussian RWMH are exactly
the existing verified single-chain kernel. -/
theorem coupledEuclideanGaussianRandomWalkMetropolisHastings_isCoupling
    (weight : (ι → ℝ) → ENNReal) (variance : ℝ≥0)
    (hvariance : variance ≠ 0) (hweight : Measurable weight) :
    IsCoupling
      (coupledEuclideanGaussianRandomWalkMetropolisHastings
        weight variance hvariance)
      (euclideanGaussianRandomWalkMetropolisHastings
        weight variance hvariance)
      (euclideanGaussianRandomWalkMetropolisHastings
        weight variance hvariance) := by
  let density := randomWalkProposalDensity
    (isotropicGaussianPDF (ι := ι) variance)
  let Q := densityProposal volume density
  let accept := densityAcceptance weight density
  letI : IsMarkovKernel Q := densityProposal_isMarkov volume
    (measurable_uncurry_euclideanGaussianProposalDensity variance)
    (euclideanGaussianProposalDensity_normalized variance hvariance)
  letI := euclideanMaximalGaussianProposalKernel_isMarkov
    (ι := ι) variance hvariance
  have hcoupling := coupledAcceptRejectKernel_isCoupling Q
    (euclideanMaximalGaussianProposalKernel variance)
    (euclideanMaximalGaussianProposalKernel_isCoupling variance hvariance)
    (measurable_uncurry_densityAcceptance hweight
      (measurable_uncurry_euclideanGaussianProposalDensity variance))
    (densityAcceptance_le_one weight density)
  simpa only [coupledEuclideanGaussianRandomWalkMetropolisHastings,
    euclideanGaussianRandomWalkMetropolisHastings,
    randomWalkMetropolisHastings, densityMetropolisHastings, density, Q,
    accept] using hcoupling

theorem euclideanGaussianDensityAcceptance_pos
    (weight : (ι → ℝ) → ENNReal) (variance : ℝ≥0)
    (hvariance : variance ≠ 0) (hweightPos : ∀ x, 0 < weight x)
    (hweightFinite : ∀ x, weight x ≠ ∞) (x z : ι → ℝ) :
    0 < densityAcceptance weight
      (randomWalkProposalDensity (isotropicGaussianPDF variance)) x z := by
  have hforward : 0 < forwardDensityFlow weight
      (randomWalkProposalDensity (isotropicGaussianPDF variance)) x z :=
    ENNReal.mul_pos (hweightPos x).ne'
      (isotropicGaussianPDF_pos variance hvariance (z - x)).ne'
  have hreverse : 0 < forwardDensityFlow weight
      (randomWalkProposalDensity (isotropicGaussianPDF variance)) z x :=
    ENNReal.mul_pos (hweightPos z).ne'
      (isotropicGaussianPDF_pos variance hvariance (x - z)).ne'
  rw [densityAcceptance]
  split_ifs with hzero
  · exact (hforward.ne' hzero).elim
  · apply ENNReal.div_pos
    · exact (lt_min hforward hreverse).ne'
    · exact ENNReal.mul_ne_top (hweightFinite x)
        (isotropicGaussianPDF_ne_top variance (z - x))

/-- Coupled finite-dimensional Gaussian RWMH has positive one-step exact
meeting probability for an everywhere positive finite target density. -/
theorem coupledEuclideanGaussianRandomWalkMetropolisHastings_meeting_pos
    (weight : (ι → ℝ) → ENNReal) (variance : ℝ≥0)
    (hvariance : variance ≠ 0) (hweight : Measurable weight)
    (hweightPos : ∀ x, 0 < weight x)
    (hweightFinite : ∀ x, weight x ≠ ∞)
    (current : (ι → ℝ) × (ι → ℝ)) :
    0 < coupledEuclideanGaussianRandomWalkMetropolisHastings
      weight variance hvariance current (Set.diagonal (ι → ℝ)) := by
  letI := euclideanMaximalGaussianProposalKernel_isMarkov
    (ι := ι) variance hvariance
  rw [coupledEuclideanGaussianRandomWalkMetropolisHastings]
  apply coupledAcceptRejectKernel_meeting_pos
  · exact measurable_uncurry_densityAcceptance hweight
      (measurable_uncurry_euclideanGaussianProposalDensity variance)
  · exact euclideanMaximalGaussianProposalKernel_diagonal_pos
      variance hvariance current
  · intro z _hz
    exact lt_min
      (euclideanGaussianDensityAcceptance_pos weight variance hvariance
        hweightPos hweightFinite current.1 z.1)
      (euclideanGaussianDensityAcceptance_pos weight variance hvariance
        hweightPos hweightFinite current.2 z.2)

/-- A common Gaussian-density floor on a measurable proposal region gives a
uniform exact-proposal-meeting constant over any paired current-state set. -/
theorem euclideanMaximalGaussianProposalKernel_isExactMeetingSmallSet_of_densityFloor
    (variance : ℝ≥0) (hvariance : variance ≠ 0)
    (C : Set ((ι → ℝ) × (ι → ℝ))) (A : Set (ι → ℝ))
    (hA : MeasurableSet A) (proposalFloor : ENNReal)
    (hleft : ∀ current ∈ C, ∀ z ∈ A,
      proposalFloor ≤ isotropicGaussianPDF variance (z - current.1))
    (hright : ∀ current ∈ C, ∀ z ∈ A,
      proposalFloor ≤ isotropicGaussianPDF variance (z - current.2)) :
    IsExactMeetingSmallSet
      (euclideanMaximalGaussianProposalKernel variance) C
      (proposalFloor * volume A) := by
  intro current hcurrent
  apply densityFloor_mul_measure_le_parameterizedMaximalCouplingKernel_diagonal
    volume (randomWalkProposalDensity (isotropicGaussianPDF variance))
    (measurable_uncurry_euclideanGaussianProposalDensity variance)
    (fun x z => isotropicGaussianPDF_ne_top variance (z - x))
    (euclideanGaussianProposalDensity_normalized variance hvariance)
    current hA proposalFloor
  · exact hleft current hcurrent
  · exact hright current hcurrent

/-- On nonempty compact current-pair and proposal regions, nondegenerate
Gaussian proposal rows have one strictly positive common density floor. -/
theorem exists_pos_euclideanGaussianProposalDensityFloor_on_compact
    (variance : ℝ≥0) (hvariance : variance ≠ 0)
    {C : Set ((ι → ℝ) × (ι → ℝ))} {A : Set (ι → ℝ)}
    (hC : IsCompact C) (hCne : C.Nonempty)
    (hA : IsCompact A) (hAne : A.Nonempty) :
    ∃ proposalFloor : ENNReal, 0 < proposalFloor ∧
      (∀ current ∈ C, ∀ z ∈ A,
        proposalFloor ≤ isotropicGaussianPDF variance (z - current.1)) ∧
      (∀ current ∈ C, ∀ z ∈ A,
        proposalFloor ≤ isotropicGaussianPDF variance (z - current.2)) := by
  let common : (((ι → ℝ) × (ι → ℝ)) × (ι → ℝ)) → ENNReal :=
    fun p => min
      (isotropicGaussianPDF variance (p.2 - p.1.1))
      (isotropicGaussianPDF variance (p.2 - p.1.2))
  have hcommon : Continuous common := by
    apply Continuous.min
    · exact (continuous_isotropicGaussianPDF variance).comp
        (continuous_snd.sub (continuous_fst.fst))
    · exact (continuous_isotropicGaussianPDF variance).comp
        (continuous_snd.sub (continuous_fst.snd))
  have hpositive : ∀ p ∈ C ×ˢ A, 0 < common p := by
    intro p hp
    exact lt_min
      (isotropicGaussianPDF_pos variance hvariance (p.2 - p.1.1))
      (isotropicGaussianPDF_pos variance hvariance (p.2 - p.1.2))
  obtain ⟨proposalFloor, hfloorPos, hfloor⟩ :=
    exists_pos_le_on_compact (hC.prod hA) (hCne.prod hAne)
      hcommon hpositive
  refine ⟨proposalFloor, hfloorPos, ?_, ?_⟩
  · intro current hcurrent z hz
    exact (hfloor (current, z) ⟨hcurrent, hz⟩).trans (min_le_left _ _)
  · intro current hcurrent z hz
    exact (hfloor (current, z) ⟨hcurrent, hz⟩).trans (min_le_right _ _)

/-- Explicit quantitative reduction for a finite-dimensional Gaussian RWMH
small set. A proposal-density floor on `A` and a simultaneous-acceptance floor
combine into the stated exact-meeting constant. -/
theorem coupledEuclideanGaussianRandomWalkMetropolisHastings_isExactMeetingSmallSet_of_floors
    (weight : (ι → ℝ) → ENNReal) (variance : ℝ≥0)
    (hvariance : variance ≠ 0) (hweight : Measurable weight)
    (C : Set ((ι → ℝ) × (ι → ℝ))) (A : Set (ι → ℝ))
    (hA : MeasurableSet A) (proposalFloor acceptanceFloor : ENNReal)
    (hleft : ∀ current ∈ C, ∀ z ∈ A,
      proposalFloor ≤ isotropicGaussianPDF variance (z - current.1))
    (hright : ∀ current ∈ C, ∀ z ∈ A,
      proposalFloor ≤ isotropicGaussianPDF variance (z - current.2))
    (haccept : ∀ current ∈ C, ∀ z ∈ Set.diagonal (ι → ℝ),
      acceptanceFloor ≤ coupledBothAcceptWeight
        (densityAcceptance weight
          (randomWalkProposalDensity (isotropicGaussianPDF variance)))
        current z) :
    IsExactMeetingSmallSet
      (coupledEuclideanGaussianRandomWalkMetropolisHastings
        weight variance hvariance)
      C (acceptanceFloor * (proposalFloor * volume A)) := by
  letI := euclideanMaximalGaussianProposalKernel_isMarkov
    (ι := ι) variance hvariance
  rw [coupledEuclideanGaussianRandomWalkMetropolisHastings]
  apply coupledAcceptRejectKernel_isExactMeetingSmallSet
    (euclideanMaximalGaussianProposalKernel variance)
    (measurable_uncurry_densityAcceptance hweight
      (measurable_uncurry_euclideanGaussianProposalDensity variance))
    (densityAcceptance_le_one weight
      (randomWalkProposalDensity (isotropicGaussianPDF variance)))
    C (proposalFloor * volume A) acceptanceFloor
  · exact euclideanMaximalGaussianProposalKernel_isExactMeetingSmallSet_of_densityFloor
      variance hvariance C A hA proposalFloor hleft hright
  · exact haccept

/-- Localized compact-ready RWMH reduction: acceptance is required only on
the restricted diagonal over the same proposal region `A` used for the
Gaussian density floor. -/
theorem coupledEuclideanGaussianRandomWalkMetropolisHastings_isExactMeetingSmallSet_of_localFloors
    (weight : (ι → ℝ) → ENNReal) (variance : ℝ≥0)
    (hvariance : variance ≠ 0) (hweight : Measurable weight)
    (C : Set ((ι → ℝ) × (ι → ℝ))) (A : Set (ι → ℝ))
    (hA : MeasurableSet A) (proposalFloor acceptanceFloor : ENNReal)
    (hleft : ∀ current ∈ C, ∀ z ∈ A,
      proposalFloor ≤ isotropicGaussianPDF variance (z - current.1))
    (hright : ∀ current ∈ C, ∀ z ∈ A,
      proposalFloor ≤ isotropicGaussianPDF variance (z - current.2))
    (haccept : ∀ current ∈ C, ∀ z ∈ diagonalOver A,
      acceptanceFloor ≤ coupledBothAcceptWeight
        (densityAcceptance weight
          (randomWalkProposalDensity (isotropicGaussianPDF variance)))
        current z) :
    IsExactMeetingSmallSet
      (coupledEuclideanGaussianRandomWalkMetropolisHastings
        weight variance hvariance)
      C (acceptanceFloor * (proposalFloor * volume A)) := by
  letI := euclideanMaximalGaussianProposalKernel_isMarkov
    (ι := ι) variance hvariance
  rw [coupledEuclideanGaussianRandomWalkMetropolisHastings]
  apply coupledAcceptRejectKernel_isExactMeetingSmallSet_of_diagonalOver
    (euclideanMaximalGaussianProposalKernel variance)
    (measurable_uncurry_densityAcceptance hweight
      (measurable_uncurry_euclideanGaussianProposalDensity variance))
    (densityAcceptance_le_one weight
      (randomWalkProposalDensity (isotropicGaussianPDF variance)))
    C hA (proposalFloor * volume A) acceptanceFloor
  · intro current hcurrent
    apply densityFloor_mul_measure_le_parameterizedMaximalCouplingKernel_diagonalOver
      volume (randomWalkProposalDensity (isotropicGaussianPDF variance))
      (measurable_uncurry_euclideanGaussianProposalDensity variance)
      (fun x z => isotropicGaussianPDF_ne_top variance (z - x))
      (euclideanGaussianProposalDensity_normalized variance hvariance)
      current hA proposalFloor
    · exact hleft current hcurrent
    · exact hright current hcurrent
  · exact haccept

end McmcLean.Kernel
