import McmcLean.Kernel.DensityCoupling
import McmcLean.Kernel.GaussianRandomWalk
import McmcLean.Kernel.CoupledMetropolisHastings

/-!
# Maximal Gaussian proposal couplings

This module specializes the general maximal density construction to Gaussian
random-walk proposal rows. It proves the two proposal marginals and strictly
positive diagonal mass for every pair of current states, packages the rows as
a measurable Markov coupling kernel, and constructs the corresponding
shared-uniform coupled RWMH transition with proved marginals and positive
one-step exact-meeting probability.
-/

open MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace McmcLean.Kernel

open ProbabilityTheory

/-- Common density of the two Gaussian proposal rows indexed by a pair of
current states. -/
noncomputable def gaussianProposalCommonDensity
    (variance : ℝ≥0) (current : ℝ × ℝ) (z : ℝ) : ENNReal :=
  min (randomWalkProposalDensity (gaussianPDF 0 variance) current.1 z)
    (randomWalkProposalDensity (gaussianPDF 0 variance) current.2 z)

theorem measurable_uncurry_gaussianProposalCommonDensity (variance : ℝ≥0) :
    Measurable (Function.uncurry (gaussianProposalCommonDensity variance)) := by
  change Measurable fun p : (ℝ × ℝ) × ℝ =>
    min (gaussianPDF 0 variance (p.2 - p.1.1))
      (gaussianPDF 0 variance (p.2 - p.1.2))
  exact ((measurable_gaussianPDF 0 variance).comp
      (measurable_snd.sub (measurable_fst.comp measurable_fst))).min
    ((measurable_gaussianPDF 0 variance).comp
      (measurable_snd.sub (measurable_snd.comp measurable_fst)))

/-- Density overlap of Gaussian proposal rows as a function of their two
centers. -/
noncomputable def gaussianProposalOverlap
    (variance : ℝ≥0) (current : ℝ × ℝ) : ENNReal :=
  ∫⁻ z, gaussianProposalCommonDensity variance current z

/-- Gaussian proposal overlap is jointly measurable in both current states. -/
theorem measurable_gaussianProposalOverlap (variance : ℝ≥0) :
    Measurable (gaussianProposalOverlap variance) := by
  exact (measurable_uncurry_gaussianProposalCommonDensity variance).lintegral_prod_right

theorem gaussianProposalOverlap_eq_densityOverlap
    (variance : ℝ≥0) (current : ℝ × ℝ) :
    gaussianProposalOverlap variance current =
      densityOverlap volume
        (randomWalkProposalDensity (gaussianPDF 0 variance) current.1)
        (randomWalkProposalDensity (gaussianPDF 0 variance) current.2) :=
  rfl

/-- The parameterized common part of the Gaussian proposal coupling, mapped
onto the diagonal. -/
noncomputable def commonGaussianProposalKernel (variance : ℝ≥0) :
    ProbabilityTheory.Kernel (ℝ × ℝ) (ℝ × ℝ) :=
  ProbabilityTheory.Kernel.map
    ((ProbabilityTheory.Kernel.const (ℝ × ℝ) volume).withDensity
      (gaussianProposalCommonDensity variance))
    (fun z => (z, z))

/-- A row of the common Gaussian proposal kernel is exactly the common density
measure pushed to the diagonal. -/
theorem commonGaussianProposalKernel_apply
    (variance : ℝ≥0) (current : ℝ × ℝ) :
    commonGaussianProposalKernel variance current =
      (commonDensityMeasure volume
        (randomWalkProposalDensity (gaussianPDF 0 variance) current.1)
        (randomWalkProposalDensity (gaussianPDF 0 variance) current.2)).map
          (fun z => (z, z)) := by
  have hdiag : Measurable (fun z : ℝ => (z, z)) :=
    measurable_id.prodMk measurable_id
  rw [commonGaussianProposalKernel,
    ProbabilityTheory.Kernel.map_apply _ hdiag,
    ProbabilityTheory.Kernel.withDensity_apply _
      (measurable_uncurry_gaussianProposalCommonDensity variance),
    ProbabilityTheory.Kernel.const_apply]
  rfl

/-- The common diagonal subkernel places exactly the proposal overlap on the
exact-meeting event. -/
theorem commonGaussianProposalKernel_diagonal
    (variance : ℝ≥0) (current : ℝ × ℝ) :
    commonGaussianProposalKernel variance current (Set.diagonal ℝ) =
      gaussianProposalOverlap variance current := by
  rw [commonGaussianProposalKernel_apply]
  have hdiag : Measurable (fun z : ℝ => (z, z)) :=
    measurable_id.prodMk measurable_id
  rw [Measure.map_apply hdiag measurableSet_diagonal]
  have hpre : (fun z : ℝ => (z, z)) ⁻¹' Set.diagonal ℝ = Set.univ := by
    ext z
    simp
  rw [hpre, commonDensityMeasure_apply_univ]
  rfl

/-- Density of the left Gaussian proposal residual after removing the common
part. -/
noncomputable def leftGaussianProposalResidualDensity
    (variance : ℝ≥0) (current : ℝ × ℝ) (z : ℝ) : ENNReal :=
  randomWalkProposalDensity (gaussianPDF 0 variance) current.1 z -
    gaussianProposalCommonDensity variance current z

/-- Density of the right Gaussian proposal residual. -/
noncomputable def rightGaussianProposalResidualDensity
    (variance : ℝ≥0) (current : ℝ × ℝ) (z : ℝ) : ENNReal :=
  randomWalkProposalDensity (gaussianPDF 0 variance) current.2 z -
    gaussianProposalCommonDensity variance current z

theorem measurable_uncurry_leftGaussianProposalResidualDensity
    (variance : ℝ≥0) :
    Measurable (Function.uncurry
      (leftGaussianProposalResidualDensity variance)) := by
  have hproposal := measurable_uncurry_randomWalkProposalDensity
    (measurable_gaussianPDF 0 variance)
  exact (hproposal.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).sub
    (measurable_uncurry_gaussianProposalCommonDensity variance)

theorem measurable_uncurry_rightGaussianProposalResidualDensity
    (variance : ℝ≥0) :
    Measurable (Function.uncurry
      (rightGaussianProposalResidualDensity variance)) := by
  have hproposal := measurable_uncurry_randomWalkProposalDensity
    (measurable_gaussianPDF 0 variance)
  exact (hproposal.comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).sub
    (measurable_uncurry_gaussianProposalCommonDensity variance)

/-- Parameterized left residual Gaussian proposal measure. -/
noncomputable def leftGaussianProposalResidualKernel (variance : ℝ≥0) :
    ProbabilityTheory.Kernel (ℝ × ℝ) ℝ :=
  (ProbabilityTheory.Kernel.const (ℝ × ℝ) volume).withDensity
    (leftGaussianProposalResidualDensity variance)

/-- Parameterized right residual Gaussian proposal measure. -/
noncomputable def rightGaussianProposalResidualKernel (variance : ℝ≥0) :
    ProbabilityTheory.Kernel (ℝ × ℝ) ℝ :=
  (ProbabilityTheory.Kernel.const (ℝ × ℝ) volume).withDensity
    (rightGaussianProposalResidualDensity variance)

instance leftGaussianProposalResidualKernel.instIsSFiniteKernel
    (variance : ℝ≥0) :
    IsSFiniteKernel (leftGaussianProposalResidualKernel variance) := by
  rw [leftGaussianProposalResidualKernel]
  apply ProbabilityTheory.Kernel.IsSFiniteKernel.withDensity
  intro current z
  apply ne_top_of_le_ne_top gaussianPDF_ne_top
  exact tsub_le_self.trans_eq rfl

instance rightGaussianProposalResidualKernel.instIsSFiniteKernel
    (variance : ℝ≥0) :
    IsSFiniteKernel (rightGaussianProposalResidualKernel variance) := by
  rw [rightGaussianProposalResidualKernel]
  apply ProbabilityTheory.Kernel.IsSFiniteKernel.withDensity
  intro current z
  apply ne_top_of_le_ne_top gaussianPDF_ne_top
  exact tsub_le_self.trans_eq rfl

theorem leftGaussianProposalResidualKernel_apply
    (variance : ℝ≥0) (current : ℝ × ℝ) :
    leftGaussianProposalResidualKernel variance current =
      leftResidualDensityMeasure volume
        (randomWalkProposalDensity (gaussianPDF 0 variance) current.1)
        (randomWalkProposalDensity (gaussianPDF 0 variance) current.2) := by
  rw [leftGaussianProposalResidualKernel,
    ProbabilityTheory.Kernel.withDensity_apply _
      (measurable_uncurry_leftGaussianProposalResidualDensity variance),
    ProbabilityTheory.Kernel.const_apply]
  rfl

theorem rightGaussianProposalResidualKernel_apply
    (variance : ℝ≥0) (current : ℝ × ℝ) :
    rightGaussianProposalResidualKernel variance current =
      rightResidualDensityMeasure volume
        (randomWalkProposalDensity (gaussianPDF 0 variance) current.1)
        (randomWalkProposalDensity (gaussianPDF 0 variance) current.2) := by
  rw [rightGaussianProposalResidualKernel,
    ProbabilityTheory.Kernel.withDensity_apply _
      (measurable_uncurry_rightGaussianProposalResidualDensity variance),
    ProbabilityTheory.Kernel.const_apply]
  rfl

/-- Conditionally independent product of the two Gaussian proposal residual
kernels. -/
noncomputable def gaussianProposalResidualProductKernel (variance : ℝ≥0) :
    ProbabilityTheory.Kernel (ℝ × ℝ) (ℝ × ℝ) :=
  leftGaussianProposalResidualKernel variance ×ₖ
    rightGaussianProposalResidualKernel variance

instance gaussianProposalResidualProductKernel.instIsSFiniteKernel
    (variance : ℝ≥0) :
    IsSFiniteKernel (gaussianProposalResidualProductKernel variance) := by
  rw [gaussianProposalResidualProductKernel]
  infer_instance

theorem gaussianProposalResidualProductKernel_apply
    (variance : ℝ≥0) (current : ℝ × ℝ) :
    gaussianProposalResidualProductKernel variance current =
      (leftResidualDensityMeasure volume
        (randomWalkProposalDensity (gaussianPDF 0 variance) current.1)
        (randomWalkProposalDensity (gaussianPDF 0 variance) current.2)).prod
      (rightResidualDensityMeasure volume
        (randomWalkProposalDensity (gaussianPDF 0 variance) current.1)
        (randomWalkProposalDensity (gaussianPDF 0 variance) current.2)) := by
  rw [gaussianProposalResidualProductKernel,
    ProbabilityTheory.Kernel.prod_apply,
    leftGaussianProposalResidualKernel_apply,
    rightGaussianProposalResidualKernel_apply]

/-- The residual product scaled by the reciprocal missing overlap mass. -/
noncomputable def scaledGaussianProposalResidualKernel (variance : ℝ≥0) :
    ProbabilityTheory.Kernel (ℝ × ℝ) (ℝ × ℝ) :=
  (gaussianProposalResidualProductKernel variance).withDensity
    (fun current _proposal => (1 - gaussianProposalOverlap variance current)⁻¹)

theorem measurable_uncurry_gaussianResidualScale (variance : ℝ≥0) :
    Measurable (Function.uncurry
      (fun current (_proposal : ℝ × ℝ) =>
        (1 - gaussianProposalOverlap variance current)⁻¹)) := by
  exact (measurable_const.sub
    ((measurable_gaussianProposalOverlap variance).comp measurable_fst)).inv

theorem scaledGaussianProposalResidualKernel_apply
    (variance : ℝ≥0) (current : ℝ × ℝ) :
    scaledGaussianProposalResidualKernel variance current =
      (1 - gaussianProposalOverlap variance current)⁻¹ •
        ((leftResidualDensityMeasure volume
          (randomWalkProposalDensity (gaussianPDF 0 variance) current.1)
          (randomWalkProposalDensity (gaussianPDF 0 variance) current.2)).prod
        (rightResidualDensityMeasure volume
          (randomWalkProposalDensity (gaussianPDF 0 variance) current.1)
          (randomWalkProposalDensity (gaussianPDF 0 variance) current.2))) := by
  rw [scaledGaussianProposalResidualKernel,
    ProbabilityTheory.Kernel.withDensity_apply _
      (measurable_uncurry_gaussianResidualScale variance),
    withDensity_const, gaussianProposalResidualProductKernel_apply]

/-- Parameterized Gaussian proposal coupling kernel: common mass on the
diagonal plus the scaled independent residual product. -/
noncomputable def maximalGaussianProposalKernel (variance : ℝ≥0) :
    ProbabilityTheory.Kernel (ℝ × ℝ) (ℝ × ℝ) :=
  commonGaussianProposalKernel variance +
    scaledGaussianProposalResidualKernel variance

/-- Maximal coupling of the one-dimensional Gaussian random-walk proposal
rows from current states `x` and `y`. -/
noncomputable def maximalGaussianProposalMeasure
    (variance : ℝ≥0) (x y : ℝ) : Measure (ℝ × ℝ) :=
  maximalDensityCoupling volume
    (randomWalkProposalDensity (gaussianPDF 0 variance) x)
    (randomWalkProposalDensity (gaussianPDF 0 variance) y)

theorem measurable_gaussianProposalDensity_left (variance : ℝ≥0) (x : ℝ) :
    Measurable (randomWalkProposalDensity (gaussianPDF 0 variance) x) :=
  Measurable.of_uncurry_left
    (measurable_uncurry_randomWalkProposalDensity
      (measurable_gaussianPDF 0 variance))

theorem gaussianProposalDensity_normalized
    (variance : ℝ≥0) (hvariance : variance ≠ 0) (x : ℝ) :
    ∫⁻ z, randomWalkProposalDensity (gaussianPDF 0 variance) x z = 1 :=
  randomWalkProposalDensity_normalized volume
    (measurable_gaussianPDF 0 variance)
    (lintegral_gaussianPDF_eq_one 0 hvariance) x

/-- For nondegenerate variance, each row of the parameterized kernel is the
maximal Gaussian proposal measure constructed above. -/
theorem maximalGaussianProposalKernel_apply
    (variance : ℝ≥0) (hvariance : variance ≠ 0) (current : ℝ × ℝ) :
    maximalGaussianProposalKernel variance current =
      maximalGaussianProposalMeasure variance current.1 current.2 := by
  rw [maximalGaussianProposalKernel, ProbabilityTheory.Kernel.coe_add,
    Pi.add_apply, commonGaussianProposalKernel_apply,
    scaledGaussianProposalResidualKernel_apply]
  rw [maximalGaussianProposalMeasure, maximalDensityCoupling]
  split_ifs with hoverlap
  · have hoverlap' : gaussianProposalOverlap variance current = 1 := by
      simpa only [gaussianProposalOverlap_eq_densityOverlap] using hoverlap
    have hleftZero : leftResidualDensityMeasure volume
        (randomWalkProposalDensity (gaussianPDF 0 variance) current.1)
        (randomWalkProposalDensity (gaussianPDF 0 variance) current.2) = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      rw [leftResidualDensityMeasure_apply_univ volume
        (measurable_gaussianProposalDensity_left variance current.1)
        (measurable_gaussianProposalDensity_left variance current.2)
        (gaussianProposalDensity_normalized variance hvariance current.1),
        ← gaussianProposalOverlap_eq_densityOverlap, hoverlap', tsub_self]
    rw [hoverlap', tsub_self, ENNReal.inv_zero, hleftZero, Measure.zero_prod,
      smul_zero, add_zero]
  · rfl

/-- The maximal Gaussian proposal measure has the intended two Gaussian
random-walk marginals. -/
theorem maximalGaussianProposalMeasure_isCoupling
    (variance : ℝ≥0) (hvariance : variance ≠ 0) (x y : ℝ) :
    IsMeasureCoupling (maximalGaussianProposalMeasure variance x y)
      (volume.withDensity
        (randomWalkProposalDensity (gaussianPDF 0 variance) x))
      (volume.withDensity
        (randomWalkProposalDensity (gaussianPDF 0 variance) y)) := by
  exact maximalDensityCoupling_isCoupling volume
    (measurable_gaussianProposalDensity_left variance x)
    (measurable_gaussianProposalDensity_left variance y)
    (gaussianProposalDensity_normalized variance hvariance x)
    (gaussianProposalDensity_normalized variance hvariance y)

/-- The same marginal theorem stated directly using the proposal kernel that
appears in the existing Gaussian RWMH definition. -/
theorem maximalGaussianProposalMeasure_isCoupling_densityProposal
    (variance : ℝ≥0) (hvariance : variance ≠ 0) (x y : ℝ) :
    IsMeasureCoupling (maximalGaussianProposalMeasure variance x y)
      (densityProposal volume
        (randomWalkProposalDensity (gaussianPDF 0 variance)) x)
      (densityProposal volume
        (randomWalkProposalDensity (gaussianPDF 0 variance)) y) := by
  have hproposal := measurable_uncurry_randomWalkProposalDensity
    (measurable_gaussianPDF 0 variance)
  have hx : densityProposal volume
      (randomWalkProposalDensity (gaussianPDF 0 variance)) x =
      volume.withDensity
        (randomWalkProposalDensity (gaussianPDF 0 variance) x) := by
    rw [densityProposal,
      ProbabilityTheory.Kernel.withDensity_apply _ hproposal,
      ProbabilityTheory.Kernel.const_apply]
  have hy : densityProposal volume
      (randomWalkProposalDensity (gaussianPDF 0 variance)) y =
      volume.withDensity
        (randomWalkProposalDensity (gaussianPDF 0 variance) y) := by
    rw [densityProposal,
      ProbabilityTheory.Kernel.withDensity_apply _ hproposal,
      ProbabilityTheory.Kernel.const_apply]
  rw [hx, hy]
  exact maximalGaussianProposalMeasure_isCoupling variance hvariance x y

/-- The parameterized maximal Gaussian proposal construction is a Markov
kernel. -/
theorem maximalGaussianProposalKernel_isMarkov
    (variance : ℝ≥0) (hvariance : variance ≠ 0) :
    IsMarkovKernel (maximalGaussianProposalKernel variance) := by
  constructor
  intro current
  rw [maximalGaussianProposalKernel_apply variance hvariance current]
  exact maximalDensityCoupling_isProbability volume
    (measurable_gaussianProposalDensity_left variance current.1)
    (measurable_gaussianProposalDensity_left variance current.2)
    (gaussianProposalDensity_normalized variance hvariance current.1)
    (gaussianProposalDensity_normalized variance hvariance current.2)

/-- The maximal Gaussian proposal kernel couples the two rows of the Gaussian
random-walk proposal kernel. -/
theorem maximalGaussianProposalKernel_isCoupling
    (variance : ℝ≥0) (hvariance : variance ≠ 0) :
    IsCoupling (maximalGaussianProposalKernel variance)
      (densityProposal volume
        (randomWalkProposalDensity (gaussianPDF 0 variance)))
      (densityProposal volume
        (randomWalkProposalDensity (gaussianPDF 0 variance))) := by
  constructor
  · ext current s hs
    rw [ProbabilityTheory.Kernel.fst_apply' _ _ hs,
      ProbabilityTheory.Kernel.comap_apply,
      maximalGaussianProposalKernel_apply variance hvariance current]
    have hrow := maximalGaussianProposalMeasure_isCoupling_densityProposal
      variance hvariance current.1 current.2
    change (maximalGaussianProposalMeasure variance current.1 current.2)
      (Prod.fst ⁻¹' s) = _
    rw [← Measure.fst_apply hs, hrow.fst]
  · ext current s hs
    rw [ProbabilityTheory.Kernel.snd_apply' _ _ hs,
      ProbabilityTheory.Kernel.comap_apply,
      maximalGaussianProposalKernel_apply variance hvariance current]
    have hrow := maximalGaussianProposalMeasure_isCoupling_densityProposal
      variance hvariance current.1 current.2
    change (maximalGaussianProposalMeasure variance current.1 current.2)
      (Prod.snd ⁻¹' s) = _
    rw [← Measure.snd_apply hs, hrow.snd]

/-- Coupled Gaussian random-walk Metropolis--Hastings using a maximal Gaussian
proposal coupling and one shared accept/reject uniform. -/
noncomputable def coupledGaussianRandomWalkMetropolisHastings
    (weight : ℝ → ENNReal) (variance : ℝ≥0) (hvariance : variance ≠ 0) :
    ProbabilityTheory.Kernel (ℝ × ℝ) (ℝ × ℝ) := by
  letI : IsMarkovKernel (maximalGaussianProposalKernel variance) :=
    maximalGaussianProposalKernel_isMarkov variance hvariance
  exact coupledAcceptRejectKernel (maximalGaussianProposalKernel variance)
    (densityAcceptance weight
      (randomWalkProposalDensity (gaussianPDF 0 variance)))
    (densityAcceptance_le_one weight
      (randomWalkProposalDensity (gaussianPDF 0 variance)))

/-- The coupled Gaussian RWMH transition is a Markov kernel. -/
theorem coupledGaussianRandomWalkMetropolisHastings_isMarkov
    (weight : ℝ → ENNReal) (variance : ℝ≥0) (hvariance : variance ≠ 0)
    (hweight : Measurable weight) :
    IsMarkovKernel
      (coupledGaussianRandomWalkMetropolisHastings weight variance hvariance) := by
  letI : IsMarkovKernel (maximalGaussianProposalKernel variance) :=
    maximalGaussianProposalKernel_isMarkov variance hvariance
  rw [coupledGaussianRandomWalkMetropolisHastings]
  apply coupledAcceptRejectKernel_isMarkov
  exact measurable_uncurry_densityAcceptance hweight
    (measurable_uncurry_randomWalkProposalDensity
      (measurable_gaussianPDF 0 variance))

/-- Both coordinates of coupled Gaussian RWMH are exactly the existing
single-chain Gaussian RWMH kernel. -/
theorem coupledGaussianRandomWalkMetropolisHastings_isCoupling
    (weight : ℝ → ENNReal) (variance : ℝ≥0) (hvariance : variance ≠ 0)
    (hweight : Measurable weight) :
    IsCoupling
      (coupledGaussianRandomWalkMetropolisHastings weight variance hvariance)
      (gaussianRandomWalkMetropolisHastings weight variance hvariance)
      (gaussianRandomWalkMetropolisHastings weight variance hvariance) := by
  let Q := densityProposal volume
    (randomWalkProposalDensity (gaussianPDF 0 variance))
  let accept := densityAcceptance weight
    (randomWalkProposalDensity (gaussianPDF 0 variance))
  letI : IsMarkovKernel Q := densityProposal_isMarkov volume
    (measurable_uncurry_randomWalkProposalDensity
      (measurable_gaussianPDF 0 variance))
    (randomWalkProposalDensity_normalized volume
      (measurable_gaussianPDF 0 variance)
      (lintegral_gaussianPDF_eq_one 0 hvariance))
  letI : IsMarkovKernel (maximalGaussianProposalKernel variance) :=
    maximalGaussianProposalKernel_isMarkov variance hvariance
  have hcoupling : IsCoupling
      (coupledAcceptRejectKernel (maximalGaussianProposalKernel variance)
        accept (densityAcceptance_le_one weight
          (randomWalkProposalDensity (gaussianPDF 0 variance))))
      (metropolisHastings Q accept) (metropolisHastings Q accept) :=
    coupledAcceptRejectKernel_isCoupling Q
      (maximalGaussianProposalKernel variance)
      (maximalGaussianProposalKernel_isCoupling variance hvariance)
      (measurable_uncurry_densityAcceptance hweight
        (measurable_uncurry_randomWalkProposalDensity
          (measurable_gaussianPDF 0 variance)))
      (densityAcceptance_le_one weight
        (randomWalkProposalDensity (gaussianPDF 0 variance)))
  simpa only [coupledGaussianRandomWalkMetropolisHastings,
    gaussianRandomWalkMetropolisHastings, randomWalkMetropolisHastings,
    densityMetropolisHastings, Q, accept] using hcoupling

/-- Every pair of nondegenerate Gaussian random-walk proposal rows has
strictly positive density overlap. -/
theorem gaussianProposalDensity_overlap_pos
    (variance : ℝ≥0) (hvariance : variance ≠ 0) (x y : ℝ) :
    0 < densityOverlap volume
      (randomWalkProposalDensity (gaussianPDF 0 variance) x)
      (randomWalkProposalDensity (gaussianPDF 0 variance) y) := by
  apply densityOverlap_pos volume
    (measurable_gaussianProposalDensity_left variance x)
    (measurable_gaussianProposalDensity_left variance y)
  · simp
  · intro z
    exact gaussianPDF_pos 0 hvariance (z - x)
  · intro z
    exact gaussianPDF_pos 0 hvariance (z - y)

/-- The maximal Gaussian proposal coupling has positive probability of
proposing exactly the same point from any two current states. -/
theorem maximalGaussianProposalMeasure_diagonal_pos
    (variance : ℝ≥0) (hvariance : variance ≠ 0) (x y : ℝ) :
    0 < maximalGaussianProposalMeasure variance x y (Set.diagonal ℝ) := by
  exact maximalDensityCoupling_diagonal_pos volume
    (gaussianProposalDensity_overlap_pos variance hvariance x y)

/-- The parameterized maximal Gaussian proposal kernel has positive exact-
agreement probability from every pair of current states. -/
theorem maximalGaussianProposalKernel_diagonal_pos
    (variance : ℝ≥0) (hvariance : variance ≠ 0) (current : ℝ × ℝ) :
    0 < maximalGaussianProposalKernel variance current (Set.diagonal ℝ) := by
  rw [maximalGaussianProposalKernel_apply variance hvariance current]
  exact maximalGaussianProposalMeasure_diagonal_pos variance hvariance
    current.1 current.2

/-- With an everywhere positive finite target density, Gaussian RWMH
acceptance is strictly positive for every current/proposed pair. -/
theorem gaussianDensityAcceptance_pos
    (weight : ℝ → ENNReal) (variance : ℝ≥0) (hvariance : variance ≠ 0)
    (hweightPos : ∀ x, 0 < weight x)
    (hweightFinite : ∀ x, weight x ≠ ∞) (x z : ℝ) :
    0 < densityAcceptance weight
      (randomWalkProposalDensity (gaussianPDF 0 variance)) x z := by
  have hforwardPos : 0 < forwardDensityFlow weight
      (randomWalkProposalDensity (gaussianPDF 0 variance)) x z := by
    exact ENNReal.mul_pos (hweightPos x).ne'
      (gaussianPDF_pos 0 hvariance (z - x)).ne'
  have hreversePos : 0 < forwardDensityFlow weight
      (randomWalkProposalDensity (gaussianPDF 0 variance)) z x := by
    exact ENNReal.mul_pos (hweightPos z).ne'
      (gaussianPDF_pos 0 hvariance (x - z)).ne'
  rw [densityAcceptance]
  split_ifs with hzero
  · exact (hforwardPos.ne' hzero).elim
  · apply ENNReal.div_pos
    · exact (lt_min hforwardPos hreversePos).ne'
    · exact ENNReal.mul_ne_top (hweightFinite x) gaussianPDF_ne_top

/-- The coupled Gaussian RWMH transition has positive probability of exact
meeting in one step whenever the target density is everywhere positive and
finite. -/
theorem coupledGaussianRandomWalkMetropolisHastings_meeting_pos
    (weight : ℝ → ENNReal) (variance : ℝ≥0) (hvariance : variance ≠ 0)
    (hweight : Measurable weight) (hweightPos : ∀ x, 0 < weight x)
    (hweightFinite : ∀ x, weight x ≠ ∞) (current : ℝ × ℝ) :
    0 < coupledGaussianRandomWalkMetropolisHastings weight variance hvariance
      current (Set.diagonal ℝ) := by
  letI : IsMarkovKernel (maximalGaussianProposalKernel variance) :=
    maximalGaussianProposalKernel_isMarkov variance hvariance
  rw [coupledGaussianRandomWalkMetropolisHastings]
  apply coupledAcceptRejectKernel_meeting_pos
  · exact measurable_uncurry_densityAcceptance hweight
      (measurable_uncurry_randomWalkProposalDensity
        (measurable_gaussianPDF 0 variance))
  · exact maximalGaussianProposalKernel_diagonal_pos variance hvariance current
  · intro z _hz
    exact lt_min
      (gaussianDensityAcceptance_pos weight variance hvariance hweightPos
        hweightFinite current.1 z.1)
      (gaussianDensityAcceptance_pos weight variance hvariance hweightPos
        hweightFinite current.2 z.2)

end McmcLean.Kernel
