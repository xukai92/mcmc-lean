import McmcLean.Hamiltonian.CoupledMultinomialHMC
import McmcLean.Hamiltonian.LocalContractivity
import McmcLean.Kernel.EuclideanGaussianProposalCoupling
import McmcLean.Kernel.MeetingDrift
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Coupled multinomial-HMC/RWMH mixtures

This module forms the paper's same-state-space mixture of the verified
finite-dimensional multinomial HMC and Gaussian RWMH transitions.  The
coupled mixture has the corresponding verified single-chain mixture on both
marginals, preserves the Boltzmann position target, and inherits positive
one-step exact-meeting probability from every positive-weight RWMH branch.
-/

open MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace McmcLean.Hamiltonian

open ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- Real-ratio form of symmetric Gaussian RWMH acceptance for a Boltzmann
target. -/
noncomputable def boltzmannRwmhAcceptance
    (potential : Position ι → ℝ) (x z : Position ι) : ENNReal :=
  ENNReal.ofReal
    (min (Real.exp (-potential x)) (Real.exp (-potential z)) /
      Real.exp (-potential x))

omit [Fintype ι] in
/-- The ratio-form Boltzmann acceptance is jointly continuous for a
continuous potential. -/
theorem continuous_uncurry_boltzmannRwmhAcceptance
    {potential : Position ι → ℝ} (hpotential : Continuous potential) :
    Continuous (Function.uncurry (boltzmannRwmhAcceptance potential)) := by
  unfold boltzmannRwmhAcceptance
  apply ENNReal.continuous_ofReal.comp
  have hleft : Continuous fun p : Position ι × Position ι =>
      Real.exp (-potential p.1) :=
    Real.continuous_exp.comp (hpotential.comp continuous_fst).neg
  have hright : Continuous fun p : Position ι × Position ι =>
      Real.exp (-potential p.2) :=
    Real.continuous_exp.comp (hpotential.comp continuous_snd).neg
  exact (hleft.min hright).div hleft fun p => (Real.exp_pos _).ne'

/-- Gaussian RWMH density acceptance is exactly the continuous real-ratio
Boltzmann formula. -/
theorem gaussianDensityAcceptance_eq_boltzmannRwmhAcceptance
    (potential : Position ι → ℝ) (variance : ℝ≥0)
    (hvariance : variance ≠ 0) (x z : Position ι) :
    McmcLean.Kernel.densityAcceptance (positionBoltzmannWeight potential)
        (McmcLean.Kernel.randomWalkProposalDensity
          (McmcLean.Kernel.isotropicGaussianPDF variance)) x z =
      boltzmannRwmhAcceptance potential x z := by
  rw [McmcLean.Kernel.randomWalk_densityAcceptance_eq_min_weight_div]
  · unfold positionBoltzmannWeight boltzmannRwmhAcceptance
    rw [← ENNReal.ofReal_min, ← ENNReal.ofReal_div_of_pos (Real.exp_pos _)]
  · exact McmcLean.Kernel.isotropicGaussianPDF_even variance
  · intro y
    exact (positionBoltzmannWeight_pos potential y).ne'
  · intro y
    exact (McmcLean.Kernel.isotropicGaussianPDF_pos variance hvariance y).ne'
  · exact McmcLean.Kernel.isotropicGaussianPDF_ne_top variance

/-- Simultaneous shared-uniform acceptance when both chains propose the same
point. -/
noncomputable def boltzmannBothAcceptance
    (potential : Position ι → ℝ)
    (current : Position ι × Position ι) (z : Position ι) : ENNReal :=
  min (boltzmannRwmhAcceptance potential current.1 z)
    (boltzmannRwmhAcceptance potential current.2 z)

omit [Fintype ι] in
theorem continuous_uncurry_boltzmannBothAcceptance
    {potential : Position ι → ℝ} (hpotential : Continuous potential) :
    Continuous (Function.uncurry (boltzmannBothAcceptance potential)) := by
  apply Continuous.min
  · exact (continuous_uncurry_boltzmannRwmhAcceptance hpotential).comp
      ((continuous_fst.fst).prodMk continuous_snd)
  · exact (continuous_uncurry_boltzmannRwmhAcceptance hpotential).comp
      ((continuous_fst.snd).prodMk continuous_snd)

omit [Fintype ι] in
theorem boltzmannBothAcceptance_pos
    (potential : Position ι → ℝ)
    (current : Position ι × Position ι) (z : Position ι) :
    0 < boltzmannBothAcceptance potential current z := by
  apply lt_min
  all_goals
    unfold boltzmannRwmhAcceptance
    rw [ENNReal.ofReal_pos]
    exact div_pos (lt_min (Real.exp_pos _) (Real.exp_pos _)) (Real.exp_pos _)

omit [Fintype ι] in
/-- On compact current and proposal regions, simultaneous Boltzmann Gaussian
RWMH acceptance has one strictly positive common floor. -/
theorem exists_pos_boltzmannBothAcceptanceFloor_on_compact
    {potential : Position ι → ℝ} (hpotential : Continuous potential)
    {C : Set (Position ι × Position ι)} {A : Set (Position ι)}
    (hC : IsCompact C) (hCne : C.Nonempty)
    (hA : IsCompact A) (hAne : A.Nonempty) :
    ∃ acceptanceFloor : ENNReal, 0 < acceptanceFloor ∧
      ∀ current ∈ C, ∀ z ∈ A,
        acceptanceFloor ≤ boltzmannBothAcceptance potential current z := by
  obtain ⟨acceptanceFloor, hfloorPos, hfloor⟩ :=
    McmcLean.Kernel.exists_pos_le_on_compact (hC.prod hA)
      (hCne.prod hAne)
      (continuous_uncurry_boltzmannBothAcceptance hpotential)
      (fun p _ => boltzmannBothAcceptance_pos potential p.1 p.2)
  exact ⟨acceptanceFloor, hfloorPos,
    fun current hcurrent z hz => hfloor (current, z) ⟨hcurrent, hz⟩⟩

/-- On a diagonal proposal, the shared-uniform simultaneous acceptance weight
is exactly the compact-friendly Boltzmann acceptance function. -/
theorem coupledBothAcceptWeight_diagonal_eq_boltzmannBothAcceptance
    (potential : Position ι → ℝ) (variance : ℝ≥0)
    (hvariance : variance ≠ 0) (current proposal : Position ι × Position ι)
    (hproposal : proposal ∈ Set.diagonal (Position ι)) :
    McmcLean.Kernel.coupledBothAcceptWeight
        (McmcLean.Kernel.densityAcceptance (positionBoltzmannWeight potential)
          (McmcLean.Kernel.randomWalkProposalDensity
            (McmcLean.Kernel.isotropicGaussianPDF variance))) current proposal =
      boltzmannBothAcceptance potential current proposal.1 := by
  rcases proposal with ⟨z₁, z₂⟩
  have hz : z₁ = z₂ := Set.mem_diagonal_iff.mp hproposal
  subst z₂
  unfold McmcLean.Kernel.coupledBothAcceptWeight
    McmcLean.Kernel.bothAcceptWeight McmcLean.Kernel.coupledLeftAcceptance
    McmcLean.Kernel.coupledRightAcceptance boltzmannBothAcceptance
  rw [gaussianDensityAcceptance_eq_boltzmannRwmhAcceptance
      potential variance hvariance current.1 z₁,
    gaussianDensityAcceptance_eq_boltzmannRwmhAcceptance
      potential variance hvariance current.2 z₁]

/-- Explicit exact-meeting constant produced by the RWMH branch of the
mixture from acceptance, proposal-density, and proposal-region bounds. -/
noncomputable def hmcRwmhMeetingBound
    (p : Set.Icc (0 : NNReal) 1)
    (acceptanceFloor proposalFloor regionMass : ENNReal) : ENNReal :=
  ((1 - p.1 : NNReal) : ENNReal) *
    (acceptanceFloor * (proposalFloor * regionMass))

/-- The explicit mixture meeting constant is strictly positive whenever all
four contributing factors are strictly positive. -/
theorem hmcRwmhMeetingBound_pos
    (p : Set.Icc (0 : NNReal) 1) (hp : p.1 < 1)
    {acceptanceFloor proposalFloor regionMass : ENNReal}
    (hacceptance : 0 < acceptanceFloor)
    (hproposal : 0 < proposalFloor) (hregion : 0 < regionMass) :
    0 < hmcRwmhMeetingBound p acceptanceFloor proposalFloor regionMass := by
  have hweightNN : 0 < (1 - p.1 : NNReal) := tsub_pos_iff_lt.mpr hp
  have hweight : 0 < (((1 - p.1 : NNReal) : NNReal) : ENNReal) := by
    exact_mod_cast hweightNN
  exact ENNReal.mul_pos hweight.ne'
    (ENNReal.mul_pos hacceptance.ne'
      (ENNReal.mul_pos hproposal.ne' hregion.ne').ne').ne'

/-- Single-chain mixture with HMC weight `p` and RWMH weight `1 - p`. -/
noncomputable def hmcRwmhMixture
    (p : Set.Icc (0 : NNReal) 1)
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) (variance : ℝ≥0)
    (hvariance : variance ≠ 0) :
    Kernel (Position ι) (Position ι) :=
  McmcLean.Kernel.mixture p
    (standardPositionMultinomialHMC potential gradient ε L
      hpotential hgradient)
    (McmcLean.Kernel.euclideanGaussianRandomWalkMetropolisHastings
      (positionBoltzmannWeight potential) variance hvariance)

instance hmcRwmhMixture_isMarkovKernel
    (p : Set.Icc (0 : NNReal) 1)
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) (variance : ℝ≥0)
    (hvariance : variance ≠ 0) :
    IsMarkovKernel (hmcRwmhMixture p potential gradient ε L hpotential
      hgradient variance hvariance) := by
  unfold hmcRwmhMixture
  letI : IsMarkovKernel
      (McmcLean.Kernel.euclideanGaussianRandomWalkMetropolisHastings
        (positionBoltzmannWeight potential) variance hvariance) :=
    McmcLean.Kernel.euclideanGaussianRandomWalkMetropolisHastings_isMarkov
      _ variance hvariance (measurable_positionBoltzmannWeight hpotential)
  infer_instance

/-- Coupled mixture using maximal shared-momentum/index HMC in the first
branch and exact-meeting Gaussian RWMH in the second. -/
noncomputable def coupledHmcRwmhMixture
    (p : Set.Icc (0 : NNReal) 1)
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) (variance : ℝ≥0)
    (hvariance : variance ≠ 0) :
    Kernel (Position ι × Position ι) (Position ι × Position ι) :=
  McmcLean.Kernel.mixture p
    (maximalSharedMomentumCoupledPositionMultinomialHMC
      potential gradient ε L hpotential hgradient)
    (McmcLean.Kernel.coupledEuclideanGaussianRandomWalkMetropolisHastings
      (positionBoltzmannWeight potential) variance hvariance)

instance coupledHmcRwmhMixture_isMarkovKernel
    (p : Set.Icc (0 : NNReal) 1)
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) (variance : ℝ≥0)
    (hvariance : variance ≠ 0) :
    IsMarkovKernel (coupledHmcRwmhMixture p potential gradient ε L hpotential
      hgradient variance hvariance) := by
  unfold coupledHmcRwmhMixture
  letI : IsMarkovKernel
      (McmcLean.Kernel.coupledEuclideanGaussianRandomWalkMetropolisHastings
        (positionBoltzmannWeight potential) variance hvariance) :=
    McmcLean.Kernel.coupledEuclideanGaussianRandomWalkMetropolisHastings_isMarkov
      _ variance hvariance (measurable_positionBoltzmannWeight hpotential)
  infer_instance

/-- The coupled mixture has the verified HMC/RWMH mixture on both marginals,
and that single-chain mixture preserves the Boltzmann position target. -/
theorem coupledHmcRwmhMixture_isCoupling_and_invariant
    (p : Set.Icc (0 : NNReal) 1)
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) (variance : ℝ≥0)
    (hvariance : variance ≠ 0) :
    McmcLean.Kernel.IsCoupling
        (coupledHmcRwmhMixture p potential gradient ε L hpotential
          hgradient variance hvariance)
        (hmcRwmhMixture p potential gradient ε L hpotential hgradient
          variance hvariance)
        (hmcRwmhMixture p potential gradient ε L hpotential hgradient
          variance hvariance) ∧
      (hmcRwmhMixture p potential gradient ε L hpotential hgradient
        variance hvariance).Invariant (positionBoltzmannTarget potential) := by
  unfold coupledHmcRwmhMixture hmcRwmhMixture
  apply McmcLean.Kernel.coupledMixture_isCoupling_and_invariant
  · exact maximalSharedMomentumCoupledPositionMultinomialHMC_isCoupling
      potential gradient ε L hpotential hgradient
  · exact McmcLean.Kernel.coupledEuclideanGaussianRandomWalkMetropolisHastings_isCoupling
      (positionBoltzmannWeight potential) variance hvariance
      (measurable_positionBoltzmannWeight hpotential)
  · exact standardPositionMultinomialHMC_invariant hpotential hgradient ε L
  · simpa [positionBoltzmannTarget, McmcLean.Kernel.densityTarget] using
      McmcLean.Kernel.euclideanGaussianRandomWalkMetropolisHastings_invariant
        (positionBoltzmannWeight potential) variance hvariance
        (measurable_positionBoltzmannWeight hpotential)
        (positionBoltzmannWeight_ne_top potential)

/-- If the RWMH branch has positive weight, the concrete coupled mixture has
positive one-step exact-meeting probability from every pair of positions. -/
theorem coupledHmcRwmhMixture_meeting_pos
    (p : Set.Icc (0 : NNReal) 1) (hp : p.1 < 1)
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) (variance : ℝ≥0)
    (hvariance : variance ≠ 0) (current : Position ι × Position ι) :
    0 < coupledHmcRwmhMixture p potential gradient ε L hpotential hgradient
      variance hvariance current (Set.diagonal (Position ι)) := by
  unfold coupledHmcRwmhMixture
  apply McmcLean.Kernel.mixture_diagonal_pos_of_second p hp
  exact McmcLean.Kernel.coupledEuclideanGaussianRandomWalkMetropolisHastings_meeting_pos
    (positionBoltzmannWeight potential) variance hvariance
    (measurable_positionBoltzmannWeight hpotential)
    (positionBoltzmannWeight_pos potential)
    (positionBoltzmannWeight_ne_top potential) current

/-- Any uniform exact-meeting bound proved for Gaussian RWMH on a paired set
transfers to the concrete HMC/RWMH mixture, multiplied by the RWMH branch
weight.  Establishing such a uniform bound on the paper's chosen small set is
an analytic obligation, stronger than pointwise positivity. -/
theorem coupledHmcRwmhMixture_isExactMeetingSmallSet
    (p : Set.Icc (0 : NNReal) 1)
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) (variance : ℝ≥0)
    (hvariance : variance ≠ 0) (C : Set (Position ι × Position ι))
    (meetingBound : ENNReal)
    (hRwmh : McmcLean.Kernel.IsExactMeetingSmallSet
      (McmcLean.Kernel.coupledEuclideanGaussianRandomWalkMetropolisHastings
        (positionBoltzmannWeight potential) variance hvariance)
      C meetingBound) :
    McmcLean.Kernel.IsExactMeetingSmallSet
      (coupledHmcRwmhMixture p potential gradient ε L hpotential hgradient
        variance hvariance)
      C (((1 - p.1 : NNReal) : ENNReal) * meetingBound) := by
  unfold coupledHmcRwmhMixture
  exact McmcLean.Kernel.mixture_isExactMeetingSmallSet_of_second
    p _ _ hRwmh

/-- Fully quantitative reduction of the concrete mixture's small-set bound
to a common Gaussian proposal region and a simultaneous-acceptance floor. -/
theorem coupledHmcRwmhMixture_isExactMeetingSmallSet_of_floors
    (p : Set.Icc (0 : NNReal) 1)
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) (variance : ℝ≥0)
    (hvariance : variance ≠ 0)
    (C : Set (Position ι × Position ι)) (A : Set (Position ι))
    (hA : MeasurableSet A) (proposalFloor acceptanceFloor : ENNReal)
    (hleft : ∀ current ∈ C, ∀ z ∈ A,
      proposalFloor ≤ McmcLean.Kernel.isotropicGaussianPDF variance
        (z - current.1))
    (hright : ∀ current ∈ C, ∀ z ∈ A,
      proposalFloor ≤ McmcLean.Kernel.isotropicGaussianPDF variance
        (z - current.2))
    (haccept : ∀ current ∈ C, ∀ z ∈ Set.diagonal (Position ι),
      acceptanceFloor ≤ McmcLean.Kernel.coupledBothAcceptWeight
        (McmcLean.Kernel.densityAcceptance (positionBoltzmannWeight potential)
          (McmcLean.Kernel.randomWalkProposalDensity
            (McmcLean.Kernel.isotropicGaussianPDF variance))) current z) :
    McmcLean.Kernel.IsExactMeetingSmallSet
      (coupledHmcRwmhMixture p potential gradient ε L hpotential hgradient
        variance hvariance)
      C (((1 - p.1 : NNReal) : ENNReal) *
        (acceptanceFloor * (proposalFloor * volume A))) := by
  apply coupledHmcRwmhMixture_isExactMeetingSmallSet p potential gradient ε L
    hpotential hgradient variance hvariance C
    (acceptanceFloor * (proposalFloor * volume A))
  exact McmcLean.Kernel.coupledEuclideanGaussianRandomWalkMetropolisHastings_isExactMeetingSmallSet_of_floors
    (positionBoltzmannWeight potential) variance hvariance
    (measurable_positionBoltzmannWeight hpotential) C A hA proposalFloor
    acceptanceFloor hleft hright haccept

/-- Compact-ready localized version of the concrete mixture bound. The
acceptance floor is needed only on the portion of the diagonal over `A`. -/
theorem coupledHmcRwmhMixture_isExactMeetingSmallSet_of_localFloors
    (p : Set.Icc (0 : NNReal) 1)
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) (variance : ℝ≥0)
    (hvariance : variance ≠ 0)
    (C : Set (Position ι × Position ι)) (A : Set (Position ι))
    (hA : MeasurableSet A) (proposalFloor acceptanceFloor : ENNReal)
    (hleft : ∀ current ∈ C, ∀ z ∈ A,
      proposalFloor ≤ McmcLean.Kernel.isotropicGaussianPDF variance
        (z - current.1))
    (hright : ∀ current ∈ C, ∀ z ∈ A,
      proposalFloor ≤ McmcLean.Kernel.isotropicGaussianPDF variance
        (z - current.2))
    (haccept : ∀ current ∈ C,
      ∀ z ∈ McmcLean.Kernel.diagonalOver A,
      acceptanceFloor ≤ McmcLean.Kernel.coupledBothAcceptWeight
        (McmcLean.Kernel.densityAcceptance (positionBoltzmannWeight potential)
          (McmcLean.Kernel.randomWalkProposalDensity
            (McmcLean.Kernel.isotropicGaussianPDF variance))) current z) :
    McmcLean.Kernel.IsExactMeetingSmallSet
      (coupledHmcRwmhMixture p potential gradient ε L hpotential hgradient
        variance hvariance)
      C (hmcRwmhMeetingBound p acceptanceFloor proposalFloor (volume A)) := by
  apply coupledHmcRwmhMixture_isExactMeetingSmallSet p potential gradient ε L
    hpotential hgradient variance hvariance C
    (acceptanceFloor * (proposalFloor * volume A))
  exact McmcLean.Kernel.coupledEuclideanGaussianRandomWalkMetropolisHastings_isExactMeetingSmallSet_of_localFloors
    (positionBoltzmannWeight potential) variance hvariance
    (measurable_positionBoltzmannWeight hpotential) C A hA proposalFloor
    acceptanceFloor hleft hright haccept

/-- On nonempty compact current/proposal regions of positive volume, the
concrete coupled HMC/RWMH mixture has a strictly positive uniform one-step
exact-meeting constant. -/
theorem exists_pos_coupledHmcRwmhMixture_exactMeetingSmallSet_on_compact
    (p : Set.Icc (0 : NNReal) 1) (hp : p.1 < 1)
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Continuous potential)
    (hgradient : Measurable gradient) (variance : ℝ≥0)
    (hvariance : variance ≠ 0)
    {C : Set (Position ι × Position ι)} {A : Set (Position ι)}
    (hC : IsCompact C) (hCne : C.Nonempty)
    (hA : IsCompact A) (hAne : A.Nonempty)
    (hAmeas : MeasurableSet A) (hAvolume : 0 < volume A) :
    ∃ meetingBound : ENNReal, 0 < meetingBound ∧
      McmcLean.Kernel.IsExactMeetingSmallSet
        (coupledHmcRwmhMixture p potential gradient ε L hpotential.measurable
          hgradient variance hvariance) C meetingBound := by
  obtain ⟨proposalFloor, hproposalFloorPos, hleft, hright⟩ :=
    McmcLean.Kernel.exists_pos_euclideanGaussianProposalDensityFloor_on_compact
      variance hvariance hC hCne hA hAne
  obtain ⟨acceptanceFloor, hacceptanceFloorPos, hacceptance⟩ :=
    exists_pos_boltzmannBothAcceptanceFloor_on_compact hpotential
      hC hCne hA hAne
  refine ⟨hmcRwmhMeetingBound p acceptanceFloor proposalFloor (volume A),
    hmcRwmhMeetingBound_pos p hp hacceptanceFloorPos hproposalFloorPos
      hAvolume, ?_⟩
  apply coupledHmcRwmhMixture_isExactMeetingSmallSet_of_localFloors
    p potential gradient ε L hpotential.measurable hgradient variance
    hvariance C A hAmeas proposalFloor acceptanceFloor hleft hright
  intro current hcurrent proposal hproposal
  apply le_trans (hacceptance current hcurrent proposal.1 hproposal.2)
  exact (coupledBothAcceptWeight_diagonal_eq_boltzmannBothAcceptance
    potential variance hvariance current proposal hproposal.1).symm.le

/-- Faithful version of the concrete coupled mixture. Off the diagonal it is
the original HMC/RWMH coupling; on the diagonal it samples one verified
single-chain mixture transition and copies the output. -/
noncomputable def stickyCoupledHmcRwmhMixture
    (p : Set.Icc (0 : NNReal) 1)
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) (variance : ℝ≥0)
    (hvariance : variance ≠ 0) :
    Kernel (Position ι × Position ι) (Position ι × Position ι) :=
  McmcLean.Kernel.stickyCoupling
    (hmcRwmhMixture p potential gradient ε L hpotential hgradient variance
      hvariance)
    (coupledHmcRwmhMixture p potential gradient ε L hpotential hgradient
      variance hvariance)

instance stickyCoupledHmcRwmhMixture_isMarkovKernel
    (p : Set.Icc (0 : NNReal) 1)
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) (variance : ℝ≥0)
    (hvariance : variance ≠ 0) :
    IsMarkovKernel
      (stickyCoupledHmcRwmhMixture p potential gradient ε L hpotential
        hgradient variance hvariance) := by
  unfold stickyCoupledHmcRwmhMixture
  infer_instance

/-- The faithful modification retains the exact verified single-chain
HMC/RWMH mixture on both marginals. -/
theorem stickyCoupledHmcRwmhMixture_isCoupling
    (p : Set.Icc (0 : NNReal) 1)
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) (variance : ℝ≥0)
    (hvariance : variance ≠ 0) :
    McmcLean.Kernel.IsCoupling
      (stickyCoupledHmcRwmhMixture p potential gradient ε L hpotential
        hgradient variance hvariance)
      (hmcRwmhMixture p potential gradient ε L hpotential hgradient variance
        hvariance)
      (hmcRwmhMixture p potential gradient ε L hpotential hgradient variance
        hvariance) := by
  apply McmcLean.Kernel.stickyCoupling_isCoupling
  exact (coupledHmcRwmhMixture_isCoupling_and_invariant p potential gradient
    ε L hpotential hgradient variance hvariance).1

/-- The concrete sticky HMC/RWMH mixture is faithful after exact meeting. -/
theorem stickyCoupledHmcRwmhMixture_isFaithful
    (p : Set.Icc (0 : NNReal) 1)
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) (variance : ℝ≥0)
    (hvariance : variance ≠ 0) :
    McmcLean.Kernel.IsFaithful
      (stickyCoupledHmcRwmhMixture p potential gradient ε L hpotential
        hgradient variance hvariance) := by
  unfold stickyCoupledHmcRwmhMixture
  exact McmcLean.Kernel.stickyCoupling_isFaithful _ _

/-- Mixture-weighted combination of HMC and RWMH drift rates. -/
noncomputable def hmcRwmhDriftRate
    (p : Set.Icc (0 : NNReal) 1) (hmcRate rwmhRate : ENNReal) : ENNReal :=
  (p.1 : ENNReal) * hmcRate +
    (((1 - p.1 : NNReal) : NNReal) : ENNReal) * rwmhRate

/-- Mixture-weighted combination of HMC and RWMH drift allowances. -/
noncomputable def hmcRwmhDriftAllowance
    (p : Set.Icc (0 : NNReal) 1)
    (hmcAllowance rwmhAllowance : ENNReal) : ENNReal :=
  (p.1 : ENNReal) * hmcAllowance +
    (((1 - p.1 : NNReal) : NNReal) : ENNReal) * rwmhAllowance

/-- The drift-rate expression `λ₀` appearing in Xu et al., Theorem 4.1.
Here `γ` is the RWMH mixture probability. -/
noncomputable def xuTheorem41Lambda0
    (γ : Set.Ioo (0 : NNReal) 1) (hmcRate rwmhGrowth : ENNReal) : ENNReal :=
  (((1 - γ.1 : NNReal) : NNReal) : ENNReal) * hmcRate +
    (γ.1 : ENNReal) * (1 + rwmhGrowth)

/-- The HMC branch weight corresponding to the paper's RWMH probability
`γ`. -/
def xuTheorem41HmcWeight (γ : Set.Ioo (0 : NNReal) 1) :
    Set.Icc (0 : NNReal) 1 :=
  ⟨1 - γ.1, ⟨bot_le, tsub_le_self⟩⟩

/-- The additive drift allowance of the paper's HMC/RWMH mixture. -/
noncomputable def xuTheorem41DriftAllowance
    (γ : Set.Ioo (0 : NNReal) 1)
    (hmcAllowance rwmhGrowth : ENNReal) : ENNReal :=
  (((1 - γ.1 : NNReal) : NNReal) : ENNReal) * hmcAllowance +
    (γ.1 : ENNReal) * rwmhGrowth

/-- The paired contraction rate displayed in the final scalar hypothesis of
Xu et al., Theorem 4.1. -/
noncomputable def xuTheorem41PairedRate
    (γ : Set.Ioo (0 : NNReal) 1) (hmcRate hmcAllowance rwmhGrowth ell1 : ENNReal) :
    ENNReal :=
  xuTheorem41Lambda0 γ hmcRate rwmhGrowth +
    2 * xuTheorem41DriftAllowance γ hmcAllowance rwmhGrowth *
      (1 - xuTheorem41Lambda0 γ hmcRate rwmhGrowth)⁻¹ * (1 + ell1)⁻¹

/-- Every finite RWMH growth coefficient admits a sufficiently small positive
RWMH mixture probability `γ` for which `λ₀<1`, provided the HMC drift rate is
already below one. -/
theorem exists_gamma_xuTheorem41Lambda0_lt_one
    (hmcRate rwmhGrowth : ENNReal)
    (hhmcRate : hmcRate < 1) (hgrowthTop : rwmhGrowth ≠ ⊤) :
    ∃ γ : Set.Ioo (0 : NNReal) 1,
      xuTheorem41Lambda0 γ hmcRate rwmhGrowth < 1 := by
  have hhmcTop : hmcRate ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hhmcRate.le
  have hgap : 0 < 1 - hmcRate := tsub_pos_iff_lt.mpr hhmcRate
  have hfactorTop : 1 + rwmhGrowth ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hgrowthTop⟩
  have hinv : Filter.Tendsto (fun n : ℕ => ((n + 2 : ℕ) : ENNReal)⁻¹)
      Filter.atTop (nhds 0) :=
    ENNReal.tendsto_inv_nat_nhds_zero.comp
      (Filter.tendsto_add_atTop_nat 2)
  have hterm : Filter.Tendsto
      (fun n : ℕ => ((n + 2 : ℕ) : ENNReal)⁻¹ * (1 + rwmhGrowth))
      Filter.atTop (nhds 0) := by
    simpa only [zero_mul] using
      ENNReal.Tendsto.mul_const hinv (.inr hfactorTop)
  have heventually := hterm.eventually (Iio_mem_nhds hgap)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 heventually
  have hNterm := hN N le_rfl
  let denominator : NNReal := N + 2
  have hdenomPos : 0 < denominator := by
    dsimp only [denominator]
    exact_mod_cast (show 0 < N + 2 by omega)
  have hdenomOne : 1 < denominator := by
    dsimp only [denominator]
    exact_mod_cast (show 1 < N + 2 by omega)
  let gammaValue : NNReal := denominator⁻¹
  have hgammaPos : 0 < gammaValue := by
    dsimp only [gammaValue]
    exact inv_pos.mpr hdenomPos
  have hgammaLt : gammaValue < 1 := by
    dsimp only [gammaValue]
    exact inv_lt_one_of_one_lt₀ hdenomOne
  let γ : Set.Ioo (0 : NNReal) 1 := ⟨gammaValue, hgammaPos, hgammaLt⟩
  refine ⟨γ, ?_⟩
  have hgammaTerm : (γ.1 : ENNReal) * (1 + rwmhGrowth) < 1 - hmcRate := by
    change ((gammaValue : NNReal) : ENNReal) * (1 + rwmhGrowth) < 1 - hmcRate
    rw [show gammaValue = denominator⁻¹ by rfl,
      ENNReal.coe_inv hdenomPos.ne']
    have hdenominator : (denominator : ENNReal) = (N + 2 : ℕ) := by
      simp [denominator]
    rw [hdenominator]
    exact hNterm
  have hweighted :
      (((1 - γ.1 : NNReal) : NNReal) : ENNReal) * hmcRate ≤ hmcRate := by
    calc
      (((1 - γ.1 : NNReal) : NNReal) : ENNReal) * hmcRate ≤
          1 * hmcRate := by
        gcongr
        exact_mod_cast (tsub_le_self : 1 - γ.1 ≤ (1 : NNReal))
      _ = hmcRate := one_mul _
  have hsum : hmcRate + (γ.1 : ENNReal) * (1 + rwmhGrowth) < 1 := by
    calc
      hmcRate + (γ.1 : ENNReal) * (1 + rwmhGrowth) <
          hmcRate + (1 - hmcRate) :=
        ENNReal.add_lt_add_left hhmcTop hgammaTerm
      _ = 1 := add_tsub_cancel_of_le hhmcRate.le
  unfold xuTheorem41Lambda0
  exact lt_of_le_of_lt (add_le_add hweighted le_rfl) hsum

/-- Once the mixture rate `λ₀` is below one and both branch-growth constants
are finite, Xu et al.'s final paired scalar inequality holds at some finite
threshold `ℓ₁>1`. Thus this displayed condition is a selectable threshold,
not an independent analytic property of the kernels. -/
theorem exists_ell1_xuTheorem41PairedRate_lt_one
    (γ : Set.Ioo (0 : NNReal) 1)
    (hmcRate hmcAllowance rwmhGrowth : ENNReal)
    (hlambda : xuTheorem41Lambda0 γ hmcRate rwmhGrowth < 1)
    (hallowanceTop : hmcAllowance ≠ ⊤)
    (hgrowthTop : rwmhGrowth ≠ ⊤) :
    ∃ ell1 : ENNReal, 1 < ell1 ∧ ell1 ≠ ⊤ ∧
      xuTheorem41PairedRate γ hmcRate hmcAllowance rwmhGrowth ell1 < 1 := by
  let lambda0 := xuTheorem41Lambda0 γ hmcRate rwmhGrowth
  let allowance := xuTheorem41DriftAllowance γ hmcAllowance rwmhGrowth
  let correction := 2 * allowance * (1 - lambda0)⁻¹
  have hlambdaTop : lambda0 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hlambda.le
  have hallowanceFinite : allowance ≠ ⊤ := by
    dsimp only [allowance, xuTheorem41DriftAllowance]
    apply ENNReal.add_ne_top.2
    constructor
    · exact ENNReal.mul_ne_top (by finiteness) hallowanceTop
    · exact ENNReal.mul_ne_top (by finiteness) hgrowthTop
  have honeSub : 1 - lambda0 ≠ 0 :=
    ne_of_gt (tsub_pos_iff_lt.mpr hlambda)
  have hcorrectionTop : correction ≠ ⊤ := by
    dsimp only [correction]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) hallowanceFinite)
      (ENNReal.inv_ne_top.2 honeSub)
  have hinv : Filter.Tendsto (fun n : ℕ => (1 + (n : ENNReal))⁻¹)
      Filter.atTop (nhds 0) := by
    have h := ENNReal.tendsto_inv_nat_nhds_zero.comp
      (Filter.tendsto_add_atTop_nat 1)
    change Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ENNReal)⁻¹)
      Filter.atTop (nhds 0) at h
    simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, add_comm] using h
  have hcorrection : Filter.Tendsto
      (fun n : ℕ => correction * (1 + (n : ENNReal))⁻¹)
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul hinv (.inr hcorrectionTop)
  have hrate : Filter.Tendsto
      (fun n : ℕ => xuTheorem41PairedRate γ hmcRate hmcAllowance
        rwmhGrowth (n : ENNReal)) Filter.atTop (nhds lambda0) := by
    have hconst : Filter.Tendsto (fun _ : ℕ => lambda0)
        Filter.atTop (nhds lambda0) := tendsto_const_nhds
    have hadd := hconst.add hcorrection
    simpa only [xuTheorem41PairedRate, lambda0, correction, allowance,
      add_zero] using hadd
  have heventuallyRate := hrate.eventually (Iio_mem_nhds hlambda)
  have heventuallyTwo : ∀ᶠ n : ℕ in Filter.atTop, 2 ≤ n :=
    Filter.eventually_atTop.2 ⟨2, fun _ hn => hn⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (heventuallyRate.and heventuallyTwo)
  have hN' := hN N le_rfl
  refine ⟨(N : ENNReal), ?_, ENNReal.natCast_ne_top N, hN'.1⟩
  exact_mod_cast (show 1 < N by omega)

/-- The drift and integrability hypotheses stated in Xu et al., Theorem 4.1.
This structure deliberately records the paper's asymmetric HMC and RWMH
bounds verbatim; it is not replaced by a stronger symmetric branch premise. -/
structure XuTheorem41DriftAssumptions
    (γ : Set.Ioo (0 : NNReal) 1)
    (hmc rwmh : Kernel (Position ι) (Position ι))
    (initial : Measure (Position ι))
    (potential : Position ι → ℝ) (S : Set (Position ι)) where
  V : Position ι → ENNReal
  driftCoefficient : ENNReal
  driftAllowance : ENNReal
  growthCoefficient : ENNReal
  ell0 : ℝ
  ell1 : ENNReal
  measurable_V : Measurable V
  one_le_V : ∀ x, 1 ≤ V x
  driftCoefficient_pos : 0 < driftCoefficient
  driftCoefficient_lt_one : driftCoefficient < 1
  driftAllowance_ne_top : driftAllowance ≠ ∞
  growthCoefficient_pos : 0 < growthCoefficient
  hmc_drift : ∀ x, (∫⁻ y, V y ∂hmc x) ≤
    driftCoefficient * V x + driftAllowance
  rwmh_growth : ∀ x, (∫⁻ y, V y ∂rwmh x) ≤ growthCoefficient * (V x + 1)
  initial_moment : (∫⁻ x, V x ∂initial) ≠ ∞
  ell1_gt_one : 1 < ell1
  ell1_ne_top : ell1 ≠ ∞
  sublevel_subset : {x | V x ≤ ell1} ⊆ S ∩ {x | potential x ≤ ell0}
  ell0_above_inf : sInf (potential '' S) < ell0
  ell0_below_sup : ell0 < sSup (potential '' S)
  lambda0_lt_one : xuTheorem41Lambda0 γ driftCoefficient growthCoefficient < 1
  scalar_condition : xuTheorem41PairedRate γ driftCoefficient
    driftAllowance growthCoefficient ell1 < 1

omit [Fintype ι] in
/-- The HMC part of the paper's Theorem 4.1 hypothesis is an ordinary affine
drift certificate. -/
theorem XuTheorem41DriftAssumptions.hmc_hasAffineDrift
    {γ : Set.Ioo (0 : NNReal) 1}
    {hmc rwmh : Kernel (Position ι) (Position ι)}
    {initial : Measure (Position ι)} {potential : Position ι → ℝ}
    {S : Set (Position ι)}
    (h : XuTheorem41DriftAssumptions γ hmc rwmh initial potential S) :
    McmcLean.Kernel.HasAffineDrift hmc h.V h.driftCoefficient
      h.driftAllowance :=
  ⟨h.measurable_V, h.hmc_drift⟩

omit [Fintype ι] in
/-- The paper's RWMH growth premise `QV≤μ(V+1)` is the affine certificate
with rate and allowance both equal to `μ`. -/
theorem XuTheorem41DriftAssumptions.rwmh_hasAffineDrift
    {γ : Set.Ioo (0 : NNReal) 1}
    {hmc rwmh : Kernel (Position ι) (Position ι)}
    {initial : Measure (Position ι)} {potential : Position ι → ℝ}
    {S : Set (Position ι)}
    (h : XuTheorem41DriftAssumptions γ hmc rwmh initial potential S) :
    McmcLean.Kernel.HasAffineDrift rwmh h.V h.growthCoefficient
      h.growthCoefficient := by
  refine ⟨h.measurable_V, fun x => ?_⟩
  calc
    (∫⁻ y, h.V y ∂rwmh x) ≤ h.growthCoefficient * (h.V x + 1) :=
      h.rwmh_growth x
    _ = h.growthCoefficient * h.V x + h.growthCoefficient := by ring

omit [Fintype ι] in
/-- The asymmetric branch assumptions in Xu et al., Theorem 4.1 imply the
paper's affine drift bound for the actual HMC/RWMH mixture, with rate `λ₀`
and allowance `(1-γ)b+γμ`. -/
theorem XuTheorem41DriftAssumptions.mixture_hasAffineDrift
    {γ : Set.Ioo (0 : NNReal) 1}
    {hmc rwmh : Kernel (Position ι) (Position ι)}
    {initial : Measure (Position ι)} {potential : Position ι → ℝ}
    {S : Set (Position ι)}
    (h : XuTheorem41DriftAssumptions γ hmc rwmh initial potential S) :
    McmcLean.Kernel.HasAffineDrift
      (McmcLean.Kernel.mixture (xuTheorem41HmcWeight γ) hmc rwmh) h.V
      (xuTheorem41Lambda0 γ h.driftCoefficient h.growthCoefficient)
      (xuTheorem41DriftAllowance γ h.driftAllowance
        h.growthCoefficient) := by
  have hrwmh : McmcLean.Kernel.HasAffineDrift rwmh h.V
      (1 + h.growthCoefficient) h.growthCoefficient := by
    refine ⟨h.measurable_V, fun x => (h.rwmh_hasAffineDrift.2 x).trans ?_⟩
    gcongr
    exact le_add_left le_rfl
  have hmixed := h.hmc_hasAffineDrift.mixture
    (xuTheorem41HmcWeight γ) hmc rwmh hrwmh
  simpa only [xuTheorem41HmcWeight, xuTheorem41Lambda0,
    xuTheorem41DriftAllowance, tsub_tsub_cancel_of_le γ.property.2.le]
    using hmixed

omit [Fintype ι] in
/-- The strict finiteness of the paper's `λ₀` forces the RWMH growth
coefficient, and hence the mixture allowance, to be finite. -/
theorem XuTheorem41DriftAssumptions.mixtureAllowance_ne_top
    {γ : Set.Ioo (0 : NNReal) 1}
    {hmc rwmh : Kernel (Position ι) (Position ι)}
    {initial : Measure (Position ι)} {potential : Position ι → ℝ}
    {S : Set (Position ι)}
    (h : XuTheorem41DriftAssumptions γ hmc rwmh initial potential S) :
    xuTheorem41DriftAllowance γ h.driftAllowance h.growthCoefficient ≠ ∞ := by
  have hgamma0 : (γ.1 : ENNReal) ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr γ.property.1.ne'
  have hgrowthTop : h.growthCoefficient ≠ ∞ := by
    intro hgrowth
    have hlambdaTop :
        xuTheorem41Lambda0 γ h.driftCoefficient h.growthCoefficient = ∞ := by
      unfold xuTheorem41Lambda0
      rw [hgrowth]
      simp [hgamma0]
    exact (ne_top_of_le_ne_top ENNReal.one_ne_top h.lambda0_lt_one.le)
      hlambdaTop
  unfold xuTheorem41DriftAllowance
  exact ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top h.driftAllowance_ne_top,
      ENNReal.mul_ne_top ENNReal.coe_ne_top hgrowthTop⟩

omit [Fintype ι] in
/-- Any initial self-coupling inherits the finite additive paired Lyapunov
moment required for the geometric-tail prefactor. -/
theorem XuTheorem41DriftAssumptions.initialCoupling_pairedMoment_ne_top
    {γ : Set.Ioo (0 : NNReal) 1}
    {hmc rwmh : Kernel (Position ι) (Position ι)}
    {initial : Measure (Position ι)} {potential : Position ι → ℝ}
    {S : Set (Position ι)}
    (h : XuTheorem41DriftAssumptions γ hmc rwmh initial potential S)
    (initialCoupling : Measure (Position ι × Position ι))
    (hinitial : IsMeasureCoupling initialCoupling initial initial) :
    (∫⁻ q, McmcLean.Kernel.IsCoupling.pairedAdd h.V q ∂initialCoupling) ≠ ∞ := by
  have heq :
      (∫⁻ q, McmcLean.Kernel.IsCoupling.pairedAdd h.V q ∂initialCoupling) =
        (∫⁻ q, h.V q ∂initial) + (∫⁻ q, h.V q ∂initial) := by
    change (∫⁻ q, h.V q.1 + h.V q.2 ∂initialCoupling) = _
    have hfst : Measurable (fun q : Position ι × Position ι => h.V q.1) :=
      h.measurable_V.comp measurable_fst
    rw [lintegral_add_left hfst,
      McmcLean.Kernel.lintegral_fst_eq_of_isMeasureCoupling hinitial
        h.measurable_V,
      McmcLean.Kernel.lintegral_snd_eq_of_isMeasureCoupling hinitial
        h.measurable_V]
  rw [heq]
  exact ENNReal.add_ne_top.2 ⟨h.initial_moment, h.initial_moment⟩

omit [Fintype ι] in
/-- Xu et al.'s final scalar inequality supplies exactly the rate comparison,
paired affine-budget absorption, and strict subunit rate needed to lift the
mixture drift through any self-coupling. -/
theorem XuTheorem41DriftAssumptions.pairedRate_spec
    {γ : Set.Ioo (0 : NNReal) 1}
    {hmc rwmh : Kernel (Position ι) (Position ι)}
    {initial : Measure (Position ι)} {potential : Position ι → ℝ}
    {S : Set (Position ι)}
    (h : XuTheorem41DriftAssumptions γ hmc rwmh initial potential S) :
    let sourceRate := xuTheorem41Lambda0 γ h.driftCoefficient
      h.growthCoefficient
    let allowance := xuTheorem41DriftAllowance γ h.driftAllowance
      h.growthCoefficient
    let threshold := 1 + h.ell1
    let pairedRate := xuTheorem41PairedRate γ h.driftCoefficient
      h.driftAllowance h.growthCoefficient h.ell1
    sourceRate ≤ pairedRate ∧
      sourceRate * threshold + (allowance + allowance) ≤
        pairedRate * threshold ∧
      pairedRate < 1 := by
  dsimp only
  let sourceRate := xuTheorem41Lambda0 γ h.driftCoefficient
    h.growthCoefficient
  let allowance := xuTheorem41DriftAllowance γ h.driftAllowance
    h.growthCoefficient
  let threshold := 1 + h.ell1
  let pairedRate := xuTheorem41PairedRate γ h.driftCoefficient
    h.driftAllowance h.growthCoefficient h.ell1
  have hthreshold0 : threshold ≠ 0 := by
    dsimp only [threshold]
    exact ne_of_gt (zero_lt_one.trans_le (le_add_right le_rfl))
  have hthresholdTop : threshold ≠ ∞ := by
    dsimp only [threshold]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, h.ell1_ne_top⟩
  have hinv : 1 ≤ (1 - sourceRate)⁻¹ := by
    exact ENNReal.one_le_inv.2 tsub_le_self
  have hallowance : allowance + allowance ≤
      (allowance + allowance) * (1 - sourceRate)⁻¹ := by
    simpa only [one_mul, mul_one, mul_comm] using
      (mul_le_mul_left hinv (allowance + allowance))
  have habsorb : sourceRate * threshold + (allowance + allowance) ≤
      pairedRate * threshold := by
    calc
      sourceRate * threshold + (allowance + allowance) ≤
          sourceRate * threshold +
            (allowance + allowance) * (1 - sourceRate)⁻¹ :=
        add_le_add le_rfl hallowance
      _ = sourceRate * threshold +
          (allowance + allowance) * (1 - sourceRate)⁻¹ *
            (threshold⁻¹ * threshold) := by
        rw [ENNReal.inv_mul_cancel hthreshold0 hthresholdTop, mul_one]
      _ = pairedRate * threshold := by
        dsimp only [pairedRate, xuTheorem41PairedRate, sourceRate,
          allowance, threshold]
        ring
  refine ⟨?_, habsorb, ?_⟩
  · dsimp only [pairedRate, xuTheorem41PairedRate, sourceRate]
    exact le_add_right le_rfl
  · exact h.scalar_condition

omit [Fintype ι] in
/-- The paper's one-chain mixture drift lifts through any verified
self-coupling to paired additive geometric drift on the `1+ℓ₁` sublevel. -/
theorem XuTheorem41DriftAssumptions.coupling_hasGeometricDrift
    {γ : Set.Ioo (0 : NNReal) 1}
    {hmc rwmh : Kernel (Position ι) (Position ι)}
    {initial : Measure (Position ι)} {potential : Position ι → ℝ}
    {S : Set (Position ι)}
    (h : XuTheorem41DriftAssumptions γ hmc rwmh initial potential S)
    (coupled : Kernel (Position ι × Position ι) (Position ι × Position ι))
    (hcoupled : McmcLean.Kernel.IsCoupling coupled
      (McmcLean.Kernel.mixture (xuTheorem41HmcWeight γ) hmc rwmh)
      (McmcLean.Kernel.mixture (xuTheorem41HmcWeight γ) hmc rwmh)) :
    McmcLean.Kernel.HasGeometricDrift coupled
      (McmcLean.Kernel.IsCoupling.pairedAdd h.V)
      (McmcLean.Kernel.lyapunovSublevel
        (McmcLean.Kernel.IsCoupling.pairedAdd h.V) (1 + h.ell1))
      (xuTheorem41PairedRate γ h.driftCoefficient h.driftAllowance
        h.growthCoefficient h.ell1)
      (xuTheorem41DriftAllowance γ h.driftAllowance h.growthCoefficient +
        xuTheorem41DriftAllowance γ h.driftAllowance h.growthCoefficient) := by
  obtain ⟨hrates, hthreshold, _hrate⟩ := h.pairedRate_spec
  exact h.mixture_hasAffineDrift.coupling_pairedAdd_sublevel
    (McmcLean.Kernel.mixture (xuTheorem41HmcWeight γ) hmc rwmh)
    coupled hcoupled hrates hthreshold

omit [Fintype ι] in
/-- The paired `1+ℓ₁` Lyapunov sublevel lies in the paper's locally
contractive region `S × S`; the lower bound `V ≥ 1` accounts for the added
one in the threshold. -/
theorem XuTheorem41DriftAssumptions.pairedSublevel_subset
    {γ : Set.Ioo (0 : NNReal) 1}
    {hmc rwmh : Kernel (Position ι) (Position ι)}
    {initial : Measure (Position ι)} {potential : Position ι → ℝ}
    {S : Set (Position ι)}
    (h : XuTheorem41DriftAssumptions γ hmc rwmh initial potential S) :
    McmcLean.Kernel.lyapunovSublevel
        (McmcLean.Kernel.IsCoupling.pairedAdd h.V) (1 + h.ell1) ⊆
      S ×ˢ S := by
  intro q hq
  have hleft : h.V q.1 ≤ h.ell1 := by
    apply (ENNReal.add_le_add_iff_right ENNReal.one_ne_top).mp
    calc
      h.V q.1 + 1 ≤ h.V q.1 + h.V q.2 :=
        add_le_add le_rfl (h.one_le_V q.2)
      _ ≤ 1 + h.ell1 := hq
      _ = h.ell1 + 1 := add_comm _ _
  have hright : h.V q.2 ≤ h.ell1 := by
    apply (ENNReal.add_le_add_iff_right ENNReal.one_ne_top).mp
    calc
      h.V q.2 + 1 ≤ h.V q.2 + h.V q.1 :=
        add_le_add le_rfl (h.one_le_V q.1)
      _ = h.V q.1 + h.V q.2 := add_comm _ _
      _ ≤ 1 + h.ell1 := hq
      _ = h.ell1 + 1 := add_comm _ _
  exact ⟨(h.sublevel_subset hleft).1, (h.sublevel_subset hright).1⟩

/-- One-step relaxed accessibility of the HMC coupling on `S × S` transfers
to the full HMC/RWMH mixture on the paired drift sublevel. The minorization
constant is multiplied by the HMC branch weight `1-γ`. -/
theorem XuTheorem41DriftAssumptions.mixture_relaxedAccessibleFrom_pairedSublevel
    {γ : Set.Ioo (0 : NNReal) 1}
    {hmc rwmh : Kernel (Position ι) (Position ι)}
    {initial : Measure (Position ι)} {potential : Position ι → ℝ}
    {S : Set (Position ι)}
    (h : XuTheorem41DriftAssumptions γ hmc rwmh initial potential S)
    (coupledHmc coupledRwmh :
      Kernel (Position ι × Position ι) (Position ι × Position ι))
    {δ : ℝ} {entry : ENNReal}
    (haccess : McmcLean.Kernel.IsRelaxedMeetingAccessibleFrom
      coupledHmc S δ 1 entry) :
    McmcLean.Kernel.IsUniformlyAccessibleFrom
      (McmcLean.Kernel.mixture (xuTheorem41HmcWeight γ)
        coupledHmc coupledRwmh)
      (McmcLean.Kernel.lyapunovSublevel
        (McmcLean.Kernel.IsCoupling.pairedAdd h.V) (1 + h.ell1))
      (McmcLean.Kernel.relaxedDiagonal δ) 1
      ((((1 - γ.1 : NNReal) : NNReal) : ENNReal) * entry) := by
  have hlocal : McmcLean.Kernel.IsUniformlyAccessibleFrom coupledHmc
      (McmcLean.Kernel.lyapunovSublevel
        (McmcLean.Kernel.IsCoupling.pairedAdd h.V) (1 + h.ell1))
      (McmcLean.Kernel.relaxedDiagonal δ) 1 entry := by
    intro q hq
    exact haccess q (h.pairedSublevel_subset hq)
  simpa only [xuTheorem41HmcWeight] using
    hlocal.mixture_first_one (xuTheorem41HmcWeight γ)
      coupledHmc coupledRwmh
      (McmcLean.Kernel.measurableSet_relaxedDiagonal δ)

/-- Abstract geometric relaxed-meeting conclusion of Xu et al.'s drift
argument. Given verified branch couplings and positive one-step HMC relaxed
accessibility on `S × S`, the actual HMC/RWMH mixture path has a geometric
tail for entry into the relaxed diagonal. -/
theorem XuTheorem41DriftAssumptions.exists_geometric_relaxedPairMeetingTail
    {γ : Set.Ioo (0 : NNReal) 1}
    {hmc rwmh : Kernel (Position ι) (Position ι)}
    {initial : Measure (Position ι)} {potential : Position ι → ℝ}
    {S : Set (Position ι)}
    (h : XuTheorem41DriftAssumptions γ hmc rwmh initial potential S)
    (coupledHmc coupledRwmh :
      Kernel (Position ι × Position ι) (Position ι × Position ι))
    [IsMarkovKernel coupledHmc] [IsMarkovKernel coupledRwmh]
    (hhmc : McmcLean.Kernel.IsCoupling coupledHmc hmc hmc)
    (hrwmh : McmcLean.Kernel.IsCoupling coupledRwmh rwmh rwmh)
    {δ : ℝ} {hmcEntry : ENNReal} (hentryPos : 0 < hmcEntry)
    (haccess : McmcLean.Kernel.IsRelaxedMeetingAccessibleFrom
      coupledHmc S δ 1 hmcEntry)
    (hsubNonempty :
      (McmcLean.Kernel.lyapunovSublevel
        (McmcLean.Kernel.IsCoupling.pairedAdd h.V) (1 + h.ell1)).Nonempty)
    (x : Position ι × Position ι)
    (hx : x ∉ McmcLean.Kernel.relaxedDiagonal δ)
    (hVxTop : McmcLean.Kernel.IsCoupling.pairedAdd h.V x ≠ ∞) :
    ∃ scale contractionRate : ENNReal,
      scale ≠ 0 ∧ scale ≠ ∞ ∧ contractionRate < 1 ∧
        McmcLean.Kernel.meetingWeight
          (McmcLean.Kernel.IsCoupling.pairedAdd h.V) scale x ≠ ∞ ∧
          ∀ n : ℕ,
            McmcLean.Kernel.relaxedPairMeetingTail
                (McmcLean.Kernel.pathKernel
                  (McmcLean.Kernel.mixture (xuTheorem41HmcWeight γ)
                    coupledHmc coupledRwmh) x) δ n ≤
              contractionRate ^ n *
                McmcLean.Kernel.meetingWeight
                  (McmcLean.Kernel.IsCoupling.pairedAdd h.V) scale x := by
  let coupled := McmcLean.Kernel.mixture (xuTheorem41HmcWeight γ)
    coupledHmc coupledRwmh
  let Vpair := McmcLean.Kernel.IsCoupling.pairedAdd h.V
  let driftRate := xuTheorem41PairedRate γ h.driftCoefficient
    h.driftAllowance h.growthCoefficient h.ell1
  let allowance := xuTheorem41DriftAllowance γ h.driftAllowance
    h.growthCoefficient +
      xuTheorem41DriftAllowance γ h.driftAllowance h.growthCoefficient
  let threshold := 1 + h.ell1
  let entry := ((((1 - γ.1 : NNReal) : NNReal) : ENNReal) * hmcEntry)
  have hcoupled : McmcLean.Kernel.IsCoupling coupled
      (McmcLean.Kernel.mixture (xuTheorem41HmcWeight γ) hmc rwmh)
      (McmcLean.Kernel.mixture (xuTheorem41HmcWeight γ) hmc rwmh) := by
    dsimp only [coupled]
    exact McmcLean.Kernel.mixture_isCoupling
      (xuTheorem41HmcWeight γ) coupledHmc coupledRwmh hmc rwmh hmc rwmh
      hhmc hrwmh
  have hdrift : McmcLean.Kernel.HasGeometricDrift coupled Vpair
      (McmcLean.Kernel.lyapunovSublevel Vpair threshold)
      driftRate allowance := by
    simpa only [coupled, Vpair, driftRate, allowance, threshold] using
      h.coupling_hasGeometricDrift coupled hcoupled
  have hfullAccess := h.mixture_relaxedAccessibleFrom_pairedSublevel
    coupledHmc coupledRwmh haccess
  have hentry : ∀ q ∈ McmcLean.Kernel.lyapunovSublevel Vpair threshold,
      entry ≤ coupled q (McmcLean.Kernel.relaxedDiagonal δ) := by
    intro q hq
    simpa only [coupled, Vpair, threshold, entry, pow_one] using
      hfullAccess q hq
  have hentryPos' : 0 < entry := by
    have hweight : 0 < (1 - γ.1 : NNReal) :=
      tsub_pos_iff_lt.mpr γ.property.2
    dsimp only [entry]
    exact ENNReal.mul_pos (ENNReal.coe_ne_zero.mpr hweight.ne') hentryPos.ne'
  have hentryLe : entry ≤ 1 := by
    obtain ⟨q, hq⟩ := hsubNonempty
    calc
      entry ≤ coupled q (McmcLean.Kernel.relaxedDiagonal δ) := hentry q hq
      _ ≤ coupled q Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hthreshold0 : threshold ≠ 0 := by
    dsimp only [threshold]
    exact ne_of_gt (zero_lt_one.trans_le (le_add_right le_rfl))
  have hthresholdTop : threshold ≠ ∞ := by
    dsimp only [threshold]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, h.ell1_ne_top⟩
  have hdriftRate : driftRate < 1 := by
    dsimp only [driftRate]
    exact h.scalar_condition
  have hallowanceTop : allowance ≠ ∞ := by
    dsimp only [allowance]
    exact ENNReal.add_ne_top.2
      ⟨h.mixtureAllowance_ne_top, h.mixtureAllowance_ne_top⟩
  have hdriftBudgetTop : driftRate * threshold + allowance ≠ ∞ :=
    ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top
          hdriftRate.le) hthresholdTop, hallowanceTop⟩
  obtain ⟨scale, contractionRate, hscale0, hscaleTop, hrate,
      hweightTop, htail⟩ :=
    hdrift.exists_scale_rate_targetHittingTail_pathKernel_le coupled
      (McmcLean.Kernel.measurableSet_relaxedDiagonal δ) hentry hdriftRate
      hentryPos' hentryLe hthreshold0 hthresholdTop hdriftBudgetTop x hx
      hVxTop
  refine ⟨scale, contractionRate, hscale0, hscaleTop, hrate, hweightTop, ?_⟩
  intro n
  calc
    McmcLean.Kernel.relaxedPairMeetingTail
        (McmcLean.Kernel.pathKernel coupled x) δ n ≤
        McmcLean.Kernel.pathKernel coupled x
          (McmcLean.Kernel.returnFailureEvent
            (McmcLean.Kernel.relaxedDiagonal δ) n) := by
      apply measure_mono
      intro path hfail
      rw [McmcLean.Kernel.mem_returnFailureEvent_iff]
      intro j hj1 hjn hclose
      apply hfail
      exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hjn), hclose⟩⟩
    _ ≤ contractionRate ^ n *
        McmcLean.Kernel.meetingWeight Vpair scale x := htail n

/-- Assumptions 1 and 2 supply the local HMC premise of Xu's geometric-tail
theorem for the implemented maximal multinomial-HMC/Gaussian-RWMH mixture.
The selected positive integration window is exposed because the drift
certificate must concern the same concrete `ε,L` HMC transition. -/
theorem LocalStrongConvexity.exists_xuGeometricRelaxedTailWindow
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {curvatureRegion : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient curvatureRegion α)
    {K : Set (Position ι)} (hK : IsCompact K)
    (hKS : K ⊆ interior curvatureRegion)
    (hScompact : IsCompact curvatureRegion)
    (hSconvex : Convex ℝ curvatureRegion)
    (gamma : Set.Ioo (0 : NNReal) 1) (variance : NNReal)
    (hvariance : variance ≠ 0) (initial : Measure (Position ι)) :
    ∃ Tmin > 0, ∃ Tmax > Tmin, ∃ δ > 0,
      ∃ hmcEntry : ENNReal, 0 < hmcEntry ∧
        ∃ εbar > 0, ∀ {ε : ℝ} {L : ℕ},
          0 < ε → ε ≤ εbar →
          Tmin ≤ ε * (L : ℝ) → ε * (L : ℝ) ≤ Tmax →
          ∀ h : XuTheorem41DriftAssumptions gamma
            (standardPositionMultinomialHMC potential gradient ε L
              hreg.contDiff_two.continuous.measurable
              hreg.contDiff_one_gradient.continuous.measurable)
            (McmcLean.Kernel.euclideanGaussianRandomWalkMetropolisHastings
              (positionBoltzmannWeight potential) variance hvariance)
            initial potential K,
          (McmcLean.Kernel.lyapunovSublevel
            (McmcLean.Kernel.IsCoupling.pairedAdd h.V)
            (1 + h.ell1)).Nonempty →
          ∀ x : Position ι × Position ι,
            x ∉ McmcLean.Kernel.relaxedDiagonal δ →
            McmcLean.Kernel.IsCoupling.pairedAdd h.V x ≠ ∞ →
            ∃ scale contractionRate : ENNReal,
              scale ≠ 0 ∧ scale ≠ ∞ ∧ contractionRate < 1 ∧
                McmcLean.Kernel.meetingWeight
                  (McmcLean.Kernel.IsCoupling.pairedAdd h.V) scale x ≠ ∞ ∧
                ∀ n : ℕ,
                  McmcLean.Kernel.relaxedPairMeetingTail
                    (McmcLean.Kernel.pathKernel
                      (coupledHmcRwmhMixture
                        (xuTheorem41HmcWeight gamma) potential gradient ε L
                        hreg.contDiff_two.continuous.measurable
                        hreg.contDiff_one_gradient.continuous.measurable
                        variance hvariance) x)
                    δ n ≤
                  contractionRate ^ n *
                    McmcLean.Kernel.meetingWeight
                      (McmcLean.Kernel.IsCoupling.pairedAdd h.V) scale x := by
  obtain ⟨Tmin, hTmin, Tmax, hTmax, δ, hδ, hmcEntry, hentry,
      εbar, hεbar, haccess⟩ :=
    hconv.exists_maximalSharedMomentum_isRelaxedMeetingAccessible
      hreg hK hKS hScompact hSconvex
  refine ⟨Tmin, hTmin, Tmax, hTmax, δ, hδ, hmcEntry, hentry,
    εbar, hεbar, ?_⟩
  intro ε L hεpos hεbar' hTmin' hTmax' h hsubNonempty x hx hVxTop
  let hpotential : Measurable potential :=
    hreg.contDiff_two.continuous.measurable
  let hgradient : Measurable gradient :=
    hreg.contDiff_one_gradient.continuous.measurable
  letI : IsMarkovKernel
      (McmcLean.Kernel.coupledEuclideanGaussianRandomWalkMetropolisHastings
        (positionBoltzmannWeight potential) variance hvariance) :=
    McmcLean.Kernel.coupledEuclideanGaussianRandomWalkMetropolisHastings_isMarkov
      _ variance hvariance (measurable_positionBoltzmannWeight hpotential)
  have hout := h.exists_geometric_relaxedPairMeetingTail
    (maximalSharedMomentumCoupledPositionMultinomialHMC
      potential gradient ε L hpotential hgradient)
    (McmcLean.Kernel.coupledEuclideanGaussianRandomWalkMetropolisHastings
      (positionBoltzmannWeight potential) variance hvariance)
    (maximalSharedMomentumCoupledPositionMultinomialHMC_isCoupling
      potential gradient ε L hpotential hgradient)
    (McmcLean.Kernel.coupledEuclideanGaussianRandomWalkMetropolisHastings_isCoupling
      (positionBoltzmannWeight potential) variance hvariance
      (measurable_positionBoltzmannWeight hpotential))
    hentry (haccess hεpos hεbar' hTmin' hTmax') hsubNonempty x hx hVxTop
  simpa only [coupledHmcRwmhMixture] using hout

/-- Initial-law form of the abstract Xu et al. geometric-tail theorem. For
any probability coupling of the paper's initial law, its assumed finite
`V`-moment yields a finite constant `C₀` in the bound `C₀ κⁿ`. -/
theorem XuTheorem41DriftAssumptions.exists_geometric_relaxedPairMeetingTail_initial
    {γ : Set.Ioo (0 : NNReal) 1}
    {hmc rwmh : Kernel (Position ι) (Position ι)}
    [IsMarkovKernel hmc] [IsMarkovKernel rwmh]
    {initial : Measure (Position ι)} [IsProbabilityMeasure initial]
    {potential : Position ι → ℝ} {S : Set (Position ι)}
    (h : XuTheorem41DriftAssumptions γ hmc rwmh initial potential S)
    (initialCoupling : Measure (Position ι × Position ι))
    (hinitial : IsMeasureCoupling initialCoupling initial initial)
    (coupledHmc coupledRwmh :
      Kernel (Position ι × Position ι) (Position ι × Position ι))
    [IsMarkovKernel coupledHmc] [IsMarkovKernel coupledRwmh]
    (hhmc : McmcLean.Kernel.IsCoupling coupledHmc hmc hmc)
    (hrwmh : McmcLean.Kernel.IsCoupling coupledRwmh rwmh rwmh)
    {δ : ℝ} {hmcEntry : ENNReal} (hentryPos : 0 < hmcEntry)
    (haccess : McmcLean.Kernel.IsRelaxedMeetingAccessibleFrom
      coupledHmc S δ 1 hmcEntry)
    (hsubNonempty :
      (McmcLean.Kernel.lyapunovSublevel
        (McmcLean.Kernel.IsCoupling.pairedAdd h.V) (1 + h.ell1)).Nonempty) :
    ∃ C₀ contractionRate : ENNReal,
      C₀ ≠ ∞ ∧ contractionRate < 1 ∧
        ∀ n : ℕ,
          McmcLean.Kernel.relaxedPairMeetingTail
              (McmcLean.Kernel.pathLaw
                (McmcLean.Kernel.laggedInitialMeasure initialCoupling
                  (McmcLean.Kernel.mixture (xuTheorem41HmcWeight γ)
                    hmc rwmh))
                (McmcLean.Kernel.mixture (xuTheorem41HmcWeight γ)
                  coupledHmc coupledRwmh)) δ n ≤
            C₀ * contractionRate ^ n := by
  letI : IsProbabilityMeasure initialCoupling := hinitial.isProbabilityMeasure
  let transition := McmcLean.Kernel.mixture (xuTheorem41HmcWeight γ) hmc rwmh
  let laggedInitial := McmcLean.Kernel.laggedInitialMeasure
    initialCoupling transition
  letI : IsProbabilityMeasure laggedInitial := by
    dsimp only [laggedInitial, transition]
    infer_instance
  let coupled := McmcLean.Kernel.mixture (xuTheorem41HmcWeight γ)
    coupledHmc coupledRwmh
  let Vpair := McmcLean.Kernel.IsCoupling.pairedAdd h.V
  let driftRate := xuTheorem41PairedRate γ h.driftCoefficient
    h.driftAllowance h.growthCoefficient h.ell1
  let allowance := xuTheorem41DriftAllowance γ h.driftAllowance
    h.growthCoefficient +
      xuTheorem41DriftAllowance γ h.driftAllowance h.growthCoefficient
  let threshold := 1 + h.ell1
  let entry := ((((1 - γ.1 : NNReal) : NNReal) : ENNReal) * hmcEntry)
  have hcoupled : McmcLean.Kernel.IsCoupling coupled
      (McmcLean.Kernel.mixture (xuTheorem41HmcWeight γ) hmc rwmh)
      (McmcLean.Kernel.mixture (xuTheorem41HmcWeight γ) hmc rwmh) := by
    dsimp only [coupled]
    exact McmcLean.Kernel.mixture_isCoupling
      (xuTheorem41HmcWeight γ) coupledHmc coupledRwmh hmc rwmh hmc rwmh
      hhmc hrwmh
  have hdrift : McmcLean.Kernel.HasGeometricDrift coupled Vpair
      (McmcLean.Kernel.lyapunovSublevel Vpair threshold)
      driftRate allowance := by
    simpa only [coupled, Vpair, driftRate, allowance, threshold] using
      h.coupling_hasGeometricDrift coupled hcoupled
  have hfullAccess := h.mixture_relaxedAccessibleFrom_pairedSublevel
    coupledHmc coupledRwmh haccess
  have hentry : ∀ q ∈ McmcLean.Kernel.lyapunovSublevel Vpair threshold,
      entry ≤ coupled q (McmcLean.Kernel.relaxedDiagonal δ) := by
    intro q hq
    simpa only [coupled, Vpair, threshold, entry, pow_one] using
      hfullAccess q hq
  have hentryPos' : 0 < entry := by
    have hweight : 0 < (1 - γ.1 : NNReal) :=
      tsub_pos_iff_lt.mpr γ.property.2
    dsimp only [entry]
    exact ENNReal.mul_pos (ENNReal.coe_ne_zero.mpr hweight.ne') hentryPos.ne'
  have hentryLe : entry ≤ 1 := by
    obtain ⟨q, hq⟩ := hsubNonempty
    calc
      entry ≤ coupled q (McmcLean.Kernel.relaxedDiagonal δ) := hentry q hq
      _ ≤ coupled q Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hthreshold0 : threshold ≠ 0 := by
    dsimp only [threshold]
    exact ne_of_gt (zero_lt_one.trans_le (le_add_right le_rfl))
  have hthresholdTop : threshold ≠ ∞ := by
    dsimp only [threshold]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, h.ell1_ne_top⟩
  have hdriftRate : driftRate < 1 := by
    dsimp only [driftRate]
    exact h.scalar_condition
  have hallowanceTop : allowance ≠ ∞ := by
    dsimp only [allowance]
    exact ENNReal.add_ne_top.2
      ⟨h.mixtureAllowance_ne_top, h.mixtureAllowance_ne_top⟩
  have hdriftBudgetTop : driftRate * threshold + allowance ≠ ∞ :=
    ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top
          hdriftRate.le) hthresholdTop, hallowanceTop⟩
  obtain ⟨scale, contractionRate, hscale0, hscaleTop, hrate, htail⟩ :=
    hdrift.exists_scale_rate_relaxedPairMeetingTail_pathLaw_le
      laggedInitial coupled hentry hdriftRate hentryPos' hentryLe
      hthreshold0 hthresholdTop hdriftBudgetTop
  let C₀ := ∫⁻ q in (McmcLean.Kernel.relaxedDiagonal δ)ᶜ,
    McmcLean.Kernel.meetingWeight Vpair scale q ∂laggedInitial
  have hsourceRateTop :
      xuTheorem41Lambda0 γ h.driftCoefficient h.growthCoefficient ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top h.lambda0_lt_one.le
  have hmomentTop : (∫⁻ q, Vpair q ∂laggedInitial) ≠ ∞ := by
    dsimp only [Vpair, laggedInitial, transition]
    exact h.mixture_hasAffineDrift.laggedInitialMeasure_pairedMoment_ne_top
      (McmcLean.Kernel.mixture (xuTheorem41HmcWeight γ) hmc rwmh)
      initial initialCoupling hinitial h.initial_moment hsourceRateTop
      h.mixtureAllowance_ne_top
  have hfullWeightTop :
      (∫⁻ q, McmcLean.Kernel.meetingWeight Vpair scale q
        ∂laggedInitial) ≠ ∞ := by
    change (∫⁻ q, 1 + scale * Vpair q ∂laggedInitial) ≠ ∞
    rw [lintegral_add_left measurable_const,
      lintegral_const, measure_univ, one_mul,
      lintegral_const_mul _ hdrift.1]
    exact ENNReal.add_ne_top.2
      ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top hscaleTop hmomentTop⟩
  have hC₀Top : C₀ ≠ ∞ := by
    apply ne_top_of_le_ne_top hfullWeightTop
    exact setLIntegral_le_lintegral _ _
  refine ⟨C₀, contractionRate, hC₀Top, hrate, ?_⟩
  intro n
  simpa only [C₀, mul_comm] using htail n

/-- Exact lag-one meeting-time closure for the paper's drift assumptions.
The paired Markov state is `(Xₙ,Yₙ₋₁)`, initialized by
`laggedInitialMeasure`; hence its ordinary exact diagonal is precisely the
paper's lag-one equality event.  The additional small-set premise makes
explicit the bridge that must turn Proposition 4.1's relaxed entry into an
exact RWMH meeting opportunity. -/
theorem XuTheorem41DriftAssumptions.exists_geometric_exactLagOneMeetingTail_initial
    {γ : Set.Ioo (0 : NNReal) 1}
    {hmc rwmh : Kernel (Position ι) (Position ι)}
    [IsMarkovKernel hmc] [IsMarkovKernel rwmh]
    {initial : Measure (Position ι)} [IsProbabilityMeasure initial]
    {potential : Position ι → ℝ} {S : Set (Position ι)}
    (h : XuTheorem41DriftAssumptions γ hmc rwmh initial potential S)
    (initialCoupling : Measure (Position ι × Position ι))
    (hinitial : IsMeasureCoupling initialCoupling initial initial)
    (coupled : Kernel (Position ι × Position ι)
      (Position ι × Position ι)) [IsMarkovKernel coupled]
    (hcoupled : McmcLean.Kernel.IsCoupling coupled
      (McmcLean.Kernel.mixture (xuTheorem41HmcWeight γ) hmc rwmh)
      (McmcLean.Kernel.mixture (xuTheorem41HmcWeight γ) hmc rwmh))
    {meetingBound : ENNReal} (hmeetingPos : 0 < meetingBound)
    (hmeeting : McmcLean.Kernel.IsExactMeetingSmallSet
      coupled
      (McmcLean.Kernel.lyapunovSublevel
        (McmcLean.Kernel.IsCoupling.pairedAdd h.V) (1 + h.ell1))
      meetingBound)
    (hfaithful : McmcLean.Kernel.IsFaithful coupled)
    (hsubNonempty :
      (McmcLean.Kernel.lyapunovSublevel
        (McmcLean.Kernel.IsCoupling.pairedAdd h.V)
        (1 + h.ell1)).Nonempty) :
    ∃ C₀ contractionRate : ENNReal,
      C₀ ≠ ∞ ∧ contractionRate < 1 ∧
        ∀ n : ℕ,
          McmcLean.Kernel.exactMeetingTail
              (McmcLean.Kernel.pathLaw
                (McmcLean.Kernel.laggedInitialMeasure initialCoupling
                  (McmcLean.Kernel.mixture (xuTheorem41HmcWeight γ)
                    hmc rwmh))
                coupled) n ≤
            C₀ * contractionRate ^ n := by
  letI : IsProbabilityMeasure initialCoupling := hinitial.isProbabilityMeasure
  let transition := McmcLean.Kernel.mixture
    (xuTheorem41HmcWeight γ) hmc rwmh
  let laggedInitial := McmcLean.Kernel.laggedInitialMeasure
    initialCoupling transition
  letI : IsProbabilityMeasure laggedInitial := by
    dsimp only [laggedInitial, transition]
    infer_instance
  let Vpair := McmcLean.Kernel.IsCoupling.pairedAdd h.V
  let driftRate := xuTheorem41PairedRate γ h.driftCoefficient
    h.driftAllowance h.growthCoefficient h.ell1
  let allowance := xuTheorem41DriftAllowance γ h.driftAllowance
    h.growthCoefficient +
      xuTheorem41DriftAllowance γ h.driftAllowance h.growthCoefficient
  let threshold := 1 + h.ell1
  have hcoupled' : McmcLean.Kernel.IsCoupling coupled transition transition := by
    simpa only [transition] using hcoupled
  have hdrift : McmcLean.Kernel.HasGeometricDrift coupled Vpair
      (McmcLean.Kernel.lyapunovSublevel Vpair threshold)
      driftRate allowance := by
    simpa only [transition, Vpair, driftRate, allowance, threshold]
      using h.coupling_hasGeometricDrift coupled hcoupled'
  have hmeeting' : McmcLean.Kernel.IsExactMeetingSmallSet coupled
      (McmcLean.Kernel.lyapunovSublevel Vpair threshold) meetingBound := by
    simpa only [Vpair, threshold] using hmeeting
  have hfaithful' : McmcLean.Kernel.IsFaithful coupled := by
    exact hfaithful
  have hmeetingLe : meetingBound ≤ 1 := by
    obtain ⟨q, hq⟩ := hsubNonempty
    calc
      meetingBound ≤ coupled q (Set.diagonal (Position ι)) :=
        hmeeting' q (by simpa only [Vpair, threshold] using hq)
      _ ≤ coupled q Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hthreshold0 : threshold ≠ 0 := by
    dsimp only [threshold]
    exact ne_of_gt (zero_lt_one.trans_le (le_add_right le_rfl))
  have hthresholdTop : threshold ≠ ∞ := by
    dsimp only [threshold]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, h.ell1_ne_top⟩
  have hdriftRate : driftRate < 1 := by
    dsimp only [driftRate]
    exact h.scalar_condition
  have hallowanceTop : allowance ≠ ∞ := by
    dsimp only [allowance]
    exact ENNReal.add_ne_top.2
      ⟨h.mixtureAllowance_ne_top, h.mixtureAllowance_ne_top⟩
  have hdriftBudgetTop : driftRate * threshold + allowance ≠ ∞ :=
    ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top
          hdriftRate.le) hthresholdTop, hallowanceTop⟩
  obtain ⟨scale, contractionRate, hscale0, hscaleTop, hrate, htail⟩ :=
    hdrift.exists_scale_rate_exactMeetingTail_pathLaw_le
      laggedInitial coupled hmeeting' hfaithful' hdriftRate hmeetingPos
      hmeetingLe hthreshold0 hthresholdTop hdriftBudgetTop
  let C₀ := McmcLean.Kernel.weightedOffDiagonalMassAtTime
    laggedInitial coupled Vpair scale 0
  have hsourceRateTop :
      xuTheorem41Lambda0 γ h.driftCoefficient h.growthCoefficient ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top h.lambda0_lt_one.le
  have hmomentTop : (∫⁻ q, Vpair q ∂laggedInitial) ≠ ∞ := by
    dsimp only [Vpair, laggedInitial, transition]
    exact h.mixture_hasAffineDrift.laggedInitialMeasure_pairedMoment_ne_top
      (McmcLean.Kernel.mixture (xuTheorem41HmcWeight γ) hmc rwmh)
      initial initialCoupling hinitial h.initial_moment hsourceRateTop
      h.mixtureAllowance_ne_top
  have hfullWeightTop :
      (∫⁻ q, McmcLean.Kernel.meetingWeight Vpair scale q
        ∂laggedInitial) ≠ ∞ := by
    change (∫⁻ q, 1 + scale * Vpair q ∂laggedInitial) ≠ ∞
    rw [lintegral_add_left measurable_const,
      lintegral_const, measure_univ, one_mul,
      lintegral_const_mul _ hdrift.1]
    exact ENNReal.add_ne_top.2
      ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top hscaleTop hmomentTop⟩
  have hC₀Top : C₀ ≠ ∞ := by
    dsimp only [C₀, McmcLean.Kernel.weightedOffDiagonalMassAtTime]
    rw [McmcLean.Kernel.lawAtTime_zero]
    apply ne_top_of_le_ne_top hfullWeightTop
    exact setLIntegral_le_lintegral _ _
  refine ⟨C₀, contractionRate, hC₀Top, hrate, ?_⟩
  intro n
  simpa only [C₀, laggedInitial, transition, mul_comm] using htail n

/-- A convex combination of two strict subunit drift rates is strict
subunit, including endpoint mixture weights. -/
theorem hmcRwmhDriftRate_lt_one
    (p : Set.Icc (0 : NNReal) 1) {hmcRate rwmhRate : ENNReal}
    (hhmc : hmcRate < 1) (hrwmh : rwmhRate < 1) :
    hmcRwmhDriftRate p hmcRate rwmhRate < 1 := by
  have hweights : (p.1 : ENNReal) +
      (((1 - p.1 : NNReal) : NNReal) : ENNReal) = 1 := by
    exact_mod_cast add_tsub_cancel_of_le p.property.2
  calc
    hmcRwmhDriftRate p hmcRate rwmhRate ≤
        (p.1 : ENNReal) * max hmcRate rwmhRate +
          (((1 - p.1 : NNReal) : NNReal) : ENNReal) *
            max hmcRate rwmhRate := by
      unfold hmcRwmhDriftRate
      gcongr
      · exact le_max_left _ _
      · exact le_max_right _ _
    _ = max hmcRate rwmhRate := by
      rw [← add_mul, hweights, one_mul]
    _ < 1 := max_lt hhmc hrwmh

/-- Component drift certificates combine into a drift certificate for the
concrete sticky HMC/RWMH coupling. The only additional obligation is the same
bound for the synchronous rows used after the chains have met. -/
theorem stickyCoupledHmcRwmhMixture_hasGeometricDrift_of_components
    (p : Set.Icc (0 : NNReal) 1)
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) (variance : ℝ≥0)
    (hvariance : variance ≠ 0)
    {V : Position ι × Position ι → ENNReal}
    {C : Set (Position ι × Position ι)}
    {hmcRate hmcAllowance rwmhRate rwmhAllowance : ENNReal}
    (hhmc : McmcLean.Kernel.HasGeometricDrift
      (maximalSharedMomentumCoupledPositionMultinomialHMC
        potential gradient ε L hpotential hgradient)
      V C hmcRate hmcAllowance)
    (hrwmh : McmcLean.Kernel.HasGeometricDrift
      (McmcLean.Kernel.coupledEuclideanGaussianRandomWalkMetropolisHastings
        (positionBoltzmannWeight potential) variance hvariance)
      V C rwmhRate rwmhAllowance)
    (hdiagonal : ∀ x ∈ Set.diagonal (Position ι),
      (∫⁻ y, V y ∂McmcLean.Kernel.synchronousCoupling
        (hmcRwmhMixture p potential gradient ε L hpotential hgradient
          variance hvariance) x) ≤
        hmcRwmhDriftRate p hmcRate rwmhRate * V x +
          C.indicator (fun _ =>
            hmcRwmhDriftAllowance p hmcAllowance rwmhAllowance) x) :
    McmcLean.Kernel.HasGeometricDrift
      (stickyCoupledHmcRwmhMixture p potential gradient ε L hpotential
        hgradient variance hvariance)
      V C (hmcRwmhDriftRate p hmcRate rwmhRate)
        (hmcRwmhDriftAllowance p hmcAllowance rwmhAllowance) := by
  have hmixture := McmcLean.Kernel.HasGeometricDrift.mixture p
    (maximalSharedMomentumCoupledPositionMultinomialHMC
      potential gradient ε L hpotential hgradient)
    (McmcLean.Kernel.coupledEuclideanGaussianRandomWalkMetropolisHastings
      (positionBoltzmannWeight potential) variance hvariance)
    hhmc hrwmh
  unfold stickyCoupledHmcRwmhMixture coupledHmcRwmhMixture
  exact hmixture.stickyCoupling
    (hmcRwmhMixture p potential gradient ε L hpotential hgradient variance
      hvariance)
    (McmcLean.Kernel.mixture p
      (maximalSharedMomentumCoupledPositionMultinomialHMC
        potential gradient ε L hpotential hgradient)
      (McmcLean.Kernel.coupledEuclideanGaussianRandomWalkMetropolisHastings
        (positionBoltzmannWeight potential) variance hvariance))
    hdiagonal

/-- For the standard additive paired Lyapunov function, correct marginals
discharge the synchronous diagonal-row obligation automatically. -/
theorem stickyCoupledHmcRwmhMixture_hasGeometricDrift_pairedAdd_of_components
    (p : Set.Icc (0 : NNReal) 1)
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) (variance : ℝ≥0)
    (hvariance : variance ≠ 0)
    {v : Position ι → ENNReal} (hv : Measurable v)
    {C : Set (Position ι × Position ι)}
    {hmcRate hmcAllowance rwmhRate rwmhAllowance : ENNReal}
    (hhmc : McmcLean.Kernel.HasGeometricDrift
      (maximalSharedMomentumCoupledPositionMultinomialHMC
        potential gradient ε L hpotential hgradient)
      (McmcLean.Kernel.IsCoupling.pairedAdd v) C hmcRate hmcAllowance)
    (hrwmh : McmcLean.Kernel.HasGeometricDrift
      (McmcLean.Kernel.coupledEuclideanGaussianRandomWalkMetropolisHastings
        (positionBoltzmannWeight potential) variance hvariance)
      (McmcLean.Kernel.IsCoupling.pairedAdd v) C rwmhRate rwmhAllowance) :
    McmcLean.Kernel.HasGeometricDrift
      (stickyCoupledHmcRwmhMixture p potential gradient ε L hpotential
        hgradient variance hvariance)
      (McmcLean.Kernel.IsCoupling.pairedAdd v) C
      (hmcRwmhDriftRate p hmcRate rwmhRate)
      (hmcRwmhDriftAllowance p hmcAllowance rwmhAllowance) := by
  have hmixture := McmcLean.Kernel.HasGeometricDrift.mixture p
    (maximalSharedMomentumCoupledPositionMultinomialHMC
      potential gradient ε L hpotential hgradient)
    (McmcLean.Kernel.coupledEuclideanGaussianRandomWalkMetropolisHastings
      (positionBoltzmannWeight potential) variance hvariance)
    hhmc hrwmh
  unfold stickyCoupledHmcRwmhMixture
  apply hmixture.stickyCoupling_pairedAdd
    (hmcRwmhMixture p potential gradient ε L hpotential hgradient variance
      hvariance)
  · exact (coupledHmcRwmhMixture_isCoupling_and_invariant p potential gradient
      ε L hpotential hgradient variance hvariance).1
  · exact hv

/-- Ordinary single-chain affine drift certificates lift through the verified
HMC and RWMH couplings, then combine into drift for the concrete sticky
mixture. -/
theorem stickyCoupledHmcRwmhMixture_hasGeometricDrift_of_singleChain
    (p : Set.Icc (0 : NNReal) 1)
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) (variance : ℝ≥0)
    (hvariance : variance ≠ 0)
    {v : Position ι → ENNReal}
    {threshold hmcSourceRate hmcSourceAllowance hmcPairedRate
      rwmhSourceRate rwmhSourceAllowance rwmhPairedRate : ENNReal}
    (hhmc : McmcLean.Kernel.HasAffineDrift
      (standardPositionMultinomialHMC potential gradient ε L
        hpotential hgradient)
      v hmcSourceRate hmcSourceAllowance)
    (hrwmh : McmcLean.Kernel.HasAffineDrift
      (McmcLean.Kernel.euclideanGaussianRandomWalkMetropolisHastings
        (positionBoltzmannWeight potential) variance hvariance)
      v rwmhSourceRate rwmhSourceAllowance)
    (hhmcRates : hmcSourceRate ≤ hmcPairedRate)
    (hhmcThreshold :
      hmcSourceRate * threshold +
          (hmcSourceAllowance + hmcSourceAllowance) ≤
        hmcPairedRate * threshold)
    (hrwmhRates : rwmhSourceRate ≤ rwmhPairedRate)
    (hrwmhThreshold :
      rwmhSourceRate * threshold +
          (rwmhSourceAllowance + rwmhSourceAllowance) ≤
        rwmhPairedRate * threshold) :
    McmcLean.Kernel.HasGeometricDrift
      (stickyCoupledHmcRwmhMixture p potential gradient ε L hpotential
        hgradient variance hvariance)
      (McmcLean.Kernel.IsCoupling.pairedAdd v)
      (McmcLean.Kernel.lyapunovSublevel
        (McmcLean.Kernel.IsCoupling.pairedAdd v) threshold)
      (hmcRwmhDriftRate p hmcPairedRate rwmhPairedRate)
      (hmcRwmhDriftAllowance p
        (hmcSourceAllowance + hmcSourceAllowance)
        (rwmhSourceAllowance + rwmhSourceAllowance)) := by
  have hhmcCoupled := hhmc.coupling_pairedAdd_sublevel
    (standardPositionMultinomialHMC potential gradient ε L
      hpotential hgradient)
    (maximalSharedMomentumCoupledPositionMultinomialHMC
      potential gradient ε L hpotential hgradient)
    (maximalSharedMomentumCoupledPositionMultinomialHMC_isCoupling
      potential gradient ε L hpotential hgradient)
    hhmcRates hhmcThreshold
  have hrwmhCoupled := hrwmh.coupling_pairedAdd_sublevel
    (McmcLean.Kernel.euclideanGaussianRandomWalkMetropolisHastings
      (positionBoltzmannWeight potential) variance hvariance)
    (McmcLean.Kernel.coupledEuclideanGaussianRandomWalkMetropolisHastings
      (positionBoltzmannWeight potential) variance hvariance)
    (McmcLean.Kernel.coupledEuclideanGaussianRandomWalkMetropolisHastings_isCoupling
      (positionBoltzmannWeight potential) variance hvariance
      (measurable_positionBoltzmannWeight hpotential))
    hrwmhRates hrwmhThreshold
  exact stickyCoupledHmcRwmhMixture_hasGeometricDrift_pairedAdd_of_components
    p potential gradient ε L hpotential hgradient variance hvariance hhmc.1
    hhmcCoupled hrwmhCoupled

/-- The faithful concrete mixture retains the strictly positive compact
exact-meeting small-set constant proved for the original coupling. -/
theorem exists_pos_stickyCoupledHmcRwmhMixture_exactMeetingSmallSet_on_compact
    (p : Set.Icc (0 : NNReal) 1) (hp : p.1 < 1)
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Continuous potential)
    (hgradient : Measurable gradient) (variance : ℝ≥0)
    (hvariance : variance ≠ 0)
    {C : Set (Position ι × Position ι)} {A : Set (Position ι)}
    (hC : IsCompact C) (hCne : C.Nonempty)
    (hA : IsCompact A) (hAne : A.Nonempty)
    (hAmeas : MeasurableSet A) (hAvolume : 0 < volume A) :
    ∃ meetingBound : ENNReal, 0 < meetingBound ∧
      McmcLean.Kernel.IsExactMeetingSmallSet
        (stickyCoupledHmcRwmhMixture p potential gradient ε L
          hpotential.measurable hgradient variance hvariance) C meetingBound := by
  obtain ⟨meetingBound, hboundPos, hsmall⟩ :=
    exists_pos_coupledHmcRwmhMixture_exactMeetingSmallSet_on_compact
      p hp potential gradient ε L hpotential hgradient variance hvariance
      hC hCne hA hAne hAmeas hAvolume
  exact ⟨meetingBound, hboundPos,
    McmcLean.Kernel.stickyCoupling_isExactMeetingSmallSet _ _ hsmall⟩

/-- Concrete exact lag-one Theorem-4.1 closure for the verified sticky
multinomial-HMC/Gaussian-RWMH mixture.  Once the paper's drift assumptions are
instantiated and their paired sublevel is compact and nonempty, the existing
localized Gaussian RWMH argument supplies the positive exact-meeting premise
needed by `exists_geometric_exactLagOneMeetingTail_initial`. -/
theorem XuTheorem41DriftAssumptions.exists_geometric_exactLagOneMeetingTail_stickyHmcRwmh
    (γ : Set.Ioo (0 : NNReal) 1)
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Continuous potential)
    (hgradient : Measurable gradient) (variance : ℝ≥0)
    (hvariance : variance ≠ 0)
    (initial : Measure (Position ι)) [IsProbabilityMeasure initial]
    (S : Set (Position ι))
    (h : XuTheorem41DriftAssumptions γ
      (standardPositionMultinomialHMC potential gradient ε L
        hpotential.measurable hgradient)
      (McmcLean.Kernel.euclideanGaussianRandomWalkMetropolisHastings
        (positionBoltzmannWeight potential) variance hvariance)
      initial potential S)
    (initialCoupling : Measure (Position ι × Position ι))
    (hinitial : IsMeasureCoupling initialCoupling initial initial)
    (hsubCompact : IsCompact
      (McmcLean.Kernel.lyapunovSublevel
        (McmcLean.Kernel.IsCoupling.pairedAdd h.V) (1 + h.ell1)))
    (hsubNonempty :
      (McmcLean.Kernel.lyapunovSublevel
        (McmcLean.Kernel.IsCoupling.pairedAdd h.V)
        (1 + h.ell1)).Nonempty)
    {A : Set (Position ι)} (hA : IsCompact A) (hAne : A.Nonempty)
    (hAmeas : MeasurableSet A) (hAvolume : 0 < volume A) :
    ∃ C₀ contractionRate : ENNReal,
      C₀ ≠ ∞ ∧ contractionRate < 1 ∧
        ∀ n : ℕ,
          McmcLean.Kernel.exactMeetingTail
            (McmcLean.Kernel.pathLaw
              (McmcLean.Kernel.laggedInitialMeasure initialCoupling
                (hmcRwmhMixture (xuTheorem41HmcWeight γ)
                  potential gradient ε L hpotential.measurable hgradient
                  variance hvariance))
              (stickyCoupledHmcRwmhMixture (xuTheorem41HmcWeight γ)
                potential gradient ε L hpotential.measurable hgradient
                variance hvariance)) n ≤
            C₀ * contractionRate ^ n := by
  letI : IsMarkovKernel
      (McmcLean.Kernel.euclideanGaussianRandomWalkMetropolisHastings
        (positionBoltzmannWeight potential) variance hvariance) :=
    McmcLean.Kernel.euclideanGaussianRandomWalkMetropolisHastings_isMarkov
      _ variance hvariance
      (measurable_positionBoltzmannWeight hpotential.measurable)
  let p := xuTheorem41HmcWeight γ
  let coupled := stickyCoupledHmcRwmhMixture p potential gradient ε L
    hpotential.measurable hgradient variance hvariance
  let C := McmcLean.Kernel.lyapunovSublevel
    (McmcLean.Kernel.IsCoupling.pairedAdd h.V) (1 + h.ell1)
  have hp : p.1 < 1 := by
    dsimp only [p, xuTheorem41HmcWeight]
    exact tsub_lt_self zero_lt_one γ.property.1
  obtain ⟨meetingBound, hmeetingPos, hmeeting⟩ :=
    exists_pos_stickyCoupledHmcRwmhMixture_exactMeetingSmallSet_on_compact
      p hp potential gradient ε L hpotential hgradient variance hvariance
      hsubCompact hsubNonempty hA hAne hAmeas hAvolume
  have hcoupled : McmcLean.Kernel.IsCoupling coupled
      (hmcRwmhMixture p potential gradient ε L hpotential.measurable
        hgradient variance hvariance)
      (hmcRwmhMixture p potential gradient ε L hpotential.measurable
        hgradient variance hvariance) := by
    dsimp only [coupled]
    exact stickyCoupledHmcRwmhMixture_isCoupling p potential gradient ε L
      hpotential.measurable hgradient variance hvariance
  have hfaithful : McmcLean.Kernel.IsFaithful coupled := by
    dsimp only [coupled]
    exact stickyCoupledHmcRwmhMixture_isFaithful p potential gradient ε L
      hpotential.measurable hgradient variance hvariance
  have hresult := h.exists_geometric_exactLagOneMeetingTail_initial
    initialCoupling hinitial coupled
    (by simpa only [p, hmcRwmhMixture] using hcoupled)
    hmeetingPos (by simpa only [C, coupled] using hmeeting)
    hfaithful hsubNonempty
  simpa only [p, coupled, hmcRwmhMixture] using hresult

/-- Component HMC and RWMH drift certificates, together with the verified
compact RWMH meeting mechanism, yield an explicit geometric meeting tail for
the concrete sticky mixture. This theorem exposes the remaining analytic
obligations branch by branch. -/
theorem exists_scale_rate_stickyCoupledHmcRwmhMixture_meetingTail_of_component_drift
    (p : Set.Icc (0 : NNReal) 1) (hp : p.1 < 1)
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Continuous potential)
    (hgradient : Measurable gradient) (variance : ℝ≥0)
    (hvariance : variance ≠ 0)
    {V : Position ι × Position ι → ENNReal}
    {threshold hmcRate hmcAllowance rwmhRate rwmhAllowance : ENNReal}
    (hhmc : McmcLean.Kernel.HasGeometricDrift
      (maximalSharedMomentumCoupledPositionMultinomialHMC
        potential gradient ε L hpotential.measurable hgradient)
      V (McmcLean.Kernel.lyapunovSublevel V threshold)
      hmcRate hmcAllowance)
    (hrwmh : McmcLean.Kernel.HasGeometricDrift
      (McmcLean.Kernel.coupledEuclideanGaussianRandomWalkMetropolisHastings
        (positionBoltzmannWeight potential) variance hvariance)
      V (McmcLean.Kernel.lyapunovSublevel V threshold)
      rwmhRate rwmhAllowance)
    (hdiagonal : ∀ x ∈ Set.diagonal (Position ι),
      (∫⁻ y, V y ∂McmcLean.Kernel.synchronousCoupling
        (hmcRwmhMixture p potential gradient ε L hpotential.measurable
          hgradient variance hvariance) x) ≤
        hmcRwmhDriftRate p hmcRate rwmhRate * V x +
          (McmcLean.Kernel.lyapunovSublevel V threshold).indicator
            (fun _ => hmcRwmhDriftAllowance p hmcAllowance rwmhAllowance) x)
    (hrate : hmcRwmhDriftRate p hmcRate rwmhRate < 1)
    (hthreshold0 : threshold ≠ 0) (hthresholdTop : threshold ≠ ∞)
    (hbudgetTop :
      hmcRwmhDriftRate p hmcRate rwmhRate * threshold +
        hmcRwmhDriftAllowance p hmcAllowance rwmhAllowance ≠ ∞)
    (hsubCompact : IsCompact (McmcLean.Kernel.lyapunovSublevel V threshold))
    (hsubNonempty :
      (McmcLean.Kernel.lyapunovSublevel V threshold).Nonempty)
    {A : Set (Position ι)}
    (hA : IsCompact A) (hAne : A.Nonempty)
    (hAmeas : MeasurableSet A) (hAvolume : 0 < volume A)
    (x : Position ι × Position ι) (hVxTop : V x ≠ ∞) :
    ∃ scale contractionRate : ENNReal,
      scale ≠ 0 ∧ scale ≠ ∞ ∧ contractionRate < 1 ∧
        McmcLean.Kernel.meetingWeight V scale x ≠ ∞ ∧
          ∀ n : ℕ,
            McmcLean.Kernel.exactMeetingTail
                (McmcLean.Kernel.pathKernel
                  (stickyCoupledHmcRwmhMixture p potential gradient ε L
                    hpotential.measurable hgradient variance hvariance) x) n ≤
              contractionRate ^ n *
                McmcLean.Kernel.meetingWeight V scale x := by
  let coupled := stickyCoupledHmcRwmhMixture p potential gradient ε L
    hpotential.measurable hgradient variance hvariance
  have hdrift : McmcLean.Kernel.HasGeometricDrift coupled V
      (McmcLean.Kernel.lyapunovSublevel V threshold)
      (hmcRwmhDriftRate p hmcRate rwmhRate)
      (hmcRwmhDriftAllowance p hmcAllowance rwmhAllowance) :=
    stickyCoupledHmcRwmhMixture_hasGeometricDrift_of_components p potential
      gradient ε L hpotential.measurable hgradient variance hvariance hhmc
      hrwmh hdiagonal
  obtain ⟨meetingBound, hmeetingPos, hmeeting⟩ :=
    exists_pos_stickyCoupledHmcRwmhMixture_exactMeetingSmallSet_on_compact
      p hp potential gradient ε L hpotential hgradient variance hvariance
      hsubCompact hsubNonempty hA hAne hAmeas hAvolume
  have hmeetingLe : meetingBound ≤ 1 := by
    obtain ⟨z, hz⟩ := hsubNonempty
    calc
      meetingBound ≤ coupled z (Set.diagonal (Position ι)) := hmeeting z hz
      _ ≤ coupled z Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  exact hdrift.exists_scale_rate_exactMeetingTail_pathKernel_le coupled hmeeting
    (stickyCoupledHmcRwmhMixture_isFaithful p potential gradient ε L
      hpotential.measurable hgradient variance hvariance)
    hrate hmeetingPos hmeetingLe hthreshold0 hthresholdTop hbudgetTop x hVxTop

/-- Additive paired Lyapunov functions give the concrete component-drift
meeting-tail theorem without a separate sticky diagonal-row hypothesis. -/
theorem exists_scale_rate_stickyCoupledHmcRwmhMixture_meetingTail_pairedAdd
    (p : Set.Icc (0 : NNReal) 1) (hp : p.1 < 1)
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Continuous potential)
    (hgradient : Measurable gradient) (variance : ℝ≥0)
    (hvariance : variance ≠ 0)
    {v : Position ι → ENNReal} (hv : Measurable v)
    {threshold hmcRate hmcAllowance rwmhRate rwmhAllowance : ENNReal}
    (hhmc : McmcLean.Kernel.HasGeometricDrift
      (maximalSharedMomentumCoupledPositionMultinomialHMC
        potential gradient ε L hpotential.measurable hgradient)
      (McmcLean.Kernel.IsCoupling.pairedAdd v)
      (McmcLean.Kernel.lyapunovSublevel
        (McmcLean.Kernel.IsCoupling.pairedAdd v) threshold)
      hmcRate hmcAllowance)
    (hrwmh : McmcLean.Kernel.HasGeometricDrift
      (McmcLean.Kernel.coupledEuclideanGaussianRandomWalkMetropolisHastings
        (positionBoltzmannWeight potential) variance hvariance)
      (McmcLean.Kernel.IsCoupling.pairedAdd v)
      (McmcLean.Kernel.lyapunovSublevel
        (McmcLean.Kernel.IsCoupling.pairedAdd v) threshold)
      rwmhRate rwmhAllowance)
    (hrate : hmcRwmhDriftRate p hmcRate rwmhRate < 1)
    (hthreshold0 : threshold ≠ 0) (hthresholdTop : threshold ≠ ∞)
    (hbudgetTop :
      hmcRwmhDriftRate p hmcRate rwmhRate * threshold +
        hmcRwmhDriftAllowance p hmcAllowance rwmhAllowance ≠ ∞)
    (hsubCompact : IsCompact (McmcLean.Kernel.lyapunovSublevel
      (McmcLean.Kernel.IsCoupling.pairedAdd v) threshold))
    (hsubNonempty : (McmcLean.Kernel.lyapunovSublevel
      (McmcLean.Kernel.IsCoupling.pairedAdd v) threshold).Nonempty)
    {A : Set (Position ι)}
    (hA : IsCompact A) (hAne : A.Nonempty)
    (hAmeas : MeasurableSet A) (hAvolume : 0 < volume A)
    (x : Position ι × Position ι)
    (hVxTop : McmcLean.Kernel.IsCoupling.pairedAdd v x ≠ ∞) :
    ∃ scale contractionRate : ENNReal,
      scale ≠ 0 ∧ scale ≠ ∞ ∧ contractionRate < 1 ∧
        McmcLean.Kernel.meetingWeight
          (McmcLean.Kernel.IsCoupling.pairedAdd v) scale x ≠ ∞ ∧
          ∀ n : ℕ,
            McmcLean.Kernel.exactMeetingTail
                (McmcLean.Kernel.pathKernel
                  (stickyCoupledHmcRwmhMixture p potential gradient ε L
                    hpotential.measurable hgradient variance hvariance) x) n ≤
              contractionRate ^ n *
                McmcLean.Kernel.meetingWeight
                  (McmcLean.Kernel.IsCoupling.pairedAdd v) scale x := by
  let V := McmcLean.Kernel.IsCoupling.pairedAdd v
  let coupled := stickyCoupledHmcRwmhMixture p potential gradient ε L
    hpotential.measurable hgradient variance hvariance
  have hdrift : McmcLean.Kernel.HasGeometricDrift coupled V
      (McmcLean.Kernel.lyapunovSublevel V threshold)
      (hmcRwmhDriftRate p hmcRate rwmhRate)
      (hmcRwmhDriftAllowance p hmcAllowance rwmhAllowance) :=
    stickyCoupledHmcRwmhMixture_hasGeometricDrift_pairedAdd_of_components
      p potential gradient ε L hpotential.measurable hgradient variance
      hvariance hv hhmc hrwmh
  obtain ⟨meetingBound, hmeetingPos, hmeeting⟩ :=
    exists_pos_stickyCoupledHmcRwmhMixture_exactMeetingSmallSet_on_compact
      p hp potential gradient ε L hpotential hgradient variance hvariance
      hsubCompact hsubNonempty hA hAne hAmeas hAvolume
  have hmeetingLe : meetingBound ≤ 1 := by
    obtain ⟨z, hz⟩ := hsubNonempty
    calc
      meetingBound ≤ coupled z (Set.diagonal (Position ι)) := hmeeting z hz
      _ ≤ coupled z Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  exact hdrift.exists_scale_rate_exactMeetingTail_pathKernel_le coupled hmeeting
    (stickyCoupledHmcRwmhMixture_isFaithful p potential gradient ε L
      hpotential.measurable hgradient variance hvariance)
    hrate hmeetingPos hmeetingLe hthreshold0 hthresholdTop hbudgetTop x hVxTop

/-- End-to-end concrete meeting-tail theorem from ordinary single-chain HMC
and RWMH affine drift certificates. Coupled drift follows solely from the
already proved exact marginal identities. -/
theorem exists_scale_rate_stickyCoupledHmcRwmhMixture_meetingTail_of_singleChain_drift
    (p : Set.Icc (0 : NNReal) 1) (hp : p.1 < 1)
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Continuous potential)
    (hgradient : Measurable gradient) (variance : ℝ≥0)
    (hvariance : variance ≠ 0)
    {v : Position ι → ENNReal}
    {threshold hmcSourceRate hmcSourceAllowance hmcPairedRate
      rwmhSourceRate rwmhSourceAllowance rwmhPairedRate : ENNReal}
    (hhmc : McmcLean.Kernel.HasAffineDrift
      (standardPositionMultinomialHMC potential gradient ε L
        hpotential.measurable hgradient)
      v hmcSourceRate hmcSourceAllowance)
    (hrwmh : McmcLean.Kernel.HasAffineDrift
      (McmcLean.Kernel.euclideanGaussianRandomWalkMetropolisHastings
        (positionBoltzmannWeight potential) variance hvariance)
      v rwmhSourceRate rwmhSourceAllowance)
    (hhmcRates : hmcSourceRate ≤ hmcPairedRate)
    (hhmcThreshold :
      hmcSourceRate * threshold +
          (hmcSourceAllowance + hmcSourceAllowance) ≤
        hmcPairedRate * threshold)
    (hrwmhRates : rwmhSourceRate ≤ rwmhPairedRate)
    (hrwmhThreshold :
      rwmhSourceRate * threshold +
          (rwmhSourceAllowance + rwmhSourceAllowance) ≤
        rwmhPairedRate * threshold)
    (hrate : hmcRwmhDriftRate p hmcPairedRate rwmhPairedRate < 1)
    (hthreshold0 : threshold ≠ 0) (hthresholdTop : threshold ≠ ∞)
    (hbudgetTop :
      hmcRwmhDriftRate p hmcPairedRate rwmhPairedRate * threshold +
        hmcRwmhDriftAllowance p
          (hmcSourceAllowance + hmcSourceAllowance)
          (rwmhSourceAllowance + rwmhSourceAllowance) ≠ ∞)
    (hsubCompact : IsCompact (McmcLean.Kernel.lyapunovSublevel
      (McmcLean.Kernel.IsCoupling.pairedAdd v) threshold))
    (hsubNonempty : (McmcLean.Kernel.lyapunovSublevel
      (McmcLean.Kernel.IsCoupling.pairedAdd v) threshold).Nonempty)
    {A : Set (Position ι)}
    (hA : IsCompact A) (hAne : A.Nonempty)
    (hAmeas : MeasurableSet A) (hAvolume : 0 < volume A)
    (x : Position ι × Position ι)
    (hVxTop : McmcLean.Kernel.IsCoupling.pairedAdd v x ≠ ∞) :
    ∃ scale contractionRate : ENNReal,
      scale ≠ 0 ∧ scale ≠ ∞ ∧ contractionRate < 1 ∧
        McmcLean.Kernel.meetingWeight
          (McmcLean.Kernel.IsCoupling.pairedAdd v) scale x ≠ ∞ ∧
          ∀ n : ℕ,
            McmcLean.Kernel.exactMeetingTail
                (McmcLean.Kernel.pathKernel
                  (stickyCoupledHmcRwmhMixture p potential gradient ε L
                    hpotential.measurable hgradient variance hvariance) x) n ≤
              contractionRate ^ n *
                McmcLean.Kernel.meetingWeight
                  (McmcLean.Kernel.IsCoupling.pairedAdd v) scale x := by
  have hhmcCoupled := hhmc.coupling_pairedAdd_sublevel
    (standardPositionMultinomialHMC potential gradient ε L
      hpotential.measurable hgradient)
    (maximalSharedMomentumCoupledPositionMultinomialHMC
      potential gradient ε L hpotential.measurable hgradient)
    (maximalSharedMomentumCoupledPositionMultinomialHMC_isCoupling
      potential gradient ε L hpotential.measurable hgradient)
    hhmcRates hhmcThreshold
  have hrwmhCoupled := hrwmh.coupling_pairedAdd_sublevel
    (McmcLean.Kernel.euclideanGaussianRandomWalkMetropolisHastings
      (positionBoltzmannWeight potential) variance hvariance)
    (McmcLean.Kernel.coupledEuclideanGaussianRandomWalkMetropolisHastings
      (positionBoltzmannWeight potential) variance hvariance)
    (McmcLean.Kernel.coupledEuclideanGaussianRandomWalkMetropolisHastings_isCoupling
      (positionBoltzmannWeight potential) variance hvariance
      (measurable_positionBoltzmannWeight hpotential.measurable))
    hrwmhRates hrwmhThreshold
  exact exists_scale_rate_stickyCoupledHmcRwmhMixture_meetingTail_pairedAdd
    p hp potential gradient ε L hpotential hgradient variance hvariance
    hhmc.1 hhmcCoupled hrwmhCoupled hrate hthreshold0 hthresholdTop
    hbudgetTop hsubCompact hsubNonempty hA hAne hAmeas hAvolume x hVxTop

/-- Canonical paired rates remove all manual rate-selection conditions. It is
enough that each ordinary single-chain affine budget fits strictly below the
chosen paired Lyapunov threshold. -/
theorem exists_scale_rate_stickyCoupledHmcRwmhMixture_meetingTail_of_singleChain_budgets
    (p : Set.Icc (0 : NNReal) 1) (hp : p.1 < 1)
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Continuous potential)
    (hgradient : Measurable gradient) (variance : ℝ≥0)
    (hvariance : variance ≠ 0)
    {v : Position ι → ENNReal}
    {threshold hmcRate hmcAllowance rwmhRate rwmhAllowance : ENNReal}
    (hhmc : McmcLean.Kernel.HasAffineDrift
      (standardPositionMultinomialHMC potential gradient ε L
        hpotential.measurable hgradient) v hmcRate hmcAllowance)
    (hrwmh : McmcLean.Kernel.HasAffineDrift
      (McmcLean.Kernel.euclideanGaussianRandomWalkMetropolisHastings
        (positionBoltzmannWeight potential) variance hvariance)
      v rwmhRate rwmhAllowance)
    (hthreshold0 : threshold ≠ 0) (hthresholdTop : threshold ≠ ∞)
    (hhmcBudget :
      hmcRate * threshold + (hmcAllowance + hmcAllowance) < threshold)
    (hrwmhBudget :
      rwmhRate * threshold + (rwmhAllowance + rwmhAllowance) < threshold)
    (hsubCompact : IsCompact (McmcLean.Kernel.lyapunovSublevel
      (McmcLean.Kernel.IsCoupling.pairedAdd v) threshold))
    (hsubNonempty : (McmcLean.Kernel.lyapunovSublevel
      (McmcLean.Kernel.IsCoupling.pairedAdd v) threshold).Nonempty)
    {A : Set (Position ι)}
    (hA : IsCompact A) (hAne : A.Nonempty)
    (hAmeas : MeasurableSet A) (hAvolume : 0 < volume A)
    (x : Position ι × Position ι)
    (hVxTop : McmcLean.Kernel.IsCoupling.pairedAdd v x ≠ ∞) :
    ∃ scale contractionRate : ENNReal,
      scale ≠ 0 ∧ scale ≠ ∞ ∧ contractionRate < 1 ∧
        McmcLean.Kernel.meetingWeight
          (McmcLean.Kernel.IsCoupling.pairedAdd v) scale x ≠ ∞ ∧
          ∀ n : ℕ,
            McmcLean.Kernel.exactMeetingTail
                (McmcLean.Kernel.pathKernel
                  (stickyCoupledHmcRwmhMixture p potential gradient ε L
                    hpotential.measurable hgradient variance hvariance) x) n ≤
              contractionRate ^ n *
                McmcLean.Kernel.meetingWeight
                  (McmcLean.Kernel.IsCoupling.pairedAdd v) scale x := by
  let hmcPairedRate := McmcLean.Kernel.affinePairedSublevelRate
    hmcRate hmcAllowance threshold
  let rwmhPairedRate := McmcLean.Kernel.affinePairedSublevelRate
    rwmhRate rwmhAllowance threshold
  obtain ⟨hhmcRates, hhmcThreshold, hhmcPairedRate⟩ :=
    McmcLean.Kernel.affinePairedSublevelRate_spec hthreshold0 hthresholdTop
      hhmcBudget
  obtain ⟨hrwmhRates, hrwmhThreshold, hrwmhPairedRate⟩ :=
    McmcLean.Kernel.affinePairedSublevelRate_spec hthreshold0 hthresholdTop
      hrwmhBudget
  have hcombinedRate :
      hmcRwmhDriftRate p hmcPairedRate rwmhPairedRate < 1 :=
    hmcRwmhDriftRate_lt_one p hhmcPairedRate hrwmhPairedRate
  have hhmcAllowanceTop : hmcAllowance + hmcAllowance ≠ ∞ := by
    exact ne_top_of_lt ((show hmcAllowance + hmcAllowance ≤
      hmcRate * threshold + (hmcAllowance + hmcAllowance) from
        le_add_left le_rfl).trans_lt hhmcBudget)
  have hrwmhAllowanceTop : rwmhAllowance + rwmhAllowance ≠ ∞ := by
    exact ne_top_of_lt ((show rwmhAllowance + rwmhAllowance ≤
      rwmhRate * threshold + (rwmhAllowance + rwmhAllowance) from
        le_add_left le_rfl).trans_lt hrwmhBudget)
  have hcombinedAllowanceTop : hmcRwmhDriftAllowance p
      (hmcAllowance + hmcAllowance)
      (rwmhAllowance + rwmhAllowance) ≠ ∞ := by
    unfold hmcRwmhDriftAllowance
    exact ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top hhmcAllowanceTop,
        ENNReal.mul_ne_top ENNReal.coe_ne_top hrwmhAllowanceTop⟩
  have hcombinedBudgetTop :
      hmcRwmhDriftRate p hmcPairedRate rwmhPairedRate * threshold +
        hmcRwmhDriftAllowance p
          (hmcAllowance + hmcAllowance)
          (rwmhAllowance + rwmhAllowance) ≠ ∞ := by
    exact ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top hcombinedRate.ne_top hthresholdTop,
        hcombinedAllowanceTop⟩
  exact exists_scale_rate_stickyCoupledHmcRwmhMixture_meetingTail_of_singleChain_drift
    p hp potential gradient ε L hpotential hgradient variance hvariance
    hhmc hrwmh hhmcRates hhmcThreshold hrwmhRates hrwmhThreshold
    hcombinedRate hthreshold0 hthresholdTop hcombinedBudgetTop hsubCompact
    hsubNonempty hA hAne hAmeas hAvolume x hVxTop

/-- A uniform finite-step return bound to the compact meeting set closes the
concrete faithful mixture to geometric off-diagonal decay along skeleton
times. This isolates the remaining output required from the drift theorem. -/
theorem exists_pos_stickyCoupledHmcRwmhMixture_skeleton_geometric
    (initial : Measure (Position ι × Position ι))
    [IsProbabilityMeasure initial]
    (p : Set.Icc (0 : NNReal) 1) (hp : p.1 < 1)
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Continuous potential)
    (hgradient : Measurable gradient) (variance : ℝ≥0)
    (hvariance : variance ≠ 0)
    {C : Set (Position ι × Position ι)} {A : Set (Position ι)}
    (hC : IsCompact C) (hCne : C.Nonempty) (hCmeas : MeasurableSet C)
    (hA : IsCompact A) (hAne : A.Nonempty)
    (hAmeas : MeasurableSet A) (hAvolume : 0 < volume A)
    (steps : ℕ) (returnBound : ENNReal) (hreturnBound : 0 < returnBound)
    (hreturn : McmcLean.Kernel.IsUniformlyAccessible
      (stickyCoupledHmcRwmhMixture p potential gradient ε L
        hpotential.measurable hgradient variance hvariance)
      C steps returnBound) :
    ∃ meetingBound : ENNReal, 0 < meetingBound ∧
      0 < meetingBound * returnBound ∧
      1 - meetingBound * returnBound < 1 ∧
      ∀ n,
        McmcLean.Kernel.offDiagonalMassAtTime initial
            (stickyCoupledHmcRwmhMixture p potential gradient ε L
              hpotential.measurable hgradient variance hvariance)
            ((steps + 1) * n) ≤
          (1 - meetingBound * returnBound) ^ n := by
  obtain ⟨meetingBound, hmeetingPos, hmeeting⟩ :=
    exists_pos_stickyCoupledHmcRwmhMixture_exactMeetingSmallSet_on_compact
      p hp potential gradient ε L hpotential hgradient variance hvariance
      hC hCne hA hAne hAmeas hAvolume
  have hproduct : 0 < meetingBound * returnBound :=
    ENNReal.mul_pos hmeetingPos.ne' hreturnBound.ne'
  refine ⟨meetingBound, hmeetingPos, hproduct,
    ENNReal.sub_lt_self (by simp) (by simp) hproduct.ne', fun n => ?_⟩
  exact McmcLean.Kernel.offDiagonalMassAtSkeletonTime_le_geometric
    initial
    (stickyCoupledHmcRwmhMixture p potential gradient ε L
      hpotential.measurable hgradient variance hvariance)
    hCmeas steps returnBound meetingBound hreturn hmeeting
    (stickyCoupledHmcRwmhMixture_isFaithful p potential gradient ε L
      hpotential.measurable hgradient variance hvariance) n

/-- Under the same finite-step return hypothesis, the concrete sticky
HMC/RWMH path law has a geometric exact meeting-time tail at every time. The
exponent counts completed skeleton blocks. -/
theorem exists_pos_stickyCoupledHmcRwmhMixture_meetingTail_geometric
    (initial : Measure (Position ι × Position ι))
    [IsProbabilityMeasure initial]
    (p : Set.Icc (0 : NNReal) 1) (hp : p.1 < 1)
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Continuous potential)
    (hgradient : Measurable gradient) (variance : ℝ≥0)
    (hvariance : variance ≠ 0)
    {C : Set (Position ι × Position ι)} {A : Set (Position ι)}
    (hC : IsCompact C) (hCne : C.Nonempty) (hCmeas : MeasurableSet C)
    (hA : IsCompact A) (hAne : A.Nonempty)
    (hAmeas : MeasurableSet A) (hAvolume : 0 < volume A)
    (steps : ℕ) (returnBound : ENNReal) (hreturnBound : 0 < returnBound)
    (hreturn : McmcLean.Kernel.IsUniformlyAccessible
      (stickyCoupledHmcRwmhMixture p potential gradient ε L
        hpotential.measurable hgradient variance hvariance)
      C steps returnBound) :
    ∃ meetingBound : ENNReal, 0 < meetingBound ∧
      0 < meetingBound * returnBound ∧
      1 - meetingBound * returnBound < 1 ∧
      ∀ n,
        McmcLean.Kernel.exactMeetingTail
            (McmcLean.Kernel.pathLaw initial
              (stickyCoupledHmcRwmhMixture p potential gradient ε L
                hpotential.measurable hgradient variance hvariance))
            n ≤
          (1 - meetingBound * returnBound) ^ (n / (steps + 1)) := by
  obtain ⟨meetingBound, hmeetingPos, hmeeting⟩ :=
    exists_pos_stickyCoupledHmcRwmhMixture_exactMeetingSmallSet_on_compact
      p hp potential gradient ε L hpotential hgradient variance hvariance
      hC hCne hA hAne hAmeas hAvolume
  have hproduct : 0 < meetingBound * returnBound :=
    ENNReal.mul_pos hmeetingPos.ne' hreturnBound.ne'
  refine ⟨meetingBound, hmeetingPos, hproduct,
    ENNReal.sub_lt_self (by simp) (by simp) hproduct.ne', fun n => ?_⟩
  exact McmcLean.Kernel.exactMeetingTail_pathLaw_le_geometric_div
    initial
    (stickyCoupledHmcRwmhMixture p potential gradient ε L
      hpotential.measurable hgradient variance hvariance)
    hCmeas steps returnBound meetingBound hreturn hmeeting
    (stickyCoupledHmcRwmhMixture_isFaithful p potential gradient ε L
      hpotential.measurable hgradient variance hvariance) n

/-- A globally bounded Foster--Lyapunov certificate closes the concrete
sticky HMC/RWMH mixture to a geometric exact meeting-time tail, without a
separate accessibility premise. The compact Lyapunov sublevel supplies the
already verified exact-meeting small set. -/
theorem exists_pos_stickyCoupledHmcRwmhMixture_meetingTail_of_bounded_drift
    (initial : Measure (Position ι × Position ι))
    [IsProbabilityMeasure initial]
    (p : Set.Icc (0 : NNReal) 1) (hp : p.1 < 1)
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Continuous potential)
    (hgradient : Measurable gradient) (variance : ℝ≥0)
    (hvariance : variance ≠ 0)
    {V : Position ι × Position ι → ENNReal}
    {driftSet : Set (Position ι × Position ι)}
    {rate allowance B R : ENNReal}
    (hdrift : McmcLean.Kernel.HasGeometricDrift
      (stickyCoupledHmcRwmhMixture p potential gradient ε L
        hpotential.measurable hgradient variance hvariance)
      V driftSet rate allowance)
    (hV : ∀ x, V x ≤ B)
    (hR0 : R ≠ 0) (hRtop : R ≠ ∞)
    (hbudget : rate * B + allowance < R)
    (hsubCompact : IsCompact (McmcLean.Kernel.lyapunovSublevel V R))
    (hsubNonempty : (McmcLean.Kernel.lyapunovSublevel V R).Nonempty)
    {A : Set (Position ι)}
    (hA : IsCompact A) (hAne : A.Nonempty)
    (hAmeas : MeasurableSet A) (hAvolume : 0 < volume A) :
    ∃ meetingBound : ENNReal, 0 < meetingBound ∧
      let returnBound := 1 - (rate * B + allowance) / R
      0 < meetingBound * returnBound ∧
        1 - meetingBound * returnBound < 1 ∧
        ∀ n,
          McmcLean.Kernel.exactMeetingTail
              (McmcLean.Kernel.pathLaw initial
                (stickyCoupledHmcRwmhMixture p potential gradient ε L
                  hpotential.measurable hgradient variance hvariance)) n ≤
            (1 - meetingBound * returnBound) ^ (n / 2) := by
  obtain ⟨meetingBound, hmeetingPos, hmeeting⟩ :=
    exists_pos_stickyCoupledHmcRwmhMixture_exactMeetingSmallSet_on_compact
      p hp potential gradient ε L hpotential hgradient variance hvariance
      hsubCompact hsubNonempty hA hAne hAmeas hAvolume
  refine ⟨meetingBound, hmeetingPos, ?_⟩
  exact hdrift.exactMeetingTail_pathLaw_le_geometric_of_bounded initial
    (stickyCoupledHmcRwmhMixture p potential gradient ε L
      hpotential.measurable hgradient variance hvariance)
    hV hR0 hRtop hbudget hmeetingPos hmeeting
    (stickyCoupledHmcRwmhMixture_isFaithful p potential gradient ε L
      hpotential.measurable hgradient variance hvariance)

end McmcLean.Hamiltonian
