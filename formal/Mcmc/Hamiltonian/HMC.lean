import Mcmc.Hamiltonian.Invariance
import Mcmc.Hamiltonian.MomentumRefresh
import Mcmc.Kernel.LiftEvolveProject
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# Complete multinomial Hamiltonian Monte Carlo kernels

This module packages momentum resampling and randomized multinomial trajectory
selection into phase- and position-space HMC kernels.  The correctness theorem
is stated against an explicit compatibility equation: the product of the
position and momentum targets must be the Boltzmann phase measure used by the
trajectory weights.  Thus neither the target factorization nor normalization
is hidden in the kernel definition.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace Mcmc.Hamiltonian

open ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- Unnormalized position density associated with a potential. -/
noncomputable def positionBoltzmannWeight (potential : Position ι → ℝ)
    (q : Position ι) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-potential q))

/-- Unnormalized momentum density associated with unit-mass quadratic kinetic
energy. -/
noncomputable def kineticBoltzmannWeight (p : Momentum ι) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-kineticEnergy p))

/-- The unnormalized Boltzmann position measure. -/
noncomputable def positionBoltzmannTarget (potential : Position ι → ℝ) :
    Measure (Position ι) :=
  volume.withDensity (positionBoltzmannWeight potential)

/-- The unnormalized Boltzmann momentum measure. -/
noncomputable def kineticBoltzmannTarget : Measure (Momentum ι) :=
  volume.withDensity kineticBoltzmannWeight

omit [Fintype ι] in
theorem measurable_positionBoltzmannWeight
    {potential : Position ι → ℝ} (hpotential : Measurable potential) :
    Measurable (positionBoltzmannWeight potential) := by
  exact ENNReal.measurable_ofReal.comp (hpotential.neg.exp)

omit [Fintype ι] in
/-- The Boltzmann position weight is strictly positive everywhere. -/
theorem positionBoltzmannWeight_pos (potential : Position ι → ℝ)
    (q : Position ι) :
    0 < positionBoltzmannWeight potential q := by
  rw [positionBoltzmannWeight, ENNReal.ofReal_pos]
  exact Real.exp_pos _

omit [Fintype ι] in
/-- The Boltzmann position weight is finite everywhere. -/
theorem positionBoltzmannWeight_ne_top (potential : Position ι → ℝ)
    (q : Position ι) :
    positionBoltzmannWeight potential q ≠ ∞ :=
  ENNReal.ofReal_ne_top

theorem measurable_kineticBoltzmannWeight :
    Measurable (kineticBoltzmannWeight : Momentum ι → ℝ≥0∞) := by
  exact ENNReal.measurable_ofReal.comp (measurable_kineticEnergy.neg.exp)

theorem boltzmannWeight_eq_position_mul_kinetic
    (potential : Position ι → ℝ) (z : PhaseSpace ι) :
    boltzmannWeight potential z =
      positionBoltzmannWeight potential z.1 * kineticBoltzmannWeight z.2 := by
  rw [boltzmannWeight, positionBoltzmannWeight, kineticBoltzmannWeight, energy]
  rw [show -(potential z.1 + kineticEnergy z.2) =
      -potential z.1 + -kineticEnergy z.2 by ring]
  rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]

/-- The phase Boltzmann measure factors exactly into its position and kinetic
Boltzmann measures. -/
theorem phaseBoltzmannTarget_eq_prod
    {potential : Position ι → ℝ} (hpotential : Measurable potential) :
    phaseBoltzmannTarget potential =
      (positionBoltzmannTarget potential).prod kineticBoltzmannTarget := by
  rw [positionBoltzmannTarget, kineticBoltzmannTarget,
    prod_withDensity
      (measurable_positionBoltzmannWeight hpotential)
      measurable_kineticBoltzmannWeight]
  unfold phaseBoltzmannTarget phaseVolume
  congr 1
  funext z
  exact boltzmannWeight_eq_position_mul_kinetic potential z

/-- The one-coordinate normalizing factor in the standard Gaussian density. -/
noncomputable def standardGaussianPrefactor : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt (2 * Real.pi)⁻¹)

/-- The finite-dimensional normalizing factor multiplying `exp (-K(p))` in
the product standard Gaussian density. -/
noncomputable def standardMomentumPrefactor : ℝ≥0∞ :=
  ∏ _ : ι, standardGaussianPrefactor

theorem isotropicGaussianPDF_one_eq_prefactor_mul_kinetic
    (p : Momentum ι) :
    Mcmc.Kernel.isotropicGaussianPDF (ι := ι) 1 p =
      standardMomentumPrefactor (ι := ι) * kineticBoltzmannWeight p := by
  unfold Mcmc.Kernel.isotropicGaussianPDF gaussianPDF gaussianPDFReal
    standardMomentumPrefactor standardGaussianPrefactor kineticBoltzmannWeight
    kineticEnergy
  norm_num
  rw [Finset.prod_mul_distrib]
  congr 1
  · simp
  · rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.exp_pos _ |>.le)]
    rw [← Real.exp_sum]
    congr 2
    ring_nf
    exact (Finset.sum_mul Finset.univ (fun x => p x ^ 2) (-1 / 2)).symm

/-- Mathlib's standard product Gaussian is the normalized scalar multiple of
the unnormalized kinetic Boltzmann measure. -/
theorem standardMomentumMeasure_eq_smul_kinetic :
    standardMomentumMeasure (ι := ι) =
      standardMomentumPrefactor (ι := ι) • kineticBoltzmannTarget := by
  unfold standardMomentumMeasure Mcmc.Kernel.densityTarget
    kineticBoltzmannTarget
  rw [show Mcmc.Kernel.isotropicGaussianPDF (ι := ι) 1 =
      standardMomentumPrefactor (ι := ι) • kineticBoltzmannWeight by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul]
    exact isotropicGaussianPDF_one_eq_prefactor_mul_kinetic p]
  exact withDensity_smul _ measurable_kineticBoltzmannWeight

/-- Invariance is unchanged by scaling the invariant measure. -/
theorem Kernel.Invariant.smul {α : Type*} [MeasurableSpace α]
    {κ : Kernel α α} {μ : Measure α} (h : κ.Invariant μ) (c : ℝ≥0∞) :
    κ.Invariant (c • μ) := by
  rw [Kernel.Invariant, Measure.comp_smul, h]

/-- The usual position Boltzmann target paired with standard Gaussian momentum
is a scalar multiple of the phase Boltzmann target. -/
theorem positionBoltzmann_prod_standardMomentum
    {potential : Position ι → ℝ} (hpotential : Measurable potential) :
    (positionBoltzmannTarget potential).prod standardMomentumMeasure =
      standardMomentumPrefactor (ι := ι) • phaseBoltzmannTarget potential := by
  letI : SFinite (kineticBoltzmannTarget (ι := ι)) := by
    unfold kineticBoltzmannTarget
    infer_instance
  rw [standardMomentumMeasure_eq_smul_kinetic,
    Measure.prod_smul_right, phaseBoltzmannTarget_eq_prod hpotential]

/-- A position is augmented with an independently sampled momentum. -/
noncomputable def positionMomentumLift
    (momentumTarget : Measure (Momentum ι)) :
    Kernel (Position ι) (PhaseSpace ι) :=
  Kernel.id ×ₖ Kernel.const (Position ι) momentumTarget

instance positionMomentumLift_isMarkovKernel
    (momentumTarget : Measure (Momentum ι))
    [IsProbabilityMeasure momentumTarget] :
    IsMarkovKernel (positionMomentumLift momentumTarget) := by
  unfold positionMomentumLift
  infer_instance

omit [Fintype ι] in
/-- The row of the momentum-augmentation kernel is a Dirac position paired
with the independently sampled momentum law. -/
theorem positionMomentumLift_apply
    (momentumTarget : Measure (Momentum ι)) [SFinite momentumTarget]
    (q : Position ι) :
    positionMomentumLift momentumTarget q =
      (Measure.dirac q).prod momentumTarget := by
  rw [positionMomentumLift, Kernel.prod_apply, Kernel.id_apply,
    Kernel.const_apply]

omit [Fintype ι] in
theorem positionMomentumLift_comp
    (positionTarget : Measure (Position ι)) [SFinite positionTarget]
    (momentumTarget : Measure (Momentum ι)) [SFinite momentumTarget] :
    positionMomentumLift momentumTarget ∘ₘ positionTarget =
      positionTarget.prod momentumTarget := by
  rw [positionMomentumLift, ← Measure.compProd_eq_comp_prod,
    Measure.compProd_const]

/-- One complete phase-space multinomial HMC step: refresh momentum, then
perform the randomized multinomial leapfrog transition. -/
noncomputable def phaseMultinomialHMC
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient)
    (momentumTarget : Measure (Momentum ι)) :
    Kernel (PhaseSpace ι) (PhaseSpace ι) :=
  randomizedMultinomialLeapfrogKernel potential gradient ε L
      hpotential hgradient ∘ₖ
    momentumRefreshWith momentumTarget

instance phaseMultinomialHMC_isMarkovKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient)
    (momentumTarget : Measure (Momentum ι))
    [IsProbabilityMeasure momentumTarget] :
    IsMarkovKernel (phaseMultinomialHMC potential gradient ε L
      hpotential hgradient momentumTarget) := by
  unfold phaseMultinomialHMC
  infer_instance

/-- The complete phase-space HMC step preserves a compatible product target. -/
theorem phaseMultinomialHMC_invariant
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) (L : ℕ)
    (positionTarget : Measure (Position ι)) [SFinite positionTarget]
    (momentumTarget : Measure (Momentum ι))
    [IsProbabilityMeasure momentumTarget]
    (hfactor : positionTarget.prod momentumTarget =
      phaseBoltzmannTarget potential) :
    (phaseMultinomialHMC potential gradient ε L hpotential hgradient
      momentumTarget).Invariant (positionTarget.prod momentumTarget) := by
  unfold phaseMultinomialHMC
  have htrajectory := randomizedMultinomialLeapfrogKernel_invariant
    hpotential hgradient ε L
  rw [← hfactor] at htrajectory
  exact htrajectory.comp
    (momentumRefreshWith_invariant positionTarget momentumTarget)

/-- The user-facing position-space multinomial HMC kernel: independently draw
momentum, perform the randomized trajectory transition, and discard momentum. -/
noncomputable def positionMultinomialHMC
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient)
    (momentumTarget : Measure (Momentum ι)) :
    Kernel (Position ι) (Position ι) :=
  (randomizedMultinomialLeapfrogKernel potential gradient ε L
      hpotential hgradient ∘ₖ
    positionMomentumLift momentumTarget).map
      (Prod.fst : PhaseSpace ι → Position ι)

instance positionMultinomialHMC_isMarkovKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient)
    (momentumTarget : Measure (Momentum ι))
    [IsProbabilityMeasure momentumTarget] :
    IsMarkovKernel (positionMultinomialHMC potential gradient ε L
      hpotential hgradient momentumTarget) := by
  unfold positionMultinomialHMC
  exact Kernel.IsMarkovKernel.map _ measurable_fst

/-- Exact momentum-integral and finite-sum expectation formula for the
implemented position-space multinomial HMC transition. -/
theorem lintegral_positionMultinomialHMC
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient)
    (momentumTarget : Measure (Momentum ι))
    [IsProbabilityMeasure momentumTarget]
    (f : Position ι → ENNReal) (hf : Measurable f) (q : Position ι) :
    (∫⁻ y, f y ∂positionMultinomialHMC potential gradient ε L
      hpotential hgradient momentumTarget q) =
      ∫⁻ p, ∑ origin : Fin (L + 1),
        PMF.uniformOfFintype (Fin (L + 1)) origin *
          ∑ selected : Fin (L + 1),
            trajectoryIndexPMF potential
                (offsetLeapfrogTrajectory gradient ε origin (q, p)) selected *
              f (offsetLeapfrogTrajectory gradient ε origin (q, p) selected).1
        ∂momentumTarget := by
  let g : PhaseSpace ι → ENNReal := fun z ↦ f z.1
  have hg : Measurable g := hf.comp measurable_fst
  rw [positionMultinomialHMC,
    Kernel.lintegral_map _ measurable_fst _ hf,
    Kernel.lintegral_comp _ _ _ hg,
    positionMomentumLift_apply]
  change (∫⁻ z, ∫⁻ w, g w
      ∂randomizedMultinomialLeapfrogKernel potential gradient ε L
        hpotential hgradient z ∂(Measure.dirac q).prod momentumTarget) = _
  rw [MeasureTheory.lintegral_prod _ hg.lintegral_kernel.aemeasurable,
    lintegral_dirac' q hg.lintegral_kernel.lintegral_prod_right]
  exact lintegral_congr fun p ↦
    lintegral_randomizedMultinomialLeapfrogKernel potential gradient ε L
      hpotential hgradient g hg (q, p)

/-- A compatible position target is invariant under the complete
position-space multinomial HMC kernel. -/
theorem positionMultinomialHMC_invariant
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) (L : ℕ)
    (positionTarget : Measure (Position ι)) [SFinite positionTarget]
    (momentumTarget : Measure (Momentum ι))
    [IsProbabilityMeasure momentumTarget]
    (hfactor : positionTarget.prod momentumTarget =
      phaseBoltzmannTarget potential) :
    (positionMultinomialHMC potential gradient ε L hpotential hgradient
      momentumTarget).Invariant positionTarget := by
  change (Mcmc.Kernel.liftEvolveProject
    (positionMomentumLift momentumTarget)
    (randomizedMultinomialLeapfrogKernel potential gradient ε L
      hpotential hgradient)
    (Prod.fst : PhaseSpace ι → Position ι) measurable_fst).Invariant
      positionTarget
  have htrajectory := randomizedMultinomialLeapfrogKernel_invariant
    hpotential hgradient ε L
  rw [← hfactor] at htrajectory
  unfold positionMomentumLift
  apply Mcmc.Kernel.compProdEvolveFst_invariant
  rw [Measure.compProd_const]
  exact htrajectory

/-- Multinomial HMC with the standard Gaussian momentum law. -/
noncomputable def standardPhaseMultinomialHMC
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    Kernel (PhaseSpace ι) (PhaseSpace ι) :=
  phaseMultinomialHMC potential gradient ε L hpotential hgradient
    standardMomentumMeasure

instance standardPhaseMultinomialHMC_isMarkovKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    IsMarkovKernel (standardPhaseMultinomialHMC potential gradient ε L
      hpotential hgradient) := by
  unfold standardPhaseMultinomialHMC
  infer_instance

/-- The complete standard-Gaussian phase-space HMC step preserves the
Boltzmann position target paired with standard Gaussian momentum. -/
theorem standardPhaseMultinomialHMC_invariant
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) (L : ℕ) :
    (standardPhaseMultinomialHMC potential gradient ε L hpotential hgradient).Invariant
      ((positionBoltzmannTarget potential).prod standardMomentumMeasure) := by
  letI : SFinite (positionBoltzmannTarget potential) := by
    unfold positionBoltzmannTarget
    infer_instance
  unfold standardPhaseMultinomialHMC phaseMultinomialHMC
  have hbase :
      (randomizedMultinomialLeapfrogKernel potential gradient ε L
        hpotential hgradient).Invariant (phaseBoltzmannTarget potential) :=
    randomizedMultinomialLeapfrogKernel_invariant hpotential hgradient ε L
  have htrajectory := Kernel.Invariant.smul hbase
    (standardMomentumPrefactor (ι := ι))
  rw [← positionBoltzmann_prod_standardMomentum hpotential] at htrajectory
  exact htrajectory.comp
    (momentumRefreshWith_invariant
      (positionBoltzmannTarget potential) standardMomentumMeasure)

/-- The standard-Gaussian, user-facing position-space multinomial HMC
kernel. -/
noncomputable def standardPositionMultinomialHMC
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    Kernel (Position ι) (Position ι) :=
  positionMultinomialHMC potential gradient ε L hpotential hgradient
    standardMomentumMeasure

instance standardPositionMultinomialHMC_isMarkovKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    IsMarkovKernel (standardPositionMultinomialHMC potential gradient ε L
      hpotential hgradient) := by
  unfold standardPositionMultinomialHMC
  infer_instance

/-- Standard multinomial HMC preserves the unnormalized position Boltzmann
measure `exp (-potential) dx`. -/
theorem standardPositionMultinomialHMC_invariant
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) (L : ℕ) :
    (standardPositionMultinomialHMC potential gradient ε L
      hpotential hgradient).Invariant (positionBoltzmannTarget potential) := by
  letI : SFinite (positionBoltzmannTarget potential) := by
    unfold positionBoltzmannTarget
    infer_instance
  change (Mcmc.Kernel.liftEvolveProject
    (positionMomentumLift standardMomentumMeasure)
    (randomizedMultinomialLeapfrogKernel potential gradient ε L
      hpotential hgradient)
    (Prod.fst : PhaseSpace ι → Position ι) measurable_fst).Invariant
      (positionBoltzmannTarget potential)
  have hbase :
      (randomizedMultinomialLeapfrogKernel potential gradient ε L
        hpotential hgradient).Invariant (phaseBoltzmannTarget potential) :=
    randomizedMultinomialLeapfrogKernel_invariant hpotential hgradient ε L
  have htrajectory := Kernel.Invariant.smul hbase
    (standardMomentumPrefactor (ι := ι))
  rw [← positionBoltzmann_prod_standardMomentum hpotential] at htrajectory
  unfold positionMomentumLift
  apply Mcmc.Kernel.compProdEvolveFst_invariant
  rw [Measure.compProd_const]
  exact htrajectory

end Mcmc.Hamiltonian
