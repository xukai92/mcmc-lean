import Mcmc.Hamiltonian.GeneralizedHMC
import Mcmc.Hamiltonian.HMC
import Mcmc.Hamiltonian.MomentumRefresh
import Mcmc.Riemannian.Metric
import Mathlib.Probability.Kernel.CompProdEqIff

/-!
# Classical Riemannian-manifold Hamiltonian Monte Carlo

This module formalizes the Gaussian-momentum RMHMC construction of Girolami
and Calderhead.  At position `q`, standard Gaussian momentum is transported
through the inverse factor of `G(q)⁻¹`; equivalently `p | q ~ N(0,G(q))`.
The metric log determinant and quadratic kinetic term are both retained in
the Hamiltonian, and the endpoint Metropolis theorem is an instance of the
momentum-law-independent generalized-HMC foundation.
-/

namespace Mcmc.Riemannian

open MeasureTheory ProbabilityTheory
open Mcmc.Hamiltonian Mcmc.Kernel
open scoped ENNReal ProbabilityTheory

variable {ι : Type*} [Fintype ι]

private theorem map_withDensity_comp
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (map : α → β) (μ : Measure α) (density : β → ℝ≥0∞)
    (hmap : Measurable map) (hdensity : Measurable density) :
    (μ.withDensity (density ∘ map)).map map =
      (μ.map map).withDensity density := by
  ext s hs
  rw [Measure.map_apply hmap hs,
    withDensity_apply _ (hs.preimage hmap), withDensity_apply _ hs,
    Measure.restrict_map hmap hs, lintegral_map hdensity hmap]
  rfl

/-- Classical RMHMC kinetic energy
`pᵀG(q)⁻¹p/2 + log(det G(q))/2`. -/
noncomputable def gaussianKineticEnergy (metric : FactoredMetric ι)
    (q : Position ι) (p : Momentum ι) : ℝ :=
  (1 / 2 : ℝ) * squaredEuclideanNorm (metric.factor q p) +
    (1 / 2 : ℝ) * metric.logDet q

/-- The nonseparable classical RMHMC Hamiltonian. -/
noncomputable def hamiltonian (potential : Position ι → ℝ)
    (metric : FactoredMetric ι) (z : PhaseSpace ι) : ℝ :=
  potential z.1 + gaussianKineticEnergy metric z.1 z.2

/-- The normalized conditional Gaussian density after inverse-factor
transport. -/
noncomputable def gaussianMomentumWeight (metric : FactoredMetric ι)
    (q : Position ι) (p : Momentum ι) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(1 / 2 : ℝ) * metric.logDet q)) *
    Mcmc.Kernel.isotropicGaussianPDF 1 (metric.factor q p)

/-- Position-dependent Gaussian momentum obtained from a standard Gaussian
by `p = A(q)⁻¹ z`, where `A(q)ᵀA(q)=G(q)⁻¹`. -/
noncomputable def gaussianMomentumMeasure (metric : FactoredMetric ι)
    (q : Position ι) : Measure (Momentum ι) :=
  standardMomentumMeasure.map (metric.factor q).symm

/-- The factor-volume identity identifies inverse-factor transport with the
complete normalized Gaussian density, including the determinant term. -/
theorem gaussianMomentumMeasure_eq_withDensity
    (metric : FactoredMetric ι)
    (hvolume : metric.HasCompatibleFactorVolume) (q : Position ι) :
    gaussianMomentumMeasure metric q =
      (volume : Measure (Momentum ι)).withDensity
        (gaussianMomentumWeight metric q) := by
  let f : Momentum ι → Momentum ι := (metric.factor q).symm
  let g : Momentum ι → ENNReal := fun p =>
    Mcmc.Kernel.isotropicGaussianPDF 1 (metric.factor q p)
  have hf : Measurable f := (metric.factor q).symm.continuous.measurable
  have hg : Measurable g :=
    (Mcmc.Kernel.measurable_isotropicGaussianPDF 1).comp
      (metric.factor q).continuous.measurable
  have hdensity :
      Mcmc.Kernel.isotropicGaussianPDF (ι := ι) 1 = g ∘ f := by
    funext p
    simp [g, f]
  rw [gaussianMomentumMeasure, standardMomentumMeasure,
    Mcmc.Kernel.densityTarget, hdensity]
  change (volume.withDensity (g ∘ f)).map f =
    volume.withDensity (gaussianMomentumWeight metric q)
  rw [map_withDensity_comp f volume g hf hg, hvolume q,
    withDensity_smul_measure]
  rw [← withDensity_smul _ hg]
  congr 1

/-- Explicit measurability obligation for a position-dependent Gaussian
momentum family. -/
def IsMeasurableGaussianMomentumFamily (metric : FactoredMetric ι) : Prop :=
  ∀ s : Set (Momentum ι), MeasurableSet s →
    Measurable fun q : Position ι => gaussianMomentumMeasure metric q s

/-- Classical RMHMC conditional Gaussian momentum as a mathlib kernel. -/
noncomputable def gaussianMomentumKernel (metric : FactoredMetric ι)
    (hmeasurable : IsMeasurableGaussianMomentumFamily metric) :
    Kernel (Position ι) (Momentum ι) where
  toFun := gaussianMomentumMeasure metric
  measurable' := by
    exact Measure.measurable_of_measurable_coe _ hmeasurable

instance gaussianMomentumKernel_isMarkov
    (metric : FactoredMetric ι)
    (hmeasurable : IsMeasurableGaussianMomentumFamily metric) :
    IsMarkovKernel (gaussianMomentumKernel metric hmeasurable) := by
  constructor
  intro q
  change IsProbabilityMeasure
    (standardMomentumMeasure.map (metric.factor q).symm)
  exact Measure.isProbabilityMeasure_map
    (metric.factor q).symm.continuous.measurable.aemeasurable

/-- The classical normalized phase weight. Its Metropolis ratio is exactly
the usual `exp(-H(q',p') + H(q,p))`; the omitted Gaussian prefactor is global
and cancels. -/
noncomputable def phaseWeight (potential : Position ι → ℝ)
    (metric : FactoredMetric ι) (z : PhaseSpace ι) : ℝ≥0∞ :=
  positionBoltzmannWeight potential z.1 *
    gaussianMomentumWeight metric z.1 z.2

/-- Unnormalized exponential weight written directly from the classical
RMHMC Hamiltonian. -/
noncomputable def hamiltonianWeight (potential : Position ι → ℝ)
    (metric : FactoredMetric ι) (z : PhaseSpace ι) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-hamiltonian potential metric z))

/-- The normalized phase weight differs from `exp(-H)` only by the global
standard-Gaussian prefactor. Consequently both give exactly the same
Metropolis acceptance ratio. -/
theorem phaseWeight_eq_prefactor_mul_hamiltonianWeight
    (potential : Position ι → ℝ) (metric : FactoredMetric ι)
    (z : PhaseSpace ι) :
    phaseWeight potential metric z =
      standardMomentumPrefactor (ι := ι) *
        hamiltonianWeight potential metric z := by
  rw [phaseWeight, gaussianMomentumWeight,
    isotropicGaussianPDF_one_eq_prefactor_mul_kinetic]
  unfold positionBoltzmannWeight hamiltonianWeight hamiltonian
    gaussianKineticEnergy kineticBoltzmannWeight kineticEnergy
  rw [show -(potential z.1 +
      ((1 / 2 : ℝ) * squaredEuclideanNorm (metric.factor z.1 z.2) +
        (1 / 2 : ℝ) * metric.logDet z.1)) =
      -potential z.1 + (-(1 / 2 : ℝ) * metric.logDet z.1) +
        (-(1 / 2 : ℝ) * squaredEuclideanNorm (metric.factor z.1 z.2)) by ring,
    Real.exp_add, Real.exp_add]
  rw [ENNReal.ofReal_mul
      (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le),
    ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hkinetic :
      ENNReal.ofReal
          (Real.exp (-(1 / 2 * ∑ i, (metric.factor z.1 z.2 i) ^ 2))) =
        ENNReal.ofReal (Real.exp
          (-(1 / 2) * squaredEuclideanNorm (metric.factor z.1 z.2))) := by
    congr 2
    unfold squaredEuclideanNorm euclideanInner
    ring_nf
  rw [hkinetic]
  ac_rfl

theorem phaseWeight_pos (potential : Position ι → ℝ)
    (metric : FactoredMetric ι) (z : PhaseSpace ι) :
    phaseWeight potential metric z ≠ 0 := by
  unfold phaseWeight gaussianMomentumWeight
  apply mul_ne_zero
  · exact (positionBoltzmannWeight_pos potential z.1).ne'
  apply mul_ne_zero
  · exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  · exact (Mcmc.Kernel.isotropicGaussianPDF_pos 1 (by norm_num) _).ne'

theorem phaseWeight_ne_top (potential : Position ι → ℝ)
    (metric : FactoredMetric ι) (z : PhaseSpace ι) :
    phaseWeight potential metric z ≠ ∞ := by
  unfold phaseWeight gaussianMomentumWeight
  exact ENNReal.mul_ne_top (positionBoltzmannWeight_ne_top potential z.1)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (Mcmc.Kernel.isotropicGaussianPDF_ne_top 1 _))

/-- Joint measurability of the conditional Gaussian density, stated as the
minimal public hypothesis needed for arbitrary metrics. -/
def IsMeasurableGaussianMomentumWeight (metric : FactoredMetric ι) : Prop :=
  Measurable (Function.uncurry (gaussianMomentumWeight metric))

theorem measurable_phaseWeight {potential : Position ι → ℝ}
    (hpotential : Measurable potential) (metric : FactoredMetric ι)
    (hweight : IsMeasurableGaussianMomentumWeight metric) :
    Measurable (phaseWeight potential metric) := by
  exact ((measurable_positionBoltzmannWeight hpotential).comp measurable_fst).mul
    hweight

/-- The classical Gaussian RMHMC phase target. -/
noncomputable def phaseTarget (potential : Position ι → ℝ)
    (metric : FactoredMetric ι) : Measure (PhaseSpace ι) :=
  phaseVolume.withDensity (phaseWeight potential metric)

/-- The Gaussian conditional kernel augments the ordinary position Boltzmann
target to the classical RMHMC phase target. -/
theorem position_compProd_gaussianMomentumKernel
    {potential : Position ι → ℝ} (hpotential : Measurable potential)
    (metric : FactoredMetric ι)
    (hvolume : metric.HasCompatibleFactorVolume)
    (hmeasurable : IsMeasurableGaussianMomentumFamily metric)
    (hweight : IsMeasurableGaussianMomentumWeight metric) :
    positionBoltzmannTarget potential ⊗ₘ
        gaussianMomentumKernel metric hmeasurable =
      phaseTarget potential metric := by
  let densityKernel :=
    (Kernel.const (Position ι) (volume : Measure (Momentum ι))).withDensity
      (gaussianMomentumWeight metric)
  have hk : gaussianMomentumKernel metric hmeasurable = densityKernel := by
    ext q s hs
    rw [gaussianMomentumKernel, Kernel.withDensity_apply _ hweight]
    exact congrArg (fun μ : Measure (Momentum ι) => μ s)
      (gaussianMomentumMeasure_eq_withDensity metric hvolume q)
  letI : SFinite (positionBoltzmannTarget potential) := by
    unfold positionBoltzmannTarget
    infer_instance
  letI : IsMarkovKernel densityKernel := by
    rw [← hk]
    infer_instance
  rw [hk, Measure.compProd_withDensity hweight, Measure.compProd_const,
    positionBoltzmannTarget,
    prod_withDensity_left (measurable_positionBoltzmannWeight hpotential)]
  change (phaseVolume.withDensity
      (fun z : PhaseSpace ι => positionBoltzmannWeight potential z.1)).withDensity
        (Function.uncurry (gaussianMomentumWeight metric)) = _
  rw [← withDensity_mul phaseVolume
    (show Measurable (fun z : PhaseSpace ι =>
        positionBoltzmannWeight potential z.1) from
      (measurable_positionBoltzmannWeight hpotential).comp measurable_fst)
    hweight]
  unfold phaseTarget phaseWeight
  rfl

/-- Classical endpoint-Metropolis RMHMC on phase space. -/
noncomputable def endpointMetropolis
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (potential : Position ι → ℝ) (metric : FactoredMetric ι)
    (selection : Mcmc.Relativistic.GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hmeasurable : selection.IsMeasurable) (ε : ℝ) :
    Kernel (PhaseSpace ι) (PhaseSpace ι) :=
  generalizedHmcMetropolis (phaseWeight potential metric) selection
    hmeasurable ε

theorem endpointMetropolis_isReversible
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    {potential : Position ι → ℝ} (hpotential : Measurable potential)
    (metric : FactoredMetric ι)
    (hweight : IsMeasurableGaussianMomentumWeight metric)
    (selection : Mcmc.Relativistic.GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid) (ε : ℝ) :
    (endpointMetropolis potential metric selection hvalid.measurable ε).IsReversible
      (phaseTarget potential metric) := by
  exact generalizedHmcMetropolis_isReversible _
    (measurable_phaseWeight hpotential metric hweight)
    (phaseWeight_pos potential metric) (phaseWeight_ne_top potential metric)
    selection hvalid ε

theorem endpointMetropolis_invariant
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    {potential : Position ι → ℝ} (hpotential : Measurable potential)
    (metric : FactoredMetric ι)
    (hweight : IsMeasurableGaussianMomentumWeight metric)
    (selection : Mcmc.Relativistic.GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid) (ε : ℝ) :
    (endpointMetropolis potential metric selection hvalid.measurable ε).Invariant
      (phaseTarget potential metric) := by
  exact generalizedHmcMetropolis_invariant _
    (measurable_phaseWeight hpotential metric hweight)
    (phaseWeight_pos potential metric) (phaseWeight_ne_top potential metric)
    selection hvalid ε

/-- User-facing classical RMHMC: refresh `N(0,G(q))`, execute the certified
generalized-leapfrog Metropolis transition, and discard momentum. -/
noncomputable def positionEndpointMetropolis
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (potential : Position ι → ℝ) (metric : FactoredMetric ι)
    (hmeasurableMomentum : IsMeasurableGaussianMomentumFamily metric)
    (selection : Mcmc.Relativistic.GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid) (ε : ℝ) :
    Kernel (Position ι) (Position ι) :=
  positionGeneralizedHmc (gaussianMomentumKernel metric hmeasurableMomentum)
    (endpointMetropolis potential metric selection hvalid.measurable ε)

/-- Main classical RMHMC theorem: under the exact generalized-leapfrog and
metric-volume certificates, the position transition preserves the desired
Boltzmann target.  This is an invariance theorem; ergodic convergence requires
additional irreducibility and recurrence assumptions. -/
theorem positionEndpointMetropolis_invariant
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    {potential : Position ι → ℝ} (hpotential : Measurable potential)
    (metric : FactoredMetric ι)
    (hvolume : metric.HasCompatibleFactorVolume)
    (hmeasurableMomentum : IsMeasurableGaussianMomentumFamily metric)
    (hweight : IsMeasurableGaussianMomentumWeight metric)
    (selection : Mcmc.Relativistic.GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid) (ε : ℝ) :
    (positionEndpointMetropolis potential metric hmeasurableMomentum selection
      hvalid ε).Invariant (positionBoltzmannTarget potential) := by
  letI : SFinite (positionBoltzmannTarget potential) := by
    unfold positionBoltzmannTarget
    infer_instance
  let phaseKernel := endpointMetropolis potential metric selection
    hvalid.measurable ε
  letI : IsMarkovKernel phaseKernel :=
    generalizedHmcMetropolis_isMarkov _
      (measurable_phaseWeight hpotential metric hweight) selection hvalid ε
  exact positionGeneralizedHmc_invariant (positionBoltzmannTarget potential)
    (gaussianMomentumKernel metric hmeasurableMomentum) phaseKernel
    (phaseTarget potential metric)
    (position_compProd_gaussianMomentumKernel hpotential metric hvolume
      hmeasurableMomentum hweight)
    (endpointMetropolis_invariant hpotential metric hweight selection hvalid ε)

end Mcmc.Riemannian
