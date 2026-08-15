import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mcmc.Hamiltonian.HMC
import Mcmc.Executable.Continuous.MetricHMC

/-!
# Linear transport of Gaussian momentum

The exact law used by Cholesky momentum refresh is the pushforward of a
standard multivariate Gaussian through the supplied linear factor.
-/

open MeasureTheory ProbabilityTheory

namespace Mcmc.Executable.Continuous

/-- Push a density through a measurable equivalence by composing it with the
inverse map. This is the measure-theoretic change-of-variables core used
below; the Jacobian factor enters through the pushed reference measure. -/
theorem map_withDensity_measurableEquiv
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (density : α → ENNReal)
    (hdensity : Measurable density) :
    (μ.withDensity density).map e =
      (μ.map e).withDensity (density ∘ e.symm) := by
  ext s hs
  rw [e.map_apply s, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs]
  rw [← lintegral_indicator (e.measurable hs), ← lintegral_indicator hs]
  rw [lintegral_map (μ := μ)
    ((hdensity.comp e.symm.measurable).indicator hs)
    e.measurable]
  congr 1
  funext x
  by_cases hx : e x ∈ s <;> simp [Set.indicator, hx]

theorem map_withDensity_measurableEquiv_of_map_eq_smul
    {α : Type*} [MeasurableSpace α]
    (e : α ≃ᵐ α) (μ : Measure α) (density : α → ENNReal)
    (hdensity : Measurable density) (scale : ENNReal)
    (hmap : μ.map e = scale • μ) :
    (μ.withDensity density).map e =
      scale • μ.withDensity (density ∘ e.symm) := by
  rw [map_withDensity_measurableEquiv e μ density hdensity, hmap,
    withDensity_smul_measure]

variable {E F Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [MeasurableSpace Ω]

/-- Gaussian momentum obtained by applying a Cholesky or square-root factor
to standard Gaussian noise. -/
noncomputable def linearGaussianMomentum (factor : E →L[ℝ] F) : Measure F :=
  (stdGaussian E).map factor

instance linearGaussianMomentum_isProbabilityMeasure (factor : E →L[ℝ] F) :
    IsProbabilityMeasure (linearGaussianMomentum factor) :=
  Measure.isProbabilityMeasure_map factor.continuous.aemeasurable

omit [FiniteDimensional ℝ F] in theorem hasLaw_linearGaussianMomentum
    {P : Measure Ω} [IsProbabilityMeasure P]
    {noise : Ω → E} (hnoise : HasLaw noise (stdGaussian E) P)
    (factor : E →L[ℝ] F) :
    HasLaw (fun ω => factor (noise ω)) (linearGaussianMomentum factor) P := by
  exact HasLaw.comp ⟨factor.measurable.aemeasurable, rfl⟩ hnoise

omit [BorelSpace E] [FiniteDimensional ℝ F] [BorelSpace F] in theorem
    linearGaussianMomentum_map_apply (factor : E →L[ℝ] F) :
    Measure.map factor (stdGaussian E) = linearGaussianMomentum factor := rfl

/-- Linear Gaussian transport remains Gaussian. -/
instance linearGaussianMomentum_isGaussian (factor : E →L[ℝ] F) :
    IsGaussian (linearGaussianMomentum factor) := by
  exact isGaussian_map_of_measurable factor.measurable

open Mcmc.Hamiltonian

variable {ι : Type*} [Fintype ι]

/-- The exact momentum law produced by applying a finite-dimensional
Cholesky factor to the project's standard momentum law. -/
noncomputable def choleskyMomentumMeasure
    (factor : Momentum ι →L[ℝ] Momentum ι) : Measure (Momentum ι) :=
  standardMomentumMeasure.map factor

instance choleskyMomentumMeasure_isProbabilityMeasure
    (factor : Momentum ι →L[ℝ] Momentum ι) :
    IsProbabilityMeasure (choleskyMomentumMeasure factor) :=
  Measure.isProbabilityMeasure_map factor.continuous.aemeasurable

theorem hasLaw_choleskyMomentumMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {noise : Ω → Momentum ι}
    (hnoise : HasLaw noise standardMomentumMeasure P)
    (factor : Momentum ι →L[ℝ] Momentum ι) :
    HasLaw (fun ω => factor (noise ω)) (choleskyMomentumMeasure factor) P := by
  exact HasLaw.comp ⟨factor.measurable.aemeasurable, rfl⟩ hnoise

/-- Exact density of an invertible linear transport of standard momentum,
parameterized by the Jacobian scaling of Lebesgue measure. For a matrix this
scale is `|det factor|⁻¹`. -/
theorem map_standardMomentumMeasure_measurableEquiv
    (factor : Momentum ι ≃ᵐ Momentum ι) (scale : ENNReal)
    (hvolume : (volume : Measure (Momentum ι)).map factor = scale • volume) :
    standardMomentumMeasure.map factor =
      (Mcmc.Hamiltonian.standardMomentumPrefactor (ι := ι) * scale) •
        (volume : Measure (Momentum ι)).withDensity
          (Mcmc.Hamiltonian.kineticBoltzmannWeight ∘ factor.symm) := by
  rw [Mcmc.Hamiltonian.standardMomentumMeasure_eq_smul_kinetic,
    Measure.map_smul]
  unfold Mcmc.Hamiltonian.kineticBoltzmannTarget
  rw [map_withDensity_measurableEquiv_of_map_eq_smul factor volume
    Mcmc.Hamiltonian.kineticBoltzmannWeight
    Mcmc.Hamiltonian.measurable_kineticBoltzmannWeight scale hvolume]
  rw [smul_smul]

/-- Quadratic kinetic energy induced by an invertible momentum factor. -/
noncomputable def transformedKineticEnergy
    (factor : Momentum ι ≃ᵐ Momentum ι) (p : Momentum ι) : ℝ :=
  Mcmc.Hamiltonian.kineticEnergy (factor.symm p)

theorem kineticBoltzmannWeight_comp_factor_symm
    (factor : Momentum ι ≃ᵐ Momentum ι) :
    Mcmc.Hamiltonian.kineticBoltzmannWeight ∘ factor.symm =
      Mcmc.Executable.Continuous.metricKineticBoltzmannWeight
        (transformedKineticEnergy factor) := by
  funext p
  rfl

theorem map_standardMomentumMeasure_eq_metricKineticTarget
    (factor : Momentum ι ≃ᵐ Momentum ι) (scale : ENNReal)
    (hvolume : (volume : Measure (Momentum ι)).map factor = scale • volume) :
    standardMomentumMeasure.map factor =
      (Mcmc.Hamiltonian.standardMomentumPrefactor (ι := ι) * scale) •
        Mcmc.Executable.Continuous.metricKineticBoltzmannTarget
          (transformedKineticEnergy factor) := by
  rw [map_standardMomentumMeasure_measurableEquiv factor scale hvolume,
    kineticBoltzmannWeight_comp_factor_symm]
  rfl

/-- The concrete Jacobian scale used for an invertible Cholesky matrix. This
is mathlib's finite-dimensional Lebesgue change-of-variables theorem, exposed
with the exact normalization consumed by the transport result above. -/
theorem choleskyMatrix_map_volume [DecidableEq ι]
    (factor : Matrix ι ι ℝ) (hfactor : Matrix.det factor ≠ 0) :
    Measure.map (Matrix.toLin' factor) (volume : Measure (Momentum ι)) =
      ENNReal.ofReal (|(Matrix.det factor)⁻¹|) • volume := by
  exact Real.map_matrix_volume_pi_eq_smul_volume_pi hfactor

/-- Fully instantiated refreshed position-kernel invariance for an invertible
Gaussian momentum factor. The inverse normalization on position cancels the
Jacobian-adjusted momentum normalization exactly. -/
theorem endpointMetricHmcPositionKernel_invariant_cholesky
    (metric : ConstantMetric ι) (factor : Momentum ι ≃ᵐ Momentum ι)
    (scale : ENNReal)
    (hvolume : (volume : Measure (Momentum ι)).map factor = scale • volume)
    (hnormalization :
      Mcmc.Hamiltonian.standardMomentumPrefactor (ι := ι) * scale ≠ 0)
    (hnormalization_top :
      Mcmc.Hamiltonian.standardMomentumPrefactor (ι := ι) * scale ≠
        (⊤ : ENNReal))
    {potential : Position ι → ℝ} {gradient : Position ι → Momentum ι}
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) (steps : Nat) :
    (endpointMetricHmcPositionKernel metric potential
      (transformedKineticEnergy factor) gradient
      (standardMomentumMeasure.map factor) ε steps hpotential
      (Mcmc.Hamiltonian.measurable_kineticEnergy.comp factor.symm.measurable)
      hgradient).Invariant
      ((Mcmc.Hamiltonian.standardMomentumPrefactor (ι := ι) * scale)⁻¹ •
        metricPositionBoltzmannTarget potential) := by
  let normalization :=
    Mcmc.Hamiltonian.standardMomentumPrefactor (ι := ι) * scale
  change normalization ≠ 0 at hnormalization
  change normalization ≠ (⊤ : ENNReal) at hnormalization_top
  letI : IsProbabilityMeasure (standardMomentumMeasure.map factor) :=
    Measure.isProbabilityMeasure_map factor.measurable.aemeasurable
  letI : SFinite (metricPositionBoltzmannTarget potential) := by
    unfold metricPositionBoltzmannTarget
    infer_instance
  letI : SFinite (normalization⁻¹ • metricPositionBoltzmannTarget potential) :=
    inferInstance
  letI : SFinite
      (metricKineticBoltzmannTarget (transformedKineticEnergy factor)) := by
    unfold metricKineticBoltzmannTarget
    infer_instance
  apply endpointMetricHmcPositionKernel_invariant metric hpotential
    (Mcmc.Hamiltonian.measurable_kineticEnergy.comp factor.symm.measurable)
    hgradient (standardMomentumMeasure.map factor)
  rw [map_standardMomentumMeasure_eq_metricKineticTarget factor scale hvolume]
  change (normalization⁻¹ • metricPositionBoltzmannTarget potential).prod
      (normalization • metricKineticBoltzmannTarget
        (transformedKineticEnergy factor)) = _
  rw [Measure.prod_smul_right, Measure.prod_smul_left, smul_smul,
    ENNReal.mul_inv_cancel hnormalization hnormalization_top, one_smul]
  exact (metricPhaseBoltzmannTarget_eq_prod hpotential
    (Mcmc.Hamiltonian.measurable_kineticEnergy.comp
      factor.symm.measurable)).symm

end Mcmc.Executable.Continuous
