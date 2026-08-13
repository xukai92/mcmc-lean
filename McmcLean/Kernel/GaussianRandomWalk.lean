import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import McmcLean.Kernel.RandomWalkMetropolisHastings

/-!
# Finite-dimensional Gaussian random-walk Metropolis--Hastings

This module supplies the finite-dimensional Gaussian RWMH specialization used
by the coupled-HMC paper.  On `ι → ℝ`, the increment density is the product of
centered one-dimensional Gaussian densities. Its measurability, normalization,
evenness, and pointwise finiteness are proved from mathlib's Gaussian integral
and finite-product Fubini theorem.
-/

open MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace McmcLean.Kernel

open ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- Product density of independent centered Gaussian coordinates with common
variance. -/
noncomputable def isotropicGaussianPDF (variance : ℝ≥0) (z : ι → ℝ) : ENNReal :=
  ∏ i, gaussianPDF 0 variance (z i)

theorem measurable_isotropicGaussianPDF (variance : ℝ≥0) :
    Measurable (isotropicGaussianPDF (ι := ι) variance) := by
  unfold isotropicGaussianPDF
  fun_prop

theorem isotropicGaussianPDF_eq_ofReal_prod (variance : ℝ≥0) (z : ι → ℝ) :
    isotropicGaussianPDF variance z =
      ENNReal.ofReal (∏ i, gaussianPDFReal 0 variance (z i)) := by
  rw [isotropicGaussianPDF, ENNReal.ofReal_prod_of_nonneg]
  · rfl
  · exact fun i _ => gaussianPDFReal_nonneg 0 variance (z i)

/-- The finite-dimensional product Gaussian density is continuous. -/
theorem continuous_isotropicGaussianPDF (variance : ℝ≥0) :
    Continuous (isotropicGaussianPDF (ι := ι) variance) := by
  rw [show isotropicGaussianPDF (ι := ι) variance =
      fun z => ENNReal.ofReal (∏ i, gaussianPDFReal 0 variance (z i)) by
    funext z
    exact isotropicGaussianPDF_eq_ofReal_prod variance z]
  apply ENNReal.continuous_ofReal.comp
  apply continuous_finsetProd
  intro i _hi
  have hpdf : Continuous (gaussianPDFReal 0 variance) := by
    unfold gaussianPDFReal
    fun_prop
  exact hpdf.comp (continuous_apply i)

/-- The product Gaussian density integrates to one in every finite
dimension. -/
theorem lintegral_isotropicGaussianPDF_eq_one
    (variance : ℝ≥0) (hvariance : variance ≠ 0) :
    ∫⁻ z : ι → ℝ, isotropicGaussianPDF variance z = 1 := by
  let f : (ι → ℝ) → ℝ := fun z => ∏ i, gaussianPDFReal 0 variance (z i)
  have hf : Integrable f (volume : Measure (ι → ℝ)) := by
    rw [volume_pi]
    exact Integrable.fintype_prod fun _ => integrable_gaussianPDFReal 0 variance
  have hnonneg : 0 ≤ᵐ[volume] f := ae_of_all _ fun z =>
    Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 variance (z i)
  simp_rw [isotropicGaussianPDF_eq_ofReal_prod]
  change ∫⁻ z : ι → ℝ, ENNReal.ofReal (f z) = 1
  rw [← ofReal_integral_eq_lintegral_ofReal hf hnonneg]
  change ENNReal.ofReal (∫ z : ι → ℝ, ∏ i, gaussianPDFReal 0 variance (z i)) = 1
  rw [volume_pi, integral_fintype_prod_eq_prod]
  simp [integral_gaussianPDFReal_eq_one 0 hvariance]

/-- The centered product Gaussian density is even. -/
theorem isotropicGaussianPDF_even (variance : ℝ≥0) (z : ι → ℝ) :
    isotropicGaussianPDF variance (-z) = isotropicGaussianPDF variance z := by
  unfold isotropicGaussianPDF
  apply Finset.prod_congr rfl
  intro i _
  simpa using gaussianPDF_zero_even variance (z i)

theorem isotropicGaussianPDF_ne_top (variance : ℝ≥0) (z : ι → ℝ) :
    isotropicGaussianPDF variance z ≠ ∞ := by
  unfold isotropicGaussianPDF
  exact ENNReal.prod_ne_top fun i _ => gaussianPDF_ne_top

/-- A nondegenerate product Gaussian density is strictly positive
everywhere. -/
theorem isotropicGaussianPDF_pos (variance : ℝ≥0) (hvariance : variance ≠ 0)
    (z : ι → ℝ) :
    0 < isotropicGaussianPDF variance z := by
  unfold isotropicGaussianPDF
  rw [pos_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr fun i _ =>
    (gaussianPDF_pos 0 hvariance (z i)).ne'

/-- The real density of a nondegenerate one-dimensional centered Gaussian,
multiplied by the identity, is integrable. -/
theorem integrable_gaussianPDFReal_mul_id
    (variance : ℝ≥0) (hvariance : variance ≠ 0) :
    Integrable (fun x : ℝ => gaussianPDFReal 0 variance x * x) := by
  have hid : Integrable id (gaussianReal 0 variance) :=
    memLp_one_iff_integrable.mp
      (memLp_id_gaussianReal' (μ := 0) (v := variance) 1 ENNReal.one_ne_top)
  rw [gaussianReal_of_var_ne_zero 0 hvariance] at hid
  have hweighted :=
    (integrable_withDensity_iff
      (measurable_gaussianPDF 0 variance)
      (ae_of_all _ fun x =>
        (show gaussianPDF 0 variance x ≠ ∞ from gaussianPDF_ne_top).lt_top)).mp hid
  simpa only [id_eq, toReal_gaussianPDF, mul_comm] using hweighted

/-- The identity map is integrable under the finite-dimensional product
Gaussian measure represented by `isotropicGaussianPDF`. -/
theorem integrable_id_withDensity_isotropicGaussianPDF
    (variance : ℝ≥0) (hvariance : variance ≠ 0) :
    Integrable id
      ((volume : Measure (ι → ℝ)).withDensity
        (isotropicGaussianPDF variance)) := by
  classical
  rw [integrable_withDensity_iff_integrable_smul'
    (measurable_isotropicGaussianPDF variance)
    (ae_of_all _ fun z => (isotropicGaussianPDF_ne_top variance z).lt_top)]
  rw [volume_pi]
  apply Integrable.of_eval
  intro i
  let factors : ι → ℝ → ℝ := fun j t =>
    if j = i then gaussianPDFReal 0 variance t * t
      else gaussianPDFReal 0 variance t
  have hprod : Integrable
      (fun z : ι → ℝ => ∏ j, factors j (z j))
      (Measure.pi fun _ : ι => (volume : Measure ℝ)) := by
    apply Integrable.fintype_prod
    intro j
    by_cases hji : j = i
    · simpa [factors, hji] using
        integrable_gaussianPDFReal_mul_id variance hvariance
    · simpa [factors, hji] using integrable_gaussianPDFReal 0 variance
  apply hprod.congr
  filter_upwards [] with z
  simp only [Pi.smul_apply, id_eq]
  rw [isotropicGaussianPDF_eq_ofReal_prod,
    ENNReal.toReal_ofReal (Finset.prod_nonneg fun j _ =>
      gaussianPDFReal_nonneg 0 variance (z j))]
  calc
    (∏ j, factors j (z j)) =
        ∏ j, if j = i then gaussianPDFReal 0 variance (z j) * z j
          else gaussianPDFReal 0 variance (z j) := by rfl
    _ = ∏ j, gaussianPDFReal 0 variance (z j) *
          (if j = i then z i else 1) := by
      apply Finset.prod_congr rfl
      intro j _hj
      by_cases hji : j = i <;> simp [hji]
    _ = (∏ j, gaussianPDFReal 0 variance (z j)) *
        ∏ j, (if j = i then z i else 1) :=
      Finset.prod_mul_distrib
    _ = (∏ j, gaussianPDFReal 0 variance (z j)) * z i := by
      simp
    _ = (∏ j, gaussianPDFReal 0 variance (z j)) • z i := by
      simp [smul_eq_mul]

/-- The first norm moment of the finite-dimensional isotropic Gaussian noise
density is finite. -/
theorem lintegral_norm_mul_isotropicGaussianPDF_ne_top
    (variance : ℝ≥0) (hvariance : variance ≠ 0) :
    (∫⁻ z : ι → ℝ, ENNReal.ofReal ‖z‖ * isotropicGaussianPDF variance z) ≠ ∞ := by
  have hid := integrable_id_withDensity_isotropicGaussianPDF
    (ι := ι) variance hvariance
  have hfinite :
      (∫⁻ z : ι → ℝ, ENNReal.ofReal ‖id z‖
        ∂(volume : Measure (ι → ℝ)).withDensity
          (isotropicGaussianPDF variance)) < ∞ :=
    (hasFiniteIntegral_iff_norm id).mp hid.hasFiniteIntegral
  simp only [id_eq] at hfinite
  have heq := lintegral_withDensity_eq_lintegral_mul
    (volume : Measure (ι → ℝ))
    (measurable_isotropicGaussianPDF variance)
    (ENNReal.continuous_ofReal.comp continuous_norm).measurable
  change (∫⁻ z : ι → ℝ, ENNReal.ofReal ‖z‖
      ∂(volume : Measure (ι → ℝ)).withDensity
        (isotropicGaussianPDF variance)) =
    ∫⁻ z : ι → ℝ, isotropicGaussianPDF variance z * ENNReal.ofReal ‖z‖
      ∂volume at heq
  calc
    (∫⁻ z : ι → ℝ, ENNReal.ofReal ‖z‖ * isotropicGaussianPDF variance z) =
        ∫⁻ z : ι → ℝ, ENNReal.ofReal ‖z‖
          ∂(volume : Measure (ι → ℝ)).withDensity
            (isotropicGaussianPDF variance) := by
      rw [heq]
      congr 1
      funext z
      exact mul_comm _ _
    _ ≠ ∞ := hfinite.ne

/-- First norm moment of the isotropic Gaussian increment density. -/
noncomputable def isotropicGaussianFirstNormMoment
    (variance : ℝ≥0) : ENNReal :=
  ∫⁻ z : ι → ℝ, ENNReal.ofReal ‖z‖ * isotropicGaussianPDF variance z

theorem isotropicGaussianFirstNormMoment_ne_top
    (variance : ℝ≥0) (hvariance : variance ≠ 0) :
    isotropicGaussianFirstNormMoment (ι := ι) variance ≠ ∞ := by
  exact lintegral_norm_mul_isotropicGaussianPDF_ne_top variance hvariance

/-- Gaussian RWMH on an arbitrary finite-dimensional coordinate space. -/
noncomputable def euclideanGaussianRandomWalkMetropolisHastings
    (weight : (ι → ℝ) → ENNReal) (variance : ℝ≥0)
    (hvariance : variance ≠ 0) :
    ProbabilityTheory.Kernel (ι → ℝ) (ι → ℝ) :=
  randomWalkMetropolisHastings volume weight
    (isotropicGaussianPDF variance)
    (measurable_isotropicGaussianPDF variance)
    (lintegral_isotropicGaussianPDF_eq_one variance hvariance)

/-- Finite-dimensional Gaussian RWMH is a Markov kernel. -/
theorem euclideanGaussianRandomWalkMetropolisHastings_isMarkov
    (weight : (ι → ℝ) → ENNReal) (variance : ℝ≥0)
    (hvariance : variance ≠ 0) (hweight : Measurable weight) :
    IsMarkovKernel
      (euclideanGaussianRandomWalkMetropolisHastings weight variance hvariance) :=
  randomWalkMetropolisHastings_isMarkov volume weight
    (isotropicGaussianPDF variance) hweight
    (measurable_isotropicGaussianPDF variance)
    (lintegral_isotropicGaussianPDF_eq_one variance hvariance)

/-- Any observable whose change is bounded by the norm of the Gaussian
increment satisfies a concrete finite affine growth bound under the verified
Gaussian RWMH kernel. -/
theorem lintegral_euclideanGaussianRandomWalkMetropolisHastings_le
    (weight : (ι → ℝ) → ENNReal) (variance : ℝ≥0)
    (hvariance : variance ≠ 0) (hweight : Measurable weight)
    {f : (ι → ℝ) → ENNReal} (hf : Measurable f)
    (htranslate : ∀ x y, f y ≤ f x + ENNReal.ofReal ‖y - x‖)
    (x : ι → ℝ) :
    (∫⁻ y, f y ∂euclideanGaussianRandomWalkMetropolisHastings
        weight variance hvariance x) ≤
      2 * f x + isotropicGaussianFirstNormMoment (ι := ι) variance := by
  simpa only [euclideanGaussianRandomWalkMetropolisHastings,
    isotropicGaussianFirstNormMoment, Function.comp_apply] using
    lintegral_randomWalkMetropolisHastings_le_two_mul_add_cost
      volume weight (isotropicGaussianPDF variance) hweight
      (measurable_isotropicGaussianPDF variance)
      (lintegral_isotropicGaussianPDF_eq_one variance hvariance) hf
      (ENNReal.continuous_ofReal.comp continuous_norm).measurable
      htranslate x

/-- Finite-dimensional Gaussian RWMH satisfies detailed balance. -/
theorem euclideanGaussianRandomWalkMetropolisHastings_isReversible
    (weight : (ι → ℝ) → ENNReal) (variance : ℝ≥0)
    (hvariance : variance ≠ 0) (hweight : Measurable weight)
    (hweightFinite : ∀ x, weight x ≠ ∞) :
    (euclideanGaussianRandomWalkMetropolisHastings weight variance
      hvariance).IsReversible (densityTarget volume weight) := by
  apply randomWalkMetropolisHastings_isReversible volume weight
    (isotropicGaussianPDF variance) hweight
    (measurable_isotropicGaussianPDF variance)
    (lintegral_isotropicGaussianPDF_eq_one variance hvariance)
  intro x y
  exact ENNReal.mul_ne_top (hweightFinite x)
    (isotropicGaussianPDF_ne_top variance (y - x))

/-- Finite-dimensional Gaussian RWMH preserves its target measure. -/
theorem euclideanGaussianRandomWalkMetropolisHastings_invariant
    (weight : (ι → ℝ) → ENNReal) (variance : ℝ≥0)
    (hvariance : variance ≠ 0) (hweight : Measurable weight)
    (hweightFinite : ∀ x, weight x ≠ ∞) :
    (euclideanGaussianRandomWalkMetropolisHastings weight variance
      hvariance).Invariant (densityTarget volume weight) := by
  apply randomWalkMetropolisHastings_invariant volume weight
    (isotropicGaussianPDF variance) hweight
    (measurable_isotropicGaussianPDF variance)
    (lintegral_isotropicGaussianPDF_eq_one variance hvariance)
  intro x y
  exact ENNReal.mul_ne_top (hweightFinite x)
    (isotropicGaussianPDF_ne_top variance (y - x))

end McmcLean.Kernel
