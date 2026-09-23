import Mcmc.Executable.Continuous.RWMH
import Mcmc.Kernel.Langevin

/-!
# Scalar and vector MALA IR-kernel refinement

Proves that the scalar and vector MALA command programs (`scalar_mala_step!`,
`vector_mala_step!`) have exact kernel semantics equal to the density-based
Metropolis-adjusted Langevin transition with Gaussian proposals, and inherit
their target-invariance theorems.

The key difficulty relative to RWMH is the asymmetric proposal: the acceptance
ratio includes a correction for the gradient-dependent drift, captured by the
squared forward and reverse residuals. The vector case lifts the scalar pattern
to `ι → ℝ` state spaces with isotropic Gaussian noise and summed squared norms.
-/

open MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory Real

namespace Mcmc.Executable.Continuous

open ProbabilityTheory
open Mcmc.Executable

/-- Scalar MALA drift: `(variance / 2) * gradient(x)`. -/
noncomputable def scalarMalaDrift (gradient : ℝ → ℝ) (variance : ℝ≥0) (x : ℝ) : ℝ :=
  ((variance : ℝ) / 2) * gradient x

theorem measurable_scalarMalaDrift {gradient : ℝ → ℝ}
    (hgradient : Measurable gradient) (variance : ℝ≥0) :
    Measurable (scalarMalaDrift gradient variance) :=
  hgradient.const_mul _

/-- Scalar Langevin proposal density: a Gaussian centred at `x + drift(x)`. -/
noncomputable def scalarLangevinProposalDensity
    (gradient : ℝ → ℝ) (variance : ℝ≥0) (x y : ℝ) : ENNReal :=
  gaussianPDF 0 variance (y - x - scalarMalaDrift gradient variance x)

theorem measurable_uncurry_scalarLangevinProposalDensity
    {gradient : ℝ → ℝ} (hgradient : Measurable gradient) (variance : ℝ≥0) :
    Measurable (Function.uncurry
      (scalarLangevinProposalDensity gradient variance)) := by
  apply (measurable_gaussianPDF 0 variance).comp
  exact (measurable_snd.sub measurable_fst).sub
    ((measurable_scalarMalaDrift hgradient variance).comp measurable_fst)

theorem scalarLangevinProposalDensity_normalized
    (gradient : ℝ → ℝ) (variance : ℝ≥0) (hvariance : variance ≠ 0) (x : ℝ) :
    ∫⁻ y, scalarLangevinProposalDensity gradient variance x y ∂volume = 1 := by
  have hrw : ∀ y, scalarLangevinProposalDensity gradient variance x y =
      Mcmc.Kernel.randomWalkProposalDensity (gaussianPDF 0 variance)
        (x + scalarMalaDrift gradient variance x) y := by
    intro y
    simp only [scalarLangevinProposalDensity, Mcmc.Kernel.randomWalkProposalDensity]
    congr 1; ring
  simp_rw [hrw]
  rw [Mcmc.Kernel.randomWalkProposalDensity_lintegral volume
    (measurable_gaussianPDF 0 variance),
    lintegral_gaussianPDF_eq_one 0 hvariance]

/-- Real acceptance threshold computed by the scalar MALA command program.
Mirrors the body of `scalar_mala_step!` in CompilerIR.lean. -/
noncomputable def malaLogDensityAcceptance
    (logDensity gradient : ℝ → ℝ) (stepSize : ℝ)
    (current proposed : ℝ) : ℝ :=
  let variance := stepSize ^ 2
  let halfVariance := variance / 2
  let forwardResidual := proposed - (current + halfVariance * gradient current)
  let reverseResidual := current - (proposed + halfVariance * gradient proposed)
  let logRatio := (logDensity proposed - logDensity current) +
    (forwardResidual ^ 2 - reverseResidual ^ 2) / (2 * variance)
  Real.exp (min 0 logRatio)

theorem malaLogDensityAcceptance_pos (logDensity gradient : ℝ → ℝ)
    (stepSize : ℝ) (current proposed : ℝ) :
    0 < malaLogDensityAcceptance logDensity gradient stepSize
      current proposed :=
  Real.exp_pos _

theorem malaLogDensityAcceptance_le_one (logDensity gradient : ℝ → ℝ)
    (stepSize : ℝ) (current proposed : ℝ) :
    malaLogDensityAcceptance logDensity gradient stepSize
      current proposed ≤ 1 := by
  unfold malaLogDensityAcceptance
  rw [← Real.exp_zero]
  exact Real.exp_le_exp.mpr (min_le_left _ _)

private lemma min_one_exp_eq_exp_min_zero (a : ℝ) :
    min 1 (Real.exp a) = Real.exp (min 0 a) := by
  by_cases ha : a ≤ 0
  · rw [min_eq_right (Real.exp_le_one_iff.mpr ha), min_eq_right ha]
  · simp only [not_le] at ha
    rw [min_eq_left (Real.one_le_exp_iff.mpr (le_of_lt ha)),
      min_eq_left (le_of_lt ha), Real.exp_zero]

/-- The program's real MALA acceptance threshold equals the zero-safe density
acceptance used by the verified MALA kernel. -/
theorem ofReal_malaAcceptance_eq_densityAcceptance
    (logDensity gradient : ℝ → ℝ) (stepSize : ℝ) (hstepSize : 0 < stepSize)
    (current proposed : ℝ) :
    ENNReal.ofReal (malaLogDensityAcceptance logDensity gradient stepSize
      current proposed) =
      Mcmc.Kernel.densityAcceptance (logDensityWeight logDensity)
        (scalarLangevinProposalDensity gradient (scaleVariance stepSize))
        current proposed := by
  set v := scaleVariance stepSize with hv_def
  have hv_ne : v ≠ 0 := scaleVariance_ne_zero hstepSize
  -- Real-valued forward and reverse density flows
  set fwd_r := Real.exp (logDensity current) *
    gaussianPDFReal 0 v (proposed - current -
      scalarMalaDrift gradient v current)
  set rev_r := Real.exp (logDensity proposed) *
    gaussianPDFReal 0 v (current - proposed -
      scalarMalaDrift gradient v proposed)
  have hfwd_pos : 0 < fwd_r :=
    mul_pos (Real.exp_pos _) (gaussianPDFReal_pos 0 v _ hv_ne)
  have hrev_nonneg : 0 ≤ rev_r :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) (gaussianPDFReal_nonneg 0 v _)
  -- Identify ENNReal forward flows with ofReal of positive reals
  have hfwd_ofReal : Mcmc.Kernel.forwardDensityFlow (logDensityWeight logDensity)
      (scalarLangevinProposalDensity gradient v) current proposed =
      ENNReal.ofReal fwd_r := by
    simp only [Mcmc.Kernel.forwardDensityFlow, logDensityWeight,
      scalarLangevinProposalDensity, gaussianPDF]
    exact (ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))).symm
  have hrev_ofReal : Mcmc.Kernel.forwardDensityFlow (logDensityWeight logDensity)
      (scalarLangevinProposalDensity gradient v) proposed current =
      ENNReal.ofReal rev_r := by
    simp only [Mcmc.Kernel.forwardDensityFlow, logDensityWeight,
      scalarLangevinProposalDensity, gaussianPDF]
    exact (ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))).symm
  -- Forward flow is nonzero
  have hfwd_ne : Mcmc.Kernel.forwardDensityFlow (logDensityWeight logDensity)
      (scalarLangevinProposalDensity gradient v) current proposed ≠ 0 := by
    rw [hfwd_ofReal]; exact (ENNReal.ofReal_pos.mpr hfwd_pos).ne'
  -- Rewrite densityAcceptance into ofReal form
  rw [Mcmc.Kernel.densityAcceptance, if_neg hfwd_ne,
    Mcmc.Kernel.symmetricAcceptedFlow, hfwd_ofReal, hrev_ofReal,
    ← ENNReal.ofReal_min, ← ENNReal.ofReal_div_of_pos hfwd_pos]
  apply congrArg ENNReal.ofReal
  -- The real-valued ratio rev_r / fwd_r = exp(logRatio)
  set logRatio := (logDensity proposed - logDensity current) +
    ((proposed - current - scalarMalaDrift gradient v current) ^ 2 -
     (current - proposed - scalarMalaDrift gradient v proposed) ^ 2) /
    (2 * (v : ℝ)) with hlogRatio_def
  have hratio : rev_r / fwd_r = Real.exp logRatio := by
    simp only [fwd_r, rev_r, gaussianPDFReal, sub_zero, hlogRatio_def]
    have hc_pos : 0 < (Real.sqrt (2 * ↑π * ↑v))⁻¹ := by positivity
    rw [show Real.exp (logDensity proposed) *
          ((Real.sqrt (2 * ↑π * ↑v))⁻¹ *
            Real.exp (-((current - proposed - scalarMalaDrift gradient v proposed) ^ 2) /
              (2 * ↑v))) =
        (Real.sqrt (2 * ↑π * ↑v))⁻¹ *
          (Real.exp (logDensity proposed) *
            Real.exp (-((current - proposed - scalarMalaDrift gradient v proposed) ^ 2) /
              (2 * ↑v))) by ring,
      show Real.exp (logDensity current) *
          ((Real.sqrt (2 * ↑π * ↑v))⁻¹ *
            Real.exp (-((proposed - current - scalarMalaDrift gradient v current) ^ 2) /
              (2 * ↑v))) =
        (Real.sqrt (2 * ↑π * ↑v))⁻¹ *
          (Real.exp (logDensity current) *
            Real.exp (-((proposed - current - scalarMalaDrift gradient v current) ^ 2) /
              (2 * ↑v))) by ring,
      mul_div_mul_left _ _ hc_pos.ne',
      ← Real.exp_add, ← Real.exp_add, ← Real.exp_sub]
    congr 1; ring
  -- Connect malaLogDensityAcceptance to exp(min 0 logRatio)
  have hv_val : (v : ℝ) = stepSize ^ 2 := rfl
  have hmala_eq : malaLogDensityAcceptance logDensity gradient stepSize
      current proposed = Real.exp (min 0 logRatio) := by
    simp only [malaLogDensityAcceptance, hlogRatio_def, scalarMalaDrift, hv_val]
    congr 1; congr 1; ring
  rw [hmala_eq]
  -- Case analysis on the sign of logRatio
  by_cases hle : 0 ≤ logRatio
  · -- logRatio ≥ 0: fwd_r ≤ rev_r, acceptance = 1
    have hfwd_le_rev : fwd_r ≤ rev_r := by
      have h1 : 1 ≤ rev_r / fwd_r := hratio ▸ Real.one_le_exp_iff.mpr hle
      rwa [le_div_iff₀ hfwd_pos, one_mul] at h1
    rw [min_eq_left hfwd_le_rev, div_self hfwd_pos.ne',
      min_eq_left hle, Real.exp_zero]
  · -- logRatio < 0: rev_r ≤ fwd_r, acceptance = exp(logRatio)
    simp only [not_le] at hle
    have hrev_le_fwd : rev_r ≤ fwd_r := by
      have h1 : rev_r / fwd_r ≤ 1 :=
        hratio ▸ Real.exp_le_one_iff.mpr (le_of_lt hle)
      rwa [div_le_iff₀ hfwd_pos, one_mul] at h1
    rw [min_eq_right hrev_le_fwd, hratio,
      min_eq_right (le_of_lt hle)]

/-- Exact verified scalar MALA kernel: density-based MH with the Langevin
proposal and the zero-safe density-ratio acceptance rule. -/
noncomputable def scalarMalaKernel (logDensity gradient : ℝ → ℝ)
    (stepSize : ℝ) (hstepSize : 0 < stepSize)
    (hgradient : Measurable gradient) : Kernel ℝ ℝ :=
  Mcmc.Kernel.densityMetropolisHastings volume (logDensityWeight logDensity)
    (scalarLangevinProposalDensity gradient (scaleVariance stepSize))
    (measurable_uncurry_scalarLangevinProposalDensity hgradient _)
    (scalarLangevinProposalDensity_normalized gradient _
      (scaleVariance_ne_zero hstepSize))

/-- Exact kernel semantics of the scalar MALA command program: its Langevin
proposal is completed by the program's log-density acceptance threshold
and rejection-at-current-state branch. -/
noncomputable def scalarMalaProgramKernel (logDensity gradient : ℝ → ℝ)
    (stepSize : ℝ) (hstepSize : 0 < stepSize)
    (hgradient : Measurable gradient) : Kernel ℝ ℝ := by
  let v := scaleVariance stepSize
  let q := scalarLangevinProposalDensity gradient v
  let Q := Mcmc.Kernel.densityProposal volume q
  letI : IsMarkovKernel Q :=
    Mcmc.Kernel.densityProposal_isMarkov volume
      (measurable_uncurry_scalarLangevinProposalDensity hgradient v)
      (scalarLangevinProposalDensity_normalized gradient v
        (scaleVariance_ne_zero hstepSize))
  exact Mcmc.Kernel.metropolisHastings Q fun current proposed =>
    ENNReal.ofReal (malaLogDensityAcceptance logDensity gradient stepSize
      current proposed)

/-- Full refinement: the exact denotation of the scalar MALA command program
is the existing verified density-based Metropolis-adjusted Langevin kernel. -/
theorem scalarMalaProgramKernel_refines (logDensity gradient : ℝ → ℝ)
    (stepSize : ℝ) (hstepSize : 0 < stepSize)
    (hgradient : Measurable gradient) :
    scalarMalaProgramKernel logDensity gradient stepSize hstepSize hgradient =
      scalarMalaKernel logDensity gradient stepSize hstepSize hgradient := by
  unfold scalarMalaProgramKernel scalarMalaKernel
  unfold Mcmc.Kernel.densityMetropolisHastings
  dsimp only
  congr 1
  funext current proposed
  exact ofReal_malaAcceptance_eq_densityAcceptance logDensity gradient stepSize
    hstepSize current proposed

/-- The scalar MALA kernel preserves the measure with density
`exp ∘ logDensity` with respect to Lebesgue measure. -/
theorem scalarMalaKernel_invariant (logDensity gradient : ℝ → ℝ)
    (stepSize : ℝ) (hstepSize : 0 < stepSize)
    (hlogDensity : Measurable logDensity) (hgradient : Measurable gradient)
    (hfinite : ∀ x y, Mcmc.Kernel.forwardDensityFlow
      (logDensityWeight logDensity)
      (scalarLangevinProposalDensity gradient (scaleVariance stepSize))
      x y ≠ ∞) :
    (scalarMalaKernel logDensity gradient stepSize hstepSize
      hgradient).Invariant
      (Mcmc.Kernel.densityTarget volume (logDensityWeight logDensity)) := by
  exact Mcmc.Kernel.densityMetropolisHastings_invariant volume
    (logDensityWeight logDensity)
    (scalarLangevinProposalDensity gradient (scaleVariance stepSize))
    (measurable_logDensityWeight hlogDensity)
    (measurable_uncurry_scalarLangevinProposalDensity hgradient _)
    (scalarLangevinProposalDensity_normalized gradient _
      (scaleVariance_ne_zero hstepSize))
    hfinite

section VectorMALA

variable {ι : Type*} [Fintype ι]

/-- Positive finite target weight represented by a real log density on `ι → ℝ`. -/
noncomputable def vectorLogDensityWeight (logDensity : (ι → ℝ) → ℝ)
    (x : ι → ℝ) : ENNReal :=
  ENNReal.ofReal (Real.exp (logDensity x))

theorem measurable_vectorLogDensityWeight {logDensity : (ι → ℝ) → ℝ}
    (hlogDensity : Measurable logDensity) :
    Measurable (vectorLogDensityWeight logDensity) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hlogDensity)

theorem vectorLogDensityWeight_ne_zero (logDensity : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    vectorLogDensityWeight logDensity x ≠ 0 := by
  simp [vectorLogDensityWeight, Real.exp_pos]

theorem vectorLogDensityWeight_ne_top (logDensity : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    vectorLogDensityWeight logDensity x ≠ ∞ := by
  simp [vectorLogDensityWeight]

/-- Real acceptance threshold computed by the vector MALA command program.
Mirrors the body of `vector_mala_step!` in CompilerIR.lean. -/
noncomputable def vectorMalaLogDensityAcceptance
    (logDensity : (ι → ℝ) → ℝ) (gradient : (ι → ℝ) → (ι → ℝ))
    (stepSize : ℝ) (current proposed : ι → ℝ) : ℝ :=
  let variance := stepSize ^ 2
  let halfVariance := variance / 2
  let forwardResidual := fun i =>
    proposed i - (current i + halfVariance * gradient current i)
  let reverseResidual := fun i =>
    current i - (proposed i + halfVariance * gradient proposed i)
  let forwardNormSq := ∑ i, forwardResidual i ^ 2
  let reverseNormSq := ∑ i, reverseResidual i ^ 2
  let logRatio := (logDensity proposed - logDensity current) +
    (forwardNormSq - reverseNormSq) / (2 * variance)
  Real.exp (min 0 logRatio)

theorem vectorMalaLogDensityAcceptance_pos (logDensity : (ι → ℝ) → ℝ)
    (gradient : (ι → ℝ) → (ι → ℝ)) (stepSize : ℝ) (current proposed : ι → ℝ) :
    0 < vectorMalaLogDensityAcceptance logDensity gradient stepSize
      current proposed :=
  Real.exp_pos _

theorem vectorMalaLogDensityAcceptance_le_one (logDensity : (ι → ℝ) → ℝ)
    (gradient : (ι → ℝ) → (ι → ℝ)) (stepSize : ℝ) (current proposed : ι → ℝ) :
    vectorMalaLogDensityAcceptance logDensity gradient stepSize
      current proposed ≤ 1 := by
  unfold vectorMalaLogDensityAcceptance
  rw [← Real.exp_zero]
  exact Real.exp_le_exp.mpr (min_le_left _ _)

/-- The program's real vector MALA acceptance threshold equals the zero-safe
density acceptance used by the verified MALA kernel. -/
theorem ofReal_vectorMalaAcceptance_eq_densityAcceptance
    (logDensity : (ι → ℝ) → ℝ) (gradient : (ι → ℝ) → (ι → ℝ))
    (stepSize : ℝ) (hstepSize : 0 < stepSize)
    (current proposed : ι → ℝ) :
    ENNReal.ofReal (vectorMalaLogDensityAcceptance logDensity gradient stepSize
      current proposed) =
      Mcmc.Kernel.densityAcceptance (vectorLogDensityWeight logDensity)
        (Mcmc.Kernel.langevinProposalDensity
          (Mcmc.Kernel.malaScoreDrift (scaleVariance stepSize) gradient)
          (scaleVariance stepSize))
        current proposed := by
  set v := scaleVariance stepSize with hv_def
  have hv_ne : v ≠ 0 := scaleVariance_ne_zero hstepSize
  set drift := Mcmc.Kernel.malaScoreDrift v gradient
  -- Real-valued forward and reverse density flows
  set fwd_r := Real.exp (logDensity current) *
    ∏ i, gaussianPDFReal 0 v (proposed i - current i - drift current i)
  set rev_r := Real.exp (logDensity proposed) *
    ∏ i, gaussianPDFReal 0 v (current i - proposed i - drift proposed i)
  have hfwd_pos : 0 < fwd_r :=
    mul_pos (Real.exp_pos _)
      (Finset.prod_pos fun i _ => gaussianPDFReal_pos 0 v _ hv_ne)
  have hrev_nonneg : 0 ≤ rev_r :=
    mul_nonneg (le_of_lt (Real.exp_pos _))
      (Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 v _)
  -- Identify ENNReal forward flows with ofReal of positive reals
  have hresidual_eq (x y : ι → ℝ) (i : ι) :
      (y - (x + drift x)) i = y i - x i - drift x i := by
    simp [Pi.sub_apply, Pi.add_apply]; ring
  have hflow_eq (x y : ι → ℝ) :
      Mcmc.Kernel.forwardDensityFlow (vectorLogDensityWeight logDensity)
        (Mcmc.Kernel.langevinProposalDensity drift v) x y =
      ENNReal.ofReal (Real.exp (logDensity x)) *
        ENNReal.ofReal (∏ i, gaussianPDFReal 0 v (y i - x i - drift x i)) := by
    simp only [Mcmc.Kernel.forwardDensityFlow, vectorLogDensityWeight,
      Mcmc.Kernel.langevinProposalDensity, Mcmc.Kernel.shiftedProposalDensity,
      Mcmc.Kernel.langevinCentre]
    congr 1
    rw [Mcmc.Kernel.isotropicGaussianPDF_eq_ofReal_prod]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [hresidual_eq]
  have hfwd_ofReal : Mcmc.Kernel.forwardDensityFlow
      (vectorLogDensityWeight logDensity)
      (Mcmc.Kernel.langevinProposalDensity drift v) current proposed =
      ENNReal.ofReal fwd_r := by
    rw [hflow_eq, ← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
  have hrev_ofReal : Mcmc.Kernel.forwardDensityFlow
      (vectorLogDensityWeight logDensity)
      (Mcmc.Kernel.langevinProposalDensity drift v) proposed current =
      ENNReal.ofReal rev_r := by
    rw [hflow_eq, ← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
  -- Forward flow is nonzero
  have hfwd_ne : Mcmc.Kernel.forwardDensityFlow
      (vectorLogDensityWeight logDensity)
      (Mcmc.Kernel.langevinProposalDensity drift v) current proposed ≠ 0 := by
    rw [hfwd_ofReal]; exact (ENNReal.ofReal_pos.mpr hfwd_pos).ne'
  -- Rewrite densityAcceptance into ofReal form
  rw [Mcmc.Kernel.densityAcceptance, if_neg hfwd_ne,
    Mcmc.Kernel.symmetricAcceptedFlow, hfwd_ofReal, hrev_ofReal,
    ← ENNReal.ofReal_min, ← ENNReal.ofReal_div_of_pos hfwd_pos]
  apply congrArg ENNReal.ofReal
  -- The real-valued ratio rev_r / fwd_r = exp(logRatio)
  set logRatio := (logDensity proposed - logDensity current) +
    ((∑ i, (proposed i - current i - drift current i) ^ 2) -
     (∑ i, (current i - proposed i - drift proposed i) ^ 2)) /
    (2 * (v : ℝ)) with hlogRatio_def
  have hratio : rev_r / fwd_r = Real.exp logRatio := by
    simp only [fwd_r, rev_r, gaussianPDFReal, sub_zero]
    have hc_pos : 0 < (Real.sqrt (2 * ↑π * ↑v))⁻¹ := by positivity
    have hfactor (ld : ℝ) (f : ι → ℝ) :
        Real.exp ld * ∏ i, (Real.sqrt (2 * ↑π * ↑v))⁻¹ *
          Real.exp (-(f i ^ 2) / (2 * ↑v)) =
        (Real.sqrt (2 * ↑π * ↑v))⁻¹ ^ Fintype.card ι *
          (Real.exp ld * Real.exp (∑ i, -(f i ^ 2) / (2 * ↑v))) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        ← Real.exp_sum]
      ring
    rw [hfactor, hfactor, mul_div_mul_left _ _ (pow_pos hc_pos _).ne',
      ← Real.exp_add, ← Real.exp_add, ← Real.exp_sub]
    congr 1
    simp only [hlogRatio_def]
    rw [← Finset.sum_div, ← Finset.sum_div, Finset.sum_neg_distrib,
      Finset.sum_neg_distrib]
    ring
  -- Connect vectorMalaLogDensityAcceptance to exp(min 0 logRatio)
  have hv_val : (v : ℝ) = stepSize ^ 2 := rfl
  have hmala_eq : vectorMalaLogDensityAcceptance logDensity gradient stepSize
      current proposed = Real.exp (min 0 logRatio) := by
    have hresidual_fwd : ∀ i,
        (proposed i - (current i + (v : ℝ) / 2 * gradient current i)) ^ 2 =
        (proposed i - current i - drift current i) ^ 2 := by
      intro i; congr 1
      simp only [drift, Mcmc.Kernel.malaScoreDrift]; ring
    have hresidual_rev : ∀ i,
        (current i - (proposed i + (v : ℝ) / 2 * gradient proposed i)) ^ 2 =
        (current i - proposed i - drift proposed i) ^ 2 := by
      intro i; congr 1
      simp only [drift, Mcmc.Kernel.malaScoreDrift]; ring
    simp only [vectorMalaLogDensityAcceptance,
      show stepSize ^ 2 = (v : ℝ) from hv_val.symm,
      hresidual_fwd, hresidual_rev]
    rfl
  rw [hmala_eq]
  -- Case analysis on the sign of logRatio
  by_cases hle : 0 ≤ logRatio
  · have hfwd_le_rev : fwd_r ≤ rev_r := by
      have h1 : 1 ≤ rev_r / fwd_r := hratio ▸ Real.one_le_exp_iff.mpr hle
      rwa [le_div_iff₀ hfwd_pos, one_mul] at h1
    rw [min_eq_left hfwd_le_rev, div_self hfwd_pos.ne',
      min_eq_left hle, Real.exp_zero]
  · simp only [not_le] at hle
    have hrev_le_fwd : rev_r ≤ fwd_r := by
      have h1 : rev_r / fwd_r ≤ 1 :=
        hratio ▸ Real.exp_le_one_iff.mpr (le_of_lt hle)
      rwa [div_le_iff₀ hfwd_pos, one_mul] at h1
    rw [min_eq_right hrev_le_fwd, hratio,
      min_eq_right (le_of_lt hle)]

/-- Exact kernel semantics of the vector MALA command program: its Langevin
proposal is completed by the program's log-density acceptance threshold
and rejection-at-current-state branch. -/
noncomputable def vectorMalaProgramKernel
    (logDensity : (ι → ℝ) → ℝ) (gradient : (ι → ℝ) → (ι → ℝ))
    (stepSize : ℝ) (hstepSize : 0 < stepSize)
    (hgradient : Measurable gradient) : Kernel (ι → ℝ) (ι → ℝ) := by
  let v := scaleVariance stepSize
  let drift := Mcmc.Kernel.malaScoreDrift v gradient
  let q := Mcmc.Kernel.langevinProposalDensity drift v
  let Q := Mcmc.Kernel.densityProposal volume q
  letI : IsMarkovKernel Q :=
    Mcmc.Kernel.densityProposal_isMarkov volume
      (Mcmc.Kernel.measurable_uncurry_langevinProposalDensity
        (Mcmc.Kernel.measurable_malaScoreDrift hgradient) v)
      (Mcmc.Kernel.langevinProposalDensity_normalized drift v
        (scaleVariance_ne_zero hstepSize))
  exact Mcmc.Kernel.metropolisHastings Q fun current proposed =>
    ENNReal.ofReal (vectorMalaLogDensityAcceptance logDensity gradient
      stepSize current proposed)

/-- Exact verified vector MALA kernel: density-based MH with the isotropic
Langevin proposal and the zero-safe density-ratio acceptance rule. -/
noncomputable def vectorMalaKernel
    (logDensity : (ι → ℝ) → ℝ) (gradient : (ι → ℝ) → (ι → ℝ))
    (stepSize : ℝ) (hstepSize : 0 < stepSize)
    (hgradient : Measurable gradient) : Kernel (ι → ℝ) (ι → ℝ) :=
  Mcmc.Kernel.scoreMALA (vectorLogDensityWeight logDensity) gradient
    (scaleVariance stepSize) hgradient (scaleVariance_ne_zero hstepSize)

/-- Full refinement: the exact denotation of the vector MALA command program
is the existing verified density-based Metropolis-adjusted Langevin kernel. -/
theorem vectorMalaProgramKernel_refines
    (logDensity : (ι → ℝ) → ℝ) (gradient : (ι → ℝ) → (ι → ℝ))
    (stepSize : ℝ) (hstepSize : 0 < stepSize)
    (hgradient : Measurable gradient) :
    vectorMalaProgramKernel logDensity gradient stepSize hstepSize hgradient =
      vectorMalaKernel logDensity gradient stepSize hstepSize hgradient := by
  unfold vectorMalaProgramKernel vectorMalaKernel
  unfold Mcmc.Kernel.scoreMALA Mcmc.Kernel.metropolisAdjustedLangevin
  unfold Mcmc.Kernel.densityMetropolisHastings
  dsimp only
  congr 1
  funext current proposed
  exact ofReal_vectorMalaAcceptance_eq_densityAcceptance logDensity gradient
    stepSize hstepSize current proposed

/-- The vector MALA kernel preserves the measure with density
`exp ∘ logDensity` with respect to Lebesgue measure. -/
theorem vectorMalaKernel_invariant
    (logDensity : (ι → ℝ) → ℝ) (gradient : (ι → ℝ) → (ι → ℝ))
    (stepSize : ℝ) (hstepSize : 0 < stepSize)
    (hlogDensity : Measurable logDensity) (hgradient : Measurable gradient)
    (hfinite : ∀ x y, Mcmc.Kernel.forwardDensityFlow
      (vectorLogDensityWeight logDensity)
      (Mcmc.Kernel.langevinProposalDensity
        (Mcmc.Kernel.malaScoreDrift (scaleVariance stepSize) gradient)
        (scaleVariance stepSize)) x y ≠ ∞) :
    (vectorMalaKernel logDensity gradient stepSize hstepSize
      hgradient).Invariant
      (Mcmc.Kernel.densityTarget volume
        (vectorLogDensityWeight logDensity)) := by
  exact Mcmc.Kernel.scoreMALA_invariant
    (vectorLogDensityWeight logDensity) gradient (scaleVariance stepSize)
    (measurable_vectorLogDensityWeight hlogDensity) hgradient
    (scaleVariance_ne_zero hstepSize) hfinite

end VectorMALA

end Mcmc.Executable.Continuous
