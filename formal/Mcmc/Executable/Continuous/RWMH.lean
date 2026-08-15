import Mcmc.Executable.Continuous.CompilerIR

/-!
# Generic scalar Gaussian RWMH refinement

This module gives the canonical continuous command program an exact kernel
semantics for arbitrary measurable real log densities and positive proposal
scales, and connects that semantics to the existing verified Gaussian RWMH
construction.
-/

open MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace Mcmc.Executable.Continuous

open ProbabilityTheory
open Mcmc.Executable

/-- Variance of a standard normal scaled by `scale`. -/
def scaleVariance (scale : ℝ) : ℝ≥0 := ⟨scale ^ 2, sq_nonneg scale⟩

/-- Positive finite target weight represented by a real log density. -/
noncomputable def logDensityWeight (logDensity : ℝ → ℝ) (x : ℝ) : ENNReal :=
  ENNReal.ofReal (Real.exp (logDensity x))

theorem measurable_logDensityWeight {logDensity : ℝ → ℝ}
    (hlogDensity : Measurable logDensity) :
    Measurable (logDensityWeight logDensity) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hlogDensity)

theorem logDensityWeight_ne_zero (logDensity : ℝ → ℝ) (x : ℝ) :
    logDensityWeight logDensity x ≠ 0 := by
  simp [logDensityWeight, Real.exp_pos]

theorem logDensityWeight_ne_top (logDensity : ℝ → ℝ) (x : ℝ) :
    logDensityWeight logDensity x ≠ ∞ := by
  simp [logDensityWeight]

/-- Real acceptance threshold computed by the portable command program. -/
noncomputable def logDensityAcceptance (logDensity : ℝ → ℝ)
    (current proposed : ℝ) : ℝ :=
  Real.exp (min 0 (logDensity proposed - logDensity current))

theorem logDensityAcceptance_pos (logDensity : ℝ → ℝ) (current proposed : ℝ) :
    0 < logDensityAcceptance logDensity current proposed :=
  Real.exp_pos _

theorem logDensityAcceptance_le_one (logDensity : ℝ → ℝ)
    (current proposed : ℝ) :
    logDensityAcceptance logDensity current proposed ≤ 1 := by
  rw [logDensityAcceptance, ← Real.exp_zero]
  exact Real.exp_le_exp.mpr (min_le_left _ _)

theorem scaleVariance_ne_zero {scale : ℝ} (hscale : 0 < scale) :
    scaleVariance scale ≠ 0 := by
  apply ne_of_gt
  change 0 < scale ^ 2
  exact sq_pos_of_pos hscale

/-- Scaling the ideal standard-normal primitive and translating by the current
state gives the Gaussian proposal law selected by `scaleVariance`. -/
theorem map_standardNormalMeasure_affine (scale current : ℝ) :
    standardNormalMeasure.map (fun noise => current + scale * noise) =
      gaussianReal current (scaleVariance scale) := by
  rw [standardNormalMeasure]
  rw [show (fun noise : ℝ => current + scale * noise) =
      (fun value : ℝ => current + value) ∘ (fun noise : ℝ => scale * noise) by
    rfl]
  rw [← Measure.map_map (by fun_prop) (by fun_prop)]
  rw [gaussianReal_map_const_mul, gaussianReal_map_const_add]
  congr 2
  · simp
  · apply NNReal.eq
    simp [scaleVariance]
    change scale ^ 2 = scale ^ 2
    rfl

/-- The density-based proposal row is exactly the affine image of the ideal
standard-normal primitive used by the command program. -/
theorem scaledGaussianProposal_row (scale current : ℝ) (hscale : 0 < scale) :
    Mcmc.Kernel.densityProposal volume
        (Mcmc.Kernel.randomWalkProposalDensity
          (gaussianPDF 0 (scaleVariance scale))) current =
      standardNormalMeasure.map (fun noise => current + scale * noise) := by
  rw [map_standardNormalMeasure_affine]
  ext set hset
  rw [Mcmc.Kernel.densityProposal_apply volume
    (Mcmc.Kernel.measurable_uncurry_randomWalkProposalDensity
      (measurable_gaussianPDF 0 (scaleVariance scale))) current hset]
  rw [gaussianReal_apply current (scaleVariance_ne_zero hscale) set]
  apply setLIntegral_congr_fun hset
  intro value _
  simp only [Mcmc.Kernel.randomWalkProposalDensity, gaussianPDF]
  rw [gaussianPDFReal_sub]
  simp

/-- The program's real log-density threshold is exactly the zero-safe density
acceptance used by the verified RWMH kernel. -/
theorem ofReal_logDensityAcceptance_eq_densityAcceptance
    (logDensity : ℝ → ℝ) (variance : ℝ≥0) (hvariance : variance ≠ 0)
    (current proposed : ℝ) :
    ENNReal.ofReal (logDensityAcceptance logDensity current proposed) =
      Mcmc.Kernel.densityAcceptance (logDensityWeight logDensity)
        (Mcmc.Kernel.randomWalkProposalDensity (gaussianPDF 0 variance))
        current proposed := by
  rw [Mcmc.Kernel.randomWalk_densityAcceptance_eq_min_weight_div
    (logDensityWeight logDensity) (gaussianPDF 0 variance)
    (Mcmc.Kernel.gaussianPDF_zero_even variance)
    (logDensityWeight_ne_zero logDensity)
    (fun z => (gaussianPDF_pos 0 hvariance z).ne')
    (fun _ => gaussianPDF_ne_top)]
  simp only [logDensityWeight]
  rw [← ENNReal.ofReal_min]
  rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _)]
  apply congrArg ENNReal.ofReal
  unfold logDensityAcceptance
  by_cases horder : logDensity current ≤ logDensity proposed
  · have hexp : Real.exp (logDensity current) ≤ Real.exp (logDensity proposed) :=
      Real.exp_le_exp.mpr horder
    rw [min_eq_left (sub_nonneg.mpr horder), Real.exp_zero,
      min_eq_left hexp, div_self (Real.exp_ne_zero _)]
  · have hreverse : logDensity proposed ≤ logDensity current := le_of_not_ge horder
    have hexp : Real.exp (logDensity proposed) ≤ Real.exp (logDensity current) :=
      Real.exp_le_exp.mpr hreverse
    rw [min_eq_right (sub_nonpos.mpr hreverse), min_eq_right hexp,
      Real.exp_sub]

/-- Exact verified Gaussian RWMH kernel selected by a log density and scale. -/
noncomputable def gaussianRwmhKernel (logDensity : ℝ → ℝ) (scale : ℝ)
    (hscale : 0 < scale) : Kernel ℝ ℝ :=
  Mcmc.Kernel.gaussianRandomWalkMetropolisHastings
    (logDensityWeight logDensity) (scaleVariance scale)
    (scaleVariance_ne_zero hscale)

/-- Exact kernel semantics of the canonical command program: its scaled
standard-normal proposal is completed by the program's log-density acceptance
threshold and rejection-at-current-state branch. -/
noncomputable def gaussianRwmhProgramKernel (logDensity : ℝ → ℝ) (scale : ℝ)
    (hscale : 0 < scale) : Kernel ℝ ℝ := by
  let variance := scaleVariance scale
  let proposalDensity :=
    Mcmc.Kernel.randomWalkProposalDensity (gaussianPDF 0 variance)
  let Q := Mcmc.Kernel.densityProposal volume proposalDensity
  letI : IsMarkovKernel Q :=
    Mcmc.Kernel.densityProposal_isMarkov volume
      (Mcmc.Kernel.measurable_uncurry_randomWalkProposalDensity
        (measurable_gaussianPDF 0 variance))
      (Mcmc.Kernel.randomWalkProposalDensity_normalized volume
        (measurable_gaussianPDF 0 variance)
        (lintegral_gaussianPDF_eq_one 0 (scaleVariance_ne_zero hscale)))
  exact Mcmc.Kernel.metropolisHastings Q fun current proposed =>
    ENNReal.ofReal (logDensityAcceptance logDensity current proposed)

/-- Full generic refinement: the exact denotation of the canonical program is
the existing verified Gaussian random-walk Metropolis--Hastings kernel. -/
theorem gaussianRwmhProgramKernel_refines (logDensity : ℝ → ℝ) (scale : ℝ)
    (hscale : 0 < scale) :
    gaussianRwmhProgramKernel logDensity scale hscale =
      gaussianRwmhKernel logDensity scale hscale := by
  unfold gaussianRwmhProgramKernel gaussianRwmhKernel
  unfold Mcmc.Kernel.gaussianRandomWalkMetropolisHastings
  unfold Mcmc.Kernel.randomWalkMetropolisHastings
  unfold Mcmc.Kernel.densityMetropolisHastings
  dsimp only
  congr 1
  funext current proposed
  exact ofReal_logDensityAcceptance_eq_densityAcceptance logDensity
    (scaleVariance scale) (scaleVariance_ne_zero hscale) current proposed

/-- The generic scalar Gaussian RWMH kernel preserves the measure with density
`exp ∘ logDensity` with respect to Lebesgue measure. -/
theorem gaussianRwmhKernel_invariant (logDensity : ℝ → ℝ) (scale : ℝ)
    (hscale : 0 < scale) (hlogDensity : Measurable logDensity) :
    (gaussianRwmhKernel logDensity scale hscale).Invariant
      (Mcmc.Kernel.densityTarget volume (logDensityWeight logDensity)) := by
  apply Mcmc.Kernel.gaussianRandomWalkMetropolisHastings_invariant
  · exact measurable_logDensityWeight hlogDensity
  · exact logDensityWeight_ne_top logDensity

/-- With explicit normalization, the invariant target is a probability
measure, giving the usual stationary-distribution statement. -/
theorem gaussianRwmhKernel_stationary_probability
    (logDensity : ℝ → ℝ) (scale : ℝ) (hscale : 0 < scale)
    (hlogDensity : Measurable logDensity)
    (hnormalized : ∫⁻ x, logDensityWeight logDensity x ∂volume = 1) :
    IsProbabilityMeasure
        (Mcmc.Kernel.densityTarget volume (logDensityWeight logDensity)) ∧
      (gaussianRwmhKernel logDensity scale hscale).Invariant
        (Mcmc.Kernel.densityTarget volume (logDensityWeight logDensity)) := by
  constructor
  · exact Mcmc.Kernel.densityTarget_isProbability volume
      (logDensityWeight logDensity) hnormalized
  · exact gaussianRwmhKernel_invariant logDensity scale hscale hlogDensity

end Mcmc.Executable.Continuous
