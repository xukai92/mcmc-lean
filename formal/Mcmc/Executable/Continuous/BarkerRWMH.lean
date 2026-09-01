import Mcmc.Executable.Continuous.RWMH
import Mcmc.Kernel.BarkerAcceptance
import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-!
# Scalar Gaussian Barker RWMH refinement

This module gives the Barker-acceptance continuous command program an exact
kernel semantics for arbitrary measurable real log densities and positive
proposal scales, and connects that semantics to the verified Barker MH
construction from `Mcmc.Kernel.BarkerAcceptance`.
-/

open MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace Mcmc.Executable.Continuous

open ProbabilityTheory
open Mcmc.Executable

/-- Real acceptance probability computed by the Barker command program:
the sigmoid of the log-density ratio. -/
noncomputable def barkerLogDensityAcceptance (logDensity : ℝ → ℝ)
    (current proposed : ℝ) : ℝ :=
  1 / (1 + Real.exp (-(logDensity proposed - logDensity current)))

theorem barkerLogDensityAcceptance_pos (logDensity : ℝ → ℝ)
    (current proposed : ℝ) :
    0 < barkerLogDensityAcceptance logDensity current proposed := by
  rw [barkerLogDensityAcceptance, one_div]
  exact inv_pos_of_pos (by positivity)

theorem barkerLogDensityAcceptance_le_one (logDensity : ℝ → ℝ)
    (current proposed : ℝ) :
    barkerLogDensityAcceptance logDensity current proposed ≤ 1 := by
  rw [barkerLogDensityAcceptance, div_le_one (by positivity : (0 : ℝ) < 1 + _)]
  linarith [Real.exp_nonneg (-(logDensity proposed - logDensity current))]

/-- The Barker log-density acceptance is the sigmoid of the log-density ratio. -/
theorem barkerLogDensityAcceptance_eq_sigmoid (logDensity : ℝ → ℝ)
    (current proposed : ℝ) :
    barkerLogDensityAcceptance logDensity current proposed =
      Real.sigmoid (logDensity proposed - logDensity current) := by
  simp [barkerLogDensityAcceptance, Real.sigmoid, one_div]

/-- The program's real sigmoid acceptance equals the Barker density acceptance
used by the verified kernel, for a symmetric Gaussian proposal density. -/
theorem ofReal_barkerLogDensityAcceptance_eq_barkerDensityAcceptance
    (logDensity : ℝ → ℝ) (variance : ℝ≥0) (hvariance : variance ≠ 0)
    (current proposed : ℝ) :
    ENNReal.ofReal (barkerLogDensityAcceptance logDensity current proposed) =
      Mcmc.Kernel.barkerDensityAcceptance (logDensityWeight logDensity)
        (Mcmc.Kernel.randomWalkProposalDensity (gaussianPDF 0 variance))
        current proposed := by
  rw [Mcmc.Kernel.barkerDensityAcceptance]
  have hflow : Mcmc.Kernel.forwardDensityFlow (logDensityWeight logDensity)
      (Mcmc.Kernel.randomWalkProposalDensity (gaussianPDF 0 variance))
      current proposed ≠ 0 := by
    rw [Mcmc.Kernel.forwardDensityFlow, Mcmc.Kernel.randomWalkProposalDensity]
    exact mul_ne_zero (logDensityWeight_ne_zero logDensity current)
      ((gaussianPDF_pos 0 hvariance (proposed - current)).ne')
  rw [if_neg hflow]
  simp only [Mcmc.Kernel.forwardDensityFlow, Mcmc.Kernel.randomWalkProposalDensity]
  have hxy : current - proposed = -(proposed - current) := by ring
  rw [hxy, Mcmc.Kernel.gaussianPDF_zero_even]
  rw [← add_mul,
    ENNReal.mul_div_mul_right _ _
      ((gaussianPDF_pos 0 hvariance (proposed - current)).ne')
      gaussianPDF_ne_top]
  simp only [logDensityWeight]
  rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _),
    ← ENNReal.ofReal_div_of_pos
      (by positivity : (0 : ℝ) < Real.exp (logDensity current) +
        Real.exp (logDensity proposed))]
  apply congrArg ENNReal.ofReal
  unfold barkerLogDensityAcceptance
  have hb : Real.exp (logDensity proposed) ≠ 0 := ne_of_gt (Real.exp_pos _)
  rw [show -(logDensity proposed - logDensity current) =
      logDensity current - logDensity proposed by ring,
    show Real.exp (logDensity current - logDensity proposed) =
      Real.exp (logDensity current) / Real.exp (logDensity proposed) by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg, div_eq_mul_inv],
    show 1 + Real.exp (logDensity current) / Real.exp (logDensity proposed) =
      (Real.exp (logDensity current) + Real.exp (logDensity proposed)) /
        Real.exp (logDensity proposed) by
      rw [add_div, div_self hb]; ring,
    one_div, inv_div, add_comm]

/-- Exact verified Gaussian Barker RWMH kernel selected by a log density and
scale. -/
noncomputable def gaussianBarkerRwmhKernel (logDensity : ℝ → ℝ) (scale : ℝ)
    (hscale : 0 < scale) : Kernel ℝ ℝ :=
  Mcmc.Kernel.barkerDensityMetropolisHastings volume
    (logDensityWeight logDensity)
    (Mcmc.Kernel.randomWalkProposalDensity (gaussianPDF 0 (scaleVariance scale)))
    (Mcmc.Kernel.measurable_uncurry_randomWalkProposalDensity
      (measurable_gaussianPDF 0 (scaleVariance scale)))
    (Mcmc.Kernel.randomWalkProposalDensity_normalized volume
      (measurable_gaussianPDF 0 (scaleVariance scale))
      (lintegral_gaussianPDF_eq_one 0 (scaleVariance_ne_zero hscale)))

/-- Exact kernel semantics of the Barker command program: its scaled
standard-normal proposal is completed by the sigmoid acceptance threshold
and rejection-at-current-state branch. -/
noncomputable def gaussianBarkerRwmhProgramKernel (logDensity : ℝ → ℝ)
    (scale : ℝ) (hscale : 0 < scale) : Kernel ℝ ℝ := by
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
    ENNReal.ofReal (barkerLogDensityAcceptance logDensity current proposed)

/-- Full generic refinement: the exact denotation of the Barker program is
the existing verified Barker Gaussian random-walk MH kernel. -/
theorem gaussianBarkerRwmhProgramKernel_refines (logDensity : ℝ → ℝ) (scale : ℝ)
    (hscale : 0 < scale) :
    gaussianBarkerRwmhProgramKernel logDensity scale hscale =
      gaussianBarkerRwmhKernel logDensity scale hscale := by
  unfold gaussianBarkerRwmhProgramKernel gaussianBarkerRwmhKernel
  unfold Mcmc.Kernel.barkerDensityMetropolisHastings
  dsimp only
  congr 1
  funext current proposed
  exact ofReal_barkerLogDensityAcceptance_eq_barkerDensityAcceptance logDensity
    (scaleVariance scale) (scaleVariance_ne_zero hscale) current proposed

/-- The generic scalar Gaussian Barker RWMH kernel preserves the measure with
density `exp ∘ logDensity` with respect to Lebesgue measure. -/
theorem gaussianBarkerRwmhKernel_invariant (logDensity : ℝ → ℝ) (scale : ℝ)
    (hscale : 0 < scale) (hlogDensity : Measurable logDensity) :
    (gaussianBarkerRwmhKernel logDensity scale hscale).Invariant
      (Mcmc.Kernel.densityTarget volume (logDensityWeight logDensity)) := by
  unfold gaussianBarkerRwmhKernel
  exact Mcmc.Kernel.barkerDensityMetropolisHastings_invariant volume
    (logDensityWeight logDensity)
    (Mcmc.Kernel.randomWalkProposalDensity (gaussianPDF 0 (scaleVariance scale)))
    (measurable_logDensityWeight hlogDensity)
    (Mcmc.Kernel.measurable_uncurry_randomWalkProposalDensity
      (measurable_gaussianPDF 0 (scaleVariance scale)))
    (Mcmc.Kernel.randomWalkProposalDensity_normalized volume
      (measurable_gaussianPDF 0 (scaleVariance scale))
      (lintegral_gaussianPDF_eq_one 0 (scaleVariance_ne_zero hscale)))

end Mcmc.Executable.Continuous
