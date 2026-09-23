import Mcmc.Executable.Continuous.MALA
import Mcmc.Kernel.PositionDependentMALA

/-!
# Dense PMALA IR-kernel refinement

Proves that the dense position-dependent MALA command program
(`dense_pmala_step!`) has exact kernel semantics equal to the density-based
Metropolis-adjusted Langevin transition with position-dependent Gaussian
proposals, conditional on measurability, normalization, and a bridge hypothesis
connecting the program's real acceptance to the density-based acceptance.

The acceptance ratio includes three asymmetric terms: the log-density ratio,
a log-determinant correction for the position-dependent covariance, and a
quadratic-form ratio from the Gaussian exponents.

## Conditional hypotheses

The refinement theorem is conditional on:
- `hmeasurable`: measurability of the uncurried position-dependent Gaussian density
- `hnormalized`: normalization of the position-dependent Gaussian
- `hbridge`: the real acceptance equals the density-based acceptance

These conditions are dischargeable for any concrete positive-definite metric
whose Gaussian density has been proved measurable and normalized.
-/

open MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory BigOperators Real

namespace Mcmc.Executable.Continuous

open ProbabilityTheory
open Mcmc.Executable

variable {ι : Type*} [Fintype ι]

/-- Real acceptance threshold computed by the dense PMALA command program.
Mirrors the Hastings ratio for a position-dependent Gaussian proposal with
mean `mean(q)` and precision `metric(q)`. -/
noncomputable def densePmalaLogDensityAcceptance
    (logDensity : (ι → ℝ) → ℝ)
    (mean : (ι → ℝ) → ι → ℝ)
    (metric : (ι → ℝ) → ι → ι → ℝ)
    (logDetMetric : (ι → ℝ) → ℝ)
    (stepSize : ℝ) (current proposed : ι → ℝ) : ℝ :=
  let fwdResidual := fun i => proposed i - mean current i
  let revResidual := fun i => current i - mean proposed i
  let fwdQuad := Mcmc.Kernel.metricQuadratic metric current fwdResidual
  let revQuad := Mcmc.Kernel.metricQuadratic metric proposed revResidual
  let logDetRatio := (logDetMetric proposed - logDetMetric current) / 2
  let logRatio := (logDensity proposed - logDensity current) +
    logDetRatio +
    (fwdQuad - revQuad) / (2 * stepSize ^ 2)
  Real.exp (min 0 logRatio)

theorem densePmalaLogDensityAcceptance_pos
    (logDensity : (ι → ℝ) → ℝ)
    (mean : (ι → ℝ) → ι → ℝ)
    (metric : (ι → ℝ) → ι → ι → ℝ)
    (logDetMetric : (ι → ℝ) → ℝ)
    (stepSize : ℝ) (current proposed : ι → ℝ) :
    0 < densePmalaLogDensityAcceptance logDensity mean metric logDetMetric
      stepSize current proposed :=
  Real.exp_pos _

theorem densePmalaLogDensityAcceptance_le_one
    (logDensity : (ι → ℝ) → ℝ)
    (mean : (ι → ℝ) → ι → ℝ)
    (metric : (ι → ℝ) → ι → ι → ℝ)
    (logDetMetric : (ι → ℝ) → ℝ)
    (stepSize : ℝ) (current proposed : ι → ℝ) :
    densePmalaLogDensityAcceptance logDensity mean metric logDetMetric
      stepSize current proposed ≤ 1 := by
  unfold densePmalaLogDensityAcceptance
  rw [← Real.exp_zero]
  exact Real.exp_le_exp.mpr (min_le_left _ _)

/-- Exact kernel semantics of the dense PMALA command program, conditional on
measurability and normalization of the position-dependent proposal density. -/
noncomputable def densePmalaProgramKernel
    (logDensity : (ι → ℝ) → ℝ)
    (stepSize : ℝ) (mean : (ι → ℝ) → ι → ℝ)
    (metric : (ι → ℝ) → ι → ι → ℝ)
    (logDetMetric : (ι → ℝ) → ℝ)
    (hmeasurable : Measurable (Function.uncurry
      (Mcmc.Kernel.densePmalaProposalDensity stepSize mean metric logDetMetric)))
    (hnormalized : ∀ q, ∫⁻ proposed,
      Mcmc.Kernel.densePmalaProposalDensity stepSize mean metric logDetMetric
        q proposed ∂volume = 1) :
    Kernel (ι → ℝ) (ι → ℝ) := by
  let q := Mcmc.Kernel.densePmalaProposalDensity stepSize mean metric logDetMetric
  let Q := Mcmc.Kernel.densityProposal volume q
  letI : IsMarkovKernel Q :=
    Mcmc.Kernel.densityProposal_isMarkov volume hmeasurable hnormalized
  exact Mcmc.Kernel.metropolisHastings Q fun current proposed =>
    ENNReal.ofReal (densePmalaLogDensityAcceptance logDensity mean metric
      logDetMetric stepSize current proposed)

/-- Full refinement: the exact denotation of the dense PMALA command program
is the existing verified dense PMALA kernel, conditional on measurability,
normalization, and a bridge hypothesis connecting the real acceptance to
the density-based acceptance.

The bridge hypothesis `hbridge` states that the `ENNReal.ofReal` of the
program's acceptance equals the density-based acceptance for every pair of
states. This holds whenever the metric is positive-definite, making both
forward and reverse proposal densities strictly positive. -/
theorem densePmalaProgramKernel_refines
    (logDensity : (ι → ℝ) → ℝ)
    (stepSize : ℝ)
    (mean : (ι → ℝ) → ι → ℝ)
    (metric : (ι → ℝ) → ι → ι → ℝ)
    (logDetMetric : (ι → ℝ) → ℝ)
    (hmeasurable : Measurable (Function.uncurry
      (Mcmc.Kernel.densePmalaProposalDensity stepSize mean metric logDetMetric)))
    (hnormalized : ∀ q, ∫⁻ proposed,
      Mcmc.Kernel.densePmalaProposalDensity stepSize mean metric logDetMetric
        q proposed ∂volume = 1)
    (hbridge : ∀ current proposed,
      ENNReal.ofReal (densePmalaLogDensityAcceptance logDensity mean metric
        logDetMetric stepSize current proposed) =
      Mcmc.Kernel.densityAcceptance (vectorLogDensityWeight logDensity)
        (Mcmc.Kernel.densePmalaProposalDensity stepSize mean metric logDetMetric)
        current proposed) :
    densePmalaProgramKernel logDensity stepSize mean metric logDetMetric
      hmeasurable hnormalized =
      Mcmc.Kernel.densePMALA (vectorLogDensityWeight logDensity) stepSize mean
        metric logDetMetric hmeasurable hnormalized := by
  unfold densePmalaProgramKernel Mcmc.Kernel.densePMALA
  unfold Mcmc.Kernel.positionDependentMALA
  unfold Mcmc.Kernel.densityMetropolisHastings
  dsimp only
  congr 1
  funext current proposed
  exact hbridge current proposed

/-- The dense PMALA kernel preserves the density target, conditional on
measurability, normalization, and pointwise finiteness of the forward flow. -/
theorem densePmalaProgramKernel_invariant
    (logDensity : (ι → ℝ) → ℝ)
    (stepSize : ℝ)
    (mean : (ι → ℝ) → ι → ℝ)
    (metric : (ι → ℝ) → ι → ι → ℝ)
    (logDetMetric : (ι → ℝ) → ℝ)
    (hlogDensity : Measurable logDensity)
    (hmeasurable : Measurable (Function.uncurry
      (Mcmc.Kernel.densePmalaProposalDensity stepSize mean metric logDetMetric)))
    (hnormalized : ∀ q, ∫⁻ proposed,
      Mcmc.Kernel.densePmalaProposalDensity stepSize mean metric logDetMetric
        q proposed ∂volume = 1)
    (hfinite : ∀ x y, Mcmc.Kernel.forwardDensityFlow
      (vectorLogDensityWeight logDensity)
      (Mcmc.Kernel.densePmalaProposalDensity stepSize mean metric logDetMetric)
      x y ≠ ∞) :
    (Mcmc.Kernel.densePMALA (vectorLogDensityWeight logDensity) stepSize mean
      metric logDetMetric hmeasurable hnormalized).Invariant
      (Mcmc.Kernel.densityTarget volume
        (vectorLogDensityWeight logDensity)) := by
  exact Mcmc.Kernel.densePMALA_invariant
    (vectorLogDensityWeight logDensity) stepSize mean metric logDetMetric
    (measurable_vectorLogDensityWeight hlogDensity)
    hmeasurable hnormalized hfinite

end Mcmc.Executable.Continuous
