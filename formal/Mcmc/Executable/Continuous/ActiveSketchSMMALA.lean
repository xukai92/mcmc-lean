import Mcmc.Executable.Continuous.DensePMALA
import Mcmc.Kernel.ActiveSketchSMMALA

/-!
# Active-Sketch sMMALA IR-kernel refinement

Proves that the active-sketch simplified manifold MALA command program
(`active_sketch_smmala_step!`) has exact kernel semantics equal to the
density-based Metropolis-adjusted Langevin transition with the sketched
metric `G(x) = S(x)ᵀS(x) + λI`, conditional on measurability,
normalization, and a bridge hypothesis connecting the program's real
acceptance to the density-based acceptance.

This is a direct specialization of the dense PMALA refinement theorem
(`densePmalaProgramKernel_refines`) with the active-sketch metric.

## Conditional hypotheses

The refinement theorem is conditional on:
- `hmeasurable`: measurability of the uncurried position-dependent Gaussian density
- `hnormalized`: normalization of the position-dependent Gaussian
- `hbridge`: the real acceptance equals the density-based acceptance
-/

open MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory BigOperators Real

namespace Mcmc.Executable.Continuous

open ProbabilityTheory
open Mcmc.Executable
open Mcmc.Kernel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Real acceptance threshold computed by the active-sketch sMMALA program.
Mirrors the dense PMALA acceptance with the sketched metric
`G(x) = S(x)ᵀS(x) + λI`. -/
noncomputable def activeSketchSmMalaLogDensityAcceptance
    (logDensity : (ι → ℝ) → ℝ)
    (stepSize : ℝ) (sketch : (ι → ℝ) → ι → ι → ℝ) (reg : ℝ)
    (score : (ι → ℝ) → ι → ℝ)
    (current proposed : ι → ℝ) : ℝ :=
  densePmalaLogDensityAcceptance logDensity
    (activeSketchMean stepSize sketch reg score)
    (activeSketchMetric sketch reg)
    (activeSketchLogDetMetric sketch reg)
    stepSize current proposed

theorem activeSketchSmMalaLogDensityAcceptance_pos
    (logDensity : (ι → ℝ) → ℝ)
    (stepSize : ℝ) (sketch : (ι → ℝ) → ι → ι → ℝ) (reg : ℝ)
    (score : (ι → ℝ) → ι → ℝ)
    (current proposed : ι → ℝ) :
    0 < activeSketchSmMalaLogDensityAcceptance logDensity stepSize sketch reg
      score current proposed :=
  densePmalaLogDensityAcceptance_pos logDensity
    (activeSketchMean stepSize sketch reg score)
    (activeSketchMetric sketch reg)
    (activeSketchLogDetMetric sketch reg)
    stepSize current proposed

theorem activeSketchSmMalaLogDensityAcceptance_le_one
    (logDensity : (ι → ℝ) → ℝ)
    (stepSize : ℝ) (sketch : (ι → ℝ) → ι → ι → ℝ) (reg : ℝ)
    (score : (ι → ℝ) → ι → ℝ)
    (current proposed : ι → ℝ) :
    activeSketchSmMalaLogDensityAcceptance logDensity stepSize sketch reg
      score current proposed ≤ 1 :=
  densePmalaLogDensityAcceptance_le_one logDensity
    (activeSketchMean stepSize sketch reg score)
    (activeSketchMetric sketch reg)
    (activeSketchLogDetMetric sketch reg)
    stepSize current proposed

/-- Exact kernel semantics of the active-sketch sMMALA command program,
conditional on measurability and normalization of the position-dependent
proposal density with the sketched metric. -/
noncomputable def activeSketchSmMalaProgramKernel
    (logDensity : (ι → ℝ) → ℝ)
    (stepSize : ℝ) (sketch : (ι → ℝ) → ι → ι → ℝ) (reg : ℝ)
    (score : (ι → ℝ) → ι → ℝ)
    (hmeasurable : Measurable (Function.uncurry
      (densePmalaProposalDensity stepSize
        (activeSketchMean stepSize sketch reg score)
        (activeSketchMetric sketch reg)
        (activeSketchLogDetMetric sketch reg))))
    (hnormalized : ∀ q, ∫⁻ proposed,
      densePmalaProposalDensity stepSize
        (activeSketchMean stepSize sketch reg score)
        (activeSketchMetric sketch reg)
        (activeSketchLogDetMetric sketch reg) q proposed
        ∂volume = 1) :
    Kernel (ι → ℝ) (ι → ℝ) :=
  densePmalaProgramKernel logDensity stepSize
    (activeSketchMean stepSize sketch reg score)
    (activeSketchMetric sketch reg)
    (activeSketchLogDetMetric sketch reg)
    hmeasurable hnormalized

/-- Full refinement: the exact denotation of the active-sketch sMMALA
command program is the existing verified active-sketch sMMALA kernel,
conditional on measurability, normalization, and a bridge hypothesis
connecting the real acceptance to the density-based acceptance. -/
theorem activeSketchSmMalaProgramKernel_refines
    (logDensity : (ι → ℝ) → ℝ)
    (stepSize : ℝ) (sketch : (ι → ℝ) → ι → ι → ℝ) (reg : ℝ)
    (score : (ι → ℝ) → ι → ℝ)
    (hmeasurable : Measurable (Function.uncurry
      (densePmalaProposalDensity stepSize
        (activeSketchMean stepSize sketch reg score)
        (activeSketchMetric sketch reg)
        (activeSketchLogDetMetric sketch reg))))
    (hnormalized : ∀ q, ∫⁻ proposed,
      densePmalaProposalDensity stepSize
        (activeSketchMean stepSize sketch reg score)
        (activeSketchMetric sketch reg)
        (activeSketchLogDetMetric sketch reg) q proposed
        ∂volume = 1)
    (hbridge : ∀ current proposed,
      ENNReal.ofReal (activeSketchSmMalaLogDensityAcceptance logDensity
        stepSize sketch reg score current proposed) =
      densityAcceptance (vectorLogDensityWeight logDensity)
        (densePmalaProposalDensity stepSize
          (activeSketchMean stepSize sketch reg score)
          (activeSketchMetric sketch reg)
          (activeSketchLogDetMetric sketch reg))
        current proposed) :
    activeSketchSmMalaProgramKernel logDensity stepSize sketch reg score
      hmeasurable hnormalized =
      activeSketchSMMALA (vectorLogDensityWeight logDensity) stepSize
        sketch reg score hmeasurable hnormalized := by
  unfold activeSketchSmMalaProgramKernel activeSketchSMMALA
  exact densePmalaProgramKernel_refines logDensity stepSize
    (activeSketchMean stepSize sketch reg score)
    (activeSketchMetric sketch reg)
    (activeSketchLogDetMetric sketch reg)
    hmeasurable hnormalized hbridge

/-- The active-sketch sMMALA kernel preserves the density target,
conditional on measurability, normalization, and pointwise finiteness
of the forward flow. -/
theorem activeSketchSmMalaProgramKernel_invariant
    (logDensity : (ι → ℝ) → ℝ)
    (stepSize : ℝ) (sketch : (ι → ℝ) → ι → ι → ℝ) (reg : ℝ)
    (score : (ι → ℝ) → ι → ℝ)
    (hlogDensity : Measurable logDensity)
    (hmeasurable : Measurable (Function.uncurry
      (densePmalaProposalDensity stepSize
        (activeSketchMean stepSize sketch reg score)
        (activeSketchMetric sketch reg)
        (activeSketchLogDetMetric sketch reg))))
    (hnormalized : ∀ q, ∫⁻ proposed,
      densePmalaProposalDensity stepSize
        (activeSketchMean stepSize sketch reg score)
        (activeSketchMetric sketch reg)
        (activeSketchLogDetMetric sketch reg) q proposed
        ∂volume = 1)
    (hfinite : ∀ x y, forwardDensityFlow
      (vectorLogDensityWeight logDensity)
      (densePmalaProposalDensity stepSize
        (activeSketchMean stepSize sketch reg score)
        (activeSketchMetric sketch reg)
        (activeSketchLogDetMetric sketch reg))
      x y ≠ ∞) :
    (activeSketchSMMALA (vectorLogDensityWeight logDensity) stepSize
      sketch reg score hmeasurable hnormalized).Invariant
      (densityTarget volume (vectorLogDensityWeight logDensity)) :=
  activeSketchSMMALA_invariant (vectorLogDensityWeight logDensity)
    stepSize sketch reg score
    (measurable_vectorLogDensityWeight hlogDensity)
    hmeasurable hnormalized hfinite

end Mcmc.Executable.Continuous
