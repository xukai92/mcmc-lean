import Mcmc.Kernel.PositionDependentMALA

/-!
# Active-Sketch simplified manifold MALA

This module formalizes the kernel theory for Active-Sketch sMMALA, a
position-dependent MALA variant that uses a sketched low-rank SPD metric
`G(x) = SᵀS + λI` where `S = S(x)` is a position-dependent sketch matrix
and `λ > 0` is a regularization parameter.

## Main definitions

* `activeSketchGramEntry`: entry `(SᵀS)ᵢⱼ = Σₖ S(x)ₖᵢ S(x)ₖⱼ`
* `activeSketchMetric`: the full metric `G(x) = SᵀS + λI`
* `activeSketchLogDetMetric`: `log det G(x)`
* `activeSketchInverseMetric`: `G(x)⁻¹`
* `activeSketchMean`: simplified MALA proposal mean using the sketch metric
* `activeSketchSMMALA`: the Metropolis-completed kernel

## Main results

* `activeSketchGram_posSemidef`: the Gram matrix `SᵀS` is positive semidefinite
* `activeSketchMetric_posDef`: the metric `SᵀS + λI` is positive definite for `λ > 0`
* `activeSketchSMMALA_isMarkov`: Markov property (via `densePMALA_isMarkov`)
* `activeSketchSMMALA_isReversible`: detailed balance (via `densePMALA_isReversible`)
* `activeSketchSMMALA_invariant`: target invariance (via `densePMALA_invariant`)
* `activeSketchMetric_eq_reg_smul_one_of_zero_sketch`: zero sketch reduces to `λI`

## Design

The kernel is a specialization of the dense PMALA framework in
`PositionDependentMALA.lean`. The novel mathematical content is the SPD
proof for the sketched metric; all kernel correctness properties are
one-line delegations to the existing `densePMALA` infrastructure.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory BigOperators

namespace Mcmc.Kernel

open ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Entry of the Gram matrix `SᵀS` at position `x`:
`(SᵀS)ᵢⱼ = Σₖ S(x)ₖᵢ · S(x)ₖⱼ`. -/
def activeSketchGramEntry (sketch : (ι → ℝ) → ι → ι → ℝ) (x : ι → ℝ) (i j : ι) : ℝ :=
  ∑ k, sketch x k i * sketch x k j

/-- Active-Sketch metric `G(x) = SᵀS + λI`. -/
def activeSketchMetric (sketch : (ι → ℝ) → ι → ι → ℝ) (reg : ℝ)
    (x : ι → ℝ) (i j : ι) : ℝ :=
  activeSketchGramEntry sketch x i j + if i = j then reg else 0

/-- Log-determinant of the Active-Sketch metric. -/
noncomputable def activeSketchLogDetMetric (sketch : (ι → ℝ) → ι → ι → ℝ)
    (reg : ℝ) (x : ι → ℝ) : ℝ :=
  Real.log (Matrix.det (Matrix.of (activeSketchMetric sketch reg x)))

/-- Inverse of the Active-Sketch metric. -/
noncomputable def activeSketchInverseMetric (sketch : (ι → ℝ) → ι → ι → ℝ)
    (reg : ℝ) (x : ι → ℝ) : ι → ι → ℝ :=
  fun i j => (Matrix.of (activeSketchMetric sketch reg x))⁻¹ i j

/-- Simplified MALA proposal mean using the Active-Sketch inverse metric. -/
noncomputable def activeSketchMean (stepSize : ℝ) (sketch : (ι → ℝ) → ι → ι → ℝ)
    (reg : ℝ) (score : (ι → ℝ) → ι → ℝ) (x : ι → ℝ) (i : ι) : ℝ :=
  x i + stepSize * simplifiedPositionDependentMalaDrift
    (activeSketchInverseMetric sketch reg) score x i

-- ============================================================
-- Phase A: Metric symmetry lemmas
-- ============================================================

omit [DecidableEq ι] in
lemma activeSketchGramEntry_comm (sketch : (ι → ℝ) → ι → ι → ℝ)
    (x : ι → ℝ) (i j : ι) :
    activeSketchGramEntry sketch x i j = activeSketchGramEntry sketch x j i := by
  simp only [activeSketchGramEntry]
  congr 1; funext k; ring

lemma activeSketchMetric_symmetric (sketch : (ι → ℝ) → ι → ι → ℝ)
    (reg : ℝ) (x : ι → ℝ) (i j : ι) :
    activeSketchMetric sketch reg x i j = activeSketchMetric sketch reg x j i := by
  simp only [activeSketchMetric, activeSketchGramEntry_comm sketch x i j, eq_comm]

lemma activeSketchMetric_isHermitian (sketch : (ι → ℝ) → ι → ι → ℝ)
    (reg : ℝ) (x : ι → ℝ) :
    (Matrix.of (activeSketchMetric sketch reg x)).IsHermitian :=
  Matrix.IsHermitian.ext fun i j => by
    simp [activeSketchMetric_symmetric sketch reg x j i]

-- ============================================================
-- Phase B: SPD proofs
-- ============================================================

omit [DecidableEq ι] in
theorem activeSketchGram_posSemidef (sketch : (ι → ℝ) → ι → ι → ℝ) (x : ι → ℝ) :
    (Matrix.of (activeSketchGramEntry sketch x)).PosSemidef := by
  have h : Matrix.of (activeSketchGramEntry sketch x) =
      (Matrix.of (sketch x)).conjTranspose * Matrix.of (sketch x) := by
    ext i j
    simp [activeSketchGramEntry, Matrix.mul_apply]
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem activeSketchMetric_posDef (sketch : (ι → ℝ) → ι → ι → ℝ)
    (reg : ℝ) (hreg : 0 < reg) (x : ι → ℝ) :
    (Matrix.of (activeSketchMetric sketch reg x)).PosDef := by
  have h : Matrix.of (activeSketchMetric sketch reg x) =
      Matrix.of (activeSketchGramEntry sketch x) +
        Matrix.diagonal (fun _ => reg) := by
    ext i j
    simp [activeSketchMetric, Matrix.diagonal]
  rw [h]
  exact Matrix.PosDef.posSemidef_add (activeSketchGram_posSemidef sketch x)
    (Matrix.PosDef.diagonal (fun _ => hreg))

-- ============================================================
-- Phase C: Identity-metric reduction
-- ============================================================

theorem activeSketchMetric_eq_reg_smul_one_of_zero_sketch (reg : ℝ) (x : ι → ℝ) :
    Matrix.of (activeSketchMetric (fun _ _ _ => (0 : ℝ)) reg x) =
      reg • (1 : Matrix ι ι ℝ) := by
  ext i j
  simp [activeSketchMetric, activeSketchGramEntry, Matrix.smul_apply,
    Matrix.one_apply]

-- ============================================================
-- Phase D: Kernel definition and correctness (delegation)
-- ============================================================

/-- Active-Sketch sMMALA kernel: a dense PMALA kernel instantiated with
the sketched metric `G(x) = SᵀS + λI` and the simplified drift. -/
noncomputable def activeSketchSMMALA (weight : (ι → ℝ) → ENNReal) (stepSize : ℝ)
    (sketch : (ι → ℝ) → ι → ι → ℝ) (reg : ℝ) (score : (ι → ℝ) → ι → ℝ)
    (hmeasurable : Measurable (Function.uncurry
      (densePmalaProposalDensity stepSize (activeSketchMean stepSize sketch reg score)
        (activeSketchMetric sketch reg) (activeSketchLogDetMetric sketch reg))))
    (hnormalized : ∀ q, ∫⁻ proposed,
      densePmalaProposalDensity stepSize (activeSketchMean stepSize sketch reg score)
        (activeSketchMetric sketch reg) (activeSketchLogDetMetric sketch reg) q proposed
        ∂volume = 1) : Kernel (ι → ℝ) (ι → ℝ) :=
  densePMALA weight stepSize (activeSketchMean stepSize sketch reg score)
    (activeSketchMetric sketch reg) (activeSketchLogDetMetric sketch reg)
    hmeasurable hnormalized

theorem activeSketchSMMALA_isMarkov (weight : (ι → ℝ) → ENNReal) (stepSize : ℝ)
    (sketch : (ι → ℝ) → ι → ι → ℝ) (reg : ℝ) (score : (ι → ℝ) → ι → ℝ)
    (hweight : Measurable weight)
    (hmeasurable : Measurable (Function.uncurry
      (densePmalaProposalDensity stepSize (activeSketchMean stepSize sketch reg score)
        (activeSketchMetric sketch reg) (activeSketchLogDetMetric sketch reg))))
    (hnormalized : ∀ q, ∫⁻ proposed,
      densePmalaProposalDensity stepSize (activeSketchMean stepSize sketch reg score)
        (activeSketchMetric sketch reg) (activeSketchLogDetMetric sketch reg) q proposed
        ∂volume = 1) :
    IsMarkovKernel (activeSketchSMMALA weight stepSize sketch reg score
      hmeasurable hnormalized) :=
  densePMALA_isMarkov weight stepSize (activeSketchMean stepSize sketch reg score)
    (activeSketchMetric sketch reg) (activeSketchLogDetMetric sketch reg) hweight
    hmeasurable hnormalized

theorem activeSketchSMMALA_isReversible (weight : (ι → ℝ) → ENNReal) (stepSize : ℝ)
    (sketch : (ι → ℝ) → ι → ι → ℝ) (reg : ℝ) (score : (ι → ℝ) → ι → ℝ)
    (hweight : Measurable weight)
    (hmeasurable : Measurable (Function.uncurry
      (densePmalaProposalDensity stepSize (activeSketchMean stepSize sketch reg score)
        (activeSketchMetric sketch reg) (activeSketchLogDetMetric sketch reg))))
    (hnormalized : ∀ q, ∫⁻ proposed,
      densePmalaProposalDensity stepSize (activeSketchMean stepSize sketch reg score)
        (activeSketchMetric sketch reg) (activeSketchLogDetMetric sketch reg) q proposed
        ∂volume = 1)
    (hfinite : ∀ x y, forwardDensityFlow weight
      (densePmalaProposalDensity stepSize (activeSketchMean stepSize sketch reg score)
        (activeSketchMetric sketch reg) (activeSketchLogDetMetric sketch reg)) x y ≠ ∞) :
    (activeSketchSMMALA weight stepSize sketch reg score
      hmeasurable hnormalized).IsReversible (densityTarget volume weight) :=
  densePMALA_isReversible weight stepSize (activeSketchMean stepSize sketch reg score)
    (activeSketchMetric sketch reg) (activeSketchLogDetMetric sketch reg) hweight
    hmeasurable hnormalized hfinite

theorem activeSketchSMMALA_invariant (weight : (ι → ℝ) → ENNReal) (stepSize : ℝ)
    (sketch : (ι → ℝ) → ι → ι → ℝ) (reg : ℝ) (score : (ι → ℝ) → ι → ℝ)
    (hweight : Measurable weight)
    (hmeasurable : Measurable (Function.uncurry
      (densePmalaProposalDensity stepSize (activeSketchMean stepSize sketch reg score)
        (activeSketchMetric sketch reg) (activeSketchLogDetMetric sketch reg))))
    (hnormalized : ∀ q, ∫⁻ proposed,
      densePmalaProposalDensity stepSize (activeSketchMean stepSize sketch reg score)
        (activeSketchMetric sketch reg) (activeSketchLogDetMetric sketch reg) q proposed
        ∂volume = 1)
    (hfinite : ∀ x y, forwardDensityFlow weight
      (densePmalaProposalDensity stepSize (activeSketchMean stepSize sketch reg score)
        (activeSketchMetric sketch reg) (activeSketchLogDetMetric sketch reg)) x y ≠ ∞) :
    (activeSketchSMMALA weight stepSize sketch reg score
      hmeasurable hnormalized).Invariant (densityTarget volume weight) :=
  densePMALA_invariant weight stepSize (activeSketchMean stepSize sketch reg score)
    (activeSketchMetric sketch reg) (activeSketchLogDetMetric sketch reg) hweight
    hmeasurable hnormalized hfinite

end Mcmc.Kernel
