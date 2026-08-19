import Mathlib.Probability.Kernel.Invariance

/-!
# Reusable invariant-kernel closure lemmas

This module contains target-preservation facts that are independent of a
particular sampler. Algorithm modules should import these foundations instead
of defining generic invariance lemmas locally.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory.Kernel.Invariant

variable {α : Type*} [MeasurableSpace α]

/-- Scaling an invariant measure by a nonnegative extended-real constant does
not change invariance. This is useful when an algorithm naturally preserves an
unnormalized target and the user-facing target differs only by normalization. -/
theorem smul {κ : Kernel α α} {μ : Measure α} (h : κ.Invariant μ)
    (c : ℝ≥0∞) :
    κ.Invariant (c • μ) := by
  rw [Kernel.Invariant, Measure.comp_smul, h]

end ProbabilityTheory.Kernel.Invariant
