import Mathlib.Probability.Kernel.Invariance

/-!
# Detailed balance for measure-theoretic kernels

This module provides the general-state interface used by the
measure-theoretic Metropolis--Hastings development.  It works directly with
mathlib's `Measure` and `ProbabilityTheory.Kernel` types and does not depend on
the elementary finite layer.

For a target measure `π` and transition kernel `P`, `proposalJoint π P` is the
law of a pair `(x, y)` obtained by first drawing `x` from `π` and then drawing
`y` from `P x`.  Detailed balance is equivalent to this joint measure being
invariant under swapping its two coordinates.
-/

open MeasureTheory
open scoped ProbabilityTheory

namespace Mcmc.Kernel

open ProbabilityTheory

variable {State : Type*} [MeasurableSpace State]

/-- The joint law `π(dx) P(x,dy)` of a state and one transition from it. -/
noncomputable def proposalJoint (π : Measure State) (P : ProbabilityTheory.Kernel State State) :
    Measure (State × State) :=
  π ⊗ₘ P

/-- The joint transition law evaluated on a measurable rectangle. -/
theorem proposalJoint_apply_prod (π : Measure State) [SFinite π]
    (P : ProbabilityTheory.Kernel State State) [IsSFiniteKernel P]
    {A B : Set State} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    proposalJoint π P (A ×ˢ B) = ∫⁻ x in A, P x B ∂π := by
  exact Measure.compProd_apply_prod hA hB

/-- A Markov transition from a probability measure has a probability joint law. -/
instance proposalJoint.instIsProbabilityMeasure (π : Measure State) [IsProbabilityMeasure π]
    (P : ProbabilityTheory.Kernel State State) [IsMarkovKernel P] :
    IsProbabilityMeasure (proposalJoint π P) := by
  unfold proposalJoint
  infer_instance

/-- Mathlib's setwise detailed-balance predicate is equivalent to symmetry of
the joint transition law under coordinate swap. -/
theorem isReversible_iff_map_swap_eq
    (π : Measure State) [IsProbabilityMeasure π]
    (P : ProbabilityTheory.Kernel State State) [IsMarkovKernel P] :
    P.IsReversible π ↔ (proposalJoint π P).map Prod.swap = proposalJoint π P := by
  constructor
  · intro hrev
    apply Measure.ext_prod
    intro A B hA hB
    rw [Measure.map_apply measurable_swap (hA.prod hB), Set.preimage_swap_prod,
      proposalJoint_apply_prod π P hB hA, proposalJoint_apply_prod π P hA hB]
    exact (hrev hA hB).symm
  · intro hsymm A B hA hB
    rw [← proposalJoint_apply_prod π P hA hB,
      ← proposalJoint_apply_prod π P hB hA]
    calc
      proposalJoint π P (A ×ˢ B) =
          (proposalJoint π P).map Prod.swap (A ×ˢ B) := by rw [hsymm]
      _ = proposalJoint π P (B ×ˢ A) := by
        rw [Measure.map_apply measurable_swap (hA.prod hB), Set.preimage_swap_prod]

/-- Symmetry of the joint transition law implies invariance of the target. -/
theorem invariant_of_map_swap_eq
    (π : Measure State) [IsProbabilityMeasure π]
    (P : ProbabilityTheory.Kernel State State) [IsMarkovKernel P]
    (hsymm : (proposalJoint π P).map Prod.swap = proposalJoint π P) :
    P.Invariant π :=
  ((isReversible_iff_map_swap_eq π P).mpr hsymm).invariant

end Mcmc.Kernel
