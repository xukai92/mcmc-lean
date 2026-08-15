import Mcmc.Finite.MarkovKernel
import Mathlib.Tactic

/-!
# Reroot-invariant dynamic candidate sets

This finite theorem isolates the balance condition needed by dynamic trajectory
samplers such as NUTS. A state-dependent candidate set is safe when membership
is symmetric and its target-mass normalizer is unchanged after rerooting at any
admissible candidate. Merely stopping at the first state-dependent event does
not provide these properties.
-/

open scoped BigOperators

namespace Mcmc.Finite.MarkovKernel

variable {State : Type*} [Fintype State]

/-- Target mass of the dynamically admitted candidate set rooted at `current`. -/
noncomputable def dynamicCandidateNormalizer (target : Distribution State)
    (admissible : State → State → Bool) (current : State) : ℝ :=
  ∑ proposed, if admissible current proposed then target.mass proposed else 0

/-- The exact structural obligations supplied by a symmetric tree builder. -/
structure RerootInvariantCandidateSet (target : Distribution State) where
  admissible : State → State → Bool
  reflexive : ∀ state, admissible state state = true
  symmetric : ∀ left right, admissible left right = admissible right left
  normalizer_eq : ∀ {left right}, admissible left right = true →
    dynamicCandidateNormalizer target admissible left =
      dynamicCandidateNormalizer target admissible right

/-- Every decidable equivalence-class candidate set satisfies the rerooting
conditions. This supplies a concrete family of genuinely state-dependent
dynamic sets (different components may expose different candidates). -/
noncomputable def equivalenceClassCandidateSet (target : Distribution State)
    (relation : Setoid State) [DecidableRel relation.r] :
    RerootInvariantCandidateSet target where
  admissible left right := decide (relation.r left right)
  reflexive state := by simp
  symmetric left right := by
    exact Bool.decide_congr ⟨relation.symm, relation.symm⟩
  normalizer_eq := by
    intro left right hadmissible
    have hlr : relation.r left right := by simpa using hadmissible
    unfold dynamicCandidateNormalizer
    apply Finset.sum_congr rfl
    intro proposed _
    have hiff : relation.r left proposed ↔ relation.r right proposed := by
      constructor
      · intro hlp
        exact relation.trans (relation.symm hlr) hlp
      · intro hrp
        exact relation.trans hlr hrp
    by_cases hleft : relation.r left proposed
    · have hright := hiff.mp hleft
      simp [hleft, hright]
    · have hright : ¬relation.r right proposed := fun h => hleft (hiff.mpr h)
      simp [hleft, hright]

theorem dynamicCandidateNormalizer_pos (target : Distribution State)
    (candidates : RerootInvariantCandidateSet target)
    (htarget : ∀ state, 0 < target.mass state) (current : State) :
    0 < dynamicCandidateNormalizer target candidates.admissible current := by
  have hterm : target.mass current ≤
      dynamicCandidateNormalizer target candidates.admissible current := by
    unfold dynamicCandidateNormalizer
    have hnonneg : ∀ proposed ∈ (Finset.univ : Finset State),
        0 ≤ if candidates.admissible current proposed then
          target.mass proposed else 0 := by
      intro proposed _
      split
      · exact target.nonneg proposed
      · exact le_rfl
    have hsingle := Finset.single_le_sum hnonneg (Finset.mem_univ current)
    simpa [candidates.reflexive] using hsingle
  exact (htarget current).trans_le hterm

/-- Select proportionally to target mass from the completed admissible set. -/
noncomputable def dynamicCandidateKernel (target : Distribution State)
    (candidates : RerootInvariantCandidateSet target)
    (htarget : ∀ state, 0 < target.mass state) : MarkovKernel State where
  prob current proposed :=
    (if candidates.admissible current proposed then target.mass proposed else 0) /
      dynamicCandidateNormalizer target candidates.admissible current
  nonneg current proposed := div_nonneg (by
    split
    · exact target.nonneg proposed
    · exact le_rfl)
    (dynamicCandidateNormalizer_pos target candidates htarget current).le
  sum_prob current := by
    rw [← Finset.sum_div]
    change dynamicCandidateNormalizer target candidates.admissible current /
      dynamicCandidateNormalizer target candidates.admissible current = 1
    exact div_self
      (dynamicCandidateNormalizer_pos target candidates htarget current).ne'

/-- Symmetric stopping plus reroot-invariant normalization gives detailed
balance for the dynamic candidate-selection transition. -/
theorem dynamicCandidateKernel_reversible (target : Distribution State)
    (candidates : RerootInvariantCandidateSet target)
    (htarget : ∀ state, 0 < target.mass state) :
    (dynamicCandidateKernel target candidates htarget).Reversible target := by
  intro left right
  by_cases hadmissible : candidates.admissible left right = true
  · have hreverse : candidates.admissible right left = true := by
      rw [← candidates.symmetric]
      exact hadmissible
    simp only [dynamicCandidateKernel, hadmissible, hreverse, if_true]
    rw [candidates.normalizer_eq hadmissible]
    ring
  · have hfalse : candidates.admissible left right = false :=
      Bool.eq_false_of_not_eq_true hadmissible
    have hreverse : candidates.admissible right left = false := by
      rw [← candidates.symmetric]
      exact hfalse
    simp [dynamicCandidateKernel, hfalse, hreverse]

theorem dynamicCandidateKernel_stationary (target : Distribution State)
    (candidates : RerootInvariantCandidateSet target)
    (htarget : ∀ state, 0 < target.mass state) :
    (dynamicCandidateKernel target candidates htarget).Stationary target :=
  (dynamicCandidateKernel_reversible target candidates htarget).stationary

end Mcmc.Finite.MarkovKernel
