import Mcmc.Finite.MarkovKernel
import Mathlib.Tactic

/-!
# Finite conditional refresh kernels

This module conditions a finite distribution on the fiber of a deterministic
statistic. Positive fibers are refreshed from the exact conditional law;
zero-mass fibers use an identity fallback so the construction remains a total
Markov kernel. The fallback is invisible at stationarity.
-/

open scoped BigOperators

namespace Mcmc.Finite.Conditional

open MarkovKernel

variable {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]

/-- Marginal mass of one fiber of a deterministic statistic. -/
def fiberMass (π : Distribution α) (statistic : α → β) (b : β) : ℝ :=
  ∑ x, if statistic x = b then π.mass x else 0

omit [DecidableEq α] in
theorem fiberMass_nonneg (π : Distribution α) (statistic : α → β) (b : β) :
    0 ≤ fiberMass π statistic b := by
  unfold fiberMass
  apply Finset.sum_nonneg
  intro x _
  by_cases h : statistic x = b <;> simp [h, π.nonneg x]

/-- Exact conditional distribution on a positive-mass statistic fiber. -/
noncomputable def fiberLaw (π : Distribution α) (statistic : α → β) (b : β)
    (hb : 0 < fiberMass π statistic b) : Distribution α where
  mass x := if statistic x = b then π.mass x / fiberMass π statistic b else 0
  nonneg x := by
    by_cases h : statistic x = b
    · simp only [h, if_true]
      exact div_nonneg (π.nonneg x) (le_of_lt hb)
    · simp [h]
  sum_mass := by
    calc
      ∑ x, (if statistic x = b then π.mass x / fiberMass π statistic b else 0) =
          ∑ x, (if statistic x = b then π.mass x else 0) /
            fiberMass π statistic b := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases h : statistic x = b <;> simp [h]
      _ = fiberMass π statistic b / fiberMass π statistic b := by
        rw [← Finset.sum_div]
        rfl
      _ = 1 := div_self (ne_of_gt hb)

/-- Refresh from the conditional law on the current statistic fiber. A
zero-mass fiber falls back to the identity transition. -/
noncomputable def kernel (π : Distribution α) (statistic : α → β) :
    MarkovKernel α where
  prob current proposed :=
    if h : 0 < fiberMass π statistic (statistic current) then
      (fiberLaw π statistic (statistic current) h).mass proposed
    else if proposed = current then 1 else 0
  nonneg current proposed := by
    split
    · exact (fiberLaw π statistic _ _).nonneg proposed
    · split <;> norm_num
  sum_prob current := by
    split
    · exact (fiberLaw π statistic _ _).sum_mass
    · simp

/-- A positive-fiber conditional refresh never changes the statistic. -/
theorem kernel_incompatible_zero (π : Distribution α) (statistic : α → β)
    (current proposed : α)
    (hcurrent : 0 < fiberMass π statistic (statistic current))
    (hincompatible : statistic proposed ≠ statistic current) :
    (kernel π statistic).prob current proposed = 0 := by
  simp [kernel, hcurrent, fiberLaw, hincompatible]

/-- Every state with positive target mass belongs to a positive-mass fiber. -/
theorem fiberMass_pos_of_mass_pos (π : Distribution α) (statistic : α → β)
    (x : α) (hx : 0 < π.mass x) :
    0 < fiberMass π statistic (statistic x) := by
  unfold fiberMass
  have hle : π.mass x ≤
      ∑ y, if statistic y = statistic x then π.mass y else 0 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ x)]
    simp only [if_true]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun y _ => by
      by_cases h : statistic y = statistic x <;> simp [h, π.nonneg y])
  exact lt_of_lt_of_le hx hle

/-- Exact conditional refresh preserves the original finite distribution. -/
theorem kernel_stationary (π : Distribution α) (statistic : α → β) :
    (kernel π statistic).Stationary π := by
  intro proposed
  by_cases hmass : 0 < π.mass proposed
  · have hfiber := fiberMass_pos_of_mass_pos π statistic proposed hmass
    calc
      ∑ current, π.mass current * (kernel π statistic).prob current proposed =
          ∑ current,
            (if statistic current = statistic proposed then π.mass current else 0) *
              (π.mass proposed / fiberMass π statistic (statistic proposed)) := by
        apply Finset.sum_congr rfl
        intro current _
        by_cases h : statistic current = statistic proposed
        · have hcurrent : 0 < fiberMass π statistic (statistic current) := by
            simpa [h] using hfiber
          change π.mass current *
              (if hc : 0 < fiberMass π statistic (statistic current) then
                (fiberLaw π statistic (statistic current) hc).mass proposed
              else if proposed = current then 1 else 0) = _
          rw [dif_pos hcurrent]
          simp [fiberLaw, h]
        · have hreverse : statistic proposed ≠ statistic current := Ne.symm h
          have hne : proposed ≠ current := fun heq => hreverse (congrArg statistic heq)
          by_cases hcurrent : 0 < fiberMass π statistic (statistic current)
          · simp [kernel, hcurrent, fiberLaw, h, hreverse]
          · simp [kernel, hcurrent, h, hne]
      _ = fiberMass π statistic (statistic proposed) *
          (π.mass proposed / fiberMass π statistic (statistic proposed)) := by
        rw [← Finset.sum_mul]
        rfl
      _ = π.mass proposed := by field_simp
  · have hzero : π.mass proposed = 0 := le_antisymm
        (not_lt.mp hmass) (π.nonneg proposed)
    rw [hzero]
    apply Finset.sum_eq_zero
    intro current _
    by_cases hfiber : 0 < fiberMass π statistic (statistic current)
    · simp [kernel, hfiber, fiberLaw, hzero]
    · by_cases heq : proposed = current
      · subst current
        simp [kernel, hfiber, hzero]
      · simp [kernel, hfiber, heq]

end Mcmc.Finite.Conditional
