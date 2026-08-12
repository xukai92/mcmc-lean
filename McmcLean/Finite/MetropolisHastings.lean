import McmcLean.Finite.MarkovKernel
import Mathlib.Tactic

/-!
# Finite-state Metropolis--Hastings

For a strictly positive target `π` and proposal kernel `Q`, the accepted
probability flow from `x` to `y` is

`min (π x * Q x y) (π y * Q y x)`.

Dividing by `π x` gives the off-diagonal transition probability.  The
remaining mass is assigned to staying at `x`.  The symmetric flow definition
handles asymmetric proposals cleanly and makes detailed balance explicit.
-/

open scoped BigOperators

namespace McmcLean.Finite
namespace MetropolisHastings

open MarkovKernel

variable {State : Type*} [Fintype State] [DecidableEq State]

/-- Accepted off-diagonal probability flow. -/
noncomputable def flow (π : Distribution State) (Q : MarkovKernel State)
    (x y : State) : ℝ :=
  min (π.mass x * Q.prob x y) (π.mass y * Q.prob y x)

/-- The usual Metropolis--Hastings acceptance probability.  Lean's real
division defines division by zero as zero, which gives the desired rejection
when the forward proposal probability vanishes. -/
noncomputable def acceptance (π : Distribution State) (Q : MarkovKernel State)
    (x y : State) : ℝ :=
  min 1 ((π.mass y * Q.prob y x) / (π.mass x * Q.prob x y))

/-- The off-diagonal MH transition probability. -/
noncomputable def move (π : Distribution State) (Q : MarkovKernel State)
    (x y : State) : ℝ :=
  if x = y then 0 else flow π Q x y / π.mass x

/-- The probability assigned to rejecting a proposal and staying at `x`. -/
noncomputable def stay (π : Distribution State) (Q : MarkovKernel State)
    (x : State) : ℝ :=
  1 - ∑ y, move π Q x y

/-- The finite-state Metropolis--Hastings transition matrix. -/
noncomputable def probability (π : Distribution State) (Q : MarkovKernel State)
    (x y : State) : ℝ :=
  move π Q x y + if x = y then stay π Q x else 0

omit [DecidableEq State] in
theorem flow_nonneg (π : Distribution State) (Q : MarkovKernel State) (x y : State) :
    0 ≤ flow π Q x y := by
  exact le_min (mul_nonneg (π.nonneg x) (Q.nonneg x y))
    (mul_nonneg (π.nonneg y) (Q.nonneg y x))

omit [DecidableEq State] in
theorem flow_symm (π : Distribution State) (Q : MarkovKernel State) (x y : State) :
    flow π Q x y = flow π Q y x := by
  simp only [flow, min_comm]

private theorem mul_min_one_div (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * min 1 (b / a) = min a b := by
  by_cases ha0 : a = 0
  · subst a
    simp [hb]
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    by_cases hba : b ≤ a
    · have hratio : b / a ≤ 1 := by
        apply (div_le_iff₀ ha_pos).2
        simpa using hba
      rw [min_eq_right hratio, min_eq_right hba]
      field_simp
    · have hab : a ≤ b := le_of_not_ge hba
      have hratio : 1 ≤ b / a := by
        apply (le_div_iff₀ ha_pos).2
        simpa using hab
      rw [min_eq_left hratio, min_eq_left hab, mul_one]

omit [DecidableEq State] in
/-- The acceptance-ratio form produces exactly the symmetric accepted flow. -/
theorem proposal_mul_acceptance (π : Distribution State) (Q : MarkovKernel State)
    (x y : State) :
    (π.mass x * Q.prob x y) * acceptance π Q x y = flow π Q x y := by
  exact mul_min_one_div _ _ (mul_nonneg (π.nonneg x) (Q.nonneg x y))
    (mul_nonneg (π.nonneg y) (Q.nonneg y x))

omit [DecidableEq State] in
theorem acceptance_nonneg (π : Distribution State) (Q : MarkovKernel State)
    (x y : State) : 0 ≤ acceptance π Q x y := by
  apply le_min zero_le_one
  exact div_nonneg (mul_nonneg (π.nonneg y) (Q.nonneg y x))
    (mul_nonneg (π.nonneg x) (Q.nonneg x y))

omit [DecidableEq State] in
theorem acceptance_le_one (π : Distribution State) (Q : MarkovKernel State)
    (x y : State) : acceptance π Q x y ≤ 1 :=
  min_le_left _ _

/-- Away from the diagonal, `move` is proposal probability times the standard
MH acceptance probability. -/
theorem move_eq_proposal_mul_acceptance (π : Distribution State) (Q : MarkovKernel State)
    (hπ : ∀ x, 0 < π.mass x) {x y : State} (hxy : x ≠ y) :
    move π Q x y = Q.prob x y * acceptance π Q x y := by
  rw [move, if_neg hxy]
  apply (div_eq_iff (ne_of_gt (hπ x))).2
  rw [← proposal_mul_acceptance π Q x y]
  ring

theorem move_nonneg (π : Distribution State) (Q : MarkovKernel State)
    (hπ : ∀ x, 0 < π.mass x) (x y : State) : 0 ≤ move π Q x y := by
  simp only [move]
  split_ifs
  · exact le_rfl
  · exact div_nonneg (flow_nonneg π Q x y) (le_of_lt (hπ x))

theorem move_le_proposal (π : Distribution State) (Q : MarkovKernel State)
    (hπ : ∀ x, 0 < π.mass x) (x y : State) : move π Q x y ≤ Q.prob x y := by
  by_cases hxy : x = y
  · simp [move, hxy, Q.nonneg]
  · rw [move, if_neg hxy]
    apply (div_le_iff₀ (hπ x)).2
    calc
      flow π Q x y ≤ π.mass x * Q.prob x y := min_le_left _ _
      _ = Q.prob x y * π.mass x := mul_comm _ _

theorem sum_move_le_one (π : Distribution State) (Q : MarkovKernel State)
    (hπ : ∀ x, 0 < π.mass x) (x : State) : ∑ y, move π Q x y ≤ 1 := by
  calc
    ∑ y, move π Q x y ≤ ∑ y, Q.prob x y :=
      Finset.sum_le_sum fun y _ => move_le_proposal π Q hπ x y
    _ = 1 := Q.sum_prob x

theorem stay_nonneg (π : Distribution State) (Q : MarkovKernel State)
    (hπ : ∀ x, 0 < π.mass x) (x : State) : 0 ≤ stay π Q x := by
  exact sub_nonneg.mpr (sum_move_le_one π Q hπ x)

theorem probability_nonneg (π : Distribution State) (Q : MarkovKernel State)
    (hπ : ∀ x, 0 < π.mass x) (x y : State) : 0 ≤ probability π Q x y := by
  apply add_nonneg (move_nonneg π Q hπ x y)
  by_cases hxy : x = y
  · simpa [hxy] using stay_nonneg π Q hπ x
  · simp [hxy]

theorem sum_probability (π : Distribution State) (Q : MarkovKernel State)
    (x : State) : ∑ y, probability π Q x y = 1 := by
  classical
  rw [show (∑ y : State, probability π Q x y) =
      (∑ y, move π Q x y) + (∑ y, if x = y then stay π Q x else 0) by
    simp only [probability, Finset.sum_add_distrib]]
  have hdiag : (∑ y : State, if x = y then stay π Q x else 0) = stay π Q x := by
    simp
  rw [hdiag, stay]
  ring

/-- The MH construction is a Markov kernel: all probabilities are nonnegative
and every row sums to one. -/
noncomputable def kernel (π : Distribution State) (Q : MarkovKernel State)
    (hπ : ∀ x, 0 < π.mass x) : MarkovKernel State where
  prob := probability π Q
  nonneg := probability_nonneg π Q hπ
  sum_prob := sum_probability π Q

theorem detailed_balance (π : Distribution State) (Q : MarkovKernel State)
    (hπ : ∀ x, 0 < π.mass x) : (kernel π Q hπ).Reversible π := by
  intro x y
  by_cases hxy : x = y
  · subst y
    rfl
  · have hyx : ¬y = x := Ne.symm hxy
    simp only [kernel, probability, move, flow, hxy, hyx, if_false, add_zero]
    rw [mul_div_cancel₀ _ (ne_of_gt (hπ x)), mul_div_cancel₀ _ (ne_of_gt (hπ y))]
    exact min_comm _ _

/-- **Finite-state Metropolis--Hastings correctness:** the target distribution
is stationary for the MH transition kernel. -/
theorem stationary (π : Distribution State) (Q : MarkovKernel State)
    (hπ : ∀ x, 0 < π.mass x) : (kernel π Q hπ).Stationary π :=
  (detailed_balance π Q hπ).stationary

end MetropolisHastings
end McmcLean.Finite
