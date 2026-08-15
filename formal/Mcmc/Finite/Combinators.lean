import Mcmc.Finite.Dynamics
import Mathlib.Tactic

/-!
# Reusable finite-kernel combinators

Identity, sequential composition, convex mixtures, and coordinate lifts for
the elementary finite interface.  The stationarity lemmas are the algebraic
foundation used by Gibbs and tempering below.
!-/

open scoped BigOperators

namespace Mcmc.Finite.MarkovKernel

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The identity transition. -/
def identity [DecidableEq α] : MarkovKernel α where
  prob x y := if x = y then 1 else 0
  nonneg x y := by split_ifs <;> positivity
  sum_prob x := by simp

/-- Sequential composition, with `first` applied before `second`. -/
def comp (second first : MarkovKernel α) : MarkovKernel α where
  prob x z := ∑ y, first.prob x y * second.prob y z
  nonneg x z := Finset.sum_nonneg fun y _ => mul_nonneg (first.nonneg x y) (second.nonneg y z)
  sum_prob x := by
    rw [Finset.sum_comm]
    calc
      ∑ y, ∑ z, first.prob x y * second.prob y z =
          ∑ y, first.prob x y * ∑ z, second.prob y z := by
            apply Finset.sum_congr rfl
            intro y _
            rw [Finset.mul_sum]
      _ = 1 := by
        simp_rw [second.sum_prob, mul_one]
        exact first.sum_prob x

/-- A convex mixture of two finite kernels. -/
def mixture (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (first second : MarkovKernel α) : MarkovKernel α where
  prob x y := p * first.prob x y + (1 - p) * second.prob x y
  nonneg x y := add_nonneg (mul_nonneg hp0 (first.nonneg x y))
    (mul_nonneg (sub_nonneg.mpr hp1) (second.nonneg x y))
  sum_prob x := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      first.sum_prob, second.sum_prob]
    ring

@[simp] theorem identity_prob [DecidableEq α] (x y : α) :
    identity.prob x y = if x = y then 1 else 0 := rfl

theorem identity_stationary [DecidableEq α] (π : Distribution α) :
    identity.Stationary π := by
  intro y
  simp [identity]

theorem comp_stationary (first second : MarkovKernel α) (π : Distribution α)
    (hfirst : first.Stationary π) (hsecond : second.Stationary π) :
    (comp second first).Stationary π := by
  intro z
  rw [show (∑ x, π.mass x * (comp second first).prob x z) =
      ∑ y, (∑ x, π.mass x * first.prob x y) * second.prob y z by
    simp only [comp, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    ring]
  rw [show (∑ y, (∑ x, π.mass x * first.prob x y) * second.prob y z) =
      ∑ y, π.mass y * second.prob y z by
    apply Finset.sum_congr rfl
    intro y _
    rw [hfirst y]]
  exact hsecond z

/-- Sequential kernel composition is associative. -/
theorem comp_assoc (first second third : MarkovKernel α) :
    comp third (comp second first) = comp (comp third second) first := by
  apply MarkovKernel.ext
  funext x z
  simp only [comp, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro w _
  ring

@[simp]
theorem comp_identity [DecidableEq α] (P : MarkovKernel α) :
    comp identity P = P := by
  apply MarkovKernel.ext
  funext x z
  simp [comp, identity]

@[simp]
theorem identity_comp [DecidableEq α] (P : MarkovKernel α) :
    comp P identity = P := by
  apply MarkovKernel.ext
  funext x z
  simp [comp, identity]

theorem mixture_stationary (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (first second : MarkovKernel α) (π : Distribution α)
    (hfirst : first.Stationary π) (hsecond : second.Stationary π) :
    (mixture p hp0 hp1 first second).Stationary π := by
  intro y
  simp only [mixture, mul_add, Finset.sum_add_distrib]
  rw [show (∑ x, π.mass x * (p * first.prob x y)) =
      p * ∑ x, π.mass x * first.prob x y by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring,
    show (∑ x, π.mass x * ((1 - p) * second.prob x y)) =
      (1 - p) * ∑ x, π.mass x * second.prob x y by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring,
    hfirst y, hsecond y]
  ring

/-- Lift a state-dependent update of the first coordinate, retaining the
second coordinate exactly. -/
def liftFst [DecidableEq β] (update : β → MarkovKernel α) :
    MarkovKernel (α × β) where
  prob x y := if x.2 = y.2 then (update x.2).prob x.1 y.1 else 0
  nonneg x y := by
    split_ifs
    · exact (update x.2).nonneg x.1 y.1
    · exact le_rfl
  sum_prob x := by
    classical
    rw [Fintype.sum_prod_type]
    simp [update x.2 |>.sum_prob]

/-- Lift a state-dependent update of the second coordinate, retaining the
first coordinate exactly. -/
def liftSnd [DecidableEq α] (update : α → MarkovKernel β) :
    MarkovKernel (α × β) where
  prob x y := if x.1 = y.1 then (update x.1).prob x.2 y.2 else 0
  nonneg x y := by
    split_ifs
    · exact (update x.1).nonneg x.2 y.2
    · exact le_rfl
  sum_prob x := by
    classical
    rw [Fintype.sum_prod_type]
    simp [update x.1 |>.sum_prob]

end Mcmc.Finite.MarkovKernel
