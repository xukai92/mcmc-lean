import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

/-!
# Finite-state Markov kernels

This file provides a deliberately small finite-state interface.  It lets the
first Metropolis--Hastings correctness proof stay algebraic; a later layer can
embed these kernels into `ProbabilityTheory.Kernel`.
-/

open scoped BigOperators

namespace Mcmc.Finite

/-- A transition matrix on a finite state space, with nonnegative entries and
rows summing to one. -/
structure MarkovKernel (State : Type*) [Fintype State] where
  prob : State → State → ℝ
  nonneg : ∀ x y, 0 ≤ prob x y
  sum_prob : ∀ x, ∑ y, prob x y = 1

namespace MarkovKernel

variable {State : Type*} [Fintype State]

/-- Finite Markov kernels are equal when their transition functions are
equal. -/
@[ext]
theorem ext {P Q : MarkovKernel State} (h : P.prob = Q.prob) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

/-- A nonnegative, normalized probability mass function on a finite type. -/
structure Distribution (State : Type*) [Fintype State] where
  mass : State → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  sum_mass : ∑ x, mass x = 1

namespace Distribution

/-- Finite distributions are equal when their mass functions are equal. -/
@[ext]
theorem ext {π ρ : Distribution State} (h : π.mass = ρ.mass) : π = ρ := by
  cases π
  cases ρ
  cases h
  rfl

/-- Finite monadic composition of distributions. -/
def bind {α β : Type*} [Fintype α] [Fintype β]
    (law : Distribution α) (next : α → Distribution β) : Distribution β where
  mass y := ∑ x, law.mass x * (next x).mass y
  nonneg y := Finset.sum_nonneg fun x _ =>
    mul_nonneg (law.nonneg x) ((next x).nonneg y)
  sum_mass := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, Distribution.sum_mass, mul_one]
    exact law.sum_mass

/-- Push a finite distribution forward through a deterministic function. -/
def map {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (law : Distribution α) (f : α → β) : Distribution β :=
  bind law fun x =>
    { mass := fun y => if y = f x then 1 else 0
      nonneg := fun y => by split <;> norm_num
      sum_mass := by simp }

@[simp] theorem bind_mass {α β : Type*} [Fintype α] [Fintype β]
    (law : Distribution α) (next : α → Distribution β) (y : β) :
    (bind law next).mass y = ∑ x, law.mass x * (next x).mass y := rfl

/-- Law of total expectation for finite distribution bind. -/
theorem bind_expectation {α β : Type*} [Fintype α] [Fintype β]
    (law : Distribution α) (next : α → Distribution β) (f : β → ℝ) :
    ∑ y, (bind law next).mass y * f y =
      ∑ x, law.mass x * ∑ y, (next x).mass y * f y := by
  simp only [bind_mass, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  exact mul_assoc _ _ _

/-- Expectation under deterministic pushforward. -/
theorem map_expectation {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (law : Distribution α) (g : α → β) (f : β → ℝ) :
    ∑ y, (map law g).mass y * f y = ∑ x, law.mass x * f (g x) := by
  rw [map, bind_expectation]
  apply Finset.sum_congr rfl
  intro x _
  simp

end Distribution

/-- Detailed balance (reversibility) with respect to `π`. -/
def Reversible (P : MarkovKernel State) (π : Distribution State) : Prop :=
  ∀ x y : State,
    (π.mass x : ℝ) * (P.prob x y : ℝ) = (π.mass y : ℝ) * (P.prob y x : ℝ)

/-- The distribution `π` is stationary for `P`. -/
def Stationary (P : MarkovKernel State) (π : Distribution State) : Prop :=
  ∀ y : State, ∑ x, (π.mass x : ℝ) * (P.prob x y : ℝ) = π.mass y

/-- Detailed balance implies stationarity on a finite state space. -/
theorem Reversible.stationary {P : MarkovKernel State} {π : Distribution State}
    (hrev : P.Reversible π) : P.Stationary π := by
  unfold Stationary
  unfold Reversible at hrev
  intro y
  calc
    ∑ x, π.mass x * P.prob x y = ∑ x, π.mass y * P.prob y x := by
      apply Finset.sum_congr rfl
      intro x _
      exact hrev x y
    _ = π.mass y * ∑ x, P.prob y x := by rw [Finset.mul_sum]
    _ = π.mass y := by rw [P.sum_prob, mul_one]

end MarkovKernel

end Mcmc.Finite
