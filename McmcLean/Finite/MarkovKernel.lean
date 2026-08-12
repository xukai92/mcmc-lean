import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

/-!
# Finite-state Markov kernels

This file provides a deliberately small finite-state interface.  It lets the
first Metropolis--Hastings correctness proof stay algebraic; a later layer can
embed these kernels into `ProbabilityTheory.Kernel`.
-/

open scoped BigOperators

namespace McmcLean.Finite

/-- A transition matrix on a finite state space, with nonnegative entries and
rows summing to one. -/
structure MarkovKernel (State : Type*) [Fintype State] where
  prob : State → State → ℝ
  nonneg : ∀ x y, 0 ≤ prob x y
  sum_prob : ∀ x, ∑ y, prob x y = 1

namespace MarkovKernel

variable {State : Type*} [Fintype State]

/-- A nonnegative, normalized probability mass function on a finite type. -/
structure Distribution (State : Type*) [Fintype State] where
  mass : State → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  sum_mass : ∑ x, mass x = 1

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

end McmcLean.Finite
