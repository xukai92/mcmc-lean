import Mcmc.PDMP.Generator
import Mcmc.Finite.Dynamics
import Mathlib.Tactic

/-!
# Bounded-rate uniformization

A finite continuous-time jump generator with total off-diagonal rate bounded
by `Λ` can be represented by a discrete Markov kernel: at the events of a
rate-`Λ` Poisson clock, take a genuine jump with probability `q(x,y)/Λ` or a
self-loop for the unused rate. This file proves the exact kernel algebra and
transports rate detailed balance to ordinary kernel reversibility.

The Poisson path construction and its real-time semigroup are deliberately a
later layer; this module supplies their checked embedded-chain foundation.
-/

open scoped BigOperators

namespace Mcmc.PDMP.FiniteRateGenerator

open Mcmc.Finite MarkovKernel

variable {State : Type*} [Fintype State] [DecidableEq State]

/-- Total rate of genuine (off-diagonal) jumps from a state. -/
def exitRate (rates : FiniteRateGenerator State) (x : State) : ℝ :=
  ∑ y, if y = x then 0 else rates.rate x y

theorem exitRate_nonneg (rates : FiniteRateGenerator State) (x : State) :
    0 ≤ rates.exitRate x := by
  unfold exitRate
  exact Finset.sum_nonneg fun y _ => by
    by_cases h : y = x <;> simp [h, rates.nonneg]

/-- The discrete embedded kernel obtained by uniformizing at rate `Λ`. -/
noncomputable def uniformizedKernel (rates : FiniteRateGenerator State) (Λ : ℝ)
    (hΛ : 0 < Λ) (hbound : ∀ x, rates.exitRate x ≤ Λ) : MarkovKernel State where
  prob x y :=
    if y = x then 1 - rates.exitRate x / Λ else rates.rate x y / Λ
  nonneg x y := by
    by_cases h : y = x
    · simp only [h, if_true]
      exact sub_nonneg.mpr (div_le_one hΛ |>.mpr (hbound x))
    · simp only [h, if_false]
      exact div_nonneg (rates.nonneg x y) (le_of_lt hΛ)
  sum_prob x := by
    have herase :
        (∑ y ∈ (Finset.univ : Finset State).erase x, rates.rate x y) =
          rates.exitRate x := by
      unfold exitRate
      calc
        (∑ y ∈ (Finset.univ : Finset State).erase x, rates.rate x y) =
            ∑ y ∈ (Finset.univ : Finset State).erase x,
              (if y = x then 0 else rates.rate x y) := by
          apply Finset.sum_congr rfl
          intro y hy
          simp [(Finset.mem_erase.mp hy).1]
        _ = ∑ y, if y = x then 0 else rates.rate x y := by
          symm
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ x)]
          simp
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ x)]
    calc
      (∑ y ∈ (Finset.univ : Finset State).erase x,
          (if y = x then 1 - rates.exitRate x / Λ
            else rates.rate x y / Λ)) +
          (if x = x then 1 - rates.exitRate x / Λ
            else rates.rate x x / Λ) =
          (∑ y ∈ (Finset.univ : Finset State).erase x,
            rates.rate x y / Λ) + (1 - rates.exitRate x / Λ) := by
        congr 1
        · apply Finset.sum_congr rfl
          intro y hy
          simp [(Finset.mem_erase.mp hy).1]
        · simp
      _ = 1 := by
        rw [← Finset.sum_div, herase]
        ring

@[simp] theorem uniformizedKernel_prob_same
    (rates : FiniteRateGenerator State) (Λ : ℝ)
    (hΛ : 0 < Λ) (hbound : ∀ x, rates.exitRate x ≤ Λ) (x : State) :
    (rates.uniformizedKernel Λ hΛ hbound).prob x x =
      1 - rates.exitRate x / Λ := by
  simp [uniformizedKernel]

@[simp] theorem uniformizedKernel_prob_ne
    (rates : FiniteRateGenerator State) (Λ : ℝ)
    (hΛ : 0 < Λ) (hbound : ∀ x, rates.exitRate x ≤ Λ)
    (x y : State) (hne : y ≠ x) :
    (rates.uniformizedKernel Λ hΛ hbound).prob x y =
      rates.rate x y / Λ := by
  simp [uniformizedKernel, hne]

/-- Rate detailed balance is exactly detailed balance of every valid
uniformization kernel. -/
theorem uniformizedKernel_reversible
    (rates : FiniteRateGenerator State) (target : Distribution State)
    (hrev : rates.Reversible target) (Λ : ℝ)
    (hΛ : 0 < Λ) (hbound : ∀ x, rates.exitRate x ≤ Λ) :
    (rates.uniformizedKernel Λ hΛ hbound).Reversible target := by
  intro x y
  by_cases hxy : x = y
  · subst y
    rfl
  · have hyx : y ≠ x := Ne.symm hxy
    rw [uniformizedKernel_prob_ne rates Λ hΛ hbound x y hyx,
      uniformizedKernel_prob_ne rates Λ hΛ hbound y x hxy]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    calc
      target.mass x * (rates.rate x y * Λ⁻¹) =
          (target.mass x * rates.rate x y) * Λ⁻¹ := by ring
      _ = (target.mass y * rates.rate y x) * Λ⁻¹ := by rw [hrev x y]
      _ = target.mass y * (rates.rate y x * Λ⁻¹) := by ring

/-- A reversible finite-rate generator therefore has a stationary embedded
uniformization chain. -/
theorem uniformizedKernel_stationary
    (rates : FiniteRateGenerator State) (target : Distribution State)
    (hrev : rates.Reversible target) (Λ : ℝ)
    (hΛ : 0 < Λ) (hbound : ∀ x, rates.exitRate x ≤ Λ) :
    (rates.uniformizedKernel Λ hΛ hbound).Stationary target :=
  (rates.uniformizedKernel_reversible target hrev Λ hΛ hbound).stationary

end Mcmc.PDMP.FiniteRateGenerator
