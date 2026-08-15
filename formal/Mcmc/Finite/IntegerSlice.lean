import Mcmc.Finite.CollapsedConditional
import Mathlib.Data.Fintype.Fin

/-!
# Executable finite integer slice sampling

For positive integer weights bounded by `maxHeight`, the under-the-graph state
space is finite: `(x,h)` is admitted exactly when `h < weight x`.  Alternating
the two exact finite conditionals and projecting to `x` gives an executable
slice transition.  The proof uses the generic conditional and
lift--evolve--project layers, while this module identifies its stationary
marginal with the normalized integer weights.
-/

open scoped BigOperators

namespace Mcmc.Finite.IntegerSlice

open MarkovKernel
open Mcmc.Finite.Conditional

variable {State : Type*} [Fintype State] [DecidableEq State] [Nonempty State]

/-- Total unnormalized integer mass. -/
def normalizer (weight : State → ℕ) : ℕ := ∑ x, weight x

omit [DecidableEq State] in
theorem normalizer_pos (weight : State → ℕ) (hpositive : ∀ x, 0 < weight x) :
    0 < normalizer weight := by
  let x : State := Classical.choice ‹Nonempty State›
  exact (hpositive x).trans_le <| Finset.single_le_sum
    (fun y _ => Nat.zero_le (weight y)) (Finset.mem_univ x)

/-- Normalized target represented by positive integer weights. -/
noncomputable def target (weight : State → ℕ)
    (hpositive : ∀ x, 0 < weight x) : Distribution State where
  mass x := (weight x : ℝ) / normalizer weight
  nonneg x := by positivity
  sum_mass := by
    rw [← Finset.sum_div]
    have hcast : (∑ x, (weight x : ℝ)) = (normalizer weight : ℝ) := by
      simp [normalizer]
    rw [hcast]
    exact div_self (by exact_mod_cast (normalizer_pos weight hpositive).ne')

omit [Fintype State] [DecidableEq State] [Nonempty State] in
theorem sum_height_indicator (maxHeight : ℕ) (weight : State → ℕ)
    (hbounded : ∀ x, weight x ≤ maxHeight) (x : State) (c : ℝ) :
    (∑ h : Fin maxHeight, if h.val < weight x then c else 0) =
      (weight x : ℝ) * c := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Fin.card_filter_val_lt, Nat.min_eq_right (hbounded x)]

/-- Uniform law on the finite integer region under the graph. -/
noncomputable def underGraph
    (maxHeight : ℕ) (weight : State → ℕ)
    (hpositive : ∀ x, 0 < weight x)
    (_hbounded : ∀ x, weight x ≤ maxHeight) :
    Distribution (State × Fin maxHeight) where
  mass z := if z.2.val < weight z.1 then
      1 / normalizer weight else 0
  nonneg z := by split <;> positivity
  sum_mass := by
    rw [Fintype.sum_prod_type]
    have hrow (x : State) :
        (∑ h : Fin maxHeight,
          if h.val < weight x then (1 : ℝ) / normalizer weight else 0) =
          (weight x : ℝ) / normalizer weight := by
      rw [sum_height_indicator maxHeight weight _hbounded x]
      simp [div_eq_mul_inv]
    simp_rw [hrow]
    rw [← Finset.sum_div]
    have hcast : (∑ x, (weight x : ℝ)) = (normalizer weight : ℝ) := by
      simp [normalizer]
    rw [hcast]
    exact div_self (by exact_mod_cast (normalizer_pos weight hpositive).ne')

/-- Refresh the position coordinate from its exact horizontal conditional at
the retained integer height. -/
noncomputable def horizontalRefresh
    (maxHeight : ℕ) (weight : State → ℕ)
    (hpositive : ∀ x, 0 < weight x)
    (hbounded : ∀ x, weight x ≤ maxHeight) :
    MarkovKernel (State × Fin maxHeight) :=
  Mcmc.Finite.Conditional.kernel
    (underGraph maxHeight weight hpositive hbounded) Prod.snd

theorem horizontalRefresh_stationary
    (maxHeight : ℕ) (weight : State → ℕ)
    (hpositive : ∀ x, 0 < weight x)
    (hbounded : ∀ x, weight x ≤ maxHeight) :
    (horizontalRefresh maxHeight weight hpositive hbounded).Stationary
      (underGraph maxHeight weight hpositive hbounded) :=
  Mcmc.Finite.Conditional.kernel_stationary _ Prod.snd

/-- Exact finite slice sampler: condition on the current position coordinate,
refresh horizontally at the sampled height, then project back to position. -/
noncomputable def sampler
    (maxHeight : ℕ) (weight : State → ℕ)
    (hpositive : ∀ x, 0 < weight x)
    (hbounded : ∀ x, weight x ≤ maxHeight) : MarkovKernel State :=
  collapsedKernel (underGraph maxHeight weight hpositive hbounded) Prod.fst
    (horizontalRefresh maxHeight weight hpositive hbounded)

/-- The position marginal of the finite under-the-graph law is exactly the
normalized integer-weight target. -/
theorem statisticMarginal_underGraph
    (maxHeight : ℕ) (weight : State → ℕ)
    (hpositive : ∀ x, 0 < weight x)
    (hbounded : ∀ x, weight x ≤ maxHeight) :
    statisticMarginal (underGraph maxHeight weight hpositive hbounded) Prod.fst =
      target weight hpositive := by
  apply Distribution.ext
  funext x
  rw [statisticMarginal_mass]
  unfold fiberMass underGraph target
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single x]
  · simp only [if_true]
    rw [sum_height_indicator maxHeight weight hbounded x]
    simp [div_eq_mul_inv]
  · intro y _hy hyx
    simp [hyx]
  · simp

/-- The executable finite integer slice sampler preserves the normalized
weight target. -/
theorem sampler_stationary
    (maxHeight : ℕ) (weight : State → ℕ)
    (hpositive : ∀ x, 0 < weight x)
    (hbounded : ∀ x, weight x ≤ maxHeight) :
    (sampler maxHeight weight hpositive hbounded).Stationary
      (target weight hpositive) := by
  rw [← statisticMarginal_underGraph maxHeight weight hpositive hbounded]
  exact collapsedKernel_stationary _ Prod.fst _
    (horizontalRefresh_stationary maxHeight weight hpositive hbounded)

end Mcmc.Finite.IntegerSlice
