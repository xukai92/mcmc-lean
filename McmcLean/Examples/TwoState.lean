import McmcLean.Finite.MetropolisHastings

/-!
# A two-state example

This file instantiates the generic theorem with a target that assigns mass
`3/4` to `true` and `1/4` to `false`, and an independent uniform proposal.
-/

open scoped BigOperators

namespace McmcLean.Examples.TwoState

open McmcLean.Finite
open McmcLean.Finite.MarkovKernel

noncomputable def target : Distribution Bool where
  mass b := if b then (3 : ℝ) / 4 else 1 / 4
  nonneg b := by cases b <;> norm_num
  sum_mass := by norm_num [Fintype.sum_bool]

noncomputable def proposal : MarkovKernel Bool where
  prob _ _ := (1 : ℝ) / 2
  nonneg _ _ := by norm_num
  sum_prob _ := by norm_num [Fintype.sum_bool]

theorem target_positive (x : Bool) : 0 < target.mass x := by
  cases x <;> norm_num [target]

/-- The generic MH theorem certifies this concrete sampler. -/
example :
    (MetropolisHastings.kernel target proposal target_positive).Stationary target :=
  MetropolisHastings.stationary target proposal target_positive

end McmcLean.Examples.TwoState
