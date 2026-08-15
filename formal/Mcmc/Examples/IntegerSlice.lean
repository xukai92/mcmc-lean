import Mcmc.Finite.IntegerSlice

/-! # Two-state executable integer slice example -/

namespace Mcmc.Examples.IntegerSlice

open Mcmc.Finite MarkovKernel

def weight : Bool → ℕ
  | false => 1
  | true => 2

theorem weight_pos (x : Bool) : 0 < weight x := by cases x <;> decide

theorem weight_le_two (x : Bool) : weight x ≤ 2 := by cases x <;> decide

noncomputable def transition : MarkovKernel Bool :=
  Mcmc.Finite.IntegerSlice.sampler 2 weight weight_pos weight_le_two

theorem transition_stationary :
    transition.Stationary
      (Mcmc.Finite.IntegerSlice.target weight weight_pos) :=
  Mcmc.Finite.IntegerSlice.sampler_stationary 2 weight weight_pos weight_le_two

@[simp] theorem target_mass_false :
    (Mcmc.Finite.IntegerSlice.target weight weight_pos).mass false = 1 / 3 := by
  norm_num [Mcmc.Finite.IntegerSlice.target,
    Mcmc.Finite.IntegerSlice.normalizer, weight]

@[simp] theorem target_mass_true :
    (Mcmc.Finite.IntegerSlice.target weight weight_pos).mass true = 2 / 3 := by
  norm_num [Mcmc.Finite.IntegerSlice.target,
    Mcmc.Finite.IntegerSlice.normalizer, weight]

end Mcmc.Examples.IntegerSlice
