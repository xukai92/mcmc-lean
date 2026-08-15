import Mcmc.Finite.ComposableInference

/-!
# Overlapping composable-inference example

This finite example exercises the scope metadata used to model Ge et al.'s
manually assigned inference engines.  The two declared scopes overlap, cover
all variables, and their scheduled full-state kernels preserve the target.
-/

namespace Mcmc.Examples.ComposableInference

open Mcmc.Finite
open Mcmc.Finite.MarkovKernel
open Mcmc.Finite.ComposableInference

inductive ModelVariable
  | continuous
  | latent
  deriving DecidableEq

noncomputable def target : Distribution (Bool × Bool) where
  mass _ := 1 / 4
  nonneg _ := by norm_num
  sum_mass := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

noncomputable def latentOperator :
    ScopedOperator (Variable := ModelVariable) target where
  scope := {ModelVariable.latent}
  kernel := identity
  stationary := identity_stationary target

/-- This operator deliberately declares an overlapping scope. -/
noncomputable def continuousAndLatentOperator :
    ScopedOperator (Variable := ModelVariable) target where
  scope := {ModelVariable.continuous, ModelVariable.latent}
  kernel := identity
  stationary := identity_stationary target

noncomputable def operators :
    List (ScopedOperator (Variable := ModelVariable) target) :=
  [latentOperator, continuousAndLatentOperator]

example : Covers operators := by
  intro v
  cases v
  · exact ⟨continuousAndLatentOperator, by simp [operators], by simp
      [continuousAndLatentOperator]⟩
  · exact ⟨latentOperator, by simp [operators], by simp [latentOperator]⟩

example : (schedule target operators).Stationary target :=
  schedule_stationary target operators

end Mcmc.Examples.ComposableInference
