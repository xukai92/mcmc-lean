import Mcmc.Kernel.AuxiliaryGibbs

/-!
# Composable general-state inference operators

This module lifts the finite composable-inference interface to mathlib's
general-state Markov kernels.  Scope annotations are execution metadata:
correctness requires every full-state operator to preserve the same target,
but does not require scopes to be disjoint or exhaustive.

The named PG--HMC construction captures the mathematical core used by a
probabilistic-programming runtime.  Particle Gibbs and HMC may have very
different internal implementations; once each induced full-state kernel
preserves the joint law, their sequential composition does too.
-/

open MeasureTheory
open scoped ProbabilityTheory

namespace Mcmc.Kernel.ComposableInference

open ProbabilityTheory

variable {Variable State : Type*} [MeasurableSpace State]

/-- A general-state target-preserving transition together with metadata
describing the model variables it may update. -/
structure ScopedOperator (target : Measure State) where
  scope : Set Variable
  kernel : Kernel State State
  isMarkov : IsMarkovKernel kernel := by infer_instance
  invariant : kernel.Invariant target

attribute [instance] ScopedOperator.isMarkov

/-- Execute target-preserving operators from left to right. -/
noncomputable def schedule (target : Measure State) :
    List (ScopedOperator (Variable := Variable) target) → Kernel State State
  | [] => Kernel.id
  | operator :: operators => schedule target operators ∘ₖ operator.kernel

instance schedule.instIsMarkovKernel (target : Measure State)
    (operators : List (ScopedOperator (Variable := Variable) target)) :
    IsMarkovKernel (schedule target operators) := by
  induction operators with
  | nil => simp only [schedule]; infer_instance
  | cons operator operators ih =>
      simp only [schedule]
      infer_instance

/-- The identity general-state kernel preserves every measure. -/
theorem id_invariant (target : Measure State) :
    (Kernel.id : Kernel State State).Invariant target := by
  rw [Kernel.Invariant]
  exact Measure.id_comp

/-- Every finite schedule of operators preserving a common target preserves
that target, including schedules with overlapping declared scopes. -/
theorem schedule_invariant (target : Measure State)
    (operators : List (ScopedOperator (Variable := Variable) target)) :
    (schedule target operators).Invariant target := by
  induction operators with
  | nil => exact id_invariant target
  | cons operator operators ih =>
      exact ih.comp operator.invariant

/-- The general-state PG--HMC composition: update the particle/latent block,
then update the differentiable block, with both represented as full-state
kernels on their common joint state space. -/
noncomputable def pgHmcKernel (pgUpdate hmcUpdate : Kernel State State) :
    Kernel State State :=
  hmcUpdate ∘ₖ pgUpdate

instance pgHmcKernel.instIsMarkovKernel
    (pgUpdate hmcUpdate : Kernel State State)
    [IsMarkovKernel pgUpdate] [IsMarkovKernel hmcUpdate] :
    IsMarkovKernel (pgHmcKernel pgUpdate hmcUpdate) := by
  unfold pgHmcKernel
  infer_instance

/-- General-state correctness of a PG-like update followed by an HMC-like
update.  This proves stationarity of the composition, not convergence from an
arbitrary initial law. -/
theorem pgHmcKernel_invariant (target : Measure State)
    (pgUpdate hmcUpdate : Kernel State State)
    (hpg : pgUpdate.Invariant target)
    (hhmc : hmcUpdate.Invariant target) :
    (pgHmcKernel pgUpdate hmcUpdate).Invariant target := by
  exact hhmc.comp hpg

/-- Instantiate the PG side with an exact auxiliary-variable conditional
update.  Its Bayes-factorization obligation and the HMC invariance obligation
are kept separate, matching how the two engines are verified. -/
theorem pgHmc_of_auxiliaryFactorization_invariant
    {Particle : Type*} [MeasurableSpace Particle]
    (target : Measure State) [SFinite target]
    (particleForward : Kernel State Particle)
    (particleReverse : Kernel Particle State)
    (hmcUpdate : Kernel State State)
    [IsMarkovKernel particleForward] [IsMarkovKernel particleReverse]
    [IsMarkovKernel hmcUpdate]
    (hfactor : Mcmc.Kernel.auxiliaryFirstJoint target particleForward =
      (particleForward ∘ₘ target) ⊗ₘ particleReverse)
    (hhmc : hmcUpdate.Invariant target) :
    (pgHmcKernel
      (Mcmc.Kernel.twoBlockConditional particleForward particleReverse)
      hmcUpdate).Invariant target := by
  apply pgHmcKernel_invariant target
  · exact Mcmc.Kernel.twoBlockConditional_invariant target
      particleForward particleReverse hfactor
  · exact hhmc

/-- Package a PG--HMC pair as a target-preserving scoped operator. -/
noncomputable def pgHmcOperator (target : Measure State)
    (pgScope hmcScope : Set Variable)
    (pgUpdate hmcUpdate : Kernel State State)
    [IsMarkovKernel pgUpdate] [IsMarkovKernel hmcUpdate]
    (hpg : pgUpdate.Invariant target) (hhmc : hmcUpdate.Invariant target) :
    ScopedOperator (Variable := Variable) target where
  scope := pgScope ∪ hmcScope
  kernel := pgHmcKernel pgUpdate hmcUpdate
  invariant := pgHmcKernel_invariant target pgUpdate hmcUpdate hpg hhmc

end Mcmc.Kernel.ComposableInference
