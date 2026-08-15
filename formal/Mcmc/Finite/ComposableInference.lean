import Mcmc.Finite.Gibbs

/-!
# Composable finite inference operators

Ge, Xu, and Ghahramani (2018) describe inference engines as Markov-chain
operators assigned to manually selected, possibly overlapping sets of model
variables.  Correctness depends on each induced full-state kernel preserving
the common target; disjointness or coverage of the declared scopes is a
separate modeling and execution concern.

This module makes that distinction explicit.  A `ScopedOperator` carries
scope metadata, a full-state kernel, and its target-stationarity theorem.
Arbitrary finite schedules of such operators preserve the target, including
schedules with overlapping scopes.
-/

namespace Mcmc.Finite.ComposableInference

open MarkovKernel

variable {Variable State : Type*} [Fintype State] [DecidableEq State]

/-- A target-preserving full-state transition together with the model
variables that an inference engine declares it may update. -/
structure ScopedOperator (π : Distribution State) where
  scope : Finset Variable
  kernel : MarkovKernel State
  stationary : kernel.Stationary π

/-- The declared scopes cover every model variable.  Coverage is useful for a
complete inference configuration, but is not needed for stationarity. -/
def Covers [DecidableEq Variable] {π : Distribution State}
    (operators : List (ScopedOperator (Variable := Variable) π)) : Prop :=
  ∀ v, ∃ operator ∈ operators, v ∈ operator.scope

/-- Execute a list of inference operators from left to right. -/
def schedule (π : Distribution State) :
    List (ScopedOperator (Variable := Variable) π) → MarkovKernel State
  | [] => identity
  | operator :: operators => comp (schedule π operators) operator.kernel

/-- Every finite composition of operators preserving the same target remains
target-stationary.  No disjointness assumption is imposed on their scopes. -/
theorem schedule_stationary (π : Distribution State)
    (operators : List (ScopedOperator (Variable := Variable) π)) :
    (schedule π operators).Stationary π := by
  induction operators with
  | nil => exact identity_stationary π
  | cons operator operators ih =>
      exact comp_stationary operator.kernel (schedule π operators) π
        operator.stationary ih

section TwoBlock

variable {Continuous Latent : Type*}
  [Fintype Continuous] [Fintype Latent]
  [DecidableEq Continuous] [DecidableEq Latent]

/-- The two-block PG--HMC pattern of Ge et al.: first update the latent block
conditional on the continuous state, then update the continuous block
conditional on the refreshed latent state.  The names describe intended
clients; correctness uses only the two slice-preservation equations. -/
def pgHmcKernel (pgUpdate : Continuous → MarkovKernel Latent)
    (hmcUpdate : Latent → MarkovKernel Continuous) :
    MarkovKernel (Continuous × Latent) :=
  comp (liftFst hmcUpdate) (liftSnd pgUpdate)

/-- A PG-like latent update followed by an HMC-like continuous update
preserves the joint target whenever both preserve their corresponding target
slices. -/
theorem pgHmcKernel_stationary (π : Distribution (Continuous × Latent))
    (pgUpdate : Continuous → MarkovKernel Latent)
    (hmcUpdate : Latent → MarkovKernel Continuous)
    (hpg : Gibbs.PreservesSndSlices π pgUpdate)
    (hhmc : Gibbs.PreservesFstSlices π hmcUpdate) :
    (pgHmcKernel pgUpdate hmcUpdate).Stationary π :=
  comp_stationary _ _ π
    (Gibbs.liftSnd_stationary π pgUpdate hpg)
    (Gibbs.liftFst_stationary π hmcUpdate hhmc)

end TwoBlock

end Mcmc.Finite.ComposableInference
