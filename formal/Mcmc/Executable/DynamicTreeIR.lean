import Mcmc.Finite.RootedTrace

/-!
# Dynamic-tree execution descriptors

Versioned metadata for checked dynamic-trajectory builders. The descriptor
does not assert that recursive NUTS rows pass reroot certification; it records
that completed rows must use the checked-or-identity policy proved in Lean.
-/

namespace Mcmc.Executable.DynamicTreeIR

inductive Builder where
  | recursiveDoubling
deriving DecidableEq, Repr

inductive StopRule where
  | endpointUTurn
deriving DecidableEq, Repr

inductive SubtreePolicy where
  | recursiveExclusion
deriving DecidableEq, Repr

inductive FailurePolicy where
  | checkedOrIdentity
deriving DecidableEq, Repr

/-- Endpoint selection performed by recursive eligible-count merges. This is
the discrete selection rule whose law is proved by `WeightedRepresentative`;
continuous eligibility and phase construction remain external inputs. -/
inductive SelectionPolicy where
  | eligibleCountStreaming
deriving DecidableEq, Repr

open Mcmc.Finite.MarkovKernel

/-- Exact mathematical semantics of a generated endpoint-selection policy.
For the current policy this is the recursive eligible-count merge used by
the NUTS `BuildTree` accumulator. -/
noncomputable def SelectionPolicy.interpret
    {State : Type*} [Fintype State]
    (policy : SelectionPolicy)
    (initial : WeightedRepresentative State)
    (rest : List (WeightedRepresentative State)) :
    WeightedRepresentative State :=
  match policy with
  | .eligibleCountStreaming => initial.mergeAll rest

/-- The generated eligible-count policy returns exactly the normalized law
of all retained endpoint weights, including empty intermediate subtrees. -/
theorem SelectionPolicy.eligibleCountStreaming_refines
    {State : Type*} [Fintype State]
    (initial : WeightedRepresentative State)
    (rest : List (WeightedRepresentative State))
    (hpositive : 0 <
      (SelectionPolicy.eligibleCountStreaming.interpret initial rest).totalWeight)
    (state : State) :
    (SelectionPolicy.eligibleCountStreaming.interpret initial rest).representativeLaw.mass
        state =
      (SelectionPolicy.eligibleCountStreaming.interpret initial rest).endpointWeight
          state /
        (SelectionPolicy.eligibleCountStreaming.interpret initial rest).totalWeight :=
  WeightedRepresentative.mergeAll_mass_eq_normalized initial rest hpositive state

structure Descriptor where
  name : String
  builder : Builder
  stopRule : StopRule
  subtreePolicy : SubtreePolicy
  selectionPolicy : SelectionPolicy
  failurePolicy : FailurePolicy
deriving DecidableEq, Repr

/-- Portable descriptor for the root-dependent recursive builder whose full
row family is accepted only after global reroot certification. -/
def checkedRecursiveDoubling : Descriptor where
  name := "checked-recursive-doubling"
  builder := .recursiveDoubling
  stopRule := .endpointUTurn
  subtreePolicy := .recursiveExclusion
  selectionPolicy := .eligibleCountStreaming
  failurePolicy := .checkedOrIdentity

end Mcmc.Executable.DynamicTreeIR
