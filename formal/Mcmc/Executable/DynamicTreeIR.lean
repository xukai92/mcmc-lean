import Mcmc.Finite.CertifiedDynamicTree

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

/-- State-independent random trace sampled before recursive construction. -/
inductive TracePolicy where
  | fairDirectionBits
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
  tracePolicy : TracePolicy
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
  tracePolicy := .fairDirectionBits
  stopRule := .endpointUTurn
  subtreePolicy := .recursiveExclusion
  selectionPolicy := .eligibleCountStreaming
  failurePolicy := .checkedOrIdentity

/-! ### Mathematical semantics of the generated recursion -/

/-- Proof-relevant finite semantics of the generated recursive-doubling
program. A direction trace is the program's state-independent auxiliary draw;
the runtime builder supplies one candidate row for every possible current
root. The global checker, rather than an unproved NUTS reroot claim, decides
whether that trace selects from its row or falls back to identity. -/
structure CheckedRecursiveDoublingProgram
    (State : Type*) [Fintype State] [DecidableEq State] (depth : ℕ) where
  candidates : (Fin depth → Bool) → State → Finset State

/-- Exact finite kernel denoted by the generated checked recursion. -/
noncomputable def CheckedRecursiveDoublingProgram.interpret
    {State : Type*} [Fintype State] [DecidableEq State] {depth : ℕ}
    (program : CheckedRecursiveDoublingProgram State depth)
    (target : Distribution State) (htarget : ∀ state, 0 < target.mass state) :
    Mcmc.Finite.MarkovKernel State :=
  CertifiedDynamicTree.randomizedCheckedOrIdentityKernel
    (uniformDirectionTraceLaw depth) target program.candidates htarget

/-- The interpretation is literally the finite auxiliary mixture over every
fair direction trace. This is the refinement target for the Julia recursion's
direction draws and global candidate-row checker. -/
theorem CheckedRecursiveDoublingProgram.interpret_prob
    {State : Type*} [Fintype State] [DecidableEq State] {depth : ℕ}
    (program : CheckedRecursiveDoublingProgram State depth)
    (target : Distribution State) (htarget : ∀ state, 0 < target.mass state)
    (current next : State) :
    (program.interpret target htarget).prob current next =
      ∑ trace : Fin depth → Bool,
        (uniformDirectionTraceLaw depth).mass trace *
          (CertifiedDynamicTree.checkedOrIdentityKernel target
            (program.candidates trace) htarget).prob current next := rfl

/-- The exact generated recursion preserves the declared target for every
candidate-row builder. Invalid direction traces are explicit identity
components, so no unconditional standard-NUTS equivalence is assumed. -/
theorem CheckedRecursiveDoublingProgram.stationary
    {State : Type*} [Fintype State] [DecidableEq State] {depth : ℕ}
    (program : CheckedRecursiveDoublingProgram State depth)
    (target : Distribution State) (htarget : ∀ state, 0 < target.mass state) :
    (program.interpret target htarget).Stationary target :=
  CertifiedDynamicTree.randomizedCheckedOrIdentityKernel_stationary
    (uniformDirectionTraceLaw depth) target program.candidates htarget

end Mcmc.Executable.DynamicTreeIR
