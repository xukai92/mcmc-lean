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

/-! ### Deterministic recursive candidate-row builder -/

/-- Zero-based closed interval retained by one rooted recursive-doubling run. -/
structure DoublingInterval where
  left : ℕ
  right : ℕ
deriving DecidableEq, Repr

/-- Once a subtree or completed join turns, later direction bits are ignored,
matching the production builder's early `break`. -/
structure DoublingBuilderState where
  interval : DoublingInterval
  active : Bool
deriving DecidableEq, Repr

/-- Fuel-bounded structural endpoint test for one completed binary subtree.
Calling it with fuel at least the state count reproduces the finite recursive
test while making termination explicit. -/
def recursiveSubtreeTurns (turns : ℕ → ℕ → Bool) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | fuel + 1, left, right =>
      if left < right then
        let middle := (left + right) / 2
        turns left right ||
          recursiveSubtreeTurns turns fuel left middle ||
          recursiveSubtreeTurns turns fuel (middle + 1) right
      else false

/-- Execute one depth-indexed left/right expansion. Out-of-range expansions
and U-turns both stop the row permanently at its preceding interval. -/
def advanceRecursiveDoubling
    (count : ℕ) (turns : ℕ → ℕ → Bool) (depth : ℕ)
    (state : DoublingBuilderState) (growRight : Bool) : DoublingBuilderState :=
  if !state.active then state
  else
    let width := 2 ^ depth
    let withinBounds := if growRight then
      state.interval.right + width < count
    else
      width ≤ state.interval.left
    if !withinBounds then { state with active := false }
    else
      let proposedLeft := if growRight then state.interval.left
        else state.interval.left - width
      let proposedRight := if growRight then state.interval.right + width
        else state.interval.right
      let newLeft := if growRight then state.interval.right + 1 else proposedLeft
      let newRight := if growRight then proposedRight else state.interval.left - 1
      if recursiveSubtreeTurns turns count newLeft newRight ||
          turns proposedLeft proposedRight then
        { state with active := false }
      else
        { interval := { left := proposedLeft, right := proposedRight },
          active := true }

def runRecursiveDoubling
    (count : ℕ) (turns : ℕ → ℕ → Bool) :
    ℕ → DoublingBuilderState → List Bool → DoublingBuilderState
  | _, state, [] => state
  | depth, state, direction :: rest =>
      runRecursiveDoubling count turns (depth + 1)
        (advanceRecursiveDoubling count turns depth state direction) rest

/-- Candidate row emitted for one root and one complete direction trace. -/
def recursiveDoublingCandidateRow
    (count depth : ℕ) (turns : Fin count → Fin count → Bool)
    (trace : Fin depth → Bool) (root : Fin count) : Finset (Fin count) :=
  let turnsNat := fun left right =>
    if hleft : left < count then
      if hright : right < count then turns ⟨left, hleft⟩ ⟨right, hright⟩
      else true
    else true
  let final := runRecursiveDoubling count turnsNat 0
    { interval := { left := root.val, right := root.val }, active := true }
    (List.ofFn trace)
  Finset.univ.filter fun state =>
    final.interval.left ≤ state.val ∧ state.val ≤ final.interval.right

/-- Concrete candidate function denoted by the generated recursive builder. -/
def recursiveDoublingProgram
    (count depth : ℕ) (turns : Fin count → Fin count → Bool) :
    CheckedRecursiveDoublingProgram (Fin count) depth where
  candidates trace root := recursiveDoublingCandidateRow count depth turns trace root

/-- Pointwise callback agreement is sufficient for equality of every emitted
candidate row. Thus numerical refinement need only certify the U-turn bits;
all interval and early-stop control flow is shared exactly. -/
theorem recursiveDoublingCandidateRow_congr
    (count depth : ℕ) (computedTurns idealTurns : Fin count → Fin count → Bool)
    (hagrees : ∀ left right, computedTurns left right = idealTurns left right)
    (trace : Fin depth → Bool) (root : Fin count) :
    recursiveDoublingCandidateRow count depth computedTurns trace root =
      recursiveDoublingCandidateRow count depth idealTurns trace root := by
  have hturns : computedTurns = idealTurns := by
    funext left right
    exact hagrees left right
  rw [hturns]

theorem recursiveDoublingProgram_candidates_eq
    (count depth : ℕ) (computedTurns idealTurns : Fin count → Fin count → Bool)
    (hagrees : ∀ left right, computedTurns left right = idealTurns left right) :
    (recursiveDoublingProgram count depth computedTurns).candidates =
      (recursiveDoublingProgram count depth idealTurns).candidates := by
  funext trace root
  exact recursiveDoublingCandidateRow_congr count depth computedTurns idealTurns
    hagrees trace root

@[simp] theorem recursiveDoublingCandidateRow_zero_depth
    (count : ℕ) (turns : Fin count → Fin count → Bool) (root : Fin count) :
    recursiveDoublingCandidateRow count 0 turns (fun index => nomatch index) root =
      {root} := by
  ext state
  simp only [recursiveDoublingCandidateRow, List.ofFn_zero,
    runRecursiveDoubling, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro h
    exact Fin.eq_of_val_eq (Nat.le_antisymm h.2 h.1)
  · intro h
    subst state
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩

end Mcmc.Executable.DynamicTreeIR
