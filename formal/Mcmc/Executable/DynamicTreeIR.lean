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

/-- Concrete interpretation of a direction trace as the initial leaf's
zero-based position in a completed tree. This convention is proved against
`doublingRootEquiv` in `Mcmc.Finite.RootedTrace`. -/
inductive RootEncoding where
  | lsbFirstGrowRightZero
deriving DecidableEq, Repr

/-- Exact decoder denoted by the generated root-encoding tag. -/
def RootEncoding.decode (encoding : RootEncoding) (depth : ℕ)
    (trace : Fin depth → Bool) : ℕ :=
  match encoding with
  | .lsbFirstGrowRightZero =>
      Mcmc.Finite.MarkovKernel.directionTraceRootValue depth trace

/-- The generated encoding recovers the zero-based root offset from the
canonical reconstruction trace. -/
@[simp] theorem RootEncoding.decode_directionTraceForRoot
    (depth : ℕ) (root : Fin (2 ^ depth)) :
    RootEncoding.lsbFirstGrowRightZero.decode depth
        (Mcmc.Finite.MarkovKernel.directionTraceForRoot depth root) = root.val :=
  Mcmc.Finite.MarkovKernel.directionTraceRootValue_directionTraceForRoot depth root

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
  rootEncoding : RootEncoding
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
  rootEncoding := .lsbFirstGrowRightZero
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

/-- Productive safe semantics obtained by replacing every raw row with its
canonical coherent subrow. This mode requires only structural root retention;
it never adds a state excluded by the recursive builder. -/
noncomputable def CheckedRecursiveDoublingProgram.interpretCoherent
    {State : Type*} [Fintype State] [DecidableEq State] {depth : ℕ}
    (program : CheckedRecursiveDoublingProgram State depth)
    (target : Distribution State) (htarget : ∀ state, 0 < target.mass state)
    (hroot : ∀ trace root, root ∈ program.candidates trace root) :
    Mcmc.Finite.MarkovKernel State :=
  CertifiedDynamicTree.randomizedCoherentKernel
    (uniformDirectionTraceLaw depth) target program.candidates hroot htarget

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

/-- Coherent-subrow recursive execution is stationary without discarding an
entire direction trace merely because some raw rows disagree. -/
theorem CheckedRecursiveDoublingProgram.interpretCoherent_stationary
    {State : Type*} [Fintype State] [DecidableEq State] {depth : ℕ}
    (program : CheckedRecursiveDoublingProgram State depth)
    (target : Distribution State) (htarget : ∀ state, 0 < target.mass state)
    (hroot : ∀ trace root, root ∈ program.candidates trace root) :
    (program.interpretCoherent target htarget hroot).Stationary target :=
  CertifiedDynamicTree.randomizedCoherentKernel_stationary
    (uniformDirectionTraceLaw depth) target program.candidates hroot htarget

/-- Candidate-row equality lifts through the entire generated semantics:
the fair direction-trace mixture, global reroot check, checked selection, and
identity fallback are all shared. -/
theorem CheckedRecursiveDoublingProgram.interpret_congr
    {State : Type*} [Fintype State] [DecidableEq State] {depth : ℕ}
    (computed ideal : CheckedRecursiveDoublingProgram State depth)
    (hcandidates : computed.candidates = ideal.candidates)
    (target : Distribution State) (htarget : ∀ state, 0 < target.mass state) :
    computed.interpret target htarget = ideal.interpret target htarget := by
  unfold CheckedRecursiveDoublingProgram.interpret
  rw [hcandidates]

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

/-- Fuel-bounded continuation bit for the complete recursive subtree call.
Singleton intervals run the leaf eligibility/divergence check; internal
intervals require both recursive calls and their endpoint join to continue. -/
def recursiveSubtreeContinues
    (leafContinues : ℕ → Bool) (turns : ℕ → ℕ → Bool) :
    ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | fuel + 1, left, right =>
      if left < right then
        let middle := (left + right) / 2
        recursiveSubtreeContinues leafContinues turns fuel left middle &&
          recursiveSubtreeContinues leafContinues turns fuel (middle + 1) right &&
          !(turns left right)
      else leafContinues left

/-- Structural turn aggregation for a balanced interval of `2 ^ depth`
consecutive phase indices beginning at `start`. This is the power-of-two
specialization of `recursiveSubtreeTurns`, stated without midpoint division. -/
def balancedSubtreeTurns (turns : ℕ → ℕ → Bool) : ℕ → ℕ → Bool
  | 0, _ => false
  | depth + 1, start =>
      let half := 2 ^ depth
      turns start (start + 2 * half - 1) ||
        balancedSubtreeTurns turns depth start ||
        balancedSubtreeTurns turns depth (start + half)

private theorem balancedInterval_midpoint (start half : ℕ) (hhalf : 0 < half) :
    (start + (start + 2 * half - 1)) / 2 = start + half - 1 := by
  omega

/-- With enough recursion fuel, the concrete index-based subtree checker is
exactly balanced structural aggregation on a power-of-two interval. -/
theorem recursiveSubtreeTurns_eq_balancedSubtreeTurns
    (turns : ℕ → ℕ → Bool) (depth start fuel : ℕ)
    (hfuel : depth < fuel) :
    recursiveSubtreeTurns turns fuel start (start + 2 ^ depth - 1) =
      balancedSubtreeTurns turns depth start := by
  induction depth generalizing start fuel with
  | zero =>
      cases fuel with
      | zero => omega
      | succ fuel => simp [recursiveSubtreeTurns, balancedSubtreeTurns]
  | succ depth ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hfuel' : depth < fuel := by omega
          have hhalf : 0 < 2 ^ depth := pow_pos (by omega) _
          have hleftRight :
              start < start + 2 ^ (depth + 1) - 1 := by
            rw [pow_succ]
            omega
          rw [recursiveSubtreeTurns]
          simp only [hleftRight, if_true]
          have hmidpoint :
              (start + (start + 2 ^ (depth + 1) - 1)) / 2 =
                start + 2 ^ depth - 1 := by
            rw [pow_succ]
            simpa [Nat.mul_comm] using
              balancedInterval_midpoint start (2 ^ depth) hhalf
          rw [hmidpoint]
          rw [ih start fuel hfuel']
          have hnext : start + 2 ^ depth - 1 + 1 =
              start + 2 ^ depth := by omega
          rw [hnext]
          have hright :
              start + 2 ^ (depth + 1) - 1 =
                (start + 2 ^ depth) + 2 ^ depth - 1 := by
            rw [pow_succ]
            omega
          rw [hright, ih (start + 2 ^ depth) fuel hfuel']
          have hend : start + 2 ^ depth + 2 ^ depth - 1 =
              start + 2 * 2 ^ depth - 1 := by omega
          simp [balancedSubtreeTurns, hend]

/-- Structural aggregation on the consecutive-index phase tree is the same
balanced Boolean computation. -/
theorem balancedIntervalPhaseTree_anyEndpointTurns
    (turns : ℕ → ℕ → Bool) (depth start : ℕ) :
    (balancedIntervalPhaseTree depth start).anyEndpointTurns turns =
      balancedSubtreeTurns turns depth start := by
  induction depth generalizing start with
  | zero => rfl
  | succ depth ih =>
      have hend : start + 2 ^ depth + 2 ^ depth - 1 =
          start + 2 * 2 ^ depth - 1 := by omega
      simp [balancedIntervalPhaseTree, RecursivePhaseTree.anyEndpointTurns,
        balancedSubtreeTurns, ih, hend]

/-- Therefore the actual fuel-bounded midpoint recursion agrees with the
structural phase-tree turn fold on every complete balanced interval. -/
theorem recursiveSubtreeTurns_eq_balancedIntervalPhaseTree
    (turns : ℕ → ℕ → Bool) (depth start fuel : ℕ)
    (hfuel : depth < fuel) :
    recursiveSubtreeTurns turns fuel start (start + 2 ^ depth - 1) =
      (balancedIntervalPhaseTree depth start).anyEndpointTurns turns := by
  rw [recursiveSubtreeTurns_eq_balancedSubtreeTurns turns depth start fuel hfuel,
    balancedIntervalPhaseTree_anyEndpointTurns]

/-- With sufficient fuel, the concrete recursive continuation—including
arbitrary leaf eligibility/divergence bits—is the completed structural flag
tree's continuation bit on the same balanced interval. -/
theorem recursiveSubtreeContinues_eq_buildFlagTree
    (leafContinues : ℕ → Bool) (turns : ℕ → ℕ → Bool)
    (depth start fuel : ℕ) (hfuel : depth < fuel) :
    recursiveSubtreeContinues leafContinues turns fuel start
        (start + 2 ^ depth - 1) =
      ((balancedIntervalPhaseTree depth start).toBuildFlagTree
        leafContinues turns).continues := by
  induction depth generalizing start fuel with
  | zero =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp [recursiveSubtreeContinues, balancedIntervalPhaseTree,
            RecursivePhaseTree.toBuildFlagTree]
  | succ depth ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hfuel' : depth < fuel := by omega
          have hhalf : 0 < 2 ^ depth := pow_pos (by omega) _
          have hleftRight :
              start < start + 2 ^ (depth + 1) - 1 := by
            rw [pow_succ]
            omega
          rw [recursiveSubtreeContinues]
          simp only [hleftRight, if_true]
          have hmidpoint :
              (start + (start + 2 ^ (depth + 1) - 1)) / 2 =
                start + 2 ^ depth - 1 := by
            rw [pow_succ]
            simpa [Nat.mul_comm] using
              balancedInterval_midpoint start (2 ^ depth) hhalf
          rw [hmidpoint, ih start fuel hfuel']
          have hnext : start + 2 ^ depth - 1 + 1 =
              start + 2 ^ depth := by omega
          rw [hnext]
          have hright :
              start + 2 ^ (depth + 1) - 1 =
                (start + 2 ^ depth) + 2 ^ depth - 1 := by
            rw [pow_succ]
            omega
          rw [hright, ih (start + 2 ^ depth) fuel hfuel']
          simp [balancedIntervalPhaseTree,
            RecursivePhaseTree.toBuildFlagTree]

/-- Hence the concrete recursion and production-style structural online
recursion return identical continuation bits, including every leaf failure. -/
theorem recursiveSubtreeContinues_eq_onlineBuildSummary
    (leafContinues : ℕ → Bool) (turns : ℕ → ℕ → Bool)
    (depth start fuel : ℕ) (hfuel : depth < fuel) :
    recursiveSubtreeContinues leafContinues turns fuel start
        (start + 2 ^ depth - 1) =
      ((balancedIntervalPhaseTree depth start).onlineBuildSummary
        leafContinues turns).continues := by
  rw [recursiveSubtreeContinues_eq_buildFlagTree leafContinues turns depth
    start fuel hfuel,
    RecursivePhaseTree.onlineBuildSummary_continues_eq_toBuildFlagTree]

/-- Equivalently, when leaves themselves are valid, the structural online
builder continues exactly when the concrete index recursion reports no turn. -/
theorem onlineBuildSummary_continues_eq_not_recursiveSubtreeTurns
    (turns : ℕ → ℕ → Bool) (depth start fuel : ℕ)
    (hfuel : depth < fuel) :
    ((balancedIntervalPhaseTree depth start).onlineBuildSummary
        (fun _ => true) turns).continues =
      !(recursiveSubtreeTurns turns fuel start
        (start + 2 ^ depth - 1)) := by
  rw [RecursivePhaseTree.onlineBuildSummary_continues_allLeaves,
    recursiveSubtreeTurns_eq_balancedIntervalPhaseTree turns depth start fuel
      hfuel]

/-- If the concrete subtree checker reports no turn, the online builder emits
exactly the consecutive balanced-interval candidate occurrences. -/
theorem onlineBuildSummary_candidates_eq_range
    (turns : ℕ → ℕ → Bool) (depth start fuel : ℕ)
    (hfuel : depth < fuel)
    (hnoTurn : recursiveSubtreeTurns turns fuel start
      (start + 2 ^ depth - 1) = false) :
    ((balancedIntervalPhaseTree depth start).onlineBuildSummary
        (fun _ => true) turns).candidates =
      (List.range (2 ^ depth)).map (start + ·) := by
  have hcontinues :
      ((balancedIntervalPhaseTree depth start).onlineBuildSummary
          (fun _ => true) turns).continues = true := by
    rw [onlineBuildSummary_continues_eq_not_recursiveSubtreeTurns
      turns depth start fuel hfuel, hnoTurn]
    rfl
  rw [RecursivePhaseTree.onlineBuildSummary_candidates_eq_leaves
    (fun _ : ℕ => true) turns (balancedIntervalPhaseTree depth start)
      hcontinues]
  exact balancedIntervalPhaseTree_leaves depth start

/-- More generally, if the concrete recursion succeeds after arbitrary leaf
checks, its structural online counterpart contains every consecutive candidate
occurrence in the balanced interval. -/
theorem onlineBuildSummary_candidates_eq_range_of_continues
    (leafContinues : ℕ → Bool) (turns : ℕ → ℕ → Bool)
    (depth start fuel : ℕ) (hfuel : depth < fuel)
    (hcontinues : recursiveSubtreeContinues leafContinues turns fuel start
      (start + 2 ^ depth - 1) = true) :
    ((balancedIntervalPhaseTree depth start).onlineBuildSummary
        leafContinues turns).candidates =
      (List.range (2 ^ depth)).map (start + ·) := by
  have honline :
      ((balancedIntervalPhaseTree depth start).onlineBuildSummary
          leafContinues turns).continues = true := by
    rw [← recursiveSubtreeContinues_eq_onlineBuildSummary leafContinues turns
      depth start fuel hfuel]
    exact hcontinues
  rw [RecursivePhaseTree.onlineBuildSummary_candidates_eq_leaves
    leafContinues turns (balancedIntervalPhaseTree depth start) honline]
  exact balancedIntervalPhaseTree_leaves depth start

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

/-- Pointwise agreement of the numerical and ideal U-turn callbacks refines
the complete randomized checked recursion, not only each deterministic row. -/
theorem recursiveDoublingProgram_interpret_eq
    (count depth : ℕ) (computedTurns idealTurns : Fin count → Fin count → Bool)
    (hagrees : ∀ left right, computedTurns left right = idealTurns left right)
    (target : Distribution (Fin count))
    (htarget : ∀ state, 0 < target.mass state) :
    (recursiveDoublingProgram count depth computedTurns).interpret target htarget =
      (recursiveDoublingProgram count depth idealTurns).interpret target htarget := by
  apply CheckedRecursiveDoublingProgram.interpret_congr
  exact recursiveDoublingProgram_candidates_eq count depth computedTurns idealTurns
    hagrees

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
