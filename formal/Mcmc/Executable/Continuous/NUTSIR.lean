import Mcmc.Executable.Continuous.DynamicTreeRefinement

/-!
# Typed executable IR for checked NUTS tree construction

This module begins the maintained NUTS Reference path.  Unlike the portable
`DynamicTreeIR.Descriptor`, the syntax below has an executable Lean
interpretation: it fixes the bounded recursion, early-exit behavior, direction
trace, candidate occurrences, and checked failure policy.  Phase integration,
leaf-energy decisions, and endpoint U-turn decisions remain typed inputs; this
is the same callback boundary used by the continuous HMC compiler IR.

The first interpreter theorem identifies the executable subtree recursion with
the existing proof-oriented `RecursivePhaseTree.onlineBuildSummary`.  It does
not claim that floating-point callbacks equal their ideal-real counterparts;
that separate implication is supplied by `DynamicTreeRefinement` certificates.
-/

namespace Mcmc.Executable.Continuous.NUTSIR

open Mcmc.Finite.MarkovKernel

/-- Selection rule carried by a complete NUTS program.  Both rules are part of
the production runtime surface; their weighted candidate consumers are kept
separate from structural tree construction. -/
inductive SelectionRule where
  | multinomial
  | slice
deriving DecidableEq, Repr

/-- Termination predicate selected by the program. -/
inductive TerminationRule where
  | classic
  | generalized
  | strictGeneralized
deriving DecidableEq, Repr

/-- The only maintained failure semantics for a verified Reference program.
An uncertified completed candidate-row family produces an identity step. -/
inductive FailureRule where
  | checkedOrIdentity
deriving DecidableEq, Repr

/-- Closed configuration syntax for one bounded NUTS transition. -/
structure Program where
  maxDepth : ℕ
  selection : SelectionRule
  termination : TerminationRule
  failure : FailureRule := .checkedOrIdentity
deriving DecidableEq, Repr

/-- First maintained concrete Reference configuration.  Making the depth part
of the artifact keeps the initial Lean/Julia trace contract closed; a later
parameterized schema can generalize it without pretending arbitrary runtime
configurations were already covered. -/
def referenceProgram : Program where
  maxDepth := 10
  selection := .multinomial
  termination := .generalized
  failure := .checkedOrIdentity

/-- State-independent outer direction choices.  A total fixed-length function
prevents trace exhaustion from being confused with a mathematical stop. -/
structure DirectionTrace (program : Program) where
  growRight : Fin program.maxDepth → Bool

/-- Typed callback environment for the structural subtree interpreter.
`leafContinues` includes eligibility/divergence checks. -/
structure SubtreeInputs (Phase : Type*) where
  leafContinues : Phase → Bool
  endpointTurns : Phase → Phase → Bool

/-- Inspectable result emitted by the executable subtree recursion.  Candidate
occurrences preserve traversal order and multiplicity. -/
structure SubtreeResult (Phase : Type*) where
  visitedLeaves : ℕ
  candidates : List Phase
  continues : Bool
deriving Repr

/-- Convert the executable result to the proof-oriented summary type. -/
def SubtreeResult.toOnlineSummary (result : SubtreeResult Phase) :
    OnlineBuildSummary Phase where
  visitedLeaves := result.visitedLeaves
  candidates := result.candidates
  continues := result.continues

/-- Lean-owned executable early-exit recursion.  The right subtree is not
visited after the left subtree fails, matching the maintained runtime call
order. -/
def executeSubtree (inputs : SubtreeInputs Phase) :
    RecursivePhaseTree Phase → SubtreeResult Phase
  | .leaf phase =>
      ⟨1, if inputs.leafContinues phase then [phase] else [],
        inputs.leafContinues phase⟩
  | .node left right =>
      let leftResult := executeSubtree inputs left
      if !leftResult.continues then leftResult
      else
        let rightResult := executeSubtree inputs right
        if !rightResult.continues then
          ⟨leftResult.visitedLeaves + rightResult.visitedLeaves,
            leftResult.candidates ++ rightResult.candidates, false⟩
        else
          ⟨leftResult.visitedLeaves + rightResult.visitedLeaves,
            leftResult.candidates ++ rightResult.candidates,
            !(inputs.endpointTurns left.leftmost right.rightmost)⟩

/-- The executable IR recursion is exactly the already audited online tree
semantics, including early exit, visited count, and ordered candidates. -/
theorem executeSubtree_toOnlineSummary (inputs : SubtreeInputs Phase)
    (tree : RecursivePhaseTree Phase) :
    (executeSubtree inputs tree).toOnlineSummary =
      tree.onlineBuildSummary inputs.leafContinues inputs.endpointTurns := by
  induction tree with
  | leaf phase =>
      simp [executeSubtree, SubtreeResult.toOnlineSummary,
        RecursivePhaseTree.onlineBuildSummary]
  | node left right ihLeft ihRight =>
      rw [executeSubtree, RecursivePhaseTree.onlineBuildSummary]
      rw [← ihLeft, ← ihRight]
      generalize executeSubtree inputs left = leftResult
      generalize executeSubtree inputs right = rightResult
      cases leftResult with
      | mk leftVisited leftCandidates leftContinues =>
          cases leftContinues <;>
            cases rightResult with
            | mk rightVisited rightCandidates rightContinues =>
                cases rightContinues <;> rfl

/-- Successful execution emits the completed tree's leaves in exactly the
same order and multiplicity. -/
theorem executeSubtree_candidates_eq_leaves (inputs : SubtreeInputs Phase)
    (tree : RecursivePhaseTree Phase)
    (hcontinues : (executeSubtree inputs tree).continues = true) :
    (executeSubtree inputs tree).candidates = tree.leaves := by
  have hsummary :
      (tree.onlineBuildSummary inputs.leafContinues
        inputs.endpointTurns).continues = true := by
    rw [← executeSubtree_toOnlineSummary inputs tree]
    exact hcontinues
  have hcandidates := tree.onlineBuildSummary_candidates_eq_leaves
    inputs.leafContinues inputs.endpointTurns hsummary
  rw [← executeSubtree_toOnlineSummary inputs tree] at hcandidates
  exact hcandidates

/-- A bounded checked-row program reuses the generated deterministic
recursive-doubling semantics.  This is the finite structural interpretation
that already carries a stationary checked-or-identity kernel theorem. -/
def Program.checkedCandidateProgram (program : Program) (count : ℕ)
    (turns : Fin count → Fin count → Bool) :
    Mcmc.Executable.DynamicTreeIR.CheckedRecursiveDoublingProgram
      (Fin count) program.maxDepth :=
  Mcmc.Executable.DynamicTreeIR.recursiveDoublingProgram
    count program.maxDepth turns

/-- Pointwise equality of computed and ideal endpoint decisions lifts through
the complete checked program interpretation. -/
theorem Program.checkedCandidateProgram_interpret_eq
    (program : Program) (count : ℕ)
    (computedTurns idealTurns : Fin count → Fin count → Bool)
    (hagrees : ∀ left right, computedTurns left right = idealTurns left right)
    (target : Distribution (Fin count))
    (htarget : ∀ state, 0 < target.mass state) :
    (program.checkedCandidateProgram count computedTurns).interpret
        target htarget =
      (program.checkedCandidateProgram count idealTurns).interpret
        target htarget :=
  Mcmc.Executable.DynamicTreeIR.recursiveDoublingProgram_interpret_eq
    count program.maxDepth computedTurns idealTurns hagrees target htarget

/-- Every typed checked NUTS candidate program has a stationary finite
structural interpretation.  Continuous phase-space invariance additionally
requires the Hamiltonian orbit-lifting theorem and is not asserted here. -/
theorem Program.checkedCandidateProgram_stationary
    (program : Program) (count : ℕ)
    (turns : Fin count → Fin count → Bool)
    (target : Distribution (Fin count))
    (htarget : ∀ state, 0 < target.mass state) :
    ((program.checkedCandidateProgram count turns).interpret target htarget).Stationary
      target :=
  (program.checkedCandidateProgram count turns).stationary target htarget

end Mcmc.Executable.Continuous.NUTSIR
