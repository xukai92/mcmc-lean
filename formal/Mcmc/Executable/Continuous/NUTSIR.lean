import Mcmc.Executable.Continuous.DynamicTreeRefinement
import Mcmc.Hamiltonian.DynamicInvariance
import Mcmc.Hamiltonian.HMC
import Mcmc.Finite.MeasureKernel

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
open MeasureTheory
open scoped ProbabilityTheory

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

/-- Typed phase value carried by the NUTS execution program.  Position and
momentum representations are parameters so exact reals and backend numeric
vectors can share the same control-flow syntax. -/
structure PhaseValue (Position Momentum : Type*) where
  position : Position
  momentum : Momentum
  logWeight : ℝ
  energy : ℝ

/-- One-step directional dynamics supplied to the tree interpreter.  For the
ideal semantics this is exact leapfrog; the Julia backend supplies its checked
numeric primitive and retains the existing refinement obligation. -/
structure Dynamics (Phase : Type*) where
  advance : Bool → Phase → Phase

/-- Construct the complete directional phase tree denoted by one recursive
`BuildTree` call.  `growRight = false` reverses node order so leaves always
remain in left-to-right trajectory order. -/
def buildPhaseTree (dynamics : Dynamics Phase) (growRight : Bool) :
    ℕ → Phase → RecursivePhaseTree Phase
  | 0, start => .leaf (dynamics.advance growRight start)
  | depth + 1, start =>
      let first := buildPhaseTree dynamics growRight depth start
      let secondStart := if growRight then first.rightmost else first.leftmost
      let second := buildPhaseTree dynamics growRight depth secondStart
      if growRight then .node first second else .node second first

@[simp] theorem buildPhaseTree_zero (dynamics : Dynamics Phase)
    (growRight : Bool) (start : Phase) :
    buildPhaseTree dynamics growRight 0 start =
      .leaf (dynamics.advance growRight start) := rfl

/-- Every depth-`d` directional call denotes exactly `2^d` integrated phase
leaves. -/
theorem buildPhaseTree_leafCount (dynamics : Dynamics Phase)
    (growRight : Bool) (depth : ℕ) (start : Phase) :
    (buildPhaseTree dynamics growRight depth start).leafCount = 2 ^ depth := by
  induction depth generalizing start with
  | zero => rfl
  | succ depth ih =>
      rw [buildPhaseTree]
      split <;> simp [RecursivePhaseTree.leafCount, ih, pow_succ] <;> omega

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

/-- Execute one directional recursive call from its typed dynamics.  Tree
construction and structural execution are now both Lean-owned definitions. -/
def executeDirectionalSubtree (dynamics : Dynamics Phase)
    (inputs : SubtreeInputs Phase) (growRight : Bool)
    (depth : ℕ) (start : Phase) : SubtreeResult Phase :=
  executeSubtree inputs (buildPhaseTree dynamics growRight depth start)

/-- A successful directional execution returns exactly `2^depth` ordered
candidate occurrences. -/
theorem executeDirectionalSubtree_candidates_length
    (dynamics : Dynamics Phase) (inputs : SubtreeInputs Phase)
    (growRight : Bool) (depth : ℕ) (start : Phase)
    (hcontinues :
      (executeDirectionalSubtree dynamics inputs growRight depth start).continues =
        true) :
    (executeDirectionalSubtree dynamics inputs growRight depth start).candidates.length =
      2 ^ depth := by
  rw [executeDirectionalSubtree,
    executeSubtree_candidates_eq_leaves inputs _ hcontinues,
    RecursivePhaseTree.length_leaves,
    buildPhaseTree_leafCount]

/-- State of the bounded outer doubling loop.  Only a subtree which passes its
internal checks and the completed outer endpoint check is admitted. -/
structure OuterResult (Phase : Type*) where
  left : Phase
  right : Phase
  candidates : List Phase
  completedDepth : ℕ
  continues : Bool
deriving Repr

/-- One outer doubling iteration at the supplied depth.  A failed subtree or
outer U-turn stops before admitting that subtree, matching the checked-row
semantics rather than silently assuming production NUTS reroot invariance. -/
def executeOuterStep (dynamics : Dynamics Phase)
    (inputs : SubtreeInputs Phase) (depth : ℕ)
    (state : OuterResult Phase) (growRight : Bool) : OuterResult Phase :=
  if !state.continues then state
  else
    let start := if growRight then state.right else state.left
    let subtree := executeDirectionalSubtree dynamics inputs growRight depth start
    if !subtree.continues then { state with continues := false }
    else
      let newLeft := if growRight then state.left
        else (buildPhaseTree dynamics growRight depth start).leftmost
      let newRight := if growRight then
          (buildPhaseTree dynamics growRight depth start).rightmost
        else state.right
      if inputs.endpointTurns newLeft newRight then
        { state with continues := false }
      else
        { left := newLeft
          right := newRight
          candidates := if growRight then
            state.candidates ++ subtree.candidates
          else subtree.candidates ++ state.candidates
          completedDepth := state.completedDepth + 1
          continues := true }

/-- Consume the state-independent outer direction trace.  The depth index is
explicit and later bits are ignored after the first failed checked expansion. -/
def executeOuterTraceAux (dynamics : Dynamics Phase)
    (inputs : SubtreeInputs Phase) :
    ℕ → OuterResult Phase → List Bool → OuterResult Phase
  | _, state, [] => state
  | depth, state, direction :: rest =>
      let next := executeOuterStep dynamics inputs depth state direction
      if !next.continues then next
      else executeOuterTraceAux dynamics inputs (depth + 1) next rest

/-- Complete deterministic replay skeleton for one bounded checked NUTS tree
transition, beginning with the refreshed initial phase as a candidate. -/
def Program.executeOuterTrace (program : Program)
    (dynamics : Dynamics Phase) (inputs : SubtreeInputs Phase)
    (trace : DirectionTrace program) (initial : Phase) : OuterResult Phase :=
  executeOuterTraceAux dynamics inputs 0
    { left := initial, right := initial, candidates := [initial]
      completedDepth := 0, continues := true }
    (List.ofFn trace.growRight)

/-- One outer step either preserves the completed depth or increments it once. -/
theorem executeOuterStep_completedDepth_le
    (dynamics : Dynamics Phase) (inputs : SubtreeInputs Phase)
    (depth : ℕ) (state : OuterResult Phase) (direction : Bool) :
    (executeOuterStep dynamics inputs depth state direction).completedDepth ≤
      state.completedDepth + 1 := by
  cases direction <;> simp only [executeOuterStep] <;>
    split <;> simp_all <;> split <;> simp_all <;> split <;> simp_all

/-- A bounded program cannot complete more outer expansions than its supplied
direction-trace length. -/
theorem executeOuterTraceAux_completedDepth_le
    (dynamics : Dynamics Phase) (inputs : SubtreeInputs Phase)
    (depth : ℕ) (state : OuterResult Phase) (directions : List Bool) :
    (executeOuterTraceAux dynamics inputs depth state directions).completedDepth ≤
      state.completedDepth + directions.length := by
  induction directions generalizing depth state with
  | nil => simp [executeOuterTraceAux]
  | cons direction rest ih =>
      rw [executeOuterTraceAux]
      simp only [List.length_cons]
      let next := executeOuterStep dynamics inputs depth state direction
      have hstep : next.completedDepth ≤ state.completedDepth + 1 :=
        executeOuterStep_completedDepth_le dynamics inputs depth state direction
      change (if !next.continues then next
        else executeOuterTraceAux dynamics inputs (depth + 1) next rest).completedDepth ≤
          state.completedDepth + (rest.length + 1)
      split
      · omega
      · have htail := ih (depth + 1) next
        omega

theorem Program.executeOuterTrace_completedDepth_le (program : Program)
    (dynamics : Dynamics Phase) (inputs : SubtreeInputs Phase)
    (trace : DirectionTrace program) (initial : Phase) :
    (program.executeOuterTrace dynamics inputs trace initial).completedDepth ≤
      program.maxDepth := by
  rw [Program.executeOuterTrace]
  simpa using executeOuterTraceAux_completedDepth_le dynamics inputs 0
    ({ left := initial, right := initial, candidates := [initial]
       completedDepth := 0, continues := true } : OuterResult Phase)
    (List.ofFn trace.growRight)

/-- Exact-real candidate weights supplied to the selection interpreter.  The
nonnegativity witness is part of the typed boundary rather than an unchecked
runtime convention. -/
structure SelectionInputs (Phase : Type*) where
  weight : Phase → ℝ
  nonnegative : ∀ phase, 0 ≤ weight phase

/-- One state-independent unit selection mark.  Backends validate the same
half-open interval before interpreting it. -/
structure SelectionMark where
  unit : ℝ
  nonnegative : 0 ≤ unit
  lt_one : unit < 1

def candidateTotalWeight (inputs : SelectionInputs Phase) : List Phase → ℝ
  | [] => 0
  | phase :: rest => inputs.weight phase + candidateTotalWeight inputs rest

/-- Inverse-CDF consumption of an ordered candidate-occurrence list.  The
fallback is used only for zero total weight or an exhausted interval caused by
an invalid premise; the public transition passes its initial phase. -/
noncomputable def selectWeightedAux (inputs : SelectionInputs Phase) :
    ℝ → Phase → List Phase → Phase
  | _, fallback, [] => fallback
  | threshold, fallback, phase :: rest =>
      if threshold < inputs.weight phase then phase
      else selectWeightedAux inputs (threshold - inputs.weight phase) fallback rest

noncomputable def selectWeighted (inputs : SelectionInputs Phase) (mark : SelectionMark)
    (fallback : Phase) (candidates : List Phase) : Phase :=
  let total := candidateTotalWeight inputs candidates
  if total ≤ 0 then fallback
  else selectWeightedAux inputs (mark.unit * total) fallback candidates

/-- Full deterministic trace carried by the first checked NUTS Reference
program: bounded direction bits followed by one weighted-selection mark. -/
structure TransitionTrace (program : Program) extends DirectionTrace program where
  selection : SelectionMark

structure TransitionResult (Phase : Type*) where
  tree : OuterResult Phase
  selected : Phase
deriving Repr

/-- Complete deterministic interpreter skeleton.  Momentum refresh and the
numeric one-step dynamics remain typed primitives outside this trace, exactly
as for the existing HMC compiler IR. -/
noncomputable def Program.executeTransition (program : Program)
    (dynamics : Dynamics Phase) (subtree : SubtreeInputs Phase)
    (selection : SelectionInputs Phase) (trace : TransitionTrace program)
    (initial : Phase) : TransitionResult Phase :=
  let tree := program.executeOuterTrace dynamics subtree trace.toDirectionTrace initial
  { tree := tree
    selected := selectWeighted selection trace.selection initial tree.candidates }

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

/-! ### Continuous orbit-row interpretation -/

/-- Endpoint decision matrix obtained from the physical leapfrog orbit anchored
at the current index. This is the exact-real callback shape mirrored by the
Julia row interpreter. -/
noncomputable def offsetEndpointTurns
    {ι : Type*} [Fintype ι]
    (gradient : Mcmc.Hamiltonian.Position ι → Mcmc.Hamiltonian.Position ι)
    (ε : ℝ) {L : ℕ}
    (turns : Mcmc.Hamiltonian.PhaseSpace ι →
      Mcmc.Hamiltonian.PhaseSpace ι → Bool)
    (z : Mcmc.Hamiltonian.PhaseSpace ι) (anchor left right : Fin (L + 1)) : Bool :=
  turns (Mcmc.Hamiltonian.offsetLeapfrogTrajectory gradient ε anchor z left)
    (Mcmc.Hamiltonian.offsetLeapfrogTrajectory gradient ε anchor z right)

/-- Reanchoring the same physical orbit leaves every indexed endpoint decision
unchanged. -/
theorem offsetEndpointTurns_orbitStable
    {ι : Type*} [Fintype ι]
    (gradient : Mcmc.Hamiltonian.Position ι → Mcmc.Hamiltonian.Position ι)
    (ε : ℝ) {L : ℕ}
    (turns : Mcmc.Hamiltonian.PhaseSpace ι →
      Mcmc.Hamiltonian.PhaseSpace ι → Bool) :
    ∀ (z : Mcmc.Hamiltonian.PhaseSpace ι)
      (origin selected left right : Fin (L + 1)),
      offsetEndpointTurns gradient ε turns
          (Mcmc.Hamiltonian.offsetLeapfrogTrajectory gradient ε origin z selected)
          selected left right =
        offsetEndpointTurns gradient ε turns z origin left right := by
  intro z origin selected left right
  unfold offsetEndpointTurns
  rw [Mcmc.Hamiltonian.offsetLeapfrogTrajectory_reroot]
  rw [Mcmc.Hamiltonian.offsetLeapfrogTrajectory_reroot]

theorem measurable_offsetEndpointTurns
    {ι : Type*} [Fintype ι]
    {gradient : Mcmc.Hamiltonian.Position ι → Mcmc.Hamiltonian.Position ι}
    (hgradient : Measurable gradient) (ε : ℝ) {L : ℕ}
    (turns : Mcmc.Hamiltonian.PhaseSpace ι →
      Mcmc.Hamiltonian.PhaseSpace ι → Bool)
    (hturns : Measurable fun pair :
      Mcmc.Hamiltonian.PhaseSpace ι × Mcmc.Hamiltonian.PhaseSpace ι =>
        turns pair.1 pair.2)
    (anchor left right : Fin (L + 1)) :
    Measurable fun z => offsetEndpointTurns gradient ε turns z anchor left right := by
  exact hturns.comp <| Measurable.prodMk
    (Mcmc.Hamiltonian.measurable_offsetLeapfrogTrajectory
      hgradient ε anchor left)
    (Mcmc.Hamiltonian.measurable_offsetLeapfrogTrajectory
      hgradient ε anchor right)

theorem measurable_vectorAdjacentUTurn
    {ι : Type*} [Fintype ι] :
    Measurable fun pair : Mcmc.Hamiltonian.PhaseSpace ι ×
        Mcmc.Hamiltonian.PhaseSpace ι =>
      Mcmc.Finite.MarkovKernel.vectorAdjacentUTurn pair.1 pair.2 := by
  apply measurable_to_bool
  rw [show (fun pair : Mcmc.Hamiltonian.PhaseSpace ι ×
      Mcmc.Hamiltonian.PhaseSpace ι =>
        Mcmc.Finite.MarkovKernel.vectorAdjacentUTurn pair.1 pair.2) ⁻¹' {true} =
      {pair | (∑ i, (pair.2.1 i - pair.1.1 i) * pair.1.2 i) < 0} ∪
      {pair | (∑ i, (pair.2.1 i - pair.1.1 i) * pair.2.2 i) < 0} by
    ext pair
    simp [Mcmc.Finite.MarkovKernel.vectorAdjacentUTurn]]
  apply MeasurableSet.union
  · apply measurableSet_lt
    · fun_prop
    · exact measurable_const
  · apply measurableSet_lt
    · fun_prop
    · exact measurable_const

/-- Interpret the same recursive-doubling row builder on every exact
Hamiltonian orbit base point. A fixed direction trace is an auxiliary
state-independent draw; endpoint decisions are allowed to depend on the
physical orbit but must address it in stable indexed coordinates. -/
def Program.rawOrbitCandidateRows
    {ι : Type*} [Fintype ι]
    (program : Program) (gradient : Mcmc.Hamiltonian.Position ι →
      Mcmc.Hamiltonian.Position ι) (ε : ℝ) (L : ℕ)
    (depth : ℕ) (_hdepth : depth ≤ program.maxDepth)
    (trace : Fin depth → Bool)
    (turns : Mcmc.Hamiltonian.PhaseSpace ι → Fin (L + 1) →
      Fin (L + 1) → Fin (L + 1) → Bool)
    (horbit : ∀ (z : Mcmc.Hamiltonian.PhaseSpace ι)
      (origin selected left right : Fin (L + 1)),
      turns (Mcmc.Hamiltonian.offsetLeapfrogTrajectory gradient ε origin z selected)
          selected left right = turns z origin left right) :
    Mcmc.Hamiltonian.RawTrajectoryCandidateRows gradient ε L where
  rows z anchor root :=
    Mcmc.Executable.DynamicTreeIR.recursiveDoublingCandidateRow
      (L + 1) depth (turns z anchor) trace root
  orbitCovariant := by
    intro z origin selected
    funext root
    exact Mcmc.Executable.DynamicTreeIR.recursiveDoublingCandidateRow_congr
      (L + 1) depth
      (turns (Mcmc.Hamiltonian.offsetLeapfrogTrajectory gradient ε origin z selected)
        selected)
      (turns z origin) (horbit z origin selected) trace root

/-- Coordinatewise measurability of the endpoint bits is sufficient for the
entire finite recursive builder, global checker, identity fallback, and final
candidate mask to be measurable. -/
theorem Program.rawOrbitCandidateRows_mask_measurable
    {ι : Type*} [Fintype ι]
    (program : Program) (gradient : Mcmc.Hamiltonian.Position ι →
      Mcmc.Hamiltonian.Position ι) (ε : ℝ) (L depth : ℕ)
    (hdepth : depth ≤ program.maxDepth) (trace : Fin depth → Bool)
    (turns : Mcmc.Hamiltonian.PhaseSpace ι → Fin (L + 1) →
      Fin (L + 1) → Fin (L + 1) → Bool)
    (horbit : ∀ (z : Mcmc.Hamiltonian.PhaseSpace ι)
      (origin selected left right : Fin (L + 1)),
      turns (Mcmc.Hamiltonian.offsetLeapfrogTrajectory gradient ε origin z selected)
          selected left right = turns z origin left right)
    (hmeasurable : ∀ anchor left right,
      Measurable fun z => turns z anchor left right) :
    Mcmc.Hamiltonian.MeasurableTrajectoryCandidateMask
      ((program.rawOrbitCandidateRows gradient ε L depth hdepth trace turns
        horbit).toCertified.mask) := by
  intro origin selected
  let decode := fun matrix : Fin (L + 1) → Fin (L + 1) → Bool =>
    decide (selected ∈
      (if Mcmc.Finite.MarkovKernel.CertifiedDynamicTree.check
          (fun root => Mcmc.Executable.DynamicTreeIR.recursiveDoublingCandidateRow
            (L + 1) depth matrix trace root)
        then Mcmc.Executable.DynamicTreeIR.recursiveDoublingCandidateRow
          (L + 1) depth matrix trace origin
        else {origin}))
  have hmatrix : Measurable fun z => turns z origin := by
    apply measurable_pi_lambda
    intro left
    apply measurable_pi_lambda
    intro right
    exact hmeasurable origin left right
  have heq : (fun z =>
      (program.rawOrbitCandidateRows gradient ε L depth hdepth trace turns
        horbit).toCertified.mask z origin selected) =
      fun z => decode (turns z origin) := by
    rfl
  rw [heq]
  exact (measurable_of_countable decode).comp hmatrix

/-- Continuous checked-or-identity kernel denoted by one fixed direction
trace of the executable recursive program. -/
noncomputable def Program.checkedOrbitKernel
    {ι : Type*} [Fintype ι]
    (program : Program)
    (potential : Mcmc.Hamiltonian.Position ι → ℝ)
    (gradient : Mcmc.Hamiltonian.Position ι → Mcmc.Hamiltonian.Position ι)
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) (L depth : ℕ) (hdepth : depth ≤ program.maxDepth)
    (trace : Fin depth → Bool)
    (turns : Mcmc.Hamiltonian.PhaseSpace ι → Fin (L + 1) →
      Fin (L + 1) → Fin (L + 1) → Bool)
    (horbit : ∀ (z : Mcmc.Hamiltonian.PhaseSpace ι)
      (origin selected left right : Fin (L + 1)),
      turns (Mcmc.Hamiltonian.offsetLeapfrogTrajectory gradient ε origin z selected)
          selected left right = turns z origin left right)
    (hmask : Mcmc.Hamiltonian.MeasurableTrajectoryCandidateMask
      ((program.rawOrbitCandidateRows gradient ε L depth hdepth trace turns
        horbit).toCertified.mask)) :
    ProbabilityTheory.Kernel (Mcmc.Hamiltonian.PhaseSpace ι)
      (Mcmc.Hamiltonian.PhaseSpace ι) :=
  Mcmc.Hamiltonian.randomizedDynamicMultinomialKernel potential gradient ε
    (program.rawOrbitCandidateRows gradient ε L depth hdepth trace turns
      horbit).toCertified.mask
    (program.rawOrbitCandidateRows gradient ε L depth hdepth trace turns
      horbit).toCertified.mask_root
    hpotential hgradient hmask

/-- The exact recursive NUTS row interpreter, global checker, identity
fallback, and multinomial selection preserve the phase-space Boltzmann target.
The remaining backend obligation is measurability/refinement of the concrete
endpoint callback used to instantiate `turns`. -/
theorem Program.checkedOrbitKernel_invariant
    {ι : Type*} [Fintype ι]
    (program : Program)
    {potential : Mcmc.Hamiltonian.Position ι → ℝ}
    {gradient : Mcmc.Hamiltonian.Position ι → Mcmc.Hamiltonian.Position ι}
    (hpotential : Measurable potential)
    (hgradient : Measurable gradient)
    (ε : ℝ) (L depth : ℕ) (hdepth : depth ≤ program.maxDepth)
    (trace : Fin depth → Bool)
    (turns : Mcmc.Hamiltonian.PhaseSpace ι → Fin (L + 1) →
      Fin (L + 1) → Fin (L + 1) → Bool)
    (horbit : ∀ (z : Mcmc.Hamiltonian.PhaseSpace ι)
      (origin selected left right : Fin (L + 1)),
      turns (Mcmc.Hamiltonian.offsetLeapfrogTrajectory gradient ε origin z selected)
          selected left right = turns z origin left right)
    (hmask : Mcmc.Hamiltonian.MeasurableTrajectoryCandidateMask
      ((program.rawOrbitCandidateRows gradient ε L depth hdepth trace turns
        horbit).toCertified.mask)) :
    (program.checkedOrbitKernel potential gradient hpotential hgradient ε L depth
      hdepth trace turns horbit hmask).Invariant
        (Mcmc.Hamiltonian.phaseBoltzmannTarget potential) :=
  (program.rawOrbitCandidateRows gradient ε L depth hdepth trace turns horbit).toCertified
    |>.randomizedKernel_invariant hpotential hgradient ε hmask

/-- Full continuous Reference kernel: draw the complete fair direction trace
independently of the current phase point, then execute its checked component. -/
noncomputable def Program.randomizedCheckedOrbitKernel
    {ι : Type*} [Fintype ι]
    (program : Program)
    (potential : Mcmc.Hamiltonian.Position ι → ℝ)
    (gradient : Mcmc.Hamiltonian.Position ι → Mcmc.Hamiltonian.Position ι)
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) (L depth : ℕ) (hdepth : depth ≤ program.maxDepth)
    (turns : Mcmc.Hamiltonian.PhaseSpace ι → Fin (L + 1) →
      Fin (L + 1) → Fin (L + 1) → Bool)
    (horbit : ∀ (z : Mcmc.Hamiltonian.PhaseSpace ι)
      (origin selected left right : Fin (L + 1)),
      turns (Mcmc.Hamiltonian.offsetLeapfrogTrajectory gradient ε origin z selected)
          selected left right = turns z origin left right)
    (hmask : ∀ trace, Mcmc.Hamiltonian.MeasurableTrajectoryCandidateMask
      ((program.rawOrbitCandidateRows gradient ε L depth hdepth trace turns
        horbit).toCertified.mask)) :
    ProbabilityTheory.Kernel (Mcmc.Hamiltonian.PhaseSpace ι)
      (Mcmc.Hamiltonian.PhaseSpace ι) :=
  Mcmc.Hamiltonian.finiteKernelMixture
    (uniformDirectionTraceLaw depth).toPMF
    (fun trace => program.checkedOrbitKernel potential gradient hpotential hgradient
      ε L depth hdepth trace turns horbit (hmask trace))

instance Program.randomizedCheckedOrbitKernel_isMarkovKernel
    {ι : Type*} [Fintype ι]
    (program : Program)
    (potential : Mcmc.Hamiltonian.Position ι → ℝ)
    (gradient : Mcmc.Hamiltonian.Position ι → Mcmc.Hamiltonian.Position ι)
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) (L depth : ℕ) (hdepth : depth ≤ program.maxDepth)
    (turns : Mcmc.Hamiltonian.PhaseSpace ι → Fin (L + 1) →
      Fin (L + 1) → Fin (L + 1) → Bool)
    (horbit : ∀ (z : Mcmc.Hamiltonian.PhaseSpace ι)
      (origin selected left right : Fin (L + 1)),
      turns (Mcmc.Hamiltonian.offsetLeapfrogTrajectory gradient ε origin z selected)
          selected left right = turns z origin left right)
    (hmask : ∀ trace, Mcmc.Hamiltonian.MeasurableTrajectoryCandidateMask
      ((program.rawOrbitCandidateRows gradient ε L depth hdepth trace turns
        horbit).toCertified.mask)) :
    ProbabilityTheory.IsMarkovKernel
      (program.randomizedCheckedOrbitKernel potential gradient hpotential hgradient
        ε L depth hdepth turns horbit hmask) := by
  constructor
  intro state
  constructor
  change (∑ trace,
    (uniformDirectionTraceLaw depth).toPMF trace •
      program.checkedOrbitKernel potential gradient hpotential hgradient ε L depth
        hdepth trace turns horbit (hmask trace) state) Set.univ = 1
  rw [MeasureTheory.Measure.finsetSum_apply]
  simp only [MeasureTheory.Measure.smul_apply, smul_eq_mul]
  trans ∑ trace, (uniformDirectionTraceLaw depth).toPMF trace
  · apply Finset.sum_congr rfl
    intro trace htrace
    have hcomponent : ProbabilityTheory.IsMarkovKernel
        (program.checkedOrbitKernel potential gradient hpotential hgradient ε L depth
          hdepth trace turns horbit (hmask trace)) := by
      unfold Program.checkedOrbitKernel
      infer_instance
    letI := hcomponent
    rw [measure_univ, mul_one]
  · exact (tsum_fintype _).symm.trans
      (PMF.tsum_coe (uniformDirectionTraceLaw depth).toPMF)

/-- The fair state-independent direction-trace mixture preserves the
phase-space Boltzmann target. -/
theorem Program.randomizedCheckedOrbitKernel_invariant
    {ι : Type*} [Fintype ι]
    (program : Program)
    {potential : Mcmc.Hamiltonian.Position ι → ℝ}
    {gradient : Mcmc.Hamiltonian.Position ι → Mcmc.Hamiltonian.Position ι}
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) (L depth : ℕ) (hdepth : depth ≤ program.maxDepth)
    (turns : Mcmc.Hamiltonian.PhaseSpace ι → Fin (L + 1) →
      Fin (L + 1) → Fin (L + 1) → Bool)
    (horbit : ∀ (z : Mcmc.Hamiltonian.PhaseSpace ι)
      (origin selected left right : Fin (L + 1)),
      turns (Mcmc.Hamiltonian.offsetLeapfrogTrajectory gradient ε origin z selected)
          selected left right = turns z origin left right)
    (hmask : ∀ trace, Mcmc.Hamiltonian.MeasurableTrajectoryCandidateMask
      ((program.rawOrbitCandidateRows gradient ε L depth hdepth trace turns
        horbit).toCertified.mask)) :
    (program.randomizedCheckedOrbitKernel potential gradient hpotential hgradient
      ε L depth hdepth turns horbit hmask).Invariant
        (Mcmc.Hamiltonian.phaseBoltzmannTarget potential) := by
  apply Mcmc.Hamiltonian.finiteKernelMixture_invariant
  intro trace
  exact program.checkedOrbitKernel_invariant hpotential hgradient ε L depth hdepth
    trace turns horbit (hmask trace)

/-- User-facing checked NUTS Reference kernel: refresh momentum, execute the
fair checked orbit transition, and project back to position space. -/
noncomputable def Program.positionRandomizedCheckedOrbitKernel
    {ι : Type*} [Fintype ι]
    (program : Program)
    (potential : Mcmc.Hamiltonian.Position ι → ℝ)
    (gradient : Mcmc.Hamiltonian.Position ι → Mcmc.Hamiltonian.Position ι)
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) (L depth : ℕ) (hdepth : depth ≤ program.maxDepth)
    (turns : Mcmc.Hamiltonian.PhaseSpace ι → Fin (L + 1) →
      Fin (L + 1) → Fin (L + 1) → Bool)
    (horbit : ∀ (z : Mcmc.Hamiltonian.PhaseSpace ι)
      (origin selected left right : Fin (L + 1)),
      turns (Mcmc.Hamiltonian.offsetLeapfrogTrajectory gradient ε origin z selected)
          selected left right = turns z origin left right)
    (hmask : ∀ trace, Mcmc.Hamiltonian.MeasurableTrajectoryCandidateMask
      ((program.rawOrbitCandidateRows gradient ε L depth hdepth trace turns
        horbit).toCertified.mask))
    (momentumTarget : MeasureTheory.Measure (Mcmc.Hamiltonian.Momentum ι)) :
    ProbabilityTheory.Kernel (Mcmc.Hamiltonian.Position ι)
      (Mcmc.Hamiltonian.Position ι) :=
  (program.randomizedCheckedOrbitKernel potential gradient hpotential hgradient
      ε L depth hdepth turns horbit hmask ∘ₖ
    Mcmc.Hamiltonian.positionMomentumLift momentumTarget).map
      (Prod.fst : Mcmc.Hamiltonian.PhaseSpace ι → Mcmc.Hamiltonian.Position ι)

instance Program.positionRandomizedCheckedOrbitKernel_isMarkovKernel
    {ι : Type*} [Fintype ι]
    (program : Program)
    (potential : Mcmc.Hamiltonian.Position ι → ℝ)
    (gradient : Mcmc.Hamiltonian.Position ι → Mcmc.Hamiltonian.Position ι)
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) (L depth : ℕ) (hdepth : depth ≤ program.maxDepth)
    (turns : Mcmc.Hamiltonian.PhaseSpace ι → Fin (L + 1) →
      Fin (L + 1) → Fin (L + 1) → Bool)
    (horbit : ∀ (z : Mcmc.Hamiltonian.PhaseSpace ι)
      (origin selected left right : Fin (L + 1)),
      turns (Mcmc.Hamiltonian.offsetLeapfrogTrajectory gradient ε origin z selected)
          selected left right = turns z origin left right)
    (hmask : ∀ trace, Mcmc.Hamiltonian.MeasurableTrajectoryCandidateMask
      ((program.rawOrbitCandidateRows gradient ε L depth hdepth trace turns
        horbit).toCertified.mask))
    (momentumTarget : MeasureTheory.Measure (Mcmc.Hamiltonian.Momentum ι))
    [MeasureTheory.IsProbabilityMeasure momentumTarget] :
    ProbabilityTheory.IsMarkovKernel
      (program.positionRandomizedCheckedOrbitKernel potential gradient hpotential
        hgradient ε L depth hdepth turns horbit hmask momentumTarget) := by
  unfold Program.positionRandomizedCheckedOrbitKernel
  exact ProbabilityTheory.Kernel.IsMarkovKernel.map _ measurable_fst

/-- A compatible position target is invariant under the complete public
checked NUTS Reference transition, including refresh and projection. -/
theorem Program.positionRandomizedCheckedOrbitKernel_invariant
    {ι : Type*} [Fintype ι]
    (program : Program)
    {potential : Mcmc.Hamiltonian.Position ι → ℝ}
    {gradient : Mcmc.Hamiltonian.Position ι → Mcmc.Hamiltonian.Position ι}
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) (L depth : ℕ) (hdepth : depth ≤ program.maxDepth)
    (turns : Mcmc.Hamiltonian.PhaseSpace ι → Fin (L + 1) →
      Fin (L + 1) → Fin (L + 1) → Bool)
    (horbit : ∀ (z : Mcmc.Hamiltonian.PhaseSpace ι)
      (origin selected left right : Fin (L + 1)),
      turns (Mcmc.Hamiltonian.offsetLeapfrogTrajectory gradient ε origin z selected)
          selected left right = turns z origin left right)
    (hmask : ∀ trace, Mcmc.Hamiltonian.MeasurableTrajectoryCandidateMask
      ((program.rawOrbitCandidateRows gradient ε L depth hdepth trace turns
        horbit).toCertified.mask))
    (positionTarget : MeasureTheory.Measure (Mcmc.Hamiltonian.Position ι))
    [MeasureTheory.SFinite positionTarget]
    (momentumTarget : MeasureTheory.Measure (Mcmc.Hamiltonian.Momentum ι))
    [MeasureTheory.IsProbabilityMeasure momentumTarget]
    (hfactor : positionTarget.prod momentumTarget =
      Mcmc.Hamiltonian.phaseBoltzmannTarget potential) :
    (program.positionRandomizedCheckedOrbitKernel potential gradient hpotential
      hgradient ε L depth hdepth turns horbit hmask momentumTarget).Invariant
        positionTarget := by
  change (Mcmc.Kernel.liftEvolveProject
    (Mcmc.Hamiltonian.positionMomentumLift momentumTarget)
    (program.randomizedCheckedOrbitKernel potential gradient hpotential hgradient
      ε L depth hdepth turns horbit hmask)
    (Prod.fst : Mcmc.Hamiltonian.PhaseSpace ι → Mcmc.Hamiltonian.Position ι)
      measurable_fst).Invariant positionTarget
  have htrajectory := program.randomizedCheckedOrbitKernel_invariant
    hpotential hgradient ε L depth hdepth turns horbit hmask
  rw [← hfactor] at htrajectory
  unfold Mcmc.Hamiltonian.positionMomentumLift
  apply Mcmc.Kernel.compProdEvolveFst_invariant
  rw [MeasureTheory.Measure.compProd_const]
  exact htrajectory

/-- Fully instantiated exact-real Reference kernel using the Euclidean
endpoint U-turn predicate decoded by the current artifact. -/
noncomputable def Program.positionVectorUTurnReferenceKernel
    {ι : Type*} [Fintype ι]
    (program : Program)
    (potential : Mcmc.Hamiltonian.Position ι → ℝ)
    (gradient : Mcmc.Hamiltonian.Position ι → Mcmc.Hamiltonian.Position ι)
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) (L depth : ℕ) (hdepth : depth ≤ program.maxDepth)
    (momentumTarget : Measure (Mcmc.Hamiltonian.Momentum ι)) :
    ProbabilityTheory.Kernel (Mcmc.Hamiltonian.Position ι)
      (Mcmc.Hamiltonian.Position ι) :=
  program.positionRandomizedCheckedOrbitKernel potential gradient hpotential hgradient
    ε L depth hdepth
    (offsetEndpointTurns gradient ε
      Mcmc.Finite.MarkovKernel.vectorAdjacentUTurn)
    (offsetEndpointTurns_orbitStable gradient ε
      Mcmc.Finite.MarkovKernel.vectorAdjacentUTurn)
    (fun trace => program.rawOrbitCandidateRows_mask_measurable gradient ε L depth
      hdepth trace
      (offsetEndpointTurns gradient ε
        Mcmc.Finite.MarkovKernel.vectorAdjacentUTurn)
      (offsetEndpointTurns_orbitStable gradient ε
        Mcmc.Finite.MarkovKernel.vectorAdjacentUTurn)
      (fun anchor left right => measurable_offsetEndpointTurns hgradient ε
        Mcmc.Finite.MarkovKernel.vectorAdjacentUTurn measurable_vectorAdjacentUTurn
        anchor left right))
    momentumTarget

/-- Main exact-real correctness theorem for the maintained checked NUTS
Reference: fair bounded direction traces, recursive rows, global certification,
identity fallback, multinomial selection, Gaussian-compatible refresh, and
position projection preserve the declared position target. -/
theorem Program.positionVectorUTurnReferenceKernel_invariant
    {ι : Type*} [Fintype ι]
    (program : Program)
    {potential : Mcmc.Hamiltonian.Position ι → ℝ}
    {gradient : Mcmc.Hamiltonian.Position ι → Mcmc.Hamiltonian.Position ι}
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) (L depth : ℕ) (hdepth : depth ≤ program.maxDepth)
    (positionTarget : Measure (Mcmc.Hamiltonian.Position ι))
    [SFinite positionTarget]
    (momentumTarget : Measure (Mcmc.Hamiltonian.Momentum ι))
    [IsProbabilityMeasure momentumTarget]
    (hfactor : positionTarget.prod momentumTarget =
      Mcmc.Hamiltonian.phaseBoltzmannTarget potential) :
    (program.positionVectorUTurnReferenceKernel potential gradient hpotential
      hgradient ε L depth hdepth momentumTarget).Invariant positionTarget := by
  apply program.positionRandomizedCheckedOrbitKernel_invariant hpotential hgradient
    ε L depth hdepth
    (offsetEndpointTurns gradient ε
      Mcmc.Finite.MarkovKernel.vectorAdjacentUTurn)
    (offsetEndpointTurns_orbitStable gradient ε
      Mcmc.Finite.MarkovKernel.vectorAdjacentUTurn)
    (fun trace => program.rawOrbitCandidateRows_mask_measurable gradient ε L depth
      hdepth trace
      (offsetEndpointTurns gradient ε
        Mcmc.Finite.MarkovKernel.vectorAdjacentUTurn)
      (offsetEndpointTurns_orbitStable gradient ε
        Mcmc.Finite.MarkovKernel.vectorAdjacentUTurn)
      (fun anchor left right => measurable_offsetEndpointTurns hgradient ε
        Mcmc.Finite.MarkovKernel.vectorAdjacentUTurn measurable_vectorAdjacentUTurn
        anchor left right))
    positionTarget momentumTarget hfactor

end Mcmc.Executable.Continuous.NUTSIR
