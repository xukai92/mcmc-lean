import Mcmc.Finite.DynamicCandidate
import Mcmc.Finite.Combinators
import Mcmc.Finite.CandidateMixture
import Mcmc.Finite.RootedTrace

/-!
# Certified finite dynamic trees

A dynamic trajectory builder may stop at a state-dependent depth.  Selection
is valid only if the completed candidate set can be rerooted at every admitted
leaf without changing that set.  This module packages that operational tree
certificate and converts it to the balance interface used by
`dynamicCandidateKernel`.

The certificate is exactly the structural boundary for a finite NUTS-style
tree builder.  It does not claim that an arbitrary first-U-turn stopping rule
satisfies reroot invariance.
-/

namespace Mcmc.Finite.MarkovKernel

variable {State : Type*} [Fintype State] [DecidableEq State]

/-- A completed finite tree represented by its admitted leaves at each root.
Rerooting at an admitted leaf must reproduce the same completed leaf set. -/
structure CertifiedDynamicTree (State : Type*) [Fintype State]
    [DecidableEq State] where
  candidates : State → Finset State
  root_mem : ∀ root, root ∈ candidates root
  reroot_eq : ∀ {root leaf}, leaf ∈ candidates root →
    candidates leaf = candidates root

/-- Decidable correctness predicate for completed candidate sets emitted by a
finite dynamic-tree builder. -/
def CertifiedDynamicTree.Checks
    (candidates : State → Finset State) : Prop :=
  (∀ root, root ∈ candidates root) ∧
    ∀ root leaf, leaf ∈ candidates root →
      candidates leaf = candidates root

instance CertifiedDynamicTree.instDecidableChecks
    (candidates : State → Finset State) : Decidable (Checks candidates) := by
  unfold Checks
  infer_instance

/-- Executable Boolean checker for a finite completed tree. -/
def CertifiedDynamicTree.check
    (candidates : State → Finset State) : Bool :=
  decide (Checks candidates)

theorem CertifiedDynamicTree.check_eq_true_iff
    (candidates : State → Finset State) :
    check candidates = true ↔ Checks candidates := by
  exact decide_eq_true_iff

/-- A successful executable check constructs the proof-bearing tree interface
consumed by the balance theorem. -/
def CertifiedDynamicTree.ofCheck
    (candidates : State → Finset State)
    (hcheck : check candidates = true) : CertifiedDynamicTree State where
  candidates := candidates
  root_mem := (check_eq_true_iff candidates).mp hcheck |>.1
  reroot_eq := by
    intro root leaf hleaf
    exact (check_eq_true_iff candidates).mp hcheck |>.2 root leaf hleaf

/-- Membership in a certified completed tree is a reroot-invariant candidate
relation. -/
noncomputable def CertifiedDynamicTree.toCandidateSet
    (target : Distribution State) (tree : CertifiedDynamicTree State) :
    RerootInvariantCandidateSet target where
  admissible root leaf := decide (leaf ∈ tree.candidates root)
  reflexive root := by simp [tree.root_mem]
  symmetric root leaf := by
    apply Bool.decide_congr
    constructor
    · intro hleaf
      rw [tree.reroot_eq hleaf]
      exact tree.root_mem root
    · intro hroot
      rw [tree.reroot_eq hroot]
      exact tree.root_mem leaf
  normalizer_eq := by
    intro root leaf hadmissible
    have hleaf : leaf ∈ tree.candidates root := by simpa using hadmissible
    have hreroot := tree.reroot_eq hleaf
    unfold dynamicCandidateNormalizer
    apply Finset.sum_congr rfl
    intro proposed _hproposed
    have hmem : proposed ∈ tree.candidates root ↔
        proposed ∈ tree.candidates leaf := by
      rw [hreroot]
    by_cases hroot : proposed ∈ tree.candidates root
    · have hleaf' := hmem.mp hroot
      simp [hroot, hleaf']
    · have hleaf' : proposed ∉ tree.candidates leaf :=
        fun h => hroot (hmem.mpr h)
      simp [hroot, hleaf']

/-- Target-weighted selection from any certified dynamic tree is reversible. -/
theorem CertifiedDynamicTree.kernel_reversible
    (target : Distribution State) (tree : CertifiedDynamicTree State)
    (htarget : ∀ state, 0 < target.mass state) :
    (dynamicCandidateKernel target (tree.toCandidateSet target) htarget).Reversible
      target :=
  dynamicCandidateKernel_reversible target (tree.toCandidateSet target) htarget

/-- Target-weighted selection from any certified dynamic tree is stationary. -/
theorem CertifiedDynamicTree.kernel_stationary
    (target : Distribution State) (tree : CertifiedDynamicTree State)
    (htarget : ∀ state, 0 < target.mass state) :
    (dynamicCandidateKernel target (tree.toCandidateSet target) htarget).Stationary
      target :=
  tree.kernel_reversible target htarget |>.stationary

/-- Checked builder output can be used directly as a stationary
target-weighted dynamic trajectory transition. -/
theorem CertifiedDynamicTree.checkedKernel_stationary
    (target : Distribution State) (candidates : State → Finset State)
    (hcheck : check candidates = true)
    (htarget : ∀ state, 0 < target.mass state) :
    (dynamicCandidateKernel target
      ((ofCheck candidates hcheck).toCandidateSet target)
      htarget).Stationary target :=
  (ofCheck candidates hcheck).kernel_stationary target htarget

/-- Total safety wrapper for an arbitrary completed candidate-row family.
Certified output uses target-weighted dynamic selection; failed certification
falls back to the identity kernel. -/
noncomputable def CertifiedDynamicTree.checkedOrIdentityKernel
    (target : Distribution State) (candidates : State → Finset State)
    (htarget : ∀ state, 0 < target.mass state) : MarkovKernel State :=
  if hcheck : check candidates = true then
    dynamicCandidateKernel target
      ((ofCheck candidates hcheck).toCandidateSet target) htarget
  else
    identity

/-- The total checked-or-identity wrapper is stationary for every candidate
family. This does not certify a failed dynamic builder; it makes failure an
explicit no-move transition. -/
theorem CertifiedDynamicTree.checkedOrIdentityKernel_stationary
    (target : Distribution State) (candidates : State → Finset State)
    (htarget : ∀ state, 0 < target.mass state) :
    (checkedOrIdentityKernel target candidates htarget).Stationary target := by
  by_cases hcheck : check candidates = true
  · rw [checkedOrIdentityKernel, dif_pos hcheck]
    exact checkedKernel_stationary target candidates hcheck htarget
  · rw [checkedOrIdentityKernel, dif_neg hcheck]
    exact identity_stationary target

/-- State-independent randomization over completed dynamic-tree traces. Each
trace is checked separately; invalid traces contribute an identity kernel. -/
noncomputable def CertifiedDynamicTree.randomizedCheckedOrIdentityKernel
    {Trace : Type*} [Fintype Trace]
    (traceLaw : Distribution Trace)
    (target : Distribution State)
    (candidates : Trace → State → Finset State)
    (htarget : ∀ state, 0 < target.mass state) : MarkovKernel State :=
  candidateMixture traceLaw fun trace =>
    checkedOrIdentityKernel target (candidates trace) htarget

/-- Randomized recursive builders preserve the target without assuming that
every direction trace certifies: the checked traces use reversible weighted
selection and all other traces make an explicit no-move transition. -/
theorem CertifiedDynamicTree.randomizedCheckedOrIdentityKernel_stationary
    {Trace : Type*} [Fintype Trace]
    (traceLaw : Distribution Trace)
    (target : Distribution State)
    (candidates : Trace → State → Finset State)
    (htarget : ∀ state, 0 < target.mass state) :
    (randomizedCheckedOrIdentityKernel traceLaw target candidates htarget).Stationary
      target := by
  apply candidateMixture_stationary
  intro trace
  exact checkedOrIdentityKernel_stationary target (candidates trace) htarget

/-- A leaf of a stopped doubling tree. `depth` may vary between tree
components, while a completed component contains `2^depth` leaf offsets. -/
structure StoppedDoublingLeaf (TreeId : Type*) [Fintype TreeId]
    (maxDepth : ℕ) where
  treeId : TreeId
  depth : Fin (maxDepth + 1)
  offset : Fin (2 ^ depth.val)
deriving DecidableEq, Fintype

/-- The completed tree component containing every leaf with the same tree ID
and stopped depth. -/
def stoppedDoublingCandidates {TreeId : Type*} [Fintype TreeId]
    [DecidableEq TreeId] (maxDepth : ℕ)
    (root : StoppedDoublingLeaf TreeId maxDepth) :
    Finset (StoppedDoublingLeaf TreeId maxDepth) :=
  Finset.univ.filter fun leaf =>
    leaf.treeId = root.treeId ∧ leaf.depth = root.depth

/-- Variable-depth stopped doubling components satisfy the reroot certificate.
The theorem certifies the completed tree; a concrete U-turn builder must still
prove that its output equals one of these components. -/
def stoppedDoublingTree {TreeId : Type*} [Fintype TreeId]
    [DecidableEq TreeId] (maxDepth : ℕ) :
    CertifiedDynamicTree (StoppedDoublingLeaf TreeId maxDepth) where
  candidates := stoppedDoublingCandidates maxDepth
  root_mem root := by simp [stoppedDoublingCandidates]
  reroot_eq := by
    intro root leaf hleaf
    simp only [stoppedDoublingCandidates, Finset.mem_filter,
      Finset.mem_univ, true_and] at hleaf
    apply Finset.filter_congr
    intro candidate _hcandidate
    constructor <;> intro h
    · exact ⟨h.1.trans hleaf.1, h.2.trans hleaf.2⟩
    · exact ⟨h.1.trans hleaf.1.symm, h.2.trans hleaf.2.symm⟩

@[simp] theorem check_stoppedDoublingCandidates
    {TreeId : Type*} [Fintype TreeId] [DecidableEq TreeId]
    (maxDepth : ℕ) :
    CertifiedDynamicTree.check (stoppedDoublingCandidates (TreeId := TreeId)
      maxDepth) = true := by
  rw [CertifiedDynamicTree.check_eq_true_iff]
  exact ⟨(stoppedDoublingTree maxDepth).root_mem,
    fun root leaf hleaf => (stoppedDoublingTree maxDepth).reroot_eq hleaf⟩

/-- Target-weighted selection from variable-depth completed doubling trees is
stationary. -/
theorem stoppedDoublingKernel_stationary
    {TreeId : Type*} [Fintype TreeId] [DecidableEq TreeId]
    (maxDepth : ℕ)
    (target : Distribution (StoppedDoublingLeaf TreeId maxDepth))
    (htarget : ∀ state, 0 < target.mass state) :
    (dynamicCandidateKernel target
      ((stoppedDoublingTree maxDepth).toCandidateSet target)
      htarget).Stationary target :=
  (stoppedDoublingTree maxDepth).kernel_stationary target htarget

/-! ### Root-dependent stopping obstruction -/

/-- Minimal root-dependent first-stop pattern: the left root admits both
leaves, while rerooting at the right leaf exposes only itself. This is the
finite structural failure that a U-turn recursion must rule out or send to the
checked identity fallback. -/
def asymmetricFirstStopCandidates : Fin 2 → Finset (Fin 2)
  | ⟨0, _⟩ => Finset.univ
  | ⟨1, _⟩ => {⟨1, by omega⟩}

@[simp] theorem check_asymmetricFirstStopCandidates :
    CertifiedDynamicTree.check asymmetricFirstStopCandidates = false := by
  native_decide

/-- Consequently there is no proof-bearing certified tree whose rows are the
naive asymmetric first-stop rows. This rules out an unconditional theorem
that root retention alone makes a stopped dynamic trajectory reroot safe. -/
theorem not_checks_asymmetricFirstStopCandidates :
    ¬ CertifiedDynamicTree.Checks asymmetricFirstStopCandidates := by
  intro hchecks
  have htrue : CertifiedDynamicTree.check asymmetricFirstStopCandidates = true :=
    (CertifiedDynamicTree.check_eq_true_iff _).2 hchecks
  simp at htrue

/-- The total safety wrapper makes the obstruction an exact no-move kernel,
not an unchecked dynamic transition. -/
theorem asymmetricFirstStop_checkedOrIdentity_eq_identity
    (target : Distribution (Fin 2))
    (htarget : ∀ state, 0 < target.mass state) :
    CertifiedDynamicTree.checkedOrIdentityKernel target
      asymmetricFirstStopCandidates htarget = identity := by
  rw [CertifiedDynamicTree.checkedOrIdentityKernel]
  simp

/-- Canonical component label on a finite trajectory: the number of declared
barrier edges strictly before the state. -/
def lineBarrierLabel (barriers : List Bool)
    (state : Fin (barriers.length + 1)) : ℕ :=
  (barriers.take state.val).count true

/-- Candidate component obtained by cutting a finite trajectory at every
declared barrier edge. -/
def lineBarrierCandidates (barriers : List Bool)
    (root : Fin (barriers.length + 1)) :
    Finset (Fin (barriers.length + 1)) :=
  Finset.univ.filter fun leaf =>
    lineBarrierLabel barriers leaf = lineBarrierLabel barriers root

/-- Scalar endpoint U-turn test for two adjacent phase points. A barrier is
declared when the displacement has negative inner product with either endpoint
momentum. -/
noncomputable def scalarAdjacentUTurn (left right : ℝ × ℝ) : Bool :=
  decide ((right.1 - left.1) * left.2 < 0 ∨
    (right.1 - left.1) * right.2 < 0)

/-- Canonical local U-turn barriers along a complete scalar trajectory. The
detector runs on the full root-independent orbit before partitioning. -/
noncomputable def scalarAdjacentUTurnBarriers : List (ℝ × ℝ) → List Bool
  | left :: right :: rest =>
      scalarAdjacentUTurn left right ::
        scalarAdjacentUTurnBarriers (right :: rest)
  | _ => []

@[simp] theorem length_scalarAdjacentUTurnBarriers
    (trajectory : List (ℝ × ℝ)) :
    (scalarAdjacentUTurnBarriers trajectory).length = trajectory.length - 1 := by
  induction trajectory with
  | nil => rfl
  | cons left tail ih =>
      cases tail with
      | nil => rfl
      | cons right rest =>
          simp [scalarAdjacentUTurnBarriers] at ih ⊢
          exact ih

/-- Barrier partitioning is reroot stable by construction. A numerical
U-turn detector may safely feed this builder only after assigning barriers on
the canonical full trajectory, rather than stopping from a root-dependent
partial view. -/
def lineBarrierTree (barriers : List Bool) :
    CertifiedDynamicTree (Fin (barriers.length + 1)) where
  candidates := lineBarrierCandidates barriers
  root_mem root := by simp [lineBarrierCandidates]
  reroot_eq := by
    intro root leaf hleaf
    simp only [lineBarrierCandidates, Finset.mem_filter, Finset.mem_univ,
      true_and] at hleaf
    apply Finset.filter_congr
    intro candidate _
    constructor <;> intro h
    · exact h.trans hleaf
    · exact h.trans hleaf.symm

@[simp] theorem check_lineBarrierCandidates (barriers : List Bool) :
    CertifiedDynamicTree.check (lineBarrierCandidates barriers) = true := by
  rw [CertifiedDynamicTree.check_eq_true_iff]
  exact ⟨(lineBarrierTree barriers).root_mem,
    fun root leaf hleaf => (lineBarrierTree barriers).reroot_eq hleaf⟩

/-- Target-weighted selection within canonical barrier-delimited trajectory
components is stationary. -/
theorem lineBarrierKernel_stationary
    (barriers : List Bool)
    (target : Distribution (Fin (barriers.length + 1)))
    (htarget : ∀ state, 0 < target.mass state) :
    (dynamicCandidateKernel target
      ((lineBarrierTree barriers).toCandidateSet target)
      htarget).Stationary target :=
  (lineBarrierTree barriers).kernel_stationary target htarget

/-- The concrete adjacent-endpoint U-turn detector produces a checked
reroot-invariant partition. This is a safe dynamic trajectory construction,
not an equivalence theorem for recursive subtree-based NUTS. -/
@[simp] theorem check_scalarAdjacentUTurnCandidates
    (trajectory : List (ℝ × ℝ)) :
    CertifiedDynamicTree.check
      (lineBarrierCandidates (scalarAdjacentUTurnBarriers trajectory)) = true :=
  check_lineBarrierCandidates _

/-- Target-weighted selection inside the concrete scalar U-turn partition is
stationary. -/
theorem scalarAdjacentUTurnKernel_stationary
    (trajectory : List (ℝ × ℝ))
    (target : Distribution
      (Fin ((scalarAdjacentUTurnBarriers trajectory).length + 1)))
    (htarget : ∀ state, 0 < target.mass state) :
    (dynamicCandidateKernel target
      ((lineBarrierTree (scalarAdjacentUTurnBarriers trajectory)).toCandidateSet
        target)
      htarget).Stationary target :=
  lineBarrierKernel_stationary _ target htarget

/-- Finite-dimensional endpoint U-turn test using the Euclidean inner
product with both endpoint momenta. -/
noncomputable def vectorAdjacentUTurn {ι : Type*} [Fintype ι]
    (left right : (ι → ℝ) × (ι → ℝ)) : Bool :=
  decide ((∑ i, (right.1 i - left.1 i) * left.2 i) < 0 ∨
    (∑ i, (right.1 i - left.1 i) * right.2 i) < 0)

/-- Root-independent finite-dimensional U-turn barriers on a complete
canonical trajectory. -/
noncomputable def vectorAdjacentUTurnBarriers {ι : Type*} [Fintype ι] :
    List ((ι → ℝ) × (ι → ℝ)) → List Bool
  | left :: right :: rest =>
      vectorAdjacentUTurn left right ::
        vectorAdjacentUTurnBarriers (right :: rest)
  | _ => []

@[simp] theorem length_vectorAdjacentUTurnBarriers
    {ι : Type*} [Fintype ι]
    (trajectory : List ((ι → ℝ) × (ι → ℝ))) :
    (vectorAdjacentUTurnBarriers trajectory).length = trajectory.length - 1 := by
  induction trajectory with
  | nil => rfl
  | cons left tail ih =>
      cases tail with
      | nil => rfl
      | cons right rest =>
          simp [vectorAdjacentUTurnBarriers] at ih ⊢
          exact ih

@[simp] theorem check_vectorAdjacentUTurnCandidates
    {ι : Type*} [Fintype ι]
    (trajectory : List ((ι → ℝ) × (ι → ℝ))) :
    CertifiedDynamicTree.check
      (lineBarrierCandidates (vectorAdjacentUTurnBarriers trajectory)) = true :=
  check_lineBarrierCandidates _

/-- Target-weighted selection inside a finite-dimensional canonical U-turn
partition is stationary. -/
theorem vectorAdjacentUTurnKernel_stationary
    {ι : Type*} [Fintype ι]
    (trajectory : List ((ι → ℝ) × (ι → ℝ)))
    (target : Distribution
      (Fin ((vectorAdjacentUTurnBarriers trajectory).length + 1)))
    (htarget : ∀ state, 0 < target.mass state) :
    (dynamicCandidateKernel target
      ((lineBarrierTree (vectorAdjacentUTurnBarriers trajectory)).toCandidateSet
        target)
      htarget).Stationary target :=
  lineBarrierKernel_stationary _ target htarget

/-- A split is blocked when any endpoint pair spanning it satisfies the
finite-dimensional U-turn test.  This aggregates turns over every trajectory
scale, unlike the adjacent-only detector. -/
noncomputable def vectorSpanningUTurn {ι : Type*} [Fintype ι]
    (left right : List ((ι → ℝ) × (ι → ℝ))) : Bool :=
  left.any fun x => right.any fun y => vectorAdjacentUTurn x y

/-- Accumulator for the canonical all-scales split detector. -/
noncomputable def vectorSpanningUTurnBarriersAux {ι : Type*} [Fintype ι] :
    List ((ι → ℝ) × (ι → ℝ)) →
      List ((ι → ℝ) × (ι → ℝ)) → List Bool
  | _seen, [] => []
  | seen, right :: rest =>
      vectorSpanningUTurn seen (right :: rest) ::
        vectorSpanningUTurnBarriersAux (seen ++ [right]) rest

@[simp] theorem length_vectorSpanningUTurnBarriersAux
    {ι : Type*} [Fintype ι]
    (seen suffix : List ((ι → ℝ) × (ι → ℝ))) :
    (vectorSpanningUTurnBarriersAux seen suffix).length = suffix.length := by
  induction suffix generalizing seen with
  | nil => rfl
  | cons right rest ih =>
      simp [vectorSpanningUTurnBarriersAux, ih]

/-- Root-independent all-scales U-turn barriers.  At the split after state
`i`, all endpoint pairs with left endpoint at or before `i` and right endpoint
after `i` are inspected.  Cutting every such turning split is conservative,
but produces completed components rather than root-dependent partial trees. -/
noncomputable def vectorSpanningUTurnBarriers {ι : Type*} [Fintype ι] :
    List ((ι → ℝ) × (ι → ℝ)) → List Bool
  | [] => []
  | first :: rest => vectorSpanningUTurnBarriersAux [first] rest

@[simp] theorem length_vectorSpanningUTurnBarriers
    {ι : Type*} [Fintype ι]
    (trajectory : List ((ι → ℝ) × (ι → ℝ))) :
    (vectorSpanningUTurnBarriers trajectory).length = trajectory.length - 1 := by
  cases trajectory with
  | nil => rfl
  | cons first rest =>
      simp [vectorSpanningUTurnBarriers]

@[simp] theorem check_vectorSpanningUTurnCandidates
    {ι : Type*} [Fintype ι]
    (trajectory : List ((ι → ℝ) × (ι → ℝ))) :
    CertifiedDynamicTree.check
      (lineBarrierCandidates (vectorSpanningUTurnBarriers trajectory)) = true :=
  check_lineBarrierCandidates _

/-- Target-weighted selection inside the conservative all-scales U-turn
partition is stationary. -/
theorem vectorSpanningUTurnKernel_stationary
    {ι : Type*} [Fintype ι]
    (trajectory : List ((ι → ℝ) × (ι → ℝ)))
    (target : Distribution
      (Fin ((vectorSpanningUTurnBarriers trajectory).length + 1)))
    (htarget : ∀ state, 0 < target.mass state) :
    (dynamicCandidateKernel target
      ((lineBarrierTree
        (vectorSpanningUTurnBarriers trajectory)).toCandidateSet target)
      htarget).Stationary target :=
  lineBarrierKernel_stationary _ target htarget

/-! ### Recursive aggregation of completed dynamic subtrees -/

/-- A completed binary dynamic tree records the barrier at each join.  A
`true` join excludes communication between its two completed subtrees; a
`false` join admits their leaves into one candidate component.  This is a
root-independent completed-tree representation, not a first-U-turn stopping
procedure. -/
inductive RecursiveBarrierTree where
  | leaf
  | node (left : RecursiveBarrierTree) (blocked : Bool)
      (right : RecursiveBarrierTree)
deriving DecidableEq

/-- Number of completed leaves represented by a recursive barrier tree. -/
def RecursiveBarrierTree.leafCount : RecursiveBarrierTree → ℕ
  | .leaf => 1
  | .node left _ right => left.leafCount + right.leafCount

/-- In-order barrier sequence obtained by recursively aggregating completed
subtrees. -/
def RecursiveBarrierTree.barriers : RecursiveBarrierTree → List Bool
  | .leaf => []
  | .node left blocked right =>
      left.barriers ++ blocked :: right.barriers

/-- Interpret a completed recursive barrier tree as the Boolean control flow
of `BuildTree`. Leaves pass the local continuation check in this structural
model; a blocked join is exactly a failed endpoint U-turn check. -/
def RecursiveBarrierTree.toNUTSBuildFlagTree :
    RecursiveBarrierTree → NUTSBuildFlagTree
  | .leaf => .leaf true
  | .node left blocked right =>
      .node left.toNUTSBuildFlagTree right.toNUTSBuildFlagTree (!blocked)

/-- Recursive `BuildTree` continuation succeeds exactly when the completed
barrier tree contains no blocked join. -/
theorem RecursiveBarrierTree.toNUTSBuildFlagTree_continues
    (tree : RecursiveBarrierTree) :
    tree.toNUTSBuildFlagTree.continues = !tree.barriers.any id := by
  induction tree with
  | leaf => rfl
  | node left blocked right ihLeft ihRight =>
      simp [RecursiveBarrierTree.toNUTSBuildFlagTree,
        RecursiveBarrierTree.barriers, ihLeft, ihRight,
        Bool.and_left_comm, Bool.and_comm]

/-- Equivalent proposition-level form: every recursive U-turn join must be
unblocked for the completed call to return `s = 1`. -/
theorem RecursiveBarrierTree.toNUTSBuildFlagTree_continues_eq_true_iff
    (tree : RecursiveBarrierTree) :
    tree.toNUTSBuildFlagTree.continues = true ↔
      ∀ blocked ∈ tree.barriers, blocked = false := by
  rw [tree.toNUTSBuildFlagTree_continues]
  simp

/-! ### Concrete recursive phase-tree flags -/

/-- A completed balanced binary tree retaining its phase point at every leaf.
This is the proof-level counterpart of the recursive interval traversed by the
Julia `subtree_turns`/`BuildTree` implementation. -/
inductive RecursivePhaseTree (Phase : Type*) where
  | leaf (phase : Phase)
  | node (left right : RecursivePhaseTree Phase)
deriving DecidableEq

/-- Leftmost phase point returned by a completed recursive call. -/
def RecursivePhaseTree.leftmost {Phase : Type*} :
    RecursivePhaseTree Phase → Phase
  | .leaf phase => phase
  | .node left _ => left.leftmost

/-- Rightmost phase point returned by a completed recursive call. -/
def RecursivePhaseTree.rightmost {Phase : Type*} :
    RecursivePhaseTree Phase → Phase
  | .leaf phase => phase
  | .node _ right => right.rightmost

/-- Number of phase leaves in a completed recursive tree. -/
def RecursivePhaseTree.leafCount {Phase : Type*} :
    RecursivePhaseTree Phase → ℕ
  | .leaf _ => 1
  | .node left right => left.leafCount + right.leafCount

/-- Left half of a flat length-`2^(depth+1)` trajectory. -/
def balancedPhaseLeftHalf {Phase : Type*} {depth : ℕ}
    (phases : Fin (2 ^ (depth + 1)) → Phase) : Fin (2 ^ depth) → Phase :=
  fun index => phases ⟨index.val, by
    rw [pow_succ]
    have hpos : 0 < 2 ^ depth := pow_pos (by norm_num) _
    omega⟩

/-- Right half of a flat length-`2^(depth+1)` trajectory. -/
def balancedPhaseRightHalf {Phase : Type*} {depth : ℕ}
    (phases : Fin (2 ^ (depth + 1)) → Phase) : Fin (2 ^ depth) → Phase :=
  fun index => phases ⟨2 ^ depth + index.val, by
    rw [pow_succ]
    omega⟩

/-- Canonical balanced recursive tree obtained by repeatedly splitting a flat
power-of-two trajectory into its left and right halves. This mirrors the
index recursion in the production `subtree_turns` implementation. -/
def balancedPhaseTree {Phase : Type*} :
    (depth : ℕ) → (Fin (2 ^ depth) → Phase) → RecursivePhaseTree Phase
  | 0, phases => .leaf (phases ⟨0, by simp⟩)
  | depth + 1, phases =>
      .node (balancedPhaseTree depth (balancedPhaseLeftHalf phases))
        (balancedPhaseTree depth (balancedPhaseRightHalf phases))

@[simp] theorem balancedPhaseTree_zero {Phase : Type*}
    (phases : Fin (2 ^ 0) → Phase) :
    balancedPhaseTree 0 phases = .leaf (phases ⟨0, by simp⟩) := rfl

@[simp] theorem balancedPhaseTree_succ {Phase : Type*} (depth : ℕ)
    (phases : Fin (2 ^ (depth + 1)) → Phase) :
    balancedPhaseTree (depth + 1) phases =
      .node (balancedPhaseTree depth (balancedPhaseLeftHalf phases))
        (balancedPhaseTree depth (balancedPhaseRightHalf phases)) := rfl

/-- A flat length-`2^depth` trajectory produces exactly `2^depth` completed
recursive leaves. -/
@[simp] theorem balancedPhaseTree_leafCount {Phase : Type*} (depth : ℕ)
    (phases : Fin (2 ^ depth) → Phase) :
    (balancedPhaseTree depth phases).leafCount = 2 ^ depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      simp only [balancedPhaseTree_succ, RecursivePhaseTree.leafCount,
        ih, pow_succ]
      omega

/-- Compute the exact recursive `BuildTree` Boolean trace. Leaves use the
supplied slice/divergence check; every internal join uses the supplied endpoint
U-turn predicate on the complete subtree's outermost phase points. -/
def RecursivePhaseTree.toBuildFlagTree {Phase : Type*}
    (leafContinues : Phase → Bool) (endpointTurns : Phase → Phase → Bool) :
    RecursivePhaseTree Phase → NUTSBuildFlagTree
  | .leaf phase => .leaf (leafContinues phase)
  | .node left right =>
      .node (left.toBuildFlagTree leafContinues endpointTurns)
        (right.toBuildFlagTree leafContinues endpointTurns)
        (!(endpointTurns left.leftmost right.rightmost))

/-- Structural proposition saying that every leaf passes its local check and
every completed recursive subtree passes its endpoint U-turn test. -/
def RecursivePhaseTree.AllChecksPass {Phase : Type*}
    (leafContinues : Phase → Bool) (endpointTurns : Phase → Phase → Bool) :
    RecursivePhaseTree Phase → Prop
  | .leaf phase => leafContinues phase = true
  | .node left right =>
      left.AllChecksPass leafContinues endpointTurns ∧
        right.AllChecksPass leafContinues endpointTurns ∧
        endpointTurns left.leftmost right.rightmost = false

/-- The computed recursive continuation bit is exact: it succeeds if and only
if all concrete leaf and recursive endpoint checks pass. -/
theorem RecursivePhaseTree.toBuildFlagTree_continues_eq_true_iff
    {Phase : Type*} (leafContinues : Phase → Bool)
    (endpointTurns : Phase → Phase → Bool)
    (tree : RecursivePhaseTree Phase) :
    (tree.toBuildFlagTree leafContinues endpointTurns).continues = true ↔
      tree.AllChecksPass leafContinues endpointTurns := by
  induction tree with
  | leaf phase => simp [RecursivePhaseTree.toBuildFlagTree,
      RecursivePhaseTree.AllChecksPass]
  | node left right ihLeft ihRight =>
      simp [RecursivePhaseTree.toBuildFlagTree,
        RecursivePhaseTree.AllChecksPass,
        ihLeft, ihRight, and_assoc]

/-- Concrete finite-dimensional NUTS flag tree using the already formalized
Euclidean endpoint U-turn predicate. -/
noncomputable def RecursivePhaseTree.toVectorNUTSBuildFlagTree
    {ι : Type*} [Fintype ι]
    (leafContinues : ((ι → ℝ) × (ι → ℝ)) → Bool)
    (tree : RecursivePhaseTree ((ι → ℝ) × (ι → ℝ))) :
    NUTSBuildFlagTree :=
  tree.toBuildFlagTree leafContinues vectorAdjacentUTurn

/-- The production vector endpoint tests and supplied divergence checks
compute exactly the structural all-checks predicate. -/
theorem RecursivePhaseTree.toVectorNUTSBuildFlagTree_continues_eq_true_iff
    {ι : Type*} [Fintype ι]
    (leafContinues : ((ι → ℝ) × (ι → ℝ)) → Bool)
    (tree : RecursivePhaseTree ((ι → ℝ) × (ι → ℝ))) :
    (tree.toVectorNUTSBuildFlagTree leafContinues).continues = true ↔
      tree.AllChecksPass leafContinues vectorAdjacentUTurn :=
  tree.toBuildFlagTree_continues_eq_true_iff leafContinues vectorAdjacentUTurn

/-- Per-root, per-doubling concrete phase trees instantiate the outer stopping
data consumed by the completed-tree rerooting theorem. -/
noncomputable def CompletedTreeStoppingData.ofVectorPhaseTrees
    {ι : Type*} [Fintype ι] {depth : ℕ}
    (leafContinues : ((ι → ℝ) × (ι → ℝ)) → Bool)
    (trees : Fin (2 ^ depth) → Fin depth →
      RecursivePhaseTree ((ι → ℝ) × (ι → ℝ))) :
    CompletedTreeStoppingData depth :=
  CompletedTreeStoppingData.ofBuildFlagTrees fun root index =>
    (trees root index).toVectorNUTSBuildFlagTree leafContinues

/-- A root survives the concrete vector NUTS stopping computation exactly
when every required recursive phase tree passes all leaf and endpoint tests. -/
theorem CompletedTreeStoppingData.ofVectorPhaseTrees_admissible_iff
    {ι : Type*} [Fintype ι] {depth : ℕ}
    (leafContinues : ((ι → ℝ) × (ι → ℝ)) → Bool)
    (trees : Fin (2 ^ depth) → Fin depth →
      RecursivePhaseTree ((ι → ℝ) × (ι → ℝ)))
    (root : Fin (2 ^ depth)) :
    (CompletedTreeStoppingData.ofVectorPhaseTrees leafContinues trees).admissible
        root ↔
      ∀ index, (trees root index).AllChecksPass leafContinues
        vectorAdjacentUTurn := by
  unfold CompletedTreeStoppingData.ofVectorPhaseTrees
  rw [CompletedTreeStoppingData.ofBuildFlagTrees_admissible_iff]
  constructor
  · intro h index
    exact ((trees root index).toVectorNUTSBuildFlagTree_continues_eq_true_iff
      leafContinues).mp (h index)
  · intro h index
    exact ((trees root index).toVectorNUTSBuildFlagTree_continues_eq_true_iff
      leafContinues).mpr (h index)

/-- Concrete stopping data directly from the flat power-of-two trajectory
segments used at each outer doubling depth and each possible root. -/
noncomputable def CompletedTreeStoppingData.ofFlatVectorTrajectories
    {ι : Type*} [Fintype ι] {depth : ℕ}
    (leafContinues : ((ι → ℝ) × (ι → ℝ)) → Bool)
    (trajectories : (root : Fin (2 ^ depth)) → (index : Fin depth) →
      Fin (2 ^ index.val) → ((ι → ℝ) × (ι → ℝ))) :
    CompletedTreeStoppingData depth :=
  CompletedTreeStoppingData.ofVectorPhaseTrees leafContinues fun root index =>
    balancedPhaseTree index.val (trajectories root index)

/-- Flat production-style trajectory segments survive C.4 rerooting exactly
when every balanced segment passes all leaf divergence/slice checks and all
recursive vector endpoint U-turn checks. -/
theorem CompletedTreeStoppingData.ofFlatVectorTrajectories_admissible_iff
    {ι : Type*} [Fintype ι] {depth : ℕ}
    (leafContinues : ((ι → ℝ) × (ι → ℝ)) → Bool)
    (trajectories : (root : Fin (2 ^ depth)) → (index : Fin depth) →
      Fin (2 ^ index.val) → ((ι → ℝ) × (ι → ℝ)))
    (root : Fin (2 ^ depth)) :
    (CompletedTreeStoppingData.ofFlatVectorTrajectories leafContinues
      trajectories).admissible root ↔
      ∀ index, (balancedPhaseTree index.val
        (trajectories root index)).AllChecksPass leafContinues
          vectorAdjacentUTurn := by
  unfold CompletedTreeStoppingData.ofFlatVectorTrajectories
  exact CompletedTreeStoppingData.ofVectorPhaseTrees_admissible_iff
    leafContinues
    (fun root index => balancedPhaseTree index.val (trajectories root index))
    root

/-! ### Retained endpoint weights on flat trajectory segments -/

/-- Indicator weight of a flat phase point passing the slice-eligibility
predicate. This is deliberately separate from the divergence continuation
predicate: Algorithm 3 permits a nondivergent leaf with eligible count zero. -/
noncomputable def flatEligibleEndpointWeight
    {Phase : Type*} {count : ℕ} (eligible : Phase → Bool)
    (phases : Fin count → Phase) (index : Fin count) : ℝ :=
  if eligible (phases index) then 1 else 0

/-- Total eligible count returned by a flat completed subtree. -/
noncomputable def flatEligibleCount
    {Phase : Type*} {count : ℕ} (eligible : Phase → Bool)
    (phases : Fin count → Phase) : ℝ :=
  ∑ index, flatEligibleEndpointWeight eligible phases index

theorem flatEligibleEndpointWeight_nonneg
    {Phase : Type*} {count : ℕ} (eligible : Phase → Bool)
    (phases : Fin count → Phase) (index : Fin count) :
    0 ≤ flatEligibleEndpointWeight eligible phases index := by
  unfold flatEligibleEndpointWeight
  split <;> norm_num

/-- Retaining one known eligible point (in particular the current root)
makes the completed endpoint normalizer strictly positive. -/
theorem flatEligibleCount_pos_of_eligible
    {Phase : Type*} {count : ℕ} (eligible : Phase → Bool)
    (phases : Fin count → Phase) (current : Fin count)
    (hcurrent : eligible (phases current) = true) :
    0 < flatEligibleCount eligible phases := by
  have hsingle : (1 : ℝ) ≤ flatEligibleCount eligible phases := by
    unfold flatEligibleCount
    have hnonneg : ∀ index ∈ (Finset.univ : Finset (Fin count)),
        0 ≤ flatEligibleEndpointWeight eligible phases index := by
      intro index _
      exact flatEligibleEndpointWeight_nonneg eligible phases index
    have hle := Finset.single_le_sum hnonneg (Finset.mem_univ current)
    simpa [flatEligibleEndpointWeight, hcurrent] using hle
  linarith

/-- Exact normalized endpoint law on the retained flat trajectory. -/
noncomputable def flatEligibleDistribution
    {Phase : Type*} {count : ℕ} (eligible : Phase → Bool)
    (phases : Fin count → Phase)
    (hpositive : 0 < flatEligibleCount eligible phases) :
    Distribution (Fin count) where
  mass index := flatEligibleEndpointWeight eligible phases index /
    flatEligibleCount eligible phases
  nonneg index := div_nonneg
    (flatEligibleEndpointWeight_nonneg eligible phases index) hpositive.le
  sum_mass := by
    rw [← Finset.sum_div]
    exact div_self hpositive.ne'

@[simp] theorem flatEligibleDistribution_mass
    {Phase : Type*} {count : ℕ} (eligible : Phase → Bool)
    (phases : Fin count → Phase)
    (hpositive : 0 < flatEligibleCount eligible phases)
    (index : Fin count) :
    (flatEligibleDistribution eligible phases hpositive).mass index =
      flatEligibleEndpointWeight eligible phases index /
        flatEligibleCount eligible phases := rfl

/-- An in-order recursive tree has exactly one fewer joins than leaves. This
identifies the `Fin` state space of the flattened checker with the completed
recursive tree's leaves. -/
@[simp] theorem RecursiveBarrierTree.length_barriers (tree : RecursiveBarrierTree) :
    tree.barriers.length + 1 = tree.leafCount := by
  induction tree with
  | leaf => rfl
  | node left blocked right ihLeft ihRight =>
      simp only [RecursiveBarrierTree.barriers, List.length_append,
        List.length_cons, RecursiveBarrierTree.leafCount]
      omega

/-- Candidate components represented by a completed recursive tree. -/
def RecursiveBarrierTree.candidates (tree : RecursiveBarrierTree)
    (root : Fin (tree.barriers.length + 1)) :
    Finset (Fin (tree.barriers.length + 1)) :=
  lineBarrierCandidates tree.barriers root

/-- Recursive subtree aggregation always produces a checked, reroot-invariant
completed candidate tree. -/
@[simp] theorem RecursiveBarrierTree.check_candidates
    (tree : RecursiveBarrierTree) :
    CertifiedDynamicTree.check tree.candidates = true :=
  check_lineBarrierCandidates tree.barriers

/-- The checked tree constructed from recursive subtree joins is definitionally
the canonical barrier-partition tree. -/
theorem RecursiveBarrierTree.ofCheck_candidates_eq (tree : RecursiveBarrierTree) :
    (CertifiedDynamicTree.ofCheck tree.candidates tree.check_candidates).candidates =
      lineBarrierCandidates tree.barriers := by
  rfl

/-- Target-weighted selection within recursively aggregated completed
subtrees is stationary. -/
theorem RecursiveBarrierTree.kernel_stationary
    (tree : RecursiveBarrierTree)
    (target : Distribution (Fin (tree.barriers.length + 1)))
    (htarget : ∀ state, 0 < target.mass state) :
    (dynamicCandidateKernel target
      ((lineBarrierTree tree.barriers).toCandidateSet target)
      htarget).Stationary target :=
  lineBarrierKernel_stationary tree.barriers target htarget

end Mcmc.Finite.MarkovKernel
