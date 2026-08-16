import Mcmc.Finite.DynamicCandidate
import Mcmc.Finite.Combinators

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
