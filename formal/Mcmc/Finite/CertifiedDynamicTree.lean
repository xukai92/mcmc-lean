import Mcmc.Finite.DynamicCandidate

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

end Mcmc.Finite.MarkovKernel
