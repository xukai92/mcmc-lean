import Mcmc.Finite.Transport
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Topology.Order.Compact

/-!
# The real finite transport polytope

Finite probability masses are converted to real coordinates so that the
transport problem can use mathlib's finite-dimensional convex geometry.  The
feasible set is a closed subset of the standard simplex.  In particular it is
compact, linear transport costs attain a minimum, and a quadratic tie-breaker
attains a maximum on the optimal face.
-/

open scoped BigOperators ENNReal NNReal

namespace Mcmc.Finite

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Real joint-mass tables with the prescribed finite PMF marginals. -/
def realTransportPlans (p : PMF α) (q : PMF β) :
    Set ((α × β) → ℝ) :=
  {r | (∀ edge, 0 ≤ r edge) ∧
    (∀ i, ∑ j, r (i, j) = (p i).toReal) ∧
    ∀ j, ∑ i, r (i, j) = (q j).toReal}

/-- Convert a nonnegative real transport table back to ENNReal masses. -/
def realTransportPlanToENNReal (r : (α × β) → ℝ) :
    (α × β) → ENNReal :=
  fun edge => ENNReal.ofReal (r edge)

omit [Fintype α] [Fintype β] in
@[simp]
theorem realTransportPlanToENNReal_apply (r : (α × β) → ℝ)
    (edge : α × β) :
    realTransportPlanToENNReal r edge = ENNReal.ofReal (r edge) :=
  rfl

/-- A feasible real table converts to a feasible ENNReal transport plan. -/
theorem realTransportPlanToENNReal_mem_transportPlans
    {p : PMF α} {q : PMF β} {r : (α × β) → ℝ}
    (hr : r ∈ realTransportPlans p q) :
    realTransportPlanToENNReal r ∈ transportPlans p q := by
  constructor
  · intro i
    unfold realTransportPlanToENNReal
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hr.1 (i, j)), hr.2.1 i,
      ENNReal.ofReal_toReal (p.apply_ne_top i)]
  · intro j
    unfold realTransportPlanToENNReal
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hr.1 (i, j)), hr.2.2 j,
      ENNReal.ofReal_toReal (q.apply_ne_top j)]

omit [Fintype α] [Fintype β] in
/-- On a nonnegative real table, conversion followed by `toReal` is the
identity coordinatewise. -/
theorem realTransportPlanToENNReal_toReal
    {r : (α × β) → ℝ} (hr : ∀ edge, 0 ≤ r edge) (edge : α × β) :
    (realTransportPlanToENNReal r edge).toReal = r edge := by
  exact ENNReal.toReal_ofReal (hr edge)

/-- Convert a finite ENNReal transport table to real coordinates. -/
def transportPlanToReal (r : (α × β) → ENNReal) : (α × β) → ℝ :=
  fun edge => (r edge).toReal

/-- A feasible ENNReal transport plan converts to a feasible real plan. -/
theorem transportPlanToReal_mem_realTransportPlans
    {p : PMF α} {q : PMF β} {r : (α × β) → ENNReal}
    (hr : r ∈ transportPlans p q) :
    transportPlanToReal r ∈ realTransportPlans p q := by
  refine ⟨fun edge => ENNReal.toReal_nonneg, ?_, ?_⟩
  · intro i
    unfold transportPlanToReal
    rw [← ENNReal.toReal_sum (fun j _ => transportPlan_apply_ne_top hr (i, j)),
      hr.1 i]
  · intro j
    unfold transportPlanToReal
    rw [← ENNReal.toReal_sum (fun i _ => transportPlan_apply_ne_top hr (i, j)),
      hr.2 j]

/-- The two finite coordinate conversions are inverse on feasible ENNReal
plans. -/
theorem realTransportPlanToENNReal_transportPlanToReal
    {p : PMF α} {q : PMF β} {r : (α × β) → ENNReal}
    (hr : r ∈ transportPlans p q) :
    realTransportPlanToENNReal (transportPlanToReal r) = r := by
  funext edge
  exact ENNReal.ofReal_toReal (transportPlan_apply_ne_top hr edge)

private theorem sum_pmf_toReal (p : PMF α) :
    ∑ i, (p i).toReal = 1 := by
  calc
    ∑ i, (p i).toReal = (∑ i, p i).toReal := by
      rw [ENNReal.toReal_sum (fun i _ => p.apply_ne_top i)]
    _ = (∑' i, p i).toReal := by rw [tsum_fintype]
    _ = 1 := by rw [p.tsum_coe, ENNReal.toReal_one]

/-- The independent product table witnesses nonemptiness of the real
transport polytope. -/
theorem independent_real_mass_mem_realTransportPlans (p : PMF α) (q : PMF β) :
    (fun edge : α × β => (p edge.1).toReal * (q edge.2).toReal) ∈
      realTransportPlans p q := by
  refine ⟨fun edge => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
    ?_, ?_⟩
  · intro i
    simp only
    rw [← Finset.mul_sum, sum_pmf_toReal, mul_one]
  · intro j
    simp only
    rw [← Finset.sum_mul, sum_pmf_toReal, one_mul]

theorem realTransportPlans_nonempty (p : PMF α) (q : PMF β) :
    (realTransportPlans p q).Nonempty :=
  ⟨_, independent_real_mass_mem_realTransportPlans p q⟩

/-- Every feasible real table has total mass one. -/
theorem realTransportPlans_sum_eq_one
    {p : PMF α} {q : PMF β} {r : (α × β) → ℝ}
    (hr : r ∈ realTransportPlans p q) :
    ∑ edge, r edge = 1 := by
  rw [show (∑ edge, r edge) = ∑ i, ∑ j, r (i, j) by
    calc
      (∑ edge, r edge) = ∑ edge ∈
          (Finset.univ : Finset α).product (Finset.univ : Finset β), r edge := by
            apply Finset.sum_subset
            · simp
            · intro edge hedge hedge'
              simp at hedge'
      _ = ∑ i, ∑ j, r (i, j) :=
        Finset.sum_product (Finset.univ : Finset α)
          (Finset.univ : Finset β) r]
  calc
    _ = ∑ i, (p i).toReal := Finset.sum_congr rfl fun i _ => hr.2.1 i
    _ = 1 := sum_pmf_toReal p

/-- Real transport plans are contained in the standard probability simplex. -/
theorem realTransportPlans_subset_stdSimplex (p : PMF α) (q : PMF β) :
    realTransportPlans p q ⊆ stdSimplex ℝ (α × β) := by
  intro r hr
  exact ⟨hr.1, realTransportPlans_sum_eq_one hr⟩

/-- The real finite transport polytope is closed. -/
theorem isClosed_realTransportPlans (p : PMF α) (q : PMF β) :
    IsClosed (realTransportPlans p q) := by
  rw [show realTransportPlans p q =
      (⋂ edge : α × β, {r | 0 ≤ r edge}) ∩
        ((⋂ i : α, {r | (∑ j, r (i, j)) = (p i).toReal}) ∩
          ⋂ j : β, {r | (∑ i, r (i, j)) = (q j).toReal}) by
    ext r
    simp [realTransportPlans]]
  apply IsClosed.inter
  · exact isClosed_iInter fun edge =>
      isClosed_le continuous_const (continuous_apply edge)
  · apply IsClosed.inter
    · exact isClosed_iInter fun i => isClosed_eq
        (continuous_finsetSum _ fun j _ => continuous_apply (i, j)) continuous_const
    · exact isClosed_iInter fun j => isClosed_eq
        (continuous_finsetSum _ fun i _ => continuous_apply (i, j)) continuous_const

/-- The real finite transport polytope is compact. -/
theorem isCompact_realTransportPlans (p : PMF α) (q : PMF β) :
    IsCompact (realTransportPlans p q) :=
  (isCompact_stdSimplex ℝ (α × β)).of_isClosed_subset
    (isClosed_realTransportPlans p q)
    (realTransportPlans_subset_stdSimplex p q)

/-- Linear transport cost in real coordinates. -/
def realTransportCost (cost : α → β → NNReal)
    (r : (α × β) → ℝ) : ℝ :=
  ∑ i, ∑ j, r (i, j) * (cost i j : ℝ)

/-- Real-coordinate transport cost agrees with the finite ENNReal cost on a
feasible transport plan. -/
theorem realTransportCost_transportPlanToReal
    (cost : α → β → NNReal) {p : PMF α} {q : PMF β}
    {r : (α × β) → ENNReal} (hr : r ∈ transportPlans p q) :
    realTransportCost cost (transportPlanToReal r) =
      (transportCost cost r).toReal := by
  unfold realTransportCost transportPlanToReal transportCost
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [ENNReal.toReal_mul]
      simp
    · intro j hj
      exact ENNReal.mul_ne_top (transportPlan_apply_ne_top hr (i, j))
        ENNReal.coe_ne_top
  · intro i hi
    exact ENNReal.sum_ne_top.2 fun j hj =>
      ENNReal.mul_ne_top (transportPlan_apply_ne_top hr (i, j))
        ENNReal.coe_ne_top

/-- Converting a nonnegative real transport table to ENNReal preserves its
transport cost. -/
theorem transportCost_realTransportPlanToENNReal
    (cost : α → β → NNReal) {r : (α × β) → ℝ}
    (hr : ∀ edge, 0 ≤ r edge) :
    transportCost cost (realTransportPlanToENNReal r) =
      ENNReal.ofReal (realTransportCost cost r) := by
  unfold realTransportCost realTransportPlanToENNReal transportCost
  calc
    (∑ i, ∑ j, ENNReal.ofReal (r (i, j)) * (cost i j : ENNReal)) =
        ∑ i, ∑ j, ENNReal.ofReal (r (i, j) * (cost i j : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [ENNReal.ofReal_mul (hr (i, j))]
      simp
    _ = ENNReal.ofReal (∑ i, ∑ j, r (i, j) * (cost i j : ℝ)) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro j hj
        exact mul_nonneg (hr (i, j)) (NNReal.coe_nonneg _)
      · intro i hi
        exact Finset.sum_nonneg fun j hj =>
          mul_nonneg (hr (i, j)) (NNReal.coe_nonneg _)

/-- Quadratic mass concentration, used to select a sparse plan within the
optimal-cost face. -/
def realTransportConcentration (r : (α × β) → ℝ) : ℝ :=
  ∑ edge, (r edge) ^ 2

/-- A tangent direction preserving every row and column sum. -/
def IsBalancedTransportDirection (d : (α × β) → ℝ) : Prop :=
  (∀ i, ∑ j, d (i, j) = 0) ∧ ∀ j, ∑ i, d (i, j) = 0

/-- Algebraic form of a cycle in the positive support of a transport table:
there is a nonzero balanced direction whose absolute value fits inside every
entry.  Such a direction can be added or subtracted while preserving
feasibility. -/
def HasBalancedSupportCycle (r : (α × β) → ℝ) : Prop :=
  ∃ d : (α × β) → ℝ,
    IsBalancedTransportDirection d ∧ d ≠ 0 ∧ ∀ edge, |d edge| ≤ r edge

/-- A positive alternating cycle presented by finitely many distinct row and
column vertices and a fixed-point-free cyclic successor. -/
def HasPositiveFinAlternatingCycle (r : (α × β) → ℝ) : Prop :=
  ∃ n : ℕ, 0 < n ∧
    ∃ (rows : Fin n ↪ α) (cols : Fin n ↪ β) (next : Fin n ≃ Fin n),
      (∀ k, next k ≠ k) ∧
      (∀ k, 0 < r (rows k, cols k)) ∧
      ∀ k, 0 < r (rows (next k), cols k)

/-- Bipartite graph whose edges are exactly the strictly positive entries of
a real transport table. -/
def transportSupportGraph (r : (α × β) → ℝ) : SimpleGraph (α ⊕ β) where
  Adj u v :=
    match u, v with
    | .inl i, .inr j => 0 < r (i, j)
    | .inr j, .inl i => 0 < r (i, j)
    | .inl _, .inl _ | .inr _, .inr _ => False
  symm := ⟨by
    intro u v huv
    cases u <;> cases v <;> exact huv⟩
  loopless := ⟨by
    intro u huu
    cases u <;> exact huu⟩

omit [Fintype α] [Fintype β] in
@[simp]
theorem transportSupportGraph_adj_inl_inr
    (r : (α × β) → ℝ) (i : α) (j : β) :
    (transportSupportGraph r).Adj (.inl i) (.inr j) ↔ 0 < r (i, j) :=
  Iff.rfl

omit [Fintype α] [Fintype β] in
@[simp]
theorem transportSupportGraph_adj_inr_inl
    (r : (α × β) → ℝ) (j : β) (i : α) :
    (transportSupportGraph r).Adj (.inr j) (.inl i) ↔ 0 < r (i, j) :=
  Iff.rfl

omit [Fintype α] [Fintype β] in
@[simp]
theorem not_transportSupportGraph_adj_inl_inl
    (r : (α × β) → ℝ) (i i' : α) :
    ¬(transportSupportGraph r).Adj (.inl i) (.inl i') := by
  simp [transportSupportGraph]

omit [Fintype α] [Fintype β] in
@[simp]
theorem not_transportSupportGraph_adj_inr_inr
    (r : (α × β) → ℝ) (j j' : β) :
    ¬(transportSupportGraph r).Adj (.inr j) (.inr j') := by
  simp [transportSupportGraph]

omit [Fintype α] [Fintype β] in
/-- The positive-support graph is bipartite in the canonical left and right
copies of the row and column types. -/
theorem transportSupportGraph_isBipartiteWith (r : (α × β) → ℝ) :
    (transportSupportGraph r).IsBipartiteWith
      (Set.range Sum.inl) (Set.range Sum.inr) := by
  constructor
  · rw [Set.disjoint_left]
    intro v hvLeft hvRight
    obtain ⟨i, rfl⟩ := hvLeft
    simp at hvRight
  · intro u v huv
    cases u with
    | inl i =>
        cases v with
        | inl i' => simp at huv
        | inr j => exact Or.inl ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩
    | inr j =>
        cases v with
        | inl i => exact Or.inr ⟨⟨j, rfl⟩, ⟨i, rfl⟩⟩
        | inr j' => simp at huv

omit [Fintype α] [Fintype β] in
theorem transportSupportGraph_isBipartite (r : (α × β) → ℝ) :
    (transportSupportGraph r).IsBipartite :=
  SimpleGraph.isBipartite_iff_exists_isBipartiteWith.mpr
    ⟨Set.range Sum.inl, Set.range Sum.inr,
      transportSupportGraph_isBipartiteWith r⟩

/-- Canonical Boolean coloring of a transport support graph: rows and columns
receive opposite colors. -/
def transportSupportColoring (r : (α × β) → ℝ) :
    (transportSupportGraph r).Coloring Bool :=
  SimpleGraph.Coloring.mk (fun vertex => vertex.isRight) (by
    intro u v huv
    cases u <;> cases v <;> simp_all [transportSupportGraph])

omit [Fintype α] [Fintype β] in
@[simp]
theorem transportSupportColoring_inl
    (r : (α × β) → ℝ) (i : α) :
    transportSupportColoring r (.inl i) = false :=
  rfl

omit [Fintype α] [Fintype β] in
@[simp]
theorem transportSupportColoring_inr
    (r : (α × β) → ℝ) (j : β) :
    transportSupportColoring r (.inr j) = true :=
  rfl

omit [Fintype α] [Fintype β] in
/-- Every closed walk in the bipartite transport support graph has even
length. -/
theorem transportSupportGraph_walk_even
    (r : (α × β) → ℝ) {v : α ⊕ β}
    (walk : (transportSupportGraph r).Walk v v) :
    Even walk.length := by
  exact ((transportSupportColoring r).even_length_iff_congr walk).mpr Iff.rfl

omit [Fintype α] [Fintype β] in
/-- Along a support-graph walk starting at a row vertex, every even-indexed
vertex is again a row vertex. -/
theorem transportSupportGraph_getVert_even_isLeft
    (r : (α × β) → ℝ) {start : α} {finish : α ⊕ β}
    (walk : (transportSupportGraph r).Walk (.inl start) finish)
    {n : ℕ} (hn : n ≤ walk.length) (heven : Even n) :
    ∃ i : α, walk.getVert n = .inl i := by
  have hevenTake : Even (walk.take n).length := by
    rw [walk.take_length, Nat.min_eq_left hn]
    exact heven
  have hcolor :=
    ((transportSupportColoring r).even_length_iff_congr (walk.take n)).mp
      hevenTake
  cases hvertex : walk.getVert n with
  | inl i => exact ⟨i, rfl⟩
  | inr j =>
      exfalso
      rw [hvertex] at hcolor
      simp at hcolor

omit [Fintype α] [Fintype β] in
/-- Odd-indexed vertices of such a walk are column vertices. -/
theorem transportSupportGraph_getVert_odd_isRight
    (r : (α × β) → ℝ) {start : α} {finish : α ⊕ β}
    (walk : (transportSupportGraph r).Walk (.inl start) finish)
    {n : ℕ} (hn : n ≤ walk.length) (hodd : Odd n) :
    ∃ j : β, walk.getVert n = .inr j := by
  cases hvertex : walk.getVert n with
  | inr j => exact ⟨j, rfl⟩
  | inl i =>
      exfalso
      have hevenTake : Even (walk.take n).length :=
        ((transportSupportColoring r).even_length_iff_congr
          (walk.take n)).mpr (by rw [hvertex]; simp)
      have heven : Even n := by
        rw [walk.take_length, Nat.min_eq_left hn] at hevenTake
        exact hevenTake
      exact (Nat.not_even_iff_odd.mpr hodd) heven

omit [Fintype α] [Fintype β] in
/-- A support-graph cycle based at a row vertex admits row/column functions
indexed by half its (even) length.  The next lemma upgrades these functions to
embeddings and records their cyclic adjacency. -/
theorem exists_transportCycle_halfIndexFunctions
    (r : (α × β) → ℝ) {start : α}
    (cycle : (transportSupportGraph r).Walk (.inl start) (.inl start))
    (hcycle : cycle.IsCycle) :
    ∃ n : ℕ, 0 < n ∧ cycle.length = 2 * n ∧
      ∃ (rows : Fin n → α) (cols : Fin n → β),
        (∀ k, cycle.getVert (2 * k.1) = .inl (rows k)) ∧
        ∀ k, cycle.getVert (2 * k.1 + 1) = .inr (cols k) := by
  have heven := transportSupportGraph_walk_even r cycle
  obtain ⟨n, hn⟩ := heven
  have hlength : cycle.length = 2 * n := by omega
  have hnpos : 0 < n := by
    have := hcycle.three_le_length
    omega
  let rows : Fin n → α := fun k =>
    Classical.choose (transportSupportGraph_getVert_even_isLeft r cycle
      (n := 2 * k.1) (by omega) (by exact ⟨k.1, by omega⟩))
  let cols : Fin n → β := fun k =>
    Classical.choose (transportSupportGraph_getVert_odd_isRight r cycle
      (n := 2 * k.1 + 1) (by omega) (by exact ⟨k.1, by omega⟩))
  refine ⟨n, hnpos, hlength, rows, cols, ?_, ?_⟩
  · intro k
    exact Classical.choose_spec
      (transportSupportGraph_getVert_even_isLeft r cycle
        (n := 2 * k.1) (by omega) (by exact ⟨k.1, by omega⟩))
  · intro k
    exact Classical.choose_spec
      (transportSupportGraph_getVert_odd_isRight r cycle
        (n := 2 * k.1 + 1) (by omega) (by exact ⟨k.1, by omega⟩))

omit [Fintype α] [Fintype β] in
/-- The half-cycle row and column enumerations are injective because a simple
cycle has no repeated vertex before its endpoint. -/
theorem exists_transportCycle_halfIndexEmbeddings
    (r : (α × β) → ℝ) {start : α}
    (cycle : (transportSupportGraph r).Walk (.inl start) (.inl start))
    (hcycle : cycle.IsCycle) :
    ∃ n : ℕ, 0 < n ∧ cycle.length = 2 * n ∧
      ∃ (rows : Fin n ↪ α) (cols : Fin n ↪ β),
        (∀ k, cycle.getVert (2 * k.1) = .inl (rows k)) ∧
        ∀ k, cycle.getVert (2 * k.1 + 1) = .inr (cols k) := by
  obtain ⟨n, hn, hlength, rows, cols, hrows, hcols⟩ :=
    exists_transportCycle_halfIndexFunctions r cycle hcycle
  have hrowsInjective : Function.Injective rows := by
    intro k l hkl
    have hverts : cycle.getVert (2 * k.1) = cycle.getVert (2 * l.1) := by
      rw [hrows k, hrows l, hkl]
    have hindices := hcycle.getVert_injOn'
      (show 2 * k.1 ≤ cycle.length - 1 by omega)
      (show 2 * l.1 ≤ cycle.length - 1 by omega) hverts
    apply Fin.ext
    omega
  have hcolsInjective : Function.Injective cols := by
    intro k l hkl
    have hverts : cycle.getVert (2 * k.1 + 1) =
        cycle.getVert (2 * l.1 + 1) := by
      rw [hcols k, hcols l, hkl]
    have hindices := hcycle.getVert_injOn'
      (show 2 * k.1 + 1 ≤ cycle.length - 1 by omega)
      (show 2 * l.1 + 1 ≤ cycle.length - 1 by omega) hverts
    apply Fin.ext
    omega
  exact ⟨n, hn, hlength, ⟨rows, hrowsInjective⟩,
    ⟨cols, hcolsInjective⟩, hrows, hcols⟩

omit [Fintype α] [Fintype β] in
/-- A support-graph cycle based at a row vertex gives the positive finite
alternating-cycle presentation used by the transport perturbation proof. -/
theorem hasPositiveFinAlternatingCycle_of_cycle_from_inl
    (r : (α × β) → ℝ) {start : α}
    (cycle : (transportSupportGraph r).Walk (.inl start) (.inl start))
    (hcycle : cycle.IsCycle) :
    HasPositiveFinAlternatingCycle r := by
  obtain ⟨n, hn, hlength, rows, cols, hrows, hcols⟩ :=
    exists_transportCycle_halfIndexEmbeddings r cycle hcycle
  have hnTwo : 2 ≤ n := by
    have := hcycle.three_le_length
    omega
  letI : NeZero n := ⟨hn.ne'⟩
  let next : Fin n ≃ Fin n := finRotate n
  have hnext : ∀ k, next k ≠ k := by
    intro k hk
    have hsupport : k ∈ (finRotate n).support := by
      rw [support_finRotate_of_le hnTwo]
      exact Finset.mem_univ k
    have hne := Equiv.Perm.mem_support.mp hsupport
    exact hne (by simpa [next] using hk)
  have hplus : ∀ k, 0 < r (rows k, cols k) := by
    intro k
    have hadj := cycle.adj_getVert_succ
      (show 2 * k.1 < cycle.length by omega)
    rw [hrows k, hcols k] at hadj
    exact hadj
  have hminus : ∀ k, 0 < r (rows (next k), cols k) := by
    intro k
    let last : Fin n := ⟨n - 1, by omega⟩
    by_cases hlast : k = last
    · subst k
      have hnextZero : next last = 0 := by
        rw [show next last = last + 1 by simp [next, finRotate_apply]]
        apply Fin.ext
        simp only [Fin.add_def, last, Fin.val_mk, Fin.val_zero]
        norm_num
        rw [show n - 1 + 1 = n by omega, Nat.mod_self]
      have hindex : 2 * last.1 + 1 = cycle.length - 1 := by
        simp only [last]
        omega
      have hadj := cycle.adj_getVert_succ
        (i := cycle.length - 1) (by omega)
      have hcolLast : cycle.getVert (cycle.length - 1) =
          .inr (cols last) := by
        rw [← hindex]
        exact hcols _
      have hrowZero : cycle.getVert cycle.length = .inl (rows 0) := by
        rw [cycle.getVert_length, ← cycle.getVert_zero]
        exact hrows 0
      have hsucc : cycle.length - 1 + 1 = cycle.length := by omega
      rw [hsucc] at hadj
      rw [hcolLast, hrowZero] at hadj
      rw [hnextZero]
      exact hadj
    · have hklt : k.1 + 1 < n := by
        by_contra h
        have hkval : k.1 = n - 1 := by omega
        apply hlast
        apply Fin.ext
        simpa [last] using hkval
      have hnextVal : (next k).1 = k.1 + 1 := by
        rw [show next k = k + 1 by simp [next, finRotate_apply]]
        exact Fin.val_add_one_of_lt' hklt
      have hadj := cycle.adj_getVert_succ
        (i := 2 * k.1 + 1) (by omega)
      have hrowNext : cycle.getVert (2 * k.1 + 2) =
          .inl (rows (next k)) := by
        have hidx : 2 * k.1 + 2 = 2 * (next k).1 := by omega
        rw [hidx]
        exact hrows (next k)
      rw [hcols k, hrowNext] at hadj
      exact hadj
  exact ⟨n, hn, rows, cols, next, hnext, hplus, hminus⟩

/-- Transpose a real transport table. -/
def transposeTransportTable (r : (α × β) → ℝ) : (β × α) → ℝ :=
  fun edge => r (edge.2, edge.1)

/-- Swapping the two vertex copies maps a support graph to the support graph
of the transposed table. -/
def transportSupportSwapHom (r : (α × β) → ℝ) :
    transportSupportGraph r →g
      transportSupportGraph (transposeTransportTable r) where
  toFun := Sum.swap
  map_rel' := by
    intro u v huv
    cases u <;> cases v <;> exact huv

omit [Fintype α] [Fintype β] in
/-- Every cycle in a transport support graph, irrespective of which side its
base vertex lies on, yields a positive finite alternating-cycle
presentation. -/
theorem hasPositiveFinAlternatingCycle_of_cycle
    (r : (α × β) → ℝ) {vertex : α ⊕ β}
    (cycle : (transportSupportGraph r).Walk vertex vertex)
    (hcycle : cycle.IsCycle) :
    HasPositiveFinAlternatingCycle r := by
  cases vertex with
  | inl start =>
      exact hasPositiveFinAlternatingCycle_of_cycle_from_inl r cycle hcycle
  | inr start =>
      let swapped := cycle.map (transportSupportSwapHom r)
      have hswapped : swapped.IsCycle :=
        hcycle.map (Equiv.sumComm α β).injective
      have htranspose :
          HasPositiveFinAlternatingCycle (transposeTransportTable r) :=
        hasPositiveFinAlternatingCycle_of_cycle_from_inl
          (transposeTransportTable r) swapped hswapped
      obtain ⟨n, hn, rowsT, colsT, next, hnext, hplusT, hminusT⟩ := htranspose
      let rows : Fin n ↪ α :=
        ⟨fun k => colsT (next.symm k),
          colsT.injective.comp next.symm.injective⟩
      let cols : Fin n ↪ β := rowsT
      refine ⟨n, hn, rows, cols, next, hnext, ?_, ?_⟩
      · intro k
        change 0 < r (colsT (next.symm k), rowsT k)
        simpa [transposeTransportTable] using hminusT (next.symm k)
      · intro k
        simpa [rows, cols, transposeTransportTable] using hplusT k

omit [Fintype α] [Fintype β] in
/-- Absence of a positive alternating-cycle presentation is equivalent to the
needed graph-theoretic direction: the positive-support graph is acyclic. -/
theorem transportSupportGraph_isAcyclic_of_not_hasPositiveFinAlternatingCycle
    {r : (α × β) → ℝ} (hcycle : ¬HasPositiveFinAlternatingCycle r) :
    (transportSupportGraph r).IsAcyclic := by
  intro vertex cycle hisCycle
  exact hcycle (hasPositiveFinAlternatingCycle_of_cycle r cycle hisCycle)

/-- Signed direction associated with an alternating cycle presentation.  The
positive edges are `(rows k, cols k)` and the negative edges are
`(rows (next k), cols k)`. -/
noncomputable def alternatingCycleDirection
    {κ : Type*} [Fintype κ]
    (rows : κ → α) (cols : κ → β) (next : κ ≃ κ) (δ : ℝ) :
    (α × β) → ℝ := by
  classical
  exact fun edge =>
    (∑ k, if edge = (rows k, cols k) then δ else 0) -
      ∑ k, if edge = (rows (next k), cols k) then δ else 0

/-- Alternating cycle directions preserve every row and column sum. -/
theorem alternatingCycleDirection_isBalanced
    {κ : Type*} [Fintype κ]
    (rows : κ → α) (cols : κ → β) (next : κ ≃ κ) (δ : ℝ) :
    IsBalancedTransportDirection
      (alternatingCycleDirection rows cols next δ) := by
  classical
  constructor
  · intro i
    unfold alternatingCycleDirection
    simp only [Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
    simp only [Prod.mk.injEq, Finset.sum_ite_irrel, Finset.sum_const_zero,
      ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact sub_eq_zero.mpr (next.sum_comp
      (fun k => if i = rows k then δ else 0)).symm
  · intro j
    unfold alternatingCycleDirection
    simp only [Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
    simp only [Prod.mk.injEq, ite_and, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp

omit [Fintype α] [Fintype β] in
/-- A genuine finite alternating cycle with nonzero amplitude gives a
nonzero direction. Injectivity keeps positive and negative cycle edges from
colliding. -/
theorem alternatingCycleDirection_ne_zero
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (rows : κ ↪ α) (cols : κ ↪ β) (next : κ ≃ κ)
    (hnext : ∀ k, next k ≠ k) {δ : ℝ} (hδ : δ ≠ 0) :
    alternatingCycleDirection rows cols next δ ≠ 0 := by
  classical
  intro hdirection
  let k₀ : κ := Classical.arbitrary κ
  have hatom := congrFun hdirection (rows k₀, cols k₀)
  simp only [alternatingCycleDirection, Pi.zero_apply] at hatom
  have hpositive :
      (∑ k, if (rows k₀, cols k₀) = (rows k, cols k) then δ else 0) = δ := by
    simp [Prod.ext_iff, rows.injective.eq_iff, cols.injective.eq_iff]
  have hnegative :
      (∑ k, if (rows k₀, cols k₀) = (rows (next k), cols k) then δ else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [if_neg]
    intro hedge
    have hcol : k₀ = k := cols.injective (congrArg Prod.snd hedge)
    subst k
    exact hnext k₀ (rows.injective (congrArg Prod.fst hedge).symm)
  rw [hpositive, hnegative, sub_zero] at hatom
  exact hδ hatom

/-- Positive mass on all edges of an explicit alternating cycle produces an
algebraic balanced support cycle. -/
theorem hasBalancedSupportCycle_of_alternatingCycle
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (r : (α × β) → ℝ) (rows : κ ↪ α) (cols : κ ↪ β)
    (next : κ ≃ κ) (hnext : ∀ k, next k ≠ k)
    (hr : ∀ edge, 0 ≤ r edge) {δ : ℝ} (hδ : 0 < δ)
    (hplus : ∀ k, δ ≤ r (rows k, cols k))
    (hminus : ∀ k, δ ≤ r (rows (next k), cols k)) :
    HasBalancedSupportCycle r := by
  classical
  let d := alternatingCycleDirection rows cols next δ
  refine ⟨d, alternatingCycleDirection_isBalanced rows cols next δ,
    alternatingCycleDirection_ne_zero rows cols next hnext hδ.ne', ?_⟩
  intro edge
  by_cases hpos : ∃ k, edge = (rows k, cols k)
  · obtain ⟨k₀, rfl⟩ := hpos
    have hpositive :
        (∑ k, if (rows k₀, cols k₀) = (rows k, cols k) then δ else 0) = δ := by
      simp [Prod.ext_iff, rows.injective.eq_iff, cols.injective.eq_iff]
    have hnegative :
        (∑ k, if (rows k₀, cols k₀) =
          (rows (next k), cols k) then δ else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [if_neg]
      intro hedge
      have hcol : k₀ = k := cols.injective (congrArg Prod.snd hedge)
      subst k
      exact hnext k₀ (rows.injective (congrArg Prod.fst hedge).symm)
    simp only [d, alternatingCycleDirection, hpositive, hnegative, sub_zero,
      abs_of_pos hδ]
    exact hplus k₀
  · by_cases hneg : ∃ k, edge = (rows (next k), cols k)
    · obtain ⟨k₀, rfl⟩ := hneg
      have hpositive :
          (∑ k, if (rows (next k₀), cols k₀) =
            (rows k, cols k) then δ else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [if_neg]
        intro hedge
        have hcol : k₀ = k := cols.injective (congrArg Prod.snd hedge)
        subst k
        exact hnext k₀ (rows.injective (congrArg Prod.fst hedge))
      have hnegative :
          (∑ k, if (rows (next k₀), cols k₀) =
            (rows (next k), cols k) then δ else 0) = δ := by
        simp [Prod.ext_iff, rows.injective.eq_iff, cols.injective.eq_iff]
      simp only [d, alternatingCycleDirection, hpositive, hnegative,
        zero_sub, abs_neg, abs_of_pos hδ]
      exact hminus k₀
    · have hpositive :
          (∑ k, if edge = (rows k, cols k) then δ else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [if_neg]
        exact fun hedge => hpos ⟨k, hedge⟩
      have hnegative :
          (∑ k, if edge = (rows (next k), cols k) then δ else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [if_neg]
        exact fun hedge => hneg ⟨k, hedge⟩
      simpa [d, alternatingCycleDirection, hpositive, hnegative] using hr edge

/-- Strict positivity on the finitely many edges of an alternating cycle is
enough: their minimum supplies a common positive perturbation amplitude. -/
theorem hasBalancedSupportCycle_of_positive_alternatingCycle
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (r : (α × β) → ℝ) (rows : κ ↪ α) (cols : κ ↪ β)
    (next : κ ≃ κ) (hnext : ∀ k, next k ≠ k)
    (hr : ∀ edge, 0 ≤ r edge)
    (hplus : ∀ k, 0 < r (rows k, cols k))
    (hminus : ∀ k, 0 < r (rows (next k), cols k)) :
    HasBalancedSupportCycle r := by
  classical
  let weight : κ ⊕ κ → ℝ
    | .inl k => r (rows k, cols k)
    | .inr k => r (rows (next k), cols k)
  obtain ⟨index, hindex, hmin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (κ ⊕ κ)) weight
      Finset.univ_nonempty
  let δ := weight index
  have hδ : 0 < δ := by
    cases index with
    | inl k => exact hplus k
    | inr k => exact hminus k
  apply hasBalancedSupportCycle_of_alternatingCycle
    r rows cols next hnext hr hδ
  · intro k
    exact hmin (.inl k) (Finset.mem_univ _)
  · intro k
    exact hmin (.inr k) (Finset.mem_univ _)

/-- A positive finite alternating-cycle presentation implies the algebraic
support-cycle condition. -/
theorem HasPositiveFinAlternatingCycle.hasBalancedSupportCycle
    {r : (α × β) → ℝ} (hr : ∀ edge, 0 ≤ r edge)
    (hcycle : HasPositiveFinAlternatingCycle r) :
    HasBalancedSupportCycle r := by
  obtain ⟨n, hn, rows, cols, next, hnext, hplus, hminus⟩ := hcycle
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  exact hasBalancedSupportCycle_of_positive_alternatingCycle
    r rows cols next hnext hr hplus hminus

theorem continuous_realTransportCost (cost : α → β → NNReal) :
    Continuous (realTransportCost cost) := by
  unfold realTransportCost
  fun_prop

theorem continuous_realTransportConcentration :
    Continuous (realTransportConcentration : ((α × β) → ℝ) → ℝ) := by
  unfold realTransportConcentration
  fun_prop

/-- Adding a balanced direction preserves the marginal equations whenever
the resulting table remains nonnegative. -/
theorem add_mem_realTransportPlans_of_balanced
    {p : PMF α} {q : PMF β} {r d : (α × β) → ℝ}
    (hr : r ∈ realTransportPlans p q)
    (hd : IsBalancedTransportDirection d)
    (hnonneg : ∀ edge, 0 ≤ r edge + d edge) :
    r + d ∈ realTransportPlans p q := by
  refine ⟨fun edge => by simpa using hnonneg edge, ?_, ?_⟩
  · intro i
    simp only [Pi.add_apply, Finset.sum_add_distrib, hr.2.1 i, hd.1 i, add_zero]
  · intro j
    simp only [Pi.add_apply, Finset.sum_add_distrib, hr.2.2 j, hd.2 j, add_zero]

/-- Subtracting a balanced direction also preserves the marginal equations
whenever the resulting table remains nonnegative. -/
theorem sub_mem_realTransportPlans_of_balanced
    {p : PMF α} {q : PMF β} {r d : (α × β) → ℝ}
    (hr : r ∈ realTransportPlans p q)
    (hd : IsBalancedTransportDirection d)
    (hnonneg : ∀ edge, 0 ≤ r edge - d edge) :
    r - d ∈ realTransportPlans p q := by
  have hneg : IsBalancedTransportDirection (-d) := by
    constructor
    · intro i
      simp only [Pi.neg_apply, Finset.sum_neg_distrib, hd.1 i, neg_zero]
    · intro j
      simp only [Pi.neg_apply, Finset.sum_neg_distrib, hd.2 j, neg_zero]
  simpa only [sub_eq_add_neg] using
    add_mem_realTransportPlans_of_balanced hr hneg hnonneg

/-- An algebraic support cycle gives feasible perturbations in both
directions. -/
theorem HasBalancedSupportCycle.two_sided_feasible
    {p : PMF α} {q : PMF β} {r : (α × β) → ℝ}
    (hr : r ∈ realTransportPlans p q)
    (hcycle : HasBalancedSupportCycle r) :
    ∃ d : (α × β) → ℝ, d ≠ 0 ∧
      r + d ∈ realTransportPlans p q ∧
      r - d ∈ realTransportPlans p q := by
  obtain ⟨d, hbalanced, hd, hbound⟩ := hcycle
  refine ⟨d, hd,
    add_mem_realTransportPlans_of_balanced hr hbalanced ?_,
    sub_mem_realTransportPlans_of_balanced hr hbalanced ?_⟩
  · intro edge
    have hlower := neg_le_of_abs_le (hbound edge)
    linarith
  · intro edge
    have hupper := (le_abs_self (d edge)).trans (hbound edge)
    linarith

theorem realTransportCost_add (cost : α → β → NNReal)
    (r d : (α × β) → ℝ) :
    realTransportCost cost (r + d) =
      realTransportCost cost r + realTransportCost cost d := by
  unfold realTransportCost
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem realTransportCost_sub (cost : α → β → NNReal)
    (r d : (α × β) → ℝ) :
    realTransportCost cost (r - d) =
      realTransportCost cost r - realTransportCost cost d := by
  unfold realTransportCost
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- The parallelogram identity for the quadratic tie-breaker. -/
theorem realTransportConcentration_add_add_sub
    (r d : (α × β) → ℝ) :
    realTransportConcentration (r + d) +
        realTransportConcentration (r - d) =
      2 * realTransportConcentration r +
        2 * realTransportConcentration d := by
  unfold realTransportConcentration
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro edge hedge
  ring

/-- The quadratic concentration of a nonzero finite direction is positive. -/
theorem realTransportConcentration_pos {d : (α × β) → ℝ} (hd : d ≠ 0) :
    0 < realTransportConcentration d := by
  obtain ⟨edge, hedge⟩ := Function.ne_iff.mp hd
  unfold realTransportConcentration
  exact Finset.sum_pos' (fun edge _ => sq_nonneg (d edge))
    ⟨edge, by simpa using sq_pos_of_ne_zero hedge⟩

/-- A finite real transport problem has an attained minimum. -/
theorem exists_realTransportCost_minimizer
    (p : PMF α) (q : PMF β) (cost : α → β → NNReal) :
    ∃ r ∈ realTransportPlans p q,
      ∀ s ∈ realTransportPlans p q,
        realTransportCost cost r ≤ realTransportCost cost s := by
  obtain ⟨r, hr, hmin⟩ :=
    (isCompact_realTransportPlans p q).exists_isMinOn
      (realTransportPlans_nonempty p q)
      (continuous_realTransportCost cost).continuousOn
  exact ⟨r, hr, hmin⟩

/-- Among all minimum-cost plans there is one maximizing the sum of squared
entries.  Alternating cycle perturbations will contradict this maximality and
therefore force its positive support to be acyclic. -/
theorem exists_minimal_realTransportCost_maximal_concentration
    (p : PMF α) (q : PMF β) (cost : α → β → NNReal) :
    ∃ r ∈ realTransportPlans p q,
      (∀ s ∈ realTransportPlans p q,
        realTransportCost cost r ≤ realTransportCost cost s) ∧
      ∀ s ∈ realTransportPlans p q,
        realTransportCost cost s = realTransportCost cost r →
        realTransportConcentration s ≤ realTransportConcentration r := by
  obtain ⟨r₀, hr₀, hmin₀⟩ := exists_realTransportCost_minimizer p q cost
  let optimal : Set ((α × β) → ℝ) :=
    {r | r ∈ realTransportPlans p q ∧
      realTransportCost cost r = realTransportCost cost r₀}
  have hoptimalCompact : IsCompact optimal := by
    apply (isCompact_realTransportPlans p q).of_isClosed_subset
    · exact (isClosed_realTransportPlans p q).inter
        (isClosed_eq (continuous_realTransportCost cost) continuous_const)
    · exact fun _ h => h.1
  have hoptimalNonempty : optimal.Nonempty := ⟨r₀, hr₀, rfl⟩
  obtain ⟨r, hr, hmax⟩ := hoptimalCompact.exists_isMaxOn hoptimalNonempty
    continuous_realTransportConcentration.continuousOn
  refine ⟨r, hr.1, ?_, ?_⟩
  · intro s hs
    rw [hr.2]
    exact hmin₀ s hs
  · intro s hs hcost
    apply hmax
    exact ⟨hs, hcost.trans hr.2⟩

/-- There is an optimal plan with no nonzero two-sided feasible perturbation.
Optimality first forces any such direction to be cost-neutral, and the
quadratic tie-breaker then forces it to vanish.  This is the algebraic
extremality property used to exclude alternating cycles in positive support. -/
theorem exists_realTransportCost_minimizer_rigid
    (p : PMF α) (q : PMF β) (cost : α → β → NNReal) :
    ∃ r ∈ realTransportPlans p q,
      (∀ s ∈ realTransportPlans p q,
        realTransportCost cost r ≤ realTransportCost cost s) ∧
      ∀ d : (α × β) → ℝ,
        r + d ∈ realTransportPlans p q →
        r - d ∈ realTransportPlans p q →
        d = 0 := by
  obtain ⟨r, hr, hmin, hmax⟩ :=
    exists_minimal_realTransportCost_maximal_concentration p q cost
  refine ⟨r, hr, hmin, ?_⟩
  intro d hadd hsub
  have haddMin := hmin (r + d) hadd
  have hsubMin := hmin (r - d) hsub
  rw [realTransportCost_add] at haddMin
  rw [realTransportCost_sub] at hsubMin
  have hcost : realTransportCost cost d = 0 := by linarith
  by_contra hd
  have haddCost : realTransportCost cost (r + d) = realTransportCost cost r := by
    rw [realTransportCost_add, hcost, add_zero]
  have hsubCost : realTransportCost cost (r - d) = realTransportCost cost r := by
    rw [realTransportCost_sub, hcost, sub_zero]
  have haddMax := hmax (r + d) hadd haddCost
  have hsubMax := hmax (r - d) hsub hsubCost
  have hpositive := realTransportConcentration_pos hd
  have hparallelogram := realTransportConcentration_add_add_sub r d
  linarith

/-- Every finite transport problem has an optimal real plan with no
algebraic cycle in its positive support. -/
theorem exists_realTransportCost_minimizer_without_balanced_support_cycle
    (p : PMF α) (q : PMF β) (cost : α → β → NNReal) :
    ∃ r ∈ realTransportPlans p q,
      (∀ s ∈ realTransportPlans p q,
        realTransportCost cost r ≤ realTransportCost cost s) ∧
      ¬ HasBalancedSupportCycle r := by
  obtain ⟨r, hr, hmin, hrigid⟩ :=
    exists_realTransportCost_minimizer_rigid p q cost
  refine ⟨r, hr, hmin, ?_⟩
  intro hcycle
  obtain ⟨d, hd, hadd, hsub⟩ := hcycle.two_sided_feasible hr
  exact hd (hrigid d hadd hsub)

/-- Consequently, every finite transport problem has an optimal plan with no
positive finite alternating-cycle presentation. -/
theorem exists_realTransportCost_minimizer_without_positive_alternating_cycle
    (p : PMF α) (q : PMF β) (cost : α → β → NNReal) :
    ∃ r ∈ realTransportPlans p q,
      (∀ s ∈ realTransportPlans p q,
        realTransportCost cost r ≤ realTransportCost cost s) ∧
      ¬ HasPositiveFinAlternatingCycle r := by
  obtain ⟨r, hr, hmin, hnobalanced⟩ :=
    exists_realTransportCost_minimizer_without_balanced_support_cycle p q cost
  refine ⟨r, hr, hmin, ?_⟩
  intro halternating
  exact hnobalanced (halternating.hasBalancedSupportCycle hr.1)

/-- Every finite real transport problem therefore has an optimal plan whose
positive-support bipartite graph is acyclic. -/
theorem exists_realTransportCost_minimizer_support_acyclic
    (p : PMF α) (q : PMF β) (cost : α → β → NNReal) :
    ∃ r ∈ realTransportPlans p q,
      (∀ s ∈ realTransportPlans p q,
        realTransportCost cost r ≤ realTransportCost cost s) ∧
      (transportSupportGraph r).IsAcyclic := by
  obtain ⟨r, hr, hmin, hncycle⟩ :=
    exists_realTransportCost_minimizer_without_positive_alternating_cycle
      p q cost
  exact ⟨r, hr, hmin,
    transportSupportGraph_isAcyclic_of_not_hasPositiveFinAlternatingCycle
      hncycle⟩

end Mcmc.Finite
