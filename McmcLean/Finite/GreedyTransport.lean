import McmcLean.Finite.MeasurableSelection
import McmcLean.Finite.Transport

/-!
# Greedy finite transport candidates

An edge order generates a transport candidate by repeatedly assigning the
minimum of the remaining row and column mass to the next edge.  This module
first establishes the parameterized measurability needed for finite
tie-breaking.  Feasibility for complete edge orders and completeness of the
candidate family for transport-polytope vertices are developed separately.
-/

open scoped ENNReal

namespace McmcLean.Finite

variable {α β Ω : Type*} [DecidableEq α] [DecidableEq β]

/-- Remaining row masses, remaining column masses, and mass allocated so far. -/
abbrev GreedyTransportState (α β : Type*) :=
  (α → ENNReal) × (β → ENNReal) × ((α × β) → ENNReal)

/-- The amount assigned at an edge is the smaller remaining marginal mass. -/
def greedyTransportAllocation
    (state : GreedyTransportState α β) (edge : α × β) : ENNReal :=
  min (state.1 edge.1) (state.2.1 edge.2)

/-- Process one edge of a greedy finite transport construction. -/
noncomputable def greedyTransportStep
    (state : GreedyTransportState α β) (edge : α × β) :
    GreedyTransportState α β :=
  let amount := greedyTransportAllocation state edge
  (Function.update state.1 edge.1 (state.1 edge.1 - amount),
    Function.update state.2.1 edge.2 (state.2.1 edge.2 - amount),
    Function.update state.2.2 edge (state.2.2 edge + amount))

/-- Initial greedy state for two finite mass functions. -/
def initialGreedyTransportState (p : α → ENNReal) (q : β → ENNReal) :
    GreedyTransportState α β :=
  (p, q, 0)

/-- State after processing an ordered list of transport edges. -/
noncomputable def greedyTransportState
    (p : α → ENNReal) (q : β → ENNReal) (order : List (α × β)) :
    GreedyTransportState α β :=
  order.foldl greedyTransportStep (initialGreedyTransportState p q)

/-- Joint mass allocated by an ordered greedy transport pass. -/
noncomputable def greedyTransportMass
    (p : α → ENNReal) (q : β → ENNReal) (order : List (α × β)) :
    (α × β) → ENNReal :=
  (greedyTransportState p q order).2.2

@[simp]
theorem greedyTransportState_nil (p : α → ENNReal) (q : β → ENNReal) :
    greedyTransportState p q [] = initialGreedyTransportState p q :=
  rfl

@[simp]
theorem greedyTransportState_append_singleton
    (p : α → ENNReal) (q : β → ENNReal)
    (order : List (α × β)) (edge : α × β) :
    greedyTransportState p q (order ++ [edge]) =
      greedyTransportStep (greedyTransportState p q order) edge := by
  simp [greedyTransportState]

/-- Coordinatewise measurability of a greedy state is preserved by one fixed
edge update. -/
theorem measurable_greedyTransportStep_coordinates
    [MeasurableSpace Ω]
    (state : Ω → GreedyTransportState α β)
    (hrow : ∀ i, Measurable fun ω => (state ω).1 i)
    (hcol : ∀ j, Measurable fun ω => (state ω).2.1 j)
    (hmass : ∀ edge, Measurable fun ω => (state ω).2.2 edge)
    (edge : α × β) :
    (∀ i, Measurable fun ω =>
        (greedyTransportStep (state ω) edge).1 i) ∧
      (∀ j, Measurable fun ω =>
        (greedyTransportStep (state ω) edge).2.1 j) ∧
      (∀ selected, Measurable fun ω =>
        (greedyTransportStep (state ω) edge).2.2 selected) := by
  have hamount : Measurable fun ω =>
      greedyTransportAllocation (state ω) edge :=
    (hrow edge.1).min (hcol edge.2)
  constructor
  · intro i
    unfold greedyTransportStep
    by_cases hi : i = edge.1
    · subst i
      simp only [Function.update_self]
      convert (hrow edge.1).sub hamount using 1
      funext ω
      rfl
    · simpa only [Function.update_of_ne hi] using hrow i
  constructor
  · intro j
    unfold greedyTransportStep
    by_cases hj : j = edge.2
    · subst j
      simp only [Function.update_self]
      convert (hcol edge.2).sub hamount using 1
      funext ω
      rfl
    · simpa only [Function.update_of_ne hj] using hcol j
  · intro selected
    unfold greedyTransportStep
    by_cases hs : selected = edge
    · subst selected
      simp only [Function.update_self]
      convert (hmass edge).add hamount using 1
      funext ω
      rfl
    · simpa only [Function.update_of_ne hs] using hmass selected

/-- Every coordinate of a parameterized greedy state is measurable whenever
the input marginal coordinates are measurable. -/
theorem measurable_greedyTransportState_coordinates
    [MeasurableSpace Ω]
    (p : Ω → α → ENNReal) (q : Ω → β → ENNReal)
    (hp : ∀ i, Measurable fun ω => p ω i)
    (hq : ∀ j, Measurable fun ω => q ω j) :
    ∀ order : List (α × β),
      (∀ i, Measurable fun ω =>
          (greedyTransportState (p ω) (q ω) order).1 i) ∧
        (∀ j, Measurable fun ω =>
          (greedyTransportState (p ω) (q ω) order).2.1 j) ∧
        (∀ edge, Measurable fun ω =>
          (greedyTransportState (p ω) (q ω) order).2.2 edge) := by
  intro order
  induction order using List.reverseRecOn with
  | nil =>
      simp only [greedyTransportState_nil, initialGreedyTransportState]
      exact ⟨hp, hq, fun _ => measurable_const⟩
  | append_singleton order edge ih =>
      simp only [greedyTransportState, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
      exact measurable_greedyTransportStep_coordinates
        (fun ω => greedyTransportState (p ω) (q ω) order)
        ih.1 ih.2.1 ih.2.2 edge

/-- In particular, every allocated atom of a greedy transport candidate is
measurable in the parameter. -/
theorem measurable_greedyTransportMass_apply
    [MeasurableSpace Ω]
    (p : Ω → α → ENNReal) (q : Ω → β → ENNReal)
    (hp : ∀ i, Measurable fun ω => p ω i)
    (hq : ∀ j, Measurable fun ω => q ω j)
    (order : List (α × β)) (edge : α × β) :
    Measurable fun ω => greedyTransportMass (p ω) (q ω) order edge := by
  exact (measurable_greedyTransportState_coordinates p q hp hq order).2.2 edge

/-- Processing an edge adds exactly its allocation to the corresponding row
of the accumulated mass and leaves all other row sums unchanged. -/
theorem sum_greedyTransportStep_mass_row
    [Fintype β] (state : GreedyTransportState α β)
    (edge : α × β) (i : α) :
    (∑ j, (greedyTransportStep state edge).2.2 (i, j)) =
      (∑ j, state.2.2 (i, j)) +
        if i = edge.1 then greedyTransportAllocation state edge else 0 := by
  classical
  by_cases hi : i = edge.1
  · subst i
    simp only [if_true]
    let f : β → ENNReal := fun j => state.2.2 (edge.1, j)
    let amount := greedyTransportAllocation state edge
    have hfun :
        (fun j => (greedyTransportStep state edge).2.2 (edge.1, j)) =
          Function.update f edge.2 (f edge.2 + amount) := by
      funext j
      unfold greedyTransportStep f amount
      by_cases hj : j = edge.2
      · subst j
        simp only [Function.update_self]
      · rw [Function.update_of_ne]
        · exact Function.update_of_ne
            (fun h => hj (congrArg Prod.snd h)) _ _
        · exact hj
    rw [hfun]
    rw [show (∑ j, Function.update f edge.2 (f edge.2 + amount) j) =
        f edge.2 + amount + ∑ j ∈ Finset.univ \ {edge.2}, f j by
      exact Finset.sum_update_of_mem (Finset.mem_univ edge.2) f _]
    change f edge.2 + amount + ∑ j ∈ Finset.univ \ {edge.2}, f j =
      (∑ j, f j) + amount
    rw [Finset.sdiff_singleton_eq_erase,
      ← Finset.sum_erase_add _ f (Finset.mem_univ edge.2)]
    ac_rfl
  · simp only [hi, if_false]
    rw [add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    unfold greedyTransportStep
    exact Function.update_of_ne (fun h => hi (congrArg Prod.fst h)) _ _

/-- Processing an edge adds exactly its allocation to the corresponding
column of the accumulated mass and leaves all other column sums unchanged. -/
theorem sum_greedyTransportStep_mass_col
    [Fintype α] (state : GreedyTransportState α β)
    (edge : α × β) (j : β) :
    (∑ i, (greedyTransportStep state edge).2.2 (i, j)) =
      (∑ i, state.2.2 (i, j)) +
        if j = edge.2 then greedyTransportAllocation state edge else 0 := by
  classical
  by_cases hj : j = edge.2
  · subst j
    simp only [if_true]
    let f : α → ENNReal := fun i => state.2.2 (i, edge.2)
    let amount := greedyTransportAllocation state edge
    have hfun :
        (fun i => (greedyTransportStep state edge).2.2 (i, edge.2)) =
          Function.update f edge.1 (f edge.1 + amount) := by
      funext i
      unfold greedyTransportStep f amount
      by_cases hi : i = edge.1
      · subst i
        simp only [Function.update_self]
      · rw [Function.update_of_ne]
        · exact Function.update_of_ne
            (fun h => hi (congrArg Prod.fst h)) _ _
        · exact hi
    rw [hfun]
    rw [show (∑ i, Function.update f edge.1 (f edge.1 + amount) i) =
        f edge.1 + amount + ∑ i ∈ Finset.univ \ {edge.1}, f i by
      exact Finset.sum_update_of_mem (Finset.mem_univ edge.1) f _]
    change f edge.1 + amount + ∑ i ∈ Finset.univ \ {edge.1}, f i =
      (∑ i, f i) + amount
    rw [Finset.sdiff_singleton_eq_erase,
      ← Finset.sum_erase_add _ f (Finset.mem_univ edge.1)]
    ac_rfl
  · simp only [hj, if_false]
    rw [add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    unfold greedyTransportStep
    exact Function.update_of_ne (fun h => hj (congrArg Prod.snd h)) _ _

/-- Row and column conservation invariant for a partially constructed greedy
transport plan. -/
def GreedyTransportConserves
    [Fintype α] [Fintype β]
    (p : α → ENNReal) (q : β → ENNReal)
    (state : GreedyTransportState α β) : Prop :=
  (∀ i, state.1 i + ∑ j, state.2.2 (i, j) = p i) ∧
    ∀ j, state.2.1 j + ∑ i, state.2.2 (i, j) = q j

omit [DecidableEq α] [DecidableEq β] in
/-- The initial greedy state satisfies both conservation identities. -/
theorem initialGreedyTransportState_conserves
    [Fintype α] [Fintype β]
    (p : α → ENNReal) (q : β → ENNReal) :
    GreedyTransportConserves p q (initialGreedyTransportState p q) := by
  constructor <;> intro x <;> simp [initialGreedyTransportState]

/-- One greedy edge update preserves row and column conservation. -/
theorem GreedyTransportConserves.step
    [Fintype α] [Fintype β]
    {p : α → ENNReal} {q : β → ENNReal}
    {state : GreedyTransportState α β}
    (h : GreedyTransportConserves p q state) (edge : α × β) :
    GreedyTransportConserves p q (greedyTransportStep state edge) := by
  let amount := greedyTransportAllocation state edge
  have hrowAmount : amount ≤ state.1 edge.1 := min_le_left _ _
  have hcolAmount : amount ≤ state.2.1 edge.2 := min_le_right _ _
  constructor
  · intro i
    rw [sum_greedyTransportStep_mass_row]
    by_cases hi : i = edge.1
    · subst i
      simp only [if_true]
      unfold greedyTransportStep
      simp only [Function.update_self]
      change state.1 edge.1 - amount +
        ((∑ j, state.2.2 (edge.1, j)) + amount) = p edge.1
      calc
        _ = (state.1 edge.1 - amount + amount) +
            ∑ j, state.2.2 (edge.1, j) := by ac_rfl
        _ = state.1 edge.1 + ∑ j, state.2.2 (edge.1, j) := by
          rw [tsub_add_cancel_of_le hrowAmount]
        _ = p edge.1 := h.1 edge.1
    · simp only [hi, if_false, add_zero]
      simp only [greedyTransportStep, Function.update_of_ne hi]
      exact h.1 i
  · intro j
    rw [sum_greedyTransportStep_mass_col]
    by_cases hj : j = edge.2
    · subst j
      simp only [if_true]
      unfold greedyTransportStep
      simp only [Function.update_self]
      change state.2.1 edge.2 - amount +
        ((∑ i, state.2.2 (i, edge.2)) + amount) = q edge.2
      calc
        _ = (state.2.1 edge.2 - amount + amount) +
            ∑ i, state.2.2 (i, edge.2) := by ac_rfl
        _ = state.2.1 edge.2 + ∑ i, state.2.2 (i, edge.2) := by
          rw [tsub_add_cancel_of_le hcolAmount]
        _ = q edge.2 := h.2 edge.2
    · simp only [hj, if_false, add_zero]
      simp only [greedyTransportStep, Function.update_of_ne hj]
      exact h.2 j

/-- Conservation holds after every finite greedy edge list. -/
theorem greedyTransportState_conserves
    [Fintype α] [Fintype β]
    (p : α → ENNReal) (q : β → ENNReal) (order : List (α × β)) :
    GreedyTransportConserves p q (greedyTransportState p q order) := by
  induction order using List.reverseRecOn with
  | nil => exact initialGreedyTransportState_conserves p q
  | append_singleton order edge ih =>
      rw [greedyTransportState_append_singleton]
      exact ih.step edge

/-- Processing an edge exhausts at least one of its two residual marginals. -/
theorem greedyTransportStep_row_eq_zero_or_col_eq_zero
    (state : GreedyTransportState α β) (edge : α × β) :
    (greedyTransportStep state edge).1 edge.1 = 0 ∨
      (greedyTransportStep state edge).2.1 edge.2 = 0 := by
  unfold greedyTransportStep greedyTransportAllocation
  simp only [Function.update_self]
  rcases le_total (state.1 edge.1) (state.2.1 edge.2) with h | h
  · left
    rw [min_eq_left h, tsub_self]
  · right
    rw [min_eq_right h, tsub_self]

/-- A zero row residual remains zero under every later greedy update. -/
theorem greedyTransportStep_row_eq_zero
    (state : GreedyTransportState α β) (edge : α × β) (i : α)
    (hi : state.1 i = 0) :
    (greedyTransportStep state edge).1 i = 0 := by
  unfold greedyTransportStep
  by_cases h : i = edge.1
  · subst i
    simp only [Function.update_self, hi, zero_tsub]
  · simp only [Function.update_of_ne h, hi]

/-- A zero column residual remains zero under every later greedy update. -/
theorem greedyTransportStep_col_eq_zero
    (state : GreedyTransportState α β) (edge : α × β) (j : β)
    (hj : state.2.1 j = 0) :
    (greedyTransportStep state edge).2.1 j = 0 := by
  unfold greedyTransportStep
  by_cases h : j = edge.2
  · subst j
    simp only [Function.update_self, hj, zero_tsub]
  · simp only [Function.update_of_ne h, hj]

/-- A zero row remains zero after a whole suffix of edge updates. -/
theorem foldl_greedyTransportStep_row_eq_zero
    (state : GreedyTransportState α β) (order : List (α × β)) (i : α)
    (hi : state.1 i = 0) :
    (order.foldl greedyTransportStep state).1 i = 0 := by
  induction order generalizing state with
  | nil => exact hi
  | cons edge order ih =>
      simp only [List.foldl_cons]
      exact ih _ (greedyTransportStep_row_eq_zero state edge i hi)

/-- A zero column remains zero after a whole suffix of edge updates. -/
theorem foldl_greedyTransportStep_col_eq_zero
    (state : GreedyTransportState α β) (order : List (α × β)) (j : β)
    (hj : state.2.1 j = 0) :
    (order.foldl greedyTransportStep state).2.1 j = 0 := by
  induction order generalizing state with
  | nil => exact hj
  | cons edge order ih =>
      simp only [List.foldl_cons]
      exact ih _ (greedyTransportStep_col_eq_zero state edge j hj)

/-- Once an edge has appeared in the order, the final state has exhausted its
row or its column. -/
theorem greedyTransportState_row_eq_zero_or_col_eq_zero_of_mem
    (p : α → ENNReal) (q : β → ENNReal)
    (order : List (α × β)) (edge : α × β) (hedge : edge ∈ order) :
    (greedyTransportState p q order).1 edge.1 = 0 ∨
      (greedyTransportState p q order).2.1 edge.2 = 0 := by
  rcases List.mem_iff_append.mp hedge with ⟨pre, suffix, rfl⟩
  unfold greedyTransportState
  rw [List.foldl_append]
  simp only [List.foldl_cons]
  rcases greedyTransportStep_row_eq_zero_or_col_eq_zero
      (pre.foldl greedyTransportStep (initialGreedyTransportState p q)) edge
      with hrow | hcol
  · left
    exact foldl_greedyTransportStep_row_eq_zero _ suffix edge.1 hrow
  · right
    exact foldl_greedyTransportStep_col_eq_zero _ suffix edge.2 hcol

/-- An edge order is complete when it contains every cell of the finite
transport table. Repetitions are allowed. -/
def IsCompleteEdgeOrder (order : List (α × β)) : Prop :=
  ∀ edge : α × β, edge ∈ order

/-- For equal finite total input mass, a complete greedy pass exhausts every
row and column residual. -/
theorem greedyTransportState_residual_eq_zero_of_complete
    [Fintype α] [Fintype β]
    (p : α → ENNReal) (q : β → ENNReal)
    (hp : ∑ i, p i = 1) (hq : ∑ j, q j = 1)
    (order : List (α × β)) (horder : IsCompleteEdgeOrder order) :
    (∀ i, (greedyTransportState p q order).1 i = 0) ∧
      ∀ j, (greedyTransportState p q order).2.1 j = 0 := by
  classical
  let state := greedyTransportState p q order
  let rowTotal := ∑ i, state.1 i
  let colTotal := ∑ j, state.2.1 j
  let massTotal := ∑ i, ∑ j, state.2.2 (i, j)
  have hconserves := greedyTransportState_conserves p q order
  have hrowTotal : rowTotal + massTotal = 1 := by
    calc
      rowTotal + massTotal = ∑ i, (state.1 i + ∑ j, state.2.2 (i, j)) := by
        simp only [rowTotal, massTotal, Finset.sum_add_distrib]
      _ = ∑ i, p i := Finset.sum_congr rfl fun i hi => hconserves.1 i
      _ = 1 := hp
  have hcolTotal : colTotal + massTotal = 1 := by
    calc
      colTotal + massTotal =
          colTotal + ∑ j, ∑ i, state.2.2 (i, j) := by
            rw [Finset.sum_comm]
      _ = ∑ j, (state.2.1 j + ∑ i, state.2.2 (i, j)) := by
        simp only [colTotal, Finset.sum_add_distrib]
      _ = ∑ j, q j := Finset.sum_congr rfl fun j hj => hconserves.2 j
      _ = 1 := hq
  have hmassFinite : massTotal ≠ ∞ := by
    apply ne_of_lt
    calc
      massTotal ≤ rowTotal + massTotal := le_add_left le_rfl
      _ = 1 := hrowTotal
      _ < ∞ := ENNReal.one_lt_top
  have hresidualTotals : rowTotal = colTotal := by
    apply (ENNReal.add_left_inj hmassFinite).mp
    exact hrowTotal.trans hcolTotal.symm
  have hrowZero : rowTotal = 0 := by
    by_contra hrow
    have hexists : ∃ i, state.1 i ≠ 0 := by
      by_contra hnone
      push Not at hnone
      exact hrow (Finset.sum_eq_zero fun i hi => hnone i)
    rcases hexists with ⟨i, hi⟩
    have hcols : ∀ j, state.2.1 j = 0 := by
      intro j
      rcases greedyTransportState_row_eq_zero_or_col_eq_zero_of_mem
          p q order (i, j) (horder (i, j)) with hri | hcj
      · exact (hi hri).elim
      · exact hcj
    have hcolZero : colTotal = 0 :=
      Finset.sum_eq_zero fun j hj => hcols j
    exact hrow (hresidualTotals.trans hcolZero)
  have hcolZero : colTotal = 0 := hresidualTotals.symm.trans hrowZero
  constructor
  · intro i
    apply le_antisymm
    · exact (Finset.single_le_sum (fun _ _ => bot_le)
        (Finset.mem_univ i)).trans_eq hrowZero
    · exact bot_le
  · intro j
    apply le_antisymm
    · exact (Finset.single_le_sum (fun _ _ => bot_le)
        (Finset.mem_univ j)).trans_eq hcolZero
    · exact bot_le

/-- Consequently, a complete greedy edge order produces a feasible transport
mass with exactly the requested finite marginals. -/
theorem greedyTransportMass_mem_transportPlans_of_complete
    [Fintype α] [Fintype β]
    (p : α → ENNReal) (q : β → ENNReal)
    (hp : ∑ i, p i = 1) (hq : ∑ j, q j = 1)
    (order : List (α × β)) (horder : IsCompleteEdgeOrder order) :
    greedyTransportMass p q order ∈ transportPlans
      (PMF.ofFintype p hp) (PMF.ofFintype q hq) := by
  rcases greedyTransportState_residual_eq_zero_of_complete
      p q hp hq order horder with ⟨hrow, hcol⟩
  have hconserves := greedyTransportState_conserves p q order
  constructor
  · intro i
    have hi := hconserves.1 i
    rw [hrow i, zero_add] at hi
    exact hi
  · intro j
    have hj := hconserves.2 j
    rw [hcol j, zero_add] at hj
    exact hj

omit [DecidableEq α] in
private theorem sum_pmf_eq_one [Fintype α] (p : PMF α) : ∑ i, p i = 1 := by
  calc
    ∑ i, p i = ∑' i, p i := by rw [tsum_fintype]
    _ = 1 := p.tsum_coe

/-- The greedy mass from a complete edge order is feasible for two PMFs. -/
theorem greedyTransportMass_mem_transportPlans
    [Fintype α] [Fintype β]
    (p : PMF α) (q : PMF β)
    (order : List (α × β)) (horder : IsCompleteEdgeOrder order) :
    greedyTransportMass (fun i => p i) (fun j => q j) order ∈
      transportPlans p q := by
  have h := greedyTransportMass_mem_transportPlans_of_complete
    (fun i => p i) (fun j => q j) (sum_pmf_eq_one p) (sum_pmf_eq_one q)
      order horder
  have hpEq : PMF.ofFintype (fun i => p i) (sum_pmf_eq_one p) = p := by
    ext i
    rfl
  have hqEq : PMF.ofFintype (fun j => q j) (sum_pmf_eq_one q) = q := by
    ext j
    rfl
  rwa [hpEq, hqEq] at h

/-- A complete greedy edge order packaged as a finite coupling. -/
noncomputable def greedyTransportCoupling
    [Fintype α] [Fintype β]
    (p : PMF α) (q : PMF β)
    (order : List (α × β)) (horder : IsCompleteEdgeOrder order) :
    PMF (α × β) :=
  transportPlanPMF p q
    (greedyTransportMass (fun i => p i) (fun j => q j) order)
    (greedyTransportMass_mem_transportPlans p q order horder)

@[simp]
theorem greedyTransportCoupling_apply
    [Fintype α] [Fintype β]
    (p : PMF α) (q : PMF β)
    (order : List (α × β)) (horder : IsCompleteEdgeOrder order)
    (edge : α × β) :
    greedyTransportCoupling p q order horder edge =
      greedyTransportMass (fun i => p i) (fun j => q j) order edge :=
  rfl

/-- Every complete greedy candidate has the requested PMF marginals. -/
theorem greedyTransportCoupling_isCoupling
    [Fintype α] [Fintype β]
    (p : PMF α) (q : PMF β)
    (order : List (α × β)) (horder : IsCompleteEdgeOrder order) :
    IsPMFCoupling (greedyTransportCoupling p q order horder) p q :=
  transportPlanPMF_isCoupling p q _ _

/-- The finite candidate type consisting of all permutations of the complete
transport table. -/
def CompleteEdgeOrder [Fintype α] [Fintype β] :=
  {order : List (α × β) //
    order ∈ (Finset.univ.toList : List (α × β)).permutations}

noncomputable instance [Fintype α] [Fintype β] :
    Fintype (CompleteEdgeOrder (α := α) (β := β)) :=
  (List.finite_toSet
    (Finset.univ.toList : List (α × β)).permutations).fintype

instance [Fintype α] [Fintype β] :
    Nonempty (CompleteEdgeOrder (α := α) (β := β)) := by
  refine ⟨⟨Finset.univ.toList, List.mem_permutations.mpr (List.Perm.refl _)⟩⟩

instance [Fintype α] [Fintype β] :
    MeasurableSpace (CompleteEdgeOrder (α := α) (β := β)) := ⊤

instance [Fintype α] [Fintype β] :
    DiscreteMeasurableSpace (CompleteEdgeOrder (α := α) (β := β)) :=
  ⟨fun _ => by simp⟩

omit [DecidableEq α] [DecidableEq β] in
/-- Every candidate order really contains every table edge. -/
theorem CompleteEdgeOrder.isComplete
    [Fintype α] [Fintype β]
    (order : CompleteEdgeOrder (α := α) (β := β)) :
    IsCompleteEdgeOrder order.1 := by
  intro edge
  have hperm := List.mem_permutations.mp order.2
  exact hperm.mem_iff.mpr (by simp)

/-- The coupling candidate indexed by a complete edge ordering. -/
noncomputable def completeOrderTransportCoupling
    [Fintype α] [Fintype β]
    (p : PMF α) (q : PMF β)
    (order : CompleteEdgeOrder (α := α) (β := β)) :
    PMF (α × β) :=
  greedyTransportCoupling p q order.1 order.isComplete

/-- Every complete-order candidate has the requested marginals. -/
theorem completeOrderTransportCoupling_isCoupling
    [Fintype α] [Fintype β]
    (p : PMF α) (q : PMF β)
    (order : CompleteEdgeOrder (α := α) (β := β)) :
    IsPMFCoupling (completeOrderTransportCoupling p q order) p q :=
  greedyTransportCoupling_isCoupling p q order.1 order.isComplete

/-- Each atom of every fixed complete-order candidate is measurable in
parameterized finite marginals. -/
theorem measurable_completeOrderTransportCoupling_apply
    [Fintype α] [Fintype β] [MeasurableSpace Ω]
    (p : Ω → PMF α) (q : Ω → PMF β)
    (hp : ∀ i, Measurable fun ω => p ω i)
    (hq : ∀ j, Measurable fun ω => q ω j)
    (order : CompleteEdgeOrder (α := α) (β := β))
    (edge : α × β) :
    Measurable fun ω => completeOrderTransportCoupling
      (p ω) (q ω) order edge := by
  simpa only [completeOrderTransportCoupling,
    greedyTransportCoupling_apply] using
    measurable_greedyTransportMass_apply
      (fun ω i => p ω i) (fun ω j => q ω j) hp hq order.1 edge

/-- Expected cost of every fixed complete-order candidate is measurable when
the marginals and finite cost matrix are parameterized measurably. -/
theorem measurable_completeOrderTransportCost
    [Fintype α] [Fintype β] [MeasurableSpace Ω]
    (p : Ω → PMF α) (q : Ω → PMF β)
    (cost : Ω → α → β → NNReal)
    (hp : ∀ i, Measurable fun ω => p ω i)
    (hq : ∀ j, Measurable fun ω => q ω j)
    (hcost : ∀ i j, Measurable fun ω => cost ω i j)
    (order : CompleteEdgeOrder (α := α) (β := β)) :
    Measurable fun ω => transportCost (cost ω)
      (completeOrderTransportCoupling (p ω) (q ω) order) := by
  unfold transportCost
  apply Finset.measurable_sum
  intro i hi
  apply Finset.measurable_sum
  intro j hj
  exact (measurable_completeOrderTransportCoupling_apply
    p q hp hq order (i, j)).mul (hcost i j).coe_nnreal_ennreal

/-- The measurably tie-broken least-cost complete edge order. -/
noncomputable def completeOrderArgmin
    [Fintype α] [Fintype β]
    (p : Ω → PMF α) (q : Ω → PMF β)
    (cost : Ω → α → β → NNReal) :
    Ω → CompleteEdgeOrder (α := α) (β := β) :=
  fintypeArgmin fun ω order =>
    transportCost (cost ω)
      (completeOrderTransportCoupling (p ω) (q ω) order)

/-- The coupling selected from the finite complete-order candidate family. -/
noncomputable def greedySelectedTransportCoupling
    [Fintype α] [Fintype β]
    (p : Ω → PMF α) (q : Ω → PMF β)
    (cost : Ω → α → β → NNReal) (ω : Ω) : PMF (α × β) :=
  completeOrderTransportCoupling (p ω) (q ω)
    (completeOrderArgmin p q cost ω)

/-- The selected candidate has exactly the requested marginals. -/
theorem greedySelectedTransportCoupling_isCoupling
    [Fintype α] [Fintype β]
    (p : Ω → PMF α) (q : Ω → PMF β)
    (cost : Ω → α → β → NNReal) (ω : Ω) :
    IsPMFCoupling (greedySelectedTransportCoupling p q cost ω) (p ω) (q ω) :=
  completeOrderTransportCoupling_isCoupling _ _ _

/-- The selected candidate costs no more than any complete-order candidate. -/
theorem greedySelectedTransportCoupling_cost_le
    [Fintype α] [Fintype β]
    (p : Ω → PMF α) (q : Ω → PMF β)
    (cost : Ω → α → β → NNReal) (ω : Ω)
    (order : CompleteEdgeOrder (α := α) (β := β)) :
    transportCost (cost ω) (greedySelectedTransportCoupling p q cost ω) ≤
      transportCost (cost ω)
        (completeOrderTransportCoupling (p ω) (q ω) order) := by
  exact fintypeArgmin_le
    (fun ω order => transportCost (cost ω)
      (completeOrderTransportCoupling (p ω) (q ω) order)) ω order

/-- Every selected joint-mass atom is measurable in the parameter. -/
theorem measurable_greedySelectedTransportCoupling_apply
    [Fintype α] [Fintype β] [MeasurableSpace Ω]
    (p : Ω → PMF α) (q : Ω → PMF β)
    (cost : Ω → α → β → NNReal)
    (hp : ∀ i, Measurable fun ω => p ω i)
    (hq : ∀ j, Measurable fun ω => q ω j)
    (hcost : ∀ i j, Measurable fun ω => cost ω i j)
    (edge : α × β) :
    Measurable fun ω => greedySelectedTransportCoupling p q cost ω edge := by
  unfold greedySelectedTransportCoupling completeOrderArgmin
  apply measurable_candidate_fintypeArgmin_of_forall
    (score := fun ω order => transportCost (cost ω)
      (completeOrderTransportCoupling (p ω) (q ω) order))
    (candidate := fun ω order =>
      completeOrderTransportCoupling (p ω) (q ω) order edge)
  · intro order
    exact measurable_completeOrderTransportCost p q cost hp hq hcost order
  · intro order
    exact measurable_completeOrderTransportCoupling_apply
      p q hp hq order edge

/-- The finite greedy candidate family is complete for a transport problem if
some candidate is no more expensive than every feasible coupling. This is the
single remaining combinatorial LP obligation for exact optimality. -/
def GreedyTransportCandidatesComplete
    [Fintype α] [Fintype β]
    (p : PMF α) (q : PMF β) (cost : α → β → NNReal) : Prop :=
  ∀ joint : PMF (α × β), IsPMFCoupling joint p q →
    ∃ order : CompleteEdgeOrder (α := α) (β := β),
      transportCost cost (completeOrderTransportCoupling p q order) ≤
        transportCost cost joint

/-- Candidate completeness upgrades finite argmin optimality to global
transport optimality. -/
theorem greedySelectedTransportCoupling_minimal
    [Fintype α] [Fintype β]
    (p : Ω → PMF α) (q : Ω → PMF β)
    (cost : Ω → α → β → NNReal) (ω : Ω)
    (hcomplete : GreedyTransportCandidatesComplete (p ω) (q ω) (cost ω))
    (joint : PMF (α × β)) (hjoint : IsPMFCoupling joint (p ω) (q ω)) :
    transportCost (cost ω) (greedySelectedTransportCoupling p q cost ω) ≤
      transportCost (cost ω) joint := by
  rcases hcomplete joint hjoint with ⟨order, horder⟩
  exact (greedySelectedTransportCoupling_cost_le
    p q cost ω order).trans horder

end McmcLean.Finite
