import McmcLean.Finite.Coupling
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.Compact

/-!
# Finite optimal transport couplings

This module represents a transport plan between finite PMFs by its joint mass
function.  The feasible set is a nonempty closed subset of a finite product of
compact `ENNReal` spaces.  Consequently every finite continuous cost has an
attained minimum.  The chosen minimizer is packaged back into a PMF and proved
to have the requested marginals.
-/

open scoped BigOperators ENNReal

namespace McmcLean.Finite

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Joint mass functions with prescribed row and column marginals. -/
def transportPlans (p : PMF α) (q : PMF β) :
    Set ((α × β) → ENNReal) :=
  {r | (∀ i, ∑ j, r (i, j) = p i) ∧
    (∀ j, ∑ i, r (i, j) = q j)}

private theorem sum_pmf (p : PMF α) : ∑ i, p i = 1 := by
  calc
    ∑ i, p i = ∑' i, p i := by rw [tsum_fintype]
    _ = 1 := p.tsum_coe

/-- The independent product mass is always a feasible transport plan. -/
theorem independent_mass_mem_transportPlans (p : PMF α) (q : PMF β) :
    (fun ij : α × β => p ij.1 * q ij.2) ∈ transportPlans p q := by
  constructor
  · intro i
    simp only
    rw [← Finset.mul_sum, sum_pmf, mul_one]
  · intro j
    simp only
    rw [← Finset.sum_mul, sum_pmf, one_mul]

theorem transportPlans_nonempty (p : PMF α) (q : PMF β) :
    (transportPlans p q).Nonempty :=
  ⟨_, independent_mass_mem_transportPlans p q⟩

/-- Every atom of a feasible finite transport plan is finite. -/
theorem transportPlan_apply_ne_top
    {p : PMF α} {q : PMF β} {r : (α × β) → ENNReal}
    (hr : r ∈ transportPlans p q) (edge : α × β) :
    r edge ≠ ∞ := by
  apply ne_of_lt
  calc
    r edge ≤ ∑ j, r (edge.1, j) :=
      Finset.single_le_sum
        (f := fun j => r (edge.1, j))
        (fun _ _ => bot_le) (Finset.mem_univ edge.2)
    _ = p edge.1 := hr.1 edge.1
    _ < ∞ := p.apply_lt_top edge.1

omit [Fintype α] in
private theorem continuous_rowSum (i : α) :
    Continuous fun r : (α × β) → ENNReal => ∑ j, r (i, j) := by
  fun_prop

omit [Fintype β] in
private theorem continuous_colSum (j : β) :
    Continuous fun r : (α × β) → ENNReal => ∑ i, r (i, j) := by
  fun_prop

/-- The finite transport polytope is closed. -/
theorem isClosed_transportPlans (p : PMF α) (q : PMF β) :
    IsClosed (transportPlans p q) := by
  rw [show transportPlans p q =
      ((⋂ i : α, {r : (α × β) → ENNReal | (∑ j, r (i, j)) = p i}) ∩
        ⋂ j : β, {r : (α × β) → ENNReal | (∑ i, r (i, j)) = q j}) by
    ext r
    simp [transportPlans]]
  apply IsClosed.inter
  · exact isClosed_iInter fun i =>
      isClosed_eq (continuous_rowSum (β := β) i) continuous_const
  · exact isClosed_iInter fun j =>
      isClosed_eq (continuous_colSum (α := α) j) continuous_const

/-- The finite transport polytope is compact. -/
theorem isCompact_transportPlans (p : PMF α) (q : PMF β) :
    IsCompact (transportPlans p q) := by
  exact isCompact_univ.of_isClosed_subset (isClosed_transportPlans p q)
    (Set.subset_univ _)

/-- Expected transport cost of a joint mass function. -/
noncomputable def transportCost (cost : α → β → NNReal)
    (r : (α × β) → ENNReal) : ENNReal :=
  ∑ i, ∑ j, r (i, j) * (cost i j : ENNReal)

/-- The cost of a feasible finite transport plan is finite. -/
theorem transportCost_ne_top (cost : α → β → NNReal)
    {p : PMF α} {q : PMF β} {r : (α × β) → ENNReal}
    (hr : r ∈ transportPlans p q) :
    transportCost cost r ≠ ∞ := by
  unfold transportCost
  exact ENNReal.sum_ne_top.2 fun i hi =>
    ENNReal.sum_ne_top.2 fun j hj =>
      ENNReal.mul_ne_top (transportPlan_apply_ne_top hr (i, j))
        ENNReal.coe_ne_top

/-- For a finite joint PMF, `transportCost` is exactly the Lebesgue integral
of the cost against the associated measure. This is the bridge used when a
finite trajectory-index coupling is pushed into a measure-valued Markov
kernel. -/
theorem lintegral_toMeasure_eq_transportCost
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (cost : α → β → NNReal) (r : PMF (α × β)) :
    (∫⁻ ij, (cost ij.1 ij.2 : ENNReal) ∂r.toMeasure) =
      transportCost cost r := by
  rw [MeasureTheory.lintegral_fintype]
  simp_rw [PMF.toMeasure_apply_singleton r _ (MeasurableSet.singleton _)]
  unfold transportCost
  calc
    (∑ ij, (cost ij.1 ij.2 : ENNReal) * r ij) =
        ∑ ij, r ij * (cost ij.1 ij.2 : ENNReal) := by
      apply Finset.sum_congr rfl
      intro ij hij
      exact mul_comm _ _
    _ = ∑ i, ∑ j, r (i, j) * (cost i j : ENNReal) := by
      symm
      simpa only [Finset.univ_product_univ] using
        (Finset.sum_product (Finset.univ : Finset α)
          (Finset.univ : Finset β)
          (fun ij => r ij * (cost ij.1 ij.2 : ENNReal))).symm

/-- A diagonal coupling has zero expected cost whenever the cost vanishes on
the diagonal. -/
theorem transportCost_diagonalCoupling_eq_zero
    {cost : α → α → NNReal} (p : PMF α)
    (hcost : ∀ i, cost i i = 0) :
    transportCost cost (diagonalCoupling p) = 0 := by
  classical
  unfold transportCost
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hij : i = j
  · subst j
    simp [hcost]
  · rw [diagonalCoupling_apply_pair]
    simp [hij]

/-- Expected cost is bounded by the exact weighted diagonal contribution plus
mismatch mass times an off-diagonal bound. Keeping the diagonal sum is crucial
for trajectory couplings whose aligned costs vary with the index. -/
theorem transportCost_le_diagonalCost_add_mul_mismatchMass
    [DecidableEq α] (cost : α → α → NNReal) (joint : PMF (α × α))
    (mismatchBound : NNReal)
    (hmismatch : ∀ i j, i ≠ j → cost i j ≤ mismatchBound) :
    transportCost cost joint ≤
      (∑ i, joint (i, i) * (cost i i : ENNReal)) +
        mismatchMass joint * (mismatchBound : ENNReal) := by
  have hrow : ∀ i : α,
      (∑ j, joint (i, j) * (cost i j : ENNReal)) ≤
        joint (i, i) * (cost i i : ENNReal) +
          ∑ j ∈ Finset.univ.erase i,
            joint (i, j) * (mismatchBound : ENNReal) := by
    intro i
    calc
      (∑ j, joint (i, j) * (cost i j : ENNReal)) =
          joint (i, i) * (cost i i : ENNReal) +
            ∑ j ∈ Finset.univ.erase i,
              joint (i, j) * (cost i j : ENNReal) := by
        rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      _ ≤ joint (i, i) * (cost i i : ENNReal) +
            ∑ j ∈ Finset.univ.erase i,
              joint (i, j) * (mismatchBound : ENNReal) := by
        apply add_le_add_right
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_right
          (ENNReal.coe_le_coe.mpr
            (hmismatch i j (Finset.mem_erase.mp hj).1.symm)) _
  unfold transportCost
  apply le_trans (Finset.sum_le_sum fun i hi => hrow i)
  rw [Finset.sum_add_distrib]
  simp_rw [← Finset.sum_mul]
  rw [← mismatchMass]

/-- Expected cost is bounded by a diagonal cost plus mismatch mass times an
off-diagonal cost bound. -/
theorem transportCost_le_add_mul_mismatchMass
    [DecidableEq α] (cost : α → α → NNReal) (joint : PMF (α × α))
    (diagonalBound mismatchBound : NNReal)
    (hdiagonal : ∀ i, cost i i ≤ diagonalBound)
    (hmismatch : ∀ i j, i ≠ j → cost i j ≤ mismatchBound) :
    transportCost cost joint ≤
      (diagonalBound : ENNReal) +
        mismatchMass joint * (mismatchBound : ENNReal) := by
  have hrow : ∀ i : α,
      (∑ j, joint (i, j) * (cost i j : ENNReal)) ≤
        joint (i, i) * (diagonalBound : ENNReal) +
          ∑ j ∈ Finset.univ.erase i,
            joint (i, j) * (mismatchBound : ENNReal) := by
    intro i
    calc
      (∑ j, joint (i, j) * (cost i j : ENNReal)) =
          joint (i, i) * (cost i i : ENNReal) +
            ∑ j ∈ Finset.univ.erase i,
              joint (i, j) * (cost i j : ENNReal) := by
        rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      _ ≤ joint (i, i) * (diagonalBound : ENNReal) +
            ∑ j ∈ Finset.univ.erase i,
              joint (i, j) * (mismatchBound : ENNReal) := by
        apply add_le_add
        · exact mul_le_mul_right (ENNReal.coe_le_coe.mpr (hdiagonal i)) _
        · apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul_right
            (ENNReal.coe_le_coe.mpr
              (hmismatch i j (Finset.mem_erase.mp hj).1.symm)) _
  unfold transportCost
  apply le_trans (Finset.sum_le_sum fun i hi => hrow i)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  simp_rw [← Finset.sum_mul]
  rw [← mismatchMass]
  have hdiag : (∑ i, joint (i, i)) ≤ 1 := by
    rw [← diagonalMass_add_mismatchMass joint]
    exact le_add_right le_rfl
  have hmul := mul_le_mul_left hdiag (diagonalBound : ENNReal)
  simpa only [one_mul, add_comm] using add_le_add_right hmul
    (mismatchMass joint * (mismatchBound : ENNReal))

/-- If every unequal pair costs at least `mismatchLower`, transport cost is at
least that floor times the coupling's unequal-pair mass. -/
theorem mismatchMass_mul_le_transportCost
    [DecidableEq α] (cost : α → α → NNReal)
    (joint : PMF (α × α)) (mismatchLower : NNReal)
    (hlower : ∀ i j, i ≠ j → mismatchLower ≤ cost i j) :
    mismatchMass joint * (mismatchLower : ENNReal) ≤
      transportCost cost joint := by
  unfold mismatchMass transportCost
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.sum_mul]
  calc
    (∑ j ∈ Finset.univ.erase i,
        joint (i, j) * (mismatchLower : ENNReal)) ≤
        ∑ j ∈ Finset.univ.erase i,
          joint (i, j) * (cost i j : ENNReal) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_right
        (ENNReal.coe_le_coe.mpr
          (hlower i j (Finset.mem_erase.mp hj).1.symm)) _
    _ ≤ ∑ j, joint (i, j) * (cost i j : ENNReal) :=
      Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)

/-- Consequently every coupling pays at least total variation times a
positive off-diagonal cost floor. This lower bound diagnoses when a desired
quadratic near-diagonal transport estimate is impossible on a fixed finite
support. -/
theorem IsPMFCoupling.totalVariation_mul_le_transportCost
    [DecidableEq α] {p q : PMF α} {joint : PMF (α × α)}
    (h : IsPMFCoupling joint p q) (cost : α → α → NNReal)
    (mismatchLower : NNReal)
    (hlower : ∀ i j, i ≠ j → mismatchLower ≤ cost i j) :
    totalVariation p q * (mismatchLower : ENNReal) ≤
      transportCost cost joint := by
  calc
    totalVariation p q * (mismatchLower : ENNReal) ≤
        mismatchMass joint * (mismatchLower : ENNReal) := by
      simpa only [mul_comm] using mul_le_mul_right
        (IsPMFCoupling.totalVariation_le_mismatchMass h)
        (mismatchLower : ENNReal)
    _ ≤ transportCost cost joint :=
      mismatchMass_mul_le_transportCost cost joint mismatchLower hlower

/-- A proposed upper bound strictly below the TV-weighted off-diagonal floor
cannot hold for any coupling. -/
theorem IsPMFCoupling.not_transportCost_le_of_lt_tv_mul
    [DecidableEq α] {p q : PMF α} {joint : PMF (α × α)}
    (h : IsPMFCoupling joint p q) (cost : α → α → NNReal)
    (mismatchLower : NNReal)
    (hlower : ∀ i j, i ≠ j → mismatchLower ≤ cost i j)
    {bound : ENNReal}
    (hstrict : bound < totalVariation p q * (mismatchLower : ENNReal)) :
    ¬ transportCost cost joint ≤ bound := by
  exact not_le_of_gt
    (hstrict.trans_le (h.totalVariation_mul_le_transportCost
      cost mismatchLower hlower))

/-- On a nontrivial finite index space, pointwise positivity of every
off-diagonal cost automatically yields one common positive cost floor. -/
theorem exists_pos_mismatchCostFloor
    [Nontrivial α] [DecidableEq α] (cost : α → α → NNReal)
    (hcost : ∀ i j, i ≠ j → 0 < cost i j) :
    ∃ floor : NNReal, 0 < floor ∧
      ∀ i j, i ≠ j → floor ≤ cost i j := by
  classical
  let edges : Finset (α × α) := Finset.univ.filter fun edge => edge.1 ≠ edge.2
  obtain ⟨i, j, hij⟩ := exists_pair_ne α
  have hedges : edges.Nonempty := by
    exact ⟨(i, j), by simp [edges, hij]⟩
  let values : Finset NNReal := edges.image fun edge => cost edge.1 edge.2
  have hvalues : values.Nonempty := hedges.image _
  let floor := values.min' hvalues
  refine ⟨floor, ?_, ?_⟩
  · have hmem := values.min'_mem hvalues
    rcases Finset.mem_image.mp hmem with ⟨edge, hedge, hedgeEq⟩
    have hne : edge.1 ≠ edge.2 := (Finset.mem_filter.mp hedge).2
    simpa only [floor, hedgeEq] using hcost edge.1 edge.2 hne
  · intro i' j' hij'
    apply Finset.min'_le
    exact Finset.mem_image.mpr ⟨(i', j'), by simp [edges, hij'], rfl⟩

/-- For a maximal coupling, the mismatch term in the expected-cost bound is
exactly total variation. This is the finite probabilistic core of the maximal
multinomial coupling contraction argument. -/
theorem IsMaximalCoupling.transportCost_le_add_totalVariation_mul
    [DecidableEq α] {p q : PMF α} {joint : PMF (α × α)}
    (hmax : IsMaximalCoupling joint p q)
    (cost : α → α → NNReal) (diagonalBound mismatchBound : NNReal)
    (hdiagonal : ∀ i, cost i i ≤ diagonalBound)
    (hmismatch : ∀ i j, i ≠ j → cost i j ≤ mismatchBound) :
    transportCost cost joint ≤
      (diagonalBound : ENNReal) +
        totalVariation p q * (mismatchBound : ENNReal) := by
  rw [← hmax.mismatchMass_eq_totalVariation]
  exact transportCost_le_add_mul_mismatchMass cost joint
    diagonalBound mismatchBound hdiagonal hmismatch

/-- Refined cost bound for the canonical maximal coupling: retain the full
overlap-weighted diagonal cost and charge only off-diagonal mass at the
mismatch bound. -/
theorem maximalCoupling_transportCost_le_diagonal_add_totalVariation_mul
    [DecidableEq α] (p q : PMF α) (cost : α → α → NNReal)
    (mismatchBound : NNReal)
    (hmismatch : ∀ i j, i ≠ j → cost i j ≤ mismatchBound) :
    transportCost cost (maximalCoupling p q) ≤
      (∑ i, min (p i) (q i) * (cost i i : ENNReal)) +
        totalVariation p q * (mismatchBound : ENNReal) := by
  apply le_trans
    (transportCost_le_diagonalCost_add_mul_mismatchMass
      cost (maximalCoupling p q) mismatchBound hmismatch)
  rw [(maximalCoupling_isMaximal p q).mismatchMass_eq_totalVariation]
  simp only [maximalCoupling_apply_diagonal]
  exact le_rfl

/-- A reusable finite weighted-contraction principle. If all scalar costs are
at most one, costs on a designated band are at most `ρ ≤ 1`, and `loss` is no
larger than the overlap weight on that band times `1-ρ`, then the weighted
cost plus `loss` is at most the total unit budget. -/
theorem weightedCost_add_bandLoss_le_one
    [DecidableEq α] (weight cost : α → ENNReal) (band : α → Prop)
    [DecidablePred band] (ρ loss : ENNReal)
    (hweight : ∑ i, weight i ≤ 1)
    (hcost : ∀ i, cost i ≤ 1)
    (hband : ∀ i, band i → cost i ≤ ρ)
    (hρ : ρ ≤ 1)
    (hloss : loss ≤ ∑ i, if band i then weight i * (1 - ρ) else 0) :
    (∑ i, weight i * cost i) + loss ≤ 1 := by
  apply le_trans (add_le_add le_rfl hloss)
  apply le_trans _ hweight
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hiband : band i
  · simp only [hiband, if_true]
    calc
      weight i * cost i + weight i * (1 - ρ) ≤
          weight i * ρ + weight i * (1 - ρ) :=
        add_le_add (by
          simpa only [mul_comm] using
            mul_le_mul_left (hband i hiband) (weight i)) le_rfl
      _ = weight i * (ρ + (1 - ρ)) := by rw [mul_add]
      _ = weight i := by
        rw [add_comm, tsub_add_cancel_of_le hρ, mul_one]
  · simp only [hiband, if_false, add_zero]
    simpa only [mul_comm, one_mul, mul_one] using
      mul_le_mul_left (hcost i) (weight i)

/-- Two-rate version of `weightedCost_add_bandLoss_le_one`.  Outside a
designated band the normalized cost may be as large as `σ`; on the band it
is at most `ρ ≤ σ`.  The overlap mass on the band then recovers the loss
`σ - ρ` from the global `σ` budget. -/
theorem weightedCost_add_bandLoss_le
    [DecidableEq α] (weight cost : α → ENNReal) (band : α → Prop)
    [DecidablePred band] (ρ σ loss budget : ENNReal)
    (hweight : ∑ i, weight i ≤ 1)
    (hcost : ∀ i, cost i ≤ σ * budget)
    (hband : ∀ i, band i → cost i ≤ ρ * budget)
    (hρσ : ρ ≤ σ)
    (hloss : loss ≤ ∑ i,
      if band i then weight i * (σ - ρ) else 0) :
    (∑ i, weight i * cost i) + loss * budget ≤ σ * budget := by
  have hlossmul : loss * budget ≤
      (∑ i, if band i then weight i * (σ - ρ) else 0) * budget :=
    by simpa only [mul_comm] using mul_le_mul_left hloss budget
  apply le_trans (add_le_add le_rfl hlossmul)
  have hweightmul : (∑ i, weight i) * (σ * budget) ≤ σ * budget := by
    simpa only [mul_comm, mul_one] using
      mul_le_mul_left hweight (σ * budget)
  apply le_trans _ hweightmul
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  have hsum : (∑ i, weight i) * (σ * budget) =
      ∑ i, weight i * (σ * budget) := by
    simpa using Finset.sum_mul Finset.univ weight (σ * budget)
  rw [hsum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hiband : band i
  · simp only [hiband, if_true]
    calc
      weight i * cost i + weight i * (σ - ρ) * budget ≤
          weight i * (ρ * budget) +
            weight i * (σ - ρ) * budget :=
        add_le_add (by simpa only [mul_comm] using
          mul_le_mul_left (hband i hiband) (weight i)) le_rfl
      _ = weight i * ((ρ + (σ - ρ)) * budget) := by ring
      _ = weight i * (σ * budget) := by
        rw [add_comm, tsub_add_cancel_of_le hρσ]
  · simp only [hiband, if_false, zero_mul, add_zero]
    simpa only [mul_comm] using mul_le_mul_left (hcost i) (weight i)

theorem continuous_transportCost (cost : α → β → NNReal) :
    Continuous (transportCost cost) := by
  unfold transportCost
  apply continuous_finsetSum
  intro i hi
  apply continuous_finsetSum
  intro j hj
  exact (ENNReal.continuous_mul_const ENNReal.coe_ne_top).comp
    (continuous_apply (i, j))

/-- Every finite transport problem has an optimal feasible joint mass. -/
theorem exists_optimalTransportPlan (p : PMF α) (q : PMF β)
    (cost : α → β → NNReal) :
    ∃ r ∈ transportPlans p q,
      ∀ s ∈ transportPlans p q, transportCost cost r ≤ transportCost cost s := by
  exact (isCompact_transportPlans p q).exists_isMinOn
    (transportPlans_nonempty p q) (continuous_transportCost cost).continuousOn

/-- A selected optimal finite transport mass. -/
noncomputable def optimalTransportPlan (p : PMF α) (q : PMF β)
    (cost : α → β → NNReal) : (α × β) → ENNReal :=
  (exists_optimalTransportPlan p q cost).choose

theorem optimalTransportPlan_mem (p : PMF α) (q : PMF β)
    (cost : α → β → NNReal) :
    optimalTransportPlan p q cost ∈ transportPlans p q :=
  (exists_optimalTransportPlan p q cost).choose_spec.1

theorem optimalTransportPlan_minimal (p : PMF α) (q : PMF β)
    (cost : α → β → NNReal) {s : (α × β) → ENNReal}
    (hs : s ∈ transportPlans p q) :
    transportCost cost (optimalTransportPlan p q cost) ≤
      transportCost cost s :=
  (exists_optimalTransportPlan p q cost).choose_spec.2 s hs

private theorem sum_transportPlan_eq_one (p : PMF α) (q : PMF β)
    {r : (α × β) → ENNReal} (hr : r ∈ transportPlans p q) :
    ∑ ij, r ij = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [hr.1]
  exact sum_pmf p

/-- Package the selected optimal mass as a probability mass function. -/
noncomputable def optimalTransportCoupling (p : PMF α) (q : PMF β)
    (cost : α → β → NNReal) : PMF (α × β) :=
  PMF.ofFintype (optimalTransportPlan p q cost)
    (sum_transportPlan_eq_one p q (optimalTransportPlan_mem p q cost))

@[simp]
theorem optimalTransportCoupling_apply (p : PMF α) (q : PMF β)
    (cost : α → β → NNReal) (ij : α × β) :
    optimalTransportCoupling p q cost ij = optimalTransportPlan p q cost ij :=
  rfl

private theorem sum_fst_fiber (r : (α × β) → ENNReal) (i : α) :
    (∑ x : α × β,
      @ite ENNReal (i = x.1) (Classical.propDecidable _) (r x) 0) =
      ∑ j, r (i, j) := by
  classical
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · simp
  · intro a ha hai
    simp [Ne.symm hai]
  · simp

private theorem sum_snd_fiber (r : (α × β) → ENNReal) (j : β) :
    (∑ x : α × β,
      @ite ENNReal (j = x.2) (Classical.propDecidable _) (r x) 0) =
      ∑ i, r (i, j) := by
  classical
  rw [Fintype.sum_prod_type]
  simp

/-- Package any feasible finite transport mass as a probability mass
function.  This constructor is useful independently of the selected optimal
plan, for example for explicitly enumerated greedy candidates. -/
noncomputable def transportPlanPMF (p : PMF α) (q : PMF β)
    (r : (α × β) → ENNReal) (hr : r ∈ transportPlans p q) :
    PMF (α × β) :=
  PMF.ofFintype r (sum_transportPlan_eq_one p q hr)

@[simp]
theorem transportPlanPMF_apply (p : PMF α) (q : PMF β)
    (r : (α × β) → ENNReal) (hr : r ∈ transportPlans p q)
    (ij : α × β) :
    transportPlanPMF p q r hr ij = r ij :=
  rfl

/-- The PMF packaged from a feasible transport mass has exactly the specified
marginals. -/
theorem transportPlanPMF_isCoupling (p : PMF α) (q : PMF β)
    (r : (α × β) → ENNReal) (hr : r ∈ transportPlans p q) :
    IsPMFCoupling (transportPlanPMF p q r hr) p q := by
  constructor
  · ext i
    rw [PMF.map_apply, tsum_fintype]
    simp only [transportPlanPMF_apply]
    rw [sum_fst_fiber (α := α) (β := β)]
    exact hr.1 i
  · ext j
    rw [PMF.map_apply, tsum_fintype]
    simp only [transportPlanPMF_apply]
    rw [sum_snd_fiber (α := α) (β := β)]
    exact hr.2 j

/-- Conversely, the atom table of any finite PMF coupling is a feasible
transport plan. -/
theorem IsPMFCoupling.mem_transportPlans
    (p : PMF α) (q : PMF β) (joint : PMF (α × β))
    (hjoint : IsPMFCoupling joint p q) :
    (fun edge => joint edge) ∈ transportPlans p q := by
  constructor
  · intro i
    have hi := congrArg (fun mass : PMF α => mass i) hjoint.1
    rw [PMF.map_apply, tsum_fintype, sum_fst_fiber] at hi
    exact hi
  · intro j
    have hj := congrArg (fun mass : PMF β => mass j) hjoint.2
    rw [PMF.map_apply, tsum_fintype, sum_snd_fiber] at hj
    exact hj

/-- The selected optimal transport PMF has exactly the prescribed marginals. -/
theorem optimalTransportCoupling_isCoupling (p : PMF α) (q : PMF β)
    (cost : α → β → NNReal) :
    IsPMFCoupling (optimalTransportCoupling p q cost) p q := by
  constructor
  · ext i
    rw [PMF.map_apply, tsum_fintype]
    simp only [optimalTransportCoupling_apply]
    rw [sum_fst_fiber (α := α) (β := β)]
    have hrow := (optimalTransportPlan_mem p q cost).1 i
    exact hrow
  · ext j
    rw [PMF.map_apply, tsum_fintype]
    simp only [optimalTransportCoupling_apply]
    rw [sum_snd_fiber (α := α) (β := β)]
    have hcol := (optimalTransportPlan_mem p q cost).2 j
    exact hcol

/-- On a common finite index space, even the optimal coupling must pay total
variation times any uniform positive off-diagonal cost floor. -/
theorem totalVariation_mul_le_optimalTransportCost
    [DecidableEq α] (p q : PMF α) (cost : α → α → NNReal)
    (mismatchLower : NNReal)
    (hlower : ∀ i j, i ≠ j → mismatchLower ≤ cost i j) :
    totalVariation p q * (mismatchLower : ENNReal) ≤
      transportCost cost (optimalTransportCoupling p q cost) := by
  exact IsPMFCoupling.totalVariation_mul_le_transportCost
    (optimalTransportCoupling_isCoupling p q cost) cost mismatchLower hlower

/-- A first-order marginal discrepancy and a positive off-diagonal cost floor
force optimal finite transport cost to dominate every quadratic rate near the
diagonal. This is the generic obstruction used to audit exponent-two local
contractivity claims on fixed finite categorical supports. -/
theorem eventually_rate_mul_sq_lt_optimalTransportCost_toReal
    [DecidableEq α]
    (left right : ℝ → PMF α) (cost : ℝ → α → α → NNReal)
    (linearRate : ℝ) (mismatchLower : NNReal) (rate : ℝ)
    (hlinearRate : 0 < linearRate) (hmismatchLower : 0 < mismatchLower)
    (hTV : ∀ᶠ t in nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ,
      linearRate * |t| < (totalVariation (left t) (right t)).toReal)
    (hcost : ∀ᶠ t in nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ,
      ∀ i j, i ≠ j → mismatchLower ≤ cost t i j) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ,
      rate * t ^ 2 <
        (transportCost (cost t)
          (optimalTransportCoupling (left t) (right t) (cost t))).toReal := by
  have hfilter : nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ ≤ nhds 0 :=
    inf_le_left
  have htend : Filter.Tendsto (fun t : ℝ => rate * |t|)
      (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ) (nhds 0) := by
    have hc : ContinuousAt (fun t : ℝ => rate * |t|) 0 := by fun_prop
    change Filter.Tendsto (fun t : ℝ => rate * |t|) (nhds 0)
      (nhds (rate * |(0 : ℝ)|)) at hc
    norm_num at hc
    have hnhds : Filter.Tendsto (fun t : ℝ => rate * |t|)
        (nhds 0) (nhds 0) := hc
    exact hnhds.mono_left hfilter
  have hsmall : ∀ᶠ t in nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ,
      rate * |t| < linearRate * (mismatchLower : ℝ) :=
    (tendsto_order.1 htend).2 _
      (mul_pos hlinearRate hmismatchLower)
  filter_upwards [hTV, hcost, hsmall, self_mem_nhdsWithin] with
      t htv hfloor hsmall hmem
  have ht0 : t ≠ 0 := by simpa using hmem
  let joint := optimalTransportCoupling (left t) (right t) (cost t)
  have hjoint : IsPMFCoupling joint (left t) (right t) :=
    optimalTransportCoupling_isCoupling _ _ _
  have htransport := hjoint.totalVariation_mul_le_transportCost
    (cost t) mismatchLower (hfloor)
  have hcostTop : transportCost (cost t) joint ≠ ⊤ :=
    transportCost_ne_top (cost t)
      (IsPMFCoupling.mem_transportPlans _ _ joint hjoint)
  have htransportReal := ENNReal.toReal_mono hcostTop htransport
  have hmismatchReal : ((mismatchLower : ENNReal).toReal) =
      (mismatchLower : ℝ) := by simp
  rw [ENNReal.toReal_mul, hmismatchReal] at htransportReal
  have habs : 0 < |t| := abs_pos.mpr ht0
  calc
    rate * t ^ 2 = (rate * |t|) * |t| := by rw [← sq_abs]; ring
    _ < (linearRate * (mismatchLower : ℝ)) * |t| :=
      mul_lt_mul_of_pos_right hsmall habs
    _ = (linearRate * |t|) * (mismatchLower : ℝ) := by ring
    _ < (totalVariation (left t) (right t)).toReal *
        (mismatchLower : ℝ) :=
      mul_lt_mul_of_pos_right htv (show 0 < (mismatchLower : ℝ) by exact hmismatchLower)
    _ ≤ (transportCost (cost t) joint).toReal := htransportReal

/-- The chosen coupling minimizes expected cost among all finite PMF
couplings. -/
theorem optimalTransportCoupling_minimal (p : PMF α) (q : PMF β)
    (cost : α → β → NNReal) (joint : PMF (α × β))
    (hjoint : IsPMFCoupling joint p q) :
    transportCost cost (optimalTransportCoupling p q cost) ≤
      transportCost cost joint := by
  apply optimalTransportPlan_minimal p q cost
  constructor
  · intro i
    have h := congrArg (fun r : PMF α => r i) hjoint.fst
    simp only [PMF.map_apply, tsum_fintype] at h
    calc
      ∑ j, joint (i, j) =
          ∑ x : α × β,
            @ite ENNReal (i = x.1) (Classical.propDecidable _) (joint x) 0 :=
        (sum_fst_fiber (α := α) (β := β) joint i).symm
      _ = p i := by simpa only using h
  · intro j
    have h := congrArg (fun r : PMF β => r j) hjoint.snd
    simp only [PMF.map_apply, tsum_fintype] at h
    calc
      ∑ i, joint (i, j) =
          ∑ x : α × β,
            @ite ENNReal (j = x.2) (Classical.propDecidable _) (joint x) 0 :=
        (sum_snd_fiber (α := α) (β := β) joint j).symm
      _ = q j := by simpa only using h

end McmcLean.Finite
