import Mcmc.Finite.MarkovKernel
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Finite rooted random-trace reversals

Dynamic samplers such as ordinary NUTS may generate a state-dependent random
tree whose candidate rows are not equal after rerooting. Correctness can still
be proved at the richer trace level when every complete forward random trace
has a bijective reverse trace with identical target-weighted construction and
selection probability. This module states and proves that exact boundary.
-/

open scoped BigOperators

namespace Mcmc.Finite.MarkovKernel

variable {State Trace : Type*} [Fintype State] [Fintype Trace]

/-- Transition obtained by first drawing a state-dependent finite trace and
then selecting the next state conditionally on that trace. -/
noncomputable def rootedTraceKernel
    (traceLaw : State → Distribution Trace)
    (selection : State → Trace → Distribution State) : MarkovKernel State where
  prob current next := ∑ trace,
    (traceLaw current).mass trace * (selection current trace).mass next
  nonneg current next := Finset.sum_nonneg fun trace _ =>
    mul_nonneg ((traceLaw current).nonneg trace)
      ((selection current trace).nonneg next)
  sum_prob current := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (selection current _).sum_mass, mul_one]
    exact (traceLaw current).sum_mass

/-- Trace-level detailed balance. The reverse trace may depend on both
endpoints; bijectivity reindexes the finite trace sum, while the pointwise
identity accounts for every construction and selection probability. -/
theorem rootedTraceKernel_reversible
    (target : Distribution State)
    (traceLaw : State → Distribution Trace)
    (selection : State → Trace → Distribution State)
    (reverseTrace : State → State → Trace ≃ Trace)
    (hreverse : ∀ current next trace,
      target.mass current * ((traceLaw current).mass trace *
          (selection current trace).mass next) =
        target.mass next *
          ((traceLaw next).mass (reverseTrace current next trace) *
          (selection next (reverseTrace current next trace)).mass current)) :
    (rootedTraceKernel traceLaw selection).Reversible target := by
  intro current next
  simp only [rootedTraceKernel, Finset.mul_sum]
  calc
    ∑ trace, target.mass current * ((traceLaw current).mass trace *
        (selection current trace).mass next) =
      ∑ trace, target.mass next *
        ((traceLaw next).mass (reverseTrace current next trace) *
        (selection next (reverseTrace current next trace)).mass current) := by
          apply Finset.sum_congr rfl
          intro trace _
          exact hreverse current next trace
    _ = ∑ trace, target.mass next * ((traceLaw next).mass trace *
        (selection next trace).mass current) := by
      simpa using Equiv.sum_comp (reverseTrace current next)
        (fun trace => target.mass next * ((traceLaw next).mass trace *
          (selection next trace).mass current))

/-- Consequently, a fully reversed rooted random-trace construction preserves
the target even when its raw candidate rows fail the simpler reroot checker. -/
theorem rootedTraceKernel_stationary
    (target : Distribution State)
    (traceLaw : State → Distribution Trace)
    (selection : State → Trace → Distribution State)
    (reverseTrace : State → State → Trace ≃ Trace)
    (hreverse : ∀ current next trace,
      target.mass current * ((traceLaw current).mass trace *
          (selection current trace).mass next) =
        target.mass next *
          ((traceLaw next).mass (reverseTrace current next trace) *
          (selection next (reverseTrace current next trace)).mass current)) :
    (rootedTraceKernel traceLaw selection).Stationary target :=
  (rootedTraceKernel_reversible target traceLaw selection reverseTrace
    hreverse).stationary

/-- Proof-bearing interface for a finite root-dependent dynamic sampler. Unlike
`CertifiedDynamicTree`, this certificate permits different candidate rows at
different roots, but it must retain the complete construction trace and prove
the stronger target-weighted reversal identity. -/
structure CertifiedRootedTraceSampler (target : Distribution State)
    (Trace : Type*) [Fintype Trace] where
  traceLaw : State → Distribution Trace
  selection : State → Trace → Distribution State
  reverseTrace : State → State → Trace ≃ Trace
  reverse_weight : ∀ current next trace,
    target.mass current * ((traceLaw current).mass trace *
        (selection current trace).mass next) =
      target.mass next *
        ((traceLaw next).mass (reverseTrace current next trace) *
        (selection next (reverseTrace current next trace)).mass current)

noncomputable def CertifiedRootedTraceSampler.kernel
    {target : Distribution State} (sampler : CertifiedRootedTraceSampler target Trace) :
    MarkovKernel State :=
  rootedTraceKernel sampler.traceLaw sampler.selection

theorem CertifiedRootedTraceSampler.reversible
    {target : Distribution State} (sampler : CertifiedRootedTraceSampler target Trace) :
    sampler.kernel.Reversible target :=
  rootedTraceKernel_reversible target sampler.traceLaw sampler.selection
    sampler.reverseTrace sampler.reverse_weight

theorem CertifiedRootedTraceSampler.stationary
    {target : Distribution State} (sampler : CertifiedRootedTraceSampler target Trace) :
    sampler.kernel.Stationary target :=
  sampler.reversible.stationary

/-! ### Factorized reversal certificates

Recursive trajectory builders usually compute their trace probability as a
product of local random choices, and then select an endpoint with a separate
conditional probability.  The following interface splits the reversal
obligation along exactly that implementation boundary.  This avoids hiding
the construction probability inside a single opaque balance hypothesis.
-/

/-- A factorized rooted-trace certificate separates reversal of the trace
construction law from reversal of the conditional endpoint selection.  The
`constructionRatio` is an arbitrary nonnegative bridge factor: in a NUTS
instantiation it records the product of reversed direction, subtree, and
multinomial-choice probabilities. -/
structure FactorizedRootedTraceSampler (target : Distribution State)
    (Trace : Type*) [Fintype Trace] where
  traceLaw : State → Distribution Trace
  selection : State → Trace → Distribution State
  reverseTrace : State → State → Trace ≃ Trace
  constructionRatio : State → State → Trace → ℝ
  constructionRatio_nonneg : ∀ current next trace,
    0 ≤ constructionRatio current next trace
  construction_reverse : ∀ current next trace,
    (traceLaw current).mass trace =
      constructionRatio current next trace *
        (traceLaw next).mass (reverseTrace current next trace)
  selection_reverse : ∀ current next trace,
    target.mass current *
        (constructionRatio current next trace *
          (selection current trace).mass next) =
      target.mass next *
        (selection next (reverseTrace current next trace)).mass current

/-- Combining the two local reversal identities gives the complete
target-weighted trace reversal required by `CertifiedRootedTraceSampler`. -/
noncomputable def FactorizedRootedTraceSampler.toCertified
    {target : Distribution State}
    (sampler : FactorizedRootedTraceSampler target Trace) :
    CertifiedRootedTraceSampler target Trace where
  traceLaw := sampler.traceLaw
  selection := sampler.selection
  reverseTrace := sampler.reverseTrace
  reverse_weight := by
    intro current next trace
    rw [sampler.construction_reverse]
    calc
      target.mass current *
          ((sampler.constructionRatio current next trace *
              (sampler.traceLaw next).mass
                (sampler.reverseTrace current next trace)) *
            (sampler.selection current trace).mass next) =
        (sampler.traceLaw next).mass
            (sampler.reverseTrace current next trace) *
          (target.mass current *
            (sampler.constructionRatio current next trace *
              (sampler.selection current trace).mass next)) := by
          ac_rfl
      _ = (sampler.traceLaw next).mass
            (sampler.reverseTrace current next trace) *
          (target.mass next *
            (sampler.selection next
              (sampler.reverseTrace current next trace)).mass current) := by
          rw [sampler.selection_reverse]
      _ = target.mass next *
          ((sampler.traceLaw next).mass
              (sampler.reverseTrace current next trace) *
            (sampler.selection next
              (sampler.reverseTrace current next trace)).mass current) := by
          ac_rfl

/-- The kernel implemented from a factorized trace certificate is reversible. -/
theorem FactorizedRootedTraceSampler.reversible
    {target : Distribution State}
    (sampler : FactorizedRootedTraceSampler target Trace) :
    (sampler.toCertified.kernel).Reversible target :=
  sampler.toCertified.reversible

/-- The kernel implemented from a factorized trace certificate preserves the
target distribution. -/
theorem FactorizedRootedTraceSampler.stationary
    {target : Distribution State}
    (sampler : FactorizedRootedTraceSampler target Trace) :
    (sampler.toCertified.kernel).Stationary target :=
  sampler.toCertified.stationary

/-! ### Normalized endpoint selection within a complete trace -/

/-- Total unnormalized endpoint weight exposed by a complete rooted trace. -/
noncomputable def traceSelectionNormalizer
    (weight : State → Trace → State → ℝ) (current : State)
    (trace : Trace) : ℝ :=
  ∑ next, weight current trace next

/-- Proof-bearing endpoint weights for a reversed complete trace. Unlike the
candidate-row checker, this permits the raw rooted rows to differ: only the
particular forward trace and its reversed trace must have matching total
weight and target-weighted endpoint flow. -/
structure ReversibleTraceSelection (target : Distribution State)
    (Trace : Type*) [Fintype Trace]
    (reverseTrace : State → State → Trace ≃ Trace)
    (constructionRatio : State → State → Trace → ℝ) where
  weight : State → Trace → State → ℝ
  weight_nonneg : ∀ current trace next, 0 ≤ weight current trace next
  normalizer_pos : ∀ current trace,
    0 < traceSelectionNormalizer weight current trace
  normalizer_reverse : ∀ current next trace,
    traceSelectionNormalizer weight current trace =
      traceSelectionNormalizer weight next (reverseTrace current next trace)
  endpoint_flow_reverse : ∀ current next trace,
    target.mass current *
        (constructionRatio current next trace * weight current trace next) =
      target.mass next *
        weight next (reverseTrace current next trace) current

/-- Normalize the endpoint weights of a complete trace. -/
noncomputable def ReversibleTraceSelection.distribution
    {target : Distribution State}
    {reverseTrace : State → State → Trace ≃ Trace}
    {constructionRatio : State → State → Trace → ℝ}
    (selection : ReversibleTraceSelection target Trace reverseTrace
      constructionRatio)
    (current : State) (trace : Trace) : Distribution State where
  mass next := selection.weight current trace next /
    traceSelectionNormalizer selection.weight current trace
  nonneg next := div_nonneg (selection.weight_nonneg current trace next)
    (selection.normalizer_pos current trace).le
  sum_mass := by
    rw [← Finset.sum_div]
    exact div_self (selection.normalizer_pos current trace).ne'

/-- Normalized endpoint selection satisfies the conditional reversal identity
needed by a factorized rooted-trace sampler. -/
theorem ReversibleTraceSelection.distribution_reverse
    {target : Distribution State}
    {reverseTrace : State → State → Trace ≃ Trace}
    {constructionRatio : State → State → Trace → ℝ}
    (selection : ReversibleTraceSelection target Trace reverseTrace
      constructionRatio) (current next : State) (trace : Trace) :
    target.mass current *
        (constructionRatio current next trace *
          (selection.distribution current trace).mass next) =
      target.mass next *
        (selection.distribution next
          (reverseTrace current next trace)).mass current := by
  simp only [ReversibleTraceSelection.distribution]
  rw [← selection.normalizer_reverse current next trace]
  simp only [div_eq_mul_inv]
  calc
    target.mass current *
        (constructionRatio current next trace *
          (selection.weight current trace next *
            (traceSelectionNormalizer selection.weight current trace)⁻¹)) =
      (target.mass current *
        (constructionRatio current next trace *
          selection.weight current trace next)) *
        (traceSelectionNormalizer selection.weight current trace)⁻¹ := by
          ac_rfl
    _ = (target.mass next *
          selection.weight next (reverseTrace current next trace) current) *
        (traceSelectionNormalizer selection.weight current trace)⁻¹ := by
          rw [selection.endpoint_flow_reverse]
    _ = target.mass next *
        (selection.weight next (reverseTrace current next trace) current *
          (traceSelectionNormalizer selection.weight current trace)⁻¹) := by
          ac_rfl

/-- Attach normalized trace endpoint weights to a factorized construction
law. This is the final generic assembly theorem needed by a finite standard-
NUTS trace instantiation. -/
noncomputable def FactorizedRootedTraceSampler.withTraceSelection
    (target : Distribution State) (traceLaw : State → Distribution Trace)
    (reverseTrace : State → State → Trace ≃ Trace)
    (constructionRatio : State → State → Trace → ℝ)
    (constructionRatio_nonneg : ∀ current next trace,
      0 ≤ constructionRatio current next trace)
    (construction_reverse : ∀ current next trace,
      (traceLaw current).mass trace =
        constructionRatio current next trace *
          (traceLaw next).mass (reverseTrace current next trace))
    (selection : ReversibleTraceSelection target Trace reverseTrace
      constructionRatio) : FactorizedRootedTraceSampler target Trace where
  traceLaw := traceLaw
  selection := selection.distribution
  reverseTrace := reverseTrace
  constructionRatio := constructionRatio
  constructionRatio_nonneg := constructionRatio_nonneg
  construction_reverse := construction_reverse
  selection_reverse := selection.distribution_reverse

/-! ### Recursive products of local random choices -/

/-- A construction law assembled from finitely many local random choices.
Each local factor has its own reversal ratio.  This is the interface used by
a recursive dynamic-tree implementation: the index may encode direction
coins, subtree-retention coins, and streaming candidate-selection coins. -/
structure LocalChoiceRootedTraceSampler (target : Distribution State)
    (Trace Index : Type*) [Fintype Trace] [Fintype Index] where
  traceLaw : State → Distribution Trace
  selection : State → Trace → Distribution State
  reverseTrace : State → State → Trace ≃ Trace
  localWeight : State → Trace → Index → ℝ
  localRatio : State → State → Trace → Index → ℝ
  localRatio_nonneg : ∀ current next trace index,
    0 ≤ localRatio current next trace index
  trace_factorization : ∀ current trace,
    (traceLaw current).mass trace = ∏ index, localWeight current trace index
  local_reverse : ∀ current next trace index,
    localWeight current trace index =
      localRatio current next trace index *
        localWeight next (reverseTrace current next trace) index
  selection_reverse : ∀ current next trace,
    target.mass current *
        ((∏ index, localRatio current next trace index) *
          (selection current trace).mass next) =
      target.mass next *
        (selection next (reverseTrace current next trace)).mass current

/-- Multiplying the local reversal equations yields the global construction
ratio required by `FactorizedRootedTraceSampler`. -/
noncomputable def LocalChoiceRootedTraceSampler.toFactorized
    {Index : Type*} [Fintype Index] {target : Distribution State}
    (sampler : LocalChoiceRootedTraceSampler target Trace Index) :
    FactorizedRootedTraceSampler target Trace where
  traceLaw := sampler.traceLaw
  selection := sampler.selection
  reverseTrace := sampler.reverseTrace
  constructionRatio current next trace :=
    ∏ index, sampler.localRatio current next trace index
  constructionRatio_nonneg := by
    intro current next trace
    classical
    induction (Finset.univ : Finset Index) using Finset.induction_on with
    | empty => simp
    | @insert index indices hnotmem ih =>
        rw [Finset.prod_insert hnotmem]
        exact mul_nonneg
          (sampler.localRatio_nonneg current next trace index) ih
  construction_reverse := by
    intro current next trace
    rw [sampler.trace_factorization, sampler.trace_factorization]
    calc
      ∏ index, sampler.localWeight current trace index =
          ∏ index, sampler.localRatio current next trace index *
            sampler.localWeight next
              (sampler.reverseTrace current next trace) index := by
        apply Finset.prod_congr rfl
        intro index _
        exact sampler.local_reverse current next trace index
      _ = (∏ index, sampler.localRatio current next trace index) *
          ∏ index, sampler.localWeight next
            (sampler.reverseTrace current next trace) index := by
        rw [Finset.prod_mul_distrib]
  selection_reverse := sampler.selection_reverse

/-- A recursive product of locally reversed choices therefore defines a
reversible rooted-trace sampler. -/
theorem LocalChoiceRootedTraceSampler.reversible
    {Index : Type*} [Fintype Index] {target : Distribution State}
    (sampler : LocalChoiceRootedTraceSampler target Trace Index) :
    (sampler.toFactorized.toCertified.kernel).Reversible target :=
  sampler.toFactorized.reversible

/-- A recursive product of locally reversed choices preserves its target. -/
theorem LocalChoiceRootedTraceSampler.stationary
    {Index : Type*} [Fintype Index] {target : Distribution State}
    (sampler : LocalChoiceRootedTraceSampler target Trace Index) :
    (sampler.toFactorized.toCertified.kernel).Stationary target :=
  sampler.toFactorized.stationary

/-! ### Uniform finite-depth direction traces -/

/-- The law of `depth` independent fair direction choices used by a bounded
doubling recursion. -/
noncomputable def uniformDirectionTraceLaw (depth : ℕ) :
    Distribution (Fin depth → Bool) where
  mass _ := ((2 : ℝ) ^ depth)⁻¹
  nonneg _ := inv_nonneg.mpr (pow_nonneg (by norm_num) _)
  sum_mass := by
    rw [Finset.sum_const]
    simp

/-- Uniform direction traces have the same mass after every bijective trace
reversal, including the endpoint-dependent reversal required by NUTS. -/
@[simp] theorem uniformDirectionTraceLaw_reverse_mass
    (depth : ℕ) (reverse : (Fin depth → Bool) ≃ (Fin depth → Bool))
    (trace : Fin depth → Bool) :
    (uniformDirectionTraceLaw depth).mass (reverse trace) =
      (uniformDirectionTraceLaw depth).mass trace := by
  rfl

/-- A bounded doubling sampler with fair direction coins is certified once
conditional endpoint selection satisfies the target-weighted reroot identity.
Thus the direction-coin part of standard NUTS is discharged here; subtree
validity and candidate-selection reversal remain explicit in `hselection`. -/
noncomputable def uniformDirectionRootedTraceSampler
    (target : Distribution State) (depth : ℕ)
    (selection : State → (Fin depth → Bool) → Distribution State)
    (reverseTrace : State → State →
      (Fin depth → Bool) ≃ (Fin depth → Bool))
    (hselection : ∀ current next trace,
      target.mass current * (selection current trace).mass next =
        target.mass next *
          (selection next (reverseTrace current next trace)).mass current) :
    FactorizedRootedTraceSampler target (Fin depth → Bool) where
  traceLaw _ := uniformDirectionTraceLaw depth
  selection := selection
  reverseTrace := reverseTrace
  constructionRatio _ _ _ := 1
  constructionRatio_nonneg := by intros; norm_num
  construction_reverse := by intros; simp
  selection_reverse := by
    intro current next trace
    simpa using hselection current next trace

/-- Stationarity wrapper for a uniformly randomized bounded doubling trace. -/
theorem uniformDirectionRootedTraceKernel_stationary
    (target : Distribution State) (depth : ℕ)
    (selection : State → (Fin depth → Bool) → Distribution State)
    (reverseTrace : State → State →
      (Fin depth → Bool) ≃ (Fin depth → Bool))
    (hselection : ∀ current next trace,
      target.mass current * (selection current trace).mass next =
        target.mass next *
          (selection next (reverseTrace current next trace)).mass current) :
    ((uniformDirectionRootedTraceSampler target depth selection reverseTrace
      hselection).toCertified.kernel).Stationary target :=
  (uniformDirectionRootedTraceSampler target depth selection reverseTrace
    hselection).stationary

/-! ### Streaming candidate selection

Algorithm 3 of Hoffman--Gelman does not materialize the complete candidate
set.  Each recursive subtree returns one representative and its eligible
count; representatives are merged with probability proportional to those
counts.  The following exact distribution is that merge operation.
-/

/-- Merge representatives from two recursive subtrees with probability
proportional to their nonnegative total candidate weights. -/
noncomputable def weightedMergeDistribution
    (left right : Distribution State) (leftWeight rightWeight : ℝ)
    (hleft : 0 ≤ leftWeight) (hright : 0 ≤ rightWeight)
    (htotal : 0 < leftWeight + rightWeight) : Distribution State where
  mass state :=
    (leftWeight * left.mass state + rightWeight * right.mass state) /
      (leftWeight + rightWeight)
  nonneg state := div_nonneg
    (add_nonneg (mul_nonneg hleft (left.nonneg state))
      (mul_nonneg hright (right.nonneg state))) htotal.le
  sum_mass := by
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    simp_rw [← Finset.mul_sum, left.sum_mass, right.sum_mass, mul_one]
    exact div_self htotal.ne'

@[simp] theorem weightedMergeDistribution_mass
    (left right : Distribution State) (leftWeight rightWeight : ℝ)
    (hleft : 0 ≤ leftWeight) (hright : 0 ≤ rightWeight)
    (htotal : 0 < leftWeight + rightWeight) (state : State) :
    (weightedMergeDistribution left right leftWeight rightWeight hleft hright
      htotal).mass state =
      (leftWeight * left.mass state + rightWeight * right.mass state) /
        (leftWeight + rightWeight) := rfl

/-- Count-proportional recursive merging preserves the normalized combined
endpoint weights.  For indicator weights this is precisely the paper's
incremental uniform-selection argument. -/
theorem weightedMergeDistribution_mass_of_normalized_weights
    (left right : Distribution State) (leftWeight rightWeight : ℝ)
    (hleft : 0 < leftWeight) (hright : 0 < rightWeight)
    (leftEndpointWeight rightEndpointWeight : State → ℝ)
    (hleftMass : ∀ state,
      left.mass state = leftEndpointWeight state / leftWeight)
    (hrightMass : ∀ state,
      right.mass state = rightEndpointWeight state / rightWeight)
    (state : State) :
    (weightedMergeDistribution left right leftWeight rightWeight hleft.le
      hright.le (add_pos hleft hright)).mass state =
      (leftEndpointWeight state + rightEndpointWeight state) /
        (leftWeight + rightWeight) := by
  simp only [weightedMergeDistribution_mass, hleftMass, hrightMass]
  field_simp [hleft.ne', hright.ne']

/-- Recursive count-proportional selection is independent of binary-tree
parenthesization.  Hence streaming `BuildTree` selection has the same law as
one weighted selection over all completed subtree leaves. -/
theorem weightedMergeDistribution_assoc
    (first second third : Distribution State)
    (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hab : 0 < a + b) (hbc : 0 < b + c)
    (habc : 0 < a + b + c) :
    weightedMergeDistribution
        (weightedMergeDistribution first second a b ha hb hab) third
        (a + b) c hab.le hc habc =
      weightedMergeDistribution first
        (weightedMergeDistribution second third b c hb hc hbc)
        a (b + c) ha hbc.le (by simpa [add_assoc] using habc) := by
  apply Distribution.ext
  funext state
  simp only [weightedMergeDistribution_mass]
  field_simp [hab.ne', hbc.ne', habc.ne']
  ring

/-- Total streaming merge used when a recursive subtree contains no eligible
leaf. If the combined count is zero the representative is semantically dead,
so the left dummy law is retained; every later positive-count merge gives it
zero probability. -/
noncomputable def totalWeightedMergeDistribution
    (left right : Distribution State) (leftWeight rightWeight : ℝ)
    (hleft : 0 ≤ leftWeight) (hright : 0 ≤ rightWeight) :
    Distribution State :=
  if htotal : 0 < leftWeight + rightWeight then
    weightedMergeDistribution left right leftWeight rightWeight hleft hright
      htotal
  else
    left

/-- A zero-count left subtree is ignored when the right subtree is nonempty. -/
@[simp] theorem totalWeightedMergeDistribution_zero_left
    (left right : Distribution State) (rightWeight : ℝ)
    (hright : 0 < rightWeight) :
    totalWeightedMergeDistribution left right 0 rightWeight (by norm_num)
      hright.le = right := by
  rw [totalWeightedMergeDistribution, dif_pos (by simpa using hright)]
  apply Distribution.ext
  funext state
  simp [weightedMergeDistribution, hright.ne']

/-- A zero-count right subtree is ignored when the left subtree is nonempty. -/
@[simp] theorem totalWeightedMergeDistribution_zero_right
    (left right : Distribution State) (leftWeight : ℝ)
    (hleft : 0 < leftWeight) :
    totalWeightedMergeDistribution left right leftWeight 0 hleft.le
      (by norm_num) = left := by
  rw [totalWeightedMergeDistribution, dif_pos (by simpa using hleft)]
  apply Distribution.ext
  funext state
  simp [weightedMergeDistribution, hleft.ne']

/-- With two empty subtrees the total merge retains its declared dummy law. -/
@[simp] theorem totalWeightedMergeDistribution_zero_zero
    (left right : Distribution State) :
    totalWeightedMergeDistribution left right 0 0 (by norm_num) (by norm_num) =
      left := by
  simp [totalWeightedMergeDistribution]

/-- When the combined count is positive, the total operation is exactly the
paper's count-proportional representative merge. -/
theorem totalWeightedMergeDistribution_of_total_pos
    (left right : Distribution State) (leftWeight rightWeight : ℝ)
    (hleft : 0 ≤ leftWeight) (hright : 0 ≤ rightWeight)
    (htotal : 0 < leftWeight + rightWeight) :
    totalWeightedMergeDistribution left right leftWeight rightWeight hleft
      hright =
      weightedMergeDistribution left right leftWeight rightWeight hleft hright
        htotal := by
  simp [totalWeightedMergeDistribution, htotal]

/-- The normalized-union law remains valid with zero-count subtrees. Their
endpoint-weight function must be identically zero, but their dummy
representative distribution is otherwise irrelevant. -/
theorem totalWeightedMergeDistribution_mass_of_normalized_weights
    (left right : Distribution State) (leftWeight rightWeight : ℝ)
    (hleft : 0 ≤ leftWeight) (hright : 0 ≤ rightWeight)
    (htotal : 0 < leftWeight + rightWeight)
    (leftEndpointWeight rightEndpointWeight : State → ℝ)
    (hleftZero : leftWeight = 0 → ∀ state, leftEndpointWeight state = 0)
    (hrightZero : rightWeight = 0 → ∀ state, rightEndpointWeight state = 0)
    (hleftMass : 0 < leftWeight → ∀ state,
      left.mass state = leftEndpointWeight state / leftWeight)
    (hrightMass : 0 < rightWeight → ∀ state,
      right.mass state = rightEndpointWeight state / rightWeight)
    (state : State) :
    (totalWeightedMergeDistribution left right leftWeight rightWeight hleft
      hright).mass state =
      (leftEndpointWeight state + rightEndpointWeight state) /
        (leftWeight + rightWeight) := by
  rcases hleft.eq_or_lt with rfl | hleftpos
  · have hrightpos : 0 < rightWeight := by simpa using htotal
    simp [hrightpos, hleftZero rfl state, hrightMass hrightpos state]
  · rcases hright.eq_or_lt with rfl | hrightpos
    · simp [hleftpos, hrightZero rfl state, hleftMass hleftpos state]
    · rw [totalWeightedMergeDistribution_of_total_pos _ _ _ _ hleft hright
        htotal]
      exact weightedMergeDistribution_mass_of_normalized_weights left right
        leftWeight rightWeight hleftpos hrightpos leftEndpointWeight
        rightEndpointWeight (hleftMass hleftpos) (hrightMass hrightpos) state

/-- Total recursive selection is associative even when any completed subtree
has zero eligible leaves. Thus skipped subtrees cannot change the final
representative law. -/
theorem totalWeightedMergeDistribution_assoc
    (first second third : Distribution State)
    (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    totalWeightedMergeDistribution
        (totalWeightedMergeDistribution first second a b ha hb) third
        (a + b) c (add_nonneg ha hb) hc =
      totalWeightedMergeDistribution first
        (totalWeightedMergeDistribution second third b c hb hc)
        a (b + c) ha (add_nonneg hb hc) := by
  rcases ha.eq_or_lt with rfl | hapos
  · rcases hb.eq_or_lt with rfl | hbpos
    · rcases hc.eq_or_lt with rfl | hcpos
      ·
        simp
      · simp [hcpos]
    · have hbcpos : 0 < b + c := lt_of_lt_of_le hbpos (le_add_of_nonneg_right hc)
      simp [hbpos, hbcpos]
  · rcases hb.eq_or_lt with rfl | hbpos
    · rcases hc.eq_or_lt with rfl | hcpos
      ·
        simp [hapos]
      · simp [hapos, hcpos]
    · rcases hc.eq_or_lt with rfl | hcpos
      ·
        simp [hbpos, add_pos hapos hbpos]
      · rw [totalWeightedMergeDistribution_of_total_pos _ _ _ _ ha hb
          (add_pos hapos hbpos)]
        rw [totalWeightedMergeDistribution_of_total_pos _ _ _ _
          (add_nonneg ha hb) hc (add_pos (add_pos hapos hbpos) hcpos)]
        rw [totalWeightedMergeDistribution_of_total_pos _ _ _ _ hb hc
          (add_pos hbpos hcpos)]
        rw [totalWeightedMergeDistribution_of_total_pos _ _ _ _ ha
          (add_nonneg hb hc) (by simpa [add_assoc] using
            (add_pos (add_pos hapos hbpos) hcpos))]
        exact weightedMergeDistribution_assoc first second third a b c ha hb hc
          (add_pos hapos hbpos) (add_pos hbpos hcpos)
          (add_pos (add_pos hapos hbpos) hcpos)

end Mcmc.Finite.MarkovKernel
