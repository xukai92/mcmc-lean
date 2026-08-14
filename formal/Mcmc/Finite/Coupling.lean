import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mcmc.Kernel.Coupling

/-!
# Couplings of finite categorical distributions

This module begins the finite categorical coupling layer used for trajectory
indices in multinomial HMC. It stays on mathlib's `PMF` API and connects its
marginal equations to the general measure-coupling interface.
-/

open MeasureTheory

namespace Mcmc
namespace Finite

variable {α β : Type*}

/-- A probability mass function on a product is a coupling when its mapped
coordinate distributions are the requested marginals. -/
def IsPMFCoupling (joint : PMF (α × β)) (left : PMF α) (right : PMF β) : Prop :=
  joint.map Prod.fst = left ∧ joint.map Prod.snd = right

namespace IsPMFCoupling

theorem fst {joint : PMF (α × β)} {left : PMF α} {right : PMF β}
    (h : IsPMFCoupling joint left right) : joint.map Prod.fst = left :=
  h.1

theorem snd {joint : PMF (α × β)} {left : PMF α} {right : PMF β}
    (h : IsPMFCoupling joint left right) : joint.map Prod.snd = right :=
  h.2

/-- Pointwise row-sum form of the first marginal equation. -/
theorem sum_right [Fintype α] [Fintype β]
    {joint : PMF (α × β)} {left : PMF α} {right : PMF β}
    (h : IsPMFCoupling joint left right) (x : α) :
    ∑ y, joint (x, y) = left x := by
  classical
  have hx := congrArg (fun r : PMF α => r x) h.fst
  rw [PMF.map_apply, ENNReal.tsum_prod'] at hx
  simp only [tsum_fintype] at hx
  have hcollapse :
      (∑ a : α, ∑ b : β, if x = a then joint (a, b) else 0) =
        ∑ b : β, joint (x, b) := by
    rw [Finset.sum_eq_single x]
    · simp
    · intro a _ hax
      simp [Ne.symm hax]
    · simp
  rw [hcollapse] at hx
  exact hx

/-- Pointwise column-sum form of the second marginal equation. -/
theorem sum_left [Fintype α] [Fintype β]
    {joint : PMF (α × β)} {left : PMF α} {right : PMF β}
    (h : IsPMFCoupling joint left right) (y : β) :
    ∑ x, joint (x, y) = right y := by
  classical
  have hy := congrArg (fun r : PMF β => r y) h.snd
  rw [PMF.map_apply, ENNReal.tsum_prod'] at hy
  simp only [tsum_fintype] at hy
  have hinner (a : α) :
      (∑ b : β, if y = b then joint (a, b) else 0) = joint (a, y) := by
    rw [Finset.sum_eq_single y]
    · simp
    · intro b _ hby
      simp [Ne.symm hby]
    · simp
  simp_rw [hinner] at hy
  exact hy

/-- A PMF coupling is a coupling in the general mathlib `Measure` interface. -/
theorem toMeasure [MeasurableSpace α] [MeasurableSpace β]
    {joint : PMF (α × β)} {left : PMF α} {right : PMF β}
    (h : IsPMFCoupling joint left right) :
    IsMeasureCoupling joint.toMeasure left.toMeasure right.toMeasure := by
  constructor
  · change joint.toMeasure.map Prod.fst = left.toMeasure
    rw [PMF.toMeasure_map (f := Prod.fst) joint measurable_fst, h.fst]
  · change joint.toMeasure.map Prod.snd = right.toMeasure
    rw [PMF.toMeasure_map (f := Prod.snd) joint measurable_snd, h.snd]

end IsPMFCoupling

/-- The common mass of two finite categorical distributions. -/
noncomputable def overlap [Fintype α] (p q : PMF α) : ENNReal :=
  ∑ x, min (p x) (q x)

/-- Mass of `p` left after removing its pointwise overlap with `q`. -/
noncomputable def leftResidual (p q : PMF α) (x : α) : ENNReal :=
  p x - min (p x) (q x)

/-- Mass of `q` left after removing its pointwise overlap with `p`. -/
noncomputable def rightResidual (p q : PMF α) (x : α) : ENNReal :=
  q x - min (p x) (q x)

/-- Total variation distance for finite categorical distributions, expressed
as one minus their common mass. -/
noncomputable def totalVariation [Fintype α] (p q : PMF α) : ENNReal :=
  1 - overlap p q

theorem overlap_le_one [Fintype α] (p q : PMF α) : overlap p q ≤ 1 := by
  calc
    overlap p q ≤ ∑ x, p x := by
      apply Finset.sum_le_sum
      intro x _
      exact min_le_left _ _
    _ = ∑' x, p x := by rw [tsum_fintype]
    _ = 1 := p.tsum_coe

@[simp]
theorem overlap_self [Fintype α] (p : PMF α) : overlap p p = 1 := by
  rw [overlap]
  simp only [min_self]
  calc
    ∑ x, p x = ∑' x, p x := by rw [tsum_fintype]
    _ = 1 := p.tsum_coe

theorem residual_eq_zero_or_eq_zero (p q : PMF α) (x : α) :
    leftResidual p q x = 0 ∨ rightResidual p q x = 0 := by
  rcases le_total (p x) (q x) with h | h
  · left
    simp [leftResidual, min_eq_left h]
  · right
    simp [rightResidual, min_eq_right h]

theorem residual_mul_self_eq_zero (p q : PMF α) (x : α) :
    leftResidual p q x * rightResidual p q x = 0 := by
  rcases residual_eq_zero_or_eq_zero p q x with h | h
  · simp [h]
  · simp [h]

/-- Finite-valued truncated subtraction distributes over a finite sum when
the subtrahend is pointwise bounded by the minuend. -/
theorem sum_tsub_eq_tsub_sum [Fintype α]
    (f g : α → ENNReal)
    (hfinite : ∀ x, f x ≠ ⊤)
    (hle : ∀ x, g x ≤ f x) :
    ∑ x, (f x - g x) = (∑ x, f x) - ∑ x, g x := by
  have hgfinite : ∀ x, g x ≠ ⊤ := fun x =>
    ne_top_of_le_ne_top (hfinite x) (hle x)
  have hlhs : (∑ x, (f x - g x)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun x _ => ENNReal.sub_ne_top (hfinite x)
  have hrhs : (∑ x, f x) - ∑ x, g x ≠ ⊤ :=
    ENNReal.sub_ne_top (ENNReal.sum_ne_top.mpr fun x _ => hfinite x)
  apply (ENNReal.toReal_eq_toReal_iff' hlhs hrhs).mp
  rw [ENNReal.toReal_sum (fun x _ => ENNReal.sub_ne_top (hfinite x))]
  simp_rw [ENNReal.toReal_sub_of_le (hle _) (hfinite _)]
  rw [ENNReal.toReal_sub_of_le (Finset.sum_le_sum fun x _ => hle x)
      (ENNReal.sum_ne_top.mpr fun x _ => hfinite x),
    ENNReal.toReal_sum (fun x _ => hfinite x),
    ENNReal.toReal_sum (fun x _ => hgfinite x),
    Finset.sum_sub_distrib]

theorem sum_leftResidual [Fintype α] (p q : PMF α) :
    ∑ x, leftResidual p q x = 1 - overlap p q := by
  simp only [leftResidual]
  rw [overlap, sum_tsub_eq_tsub_sum]
  · have hp : ∑ x, p x = 1 := by
      calc
        ∑ x, p x = ∑' x, p x := by rw [tsum_fintype]
        _ = 1 := p.tsum_coe
    rw [hp]
  · exact p.apply_ne_top
  · exact fun x => min_le_left _ _

theorem sum_rightResidual [Fintype α] (p q : PMF α) :
    ∑ x, rightResidual p q x = 1 - overlap p q := by
  simp only [rightResidual]
  rw [overlap, sum_tsub_eq_tsub_sum]
  · have hq : ∑ x, q x = 1 := by
      calc
        ∑ x, q x = ∑' x, q x := by rw [tsum_fintype]
        _ = 1 := q.tsum_coe
    rw [hq]
  · exact q.apply_ne_top
  · exact fun x => min_le_right _ _

/-- The left residual is the positive part of the pointwise mass difference. -/
theorem leftResidual_eq_tsub (p q : PMF α) (x : α) :
    leftResidual p q x = p x - q x := by
  unfold leftResidual
  rcases le_total (p x) (q x) with h | h
  · rw [min_eq_left h, tsub_self, tsub_eq_zero_of_le h]
  · rw [min_eq_right h]

/-- Total variation is bounded by any pointwise upper bound on the positive
mass differences.  This is the finite interface used for multinomial
trajectory-weight estimates. -/
theorem totalVariation_le_sum_of_le_add [Fintype α]
    (p q : PMF α) (δ : α → ENNReal)
    (h : ∀ x, p x ≤ q x + δ x) :
    totalVariation p q ≤ ∑ x, δ x := by
  rw [totalVariation, ← sum_leftResidual]
  apply Finset.sum_le_sum
  intro x hx
  rw [leftResidual_eq_tsub]
  exact tsub_le_iff_left.mpr (by simpa [add_comm] using h x)

/-- A uniform pointwise probability error bounds total variation by the
number of categories times that error. -/
theorem totalVariation_le_card_mul_of_le_add [Fintype α]
    (p q : PMF α) (δ : ENNReal)
    (h : ∀ x, p x ≤ q x + δ) :
    totalVariation p q ≤ Fintype.card α * δ := by
  apply le_trans (totalVariation_le_sum_of_le_add p q (fun _ => δ) h)
  simp

/-- A common multiplicative domination factor gives a dimension-free total
variation bound.  In applications, an energy error `r` typically supplies
`c = exp r`. -/
theorem totalVariation_le_tsub_one_of_le_mul [Fintype α]
    (p q : PMF α) (c : ENNReal) (hc : 1 ≤ c)
    (h : ∀ x, p x ≤ c * q x) :
    totalVariation p q ≤ c - 1 := by
  have hpoint : ∀ x, p x ≤ q x + (c - 1) * q x := by
    intro x
    apply le_trans (h x)
    calc
      c * q x = ((c - 1) + 1) * q x := by
        rw [tsub_add_cancel_of_le hc]
      _ ≤ q x + (c - 1) * q x := by
        rw [add_mul, one_mul, add_comm]
  apply le_trans
    (totalVariation_le_sum_of_le_add p q (fun x => (c - 1) * q x) hpoint)
  calc
    ∑ x, (c - 1) * q x = (c - 1) * ∑ x, q x := by
      rw [Finset.mul_sum]
    _ ≤ c - 1 := by
      rw [show ∑ x, q x = 1 by
        calc
          ∑ x, q x = ∑' x, q x := by rw [tsum_fintype]
          _ = 1 := q.tsum_coe, mul_one]

theorem tsum_leftResidual [Fintype α] (p q : PMF α) :
    ∑' x, leftResidual p q x = 1 - overlap p q := by
  rw [tsum_fintype, sum_leftResidual]

theorem tsum_rightResidual [Fintype α] (p q : PMF α) :
    ∑' x, rightResidual p q x = 1 - overlap p q := by
  rw [tsum_fintype, sum_rightResidual]

theorem one_sub_overlap_ne_zero [Fintype α] (p q : PMF α)
    (h : overlap p q ≠ 1) :
    1 - overlap p q ≠ 0 := by
  intro hz
  have hone_le : 1 ≤ overlap p q := tsub_eq_zero_iff_le.mp hz
  exact h (le_antisymm (overlap_le_one p q) hone_le)

/-- The normalized residual of the left marginal, available whenever the
two distributions do not have full overlap. -/
noncomputable def leftResidualPMF [Fintype α]
    (p q : PMF α) (h : overlap p q ≠ 1) : PMF α :=
  PMF.normalize (leftResidual p q)
    (by rw [tsum_leftResidual]; exact one_sub_overlap_ne_zero p q h)
    (by rw [tsum_leftResidual]; exact ENNReal.sub_ne_top ENNReal.one_ne_top)

/-- The normalized residual of the right marginal. -/
noncomputable def rightResidualPMF [Fintype α]
    (p q : PMF α) (h : overlap p q ≠ 1) : PMF α :=
  PMF.normalize (rightResidual p q)
    (by rw [tsum_rightResidual]; exact one_sub_overlap_ne_zero p q h)
    (by rw [tsum_rightResidual]; exact ENNReal.sub_ne_top ENNReal.one_ne_top)

@[simp]
theorem leftResidualPMF_apply [Fintype α]
    (p q : PMF α) (h : overlap p q ≠ 1) (x : α) :
    leftResidualPMF p q h x =
      leftResidual p q x * (1 - overlap p q)⁻¹ := by
  rw [leftResidualPMF, PMF.normalize_apply, tsum_leftResidual]

@[simp]
theorem rightResidualPMF_apply [Fintype α]
    (p q : PMF α) (h : overlap p q ≠ 1) (x : α) :
    rightResidualPMF p q h x =
      rightResidual p q x * (1 - overlap p q)⁻¹ := by
  rw [rightResidualPMF, PMF.normalize_apply, tsum_rightResidual]

theorem residualPMF_mul_self_eq_zero [Fintype α]
    (p q : PMF α) (h : overlap p q ≠ 1) (x : α) :
    leftResidualPMF p q h x * rightResidualPMF p q h x = 0 := by
  rw [leftResidualPMF_apply, rightResidualPMF_apply]
  calc
    leftResidual p q x * (1 - overlap p q)⁻¹ *
        (rightResidual p q x * (1 - overlap p q)⁻¹) =
      (leftResidual p q x * rightResidual p q x) *
        ((1 - overlap p q)⁻¹ * (1 - overlap p q)⁻¹) := by ac_rfl
    _ = 0 := by rw [residual_mul_self_eq_zero, zero_mul]

theorem totalVariation_le_one [Fintype α] (p q : PMF α) :
    totalVariation p q ≤ 1 := by
  exact tsub_le_self

/-- Total variation dominates the absolute discrepancy of every individual
atom, stated in ordinary real coordinates. -/
theorem abs_toReal_sub_toReal_le_totalVariation_toReal
    [Fintype α] (p q : PMF α) (x : α) :
    |(p x).toReal - (q x).toReal| ≤ (totalVariation p q).toReal := by
  classical
  have htvTop : totalVariation p q ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (totalVariation_le_one p q)
  rcases le_total (p x) (q x) with hpq | hqp
  · rw [abs_of_nonpos (sub_nonpos.mpr (ENNReal.toReal_mono (q.apply_ne_top x) hpq))]
    rw [neg_sub]
    rw [← ENNReal.toReal_sub_of_le hpq (q.apply_ne_top x)]
    apply ENNReal.toReal_mono htvTop
    rw [totalVariation, ← sum_rightResidual]
    have hsingle := Finset.single_le_sum
      (fun _ _ => bot_le) (Finset.mem_univ x)
      (f := fun y => rightResidual p q y)
    simpa [rightResidual, min_eq_left hpq] using hsingle
  · rw [abs_of_nonneg (sub_nonneg.mpr (ENNReal.toReal_mono (p.apply_ne_top x) hqp))]
    rw [← ENNReal.toReal_sub_of_le hqp (p.apply_ne_top x)]
    apply ENNReal.toReal_mono htvTop
    rw [totalVariation, ← sum_leftResidual]
    have hsingle := Finset.single_le_sum
      (fun _ _ => bot_le) (Finset.mem_univ x)
      (f := fun y => leftResidual p q y)
    simpa [leftResidual, min_eq_right hqp] using hsingle

@[simp]
theorem totalVariation_self [Fintype α] (p : PMF α) :
    totalVariation p p = 0 := by
  rw [totalVariation, overlap_self, tsub_self]

/-- The diagonal coupling, used when both categorical marginals coincide. -/
noncomputable def diagonalCoupling (p : PMF α) : PMF (α × α) :=
  p.map fun x => (x, x)

/-- The diagonal construction has `p` on both marginals. -/
theorem diagonalCoupling_isCoupling (p : PMF α) :
    IsPMFCoupling (diagonalCoupling p) p p := by
  constructor
  · rw [diagonalCoupling, PMF.map_comp]
    change p.map id = p
    exact PMF.map_id p
  · rw [diagonalCoupling, PMF.map_comp]
    change p.map id = p
    exact PMF.map_id p

/-- The independent product of two PMFs. -/
noncomputable def independentCoupling (p : PMF α) (q : PMF β) : PMF (α × β) :=
  p.bind fun x => q.map fun y => (x, y)

/-- The independent product has the requested marginals. -/
theorem independentCoupling_isCoupling (p : PMF α) (q : PMF β) :
    IsPMFCoupling (independentCoupling p q) p q := by
  constructor
  · rw [independentCoupling, PMF.map_bind]
    calc
      (p.bind fun a => (q.map fun y => (a, y)).map Prod.fst) =
          p.bind PMF.pure := by
            congr 1
            funext a
            rw [PMF.map_comp]
            change q.map (Function.const β a) = PMF.pure a
            exact PMF.map_const q a
      _ = p := PMF.bind_pure p
  · rw [independentCoupling, PMF.map_bind]
    calc
      (p.bind fun a => (q.map fun y => (a, y)).map Prod.snd) =
          p.bind (fun _ => q) := by
            congr 1
            funext a
            rw [PMF.map_comp]
            change q.map id = q
            exact PMF.map_id q
      _ = q := PMF.bind_const p q

@[simp]
theorem independentCoupling_apply [Fintype α] [Fintype β]
    (p : PMF α) (q : PMF β) (x : α) (y : β) :
    independentCoupling p q (x, y) = p x * q y := by
  classical
  have hmap (a : α) : (q.map fun b => (a, b)) (x, y) =
      if x = a then q y else 0 := by
    rw [PMF.map_apply, tsum_fintype]
    by_cases h : x = a
    · subst a
      simp
    · simp [h]
  rw [independentCoupling, PMF.bind_apply, tsum_fintype]
  simp_rw [hmap]
  simp

/-- The normalized residuals cannot meet under their independent coupling. -/
theorem residualIndependentCoupling_diagonal_eq_zero [Fintype α]
    (p q : PMF α) (h : overlap p q ≠ 1) :
    ∑ x, independentCoupling (leftResidualPMF p q h)
      (rightResidualPMF p q h) (x, x) = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  rw [independentCoupling_apply]
  exact residualPMF_mul_self_eq_zero p q h x

/-- A convex mixture of finite PMFs, with weight `c` on the first component. -/
noncomputable def pmfMixture [Fintype α] (c : ENNReal) (hc : c ≤ 1)
    (p q : PMF α) : PMF α :=
  PMF.ofFintype (fun x => c * p x + (1 - c) * q x) (by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hp : ∑ x, p x = 1 := by
      calc
        ∑ x, p x = ∑' x, p x := by rw [tsum_fintype]
        _ = 1 := p.tsum_coe
    have hq : ∑ x, q x = 1 := by
      calc
        ∑ x, q x = ∑' x, q x := by rw [tsum_fintype]
        _ = 1 := q.tsum_coe
    rw [hp, hq, mul_one, mul_one]
    simpa [add_comm] using tsub_add_cancel_of_le hc)

@[simp]
theorem pmfMixture_apply [Fintype α] (c : ENNReal) (hc : c ≤ 1)
    (p q : PMF α) (x : α) :
    pmfMixture c hc p q x = c * p x + (1 - c) * q x :=
  rfl

/-- Mapping a finite PMF commutes with convex mixture. -/
theorem map_pmfMixture [Fintype α] [Fintype β] (c : ENNReal) (hc : c ≤ 1)
    (p q : PMF α) (f : α → β) :
    (pmfMixture c hc p q).map f =
      pmfMixture c hc (p.map f) (q.map f) := by
  classical
  ext y
  simp only [PMF.map_apply, tsum_fintype, pmfMixture_apply]
  calc
    (∑ a, if y = f a then c * p a + (1 - c) * q a else 0) =
        ∑ a, ((if y = f a then c * p a else 0) +
          (if y = f a then (1 - c) * q a else 0)) := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : y = f a <;> simp [h]
    _ = c * ∑ a, (if y = f a then p a else 0) +
        (1 - c) * ∑ a, (if y = f a then q a else 0) := by
      rw [Finset.sum_add_distrib]
      congr 1
      · calc
          (∑ a, if y = f a then c * p a else 0) =
              ∑ a, c * (if y = f a then p a else 0) := by
            apply Finset.sum_congr rfl
            intro a _
            by_cases h : y = f a <;> simp [h]
          _ = c * ∑ a, (if y = f a then p a else 0) :=
            by rw [Finset.mul_sum]
      · calc
          (∑ a, if y = f a then (1 - c) * q a else 0) =
              ∑ a, (1 - c) * (if y = f a then q a else 0) := by
            apply Finset.sum_congr rfl
            intro a _
            by_cases h : y = f a <;> simp [h]
          _ = (1 - c) * ∑ a, (if y = f a then q a else 0) :=
            by rw [Finset.mul_sum]

@[simp]
theorem pmfMixture_self [Fintype α] (c : ENNReal) (hc : c ≤ 1)
    (p : PMF α) : pmfMixture c hc p p = p := by
  ext x
  rw [pmfMixture_apply]
  calc
    c * p x + (1 - c) * p x = (c + (1 - c)) * p x := by
      rw [add_mul]
    _ = p x := by
      rw [show c + (1 - c) = 1 by
        simpa [add_comm] using tsub_add_cancel_of_le hc, one_mul]

/-- A common convex mixture of two couplings couples the corresponding
mixtures of their marginals. -/
theorem pmfMixture_isCoupling [Fintype α] [Fintype β]
    (c : ENNReal) (hc : c ≤ 1)
    {j₁ j₂ : PMF (α × β)} {p₁ p₂ : PMF α} {q₁ q₂ : PMF β}
    (h₁ : IsPMFCoupling j₁ p₁ q₁) (h₂ : IsPMFCoupling j₂ p₂ q₂) :
    IsPMFCoupling (pmfMixture c hc j₁ j₂)
      (pmfMixture c hc p₁ p₂) (pmfMixture c hc q₁ q₂) := by
  constructor
  · rw [map_pmfMixture, h₁.fst, h₂.fst]
  · rw [map_pmfMixture, h₁.snd, h₂.snd]

/-- The normalized common part of two non-disjoint finite PMFs. -/
noncomputable def commonPMF [Fintype α] (p q : PMF α)
    (h : overlap p q ≠ 0) : PMF α :=
  PMF.normalize (fun x => min (p x) (q x))
    (by rwa [tsum_fintype])
    (by
      rw [tsum_fintype]
      exact ne_top_of_le_ne_top ENNReal.one_ne_top (overlap_le_one p q))

@[simp]
theorem commonPMF_apply [Fintype α] (p q : PMF α)
    (h : overlap p q ≠ 0) (x : α) :
    commonPMF p q h x = min (p x) (q x) * (overlap p q)⁻¹ := by
  rw [commonPMF, PMF.normalize_apply, tsum_fintype, overlap]

theorem overlap_mul_commonPMF_apply [Fintype α] (p q : PMF α)
    (h : overlap p q ≠ 0) (x : α) :
    overlap p q * commonPMF p q h x = min (p x) (q x) := by
  rw [commonPMF_apply]
  calc
    overlap p q * (min (p x) (q x) * (overlap p q)⁻¹) =
        min (p x) (q x) * (overlap p q * (overlap p q)⁻¹) := by ac_rfl
    _ = min (p x) (q x) := by
      rw [ENNReal.mul_inv_cancel h
        (ne_top_of_le_ne_top ENNReal.one_ne_top (overlap_le_one p q)), mul_one]

theorem one_sub_overlap_mul_leftResidualPMF_apply [Fintype α]
    (p q : PMF α) (h : overlap p q ≠ 1) (x : α) :
    (1 - overlap p q) * leftResidualPMF p q h x = leftResidual p q x := by
  rw [leftResidualPMF_apply]
  calc
    (1 - overlap p q) * (leftResidual p q x * (1 - overlap p q)⁻¹) =
        leftResidual p q x * ((1 - overlap p q) * (1 - overlap p q)⁻¹) := by ac_rfl
    _ = leftResidual p q x := by
      rw [ENNReal.mul_inv_cancel (one_sub_overlap_ne_zero p q h)
        (ENNReal.sub_ne_top ENNReal.one_ne_top), mul_one]

theorem one_sub_overlap_mul_rightResidualPMF_apply [Fintype α]
    (p q : PMF α) (h : overlap p q ≠ 1) (x : α) :
    (1 - overlap p q) * rightResidualPMF p q h x = rightResidual p q x := by
  rw [rightResidualPMF_apply]
  calc
    (1 - overlap p q) * (rightResidual p q x * (1 - overlap p q)⁻¹) =
        rightResidual p q x * ((1 - overlap p q) * (1 - overlap p q)⁻¹) := by ac_rfl
    _ = rightResidual p q x := by
      rw [ENNReal.mul_inv_cancel (one_sub_overlap_ne_zero p q h)
        (ENNReal.sub_ne_top ENNReal.one_ne_top), mul_one]

/-- Splitting off and normalizing the common mass reconstructs the left
marginal. -/
theorem pmfMixture_common_left_eq [Fintype α] (p q : PMF α)
    (hzero : overlap p q ≠ 0) (hfull : overlap p q ≠ 1) :
    pmfMixture (overlap p q) (overlap_le_one p q)
      (commonPMF p q hzero) (leftResidualPMF p q hfull) = p := by
  ext x
  rw [pmfMixture_apply, overlap_mul_commonPMF_apply,
    one_sub_overlap_mul_leftResidualPMF_apply]
  simp only [leftResidual]
  rw [add_comm, tsub_add_cancel_of_le (min_le_left (p x) (q x))]

/-- Splitting off and normalizing the common mass reconstructs the right
marginal. -/
theorem pmfMixture_common_right_eq [Fintype α] (p q : PMF α)
    (hzero : overlap p q ≠ 0) (hfull : overlap p q ≠ 1) :
    pmfMixture (overlap p q) (overlap_le_one p q)
      (commonPMF p q hzero) (rightResidualPMF p q hfull) = q := by
  ext x
  rw [pmfMixture_apply, overlap_mul_commonPMF_apply,
    one_sub_overlap_mul_rightResidualPMF_apply]
  simp only [rightResidual]
  rw [add_comm, tsub_add_cancel_of_le (min_le_right (p x) (q x))]

theorem eq_of_overlap_eq_one [Fintype α] (p q : PMF α)
    (h : overlap p q = 1) : p = q := by
  have hleftSum : ∑ x, leftResidual p q x = 0 := by
    rw [sum_leftResidual, h, tsub_self]
  have hrightSum : ∑ x, rightResidual p q x = 0 := by
    rw [sum_rightResidual, h, tsub_self]
  ext x
  have hleft : leftResidual p q x = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => bot_le)).mp hleftSum x
      (Finset.mem_univ x)
  have hright : rightResidual p q x = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => bot_le)).mp hrightSum x
      (Finset.mem_univ x)
  have hpq : p x ≤ q x := by
    exact (tsub_eq_zero_iff_le.mp hleft).trans (min_le_right _ _)
  have hqp : q x ≤ p x := by
    exact (tsub_eq_zero_iff_le.mp hright).trans (min_le_left _ _)
  exact le_antisymm hpq hqp

theorem min_apply_eq_zero_of_overlap_eq_zero [Fintype α] (p q : PMF α)
    (h : overlap p q = 0) (x : α) : min (p x) (q x) = 0 := by
  have hsum : ∑ x, min (p x) (q x) = 0 := by simpa [overlap] using h
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => bot_le)).mp hsum x
    (Finset.mem_univ x)

@[simp]
theorem diagonalCoupling_apply (p : PMF α) (x : α) :
    diagonalCoupling p (x, x) = p x := by
  classical
  simp [diagonalCoupling, PMF.map_apply]

theorem diagonalCoupling_apply_pair [Fintype α] [DecidableEq α]
    (p : PMF α) (x y : α) :
    diagonalCoupling p (x, y) = if x = y then p x else 0 := by
  classical
  rw [diagonalCoupling, PMF.map_apply, tsum_fintype]
  by_cases hxy : x = y
  · subst y
    simp
  · simp [hxy, Ne.symm hxy]

/-- A categorical coupling is maximal when its diagonal mass is the common
mass of its marginals. -/
def IsMaximalCoupling [Fintype α] (joint : PMF (α × α)) (p q : PMF α) : Prop :=
  IsPMFCoupling joint p q ∧ ∑ x, joint (x, x) = overlap p q

/-- Probability mass assigned to unequal pairs by a finite joint PMF. -/
noncomputable def mismatchMass [Fintype α] [DecidableEq α]
    (joint : PMF (α × α)) : ENNReal :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, joint (i, j)

/-- Mismatch probability after first sampling a finite latent variable and
then sampling a conditional joint law.  This is the finite law-of-total-
probability identity for the event that the two coordinates differ. -/
theorem mismatchMass_bind [Fintype α] [DecidableEq α]
    {κ : Type*} [Fintype κ] (p : PMF κ) (joint : κ → PMF (α × α)) :
    mismatchMass (p.bind joint) =
      ∑ k, p k * mismatchMass (joint k) := by
  unfold mismatchMass
  simp_rw [PMF.bind_apply, tsum_fintype]
  calc
    (∑ i, ∑ j ∈ Finset.univ.erase i,
        ∑ k, p k * joint k (i, j)) =
        ∑ i, ∑ k, ∑ j ∈ Finset.univ.erase i,
          p k * joint k (i, j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j ∈ Finset.univ.erase i,
          p k * joint k (i, j) := by
      rw [Finset.sum_comm]
    _ = ∑ k, p k * ∑ i, ∑ j ∈ Finset.univ.erase i,
          joint k (i, j) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
      apply congrArg
      funext i
      rw [Finset.mul_sum]

/-- Diagonal and mismatch masses partition the total mass of a finite joint
PMF. -/
theorem diagonalMass_add_mismatchMass [Fintype α] [DecidableEq α]
    (joint : PMF (α × α)) :
    (∑ i, joint (i, i)) + mismatchMass joint = 1 := by
  have hrow : ∀ i : α,
      joint (i, i) + ∑ j ∈ Finset.univ.erase i, joint (i, j) =
        ∑ j, joint (i, j) := by
    intro i
    rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  calc
    (∑ i, joint (i, i)) + mismatchMass joint =
        ∑ i, (joint (i, i) +
          ∑ j ∈ Finset.univ.erase i, joint (i, j)) := by
      rw [mismatchMass, Finset.sum_add_distrib]
    _ = ∑ i, ∑ j, joint (i, j) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hrow i
    _ = ∑ ij : α × α, joint ij := by
      rw [← Finset.sum_product]
      simp
    _ = ∑' ij : α × α, joint ij := by rw [tsum_fintype]
    _ = 1 := joint.tsum_coe

/-- Every coupling's unequal-pair probability is at least the total variation
distance of its marginals. Maximal couplings are exactly the equality case. -/
theorem IsPMFCoupling.totalVariation_le_mismatchMass
    [Fintype α] [DecidableEq α]
    {joint : PMF (α × α)} {p q : PMF α}
    (h : IsPMFCoupling joint p q) :
    totalVariation p q ≤ mismatchMass joint := by
  have hdiag : (∑ i, joint (i, i)) ≤ overlap p q := by
    unfold overlap
    apply Finset.sum_le_sum
    intro i _
    apply le_min
    · exact (Finset.single_le_sum (fun _ _ => bot_le)
        (Finset.mem_univ i)).trans_eq (h.sum_right i)
    · exact (Finset.single_le_sum (fun _ _ => bot_le)
        (Finset.mem_univ i)).trans_eq (h.sum_left i)
  rw [totalVariation]
  rw [tsub_le_iff_right]
  calc
    1 = (∑ i, joint (i, i)) + mismatchMass joint :=
      (diagonalMass_add_mismatchMass joint).symm
    _ ≤ overlap p q + mismatchMass joint := add_le_add_left hdiag _
    _ = mismatchMass joint + overlap p q := add_comm _ _

/-- For a maximal coupling, mismatch probability is exactly total variation. -/
theorem IsMaximalCoupling.mismatchMass_eq_totalVariation
    [Fintype α] [DecidableEq α]
    {joint : PMF (α × α)} {p q : PMF α}
    (h : IsMaximalCoupling joint p q) :
    mismatchMass joint = totalVariation p q := by
  rw [totalVariation, ← h.2]
  apply ENNReal.eq_sub_of_add_eq
    (ENNReal.sum_ne_top.mpr fun i hi => joint.apply_ne_top (i, i))
  rw [add_comm]
  exact diagonalMass_add_mismatchMass joint

/-- Maximality in overlap form is the usual statement that the meeting
probability is `1 - dTV(p,q)`. -/
theorem IsMaximalCoupling.diagonal_eq_one_sub_totalVariation
    [Fintype α] {joint : PMF (α × α)} {p q : PMF α}
    (h : IsMaximalCoupling joint p q) :
    ∑ x, joint (x, x) = 1 - totalVariation p q := by
  rw [h.2, totalVariation,
    ENNReal.sub_sub_cancel ENNReal.one_ne_top (overlap_le_one p q)]

/-- When the marginals coincide, the diagonal coupling is maximal. -/
theorem diagonalCoupling_isMaximal [Fintype α] (p : PMF α) :
    IsMaximalCoupling (diagonalCoupling p) p p := by
  constructor
  · exact diagonalCoupling_isCoupling p
  · simp [overlap]

/-- The standard maximal coupling: use the common mass on the diagonal and,
conditional on not using it, draw independently from the disjoint residuals. -/
noncomputable def maximalCoupling [Fintype α] (p q : PMF α) : PMF (α × α) := by
  classical
  by_cases hfull : overlap p q = 1
  · exact diagonalCoupling p
  by_cases hzero : overlap p q = 0
  · exact independentCoupling p q
  exact pmfMixture (overlap p q) (overlap_le_one p q)
    (diagonalCoupling (commonPMF p q hzero))
    (independentCoupling (leftResidualPMF p q hfull)
      (rightResidualPMF p q hfull))

@[simp]
theorem maximalCoupling_self [Fintype α] (p : PMF α) :
    maximalCoupling p p = diagonalCoupling p := by
  unfold maximalCoupling
  simp only [overlap_self, ↓reduceDIte]

/-- Every pair of finite categorical distributions admits a maximal coupling. -/
theorem maximalCoupling_isMaximal [Fintype α] (p q : PMF α) :
    IsMaximalCoupling (maximalCoupling p q) p q := by
  classical
  unfold maximalCoupling
  split_ifs with hfull hzero
  · have hpq : p = q := eq_of_overlap_eq_one p q hfull
    subst q
    exact diagonalCoupling_isMaximal p
  · constructor
    · exact independentCoupling_isCoupling p q
    · rw [hzero]
      apply Finset.sum_eq_zero
      intro x _
      rw [independentCoupling_apply]
      have hmin := min_apply_eq_zero_of_overlap_eq_zero p q hzero x
      rcases min_eq_zero.mp hmin with hp | hq
      · simp [hp]
      · simp [hq]
  · constructor
    · have hcoupling := pmfMixture_isCoupling (overlap p q) (overlap_le_one p q)
          (diagonalCoupling_isCoupling (commonPMF p q hzero))
          (independentCoupling_isCoupling
            (leftResidualPMF p q hfull) (rightResidualPMF p q hfull))
      rw [pmfMixture_common_left_eq p q hzero hfull,
        pmfMixture_common_right_eq p q hzero hfull] at hcoupling
      exact hcoupling
    · simp only [pmfMixture_apply]
      calc
        (∑ x, (overlap p q * diagonalCoupling (commonPMF p q hzero) (x, x) +
            (1 - overlap p q) *
              independentCoupling (leftResidualPMF p q hfull)
                (rightResidualPMF p q hfull) (x, x))) =
            overlap p q * ∑ x, diagonalCoupling (commonPMF p q hzero) (x, x) +
              (1 - overlap p q) * ∑ x,
                independentCoupling (leftResidualPMF p q hfull)
                  (rightResidualPMF p q hfull) (x, x) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        _ = overlap p q * 1 + (1 - overlap p q) * 0 := by
          rw [residualIndependentCoupling_diagonal_eq_zero]
          simp only [diagonalCoupling_apply]
          have hcommon : ∑ x, commonPMF p q hzero x = 1 := by
            calc
              ∑ x, commonPMF p q hzero x = ∑' x, commonPMF p q hzero x := by
                rw [tsum_fintype]
              _ = 1 := (commonPMF p q hzero).tsum_coe
          rw [hcommon]
        _ = overlap p q := by simp

/-- A branch-free pointwise formula for the standard maximal coupling.  It is
particularly useful for proving measurability of parameterized maximal
categorical laws. -/
theorem maximalCoupling_apply_formula [Fintype α] [DecidableEq α]
    (p q : PMF α) (x y : α) :
    maximalCoupling p q (x, y) =
      (if x = y then min (p x) (q x) else 0) +
        leftResidual p q x * rightResidual p q y *
          (1 - overlap p q)⁻¹ := by
  classical
  by_cases hxy : x = y
  · subst y
    rw [if_pos rfl]
    by_cases hfull : overlap p q = 1
    · have hpq : p = q := eq_of_overlap_eq_one p q hfull
      subst q
      simp [maximalCoupling, leftResidual, rightResidual]
    · by_cases hzero : overlap p q = 0
      · have hmin := min_apply_eq_zero_of_overlap_eq_zero p q hzero x
        simp [maximalCoupling, hzero, independentCoupling_apply,
          leftResidual, rightResidual, hmin]
      · rw [maximalCoupling]
        simp only [dif_neg hfull, dif_neg hzero]
        rw [pmfMixture_apply, diagonalCoupling_apply,
          independentCoupling_apply]
        rw [overlap_mul_commonPMF_apply]
        rw [residualPMF_mul_self_eq_zero]
        simp [residual_mul_self_eq_zero]
  · rw [if_neg hxy]
    by_cases hfull : overlap p q = 1
    · have hpq : p = q := eq_of_overlap_eq_one p q hfull
      subst q
      simp [maximalCoupling, diagonalCoupling_apply_pair, hxy,
        leftResidual, rightResidual]
    · by_cases hzero : overlap p q = 0
      · have hminx := min_apply_eq_zero_of_overlap_eq_zero p q hzero x
        have hminy := min_apply_eq_zero_of_overlap_eq_zero p q hzero y
        simp [maximalCoupling, hzero, independentCoupling_apply,
          leftResidual, rightResidual, hminx, hminy]
      · rw [maximalCoupling]
        simp only [dif_neg hfull, dif_neg hzero]
        rw [pmfMixture_apply, diagonalCoupling_apply_pair,
          if_neg hxy, mul_zero, independentCoupling_apply, zero_add]
        simp only [zero_add]
        calc
          (1 - overlap p q) *
              (leftResidualPMF p q hfull x * rightResidualPMF p q hfull y) =
              leftResidual p q x * rightResidualPMF p q hfull y := by
            rw [← mul_assoc, one_sub_overlap_mul_leftResidualPMF_apply]
          _ = leftResidual p q x * rightResidual p q y *
              (1 - overlap p q)⁻¹ := by
            rw [rightResidualPMF_apply]
            ac_rfl

/-- The diagonal atoms of the canonical maximal coupling are exactly the
pointwise overlaps of its marginals. -/
theorem maximalCoupling_apply_diagonal [Fintype α] [DecidableEq α]
    (p q : PMF α) (x : α) :
    maximalCoupling p q (x, x) = min (p x) (q x) := by
  rw [maximalCoupling_apply_formula, if_pos rfl,
    residual_mul_self_eq_zero, zero_mul, add_zero]

/-- The overlap of two measurably parameterized finite PMFs is measurable. -/
theorem measurable_overlap {Ω : Type*} [MeasurableSpace Ω]
    [Fintype α] (p q : Ω → PMF α)
    (hp : ∀ x, Measurable fun ω => p ω x)
    (hq : ∀ x, Measurable fun ω => q ω x) :
    Measurable fun ω => overlap (p ω) (q ω) := by
  unfold overlap
  apply Finset.measurable_sum
  intro x hx
  exact (hp x).min (hq x)

/-- Every atom of the standard maximal coupling is measurable when the atoms
of both marginal PMFs are measurable. -/
theorem measurable_maximalCoupling_apply
    {Ω : Type*} [MeasurableSpace Ω] [Fintype α] [DecidableEq α]
    (p q : Ω → PMF α)
    (hp : ∀ x, Measurable fun ω => p ω x)
    (hq : ∀ x, Measurable fun ω => q ω x)
    (x y : α) :
    Measurable fun ω => maximalCoupling (p ω) (q ω) (x, y) := by
  simp_rw [maximalCoupling_apply_formula]
  apply Measurable.add
  · by_cases hxy : x = y
    · subst y
      simpa using (hp x).min (hq x)
    · simp only [hxy, if_false]
      exact measurable_const
  · apply Measurable.mul
    · apply Measurable.mul
      · unfold leftResidual
        exact (hp x).sub ((hp x).min (hq x))
      · unfold rightResidual
        exact (hq y).sub ((hp y).min (hq y))
    · apply Measurable.inv
      exact measurable_const.sub (measurable_overlap p q hp hq)

end Finite
end Mcmc
