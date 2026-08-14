import Mcmc.Finite.Coupling
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Order.Lattice

/-!
# Marginal repair for approximate finite couplings

This module formalizes Algorithm 5 of Xu, Fjelde, Sutton, and Ge (2021).
An arbitrary joint PMF is mixed with an independent coupling of residual
marginals.  Whenever the mixing coefficient is pointwise admissible, the
result has exactly the requested marginals.
-/

open scoped BigOperators ENNReal

namespace Mcmc.Finite

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Pointwise admissibility of a coefficient placed on an approximate joint
law with respect to the desired marginals. -/
def IsMarginalRepairWeight (weight : ENNReal) (joint : PMF (α × β))
    (left : PMF α) (right : PMF β) : Prop :=
  weight ≤ 1 ∧
    (∀ x, weight * (joint.map Prod.fst) x ≤ left x) ∧
    ∀ y, weight * (joint.map Prod.snd) y ≤ right y

/-- Unnormalized residual marginal after retaining `weight` of an
approximate marginal. -/
noncomputable def marginalRepairResidualMass (weight : ENNReal)
    (target candidate : PMF α) (x : α) : ENNReal :=
  target x - weight * candidate x

theorem sum_marginalRepairResidualMass
    {weight : ENNReal} (_hweight : weight ≤ 1)
    (target candidate : PMF α)
    (hadmissible : ∀ x, weight * candidate x ≤ target x) :
    ∑ x, marginalRepairResidualMass weight target candidate x = 1 - weight := by
  unfold marginalRepairResidualMass
  rw [sum_tsub_eq_tsub_sum]
  · rw [← Finset.mul_sum]
    have htarget : ∑ x, target x = 1 := by
      calc
        ∑ x, target x = ∑' x, target x := by rw [tsum_fintype]
        _ = 1 := target.tsum_coe
    have hcandidate : ∑ x, candidate x = 1 := by
      calc
        ∑ x, candidate x = ∑' x, candidate x := by rw [tsum_fintype]
        _ = 1 := candidate.tsum_coe
    rw [htarget, hcandidate, mul_one]
  · exact target.apply_ne_top
  · exact hadmissible

/-- The normalized residual marginal used by Algorithm 5 when the retained
coefficient is strictly below one. -/
noncomputable def marginalRepairResidualPMF
    (weight : ENNReal) (hweight : weight < 1)
    (target candidate : PMF α)
    (hadmissible : ∀ x, weight * candidate x ≤ target x) : PMF α :=
  PMF.normalize (marginalRepairResidualMass weight target candidate)
    (by
      rw [tsum_fintype,
        sum_marginalRepairResidualMass hweight.le target candidate hadmissible]
      exact ne_of_gt (tsub_pos_iff_lt.mpr hweight))
    (by
      rw [tsum_fintype,
        sum_marginalRepairResidualMass hweight.le target candidate hadmissible]
      exact ENNReal.sub_ne_top ENNReal.one_ne_top)

@[simp]
theorem marginalRepairResidualPMF_apply
    (weight : ENNReal) (hweight : weight < 1)
    (target candidate : PMF α)
    (hadmissible : ∀ x, weight * candidate x ≤ target x) (x : α) :
    marginalRepairResidualPMF weight hweight target candidate hadmissible x =
      (target x - weight * candidate x) * (1 - weight)⁻¹ := by
  rw [marginalRepairResidualPMF, PMF.normalize_apply, tsum_fintype,
    sum_marginalRepairResidualMass hweight.le target candidate hadmissible]
  rfl

/-- Mixing an admissible approximate marginal with its normalized residual
recovers the desired marginal exactly. -/
theorem pmfMixture_marginalRepairResidualPMF
    (weight : ENNReal) (hweight : weight < 1)
    (target candidate : PMF α)
    (hadmissible : ∀ x, weight * candidate x ≤ target x) :
    pmfMixture weight hweight.le candidate
      (marginalRepairResidualPMF weight hweight target candidate hadmissible) =
        target := by
  ext x
  rw [pmfMixture_apply, marginalRepairResidualPMF_apply]
  have hdiff0 : 1 - weight ≠ 0 := ne_of_gt (tsub_pos_iff_lt.mpr hweight)
  have hdiffTop : 1 - weight ≠ ∞ := ENNReal.sub_ne_top ENNReal.one_ne_top
  calc
    weight * candidate x +
        (1 - weight) * ((target x - weight * candidate x) * (1 - weight)⁻¹) =
      weight * candidate x +
        ((1 - weight) * (1 - weight)⁻¹) *
          (target x - weight * candidate x) := by ac_rfl
    _ = weight * candidate x +
        (target x - weight * candidate x) := by
      rw [ENNReal.mul_inv_cancel hdiff0 hdiffTop, one_mul]
    _ = target x := by
      rw [add_comm]
      exact tsub_add_cancel_of_le (hadmissible x)

/-- Algorithm 5 at any strict admissible coefficient: retain the approximate
joint with that probability and otherwise sample independently from the two
normalized residual marginals. -/
noncomputable def marginalRepairedCoupling
    (weight : ENNReal) (hweight : weight < 1)
    (joint : PMF (α × β)) (left : PMF α) (right : PMF β)
    (hadmissible : IsMarginalRepairWeight weight joint left right) :
    PMF (α × β) :=
  pmfMixture weight hweight.le joint
    (independentCoupling
      (marginalRepairResidualPMF weight hweight left (joint.map Prod.fst)
        hadmissible.2.1)
      (marginalRepairResidualPMF weight hweight right (joint.map Prod.snd)
        hadmissible.2.2))

/-- The marginal-repaired joint has exactly the requested marginals. -/
theorem marginalRepairedCoupling_isCoupling
    (weight : ENNReal) (hweight : weight < 1)
    (joint : PMF (α × β)) (left : PMF α) (right : PMF β)
    (hadmissible : IsMarginalRepairWeight weight joint left right) :
    IsPMFCoupling
      (marginalRepairedCoupling weight hweight joint left right hadmissible)
      left right := by
  unfold marginalRepairedCoupling
  have hindependent := independentCoupling_isCoupling
    (marginalRepairResidualPMF weight hweight left (joint.map Prod.fst)
      hadmissible.2.1)
    (marginalRepairResidualPMF weight hweight right (joint.map Prod.snd)
      hadmissible.2.2)
  have hjoint : IsPMFCoupling joint (joint.map Prod.fst) (joint.map Prod.snd) :=
    ⟨rfl, rfl⟩
  have hmix := pmfMixture_isCoupling weight hweight.le hjoint hindependent
  rw [pmfMixture_marginalRepairResidualPMF weight hweight left
      (joint.map Prod.fst) hadmissible.2.1,
    pmfMixture_marginalRepairResidualPMF weight hweight right
      (joint.map Prod.snd) hadmissible.2.2] at hmix
  exact hmix

@[simp]
theorem marginalRepairedCoupling_apply
    (weight : ENNReal) (hweight : weight < 1)
    (joint : PMF (α × β)) (left : PMF α) (right : PMF β)
    (hadmissible : IsMarginalRepairWeight weight joint left right)
    (edge : α × β) :
    marginalRepairedCoupling weight hweight joint left right hadmissible edge =
      weight * joint edge + (1 - weight) *
        (((left edge.1 - weight * (joint.map Prod.fst) edge.1) *
          (1 - weight)⁻¹) *
        ((right edge.2 - weight * (joint.map Prod.snd) edge.2) *
          (1 - weight)⁻¹)) := by
  rw [marginalRepairedCoupling, pmfMixture_apply,
    independentCoupling_apply, marginalRepairResidualPMF_apply,
    marginalRepairResidualPMF_apply]

/-- The ratios appearing in equation (20), with an extra `none` entry for the
upper bound one. -/
noncomputable def marginalRepairRatio
    (joint : PMF (α × β)) (left : PMF α) (right : PMF β) :
    Option (α ⊕ β) → ENNReal
  | none => 1
  | some (.inl x) =>
      if (joint.map Prod.fst) x = 0 then 1
      else left x / (joint.map Prod.fst) x
  | some (.inr y) =>
      if (joint.map Prod.snd) y = 0 then 1
      else right y / (joint.map Prod.snd) y

/-- Equation (20): the largest coefficient that can be retained without
overshooting either desired marginal. -/
noncomputable def maximalMarginalRepairWeight
    (joint : PMF (α × β)) (left : PMF α) (right : PMF β) : ENNReal := by
  classical
  exact (Finset.univ : Finset (Option (α ⊕ β))).inf'
    (Finset.univ_nonempty) (marginalRepairRatio joint left right)

theorem maximalMarginalRepairWeight_le_ratio
    (joint : PMF (α × β)) (left : PMF α) (right : PMF β)
    (i : Option (α ⊕ β)) :
    maximalMarginalRepairWeight joint left right ≤
      marginalRepairRatio joint left right i := by
  classical
  exact Finset.inf'_le _ (Finset.mem_univ i)

/-- The coefficient from equation (20) is admissible. -/
theorem maximalMarginalRepairWeight_isMarginalRepairWeight
    (joint : PMF (α × β)) (left : PMF α) (right : PMF β) :
    IsMarginalRepairWeight
      (maximalMarginalRepairWeight joint left right) joint left right := by
  let weight := maximalMarginalRepairWeight joint left right
  refine ⟨?_, ?_, ?_⟩
  · simpa [marginalRepairRatio] using
      (maximalMarginalRepairWeight_le_ratio joint left right none)
  · intro x
    have hratio := maximalMarginalRepairWeight_le_ratio joint left right
      (some (.inl x))
    by_cases hx : (joint.map Prod.fst) x = 0
    · simp [hx]
    · simp only [marginalRepairRatio, hx, if_false] at hratio
      exact (ENNReal.le_div_iff_mul_le (Or.inl hx)
        (Or.inl ((joint.map Prod.fst).apply_ne_top x))).mp hratio
  · intro y
    have hratio := maximalMarginalRepairWeight_le_ratio joint left right
      (some (.inr y))
    by_cases hy : (joint.map Prod.snd) y = 0
    · simp [hy]
    · simp only [marginalRepairRatio, hy, if_false] at hratio
      exact (ENNReal.le_div_iff_mul_le (Or.inl hy)
        (Or.inl ((joint.map Prod.snd).apply_ne_top y))).mp hratio

/-- Maximality of equation (20): every admissible retained coefficient is at
most the finite minimum of the marginal ratios. -/
theorem le_maximalMarginalRepairWeight
    {weight : ENNReal} {joint : PMF (α × β)} {left : PMF α} {right : PMF β}
    (h : IsMarginalRepairWeight weight joint left right) :
    weight ≤ maximalMarginalRepairWeight joint left right := by
  classical
  unfold maximalMarginalRepairWeight
  apply Finset.le_inf'
  intro i hi
  cases i with
  | none => simpa [marginalRepairRatio] using h.1
  | some i =>
      cases i with
      | inl x =>
          by_cases hx : (joint.map Prod.fst) x = 0
          · simpa [marginalRepairRatio, hx] using h.1
          · simp only [marginalRepairRatio, hx, if_false]
            exact (ENNReal.le_div_iff_mul_le (Or.inl hx)
              (Or.inl ((joint.map Prod.fst).apply_ne_top x))).mpr (h.2.1 x)
      | inr y =>
          by_cases hy : (joint.map Prod.snd) y = 0
          · simpa [marginalRepairRatio, hy] using h.1
          · simp only [marginalRepairRatio, hy, if_false]
            exact (ENNReal.le_div_iff_mul_le (Or.inl hy)
              (Or.inl ((joint.map Prod.snd).apply_ne_top y))).mpr (h.2.2 y)

/-- Pointwise domination between finite PMFs of equal total mass is equality. -/
theorem PMF.eq_of_apply_le (p q : PMF α) (h : ∀ x, p x ≤ q x) : p = q := by
  classical
  apply PMF.ext
  intro x
  apply le_antisymm (h x)
  by_contra hnot
  have hx : p x < q x := lt_of_not_ge hnot
  have hreal : ∀ y, (p y).toReal ≤ (q y).toReal := fun y =>
    ENNReal.toReal_mono (q.apply_ne_top y) (h y)
  have hxreal : (p x).toReal < (q x).toReal :=
    ENNReal.toReal_strict_mono (q.apply_ne_top x) hx
  have hsum : (∑ y, (p y).toReal) < ∑ y, (q y).toReal :=
    Finset.sum_lt_sum (fun y hy => hreal y)
      ⟨x, Finset.mem_univ x, hxreal⟩
  have hp : ∑ y, (p y).toReal = 1 := by
    calc
      ∑ y, (p y).toReal = (∑ y, p y).toReal := by
        rw [ENNReal.toReal_sum (fun y _ => p.apply_ne_top y)]
      _ = (∑' y, p y).toReal := by rw [tsum_fintype]
      _ = 1 := by rw [p.tsum_coe, ENNReal.toReal_one]
  have hq : ∑ y, (q y).toReal = 1 := by
    calc
      ∑ y, (q y).toReal = (∑ y, q y).toReal := by
        rw [ENNReal.toReal_sum (fun y _ => q.apply_ne_top y)]
      _ = (∑' y, q y).toReal := by rw [tsum_fintype]
      _ = 1 := by rw [q.tsum_coe, ENNReal.toReal_one]
  rw [hp, hq] at hsum
  exact (lt_irrefl 1) hsum

/-- Weight one occurs exactly in the unbiased case, so Algorithm 5 reduces
to the original joint law. -/
theorem isCoupling_of_maximalMarginalRepairWeight_eq_one
    {joint : PMF (α × β)} {left : PMF α} {right : PMF β}
    (hweight : maximalMarginalRepairWeight joint left right = 1) :
    IsPMFCoupling joint left right := by
  have hadmissible :=
    maximalMarginalRepairWeight_isMarginalRepairWeight joint left right
  rw [hweight] at hadmissible
  constructor
  · apply PMF.eq_of_apply_le
    intro x
    simpa using hadmissible.2.1 x
  · apply PMF.eq_of_apply_le
    intro y
    simpa using hadmissible.2.2 y

/-- Algorithm 5 with its maximal coefficient, including the unbiased
weight-one branch. -/
noncomputable def maximallyMarginalRepairedCoupling
    (joint : PMF (α × β)) (left : PMF α) (right : PMF β) : PMF (α × β) := by
  let weight := maximalMarginalRepairWeight joint left right
  by_cases hweight : weight < 1
  · exact marginalRepairedCoupling weight hweight joint left right
      (maximalMarginalRepairWeight_isMarginalRepairWeight joint left right)
  · exact joint

/-- The complete Algorithm 5 construction has exactly the target marginals. -/
theorem maximallyMarginalRepairedCoupling_isCoupling
    (joint : PMF (α × β)) (left : PMF α) (right : PMF β) :
    IsPMFCoupling
      (maximallyMarginalRepairedCoupling joint left right) left right := by
  let weight := maximalMarginalRepairWeight joint left right
  by_cases hweight : weight < 1
  · rw [maximallyMarginalRepairedCoupling]
    rw [dif_pos hweight]
    exact marginalRepairedCoupling_isCoupling weight hweight joint left right
      (maximalMarginalRepairWeight_isMarginalRepairWeight joint left right)
  · have hle :=
      (maximalMarginalRepairWeight_isMarginalRepairWeight joint left right).1
    have hone : weight = 1 := le_antisymm hle (not_lt.mp hweight)
    rw [maximallyMarginalRepairedCoupling]
    rw [dif_neg hweight]
    exact isCoupling_of_maximalMarginalRepairWeight_eq_one hone

@[simp]
theorem maximallyMarginalRepairedCoupling_apply
    (joint : PMF (α × β)) (left : PMF α) (right : PMF β)
    (edge : α × β) :
    maximallyMarginalRepairedCoupling joint left right edge =
      if _hweight : maximalMarginalRepairWeight joint left right < 1 then
        maximalMarginalRepairWeight joint left right * joint edge +
          (1 - maximalMarginalRepairWeight joint left right) *
            (((left edge.1 - maximalMarginalRepairWeight joint left right *
                (joint.map Prod.fst) edge.1) *
              (1 - maximalMarginalRepairWeight joint left right)⁻¹) *
            ((right edge.2 - maximalMarginalRepairWeight joint left right *
                (joint.map Prod.snd) edge.2) *
              (1 - maximalMarginalRepairWeight joint left right)⁻¹))
      else joint edge := by
  rw [maximallyMarginalRepairedCoupling]
  split_ifs with h
  · exact marginalRepairedCoupling_apply _ h _ _ _ _ edge
  · rfl

/-- An already unbiased candidate admits coefficient one. -/
theorem maximalMarginalRepairWeight_eq_one_of_isCoupling
    {joint : PMF (α × β)} {left : PMF α} {right : PMF β}
    (hjoint : IsPMFCoupling joint left right) :
    maximalMarginalRepairWeight joint left right = 1 := by
  apply le_antisymm
  · exact (maximalMarginalRepairWeight_isMarginalRepairWeight
      joint left right).1
  · apply le_maximalMarginalRepairWeight
    refine ⟨le_rfl, ?_, ?_⟩
    · intro x
      rw [one_mul, hjoint.1]
    · intro y
      rw [one_mul, hjoint.2]

/-- In the unbiased case Algorithm 5 reduces to the supplied joint law. -/
theorem maximallyMarginalRepairedCoupling_eq_of_isCoupling
    {joint : PMF (α × β)} {left : PMF α} {right : PMF β}
    (hjoint : IsPMFCoupling joint left right) :
    maximallyMarginalRepairedCoupling joint left right = joint := by
  rw [maximallyMarginalRepairedCoupling]
  have hone := maximalMarginalRepairWeight_eq_one_of_isCoupling hjoint
  rw [dif_neg (by simp [hone])]

section Measurable

variable {Ω γ : Type*} [MeasurableSpace Ω]

/-- Finite coordinate marginals are measurable whenever every joint atom is
measurable. -/
theorem measurable_pmf_map_apply_of_fintype
    (joint : Ω → PMF (α × β))
    (hjoint : ∀ edge, Measurable fun ω => joint ω edge)
    (f : α × β → γ) (x : γ) :
    Measurable fun ω => ((joint ω).map f) x := by
  simp only [PMF.map_apply, tsum_fintype]
  apply Finset.measurable_sum
  intro edge hedge
  by_cases h : x = f edge
  · simpa [h] using hjoint edge
  · simp [h]

/-- The equation (20) coefficient is measurable for a measurable finite
candidate and measurable target marginals. -/
theorem measurable_maximalMarginalRepairWeight
    (joint : Ω → PMF (α × β)) (left : Ω → PMF α) (right : Ω → PMF β)
    (hjoint : ∀ edge, Measurable fun ω => joint ω edge)
    (hleft : ∀ x, Measurable fun ω => left ω x)
    (hright : ∀ y, Measurable fun ω => right ω y) :
    Measurable fun ω =>
      maximalMarginalRepairWeight (joint ω) (left ω) (right ω) := by
  classical
  let leftCandidate : α → Ω → ENNReal := fun x ω =>
    ((joint ω).map Prod.fst) x
  let rightCandidate : β → Ω → ENNReal := fun y ω =>
    ((joint ω).map Prod.snd) y
  have hleftCandidate : ∀ x, Measurable (leftCandidate x) := fun x =>
    measurable_pmf_map_apply_of_fintype joint hjoint Prod.fst x
  have hrightCandidate : ∀ y, Measurable (rightCandidate y) := fun y =>
    measurable_pmf_map_apply_of_fintype joint hjoint Prod.snd y
  unfold maximalMarginalRepairWeight
  let ratios : Option (α ⊕ β) → Ω → ENNReal := fun i ω =>
    marginalRepairRatio (joint ω) (left ω) (right ω) i
  have hratios : ∀ i, Measurable (ratios i) := by
    intro i
    cases i with
    | none => exact measurable_const
    | some i =>
        cases i with
        | inl x =>
            dsimp only [ratios, marginalRepairRatio]
            exact Measurable.ite (measurableSet_eq_fun (hleftCandidate x)
              measurable_const) measurable_const
              ((hleft x).div (hleftCandidate x))
        | inr y =>
            dsimp only [ratios, marginalRepairRatio]
            exact Measurable.ite (measurableSet_eq_fun (hrightCandidate y)
              measurable_const) measurable_const
              ((hright y).div (hrightCandidate y))
  have hinf : Measurable
      ((Finset.univ : Finset (Option (α ⊕ β))).inf'
        Finset.univ_nonempty ratios) := by
    apply Finset.inf'_induction
    · intro f hf g hg
      exact hf.inf hg
    · intro i hi
      exact hratios i
  convert hinf using 1
  funext ω
  have happ := Finset.apply_inf'_eq_inf'_comp
    (f := ratios) Finset.univ_nonempty
    (fun f : Ω → ENNReal => f ω) (fun _ _ => rfl)
  symm
  simpa only [ratios, Function.comp_apply] using happ

/-- Algorithm 5 preserves atom measurability. -/
theorem measurable_maximallyMarginalRepairedCoupling_apply
    (joint : Ω → PMF (α × β)) (left : Ω → PMF α) (right : Ω → PMF β)
    (hjoint : ∀ edge, Measurable fun ω => joint ω edge)
    (hleft : ∀ x, Measurable fun ω => left ω x)
    (hright : ∀ y, Measurable fun ω => right ω y)
    (edge : α × β) :
    Measurable fun ω =>
      maximallyMarginalRepairedCoupling (joint ω) (left ω) (right ω) edge := by
  classical
  let weight : Ω → ENNReal := fun ω =>
    maximalMarginalRepairWeight (joint ω) (left ω) (right ω)
  have hweight : Measurable weight :=
    measurable_maximalMarginalRepairWeight joint left right hjoint hleft hright
  have hleftCandidate : Measurable fun ω => ((joint ω).map Prod.fst) edge.1 :=
    measurable_pmf_map_apply_of_fintype joint hjoint Prod.fst edge.1
  have hrightCandidate : Measurable fun ω => ((joint ω).map Prod.snd) edge.2 :=
    measurable_pmf_map_apply_of_fintype joint hjoint Prod.snd edge.2
  let repairedAtom : Ω → ENNReal := fun ω =>
    weight ω * joint ω edge + (1 - weight ω) *
      (((left ω edge.1 - weight ω * (joint ω).map Prod.fst edge.1) *
        (1 - weight ω)⁻¹) *
      ((right ω edge.2 - weight ω * (joint ω).map Prod.snd edge.2) *
        (1 - weight ω)⁻¹))
  have hrepaired : Measurable repairedAtom := by
    dsimp only [repairedAtom]
    fun_prop
  have hpiece : Measurable fun ω =>
      if weight ω < 1 then repairedAtom ω else joint ω edge :=
    Measurable.ite (measurableSet_lt hweight measurable_const)
      hrepaired (hjoint edge)
  convert hpiece using 1
  funext ω
  rw [maximallyMarginalRepairedCoupling_apply]
  rfl

end Measurable

end Mcmc.Finite
