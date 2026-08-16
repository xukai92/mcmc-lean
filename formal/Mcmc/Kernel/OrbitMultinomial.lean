import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Kernel.Invariance

/-!
# Multinomial selection on a measure-preserving orbit

This module isolates the algebraic core of multinomial HMC.  A current state
is placed uniformly at one of `L + 1` trajectory indices, the other points are
obtained by signed powers of a measure-preserving permutation, and an output
index is selected proportionally to a positive finite weight.

The resulting kernel is reversible for `μ.withDensity weight`.  No separable
Hamiltonian, Euclidean momentum law, or explicit leapfrog formula is needed.
-/

open MeasureTheory
open scoped BigOperators ENNReal ProbabilityTheory

namespace Mcmc.Kernel

open ProbabilityTheory

variable {α : Type*} [MeasurableSpace α]

/-- Point `i` of an orbit whose current state is located at `origin`. -/
def orbitPoint (T : Equiv.Perm α) {L : ℕ} (origin : Fin (L + 1))
    (z : α) (i : Fin (L + 1)) : α :=
  (T ^ ((i.val : ℤ) - (origin.val : ℤ))) z

omit [MeasurableSpace α] in
@[simp]
theorem orbitPoint_origin (T : Equiv.Perm α) {L : ℕ}
    (origin : Fin (L + 1)) (z : α) : orbitPoint T origin z origin = z := by
  simp [orbitPoint]

omit [MeasurableSpace α] in
/-- Re-rooting an orbit at any indexed point leaves every indexed point
unchanged. -/
theorem orbitPoint_reroot (T : Equiv.Perm α) {L : ℕ}
    (origin selected i : Fin (L + 1)) (z : α) :
    orbitPoint T selected (orbitPoint T origin z selected) i =
      orbitPoint T origin z i := by
  rw [orbitPoint, orbitPoint, orbitPoint, ← Equiv.Perm.mul_apply,
    ← zpow_add]
  congr 1
  ring_nf

/-- Sum of weights along a nonempty finite orbit. -/
noncomputable def orbitNormalizer (weight : α → ENNReal) (T : Equiv.Perm α)
    {L : ℕ} (origin : Fin (L + 1)) (z : α) : ENNReal :=
  ∑ i, weight (orbitPoint T origin z i)

omit [MeasurableSpace α] in
theorem orbitNormalizer_ne_zero
    {weight : α → ENNReal} (hweight0 : ∀ z, weight z ≠ 0)
    (T : Equiv.Perm α) {L : ℕ} (origin : Fin (L + 1)) (z : α) :
    orbitNormalizer weight T origin z ≠ 0 := by
  apply ne_of_gt
  refine lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr
    (hweight0 (orbitPoint T origin z (0 : Fin (L + 1))))) ?_
  exact Finset.single_le_sum
    (s := Finset.univ)
    (f := fun i : Fin (L + 1) => weight (orbitPoint T origin z i))
    (fun _ _ => bot_le) (Finset.mem_univ _)

omit [MeasurableSpace α] in
theorem orbitNormalizer_ne_top
    {weight : α → ENNReal} (hweightTop : ∀ z, weight z ≠ ∞)
    (T : Equiv.Perm α) {L : ℕ} (origin : Fin (L + 1)) (z : α) :
    orbitNormalizer weight T origin z ≠ ∞ := by
  simp [orbitNormalizer, hweightTop]

/-- Normalized multinomial probability of one orbit index. -/
noncomputable def orbitIndexProbability
    (weight : α → ENNReal) (T : Equiv.Perm α) {L : ℕ}
    (origin selected : Fin (L + 1)) (z : α) : ENNReal :=
  weight (orbitPoint T origin z selected) *
    (orbitNormalizer weight T origin z)⁻¹

omit [MeasurableSpace α] in
theorem orbitNormalizer_reroot (weight : α → ENNReal) (T : Equiv.Perm α)
    {L : ℕ} (origin selected : Fin (L + 1)) (z : α) :
    orbitNormalizer weight T selected (orbitPoint T origin z selected) =
      orbitNormalizer weight T origin z := by
  unfold orbitNormalizer
  apply Finset.sum_congr rfl
  intro i _
  rw [orbitPoint_reroot]

omit [MeasurableSpace α] in
/-- Target-weighted selected-index flow is symmetric under re-rooting. -/
theorem orbitIndexProbability_flow_reroot
    (weight : α → ENNReal) (T : Equiv.Perm α) {L : ℕ}
    (origin selected : Fin (L + 1)) (z : α) :
    weight z * orbitIndexProbability weight T origin selected z =
      weight (orbitPoint T origin z selected) *
        orbitIndexProbability weight T selected origin
          (orbitPoint T origin z selected) := by
  unfold orbitIndexProbability
  rw [orbitNormalizer_reroot, orbitPoint_reroot, orbitPoint_origin]
  ac_rfl

theorem measurable_orbitPoint
    {T : Equiv.Perm α} (hT : Measurable T) (hTinv : Measurable T.symm)
    {L : ℕ} (origin i : Fin (L + 1)) :
    Measurable fun z => orbitPoint T origin z i := by
  generalize hn : (i.val : ℤ) - (origin.val : ℤ) = n
  unfold orbitPoint
  rw [hn]
  cases n with
  | ofNat n =>
      convert hT.iterate n using 1
      ext z
      change (T ^ n) z = _
      rw [Equiv.Perm.coe_pow]
  | negSucc n =>
      simp only [zpow_negSucc, Equiv.Perm.coe_inv]
      exact hTinv.iterate (n + 1)

theorem measurePreserving_orbitPoint
    {μ : Measure α} {T : Equiv.Perm α}
    (hT : MeasurePreserving T μ μ)
    (hTinv : MeasurePreserving T.symm μ μ)
    {L : ℕ} (origin i : Fin (L + 1)) :
    MeasurePreserving (fun z => orbitPoint T origin z i) μ μ := by
  generalize hn : (i.val : ℤ) - (origin.val : ℤ) = n
  unfold orbitPoint
  rw [hn]
  cases n with
  | ofNat n =>
      convert hT.iterate n using 1
      ext z
      change (T ^ n) z = _
      rw [Equiv.Perm.coe_pow]
  | negSucc n =>
      simp only [zpow_negSucc, Equiv.Perm.coe_inv]
      exact hTinv.iterate (n + 1)

theorem measurable_orbitIndexProbability
    {weight : α → ENNReal} (hweight : Measurable weight)
    {T : Equiv.Perm α} (hT : Measurable T) (hTinv : Measurable T.symm)
    {L : ℕ} (origin selected : Fin (L + 1)) :
    Measurable (orbitIndexProbability weight T origin selected) := by
  unfold orbitIndexProbability orbitNormalizer
  apply Measurable.mul
  · exact hweight.comp (measurable_orbitPoint hT hTinv origin selected)
  · apply Measurable.inv
    apply Finset.measurable_sum
    intro i _
    exact hweight.comp (measurable_orbitPoint hT hTinv origin i)

/-- Random-origin multinomial orbit transition. -/
noncomputable def orbitMultinomialKernel
    (weight : α → ENNReal) (T : Equiv.Perm α) (L : ℕ)
    (_hweight0 : ∀ z, weight z ≠ 0) (_hweightTop : ∀ z, weight z ≠ ∞)
    (hweight : Measurable weight) (hT : Measurable T)
    (hTinv : Measurable T.symm) : Kernel α α where
  toFun z := ∑ origin : Fin (L + 1),
    (PMF.uniformOfFintype (Fin (L + 1)) origin) •
      ∑ selected : Fin (L + 1),
        orbitIndexProbability weight T origin selected z •
          Measure.dirac (orbitPoint T origin z selected)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ hs]
    apply Finset.measurable_sum
    intro origin _
    apply measurable_const.mul
    apply Finset.measurable_sum
    intro selected _
    exact (measurable_orbitIndexProbability hweight hT hTinv origin selected).mul
      (measurable_const.indicator
        (measurable_orbitPoint hT hTinv origin selected hs))

theorem orbitMultinomialKernel_apply_set
    (weight : α → ENNReal) (T : Equiv.Perm α) (L : ℕ)
    (hweight0 : ∀ z, weight z ≠ 0) (hweightTop : ∀ z, weight z ≠ ∞)
    (hweight : Measurable weight) (hT : Measurable T)
    (hTinv : Measurable T.symm) (z : α) (s : Set α)
    (hs : MeasurableSet s) :
    orbitMultinomialKernel weight T L hweight0 hweightTop hweight hT hTinv z s =
      ∑ origin : Fin (L + 1),
        PMF.uniformOfFintype (Fin (L + 1)) origin *
          ∑ selected : Fin (L + 1),
            orbitIndexProbability weight T origin selected z *
              s.indicator (fun _ : α => (1 : ENNReal))
                (orbitPoint T origin z selected) := by
  change (∑ origin : Fin (L + 1),
    (PMF.uniformOfFintype (Fin (L + 1)) origin) •
      ∑ selected : Fin (L + 1),
        orbitIndexProbability weight T origin selected z •
          Measure.dirac (orbitPoint T origin z selected)) s = _
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro origin _
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul]
  congr 1

/-- A zero-length orbit contains only the current state, so multinomial
selection is exactly the identity kernel.  This boundary is important for
convergence claims: invariance still holds, but no movement is possible. -/
theorem orbitMultinomialKernel_zero
    (weight : α → ENNReal) (T : Equiv.Perm α)
    (hweight0 : ∀ z, weight z ≠ 0) (hweightTop : ∀ z, weight z ≠ ∞)
    (hweight : Measurable weight) (hT : Measurable T)
    (hTinv : Measurable T.symm) :
    orbitMultinomialKernel weight T 0 hweight0 hweightTop hweight hT hTinv =
      Kernel.id := by
  ext z s hs
  rw [orbitMultinomialKernel_apply_set weight T 0 hweight0 hweightTop
    hweight hT hTinv z s hs]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
    PMF.uniformOfFintype_apply, Fintype.card_fin, Nat.reduceAdd,
    Nat.cast_one, inv_one, one_mul, orbitIndexProbability,
    orbitNormalizer, orbitPoint, Fin.val_zero, Nat.cast_zero, sub_self,
    zpow_zero, Kernel.id_apply]
  change weight z * (weight z)⁻¹ *
    s.indicator (fun _ : α => (1 : ENNReal)) z = Measure.dirac z s
  rw [ENNReal.mul_inv_cancel (hweight0 z) (hweightTop z)]
  rw [Measure.dirac_apply' _ hs]
  by_cases hz : z ∈ s <;> simp [hz]

instance orbitMultinomialKernel_isMarkovKernel
    {weight : α → ENNReal} (hweight0 : ∀ z, weight z ≠ 0)
    (hweightTop : ∀ z, weight z ≠ ∞)
    (T : Equiv.Perm α) (L : ℕ) (hweight : Measurable weight)
    (hT : Measurable T) (hTinv : Measurable T.symm) :
    IsMarkovKernel (orbitMultinomialKernel weight T L hweight0 hweightTop
      hweight hT hTinv) := by
  constructor
  intro z
  constructor
  rw [orbitMultinomialKernel_apply_set weight T L hweight0 hweightTop
    hweight hT hTinv z Set.univ MeasurableSet.univ]
  simp only [Set.indicator_of_mem, Set.mem_univ, mul_one]
  have hsum (origin : Fin (L + 1)) :
      ∑ selected : Fin (L + 1),
          orbitIndexProbability weight T origin selected z = 1 := by
    unfold orbitIndexProbability orbitNormalizer
    rw [← Finset.sum_mul]
    exact ENNReal.mul_inv_cancel
      (orbitNormalizer_ne_zero hweight0 T origin z)
      (orbitNormalizer_ne_top hweightTop T origin z)
  calc
    _ = ∑ origin : Fin (L + 1),
        PMF.uniformOfFintype (Fin (L + 1)) origin * 1 := by
      apply Finset.sum_congr rfl
      intro origin _
      rw [hsum]
    _ = 1 := by
      simp only [mul_one]
      exact (tsum_fintype _).symm.trans (PMF.tsum_coe _)

/-- Subkernel for one ordered origin/selected pair. -/
noncomputable def orbitComponentKernel
    (weight : α → ENNReal) (T : Equiv.Perm α) {L : ℕ}
    (origin selected : Fin (L + 1)) (hweight : Measurable weight)
    (hT : Measurable T) (hTinv : Measurable T.symm) : Kernel α α where
  toFun z := orbitIndexProbability weight T origin selected z •
    Measure.dirac (orbitPoint T origin z selected)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp only [Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul]
    exact (measurable_orbitIndexProbability hweight hT hTinv origin selected).mul
      (measurable_const.indicator
        (measurable_orbitPoint hT hTinv origin selected hs))

theorem orbitComponentKernel_apply
    (weight : α → ENNReal) (T : Equiv.Perm α) {L : ℕ}
    (origin selected : Fin (L + 1)) (hweight : Measurable weight)
    (hT : Measurable T) (hTinv : Measurable T.symm)
    (z : α) (s : Set α) (hs : MeasurableSet s) :
    orbitComponentKernel weight T origin selected hweight hT hTinv z s =
      orbitIndexProbability weight T origin selected z *
        s.indicator (fun _ : α => (1 : ENNReal))
          (orbitPoint T origin z selected) := by
  change (orbitIndexProbability weight T origin selected z •
    Measure.dirac (orbitPoint T origin z selected)) s = _
  by_cases hmem : orbitPoint T origin z selected ∈ s <;>
    simp [Measure.dirac_apply' _ hs, Set.indicator, hmem]

/-- Ordered-index flow satisfies balance after swapping its two indices. -/
theorem orbitComponentKernel_balance
    {μ : Measure α} {weight : α → ENNReal} (hweight : Measurable weight)
    {T : Equiv.Perm α} (hT : MeasurePreserving T μ μ)
    (hTinv : MeasurePreserving T.symm μ μ) {L : ℕ}
    (origin selected : Fin (L + 1))
    {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫⁻ z in A, orbitComponentKernel weight T origin selected hweight
        hT.measurable hTinv.measurable z B ∂μ.withDensity weight =
      ∫⁻ z in B, orbitComponentKernel weight T selected origin hweight
        hT.measurable hTinv.measurable z A ∂μ.withDensity weight := by
  rw [setLIntegral_withDensity_eq_setLIntegral_mul μ hweight
    ((orbitComponentKernel weight T origin selected hweight hT.measurable
      hTinv.measurable).measurable_coe hB) hA]
  rw [setLIntegral_withDensity_eq_setLIntegral_mul μ hweight
    ((orbitComponentKernel weight T selected origin hweight hT.measurable
      hTinv.measurable).measurable_coe hA) hB]
  rw [← lintegral_indicator hA, ← lintegral_indicator hB]
  simp_rw [orbitComponentKernel_apply weight T origin selected hweight
    hT.measurable hTinv.measurable _ B hB]
  simp_rw [orbitComponentKernel_apply weight T selected origin hweight
    hT.measurable hTinv.measurable _ A hA]
  let reverse : α → ENNReal := fun z =>
    (B ∩ (fun z => orbitPoint T selected z origin) ⁻¹' A).indicator
      (fun z => weight z * orbitIndexProbability weight T selected origin z) z
  have hreverse : Measurable reverse := by
    apply Measurable.indicator
    · exact hweight.mul (measurable_orbitIndexProbability hweight
        hT.measurable hTinv.measurable selected origin)
    · exact hB.inter (measurable_orbitPoint hT.measurable hTinv.measurable
        selected origin hA)
  have hrhs :
      (fun z => B.indicator (weight * fun a =>
        orbitIndexProbability weight T selected origin a *
          A.indicator (fun _ : α => (1 : ENNReal))
            (orbitPoint T selected a origin)) z) = reverse := by
    funext z
    by_cases hzB : z ∈ B <;>
      by_cases hzA : orbitPoint T selected z origin ∈ A <;>
        simp [reverse, Set.indicator, hzA, hzB]
  rw [hrhs]
  rw [← (measurePreserving_orbitPoint hT hTinv origin selected).lintegral_comp
    hreverse]
  apply lintegral_congr
  intro z
  have hback : orbitPoint T selected (orbitPoint T origin z selected) origin = z := by
    rw [orbitPoint_reroot, orbitPoint_origin]
  have hflow := orbitIndexProbability_flow_reroot weight T origin selected z
  by_cases hzA : z ∈ A <;>
    by_cases hzB : orbitPoint T origin z selected ∈ B <;>
      simp [reverse, Set.indicator, hzA, hzB, hback, ← hflow]

private theorem orbitMultinomialKernel_flow_sum
    {μ : Measure α} {weight : α → ENNReal}
    (hweight0 : ∀ z, weight z ≠ 0) (hweightTop : ∀ z, weight z ≠ ∞)
    (hweight : Measurable weight) {T : Equiv.Perm α}
    (hT : MeasurePreserving T μ μ) (hTinv : MeasurePreserving T.symm μ μ)
    (L : ℕ) {A B : Set α} (_hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫⁻ z in A, orbitMultinomialKernel weight T L hweight0 hweightTop hweight
        hT.measurable hTinv.measurable z B ∂μ.withDensity weight =
      ∑ origin : Fin (L + 1),
        PMF.uniformOfFintype (Fin (L + 1)) origin *
          ∑ selected : Fin (L + 1),
            ∫⁻ z in A, orbitComponentKernel weight T origin selected hweight
              hT.measurable hTinv.measurable z B ∂μ.withDensity weight := by
  simp_rw [orbitMultinomialKernel_apply_set weight T L hweight0 hweightTop
    hweight hT.measurable hTinv.measurable _ B hB]
  simp_rw [orbitComponentKernel_apply weight T _ _ hweight hT.measurable
    hTinv.measurable _ B hB]
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro origin _
    change (∫⁻ z in A,
        PMF.uniformOfFintype (Fin (L + 1)) origin *
          (∑ selected : Fin (L + 1),
            orbitIndexProbability weight T origin selected z *
              B.indicator (fun _ : α => (1 : ENNReal))
                (orbitPoint T origin z selected))
        ∂μ.withDensity weight) = _
    change (∫⁻ z,
        PMF.uniformOfFintype (Fin (L + 1)) origin *
          (∑ selected : Fin (L + 1),
            orbitIndexProbability weight T origin selected z *
              B.indicator (fun _ : α => (1 : ENNReal))
                (orbitPoint T origin z selected))
        ∂(μ.withDensity weight).restrict A) = _
    have hsumMeas : Measurable fun z =>
        ∑ selected : Fin (L + 1),
          orbitIndexProbability weight T origin selected z *
            B.indicator (fun _ : α => (1 : ENNReal))
              (orbitPoint T origin z selected) :=
      Finset.measurable_sum _ fun selected _ =>
      (measurable_orbitIndexProbability hweight hT.measurable hTinv.measurable
        origin selected).mul (measurable_const.indicator
          (measurable_orbitPoint hT.measurable hTinv.measurable
            origin selected hB))
    calc
      _ = PMF.uniformOfFintype (Fin (L + 1)) origin *
          ∫⁻ z, (∑ selected : Fin (L + 1),
            orbitIndexProbability weight T origin selected z *
              B.indicator (fun _ : α => (1 : ENNReal))
                (orbitPoint T origin z selected))
            ∂(μ.withDensity weight).restrict A :=
        lintegral_const_mul _ hsumMeas
      _ = _ := by
        congr 1
        exact lintegral_finsetSum Finset.univ (fun selected _ =>
          (measurable_orbitIndexProbability hweight hT.measurable
            hTinv.measurable origin selected).mul
              (measurable_const.indicator
                (measurable_orbitPoint hT.measurable hTinv.measurable
                  origin selected hB)))
  · intro origin _
    exact measurable_const.mul (Finset.measurable_sum _ fun selected _ =>
      (measurable_orbitIndexProbability hweight hT.measurable hTinv.measurable
        origin selected).mul (measurable_const.indicator
          (measurable_orbitPoint hT.measurable hTinv.measurable
            origin selected hB)))

/-- The random-origin orbit transition is reversible for the weighted base
measure. -/
theorem orbitMultinomialKernel_isReversible
    {μ : Measure α} {weight : α → ENNReal}
    (hweight0 : ∀ z, weight z ≠ 0) (hweightTop : ∀ z, weight z ≠ ∞)
    (hweight : Measurable weight) {T : Equiv.Perm α}
    (hT : MeasurePreserving T μ μ)
    (hTinv : MeasurePreserving T.symm μ μ) (L : ℕ) :
    (orbitMultinomialKernel weight T L hweight0 hweightTop hweight
      hT.measurable hTinv.measurable).IsReversible (μ.withDensity weight) := by
  intro A B hA hB
  rw [orbitMultinomialKernel_flow_sum hweight0 hweightTop hweight hT hTinv L hA hB]
  rw [orbitMultinomialKernel_flow_sum hweight0 hweightTop hweight hT hTinv L hB hA]
  trans ∑ origin : Fin (L + 1),
      PMF.uniformOfFintype (Fin (L + 1)) origin *
        ∑ selected : Fin (L + 1),
          ∫⁻ z in B, orbitComponentKernel weight T selected origin hweight
            hT.measurable hTinv.measurable z A ∂μ.withDensity weight
  · apply Finset.sum_congr rfl
    intro origin _
    congr 1
    apply Finset.sum_congr rfl
    intro selected _
    exact orbitComponentKernel_balance hweight hT hTinv origin selected hA hB
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]

/-- Reversibility gives invariance of the weighted measure. -/
theorem orbitMultinomialKernel_invariant
    {μ : Measure α} {weight : α → ENNReal}
    (hweight0 : ∀ z, weight z ≠ 0) (hweightTop : ∀ z, weight z ≠ ∞)
    (hweight : Measurable weight) {T : Equiv.Perm α}
    (hT : MeasurePreserving T μ μ)
    (hTinv : MeasurePreserving T.symm μ μ) (L : ℕ) :
    (orbitMultinomialKernel weight T L hweight0 hweightTop hweight
      hT.measurable hTinv.measurable).Invariant (μ.withDensity weight) :=
  (orbitMultinomialKernel_isReversible hweight0 hweightTop hweight hT hTinv L).invariant

end Mcmc.Kernel
