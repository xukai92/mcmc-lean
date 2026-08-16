import Mcmc.Kernel.MeetingDrift
import Mathlib.MeasureTheory.Measure.Sub

/-!
# General-state quantitative convergence through couplings

This module supplies the eventwise coupling inequality and a geometric
kernel-power consequence.  Unlike stationarity, these statements quantify
convergence of transition laws.  They are designed as the target interface
for Doeblin and independence-Metropolis minorization arguments.
!-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace Mcmc

variable {α : Type*} [MeasurableSpace α]

namespace IsMeasureCoupling

/-- The probability assigned differently by two marginal laws on any event
is controlled by the coupling's off-diagonal mass. -/
theorem fst_apply_le_snd_apply_add_compl_diagonal
    {ρ : Measure (α × α)} {μ ν : Measure α}
    (h : IsMeasureCoupling ρ μ ν) {s : Set α} (hs : MeasurableSet s) :
    μ s ≤ ν s + ρ (Set.diagonal α)ᶜ := by
  let A : Set (α × α) := Prod.fst ⁻¹' s
  let B : Set (α × α) := Prod.snd ⁻¹' s
  have hsubset : A ⊆ B ∪ (Set.diagonal α)ᶜ := by
    intro z hz
    by_cases heq : z.1 = z.2
    · left
      change z.1 ∈ s at hz
      change z.2 ∈ s
      rw [← heq]
      exact hz
    · right
      simpa [Set.mem_diagonal_iff] using heq
  calc
    μ s = ρ A := by
      rw [← h.fst, Measure.fst_apply hs]
    _ ≤ ρ (B ∪ (Set.diagonal α)ᶜ) := measure_mono hsubset
    _ ≤ ρ B + ρ (Set.diagonal α)ᶜ := measure_union_le _ _
    _ = ν s + ρ (Set.diagonal α)ᶜ := by
      rw [← h.snd, Measure.snd_apply hs]

/-- Symmetric eventwise coupling inequality. -/
theorem snd_apply_le_fst_apply_add_compl_diagonal
    {ρ : Measure (α × α)} {μ ν : Measure α}
    (h : IsMeasureCoupling ρ μ ν) {s : Set α} (hs : MeasurableSet s) :
    ν s ≤ μ s + ρ (Set.diagonal α)ᶜ := by
  let A : Set (α × α) := Prod.snd ⁻¹' s
  let B : Set (α × α) := Prod.fst ⁻¹' s
  have hsubset : A ⊆ B ∪ (Set.diagonal α)ᶜ := by
    intro z hz
    by_cases heq : z.1 = z.2
    · left
      change z.2 ∈ s at hz
      change z.1 ∈ s
      rw [heq]
      exact hz
    · right
      simpa [Set.mem_diagonal_iff] using heq
  calc
    ν s = ρ A := by
      rw [← h.snd, Measure.snd_apply hs]
    _ ≤ ρ (B ∪ (Set.diagonal α)ᶜ) := measure_mono hsubset
    _ ≤ ρ B + ρ (Set.diagonal α)ᶜ := measure_union_le _ _
    _ = μ s + ρ (Set.diagonal α)ᶜ := by
      rw [← h.fst, Measure.fst_apply hs]

end IsMeasureCoupling

namespace Kernel

open ProbabilityTheory

/-- A faithful path-law meeting tail controls the eventwise discrepancy of
two marginal chains, even when their initial laws differ. -/
theorem lawAtTime_left_apply_le_right_add_exactMeetingTail
    [MeasurableEq α]
    (initialCoupling : Measure (α × α)) [IsProbabilityMeasure initialCoupling]
    (leftInitial rightInitial : Measure α)
    (transition : Kernel α α) [IsMarkovKernel transition]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (hinitial : IsMeasureCoupling initialCoupling leftInitial rightInitial)
    (hcoupled : IsCoupling coupled transition transition)
    (hfaithful : IsFaithful coupled) (n : ℕ)
    {s : Set α} (hs : MeasurableSet s) :
    lawAtTime leftInitial transition n s ≤
      lawAtTime rightInitial transition n s +
        exactMeetingTail (pathLaw initialCoupling coupled) n := by
  have hmarginals := lawAtTime_isMeasureCoupling initialCoupling
    leftInitial rightInitial coupled transition transition hinitial hcoupled n
  have hcoupling := hmarginals.fst_apply_le_snd_apply_add_compl_diagonal hs
  rw [← offDiagonalMassAtTime_eq_exactMeetingTail_pathLaw_of_faithful
    initialCoupling coupled hfaithful n]
  exact hcoupling

/-- Symmetric eventwise form of the heterogeneous-initialization meeting-tail
bound. -/
theorem lawAtTime_right_apply_le_left_add_exactMeetingTail
    [MeasurableEq α]
    (initialCoupling : Measure (α × α)) [IsProbabilityMeasure initialCoupling]
    (leftInitial rightInitial : Measure α)
    (transition : Kernel α α) [IsMarkovKernel transition]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (hinitial : IsMeasureCoupling initialCoupling leftInitial rightInitial)
    (hcoupled : IsCoupling coupled transition transition)
    (hfaithful : IsFaithful coupled) (n : ℕ)
    {s : Set α} (hs : MeasurableSet s) :
    lawAtTime rightInitial transition n s ≤
      lawAtTime leftInitial transition n s +
        exactMeetingTail (pathLaw initialCoupling coupled) n := by
  have hmarginals := lawAtTime_isMeasureCoupling initialCoupling
    leftInitial rightInitial coupled transition transition hinitial hcoupled n
  have hcoupling := hmarginals.snd_apply_le_fst_apply_add_compl_diagonal hs
  rw [← offDiagonalMassAtTime_eq_exactMeetingTail_pathLaw_of_faithful
    initialCoupling coupled hfaithful n]
  exact hcoupling

/-- If the right marginal starts stationary, the coupling tail directly
controls eventwise convergence of the left chain. -/
theorem lawAtTime_apply_le_invariant_add_exactMeetingTail
    [MeasurableEq α]
    (initialCoupling : Measure (α × α)) [IsProbabilityMeasure initialCoupling]
    (leftInitial target : Measure α)
    (transition : Kernel α α) [IsMarkovKernel transition]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (hinitial : IsMeasureCoupling initialCoupling leftInitial target)
    (hcoupled : IsCoupling coupled transition transition)
    (hfaithful : IsFaithful coupled) (hinvariant : transition.Invariant target)
    (n : ℕ) {s : Set α} (hs : MeasurableSet s) :
    lawAtTime leftInitial transition n s ≤
      target s + exactMeetingTail (pathLaw initialCoupling coupled) n := by
  simpa only [lawAtTime_eq_of_invariant target transition hinvariant n] using
    lawAtTime_left_apply_le_right_add_exactMeetingTail initialCoupling
      leftInitial target transition coupled hinitial hcoupled hfaithful n hs

/-- A kernel uniformly minorizes a measure with coefficient `ε`. -/
def UniformlyMinorizes (transition : Kernel α α) (ε : ENNReal)
    (target : Measure α) : Prop :=
  ∀ x s, MeasurableSet s → ε * target s ≤ transition x s

private theorem minorization_measure_le
    (transition : Kernel α α) (target : Measure α) (ε : ENNReal)
    (hminor : UniformlyMinorizes transition ε target) (x : α) :
    ε • target ≤ transition x := by
  apply Measure.le_iff.mpr
  intro s hs
  simpa [Measure.smul_apply, smul_eq_mul] using hminor x s hs

/-- The residual transition obtained by removing a strict Doeblin component
and renormalizing the remaining row mass. -/
noncomputable def minorizationResidual
    (transition : Kernel α α) [IsMarkovKernel transition]
    (target : Measure α) [IsProbabilityMeasure target]
    (ε : Set.Icc (0 : NNReal) 1) (_hε : ε.1 < 1)
    (hminor : UniformlyMinorizes transition ε.1 target) : Kernel α α where
  toFun x := (((1 - ε.1 : NNReal) : ENNReal)⁻¹) •
    (transition x - (ε.1 : ENNReal) • target)
  measurable' := by
    letI : IsFiniteMeasure ((ε.1 : ENNReal) • target) :=
      target.smul_finite ENNReal.coe_ne_top
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    have hinner : Measurable (fun x => transition x s -
        (ε.1 : ENNReal) * target s) :=
      (transition.measurable_coe hs).sub measurable_const
    have houter : Measurable (fun x =>
        (((1 - ε.1 : NNReal) : ENNReal)⁻¹) *
          (transition x s - (ε.1 : ENNReal) * target s)) :=
      measurable_const.mul hinner
    convert houter using 1
    funext x
    rw [Measure.smul_apply, smul_eq_mul, Measure.sub_apply hs
      (minorization_measure_le transition target ε.1 hminor x),
      Measure.smul_apply, smul_eq_mul]

instance minorizationResidual.instIsMarkovKernel
    (transition : Kernel α α) [IsMarkovKernel transition]
    (target : Measure α) [IsProbabilityMeasure target]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hminor : UniformlyMinorizes transition ε.1 target) :
    IsMarkovKernel (minorizationResidual transition target ε hε hminor) where
  isProbabilityMeasure x := by
    letI : IsFiniteMeasure ((ε.1 : ENNReal) • target) :=
      target.smul_finite ENNReal.coe_ne_top
    constructor
    change ((↑(1 - ε.1) : ENNReal)⁻¹) *
      ((transition x - (ε.1 : ENNReal) • target) Set.univ) = 1
    rw [Measure.sub_apply MeasurableSet.univ
      (minorization_measure_le transition target ε.1 hminor x),
      Measure.smul_apply, measure_univ, measure_univ, smul_eq_mul]
    simp only [mul_one]
    have hcoe : ((1 - ε.1 : NNReal) : ENNReal) =
        1 - (ε.1 : ENNReal) := ENNReal.coe_sub
    rw [← hcoe]
    have hrpos : 0 < (1 - ε.1 : NNReal) := tsub_pos_iff_lt.mpr hε
    exact ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.mpr hrpos.ne') ENNReal.coe_ne_top

/-- Removing and then restoring the Doeblin component recovers every original
transition row exactly. -/
theorem mixture_minorizationResidual_eq
    (transition : Kernel α α) [IsMarkovKernel transition]
    (target : Measure α) [IsProbabilityMeasure target]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hminor : UniformlyMinorizes transition ε.1 target) :
    Mcmc.Kernel.mixture ε (Kernel.const α target)
      (minorizationResidual transition target ε hε hminor) = transition := by
  letI : IsFiniteMeasure ((ε.1 : ENNReal) • target) :=
    target.smul_finite ENNReal.coe_ne_top
  ext x s hs
  rw [Mcmc.Kernel.mixture_apply, Measure.add_apply, Kernel.const_apply]
  change (ε.1 : ENNReal) * target s +
    ((1 - ε.1 : NNReal) : ENNReal) *
      (((1 - ε.1 : NNReal) : ENNReal)⁻¹ *
        ((transition x - (ε.1 : ENNReal) • target) s)) = transition x s
  rw [Measure.sub_apply hs
    (minorization_measure_le transition target ε.1 hminor x),
    Measure.smul_apply, smul_eq_mul]
  have hrpos : 0 < (1 - ε.1 : NNReal) := tsub_pos_iff_lt.mpr hε
  have hr0 : ((1 - ε.1 : NNReal) : ENNReal) ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr hrpos.ne'
  rw [← mul_assoc, ENNReal.mul_inv_cancel hr0 ENNReal.coe_ne_top, one_mul,
    add_tsub_cancel_of_le
      (hminor x s hs)]

/-- If the original transition preserves the minorized probability measure,
then its normalized residual transition preserves it as well. -/
theorem minorizationResidual_invariant
    (transition : Kernel α α) [IsMarkovKernel transition]
    (target : Measure α) [IsProbabilityMeasure target]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hminor : UniformlyMinorizes transition ε.1 target)
    (hinvariant : transition.Invariant target) :
    (minorizationResidual transition target ε hε hminor).Invariant target := by
  let residual := minorizationResidual transition target ε hε hminor
  have hmixture : (Mcmc.Kernel.mixture ε (Kernel.const α target) residual).Invariant
      target := by
    rw [mixture_minorizationResidual_eq transition target ε hε hminor]
    exact hinvariant
  rw [ProbabilityTheory.Kernel.Invariant] at hmixture ⊢
  rw [mixture_comp_measure, Measure.const_comp, measure_univ, one_smul] at hmixture
  ext s hs
  change (residual ∘ₘ target) s = target s
  have heq := congrArg (fun μ : Measure α => μ s) hmixture
  simp only [Measure.add_apply, Measure.smul_apply, ENNReal.smul_def,
    smul_eq_mul] at heq
  have htargetTop : target s ≠ ∞ := measure_ne_top target s
  have hleftTop : (ε.1 : ENNReal) * target s ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top htargetTop
  have hbase : (ε.1 : ENNReal) * target s +
      ((1 - ε.1 : NNReal) : ENNReal) * target s = target s := by
    rw [← add_mul, ← ENNReal.coe_add, add_tsub_cancel_of_le ε.property.2]
    simp
  have hscaled : ((1 - ε.1 : NNReal) : ENNReal) *
      (residual ∘ₘ target) s =
      ((1 - ε.1 : NNReal) : ENNReal) * target s := by
    apply (ENNReal.add_left_inj hleftTop).mp
    simpa [add_comm] using heq.trans hbase.symm
  have hrpos : 0 < (1 - ε.1 : NNReal) := tsub_pos_iff_lt.mpr hε
  apply (ENNReal.mul_left_inj (ENNReal.coe_ne_zero.mpr hrpos.ne')
    ENNReal.coe_ne_top).mp
  simpa [mul_comm] using hscaled

/-- Evolving any probability law through a minorized transition exposes the
same refresh/residual mixture as the pointwise kernel decomposition. -/
theorem minorized_comp_measure_eq
    (transition : Kernel α α) [IsMarkovKernel transition]
    (target initial : Measure α) [IsProbabilityMeasure target]
    [IsProbabilityMeasure initial]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hminor : UniformlyMinorizes transition ε.1 target) :
    transition ∘ₘ initial =
      (ε.1 : ENNReal) • target + ((1 - ε.1 : NNReal) : ENNReal) •
        (minorizationResidual transition target ε hε hminor ∘ₘ initial) := by
  let residual := minorizationResidual transition target ε hε hminor
  calc
    transition ∘ₘ initial =
        Mcmc.Kernel.mixture ε (Kernel.const α target) residual ∘ₘ initial := by
      exact congrArg (fun k : Kernel α α => k ∘ₘ initial)
        (mixture_minorizationResidual_eq transition target ε hε hminor).symm
    _ = (ε.1 : ENNReal) • target +
        ((1 - ε.1 : NNReal) : ENNReal) • (residual ∘ₘ initial) := by
      rw [mixture_comp_measure, Measure.const_comp, measure_univ, one_smul]
      ext s hs
      simp only [Measure.add_apply, Measure.smul_apply]
      rfl

/-- Exact regenerative representation of every finite-time law.  Its first
coefficient is the probability that at least one refresh has occurred; the
second is the probability of taking only residual branches. -/
theorem lawAtTime_eq_refresh_add_residual
    (transition : Kernel α α) [IsMarkovKernel transition]
    (target initial : Measure α) [IsProbabilityMeasure target]
    [IsProbabilityMeasure initial]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hminor : UniformlyMinorizes transition ε.1 target)
    (hinvariant : transition.Invariant target) (n : ℕ) :
    lawAtTime initial transition n =
      ((1 - (1 - ε.1) ^ n : NNReal) : ENNReal) • target +
        (((1 - ε.1) ^ n : NNReal) : ENNReal) •
          lawAtTime initial
            (minorizationResidual transition target ε hε hminor) n := by
  let residual := minorizationResidual transition target ε hε hminor
  have hresidual : residual.Invariant target :=
    minorizationResidual_invariant transition target ε hε hminor hinvariant
  induction n with
  | zero => simp [lawAtTime_zero]
  | succ n ih =>
      rw [lawAtTime_succ,
        minorized_comp_measure_eq transition target
          (lawAtTime initial transition n) ε hε hminor,
        ih, Measure.comp_add]
      simp_rw [Measure.comp_smul]
      rw [hresidual.def, ← lawAtTime_succ]
      simp only [pow_succ]
      let r : NNReal := 1 - ε.1
      have hrle : r ≤ 1 := by simp [r]
      have hrpowle : r ^ n ≤ 1 := pow_le_one₀ (by positivity) hrle
      have hrprodle : r ^ n * r ≤ 1 := by
        exact mul_le_one₀ hrpowle (by positivity) hrle
      have hsum : ε.1 + r = 1 := by
        simp [r, add_tsub_cancel_of_le ε.property.2]
      have hcoef : ε.1 + r * (1 - r ^ n) = 1 - r ^ n * r := by
        apply NNReal.eq
        have hsumR := congrArg (fun z : NNReal => (z : ℝ)) hsum
        norm_num at hsumR
        simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_sub hrpowle,
          NNReal.coe_sub hrprodle, NNReal.coe_one]
        nlinarith
      ext s hs
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      change (ε.1 : ENNReal) * target s + (r : ENNReal) *
          (((1 - r ^ n : NNReal) : ENNReal) * target s +
            ((r ^ n : NNReal) : ENNReal) *
              lawAtTime initial residual (n + 1) s) =
        ((1 - r ^ n * r : NNReal) : ENNReal) * target s +
          ((r ^ n * r : NNReal) : ENNReal) *
            lawAtTime initial residual (n + 1) s
      rw [mul_add, ← mul_assoc, ← mul_assoc, ← ENNReal.coe_mul,
        ← ENNReal.coe_mul, ← add_assoc, ← add_mul, ← ENNReal.coe_add,
        hcoef]
      simp [mul_comm]

/-- The regenerative representation gives the upper half of an eventwise
total-variation bound with geometric remainder `(1-ε)^n`. -/
theorem lawAtTime_apply_le_target_add_geometric
    (transition : Kernel α α) [IsMarkovKernel transition]
    (target initial : Measure α) [IsProbabilityMeasure target]
    [IsProbabilityMeasure initial]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hminor : UniformlyMinorizes transition ε.1 target)
    (hinvariant : transition.Invariant target) (n : ℕ)
    {s : Set α} (_hs : MeasurableSet s) :
    lawAtTime initial transition n s ≤
      target s + (((1 - ε.1) ^ n : NNReal) : ENNReal) := by
  rw [lawAtTime_eq_refresh_add_residual transition target initial ε hε
    hminor hinvariant n, Measure.add_apply, Measure.smul_apply,
    Measure.smul_apply]
  let r : NNReal := (1 - ε.1) ^ n
  have hrle : r ≤ 1 := pow_le_one₀ (by positivity) (by simp)
  have hresidual : lawAtTime initial
      (minorizationResidual transition target ε hε hminor) n s ≤ 1 := by
    calc
      _ ≤ lawAtTime initial
          (minorizationResidual transition target ε hε hminor) n Set.univ :=
        measure_mono (Set.subset_univ s)
      _ = 1 := measure_univ
  change ((1 - r : NNReal) : ENNReal) * target s + (r : ENNReal) * _ ≤
    target s + (r : ENNReal)
  calc
    _ ≤ 1 * target s + (r : ENNReal) * 1 := by
      gcongr
      exact_mod_cast (show 1 - r ≤ 1 from tsub_le_self)
    _ = target s + (r : ENNReal) := by simp

/-- The symmetric half of the eventwise geometric bound. -/
theorem target_apply_le_lawAtTime_add_geometric
    (transition : Kernel α α) [IsMarkovKernel transition]
    (target initial : Measure α) [IsProbabilityMeasure target]
    [IsProbabilityMeasure initial]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hminor : UniformlyMinorizes transition ε.1 target)
    (hinvariant : transition.Invariant target) (n : ℕ)
    {s : Set α} (_hs : MeasurableSet s) :
    target s ≤ lawAtTime initial transition n s +
      (((1 - ε.1) ^ n : NNReal) : ENNReal) := by
  rw [lawAtTime_eq_refresh_add_residual transition target initial ε hε
    hminor hinvariant n, Measure.add_apply, Measure.smul_apply,
    Measure.smul_apply]
  let r : NNReal := (1 - ε.1) ^ n
  have hrle : r ≤ 1 := pow_le_one₀ (by positivity) (by simp)
  have hsplit : ((1 - r : NNReal) : ENNReal) * target s +
      (r : ENNReal) * target s = target s := by
    rw [← add_mul, ← ENNReal.coe_add, tsub_add_cancel_of_le hrle]
    simp
  calc
    target s = ((1 - r : NNReal) : ENNReal) * target s +
        (r : ENNReal) * target s := hsplit.symm
    _ ≤ (((1 - r : NNReal) : ENNReal) * target s +
          (r : ENNReal) * lawAtTime initial
            (minorizationResidual transition target ε hε hminor) n s) + r := by
      have hb : (r : ENNReal) * target s ≤ (r : ENNReal) := by
        have ht : target s ≤ (1 : ENNReal) := calc
          target s ≤ target Set.univ := measure_mono (Set.subset_univ s)
          _ = 1 := measure_univ
        calc
          (r : ENNReal) * target s ≤ r * 1 :=
            mul_le_mul_right ht (r : ENNReal)
          _ = r := mul_one _
      calc
        _ ≤ ((1 - r : NNReal) : ENNReal) * target s + r :=
          add_le_add_right hb _
        _ ≤ (((1 - r : NNReal) : ENNReal) * target s +
              (r : ENNReal) * lawAtTime initial
                (minorizationResidual transition target ε hε hminor) n s) + r := by
          gcongr
          exact le_add_right le_rfl

/-- A coupling certificate giving a uniform geometric off-diagonal bound for
all finite iterates. -/
structure HasGeometricCoupling
    (transition : Kernel α α) (rate : ENNReal) where
  coupled : Kernel (α × α) (α × α)
  isCoupling : IsCoupling coupled transition transition
  offDiagonal_le : ∀ n x,
    (coupled ^ n) x (Set.diagonal α)ᶜ ≤ rate ^ n

/-- A geometric coupling yields an explicit eventwise convergence bound
between chains started from arbitrary states. This is a quantitative
general-state conclusion, strictly stronger than invariance. -/
theorem HasGeometricCoupling.pow_apply_le_add
    {transition : Kernel α α} {rate : ENNReal}
    (h : HasGeometricCoupling transition rate)
    (n : ℕ) (x y : α) {s : Set α} (hs : MeasurableSet s) :
    (transition ^ n) x s ≤ (transition ^ n) y s + rate ^ n := by
  have hc := pow_isCoupling h.coupled transition transition h.isCoupling n
  have hm : IsMeasureCoupling ((h.coupled ^ n) (x, y))
      ((transition ^ n) x) ((transition ^ n) y) := by
    exact ⟨hc.fst_apply (x, y), hc.snd_apply (x, y)⟩
  apply (hm.fst_apply_le_snd_apply_add_compl_diagonal hs).trans
  gcongr
  exact h.offDiagonal_le n (x, y)

/-- The symmetric eventwise form follows by exchanging the initial states. -/
theorem HasGeometricCoupling.pow_apply_le_add_symm
    {transition : Kernel α α} {rate : ENNReal}
    (h : HasGeometricCoupling transition rate)
    (n : ℕ) (x y : α) {s : Set α} (hs : MeasurableSet s) :
    (transition ^ n) y s ≤ (transition ^ n) x s + rate ^ n :=
  h.pow_apply_le_add n y x hs

section StationaryTarget

variable [MeasurableEq α]

/-- A uniform geometric coupling also couples a point-started chain to a
stationary target-started chain. Its off-diagonal mass keeps the same bound. -/
theorem HasGeometricCoupling.exists_stationaryCoupling
    {transition : Kernel α α} [IsMarkovKernel transition]
    {rate : ENNReal} (h : HasGeometricCoupling transition rate)
    (target : Measure α) [IsProbabilityMeasure target]
    (hinvariant : transition.Invariant target) (x : α) (n : ℕ) :
    ∃ ρ : Measure (α × α),
      IsMeasureCoupling ρ (lawAtTime (Measure.dirac x) transition n) target ∧
        ρ (Set.diagonal α)ᶜ ≤ rate ^ n := by
  let initial : Measure (α × α) := (Measure.dirac x).prod target
  let ρ := lawAtTime initial h.coupled n
  have hinitial : IsMeasureCoupling initial (Measure.dirac x) target :=
    isMeasureCoupling_prod _ _
  have hmarginals := lawAtTime_isMeasureCoupling initial
    (Measure.dirac x) target h.coupled transition transition hinitial
    h.isCoupling n
  have htarget : lawAtTime target transition n = target :=
    lawAtTime_eq_of_invariant target transition hinvariant n
  refine ⟨ρ, ?_, ?_⟩
  · simpa [ρ, htarget] using hmarginals
  · change lawAtTime initial h.coupled n (Set.diagonal α)ᶜ ≤ rate ^ n
    rw [lawAtTime, Measure.bind_apply measurableSet_diagonal.compl
      (h.coupled ^ n).aemeasurable]
    calc
      (∫⁻ z, (h.coupled ^ n) z (Set.diagonal α)ᶜ ∂initial) ≤
          ∫⁻ _z, rate ^ n ∂initial := by
        apply lintegral_mono
        intro z
        exact h.offDiagonal_le n z
      _ = rate ^ n := by simp [initial]

/-- Quantitative eventwise marginal convergence from any Dirac start to an
invariant probability target. This is a convergence statement, not merely
stationarity. -/
theorem HasGeometricCoupling.lawAtTime_dirac_apply_le_target_add
    {transition : Kernel α α} [IsMarkovKernel transition]
    {rate : ENNReal} (h : HasGeometricCoupling transition rate)
    (target : Measure α) [IsProbabilityMeasure target]
    (hinvariant : transition.Invariant target) (x : α) (n : ℕ)
    {s : Set α} (hs : MeasurableSet s) :
    lawAtTime (Measure.dirac x) transition n s ≤ target s + rate ^ n := by
  obtain ⟨ρ, hρ, hoff⟩ :=
    h.exists_stationaryCoupling target hinvariant x n
  exact (hρ.fst_apply_le_snd_apply_add_compl_diagonal hs).trans
    (add_le_add_right hoff _)

theorem HasGeometricCoupling.target_apply_le_lawAtTime_dirac_add
    {transition : Kernel α α} [IsMarkovKernel transition]
    {rate : ENNReal} (h : HasGeometricCoupling transition rate)
    (target : Measure α) [IsProbabilityMeasure target]
    (hinvariant : transition.Invariant target) (x : α) (n : ℕ)
    {s : Set α} (hs : MeasurableSet s) :
    target s ≤ lawAtTime (Measure.dirac x) transition n s + rate ^ n := by
  obtain ⟨ρ, hρ, hoff⟩ :=
    h.exists_stationaryCoupling target hinvariant x n
  exact (hρ.snd_apply_le_fst_apply_add_compl_diagonal hs).trans
    (add_le_add_right hoff _)

end StationaryTarget

end Kernel
end Mcmc
