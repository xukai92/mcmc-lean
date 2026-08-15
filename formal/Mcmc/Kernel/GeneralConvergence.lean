import Mcmc.Kernel.Coupling
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

end IsMeasureCoupling

namespace Kernel

open ProbabilityTheory

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

end Kernel
end Mcmc
