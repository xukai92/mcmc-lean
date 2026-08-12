import McmcLean.Finite.MarkovKernel
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic

/-!
# Embedding finite kernels into mathlib

This file connects the elementary finite distributions and Markov kernels in
`McmcLean.Finite` to mathlib's `PMF`, `Measure`, and
`ProbabilityTheory.Kernel` interfaces.  The elementary layer remains
independent of measure theory; this module is the interoperability boundary.
-/

open scoped BigOperators ENNReal MeasureTheory ProbabilityTheory

namespace McmcLean.Finite
namespace MarkovKernel

open MeasureTheory ProbabilityTheory

variable {State : Type*} [Fintype State]

namespace Distribution

/-- A finite distribution as a mathlib probability mass function. -/
noncomputable def toPMF (π : Distribution State) : PMF State :=
  PMF.ofFintype (fun x => ENNReal.ofReal (π.mass x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · simp [π.sum_mass]
    · exact fun x _ => π.nonneg x)

@[simp]
theorem toPMF_apply (π : Distribution State) (x : State) :
    π.toPMF x = ENNReal.ofReal (π.mass x) :=
  rfl

@[simp]
theorem toPMF_apply_toReal (π : Distribution State) (x : State) :
    (π.toPMF x).toReal = π.mass x := by
  simp [π.nonneg x]

/-- A finite distribution as a probability measure. -/
noncomputable def toMeasure [MeasurableSpace State] (π : Distribution State) : Measure State :=
  π.toPMF.toMeasure

instance [MeasurableSpace State] (π : Distribution State) :
    IsProbabilityMeasure π.toMeasure :=
  PMF.toMeasure.isProbabilityMeasure π.toPMF

@[simp]
theorem toMeasure_apply_singleton [MeasurableSpace State] [MeasurableSingletonClass State]
    (π : Distribution State) (x : State) :
    π.toMeasure {x} = ENNReal.ofReal (π.mass x) := by
  rw [toMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton x)]
  rfl

end Distribution

/-- A row of a finite Markov kernel as a mathlib probability mass function. -/
noncomputable def rowPMF (P : MarkovKernel State) (x : State) : PMF State :=
  PMF.ofFintype (fun y => ENNReal.ofReal (P.prob x y)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · simp [P.sum_prob]
    · exact fun y _ => P.nonneg x y)

@[simp]
theorem rowPMF_apply (P : MarkovKernel State) (x y : State) :
    P.rowPMF x y = ENNReal.ofReal (P.prob x y) :=
  rfl

@[simp]
theorem rowPMF_apply_toReal (P : MarkovKernel State) (x y : State) :
    (P.rowPMF x y).toReal = P.prob x y := by
  simp [P.nonneg x y]

/-- An elementary finite Markov kernel as a mathlib measure-theoretic kernel. -/
noncomputable def toMeasureKernel [MeasurableSpace State] [MeasurableSingletonClass State]
    (P : MarkovKernel State) : ProbabilityTheory.Kernel State State :=
  ProbabilityTheory.Kernel.ofFunOfCountable fun x => (P.rowPMF x).toMeasure

instance [MeasurableSpace State] [MeasurableSingletonClass State] (P : MarkovKernel State) :
    IsMarkovKernel P.toMeasureKernel where
  isProbabilityMeasure x := PMF.toMeasure.isProbabilityMeasure (P.rowPMF x)

@[simp]
theorem toMeasureKernel_apply_singleton [MeasurableSpace State]
    [MeasurableSingletonClass State] (P : MarkovKernel State) (x y : State) :
    P.toMeasureKernel x {y} = ENNReal.ofReal (P.prob x y) := by
  change (P.rowPMF x).toMeasure {y} = ENNReal.ofReal (P.prob x y)
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton y)]
  rfl

@[simp]
theorem toMeasureKernel_apply [MeasurableSpace State] [MeasurableSingletonClass State]
    (P : MarkovKernel State) (x : State) (s : Set State) :
    P.toMeasureKernel x s =
      ∑ y, s.indicator (fun y => ENNReal.ofReal (P.prob x y)) y := by
  change (P.rowPMF x).toMeasure s = _
  rw [PMF.toMeasure_apply_fintype]
  rfl

private theorem flow_lintegral [MeasurableSpace State] [MeasurableSingletonClass State]
    (P : MarkovKernel State) (π : Distribution State) (A B : Set State) :
    ∫⁻ x in A, P.toMeasureKernel x B ∂π.toMeasure =
      ∑ x, A.indicator
        (fun x => ∑ y, B.indicator
          (fun y => ENNReal.ofReal (π.mass x * P.prob x y)) y) x := by
  rw [lintegral_fintype]
  apply Finset.sum_congr rfl
  intro x _
  rw [Measure.restrict_apply (measurableSet_singleton x)]
  by_cases hx : x ∈ A
  · have hsingleton : ({x} : Set State) ∩ A = {x} := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · exact And.left
      · intro hzx
        exact ⟨hzx, hzx ▸ hx⟩
    rw [hsingleton, Distribution.toMeasure_apply_singleton, toMeasureKernel_apply]
    simp only [Set.indicator_of_mem hx]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : y ∈ B
    · simp only [Set.indicator_of_mem hy]
      rw [← ENNReal.ofReal_mul (P.nonneg x y), mul_comm]
    · simp [Set.indicator_of_notMem hy]
  · have hempty : ({x} : Set State) ∩ A = ∅ := by
      ext z
      constructor
      · intro hz
        exact (hx (hz.1 ▸ hz.2)).elim
      · intro hz
        exact hz.elim
    simp [hempty, Set.indicator_of_notMem hx]

/-- Elementary pointwise detailed balance implies mathlib's setwise
reversibility for the embedded kernel and measure. -/
theorem Reversible.isReversible [MeasurableSpace State] [MeasurableSingletonClass State]
    {P : MarkovKernel State} {π : Distribution State} (hrev : P.Reversible π) :
    ProbabilityTheory.Kernel.IsReversible P.toMeasureKernel π.toMeasure := by
  classical
  intro A B _ _
  rw [flow_lintegral, flow_lintegral]
  calc
    (∑ x, A.indicator
        (fun x => ∑ y, B.indicator
          (fun y => ENNReal.ofReal (π.mass x * P.prob x y)) y) x) =
        ∑ x, ∑ y, A.indicator
          (fun _ => B.indicator
            (fun _ => ENNReal.ofReal (π.mass x * P.prob x y)) y) x := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ A
      · simp only [Set.indicator_of_mem hx]
        apply Finset.sum_congr rfl
        intro y _
        rfl
      · simp only [Set.indicator_of_notMem hx, Finset.sum_const_zero]
    _ = ∑ x, ∑ y, A.indicator
          (fun _ => B.indicator
            (fun _ => ENNReal.ofReal (π.mass y * P.prob y x)) y) x := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [hrev x y]
    _ = ∑ y, ∑ x, A.indicator
          (fun _ => B.indicator
            (fun _ => ENNReal.ofReal (π.mass y * P.prob y x)) y) x :=
      Finset.sum_comm
    _ = ∑ y, B.indicator
          (fun y => ∑ x, A.indicator
            (fun x => ENNReal.ofReal (π.mass y * P.prob y x)) x) y := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y ∈ B
      · simp only [Set.indicator_of_mem hy]
        apply Finset.sum_congr rfl
        intro x _
        rfl
      · simp only [Set.indicator_of_notMem hy, Set.indicator_zero, Finset.sum_const_zero]

/-- Elementary detailed balance gives mathlib kernel invariance through the
generic theorem that reversibility implies invariance. -/
theorem Reversible.invariantMeasure [MeasurableSpace State] [MeasurableSingletonClass State]
    {P : MarkovKernel State} {π : Distribution State} (hrev : P.Reversible π) :
    ProbabilityTheory.Kernel.Invariant P.toMeasureKernel π.toMeasure :=
  hrev.isReversible.invariant

end MarkovKernel
end McmcLean.Finite
