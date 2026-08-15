import Mcmc.Kernel.GeneralConvergence
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Refresh-augmented invariant kernels

Adding a positive independent draw from the target gives an invariant kernel
an explicit Doeblin component. This is useful for honest concrete convergence
clients: the conclusion applies to the augmented algorithm, not automatically
to its unrefreshed branch.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace Mcmc.Kernel

open ProbabilityTheory

variable {α : Type*} [MeasurableSpace α]

/-- Probability normalization of a finite measure, exposed at `Measure` type. -/
noncomputable def finiteNormalize [Nonempty α] (target : Measure α)
    [IsFiniteMeasure target] : Measure α :=
  ((MeasureTheory.FiniteMeasure.normalize
      (⟨target, inferInstance⟩ : MeasureTheory.FiniteMeasure α) :
    ProbabilityMeasure α) : Measure α)

instance finiteNormalize.instIsProbabilityMeasure [Nonempty α]
    (target : Measure α) [IsFiniteMeasure target] :
    IsProbabilityMeasure (finiteNormalize target) := by
  unfold finiteNormalize
  infer_instance

/-- Invariance survives normalization of a nonzero finite target. -/
theorem invariant_finiteNormalize
    [Nonempty α] (transition : Kernel α α) (target : Measure α)
    [IsFiniteMeasure target] (htarget : target ≠ 0)
    (hinvariant : transition.Invariant target) :
    transition.Invariant (finiteNormalize target) := by
  let finiteTarget : MeasureTheory.FiniteMeasure α := ⟨target, inferInstance⟩
  have hfiniteTarget : finiteTarget ≠ 0 := by
    intro hzero
    apply htarget
    have hcoerced := congrArg
      (fun μ : MeasureTheory.FiniteMeasure α => (μ : Measure α)) hzero
    simpa [finiteTarget] using hcoerced
  change transition.Invariant
    ((MeasureTheory.FiniteMeasure.normalize finiteTarget : ProbabilityMeasure α) : Measure α)
  rw [MeasureTheory.FiniteMeasure.toMeasure_normalize_eq_of_nonzero finiteTarget hfiniteTarget]
  change transition.Invariant (finiteTarget.mass⁻¹ • target)
  rw [← Measure.coe_nnreal_smul]
  rw [ProbabilityTheory.Kernel.Invariant, Measure.comp_smul, hinvariant]

/-- Mix an existing transition with an independent target refresh. `p` is the
weight of the existing transition. -/
noncomputable def refreshAugmented (p : Set.Icc (0 : NNReal) 1)
    (transition : Kernel α α) (target : Measure α) : Kernel α α :=
  mixture p transition (Kernel.const α target)

instance refreshAugmented.instIsMarkovKernel
    (p : Set.Icc (0 : NNReal) 1) (transition : Kernel α α)
    [IsMarkovKernel transition] (target : Measure α)
    [IsProbabilityMeasure target] :
    IsMarkovKernel (refreshAugmented p transition target) := by
  unfold refreshAugmented
  infer_instance

theorem refreshAugmented_invariant
    (p : Set.Icc (0 : NNReal) 1) (transition : Kernel α α)
    (target : Measure α) [IsProbabilityMeasure target]
    (hinvariant : transition.Invariant target) :
    (refreshAugmented p transition target).Invariant target := by
  exact mixture_invariant p transition (Kernel.const α target) target
    hinvariant (by simp [ProbabilityTheory.Kernel.Invariant])

/-- The independent branch is a uniform minorization with coefficient `1-p`. -/
theorem refreshAugmented_uniformlyMinorizes
    (p : Set.Icc (0 : NNReal) 1) (transition : Kernel α α)
    (target : Measure α) [IsProbabilityMeasure target] :
    UniformlyMinorizes (refreshAugmented p transition target)
      (1 - p.1 : NNReal) target := by
  intro x s hs
  simp only [refreshAugmented]
  exact mixture_apply_second_le p transition (Kernel.const α target) x hs

/-- Explicit upper eventwise convergence bound. The residual rate is exactly
`p`, the probability of avoiding refresh at each iteration. -/
theorem refreshAugmented_lawAtTime_apply_le
    (p : Set.Icc (0 : NNReal) 1) (hp0 : 0 < p.1)
    (transition : Kernel α α) [IsMarkovKernel transition]
    (target initial : Measure α) [IsProbabilityMeasure target]
    [IsProbabilityMeasure initial] (hinvariant : transition.Invariant target)
    (n : ℕ) {s : Set α} (hs : MeasurableSet s) :
    lawAtTime initial (refreshAugmented p transition target) n s ≤
      target s + ((p.1 ^ n : NNReal) : ENNReal) := by
  let ε : Set.Icc (0 : NNReal) 1 :=
    ⟨1 - p.1, by simp, by simp⟩
  have hε : ε.1 < 1 := by
    change 1 - p.1 < 1
    exact tsub_lt_self (by simp) hp0
  have hminor := refreshAugmented_uniformlyMinorizes p transition target
  have hinv := refreshAugmented_invariant p transition target hinvariant
  simpa [ε, tsub_tsub_cancel_of_le p.property.2] using
    lawAtTime_apply_le_target_add_geometric
      (refreshAugmented p transition target) target initial ε hε hminor hinv n hs

/-- Symmetric eventwise convergence bound. -/
theorem refreshAugmented_target_apply_le_lawAtTime
    (p : Set.Icc (0 : NNReal) 1) (hp0 : 0 < p.1)
    (transition : Kernel α α) [IsMarkovKernel transition]
    (target initial : Measure α) [IsProbabilityMeasure target]
    [IsProbabilityMeasure initial] (hinvariant : transition.Invariant target)
    (n : ℕ) {s : Set α} (hs : MeasurableSet s) :
    target s ≤ lawAtTime initial (refreshAugmented p transition target) n s +
      ((p.1 ^ n : NNReal) : ENNReal) := by
  let ε : Set.Icc (0 : NNReal) 1 :=
    ⟨1 - p.1, by simp, by simp⟩
  have hε : ε.1 < 1 := by
    change 1 - p.1 < 1
    exact tsub_lt_self (by simp) hp0
  have hminor := refreshAugmented_uniformlyMinorizes p transition target
  have hinv := refreshAugmented_invariant p transition target hinvariant
  simpa [ε, tsub_tsub_cancel_of_le p.property.2] using
    target_apply_le_lawAtTime_add_geometric
      (refreshAugmented p transition target) target initial ε hε hminor hinv n hs

/-- A genuinely positive refresh probability (`p < 1`) makes the displayed
geometric remainder tend to zero. -/
theorem refreshAugmented_rate_tendsto_zero
    (p : Set.Icc (0 : NNReal) 1) (hp : p.1 < 1) :
    Filter.Tendsto (fun n : ℕ => (((p.1 : NNReal) : ENNReal) ^ n))
      Filter.atTop (nhds 0) := by
  exact ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by exact_mod_cast hp)

end Mcmc.Kernel
