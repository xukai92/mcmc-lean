import Mcmc.Kernel.AuxiliaryGibbs
import Mcmc.Kernel.MetropolisHastings
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Kernel.CompProdEqIff

/-!
# General-state slice-height kernels

This module begins the concrete slice-sampling client of `AuxiliaryGibbs`.
For a strictly positive measurable real weight `w`, it constructs the Markov
kernel that draws a height uniformly from `(0, w x]`.  The horizontal
level-set conditional remains a separate kernel and must satisfy the explicit
joint-factorization equation from `sliceSampler_invariant`.
-/

open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

namespace Mcmc.Kernel

open ProbabilityTheory

variable {State : Type*} [MeasurableSpace State]

/-- Density with respect to real Lebesgue measure of a uniform height in
`(0, weight x]`. -/
noncomputable def sliceHeightDensity (weight : State → ℝ)
    (x : State) (u : ℝ) : ENNReal :=
  if u ∈ Ioc 0 (weight x) then (ENNReal.ofReal (weight x))⁻¹ else 0

theorem measurable_uncurry_sliceHeightDensity
    {weight : State → ℝ} (hweight : Measurable weight) :
    Measurable (Function.uncurry (sliceHeightDensity weight)) := by
  have hset : MeasurableSet {p : State × ℝ | p.2 ∈ Ioc 0 (weight p.1)} := by
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (hweight.comp measurable_fst))
  rw [show Function.uncurry (sliceHeightDensity weight) = fun p =>
      if p ∈ {p : State × ℝ | p.2 ∈ Ioc 0 (weight p.1)}
      then (ENNReal.ofReal (weight p.1))⁻¹ else 0 by rfl]
  exact Measurable.ite hset
    ((ENNReal.measurable_ofReal.comp (hweight.comp measurable_fst)).inv)
    measurable_const

omit [MeasurableSpace State] in
theorem sliceHeightDensity_lintegral
    (weight : State → ℝ) (hpositive : ∀ x, 0 < weight x) (x : State) :
    ∫⁻ u, sliceHeightDensity weight x u ∂volume = 1 := by
  rw [show sliceHeightDensity weight x =
      (Ioc 0 (weight x)).indicator
        (fun _ => (ENNReal.ofReal (weight x))⁻¹) by
    funext u
    by_cases hu : u ∈ Ioc 0 (weight x) <;>
      simp [sliceHeightDensity, hu]]
  rw [lintegral_indicator measurableSet_Ioc]
  rw [MeasureTheory.lintegral_const, Measure.restrict_apply_univ,
    Real.volume_Ioc, sub_zero]
  exact ENNReal.inv_mul_cancel
    (ENNReal.ofReal_ne_zero_iff.mpr (hpositive x)) ENNReal.ofReal_ne_top

/-- The vertical update of slice sampling: conditionally uniform height below
the current unnormalized target weight. -/
noncomputable def sliceHeightKernel
    (weight : State → ℝ) (_hweight : Measurable weight)
    (_hpositive : ∀ x, 0 < weight x) : Kernel State ℝ :=
  (Kernel.const State (volume : Measure ℝ)).withDensity
    (sliceHeightDensity weight)

instance sliceHeightKernel.instIsMarkovKernel
    (weight : State → ℝ) (hweight : Measurable weight)
    (hpositive : ∀ x, 0 < weight x) :
    IsMarkovKernel (sliceHeightKernel weight hweight hpositive) := by
  constructor
  intro x
  constructor
  rw [sliceHeightKernel, ProbabilityTheory.Kernel.withDensity_apply'
    _ (measurable_uncurry_sliceHeightDensity hweight),
    ProbabilityTheory.Kernel.const_apply,
    Measure.restrict_univ, sliceHeightDensity_lintegral weight hpositive]

/-- Indicator density of the region under the graph of `weight`, in
state--height coordinate order. -/
noncomputable def sliceUnderGraphDensity (weight : State → ℝ)
    (p : State × ℝ) : ENNReal :=
  if p.2 ∈ Ioc 0 (weight p.1) then 1 else 0

theorem measurable_sliceUnderGraphDensity
    {weight : State → ℝ} (hweight : Measurable weight) :
    Measurable (sliceUnderGraphDensity weight) := by
  apply Measurable.ite
  · exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (hweight.comp measurable_fst))
  · exact measurable_const
  · exact measurable_const

/-- Lebesgue-under-the-graph measure associated with an unnormalized positive
weight and a base measure on states. -/
noncomputable def sliceUnderGraph
    (base : Measure State) (weight : State → ℝ) : Measure (State × ℝ) :=
  (base.prod volume).withDensity (sliceUnderGraphDensity weight)

/-- Multiplying the weighted target by its normalized vertical conditional
cancels the target weight and produces the under-the-graph joint measure. -/
theorem compProd_sliceHeightKernel_eq_sliceUnderGraph
    (base : Measure State) [SFinite base]
    (weight : State → ℝ) (hweight : Measurable weight)
    (hpositive : ∀ x, 0 < weight x) :
    (base.withDensity (fun x => ENNReal.ofReal (weight x))) ⊗ₘ
        sliceHeightKernel weight hweight hpositive =
      sliceUnderGraph base weight := by
  letI : IsMarkovKernel
      ((Kernel.const State (volume : Measure ℝ)).withDensity
        (sliceHeightDensity weight)) := by
    change IsMarkovKernel (sliceHeightKernel weight hweight hpositive)
    infer_instance
  have hwenn : Measurable (fun x : State => ENNReal.ofReal (weight x)) :=
    ENNReal.measurable_ofReal.comp hweight
  rw [sliceHeightKernel, Measure.compProd_withDensity
    (measurable_uncurry_sliceHeightDensity hweight),
    Measure.compProd_const,
    prod_withDensity_left hwenn,
    ← withDensity_mul]
  · unfold sliceUnderGraph
    congr 1
    funext p
    by_cases hp : p.2 ∈ Ioc 0 (weight p.1)
    · have hcond : 0 < p.2 ∧ p.2 ≤ weight p.1 := by
        simpa [Set.mem_Ioc] using hp
      simp only [Pi.mul_apply, sliceHeightDensity,
        sliceUnderGraphDensity, hp, if_true]
      exact ENNReal.mul_inv_cancel
        (ENNReal.ofReal_ne_zero_iff.mpr (hpositive p.1)) ENNReal.ofReal_ne_top
    · have hcond : ¬ (0 < p.2 ∧ p.2 ≤ weight p.1) := by
        simpa [Set.mem_Ioc] using hp
      simp [sliceHeightDensity, sliceUnderGraphDensity, hp, hcond]
  · exact hwenn.comp measurable_fst
  · exact measurable_uncurry_sliceHeightDensity hweight

/-- In auxiliary-first coordinate order, the lifted weighted target is the
swapped under-the-graph measure. -/
theorem auxiliaryFirstJoint_sliceHeightKernel
    (base : Measure State) [SFinite base]
    (weight : State → ℝ) (hweight : Measurable weight)
    (hpositive : ∀ x, 0 < weight x) :
    auxiliaryFirstJoint
        (base.withDensity (fun x => ENNReal.ofReal (weight x)))
        (sliceHeightKernel weight hweight hpositive) =
      (sliceUnderGraph base weight).map Prod.swap := by
  rw [auxiliaryFirstJoint,
    compProd_sliceHeightKernel_eq_sliceUnderGraph base weight hweight hpositive]

/-- Slice sampling obtained by pairing the concrete vertical height kernel
with a supplied horizontal level-set conditional. -/
noncomputable def exactSliceSampler
    (weight : State → ℝ) (hweight : Measurable weight)
    (hpositive : ∀ x, 0 < weight x)
    (horizontal : Kernel ℝ State) : Kernel State State :=
  sliceSampler (sliceHeightKernel weight hweight hpositive) horizontal

/-- Correctness of the concrete vertical/exact-horizontal slice sampler.  The
remaining hypothesis is precisely that `horizontal` is the reverse
conditional of the vertical under-graph joint law. -/
theorem exactSliceSampler_invariant
    (target : Measure State) [SFinite target]
    (weight : State → ℝ) (hweight : Measurable weight)
    (hpositive : ∀ x, 0 < weight x)
    (horizontal : Kernel ℝ State) [IsMarkovKernel horizontal]
    (hslice : auxiliaryFirstJoint target
        (sliceHeightKernel weight hweight hpositive) =
      (sliceHeightKernel weight hweight hpositive ∘ₘ target) ⊗ₘ horizontal) :
    (exactSliceSampler weight hweight hpositive horizontal).Invariant target := by
  exact sliceSampler_invariant target
    (sliceHeightKernel weight hweight hpositive) horizontal hslice

/-- Concrete under-the-graph formulation of slice invariance.  It remains to
construct a horizontal Markov kernel giving the displayed factorization; no
ergodicity or rate conclusion follows from this equation alone. -/
theorem exactSliceSampler_invariant_underGraph
    (base : Measure State) [SFinite base]
    (weight : State → ℝ) (hweight : Measurable weight)
    (hpositive : ∀ x, 0 < weight x)
    (horizontal : Kernel ℝ State) [IsMarkovKernel horizontal]
    (hhorizontal : (sliceUnderGraph base weight).map Prod.swap =
      (sliceHeightKernel weight hweight hpositive ∘ₘ
          base.withDensity (fun x => ENNReal.ofReal (weight x))) ⊗ₘ horizontal) :
    (exactSliceSampler weight hweight hpositive horizontal).Invariant
      (base.withDensity (fun x => ENNReal.ofReal (weight x))) := by
  apply exactSliceSampler_invariant
    (base.withDensity (fun x => ENNReal.ofReal (weight x)))
      weight hweight hpositive horizontal
  rw [auxiliaryFirstJoint_sliceHeightKernel base weight hweight hpositive]
  exact hhorizontal

end Mcmc.Kernel
