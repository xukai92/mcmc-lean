import Mcmc.Kernel.AuxiliaryGibbs
import Mcmc.Kernel.MetropolisHastings
import Mcmc.Kernel.ParameterMixture
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# General-state slice-height kernels

This module supplies the concrete slice-sampling client of `AuxiliaryGibbs`.
For a strictly positive measurable real weight `w`, it constructs the Markov
kernel that draws a height uniformly from `(0, w x]`, obtains the horizontal
conditional by standard-Borel disintegration, and proves that the resulting
general-state kernel preserves the weighted target. It does not infer
irreducibility, convergence, or a rate from invariance.
-/

open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

namespace Mcmc.Kernel

open ProbabilityTheory

variable {State : Type*} [MeasurableSpace State]

/-- Swapping a product measure carrying a measurable density swaps the density
arguments as well. This change-of-coordinate lemma is used below to rewrite
the state--height under-graph law in height--state order. -/
theorem map_swap_prod_withDensity
    {Left Right : Type*} [MeasurableSpace Left] [MeasurableSpace Right]
    (left : Measure Left) (right : Measure Right) [SFinite left] [SFinite right]
    (density : Left × Right → ENNReal) (hdensity : Measurable density) :
    ((left.prod right).withDensity density).map Prod.swap =
      (right.prod left).withDensity (density ∘ Prod.swap) := by
  ext event hevent
  rw [Measure.map_apply measurable_swap hevent,
    withDensity_apply _ (measurable_swap hevent),
    withDensity_apply _ hevent,
    ← lintegral_indicator (measurable_swap hevent),
    ← lintegral_indicator hevent, ← Measure.prod_swap]
  rw [MeasureTheory.lintegral_map]
  · apply lintegral_congr
    intro point
    simp only [Set.indicator, Set.mem_preimage, Function.comp_apply,
      Prod.swap_swap]
    by_cases hp : point ∈ event
    · rw [if_pos hp, if_pos]
      simpa using hp
    · rw [if_neg hp, if_neg]
      simpa using hp
  · exact hdensity.indicator (measurable_swap hevent)
  · exact measurable_swap

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

/-! ### Uniform kernels on measurable variable intervals -/

/-- Density of the uniform probability law on `(lower parameter,
upper parameter]`. -/
noncomputable def variableIntervalDensity {Parameter : Type*}
    (lower upper : Parameter → ℝ) (parameter : Parameter) (x : ℝ) : ENNReal :=
  if x ∈ Ioc (lower parameter) (upper parameter) then
    (ENNReal.ofReal (upper parameter - lower parameter))⁻¹
  else 0

/-- Unnormalized height marginal associated with interval endpoints. -/
noncomputable def intervalHeightDensity
    (lower upper : ℝ → ℝ) (parameter : ℝ) : ENNReal :=
  ENNReal.ofReal (upper parameter - lower parameter)

theorem measurable_intervalHeightDensity
    {lower upper : ℝ → ℝ}
    (hlower : Measurable lower) (hupper : Measurable upper) :
    Measurable (intervalHeightDensity lower upper) := by
  exact ENNReal.measurable_ofReal.comp (hupper.sub hlower)

/-- Lebesgue height measure weighted by the width of its horizontal interval. -/
noncomputable def intervalHeightMeasure (lower upper : ℝ → ℝ) :
    Measure ℝ :=
  (volume : Measure ℝ).withDensity (intervalHeightDensity lower upper)

theorem measurable_uncurry_variableIntervalDensity
    {Parameter : Type*} [MeasurableSpace Parameter]
    {lower upper : Parameter → ℝ}
    (hlower : Measurable lower) (hupper : Measurable upper) :
    Measurable (Function.uncurry (variableIntervalDensity lower upper)) := by
  have hset : MeasurableSet {p : Parameter × ℝ |
      p.2 ∈ Ioc (lower p.1) (upper p.1)} := by
    exact (measurableSet_lt (hlower.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (hupper.comp measurable_fst))
  rw [show Function.uncurry (variableIntervalDensity lower upper) = fun p ↦
      if p ∈ {p : Parameter × ℝ |
          p.2 ∈ Ioc (lower p.1) (upper p.1)}
      then (ENNReal.ofReal (upper p.1 - lower p.1))⁻¹ else 0 by rfl]
  exact Measurable.ite hset
    ((ENNReal.measurable_ofReal.comp
      ((hupper.comp measurable_fst).sub
        (hlower.comp measurable_fst))).inv)
    measurable_const

omit [MeasurableSpace State] in
theorem variableIntervalDensity_lintegral
    {Parameter : Type*} (lower upper : Parameter → ℝ)
    (parameter : Parameter) (hordered : lower parameter < upper parameter) :
    ∫⁻ x, variableIntervalDensity lower upper parameter x ∂volume = 1 := by
  rw [show variableIntervalDensity lower upper parameter =
      (Ioc (lower parameter) (upper parameter)).indicator
        (fun _ ↦ (ENNReal.ofReal
          (upper parameter - lower parameter))⁻¹) by
    funext x
    by_cases hx : x ∈ Ioc (lower parameter) (upper parameter) <;>
      simp [variableIntervalDensity, hx]]
  rw [lintegral_indicator measurableSet_Ioc, MeasureTheory.lintegral_const,
    Measure.restrict_apply_univ, Real.volume_Ioc]
  exact ENNReal.inv_mul_cancel
    (ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hordered))
    ENNReal.ofReal_ne_top

/-- Markov kernel that samples uniformly from a measurable interval depending
on its input parameter. This is the exact horizontal proposal primitive needed
by stepping-out bracket constructions. -/
noncomputable def variableIntervalKernel {Parameter : Type*}
    [MeasurableSpace Parameter]
    (lower upper : Parameter → ℝ) (_hlower : Measurable lower)
    (_hupper : Measurable upper)
    (_hordered : ∀ parameter, lower parameter < upper parameter) :
    Kernel Parameter ℝ :=
  (Kernel.const Parameter (volume : Measure ℝ)).withDensity
    (variableIntervalDensity lower upper)

instance variableIntervalKernel.instIsMarkovKernel
    {Parameter : Type*} [MeasurableSpace Parameter]
    (lower upper : Parameter → ℝ) (hlower : Measurable lower)
    (hupper : Measurable upper)
    (hordered : ∀ parameter, lower parameter < upper parameter) :
    IsMarkovKernel
      (variableIntervalKernel lower upper hlower hupper hordered) := by
  constructor
  intro parameter
  constructor
  rw [variableIntervalKernel, ProbabilityTheory.Kernel.withDensity_apply'
    _ (measurable_uncurry_variableIntervalDensity hlower hupper),
    ProbabilityTheory.Kernel.const_apply, Measure.restrict_univ,
    variableIntervalDensity_lintegral lower upper parameter
      (hordered parameter)]

/-- Each row of the variable-interval kernel is exactly normalized Lebesgue
restriction to its declared interval. -/
theorem variableIntervalKernel_apply_eq_smul_restrict
    {Parameter : Type*} [MeasurableSpace Parameter]
    (lower upper : Parameter → ℝ) (hlower : Measurable lower)
    (hupper : Measurable upper)
    (hordered : ∀ parameter, lower parameter < upper parameter)
    (parameter : Parameter) :
    variableIntervalKernel lower upper hlower hupper hordered parameter =
      (ENNReal.ofReal (upper parameter - lower parameter))⁻¹ •
        (volume.restrict (Ioc (lower parameter) (upper parameter))) := by
  rw [variableIntervalKernel,
    ProbabilityTheory.Kernel.withDensity_apply
      _ (measurable_uncurry_variableIntervalDensity hlower hupper),
    ProbabilityTheory.Kernel.const_apply]
  rw [show variableIntervalDensity lower upper parameter =
      (Ioc (lower parameter) (upper parameter)).indicator
        (fun _ ↦ (ENNReal.ofReal
          (upper parameter - lower parameter))⁻¹) by
    funext x
    by_cases hx : x ∈ Ioc (lower parameter) (upper parameter) <;>
      simp [variableIntervalDensity, hx],
    withDensity_indicator measurableSet_Ioc,
    withDensity_const]

/-- Closed event-probability formula for a variable-interval draw. -/
theorem variableIntervalKernel_apply_event
    {Parameter : Type*} [MeasurableSpace Parameter]
    (lower upper : Parameter → ℝ) (hlower : Measurable lower)
    (hupper : Measurable upper)
    (hordered : ∀ parameter, lower parameter < upper parameter)
    (parameter : Parameter) {event : Set ℝ} (hevent : MeasurableSet event) :
    variableIntervalKernel lower upper hlower hupper hordered parameter event =
      (ENNReal.ofReal (upper parameter - lower parameter))⁻¹ *
        volume (event ∩ Ioc (lower parameter) (upper parameter)) := by
  rw [variableIntervalKernel_apply_eq_smul_restrict lower upper hlower hupper
    hordered parameter, Measure.smul_apply, Measure.restrict_apply hevent,
    smul_eq_mul]

/-- Multiplying the interval-width height marginal by its normalized
horizontal interval kernel cancels the width and leaves the indicator of the
height--state interval region. -/
theorem compProd_intervalHeightMeasure_variableIntervalKernel
    (lower upper : ℝ → ℝ) (hlower : Measurable lower)
    (hupper : Measurable upper)
    (hordered : ∀ parameter, lower parameter < upper parameter) :
    intervalHeightMeasure lower upper ⊗ₘ
        variableIntervalKernel lower upper hlower hupper hordered =
      ((volume : Measure ℝ).prod volume).withDensity (fun p : ℝ × ℝ ↦
        if p.2 ∈ Ioc (lower p.1) (upper p.1) then 1 else 0) := by
  let intervalDensity : ℝ × ℝ → ENNReal := fun p ↦
    if p.2 ∈ Ioc (lower p.1) (upper p.1) then 1 else 0
  have hintervalDensity : Measurable intervalDensity := by
    apply Measurable.ite
    · exact (measurableSet_lt (hlower.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hupper.comp measurable_fst))
    · exact measurable_const
    · exact measurable_const
  letI : IsMarkovKernel
      (variableIntervalKernel lower upper hlower hupper hordered) :=
    variableIntervalKernel.instIsMarkovKernel lower upper hlower hupper hordered
  letI : IsMarkovKernel
      ((Kernel.const ℝ (volume : Measure ℝ)).withDensity
        (variableIntervalDensity lower upper)) := by
    change IsMarkovKernel
      (variableIntervalKernel lower upper hlower hupper hordered)
    infer_instance
  unfold variableIntervalKernel intervalHeightMeasure
  rw [Measure.compProd_withDensity
    (measurable_uncurry_variableIntervalDensity hlower hupper),
    Measure.compProd_const,
    prod_withDensity_left (measurable_intervalHeightDensity hlower hupper),
    ← withDensity_mul]
  · congr 1
    funext p
    change intervalHeightDensity lower upper p.1 *
        variableIntervalDensity lower upper p.1 p.2 = intervalDensity p
    by_cases hp : p.2 ∈ Ioc (lower p.1) (upper p.1)
    · simp only [intervalHeightDensity, variableIntervalDensity, hp,
        if_true, intervalDensity]
      exact ENNReal.mul_inv_cancel
        (ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr (hordered p.1)))
        ENNReal.ofReal_ne_top
    · change intervalHeightDensity lower upper p.1 *
          (if p.2 ∈ Ioc (lower p.1) (upper p.1) then
            (ENNReal.ofReal (upper p.1 - lower p.1))⁻¹ else 0) =
          (if p.2 ∈ Ioc (lower p.1) (upper p.1) then 1 else 0)
      rw [if_neg hp, if_neg hp, mul_zero]
  · exact (measurable_intervalHeightDensity hlower hupper).comp measurable_fst
  · exact measurable_uncurry_variableIntervalDensity hlower hupper

/-- The variable-interval draw lies in its declared bracket with probability
one. -/
theorem variableIntervalKernel_apply_interval
    {Parameter : Type*} [MeasurableSpace Parameter]
    (lower upper : Parameter → ℝ) (hlower : Measurable lower)
    (hupper : Measurable upper)
    (hordered : ∀ parameter, lower parameter < upper parameter)
    (parameter : Parameter) :
    variableIntervalKernel lower upper hlower hupper hordered parameter
        (Ioc (lower parameter) (upper parameter)) = 1 := by
  rw [variableIntervalKernel,
    ProbabilityTheory.Kernel.withDensity_apply'
      _ (measurable_uncurry_variableIntervalDensity hlower hupper),
    ProbabilityTheory.Kernel.const_apply]
  rw [← lintegral_indicator measurableSet_Ioc]
  have hindicator :
      (Ioc (lower parameter) (upper parameter)).indicator
          (variableIntervalDensity lower upper parameter) =
        variableIntervalDensity lower upper parameter := by
    funext x
    by_cases hx : x ∈ Ioc (lower parameter) (upper parameter) <;>
      simp [variableIntervalDensity, hx]
  rw [hindicator]
  exact variableIntervalDensity_lintegral lower upper parameter
    (hordered parameter)

/-- Measurable set of parameters whose declared interval has positive width. -/
def validVariableIntervalSet {Parameter : Type*} [MeasurableSpace Parameter]
    (lower upper : Parameter → ℝ) : Set Parameter :=
  {parameter | lower parameter < upper parameter}

theorem measurableSet_validVariableIntervalSet
    {Parameter : Type*} [MeasurableSpace Parameter]
    {lower upper : Parameter → ℝ}
    (hlower : Measurable lower) (hupper : Measurable upper) :
    MeasurableSet (validVariableIntervalSet lower upper) :=
  measurableSet_lt hlower hupper

/-- Total variable-interval proposal. Positive-width rows are uniform on the
declared interval; zero/negative-width rows use the identity kernel. The
fallback is irrelevant under a width-weighted height law but makes this a
genuine Markov kernel on the entire height space. -/
noncomputable def totalVariableIntervalKernel
    (lower upper : ℝ → ℝ) (hlower : Measurable lower)
    (hupper : Measurable upper) : Kernel ℝ ℝ := by
  classical
  exact Kernel.piecewise (measurableSet_validVariableIntervalSet hlower hupper)
    ((Kernel.const ℝ (volume : Measure ℝ)).withDensity
      (variableIntervalDensity lower upper)) Kernel.id

instance totalVariableIntervalKernel.instIsMarkovKernel
    (lower upper : ℝ → ℝ) (hlower : Measurable lower)
    (hupper : Measurable upper) :
    IsMarkovKernel (totalVariableIntervalKernel lower upper hlower hupper) := by
  classical
  constructor
  intro parameter
  constructor
  rw [totalVariableIntervalKernel, Kernel.piecewise_apply]
  by_cases hvalid : parameter ∈ validVariableIntervalSet lower upper
  · rw [if_pos hvalid,
      ProbabilityTheory.Kernel.withDensity_apply'
        _ (measurable_uncurry_variableIntervalDensity hlower hupper),
      ProbabilityTheory.Kernel.const_apply, Measure.restrict_univ]
    exact variableIntervalDensity_lintegral lower upper parameter hvalid
  · rw [if_neg hvalid, ProbabilityTheory.Kernel.id_apply]
    simp

/-- On a positive-width parameter, the total proposal agrees exactly with the
normalized variable-interval kernel. -/
theorem totalVariableIntervalKernel_apply_of_lt
    (lower upper : ℝ → ℝ) (hlower : Measurable lower)
    (hupper : Measurable upper) (parameter : ℝ)
    (hvalid : lower parameter < upper parameter) :
    totalVariableIntervalKernel lower upper hlower hupper parameter =
      (ENNReal.ofReal (upper parameter - lower parameter))⁻¹ •
        (volume.restrict (Ioc (lower parameter) (upper parameter))) := by
  classical
  have hmem : parameter ∈ validVariableIntervalSet lower upper := hvalid
  rw [totalVariableIntervalKernel, Kernel.piecewise_apply,
    if_pos hmem]
  rw [ProbabilityTheory.Kernel.withDensity_apply
    _ (measurable_uncurry_variableIntervalDensity hlower hupper),
    ProbabilityTheory.Kernel.const_apply]
  rw [show variableIntervalDensity lower upper parameter =
      (Ioc (lower parameter) (upper parameter)).indicator
        (fun _ ↦ (ENNReal.ofReal
          (upper parameter - lower parameter))⁻¹) by
    funext x
    by_cases hx : x ∈ Ioc (lower parameter) (upper parameter) <;>
      simp [variableIntervalDensity, hx],
    withDensity_indicator measurableSet_Ioc, withDensity_const]

/-- Zero-width fallback parameters are null under the interval-width height
measure, provided endpoint order never reverses. -/
theorem intervalHeightMeasure_invalid_zero
    (lower upper : ℝ → ℝ) (hlower : Measurable lower)
    (hupper : Measurable upper) (hle : ∀ parameter, lower parameter ≤ upper parameter) :
    intervalHeightMeasure lower upper
        (validVariableIntervalSet lower upper)ᶜ = 0 := by
  rw [intervalHeightMeasure,
    withDensity_apply _
      (measurableSet_validVariableIntervalSet hlower hupper).compl]
  rw [← lintegral_indicator
    (measurableSet_validVariableIntervalSet hlower hupper).compl]
  have hzero :
      (validVariableIntervalSet lower upper)ᶜ.indicator
          (intervalHeightDensity lower upper) = 0 := by
    funext parameter
    by_cases hvalid : parameter ∈ validVariableIntervalSet lower upper
    · simp [Set.indicator, hvalid]
    · have heq : upper parameter - lower parameter = 0 := by
        have hnotlt : ¬ lower parameter < upper parameter := hvalid
        linarith [hle parameter]
      simp [Set.indicator, hvalid, intervalHeightDensity, heq]
  rw [hzero]
  simp

/-- Under the width-weighted height law, the total fallback kernel agrees
almost everywhere with the raw interval-density kernel. -/
theorem totalVariableIntervalKernel_ae_eq_withDensity
    (lower upper : ℝ → ℝ) (hlower : Measurable lower)
    (hupper : Measurable upper) (hle : ∀ parameter, lower parameter ≤ upper parameter) :
    totalVariableIntervalKernel lower upper hlower hupper =ᵐ[
      intervalHeightMeasure lower upper]
      (Kernel.const ℝ (volume : Measure ℝ)).withDensity
        (variableIntervalDensity lower upper) := by
  classical
  show ∀ᵐ parameter ∂intervalHeightMeasure lower upper,
    totalVariableIntervalKernel lower upper hlower hupper parameter =
      ((Kernel.const ℝ (volume : Measure ℝ)).withDensity
        (variableIntervalDensity lower upper)) parameter
  rw [ae_iff]
  apply measure_mono_null
    (t := (validVariableIntervalSet lower upper)ᶜ)
  · intro parameter hne
    by_contra hnotInvalid
    have hvalid : parameter ∈ validVariableIntervalSet lower upper := by
      simpa using hnotInvalid
    apply hne
    rw [totalVariableIntervalKernel, Kernel.piecewise_apply, if_pos hvalid]
  · exact intervalHeightMeasure_invalid_zero lower upper hlower hupper hle

/-- With nonnegative widths, the raw interval-density kernel is s-finite even
though its zero-width rows need not be probability measures. -/
theorem variableIntervalDensity_ne_top
    (lower upper : ℝ → ℝ) :
    ∀ parameter state, variableIntervalDensity lower upper parameter state ≠ ∞ := by
  intro parameter state
  by_cases hmem : state ∈ Ioc (lower parameter) (upper parameter)
  · simp only [variableIntervalDensity, hmem, if_true]
    rw [ENNReal.inv_ne_top]
    exact ENNReal.ofReal_ne_zero_iff.mpr
      (sub_pos.mpr (lt_of_lt_of_le hmem.1 hmem.2))
  · simp [variableIntervalDensity, hmem]

/-- Width cancellation remains valid for merely nonnegative interval widths
when the raw density kernel is used. Empty rows contribute zero mass. -/
theorem compProd_intervalHeightMeasure_withDensity
    (lower upper : ℝ → ℝ) (hlower : Measurable lower)
    (hupper : Measurable upper) :
    intervalHeightMeasure lower upper ⊗ₘ
        ((Kernel.const ℝ (volume : Measure ℝ)).withDensity
          (variableIntervalDensity lower upper)) =
      ((volume : Measure ℝ).prod volume).withDensity (fun p : ℝ × ℝ ↦
        if p.2 ∈ Ioc (lower p.1) (upper p.1) then 1 else 0) := by
  let raw := (Kernel.const ℝ (volume : Measure ℝ)).withDensity
    (variableIntervalDensity lower upper)
  letI : IsSFiniteKernel raw :=
    Kernel.IsSFiniteKernel.withDensity (Kernel.const ℝ (volume : Measure ℝ))
      (variableIntervalDensity_ne_top lower upper)
  let intervalDensity : ℝ × ℝ → ENNReal := fun p ↦
    if p.2 ∈ Ioc (lower p.1) (upper p.1) then 1 else 0
  unfold intervalHeightMeasure
  change (volume.withDensity (intervalHeightDensity lower upper)) ⊗ₘ raw = _
  rw [Measure.compProd_withDensity
    (measurable_uncurry_variableIntervalDensity hlower hupper),
    Measure.compProd_const,
    prod_withDensity_left (measurable_intervalHeightDensity hlower hupper),
    ← withDensity_mul]
  · congr 1
    funext p
    change intervalHeightDensity lower upper p.1 *
        variableIntervalDensity lower upper p.1 p.2 = intervalDensity p
    by_cases hp : p.2 ∈ Ioc (lower p.1) (upper p.1)
    · have hlt : lower p.1 < upper p.1 := lt_of_lt_of_le hp.1 hp.2
      simp only [intervalHeightDensity, variableIntervalDensity, hp,
        if_true, intervalDensity]
      exact ENNReal.mul_inv_cancel
        (ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hlt))
        ENNReal.ofReal_ne_top
    · change intervalHeightDensity lower upper p.1 *
          (if p.2 ∈ Ioc (lower p.1) (upper p.1) then
            (ENNReal.ofReal (upper p.1 - lower p.1))⁻¹ else 0) =
          (if p.2 ∈ Ioc (lower p.1) (upper p.1) then 1 else 0)
      rw [if_neg hp, if_neg hp, mul_zero]
  · exact (measurable_intervalHeightDensity hlower hupper).comp measurable_fst
  · exact measurable_uncurry_variableIntervalDensity hlower hupper

/-- The total fallback kernel has the same width-cancellation factorization:
fallback rows occur only on a null set of the height marginal. -/
theorem compProd_intervalHeightMeasure_totalVariableIntervalKernel
    (lower upper : ℝ → ℝ) (hlower : Measurable lower)
    (hupper : Measurable upper)
    (hle : ∀ parameter, lower parameter ≤ upper parameter) :
    intervalHeightMeasure lower upper ⊗ₘ
        totalVariableIntervalKernel lower upper hlower hupper =
      ((volume : Measure ℝ).prod volume).withDensity (fun p : ℝ × ℝ ↦
        if p.2 ∈ Ioc (lower p.1) (upper p.1) then 1 else 0) := by
  let raw := (Kernel.const ℝ (volume : Measure ℝ)).withDensity
    (variableIntervalDensity lower upper)
  letI : IsSFiniteKernel raw :=
    Kernel.IsSFiniteKernel.withDensity (Kernel.const ℝ (volume : Measure ℝ))
      (variableIntervalDensity_ne_top lower upper)
  calc
    _ = intervalHeightMeasure lower upper ⊗ₘ raw :=
      Measure.compProd_congr
        (totalVariableIntervalKernel_ae_eq_withDensity
          lower upper hlower hupper hle)
    _ = _ := compProd_intervalHeightMeasure_withDensity
      lower upper hlower hupper

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

/-- The under-graph measure in height--state order is the swapped density over
the correspondingly swapped product base measure. -/
theorem map_swap_sliceUnderGraph
    (base : Measure State) [SFinite base]
    (weight : State → ℝ) (hweight : Measurable weight) :
    (sliceUnderGraph base weight).map Prod.swap =
      (volume.prod base).withDensity
        (sliceUnderGraphDensity weight ∘ Prod.swap) := by
  unfold sliceUnderGraph
  rw [map_swap_prod_withDensity base volume
    (sliceUnderGraphDensity weight) (measurable_sliceUnderGraphDensity hweight)]

/-- If every positive superlevel set of a real weight is exactly a measurable
interval, the explicit width-weighted height law and uniform horizontal
interval kernel reconstruct the swapped under-graph joint measure. -/
theorem compProd_intervalKernel_eq_map_swap_sliceUnderGraph
    (weight lower upper : ℝ → ℝ)
    (hweight : Measurable weight) (hlower : Measurable lower)
    (hupper : Measurable upper)
    (hordered : ∀ height, lower height < upper height)
    (hlevel : ∀ height state,
      state ∈ Ioc (lower height) (upper height) ↔
        height ∈ Ioc 0 (weight state)) :
    intervalHeightMeasure lower upper ⊗ₘ
        variableIntervalKernel lower upper hlower hupper hordered =
      (sliceUnderGraph volume weight).map Prod.swap := by
  rw [compProd_intervalHeightMeasure_variableIntervalKernel lower upper
    hlower hupper hordered,
    map_swap_sliceUnderGraph volume weight hweight]
  congr 1
  funext p
  simp only [sliceUnderGraphDensity, Function.comp_apply]
  rw [if_congr (hlevel p.1 p.2) rfl rfl]
  rfl

/-- Nonnegative-width interval level sets reconstruct the swapped under-graph
measure using the total interval kernel. Degenerate rows use the identity
fallback, but have zero mass under the height marginal. -/
theorem compProd_totalIntervalKernel_eq_map_swap_sliceUnderGraph
    (weight lower upper : ℝ → ℝ)
    (hweight : Measurable weight) (hlower : Measurable lower)
    (hupper : Measurable upper)
    (hordered : ∀ height, lower height ≤ upper height)
    (hlevel : ∀ height state,
      state ∈ Ioc (lower height) (upper height) ↔
        height ∈ Ioc 0 (weight state)) :
    intervalHeightMeasure lower upper ⊗ₘ
        totalVariableIntervalKernel lower upper hlower hupper =
      (sliceUnderGraph volume weight).map Prod.swap := by
  rw [compProd_intervalHeightMeasure_totalVariableIntervalKernel lower upper
    hlower hupper hordered,
    map_swap_sliceUnderGraph volume weight hweight]
  congr 1
  funext p
  simp only [sliceUnderGraphDensity, Function.comp_apply]
  rw [if_congr (hlevel p.1 p.2) rfl rfl]
  rfl

/-- Almost-everywhere form of the total interval factorization. This is the
natural interface for continuous level sets: changing interval endpoints does
not change their Lebesgue law, even though it changes literal membership. -/
theorem compProd_totalIntervalKernel_eq_map_swap_sliceUnderGraph_ae
    (weight lower upper : ℝ → ℝ)
    (hweight : Measurable weight) (hlower : Measurable lower)
    (hupper : Measurable upper)
    (hordered : ∀ height, lower height ≤ upper height)
    (hlevel : ∀ᵐ p : ℝ × ℝ ∂(volume : Measure ℝ).prod volume,
      (p.2 ∈ Ioc (lower p.1) (upper p.1) ↔
        p.1 ∈ Ioc 0 (weight p.2))) :
    intervalHeightMeasure lower upper ⊗ₘ
        totalVariableIntervalKernel lower upper hlower hupper =
      (sliceUnderGraph volume weight).map Prod.swap := by
  rw [compProd_intervalHeightMeasure_totalVariableIntervalKernel lower upper
    hlower hupper hordered,
    map_swap_sliceUnderGraph volume weight hweight]
  apply withDensity_congr_ae
  filter_upwards [hlevel] with p hp
  simp only [sliceUnderGraphDensity, Function.comp_apply]
  rw [if_congr hp rfl rfl]
  simp [Prod.swap]

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

/-- For interval superlevel sets, the vertical slice-height marginal is the
explicit width-weighted height measure. -/
theorem sliceHeightKernel_comp_weightedVolume_eq_intervalHeightMeasure
    (weight lower upper : ℝ → ℝ)
    (hweight : Measurable weight) (hlower : Measurable lower)
    (hupper : Measurable upper) (hpositive : ∀ x, 0 < weight x)
    (hordered : ∀ height, lower height ≤ upper height)
    (hlevel : ∀ height state,
      state ∈ Ioc (lower height) (upper height) ↔
        height ∈ Ioc 0 (weight state)) :
    sliceHeightKernel weight hweight hpositive ∘ₘ
        (volume : Measure ℝ).withDensity
          (fun x => ENNReal.ofReal (weight x)) =
      intervalHeightMeasure lower upper := by
  letI : SFinite (intervalHeightMeasure lower upper) := by
    unfold intervalHeightMeasure
    infer_instance
  have hvertical := congrArg Measure.snd
    (compProd_sliceHeightKernel_eq_sliceUnderGraph
      (volume : Measure ℝ) weight hweight hpositive)
  rw [Measure.snd_compProd] at hvertical
  have hhorizontal := congrArg Measure.fst
    (compProd_totalIntervalKernel_eq_map_swap_sliceUnderGraph
      weight lower upper hweight hlower hupper hordered hlevel)
  rw [Measure.fst_compProd, Measure.fst_map_swap] at hhorizontal
  exact hvertical.trans hhorizontal.symm

/-- Almost-everywhere level-set identification is sufficient to identify the
vertical height marginal. In particular, open/closed endpoint conventions do
not become artificial sampler assumptions. -/
theorem sliceHeightKernel_comp_weightedVolume_eq_intervalHeightMeasure_ae
    (weight lower upper : ℝ → ℝ)
    (hweight : Measurable weight) (hlower : Measurable lower)
    (hupper : Measurable upper) (hpositive : ∀ x, 0 < weight x)
    (hordered : ∀ height, lower height ≤ upper height)
    (hlevel : ∀ᵐ p : ℝ × ℝ ∂(volume : Measure ℝ).prod volume,
      (p.2 ∈ Ioc (lower p.1) (upper p.1) ↔
        p.1 ∈ Ioc 0 (weight p.2))) :
    sliceHeightKernel weight hweight hpositive ∘ₘ
        (volume : Measure ℝ).withDensity
          (fun x => ENNReal.ofReal (weight x)) =
      intervalHeightMeasure lower upper := by
  letI : SFinite (intervalHeightMeasure lower upper) := by
    unfold intervalHeightMeasure
    infer_instance
  have hvertical := congrArg Measure.snd
    (compProd_sliceHeightKernel_eq_sliceUnderGraph
      (volume : Measure ℝ) weight hweight hpositive)
  rw [Measure.snd_compProd] at hvertical
  have hhorizontal := congrArg Measure.fst
    (compProd_totalIntervalKernel_eq_map_swap_sliceUnderGraph_ae
      weight lower upper hweight hlower hupper hordered hlevel)
  rw [Measure.fst_compProd, Measure.fst_map_swap] at hhorizontal
  exact hvertical.trans hhorizontal.symm

/-- The measurable horizontal level-set update obtained by disintegrating the
finite under-the-graph measure in height--state order.  On heights with
positive marginal mass this is the normalized restriction of `base` to the
corresponding level set, up to the usual almost-everywhere uniqueness of
conditional probabilities. -/
noncomputable def sliceHorizontalKernel
    (base : Measure State) (weight : State → ℝ)
    [IsFiniteMeasure (sliceUnderGraph base weight)] [StandardBorelSpace State]
    [Nonempty State] :
    Kernel ℝ State :=
  ((sliceUnderGraph base weight).map Prod.swap).condKernel

instance sliceHorizontalKernel.instIsMarkovKernel
    (base : Measure State) (weight : State → ℝ)
    [IsFiniteMeasure (sliceUnderGraph base weight)] [StandardBorelSpace State]
    [Nonempty State] :
    IsMarkovKernel (sliceHorizontalKernel base weight) := by
  unfold sliceHorizontalKernel
  infer_instance

/-- The disintegrated horizontal kernel exactly reconstructs the swapped
under-the-graph joint measure from its height marginal. -/
theorem compProd_sliceHorizontalKernel
    (base : Measure State) [SFinite base]
    (weight : State → ℝ) (hweight : Measurable weight)
    (hpositive : ∀ x, 0 < weight x)
    [IsFiniteMeasure (sliceUnderGraph base weight)] [StandardBorelSpace State]
    [Nonempty State] :
    (sliceHeightKernel weight hweight hpositive ∘ₘ
        base.withDensity (fun x => ENNReal.ofReal (weight x))) ⊗ₘ
        sliceHorizontalKernel base weight =
      (sliceUnderGraph base weight).map Prod.swap := by
  let joint := (sliceUnderGraph base weight).map Prod.swap
  have hmarginal : joint.fst =
      sliceHeightKernel weight hweight hpositive ∘ₘ
        base.withDensity (fun x => ENNReal.ofReal (weight x)) := by
    rw [show joint = (sliceUnderGraph base weight).map Prod.swap by rfl,
      Measure.fst_map_swap,
      ← compProd_sliceHeightKernel_eq_sliceUnderGraph base weight hweight hpositive,
      Measure.snd_compProd]
  rw [← hmarginal]
  exact MeasureTheory.Measure.disintegrate joint joint.condKernel

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

/-- Fully explicit exact slice sampler for a one-dimensional target whose
superlevel sets are measurable intervals. Empty level sets use the total
kernel's identity fallback; those rows have zero height-marginal mass. -/
noncomputable def intervalLevelSliceSampler
    (weight lower upper : ℝ → ℝ)
    (hweight : Measurable weight) (hlower : Measurable lower)
    (hupper : Measurable upper) (hpositive : ∀ x, 0 < weight x) :
    Kernel ℝ ℝ :=
  exactSliceSampler weight hweight hpositive
    (totalVariableIntervalKernel lower upper hlower hupper)

/-- The explicit interval-level slice sampler preserves the unnormalized
weighted Lebesgue target. This is stationarity only; it does not assert
irreducibility, convergence, or a mixing rate. -/
theorem intervalLevelSliceSampler_invariant
    (weight lower upper : ℝ → ℝ)
    (hweight : Measurable weight) (hlower : Measurable lower)
    (hupper : Measurable upper) (hpositive : ∀ x, 0 < weight x)
    (hordered : ∀ height, lower height ≤ upper height)
    (hlevel : ∀ height state,
      state ∈ Ioc (lower height) (upper height) ↔
        height ∈ Ioc 0 (weight state)) :
    (intervalLevelSliceSampler weight lower upper hweight hlower hupper
      hpositive).Invariant
        ((volume : Measure ℝ).withDensity
          (fun x => ENNReal.ofReal (weight x))) := by
  apply exactSliceSampler_invariant_underGraph
    (volume : Measure ℝ) weight hweight hpositive
      (totalVariableIntervalKernel lower upper hlower hupper)
  rw [sliceHeightKernel_comp_weightedVolume_eq_intervalHeightMeasure
    weight lower upper hweight hlower hupper hpositive hordered hlevel]
  exact (compProd_totalIntervalKernel_eq_map_swap_sliceUnderGraph
    weight lower upper hweight hlower hupper hordered hlevel).symm

/-- Endpoint-insensitive version of explicit interval-level slice invariance.
Level-set equality is required only almost everywhere under planar Lebesgue
measure. -/
theorem intervalLevelSliceSampler_invariant_ae
    (weight lower upper : ℝ → ℝ)
    (hweight : Measurable weight) (hlower : Measurable lower)
    (hupper : Measurable upper) (hpositive : ∀ x, 0 < weight x)
    (hordered : ∀ height, lower height ≤ upper height)
    (hlevel : ∀ᵐ p : ℝ × ℝ ∂(volume : Measure ℝ).prod volume,
      (p.2 ∈ Ioc (lower p.1) (upper p.1) ↔
        p.1 ∈ Ioc 0 (weight p.2))) :
    (intervalLevelSliceSampler weight lower upper hweight hlower hupper
      hpositive).Invariant
        ((volume : Measure ℝ).withDensity
          (fun x => ENNReal.ofReal (weight x))) := by
  apply exactSliceSampler_invariant_underGraph
    (volume : Measure ℝ) weight hweight hpositive
      (totalVariableIntervalKernel lower upper hlower hupper)
  rw [sliceHeightKernel_comp_weightedVolume_eq_intervalHeightMeasure_ae
    weight lower upper hweight hlower hupper hpositive hordered hlevel]
  exact (compProd_totalIntervalKernel_eq_map_swap_sliceUnderGraph_ae
    weight lower upper hweight hlower hupper hordered hlevel).symm

/-- Slice update whose horizontal transition may depend on both the sampled
height and current state. This is the appropriate exact-kernel interface for
stepping-out and shrinkage algorithms. -/
noncomputable def withinSliceSampler
    (weight : State → ℝ) (hweight : Measurable weight)
    (hpositive : ∀ x, 0 < weight x)
    (horizontal : Kernel (ℝ × State) (ℝ × State)) : Kernel State State :=
  auxiliaryInvariantUpdate (sliceHeightKernel weight hweight hpositive)
    horizontal

/-- A horizontal transition preserving the swapped under-the-graph joint law
yields an invariant weighted-target slice sampler. Exact conditional redraw is
not required. -/
theorem withinSliceSampler_invariant_underGraph
    (base : Measure State) [SFinite base]
    (weight : State → ℝ) (hweight : Measurable weight)
    (hpositive : ∀ x, 0 < weight x)
    (horizontal : Kernel (ℝ × State) (ℝ × State))
    [IsMarkovKernel horizontal]
    (hhorizontal : horizontal.Invariant
      ((sliceUnderGraph base weight).map Prod.swap)) :
    (withinSliceSampler weight hweight hpositive horizontal).Invariant
      (base.withDensity (fun x => ENNReal.ofReal (weight x))) := by
  apply auxiliaryInvariantUpdate_invariant
  rw [auxiliaryFirstJoint_sliceHeightKernel base weight hweight hpositive]
  exact hhorizontal

/-! ### Randomized horizontal updates -/

/-- Independently randomize a family of height/current-state horizontal
updates, then project through the usual vertical slice augmentation.  This is
the exact kernel shape of stepping-out algorithms whose bracket offset and
left/right expansion allocation are sampled independently of the current
augmented state. -/
noncomputable def randomizedWithinSliceSampler
    {Parameter : Type*} [MeasurableSpace Parameter]
    (weight : State → ℝ) (hweight : Measurable weight)
    (hpositive : ∀ x, 0 < weight x)
    (horizontalFamily : Kernel ((ℝ × State) × Parameter) (ℝ × State))
    (parameterLaw : Measure Parameter) : Kernel State State :=
  withinSliceSampler weight hweight hpositive
    (independentParameterMixture horizontalFamily parameterLaw)

instance randomizedWithinSliceSampler.instIsMarkovKernel
    {Parameter : Type*} [MeasurableSpace Parameter]
    (weight : State → ℝ) (hweight : Measurable weight)
    (hpositive : ∀ x, 0 < weight x)
    (horizontalFamily : Kernel ((ℝ × State) × Parameter) (ℝ × State))
    [IsMarkovKernel horizontalFamily]
    (parameterLaw : Measure Parameter) [IsProbabilityMeasure parameterLaw] :
    IsMarkovKernel (randomizedWithinSliceSampler weight hweight hpositive
      horizontalFamily parameterLaw) := by
  letI : IsMarkovKernel (sliceHeightKernel weight hweight hpositive) :=
    sliceHeightKernel.instIsMarkovKernel weight hweight hpositive
  letI : IsMarkovKernel
      (independentParameterMixture horizontalFamily parameterLaw) := by
    infer_instance
  unfold randomizedWithinSliceSampler withinSliceSampler
  infer_instance

/-- Randomized stepping-out/shrinkage preserves the weighted target once
every fixed randomization section preserves the swapped under-graph joint
law. This reduces correctness of bracket randomization to a deterministic
section theorem and prevents independent runtime randomness from becoming an
untracked assumption. -/
theorem randomizedWithinSliceSampler_invariant_underGraph
    {Parameter : Type*} [MeasurableSpace Parameter]
    (base : Measure State) [SFinite base]
    (weight : State → ℝ) (hweight : Measurable weight)
    [SFinite (sliceUnderGraph base weight)]
    (hpositive : ∀ x, 0 < weight x)
    (horizontalFamily : Kernel ((ℝ × State) × Parameter) (ℝ × State))
    [IsMarkovKernel horizontalFamily]
    (parameterLaw : Measure Parameter) [IsProbabilityMeasure parameterLaw]
    (hsection : ∀ parameter,
      (Kernel.comap horizontalFamily
        (fun state : ℝ × State ↦ (state, parameter))
        (measurable_id.prodMk measurable_const)).Invariant
          ((sliceUnderGraph base weight).map Prod.swap)) :
    (randomizedWithinSliceSampler weight hweight hpositive horizontalFamily
      parameterLaw).Invariant
        (base.withDensity (fun x ↦ ENNReal.ofReal (weight x))) := by
  apply withinSliceSampler_invariant_underGraph base weight hweight hpositive
  exact independentParameterMixture_invariant horizontalFamily
    ((sliceUnderGraph base weight).map Prod.swap) parameterLaw hsection

/-- Almost-everywhere fixed-randomization preservation is sufficient. This is
the natural interface for continuous uniform bracket offsets, whose endpoint
exceptions have zero parameter-law mass. -/
theorem randomizedWithinSliceSampler_invariant_underGraph_ae
    {Parameter : Type*} [MeasurableSpace Parameter]
    (base : Measure State) [SFinite base]
    (weight : State → ℝ) (hweight : Measurable weight)
    [SFinite (sliceUnderGraph base weight)]
    (hpositive : ∀ x, 0 < weight x)
    (horizontalFamily : Kernel ((ℝ × State) × Parameter) (ℝ × State))
    [IsMarkovKernel horizontalFamily]
    (parameterLaw : Measure Parameter) [IsProbabilityMeasure parameterLaw]
    (hsection : ∀ᵐ parameter ∂parameterLaw,
      (Kernel.comap horizontalFamily
        (fun state : ℝ × State ↦ (state, parameter))
        (measurable_id.prodMk measurable_const)).Invariant
          ((sliceUnderGraph base weight).map Prod.swap)) :
    (randomizedWithinSliceSampler weight hweight hpositive horizontalFamily
      parameterLaw).Invariant
        (base.withDensity (fun x ↦ ENNReal.ofReal (weight x))) := by
  apply withinSliceSampler_invariant_underGraph base weight hweight hpositive
  exact independentParameterMixture_invariant_ae horizontalFamily
    ((sliceUnderGraph base weight).map Prod.swap) parameterLaw hsection

/-! ### Deterministic trace-reversal sections -/

/-- A jointly measurable fixed-trace update, interpreted as a deterministic
horizontal-kernel family. `Parameter` contains all random choices used by one
execution trace; mixing over its law happens only after each deterministic
section has been verified. -/
noncomputable def deterministicHorizontalFamily
    {Parameter : Type*} [MeasurableSpace Parameter]
    (transform : ((ℝ × State) × Parameter) → (ℝ × State))
    (htransform : Measurable transform) :
    Kernel ((ℝ × State) × Parameter) (ℝ × State) :=
  Kernel.deterministic transform htransform

instance deterministicHorizontalFamily.instIsMarkovKernel
    {Parameter : Type*} [MeasurableSpace Parameter]
    (transform : ((ℝ × State) × Parameter) → (ℝ × State))
    (htransform : Measurable transform) :
    IsMarkovKernel (deterministicHorizontalFamily transform htransform) := by
  unfold deterministicHorizontalFamily
  infer_instance

/-- Fixing the trace parameter in a deterministic horizontal family gives the
deterministic kernel of the corresponding section. -/
theorem comap_deterministicHorizontalFamily
    {Parameter : Type*} [MeasurableSpace Parameter]
    (transform : ((ℝ × State) × Parameter) → (ℝ × State))
    (htransform : Measurable transform) (parameter : Parameter) :
    Kernel.comap (deterministicHorizontalFamily transform htransform)
        (fun state : ℝ × State ↦ (state, parameter))
        (measurable_id.prodMk measurable_const) =
      Kernel.deterministic (fun state ↦ transform (state, parameter))
        (htransform.comp (measurable_id.prodMk measurable_const)) := by
  ext state event hevent
  simp [deterministicHorizontalFamily, Kernel.comap_apply,
    Kernel.deterministic_apply, hevent]

/-- Trace-reversal endpoint for practical slice updates. If every fixed trace
acts by a measurable measure-preserving map on the swapped under-graph law,
then independently sampling the trace and applying that deterministic section
preserves the weighted target exactly. This theorem isolates the remaining
algorithm proof: construct the trace reversal and prove its preservation. -/
theorem deterministicRandomizedWithinSliceSampler_invariant_underGraph
    {Parameter : Type*} [MeasurableSpace Parameter]
    (base : Measure State) [SFinite base]
    (weight : State → ℝ) (hweight : Measurable weight)
    [SFinite (sliceUnderGraph base weight)]
    (hpositive : ∀ x, 0 < weight x)
    (transform : ((ℝ × State) × Parameter) → (ℝ × State))
    (htransform : Measurable transform)
    (parameterLaw : Measure Parameter) [IsProbabilityMeasure parameterLaw]
    (hpreserving : ∀ parameter, MeasurePreserving
      (fun state ↦ transform (state, parameter))
      ((sliceUnderGraph base weight).map Prod.swap)
      ((sliceUnderGraph base weight).map Prod.swap)) :
    (randomizedWithinSliceSampler weight hweight hpositive
      (deterministicHorizontalFamily transform htransform)
      parameterLaw).Invariant
        (base.withDensity (fun x ↦ ENNReal.ofReal (weight x))) := by
  apply randomizedWithinSliceSampler_invariant_underGraph
    base weight hweight hpositive
      (deterministicHorizontalFamily transform htransform) parameterLaw
  intro parameter
  rw [comap_deterministicHorizontalFamily transform htransform parameter]
  exact deterministic_invariant_of_measurePreserving
    ((sliceUnderGraph base weight).map Prod.swap)
    (htransform.comp (measurable_id.prodMk measurable_const))
    (hpreserving parameter)

/-- Continuous traces need only be measure preserving almost surely under the
trace law. This admits null boundary traces created by uniforms equal to an
endpoint without turning them into global algorithm assumptions. -/
theorem deterministicRandomizedWithinSliceSampler_invariant_underGraph_ae
    {Parameter : Type*} [MeasurableSpace Parameter]
    (base : Measure State) [SFinite base]
    (weight : State → ℝ) (hweight : Measurable weight)
    [SFinite (sliceUnderGraph base weight)]
    (hpositive : ∀ x, 0 < weight x)
    (transform : ((ℝ × State) × Parameter) → (ℝ × State))
    (htransform : Measurable transform)
    (parameterLaw : Measure Parameter) [IsProbabilityMeasure parameterLaw]
    (hpreserving : ∀ᵐ parameter ∂parameterLaw, MeasurePreserving
      (fun state ↦ transform (state, parameter))
      ((sliceUnderGraph base weight).map Prod.swap)
      ((sliceUnderGraph base weight).map Prod.swap)) :
    (randomizedWithinSliceSampler weight hweight hpositive
      (deterministicHorizontalFamily transform htransform)
      parameterLaw).Invariant
        (base.withDensity (fun x ↦ ENNReal.ofReal (weight x))) := by
  apply randomizedWithinSliceSampler_invariant_underGraph_ae
    base weight hweight hpositive
      (deterministicHorizontalFamily transform htransform) parameterLaw
  filter_upwards [hpreserving] with parameter hp
  rw [comap_deterministicHorizontalFamily transform htransform parameter]
  exact deterministic_invariant_of_measurePreserving
    ((sliceUnderGraph base weight).map Prod.swap)
    (htransform.comp (measurable_id.prodMk measurable_const)) hp

/-! ### Joint trace-space reversals -/

/-- Horizontal update obtained by sampling a complete independent execution
trace, applying a deterministic map on augmented-state--trace space, and
discarding the transformed trace. This is the appropriate semantics when the
reverse execution uses a different trace from the forward execution. -/
noncomputable def traceDrivenHorizontalKernel
    {Trace : Type*} [MeasurableSpace Trace]
    (traceLaw : Measure Trace)
    (transform : ((ℝ × State) × Trace) → ((ℝ × State) × Trace))
    (htransform : Measurable transform) : Kernel (ℝ × State) (ℝ × State) :=
  liftEvolveProject
    (Kernel.id ×ₖ Kernel.const (ℝ × State) traceLaw)
    (Kernel.deterministic transform htransform)
    Prod.fst measurable_fst

instance traceDrivenHorizontalKernel.instIsMarkovKernel
    {Trace : Type*} [MeasurableSpace Trace]
    (traceLaw : Measure Trace) [IsProbabilityMeasure traceLaw]
    (transform : ((ℝ × State) × Trace) → ((ℝ × State) × Trace))
    (htransform : Measurable transform) :
    IsMarkovKernel (traceDrivenHorizontalKernel traceLaw transform htransform) := by
  unfold traceDrivenHorizontalKernel
  infer_instance

/-- A measure-preserving deterministic trace reversal makes the induced
horizontal update invariant. Unlike fixed-section preservation, this permits
the inverse execution to transform the random trace. -/
theorem traceDrivenHorizontalKernel_invariant
    {Trace : Type*} [MeasurableSpace Trace]
    (joint : Measure (ℝ × State)) [SFinite joint]
    (traceLaw : Measure Trace) [IsProbabilityMeasure traceLaw]
    (transform : ((ℝ × State) × Trace) → ((ℝ × State) × Trace))
    (htransform : Measurable transform)
    (hpreserving : MeasurePreserving transform
      (joint ⊗ₘ Kernel.const (ℝ × State) traceLaw)
      (joint ⊗ₘ Kernel.const (ℝ × State) traceLaw)) :
    (traceDrivenHorizontalKernel traceLaw transform htransform).Invariant
      joint := by
  unfold traceDrivenHorizontalKernel
  apply compProdEvolveFst_invariant joint
    (Kernel.const (ℝ × State) traceLaw)
  exact deterministic_invariant_of_measurePreserving
    (joint ⊗ₘ Kernel.const (ℝ × State) traceLaw) htransform hpreserving

/-- End-to-end trace-reversal theorem for practical slice sampling. A
measure-preserving map on under-graph-state--trace space induces an exact
weighted-target invariant sampler after trace sampling and projection. -/
theorem traceDrivenWithinSliceSampler_invariant_underGraph
    {Trace : Type*} [MeasurableSpace Trace]
    (base : Measure State) [SFinite base]
    (weight : State → ℝ) (hweight : Measurable weight)
    [SFinite (sliceUnderGraph base weight)]
    (hpositive : ∀ x, 0 < weight x)
    (traceLaw : Measure Trace) [IsProbabilityMeasure traceLaw]
    (transform : ((ℝ × State) × Trace) → ((ℝ × State) × Trace))
    (htransform : Measurable transform)
    (hpreserving : MeasurePreserving transform
      (((sliceUnderGraph base weight).map Prod.swap) ⊗ₘ
        Kernel.const (ℝ × State) traceLaw)
      (((sliceUnderGraph base weight).map Prod.swap) ⊗ₘ
        Kernel.const (ℝ × State) traceLaw)) :
    (withinSliceSampler weight hweight hpositive
      (traceDrivenHorizontalKernel traceLaw transform htransform)).Invariant
        (base.withDensity (fun x ↦ ENNReal.ofReal (weight x))) := by
  apply withinSliceSampler_invariant_underGraph
    base weight hweight hpositive
  exact traceDrivenHorizontalKernel_invariant
    ((sliceUnderGraph base weight).map Prod.swap)
    traceLaw transform htransform hpreserving

/-- A fully constructed exact general-state slice sampler on a standard Borel
state space, using the conditional kernel of the finite under-the-graph
measure for its horizontal update. -/
noncomputable def disintegratedSliceSampler
    (base : Measure State) (weight : State → ℝ)
    (hweight : Measurable weight) (hpositive : ∀ x, 0 < weight x)
    [IsFiniteMeasure (sliceUnderGraph base weight)] [StandardBorelSpace State]
    [Nonempty State] : Kernel State State :=
  exactSliceSampler weight hweight hpositive
    (sliceHorizontalKernel base weight)

/-- The disintegrated exact slice sampler preserves the weighted target.
This is an invariance theorem; no irreducibility, convergence, or rate claim
is implied. -/
theorem disintegratedSliceSampler_invariant
    (base : Measure State) [SFinite base]
    (weight : State → ℝ) (hweight : Measurable weight)
    (hpositive : ∀ x, 0 < weight x)
    [IsFiniteMeasure (sliceUnderGraph base weight)] [StandardBorelSpace State]
    [Nonempty State] :
    (disintegratedSliceSampler base weight hweight hpositive).Invariant
      (base.withDensity (fun x => ENNReal.ofReal (weight x))) := by
  apply exactSliceSampler_invariant_underGraph base weight hweight hpositive
    (sliceHorizontalKernel base weight)
  exact (compProd_sliceHorizontalKernel base weight hweight hpositive).symm

/-- Slice-specific wrapper around general disintegration when the target
measure itself is already finite. This avoids asking a client to separately
construct a finite-measure instance for the equal under-graph joint. -/
noncomputable def targetDisintegratedSliceSampler
    (target : Measure State) [IsFiniteMeasure target]
    (weight : State → ℝ) (hweight : Measurable weight)
    (hpositive : ∀ x, 0 < weight x)
    [StandardBorelSpace State] [Nonempty State] : Kernel State State :=
  exactSliceSampler weight hweight hpositive
    (disintegratedAuxiliaryReverse target
      (sliceHeightKernel weight hweight hpositive))

/-- The finite-target disintegrated slice wrapper preserves its supplied
target. For the usual weighted-base interpretation, clients should additionally
identify `target` with the intended density measure. -/
theorem targetDisintegratedSliceSampler_invariant
    (target : Measure State) [IsFiniteMeasure target]
    (weight : State → ℝ) (hweight : Measurable weight)
    (hpositive : ∀ x, 0 < weight x)
    [StandardBorelSpace State] [Nonempty State] :
    (targetDisintegratedSliceSampler target weight hweight hpositive).Invariant
      target := by
  exact twoBlockConditional_disintegrated_invariant target
    (sliceHeightKernel weight hweight hpositive)

end Mcmc.Kernel
