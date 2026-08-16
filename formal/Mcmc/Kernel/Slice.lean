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
    (hordered : ∀ parameter, lower parameter < upper parameter)
    (parameter : Parameter) :
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
    (ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr (hordered parameter)))
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
    variableIntervalDensity_lintegral lower upper hordered]

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
  exact variableIntervalDensity_lintegral lower upper hordered parameter

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
