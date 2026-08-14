import Mathlib.Probability.Kernel.Composition.CompMap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Invariance

/-!
# Couplings of measures and Markov kernels

This module defines the measure-theoretic coupling interface used for coupled
MCMC.  A coupling of `μ` and `ν` is a measure on the product space with those
two marginals.  A coupled kernel for `κ` and `η` is a product-valued kernel
whose first marginal applies `κ` to the first input coordinate and whose
second marginal applies `η` to the second input coordinate.

The definitions use mathlib's existing marginal, map, comap, and product
operations.  They do not introduce a parallel notion of probability measure
or Markov kernel.
-/

open MeasureTheory
open scoped ProbabilityTheory

namespace Mcmc

variable {α β γ δ ε ζ : Type*}
  [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace γ] [MeasurableSpace δ]
  [MeasurableSpace ε] [MeasurableSpace ζ]

/-- `ρ` is a coupling of `μ` and `ν` when its coordinate marginals are exactly
`μ` and `ν`. -/
def IsMeasureCoupling (ρ : Measure (α × β)) (μ : Measure α) (ν : Measure β) : Prop :=
  ρ.fst = μ ∧ ρ.snd = ν

namespace IsMeasureCoupling

/-- The first marginal of a coupling. -/
theorem fst {ρ : Measure (α × β)} {μ : Measure α} {ν : Measure β}
    (h : IsMeasureCoupling ρ μ ν) :
    ρ.fst = μ :=
  h.1

/-- The second marginal of a coupling. -/
theorem snd {ρ : Measure (α × β)} {μ : Measure α} {ν : Measure β}
    (h : IsMeasureCoupling ρ μ ν) :
    ρ.snd = ν :=
  h.2

/-- A coupling of a probability measure has total mass one. -/
theorem isProbabilityMeasure {ρ : Measure (α × β)} {μ : Measure α} {ν : Measure β}
    (h : IsMeasureCoupling ρ μ ν) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure ρ where
  measure_univ := by
    rw [← Measure.fst_univ, h.fst, measure_univ]

/-- Swapping coordinates swaps the marginals of a coupling. -/
theorem swap {ρ : Measure (α × β)} {μ : Measure α} {ν : Measure β}
    (h : IsMeasureCoupling ρ μ ν) :
    IsMeasureCoupling (ρ.map Prod.swap) ν μ := by
  exact ⟨Measure.fst_map_swap.trans h.snd, Measure.snd_map_swap.trans h.fst⟩

end IsMeasureCoupling

/-- The independent product measure is a coupling. -/
theorem isMeasureCoupling_prod (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsMeasureCoupling (μ.prod ν) μ ν := by
  exact ⟨Measure.fst_prod, Measure.snd_prod⟩

namespace Kernel

open ProbabilityTheory

/-- `coupled` couples `left` and `right` when each output marginal is the
corresponding kernel applied only to its own input coordinate. -/
def IsCoupling
    (coupled : ProbabilityTheory.Kernel (α × β) (γ × δ))
    (left : ProbabilityTheory.Kernel α γ)
    (right : ProbabilityTheory.Kernel β δ) : Prop :=
  coupled.fst = left.comap Prod.fst measurable_fst ∧
    coupled.snd = right.comap Prod.snd measurable_snd

namespace IsCoupling

/-- The first marginal identity of a coupled kernel. -/
theorem fst
    {coupled : ProbabilityTheory.Kernel (α × β) (γ × δ)}
    {left : ProbabilityTheory.Kernel α γ}
    {right : ProbabilityTheory.Kernel β δ}
    (h : IsCoupling coupled left right) :
    coupled.fst = left.comap Prod.fst measurable_fst :=
  h.1

/-- The second marginal identity of a coupled kernel. -/
theorem snd
    {coupled : ProbabilityTheory.Kernel (α × β) (γ × δ)}
    {left : ProbabilityTheory.Kernel α γ}
    {right : ProbabilityTheory.Kernel β δ}
    (h : IsCoupling coupled left right) :
    coupled.snd = right.comap Prod.snd measurable_snd :=
  h.2

/-- Pointwise form of the first marginal identity. -/
theorem fst_apply
    {coupled : ProbabilityTheory.Kernel (α × β) (γ × δ)}
    {left : ProbabilityTheory.Kernel α γ}
    {right : ProbabilityTheory.Kernel β δ}
    (h : IsCoupling coupled left right) (x : α × β) :
    coupled.fst x = left x.1 := by
  rw [h.fst, ProbabilityTheory.Kernel.comap_apply]

/-- Pointwise form of the second marginal identity. -/
theorem snd_apply
    {coupled : ProbabilityTheory.Kernel (α × β) (γ × δ)}
    {left : ProbabilityTheory.Kernel α γ}
    {right : ProbabilityTheory.Kernel β δ}
    (h : IsCoupling coupled left right) (x : α × β) :
    coupled.snd x = right x.2 := by
  rw [h.snd, ProbabilityTheory.Kernel.comap_apply]

/-- Additive lift of a one-state function to a paired state. -/
def pairedAdd (v : γ → ENNReal) (z : γ × γ) : ENNReal :=
  v z.1 + v z.2

theorem measurable_pairedAdd {v : γ → ENNReal} (hv : Measurable v) :
    Measurable (pairedAdd v) :=
  (hv.comp measurable_fst).add (hv.comp measurable_snd)

/-- The expected additive paired function depends only on the two marginals
of a coupling, not on their dependence structure. -/
theorem lintegral_pairedAdd
    {coupled : ProbabilityTheory.Kernel (α × β) (γ × γ)}
    {left : ProbabilityTheory.Kernel α γ}
    {right : ProbabilityTheory.Kernel β γ}
    (h : IsCoupling coupled left right)
    {v : γ → ENNReal} (hv : Measurable v) (x : α × β) :
    (∫⁻ z, pairedAdd v z ∂coupled x) =
      (∫⁻ y, v y ∂left x.1) + (∫⁻ y, v y ∂right x.2) := by
  change (∫⁻ z, v z.1 + v z.2 ∂coupled x) = _
  have hfst : Measurable (fun z : γ × γ => v z.1) :=
    hv.comp measurable_fst
  rw [lintegral_add_left hfst]
  rw [← ProbabilityTheory.Kernel.lintegral_fst coupled x hv,
    ← ProbabilityTheory.Kernel.lintegral_snd coupled x hv,
    h.fst_apply x, h.snd_apply x]

end IsCoupling

/-- The conditionally independent product of two kernels is a coupling. -/
noncomputable def independentCoupling
    (left : ProbabilityTheory.Kernel α γ)
    (right : ProbabilityTheory.Kernel β δ) :
    ProbabilityTheory.Kernel (α × β) (γ × δ) :=
  (left.comap Prod.fst measurable_fst) ×ₖ
    (right.comap Prod.snd measurable_snd)

instance independentCoupling.instIsMarkovKernel
    (left : ProbabilityTheory.Kernel α γ) [IsMarkovKernel left]
    (right : ProbabilityTheory.Kernel β δ) [IsMarkovKernel right] :
    IsMarkovKernel (independentCoupling left right) := by
  unfold independentCoupling
  infer_instance

/-- The independent product construction has the requested kernel marginals. -/
theorem independentCoupling_isCoupling
    (left : ProbabilityTheory.Kernel α γ) [IsMarkovKernel left]
    (right : ProbabilityTheory.Kernel β δ) [IsMarkovKernel right] :
    IsCoupling (independentCoupling left right) left right := by
  constructor <;> simp [independentCoupling]

/-- Mapping the two output coordinates of a coupled kernel preserves the
coupling relation and maps the corresponding marginal kernels. -/
theorem map_isCoupling
    (coupled : ProbabilityTheory.Kernel (α × β) (γ × δ))
    (left : ProbabilityTheory.Kernel α γ)
    (right : ProbabilityTheory.Kernel β δ)
    (h : IsCoupling coupled left right)
    (f : γ → ε) (g : δ → ζ) (hf : Measurable f) (hg : Measurable g) :
    IsCoupling (coupled.map (Prod.map f g))
      (left.map f) (right.map g) := by
  constructor
  · rw [ProbabilityTheory.Kernel.fst_eq,
      ← ProbabilityTheory.Kernel.map_comp_right coupled (hf.prodMap hg) measurable_fst]
    change coupled.map (f ∘ Prod.fst) = _
    rw [ProbabilityTheory.Kernel.map_comp_right coupled measurable_fst hf,
      ← ProbabilityTheory.Kernel.fst_eq, h.fst,
      ← ProbabilityTheory.Kernel.comap_map_comm left measurable_fst hf]
  · rw [ProbabilityTheory.Kernel.snd_eq,
      ← ProbabilityTheory.Kernel.map_comp_right coupled (hf.prodMap hg) measurable_snd]
    change coupled.map (g ∘ Prod.snd) = _
    rw [ProbabilityTheory.Kernel.map_comp_right coupled measurable_snd hg,
      ← ProbabilityTheory.Kernel.snd_eq, h.snd,
      ← ProbabilityTheory.Kernel.comap_map_comm right measurable_snd hg]

/-- A convex mixture of two kernels, with `p` the weight of the first
kernel. The interval-valued weight makes normalization part of the input. -/
noncomputable def mixture
    (p : Set.Icc (0 : NNReal) 1)
    (first second : ProbabilityTheory.Kernel α β) :
    ProbabilityTheory.Kernel α β where
  toFun x := p.1 • first x + (1 - p.1) • second x
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    exact (measurable_const.mul (first.measurable_coe hs)).add
      (measurable_const.mul (second.measurable_coe hs))

@[simp]
theorem mixture_apply
    (p : Set.Icc (0 : NNReal) 1)
    (first second : ProbabilityTheory.Kernel α β) (x : α) :
    mixture p first second x = p.1 • first x + (1 - p.1) • second x :=
  rfl

instance mixture.instIsMarkovKernel
    (p : Set.Icc (0 : NNReal) 1)
    (first second : ProbabilityTheory.Kernel α β)
    [IsMarkovKernel first] [IsMarkovKernel second] :
    IsMarkovKernel (mixture p first second) where
  isProbabilityMeasure x := by
    constructor
    simp only [mixture_apply, Measure.add_apply, Measure.smul_apply,
      measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one]
    exact_mod_cast add_tsub_cancel_of_le p.property.2

/-- Mixing two couplings with a shared weight couples the corresponding
mixtures of their marginal kernels. -/
theorem mixture_isCoupling
    (p : Set.Icc (0 : NNReal) 1)
    (coupled₁ coupled₂ : ProbabilityTheory.Kernel (α × β) (γ × δ))
    (left₁ left₂ : ProbabilityTheory.Kernel α γ)
    (right₁ right₂ : ProbabilityTheory.Kernel β δ)
    (h₁ : IsCoupling coupled₁ left₁ right₁)
    (h₂ : IsCoupling coupled₂ left₂ right₂) :
    IsCoupling (mixture p coupled₁ coupled₂)
      (mixture p left₁ left₂) (mixture p right₁ right₂) := by
  constructor
  · ext x s hs
    rw [ProbabilityTheory.Kernel.comap_apply]
    simp only [ProbabilityTheory.Kernel.fst_apply' _ _ hs, mixture_apply,
      Measure.add_apply, Measure.smul_apply]
    change p.1 • coupled₁ x (Prod.fst ⁻¹' s) +
      (1 - p.1) • coupled₂ x (Prod.fst ⁻¹' s) = _
    rw [← Measure.fst_apply (ρ := coupled₁ x) hs,
      ← Measure.fst_apply (ρ := coupled₂ x) hs]
    change p.1 • (coupled₁.fst x) s + (1 - p.1) • (coupled₂.fst x) s = _
    rw [h₁.fst_apply, h₂.fst_apply]
  · ext x s hs
    rw [ProbabilityTheory.Kernel.comap_apply]
    simp only [ProbabilityTheory.Kernel.snd_apply' _ _ hs, mixture_apply,
      Measure.add_apply, Measure.smul_apply]
    rw [← Measure.snd_apply (ρ := coupled₁ x) hs,
      ← Measure.snd_apply (ρ := coupled₂ x) hs]
    change p.1 • (coupled₁.snd x) s + (1 - p.1) • (coupled₂.snd x) s = _
    rw [h₁.snd_apply, h₂.snd_apply]

/-- A kernel mixture dominates the weighted contribution of its second
branch on every measurable event. -/
theorem mixture_apply_second_le
    (p : Set.Icc (0 : NNReal) 1)
    (first second : ProbabilityTheory.Kernel α β)
    (x : α) {s : Set β} (_hs : MeasurableSet s) :
    ((1 - p.1 : NNReal) : ENNReal) * second x s ≤
      mixture p first second x s := by
  rw [mixture_apply, Measure.add_apply, Measure.smul_apply,
    Measure.smul_apply]
  exact le_add_left le_rfl

/-- A kernel mixture also dominates the weighted contribution of its first
branch on every measurable event. -/
theorem mixture_apply_first_le
    (p : Set.Icc (0 : NNReal) 1)
    (first second : ProbabilityTheory.Kernel α β)
    (x : α) {s : Set β} (_hs : MeasurableSet s) :
    (p.1 : ENNReal) * first x s ≤ mixture p first second x s := by
  rw [mixture_apply, Measure.add_apply, Measure.smul_apply,
    Measure.smul_apply]
  exact le_add_right le_rfl

/-- If the second branch has positive mass on an event and receives positive
mixture weight, then the complete mixture has positive mass on that event. -/
theorem mixture_apply_pos_of_second
    (p : Set.Icc (0 : NNReal) 1) (hp : p.1 < 1)
    (first second : ProbabilityTheory.Kernel α β)
    (x : α) {s : Set β} (hs : MeasurableSet s)
    (hsecond : 0 < second x s) :
    0 < mixture p first second x s := by
  apply lt_of_lt_of_le _ (mixture_apply_second_le p first second x hs)
  have hweight : 0 < (1 - p.1 : NNReal) := tsub_pos_iff_lt.mpr hp
  exact ENNReal.mul_pos (by exact_mod_cast hweight.ne') hsecond.ne'

/-- In particular, an exact-meeting second branch gives the complete coupled
mixture positive one-step meeting probability. This is the structural transfer
used when the RWMH branch is mixed with coupled HMC. -/
theorem mixture_diagonal_pos_of_second [MeasurableEq β]
    (p : Set.Icc (0 : NNReal) 1) (hp : p.1 < 1)
    (first second : ProbabilityTheory.Kernel α (β × β))
    (x : α) (hsecond : 0 < second x (Set.diagonal β)) :
    0 < mixture p first second x (Set.diagonal β) :=
  mixture_apply_pos_of_second p hp first second x measurableSet_diagonal
    hsecond

/-- Evolving a measure through a kernel mixture is the corresponding mixture
of the two evolved measures. -/
theorem mixture_comp_measure
    (p : Set.Icc (0 : NNReal) 1)
    (first second : ProbabilityTheory.Kernel α β)
    (initial : Measure α) :
    mixture p first second ∘ₘ initial =
      p.1 • (first ∘ₘ initial) + (1 - p.1) • (second ∘ₘ initial) := by
  ext s hs
  rw [Measure.bind_apply hs (mixture p first second).aemeasurable]
  simp only [mixture_apply, Measure.add_apply, Measure.smul_apply,
    ENNReal.smul_def, smul_eq_mul]
  rw [lintegral_add_left (μ := initial)
      (f := fun a => (p.1 : ENNReal) * first a s)
      (measurable_const.mul (first.measurable_coe hs))
      (fun a => ((1 - p.1 : NNReal) : ENNReal) * second a s)]
  rw [lintegral_const_mul _ (first.measurable_coe hs),
    lintegral_const_mul _ (second.measurable_coe hs)]
  rw [Measure.bind_apply hs first.aemeasurable,
    Measure.bind_apply hs second.aemeasurable]

/-- A convex mixture of two kernels preserving the same measure also
preserves that measure. -/
theorem mixture_invariant
    (p : Set.Icc (0 : NNReal) 1)
    (first second : ProbabilityTheory.Kernel α α)
    (target : Measure α)
    (hFirst : first.Invariant target)
    (hSecond : second.Invariant target) :
    (mixture p first second).Invariant target := by
  rw [ProbabilityTheory.Kernel.Invariant, mixture_comp_measure,
    hFirst.def, hSecond.def, ← add_smul, add_tsub_cancel_of_le p.property.2,
    one_smul]

/-- Structural correctness of the coupled mixture used later for the
HMC/RWMH transition: it has the mixture kernel on both marginals, and that
single-chain mixture preserves the common target. -/
theorem coupledMixture_isCoupling_and_invariant
    (p : Set.Icc (0 : NNReal) 1)
    (firstCoupled secondCoupled :
      ProbabilityTheory.Kernel (α × α) (α × α))
    (first second : ProbabilityTheory.Kernel α α)
    (target : Measure α)
    (hFirstCoupled : IsCoupling firstCoupled first first)
    (hSecondCoupled : IsCoupling secondCoupled second second)
    (hFirstInvariant : first.Invariant target)
    (hSecondInvariant : second.Invariant target) :
    IsCoupling (mixture p firstCoupled secondCoupled)
        (mixture p first second) (mixture p first second) ∧
      (mixture p first second).Invariant target := by
  exact ⟨mixture_isCoupling p firstCoupled secondCoupled first second
    first second hFirstCoupled hSecondCoupled,
    mixture_invariant p first second target hFirstInvariant hSecondInvariant⟩

/-- Sequential composition of coupled transitions couples the sequential
compositions of their marginal transitions. -/
theorem comp_isCoupling
    (firstCoupled : ProbabilityTheory.Kernel (α × β) (γ × δ))
    (secondCoupled : ProbabilityTheory.Kernel (γ × δ) (ε × ζ))
    (firstLeft : ProbabilityTheory.Kernel α γ)
    (secondLeft : ProbabilityTheory.Kernel γ ε)
    (firstRight : ProbabilityTheory.Kernel β δ)
    (secondRight : ProbabilityTheory.Kernel δ ζ)
    (hFirst : IsCoupling firstCoupled firstLeft firstRight)
    (hSecond : IsCoupling secondCoupled secondLeft secondRight) :
    IsCoupling (secondCoupled ∘ₖ firstCoupled)
      (secondLeft ∘ₖ firstLeft) (secondRight ∘ₖ firstRight) := by
  constructor
  · rw [ProbabilityTheory.Kernel.fst_comp, hSecond.fst,
      ← ProbabilityTheory.Kernel.comp_map, ← ProbabilityTheory.Kernel.fst_eq,
      hFirst.fst]
    simp only [← ProbabilityTheory.Kernel.comp_deterministic_eq_comap,
      ProbabilityTheory.Kernel.comp_assoc]
  · rw [ProbabilityTheory.Kernel.snd_comp, hSecond.snd,
      ← ProbabilityTheory.Kernel.comp_map, ← ProbabilityTheory.Kernel.snd_eq,
      hFirst.snd]
    simp only [← ProbabilityTheory.Kernel.comp_deterministic_eq_comap,
      ProbabilityTheory.Kernel.comp_assoc]

/-- The identity transition on a product space couples the two coordinate
identity transitions. -/
theorem id_isCoupling :
    IsCoupling
      (ProbabilityTheory.Kernel.id : ProbabilityTheory.Kernel (α × β) (α × β))
      (ProbabilityTheory.Kernel.id : ProbabilityTheory.Kernel α α)
      (ProbabilityTheory.Kernel.id : ProbabilityTheory.Kernel β β) := by
  constructor
  · ext x s hs
    rw [ProbabilityTheory.Kernel.fst_apply' _ _ hs,
      ProbabilityTheory.Kernel.comap_apply]
    simp only [ProbabilityTheory.Kernel.id]
    change (ProbabilityTheory.Kernel.deterministic id measurable_id x)
      (Prod.fst ⁻¹' s) = _
    rw [ProbabilityTheory.Kernel.deterministic_apply' _ _ (measurable_fst hs),
      ProbabilityTheory.Kernel.deterministic_apply' _ _ hs]
    rfl
  · ext x s hs
    rw [ProbabilityTheory.Kernel.snd_apply' _ _ hs,
      ProbabilityTheory.Kernel.comap_apply]
    simp only [ProbabilityTheory.Kernel.id]
    rw [ProbabilityTheory.Kernel.deterministic_apply' _ _ (measurable_snd hs),
      ProbabilityTheory.Kernel.deterministic_apply' _ _ hs]
    rfl

/-- Every finite iterate of a coupled endokernel couples the corresponding
iterates of its two marginal endokernels. -/
theorem pow_isCoupling
    (coupled : ProbabilityTheory.Kernel (α × β) (α × β))
    (left : ProbabilityTheory.Kernel α α)
    (right : ProbabilityTheory.Kernel β β)
    (h : IsCoupling coupled left right) (n : ℕ) :
    IsCoupling (coupled ^ n) (left ^ n) (right ^ n) := by
  induction n with
  | zero =>
      change IsCoupling ProbabilityTheory.Kernel.id
        ProbabilityTheory.Kernel.id ProbabilityTheory.Kernel.id
      exact id_isCoupling
  | succ n ih =>
      rw [pow_succ, pow_succ, pow_succ]
      exact comp_isCoupling coupled (coupled ^ n) left (left ^ n)
        right (right ^ n) h ih

/-- Applying a coupled transition to a coupled initial law preserves the
coupling relation and evolves each marginal by its corresponding kernel. -/
theorem compMeasure_isMeasureCoupling
    (initial : Measure (α × β)) (leftInitial : Measure α)
    (rightInitial : Measure β)
    (coupled : ProbabilityTheory.Kernel (α × β) (γ × δ))
    (left : ProbabilityTheory.Kernel α γ)
    (right : ProbabilityTheory.Kernel β δ)
    (hInitial : IsMeasureCoupling initial leftInitial rightInitial)
    (hCoupled : IsCoupling coupled left right) :
    IsMeasureCoupling (Measure.bind initial coupled)
      (Measure.bind leftInitial left) (Measure.bind rightInitial right) := by
  constructor
  · change (Measure.bind initial coupled).map Prod.fst = Measure.bind leftInitial left
    rw [Measure.map_comp _ _ measurable_fst, ← ProbabilityTheory.Kernel.fst_eq, hCoupled.fst,
      ← ProbabilityTheory.Kernel.comp_deterministic_eq_comap,
      ← Measure.comp_assoc, Measure.deterministic_comp_eq_map]
    change Measure.bind initial.fst left = Measure.bind leftInitial left
    rw [hInitial.fst]
  · change (Measure.bind initial coupled).map Prod.snd = Measure.bind rightInitial right
    rw [Measure.map_comp _ _ measurable_snd, ← ProbabilityTheory.Kernel.snd_eq, hCoupled.snd,
      ← ProbabilityTheory.Kernel.comp_deterministic_eq_comap,
      ← Measure.comp_assoc, Measure.deterministic_comp_eq_map]
    change Measure.bind initial.snd right = Measure.bind rightInitial right
    rw [hInitial.snd]

end Kernel
end Mcmc
