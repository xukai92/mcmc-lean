import Mcmc.Kernel.MetropolisHastings
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Tagged-state reversible-jump Metropolis--Hastings

Reversible-jump MCMC is ordinary Metropolis--Hastings on a disjoint union of
model-specific state spaces once all proposal factors and change-of-variables
Jacobians have been expressed as densities with respect to one tagged
reference measure.  This module supplies that tagged reference and packages
the general density-MH correctness theorem for two models.

The package does not assume a Jacobian formula.  A concrete dimension-changing
move must prove that its supplied forward and reverse densities are the actual
pushforward densities of its auxiliary-variable transport.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace Mcmc.Kernel

open ProbabilityTheory

variable {Left Right : Type*} [MeasurableSpace Left] [MeasurableSpace Right]

/-- Common reference measure on a two-model disjoint union. -/
noncomputable def twoModelReference
    (left : Measure Left) (right : Measure Right) : Measure (Left ⊕ Right) :=
  left.map Sum.inl + right.map Sum.inr

instance twoModelReference.instSFinite
    (left : Measure Left) (right : Measure Right)
    [SFinite left] [SFinite right] :
    SFinite (twoModelReference left right) := by
  unfold twoModelReference
  infer_instance

/-- Certificate that a proposed dimension-changing transport really has the
claimed density with respect to the destination-model reference measure.
In applications, `pushforward_eq` is the change-of-variables theorem whose
density contains the appropriate Jacobian factor. -/
structure TransportDensityCertificate
    {Aux : Type*} [MeasurableSpace Aux]
    (sourceAuxiliary : Left → Measure Aux)
    (destinationReference : Measure Right)
    (transport : Left → Aux → Right)
    (crossDensity : Left → Right → ENNReal) where
  measurableTransport : ∀ x, Measurable (transport x)
  pushforward_eq : ∀ x,
    (sourceAuxiliary x).map (transport x) =
      destinationReference.withDensity (crossDensity x)

omit [MeasurableSpace Left] in
/-- Independent dimension-matching transports compose by products. The
cross-model density is the product of the coordinate densities, so Jacobian
factors compose without rebuilding the change-of-variables argument for every
new product dimension. -/
theorem TransportDensityCertificate.prod
    {Aux₁ Aux₂ Right₁ Right₂ : Type*}
    [MeasurableSpace Aux₁] [MeasurableSpace Aux₂]
    [MeasurableSpace Right₁] [MeasurableSpace Right₂]
    {sourceAuxiliary₁ : Left → Measure Aux₁}
    {sourceAuxiliary₂ : Left → Measure Aux₂}
    {destinationReference₁ : Measure Right₁}
    {destinationReference₂ : Measure Right₂}
    {transport₁ : Left → Aux₁ → Right₁}
    {transport₂ : Left → Aux₂ → Right₂}
    {crossDensity₁ : Left → Right₁ → ENNReal}
    {crossDensity₂ : Left → Right₂ → ENNReal}
    [∀ x, SFinite (sourceAuxiliary₁ x)]
    [∀ x, SFinite (sourceAuxiliary₂ x)]
    [SFinite destinationReference₂]
    (first : TransportDensityCertificate sourceAuxiliary₁
      destinationReference₁ transport₁ crossDensity₁)
    (second : TransportDensityCertificate sourceAuxiliary₂
      destinationReference₂ transport₂ crossDensity₂)
    (hmeasurable₁ : ∀ x, Measurable (crossDensity₁ x))
    (hmeasurable₂ : ∀ x, Measurable (crossDensity₂ x)) :
    TransportDensityCertificate
      (fun x => (sourceAuxiliary₁ x).prod (sourceAuxiliary₂ x))
      (destinationReference₁.prod destinationReference₂)
      (fun x u => (transport₁ x u.1, transport₂ x u.2))
      (fun x y => crossDensity₁ x y.1 * crossDensity₂ x y.2) where
  measurableTransport x :=
    (first.measurableTransport x).comp measurable_fst |>.prodMk
      ((second.measurableTransport x).comp measurable_snd)
  pushforward_eq x := by
    rw [show (fun u : Aux₁ × Aux₂ =>
        (transport₁ x u.1, transport₂ x u.2)) =
      Prod.map (transport₁ x) (transport₂ x) by rfl]
    rw [← Measure.map_prod_map (sourceAuxiliary₁ x) (sourceAuxiliary₂ x)
      (first.measurableTransport x) (second.measurableTransport x),
      first.pushforward_eq x, second.pushforward_eq x]
    exact prod_withDensity (hmeasurable₁ x) (hmeasurable₂ x)

omit [MeasurableSpace Left] in
/-- A probability auxiliary law and a transport-density certificate imply
normalization of every claimed cross-model density. -/
theorem TransportDensityCertificate.lintegral_crossDensity_eq_one
    {Aux : Type*} [MeasurableSpace Aux]
    (sourceAuxiliary : Left → Measure Aux)
    (destinationReference : Measure Right)
    (transport : Left → Aux → Right)
    (crossDensity : Left → Right → ENNReal)
    (h : TransportDensityCertificate sourceAuxiliary destinationReference
      transport crossDensity)
    [∀ x, IsProbabilityMeasure (sourceAuxiliary x)] (x : Left) :
    ∫⁻ y, crossDensity x y ∂destinationReference = 1 := by
  calc
    (∫⁻ y, crossDensity x y ∂destinationReference) =
        destinationReference.withDensity (crossDensity x) Set.univ := by
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    _ = (sourceAuxiliary x).map (transport x) Set.univ := by
      rw [← h.pushforward_eq x]
    _ = sourceAuxiliary x Set.univ := by
      rw [Measure.map_apply_of_aemeasurable
        (h.measurableTransport x).aemeasurable MeasurableSet.univ]
      rfl
    _ = 1 := measure_univ

/-- A complete density-level reversible-jump specification.  Proposal
normalization is required for every tagged current state, and finite forward
flow excludes infinite density representatives from the accepted-flow proof. -/
structure ReversibleJumpSpec (reference : Measure (Left ⊕ Right))
    [SFinite reference] (weight : (Left ⊕ Right) → ENNReal) where
  proposalDensity : (Left ⊕ Right) → (Left ⊕ Right) → ENNReal
  measurableProposal : Measurable (Function.uncurry proposalDensity)
  normalized : ∀ x, ∫⁻ y, proposalDensity x y ∂reference = 1
  finiteFlow : ∀ x y, forwardDensityFlow weight proposalDensity x y ≠ ∞

/-- Reversible-jump MH obtained by applying density MH on the tagged space. -/
noncomputable def reversibleJumpMetropolisHastings
    (reference : Measure (Left ⊕ Right)) [SFinite reference]
    (weight : (Left ⊕ Right) → ENNReal)
    (spec : ReversibleJumpSpec reference weight) :
    Kernel (Left ⊕ Right) (Left ⊕ Right) :=
  densityMetropolisHastings reference weight spec.proposalDensity
    spec.measurableProposal spec.normalized

theorem reversibleJumpMetropolisHastings_isMarkov
    (reference : Measure (Left ⊕ Right)) [SFinite reference]
    (weight : (Left ⊕ Right) → ENNReal) (hweight : Measurable weight)
    (spec : ReversibleJumpSpec reference weight) :
    IsMarkovKernel (reversibleJumpMetropolisHastings reference weight spec) := by
  exact densityMetropolisHastings_isMarkov reference weight
    spec.proposalDensity hweight spec.measurableProposal spec.normalized

theorem reversibleJumpMetropolisHastings_isReversible
    (reference : Measure (Left ⊕ Right)) [SFinite reference]
    (weight : (Left ⊕ Right) → ENNReal) (hweight : Measurable weight)
    (spec : ReversibleJumpSpec reference weight) :
    (reversibleJumpMetropolisHastings reference weight spec).IsReversible
      (densityTarget reference weight) := by
  exact densityMetropolisHastings_isReversible reference weight
    spec.proposalDensity hweight spec.measurableProposal spec.normalized
    spec.finiteFlow

theorem reversibleJumpMetropolisHastings_invariant
    (reference : Measure (Left ⊕ Right)) [SFinite reference]
    (weight : (Left ⊕ Right) → ENNReal) (hweight : Measurable weight)
    (spec : ReversibleJumpSpec reference weight) :
    (reversibleJumpMetropolisHastings reference weight spec).Invariant
      (densityTarget reference weight) := by
  exact densityMetropolisHastings_invariant reference weight
    spec.proposalDensity hweight spec.measurableProposal spec.normalized
    spec.finiteFlow

omit [MeasurableSpace Left] [MeasurableSpace Right] in
/-- The accepted cross-model flow is the minimum of the forward and reverse
tagged proposal flows.  This is where a concrete RJ implementation's model
probabilities, auxiliary densities, and Jacobian-corrected transport density
enter the proof. -/
theorem reversibleJump_crossModel_acceptedFlow
    (weight : (Left ⊕ Right) → ENNReal)
    (proposalDensity : (Left ⊕ Right) → (Left ⊕ Right) → ENNReal)
    (x : Left) (y : Right) :
    symmetricAcceptedFlow weight proposalDensity (Sum.inl x) (Sum.inr y) =
      min (weight (Sum.inl x) * proposalDensity (Sum.inl x) (Sum.inr y))
        (weight (Sum.inr y) * proposalDensity (Sum.inr y) (Sum.inl x)) := by
  rfl

omit [MeasurableSpace Left] [MeasurableSpace Right] in
/-- Cross-model accepted flow is exactly symmetric under reversing the model
move, including zero forward or reverse proposal densities. -/
theorem reversibleJump_crossModel_acceptedFlow_symm
    (weight : (Left ⊕ Right) → ENNReal)
    (proposalDensity : (Left ⊕ Right) → (Left ⊕ Right) → ENNReal)
    (x : Left) (y : Right) :
    symmetricAcceptedFlow weight proposalDensity (Sum.inl x) (Sum.inr y) =
      symmetricAcceptedFlow weight proposalDensity (Sum.inr y) (Sum.inl x) := by
  exact (symmetricAcceptedFlow_swap weight proposalDensity _ _).symm

end Mcmc.Kernel
