import McmcLean.Kernel.MetropolisHastings

/-!
# Metropolis correction of deterministic proposals

This module specializes the general accepted-flow Metropolis construction to
a measurable deterministic proposal `T`.  It uses the zero-safe symmetric
accepted flow `min (w x) (w (T x))` and exposes the balance theorem required
for endpoint-corrected generalized HMC.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace McmcLean.Kernel

open ProbabilityTheory

variable {State : Type*} [MeasurableSpace State]

/-- Deterministic proposal kernel concentrated at `T x`. -/
noncomputable def deterministicProposal
    (T : State → State) (hT : Measurable T) : Kernel State State :=
  Kernel.deterministic T hT

instance deterministicProposal_isMarkov
    (T : State → State) (hT : Measurable T) :
    IsMarkovKernel (deterministicProposal T hT) := by
  unfold deterministicProposal
  infer_instance

theorem deterministicProposal_apply
    (T : State → State) (hT : Measurable T) (x : State) :
    deterministicProposal T hT x = Measure.dirac (T x) := by
  exact Kernel.deterministic_apply hT x

/-- Acceptance probability for a deterministic proposal, expressed through
the symmetric minimum of the current and proposed target weights. -/
noncomputable def deterministicAcceptance
    (weight : State → ℝ≥0∞) (T : State → State) (x : State) : ℝ≥0∞ :=
  min (weight x) (weight (T x)) / weight x

omit [MeasurableSpace State] in
theorem deterministicAcceptance_le_one
    (weight : State → ℝ≥0∞) (T : State → State) (x : State) :
    deterministicAcceptance weight T x ≤ 1 := by
  unfold deterministicAcceptance
  apply ENNReal.div_le_of_le_mul'
  simpa only [mul_one] using min_le_left (weight x) (weight (T x))

theorem measurable_deterministicAcceptance
    {weight : State → ℝ≥0∞} {T : State → State}
    (hweight : Measurable weight) (hT : Measurable T) :
    Measurable (deterministicAcceptance weight T) := by
  exact (hweight.min (hweight.comp hT)).div hweight

omit [MeasurableSpace State] in
/-- Multiplication by the current target weight recovers the symmetric
accepted flow. -/
theorem weight_mul_deterministicAcceptance
    (weight : State → ℝ≥0∞) (T : State → State)
    (hpositive : ∀ x, weight x ≠ 0)
    (hfinite : ∀ x, weight x ≠ ∞) (x : State) :
    weight x * deterministicAcceptance weight T x =
      min (weight x) (weight (T x)) := by
  exact ENNReal.mul_div_cancel (hpositive x) (hfinite x)

/-- Metropolis completion of a deterministic proposal. -/
noncomputable def deterministicMetropolis
    (weight : State → ℝ≥0∞) (T : State → State) (hT : Measurable T) :
    Kernel State State :=
  metropolisHastings (deterministicProposal T hT)
    (fun x _ => deterministicAcceptance weight T x)

theorem deterministicMetropolis_isMarkov
    (weight : State → ℝ≥0∞) (T : State → State)
    (hweight : Measurable weight) (hT : Measurable T) :
    IsMarkovKernel (deterministicMetropolis weight T hT) := by
  unfold deterministicMetropolis
  apply metropolisHastings_isMarkov
  · change Measurable fun p : State × State =>
      deterministicAcceptance weight T p.1
    exact (measurable_deterministicAcceptance hweight hT).comp measurable_fst
  · intro x y
    exact deterministicAcceptance_le_one weight T x

/-- Explicit transition row: accept the deterministic proposal with its
symmetric-flow probability and otherwise retain the current state. -/
theorem deterministicMetropolis_apply
    (weight : State → ℝ≥0∞) (T : State → State)
    (hweight : Measurable weight) (hT : Measurable T)
    (x : State) (s : Set State) (hs : MeasurableSet s) :
    deterministicMetropolis weight T hT x s =
      deterministicAcceptance weight T x * s.indicator 1 (T x) +
        (1 - deterministicAcceptance weight T x) * s.indicator 1 x := by
  classical
  let haccept : Measurable (Function.uncurry
      (fun x (_ : State) => deterministicAcceptance weight T x)) := by
    change Measurable fun p : State × State =>
      deterministicAcceptance weight T p.1
    exact (measurable_deterministicAcceptance hweight hT).comp measurable_fst
  letI : IsMarkovKernel (deterministicProposal T hT) := inferInstance
  rw [deterministicMetropolis,
    metropolisHastings_apply (deterministicProposal T hT)
      haccept x hs,
    deterministicProposal_apply]
  rw [setLIntegral_dirac' measurable_const hs]
  unfold rejectionProbability acceptanceMass
  rw [deterministicProposal_apply,
    lintegral_dirac' (T x)
      (Measurable.of_uncurry_left
        haccept)]
  by_cases hTx : T x ∈ s <;> simp [Set.indicator, hTx]

/-- The accepted deterministic subkernel has one atom at the proposed state. -/
theorem deterministicAcceptedKernel_apply
    (weight : State → ℝ≥0∞) (T : State → State)
    (hweight : Measurable weight) (hT : Measurable T)
    (x : State) (s : Set State) (hs : MeasurableSet s) :
    acceptedKernel (deterministicProposal T hT)
        (fun x _ => deterministicAcceptance weight T x) x s =
      deterministicAcceptance weight T x * s.indicator 1 (T x) := by
  classical
  let haccept : Measurable (Function.uncurry
      (fun x (_ : State) => deterministicAcceptance weight T x)) := by
    change Measurable fun p : State × State =>
      deterministicAcceptance weight T p.1
    exact (measurable_deterministicAcceptance hweight hT).comp measurable_fst
  rw [acceptedKernel, Kernel.withDensity_apply' _ haccept,
    deterministicProposal_apply, setLIntegral_dirac' measurable_const hs]
  by_cases hTx : T x ∈ s <;> simp [Set.indicator, hTx]

/-- The accepted flow of a deterministic involutive, measure-preserving
proposal is reversible with respect to the weighted reference measure. -/
theorem deterministicAcceptedKernel_isReversible
    (reference : Measure State) (weight : State → ℝ≥0∞)
    (T : State → State) (hT : Measurable T)
    (hweight : Measurable weight)
    (hpositive : ∀ x, weight x ≠ 0)
    (hfinite : ∀ x, weight x ≠ ∞)
    (hinvolutive : Function.Involutive T)
    (hpreserving : MeasurePreserving T reference reference) :
    (acceptedKernel (deterministicProposal T hT)
      (fun x _ => deterministicAcceptance weight T x)).IsReversible
        (reference.withDensity weight) := by
  let flow : State → ℝ≥0∞ := fun x => min (weight x) (weight (T x))
  have hflow : Measurable flow := hweight.min (hweight.comp hT)
  have hflowT (x : State) : flow (T x) = flow x := by
    simp only [flow, hinvolutive x, min_comm]
  intro A B hA hB
  rw [setLIntegral_withDensity_eq_setLIntegral_mul reference hweight
      ((acceptedKernel (deterministicProposal T hT)
        (fun x _ => deterministicAcceptance weight T x)).measurable_coe hB) hA,
    setLIntegral_withDensity_eq_setLIntegral_mul reference hweight
      ((acceptedKernel (deterministicProposal T hT)
        (fun x _ => deterministicAcceptance weight T x)).measurable_coe hA) hB]
  simp_rw [deterministicAcceptedKernel_apply weight T hweight hT _ B hB,
    deterministicAcceptedKernel_apply weight T hweight hT _ A hA]
  rw [← lintegral_indicator hA, ← lintegral_indicator hB]
  let reverseIntegrand : State → ℝ≥0∞ := fun x =>
    (B ∩ T ⁻¹' A).indicator flow x
  have hreverse : Measurable reverseIntegrand := by
    exact hflow.indicator (hB.inter (hT hA))
  have hrightIntegral :
      (∫⁻ x, B.indicator
        (weight * fun x => deterministicAcceptance weight T x *
          A.indicator 1 (T x)) x ∂reference) =
        ∫⁻ x, reverseIntegrand x ∂reference := by
    apply lintegral_congr
    intro x
    change B.indicator
        (fun x => weight x *
          (deterministicAcceptance weight T x * A.indicator 1 (T x))) x =
      reverseIntegrand x
    have hw : weight x * deterministicAcceptance weight T x = flow x := by
      exact weight_mul_deterministicAcceptance weight T hpositive hfinite x
    classical
    by_cases hxB : x ∈ B <;> by_cases hTxA : T x ∈ A <;>
      simp [reverseIntegrand, Set.indicator, hxB, hTxA, hw]
  rw [hrightIntegral]
  rw [← hpreserving.lintegral_comp hreverse]
  apply lintegral_congr
  intro x
  change A.indicator
      (fun x => weight x *
        (deterministicAcceptance weight T x * B.indicator 1 (T x))) x =
    reverseIntegrand (T x)
  have hw : weight x * deterministicAcceptance weight T x = flow x := by
    exact weight_mul_deterministicAcceptance weight T hpositive hfinite x
  classical
  by_cases hxA : x ∈ A <;> by_cases hTxB : T x ∈ B <;>
    simp [reverseIntegrand, Set.indicator, hxA, hTxB, hinvolutive x,
      hflowT, hw]

/-- Deterministic Metropolis correction is reversible under an involutive,
reference-measure-preserving proposal. -/
theorem deterministicMetropolis_isReversible
    (reference : Measure State) (weight : State → ℝ≥0∞)
    (T : State → State) (hT : Measurable T)
    (hweight : Measurable weight)
    (hpositive : ∀ x, weight x ≠ 0)
    (hfinite : ∀ x, weight x ≠ ∞)
    (hinvolutive : Function.Involutive T)
    (hpreserving : MeasurePreserving T reference reference) :
    (deterministicMetropolis weight T hT).IsReversible
      (reference.withDensity weight) := by
  unfold deterministicMetropolis
  apply metropolisHastings_isReversible
  · change Measurable fun p : State × State =>
      deterministicAcceptance weight T p.1
    exact (measurable_deterministicAcceptance hweight hT).comp measurable_fst
  · exact deterministicAcceptedKernel_isReversible reference weight T hT
      hweight hpositive hfinite hinvolutive hpreserving

/-- Deterministic Metropolis correction preserves the weighted target under
the same involution and reference-volume assumptions. -/
theorem deterministicMetropolis_invariant
    (reference : Measure State) (weight : State → ℝ≥0∞)
    (T : State → State) (hT : Measurable T)
    (hweight : Measurable weight)
    (hpositive : ∀ x, weight x ≠ 0)
    (hfinite : ∀ x, weight x ≠ ∞)
    (hinvolutive : Function.Involutive T)
    (hpreserving : MeasurePreserving T reference reference) :
    (deterministicMetropolis weight T hT).Invariant
      (reference.withDensity weight) := by
  letI : IsMarkovKernel (deterministicMetropolis weight T hT) :=
    deterministicMetropolis_isMarkov weight T hweight hT
  exact (deterministicMetropolis_isReversible reference weight T hT hweight
    hpositive hfinite hinvolutive hpreserving).invariant

end McmcLean.Kernel
