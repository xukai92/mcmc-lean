import Mathlib.Probability.Kernel.WithDensity
import Mcmc.Kernel.DetailedBalance

/-!
# General-state Metropolis--Hastings completion

This module constructs a Markov transition from a proposal kernel and a
measurable acceptance probability.  The accepted part is the proposal with
the acceptance function as density; the missing mass is placed at the current
state.  If the accepted flow is reversible, the completed transition is
reversible and hence preserves the target.

This is the measure-theoretic accepted-flow core used later for density-based
Metropolis--Hastings and random-walk Metropolis--Hastings.  It also defines the
zero-safe density-ratio acceptance rule and proves its pointwise symmetric-flow
identity; identifying its accepted joint law under a reference measure is the
next theorem layer.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace Mcmc.Kernel

open ProbabilityTheory

variable {State : Type*} [MeasurableSpace State]

/-- Unnormalized forward proposal flow for density-based MH. -/
noncomputable def forwardDensityFlow (weight : State → ENNReal)
    (proposalDensity : State → State → ENNReal) (x y : State) : ENNReal :=
  weight x * proposalDensity x y

/-- The symmetric accepted-flow density used by Metropolis--Hastings. -/
noncomputable def symmetricAcceptedFlow (weight : State → ENNReal)
    (proposalDensity : State → State → ENNReal) (x y : State) : ENNReal :=
  min (forwardDensityFlow weight proposalDensity x y)
    (forwardDensityFlow weight proposalDensity y x)

/-- Density-based MH acceptance probability.  A zero forward flow is rejected
explicitly, avoiding an ambiguous `0 / 0` acceptance ratio. -/
noncomputable def densityAcceptance (weight : State → ENNReal)
    (proposalDensity : State → State → ENNReal) (x y : State) : ENNReal :=
  if forwardDensityFlow weight proposalDensity x y = 0 then 0
  else symmetricAcceptedFlow weight proposalDensity x y /
    forwardDensityFlow weight proposalDensity x y

omit [MeasurableSpace State] in
theorem symmetricAcceptedFlow_swap (weight : State → ENNReal)
    (proposalDensity : State → State → ENNReal) (x y : State) :
    symmetricAcceptedFlow weight proposalDensity y x =
      symmetricAcceptedFlow weight proposalDensity x y := by
  simp [symmetricAcceptedFlow, min_comm]

omit [MeasurableSpace State] in
theorem densityAcceptance_le_one (weight : State → ENNReal)
    (proposalDensity : State → State → ENNReal) (x y : State) :
    densityAcceptance weight proposalDensity x y ≤ 1 := by
  rw [densityAcceptance]
  split_ifs with hzero
  · exact bot_le
  · apply ENNReal.div_le_of_le_mul'
    rw [symmetricAcceptedFlow]
    simpa only [mul_one] using min_le_left
      (forwardDensityFlow weight proposalDensity x y)
      (forwardDensityFlow weight proposalDensity y x)

omit [MeasurableSpace State] in
/-- Multiplying the acceptance probability by the forward density recovers
the symmetric accepted flow.  Finiteness excludes only pointwise infinite
density representatives; the zero-flow case is handled without division. -/
theorem forwardDensityFlow_mul_densityAcceptance
    (weight : State → ENNReal) (proposalDensity : State → State → ENNReal)
    (hfinite : ∀ x y, forwardDensityFlow weight proposalDensity x y ≠ ∞)
    (x y : State) :
    forwardDensityFlow weight proposalDensity x y *
        densityAcceptance weight proposalDensity x y =
      symmetricAcceptedFlow weight proposalDensity x y := by
  rw [densityAcceptance]
  split_ifs with hzero
  · rw [hzero, zero_mul]
    simp [symmetricAcceptedFlow, hzero]
  · exact ENNReal.mul_div_cancel hzero (hfinite x y)

theorem measurable_uncurry_forwardDensityFlow
    {weight : State → ENNReal} {proposalDensity : State → State → ENNReal}
    (hweight : Measurable weight)
    (hproposal : Measurable (Function.uncurry proposalDensity)) :
    Measurable (Function.uncurry (forwardDensityFlow weight proposalDensity)) := by
  exact (hweight.comp measurable_fst).mul hproposal

theorem measurable_uncurry_symmetricAcceptedFlow
    {weight : State → ENNReal} {proposalDensity : State → State → ENNReal}
    (hweight : Measurable weight)
    (hproposal : Measurable (Function.uncurry proposalDensity)) :
    Measurable (Function.uncurry (symmetricAcceptedFlow weight proposalDensity)) := by
  have hforward := measurable_uncurry_forwardDensityFlow hweight hproposal
  exact hforward.min (hforward.comp measurable_swap)

theorem measurable_uncurry_densityAcceptance
    {weight : State → ENNReal} {proposalDensity : State → State → ENNReal}
    (hweight : Measurable weight)
    (hproposal : Measurable (Function.uncurry proposalDensity)) :
    Measurable (Function.uncurry (densityAcceptance weight proposalDensity)) := by
  have hforward := measurable_uncurry_forwardDensityFlow hweight hproposal
  have hflow := measurable_uncurry_symmetricAcceptedFlow hweight hproposal
  rw [show Function.uncurry (densityAcceptance weight proposalDensity) =
      fun p => if Function.uncurry (forwardDensityFlow weight proposalDensity) p = 0
        then 0 else Function.uncurry (symmetricAcceptedFlow weight proposalDensity) p /
          Function.uncurry (forwardDensityFlow weight proposalDensity) p by rfl]
  apply Measurable.ite
  · exact hforward (measurableSet_singleton 0)
  · exact measurable_const
  · exact hflow.div hforward

/-- A target measure represented by a density with respect to a common
reference measure. -/
noncomputable def densityTarget (reference : Measure State)
    (weight : State → ENNReal) : Measure State :=
  reference.withDensity weight

/-- A proposal kernel represented by transition densities with respect to a
common reference measure. -/
noncomputable def densityProposal (reference : Measure State) [SFinite reference]
    (proposalDensity : State → State → ENNReal) :
    ProbabilityTheory.Kernel State State :=
  (ProbabilityTheory.Kernel.const State reference).withDensity proposalDensity

theorem densityProposal_apply (reference : Measure State) [SFinite reference]
    {proposalDensity : State → State → ENNReal}
    (hproposal : Measurable (Function.uncurry proposalDensity))
    (x : State) {s : Set State} (_hs : MeasurableSet s) :
    densityProposal reference proposalDensity x s =
      ∫⁻ y in s, proposalDensity x y ∂reference := by
  rw [densityProposal, ProbabilityTheory.Kernel.withDensity_apply'
    _ hproposal, ProbabilityTheory.Kernel.const_apply]

/-- Integrating an observable against a density proposal is integration
against its row density with respect to the reference measure. -/
theorem lintegral_densityProposal
    (reference : Measure State) [SFinite reference]
    {proposalDensity : State → State → ENNReal}
    (hproposal : Measurable (Function.uncurry proposalDensity))
    {f : State → ENNReal} (hf : Measurable f) (x : State) :
    (∫⁻ y, f y ∂densityProposal reference proposalDensity x) =
      ∫⁻ y, proposalDensity x y * f y ∂reference := by
  rw [densityProposal, ProbabilityTheory.Kernel.withDensity_apply _ hproposal,
    ProbabilityTheory.Kernel.const_apply,
    lintegral_withDensity_eq_lintegral_mul _
      (Measurable.of_uncurry_left hproposal) hf]
  rfl

/-- Pointwise normalization of proposal densities makes the density proposal
a Markov kernel. -/
theorem densityProposal_isMarkov (reference : Measure State) [SFinite reference]
    {proposalDensity : State → State → ENNReal}
    (hproposal : Measurable (Function.uncurry proposalDensity))
    (hnorm : ∀ x, ∫⁻ y, proposalDensity x y ∂reference = 1) :
    IsMarkovKernel (densityProposal reference proposalDensity) := by
  constructor
  intro x
  constructor
  rw [densityProposal_apply reference hproposal x MeasurableSet.univ,
    Measure.restrict_univ, hnorm]

/-- Normalizing the target density makes its with-density measure a
probability measure. -/
theorem densityTarget_isProbability (reference : Measure State)
    (weight : State → ENNReal)
    (hnorm : ∫⁻ x, weight x ∂reference = 1) :
    IsProbabilityMeasure (densityTarget reference weight) := by
  constructor
  rw [densityTarget, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, hnorm]

/-- The sub-Markov kernel carrying accepted proposals. -/
noncomputable def acceptedKernel (Q : ProbabilityTheory.Kernel State State)
    [IsSFiniteKernel Q] (accept : State → State → ENNReal) :
    ProbabilityTheory.Kernel State State :=
  Q.withDensity accept

/-- The accepted kernel for normalized proposal densities.  The normalization
proof supplies the s-finiteness instance required by `Kernel.withDensity`. -/
noncomputable def densityAcceptedKernel
    (reference : Measure State) [SFinite reference]
    (weight : State → ENNReal) (proposalDensity : State → State → ENNReal)
    (hproposal : Measurable (Function.uncurry proposalDensity))
    (hproposalNorm : ∀ x, ∫⁻ y, proposalDensity x y ∂reference = 1) :
    ProbabilityTheory.Kernel State State := by
  letI : IsMarkovKernel (densityProposal reference proposalDensity) :=
    densityProposal_isMarkov reference hproposal hproposalNorm
  exact acceptedKernel (densityProposal reference proposalDensity)
    (densityAcceptance weight proposalDensity)

/-- Under a common reference measure, density-ratio MH has a reversible
accepted flow: both directions have density equal to the same pointwise
minimum. -/
theorem densityAcceptedKernel_isReversible
    (reference : Measure State) [SFinite reference]
    (weight : State → ENNReal) (proposalDensity : State → State → ENNReal)
    (hweight : Measurable weight)
    (hproposal : Measurable (Function.uncurry proposalDensity))
    (hproposalNorm : ∀ x, ∫⁻ y, proposalDensity x y ∂reference = 1)
    (hfinite : ∀ x y, forwardDensityFlow weight proposalDensity x y ≠ ∞) :
    (densityAcceptedKernel reference weight proposalDensity hproposal
      hproposalNorm).IsReversible
        (densityTarget reference weight) := by
  let Q := densityProposal reference proposalDensity
  let accept := densityAcceptance weight proposalDensity
  letI : IsMarkovKernel Q := densityProposal_isMarkov reference hproposal hproposalNorm
  change (acceptedKernel Q accept).IsReversible (densityTarget reference weight)
  have haccept : Measurable (Function.uncurry accept) :=
    measurable_uncurry_densityAcceptance hweight hproposal
  have hacceptedApply (x : State) {s : Set State} (hs : MeasurableSet s) :
      acceptedKernel Q accept x s =
        ∫⁻ y in s, proposalDensity x y * accept x y ∂reference := by
    rw [acceptedKernel, ProbabilityTheory.Kernel.withDensity_apply' Q haccept x s]
    change ∫⁻ y in s, accept x y ∂(densityProposal reference proposalDensity x) = _
    rw [densityProposal, ProbabilityTheory.Kernel.withDensity_apply _ hproposal,
      ProbabilityTheory.Kernel.const_apply,
      setLIntegral_withDensity_eq_setLIntegral_mul reference
        (Measurable.of_uncurry_left hproposal)
        (Measurable.of_uncurry_left haccept) hs]
    congr 1
  intro A B hA hB
  rw [densityTarget,
    setLIntegral_withDensity_eq_setLIntegral_mul reference hweight
      ((acceptedKernel Q accept).measurable_coe hB) hA,
    setLIntegral_withDensity_eq_setLIntegral_mul reference hweight
      ((acceptedKernel Q accept).measurable_coe hA) hB]
  simp only [Pi.mul_apply]
  simp_rw [hacceptedApply _ hB]
  simp_rw [hacceptedApply _ hA]
  have hflowMeas : Measurable
      (Function.uncurry (symmetricAcceptedFlow weight proposalDensity)) :=
    measurable_uncurry_symmetricAcceptedFlow hweight hproposal
  calc
    (∫⁻ x in A, weight x *
        (∫⁻ y in B, proposalDensity x y * accept x y ∂reference) ∂reference) =
        ∫⁻ x in A, ∫⁻ y in B,
          weight x * (proposalDensity x y * accept x y) ∂reference ∂reference := by
      congr 1
      funext x
      exact (lintegral_const_mul (μ := reference.restrict B) (weight x)
        ((Measurable.of_uncurry_left hproposal).mul
          (Measurable.of_uncurry_left haccept))).symm
    _ = ∫⁻ x in A, ∫⁻ y in B,
          symmetricAcceptedFlow weight proposalDensity x y ∂reference ∂reference := by
      apply setLIntegral_congr_fun hA
      intro x _
      apply setLIntegral_congr_fun hB
      intro y _
      change weight x * (proposalDensity x y * accept x y) = _
      rw [← mul_assoc, ← forwardDensityFlow,
        forwardDensityFlow_mul_densityAcceptance weight proposalDensity hfinite]
    _ = ∫⁻ z in A ×ˢ B,
          Function.uncurry (symmetricAcceptedFlow weight proposalDensity) z
          ∂reference.prod reference := by
      rw [setLIntegral_prod _ hflowMeas.aemeasurable]
      rfl
    _ = ∫⁻ x in B, ∫⁻ y in A,
          symmetricAcceptedFlow weight proposalDensity x y ∂reference ∂reference := by
      rw [setLIntegral_prod_symm _ hflowMeas.aemeasurable]
      apply setLIntegral_congr_fun hB
      intro x _
      apply setLIntegral_congr_fun hA
      intro y _
      exact symmetricAcceptedFlow_swap weight proposalDensity x y
    _ = ∫⁻ x in B, weight x *
        (∫⁻ y in A, proposalDensity x y * accept x y ∂reference) ∂reference := by
      apply setLIntegral_congr_fun hB
      intro x _
      change (∫⁻ y in A, symmetricAcceptedFlow weight proposalDensity x y ∂reference) =
        weight x * (∫⁻ y in A, proposalDensity x y * accept x y ∂reference)
      calc
        (∫⁻ y in A, symmetricAcceptedFlow weight proposalDensity x y ∂reference) =
            ∫⁻ y in A, weight x * (proposalDensity x y * accept x y) ∂reference := by
          apply setLIntegral_congr_fun hA
          intro y _
          change symmetricAcceptedFlow weight proposalDensity x y =
            weight x * (proposalDensity x y * accept x y)
          rw [← mul_assoc, ← forwardDensityFlow,
            forwardDensityFlow_mul_densityAcceptance weight proposalDensity hfinite]
        _ = weight x *
            (∫⁻ y in A, proposalDensity x y * accept x y ∂reference) :=
          lintegral_const_mul (μ := reference.restrict A) (weight x)
            ((Measurable.of_uncurry_left hproposal).mul
              (Measurable.of_uncurry_left haccept))

/-- Total proposal mass accepted from `x`. -/
noncomputable def acceptanceMass (Q : ProbabilityTheory.Kernel State State)
    (accept : State → State → ENNReal) (x : State) : ENNReal :=
  ∫⁻ y, accept x y ∂Q x

/-- Probability of rejecting and retaining the current state. -/
noncomputable def rejectionProbability (Q : ProbabilityTheory.Kernel State State)
    (accept : State → State → ENNReal) (x : State) : ENNReal :=
  1 - acceptanceMass Q accept x

/-- The rejected mass, placed at the current state. -/
noncomputable def rejectionKernel (Q : ProbabilityTheory.Kernel State State)
    [IsSFiniteKernel Q] (accept : State → State → ENNReal) :
    ProbabilityTheory.Kernel State State :=
  ProbabilityTheory.Kernel.id.withDensity
    (fun x _ => rejectionProbability Q accept x)

/-- Metropolis--Hastings completion of an accepted proposal flow. -/
noncomputable def metropolisHastings (Q : ProbabilityTheory.Kernel State State)
    [IsSFiniteKernel Q] (accept : State → State → ENNReal) :
    ProbabilityTheory.Kernel State State :=
  acceptedKernel Q accept + rejectionKernel Q accept

theorem measurable_acceptanceMass (Q : ProbabilityTheory.Kernel State State)
    [IsSFiniteKernel Q] {accept : State → State → ENNReal}
    (haccept : Measurable (Function.uncurry accept)) :
    Measurable (acceptanceMass Q accept) := by
  exact haccept.lintegral_kernel_prod_right

theorem measurable_rejectionProbability (Q : ProbabilityTheory.Kernel State State)
    [IsSFiniteKernel Q] {accept : State → State → ENNReal}
    (haccept : Measurable (Function.uncurry accept)) :
    Measurable (rejectionProbability Q accept) := by
  exact measurable_const.sub (measurable_acceptanceMass Q haccept)

theorem measurable_uncurry_rejectionProbability
    (Q : ProbabilityTheory.Kernel State State) [IsSFiniteKernel Q]
    {accept : State → State → ENNReal}
    (haccept : Measurable (Function.uncurry accept)) :
    Measurable (Function.uncurry
      (fun x (_ : State) => rejectionProbability Q accept x)) := by
  exact (measurable_rejectionProbability Q haccept).comp measurable_fst

theorem acceptanceMass_le_one (Q : ProbabilityTheory.Kernel State State)
    [IsMarkovKernel Q] {accept : State → State → ENNReal}
    (hle : ∀ x y, accept x y ≤ 1) (x : State) :
    acceptanceMass Q accept x ≤ 1 := by
  calc
    acceptanceMass Q accept x ≤ ∫⁻ _y, (1 : ENNReal) ∂Q x :=
      lintegral_mono (hle x)
    _ = 1 := by simp

theorem metropolisHastings_apply
    (Q : ProbabilityTheory.Kernel State State) [IsMarkovKernel Q]
    {accept : State → State → ENNReal}
    (haccept : Measurable (Function.uncurry accept))
    (x : State) {s : Set State} (hs : MeasurableSet s) :
    metropolisHastings Q accept x s =
      (∫⁻ y in s, accept x y ∂Q x) +
        rejectionProbability Q accept x * s.indicator 1 x := by
  classical
  rw [metropolisHastings, acceptedKernel, rejectionKernel,
    ProbabilityTheory.Kernel.coe_add, Pi.add_apply, Measure.coe_add,
    Pi.add_apply, ProbabilityTheory.Kernel.withDensity_apply' Q haccept x s,
    ProbabilityTheory.Kernel.withDensity_apply'
      ProbabilityTheory.Kernel.id
      (measurable_uncurry_rejectionProbability Q haccept) x s,
    ProbabilityTheory.Kernel.id_apply]
  rw [setLIntegral_dirac' measurable_const hs]
  by_cases hx : x ∈ s <;> simp [hx]

/-- Completing an acceptance function bounded by one produces a Markov
kernel. -/
theorem metropolisHastings_isMarkov
    (Q : ProbabilityTheory.Kernel State State) [IsMarkovKernel Q]
    {accept : State → State → ENNReal}
    (haccept : Measurable (Function.uncurry accept))
    (hle : ∀ x y, accept x y ≤ 1) :
    IsMarkovKernel (metropolisHastings Q accept) := by
  constructor
  intro x
  constructor
  rw [metropolisHastings_apply Q haccept x MeasurableSet.univ]
  simp only [Set.indicator_of_mem (Set.mem_univ x), Pi.one_apply]
  rw [rejectionProbability]
  simp only [Measure.restrict_univ, mul_one]
  change acceptanceMass Q accept x + (1 - acceptanceMass Q accept x) = 1
  simpa [add_comm] using tsub_add_cancel_of_le (acceptanceMass_le_one Q hle x)

/-- Metropolis--Hastings cannot increase a nonnegative observable by more
than the full proposal contribution plus one retained copy of its current
value.  This deliberately coarse bound is useful for proving the RWMH growth
premise in Xu et al.; it is independent of the target density. -/
theorem lintegral_metropolisHastings_le_proposal_add
    (Q : ProbabilityTheory.Kernel State State) [IsMarkovKernel Q]
    {accept : State → State → ENNReal}
    (haccept : Measurable (Function.uncurry accept))
    (hle : ∀ x y, accept x y ≤ 1)
    {f : State → ENNReal} (hf : Measurable f) (x : State) :
    (∫⁻ y, f y ∂metropolisHastings Q accept x) ≤
      (∫⁻ y, f y ∂Q x) + f x := by
  rw [metropolisHastings, ProbabilityTheory.Kernel.coe_add, Pi.add_apply,
    lintegral_add_measure]
  apply add_le_add
  · rw [acceptedKernel, ProbabilityTheory.Kernel.withDensity_apply _ haccept,
      lintegral_withDensity_eq_lintegral_mul _
        (Measurable.of_uncurry_left haccept) hf]
    apply lintegral_mono
    intro y
    change accept x y * f y ≤ f y
    calc
      accept x y * f y ≤ 1 * f y := by gcongr; exact hle x y
      _ = f y := one_mul _
  · rw [rejectionKernel, ProbabilityTheory.Kernel.withDensity_apply _
      (measurable_uncurry_rejectionProbability Q haccept),
      ProbabilityTheory.Kernel.id_apply,
      lintegral_withDensity_eq_lintegral_mul _ measurable_const hf,
      lintegral_dirac' x (measurable_const.mul hf)]
    change rejectionProbability Q accept x * f x ≤ f x
    calc
      rejectionProbability Q accept x * f x ≤ 1 * f x := by
        gcongr
        exact tsub_le_self
      _ = f x := one_mul _

theorem rejectionKernel_apply
    (Q : ProbabilityTheory.Kernel State State) [IsMarkovKernel Q]
    {accept : State → State → ENNReal}
    (haccept : Measurable (Function.uncurry accept))
    (x : State) {s : Set State} (hs : MeasurableSet s) :
    rejectionKernel Q accept x s =
      rejectionProbability Q accept x * s.indicator 1 x := by
  classical
  rw [rejectionKernel, ProbabilityTheory.Kernel.withDensity_apply'
      ProbabilityTheory.Kernel.id
      (measurable_uncurry_rejectionProbability Q haccept) x s,
    ProbabilityTheory.Kernel.id_apply,
    setLIntegral_dirac' measurable_const hs]
  by_cases hx : x ∈ s <;> simp [hx]

/-- A rejection kernel carries only diagonal flow and is therefore reversible
with respect to every measure. -/
theorem rejectionKernel_isReversible
    (π : Measure State)
    (Q : ProbabilityTheory.Kernel State State) [IsMarkovKernel Q]
    {accept : State → State → ENNReal}
    (haccept : Measurable (Function.uncurry accept)) :
    (rejectionKernel Q accept).IsReversible π := by
  intro A B hA hB
  simp_rw [rejectionKernel_apply Q haccept _ hB]
  have hleft :
      (fun x => rejectionProbability Q accept x * B.indicator 1 x) =
        B.indicator (rejectionProbability Q accept) := by
    funext x
    classical
    by_cases hx : x ∈ B <;> simp [hx]
  rw [hleft, setLIntegral_indicator hB]
  simp_rw [rejectionKernel_apply Q haccept _ hA]
  have hright :
      (fun x => rejectionProbability Q accept x * A.indicator 1 x) =
        A.indicator (rejectionProbability Q accept) := by
    funext x
    classical
    by_cases hx : x ∈ A <;> simp [hx]
  rw [hright, setLIntegral_indicator hA, Set.inter_comm]

/-- The sum of two reversible (possibly sub-Markov) kernels is reversible. -/
theorem isReversible_add
    {κ η : ProbabilityTheory.Kernel State State} {π : Measure State}
    (hκ : κ.IsReversible π) (hη : η.IsReversible π) :
    (κ + η).IsReversible π := by
  intro A B hA hB
  simp only [ProbabilityTheory.Kernel.coe_add, Pi.add_apply, Measure.coe_add,
    Pi.add_apply]
  rw [lintegral_add_left (κ.measurable_coe hB),
    lintegral_add_left (κ.measurable_coe hA), hκ hA hB, hη hA hB]

/-- Symmetry of the accepted flow implies detailed balance for the completed
Metropolis--Hastings transition. -/
theorem metropolisHastings_isReversible
    (π : Measure State)
    (Q : ProbabilityTheory.Kernel State State) [IsMarkovKernel Q]
    {accept : State → State → ENNReal}
    (haccept : Measurable (Function.uncurry accept))
    (haccepted : (acceptedKernel Q accept).IsReversible π) :
    (metropolisHastings Q accept).IsReversible π := by
  exact isReversible_add haccepted (rejectionKernel_isReversible π Q haccept)

/-- A measurable, bounded acceptance rule with symmetric accepted flow leaves
the target invariant. -/
theorem metropolisHastings_invariant
    (π : Measure State)
    (Q : ProbabilityTheory.Kernel State State) [IsMarkovKernel Q]
    {accept : State → State → ENNReal}
    (haccept : Measurable (Function.uncurry accept))
    (hle : ∀ x y, accept x y ≤ 1)
    (haccepted : (acceptedKernel Q accept).IsReversible π) :
    (metropolisHastings Q accept).Invariant π := by
  letI : IsMarkovKernel (metropolisHastings Q accept) :=
    metropolisHastings_isMarkov Q haccept hle
  exact (metropolisHastings_isReversible π Q haccept haccepted).invariant

/-- The density-based Metropolis--Hastings transition built from a normalized
proposal density and the zero-safe symmetric-flow acceptance rule. -/
noncomputable def densityMetropolisHastings
    (reference : Measure State) [SFinite reference]
    (weight : State → ENNReal) (proposalDensity : State → State → ENNReal)
    (hproposal : Measurable (Function.uncurry proposalDensity))
    (hproposalNorm : ∀ x, ∫⁻ y, proposalDensity x y ∂reference = 1) :
    ProbabilityTheory.Kernel State State := by
  letI : IsMarkovKernel (densityProposal reference proposalDensity) :=
    densityProposal_isMarkov reference hproposal hproposalNorm
  exact metropolisHastings (densityProposal reference proposalDensity)
    (densityAcceptance weight proposalDensity)

/-- Density-based MH is a Markov kernel. -/
theorem densityMetropolisHastings_isMarkov
    (reference : Measure State) [SFinite reference]
    (weight : State → ENNReal) (proposalDensity : State → State → ENNReal)
    (hweight : Measurable weight)
    (hproposal : Measurable (Function.uncurry proposalDensity))
    (hproposalNorm : ∀ x, ∫⁻ y, proposalDensity x y ∂reference = 1) :
    IsMarkovKernel
      (densityMetropolisHastings reference weight proposalDensity hproposal
        hproposalNorm) := by
  let Q := densityProposal reference proposalDensity
  let accept := densityAcceptance weight proposalDensity
  letI : IsMarkovKernel Q := densityProposal_isMarkov reference hproposal hproposalNorm
  change IsMarkovKernel (metropolisHastings Q accept)
  exact metropolisHastings_isMarkov Q
    (measurable_uncurry_densityAcceptance hweight hproposal)
    (densityAcceptance_le_one weight proposalDensity)

/-- Coarse observable growth bound for density-based MH.  Accepted moves are
dominated by the entire proposal row, and rejected moves retain the current
observable value. -/
theorem lintegral_densityMetropolisHastings_le_proposal_add
    (reference : Measure State) [SFinite reference]
    (weight : State → ENNReal) (proposalDensity : State → State → ENNReal)
    (hweight : Measurable weight)
    (hproposal : Measurable (Function.uncurry proposalDensity))
    (hproposalNorm : ∀ x, ∫⁻ y, proposalDensity x y ∂reference = 1)
    {f : State → ENNReal} (hf : Measurable f) (x : State) :
    (∫⁻ y, f y ∂densityMetropolisHastings reference weight proposalDensity
        hproposal hproposalNorm x) ≤
      (∫⁻ y, proposalDensity x y * f y ∂reference) + f x := by
  let Q := densityProposal reference proposalDensity
  letI : IsMarkovKernel Q := densityProposal_isMarkov reference hproposal hproposalNorm
  have hbound := lintegral_metropolisHastings_le_proposal_add Q
    (measurable_uncurry_densityAcceptance hweight hproposal)
    (densityAcceptance_le_one weight proposalDensity) hf x
  rw [lintegral_densityProposal reference hproposal hf x] at hbound
  simpa only [densityMetropolisHastings, Q] using hbound

/-- Density-based MH satisfies detailed balance with respect to its target
density. -/
theorem densityMetropolisHastings_isReversible
    (reference : Measure State) [SFinite reference]
    (weight : State → ENNReal) (proposalDensity : State → State → ENNReal)
    (hweight : Measurable weight)
    (hproposal : Measurable (Function.uncurry proposalDensity))
    (hproposalNorm : ∀ x, ∫⁻ y, proposalDensity x y ∂reference = 1)
    (hfinite : ∀ x y, forwardDensityFlow weight proposalDensity x y ≠ ∞) :
    (densityMetropolisHastings reference weight proposalDensity hproposal
      hproposalNorm).IsReversible (densityTarget reference weight) := by
  let Q := densityProposal reference proposalDensity
  let accept := densityAcceptance weight proposalDensity
  letI : IsMarkovKernel Q := densityProposal_isMarkov reference hproposal hproposalNorm
  change (metropolisHastings Q accept).IsReversible (densityTarget reference weight)
  apply metropolisHastings_isReversible
    (densityTarget reference weight) Q
    (measurable_uncurry_densityAcceptance hweight hproposal)
  change (densityAcceptedKernel reference weight proposalDensity hproposal
    hproposalNorm).IsReversible (densityTarget reference weight)
  exact densityAcceptedKernel_isReversible reference weight proposalDensity
    hweight hproposal hproposalNorm hfinite

/-- Density-based MH preserves the measure represented by its target density.
When the density integrates to one, `densityTarget_isProbability` additionally
identifies this invariant measure as a probability measure. -/
theorem densityMetropolisHastings_invariant
    (reference : Measure State) [SFinite reference]
    (weight : State → ENNReal) (proposalDensity : State → State → ENNReal)
    (hweight : Measurable weight)
    (hproposal : Measurable (Function.uncurry proposalDensity))
    (hproposalNorm : ∀ x, ∫⁻ y, proposalDensity x y ∂reference = 1)
    (hfinite : ∀ x y, forwardDensityFlow weight proposalDensity x y ≠ ∞) :
    (densityMetropolisHastings reference weight proposalDensity hproposal
      hproposalNorm).Invariant (densityTarget reference weight) := by
  letI : IsMarkovKernel
      (densityMetropolisHastings reference weight proposalDensity hproposal
        hproposalNorm) :=
    densityMetropolisHastings_isMarkov reference weight proposalDensity
      hweight hproposal hproposalNorm
  exact (densityMetropolisHastings_isReversible reference weight proposalDensity
    hweight hproposal hproposalNorm hfinite).invariant

end Mcmc.Kernel
