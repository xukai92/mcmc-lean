import Mcmc.Kernel.MetropolisHastings

/-!
# Barker's acceptance rule for density-based Metropolis--Hastings

This module defines the Barker (1965) acceptance function and proves that the
resulting Metropolis--Hastings transition is reversible and preserves the target
measure.  The accepted flow `a·b/(a+b)` (harmonic-mean form) is manifestly
symmetric; it replaces the min-based flow of the standard MH rule.

The Barker acceptance is always ≤ the standard MH acceptance (harmonic mean ≤
minimum), so the Barker kernel accepts less often but has a differentiable
acceptance function in the density ratio.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace Mcmc.Kernel

open ProbabilityTheory

variable {State : Type*} [MeasurableSpace State]

/-- Barker's accepted flow: the product-over-sum (harmonic) form of the
pairwise flow density.  For `a = forwardDensityFlow x y` and
`b = forwardDensityFlow y x`, this is `a·b/(a+b)`. -/
noncomputable def barkerAcceptedFlow (weight : State → ENNReal)
    (proposalDensity : State → State → ENNReal) (x y : State) : ENNReal :=
  forwardDensityFlow weight proposalDensity x y *
    forwardDensityFlow weight proposalDensity y x /
      (forwardDensityFlow weight proposalDensity x y +
        forwardDensityFlow weight proposalDensity y x)

/-- Barker's acceptance probability.  When the forward flow is zero, the
proposal is rejected outright; otherwise the acceptance is the reverse flow
fraction of the total bilateral flow. -/
noncomputable def barkerDensityAcceptance (weight : State → ENNReal)
    (proposalDensity : State → State → ENNReal) (x y : State) : ENNReal :=
  if forwardDensityFlow weight proposalDensity x y = 0 then 0
  else forwardDensityFlow weight proposalDensity y x /
    (forwardDensityFlow weight proposalDensity x y +
      forwardDensityFlow weight proposalDensity y x)

omit [MeasurableSpace State] in
/-- The Barker accepted flow is symmetric: `a·b/(a+b)` is invariant under
swapping `a` and `b`. -/
theorem barkerAcceptedFlow_swap (weight : State → ENNReal)
    (proposalDensity : State → State → ENNReal) (x y : State) :
    barkerAcceptedFlow weight proposalDensity y x =
      barkerAcceptedFlow weight proposalDensity x y := by
  simp [barkerAcceptedFlow, mul_comm, add_comm]

omit [MeasurableSpace State] in
/-- The Barker acceptance probability is at most one. -/
theorem barkerDensityAcceptance_le_one (weight : State → ENNReal)
    (proposalDensity : State → State → ENNReal) (x y : State) :
    barkerDensityAcceptance weight proposalDensity x y ≤ 1 := by
  rw [barkerDensityAcceptance]
  split_ifs with hzero
  · exact bot_le
  · apply ENNReal.div_le_of_le_mul'
    simpa only [mul_one] using le_add_left le_rfl

omit [MeasurableSpace State] in
/-- Multiplying the forward density flow by the Barker acceptance probability
recovers the Barker accepted flow.  Unlike the standard MH analogue, no
finiteness hypothesis is needed: the identity is purely algebraic. -/
theorem forwardDensityFlow_mul_barkerDensityAcceptance
    (weight : State → ENNReal) (proposalDensity : State → State → ENNReal)
    (x y : State) :
    forwardDensityFlow weight proposalDensity x y *
        barkerDensityAcceptance weight proposalDensity x y =
      barkerAcceptedFlow weight proposalDensity x y := by
  rw [barkerDensityAcceptance]
  split_ifs with hzero
  · rw [hzero, zero_mul]
    simp [barkerAcceptedFlow, hzero]
  · rw [barkerAcceptedFlow, div_eq_mul_inv, div_eq_mul_inv, mul_assoc]

/-- The uncurried Barker accepted flow is measurable. -/
theorem measurable_uncurry_barkerAcceptedFlow
    {weight : State → ENNReal} {proposalDensity : State → State → ENNReal}
    (hweight : Measurable weight)
    (hproposal : Measurable (Function.uncurry proposalDensity)) :
    Measurable (Function.uncurry (barkerAcceptedFlow weight proposalDensity)) := by
  have hforward := measurable_uncurry_forwardDensityFlow hweight hproposal
  have hreverse := hforward.comp measurable_swap
  exact (hforward.mul hreverse).div (hforward.add hreverse)

/-- The uncurried Barker acceptance probability is measurable. -/
theorem measurable_uncurry_barkerDensityAcceptance
    {weight : State → ENNReal} {proposalDensity : State → State → ENNReal}
    (hweight : Measurable weight)
    (hproposal : Measurable (Function.uncurry proposalDensity)) :
    Measurable (Function.uncurry (barkerDensityAcceptance weight proposalDensity)) := by
  have hforward := measurable_uncurry_forwardDensityFlow hweight hproposal
  have hreverse := hforward.comp measurable_swap
  rw [show Function.uncurry (barkerDensityAcceptance weight proposalDensity) =
      fun p => if Function.uncurry (forwardDensityFlow weight proposalDensity) p = 0
        then 0 else Function.uncurry (forwardDensityFlow weight proposalDensity)
          (p.2, p.1) /
          (Function.uncurry (forwardDensityFlow weight proposalDensity) p +
            Function.uncurry (forwardDensityFlow weight proposalDensity)
              (p.2, p.1)) by rfl]
  apply Measurable.ite
  · exact hforward (measurableSet_singleton 0)
  · exact measurable_const
  · exact hreverse.div (hforward.add hreverse)

/-- The sub-Markov kernel of accepted Barker proposals. -/
noncomputable def barkerDensityAcceptedKernel
    (reference : Measure State) [SFinite reference]
    (weight : State → ENNReal) (proposalDensity : State → State → ENNReal)
    (hproposal : Measurable (Function.uncurry proposalDensity))
    (hproposalNorm : ∀ x, ∫⁻ y, proposalDensity x y ∂reference = 1) :
    ProbabilityTheory.Kernel State State := by
  letI : IsMarkovKernel (densityProposal reference proposalDensity) :=
    densityProposal_isMarkov reference hproposal hproposalNorm
  exact acceptedKernel (densityProposal reference proposalDensity)
    (barkerDensityAcceptance weight proposalDensity)

/-- Under a common reference measure, Barker's density-ratio acceptance has a
reversible accepted flow: both directions have density equal to the same
product-over-sum accepted flow. -/
theorem barkerDensityAcceptedKernel_isReversible
    (reference : Measure State) [SFinite reference]
    (weight : State → ENNReal) (proposalDensity : State → State → ENNReal)
    (hweight : Measurable weight)
    (hproposal : Measurable (Function.uncurry proposalDensity))
    (hproposalNorm : ∀ x, ∫⁻ y, proposalDensity x y ∂reference = 1) :
    (barkerDensityAcceptedKernel reference weight proposalDensity hproposal
      hproposalNorm).IsReversible
        (densityTarget reference weight) := by
  let Q := densityProposal reference proposalDensity
  let accept := barkerDensityAcceptance weight proposalDensity
  letI : IsMarkovKernel Q := densityProposal_isMarkov reference hproposal hproposalNorm
  change (acceptedKernel Q accept).IsReversible (densityTarget reference weight)
  have haccept : Measurable (Function.uncurry accept) :=
    measurable_uncurry_barkerDensityAcceptance hweight hproposal
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
      (Function.uncurry (barkerAcceptedFlow weight proposalDensity)) :=
    measurable_uncurry_barkerAcceptedFlow hweight hproposal
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
          barkerAcceptedFlow weight proposalDensity x y ∂reference ∂reference := by
      apply setLIntegral_congr_fun hA
      intro x _
      apply setLIntegral_congr_fun hB
      intro y _
      change weight x * (proposalDensity x y * accept x y) = _
      rw [← mul_assoc, ← forwardDensityFlow,
        forwardDensityFlow_mul_barkerDensityAcceptance weight proposalDensity]
    _ = ∫⁻ z in A ×ˢ B,
          Function.uncurry (barkerAcceptedFlow weight proposalDensity) z
          ∂reference.prod reference := by
      rw [setLIntegral_prod _ hflowMeas.aemeasurable]
      rfl
    _ = ∫⁻ x in B, ∫⁻ y in A,
          barkerAcceptedFlow weight proposalDensity x y ∂reference ∂reference := by
      rw [setLIntegral_prod_symm _ hflowMeas.aemeasurable]
      apply setLIntegral_congr_fun hB
      intro x _
      apply setLIntegral_congr_fun hA
      intro y _
      exact barkerAcceptedFlow_swap weight proposalDensity x y
    _ = ∫⁻ x in B, weight x *
        (∫⁻ y in A, proposalDensity x y * accept x y ∂reference) ∂reference := by
      apply setLIntegral_congr_fun hB
      intro x _
      change (∫⁻ y in A, barkerAcceptedFlow weight proposalDensity x y ∂reference) =
        weight x * (∫⁻ y in A, proposalDensity x y * accept x y ∂reference)
      calc
        (∫⁻ y in A, barkerAcceptedFlow weight proposalDensity x y ∂reference) =
            ∫⁻ y in A, weight x * (proposalDensity x y * accept x y) ∂reference := by
          apply setLIntegral_congr_fun hA
          intro y _
          change barkerAcceptedFlow weight proposalDensity x y =
            weight x * (proposalDensity x y * accept x y)
          rw [← mul_assoc, ← forwardDensityFlow,
            forwardDensityFlow_mul_barkerDensityAcceptance weight proposalDensity]
        _ = weight x *
            (∫⁻ y in A, proposalDensity x y * accept x y ∂reference) :=
          lintegral_const_mul (μ := reference.restrict A) (weight x)
            ((Measurable.of_uncurry_left hproposal).mul
              (Measurable.of_uncurry_left haccept))

/-- The density-based Barker MH transition built from a normalized proposal
density and Barker's acceptance rule. -/
noncomputable def barkerDensityMetropolisHastings
    (reference : Measure State) [SFinite reference]
    (weight : State → ENNReal) (proposalDensity : State → State → ENNReal)
    (hproposal : Measurable (Function.uncurry proposalDensity))
    (hproposalNorm : ∀ x, ∫⁻ y, proposalDensity x y ∂reference = 1) :
    ProbabilityTheory.Kernel State State := by
  letI : IsMarkovKernel (densityProposal reference proposalDensity) :=
    densityProposal_isMarkov reference hproposal hproposalNorm
  exact metropolisHastings (densityProposal reference proposalDensity)
    (barkerDensityAcceptance weight proposalDensity)

/-- Barker's density-based MH is a Markov kernel. -/
theorem barkerDensityMetropolisHastings_isMarkov
    (reference : Measure State) [SFinite reference]
    (weight : State → ENNReal) (proposalDensity : State → State → ENNReal)
    (hweight : Measurable weight)
    (hproposal : Measurable (Function.uncurry proposalDensity))
    (hproposalNorm : ∀ x, ∫⁻ y, proposalDensity x y ∂reference = 1) :
    IsMarkovKernel
      (barkerDensityMetropolisHastings reference weight proposalDensity hproposal
        hproposalNorm) := by
  let Q := densityProposal reference proposalDensity
  let accept := barkerDensityAcceptance weight proposalDensity
  letI : IsMarkovKernel Q := densityProposal_isMarkov reference hproposal hproposalNorm
  change IsMarkovKernel (metropolisHastings Q accept)
  exact metropolisHastings_isMarkov Q
    (measurable_uncurry_barkerDensityAcceptance hweight hproposal)
    (barkerDensityAcceptance_le_one weight proposalDensity)

/-- Barker's density-based MH satisfies detailed balance. -/
theorem barkerDensityMetropolisHastings_isReversible
    (reference : Measure State) [SFinite reference]
    (weight : State → ENNReal) (proposalDensity : State → State → ENNReal)
    (hweight : Measurable weight)
    (hproposal : Measurable (Function.uncurry proposalDensity))
    (hproposalNorm : ∀ x, ∫⁻ y, proposalDensity x y ∂reference = 1) :
    (barkerDensityMetropolisHastings reference weight proposalDensity hproposal
      hproposalNorm).IsReversible (densityTarget reference weight) := by
  let Q := densityProposal reference proposalDensity
  let accept := barkerDensityAcceptance weight proposalDensity
  letI : IsMarkovKernel Q := densityProposal_isMarkov reference hproposal hproposalNorm
  change (metropolisHastings Q accept).IsReversible (densityTarget reference weight)
  apply metropolisHastings_isReversible
    (densityTarget reference weight) Q
    (measurable_uncurry_barkerDensityAcceptance hweight hproposal)
  change (barkerDensityAcceptedKernel reference weight proposalDensity hproposal
    hproposalNorm).IsReversible (densityTarget reference weight)
  exact barkerDensityAcceptedKernel_isReversible reference weight proposalDensity
    hweight hproposal hproposalNorm

/-- Barker's density-based MH preserves the target measure.  Note: stationarity
alone does not imply convergence from arbitrary initial states; a convergence
result would require additional irreducibility and aperiodicity hypotheses. -/
theorem barkerDensityMetropolisHastings_invariant
    (reference : Measure State) [SFinite reference]
    (weight : State → ENNReal) (proposalDensity : State → State → ENNReal)
    (hweight : Measurable weight)
    (hproposal : Measurable (Function.uncurry proposalDensity))
    (hproposalNorm : ∀ x, ∫⁻ y, proposalDensity x y ∂reference = 1) :
    (barkerDensityMetropolisHastings reference weight proposalDensity hproposal
      hproposalNorm).Invariant (densityTarget reference weight) := by
  letI : IsMarkovKernel
      (barkerDensityMetropolisHastings reference weight proposalDensity hproposal
        hproposalNorm) :=
    barkerDensityMetropolisHastings_isMarkov reference weight proposalDensity
      hweight hproposal hproposalNorm
  exact (barkerDensityMetropolisHastings_isReversible reference weight proposalDensity
    hweight hproposal hproposalNorm).invariant

end Mcmc.Kernel
