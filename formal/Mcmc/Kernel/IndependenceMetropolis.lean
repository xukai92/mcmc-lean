import Mcmc.Kernel.GeneralConvergence
import Mcmc.Kernel.MetropolisHastings

/-!
# General-state independence Metropolis--Hastings

This module isolates state-independent proposal densities and proves the
Doeblin minorization supplied by a uniform lower bound on their accepted
density.  A later algebraic lemma derives that lower bound from the classical
bounded target-to-proposal density ratio.
!-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace Mcmc.Kernel

open ProbabilityTheory

variable {State : Type*} [MeasurableSpace State]

/-- A state-independent proposal density. -/
def independenceProposalDensity (proposalWeight : State → ENNReal) :
    State → State → ENNReal := fun _ y => proposalWeight y

theorem measurable_uncurry_independenceProposalDensity
    {proposalWeight : State → ENNReal} (hproposal : Measurable proposalWeight) :
    Measurable (Function.uncurry (independenceProposalDensity proposalWeight)) :=
  hproposal.comp measurable_snd

/-- The general density-MH constructor specialized to an independence
proposal. -/
noncomputable def independenceMetropolisHastings
    (reference : Measure State) [SFinite reference]
    (targetWeight proposalWeight : State → ENNReal)
    (hproposal : Measurable proposalWeight)
    (hproposalNorm : ∫⁻ y, proposalWeight y ∂reference = 1) :
    Kernel State State :=
  densityMetropolisHastings reference targetWeight
    (independenceProposalDensity proposalWeight)
    (measurable_uncurry_independenceProposalDensity hproposal)
    (fun _ => hproposalNorm)

theorem independenceMetropolisHastings_isMarkov
    (reference : Measure State) [SFinite reference]
    (targetWeight proposalWeight : State → ENNReal)
    (htarget : Measurable targetWeight) (hproposal : Measurable proposalWeight)
    (hproposalNorm : ∫⁻ y, proposalWeight y ∂reference = 1) :
    IsMarkovKernel (independenceMetropolisHastings reference targetWeight
      proposalWeight hproposal hproposalNorm) :=
  densityMetropolisHastings_isMarkov reference targetWeight _ htarget
    (measurable_uncurry_independenceProposalDensity hproposal) (fun _ => hproposalNorm)

omit [MeasurableSpace State] in
/-- The classical bounded target-to-proposal ratio gives the accepted-density
floor `targetWeight / M`. Positivity and finiteness hypotheses make every
division cancellation explicit. -/
theorem independence_acceptedDensity_lower_of_le_mul
    (targetWeight proposalWeight : State → ENNReal) (M : ENNReal)
    (hM0 : M ≠ 0) (hMtop : M ≠ ∞)
    (htarget0 : ∀ x, targetWeight x ≠ 0)
    (htargetTop : ∀ x, targetWeight x ≠ ∞)
    (hproposal0 : ∀ x, proposalWeight x ≠ 0)
    (hproposalTop : ∀ x, proposalWeight x ≠ ∞)
    (hbound : ∀ x, targetWeight x ≤ M * proposalWeight x)
    (x y : State) :
    targetWeight y / M ≤ proposalWeight y *
      densityAcceptance targetWeight
        (independenceProposalDensity proposalWeight) x y := by
  let wx := targetWeight x
  let wy := targetWeight y
  let qx := proposalWeight x
  let qy := proposalWeight y
  have hwyM : wy / M ≤ qy := by
    apply (ENNReal.div_le_iff hM0 hMtop).2
    simpa [wy, qy, mul_comm] using hbound y
  have hwxM : wx / M ≤ qx := by
    apply (ENNReal.div_le_iff hM0 hMtop).2
    simpa [wx, qx, mul_comm] using hbound x
  have hflow0 : forwardDensityFlow targetWeight
      (independenceProposalDensity proposalWeight) x y ≠ 0 := by
    simp [forwardDensityFlow, independenceProposalDensity, htarget0 x,
      hproposal0 y]
  have heq : qy * densityAcceptance targetWeight
      (independenceProposalDensity proposalWeight) x y =
      min (wx * qy) (wy * qx) / wx := by
    apply (ENNReal.mul_left_inj (htarget0 x) (htargetTop x)).mp
    calc
      (qy * densityAcceptance targetWeight
          (independenceProposalDensity proposalWeight) x y) * wx =
          (wx * qy) * densityAcceptance targetWeight
            (independenceProposalDensity proposalWeight) x y := by ac_rfl
      _ = min (wx * qy) (wy * qx) := by
        simpa [wx, wy, qx, qy, symmetricAcceptedFlow,
          forwardDensityFlow, independenceProposalDensity] using
          forwardDensityFlow_mul_densityAcceptance targetWeight
            (independenceProposalDensity proposalWeight)
            (fun a b => ENNReal.mul_ne_top (htargetTop a) (hproposalTop b)) x y
      _ = (min (wx * qy) (wy * qx) / wx) * wx := by
        rw [ENNReal.div_mul_cancel (htarget0 x) (htargetTop x)]
  rw [heq]
  apply (ENNReal.le_div_iff_mul_le (Or.inl (htarget0 x))
    (Or.inl (htargetTop x))).2
  apply le_min
  · calc
      targetWeight y / M * wx = wx * (wy / M) := by simp [wx, wy, mul_comm]
      _ ≤ wx * qy := by simpa [mul_comm] using mul_le_mul_right hwyM wx
  · calc
      targetWeight y / M * wx = wy * (wx / M) := by
        simp [wx, wy, div_eq_mul_inv]
        ac_rfl
      _ ≤ wy * qx := by simpa [mul_comm] using mul_le_mul_right hwxM wy

/-- A pointwise accepted-density floor integrates to a Doeblin
minorization. This theorem includes the rejection mass automatically. -/
theorem independenceMetropolisHastings_uniformlyMinorizes
    (reference : Measure State) [SFinite reference]
    (targetWeight proposalWeight : State → ENNReal)
    (htarget : Measurable targetWeight) (hproposal : Measurable proposalWeight)
    (hproposalNorm : ∫⁻ y, proposalWeight y ∂reference = 1)
    (ε : ENNReal)
    (hlower : ∀ x y,
      ε * targetWeight y ≤ proposalWeight y *
        densityAcceptance targetWeight
          (independenceProposalDensity proposalWeight) x y) :
    UniformlyMinorizes
      (independenceMetropolisHastings reference targetWeight proposalWeight
        hproposal hproposalNorm)
      ε (densityTarget reference targetWeight) := by
  let Q := densityProposal reference (independenceProposalDensity proposalWeight)
  let accept := densityAcceptance targetWeight
    (independenceProposalDensity proposalWeight)
  letI : IsMarkovKernel Q := densityProposal_isMarkov reference
    (measurable_uncurry_independenceProposalDensity hproposal) (fun _ => hproposalNorm)
  intro x s hs
  rw [densityTarget, withDensity_apply _ hs]
  change ε * (∫⁻ y in s, targetWeight y ∂reference) ≤ _
  rw [← lintegral_const_mul _ htarget]
  change (∫⁻ y in s, ε * targetWeight y ∂reference) ≤ _
  have haccept : Measurable (Function.uncurry accept) :=
    measurable_uncurry_densityAcceptance htarget
      (measurable_uncurry_independenceProposalDensity hproposal)
  rw [show independenceMetropolisHastings reference targetWeight proposalWeight
      hproposal hproposalNorm = metropolisHastings Q accept by rfl,
    metropolisHastings_apply Q haccept x hs]
  apply le_add_right
  change (∫⁻ y in s, accept x y ∂
    densityProposal reference (independenceProposalDensity proposalWeight) x) ≥ _
  rw [densityProposal, ProbabilityTheory.Kernel.withDensity_apply _
      (measurable_uncurry_independenceProposalDensity hproposal),
    ProbabilityTheory.Kernel.const_apply]
  change (∫⁻ y in s, accept x y ∂reference.withDensity proposalWeight) ≥ _
  rw [setLIntegral_withDensity_eq_setLIntegral_mul reference hproposal
    (Measurable.of_uncurry_left haccept) hs]
  exact setLIntegral_mono' hs fun y _ => hlower x y

/-- Classical independence-MH Doeblin bound: if the normalized target density
is everywhere at most `M` times the proposal density, every transition row
dominates `1/M` times the target probability measure. -/
theorem independenceMetropolisHastings_uniformlyMinorizes_of_le_mul
    (reference : Measure State) [SFinite reference]
    (targetWeight proposalWeight : State → ENNReal)
    (htarget : Measurable targetWeight) (hproposal : Measurable proposalWeight)
    (hproposalNorm : ∫⁻ y, proposalWeight y ∂reference = 1)
    (M : ENNReal) (hM0 : M ≠ 0) (hMtop : M ≠ ∞)
    (htarget0 : ∀ x, targetWeight x ≠ 0)
    (htargetTop : ∀ x, targetWeight x ≠ ∞)
    (hproposal0 : ∀ x, proposalWeight x ≠ 0)
    (hproposalTop : ∀ x, proposalWeight x ≠ ∞)
    (hbound : ∀ x, targetWeight x ≤ M * proposalWeight x) :
    UniformlyMinorizes
      (independenceMetropolisHastings reference targetWeight proposalWeight
        hproposal hproposalNorm)
      (1 / M) (densityTarget reference targetWeight) := by
  apply independenceMetropolisHastings_uniformlyMinorizes reference
    targetWeight proposalWeight htarget hproposal hproposalNorm
  intro x y
  simpa [one_div, div_eq_mul_inv, mul_comm] using
    independence_acceptedDensity_lower_of_le_mul targetWeight proposalWeight M
      hM0 hMtop htarget0 htargetTop hproposal0 hproposalTop hbound x y

end Mcmc.Kernel
