import Mcmc.Executable.Finite.Categorical
import Mcmc.Finite.MetropolisHastings

/-!
# Executable finite Metropolis--Hastings

This module implements a finite MH step using natural weights only.  Proposal
selection is cumulative.  The acceptance comparison cross-multiplies target
and proposal weights, so execution performs no division or floating-point
arithmetic.
-/

namespace Mcmc.Executable.Finite

/-- A proposal matrix represented by one positive-total weight vector per row. -/
structure NatKernelWeights (n : ℕ) where
  row : Fin n → NatWeights n

/-- A target whose atoms are all strictly positive, as required by the local
finite MH correctness theorem. -/
structure PositiveNatWeights (n : ℕ) extends NatWeights n where
  weight_pos : ∀ i, 0 < weight i

namespace NatKernelWeights

/-- Real-valued kernel realization used by the existing finite theory. -/
noncomputable def toKernel {n : ℕ} (proposal : NatKernelWeights n) :
    Mcmc.Finite.MarkovKernel (Fin n) where
  prob x y := (proposal.row x).toDistribution.mass y
  nonneg x y := (proposal.row x).toDistribution.nonneg y
  sum_prob x := (proposal.row x).toDistribution.sum_mass

/-- Denominator of the exact MH acceptance comparison for a proposal `x → y`. -/
def acceptanceUpper {n : ℕ} (target : PositiveNatWeights n)
    (proposal : NatKernelWeights n) (x y : Fin n) : ℕ :=
  target.weight x * (proposal.row x).weight y * (proposal.row y).total

/-- Numerator, capped by the denominator, of the exact MH acceptance comparison. -/
def acceptanceThreshold {n : ℕ} (target : PositiveNatWeights n)
    (proposal : NatKernelWeights n) (x y : Fin n) : ℕ :=
  min (acceptanceUpper target proposal x y)
    (target.weight y * (proposal.row y).weight x * (proposal.row x).total)

end NatKernelWeights

theorem PositiveNatWeights.toDistribution_positive {n : ℕ}
    (target : PositiveNatWeights n) (i : Fin n) :
    0 < target.toNatWeights.toDistribution.mass i := by
  rw [NatWeights.toDistribution_mass]
  exact div_pos (by exact_mod_cast target.weight_pos i)
    (by exact_mod_cast target.total_pos)

/-- Rejection/acceptance weights for an off-diagonal proposal. Index `0`
rejects and index `1` accepts. -/
def acceptanceWeights {n : ℕ} (target : PositiveNatWeights n)
    (proposal : NatKernelWeights n) (current proposed : Fin n)
    (hupper : 0 < proposal.acceptanceUpper target current proposed) :
    NatWeights 2 where
  weight decision := if decision = 0 then
    proposal.acceptanceUpper target current proposed -
      proposal.acceptanceThreshold target current proposed
  else
    proposal.acceptanceThreshold target current proposed
  total_pos := by
    have hthreshold : proposal.acceptanceThreshold target current proposed ≤
        proposal.acceptanceUpper target current proposed :=
      min_le_left _ _
    change 0 < (proposal.acceptanceUpper target current proposed -
      proposal.acceptanceThreshold target current proposed) +
        proposal.acceptanceThreshold target current proposed
    omega

@[simp]
theorem acceptanceWeights_total {n : ℕ} (target : PositiveNatWeights n)
    (proposal : NatKernelWeights n) (current proposed : Fin n)
    (hupper : 0 < proposal.acceptanceUpper target current proposed) :
    (acceptanceWeights target proposal current proposed hupper).total =
      proposal.acceptanceUpper target current proposed := by
  have hthreshold : proposal.acceptanceThreshold target current proposed ≤
      proposal.acceptanceUpper target current proposed :=
    min_le_left _ _
  simp [acceptanceWeights, NatWeights.total, Fin.sum_univ_two,
    Nat.sub_add_cancel hthreshold]

@[simp]
theorem acceptanceWeights_zero {n : ℕ} (target : PositiveNatWeights n)
    (proposal : NatKernelWeights n) (current proposed : Fin n)
    (hupper : 0 < proposal.acceptanceUpper target current proposed) :
    (acceptanceWeights target proposal current proposed hupper).weight 0 =
      proposal.acceptanceUpper target current proposed -
        proposal.acceptanceThreshold target current proposed := by
  simp [acceptanceWeights]

@[simp]
theorem acceptanceWeights_one {n : ℕ} (target : PositiveNatWeights n)
    (proposal : NatKernelWeights n) (current proposed : Fin n)
    (hupper : 0 < proposal.acceptanceUpper target current proposed) :
    (acceptanceWeights target proposal current proposed hupper).weight 1 =
      proposal.acceptanceThreshold target current proposed := by
  simp [acceptanceWeights]

/-- Exact PMF semantics of generic finite proposal/accept/reject control flow. -/
noncomputable def stepPMF {n : ℕ} (target : PositiveNatWeights n)
    (proposal : NatKernelWeights n) (current : Fin n) : PMF (Fin n) :=
  (proposal.row current).selectPMF.bind fun proposed ↦
    if _hself : proposed = current then
      PMF.pure current
    else
      let upper := proposal.acceptanceUpper target current proposed
      if hupper : 0 < upper then
        (acceptanceWeights target proposal current proposed hupper).selectPMF.map
          fun decision ↦ if decision = 1 then proposed else current
      else
        PMF.pure current

theorem acceptanceUpper_pos_iff {n : ℕ} (target : PositiveNatWeights n)
    (proposal : NatKernelWeights n) (current proposed : Fin n) :
    0 < proposal.acceptanceUpper target current proposed ↔
      0 < (proposal.row current).weight proposed := by
  simp [NatKernelWeights.acceptanceUpper, target.weight_pos,
    (proposal.row proposed).total_positive]

/-- Off the diagonal, only proposing the requested next state and accepting it
can produce that state. -/
theorem stepPMF_apply_of_ne {n : ℕ} (target : PositiveNatWeights n)
    (proposal : NatKernelWeights n) {current next : Fin n}
    (hne : next ≠ current) :
    stepPMF target proposal current next =
      ((proposal.row current).weight next : ENNReal) /
        ((proposal.row current).total : ENNReal) *
      (proposal.acceptanceThreshold target current next : ENNReal) /
        (proposal.acceptanceUpper target current next : ENNReal) := by
  rw [stepPMF, (proposal.row current).selectPMF_eq_toPMF,
    PMF.bind_apply, tsum_fintype]
  classical
  rw [Finset.sum_eq_single next]
  · simp only [NatWeights.toPMF_apply]
    simp [hne]
    by_cases hupper : 0 < proposal.acceptanceUpper target current next
    · simp [hupper, NatWeights.selectPMF_eq_toPMF,
        NatWeights.toPMF_apply, PMF.map_apply, tsum_fintype,
        acceptanceWeights_total, hne, div_eq_mul_inv, mul_assoc]
    · have hzero : (proposal.row current).weight next = 0 := by
        exact Nat.eq_zero_of_not_pos
          ((acceptanceUpper_pos_iff target proposal current next).not.mp hupper)
      simp [hzero]
  · intro proposed _ hproposed
    by_cases hself : proposed = current
    · subst proposed
      simp [hne]
    · by_cases hupper : 0 < proposal.acceptanceUpper target current proposed
      · have hnex : next ≠ proposed := Ne.symm hproposed
        simp [hself, hupper, NatWeights.selectPMF_eq_toPMF, PMF.map_apply,
          tsum_fintype, hnex, hne]
      · simp [hself, hupper, hne]
  · simp

/-- The integer threshold ratio is exactly the usual real-valued MH
acceptance probability whenever the proposed edge has positive weight. -/
theorem acceptanceThreshold_div_eq_acceptance {n : ℕ}
    (target : PositiveNatWeights n) (proposal : NatKernelWeights n)
    (current proposed : Fin n)
    (hproposal : 0 < (proposal.row current).weight proposed) :
    (proposal.acceptanceThreshold target current proposed : ℝ) /
        (proposal.acceptanceUpper target current proposed : ℝ) =
      Mcmc.Finite.MetropolisHastings.acceptance
        target.toNatWeights.toDistribution proposal.toKernel current proposed := by
  have htargetCurrent : (0 : ℝ) < target.weight current := by
    exact_mod_cast target.weight_pos current
  have htargetProposed : (0 : ℝ) < target.weight proposed := by
    exact_mod_cast target.weight_pos proposed
  have hproposalReal : (0 : ℝ) < (proposal.row current).weight proposed := by
    exact_mod_cast hproposal
  have hcurrentTotal : (0 : ℝ) < (proposal.row current).total := by
    exact_mod_cast (proposal.row current).total_positive
  have hproposedTotal : (0 : ℝ) < (proposal.row proposed).total := by
    exact_mod_cast (proposal.row proposed).total_positive
  have htargetTotal : (0 : ℝ) < target.toNatWeights.total := by
    exact_mod_cast target.total_pos
  have hdenom : (0 : ℝ) <
      target.weight current * (proposal.row current).weight proposed *
        (proposal.row proposed).total := by positivity
  have hratio :
      ((target.weight proposed : ℝ) / target.toNatWeights.total *
          ((proposal.row proposed).weight current / (proposal.row proposed).total)) /
        ((target.weight current : ℝ) / target.toNatWeights.total *
          ((proposal.row current).weight proposed / (proposal.row current).total)) =
      ((target.weight proposed : ℝ) * (proposal.row proposed).weight current *
          (proposal.row current).total) /
        ((target.weight current : ℝ) * (proposal.row current).weight proposed *
          (proposal.row proposed).total) := by
    field_simp
  rw [Mcmc.Finite.MetropolisHastings.acceptance]
  simp only [NatWeights.toDistribution_mass, NatKernelWeights.toKernel]
  rw [hratio]
  simp only [NatKernelWeights.acceptanceThreshold,
    NatKernelWeights.acceptanceUpper, Nat.cast_min, Nat.cast_mul]
  rw [← min_div_div_right (le_of_lt hdenom)]
  rw [div_self (ne_of_gt hdenom)]

/-- Off-diagonal executable mass equals the existing finite MH transition
probability. -/
theorem stepPMF_apply_toReal_of_ne {n : ℕ}
    (target : PositiveNatWeights n) (proposal : NatKernelWeights n)
    {current next : Fin n} (hne : next ≠ current) :
    (stepPMF target proposal current next).toReal =
      (Mcmc.Finite.MetropolisHastings.kernel
        target.toNatWeights.toDistribution proposal.toKernel
        target.toDistribution_positive).prob current next := by
  rw [stepPMF_apply_of_ne target proposal hne, ENNReal.toReal_div,
    ENNReal.toReal_mul, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast]
  rw [mul_div_assoc]
  by_cases hzero : (proposal.row current).weight next = 0
  · simp [hzero, Mcmc.Finite.MetropolisHastings.kernel,
      Mcmc.Finite.MetropolisHastings.probability,
      Mcmc.Finite.MetropolisHastings.move,
      Mcmc.Finite.MetropolisHastings.flow, Ne.symm hne,
      NatKernelWeights.toKernel, NatWeights.toDistribution_mass]
    rw [min_eq_left (by positivity)]
    simp
  · have hpositive : 0 < (proposal.row current).weight next :=
      Nat.pos_of_ne_zero hzero
    rw [acceptanceThreshold_div_eq_acceptance target proposal current next hpositive]
    rw [show (Mcmc.Finite.MetropolisHastings.kernel
        target.toNatWeights.toDistribution proposal.toKernel
        target.toDistribution_positive).prob current next =
      Mcmc.Finite.MetropolisHastings.move
        target.toNatWeights.toDistribution proposal.toKernel current next by
      simp [Mcmc.Finite.MetropolisHastings.kernel,
        Mcmc.Finite.MetropolisHastings.probability, Ne.symm hne]]
    rw [Mcmc.Finite.MetropolisHastings.move_eq_proposal_mul_acceptance
      target.toNatWeights.toDistribution proposal.toKernel
      target.toDistribution_positive (Ne.symm hne)]
    rfl

theorem sum_stepPMF_toReal {n : ℕ} (target : PositiveNatWeights n)
    (proposal : NatKernelWeights n) (current : Fin n) :
    ∑ next : Fin n, (stepPMF target proposal current next).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun _ _ ↦ PMF.apply_ne_top _ _)]
  have hsum := PMF.tsum_coe (stepPMF target proposal current)
  rw [tsum_fintype] at hsum
  rw [hsum]
  norm_num

/-- The diagonal executable mass follows from normalization and the proved
off-diagonal equality. -/
theorem stepPMF_apply_toReal {n : ℕ} (target : PositiveNatWeights n)
    (proposal : NatKernelWeights n) (current next : Fin n) :
    (stepPMF target proposal current next).toReal =
      (Mcmc.Finite.MetropolisHastings.kernel
        target.toNatWeights.toDistribution proposal.toKernel
        target.toDistribution_positive).prob current next := by
  by_cases hne : next ≠ current
  · exact stepPMF_apply_toReal_of_ne target proposal hne
  · have heq : next = current := not_ne_iff.mp hne
    subst next
    let kernel := Mcmc.Finite.MetropolisHastings.kernel
      target.toNatWeights.toDistribution proposal.toKernel
      target.toDistribution_positive
    have hexec := sum_stepPMF_toReal target proposal current
    have hkernel := kernel.sum_prob current
    have hrest :
        ∑ next ∈ (Finset.univ.erase current),
            (stepPMF target proposal current next).toReal =
          ∑ next ∈ (Finset.univ.erase current), kernel.prob current next := by
      apply Finset.sum_congr rfl
      intro state hstate
      exact stepPMF_apply_toReal_of_ne target proposal
        (Finset.mem_erase.mp hstate).1
    rw [← Finset.sum_erase_add Finset.univ
      (fun state ↦ (stepPMF target proposal current state).toReal)
      (Finset.mem_univ current)] at hexec
    rw [← Finset.sum_erase_add Finset.univ (kernel.prob current)
      (Finset.mem_univ current)] at hkernel
    linarith

/-- Generic finite executable MH refinement. -/
theorem stepPMF_refines {n : ℕ} (target : PositiveNatWeights n)
    (proposal : NatKernelWeights n) (current : Fin n) :
    stepPMF target proposal current =
      (Mcmc.Finite.MetropolisHastings.kernel
        target.toNatWeights.toDistribution proposal.toKernel
        target.toDistribution_positive).rowPMF current := by
  ext next
  have hreal := stepPMF_apply_toReal target proposal current next
  have hrow := Mcmc.Finite.MarkovKernel.rowPMF_apply_toReal
    (Mcmc.Finite.MetropolisHastings.kernel
      target.toNatWeights.toDistribution proposal.toKernel
      target.toDistribution_positive) current next
  have hreal' :
      (stepPMF target proposal current next).toReal =
        ((Mcmc.Finite.MetropolisHastings.kernel
          target.toNatWeights.toDistribution proposal.toKernel
          target.toDistribution_positive).rowPMF current next).toReal :=
    hreal.trans hrow.symm
  have hleft := PMF.apply_ne_top (stepPMF target proposal current) next
  have hright := PMF.apply_ne_top
    ((Mcmc.Finite.MetropolisHastings.kernel
      target.toNatWeights.toDistribution proposal.toKernel
      target.toDistribution_positive).rowPMF current) next
  rw [← ENNReal.coe_toNNReal hleft, ← ENNReal.coe_toNNReal hright]
  congr 1
  exact NNReal.eq hreal'

/-- Replay one exact finite MH transition.  A self-proposal returns immediately;
an off-diagonal proposal consumes a second bounded draw for acceptance. -/
def replayMHStep {n : ℕ} (target : PositiveNatWeights n)
    (proposal : NatKernelWeights n) (current : Fin n)
    (trace : List DrawEvent) : Except ExecError (Fin n × List DrawEvent) := do
  let proposalResult ← replayCategorical (proposal.row current) trace
  let proposed := proposalResult.1
  if proposed = current then
    return (current, proposalResult.2)
  let upper := proposal.acceptanceUpper target current proposed
  let acceptResult ← replayDraw upper proposalResult.2
  if acceptResult.value < proposal.acceptanceThreshold target current proposed then
    return (proposed, acceptResult.remaining)
  else
    return (current, acceptResult.remaining)

end Mcmc.Executable.Finite
