import Mcmc.Executable.Finite.MetropolisHastings
import Mcmc.Examples.TwoState
import Mathlib.Tactic

/-!
# Executable two-state Metropolis--Hastings example

The encoding is `0 = false`, `1 = true`.  Target weights are `[1, 3]` and
both proposal rows are `[1, 1]`, matching `Mcmc.Examples.TwoState` exactly.
-/

namespace Mcmc.Executable.Finite.TwoState

def target : PositiveNatWeights 2 where
  weight := ![1, 3]
  total_pos := by native_decide
  weight_pos := by decide

def proposalRow : NatWeights 2 where
  weight := ![1, 1]
  total_pos := by native_decide

def proposal : NatKernelWeights 2 where
  row := fun _ => proposalRow

/-- Exact output-row weights of the two-state MH transition. -/
def transitionRow (current : Fin 2) : NatWeights 2 :=
  if current = 0 then
    { weight := ![1, 1], total_pos := by native_decide }
  else
    { weight := ![1, 5], total_pos := by native_decide }

/-- Rejection/acceptance weights for an off-diagonal proposal (`0` rejects,
`1` accepts). -/
def acceptanceWeights (current proposed : Fin 2) (hne : proposed ≠ current) :
    NatWeights 2 where
  weight decision := if decision = 0 then
    proposal.acceptanceUpper target current proposed -
      proposal.acceptanceThreshold target current proposed
  else
    proposal.acceptanceThreshold target current proposed
  total_pos := by
    fin_cases current <;> fin_cases proposed <;>
      simp_all [NatKernelWeights.acceptanceUpper,
        NatKernelWeights.acceptanceThreshold, proposal, proposalRow, target,
        NatWeights.total]

/-- Exact PMF semantics of the same proposal/accept/reject control flow used by
`replayMHStep`. -/
noncomputable def stepPMF (current : Fin 2) : PMF (Fin 2) :=
  proposalRow.selectPMF.bind fun proposed ↦
    if hself : proposed = current then
      PMF.pure current
    else
      (acceptanceWeights current proposed hself).selectPMF.map fun decision ↦
        if decision = 1 then proposed else current

/-- The operational MH program's exact denotation is the simple transition-row
weight vector above. -/
theorem stepPMF_eq_transitionRow (current : Fin 2) :
    stepPMF current = (transitionRow current).toPMF := by
  rw [stepPMF, proposalRow.selectPMF_eq_toPMF]
  ext next
  rw [PMF.bind_apply, tsum_fintype]
  fin_cases current <;> fin_cases next <;>
    norm_num [proposalRow, NatWeights.toPMF_apply, acceptanceWeights,
      NatWeights.selectPMF_eq_toPMF, PMF.map_apply, PMF.pure_apply,
      tsum_fintype, transitionRow, NatKernelWeights.acceptanceUpper,
      NatKernelWeights.acceptanceThreshold, proposal, target, NatWeights.total,
      ENNReal.div_eq_inv_mul]
  · rw [ENNReal.inv_mul_cancel] <;> norm_num
  · have hl : (2 : ENNReal)⁻¹ * ((6 : ENNReal)⁻¹ * 2) ≠ ⊤ := by finiteness
    have hr : (6 : ENNReal)⁻¹ ≠ ⊤ := by finiteness
    rw [← ENNReal.coe_toNNReal hl, ← ENNReal.coe_toNNReal hr]
    norm_num [ENNReal.toNNReal_mul, ENNReal.toNNReal_inv,
      ENNReal.toNNReal_ofNat]
  · have hl : (2 : ENNReal)⁻¹ * ((6 : ENNReal)⁻¹ * 4) +
        (2 : ENNReal)⁻¹ ≠ ⊤ := by finiteness
    have hr : (6 : ENNReal)⁻¹ * 5 ≠ ⊤ := by finiteness
    rw [← ENNReal.coe_toNNReal hl, ← ENNReal.coe_toNNReal hr]
    congr 1
    rw [ENNReal.toNNReal_add (by finiteness) (by finiteness)]
    norm_num [ENNReal.toNNReal_mul, ENNReal.toNNReal_inv,
      ENNReal.toNNReal_ofNat]

/-- The exact executable row law is the row PMF of the already-verified finite
MH kernel.  Thus its detailed balance and invariance results are inherited. -/
theorem transitionRow_refines (current : Fin 2) :
    (transitionRow current).toPMF =
      (Mcmc.Finite.MetropolisHastings.kernel
        target.toNatWeights.toDistribution proposal.toKernel
        target.toDistribution_positive).rowPMF current := by
  ext next
  fin_cases current <;> fin_cases next <;>
    norm_num [transitionRow, NatWeights.toPMF_apply,
      Mcmc.Finite.MarkovKernel.rowPMF_apply,
      Mcmc.Finite.MetropolisHastings.kernel,
      Mcmc.Finite.MetropolisHastings.probability,
      Mcmc.Finite.MetropolisHastings.move,
      Mcmc.Finite.MetropolisHastings.flow,
      Mcmc.Finite.MetropolisHastings.stay,
      NatKernelWeights.toKernel, proposal, proposalRow, target,
      NatWeights.toDistribution_mass, NatWeights.total,
      ENNReal.ofReal_div_of_pos]

/-- End-to-end finite MVP refinement: executable MH semantics equals the row
PMF of the existing verified MH kernel. -/
theorem stepPMF_refines (current : Fin 2) :
    stepPMF current =
      (Mcmc.Finite.MetropolisHastings.kernel
        target.toNatWeights.toDistribution proposal.toKernel
        target.toDistribution_positive).rowPMF current :=
  (stepPMF_eq_transitionRow current).trans (transitionRow_refines current)

example : replayMHStep target proposal 0 [⟨2, 0⟩] = .ok (0, []) := by
  native_decide

example : replayMHStep target proposal 0 [⟨2, 1⟩, ⟨2, 0⟩] = .ok (1, []) := by
  native_decide

example : replayMHStep target proposal 1 [⟨2, 0⟩, ⟨6, 0⟩] = .ok (0, []) := by
  native_decide

example : replayMHStep target proposal 1 [⟨2, 0⟩, ⟨6, 2⟩] = .ok (1, []) := by
  native_decide

example : replayMHStep target proposal 1 [⟨2, 1⟩] = .ok (1, []) := by
  native_decide

end Mcmc.Executable.Finite.TwoState
