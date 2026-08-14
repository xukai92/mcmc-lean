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

/-- The generic executable semantics specialize to the explicit two-state row. -/
theorem stepPMF_eq_transitionRow (current : Fin 2) :
    Mcmc.Executable.Finite.stepPMF target proposal current =
      (transitionRow current).toPMF :=
  (Mcmc.Executable.Finite.stepPMF_refines target proposal current).trans
    (transitionRow_refines current).symm

/-- End-to-end finite MVP refinement: executable MH semantics equals the row
PMF of the existing verified MH kernel. -/
theorem stepPMF_refines (current : Fin 2) :
    Mcmc.Executable.Finite.stepPMF target proposal current =
      (Mcmc.Finite.MetropolisHastings.kernel
        target.toNatWeights.toDistribution proposal.toKernel
        target.toDistribution_positive).rowPMF current :=
  Mcmc.Executable.Finite.stepPMF_refines target proposal current

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
