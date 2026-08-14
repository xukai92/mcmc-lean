import Mcmc.Executable.Finite.MetropolisHastings
import Mathlib.Tactic

/-!
# Asymmetric three-state executable MH example

This fixture exercises unequal proposal-row totals and a one-way proposal edge:
state `0` can propose state `2`, while state `2` has zero proposal weight back
to state `0`. The MH acceptance threshold therefore rejects that move exactly.
-/

namespace Mcmc.Executable.Finite.AsymmetricThreeState

def target : PositiveNatWeights 3 where
  weight := ![1, 2, 3]
  total_pos := by native_decide
  weight_pos := by decide

def proposal : NatKernelWeights 3 where
  row state := match state with
    | 0 => { weight := ![1, 2, 1], total_pos := by native_decide }
    | 1 => { weight := ![1, 1, 1], total_pos := by native_decide }
    | 2 => { weight := ![0, 2, 1], total_pos := by native_decide }

/-- The generic refinement theorem applies without symmetry or strictly
positive proposal atoms. -/
example (current : Fin 3) :
    stepPMF target proposal current =
      (Mcmc.Finite.MetropolisHastings.kernel
        target.toNatWeights.toDistribution proposal.toKernel
        target.toDistribution_positive).rowPMF current :=
  stepPMF_refines target proposal current

/-- The one-way `0 → 2` proposal is rejected because its reverse weight is
zero. -/
example : replayMHStep target proposal 0 [⟨4, 3⟩, ⟨3, 0⟩] = .ok (0, []) := by
  native_decide

/-- A `2 → 1` proposal uses the cross-multiplied acceptance bound `18` and is
accepted below threshold `6`. -/
example : replayMHStep target proposal 2 [⟨3, 0⟩, ⟨18, 5⟩] = .ok (1, []) := by
  native_decide

example : replayMHStep target proposal 2 [⟨3, 0⟩, ⟨18, 6⟩] = .ok (2, []) := by
  native_decide

end Mcmc.Executable.Finite.AsymmetricThreeState
