import Mcmc.Executable.Finite.Categorical
import Mathlib.Tactic

/-!
# Executable finite primitive examples

Small exact examples protect cumulative-boundary and trace-validation behavior
before the complete finite Metropolis--Hastings program is assembled.
-/

namespace Mcmc.Executable.Finite.Examples

/-- Three outcomes with one zero-weight entry. -/
def weights : NatWeights 3 where
  weight := ![1, 0, 2]
  total_pos := by native_decide

example : weights.total = 3 := by native_decide

example : (weights.select ⟨0, by native_decide⟩).val = 0 := by
  native_decide

example : (weights.select ⟨1, by native_decide⟩).val = 2 := by
  native_decide

example : (weights.select ⟨2, by native_decide⟩).val = 2 := by
  native_decide

example : replayCategorical weights [⟨3, 1⟩] = .ok (⟨2, by omega⟩, []) := by
  native_decide

example : replayCategorical weights [⟨4, 1⟩] =
    .error (.boundMismatch 3 4) := by
  native_decide

example : replayCategorical weights [⟨3, 3⟩] =
    .error (.outOfRange 3 3) := by
  native_decide

end Mcmc.Executable.Finite.Examples
