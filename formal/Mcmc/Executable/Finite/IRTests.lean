import Mcmc.Executable.Finite.CompilerIRInterpreter
import Mcmc.Executable.IRFormat

/-! Compile-time regressions for the canonical finite sampler IR. -/

namespace Mcmc.Executable.Finite.CompilerIR.Tests

example : Mcmc.Executable.IRFormat.version = 18 := rfl

example : runCategorical [1, 0, 2] [⟨3, 1⟩] = .ok (2, []) := by
  native_decide

example : runMetropolisHastings
    [1, 3] [[1, 1], [1, 1]] 0 [⟨2, 1⟩, ⟨2, 0⟩] = .ok (1, []) := by
  native_decide

example : runMetropolisHastings
    [1, 3] [[1, 1], [1, 1]] 1 [⟨2, 1⟩] = .ok (1, []) := by
  native_decide

/-- The zero-based Lean recursion matches the seven-point monotone-orbit row
used by the Julia conformance test: root 2, then right/left doubling, retains
indices 0 through 3 before the boundary stop. -/
example :
    Mcmc.Executable.DynamicTreeIR.recursiveDoublingCandidateRow
      7 2 (fun _ _ => false) ![true, false] ⟨2, by omega⟩ =
        Finset.univ.filter (fun state : Fin 7 => state.val ≤ 3) := by
  native_decide

end Mcmc.Executable.Finite.CompilerIR.Tests
