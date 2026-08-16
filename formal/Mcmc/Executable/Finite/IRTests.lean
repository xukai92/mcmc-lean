import Mcmc.Executable.Finite.CompilerIRInterpreter
import Mcmc.Executable.IRFormat

/-! Compile-time regressions for the canonical finite sampler IR. -/

namespace Mcmc.Executable.Finite.CompilerIR.Tests

example : Mcmc.Executable.IRFormat.version = 14 := rfl

example : runCategorical [1, 0, 2] [⟨3, 1⟩] = .ok (2, []) := by
  native_decide

example : runMetropolisHastings
    [1, 3] [[1, 1], [1, 1]] 0 [⟨2, 1⟩, ⟨2, 0⟩] = .ok (1, []) := by
  native_decide

example : runMetropolisHastings
    [1, 3] [[1, 1], [1, 1]] 1 [⟨2, 1⟩] = .ok (1, []) := by
  native_decide

end Mcmc.Executable.Finite.CompilerIR.Tests
