import Mcmc.Executable.Finite.CompilerIRInterpreter
import Mcmc.Executable.IRFormat

/-! Compile-time regressions for the canonical finite sampler IR. -/

namespace Mcmc.Executable.Finite.CompilerIR.Tests

example : Mcmc.Executable.IRFormat.version = 27 := rfl

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

/-- The concrete midpoint recursion checks all joins of a balanced four-leaf
subtree and reports no turn when every endpoint predicate is false. -/
example :
    Mcmc.Executable.DynamicTreeIR.recursiveSubtreeTurns
      (fun _ _ => false) 5 3 6 = false := by
  native_decide

/-- The same recursion observes the outer `[3,6]` join. -/
example :
    Mcmc.Executable.DynamicTreeIR.recursiveSubtreeTurns
      (fun left right => decide (left = 3 ∧ right = 6)) 5 3 6 = true := by
  native_decide

/-- Complete recursive continuation succeeds when every leaf and join in the
same interval succeeds. -/
example :
    Mcmc.Executable.DynamicTreeIR.recursiveSubtreeContinues
      (fun _ => true) (fun _ _ => false) 5 3 6 = true := by
  native_decide

/-- A failed interior leaf is propagated through the concrete recursion. -/
example :
    Mcmc.Executable.DynamicTreeIR.recursiveSubtreeContinues
      (fun index => decide (index != 4)) (fun _ _ => false) 5 3 6 = false := by
  native_decide

end Mcmc.Executable.Finite.CompilerIR.Tests
