import Mcmc.Codegen.Julia.Finite

/-! Compile-time regressions for the restricted Julia backend. -/

namespace Mcmc.Codegen.Julia.Tests

open Mcmc.Codegen.Julia

example : Mcmc.Codegen.Julia.Finite.module.validate = .ok () := by
  native_decide

private def invalidModule : Module where
  name := "Injected; error(\"bad\")"
  imports := []
  functions := []

example : invalidModule.validate =
    .error "unsupported or invalid Julia AST identifier/type" := by
  native_decide

private def unsupportedCallModule : Module where
  name := "LooksValid"
  imports := []
  functions := [{
    name := "entry"
    arguments := []
    body := [.expression (.call (.name "unsupported_call") [])]
  }]

example : unsupportedCallModule.validate =
    .error "unsupported or invalid Julia AST identifier/type" := by
  native_decide

example : (Mcmc.Codegen.Julia.Finite.lower
    Mcmc.Executable.Finite.Program.categorical).length = 1 :=
  rfl

example : (Mcmc.Codegen.Julia.Finite.lower
    Mcmc.Executable.Finite.Program.metropolisHastings).length = 2 :=
  rfl

end Mcmc.Codegen.Julia.Tests
