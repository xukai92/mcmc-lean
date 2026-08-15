import Mcmc.Executable.Continuous.CompilerIR

/-!
# Deferred numerical refinement contract

This module records, without asserting, the theorem required to connect an
external finite-precision backend to the ideal-real continuous sampler IR.
There is deliberately no instance for Julia or `Float64`: supplying one is the
deferred numerical-refinement milestone.
-/

namespace Mcmc.Executable.Continuous

open Mcmc.Executable

/-- Abstract interface of a state-passing numerical Gaussian-RWMH backend. -/
structure NumericalBackend where
  Value : Type
  Source : Type
  Error : Type
  step : Source → (Value → Value) → Value → Value →
    Except Error (Value × Source)

/-- Relations explaining how backend values, callbacks, and random sources
represent ideal reals, log densities, and event traces. -/
structure NumericalRepresentation (backend : NumericalBackend) where
  value : backend.Value → ℝ → Prop
  logDensity : (backend.Value → backend.Value) → (ℝ → ℝ) → Prop
  source : backend.Source → List IR.Event → Prop

/-- The exact obligation intentionally deferred for a concrete numerical
backend. This is a hypothesis-bearing contract, not an axiom and not an
instance claiming that Julia satisfies it. -/
structure NumericalRefinement (backend : NumericalBackend)
    (representation : NumericalRepresentation backend) : Prop where
  step_refines :
    ∀ {backendSource backendLogDensity backendScale backendCurrent
        backendResult backendRemaining logDensity scale current trace result remaining},
      representation.source backendSource trace →
      representation.logDensity backendLogDensity logDensity →
      representation.value backendScale scale →
      representation.value backendCurrent current →
      backend.step backendSource backendLogDensity backendScale backendCurrent =
        .ok (backendResult, backendRemaining) →
      CompilerIR.runGaussianRwmh logDensity scale current trace =
        .ok ⟨result, remaining⟩ →
      representation.value backendResult result ∧
        representation.source backendRemaining remaining

end Mcmc.Executable.Continuous
