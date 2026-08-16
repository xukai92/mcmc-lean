import Mcmc.Executable.Continuous.CompilerIR

/-!
# Numerical refinement contract and exact interpreter instance

This module records, without asserting, the theorem required to connect an
external finite-precision backend to the ideal-real continuous sampler IR.
The ideal-real interpreter instantiates the contract as a proved oracle.
There is deliberately no equality-based instance for Julia or `Float64`:
those backends use bounded-error and decision-margin certificates instead.
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

/-- Exact ideal-real backend obtained by exposing the verified IR interpreter
through the generic numerical-backend interface.  This is a concrete oracle
for differential testing; it is not an IEEE floating-point implementation. -/
noncomputable def exactInterpreterBackend : NumericalBackend where
  Value := ℝ
  Source := List IR.Event
  Error := CompilerIR.RuntimeError
  step source logDensity scale current :=
    (CompilerIR.runGaussianRwmh logDensity scale current source).map
      fun replay => (replay.value, replay.remaining)

/-- Exact representation uses equality for values, callbacks, and event
sources. -/
def exactInterpreterRepresentation :
    NumericalRepresentation exactInterpreterBackend where
  value computed ideal := computed = ideal
  logDensity computed ideal := computed = ideal
  source computed ideal := computed = ideal

/-- The ideal-real interpreter satisfies the numerical-refinement contract
without assumptions.  External backends can be tested against this oracle,
while bounded Float64 refinement continues to use the separate error and
decision-margin theorems. -/
theorem exactInterpreter_refines :
    NumericalRefinement exactInterpreterBackend
      exactInterpreterRepresentation := by
  constructor
  intro backendSource backendLogDensity backendScale backendCurrent
    backendResult backendRemaining logDensity scale current trace result
    remaining hsource hlogDensity hscale hcurrent hbackend hideal
  change backendSource = trace at hsource
  change backendLogDensity = logDensity at hlogDensity
  change backendScale = scale at hscale
  change backendCurrent = current at hcurrent
  subst backendSource
  subst backendLogDensity
  subst backendScale
  subst backendCurrent
  change
    (CompilerIR.runGaussianRwmh logDensity scale current trace).map
        (fun replay => (replay.value, replay.remaining)) =
      .ok (backendResult, backendRemaining) at hbackend
  rw [hideal] at hbackend
  simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at hbackend
  exact ⟨hbackend.1.symm, hbackend.2.symm⟩

end Mcmc.Executable.Continuous
