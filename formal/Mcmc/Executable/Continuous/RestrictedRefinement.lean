import Mcmc.Executable.Continuous.RestrictedTarget

/-!
# Recursive numerical refinement for restricted targets

This module separates the generated expression tree from a concrete numeric
backend. Per-operation rounding and libm obligations are fields of
`RestrictedBackend`; Lean composes them into one end-to-end value bound for
every portable expression.
-/

namespace Mcmc.Executable.Continuous

theorem Approximates.trans {computed middle ideal firstError secondError : ℝ}
    (hfirst : Approximates computed middle firstError)
    (hsecond : Approximates middle ideal secondError) :
    Approximates computed ideal (firstError + secondError) := by
  rw [Approximates]
  calc
    |computed - ideal| = |(computed - middle) + (middle - ideal)| := by ring_nf
    _ ≤ |computed - middle| + |middle - ideal| := abs_add_le _ _
    _ ≤ firstError + secondError := add_le_add hfirst hsecond

theorem Approximates.neg {computed ideal error : ℝ}
    (h : Approximates computed ideal error) :
    Approximates (-computed) (-ideal) error := by
  rw [Approximates] at h ⊢
  rw [show -computed - -ideal = -(computed - ideal) by ring, abs_neg]
  exact h

/-- A scalar backend plus explicit local error evidence. `expTransportError`
includes both the backend's local `exp` error and transport from an already
approximate argument; a client may establish it on a bounded admitted domain.
-/
structure RestrictedBackend where
  rational : Int → Nat → ℝ
  add : ℝ → ℝ → ℝ
  mul : ℝ → ℝ → ℝ
  neg : ℝ → ℝ
  exp : ℝ → ℝ
  rationalError : Int → Nat → ℝ
  addError : ℝ → ℝ → ℝ
  mulError : ℝ → ℝ → ℝ
  negError : ℝ → ℝ
  expTransportError : ℝ → ℝ → ℝ → ℝ
  rational_bound : ∀ numerator denominator,
    Approximates (rational numerator denominator)
      ((numerator : ℝ) / (denominator : ℝ))
      (rationalError numerator denominator)
  add_bound : ∀ left right,
    Approximates (add left right) (left + right) (addError left right)
  mul_bound : ∀ left right,
    Approximates (mul left right) (left * right) (mulError left right)
  neg_bound : ∀ value,
    Approximates (neg value) (-value) (negError value)
  exp_transport_bound : ∀ computed ideal error,
    Approximates computed ideal error →
      Approximates (exp computed) (Real.exp ideal)
        (expTransportError computed ideal error)

/-- Numeric interpretation supplied by a certified backend. -/
def RestrictedArtifactExpr.backendEval (backend : RestrictedBackend) :
    RestrictedArtifactExpr → ℝ → ℝ
  | .input, x => x
  | .rational numerator denominator, _ => backend.rational numerator denominator
  | .add left right, x => backend.add (left.backendEval backend x)
      (right.backendEval backend x)
  | .mul left right, x => backend.mul (left.backendEval backend x)
      (right.backendEval backend x)
  | .neg value, x => backend.neg (value.backendEval backend x)
  | .exp value, x => backend.exp (value.backendEval backend x)

/-- Error accumulated structurally from the backend certificates. -/
noncomputable def RestrictedArtifactExpr.accumulatedError
    (backend : RestrictedBackend) (computedInput idealInput : ℝ)
    (inputError : ℝ) :
    RestrictedArtifactExpr → ℝ
  | .input => inputError
  | .rational numerator denominator => backend.rationalError numerator denominator
  | .add left right =>
      backend.addError (left.backendEval backend computedInput)
          (right.backendEval backend computedInput) +
        (left.accumulatedError backend computedInput idealInput inputError +
          right.accumulatedError backend computedInput idealInput inputError)
  | .mul left right =>
      backend.mulError (left.backendEval backend computedInput)
          (right.backendEval backend computedInput) +
        (left.accumulatedError backend computedInput idealInput inputError *
            |right.backendEval backend computedInput| +
          |left.compile.eval idealInput| *
            right.accumulatedError backend computedInput idealInput inputError)
  | .neg value =>
      backend.negError (value.backendEval backend computedInput) +
        value.accumulatedError backend computedInput idealInput inputError
  | .exp value =>
      backend.expTransportError (value.backendEval backend computedInput)
        (value.compile.eval idealInput)
        (value.accumulatedError backend computedInput idealInput inputError)

/-- Recursive end-to-end refinement theorem. No arithmetic or transcendental
operation is silently assumed exact: all such facts come from `backend`. -/
theorem RestrictedArtifactExpr.backendEval_approximates
    (backend : RestrictedBackend) (expression : RestrictedArtifactExpr)
    {computedInput idealInput inputError : ℝ}
    (hinput : Approximates computedInput idealInput inputError) :
    Approximates (expression.backendEval backend computedInput)
      (expression.compile.eval idealInput)
      (expression.accumulatedError backend computedInput idealInput inputError) := by
  induction expression with
  | input => exact hinput
  | rational numerator denominator => exact backend.rational_bound _ _
  | add left right hleft hright =>
      exact (backend.add_bound _ _).trans (hleft.add hright)
  | mul left right hleft hright =>
      exact (backend.mul_bound _ _).trans (hleft.mul hright)
  | neg value hvalue =>
      exact (backend.neg_bound _).trans hvalue.neg
  | exp value hvalue =>
      exact backend.exp_transport_bound _ _ _ hvalue

/-- Turn operation-level backend evidence into the value/gradient certificate
consumed by the bounded sampler layers. Both expressions are evaluated by the
same backend and the derivative tree is generated in Lean. -/
noncomputable def RestrictedArtifactExpr.targetCertificate
    (backend : RestrictedBackend) (expression : RestrictedArtifactExpr)
    {computedInput idealInput inputError : ℝ}
    (hinput : Approximates computedInput idealInput inputError) :
    RestrictedTargetCertificate expression.compile where
  idealInput := idealInput
  computedInput := computedInput
  computedValue := expression.backendEval backend computedInput
  computedDerivative := expression.derivative.backendEval backend computedInput
  inputError := inputError
  valueError := expression.accumulatedError backend computedInput idealInput inputError
  derivativeError := expression.derivative.accumulatedError backend
    computedInput idealInput inputError
  input_bound := hinput
  value_bound := expression.backendEval_approximates backend hinput
  derivative_bound := by
    rw [← expression.compile_derivative]
    exact expression.derivative.backendEval_approximates backend hinput

end Mcmc.Executable.Continuous
