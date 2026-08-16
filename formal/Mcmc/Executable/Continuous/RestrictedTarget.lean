import Mcmc.Executable.Continuous.BackendCertificates
import Mcmc.Executable.Continuous.RestrictedArtifact

/-!
# Restricted differentiable target expressions

Arbitrary foreign callbacks cannot be covered by a cross-language correctness
theorem. This small first-order expression language provides a checkable
alternative: its value and symbolic derivative are defined in Lean, and the
derivative interpreter is proved correct for every expression.
-/

namespace Mcmc.Executable.Continuous

/-- Scalar target expressions admitted by the first restricted callback
surface. They cover polynomial and exponential potentials without partial
operations. -/
inductive RestrictedExpr where
  | input
  | const (value : ℝ)
  | add (left right : RestrictedExpr)
  | mul (left right : RestrictedExpr)
  | neg (value : RestrictedExpr)
  | exp (value : RestrictedExpr)
  | sin (value : RestrictedExpr)
  | cos (value : RestrictedExpr)

/-- Compile portable rational syntax into the verified ideal-real language. -/
noncomputable def RestrictedArtifactExpr.compile :
    RestrictedArtifactExpr → RestrictedExpr
  | .input => .input
  | .rational numerator denominator =>
      .const ((numerator : ℝ) / (denominator : ℝ))
  | .add left right => .add left.compile right.compile
  | .mul left right => .mul left.compile right.compile
  | .neg value => .neg value.compile
  | .exp value => .exp value.compile
  | .sin value => .sin value.compile
  | .cos value => .cos value.compile

/-- Ideal-real interpretation. -/
noncomputable def RestrictedExpr.eval : RestrictedExpr → ℝ → ℝ
  | .input, x => x
  | .const value, _ => value
  | .add left right, x => left.eval x + right.eval x
  | .mul left right, x => left.eval x * right.eval x
  | .neg value, x => -value.eval x
  | .exp value, x => Real.exp (value.eval x)
  | .sin value, x => Real.sin (value.eval x)
  | .cos value, x => Real.cos (value.eval x)

/-- Symbolic first derivative in the same expression language. -/
def RestrictedExpr.derivative : RestrictedExpr → RestrictedExpr
  | .input => .const 1
  | .const _ => .const 0
  | .add left right => .add left.derivative right.derivative
  | .mul left right =>
      .add (.mul left.derivative right) (.mul left right.derivative)
  | .neg value => .neg value.derivative
  | .exp value => .mul (.exp value) value.derivative
  | .sin value => .mul (.cos value) value.derivative
  | .cos value => .neg (.mul (.sin value) value.derivative)

theorem RestrictedArtifactExpr.compile_derivative
    (expression : RestrictedArtifactExpr) :
    expression.derivative.compile = expression.compile.derivative := by
  induction expression with
  | input => norm_num [RestrictedArtifactExpr.derivative,
      RestrictedArtifactExpr.compile, RestrictedExpr.derivative]
  | rational numerator denominator =>
      norm_num [RestrictedArtifactExpr.derivative,
        RestrictedArtifactExpr.compile, RestrictedExpr.derivative]
  | add left right hleft hright =>
      simp only [RestrictedArtifactExpr.derivative,
        RestrictedArtifactExpr.compile, RestrictedExpr.derivative]
      rw [hleft, hright]
  | mul left right hleft hright =>
      simp only [RestrictedArtifactExpr.derivative,
        RestrictedArtifactExpr.compile, RestrictedExpr.derivative]
      rw [hleft, hright]
  | neg value hvalue =>
      simp only [RestrictedArtifactExpr.derivative,
        RestrictedArtifactExpr.compile, RestrictedExpr.derivative]
      rw [hvalue]
  | exp value hvalue =>
      simp only [RestrictedArtifactExpr.derivative,
        RestrictedArtifactExpr.compile, RestrictedExpr.derivative]
      rw [hvalue]
  | sin value hvalue =>
      simp only [RestrictedArtifactExpr.derivative,
        RestrictedArtifactExpr.compile, RestrictedExpr.derivative]
      rw [hvalue]
  | cos value hvalue =>
      simp only [RestrictedArtifactExpr.derivative,
        RestrictedArtifactExpr.compile, RestrictedExpr.derivative]
      rw [hvalue]

theorem RestrictedExpr.hasDerivAt_eval (expression : RestrictedExpr) (x : ℝ) :
    HasDerivAt expression.eval (expression.derivative.eval x) x := by
  induction expression with
  | input =>
      change HasDerivAt (fun y : ℝ => y) 1 x
      exact hasDerivAt_id x
  | const value =>
      change HasDerivAt (fun _ : ℝ => value) 0 x
      exact hasDerivAt_const x value
  | add left right hleft hright =>
      change HasDerivAt (fun y => left.eval y + right.eval y)
        (left.derivative.eval x + right.derivative.eval x) x
      convert hleft.add hright using 1
      all_goals first | exact Subsingleton.elim _ _ | rfl
  | mul left right hleft hright =>
      change HasDerivAt (fun y => left.eval y * right.eval y)
        (left.derivative.eval x * right.eval x +
          left.eval x * right.derivative.eval x) x
      convert hleft.mul hright using 1
      all_goals first | exact Subsingleton.elim _ _ | rfl
  | neg value hvalue =>
      change HasDerivAt (fun y => -value.eval y) (-value.derivative.eval x) x
      convert hvalue.neg using 1
      all_goals first | exact Subsingleton.elim _ _ | rfl
  | exp value hvalue =>
      change HasDerivAt (fun y => Real.exp (value.eval y))
        (Real.exp (value.eval x) * value.derivative.eval x) x
      simpa [mul_comm] using hvalue.exp
  | sin value hvalue =>
      change HasDerivAt (fun y => Real.sin (value.eval y))
        (Real.cos (value.eval x) * value.derivative.eval x) x
      convert Real.hasDerivAt_sin (value.eval x) |>.comp x hvalue using 1
      all_goals first | exact Subsingleton.elim _ _ | rfl
  | cos value hvalue =>
      change HasDerivAt (fun y => Real.cos (value.eval y))
        (-(Real.sin (value.eval x) * value.derivative.eval x)) x
      convert Real.hasDerivAt_cos (value.eval x) |>.comp x hvalue using 1
      all_goals first | exact Subsingleton.elim _ _ | rfl | ring

theorem RestrictedExpr.deriv_eval (expression : RestrictedExpr) (x : ℝ) :
    deriv expression.eval x = expression.derivative.eval x :=
  (expression.hasDerivAt_eval x).deriv

theorem RestrictedExpr.differentiable (expression : RestrictedExpr) :
    Differentiable ℝ expression.eval := fun x =>
  (expression.hasDerivAt_eval x).differentiableAt

theorem RestrictedExpr.measurable (expression : RestrictedExpr) :
    Measurable expression.eval := expression.differentiable.continuous.measurable

/-- Multiplication transports two absolute-error bounds. The asymmetric form
uses the computed right operand and ideal left operand, which avoids requiring
separate magnitude bounds. -/
theorem Approximates.mul {aHat a bHat b ea eb : ℝ}
    (ha : Approximates aHat a ea) (hb : Approximates bHat b eb) :
    Approximates (aHat * bHat) (a * b) (ea * |bHat| + |a| * eb) := by
  rw [Approximates]
  have hid : aHat * bHat - a * b = (aHat - a) * bHat + a * (bHat - b) := by
    ring
  rw [hid]
  calc
    |(aHat - a) * bHat + a * (bHat - b)| ≤
        |(aHat - a) * bHat| + |a * (bHat - b)| := abs_add_le _ _
    _ = |aHat - a| * |bHat| + |a| * |bHat - b| := by rw [abs_mul, abs_mul]
    _ ≤ ea * |bHat| + |a| * eb := by
      change |aHat - a| ≤ ea at ha
      change |bHat - b| ≤ eb at hb
      gcongr

/-- Backend-facing evidence that a value/gradient pair refines the verified
ideal-real semantics of one restricted expression. This is intentionally a
parallel numerical certificate, rather than an assumption hidden inside the
expression interpreter. -/
structure RestrictedTargetCertificate (expression : RestrictedExpr) where
  idealInput : ℝ
  computedInput : ℝ
  computedValue : ℝ
  computedDerivative : ℝ
  inputError : ℝ
  valueError : ℝ
  derivativeError : ℝ
  input_bound : Approximates computedInput idealInput inputError
  value_bound : Approximates computedValue (expression.eval idealInput) valueError
  derivative_bound : Approximates computedDerivative
    (expression.derivative.eval idealInput) derivativeError

/-- Centered Gaussian potential `x²/2` in the restricted language. -/
noncomputable def restrictedGaussianPotential : RestrictedExpr :=
  .mul (.const (1 / 2)) (.mul .input .input)

theorem restrictedGaussianArtifact_compile :
    restrictedGaussianArtifact.compile = restrictedGaussianPotential := by
  norm_num [restrictedGaussianArtifact, RestrictedArtifactExpr.compile,
    restrictedGaussianPotential]

@[simp] theorem restrictedGaussianPotential_eval (x : ℝ) :
    restrictedGaussianPotential.eval x = x ^ 2 / 2 := by
  simp [restrictedGaussianPotential, RestrictedExpr.eval]
  ring

@[simp] theorem restrictedGaussianPotential_derivative_eval (x : ℝ) :
    restrictedGaussianPotential.derivative.eval x = x := by
  simp [restrictedGaussianPotential, RestrictedExpr.derivative,
    RestrictedExpr.eval]
  ring

/-- Verified ideal value semantics of the generated nonconstant SoftAbs
potential artifact. -/
theorem restrictedSinusoidalPotentialArtifact_eval (x : ℝ) :
    restrictedSinusoidalPotentialArtifact.compile.eval x =
      x ^ 2 / 2 - Real.sin x := by
  simp [restrictedSinusoidalPotentialArtifact, RestrictedArtifactExpr.compile,
    RestrictedExpr.eval, restrictedGaussianArtifact]
  ring

/-- Its generated symbolic derivative is the exact force `x - cos x`. -/
theorem restrictedSinusoidalPotentialArtifact_derivative_eval (x : ℝ) :
    restrictedSinusoidalPotentialArtifact.derivative.compile.eval x =
      x - Real.cos x := by
  rw [RestrictedArtifactExpr.compile_derivative]
  simp [restrictedSinusoidalPotentialArtifact, RestrictedArtifactExpr.compile,
    RestrictedExpr.derivative, RestrictedExpr.eval, restrictedGaussianArtifact]
  ring

/-- Differentiating the generated force again yields the exact Hessian used
by the nonconstant SoftAbs metric client. -/
theorem restrictedSinusoidalPotentialArtifact_secondDerivative_eval (x : ℝ) :
    restrictedSinusoidalPotentialArtifact.derivative.derivative.compile.eval x =
      1 + Real.sin x := by
  simp [restrictedSinusoidalPotentialArtifact, restrictedGaussianArtifact,
    RestrictedArtifactExpr.derivative, RestrictedArtifactExpr.compile,
    RestrictedExpr.eval]
  ring

/-- The Gaussian restricted target obtains an end-to-end certificate directly
from its input bound. It is the first concrete bridge from restricted syntax to
the existing bounded RWMH/HMC callback contracts. -/
noncomputable def restrictedGaussianCertificate
    {computedInput idealInput inputError : ℝ}
    (hinput : Approximates computedInput idealInput inputError) :
    RestrictedTargetCertificate restrictedGaussianPotential where
  idealInput := idealInput
  computedInput := computedInput
  computedValue := computedInput ^ 2 / 2
  computedDerivative := computedInput
  inputError := inputError
  valueError := (inputError * |computedInput| + |idealInput| * inputError) / 2
  derivativeError := inputError
  input_bound := hinput
  value_bound := by
    rw [restrictedGaussianPotential_eval, div_eq_mul_inv, pow_two, pow_two]
    have hsquare := hinput.mul hinput
    have hhalf : Approximates ((2 : ℝ)⁻¹) (2 : ℝ)⁻¹ 0 := Approximates.refl _
    convert hsquare.mul hhalf using 1 <;> ring_nf
  derivative_bound := by
    simpa using hinput

end Mcmc.Executable.Continuous
