import Mcmc.Executable.Continuous.RestrictedTarget
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

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

/-- On an explicitly bounded-above domain, the ideal exponential transports
an input error with Lipschitz factor `exp upper`. This discharges the analytic
part of a backend `exp` certificate; only the backend's local libm error at the
computed argument remains implementation-specific. -/
theorem exp_approximates_exp_of_le
    {computed ideal error upper : ℝ}
    (hinput : Approximates computed ideal error)
    (hcomputed : computed ≤ upper) (hideal : ideal ≤ upper) :
    Approximates (Real.exp computed) (Real.exp ideal)
      (Real.exp upper * error) := by
  rw [Approximates] at hinput ⊢
  have hlipschitz :
      |Real.exp computed - Real.exp ideal| ≤
        Real.exp upper * |computed - ideal| := by
    have hmean := Convex.norm_image_sub_le_of_norm_deriv_le
      (s := Set.Iic upper) (f := Real.exp)
      (fun x _ => Real.differentiableAt_exp)
      (fun x hx => by
        rw [Real.deriv_exp, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos x)]
        exact Real.exp_le_exp.mpr hx)
      (convex_Iic upper) hideal hcomputed
    simpa [Real.norm_eq_abs, abs_sub_comm] using hmean
  exact hlipschitz.trans
    (mul_le_mul_of_nonneg_left hinput (Real.exp_nonneg upper))

/-- Compose a backend's local `exp`/libm error with transport of an already
approximate, bounded argument. -/
theorem exp_backend_approximates_of_le
    {computedExp computed ideal localError inputError upper : ℝ}
    (hlocal : Approximates computedExp (Real.exp computed) localError)
    (hinput : Approximates computed ideal inputError)
    (hcomputed : computed ≤ upper) (hideal : ideal ≤ upper) :
    Approximates computedExp (Real.exp ideal)
      (localError + Real.exp upper * inputError) :=
  hlocal.trans (exp_approximates_exp_of_le hinput hcomputed hideal)

theorem sin_approximates {computed ideal error : ℝ}
    (hinput : Approximates computed ideal error) :
    Approximates (Real.sin computed) (Real.sin ideal) error := by
  rw [Approximates] at hinput ⊢
  have hlip : |Real.sin computed - Real.sin ideal| ≤ |computed - ideal| := by
    simpa [Real.dist_eq] using
      Real.lipschitzWith_sin.dist_le_mul computed ideal
  exact hlip.trans hinput

theorem cos_approximates {computed ideal error : ℝ}
    (hinput : Approximates computed ideal error) :
    Approximates (Real.cos computed) (Real.cos ideal) error := by
  rw [Approximates] at hinput ⊢
  have hlip : |Real.cos computed - Real.cos ideal| ≤ |computed - ideal| := by
    simpa [Real.dist_eq] using
      Real.lipschitzWith_cos.dist_le_mul computed ideal
  exact hlip.trans hinput

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
  sin : ℝ → ℝ
  cos : ℝ → ℝ
  rationalError : Int → Nat → ℝ
  addError : ℝ → ℝ → ℝ
  mulError : ℝ → ℝ → ℝ
  negError : ℝ → ℝ
  expTransportError : ℝ → ℝ → ℝ → ℝ
  sinTransportError : ℝ → ℝ → ℝ → ℝ
  cosTransportError : ℝ → ℝ → ℝ → ℝ
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
  sin_transport_bound : ∀ computed ideal error,
    Approximates computed ideal error →
      Approximates (sin computed) (Real.sin ideal)
        (sinTransportError computed ideal error)
  cos_transport_bound : ∀ computed ideal error,
    Approximates computed ideal error →
      Approximates (cos computed) (Real.cos ideal)
        (cosTransportError computed ideal error)

/-- Easier concrete-backend contract. Arithmetic operations retain their
local rounding bounds, while `exp_local_bound` concerns only the backend
result versus the ideal exponential at the same computed argument. Lean then
adds argument transport itself. -/
structure RestrictedPrimitiveBackend where
  rational : Int → Nat → ℝ
  add : ℝ → ℝ → ℝ
  mul : ℝ → ℝ → ℝ
  neg : ℝ → ℝ
  exp : ℝ → ℝ
  sin : ℝ → ℝ
  cos : ℝ → ℝ
  rationalError : Int → Nat → ℝ
  addError : ℝ → ℝ → ℝ
  mulError : ℝ → ℝ → ℝ
  negError : ℝ → ℝ
  expLocalError : ℝ → ℝ
  sinLocalError : ℝ → ℝ
  cosLocalError : ℝ → ℝ
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
  exp_local_bound : ∀ value,
    Approximates (exp value) (Real.exp value) (expLocalError value)
  sin_local_bound : ∀ value,
    Approximates (sin value) (Real.sin value) (sinLocalError value)
  cos_local_bound : ∀ value,
    Approximates (cos value) (Real.cos value) (cosLocalError value)

/-- Upgrade local primitive bounds to the recursive restricted-expression
backend. The exponential transport factor is finite and selected separately
at every expression node. -/
noncomputable def RestrictedPrimitiveBackend.toRestrictedBackend
    (backend : RestrictedPrimitiveBackend) : RestrictedBackend where
  rational := backend.rational
  add := backend.add
  mul := backend.mul
  neg := backend.neg
  exp := backend.exp
  sin := backend.sin
  cos := backend.cos
  rationalError := backend.rationalError
  addError := backend.addError
  mulError := backend.mulError
  negError := backend.negError
  expTransportError computed ideal error :=
    backend.expLocalError computed + Real.exp (max computed ideal) * error
  sinTransportError computed _ideal error := backend.sinLocalError computed + error
  cosTransportError computed _ideal error := backend.cosLocalError computed + error
  rational_bound := backend.rational_bound
  add_bound := backend.add_bound
  mul_bound := backend.mul_bound
  neg_bound := backend.neg_bound
  exp_transport_bound computed ideal _error hinput :=
    exp_backend_approximates_of_le (backend.exp_local_bound computed) hinput
      (le_max_left computed ideal) (le_max_right computed ideal)
  sin_transport_bound computed _ideal _error hinput :=
    (backend.sin_local_bound computed).trans (sin_approximates hinput)
  cos_transport_bound computed _ideal _error hinput :=
    (backend.cos_local_bound computed).trans (cos_approximates hinput)

/-- Exact-real primitive backend for generated restricted expressions. This is
the proof-side reference semantics: all local errors are zero. It deliberately
does not model IEEE arithmetic or platform transcendental functions. -/
noncomputable def exactRestrictedPrimitiveBackend : RestrictedPrimitiveBackend where
  rational numerator denominator := (numerator : ℝ) / (denominator : ℝ)
  add := (· + ·)
  mul := (· * ·)
  neg := (-·)
  exp := Real.exp
  sin := Real.sin
  cos := Real.cos
  rationalError _ _ := 0
  addError _ _ := 0
  mulError _ _ := 0
  negError _ := 0
  expLocalError _ := 0
  sinLocalError _ := 0
  cosLocalError _ := 0
  rational_bound _ _ := Approximates.refl _
  add_bound _ _ := Approximates.refl _
  mul_bound _ _ := Approximates.refl _
  neg_bound _ := Approximates.refl _
  exp_local_bound _ := Approximates.refl _
  sin_local_bound _ := Approximates.refl _
  cos_local_bound _ := Approximates.refl _

/-- Exact restricted-expression backend with analytic transport of a possibly
inexact input. Its operations are ideal real operations; only input error can
propagate. -/
noncomputable def exactRestrictedBackend : RestrictedBackend where
  rational numerator denominator := (numerator : ℝ) / (denominator : ℝ)
  add := (· + ·)
  mul := (· * ·)
  neg := (-·)
  exp := Real.exp
  sin := Real.sin
  cos := Real.cos
  rationalError _ _ := 0
  addError _ _ := 0
  mulError _ _ := 0
  negError _ := 0
  expTransportError computed ideal error :=
    Real.exp (max computed ideal) * error
  sinTransportError _ _ error := error
  cosTransportError _ _ error := error
  rational_bound _ _ := Approximates.refl _
  add_bound _ _ := Approximates.refl _
  mul_bound _ _ := Approximates.refl _
  neg_bound _ := Approximates.refl _
  exp_transport_bound computed ideal _error hinput :=
    exp_approximates_exp_of_le hinput
      (le_max_left computed ideal) (le_max_right computed ideal)
  sin_transport_bound _ _ _ hinput := sin_approximates hinput
  cos_transport_bound _ _ _ hinput := cos_approximates hinput

@[simp] theorem exactRestrictedBackend_rational (numerator : Int)
    (denominator : Nat) :
    exactRestrictedBackend.rational numerator denominator =
      (numerator : ℝ) / (denominator : ℝ) := rfl

@[simp] theorem exactRestrictedBackend_add (left right : ℝ) :
    exactRestrictedBackend.add left right = left + right := rfl

@[simp] theorem exactRestrictedBackend_mul (left right : ℝ) :
    exactRestrictedBackend.mul left right = left * right := rfl

@[simp] theorem exactRestrictedBackend_neg (value : ℝ) :
    exactRestrictedBackend.neg value = -value := rfl

@[simp] theorem exactRestrictedBackend_exp (value : ℝ) :
    exactRestrictedBackend.exp value = Real.exp value := rfl

@[simp] theorem exactRestrictedBackend_sin (value : ℝ) :
    exactRestrictedBackend.sin value = Real.sin value := rfl

@[simp] theorem exactRestrictedBackend_cos (value : ℝ) :
    exactRestrictedBackend.cos value = Real.cos value := rfl

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
  | .sin value, x => backend.sin (value.backendEval backend x)
  | .cos value, x => backend.cos (value.backendEval backend x)

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
  | .sin value =>
      backend.sinTransportError (value.backendEval backend computedInput)
        (value.compile.eval idealInput)
        (value.accumulatedError backend computedInput idealInput inputError)
  | .cos value =>
      backend.cosTransportError (value.backendEval backend computedInput)
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
  | sin value hvalue =>
    exact backend.sin_transport_bound _ _ _ hvalue
  | cos value hvalue =>
    exact backend.cos_transport_bound _ _ _ hvalue

/-- The exact reference backend evaluates every generated artifact exactly as
its verified ideal-real compilation. -/
theorem RestrictedArtifactExpr.exactRestrictedBackend_eval
    (expression : RestrictedArtifactExpr) (input : ℝ) :
    expression.backendEval exactRestrictedBackend input =
      expression.compile.eval input := by
  induction expression <;>
    simp only [RestrictedArtifactExpr.backendEval,
      RestrictedArtifactExpr.compile, RestrictedExpr.eval,
      exactRestrictedBackend_rational, exactRestrictedBackend_add,
      exactRestrictedBackend_mul, exactRestrictedBackend_neg,
      exactRestrictedBackend_exp, exactRestrictedBackend_sin,
      exactRestrictedBackend_cos, *]

/-- Every generated target artifact therefore has a zero-error value and
symbolic-gradient certificate at an exactly represented input. -/
noncomputable def RestrictedArtifactExpr.exactTargetCertificate
    (expression : RestrictedArtifactExpr) (input : ℝ) :
    RestrictedTargetCertificate expression.compile where
  idealInput := input
  computedInput := input
  computedValue := expression.backendEval exactRestrictedBackend input
  computedDerivative :=
    expression.derivative.backendEval exactRestrictedBackend input
  inputError := 0
  valueError := 0
  derivativeError := 0
  input_bound := Approximates.refl input
  value_bound := by
    rw [expression.exactRestrictedBackend_eval]
    exact Approximates.refl _
  derivative_bound := by
    rw [expression.derivative.exactRestrictedBackend_eval,
      expression.compile_derivative]
    exact Approximates.refl _

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

/-- Assumption-free ex-post enclosure for one sine/cosine pair on `[-1,1]`.
The checker uses mathlib's proved cubic sine and quadratic cosine remainders;
all submitted values and radii are rational. -/
structure SinCosRationalIntervalCertificate where
  input : ℚ
  computedSin : ℚ
  sinError : ℚ
  computedCos : ℚ
  cosError : ℚ
deriving DecidableEq, Repr

namespace SinCosRationalIntervalCertificate

def sinCenter (certificate : SinCosRationalIntervalCertificate) : ℚ :=
  certificate.input - certificate.input ^ 3 / 6

def sinRemainder (certificate : SinCosRationalIntervalCertificate) : ℚ :=
  |certificate.input| ^ 5 / 100

def cosCenter (certificate : SinCosRationalIntervalCertificate) : ℚ :=
  1 - certificate.input ^ 2 / 2

def cosRemainder (certificate : SinCosRationalIntervalCertificate) : ℚ :=
  |certificate.input| ^ 4 * (5 / 96)

def Valid (certificate : SinCosRationalIntervalCertificate) : Prop :=
  |certificate.input| ≤ 1 ∧ 0 ≤ certificate.sinError ∧
    |certificate.computedSin - certificate.sinCenter| +
      certificate.sinRemainder ≤ certificate.sinError ∧
    0 ≤ certificate.cosError ∧
    |certificate.computedCos - certificate.cosCenter| +
      certificate.cosRemainder ≤ certificate.cosError

instance (certificate : SinCosRationalIntervalCertificate) :
    Decidable certificate.Valid := by
  unfold Valid
  infer_instance

def check (certificate : SinCosRationalIntervalCertificate) : Bool :=
  decide certificate.Valid

@[simp] theorem check_eq_true_iff
    (certificate : SinCosRationalIntervalCertificate) :
    certificate.check = true ↔ certificate.Valid := by
  simp [check]

theorem sin_approximates (certificate : SinCosRationalIntervalCertificate)
    (hvalid : certificate.Valid) :
    Approximates (certificate.computedSin : ℝ)
      (Real.sin certificate.input) certificate.sinError := by
  have hx : |(certificate.input : ℝ)| ≤ 1 := by
    exact_mod_cast hvalid.1
  have hremainder := Real.sin_bound hx
  have hbudget :
      |(certificate.computedSin : ℝ) - certificate.sinCenter| +
        certificate.sinRemainder ≤ certificate.sinError := by
    exact_mod_cast hvalid.2.2.1
  unfold Approximates
  calc
    |(certificate.computedSin : ℝ) - Real.sin certificate.input| ≤
        |(certificate.computedSin : ℝ) - certificate.sinCenter| +
          |(certificate.sinCenter : ℝ) - Real.sin certificate.input| := by
      rw [show (certificate.computedSin : ℝ) - Real.sin certificate.input =
          (certificate.computedSin - certificate.sinCenter) +
            (certificate.sinCenter - Real.sin certificate.input) by ring]
      exact abs_add_le _ _
    _ ≤ |(certificate.computedSin : ℝ) - certificate.sinCenter| +
        certificate.sinRemainder := by
      exact add_le_add (le_refl _)
        (by simpa [sinCenter, sinRemainder, abs_sub_comm] using hremainder)
    _ ≤ certificate.sinError := hbudget

theorem cos_approximates (certificate : SinCosRationalIntervalCertificate)
    (hvalid : certificate.Valid) :
    Approximates (certificate.computedCos : ℝ)
      (Real.cos certificate.input) certificate.cosError := by
  have hx : |(certificate.input : ℝ)| ≤ 1 := by
    exact_mod_cast hvalid.1
  have hremainder := Real.cos_bound hx
  have hbudget :
      |(certificate.computedCos : ℝ) - certificate.cosCenter| +
        certificate.cosRemainder ≤ certificate.cosError := by
    exact_mod_cast hvalid.2.2.2.2
  unfold Approximates
  calc
    |(certificate.computedCos : ℝ) - Real.cos certificate.input| ≤
        |(certificate.computedCos : ℝ) - certificate.cosCenter| +
          |(certificate.cosCenter : ℝ) - Real.cos certificate.input| := by
      rw [show (certificate.computedCos : ℝ) - Real.cos certificate.input =
          (certificate.computedCos - certificate.cosCenter) +
            (certificate.cosCenter - Real.cos certificate.input) by ring]
      exact abs_add_le _ _
    _ ≤ |(certificate.computedCos : ℝ) - certificate.cosCenter| +
        certificate.cosRemainder := by
      exact add_le_add (le_refl _)
        (by simpa [cosCenter, cosRemainder, abs_sub_comm] using hremainder)
    _ ≤ certificate.cosError := hbudget

end SinCosRationalIntervalCertificate

end Mcmc.Executable.Continuous
