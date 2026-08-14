import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.MapComap
import Mcmc.Executable.Primitive

/-!
# A typed first-order sampler IR

Programs bind syntax variables, not Lean continuations.  The same closed
syntax has a deterministic trace interpretation and a compositional mathlib
kernel interpretation.  The initial value universe is deliberately small: it
contains exactly the real, Boolean, and finite values needed by the first
finite and continuous sampler slices.
-/

open MeasureTheory
open scoped ProbabilityTheory

namespace Mcmc.Executable.IR

open ProbabilityTheory

/-- Object-language value types. -/
inductive Ty where
  | real
  | bool
  | fin (size : ℕ)

/-- Lean interpretation of an object-language type. -/
@[reducible] def Ty.denote : Ty → Type
  | .real => ℝ
  | .bool => Bool
  | .fin size => Fin size

instance (τ : Ty) : MeasurableSpace τ.denote := by
  cases τ <;> infer_instance

/-- A de Bruijn variable in a typed context. -/
inductive Var : List Ty → Ty → Type
  | here : Var (τ :: Γ) τ
  | there : Var Γ τ → Var (σ :: Γ) τ

/-- Runtime environment for a typed context. -/
@[reducible] def Env : List Ty → Type
  | [] => PUnit
  | τ :: Γ => τ.denote × Env Γ

instance (Γ : List Ty) : MeasurableSpace (Env Γ) := by
  induction Γ with
  | nil => exact inferInstance
  | cons τ Γ ih =>
      letI : MeasurableSpace (Env Γ) := ih
      exact inferInstance

/-- Read a typed variable from its environment. -/
def Var.get : Var Γ τ → Env Γ → τ.denote
  | .here, env => env.1
  | .there name, env => name.get env.2

theorem Var.measurable_get (name : Var Γ τ) : Measurable name.get := by
  induction name with
  | here => exact measurable_fst
  | there name ih => exact ih.comp measurable_snd

/-- Pure expressions used by sampler programs. -/
inductive Expr (Γ : List Ty) : Ty → Type
  | var (name : Var Γ τ) : Expr Γ τ
  | real (value : ℝ) : Expr Γ .real
  | bool (value : Bool) : Expr Γ .bool
  | add (left right : Expr Γ .real) : Expr Γ .real
  | sub (left right : Expr Γ .real) : Expr Γ .real
  | mul (left right : Expr Γ .real) : Expr Γ .real
  | exp (value : Expr Γ .real) : Expr Γ .real
  | log (value : Expr Γ .real) : Expr Γ .real
  | min (left right : Expr Γ .real) : Expr Γ .real
  | lt (left right : Expr Γ .real) : Expr Γ .bool
  | ite (condition : Expr Γ .bool) (yes no : Expr Γ τ) : Expr Γ τ

/-- Evaluate a pure expression. -/
noncomputable def Expr.eval : Expr Γ τ → Env Γ → τ.denote
  | .var name, env => name.get env
  | .real value, _ => value
  | .bool value, _ => value
  | .add left right, env => left.eval env + right.eval env
  | .sub left right, env => left.eval env - right.eval env
  | .mul left right, env => left.eval env * right.eval env
  | .exp value, env => Real.exp (value.eval env)
  | .log value, env => Real.log (value.eval env)
  | .min left right, env => Min.min (left.eval env) (right.eval env)
  | .lt left right, env => decide (left.eval env < right.eval env)
  | .ite condition yes no, env => if condition.eval env then yes.eval env else no.eval env

theorem Expr.measurable_eval (expression : Expr Γ τ) : Measurable expression.eval := by
  induction expression with
  | var name => exact name.measurable_get
  | real | bool => exact measurable_const
  | add _ _ left right => exact left.add right
  | sub _ _ left right => exact left.sub right
  | mul _ _ left right => exact left.mul right
  | exp _ value => exact Real.measurable_exp.comp value
  | log _ value => exact Real.measurable_log.comp value
  | min _ _ left right => exact left.min right
  | lt left right hleft hright =>
      change Measurable (fun env => if left.eval env < right.eval env then true else false)
      exact Measurable.ite (measurableSet_lt hleft hright) measurable_const measurable_const
  | ite condition yes no hcondition hyes hno =>
      exact Measurable.ite (hcondition (measurableSet_singleton true)) hyes hno

/-- Typed stochastic primitives in the first-order IR. -/
inductive Prim : Ty → Type
  | drawBelow (upper : ℕ) (positive : 0 < upper) : Prim (.fin upper)
  | standardNormal : Prim .real
  | uniformUnit : Prim .real

/-- Exact probability-measure interpretation of an IR primitive. -/
noncomputable def Prim.measure : {τ : Ty} → Prim τ → Measure τ.denote
  | _, .drawBelow upper positive => drawBelowMeasure upper positive
  | _, .standardNormal => standardNormalMeasure
  | _, .uniformUnit => unitUniform

theorem Prim.isProbabilityMeasure (primitive : Prim τ) :
    IsProbabilityMeasure primitive.measure := by
  cases primitive with
  | drawBelow upper positive =>
      simpa [Prim.measure] using drawBelowMeasure_isProbability upper positive
  | standardNormal =>
      simpa [Prim.measure] using standardNormalMeasure_isProbability
  | uniformUnit =>
      simpa [Prim.measure] using unitUniform_isProbabilityMeasure

/-- Inspectable first-order sampler programs. `letE` and `sample` extend the
de Bruijn context of their body; neither constructor stores a Lean function. -/
inductive Program : List Ty → Ty → Type
  | ret (value : Expr Γ τ) : Program Γ τ
  | letE (value : Expr Γ σ) (body : Program (σ :: Γ) τ) : Program Γ τ
  | sample (primitive : Prim σ) (body : Program (σ :: Γ) τ) : Program Γ τ

/-- Exact kernel interpretation. A program with free variables is a kernel
from environments to results; a closed program is evaluated at `PUnit.unit`. -/
noncomputable def Program.kernel : Program Γ τ → Kernel (Env Γ) τ.denote
  | .ret value => Kernel.deterministic value.eval value.measurable_eval
  | .letE value body =>
      let binding := Kernel.deterministic value.eval value.measurable_eval
      Kernel.snd (binding.compProd
        (body.kernel.comap Prod.swap measurable_swap))
  | .sample primitive body =>
      let draw := Kernel.const (Env Γ) primitive.measure
      Kernel.snd (draw.compProd
        (body.kernel.comap Prod.swap measurable_swap))

theorem Program.isMarkovKernel (program : Program Γ τ) :
    IsMarkovKernel program.kernel := by
  induction program with
  | ret =>
      rw [Program.kernel]
      infer_instance
  | letE value body ih =>
      letI : IsMarkovKernel body.kernel := ih
      rw [Program.kernel]
      infer_instance
  | sample primitive body ih =>
      letI : IsProbabilityMeasure primitive.measure := primitive.isProbabilityMeasure
      letI : IsMarkovKernel body.kernel := ih
      rw [Program.kernel]
      infer_instance

/-- Operational bind equation for a pure `let`. -/
theorem Program.kernel_letE_apply (value : Expr Γ σ)
    (body : Program (σ :: Γ) τ) (env : Env Γ) :
    (Program.letE value body).kernel env = body.kernel (value.eval env, env) := by
  letI : IsMarkovKernel body.kernel := body.isMarkovKernel
  ext set hset
  rw [Program.kernel, Kernel.snd_apply' _ _ hset,
    Kernel.compProd_apply (measurable_snd hset)]
  simp only [Kernel.deterministic_apply, Kernel.comap_apply]
  change (∫⁻ b, body.kernel (b, env) set ∂Measure.dirac (value.eval env)) = _
  have hf : Measurable (fun b : σ.denote => body.kernel (b, env) set) :=
    (body.kernel.measurable_coe hset).comp (measurable_id.prod measurable_const)
  rw [lintegral_dirac' _ hf]

/-- Kernel bind equation for a primitive draw. -/
theorem Program.kernel_sample_apply (primitive : Prim σ)
    (body : Program (σ :: Γ) τ) (env : Env Γ) {set : Set τ.denote}
    (hset : MeasurableSet set) :
    (Program.sample primitive body).kernel env set =
      ∫⁻ value, body.kernel (value, env) set ∂primitive.measure := by
  letI : IsProbabilityMeasure primitive.measure := primitive.isProbabilityMeasure
  letI : IsMarkovKernel body.kernel := body.isMarkovKernel
  rw [Program.kernel, Kernel.snd_apply' _ _ hset,
    Kernel.compProd_apply (measurable_snd hset)]
  simp only [Kernel.const_apply, Kernel.comap_apply]
  rfl

/-- A closed program's exact output measure. -/
noncomputable def Program.measure (program : Program [] τ) : Measure τ.denote :=
  program.kernel PUnit.unit

instance (program : Program [] τ) : IsProbabilityMeasure program.measure := by
  exact program.isMarkovKernel.isProbabilityMeasure PUnit.unit

/-- Typed operational trace events for the IR. -/
inductive Event where
  | drawBelow (upper value : ℕ)
  | standardNormal (value : ℝ)
  | uniformUnit (value : ℝ)

/-- Operational failures are explicit and distinct from mathematical mass. -/
inductive Error where
  | exhausted
  | kindMismatch
  | boundMismatch (expected actual : ℕ)
  | outOfRangeNatural (upper value : ℕ)
  | outOfRangeUnit (value : ℝ)

structure Replay (α : Type) where
  value : α
  remaining : List Event

/-- Replay one primitive event. This ideal-real interpreter is noncomputable;
backends use a separate serializable numeric representation. -/
noncomputable def Prim.replay (primitive : Prim τ) (trace : List Event) :
    Except Error (Replay τ.denote) :=
  match trace with
  | [] => .error .exhausted
  | event :: rest =>
      match primitive, event with
      | .drawBelow upper _, .drawBelow actual value =>
          if actual ≠ upper then .error (.boundMismatch upper actual)
          else if h : value < upper then .ok ⟨⟨value, h⟩, rest⟩
          else .error (.outOfRangeNatural upper value)
      | .standardNormal, .standardNormal value => .ok ⟨value, rest⟩
      | .uniformUnit, .uniformUnit value =>
          if 0 ≤ value ∧ value < 1 then .ok ⟨value, rest⟩
          else .error (.outOfRangeUnit value)
      | _, _ => .error .kindMismatch

/-- Deterministic trace interpretation of the same program syntax. -/
noncomputable def Program.replay : Program Γ τ → Env Γ → List Event →
    Except Error (Replay τ.denote)
  | .ret value, env, trace => .ok ⟨value.eval env, trace⟩
  | .letE value body, env, trace => body.replay (value.eval env, env) trace
  | .sample primitive body, env, trace =>
      match primitive.replay trace with
      | .error error => .error error
      | .ok draw => body.replay (draw.value, env) draw.remaining

end Mcmc.Executable.IR
