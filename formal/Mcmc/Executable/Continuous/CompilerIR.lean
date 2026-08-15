import Mcmc.Executable.GaussianRWMH

/-!
# Serializable continuous sampler command IR

This small typed language is the portable algorithm artifact for scalar
Gaussian RWMH.  A target log density is an explicit runtime input; it is not
embedded as an opaque Lean function in the syntax.  The stochastic surface is
limited to ideal standard-normal and unit-uniform draws.
-/

namespace Mcmc.Executable.Continuous.CompilerIR

open Mcmc.Executable

/-- Pure value types needed by scalar continuous RWMH. -/
inductive Ty where
  | real
  | bool
  deriving DecidableEq, Repr

abbrev Ty.denote : Ty → Type
  | .real => ℝ
  | .bool => Bool

/-- Named typed variable in the portable command language. -/
structure Var (type : Ty) where
  name : String
  deriving DecidableEq, Repr

/-- Pure continuous expressions. `logDensity` calls the explicit target input. -/
inductive Expr : Ty → Type where
  | var (value : Var type) : Expr type
  | real (value : Int) : Expr .real
  | add (left right : Expr .real) : Expr .real
  | sub (left right : Expr .real) : Expr .real
  | mul (left right : Expr .real) : Expr .real
  | exp (value : Expr .real) : Expr .real
  | min (left right : Expr .real) : Expr .real
  | lt (left right : Expr .real) : Expr .bool
  | logDensity (value : Expr .real) : Expr .real

/-- First-order continuous commands. -/
inductive Stmt where
  | letE (destination : Var type) (value : Expr type)
  | sampleStandardNormal (destination : Var .real)
  | sampleUniformUnit (destination : Var .real)
  | ifThen (condition : Expr .bool) (body : List Stmt)
  | return (value : Expr .real)

/-- Portable program descriptor with explicit runtime inputs. -/
structure Program where
  name : String
  sourceInput : String
  logDensityInput : String
  realInputs : List String
  body : List Stmt

def noiseVar : Var .real := ⟨"noise"⟩
def proposedVar : Var .real := ⟨"proposed"⟩
def currentLogDensityVar : Var .real := ⟨"current_log_density"⟩
def proposedLogDensityVar : Var .real := ⟨"proposed_log_density"⟩
def thresholdVar : Var .real := ⟨"threshold"⟩
def uniformVar : Var .real := ⟨"uniform"⟩
def scaleVar : Var .real := ⟨"scale"⟩
def currentVar : Var .real := ⟨"current"⟩

/-- Generic scalar Gaussian RWMH algorithm. -/
def gaussianRwmhProgram : Program where
  name := "gaussian_rwmh_step!"
  sourceInput := "source"
  logDensityInput := "logdensity"
  realInputs := [scaleVar.name, currentVar.name]
  body :=
    [.sampleStandardNormal noiseVar,
      .letE proposedVar
        (.add (.var currentVar) (.mul (.var scaleVar) (.var noiseVar))),
      .letE currentLogDensityVar (.logDensity (.var currentVar)),
      .letE proposedLogDensityVar (.logDensity (.var proposedVar)),
      .letE thresholdVar
        (.exp (.min (.real 0)
          (.sub (.var proposedLogDensityVar) (.var currentLogDensityVar)))),
      .sampleUniformUnit uniformVar,
      .ifThen (.lt (.var uniformVar) (.var thresholdVar))
        [.return (.var proposedVar)],
      .return (.var currentVar)]

/-- Runtime environment for the ideal-real Lean interpreter. -/
structure Env where
  trace : List IR.Event
  logDensity : ℝ → ℝ
  reals : List (String × ℝ) := []
  bools : List (String × Bool) := []

private def lookup (name : String) : List (String × α) → Option α
  | [] => none
  | (candidate, value) :: rest =>
      if candidate = name then some value else lookup name rest

private def store (name : String) (value : α) (values : List (String × α)) :
    List (String × α) :=
  (name, value) :: values.filter fun entry => entry.1 != name

private def Env.get {type : Ty} (env : Env) (target : Var type) : Option
    type.denote :=
  match type with
  | .real => lookup target.name env.reals
  | .bool => lookup target.name env.bools

private def Env.set {type : Ty} (env : Env) (target : Var type)
    (value : type.denote) : Env :=
  match type with
  | .real => { env with reals := store target.name value env.reals }
  | .bool => { env with bools := store target.name value env.bools }

/-- Errors of the portable continuous interpreter. -/
inductive RuntimeError where
  | primitive (error : IR.Error)
  | missingVariable (name : String)
  | fuelExhausted
  | programDidNotReturn

private def require (name : String) : Option α → Except RuntimeError α
  | some value => .ok value
  | none => .error (.missingVariable name)

private theorem except_ok_bind (value : α)
    (next : α → Except RuntimeError β) :
    (Except.ok value >>= next) = next value := rfl

/-- Evaluate one pure expression against an explicit target callback. -/
noncomputable def evalExpr : {type : Ty} → Expr type → Env →
    Except RuntimeError (type.denote × Env)
  | _, .var target, env => do
      let value ← require target.name (env.get target)
      return (value, env)
  | _, .real value, env => .ok (value, env)
  | _, .add left right, env => do
      let (left, env) ← evalExpr left env
      let (right, env) ← evalExpr right env
      return (left + right, env)
  | _, .sub left right, env => do
      let (left, env) ← evalExpr left env
      let (right, env) ← evalExpr right env
      return (left - right, env)
  | _, .mul left right, env => do
      let (left, env) ← evalExpr left env
      let (right, env) ← evalExpr right env
      return (left * right, env)
  | _, .exp value, env => do
      let (value, env) ← evalExpr value env
      return (Real.exp value, env)
  | _, .min left right, env => do
      let (left, env) ← evalExpr left env
      let (right, env) ← evalExpr right env
      return (min left right, env)
  | _, .lt left right, env => do
      let (left, env) ← evalExpr left env
      let (right, env) ← evalExpr right env
      return (decide (left < right), env)
  | _, .logDensity value, env => do
      let (value, env) ← evalExpr value env
      return (env.logDensity value, env)

inductive Control where
  | next (env : Env)
  | returned (value : ℝ) (env : Env)

private def Stmt.cost : Stmt → Nat
  | .ifThen _ body => 1 + body.foldl (fun total statement => total + statement.cost) 0
  | _ => 1

private def statementsCost (statements : List Stmt) : Nat :=
  statements.foldl (fun total statement => total + statement.cost) 0

/-- Fuel-indexed ideal-real interpreter. Fuel is exposed only to make recursive
control flow structurally transparent to Lean; public execution derives a
sufficient bound from the syntax. -/
noncomputable def runStatementsFuel : Nat → List Stmt → Env →
    Except RuntimeError Control
  | 0, _, _ => .error .fuelExhausted
  | _ + 1, [], env => .ok (.next env)
  | fuel + 1, statement :: rest, env =>
      match statement with
      | .letE destination value => do
          let (value, env) ← evalExpr value env
          runStatementsFuel fuel rest (env.set destination value)
      | .sampleStandardNormal destination =>
          match IR.Prim.replay .standardNormal env.trace with
          | .error error => .error (.primitive error)
          | .ok draw => runStatementsFuel fuel rest
              ({ env with trace := draw.remaining }.set destination draw.value)
      | .sampleUniformUnit destination =>
          match IR.Prim.replay .uniformUnit env.trace with
          | .error error => .error (.primitive error)
          | .ok draw => runStatementsFuel fuel rest
              ({ env with trace := draw.remaining }.set destination draw.value)
      | .ifThen condition body => do
          let (condition, env) ← evalExpr condition env
          if condition then
            match ← runStatementsFuel fuel body env with
            | .returned value env => return .returned value env
            | .next env => runStatementsFuel fuel rest env
          else runStatementsFuel fuel rest env
      | .return value => do
          let (value, env) ← evalExpr value env
          return .returned value env

/-- Interpret a statement list using the syntax-derived fuel bound. -/
noncomputable def runStatements (statements : List Stmt) (env : Env) :
    Except RuntimeError Control :=
  runStatementsFuel (statementsCost statements + 1) statements env

/-- Execute the generic program with ideal-real inputs and events. -/
noncomputable def runGaussianRwmh (logDensity : ℝ → ℝ) (scale current : ℝ)
    (trace : List IR.Event) : Except RuntimeError (IR.Replay ℝ) := do
  let env : Env :=
    { trace, logDensity,
      reals := [(scaleVar.name, scale), (currentVar.name, current)] }
  match ← runStatements gaussianRwmhProgram.body env with
  | .next _ => .error .programDidNotReturn
  | .returned value env => .ok ⟨value, env.trace⟩

/-- Mathematical standard-Gaussian log weight used by the proved exact
specialization. -/
noncomputable def standardGaussianLogDensity (value : ℝ) : ℝ :=
  -(value * value) / 2

/-- The portable program exposes the complete proposal/accept-or-retain result
on every valid ideal trace. -/
theorem runGaussianRwmh_standard_refines (current noise uniform : ℝ)
    (hunit : 0 ≤ uniform ∧ uniform < 1) (rest : List IR.Event) :
    runGaussianRwmh standardGaussianLogDensity 1 current
        (.standardNormal noise :: .uniformUnit uniform :: rest) =
      .ok ⟨if uniform < standardGaussianAcceptance current (current + noise)
        then current + noise else current, rest⟩ := by
  simp [runGaussianRwmh, runStatements, statementsCost, Stmt.cost,
    gaussianRwmhProgram, runStatementsFuel, evalExpr, Env.get, Env.set, lookup,
    store, require, noiseVar, proposedVar, currentLogDensityVar,
    proposedLogDensityVar, thresholdVar, uniformVar, scaleVar, currentVar,
    IR.Prim.replay, standardGaussianAcceptance]
  simp only [except_ok_bind]
  simp [lookup, hunit, standardGaussianLogDensity]
  simp only [except_ok_bind]
  simp
  have hexponent :
      -((current + noise) * (current + noise)) / 2 - -(current * current) / 2 =
        (current * current - (current + noise) * (current + noise)) * (1 / 2) := by
    ring
  rw [hexponent]
  by_cases haccept : uniform < Real.exp
      (min 0 ((current * current - (current + noise) * (current + noise)) * (2 : ℝ)⁻¹))
  · simp [haccept, except_ok_bind]
  · simp [haccept, except_ok_bind]

end Mcmc.Executable.Continuous.CompilerIR
