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
  | nat
  | realVector
  deriving DecidableEq, Repr

abbrev Ty.denote : Ty → Type
  | .real => ℝ
  | .bool => Bool
  | .nat => Nat
  | .realVector => List ℝ

/-- Named typed variable in the portable command language. -/
structure Var (type : Ty) where
  name : String
  deriving DecidableEq, Repr

/-- Pure continuous expressions. `logDensity` calls the explicit target input. -/
inductive Expr : Ty → Type where
  | var (value : Var type) : Expr type
  | real (value : Int) : Expr .real
  | nat (value : Nat) : Expr .nat
  | add (left right : Expr .real) : Expr .real
  | sub (left right : Expr .real) : Expr .real
  | mul (left right : Expr .real) : Expr .real
  | div (left right : Expr .real) : Expr .real
  | exp (value : Expr .real) : Expr .real
  | min (left right : Expr .real) : Expr .real
  | lt (left right : Expr .real) : Expr .bool
  | logDensity (value : Expr .real) : Expr .real
  | gradient (value : Expr .real) : Expr .real
  | leapfrogPosition (stepSize : Expr .real) (steps : Expr .nat)
      (position momentum : Expr .real) : Expr .real
  | leapfrogMomentum (stepSize : Expr .real) (steps : Expr .nat)
      (position momentum : Expr .real) : Expr .real
  | vectorLogDensity (value : Expr .realVector) : Expr .real
  | vectorGradient (value : Expr .realVector) : Expr .realVector
  | vectorAddScaled (left : Expr .realVector) (scale : Expr .real)
      (right : Expr .realVector) : Expr .realVector
  | vectorSub (left right : Expr .realVector) : Expr .realVector
  | vectorLeapfrogPosition (stepSize : Expr .real) (steps : Expr .nat)
      (position momentum : Expr .realVector) : Expr .realVector
  | vectorLeapfrogMomentum (stepSize : Expr .real) (steps : Expr .nat)
      (position momentum : Expr .realVector) : Expr .realVector
  | vectorGaussLegendrePosition (stepSize : Expr .real) (steps iterations : Expr .nat)
      (position momentum : Expr .realVector) : Expr .realVector
  | vectorGaussLegendreMomentum (stepSize : Expr .real) (steps iterations : Expr .nat)
      (position momentum : Expr .realVector) : Expr .realVector
  | squaredNorm (value : Expr .realVector) : Expr .real

/-- First-order continuous commands. -/
inductive Stmt where
  | letE (destination : Var type) (value : Expr type)
  | sampleStandardNormal (destination : Var .real)
  | sampleUniformUnit (destination : Var .real)
  | sampleStandardNormalVector (destination : Var .realVector)
      (dimension : Expr .nat)
  | ifThen (condition : Expr .bool) (body : List Stmt)
  | return (value : Expr .real)
  | returnVector (value : Expr .realVector)

/-- Portable program descriptor with explicit runtime inputs. -/
structure Program where
  name : String
  sourceInput : String
  logDensityInput : String
  gradientInput : Option String := none
  realInputs : List String
  natInputs : List String := []
  vectorInputs : List String := []
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
  gradient : ℝ → ℝ := fun _ => 0
  vectorLogDensity : List ℝ → ℝ := fun _ => 0
  vectorGradient : List ℝ → List ℝ := fun value => value.map fun _ => 0
  reals : List (String × ℝ) := []
  bools : List (String × Bool) := []
  nats : List (String × Nat) := []
  vectors : List (String × List ℝ) := []

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
  | .nat => lookup target.name env.nats
  | .realVector => lookup target.name env.vectors

private def Env.set {type : Ty} (env : Env) (target : Var type)
    (value : type.denote) : Env :=
  match type with
  | .real => { env with reals := store target.name value env.reals }
  | .bool => { env with bools := store target.name value env.bools }
  | .nat => { env with nats := store target.name value env.nats }
  | .realVector => { env with vectors := store target.name value env.vectors }

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

/-- Pure scalar unit-mass leapfrog iteration used by the portable HMC IR. -/
noncomputable def scalarLeapfrogN (gradient : ℝ → ℝ) (stepSize : ℝ) :
    Nat → ℝ → ℝ → ℝ × ℝ
  | 0, position, momentum => (position, momentum)
  | steps + 1, position, momentum =>
      let previous := scalarLeapfrogN gradient stepSize steps position momentum
      let halfMomentum := previous.2 - stepSize * gradient previous.1 / 2
      let nextPosition := previous.1 + stepSize * halfMomentum
      let nextMomentum := halfMomentum - stepSize * gradient nextPosition / 2
      (nextPosition, nextMomentum)

noncomputable def vectorSubScaled (left : List ℝ) (scale : ℝ)
    (right : List ℝ) : List ℝ :=
  List.zipWith (fun x y => x - scale * y) left right

noncomputable def vectorAddScaled (left : List ℝ) (scale : ℝ)
    (right : List ℝ) : List ℝ :=
  List.zipWith (fun x y => x + scale * y) left right

/-- Dimension-polymorphic, unit-mass leapfrog iteration used by vector HMC. -/
noncomputable def vectorLeapfrogN (gradient : List ℝ → List ℝ)
    (stepSize : ℝ) : Nat → List ℝ → List ℝ → List ℝ × List ℝ
  | 0, position, momentum => (position, momentum)
  | steps + 1, position, momentum =>
      let previous := vectorLeapfrogN gradient stepSize steps position momentum
      let halfMomentum := vectorSubScaled previous.2 (stepSize / 2)
        (gradient previous.1)
      let nextPosition := vectorAddScaled previous.1 stepSize halfMomentum
      let nextMomentum := vectorSubScaled halfMomentum (stepSize / 2)
        (gradient nextPosition)
      (nextPosition, nextMomentum)

private noncomputable def vectorField (gradient : List ℝ → List ℝ)
    (state : List ℝ × List ℝ) : List ℝ × List ℝ :=
  (state.2, (gradient state.1).map (-·))

/-- Fixed-work simultaneous-stage interpretation of two-stage
Gauss--Legendre. The exact Lean theorem is about stage witnesses; this
executable approximation has a declared iteration count. -/
noncomputable def vectorGaussLegendreStep (gradient : List ℝ → List ℝ)
    (stepSize : ℝ) (iterations : Nat) (position momentum : List ℝ) :
    List ℝ × List ℝ :=
  let r := Real.sqrt 3 / 6
  let initial := (position, momentum)
  let initialField := vectorField gradient initial
  let stages := (List.range iterations).foldl (fun stages _ =>
    let firstState :=
      (vectorAddScaled position stepSize
          (vectorAddScaled (stages.1.1.map ((1 / 4) * ·)) 1
            (stages.2.1.map ((1 / 4 - r) * ·))),
       vectorAddScaled momentum stepSize
          (vectorAddScaled (stages.1.2.map ((1 / 4) * ·)) 1
            (stages.2.2.map ((1 / 4 - r) * ·))))
    let secondState :=
      (vectorAddScaled position stepSize
          (vectorAddScaled (stages.1.1.map ((1 / 4 + r) * ·)) 1
            (stages.2.1.map ((1 / 4) * ·))),
       vectorAddScaled momentum stepSize
          (vectorAddScaled (stages.1.2.map ((1 / 4 + r) * ·)) 1
            (stages.2.2.map ((1 / 4) * ·))))
    (vectorField gradient firstState, vectorField gradient secondState))
    (initialField, initialField)
  (vectorAddScaled position (stepSize / 2)
      (vectorAddScaled stages.1.1 1 stages.2.1),
   vectorAddScaled momentum (stepSize / 2)
      (vectorAddScaled stages.1.2 1 stages.2.2))

noncomputable def vectorGaussLegendreN (gradient : List ℝ → List ℝ)
    (stepSize : ℝ) (iterations : Nat) : Nat → List ℝ → List ℝ → List ℝ × List ℝ
  | 0, position, momentum => (position, momentum)
  | steps + 1, position, momentum =>
      let previous := vectorGaussLegendreN gradient stepSize iterations
        steps position momentum
      vectorGaussLegendreStep gradient stepSize iterations previous.1 previous.2

/-- Evaluate one pure expression against an explicit target callback. -/
noncomputable def evalExpr : {type : Ty} → Expr type → Env →
    Except RuntimeError (type.denote × Env)
  | _, .var target, env => do
      let value ← require target.name (env.get target)
      return (value, env)
  | _, .real value, env => .ok (value, env)
  | _, .nat value, env => .ok (value, env)
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
  | _, .div left right, env => do
      let (left, env) ← evalExpr left env
      let (right, env) ← evalExpr right env
      return (left / right, env)
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
  | _, .gradient value, env => do
      let (value, env) ← evalExpr value env
      return (env.gradient value, env)
  | _, .leapfrogPosition stepSize steps position momentum, env => do
      let (stepSize, env) ← evalExpr stepSize env
      let (steps, env) ← evalExpr steps env
      let (position, env) ← evalExpr position env
      let (momentum, env) ← evalExpr momentum env
      return ((scalarLeapfrogN env.gradient stepSize steps position momentum).1, env)
  | _, .leapfrogMomentum stepSize steps position momentum, env => do
      let (stepSize, env) ← evalExpr stepSize env
      let (steps, env) ← evalExpr steps env
      let (position, env) ← evalExpr position env
      let (momentum, env) ← evalExpr momentum env
      return ((scalarLeapfrogN env.gradient stepSize steps position momentum).2, env)
  | _, .vectorLogDensity value, env => do
      let (value, env) ← evalExpr value env
      return (env.vectorLogDensity value, env)
  | _, .vectorGradient value, env => do
      let (value, env) ← evalExpr value env
      return (env.vectorGradient value, env)
  | _, .vectorAddScaled left scale right, env => do
      let (left, env) ← evalExpr left env
      let (scale, env) ← evalExpr scale env
      let (right, env) ← evalExpr right env
      return (vectorAddScaled left scale right, env)
  | _, .vectorSub left right, env => do
      let (left, env) ← evalExpr left env
      let (right, env) ← evalExpr right env
      return (List.zipWith (· - ·) left right, env)
  | _, .vectorLeapfrogPosition stepSize steps position momentum, env => do
      let (stepSize, env) ← evalExpr stepSize env
      let (steps, env) ← evalExpr steps env
      let (position, env) ← evalExpr position env
      let (momentum, env) ← evalExpr momentum env
      return ((vectorLeapfrogN env.vectorGradient stepSize steps position momentum).1, env)
  | _, .vectorLeapfrogMomentum stepSize steps position momentum, env => do
      let (stepSize, env) ← evalExpr stepSize env
      let (steps, env) ← evalExpr steps env
      let (position, env) ← evalExpr position env
      let (momentum, env) ← evalExpr momentum env
      return ((vectorLeapfrogN env.vectorGradient stepSize steps position momentum).2, env)
  | _, .vectorGaussLegendrePosition stepSize steps iterations position momentum, env => do
      let (stepSize, env) ← evalExpr stepSize env
      let (steps, env) ← evalExpr steps env
      let (iterations, env) ← evalExpr iterations env
      let (position, env) ← evalExpr position env
      let (momentum, env) ← evalExpr momentum env
      return ((vectorGaussLegendreN env.vectorGradient stepSize iterations steps position momentum).1, env)
  | _, .vectorGaussLegendreMomentum stepSize steps iterations position momentum, env => do
      let (stepSize, env) ← evalExpr stepSize env
      let (steps, env) ← evalExpr steps env
      let (iterations, env) ← evalExpr iterations env
      let (position, env) ← evalExpr position env
      let (momentum, env) ← evalExpr momentum env
      return ((vectorGaussLegendreN env.vectorGradient stepSize iterations steps position momentum).2, env)
  | _, .squaredNorm value, env => do
      let (value, env) ← evalExpr value env
      return (value.foldl (fun total x => total + x * x) 0, env)

inductive Control where
  | next (env : Env)
  | returned (value : ℝ) (env : Env)
  | returnedVector (value : List ℝ) (env : Env)

private def Stmt.cost : Stmt → Nat
  | .ifThen _ body => 1 + body.foldl (fun total statement => total + statement.cost) 0
  | _ => 1

private def statementsCost (statements : List Stmt) : Nat :=
  statements.foldl (fun total statement => total + statement.cost) 0

/-- Consume exactly `count` standard-normal events. Kept separate from the
statement interpreter so trace consumption can be proved by induction. -/
noncomputable def drawStandardNormalVector : Nat → Env →
    Except RuntimeError (List ℝ × Env)
  | 0, env => .ok ([], env)
  | count + 1, env =>
      match IR.Prim.replay .standardNormal env.trace with
      | .error error => .error (.primitive error)
      | .ok draw => do
          let (tail, env) ← drawStandardNormalVector count
            { env with trace := draw.remaining }
          return (draw.value :: tail, env)

theorem drawStandardNormalVector_replays (values : List ℝ) (env : Env) :
    drawStandardNormalVector values.length
        { env with trace := values.map IR.Event.standardNormal ++ env.trace } =
      .ok (values, env) := by
  induction values generalizing env with
  | nil => rfl
  | cons value values ih =>
      simp [drawStandardNormalVector, IR.Prim.replay, ih]

noncomputable def replayStandardNormalVector : Nat → List IR.Event →
    Except RuntimeError (IR.Replay (List ℝ))
  | 0, trace => .ok ⟨[], trace⟩
  | count + 1, trace =>
      match IR.Prim.replay .standardNormal trace with
      | .error error => .error (.primitive error)
      | .ok draw => do
          let tail ← replayStandardNormalVector count draw.remaining
          return ⟨draw.value :: tail.value, tail.remaining⟩

@[simp] theorem replayStandardNormalVector_replays
    (values : List ℝ) (rest : List IR.Event) :
    replayStandardNormalVector values.length
        (values.map IR.Event.standardNormal ++ rest) = .ok ⟨values, rest⟩ := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp [replayStandardNormalVector, IR.Prim.replay, ih]

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
      | .sampleStandardNormalVector destination dimension => do
          let (dimension, env) ← evalExpr dimension env
          let (values, env) ← drawStandardNormalVector dimension env
          runStatementsFuel fuel rest (env.set destination values)
      | .ifThen condition body => do
          let (condition, env) ← evalExpr condition env
          if condition then
            match ← runStatementsFuel fuel body env with
            | .returned value env => return .returned value env
            | .returnedVector value env => return .returnedVector value env
            | .next env => runStatementsFuel fuel rest env
          else runStatementsFuel fuel rest env
      | .return value => do
          let (value, env) ← evalExpr value env
          return .returned value env
      | .returnVector value => do
          let (value, env) ← evalExpr value env
          return .returnedVector value env

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
  | .returnedVector _ _ => .error .programDidNotReturn

/-- Mathematical standard-Gaussian log weight used by the proved exact
specialization. -/
noncomputable def standardGaussianLogDensity (value : ℝ) : ℝ :=
  -(value * value) / 2

/-- Complete proposal/accept-or-retain behavior for an arbitrary target log
density and proposal scale. -/
theorem runGaussianRwmh_refines (logDensity : ℝ → ℝ) (scale current noise uniform : ℝ)
    (hunit : 0 ≤ uniform ∧ uniform < 1) (rest : List IR.Event) :
    runGaussianRwmh logDensity scale current
        (.standardNormal noise :: .uniformUnit uniform :: rest) =
      .ok ⟨if uniform < Real.exp
          (min 0 (logDensity (current + scale * noise) - logDensity current))
        then current + scale * noise else current, rest⟩ := by
  simp [runGaussianRwmh, runStatements, statementsCost, Stmt.cost,
    gaussianRwmhProgram, runStatementsFuel, evalExpr, Env.get, Env.set, lookup,
    store, require, noiseVar, proposedVar, currentLogDensityVar,
    proposedLogDensityVar, thresholdVar, uniformVar, scaleVar, currentVar,
    IR.Prim.replay]
  simp only [except_ok_bind]
  simp [lookup, hunit]
  simp only [except_ok_bind]
  by_cases haccept : uniform < Real.exp
      (min 0 (logDensity (current + scale * noise) - logDensity current))
  · simp [haccept, except_ok_bind]
  · simp [haccept, except_ok_bind]

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

/-- Variables used by the scalar one-step endpoint HMC program. -/
def momentumVar : Var .real := ⟨"momentum"⟩
def halfMomentumVar : Var .real := ⟨"half_momentum"⟩
def nextPositionVar : Var .real := ⟨"next_position"⟩
def nextMomentumVar : Var .real := ⟨"next_momentum"⟩
def currentEnergyVar : Var .real := ⟨"current_energy"⟩
def nextEnergyVar : Var .real := ⟨"next_energy"⟩
def stepSizeVar : Var .real := ⟨"step_size"⟩
def stepsVar : Var .nat := ⟨"steps"⟩
def dimensionVar : Var .nat := ⟨"dimension"⟩
def vectorCurrentVar : Var .realVector := ⟨"current"⟩
def vectorMomentumVar : Var .realVector := ⟨"momentum"⟩
def vectorNextPositionVar : Var .realVector := ⟨"next_position"⟩
def vectorNextMomentumVar : Var .realVector := ⟨"next_momentum"⟩
def iterationsVar : Var .nat := ⟨"iterations"⟩

def logRatioVar : Var .real := ⟨"log_ratio"⟩

/-- Scalar Gaussian RWMH with Barker's sigmoid acceptance. -/
def gaussianBarkerRwmhProgram : Program where
  name := "scalar_barker_rwmh_step!"
  sourceInput := "source"
  logDensityInput := "logdensity"
  realInputs := [scaleVar.name, currentVar.name]
  body :=
    [.sampleStandardNormal noiseVar,
      .letE proposedVar
        (.add (.var currentVar) (.mul (.var scaleVar) (.var noiseVar))),
      .letE currentLogDensityVar (.logDensity (.var currentVar)),
      .letE proposedLogDensityVar (.logDensity (.var proposedVar)),
      .letE logRatioVar
        (.sub (.var proposedLogDensityVar) (.var currentLogDensityVar)),
      .letE thresholdVar
        (.div (.real 1)
          (.add (.real 1)
            (.exp (.sub (.real 0) (.var logRatioVar))))),
      .sampleUniformUnit uniformVar,
      .ifThen (.lt (.var uniformVar) (.var thresholdVar))
        [.return (.var proposedVar)],
      .return (.var currentVar)]

def malaVarianceVar : Var .real := ⟨"variance"⟩
def malaHalfVarianceVar : Var .real := ⟨"half_variance"⟩
def malaCurrentGradientVar : Var .real := ⟨"current_gradient"⟩
def malaProposedGradientVar : Var .real := ⟨"proposed_gradient"⟩
def malaForwardResidualVar : Var .real := ⟨"forward_residual"⟩
def malaReverseResidualVar : Var .real := ⟨"reverse_residual"⟩
def malaLogRatioVar : Var .real := ⟨"log_ratio"⟩
def malaVectorNoiseVar : Var .realVector := ⟨"noise"⟩
def malaVectorProposedVar : Var .realVector := ⟨"proposed"⟩
def malaVectorCurrentGradientVar : Var .realVector := ⟨"current_gradient"⟩
def malaVectorProposedGradientVar : Var .realVector := ⟨"proposed_gradient"⟩
def malaVectorForwardResidualVar : Var .realVector := ⟨"forward_residual"⟩
def malaVectorReverseResidualVar : Var .realVector := ⟨"reverse_residual"⟩

private def two : Expr .real := .real 2

/-- Scalar isotropic Metropolis-adjusted Langevin transition. `step_size` is
the Gaussian proposal standard deviation. -/
def scalarMalaProgram : Program where
  name := "scalar_mala_step!"
  sourceInput := "source"
  logDensityInput := "logdensity"
  gradientInput := some "gradient"
  realInputs := [stepSizeVar.name, currentVar.name]
  body :=
    [.letE malaVarianceVar (.mul (.var stepSizeVar) (.var stepSizeVar)),
      .letE malaHalfVarianceVar (.div (.var malaVarianceVar) two),
      .letE malaCurrentGradientVar (.gradient (.var currentVar)),
      .sampleStandardNormal noiseVar,
      .letE proposedVar
        (.add (.add (.var currentVar)
          (.mul (.var malaHalfVarianceVar) (.var malaCurrentGradientVar)))
          (.mul (.var stepSizeVar) (.var noiseVar))),
      .letE malaProposedGradientVar (.gradient (.var proposedVar)),
      .letE malaForwardResidualVar
        (.sub (.var proposedVar) (.add (.var currentVar)
          (.mul (.var malaHalfVarianceVar) (.var malaCurrentGradientVar)))),
      .letE malaReverseResidualVar
        (.sub (.var currentVar) (.add (.var proposedVar)
          (.mul (.var malaHalfVarianceVar) (.var malaProposedGradientVar)))),
      .letE malaLogRatioVar
        (.add (.sub (.logDensity (.var proposedVar))
          (.logDensity (.var currentVar)))
          (.div (.sub
            (.mul (.var malaForwardResidualVar) (.var malaForwardResidualVar))
            (.mul (.var malaReverseResidualVar) (.var malaReverseResidualVar)))
            (.mul two (.var malaVarianceVar)))),
      .letE thresholdVar (.exp (.min (.real 0) (.var malaLogRatioVar))),
      .sampleUniformUnit uniformVar,
      .ifThen (.lt (.var uniformVar) (.var thresholdVar))
        [.return (.var proposedVar)],
      .return (.var currentVar)]

/-- Dimension-polymorphic isotropic Metropolis-adjusted Langevin transition. -/
def vectorMalaProgram : Program where
  name := "vector_mala_step!"
  sourceInput := "source"
  logDensityInput := "logdensity"
  gradientInput := some "gradient"
  realInputs := [stepSizeVar.name]
  natInputs := [dimensionVar.name]
  vectorInputs := [vectorCurrentVar.name]
  body :=
    [.letE malaVarianceVar (.mul (.var stepSizeVar) (.var stepSizeVar)),
      .letE malaHalfVarianceVar (.div (.var malaVarianceVar) two),
      .letE malaVectorCurrentGradientVar
        (.vectorGradient (.var vectorCurrentVar)),
      .sampleStandardNormalVector malaVectorNoiseVar (.var dimensionVar),
      .letE malaVectorProposedVar
        (.vectorAddScaled
          (.vectorAddScaled (.var vectorCurrentVar)
            (.var malaHalfVarianceVar) (.var malaVectorCurrentGradientVar))
          (.var stepSizeVar) (.var malaVectorNoiseVar)),
      .letE malaVectorProposedGradientVar
        (.vectorGradient (.var malaVectorProposedVar)),
      .letE malaVectorForwardResidualVar
        (.vectorSub (.var malaVectorProposedVar)
          (.vectorAddScaled (.var vectorCurrentVar)
            (.var malaHalfVarianceVar) (.var malaVectorCurrentGradientVar))),
      .letE malaVectorReverseResidualVar
        (.vectorSub (.var vectorCurrentVar)
          (.vectorAddScaled (.var malaVectorProposedVar)
            (.var malaHalfVarianceVar) (.var malaVectorProposedGradientVar))),
      .letE malaLogRatioVar
        (.add (.sub (.vectorLogDensity (.var malaVectorProposedVar))
          (.vectorLogDensity (.var vectorCurrentVar)))
          (.div (.sub (.squaredNorm (.var malaVectorForwardResidualVar))
            (.squaredNorm (.var malaVectorReverseResidualVar)))
            (.mul two (.var malaVarianceVar)))),
      .letE thresholdVar (.exp (.min (.real 0) (.var malaLogRatioVar))),
      .sampleUniformUnit uniformVar,
      .ifThen (.lt (.var uniformVar) (.var thresholdVar))
        [.returnVector (.var malaVectorProposedVar)],
      .returnVector (.var vectorCurrentVar)]

/-- Scalar, unit-mass endpoint HMC with one leapfrog step. The target supplies
both its log density and the gradient of its negative log density. -/
def scalarHmcProgram : Program where
  name := "scalar_hmc_step!"
  sourceInput := "source"
  logDensityInput := "logdensity"
  gradientInput := some "gradient"
  realInputs := [stepSizeVar.name, currentVar.name]
  natInputs := [stepsVar.name]
  body :=
    [.sampleStandardNormal momentumVar,
      .letE nextPositionVar
        (.leapfrogPosition (.var stepSizeVar) (.var stepsVar)
          (.var currentVar) (.var momentumVar)),
      .letE nextMomentumVar
        (.leapfrogMomentum (.var stepSizeVar) (.var stepsVar)
          (.var currentVar) (.var momentumVar)),
      .letE currentEnergyVar
        (.add (.sub (.real 0) (.logDensity (.var currentVar)))
          (.div (.mul (.var momentumVar) (.var momentumVar)) two)),
      .letE nextEnergyVar
        (.add (.sub (.real 0) (.logDensity (.var nextPositionVar)))
          (.div (.mul (.var nextMomentumVar) (.var nextMomentumVar)) two)),
      .letE thresholdVar
        (.exp (.min (.real 0)
          (.sub (.var currentEnergyVar) (.var nextEnergyVar)))),
      .sampleUniformUnit uniformVar,
      .ifThen (.lt (.var uniformVar) (.var thresholdVar))
        [.return (.var nextPositionVar)],
      .return (.var currentVar)]

/-- Dimension-polymorphic, unit-mass endpoint HMC. Its runtime dimension is
checked against the current position by the maintained interpreters. -/
def vectorHmcProgram : Program where
  name := "vector_hmc_step!"
  sourceInput := "source"
  logDensityInput := "logdensity"
  gradientInput := some "gradient"
  realInputs := [stepSizeVar.name]
  natInputs := [stepsVar.name, dimensionVar.name]
  vectorInputs := [vectorCurrentVar.name]
  body :=
    [.sampleStandardNormalVector vectorMomentumVar (.var dimensionVar),
      .letE vectorNextPositionVar
        (.vectorLeapfrogPosition (.var stepSizeVar) (.var stepsVar)
          (.var vectorCurrentVar) (.var vectorMomentumVar)),
      .letE vectorNextMomentumVar
        (.vectorLeapfrogMomentum (.var stepSizeVar) (.var stepsVar)
          (.var vectorCurrentVar) (.var vectorMomentumVar)),
      .letE currentEnergyVar
        (.add (.sub (.real 0) (.vectorLogDensity (.var vectorCurrentVar)))
          (.div (.squaredNorm (.var vectorMomentumVar)) two)),
      .letE nextEnergyVar
        (.add (.sub (.real 0) (.vectorLogDensity (.var vectorNextPositionVar)))
          (.div (.squaredNorm (.var vectorNextMomentumVar)) two)),
      .letE thresholdVar
        (.exp (.min (.real 0)
          (.sub (.var currentEnergyVar) (.var nextEnergyVar)))),
      .sampleUniformUnit uniformVar,
      .ifThen (.lt (.var uniformVar) (.var thresholdVar))
        [.returnVector (.var vectorNextPositionVar)],
      .returnVector (.var vectorCurrentVar)]

/-- Fixed-work two-stage Gauss--Legendre endpoint HMC artifact. -/
def vectorGaussLegendreHmcProgram : Program where
  name := "vector_gauss_legendre_hmc_step!"
  sourceInput := "source"
  logDensityInput := "logdensity"
  gradientInput := some "gradient"
  realInputs := [stepSizeVar.name]
  natInputs := [stepsVar.name, iterationsVar.name, dimensionVar.name]
  vectorInputs := [vectorCurrentVar.name]
  body :=
    [.sampleStandardNormalVector vectorMomentumVar (.var dimensionVar),
      .letE vectorNextPositionVar
        (.vectorGaussLegendrePosition (.var stepSizeVar) (.var stepsVar)
          (.var iterationsVar) (.var vectorCurrentVar) (.var vectorMomentumVar)),
      .letE vectorNextMomentumVar
        (.vectorGaussLegendreMomentum (.var stepSizeVar) (.var stepsVar)
          (.var iterationsVar) (.var vectorCurrentVar) (.var vectorMomentumVar)),
      .letE currentEnergyVar
        (.add (.sub (.real 0) (.vectorLogDensity (.var vectorCurrentVar)))
          (.div (.squaredNorm (.var vectorMomentumVar)) two)),
      .letE nextEnergyVar
        (.add (.sub (.real 0) (.vectorLogDensity (.var vectorNextPositionVar)))
          (.div (.squaredNorm (.var vectorNextMomentumVar)) two)),
      .letE thresholdVar
        (.exp (.min (.real 0)
          (.sub (.var currentEnergyVar) (.var nextEnergyVar)))),
      .sampleUniformUnit uniformVar,
      .ifThen (.lt (.var uniformVar) (.var thresholdVar))
        [.returnVector (.var vectorNextPositionVar)],
      .returnVector (.var vectorCurrentVar)]

/-- Execute scalar one-step HMC against ideal-real callbacks and events. -/
noncomputable def runScalarHmc (logDensity gradient : ℝ → ℝ)
    (stepSize : ℝ) (steps : Nat) (current : ℝ) (trace : List IR.Event) :
    Except RuntimeError (IR.Replay ℝ) := do
  let env : Env :=
    { trace, logDensity, gradient,
      reals := [(stepSizeVar.name, stepSize), (currentVar.name, current)],
      nats := [(stepsVar.name, steps)] }
  match ← runStatements scalarHmcProgram.body env with
  | .next _ => .error .programDidNotReturn
  | .returned value env => .ok ⟨value, env.trace⟩
  | .returnedVector _ _ => .error .programDidNotReturn

/-- Ideal-real interpretation of the vector HMC program. -/
noncomputable def runVectorHmc (logDensity : List ℝ → ℝ)
    (gradient : List ℝ → List ℝ) (stepSize : ℝ) (steps : Nat)
    (current : List ℝ) (trace : List IR.Event) :
    Except RuntimeError (IR.Replay (List ℝ)) := do
  let momentum ← replayStandardNormalVector current.length trace
  let uniform ← match IR.Prim.replay .uniformUnit momentum.remaining with
    | .error error => .error (.primitive error)
    | .ok draw => .ok draw
  let next := vectorLeapfrogN gradient stepSize steps current momentum.value
  let currentEnergy := -logDensity current +
    momentum.value.foldl (fun total x => total + x * x) 0 / 2
  let nextEnergy := -logDensity next.1 +
    next.2.foldl (fun total x => total + x * x) 0 / 2
  return ⟨if uniform.value < Real.exp (min 0 (currentEnergy - nextEnergy))
    then next.1 else current, uniform.remaining⟩

/-- The vector command consumes one normal event per coordinate followed by
one uniform event and returns precisely the endpoint-corrected HMC result. -/
theorem runVectorHmc_refines (logDensity : List ℝ → ℝ)
    (gradient : List ℝ → List ℝ) (stepSize : ℝ) (steps : Nat)
    (current momentum : List ℝ) (hlen : momentum.length = current.length)
    (uniform : ℝ) (hunit : 0 ≤ uniform ∧ uniform < 1)
    (rest : List IR.Event) :
    let next := vectorLeapfrogN gradient stepSize steps current momentum
    let currentEnergy := -logDensity current +
      momentum.foldl (fun total x => total + x * x) 0 / 2
    let nextEnergy := -logDensity next.1 +
      next.2.foldl (fun total x => total + x * x) 0 / 2
    runVectorHmc logDensity gradient stepSize steps current
        (momentum.map IR.Event.standardNormal ++
          .uniformUnit uniform :: rest) =
      .ok ⟨if uniform < Real.exp (min 0 (currentEnergy - nextEnergy))
        then next.1 else current, rest⟩ := by
  simp [runVectorHmc, ← hlen,
    IR.Prim.replay, hunit, except_ok_bind]

/-- The portable HMC program performs exactly one velocity-Verlet/leapfrog
step followed by the endpoint Hamiltonian correction. -/
theorem runScalarHmc_refines (logDensity gradient : ℝ → ℝ)
    (stepSize current momentum uniform : ℝ) (steps : Nat)
    (hunit : 0 ≤ uniform ∧ uniform < 1) (rest : List IR.Event) :
    let next := scalarLeapfrogN gradient stepSize steps current momentum
    let nextPosition := next.1
    let nextMomentum := next.2
    let currentEnergy := -logDensity current + momentum * momentum / 2
    let nextEnergy := -logDensity nextPosition + nextMomentum * nextMomentum / 2
    runScalarHmc logDensity gradient stepSize steps current
        (.standardNormal momentum :: .uniformUnit uniform :: rest) =
      .ok ⟨if uniform < Real.exp (min 0 (currentEnergy - nextEnergy))
        then nextPosition else current, rest⟩ := by
  simp [runScalarHmc, scalarHmcProgram, runStatements, statementsCost,
    Stmt.cost, runStatementsFuel, evalExpr, Env.get, Env.set, lookup, store,
    require, momentumVar, nextPositionVar, nextMomentumVar,
    currentEnergyVar, nextEnergyVar, stepSizeVar, stepsVar, currentVar,
    thresholdVar, uniformVar, two, IR.Prim.replay, hunit, except_ok_bind]
  by_cases h : uniform < Real.exp (min 0
      (-logDensity current + momentum * momentum / 2 -
        (-logDensity (scalarLeapfrogN gradient stepSize steps current momentum).1 +
          (scalarLeapfrogN gradient stepSize steps current momentum).2 *
            (scalarLeapfrogN gradient stepSize steps current momentum).2 / 2)))
  · simp [h, except_ok_bind]
  · simp [h, except_ok_bind]

end Mcmc.Executable.Continuous.CompilerIR
