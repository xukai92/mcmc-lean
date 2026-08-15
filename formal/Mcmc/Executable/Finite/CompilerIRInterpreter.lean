import Mcmc.Executable.Finite.CompilerIR
import Mcmc.Executable.Finite.MetropolisHastings

/-!
# Deterministic semantics for the finite command IR

The interpreter uses natural-number arithmetic and explicit finite draw
traces. It is the executable Lean semantics of the backend-neutral command IR;
backend validation failures remain distinct from primitive trace failures.
-/

namespace Mcmc.Executable.Finite.CompilerIR

/-- Failures of the command interpreter. -/
inductive RuntimeError where
  | primitive (error : ExecError)
  | program (failure : Failure)
  | missingVariable (name : String)
  | indexOutOfBounds
  deriving DecidableEq, Repr, Inhabited

/-- Runtime store, separated by IR type so lookup never requires an unsafe
cast. -/
structure Env where
  sources : List (String × List DrawEvent) := []
  naturals : List (String × Nat) := []
  booleans : List (String × Bool) := []
  vectors : List (String × List Nat) := []
  matrices : List (String × List (List Nat)) := []
  deriving Inhabited

private def lookup (name : String) : List (String × α) → Option α
  | [] => none
  | (candidate, value) :: rest =>
      if candidate = name then some value else lookup name rest

private def store (name : String) (value : α) : List (String × α) → List (String × α)
  | [] => [(name, value)]
  | (candidate, old) :: rest =>
      if candidate = name then (name, value) :: rest
      else (candidate, old) :: store name value rest

/-- Lean value represented by an IR type. -/
abbrev Ty.denote : Ty → Type
  | .source => List DrawEvent
  | .nat => Nat
  | .bool => Bool
  | .natVector => List Nat
  | .natMatrix => List (List Nat)

private def Env.get {type : Ty} (env : Env) (targetVar : Var type) :
    Option type.denote :=
  match type with
  | .source => lookup targetVar.name env.sources
  | .nat => lookup targetVar.name env.naturals
  | .bool => lookup targetVar.name env.booleans
  | .natVector => lookup targetVar.name env.vectors
  | .natMatrix => lookup targetVar.name env.matrices

private def Env.set {type : Ty} (env : Env) (targetVar : Var type)
    (value : type.denote) : Env :=
  match type with
  | .source => { env with sources := store targetVar.name value env.sources }
  | .nat => { env with naturals := store targetVar.name value env.naturals }
  | .bool => { env with booleans := store targetVar.name value env.booleans }
  | .natVector => { env with vectors := store targetVar.name value env.vectors }
  | .natMatrix => { env with matrices := store targetVar.name value env.matrices }

private def Env.setSource (env : Env) (targetVar : Var .source)
    (value : List DrawEvent) : Env :=
  { env with sources := store targetVar.name value env.sources }

private def require (name : String) : Option α → Except RuntimeError α
  | some value => .ok value
  | none => .error (.missingVariable name)

private def getAt (values : List α) (index : Nat) : Except RuntimeError α :=
  match values[index]? with
  | some value => .ok value
  | none => .error .indexOutOfBounds

private def evalCategoricalPrimitive (source : Var .source)
    (trace : List DrawEvent) (weights : List Nat) (env : Env) :
    Except RuntimeError (Nat × Env) := do
  let total := weights.sum
  let drawResult ← (replayDraw total trace).mapError .primitive
  let index ← match selectFromList weights drawResult.value with
    | some index => .ok index
    | none => .error (.program (.internal "categorical selection failed"))
  return (index, env.setSource source drawResult.remaining)

/-- Evaluate an expression, including trace-consuming categorical calls. -/
def evalExpr : {type : Ty} → Expr type → Env →
    Except RuntimeError (type.denote × Env)
  | _, .var targetVar, env => do
      let value ← require targetVar.name (env.get targetVar)
      return (value, env)
  | _, .nat value, env => .ok (value, env)
  | _, .vector values, env => .ok (values, env)
  | _, .matrix rows, env => .ok (rows, env)
  | _, .add left right, env => do
      let (leftValue, env) ← evalExpr left env
      let (rightValue, env) ← evalExpr right env
      return (Nat.add leftValue rightValue, env)
  | _, .sub left right, env => do
      let (leftValue, env) ← evalExpr left env
      let (rightValue, env) ← evalExpr right env
      return (Nat.sub leftValue rightValue, env)
  | _, .mul left right, env => do
      let (leftValue, env) ← evalExpr left env
      let (rightValue, env) ← evalExpr right env
      return (Nat.mul leftValue rightValue, env)
  | _, .min left right, env => do
      let (leftValue, env) ← evalExpr left env
      let (rightValue, env) ← evalExpr right env
      return (Nat.min leftValue rightValue, env)
  | _, .length value, env => do
      let (values, env) ← evalExpr value env
      return (values.length, env)
  | _, .rowCount value, env => do
      let (rows, env) ← evalExpr value env
      return (rows.length, env)
  | _, .total value, env => do
      let (values, env) ← evalExpr value env
      return (values.sum, env)
  | _, .index value index, env => do
      let (values, env) ← evalExpr value env
      let (index, env) ← evalExpr index env
      return (← getAt values index, env)
  | _, .row value index, env => do
      let (rows, env) ← evalExpr value env
      let (index, env) ← evalExpr index env
      return (← getAt rows index, env)
  | _, .lt left right, env => do
      let (leftValue, env) ← evalExpr left env
      let (rightValue, env) ← evalExpr right env
      return (@decide (Nat.lt leftValue rightValue) (Nat.decLt leftValue rightValue), env)
  | _, .le left right, env => do
      let (leftValue, env) ← evalExpr left env
      let (rightValue, env) ← evalExpr right env
      return (@decide (Nat.le leftValue rightValue) (Nat.decLe leftValue rightValue), env)
  | _, .eq left right, env => do
      let (leftValue, env) ← evalExpr left env
      let (rightValue, env) ← evalExpr right env
      return (@decide (leftValue = rightValue) (Nat.decEq leftValue rightValue), env)
  | _, .and left right, env => do
      let (leftValue, env) ← evalExpr left env
      let (rightValue, env) ← evalExpr right env
      return (leftValue && rightValue, env)
  | _, .allNonnegative value, env => do
      let (_, env) ← evalExpr value env
      return (true, env)
  | _, .allPositive value, env => do
      let (values, env) ← evalExpr value env
      return (values.all fun value => decide (0 < value), env)
  | _, .allRowsLength value size, env => do
      let (rows, env) ← evalExpr value env
      let (size, env) ← evalExpr size env
      return (rows.all fun row => decide (row.length = size), env)
  | _, .allRowsNonnegativePositive value, env => do
      let (rows, env) ← evalExpr value env
      return (rows.all fun row => decide (0 < row.sum), env)
  | _, .toExactVector value, env => evalExpr value env
  | _, .toExactMatrix value, env => evalExpr value env
  | _, .categorical (.var source) weights, env => do
      let trace ← require source.name (env.get source)
      let (weights, env) ← evalExpr weights env
      evalCategoricalPrimitive source trace weights env

/-- Statement-list control outcome. -/
inductive Control where
  | next (env : Env)
  | returned (value : Nat) (env : Env)
  deriving Inhabited

mutual
  /-- Execute a statement list. -/
  def runStatements : List Stmt → Env → Except RuntimeError Control
    | [], env => .ok (.next env)
    | statement :: rest, env => do
        let result ← runStatement statement env
        match result with
        | .returned value env => return .returned value env
        | .next env => runStatements rest env

  private def runStatement : Stmt → Env → Except RuntimeError Control
    | .letE destination value, env => do
        let (value, env) ← evalExpr value env
        return .next (env.set destination value)
    | .guard condition failure, env => do
        let (condition, env) ← evalExpr condition env
        match condition with
        | true => return .next env
        | false => throw (.program failure)
    | .drawBelow destination (.var source) upper, env => do
        let trace ← require source.name (env.get source)
        let (upper, env) ← evalExpr upper env
        let result ← (replayDraw upper trace).mapError .primitive
        return .next ((env.set source result.remaining).set destination result.value)
    | .ifThen condition body, env => do
        let (condition, env) ← evalExpr condition env
        match condition with
        | true => runStatements body env
        | false => return .next env
    | .return value, env => do
        let (value, env) ← evalExpr value env
        return .returned value env
    | .fail failure, _ => throw (.program failure)

end

private theorem runStatements_cons_next (statement : Stmt) (rest : List Stmt)
    (env nextEnv : Env)
    (h : runStatement statement env = .ok (.next nextEnv)) :
  runStatements (statement :: rest) env = runStatements rest nextEnv := by
  rw [runStatements.eq_def]
  simp [h]
  rfl

private theorem runStatements_cons_returned (statement : Stmt) (rest : List Stmt)
    (env nextEnv : Env) (value : Nat)
    (h : runStatement statement env = .ok (.returned value nextEnv)) :
  runStatements (statement :: rest) env = .ok (.returned value nextEnv) := by
  rw [runStatements.eq_def]
  simp [h]
  rfl

private theorem runStatements_cons_error (statement : Stmt) (rest : List Stmt)
    (env : Env) (error : RuntimeError)
    (h : runStatement statement env = .error error) :
    runStatements (statement :: rest) env = .error error := by
  rw [runStatements.eq_def]
  simp [h]
  rfl

/-- Execute a program body from an explicitly prepared environment. -/
def Program.run (program : Program) (env : Env) : Except RuntimeError Control :=
  runStatements program.body env

/-- Initial environment for the finite categorical program. -/
def categoricalEnv (weights : List Nat) (trace : List DrawEvent) : Env where
  sources := [("source", trace)]
  vectors := [("weights", weights)]

/-- Initial environment for the generic finite MH program. -/
def metropolisHastingsEnv (target : List Nat) (proposal : List (List Nat))
    (current : Nat) (trace : List DrawEvent) : Env where
  sources := [("source", trace)]
  naturals := [("current", current)]
  vectors := [("target", target)]
  matrices := [("proposal", proposal)]

/-- Extract the returned state and remaining source trace. -/
def finish (result : Except RuntimeError Control) :
    Except RuntimeError (Nat × List DrawEvent) := do
  match ← result with
  | .next _ => throw (.program (.internal "program did not return"))
  | .returned value env =>
      let trace ← require "source" (lookup "source" env.sources)
      return (value, trace)

/-- Execute the canonical categorical command program. -/
def runCategorical (weights : List Nat) (trace : List DrawEvent) :
    Except RuntimeError (Nat × List DrawEvent) :=
  finish (categoricalProgram.run (categoricalEnv weights trace))

/-- Execute the canonical generic finite MH command program. -/
def runMetropolisHastings (target : List Nat) (proposal : List (List Nat))
    (current : Nat) (trace : List DrawEvent) :
    Except RuntimeError (Nat × List DrawEvent) :=
  finish (metropolisHastingsProgram.run
    (metropolisHastingsEnv target proposal current trace))

private def categoricalPrimitiveReplay (weights : List Nat)
    (trace : List DrawEvent) : Except RuntimeError (Nat × Env) :=
  evalCategoricalPrimitive sourceVar trace weights (categoricalEnv weights trace)

private theorem evalExpr_categorical_eq_primitiveReplay (weights : List Nat)
    (trace : List DrawEvent) :
    evalExpr (.categorical (.var sourceVar) (.var weightsVar))
        (categoricalEnv weights trace) =
      categoricalPrimitiveReplay weights trace := by
  rfl

private theorem categoricalPrimitiveReplay_error {n : Nat}
    (weights : NatWeights n) (trace : List DrawEvent) (error : ExecError)
    (hdraw : replayDraw weights.total trace = .error error) :
    categoricalPrimitiveReplay weights.weightList trace =
      .error (.primitive error) := by
  unfold categoricalPrimitiveReplay
  dsimp [evalCategoricalPrimitive]
  rw [NatWeights.sum_weightList, hdraw]
  rfl

private theorem categoricalPrimitiveReplay_ok {n : Nat}
    (weights : NatWeights n) (trace : List DrawEvent) (drawResult : DrawResult)
    (hdraw : replayDraw weights.total trace = .ok drawResult) :
    categoricalPrimitiveReplay weights.weightList trace =
      .ok ((weights.select ⟨drawResult.value,
        replayDraw_success_value_lt hdraw⟩).val,
        categoricalEnv weights.weightList drawResult.remaining) := by
  have hselect : selectFromList weights.weightList drawResult.value =
      some (weights.select ⟨drawResult.value,
        replayDraw_success_value_lt hdraw⟩).val :=
    (weights.select_val_eq_iff
      ⟨drawResult.value, replayDraw_success_value_lt hdraw⟩ _).mp rfl
  unfold categoricalPrimitiveReplay
  dsimp [evalCategoricalPrimitive]
  rw [NatWeights.sum_weightList, hdraw]
  change (match selectFromList weights.weightList drawResult.value with
    | some index => Except.ok (ε := RuntimeError)
        (index, categoricalEnv weights.weightList drawResult.remaining)
    | none => Except.error
        (RuntimeError.program (.internal "categorical selection failed"))) = _
  rw [hselect]

/-- The IR categorical primitive consumes exactly the established bounded
draw and selects the same proof-carrying finite index. -/
theorem evalExpr_categorical_refines {n : Nat} (weights : NatWeights n)
    (trace : List DrawEvent) :
    evalExpr (.categorical (.var sourceVar) (.var weightsVar))
        (categoricalEnv weights.weightList trace) =
      match replayCategorical weights trace with
      | .error error => .error (.primitive error)
      | .ok (index, rest) =>
          .ok (index.val,
            (categoricalEnv weights.weightList trace).set sourceVar rest) := by
  rw [evalExpr_categorical_eq_primitiveReplay]
  cases hdraw : replayDraw weights.total trace with
  | error error =>
      rw [categoricalPrimitiveReplay_error weights trace error hdraw]
      have hreplay : replayCategorical weights trace = .error error := by
        unfold replayCategorical
        split <;> simp_all
      rw [hreplay]
  | ok drawResult =>
      rw [categoricalPrimitiveReplay_ok weights trace drawResult hdraw]
      have hreplay : replayCategorical weights trace =
          .ok (weights.select ⟨drawResult.value,
            replayDraw_success_value_lt hdraw⟩, drawResult.remaining) := by
        unfold replayCategorical
        split
        · simp_all
        · rename_i other heq
          have hsame : other = drawResult := by
            rw [hdraw] at heq
            exact (Except.ok.inj heq).symm
          subst other
          rfl
      rw [hreplay]
      rfl

/-- Embed the proof-carrying categorical replay result into the raw index
encoding returned by the serializable IR. -/
def liftCategoricalResult {n : Nat} :
    Except ExecError (Fin n × List DrawEvent) →
      Except RuntimeError (Nat × List DrawEvent)
  | .error error => .error (.primitive error)
  | .ok (index, rest) => .ok (index.val, rest)

/-- The complete categorical command program agrees with the established
replay semantics for every positive-total weight vector and trace. -/
theorem runCategorical_refines {n : Nat} (weights : NatWeights n)
    (trace : List DrawEvent) :
    runCategorical weights.weightList trace =
      liftCategoricalResult (replayCategorical weights trace) := by
  let selected : Var .nat := ⟨"selected"⟩
  let env0 := categoricalEnv weights.weightList trace
  cases hreplay : replayCategorical weights trace with
  | error error =>
      have heval : evalExpr (.categorical (.var sourceVar) (.var weightsVar)) env0 =
          .error (.primitive error) := by
        simpa [env0, hreplay] using evalExpr_categorical_refines weights trace
      have hstatement : runStatement
          (.letE selected (.categorical (.var sourceVar) (.var weightsVar))) env0 =
          .error (.primitive error) := by
        unfold runStatement
        rw [heval]
        rfl
      unfold runCategorical Program.run
      rw [show categoricalProgram.body =
        [.letE selected (.categorical (.var sourceVar) (.var weightsVar)),
          .return (.var selected)] by rfl]
      rw [runStatements_cons_error _ _ _ _ hstatement]
      rfl
  | ok result =>
      rcases result with ⟨index, rest⟩
      let env1 := (env0.set sourceVar rest).set selected index.val
      have heval : evalExpr (.categorical (.var sourceVar) (.var weightsVar)) env0 =
          .ok (index.val, env0.set sourceVar rest) := by
        simpa [env0, hreplay] using evalExpr_categorical_refines weights trace
      have hfirst : runStatement
          (.letE selected (.categorical (.var sourceVar) (.var weightsVar))) env0 =
          .ok (.next env1) := by
        unfold runStatement
        rw [heval]
        rfl
      have hsecond : runStatement (.return (.var selected)) env1 =
          .ok (.returned index.val env1) := by
        simp [runStatement, evalExpr, env1, env0, categoricalEnv, Env.get,
          Env.set, lookup, store, require, selected, sourceVar]
      unfold runCategorical Program.run
      rw [show categoricalProgram.body =
        [.letE selected (.categorical (.var sourceVar) (.var weightsVar)),
          .return (.var selected)] by rfl]
      rw [runStatements_cons_next _ _ _ _ hfirst]
      rw [runStatements_cons_returned _ _ _ _ _ hsecond]
      simp [finish, env1, env0, categoricalEnv, Env.set,
        store, require, selected, sourceVar]
      rfl

/-- Stable list encoding of the proposal rows in `Fin` order. -/
def proposalRowLists {n : Nat} (proposal : NatKernelWeights n) :
    List (List Nat) :=
  List.ofFn fun state => (proposal.row state).weightList

@[simp]
theorem length_proposalRowLists {n : Nat}
    (proposal : NatKernelWeights n) : (proposalRowLists proposal).length = n := by
  simp [proposalRowLists]

@[simp]
theorem proposalRowLists_getElem {n : Nat}
    (proposal : NatKernelWeights n) (state : Fin n) :
    (proposalRowLists proposal)[state.val] = (proposal.row state).weightList := by
  simp [proposalRowLists]

@[simp]
private theorem getAt_proposalRowLists {n : Nat}
    (proposal : NatKernelWeights n) (state : Fin n) :
    getAt (proposalRowLists proposal) state.val =
      .ok (proposal.row state).weightList := by
  unfold getAt
  rw [List.getElem?_eq_getElem (by simp)]
  simp

@[simp]
private theorem getAt_weightList {n : Nat} (weights : NatWeights n)
    (state : Fin n) :
    getAt weights.weightList state.val = .ok (weights.weight state) := by
  unfold getAt
  rw [List.getElem?_eq_getElem (by simp)]
  simp [NatWeights.weightList]

private theorem evalExpr_mhRow {n : Nat}
    (target : PositiveNatWeights n) (proposal : NatKernelWeights n)
    (current : Fin n) (trace : List DrawEvent) :
    evalExpr (.row (.var proposalVar) (.var currentVar))
        (metropolisHastingsEnv target.weightList (proposalRowLists proposal)
          current.val trace) =
      .ok ((proposal.row current).weightList,
        metropolisHastingsEnv target.weightList (proposalRowLists proposal)
          current.val trace) := by
  change (do
    let row ← getAt (proposalRowLists proposal) current.val
    return (row, metropolisHastingsEnv target.weightList
      (proposalRowLists proposal) current.val trace)) = _
  rw [getAt_proposalRowLists]
  rfl

private theorem evalExpr_mhCategorical_error {n : Nat}
    (target : PositiveNatWeights n) (proposal : NatKernelWeights n)
    (current : Fin n) (trace : List DrawEvent) (error : ExecError)
    (hdraw : replayDraw (proposal.row current).total trace = .error error) :
    evalExpr
        (.categorical (.var sourceVar)
          (.row (.var proposalVar) (.var currentVar)))
        (metropolisHastingsEnv target.weightList (proposalRowLists proposal)
          current.val trace) =
      .error (.primitive error) := by
  unfold evalExpr
  rw [show require sourceVar.name
      ((metropolisHastingsEnv target.weightList (proposalRowLists proposal)
        current.val trace).get sourceVar) = .ok trace by rfl]
  rw [evalExpr_mhRow target proposal current trace]
  change evalCategoricalPrimitive sourceVar trace
    (proposal.row current).weightList
    (metropolisHastingsEnv target.weightList (proposalRowLists proposal)
      current.val trace) = _
  dsimp [evalCategoricalPrimitive]
  rw [NatWeights.sum_weightList, hdraw]
  rfl

private theorem evalExpr_mhCategorical_ok {n : Nat}
    (target : PositiveNatWeights n) (proposal : NatKernelWeights n)
    (current : Fin n) (trace : List DrawEvent) (drawResult : DrawResult)
    (hdraw : replayDraw (proposal.row current).total trace = .ok drawResult) :
    evalExpr
        (.categorical (.var sourceVar)
          (.row (.var proposalVar) (.var currentVar)))
        (metropolisHastingsEnv target.weightList (proposalRowLists proposal)
          current.val trace) =
      .ok ((proposal.row current).select
          ⟨drawResult.value, replayDraw_success_value_lt hdraw⟩ |>.val,
        (metropolisHastingsEnv target.weightList (proposalRowLists proposal)
          current.val trace).setSource sourceVar drawResult.remaining) := by
  have hselect : selectFromList (proposal.row current).weightList drawResult.value =
      some ((proposal.row current).select
        ⟨drawResult.value, replayDraw_success_value_lt hdraw⟩).val :=
    ((proposal.row current).select_val_eq_iff
      ⟨drawResult.value, replayDraw_success_value_lt hdraw⟩ _).mp rfl
  unfold evalExpr
  rw [show require sourceVar.name
      ((metropolisHastingsEnv target.weightList (proposalRowLists proposal)
        current.val trace).get sourceVar) = .ok trace by rfl]
  rw [evalExpr_mhRow target proposal current trace]
  change evalCategoricalPrimitive sourceVar trace
    (proposal.row current).weightList
    (metropolisHastingsEnv target.weightList (proposalRowLists proposal)
      current.val trace) = _
  dsimp [evalCategoricalPrimitive]
  rw [NatWeights.sum_weightList, hdraw]
  change (match selectFromList (proposal.row current).weightList drawResult.value with
    | some index => Except.ok (ε := RuntimeError)
        (index, (metropolisHastingsEnv target.weightList (proposalRowLists proposal)
          current.val trace).setSource sourceVar drawResult.remaining)
    | none => Except.error
        (RuntimeError.program (.internal "categorical selection failed"))) = _
  rw [hselect]

private theorem runMHProgram_proposal_error {n : Nat}
    (target : PositiveNatWeights n) (proposal : NatKernelWeights n)
    (current : Fin n) (trace : List DrawEvent) (error : ExecError)
    (hdraw : replayDraw (proposal.row current).total trace = .error error) :
    metropolisHastingsProgram.run
        (metropolisHastingsEnv target.weightList (proposalRowLists proposal)
          current.val trace) =
      .error (.primitive error) := by
  let env0 := metropolisHastingsEnv target.weightList (proposalRowLists proposal)
    current.val trace
  have hfirst : runStatement
      (.letE proposedVar (.categorical (.var sourceVar)
        (.row (.var proposalVar) (.var currentVar)))) env0 =
      .error (.primitive error) := by
    unfold runStatement
    rw [evalExpr_mhCategorical_error target proposal current trace error hdraw]
    rfl
  unfold Program.run metropolisHastingsProgram
  rw [show metropolisHastingsBody =
      (.letE proposedVar (.categorical (.var sourceVar)
        (.row (.var proposalVar) (.var currentVar)))) ::
        metropolisHastingsBody.tail by rfl]
  exact runStatements_cons_error _ _ _ _ hfirst

private def mhEnvAfterProposal {n : Nat}
    (target : PositiveNatWeights n) (proposal : NatKernelWeights n)
    (current : Fin n) (trace : List DrawEvent) (drawResult : DrawResult)
    (hdraw : replayDraw (proposal.row current).total trace = .ok drawResult) : Env :=
  ((metropolisHastingsEnv target.weightList (proposalRowLists proposal)
      current.val trace).setSource sourceVar drawResult.remaining).set proposedVar
    ((proposal.row current).select
      ⟨drawResult.value, replayDraw_success_value_lt hdraw⟩).val

private theorem runMetropolisHastings_afterProposal {n : Nat}
    (target : PositiveNatWeights n) (proposal : NatKernelWeights n)
    (current : Fin n) (trace : List DrawEvent) (drawResult : DrawResult)
    (hdraw : replayDraw (proposal.row current).total trace = .ok drawResult) :
    runMetropolisHastings target.weightList (proposalRowLists proposal)
        current.val trace =
      finish (runStatements metropolisHastingsBody.tail
        (mhEnvAfterProposal target proposal current trace drawResult hdraw)) := by
  let env0 := metropolisHastingsEnv target.weightList (proposalRowLists proposal)
    current.val trace
  have hfirst : runStatement
      (.letE proposedVar (.categorical (.var sourceVar)
        (.row (.var proposalVar) (.var currentVar)))) env0 =
      .ok (.next (mhEnvAfterProposal target proposal current trace drawResult hdraw)) := by
    unfold runStatement
    rw [evalExpr_mhCategorical_ok target proposal current trace drawResult hdraw]
    rfl
  unfold runMetropolisHastings Program.run metropolisHastingsProgram
  change finish (runStatements metropolisHastingsBody env0) = _
  rw [show metropolisHastingsBody =
      (.letE proposedVar (.categorical (.var sourceVar)
        (.row (.var proposalVar) (.var currentVar)))) ::
        metropolisHastingsBody.tail by rfl]
  rw [runStatements_cons_next _ _ _ _ hfirst]
  rfl

private theorem runMetropolisHastings_afterOffdiagProposal {n : Nat}
    (target : PositiveNatWeights n) (proposal : NatKernelWeights n)
    (current : Fin n) (trace : List DrawEvent) (drawResult : DrawResult)
    (hdraw : replayDraw (proposal.row current).total trace = .ok drawResult)
    (hself : (proposal.row current).select
      ⟨drawResult.value, replayDraw_success_value_lt hdraw⟩ ≠ current) :
    runMetropolisHastings target.weightList (proposalRowLists proposal)
        current.val trace =
      finish (runStatements metropolisHastingsBody.tail.tail
        (mhEnvAfterProposal target proposal current trace drawResult hdraw)) := by
  let env1 := mhEnvAfterProposal target proposal current trace drawResult hdraw
  have hselfVal : ((proposal.row current).select
      ⟨drawResult.value, replayDraw_success_value_lt hdraw⟩).val ≠ current.val := by
    intro h
    exact hself (Fin.ext h)
  have hsecond : runStatement
      (.ifThen (.eq (.var proposedVar) (.var currentVar))
        [.return (.var currentVar)]) env1 = .ok (.next env1) := by
    simp [runStatement, evalExpr, env1, mhEnvAfterProposal,
      metropolisHastingsEnv, Env.get, Env.set, Env.setSource, lookup, store,
      require, proposedVar, currentVar, sourceVar]
    simp only [bind, Except.bind]
    simp [lookup]
    split <;> simp_all
    all_goals rfl
  rw [runMetropolisHastings_afterProposal target proposal current trace drawResult hdraw]
  rw [show metropolisHastingsBody.tail =
      (.ifThen (.eq (.var proposedVar) (.var currentVar))
        [.return (.var currentVar)]) :: metropolisHastingsBody.tail.tail by rfl]
  rw [runStatements_cons_next _ _ _ _ hsecond]
  rfl

private theorem evalExpr_mhUpper {n : Nat}
    (target : PositiveNatWeights n) (proposal : NatKernelWeights n)
    (current : Fin n) (trace : List DrawEvent) (drawResult : DrawResult)
    (hdraw : replayDraw (proposal.row current).total trace = .ok drawResult) :
    evalExpr mhUpper
        (mhEnvAfterProposal target proposal current trace drawResult hdraw) =
      .ok (proposal.acceptanceUpper target current
          ((proposal.row current).select
            ⟨drawResult.value, replayDraw_success_value_lt hdraw⟩),
        mhEnvAfterProposal target proposal current trace drawResult hdraw) := by
  simp [mhUpper, mhCurrentRow, mhProposedRow, evalExpr, mhEnvAfterProposal,
    metropolisHastingsEnv, Env.get, Env.set, Env.setSource, lookup, store,
    require, targetVar, proposalVar, currentVar, proposedVar,
    NatKernelWeights.acceptanceUpper]
  simp only [bind, Except.bind]
  simp [lookup, getAt_proposalRowLists, getAt_weightList,
    NatWeights.sum_weightList]

private theorem evalExpr_mhThreshold {n : Nat}
    (target : PositiveNatWeights n) (proposal : NatKernelWeights n)
    (current : Fin n) (trace : List DrawEvent) (drawResult : DrawResult)
    (hdraw : replayDraw (proposal.row current).total trace = .ok drawResult) :
    evalExpr mhThreshold
        (mhEnvAfterProposal target proposal current trace drawResult hdraw) =
      .ok (proposal.acceptanceThreshold target current
          ((proposal.row current).select
            ⟨drawResult.value, replayDraw_success_value_lt hdraw⟩),
        mhEnvAfterProposal target proposal current trace drawResult hdraw) := by
  simp [mhThreshold, mhUpper, mhCurrentRow, mhProposedRow, evalExpr,
    mhEnvAfterProposal, metropolisHastingsEnv, Env.get, Env.set, Env.setSource,
    lookup, store, require, targetVar, proposalVar, currentVar, proposedVar,
    NatKernelWeights.acceptanceUpper, NatKernelWeights.acceptanceThreshold]
  simp only [bind, Except.bind]
  simp [lookup, getAt_proposalRowLists, getAt_weightList,
    NatWeights.sum_weightList]

private theorem runMetropolisHastings_acceptanceError {n : Nat}
    (target : PositiveNatWeights n) (proposal : NatKernelWeights n)
    (current : Fin n) (trace : List DrawEvent) (proposalDraw : DrawResult)
    (hproposalDraw : replayDraw (proposal.row current).total trace = .ok proposalDraw)
    (hself : (proposal.row current).select
      ⟨proposalDraw.value, replayDraw_success_value_lt hproposalDraw⟩ ≠ current)
    (error : ExecError)
    (hacceptDraw : replayDraw (proposal.acceptanceUpper target current
        ((proposal.row current).select
          ⟨proposalDraw.value, replayDraw_success_value_lt hproposalDraw⟩))
        proposalDraw.remaining = .error error) :
    runMetropolisHastings target.weightList (proposalRowLists proposal)
        current.val trace = .error (.primitive error) := by
  let env1 := mhEnvAfterProposal target proposal current trace proposalDraw hproposalDraw
  have hsource : require sourceVar.name (env1.get sourceVar) =
      .ok proposalDraw.remaining := by rfl
  have hdrawStatement : runStatement
      (.drawBelow drawVar (.var sourceVar) mhUpper) env1 =
      .error (.primitive error) := by
    unfold runStatement
    rw [hsource]
    rw [evalExpr_mhUpper target proposal current trace proposalDraw hproposalDraw]
    simp only [bind, Except.bind]
    rw [hacceptDraw]
    rfl
  rw [runMetropolisHastings_afterOffdiagProposal target proposal current trace
    proposalDraw hproposalDraw hself]
  rw [show metropolisHastingsBody.tail.tail =
      (.drawBelow drawVar (.var sourceVar) mhUpper) ::
        metropolisHastingsBody.tail.tail.tail by rfl]
  rw [runStatements_cons_error _ _ _ _ hdrawStatement]
  rfl

private theorem evalExpr_mhThreshold_afterDraw {n : Nat}
    (target : PositiveNatWeights n) (proposal : NatKernelWeights n)
    (current : Fin n) (trace : List DrawEvent) (proposalDraw acceptDraw : DrawResult)
    (hproposalDraw : replayDraw (proposal.row current).total trace = .ok proposalDraw) :
    let env := ((mhEnvAfterProposal target proposal current trace proposalDraw
      hproposalDraw).set sourceVar acceptDraw.remaining).set drawVar acceptDraw.value
    evalExpr mhThreshold env =
      .ok (proposal.acceptanceThreshold target current
          ((proposal.row current).select
            ⟨proposalDraw.value, replayDraw_success_value_lt hproposalDraw⟩), env) := by
  simp [mhThreshold, mhUpper, mhCurrentRow, mhProposedRow, evalExpr,
    mhEnvAfterProposal, metropolisHastingsEnv, Env.get, Env.set, Env.setSource,
    lookup, store, require, targetVar, proposalVar, currentVar, proposedVar,
    sourceVar, drawVar, NatKernelWeights.acceptanceUpper,
    NatKernelWeights.acceptanceThreshold]
  simp only [bind, Functor.map, Except.bind, Except.map]
  simp [lookup, getAt_proposalRowLists, getAt_weightList, NatWeights.sum_weightList]

private theorem evalExpr_mhDecision_afterDraw {n : Nat}
    (target : PositiveNatWeights n) (proposal : NatKernelWeights n)
    (current : Fin n) (trace : List DrawEvent) (proposalDraw acceptDraw : DrawResult)
    (hproposalDraw : replayDraw (proposal.row current).total trace = .ok proposalDraw) :
    let env := ((mhEnvAfterProposal target proposal current trace proposalDraw
      hproposalDraw).set sourceVar acceptDraw.remaining).set drawVar acceptDraw.value
    evalExpr (.lt (.var drawVar) mhThreshold) env =
      .ok (acceptDraw.value < proposal.acceptanceThreshold target current
          ((proposal.row current).select
            ⟨proposalDraw.value, replayDraw_success_value_lt hproposalDraw⟩), env) := by
  dsimp only
  let env := ((mhEnvAfterProposal target proposal current trace proposalDraw
    hproposalDraw).set sourceVar acceptDraw.remaining).set drawVar acceptDraw.value
  change evalExpr (.lt (.var drawVar) mhThreshold) env = _
  have hdraw : evalExpr (.var drawVar) env = .ok (acceptDraw.value, env) := by
    simp [evalExpr, env, mhEnvAfterProposal, metropolisHastingsEnv, Env.get,
      Env.set, Env.setSource, lookup, store, require, sourceVar, drawVar,
      proposedVar]
  have hthreshold : evalExpr mhThreshold env =
      .ok (proposal.acceptanceThreshold target current
        ((proposal.row current).select
          ⟨proposalDraw.value, replayDraw_success_value_lt hproposalDraw⟩), env) := by
    simpa [env] using evalExpr_mhThreshold_afterDraw target proposal current trace
      proposalDraw acceptDraw hproposalDraw
  unfold evalExpr
  rw [hdraw]
  simp only [bind, Except.bind]
  rw [hthreshold]
  rfl

private theorem runMetropolisHastings_acceptanceOk {n : Nat}
    (target : PositiveNatWeights n) (proposal : NatKernelWeights n)
    (current : Fin n) (trace : List DrawEvent) (proposalDraw acceptDraw : DrawResult)
    (hproposalDraw : replayDraw (proposal.row current).total trace = .ok proposalDraw)
    (hself : (proposal.row current).select
      ⟨proposalDraw.value, replayDraw_success_value_lt hproposalDraw⟩ ≠ current)
    (hacceptDraw : replayDraw (proposal.acceptanceUpper target current
        ((proposal.row current).select
          ⟨proposalDraw.value, replayDraw_success_value_lt hproposalDraw⟩))
        proposalDraw.remaining = .ok acceptDraw) :
    runMetropolisHastings target.weightList (proposalRowLists proposal)
        current.val trace =
      if acceptDraw.value < proposal.acceptanceThreshold target current
          ((proposal.row current).select
            ⟨proposalDraw.value, replayDraw_success_value_lt hproposalDraw⟩) then
        .ok (((proposal.row current).select
          ⟨proposalDraw.value, replayDraw_success_value_lt hproposalDraw⟩).val,
          acceptDraw.remaining)
      else .ok (current.val, acceptDraw.remaining) := by
  let proposed := (proposal.row current).select
    ⟨proposalDraw.value, replayDraw_success_value_lt hproposalDraw⟩
  let env1 := mhEnvAfterProposal target proposal current trace proposalDraw hproposalDraw
  let env2 := (env1.set sourceVar acceptDraw.remaining).set drawVar acceptDraw.value
  have hsource : require sourceVar.name (env1.get sourceVar) =
      .ok proposalDraw.remaining := by rfl
  have hdrawStatement : runStatement
      (.drawBelow drawVar (.var sourceVar) mhUpper) env1 = .ok (.next env2) := by
    unfold runStatement
    rw [hsource]
    rw [evalExpr_mhUpper target proposal current trace proposalDraw hproposalDraw]
    simp only [bind, Except.bind]
    rw [hacceptDraw]
    rfl
  have hproposed : evalExpr (.var proposedVar) env2 = .ok (proposed.val, env2) := by
    simp [evalExpr, env2, env1, proposed, mhEnvAfterProposal,
      metropolisHastingsEnv, Env.get, Env.set, Env.setSource, lookup, store,
      require, proposedVar, sourceVar, drawVar]
  have hcurrent : evalExpr (.var currentVar) env2 = .ok (current.val, env2) := by
    simp [evalExpr, env2, env1, mhEnvAfterProposal, metropolisHastingsEnv,
      Env.get, Env.set, Env.setSource, lookup, store, require, currentVar,
      proposedVar, sourceVar, drawVar]
  have hremaining : require sourceVar.name (env2.get sourceVar) =
      .ok acceptDraw.remaining := by rfl
  rw [runMetropolisHastings_afterOffdiagProposal target proposal current trace
    proposalDraw hproposalDraw hself]
  rw [show metropolisHastingsBody.tail.tail =
      (.drawBelow drawVar (.var sourceVar) mhUpper) ::
        metropolisHastingsBody.tail.tail.tail by rfl]
  rw [runStatements_cons_next _ _ _ _ hdrawStatement]
  by_cases haccept : acceptDraw.value <
      proposal.acceptanceThreshold target current proposed
  · have hif : runStatement
        (.ifThen (.lt (.var drawVar) mhThreshold) [.return (.var proposedVar)])
        env2 = .ok (.returned proposed.val env2) := by
      unfold runStatement
      rw [evalExpr_mhDecision_afterDraw target proposal current trace proposalDraw
        acceptDraw hproposalDraw]
      change (match decide (acceptDraw.value <
          proposal.acceptanceThreshold target current proposed) with
        | true => runStatements [.return (.var proposedVar)] env2
        | false => pure (.next env2)) = _
      simp [haccept, runStatements, runStatement, hproposed]
      rfl
    rw [show metropolisHastingsBody.tail.tail.tail =
        (.ifThen (.lt (.var drawVar) mhThreshold) [.return (.var proposedVar)]) ::
          metropolisHastingsBody.tail.tail.tail.tail by rfl]
    rw [runStatements_cons_returned _ _ _ _ _ hif]
    change finish (.ok (.returned proposed.val env2)) = _
    rw [if_pos (by simpa [proposed] using haccept)]
    unfold finish
    simp only [bind, Except.bind]
    rw [show require "source" (lookup "source" env2.sources) =
      .ok acceptDraw.remaining by
        simpa [sourceVar, Env.get] using hremaining]
    rfl
  · have hif : runStatement
        (.ifThen (.lt (.var drawVar) mhThreshold) [.return (.var proposedVar)])
        env2 = .ok (.next env2) := by
      unfold runStatement
      rw [evalExpr_mhDecision_afterDraw target proposal current trace proposalDraw
        acceptDraw hproposalDraw]
      change (match decide (acceptDraw.value <
          proposal.acceptanceThreshold target current proposed) with
        | true => runStatements [.return (.var proposedVar)] env2
        | false => pure (.next env2)) = _
      simp [haccept]
      rfl
    rw [show metropolisHastingsBody.tail.tail.tail =
        (.ifThen (.lt (.var drawVar) mhThreshold) [.return (.var proposedVar)]) ::
          metropolisHastingsBody.tail.tail.tail.tail by rfl]
    rw [runStatements_cons_next _ _ _ _ hif]
    change finish (runStatements metropolisHastingsBody.tail.tail.tail.tail env2) = _
    rw [show metropolisHastingsBody.tail.tail.tail.tail =
      [.return (.var currentVar)] by rfl]
    rw [if_neg (by simpa [proposed] using haccept)]
    have hreturn : runStatements [.return (.var currentVar)] env2 =
        .ok (.returned current.val env2) := by
      simp [runStatements, runStatement, hcurrent]
      rfl
    rw [hreturn]
    unfold finish
    simp only [bind, Except.bind]
    rw [show require "source" (lookup "source" env2.sources) =
      .ok acceptDraw.remaining by
        simpa [sourceVar, Env.get] using hremaining]
    rfl

private theorem runMetropolisHastings_self {n : Nat}
    (target : PositiveNatWeights n) (proposal : NatKernelWeights n)
    (current : Fin n) (trace : List DrawEvent)
    (drawResult : DrawResult)
    (hdraw : replayDraw (proposal.row current).total trace = .ok drawResult)
    (hself : (proposal.row current).select
      ⟨drawResult.value, replayDraw_success_value_lt hdraw⟩ = current) :
    runMetropolisHastings target.weightList (proposalRowLists proposal)
        current.val trace = .ok (current.val, drawResult.remaining) := by
  let env0 := metropolisHastingsEnv target.weightList (proposalRowLists proposal)
    current.val trace
  let selected := (proposal.row current).select
    ⟨drawResult.value, replayDraw_success_value_lt hdraw⟩
  let env1 := (env0.setSource sourceVar drawResult.remaining).set proposedVar selected.val
  have hselfVal : ((proposal.row current).select
      ⟨drawResult.value, replayDraw_success_value_lt hdraw⟩).val = current.val :=
    congrArg Fin.val hself
  have hfirst : runStatement
      (.letE proposedVar (.categorical (.var sourceVar)
        (.row (.var proposalVar) (.var currentVar)))) env0 =
      .ok (.next env1) := by
    unfold runStatement
    rw [evalExpr_mhCategorical_ok target proposal current trace drawResult hdraw]
    rfl
  have hsecond : runStatement
      (.ifThen (.eq (.var proposedVar) (.var currentVar))
        [.return (.var currentVar)]) env1 =
      .ok (.returned current.val env1) := by
    simp [runStatement, evalExpr, Ty.denote, env1, env0, selected,
      metropolisHastingsEnv, Env.get, Env.set, Env.setSource, lookup, store,
      require, proposedVar, currentVar, sourceVar, hselfVal, runStatements]
    simp only [bind, pure, Functor.map, Except.bind, Except.pure, Except.map]
    simp [lookup]
  unfold runMetropolisHastings Program.run metropolisHastingsProgram
  change finish (runStatements metropolisHastingsBody env0) = _
  rw [show metropolisHastingsBody =
      (.letE proposedVar (.categorical (.var sourceVar)
        (.row (.var proposalVar) (.var currentVar)))) ::
        metropolisHastingsBody.tail by rfl]
  rw [runStatements_cons_next _ _ _ _ hfirst]
  rw [show metropolisHastingsBody.tail =
      (.ifThen (.eq (.var proposedVar) (.var currentVar))
        [.return (.var currentVar)]) :: metropolisHastingsBody.tail.tail by rfl]
  rw [runStatements_cons_returned _ _ _ _ _ hsecond]
  simp [finish, env1, env0, Env.set, Env.setSource, sourceVar, proposedVar,
    metropolisHastingsEnv, store, require]
  simp only [bind, Functor.map, Except.bind, Except.map]
  simp [lookup]

/-- Embed the established proof-carrying MH replay result into the raw state
encoding returned by the serializable IR. -/
def liftMHResult {n : Nat} :
    Except ExecError (Fin n × List DrawEvent) →
      Except RuntimeError (Nat × List DrawEvent)
  | .error error => .error (.primitive error)
  | .ok (state, rest) => .ok (state.val, rest)

/-- Universal trace-refinement target for the generic finite MH command IR. -/
theorem runMetropolisHastings_refines {n : Nat}
    (target : PositiveNatWeights n) (proposal : NatKernelWeights n)
    (current : Fin n) (trace : List DrawEvent) :
    runMetropolisHastings target.toNatWeights.weightList (proposalRowLists proposal)
        current.val trace =
      liftMHResult (replayMHStep target proposal current trace) := by
  cases hproposalDraw : replayDraw (proposal.row current).total trace with
  | error error =>
      have hproposalReplay : replayCategorical (proposal.row current) trace =
          .error error := by
        unfold replayCategorical
        split <;> simp_all
      have hmh : replayMHStep target proposal current trace = .error error := by
        unfold replayMHStep
        rw [hproposalReplay]
        rfl
      rw [hmh]
      unfold runMetropolisHastings
      rw [runMHProgram_proposal_error target proposal current trace error
        hproposalDraw]
      rfl
  | ok proposalDraw =>
      have hproposalLt : proposalDraw.value < (proposal.row current).total :=
        replayDraw_success_value_lt hproposalDraw
      let proposed := (proposal.row current).select
        ⟨proposalDraw.value, hproposalLt⟩
      have hselect : selectFromList (proposal.row current).weightList
          proposalDraw.value = some proposed.val :=
        ((proposal.row current).select_val_eq_iff
          ⟨proposalDraw.value, hproposalLt⟩ proposed.val).mp rfl
      have hproposalReplay : replayCategorical (proposal.row current) trace =
          .ok (proposed, proposalDraw.remaining) := by
        unfold replayCategorical
        split
        · simp_all
        · rename_i other heq
          have hsame : other = proposalDraw := by
            rw [hproposalDraw] at heq
            exact (Except.ok.inj heq).symm
          subst other
          rfl
      by_cases hself : proposed = current
      · have hmh : replayMHStep target proposal current trace =
            .ok (current, proposalDraw.remaining) := by
          simp [replayMHStep, hproposalReplay, hself, bind, pure,
            Except.bind, Except.pure]
        rw [hmh]
        rw [runMetropolisHastings_self target proposal current trace proposalDraw
          hproposalDraw hself]
        rfl
      · have hselfVal : proposed.val ≠ current.val := by
          intro h
          exact hself (Fin.ext h)
        let upper := proposal.acceptanceUpper target current proposed
        cases hacceptDraw : replayDraw upper proposalDraw.remaining with
        | error error =>
            simp [upper, NatKernelWeights.acceptanceUpper] at hacceptDraw
            have hmh : replayMHStep target proposal current trace = .error error := by
              unfold replayMHStep
              rw [hproposalReplay]
              simp only [bind, Except.bind]
              rw [if_neg hself]
              rw [show replayDraw (proposal.acceptanceUpper target current proposed)
                  proposalDraw.remaining = .error error by
                simpa [NatKernelWeights.acceptanceUpper] using hacceptDraw]
            rw [hmh]
            rw [runMetropolisHastings_acceptanceError target proposal current trace
              proposalDraw hproposalDraw hself error (by
                simpa [NatKernelWeights.acceptanceUpper] using hacceptDraw)]
            rfl
        | ok acceptDraw =>
            simp [upper, NatKernelWeights.acceptanceUpper] at hacceptDraw
            by_cases haccept : acceptDraw.value <
                proposal.acceptanceThreshold target current proposed
            · have hacceptBoth :
                  acceptDraw.value < proposal.acceptanceUpper target current proposed ∧
                  acceptDraw.value < target.weight proposed *
                    (proposal.row proposed).weight current * (proposal.row current).total := by
                simpa [NatKernelWeights.acceptanceThreshold] using haccept
              have hacceptDecision :
                  (decide (acceptDraw.value <
                      proposal.acceptanceUpper target current proposed) &&
                    decide (acceptDraw.value < target.weight proposed *
                      (proposal.row proposed).weight current *
                        (proposal.row current).total)) = true := by
                simp [hacceptBoth.1, hacceptBoth.2]
              simp [NatKernelWeights.acceptanceUpper, proposed] at hacceptDecision
              have hmh : replayMHStep target proposal current trace =
                  .ok (proposed, acceptDraw.remaining) := by
                unfold replayMHStep
                rw [hproposalReplay]
                simp only [bind, Except.bind]
                rw [if_neg hself]
                rw [show replayDraw (proposal.acceptanceUpper target current proposed)
                    proposalDraw.remaining = .ok acceptDraw by
                  simpa [NatKernelWeights.acceptanceUpper] using hacceptDraw]
                change (if acceptDraw.value <
                    proposal.acceptanceThreshold target current proposed then
                  pure (proposed, acceptDraw.remaining)
                else pure (current, acceptDraw.remaining)) = _
                rw [if_pos haccept]
                rfl
              rw [hmh]
              rw [runMetropolisHastings_acceptanceOk target proposal current trace
                proposalDraw acceptDraw hproposalDraw hself (by
                  simpa [NatKernelWeights.acceptanceUpper] using hacceptDraw)]
              change (if acceptDraw.value <
                  proposal.acceptanceThreshold target current proposed then
                Except.ok (proposed.val, acceptDraw.remaining)
              else Except.ok (current.val, acceptDraw.remaining)) = _
              rw [if_pos haccept]
              rfl
            · have hacceptBoth :
                  ¬(acceptDraw.value < proposal.acceptanceUpper target current proposed ∧
                    acceptDraw.value < target.weight proposed *
                      (proposal.row proposed).weight current * (proposal.row current).total) := by
                intro hboth
                apply haccept
                simpa [NatKernelWeights.acceptanceThreshold] using hboth
              have hacceptDecision :
                  (decide (acceptDraw.value <
                      proposal.acceptanceUpper target current proposed) &&
                    decide (acceptDraw.value < target.weight proposed *
                      (proposal.row proposed).weight current *
                        (proposal.row current).total)) = false := by
                by_cases hupperDraw : acceptDraw.value <
                    proposal.acceptanceUpper target current proposed
                · have hnumerator : ¬acceptDraw.value < target.weight proposed *
                      (proposal.row proposed).weight current *
                        (proposal.row current).total := by
                    intro hnumerator
                    exact hacceptBoth ⟨hupperDraw, hnumerator⟩
                  simp [hupperDraw, hnumerator]
                · simp [hupperDraw]
              change
                  (decide (acceptDraw.value < target.weight current *
                      (proposal.row current).weight
                        ((proposal.row current).select
                          ⟨proposalDraw.value, hproposalLt⟩) *
                      (proposal.row ((proposal.row current).select
                        ⟨proposalDraw.value, hproposalLt⟩)).total) &&
                    decide (acceptDraw.value <
                      target.weight ((proposal.row current).select
                        ⟨proposalDraw.value, hproposalLt⟩) *
                      (proposal.row ((proposal.row current).select
                        ⟨proposalDraw.value, hproposalLt⟩)).weight current *
                      (proposal.row current).total)) = false at hacceptDecision
              have hmh : replayMHStep target proposal current trace =
                  .ok (current, acceptDraw.remaining) := by
                unfold replayMHStep
                rw [hproposalReplay]
                simp only [bind, Except.bind]
                rw [if_neg hself]
                rw [show replayDraw (proposal.acceptanceUpper target current proposed)
                    proposalDraw.remaining = .ok acceptDraw by
                  simpa [NatKernelWeights.acceptanceUpper] using hacceptDraw]
                change (if acceptDraw.value <
                    proposal.acceptanceThreshold target current proposed then
                  pure (proposed, acceptDraw.remaining)
                else pure (current, acceptDraw.remaining)) = _
                rw [if_neg haccept]
                rfl
              rw [hmh]
              rw [runMetropolisHastings_acceptanceOk target proposal current trace
                proposalDraw acceptDraw hproposalDraw hself (by
                  simpa [NatKernelWeights.acceptanceUpper] using hacceptDraw)]
              change (if acceptDraw.value <
                  proposal.acceptanceThreshold target current proposed then
                Except.ok (proposed.val, acceptDraw.remaining)
              else Except.ok (current.val, acceptDraw.remaining)) = _
              rw [if_neg haccept]
              rfl

end Mcmc.Executable.Finite.CompilerIR
