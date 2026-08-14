import Mcmc.Codegen.Julia.Ast
import Mcmc.Executable.Finite.CompilerIR
import Mcmc.Executable.Finite.Program

/-!
# Lowering the backend-neutral finite IR to Julia

Zero-based IR indices are converted to Julia's one-based indexing only here.
-/

namespace Mcmc.Codegen.Julia.Finite

open Mcmc.Codegen.Julia
open Mcmc.Executable.Finite
namespace IR

abbrev Ty := Mcmc.Executable.Finite.CompilerIR.Ty
abbrev Expr := Mcmc.Executable.Finite.CompilerIR.Expr
abbrev Failure := Mcmc.Executable.Finite.CompilerIR.Failure
abbrev Stmt := Mcmc.Executable.Finite.CompilerIR.Stmt
abbrev Program := Mcmc.Executable.Finite.CompilerIR.Program

def categoricalProgram := Mcmc.Executable.Finite.CompilerIR.categoricalProgram
def metropolisHastingsProgram := Mcmc.Executable.Finite.CompilerIR.metropolisHastingsProgram
def twoStateTarget := Mcmc.Executable.Finite.CompilerIR.twoStateTarget
def twoStateProposal := Mcmc.Executable.Finite.CompilerIR.twoStateProposal

end IR

private def n (value : String) : Expr := .name value
private def i (value : Int) : Expr := .integer value
private def call (callee : String) (arguments : List Expr) : Expr :=
  .call (n callee) arguments
private def bin (op : BinaryOp) (left right : Expr) : Expr := .binary op left right
private def plusOne (value : Expr) : Expr := bin .add value (i 1)
private def index1 (array index : Expr) : Expr := .index array [plusOne index]

private def lowerExpr : {type : IR.Ty} → IR.Expr type → Expr
  | _, .var value => n value.name
  | _, .nat value => .integer (Int.ofNat value)
  | _, .vector values => .vector (values.map fun value => .integer (Int.ofNat value))
  | _, .matrix rows => .vector (rows.map fun row =>
      .vector (row.map fun value => .integer (Int.ofNat value)))
  | _, .add left right => bin .add (lowerExpr left) (lowerExpr right)
  | _, .sub left right => bin .sub (lowerExpr left) (lowerExpr right)
  | _, .mul left right => bin .mul (lowerExpr left) (lowerExpr right)
  | _, .min left right => call "min" [lowerExpr left, lowerExpr right]
  | _, .length value => call "length" [lowerExpr value]
  | _, .rowCount value => call "length" [lowerExpr value]
  | _, .total value => call "sum" [lowerExpr value]
  | _, .index value index => index1 (lowerExpr value) (lowerExpr index)
  | _, .row value index => index1 (lowerExpr value) (lowerExpr index)
  | _, .lt left right => bin .lt (lowerExpr left) (lowerExpr right)
  | _, .le left right => bin .le (lowerExpr left) (lowerExpr right)
  | _, .eq left right => bin .eq (lowerExpr left) (lowerExpr right)
  | _, .and left right => bin .and (lowerExpr left) (lowerExpr right)
  | _, .allNonnegative value => call "all" [
      .lambda ["weight"] (bin .le (i 0) (n "weight")), lowerExpr value]
  | _, .allPositive value => call "all" [
      .lambda ["weight"] (bin .lt (i 0) (n "weight")), lowerExpr value]
  | _, .allRowsLength value size => call "all" [
      .lambda ["row"] (bin .eq (call "length" [n "row"]) (lowerExpr size)),
      lowerExpr value]
  | _, .allRowsNonnegativePositive value => call "all" [
      .lambda ["row"] (bin .and
        (call "all" [.lambda ["weight"] (bin .le (i 0) (n "weight")), n "row"])
        (bin .lt (i 0) (call "sum" [n "row"]))), lowerExpr value]
  | _, .toExactVector value => .broadcastCall (n "BigInt") (lowerExpr value)
  | _, .toExactMatrix value => .comprehension
      (.broadcastCall (n "BigInt") (n "row")) "row" (lowerExpr value)
  | _, .categorical source weights =>
      call "categorical_index!" [lowerExpr source, lowerExpr weights]

private def lowerFailure : IR.Failure → Failure
  | .argument message => .argumentError message
  | .dimension message => .dimensionMismatch message
  | .internal message => .error message

private def lowerStmt : IR.Stmt → Stmt
    | .letE destination value => .assign destination.name (lowerExpr value)
    | .guard condition failure => .guard (lowerExpr condition) (lowerFailure failure)
    | .drawBelow destination source upper =>
        .assign destination.name (call "draw_below!" [lowerExpr source, lowerExpr upper])
    | .forVector index weight vector body =>
        let rawIndex := index.name ++ "_julia"
        .forPairs rawIndex weight.name vector.name <|
          .assign index.name (bin .sub (n rawIndex) (i 1)) :: body.map lowerStmt
    | .ifThen condition body => .ifThen (lowerExpr condition) (body.map lowerStmt)
    | .subtractAssign destination value =>
        .subtractAssign destination.name (lowerExpr value)
    | .return value => .return (lowerExpr value)
    | .fail failure => .expression <| match lowerFailure failure with
        | .argumentError message => call "throw" [call "ArgumentError" [.string message]]
        | .dimensionMismatch message => call "throw" [call "DimensionMismatch" [.string message]]
        | .error message => call "error" [.string message]

private def lowerType : IR.Ty → String
  | .source => "AbstractRandomSource"
  | .nat => "Integer"
  | .natVector => "AbstractVector{<:Integer}"
  | .natMatrix => "AbstractVector"
  | .bool => "Bool"

private def lowerProgram (program : IR.Program) : Function where
  name := program.name
  arguments := program.inputs.map fun input => ⟨input.name, lowerType input.type⟩
  body := program.body.map lowerStmt

private def twoStateFunction : Function where
  name := "two_state_mh_step!"
  arguments := [⟨"source", "AbstractRandomSource"⟩, ⟨"current", "Integer"⟩]
  body := [.return (call "finite_mh_step!" [n "source",
    lowerExpr IR.twoStateTarget, lowerExpr IR.twoStateProposal, n "current"])]

/-- Lower a supported typed finite entry descriptor. The descriptor selects a
backend-neutral command program; lowering is structural over that program. -/
def lower : {signature : Signature} → Program signature → List Function
  | _, .categorical => [lowerProgram IR.categoricalProgram]
  | _, .metropolisHastings =>
      [lowerProgram IR.metropolisHastingsProgram, twoStateFunction]

def module : Module where
  name := "FiniteCore"
  imports := [("...Runtime", ["AbstractRandomSource", "draw_below!"])]
  functions := lower Program.categorical ++ lower Program.metropolisHastings

end Mcmc.Codegen.Julia.Finite
