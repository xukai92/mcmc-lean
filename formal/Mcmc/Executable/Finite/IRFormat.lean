import Mcmc.Executable.Finite.CompilerIR

/-!
# Versioned textual format for finite sampler IR

The artifact is data, not Julia source. Its deliberately small S-expression
format is consumed by the maintained Julia reference interpreter.
-/

namespace Mcmc.Executable.Finite.CompilerIR.Format

def version : Nat := 1

private def quote (value : String) : String :=
  let escapedBackslash := value.replace "\\" "\\\\"
  let escapedQuote := escapedBackslash.replace "\"" "\\\""
  let escapedNewline := escapedQuote.replace "\n" "\\n"
  "\"" ++ escapedNewline ++ "\""

private def tyRender : Ty → String
  | .source => "source"
  | .nat => "nat"
  | .bool => "bool"
  | .natVector => "nat-vector"
  | .natMatrix => "nat-matrix"

private def list (items : List String) : String :=
  "(" ++ String.intercalate " " items ++ ")"

private def exprRender : {type : Ty} → Expr type → String
  | type, .var value => list ["var", tyRender type, quote value.name]
  | _, .nat value => list ["nat", toString value]
  | _, .vector values => list ("vector" :: values.map toString)
  | _, .matrix rows => list ("matrix" :: rows.map fun row =>
      list ("row" :: row.map toString))
  | _, .add left right => list ["add", exprRender left, exprRender right]
  | _, .sub left right => list ["sub", exprRender left, exprRender right]
  | _, .mul left right => list ["mul", exprRender left, exprRender right]
  | _, .min left right => list ["min", exprRender left, exprRender right]
  | _, .length value => list ["length", exprRender value]
  | _, .rowCount value => list ["row-count", exprRender value]
  | _, .total value => list ["total", exprRender value]
  | _, .index value index => list ["index", exprRender value, exprRender index]
  | _, .row value index => list ["row-at", exprRender value, exprRender index]
  | _, .lt left right => list ["lt", exprRender left, exprRender right]
  | _, .le left right => list ["le", exprRender left, exprRender right]
  | _, .eq left right => list ["eq", exprRender left, exprRender right]
  | _, .and left right => list ["and", exprRender left, exprRender right]
  | _, .allNonnegative value => list ["all-nonnegative", exprRender value]
  | _, .allPositive value => list ["all-positive", exprRender value]
  | _, .allRowsLength value size =>
      list ["all-rows-length", exprRender value, exprRender size]
  | _, .allRowsNonnegativePositive value =>
      list ["all-rows-nonnegative-positive", exprRender value]
  | _, .toExactVector value => list ["to-exact-vector", exprRender value]
  | _, .toExactMatrix value => list ["to-exact-matrix", exprRender value]
  | _, .categorical source weights =>
      list ["categorical", exprRender source, exprRender weights]

private def failureRender : Failure → String
  | .argument message => list ["argument", quote message]
  | .dimension message => list ["dimension", quote message]
  | .internal message => list ["internal", quote message]

private def stmtRender : Stmt → String
  | .letE destination value =>
      list ["let", quote destination.name, exprRender value]
  | .guard condition failure =>
      list ["guard", exprRender condition, failureRender failure]
  | .drawBelow destination source upper =>
      list ["draw-below", quote destination.name, exprRender source, exprRender upper]
  | .ifThen condition body =>
      list ["if", exprRender condition, list ("body" :: body.map stmtRender)]
  | .return value => list ["return", exprRender value]
  | .fail failure => list ["fail", failureRender failure]

private def Input.render (input : Input) : String :=
  list ["input", tyRender input.type, quote input.name]

private def programRender (program : Program) : String :=
  list ["program", quote program.name,
    list ("inputs" :: program.inputs.map Input.render),
    list ("body" :: program.body.map stmtRender)]

/-- Serialize all finite reference entry programs with a format version. -/
def render : String :=
  list ["verified-samplers-ir", toString version,
    programRender categoricalProgram, programRender metropolisHastingsProgram] ++ "\n"

end Mcmc.Executable.Finite.CompilerIR.Format
