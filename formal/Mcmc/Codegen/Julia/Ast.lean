/-!
# Restricted Julia syntax

This is a deliberately small backend AST.  It has no raw-expression or
raw-statement escape hatch: extending generated code requires extending and
reviewing this datatype and printer.
-/

namespace Mcmc.Codegen.Julia

inductive BinaryOp where
  | add | sub | mul | lt | le | eq | and | or

inductive Expr where
  | name (value : String)
  | integer (value : Int)
  | string (value : String)
  | call (callee : Expr) (arguments : List Expr)
  | index (array : Expr) (indices : List Expr)
  | binary (op : BinaryOp) (left right : Expr)
  | lambda (arguments : List String) (body : Expr)
  | vector (values : List Expr)
  | comprehension (value : Expr) (binder : String) (source : Expr)
  | broadcastCall (callee argument : Expr)
  | ifThenElse (condition yes no : Expr)

inductive Failure where
  | argumentError (message : String)
  | dimensionMismatch (message : String)
  | error (message : String)

inductive Stmt where
  | assign (name : String) (value : Expr)
  | guard (condition : Expr) (failure : Failure)
  | forPairs (index value collection : String) (body : List Stmt)
  | ifThen (condition : Expr) (body : List Stmt)
  | return (value : Expr)
  | subtractAssign (name : String) (value : Expr)
  | expression (value : Expr)

structure Argument where
  name : String
  type : String

structure Function where
  name : String
  arguments : List Argument
  body : List Stmt

structure Module where
  name : String
  imports : List (String × List String)
  functions : List Function

private def escapeString (value : String) : String :=
  value.replace "\\" "\\\\" |>.replace "\"" "\\\""

private def spaces (count : Nat) : String :=
  String.ofList (List.replicate count ' ')

private def validIdentifier (value : String) : Bool :=
  match value.toList with
  | [] => false
  | first :: rest =>
      (first.isAlpha || first = '_') &&
        rest.all fun char => char.isAlphanum || char = '_' || char = '!'

private def validType : String → Bool
  | "AbstractRandomSource" | "AbstractVector{<:Integer}"
  | "AbstractVector" | "Integer" | "Bool" => true
  | _ => false

private def validCallee : String → Bool
  | "all" | "length" | "sum" | "min" | "BigInt"
  | "categorical_index!" | "finite_mh_step!" | "draw_below!"
  | "throw" | "ArgumentError" | "DimensionMismatch" | "error" => true
  | _ => false

mutual
  private partial def Expr.valid : Expr → Bool
    | .name value => validIdentifier value
    | .integer _ | .string _ => true
    | .call (.name callee) arguments =>
        validCallee callee && arguments.all Expr.valid
    | .call _ _ => false
    | .index array indices => array.valid && indices.all Expr.valid
    | .binary _ left right => left.valid && right.valid
    | .lambda arguments body => arguments.all validIdentifier && body.valid
    | .vector values => values.all Expr.valid
    | .comprehension value binder source =>
        value.valid && validIdentifier binder && source.valid
    | .broadcastCall (.name callee) argument =>
        validCallee callee && argument.valid
    | .broadcastCall _ _ => false
    | .ifThenElse condition yes no => condition.valid && yes.valid && no.valid

  private partial def Stmt.valid : Stmt → Bool
    | .assign name value => validIdentifier name && value.valid
    | .guard condition _ => condition.valid
    | .forPairs index value collection body =>
        validIdentifier index && validIdentifier value && validIdentifier collection &&
          body.all Stmt.valid
    | .ifThen condition body => condition.valid && body.all Stmt.valid
    | .return value | .expression value => value.valid
    | .subtractAssign name value => validIdentifier name && value.valid
end

private def Argument.valid (argument : Argument) : Bool :=
  validIdentifier argument.name && validType argument.type

private def Function.valid (function : Function) : Bool :=
  validIdentifier function.name && function.arguments.all Argument.valid &&
    function.body.all Stmt.valid

/-- Validate every identifier and the small allowlist of backend types. -/
def Module.validate (module : Module) : Except String Unit :=
  if validIdentifier module.name &&
      module.imports.all (fun (path, names) =>
        path = "...Runtime" && names.all validIdentifier) &&
      module.functions.all Function.valid then
    .ok ()
  else
    .error "unsupported or invalid Julia AST identifier/type"

private def BinaryOp.render : BinaryOp → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .lt => "<"
  | .le => "<="
  | .eq => "=="
  | .and => "&&"
  | .or => "||"

mutual
  private def Expr.render : Expr → String
    | .name value => value
    | .integer value => toString value
    | .string value => s!"\"{escapeString value}\""
    | .call callee arguments =>
        s!"{callee.render}({String.intercalate ", " (arguments.map Expr.render)})"
    | .index array indices =>
        s!"{array.render}[{String.intercalate ", " (indices.map Expr.render)}]"
    | .binary op left right => s!"({left.render} {op.render} {right.render})"
    | .lambda arguments body =>
        s!"({String.intercalate ", " arguments}) -> {body.render}"
    | .vector values => s!"[{String.intercalate ", " (values.map Expr.render)}]"
    | .comprehension value binder source =>
        s!"[{value.render} for {binder} in {source.render}]"
    | .broadcastCall callee argument => s!"{callee.render}.({argument.render})"
    | .ifThenElse condition yes no =>
        s!"({condition.render} ? {yes.render} : {no.render})"

  private def Failure.render : Failure → String
    | .argumentError message => s!"throw(ArgumentError(\"{escapeString message}\"))"
    | .dimensionMismatch message =>
        s!"throw(DimensionMismatch(\"{escapeString message}\"))"
    | .error message => s!"error(\"{escapeString message}\")"

  private def Stmt.render (indent : Nat) : Stmt → String
    | .assign name value => s!"{spaces indent}{name} = {value.render}\n"
    | .guard condition failure =>
        s!"{spaces indent}{condition.render} || {failure.render}\n"
    | .forPairs index value collection body =>
        s!"{spaces indent}for ({index}, {value}) in pairs({collection})\n" ++
          renderStatements (indent + 4) body ++
          s!"{spaces indent}end\n"
    | .ifThen condition body =>
        s!"{spaces indent}if {condition.render}\n" ++
          renderStatements (indent + 4) body ++
          s!"{spaces indent}end\n"
    | .return value => s!"{spaces indent}return {value.render}\n"
    | .subtractAssign name value =>
        s!"{spaces indent}{name} -= {value.render}\n"
    | .expression value => s!"{spaces indent}{value.render}\n"

  private def renderStatements (indent : Nat) (statements : List Stmt) : String :=
    String.join (statements.map (Stmt.render indent))
end

private def Argument.render (argument : Argument) : String :=
  s!"{argument.name}::{argument.type}"

private def Function.render (function : Function) : String :=
  s!"function {function.name}({String.intercalate ", "
      (function.arguments.map Argument.render)})\n" ++
    renderStatements 4 function.body ++ "end\n"

/-- Deterministically print a validated restricted AST. -/
def Module.render (module : Module) : Except String String := do
  module.validate
  return (s!"# This file is generated by `lake exe generate_julia`; do not edit.\n\n" ++
  s!"module {module.name}\n\n" ++
  String.join (module.imports.map fun (path, names) =>
    s!"using {path}: {String.intercalate ", " names}\n") ++
  "\n" ++ String.intercalate "\n" (module.functions.map Function.render) ++
  s!"\nend\n")

end Mcmc.Codegen.Julia
