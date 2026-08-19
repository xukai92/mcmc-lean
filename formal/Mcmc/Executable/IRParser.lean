import Mcmc.Executable.IRFormat

/-!
# Parser foundation for the sampler artifact

This module parses the backend-neutral S-expression syntax emitted by
`Mcmc.Executable.IRFormat`.  It deliberately starts below the typed command IR:
the first trust-reduction milestone is a checked textual round trip for the two
exact finite programs.  A later typed decoder can reuse this syntax tree
without coupling the parser to Julia.
-/

namespace Mcmc.Executable.IRParser

open Std.Internal.Parsec String

/-- Syntax tree for the serialized sampler artifact. Quoted strings and atoms
remain distinct so re-rendering preserves the artifact grammar exactly. -/
inductive SExpr where
  | atom (value : String)
  | quoted (value : String)
  | list (items : List SExpr)
  deriving Repr

private def quote (value : String) : String :=
  let escapedBackslash := value.replace "\\" "\\\\"
  let escapedQuote := escapedBackslash.replace "\"" "\\\""
  let escapedNewline := escapedQuote.replace "\n" "\\n"
  "\"" ++ escapedNewline ++ "\""

/-- Canonical rendering of a parsed S-expression. -/
def SExpr.render : SExpr → String
  | .atom value => value
  | .quoted value => quote value
  | .list items => "(" ++ String.intercalate " " (items.map SExpr.render) ++ ")"

private def atomChar : Parser Char := attempt do
  let value ← any
  if value.isWhitespace || value = '(' || value = ')' || value = '"' then
    fail "artifact atom character expected"
  else
    pure value

private partial def quotedChars (accumulator : String := "") : Parser String := do
  let value ← any
  if value = '"' then
    pure accumulator
  else if value = '\\' then
    let escaped ← any
    match escaped with
    | '\\' => quotedChars (accumulator.push '\\')
    | '"' => quotedChars (accumulator.push '"')
    | 'n' => quotedChars (accumulator.push '\n')
    | _ => fail "unsupported artifact string escape"
  else
    quotedChars (accumulator.push value)

private def quoted : Parser SExpr := do
  skipChar '"'
  pure (.quoted (← quotedChars))

private def atom : Parser SExpr := do
  let value ← many1Chars atomChar
  pure (.atom value)

private partial def expression : Parser SExpr := do
  ws
  match ← peek! with
  | '(' =>
      skip
      ws
      let items ← many (expression <* ws)
      skipChar ')'
      pure (.list items.toList)
  | '"' => quoted
  | ')' => fail "unexpected closing parenthesis"
  | _ => atom

/-- Parse exactly one artifact S-expression, allowing surrounding whitespace. -/
def parse (source : String) : Except String SExpr :=
  Parser.run (ws *> expression <* ws <* eof) source

/-- Whether parsing followed by canonical rendering reproduces the input. -/
def textRoundTrips (source : String) : Bool :=
  match parse source with
  | .ok expression => expression.render = source
  | .error _ => false

/-- Check the versioned envelope shared by every backend consumer. Individual
declaration decoders remain responsible for their typed payloads. -/
def validatesArtifactEnvelope (source : String) : Bool :=
  match parse source with
  | .ok (.list (.atom "verified-samplers-ir" :: .atom encodedVersion :: declarations)) =>
      encodedVersion.toNat? == some IRFormat.version &&
        !declarations.isEmpty && declarations.all fun declaration =>
          match declaration with
          | .list _ => true
          | _ => false
  | _ => false

open Mcmc.Executable.Finite.CompilerIR

private def atomValue : SExpr → Except String String
  | .atom value => pure value
  | _ => throw "artifact atom expected"

private def quotedValue : SExpr → Except String String
  | .quoted value => pure value
  | _ => throw "artifact quoted string expected"

private def listValue : SExpr → Except String (List SExpr)
  | .list values => pure values
  | _ => throw "artifact list expected"

private def naturalValue (expression : SExpr) : Except String Nat := do
  let value ← atomValue expression
  match value.toNat? with
  | some result => pure result
  | none => throw s!"invalid artifact natural: {value}"

private def decodeTy : SExpr → Except String Ty
  | .atom "source" => pure .source
  | .atom "nat" => pure .nat
  | .atom "bool" => pure .bool
  | .atom "nat-vector" => pure .natVector
  | .atom "nat-matrix" => pure .natMatrix
  | _ => throw "invalid finite artifact type"

private def checkTy : Ty → Ty → Except String Unit
  | .source, .source | .nat, .nat | .bool, .bool |
      .natVector, .natVector | .natMatrix, .natMatrix => pure ()
  | _, _ => throw "finite artifact expression type mismatch"

private structure PackedExpr where
  type : Ty
  value : Expr type

mutual
  private partial def decodeSource : SExpr → Except String (Expr .source)
    | .list [.atom "var", encodedType, name] => do
        checkTy .source (← decodeTy encodedType)
        pure (.var ⟨← quotedValue name⟩)
    | _ => throw "invalid finite source expression"

  private partial def decodeNat : SExpr → Except String (Expr .nat)
    | .list [.atom "var", encodedType, name] => do
        checkTy .nat (← decodeTy encodedType)
        pure (.var ⟨← quotedValue name⟩)
    | .list [.atom "nat", value] => do pure (.nat (← naturalValue value))
    | .list [.atom "add", left, right] => do
        pure (.add (← decodeNat left) (← decodeNat right))
    | .list [.atom "sub", left, right] => do
        pure (.sub (← decodeNat left) (← decodeNat right))
    | .list [.atom "mul", left, right] => do
        pure (.mul (← decodeNat left) (← decodeNat right))
    | .list [.atom "min", left, right] => do
        pure (.min (← decodeNat left) (← decodeNat right))
    | .list [.atom "length", value] => do pure (.length (← decodeNatVector value))
    | .list [.atom "row-count", value] => do
        pure (.rowCount (← decodeNatMatrix value))
    | .list [.atom "total", value] => do pure (.total (← decodeNatVector value))
    | .list [.atom "index", value, index] => do
        pure (.index (← decodeNatVector value) (← decodeNat index))
    | .list [.atom "categorical", source, weights] => do
        pure (.categorical (← decodeSource source) (← decodeNatVector weights))
    | _ => throw "invalid finite natural expression"

  private partial def decodeBool : SExpr → Except String (Expr .bool)
    | .list [.atom "var", encodedType, name] => do
        checkTy .bool (← decodeTy encodedType)
        pure (.var ⟨← quotedValue name⟩)
    | .list [.atom "lt", left, right] => do
        pure (.lt (← decodeNat left) (← decodeNat right))
    | .list [.atom "le", left, right] => do
        pure (.le (← decodeNat left) (← decodeNat right))
    | .list [.atom "eq", left, right] => do
        pure (.eq (← decodeNat left) (← decodeNat right))
    | .list [.atom "and", left, right] => do
        pure (.and (← decodeBool left) (← decodeBool right))
    | .list [.atom "all-nonnegative", value] => do
        pure (.allNonnegative (← decodeNatVector value))
    | .list [.atom "all-positive", value] => do
        pure (.allPositive (← decodeNatVector value))
    | .list [.atom "all-rows-length", value, size] => do
        pure (.allRowsLength (← decodeNatMatrix value) (← decodeNat size))
    | .list [.atom "all-rows-nonnegative-positive", value] => do
        pure (.allRowsNonnegativePositive (← decodeNatMatrix value))
    | _ => throw "invalid finite Boolean expression"

  private partial def decodeNatVector : SExpr → Except String (Expr .natVector)
    | .list [.atom "var", encodedType, name] => do
        checkTy .natVector (← decodeTy encodedType)
        pure (.var ⟨← quotedValue name⟩)
    | .list (.atom "vector" :: values) => do pure (.vector (← values.mapM naturalValue))
    | .list [.atom "row-at", value, index] => do
        pure (.row (← decodeNatMatrix value) (← decodeNat index))
    | .list [.atom "to-exact-vector", value] => do
        pure (.toExactVector (← decodeNatVector value))
    | _ => throw "invalid finite natural-vector expression"

  private partial def decodeNatMatrix : SExpr → Except String (Expr .natMatrix)
    | .list [.atom "var", encodedType, name] => do
        checkTy .natMatrix (← decodeTy encodedType)
        pure (.var ⟨← quotedValue name⟩)
    | .list (.atom "matrix" :: rows) => do
        let decoded ← rows.mapM fun row => do
          match ← listValue row with
          | .atom "row" :: values => values.mapM naturalValue
          | _ => throw "invalid finite artifact matrix row"
        pure (.matrix decoded)
    | .list [.atom "to-exact-matrix", value] => do
        pure (.toExactMatrix (← decodeNatMatrix value))
    | _ => throw "invalid finite natural-matrix expression"
end

private def decodeExpr : (expected : Ty) → SExpr → Except String (Expr expected)
  | .source, expression => decodeSource expression
  | .nat, expression => decodeNat expression
  | .bool, expression => decodeBool expression
  | .natVector, expression => decodeNatVector expression
  | .natMatrix, expression => decodeNatMatrix expression

private partial def decodePackedExpr (expression : SExpr) :
    Except String PackedExpr := do
  let type ← match expression with
    | .list [.atom "var", encodedType, _] => decodeTy encodedType
    | .list (.atom tag :: _) =>
        if tag ∈ ["nat", "add", "sub", "mul", "min", "length", "row-count",
            "total", "index", "categorical"] then pure .nat
        else if tag ∈ ["vector", "row-at", "to-exact-vector"] then pure .natVector
        else if tag ∈ ["matrix", "to-exact-matrix"] then pure .natMatrix
        else if tag ∈ ["lt", "le", "eq", "and", "all-nonnegative", "all-positive",
            "all-rows-length", "all-rows-nonnegative-positive"] then pure .bool
        else throw "unknown finite artifact expression constructor"
    | _ => throw "invalid finite artifact expression"
  pure ⟨type, ← decodeExpr type expression⟩

private def decodeFailure : SExpr → Except String Failure
  | .list [.atom "argument", .quoted message] => pure (.argument message)
  | .list [.atom "dimension", .quoted message] => pure (.dimension message)
  | .list [.atom "internal", .quoted message] => pure (.internal message)
  | _ => throw "invalid finite artifact failure"

private partial def decodeStmt : SExpr → Except String Stmt
  | .list [.atom "let", name, value] => do
      let destination ← quotedValue name
      let packed ← decodePackedExpr value
      pure (.letE ⟨destination⟩ packed.value)
  | .list [.atom "guard", condition, failure] => do
      pure (.guard (← decodeExpr .bool condition) (← decodeFailure failure))
  | .list [.atom "draw-below", name, source, upper] => do
      pure (.drawBelow ⟨← quotedValue name⟩ (← decodeExpr .source source)
        (← decodeExpr .nat upper))
  | .list [.atom "if", condition, .list (.atom "body" :: body)] => do
      pure (.ifThen (← decodeExpr .bool condition) (← body.mapM decodeStmt))
  | .list [.atom "return", value] => do pure (.return (← decodeExpr .nat value))
  | .list [.atom "fail", failure] => do pure (.fail (← decodeFailure failure))
  | _ => throw "invalid finite artifact statement"

private def decodeInput : SExpr → Except String Input
  | .list [.atom "input", type, .quoted name] => do pure ⟨← decodeTy type, name⟩
  | _ => throw "invalid finite artifact input"

/-- Decode the parsed syntax of one typed finite command-IR program. -/
def decodeFiniteProgram : SExpr → Except String Program
  | .list [.atom "program", .quoted name, .list (.atom "inputs" :: inputs),
      .list (.atom "body" :: body)] => do
    pure ⟨name, ← inputs.mapM decodeInput, ← body.mapM decodeStmt⟩
  | _ => throw "invalid finite artifact program"

/-- Decode the two registered exact finite programs from the leading slots of
the complete artifact. Later declarations may evolve independently. -/
def decodeRegisteredFinitePrograms (source : String) :
    Except String (Program × Program) := do
  match ← parse source with
  | .list (.atom "verified-samplers-ir" :: .atom encodedVersion ::
      categorical :: metropolisHastings :: _) =>
      if encodedVersion.toNat? != some IRFormat.version then
        throw "unsupported artifact version"
      pure (← decodeFiniteProgram categorical,
        ← decodeFiniteProgram metropolisHastings)
  | _ => throw "invalid sampler artifact envelope"

/-- Whether the complete artifact contains the two canonical, typed finite
programs in their registered slots. -/
def registeredFiniteProgramsRoundTrip (source : String) : Bool :=
  match decodeRegisteredFinitePrograms source with
  | .error _ => false
  | .ok (categorical, metropolisHastings) =>
      IRFormat.finiteProgramRender categorical =
          IRFormat.finiteProgramRender categoricalProgram &&
        IRFormat.finiteProgramRender metropolisHastings =
          IRFormat.finiteProgramRender metropolisHastingsProgram

/-- Whether text parses, decodes to the typed finite IR, and re-renders
byte-for-byte. -/
def typedFiniteProgramRoundTrips (source : String) : Bool :=
  match parse source with
  | .error _ => false
  | .ok parsed =>
      match decodeFiniteProgram parsed with
      | .error _ => false
      | .ok program => IRFormat.finiteProgramRender program = source

open Mcmc.Executable.Finite.CompilerIR in
/-- The emitted categorical finite program is accepted by the Lean parser and
round-trips byte for byte. -/
theorem categoricalProgram_textRoundTrips :
    textRoundTrips (IRFormat.finiteProgramRender categoricalProgram) := by
  native_decide

open Mcmc.Executable.Finite.CompilerIR in
/-- The categorical artifact decodes back into well-typed finite IR and
re-renders byte for byte. -/
theorem categoricalProgram_typedRoundTrips :
    typedFiniteProgramRoundTrips
      (IRFormat.finiteProgramRender categoricalProgram) := by
  native_decide

open Mcmc.Executable.Finite.CompilerIR in
/-- The emitted generic finite-MH program is accepted by the Lean parser and
round-trips byte for byte. -/
theorem metropolisHastingsProgram_textRoundTrips :
    textRoundTrips (IRFormat.finiteProgramRender metropolisHastingsProgram) := by
  native_decide

open Mcmc.Executable.Finite.CompilerIR in
/-- The generic finite-MH artifact decodes back into well-typed finite IR and
re-renders byte for byte. -/
theorem metropolisHastingsProgram_typedRoundTrips :
    typedFiniteProgramRoundTrips
      (IRFormat.finiteProgramRender metropolisHastingsProgram) := by
  native_decide

/-- Escaped strings used by the artifact format round-trip through the parser. -/
theorem escapedString_textRoundTrips :
    textRoundTrips (SExpr.render (.quoted "quote \" slash \\ newline\n")) := by
  native_decide

/-- The typed decoder rejects a variable whose serialized type disagrees with
the enclosing return statement. -/
theorem illTypedReturn_rejected :
    typedFiniteProgramRoundTrips
      "(program \"bad\" (inputs) (body (return (var bool \"x\"))))" = false := by
  native_decide

/-- The generated complete artifact has the current versioned envelope. -/
theorem renderedArtifact_validatesEnvelope :
    validatesArtifactEnvelope IRFormat.render := by
  native_decide

/-- The complete generated artifact independently parses and type-checks its
two registered exact finite programs. -/
theorem renderedArtifact_registeredFiniteProgramsRoundTrip :
    registeredFiniteProgramsRoundTrip IRFormat.render := by
  native_decide

open Mcmc.Executable.Continuous.CompilerIR in
/-- The existing scalar Gaussian-RWMH declaration canonically parses and
re-renders. This is a syntax result, not a typed continuous-IR decoder or an
interpreter-correspondence theorem. -/
theorem gaussianRwmhProgram_textRoundTrips :
    textRoundTrips (IRFormat.continuousProgramRender gaussianRwmhProgram) := by
  native_decide

open Mcmc.Executable.Continuous.CompilerIR in
/-- The existing scalar fixed-step-HMC declaration canonically parses and
re-renders. Its stronger semantic boundaries remain recorded separately. -/
theorem scalarHmcProgram_textRoundTrips :
    textRoundTrips (IRFormat.continuousProgramRender scalarHmcProgram) := by
  native_decide

/-- The first executable checked-NUTS tree program has canonical syntax.  Its
stronger structural semantics are proved in `Continuous.NUTSIR`; this theorem
guards only the independent textual transport boundary. -/
theorem checkedNutsTreeProgram_textRoundTrips :
    textRoundTrips (IRFormat.nutsTreeProgramRender "checked-nuts-reference"
      Mcmc.Executable.Continuous.NUTSIR.referenceProgram) := by
  native_decide

end Mcmc.Executable.IRParser
