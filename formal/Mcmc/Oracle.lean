import Mcmc.Executable.Finite.TwoState
import Mcmc.Executable.Finite.CompilerIRInterpreter
import Mcmc.Executable.Continuous.RestrictedCertificate

/-! A small compiled oracle for cross-language conformance tests. -/

open Mcmc.Executable.Finite

private def usage : String :=
  "usage: mcmc-oracle categorical WEIGHTS DRAW | mh STATE PROPOSAL_DRAW [ACCEPT_DRAW] | gaussian_certificate INPUT VALUE DERIVATIVE HESSIAN VALUE_ERROR DERIVATIVE_ERROR HESSIAN_ERROR"

private def parseNat (text : String) : Except String Nat :=
  match text.toNat? with
  | some value => .ok value
  | none => .error s!"invalid natural: {text}"

private def parseWeights (text : String) : Except String (List Nat) := do
  let fields := text.splitOn ","
  if fields.isEmpty then throw "empty weights"
  fields.mapM parseNat

private def parseRows (text : String) : Except String (List (List Nat)) :=
  (text.splitOn ";").mapM parseWeights

private def parseRat (text : String) : Except String ℚ := do
  match text.splitOn "/" with
  | [numeratorText, denominatorText] =>
      let numerator ← match numeratorText.toInt? with
        | some value => .ok value
        | none => .error s!"invalid rational numerator: {numeratorText}"
      let denominator ← parseNat denominatorText
      if hdenominator : denominator ≠ 0 then
        return Rat.normalize numerator denominator hdenominator
      else
        throw "rational denominator must be positive"
  | _ => throw s!"invalid rational: {text}"

private def runGaussianCertificate
    (inputText valueText derivativeText hessianText valueErrorText
      derivativeErrorText hessianErrorText : String) :
    IO Unit := do
  match parseRat inputText, parseRat valueText, parseRat derivativeText,
      parseRat hessianText, parseRat valueErrorText, parseRat derivativeErrorText,
      parseRat hessianErrorText with
  | .ok input, .ok value, .ok derivative, .ok hessian, .ok valueError,
      .ok derivativeError, .ok hessianError =>
      let certificate :
          Mcmc.Executable.Continuous.RestrictedGaussianRationalCertificate :=
        { input := input
          computedValue := value
          computedDerivative := derivative
          computedSecondDerivative := hessian
          valueError := valueError
          derivativeError := derivativeError
          secondDerivativeError := hessianError }
      if certificate.check then IO.println "ok" else IO.println "error invalidCertificate"
  | .error error, _, _, _, _, _, _ | _, .error error, _, _, _, _, _ |
      _, _, .error error, _, _, _, _ | _, _, _, .error error, _, _, _ |
      _, _, _, _, .error error, _, _ | _, _, _, _, _, .error error, _ |
      _, _, _, _, _, _, .error error => IO.println s!"error {error}"

private def printIRResult
    (result : Except CompilerIR.RuntimeError (Nat × List DrawEvent)) : IO Unit :=
  match result with
  | .ok (state, remaining) => IO.println s!"ok {state} {remaining.length}"
  | .error error => IO.println s!"error {repr error}"

private def runCategorical (weightsText drawText : String) : IO Unit := do
  match parseWeights weightsText, parseNat drawText with
  | .ok weights, .ok draw =>
      let total := weights.sum
      match CompilerIR.runCategorical weights [⟨total, draw⟩] with
      | .ok (index, _) => IO.println s!"ok {index}"
      | .error error => IO.println s!"error {repr error}"
  | .error error, _ | _, .error error => IO.println s!"error {error}"

private def runMH (stateText proposalText : String) (acceptText : Option String) : IO Unit := do
  match parseNat stateText, parseNat proposalText with
  | .ok state, .ok proposalDraw =>
      if hstate : state < 2 then
        let current : Fin 2 := ⟨state, hstate⟩
        if hproposal : proposalDraw < 2 then
          let baseTrace := [DrawEvent.mk 2 proposalDraw]
          let traceResult : Except String (List DrawEvent) :=
            if proposalDraw = state then
              .ok baseTrace
            else
              match acceptText with
              | none => .error "missing acceptance draw"
              | some text => do
                  let acceptDraw ← parseNat text
                  let proposed : Fin 2 := ⟨proposalDraw, hproposal⟩
                  let upper :=
                    Mcmc.Executable.Finite.TwoState.proposal.acceptanceUpper
                      Mcmc.Executable.Finite.TwoState.target current proposed
                  .ok (baseTrace ++ [DrawEvent.mk upper acceptDraw])
          match traceResult with
          | .error error => IO.println s!"error {error}"
          | .ok trace =>
              printIRResult (CompilerIR.runMetropolisHastings
                [1, 3] [[1, 1], [1, 1]] current.val trace)
        else
          IO.println s!"error outOfRange 2 {proposalDraw}"
      else
        IO.println s!"error invalidState {state}"
  | .error error, _ | _, .error error => IO.println s!"error {error}"

private def runGenericMH (targetText rowsText stateText proposalText : String)
    (acceptText : Option String) : IO Unit := do
  match parseWeights targetText, parseRows rowsText, parseNat stateText,
      parseNat proposalText with
  | .ok target, .ok rows, .ok state, .ok proposalDraw =>
      let stateCount := target.length
      if stateCount = 0 || target.any (· = 0) then
        IO.println "error targetWeightsMustBePositive"
      else if rows.length != stateCount || rows.any (fun row ↦
          row.length != stateCount || row.sum = 0) then
        IO.println "error invalidProposalDimensionsOrTotal"
      else if _hstate : state < stateCount then
        let targetArray := target.toArray
        let rowArrays := (rows.map List.toArray).toArray
        let currentRow := rowArrays[state]!
        let currentTotal := currentRow.toList.sum
        if _hdraw : proposalDraw < currentTotal then
          match selectFromList currentRow.toList proposalDraw with
          | none => IO.println "error internalSelectionFailure"
          | some proposed =>
              if proposed = state then
                printIRResult (CompilerIR.runMetropolisHastings target rows state
                  [⟨currentTotal, proposalDraw⟩])
              else
                match acceptText with
                | none => IO.println "error missing acceptance draw"
                | some text =>
                    match parseNat text with
                    | .error error => IO.println s!"error {error}"
                    | .ok acceptDraw =>
                        let proposedRow := rowArrays[proposed]!
                        let upper := targetArray[state]! * currentRow[proposed]! *
                          proposedRow.toList.sum
                        printIRResult (CompilerIR.runMetropolisHastings target rows state
                          [⟨currentTotal, proposalDraw⟩, ⟨upper, acceptDraw⟩])
        else
          IO.println s!"error outOfRange {currentTotal} {proposalDraw}"
      else
        IO.println s!"error invalidState {state}"
  | .error error, _, _, _ | _, .error error, _, _ |
      _, _, .error error, _ | _, _, _, .error error =>
      IO.println s!"error {error}"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["categorical", weights, draw] =>
      runCategorical weights draw
      return 0
  | ["mh", state, proposal] =>
      runMH state proposal none
      return 0
  | ["mh", state, proposal, accept] =>
      runMH state proposal (some accept)
      return 0
  | ["mh_generic", target, rows, state, proposal] =>
      runGenericMH target rows state proposal none
      return 0
  | ["mh_generic", target, rows, state, proposal, accept] =>
      runGenericMH target rows state proposal (some accept)
      return 0
  | ["gaussian_certificate", input, value, derivative, hessian, valueError,
      derivativeError, hessianError] =>
      runGaussianCertificate input value derivative hessian valueError
        derivativeError hessianError
      return 0
  | _ =>
      IO.eprintln usage
      return 2
