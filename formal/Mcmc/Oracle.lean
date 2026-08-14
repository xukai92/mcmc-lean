import Mcmc.Executable.Finite.TwoState

/-! A small compiled oracle for cross-language conformance tests. -/

open Mcmc.Executable.Finite

private def usage : String :=
  "usage: mcmc-oracle categorical WEIGHTS DRAW | mh STATE PROPOSAL_DRAW [ACCEPT_DRAW]"

private def parseNat (text : String) : Except String Nat :=
  match text.toNat? with
  | some value => .ok value
  | none => .error s!"invalid natural: {text}"

private def parseWeights (text : String) : Except String (List Nat) := do
  let fields := text.splitOn ","
  if fields.isEmpty then throw "empty weights"
  fields.mapM parseNat

private def printExecResult {n : Nat}
    (result : Except ExecError (Fin n × List DrawEvent)) : IO Unit :=
  match result with
  | .ok (state, remaining) => IO.println s!"ok {state.val} {remaining.length}"
  | .error error => IO.println s!"error {repr error}"

private def runCategorical (weightsText drawText : String) : IO Unit := do
  match parseWeights weightsText, parseNat drawText with
  | .ok weights, .ok draw =>
      let total := weights.sum
      if total = 0 then
        IO.println "error invalidBound"
      else if draw < total then
        match selectFromList weights draw with
        | some index => IO.println s!"ok {index}"
        | none => IO.println "error internalSelectionFailure"
      else
        IO.println s!"error outOfRange {total} {draw}"
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
              printExecResult (replayMHStep
                Mcmc.Executable.Finite.TwoState.target
                Mcmc.Executable.Finite.TwoState.proposal current trace)
        else
          IO.println s!"error outOfRange 2 {proposalDraw}"
      else
        IO.println s!"error invalidState {state}"
  | .error error, _ | _, .error error => IO.println s!"error {error}"

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
  | _ =>
      IO.eprintln usage
      return 2
