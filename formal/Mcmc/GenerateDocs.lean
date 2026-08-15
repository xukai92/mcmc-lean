import Mcmc.Docs.Graph

/-! Emit documentation artifacts whose structure is maintained in Lean. -/

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
      IO.FS.writeFile path (Mcmc.Docs.renderGraphs ++ "\n")
      return 0
  | _ =>
      IO.eprintln "usage: generate_docs OUTPUT"
      return 2
