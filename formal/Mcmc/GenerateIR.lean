import Mcmc.Executable.IRFormat

/-! Emit the versioned sampler IR artifact consumed by Julia Reference. -/

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
      IO.FS.writeFile path Mcmc.Executable.IRFormat.render
      return 0
  | _ =>
      IO.eprintln "usage: generate_ir OUTPUT"
      return 2
