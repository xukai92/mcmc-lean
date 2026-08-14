import Mcmc.Codegen.Julia.Finite

/-!
# Julia generator executable

The generated finite core is obtained by lowering typed finite sampler entry
programs to the restricted Julia AST and printing that AST. No Julia algorithm
is embedded as a source string in this executable.
-/

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
      match Mcmc.Codegen.Julia.Finite.module.render with
      | .ok source =>
          IO.FS.writeFile path source
          return 0
      | .error message =>
          IO.eprintln s!"generation failed: {message}"
          return 1
  | _ =>
      IO.eprintln "usage: generate_julia OUTPUT"
      return 2
