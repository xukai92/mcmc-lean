import Mcmc.Executable.Continuous.MultinomialHMC

/-!
# Typed multinomial-HMC artifact descriptor
-/

namespace Mcmc.Executable.Continuous.MultinomialCompilerIR

open Mcmc.Hamiltonian

inductive Command where
  | hmcStep

structure Program where
  name : String
  body : Command

def program : Program where
  name := "multinomial_hmc_step!"
  body := .hmcStep

/-- Ideal finite-choice semantics of the typed multinomial command. -/
noncomputable def Command.choicePMF {ι : Type*} [Fintype ι]
    (_command : Command) (potential : Position ι → ℝ)
    (gradient : Position ι → Position ι) (ε : ℝ) (L : ℕ)
    (phase : PhaseSpace ι) : PMF (Fin (L + 1) × Fin (L + 1)) :=
  Mcmc.Executable.Continuous.multinomialHmcChoicePMF
    potential gradient ε L phase

/-- The generated command's ideal output law is exactly the verified
randomized-origin multinomial trajectory law. -/
theorem program_choicePMF_map_result {ι : Type*} [Fintype ι]
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (phase : PhaseSpace ι) :
    (program.body.choicePMF potential gradient ε L phase).map
        (fun choice => Mcmc.Executable.Continuous.multinomialHmcResult
          gradient ε choice.1 choice.2 phase) =
      randomizedMultinomialLeapfrogPMF potential gradient ε L phase :=
  Mcmc.Executable.Continuous.multinomialHmcChoicePMF_map_result
    potential gradient ε L phase

private def quote (value : String) : String := "\"" ++ value ++ "\""

def Program.render (program : Program) : String :=
  "(program " ++ quote program.name ++
    " (inputs (input source \"source\") (input log-density \"logdensity\")" ++
    " (input gradient \"gradient\") (input real \"step_size\")" ++
    " (input nat \"steps\") (input real-vector \"current\"))" ++
    " (body (return (multinomial-hmc (var source \"source\")" ++
    " (var real \"step_size\") (var nat \"steps\")" ++
    " (var real-vector \"current\")))))"

end Mcmc.Executable.Continuous.MultinomialCompilerIR
