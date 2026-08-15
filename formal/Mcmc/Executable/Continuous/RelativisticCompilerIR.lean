/-!
# Corrected relativistic multinomial-HMC artifact descriptor

The command uses a diagonal constant metric, the dimension-correct radial law,
uniform spherical direction generated from Gaussian coordinates, and inverse
factor transport. It is the executable constant-metric specialization of the
corrected Xu--Ge construction; position-dependent metrics additionally require
the certified implicit-solver interface.
-/

namespace Mcmc.Executable.Continuous.RelativisticCompilerIR

structure Program where
  name : String

def program : Program where
  name := "relativistic_multinomial_hmc_step!"

def certifiedPositionDependentProgram : Program where
  name := "certified_relativistic_multinomial_hmc_step!"

private def quote (value : String) : String := "\"" ++ value ++ "\""

def Program.render (program : Program) : String :=
  if program.name = certifiedPositionDependentProgram.name then
    "(program " ++ quote program.name ++
    " (inputs (input source \"source\") (input hamiltonian \"hamiltonian\")" ++
    " (input metric-factor \"metric_factor\") (input integrator \"integrator\")" ++
    " (input real \"step_size\") (input nat \"steps\")" ++
    " (input real-vector \"current\") (input real \"relativistic_mass\"))" ++
    " (body (return (certified-relativistic-multinomial-hmc" ++
    " (var source \"source\") (var real \"step_size\")" ++
    " (var nat \"steps\") (var real-vector \"current\")" ++
    " (var real \"relativistic_mass\")))))"
  else "(program " ++ quote program.name ++
    " (inputs (input source \"source\") (input log-density \"logdensity\")" ++
    " (input gradient \"gradient\") (input real \"step_size\")" ++
    " (input nat \"steps\") (input real-vector \"current\")" ++
    " (input real-vector \"mass\") (input real \"relativistic_mass\"))" ++
    " (body (return (relativistic-multinomial-hmc" ++
    " (var source \"source\") (var real \"step_size\")" ++
    " (var nat \"steps\") (var real-vector \"current\")" ++
    " (var real-vector \"mass\") (var real \"relativistic_mass\")))))"

end Mcmc.Executable.Continuous.RelativisticCompilerIR
