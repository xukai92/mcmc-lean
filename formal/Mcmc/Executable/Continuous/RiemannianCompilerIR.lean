/-!
# Classical RMHMC artifact descriptor

The reference command uses position-dependent Gaussian momentum transported
by the inverse metric factor and a certificate-gated generalized-leapfrog
endpoint Metropolis transition.
-/

namespace Mcmc.Executable.Continuous.RiemannianCompilerIR

structure Program where
  name : String

def program : Program where
  name := "classical_rmhmc_step!"

private def quote (value : String) : String := "\"" ++ value ++ "\""

def Program.render (program : Program) : String :=
  "(program " ++ quote program.name ++
  " (inputs (input source \"source\") (input hamiltonian \"hamiltonian\")" ++
  " (input metric-factor \"metric_factor\") (input integrator \"integrator\")" ++
  " (input real \"step_size\") (input nat \"steps\")" ++
  " (input real-vector \"current\"))" ++
  " (body (return (classical-rmhmc (var source \"source\")" ++
  " (var real \"step_size\") (var nat \"steps\")" ++
  " (var real-vector \"current\")))))"

end Mcmc.Executable.Continuous.RiemannianCompilerIR
