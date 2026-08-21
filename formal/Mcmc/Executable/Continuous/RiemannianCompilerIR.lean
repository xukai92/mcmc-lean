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

def approximateProgram : Program where
  name := "approximate_classical_rmhmc_step!"

/-- Generic dense-metric bounded-residual RMHMC reference entry point. -/
def denseProgram : Program where
  name := "dense_rmhmc_step!"

/-- Structured-momentum bounded-residual RMHMC reference entry point. -/
def structuredProgram : Program where
  name := "random_sketch_rmhmc_step!"

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

def renderApproximate : String :=
  "(program " ++ quote approximateProgram.name ++
  " (inputs (input source \"source\") (input hamiltonian \"hamiltonian\")" ++
  " (input metric-factor \"metric_factor\") (input integrator \"integrator\")" ++
  " (input real \"step_size\") (input nat \"steps\")" ++
  " (input real-vector \"current\") (input real \"residual_tolerance\"))" ++
  " (body (return (approximate-classical-rmhmc (var source \"source\")" ++
  " (var real \"step_size\") (var nat \"steps\")" ++
  " (var real-vector \"current\") (var real \"residual_tolerance\")))))"

/-- Render the explicit dense-RMHMC alias of the generic classical command. -/
def renderDense : String :=
  "(program " ++ quote denseProgram.name ++
  " (inputs (input source \"source\") (input hamiltonian \"hamiltonian\")" ++
  " (input metric-factor \"metric_factor\") (input integrator \"integrator\")" ++
  " (input real \"step_size\") (input nat \"steps\")" ++
  " (input real-vector \"current\") (input real \"residual_tolerance\"))" ++
  " (body (return (approximate-classical-rmhmc (var source \"source\")" ++
  " (var real \"step_size\") (var nat \"steps\")" ++
  " (var real-vector \"current\") (var real \"residual_tolerance\")))))"

/-- Render structured RMHMC with a callback-defined momentum refresh. -/
def renderStructured : String :=
  "(program " ++ quote structuredProgram.name ++
  " (inputs (input source \"source\") (input hamiltonian \"hamiltonian\")" ++
  " (input momentum-sampler \"momentum_sampler\")" ++
  " (input integrator \"integrator\") (input real \"step_size\")" ++
  " (input nat \"steps\") (input real-vector \"current\")" ++
  " (input real \"residual_tolerance\"))" ++
  " (body (return (structured-rmhmc (var source \"source\")" ++
  " (var real \"step_size\") (var nat \"steps\")" ++
  " (var real-vector \"current\") (var real \"residual_tolerance\")))))"

end Mcmc.Executable.Continuous.RiemannianCompilerIR
