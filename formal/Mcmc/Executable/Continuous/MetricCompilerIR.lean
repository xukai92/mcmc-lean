/-!
# Typed constant-metric HMC artifact descriptors

The metric kind is carried by the Lean type, preventing diagonal and dense
runtime inputs from being interchanged when the portable programs are built.
-/

namespace Mcmc.Executable.Continuous.MetricCompilerIR

inductive Kind where
  | diagonal
  | dense

inductive MetricInput : Kind → Type where
  | diagonalMass : MetricInput .diagonal
  | denseMass : MetricInput .dense

/-- The typed high-level command implemented by a constant-metric artifact.
Its index guarantees that the command and metric input have the same shape. -/
inductive Command : Kind → Type where
  | hmcStep (metricInput : MetricInput kind) : Command kind
  | multinomialHmcStep (metricInput : MetricInput kind) : Command kind

structure Program (kind : Kind) where
  name : String
  metricInput : MetricInput kind
  body : Command kind

def diagonalHmcProgram : Program .diagonal where
  name := "diagonal_hmc_step!"
  metricInput := .diagonalMass
  body := .hmcStep .diagonalMass

def denseHmcProgram : Program .dense where
  name := "dense_hmc_step!"
  metricInput := .denseMass
  body := .hmcStep .denseMass

def diagonalMultinomialHmcProgram : Program .diagonal where
  name := "diagonal_multinomial_hmc_step!"
  metricInput := .diagonalMass
  body := .multinomialHmcStep .diagonalMass

def denseMultinomialHmcProgram : Program .dense where
  name := "dense_multinomial_hmc_step!"
  metricInput := .denseMass
  body := .multinomialHmcStep .denseMass

private def quote (value : String) : String := "\"" ++ value ++ "\""

def Program.render {kind : Kind} (program : Program kind) : String :=
  let metricType := match kind with
    | .diagonal => "real-vector"
    | .dense => "real-matrix"
  let metricKind := match kind with
    | .diagonal => "diagonal"
    | .dense => "dense"
  let operation := match program.body with
    | .hmcStep _ => "metric-hmc"
    | .multinomialHmcStep _ => "metric-multinomial-hmc"
  "(program " ++ quote program.name ++
    " (inputs (input source \"source\") (input log-density \"logdensity\")" ++
    " (input gradient \"gradient\") (input real \"step_size\")" ++
    " (input nat \"steps\") (input real-vector \"current\")" ++
    " (input " ++ metricType ++ " \"mass\"))" ++
    " (body (return (" ++ operation ++ " " ++ metricKind ++
      " (var source \"source\") (var real \"step_size\")" ++
      " (var nat \"steps\") (var real-vector \"current\")" ++
      " (var " ++ metricType ++ " \"mass\")))))"

end Mcmc.Executable.Continuous.MetricCompilerIR
