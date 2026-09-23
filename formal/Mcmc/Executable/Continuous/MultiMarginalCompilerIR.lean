import Mcmc.Hamiltonian.MultiMarginalTransportHMC

/-!
# Multi-marginal transport HMC artifact descriptor

The command implements K-chain shared-momentum multinomial HMC from
`MultiMarginalTransportHMC.lean`.  All K chains draw one common
momentum vector and independently select trajectory indices via
multinomial weighting.  The flattened `current_positions` real-vector
carries K×dim scalars; the runtime interpreter reshapes by `chain_count`.
-/

namespace Mcmc.Executable.Continuous.MultiMarginalCompilerIR

structure Program where
  name : String

def program : Program where
  name := "multi_marginal_transport_hmc_step!"

private def quote (value : String) : String := "\"" ++ value ++ "\""

def Program.render (program : Program) : String :=
  "(program " ++ quote program.name ++
    " (inputs (input source \"source\") (input log-density \"logdensity\")" ++
    " (input gradient \"gradient\") (input real \"step_size\")" ++
    " (input nat \"steps\") (input nat \"chain_count\")" ++
    " (input real-vector \"current_positions\"))" ++
    " (body (return (multi-marginal-transport-hmc" ++
    " (var source \"source\") (var real \"step_size\")" ++
    " (var nat \"steps\") (var nat \"chain_count\")" ++
    " (var real-vector \"current_positions\")))))"

end Mcmc.Executable.Continuous.MultiMarginalCompilerIR
