import Mcmc.Hamiltonian.TransportCoupledMultinomialHMC

/-!
# Transport-coupled multinomial HMC IR program

This module defines the IR program representation for the 28th IR program,
`transport_coupled_multinomial_hmc_step!`, which implements the K-chain
transport-coupled multinomial HMC kernel.

The program follows the same pattern as `SharedMomentumCompilerIR.lean`:
a structure holding the program name and a renderer producing the
S-expression format consumed by the IR parser.
-/

namespace Mcmc.Executable.Continuous.TransportCoupledCompilerIR

open MeasureTheory ProbabilityTheory Mcmc.Hamiltonian
open scoped ENNReal

variable {ι : Type*} [Fintype ι]

structure Program where
  name : String

def program : Program where
  name := "transport_coupled_multinomial_hmc_step!"

private def quote (value : String) : String := "\"" ++ value ++ "\""

def Program.render (program : Program) : String :=
  "(program " ++ quote program.name ++
    " (inputs (input source \"source\") (input log-density \"logdensity\")" ++
    " (input gradient \"gradient\") (input real \"step_size\")" ++
    " (input nat \"steps\") (input nat \"chain_count\")" ++
    " (input real-vector \"current_positions\"))" ++
    " (body (return (transport-coupled-multinomial-hmc" ++
    " (var source \"source\") (var real \"step_size\")" ++
    " (var nat \"steps\") (var nat \"chain_count\")" ++
    " (var real-vector \"current_positions\")))))"

/-! ### Program kernel and refinement -/

noncomputable def transportCoupledMultinomialHmcProgramKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (K : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient)
    (momentumTarget : Measure (Momentum ι)) :
    Kernel (Fin K → Position ι) (Fin K → Position ι) :=
  transportCoupledMultinomialHMC potential gradient ε L K
    hpotential hgradient momentumTarget

theorem transportCoupledMultinomialHmcProgramKernel_refines
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (K : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient)
    (momentumTarget : Measure (Momentum ι)) :
    transportCoupledMultinomialHmcProgramKernel potential gradient ε L K
      hpotential hgradient momentumTarget =
    transportCoupledMultinomialHMC potential gradient ε L K
      hpotential hgradient momentumTarget := rfl

end Mcmc.Executable.Continuous.TransportCoupledCompilerIR
