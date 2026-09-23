import Mcmc.Hamiltonian.MultiMarginalTransportHMC

/-!
# Multi-marginal transport HMC IR refinement

This module connects the `multi_marginal_transport_hmc_step!` IR program to
its verified mathematical kernel, following the refinement pattern from
`CoupledRefinement.lean`.

## Main results

* `multiMarginalTransportHmcProgramKernel_refines`: the program kernel equals
  `multiMarginalTransportHMC`
* `multiMarginalTransportHmcProgramKernel_marginal`: each coordinate marginal
  of the program kernel equals `positionMultinomialHMC`, via rewriting through
  the refinement theorem and `multiMarginalTransportHMC_marginal`
-/

namespace Mcmc.Executable.Continuous.MultiMarginalCompilerIR

open MeasureTheory ProbabilityTheory Mcmc.Hamiltonian
open scoped ENNReal

variable {ι : Type*} [Fintype ι]

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

/-! ### Program kernel and refinement -/

noncomputable def multiMarginalTransportHmcProgramKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (K : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient)
    (momentumTarget : Measure (Momentum ι)) :
    Kernel (Fin K → Position ι) (Fin K → Position ι) :=
  multiMarginalTransportHMC potential gradient ε L K
    hpotential hgradient momentumTarget

theorem multiMarginalTransportHmcProgramKernel_refines
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (K : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient)
    (momentumTarget : Measure (Momentum ι)) :
    multiMarginalTransportHmcProgramKernel potential gradient ε L K
      hpotential hgradient momentumTarget =
    multiMarginalTransportHMC potential gradient ε L K
      hpotential hgradient momentumTarget := rfl

/-! ### Marginal corollary -/

theorem multiMarginalTransportHmcProgramKernel_marginal
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (K : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient)
    (momentumTarget : Measure (Momentum ι))
    [IsProbabilityMeasure momentumTarget]
    (k : Fin K) (x : Fin K → Position ι) :
    (multiMarginalTransportHmcProgramKernel potential gradient ε L K
      hpotential hgradient momentumTarget x).map (Function.eval k) =
      positionMultinomialHMC potential gradient ε L hpotential hgradient
        momentumTarget (x k) := by
  rw [multiMarginalTransportHmcProgramKernel_refines]
  exact multiMarginalTransportHMC_marginal potential gradient ε L K
    hpotential hgradient momentumTarget k x

end Mcmc.Executable.Continuous.MultiMarginalCompilerIR
