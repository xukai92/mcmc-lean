import Mcmc.Executable.Continuous.TransportCoupledCompilerIR

/-!
# IR-kernel refinement for transport-coupled multinomial HMC

This module connects the `transport_coupled_multinomial_hmc_step!` IR program
to its verified mathematical kernel, following the refinement pattern from
`SharedMomentumCompilerIR.lean` and `CoupledRefinement.lean`.

## Main results

* `transportCoupledMultinomialHmcProgramKernel_refines`: the program kernel
  equals `transportCoupledMultinomialHMC`
* `transportCoupledMultinomialHmcProgramKernel_marginal`: each coordinate
  marginal of the program kernel equals `positionMultinomialHMC`, via
  rewriting through the refinement theorem and
  `transportCoupledMultinomialHMC_marginal`
-/

namespace Mcmc.Executable.Continuous.TransportCoupledRefinement

open MeasureTheory ProbabilityTheory Mcmc.Hamiltonian
open scoped ENNReal

variable {ι : Type*} [Fintype ι]

/-! ### Marginal corollary -/

theorem transportCoupledMultinomialHmcProgramKernel_marginal
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (K : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient)
    (momentumTarget : Measure (Momentum ι))
    [IsProbabilityMeasure momentumTarget]
    (k : Fin K) (x : Fin K → Position ι) :
    (TransportCoupledCompilerIR.transportCoupledMultinomialHmcProgramKernel
      potential gradient ε L K hpotential hgradient momentumTarget x).map
        (Function.eval k) =
      positionMultinomialHMC potential gradient ε L hpotential hgradient
        momentumTarget (x k) := by
  rw [TransportCoupledCompilerIR.transportCoupledMultinomialHmcProgramKernel_refines]
  exact transportCoupledMultinomialHMC_marginal potential gradient ε L K
    hpotential hgradient momentumTarget k x

#print axioms transportCoupledMultinomialHmcProgramKernel_marginal

end Mcmc.Executable.Continuous.TransportCoupledRefinement
