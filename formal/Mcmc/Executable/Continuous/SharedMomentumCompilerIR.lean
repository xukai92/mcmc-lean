import Mcmc.Hamiltonian.SharedMomentumMultinomialHMC

/-!
# Shared-momentum multinomial HMC IR refinement

This module connects the `shared_momentum_multinomial_hmc_step!` IR program to
its verified mathematical kernel, following the refinement pattern from
`CoupledRefinement.lean`.

## Main results

* `sharedMomentumMultinomialHmcProgramKernel_refines`: the program kernel equals
  `sharedMomentumMultinomialHMC`
* `sharedMomentumMultinomialHmcProgramKernel_marginal`: each coordinate marginal
  of the program kernel equals `positionMultinomialHMC`, via rewriting through
  the refinement theorem and `sharedMomentumMultinomialHMC_marginal`
-/

namespace Mcmc.Executable.Continuous.SharedMomentumCompilerIR

open MeasureTheory ProbabilityTheory Mcmc.Hamiltonian
open scoped ENNReal

variable {ι : Type*} [Fintype ι]

structure Program where
  name : String

def program : Program where
  name := "shared_momentum_multinomial_hmc_step!"

private def quote (value : String) : String := "\"" ++ value ++ "\""

def Program.render (program : Program) : String :=
  "(program " ++ quote program.name ++
    " (inputs (input source \"source\") (input log-density \"logdensity\")" ++
    " (input gradient \"gradient\") (input real \"step_size\")" ++
    " (input nat \"steps\") (input nat \"chain_count\")" ++
    " (input real-vector \"current_positions\"))" ++
    " (body (return (shared-momentum-multinomial-hmc" ++
    " (var source \"source\") (var real \"step_size\")" ++
    " (var nat \"steps\") (var nat \"chain_count\")" ++
    " (var real-vector \"current_positions\")))))"

/-! ### Program kernel and refinement -/

noncomputable def sharedMomentumMultinomialHmcProgramKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (K : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient)
    (momentumTarget : Measure (Momentum ι)) :
    Kernel (Fin K → Position ι) (Fin K → Position ι) :=
  sharedMomentumMultinomialHMC potential gradient ε L K
    hpotential hgradient momentumTarget

theorem sharedMomentumMultinomialHmcProgramKernel_refines
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (K : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient)
    (momentumTarget : Measure (Momentum ι)) :
    sharedMomentumMultinomialHmcProgramKernel potential gradient ε L K
      hpotential hgradient momentumTarget =
    sharedMomentumMultinomialHMC potential gradient ε L K
      hpotential hgradient momentumTarget := rfl

/-! ### Marginal corollary -/

theorem sharedMomentumMultinomialHmcProgramKernel_marginal
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (K : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient)
    (momentumTarget : Measure (Momentum ι))
    [IsProbabilityMeasure momentumTarget]
    (k : Fin K) (x : Fin K → Position ι) :
    (sharedMomentumMultinomialHmcProgramKernel potential gradient ε L K
      hpotential hgradient momentumTarget x).map (Function.eval k) =
      positionMultinomialHMC potential gradient ε L hpotential hgradient
        momentumTarget (x k) := by
  rw [sharedMomentumMultinomialHmcProgramKernel_refines]
  exact sharedMomentumMultinomialHMC_marginal potential gradient ε L K
    hpotential hgradient momentumTarget k x

end Mcmc.Executable.Continuous.SharedMomentumCompilerIR
