import Mcmc.Hamiltonian.MultiMarginalTransportHMC

/-!
# K=2 instantiation of multi-marginal transport HMC

This module specializes the general `multiMarginalTransportHMC_marginal`
theorem to K=2, showing that both coordinates (Fin 2) marginals equal
`positionMultinomialHMC`.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace Mcmc.Examples.MultiMarginalTransportK2

open ProbabilityTheory Mcmc.Hamiltonian

variable {ι : Type*} [Fintype ι]

/-- At K=2, the first marginal of the multi-marginal kernel equals
the single-chain `positionMultinomialHMC`. -/
theorem marginal_zero
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ)
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (momentumTarget : Measure (Momentum ι))
    [IsProbabilityMeasure momentumTarget]
    (x : Fin 2 → Position ι) :
    (multiMarginalTransportHMC potential gradient ε L 2
      hpotential hgradient momentumTarget x).map (Function.eval 0) =
      positionMultinomialHMC potential gradient ε L hpotential hgradient
        momentumTarget (x 0) :=
  multiMarginalTransportHMC_marginal potential gradient ε L 2
    hpotential hgradient momentumTarget 0 x

/-- At K=2, the second marginal of the multi-marginal kernel equals
the single-chain `positionMultinomialHMC`. -/
theorem marginal_one
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ)
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (momentumTarget : Measure (Momentum ι))
    [IsProbabilityMeasure momentumTarget]
    (x : Fin 2 → Position ι) :
    (multiMarginalTransportHMC potential gradient ε L 2
      hpotential hgradient momentumTarget x).map (Function.eval 1) =
      positionMultinomialHMC potential gradient ε L hpotential hgradient
        momentumTarget (x 1) :=
  multiMarginalTransportHMC_marginal potential gradient ε L 2
    hpotential hgradient momentumTarget 1 x

end Mcmc.Examples.MultiMarginalTransportK2
