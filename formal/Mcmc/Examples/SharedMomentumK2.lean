import Mcmc.Hamiltonian.SharedMomentumMultinomialHMC

/-!
# K=2 instantiation of shared-momentum multinomial HMC

This module specializes the general `sharedMomentumMultinomialHMC_marginal`
theorem to K=2, showing that both coordinates (Fin 2) marginals equal
`positionMultinomialHMC`.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace Mcmc.Examples.SharedMomentumK2

open ProbabilityTheory Mcmc.Hamiltonian

variable {ι : Type*} [Fintype ι]

/-- At K=2, the first marginal of the shared-momentum multinomial kernel equals
the single-chain `positionMultinomialHMC`. -/
theorem marginal_zero
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ)
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (momentumTarget : Measure (Momentum ι))
    [IsProbabilityMeasure momentumTarget]
    (x : Fin 2 → Position ι) :
    (sharedMomentumMultinomialHMC potential gradient ε L 2
      hpotential hgradient momentumTarget x).map (Function.eval 0) =
      positionMultinomialHMC potential gradient ε L hpotential hgradient
        momentumTarget (x 0) :=
  sharedMomentumMultinomialHMC_marginal potential gradient ε L 2
    hpotential hgradient momentumTarget 0 x

/-- At K=2, the second marginal of the shared-momentum multinomial kernel equals
the single-chain `positionMultinomialHMC`. -/
theorem marginal_one
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ)
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (momentumTarget : Measure (Momentum ι))
    [IsProbabilityMeasure momentumTarget]
    (x : Fin 2 → Position ι) :
    (sharedMomentumMultinomialHMC potential gradient ε L 2
      hpotential hgradient momentumTarget x).map (Function.eval 1) =
      positionMultinomialHMC potential gradient ε L hpotential hgradient
        momentumTarget (x 1) :=
  sharedMomentumMultinomialHMC_marginal potential gradient ε L 2
    hpotential hgradient momentumTarget 1 x

end Mcmc.Examples.SharedMomentumK2
