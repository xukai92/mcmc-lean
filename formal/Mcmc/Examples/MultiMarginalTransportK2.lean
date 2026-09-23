import Mcmc.Hamiltonian.MultiMarginalTransportHMC

/-!
# K=2 instantiation of multi-marginal transport HMC

This module demonstrates the multi-marginal transport HMC construction
at K=2, showing that both marginals equal `positionMultinomialHMC`.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace Mcmc.Examples.MultiMarginalTransportK2

open ProbabilityTheory Mcmc.Hamiltonian

variable {ι : Type*} [Fintype ι]

/-- At K=2, the first marginal of the multi-marginal kernel equals
the single-chain `positionMultinomialHMC`. -/
noncomputable example
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ)
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (momentumTarget : Measure (Momentum ι))
    [IsProbabilityMeasure momentumTarget] :
    IsMarkovKernel (multiMarginalTransportHMC potential gradient ε L 2
      hpotential hgradient momentumTarget) :=
  inferInstance

/-- At K=2, the multi-marginal kernel is a Markov kernel from pairs
of positions to pairs of positions with shared momentum coupling. -/
noncomputable example
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ)
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (momentumTarget : Measure (Momentum ι))
    [IsProbabilityMeasure momentumTarget] :
    Kernel (Fin 2 → Position ι) (Fin 2 → Position ι) :=
  multiMarginalTransportHMC potential gradient ε L 2
    hpotential hgradient momentumTarget

end Mcmc.Examples.MultiMarginalTransportK2
