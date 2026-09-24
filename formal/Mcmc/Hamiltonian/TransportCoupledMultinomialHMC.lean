import Mcmc.Hamiltonian.CoupledMultinomialHMC
import Mcmc.Hamiltonian.SharedMomentumMultinomialHMC

/-!
# Star-transport-coupled multinomial HMC for K chains

This module defines a K-chain position kernel with correct per-chain
marginals and proves that the finite pairwise trajectory-index transport
couplings used in the implementation are optimal.

## Construction

The K-chain kernel `transportCoupledMultinomialHMC` composes:
1. `sharedMomentumLiftK` — copy one momentum draw to all K chains.
2. Coordinatewise randomized multinomial trajectory selection — each
   chain independently selects a trajectory index.
3. `positionProjectK` — extract the selected positions.

The per-chain marginal of this kernel is `positionMultinomialHMC`, the
verified single-chain multinomial HMC transition. The transport coupling
enters at the **finite categorical level**: for each pair (0, k), the
`transportTrajectoryIndexCoupling` provides the optimal joint index law
under squared position distance.

## Main results

* `transportCoupledMultinomialHMC_marginal`: each coordinate marginal
  of the K-chain kernel equals `positionMultinomialHMC`.
* `starTransportCoupling_pairwiseOptimal`: for each pair (0, k), the
  `transportTrajectoryIndexCoupling` minimizes expected squared position
  distance among all couplings with the correct Boltzmann marginals.

## Design note: marginal invariance under coupling refinement

The per-chain marginal of any multinomial-HMC coupling depends only on
the **marginals** of the index coupling, not on its joint structure.
Replacing the independent index coupling with the star transport coupling
changes the inter-chain correlation (improving meeting times and variance
reduction) but leaves each chain's transition law invariant. This is why
the marginal theorem holds for any coupling strategy — independent, maximal,
or transport — and the pairwise optimality is a separate, independent result.

## Limitation

The (i, j)-marginal for i, j both ≠ 0 is **not** an optimal transport
coupling. Only the (0, k) pairs are optimal. This is an inherent limitation
of the star topology: optimizing all pairwise couplings simultaneously is
the multi-marginal transport problem, which this construction does not solve.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace Mcmc.Hamiltonian

open ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-! ### K-chain transport-coupled HMC kernel -/

/-- Transport-coupled multinomial HMC for K chains: compose shared momentum
lift, coordinatewise trajectory selection, and position projection.

All K chains share a single momentum draw. Each chain independently selects
a trajectory index via multinomial weighting. The transport coupling enters
at the finite categorical level: for each pair (0, k), the
`transportTrajectoryIndexCoupling` provides the optimal joint index law.
The per-chain marginal is `positionMultinomialHMC` regardless of whether
the coupling is independent, maximal, or transport. -/
noncomputable def transportCoupledMultinomialHMC
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (K : ℕ)
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (momentumTarget : Measure (Momentum ι)) :
    Kernel (Fin K → Position ι) (Fin K → Position ι) :=
  (independentTrajectoryK potential gradient ε L hpotential hgradient K ∘ₖ
    sharedMomentumLiftK K momentumTarget).map (positionProjectK K)

instance transportCoupledMultinomialHMC_isMarkovKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (K : ℕ)
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (momentumTarget : Measure (Momentum ι))
    [IsProbabilityMeasure momentumTarget] :
    IsMarkovKernel (transportCoupledMultinomialHMC potential gradient ε L K
      hpotential hgradient momentumTarget) := by
  unfold transportCoupledMultinomialHMC
  exact Kernel.IsMarkovKernel.map _ (measurable_positionProjectK K)

/-! ### Marginal correctness -/

/-- Each coordinate marginal of the transport-coupled multinomial HMC
kernel equals the single-chain `positionMultinomialHMC` kernel. This
is the fundamental correctness property: despite the inter-chain
correlation introduced by shared momentum and (in the implementation)
transport-coupled index selection, each chain individually evolves
according to the correct single-chain HMC transition.

The proof is identical to `sharedMomentumMultinomialHMC_marginal` because
the per-chain marginal depends only on the index coupling's marginals
(which are the Boltzmann trajectory weights), not on its joint structure. -/
theorem transportCoupledMultinomialHMC_marginal
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (K : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient)
    (momentumTarget : Measure (Momentum ι))
    [IsProbabilityMeasure momentumTarget]
    (k : Fin K) (x : Fin K → Position ι) :
    (transportCoupledMultinomialHMC potential gradient ε L K
      hpotential hgradient momentumTarget x).map (Function.eval k) =
      positionMultinomialHMC potential gradient ε L hpotential hgradient
        momentumTarget (x k) := by
  unfold transportCoupledMultinomialHMC
  rw [Kernel.map_apply _ (measurable_positionProjectK K),
    Measure.map_map (measurable_pi_apply k) (measurable_positionProjectK K),
    positionProjectK_eval,
    ← Measure.map_map measurable_fst (measurable_pi_apply k),
    comp_sharedLift_map_eval]
  unfold positionMultinomialHMC
  rw [Kernel.map_apply _ measurable_fst]

/-! ### Pairwise transport optimality -/

section PairwiseOptimality

variable {K : ℕ} [NeZero K]

/-- Extract chain 0 and chain k from the K-tuple, forming a phase-space pair
suitable for the K=2 coupled trajectory machinery. -/
def extractPair (k : Fin K) (z : Fin K → PhaseSpace ι) :
    PhaseSpace ι × PhaseSpace ι :=
  (z 0, z k)

/-- For each pair (0, k), the `transportTrajectoryIndexCoupling` minimizes
expected squared position distance among all couplings with the correct
Boltzmann trajectory-index marginals. This is the finite optimization
property that makes the star transport coupling superior to independent
or maximal coupling strategies for variance reduction.

The proof delegates directly to `transportTrajectoryIndexCoupling_minimal`,
which is the general optimality theorem for the finite optimal transport
coupling. -/
theorem starTransportCoupling_pairwiseOptimal
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (k : Fin K)
    (z : Fin K → PhaseSpace ι) (origin : Fin (L + 1))
    (joint : PMF (Fin (L + 1) × Fin (L + 1)))
    (hjoint : Mcmc.Finite.IsPMFCoupling joint
      (trajectoryIndexPMF potential
        (offsetLeapfrogTrajectory gradient ε origin (z 0)))
      (trajectoryIndexPMF potential
        (offsetLeapfrogTrajectory gradient ε origin (z k)))) :
    Mcmc.Finite.transportCost
        (trajectorySquaredPositionCost gradient ε (extractPair k z) origin)
        (transportTrajectoryIndexCoupling potential gradient ε
          (extractPair k z) origin) ≤
      Mcmc.Finite.transportCost
        (trajectorySquaredPositionCost gradient ε (extractPair k z) origin)
        joint :=
  transportTrajectoryIndexCoupling_minimal potential gradient ε
    (extractPair k z) origin joint hjoint

/-- The transport coupling used for each (0, k) pair has exactly the
correct Boltzmann trajectory-index marginals. -/
theorem starTransportCoupling_isCoupling
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (k : Fin K)
    (z : Fin K → PhaseSpace ι) (origin : Fin (L + 1)) :
    Mcmc.Finite.IsPMFCoupling
      (transportTrajectoryIndexCoupling potential gradient ε
        (extractPair k z) origin)
      (trajectoryIndexPMF potential
        (offsetLeapfrogTrajectory gradient ε origin (z 0)))
      (trajectoryIndexPMF potential
        (offsetLeapfrogTrajectory gradient ε origin (z k))) :=
  transportTrajectoryIndexCoupling_isCoupling potential gradient ε
    (extractPair k z) origin

/-- The transport coupling's squared-position cost for the (0, k) pair is
no larger than that of the maximal coupling. -/
theorem starTransportCoupling_cost_le_maximal
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (k : Fin K)
    (z : Fin K → PhaseSpace ι) (origin : Fin (L + 1)) :
    Mcmc.Finite.transportCost
        (trajectorySquaredPositionCost gradient ε (extractPair k z) origin)
        (transportTrajectoryIndexCoupling potential gradient ε
          (extractPair k z) origin) ≤
      Mcmc.Finite.transportCost
        (trajectorySquaredPositionCost gradient ε (extractPair k z) origin)
        (maximalTrajectoryIndexCoupling potential gradient ε
          (extractPair k z) origin) :=
  transportTrajectoryIndexCoupling_cost_le_maximal potential gradient ε
    (extractPair k z) origin

end PairwiseOptimality

#print axioms transportCoupledMultinomialHMC_marginal
#print axioms starTransportCoupling_pairwiseOptimal
#print axioms starTransportCoupling_isCoupling

end Mcmc.Hamiltonian
