# Multi-marginal transport coupling: construction and limitations

## Transport construction

The star-transport-coupled multinomial HMC kernel uses a star topology:
chain 0 is the reference, and each pair (0, k) for k = 1, ..., K-1 uses
the existing K=2 `transportTrajectoryIndexCoupling` to jointly select
trajectory indices under squared position distance.

### Formal definitions (Lean 4)

| Definition | Module | Description |
|---|---|---|
| `transportCoupledMultinomialHMC` | `Mcmc.Hamiltonian.TransportCoupledMultinomialHMC` | K-chain position kernel: `Kernel (Fin K → Position ι) (Fin K → Position ι)` |
| `extractPair` | same | Extract (chain 0, chain k) phase-space pair |
| `transportTrajectoryIndexCoupling` | `Mcmc.Hamiltonian.CoupledMultinomialHMC` | K=2 optimal transport coupling under `trajectorySquaredPositionCost` |

### Formal theorems

| Theorem | Module | Statement |
|---|---|---|
| `transportCoupledMultinomialHMC_marginal` | `TransportCoupledMultinomialHMC` | `(kernel x).map (eval k) = positionMultinomialHMC(x k)` for all k |
| `starTransportCoupling_pairwiseOptimal` | same | Transport cost of (0, k) coupling ≤ cost of any coupling with same marginals |
| `starTransportCoupling_isCoupling` | same | Transport coupling has correct Boltzmann trajectory-index marginals |
| `starTransportCoupling_cost_le_maximal` | same | Transport cost ≤ maximal coupling cost |
| `transportCoupledMultinomialHmcProgramKernel_refines` | `TransportCoupledCompilerIR` | Program kernel = `transportCoupledMultinomialHMC` |
| `transportCoupledMultinomialHmcProgramKernel_marginal` | `TransportCoupledRefinement` | Marginal corollary for IR program kernel |

## Star topology limitation

**The (i, j)-marginal for i, j both ≠ 0 is NOT an optimal transport coupling.**

Only (0, k) pairs minimize the expected squared position distance cost.
The (i, j) pair for i, j ≠ 0 is implicitly coupled through the shared
reference chain 0, but this induced coupling is generally suboptimal.

### Why this is inherent

Optimizing all K(K-1)/2 pairwise couplings simultaneously is the
multi-marginal optimal transport problem. For K > 2, the star construction
solves K-1 independent K=2 problems (sharing the reference chain) rather
than the NP-hard multi-marginal problem. This is a deliberate design
choice: the star topology reuses the existing K=2 transport machinery
directly, avoids the combinatorial complexity of multi-marginal transport,
and still provides optimal coupling between the reference chain and each
other chain.

### When the star coupling is sufficient

The star coupling is optimal when:
1. The primary goal is coupling chain 0 with each other chain (e.g., for
   meeting-time estimation between a reference chain and test chains).
2. The chains are close to a common stationary distribution (so the
   induced (i, j) coupling is near-optimal because both chains are
   close to chain 0).

The star coupling is suboptimal when:
1. Pairwise correlations between non-reference chains are important
   (e.g., for multi-chain variance reduction across all pairs).
2. The chains are far apart and the reference chain is not representative.

## Julia implementation

The Julia implementation in `Optimized.transport_coupled_multinomial_hmc_step!`
implements the star coupling faithfully:
1. Shared momentum and shared trajectory origin for all K chains.
2. Chain 0's trajectory index sampled from its Boltzmann marginal.
3. For each k ≥ 1: pairwise transport plan solved greedily for the
   (0, k) cost matrix; chain k's index sampled from the conditional
   of the transport plan given chain 0's selected index.

The greedy transport solver `_solve_transport_plan!` finds a feasible
transport plan by iteratively assigning mass to the lowest-cost edge.
This is not the LP-optimal plan but a practical approximation that
runs in O(n²) time per pair (n = trajectory length + 1).
