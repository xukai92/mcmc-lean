# Project completion status

This matrix is the authoritative high-level status of the expanded Verified
Samplers goal. “Complete” means complete only at the stated boundary; it never
promotes invariance to convergence or an ideal-real theorem to arbitrary
floating-point code.

| Workstream | Evidence and exact status |
|---|---|
| General-state PG--HMC | Complete for common-target kernel invariance through Mcmc.Kernel.ComposableInference and the sign/quadrant GeneralStatePgHmc clients using the actual Gaussian SoftAbs transition. Runtime callback equality with a bound Lean kernel remains explicit. |
| Positive-horizon particle Gibbs | Complete for the supportable cumulative backward-potential schedule under primitive finite full support, including geometric TV convergence and a fixed-iteration particle-count limit. Recursive raw-current substitution beyond one step and horizon-uniform rates are not claimed. |
| Particle-count SMC asymptotics | Complete at fixed finite horizon through explicit C/N mean-square and probability bounds. A reusable strict-contraction theorem upgrades count-independent affine one-step estimates to uniform-in-time C/N bounds. A concrete positive-potential finite Feynman--Kac client with complete-refresh mutation is now instantiated: after every positive horizon its actual bootstrap population is exactly iid, its normalized target is the refresh law, and empirical MSE is exactly variance/N uniformly in time. Less degenerate mixing models and particle-count-uniform PG mixing remain open. |
| Diagonal SoftAbs / Xu--Ge solver | Complete for the exact Gaussian, bounded 2 + sin(q), and shifted-sinusoidal clients, including selected solver, reversal, phase volume, and invariance. Generic six-step Float64 solving still requires residual and primitive-error certificates. |
| Cross-language refinement | Complete for the declared IR operations, byte-for-byte generation, Lean oracle, trace replay, exact dyadic polynomial checks, and guarded bounded-error contracts. Platform libm, arbitrary callbacks, RNGs, and unrestricted IEEE execution remain outside the proof. |
| Ge et al. coroutine/operators | Complete for explicit copyable cursor state, generated PG--HMC descriptors, semantic BoundOperator bindings, and descriptor-ordered invariance. Opaque Task stack copying and arbitrary callback equivalence are not claimed. |
| Constrained transforms | Complete at exact measurable-equivalence semantics and guarded positive-log/open-unit refinement boundaries. Platform transcendental accuracy remains a premise. |
| Dynamic NUTS | Complete for conservative certified dynamic trees, stopped doubling, all-scales/adjacent builders, checked-or-identity execution, and replay tests. For ordinary root-dependent construction, Lean provides the richer complete-trace reversal certificate. Exact completed-tree combinatorics instantiate C.4; flat phase arrays build balanced recursive trees whose divergence/slice and vector U-turn checks instantiate stopping admissibility. Slice eligibility has exact weights/counts, and all streaming merges equal normalized retained-endpoint selection, including empty segments. Completed-tree conditional selection has detailed balance/stationarity. The outer augmentation and varying-fiber bridge are instantiated end to end at the finite mathematical layer: admissible joint slice weights are normalized on each completed tree, its certified rooted transition is lifted to the common phase state, and summing the state-dependent auxiliary law yields a reversible and stationary marginal sampler. IR version 17 declares the proved eligible-count streaming policy; Julia Reference interprets its recursive merges and Optimized independently samples the flattened eligible law. Bounded scalar comparison and two-endpoint U-turn certificates prove exact Boolean agreement outside strict uncertainty bands, and pointwise agreement lifts through the entire recursive flag tree. Endpoint dot-product errors are derived compositionally from coordinatewise phase bounds plus an explicit final-reduction rounding bound. Existing `LeapfrogStepCertificate` endpoints reindex onto common finite phase coordinates, assemble into bounded trajectories, and feed a theorem equating the computed callback with the exact `vectorAdjacentUTurn` predicate. A concrete kick-drift-kick recurrence now propagates nonnegative Lipschitz-gradient, gradient-evaluation, half-kick-rounding, and drift-rounding budgets; stored endpoint certificates are widened to its per-step schedule, mirrored by Julia BigFloat evaluation. Slice eligibility and divergence continuation similarly compose Hamiltonian bounds; the completed-tree runtime record releases bits only when every margin is stable. Remaining production work is proving actual backend operations satisfy the declared local budgets and proving the resulting auxiliary law; candidate-row equality remains invalid. |
| Practical slice sampling | Exact disintegration, interval kernels, randomized horizontal updates, joint trace reversal, guarded success, and literal ideal-real finite stepping-out/shrinkage semantics are present, including distinct malformed-trace failure and budget-exhaustion identity behavior. Lean proves both signed allocation-shift cases, equality of the actually stopped bracket, shrink-trace likelihood symmetry, and their end-to-end successful-trace likelihood assembly. Valid integer allocations are now exhibited as a finite type, and rerooting preserves their complete counting sums. Accepted-point restricted measure preservation and Haar offset preservation are also checked. Packaging the varying rejected-length and offset-dependent allocation strata into one restricted product-measure theorem remains; platform-specific callback, `log`, RNG, and arithmetic bounds remain explicit inputs. |
| Reversible jump | Complete for scalar, planar, dimension-generic product, three-dimensional executable, and nonlinear cubic triangular-shear clients. A compiler for arbitrary nonlinear diffeomorphisms is optional breadth. |
| Xu et al. 2021 | Complete for the corrected theorem surface and fully instantiated Gaussian and regularized-logistic meeting, marginal/target convergence, unbiasedness, and finite variance. The obstructed exponent-two statement is not asserted; more targets and full floating-point experiment reproduction remain extensions. |
| Concrete GR-HMC convergence | Complete for the bare one-dimensional Gaussian SoftAbs epsilon=1, L=1 chain, including drift, compact minorization, skeleton meeting, residue lift, and setwise convergence. No general ergodicity claim follows. |
| Adaptation | Predetermined schedules, finite freeze, proxy/containment closure, counterexamples, and warmup-only RWMH tests are complete. A concrete state-selected Bool rule changes forever, has a common one-half Doeblin component after substitution, and has machine-checked setwise convergence; its matching Julia diagnostic is active. Constructing proxy certificates for realistic continuous, genuinely history-dependent rules remains open. |
| PDMP foundations | General infrastructure and the stationary-suspension theorem are present. Exact Gaussian Zig-Zag nonexplosion/stationarity and unit-speed one-dimensional Gaussian BPS stationarity are complete. For general unbounded rates, Lean has proof-bearing total and partial inverse-integrated-hazard clocks tied to the integrated canonical BPS rate. The inactive-aware repeated executor uses fresh unit-exponential marks, restarts after exact events, absorbs after residual flow, and yields Markov truncated-horizon kernels for every event budget. Deterministic hazard-prefix replay is append-compatible and stable after completion; `CompletesFiniteHorizons` states the exact almost-sure finite-prefix obligation under the iid infinite hazard law. A concrete multidimensional Gaussian inverse, proof of this completion condition, construction of the untruncated limit kernel, stationarity, semigroup, and convergence remain open. |
| Diagnostics | All registered Julia suites are active and passing. Statistical and finite-difference tests are diagnostics, not replacements for formal or refinement theorems. |

## Release evidence

The complete release gate is:

    make test
    make check-docs-generated
    julia --project=docs docs/make.jl

The first command builds the full Lean library and oracle, checks generated IR
byte-for-byte, and runs every Julia testset.

## Dependency-ordered remaining work

1. Prove restricted trace preservation for the concrete stepping-out/shrinkage
   success transform and derive concrete platform bounds that instantiate its
   existing bounded comparison-refinement certificate.
2. Certify a production-style randomized NUTS recursion or prove a precisely
   scoped equivalence to the conservative dynamic-tree interface.
3. Extend the concrete indefinitely state-selected finite certificate to a
   realistic continuous and genuinely history-dependent rule through the
   existing diminishing-adaptation/containment proxy interface.
4. Extend the exact complete-refresh uniform particle result to partially
   mixing Feynman--Kac models, then derive particle-count-uniform PG mixing
   and stronger particle-MCMC asymptotics.
5. Instantiate the partial inverse-integrated-hazard interface for a concrete
   multidimensional Gaussian BPS and prove `CompletesFiniteHorizons`; then
   identify the stabilized limit of the truncated kernels and prove
   stationarity, followed separately by semigroup and ergodicity.
6. Add broader target/runtime instantiations without weakening the numerical
   boundary.
