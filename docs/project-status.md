# Project completion status

This matrix is the authoritative high-level status of the Verified Samplers
core. “Complete” means complete only at the stated boundary; it never promotes
invariance to convergence or an ideal-real theorem to arbitrary floating-point
code.

For a compact method-by-property view, start with the
[progress matrix](progress.md). This page is the detailed qualification ledger.

## Core completion boundary

The release goal is exact sampler mathematics, auditable executable
implementations, and tests that keep those implementations aligned with the
declared semantics. It includes the existing kernel/invariance theorems,
explicitly scoped convergence results, generated/reference/optimized Julia
paths, reproducible examples, and deterministic, property, and statistical
diagnostics.

The following are useful research extensions, but are **not core-completion
blockers**:

- generic IEEE-754, platform `libm`, serializer, or RNG refinement theorems;
- completion of the experimental per-execution floating-point certificate
  stack, including multi-step GR-HMC error transport;
- equivalence with production recursive NUTS rather than the checked dynamic
  tree algorithms already supplied;
- multidimensional BPS weak-forward uniqueness and refreshed ergodicity;
- realistic never-freezing adaptation without an exact target-refresh branch;
- model-uniform growing-horizon SMC/particle-MCMC stability; and
- exhaustive target breadth or reproduction of every paper experiment.

Existing certificate and hard-analysis modules remain built, documented, and
available for later work. Parking them changes the project milestone, not the
strength of any theorem already proved.

| Workstream | Evidence and exact status |
|---|---|
| General-state PG--HMC | Complete for common-target kernel invariance through Mcmc.Kernel.ComposableInference and the sign/quadrant GeneralStatePgHmc clients using the actual Gaussian SoftAbs transition. Runtime callback equality with a bound Lean kernel remains explicit. |
| Positive-horizon particle Gibbs | Complete for the supportable cumulative backward-potential schedule under primitive finite full support, including fixed-count geometric TV convergence, a fixed-iteration particle-count limit, and one geometric rate uniform over every particle count `N ≥ 2` at each fixed horizon. For every tolerance, one iteration threshold controls all counts simultaneously. Consequently convergence holds for any particle-count schedule and any independently chosen PG-iteration schedule tending to infinity; counts may grow, shrink, or oscillate. For jointly varying model horizons, a new scalar closure theorem proves convergence whenever the actual horizon-indexed TV errors have certified geometric bounds with one positive minorization floor and the PG-iteration schedule diverges; trajectory types may vary behind that scalar interface. Primitive full support alone is not claimed to supply a horizon-uniform floor, and recursive raw-current substitution beyond one step remains open. |
| Particle-count SMC asymptotics | Complete at fixed finite horizon through explicit C/N mean-square and probability bounds. Reusable theorems now cover time-inhomogeneous affine recurrences: stage contraction and Monte Carlo noise may both vary under one strict contraction ceiling and noise ceiling, yielding a uniform-in-time C/N bound and consistency along arbitrary horizon schedules as particle count tends to infinity. Complete-refresh, constant partial-refresh, and genuinely time-varying partial-refresh finite Feynman--Kac clients are instantiated; the varying client permits an arbitrary refresh schedule under one positive lower bound. The constant client additionally has an explicit time-uniform `C/(N ε²)` deviation bound. This is a stable-model interface plus concrete clients, not a general stability theorem for every SMC model. The associated backward-potential particle-Gibbs theorem is uniform in particle count at each fixed horizon. Julia exposes a standalone seeded one-step particle-count/TV experiment matching the registered regression diagnostic. Joint growing-horizon particle-Gibbs asymptotics remain open. |
| Diagonal SoftAbs / Xu--Ge solver | Complete for the exact Gaussian, bounded 2 + sin(q), and shifted-sinusoidal clients, including selected solver, reversal, phase volume, and invariance. A generated strongly convex quartic target supplies an additional polynomial position-dependent Hessian client: Lean proves its emitted formulas and positivity, Julia interprets the same artifact, and an oracle-checked exact-rational Hessian record feeds directly into the guarded SoftAbs metric-entry certificate. Besides the exact unit-smoothing/zero-Hessian entry, nonzero Float64 entries at `(α,h)=(1,1)`, `(1,0.1)`, and the rounded-product case `(0.1,0.1)` are certified end to end: a checked argument-product residual, proved `tanh` enclosure and one-Lipschitz transport, exact division residual, square-root enclosure, reciprocal residual, and a 32-term rational-series log enclosure compose into one `SoftAbsMetricEntryCertificate`. A linked `(α,h,U,p)=(0.1,0.1,0.5,0.25)` record additionally propagates the factor through rounded transformed-momentum/radicand arithmetic, kinetic square root, log determinant, and final scalar Hamiltonian energy. Purely rational lower-bound certificates now upper-bound every metric and endpoint error. Finite families automatically take maximum endpoint and stabilized-exponential errors and feed an arithmetic-aware multinomial-selection certificate; Julia/oracle exercise three rounded energies, transported weights, actual cumulative sums, the scaled draw, and computed-boundary separation. The maintained bounded run closes a fully linked one-step/two-endpoint practical selection. Its multi-step successor checks exact rounded state threading, identifies every local endpoint with the established exact GR step, and proves the correct `local + K·prior` trajectory recurrence. A regional rational certificate supplies a sound pairwise step bound without asserting false global Lipschitzness. Composing that bound through a complete long-trajectory selection certificate is parked with the optional numerical-refinement layer. RNG distributional semantics also remain explicit. |
| Cross-language refinement | Complete for the declared IR operations, byte-for-byte generation, Lean oracle, trace replay, exact dyadic polynomial checks, and guarded bounded-error contracts. Lean now parses the artifact S-expression grammar and decodes the categorical and generic finite-MH declarations back into typed finite IR, with byte-for-byte re-render theorems and ill-typed-input rejection. This is not yet a correspondence theorem for the Julia parser. Generated restricted expressions have an exact-real backend and recursive semantic equality. Gaussian and quartic Float64 callbacks serialize exact-rational value/force/Hessian errors checked by the Lean oracle. Exact-dyadic Gaussian leapfrog checking covers an actual maintained eight-step Float64 trajectory, and a target-independent rounded checker serializes and Lean-checks the exact rational residual of every half kick, drift, and final kick; both reject tampered records. The generic arithmetic checker is now composed formally with two generated quartic callback certificates, and Julia/Lean oracle regressions cover an actual optimized quartic step. These are per-execution primitive witnesses, not a uniform IEEE theorem. Every generated Gaussian, sinusoidal, and quartic artifact is exercised through the public RWMH, scalar-HMC, and practical-slice adapters; the seeded quartic experiment compares all three, while its slice trace submits every observed callback to the oracle. Analytic reciprocal/square-root/log transport is proved, and `SoftAbsLocalPrimitiveBackend` upgrades local operation bounds automatically. Assumption-free ex-post square-root, reciprocal, positive-log, nonpositive-exponential, and positive-branch SoftAbs certificates convert actual Float64 inputs and outputs to exact rationals. The maintained bounded `2+sin(q)` solver now has linked per-execution certificates through sine/cosine, transformed momentum, rounded radicand, square root, reciprocal, all 29 callback invocations, all 28 rounded affine updates, both residual-to-fixed-point bounds, cross-loop sensitivity, the final momentum kick, the complete exact phase endpoint, and Hamiltonian transport from the rounded endpoint. Lean-oracle tests reject count/order/linkage/rate/combined-radius/endpoint-energy tampering. Lean proves `max(0,1+x) ≤ exp x ≤ 1/(1-x)` on `x≤0`, `x/(1+x) ≤ tanh x ≤ min(x,1)`, and the needed one-Lipschitz transports. Rounded arguments and divisions are checked for actual executions. Platform-wide libm bounds, arbitrary callbacks, RNG laws, serializer correctness beyond checked records, and a priori uniform IEEE bounds remain outside the proof. |
| Ge et al. coroutine/operators | Complete for explicit copyable cursor state, generated PG--HMC descriptors, semantic BoundOperator bindings, and descriptor-ordered invariance. A seeded generated-schedule experiment binds exact binary-latent Gibbs and scalar conditional HMC callbacks for a Gaussian mixture and reports its known joint marginals. Opaque Task stack copying, arbitrary callback equivalence, and Float64 kernel refinement are not claimed. |
| Constrained transforms | Complete at exact measurable-equivalence semantics and guarded positive-log/open-unit refinement boundaries. Platform transcendental accuracy remains a premise. |
| Dynamic NUTS | Complete for conservative certified dynamic trees, stopped doubling, checked-or-identity execution, eligible-count streaming, finite auxiliary-law stationarity, completed-tree C.4 rerooting, recursive flag/callback refinement, and linked leapfrog error certificates. Julia routes canonical `NUTS` through the productive completed-tree Reference: each possible root receives its unique reconstruction trace and selection is restricted to the common C.4-admissible component. `CheckedRecursiveDynamicHMC` retains the conservative fixed-trace checked-or-identity experiment. The separately namespaced production-shaped fixed-parameter `Optimized.NUTS` runtime covers classic/generalized/strict-generalized termination, multinomial/slice selection, and ordinary/jittered/tempered leapfrog over every maintained fixed metric, but remains runtime-only. Exact-dyadic and rounded Gaussian certificates exercise the numerical boundary. Arbitrary Float64 trajectory/callback refinement and equivalence with the production-shaped transition remain open. |
| Practical slice sampling | Complete at the exact mathematical layer for bounded stepping-out/shrinkage runtime. The development proves the variable-length trace law, measurable rerooting and replay, successful and exhaustion branches, completed-kernel identification, log-under-graph weighting, joint preservation, and final target invariance. `practicalRuntimeSliceSampler_invariant` covers the actual bounded sampler with exhaustion as an identity update. The Reference runtime now emits its ordered comparison trace; Lean lifts pointwise margins to full decision-trace equality, while Julia composes callback, `log(u)`, and addition errors. For the generated quartic target, exact-rational artifacts discharge every callback and the dyadic addition error. The raw uniform is recorded, and a guarded theorem transports its error through a locally bounded logarithm. Exact-real log oracle evidence, a sound platform/RNG bound, and general callback bounds remain explicit executable boundaries. |
| Reversible jump | Complete for scalar, planar, dimension-generic product, three-dimensional executable, and nonlinear cubic triangular-shear clients. A compiler for arbitrary nonlinear diffeomorphisms is optional breadth. |
| Xu et al. 2021 | Complete for the corrected theorem surface and fully instantiated Gaussian and regularized-logistic meeting, marginal/target convergence, unbiasedness, and finite variance. The executable layer now includes seeded replicated Gaussian and finite-data regularized-logistic meeting-time experiments with explicit right censoring and observed/horizon-restricted summaries. The obstructed exponent-two statement is not asserted; more targets and full floating-point reproduction of every paper experiment remain extensions. |
| Concrete GR-HMC convergence | Complete for the bare one-dimensional Gaussian SoftAbs epsilon=1, L=1 chain, including drift, compact minorization, skeleton meeting, residue lift, and setwise convergence. No general ergodicity claim follows. |
| Adaptation | Predetermined schedules, finite freeze, proxy/containment closure, counterexamples, and warmup-only RWMH tests are complete. Finite freeze canonically constructs a `ProxyConvergenceCertificate` with zero approximation error and geometric containment. A continuous warmup selector reads the complete real-valued trajectory's empirical second moment and then freezes, with a conditional setwise theorem. The genuinely complete-history vanishing-error route is now instantiated too: a jointly measurable real-valued client selects the full-history empirical mean, retains that anchor with nonzero weight `1/(n+2)`, otherwise refreshes independently from an arbitrary probability target, never freezes, and has machine-checked setwise convergence of its actual marginals. Julia supplies seeded Gaussian regression and two-initial-state experiments. Separately, the never-freezing state-selected Bool client has a common one-half Doeblin component and checked setwise convergence. More sampler-realistic continuous adaptation without an exact target-refresh branch remains open. |
| PDMP foundations | General infrastructure and the stationary-suspension theorem are present. Exact Gaussian Zig-Zag nonexplosion/stationarity and unit-speed one-dimensional Gaussian BPS stationarity are complete. For general unbounded rates, Lean has proof-bearing partial inverse-integrated-hazard clocks tied to the integrated canonical BPS rate. The multidimensional standard-Gaussian BPS client proves exact inversion, finite-horizon nonexplosion (`CompletesFiniteHorizons`), measurable totalized endpoint selection, and a Markov horizon kernel. Its clock cocycle, exponential memorylessness, boundary-null completion strata, countwise fresh-residual independence, countable gluing, and final pathwise splice yield an exact strong-Markov time-split law and a global bounce-horizon semigroup theorem. The endpoint is exposed jointly measurably in state and time. A generic executor interleaves such a family with refreshes at exact Poisson/ordered-uniform times; its integrated horizon kernel is Markov and preserves every common target. Gaussian BPS instantiates this with standard Gaussian velocity refresh, yielding a genuine Poisson-refreshed horizon kernel with conditional target invariance. The checked generator domain and target-started weak-forward uniqueness interface are instantiated. Lean proves that bounce-only dynamics preserve angular momentum. Proving scalar uniqueness—and hence unconditional multidimensional stationarity—plus the refreshed semigroup law and refreshed ergodicity/convergence remain open. |
| Diagnostics | All registered Julia suites are active and passing. Standalone seeded harnesses cover the paper clients and now include a Gaussian RWMH/reference-HMC/optimized-HMC algorithmic-performance CSV with ESS and callback-work counts. Statistical, finite-difference, and performance tests are diagnostics, not replacements for formal or refinement theorems. |

## Release evidence

The complete release gate is:

    make test
    make check-docs-generated
    julia --project=docs docs/make.jl

The first command builds the full Lean library and oracle, checks generated IR
byte-for-byte, and runs every Julia testset.

## Current release state

The core integration audit is complete: public claims were reconciled with the
compiled APIs, Julia integration defects found by the audit were fixed,
generated artifacts are reproducible, and the release gates pass. The
following theorem-heavy endpoints are parked:

- completed-tree C.4 dynamic HMC is now productive in Julia; production
  closure has reduced bit-index reconstruction to one explicit encoding proved
  in Lean, emitted by the versioned IR, and exhaustively tested by Julia with a
  fail-closed descriptor check; compiled-source refinement, callback/platform
  bounds, and the exact relation to ordinary recursive NUTS stopping semantics
  remain;
- platform-level slice and transform refinement needs sound libm and RNG
  evidence, beyond the existing guarded exact-real contracts;
- never-freezing continuous adaptation now has a jointly measurable,
  complete-history, nonzero-error target-refresh client; replacing its exact
  refresh oracle by a realistic MCMC transition is a stronger later target;
- general growing-horizon SMC/particle-MCMC needs model stability assumptions,
  beyond the reusable strict-contraction interface and partial-refresh client;
- multidimensional BPS still needs scalar weak-forward uniqueness and then a
  separate refreshed-ergodicity argument.

These are not represented as completed merely because their interfaces,
fail-closed runtimes, or concrete lower-dimensional clients are complete.

The parked list is a future research menu and carries no implied completion
order. A subsequent code change must rerun the relevant release gates; it does
not reopen these research items as core blockers.
