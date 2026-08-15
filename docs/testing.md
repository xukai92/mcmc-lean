# Testing strategy

The Julia suite separates formal conformance, exact finite properties,
empirical distribution diagnostics, active numerical-sampler tests, and
explicitly deferred robustness or performance tests.

## Implemented finite tests

- `test/runtests.jl` exhaustively replays all categorical and two-state MH
  choices through the interpreted reference and optimized Julia implementations and
  compares them with the compiled Lean oracle.
- `test/properties.jl` enumerates primitive draws to recover exact rational
  categorical and transition probabilities. It checks row normalization,
  detailed balance, stationarity, and reference-versus-optimized equality.
- `test/geweke.jl` performs a seeded categorical chi-squared diagnostic,
  per-category frequency checks, and two-state stationary mean and variance
  checks using batch-means standard errors.
- `test/unit.jl` checks RNG and trace-source contracts, bounds, exhaustion,
  invalid weights, and public argument validation.
- `test/generic_mh.jl` exhaustively enumerates an asymmetric three-state
  proposal with zero edges. It compares exact rational MH rows, the Lean
  oracle, interpreted Julia reference, and optimized Julia, then checks normalization and
  stationarity.
- `test/particle_gibbs.jl` exercises exact-integer bootstrap particle Gibbs
  for a finite hidden Markov model. It checks fixed-trace
  Reference/Optimized agreement, the formally proved one-particle identity,
  public validation, empirical path frequencies on a symmetric two-state
  model, and the exact zero-horizon `N⁻¹ I + (1-N⁻¹) Π` specialization. The
  frequency checks are runtime regressions, not substitutes for the Lean
  convergence theorem.
- `test/integer_slice.jl` exhaustively replays the exact finite integer-slice
  transition through independent Reference and Optimized implementations. It
  checks draw bounds and consumption, public validation, implementation
  agreement, and empirical recovery of a two-state target with weights
  `[1, 2]`. Lean separately proves stationarity of the collapsed transition
  for arbitrary positive finite integer weights.

The optimized categorical implementation uses cumulative sums and binary
search, whereas the reference IR interpreter uses a linear cumulative scan.
Both consume the same explicit `draw_below!` interface. The public sampler
currently calls the reference interpreter; the optimized module remains an
internal differential-testing target.

The exact tests and Lean proofs establish stronger facts than finite-sample
statistical tests. The empirical diagnostics remain valuable for detecting
RNG integration, indexing, batching, and public-API defects.

## Implemented continuous tests

The suite covers scalar and vector endpoint HMC, diagonal and dense
constant-metric HMC, and randomized-origin multinomial HMC. Active tests
include energy conservation, replay reversibility, finite-difference volume,
Reference/Optimized fixed-trace comparison, standard-normal and quartic-target
moments, correlated and ill-conditioned Gaussian metrics, multinomial event
ordering, and public sampling APIs. RWMH and HMC also have per-run bounded
decision-certificate unit tests.

Position-dependent generalized leapfrog now has Reference-versus-Optimized
fixed-point tests using nonseparable derivatives, direct checks of both
implicit residuals, public-API validation, and a check that approximate
residual data is not accepted as an exact solver certificate. The smooth
momentum-even formal test Hamiltonian `a q √(1+p²)` is replayed in Julia with
reversal and finite-difference unit-Jacobian checks; the latter remains an
empirical regression rather than a measure-preservation proof. Lean separately
proves that an exact differentiability/unit-Jacobian certificate would imply
phase-volume preservation, but the finite-difference check does not construct
that certificate. For the bounded nonconstant metric `2 + sin(q)`, Lean now
constructs the exact certificate and proves phase-volume preservation; the
Julia residual/reversal tests remain implementation regressions for finite
floating-point iterations rather than that exact proof.

The bilinear exact solver has a stronger formal check:
`bilinearContractiveSolverAt_volumePreserving` proves exact phase-volume
preservation in arbitrary finite dimension. No numerical tolerance enters
that result.

The same position-dependent suite now evaluates the complete bounded-metric
GR callbacks for `scale(q) = 2 + sin(q)`. Reference and Optimized iterations
agree, both residuals fall below tolerance, and opposite-step replay checks
momentum-flip reversal. Lean separately proves the global contraction and
exact reversal statements.

`test/composable.jl` checks declared-variable coverage, overlapping scopes,
left-to-right PG/HMC-style execution order, repeated sampling, and invalid
scope configurations for the executable composable-inference API. It also
decodes the Lean-generated Ge PG--HMC descriptor and checks its names, scopes,
ordering, missing-callback failures, and runtime execution.

`test/xu21_coupling.jl` exercises the public coupled HMC/RWMH mixture, checks
output shape and finiteness, validates dimension failures, and verifies
faithfulness under repeated replay after the chains are exactly equal. These
are implementation regressions; the ideal marginal identities come from Lean.

These numerical checks complement the Lean phase-volume, PMF, kernel-row, and
invariance theorems; they do not replace them.

## Active and deferred diagnostics

`test/future_continuous.jl` now actively checks:

- a seeded Geweke forward/backward diagnostic for a hierarchical Gaussian
  model, using exact forward simulation and public scalar HMC in the backward
  conditional update; it compares both marginals, joint moments, and exact
  seeded replay;
- zero-momentum leapfrog behavior;
- a 16-dimensional vector-HMC execution for shape and finite outputs;
- ill-conditioned metric-HMC moment recovery;
- multimodal three-state MH frequencies;
- deterministic scalar kinetic-energy trace agreement between Reference and
  Optimized; and
- seeded scalar-HMC and Gaussian-RWMH effective-sample-size regressions, plus
  exact callback-count checks for the interpreted Reference and independent
  Optimized scalar-HMC implementations.

It retains skipped testsets only for:

- DHMC categorical targets.

Warmup-only Gaussian-RWMH adaptation is active. Tests verify deterministic
replay, scale bounds, the `1/√n` update envelope, exact freezing into the
ordinary `GaussianRWMH` API, validation failures, and normal-target moments.
The warmup trajectory itself is not treated as stationary output.

These become active only when the corresponding executable APIs and contracts exist. In
particular, a finite-difference Jacobian check will be classified as an
empirical regression test, not as a replacement for a Lean
measure-preservation theorem.

Run the complete cross-language suite with:

```sh
make test
```
