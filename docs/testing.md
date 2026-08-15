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

`test/xu21_coupling.jl` exercises the public coupled HMC/RWMH mixture, checks
output shape and finiteness, validates dimension failures, and verifies
faithfulness under repeated replay after the chains are exactly equal. These
are implementation regressions; the ideal marginal identities come from Lean.

These numerical checks complement the Lean phase-volume, PMF, kernel-row, and
invariance theorems; they do not replace them.

## Skeletoned future tests

`test/future_continuous.jl` registers skipped testsets for:

- a full Geweke forward/backward joint-distribution test;
- DHMC categorical targets and kinetic/momentum units;
- nonsmooth boundaries, high dimension, ill-conditioning, and multimodality;
- adaptation; and
- ESS and gradient-count benchmarks.

These become active only when the corresponding executable APIs and contracts exist. In
particular, a finite-difference Jacobian check will be classified as an
empirical regression test, not as a replacement for a Lean
measure-preservation theorem.

Run the complete cross-language suite with:

```sh
make test
```
