# Testing strategy

The Julia suite separates formal conformance, exact finite properties,
empirical distribution diagnostics, active numerical-sampler tests, and
active robustness and performance regressions. No registered testset is
skipped or marked broken.

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
  model, and the exact zero-horizon `N⁻¹ I + (1-N⁻¹) Π` specialization. A
  fixed-seed positive-horizon experiment additionally measures one-step TV
  error at `N = 1,2,4,8` against the known uniform four-path target; it checks
  the exact identity error at `N=1` and decreasing observed errors on that
  declared run. These frequency checks are runtime regressions, not
  substitutes for Lean's particle-count theorem or universal monotonicity
  claims.
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

Restricted-target tests decode the Lean-generated Gaussian expression, check
its value and symbolic derivative, and reject non-finite exponential results.
They now also construct exact dyadic Float64 certificates for `x²/2`: tests
compare the stored ideal values and observed errors as `Rational{BigInt}`, so
this polynomial check uses neither approximate BigFloat references nor libm.
When the Lean oracle binary is available, the suite serializes that exact
record to Lean, checks that it is accepted, and checks that a mutated
derivative error is rejected. Lean's checker theorem turns acceptance into the
corresponding approximation facts.
They also decode the generated sinusoidal potential and compare its value and
symbolic force against `x²/2-sin(x)` and `x-cos(x)` at representative inputs.
These are execution regressions; Lean's recursive backend theorem carries the
explicit local `sin`/`cos` error premises needed for numerical refinement.

The continuous slice suite compares Reference and Optimized bounded rejection
updates on identical uniform traces, including a forced rejection/retry path.
It checks deterministic seeded replay, interval containment, and the known
mean and variance of a bounded uniform target. These tests exercise the
practical implementation; they do not identify Float64 callback evaluation or
the finite retry guard with the disintegrated ideal slice kernel.
The stepping-out suite additionally replays expansion and shrinkage traces,
checks seeded Gaussian moments, and forces finite shrinkage exhaustion. On
exhaustion the algorithmic attempt budget returns the current state; malformed
or genuinely depleted replay sources still fail rather than inventing random
values. Lean separately proves that such an identity fallback preserves the
target once the successful trace map preserves the restricted joint law. On
exhaustion both implementations return the current state after consuming the
same trace. These tests do not replace
the remaining proof that the concrete joint state--trace reversal preserves
the ideal under-graph product law.

Dynamic-tree tests exercise the runtime form of Lean's completed-tree checker:
they accept components with different candidate counts and reject missing-root
and asymmetric-reroot outputs. They also cover no barriers, all barriers, and
mixed canonical orbit partitions. This validates certificate and partition
transport logic, not the geometry of a future floating-point U-turn detector.
They now also exercise root-dependent power-of-two expansion with recursive
subtree U-turn exclusion. The suite checks a certified zero-depth tree,
boundary- and turn-induced global certificate failures, and verifies that a
failed recursive family takes the no-draw identity fallback. This tests the
safe executable boundary; it is not evidence that standard randomized NUTS
always produces reroot-invariant rows.

The Gaussian Zig-Zag suite checks the Lean-proved closed-form integrated-
hazard inversion at representative phase states, deterministic seeded event
simulation, velocity validity, and stationary Gaussian moments. The exact
clock algebra, nonexplosion, regenerative suspension, and target stationarity
of the actual stopped horizon kernel are formalized over `ℝ`; the moment test
remains a runtime diagnostic for the Float64 scheduler. The same exact
stationarity theorem transfers to the unit-speed one-dimensional Gaussian BPS
client, without asserting a floating-point refinement or convergence rate.

The practical stepping-out/shrinkage slice suite also checks stable and
unstable bounded-comparison certificates. Lean proves that a stable
certificate forces every endpoint-stop and proposal-accept decision in the
finite trace to agree with ideal-real execution. The supplied ideal values and
platform error bounds remain certificate inputs, and this test is not evidence
for the separate restricted joint trace-preservation theorem.

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

Constrained-transform diagnostics cover both positive-log exponential-target
sampling and the IR-16 open-unit artanh-affine convention. The latter checks
strict `(0,1)` containment, seeded reproducibility, uniform mean and variance,
descriptor fields, and endpoint rejection. These tests exercise the Jacobian
implementation but do not identify platform transcendental functions with
Lean's exact reals.

## Active and deferred diagnostics

`test/continuous.jl` actively checks:

- a seeded Geweke forward/backward diagnostic for a hierarchical Gaussian
  model, using exact forward simulation and public scalar HMC in the backward
  conditional update; it compares both marginals, joint moments, and exact
  seeded replay;
- zero-momentum leapfrog behavior;
- a 16-dimensional vector-HMC execution for shape and finite outputs;
- ill-conditioned metric-HMC moment recovery;
- multimodal three-state MH frequencies;
- categorical discontinuous HMC: deterministic Reference/Optimized traces for
  uphill crossing, reflection, and zero-energy downhill crossing, plus a
  seeded stationary-frequency diagnostic for repeated Laplace-momentum
  coordinate updates;
- deterministic scalar kinetic-energy trace agreement between Reference and
  Optimized; and
- seeded scalar-HMC and Gaussian-RWMH effective-sample-size regressions, plus
  exact callback-count checks for the interpreted Reference and independent
  Optimized scalar-HMC implementations.

No registered diagnostic testset is currently skipped.

Warmup-only Gaussian-RWMH adaptation is active. Tests verify deterministic
replay, scale bounds, the `1/√n` update envelope, exact freezing into the
ordinary `GaussianRWMH` API, validation failures, and normal-target moments.
The warmup trajectory itself is not treated as stationary output.

The categorical DHMC frequency check is an implementation regression, not a
replacement for the paper's almost-everywhere volume-preservation and
random-order reversibility arguments. Lean currently proves the exact
crossing/reflection energy identity and identifies a single positive symmetric
finite update with a stationary MH kernel. Full repeated-trajectory
phase-kernel invariance remains a separate obligation.

Run the complete cross-language suite with:

```sh
make test
```
