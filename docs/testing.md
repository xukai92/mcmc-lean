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
All three generated Gaussian, sinusoidal, and quartic targets are exercised
through the public restricted RWMH, scalar-HMC, and practical-slice adapters
with seeded replay, finite-output, and movement checks.

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
transport logic. Vector U-turn tests now include a four-leaf orbit with a
positive `0.1` coordinate-error budget: every ordered distinct pair certifies,
while zero-displacement self-pairs correctly remain ambiguous and are handled
structurally by the Lean theorem. A linked two-endpoint leapfrog certificate is
also lifted automatically to the complete off-diagonal U-turn matrix, checking
the adapter from primitive recurrence bounds to recursive callback margins.
These supplied bounds are not evidence for a particular platform's rounding.
Separately, the exact-dyadic Gaussian regression runs eight maintained
optimized Float64 leapfrog steps at step size `1/2`, serializes every value as
its exact rational, and asks the compiled Lean oracle to check every half kick,
drift, and final kick. A modified endpoint is rejected, and a `0.1` step is
rejected by the exact checker when rounding prevents rational equality. The
rounded checker accepts that same execution only after recording its exact
nonzero final-kick residual; falsifying that residual to zero is rejected by
Lean. These are real per-execution platform records, not an a priori uniform
IEEE error theorem.
Three such `0.1` steps are now linked into the actual four-leaf Float64 orbit.
The oracle checks its eight exact binary-rational phase coordinates against the
Lean client and rejects a changed endpoint. Every ordered distinct endpoint
pair clears the proved `10⁻¹⁴` position/momentum budget; self-pairs remain the
structurally handled zero-displacement case. Thus rounded arithmetic reaches
the full checked recursive-kernel theorem for this concrete orbit rather than
stopping at isolated primitive steps.
The same suite executes a generated-quartic optimized leapfrog step, checks its
current and next gradient evaluations with the quartic oracle, checks all three
arithmetic residuals with the target-independent rounded-leapfrog oracle, and
verifies exact field linkage in Julia. Lean's composite certificate packages
the corresponding mathematical obligation.
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

The randomized recursive dynamic-HMC suite replays momentum, origin, Boolean
doubling directions, and selection events. It checks Reference/Optimized
agreement, deterministic seeded sampling, and the proved failure policy: a
direction trace whose complete rooted row family fails reroot certification
returns the current state without consuming a selector draw. This exercises
the stationary checked-mixture boundary; it does not assert equivalence to an
unchecked production NUTS recursion.

Position-dependent generalized leapfrog now has Reference-versus-Optimized
fixed-point tests using nonseparable derivatives, direct checks of both
implicit residuals, public-API validation, and a check that approximate
residual data is not accepted as an exact solver certificate. The smooth
reference solver also returns an audit trace containing both final iterates,
their callback values, one-more-update values, iteration counts, and every
ordered callback invocation. Tests recompute both
reported residual norms from that trace, submit one scalar rounded-update and
contraction pair to the Lean oracle, and verify that a mutated rational
residual fails closed. Both implicit loops also submit their exact observed
affine-arithmetic residuals; mutated totals fail closed. The callback-error
premise remains explicit.
The smooth
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
exact reversal statements. At the maintained initial position `q=0.25`, the
suite also submits the actual Float64 sine and cosine values to the rational
Taylor-enclosure oracle and verifies that a zeroed sine radius fails closed.
It additionally certifies all 29 callback invocations in the maintained solve.
The Lean checker validates the phase order and count
`halfIterations + positionIterations + 4`; tests independently mutate the
declared count, first callback kind, and an arithmetic radius and require all
three records to fail closed.
Every loop candidate and final recomputation is also retained as an affine
update. The suite submits all 28 linked records to the oracle: one-source
momentum updates and two-source position updates must use exactly the computed
callback centers, their Float64 summation residual, and error sums proved by
their callback certificates. At least one maintained velocity sum is asserted
to have a genuinely nonzero rounding residual. A
mutated linked callback radius is rejected.
The suite finally selects the last half-momentum and position residual updates,
constructs their rational a posteriori contraction bounds, and submits both
fully linked records to the oracle. Their rates are checked against the actual
Float64 step size, and rate mutation is required to fail closed. Lean's
soundness theorems turn each accepted record into a distance bound from the
returned runtime iterate to the unique exact implicit fixed point.
The maintained solve additionally forms a two-endpoint multinomial orbit from
its exact represented input and transported exact output. Tests check the
common Hamiltonian radius, both maximum-stabilized exponential records, the
actual rounded cumulative sums, the scaled draw, and strict separation from
both selection boundaries. Oracle regressions mutate the initial momentum,
common radius, and stabilized argument link and require fail-closed rejection.
Two solver calls are also executed sequentially and submitted as one linked
trajectory record. Its checker requires a common step size and exact equality
of the first rounded endpoint with the second represented input. A changed
initial position and a truncated second record are rejected. This test covers
state threading; the explicit regional Lipschitz budget needed to transport
the two local radii to one exact two-step orbit remains a formalized premise.
The two records are then checked jointly. The combined certificate verifies
that both phases share the initial position and that the position callbacks
consume the returned half momentum; its position budget includes the proved
nine-Lipschitz half-momentum sensitivity term. Mutating that combined radius
is required to fail closed. The suite then certifies the final momentum affine
update, complete phase radius, and bounded-Hamiltonian evaluation at the
returned endpoint. Both endpoint and energy-radius mutations must fail closed.

`test/composable.jl` checks declared-variable coverage, overlapping scopes,
left-to-right PG/HMC-style execution order, repeated sampling, and invalid
scope configurations for the executable composable-inference API. It also
decodes the Lean-generated Ge PG--HMC descriptor and checks its names, scopes,
ordering, missing-callback failures, and runtime execution.

`test/xu21_coupling.jl` exercises the public coupled HMC/RWMH mixture, checks
output shape and finiteness, validates dimension failures, and verifies
faithfulness under repeated replay after the chains are exactly equal. These
are implementation regressions; the ideal marginal identities come from Lean.
It also checks the seeded replicated `coupled_meeting_diagnostic`, including
reproducibility, explicit right censoring, and the zero-time already-met edge
case. A command-line Gaussian experiment is available as:

```sh
julia --project=VerifiedSamplers.jl \
  VerifiedSamplers.jl/experiments/xu21_gaussian_meeting.jl 2021 100 2000
```

Equivalently, `make experiment-xu21` uses those defaults; `XU21_SEED`,
`XU21_REPLICATES`, and `XU21_HORIZON` override them.
`make experiment-xu21-logistic` runs the same diagnostic for a documented
two-dimensional finite-data, `L²`-regularized logistic target, matching the
second target family whose ideal meeting theorem is instantiated in Lean.
Its observed and horizon-restricted meeting-time means are empirical summaries
only; they do not replace the machine-checked geometric meeting-tail theorem.

`make experiment-particle-gibbs-count` runs the fixed-horizon one-step
particle-count diagnostic independently of the test suite. Its defaults use
counts `1,2,4,8`, 8,000 replicates, and a fixed seed; `PG_COUNTS`,
`PG_REPETITIONS`, and `PG_SEED` override them. The output reports empirical TV
distance from the uniform four-path target. This illustrates the proved
fixed-iteration particle-count regime but is not a proof of monotonicity or a
joint growing-horizon/count limit.

`make experiment-dynamic-hmc` runs the conservative spanning, checked
first-stop, and checked recursive-doubling dynamic-HMC interfaces on the same
standard-Gaussian family. It reports maximum absolute coordinate-mean and
variance errors after burn-in, together with the fraction of iterations that
change position. Seed, draw count, burn-in, and dimension are configurable
through the corresponding `DYNAMIC_HMC_*` Make variables. The movement rate
is essential to interpreting fail-closed checked policies: in particular, the
current recursive descriptor can reject every Gaussian trace and therefore
return the identity kernel. This is a reproducible certification diagnostic,
not evidence that every checked interface is an effective sampler; it neither
identifies them with standard NUTS nor proves convergence or relative
efficiency.

`make experiment-restricted-quartic` runs RWMH, scalar HMC, and practical
slice sampling against the same generated `x⁴/4+x²/2` artifact through the
three `restricted_potential_*` adapters. Its CSV output reports each explicit
configuration, movement, mean, and second and fourth empirical moments after
burn-in. `QUARTIC_SEED`, `QUARTIC_DRAWS`, `QUARTIC_BURNIN`, and
`QUARTIC_SCALE` control the run (the scale applies to RWMH; HMC and slice
settings are printed in their rows). These are reproducible implementation
diagnostics: the Lean artifact theorem identifies the exact target formula,
but finite-run moments neither prove convergence nor discharge the Float64/RNG
refinement boundary.

`make experiment-reversible-jump` runs the nonlinear cubic-shear and
three-dimensional product birth/death clients with fixed seeds. It reports
empty-model occupancy and the largest canonical-coordinate mean and variance
errors after undoing the shear where applicable. `RJ_SEED` and `RJ_DRAWS`
control the run. The exact one-half occupancy here also follows operationally
from deterministic alternation; the empirical coordinate summaries are
runtime diagnostics and do not replace Lean's transport-density and invariance
theorems.

`make experiment-warmup-rwmh` runs bounded Robbins--Monro scale adaptation on
a standard normal target and then samples only from the returned frozen
`GaussianRWMH`. It reports the frozen scale, warmup acceptance frequency, and
retained mean and variance. `WARMUP_SEED`, `WARMUP_DRAWS`, and
`WARMUP_RETAINED` control the run. Warmup states are deliberately excluded
from the retained summaries; this experiment does not claim the adaptive
trajectory itself is stationary.

`make experiment-constrained-transforms` runs the positive-log exponential
target and open-unit artanh-affine uniform target under explicit seeds. It
reports support violations and retained mean/variance errors. The corresponding
exact measurable-equivalence and Jacobian results are in Lean; platform
`exp`, `log`, `tanh`, `artanh`, arithmetic, and RNG accuracy remain the
guarded executable boundary.

`make experiment-ge-pg-hmc` decodes the Lean-generated `ge-pg-hmc` operator
schedule and binds it to a concrete binary-latent Gaussian mixture: an exact
Gibbs latent update followed by scalar HMC for the conditional continuous
coordinate. It reports latent frequency and continuous mean/variance against
the known values `1/2`, `0`, and `2`. This checks generated ordering, callback
binding, and execution; the existing Lean common-target composition theorem,
not the finite-run moments, establishes ideal invariance once the component
kernel premises are supplied.
The same seeded Gaussian-mixture client is registered in the Julia suite: it
checks exact replay and tolerances around latent probability `1/2`, continuous
mean `0`, and continuous variance `2` after burn-in.

`make experiment-gaussian-softabs` runs the maintained diagonal SoftAbs
GR-HMC Gaussian specialization with configurable seed, draw count, burn-in,
and dimension, using step size `0.2` and ten integration steps. It reports
movement and the largest coordinate mean and
variance errors. Lean proves exact endpoint/multinomial invariance for this
constant-Hessian client and separately proves setwise convergence for its
one-dimensional bare specialization; the experiment does not extend either
claim to unrestricted Float64 execution or arbitrary dimensions.
The same two-dimensional tuning is an active seeded regression with retained
coordinate mean and variance tolerances.
The guarded metric tests additionally send the exact unit-smoothing,
zero-Hessian SoftAbs record to Lean and reject a mutated logarithm. For a
nontrivial primitive call, Julia converts the input `0.5`, its Float64 square
root, and a conservative error radius to exact rationals. The Lean oracle
checks the squared interval and rejects the same record with its radius changed
to zero. It then certifies the actual reciprocal of that computed square root
from its exact rational residual and rejects a falsely zero residual. Thus
the combined command certifies the linked inverse-square-root computation and
rejects the same false residual. These tests certify the observed primitive
calls rather than merely comparing them approximately with another
floating-point oracle. A nontrivial SoftAbs eigenvalue additionally exercises
  the 32-term rational-series logarithm enclosure: Lean accepts the actual
  `log` output and rejects a falsely zero radius; the exact `log(1)=0` boundary
  is also covered.
Finally, the same nonzero entry is submitted as one linked positive-SoftAbs
record. The oracle checks the `tanh(1)` enclosure, rounded division, square
root, reciprocal, logarithm, and every shared intermediate; changing the tanh
radius to zero rejects the complete record.
The same complete path is exercised at Hessian `0.1`, demonstrating that the
`tanh x ≤ x` upper bound retains a positive useful interval for small inputs.
The `(α,h)=(0.1,0.1)` regression additionally has a genuinely nonzero Float64
argument-product residual. The oracle accepts that residual through Lean's
one-Lipschitz `tanh` transport and rejects the same record after the residual
is changed to zero.
That metric entry is also consumed by a scalar-Hamiltonian regression at
`(α,h,U,p)=(0.1,0.1,0.5,0.25)`. The compiled oracle checks the observed
transformed-momentum radicand, kinetic square root, and final energy addition;
the radicand and energy residuals are both genuinely nonzero. Replacing the
radicand residual by zero rejects the linked endpoint record.
The endpoint format is also exercised as a three-element SoftAbs trajectory
with distinct Hessians, potentials, and momenta. The oracle checks every
constituent record, rejects a modified first-endpoint radicand residual, and
rejects a truncated payload whose declared count no longer matches its
fields. Lean separately proves how a finite family with a common energy budget
feeds the stabilized multinomial-selection certificate.
The guarded metric suite additionally checks `exp(-0.1)` through the rational
nonpositive enclosure and rejects a zero radius. A linked transport record
targets exact `-1/10`; its Float64 argument residual is nonzero, accepted by
Lean, and rejected after mutation to zero. These checks remove a libm premise
for each accepted stabilized exponential call, while cumulative arithmetic and
RNG evidence remain separate.
The three-endpoint SoftAbs trajectory additionally generates all stabilized
weights from the checked endpoint energies. Its wider potential range forces
nonzero Float64 subtraction residuals. The oracle accepts the full transported
weight list, rejects a zeroed nonzero argument residual, and rejects a
count/payload truncation.
Those weights are accumulated by the actual sequential Float64 loop. Two
maintained prefix errors are nonzero; Lean checks every boundary against the
exact rational prefix and rejects a zeroed error or truncated record. The
final `0.37*total` draw also has a nonzero multiplication residual, accepted
by the oracle and rejected when replaced by zero.

These numerical checks complement the Lean phase-volume, PMF, kernel-row, and
invariance theorems; they do not replace them.

Constrained-transform diagnostics cover both positive-log exponential-target
sampling and the IR-16 open-unit artanh-affine convention. The latter checks
strict `(0,1)` containment, seeded reproducibility, uniform mean and variance,
descriptor fields, and endpoint rejection. These tests exercise the Jacobian
implementation but do not identify platform transcendental functions with
Lean's exact reals.

Practical-slice comparison witnesses are deliberately pointwise. The Julia
certificate checks a common strict margin, while Lean proves agreement for
each `<`, `≤`, or `≥` comparison through `lt_threshold_eq`,
`le_threshold_eq`, and `ge_threshold_eq`. Lean's `decisionTrace_eq` now lifts
these results over an explicitly ordered comparison-kind schedule. Julia's
`SliceDecisionTraceCertificate` records the matching schedule and fails closed
when any margin is ambiguous. `trace_stepping_out_slice` instruments the
maintained Reference path and records its threshold, ordered kinds, callback
values, and result; `certify_stepping_out_slice_trace` attaches supplied ideal
values and bounds. Justifying those callback/threshold bounds and the RNG
draws remains required for an end-to-end Float64 execution certificate.
`SliceThresholdCertificate` further decomposes the threshold witness into the
current-state callback, `log(u)`, and final rounded addition. Lean proves that
their errors add; Julia checks each component and rejects a certificate tied
to a different observed threshold. Tests using zero-error self-witnesses check
this plumbing only, not the truth of platform accuracy assumptions.
For the generated quartic potential, `certify_restricted_quartic_slice_trace`
uses the recorded evaluation positions to check the current-state and every
comparison callback against exact rational polynomial formulas. It also
computes the final addition error exactly from the three observed dyadic
numbers. The full cross-language suite submits the current-state and every
recorded comparison callback to `mcmc_oracle`; each must satisfy Lean's proved
quartic formulas and exact error checker. A deliberately mismatched base is
rejected. The test treats the
observed `log(u)` as its own ideal solely to exercise plumbing; a real backend
certificate must justify that remaining logarithm/RNG relation.
The trace also records the raw uniform. `SliceLogUniformCertificate` checks a
bound from that draw to an ideal draw, a local backend-log bound, and a positive
lower guard, then applies Lean's `localError + inputError/lower` transport
theorem. Its exact-real logarithm inputs still require an analytic or trusted
oracle; the zero-error self-witness regression is not a claim about `libm`.
At the formal layer, `SliceThresholdCertificate.ofLogUniform` connects this
guarded log certificate directly to the sampled-height certificate and exposes
the resulting callback, local-log, RNG-input, and addition error sum.
`SliceComparisonCertificate.ofThreshold` then fixes that sum as the threshold
uncertainty used by every ordered branch margin; Julia mirrors this with a
decision-trace overload taking the complete threshold record.

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

Dynamic-tree tests also exercise the canonical coherent-subrow repair. They
check that it never adds a raw candidate, always returns a certified partition
for root-retaining input, preserves an already certified family exactly, and
rejects malformed rows that omit their root. This repair is a safety utility;
tests do not present its singleton result on one-sided recursive rows as a
productive NUTS transition.
The `CompletedTreeC4DynamicHMC` tests instead exercise the productive
completed-tree route: monotone power-of-two orbits retain every root, fixed
traces agree between Reference and Optimized selectors and move, malformed
non-power-of-two inputs are rejected, and seeded Gaussian chains replay
exactly with finite nontrivial output. `make experiment-dynamic-hmc` reports
this C.4 client alongside the conservative, first-stop, and old per-direction
checked interfaces.

Warmup-only Gaussian-RWMH adaptation is active. Tests verify deterministic
replay, scale bounds, the `1/√n` update envelope, exact freezing into the
ordinary `GaussianRWMH` API, validation failures, and normal-target moments.
The warmup trajectory itself is not treated as stationary output.
`make experiment-indefinite-adaptation` separately runs the proved
never-freezing Boolean client from both initial states and reports seeded tail
frequencies. It illustrates the concrete setwise-convergence theorem; the
frequencies are diagnostics rather than proof evidence.
`make experiment-indefinite-continuous-adaptation` runs the proved real-valued
history-anchor/target-refresh client from initial states `-4` and `4`, using a
Gaussian refresh callback and reporting tail means and variances. Lean's
theorem accepts any probability target; callback equality and Float64
arithmetic remain runtime conformance boundaries.

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

Run every standalone reproducible empirical harness with:

```sh
make experiments
```

This explicit target includes Xu meeting diagnostics, particle-count,
dynamic-HMC, generated-quartic, reversible-jump, warmup adaptation,
indefinite Boolean and continuous adaptation, constrained-transform,
generated PG--HMC, Gaussian SoftAbs, and Gaussian algorithmic-performance
experiments.
It is not a dependency of `make test`: longer empirical reproduction remains
an intentional user action rather than an implicit build side effect.

`make experiment-gaussian-performance` reports seeded RWMH plus public
reference-path and maintained optimized HMC movement, autocorrelation ESS,
gradient calls, log-density calls, and HMC ESS per gradient evaluation as CSV.
These are reproducible algorithmic-work metrics; the harness deliberately
omits wall-clock thresholds, which would be unstable across machines. The
command also requires the reference and optimized HMC chains to agree exactly
under identical seeded draws. The registered Julia suite separately enforces
minimum ESS, differential replay, and exact callback-count regressions.

Sampling-quality formulas shared with the HMC benchmark live in
`VerifiedSamplers.jl/test/support/QualityDiagnostics.jl`. Integrated tests use
the same initial-positive-sequence ESS, known-moment, covariance, marginal
quantile, and batch-means standard-error definitions as benchmark clients.
Small calibrated regressions belong in the test suite; multi-chain and
exploratory summaries remain non-gating benchmark evidence. None of these
diagnostics is promoted to a stationarity or convergence proof.

Quality work follows a stability-first order:

1. share definitions and deterministic unit tests (current phase);
2. add small known-covariance and known-quantile sampler regressions with
   batch-means uncertainty used to calibrate tolerances;
3. add multiple-chain split rank-normalized R-hat and bulk/tail ESS to the
   benchmark report, including ESS per gradient evaluation; and
4. add covariance and ECDF/quantile visualizations with explicit Monte Carlo
   uncertainty and conspicuous non-gating warnings.

Only metrics demonstrated stable across supported Julia versions and CI
machines should become integrated pass/fail contracts.
