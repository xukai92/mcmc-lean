# Continuous executable contract

## Purpose

This note fixes the semantic and runtime boundaries for continuous Gaussian
RWMH. It prevents three different objects from being described as though they
were the same implementation:

1. an exact mathlib probability measure and Markov kernel;
2. an ideal-real sampler program and mathematical trace replay; and
3. a Julia `Float64` program driven by a concrete `AbstractRNG`.

## Exact Lean layer

`Mcmc.Executable.IR` is an intrinsically typed, first-order syntax. Its binders
use typed de Bruijn variables; `letE` and `sample` contain syntax bodies rather
than opaque Lean continuations. Pure expressions currently cover real and
Boolean arithmetic sufficient for the initial accept/reject program, and the
primitive universe contains:

- positive bounded-natural draws;
- an ideal scalar standard normal; and
- an ideal unit uniform.

Every program has two interpretations:

- `Program.kernel`, a mathlib `ProbabilityTheory.Kernel` from typed
  environments to results; and
- `Program.replay`, deterministic consumption of kind-tagged trace events.

Lean proves every program kernel is Markov. A trace is an operational witness,
not a random measure, and replay failure is not assigned probability mass.
The ideal-real replay interpreter is intentionally `noncomputable`.

The foundational unit-scale specialization, `standardGaussianProposalProgram`,
establishes that for every scalar current state it:

- replays a normal event as `current + noise`;
- denotes `gaussianReal current 1`; and
- equals the proposal row built from
  `randomWalkProposalDensity (gaussianPDF 0 1)` in the existing RWMH theory.

The generic IR step draws both proposal noise and a unit uniform. Its trace
theorem exposes the exact accept-or-retain result for every real log-density
function and scale. For a measurable log density and positive scale, Lean
identifies the scaled-normal proposal law, proves that the real threshold is
pointwise equal (after `ENNReal.ofReal`) to the existing zero-safe
`densityAcceptance`, and identifies the exact program kernel with the existing
verified Gaussian `randomWalkMetropolisHastings` construction. That kernel
preserves the measure with density `exp ∘ logDensity`; if this density
integrates to one, Lean also packages it as a stationary probability measure.

The separately serializable named-variable command IR has a deterministic
fuel-indexed Lean interpreter whose public fuel bound is computed from the
syntax. Its generic trace theorem covers arbitrary log densities and scales;
the standard-Gaussian/unit-scale theorem remains as a concrete regression
specialization. Fuel is an implementation device, not an additional runtime
input or probabilistic assumption.

## Julia layer

The current version-19 artifact contains scalar and vector-valued multi-step endpoint
HMC (introduced in version 5), constant-metric programs (version 6), and the
randomized-origin multinomial-HMC command.
Its explicit callbacks are the target log density and the gradient of the
negative log density, together with positive step size and trajectory length.
Lean proves the command trace formula, its integrator equals the established
Hamiltonian `leapfrogN` map for every finite length, and every associated ideal
endpoint kernel preserves the Boltzmann phase target. The full standard-normal
momentum refresh, phase evolution, and position projection is packaged as a
Markov kernel and proved invariant for every compatible position target. The Julia
Reference/Optimized agreement and integrator property tests remain Float64
implementation evidence subject to the same numerical-refinement boundary.

The vector command uses a runtime dimension, a real-vector position, one
standard-normal event per coordinate, vector log-density/gradient callbacks,
and a unit uniform. Its Julia Reference interpretation is driven entirely by
the serialized program. Optimized is independent. Lean's endpoint-HMC
invariance theorem is dimension-polymorphic, and
`vectorLeapfrogN_positionList` proves that the list-valued executable
integrator is the coordinate serialization of the `Fin n → ℝ`
Hamiltonian integrator.

The vector replay theorem now covers the complete normal-event prefix,
uniform event, endpoint energies, decision, result, and remaining trace. The
bounded HMC layer gives coordinatewise trajectory certificates and a stable
acceptance theorem outside the explicit uniform/threshold error band.
Constant diagonal and dense metrics have exact Lean velocity maps,
time-reversal and endpoint-invariance theorems. Their type-indexed commands are
part of generated IR version 16 and are interpreted by Julia Reference. Lean
proves that applying an invertible factor to standard momentum gives the
pushforward Gaussian law, identifies its determinant-normalized quadratic
kinetic density, and instantiates refreshed position-target invariance.

The same artifact contains the continuous RWMH command program. Julia
Reference interprets its expressions, callback calls, draws, branch, and
return; public `GaussianRWMH` uses this path. Optimized remains an independent
differential-test implementation. Both use:

```text
standard_normal!(RNGSource(rng)) = randn(rng)
uniform_unit!(RNGSource(rng))    = rand(rng)
```

and evaluates target log densities, proposals, ratios, and comparisons in
`Float64`. `FloatTraceSource` has distinct `NormalEvent` and `UniformEvent`
constructors and rejects kind mismatches and unit-uniform values outside
`[0,1)`. These events contain floating-point values; they are not encodings of
arbitrary Lean real numbers.

Reference and Optimized are compared on deterministic accept and reject traces
across multiple callbacks and positive scales, and the public path has a
normal-target moment test. These tests can expose implementation defects but do
not prove equality of probability laws.

## Restricted target expressions

`Mcmc.Executable.Continuous.RestrictedExpr` is the first callback-free scalar
target surface. Lean interprets the syntax over ideal reals and proves its
symbolic derivative correct for every admitted expression. The corresponding
Julia algebraic data types are evaluated structurally; arbitrary Julia
functions are therefore not mistaken for expressions covered by that theorem.

`RestrictedTargetCertificate` records input, value, and derivative errors
against the Lean semantics. The centered Gaussian expression `x²/2` has a
derived certificate whose value-error formula follows from the input bound and
whose derivative error is exactly the input error. This does not identify
Float64 arithmetic with real arithmetic: operation-level rounding and libm
evidence must supply the certificate, and non-finite Julia intermediates are
rejected. Generated IR version 11 carries a canonical rational-literal target
tree. Lean proves the generated Gaussian tree compiles to `x²/2`; Julia decodes
that declaration to construct the public `restricted_gaussian_potential`, so
this example no longer relies on a second handwritten Julia tree.

IR version 12 additionally carries checked composable-inference schedule
metadata. The canonical Ge PG--HMC descriptor is coverage-checked in Lean and
decoded by Julia with its operator names, scopes, and order intact. Runtime
callbacks are supplied by name; their semantic refinement to the formal PG and
HMC kernels remains separate evidence.

`RestrictedBackend` specifies numeric implementations of every portable
primitive together with local absolute-error evidence. Lean recursively
accumulates these errors through both the generated target and its generated
symbolic derivative, producing a `RestrictedTargetCertificate`. The
exponential field deliberately includes its admitted-domain transport bound;
there is no false global Lipschitz claim for `exp` and no implicit assertion
about a platform's libm.

## Multinomial HMC

The generated multinomial command consumes one standard-normal event per
coordinate, an exact bounded integer origin event, and a unit-uniform event
for cumulative Boltzmann-weight selection. Lean proves that the corresponding
ideal finite choice law maps exactly to `randomizedMultinomialLeapfrogPMF` and
to the row of the verified invariant kernel. The complete ideal command uses
standard-Gaussian momentum refresh and preserves the position Boltzmann
target.

Julia evaluates stabilized Float64 log weights and cumulative sums. Reference
and Optimized use independently organized trajectory construction and are
differentially tested, but equality with the ideal categorical law remains
conditional on bounds for trajectory energies, `exp`, summation, and the
selection-boundary margin.

Lean proves the corresponding all-boundaries stability theorem: if the ideal
draw is farther from every ideal cumulative boundary than the combined draw
and boundary errors, computed and ideal scans return the same index. The Julia
certificate API checks supplied witnesses in parallel with sampler execution.

Version 9 also contains diagonal and dense constant-metric multinomial
commands. Their ideal semantics has exact phase and refreshed-position
invariance, including the Cholesky momentum specialization.

## Position-dependent implicit solver

The public `fixed_point_generalized_leapfrog` function now performs both
implicit generalized-leapfrog loops for user-supplied position and momentum
derivatives. Reference and Optimized implementations are differentially tested
on a genuinely position-dependent kinetic derivative. The returned
`ImplicitSolveCertificate` records the measured half-momentum and position
residuals.

The formal counterparts are `ContractiveGeneralizedLeapfrogSolver` and the
step-restricted `ContractiveGeneralizedLeapfrogSolverAt`. Banach contraction
certificates construct exact fixed points for both equations and prove
uniqueness. The fixed-step interface is essential for nonseparable problems:
the concrete smooth momentum-even Hamiltonian
`H(q,p) = a q √(1+p²)` proves both loops contract under `|εa/2| < 1`, rather
than assuming contraction for every real step size. Lean verifies its stated
derivatives, exact-solve uniqueness, convergence of both practical loops,
measurability, and momentum-flip reversal. A bilinear closed-form stress test
is also retained. Opposite-step uniqueness now proves that the exact step is
bijective, and a reusable change-of-variables theorem turns an explicit
differentiability/unit-Jacobian certificate into product phase-volume
preservation. The generic smooth stress model is not the concrete volume
client; the bounded positive nonconstant metric client below closes the metric,
contraction, differentiability, exact unit-Jacobian, and phase-volume
obligations. Its exact Banach selection therefore supplies the complete formal
integrator validity result; Float64 finite loops remain governed by the
separate residual/refinement boundary.

For comparison, `bilinearContractiveSolverAt_volumePreserving` closes the
measure-theoretic argument for the bilinear implicit stress model in every
finite dimension: the exact selected map is a pair of reciprocal dilations,
whose Haar scaling factors cancel. That theorem validates the solver
machinery but does not identify the bilinear model with the complete
momentum-even GR Hamiltonian.

The bounded scalar GR example uses the same callbacks in Lean and Julia. Its
factor is `2 + sin(q)` and its compensating potential cancels the
log-determinant term. Lean proves the exact implicit maps contract for
`3|ε|/2 < 1`; Julia's Reference and Optimized loops are differential-tested
for residual convergence and reversal. Their measured nonzero residuals are
still approximation evidence, not equality with the Banach-selected point.
The reusable `contractiveGeneralizedLeapfrogSolverAtOfLipschitz` constructor
now derives this exact selection from global slice-Lipschitz constants alone;
the bounded scalar client is proved step-equivalent to that generic route.
This is the intended entry point for target-specific SoftAbs derivative
bounds.

A small positive residual is not reclassified as equality. Consequently the
practical Float64 solver is useful for diagnostics and convergence testing but
the exact `CertifiedRelativisticMultinomialHMC` interface rejects it unless the
residuals are exactly zero and all global validity witnesses are supplied.

The guarded SoftAbs numerical layer now continues beyond metric evaluation.
For the scalar unit-parameter client it transports factor and momentum errors
through the relativistic radicand and square root, then combines potential,
kinetic, and log-determinant errors into a complete Hamiltonian-value bound.
The Julia evaluator follows that exact expression. Two endpoint instances can
therefore feed the existing energy-difference and acceptance-margin theorems;
primitive `Float64`/libm bounds remain explicit backend evidence.
For the polynomial Gaussian callback, the executable exact-rational checker
now covers value, gradient, and Hessian. This part needs no libm premise and
feeds the constant-Hessian diagonal SoftAbs client; it does not certify the
subsequent square root, reciprocal, or logarithm implementation.

The generic `NumericalRefinement` contract is now inhabited by the ideal-real
Lean interpreter itself.  It provides an assumption-free oracle theorem for
Gaussian RWMH trace replay.  This does not collapse the language boundary:
Julia and IEEE values continue to use explicit approximation relations and
margin conditions rather than definitional equality with real arithmetic.

## Xu et al. coupled mixture

Version 9 contains separate commands for coupled multinomial HMC, coupled
Gaussian RWMH, and their mixture. Lean assigns them the existing ideal
shared-momentum/maximal-index HMC coupling and maximal-Gaussian sticky RWMH
coupling. Each command has the verified single-chain transition on both
marginals; the mixture therefore has the verified HMC/RWMH mixture on both
marginals.

Julia interprets the commands with shared random events and exposes exact
equality after each step as `met`. Tests verify faithfulness from an already
equal pair. These facts do not discharge floating-point trajectory, Gaussian
proposal, categorical-boundary, callback, or RNG refinement.

## Required refinement assumptions

`Mcmc.Executable.Continuous.BoundedRWMH` now discharges the generic error
composition. Its `Approximates` relation and `RwmhErrorCertificate` prove:

- an explicit affine-proposal error bound from current, scale, and noise
  errors;
- additive propagation of the two callback errors into the log ratio;
- nonexpansiveness of clamping at zero;
- one-Lipschitz transport through `exp` on the nonpositive half-line;
- exact accept/reject agreement whenever the ideal comparison margin is
  larger than the combined threshold/uniform error; and
- a returned-state error bounded by the selected current/proposal budget.

If the branches disagree, Lean proves that the ideal draw lies inside the
same combined-error band around the threshold. This is the unavoidable
boundary qualification for a discontinuous accept/reject decision.

Backend certificates must account for each of the following separately:

| Boundary | Required statement |
|---|---|
| Ideal standard normal to runtime RNG | The supported RNG and Julia version implement the documented `randn` distribution, or a quantified approximation bound is supplied. |
| Ideal unit uniform to runtime RNG | `rand` has the documented support/distribution and endpoint convention. |
| Real arithmetic to `Float64` | Overflow, underflow, `NaN`, infinities, rounding, and transcendental error are either excluded by preconditions or bounded. |
| Target expression to Julia callback | The callback implements the same log weight on the admitted domain, up to the stated numeric error. |
| Ideal continuous IR to Julia | The maintained interpreter mirrors primitive order and control flow and is differentially tested. Bounded-error composition covers positive-log and open-unit-artanh transforms, while primitive platform libm/RNG certificates and a complete cross-language theorem remain future work. |
| Exact-dyadic Gaussian leapfrog | Julia converts every finite observed input, half-kick, drift, and final-kick value to its exact binary rational. The compiled Lean oracle checks the three Gaussian leapfrog equations exactly. Active tests cover eight maintained optimized steps and reject a tampered endpoint. Only executions with no arithmetic rounding relative to the rational equations certify; general rounded IEEE trajectories remain in the bounded-error layer. |
| Rounded Gaussian leapfrog residuals | For any finite observed Gaussian step, Julia computes each local residual using exact rationals and Lean checks that exact residual through the compiled oracle. The resulting Lean theorems expose real absolute-error bounds for the half kick, drift, and final kick. This is sound ex-post evidence for that execution; converting it into an a priori platform-wide bound or covering non-polynomial callbacks remains separate. |

`BackendRwmhCertificate` and `BackendHmcCertificate` now compose these
operation-level claims into the exact Lean decision-stability certificates.
The matching Julia `Certificates` module checks execution-specific witnesses,
adds callback or endpoint-energy error to the `exp` error, and reports whether
the ideal decision margin exceeds the resulting threshold/RNG uncertainty
band.

`NumericalRefinement` retains the exact backend contract, while
`BoundedRWMH`, `BoundedHMC`, and `BackendCertificates` give the practically
attainable finite-error contract. A per-run Julia witness is conditional on
the supplied ideal values and primitive bounds. No universal theorem about
Julia callbacks, LLVM lowering, platform libm, or RNG distributions is
defined; supplying those assumptions remains explicit and adds no axiom to
the trusted Lean environment.

For generated restricted target expressions, `exactRestrictedPrimitiveBackend`
and `exactRestrictedBackend` instantiate every arithmetic and transcendental
operation with its ideal-real meaning. Lean proves recursively that this
reference evaluation equals the compiled expression and constructs a
zero-error value/symbolic-gradient `exactTargetCertificate` at an exactly
represented input. External finite-precision backends still enter through
the separate operation-local error fields; the exact backend is an oracle and
does not assert anything about IEEE or `libm` behavior.

The generated target table also includes the strongly convex polynomial
`restricted-quartic-potential`, with
`U(x)=x⁴/4+x²/2`. Lean proves that its generated first and second symbolic
derivatives are `x³+x` and `3x²+1`, respectively, and proves the Hessian is
strictly positive everywhere. Julia parses that same emitted tree and checks
value, force, Hessian, and positive SoftAbs metric evaluation. The polynomial
callback itself requires no target-side transcendental primitive; SoftAbs
square root, inverse, and logarithm retain their separate platform boundary.
For each finite Float64 quartic evaluation, Julia can serialize the input,
value, force, Hessian, and their observed errors as exact dyadic rationals.
The compiled Lean oracle independently checks these against the three proved
quartic formulas, and accepted records yield `Approximates` theorems after
embedding into the reals. This artifact-level check does not certify Julia's
serializer or the subsequent SoftAbs transcendental operations.
`RestrictedQuarticRationalCertificate.softAbsMetricEntryCertificate` then
uses the accepted Hessian record as the input bound for the existing guarded
metric pipeline. Thus the callback-to-Hessian edge is closed for each checked
artifact; SoftAbs evaluation and its derived positive-domain operations remain
explicit backend contracts rather than being silently assumed.

At the maintained Julia API, `restricted_potential_rwmh` turns any parsed
`RestrictedExpr` potential into the sign-correct log-density callback consumed
by `GaussianRWMH`. `restricted_potential_hmc` additionally routes the same
tree's symbolic derivative into `ScalarHMC`, while
`restricted_potential_slice` supplies the potential value to the maintained
stepping-out sampler. Consequently the generated quartic artifact is runnable
through all three algorithms without handwritten duplicate formulas.
Deterministic regression tests check replay and finite movement; the exact
Lean target semantics do not by themselves certify Float64 proposal,
integrator, slice arithmetic, or RNG behavior.

The analytic transport part of the derived positive-domain operations is now
reusable rather than backend-specific. `sqrt_approximates_sqrt`,
`inv_approximates_inv`, and `log_approximates_log` prove the respective factors

```text
1 / (sqrt(computed) + sqrt(ideal))
1 / (|computed| |ideal|)
1 / min(computed, ideal)
```

on their positive/nonzero domains. Their `*_backend_approximates` companions
add a backend's local operation error. The remaining platform obligations are
therefore local rounding/libm evidence, SoftAbs-transform transport, solver
arithmetic, and RNG semantics.
`SoftAbsLocalPrimitiveBackend` is the resulting client-facing contract. Its
upgrade constructor automatically installs the three displayed transport
terms into `SoftAbsPrimitiveBackend`; a platform adapter supplies only local
errors for those operations plus the still-complete SoftAbs-transform bound.

Square root also has an assumption-free, execution-specific route.
`SqrtRationalIntervalCertificate` records the exact rational representations
of a nonnegative Float64 input, its computed square root, and a rational
radius. Lean checks that the two squared interval endpoints enclose the input
and proves that the computed value is within that radius of `Real.sqrt`.
Julia derives a conservative radius by exact rational arithmetic and the
compiled oracle accepts a genuine `sqrt(0.5)` execution while rejecting a
zero-radius mutation. This is sound ex-post evidence for the observed call;
it is not a uniform accuracy theorem for the platform implementation.
`ReciprocalRationalResidualCertificate` handles the next SoftAbs operation in
the same execution-specific manner: Julia computes the exact rational residual
from a nonzero Float64 input and output, and Lean proves the corresponding real
absolute-error bound. Its regression certifies the reciprocal of the observed
`sqrt(0.5)` output and rejects a falsely zero residual. A composition theorem
then targets the inverse square root of the original input with the sum of the
checked local reciprocal residual and exact reciprocal transport term; the
combined oracle command checks the shared intermediate value.
`LogRationalIntervalCertificate` closes the local positive-log call without a
libm premise as well. With `z = (x - 1)/(x + 1)`, it checks the observed output
against the first 32 rational terms of the artanh series for `log x` plus the
proved remainder `2*|z|^65/(1-z^2)`. Lean then proves the observed output bound
and can transport it to an approximate positive ideal input. The enclosure is
sound for every positive rational input and is tight enough for the maintained
nontrivial SoftAbs selection margin.

The positive SoftAbs transform is no longer entirely opaque. Lean proves
`x/(1+x) ≤ tanh x ≤ min(x,1)` for `x>0`; a rational certificate encloses the observed
Float64 `tanh`, requires its symmetric error interval to retain a positive
denominator, and checks the exact residual of the subsequent division.
Lean also proves that `tanh` is globally one-Lipschitz, so the certificate
records the exact rational residual of the rounded Float64 product `α*h` and
transports it to the ideal argument instead of requiring that product to be
exact.
`PositiveSoftAbsMetricRationalCertificate` links that result to the square-root,
reciprocal, and logarithm records and constructs the complete metric-entry
witness. The maintained `(α,h)=(1,1)`, small-argument `(1,0.1)`, and rounded-
product `(0.1,0.1)` calls pass this route, while mutated argument or `tanh`
radii fail. This is a sound per-execution adapter, not a universal `tanh`
accuracy model.

`PositiveSoftAbsHamiltonianRationalCertificate` composes the metric entry into
the scalar unit-parameter relativistic Hamiltonian used for trajectory
weights. It records the observed potential and momentum, a rational residual
for the rounded transformed-momentum radicand, an ex-post square-root
certificate for the kinetic term, and the final energy-addition residual.
Lean transports these to the ideal SoftAbs factor and proves the complete
endpoint-energy bound. This closes one endpoint evaluation; iteration of the
approximate implicit solver and multi-endpoint selection remain separate
trajectory obligations.

`PositiveSoftAbsMetricErrorUpperCertificate` and
`PositiveSoftAbsHamiltonianErrorUpperCertificate` make these analytic radii
usable by a foreign runtime without serializing irrational ideal quantities.
Checked positive rational lower bounds on `tanh` and the relevant square roots
yield rational upper bounds for the metric factor, log determinant, transformed
momentum, radicand, kinetic term, and final energy.

The implicit-solver side has a matching rational arithmetic layer.
`AposterioriContractionRationalCertificate` checks a rate in `[0,1)` and the
exact budget `residualUpper/(1-rate)`. Lean's theorem turns this into distance
to the unique fixed point only after a client proves both the contraction and
that `residualUpper` bounds the exact one-step residual. Julia and the oracle
exercise this record on the maintained fixed-point solver. Consequently a
rounded callback residual is never silently promoted to an exact residual.
The reference runtime additionally exposes
`fixed_point_generalized_leapfrog_trace`: its final iterate, one-more-update,
and iteration count for each implicit loop are the actual values used to form
the residual. `RoundedContractionResidualRationalCertificate` checks the exact
rational formula `|iterate-computedUpdate|+updateError`; Lean proves that a
valid callback/arithmetic bound for `updateError` yields the exact residual
premise above and hence the distance-to-fixed-point conclusion. The trace does
not itself prove that target-specific update-error premise.

The update arithmetic is now checked separately from that premise.
`RoundedAffineUpdateRationalCertificate` represents the common solver form
`base + scale*callback`, records the actual computed callback and update, and
checks their exact rational multiply/add residual. Lean proves that adding
`|scale|*callbackError` gives a sound exact-update radius and feeds it directly
to the contraction theorem. The reference trace retains the callback used by
each final half-momentum and position update, so the Julia records bind to the
executed values. Only `callbackError` remains target/platform evidence.

For the maintained bounded-client range, sine and cosine no longer require a
platform accuracy premise. `SinCosRationalIntervalCertificate` checks the
observed values against mathlib's proved cubic-sine and quadratic-cosine
remainders on `[-1,1]`. Lean transports these enclosures into `2+sin(q)` and
the scale-times-cosine factor used by the position callback. Julia/oracle cover
the actual `q=0.25` execution and reject a false zero radius. The linked
`BoundedScalarCallbackRationalCertificate` now continues through the observed
rounded transformed momentum and radicand, an ex-post square-root enclosure,
the reciprocal, and both final callback arithmetic expressions. Lean proves
the two checked outputs approximate the exact bounded-client position and
momentum derivatives; Julia/oracle exercise `(q,p)=(0.25,-0.35)` and reject
tampered radicand and callback residuals. This remains a per-execution,
range-guarded result rather than a platform-wide libm theorem.

The reference fixed-point trace also retains every callback evaluation, not
only the two final residual callbacks. Its ordered certificate schema requires
one position callback per half-momentum iteration, the initial momentum
callback and one per position iteration, followed by the final position,
momentum, and position calls. Lean derives the total count
`halfIterations + positionIterations + 4` and proves the selected approximation
statement for every entry. The Julia/Lean regression covers all 29 calls in
the maintained solve and fails closed on count, order, or entry tampering.

Rounded update coverage follows the same trace. Each half-momentum or final
momentum update links one checked position derivative to its observed
`base + scale*callback` result; each implicit position update links the sum of
the checked initial and terminal velocities. The combined Lean certificate
checks those centers and the sum of their radii before applying the exact
rational affine residual theorem. It also includes the observed rounding
residual when the two Float64 velocities are added; seven such sums are
nonexact in the maintained trace. Julia/oracle validate all 28 executed
updates in the maintained run and reject a callback-radius mutation.

The maintained trace now closes the fixed-point step as well. Its final
half-momentum and position recomputations feed phase-tagged rational residual
and contraction records. `BoundedScalarSolverContractionRationalCertificate`
checks the complete affine provenance, returned iterate, exact step-dependent
rate, and `|ε/2|*3 < 1` solver condition. Lean then proves the reported distance
from each runtime iterate to the corresponding unique exact fixed point. This
is still an execution-specific certificate; it does not assert a platform-wide
Float64 or libm error model.

The two fixed-point records are not incorrectly identified with an exact phase
endpoint. The implicit position map uses the rounded half momentum, so Lean
first proves a global `9` momentum-Lipschitz bound for the bounded velocity
callback and a fixed-point sensitivity theorem. The paired rational
certificate checks the cross-loop callback linkage and adds that sensitivity
to the position residual budget. It therefore constructs exact half-momentum
and position fixed points with coordinate error bounds. The final affine
callback record is now linked as well. Explicit analytic force bounds propagate
those coordinates through the last kick, producing an exact endpoint and
product-metric radius. A separately checked endpoint callback then evaluates
the bounded Hamiltonian and transports it to that exact endpoint. These remain
per-execution rational certificates, not a platform-wide floating-point model.

`PositiveSoftAbsEndpointStateTransportCertificate` closes the next generic
composition. It adds `energyLipschitz * solverStateError` to the fully rational
endpoint-evaluation error. Lean proves both the region-restricted energy
transport and a direct scalar theorem chaining the rounded residual,
contraction-selected fixed point, and endpoint energy. The runtime constructor
can consume a `RoundedContractionPairCertificate` directly. Supplying a sound
numeric Hamiltonian Lipschitz bound and the callback/arithmetic error for a
specific practical SoftAbs trajectory remains a target-level obligation.

The bounded nonconstant solver client already supplies such analytic constants
for its complete Hamiltonian
`H(q,p)=sqrt(1+((2+sin(q))*p)^2)`: Lean proves a global momentum constant `3`
and a global position constant `|p|`. Thus its remaining runtime boundary is
the rounded callback/update evidence, rather than an unspecified Hamiltonian
regularity premise. The generated quartic diagonal-SoftAbs target requires a
separate target-specific bound.

At the finite-trajectory layer,
`PositiveSoftAbsHamiltonianTrajectoryCertificate` collects heterogeneous
endpoint witnesses and automatically constructs a conservative common budget
as the finite maximum of their complete derived errors. Lean feeds
its energy theorem directly into `stabilizedMultinomialSelectionCertificate`,
thereby composing maximum stabilization, exponential errors, cumulative
boundaries, the scaled uniform draw, and the final decision-margin theorem.
The Julia wire record carries a count followed by complete endpoint records;
the oracle rejects inconsistent lengths or any invalid endpoint. For the
maintained three-endpoint execution, Julia also constructs local
nonpositive-exponential certificates, exact cumulative-sum and scaled-draw
residuals, and the rational endpoint upper bounds above. Its strict decision
margin proves equality of computed and ideal selected indices. A generic
Float64 implicit-solver trajectory still needs target-specific update-error
and Lipschitz witnesses; RNG distributional semantics also remain separate.
An exact-real specialization supplies exact stabilized exponentials,
summation, multiplication, and uniform input and constructs the complete
selection certificate with zero backend-local errors. It isolates the
remaining practical obligation to the corresponding concrete backend calls.

Nonpositive stabilized exponentials also have an assumption-free ex-post
backend certificate. Lean proves the global rational enclosure
`max(0,1+x) ≤ exp(x) ≤ 1/(1-x)` for `x ≤ 0`; the accepted interval therefore
proves the observed Float64 result without a libm accuracy axiom. A linked
record transports a rounded computed argument to an exact rational ideal
argument using the unit Lipschitz constant of `exp` on the nonpositive
half-line and directly yields the `stabilizedBoltzmannWeight` premise. The
enclosure is conservative, especially far below zero.

`PositiveSoftAbsStabilizedWeightTrajectoryCertificate` links one transported
exponential to every endpoint's exact maximum-stabilized argument. Lean takes
the finite maximum of their result-plus-argument errors and supplies the
weight premise to the trajectory selection constructor automatically. The
corresponding Julia constructor derives exact rational ideal arguments from
the checked Float64 endpoint energies and records each rounded subtraction.
The arithmetic-aware selection constructor accepts the actual rounded prefix
sums and total, their errors against exact sums of the computed weights, and
the residual of the final `uniform*total` multiplication. The rational
`RoundedCumulativeRationalCertificate` checks every prefix directly against
the exact binary-rational weight sum rather than trusting an already rounded
predecessor. `ScaledDrawRationalCertificate` checks the final product. Once
these are supplied, `MultinomialDecisionRationalCertificate` checks the final
separation using the actual computed draw and boundaries. Lean proves this
computed-value separation implies the same selected index as the ideal
selection whenever the recorded errors upper-bound the complete composed bounds.
The uniform source's distributional interpretation remains separate.

For example, after obtaining analytic or trusted-oracle bounds for one RWMH
execution:

```julia
using VerifiedSamplers

certificate = Certificates.certify_rwmh_decision(
    computed_current_logdensity=-0.5,
    ideal_current_logdensity=big"-0.5",
    current_logdensity_bound=big"0",
    computed_proposal_logdensity=-0.5,
    ideal_proposal_logdensity=big"-0.5",
    proposal_logdensity_bound=big"0",
    computed_threshold=1.0,
    ideal_threshold=big"1",
    exp_bound=big"0",
    computed_uniform=0.25,
    ideal_uniform=big"0.25",
    uniform_bound=big"0")

Certificates.is_stable(certificate) # branch agreement follows conditionally
```
