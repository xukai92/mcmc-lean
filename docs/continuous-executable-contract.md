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

The version-10 artifact contains scalar and vector-valued multi-step endpoint
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
part of generated IR version 10 and are interpreted by Julia Reference. Lean
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
| Ideal continuous IR to Julia | The maintained interpreter mirrors primitive order and control flow and is differentially tested; a machine-checked cross-language/numerical refinement remains future work. |

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
