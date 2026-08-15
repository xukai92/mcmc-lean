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

The version-6 artifact contains scalar and vector-valued multi-step endpoint
HMC (introduced in version 5), together with constant-metric programs.
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
part of generated IR version 6 and are interpreted by Julia Reference. Lean
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
