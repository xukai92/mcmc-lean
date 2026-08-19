# Gaussian RWMH development record

This is the completed obligation record for scalar Gaussian random-walk
Metropolis--Hastings (RWMH). It is the reference example for the
[sampler-development template](sampler-development-template.md), and records
what each repository layer establishes without treating tests as proofs.

## 1. Mathematical identity

- **State space:** `ℝ` with its Borel measurable space.
- **Target:** the measure with Lebesgue density `exp ∘ logDensity`.
- **Proposal:** `y = x + scale * z`, where `z` is standard normal and
  `scale > 0`.
- **Transition:** accept with probability
  `min(1, exp(logDensity y - logDensity x))`; otherwise retain `x`.
- **Formal assumptions:** a positive proposal scale and measurable,
  everywhere-finite real-valued log density. Normalization is needed only for
  the stationary-probability statement.
- **Claim level:** Markov-kernel validity, reversibility, and target
  invariance. No generic convergence-from-an-initial-state claim is made.

The reusable general-state construction is
`Mcmc.Kernel.gaussianRandomWalkMetropolisHastings` in
`formal/Mcmc/Kernel/RandomWalkMetropolisHastings.lean`.

## 2. Formal evidence

| Obligation | Lean declaration | Status |
|---|---|---|
| Mathematical transition | `gaussianRandomWalkMetropolisHastings` | Proved construction |
| Markov-kernel validity | `gaussianRandomWalkMetropolisHastings_isMarkov` | Proved |
| Reversibility | `gaussianRandomWalkMetropolisHastings_isReversible` | Proved |
| Target invariance | `gaussianRandomWalkMetropolisHastings_invariant` | Proved |
| Normalized stationary target | `gaussianRwmhKernel_stationary_probability` | Proved under explicit normalization |
| Generic convergence | — | Not claimed; no irreducibility/aperiodicity or convergence mode is supplied here |

## 3. Executable presentation

`gaussianRwmhProgram` in
`formal/Mcmc/Executable/Continuous/CompilerIR.lean` uses the existing typed
continuous command IR. One step consumes a standard-normal draw and a
unit-uniform draw, evaluates the log-density callback at the current and
proposed states, and returns either the proposal or current state.

The ideal-real Lean interpreter is explicit-trace execution:
`runGaussianRwmh` takes real-valued noise and uniform streams rather than a
platform RNG. `runGaussianRwmh_refines` proves its deterministic result and
trace consumption. The command is serialized by `Mcmc.Executable.IRFormat`
into `VerifiedSamplers.jl/src/Reference/Samplers.ir`; generation remains an
explicit `make generate` operation.

## 4. Refinement boundary

The strongest mathematical bridge is exact kernel equality:
`gaussianRwmhProgramKernel_refines` proves that the exact kernel denotation of
the command is the verified Gaussian RWMH kernel. Consequently
`gaussianRwmhKernel_invariant` transfers target invariance to that denotation.

Separately, the Lean trace interpreter has deterministic replay theorems.
Artifact regeneration is checked byte-for-byte, while Julia parser behavior
and Reference/Optimized agreement are tested. These facts do **not** prove a
general equality between exact-real Lean execution and Julia `Float64`, its
callbacks, transcendental functions, or RNG law. The bounded RWMH certificate
path documents conditional, per-execution numerical evidence; it is not on the
ordinary execution path.

## 5. Maintained Julia paths

| Layer | Declaration or file | Evidence |
|---|---|---|
| Canonical artifact | `VerifiedSamplers.jl/src/Reference/Samplers.ir` | `make check-generated` |
| Reference interpreter | `Reference.gaussian_rwmh_step!` | fixed-trace and malformed-input tests |
| Public sampler | `GaussianRWMH`, `step`, and `sample` | seeded API tests |
| Optimized comparison | `Optimized.gaussian_rwmh_step!` | deterministic differential tests |

The public sampler deliberately routes through Reference. Optimized is an
independent handwritten comparison and does not inherit the Lean theorem.

## 6. Diagnostics

The continuous Julia tests cover forced accept/reject traces, random-source
consumption, validation errors, Reference/Optimized agreement, and seeded
Gaussian moment checks. Shared moment, covariance, quantile, ESS, and
batch-means formulas live in
`VerifiedSamplers.jl/test/support/QualityDiagnostics.jl`. Statistical tests are
implementation regressions, not proofs of detailed balance or convergence.

## 7. Completion evidence

- [x] Public Lean modules are exported through `formal/Mcmc.lean`.
- [x] Assumptions and theorem strength are explicit.
- [x] Exact kernel and trace-refinement boundaries are recorded.
- [x] Canonical artifact regeneration is checked.
- [x] Reference, public, and Optimized Julia paths are tested.
- [x] Exact-real versus `Float64` limitations remain visible.
- [x] Repository validation commands cover the maintained path.

The corresponding source-by-source diagram and runnable Julia example are in
[Verified execution and optimization](verified-execution-and-optimization.md#worked-path-continuous-gaussian-rwmh).
