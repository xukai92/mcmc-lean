# Non-adaptive AdvancedHMC parity

This page fixes the scope of the current runtime-coverage goal. The comparison
target is the fixed-parameter algorithmic surface of AdvancedHMC.jl, not its
adaptation, accelerator, or probabilistic-programming integrations.

The audit follows AdvancedHMC's current [detailed API](https://turinglang.org/AdvancedHMC.jl/stable/api/)
and its authoritative [integrator](https://github.com/TuringLang/AdvancedHMC.jl/blob/master/src/integrator.jl)
and [trajectory](https://github.com/TuringLang/AdvancedHMC.jl/blob/master/src/trajectory.jl)
sources. In particular, fixed integration time uses
`max(1, floor(trajectory_length / nominal_step_size))`, and jitter is symmetric
around the nominal step size. The prose formula in the upstream jitter
docstring omits that symmetry, while the implementation applies it.

“Runnable” means a stable public Julia constructor and `step`/`sample` path with
deterministic tests. It does not by itself mean that Julia `Float64` execution
has inherited an exact-real Lean theorem. Formal and execution-refinement
coverage are tracked separately.

## Included surface

| Family | Target |
|---|---|
| Static trajectory | Endpoint HMC with fixed step count or fixed integration time |
| Fixed multinomial trajectory | Multinomial HMC with a fixed trajectory |
| Dynamic trajectory | Classic and generalized no-U-turn termination |
| Dynamic selection | Multinomial and slice selection for each no-U-turn criterion |
| Integrators | Ordinary, per-trajectory jittered, and tempered leapfrog |
| Metrics | Unit, diagonal, dense, and fixed low-rank-update Euclidean metrics |
| Momentum | Full and partial refreshment |
| Safety | Maximum tree depth and Hamiltonian-divergence termination |
| Results | Structured acceptance, energy, step-count, depth, and divergence diagnostics |

This is feature-level coverage, not a claim that every trajectory, integrator,
metric, and momentum-refresh component can currently be combined arbitrarily.
The maintained combinations are:

| Trajectory | Ordinary | Jittered | Tempered | Partial refresh |
|---|---:|---:|---:|---:|
| Fixed-step endpoint | Yes | Yes | Yes | Yes, ordinary integrator |
| Fixed integration time endpoint | Yes | Via equivalent fixed nominal step count | Via equivalent fixed nominal step count | No dedicated wrapper |
| Fixed multinomial | Yes | No dedicated wrapper | No dedicated wrapper | No dedicated wrapper |
| Dynamic NUTS | Yes | Yes | Yes | No dedicated wrapper |

All maintained ordinary endpoint and NUTS paths accept unit, diagonal, dense,
and fixed low-rank-update metrics. Jittered, tempered, and partial-refresh
endpoint paths accept the same metrics. “Via equivalent fixed nominal step
count” means the user constructs the corresponding integrator sampler with the
step count determined from the nominal step size; it is not yet one composable
constructor.

The production-shaped fixed-parameter NUTS family is now runnable. Existing
checked dynamic-tree samplers remain distinct foundations and conservative
clients: runtime availability is not relabeled as verified recursive NUTS
without the remaining correspondence argument.

## Explicit exclusions

- HMCDA, dual averaging, and initial-step-size adaptation;
- mass-matrix adaptation and Stan-style windowed warmup;
- GPU, threaded, distributed, and vectorized-chain execution;
- automatic differentiation; and
- AbstractMCMC or Turing integration.

Users therefore supply the log density, gradient, fixed step size, fixed metric,
and termination limits. Excluding warmup does not weaken the desired fixed-kernel
invariance result: parameters are selected externally and held constant during
the chain.

## Delivery standard

Each covered sampler should provide:

1. a public Julia API using `sample(rng, sampler, initial, count)`;
2. deterministic primitive-trace or Reference/Optimized comparison tests;
3. property and seeded distributional diagnostics appropriate to the method;
4. ideal semantics in Lean and a clear lowering/refinement boundary; and
5. an invariance theorem, or an explicit runtime-only label until that theorem
   is supplied.

The mathematical sampler is defined independently of the executable IR. When a
new component is missing, the project follows the choices in
[Adding a sampler](development-guide.md): reuse the core IR, add a reusable IR
construct, or introduce a typed sub-IR/certified primitive.

## Current implementation snapshot

| Capability | Runtime | Formal boundary |
|---|---|---|
| Fixed-step endpoint HMC | Complete | Existing exact endpoint-HMC theory |
| Fixed-integration-time endpoint HMC | Complete | Reuses a fixed positive step count; dedicated public documentation pending |
| Fixed multinomial HMC | Complete | Existing exact multinomial-HMC theory |
| Jittered endpoint HMC | Complete | Runtime mixture over fixed-step transitions; dedicated IR/refinement pending |
| Tempered endpoint HMC | Complete | Runtime implementation; formal integrator/refinement pending |
| Fixed-parameter NUTS family | Complete for classic/generalized × slice/multinomial × ordinary/jittered/tempered runtime combinations | Lean proves equal continuation and equal ordered candidate occurrences for successful online/completed builds; numerical tree construction and full transition correspondence remain pending |
| Partial momentum refresh | Complete for fixed-step endpoint runtime | Formal momentum-refresh foundations exist; runtime composition refinement pending |
| Fixed low-rank-update metric | Complete through dense Reference lowering | General constant-metric foundations exist; factorized-performance lowering is not claimed |
| Structured transition diagnostics | Complete for NUTS and partial-refresh transitions | Diagnostic data are not part of kernel correctness |

## Current runtime example

The default fixed-parameter NUTS configuration uses generalized U-turn
termination and multinomial trajectory selection:

```julia
using Random
using VerifiedSamplers

logdensity(q) = -sum(abs2, q) / 2
gradient(q) = q

sampler = NUTS(logdensity, gradient, 0.25;
    max_depth=8,
    max_energy_error=1000.0,
    termination=:generalized,
    selection=:multinomial)

run = sample_with_diagnostics(MersenneTwister(42), sampler, zeros(4), 2_000)
draws = run.samples
depths = [result.tree_depth for result in run.diagnostics]
divergences = count(result -> result.divergent, run.diagnostics)
```

Changing `termination` to `:classic` or `selection` to `:slice` selects the
other covered combinations. This is presently a tested runtime implementation,
not yet the endpoint of a Lean theorem identifying the online recursive Julia
transition with the certified completed-tree kernel.

The existing formal bridge is narrower and useful: for a precomputed recursive
phase tree, `onlineBuildSummary_continues_eq_toBuildFlagTree` proves that an
online builder which skips the right subtree after failure returns the same
continuation bit as the completed-tree checker. A successful online build also
visits every leaf and returns exactly the completed tree's candidate
occurrences, preserving order and multiplicity. The generic consumer theorem
then covers weighting and selection under any fixed random trace. Existing
bounded leaf-energy and U-turn certificates now refine the entire online
summary—continuation, visit count, and candidates—to its ideal-real counterpart.
For balanced power-of-two intervals, the fuel-bounded index recursion used by
the generated descriptor is also proved equal to the structural U-turn fold;
the corresponding concrete continuation recursion now includes arbitrary
leaf eligibility/divergence checks and is proved equal to both completed and
online structural continuation. Every successful subtree emits exactly its
consecutive index range. These theorems do not yet identify Julia's concrete
call trace with that Lean index recursion or identify the resulting complete
transition with a verified invariant kernel.
