# verified-samplers

**[Documentation](https://xukai92.github.io/mcmc-lean/)**

`verified-samplers` develops machine-checked MCMC algorithms in Lean 4 and
connects them to an auditable Julia runtime. The formal layer uses mathlib's
measure theory and `ProbabilityTheory.Kernel`; the runtime separates generated
reference programs from maintained optimized implementations.

The project proves exact mathematical statements about samplers. It does not
infer convergence from stationarity, or Float64 correctness from an exact-real
theorem. Every such boundary is stated explicitly.

## Repository layout

```text
formal/                         Lean library, examples, IR, and oracle
VerifiedSamplers.jl/            maintained Julia package
  src/Reference/                generated/interpreted reference layer
  src/Optimized/                independent optimized implementations
  src/Backends/                 capability, batching, and parallel contracts
  src/Evaluation/               shared targets and statistical diagnostics
  src/Public/                   extracted public sampler dispatch surfaces
docs/                           architecture, theorem coverage, and roadmaps
Makefile                        reproducible build, generation, and test gates
```

The Lean library is rooted at `Mcmc`; its public import surface is
`formal/Mcmc.lean`. Reference generation is explicit—ordinary builds never
rewrite committed artifacts.

## Current scope

The core release includes:

- general-state and finite Metropolis--Hastings foundations;
- RWMH, HMC, multinomial HMC, coupling, and meeting-time results;
- corrected theorem coverage for Xu et al. (2021) and Xu and Ge (2024);
- composable PG--HMC semantics inspired by Ge et al. (2018);
- finite SMC, pseudo-marginal methods, PMMH, and particle Gibbs;
- checked dynamic-tree HMC, practical slice sampling, and reversible jump;
- scoped adaptation, PDMP, and concrete convergence results; and
- generated/reference/optimized Julia paths with deterministic, property,
  statistical, and performance diagnostics.

Generic IEEE-754, platform `libm`, serializer, and RNG correctness are not core
requirements. The existing numerical-certificate layer is retained as
experimental infrastructure. Production recursive-NUTS equivalence,
multidimensional BPS uniqueness/ergodicity, broadly model-uniform
growing-horizon particle stability, and stronger adaptation results are parked
research extensions.

See the [progress matrix](docs/progress.md) for method-by-property coverage and
the [project status](docs/project-status.md) for exact boundaries.

## Build and test

The formal project pins Lean and mathlib. From the repository root:

```sh
cd formal
lake update
lake exe cache get
cd ..

make test
```

Useful narrower commands are:

```sh
make formal                 # build the Lean library
make julia                  # run the Julia package tests
make generate               # explicitly regenerate the committed IR
make check-generated        # require byte-for-byte generated-IR agreement
make check-docs-generated   # require generated graph/document agreement
julia --project=docs docs/make.jl
```

## Minimal Julia examples

```julia
using Random
using VerifiedSamplers

rng = MersenneTwister(42)

# Random-walk Metropolis for a standard normal target.
rwmh = GaussianRWMH(x -> -x^2 / 2, 0.8)
rwmh_draws = sample(rng, rwmh, 0.0, 2_000)

# Vector endpoint HMC for a standard Gaussian target.
hmc = VectorHMC(q -> -sum(abs2, q) / 2, identity, 0.15, 8)
hmc_draws = sample(rng, hmc, zeros(2), 2_000)
```

The API uses `sample(rng, sampler, initial, count)`. Methods without an explicit
RNG dispatch to Julia's default RNG. See the
[executable architecture](docs/executable-architecture.md) and
[testing strategy](docs/testing.md) before interpreting runtime tests as formal
guarantees.

## Documentation map

- [Architecture](docs/architecture.md): mathlib measures through kernels,
  samplers, paper clients, and executable layers.
- [Adding a sampler](docs/development-guide.md): contributor workflow from
  mathematical formalization through IR refinement and Julia integration.
- [AdvancedHMC parity](docs/advancedhmc-parity.md): current non-adaptive
  fixed-parameter HMC/NUTS coverage goal.
- [Progress matrix](docs/progress.md): concise method/property coverage.
- [Core release audit](docs/core-release-audit.md): named evidence and release
  gates.
- [Project status](docs/project-status.md): detailed completed and parked work.
- [Overall roadmap](docs/project-roadmap.md): dependency history and future
  research branches.
- [Related work](docs/related-work.md): literature and design implications.
- [Xu et al. 2021 audit](docs/xu21-coverage.md),
  [Xu and Ge 2024 audit](docs/xu24-coverage.md), and
  [Ge et al. 2018 audit](docs/ge18-coverage.md): paper-statement corrections and
  precise theorem coverage.
- [Development log](docs/development-log.md): theorem-level implementation
  ledger.

## Claim discipline

- Detailed balance implies stationarity.
- Stationarity alone does not imply convergence from arbitrary initial states.
- Convergence claims state their ergodicity assumptions and mode of
  convergence.
- Exact-real Lean semantics do not automatically describe Julia Float64
  execution.
- Statistical tests diagnose implementations; they do not replace proofs.

These distinctions are part of the public contract, not merely caveats.
