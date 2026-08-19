# Progress matrix

This page is the concise, method-by-property view of the repository. The
[project status](project-status.md) gives the hypotheses and exact theorem
boundaries; paper-specific repairs live in the corresponding coverage audits.

## Overall snapshot

| Area | Current state | Meaning |
|---|---|---|
| Core formal library | Complete at the declared theorem surface | Exact kernels/laws and their stated invariance, coupling, convergence, or estimator properties compile without proof placeholders |
| Paper targets | Complete with documented corrections | Xu et al. (2021), Xu and Ge (2024), and the formal core drawn from Ge et al. (2018) have claim-by-claim audits |
| Maintained Julia runtime | Complete for the registered core methods | Public samplers, generated/reference paths, optimized implementations, and registered diagnostics pass the release suite |
| Cross-language assurance | Complete at the declared exact/guarded boundary | IR regeneration, typed finite parse/decode/re-render, oracle replay, exact finite execution, and selected per-run certificates are checked |
| Universal floating-point assurance | Parked | No generic Julia/LLVM/IEEE-754/`libm`/RNG theorem is claimed |
| Hard research extensions | Parked after substantial foundations | Production-NUTS equivalence, multidimensional BPS uniqueness/ergodicity, broader adaptive convergence, and model-uniform growing-horizon particle results are not core blockers |

## How to read the matrix

- **Proved** means machine checked in Lean at the stated scope.
- **Conditional** means Lean proves the result from explicit assumptions or a
  supplied certificate; it is not an unconditional implementation claim.
- **Tested** describes Julia evidence, not a mathematical proof.
- **Parked** is outside the current core-completion boundary.
- A dash means the property is not currently claimed for that method.

## Sampler coverage

| Method or layer | Exact kernel / law | Invariance / reversibility | Convergence or quantitative result | Maintained Julia | Execution refinement |
|---|---|---|---|---|---|
| Finite MH | Proved | Proved, including asymmetric and zero-proposal cases | Conditional finite-chain results | Reference + Optimized; exhaustive traces | Exact integer trace/oracle path |
| General-state MH and Gaussian RWMH | Proved with mathlib kernels | Proved for the normalized target | Independence-MH geometric bound; no generic RWMH convergence claim | Reference + Optimized | Guarded scalar decision certificates; generic Float64 proof parked |
| Endpoint HMC | Proved phase and position kernels | Proved from reversal and volume preservation | Concrete GR-HMC result below; no generic HMC convergence claim | Scalar/vector Reference + Optimized | Exact dyadic and guarded rounded trajectory checks |
| Multinomial HMC | Proved randomized-origin and constant-metric kernels | Proved | Xu et al. coupling/meeting results on instantiated targets | Reference + Optimized | Guarded weight and selection certificates |
| Diagonal SoftAbs / GR-HMC | Proved exact generalized-leapfrog client | Proved for Gaussian and bounded position-dependent clients | Proved setwise convergence for the one-dimensional Gaussian `ε=1`, `L=1` chain | `GaussianSoftAbsGRHMC` and certified position-dependent interface | Per-execution certificates retained; generic platform refinement parked |
| General-state PG--HMC composition | Proved operator composition | Proved common-target invariance | Exact-refresh augmented clients have scoped convergence; unaugmented stationarity is not promoted to convergence | Generated schedule and Gaussian-mixture diagnostic | Callback equality remains an explicit boundary |
| SMC, pseudo-marginal, PIMH, and PMMH | Proved finite-horizon extended laws | Proved for the stated extended targets and marginals | Fixed-horizon `C/N` particle bounds under explicit stability assumptions | Particle-count experiment; finite clients | Exact finite arithmetic where implemented |
| Particle Gibbs | Proved conditional-SMC and selected-path laws | Proved | Fixed-horizon geometric TV bounds and particle-count results under stated support/minorization assumptions | Finite-HMM Reference/Optimized trace replay | Exact integer finite client |
| Checked dynamic-tree HMC | Proved for certified completed trees and C.4 construction | Proved; invalid certificates fall back to identity | No generic NUTS convergence claim | Conservative, C.4, first-stop checked, and recursive checked clients | Local trajectory/decision certificates; production-NUTS equivalence parked |
| Fixed-parameter production-shaped NUTS | Runtime semantics only | Not yet proved for the runtime transition | — | Classic/generalized termination × multinomial/slice selection, fixed metrics, depth/divergence diagnostics | Certified decisions refine online candidates; balanced index recursion equals the structural turn fold; Julia call-trace, leaf-failure, and full-transition correspondence remain |
| Practical slice sampling | Proved bounded stepping-out/shrinkage law | Proved, including identity exhaustion fallback | — | Reference/runtime implementation and diagnostics | Guarded callback/log/decision trace; generic platform proof parked |
| Reversible jump | Proved transport-density kernels | Proved for scalar, planar, product, and nonlinear shear clients | — | Sheared and three-dimensional clients | Exact transport theorem; generic compiler optional |
| Adaptation | Proved finite-freeze, proxy, and selected indefinite interfaces | Frozen/common-target cases proved | Scoped setwise convergence and counterexamples | Warmup and indefinite demonstration clients | Realistic never-freezing MCMC replacement parked |
| Zig-Zag and BPS foundations | Proved stopped/horizon kernels at documented scopes | One-dimensional Gaussian Zig-Zag/BPS proved; multidimensional BPS remains conditional | Nonexplosion and semigroup components proved; multidimensional uniqueness/ergodicity parked | Gaussian Zig-Zag client | Exact event semantics; platform clock refinement not claimed |

## Paper targets

| Target | Formal status | Executable status | Important qualification |
|---|---|---|---|
| Xu et al. (2021) | Corrected main theorem surface, Gaussian and regularized-logistic meeting/marginal/unbiased-estimator results | Seeded Gaussian and finite-data logistic experiments | The obstructed exponent-two statement is not asserted |
| Xu and Ge (2024) | Corrected relativistic momentum/transport statements and exact diagonal SoftAbs solver clients | Constant-metric and certificate-gated position-dependent implementations | Exact solver validity does not imply arbitrary finite-loop Float64 equivalence |
| Ge et al. (2018) | Target-preserving composition, finite probabilistic-program semantics, and coroutine/operator foundations | Generated PG--HMC descriptors, observation cursor, and mixed-state diagnostic | Systems-performance and arbitrary callback claims are not formalized |

## Core completion versus parked research

The core release requires exact mathematical semantics and proofs at their
declared scopes, maintained Julia paths, reproducible generated artifacts,
examples, diagnostics, and documentation. It deliberately does not require:

- universal Julia/LLVM/IEEE-754, `libm`, serializer, or RNG correctness;
- completion of every experimental numerical certificate;
- equivalence to ordinary production recursive NUTS;
- multidimensional BPS weak-forward uniqueness or refreshed ergodicity;
- model-uniform growing-horizon particle-MCMC stability; or
- a realistic never-freezing adaptive MCMC theorem without exact refresh.

Existing foundations for these branches remain in the repository and continue
to build. “Parked” does not mean disproved or deleted.

## Release evidence

The authoritative gates are:

```sh
make test
make check-docs-generated
julia --project=docs docs/make.jl
```

See the [core release audit](core-release-audit.md) for dated evidence and the
[testing strategy](testing.md) for what each test class does—and does not—show.
