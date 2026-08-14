# verified-samplers

`verified-samplers` formalizes Markov chain Monte Carlo algorithms and coupling
arguments in Lean 4 and is developing an auditable Julia reference and runtime
layer. The mathematical development uses mathlib's measure and
`ProbabilityTheory.Kernel` interfaces.

The two paper targets are:

- Xu et al., [“Couplings for Multinomial Hamiltonian Monte Carlo”](https://proceedings.mlr.press/v130/xu21i.html)
  (AISTATS 2021): [coverage audit](docs/xu21-coverage.md) and
  [roadmap](docs/xu21-roadmap.md);
- Xu and Ge, [“Practical Hamiltonian Monte Carlo on Riemannian Manifolds via
  Relativity Theory”](https://proceedings.mlr.press/v235/xu24i.html)
  (ICML 2024): [coverage audit](docs/xu24-coverage.md) and
  [roadmap](docs/xu24-roadmap.md).

The algorithms are defined as mathlib kernels rather than assumed through
opaque interfaces. Any corrected, conditional, obstructed, or empirical paper
statement is classified in its corresponding coverage audit.

Betancourt's [*A Conceptual Introduction to Hamiltonian Monte
Carlo*](https://arxiv.org/abs/1701.02434) is used as a foundational HMC
reference. Its lift--evolve--project correctness spine and the boundary between
invariance, convergence, and conceptual guidance are mapped in the
[foundation coverage note](docs/betancourt17-coverage.md).
Neal's [*MCMC using Hamiltonian
dynamics*](https://arxiv.org/abs/1206.1901) additionally informs the endpoint
Metropolis, momentum-transition, partial-refreshment, and windowed-HMC
boundaries recorded in its [foundation coverage note](docs/neal12-coverage.md).

## Current status

The repository now contains machine-checked implementations and proofs for:

- general-state Metropolis--Hastings, Gaussian RWMH, and coupled Gaussian
  RWMH as mathlib Markov kernels;
- a general lift--evolve--project invariance theorem for auxiliary-variable
  MCMC, including a deterministic measure-preserving-flow specialization;
- a phase-space lifting theorem for arbitrary invariant momentum transitions,
  with full independent refreshment as a specialization;
- finite-dimensional leapfrog dynamics and full multinomial HMC, including
  momentum refresh, randomized trajectory origin, multinomial selection, and
  target invariance;
- corrected relativistic and Riemannian momentum measures, the diagonal
  SoftAbs Hamiltonian and its derivatives, and endpoint and multinomial
  GR-HMC target-invariance theorems;
- maximal and optimal-transport trajectory-index couplings, with exact HMC
  marginals;
- a measurable finite optimal-transport selector with proved optimality;
- the coupled multinomial-HMC/Gaussian-RWMH mixture and its invariant
  single-chain marginal;
- exact-meeting and relaxed-meeting path events, drift interfaces, and
  geometric tail theorems;
- the finite lagged telescoping estimator, its exact marginal-expectation
  identity, and an infinite stopped estimator which is `L¹`, unbiased for
  bounded observables under kernel-level faithfulness, and in `L²` under a
  geometric meeting tail, together with finite expected correction count and
  almost-surely finite pathwise correction work, plus
  a stationary-start invariant-expectation specialization; a uniform
  higher-moment theorem also proves unbiasedness and finite variance for
  unbounded observables, while its stationary form requires only one
  target-space `MemLp` certificate;
- Xu et al.'s regularity and local-strong-convexity assumptions;
- compact-uniform exact-flow and leapfrog contraction estimates;
- total-variation and relative centered-energy estimates for multinomial
  trajectory weights;
- general `C²` locally uniform `o(|ε|)` control of the phase derivative of
  one leapfrog energy defect;
- cutoff-wise maximal-coupling contraction and one-step relaxed accessibility
  of the implemented shared-momentum HMC kernel;
- composition of that accessibility result with Xu's drift assumptions to
  obtain a geometric relaxed-meeting tail for the concrete HMC/RWMH mixture;
  and
- a finite-data `L²`-regularized logistic-regression potential with its exact
  leapfrog gradient, explicit global smoothness constant, strong convexity,
  and concrete coupled-HMC relaxed-accessibility window.

There is also a fully instantiated standard-Gaussian result in every nonempty
finite dimension: for the verified multinomial-HMC/Gaussian-RWMH mixture,
Lean proves a geometric exact lag-one meeting tail from deterministic
initialization. This includes a proved affine drift inequality for the actual
selected HMC transition at `ε = √2`, `L = 1`.
For bounded observables, a concrete wrapper additionally proves estimator
unbiasedness and finite variance conditional on the explicitly stated
Dirac-start marginal-expectation convergence obligation.

The finite-data `L²`-regularized logistic target is also fully instantiated:
at any cancellation step `ε²λ = 2` with `L = 1`, Lean proves HMC drift,
compact energy geometry, and a geometric exact lag-one meeting tail for the
concrete sticky HMC/RWMH mixture in every nonempty finite dimension.
It has the analogous bounded-observable estimator wrapper with marginal
expectation convergence left explicit.

### Executable finite MVP

The finite executable vertical slice is operational. Lean proves that the
cumulative natural-weight selector has exactly its normalized PMF and that the
two-state executable MH step has the same row PMF as the existing verified
finite MH kernel. A compiled Lean binary is the conformance oracle. Lean also
emits the production Julia core, which is exercised against the oracle on
every valid categorical and two-state MH trace.

The public Julia interface uses positional RNG dispatch:

```julia
using VerifiedSamplers, Random

target = FiniteWeights([1, 0, 2])
samples = sample(MersenneTwister(1), target, 100)
chain = sample(MersenneTwister(2), TwoStateMH(), false, 100)
```

The no-RNG methods delegate to `Random.default_rng()`. Julia indices are
one-based at the public categorical API; the generated core and Lean `Fin`
encoding are zero-based.

## What “HMC” means here

The paper's main results concern multinomial HMC. Accordingly, the formalized
transition contains:

1. Gaussian momentum refresh;
2. forward and backward leapfrog trajectory generation;
3. randomized placement of the current state in the trajectory; and
4. multinomial state selection using Hamiltonian weights.

Endpoint-only Metropolis HMC is a different comparison algorithm and is not
silently substituted for multinomial HMC.

The coupled HMC kernels are separately proved to have the verified
single-chain multinomial-HMC kernel as both marginals. Likewise, the coupled
RWMH kernel has the verified RWMH kernel as both marginals.

## Paper-statement audit

The README records only the headline qualifications. Each paper has a
consistently named coverage audit with the exact claims, Lean artifacts,
corrections, and remaining conditions.

### Xu et al. (2021): Couplings for Multinomial HMC

- Printed Condition 1 cannot hold on a nontrivial region under quantifiers
  reaching zero integration time; the proved replacement uses a positive
  integration-time window and, where needed, a fixed kinetic cutoff.
- The unconditional exponent-two contraction route is obstructed in the
  audited short-time regime; the completed meeting proof instead uses the
  repaired first-moment maximal-coupling route and an explicit drift premise.

See the [2021 coverage audit](docs/xu21-coverage.md) and
[2021 roadmap](docs/xu21-roadmap.md).

### Xu and Ge (2024): Relativistic Riemannian HMC

- Algorithm 1 needs `r^(d-1)`, a genuinely uniform spherical direction, and
  inverse-factor transport under the paper's factor convention.
- Equation (9) needs the momentum gradient and a corrected anisotropic bound.
- Momentum symmetry alone does not establish kernel validity.
- Six fixed-point iterations are only approximate in general; exact kernel
  correctness remains conditional on the explicit integrator certificate.

See the [2024 coverage audit](docs/xu24-coverage.md) and
[2024 roadmap](docs/xu24-roadmap.md).

## Main theorem boundary

The general theorem surface now has the following dependency chain:

```text
RegularPotential + LocalStrongConvexity
  → cutoff-wise maximal multinomial-HMC contraction
  → relaxed accessibility of the implemented coupled HMC kernel

XuTheorem41DriftAssumptions for the same selected HMC/RWMH kernels
  + relaxed accessibility
  → geometric relaxed-meeting tail for the concrete coupled mixture
```

The exact lag-one theorem uses the faithful sticky mixture and the localized
Gaussian-RWMH exact-meeting small set. Its abstract and finite-dimensional
standard-Gaussian forms are proved.

For a general target, the remaining analytic input is a compatible
Foster--Lyapunov drift certificate for at least one `ε,L` pair selected by the
local-convexity window. Such a drift condition is an explicit hypothesis of
the paper's meeting-time result; it does not follow from local strong
convexity alone. Higher-dimensional or non-Gaussian validated instances must
provide that target-specific drift analysis.

For regularized logistic regression, the local regularity, convexity, and HMC
accessibility obligations are proved. For the cancellation step size
`ε² λ = 2`, Lean also proves exact leapfrog position and momentum formulas
and a one-step Hamiltonian-defect envelope with the strict coercive term
`-(λ/8)‖q‖²`. The capped-retention envelope is integrated against refreshed
Gaussian momentum, yielding a finite explicit allowance and a strict affine
drift theorem for the actual `L = 1` multinomial-HMC kernel. The remaining
compact energy geometry is also proved, culminating in a fully instantiated
exact lag-one geometric meeting-tail theorem for the concrete sticky
regularized-logistic HMC/RWMH mixture in every nonempty finite dimension.

Floating-point refinement and reproduction of the paper's experiments are
separate goals and are not claimed as machine-checked results.

## Mathematical boundaries

These implications must not be conflated:

```text
kernel validity
  < target invariance
  < convergence from arbitrary initial states
  < geometric meeting tails
  < finite-variance unbiased estimation
```

Detailed balance implies invariance, not convergence. A coupled kernel having
the correct marginals does not imply that the chains meet. Geometric tails
require drift and small-set or accessibility arguments in addition to local
HMC contraction.

## Build

The repository pins Lean and mathlib. From the repository root:

```sh
cd formal
lake update
lake exe cache get
lake build
```

For a narrow check while editing the main analytic module:

```sh
cd formal
lake env lean Mcmc/Hamiltonian/LocalContractivity.lean
```

From the repository root, `make formal`, `make julia`, and `make test` provide
the corresponding aggregate entry points. `make oracle` compiles the Lean
conformance oracle, `make generate` explicitly regenerates the committed Julia
core, and `make check-generated` checks freshness without modifying the tree.
The [testing strategy](docs/testing.md) records the exact, differential,
statistical, and skeletoned future test layers.

## Repository guide

- [`formal/`](formal/): pinned Lean project containing the `Mcmc` library.
- [`VerifiedSamplers.jl/`](VerifiedSamplers.jl/): Julia package, with
  compiler-emitted generated code and maintained optimized code in separate
  internal submodules.
- [`docs/`](docs/): architecture notes, coverage audits, roadmaps, and the
  development log.

## License

See [`LICENSE`](LICENSE).
