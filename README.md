# verified-samplers

**[Documentation](https://xukai92.github.io/mcmc-lean/)**

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

The [overall project roadmap](docs/project-roadmap.md) integrates these paper
targets with executable work and the broader
[algorithm scope review](docs/algorithm-scope-review.md). Finite Gibbs,
two-temperature tempering, finite pseudo-marginal MH, executable Xu et al.
coupling, and general-state MALA correctness are complete. A bounded-weight
independence-MH minorization, exact regenerative representation, and explicit
`(1 - 1 / M)^n` eventwise convergence bound are also proved. The pre-Xu
foundation also has a finite adaptive-MCMC counterexample: state-dependent
selection can destroy stationarity even when every frozen kernel preserves
the target. A finite-horizon homogeneous Feynman--Kac/SMC expectation theorem
and its time-inhomogeneous finite-sequence extension are also complete. The
finite law is now realized over explicit ancestry and population histories and
feeds an exact pseudo-marginal client whose complete fixed-horizon schedule may
depend on the proposed state. A history-weighted uniformly selected terminal
particle is also proved to have the normalized Feynman--Kac terminal marginal;
stored ancestry now extracts a correctly sized full genealogy with proved
initial/terminal endpoints. Its full path-observable many-to-one law, complete
particle MCMC, and corrected Xu--Ge execution remain.

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
- general-state independence MH with the classical bounded-density-ratio
  `1 / M` target minorization, exact Doeblin residual decomposition, and
  two-sided eventwise convergence rate `(1 - 1 / M)^n` for `M > 1`;
- finite-dimensional state-dependent Gaussian proposals, with ULA proved
  Markov but not target-exact and MALA proved reversible and target-invariant;
- general-state two-block auxiliary Gibbs/data augmentation, including a
  slice-sampling interface whose correctness is reduced to an explicit
  vertical/horizontal joint-factorization equation;
- a concrete measurable vertical slice-height Markov kernel and proof that
  its lifted weighted target is exactly Lebesgue measure under the target
  graph; horizontal level-set disintegration remains explicit;
- tagged two-model reversible-jump MH with a common reference measure,
  transport-density certificate, cross-model accepted-flow symmetry, and
  Markov/reversibility/invariance theorems;
- finite iid particle clouds whose average nonnegative importance weight is
  proved unbiased, together with the resulting pseudo-marginal MH extended
  stationarity and exact target marginal;
- unbiased multinomial ancestor resampling, heterogeneous propagation, and a
  one-step bootstrap resample--propagate expectation identity, lifted to an
  arbitrary finite-horizon homogeneous Feynman--Kac expectation theorem for
  strictly positive potentials and to time-varying finite sequences;
- a normalized finite distribution over complete SMC population/ancestry
  histories, an exact product-weight expectation theorem, and the resulting
  explicit-history pseudo-marginal kernel with exact stationary state marginal,
  including state-indexed potentials and transitions at a common horizon;
- the normalized history-weighted selected-particle target and exact
  observable/eventwise identification of its Feynman--Kac terminal marginal;
- backward tracing through stored ancestor maps, producing a selected genealogy
  of the correct length with machine-checked initial and terminal endpoints;
- reusable finite identity, composition, mixture, and coordinate-lift
  combinators; finite one-site, random-scan, and systematic-scan Gibbs;
- finite state-dependent kernel selection and a checked counterexample showing
  that common invariance of all frozen kernels does not imply invariance after
  state-dependent selection;
- two-temperature parallel tempering with an MH-corrected swap, product-target
  stationarity, and an exact cold-marginal theorem;
- finite pseudo-marginal MH with a nonnegative unbiased estimator, including
  zero estimator values, exact extended-target stationarity, and the desired
  target marginal;
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

### Executable finite samplers

The finite executable vertical slice is operational. Lean proves that the
cumulative natural-weight selector has exactly its normalized PMF. For any
strictly positive target weights and positive-total proposal rows on `Fin n`,
Lean proves that the generic executable MH step has the same row PMF as the
existing verified finite MH kernel, including asymmetric and zero proposal
edges. A compiled Lean binary is the conformance oracle. Lean also emits the
versioned sampler IR consumed by the maintained Julia reference interpreter,
which is exercised against the oracle and an independent optimized
implementation on exhaustive small finite traces. Universal trace-refinement
theorems prove that the Lean IR interpreter agrees with the established
categorical and MH replay semantics for every valid finite configuration and
trace.

The public Julia interface uses positional RNG dispatch:

```julia
using VerifiedSamplers, Random

target = FiniteWeights([1, 0, 2])
samples = sample(MersenneTwister(1), target, 100)
chain = sample(MersenneTwister(2), TwoStateMH(), false, 100)

proposal = FiniteKernelWeights([
    [1, 2, 1],
    [1, 1, 1],
    [0, 2, 1],
])
sampler = FiniteMH(FiniteWeights([1, 2, 3]), proposal)
generic_chain = sample(MersenneTwister(3), sampler, 1, 100)
```

The no-RNG methods delegate to `Random.default_rng()`. Julia indices are
one-based at the public categorical API; the reference interpreter and Lean `Fin`
encoding are zero-based.

### Continuous executable boundary

The continuous executable layer uses typed ideal primitives for bounded
natural draws, a standard normal, and a unit uniform. Lean identifies the
standard-normal denotation with mathlib's exact Gaussian density measure and
validates kind-tagged mathematical traces. The versioned sampler artifact now
contains an inspectable Gaussian RWMH program interpreted by Julia Reference;
Optimized remains an independent tested `Float64` implementation:

```julia
sampler = GaussianRWMH(x -> -x^2 / 2, 1.0)
chain = sample(MersenneTwister(4), sampler, 0.0, 10_000)
```

The typed first-order Lean IR now has exact kernel and trace interpretations,
and the canonical scalar program is proved to have the full
proposal/accept-or-retain trace behavior for arbitrary real log densities and
scales. For measurable log densities and positive scales, its exact kernel
semantics equals the existing verified Gaussian RWMH construction and preserves
the density `exp ∘ logdensity`; explicit normalization makes that target a
stationary probability measure. Public Julia sampling routes through the
serialized IR interpreter. No theorem equates its finite-precision law with
the exact Lean kernel; the explicit boundary is deliberate:
mathlib `ℝ`, `gaussianReal`, and `Measure` are semantic objects, whereas Julia
uses `Float64` and the selected `AbstractRNG` implementation.

Lean records the missing backend theorem as
`NumericalRefinement`: an explicit hypothesis-bearing contract with no Julia
or Float64 witness. Thus downstream work can name the deferred obligation
without silently assuming that it has already been proved.

Lean now also provides a bounded refinement layer. It composes absolute error
bounds for the affine proposal, callback log ratio, clamping, exponential
threshold, and uniform draw. The Float64 and ideal executions provably take
the same branch whenever the ideal uniform-to-threshold margin exceeds the
combined threshold and uniform errors; any branch disagreement is confined to
that explicit boundary band. Concrete Julia/libm/RNG error certificates are
still inputs to this theorem rather than assumed facts.

| Layer | Current guarantee |
|---|---|
| Ideal trace | Proved for arbitrary scalar log densities and real scales |
| Exact kernel | Proved for measurable log densities and positive scales |
| Stationarity | Proved for the normalized `exp ∘ logdensity` target |
| Julia Reference | Interprets the committed version-9 sampler IR |
| Julia Optimized | Independently implemented and differentially tested |
| Bounded numeric refinement | Proved composition and decision-stability theorems, conditional on concrete operation-error certificates |
| Julia execution certificates | Per-run checked RWMH/HMC decision witnesses with explicit callback, libm, and RNG bounds |
| Universal Float64/RNG theorem | Not claimed; still requires a formal Julia/LLVM/libm/RNG semantics and callback specifications |

See the [continuous executable contract](docs/continuous-executable-contract.md)
for the exact theorem and runtime boundaries, and the
[executable roadmap](docs/executable-roadmap.md) for prioritized next steps.

The executable HMC slice is also operational: scalar and vector-valued, unit-mass,
endpoint-corrected HMC with any positive finite number of leapfrog steps. Lean
proves its ideal trace formula, identifies its deterministic update with the
established `leapfrogN` map for every trajectory length, and proves exact
phase-volume preservation and Boltzmann-target invariance of the corresponding
phase kernel. The complete refresh–evolve–project position kernel is also
defined and proved invariant for every compatible position target. The
version-9 artifact is interpreted by Julia Reference and
differentially tested against Optimized, including energy, reversibility,
numerical-volume, Gaussian-moment, and non-Gaussian quartic-moment tests:

```julia
sampler = ScalarHMC(x -> -x^4 / 4, x -> x^3, 0.15, 6)
chain = sample(MersenneTwister(7), sampler, 0.0, 10_000)

vector_sampler = VectorHMC(q -> -sum(abs2, q) / 2, identity, 0.18, 6)
# Columns are successive two-dimensional states.
vector_chain = sample(MersenneTwister(8), vector_sampler, [0.0, 0.0], 10_000)
```

The vector program draws one normal momentum per coordinate and is generated
from the typed Lean command IR. Lean proves that its list-valued integrator is
extensionally the existing `Position (Fin n)` leapfrog map, and the generic
exact endpoint kernel is invariant in every finite dimension. Reference and
Optimized agree on fixed traces, and the public sampler is tested on a
two-dimensional Gaussian.

Constant-metric execution is also available through `MetricHMC` with either
`DiagonalMetric` or symmetric positive-definite `DenseMetric`:

```julia
Σ = [1.0 0.8; 0.8 2.0]
precision = inv(Σ)
sampler = MetricHMC(q -> -dot(q, precision * q) / 2,
    q -> precision * q, DenseMetric(Σ), 0.15, 6)
chain = sample(MersenneTwister(9), sampler, zeros(2), 10_000)
```

Lean defines the corresponding diagonal and dense inverse-mass velocity maps,
proves exact time reversal, endpoint-proposal involution, phase-volume
preservation, Boltzmann phase invariance, and refreshed position invariance.
The version-9 artifact retains the type-indexed diagonal and dense commands
introduced in version 6, so Julia Reference executes both through the
generated IR. Lean also proves the
linear/Cholesky Gaussian pushforward law and its determinant-normalized
quadratic kinetic density using mathlib's matrix change-of-variables theorem.

The Xu et al. coupled HMC/RWMH mixture is exposed through the version-9 IR:

```julia
sampler = Xu21CoupledSampler(q -> -sum(abs2, q) / 2, identity,
    0.15, 4, 0.6, 0.9)
coupled = sample(MersenneTwister(21), sampler,
    ([0.0, 0.0], [2.0, -1.0]), 1_000)
findfirst(coupled.met)
```

The interpreter uses shared momentum and trajectory origin, maximal coupling
of multinomial indices, maximal Gaussian proposals, shared accept/reject
uniforms, and a shared mixture decision. Lean proves that the ideal command
has the verified single-chain mixture on both marginals; `met` records exact
replay-level equality. As elsewhere, concrete Float64 execution is separated
from the ideal-real theorem by the numerical-refinement boundary.

Backend-facing Lean certificates now compose proposal, callback, endpoint
energy, `exp`, and RNG bounds into the RWMH/HMC decision-stability theorems.
Julia exposes matching per-run checked witnesses through
`VerifiedSamplers.Certificates`. These certify branch agreement only when the
supplied ideal values and primitive bounds are valid and the comparison lies
outside their uncertainty band; they are not a universal proof of arbitrary
Julia callbacks or platform `libm` behavior.

Executable randomized-origin multinomial HMC is available separately from
endpoint-corrected HMC:

```julia
sampler = MultinomialHMC(q -> -sum(abs2, q) / 2, identity, 0.2, 6)
chain = sample(MersenneTwister(10), sampler, zeros(2), 10_000)
```

Lean proves that the ideal origin/index choice program has exactly the
existing `randomizedMultinomialLeapfrogPMF` law, identifies its measure with
the verified kernel row, and assigns the complete refresh–evolve–project
command the proved invariant position kernel. Julia Reference interprets the
generated version-9 command; Optimized independently builds the re-rooted
trajectory. Float64 Boltzmann weights and categorical boundary decisions
retain the explicit numerical-refinement qualification.

The same algorithm is available with diagonal or dense constant metrics via
`MetricMultinomialHMC`. Lean proves orbit-kernel phase and refreshed-position
invariance, including the Cholesky-refreshed specialization. The artifact
contains separate metric-kind-correct commands.

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
reference IR artifact consumed by the maintained Julia interpreter,
and `make check-generated` checks freshness without modifying the tree.
`make docs` regenerates the Lean-owned architecture graphs and builds the
Documenter site locally in `docs/build/`; `make check-docs-generated` verifies
that the committed graph page is current.
The [testing strategy](docs/testing.md) records the exact, differential,
statistical, and skeletoned future test layers.

## Repository guide

- [`formal/`](formal/): pinned Lean project containing the `Mcmc` library.
- [`VerifiedSamplers.jl/`](VerifiedSamplers.jl/): Julia package, with
  interpreted reference and maintained optimized implementations in separate
  internal submodules.
- [`docs/`](docs/): architecture notes, coverage audits, roadmaps, and the
  development log.

## License

See [`LICENSE`](LICENSE).
