# mcmc-lean

`mcmc-lean` formalizes Markov chain Monte Carlo algorithms and coupling
arguments in Lean 4 on mathlib's measure and `ProbabilityTheory.Kernel`
interfaces.

The main research target is Xu, Fjelde, Sutton, and Ge,
[“Couplings for Multinomial Hamiltonian Monte Carlo”](https://proceedings.mlr.press/v130/xu21i.html)
(AISTATS 2021). The development defines RWMH and multinomial HMC themselves;
they are not represented by opaque kernels assumed to be correct.

## Current status

The repository now contains machine-checked implementations and proofs for:

- general-state Metropolis--Hastings, Gaussian RWMH, and coupled Gaussian
  RWMH as mathlib Markov kernels;
- finite-dimensional leapfrog dynamics and full multinomial HMC, including
  momentum refresh, randomized trajectory origin, multinomial selection, and
  target invariance;
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
  of the implemented shared-momentum HMC kernel; and
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

The repository preserves an important distinction discovered during
formalization.

### Condition 1: contraction must use a positive window

Xu et al.'s printed Condition 1 requires one subunit contraction rate for all
sufficiently small trajectory lengths. Under the direct discrete
interpretation this includes `L = 0`, whose transition is the identity. Lean
proves that a set containing two distinct positions then forces the alleged
contraction rate to be at least one. Merely excluding `L = 0` is not enough if
the corresponding integration times may still approach zero: those
transitions approach the identity, so no single rate strictly below one can
hold uniformly.

The corrected statement uses a nondegenerate positive integration-time
window

```text
0 < T_min <= epsilon * L <= T_max
```

and asserts a subunit contraction rate only on that window.

The library therefore provides three explicit interfaces:

- the verbatim condition and its impossibility theorem;
- a positive-integration-window repair; and
- a cutoff-wise positive-window condition matching what compact local
  strong-convexity arguments actually prove.

The stronger repaired interface chooses one window and rate before every
kinetic cutoff. Compact local strong convexity does not automatically provide
that quantifier order. The cutoff-wise theorem instead fixes a positive
kinetic cutoff and then selects a positive window, rate, and numerical
threshold.

For the meeting-time argument, one cutoff is enough: Lean selects the
positive-mass event `K(p) ≤ 1`, integrates the conditional contraction through
Gaussian momentum refresh, and obtains the required one-step relaxed-entry
constant. Thus the general local-accessibility theorem does not assume the
stronger uniform-over-all-cutoffs condition. The implication for the paper is
that local strong convexity supports the needed contraction after fixing a
kinetic cutoff and selecting a nondegenerate time window, not uniformly over
arbitrarily short trajectories.

### Exponent-two contraction: the unconditional route is obstructed

The exponent-two optimal-transport condition has an additional limitation.
For the scalar standard Gaussian on `Set.univ` and windows containing short
times, Lean proves a first-order index-mass obstruction. Nearby chains can
select different multinomial trajectory indices with probability of first
order in their initial separation, whereas a squared-distance contraction
budget is only second order. Consequently, the paper's unconditional
exponent-two estimate is not established under those broad quantifiers.

The exponent-two theorems therefore remain conditional on an additional
contraction certificate. The proved replacement uses first-moment
(`p = 1`) maximal coupling, whose error budget has the correct order. This
replacement still supplies the local relaxed accessibility needed by the
geometric meeting-time argument. It does not show that the algorithm or the
meeting conclusion fails; it changes the hypotheses and proof route used to
justify that conclusion.

Finally, the global drift premise remains independent: it is not a consequence
of local strong convexity. With that drift premise supplied for the selected
HMC/RWMH kernels, the repaired first-moment accessibility route still yields
the paper's geometric meeting conclusion. Geometric meeting, in turn, should
not be described as marginal convergence from arbitrary initial states
without a separate ergodicity argument.

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
lake update
lake exe cache get
lake build
```

For a narrow check while editing the main analytic module:

```sh
lake env lean McmcLean/Hamiltonian/LocalContractivity.lean
```

## Repository guide

- [`McmcLean/Finite/`](McmcLean/Finite/): elementary finite kernels,
  couplings, transport, and finite-to-mathlib bridges.
- [`McmcLean/Kernel/`](McmcLean/Kernel/): general-state MH/RWMH, coupled
  kernels, path laws, meeting events, and drift machinery.
- [`McmcLean/Hamiltonian/Leapfrog.lean`](McmcLean/Hamiltonian/Leapfrog.lean):
  leapfrog definitions and deterministic identities.
- [`McmcLean/Hamiltonian/HMC.lean`](McmcLean/Hamiltonian/HMC.lean):
  phase- and position-space multinomial HMC and invariance.
- [`McmcLean/Hamiltonian/CoupledMultinomialHMC.lean`](McmcLean/Hamiltonian/CoupledMultinomialHMC.lean):
  coupled multinomial HMC with exact marginals.
- [`McmcLean/Hamiltonian/LocalContractivity.lean`](McmcLean/Hamiltonian/LocalContractivity.lean):
  Xu conditions, contraction estimates, numerical-error analysis, and
  kernel accessibility.
- [`McmcLean/Hamiltonian/CoupledMixture.lean`](McmcLean/Hamiltonian/CoupledMixture.lean):
  verified HMC/RWMH mixtures and geometric meeting-tail theorems.
- [`McmcLean/Hamiltonian/QuadraticGaussian.lean`](McmcLean/Hamiltonian/QuadraticGaussian.lean)
  and [`QuadraticGaussianXu.lean`](McmcLean/Hamiltonian/QuadraticGaussianXu.lean):
  validated Gaussian specializations.
- [`McmcLean/Hamiltonian/LogisticRegression.lean`](McmcLean/Hamiltonian/LogisticRegression.lean):
  verified regularized-logistic potential, gradient, paper assumptions, and
  local coupled-HMC accessibility.
- [`docs/roadmap.md`](docs/roadmap.md): dependency-ordered research roadmap.
- [`docs/paper-coverage.md`](docs/paper-coverage.md): claim-by-claim mapping
  from the paper's algorithms and Section 4 results to compiled Lean artifacts.
- [`docs/development-log.md`](docs/development-log.md): chronological proof
  milestones and limitations.
- [`docs/related-work.md`](docs/related-work.md): literature and architecture
  notes.

## License

See [`LICENSE`](LICENSE).
