# Roadmap

This is the dependency-ordered plan for formalizing Xu, Fjelde, Sutton, and
Ge, [“Couplings for Multinomial Hamiltonian Monte Carlo”](https://proceedings.mlr.press/v130/xu21i.html)
(AISTATS 2021). It records current proof boundaries rather than every
historical intermediate lemma.

## Target theorem surface

The project aims to machine-check:

1. the RWMH and multinomial-HMC algorithms used by the paper;
2. their coupled versions and exact marginal identities;
3. local contraction of coupled Hamiltonian trajectories;
4. multinomial-weight and coupling-cost bounds;
5. relaxed and exact meeting mechanisms;
6. Xu's drift-to-geometric-meeting argument; and
7. representative fully instantiated targets.

The algorithms are part of the theorem, not unexplained kernel assumptions.
Experimental comparisons and floating-point implementations are separate
goals.

See [`paper-coverage.md`](paper-coverage.md) for the claim-by-claim audit of
Algorithms 1--6 and the Section 4 theorem chain.

## Completed foundations

### Measure-theoretic kernels

- General-state Metropolis--Hastings is defined with mathlib measures and
  kernels and proved Markov, reversible, and invariant.
- Gaussian RWMH and its coupled proposal/acceptance construction are proved
  kernels with exact marginals.
- Finite-state definitions interoperate with mathlib PMFs, measures, and
  kernels.
- Coupled-chain path laws, exact and lag-one meeting events, small sets,
  drift predicates, and geometric tail recurrences are formalized.

### Multinomial HMC

- Leapfrog is defined on finite-dimensional phase space with reversibility,
  volume preservation, stability, and deterministic error identities.
- The full multinomial-HMC transition includes momentum refresh, randomized
  trajectory origin, and conditional Boltzmann index selection.
- Phase- and position-space HMC kernels are proved Markov and target
  invariant.
- Shared-momentum maximal and transport trajectory couplings have the exact
  single-chain HMC marginals.

### Finite transport

- Maximal categorical coupling and finite transport costs are formalized.
- A measurable greedy finite selector is proved to have correct marginals and
  globally minimal squared cost.
- The selector lifts to an implemented transport-HMC coupling kernel.

### Coupled mixture

- The verified HMC and Gaussian-RWMH kernels are combined into the paper's
  single-chain mixture.
- The coupled mixture has that verified mixture as both marginals.
- A faithful sticky version preserves exact meetings.
- Localized Gaussian-RWMH minorization supplies positive exact-meeting small
  sets on compact paired regions.

## Completed Xu analysis

### Assumptions and exact flow

- `RegularPotential` formalizes the paper's global `C²` and Lipschitz-gradient
  assumption.
- `LocalStrongConvexity` formalizes strong monotonicity on a compact region.
- Exact Hamiltonian curves exist, and compact families have explicit
  containment and contraction horizons.

### Leapfrog and trajectory weights

- Leapfrog-versus-flow position error and phase stability are controlled on
  bounded horizons.
- Aligned trajectory costs have overlap-weighted contraction estimates.
- Total variation of trajectory-index laws is bounded through centered
  Hamiltonian defects.
- For every `RegularPotential`, the phase derivative of one leapfrog energy
  defect is uniformly `o(|ε|)` on bounded phase families. This closes the
  general relative numerical-error argument after fixed-horizon telescoping.

### Local coupled-HMC accessibility

- At every fixed kinetic cutoff, compact local strong convexity yields a
  positive integration window and a subunit maximal-coupling first-moment
  contraction rate.
- This bound holds for the actual randomized-origin maximal coupled kernel.
- Selecting the positive-mass momentum event `K(p) ≤ 1` and applying the
  first-moment Markov inequality proves one-step relaxed accessibility for the
  implemented shared-momentum maximal HMC kernel.

### Meeting tails

- `XuTheorem41DriftAssumptions` records the paper's HMC drift, RWMH growth,
  level-set geometry, initialization, and scalar conditions.
- Those assumptions imply geometric relaxed-meeting tails once local HMC
  accessibility is available.
- Local strong convexity is now composed with this theorem for the exact
  verified HMC/RWMH kernels and their concrete coupled mixture.
- Compact exact-meeting minorization plus faithfulness gives geometric exact
  lag-one meeting tails for the sticky mixture.
- A standard-Gaussian specialization in every nonempty finite dimension
  proves all required drift and geometric premises for the explicit
  `ε = √2`, `L = 1` multinomial-HMC transition.

## Statement corrections and limitations

### Printed Condition 1

The direct discrete reading of the paper's Condition 1 includes `L = 0` among
all sufficiently small trajectory lengths. This is the identity transition,
so any nontrivial state set forces the contraction rate to be at least one.
The impossibility theorem is formalized.

The library retains the printed condition but uses explicit repaired
interfaces for nontrivial results:

- a positive-integration-window condition;
- a stronger window and rate uniform over all kinetic cutoffs; and
- a cutoff-wise positive-window condition.

Compact local strong convexity proves the cutoff-wise version. The stronger
uniform-over-cutoffs version remains a valid optional hypothesis but is not
silently inferred. The meeting proof needs only one positive-mass cutoff, so
the cutoff-wise route suffices for local accessibility.

### Optimal-transport route

The finite transport implementation and all kernel bridges are complete.
However, the paper-style exponent-two contraction certificate is not an
unconditional Gaussian theorem. In the scalar standard-Gaussian case on
`Set.univ`, Lean proves a short-time index-mass obstruction for relevant
windows. Conditional exponent-two implications remain available and are
labelled accordingly.

### General drift

Regularity and local strong convexity do not by themselves imply the global
Foster--Lyapunov drift condition used by Theorem 4.1. The general composition
therefore takes a `XuTheorem41DriftAssumptions` certificate for the same
selected `ε,L` HMC/RWMH kernels.

The finite-dimensional standard-Gaussian family supplies such certificates.
Additional target families require target-specific drift proofs.

## Follow-on work outside the target theorem surface

### Priority 1: additional validated targets

- Extend the fully instantiated regularized-logistic exact-tail theorem beyond
  its proved cancellation-step `L = 1` parameter family. The current theorem
  includes global HMC drift, compact energy geometry, concrete HMC/RWMH
  kernels and couplings, and the final exact lag-one geometric meeting tail.
- Instantiate another controlled non-Gaussian target under explicit
  coercivity and moment assumptions.
- Relate selected local-contraction windows to practical HMC parameter
  families without weakening theorem hypotheses.

### Priority 2: theorem-surface consolidation

- Prove concrete marginal convergence from the Dirac starts used by the
  fully instantiated Gaussian and regularized-logistic meeting-tail theorems,
  or state an appropriately justified ergodicity premise in their estimator
  wrappers. Stationary higher moments now require only `MemLp h p target`.

- Add concise public wrappers for the most important general and instantiated
  results.
- Reduce legacy conditional interfaces where a stronger proved theorem now
  subsumes them, while preserving useful diagnostic counterexamples.
- Keep `README.md`, this roadmap, and the chronological development log
  synchronized with the compiled theorem surface.

### Priority 3: optional extensions

- Investigate global curvature or coercivity hypotheses that imply the
  stronger cutoff-uniform positive-window condition.
- Characterize parameter regimes where the exponent-two transport route is
  genuinely contractive.
- Refine the mathematical kernels to executable or floating-point
  implementations with verified numerical error.
- Extend the proved higher-moment finite-variance and expected-correction
  conclusions to the paper's fuller runtime-cost formulation.

## Validation gates

For every code change:

```sh
lake env lean <changed-module>
lake build
git diff --check
```

No theorem may be completed with `sorry`, `admit`, an axiom, or a disabled
linter workaround. Documentation must distinguish kernel validity,
invariance, local contraction, relaxed meeting, exact meeting, and convergence
from arbitrary initial states.
