# Roadmap

This document describes a dependency-ordered path from the repository's
current finite-state Metropolis--Hastings stationarity theorem to a reusable
Lean foundation for verifying MCMC algorithms. It is a research roadmap, not
a release schedule.

The roadmap is informed by the survey in [`related-work.md`](related-work.md)
and the repository's completed milestones in
[`development-log.md`](development-log.md). Its central organizing principle
is that several different claims are often called "MCMC correctness" and must
remain separate in the formal theorem surface.

## Roadmap status

- [x] **Baseline:** finite-state MH kernel, detailed balance, and stationarity
- [ ] **In progress -- Phase 1:** finite-to-mathlib interoperability
- [ ] **Planned -- Phase 2:** finite-chain dynamics
- [ ] **Planned -- Phase 3:** finite-state convergence
- [ ] **Planned -- Phase 4:** Metropolis--Hastings convergence
- [ ] **Planned -- Phase 5:** reusable finite MCMC constructions
- [ ] **Planned -- Phase 6:** executable refinement and trajectories
- [ ] **Planned -- Phase 7:** measurable-state kernels
- [ ] **Planned -- Phase 8:** quantitative and statistical theory

A phase is checked only when its exit criterion is satisfied. While a phase
is in progress, change its marker from **Planned** or **Next** to **In
progress** and add a short note here if needed. Detailed completed work remains
recorded in [`development-log.md`](development-log.md).

## Intended proof stack

A fully verified algorithm should eventually connect five layers:

1. an executable transition step realizes an abstract transition kernel;
2. the transition is a well-formed Markov kernel;
3. the target is invariant, often as a consequence of detailed balance;
4. explicit ergodicity assumptions imply convergence in a specified mode;
5. stronger assumptions give quantitative mixing or estimator guarantees.

The library should allow results at any one of these layers without requiring
all the stronger layers. In particular:

```text
detailed balance  ==>  stationarity
```

does not imply convergence from an arbitrary initial distribution. A theorem
should be described as a convergence theorem only when it states the required
ergodicity hypotheses and the mode of convergence.

## Current baseline

**Status:** Complete

The repository currently provides an elementary finite-state interface and a
Metropolis--Hastings construction. For a strictly positive finite target and
an arbitrary proposal kernel, it proves:

- nonnegativity and normalization of the MH transition;
- equivalence of the symmetric accepted-flow and acceptance-ratio formulas;
- detailed balance with respect to the target; and
- stationarity of the target.

The accepted-flow identity

```text
min (pi(x) * q(x,y)) (pi(y) * q(y,x))
```

should remain the algebraic core of finite MH proofs, including cases with a
zero forward or reverse proposal probability.

## Design principles

- Keep the current elementary finite layer as a transparent reference proof.
- Add bridges to mathlib instead of replacing working local definitions
  prematurely.
- Reuse mathlib's stochastic matrices, kernel composition, irreducibility,
  PMFs, measures, and trajectory construction.
- Introduce abstractions only after at least two algorithms demonstrate the
  common interface they need.
- State positivity, support, irreducibility, aperiodicity, and measurability
  assumptions explicitly.
- Separate abstract kernel correctness from executable sampling and numeric
  approximation.
- Prefer quantitative statements when they do not substantially complicate
  the qualitative theorem.

## Phase 1: finite-to-mathlib interoperability

**Status:** In progress

The PMF, measure, and `ProbabilityTheory.Kernel` bridge is complete. The
stochastic-matrix bridge remains before this phase's exit criterion is met.

Add a module such as `McmcLean/Finite/MeasureKernel.lean` that relates the
elementary finite structures to:

- `PMF` and `Measure`;
- `Matrix State State Real` and `Matrix.rowStochastic`; and
- `ProbabilityTheory.Kernel` on a discrete measurable space.

The bridge should prove that singleton probabilities agree and that:

- local stationarity corresponds to mathlib kernel invariance;
- local detailed balance implies `Kernel.IsReversible`; and
- the existing MH result therefore produces a mathlib-invariant probability
  measure.

This phase should not introduce measure theory into the definitions in
`Finite/MarkovKernel.lean`.

**Exit criterion:** an elementary finite kernel can be used by mathlib's
kernel-composition, kernel-power, irreducibility, and trajectory APIs without
reproving its one-step correctness.

## Phase 2: finite-chain dynamics

**Status:** Planned

Develop reusable dynamics in modules such as:

```text
McmcLean/Finite/Dynamics.lean
McmcLean/Finite/Irreducible.lean
McmcLean/Finite/TotalVariation.lean
```

The layer should include:

- evolution of an initial distribution by a transition kernel;
- kernel and matrix powers;
- finite Chapman--Kolmogorov identities;
- preservation of stationarity under powers;
- reachability through positive transition probabilities;
- bridges to `Matrix.IsIrreducible`, `Matrix.IsPrimitive`, and
  `Kernel.IsIrreducible`; and
- finite total-variation distance, with its equivalent half-L1 formula.

**Exit criterion:** finite multi-step questions can be expressed without
unfolding the MH construction, and matrix and measure formulations are linked
by named lemmas.

## Phase 3: finite-state convergence

**Status:** Planned

Prove the first finite convergence theorem under a primitive-kernel
hypothesis. A preferred route is an elementary finite minorization and
contraction argument:

1. a strictly positive power gives a uniform positive lower bound;
2. the lower bound yields contraction in total variation;
3. iteration yields an explicit geometric estimate; and
4. the estimate yields convergence and uniqueness of the stationary
   distribution.

The main statement should identify both its initial distribution and its mode
of convergence, for example:

```text
primitive P + stationary pi
  ==> P^n evolves every initial distribution to pi in total variation
```

Then prove user-facing sufficient conditions, initially:

```text
irreducible + positive diagonal  ==>  primitive  ==>  convergence
```

A general finite period/GCD interface can be added after this first useful
aperiodicity theorem.

**Exit criterion:** the project can accurately claim a finite-state MCMC
convergence theorem with explicit ergodicity hypotheses and, preferably, a
geometric bound.

## Phase 4: Metropolis--Hastings convergence

**Status:** Planned

Lift the generic finite convergence theory back to MH. This requires:

- an accepted-flow graph for the MH transition;
- usable sufficient conditions for its strong connectivity;
- proofs relating accepted-flow connectivity to MH irreducibility;
- support lemmas for asymmetric and zero proposal probabilities; and
- a generic lazy-kernel construction

```text
lazy(P) = (1 / 2) I + (1 / 2) P.
```

Laziness should be proved to preserve stationarity and reversibility while
providing positive diagonal entries. The resulting flagship theorem should
state that an irreducible lazy finite MH chain converges to its target in total
variation.

Proposal irreducibility alone must not be used as an MH irreducibility
hypothesis: a positive forward proposal with zero reverse proposal can have
zero accepted flow.

The strictly positive target assumption can later be relaxed by restricting
the chain to the target's support. Zero target mass should not be hidden by
real division conventions.

**Exit criterion:** the existing MH stationarity theorem has a convergence
corollary whose extra assumptions are explicit and mathematically sufficient.

## Phase 5: reusable finite MCMC constructions

**Status:** Planned

Add algorithms as instances of the generic finite theory rather than as
self-contained proofs. Candidate modules, in approximate dependency order,
are:

1. lazy kernels, mixtures, and compositions of invariant kernels;
2. independence Metropolis--Hastings;
3. random-walk Metropolis on finite graphs;
4. finite Gibbs and random-scan Gibbs;
5. component-wise or block Metropolis--Hastings; and
6. examples exercising asymmetric and partially supported proposals.

Each algorithm should expose, as applicable:

```text
kernel
kernel_isMarkov
reversible or invariant
irreducible conditions
convergence
quantitative bound
```

This phase should also determine whether a common construction record is
useful. Non-reversible invariant kernels must remain representable even though
reversibility is the main proof technique for MH and Gibbs.

Simulated annealing should come later: it is time-inhomogeneous and does not
fit an ordinary stationary-kernel theorem without additional theory.

**Exit criterion:** at least two algorithm families reuse the same dynamics
and convergence APIs without duplicating essential Markov-chain arguments.

## Phase 6: executable refinement and trajectories

**Status:** Planned

Separate an executable sampling step from its mathematical kernel. Suggested
modules include:

```text
McmcLean/Execution/Step.lean
McmcLean/Execution/Trajectory.lean
```

For finite MH, define a `PMF`-valued proposal and accept/reject program, then
prove that its output law equals the abstract MH transition. This proof should
account explicitly for proposal generation, uniform randomness, acceptance
comparison, and rejection.

Use mathlib's Ionescu--Tulcea infrastructure to connect repeated kernel steps
to a law on trajectories. Keep this refinement boundary independent of a
particular code generator or runtime until a concrete extraction target is
chosen.

**Exit criterion:** a theorem about an abstract finite kernel can be applied
to the distribution generated by a formally specified transition program.

## Phase 7: measurable-state kernels

**Status:** Planned

Begin the general-state layer only after the finite interfaces have stabilized.
Suggested modules are:

```text
McmcLean/Kernel/DetailedBalance.lean
McmcLean/Kernel/MetropolisHastings/Density.lean
McmcLean/Kernel/MetropolisHastings/RadonNikodym.lean
```

Proceed in two stages:

1. a density-based MH theorem relative to a common reference measure, with
   all measurability and integrability assumptions stated explicitly; and
2. a Radon--Nikodym formulation based on the joint proposal measure
   `pi(dx) Q(x,dy)` and its coordinate-swapped counterpart.

The first deliverable in this layer is construction of a measurable Markov
kernel plus detailed balance and invariance. It is not yet a general-state
convergence theorem.

**Exit criterion:** a reusable mathlib `ProbabilityTheory.Kernel` MH theorem
proves invariance on a meaningful class of non-finite state spaces.

## Phase 8: quantitative and statistical theory

**Status:** Planned

Longer-term research directions include:

- coupling inequalities and coupling-based mixing bounds;
- minorization, small sets, and drift conditions;
- geometric and subgeometric ergodicity;
- Wasserstein contraction;
- perturbation bounds for approximate or floating-point kernels;
- laws of large numbers for MCMC averages;
- central limit theorems and asymptotic variance; and
- adaptive or time-inhomogeneous MCMC.

These should be split into independent milestones. Harris recurrence, MCMC
CLTs, and floating-point refinement are substantial formalization projects,
not prerequisites for a useful finite algorithm library.

## Immediate implementation sequence

The next three coherent code changes should be:

1. **Finite measure-kernel bridge:** conversions and the
   reversibility/invariance correspondence.
2. **Finite dynamics:** evolution, powers, matrix views, and stationarity
   under iteration.
3. **Finite total variation and convergence:** contraction lemmas followed by
   the primitive-kernel convergence theorem.

After those changes, the first end-to-end demonstration should prove total-
variation convergence of an irreducible lazy version of the existing finite
MH construction. That result will exercise every foundational seam before the
library expands to more algorithms or measurable state spaces.

## Scope boundaries

The following are intentionally not near-term claims:

- stationarity is not convergence;
- uniqueness of a stationary distribution is not by itself convergence;
- an abstract real-valued kernel theorem does not verify a floating-point
  implementation;
- exact independent-sampler correctness does not establish MCMC mixing; and
- a finite convergence theorem does not establish Harris recurrence on
  general state spaces.

Documentation and theorem names should continue to make these boundaries
visible as the library grows.
