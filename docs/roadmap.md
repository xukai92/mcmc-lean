# Roadmap

This document describes a dependency-ordered path from the repository's
current finite-state Metropolis--Hastings stationarity theorem to a reusable,
measure-theoretic Lean foundation for verifying MCMC algorithms. It is a
research roadmap, not a release schedule.

The roadmap is informed by the survey in [`related-work.md`](related-work.md)
and the repository's completed milestones in
[`development-log.md`](development-log.md). Its central organizing principle
is that several different claims are often called "MCMC correctness" and must
remain separate in the formal theorem surface.

## Roadmap status

- [x] **Baseline:** finite-state MH kernel, detailed balance, and stationarity
- [x] **Phase 1:** finite-to-mathlib interoperability
- [ ] **Next -- Phase 2:** mathlib-native kernel foundations
- [ ] **Planned -- Phase 3:** density-based measurable-state MH
- [ ] **Planned -- Phase 4:** finite specialization and API migration
- [ ] **Planned -- Phase 5:** Radon--Nikodym measurable-state MH
- [ ] **Planned -- Phase 6:** dynamics and convergence
- [ ] **Planned -- Phase 7:** reusable algorithms, execution, and trajectories
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

- Use mathlib's `Measure` and `ProbabilityTheory.Kernel` as the primary
  mathematical interface for all new reusable results.
- Use `PMF` as the mathlib-native frontend for finite or countable
  probabilistic programs, not as the foundation of the general-state theory.
- Freeze the current elementary finite layer as a transparent reference proof
  while the general theorem is developed; do not add substantial parallel
  dynamics or algorithm infrastructure to it.
- Derive finite MH correctness from the general theorem, prove
  theorem-for-theorem parity, and only then retire the local finite types from
  the public API.
- Reuse mathlib's kernel composition, powers, irreducibility, invariance,
  integration, and trajectory construction.
- Introduce abstractions only after at least two algorithms demonstrate the
  common interface they need.
- State positivity, support, irreducibility, aperiodicity, and measurability
  assumptions explicitly.
- Separate abstract kernel correctness from executable sampling and numeric
  approximation.
- Prefer quantitative statements when they do not substantially complicate
  the qualitative theorem.

## Phase 1: finite-to-mathlib interoperability

**Status:** Complete

The local finite types now interoperate with `PMF`, `Measure`,
`ProbabilityTheory.Kernel`, and `Matrix.rowStochastic`. Pointwise detailed
balance lifts to mathlib reversibility and invariance; the matrix and
measure-kernel views agree on singleton transition probabilities.

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

## Phase 2: mathlib-native kernel foundations

**Status:** Next

Establish the definitions needed to state MH directly for measurable spaces,
using mathlib rather than generalized versions of the local finite
structures. Suggested modules are:

```text
McmcLean/Kernel/DetailedBalance.lean
McmcLean/Kernel/AcceptedFlow.lean
```

The layer should:

- take a target `Measure State` with an explicit `IsProbabilityMeasure`
  assumption;
- take proposals and transitions as `ProbabilityTheory.Kernel State State`
  with explicit `IsMarkovKernel` assumptions;
- reuse `Kernel.IsReversible` and `Kernel.Invariant` rather than introduce
  competing predicates;
- define the forward joint proposal measure `pi(dx) Q(x,dy)` and its
  coordinate swap;
- collect the measurability lemmas needed for acceptance functions,
  off-diagonal moves, and rejection mass; and
- verify the definitions on at least one finite discrete space and one
  non-finite standard Borel space.

The completed one-step finite dynamics result remains available as a baseline,
but finite powers, reachability, and total variation are deferred until they
can be built on the mathlib-native kernel interface.

**Exit criterion:** detailed balance, invariance, accepted flow, and rejection
can be stated without the local `Finite.Distribution` or
`Finite.MarkovKernel` types, and the interface is sufficient to state the
general MH construction.

## Phase 3: density-based measurable-state MH

**Status:** Planned

Prove the first general-state MH correctness theorem under a common reference
measure. Suggested module:

```text
McmcLean/Kernel/MetropolisHastings/Density.lean
```

Assume measurable target and proposal densities with their normalization and
kernel measurability obligations stated explicitly. Define the acceptance
probability, accepted move kernel, rejection probability, and resulting MH
kernel. Prove:

- the construction is measurable and is a Markov kernel;
- the accepted flow is symmetric, including where either density vanishes;
- `Kernel.IsReversible` with respect to the target; and
- `Kernel.Invariant` via mathlib's reversibility theorem.

The first theorem may assume a normalized target density and proposal
densities relative to a common reference measure. Positivity must not be used
to conceal zero-density or asymmetric-support cases.

**Exit criterion:** a reusable mathlib `ProbabilityTheory.Kernel` MH theorem
proves invariance on both a finite discrete example and a meaningful
continuous example.

## Phase 4: finite specialization and API migration

**Status:** Planned

Specialize the general theorem to a finite type with its discrete measurable
structure. Use `PMF State` for finite targets and `State → PMF State` for
proposal programs, converting them to mathlib measures and kernels.

Before changing the public import surface, recover all current finite
guarantees:

- a valid MH transition kernel;
- accepted-flow and usual acceptance-ratio equivalence;
- pointwise detailed balance and stationarity as corollaries of the setwise
  results;
- zero forward or reverse proposal edge cases;
- agreement with `PMF.bind` and row-stochastic matrices where useful; and
- the existing two-state example.

Keep the elementary finite modules during this phase as a regression oracle.
Once theorem-for-theorem parity is established, move examples and downstream
work to the mathlib-native API, remove the local types from `McmcLean.lean`,
and either retain the elementary development in a clearly marked reference
namespace or remove it in a separate reviewed change.

**Exit criterion:** finite MH correctness is a specialization of the general
measure-theoretic theorem, all current public results have replacements, and
no public downstream module requires the local finite types.

## Phase 5: Radon--Nikodym measurable-state MH

**Status:** Planned

Generalize the density theorem using the forward joint proposal measure

```text
pi(dx) Q(x,dy)
```

and its coordinate-swapped counterpart. Define acceptance using an
appropriate Radon--Nikodym derivative or a symmetric dominating measure, then
prove that the construction agrees with the density-based theorem when common
densities exist.

This phase must state the absolute-continuity and measurability assumptions
precisely. It must also account for mutually singular components rather than
silently assigning a real-valued ratio at points where no pointwise density
exists.

**Exit criterion:** the MH invariance theorem is expressed intrinsically in
terms of measures and kernels and does not require a preselected common
reference measure.

## Phase 6: dynamics and convergence

**Status:** Planned

Develop dynamics using mathlib kernel composition and powers. Start with a
finite convergence theorem, where compact finite arguments give the clearest
first result, then isolate assumptions that extend to general spaces.

For finite kernels, prove convergence under a primitive-kernel hypothesis. A
preferred route is an elementary finite minorization and contraction argument:

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

**Intermediate milestone:** the project can accurately claim a generic
finite-state Markov-chain convergence theorem with explicit ergodicity
hypotheses and, preferably, a geometric bound.

Then specialize the generic finite convergence theory to MH. This requires:

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

**Exit criterion:** the mathlib-native MH invariance theorem has a convergence
corollary whose extra assumptions are explicit and mathematically sufficient;
the theorem states its initial distribution and mode of convergence.

## Phase 7: reusable algorithms, execution, and trajectories

**Status:** Planned

Add algorithms as instances of the mathlib-native kernel theory rather than as
self-contained finite proofs. Candidate constructions include:

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

For executable finite or countable algorithms, separate a `PMF`-valued
sampling step from its mathematical measure kernel. Suggested modules include:

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

**Exit criterion:** at least two algorithm families reuse the same kernel and
invariance APIs, and a theorem about an abstract kernel can be applied to the
law generated by a formally specified transition program.

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

1. **Kernel foundations:** introduce the mathlib-native target, proposal-joint-
   measure, and detailed-balance interfaces without depending on local finite
   definitions.
2. **Density construction:** construct the measurable accepted-move and
   rejection kernels from normalized densities and prove they form a Markov
   kernel.
3. **Density correctness:** prove reversibility and invariance, then instantiate
   the theorem on one continuous and one finite example.

After those changes, specialize the density theorem to the existing finite
examples and begin theorem-for-theorem API migration. The Radon--Nikodym
formulation follows without blocking retirement of the parallel local API. Do
not expand local finite powers, reachability, convergence, or additional
finite algorithms in parallel unless they are needed as a focused test of the
new interface.

## Scope boundaries

The following are intentionally not near-term claims:

- stationarity is not convergence;
- uniqueness of a stationary distribution is not by itself convergence;
- an abstract mathematical kernel theorem does not verify a floating-point
  implementation;
- exact independent-sampler correctness does not establish MCMC mixing; and
- a finite convergence theorem does not establish Harris recurrence on
  general state spaces.

Documentation and theorem names should continue to make these boundaries
visible as the library grows.
