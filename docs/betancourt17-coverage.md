# Betancourt (2017) foundation coverage

This note maps Michael Betancourt's [*A Conceptual Introduction to
Hamiltonian Monte Carlo*](https://arxiv.org/abs/1701.02434) to reusable Lean
foundations. The paper is a conceptual review, not a paper whose every
geometric or empirical discussion is intended as a formal theorem.

## Correctness spine

The paper's ideal HMC transition has three stages: sample momentum to lift a
position into phase space, evolve under Hamiltonian flow, and discard momentum.
`Mcmc.Kernel.liftEvolveProject_invariant` now formalizes the abstract
measure-theoretic argument. Its hypotheses deliberately expose all three
obligations:

1. the lift maps the position target to the phase target;
2. the phase-space evolution preserves the phase target; and
3. projection maps the phase target back to the position target.

`liftDeterministicProject_invariant` specializes the evolution to a measurable
measure-preserving map, matching ideal Hamiltonian flow.
`compProdEvolveFst_invariant` specializes the lift to a conditional auxiliary
kernel and discharges the canonical product-measure and projection equations.
`Mcmc.Hamiltonian.positionMultinomialHMC_invariant` is an instance of the general
theorem, with randomized leapfrog trajectory selection as the invariant
phase-space evolution. The endpoint and multinomial GR-HMC position theorems
use the conditional-kernel specialization for their position-dependent
momentum laws.

For numerical HMC, the repository separately proves the ingredients emphasized
by the paper:

- `formal/Mcmc/Hamiltonian/VolumePreservation.lean` proves phase-volume preservation for
  leapfrog steps and their iterates;
- `formal/Mcmc/Hamiltonian/RandomizedTrajectory.lean` implements random trajectory origin;
- `formal/Mcmc/Hamiltonian/Multinomial.lean` implements canonical-density-weighted state
  selection; and
- `formal/Mcmc/Hamiltonian/Invariance.lean` proves invariance of the resulting corrected
  phase-space transition.

This matches the static trajectory construction in Appendix A.2 rather than
silently treating an approximate numerical trajectory as exact Hamiltonian
flow.

## Claim boundary

The paper repeatedly qualifies its invariance and asymptotic discussion with
regularity or ergodicity conditions. Accordingly:

- invariance of a one-step kernel is not described here as convergence from an
  arbitrary initial distribution;
- central-limit, geometric-ergodicity, and effective-sample-size conclusions
  require additional hypotheses not supplied by the lift--evolve--project
  theorem; and
- typical-set geometry, tuning guidance, divergences, and efficiency
  comparisons remain conceptual or diagnostic material unless separately
  stated as mathematical claims with explicit assumptions.

The paper's progressive sampling construction in Appendix A.3 is not yet a
separate public abstraction. The current finite trajectory selector proves the
needed normalized categorical selection directly; a generic progressive
mixture theorem should be added only when a downstream algorithm needs it.
