# Neal (2012) foundation coverage

This note maps Radford Neal's [*MCMC using Hamiltonian
dynamics*](https://arxiv.org/abs/1206.1901) to the reusable Lean foundations.
The chapter reviews basic endpoint HMC and several variants; it is not treated
as one monolithic theorem target.

## Basic HMC correctness

Neal separates an HMC iteration into momentum refreshment and a
Metropolis-corrected numerical trajectory. The repository reflects that
factorization:

- `McmcLean.Hamiltonian.momentumTransition_invariant` lifts any invariant
  momentum kernel to an invariant phase-space transition. Full independent
  refreshment is its constant-kernel specialization.
- `McmcLean.Kernel.deterministicMetropolis_invariant` proves correctness of an
  endpoint proposal from measurability, involutivity, reference-volume
  preservation, and the exact target weight.
- `McmcLean.Kernel.liftEvolveProject_invariant` then transports phase-space
  invariance to the position target.

The endpoint theorem captures Neal's use of a momentum flip to make a
reversible leapfrog proposal. Leapfrog volume preservation and reversibility
are proved separately rather than inferred from approximate energy
conservation.

Neal also observes that the dynamics used to construct a proposal may use an
approximate Hamiltonian, provided the proposal remains reversible and volume
preserving and acceptance uses the exact target Hamiltonian. The generic
deterministic-Metropolis interface already keeps the proposal map and target
weight separate, so it supports this distinction.

## Variants and missing specializations

### Partial momentum refreshment

Equation (5.19) uses the Gaussian AR(1) update
`p' = α p + sqrt (1 - α²) n`. The new `momentumTransition` abstraction is the
required phase-space foundation: once this AR(1) kernel is proved to preserve
the chosen Gaussian momentum law, its phase-target invariance follows
immediately. The concrete finite-dimensional Gaussian AR(1) kernel and its
invariance proof remain to be added.

Neal emphasizes that composing individually reversible transitions need not
produce a reversible transition, although invariance is preserved. The library
therefore uses invariance, not reversibility, as the composition contract for
generalized HMC.

### Windowed selection

The randomized-origin, canonical-weight selection argument underlying the
repository's multinomial HMC is formalized by
`McmcLean.Kernel.orbitMultinomialKernel`. It is closely related to Neal's
windowed trajectory reasoning and streaming weighted selection. Neal's exact
two-window accept/reject construction is not currently exposed as its own
kernel, so no equivalence with that algorithm is claimed.

### Random trajectory parameters and ergodicity

The chapter gives periodic trajectories as a concrete reason fixed leapfrog
lengths can fail to be ergodic and recommends randomizing the step size or
number of steps. This supports adding invariant mixtures over trajectory
parameters, but randomization alone must not be advertised as a general
convergence theorem. Irreducibility, aperiodicity, recurrence or drift, and a
mode of convergence still require explicit hypotheses.

Short-cut trajectories, tempered trajectories, and adaptive tuning require
additional symmetry or non-homogeneous-chain foundations and are not implied
by the current HMC correctness theorems.
