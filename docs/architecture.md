# Formalization architecture

This document shows how the formalization is layered from mathlib's
measure-theoretic foundations through the implemented RWMH and multinomial-HMC
algorithms to the main meeting result of Xu, Fjelde, Sutton, and Ge.

## End-to-end dependency graph

```mermaid
flowchart TB
  subgraph Mathlib[mathlib measure theory]
    Measure[Measure α<br/>integration, products, pushforwards, densities]
    Kernel[Kernel α β<br/>state-dependent measures and composition]
    Gaussian[Gaussian measures]
    Invariance[Detailed balance and invariance infrastructure]
  end

  subgraph Generic[Generic MCMC and coupling layer]
    MH[General-state Metropolis--Hastings]
    Coupling[Kernel couplings<br/>proved left and right marginals]
    Paths[Coupled-chain path laws]
    Meeting[Meeting events, drift, and geometric tails]
  end

  subgraph RWMH[RWMH branch]
    RWProposal[Gaussian random-walk proposal]
    RWKernel[Gaussian RWMH kernel]
    CoupledProposal[Coupled Gaussian proposals]
    CoupledRWMH[Coupled RWMH<br/>shared accept/reject decision]
    ExactMeeting[RWMH exact-meeting small set]
  end

  subgraph HMC[Multinomial-HMC branch]
    Potential[Potential U and gradient ∇U]
    Leapfrog[Leapfrog dynamics]
    Trajectory[Randomized finite trajectory]
    Multinomial[Hamiltonian multinomial weights]
    Momentum[Gaussian momentum refresh]
    HMCKernel[Multinomial-HMC kernel]
    HMCInvariant[Target invariance]
    IndexCoupling[Coupled trajectory-index selection<br/>maximal p=1; conditional transport p=2]
    CoupledHMC[Coupled HMC<br/>proved HMC marginals]
    Accessibility[Local relaxed accessibility]
  end

  subgraph Xu[Xu et al. theorem layer]
    Mixture[Sticky coupled HMC/RWMH mixture]
    Drift[Global Foster--Lyapunov drift premise]
    Theorem41[Geometric exact lag-one meeting tail<br/>Theorem 4.1]
    Estimator[Unbiased-estimator consequences<br/>under stated convergence and moment inputs]
  end

  Measure --> Kernel
  Measure --> MH
  Kernel --> MH
  Kernel --> Coupling
  Kernel --> Paths
  Invariance --> MH
  Gaussian --> RWProposal
  Gaussian --> Momentum

  MH --> RWKernel
  RWProposal --> RWKernel
  RWKernel --> CoupledRWMH
  Coupling --> CoupledProposal
  CoupledProposal --> CoupledRWMH
  CoupledRWMH --> ExactMeeting

  Potential --> Leapfrog
  Leapfrog --> Trajectory
  Trajectory --> Multinomial
  Momentum --> HMCKernel
  Multinomial --> HMCKernel
  HMCKernel --> HMCInvariant
  Invariance --> HMCInvariant
  Coupling --> IndexCoupling
  Multinomial --> IndexCoupling
  IndexCoupling --> CoupledHMC
  Momentum --> CoupledHMC
  CoupledHMC --> Accessibility

  Paths --> Meeting
  Meeting --> Theorem41
  CoupledHMC --> Mixture
  CoupledRWMH --> Mixture
  Mixture --> Theorem41
  Accessibility --> Theorem41
  ExactMeeting --> Theorem41
  Drift --> Theorem41
  Theorem41 --> Estimator
```

The two algorithm branches are concrete: RWMH and multinomial HMC are defined
as mathlib kernels and proved correct before they are used in the coupled
mixture. The final theorem does not assume opaque single-chain algorithms.

## Where the finite layer fits

The chain state and momentum spaces are continuous, but a multinomial-HMC
transition selects from a finite leapfrog trajectory. Finite probability and
transport are therefore an internal component of the general-state kernel,
not a restriction of the final theorem to finite state spaces.

```mermaid
flowchart LR
  Continuous[Continuous position and momentum]
  FiniteTrajectory[Finite trajectory indices<br/>from 0 through L]
  IndexLaw[Finite multinomial distributions]
  FiniteCoupling[Finite maximal or transport coupling]
  Output[Continuous coupled output positions]

  Continuous --> FiniteTrajectory --> IndexLaw --> FiniteCoupling --> Output
```

The reusable finite coupling and transport definitions live under
`McmcLean/Finite/`. Their measurable kernel lifts connect finite index
couplings back to the continuous phase-space kernels.

## Logical boundary of the main theorem

The important implication structure is

```text
regularity + local strong convexity
  -> cutoff-wise positive-window HMC contraction
  -> local relaxed accessibility

local relaxed accessibility
  + RWMH exact-meeting small set
  + global drift for the selected HMC/RWMH kernels
  -> geometric exact lag-one meeting tail
```

Local strong convexity does not imply the global drift premise. Geometric
meeting also does not, by itself, prove marginal convergence from arbitrary
initial states. Those obligations remain explicit at theorem endpoints.

## Main module map

- `McmcLean/Kernel/MetropolisHastings.lean` defines general-state MH.
- `McmcLean/Kernel/RandomWalkMetropolisHastings.lean` specializes it to
  Gaussian RWMH.
- `McmcLean/Kernel/CoupledMetropolisHastings.lean` constructs coupled MH with
  proved marginals.
- `McmcLean/Hamiltonian/Leapfrog.lean` defines the deterministic integrator.
- `McmcLean/Hamiltonian/MultinomialHMC.lean` constructs the multinomial-HMC
  transition.
- `McmcLean/Hamiltonian/Invariance.lean` proves its invariance properties.
- `McmcLean/Hamiltonian/CoupledMultinomialHMC.lean` constructs coupled HMC with
  proved marginals.
- `McmcLean/Hamiltonian/LocalContractivity.lean` connects the repaired Xu
  conditions to local accessibility.
- `McmcLean/Kernel/MeetingDrift.lean` contains the abstract drift and meeting
  machinery.
- `McmcLean/Hamiltonian/CoupledMixture.lean` assembles the concrete mixture and
  Xu-style geometric meeting theorem.
- `McmcLean/Kernel/UnbiasedEstimator.lean` develops downstream estimator
  consequences.

See [`xu21-coverage.md`](xu21-coverage.md) for the claim-by-claim
correspondence with the 2021 paper.
