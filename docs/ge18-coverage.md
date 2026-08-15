# Ge, Xu, and Ghahramani (2018) coverage audit

This audit covers [*Turing: A Language for Flexible Probabilistic
Inference*](https://proceedings.mlr.press/v84/ge18b.html). The paper is a
probabilistic-programming systems and empirical paper, not a theorem paper.
Accordingly, this project separates kernel-correctness statements from
implementation features and experiments.

## Formalizable mathematical core

| Paper item | Repository evidence | Classification |
|---|---|---|
| A probabilistic model defines a posterior target over global and local variables | `Mcmc.Finite.ProbabilisticProgram.Model` gives finite `assume`/`observe` factor semantics, evidence, and a normalized posterior; `CoroutineState` gives one-observation suspend/resume semantics and refines completed traces; the general-state `Measure` layer supplies the continuous target | Machine checked for finite traces and arbitrary pause boundaries; Julia task/copying refinement remains implementation work |
| MCMC engines act on manually selected subsets of variables | `Mcmc.Finite.ComposableInference.ScopedOperator` records scope metadata and the induced full-state kernel | Machine checked at the finite kernel level |
| Selected subsets may overlap and their union should cover the model variables | `Covers` records union coverage; `schedule_stationary` deliberately needs neither coverage nor disjointness | Corrected separation: coverage is an inference-configuration condition, while stationarity follows from preservation by every full-state operator |
| Operators can be composed into a Gibbs-style schedule | `schedule` and `schedule_stationary` prove that every finite schedule of common-target-stationary operators preserves the target | Machine checked |
| A runtime engine executes scoped operators in user-specified order | Julia `ScopedInferenceOperator` and `ComposableSampler`, with coverage and ordering tests | Executable; its target correctness is conditional on matching each callback to a proved full-state kernel |
| Particle Gibbs can update latent/discrete variables and HMC can update differentiable continuous variables | `pgHmcKernel` and `pgHmcKernel_stationary` formalize the two-block pattern in Equations (7)--(8) through explicit slice-preservation hypotheses; `Mcmc.Examples.ComposableInference` gives a nonidentity two-block finite instance | Machine checked at the finite product-state level; the example deliberately does not call a finite refresh transition numerical HMC |
| PG, PMMH, and SMC are available component engines | Finite SMC, concrete conditional SMC, PIMH, state-indexed PMMH, and particle Gibbs are proved in the particle-MCMC layer; Julia exposes an exact-integer finite-HMM PG runner | Machine checked for fixed finite state, horizon, and particle count; PG execution is differentially tested |
| HMC/NUTS is not directly applicable to discrete variables | The current HMC interfaces act on Euclidean coordinates; no claim is made that ordinary gradient HMC updates discrete coordinates | Scope restriction, not a universal impossibility theorem |
| Candidate-based trajectory selection preserves a target | `candidateMixture_stationary` proves this for state-independent selection among common-target stationary kernels | Machine checked sufficient condition; intentionally not a theorem about dynamically stopped NUTS trees |

The important correction is that a declared variable scope does not itself
justify an update. Each component must induce a Markov kernel on the complete
state and preserve the same joint target. Once those premises hold, overlap is
harmless for stationarity and finite sequential composition is exact.

## Particle-Gibbs boundary

The repository now proves exact conditional SMC and particle-Gibbs
stationarity. It also proves `particleGibbsKernel_unit_eq_identity`: with one
particle, PG is exactly the identity transition. Thus the paper's practical PG
claims cannot be strengthened to particle-count-uniform mixing without further
hypotheses. At zero horizon, however, the state kernel is proved exactly equal
to `N⁻¹ I + (1-N⁻¹) Π`; its total-variation error after `k` iterations is
exactly `N⁻ᵏ` times the initial error. Thus every `N ≥ 2` converges
geometrically in this specialization, while `N = 1` remains the identity.
For positive horizons, a count-indexed `Fin N` theorem now derives a uniform
geometric TV rate from an explicit pointwise bounded-model minorization and
proves that its displayed refresh coefficient improves monotonically with
`N`. Deriving that minorization from primitive potential and transition bounds
for each concrete conditional-SMC generator remains model-specific.

The executable `FiniteHMMParticleGibbs` mirrors this finite bootstrap case
with integer weights and explicit RNG consumption. Reference and Optimized
implementations agree under deterministic trace replay, and the public API
uses positional RNG dispatch. This executable agreement does not replace the
formal stationarity theorem or establish convergence from arbitrary paths.

## Implementation and empirical claims

The following are not promoted to mathematical theorems:

- coroutine-based storage and copying of probabilistic-program states;
- forward- versus reverse-mode automatic-differentiation performance;
- vectorized random-variable speedups;
- constrained-variable transformations without an explicit Jacobian theorem;
- the reported NUTS versus `Gibbs(PG, NUTS)` traces and mode exploration; and
- the illustrative Turing/Stan timings, which the paper itself says are not
  serious benchmarks.

These belong in executable regression tests, reproducible experiments, or
future compiler/refinement layers. In particular, the figures show behavior
for specific models and configurations; they do not prove universal mixing or
efficiency dominance.

## Remaining milestones

1. Instantiate the proved general-state `pgHmcKernel_stationary` theorem with a
   substantive mixed discrete/continuous model. The measure-kernel composition
   and auxiliary conditional factorization are complete; only the concrete
   model client remains.
2. Connect the executable blocked-engine callbacks to generated descriptions
   of the corresponding formal full-state kernels.
3. Extend the proved static candidate-mixture condition to dynamically grown,
   symmetrically stopped NUTS trees before using NUTS as a verified component.
4. Connect the proved finite suspend/resume semantics to Julia task copying and
   generated trace-state descriptions; the mathematical arbitrary-pause
   refinement to completed traces is now machine checked.
5. Keep the stochastic-volatility, Gaussian-mixture, AD, and runtime results
   as reproducible empirical suites rather than paper-wide theorems.
