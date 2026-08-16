# Ge, Xu, and Ghahramani (2018) coverage audit

This audit covers [*Turing: A Language for Flexible Probabilistic
Inference*](https://proceedings.mlr.press/v84/ge18b.html). The paper is a
probabilistic-programming systems and empirical paper, not a theorem paper.
Accordingly, this project separates kernel-correctness statements from
implementation features and experiments.

## Formalizable mathematical core

| Paper item | Repository evidence | Classification |
|---|---|---|
| A probabilistic model defines a posterior target over global and local variables | `Mcmc.Finite.ProbabilisticProgram.Model` gives finite `assume`/`observe` factor semantics, evidence, and a normalized posterior; `CoroutineState` gives one-observation suspend/resume semantics and refines completed traces; the general-state `Measure` layer supplies the continuous target | Machine checked for finite traces and arbitrary pause boundaries; Julia mirrors the cursor as explicit copyable data rather than copying opaque `Task` stacks |
| MCMC engines act on manually selected subsets of variables | `Mcmc.Finite.ComposableInference.ScopedOperator` records scope metadata and the induced full-state kernel | Machine checked at the finite kernel level |
| Selected subsets may overlap and their union should cover the model variables | `Covers` records union coverage; `schedule_stationary` deliberately needs neither coverage nor disjointness | Corrected separation: coverage is an inference-configuration condition, while stationarity follows from preservation by every full-state operator |
| Operators can be composed into a Gibbs-style schedule | `schedule` and `schedule_stationary` prove that every finite schedule of common-target-stationary operators preserves the target | Machine checked |
| A runtime engine executes scoped operators in user-specified order | Lean-generated IR version 12 includes a coverage-checked PG--HMC schedule descriptor; Julia `generated_schedule`, `ScopedInferenceOperator`, and `ComposableSampler` preserve its names, scopes, and ordering | Executable metadata refinement; target correctness remains conditional on matching each named callback to its proved full-state kernel |
| Particle Gibbs can update latent/discrete variables and HMC can update differentiable continuous variables | `pgHmcKernel` and `pgHmcKernel_stationary` formalize the two-block pattern in Equations (7)--(8) through explicit slice-preservation hypotheses; `Mcmc.Examples.ComposableInference` gives a nonidentity two-block finite instance | Machine checked at the finite product-state level; the example deliberately does not call a finite refresh transition numerical HMC |
| PG, PMMH, and SMC are available component engines | Finite SMC, concrete conditional SMC, PIMH, state-indexed PMMH, and particle Gibbs are proved in the particle-MCMC layer; Julia exposes an exact-integer finite-HMM PG runner | Machine checked for fixed finite state, horizon, and particle count; PG execution is differentially tested |
| HMC/NUTS is not directly applicable to discrete variables | The current HMC interfaces act on Euclidean coordinates; no claim is made that ordinary gradient HMC updates discrete coordinates | Scope restriction, not a universal impossibility theorem |
| Candidate-based trajectory selection preserves a target | `candidateMixture_stationary` handles state-independent mixtures; `dynamicCandidateKernel_stationary` handles target-weighted state-dependent sets; `CertifiedDynamicTree` derives its premises directly from completed candidate finsets | Machine checked static and dynamic structural cores, including variable-depth stopped doubling components; a numerical U-turn builder must refine the completed-tree certificate |

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

For particle-count consistency, the exact one-step resample--propagate MSE is
now complemented by a checked self-normalized-ratio perturbation bound and a
finite-horizon affine error recursion.  Consequently a concrete sequential
client can obtain fixed-horizon `O(1/N)` control by supplying normalizer lower
bounds and stagewise stability constants.  Uniform-in-time consistency still
needs a strict stability argument.

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
- runtime constrained-variable transformations that have not been matched to
  an explicit pushed-measure/Jacobian theorem;
- the reported NUTS versus `Gibbs(PG, NUTS)` traces and mode exploration; and
- the illustrative Turing/Stan timings, which the paper itself says are not
  serious benchmarks.

These belong in executable regression tests, reproducible experiments, or
future compiler/refinement layers. In particular, the figures show behavior
for specific models and configurations; they do not prove universal mixing or
efficiency dominance.

The mathematical constrained-coordinate foundation is now explicit.
`transformedKernel_invariant` conjugates an unconstrained kernel by a measurable
equivalence and transports invariance from the pushed target measure back to
the constrained target. The standard positive-real log/exp equivalence is
instantiated. Any Jacobian belongs in the density identification of that pushed
measure; the theorem does not permit silently reusing the untransformed density.
Generated Julia transforms and their floating-point refinement remain runtime
work. A public `PositiveTransformedRWMH` runtime client now implements the
standard log transform, including the required `+y` log-Jacobian, validates
the positive domain, and has reproducible exponential-target diagnostics.
Connecting its `Float64` `log`/`exp` calls to the exact conjugation theorem
remains the numerical boundary.

## Remaining milestones

1. Extend the concrete model library beyond the completed dependent sign-region
   client. `Examples.GeneralStatePgHmc` deterministically augments a Gaussian
   position by its Boolean sign region, constructs the reverse half-line
   conditional by standard-Borel disintegration, and composes that exact
   two-block update with the actual Gaussian SoftAbs multinomial GR-HMC
   transition. A multivariate likelihood model would be the next richer
   example, not a missing foundation theorem.
2. Complete runtime callback refinement beyond the new checked semantic
   binding. `ComposableSemantics.BoundOperator` now pairs every generated
   descriptor with its actual full-state kernel and invariance proof, and
   `BoundSchedule.kernel_invariant` proves that descriptor-ordered execution
   preserves the target. Julia callback equality with those bound kernels
   remains an explicit language-boundary obligation.
3. The numerical U-turn-to-certificate connection is complete for two safe
   canonical-orbit builders.
   `CertifiedDynamicTree` now expresses root inclusion and exact reroot equality
   directly in terms of generated candidate `Finset`s and automatically yields
   detailed balance and stationarity. `StoppedDoublingLeaf` instantiates
   variable stopped depths with `2^depth` leaf indices and proves stationarity
   of target-weighted selection from each completed component. The connected
   builders are adjacent endpoint barriers and a
   conservative all-scales detector that checks every endpoint pair spanning
   each split. Both have Lean stationarity theorems and Julia implementations.
   Equivalence to the usual root-dependent recursive first-stop NUTS algorithm
   remains intentionally unclaimed.
4. Extend generated trace-state descriptions if richer source programs need
   them. Julia now uses an explicit, copyable `ObservationCursor` matching the
   proved finite suspend/resume state and tests pause/copy/resume against
   uninterrupted execution. It deliberately does not copy opaque Julia
   `Task` stacks; all resumable state is represented as ordinary data.
5. Keep the stochastic-volatility, Gaussian-mixture, AD, and runtime results
   as reproducible empirical suites rather than paper-wide theorems.
