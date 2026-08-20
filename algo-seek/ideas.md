# Algorithm-seeking notebook

This note records candidate sampler ideas before implementation. Claims of
novelty are provisional until the related-work audit is complete. The primary
goal is practical benefit per unit of computation; formalization should make
the resulting algorithm trustworthy rather than serve as its only motivation.

See the [hierarchical-refinement HMC
roadmap](idea-hierarchical-refinement-hmc.md) for a comparison of the formal
and executable work required for DR-G-HMC, ATLAS, and the proposed hierarchical
refinement sampler.

## Evaluation principles

A candidate should identify:

- a concrete target pathology or workload;
- a baseline it is intended to improve upon;
- the computational resource being reused or saved;
- an exact transition rule, including failure behavior; and
- an empirical metric such as effective samples per gradient evaluation or
  per second, not merely acceptance probability.

Stationarity alone is not evidence of practical improvement. Multiproposal
methods in particular must account for all proposal, gradient, synchronization,
and selection costs.

## Lead idea: Multi-Scale Reuse HMC

### Intended benefit

Use large leapfrog steps in benign regions while refining only difficult
trajectory segments. Reuse the coarse computation and retain useful states
from both coarse and refined paths. The intended result is lower sensitivity
to a globally chosen step size and fewer wasted trajectories on targets with
spatially varying curvature.

Potential target classes include funnels, hierarchical models, anisotropic
posteriors, and distributions containing localized regions of high curvature.

### Provisional transition

1. Refresh momentum and construct an aggressive coarse leapfrog trajectory.
2. Compute a local diagnostic on each segment, initially an energy-error or
   curvature-change threshold.
3. Replace flagged segments by two half steps, recursively up to a fixed
   refinement depth.
4. Retain candidates from the coarse and refined levels in a finite trajectory
   network.
5. Select an output using an exactly corrected endpoint or multinomial rule.
6. Use a defined identity or coarser-level fallback if construction or a
   certificate fails.

The smallest prototype uses step sizes `epsilon` and `epsilon / 2`, a fixed
integration-time budget, one refinement level, and scalar energy-error
triggering.

### Practical hypotheses to test

- Refinement is sparse enough that it costs less than globally using the
  smallest step size.
- Coarse gradient evaluations or states can actually be reused by refined
  branches rather than merely recomputed.
- Candidate recycling improves movement when the aggressive endpoint would
  otherwise be rejected.
- Branching or batching maps efficiently to CPU SIMD, threads, or accelerators.
- Any selection correction does not erase the gain by overwhelmingly choosing
  the current or fine-path state.

### Initial baselines

- fixed-step endpoint HMC;
- multinomial HMC;
- NUTS;
- delayed-rejection HMC/GHMC;
- locally adaptive HMC such as ATLAS; and
- globally small-step HMC at a matched divergence rate.

### Key unresolved design questions

- Can a state-triggered refinement rule be made exactly reversible without
  rebuilding the full candidate network from every possible root?
- Which computations are genuinely shared between coarse and fine leapfrog
  paths?
- Should coarse nodes remain selectable after their segments are refined?
- Is correction best expressed through multinomial rerooting, delayed
  rejection, an extended-state involution, or an MH correction on the entire
  generated network?
- Should refinement respond to energy error, local Hessian information,
  force variation, or a cheap embedded-integrator estimate?

## Other algorithm ideas

### Equivariant proposal-network sampler

Generate a random finite network using heterogeneous reversible
transformations, such as several integration scales or dynamics. Require the
network law to transform equivariantly when rerooted at an admitted candidate,
then select using target weights.

The practical case requires shared computation or heterogeneous moves that a
single trajectory cannot provide. A deterministic reroot-invariant candidate
graph alone is already close to machinery present in this repository and to
general multiproposal MCMC.

### Coupling-aware HMC

Select trajectories jointly for two chains to maximize contraction or exact
meeting while preserving each chain's intended HMC marginal. The benefit is
shorter meeting times and more efficient unbiased MCMC estimators, rather than
necessarily better ordinary single-chain sampling.

### Global-local portfolio sampler

Combine local HMC with tempered, independence, or learned mode-jump moves. Use
an exact mixture or extended-state correction. The intended benefit is more
reliable movement between separated modes while retaining efficient local
exploration.

This direction must state its mode-discovery assumptions and compare against
parallel tempering and modern adaptive multimodal samplers.

### Failure-recycling HMC

When a long or aggressive HMC trajectory diverges or is rejected, reuse its
valid prefix, a shorter endpoint, or a refined retry instead of discarding all
work. The intended benefit is robustness and less wasted gradient computation.

This overlaps delayed rejection, extra-chance HMC, windowed HMC, and
multinomial trajectory selection; a new version needs a distinct reuse rule or
cost advantage.

### Self-certifying locally adaptive HMC

Use a locally chosen step size, metric, or approximate implicit integrator,
but expose numerical reversibility, solver, or trajectory checks as part of
the transition. Failed checks take a safe fallback. The intended benefit is
access to aggressive local geometry adaptation without silent numerical
invalidity.

### Multi-scale global-local variant

Use the multi-scale refinement mechanism for local motion and occasionally
seed coarse branches with tempered or mode-oriented transformations. This is a
longer-term synthesis, not the first prototype.

## Current repository fit

Reusable ingredients already include fixed and randomized HMC schedules,
leapfrog permutations, randomized-origin multinomial trajectories,
reroot-invariant dynamic candidates, checked dynamic trees, parameter
mixtures, numerical certificates, and Julia Reference/Optimized HMC paths.

The apparent missing ingredient is an exact semantic treatment of a
coarse/fine trajectory hierarchy whose refinement decisions depend on the
realized path and whose computation is reused by an executable implementation.

## Research status

The fine-grained search below was performed on 2026-08-20. It covered adaptive
and variable-step HMC, delayed rejection, generalized HMC, trajectory
recycling, compressible HMC, multirate integration, and coarse/fine or local
trajectory refinement. It used arXiv, PMLR, Project Euclid, journal pages, and
forward/backward terminology searches. A negative search result is evidence
about the public literature found, not proof that no equivalent method exists.

## Related-work audit for Multi-Scale Reuse HMC

### Very close work

#### Delayed-rejection HMC

Modi, Barnett, and Carpenter propose retrying a rejected HMC trajectory with
geometrically smaller step sizes. They target precisely the global-step-size
failure on multiscale distributions and report improvements in effective
sample size per gradient evaluation. The smaller step size is used over a
complete retried trajectory, so computation from the original trajectory is
largely discarded.

- Paper: [Delayed rejection Hamiltonian Monte Carlo for sampling multiscale
  distributions](https://doi.org/10.1214/23-BA1360)
- Preprint: <https://arxiv.org/abs/2110.00610>

This substantially overlaps the proposed failure-recycling variant and the
idea of retrying with `epsilon / 2`. Those pieces are not novel by themselves.

#### Delayed-rejection generalized HMC

Turok, Modi, and Carpenter's DR-G-HMC uses persistent momentum and normally
attempts one leapfrog step per Markov transition. After a rejection it retries
that step with a geometrically smaller step size. The resulting stochastic
trajectory uses large steps in flat regions and small steps only where needed,
avoiding DR-HMC's globally fine retry.

- Paper: [Sampling From Multiscale Densities With Delayed Rejection
  Generalized Hamiltonian Monte Carlo](https://proceedings.mlr.press/v258/turok25a.html)
- Updated preprint: <https://arxiv.org/abs/2406.02741>

This work already establishes the broad practical claim originally proposed
for Multi-Scale Reuse HMC. It is the closest baseline and means that “locally
use smaller steps only in difficult regions” is not a novelty claim.

The remaining distinction is that DR-G-HMC makes a corrected Markov decision
after each individual leapfrog step. It does not appear to construct one long
coarse trajectory, refine selected interior segments, and select jointly from
a retained coarse/fine hierarchy.

#### ATLAS

ATLAS estimates local curvature from positions and gradients along a short
trajectory, constructs a local step-size distribution, adapts trajectory
length with a no-U-turn rule, and uses delayed rejection. Its implementation
reuses positions and gradients from a rejected trajectory when estimating the
local Hessian. It also evaluates reverse construction and rejects incompatible
forward/reverse branches.

- Preprint and supplementary algorithms: <https://arxiv.org/abs/2410.21587>

ATLAS therefore overlaps local diagnostics, reuse of failed work, local step
size selection, and branch-aware correction. The proposed method would need to
reuse work *inside the accepted trajectory representation*, rather than only
using previous work to choose the parameters of a fresh trajectory.

### Other important precedents

#### Adaptive reversible integrators

Okudo and Suzuki give an explicit, reversible, volume-preserving adaptive
step-size method for HMC. Earlier numerical-analysis work also develops
reversible variable-step strategies and warns that naive state-dependent step
selection destroys the favorable structure of symplectic methods.

- [Hamiltonian Monte Carlo with explicit, reversible, and volume-preserving
  adaptive step size control](https://doi.org/10.14495/jsiaml.9.33)
- [Reversible long-term integration with variable
  stepsizes](https://doi.org/10.1137/S1064827595285494)

Consequently, variable step size or reversible local error control alone is
not new. A segment-refinement rule must be compared with these integrators on
cost, stability, and ease of implementation.

#### Variable-length compressible HMC

Nishimura and Dunson develop acceptance mechanisms for reversible,
non-volume-preserving dynamics, variable integration time, variable-step
integrators, and avoiding wasted unstable trajectories.

- [Variable length trajectory compressible hybrid Monte
  Carlo](https://arxiv.org/abs/1604.00889)

This is a broad correction framework that could subsume some adaptive
integrator designs. Any proposal-network correction should be checked against
its extended-state and Jacobian treatment.

#### Recycling intermediate trajectory states

Nishimura and Dunson recycle intermediate states from HMC and NUTS trajectories
with essentially no additional gradient cost.

- [Recycling Intermediate Steps to Improve Hamiltonian Monte
  Carlo](https://arxiv.org/abs/1511.06925)

Retaining coarse or intermediate candidates is therefore not novel alone. The
distinct question is whether candidates from multiple resolution levels can be
combined with sparse refinement and an efficient exact selection rule.

#### Windowed, short-cut, and multirate HMC

Neal's review describes windowed acceptance, short-cut trajectories that stop
wasting computation when integration behaves badly, and multiple time-scale
integrators. Multiple-time-scale HMC is especially established when the
Hamiltonian decomposes into force terms that can be evaluated at different
frequencies. That is different from spatially refining arbitrary trajectory
segments, but it occupies adjacent terminology.

- [MCMC using Hamiltonian dynamics](https://arxiv.org/abs/1206.1901)

### Computation-reuse reality check

A coarse leapfrog step and two half steps share the starting force evaluation,
but their endpoints generally differ. The coarse endpoint force is therefore
not automatically reusable as the fine endpoint force. Sparse refinement can
still save work relative to globally fine integration, but the prototype must
count exact force evaluations and should not assume full nesting of leapfrog
computations.

The coarse result can serve as an embedded error estimate or remain a proposal
candidate. Whether retaining it helps after exact correction is an empirical
question.

## Provisional novelty assessment

The original broad Multi-Scale Reuse HMC pitch is **not novel**: DR-G-HMC
already adapts step size locally along a persistent Hamiltonian trajectory,
and ATLAS combines local curvature estimation, delayed rejection, trajectory
adaptation, and reuse of rejected gradients.

The narrower concept below was **not found as an explicit algorithm in this
search**:

> Construct a long, directed HMC proposal as a bounded coarse trajectory;
> refine only flagged interior segments into a coarse/fine hierarchy; retain
> useful states at multiple resolutions; and make one exact selection from the
> resulting hierarchy while accounting for the path-dependent refinement law.

This is only a plausible gap, not yet a novelty claim. Its useful distinction
from DR-G-HMC would be preservation of long-trajectory proposals and joint
candidate selection, rather than a Metropolis decision after every single
step. Its distinction from ATLAS would be refinement within one proposal
network rather than using a diagnostic trajectory to parameterize another.

### Go/no-go questions before formalization

1. Can the refined hierarchy be generated reversibly without expensive ghost
   reconstruction from every candidate?
2. Does it use fewer gradients than DR-G-HMC and globally fine NUTS at matched
   sampling quality?
3. Does one long corrected selection preserve more directed movement than
   per-step generalized HMC?
4. Are coarse candidates selected often enough to justify retaining them?
5. Does sparse refinement occur on realistic hierarchical targets, or do
   difficult regions force refinement of nearly the entire trajectory?

The next appropriate step is a deliberately non-formal Julia prototype with
one refinement level, exact gradient accounting, and comparisons against HMC,
NUTS, DR-HMC, and DR-G-HMC on a funnel and at least one ordinary posterior.
