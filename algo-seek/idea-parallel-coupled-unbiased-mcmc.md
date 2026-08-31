# Parallel coupled MCMC for unbiased estimation

## Motivation

Coupled MCMC can turn finite runs into unbiased estimators and average
independent estimator replicates across processors. Its practical bottleneck
is the joint distribution of estimator variance and random completion cost:

```text
H_r = unbiased estimator
C_r = computation required to reach and pass the meeting time
```

The relevant objectives are work-normalized variance and wall-clock latency
under a declared processor budget. A small mean meeting time is insufficient
when rare late meetings dominate variance or batch makespan.

This note records two related directions:

1. parallel execution inside an HMC or coupled-HMC transition; and
2. unbiased scheduling and combination of random-duration replicates.

The closest foundations are Jacob, O'Leary, and Atchadé's
[unbiased coupled MCMC framework](https://doi.org/10.1111/rssb.12336), Heng and
Jacob's [coupled HMC construction](https://doi.org/10.1093/biomet/asy074), and
Xu et al.'s [multinomial-HMC coupling](https://proceedings.mlr.press/v130/xu21i.html).
Work on [parallelizing MCMC across sequence
length](https://proceedings.neurips.cc/paper_files/paper/2025/file/202886ee1c9ca735cb5bff3a00a69883-Paper-Conference.pdf)
shows that time-direction parallelism is active research, not an unclaimed
idea.

## The central coupled-MCMC difficulty

A useful coupling must handle three regimes:

```text
far apart              nearby                 almost identical
global exploration  -> contraction         -> exact meeting
```

Shared randomness may contract nearby chains without synchronizing different
modes. More independent proposals may explore better without contracting. In
a continuous state space, numerical closeness is not exact meeting: a maximal,
sticky, or other positive-meeting mechanism remains necessary. Coupling does
not repair a marginal kernel that mixes poorly.

Evaluation must report the meeting-time distribution, high quantiles and
censoring, estimator variance, expected work, work-normalized variance, and
wall-clock completion under an explicit processor budget. Initialization,
lag, and averaging parameters are part of the comparison.

## Direction A: parallel trajectories

Ordinary leapfrog is recurrent across integration time:

```text
(q_0, p_0) -> (q_1, p_1) -> ... -> (q_L, p_L)
```

Parallelism inside a gradient evaluation and between the two marginal chains
is comparatively direct. Parallelism across leapfrog steps is difficult
because every state determines the next gradient. Parallel-in-time or
speculative methods must charge reconciliation and discarded work and preserve
the proposal properties used by the MH correction.

A candidate natural for this project is a parallel trajectory network:

```text
                    coarse reversible path
                  /                        \
current state ---+--- refined path --------+--- corrected selection
                  \--- alternative scale --/
```

Branches execute concurrently. Correctness should come from a proved
rerooting, involution, delayed-rejection, or multinomial-selection rule rather
than treating an arbitrary parallel ODE approximation as leapfrog. Required
obligations include exact marginal transition laws, reversibility/volume or an
explicit density correction, deterministic replay, defined failure behavior,
and agreement between implemented and proved selection.

This direction is broader than the parallel nonlinear-recurrence construction
already demonstrated for HMC. A dedicated audit must compare at least:

- parallel-in-time families: Parareal, PFASST, MGRIT, multiple shooting, and
  revisionist/deferred-correction methods;
- parallel-across-method families: simultaneous Runge--Kutta stages,
  collocation, and spectral deferred correction;
- geometric variants: symmetric/symplectic Parareal, variational methods, and
  symplectic implicit Runge--Kutta;
- algebraic methods: exact affine/polynomial composition and prefix scans; and
- model-structured methods: force splitting, sparse blocks, and batched target
  evaluations.

The HMC objective differs from a conventional ODE objective. Trajectory error
matters through acceptance and movement, while exact validity depends on the
finite implemented proposal map. For every candidate the audit will therefore
record parallel depth, total work, synchronization, memory, accelerator fit,
finite-iteration reversibility, volume preservation or Jacobian correction,
and failure semantics. Numerical convergence to a serial integrator is not by
itself treated as an exact finite-iteration HMC theorem.

See the [parallel HMC integrator audit](parallel-hmc-integrator-audit.md) for
the detailed comparison, HMC validity gate, and source review.

## Direction B: scheduling random-duration replicates

Independent unbiased replicates are embarrassingly parallel only if random
completion can be ignored. A fixed batch waits for its slowest member. More
aggressive policies can silently introduce completion bias because `H_r` and
`C_r` need not be independent.

Policies that are not automatically safe include:

- averaging only replicates completed before a deadline;
- cancelling or restarting late meetings;
- launching duplicates and retaining the first completion;
- weighting estimates by observed runtime; and
- stopping after a data-dependent number of completed replicates.

A conservative baseline declares a fixed set of replicate identifiers,
completes every replicate, and uses predetermined weights. Dynamic work
stealing is then only an implementation detail. A more interesting
**malleable coupled-MCMC scheduler** changes computational resources without
selecting estimators:

```text
many pairs start with few workers
             |
short pairs finish and release workers
             |
released workers accelerate likelihoods, particles, gradients,
or parallel trajectory branches of the remaining declared pairs
             |
all declared estimators finish and are combined
```

If allocation changes only evaluation time—not random choices or arithmetic
semantics—the estimator law is unchanged. Floating-point reductions,
race-dependent RNG consumption, and approximate solvers can make scheduling
observable, so this boundary must be explicit.

## Heterogeneous unbiased estimators

Different coupling strategies may all satisfy `E[H_j] = pi(h)`. They can be
combined with predetermined weights summing to one. A separate pilot can
estimate variance and cost, freeze production allocation, and use a rule such
as

```text
n_j proportional to sqrt(variance_j / cost_j).
```

Weights or strategies learned from the same production estimator values are
not presumed unbiased. Independent pilots, sample splitting, or a proved
adaptive rule are required. Finite-time ratios such as total reward divided by
random completed work are likewise not presumed unbiased merely because each
`H_j` is unbiased.

## Combined architecture

```text
                 fixed declared estimator set
                            |
           +----------------+----------------+
           |                |                |
      coupled pair     coupled pair     coupled pair
         short            medium            long
           |                |                |
           +---- released processors ------>|
                                            |
                              parallel target/trajectory work
                                            |
                                      exact meeting
```

The scheduler attacks wall-clock tails; the inner parallel method accelerates
one transition. Neither should alter the declared coupled kernel.

## Phased study

1. Record joint `(meeting time, estimator value, per-step cost)` traces for the
   existing coupled RWMH and multinomial-HMC clients.
2. Build a replay-only scheduling simulator comparing fixed batches, dynamic
   queues, and malleable allocation without changing sampler code.
3. State and prove a scheduler-independence theorem for fixed declared
   replicates under an abstract cost/resource model.
4. Add parallel target and gradient evaluation, which is lower risk than
   parallelizing integration time.
5. Prototype a finite parallel trajectory network with an exact corrected
   selection rule.
6. Combine both layers and evaluate work-normalized variance and makespan.

This direction does not claim that scheduling reduces total mathematical
work. Its first target is lower latency and better processor utilization
without completion bias. Reducing total work requires a better coupling,
reusable trajectory computation, or better allocation among heterogeneous
unbiased estimators.

## Variance-reduction audit

The repository currently has an important layer mismatch. The Lean module
`Mcmc.Kernel.UnbiasedEstimator` proves the finite telescoping identity and,
under explicit meeting-tail and moment hypotheses, unbiasedness and finite
variance of the stopped estimator. The Julia `Xu21CoupledSampler` exposes
meeting times and censoring diagnostics, but not the estimator itself. Meeting
time is therefore measurable while the actual objective

```text
expected work * variance(H)
```

is not yet available end to end.

The literature suggests four distinct variance levers, in increasing order of
implementation and proof risk:

1. **Time averaging and independent pilot tuning.** Implement `H_{k:m}` rather
   than only `H_k`. Use an independent pilot sample of meeting times to freeze
   `k` at a high meeting-time quantile and compare predetermined multiples
   `m/k`. Heng and Jacob report that this can reduce relative inefficiency by
   orders of magnitude. Tuning on production estimator values would require a
   separate justification.
2. **General lag `L`.** A lag larger than one reduces the number and weights of
   bias-correction terms and can lower variance at similar work. This changes
   the path construction and should be formalized as a general-lag telescoping
   identity before it becomes a verified runtime option.
3. **Same-marginal control variates.** Since `X_t` and `Y_t` have the same
   marginal law at fixed `t`, predetermined linear combinations of
   `h(X_t)-h(Y_t)` have expectation zero. Coefficients estimated on an
   independent pilot and frozen for production preserve the simple
   unbiasedness argument. Jointly fitted production coefficients are not
   silently assumed unbiased.
4. **Surrogate-Hamiltonian and antithetic controls.** A tractable approximation
   `Q` to the target can provide a correlated control chain with known or
   cheaply unbiased expectations; antithetic HMC can be layered on top when
   approximate symmetry is present. This adds a second target, coupling,
   fitting boundary, and cost model, so it follows the generic estimator work.

The immediate implementation milestone should therefore be deliberately
small:

```text
faithful coupled path
    -> executable H_{k:m} and signed correction trace
    -> replicated variance, cost, and work-normalized variance diagnostics
    -> independent pilot selection of frozen (k,m)
```

Only after this baseline exists can a change to multinomial coupling, mixture
weight, trajectory length, lag, or control variate be called a variance
improvement rather than merely a meeting-time improvement.

Primary references for this ordering are Heng and Jacob's
[unbiased HMC study](https://doi.org/10.1093/biomet/asy074), Vanetti and
Doucet's general-lag discussion in the
[JRSS-B discussion](https://rss.onlinelibrary.wiley.com/doi/full/10.1111/rssb.12336),
Craiu and Meng's
[same-marginal control variates](https://doi.org/10.5705/ss.202020.0461), and
Piponi, Hoffman, and Sountsov's
[surrogate and antithetic HMC controls](https://proceedings.mlr.press/v108/piponi20a.html).
