# Statistically sensed local curvature for RMHMC

This note positions a possible position-dependent metric for Riemann manifold
Hamiltonian Monte Carlo (RMHMC). The idea is to spend a fixed budget of `M`
additional curvature-vector passes, relative to ordinary HMC, at each metric
evaluation. Those passes sense a local dense subspace without forming or
factoring a dense Hessian. It is an algorithm-seeking note, not a novelty claim
or an implementation commitment.

The intended metric has structured form

```text
G_M(q) = lambda I + D(q) + U_M(q) U_M(q)^T,
```

where the optional `D(q)` senses coordinate-wise curvature, the `M` columns of
`U_M(q)` sense locally important directions, and `lambda > 0` supplies a
strictly positive floor. The main candidate is the low-rank dense correction;
a purely diagonal estimate is only a validation baseline. All retained terms
remain position dependent: a metric
learned during warmup and then frozen is a useful preconditioned-HMC baseline,
but it no longer realizes RMHMC's local-geometric promise.

The budgeted question is:

> Given exactly `M` additional curvature passes beyond ordinary HMC, which
> smooth position-dependent metric yields the best effective samples per pass
> and per second while retaining a corrected invariant transition?

## Phased research ladder

| Stage | Online curvature passes per metric evaluation | Metric | Learning/adaptation |
|---|---:|---|---|
| Ordinary HMC | `0` | fixed Euclidean | none |
| Full dense RMHMC | up to `d` HVPs | full local | none |
| Random-sketch RMHMC | `M << d` HVPs | local ridge plus rank `M` | none |
| Frozen amortized RMHMC | `0` | learned local structured metric | offline, then frozen |
| Hybrid RMHMC | `m << M` HVPs | frozen learned metric plus local residual | offline, then fixed probes |
| Online learned RMHMC | variable | continually learned local metric | online adaptive MCMC |

The first implementation milestone stops at random-sketch RMHMC. Offline
amortization can train a smooth linear, random-feature, shallow, or
autoencoder-style predictor from saved `(q, z, C(q)z)` observations. Continued
online updates are a later stage because they change the transition kernel and
need adaptive-MCMC or extended-state theory.

## Where the idea sits

The proposal combines four established lines of work.

1. **RMHMC.** Girolami and Calderhead define HMC with a smooth
   position-dependent positive-definite metric, including its log-determinant
   and metric-force terms. This supplies the target Hamiltonian and the
   correctness obligations; replacing the exact Hessian by another valid
   metric does not by itself make the invariant distribution approximate.
2. **Fisher and generalized Gauss--Newton geometry.** Fisher and generalized
   Gauss--Newton (GGN) matrices provide positive-semidefinite curvature
   surrogates. They are often preferable to a raw, possibly indefinite
   Hessian, although the empirical Fisher is not interchangeable with the
   Fisher or GGN.
3. **Randomized numerical linear algebra.** Hutchinson-style probes estimate
   diagonals and traces, while randomized range finding, Nyström methods, and
   fixed-step Krylov/Lanczos methods sense a dominant subspace using
   matrix-vector products. These methods motivate repeated Hessian-vector,
   Fisher-vector, or GGN-vector passes rather than dense matrix construction.
4. **Auxiliary-variable MCMC.** Random probes can either be fixed algorithm
   parameters or included in an extended state. The latter could permit probe
   refreshment between trajectories while requiring the trajectory and its
   reverse to use the same probes.

The candidate contribution is therefore not “use an approximate Hessian” or
“use random projections” in isolation. The research question is whether a
smooth, structured, locally re-evaluated metric built from a small statistical
probe budget can make corrected RMHMC cheaper per effective sample, with an
exact conditional or extended-state correctness argument.

## Plausible constructions

### Budgeted rank-`M` local metric

For fixed probes `z_1, ..., z_M`, compute

```text
u_j(q) = C(q) z_j
G_M(q) = lambda I + (1 / M) sum_j u_j(q) u_j(q)^T,
```

where `C(q)` is a Hessian, Fisher, or GGN operator. The resulting matrix is
dense in its entries but represented as a ridge plus a rank-`M` update. It
therefore captures rotated local curvature that no diagonal metric can
represent. Woodbury and determinant identities reduce its inverse and log
determinant to operations on an `M`-by-`M` Gram matrix.

This is the primary candidate. It uses exactly `M` curvature-vector products
per metric evaluation, has linear-in-`d` storage for fixed `M`, and introduces
a natural controlled budget curve `M = 0, 1, 2, 4, 8, ...`. The case `M = 0`
is ordinary HMC with the ridge metric.

### Fixed-probe diagonal baseline

For fixed Rademacher vectors `z_1, ..., z_m`, estimate a local diagonal by

```text
d_hat(q) = (1 / m) sum_j z_j .* (C(q) z_j),
```

where `C(q)` is preferably a Fisher or GGN operator. Apply a smooth positive
map and add a ridge before using the estimate as `D(q)`. This requires `m`
curvature-vector products and `O(d)` metric solves and log determinants.

This is the lowest-complexity genuinely position-dependent control. Probe
averaging supplies a statistical accuracy--cost tradeoff, while fixing the
probes makes the metric a deterministic function of `q`. It cannot capture
rotated curvature and is not the intended research endpoint.

### Orthonormalized or Krylov rank-`M` metric

For a fixed test matrix `Omega` with `r` columns, compute one or more passes

```text
Y(q) = C(q) Omega
```

and construct a rank-`r` factor `U(q)` from the sensed range. A diagonal term
and positive ridge cover curvature outside that range. Woodbury and determinant
identities can reduce metric solves and log determinants to structured
`d`-by-`r` operations rather than dense `d`-dimensional factorization.

This is attractive when a few local directions dominate, but differentiating
through QR, eigensolvers, or Lanczos recurrences is delicate near repeated
eigenvalues and breakdowns. A first specification should use fixed rank,
fixed probe vectors, fixed pass count, and deterministic breakdown behavior.

### Confidence-regularized metric

Repeated probes also expose estimator variability. A smooth function of that
variability could increase the ridge or shrink uncertain directions toward a
simple diagonal metric. This gives a statistical interpretation to metric
regularization:

```text
high probe agreement     -> trust more local structure
low probe agreement      -> shrink smoothly toward a safer metric
```

Hard confidence thresholds, discontinuous eigenvalue clipping, and adaptive
rank changes should be avoided because they make `q -> G(q)` nonsmooth.

### Refreshed probes as auxiliary state

A more ambitious transition samples a probe collection between trajectories,
holds it fixed throughout one forward/reverse trajectory construction, and
then updates it as an auxiliary variable. This could avoid committing the
whole chain to one sketch while preserving a well-defined conditional metric.
It needs a new extended-state invariance theorem; independently refreshing
probes inside integrator steps is not covered by ordinary RMHMC correctness.

## Correctness boundary

For a fixed probe collection, statistical estimation error affects the quality
of the geometry, not automatically the stationary target. Exact corrected
RMHMC remains plausible only if:

- `G(q)` is a declared measurable, sufficiently smooth, strictly
  positive-definite metric;
- the inverse, log determinant, and force are mutually consistent operations
  on that same metric;
- the dynamics differentiate through the metric estimator rather than treating
  a changing estimate as constant;
- the numerical proposal is reversible and volume preserving, or carries the
  appropriate correction; and
- any probe randomness is fixed for the proposal or represented explicitly in
  the Markov state.

For Hessian-derived `C(q)`, differentiating the metric generally introduces
third-derivative contractions. Automatic differentiation can avoid storing a
third-order tensor, but it does not remove that underlying work. Fisher/GGN
factorizations can be more attractive because their metric forces may be
expressible using lower-order derivatives of model factors.

Warmup-only accumulation, online quasi-Newton history, and local statistical
sensing are different algorithms. A warmup estimator that is frozen produces
ordinary preconditioned HMC. An estimator updated using past sampled states
after warmup creates an adaptive, history-dependent chain unless additional
adaptive-MCMC or extended-state theory is supplied.

## Complexity against dense RMHMC

Let `d` be dimension, `L` the number of generalized-leapfrog steps, `K` the
number of implicit-solver iterations per step, `C_v` the cost of one
curvature-vector product, and `C_dv` the cost of differentiating one such
product with respect to position.

For a Hessian-derived dense standard metric, explicit construction takes up
to `d` curvature-vector products, storage is `O(d^2)`, and Cholesky
factorization is `O(d^3)` per metric evaluation. Suppressing model-specific
metric-derivative costs, a trajectory therefore has the characteristic cost

```text
O(L K (d C_v + d^3 + dense metric-force cost)).
```

For the ridge-plus-rank-`M` representation, constructing `U_M` takes `M`
curvature-vector products. Forming and factoring its Gram matrix takes
`O(d M^2 + M^3)`, storage is `O(d M)`, and subsequent solves cost
`O(d M + M^2)`. The corresponding trajectory cost is approximately

```text
O(L K (M C_v + d M^2 + M^3 + M C_dv)).
```

Thus, for fixed `M << d`, the proposal replaces `d` curvature passes by `M`,
quadratic storage by linear storage, and cubic dense factorization by
structured low-rank algebra. This is a comparison with an unstructured dense
RMHMC implementation; an analytically structured standard metric may already
be cheaper.

The `M C_dv` term is the main risk. Hessian-derived probes generally require
third-derivative contractions in the RMHMC metric force. Automatic
differentiation can avoid materializing a third-order tensor but cannot remove
the mathematical work. Fisher/GGN factors are attractive when their force can
instead be expressed through model Jacobians and lower-order derivatives.

The budget is most cleanly interpreted as `M` extra passes at every metric
evaluation. Sensing once at the start of a trajectory and then freezing the
metric is cheaper, but the resulting start-dependent proposal is not standard
RMHMC and requires a separate reverse-proposal or extended-state argument.

## Evidence needed before formalization

The first empirical question is whether local sensing pays for itself. On
targets with known curvature and on hierarchical/funnel models, compare:

- dense classical RMHMC;
- fixed global preconditioned HMC;
- a fixed-probe diagonal Fisher/GGN baseline; and
- the budgeted ridge-plus-rank-`M` metric across several values of `M`.

Report effective samples per second and per curvature-vector product, not only
acceptance. Also report metric-estimation error on small problems, integrator
iterations, energy error, conditioning, and failure or fallback frequency.

A useful first research prototype is the direct outer-product construction
`G_M(q) = lambda I + U_M(q) U_M(q)^T / M`. It has an immediate SPD proof and
avoids differentiating an eigensolver. A diagonal estimator should remain a
control, while orthonormalized/Krylov and refreshed-probe variants should
follow only if the direct rank-`M` metric shows that local statistical sensing
can repay its derivative cost.

### Initial executable benchmark

`make benchmark-random-sketch-rmhmc` compares ordinary HMC, a full dense GGN
metric, a random-sketch metric materialized through dense RMHMC, and the exact
same sketch executed with Woodbury/determinant-lemma algebra. The workload is
a nonlinear banana target with known first and second moments. The benchmark
reports minimum coordinate ESS per second, per retained transition, and per
configured integrator step, alongside draws per second and memory.

The matched dense-versus-structured comparison isolates implementation cost:
the two rows represent the same `G_M(q)`. Comparisons with ordinary HMC and
full dense RMHMC instead measure the combined geometry/cost tradeoff and must
not be described as implementation-only speedups. At modest dimension,
ordinary HMC may remain superior in ESS per second; the research hypothesis is
not accepted until targets and dimensions are found where local geometry
repays curvature sensing.

The initial 2026-08-20 run used a 20-dimensional banana target, `M = 4`, three
chains of 500 draws, five configured integration steps, and 20 fixed-point
iterations per step:

| Algorithm | Draws/s | Minimum ESS/s | Minimum ESS/integrator step |
|---|---:|---:|---:|
| Ordinary HMC | 69,270 | 873.72 | 0.00298 |
| Full dense GGN RMHMC | 50.52 | 0.50 | 0.00220 |
| Sketch metric, materialized dense | 35.38 | 0.64 | 0.00408 |
| Sketch metric, structured | 737.39 | 12.50 | 0.00380 |

The matched sketch rows have similar per-step efficiency within the noise of
these short chains, while structured algebra improves raw throughput by
`20.84x` and minimum ESS/s by `19.39x`. Ordinary HMC remains decisively better
in absolute ESS/s on this workload. These are exploratory benchmark numbers,
not evidence that the random-sketch geometry already beats ordinary HMC or
full RMHMC. Longer chains, tuning at matched computational budgets, and harder
geometry are required before evaluating that hypothesis.

### Hard-geometry confirmation study

`make benchmark-random-sketch-geometry` uses a two-dimensional strongly warped
Gaussian with banana parameter `2.0`. Its inverse transformation is known, so
all convergence, bulk/tail ESS, jump-distance, mean, and variance diagnostics
are computed in latent standard-normal coordinates. Step size and integration
time are tuned separately. The confirmation run uses four chains of 2,000
iterations, discards the first 1,000 from each chain, and excludes
configurations with any numerical failure when selecting a best observed row.

| Algorithm | `epsilon` | Integration time | Bulk ESS/transition | Tail ESS/transition | Tail ESS/s | `Rhat` |
|---|---:|---:|---:|---:|---:|---:|
| Ordinary HMC | 0.001 | 0.1 | 0.01595 | 0.00620 | 36.82 | 1.695 |
| Exact-map Transport HMC | 0.2 | 1.0 | 0.29102 | 0.55553 | 97,568.88 | 1.005 |
| Rank-one likelihood-informed HMC | 0.1 | 1.0 | 0.07058 | 0.29305 | 24,240.67 | 1.107 |
| Full dense GGN RMHMC | 0.04 | 1.0 | 0.11815 | 0.17369 | 189.31 | 1.011 |
| Rank-one random-sketch RMHMC | 0.005 | 1.0 | 0.12178 | 0.19032 | 29.08 | 1.006 |

Exact-map Transport HMC has strong between-chain agreement and is the clear
upper baseline, but it is given the analytically known inverse warp and does
not include map-learning cost. The two Riemannian rows also have acceptable
between-chain agreement, and the sketch slightly exceeds full RMHMC in both
bulk and tail ESS per retained transition. The selected likelihood-informed
and ordinary-HMC rows have `Rhat = 1.107` and `1.695`, respectively, so their
ESS estimates are not reliable converged comparisons. The likelihood-informed
`epsilon=0.2` alternative improves agreement to `Rhat=1.017`, with tail
ESS/transition `0.25412` and nominal tail ESS/s `34,659.10`.

The practical-cost comparison remains mixed. Full RMHMC is faster than the
rank-one sketch in the 2D confirmation, where low-rank structure has little
opportunity to repay callback overhead. The dimension sweep below is the more
relevant implementation-scaling comparison.

The next scaling study is implemented by
`make benchmark-random-sketch-dimensions`. It replaces the axis-aligned banana
with a dense rotated volume-preserving shear

```text
y(q) = q + b ((a^T q)^2 - 1) c,    a^T c = 0,
```

whose inverse and pullback GGN metric are known. This preserves exact latent
standard-normal diagnostics while varying ambient dimension independently of
the intrinsic nonlinear geometry. The runner produces per-dimension CSV files,
a combined no-failure-row summary, and terminal plots for bulk/tail ESS per
transition and tail ESS per second.

### Probe-rank and solver audit

The first sweep accidentally used a zero fixed-point stopping tolerance and a
50-iteration cap, effectively forcing 50 iterations. The refined comparison
uses tolerance `1e-10`, a 25-iteration cap, and the separate `1e-6` residual
acceptance gate. A 12-iteration cap was tested and rejected by that gate. Thus
25 is a fail-closed empirical setting for this workload, not a general theorem
about fixed-point convergence.

With four 2,000-iteration chains and 1,000 burn-in iterations, rank one and
`ceil(log2(d))` probes give the
following best observed tail rows. Rows with elevated `Rhat` are exploratory
and their ESS estimates should not be treated as converged:

| `d` | Rank-one ESS/transition | Rank-one ESS/s | Rank-one `Rhat` | Rank-log `M` | Rank-log ESS/transition | Rank-log ESS/s | Rank-log `Rhat` |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 2 | 0.319 | 44.27 | 1.004 | 1 | 0.319 | 44.36 | 1.004 |
| 4 | 0.324 | 41.41 | 1.018 | 2 | 0.322 | 41.03 | 1.010 |
| 8 | 0.375 | 75.96 | 1.030 | 3 | 0.407 | 32.56 | 1.062 |
| 16 | 0.625 | 107.15 | 1.306 | 4 | 0.361 | 33.55 | 1.110 |
| 32 | n/a | n/a | n/a | 5 | 0.714 | 12.98 | 1.120 |

This target has one intrinsic nonlinear direction, so increasing sketch rank
mostly adds irrelevant work. Rank-log sometimes improves between-chain
agreement at intermediate dimensions, but it does not improve the overall
quality/cost trade-off here. A fair positive test needs genuinely higher-rank
local geometry.

Artifact version 23 now supplies explicit IR-backed Reference entries for
dense and random-sketch RMHMC. The random-sketch program owns structured
momentum refresh, repeated residual-gated integration, energy comparison, and
accept/reject; seeded tests compare it with the independent Optimized path.
Curvature actions, derivatives, and the finite-tolerance solver remain
declared host callbacks, so this closes the executable reference architecture
without claiming a theorem about Julia or positive-residual stationarity.

## Primary precedents

- Mark Girolami and Ben Calderhead, [Riemann manifold Langevin and Hamiltonian
  Monte Carlo methods](https://doi.org/10.1111/j.1467-9868.2010.00765.x),
  JRSS B, 2011.
- Michael Betancourt, [A general metric for Riemannian manifold Hamiltonian
  Monte Carlo](https://arxiv.org/abs/1212.4693), 2012, for the smooth SoftAbs
  treatment of indefinite Hessian curvature.
- James Martens, [New insights and perspectives on the natural gradient
  method](https://jmlr.org/papers/v21/17-678.html), JMLR, 2020, for Fisher/GGN
  relations and the empirical-Fisher distinction.
- Barak A. Pearlmutter, [Fast exact multiplication by the
  Hessian](https://doi.org/10.1162/neco.1994.6.1.147), *Neural Computation*,
  1994.
- Nathan Halko, Per-Gunnar Martinsson, and Joel A. Tropp, [Finding structure
  with randomness](https://arxiv.org/abs/0909.4061), SIAM Review, 2011.
- Per-Gunnar Martinsson and Joel A. Tropp, [Randomized numerical linear
  algebra: foundations and algorithms](https://arxiv.org/abs/2002.01387),
  *Acta Numerica*, 2020.

As of 2026-08-20, this note has not established whether the particular
fixed-probe, confidence-regularized RMHMC combination already appears in the
literature. Any novelty statement requires a narrower algorithm-level search.
