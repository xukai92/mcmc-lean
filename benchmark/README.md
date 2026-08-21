# HMC benchmarks

This isolated Julia environment compares fixed-step endpoint HMC,
fixed-length multinomial HMC, and fixed-parameter NUTS from VerifiedSamplers
and AdvancedHMC on a small target suite. The
default workload is 10,000 transitions in 100 dimensions, with step size 0.08;
the fixed-length algorithms use 10 leapfrog steps per transition.

```sh
make benchmark-hmc
make benchmark-report
```

For fast harness and page-layout iteration, use:

```sh
make benchmark-dev
```

To exercise the small acceptance benchmark for the current optimized-NUTS
phase-specialization pass, use:

```sh
make benchmark-nuts-optimization
```

This focused run prints its transformation name, assurance class, per-chain
times, median, and throughput. It complements rather than replaces the full
cross-implementation benchmark and correctness gates.

The focused classical-RMHMC comparison is:

```sh
make benchmark-rmhmc
```

It compares generated Reference, independent Optimized, and the pinned
AdvancedHMC generalized-leapfrog implementation on the nonconstant metric
`G(q)=diag(2+sin(qᵢ))`. All rows use the same target, step size, trajectory
length, fixed-point iteration count, and initial state. The VerifiedSamplers
rows check a declared residual tolerance but do not relabel the resulting
finite solve as exactly reversible, volume preserving, or stationary.
AdvancedHMC 0.8 does not
load its Riemannian metric implementation into its public module, so the script
loads that pinned internal source explicitly and labels the result
`advancedhmc`; this implementation-status caveat belongs here rather than in
the plot label. Environment variables `RMHMC_DIMENSION`,
`RMHMC_DRAWS`, `RMHMC_STEPS`, `RMHMC_STEP_SIZE`,
`RMHMC_SOLVER_ITERATIONS`, `RMHMC_RESIDUAL_TOLERANCE`, and `RMHMC_SEEDS`
control the workload.

The script reports median allocated bytes as well as throughput and simple
Gaussian moment errors. These remain machine-specific diagnostics rather than
formal correctness or convergence evidence.
It writes `rmhmc.csv`, `rmhmc-timings.csv`, `rmhmc-quality.csv`, and
`rmhmc-metadata.csv` under `benchmark/results/`. Production
`make benchmark-report` appends those rows to the shared tables, static chart,
and interactive website explorer while displaying their separate workload
configuration.

The random-sketch RMHMC studies use this same benchmark environment:

```sh
make benchmark-random-sketch-rmhmc
make benchmark-random-sketch-geometry
make benchmark-random-sketch-dimensions
make benchmark-random-sketch-rank-log
```

The dimension command runs isolated geometry-study jobs at ambient dimensions
`2,4,8,16` by default. They use a dense rotated, volume-preserving warp
with a known inverse, so all diagnostics are evaluated in latent
standard-normal coordinates. Dimension one remains available as an optional
unwarped Gaussian smoke-test baseline but is not part of the default sweep.
It reports every completed chain with an estimated completion time and
incrementally writes a `*-progress.csv` checkpoint beside each dimension's
result. Thus interrupted runs retain per-chain status and timing, although they
do not resume sampler state. It also writes per-dimension CSV files, a combined
best-stable-row CSV, and UnicodePlots charts for bulk/tail ESS per transition
and tail ESS per second. Override `GEOMETRY_STUDY_DIMENSIONS` and
`GEOMETRY_STUDY_DRAWS` for development runs. The default sweep uses 1,000
draws rather than the 4,000-draw 2D confirmation workload and remains
exploratory until a full run is explicitly recorded and reviewed.

The rank-log command uses `ceil(log2(d))` fixed random probes, records the
probe count in every result row, and writes separate `*-rank-log-*` artifacts.
The implicit fixed-point solver stops at tolerance `1e-10`, subject to a
25-iteration cap; every accepted transition must also satisfy the independent
`1e-6` residual check. Override these with
`GEOMETRY_STUDY_SOLVER_TOLERANCE` and
`GEOMETRY_STUDY_SOLVER_ITERATIONS` when studying solver sensitivity.

Execution labels in this exploratory study are intentionally narrower than
the repository-wide benchmark labels. `VectorHMC` invokes the IR-backed
Reference transition, while the study explicitly selects the Optimized dense
and sketch RMHMC paths. Artifact version 23 now also supplies IR-backed
Reference entries for dense and random-sketch RMHMC, but those are parity
anchors rather than the timed rows in this study. Metric and curvature
callbacks remain declared host boundaries for both paths. Consequently these
wall-clock rows do not compare three implementations at the same execution
layer; interpret cross-method ESS/s accordingly.

To make a fail-closed acceptance decision, first record the pre-change median,
then run the complete release gate and candidate measurement together:

```sh
make optimization-trial OPTIMIZATION_BASELINE_SECONDS=1.23 \
    OPTIMIZATION_MINIMUM_SPEEDUP=1.05
```

The command emits a line-oriented acceptance record and fails if any gate or
the requested speedup fails. A benchmark alone never accepts a change.

Development mode defaults to 1,000 transitions and three timed chains per
case. It writes `benchmark/results/dev.csv` rather than replacing the full
`latest.csv`, and marks the generated page as non-publication-quality. The
usual `HMC_DRAWS` environment variable can still override the development
chain length.

The comparison uses an identity mass matrix and analytic gradients for both
packages; it intentionally excludes automatic-differentiation time. Compilation
is warmed before each complete chain is measured. Every implementation stores
the full chain, so timing and quality use exactly the same execution workload.

The endpoint rows implement directly corresponding endpoint proposals. The
multinomial rows compare each package's fixed-length multinomial trajectory
implementation; they have the same target and integration budget, but their
trajectory construction and selection mechanics are not claimed to be
identical.

The `nuts-complete` rows compare the Lean-proved completed-tree C.4 Reference
against Optimized and AdvancedHMC fixed-length multinomial trajectories using
the same `2^d` leapfrog budget. They are work-matched, not claimed to implement
the same transition. The separate `nuts-dynamic` rows compare the independent
production-shaped `Optimized.NUTS` against AdvancedHMC using the same maximum
depth and generalized U-turn termination. There is no Reference row in that
group until early-stopping dynamic NUTS has a verified Reference
implementation. Mean leapfrog work remains visible for both groups.

The full runner records ten complete chains per case using the explicit fixed
seed list `4109:4118` by default. The report shows every chain timing together
with the median and IQR. `HMC_SEEDS` accepts a comma-separated replacement;
development mode uses the first three configured seeds. During execution the
runner prints the current target/algorithm/implementation case, total case
count, and elapsed wall time; progress output occurs outside timed regions.

The report covers an isotropic Gaussian, an AR(1)-correlated Gaussian, a
product quartic, an ill-conditioned diagonal Gaussian, and a symmetric
regularized-logistic target. The latter two targets extend the original suite;
endpoint and multinomial rows suffixed by their metric kind (`-dense` or
`-diagonal`) include the implemented
VerifiedSamplers Reference and Optimized constant-metric paths in new runs.
The Optimized runner prepares each metric once per complete chain. Diagonal
masses cache their inverse and square root; dense masses cache their Cholesky
factor and inverse-mass action. Adjacent leapfrog steps share their endpoint
gradient, and randomized-origin multinomial trajectories construct the left
and right branches directly instead of retracing the backward branch.
Raw results are written to
`benchmark/results/latest.csv`, with repetition-level measurements in
`benchmark/results/timings.csv`. `benchmark/report.jl` generates the committed
documentation page and SVG chart from those files. Run metadata is stored
separately in `benchmark/results/metadata.csv`, so regenerating a historical
report does not relabel it with the current checkout or machine.

The generated Documenter page also includes an interactive Plotly explorer
with metric, target, algorithm, implementation, and grouping controls. Its
browser dataset is generated from the same committed CSV files. The SVG is
retained as a static fallback for non-JavaScript readers and portable output.
The site-wide **Full width** navbar control expands the chart and tables and
persists the selected layout locally across documentation pages.

The same timed chains write quality summaries to
`benchmark/results/quality.csv`. They report
moment error against each fixture's known mean and marginal variance, minimum
coordinate ESS, ESS/s, movement, AdvancedHMC acceptance and divergences, and
mean integration work. New runs also report worst split rank-normalized R-hat,
minimum bulk/tail ESS, and a labelled ESS-per-gradient-work proxy across the
first four coordinates. The formulas and standard targets come from the
shared `VerifiedSamplers.Evaluation` module rather than a benchmark-specific
implementation. Integrated tests consume that same layer for lightweight
regression gates; this benchmark adds larger workloads, timing, aggregation,
and reporting.

Because every compared implementation now pays the same chain-storage cost,
no second quality-only sampling workload is needed. Diagnostic calculations
run after timing and are not charged to throughput.

Quality diagnostics in the report are not convergence proofs or CI gates.
Multiple independently seeded chains, split rank-normalized R-hat, and
bulk/tail ESS are implemented. New runs also record maximum covariance error
for Gaussian fixtures, maximum marginal-median error (all fixtures are
symmetric), and batch-means Monte Carlo standard error for means. Remaining
work is raw-chain covariance/ECDF visualization and uncertainty intervals for
covariance and quantile errors. Small,
stable covariance and known-quantile regressions belong in the integrated test
suite; the multi-chain and distributional report remains in this environment.

The workload can be changed through `HMC_DIMENSION`, `HMC_DRAWS`,
`HMC_LEAPFROG_STEPS`, `HMC_STEP_SIZE`, `HMC_SEED`, and `HMC_SEEDS`.
`HMC_NUTS_MAX_DEPTH` is the single shared tree-depth budget for Reference,
Optimized, and AdvancedHMC NUTS. Reference constructs the complete tree at
that depth, while the dynamic implementations may stop earlier. The default is
four, so every implementation uses at most 16 leapfrog steps per transition.
`HMC_SEED` determines
the default consecutive seed list; an explicit `HMC_SEEDS` takes precedence.
