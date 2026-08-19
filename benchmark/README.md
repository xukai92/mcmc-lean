# HMC benchmarks

This isolated Julia environment compares fixed-step endpoint HMC,
fixed-length multinomial HMC, and AdvancedHMC NUTS on a small target suite. The
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

The committed NUTS row is AdvancedHMC-only and reports its observed average
leapfrog count because its work per transition is dynamic. Those measurements
predate the repository's separately labelled production-shaped NUTS runtime.
That runtime is not retroactively inserted into the stored results, and its
Lean invariance/correspondence boundary remains explicit. The certified
checked-tree samplers remain distinct from both production-shaped runtimes.

The full runner records ten complete chains per case using the explicit fixed
seed list `4109:4118` by default. The report shows every chain timing together
with the median and IQR. `HMC_SEEDS` accepts a comma-separated replacement;
development mode uses the first three configured seeds.

The report covers an isotropic Gaussian, an AR(1)-correlated Gaussian, a
product quartic, an ill-conditioned diagonal Gaussian, and a symmetric
regularized-logistic target. The latter two targets extend the original suite;
preconditioned endpoint and multinomial rows are AdvancedHMC-only in this
first pass. Raw results are written to
`benchmark/results/latest.csv`, with repetition-level measurements in
`benchmark/results/timings.csv`. `benchmark/report.jl` generates the committed
documentation page and SVG chart from those files. Run metadata is stored
separately in `benchmark/results/metadata.csv`, so regenerating a historical
report does not relabel it with the current checkout or machine.

The same timed chains write quality summaries to
`benchmark/results/quality.csv`. They report
moment error against each fixture's known mean and marginal variance, minimum
coordinate ESS, ESS/s, movement, AdvancedHMC acceptance and divergences, and
mean integration work. New runs also report worst split rank-normalized R-hat,
minimum bulk/tail ESS, and a labelled ESS-per-gradient-work proxy across the
first four coordinates. The formulas come from the shared
`VerifiedSamplers.jl/test/support/QualityDiagnostics.jl` support module rather
than a benchmark-specific implementation. These extend the lightweight
gradient and moment checks registered in the Julia integration suite.

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
`HMC_NUTS_MAX_DEPTH` controls the NUTS tree-depth cap. `HMC_SEED` determines
the default consecutive seed list; an explicit `HMC_SEEDS` takes precedence.
