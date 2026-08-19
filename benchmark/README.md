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
is warmed before `BenchmarkTools` measures each complete chain. The benchmark
uses the low-level transition interfaces so that AdvancedHMC's optional sample
and diagnostic storage is not charged only to AdvancedHMC.

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

The full runner records ten complete-chain timing repetitions per case by
default. The report shows every repetition together with the median and IQR;
`HMC_REPETITIONS` changes that fixed count.

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

Separate quality chains write `benchmark/results/quality.csv`. They report
moment error against each fixture's known mean and marginal variance, minimum
coordinate ESS, ESS/s, movement, AdvancedHMC acceptance and divergences, and
mean integration work. These extend the lightweight gradient and moment checks
registered in the Julia integration suite.

Quality diagnostics in the report are not convergence proofs or CI gates. The
planned stronger checks are multiple independently seeded chains, split
rank-normalized R-hat, bulk and tail ESS (also per gradient evaluation), full
covariance error for Gaussian targets, marginal quantile or ECDF error for
product targets, and Monte Carlo uncertainty for reported errors. Small,
stable covariance and known-quantile regressions belong in the integrated test
suite; the multi-chain and distributional report remains in this environment.

The workload can be changed through `HMC_DIMENSION`, `HMC_DRAWS`,
`HMC_LEAPFROG_STEPS`, `HMC_STEP_SIZE`, `HMC_SEED`, and
`HMC_BENCHMARK_SECONDS`. `HMC_NUTS_MAX_DEPTH` controls the NUTS tree-depth cap.
`HMC_QUALITY_DRAWS` controls the separate sampling-quality chains.
