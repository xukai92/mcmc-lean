# HMC benchmark report

This is a reproducible implementation benchmark, not a theorem about convergence or a claim that Float64 execution is identical to the exact-real Lean semantics.

![HMC transition-throughput distributions](assets/benchmarks/hmc-throughput.svg)

Rows are grouped first by target and then by algorithm. Within each row, colors compare libraries implementing that same `target × algorithm` case. Small translucent points are complete-chain timing repetitions; large points and thick intervals are medians and IQRs. The shared logarithmic axis retains absolute throughput and remains extensible to additional libraries.

Preconditioned endpoint and multinomial rows are AdvancedHMC-only in this first pass; their absence of VerifiedSamplers points is intentional, not missing data.

The stored NUTS measurements are likewise AdvancedHMC-only. They were produced before the repository added its separately labelled production-shaped NUTS runtime and are not retroactively supplemented. That runtime remains runtime-only at the current Lean correspondence boundary.

## Configuration

- Commit: `5af0a43`
- Julia: `1.12.5`
- CPU: `Intel Xeon Processor (SapphireRapids)`
- Dimension: `100`
- Draws per measured chain: `10000`
- Complete-chain timing repetitions per case: `10`
- Step size: `0.08`
- Fixed trajectory length: `10` leapfrog steps
- Gradients: analytic callbacks for both packages; AD time excluded

## Results

### Median transitions per second

#### Endpoint

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Isotropic Gaussian | 26099 | 107010 | 68164 |
| Correlated Gaussian (ρ=0.9) | 11007 | 31620 | 23391 |
| Product quartic | 24045 | 108620 | 48698 |
| Ill-conditioned Gaussian | 24892 | 116452 | 62098 |
| Regularized logistic | 13975 | 39032 | 24288 |

#### Multinomial

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Isotropic Gaussian | 22400 | 50006 | 34795 |
| Correlated Gaussian (ρ=0.9) | 7618 | 18346 | 19341 |
| Product quartic | 18266 | 39157 | 30750 |
| Ill-conditioned Gaussian | 17573 | 38940 | 34468 |
| Regularized logistic | 8669 | 19282 | 18508 |

#### Nuts

| Target | advancedhmc |
|---|---:|
| Isotropic Gaussian | 7930 |
| Correlated Gaussian (ρ=0.9) | 1861 |
| Product quartic | 13638 |
| Ill-conditioned Gaussian | 1143 |
| Regularized logistic | 4086 |

#### Preconditioned-endpoint

| Target | advancedhmc |
|---|---:|
| Correlated Gaussian (ρ=0.9) | 12669 |
| Ill-conditioned Gaussian | 48823 |

#### Preconditioned-multinomial

| Target | advancedhmc |
|---|---:|
| Correlated Gaussian (ρ=0.9) | 10765 |
| Ill-conditioned Gaussian | 29484 |

### Complete summary

| Target | Algorithm | Implementation | Median | IQR | Draws/s | Mean steps | Allocations |
|---|---|---|---:|---:|---:|---:|---:|
| Isotropic Gaussian | endpoint | verified-reference | 383.2 ms | 381.0–385.1 ms | 26099 | 10.0 | 5639933 |
| Isotropic Gaussian | endpoint | verified-optimized | 93.4 ms | 61.6–134.7 ms | 107010 | 10.0 | 970025 |
| Isotropic Gaussian | endpoint | advancedhmc | 146.7 ms | 145.3–157.2 ms | 68164 | 10.0 | 2100033 |
| Isotropic Gaussian | multinomial | verified-reference | 446.4 ms | 431.1–452.6 ms | 22400 | 10.0 | 5000714 |
| Isotropic Gaussian | multinomial | verified-optimized | 200.0 ms | 187.9–235.1 ms | 50006 | 10.0 | 1966420 |
| Isotropic Gaussian | multinomial | advancedhmc | 287.4 ms | 285.6–291.3 ms | 34795 | 10.0 | 2947307 |
| Isotropic Gaussian | nuts | advancedhmc | 1261.1 ms | 1246.4–1431.0 ms | 7930 | 63.0 | 16449841 |
| Correlated Gaussian (ρ=0.9) | endpoint | verified-reference | 908.5 ms | 900.8–922.3 ms | 11007 | 10.0 | 6539529 |
| Correlated Gaussian (ρ=0.9) | endpoint | verified-optimized | 316.3 ms | 308.8–342.0 ms | 31620 | 10.0 | 1430025 |
| Correlated Gaussian (ρ=0.9) | endpoint | advancedhmc | 427.5 ms | 424.5–429.7 ms | 23391 | 10.0 | 2540037 |
| Correlated Gaussian (ρ=0.9) | multinomial | verified-reference | 1312.7 ms | 1302.8–1319.6 ms | 7618 | 10.0 | 6881366 |
| Correlated Gaussian (ρ=0.9) | multinomial | verified-optimized | 545.1 ms | 536.9–562.9 ms | 18346 | 10.0 | 2795088 |
| Correlated Gaussian (ρ=0.9) | multinomial | advancedhmc | 517.0 ms | 500.7–526.6 ms | 19341 | 10.0 | 3387311 |
| Correlated Gaussian (ρ=0.9) | nuts | advancedhmc | 5373.2 ms | 5192.7–5711.4 ms | 1861 | 122.9 | 36977797 |
| Correlated Gaussian (ρ=0.9) | preconditioned-endpoint | advancedhmc | 789.4 ms | 778.4–801.4 ms | 12669 | 10.0 | 2540037 |
| Correlated Gaussian (ρ=0.9) | preconditioned-multinomial | advancedhmc | 928.9 ms | 918.7–950.7 ms | 10765 | 10.0 | 3387311 |
| Product quartic | endpoint | verified-reference | 415.9 ms | 411.2–420.3 ms | 24045 | 10.0 | 6439801 |
| Product quartic | endpoint | verified-optimized | 92.1 ms | 86.3–187.3 ms | 108620 | 10.0 | 1370025 |
| Product quartic | endpoint | advancedhmc | 205.3 ms | 202.3–215.8 ms | 48698 | 10.0 | 2320035 |
| Product quartic | multinomial | verified-reference | 547.5 ms | 542.1–553.7 ms | 18266 | 10.0 | 6601366 |
| Product quartic | multinomial | verified-optimized | 255.4 ms | 245.0–270.1 ms | 39157 | 10.0 | 2565088 |
| Product quartic | multinomial | advancedhmc | 325.2 ms | 320.8–332.6 ms | 30750 | 10.0 | 3167309 |
| Product quartic | nuts | advancedhmc | 733.3 ms | 725.4–745.0 ms | 13638 | 31.0 | 8780035 |
| Ill-conditioned Gaussian | endpoint | verified-reference | 401.7 ms | 393.9–407.9 ms | 24892 | 10.0 | 6537487 |
| Ill-conditioned Gaussian | endpoint | verified-optimized | 85.9 ms | 79.8–182.2 ms | 116452 | 10.0 | 1430025 |
| Ill-conditioned Gaussian | endpoint | advancedhmc | 161.0 ms | 157.5–168.1 ms | 62098 | 10.0 | 2540037 |
| Ill-conditioned Gaussian | multinomial | verified-reference | 569.1 ms | 557.4–587.8 ms | 17573 | 10.0 | 6881366 |
| Ill-conditioned Gaussian | multinomial | verified-optimized | 256.8 ms | 248.0–274.5 ms | 38940 | 10.0 | 2795088 |
| Ill-conditioned Gaussian | multinomial | advancedhmc | 290.1 ms | 288.7–297.0 ms | 34468 | 10.0 | 3387311 |
| Ill-conditioned Gaussian | nuts | advancedhmc | 8750.0 ms | 7880.3–8953.4 ms | 1143 | 323.5 | 97160197 |
| Ill-conditioned Gaussian | preconditioned-endpoint | advancedhmc | 204.8 ms | 201.1–213.7 ms | 48823 | 10.0 | 2770039 |
| Ill-conditioned Gaussian | preconditioned-multinomial | advancedhmc | 339.2 ms | 303.7–342.6 ms | 29484 | 10.0 | 3607313 |
| Regularized logistic | endpoint | verified-reference | 715.6 ms | 711.0–718.0 ms | 13975 | 10.0 | 6439897 |
| Regularized logistic | endpoint | verified-optimized | 256.2 ms | 252.6–345.5 ms | 39032 | 10.0 | 1370025 |
| Regularized logistic | endpoint | advancedhmc | 411.7 ms | 404.8–417.0 ms | 24288 | 10.0 | 2320035 |
| Regularized logistic | multinomial | verified-reference | 1153.6 ms | 1148.4–1163.8 ms | 8669 | 10.0 | 6601366 |
| Regularized logistic | multinomial | verified-optimized | 518.6 ms | 514.4–523.3 ms | 19282 | 10.0 | 2565088 |
| Regularized logistic | multinomial | advancedhmc | 540.3 ms | 520.3–549.9 ms | 18508 | 10.0 | 3167309 |
| Regularized logistic | nuts | advancedhmc | 2447.3 ms | 2422.5–2491.8 ms | 4086 | 50.6 | 14254259 |

## Sampling quality

Quality runs are separate seeded chains rather than BenchmarkTools trials. Moment errors use each target's known zero mean and analytical or independently computed marginal variance. ESS is the minimum autocorrelation ESS among the first four coordinates after ten-percent burn-in.

| Target | Algorithm | Implementation | ESS/s | Mean RMSE (std.) | Variance RMSE (relative) | Movement | Acceptance | Divergences | Mean steps |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|
| Isotropic Gaussian | endpoint | verified-optimized | 14149.4 | 0.017 | 0.018 | 0.996 | — | 0 | 10.0 |
| Isotropic Gaussian | endpoint | advancedhmc | 7497.2 | 0.017 | 0.016 | 0.996 | 0.995 | 0 | 10.0 |
| Isotropic Gaussian | multinomial | verified-optimized | 909.6 | 0.042 | 0.041 | 0.993 | — | 0 | 10.0 |
| Isotropic Gaussian | multinomial | advancedhmc | 382.7 | 0.039 | 0.041 | 0.909 | 0.998 | 0 | 10.0 |
| Isotropic Gaussian | nuts | advancedhmc | 7137.7 | 0.004 | 0.016 | 1.000 | 0.996 | 0 | 63.0 |
| Correlated Gaussian (ρ=0.9) | endpoint | verified-optimized | 614.2 | 0.035 | 0.051 | 0.975 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | endpoint | advancedhmc | 534.9 | 0.038 | 0.040 | 0.976 | 0.974 | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | multinomial | verified-optimized | 97.2 | 0.102 | 0.075 | 0.993 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | multinomial | advancedhmc | 35.7 | 0.102 | 0.173 | 0.908 | 0.954 | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | nuts | advancedhmc | 1159.6 | 0.006 | 0.012 | 1.000 | 0.948 | 0 | 122.1 |
| Correlated Gaussian (ρ=0.9) | preconditioned-endpoint | advancedhmc | 1344.0 | 0.015 | 0.016 | 0.996 | 0.995 | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | preconditioned-multinomial | advancedhmc | 282.8 | 0.039 | 0.029 | 0.909 | 0.998 | 0 | 10.0 |
| Product quartic | endpoint | verified-optimized | 23965.5 | 0.011 | 0.008 | 0.988 | — | 0 | 10.0 |
| Product quartic | endpoint | advancedhmc | 14574.5 | 0.011 | 0.007 | 0.989 | 0.988 | 0 | 10.0 |
| Product quartic | multinomial | verified-optimized | 1470.4 | 0.029 | 0.021 | 0.993 | — | 0 | 10.0 |
| Product quartic | multinomial | advancedhmc | 1460.1 | 0.030 | 0.021 | 0.908 | 0.990 | 0 | 10.0 |
| Product quartic | nuts | advancedhmc | 7209.2 | 0.006 | 0.010 | 1.000 | 0.988 | 0 | 31.0 |
| Ill-conditioned Gaussian | endpoint | verified-optimized | 10619.1 | 0.062 | 0.075 | 0.877 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | endpoint | advancedhmc | 8584.5 | 0.058 | 0.069 | 0.879 | 0.877 | 0 | 10.0 |
| Ill-conditioned Gaussian | multinomial | verified-optimized | 20503.6 | 0.145 | 0.155 | 0.993 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | multinomial | advancedhmc | 21411.9 | 0.126 | 0.149 | 0.904 | 0.896 | 0 | 10.0 |
| Ill-conditioned Gaussian | nuts | advancedhmc | 925.4 | 0.007 | 0.017 | 1.000 | 0.888 | 0 | 324.3 |
| Ill-conditioned Gaussian | preconditioned-endpoint | advancedhmc | 4825.6 | 0.017 | 0.016 | 0.996 | 0.995 | 0 | 10.0 |
| Ill-conditioned Gaussian | preconditioned-multinomial | advancedhmc | 336.7 | 0.039 | 0.041 | 0.909 | 0.998 | 0 | 10.0 |
| Regularized logistic | endpoint | verified-optimized | 7296.6 | 0.014 | 0.016 | 0.993 | — | 0 | 10.0 |
| Regularized logistic | endpoint | advancedhmc | 5162.5 | 0.014 | 0.014 | 0.993 | 0.993 | 0 | 10.0 |
| Regularized logistic | multinomial | verified-optimized | 563.0 | 0.035 | 0.034 | 0.993 | — | 0 | 10.0 |
| Regularized logistic | multinomial | advancedhmc | 630.5 | 0.033 | 0.037 | 0.909 | 0.997 | 0 | 10.0 |
| Regularized logistic | nuts | advancedhmc | 3497.9 | 0.006 | 0.017 | 1.000 | 0.994 | 0 | 50.4 |

## Interpretation

Endpoint rows are directly matched fixed-step proposals. Multinomial rows share the target and integration budget, but the packages use different trajectory construction and selection mechanics. NUTS uses variable work per transition, so its draws/s should be read together with its mean leapfrog count and not compared directly with fixed ten-step HMC.

The timing distribution describes repeated execution on one machine and is not a cross-machine confidence interval. The quality table reports acceptance, divergences, a simple autocorrelation ESS estimate, and ESS/s, but not yet ESS per gradient evaluation. These are diagnostics rather than proofs that a chain has converged.

## Quality-check roadmap

Lightweight, reproducible checks belong in the integrated Julia tests: retain the target gradient contracts and known-moment regressions, add full covariance checks for correlated Gaussian targets, and add a small set of analytically known marginal quantiles. Their tolerances must account for autocorrelation and remain stable in routine CI.

The benchmark should carry the more computational and exploratory checks:

- run multiple independently seeded chains and report between-chain diagnostics such as split rank-normalized R-hat;
- report bulk and tail ESS, preferably also per gradient evaluation;
- visualize covariance error for Gaussian targets and empirical-versus-known quantiles or ECDF differences for product targets;
- attach Monte Carlo uncertainty to moment and quantile errors instead of interpreting raw errors without a sampling scale;
- define conspicuous warning thresholds, while keeping benchmark diagnostics non-gating until their calibration is demonstrably stable.

## Targets

- **Isotropic Gaussian:** baseline identity geometry.
- **Correlated Gaussian:** AR(1) covariance with adjacent correlation `0.9`, sampled using the same identity metric to expose difficult geometry.
- **Product quartic:** independent coordinates with potential `x⁴/4 + x²/2`, adding a nonlinear strongly convex target.

- **Ill-conditioned Gaussian:** diagonal covariance ranging from `10⁻²` to `10²`; it also activates matched constant-metric algorithms.
- **Regularized logistic:** a symmetric product logistic posterior with paired labels and a standard-normal prior.

## Reproduce

```sh
make benchmark-hmc
make benchmark-report
```

Aggregate measurements are committed at [`benchmark/results/latest.csv`](https://github.com/xukai92/mcmc-lean/blob/main/benchmark/results/latest.csv), with every timing repetition in [`benchmark/results/timings.csv`](https://github.com/xukai92/mcmc-lean/blob/main/benchmark/results/timings.csv) and sampling diagnostics in [`benchmark/results/quality.csv`](https://github.com/xukai92/mcmc-lean/blob/main/benchmark/results/quality.csv).
