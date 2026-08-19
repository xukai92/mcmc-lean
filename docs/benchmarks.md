# HMC benchmark report

This is a reproducible implementation benchmark, not a theorem about convergence or a claim that Float64 execution is identical to the exact-real Lean semantics.

![HMC transition-throughput distributions](assets/benchmarks/hmc-throughput.svg)

Rows are grouped first by target and then by algorithm. Within each row, colors compare libraries implementing that same `target × algorithm` case. Small translucent points are complete-chain timing repetitions; large points and thick intervals are medians and IQRs. The shared logarithmic axis retains absolute throughput and remains extensible to additional libraries.

Preconditioned endpoint and multinomial rows include VerifiedSamplers' Reference and Optimized constant-metric paths.

VerifiedSamplers NUTS is labelled `verified-runtime`, not `verified-reference`: the production-shaped implementation is tested, while full Lean transition correspondence remains open.

## Configuration

- Commit: `186f4bc`
- Julia: `1.12.5`
- CPU: `Intel Xeon Processor (SapphireRapids)`
- Dimension: `100`
- Draws per measured chain: `10000`
- Complete-chain timing repetitions per case: `10`
- Step size: `0.08`
- Fixed trajectory length: `10` leapfrog steps
- Gradients: analytic callbacks for both packages; AD time excluded

- Fixed timed/quality seeds per case: `4109, 4110, 4111, 4112, 4113, 4114, 4115, 4116, 4117, 4118`
- Retained timed chains per case: `10`

## Results

### Median transitions per second

#### Endpoint

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Isotropic Gaussian | 17254 | 84002 | 23627 |
| Correlated Gaussian (ρ=0.9) | 8865 | 23686 | 12983 |
| Product quartic | 12854 | 42502 | 19027 |
| Ill-conditioned Gaussian | 12303 | 41937 | 18650 |
| Regularized logistic | 9125 | 27226 | 13280 |

#### Multinomial

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Isotropic Gaussian | 11421 | 35439 | 19472 |
| Correlated Gaussian (ρ=0.9) | 5414 | 11319 | 12025 |
| Product quartic | 8935 | 20487 | 15571 |
| Ill-conditioned Gaussian | 8219 | 20325 | 14892 |
| Regularized logistic | 5610 | 12409 | 11663 |

#### Nuts

| Target | advancedhmc | verified-runtime |
|---|---:|---:|
| Isotropic Gaussian | 5234 | 5003 |
| Correlated Gaussian (ρ=0.9) | 1456 | 1286 |
| Product quartic | 6246 | 6295 |
| Ill-conditioned Gaussian | 752 | 918 |
| Regularized logistic | 2911 | 2973 |

#### Preconditioned-endpoint

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Correlated Gaussian (ρ=0.9) | 3693 | 5130 | 8438 |
| Ill-conditioned Gaussian | 23128 | 72399 | 16869 |

#### Preconditioned-multinomial

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Correlated Gaussian (ρ=0.9) | 1598 | 3082 | 7938 |
| Ill-conditioned Gaussian | 6207 | 15269 | 13657 |

### Complete summary

| Target | Algorithm | Implementation | Median | IQR | Draws/s | Mean steps | Allocations |
|---|---|---|---:|---:|---:|---:|---:|
| Isotropic Gaussian | endpoint | verified-reference | 579.6 ms | 557.3–601.5 ms | 17254 | 10.0 | n/a |
| Isotropic Gaussian | endpoint | verified-optimized | 119.0 ms | 118.3–119.6 ms | 84002 | 10.0 | n/a |
| Isotropic Gaussian | endpoint | advancedhmc | 423.2 ms | 421.0–426.8 ms | 23627 | 10.0 | n/a |
| Isotropic Gaussian | multinomial | verified-reference | 875.6 ms | 868.8–877.7 ms | 11421 | 10.0 | n/a |
| Isotropic Gaussian | multinomial | verified-optimized | 282.2 ms | 281.2–282.9 ms | 35439 | 10.0 | n/a |
| Isotropic Gaussian | multinomial | advancedhmc | 513.6 ms | 511.9–515.0 ms | 19472 | 10.0 | n/a |
| Isotropic Gaussian | nuts | verified-runtime | 1998.9 ms | 1950.0–2038.7 ms | 5003 | 63.0 | n/a |
| Isotropic Gaussian | nuts | advancedhmc | 1910.6 ms | 1850.1–1939.2 ms | 5234 | 63.0 | n/a |
| Correlated Gaussian (ρ=0.9) | endpoint | verified-reference | 1128.0 ms | 1118.1–1138.2 ms | 8865 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | endpoint | verified-optimized | 422.2 ms | 421.1–424.7 ms | 23686 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | endpoint | advancedhmc | 770.2 ms | 740.2–778.8 ms | 12983 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | multinomial | verified-reference | 1847.0 ms | 1827.2–1855.5 ms | 5414 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | multinomial | verified-optimized | 883.5 ms | 878.9–891.0 ms | 11319 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | multinomial | advancedhmc | 831.6 ms | 829.9–847.3 ms | 12025 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | nuts | verified-runtime | 7774.6 ms | 7592.9–7836.5 ms | 1286 | 122.6 | n/a |
| Correlated Gaussian (ρ=0.9) | nuts | advancedhmc | 6866.5 ms | 6614.1–6995.2 ms | 1456 | 122.4 | n/a |
| Correlated Gaussian (ρ=0.9) | preconditioned-endpoint | verified-reference | 2707.8 ms | 2599.8–2733.5 ms | 3693 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | preconditioned-endpoint | verified-optimized | 1949.2 ms | 1930.5–1962.8 ms | 5130 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | preconditioned-endpoint | advancedhmc | 1185.1 ms | 1175.3–1192.9 ms | 8438 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | preconditioned-multinomial | verified-reference | 6258.5 ms | 5981.4–6290.9 ms | 1598 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | preconditioned-multinomial | verified-optimized | 3244.3 ms | 3232.7–3253.2 ms | 3082 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | preconditioned-multinomial | advancedhmc | 1259.7 ms | 1253.8–1284.0 ms | 7938 | 10.0 | n/a |
| Product quartic | endpoint | verified-reference | 778.0 ms | 765.8–780.4 ms | 12854 | 10.0 | n/a |
| Product quartic | endpoint | verified-optimized | 235.3 ms | 232.3–238.9 ms | 42502 | 10.0 | n/a |
| Product quartic | endpoint | advancedhmc | 525.6 ms | 520.5–532.8 ms | 19027 | 10.0 | n/a |
| Product quartic | multinomial | verified-reference | 1119.1 ms | 1112.8–1164.3 ms | 8935 | 10.0 | n/a |
| Product quartic | multinomial | verified-optimized | 488.1 ms | 485.0–490.7 ms | 20487 | 10.0 | n/a |
| Product quartic | multinomial | advancedhmc | 642.2 ms | 639.8–644.3 ms | 15571 | 10.0 | n/a |
| Product quartic | nuts | verified-runtime | 1588.6 ms | 1585.1–1597.0 ms | 6295 | 31.0 | n/a |
| Product quartic | nuts | advancedhmc | 1601.1 ms | 1596.9–1610.2 ms | 6246 | 31.0 | n/a |
| Ill-conditioned Gaussian | endpoint | verified-reference | 812.8 ms | 800.2–825.4 ms | 12303 | 10.0 | n/a |
| Ill-conditioned Gaussian | endpoint | verified-optimized | 238.5 ms | 237.8–240.0 ms | 41937 | 10.0 | n/a |
| Ill-conditioned Gaussian | endpoint | advancedhmc | 536.2 ms | 532.0–541.1 ms | 18650 | 10.0 | n/a |
| Ill-conditioned Gaussian | multinomial | verified-reference | 1216.7 ms | 1205.3–1227.5 ms | 8219 | 10.0 | n/a |
| Ill-conditioned Gaussian | multinomial | verified-optimized | 492.0 ms | 490.9–493.0 ms | 20325 | 10.0 | n/a |
| Ill-conditioned Gaussian | multinomial | advancedhmc | 671.5 ms | 669.9–674.4 ms | 14892 | 10.0 | n/a |
| Ill-conditioned Gaussian | nuts | verified-runtime | 10894.0 ms | 10769.5–11286.9 ms | 918 | 323.1 | n/a |
| Ill-conditioned Gaussian | nuts | advancedhmc | 13302.6 ms | 12725.4–13562.2 ms | 752 | 323.4 | n/a |
| Ill-conditioned Gaussian | preconditioned-endpoint | verified-reference | 432.4 ms | 430.3–435.3 ms | 23128 | 10.0 | n/a |
| Ill-conditioned Gaussian | preconditioned-endpoint | verified-optimized | 138.1 ms | 137.1–139.4 ms | 72399 | 10.0 | n/a |
| Ill-conditioned Gaussian | preconditioned-endpoint | advancedhmc | 592.8 ms | 591.8–596.3 ms | 16869 | 10.0 | n/a |
| Ill-conditioned Gaussian | preconditioned-multinomial | verified-reference | 1611.0 ms | 1601.9–1620.6 ms | 6207 | 10.0 | n/a |
| Ill-conditioned Gaussian | preconditioned-multinomial | verified-optimized | 654.9 ms | 652.9–656.3 ms | 15269 | 10.0 | n/a |
| Ill-conditioned Gaussian | preconditioned-multinomial | advancedhmc | 732.2 ms | 728.8–737.2 ms | 13657 | 10.0 | n/a |
| Regularized logistic | endpoint | verified-reference | 1095.9 ms | 1086.1–1101.2 ms | 9125 | 10.0 | n/a |
| Regularized logistic | endpoint | verified-optimized | 367.3 ms | 364.7–368.9 ms | 27226 | 10.0 | n/a |
| Regularized logistic | endpoint | advancedhmc | 753.0 ms | 749.6–758.8 ms | 13280 | 10.0 | n/a |
| Regularized logistic | multinomial | verified-reference | 1782.4 ms | 1721.0–1802.1 ms | 5610 | 10.0 | n/a |
| Regularized logistic | multinomial | verified-optimized | 805.9 ms | 797.2–813.3 ms | 12409 | 10.0 | n/a |
| Regularized logistic | multinomial | advancedhmc | 857.4 ms | 851.1–863.2 ms | 11663 | 10.0 | n/a |
| Regularized logistic | nuts | verified-runtime | 3364.1 ms | 3344.6–3386.3 ms | 2973 | 50.4 | n/a |
| Regularized logistic | nuts | advancedhmc | 3435.1 ms | 3398.9–3461.2 ms | 2911 | 50.4 | n/a |

## Sampling quality

The same independently seeded full chains supply timing and quality evidence. Full-chain storage is included equally in every implementation's timing; diagnostics are computed afterward. Moment errors use each target's known zero mean and analytical or independently computed marginal variance. The table reports the worst split rank-normalized R-hat and minimum bulk/tail ESS among the first four coordinates after ten-percent per-chain burn-in. A warning marker at R-hat above 1.01 is conspicuous but non-gating.

| Target | Algorithm | Implementation | R-hat | Bulk ESS | Tail ESS | Bulk ESS/gradient proxy | Mean MCSE (max) | Covariance error (max) | Median error (max) | ESS/s | Mean RMSE (std.) | Variance RMSE (relative) | Movement | Acceptance | Divergences | Mean steps |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Isotropic Gaussian | endpoint | verified-reference | 1.001 | 15042.3 | 30906.0 | 0.0075 | 0.0083 | 0.0250 | 0.0298 | 2688.8 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Isotropic Gaussian | endpoint | verified-optimized | 1.001 | 15042.3 | 30906.0 | 0.0075 | 0.0083 | 0.0250 | 0.0298 | 12707.9 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Isotropic Gaussian | endpoint | advancedhmc | 1.001 | 15179.2 | 31583.1 | 0.0152 | 0.0083 | 0.0219 | 0.0203 | 3594.0 | 0.008 | 0.007 | 0.995 | 0.995 | 0 | 10.0 |
| Isotropic Gaussian | multinomial | verified-reference | 1.003 | 2768.7 | 6427.5 | 0.0014 | 0.0183 | 0.0601 | 0.0502 | 304.6 | 0.018 | 0.021 | 0.909 | — | 0 | 10.0 |
| Isotropic Gaussian | multinomial | verified-optimized | 1.003 | 2768.7 | 6427.5 | 0.0014 | 0.0183 | 0.0601 | 0.0502 | 940.8 | 0.018 | 0.021 | 0.991 | — | 0 | 10.0 |
| Isotropic Gaussian | multinomial | advancedhmc | 1.006 | 2787.5 | 6409.1 | 0.0028 | 0.0177 | 0.0608 | 0.0518 | 527.8 | 0.016 | 0.020 | 0.909 | 0.998 | 0 | 10.0 |
| Isotropic Gaussian | nuts | verified-runtime | 1.000 | 90000.0 | 68651.3 | 0.0071 | 0.0021 | 0.0219 | 0.0072 | 4513.4 | 0.002 | 0.008 | 1.000 | 0.996 | 0 | 63.0 |
| Isotropic Gaussian | nuts | advancedhmc | 1.000 | 90000.0 | 67827.6 | 0.0143 | 0.0022 | 0.0233 | 0.0071 | 4733.6 | 0.002 | 0.009 | 1.000 | 0.996 | 0 | 63.0 |
| Correlated Gaussian (ρ=0.9) | endpoint | verified-reference | 1.006 | 2040.0 | 5988.2 | 0.0010 | 0.0208 | 0.0547 | 0.0402 | 174.0 | 0.019 | 0.025 | 0.973 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | endpoint | verified-optimized | 1.006 | 2040.0 | 5988.2 | 0.0010 | 0.0208 | 0.0547 | 0.0402 | 464.3 | 0.019 | 0.025 | 0.973 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | endpoint | advancedhmc | 1.005 | 2372.8 | 6405.1 | 0.0024 | 0.0212 | 0.0552 | 0.0620 | 297.9 | 0.031 | 0.026 | 0.974 | 0.974 | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | multinomial | verified-reference | ⚠ 1.020 | 537.0 | 2841.7 | 0.0003 | 0.0294 | 0.1682 | 0.0832 | 23.9 | 0.035 | 0.060 | 0.908 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | multinomial | verified-optimized | ⚠ 1.020 | 537.0 | 2841.7 | 0.0003 | 0.0294 | 0.1682 | 0.0832 | 49.8 | 0.035 | 0.060 | 0.991 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | multinomial | advancedhmc | ⚠ 1.031 | 604.4 | 2531.8 | 0.0006 | 0.0279 | 0.1029 | 0.1102 | 50.0 | 0.055 | 0.041 | 0.909 | 0.953 | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | nuts | verified-runtime | 1.000 | 64132.9 | 65822.9 | 0.0026 | 0.0045 | 0.0123 | 0.0105 | 837.4 | 0.004 | 0.005 | 1.000 | 0.948 | 0 | 122.6 |
| Correlated Gaussian (ρ=0.9) | nuts | advancedhmc | 1.000 | 62565.6 | 67093.6 | 0.0051 | 0.0046 | 0.0125 | 0.0128 | 930.2 | 0.003 | 0.006 | 1.000 | 0.948 | 0 | 122.4 |
| Correlated Gaussian (ρ=0.9) | preconditioned-endpoint | verified-reference | 1.001 | 15195.3 | 33300.2 | 0.0076 | 0.0082 | 0.0260 | 0.0286 | 587.6 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | preconditioned-endpoint | verified-optimized | 1.001 | 15195.3 | 33300.2 | 0.0076 | 0.0082 | 0.0260 | 0.0286 | 810.3 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | preconditioned-endpoint | advancedhmc | 1.001 | 15789.1 | 32462.1 | 0.0158 | 0.0082 | 0.0194 | 0.0209 | 1344.4 | 0.010 | 0.007 | 0.995 | 0.995 | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | preconditioned-multinomial | verified-reference | 1.003 | 2704.1 | 6205.3 | 0.0014 | 0.0182 | 0.0469 | 0.0309 | 45.5 | 0.014 | 0.020 | 0.909 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | preconditioned-multinomial | verified-optimized | 1.003 | 2704.1 | 6205.3 | 0.0014 | 0.0182 | 0.0469 | 0.0309 | 86.7 | 0.014 | 0.020 | 0.991 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | preconditioned-multinomial | advancedhmc | 1.005 | 2725.7 | 6263.5 | 0.0027 | 0.0181 | 0.0577 | 0.0572 | 201.7 | 0.019 | 0.023 | 0.909 | 0.998 | 0 | 10.0 |
| Product quartic | endpoint | verified-reference | 1.000 | 36720.4 | 84182.5 | 0.0184 | 0.0038 | — | 0.0204 | 4472.7 | 0.006 | 0.004 | 0.988 | — | 0 | 10.0 |
| Product quartic | endpoint | verified-optimized | 1.000 | 36720.4 | 84182.5 | 0.0184 | 0.0038 | — | 0.0204 | 14569.1 | 0.006 | 0.004 | 0.988 | — | 0 | 10.0 |
| Product quartic | endpoint | advancedhmc | 1.000 | 36781.8 | 86589.9 | 0.0368 | 0.0037 | — | 0.0123 | 6845.9 | 0.005 | 0.004 | 0.988 | 0.988 | 0 | 10.0 |
| Product quartic | multinomial | verified-reference | 1.001 | 5888.8 | 16258.9 | 0.0029 | 0.0090 | — | 0.0298 | 502.0 | 0.012 | 0.010 | 0.909 | — | 0 | 10.0 |
| Product quartic | multinomial | verified-optimized | 1.001 | 5888.8 | 16258.9 | 0.0029 | 0.0090 | — | 0.0298 | 1164.7 | 0.012 | 0.010 | 0.991 | — | 0 | 10.0 |
| Product quartic | multinomial | advancedhmc | 1.003 | 5782.8 | 16728.8 | 0.0058 | 0.0089 | — | 0.0274 | 924.5 | 0.012 | 0.011 | 0.909 | 0.990 | 0 | 10.0 |
| Product quartic | nuts | verified-runtime | 1.000 | 90000.0 | 76482.6 | 0.0145 | 0.0020 | — | 0.0100 | 5658.8 | 0.003 | 0.005 | 1.000 | 0.988 | 0 | 31.0 |
| Product quartic | nuts | advancedhmc | 1.000 | 90000.0 | 78149.5 | 0.0290 | 0.0021 | — | 0.0070 | 5609.0 | 0.003 | 0.006 | 1.000 | 0.988 | 0 | 31.0 |
| Ill-conditioned Gaussian | endpoint | verified-reference | 1.001 | 16306.8 | 32614.1 | 0.0082 | 0.2984 | 16.9459 | 2.8810 | 2071.9 | 0.048 | 0.023 | 0.873 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | endpoint | verified-optimized | 1.001 | 16306.8 | 32614.1 | 0.0082 | 0.2984 | 16.9459 | 2.8810 | 6983.7 | 0.048 | 0.023 | 0.873 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | endpoint | advancedhmc | 1.000 | 16030.4 | 31434.9 | 0.0160 | 0.3020 | 8.1615 | 1.2309 | 3037.1 | 0.030 | 0.030 | 0.877 | 0.876 | 0 | 10.0 |
| Ill-conditioned Gaussian | multinomial | verified-reference | 1.000 | 79177.0 | 53043.3 | 0.0396 | 0.2795 | 20.1561 | 1.6843 | 6639.5 | 0.051 | 0.057 | 0.905 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | multinomial | verified-optimized | 1.000 | 79177.0 | 53043.3 | 0.0396 | 0.2795 | 20.1561 | 1.6843 | 16346.7 | 0.051 | 0.057 | 0.991 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | multinomial | advancedhmc | 1.000 | 79795.2 | 52953.3 | 0.0798 | 0.2680 | 19.4246 | 2.5623 | 11994.3 | 0.056 | 0.063 | 0.906 | 0.895 | 0 | 10.0 |
| Ill-conditioned Gaussian | nuts | verified-runtime | 1.000 | 87473.8 | 58750.0 | 0.0014 | 0.0529 | 1.3289 | 0.0390 | 806.9 | 0.003 | 0.008 | 1.000 | 0.888 | 0 | 323.1 |
| Ill-conditioned Gaussian | nuts | advancedhmc | 1.000 | 86754.6 | 55567.6 | 0.0027 | 0.0522 | 0.6444 | 0.0697 | 669.3 | 0.003 | 0.008 | 1.000 | 0.889 | 0 | 323.4 |
| Ill-conditioned Gaussian | preconditioned-endpoint | verified-reference | 1.001 | 15042.3 | 30906.0 | 0.0075 | 0.0798 | 1.3167 | 0.2859 | 3510.8 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | preconditioned-endpoint | verified-optimized | 1.001 | 15042.3 | 30906.0 | 0.0075 | 0.0798 | 1.3167 | 0.2859 | 10873.1 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | preconditioned-endpoint | advancedhmc | 1.001 | 15179.2 | 31583.1 | 0.0152 | 0.0764 | 1.1941 | 0.1266 | 2573.8 | 0.008 | 0.007 | 0.995 | 0.995 | 0 | 10.0 |
| Ill-conditioned Gaussian | preconditioned-multinomial | verified-reference | 1.003 | 2768.7 | 6427.5 | 0.0014 | 0.1737 | 2.8200 | 0.2501 | 165.1 | 0.018 | 0.021 | 0.909 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | preconditioned-multinomial | verified-optimized | 1.003 | 2768.7 | 6427.5 | 0.0014 | 0.1737 | 2.8200 | 0.2501 | 405.3 | 0.018 | 0.021 | 0.991 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | preconditioned-multinomial | advancedhmc | 1.006 | 2787.5 | 6409.1 | 0.0028 | 0.1670 | 3.4796 | 0.3842 | 369.9 | 0.016 | 0.020 | 0.909 | 0.998 | 0 | 10.0 |
| Regularized logistic | endpoint | verified-reference | 1.000 | 23123.2 | 41791.1 | 0.0116 | 0.0057 | — | 0.0208 | 2090.5 | 0.007 | 0.008 | 0.992 | — | 0 | 10.0 |
| Regularized logistic | endpoint | verified-optimized | 1.000 | 23123.2 | 41791.1 | 0.0116 | 0.0057 | — | 0.0208 | 6213.5 | 0.007 | 0.008 | 0.992 | — | 0 | 10.0 |
| Regularized logistic | endpoint | advancedhmc | 1.001 | 23430.9 | 41867.0 | 0.0234 | 0.0057 | — | 0.0130 | 3140.8 | 0.007 | 0.007 | 0.992 | 0.992 | 0 | 10.0 |
| Regularized logistic | multinomial | verified-reference | 1.002 | 4012.4 | 8207.9 | 0.0020 | 0.0131 | — | 0.0326 | 218.6 | 0.014 | 0.018 | 0.909 | — | 0 | 10.0 |
| Regularized logistic | multinomial | verified-optimized | 1.002 | 4012.4 | 8207.9 | 0.0020 | 0.0131 | — | 0.0326 | 480.8 | 0.014 | 0.018 | 0.991 | — | 0 | 10.0 |
| Regularized logistic | multinomial | advancedhmc | 1.004 | 3894.3 | 8449.2 | 0.0039 | 0.0128 | — | 0.0357 | 450.4 | 0.014 | 0.018 | 0.909 | 0.997 | 0 | 10.0 |
| Regularized logistic | nuts | verified-runtime | 1.000 | 90000.0 | 64685.4 | 0.0089 | 0.0024 | — | 0.0069 | 2679.4 | 0.003 | 0.008 | 1.000 | 0.994 | 0 | 50.4 |
| Regularized logistic | nuts | advancedhmc | 1.000 | 90000.0 | 66197.1 | 0.0178 | 0.0024 | — | 0.0085 | 2624.1 | 0.003 | 0.008 | 1.000 | 0.994 | 0 | 50.4 |

## Interpretation

Endpoint rows are directly matched fixed-step proposals. Multinomial rows share the target and integration budget, but the packages use different trajectory construction and selection mechanics. NUTS uses variable work per transition, so its draws/s should be read together with its mean leapfrog count and not compared directly with fixed ten-step HMC.

The timing distribution describes repeated execution on one machine and is not a cross-machine confidence interval. The quality table reports acceptance, divergences, autocorrelation ESS, and—on new runs—split rank-normalized R-hat plus bulk/tail ESS. The ESS/gradient column is explicitly a work proxy: it divides bulk ESS by recorded leapfrog work, using two gradient callbacks per maintained direct leapfrog step and one per AdvancedHMC-reported step. It is not an instrumented hardware counter. These are diagnostics rather than proofs that a chain has converged.

## Quality-check roadmap

Lightweight, reproducible checks belong in the integrated Julia tests: retain the target gradient contracts and known-moment regressions, add full covariance checks for correlated Gaussian targets, and add a small set of analytically known marginal quantiles. Their tolerances must account for autocorrelation and remain stable in routine CI.

The benchmark now runs independently seeded quality chains and reports split rank-normalized R-hat, bulk/tail ESS, and a clearly labelled gradient-work proxy. Remaining exploratory improvements are:

- add raw-chain covariance and ECDF plots; new runs already record maximum Gaussian covariance error and symmetry-implied marginal median error;
- extend the recorded batch-means mean MCSE to uncertainty intervals for covariance and quantile errors;
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
