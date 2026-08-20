# HMC benchmark report

This is a reproducible implementation benchmark, not a theorem about convergence or a claim that Float64 execution is identical to the exact-real Lean semantics.

```@raw html
<div id="hmc-benchmark-explorer" class="benchmark-explorer" aria-label="Interactive HMC benchmark explorer">
  <p class="benchmark-loading">Loading interactive benchmark…</p>
</div>
```

The interactive chart supports metric, target, algorithm, implementation, and grouping controls. Hover over a point for its chain seed and repetition or its aggregate quality diagnostics.

Use the **Full width** control in the documentation navbar for a wider chart and table layout; the choice persists across pages.

??? note "Static chart fallback"
    The committed SVG remains available for non-JavaScript readers and portable rendering.

    ![HMC transition-throughput distributions](assets/benchmarks/hmc-throughput.svg)

Rows are grouped first by target and then by algorithm. Within each row, colors compare libraries implementing that same `target × algorithm` case. Small translucent points are complete-chain timing repetitions; large points and thick intervals are medians and IQRs. The shared logarithmic axis retains absolute throughput and remains extensible to additional libraries.

Preconditioned endpoint and multinomial rows include VerifiedSamplers' Reference and Optimized constant-metric paths.

The `nuts-complete` group gives all three implementations the same fixed `2^d` leapfrog budget. Its `verified-reference` row uses the completed-tree C.4 rerooting construction proved in Lean; the Optimized and AdvancedHMC rows use their fixed-length multinomial implementations and are work-matched rather than transition-equivalent. The separate `nuts-dynamic` group compares Optimized against AdvancedHMC under the same maximum depth and generalized U-turn termination.

## Configuration

- Commit: `5ebf46f`
- Julia: `1.12.5`
- CPU: `Intel Xeon Processor (SapphireRapids)`
- Dimension: `100`
- Draws per measured chain: `10000`
- Complete-chain timing repetitions per case: `10`
- Step size: `0.08`
- Fixed trajectory length: `10` leapfrog steps
- Shared NUTS depth budget: `4`
- Completed-tree trajectory length: `16` leapfrog steps
- Gradients: analytic callbacks for both packages; AD time excluded

- Fixed timed/quality seeds per case: `4109, 4110, 4111, 4112, 4113, 4114, 4115, 4116, 4117, 4118`
- Retained timed chains per case: `10`

## Results

### Median transitions per second

#### Endpoint

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Isotropic Gaussian | 14196 | 82076 | 22624 |
| Correlated Gaussian (ρ=0.9) | 11491 | 42149 | 19120 |
| Product quartic | 10978 | 40640 | 17618 |
| Ill-conditioned Gaussian | 10847 | 42148 | 19563 |
| Regularized logistic | 8586 | 25880 | 13440 |

#### Multinomial

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Isotropic Gaussian | 11407 | 34250 | 18936 |
| Correlated Gaussian (ρ=0.9) | 8973 | 21500 | 16266 |
| Product quartic | 8509 | 19704 | 14646 |
| Ill-conditioned Gaussian | 8130 | 21220 | 15675 |
| Regularized logistic | 5765 | 13104 | 11799 |

#### Nuts-complete

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Isotropic Gaussian | 1934 | 20174 | 11874 |
| Correlated Gaussian (ρ=0.9) | 1678 | 13153 | 10612 |
| Product quartic | 1522 | 12092 | 9772 |
| Ill-conditioned Gaussian | 1465 | 13703 | 10557 |
| Regularized logistic | 1332 | 8038 | 7798 |

#### Nuts-dynamic

| Target | verified-optimized | advancedhmc |
|---|---:|---:|
| Isotropic Gaussian | 18643 | 12029 |
| Correlated Gaussian (ρ=0.9) | 14042 | 10379 |
| Product quartic | 12825 | 9541 |
| Ill-conditioned Gaussian | 14602 | 10156 |
| Regularized logistic | 9261 | 7823 |

#### Preconditioned-endpoint

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Correlated Gaussian (ρ=0.9) | 4143 | 18974 | 10402 |
| Ill-conditioned Gaussian | 21923 | 152137 | 17290 |

#### Preconditioned-multinomial

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Correlated Gaussian (ρ=0.9) | 1805 | 15560 | 9407 |
| Ill-conditioned Gaussian | 5614 | 93878 | 14982 |

### Complete summary

| Target | Algorithm | Implementation | Median | IQR | Draws/s | Mean steps | Allocations |
|---|---|---|---:|---:|---:|---:|---:|
| Isotropic Gaussian | endpoint | verified-reference | 704.4 ms | 654.7–722.6 ms | 14196 | 10.0 | n/a |
| Isotropic Gaussian | endpoint | verified-optimized | 121.8 ms | 121.4–122.1 ms | 82076 | 10.0 | n/a |
| Isotropic Gaussian | endpoint | advancedhmc | 442.0 ms | 432.2–452.8 ms | 22624 | 10.0 | n/a |
| Isotropic Gaussian | multinomial | verified-reference | 876.7 ms | 863.4–880.7 ms | 11407 | 10.0 | n/a |
| Isotropic Gaussian | multinomial | verified-optimized | 292.0 ms | 288.7–296.2 ms | 34250 | 10.0 | n/a |
| Isotropic Gaussian | multinomial | advancedhmc | 528.1 ms | 521.3–528.9 ms | 18936 | 10.0 | n/a |
| Isotropic Gaussian | nuts-complete | verified-reference | 5169.7 ms | 5040.5–5263.6 ms | 1934 | 16.0 | n/a |
| Isotropic Gaussian | nuts-complete | verified-optimized | 495.7 ms | 493.4–498.1 ms | 20174 | 16.0 | n/a |
| Isotropic Gaussian | nuts-complete | advancedhmc | 842.2 ms | 835.7–851.8 ms | 11874 | 16.0 | n/a |
| Isotropic Gaussian | nuts-dynamic | verified-optimized | 536.4 ms | 531.0–540.3 ms | 18643 | 15.0 | n/a |
| Isotropic Gaussian | nuts-dynamic | advancedhmc | 831.3 ms | 827.6–844.4 ms | 12029 | 15.0 | n/a |
| Correlated Gaussian (ρ=0.9) | endpoint | verified-reference | 870.3 ms | 853.0–885.2 ms | 11491 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | endpoint | verified-optimized | 237.3 ms | 235.7–241.6 ms | 42149 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | endpoint | advancedhmc | 523.0 ms | 515.9–532.2 ms | 19120 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | multinomial | verified-reference | 1114.5 ms | 1106.6–1126.2 ms | 8973 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | multinomial | verified-optimized | 465.1 ms | 462.1–467.4 ms | 21500 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | multinomial | advancedhmc | 614.8 ms | 608.4–620.3 ms | 16266 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | nuts-complete | verified-reference | 5958.5 ms | 5851.9–6022.6 ms | 1678 | 16.0 | n/a |
| Correlated Gaussian (ρ=0.9) | nuts-complete | verified-optimized | 760.3 ms | 755.2–762.3 ms | 13153 | 16.0 | n/a |
| Correlated Gaussian (ρ=0.9) | nuts-complete | advancedhmc | 942.4 ms | 937.4–946.9 ms | 10612 | 16.0 | n/a |
| Correlated Gaussian (ρ=0.9) | nuts-dynamic | verified-optimized | 712.1 ms | 709.5–720.3 ms | 14042 | 15.0 | n/a |
| Correlated Gaussian (ρ=0.9) | nuts-dynamic | advancedhmc | 963.5 ms | 956.7–968.8 ms | 10379 | 15.0 | n/a |
| Correlated Gaussian (ρ=0.9) | preconditioned-endpoint | verified-reference | 2413.4 ms | 2382.4–2460.6 ms | 4143 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | preconditioned-endpoint | verified-optimized | 527.0 ms | 524.4–530.0 ms | 18974 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | preconditioned-endpoint | advancedhmc | 961.3 ms | 956.1–968.7 ms | 10402 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | preconditioned-multinomial | verified-reference | 5540.0 ms | 5506.6–5573.7 ms | 1805 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | preconditioned-multinomial | verified-optimized | 642.7 ms | 635.8–653.7 ms | 15560 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | preconditioned-multinomial | advancedhmc | 1063.0 ms | 1057.0–1068.7 ms | 9407 | 10.0 | n/a |
| Product quartic | endpoint | verified-reference | 910.9 ms | 893.7–919.7 ms | 10978 | 10.0 | n/a |
| Product quartic | endpoint | verified-optimized | 246.1 ms | 242.8–246.8 ms | 40640 | 10.0 | n/a |
| Product quartic | endpoint | advancedhmc | 567.6 ms | 563.0–573.1 ms | 17618 | 10.0 | n/a |
| Product quartic | multinomial | verified-reference | 1175.3 ms | 1171.7–1187.4 ms | 8509 | 10.0 | n/a |
| Product quartic | multinomial | verified-optimized | 507.5 ms | 501.4–512.0 ms | 19704 | 10.0 | n/a |
| Product quartic | multinomial | advancedhmc | 682.8 ms | 672.1–686.6 ms | 14646 | 10.0 | n/a |
| Product quartic | nuts-complete | verified-reference | 6570.2 ms | 6456.0–6588.5 ms | 1522 | 16.0 | n/a |
| Product quartic | nuts-complete | verified-optimized | 827.0 ms | 824.0–835.3 ms | 12092 | 16.0 | n/a |
| Product quartic | nuts-complete | advancedhmc | 1023.4 ms | 1011.2–1030.7 ms | 9772 | 16.0 | n/a |
| Product quartic | nuts-dynamic | verified-optimized | 779.8 ms | 771.9–781.3 ms | 12825 | 15.0 | n/a |
| Product quartic | nuts-dynamic | advancedhmc | 1048.1 ms | 1026.4–1057.9 ms | 9541 | 15.0 | n/a |
| Ill-conditioned Gaussian | endpoint | verified-reference | 921.9 ms | 881.2–928.9 ms | 10847 | 10.0 | n/a |
| Ill-conditioned Gaussian | endpoint | verified-optimized | 237.3 ms | 235.4–243.0 ms | 42148 | 10.0 | n/a |
| Ill-conditioned Gaussian | endpoint | advancedhmc | 511.2 ms | 509.0–515.2 ms | 19563 | 10.0 | n/a |
| Ill-conditioned Gaussian | multinomial | verified-reference | 1230.0 ms | 1213.2–1235.6 ms | 8130 | 10.0 | n/a |
| Ill-conditioned Gaussian | multinomial | verified-optimized | 471.2 ms | 467.8–475.9 ms | 21220 | 10.0 | n/a |
| Ill-conditioned Gaussian | multinomial | advancedhmc | 638.0 ms | 617.7–645.4 ms | 15675 | 10.0 | n/a |
| Ill-conditioned Gaussian | nuts-complete | verified-reference | 6824.6 ms | 6717.6–6840.5 ms | 1465 | 16.0 | n/a |
| Ill-conditioned Gaussian | nuts-complete | verified-optimized | 729.8 ms | 725.0–732.9 ms | 13703 | 16.0 | n/a |
| Ill-conditioned Gaussian | nuts-complete | advancedhmc | 947.3 ms | 942.2–955.1 ms | 10557 | 16.0 | n/a |
| Ill-conditioned Gaussian | nuts-dynamic | verified-optimized | 684.9 ms | 680.9–689.4 ms | 14602 | 15.0 | n/a |
| Ill-conditioned Gaussian | nuts-dynamic | advancedhmc | 984.7 ms | 977.6–992.6 ms | 10156 | 15.0 | n/a |
| Ill-conditioned Gaussian | preconditioned-endpoint | verified-reference | 456.1 ms | 450.9–460.2 ms | 21923 | 10.0 | n/a |
| Ill-conditioned Gaussian | preconditioned-endpoint | verified-optimized | 65.7 ms | 65.0–67.1 ms | 152137 | 10.0 | n/a |
| Ill-conditioned Gaussian | preconditioned-endpoint | advancedhmc | 578.4 ms | 573.2–580.7 ms | 17290 | 10.0 | n/a |
| Ill-conditioned Gaussian | preconditioned-multinomial | verified-reference | 1781.4 ms | 1768.5–1794.4 ms | 5614 | 10.0 | n/a |
| Ill-conditioned Gaussian | preconditioned-multinomial | verified-optimized | 106.5 ms | 104.1–109.2 ms | 93878 | 10.0 | n/a |
| Ill-conditioned Gaussian | preconditioned-multinomial | advancedhmc | 667.5 ms | 666.5–669.9 ms | 14982 | 10.0 | n/a |
| Regularized logistic | endpoint | verified-reference | 1164.7 ms | 1122.9–1174.5 ms | 8586 | 10.0 | n/a |
| Regularized logistic | endpoint | verified-optimized | 386.4 ms | 382.3–388.9 ms | 25880 | 10.0 | n/a |
| Regularized logistic | endpoint | advancedhmc | 744.0 ms | 739.0–751.0 ms | 13440 | 10.0 | n/a |
| Regularized logistic | multinomial | verified-reference | 1734.5 ms | 1719.9–1736.8 ms | 5765 | 10.0 | n/a |
| Regularized logistic | multinomial | verified-optimized | 763.1 ms | 757.5–775.4 ms | 13104 | 10.0 | n/a |
| Regularized logistic | multinomial | advancedhmc | 847.5 ms | 843.3–851.6 ms | 11799 | 10.0 | n/a |
| Regularized logistic | nuts-complete | verified-reference | 7507.1 ms | 7445.6–7577.6 ms | 1332 | 16.0 | n/a |
| Regularized logistic | nuts-complete | verified-optimized | 1244.1 ms | 1239.5–1250.5 ms | 8038 | 16.0 | n/a |
| Regularized logistic | nuts-complete | advancedhmc | 1282.5 ms | 1273.9–1301.7 ms | 7798 | 16.0 | n/a |
| Regularized logistic | nuts-dynamic | verified-optimized | 1079.8 ms | 1070.7–1091.4 ms | 9261 | 15.0 | n/a |
| Regularized logistic | nuts-dynamic | advancedhmc | 1278.4 ms | 1264.2–1294.8 ms | 7823 | 15.0 | n/a |

## Sampling quality

The same independently seeded full chains supply timing and quality evidence. Full-chain storage is included equally in every implementation's timing; diagnostics are computed afterward. Moment errors use each target's known zero mean and analytical or independently computed marginal variance. The table reports the worst split rank-normalized R-hat and minimum bulk/tail ESS among the first four coordinates after ten-percent per-chain burn-in. A warning marker at R-hat above 1.01 is conspicuous but non-gating.

| Target | Algorithm | Implementation | R-hat | Bulk ESS | Tail ESS | Bulk ESS/gradient proxy | Mean MCSE (max) | Covariance error (max) | Median error (max) | ESS/s | Mean RMSE (std.) | Variance RMSE (relative) | Movement | Acceptance | Divergences | Mean steps |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Isotropic Gaussian | endpoint | verified-reference | 1.001 | 15042.3 | 30906.0 | 0.0075 | 0.0083 | 0.0250 | 0.0298 | 2243.4 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Isotropic Gaussian | endpoint | verified-optimized | 1.001 | 15042.3 | 30906.0 | 0.0075 | 0.0083 | 0.0250 | 0.0298 | 12450.9 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Isotropic Gaussian | endpoint | advancedhmc | 1.001 | 15179.2 | 31583.1 | 0.0152 | 0.0083 | 0.0219 | 0.0203 | 3458.7 | 0.008 | 0.007 | 0.995 | 0.995 | 0 | 10.0 |
| Isotropic Gaussian | multinomial | verified-reference | 1.003 | 2768.7 | 6427.5 | 0.0014 | 0.0183 | 0.0601 | 0.0502 | 304.2 | 0.018 | 0.021 | 0.909 | — | 0 | 10.0 |
| Isotropic Gaussian | multinomial | verified-optimized | 1.003 | 2768.7 | 6427.5 | 0.0014 | 0.0183 | 0.0601 | 0.0502 | 909.6 | 0.018 | 0.021 | 0.991 | — | 0 | 10.0 |
| Isotropic Gaussian | multinomial | advancedhmc | 1.006 | 2787.5 | 6409.1 | 0.0028 | 0.0177 | 0.0608 | 0.0518 | 513.5 | 0.016 | 0.020 | 0.909 | 0.998 | 0 | 10.0 |
| Isotropic Gaussian | nuts-complete | verified-reference | 1.001 | 5919.4 | 11556.4 | 0.0018 | 0.0131 | 0.0393 | 0.0381 | 112.6 | 0.012 | 0.014 | 0.995 | — | 0 | 16.0 |
| Isotropic Gaussian | nuts-complete | verified-optimized | 1.001 | 6778.3 | 12772.2 | 0.0021 | 0.0124 | 0.0343 | 0.0360 | 1339.9 | 0.011 | 0.013 | 0.996 | — | 0 | 16.0 |
| Isotropic Gaussian | nuts-complete | advancedhmc | 1.002 | 6659.4 | 13630.9 | 0.0042 | 0.0121 | 0.0411 | 0.0338 | 812.2 | 0.011 | 0.014 | 0.941 | 0.997 | 0 | 16.0 |
| Isotropic Gaussian | nuts-dynamic | verified-optimized | 1.001 | 10480.3 | 22574.3 | 0.0035 | 0.0098 | 0.0256 | 0.0225 | 1928.8 | 0.009 | 0.008 | 1.000 | 0.997 | 0 | 15.0 |
| Isotropic Gaussian | nuts-dynamic | advancedhmc | 1.001 | 10631.5 | 21690.6 | 0.0071 | 0.0098 | 0.0285 | 0.0223 | 1302.0 | 0.009 | 0.010 | 1.000 | 0.997 | 0 | 15.0 |
| Correlated Gaussian (ρ=0.9) | endpoint | verified-reference | 1.006 | 2040.0 | 5988.2 | 0.0010 | 0.0208 | 0.0547 | 0.0402 | 228.4 | 0.019 | 0.025 | 0.973 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | endpoint | verified-optimized | 1.006 | 2040.0 | 5988.2 | 0.0010 | 0.0208 | 0.0547 | 0.0402 | 822.8 | 0.019 | 0.025 | 0.973 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | endpoint | advancedhmc | 1.005 | 2372.8 | 6405.1 | 0.0024 | 0.0212 | 0.0552 | 0.0620 | 432.1 | 0.031 | 0.026 | 0.974 | 0.974 | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | multinomial | verified-reference | ⚠ 1.020 | 537.0 | 2841.7 | 0.0003 | 0.0294 | 0.1682 | 0.0832 | 39.4 | 0.035 | 0.060 | 0.908 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | multinomial | verified-optimized | ⚠ 1.020 | 537.0 | 2841.7 | 0.0003 | 0.0294 | 0.1682 | 0.0832 | 94.2 | 0.035 | 0.060 | 0.991 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | multinomial | advancedhmc | ⚠ 1.031 | 604.4 | 2531.8 | 0.0006 | 0.0279 | 0.1029 | 0.1102 | 68.1 | 0.055 | 0.041 | 0.909 | 0.953 | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | nuts-complete | verified-reference | ⚠ 1.013 | 1003.0 | 3757.9 | 0.0003 | 0.0257 | 0.0842 | 0.0930 | 14.4 | 0.040 | 0.032 | 0.932 | — | 0 | 16.0 |
| Correlated Gaussian (ρ=0.9) | nuts-complete | verified-optimized | 1.008 | 1152.1 | 4200.8 | 0.0004 | 0.0253 | 0.0849 | 0.0457 | 125.8 | 0.022 | 0.035 | 0.996 | — | 0 | 16.0 |
| Correlated Gaussian (ρ=0.9) | nuts-complete | advancedhmc | ⚠ 1.015 | 1187.6 | 3994.8 | 0.0007 | 0.0247 | 0.0760 | 0.0755 | 99.3 | 0.039 | 0.033 | 0.940 | 0.952 | 0 | 16.0 |
| Correlated Gaussian (ρ=0.9) | nuts-dynamic | verified-optimized | 1.005 | 1410.2 | 5758.8 | 0.0005 | 0.0225 | 0.0541 | 0.0590 | 169.7 | 0.023 | 0.024 | 1.000 | 0.949 | 0 | 15.0 |
| Correlated Gaussian (ρ=0.9) | nuts-dynamic | advancedhmc | 1.003 | 1567.8 | 5410.3 | 0.0010 | 0.0227 | 0.0616 | 0.0540 | 142.8 | 0.023 | 0.029 | 1.000 | 0.949 | 0 | 15.0 |
| Correlated Gaussian (ρ=0.9) | preconditioned-endpoint | verified-reference | 1.001 | 15195.3 | 33300.2 | 0.0076 | 0.0082 | 0.0260 | 0.0286 | 649.0 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | preconditioned-endpoint | verified-optimized | 1.001 | 15195.3 | 33300.2 | 0.0138 | 0.0082 | 0.0260 | 0.0286 | 2977.7 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | preconditioned-endpoint | advancedhmc | 1.001 | 15789.1 | 32462.1 | 0.0158 | 0.0082 | 0.0194 | 0.0209 | 1650.9 | 0.010 | 0.007 | 0.995 | 0.995 | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | preconditioned-multinomial | verified-reference | 1.003 | 2704.1 | 6205.3 | 0.0014 | 0.0182 | 0.0469 | 0.0309 | 50.7 | 0.014 | 0.020 | 0.909 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | preconditioned-multinomial | verified-optimized | 1.003 | 2704.1 | 6205.3 | 0.0025 | 0.0182 | 0.0469 | 0.0309 | 433.2 | 0.014 | 0.020 | 0.909 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | preconditioned-multinomial | advancedhmc | 1.005 | 2725.7 | 6263.5 | 0.0027 | 0.0181 | 0.0577 | 0.0572 | 242.1 | 0.019 | 0.023 | 0.909 | 0.998 | 0 | 10.0 |
| Product quartic | endpoint | verified-reference | 1.000 | 36720.4 | 84182.5 | 0.0184 | 0.0038 | — | 0.0204 | 3919.4 | 0.006 | 0.004 | 0.988 | — | 0 | 10.0 |
| Product quartic | endpoint | verified-optimized | 1.000 | 36720.4 | 84182.5 | 0.0184 | 0.0038 | — | 0.0204 | 14032.7 | 0.006 | 0.004 | 0.988 | — | 0 | 10.0 |
| Product quartic | endpoint | advancedhmc | 1.000 | 36781.8 | 86589.9 | 0.0368 | 0.0037 | — | 0.0123 | 6386.5 | 0.005 | 0.004 | 0.988 | 0.988 | 0 | 10.0 |
| Product quartic | multinomial | verified-reference | 1.001 | 5888.8 | 16258.9 | 0.0029 | 0.0090 | — | 0.0298 | 483.2 | 0.012 | 0.010 | 0.909 | — | 0 | 10.0 |
| Product quartic | multinomial | verified-optimized | 1.001 | 5888.8 | 16258.9 | 0.0029 | 0.0090 | — | 0.0298 | 1136.0 | 0.012 | 0.010 | 0.991 | — | 0 | 10.0 |
| Product quartic | multinomial | advancedhmc | 1.003 | 5782.8 | 16728.8 | 0.0058 | 0.0089 | — | 0.0274 | 871.0 | 0.012 | 0.011 | 0.909 | 0.990 | 0 | 10.0 |
| Product quartic | nuts-complete | verified-reference | 1.001 | 12222.1 | 28538.8 | 0.0038 | 0.0063 | — | 0.0232 | 192.2 | 0.008 | 0.008 | 0.995 | — | 0 | 16.0 |
| Product quartic | nuts-complete | verified-optimized | 1.001 | 13995.7 | 31449.0 | 0.0044 | 0.0060 | — | 0.0199 | 1716.1 | 0.008 | 0.007 | 0.996 | — | 0 | 16.0 |
| Product quartic | nuts-complete | advancedhmc | 1.001 | 14335.6 | 32305.9 | 0.0090 | 0.0060 | — | 0.0193 | 1381.8 | 0.008 | 0.007 | 0.941 | 0.989 | 0 | 16.0 |
| Product quartic | nuts-dynamic | verified-optimized | 1.000 | 24134.2 | 54279.9 | 0.0080 | 0.0046 | — | 0.0138 | 2981.0 | 0.006 | 0.005 | 1.000 | 0.988 | 0 | 15.0 |
| Product quartic | nuts-dynamic | advancedhmc | 1.000 | 24640.2 | 54886.3 | 0.0164 | 0.0046 | — | 0.0123 | 2319.2 | 0.006 | 0.005 | 1.000 | 0.988 | 0 | 15.0 |
| Ill-conditioned Gaussian | endpoint | verified-reference | 1.001 | 16306.8 | 32614.1 | 0.0082 | 0.2984 | 16.9459 | 2.8810 | 1852.2 | 0.048 | 0.023 | 0.873 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | endpoint | verified-optimized | 1.001 | 16306.8 | 32614.1 | 0.0082 | 0.2984 | 16.9459 | 2.8810 | 6990.9 | 0.048 | 0.023 | 0.873 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | endpoint | advancedhmc | 1.000 | 16030.4 | 31434.9 | 0.0160 | 0.3020 | 8.1615 | 1.2309 | 3173.3 | 0.030 | 0.030 | 0.877 | 0.876 | 0 | 10.0 |
| Ill-conditioned Gaussian | multinomial | verified-reference | 1.000 | 79177.0 | 53043.3 | 0.0396 | 0.2795 | 20.1561 | 1.6843 | 6580.1 | 0.051 | 0.057 | 0.905 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | multinomial | verified-optimized | 1.000 | 79177.0 | 53043.3 | 0.0396 | 0.2795 | 20.1561 | 1.6843 | 17051.1 | 0.051 | 0.057 | 0.991 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | multinomial | advancedhmc | 1.000 | 79795.2 | 52953.3 | 0.0798 | 0.2680 | 19.4246 | 2.5623 | 12739.5 | 0.056 | 0.063 | 0.906 | 0.895 | 0 | 10.0 |
| Ill-conditioned Gaussian | nuts-complete | verified-reference | 1.000 | 87055.4 | 54706.2 | 0.0272 | 0.3021 | 13.3298 | 1.2211 | 1304.0 | 0.035 | 0.038 | 0.995 | — | 0 | 16.0 |
| Ill-conditioned Gaussian | nuts-complete | verified-optimized | 1.000 | 82995.2 | 55863.3 | 0.0259 | 0.3065 | 12.3651 | 1.2725 | 11736.3 | 0.035 | 0.036 | 0.996 | — | 0 | 16.0 |
| Ill-conditioned Gaussian | nuts-complete | advancedhmc | 1.000 | 86291.9 | 56109.0 | 0.0539 | 0.2859 | 13.3656 | 1.7168 | 9267.7 | 0.037 | 0.040 | 0.939 | 0.893 | 0 | 16.0 |
| Ill-conditioned Gaussian | nuts-dynamic | verified-optimized | 1.000 | 86734.3 | 54470.5 | 0.0289 | 0.2915 | 18.1091 | 1.7082 | 13146.4 | 0.032 | 0.038 | 1.000 | 0.886 | 0 | 15.0 |
| Ill-conditioned Gaussian | nuts-dynamic | advancedhmc | 1.000 | 86979.1 | 55881.0 | 0.0580 | 0.3187 | 14.4449 | 1.0218 | 9135.6 | 0.031 | 0.035 | 1.000 | 0.885 | 0 | 15.0 |
| Ill-conditioned Gaussian | preconditioned-endpoint | verified-reference | 1.001 | 15042.3 | 30906.0 | 0.0075 | 0.0798 | 1.3167 | 0.2859 | 3333.9 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | preconditioned-endpoint | verified-optimized | 1.001 | 15042.3 | 30906.0 | 0.0137 | 0.0798 | 1.3167 | 0.2859 | 22963.4 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | preconditioned-endpoint | advancedhmc | 1.001 | 15179.2 | 31583.1 | 0.0152 | 0.0764 | 1.1941 | 0.1266 | 2647.8 | 0.008 | 0.007 | 0.995 | 0.995 | 0 | 10.0 |
| Ill-conditioned Gaussian | preconditioned-multinomial | verified-reference | 1.003 | 2768.7 | 6427.5 | 0.0014 | 0.1737 | 2.8200 | 0.2501 | 149.8 | 0.018 | 0.021 | 0.909 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | preconditioned-multinomial | verified-optimized | 1.003 | 2768.7 | 6427.5 | 0.0025 | 0.1737 | 2.8200 | 0.2501 | 2495.1 | 0.018 | 0.021 | 0.909 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | preconditioned-multinomial | advancedhmc | 1.006 | 2787.5 | 6409.1 | 0.0028 | 0.1670 | 3.4796 | 0.3842 | 405.0 | 0.016 | 0.020 | 0.909 | 0.998 | 0 | 10.0 |
| Regularized logistic | endpoint | verified-reference | 1.000 | 23123.2 | 41791.1 | 0.0116 | 0.0057 | — | 0.0208 | 2000.1 | 0.007 | 0.008 | 0.992 | — | 0 | 10.0 |
| Regularized logistic | endpoint | verified-optimized | 1.000 | 23123.2 | 41791.1 | 0.0116 | 0.0057 | — | 0.0208 | 5922.1 | 0.007 | 0.008 | 0.992 | — | 0 | 10.0 |
| Regularized logistic | endpoint | advancedhmc | 1.001 | 23430.9 | 41867.0 | 0.0234 | 0.0057 | — | 0.0130 | 3183.1 | 0.007 | 0.007 | 0.992 | 0.992 | 0 | 10.0 |
| Regularized logistic | multinomial | verified-reference | 1.002 | 4012.4 | 8207.9 | 0.0020 | 0.0131 | — | 0.0326 | 223.8 | 0.014 | 0.018 | 0.909 | — | 0 | 10.0 |
| Regularized logistic | multinomial | verified-optimized | 1.002 | 4012.4 | 8207.9 | 0.0020 | 0.0131 | — | 0.0326 | 506.5 | 0.014 | 0.018 | 0.991 | — | 0 | 10.0 |
| Regularized logistic | multinomial | advancedhmc | 1.004 | 3894.3 | 8449.2 | 0.0039 | 0.0128 | — | 0.0357 | 455.1 | 0.014 | 0.018 | 0.909 | 0.997 | 0 | 10.0 |
| Regularized logistic | nuts-complete | verified-reference | 1.001 | 8413.0 | 14982.2 | 0.0026 | 0.0093 | — | 0.0277 | 110.2 | 0.010 | 0.013 | 0.995 | — | 0 | 16.0 |
| Regularized logistic | nuts-complete | verified-optimized | 1.001 | 9495.5 | 16252.8 | 0.0030 | 0.0088 | — | 0.0227 | 792.2 | 0.009 | 0.012 | 0.996 | — | 0 | 16.0 |
| Regularized logistic | nuts-complete | advancedhmc | 1.002 | 9759.9 | 17582.0 | 0.0061 | 0.0086 | — | 0.0239 | 758.3 | 0.009 | 0.012 | 0.941 | 0.996 | 0 | 16.0 |
| Regularized logistic | nuts-dynamic | verified-optimized | 1.001 | 15585.4 | 29600.1 | 0.0052 | 0.0068 | — | 0.0166 | 1384.0 | 0.007 | 0.007 | 1.000 | 0.996 | 0 | 15.0 |
| Regularized logistic | nuts-dynamic | advancedhmc | 1.001 | 15993.2 | 29018.0 | 0.0107 | 0.0068 | — | 0.0151 | 1288.7 | 0.008 | 0.008 | 1.000 | 0.996 | 0 | 15.0 |

## Interpretation

Endpoint rows are directly matched fixed-step proposals. Multinomial rows share the target and integration budget, but the packages use different trajectory construction and selection mechanics. `nuts-complete` rows have the same fixed depth-derived work budget but are not transition-equivalent. `nuts-dynamic` rows use variable work up to that shared budget, so their draws/s should be read together with mean leapfrog count.

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
