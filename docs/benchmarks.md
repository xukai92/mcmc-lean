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

Endpoint and multinomial labels ending in `-dense` or `-diagonal` include VerifiedSamplers' Reference and Optimized constant-metric paths.

The `nuts-complete` group gives all three implementations the same fixed `2^d` leapfrog budget. Its `verified-reference` row uses the completed-tree C.4 rerooting construction proved in Lean; the Optimized and AdvancedHMC rows use their fixed-length multinomial implementations and are work-matched rather than transition-equivalent. The separate `nuts-dynamic` group compares Optimized against AdvancedHMC under the same maximum depth and generalized U-turn termination.

## Configuration

- Commit: `c92571c`
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
| Isotropic Gaussian | 13929 | 80436 | 22890 |
| Correlated Gaussian (ρ=0.9) | 11340 | 41858 | 19167 |
| Product quartic | 11186 | 41399 | 18237 |
| Ill-conditioned Gaussian | 11034 | 43042 | 19957 |
| Regularized logistic | 8690 | 26034 | 13422 |

#### Multinomial

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Isotropic Gaussian | 11153 | 34394 | 18696 |
| Correlated Gaussian (ρ=0.9) | 8921 | 21681 | 16286 |
| Product quartic | 8497 | 20212 | 14872 |
| Ill-conditioned Gaussian | 8346 | 22162 | 16845 |
| Regularized logistic | 5569 | 12604 | 11552 |

#### Nuts-complete

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Isotropic Gaussian | 1826 | 20128 | 11983 |
| Correlated Gaussian (ρ=0.9) | 1653 | 12868 | 10643 |
| Product quartic | 1550 | 12691 | 9886 |
| Ill-conditioned Gaussian | 1485 | 14093 | 10882 |
| Regularized logistic | 1309 | 7786 | 7607 |

#### Nuts-dynamic

| Target | verified-optimized | advancedhmc |
|---|---:|---:|
| Isotropic Gaussian | 19006 | 11712 |
| Correlated Gaussian (ρ=0.9) | 13804 | 10219 |
| Product quartic | 12948 | 9853 |
| Ill-conditioned Gaussian | 15183 | 10351 |
| Regularized logistic | 9165 | 7617 |

#### Endpoint-dense

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Correlated Gaussian (ρ=0.9) | 3960 | 19573 | 10321 |

#### Multinomial-dense

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Correlated Gaussian (ρ=0.9) | 1771 | 15502 | 9360 |

#### Endpoint-diagonal

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Ill-conditioned Gaussian | 22755 | 155318 | 18112 |

#### Multinomial-diagonal

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Ill-conditioned Gaussian | 5843 | 97091 | 15100 |

### Complete summary

| Target | Algorithm | Implementation | Median | IQR | Draws/s | Mean steps | Allocations |
|---|---|---|---:|---:|---:|---:|---:|
| Isotropic Gaussian | endpoint | verified-reference | 717.9 ms | 708.4–724.3 ms | 13929 | 10.0 | n/a |
| Isotropic Gaussian | endpoint | verified-optimized | 124.3 ms | 123.7–124.6 ms | 80436 | 10.0 | n/a |
| Isotropic Gaussian | endpoint | advancedhmc | 436.9 ms | 436.5–440.5 ms | 22890 | 10.0 | n/a |
| Isotropic Gaussian | multinomial | verified-reference | 896.6 ms | 890.7–899.5 ms | 11153 | 10.0 | n/a |
| Isotropic Gaussian | multinomial | verified-optimized | 290.7 ms | 288.4–293.0 ms | 34394 | 10.0 | n/a |
| Isotropic Gaussian | multinomial | advancedhmc | 534.9 ms | 532.7–537.6 ms | 18696 | 10.0 | n/a |
| Isotropic Gaussian | nuts-complete | verified-reference | 5476.3 ms | 5361.0–5573.7 ms | 1826 | 16.0 | n/a |
| Isotropic Gaussian | nuts-complete | verified-optimized | 496.8 ms | 493.6–499.8 ms | 20128 | 16.0 | n/a |
| Isotropic Gaussian | nuts-complete | advancedhmc | 834.5 ms | 832.8–840.0 ms | 11983 | 16.0 | n/a |
| Isotropic Gaussian | nuts-dynamic | verified-optimized | 526.2 ms | 524.9–527.9 ms | 19006 | 15.0 | n/a |
| Isotropic Gaussian | nuts-dynamic | advancedhmc | 853.8 ms | 851.4–864.8 ms | 11712 | 15.0 | n/a |
| Correlated Gaussian (ρ=0.9) | endpoint | verified-reference | 881.8 ms | 877.4–909.7 ms | 11340 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | endpoint | verified-optimized | 238.9 ms | 237.6–239.9 ms | 41858 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | endpoint | advancedhmc | 521.7 ms | 515.6–528.9 ms | 19167 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | multinomial | verified-reference | 1121.0 ms | 1114.4–1125.6 ms | 8921 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | multinomial | verified-optimized | 461.2 ms | 444.3–480.1 ms | 21681 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | multinomial | advancedhmc | 614.0 ms | 610.0–627.9 ms | 16286 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | nuts-complete | verified-reference | 6051.2 ms | 5973.4–6099.6 ms | 1653 | 16.0 | n/a |
| Correlated Gaussian (ρ=0.9) | nuts-complete | verified-optimized | 777.1 ms | 770.4–786.8 ms | 12868 | 16.0 | n/a |
| Correlated Gaussian (ρ=0.9) | nuts-complete | advancedhmc | 939.6 ms | 932.9–945.0 ms | 10643 | 16.0 | n/a |
| Correlated Gaussian (ρ=0.9) | nuts-dynamic | verified-optimized | 724.4 ms | 722.9–730.3 ms | 13804 | 15.0 | n/a |
| Correlated Gaussian (ρ=0.9) | nuts-dynamic | advancedhmc | 978.6 ms | 976.3–985.4 ms | 10219 | 15.0 | n/a |
| Correlated Gaussian (ρ=0.9) | endpoint-dense | verified-reference | 2525.4 ms | 2518.3–2537.4 ms | 3960 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | endpoint-dense | verified-optimized | 510.9 ms | 509.8–512.0 ms | 19573 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | endpoint-dense | advancedhmc | 968.9 ms | 962.8–971.7 ms | 10321 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | multinomial-dense | verified-reference | 5648.0 ms | 5624.5–5701.6 ms | 1771 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | multinomial-dense | verified-optimized | 645.1 ms | 642.3–647.4 ms | 15502 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | multinomial-dense | advancedhmc | 1068.3 ms | 1062.6–1073.9 ms | 9360 | 10.0 | n/a |
| Product quartic | endpoint | verified-reference | 894.0 ms | 883.1–897.1 ms | 11186 | 10.0 | n/a |
| Product quartic | endpoint | verified-optimized | 241.6 ms | 238.7–243.2 ms | 41399 | 10.0 | n/a |
| Product quartic | endpoint | advancedhmc | 548.3 ms | 546.8–557.1 ms | 18237 | 10.0 | n/a |
| Product quartic | multinomial | verified-reference | 1176.9 ms | 1163.0–1183.5 ms | 8497 | 10.0 | n/a |
| Product quartic | multinomial | verified-optimized | 494.8 ms | 493.0–495.4 ms | 20212 | 10.0 | n/a |
| Product quartic | multinomial | advancedhmc | 672.4 ms | 668.5–679.0 ms | 14872 | 10.0 | n/a |
| Product quartic | nuts-complete | verified-reference | 6452.5 ms | 6414.3–6481.1 ms | 1550 | 16.0 | n/a |
| Product quartic | nuts-complete | verified-optimized | 788.0 ms | 783.9–791.2 ms | 12691 | 16.0 | n/a |
| Product quartic | nuts-complete | advancedhmc | 1011.6 ms | 1007.8–1016.4 ms | 9886 | 16.0 | n/a |
| Product quartic | nuts-dynamic | verified-optimized | 772.3 ms | 766.4–776.5 ms | 12948 | 15.0 | n/a |
| Product quartic | nuts-dynamic | advancedhmc | 1015.0 ms | 1013.4–1018.2 ms | 9853 | 15.0 | n/a |
| Ill-conditioned Gaussian | endpoint | verified-reference | 906.3 ms | 887.9–912.2 ms | 11034 | 10.0 | n/a |
| Ill-conditioned Gaussian | endpoint | verified-optimized | 232.3 ms | 230.6–234.5 ms | 43042 | 10.0 | n/a |
| Ill-conditioned Gaussian | endpoint | advancedhmc | 501.1 ms | 499.7–506.4 ms | 19957 | 10.0 | n/a |
| Ill-conditioned Gaussian | multinomial | verified-reference | 1198.1 ms | 1193.1–1203.5 ms | 8346 | 10.0 | n/a |
| Ill-conditioned Gaussian | multinomial | verified-optimized | 451.2 ms | 448.9–451.9 ms | 22162 | 10.0 | n/a |
| Ill-conditioned Gaussian | multinomial | advancedhmc | 593.6 ms | 589.0–594.9 ms | 16845 | 10.0 | n/a |
| Ill-conditioned Gaussian | nuts-complete | verified-reference | 6732.0 ms | 6620.6–6785.9 ms | 1485 | 16.0 | n/a |
| Ill-conditioned Gaussian | nuts-complete | verified-optimized | 709.6 ms | 708.0–710.8 ms | 14093 | 16.0 | n/a |
| Ill-conditioned Gaussian | nuts-complete | advancedhmc | 918.9 ms | 914.6–923.3 ms | 10882 | 16.0 | n/a |
| Ill-conditioned Gaussian | nuts-dynamic | verified-optimized | 658.6 ms | 652.8–659.5 ms | 15183 | 15.0 | n/a |
| Ill-conditioned Gaussian | nuts-dynamic | advancedhmc | 966.1 ms | 955.8–972.4 ms | 10351 | 15.0 | n/a |
| Ill-conditioned Gaussian | endpoint-diagonal | verified-reference | 439.5 ms | 434.9–443.5 ms | 22755 | 10.0 | n/a |
| Ill-conditioned Gaussian | endpoint-diagonal | verified-optimized | 64.4 ms | 63.7–65.1 ms | 155318 | 10.0 | n/a |
| Ill-conditioned Gaussian | endpoint-diagonal | advancedhmc | 552.1 ms | 549.0–559.1 ms | 18112 | 10.0 | n/a |
| Ill-conditioned Gaussian | multinomial-diagonal | verified-reference | 1711.4 ms | 1702.0–1743.2 ms | 5843 | 10.0 | n/a |
| Ill-conditioned Gaussian | multinomial-diagonal | verified-optimized | 103.0 ms | 102.7–104.5 ms | 97091 | 10.0 | n/a |
| Ill-conditioned Gaussian | multinomial-diagonal | advancedhmc | 662.2 ms | 655.5–663.5 ms | 15100 | 10.0 | n/a |
| Regularized logistic | endpoint | verified-reference | 1150.8 ms | 1137.0–1160.4 ms | 8690 | 10.0 | n/a |
| Regularized logistic | endpoint | verified-optimized | 384.1 ms | 367.6–385.8 ms | 26034 | 10.0 | n/a |
| Regularized logistic | endpoint | advancedhmc | 745.1 ms | 739.9–747.1 ms | 13422 | 10.0 | n/a |
| Regularized logistic | multinomial | verified-reference | 1795.6 ms | 1790.1–1810.8 ms | 5569 | 10.0 | n/a |
| Regularized logistic | multinomial | verified-optimized | 793.4 ms | 792.7–796.7 ms | 12604 | 10.0 | n/a |
| Regularized logistic | multinomial | advancedhmc | 865.7 ms | 863.7–870.1 ms | 11552 | 10.0 | n/a |
| Regularized logistic | nuts-complete | verified-reference | 7638.2 ms | 7595.2–7737.4 ms | 1309 | 16.0 | n/a |
| Regularized logistic | nuts-complete | verified-optimized | 1284.4 ms | 1278.7–1286.8 ms | 7786 | 16.0 | n/a |
| Regularized logistic | nuts-complete | advancedhmc | 1314.6 ms | 1309.3–1322.2 ms | 7607 | 16.0 | n/a |
| Regularized logistic | nuts-dynamic | verified-optimized | 1091.1 ms | 1085.9–1098.7 ms | 9165 | 15.0 | n/a |
| Regularized logistic | nuts-dynamic | advancedhmc | 1312.8 ms | 1298.4–1322.9 ms | 7617 | 15.0 | n/a |

## Sampling quality

The same independently seeded full chains supply timing and quality evidence. Full-chain storage is included equally in every implementation's timing; diagnostics are computed afterward. Moment errors use each target's known zero mean and analytical or independently computed marginal variance. The table reports the worst split rank-normalized R-hat and minimum bulk/tail ESS among the first four coordinates after ten-percent per-chain burn-in. A warning marker at R-hat above 1.01 is conspicuous but non-gating.

| Target | Algorithm | Implementation | R-hat | Bulk ESS | Tail ESS | Bulk ESS/gradient proxy | Mean MCSE (max) | Covariance error (max) | Median error (max) | ESS/s | Mean RMSE (std.) | Variance RMSE (relative) | Movement | Acceptance | Divergences | Mean steps |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Isotropic Gaussian | endpoint | verified-reference | 1.001 | 15042.3 | 30906.0 | 0.0075 | 0.0083 | 0.0250 | 0.0298 | 2196.6 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Isotropic Gaussian | endpoint | verified-optimized | 1.001 | 15042.3 | 30906.0 | 0.0075 | 0.0083 | 0.0250 | 0.0298 | 12199.7 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Isotropic Gaussian | endpoint | advancedhmc | 1.001 | 15179.2 | 31583.1 | 0.0152 | 0.0083 | 0.0219 | 0.0203 | 3482.0 | 0.008 | 0.007 | 0.995 | 0.995 | 0 | 10.0 |
| Isotropic Gaussian | multinomial | verified-reference | 1.003 | 2768.7 | 6427.5 | 0.0014 | 0.0183 | 0.0601 | 0.0502 | 297.2 | 0.018 | 0.021 | 0.909 | — | 0 | 10.0 |
| Isotropic Gaussian | multinomial | verified-optimized | 1.003 | 2768.7 | 6427.5 | 0.0014 | 0.0183 | 0.0601 | 0.0502 | 914.2 | 0.018 | 0.021 | 0.991 | — | 0 | 10.0 |
| Isotropic Gaussian | multinomial | advancedhmc | 1.006 | 2787.5 | 6409.1 | 0.0028 | 0.0177 | 0.0608 | 0.0518 | 505.8 | 0.016 | 0.020 | 0.909 | 0.998 | 0 | 10.0 |
| Isotropic Gaussian | nuts-complete | verified-reference | 1.001 | 5919.4 | 11556.4 | 0.0018 | 0.0131 | 0.0393 | 0.0381 | 106.4 | 0.012 | 0.014 | 0.995 | — | 0 | 16.0 |
| Isotropic Gaussian | nuts-complete | verified-optimized | 1.001 | 6778.3 | 12772.2 | 0.0021 | 0.0124 | 0.0343 | 0.0360 | 1340.2 | 0.011 | 0.013 | 0.996 | — | 0 | 16.0 |
| Isotropic Gaussian | nuts-complete | advancedhmc | 1.002 | 6659.4 | 13630.9 | 0.0042 | 0.0121 | 0.0411 | 0.0338 | 818.8 | 0.011 | 0.014 | 0.941 | 0.997 | 0 | 16.0 |
| Isotropic Gaussian | nuts-dynamic | verified-optimized | 1.001 | 10480.3 | 22574.3 | 0.0035 | 0.0098 | 0.0256 | 0.0225 | 1968.7 | 0.009 | 0.008 | 1.000 | 0.997 | 0 | 15.0 |
| Isotropic Gaussian | nuts-dynamic | advancedhmc | 1.001 | 10631.5 | 21690.6 | 0.0071 | 0.0098 | 0.0285 | 0.0223 | 1268.5 | 0.009 | 0.010 | 1.000 | 0.997 | 0 | 15.0 |
| Correlated Gaussian (ρ=0.9) | endpoint | verified-reference | 1.006 | 2040.0 | 5988.2 | 0.0010 | 0.0208 | 0.0547 | 0.0402 | 226.4 | 0.019 | 0.025 | 0.973 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | endpoint | verified-optimized | 1.006 | 2040.0 | 5988.2 | 0.0010 | 0.0208 | 0.0547 | 0.0402 | 822.0 | 0.019 | 0.025 | 0.973 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | endpoint | advancedhmc | 1.005 | 2372.8 | 6405.1 | 0.0024 | 0.0212 | 0.0552 | 0.0620 | 434.9 | 0.031 | 0.026 | 0.974 | 0.974 | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | multinomial | verified-reference | ⚠ 1.020 | 537.0 | 2841.7 | 0.0003 | 0.0294 | 0.1682 | 0.0832 | 39.3 | 0.035 | 0.060 | 0.908 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | multinomial | verified-optimized | ⚠ 1.020 | 537.0 | 2841.7 | 0.0003 | 0.0294 | 0.1682 | 0.0832 | 94.7 | 0.035 | 0.060 | 0.991 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | multinomial | advancedhmc | ⚠ 1.031 | 604.4 | 2531.8 | 0.0006 | 0.0279 | 0.1029 | 0.1102 | 67.7 | 0.055 | 0.041 | 0.909 | 0.953 | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | nuts-complete | verified-reference | ⚠ 1.013 | 1003.0 | 3757.9 | 0.0003 | 0.0257 | 0.0842 | 0.0930 | 14.2 | 0.040 | 0.032 | 0.932 | — | 0 | 16.0 |
| Correlated Gaussian (ρ=0.9) | nuts-complete | verified-optimized | 1.008 | 1152.1 | 4200.8 | 0.0004 | 0.0253 | 0.0849 | 0.0457 | 122.6 | 0.022 | 0.035 | 0.996 | — | 0 | 16.0 |
| Correlated Gaussian (ρ=0.9) | nuts-complete | advancedhmc | ⚠ 1.015 | 1187.6 | 3994.8 | 0.0007 | 0.0247 | 0.0760 | 0.0755 | 100.0 | 0.039 | 0.033 | 0.940 | 0.952 | 0 | 16.0 |
| Correlated Gaussian (ρ=0.9) | nuts-dynamic | verified-optimized | 1.005 | 1410.2 | 5758.8 | 0.0005 | 0.0225 | 0.0541 | 0.0590 | 167.1 | 0.023 | 0.024 | 1.000 | 0.949 | 0 | 15.0 |
| Correlated Gaussian (ρ=0.9) | nuts-dynamic | advancedhmc | 1.003 | 1567.8 | 5410.3 | 0.0010 | 0.0227 | 0.0616 | 0.0540 | 140.2 | 0.023 | 0.029 | 1.000 | 0.949 | 0 | 15.0 |
| Correlated Gaussian (ρ=0.9) | endpoint-dense | verified-reference | 1.001 | 15195.3 | 33300.2 | 0.0076 | 0.0082 | 0.0260 | 0.0286 | 622.6 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | endpoint-dense | verified-optimized | 1.001 | 15195.3 | 33300.2 | 0.0138 | 0.0082 | 0.0260 | 0.0286 | 3078.3 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | endpoint-dense | advancedhmc | 1.001 | 15789.1 | 32462.1 | 0.0158 | 0.0082 | 0.0194 | 0.0209 | 1645.0 | 0.010 | 0.007 | 0.995 | 0.995 | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | multinomial-dense | verified-reference | 1.003 | 2704.1 | 6205.3 | 0.0014 | 0.0182 | 0.0469 | 0.0309 | 49.6 | 0.014 | 0.020 | 0.909 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | multinomial-dense | verified-optimized | 1.003 | 2704.1 | 6205.3 | 0.0025 | 0.0182 | 0.0469 | 0.0309 | 433.5 | 0.014 | 0.020 | 0.909 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | multinomial-dense | advancedhmc | 1.005 | 2725.7 | 6263.5 | 0.0027 | 0.0181 | 0.0577 | 0.0572 | 240.9 | 0.019 | 0.023 | 0.909 | 0.998 | 0 | 10.0 |
| Product quartic | endpoint | verified-reference | 1.000 | 36720.4 | 84182.5 | 0.0184 | 0.0038 | — | 0.0204 | 3910.0 | 0.006 | 0.004 | 0.988 | — | 0 | 10.0 |
| Product quartic | endpoint | verified-optimized | 1.000 | 36720.4 | 84182.5 | 0.0184 | 0.0038 | — | 0.0204 | 14281.5 | 0.006 | 0.004 | 0.988 | — | 0 | 10.0 |
| Product quartic | endpoint | advancedhmc | 1.000 | 36781.8 | 86589.9 | 0.0368 | 0.0037 | — | 0.0123 | 6569.5 | 0.005 | 0.004 | 0.988 | 0.988 | 0 | 10.0 |
| Product quartic | multinomial | verified-reference | 1.001 | 5888.8 | 16258.9 | 0.0029 | 0.0090 | — | 0.0298 | 485.9 | 0.012 | 0.010 | 0.909 | — | 0 | 10.0 |
| Product quartic | multinomial | verified-optimized | 1.001 | 5888.8 | 16258.9 | 0.0029 | 0.0090 | — | 0.0298 | 1152.2 | 0.012 | 0.010 | 0.991 | — | 0 | 10.0 |
| Product quartic | multinomial | advancedhmc | 1.003 | 5782.8 | 16728.8 | 0.0058 | 0.0089 | — | 0.0274 | 879.1 | 0.012 | 0.011 | 0.909 | 0.990 | 0 | 10.0 |
| Product quartic | nuts-complete | verified-reference | 1.001 | 12222.1 | 28538.8 | 0.0038 | 0.0063 | — | 0.0232 | 194.6 | 0.008 | 0.008 | 0.995 | — | 0 | 16.0 |
| Product quartic | nuts-complete | verified-optimized | 1.001 | 13995.7 | 31449.0 | 0.0044 | 0.0060 | — | 0.0199 | 1803.8 | 0.008 | 0.007 | 0.996 | — | 0 | 16.0 |
| Product quartic | nuts-complete | advancedhmc | 1.001 | 14335.6 | 32305.9 | 0.0090 | 0.0060 | — | 0.0193 | 1396.7 | 0.008 | 0.007 | 0.941 | 0.989 | 0 | 16.0 |
| Product quartic | nuts-dynamic | verified-optimized | 1.000 | 24134.2 | 54279.9 | 0.0080 | 0.0046 | — | 0.0138 | 3020.1 | 0.006 | 0.005 | 1.000 | 0.988 | 0 | 15.0 |
| Product quartic | nuts-dynamic | advancedhmc | 1.000 | 24640.2 | 54886.3 | 0.0164 | 0.0046 | — | 0.0123 | 2378.9 | 0.006 | 0.005 | 1.000 | 0.988 | 0 | 15.0 |
| Ill-conditioned Gaussian | endpoint | verified-reference | 1.001 | 16306.8 | 32614.1 | 0.0082 | 0.2984 | 16.9459 | 2.8810 | 1896.3 | 0.048 | 0.023 | 0.873 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | endpoint | verified-optimized | 1.001 | 16306.8 | 32614.1 | 0.0082 | 0.2984 | 16.9459 | 2.8810 | 7171.1 | 0.048 | 0.023 | 0.873 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | endpoint | advancedhmc | 1.000 | 16030.4 | 31434.9 | 0.0160 | 0.3020 | 8.1615 | 1.2309 | 3237.9 | 0.030 | 0.030 | 0.877 | 0.876 | 0 | 10.0 |
| Ill-conditioned Gaussian | multinomial | verified-reference | 1.000 | 79177.0 | 53043.3 | 0.0396 | 0.2795 | 20.1561 | 1.6843 | 6730.0 | 0.051 | 0.057 | 0.905 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | multinomial | verified-optimized | 1.000 | 79177.0 | 53043.3 | 0.0396 | 0.2795 | 20.1561 | 1.6843 | 17814.0 | 0.051 | 0.057 | 0.991 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | multinomial | advancedhmc | 1.000 | 79795.2 | 52953.3 | 0.0798 | 0.2680 | 19.4246 | 2.5623 | 13608.0 | 0.056 | 0.063 | 0.906 | 0.895 | 0 | 10.0 |
| Ill-conditioned Gaussian | nuts-complete | verified-reference | 1.000 | 87055.4 | 54706.2 | 0.0272 | 0.3021 | 13.3298 | 1.2211 | 1312.9 | 0.035 | 0.038 | 0.995 | — | 0 | 16.0 |
| Ill-conditioned Gaussian | nuts-complete | verified-optimized | 1.000 | 82995.2 | 55863.3 | 0.0259 | 0.3065 | 12.3651 | 1.2725 | 12037.9 | 0.035 | 0.036 | 0.996 | — | 0 | 16.0 |
| Ill-conditioned Gaussian | nuts-complete | advancedhmc | 1.000 | 86291.9 | 56109.0 | 0.0539 | 0.2859 | 13.3656 | 1.7168 | 9525.0 | 0.037 | 0.040 | 0.939 | 0.893 | 0 | 16.0 |
| Ill-conditioned Gaussian | nuts-dynamic | verified-optimized | 1.000 | 86734.3 | 54470.5 | 0.0289 | 0.2915 | 18.1091 | 1.7082 | 13689.7 | 0.032 | 0.038 | 1.000 | 0.886 | 0 | 15.0 |
| Ill-conditioned Gaussian | nuts-dynamic | advancedhmc | 1.000 | 86979.1 | 55881.0 | 0.0580 | 0.3187 | 14.4449 | 1.0218 | 9312.5 | 0.031 | 0.035 | 1.000 | 0.885 | 0 | 15.0 |
| Ill-conditioned Gaussian | endpoint-diagonal | verified-reference | 1.001 | 15042.3 | 30906.0 | 0.0075 | 0.0798 | 1.3167 | 0.2859 | 3451.3 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | endpoint-diagonal | verified-optimized | 1.001 | 15042.3 | 30906.0 | 0.0137 | 0.0798 | 1.3167 | 0.2859 | 23603.4 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | endpoint-diagonal | advancedhmc | 1.001 | 15179.2 | 31583.1 | 0.0152 | 0.0764 | 1.1941 | 0.1266 | 2758.2 | 0.008 | 0.007 | 0.995 | 0.995 | 0 | 10.0 |
| Ill-conditioned Gaussian | multinomial-diagonal | verified-reference | 1.003 | 2768.7 | 6427.5 | 0.0014 | 0.1737 | 2.8200 | 0.2501 | 154.5 | 0.018 | 0.021 | 0.909 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | multinomial-diagonal | verified-optimized | 1.003 | 2768.7 | 6427.5 | 0.0025 | 0.1737 | 2.8200 | 0.2501 | 2562.1 | 0.018 | 0.021 | 0.909 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | multinomial-diagonal | advancedhmc | 1.006 | 2787.5 | 6409.1 | 0.0028 | 0.1670 | 3.4796 | 0.3842 | 409.9 | 0.016 | 0.020 | 0.909 | 0.998 | 0 | 10.0 |
| Regularized logistic | endpoint | verified-reference | 1.000 | 23123.2 | 41791.1 | 0.0116 | 0.0057 | — | 0.0208 | 2002.1 | 0.007 | 0.008 | 0.992 | — | 0 | 10.0 |
| Regularized logistic | endpoint | verified-optimized | 1.000 | 23123.2 | 41791.1 | 0.0116 | 0.0057 | — | 0.0208 | 6013.0 | 0.007 | 0.008 | 0.992 | — | 0 | 10.0 |
| Regularized logistic | endpoint | advancedhmc | 1.001 | 23430.9 | 41867.0 | 0.0234 | 0.0057 | — | 0.0130 | 3177.0 | 0.007 | 0.007 | 0.992 | 0.992 | 0 | 10.0 |
| Regularized logistic | multinomial | verified-reference | 1.002 | 4012.4 | 8207.9 | 0.0020 | 0.0131 | — | 0.0326 | 215.3 | 0.014 | 0.018 | 0.909 | — | 0 | 10.0 |
| Regularized logistic | multinomial | verified-optimized | 1.002 | 4012.4 | 8207.9 | 0.0020 | 0.0131 | — | 0.0326 | 488.0 | 0.014 | 0.018 | 0.991 | — | 0 | 10.0 |
| Regularized logistic | multinomial | advancedhmc | 1.004 | 3894.3 | 8449.2 | 0.0039 | 0.0128 | — | 0.0357 | 445.3 | 0.014 | 0.018 | 0.909 | 0.997 | 0 | 10.0 |
| Regularized logistic | nuts-complete | verified-reference | 1.001 | 8413.0 | 14982.2 | 0.0026 | 0.0093 | — | 0.0277 | 108.2 | 0.010 | 0.013 | 0.995 | — | 0 | 16.0 |
| Regularized logistic | nuts-complete | verified-optimized | 1.001 | 9495.5 | 16252.8 | 0.0030 | 0.0088 | — | 0.0227 | 769.8 | 0.009 | 0.012 | 0.996 | — | 0 | 16.0 |
| Regularized logistic | nuts-complete | advancedhmc | 1.002 | 9759.9 | 17582.0 | 0.0061 | 0.0086 | — | 0.0239 | 742.6 | 0.009 | 0.012 | 0.941 | 0.996 | 0 | 16.0 |
| Regularized logistic | nuts-dynamic | verified-optimized | 1.001 | 15585.4 | 29600.1 | 0.0052 | 0.0068 | — | 0.0166 | 1369.7 | 0.007 | 0.007 | 1.000 | 0.996 | 0 | 15.0 |
| Regularized logistic | nuts-dynamic | advancedhmc | 1.001 | 15993.2 | 29018.0 | 0.0107 | 0.0068 | — | 0.0151 | 1254.6 | 0.008 | 0.008 | 1.000 | 0.996 | 0 | 15.0 |

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
