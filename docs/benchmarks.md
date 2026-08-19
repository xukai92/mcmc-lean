# HMC benchmark report

This is a reproducible implementation benchmark, not a theorem about convergence or a claim that Float64 execution is identical to the exact-real Lean semantics.

```@raw html
<div id="hmc-benchmark-explorer" class="benchmark-explorer" aria-label="Interactive HMC benchmark explorer">
  <p class="benchmark-loading">Loading interactive benchmark…</p>
</div>
```

The interactive chart supports metric, target, algorithm, implementation, and grouping controls. Hover over a point for its chain seed and repetition or its aggregate quality diagnostics.

??? note "Static chart fallback"
    The committed SVG remains available for non-JavaScript readers and portable rendering.

    ![HMC transition-throughput distributions](assets/benchmarks/hmc-throughput.svg)

Rows are grouped first by target and then by algorithm. Within each row, colors compare libraries implementing that same `target × algorithm` case. Small translucent points are complete-chain timing repetitions; large points and thick intervals are medians and IQRs. The shared logarithmic axis retains absolute throughput and remains extensible to additional libraries.

Preconditioned endpoint and multinomial rows include VerifiedSamplers' Reference and Optimized constant-metric paths.

VerifiedSamplers `NUTS` is labelled `verified-reference`: it is the checked Lean-IR-driven sampler connected to the exact-real invariance theorem. The independent handwritten `Optimized.NUTS` is labelled `verified-optimized`; that label identifies the project's optimized implementation, for which conformance and statistical tests are empirical evidence rather than a formal transition-equivalence proof.

## Configuration

- Commit: `fc55556`
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
| Isotropic Gaussian | 14126 | 79136 | 22071 |
| Correlated Gaussian (ρ=0.9) | 7889 | 21859 | 13004 |
| Product quartic | 10614 | 39974 | 17024 |
| Ill-conditioned Gaussian | 10591 | 46461 | 17280 |
| Regularized logistic | 8031 | 27413 | 12703 |

#### Multinomial

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Isotropic Gaussian | 11146 | 33446 | 18138 |
| Correlated Gaussian (ρ=0.9) | 5261 | 10922 | 11308 |
| Product quartic | 7692 | 19633 | 15165 |
| Ill-conditioned Gaussian | 7633 | 19742 | 14766 |
| Regularized logistic | 5203 | 12553 | 11569 |

#### Nuts

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Isotropic Gaussian | 8538 | 4498 | 4539 |
| Correlated Gaussian (ρ=0.9) | 5518 | 1195 | 1339 |
| Product quartic | 7198 | 6167 | 5558 |
| Ill-conditioned Gaussian | 7073 | 799 | 668 |
| Regularized logistic | 5928 | 2790 | 2707 |

#### Preconditioned-endpoint

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Correlated Gaussian (ρ=0.9) | 3635 | 5250 | 8160 |
| Ill-conditioned Gaussian | 21933 | 67344 | 15831 |

#### Preconditioned-multinomial

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Correlated Gaussian (ρ=0.9) | 1531 | 2993 | 7496 |
| Ill-conditioned Gaussian | 5486 | 16541 | 14293 |

### Complete summary

| Target | Algorithm | Implementation | Median | IQR | Draws/s | Mean steps | Allocations |
|---|---|---|---:|---:|---:|---:|---:|
| Isotropic Gaussian | endpoint | verified-reference | 707.9 ms | 704.3–709.9 ms | 14126 | 10.0 | n/a |
| Isotropic Gaussian | endpoint | verified-optimized | 126.4 ms | 125.3–127.2 ms | 79136 | 10.0 | n/a |
| Isotropic Gaussian | endpoint | advancedhmc | 453.1 ms | 449.6–458.2 ms | 22071 | 10.0 | n/a |
| Isotropic Gaussian | multinomial | verified-reference | 897.2 ms | 892.3–909.5 ms | 11146 | 10.0 | n/a |
| Isotropic Gaussian | multinomial | verified-optimized | 299.0 ms | 297.3–299.4 ms | 33446 | 10.0 | n/a |
| Isotropic Gaussian | multinomial | advancedhmc | 551.3 ms | 550.7–551.7 ms | 18138 | 10.0 | n/a |
| Isotropic Gaussian | nuts | verified-reference | 1171.3 ms | 1163.4–1183.3 ms | 8538 | 22.5 | n/a |
| Isotropic Gaussian | nuts | verified-optimized | 2223.0 ms | 2203.4–2240.7 ms | 4498 | 63.0 | n/a |
| Isotropic Gaussian | nuts | advancedhmc | 2203.1 ms | 2166.1–2257.2 ms | 4539 | 63.0 | n/a |
| Correlated Gaussian (ρ=0.9) | endpoint | verified-reference | 1267.6 ms | 1253.4–1273.6 ms | 7889 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | endpoint | verified-optimized | 457.5 ms | 449.0–468.0 ms | 21859 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | endpoint | advancedhmc | 769.0 ms | 764.6–774.9 ms | 13004 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | multinomial | verified-reference | 1900.8 ms | 1897.5–1923.3 ms | 5261 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | multinomial | verified-optimized | 915.6 ms | 909.1–921.8 ms | 10922 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | multinomial | advancedhmc | 884.3 ms | 880.1–896.9 ms | 11308 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | nuts | verified-reference | 1812.2 ms | 1798.0–1830.6 ms | 5518 | 22.5 | n/a |
| Correlated Gaussian (ρ=0.9) | nuts | verified-optimized | 8370.3 ms | 8232.4–8418.9 ms | 1195 | 122.6 | n/a |
| Correlated Gaussian (ρ=0.9) | nuts | advancedhmc | 7468.0 ms | 7410.5–7576.7 ms | 1339 | 122.4 | n/a |
| Correlated Gaussian (ρ=0.9) | preconditioned-endpoint | verified-reference | 2751.3 ms | 2720.3–2765.2 ms | 3635 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | preconditioned-endpoint | verified-optimized | 1904.9 ms | 1893.4–1942.9 ms | 5250 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | preconditioned-endpoint | advancedhmc | 1225.5 ms | 1218.9–1236.3 ms | 8160 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | preconditioned-multinomial | verified-reference | 6530.2 ms | 6469.4–6640.9 ms | 1531 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | preconditioned-multinomial | verified-optimized | 3341.4 ms | 3270.5–3405.6 ms | 2993 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | preconditioned-multinomial | advancedhmc | 1334.0 ms | 1328.4–1338.2 ms | 7496 | 10.0 | n/a |
| Product quartic | endpoint | verified-reference | 942.2 ms | 938.8–950.0 ms | 10614 | 10.0 | n/a |
| Product quartic | endpoint | verified-optimized | 250.2 ms | 247.5–251.2 ms | 39974 | 10.0 | n/a |
| Product quartic | endpoint | advancedhmc | 587.4 ms | 578.2–591.2 ms | 17024 | 10.0 | n/a |
| Product quartic | multinomial | verified-reference | 1300.1 ms | 1287.9–1318.3 ms | 7692 | 10.0 | n/a |
| Product quartic | multinomial | verified-optimized | 509.4 ms | 504.5–515.3 ms | 19633 | 10.0 | n/a |
| Product quartic | multinomial | advancedhmc | 659.4 ms | 656.2–665.5 ms | 15165 | 10.0 | n/a |
| Product quartic | nuts | verified-reference | 1389.2 ms | 1373.8–1395.6 ms | 7198 | 22.5 | n/a |
| Product quartic | nuts | verified-optimized | 1621.4 ms | 1609.3–1630.5 ms | 6167 | 31.0 | n/a |
| Product quartic | nuts | advancedhmc | 1799.3 ms | 1787.6–1807.7 ms | 5558 | 31.0 | n/a |
| Ill-conditioned Gaussian | endpoint | verified-reference | 944.2 ms | 939.7–974.8 ms | 10591 | 10.0 | n/a |
| Ill-conditioned Gaussian | endpoint | verified-optimized | 215.2 ms | 213.3–216.5 ms | 46461 | 10.0 | n/a |
| Ill-conditioned Gaussian | endpoint | advancedhmc | 578.7 ms | 577.3–582.9 ms | 17280 | 10.0 | n/a |
| Ill-conditioned Gaussian | multinomial | verified-reference | 1310.0 ms | 1295.3–1322.5 ms | 7633 | 10.0 | n/a |
| Ill-conditioned Gaussian | multinomial | verified-optimized | 506.5 ms | 503.6–508.6 ms | 19742 | 10.0 | n/a |
| Ill-conditioned Gaussian | multinomial | advancedhmc | 677.2 ms | 671.3–680.3 ms | 14766 | 10.0 | n/a |
| Ill-conditioned Gaussian | nuts | verified-reference | 1413.8 ms | 1405.3–1419.6 ms | 7073 | 22.5 | n/a |
| Ill-conditioned Gaussian | nuts | verified-optimized | 12520.7 ms | 12446.4–12644.1 ms | 799 | 323.1 | n/a |
| Ill-conditioned Gaussian | nuts | advancedhmc | 14965.3 ms | 14844.3–15191.0 ms | 668 | 323.4 | n/a |
| Ill-conditioned Gaussian | preconditioned-endpoint | verified-reference | 455.9 ms | 452.7–462.8 ms | 21933 | 10.0 | n/a |
| Ill-conditioned Gaussian | preconditioned-endpoint | verified-optimized | 148.5 ms | 147.1–149.4 ms | 67344 | 10.0 | n/a |
| Ill-conditioned Gaussian | preconditioned-endpoint | advancedhmc | 631.7 ms | 616.1–649.5 ms | 15831 | 10.0 | n/a |
| Ill-conditioned Gaussian | preconditioned-multinomial | verified-reference | 1822.9 ms | 1807.5–1851.9 ms | 5486 | 10.0 | n/a |
| Ill-conditioned Gaussian | preconditioned-multinomial | verified-optimized | 604.6 ms | 602.5–607.2 ms | 16541 | 10.0 | n/a |
| Ill-conditioned Gaussian | preconditioned-multinomial | advancedhmc | 699.6 ms | 693.0–703.9 ms | 14293 | 10.0 | n/a |
| Regularized logistic | endpoint | verified-reference | 1245.2 ms | 1243.2–1288.3 ms | 8031 | 10.0 | n/a |
| Regularized logistic | endpoint | verified-optimized | 364.8 ms | 361.8–366.0 ms | 27413 | 10.0 | n/a |
| Regularized logistic | endpoint | advancedhmc | 787.2 ms | 762.0–815.2 ms | 12703 | 10.0 | n/a |
| Regularized logistic | multinomial | verified-reference | 1922.0 ms | 1877.3–1983.4 ms | 5203 | 10.0 | n/a |
| Regularized logistic | multinomial | verified-optimized | 796.6 ms | 787.4–804.1 ms | 12553 | 10.0 | n/a |
| Regularized logistic | multinomial | advancedhmc | 864.4 ms | 854.3–872.5 ms | 11569 | 10.0 | n/a |
| Regularized logistic | nuts | verified-reference | 1686.9 ms | 1676.0–1709.0 ms | 5928 | 22.5 | n/a |
| Regularized logistic | nuts | verified-optimized | 3584.1 ms | 3570.6–3636.8 ms | 2790 | 50.4 | n/a |
| Regularized logistic | nuts | advancedhmc | 3694.5 ms | 3667.4–3777.8 ms | 2707 | 50.4 | n/a |

## Sampling quality

The same independently seeded full chains supply timing and quality evidence. Full-chain storage is included equally in every implementation's timing; diagnostics are computed afterward. Moment errors use each target's known zero mean and analytical or independently computed marginal variance. The table reports the worst split rank-normalized R-hat and minimum bulk/tail ESS among the first four coordinates after ten-percent per-chain burn-in. A warning marker at R-hat above 1.01 is conspicuous but non-gating.

| Target | Algorithm | Implementation | R-hat | Bulk ESS | Tail ESS | Bulk ESS/gradient proxy | Mean MCSE (max) | Covariance error (max) | Median error (max) | ESS/s | Mean RMSE (std.) | Variance RMSE (relative) | Movement | Acceptance | Divergences | Mean steps |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Isotropic Gaussian | endpoint | verified-reference | 1.001 | 15042.3 | 30906.0 | 0.0075 | 0.0083 | 0.0250 | 0.0298 | 2202.8 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Isotropic Gaussian | endpoint | verified-optimized | 1.001 | 15042.3 | 30906.0 | 0.0075 | 0.0083 | 0.0250 | 0.0298 | 12009.6 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Isotropic Gaussian | endpoint | advancedhmc | 1.001 | 15179.2 | 31583.1 | 0.0152 | 0.0083 | 0.0219 | 0.0203 | 3368.9 | 0.008 | 0.007 | 0.995 | 0.995 | 0 | 10.0 |
| Isotropic Gaussian | multinomial | verified-reference | 1.003 | 2768.7 | 6427.5 | 0.0014 | 0.0183 | 0.0601 | 0.0502 | 294.7 | 0.018 | 0.021 | 0.909 | — | 0 | 10.0 |
| Isotropic Gaussian | multinomial | verified-optimized | 1.003 | 2768.7 | 6427.5 | 0.0014 | 0.0183 | 0.0601 | 0.0502 | 889.7 | 0.018 | 0.021 | 0.991 | — | 0 | 10.0 |
| Isotropic Gaussian | multinomial | advancedhmc | 1.006 | 2787.5 | 6409.1 | 0.0028 | 0.0177 | 0.0608 | 0.0518 | 491.4 | 0.016 | 0.020 | 0.909 | 0.998 | 0 | 10.0 |
| Isotropic Gaussian | nuts | verified-reference | 1.000 | 0.0 | 0.0 | 0.0000 | 0.0000 | 1.0000 | 0.0000 | 0.0 | 0.000 | 1.000 | 0.000 | — | 0 | 22.5 |
| Isotropic Gaussian | nuts | verified-optimized | 1.000 | 90000.0 | 68651.3 | 0.0071 | 0.0021 | 0.0219 | 0.0072 | 4044.7 | 0.002 | 0.008 | 1.000 | 0.996 | 0 | 63.0 |
| Isotropic Gaussian | nuts | advancedhmc | 1.000 | 90000.0 | 67827.6 | 0.0143 | 0.0022 | 0.0233 | 0.0071 | 4068.2 | 0.002 | 0.009 | 1.000 | 0.996 | 0 | 63.0 |
| Correlated Gaussian (ρ=0.9) | endpoint | verified-reference | 1.006 | 2040.0 | 5988.2 | 0.0010 | 0.0208 | 0.0547 | 0.0402 | 157.2 | 0.019 | 0.025 | 0.973 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | endpoint | verified-optimized | 1.006 | 2040.0 | 5988.2 | 0.0010 | 0.0208 | 0.0547 | 0.0402 | 427.4 | 0.019 | 0.025 | 0.973 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | endpoint | advancedhmc | 1.005 | 2372.8 | 6405.1 | 0.0024 | 0.0212 | 0.0552 | 0.0620 | 294.3 | 0.031 | 0.026 | 0.974 | 0.974 | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | multinomial | verified-reference | ⚠ 1.020 | 537.0 | 2841.7 | 0.0003 | 0.0294 | 0.1682 | 0.0832 | 23.0 | 0.035 | 0.060 | 0.908 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | multinomial | verified-optimized | ⚠ 1.020 | 537.0 | 2841.7 | 0.0003 | 0.0294 | 0.1682 | 0.0832 | 48.0 | 0.035 | 0.060 | 0.991 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | multinomial | advancedhmc | ⚠ 1.031 | 604.4 | 2531.8 | 0.0006 | 0.0279 | 0.1029 | 0.1102 | 47.1 | 0.055 | 0.041 | 0.909 | 0.953 | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | nuts | verified-reference | 1.000 | 0.0 | 0.0 | 0.0000 | 0.0000 | 1.0000 | 0.0000 | 0.0 | 0.000 | 1.000 | 0.000 | — | 0 | 22.5 |
| Correlated Gaussian (ρ=0.9) | nuts | verified-optimized | 1.000 | 64132.9 | 65822.9 | 0.0026 | 0.0045 | 0.0123 | 0.0105 | 771.8 | 0.004 | 0.005 | 1.000 | 0.948 | 0 | 122.6 |
| Correlated Gaussian (ρ=0.9) | nuts | advancedhmc | 1.000 | 62565.6 | 67093.6 | 0.0051 | 0.0046 | 0.0125 | 0.0128 | 839.0 | 0.003 | 0.006 | 1.000 | 0.948 | 0 | 122.4 |
| Correlated Gaussian (ρ=0.9) | preconditioned-endpoint | verified-reference | 1.001 | 15195.3 | 33300.2 | 0.0076 | 0.0082 | 0.0260 | 0.0286 | 572.0 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | preconditioned-endpoint | verified-optimized | 1.001 | 15195.3 | 33300.2 | 0.0076 | 0.0082 | 0.0260 | 0.0286 | 819.0 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | preconditioned-endpoint | advancedhmc | 1.001 | 15789.1 | 32462.1 | 0.0158 | 0.0082 | 0.0194 | 0.0209 | 1296.9 | 0.010 | 0.007 | 0.995 | 0.995 | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | preconditioned-multinomial | verified-reference | 1.003 | 2704.1 | 6205.3 | 0.0014 | 0.0182 | 0.0469 | 0.0309 | 42.9 | 0.014 | 0.020 | 0.909 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | preconditioned-multinomial | verified-optimized | 1.003 | 2704.1 | 6205.3 | 0.0014 | 0.0182 | 0.0469 | 0.0309 | 84.0 | 0.014 | 0.020 | 0.991 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | preconditioned-multinomial | advancedhmc | 1.005 | 2725.7 | 6263.5 | 0.0027 | 0.0181 | 0.0577 | 0.0572 | 192.4 | 0.019 | 0.023 | 0.909 | 0.998 | 0 | 10.0 |
| Product quartic | endpoint | verified-reference | 1.000 | 36720.4 | 84182.5 | 0.0184 | 0.0038 | — | 0.0204 | 3750.7 | 0.006 | 0.004 | 0.988 | — | 0 | 10.0 |
| Product quartic | endpoint | verified-optimized | 1.000 | 36720.4 | 84182.5 | 0.0184 | 0.0038 | — | 0.0204 | 13736.0 | 0.006 | 0.004 | 0.988 | — | 0 | 10.0 |
| Product quartic | endpoint | advancedhmc | 1.000 | 36781.8 | 86589.9 | 0.0368 | 0.0037 | — | 0.0123 | 6242.0 | 0.005 | 0.004 | 0.988 | 0.988 | 0 | 10.0 |
| Product quartic | multinomial | verified-reference | 1.001 | 5888.8 | 16258.9 | 0.0029 | 0.0090 | — | 0.0298 | 438.4 | 0.012 | 0.010 | 0.909 | — | 0 | 10.0 |
| Product quartic | multinomial | verified-optimized | 1.001 | 5888.8 | 16258.9 | 0.0029 | 0.0090 | — | 0.0298 | 1119.2 | 0.012 | 0.010 | 0.991 | — | 0 | 10.0 |
| Product quartic | multinomial | advancedhmc | 1.003 | 5782.8 | 16728.8 | 0.0058 | 0.0089 | — | 0.0274 | 887.8 | 0.012 | 0.011 | 0.909 | 0.990 | 0 | 10.0 |
| Product quartic | nuts | verified-reference | 1.000 | 0.0 | 0.0 | 0.0000 | 0.0000 | — | 0.0000 | 0.0 | 0.000 | 1.000 | 0.000 | — | 0 | 22.5 |
| Product quartic | nuts | verified-optimized | 1.000 | 90000.0 | 76482.6 | 0.0145 | 0.0020 | — | 0.0100 | 5550.4 | 0.003 | 0.005 | 1.000 | 0.988 | 0 | 31.0 |
| Product quartic | nuts | advancedhmc | 1.000 | 90000.0 | 78149.5 | 0.0290 | 0.0021 | — | 0.0070 | 5005.5 | 0.003 | 0.006 | 1.000 | 0.988 | 0 | 31.0 |
| Ill-conditioned Gaussian | endpoint | verified-reference | 1.001 | 16306.8 | 32614.1 | 0.0082 | 0.2984 | 16.9459 | 2.8810 | 1768.1 | 0.048 | 0.023 | 0.873 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | endpoint | verified-optimized | 1.001 | 16306.8 | 32614.1 | 0.0082 | 0.2984 | 16.9459 | 2.8810 | 7762.1 | 0.048 | 0.023 | 0.873 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | endpoint | advancedhmc | 1.000 | 16030.4 | 31434.9 | 0.0160 | 0.3020 | 8.1615 | 1.2309 | 2804.3 | 0.030 | 0.030 | 0.877 | 0.876 | 0 | 10.0 |
| Ill-conditioned Gaussian | multinomial | verified-reference | 1.000 | 79177.0 | 53043.3 | 0.0396 | 0.2795 | 20.1561 | 1.6843 | 6143.1 | 0.051 | 0.057 | 0.905 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | multinomial | verified-optimized | 1.000 | 79177.0 | 53043.3 | 0.0396 | 0.2795 | 20.1561 | 1.6843 | 15916.2 | 0.051 | 0.057 | 0.991 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | multinomial | advancedhmc | 1.000 | 79795.2 | 52953.3 | 0.0798 | 0.2680 | 19.4246 | 2.5623 | 11922.8 | 0.056 | 0.063 | 0.906 | 0.895 | 0 | 10.0 |
| Ill-conditioned Gaussian | nuts | verified-reference | 1.000 | 0.0 | 0.0 | 0.0000 | 0.0000 | 100.0000 | 0.0000 | 0.0 | 0.000 | 1.000 | 0.000 | — | 0 | 22.5 |
| Ill-conditioned Gaussian | nuts | verified-optimized | 1.000 | 87473.8 | 58750.0 | 0.0014 | 0.0529 | 1.3289 | 0.0390 | 711.5 | 0.003 | 0.008 | 1.000 | 0.888 | 0 | 323.1 |
| Ill-conditioned Gaussian | nuts | advancedhmc | 1.000 | 86754.6 | 55567.6 | 0.0027 | 0.0522 | 0.6444 | 0.0697 | 585.5 | 0.003 | 0.008 | 1.000 | 0.889 | 0 | 323.4 |
| Ill-conditioned Gaussian | preconditioned-endpoint | verified-reference | 1.001 | 15042.3 | 30906.0 | 0.0075 | 0.0798 | 1.3167 | 0.2859 | 3322.8 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | preconditioned-endpoint | verified-optimized | 1.001 | 15042.3 | 30906.0 | 0.0075 | 0.0798 | 1.3167 | 0.2859 | 10210.2 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | preconditioned-endpoint | advancedhmc | 1.001 | 15179.2 | 31583.1 | 0.0152 | 0.0764 | 1.1941 | 0.1266 | 2417.7 | 0.008 | 0.007 | 0.995 | 0.995 | 0 | 10.0 |
| Ill-conditioned Gaussian | preconditioned-multinomial | verified-reference | 1.003 | 2768.7 | 6427.5 | 0.0014 | 0.1737 | 2.8200 | 0.2501 | 145.4 | 0.018 | 0.021 | 0.909 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | preconditioned-multinomial | verified-optimized | 1.003 | 2768.7 | 6427.5 | 0.0014 | 0.1737 | 2.8200 | 0.2501 | 433.8 | 0.018 | 0.021 | 0.991 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | preconditioned-multinomial | advancedhmc | 1.006 | 2787.5 | 6409.1 | 0.0028 | 0.1670 | 3.4796 | 0.3842 | 382.1 | 0.016 | 0.020 | 0.909 | 0.998 | 0 | 10.0 |
| Regularized logistic | endpoint | verified-reference | 1.000 | 23123.2 | 41791.1 | 0.0116 | 0.0057 | — | 0.0208 | 1819.9 | 0.007 | 0.008 | 0.992 | — | 0 | 10.0 |
| Regularized logistic | endpoint | verified-optimized | 1.000 | 23123.2 | 41791.1 | 0.0116 | 0.0057 | — | 0.0208 | 6225.1 | 0.007 | 0.008 | 0.992 | — | 0 | 10.0 |
| Regularized logistic | endpoint | advancedhmc | 1.001 | 23430.9 | 41867.0 | 0.0234 | 0.0057 | — | 0.0130 | 3022.7 | 0.007 | 0.007 | 0.992 | 0.992 | 0 | 10.0 |
| Regularized logistic | multinomial | verified-reference | 1.002 | 4012.4 | 8207.9 | 0.0020 | 0.0131 | — | 0.0326 | 200.8 | 0.014 | 0.018 | 0.909 | — | 0 | 10.0 |
| Regularized logistic | multinomial | verified-optimized | 1.002 | 4012.4 | 8207.9 | 0.0020 | 0.0131 | — | 0.0326 | 483.5 | 0.014 | 0.018 | 0.991 | — | 0 | 10.0 |
| Regularized logistic | multinomial | advancedhmc | 1.004 | 3894.3 | 8449.2 | 0.0039 | 0.0128 | — | 0.0357 | 448.4 | 0.014 | 0.018 | 0.909 | 0.997 | 0 | 10.0 |
| Regularized logistic | nuts | verified-reference | 1.000 | 0.0 | 0.0 | 0.0000 | 0.0000 | — | 0.0000 | 0.0 | 0.000 | 1.000 | 0.000 | — | 0 | 22.5 |
| Regularized logistic | nuts | verified-optimized | 1.000 | 90000.0 | 64685.4 | 0.0089 | 0.0024 | — | 0.0069 | 2491.2 | 0.003 | 0.008 | 1.000 | 0.994 | 0 | 50.4 |
| Regularized logistic | nuts | advancedhmc | 1.000 | 90000.0 | 66197.1 | 0.0178 | 0.0024 | — | 0.0085 | 2417.5 | 0.003 | 0.008 | 1.000 | 0.994 | 0 | 50.4 |

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
