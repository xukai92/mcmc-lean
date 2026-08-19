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

VerifiedSamplers `NUTS` is labelled `verified-reference`: it uses the completed-tree C.4 rerooting construction proved in Lean. The independent handwritten `Optimized.NUTS` is labelled `verified-optimized`; that label identifies the project's optimized implementation, for which conformance and statistical tests are empirical evidence rather than a formal transition-equivalence proof.

## Configuration

- Commit: `dd90fdb`
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
| Isotropic Gaussian | 14198 | 80764 | 22368 |
| Correlated Gaussian (ρ=0.9) | 11243 | 41367 | 19322 |
| Product quartic | 11048 | 41239 | 18348 |
| Ill-conditioned Gaussian | 10770 | 40746 | 18767 |
| Regularized logistic | 8484 | 28295 | 13579 |

#### Multinomial

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Isotropic Gaussian | 11456 | 34720 | 18986 |
| Correlated Gaussian (ρ=0.9) | 8878 | 21220 | 15910 |
| Product quartic | 8232 | 19700 | 14733 |
| Ill-conditioned Gaussian | 8097 | 20820 | 16094 |
| Regularized logistic | 5650 | 12972 | 11872 |

#### Nuts

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Isotropic Gaussian | 1901 | 5451 | 4777 |
| Correlated Gaussian (ρ=0.9) | 1625 | 2522 | 2207 |
| Product quartic | 1490 | 6986 | 5913 |
| Ill-conditioned Gaussian | 1401 | 1061 | 765 |
| Regularized logistic | 1290 | 3185 | 2855 |

#### Preconditioned-endpoint

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Correlated Gaussian (ρ=0.9) | 4067 | 5908 | 10365 |
| Ill-conditioned Gaussian | 22396 | 71244 | 17574 |

#### Preconditioned-multinomial

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Correlated Gaussian (ρ=0.9) | 1849 | 3566 | 9334 |
| Ill-conditioned Gaussian | 5725 | 14872 | 15012 |

### Complete summary

| Target | Algorithm | Implementation | Median | IQR | Draws/s | Mean steps | Allocations |
|---|---|---|---:|---:|---:|---:|---:|
| Isotropic Gaussian | endpoint | verified-reference | 704.3 ms | 690.3–713.9 ms | 14198 | 10.0 | n/a |
| Isotropic Gaussian | endpoint | verified-optimized | 123.8 ms | 122.8–125.0 ms | 80764 | 10.0 | n/a |
| Isotropic Gaussian | endpoint | advancedhmc | 447.1 ms | 439.0–451.4 ms | 22368 | 10.0 | n/a |
| Isotropic Gaussian | multinomial | verified-reference | 872.9 ms | 862.0–891.2 ms | 11456 | 10.0 | n/a |
| Isotropic Gaussian | multinomial | verified-optimized | 288.0 ms | 285.6–289.6 ms | 34720 | 10.0 | n/a |
| Isotropic Gaussian | multinomial | advancedhmc | 526.7 ms | 524.9–531.4 ms | 18986 | 10.0 | n/a |
| Isotropic Gaussian | nuts | verified-reference | 5261.2 ms | 5125.6–5402.8 ms | 1901 | 16.0 | n/a |
| Isotropic Gaussian | nuts | verified-optimized | 1834.5 ms | 1827.3–1851.4 ms | 5451 | 63.0 | n/a |
| Isotropic Gaussian | nuts | advancedhmc | 2093.3 ms | 2001.7–2147.0 ms | 4777 | 63.0 | n/a |
| Correlated Gaussian (ρ=0.9) | endpoint | verified-reference | 889.5 ms | 873.3–899.0 ms | 11243 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | endpoint | verified-optimized | 241.7 ms | 237.2–244.4 ms | 41367 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | endpoint | advancedhmc | 517.6 ms | 514.3–529.1 ms | 19322 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | multinomial | verified-reference | 1126.4 ms | 1104.9–1140.9 ms | 8878 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | multinomial | verified-optimized | 471.3 ms | 447.6–479.6 ms | 21220 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | multinomial | advancedhmc | 628.5 ms | 620.6–640.7 ms | 15910 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | nuts | verified-reference | 6154.4 ms | 6054.4–6297.7 ms | 1625 | 16.0 | n/a |
| Correlated Gaussian (ρ=0.9) | nuts | verified-optimized | 3965.3 ms | 3934.5–4004.9 ms | 2522 | 122.6 | n/a |
| Correlated Gaussian (ρ=0.9) | nuts | advancedhmc | 4530.8 ms | 4478.1–4570.8 ms | 2207 | 122.4 | n/a |
| Correlated Gaussian (ρ=0.9) | preconditioned-endpoint | verified-reference | 2458.9 ms | 2439.9–2464.0 ms | 4067 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | preconditioned-endpoint | verified-optimized | 1692.6 ms | 1683.7–1728.6 ms | 5908 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | preconditioned-endpoint | advancedhmc | 964.8 ms | 955.4–977.7 ms | 10365 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | preconditioned-multinomial | verified-reference | 5408.5 ms | 5388.0–5560.7 ms | 1849 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | preconditioned-multinomial | verified-optimized | 2804.2 ms | 2791.7–2839.1 ms | 3566 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | preconditioned-multinomial | advancedhmc | 1071.3 ms | 1060.0–1075.7 ms | 9334 | 10.0 | n/a |
| Product quartic | endpoint | verified-reference | 905.2 ms | 889.3–912.3 ms | 11048 | 10.0 | n/a |
| Product quartic | endpoint | verified-optimized | 242.5 ms | 240.8–243.8 ms | 41239 | 10.0 | n/a |
| Product quartic | endpoint | advancedhmc | 545.0 ms | 539.8–556.1 ms | 18348 | 10.0 | n/a |
| Product quartic | multinomial | verified-reference | 1214.8 ms | 1178.7–1236.1 ms | 8232 | 10.0 | n/a |
| Product quartic | multinomial | verified-optimized | 507.6 ms | 504.2–511.0 ms | 19700 | 10.0 | n/a |
| Product quartic | multinomial | advancedhmc | 678.7 ms | 672.9–681.7 ms | 14733 | 10.0 | n/a |
| Product quartic | nuts | verified-reference | 6709.3 ms | 6632.7–6793.5 ms | 1490 | 16.0 | n/a |
| Product quartic | nuts | verified-optimized | 1431.5 ms | 1429.9–1435.3 ms | 6986 | 31.0 | n/a |
| Product quartic | nuts | advancedhmc | 1691.3 ms | 1688.3–1710.8 ms | 5913 | 31.0 | n/a |
| Ill-conditioned Gaussian | endpoint | verified-reference | 928.5 ms | 909.7–936.5 ms | 10770 | 10.0 | n/a |
| Ill-conditioned Gaussian | endpoint | verified-optimized | 245.4 ms | 243.2–246.1 ms | 40746 | 10.0 | n/a |
| Ill-conditioned Gaussian | endpoint | advancedhmc | 532.9 ms | 516.2–543.8 ms | 18767 | 10.0 | n/a |
| Ill-conditioned Gaussian | multinomial | verified-reference | 1235.0 ms | 1226.0–1252.2 ms | 8097 | 10.0 | n/a |
| Ill-conditioned Gaussian | multinomial | verified-optimized | 480.3 ms | 476.1–484.9 ms | 20820 | 10.0 | n/a |
| Ill-conditioned Gaussian | multinomial | advancedhmc | 621.3 ms | 617.9–623.6 ms | 16094 | 10.0 | n/a |
| Ill-conditioned Gaussian | nuts | verified-reference | 7136.6 ms | 7010.3–7172.2 ms | 1401 | 16.0 | n/a |
| Ill-conditioned Gaussian | nuts | verified-optimized | 9421.8 ms | 9390.2–9532.9 ms | 1061 | 323.1 | n/a |
| Ill-conditioned Gaussian | nuts | advancedhmc | 13068.5 ms | 13028.8–13351.9 ms | 765 | 323.4 | n/a |
| Ill-conditioned Gaussian | preconditioned-endpoint | verified-reference | 446.5 ms | 442.9–449.6 ms | 22396 | 10.0 | n/a |
| Ill-conditioned Gaussian | preconditioned-endpoint | verified-optimized | 140.4 ms | 139.6–141.1 ms | 71244 | 10.0 | n/a |
| Ill-conditioned Gaussian | preconditioned-endpoint | advancedhmc | 569.0 ms | 564.9–575.2 ms | 17574 | 10.0 | n/a |
| Ill-conditioned Gaussian | preconditioned-multinomial | verified-reference | 1746.8 ms | 1710.1–1760.0 ms | 5725 | 10.0 | n/a |
| Ill-conditioned Gaussian | preconditioned-multinomial | verified-optimized | 672.4 ms | 668.7–678.3 ms | 14872 | 10.0 | n/a |
| Ill-conditioned Gaussian | preconditioned-multinomial | advancedhmc | 666.1 ms | 660.5–671.7 ms | 15012 | 10.0 | n/a |
| Regularized logistic | endpoint | verified-reference | 1178.6 ms | 1166.7–1198.9 ms | 8484 | 10.0 | n/a |
| Regularized logistic | endpoint | verified-optimized | 353.4 ms | 350.2–360.6 ms | 28295 | 10.0 | n/a |
| Regularized logistic | endpoint | advancedhmc | 736.4 ms | 732.2–740.9 ms | 13579 | 10.0 | n/a |
| Regularized logistic | multinomial | verified-reference | 1769.8 ms | 1757.0–1787.5 ms | 5650 | 10.0 | n/a |
| Regularized logistic | multinomial | verified-optimized | 770.9 ms | 765.0–780.8 ms | 12972 | 10.0 | n/a |
| Regularized logistic | multinomial | advancedhmc | 842.3 ms | 829.3–849.9 ms | 11872 | 10.0 | n/a |
| Regularized logistic | nuts | verified-reference | 7752.5 ms | 7686.6–7802.4 ms | 1290 | 16.0 | n/a |
| Regularized logistic | nuts | verified-optimized | 3139.9 ms | 3108.7–3157.9 ms | 3185 | 50.4 | n/a |
| Regularized logistic | nuts | advancedhmc | 3502.5 ms | 3485.5–3540.8 ms | 2855 | 50.4 | n/a |

## Sampling quality

The same independently seeded full chains supply timing and quality evidence. Full-chain storage is included equally in every implementation's timing; diagnostics are computed afterward. Moment errors use each target's known zero mean and analytical or independently computed marginal variance. The table reports the worst split rank-normalized R-hat and minimum bulk/tail ESS among the first four coordinates after ten-percent per-chain burn-in. A warning marker at R-hat above 1.01 is conspicuous but non-gating.

| Target | Algorithm | Implementation | R-hat | Bulk ESS | Tail ESS | Bulk ESS/gradient proxy | Mean MCSE (max) | Covariance error (max) | Median error (max) | ESS/s | Mean RMSE (std.) | Variance RMSE (relative) | Movement | Acceptance | Divergences | Mean steps |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Isotropic Gaussian | endpoint | verified-reference | 1.001 | 15042.3 | 30906.0 | 0.0075 | 0.0083 | 0.0250 | 0.0298 | 2238.1 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Isotropic Gaussian | endpoint | verified-optimized | 1.001 | 15042.3 | 30906.0 | 0.0075 | 0.0083 | 0.0250 | 0.0298 | 11878.5 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Isotropic Gaussian | endpoint | advancedhmc | 1.001 | 15179.2 | 31583.1 | 0.0152 | 0.0083 | 0.0219 | 0.0203 | 3434.5 | 0.008 | 0.007 | 0.995 | 0.995 | 0 | 10.0 |
| Isotropic Gaussian | multinomial | verified-reference | 1.003 | 2768.7 | 6427.5 | 0.0014 | 0.0183 | 0.0601 | 0.0502 | 303.1 | 0.018 | 0.021 | 0.909 | — | 0 | 10.0 |
| Isotropic Gaussian | multinomial | verified-optimized | 1.003 | 2768.7 | 6427.5 | 0.0014 | 0.0183 | 0.0601 | 0.0502 | 921.0 | 0.018 | 0.021 | 0.991 | — | 0 | 10.0 |
| Isotropic Gaussian | multinomial | advancedhmc | 1.006 | 2787.5 | 6409.1 | 0.0028 | 0.0177 | 0.0608 | 0.0518 | 512.3 | 0.016 | 0.020 | 0.909 | 0.998 | 0 | 10.0 |
| Isotropic Gaussian | nuts | verified-reference | 1.001 | 5919.4 | 11556.4 | 0.0018 | 0.0131 | 0.0393 | 0.0381 | 110.1 | 0.012 | 0.014 | 0.995 | — | 0 | 16.0 |
| Isotropic Gaussian | nuts | verified-optimized | 1.000 | 90000.0 | 68651.3 | 0.0071 | 0.0021 | 0.0219 | 0.0072 | 4901.5 | 0.002 | 0.008 | 1.000 | 0.996 | 0 | 63.0 |
| Isotropic Gaussian | nuts | advancedhmc | 1.000 | 90000.0 | 67827.6 | 0.0143 | 0.0022 | 0.0233 | 0.0071 | 4326.3 | 0.002 | 0.009 | 1.000 | 0.996 | 0 | 63.0 |
| Correlated Gaussian (ρ=0.9) | endpoint | verified-reference | 1.006 | 2040.0 | 5988.2 | 0.0010 | 0.0208 | 0.0547 | 0.0402 | 227.2 | 0.019 | 0.025 | 0.973 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | endpoint | verified-optimized | 1.006 | 2040.0 | 5988.2 | 0.0010 | 0.0208 | 0.0547 | 0.0402 | 816.3 | 0.019 | 0.025 | 0.973 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | endpoint | advancedhmc | 1.005 | 2372.8 | 6405.1 | 0.0024 | 0.0212 | 0.0552 | 0.0620 | 435.9 | 0.031 | 0.026 | 0.974 | 0.974 | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | multinomial | verified-reference | ⚠ 1.020 | 537.0 | 2841.7 | 0.0003 | 0.0294 | 0.1682 | 0.0832 | 39.2 | 0.035 | 0.060 | 0.908 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | multinomial | verified-optimized | ⚠ 1.020 | 537.0 | 2841.7 | 0.0003 | 0.0294 | 0.1682 | 0.0832 | 94.1 | 0.035 | 0.060 | 0.991 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | multinomial | advancedhmc | ⚠ 1.031 | 604.4 | 2531.8 | 0.0006 | 0.0279 | 0.1029 | 0.1102 | 66.4 | 0.055 | 0.041 | 0.909 | 0.953 | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | nuts | verified-reference | ⚠ 1.013 | 1003.0 | 3757.9 | 0.0003 | 0.0257 | 0.0842 | 0.0930 | 13.9 | 0.040 | 0.032 | 0.932 | — | 0 | 16.0 |
| Correlated Gaussian (ρ=0.9) | nuts | verified-optimized | 1.000 | 64132.9 | 65822.9 | 0.0026 | 0.0045 | 0.0123 | 0.0105 | 1616.3 | 0.004 | 0.005 | 1.000 | 0.948 | 0 | 122.6 |
| Correlated Gaussian (ρ=0.9) | nuts | advancedhmc | 1.000 | 62565.6 | 67093.6 | 0.0051 | 0.0046 | 0.0125 | 0.0128 | 1397.4 | 0.003 | 0.006 | 1.000 | 0.948 | 0 | 122.4 |
| Correlated Gaussian (ρ=0.9) | preconditioned-endpoint | verified-reference | 1.001 | 15195.3 | 33300.2 | 0.0076 | 0.0082 | 0.0260 | 0.0286 | 640.5 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | preconditioned-endpoint | verified-optimized | 1.001 | 15195.3 | 33300.2 | 0.0076 | 0.0082 | 0.0260 | 0.0286 | 923.4 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | preconditioned-endpoint | advancedhmc | 1.001 | 15789.1 | 32462.1 | 0.0158 | 0.0082 | 0.0194 | 0.0209 | 1646.3 | 0.010 | 0.007 | 0.995 | 0.995 | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | preconditioned-multinomial | verified-reference | 1.003 | 2704.1 | 6205.3 | 0.0014 | 0.0182 | 0.0469 | 0.0309 | 51.4 | 0.014 | 0.020 | 0.909 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | preconditioned-multinomial | verified-optimized | 1.003 | 2704.1 | 6205.3 | 0.0014 | 0.0182 | 0.0469 | 0.0309 | 99.9 | 0.014 | 0.020 | 0.991 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | preconditioned-multinomial | advancedhmc | 1.005 | 2725.7 | 6263.5 | 0.0027 | 0.0181 | 0.0577 | 0.0572 | 239.7 | 0.019 | 0.023 | 0.909 | 0.998 | 0 | 10.0 |
| Product quartic | endpoint | verified-reference | 1.000 | 36720.4 | 84182.5 | 0.0184 | 0.0038 | — | 0.0204 | 3929.2 | 0.006 | 0.004 | 0.988 | — | 0 | 10.0 |
| Product quartic | endpoint | verified-optimized | 1.000 | 36720.4 | 84182.5 | 0.0184 | 0.0038 | — | 0.0204 | 14208.6 | 0.006 | 0.004 | 0.988 | — | 0 | 10.0 |
| Product quartic | endpoint | advancedhmc | 1.000 | 36781.8 | 86589.9 | 0.0368 | 0.0037 | — | 0.0123 | 6627.3 | 0.005 | 0.004 | 0.988 | 0.988 | 0 | 10.0 |
| Product quartic | multinomial | verified-reference | 1.001 | 5888.8 | 16258.9 | 0.0029 | 0.0090 | — | 0.0298 | 471.4 | 0.012 | 0.010 | 0.909 | — | 0 | 10.0 |
| Product quartic | multinomial | verified-optimized | 1.001 | 5888.8 | 16258.9 | 0.0029 | 0.0090 | — | 0.0298 | 1120.5 | 0.012 | 0.010 | 0.991 | — | 0 | 10.0 |
| Product quartic | multinomial | advancedhmc | 1.003 | 5782.8 | 16728.8 | 0.0058 | 0.0089 | — | 0.0274 | 871.2 | 0.012 | 0.011 | 0.909 | 0.990 | 0 | 10.0 |
| Product quartic | nuts | verified-reference | 1.001 | 12222.1 | 28538.8 | 0.0038 | 0.0063 | — | 0.0232 | 186.8 | 0.008 | 0.008 | 0.995 | — | 0 | 16.0 |
| Product quartic | nuts | verified-optimized | 1.000 | 90000.0 | 76482.6 | 0.0145 | 0.0020 | — | 0.0100 | 6287.4 | 0.003 | 0.005 | 1.000 | 0.988 | 0 | 31.0 |
| Product quartic | nuts | advancedhmc | 1.000 | 90000.0 | 78149.5 | 0.0290 | 0.0021 | — | 0.0070 | 5305.5 | 0.003 | 0.006 | 1.000 | 0.988 | 0 | 31.0 |
| Ill-conditioned Gaussian | endpoint | verified-reference | 1.001 | 16306.8 | 32614.1 | 0.0082 | 0.2984 | 16.9459 | 2.8810 | 1837.6 | 0.048 | 0.023 | 0.873 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | endpoint | verified-optimized | 1.001 | 16306.8 | 32614.1 | 0.0082 | 0.2984 | 16.9459 | 2.8810 | 6803.6 | 0.048 | 0.023 | 0.873 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | endpoint | advancedhmc | 1.000 | 16030.4 | 31434.9 | 0.0160 | 0.3020 | 8.1615 | 1.2309 | 3064.9 | 0.030 | 0.030 | 0.877 | 0.876 | 0 | 10.0 |
| Ill-conditioned Gaussian | multinomial | verified-reference | 1.000 | 79177.0 | 53043.3 | 0.0396 | 0.2795 | 20.1561 | 1.6843 | 6495.4 | 0.051 | 0.057 | 0.905 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | multinomial | verified-optimized | 1.000 | 79177.0 | 53043.3 | 0.0396 | 0.2795 | 20.1561 | 1.6843 | 16783.1 | 0.051 | 0.057 | 0.991 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | multinomial | advancedhmc | 1.000 | 79795.2 | 52953.3 | 0.0798 | 0.2680 | 19.4246 | 2.5623 | 13007.9 | 0.056 | 0.063 | 0.906 | 0.895 | 0 | 10.0 |
| Ill-conditioned Gaussian | nuts | verified-reference | 1.000 | 87055.4 | 54706.2 | 0.0272 | 0.3021 | 13.3298 | 1.2211 | 1248.8 | 0.035 | 0.038 | 0.995 | — | 0 | 16.0 |
| Ill-conditioned Gaussian | nuts | verified-optimized | 1.000 | 87473.8 | 58750.0 | 0.0014 | 0.0529 | 1.3289 | 0.0390 | 940.9 | 0.003 | 0.008 | 1.000 | 0.888 | 0 | 323.1 |
| Ill-conditioned Gaussian | nuts | advancedhmc | 1.000 | 86754.6 | 55567.6 | 0.0027 | 0.0522 | 0.6444 | 0.0697 | 668.2 | 0.003 | 0.008 | 1.000 | 0.889 | 0 | 323.4 |
| Ill-conditioned Gaussian | preconditioned-endpoint | verified-reference | 1.001 | 15042.3 | 30906.0 | 0.0075 | 0.0798 | 1.3167 | 0.2859 | 3400.8 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | preconditioned-endpoint | verified-optimized | 1.001 | 15042.3 | 30906.0 | 0.0075 | 0.0798 | 1.3167 | 0.2859 | 10802.7 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | preconditioned-endpoint | advancedhmc | 1.001 | 15179.2 | 31583.1 | 0.0152 | 0.0764 | 1.1941 | 0.1266 | 2677.3 | 0.008 | 0.007 | 0.995 | 0.995 | 0 | 10.0 |
| Ill-conditioned Gaussian | preconditioned-multinomial | verified-reference | 1.003 | 2768.7 | 6427.5 | 0.0014 | 0.1737 | 2.8200 | 0.2501 | 153.1 | 0.018 | 0.021 | 0.909 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | preconditioned-multinomial | verified-optimized | 1.003 | 2768.7 | 6427.5 | 0.0014 | 0.1737 | 2.8200 | 0.2501 | 394.9 | 0.018 | 0.021 | 0.991 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | preconditioned-multinomial | advancedhmc | 1.006 | 2787.5 | 6409.1 | 0.0028 | 0.1670 | 3.4796 | 0.3842 | 412.8 | 0.016 | 0.020 | 0.909 | 0.998 | 0 | 10.0 |
| Regularized logistic | endpoint | verified-reference | 1.000 | 23123.2 | 41791.1 | 0.0116 | 0.0057 | — | 0.0208 | 1942.7 | 0.007 | 0.008 | 0.992 | — | 0 | 10.0 |
| Regularized logistic | endpoint | verified-optimized | 1.000 | 23123.2 | 41791.1 | 0.0116 | 0.0057 | — | 0.0208 | 6395.6 | 0.007 | 0.008 | 0.992 | — | 0 | 10.0 |
| Regularized logistic | endpoint | advancedhmc | 1.001 | 23430.9 | 41867.0 | 0.0234 | 0.0057 | — | 0.0130 | 3206.7 | 0.007 | 0.007 | 0.992 | 0.992 | 0 | 10.0 |
| Regularized logistic | multinomial | verified-reference | 1.002 | 4012.4 | 8207.9 | 0.0020 | 0.0131 | — | 0.0326 | 218.8 | 0.014 | 0.018 | 0.909 | — | 0 | 10.0 |
| Regularized logistic | multinomial | verified-optimized | 1.002 | 4012.4 | 8207.9 | 0.0020 | 0.0131 | — | 0.0326 | 502.1 | 0.014 | 0.018 | 0.991 | — | 0 | 10.0 |
| Regularized logistic | multinomial | advancedhmc | 1.004 | 3894.3 | 8449.2 | 0.0039 | 0.0128 | — | 0.0357 | 459.1 | 0.014 | 0.018 | 0.909 | 0.997 | 0 | 10.0 |
| Regularized logistic | nuts | verified-reference | 1.001 | 8413.0 | 14982.2 | 0.0026 | 0.0093 | — | 0.0277 | 107.1 | 0.010 | 0.013 | 0.995 | — | 0 | 16.0 |
| Regularized logistic | nuts | verified-optimized | 1.000 | 90000.0 | 64685.4 | 0.0089 | 0.0024 | — | 0.0069 | 2861.6 | 0.003 | 0.008 | 1.000 | 0.994 | 0 | 50.4 |
| Regularized logistic | nuts | advancedhmc | 1.000 | 90000.0 | 66197.1 | 0.0178 | 0.0024 | — | 0.0085 | 2565.4 | 0.003 | 0.008 | 1.000 | 0.994 | 0 | 50.4 |

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
