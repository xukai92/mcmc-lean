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

- Commit: `741d015`
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
| Isotropic Gaussian | 13821 | 81316 | 22755 |
| Correlated Gaussian (ρ=0.9) | 11563 | 43059 | 18983 |
| Product quartic | 10993 | 41550 | 18229 |
| Ill-conditioned Gaussian | 10554 | 41565 | 18842 |
| Regularized logistic | 8325 | 27368 | 13207 |

#### Multinomial

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Isotropic Gaussian | 11061 | 34680 | 18946 |
| Correlated Gaussian (ρ=0.9) | 8999 | 23176 | 16119 |
| Product quartic | 8252 | 19807 | 14766 |
| Ill-conditioned Gaussian | 8046 | 21135 | 15939 |
| Regularized logistic | 5468 | 12582 | 11614 |

#### Nuts

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Isotropic Gaussian | 1847 | 5443 | 4800 |
| Correlated Gaussian (ρ=0.9) | 1610 | 2590 | 2301 |
| Product quartic | 1479 | 6940 | 5703 |
| Ill-conditioned Gaussian | 1434 | 1111 | 766 |
| Regularized logistic | 1265 | 3133 | 2755 |

#### Preconditioned-endpoint

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Correlated Gaussian (ρ=0.9) | 4089 | 18764 | 10375 |
| Ill-conditioned Gaussian | 22677 | 158653 | 18259 |

#### Preconditioned-multinomial

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Correlated Gaussian (ρ=0.9) | 1843 | 15720 | 9428 |
| Ill-conditioned Gaussian | 5962 | 96416 | 14799 |

### Complete summary

| Target | Algorithm | Implementation | Median | IQR | Draws/s | Mean steps | Allocations |
|---|---|---|---:|---:|---:|---:|---:|
| Isotropic Gaussian | endpoint | verified-reference | 723.5 ms | 705.1–731.7 ms | 13821 | 10.0 | n/a |
| Isotropic Gaussian | endpoint | verified-optimized | 123.0 ms | 119.1–124.4 ms | 81316 | 10.0 | n/a |
| Isotropic Gaussian | endpoint | advancedhmc | 439.5 ms | 437.9–450.2 ms | 22755 | 10.0 | n/a |
| Isotropic Gaussian | multinomial | verified-reference | 904.1 ms | 894.4–906.3 ms | 11061 | 10.0 | n/a |
| Isotropic Gaussian | multinomial | verified-optimized | 288.3 ms | 286.1–291.7 ms | 34680 | 10.0 | n/a |
| Isotropic Gaussian | multinomial | advancedhmc | 527.8 ms | 524.6–528.4 ms | 18946 | 10.0 | n/a |
| Isotropic Gaussian | nuts | verified-reference | 5415.1 ms | 5269.7–5464.7 ms | 1847 | 16.0 | n/a |
| Isotropic Gaussian | nuts | verified-optimized | 1837.2 ms | 1806.8–1852.2 ms | 5443 | 63.0 | n/a |
| Isotropic Gaussian | nuts | advancedhmc | 2083.4 ms | 2056.7–2151.5 ms | 4800 | 63.0 | n/a |
| Correlated Gaussian (ρ=0.9) | endpoint | verified-reference | 864.9 ms | 840.7–873.5 ms | 11563 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | endpoint | verified-optimized | 232.2 ms | 231.1–233.0 ms | 43059 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | endpoint | advancedhmc | 526.8 ms | 522.2–529.8 ms | 18983 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | multinomial | verified-reference | 1111.2 ms | 1106.6–1127.5 ms | 8999 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | multinomial | verified-optimized | 431.5 ms | 426.8–457.8 ms | 23176 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | multinomial | advancedhmc | 620.4 ms | 606.8–632.2 ms | 16119 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | nuts | verified-reference | 6209.4 ms | 6087.8–6278.2 ms | 1610 | 16.0 | n/a |
| Correlated Gaussian (ρ=0.9) | nuts | verified-optimized | 3861.2 ms | 3833.1–3893.8 ms | 2590 | 122.6 | n/a |
| Correlated Gaussian (ρ=0.9) | nuts | advancedhmc | 4346.9 ms | 4265.7–4459.6 ms | 2301 | 122.4 | n/a |
| Correlated Gaussian (ρ=0.9) | preconditioned-endpoint | verified-reference | 2445.3 ms | 2435.4–2457.8 ms | 4089 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | preconditioned-endpoint | verified-optimized | 532.9 ms | 530.2–542.4 ms | 18764 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | preconditioned-endpoint | advancedhmc | 963.8 ms | 949.4–979.3 ms | 10375 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | preconditioned-multinomial | verified-reference | 5424.8 ms | 5379.7–5471.9 ms | 1843 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | preconditioned-multinomial | verified-optimized | 636.2 ms | 627.0–644.8 ms | 15720 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | preconditioned-multinomial | advancedhmc | 1060.7 ms | 1052.7–1072.5 ms | 9428 | 10.0 | n/a |
| Product quartic | endpoint | verified-reference | 909.6 ms | 886.3–916.6 ms | 10993 | 10.0 | n/a |
| Product quartic | endpoint | verified-optimized | 240.7 ms | 238.8–241.8 ms | 41550 | 10.0 | n/a |
| Product quartic | endpoint | advancedhmc | 548.6 ms | 545.6–555.1 ms | 18229 | 10.0 | n/a |
| Product quartic | multinomial | verified-reference | 1211.8 ms | 1184.2–1245.4 ms | 8252 | 10.0 | n/a |
| Product quartic | multinomial | verified-optimized | 504.9 ms | 501.2–507.3 ms | 19807 | 10.0 | n/a |
| Product quartic | multinomial | advancedhmc | 677.2 ms | 674.6–680.1 ms | 14766 | 10.0 | n/a |
| Product quartic | nuts | verified-reference | 6759.1 ms | 6621.2–6854.3 ms | 1479 | 16.0 | n/a |
| Product quartic | nuts | verified-optimized | 1440.9 ms | 1435.8–1450.4 ms | 6940 | 31.0 | n/a |
| Product quartic | nuts | advancedhmc | 1753.4 ms | 1735.3–1759.8 ms | 5703 | 31.0 | n/a |
| Ill-conditioned Gaussian | endpoint | verified-reference | 947.5 ms | 933.3–957.7 ms | 10554 | 10.0 | n/a |
| Ill-conditioned Gaussian | endpoint | verified-optimized | 240.6 ms | 239.2–242.2 ms | 41565 | 10.0 | n/a |
| Ill-conditioned Gaussian | endpoint | advancedhmc | 530.7 ms | 514.1–546.2 ms | 18842 | 10.0 | n/a |
| Ill-conditioned Gaussian | multinomial | verified-reference | 1242.9 ms | 1230.1–1253.0 ms | 8046 | 10.0 | n/a |
| Ill-conditioned Gaussian | multinomial | verified-optimized | 473.2 ms | 469.6–476.8 ms | 21135 | 10.0 | n/a |
| Ill-conditioned Gaussian | multinomial | advancedhmc | 627.4 ms | 613.9–628.9 ms | 15939 | 10.0 | n/a |
| Ill-conditioned Gaussian | nuts | verified-reference | 6973.5 ms | 6918.6–7048.9 ms | 1434 | 16.0 | n/a |
| Ill-conditioned Gaussian | nuts | verified-optimized | 9001.7 ms | 8926.6–9116.1 ms | 1111 | 323.1 | n/a |
| Ill-conditioned Gaussian | nuts | advancedhmc | 13046.8 ms | 13009.0–13190.9 ms | 766 | 323.4 | n/a |
| Ill-conditioned Gaussian | preconditioned-endpoint | verified-reference | 441.0 ms | 437.2–444.9 ms | 22677 | 10.0 | n/a |
| Ill-conditioned Gaussian | preconditioned-endpoint | verified-optimized | 63.0 ms | 62.4–64.0 ms | 158653 | 10.0 | n/a |
| Ill-conditioned Gaussian | preconditioned-endpoint | advancedhmc | 547.7 ms | 543.2–551.6 ms | 18259 | 10.0 | n/a |
| Ill-conditioned Gaussian | preconditioned-multinomial | verified-reference | 1677.4 ms | 1657.2–1725.5 ms | 5962 | 10.0 | n/a |
| Ill-conditioned Gaussian | preconditioned-multinomial | verified-optimized | 103.7 ms | 103.3–105.1 ms | 96416 | 10.0 | n/a |
| Ill-conditioned Gaussian | preconditioned-multinomial | advancedhmc | 675.7 ms | 672.5–678.0 ms | 14799 | 10.0 | n/a |
| Regularized logistic | endpoint | verified-reference | 1201.2 ms | 1188.1–1246.4 ms | 8325 | 10.0 | n/a |
| Regularized logistic | endpoint | verified-optimized | 365.4 ms | 362.7–367.1 ms | 27368 | 10.0 | n/a |
| Regularized logistic | endpoint | advancedhmc | 757.2 ms | 755.6–764.1 ms | 13207 | 10.0 | n/a |
| Regularized logistic | multinomial | verified-reference | 1828.8 ms | 1823.0–1845.1 ms | 5468 | 10.0 | n/a |
| Regularized logistic | multinomial | verified-optimized | 794.8 ms | 788.5–803.9 ms | 12582 | 10.0 | n/a |
| Regularized logistic | multinomial | advancedhmc | 861.0 ms | 859.4–865.8 ms | 11614 | 10.0 | n/a |
| Regularized logistic | nuts | verified-reference | 7902.6 ms | 7844.3–7921.7 ms | 1265 | 16.0 | n/a |
| Regularized logistic | nuts | verified-optimized | 3191.7 ms | 3183.5–3195.4 ms | 3133 | 50.4 | n/a |
| Regularized logistic | nuts | advancedhmc | 3629.5 ms | 3597.8–3638.6 ms | 2755 | 50.4 | n/a |

## Sampling quality

The same independently seeded full chains supply timing and quality evidence. Full-chain storage is included equally in every implementation's timing; diagnostics are computed afterward. Moment errors use each target's known zero mean and analytical or independently computed marginal variance. The table reports the worst split rank-normalized R-hat and minimum bulk/tail ESS among the first four coordinates after ten-percent per-chain burn-in. A warning marker at R-hat above 1.01 is conspicuous but non-gating.

| Target | Algorithm | Implementation | R-hat | Bulk ESS | Tail ESS | Bulk ESS/gradient proxy | Mean MCSE (max) | Covariance error (max) | Median error (max) | ESS/s | Mean RMSE (std.) | Variance RMSE (relative) | Movement | Acceptance | Divergences | Mean steps |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Isotropic Gaussian | endpoint | verified-reference | 1.001 | 15042.3 | 30906.0 | 0.0075 | 0.0083 | 0.0250 | 0.0298 | 2186.2 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Isotropic Gaussian | endpoint | verified-optimized | 1.001 | 15042.3 | 30906.0 | 0.0075 | 0.0083 | 0.0250 | 0.0298 | 12439.6 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Isotropic Gaussian | endpoint | advancedhmc | 1.001 | 15179.2 | 31583.1 | 0.0152 | 0.0083 | 0.0219 | 0.0203 | 3444.0 | 0.008 | 0.007 | 0.995 | 0.995 | 0 | 10.0 |
| Isotropic Gaussian | multinomial | verified-reference | 1.003 | 2768.7 | 6427.5 | 0.0014 | 0.0183 | 0.0601 | 0.0502 | 294.7 | 0.018 | 0.021 | 0.909 | — | 0 | 10.0 |
| Isotropic Gaussian | multinomial | verified-optimized | 1.003 | 2768.7 | 6427.5 | 0.0014 | 0.0183 | 0.0601 | 0.0502 | 920.6 | 0.018 | 0.021 | 0.991 | — | 0 | 10.0 |
| Isotropic Gaussian | multinomial | advancedhmc | 1.006 | 2787.5 | 6409.1 | 0.0028 | 0.0177 | 0.0608 | 0.0518 | 513.5 | 0.016 | 0.020 | 0.909 | 0.998 | 0 | 10.0 |
| Isotropic Gaussian | nuts | verified-reference | 1.001 | 5919.4 | 11556.4 | 0.0018 | 0.0131 | 0.0393 | 0.0381 | 108.2 | 0.012 | 0.014 | 0.995 | — | 0 | 16.0 |
| Isotropic Gaussian | nuts | verified-optimized | 1.000 | 90000.0 | 68651.3 | 0.0071 | 0.0021 | 0.0219 | 0.0072 | 4911.8 | 0.002 | 0.008 | 1.000 | 0.996 | 0 | 63.0 |
| Isotropic Gaussian | nuts | advancedhmc | 1.000 | 90000.0 | 67827.6 | 0.0143 | 0.0022 | 0.0233 | 0.0071 | 4299.3 | 0.002 | 0.009 | 1.000 | 0.996 | 0 | 63.0 |
| Correlated Gaussian (ρ=0.9) | endpoint | verified-reference | 1.006 | 2040.0 | 5988.2 | 0.0010 | 0.0208 | 0.0547 | 0.0402 | 234.6 | 0.019 | 0.025 | 0.973 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | endpoint | verified-optimized | 1.006 | 2040.0 | 5988.2 | 0.0010 | 0.0208 | 0.0547 | 0.0402 | 845.1 | 0.019 | 0.025 | 0.973 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | endpoint | advancedhmc | 1.005 | 2372.8 | 6405.1 | 0.0024 | 0.0212 | 0.0552 | 0.0620 | 431.5 | 0.031 | 0.026 | 0.974 | 0.974 | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | multinomial | verified-reference | ⚠ 1.020 | 537.0 | 2841.7 | 0.0003 | 0.0294 | 0.1682 | 0.0832 | 39.4 | 0.035 | 0.060 | 0.908 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | multinomial | verified-optimized | ⚠ 1.020 | 537.0 | 2841.7 | 0.0003 | 0.0294 | 0.1682 | 0.0832 | 99.4 | 0.035 | 0.060 | 0.991 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | multinomial | advancedhmc | ⚠ 1.031 | 604.4 | 2531.8 | 0.0006 | 0.0279 | 0.1029 | 0.1102 | 67.6 | 0.055 | 0.041 | 0.909 | 0.953 | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | nuts | verified-reference | ⚠ 1.013 | 1003.0 | 3757.9 | 0.0003 | 0.0257 | 0.0842 | 0.0930 | 13.8 | 0.040 | 0.032 | 0.932 | — | 0 | 16.0 |
| Correlated Gaussian (ρ=0.9) | nuts | verified-optimized | 1.000 | 64132.9 | 65822.9 | 0.0026 | 0.0045 | 0.0123 | 0.0105 | 1666.8 | 0.004 | 0.005 | 1.000 | 0.948 | 0 | 122.6 |
| Correlated Gaussian (ρ=0.9) | nuts | advancedhmc | 1.000 | 62565.6 | 67093.6 | 0.0051 | 0.0046 | 0.0125 | 0.0128 | 1444.8 | 0.003 | 0.006 | 1.000 | 0.948 | 0 | 122.4 |
| Correlated Gaussian (ρ=0.9) | preconditioned-endpoint | verified-reference | 1.001 | 15195.3 | 33300.2 | 0.0076 | 0.0082 | 0.0260 | 0.0286 | 643.6 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | preconditioned-endpoint | verified-optimized | 1.001 | 15195.3 | 33300.2 | 0.0138 | 0.0082 | 0.0260 | 0.0286 | 2939.3 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | preconditioned-endpoint | advancedhmc | 1.001 | 15789.1 | 32462.1 | 0.0158 | 0.0082 | 0.0194 | 0.0209 | 1649.0 | 0.010 | 0.007 | 0.995 | 0.995 | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | preconditioned-multinomial | verified-reference | 1.003 | 2704.1 | 6205.3 | 0.0014 | 0.0182 | 0.0469 | 0.0309 | 51.9 | 0.014 | 0.020 | 0.909 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | preconditioned-multinomial | verified-optimized | 1.003 | 2704.1 | 6205.3 | 0.0025 | 0.0182 | 0.0469 | 0.0309 | 439.3 | 0.014 | 0.020 | 0.909 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | preconditioned-multinomial | advancedhmc | 1.005 | 2725.7 | 6263.5 | 0.0027 | 0.0181 | 0.0577 | 0.0572 | 242.3 | 0.019 | 0.023 | 0.909 | 0.998 | 0 | 10.0 |
| Product quartic | endpoint | verified-reference | 1.000 | 36720.4 | 84182.5 | 0.0184 | 0.0038 | — | 0.0204 | 3913.5 | 0.006 | 0.004 | 0.988 | — | 0 | 10.0 |
| Product quartic | endpoint | verified-optimized | 1.000 | 36720.4 | 84182.5 | 0.0184 | 0.0038 | — | 0.0204 | 14341.9 | 0.006 | 0.004 | 0.988 | — | 0 | 10.0 |
| Product quartic | endpoint | advancedhmc | 1.000 | 36781.8 | 86589.9 | 0.0368 | 0.0037 | — | 0.0123 | 6578.3 | 0.005 | 0.004 | 0.988 | 0.988 | 0 | 10.0 |
| Product quartic | multinomial | verified-reference | 1.001 | 5888.8 | 16258.9 | 0.0029 | 0.0090 | — | 0.0298 | 470.1 | 0.012 | 0.010 | 0.909 | — | 0 | 10.0 |
| Product quartic | multinomial | verified-optimized | 1.001 | 5888.8 | 16258.9 | 0.0029 | 0.0090 | — | 0.0298 | 1130.2 | 0.012 | 0.010 | 0.991 | — | 0 | 10.0 |
| Product quartic | multinomial | advancedhmc | 1.003 | 5782.8 | 16728.8 | 0.0058 | 0.0089 | — | 0.0274 | 875.4 | 0.012 | 0.011 | 0.909 | 0.990 | 0 | 10.0 |
| Product quartic | nuts | verified-reference | 1.001 | 12222.1 | 28538.8 | 0.0038 | 0.0063 | — | 0.0232 | 186.0 | 0.008 | 0.008 | 0.995 | — | 0 | 16.0 |
| Product quartic | nuts | verified-optimized | 1.000 | 90000.0 | 76482.6 | 0.0145 | 0.0020 | — | 0.0100 | 6245.1 | 0.003 | 0.005 | 1.000 | 0.988 | 0 | 31.0 |
| Product quartic | nuts | advancedhmc | 1.000 | 90000.0 | 78149.5 | 0.0290 | 0.0021 | — | 0.0070 | 5157.9 | 0.003 | 0.006 | 1.000 | 0.988 | 0 | 31.0 |
| Ill-conditioned Gaussian | endpoint | verified-reference | 1.001 | 16306.8 | 32614.1 | 0.0082 | 0.2984 | 16.9459 | 2.8810 | 1799.7 | 0.048 | 0.023 | 0.873 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | endpoint | verified-optimized | 1.001 | 16306.8 | 32614.1 | 0.0082 | 0.2984 | 16.9459 | 2.8810 | 6926.1 | 0.048 | 0.023 | 0.873 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | endpoint | advancedhmc | 1.000 | 16030.4 | 31434.9 | 0.0160 | 0.3020 | 8.1615 | 1.2309 | 3064.2 | 0.030 | 0.030 | 0.877 | 0.876 | 0 | 10.0 |
| Ill-conditioned Gaussian | multinomial | verified-reference | 1.000 | 79177.0 | 53043.3 | 0.0396 | 0.2795 | 20.1561 | 1.6843 | 6463.0 | 0.051 | 0.057 | 0.905 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | multinomial | verified-optimized | 1.000 | 79177.0 | 53043.3 | 0.0396 | 0.2795 | 20.1561 | 1.6843 | 17051.8 | 0.051 | 0.057 | 0.991 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | multinomial | advancedhmc | 1.000 | 79795.2 | 52953.3 | 0.0798 | 0.2680 | 19.4246 | 2.5623 | 12973.5 | 0.056 | 0.063 | 0.906 | 0.895 | 0 | 10.0 |
| Ill-conditioned Gaussian | nuts | verified-reference | 1.000 | 87055.4 | 54706.2 | 0.0272 | 0.3021 | 13.3298 | 1.2211 | 1271.6 | 0.035 | 0.038 | 0.995 | — | 0 | 16.0 |
| Ill-conditioned Gaussian | nuts | verified-optimized | 1.000 | 87473.8 | 58750.0 | 0.0014 | 0.0529 | 1.3289 | 0.0390 | 988.9 | 0.003 | 0.008 | 1.000 | 0.888 | 0 | 323.1 |
| Ill-conditioned Gaussian | nuts | advancedhmc | 1.000 | 86754.6 | 55567.6 | 0.0027 | 0.0522 | 0.6444 | 0.0697 | 670.9 | 0.003 | 0.008 | 1.000 | 0.889 | 0 | 323.4 |
| Ill-conditioned Gaussian | preconditioned-endpoint | verified-reference | 1.001 | 15042.3 | 30906.0 | 0.0075 | 0.0798 | 1.3167 | 0.2859 | 3454.0 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | preconditioned-endpoint | verified-optimized | 1.001 | 15042.3 | 30906.0 | 0.0137 | 0.0798 | 1.3167 | 0.2859 | 24009.3 | 0.009 | 0.009 | 0.996 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | preconditioned-endpoint | advancedhmc | 1.001 | 15179.2 | 31583.1 | 0.0152 | 0.0764 | 1.1941 | 0.1266 | 2790.2 | 0.008 | 0.007 | 0.995 | 0.995 | 0 | 10.0 |
| Ill-conditioned Gaussian | preconditioned-multinomial | verified-reference | 1.003 | 2768.7 | 6427.5 | 0.0014 | 0.1737 | 2.8200 | 0.2501 | 157.3 | 0.018 | 0.021 | 0.909 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | preconditioned-multinomial | verified-optimized | 1.003 | 2768.7 | 6427.5 | 0.0025 | 0.1737 | 2.8200 | 0.2501 | 2547.6 | 0.018 | 0.021 | 0.909 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | preconditioned-multinomial | advancedhmc | 1.006 | 2787.5 | 6409.1 | 0.0028 | 0.1670 | 3.4796 | 0.3842 | 401.1 | 0.016 | 0.020 | 0.909 | 0.998 | 0 | 10.0 |
| Regularized logistic | endpoint | verified-reference | 1.000 | 23123.2 | 41791.1 | 0.0116 | 0.0057 | — | 0.0208 | 1892.7 | 0.007 | 0.008 | 0.992 | — | 0 | 10.0 |
| Regularized logistic | endpoint | verified-optimized | 1.000 | 23123.2 | 41791.1 | 0.0116 | 0.0057 | — | 0.0208 | 6248.8 | 0.007 | 0.008 | 0.992 | — | 0 | 10.0 |
| Regularized logistic | endpoint | advancedhmc | 1.001 | 23430.9 | 41867.0 | 0.0234 | 0.0057 | — | 0.0130 | 3123.4 | 0.007 | 0.007 | 0.992 | 0.992 | 0 | 10.0 |
| Regularized logistic | multinomial | verified-reference | 1.002 | 4012.4 | 8207.9 | 0.0020 | 0.0131 | — | 0.0326 | 211.3 | 0.014 | 0.018 | 0.909 | — | 0 | 10.0 |
| Regularized logistic | multinomial | verified-optimized | 1.002 | 4012.4 | 8207.9 | 0.0020 | 0.0131 | — | 0.0326 | 488.2 | 0.014 | 0.018 | 0.991 | — | 0 | 10.0 |
| Regularized logistic | multinomial | advancedhmc | 1.004 | 3894.3 | 8449.2 | 0.0039 | 0.0128 | — | 0.0357 | 447.1 | 0.014 | 0.018 | 0.909 | 0.997 | 0 | 10.0 |
| Regularized logistic | nuts | verified-reference | 1.001 | 8413.0 | 14982.2 | 0.0026 | 0.0093 | — | 0.0277 | 105.0 | 0.010 | 0.013 | 0.995 | — | 0 | 16.0 |
| Regularized logistic | nuts | verified-optimized | 1.000 | 90000.0 | 64685.4 | 0.0089 | 0.0024 | — | 0.0069 | 2822.0 | 0.003 | 0.008 | 1.000 | 0.994 | 0 | 50.4 |
| Regularized logistic | nuts | advancedhmc | 1.000 | 90000.0 | 66197.1 | 0.0178 | 0.0024 | — | 0.0085 | 2486.1 | 0.003 | 0.008 | 1.000 | 0.994 | 0 | 50.4 |

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
