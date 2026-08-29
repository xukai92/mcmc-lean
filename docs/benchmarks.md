# Sampler benchmark report

!!! warning "Development-mode results"
    This page was generated from a short `--dev` run for layout iteration. Its timings are not publication-quality.

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

- Commit: `a17a3aa`
- Julia: `1.12.5`
- CPU: `Intel Xeon Processor (SapphireRapids)`
- Dimension: `100`
- Draws per measured chain: `100`
- Complete-chain timing repetitions per case: `2`
- Step size: `0.08`
- Fixed trajectory length: `10` leapfrog steps
- Shared NUTS depth budget: `4`
- Completed-tree trajectory length: `16` leapfrog steps
- Gradients: analytic callbacks for both packages; AD time excluded

- Fixed timed/quality seeds per main-suite case: `4109, 4110`
- Retained timed chains per case: `2`

## Results

### Median transitions per second

#### Endpoint

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Isotropic Gaussian | 29628 | 151799 | 64770 |
| Correlated Gaussian (ρ=0.9) | 26303 | 103739 | 57982 |
| Product quartic | 25045 | 94330 | 44941 |
| Ill-conditioned Gaussian | 24425 | 101519 | 55636 |
| Regularized logistic | 15122 | 43447 | 25707 |

#### Multinomial

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Isotropic Gaussian | 27418 | 80319 | 42521 |
| Correlated Gaussian (ρ=0.9) | 20126 | 55112 | 38360 |
| Product quartic | 18046 | 43584 | 32339 |
| Ill-conditioned Gaussian | 20171 | 55548 | 37086 |
| Regularized logistic | 9676 | 20977 | 21560 |

#### Nuts-complete

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Isotropic Gaussian | 1292 | 53258 | 28417 |
| Correlated Gaussian (ρ=0.9) | 1430 | 36501 | 27149 |
| Product quartic | 1405 | 30041 | 23819 |
| Ill-conditioned Gaussian | 1432 | 37209 | 27487 |
| Regularized logistic | 1300 | 13162 | 14964 |

#### Nuts-dynamic

| Target | verified-optimized | advancedhmc |
|---|---:|---:|
| Isotropic Gaussian | 46499 | 32513 |
| Correlated Gaussian (ρ=0.9) | 36179 | 29349 |
| Product quartic | 29995 | 24799 |
| Ill-conditioned Gaussian | 35368 | 28085 |
| Regularized logistic | 15745 | 15811 |

#### MALA

| Target | verified-reference | verified-optimized |
|---|---:|---:|
| Isotropic Gaussian | 73133 | 680288 |
| Correlated Gaussian (ρ=0.9) | 68629 | 511476 |
| Product quartic | 70036 | 365130 |
| Ill-conditioned Gaussian | 68888 | 464374 |
| Regularized logistic | 54556 | 186302 |

#### Gauss-legendre-2stage

| Target | verified-reference | verified-optimized |
|---|---:|---:|
| Isotropic Gaussian | 1079 | 3665 |
| Correlated Gaussian (ρ=0.9) | 1011 | 2907 |
| Product quartic | 982 | 2762 |
| Ill-conditioned Gaussian | 972 | 2746 |
| Regularized logistic | 796 | 2071 |

#### Gauss-legendre-2stage-parallel

| Target | verified-optimized |
|---|---:|
| Isotropic Gaussian | 1008 |
| Correlated Gaussian (ρ=0.9) | 1007 |
| Product quartic | 989 |
| Ill-conditioned Gaussian | 1003 |
| Regularized logistic | 946 |

#### Gauss-legendre-2stage-simd

| Target | verified-optimized |
|---|---:|
| Isotropic Gaussian | 38090 |
| Correlated Gaussian (ρ=0.9) | 21019 |
| Product quartic | 18053 |
| Ill-conditioned Gaussian | 19653 |
| Regularized logistic | 6717 |

#### Endpoint-dense

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Correlated Gaussian (ρ=0.9) | 4739 | 20271 | 17429 |

#### Multinomial-dense

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Correlated Gaussian (ρ=0.9) | 2268 | 12113 | 16093 |

#### Endpoint-diagonal

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Ill-conditioned Gaussian | 52936 | 205572 | 52221 |

#### Multinomial-diagonal

| Target | verified-reference | verified-optimized | advancedhmc |
|---|---:|---:|---:|
| Ill-conditioned Gaussian | 14369 | 127356 | 34568 |

### Complete summary

| Target | Algorithm | Implementation | Median | IQR | Draws/s | Mean steps | Allocations |
|---|---|---|---:|---:|---:|---:|---:|
| Isotropic Gaussian | endpoint | verified-reference | 3.4 ms | 3.2–3.6 ms | 29628 | 10.0 | n/a |
| Isotropic Gaussian | endpoint | verified-optimized | 0.7 ms | 0.7–0.7 ms | 151799 | 10.0 | n/a |
| Isotropic Gaussian | endpoint | advancedhmc | 1.5 ms | 1.5–1.6 ms | 64770 | 10.0 | n/a |
| Isotropic Gaussian | multinomial | verified-reference | 3.6 ms | 3.6–3.7 ms | 27418 | 10.0 | n/a |
| Isotropic Gaussian | multinomial | verified-optimized | 1.2 ms | 1.2–1.3 ms | 80319 | 10.0 | n/a |
| Isotropic Gaussian | multinomial | advancedhmc | 2.4 ms | 2.3–2.4 ms | 42521 | 10.0 | n/a |
| Isotropic Gaussian | nuts-complete | verified-reference | 77.4 ms | 73.1–81.7 ms | 1292 | 16.0 | n/a |
| Isotropic Gaussian | nuts-complete | verified-optimized | 1.9 ms | 1.9–1.9 ms | 53258 | 16.0 | n/a |
| Isotropic Gaussian | nuts-complete | advancedhmc | 3.5 ms | 3.5–3.6 ms | 28417 | 16.0 | n/a |
| Isotropic Gaussian | nuts-dynamic | verified-optimized | 2.2 ms | 2.1–2.2 ms | 46499 | 15.0 | n/a |
| Isotropic Gaussian | nuts-dynamic | advancedhmc | 3.1 ms | 3.1–3.1 ms | 32513 | 15.0 | n/a |
| Isotropic Gaussian | mala | verified-reference | 1.4 ms | 1.4–1.4 ms | 73133 | 1.0 | n/a |
| Isotropic Gaussian | mala | verified-optimized | 0.1 ms | 0.1–0.2 ms | 680288 | 1.0 | n/a |
| Isotropic Gaussian | gauss-legendre-2stage | verified-reference | 92.7 ms | 91.8–93.5 ms | 1079 | 10.0 | n/a |
| Isotropic Gaussian | gauss-legendre-2stage | verified-optimized | 27.3 ms | 27.2–27.4 ms | 3665 | 10.0 | n/a |
| Isotropic Gaussian | gauss-legendre-2stage-parallel | verified-optimized | 99.2 ms | 96.8–101.7 ms | 1008 | 10.0 | n/a |
| Isotropic Gaussian | gauss-legendre-2stage-simd | verified-optimized | 2.6 ms | 2.6–2.7 ms | 38090 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | endpoint | verified-reference | 3.8 ms | 3.7–3.9 ms | 26303 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | endpoint | verified-optimized | 1.0 ms | 0.9–1.0 ms | 103739 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | endpoint | advancedhmc | 1.7 ms | 1.7–1.7 ms | 57982 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | multinomial | verified-reference | 5.0 ms | 5.0–5.0 ms | 20126 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | multinomial | verified-optimized | 1.8 ms | 1.8–1.8 ms | 55112 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | multinomial | advancedhmc | 2.6 ms | 2.6–2.6 ms | 38360 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | nuts-complete | verified-reference | 69.9 ms | 69.6–70.3 ms | 1430 | 16.0 | n/a |
| Correlated Gaussian (ρ=0.9) | nuts-complete | verified-optimized | 2.7 ms | 2.7–2.8 ms | 36501 | 16.0 | n/a |
| Correlated Gaussian (ρ=0.9) | nuts-complete | advancedhmc | 3.7 ms | 3.7–3.7 ms | 27149 | 16.0 | n/a |
| Correlated Gaussian (ρ=0.9) | nuts-dynamic | verified-optimized | 2.8 ms | 2.7–2.8 ms | 36179 | 15.0 | n/a |
| Correlated Gaussian (ρ=0.9) | nuts-dynamic | advancedhmc | 3.4 ms | 3.4–3.4 ms | 29349 | 15.0 | n/a |
| Correlated Gaussian (ρ=0.9) | mala | verified-reference | 1.5 ms | 1.4–1.5 ms | 68629 | 1.0 | n/a |
| Correlated Gaussian (ρ=0.9) | mala | verified-optimized | 0.2 ms | 0.2–0.2 ms | 511476 | 1.0 | n/a |
| Correlated Gaussian (ρ=0.9) | gauss-legendre-2stage | verified-reference | 98.9 ms | 98.3–99.4 ms | 1011 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | gauss-legendre-2stage | verified-optimized | 34.4 ms | 34.3–34.5 ms | 2907 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | gauss-legendre-2stage-parallel | verified-optimized | 99.3 ms | 98.1–100.5 ms | 1007 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | gauss-legendre-2stage-simd | verified-optimized | 4.8 ms | 4.7–4.8 ms | 21019 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | endpoint-dense | verified-reference | 21.1 ms | 20.8–21.4 ms | 4739 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | endpoint-dense | verified-optimized | 4.9 ms | 4.9–5.0 ms | 20271 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | endpoint-dense | advancedhmc | 5.7 ms | 5.7–5.8 ms | 17429 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | multinomial-dense | verified-reference | 44.1 ms | 43.8–44.4 ms | 2268 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | multinomial-dense | verified-optimized | 8.3 ms | 7.4–9.1 ms | 12113 | 10.0 | n/a |
| Correlated Gaussian (ρ=0.9) | multinomial-dense | advancedhmc | 6.2 ms | 6.1–6.3 ms | 16093 | 10.0 | n/a |
| Product quartic | endpoint | verified-reference | 4.0 ms | 3.9–4.0 ms | 25045 | 10.0 | n/a |
| Product quartic | endpoint | verified-optimized | 1.1 ms | 1.1–1.1 ms | 94330 | 10.0 | n/a |
| Product quartic | endpoint | advancedhmc | 2.2 ms | 2.2–2.2 ms | 44941 | 10.0 | n/a |
| Product quartic | multinomial | verified-reference | 5.5 ms | 5.5–5.6 ms | 18046 | 10.0 | n/a |
| Product quartic | multinomial | verified-optimized | 2.3 ms | 2.3–2.3 ms | 43584 | 10.0 | n/a |
| Product quartic | multinomial | advancedhmc | 3.1 ms | 3.1–3.1 ms | 32339 | 10.0 | n/a |
| Product quartic | nuts-complete | verified-reference | 71.2 ms | 70.7–71.6 ms | 1405 | 16.0 | n/a |
| Product quartic | nuts-complete | verified-optimized | 3.3 ms | 3.3–3.3 ms | 30041 | 16.0 | n/a |
| Product quartic | nuts-complete | advancedhmc | 4.2 ms | 4.2–4.2 ms | 23819 | 16.0 | n/a |
| Product quartic | nuts-dynamic | verified-optimized | 3.3 ms | 3.3–3.3 ms | 29995 | 15.0 | n/a |
| Product quartic | nuts-dynamic | advancedhmc | 4.0 ms | 4.0–4.0 ms | 24799 | 15.0 | n/a |
| Product quartic | mala | verified-reference | 1.4 ms | 1.4–1.4 ms | 70036 | 1.0 | n/a |
| Product quartic | mala | verified-optimized | 0.3 ms | 0.3–0.3 ms | 365130 | 1.0 | n/a |
| Product quartic | gauss-legendre-2stage | verified-reference | 101.8 ms | 101.8–101.9 ms | 982 | 10.0 | n/a |
| Product quartic | gauss-legendre-2stage | verified-optimized | 36.2 ms | 35.9–36.5 ms | 2762 | 10.0 | n/a |
| Product quartic | gauss-legendre-2stage-parallel | verified-optimized | 101.1 ms | 100.7–101.6 ms | 989 | 10.0 | n/a |
| Product quartic | gauss-legendre-2stage-simd | verified-optimized | 5.5 ms | 5.2–5.9 ms | 18053 | 10.0 | n/a |
| Ill-conditioned Gaussian | endpoint | verified-reference | 4.1 ms | 4.1–4.1 ms | 24425 | 10.0 | n/a |
| Ill-conditioned Gaussian | endpoint | verified-optimized | 1.0 ms | 1.0–1.0 ms | 101519 | 10.0 | n/a |
| Ill-conditioned Gaussian | endpoint | advancedhmc | 1.8 ms | 1.8–1.8 ms | 55636 | 10.0 | n/a |
| Ill-conditioned Gaussian | multinomial | verified-reference | 5.0 ms | 4.9–5.0 ms | 20171 | 10.0 | n/a |
| Ill-conditioned Gaussian | multinomial | verified-optimized | 1.8 ms | 1.8–1.8 ms | 55548 | 10.0 | n/a |
| Ill-conditioned Gaussian | multinomial | advancedhmc | 2.7 ms | 2.7–2.7 ms | 37086 | 10.0 | n/a |
| Ill-conditioned Gaussian | nuts-complete | verified-reference | 69.8 ms | 69.7–70.0 ms | 1432 | 16.0 | n/a |
| Ill-conditioned Gaussian | nuts-complete | verified-optimized | 2.7 ms | 2.7–2.7 ms | 37209 | 16.0 | n/a |
| Ill-conditioned Gaussian | nuts-complete | advancedhmc | 3.6 ms | 3.6–3.6 ms | 27487 | 16.0 | n/a |
| Ill-conditioned Gaussian | nuts-dynamic | verified-optimized | 2.8 ms | 2.8–2.9 ms | 35368 | 15.0 | n/a |
| Ill-conditioned Gaussian | nuts-dynamic | advancedhmc | 3.6 ms | 3.6–3.6 ms | 28085 | 15.0 | n/a |
| Ill-conditioned Gaussian | mala | verified-reference | 1.5 ms | 1.4–1.5 ms | 68888 | 1.0 | n/a |
| Ill-conditioned Gaussian | mala | verified-optimized | 0.2 ms | 0.2–0.2 ms | 464374 | 1.0 | n/a |
| Ill-conditioned Gaussian | gauss-legendre-2stage | verified-reference | 102.8 ms | 102.2–103.5 ms | 972 | 10.0 | n/a |
| Ill-conditioned Gaussian | gauss-legendre-2stage | verified-optimized | 36.4 ms | 36.3–36.5 ms | 2746 | 10.0 | n/a |
| Ill-conditioned Gaussian | gauss-legendre-2stage-parallel | verified-optimized | 99.7 ms | 99.3–100.1 ms | 1003 | 10.0 | n/a |
| Ill-conditioned Gaussian | gauss-legendre-2stage-simd | verified-optimized | 5.1 ms | 5.0–5.2 ms | 19653 | 10.0 | n/a |
| Ill-conditioned Gaussian | endpoint-diagonal | verified-reference | 1.9 ms | 1.8–1.9 ms | 52936 | 10.0 | n/a |
| Ill-conditioned Gaussian | endpoint-diagonal | verified-optimized | 0.5 ms | 0.5–0.5 ms | 205572 | 10.0 | n/a |
| Ill-conditioned Gaussian | endpoint-diagonal | advancedhmc | 1.9 ms | 1.9–1.9 ms | 52221 | 10.0 | n/a |
| Ill-conditioned Gaussian | multinomial-diagonal | verified-reference | 7.0 ms | 6.9–7.0 ms | 14369 | 10.0 | n/a |
| Ill-conditioned Gaussian | multinomial-diagonal | verified-optimized | 0.8 ms | 0.8–0.8 ms | 127356 | 10.0 | n/a |
| Ill-conditioned Gaussian | multinomial-diagonal | advancedhmc | 2.9 ms | 2.9–2.9 ms | 34568 | 10.0 | n/a |
| Regularized logistic | endpoint | verified-reference | 6.6 ms | 6.5–6.7 ms | 15122 | 10.0 | n/a |
| Regularized logistic | endpoint | verified-optimized | 2.3 ms | 2.3–2.3 ms | 43447 | 10.0 | n/a |
| Regularized logistic | endpoint | advancedhmc | 3.9 ms | 3.8–4.0 ms | 25707 | 10.0 | n/a |
| Regularized logistic | multinomial | verified-reference | 10.3 ms | 10.3–10.4 ms | 9676 | 10.0 | n/a |
| Regularized logistic | multinomial | verified-optimized | 4.8 ms | 4.7–4.9 ms | 20977 | 10.0 | n/a |
| Regularized logistic | multinomial | advancedhmc | 4.6 ms | 4.6–4.7 ms | 21560 | 10.0 | n/a |
| Regularized logistic | nuts-complete | verified-reference | 76.9 ms | 76.8–77.0 ms | 1300 | 16.0 | n/a |
| Regularized logistic | nuts-complete | verified-optimized | 7.6 ms | 7.6–7.6 ms | 13162 | 16.0 | n/a |
| Regularized logistic | nuts-complete | advancedhmc | 6.7 ms | 6.6–6.7 ms | 14964 | 16.0 | n/a |
| Regularized logistic | nuts-dynamic | verified-optimized | 6.4 ms | 6.3–6.4 ms | 15745 | 15.0 | n/a |
| Regularized logistic | nuts-dynamic | advancedhmc | 6.3 ms | 6.3–6.3 ms | 15811 | 15.0 | n/a |
| Regularized logistic | mala | verified-reference | 1.8 ms | 1.8–1.9 ms | 54556 | 1.0 | n/a |
| Regularized logistic | mala | verified-optimized | 0.5 ms | 0.5–0.5 ms | 186302 | 1.0 | n/a |
| Regularized logistic | gauss-legendre-2stage | verified-reference | 125.6 ms | 125.4–125.7 ms | 796 | 10.0 | n/a |
| Regularized logistic | gauss-legendre-2stage | verified-optimized | 48.3 ms | 48.1–48.5 ms | 2071 | 10.0 | n/a |
| Regularized logistic | gauss-legendre-2stage-parallel | verified-optimized | 105.7 ms | 103.3–108.1 ms | 946 | 10.0 | n/a |
| Regularized logistic | gauss-legendre-2stage-simd | verified-optimized | 14.9 ms | 14.7–15.1 ms | 6717 | 10.0 | n/a |

## Sampling quality

The same independently seeded full chains supply timing and quality evidence. Full-chain storage is included equally in every implementation's timing; diagnostics are computed afterward. Moment errors use each target's known zero mean and analytical or independently computed marginal variance. The table reports the worst split rank-normalized R-hat and minimum bulk/tail ESS among the first four coordinates after ten-percent per-chain burn-in. A warning marker at R-hat above 1.01 is conspicuous but non-gating.

| Target | Algorithm | Implementation | R-hat | Bulk ESS | Tail ESS | Bulk ESS/gradient proxy | Mean MCSE (max) | Covariance error (max) | Median error (max) | ESS/s | Mean RMSE (std.) | Variance RMSE (relative) | Movement | Acceptance | Divergences | Mean steps |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Isotropic Gaussian | endpoint | verified-reference | ⚠ 1.124 | 42.2 | 80.5 | 0.0106 | 0.2019 | 0.4591 | 0.3664 | 2860.4 | 0.171 | 0.156 | 1.000 | — | 0 | 10.0 |
| Isotropic Gaussian | endpoint | verified-optimized | ⚠ 1.124 | 42.2 | 80.5 | 0.0106 | 0.2019 | 0.4591 | 0.3664 | 14655.7 | 0.171 | 0.156 | 1.000 | — | 0 | 10.0 |
| Isotropic Gaussian | endpoint | advancedhmc | ⚠ 1.092 | 37.5 | 60.2 | 0.0188 | 0.2132 | 0.5017 | 0.6033 | 4892.5 | 0.187 | 0.159 | 1.000 | 0.994 | 0 | 10.0 |
| Isotropic Gaussian | multinomial | verified-reference | ⚠ 1.500 | 20.2 | 6.4 | 0.0050 | 0.2986 | 1.2174 | 0.9185 | 1028.1 | 0.392 | 0.368 | 0.919 | — | 0 | 10.0 |
| Isotropic Gaussian | multinomial | verified-optimized | ⚠ 1.500 | 20.2 | 6.4 | 0.0050 | 0.2986 | 1.2174 | 0.9185 | 3011.7 | 0.392 | 0.368 | 0.990 | — | 0 | 10.0 |
| Isotropic Gaussian | multinomial | advancedhmc | ⚠ 1.446 | 16.1 | 6.1 | 0.0081 | 0.2904 | 1.5113 | 1.1054 | 1527.0 | 0.388 | 0.375 | 0.869 | 0.998 | 0 | 10.0 |
| Isotropic Gaussian | nuts-complete | verified-reference | ⚠ 1.258 | 21.9 | 6.4 | 0.0034 | 0.2875 | 0.9922 | 0.6883 | 76.6 | 0.282 | 0.280 | 0.995 | — | 0 | 16.0 |
| Isotropic Gaussian | nuts-complete | verified-optimized | ⚠ 1.246 | 25.3 | 6.4 | 0.0040 | 0.2776 | 0.9019 | 0.6811 | 3254.3 | 0.261 | 0.270 | 0.995 | — | 0 | 16.0 |
| Isotropic Gaussian | nuts-complete | advancedhmc | ⚠ 1.409 | 20.4 | 7.3 | 0.0064 | 0.3175 | 1.0963 | 0.7118 | 1453.3 | 0.257 | 0.283 | 0.924 | 0.997 | 0 | 16.0 |
| Isotropic Gaussian | nuts-dynamic | verified-optimized | ⚠ 1.051 | 35.1 | 51.3 | 0.0059 | 0.2183 | 0.5505 | 0.6185 | 4929.2 | 0.209 | 0.182 | 1.000 | 0.997 | 0 | 15.0 |
| Isotropic Gaussian | nuts-dynamic | advancedhmc | ⚠ 1.171 | 31.3 | 25.1 | 0.0104 | 0.2513 | 0.7189 | 0.6113 | 2397.4 | 0.194 | 0.223 | 1.000 | 0.997 | 0 | 15.0 |
| Isotropic Gaussian | mala | verified-reference | ⚠ 2.923 | 17.5 | 4.9 | 0.0438 | 0.1171 | 0.9647 | 0.7409 | 1532.9 | 0.316 | 0.824 | 1.000 | — | 0 | 1.0 |
| Isotropic Gaussian | mala | verified-optimized | ⚠ 2.923 | 17.5 | 4.9 | 0.0438 | 0.1171 | 0.9647 | 0.7409 | 14258.7 | 0.316 | 0.824 | 1.000 | — | 0 | 1.0 |
| Isotropic Gaussian | gauss-legendre-2stage | verified-reference | ⚠ 1.124 | 42.2 | 80.5 | 0.0013 | 0.2018 | 0.4586 | 0.3661 | 104.1 | 0.171 | 0.156 | 1.000 | — | 0 | 10.0 |
| Isotropic Gaussian | gauss-legendre-2stage | verified-optimized | ⚠ 1.124 | 42.2 | 80.5 | 0.0013 | 0.2018 | 0.4586 | 0.3661 | 353.7 | 0.171 | 0.156 | 1.000 | — | 0 | 10.0 |
| Isotropic Gaussian | gauss-legendre-2stage-parallel | verified-optimized | ⚠ 1.124 | 42.2 | 80.5 | 0.0013 | 0.2018 | 0.4586 | 0.3661 | 97.3 | 0.171 | 0.156 | 1.000 | — | 0 | 10.0 |
| Isotropic Gaussian | gauss-legendre-2stage-simd | verified-optimized | ⚠ 1.124 | 42.2 | 80.5 | 0.0013 | 0.2018 | 0.4586 | 0.3661 | 3675.8 | 0.171 | 0.156 | 1.000 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | endpoint | verified-reference | ⚠ 1.134 | 37.7 | 72.3 | 0.0094 | 0.2306 | 0.6738 | 0.7015 | 1924.2 | 0.281 | 0.383 | 0.980 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | endpoint | verified-optimized | ⚠ 1.134 | 37.7 | 72.3 | 0.0094 | 0.2306 | 0.6738 | 0.7015 | 7589.3 | 0.281 | 0.383 | 0.980 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | endpoint | advancedhmc | ⚠ 1.362 | 21.7 | 8.0 | 0.0108 | 0.2516 | 0.7690 | 0.7364 | 2016.0 | 0.274 | 0.338 | 0.990 | 0.972 | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | multinomial | verified-reference | ⚠ 1.759 | 31.6 | 5.8 | 0.0079 | 0.1544 | 0.8381 | 0.8409 | 728.6 | 0.386 | 0.607 | 0.914 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | multinomial | verified-optimized | ⚠ 1.759 | 31.6 | 5.8 | 0.0079 | 0.1544 | 0.8381 | 0.8409 | 1995.3 | 0.386 | 0.607 | 0.990 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | multinomial | advancedhmc | ⚠ 1.201 | 19.8 | 14.6 | 0.0099 | 0.1703 | 0.8532 | 0.8703 | 1933.7 | 0.408 | 0.694 | 0.894 | 0.950 | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | nuts-complete | verified-reference | ⚠ 1.750 | 19.0 | 5.3 | 0.0030 | 0.2446 | 0.7900 | 0.9227 | 26.9 | 0.449 | 0.448 | 0.955 | — | 0 | 16.0 |
| Correlated Gaussian (ρ=0.9) | nuts-complete | verified-optimized | ⚠ 1.740 | 31.6 | 7.6 | 0.0049 | 0.2087 | 0.7386 | 0.9327 | 1151.4 | 0.442 | 0.451 | 0.995 | — | 0 | 16.0 |
| Correlated Gaussian (ρ=0.9) | nuts-complete | advancedhmc | ⚠ 1.188 | 22.0 | 9.0 | 0.0069 | 0.2161 | 0.7883 | 0.9091 | 1578.8 | 0.423 | 0.568 | 0.929 | 0.954 | 0 | 16.0 |
| Correlated Gaussian (ρ=0.9) | nuts-dynamic | verified-optimized | ⚠ 1.347 | 27.1 | 31.3 | 0.0045 | 0.1956 | 0.7127 | 1.1634 | 1001.1 | 0.563 | 0.396 | 1.000 | 0.941 | 0 | 15.0 |
| Correlated Gaussian (ρ=0.9) | nuts-dynamic | advancedhmc | ⚠ 1.517 | 21.2 | 6.4 | 0.0071 | 0.1980 | 0.7912 | 1.0486 | 1385.8 | 0.508 | 0.424 | 1.000 | 0.945 | 0 | 15.0 |
| Correlated Gaussian (ρ=0.9) | mala | verified-reference | ⚠ 2.942 | 14.6 | 4.9 | 0.0366 | 0.0965 | 0.9832 | 0.5068 | 1519.2 | 0.200 | 0.904 | 0.980 | — | 0 | 1.0 |
| Correlated Gaussian (ρ=0.9) | mala | verified-optimized | ⚠ 2.942 | 14.6 | 4.9 | 0.0366 | 0.0965 | 0.9832 | 0.5068 | 11322.2 | 0.200 | 0.904 | 0.980 | — | 0 | 1.0 |
| Correlated Gaussian (ρ=0.9) | gauss-legendre-2stage | verified-reference | ⚠ 1.125 | 40.6 | 82.7 | 0.0013 | 0.2407 | 0.6494 | 0.7089 | 78.3 | 0.267 | 0.381 | 1.000 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | gauss-legendre-2stage | verified-optimized | ⚠ 1.125 | 40.6 | 82.7 | 0.0013 | 0.2407 | 0.6494 | 0.7089 | 225.1 | 0.267 | 0.381 | 1.000 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | gauss-legendre-2stage-parallel | verified-optimized | ⚠ 1.125 | 40.6 | 82.7 | 0.0013 | 0.2407 | 0.6494 | 0.7089 | 78.0 | 0.267 | 0.381 | 1.000 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | gauss-legendre-2stage-simd | verified-optimized | ⚠ 1.125 | 40.6 | 82.7 | 0.0013 | 0.2407 | 0.6494 | 0.7089 | 1627.9 | 0.267 | 0.381 | 1.000 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | endpoint-dense | verified-reference | ⚠ 1.052 | 36.4 | 58.0 | 0.0091 | 0.2063 | 0.5264 | 0.3708 | 604.9 | 0.122 | 0.150 | 1.000 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | endpoint-dense | verified-optimized | ⚠ 1.052 | 36.4 | 58.0 | 0.0165 | 0.2063 | 0.5264 | 0.3708 | 2587.4 | 0.122 | 0.150 | 1.000 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | endpoint-dense | advancedhmc | ⚠ 1.108 | 39.0 | 63.6 | 0.0195 | 0.1997 | 0.6104 | 0.3478 | 1040.8 | 0.153 | 0.189 | 1.000 | 0.994 | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | multinomial-dense | verified-reference | ⚠ 1.597 | 24.6 | 7.0 | 0.0061 | 0.2590 | 0.8877 | 1.0230 | 61.9 | 0.444 | 0.338 | 0.919 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | multinomial-dense | verified-optimized | ⚠ 1.597 | 24.6 | 7.0 | 0.0112 | 0.2590 | 0.8877 | 1.0230 | 330.3 | 0.444 | 0.338 | 0.919 | — | 0 | 10.0 |
| Correlated Gaussian (ρ=0.9) | multinomial-dense | advancedhmc | ⚠ 1.218 | 16.6 | 29.1 | 0.0083 | 0.2459 | 0.7590 | 1.0755 | 694.5 | 0.375 | 0.439 | 0.869 | 0.998 | 0 | 10.0 |
| Product quartic | endpoint | verified-reference | ⚠ 1.035 | 81.0 | 122.4 | 0.0202 | 0.1014 | — | 0.2329 | 5981.3 | 0.110 | 0.084 | 1.000 | — | 0 | 10.0 |
| Product quartic | endpoint | verified-optimized | ⚠ 1.035 | 81.0 | 122.4 | 0.0202 | 0.1014 | — | 0.2329 | 22527.8 | 0.110 | 0.084 | 1.000 | — | 0 | 10.0 |
| Product quartic | endpoint | advancedhmc | ⚠ 1.047 | 73.8 | 123.2 | 0.0369 | 0.1042 | — | 0.2725 | 15250.7 | 0.122 | 0.085 | 0.990 | 0.986 | 0 | 10.0 |
| Product quartic | multinomial | verified-reference | ⚠ 1.303 | 24.4 | 10.6 | 0.0061 | 0.1854 | — | 0.5951 | 996.8 | 0.288 | 0.221 | 0.924 | — | 0 | 10.0 |
| Product quartic | multinomial | verified-optimized | ⚠ 1.303 | 24.4 | 10.6 | 0.0061 | 0.1854 | — | 0.5951 | 2407.4 | 0.288 | 0.221 | 0.990 | — | 0 | 10.0 |
| Product quartic | multinomial | advancedhmc | ⚠ 1.434 | 20.2 | 8.4 | 0.0101 | 0.1967 | — | 0.5990 | 1500.4 | 0.272 | 0.236 | 0.859 | 0.990 | 0 | 10.0 |
| Product quartic | nuts-complete | verified-reference | ⚠ 1.243 | 30.4 | 22.0 | 0.0047 | 0.1479 | — | 0.3992 | 103.6 | 0.188 | 0.162 | 0.980 | — | 0 | 16.0 |
| Product quartic | nuts-complete | verified-optimized | ⚠ 1.231 | 41.2 | 60.1 | 0.0064 | 0.1425 | — | 0.4199 | 2627.1 | 0.179 | 0.159 | 0.995 | — | 0 | 16.0 |
| Product quartic | nuts-complete | advancedhmc | ⚠ 1.254 | 26.8 | 8.9 | 0.0084 | 0.1598 | — | 0.3902 | 1929.4 | 0.176 | 0.154 | 0.934 | 0.989 | 0 | 16.0 |
| Product quartic | nuts-dynamic | verified-optimized | ⚠ 1.040 | 58.1 | 90.0 | 0.0097 | 0.1206 | — | 0.3449 | 8751.9 | 0.146 | 0.095 | 1.000 | 0.987 | 0 | 15.0 |
| Product quartic | nuts-dynamic | advancedhmc | ⚠ 1.057 | 56.0 | 78.2 | 0.0187 | 0.1171 | — | 0.3431 | 3655.6 | 0.133 | 0.117 | 1.000 | 0.987 | 0 | 15.0 |
| Product quartic | mala | verified-reference | ⚠ 2.921 | 17.6 | 4.9 | 0.0440 | 0.1132 | — | 0.7125 | 1405.6 | 0.431 | 0.689 | 1.000 | — | 0 | 1.0 |
| Product quartic | mala | verified-optimized | ⚠ 2.921 | 17.6 | 4.9 | 0.0440 | 0.1132 | — | 0.7125 | 7327.8 | 0.431 | 0.689 | 1.000 | — | 0 | 1.0 |
| Product quartic | gauss-legendre-2stage | verified-reference | ⚠ 1.035 | 75.2 | 122.4 | 0.0023 | 0.1015 | — | 0.2337 | 234.0 | 0.110 | 0.084 | 1.000 | — | 0 | 10.0 |
| Product quartic | gauss-legendre-2stage | verified-optimized | ⚠ 1.035 | 75.2 | 122.4 | 0.0023 | 0.1015 | — | 0.2337 | 657.9 | 0.110 | 0.084 | 1.000 | — | 0 | 10.0 |
| Product quartic | gauss-legendre-2stage-parallel | verified-optimized | ⚠ 1.035 | 75.2 | 122.4 | 0.0023 | 0.1015 | — | 0.2337 | 235.6 | 0.110 | 0.084 | 1.000 | — | 0 | 10.0 |
| Product quartic | gauss-legendre-2stage-simd | verified-optimized | ⚠ 1.035 | 75.2 | 122.4 | 0.0023 | 0.1015 | — | 0.2337 | 4300.7 | 0.110 | 0.084 | 1.000 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | endpoint | verified-reference | ⚠ 1.022 | 46.2 | 132.0 | 0.0115 | 0.9536 | 93.8893 | 7.2268 | 5424.1 | 0.285 | 0.441 | 0.904 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | endpoint | verified-optimized | ⚠ 1.022 | 46.2 | 132.0 | 0.0115 | 0.9536 | 93.8893 | 7.2268 | 22544.1 | 0.285 | 0.441 | 0.904 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | endpoint | advancedhmc | ⚠ 1.013 | 49.5 | 72.4 | 0.0248 | 1.6409 | 90.9985 | 4.2812 | 11814.3 | 0.275 | 0.415 | 0.884 | 0.856 | 0 | 10.0 |
| Ill-conditioned Gaussian | multinomial | verified-reference | ⚠ 1.028 | 144.0 | 105.1 | 0.0360 | 0.4932 | 97.0077 | 3.1443 | 14257.3 | 0.342 | 0.548 | 0.924 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | multinomial | verified-optimized | ⚠ 1.028 | 144.0 | 105.1 | 0.0360 | 0.4932 | 97.0077 | 3.1443 | 39263.3 | 0.342 | 0.548 | 0.985 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | multinomial | advancedhmc | ⚠ 1.043 | 120.5 | 96.9 | 0.0602 | 0.5547 | 93.3144 | 3.1007 | 22231.0 | 0.259 | 0.543 | 0.879 | 0.894 | 0 | 10.0 |
| Ill-conditioned Gaussian | nuts-complete | verified-reference | ⚠ 1.012 | 130.7 | 68.5 | 0.0204 | 0.6779 | 91.8495 | 4.0711 | 1109.8 | 0.327 | 0.470 | 0.995 | — | 0 | 16.0 |
| Ill-conditioned Gaussian | nuts-complete | verified-optimized | ⚠ 1.039 | 139.5 | 65.4 | 0.0218 | 0.7144 | 89.1793 | 4.2056 | 22138.6 | 0.327 | 0.453 | 0.995 | — | 0 | 16.0 |
| Ill-conditioned Gaussian | nuts-complete | advancedhmc | ⚠ 1.017 | 145.4 | 71.0 | 0.0454 | 0.8448 | 86.5424 | 4.8885 | 20203.9 | 0.296 | 0.454 | 0.929 | 0.888 | 0 | 16.0 |
| Ill-conditioned Gaussian | nuts-dynamic | verified-optimized | ⚠ 1.042 | 151.5 | 109.8 | 0.0252 | 0.7361 | 94.6689 | 5.1605 | 22868.9 | 0.308 | 0.433 | 1.000 | 0.872 | 0 | 15.0 |
| Ill-conditioned Gaussian | nuts-dynamic | advancedhmc | 1.004 | 146.9 | 118.5 | 0.0490 | 0.8566 | 88.9917 | 6.1029 | 21317.4 | 0.257 | 0.428 | 1.000 | 0.864 | 0 | 15.0 |
| Ill-conditioned Gaussian | mala | verified-reference | ⚠ 1.121 | 37.5 | 34.7 | 0.0939 | 0.1166 | 99.8837 | 0.8810 | 6851.7 | 0.297 | 0.771 | 0.914 | — | 0 | 1.0 |
| Ill-conditioned Gaussian | mala | verified-optimized | ⚠ 1.121 | 37.5 | 34.7 | 0.0939 | 0.1166 | 99.8837 | 0.8810 | 46187.5 | 0.297 | 0.771 | 0.914 | — | 0 | 1.0 |
| Ill-conditioned Gaussian | gauss-legendre-2stage | verified-reference | ⚠ 1.044 | 36.1 | 105.0 | 0.0011 | 0.9949 | 92.9845 | 7.2413 | 147.4 | 0.255 | 0.431 | 1.000 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | gauss-legendre-2stage | verified-optimized | ⚠ 1.044 | 36.1 | 105.0 | 0.0011 | 0.9949 | 92.9845 | 7.2413 | 416.3 | 0.255 | 0.431 | 1.000 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | gauss-legendre-2stage-parallel | verified-optimized | ⚠ 1.044 | 36.1 | 105.0 | 0.0011 | 0.9949 | 92.9845 | 7.2413 | 152.0 | 0.255 | 0.431 | 1.000 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | gauss-legendre-2stage-simd | verified-optimized | ⚠ 1.044 | 36.1 | 105.0 | 0.0011 | 0.9949 | 92.9845 | 7.2413 | 2978.6 | 0.255 | 0.431 | 1.000 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | endpoint-diagonal | verified-reference | ⚠ 1.124 | 42.2 | 80.5 | 0.0106 | 1.7537 | 20.5116 | 2.2073 | 5110.8 | 0.171 | 0.156 | 1.000 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | endpoint-diagonal | verified-optimized | ⚠ 1.124 | 42.2 | 80.5 | 0.0192 | 1.7537 | 20.5116 | 2.2073 | 19847.4 | 0.171 | 0.156 | 1.000 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | endpoint-diagonal | advancedhmc | ⚠ 1.092 | 37.5 | 60.2 | 0.0188 | 1.4913 | 28.1559 | 5.2305 | 3944.7 | 0.187 | 0.159 | 1.000 | 0.994 | 0 | 10.0 |
| Ill-conditioned Gaussian | multinomial-diagonal | verified-reference | ⚠ 1.500 | 20.2 | 6.4 | 0.0050 | 1.8036 | 45.3472 | 5.4250 | 538.8 | 0.392 | 0.368 | 0.919 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | multinomial-diagonal | verified-optimized | ⚠ 1.500 | 20.2 | 6.4 | 0.0092 | 1.8036 | 45.3472 | 5.4250 | 4775.4 | 0.392 | 0.368 | 0.919 | — | 0 | 10.0 |
| Ill-conditioned Gaussian | multinomial-diagonal | advancedhmc | ⚠ 1.446 | 16.1 | 6.1 | 0.0081 | 1.8154 | 59.6080 | 7.2162 | 1241.4 | 0.388 | 0.375 | 0.869 | 0.998 | 0 | 10.0 |
| Regularized logistic | endpoint | verified-reference | ⚠ 1.077 | 58.6 | 49.5 | 0.0147 | 0.1475 | — | 0.2814 | 1992.9 | 0.140 | 0.137 | 1.000 | — | 0 | 10.0 |
| Regularized logistic | endpoint | verified-optimized | ⚠ 1.077 | 58.6 | 49.5 | 0.0147 | 0.1475 | — | 0.2814 | 5725.6 | 0.140 | 0.137 | 1.000 | — | 0 | 10.0 |
| Regularized logistic | endpoint | advancedhmc | ⚠ 1.061 | 46.8 | 88.5 | 0.0234 | 0.1573 | — | 0.4048 | 6004.4 | 0.156 | 0.140 | 0.990 | 0.991 | 0 | 10.0 |
| Regularized logistic | multinomial | verified-reference | ⚠ 1.359 | 23.2 | 6.4 | 0.0058 | 0.2493 | — | 0.6515 | 441.2 | 0.338 | 0.329 | 0.919 | — | 0 | 10.0 |
| Regularized logistic | multinomial | verified-optimized | ⚠ 1.359 | 23.2 | 6.4 | 0.0058 | 0.2493 | — | 0.6515 | 956.4 | 0.338 | 0.329 | 0.990 | — | 0 | 10.0 |
| Regularized logistic | multinomial | advancedhmc | ⚠ 1.430 | 17.3 | 8.1 | 0.0086 | 0.2563 | — | 0.7618 | 878.9 | 0.332 | 0.347 | 0.864 | 0.996 | 0 | 10.0 |
| Regularized logistic | nuts-complete | verified-reference | ⚠ 1.222 | 28.2 | 13.1 | 0.0044 | 0.2153 | — | 0.5786 | 88.8 | 0.235 | 0.257 | 0.995 | — | 0 | 16.0 |
| Regularized logistic | nuts-complete | verified-optimized | ⚠ 1.210 | 33.3 | 13.1 | 0.0052 | 0.2053 | — | 0.5202 | 918.3 | 0.218 | 0.245 | 0.995 | — | 0 | 16.0 |
| Regularized logistic | nuts-complete | advancedhmc | ⚠ 1.325 | 23.2 | 7.3 | 0.0073 | 0.2478 | — | 0.4871 | 963.7 | 0.215 | 0.255 | 0.924 | 0.995 | 0 | 16.0 |
| Regularized logistic | nuts-dynamic | verified-optimized | ⚠ 1.031 | 44.8 | 74.6 | 0.0075 | 0.1640 | — | 0.4483 | 3254.0 | 0.173 | 0.161 | 1.000 | 0.995 | 0 | 15.0 |
| Regularized logistic | nuts-dynamic | advancedhmc | ⚠ 1.102 | 39.0 | 33.3 | 0.0130 | 0.2073 | — | 0.4041 | 1670.7 | 0.163 | 0.207 | 1.000 | 0.995 | 0 | 15.0 |
| Regularized logistic | mala | verified-reference | ⚠ 2.916 | 17.6 | 4.9 | 0.0439 | 0.1140 | — | 0.7161 | 1148.9 | 0.359 | 0.773 | 1.000 | — | 0 | 1.0 |
| Regularized logistic | mala | verified-optimized | ⚠ 2.916 | 17.6 | 4.9 | 0.0439 | 0.1140 | — | 0.7161 | 3923.4 | 0.359 | 0.773 | 1.000 | — | 0 | 1.0 |
| Regularized logistic | gauss-legendre-2stage | verified-reference | ⚠ 1.077 | 58.6 | 49.5 | 0.0018 | 0.1473 | — | 0.2811 | 104.9 | 0.140 | 0.137 | 1.000 | — | 0 | 10.0 |
| Regularized logistic | gauss-legendre-2stage | verified-optimized | ⚠ 1.077 | 58.6 | 49.5 | 0.0018 | 0.1473 | — | 0.2811 | 272.8 | 0.140 | 0.137 | 1.000 | — | 0 | 10.0 |
| Regularized logistic | gauss-legendre-2stage-parallel | verified-optimized | ⚠ 1.077 | 58.6 | 49.5 | 0.0018 | 0.1473 | — | 0.2811 | 124.6 | 0.140 | 0.137 | 1.000 | — | 0 | 10.0 |
| Regularized logistic | gauss-legendre-2stage-simd | verified-optimized | ⚠ 1.077 | 58.6 | 49.5 | 0.0018 | 0.1473 | — | 0.2811 | 884.7 | 0.140 | 0.137 | 1.000 | — | 0 | 10.0 |

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

- **Position-dependent Gaussian:** standard-normal target with `G(q)=diag(2+sin(qᵢ))`; this activates generic dense RMHMC metric derivatives and implicit solves.

## Reproduce

```sh
make benchmark-hmc
make benchmark-rmhmc
make benchmark-report
```

Aggregate measurements are committed at [`benchmark/results/latest.csv`](https://github.com/xukai92/mcmc-lean/blob/main/benchmark/results/latest.csv), with every timing repetition in [`benchmark/results/timings.csv`](https://github.com/xukai92/mcmc-lean/blob/main/benchmark/results/timings.csv) and sampling diagnostics in [`benchmark/results/quality.csv`](https://github.com/xukai92/mcmc-lean/blob/main/benchmark/results/quality.csv).
