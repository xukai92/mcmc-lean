# Pre-registered analysis plan

This plan is frozen before confirmatory runs begin. Changes after the first
confirmatory run require explicit justification and are reported as deviations.

## Primary outcome

**Success rate** per condition x task. Binary: all evaluator gates pass (1) or
any gate fails (0).

### Formalize success criteria
All of:
1. `lake build` succeeds (0 errors)
2. `make check-generated` passes (IR matches Lean source)
3. Proof hygiene: 0 sorry, 0 admit, 0 axiom in new .lean files
4. Expected theorem names appear as compiled declarations
5. Expert review: formal specification matches intended algorithm (blinded)

### Optimize success criteria
All of:
1. Conformance gate passes (bit-exact or numerical per declared tier)
2. `make julia` passes (full Julia test suite)
3. Benchmark: speedup >= declared threshold (default 1.0x, no regression)
4. Statistical equivalence: sample moments within expected range
5. Scope check: only allowed files modified, Reference untouched

## Secondary outcomes

| Metric | Unit | Collected from |
|--------|------|----------------|
| Wall time | seconds | manifest.json timestamp delta |
| Model tokens | count | agent session transcript |
| Tool calls | count | agent session transcript |
| Builder retries | count | RELOOP count in manifest |
| Human interventions | count | human gate log |

### Optimize-specific
| Metric | Unit | How measured |
|--------|------|-------------|
| Throughput | transitions/s | @elapsed benchmark, median of 5+ seeds |
| Allocation | bytes/step | @allocated, single step after warmup |
| Sampling quality | ESS, Rhat | 10K-draw chain on standard Gaussian |

### Formalize-specific
| Metric | Unit | How measured |
|--------|------|-------------|
| Lean lines added | count | git diff --stat on .lean files |
| Theorems proved | count | grep "theorem" in new .lean files |
| Sorry count | count | must be 0 (gate enforced) |
| IR version bump | boolean | IRFormat.lean version changed |

## Statistical analysis

### Paired comparison (primary)
For each agent (Claude, Codex), compare factory vs direct:
- **McNemar's exact test** on the 2x2 success/failure table
- Report exact p-value and odds ratio with 95% CI
- Significance threshold: alpha = 0.05 (two-sided)

### Continuous metrics
- **Wilcoxon signed-rank test** for paired continuous outcomes (wall time,
  tokens) within agent
- Report median difference with 95% CI via Hodges-Lehmann estimator

### Reporting
- Per-task outcomes reported individually (not just aggregates)
- Bootstrap 95% CIs (10,000 resamples) for aggregate success rates
- Effect sizes reported alongside p-values
- All failed runs reported with failure mode classification

## Failure classification

Each failed run is classified by defect type:
1. **Specification error**: wrong mathematical statement
2. **Proof gap**: correct statement but sorry/admit used
3. **IR mismatch**: IR program doesn't match kernel theory
4. **Conformance failure**: Optimized doesn't match Reference
5. **Regression**: optimization made performance worse
6. **Scope violation**: modified forbidden files
7. **Timeout**: exceeded wall time cap
8. **Infrastructure**: tool/environment failure (not agent's fault)

## Pre-registration commitment

This analysis plan is committed to the repository before any confirmatory run.
The commit hash of this file serves as the pre-registration timestamp.
Deviations from this plan are permitted but must be:
1. Documented with justification
2. Reported alongside the pre-registered analysis
3. Clearly labeled as exploratory
