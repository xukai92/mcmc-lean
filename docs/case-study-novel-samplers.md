# Case study: building two novel MCMC samplers

This case study documents the development of Active-Sketch sMMALA and
Shared-Momentum Multinomial HMC using the verified-samplers harness. Both
algorithms were formalized in Lean 4, compiled to IR programs, and
implemented as executable Julia samplers within a single 24-hour period
(2026-09-23 to 2026-09-24). The document records what happened, what the
harness caught, and what it cannot catch.

## Build method

Each sampler was developed in a separate factory CEO session launched via
`factory tmux --engine tool --focus` with an algorithm-specific directive.
Each session ran the `formalize.py` workflow DAG internally (25 nodes, 34
edges), which orchestrates parallel research, strategy, two-phase building,
and parallel QA (code review, adversarial testing, health check). The two
sessions ran concurrently — their kernel theory commits are 51 minutes apart.

The human authored algorithm specifications, launched the factory sessions,
merged results to main, and resolved conflicts between the parallel branches.
The benchmark phase involved additional factory sessions. This was not a
push-button process: the human made judgment calls about merge ordering,
benchmark design, and which QA findings required remediation.

## Active-Sketch sMMALA

Active-Sketch simplified manifold MALA uses a sketched position-dependent
metric `G(x) = S(x)^T S(x) + λI`, where `S(x)` is an `M × d` sketch matrix.
This eliminates the `O(d⁴)` metric-derivative divergence computation required
by dense PMALA, reducing per-step cost to `O(Md² + d³)`.

### Development timeline

| Stage | Commit | Timestamp (UTC) | Elapsed | Files | Insertions/Deletions | Description |
|-------|--------|-----------------|---------|-------|----------------------|-------------|
| Kernel theory | `1b27257` | 2026-09-23 04:55:46 | +0h 00m | 3 | +229 | Lean formalization of sketched metric and simplified drift |
| IR program | `5794440` | 2026-09-23 14:40:09 | +9h 44m | 4 | +20/−3 | IR emission wired into IRFormat |
| E2E pipeline | `48de407` | 2026-09-23 21:02:19 | +16h 07m | 11 | +614/−23 | Refinement theorem, Reference, Optimized, conformance tests, public API |
| Test fix | `404db1a` | 2026-09-23 21:49:38 | +16h 54m | 1 | +2/−1 | Add to 27-program list in unit tests |
| Shared benchmark | `e8e0e19` | 2026-09-24 01:55:57 | +21h 00m | 9 | +1146/−4 | Initial combined benchmark for both samplers |
| Benchmark rewrite | `b890ca9` | 2026-09-24 03:31:31 | +22h 36m | 3 | +564/−469 | Focused paper-quality Active-Sketch benchmark |
| Dev-mode results | `bcca3f3` | 2026-09-24 04:17:58 | +23h 22m | 4 | +106 | Development-mode benchmark outputs |

**Total wall-clock time:** ~23 hours 22 minutes (first commit to last).

### Narrative

The development proceeded in three phases: kernel theory (Lean formalization),
IR pipeline (emission, refinement theorem, Julia implementations), and
benchmarking (three iterations).

The kernel theory in `ActiveSketchSMMALA.lean` proved that the sketched metric
specializes the existing dense PMALA infrastructure. The refinement theorem
`activeSketchSmMalaProgramKernel_refines` establishes kernel equality by
delegating to the dense PMALA proof — no `sorry`, `admit`, or `axiom`. The
companion `activeSketchSmMalaProgramKernel_invariant` proves target invariance.

The E2E pipeline commit (`48de407`) was the largest, touching 11 files across
Lean, Julia Reference, Optimized, tests, and documentation. The Optimized
implementation uses `ActiveSketchSMMALAWorkspace{T}` with preallocated buffers
for zero steady-state allocation and generic `T<:AbstractFloat` typing. Three
conformance test cases exercise asymmetric sketch (`M < d`), square sketch
(`M = d`, degenerating toward dense PMALA), and zero sketch (`λI` metric).

No QA rejections occurred during the core development. The test fix at
`404db1a` was a minor omission — adding the new program to the 27-program
enumeration in unit tests.

The benchmark phase required three iterations: an initial shared benchmark
covering both samplers (`e8e0e19`), a focused rewrite as a paper-quality
Active-Sketch benchmark (`b890ca9`), and the development-mode result
generation (`bcca3f3`). The benchmark includes 5 targets (isotropic Gaussian,
correlated Gaussian, ill-conditioned Gaussian, regularized logistic, Neal's
funnel), 3 baselines (MALA, multinomial HMC, dense PMALA), and a sketch-rank
sweep over `M ∈ {5, 10, 20}`.

**Deferred:** Full statistical evaluation at `d=50` and `d=100` remains
pending. The development-mode results use `d=10` with shortened chains.

## Shared-Momentum Multinomial HMC

Shared-Momentum Multinomial HMC couples `K` chains by drawing one shared momentum
vector and running independent multinomial HMC transitions per chain. The
construction is a valid coupling: each coordinate marginal equals single-chain
`positionMultinomialHMC`, while shared momentum creates inter-chain correlation
by design. Product invariance does not hold.

### Development timeline

| Stage | Commit | Timestamp (UTC) | Elapsed | Files | Insertions/Deletions | Description |
|-------|--------|-----------------|---------|-------|----------------------|-------------|
| Kernel theory | `f544cfc` | 2026-09-23 05:46:14 | +0h 00m | 3 | +342 | Lean formalization of K-chain shared-momentum kernel |
| IR program | `3f46494` | 2026-09-23 14:38:22 | +8h 52m | 4 | +38/−1 | CompilerIR program for shared-momentum multinomial |
| Marginal theorem | `cf8d54a` | 2026-09-23 20:41:17 | +14h 55m | 4 | +185/−32 | Prove each marginal equals positionMultinomialHMC; IR refinement |
| Julia implementation | `fc9a601` | 2026-09-23 20:53:42 | +15h 07m | 4 | +308/−2 | Reference, Optimized, conformance tests |
| Evaluation module | `9674bf9` | 2026-09-23 20:58:10 | +15h 12m | 3 | +180 | SharedMomentumEval with variance reduction and meeting times |
| QA fix 1 | `98f2598` | 2026-09-23 21:22:13 | +15h 36m | 2 | +12/−4 | Gradient sign convention and workspace validation |
| Paper benchmark | `bb521c8` | 2026-09-24 03:31:01 | +21h 45m | 4 | +1087/−1 | Three-arm comparison with conformance gates |
| QA fix 2 | `8774cb0` | 2026-09-24 03:47:36 | +22h 01m | 1 | +22/−91 | Fix 7 issues in benchmark |
| Coupling diagnostic | `e7dee02` | 2026-09-24 04:01:47 | +22h 16m | 6 | +463/−37 | Replace meeting-time with coupling-quality diagnostic |

**Total wall-clock time:** ~22 hours 16 minutes (first commit to last).

### Narrative

The development had two distinct tempos. The initial Lean formalization
(kernel theory + IR program + marginal theorem) spanned ~15 hours, with a
~6-hour gap between the IR program (`3f46494`, 14:38 UTC) and the marginal
theorem (`cf8d54a`, 20:41 UTC). This gap is notably longer than any other
inter-commit interval in either sampler's timeline, suggesting the marginal
theorem required sustained proving effort. The theorem
`sharedMomentumMultinomialHMC_marginal` establishes that each coordinate marginal
of the K-chain kernel equals the single-chain `positionMultinomialHMC`, with
auxiliary lemmas for `positionProjectK_eval`, `sharedMomentumLiftK_map_eval`,
and `comp_sharedLift_map_eval`. A K=2 specialization demonstrates both
marginals explicitly.

Once the theorem landed, the Julia implementation and evaluation module
followed rapidly — three commits in 17 minutes (`cf8d54a` → `fc9a601` →
`9674bf9`). The Optimized implementation uses
`SharedMomentumMultinomialHMCWorkspace{T<:AbstractFloat}` with preallocated
buffers. Conformance tests verify Reference == Optimized for `K=2` (`dim=2`)
and `K=3` (`dim=1`), plus Float32 and workspace reuse.

This rapid phase was followed by two QA cycles that caught 9 bugs total.

**QA cycle 1** (`98f2598`): The QA agents flagged two issues in the evaluation
module:

1. **Gradient sign convention.** The `SharedMomentumEval.evaluate` function
   accepted a parameter named `gradient`, but the sampler expects ∇U (the
   potential gradient, where `U = −log π`), not ∇log π. Passing ∇log π caused
   divergent leapfrog integration and frozen chains. The fix renamed the
   parameter to `potential_gradient` and added documentation making the
   convention explicit.

2. **Workspace buffer validation.** The workspace-based
   `shared_momentum_multinomial_hmc_step!` did not validate that the `steps`
   parameter fit within the preallocated `positions` and `logweights` buffers.
   The fix added a dimension check that throws `DimensionMismatch` when
   `steps` exceeds the workspace allocation.

**QA cycle 2** (`8774cb0`): A second QA pass on the benchmark code caught 7
more issues:

1. **Neal's funnel gradient sign error.** The `∂U/∂v` accumulator had
   `+= (q[i]² / (2 exp(v)) − 0.5)` where the correct sign is `−=`. This
   affected both dev and full benchmark targets. The sign error would produce
   incorrect potential gradients, biasing the funnel chains.

2. **Pooled variance reduction metric.** The original code computed
   `var(bulk_ess)` as a variance reduction proxy, which is not meaningful.
   The fix computes VR from x₁ sample mean variance across chains and
   replicates, adding a `mean_x1` column for this computation.

3. **Meeting time tolerance.** The tolerance for detecting chain meetings was
   `1e-12`, which is unrealistic for continuous-state HMC. Relaxed to `1e-6`.

4. **Operator precedence bug.** A missing parenthesization around an OR
   condition before `&& continue` caused only one emptiness check to gate the
   continue statement.

5. **Unused parameters.** `compute_acceptance_rate` carried dead `d` and `K`
   parameters.

6. **Dead code.** A multi-chain `compute_diagnostics` function was never
   called.

7. **Duplicate function.** `_crn_multinomial_select!` was identical to
   `_shared_momentum_multinomial_step!`. Removed the duplicate and updated the
   call site.

The IR refinement theorem `sharedMomentumMultinomialHmcProgramKernel_refines`
closed the last open IR program, bringing the count to 27/27 programs with
refinement theorems (15 modeled-kernel, 5 replay-spec, 7 conditional on
solver certificate, 0 open).

## Comparison

| Metric | Active-Sketch sMMALA | Shared-Momentum Multinomial HMC |
|--------|----------------------|------------------------------|
| Wall-clock time (first to last commit) | ~23h 22m | ~22h 16m |
| Commits | 7 | 9 |
| QA rejections | 0 | 2 cycles, 9 bugs |
| Lean files changed (core) | 4 | 5 |
| Lean insertions (core, commits 1–3) | +249 | +380 |
| Julia insertions (core, E2E commit) | +614 (11 files) | +488 (7 files across 2 commits) |
| Benchmark insertions | +1816 (3 commits) | +1572 (3 commits) |
| Refinement strength | Modeled-kernel | Modeled-kernel + marginal corollary |
| Factory sessions | ≥2 (core + benchmark) | ≥2 (core + benchmark) |
| Deferred items | Full-scale eval (d=50/100) | Full-scale eval, production benchmark |

Both samplers achieved modeled-kernel refinement — the strongest category,
proving `ProgramKernel = Kernel` equality. Shared-Momentum Multinomial additionally proved
its marginal corollary, which has no analogue for Active-Sketch (a single-chain
sampler). Active-Sketch's proof strategy was simpler: specialize the existing
dense PMALA infrastructure with the sketch metric `G(x) = S(x)^T S(x) + λI`.
Shared-Momentum Multinomial required novel auxiliary lemmas for the product-space
projection and shared-momentum lift.

## What harness-enabled development means

The verified-samplers harness provides several layers of automated checking.
Each layer has specific capabilities and specific blind spots.

**Lean compiler.** Type-checks all proofs. Prevents `sorry`, `admit`, and
`axiom` from appearing in committed code (enforced by CLAUDE.md convention and
CI). This guarantees that stated theorems follow from their hypotheses under
Lean's type theory. It does not guarantee that the hypotheses are satisfiable,
that the theorems are useful, or that they correspond to the intended
mathematical statement.

**IR compiler.** Translates verified kernel definitions to executable IR
programs via `make generate`. The refinement theorems
(`activeSketchSmMalaProgramKernel_refines`,
`sharedMomentumMultinomialHmcProgramKernel_refines`) prove that the IR program's
assembled kernel equals the mathematical kernel. This is a Lean theorem about
the IR semantics, not about Julia's floating-point execution of that IR.

**Conformance framework.** Tests numerical equivalence between the IR-backed
Reference interpreter and the independently maintained Optimized Julia
implementation. Active-Sketch tested three cases (asymmetric, square, zero
sketch). Shared-Momentum Multinomial tested `K=2`/`K=3` configurations, Float32 typing, and
workspace reuse. Conformance catches implementation divergence between paths;
it does not prove that either path is correct.

**QA agents.** Automated code review, adversarial testing, and health checking
run as part of the factory workflow DAG. In this case study they caught:
- Gradient sign convention error (potential gradient vs. log-density gradient)
- Workspace buffer bounds validation gap
- Neal's funnel gradient sign error in benchmark code
- A pooled variance reduction metric that computed the wrong quantity
- Unrealistic tolerance, operator precedence, dead code, and duplication

These are real bugs. The gradient sign convention error (`98f2598`) would have
produced divergent leapfrog trajectories. The funnel gradient sign error
(`8774cb0`) would have biased benchmark results for one of the three targets.

**What these layers cannot catch:**
- Algorithmic design quality — whether the sketch metric is a good
  approximation for a given target class
- Statistical efficiency — whether the sampler mixes well enough to be
  competitive with alternatives
- Mathematical novelty — whether the construction is original
- Hypothesis satisfiability — whether the Lean theorem's preconditions hold
  in practice for targets of interest
- Floating-point faithfulness — the refinement theorem operates at the level
  of Lean's exact-real semantics, not Julia's IEEE 754 arithmetic

The harness verifies the properties it was designed to check. The gap between
"type-checks" and "works well on real problems" is filled by benchmarking,
statistical evaluation, and human judgment — none of which are automated by
the current pipeline.

## Human role

The human performed the following tasks during this development:

- **Algorithm specification.** Authored the mathematical descriptions and
  design decisions for both samplers before launching factory sessions.
- **Session management.** Launched concurrent factory CEO sessions, monitored
  progress, and decided when to merge.
- **Branch integration.** Merged the two parallel development branches to
  main, resolving conflicts in shared files (IR refinement tracker, development
  log, unit test lists).
- **Test list reconciliation.** Fixed the 27-program enumeration discrepancy
  when the Active-Sketch branch didn't know about the Shared-Momentum Multinomial branch's
  additions.
- **Benchmark design.** Specified the target distributions, baseline samplers,
  and evaluation metrics for the paper-quality benchmarks.
- **QA triage.** Reviewed QA agent findings and decided which required fixes
  and which were acceptable.
- **Statistical interpretation.** Assessed whether development-mode benchmark
  results were sufficient or required full-scale runs (deferred for both
  samplers pending paper deadlines).

The factory agents wrote the Lean proofs, Julia implementations, test cases,
and benchmark harnesses. The human made the decisions that required domain
knowledge about MCMC algorithms, paper strategy, and what "good enough" means
for a given development stage.
