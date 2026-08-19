# Development log

## 2026-08-19: Lean-owned checked NUTS subtree IR foundation

Added the first typed executable NUTS tree program in Lean. Its interpreter
owns early-exit recursion, visited-leaf accounting, continuation, and ordered
candidate occurrences; Lean proves it equal to the existing audited
`OnlineBuildSummary`. The program also reuses the checked candidate-row
stationarity theorem while explicitly withholding a continuous Float64
invariance claim.

Artifact format version 20 now carries the concrete
`checked-nuts-reference` tree program. Julia strictly decodes that program and
uses a small generic tree interpreter with deterministic success, early-left-
failure, and root-turn tests. Lean now also owns typed directional phase-tree
construction from a one-step dynamics callback, proves the resulting leaf
count, and composes it with the structural interpreter; Julia interprets the
same forward/backward construction and checks candidate ordering. This is not
yet a complete NUTS transition. Lean and Julia now also consume the bounded
outer direction trace, stop before admitting a failed expansion, preserve
left-to-right occurrence order, and consume one explicit multinomial selection
mark. Lean proves the completed outer depth is bounded by the supplied trace.
Checked all-root row assembly and the continuous orbit lift remain the next
correspondence layers. Accordingly the benchmark remains labelled
`verified-runtime`.

## 2026-08-19: completed implemented-sampler benchmark rows

Extended new HMC benchmark runs with the already implemented VerifiedSamplers
production-shaped NUTS runtime and the Reference and Optimized constant-metric
endpoint and multinomial paths. NUTS is deliberately labelled
`verified-runtime`, since its full Lean transition-correspondence proof remains
open. Case-level progress reporting now identifies the target, algorithm,
implementation, total case count, and elapsed wall time outside timed regions.
The full benchmark was rerun before publishing these changes.

Earlier milestones are preserved in archive
[part 1](development-log-archive.md),
[part 2](development-log-archive-2.md), and
[part 3](development-log-archive-3.md).

## 2026-08-19: bounded log archives and validation CI

Split the historical development ledger at complete entry boundaries into
three published archive pages, keeping the current page focused and preserving
all prior text. Documentation CI now checks the committed Lean-generated page
instead of silently overwriting it. A separate validation workflow runs the
existing full Lean/generated-IR/Julia test target plus the generated-doc check;
this adds no benchmark gate or algorithm scope.

## 2026-08-19: unified timing and quality benchmark chains

Reworked the benchmark protocol so each timed repetition uses a distinct seed
from an explicit fixed list, retains its complete chain, and supplies both
performance and quality evidence. All compared implementations now pay the
same chain-storage cost; diagnostic calculations happen after timing, and the
separate quality-only sampling workload is removed. Historical committed CSVs
remain provenance-correct and render through the backward-compatible report.
The full benchmark was not rerun.

## 2026-08-19: non-gating multi-chain benchmark diagnostics

The benchmark quality path now uses independently seeded chains and the shared
split rank-normalized R-hat, bulk/tail ESS, covariance, marginal-quantile, and
batch-means functions. New CSV rows include a clearly labelled gradient-work
proxy, maximum Gaussian covariance error, symmetry-implied marginal-median
error, and mean MCSE. Reports remain backward-compatible with historical rows
and mark R-hat above 1.01 visibly without turning it into a CI gate. A tiny
development run validated the harness; the slow full benchmark was not rerun.

## 2026-08-19: canonical continuous and whole-artifact syntax round trips

Lean now checks canonical parse/re-render results for the existing scalar
Gaussian-RWMH and scalar fixed-step-HMC declarations. The complete artifact
already has a checked envelope parse. These deliberately remain syntax
results; the exact finite core retains the stronger typed decoder, while a
general typed continuous decoder and Julia-interpreter correspondence remain
outside this bounded improvement.

## 2026-08-19: shared deterministic trace-conformance contract

Added a small test-support harness that replays one floating-point primitive
event list through independent Reference and Optimized sources and compares
both results and trace consumption. Scalar Gaussian RWMH and fixed-step HMC now
use the shared contract, retaining explicit expected accept/reject checks where
applicable. This standardizes existing test evidence without treating it as a
Julia-semantics proof.

## 2026-08-19: exhaustive maintained IR input validation

The Julia artifact decoder now rejects unknown input kinds and duplicate input
names instead of allowing an unknown kind through or silently overwriting an
environment binding. Runtime argument validation explicitly covers every input
kind present in canonical artifact version 19, including exact natural vectors
and matrices and the existing certified-HMC callbacks. Parser and validator
regressions cover the rejection cases. The artifact format and algorithm set
are unchanged.

## 2026-08-19: shared scalar runtime input contracts

Centralized the already-identical positive-finite parameter, positive-count,
and finite scalar-state checks used by the public, Reference, and Optimized
RWMH/scalar-HMC paths. Transition arithmetic and callback evaluation remain
independent, preserving the value of differential testing. Unit tests fix the
shared validation behavior. This is an execution-infrastructure refactor and
does not change any sampler or theorem claim.

## 2026-08-19: generated assurance registry and HMC golden-path audit

Added a Lean-maintained, generated assurance registry for the existing scalar
Gaussian RWMH and fixed-step endpoint-HMC golden paths. Evidence is recorded by
independent facet rather than a single maturity badge, so proved exact-real
results do not upgrade test-supported Julia behavior. The accompanying HMC
development record identifies the existing checked kernel invariance,
integrator correspondence, and deterministic replay results, while preserving
the absence of one full command-kernel equality theorem as an explicit
composition gap. No sampler or mathematical claim was added.

## 2026-08-19: calibrated RWMH quality regression

Reused the existing seeded scalar Gaussian RWMH chain to exercise the shared
moment, covariance, marginal-quantile, autocorrelation-ESS, and batch-means
interfaces in one integrated regression. The mean tolerance is calibrated by
the observed batch-means Monte Carlo standard error, while variance and
quantile tolerances remain conservative fixed regression thresholds. This adds
no extra sampling workload and remains empirical implementation evidence, not
a convergence theorem.

## 2026-08-19: completed RWMH sampler-development record

Applied the sampler-development obligation template to scalar Gaussian RWMH.
The resulting record connects the general-state Markov, reversibility, and
invariance theorems to the exact kernel denotation, explicit-trace Lean
interpreter, canonical artifact, Julia Reference/public/Optimized paths, and
shared diagnostics. It also records normalization and convergence as separate
obligations and keeps Julia `Float64`, callback, parser, and RNG assumptions
outside the exact-real theorem. This is documentation of the existing golden
path, not a new algorithm or a stronger execution theorem.

## 2026-08-19: fixed-parameter HMC runtime parity and recursive control bridge

Added a non-adaptive Julia HMC surface covering fixed integration time,
per-trajectory step-size jitter, symmetric momentum tempering, persistent
partial momentum refresh, and fixed low-rank-update metrics. Added classic and
generalized NUTS with multinomial and slice selection, bounded tree depth,
divergence termination, and structured diagnostics. Seeded primitive-trace,
metric, divergence, reproducibility, and Gaussian-moment tests cover the new
runtime paths. This is runtime coverage, not a blanket `Float64` correctness or
stationarity claim.

At the formal control-flow boundary, `RecursivePhaseTree.onlineBuildSummary`
models production-style early exit on a precomputed phase tree. Lean proves
that its continuation result equals the existing completed-tree flag semantics
and that a successful build visits every leaf. It now also retains candidate
occurrences and proves that every successful online build yields exactly the
completed tree's ordered leaf sequence, including multiplicity. A generic
consumer congruence theorem covers weighting and selection under a fixed random
trace. The bounded numerical refinement now lifts tree-local leaf-energy and
U-turn certificates through that full online summary, including visited count
and candidate order. The generated descriptor's fuel-bounded midpoint checker
is now proved equal to structural U-turn aggregation on every balanced
power-of-two interval. If it reports no turn, Lean identifies the online
candidate occurrences with the exact consecutive index range. A second
fuel-bounded recursion incorporates arbitrary leaf eligibility/divergence
bits; Lean proves its continuation equals both the completed flag tree and the
early-exit online summary, and proves the same exact range result whenever it
succeeds. Connecting Julia's concrete call trace to this Lean recursion and
then relating the complete Julia transition to a verified invariant kernel
remain explicit obligations.

The upstream API audit also corrected fixed-integration-time behavior to
AdvancedHMC's `max(1, floor(λ / ε))`: a positive integration time shorter than
one nominal step now executes one step instead of being rejected. The parity
page distinguishes feature-level coverage from full Cartesian component
composition and records which integrator/trajectory combinations have
dedicated constructors. NUTS now supports ordinary, per-trajectory jittered,
and tempered leapfrog across both termination criteria, both selection rules,
and every maintained fixed metric. The audit also corrected slice-mode
divergence to use its sampled log-slice threshold and changed reported tree
depth to count only successful doublings, matching the upstream transition.
Outer candidate replacement now uses the upstream subtree/current MH ratio,
while recursive internal merges retain normalized combined-tree selection;
these are deliberately separate rules. The maximum-energy diagnostic retains
the signed error with greatest absolute magnitude rather than only its
absolute value.

Fixed multinomial HMC now composes with per-trajectory step-size jitter for
unit, diagonal, dense, and fixed low-rank-update metrics. A deterministic trace
test identifies the result with the existing fixed-step Reference transition at
the realized step size, and metric smoke tests plus a Gaussian-moment diagnostic
exercise the public API. The constructor intentionally rejects tempered
multinomial trajectories: the endpoint tempering argument does not supply the
correct weights for selecting an intermediate tempered state, and a strong
diagnostic gave empirical evidence of bias for the naive energy weighting.
Tempered endpoint HMC and tempered NUTS remain available; fixed tempered
multinomial selection needs a separate weighting theorem before it can be
exposed safely.

The fixed-integration-time endpoint constructor now accepts the same ordinary,
jittered, and tempered integrator choices as fixed-step endpoint HMC. It derives
the positive step count from integration time and nominal step size before
constructing the selected fixed-step sampler. Seeded equality tests identify
the jittered and tempered wrappers with those underlying transitions, including
a non-unit metric.

The upstream completion audit identified a previously omitted dynamic criterion:
`StrictGeneralisedNoUTurn`. The public NUTS constructor now accepts
`termination=:strict_generalized` and applies the ordinary generalized check
plus AdvancedHMC's left- and right-subtree interface checks at every merge.
Deterministic tests cover the complete three-termination × two-selection ×
three-integrator runtime matrix, and a synthetic tree distinguishes the strict
criterion from the ordinary generalized one.

The parity page now also accounts explicitly for AdvancedHMC's
position-dependent `GeneralizedLeapfrog`. Existing fixed-point Reference and
Optimized execution, certified solver clients, and `GaussianSoftAbsGRHMC` are
linked as the separate GR-HMC coverage track; they are not presented as an
arbitrary composition with the fixed-Euclidean NUTS matrix.

## 2026-08-19: typed finite artifact parsing and lightweight optimization plan

Added a Lean parser for the canonical S-expression artifact syntax and a typed
decoder for the finite command IR. The categorical and generic finite-MH
programs now have compiled byte-for-byte parse/decode/re-render theorems;
escaped strings round-trip, and an ill-typed return is rejected. This closes a
finite serializer-format trust gap without claiming equivalence to the Julia
parser or a formal semantics for Julia. The execution plan now keeps the
existing handwritten `Optimized` layer, avoids a new optimizer framework, and
reserves Metatheory.jl or IRTools.jl for concrete benchmark-motivated
transformations whose semantic preservation is separately proved or checked.
