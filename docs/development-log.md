# Development log

## 2026-08-21: fixed-map transport HMC

Added `Mcmc.Hamiltonian.TransportHMC`, which reuses exact measurable-
equivalence kernel conjugation. Its multinomial-HMC client exposes the target
pushforward equality as the change-of-variables/Jacobian obligation. The Julia
`TransportHMC` interface takes a forward map, inverse, Jacobian-transpose
action, log absolute Jacobian determinant, and its gradient. It reuses the
IR-backed vector endpoint-HMC Reference and generic Optimized transition.

Tests cover exact affine Reference/Optimized replay, original-coordinate
moments, a nonlinear `sinh` map, validation, and `Float32` Optimized execution.
The map is fixed during retained sampling; learning, callback consistency,
concrete analytic Jacobian proofs, and endpoint executable refinement remain
declared boundaries.

The hard-geometry benchmark now includes both methods. Exact-map Transport HMC
uses the analytically known inverse warp and reaches tail ESS/transition
`0.5555` with `Rhat=1.005`; this is an oracle upper baseline that excludes map
learning. Fixed rank-one likelihood-informed HMC reaches `0.2931`, but
`Rhat=1.107` makes its short-run ESS/s non-interpretable as converged evidence.

Added a generic `RankOnePolynomialTransport` and its moment-based fitter. The
map is full dimensional but has one triangular quadratic coupling, analytic
inverse and pullback, and constant log determinant. Tests recover hidden
directions on a rotated dimension-16 banana, check forward/inverse agreement,
and exercise `Float32`. With 5,000 controlled independent target training
samples, the selected fitted-map benchmark reaches tail ESS/transition
`0.5051` and `Rhat=1.004`, compared with `0.5113` and `1.005` for the analytic
oracle. Training-sample acquisition remains deliberately unclaimed.

The practical acquisition follow-up gives every method four independent
chains. Each runs exactly 1,000 ordinary-HMC transitions and continues from
its own endpoint and RNG state under the evaluated transition; the fitted
method pools its own 4,000 warmup states and freezes one map. Selected
ordinary-HMC, analytic-map, and fitted-map continuations have tail
ESS/transition `0.1543`, `0.4595`, and `0.3819` and Rhat `1.046`, `1.006`, and
`1.008`; charging each method's acquisition gives end-to-end tail ESS/s about
`544`, `4,494`, and `2,299`. This work also found
that the geometry-study HMC baseline passed the score instead of the potential
gradient; the sign was corrected and affected benchmark evidence regenerated.

## 2026-08-21: fixed likelihood-informed split

Added the exact `likelihoodInformedSplit_invariant` composition theorem and a
Julia `LikelihoodInformedHMC` client for targets represented as a likelihood
times a standard Gaussian reference. It performs conditional endpoint HMC in
a fixed orthonormal active subspace and an MH-corrected pCN proposal in the
orthogonal complement; the pCN acceptance ratio contains only the likelihood
change because the proposal is reversible for the Gaussian reference.

Reference and generic Optimized paths share the existing vector-HMC engine.
Tests cover exact path replay, Gaussian-reference moments, a nontrivial
active-direction posterior variance, invalid bases, and `Float32`. Concrete
Lean component-invariance clients and a typed descriptor for the composed
schedule remain open, so the current theorem surface is explicitly
conditional rather than presented as full command refinement.

## 2026-08-20: RMHMC website benchmark integration

The focused nonconstant classical-RMHMC runner now emits the same aggregate,
per-seed timing, sampling-quality, and provenance schemas as the main HMC
suite. The production report appends its three implementation rows to the
shared tables, SVG, and interactive explorer while displaying the separate
five-dimensional, three-chain workload and AdvancedHMC internal-source caveat.
The committed measurements were produced from benchmark harness commit
`6258cc9`.

## 2026-08-20: focused classical RMHMC benchmark

Added artifact version 22 and public generic `DenseRiemannianRMHMC`, which
compose arbitrary dense positive metrics, their derivative tensors, classical
Gaussian Hamiltonian derivatives, and fixed-point generalized leapfrog.
Finite solves must meet a declared residual tolerance and remain explicitly
approximate; `ClassicalRMHMC` still requires an exact solver certificate.
Public and Optimized sampler arithmetic now preserve a concrete
`T<:AbstractFloat`, with Float64 conversion confined to generated Reference.

`make benchmark-rmhmc` compares generated Reference, independent Optimized,
and the pinned AdvancedHMC Riemannian path on `G(q)=diag(2+sin(qᵢ))` with a
shared iteration and trajectory budget. It reports median throughput,
allocations, and Gaussian mean/variance errors without claiming that residual
acceptance proves exact stationarity.

## 2026-08-20: executable classical RMHMC

Artifact format version 21 adds the Lean-emitted `classical_rmhmc_step!`
descriptor. The Reference interpreter refreshes `N(0,G(q))` momentum by
inverse-factor transport, requires an exact generalized-leapfrog certificate
at every step, and applies endpoint Metropolis correction. An independently
maintained, generically typed Optimized transition follows the same callback
contract. Public `ClassicalRMHMC` defaults to Reference and permits an explicit
`:optimized` selection. Deterministic replay, nonidentity constant-factor
differential tests, Gaussian moments, invalid-factor checks, and rejection of
approximate implicit solves cover the executable boundary.

## 2026-08-20: classical Gaussian-momentum RMHMC foundation

Classical RMHMC now precedes the Xu--Ge relativistic specialization in the
formal dependency order. `Mcmc.Hamiltonian.GeneralizedHMC` extracts the
momentum-law-independent generalized-leapfrog endpoint theorem: exact
measurability, reversal, phase-volume preservation, Metropolis reversibility,
phase invariance, and lift/evolve/project position invariance.

`Mcmc.Riemannian.Classical` instantiates that foundation with
`p | q ~ N(0,G(q))`. Lean proves the inverse-factor Gaussian transport density,
including the determinant term; identifies the normalized phase weight with
the paper Hamiltonian up to one global Gaussian prefactor; and proves that the
certified endpoint transition preserves the intended position Boltzmann
measure. The identity-metric client discharges every obligation with the
explicit separable generalized leapfrog. Arbitrary nonconstant metrics still
require measurable factor data and an exact valid implicit-solver certificate;
finite-tolerance fixed-point iteration is not silently treated as exact.

## 2026-08-20: consolidation roadmap and executable registries

The canonical roadmap now treats assurance declarations, deterministic replay,
the optimization gate, independent chains, host batching, and the scoped
accelerator adapter as completed foundations. Its active ordering is
modularization, uniform sampler obligation records, packaging of existing HMC
boundaries, continuous-contract consolidation, concrete backend conformance,
and demand-driven optimization; numerical universality and hard new theorem
families remain parked.

Julia public engines for finite MH, finite particle Gibbs, composable
inference, observation cursors, Gaussian Zig-Zag, and the Xu coupling moved to
coherent files without changing dispatch. Reference artifact parsing is now
separate from transition execution. The certificate aggregation was split into
rational SoftAbs, dynamic-tree, practical-slice, and implicit-solver engines.
Lean adds `finiteScheduledEndpointHmcKernel_invariant`, proving that an
independent finite choice of endpoint-HMC step size and step count preserves
the same explicitly factored target. This does not identify continuous Julia
jitter with the finite mixture.

A generated Reference artifact registry now lists every decoded executable
facet directly from artifact version 20, and the common sampler obligation
matrix records exact semantics, runtime paths, evidence, and open refinement
boundaries uniformly.

## 2026-08-20: explicit benchmark metric labels

Constant-metric benchmark algorithms now put the trajectory family first and
name the metric representation explicitly: `endpoint-dense`,
`multinomial-dense`, `endpoint-diagonal`, and `multinomial-diagonal`. The
runner derives the suffix from the configured mass representation, so future
targets cannot silently reuse an ambiguous `preconditioned-*` label. Existing
recorded measurements were relabelled without changing their values.

## 2026-08-20: generic optimized floating-point implementations

The optimized continuous stack now propagates a single
`T<:AbstractFloat` through sampler parameters, state, prepared and public
metrics, workspaces, trajectories, NUTS trees, and transition diagnostics.
Random draws are converted to `T` only at the runtime-source boundary. The
coverage includes fixed, metric, multinomial, relativistic, generalized,
jittered, tempered, partial-momentum, slice, DHMC, and dynamic-NUTS paths.
Float32, Float64, and BigFloat type-preservation tests accompany the existing
behavioral suite. The 67-case Float64 development benchmark showed no material
regression relative to the pre-refactor measurements.

## 2026-08-20: shared NUTS benchmark depth budget

The `nuts-complete` and `nuts-dynamic` benchmark groups no longer give
completed-tree Reference NUTS a depth of four while giving Optimized and
AdvancedHMC a maximum depth of ten. A single
`HMC_NUTS_MAX_DEPTH` setting now applies to all three, with a tractable default
of four. Reference uses the full `2^d` budget; dynamic NUTS may stop earlier,
so the report continues to expose mean leapfrog work alongside throughput.

## 2026-08-20: prepared-metric endpoint and multinomial optimization

The independent constant-metric Optimized backend now prepares a metric once
per chain. Diagonal preparation caches inverse and square-root entries; dense
preparation caches the Cholesky momentum map and a BLAS-ready inverse-mass
matrix. Leapfrog reuses the force shared by adjacent steps, reducing gradient
callbacks from `2L` to `L+1`. Randomized-origin multinomial construction now
integrates its left and right branches from the original phase point in exactly
`L` total steps instead of retracing the left branch, stores only positions and
log weights, and preserves the random-event schedule.

The complete ten-chain benchmark passed. On its 100-dimensional correlated
Gaussian fixture, Optimized preconditioned endpoint reached about 18.8k
transitions/s versus AdvancedHMC's 10.4k, and Optimized preconditioned
multinomial reached about 15.7k/s versus 9.4k. On the diagonal
ill-conditioned fixture the corresponding rates were about 159k versus 18.3k
and 96.4k versus 14.8k. These are empirical measurements on the recorded
benchmark host, not formal performance claims.

## 2026-08-19: backend contracts, replay, and independent chains

The Julia package now exposes typed backend capabilities separately from
assurance classes, rejects unsupported capabilities, and promotes deterministic
trace replay from test support into `VerifiedSamplers.Evaluation`. Replay
compares values or matching failures and exact event consumption. A parallel
CPU executor runs independent chains from explicit seeds and preserves input
ordering, with sequential-equivalence tests. The optimized NUTS forwarding
surface moved out of the central public module without changing its API.
Exact-integer replay also compares the complete sequence of requested draw
bounds, not only results and remaining trace length.

Optimization trials now require an explicit pre-change baseline, the complete
release gate, a measured speedup threshold, and a machine-readable acceptance
record. Numerical certificates remain optional evidence rather than an
execution layer.

A batched-transition protocol adds a maintained ordinary-array reference and a
fail-closed accelerator adapter. Adapters declare operations and evidence and
own device transfer, RNG, reductions, callbacks, and materialization; merely
registering one grants no numerical or formal assurance. The backend capability
page is generated directly from the Julia registry.
The first maintained accelerator-ready operation is batched Gaussian RWMH over
broadcast-compatible arrays. Gaussian and uniform events are explicit, and its
host-array result is checked event-for-event against scalar Reference. No GPU
runtime or device arithmetic is thereby certified.

## 2026-08-19: shared Evaluation layer

Standard evaluation targets and sampling-quality diagnostics now live in the
public `VerifiedSamplers.Evaluation` module. CI tests consume it for small,
stable regression gates; the benchmark consumes the same definitions and adds
multi-chain workloads, timing, aggregation, CSV output, and visualization.
The benchmark no longer reaches into `test/support`, while remaining
explicitly layered on top of the statistical evaluation foundation.

## 2026-08-19: first measured NUTS optimization and width control

An agentic code-review pass found that the optimized NUTS path redundantly
copied already-owned phase vectors. It now specializes phase construction for
already-owned
`Vector{Float64}` states, eliminating redundant elementwise conversions at
every tree leaf while preserving the generic conversion boundary. The
repeatable `make benchmark-nuts-optimization` acceptance experiment reports
its transformation and assurance class; the initial 100-dimensional run
improved median 10,000-draw time from 0.865 to 0.755 seconds. Existing trace,
property, and statistical gates remain required because this is a
test-supported Julia optimization, not a new Lean transition-equivalence
theorem. Program-transformation packages, profilers, and compiler diagnostics
are documented as optional tools available throughout future optimization
passes rather than mandatory pipeline stages.

Documenter retains its readable 50-rem default. A navbar toggle now switches
between normal and full-width content, persists the preference locally, and
falls back to the normal responsive layout on small screens.

## 2026-08-19: canonical NUTS uses productive completed-tree rerooting

The canonical Julia `NUTS` Reference now uses `CompletedTreeC4DynamicHMC`.
Unlike the fixed-trace global checker, this construction gives every possible
root its unique direction trace for reconstructing the same completed tree,
then retains the roots satisfying the C.4 stopping condition. Lean proves the
fair reconstruction traces have equal mass and proves reversibility and
stationarity of the resulting completed-tree sampler. The older
`CheckedRecursiveDynamicHMC` remains available as the conservative
checked-or-identity experiment rather than an alias for `NUTS`.

The Julia suite now requires canonical `NUTS` to make a nonidentity move on a
seeded Gaussian run. The benchmark parameter is tree depth
(`HMC_NUTS_REFERENCE_DEPTH`) rather than a misleading arbitrary orbit length.

## 2026-08-19: interactive benchmark explorer

The benchmark report generator now emits a browser dataset from the same
committed timing and quality CSVs used by its tables and static SVG. The
Documenter page adds a Plotly explorer with metric, target, algorithm,
implementation, and grouping controls, including per-seed timing hover data.
The existing SVG remains the non-JavaScript and portable-rendering fallback.

## 2026-08-19: NUTS names follow verification boundaries

This earlier milestone moved the canonical public `NUTS` constructor to the
checked, Lean-IR-driven Reference implementation. The completed-tree milestone
above subsequently made `NUTS` productive; `CheckedRecursiveDynamicHMC` now
names only the older conservative experiment. The independent handwritten
production-shaped comparator is available as `Optimized.NUTS`, while
`VerifiedNUTS` remains a compatibility alias. Benchmark rows for the
handwritten implementation are correspondingly
labelled `verified-optimized`, while checked `NUTS` is
`verified-reference`. The optimized label records empirical conformance and
statistical evidence; no equivalence theorem between the two transitions is
claimed.

## 2026-08-19: continuous checked-row invariance bridge

Added the general-state theorem needed by checked multinomial NUTS selection.
Lean now constructs a measurable Markov kernel from a finite, phase-dependent
candidate mask and proves detailed balance and invariance of the phase-space
Boltzmann measure when the mask retains its root, is reroot invariant at every
admitted candidate, and has symmetric pair membership. A proof-bearing
`CertifiedTrajectoryCandidateRows` interface derives those algebraic
conditions from globally checked finite rows plus Hamiltonian-orbit covariance.
Lean also proves that an arbitrary orbit-covariant raw row builder can be made
total by the executable checked-or-identity transformation: rejected families
become singleton rows, while accepted families retain their candidates.

The Julia `CheckedRecursiveDynamicHMC` path now delegates row construction,
global checking, identity fallback, and weighted selection directly to the
decoded `checked-nuts-reference` program interpreter. It is also exported as
canonical `NUTS`. The independent handwritten production-shaped comparator is
now explicitly named `Optimized.NUTS`.

`Program.rawOrbitCandidateRows` now identifies the concrete
`recursiveDoublingCandidateRow` interpreter with the continuous checked-row
interface for each bounded direction trace. Pointwise orbit stability of the
endpoint-turn callback proves covariance of every emitted row, after which the
global checker, identity fallback, detailed-balance theorem, and invariance
theorem compose in `Program.checkedOrbitKernel_invariant`.
The bounded trace length is explicit and checked against the artifact's
maximum, matching Julia's decoder contract. Lean now also forms the fair
state-independent mixture over all direction traces of that length and proves
it invariant. Finally, momentum refresh and position projection are composed
in `Program.positionRandomizedCheckedOrbitKernel_invariant`, giving the
user-facing exact-real target theorem rather than only a phase-space result.
The row certificate now carries the orbit's anchor index explicitly; this
prevents hypothetical reroot rows from accidentally being computed on shifted
physical orbits. Lean proves that the actual Euclidean endpoint U-turn
predicate is measurable and stable under reanchoring. Consequently
`Program.positionVectorUTurnReferenceKernel_invariant` discharges the complete
ideal structural stack without leaving abstract checker or measurability
assumptions.

This closes the exact-real measure-level theorem and migrates the
conservative checked Reference sampler. It does not yet prove that Julia's
floating leapfrog and U-turn callbacks refine that exact-real orbit-row family,
nor
that the separate production-shaped `Optimized.NUTS` transition is equivalent to the
checked Reference. Those boundaries remain required before changing the
`verified-optimized` row from empirical evidence to a formal correspondence
claim.

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
Julia now also interprets every rooted row, applies the exact executable
root-retention/reroot-equality check, and consumes no selection mark on the
identity branch; conformance tests compare this result with the pre-existing
certificate API. The general continuous checked-row invariance theorem is now
available in the next layer, while the concrete recursive interpreter's
orbit-covariance proof and public sampler migration remained at this milestone.
The later namespace cleanup and rerun now label the checked client
`verified-reference` and the independent comparator `verified-optimized`.

## 2026-08-19: completed implemented-sampler benchmark rows

Extended new HMC benchmark runs with the already implemented VerifiedSamplers
production-shaped NUTS runtime and the Reference and Optimized constant-metric
endpoint and multinomial paths. The handwritten NUTS comparator is labelled
`verified-optimized`, denoting empirical conformance and statistical evidence
rather than a completed Lean transition-correspondence proof. Case-level
progress reporting now identifies the target, algorithm,
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
kind present in canonical artifact version 20, including exact natural vectors
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

## 2026-08-20: budgeted random-sketch RMHMC prototype

Added a generic fixed-probe `RandomSketchRMHMC` runtime. Given `M` fixed
curvature probes, it constructs the position-dependent metric
`G_M(q) = lambda I + U_M(q) U_M(q)^T`, samples its Gaussian momentum without a
dense factorization, and evaluates inverse actions, log determinants, and
metric-force contractions using an `M`-dimensional Gram matrix. The runtime
uses the existing bounded-residual generalized leapfrog and therefore does not
claim exact floating-point reversibility, volume preservation, or stationarity.

The accompanying nonlinear-banana benchmark compares ordinary HMC, full dense
GGN RMHMC, the sketch materialized through dense RMHMC, and the same sketch
using structured algebra. It reports ESS per second and per configured
integrator step in addition to raw throughput. The matched sketch rows isolate
the structured implementation gain; ordinary-HMC and full-RMHMC comparisons
also change geometry and answer a different efficiency question. Offline
amortized curvature prediction and online adaptation remain later research
stages.

A subsequent hard-geometry study evaluates a strongly warped Gaussian in its
known latent standard-normal coordinates. The current protocol runs four
2,000-iteration chains and discards the first 1,000 iterations. The 2D full
and rank-one sketch RMHMC rows have rank-normalized `Rhat` of `1.011` and
`1.006`; the sketch slightly exceeds full RMHMC in bulk and tail ESS per
retained transition. The selected HMC row has `Rhat = 1.204`, so ratios against
its ESS estimate are not treated as converged evidence.

The benchmark environment now pins `UnicodePlots` and the geometry-study
runner has an optional dimension-sweep mode. Sweep children use a dense rotated
volume-preserving warp with known inverse and analytic pullback metric, then
aggregate the best numerically stable rows across ambient dimension. The
runner writes both CSV summaries and terminal-rendered plots. All current
geometry sweeps use the same 2,000-iteration/1,000-burn-in policy and record
total, burn-in, and retained counts in each result row.

## 2026-08-21: sketch-rank and implicit-solver audit

The dimension runner now checkpoints every chain, records the probe count, and
supports the schedule `M(d) = ceil(log2(d))`. An audit found that the original
study passed a zero fixed-point stopping tolerance with a 50-iteration cap,
which normally forced all 50 iterations. The refined study instead stops at
`1e-10`, caps at 25 iterations, and retains the independent `1e-6` residual
gate. A 12-iteration trial failed closed at that gate; 25 passed the exercised
workloads and roughly doubled rank-one throughput at dimensions 2 and 16.

The rank-log result is negative on the current intrinsically rank-one warped
target. At dimensions 4 and 8 it improves some `Rhat` values, but additional
probe work reduces ESS/s; at dimension 32 its selected row has `Rhat = 1.120`
and is not a trustworthy convergence result. This does not reject higher-rank
sketching on genuinely higher-rank geometry. It shows that probe rank must be
treated as a measured budget rather than increased automatically.

The same audit corrected the execution-layer description. `VectorHMC` in this
study is the IR-backed Reference transition. Dense and sketch RMHMC use the
Optimized generalized-leapfrog machinery, while metric construction and public
orchestration remain direct Julia in those timed rows.

## 2026-08-21: IR-backed dense and random-sketch RMHMC Reference

Artifact version 23 adds explicit `dense_rmhmc_step!` and
`random_sketch_rmhmc_step!` programs. The dense entry gives the existing
bounded-residual classical primitive an unambiguous public artifact name. The
random-sketch entry uses a new `structured-rmhmc` primitive whose IR-declared
transition owns momentum refresh, repeated certificate checking, Hamiltonian
comparison, and accept/reject. Its structured momentum callback consumes the
required `d + M` standard normals without materializing a dense factor.

Public `implementation=:reference` now routes both samplers through these
artifact programs; `implementation=:optimized` remains an independently
maintained path. Seeded multi-step tests compare the two paths. This is an
IR-backed executable Reference contract, not a theorem about Julia, callbacks,
floating-point fixed-point solves, or positive-residual stationarity. Metric,
curvature-action, derivative, and finite-tolerance integrator callbacks remain
explicit host boundaries.

## 2026-08-21: optimized RMHMC linear-algebra pass

The maintained dense RMHMC path now reuses one Cholesky factorization within
each Hamiltonian or force callback and computes the inverse-metric trace terms
with one matrix solve rather than one solve per coordinate. The structured
random-sketch path similarly reuses one small Gram-matrix factorization for
all inverse actions within a callback, caches typed factor/derivative geometry
across repeated fixed-point evaluations at the same position, fuses the force
contractions, and fills factor work arrays without temporary column
assignments.

Seeded Reference/Optimized trajectory parity, statistical smoke tests, and
`Float32` type-propagation tests continue to pass. The exploratory
`random_sketch_*` research workloads explicitly select these Optimized dense
and sketch paths; the separate RMHMC comparison benchmark retains its
Reference, Optimized, and AdvancedHMC rows.

On the dimension-20 matched-metric workload, the cached structured path
increased from about 972 to 2,157 draws/s and reduced median allocation from
2.20 GB to 0.56 GB. A non-writing dimension-16 geometry confirmation reduced
the optimized sketch chain time from about 19.5 to 10.6 seconds and increased
tail ESS/s from 25.6 to 52.6 for the exercised seeded configuration. These are
machine-specific empirical measurements, not formal performance claims.

## 2026-08-21: end-to-end isotropic MALA

Added explicit scalar and vector MALA programs to artifact version 24. The
programs use proposal standard deviation `ε`, mean
`q + ε²/2 ∇logπ(q)`, and the full forward/reverse Gaussian Hastings
correction. Julia now exposes an IR-interpreted Float64 Reference and an
independent generic `T<:AbstractFloat` Optimized implementation through the
same `MALA` public API. Seeded event replay, normal-target moments, vector
dimension checks, and `Float32` propagation cover the maintained paths.

The general-state Lean theorem remains the mathematical source of truth:
MALA is Markov, reversible, and invariant under its stated measurability,
positive-variance, and finite-flow hypotheses. This is not a geometric
convergence theorem, and it does not identify Float64 Julia execution with
exact-real semantics. The shared benchmark now records MALA Reference and
Optimized timing and quality rows with a separately reported step size.

The contributor guide now uses this addition as a worked vertical slice. It
records the recommended file-by-file order, stage exit conditions, definition
of done, and the still-open full stochastic command-to-`scoreMALA` refinement
as a distinct obligation rather than treating artifact generation or replay
tests as a proof of that bridge.

The hard-geometry random-sketch study now includes the Optimized MALA path with
an independent proposal-standard-deviation grid. A complete four-chain run at
2,000 iterations with 1,000 discarded selected `ε=0.3` by tail ESS per
transition, but its rank-normalized `Rhat=1.362` shows that the chains did not
mix adequately. Its large nominal ESS/s is therefore not interpreted as
quality-adjusted performance. On the same run, full and sketch RMHMC retained
`Rhat=1.011` and `1.006` with tail ESS/transition `0.1737` and `0.1903`.

## 2026-08-21: position-dependent MALA foundation

Added an algorithm-seeking plan for the Langevin use of full and random-sketch
metrics. Following Xifara et al., the primary convention targets a density with
respect to Lebesgue measure and includes half the row divergence of the inverse
metric. The note separately labels original/full MMALA and simplified MMALA so
their reference-measure and diffusion interpretations are not conflated.

The new Lean module defines inverse-metric action, inverse-metric divergence,
the corrected and simplified drifts, and the Euler mean. It packages the
measurability and row-normalization obligations of a position-dependent
proposal density and proves its Metropolis completion Markov, reversible, and
invariant. A dense state-dependent Gaussian client must next prove that its
implemented mean/covariance density satisfies this interface. The dense
Gaussian formula is now explicit, while analytic row normalization remains a
client hypothesis rather than an axiom hidden in the kernel definition.

Artifact version 25 adds `dense_pmala_step!` with explicit target-score,
metric, metric-derivative, step-size, and state inputs. Julia supplies an
IR-interpreted Float64 Reference, an independent generic Optimized transition,
and public `DensePMALA` dispatch. Shared-event tests check both implementations,
the identity metric reduces to ordinary MALA, standard-normal moment tests pass,
and the maintained path preserves `Float32`.

The hard-geometry study selected dense PMALA at `ε=1.0`, with tail
ESS/transition `0.1912`, nominal tail ESS/s about `27,077`, and
rank-normalized `Rhat=1.050`. The per-transition result is competitive with
full and sketch RMHMC, but the borderline `Rhat` means the throughput-adjusted
ESS remains exploratory pending a longer run.
## 2026-08-28: parallel trajectory and Gauss--Legendre foundation

The parallel-integrator audit is now backed by an initial implementation.
Lean proves associative scalar-affine summaries, exact equality of an
edge-certified candidate trace with serial recurrence, the two-stage
Gauss--Legendre symplectic coefficient identities, and exact reverse-stage
algebra. IR format 26 adds an emitted vector Gauss--Legendre endpoint-HMC
program. The Julia Reference interprets that artifact; the generic Optimized
path offers serial and concurrent stage evaluation. Cross-layer parity,
reverse-step, exact-fallback, affine-scan, and `Float32` tests are included.
The public `GaussLegendreHMC` sampler selects the IR-backed Reference or the
generic Optimized backend and makes concurrent stage execution explicit.

The current finite fixed-point iteration is not claimed to satisfy the exact
stage equations merely because its residual is small. The remaining formal
gate is exact-stage certification/fallback plus the local theorem connecting
the symplectic Runge--Kutta coefficient condition to phase-volume
preservation. A two-thread development benchmark is integrated, but its cheap
100-dimensional targets expose scheduling overhead rather than a speedup.
