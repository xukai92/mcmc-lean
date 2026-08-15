# Development log

Entries through the earlier 2026-08-13 work are preserved in the
[development-log archive](development-log-archive.md).

## 2026-08-15: finite adaptive-kernel boundary

Added state-dependent selection from a family of finite Markov kernels and a
machine-checked two-state counterexample. The identity and flip kernels each
preserve the uniform target, but choosing the identity at `false` and the flip
at `true` sends both states to `false`, so the selected kernel does not preserve
that target.

This is a deliberately negative boundary result: validity of every frozen
kernel is not sufficient for state-dependent adaptation. It is not an adaptive
convergence theorem. History-dependent/nonhomogeneous chain semantics,
diminishing adaptation, mixing times, and containment remain future layers.

## 2026-08-15: finite multinomial-resampling and propagation identities

Generalized the iid particle theorem from unit-mean scores to arbitrary
observables. Defined multinomial ancestor resampling and proved that it
preserves every normalized weighted empirical average in conditional
expectation. Added heterogeneous independent particle populations for
conditional propagation through distinct kernel rows.

Lean now proves the one-step bootstrap resample--propagate identity: the
expected next empirical average is the current normalized weighted average of
the transition expectation. This is the local Feynman--Kac induction step.
The multi-time product-of-average-weights normalizing-constant theorem,
explicit ancestry history, and PIMH/PMMH clients remain next; no convergence
or particle-efficiency statement follows from the one-step identity.

## 2026-08-15: finite iid particle-estimator prerequisite

Added finite iid particle populations for every positive finite particle
index type. Lean proves population normalization, the weighted expectation of
each coordinate, and exact nonnegativity and unbiasedness of the average of
unit-mean particle weights. The result is packaged as the estimator consumed
by finite pseudo-marginal MH.

The resulting particle-importance MH kernel has machine-checked extended
stationarity and the exact requested state marginal for every positive finite
particle count. This is not yet bootstrap SMC, PIMH, PMMH, or particle Gibbs:
sequential propagation, resampling, ancestry, and Feynman--Kac
normalizing-constant unbiasedness remain explicit next obligations. No chain
convergence or particle-count consistency is claimed.

## 2026-08-15: tagged-space reversible-jump foundation

Added the common reference measure on a two-model disjoint union and packaged
general density MH as a reversible-jump specification. Lean proves the
resulting kernel is Markov, reversible, and target-invariant. Cross-model
accepted flow is exposed explicitly and remains symmetric even when one
proposal direction has zero density.

A transport-density certificate now isolates the real reversible-jump
obligation: the dimension-changing auxiliary transport must push its source
law to the claimed destination density, where a Euclidean client would prove
the Jacobian formula. Probability auxiliary laws imply normalization of the
certified cross-model density. A two-singleton-model example compiles and is
documented as periodic, hence invariant but not claimed convergent.

## 2026-08-15: general-state auxiliary Gibbs and slice interface

Added a measure-theoretic two-block conditional sampler on mathlib kernels.
The forward kernel constructs an auxiliary-first joint law; an explicit
reverse-factorization equation supplies the opposite conditional. Lean proves
that refreshing from the reverse conditional preserves the joint law and that
lifting, refreshing, and projecting preserves the original target.

Slice sampling is exposed as a named client with the exact vertical/horizontal
joint-factorization obligation. This is an invariance foundation, not yet a
concrete uniform-under-the-graph kernel, stepping-out implementation, or
convergence theorem.

## 2026-08-15: concrete vertical slice kernel and under-graph law

Added the general-state vertical slice update for a strictly positive
measurable real weight. Lean proves joint measurability, exact normalization
of the uniform height density on `(0, w(x)]`, and the Markov property. It also
proves that composing the weighted target with this height kernel cancels the
weight exactly and yields Lebesgue measure under the graph of `w`.

The slice invariance theorem is now stated using that concrete under-graph
measure. Its remaining obligation is the reverse factorization supplied by a
horizontal level-set conditional. Constructing that kernel generally requires
measurable disintegration and finite positive level-set mass; neither its
existence nor convergence is being assumed implicitly.

## 2026-08-15: pre-Xu general-state MH foundations

Added a general Doeblin-minorization interface and constructed the normalized
residual Markov kernel, with an exact proof that restoring the refresh
component recovers the original transition. Specialized general-state
independence MH to state-independent proposal densities and proved the
classical bounded target-to-proposal density ratio yields the `1 / M` target
minorization. The residual is proved target-invariant, its finite-time law has
an exact regenerative decomposition, and both directions of every measurable
event discrepancy are bounded by `(1 - 1 / M)^n` for the nontrivial `M > 1`
case. This is a genuine quantitative convergence theorem, not an inference
from stationarity alone. The exact-proposal boundary `M = 1` remains a
separate simplification theorem.

Added finite-dimensional state-dependent Gaussian proposals, ULA, and MALA.
Lean proves proposal normalization, the Markov property of ULA, and the Markov,
reversibility, and target-invariance properties of MALA. No target exactness
is claimed for fixed-step ULA, and no geometric-ergodicity claim is inferred
for MALA.

## 2026-08-15: executable Xu et al. coupled mixture

Advanced the sampler artifact to version 9 with generated descriptors for
coupled multinomial HMC, coupled Gaussian RWMH, and their shared mixture.
Julia Reference interprets shared momentum/origin trajectories with maximal
categorical coupling, maximal Gaussian proposals, shared acceptance uniforms,
and a shared mixture choice. The public `Xu21CoupledSampler` returns both
chains and replay-level exact-meeting flags; tests cover execution, validation,
and faithfulness after meeting.

Lean identifies the ideal mixture command with the existing verified coupled
kernel and proves that both marginals are the verified single-chain HMC/RWMH
mixture. The equality between this ideal-real denotation and Float64 replay is
not claimed; it remains governed by the explicit numerical-refinement
boundary.

## 2026-08-15: finite Gibbs, tempering, and pseudo-marginal foundations

Added reusable identity, composition, convex-mixture, and coordinate-lift
combinators for finite kernels, with stationarity closure. Built one-site,
random-scan, and systematic-scan Gibbs kernels from explicit target-slice
invariance equations. Added a two-temperature sampler whose within-replica
updates and MH-corrected swap preserve the product-temperature target, and
proved that its cold marginal is the requested target.

Generalized finite MH to targets containing zero-mass states and used it to
formalize pseudo-marginal MH with a nonnegative unbiased finite estimator.
Lean proves normalization of the extended target, its exact desired marginal,
detailed balance, and stationarity, including zero estimator values. These are
invariance results; no convergence or mixing claim is inferred.

## 2026-08-15: integrated project roadmap

Folded the broader primary-source algorithm review into a canonical project
roadmap. Its proposed combinator layer was reconciled with existing mixture,
product/lift/project, marginal, and path APIs. The selected next milestone is
API consolidation plus missing coordinate lifts and finite Gibbs kernels,
followed by parallel tempering and finite pseudo-marginal MH. Executable Xu et
al. coupling remains the next runtime milestone, followed by
certificate-bearing Xu and Ge execution.

## 2026-08-15: metric multinomial execution and selection certificates

Advanced the generated artifact to version 8 with diagonal and dense
constant-metric multinomial-HMC commands. Lean instantiates the generic orbit
kernel with constant-metric leapfrog and proves phase, refreshed-position, and
Cholesky-refreshed invariance. Julia Reference and Optimized retain independent
trajectory construction and pass correlated-Gaussian tests.

Added a parallel conditional certificate for multinomial categorical
selection. Lean proves identical indices outside every cumulative-boundary
uncertainty band and localizes disagreement to at least one band. Julia checks
matching per-run witnesses. Reference now also rejects nonfinite states and
callback results, non-real log densities, and malformed gradients;
certification remains outside the execution path.

## 2026-08-15: broader MCMC and HMC algorithm scope review

Added a primary-source literature triage covering twenty foundational and
high-impact papers across MH and Gibbs foundations, MALA, adaptive and
reversible-jump MCMC, pseudo-marginal and particle MCMC, geometric and manifold
HMC, NUTS, slice sampling, tempering, nonreversible PDMPs, coupled unbiased
estimation, and parallel evaluation across chain length. Each entry records the
claim boundary, the smallest useful repository integration, dependencies, and
formalization priority.

The review includes Zoltowski et al. (2025), arXiv:2508.18413v2, as a later
execution-refinement target: full solver convergence reproduces a seeded
sequential trace, while tolerance stopping and early stopping remain separate
numeric and bias obligations. The resulting near-term scope prioritizes kernel
composition/product/marginal infrastructure, finite Gibbs and tempering, and a
finite pseudo-marginal theorem before opening larger continuous-time or
nonhomogeneous-chain branches.

## 2026-08-15: executable progress review and next roadmap

Audited the version-7 executable surface after completing multinomial HMC.
The documentation now distinguishes five completed vertical slices: exact
finite MH, Gaussian RWMH, endpoint HMC, constant-metric HMC, and
randomized-origin multinomial HMC. Stale version-2 and future-HMC descriptions
were removed from the architecture and testing notes.

Added a current executable roadmap. The next priorities are multinomial
selection error certificates, constant-metric multinomial HMC, executable
coupled samplers for Xu et al. (2021), and certificate-bearing
relativistic/Riemannian execution for Xu and Ge (2024). Callback hardening,
adaptation, and performance work remain later, separately specified layers.

## 2026-08-15: generated executable multinomial HMC

Added a typed randomized-origin multinomial-HMC artifact and advanced the
generated sampler format to version 7. Lean proves that mapping the joint
uniform-origin/Boltzmann-index program through its deterministic trajectory
result gives exactly the existing verified multinomial PMF and kernel row.
The complete executable semantics is the standard-Gaussian
refresh–evolve–project kernel and inherits its position-target invariance.

Julia Reference interprets the generated command; Optimized independently
constructs the re-rooted trajectory. The public `MultinomialHMC` API follows
the positional-RNG convention. Fixed-trace differential tests and a
two-dimensional Gaussian moment test cover event ordering, indexing, and the
public sampling path. Float64 weight normalization and categorical selection
remain under the documented bounded-refinement boundary.

## 2026-08-15: backend-facing bounded decision certificates

Added operation-level Lean certificates for RWMH and endpoint HMC. Proposal,
callback, endpoint-energy, exponential, and uniform-draw bounds now compose
into the existing machine-checked comparison-stability and returned-state
bounds. No Julia, libm, callback, or RNG property is asserted axiomatically.

The Julia `Certificates` module provides matching execution-specific checked
witnesses. It validates supplied values and error budgets using `BigFloat`,
computes the same RWMH/HMC uncertainty sums as Lean, and reports whether the
accept/reject branch is outside the uncertainty band. These witnesses are
conditional certificates, not a universal semantics theorem for arbitrary
Julia callbacks or platform numerical libraries.

## 2026-08-15: fully generated and invariant constant-metric HMC

Completed Phase 1 of the constant-metric executable roadmap. Lean now proves
negative-step inversion, momentum-flip time reversal, arbitrary finite
trajectory permutation semantics, endpoint involution, phase-volume
preservation, deterministic-Metropolis Boltzmann invariance, and
refresh–evolve–project position invariance for constant metrics. Diagonal and
dense inverse-mass velocity maps instantiate the common interface.

The sampler artifact is now version 6. Type-indexed diagonal and dense metric
commands are generated from Lean, and Julia Reference routes both public
metric paths through `run_program`; Optimized remains independent. The
Gaussian transport layer proves the standard-momentum pushforward law,
pushforward of densities through measurable equivalences, the exact Jacobian
normalization, the quadratic transformed kinetic density, and the final
Cholesky-refreshed position-invariance theorem. Mathlib's invertible-matrix
Lebesgue theorem supplies the concrete `|det L|⁻¹` scale.

## 2026-08-15: vector trace, bounded refinement, and constant metrics

Closed the ideal vector-HMC replay theorem: a transition consumes exactly one
standard-normal event per coordinate and one unit-uniform event, exposes the
multi-step endpoint energies and acceptance branch, and returns the untouched
trace suffix. Added backend-independent coordinatewise leapfrog, energy,
threshold, and decision-stability certificates for bounded numerical
refinement.

Added public constant-metric HMC with positive diagonal and symmetric
positive-definite dense masses. Reference and Optimized implementations are
differentially tested. Lean defines diagonal and dense inverse-mass velocity
maps and proves one-step and arbitrary finite-step phase-volume preservation.
Tests now cover a correlated Gaussian, an ill-conditioned Gaussian,
Reference/Optimized fixed-trace agreement, and finite-difference dense-metric
phase-volume preservation. A concrete Float64 error witness and the
measure-level Cholesky/Gaussian refinement remain explicit future obligations.

## 2026-08-15: vector-valued executable HMC

Extended the generated sampler artifact to version 5 with a typed real-vector
command surface, vector target and gradient callbacks, dimension-indexed
standard-normal momentum draws, vector leapfrog expressions, kinetic energy,
and endpoint acceptance. Julia Reference interprets that generated program;
Optimized supplies an independent implementation. The public `VectorHMC` API
uses positional RNG dispatch and returns samples as columns of a matrix.

The exact endpoint-HMC phase and refresh–evolve–project position invariance
theorems were generalized from `Unit` to every finite coordinate type. Lean
also proves that list-valued executable leapfrog is exactly coordinate
serialization of the existing `Fin n → ℝ` Hamiltonian map. Tests cover
deterministic Reference/Optimized agreement, event consumption,
multidimensional reversibility, and two-dimensional Gaussian moments and
covariance. Finite-precision refinement remains separate and deferred.

## 2026-08-15: multi-step working scalar HMC sampler

Generalized the executable scalar HMC transition from one leapfrog step to any
positive runtime trajectory length. Version 4 of the typed artifact adds a
natural input and explicit scalar leapfrog-iteration expressions. Lean proves
the IR integrator equals the existing `leapfrogN` map for every finite length,
and proves involutivity, phase-volume preservation, Markov validity, and
Boltzmann-target invariance for the corresponding multi-step endpoint kernel.

Julia Reference interprets the trajectory length from the artifact; Optimized
uses an independent loop. The public `ScalarHMC(logdensity, gradient,
step_size, steps)` validates both tuning parameters and retains positional-RNG
dispatch. Differential trace tests now use multiple steps, and sampling tests
cover both a standard Gaussian and the non-Gaussian density
`exp(-x^4/4)` with its known second moment.

## 2026-08-15: bounded numerical refinement for scalar RWMH

Added a theorem-backed finite-error layer between ideal-real RWMH and a
floating-point backend. Absolute approximation bounds compose through the
affine Gaussian proposal and callback log-ratio subtraction. Clamping at zero
is nonexpansive, and Lean proves `exp` is one-Lipschitz on the resulting
nonpositive domain, yielding a complete acceptance-threshold budget.

The accept/reject comparison is proved stable whenever its ideal margin
exceeds the combined uniform and threshold errors. Conversely, any changed
branch is proved to lie inside exactly that error band. Under stability, the
returned value approximates the ideal command-interpreter result by the error
of the selected proposal/current branch. Concrete Julia `Float64`, libm,
callback, and RNG error certificates remain explicit external obligations.

## 2026-08-15: executable scalar HMC vertical slice

Extended the sampler artifact to version 3 with scalar, unit-mass,
endpoint-corrected HMC using one leapfrog step. The Lean command interpreter
has a complete ideal trace theorem. Its position/momentum formulas are proved
equal to the existing leapfrog map; the corresponding flipped endpoint
proposal is involutive and phase-volume preserving, and its exact Metropolis
kernel preserves the Boltzmann phase target.

Julia Reference interprets the new program while Optimized independently
implements it. Activated energy, reversibility, finite-difference volume,
deterministic differential, and standard-normal moment tests. The artifact
loader now enforces canonical S-expression round trips and runtime input-kind
checks. Cross-language Float64/RNG refinement and vector/multistep HMC remain
future extensions.

## 2026-08-15: Documenter site and Lean-owned architecture graphs

Added a Documenter.jl site that publishes the existing canonical Markdown
notes as a navigable GitHub Pages site. The root Makefile can build the site
locally, and a GitHub Actions workflow checks and deploys it from `main`.

Added typed documentation-graph data under `Mcmc.Docs` and a Lean executable
that emits the committed Mermaid page. The initial generated diagrams cover
the formalization dependency layers and the executable assurance chain. Edge
labels distinguish proved refinement, generated artifacts, differential-test
evidence, and the explicitly deferred floating-point refinement obligation.

## 2026-08-15: generic scalar Gaussian RWMH refinement

Generalized the canonical continuous command trace theorem to arbitrary real
log densities and proposal scales. For measurable log densities and positive
scales, Lean now connects the scaled standard-normal proposal and exponential
log-ratio threshold to the existing verified Gaussian RWMH kernel, proves exact
kernel equality, and inherits invariance of the `exp ∘ logDensity` target.
Explicit normalization packages the target as a stationary probability
measure.

Added `NumericalRefinement`, an explicit backend contract for values,
callbacks, sources, and step results. The repository deliberately supplies no
Julia/Float64 witness; this records rather than discharges the future numerical
refinement obligation.

## 2026-08-15: sampler-wide IR artifact naming

Renamed the mixed finite/continuous artifact from `Reference/Finite.ir` to
`Reference/Samplers.ir` and moved its versioned serializer from the finite
namespace to `Mcmc.Executable.IRFormat`. Format version 2 and the serialized
program data are unchanged.

## 2026-08-15: continuous RWMH enters the interpreted sampler artifact

Extended the sampler artifact to version 2 with an inspectable scalar Gaussian
RWMH program. Julia Reference interprets its Float64 expressions and explicit
normal/uniform commands; public `GaussianRWMH` steps now use Reference while
Optimized remains an independent differential-test target.

The named-variable command interpreter is deterministic and uses a
syntax-derived fuel bound. Its Lean trace theorem proves the full proposed or
retained result for valid normal/uniform traces at the exact standard-Gaussian
specialization.

At the exact layer, proved that the complete ideal standard-Gaussian RWMH
program measure equals the existing verified density-based RWMH kernel row.
The Julia trace comparisons and moment test remain implementation evidence:
callbacks, Float64 arithmetic and `exp`, `randn`, and `rand` are explicit trust
boundaries pending a separate numerical refinement proof.

## 2026-08-14: interpreted reference artifact replaces generated Julia code

Made the finite command IR an executable cross-language artifact. Lean now has
a deterministic command interpreter, emits a versioned S-expression
`Reference/Samplers.ir`, and builds the conformance oracle on the IR interpreter.
Julia's maintained `VerifiedSamplers.Reference` module parses and interprets
that data using the shared `draw_below!` runtime contract. The public finite
API and exhaustive tests now compare this interpreted reference with the
independent optimized implementation.

Removed the generated Julia algorithm module, restricted Julia AST, printer,
and source generator after the interpreted path passed the complete finite
suite. Universal Lean theorems now connect the command interpreter to the
older categorical and generic MH replay definitions for every valid finite
configuration and trace. Serialization, Julia interpretation, and concrete
RNG execution remain explicit cross-language trust boundaries. Continuous
primitives retain exact mathlib `Measure` denotations while `Float64` and RNG
behavior remain a separate refinement problem.

## 2026-08-14: finite generation moved to typed compiler IR

Replaced the algorithm-sized Julia source template with typed finite entry
descriptors, a backend-neutral typed command IR, and structural lowering to a
restricted Julia AST. The IR now contains the cumulative categorical selector
and generic finite MH validation/proposal/accept/reject control flow; Julia's
one-based indexing is confined to the backend. The AST has no raw-source
escape constructor and validates its identifier, type, and import allowlists
before deterministic printing.

The entry descriptors are explicitly anchored to the existing exact
categorical and generic finite-MH PMF theorems. Compiler semantic preservation
from command IR through emitted Julia remains a future theorem, so exhaustive
Lean/generated/optimized trace tests continue to guard that boundary.
Recorded the follow-up migration: add a command-IR trace interpreter, prove it
equal to the older replay functions, then make that interpreter canonical and
deprecate the duplicate replay algorithms. The same interpreter/denotation
pattern extends to continuous measure semantics, while concrete `Float64` and
RNG behavior remains a separate refinement boundary.

## 2026-08-14: continuous executable primitive boundary

Added result-typed ideal sampler primitives for positive bounded naturals,
the standard normal, and the unit uniform. Their Lean denotations are
probability measures, and the standard-normal denotation is proved equal to
the exact mathlib Gaussian density measure used by the existing general-state
RWMH theory. Added kind-tagged mathematical trace replay with explicit
exhaustion, mismatch, and range failures.

Added a separately labeled one-dimensional Float64 Gaussian RWMH
implementation to Julia, including positional-RNG sampling, typed normal and
uniform replay events, deterministic accept/reject checks, and a normal-target
moment test. This is a tested optimized implementation, not generated code or
a proof of floating-point equivalence. The remaining continuous milestone is
the compositional first-order sampler IR and its ideal RWMH refinement theorem,
followed by an explicit Julia numeric/RNG contract.

## 2026-08-14: typed sampler IR and Gaussian proposal refinement

Added an intrinsically typed first-order sampler IR. Typed de Bruijn variables
make `let` and stochastic bind inspectable syntax rather than embedded Lean
continuations. Pure expressions, exact mathlib-kernel semantics, and
deterministic kind-tagged trace replay share the same program, and Lean proves
that every program interpretation is a Markov kernel.

Implemented the scalar ideal standard-Gaussian proposal program and proved
that it replays as addition, denotes `gaussianReal current 1`, and equals the
proposal row used by the existing density-based RWMH construction. Added the
continuous executable contract separating exact measures, ideal-real replay,
and Julia Float64/RNG assumptions. The complete IR step and its trace theorem
are now implemented, its real threshold is proved pointwise equal to the
existing zero-safe density acceptance, and the unit-uniform accept/reject
integral is proved exactly. The remaining theorem boundary is their final
composition into equality with the existing verified RWMH kernel.

## 2026-08-14: generic executable finite MH

Generalized the exact proposal/accept/reject PMF from the two-state fixture to
arbitrary `Fin n`. Lean now proves row-PMF equality with the existing finite
MH kernel for every strictly positive natural-weight target and every
positive-total natural proposal row, including asymmetric and zero proposal
edges. The diagonal case is derived from normalization after proving every
off-diagonal mass algebraically.

Generalized the emitted and optimized Julia cores, compiled Lean oracle, and
public API. `FiniteKernelWeights` validates square nonnegative proposal
matrices with positive row totals; `FiniteMH` exposes positional-RNG `step` and
`sample` methods. An asymmetric three-state example with zero edges is
exhaustively enumerated and compared across exact rational expectations, the
Lean oracle, generated Julia, and optimized Julia.

## 2026-08-14: differential and statistical Julia test layers

Added a maintained optimized finite implementation using cumulative sums and
binary search, while retaining the generated linear-scan core as the public
execution path. Exhaustive trace tests now compare the compiled Lean oracle,
generated Julia, and optimized Julia, including their random-bound requests.
Added exact rational transition checks, direct detailed-balance and
stationarity regressions, categorical chi-squared and per-category frequency
diagnostics, two-state batch-means moment checks, and runtime unit tests.
Named skipped skeletons record the future integrator, Geweke, DHMC,
adaptation, robustness, and performance test surface.

## 2026-08-14: finite executable MVP completed

Completed the exact two-state vertical slice. The cumulative selector now has
a universal PMF theorem: a uniform draw below the total produces each `Fin n`
atom with probability equal to its normalized natural weight, including zero
weights. Added exact integer proposal/accept/reject execution and proved the
two-state step PMF equal to the existing verified finite-MH row PMF, so the
existing detailed-balance and invariance results apply without duplication.

Added a compiled Lean conformance oracle, a deterministic Lean emitter, the
`VerifiedSamplers.Generated` Julia core, maintained RNG and trace sources, and
the public positional-RNG methods `sample(rng, ...)` with default-RNG dispatch
fallbacks. Exhaustive tests compare every valid categorical and two-state MH
trace with the Lean oracle. Generation is explicit through `make generate` and
`make check-generated`; Julia installation does not require Lean. General
arbitrary-size executable-MH refinement, compiler correctness, continuous
primitives, and floating-point refinement remain later extensions.

## 2026-08-14: finite executable primitives begin

Implemented the first exact executable layer. Positive-total natural weights
now normalize to a mathlib PMF and are proved equal to the existing finite
distribution embedding. Added the uniform `drawBelow` semantics, a validated
deterministic trace event format with explicit failure modes, and an executable
cumulative categorical selector. Lean proves that every in-range draw selects
an in-range index and that selection succeeds exactly below total mass.
Compiled examples cover zero-weight entries, cumulative boundaries, trace
bound mismatches, and out-of-range draws. The exact PMF law and two-state
finite-MH refinement were subsequently completed in the MVP above.

## 2026-08-14: finite executable milestone planned

Fixed the first executable slice around `Fin n`, positive-total natural
weights, one uniform `drawBelow` primitive, and separate PMF, trace, and Julia
execution semantics. The milestone will prove row-PMF equality between an
executable proposal/accept/reject program and the existing finite MH kernel,
then emit and exhaustively test the two-state reference implementation. The
roadmap keeps integer overflow, Julia runtime behavior, and emitter correctness
as explicit boundaries rather than folding them into the Lean theorem. The
earlier standalone Julia proposal has been consolidated into the architecture
and finite roadmap so scope, component ownership, and implementation order have
single canonical homes.

## 2026-08-14: verified-samplers repository skeleton

Reorganized the project around a language-neutral repository boundary. The
Lean project now lives under `formal/`, and its public module and namespace are
renamed from `McmcLean` to `Mcmc`. Added the `VerifiedSamplers.jl` package with
separate internal `Reference` and `Optimized` submodules. The former is the
future explicit destination of compiler-emitted code; ordinary builds and
package installation will not rewrite it. Added root Make targets for formal
and Julia validation plus documented generation placeholders.

## 2026-08-14: invariant momentum-transition foundation

Following the factorization emphasized in Neal's HMC review, generalized the
phase-space refresh layer from independent resampling to an arbitrary Markov
momentum transition preserving the momentum target. Full momentum refreshment
is now a specialization of this theorem. This supplies the common foundation
for a future partial Gaussian AR(1) refresh kernel without claiming that the
concrete AR(1) invariance proof is already complete. Added a coverage note
mapping endpoint correction, approximate proposal dynamics, windowed
selection, parameter randomization, and their theorem boundaries.

## 2026-08-14: auxiliary-variable HMC foundation

Added a general measure-theoretic lift--evolve--project kernel and proved that
it preserves a position target whenever the lift produces an extended target,
the extended transition preserves that target, and projection recovers the
position target. A deterministic measure-preserving-map specialization covers
the ideal Hamiltonian-flow construction. A conditional-auxiliary-kernel
corollary automatically discharges the canonical product lift and first
projection equations. The Euclidean multinomial-HMC and both endpoint and
multinomial GR-HMC position-invariance proofs now consume this common result
instead of repeating measure-composition arguments. Added a coverage note mapping
Betancourt's conceptual HMC review to the machine-checked foundation and
separating invariance from unproved ergodic or efficiency claims.

## 2026-08-14: per-paper documentation cleanup

Standardized the paper documentation as `xu21-{coverage,roadmap}.md` and
`xu24-{coverage,roadmap}.md`. The README now gives only headline corrections
and links to the canonical coverage audits. Detailed statement repairs,
obstructions, implications, and theorem references live in the corresponding
coverage file; the related-work note now links there instead of duplicating
the audits.

## 2026-08-14: diagonal SoftAbs kernel closure

Proved joint measurability of the complete diagonal-SoftAbs GR Hamiltonian
from a measurable potential and coordinatewise measurable Hessian diagonal.
The exact factor-volume theorem now yields its measurable normalized momentum
family. New endpoint-Metropolis and multinomial position-kernel theorems prove
invariance of the intended position target for the concrete SoftAbs metric;
their only remaining numerical premise is the explicit generalized-leapfrog
`IsValid` certificate. The coverage audit now removes the previously open
SoftAbs measure-interface obligation.

Strengthened the corrected fixed-point analysis. Under an explicit
`ContractingWith K` hypothesis, both implicit finite loops now converge to
their unique fixed points, with a priori geometric distance bounds after any
number of iterations. Separately, measurable Hamiltonian derivative fields
make each finite loop and the complete finite generalized-leapfrog update
measurable. `FiniteFixedPointIsValid` therefore derives its measurability field
and retains only zero residual, uniqueness, time reversal, and phase-volume
preservation as solver-specific obligations. These results quantify the
paper's approximation practice without incorrectly promoting a fixed count to
an exact integrator.

Closed the removable SoftAbs branch at zero. Lean proves
`x cosh x - sinh x = o(x²)` from the hyperbolic derivative identities and
shows `x sinh x ~ x²`; hence the unit SoftAbs difference quotient tends to
zero. Scaling gives differentiability of `softAbs α` at zero for every
`α>0`, and the existing quotient proof handles all nonzero points.
`diagonalSoftAbsDerivativeData` and
`diagonalSoftAbsMetricEquation12CertificateOfDifferentiable` now turn any
coordinatewise differentiable Hessian diagonal into the complete Equation
(12) certificate with no nonzero-eigenvalue assumption.

## 2026-08-14: relativistic Riemannian HMC formalization begins

Added the Xu and Ge 2024 roadmap and began its lowest algebraic layer.  The
new relativistic module defines special-relativistic mass, kinetic energy, and
velocity and targets the strict speed bound underlying the paper's
Riemannian construction.  The roadmap records two proof boundaries from the
initial paper audit: the printed higher-dimensional momentum sampler uses the
two-dimensional radial Jacobian and independent uniform spherical angles, and
the paper's sampler-validity discussion is informal.  The corrected
formalization will prove the dimension-dependent radial/directional
pushforward and will make generalized-leapfrog solvability, reversibility,
volume preservation, and measurability explicit.

The first radial-momentum layer now uses the dimension-dependent polar
Jacobian `r^(d-1)`.  Lean proves that it reduces to the paper's printed factor
`r` in dimension two and proves a concrete mismatch at radius two in
dimension three.  Mathlib's `Measure.toSphere` and `Measure.volumeIoiPow`
provide the intended foundation for the corrected radial/uniform-direction
measure pushforward.

Added an abstract factored Riemannian layer that keeps the quadratic-form
factor and inverse-metric action distinct.  Lean proves positivity of the
general-relativistic mass and the corrected anisotropic velocity bound
`‖G⁻¹p‖ / (‖Ap‖/c)`.  The paper audit now records that the mass argument and
norm ratio printed after Equation (9) do not follow in general from
`AᵀA = G⁻¹`.  The audit is now machine checked by the anisotropic instance
`A = diag(2,1)`, `G⁻¹ = diag(4,1)`, `p = (1,1)`, for which Lean proves the
corrected ratio is strictly larger than the printed ratio.

The corrected polar sampler is now connected end to end at the unnormalized
measure level.  Using mathlib's Haar sphere measure, `volumeIoiPow (d-1)`, and
the measurable polar synthesis map, Lean proves that the sampler's pushforward
is exactly the Cartesian measure with relativistic Boltzmann density.  This is
the distributional identity missing from the paper's printed
higher-dimensional Algorithm 1.

Added the raw position-dependent factored-metric interface and the complete
nonseparable GR Hamiltonian from Equation (8).  The factor, inverse-metric
action, and log determinant remain separate so their matrix and calculus
compatibility cannot be assumed accidentally.  The full Hamiltonian is proved
invariant under momentum flip, the mass is positive for positive physical
parameters, and the corrected pointwise anisotropic speed bound is lifted to
the position-dependent interface.

Strengthened the factored-metric interface so its quadratic-form factor is a
continuous linear equivalence.  This makes the corrected affine momentum
transport definable without a choice of inverse: the conditional momentum
measure at `q` is the map of the isotropic relativistic measure by
`factor(q)⁻¹`.  The audit records that Algorithm 1's printed `A_qᵀ` transport
is inconsistent with its stated `A_qᵀA_q=G_q⁻¹` convention unless additional
special structure makes transpose and inverse coincide.

Closed the normalization obligation for positive mass and speed parameters.
The relativistic radial energy strictly dominates `c*r`; the resulting
Boltzmann density is bounded by an integrable Gamma tail.  Lean uses this to
prove finite, nonzero Cartesian mass and constructs a normalized
`ProbabilityMeasure`.  Transporting it through `factor(q)⁻¹` gives an actual
position-dependent momentum probability law, and mapping that law forward by
`factor(q)` is proved to recover the normalized isotropic law exactly.

Formalized the generalized implicit-leapfrog equations from the paper and a
selection interface that witnesses an actual solution.  Existence is kept
strictly separate from measurability, uniqueness, momentum-flip time
reversibility, and phase-volume preservation; the later kernel theorem will
consume an explicit certificate containing all four obligations.  Lean also
proves directly from the equations that every selected implementation is the
identity at zero step size.

Added the first concrete metric specialization.  For `A=G⁻¹=I` and zero log
determinant, Lean proves that the GR kinetic energy and velocity reduce exactly
to their special-relativistic forms, the normalized conditional momentum law
is the isotropic relativistic probability, and the momentum family satisfies
the kernel measurability obligation.  The resulting concrete momentum kernel
is a proved mathlib Markov kernel.

Added the generic deterministic Metropolis layer needed for endpoint GR-HMC.
A measurable deterministic map now yields a proposal kernel, a zero-safe
symmetric-minimum acceptance probability, and a completed Markov kernel with
an explicit accept-or-retain row formula.  The accepted-flow multiplication
identity is proved for positive finite target weights.  For every measurable
involutive proposal preserving the reference measure, Lean now proves that
the accepted flow and completed Metropolis kernel are reversible with respect
to the weighted target measure, and hence that the completed kernel preserves
that target.  Applying this theorem to GR-HMC still requires a measurable
generalized-leapfrog endpoint map together with its time-reversal and
phase-volume certificates.

Connected that generic result to generalized leapfrog. Lean derives the
inverse-step identity `step(-ε) (step ε z) = z` from the implicit equations and
their uniqueness, rather than adding it as another unsupported assumption.
The paper's time-reversal condition then makes momentum flip after a step an
involution. Momentum flip is separately proved to preserve finite-dimensional
phase Lebesgue measure, so a valid generalized-leapfrog certificate makes the
whole endpoint proposal volume preserving.

The resulting endpoint-Metropolis GR-HMC kernel is now defined against the
full position-dependent Hamiltonian. Lean proves it is Markov, reversible,
and invariant for the unnormalized GR Boltzmann measure. The result remains
explicitly conditional on existence, uniqueness, measurability, reversal, and
volume preservation of the selected implicit solver.

Added the complete user-facing position transition: it draws from the
position-dependent relativistic momentum kernel, runs endpoint-corrected
GR-HMC in phase space, and projects to position. Lean proves this kernel is
Markov and preserves any position target satisfying an explicit disintegration
compatibility equation with the normalized conditional momentum law. The
equation deliberately exposes the metric determinant/Jacobian obligation;
deriving it for a concrete nonconstant factored metric, multinomial correction,
and concrete nonconstant solver certificates remain to be formalized.

Auditing the identity-metric compatibility proof exposed an internal norm
mismatch: `Momentum ι = ι → ℝ` has mathlib's product/sup norm, whereas the
Hamiltonian's `euclideanNorm` is `L²`. The earlier generic ambient-norm radial
measure was therefore not the Hamiltonian momentum law above dimension one.
The corrected construction now starts on `EuclideanSpace ℝ ι`, uses the proven
polar sampler there, and transports through mathlib's volume-preserving
Euclidean coordinate equivalence. Lean proves the resulting Cartesian density
is exactly the density formed from `euclideanNorm`; all Riemannian momentum
refresh definitions now use this corrected law.

The identity-metric compatibility equation is now proved completely. The GR
phase measure factors into the ordinary position Boltzmann measure and the
unnormalized corrected relativistic momentum measure. After accounting for
the momentum partition function, the normalized refresh law reconstructs that
phase measure. Consequently Lean proves the full identity-metric position
endpoint GR-HMC kernel preserves its position target, conditional only on the
explicit generalized-leapfrog validity certificate.

The general metric determinant obligation is now isolated as
`HasCompatibleFactorVolume`, an exact statement about Lebesgue measure under
the inverse factor. Lean proves that this certificate identifies the
transported conditional momentum measure with the full Riemannian kinetic
density, including its log-determinant term. A position-dependent scalar-factor
metric satisfies the certificate, so this is no longer only a constant-metric
test. The final kernel-level reconstruction is not yet derived automatically
from this certificate; the general position-invariance theorem still takes
its explicit compatibility equation as a hypothesis.

Added the multinomial GR-HMC correction. A generic orbit theorem proves that
uniform random re-rooting followed by positive finite weighted index selection
along a measurable measure-preserving permutation is a Markov kernel reversible
for the corresponding weighted base measure. A uniquely selected generalized-
leapfrog step instantiates the permutation, with its negative step as inverse.
Consequently the multinomial GR phase kernel is reversible and invariant, and
its momentum-refresh/projected position kernel preserves every explicitly
compatible position target. The identity metric supplies a concrete end-to-end
position-invariance instance. These results remain conditional on the selected
implicit solver's validity certificate, not merely on its equations.

Completed `docs/xu24-coverage.md`, an equation-by-equation and algorithm-level
audit against the published ICML paper. It records machine-checked,
conditional, corrected, and implementation-only items separately. In
particular, Equation (9) also has a derivative-variable typo (`∇q H` where
Hamiltonian velocity is `∇p H`), Algorithm 1 has three independent general-
dimension/transport defects, and Section 5.2's symmetry argument omits the
conditional-law disintegration and numerical-map obligations. Equations
(12)--(13), a concrete SoftAbs metric and derivative implementation, and an
exactly certified finite-iteration implicit solver remain outside the current
executable instance. Experimental stability and ESS results are not promoted
to universal theorems.

Closed the general metric-to-kernel compatibility gap. Lean now proves the
normalized conditional momentum density row by row, derives kernel
measurability from the joint density, and reconstructs the GR phase target from
the scaled position target and refresh kernel. The position-dependent scalar
factor consequently has full endpoint and multinomial position-invariance
theorems. Its Hamiltonian measurability is derived from measurable potential
and positive measurable scale fields, leaving only the explicit generalized-
leapfrog validity certificate as the numerical premise.

Formalized Equation (13) as a genuine Fréchet-derivative identity. The
special-relativistic kinetic derivative is first proved directionally and
then lifted to `fderiv`; composition with the position-fixed metric factor
gives the GR momentum derivative `G⁻¹p/M`. The theorem requires the precise
bilinear compatibility condition `⟪A x, A y⟫ = ⟪G⁻¹x, y⟫`, exposing rather
than hiding the paper's `AᵀA = G⁻¹` obligation. This isolated Equation (12),
which additionally requires derivatives of the position-dependent metric
data, as the next calculus obligation.

Formalized Equation (12) in directional Fréchet-derivative form. A new
`Equation12Certificate` records the precise matrix-calculus obligations:
the derivative of `pᵀG⁻¹p` is
`-pᵀG⁻¹(dG)G⁻¹p`, and the derivative of `log det G` is
`tr(G⁻¹dG)`. Lean derives both the published inverse-mass/trace kinetic
formula and the complete Hamiltonian position derivative from this
certificate. Thus Equations (12)--(13) are no longer open abstract calculus
claims; the remaining implementation task is to construct the certificate
for the paper's concrete SoftAbs or diagonal-SoftAbs metric.

Added the paper's diagonal SoftAbs metric from Section 5.4. The scalar
transform is defined as `x / tanh(αx)` away from zero and by its limiting
value `1/α` at zero; Lean proves it is strictly positive for `α>0`. The
resulting diagonal metric has inverse-square-root factor, inverse action, and
log determinant, and Lean proves `AᵀA=G⁻¹` and specializes Equation (13) to
it. Lean also proves exact factor-volume compatibility: mathlib's determinant
change-of-variables theorem reduces the inverse-factor Jacobian to the product
of positive square-root eigenvalues, which is shown equal to the exponential
of half the stored log determinant. Its Equation (12) certificate still
depends on differentiability of the supplied Hessian diagonal.

Closed the matrix-calculus part of that remaining Equation (12) obligation.
`DiagonalEigenvalueDerivativeData` records coordinatewise Fréchet derivatives
of the positive diagonal eigenvalues. Lean automatically constructs
`Equation12Certificate`, proving both the derivative of the inverse quadratic
form and the derivative of the log determinant as the required trace. Thus a
concrete target now only needs to differentiate its Hessian diagonal through
the scalar SoftAbs transform; smoothness at a zero Hessian entry remains an
explicit analytic boundary.

Proved the SoftAbs chain rule away from zero. Real `tanh` is differentiable,
the quotient branch is differentiable for `α>0` and a nonzero input, and
`diagonalSoftAbsDerivativeDataOfNonzero` now turns any differentiable Hessian
diagonal with nonzero entries at the current position into the complete
Equation (12) certificate. Only the removable zero-eigenvalue branch remains
outside this scalar calculus layer.

Formalized the practical finite fixed-point loops used for generalized
leapfrog. `finiteFixedPointGeneralizedLeapfrog_satisfies_iff` proves that the
returned transition satisfies Equations (6)--(7) exactly iff the last values
of both loops are genuine fixed points. A one-dimensional compiled
counterexample uses the experimental count `n=6`: the half-momentum iteration
alternates between zero and one, so its sixth value is not fixed and the full
update does not satisfy the generalized-leapfrog equations. Consequently the
paper's finite iteration count cannot justify exact reversibility or volume
preservation without further assumptions, convergence-to-tolerance analysis,
or an additional correction mechanism.

Added the corrected finite-solver interface. `FiniteFixedPointIsExact`
requires both implicit residuals to vanish; only then does
`finiteFixedPointSelection` construct a genuine generalized-leapfrog
selection. `FiniteFixedPointIsValid` additionally requires measurability,
uniqueness, time reversal, and volume preservation. The six-step example
proves that even the first, zero-residual premise fails in general.

This file records completed milestones, current limitations, and likely next
steps. It is descriptive rather than a promise about release dates.

## Next steps

1. Extend the complete finite-dimensional standard-Gaussian Theorem 4.1
   instance to broader step counts and target classes under explicit drift
   hypotheses.
2. Instantiate an applied target such as logistic regression under explicit
   coercivity and moment assumptions.
3. Formalize the unbiased-estimator expectation, variance, and expected-cost
   consequences after the geometric meeting-tail theorem.
