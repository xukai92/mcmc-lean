# Development log

Entries through the earlier 2026-08-13 work are preserved in the
[development-log archive](development-log-archive.md).

## 2026-08-15: next-phase solver, particle-count boundary, and composable inference

Added the exact Banach-fixed-point construction missing from the generalized
leapfrog layer. `ContractiveGeneralizedLeapfrogSolver` consumes contraction
certificates for both implicit equations, constructs an exact selected solve,
proves uniqueness, and connects the practical finite loops to that solve by
convergence theorems. The Julia Reference and Optimized layers now provide a
position-dependent fixed-point implementation with measured residual
certificates and differential tests. Positive residuals remain approximation
data and are still rejected by the exact GR-HMC client.

Strengthened the particle-Gibbs boundary in both directions. Recursive
forced-lineage PG remains exact for supported positive paths, while Lean now
proves that one-particle PG is exactly the identity kernel. Therefore no
particle-count-uniform convergence claim follows from stationarity. Added
Reference, Optimized, and public Julia execution for exact-integer bootstrap
particle Gibbs on finite hidden Markov models, including deterministic replay,
one-particle, validation, and symmetric-model frequency tests.

Audited Ge, Xu, and Ghahramani (2018) and added scoped composable inference
operators. Arbitrary finite schedules of common-target-stationary full-state
kernels preserve the target even when declared variable scopes overlap. A
two-block PG--HMC theorem formalizes the paper's central composition pattern;
coverage of all declared variables remains a separate configuration property.

Added the quantitative special case that can be established without hidden
mixing assumptions: zero-horizon particle Gibbs is exactly
`N⁻¹ I + (1-N⁻¹) Π`, so its total-variation error contracts by exactly `N⁻¹`
per iteration and tends to zero for `N ≥ 2`. The Julia finite-HMM test mirrors
this formula empirically.

Corrected the contraction API for genuinely implicit dynamics by adding a
fixed-step solver certificate. A concrete nonseparable bilinear Hamiltonian
now has machine-checked contraction of both implicit equations under
`|εa/2| < 1`, exact fixed-point solutions, and uniqueness. Added finite
probabilistic-program `assume`/`observe` factor semantics with normalized
posterior, plus a stationary static candidate-mixture theorem. Dynamic NUTS
stopping and coroutine refinement remain explicitly outside those theorems.

Added a stronger smooth momentum-even solver model
`H(q,p) = a q √(1+p²)`. Lean checks the two supplied derivatives against this
Hamiltonian, proves their parity, proves global contraction of both implicit
maps under `|εa/2| < 1`, and derives exact uniqueness, convergence of both
finite iterations, measurability, and momentum-flip time reversal. Julia now
tests the same callbacks for residual convergence, reversal, and an empirical
finite-difference unit Jacobian. The Jacobian test is not promoted to a Lean
phase-volume theorem. Instead, Lean now proves the exact analytic boundary:
opposite-step uniqueness makes the selected step bijective, and a
differentiability plus unit-absolute-determinant certificate promotes it to a
product-phase-volume-preserving map by Mathlib's additive-Haar
change-of-variables theorem. The concrete Jacobian certificate itself remains
to be proved; no numerical finite-difference result is used as its witness.

Closed the phase-volume obligation completely for the bilinear implicit stress
model. Its Banach-selected solve is proved equal to reciprocal scalar
position/momentum dilations, and the exact Haar scaling formula proves product
phase-volume preservation in every finite dimension. This is a genuine
nonzero-step implicit-solver theorem, but the bilinear Hamiltonian is not
momentum-even and is not presented as a GR target; the smooth momentum-even
relativistic-shaped model retains its explicit Jacobian-certificate boundary.

Made the nonconstant metric endpoint fully concrete. The canonical scalar
factor `quadraticScalarScale(q) = 1 + ‖q‖²` is machine-checked globally
positive and demonstrably nonconstant in one dimension. Its associated
factored Riemannian metric satisfies the exact inverse-factor Haar/Jacobian
identity, and every measurable potential produces a measurable complete GR
Hamiltonian. The remaining solver task is now the derivative and contraction
analysis for this concrete Hamiltonian, rather than construction of a valid
positive metric field.

Completed the calculus side of that link in one dimension. Lean now constructs
the covariant metric-variation map for `1 + ‖q‖²`, proves the quadratic-form
and log-determinant derivative identities required by the Equation (12)
certificate, proves `AᵀA = G⁻¹`, and instantiates both paper Equations (12) and
(13) for the complete GR Hamiltonian. The resulting
`quadraticScalarGRPositionDerivative` and
`quadraticScalarGRMomentumDerivative` are exact Fréchet-derivative callbacks.
The remaining analytic task is proving the fixed-point contraction and
phase-volume certificate for a useful nonzero step size.

Closed the contraction endpoint with a bounded nonconstant metric client.
For `scale(q) = 2 + sin(q)` and potential `log(scale(q))`, the complete GR
Hamiltonian is exactly `sqrt(1 + (scale(q)p)^2)`. Lean proves the implemented
callbacks are its derivatives, establishes global relativistic-profile
Lipschitz bounds, and proves both implicit maps contract for `3|ε|/2 < 1`.
The exact Banach solve is unique, measurable, the limit of both finite loops,
and momentum-flip reversible. Reference and Optimized Julia implementations
agree on these callbacks and pass residual and reversal tests. Its remaining
formal endpoint is the isolated differentiability/unit-Jacobian certificate;
opposite-step uniqueness already supplies bijectivity.

Advanced that endpoint by proving the exact mixed-partial identity for the
bounded callbacks. Lean differentiates the position force with respect to
momentum and the velocity with respect to position, proves the resulting
expressions equal, and records the scalar generalized-leapfrog determinant
cancellation. Thus the unit-Jacobian proof is reduced to differentiability of
the globally selected implicit inverse maps; the algebraic symplectic
cancellation itself is no longer assumed.

## 2026-08-15: adaptive convergence, exact slice disintegration, and Euclidean RJ

Completed the finite Roberts--Rosenthal argument. An anchored augmented process
compares the actual adaptive window with the kernel frozen at its beginning.
Lean proves the exact row-TV comparison, bounds accumulated anchor variation
from the Diminishing Adaptation change probability, and combines the resulting
finite-window estimate with Containment. The public theorem concludes
total-variation convergence of deterministic state-marginal laws; it does not
claim almost-sure path convergence, an LLN, a CLT, or a uniform rate.

For general-state slice sampling, the finite under-the-graph measure is now
disintegrated in height--state order on a nonempty standard Borel state space.
The resulting measurable horizontal Markov kernel reconstructs the joint law,
so the fully constructed exact slice sampler preserves the weighted target.
No irreducibility or convergence theorem is inferred from invariance.

Added a nontrivial reversible-jump client between a zero-dimensional `Unit`
model and a scalar real model. The birth move transports a uniform auxiliary
variable by `y = 2u`; Lean proves its pushforward has density `1/4` on
`(-2,2]`, thereby checking the inverse-Jacobian factor, and proves invariance
of the resulting birth/death RJ-MH kernel.

## 2026-08-15: random adaptive state-marginal dynamics

Defined state and parameter marginals of finite augmented laws and the exact
next-state mixture obtained by averaging the currently selected kernel row over
the augmented law. Lean proves that evolving the augmented process and then
summing out the updated parameter gives exactly this mixture; the parameter
update cannot alter the same-step state marginal.

Defined the adaptive state law at every time and proved its successor identity.
The total-variation distance of the next state law from a target is bounded by
the current augmented-law average of the selected row's distance to that
target. This supplies the explicit marginal object for the eventual adaptive
convergence theorem, but does not itself show that the bound vanishes.

## 2026-08-15: adaptive finite-window TV estimates

Proved symmetry and the triangle inequality for finite distribution total
variation. Lean now verifies the two analytic estimates underlying adaptive
finite-window comparisons: applying a common Markov kernel contracts TV, and
changing the kernel for a fixed input law costs at most the law-weighted row
TV, hence at most any uniform row-TV bound.

By induction, laws driven from the same initial distribution by two
predetermined kernel schedules differ after any finite horizon by at most the
sum of their per-step uniform kernel distances. This is the deterministic
telescoping core of the Roberts--Rosenthal proof. It is not yet the random
adaptive convergence theorem: Diminishing Adaptation and Containment still
must control the good finite-window event and its complement.

## 2026-08-15: finite adaptive Containment

Added point-mass distributions, homogeneous finite-kernel iteration, and
finite distribution total variation with its `[0,1]` bounds. Defined uniform
mixing by a fixed horizon for a target distribution.

For the random adaptive process, defined the probability that the kernel
selected at time `n`, started from the current chain state, remains farther
than a TV tolerance from the target after a proposed horizon. Lean proves this
failure probability lies in `[0,1]`. Containment is then stated as boundedness
in probability of the required horizon along the actual augmented process.

Simultaneous uniform mixing of all parameter-indexed kernels is proved to imply
Containment for every initial augmented law. Diminishing Adaptation plus
Containment is not yet labeled a convergence theorem: the finite-window
coupling argument remains to be formalized.

## 2026-08-15: finite random Diminishing Adaptation semantics

Defined a finite random adaptive process whose current tuning parameter selects
a state kernel and whose conditional update samples the next parameter after
the next state is observed. The resulting transition on `(state, parameter)` is
proved to be a Markov kernel, giving an explicit evolving augmented law rather
than treating adaptation as an opaque kernel sequence.

Defined the probability that successive selected kernels differ by more than a
given finite row-TV threshold and proved it lies in `[0,1]`. Diminishing
Adaptation is formalized as convergence of this change probability to zero
under the actual process law. If all parameters select the same frozen state
kernel, arbitrary random parameter updates are proved diminishing.

This is a finite Markovian convergence-in-probability definition, not an
adaptive convergence theorem. Mixing times, Containment, and the
Roberts--Rosenthal finite-window argument remain future layers; finite tuning
parameters encode only fixed finite memory unless the augmented state is
enlarged.

## 2026-08-15: predetermined nonhomogeneous adaptive foundation

Defined evolution through finite and time-indexed predetermined kernel
schedules. Lean proves that a common stationary target remains the law after
every finite prefix when the chain starts at that target. This positive theorem
is intentionally contrasted with the existing state-dependent-selection
counterexample: predetermined scheduling is not adaptive selection from the
current chain state.

Added finite row total-variation distance, including nonnegativity, symmetry,
the unit upper bound, and uniform kernel-distance predicates. Defined a
deterministic diminishing-schedule condition and proved every frozen schedule
satisfies it. Roberts--Rosenthal diminishing adaptation for a random
history-dependent process, mixing times, containment, and convergence remain
future theorems; none follows from common invariance or deterministic
diminishing alone.

## 2026-08-15: fully state-indexed finite PMMH

Transported each parameter-specific SMC history and selected terminal index
across the canonical equal-horizon history equivalence into one common PMMH
auxiliary-state type. The initial law, every potential, and every transition
kernel may now depend on the proposed parameter; only the finite schedule
length is shared.

Lean proves that the transported estimator is nonnegative and unit mean, that
the resulting PMMH extended target is stationary, and that its parameter
marginal is exactly the requested target. It also proves the target-weighted
joint parameter/selected-trajectory expectation against each parameter's own
Feynman--Kac model. A concrete Boolean example uses different potential and
transition kernels at its two parameter values. These are stationarity and
exact-marginal results, not chain-convergence or particle-efficiency results.
At that checkpoint, conditional SMC and particle Gibbs remained separate.

## 2026-08-15: conditional-SMC specification and particle-Gibbs kernel

Added a reusable finite conditional-fiber refresh kernel with a total identity
fallback on zero-mass fibers and proved that it preserves its source
distribution. Instantiated it on the selected-trajectory statistic of the SMC
extended target, obtaining a normalized conditional-history law, retained-path
compatibility, and the exact marginal-times-conditional factorization.

Composing that conditional refresh with uniform terminal-index reselection
gives a finite particle-Gibbs kernel with machine-checked extended-target
stationarity and exact normalized Feynman--Kac path marginal. A separate
forced-coordinate population law and recursive forced-lineage generator were
then defined and normalized compositionally. At that checkpoint, the remaining
M1 obligation was pointwise equivalence between that concrete generator and the
exact conditional specification. No chain-convergence or particle-efficiency
claim is made.

The remaining equivalence is now closed. Lean proves the recursive suffix mass
formula, the normalized Feynman--Kac trajectory marginal, equality of the full
forced-lineage law with the conditional selected-particle law on every positive
supported path, and row-level agreement with the stationary conditional-SMC
kernel. This completes the finite conditional-SMC and particle-Gibbs Phase I
milestones without adding a convergence or particle-efficiency claim.

The Phase I core release audit then passed end to end: `lake build` completed
all 3901 jobs; the Julia package tests passed (with only the intentionally
marked future tests broken/skipped); generated IR and generated documentation
matched byte-for-byte; Documenter built successfully; `git diff --check`
passed; and the changed Lean sources contain no `sorry`, `admit`, or `axiom`.
See [the evidence table](core-release-audit.md) for the milestone boundaries.

## 2026-08-15: corrected executable relativistic constant-metric client

Added generated IR version 10 and Julia Reference/Optimized implementations of
a diagonal constant-metric relativistic multinomial HMC client. Momentum uses
the dimension-correct `r^(d-1)` radial law via a Gamma rejection proposal,
Gaussian-normalized uniform spherical direction, and the corrected inverse
factor transport. Differential replay and public sampling tests pass.

This is a working constant-metric specialization, not yet the full
position-dependent Xu--Ge implementation. The latter still requires a valid
implicit generalized-leapfrog solver. Backend residual certificates explicitly
accept a solver as exact only at zero certified residual budget together with
separate uniqueness, reversibility, and volume-preservation witnesses; a small
positive tolerance remains an approximation claim.

## 2026-08-15: finite PMMH stationary exactness

Packaged a complete SMC history and selected terminal index as the auxiliary
state of a unit-mean pseudo-marginal estimator, allowing the initial particle
law to depend on the proposed parameter while sharing a finite step schedule.
Defined the resulting particle marginal Metropolis--Hastings kernel.

Lean proves extended-target stationarity and the exact requested parameter
marginal. It also proves that each parameter slice of the extended target is
the parameter mass times its history-weighted selected-particle target. Hence
every joint parameter/selected-path observable has the target-weighted exact
normalized Feynman--Kac expectation. This entry records the initial
shared-schedule result; it was subsequently generalized above. No convergence
or efficiency result is claimed.

## 2026-08-15: full path many-to-one theorem and finite PIMH

Generalized the one-transition SMC identity to ancestors carrying arbitrary
labels. This permits labels to be complete path prefixes: resampling inherits
the selected ancestor's prefix and propagation appends the child state. Lean
proves by induction over every finite schedule that the explicit-history
expectation of any terminal label observable equals the exact one-particle
Feynman--Kac value. Averaging the iid initial cloud gives the full many-to-one
path theorem.

Forward-propagated singleton prefixes are proved equal to the earlier
backward-traced selected genealogy. Weighting the history law by its normalizing
estimate and selecting a terminal index therefore gives the exact normalized
Feynman--Kac expectation for every observable of the complete path.

Defined finite PIMH as independence Metropolis--Hastings proposing a fresh SMC
history and terminal index and targeting this history-weighted distribution.
Lean proves extended-target stationarity and exact stationary selected-path
expectations. No irreducibility, convergence-from-arbitrary-start, mixing-rate,
or particle-efficiency claim is made; PMMH and particle Gibbs remain future
clients.

## 2026-08-15: one-transition SMC many-to-one identity

Proved a conditional propagation identity for arbitrary observables of a
resampled ancestor and its propagated child. Combining it with multinomial
resampling and empirical-potential normalization shows that the average
potential cancels the resampling denominator and recovers the exact empirical
Feynman--Kac parent--child expectation. Averaging an iid initial cloud gives the
corresponding exact one-particle pair expectation.

This is the one-transition many-to-one base case for the selected genealogy.
It is stronger than terminal-only correctness but not yet the arbitrary-horizon
path law: recursively threading prefix-dependent observables through later
ancestor maps remains the next theorem. No PIMH or convergence claim is made.

## 2026-08-15: selected ancestry extraction

Added recursive backward-index tracing through every stored multinomial
ancestor map and extracted the corresponding full state genealogy for a
selected terminal particle. Lean proves that the path has exactly one more
state than the number of SMC transitions, starts at the computed initial
ancestor, and ends at the previously verified selected terminal state. The
exact terminal expectation is restated directly through this path endpoint.

This closes the data-structure and endpoint layer but not the full PIMH path
law. The next mathematical obligation is a many-to-one identity for arbitrary
observables of the entire selected genealogy. The existing terminal-observable
identity is strictly weaker and is not presented as trajectory exactness or
chain convergence.

## 2026-08-15: selected-particle Feynman--Kac marginal

Added terminal-population extraction from explicit SMC histories and proved
that every concrete history value factors into its normalizing weight times a
terminal empirical average. Defined the normalized extended target obtained by
weighting the SMC history law with its normalizing estimate and selecting a
terminal particle uniformly.

Lean proves that every observable of the selected terminal state has exactly
the normalized one-particle Feynman--Kac expectation; a singleton-event theorem
states the marginal mass directly. This is the selected-terminal exactness
lemma beneath particle MCMC. It is not yet the full ancestral-trajectory target
used by PIMH/PMMH, and it makes no chain-convergence claim.

## 2026-08-15: state-indexed finite SMC schedules

Generalized the explicit-history pseudo-marginal client so the initial law and
every potential and transition kernel may depend on the proposed state at a
shared finite horizon. Histories for equal-length schedules are connected by a
canonical equivalence; the state-dependent history law and weight are relabeled
through that equivalence into one common finite estimator-state type.

The transported normalizing weight remains nonnegative and unit mean. Lean
therefore proves exact extended-target stationarity and the requested state
marginal for the resulting state-indexed SMC pseudo-marginal kernel. A retained
latent trajectory and the specific PIMH/PMMH extended targets remain future
work; no chain-convergence or particle-efficiency claim is made.

## 2026-08-15: explicit finite SMC histories and pseudo-marginal client

Added a recursively typed finite history containing every multinomial ancestor
map and propagated population. Its conditional continuation law and complete
iid-initialized history law are normalized distributions. Lean proves that the
expectation of the concrete product of empirical average potentials and a
terminal empirical observable equals the previously established exact
one-particle Feynman--Kac expectation.

For a shared finite step schedule and state-indexed initial laws with positive
normalizing constants, the normalized history weight is now packaged as a
nonnegative unit-mean pseudo-marginal estimator. The resulting MH kernel has
machine-checked extended-target stationarity and exact requested state
marginal. This is an explicit-history SMC pseudo-marginal client, not yet full
PIMH or PMMH: state-indexed schedules, selected latent trajectories, and their
extended targets remain separate.

## 2026-08-15: finite-horizon homogeneous SMC identity

Defined normalized empirical potential weights for strictly positive finite
potentials and proved the weighted resample--propagate identity: the current
average potential cancels the resampling normalizer exactly. Defined matching
one-particle and particle Feynman--Kac transforms and proved by induction that
their iterates agree on empirical averages for every finite horizon. Averaging
an iid initial cloud therefore yields exactly the corresponding one-particle
Feynman--Kac expectation.

This is the finite-horizon normalizing-estimator theorem (take the terminal
observable to be one), expressed through nested conditional expectations. A
list-indexed extension proves the same identity for time-varying potentials and
transition kernels. It does not yet package explicit ancestry as a finite
estimator state, nor prove particle-filter convergence or efficiency.

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

The bounded position-dependent solver now has continuous exact selections.
A reusable parameter-dependent Banach theorem proves that the unique fixed
point of a jointly continuous uniformly contractive family varies
continuously with its parameters. The bounded `2 + sin(q)` client instantiates
this theorem for its implicit half-momentum and next-position solves and for
the assembled generalized-leapfrog step. Together with the already proved
mixed-partial identity and scalar determinant cancellation, four explicit
triangular maps and their checked solver identities isolate the remaining
phase-volume obligation to the differentiability upgrade supplied by the
inverse-function theorem.

Added a concrete nonidentity client for Ge et al.'s two-block composition.
The new symmetric `preservesSndSlices_product` lemma complements the existing
first-coordinate result, and the compiled example composes independent
conditional refreshes of the latent and continuous-role finite blocks. This
checks that the abstract PG--HMC schedule API is instantiable while explicitly
avoiding the false claim that a finite refresh transition is itself numerical
HMC; the genuine continuous conditional instantiation remains a later bridge.

Packaged the inverse-function step into a reusable theorem:
`differentiable_of_continuous_leftInverse_of_det_fderiv_ne_zero` constructs
the continuous-linear equivalence from the nonzero determinant and proves a
continuous global inverse differentiable. The bounded solver now also exposes
its two callbacks directly on scalar coordinates `ℝ × ℝ`, alongside reusable
differentiability results for the scalar position and scaled-velocity
profiles. This avoids relying on expensive unfolding through `Unit → ℝ` and
sets up the remaining two-by-two determinant calculation.

Closed the differentiability proof for the first implicit generalized-
leapfrog stage. The incoming scalar triangular map now has an explicit
Fréchet derivative matrix and checked determinant formula. The momentum mixed
partial is bounded by three, so the contraction step-size condition makes the
determinant nonzero everywhere. Scalar/`PhaseSpace Unit` equivalences connect
the actual Banach-selected half-momentum solve to a continuous global inverse;
the reusable inverse theorem therefore proves that selected solve
differentiable. The position mixed partial is also bounded by two and its
corresponding diagonal factor is proved nonzero, preparing the symmetric
position-stage argument.

Closed the bounded position-dependent solver's final analytic endpoint. A
second parameterized Banach construction gives a continuous global inverse of
the left position map; its explicit triangular derivative is nonsingular, so
the inverse is differentiable. Lean identifies the complete solver with the
composition of incoming inverse, right map, left inverse, and outgoing map,
computes the derivative determinant of every stage, and uses the mixed-partial
identity to cancel the incoming/right and left/outgoing factors exactly. A
linear equivalence between scalar coordinates and `PhaseSpace Unit` transports
determinant one, and `boundedScalarContractiveSolverAt_volumePreserving`
proves preservation of product phase volume for every `3|ε|/2 < 1`.

Reconciled the active roadmaps after that proof. B2 is now recorded complete
at the exact and certificate-gated runtime levels; remaining Xu--Ge work is
classified as restricted Float64 refinement and a target-specific solver
certificate for the paper-style diagonal SoftAbs client. The executable
roadmap no longer describes the implemented corrected Riemannian runtime as
future construction.

## Next steps

The Gaussian diagonal-SoftAbs client is now end-to-end. Lean connects the
actual Gaussian Hessian to a strictly non-identity SoftAbs metric, packages the
explicit separable update as a valid generalized-leapfrog selection, and
proves endpoint and multinomial GR-HMC position invariance. Julia exposes
`GaussianSoftAbsGRHMC`; the package suite checks seeded reproducibility,
dimension and parameter validation, and finite outputs.

- The general-state composable-inference layer is now machine checked:
  target-preserving kernels carry optional variable-scope metadata, arbitrary
  finite schedules preserve their common `Measure`, and a named PG--HMC
  composition theorem combines an exact auxiliary-variable conditional PG
  update with any invariant HMC update. This is a stationarity result; it does
  not silently claim convergence.
- The finite quantitative foundation now includes an exact Doeblin refresh
  certificate `P = εΠ + (1-ε)R`, its finite-time regenerative identity, a
  uniform `(1-ε)^n` total-variation bound, and convergence for `ε > 0`.
  Positive-horizon particle Gibbs is connected to this theorem on its proper
  fixed-length trajectory state space, obtained by an exact finite
  condition--evolve--project construction. A pointwise minorization now
  automatically constructs the residual kernel and certificate. Concrete
  bounded-potential models must still prove that positive lower bound; the
  theorem does not infer it from stationarity.
  Strict positivity of every finite trajectory-kernel entry is now also a
  directly usable sufficient condition: Lean constructs a conservative
  positive coefficient from the product of all matrix entries and proves TV
  convergence from every initial trajectory law.

1. Instantiate the general-state PG--HMC theorem with a substantive mixed
   discrete/continuous model.
2. Discharge the positive-horizon particle-Gibbs refresh certificate for
   bounded-potential model classes and sharpen its particle-count dependence.
3. Certify a practical diagonal SoftAbs solver and restricted Float64/Julia
   refinement.
4. Extend the Ge, Xu, GR-HMC convergence, dynamic-NUTS, slice, reversible-
   jump, adaptation, particle-asymptotic, and PDMP branches tracked in the
   overall roadmap.

Started the restricted cross-language target milestone. Lean now has a small
scalar expression language with a total ideal-real evaluator, a symbolic
derivative, and machine-checked derivative correctness, differentiability, and
measurability for every expression. `RestrictedTargetCertificate` exposes
input/value/gradient numerical errors rather than hiding callback correctness;
the Gaussian `x²/2` target derives its complete value and derivative bounds from
one input approximation. Julia mirrors the expression tree, evaluates value and
gradient together, rejects non-finite intermediates, and passes Gaussian,
exponential, and overflow tests. Generated-artifact serialization and recursive
primitive rounding/libm certificates remain explicit next obligations.

Closed the first restricted-expression generation gap. A dependency-light
portable AST with rational literals is emitted in version-11 `Samplers.ir`.
Lean proves the canonical Gaussian artifact compiles to the verified `x²/2`
expression, while Julia's public Gaussian expression is decoded from that
artifact rather than copied by hand. The loader distinguishes program and
target declarations and retains its program-only compatibility entry point.

Added recursive restricted-backend refinement. Portable target trees now have
a portable symbolic derivative, proved to compile to the derivative of their
ideal-real expression. A backend supplies certified rational, arithmetic,
negation, and exponential operations; Lean composes their local errors through
both trees and constructs the value/gradient certificate consumed downstream.
The `exp` transport premise remains domain- and backend-specific by design.

Made positive-horizon particle count explicit. The trajectory kernel is now
instantiated with labels `Fin N`; a bounded-potential minorization certificate
uses `N-1` non-retained particles and exposes the coefficient
`((N-1)/(N-1+B))^(T+1)`. Lean proves positivity, strict subunitness, monotonicity
in `N`, construction of the stationary residual kernel, the corresponding
uniform geometric TV bound, and convergence from every initial trajectory law.
The pointwise minorization remains a model-specific conditional-SMC obligation;
it is not inferred from stationarity or from the name “bounded potential.”

Added small-step finite probabilistic-program execution for the Ge et al.
coroutine track. A cursor records the assumed state, accumulated observation
weight, and remaining factors; `resume` consumes one observation and `run`
supports arbitrary pause boundaries. Lean proves the prefix closed form,
equality with completed `traceWeight`, and equivalence of paused/resumed versus
uninterrupted execution. This is the mathematical state-machine refinement;
Julia task copying and source-language lowering remain separate.

Added the finite dynamic-candidate balance core needed before a verified NUTS
tree can be claimed. Candidate membership may depend on the current state, but
must be symmetric and have a target-mass normalizer unchanged by rerooting at
any admitted candidate. Target-weighted selection is then proved reversible
and stationary. Decidable equivalence-class candidates instantiate the API and
can vary genuinely between components. A concrete doubling/U-turn builder must
still establish this certificate; naïve first-U-turn stopping is not covered.

Added an exact general-state constrained-coordinate transport theorem. A
kernel invariant for the pushforward target in unconstrained coordinates is
conjugated through a measurable equivalence and proved invariant for the
original constrained measure. The positive-real log/exp equivalence is a
concrete client. This locates Jacobian correction at the pushed-density
identification and prevents an unconstrained implementation from silently
claiming the original density unchanged.

Added generated composable-inference metadata. Lean defines portable engine,
operator, and schedule descriptors, proves coverage of the canonical Ge et al.
PG--HMC schedule, and emits it in IR version 12. Julia decodes the descriptor
and `generated_schedule` instantiates callbacks in the generated order with
the generated scopes. Tests cover execution order, state changes, missing
callbacks, and unknown schedules. This verifies configuration transport, not
yet semantic equality of arbitrary callbacks with formal kernels.
