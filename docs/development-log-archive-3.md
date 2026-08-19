# Development log archive, part 3

Continued from [part 2](development-log-archive-2.md).

## 2026-08-16: exact finite-particle variance identity

Added the first particle-count asymptotic foundation beyond unbiasedness.
For an arbitrary finite iid particle cloud, Lean proves factorization of
distinct-coordinate expectations, zero expectation of the centered score,
and the exact second-moment identity for the centered particle sum. It then
derives

`E[(particleAverage - expectation)²] = variance / particle-count`

for every positive finite count. This is an exact finite theorem and supplies
the quantitative `1/N` mean-square scaling used by particle consistency
arguments. The count-indexed `Fin (extra+1)` estimator is then proved to
converge to zero in mean square as `extra → ∞`. A finite Chebyshev bound
controls the exact probability that the empirical average lies outside any
fixed positive tolerance, yielding convergence in probability as well. These
are not central-limit theorems and do not yet establish sequential
particle-filter asymptotics.

## 2026-08-16: bounded continuous slice execution

Added a public `BoundedRejectionSlice` Julia sampler for continuous densities
restricted to a finite interval. The vertical height is sampled in log space;
the horizontal conditional is implemented by uniform rejection over the full
interval. Independent Reference and low-allocation Optimized loops agree on
fixed traces, including rejection/retry, and tests cover seeded replay,
support containment, and the exact bounded-uniform moments.

The corresponding ideal general-state kernel is already proved invariant in
Lean through under-graph disintegration. The runtime is deliberately not
claimed as an unconditional refinement: arbitrary callbacks, Float64 uniform
draws, and exhaustion of the finite attempt guard remain explicit execution
boundaries.

The Lean API now also offers a finite-target disintegrated wrapper, avoiding a
redundant client-side finiteness proof for the equal under-graph joint. A
continuous example instantiates it for the uniform probability law on
`(-2,2]` and proves exact invariance. This is the ideal mathematical client
behind the runtime's flat-density test, while cross-language numerical
refinement remains explicitly separate.

## 2026-08-16: generated sinusoidal target refinement

Extended restricted artifact IR to version 13 with portable sine and cosine
nodes. Lean proves the new symbolic derivative cases, differentiability, and
recursive backend refinement. Argument transport uses the global
one-Lipschitz bounds of sine and cosine; only backend-local libm errors remain
primitive obligations. The generated `x²/2-sin(x)` artifact is proved to have
ideal value `x²/2-sin(x)` and force `x-cos(x)`, matching the genuinely
position-dependent SoftAbs foundation.

Julia decodes the generated tree, evaluates its value and symbolic force, and
tests both at representative inputs. This closes generated target/force
transport, not the later `tanh`/square-root/log metric evaluation or the
nonzero-step implicit-solver validity certificate.

## 2026-08-16: guarded SoftAbs metric refinement

Added an operation-local numerical contract for one diagonal SoftAbs metric
entry. Given a Hessian approximation and backend error bounds, Lean now
composes guarded approximations for the positive SoftAbs eigenvalue, its
square root, inverse-square-root factor, and log-determinant contribution.
The ideal positivity proof discharges every exact-real domain obligation.
The construction now lifts coordinatewise over any finite diagonal metric;
a reusable finite-sum lemma proves that entrywise log-determinant errors add
to a certified bound for the complete log determinant.
For the generated sinusoidal target, Lean also proves that the second
symbolic derivative is exactly `1 + sin(x)` and feeds its recursive backend
error certificate directly into the SoftAbs metric-entry constructor. Julia
now evaluates value, force, and symbolic Hessian from the same generated
expression before exercising the guarded metric evaluator.

The implicit-solver refinement now has its positive-error theorem as well.
For any genuine contraction, Lean transports an approximate computed residual
to the a posteriori bound
`distance_to_exact ≤ (|computed residual| + residual error)/(1-rate)` and
specializes it to both generalized-leapfrog implicit loops. Julia checks and
evaluates the same scalar bound. This turns practical nonzero residuals into
quantified approximation guarantees; it does not misclassify them as exact,
reversible, or volume-preserving solves.

Julia's guarded metric surface now also evaluates a complete nonempty
diagonal, returning per-coordinate factors and the aggregate log determinant.
This mirrors the finite-dimensional Lean certificate rather than leaving the
runtime at a scalar-only demonstration.

## 2026-08-16: heterogeneous particle propagation variance

Extended the particle-count asymptotic foundation from iid populations to
independent, non-identically distributed coordinates, the conditional law
that arises after fixing SMC ancestor indices. Lean proves exact
factorization of distinct coordinates, cancellation of all cross-coordinate
covariances, and

`MSE(empirical average) = (sum of coordinate variances) / N²`.

For triangular arrays whose coordinate laws may change with particle count,
a uniform coordinate-variance bound now yields conditional `V/N` MSE,
mean-square consistency, a finite Chebyshev bound, and convergence in
probability around the count-specific mean. This supplies the per-stage local
term for a sequential resample--propagate recurrence. It is not yet the
completed normalized particle-filter consistency theorem, because random
resampling weights and previous-stage empirical error must still be composed.

The random multinomial-resampling layer is now composed for one complete
bootstrap step. Lean proves the exact conditional bias--variance identity

`MSE(next average) = (mean propagation variance + ancestry-mean variance) / N`

for resampling followed by heterogeneous Markov propagation, and derives a
client-facing bound from separate uniform propagation and ancestry variance
bounds. Thus random resampling weights are no longer missing from the local
recurrence; iteration across horizons and control of the nonlinear normalized
weight map remain the sequential consistency obligations.

## 2026-08-16: concrete certified scalar U-turn partition

Added the first numerical stopping detector that feeds the reroot-safe dynamic
tree construction. On a complete canonical scalar phase trajectory, an edge
is marked whenever its displacement has negative product with either endpoint
momentum. Lean proves that the resulting barrier list has exactly one entry
per adjacent pair, passes the dynamic-tree checker, and yields a stationary
target-weighted candidate kernel. Julia implements the identical detector and
checks representative turns and invalid trajectories.

This construction is intentionally narrower than recursive NUTS: it is a
root-independent adjacent-endpoint detector followed by canonical component
partitioning. Recursive subtree U-turn aggregation, doubling, and multinomial
selection over such a tree still require their own equivalence and refinement
proofs.

The same construction now covers every finite-dimensional Euclidean phase
trajectory. Lean uses the endpoint displacement inner products with both
momenta, proves the barrier count and checked reroot partition, and derives
stationarity. Julia mirrors the vector detector with dimension and finiteness
validation. The scalar client remains the one-coordinate specialization in
spirit; no floating-point equivalence theorem is inferred from the tests.

Added a conservative all-scales variant.  For every split of the completed
canonical orbit it inspects every endpoint pair spanning that split and cuts
the orbit if any pair satisfies the vector U-turn condition.  Lean proves the
barrier count, reroot certificate, and stationarity of target-weighted
selection; Julia mirrors the construction and is differentially guarded by
the same completed-partition checker.  This incorporates recursive-scale
subtree information while deliberately remaining distinct from root-dependent
first-U-turn NUTS.

## 2026-08-16: product-compositional reversible-jump transports

Added a reusable product constructor for reversible-jump transport-density
certificates. Two independently certified auxiliary transports now yield a
product transport whose destination reference is the product measure and
whose cross density is the product of the component Jacobian-corrected
densities. The planar birth/death certificate is rebuilt from two scalar
certificates, and recursively composing it with a third scalar certificate
produces a checked three-dimensional transport.

This removes the need to repeat the measure-level change-of-variables proof
for every product dimension. A complete three-dimensional MH client is not
claimed at this checkpoint; the proved artifact is its normalized
transport-density core.

The product certificate is now connected to a complete three-dimensional
birth/death client.  The tagged reference measure, determinant-corrected cross
proposal, proposal normalization, finite accepted flow, and resulting
Metropolis--Hastings invariance theorem are all machine checked.  This closes
the earlier gap between the compositional transport core and a usable
reversible-jump transition in dimension three.

## 2026-08-16: concrete Gaussian Zig-Zag generator tests

Instantiated the one-dimensional Zig-Zag generator with the standard Gaussian
potential gradient. For the velocity observable, Lean reduces the summed
generator to the odd function `-2q` and proves its Gaussian integral is zero.
For the nontrivial position-times-velocity observable, it reduces the
generator to `2-2q²` and closes the integral using mathlib's exact Gaussian
mean and variance theorems.

These are concrete generator-balance clients rather than a full invariant-
semigroup result. Extending from this checked test family to an integration-
by-parts class, and connecting it to the all-count event scheduler, remain
explicit PDMP obligations.

The Gaussian test family now closes under every affine velocity-odd
observable `(a+bq)v`.  Lean computes the generator sum symbolically and uses
the exact Gaussian first and second moments to prove zero mean for arbitrary
real coefficients.  This replaces two isolated checks by their full
two-dimensional linear span, while retaining the explicit boundary: generator
balance on this class is not yet an invariant-semigroup theorem.

Added an executable Gaussian Zig-Zag clock.  Along the linear flow the
switching rate is `max(0,vq+t)`; Lean defines its integrated hazard, proves the
closed-form inverse waiting time nonnegative, and proves exact inversion for
every positive exponential draw.  Julia mirrors that formula in a
fixed-observation-horizon simulator and tests the hazard identity,
reproducibility, velocity domain, and standard-Gaussian moments.  The
Float64 square-root/exponential-draw layer remains numerical evidence, while
the algebraic clock identity is machine checked over the reals.

## 2026-08-16: practical stepping-out slice runtime

Added a public `SteppingOutSlice` sampler on the real line with randomized
initial brackets, bounded stepping out, and shrinkage. Independent Reference
and low-allocation Optimized implementations agree under deterministic trace
replay; seeded standard-normal moment tests, reproducibility, and invalid
configuration tests are active.

The ideal under-graph disintegration theorem remains the mathematical
invariance endpoint. The adaptive bracket algorithm, Float64 callbacks, and
finite expansion/shrinkage guards have not yet been refined to that kernel, so
the runtime is not advertised as machine-checked exact slice sampling.

Julia exposes the matching guarded Float64 evaluator, including the removable
zero-Hessian branch, and tests its algebraic outputs and invalid domains. This
is deliberately runtime evidence rather than a platform certificate: error
bounds for `tanh`, `sqrt`, reciprocal, and `log` remain explicit backend
premises, and the position-dependent implicit solver remains the next
separate refinement obligation.

Extended that guarded refinement through the scalar Hamiltonian consumed by
accept/reject.  Lean now composes the certified SoftAbs factor with an
approximate momentum, propagates error through the transformed square and
positive radicand, applies the guarded square-root backend, and combines the
result with certified potential and half-log-determinant terms.  Julia exposes
and tests the identical unit-parameter expression
`U + sqrt(1 + (A*p)^2) + log(G)/2`.  The result supplies endpoint-energy error
inputs to the existing stable-decision theorem; it still does not assert a
global libm error bound for arbitrary Julia platforms.

Instantiated the abstract numerical-refinement interface with the exact
ideal-real Lean IR interpreter. Equality represents values, target callbacks,
and event sources, and `exactInterpreter_refines` proves the complete RWMH
step contract without hypotheses.  This gives differential tests a formal
oracle while preserving the intended boundary: Julia `Float64` is related by
bounded-error and stable-decision certificates, not by a false equality
instance.

Added the first executable constrained-coordinate client.
`PositiveTransformedRWMH` maps a positive state through `log`, runs the
existing Gaussian RWMH implementation with unconstrained log density
`logπ(exp(y)) + y`, and maps back through `exp`.  Julia tests positivity,
deterministic replay, validation, and exponential-target moments.  The `+y`
term makes the measure Jacobian visible and aligns the runtime with
`transformedKernel_invariant`; bounded `Float64` refinement of `log` and `exp`
remains explicit rather than being inferred from the empirical test.

Added the matching bounded numerical layer.  On inputs uniformly bounded
below by a positive `lower`, Lean proves that `log` transports absolute error
with factor `1/lower`, composes this with a backend-local libm error, adds the
unconstrained coordinate as the exact log-Jacobian correction, and transports
the returned coordinate through `exp` on an explicit upper-bounded region.
This closes the backend-independent arithmetic for the positive transform;
a concrete platform still supplies its local `log` and `exp` errors.

Promoted the transform convention into generated IR version 14.  Lean emits a
`positive-log` descriptor containing the constrained/unconstrained types,
`log`/`exp` directions, and the identity log-Jacobian expression.  Julia
parses, validates, and exposes that descriptor through `generated_transform`;
artifact reproducibility and descriptor fields are tested.  The handwritten
runtime therefore consumes a convention that is versioned at the Lean
boundary rather than duplicating undocumented metadata.

Extended the general-state PG--HMC client to a genuinely multivariate mixed
state. A two-dimensional Gaussian position is deterministically augmented by
its four-valued quadrant, standard-Borel disintegration supplies the exact
Gaussian-quadrant reverse conditional, and the resulting two-block auxiliary
update is composed with the actual two-dimensional Gaussian SoftAbs
multinomial GR-HMC transition. Lean proves invariance of the normalized
continuous target for the complete schedule.

Added a reproducible exact-meeting diagnostic for the executable Xu et al.
coupling. `coupled_meeting_time` advances the faithful coupled mixture until
the first bitwise-equal state or a caller-supplied finite horizon, reports
time zero for an already met pair, and is deterministic under a fixed RNG.
Tests include a nontrivial Gaussian pair that meets within the diagnostic
horizon. This helper supports experiment reproduction; it is not used as
evidence for the separate machine-checked geometric-tail theorem.

## 2026-08-16: normalized particle-error recursion

Added the deterministic nonlinear bridge needed beyond the exact one-step
resample--propagate variance identity.  Lean bounds perturbation of a
self-normalized estimate by separate numerator and normalizer errors, with an
explicit positive lower bound on the approximate normalizer.  It also proves
the finite-horizon geometric-sum solution of an affine one-step error
recurrence.  Together these isolate the assumptions needed to propagate
`O(1/N)` error through finitely many normalized Feynman--Kac stages.  A
uniform-in-time theorem still requires a strict stability estimate and is not
inferred from these local bounds.

## 2026-08-16: nondegenerate nonconstant SoftAbs bounds

Added a second actual-Hessian SoftAbs client designed for the implicit-solver
path. For `U(q)=q²-sin(q)`, Lean proves `U''(q)=2+sin(q) ∈ [1,3]`, constructs
the diagonal SoftAbs metric and its Equation (12) certificate, and proves
measurability and uniform positive lower and finite upper eigenvalue bounds.
An explicit derivative calculation for `x/tanh(x)` on the positive branch,
compactness of `[1,3]`, and the mean-value theorem give a finite uniform
derivative bound and a Lipschitz certificate. Composition with the actual
Hessian proves that the target's scalar metric eigenvalue is globally
Lipschitz. This is the metric-level analytic input; the complete Hamiltonian's
two slice-Lipschitz estimates and the consequent nonzero-step solver and
phase-volume theorem remain separate obligations.

Extracted the reusable scalar slice calculation and applied it to that client.
For an arbitrary positive scalar factor, Lean now proves the momentum-slice
bound for the complete position derivative and the position-slice bound for
the momentum derivative; every position-only force term cancels in the former.
The generic scalar Hamiltonian derivative formulas connect these callbacks to
the complete Hamiltonian rather than merely to a synthetic fixed-point model.
For the nondegenerate SoftAbs client, compact smoothness gives a global
inverse-square-root-factor Lipschitz constant and derivative bound. Lean then
constructs an explicit nonzero admissible step, its exact Banach-selected
generalized-leapfrog solver, and the certified negative-step inverse. Exact
phase-volume preservation is still a distinct Jacobian theorem and is not
inferred from invertibility alone.

The phase-volume proof has now been factored at its lowest reusable layer.
`ScalarJacobian` defines generic vertical and horizontal triangular shears for
arbitrary differentiable scalar callbacks, proves their actual `2×2` Fréchet
derivative matrices and determinant formulas, and proves that equality of the
Hamiltonian mixed partials pairs the incoming/right and left/outgoing
determinants. A separate generic calculation proves that the scalar
relativistic position and momentum callbacks have equal mixed slice
derivatives for every differentiable positive factor; the nonconstant SoftAbs
client instantiates that identity. Remaining is the global inverse-stage
composition that turns these paired factors into determinant one for the
Banach-selected step.

The global determinant composition itself is now generic as well.
`scalarGeneralizedLeapfrogStep` composes arbitrary differentiable incoming and
left inverse selections with the right and outgoing shears. Given the two
left-inverse identities and the mixed-partial equality, Lean multiplies the
four actual Fréchet determinants, uses the inverse-function determinant
identities, and proves determinant exactly one. Separate reusable lemmas show
that the strict slice-contraction inequalities make the incoming and left-map
Jacobians nonsingular. The target-specific residue is therefore narrowed to
constructing the scalar-coordinate inverse selections from the existing
Banach solver and proving their continuity/differentiability.

That generic inverse-selection layer is now complete. For arbitrary scalar
callbacks with uniform slice-Lipschitz constants, Lean constructs both global
Banach fixed-point selections, proves the triangular maps are their left
inverses, and derives continuity from the uniform fixed-point theorem. The
strict contraction bounds make the triangular Jacobians nonsingular, so the
global inverse theorem proves both selections differentiable. Combining these
results with the generic determinant composition yields an end-to-end
determinant-one theorem for a fully constructed scalar Banach generalized-
leapfrog step. The SoftAbs client still needs a lightweight opaque callback
binding to this generic real-coordinate theorem and conjugation back to
`PhaseSpace Unit`; this is an elaboration/interface task rather than another
Jacobian calculation.

The target binding is now closed as well. Lean proves that the constructed
scalar Banach step satisfies all three generalized-leapfrog coordinate
equations, transports those equations through the scalar/`PhaseSpace Unit`
linear equivalence, and invokes uniqueness of the existing contraction solver.
Consequently the auxiliary Jacobian construction and the actual certified
nonconstant SoftAbs Hamiltonian step are pointwise equal. The step is bijective,
differentiable, has determinant one everywhere, and exactly preserves phase
volume. The remaining boundary for this client is the deliberately separate
bounded Float64 refinement of the Julia implicit iterations.

The first target-specific numerical bridge now reuses that exact solver.
`RelativisticCertificates` specializes the generic computed-residual theorem
to the nonconstant actual-Hessian SoftAbs callbacks. A finite half-momentum
loop is bounded against the certified solver's exact half momentum, and a
finite position loop at that exact half momentum is bounded against its exact
next position, both with the a posteriori budget
`(|reportedResidual| + residualError) / (1 - contractionRate)`. The remaining
coupled numerical step is explicit: transport the approximate half-momentum
error into the position solve and final momentum, then into energy and
multinomial-selection certificates.

The position part of that coupled step is now closed. For arbitrary scalar
relativistic callbacks, a new cross-slice lemma bounds the momentum derivative
as a function of momentum by the square of a uniform metric-factor bound.
For the nonconstant SoftAbs client the factor is proved globally at most one,
so this cross Lipschitz constant is exactly one. A reusable fixed-point
stability theorem then bounds the change of the implicit next position under
a perturbed half momentum. Combining it with the reported position residual
gives an explicit two-term error bound against the actual certified solver's
next position. Final-momentum and energy/selection propagation remain the
next numerical links.

Added the reusable final-kick link. If the Hamiltonian position derivative is
Lipschitz in momentum with constant `P` and in position with constant `Q`, the
outgoing momentum error is bounded by
`(1 + |ε/2|P) * pError + |ε/2|Q * qError`. The proof is coordinate-free over
every finite-dimensional phase space. The target's global `P` is already
available; `Q` must be certified on the bounded numerical trajectory region,
as must the endpoint-energy Lipschitz constant, rather than falsely asserting
a global bound for the quadratic potential.

Added the matching bounded-region energy bridge. For any phase Hamiltonian
that is Lipschitz on a certified region containing both the computed and ideal
states, Lean now turns a state-distance budget plus a backend energy-evaluation
budget into an endpoint-energy approximation. The pre-existing endpoint
difference and stable HMC/multinomial decision theorems can consume this result.
This preserves the correct local nature of the quadratic SoftAbs target rather
than smuggling in a false global Lipschitz premise.

Closed the compact-region existence obligation for the actual target. The
scalar SoftAbs Hamiltonian is proved smooth, as is its position callback via
identification with the first coordinate of the Hamiltonian Fréchet
derivative. On every closed phase ball, compactness and continuity attain a
maximum derivative norm; the mean-value theorem turns that maximum into a
checked `LipschitzOnWith` constant. Canonical radii automatically enclose each
computed/ideal phase pair. Lean now combines position and outgoing-momentum
coordinate errors in the product metric and transports them to endpoint-energy
error. The final discontinuous multinomial choice remains conditional only on
the explicit runtime boundary-margin certificate and backend primitive-error
witnesses.

Completed the remaining multinomial arithmetic composition. A uniform family
of endpoint-energy certificates now propagates through negation, the finite
maximum used for log-sum-exp stabilization, shifted nonpositive exponentials,
total and cumulative weight sums, and the scaled uniform draw. The checked
boundary budget is
`trajectoryCount * (expError + 2 * energyError)`; the draw budget additionally
records backend multiplication, RNG, and total-weight errors. A constructor
packages these facts into the existing list-based selection certificate, whose
stable-margin theorem proves the computed and ideal trajectory indices equal.
This closes the backend-independent Xu--Ge refinement chain without pretending
to prove universal Julia/libm/RNG bounds.

## 2026-08-16: normalized logistic stationary coupling

Closed the analytic moment obligation that separated the regularized-logistic
Xu client from its normalized posterior. Coordinate Gaussian integrability
now supplies a finite Euclidean first moment for the quadratic envelope;
coercivity transfers this to `1 + dist q 0` under the logistic Boltzmann
density and then through finite-measure normalization. Lean consequently
proves the normalized posterior's finite distance-Lyapunov moment, the finite
paired moment for a point mass and stationary draw, and a geometric same-time
meeting tail for the concrete sticky HMC/RWMH mixture. The remaining packaging
step was to select this tail and the lag-one estimator tail from the same drift
record and identify the estimator mean with the normalized posterior integral.
That packaging is now complete: one selected mixture supplies both tails, so
bounded point-started expectations converge to the normalized posterior
integral and the stopped lag-one estimator is unbiased for exactly that
integral with finite variance.

## 2026-08-16: direct setwise convergence for refreshed GR-HMC

Upgraded the reusable refresh-augmentation layer from two geometric event
bounds plus a vanishing remainder to a direct setwise convergence theorem.
For `0 < p < 1`, every initial probability law converges on every measurable
event to the invariant target; the proof sandwiches the evolving event mass
between `target - p^n` and `target + p^n`. The concrete Gaussian diagonal-
SoftAbs multinomial GR-HMC client instantiates this theorem. The result remains
explicitly about the target-refresh-augmented chain and makes no convergence
claim for bare GR-HMC.

## 2026-08-16: zero-boundary adjacent-count PDMP flux

Simplified the fixed-horizon PDMP stationarity interface at the exact
cross-count boundary. Lean now proves that `flux 0 = 0` automatically implies
equality between the sum of positive-count incoming fluxes and the full flux
sum, by splitting count zero and reindexing positive naturals. A new horizon
theorem consumes only the transported-stratum decomposition, the weighted-
target decomposition, and this zero-boundary fact. Concrete Zig-Zag/BPS
clients still owe the spatial decomposition itself, but no longer need to
repeat infinite-measure reindexing.

## 2026-08-16: dynamic-tree executable conformance fix

Running the complete Julia package suite activated a previously failing
all-scales U-turn case. Julia's comma-form nested-loop `break` exited the full
split/left/right loop nest after the first detected turn, so later splits were
never checked and unrelated leaves were incorrectly merged. The implementation
now accumulates every spanning endpoint test, matching Lean's
`vectorSpanningUTurnBarriers` definition. The targeted dynamic-tree suite and
the full Julia suite now pass, including the continuous diagnostics and
robustness/performance test groups.

## 2026-08-16: non-product reversible-jump client

Added a complete triangular-shear birth/death client. The dimension-matching
map `(u₁,u₂) ↦ (2u₁+8u₂³,2u₂)` is nonlinear and not a product
transport. Lean factors the cubic triangular map into swaps and a measurable
translation skew product to prove that its unit-determinant postcomposition
preserves planar volume, derives the inverse-Jacobian density
`1/16` on the nonlinear sheared curved strip, and packages the exact auxiliary
pushforward as a transport-density certificate. The resulting tagged proposal
is normalized and its reversible-jump MH transition preserves the intended
tagged target.

## 2026-08-16: setwise convergence for mixed PG--GR-HMC

Extended the dependent Boolean/Gaussian general-state composition with an
explicit normalized-target refresh branch. The original two-block
disintegration update followed by Gaussian SoftAbs GR-HMC remains the active
branch, and its existing common-target stationarity theorem feeds the generic
refresh convergence result. For `0 < p < 1`, Lean now proves setwise
convergence on every measurable event from every initial probability law. The
unaugmented PG--GR-HMC composition remains correctly described as stationary,
not automatically convergent.

## 2026-08-16: stationary telegraph PDMP client

Added a nontrivial flow-driven process client whose conditional horizon
execution is proved stationary. The Boolean-velocity telegraph flow is a
measurable semiflow; a skew-product argument proves every linear flow preserves
equal mass on both velocities times Lebesgue position, and a second
skew-product argument proves the velocity flip preserves the same target.
With a constant event rate equal to the homogeneous clock, the uniformized
kernel is exactly the flip. A reusable induction now shows that arbitrary
supplied finite candidate waits, including candidates beyond the horizon,
preserve the target. The target is sigma-finite, so neither probability
ergodicity nor convergence is claimed, and canonical state-dependent
Zig-Zag/BPS spatial flux remains open.

## 2026-08-16: scalar Gaussian SoftAbs tail algebra

Exposed exact one-dimensional formulas for the Gaussian diagonal-SoftAbs
client's relativistic velocity, complete Hamiltonian, and both coordinates of
its unit generalized-leapfrog step.  These lemmas reduce the remaining bare
GR-HMC tail argument to inequalities over real scalars while retaining a
checked connection to the actual solver.  The already-proved central-momentum
event moves each Gaussian tail inward by a uniform positive distance; the
next obligation is an energy comparison giving that inward trajectory a
uniform multinomial-selection probability.  No bare-kernel convergence claim
is made yet.

## 2026-08-16: corrected Gaussian SoftAbs endpoint selection

Closed the exact energy-comparison obligation for the concrete
one-dimensional `ε=1`, `L=1` Gaussian SoftAbs client.  Lean proves the
SoftAbs eigenvalue lies between one and two, derives uniform square-root
bounds, and shows that on `q ≥ 6, p ∈ [0,1]` the actual generalized-leapfrog
endpoint moves inward and has nonpositive complete-Hamiltonian defect.  A
negation-equivariance proof supplies the symmetric `q ≤ -6, p ∈ [-1,0]`
case.  Consequently, when the current phase point is rooted at index zero,
the inward endpoint has at least one half of the two-point multinomial
selection probability.  Remaining work for bare-kernel convergence is to
integrate this pointwise floor through random-origin selection and momentum
refresh, then turn it into a Lyapunov drift/minorization certificate.

## 2026-08-16: bare Gaussian SoftAbs kernel tail events

Propagated the endpoint correction through the actual algorithmic kernels.
A reusable orbit lemma lower-bounds the full random-origin kernel by any one
origin/selection branch, and another proves probability one for events
containing every orbit point.  A new nested-integral theorem exposes the exact
momentum-refresh semantics of position-space multinomial GR-HMC.  Using these
bridges, Lean proves that the concrete `ε=1`, `L=1` position sampler has a
strictly positive, position-uniform probability of moving inward by the
certified SoftAbs distance on each tail.  It also proves the relativistic
finite-speed fact that every output lies within one position unit of its
input almost surely.  The remaining bare-kernel convergence obligation is an
asymptotic drift/minorization argument; the current results do not yet claim
ergodicity by themselves.

## 2026-08-16: expanding-band Gaussian SoftAbs correction

Strengthened the fixed central-momentum calculation to the position-indexed
band `|p| ≤ q/2 - 2` on the positive tail.  Forward-time correction handles
nonnegative momenta; generalized-leapfrog time reversal handles nonpositive
momenta through the backward trajectory origin.  Lean proves throughout this
band that both trajectory directions are non-outward and that an endpoint at
least the certified SoftAbs distance inward is selected with probability at
least one quarter.  The exact transported momentum probability of this band
is proved to tend to one as `q → +∞`.  Reusable GR-HMC infrastructure now
propagates any measurable momentum-subset phase-event floor through refresh
and position projection.  Thus the actual position kernel inherits both the
expanding inward floor and the non-outward mass.  The symmetric negative-tail
packaging and the final Lyapunov/minorization theorem remain open.

## 2026-08-16: symmetric expanding-band tail certificates

Completed the exact negative-tail counterpart.  Negation invariance of the
Gaussian Hamiltonian and generalized-leapfrog momentum-flip reversibility
transfer the forward/backward energy corrections without changing constants.
For `|p| ≤ -q/2 - 2`, Lean proves both phase endpoints are non-outward and an
endpoint at least the SoftAbs minimum speed inward is selected with
probability at least one quarter.  Both statements are propagated through
momentum refresh to the actual position kernel.  The shared tail-band mass
tends to one, and Lean now proves an eventual strict scalar budget comparing
the band-complement probability with the inward displacement.  What remains
is to convert these eventwise bounds into a checked Lyapunov expectation
inequality and supply a local small-set/coupling certificate.

## 2026-08-16: stationary Gaussian Zig-Zag Palm product law

Completed the Palm input for the scalar Gaussian Zig-Zag renewal proof. Lean
first rewrites the pointwise residual-hazard fiber identity as a set integral,
then uses Tonelli over the literal regenerative-cycle occupation law. The
resulting probability pushforward of occupied signed position and remaining
integrated hazard is exactly the product of the standard Gaussian law and an
independent unit exponential law. This is a joint-law theorem, not merely two
marginal calculations. The remaining scalar process obligation is the
stationary renewal-shift/horizon identification and its transfer through the
already-proved signed/physical conjugacy.

## 2026-08-16: stationary-cycle/exact-clock pathwise bridge

Connected the Palm construction to the executable exact path recursion. For
every occupied signed position strictly inside a cycle with a genuine negative
right reset, Lean proves that the cycle's residual quadratic hazard makes the
canonical inverse clock wait exactly the remaining geometric distance, and
that its event update lands exactly at the stored right reset. The signed
first-event endpoint is consequently rewritten into the literal cycle branch:
translate within the current interval, or restart the exact horizon execution
from the right reset with the remaining horizon. This removes the last
coordinate-level mismatch before the stationary renewal-shift argument.

## 2026-08-16: stopped-horizon stationary-cycle identification

Lifted the Palm product law through velocity labels and iid future hazard
tails. Lean proves that extracting occupied position and residual clock from
the normalized stationary cycle, adjoining an independent velocity, and
consing the residual clock onto a fresh iid tail gives exactly the Gaussian
phase target times the iid hazard-stream law. The signed horizon kernel is
also proved equal to its direct jointly measurable sampling construction.
Consequently, target-started stopped execution is now exactly the pushforward
of stationary cycle occupation, velocity, and future tail through the actual
stopped executor. The remaining theorem is purely the measure-preserving
stationary renewal shift; there is no longer an unproved conditional-law,
coordinate, or executor-identification step around it.

## 2026-08-16: regenerative suspension base invariance

Constructed the base environment underlying the remaining stationary renewal
shift: two consecutive negative-Rayleigh resets plus the iid future hazard
tail. Its event shift discards the consumed left reset, promotes the old right
reset, generates the new right reset from the tail head, and advances the
tail. Lean proves this transformation preserves the full environment law.
The current interval roof is measurable and strictly positive almost surely.
After adjoining the independent uniform velocity label and flipping it at
each event, the phase-environment shift is also proved measure preserving.
Thus the remaining work is precisely the special-flow/suspension theorem that
lifts this invariant base map and positive roof to arbitrary real-time shifts.

## 2026-08-16: reusable stationary-suspension occupation layer

Added `Mcmc.PDMP.StationarySuspension` as the general renewal layer. It defines
the measurable fundamental domain below a roof, its unnormalized and
normalized occupation measures, and proves the exact total-mass/mean-roof
identity. For every nonnegative horizon, Lean partitions roof occupation into
the no-boundary survivor segment and the boundary-crossing segment. The
survivor branch is already complete: fiberwise Lebesgue translation maps it
exactly onto the terminal segment of each roof. The Gaussian Zig-Zag event
environment, invariant phase base, positive roof, and concrete suspension
occupation are instantiated against this API. What remains in this layer is
the countable crossing reduction, using nonexplosion to exhaust all event
counts.

## 2026-08-16: measurable countable suspension executor

Extended the reusable suspension layer with measurable base iterates,
cumulative roofs, crossing predicates, the first crossing index, and the
total special-flow endpoint. On every terminating nonnegative shift from a
valid age, Lean proves that the selected residual age lies in the fundamental
domain of the selected future roof. The Gaussian client now has an explicit
measurable decoder from suspension age to signed cycle position, and
fiberwise Lebesgue translation is proved exactly equal to the existing
literal cycle-interval kernel (open versus half-open endpoints are discharged
as a volume-null distinction). The next proof is the crossing-count
truncation identity and vanishing nonexplosive remainder, after which the
generic endpoint preserves normalized occupation.

## 2026-08-16: suspension crossing recursion

Completed the pathwise recursion needed for the countable crossing proof.
Lean now splits cumulative roofs into the current roof plus the shifted-base
tail, proves the corresponding equivalence of later crossing predicates, and
shows that whenever the horizon reaches the current boundary, the total
special-flow endpoint is exactly the endpoint obtained by restarting from the
base-shifted environment at age zero with the residual horizon. Before the
first boundary it is exactly vertical translation. These two exhaustive
equations are the induction interface for the remaining finite-crossing
measure identity and nonexplosive limit.

## 2026-08-16: stationary-suspension invariance

Completed the reusable special-flow theorem. For a measurable base map that
preserves a probability measure, a measurable almost-everywhere nonnegative
roof, and almost-sure nonexplosion, Lean proves that every nonnegative-time
suspension endpoint preserves the unnormalized roof-occupation measure. The
proof telescopes the occupation of every orbit interval across all crossed
roofs, uses base invariance for the boundary flux, and cancels the finite
initial segment. This closes the abstract continuous-time renewal argument;
the remaining work is to discharge its hypotheses for the Gaussian Zig-Zag
environment and push the resulting invariant law through the existing
decoder and signed/physical/BPS equivalences.

## 2026-08-16: Gaussian regenerative nonexplosion

Discharged the abstract suspension theorem's final probabilistic hypothesis
for the Gaussian Zig-Zag environment. Lean tracks the iid hazard tail through
every event shift, identifies each newly generated right reset, and proves
that every future roof dominates the corresponding square-root hazard term.
The previously established almost-sure divergence of that series forces the
cumulative roof time past every finite horizon. Consequently, the concrete
Gaussian suspension occupation measure is now machine-checked invariant at
every nonnegative time. Only the pathwise decoder/intertwining transfer to the
public stopped Zig-Zag kernel remains.

## 2026-08-16: suspension/stationary-cycle decoder law

Completed the measure-level decoder identification. A checked permutation of
the reset, future-hazard, velocity, and age product coordinates moves the
suspension age beside its reset pair. Fiberwise translation then maps the age
interval exactly to the literal regenerative-cycle kernel, and product-map
laws restore the public stationary-cycle coordinate order. Thus decoded
unnormalized suspension occupation is exactly the mean cycle duration times
the normalized stationary-cycle source law used by the stopped executor.
The remaining transfer is now solely the pathwise commuting equation between
the suspension endpoint and the exact stopped recursion.

## 2026-08-16: exact Gaussian Zig-Zag and unit-BPS stationarity

Closed the end-to-end regenerative proof for the actual stopped executor.
Lean proves pointwise, by induction on a finite suspension-crossing witness,
that the exact signed inverse-clock recursion commutes with the suspension
endpoint on every positive divergent hazard stream. The equation holds almost
surely under normalized suspension occupation. Combining it with suspension
invariance and the exact Palm decoder law proves that the signed Gaussian
Zig-Zag horizon kernel preserves the Gaussian/equal-velocity target for every
nonnegative horizon. The existing involutive signed/physical conjugacy then
proves the same theorem for the production physical Zig-Zag kernel, and the
proved one-dimensional BPS identification transfers it to exact unit-speed
Gaussian BPS. These are stationarity theorems, not semigroup, ergodicity, or
convergence theorems; those remain separate milestones.

## 2026-08-17: factorized rooted-trace reversal

Refined the correctness boundary for ordinary root-dependent randomized NUTS.
The new `FactorizedRootedTraceSampler` separates the probability of building
a complete random trace from the probability of selecting an endpoint from
that trace.  A nonnegative bridge factor records how the construction law
changes under endpoint rerooting; one local construction identity and one
target-weighted selection identity are now sufficient for Lean to derive the
existing complete trace-reversal certificate, detailed balance, and
stationarity.  This is a proved compositional reduction, not yet a proof of
standard NUTS: the remaining obligation is to define the exact recursive
direction/subtree/candidate trace and discharge these two identities.

The construction side is now refined further. `LocalChoiceRootedTraceSampler`
proves that a finite product of local random-choice reversal ratios supplies
the global trace-law ratio automatically. The concrete law of a bounded vector
of independent fair Boolean doubling directions is defined and normalized,
and Lean proves that every endpoint-dependent bijection of those traces
preserves its mass. Consequently the fair direction coins used by the Julia
recursive builder are no longer part of the open balance argument. What
remains is to retain subtree-validity and streaming candidate choices in the
trace and prove their target-weighted conditional selection reversal.

Added the normalization theorem for that remaining endpoint step.
`ReversibleTraceSelection` accepts nonnegative endpoint weights on a complete
rooted trace, positivity of their total, equality of that total after complete
trace reversal, and a pointwise target-weighted endpoint-flow equation. Lean
constructs the normalized conditional distribution and proves its exact
selection-reversal identity. `withTraceSelection` then assembles it with the
factorized construction law into the public detailed-balance and stationarity
certificate. Raw candidate rows are allowed to differ; the theorem compares
the particular forward trace with its bijectively reversed trace, avoiding the
known-false universal row-equality premise.

Matched the efficient candidate-selection step in Hoffman--Gelman Algorithm 3.
`weightedMergeDistribution` is the exact law obtained by retaining one
representative from each completed subtree and choosing between them with
probability proportional to their eligible counts. Lean proves that merging
two already normalized subtree laws yields the normalized law on their
combined endpoint weights. It also proves associativity, so the final law is
independent of the recursive binary-tree parenthesization. This closes the
paper's incremental-uniform-selection argument for positive completed
subtrees. The full standard-NUTS trace still has to encode and reverse skipped
zero-eligible subtrees, U-turn continuation flags, and the outer doubling
stopping decisions.

Extended the streaming merge to all nonnegative eligible counts. A zero-count
subtree may carry an arbitrary dummy representative law, but Lean proves it is
ignored whenever its sibling has positive count; two zero-count subtrees keep
only a semantically dead dummy. The total merge is associative across every
zero/positive combination. Its mass theorem permits zero-count endpoint
weights and proves that any positive combined subtree still has exactly the
normalized union law. Thus zero-eligible/skipped `BuildTree` branches are no
longer an open candidate-selection issue. The remaining standard-NUTS work is
the complete trace reversal for continuation/U-turn flags and the outer
state-dependent stopping sequence.

Formalized the completed-tree combinatorics used by the paper's condition C.4
argument. The actual recursive binary encoding gives an equivalence between
height-`d` Boolean direction traces and the `2^d` possible initial-leaf
locations. Therefore every leaf has a unique trace reconstructing the same
completed tree and every such trace has probability `2^-d`. Lean constructs
an endpoint-dependent permutation exchanging the two compatible rerooted
traces and proves exact construction-mass preservation. Deterministic
`CompletedTreeStoppingData` records the first continuation depth at every
root; its admissible roots are exactly those that survive through the full
completed depth, and all admitted rerootings retain the common construction
mass. The remaining algorithm-specific step is to prove that the concrete
recursive divergence/U-turn flags compute this stopping data and that the
accepted final-doubling subset matches its admissible roots.

Added the exact Boolean control flow of the recursive stopping computation.
`NUTSBuildFlagTree` records leaf divergence/slice continuation, both recursive
children, and each join U-turn check; its returned continuation flag is their
conjunction. `truePrefixLength` models the outer loop's first failure and is
proved bounded by the maximum depth, reaching full depth exactly when every
outer flag succeeds. Per-root arrays of these recursive trees now construct
`CompletedTreeStoppingData`, with admissibility equivalent to success of every
required call. A failed final call is explicitly excluded, while a successful
one is included. The existing `RecursiveBarrierTree` is connected to this
control flow, and Lean proves its recursive call succeeds exactly when none of
its completed joins is blocked. The remaining standard-NUTS instantiation is
to show that the production trajectory builder's actual divergence and vector
endpoint tests produce these per-root flag trees and the same retained
endpoint weights.

Connected the stopping interface to concrete finite-dimensional phase data.
`RecursivePhaseTree` stores the phase point at every completed leaf and
computes the leftmost/rightmost endpoints returned by recursive `BuildTree`.
Given an executable leaf slice/divergence predicate, it constructs the exact
flag tree whose internal checks use the existing Euclidean
`vectorAdjacentUTurn`. Lean proves that the returned continuation bit is true
if and only if every leaf predicate and every recursive endpoint test passes.
Arrays of these concrete phase trees over every possible root and doubling
depth now instantiate `CompletedTreeStoppingData`, with C.4 admissibility
equivalent to all of those concrete checks. Remaining production integration
is to prove that the flat recursive-doubling trajectory implementation builds
these same balanced phase trees and retained endpoint weights, then assemble
the already proved rooted-trace certificate.

Added the flat production trajectory bridge. A `Fin (2^d)` phase array now
unfolds by explicit left/right half indexing into the canonical balanced
`RecursivePhaseTree`; Lean proves the recursion equations and exact `2^d`
leaf count. Per-root arrays of the flat power-of-two segments used at each
outer doubling depth directly instantiate the concrete vector stopping data,
so admissibility is stated without a caller-supplied tree conversion. Slice
eligibility is kept distinct from divergence continuation: each flat endpoint
has an exact zero/one eligible weight, their sum is the returned count, root
retention proves that count positive, and Lean constructs the normalized
retained-endpoint distribution. The remaining NUTS assembly obligation is to
prove the production streaming representative draws refine this normalized
flat law across the outer doubling updates and then discharge the complete
trace endpoint-flow identity.

Closed the mathematical outer streaming-draw refinement. A
`WeightedRepresentative` packages a partial tree's endpoint-weight function,
nonnegative total eligible count, representative distribution, zero-count
behavior, and normalized-mass theorem. The total count-proportional merge is
proved to preserve this invariant even when either or both subtrees are empty;
folding it over all outer doublings therefore returns exactly the normalized
sum of all retained endpoint weights and is reassociation invariant. Flat
power-of-two eligibility segments instantiate the package: positive segments
use `flatEligibleDistribution`, while empty segments carry an explicit dummy
law whose influence is proved zero. The remaining standard-NUTS proof is the
final complete-trace endpoint-flow identity tying rerooted retained weights to
the slice-augmented phase target, plus executable correspondence for the
runtime representative draw.

Closed the complete-tree conditional endpoint-flow theorem. A new
`RerootedTraceCandidateSet` records retained membership on a particular full
trace, membership symmetry under its endpoint-dependent reverse trace, and
equality of the target-mass normalizer. Target-weighted retained endpoints
then satisfy the pointwise flow equation algebraically, and Lean constructs
the normalized `ReversibleTraceSelection` and full factorized rooted sampler.
For any concrete `CompletedTreeStoppingData`, the C.4-admissible root subtype
now instantiates this construction with the exact fair direction law and
completed-tree reroot permutation. The resulting conditional transition has
machine-checked detailed balance and stationarity for every strictly positive
target on those roots. This closes selection conditional on a completed
`B,C`; full original NUTS still requires composing the state-dependent law of
completed trees and slice augmentation (or proving the production multinomial
variant refines this conditional decomposition), plus runtime draw refinement.

Added the outer auxiliary-augmentation theorem in
`Mcmc.Finite.NUTSAugmentation`. `auxiliaryCollapsedKernel` draws an arbitrary
state-dependent finite completed-tree/slice auxiliary, applies its indexed
conditional root kernel, and discards the auxiliary. Pointwise balance of each
unnormalized joint slice proves detailed balance of the collapsed transition;
the weaker summed slice equation independently proves stationarity.
`ConditionalAuxiliaryReversibility` reduces the obligation to reversibility
with respect to the normalized state target on every positive auxiliary
fiber, and proves all terms on zero-mass fibers vanish. The construction is
fully instantiated by an exact conditional-refresh Gibbs sampler for every
finite target and state-dependent auxiliary law. For NUTS, this closes the
general composition theorem from a completed-tree/slice conditional proof to
the marginal state kernel. Remaining algorithm-specific work is to embed each
tree's varying C.4-admissible root subtype into a common phase-state kernel
with the prescribed fallback and verify the production tree law and runtime
draw against that certificate.

Closed the varying-fiber/common-state embedding theorem.
`liftAdmissibleSubtypeKernel` promotes a kernel on one auxiliary's admissible
root subtype to the shared phase state: admitted roots use the subtype kernel
and cannot leave its fiber, while inadmissible roots use an explicit identity
fallback. Lean proves row normalization. `AdmissibleSubtypeFiber` relates the
normalized subtype target to an unnormalized full-state auxiliary-slice
weight; subtype detailed balance then transfers to exact full-state slice
flow, including cross-boundary and outside-fiber zero cases.
`AuxiliarySubtypeFiberCertificate` packages a different admitted predicate and
conditional kernel for every completed-tree/slice auxiliary and now assembles
them into one common-state reversible and stationary sampler through the
outer augmentation theorem. The remaining production-specific NUTS work is
to instantiate these fiber records from the concrete completed-tree data and
target/slice weights and to prove executable representative-draw refinement.

## 2026-08-17: finite completed-tree NUTS fiber instantiation

Closed the remaining finite mathematical instantiation of the varying-fiber
theorem. `completedTreeAdmissibleTarget` normalizes an arbitrary nonnegative
weight over exactly one completed tree's C.4-admissible roots.
`CompletedTreeStoppingData.admissibleSubtypeFiber` installs the previously
proved rooted completed-tree transition on that conditional target and proves
the full-state fiber certificate. A family of these records now constructs
`completedTreeAuxiliarySampler`; Lean proves the resulting common-state kernel
reversible and stationary after the state-dependent completed-tree/slice
auxiliary is discarded. The theorem deliberately exposes its support
conditions: joint slice weight is positive at every admitted root, has a
positive admitted normalizer, and is zero outside C.4. It does not yet prove
that the Julia recursive builder's tree/slice distribution and streaming
representative draw satisfy those conditions; that executable refinement is
the remaining production-NUTS boundary.

## 2026-08-17: generated NUTS eligible-count selection

Made the exact discrete representative rule part of generated IR version 17.
`SelectionPolicy.eligibleCountStreaming` has Lean semantics given by recursive
`WeightedRepresentative.mergeAll`, and its refinement theorem states that the
resulting law is exactly the normalized sum of retained endpoint weights,
including empty intermediate subtrees. The generated dynamic-tree descriptor
now requires this policy. Julia Reference interprets it via local uniform
subtree representatives and count-proportional merges; Optimized independently
draws one ticket from the flattened eligible occurrences. Deterministic trace
tests cover both execution shapes, and empirical/reproducibility tests cover
their common law. This discharges the executable discrete selection rule, not
the floating-point claim that production phase, slice, divergence, and U-turn
callbacks produce the Lean-declared tree auxiliary and eligibility data.

## 2026-08-17: bounded dynamic-tree decision refinement

Added the numerical decision layer between floating-point callbacks and the
ideal completed-tree flags. `SeparatedZeroCertificate` proves a computed sign
equals its ideal sign when an absolute-error interval lies strictly on one side
of zero. `SeparatedComparisonCertificate` composes two operand bounds for
slice/divergence comparisons, and `UTurnDecisionCertificate` composes both
endpoint dot-product signs. A structural theorem lifts pointwise leaf and
endpoint agreement through the full recursive `NUTSBuildFlagTree`, so its
continuation result agrees exactly. Julia mirrors these execution-specific
certificates with BigFloat checks and tests stable negative/positive,
two-sided comparison, U-turn, and exact-boundary rejection cases. As elsewhere
in the numerical layer, supplied ideal values and analytic bounds remain proof
inputs; these records do not establish arbitrary callback or platform error
bounds by observation alone.

## 2026-08-17: compositional vector U-turn bounds

Removed the need for an opaque endpoint-dot error premise.
`endpointDot_approximates` derives the error of each Euclidean U-turn dot
product from componentwise left/right position and momentum bounds, following
the exact subtraction, multiplication, and finite-sum expression.
`roundedEndpointDot_approximates` then composes an explicit bound for the
backend's final floating-point arithmetic/reduction. A
`VectorUTurnDecisionCertificate` packages both endpoint momenta and derives
the scalar sign certificates used by the recursive-tree theorem. Julia mirrors
the formula, checks every component against its supplied BigFloat ideal,
requires a separate reduction-rounding budget, and exposes a fail-closed
decision returning `nothing` at ambiguous margins. The trajectory wrapper
constructs this evidence for every adjacent endpoint pair and returns the full
Boolean barrier vector only when every edge is stable. This advances numerical
composition but still treats ideal phase endpoints and their analytic error
bounds as external witnesses.

## 2026-08-17: bounded NUTS leaf and completed-tree decisions

Connected bounded Hamiltonian evaluations to the two distinct leaf bits in
Algorithm 3. `NUTSLeafEnergyCertificate` proves strict log-slice eligibility
and divergence continuation agree with ideal arithmetic from explicit
log-slice, energy, maximum-energy-error, and threshold-reduction bounds. The
strict convention deliberately leaves equality uncertified; an endpoint may
be ineligible while continuation remains true. Leaf and U-turn certificates
now automatically establish the tree-local `DecisionsAgree` proposition, so
Lean proves the entire computed recursive flag tree equals the ideal tree.
Julia's `NUTSCompletedTreeCertificate` packages all visited leaves and joins
and returns their eligible, continuation, and U-turn vectors only when every
comparison is stable. Analytic construction of the ideal phase trajectory and
Hamiltonian bounds remains a separate backend obligation.

## 2026-08-17: leapfrog endpoint to NUTS phase adapter

Connected the existing HMC numerical endpoint interface directly to dynamic
tree decisions. `VectorApproximates.at` extracts scalar coordinate bounds from
the list-level leapfrog certificate. `CertifiedLeapfrogPhaseEndpoint` reindexes
certified position and momentum lists onto one declared finite dimension, and
`CertifiedLeapfrogPhaseTrajectory` stores a common-dimension bounded phase
array. Two adapted endpoints now construct the previously proved vector U-turn
certificate using only strict separation premises. Lean proves its computed
and ideal bits are exactly `vectorAdjacentUTurn` on the corresponding phase
pairs, then proves those bits equal. This closes the interface adapter; a
concrete Float64 backend must still provide the per-step error recurrence,
Hamiltonian evaluation bounds, and final reduction bounds for every generated
endpoint.

## 2026-08-17: concrete leapfrog error recurrence

Instantiated the previously abstract trajectory error model for standard
Euclidean kick-drift-kick leapfrog. `EuclideanLeapfrogErrorParameters` records
nonnegative step magnitude, gradient Lipschitz/evaluation error, and separate
half-kick and drift rounding budgets. Lean defines the half-step, position,
and final-momentum recurrence and proves both propagated errors nonnegative.
`LeapfrogTrajectoryErrorCertificate` requires each stored endpoint bound to
lie below the corresponding recurrence iterate; `scheduledEndpoint` safely
widens it to that budget, and the dynamic-tree adapter turns the entire
schedule into common-dimensional certified phases. Julia evaluates the same
recurrence in BigFloat and tests nonnegativity, schedule length, and invalid
parameters. This is a proved composition rule, not evidence that arbitrary
Float64 gradients or arithmetic satisfy the supplied local constants.

## 2026-08-17: primitive leapfrog operation certificates

Reduced the recurrence premise to operation-local witnesses.
`roundedAffineUpdate_approximates` composes bounded base/direction operands, a
coefficient-magnitude bound, and a final rounding witness for
`base + coefficient * direction`. A
`EuclideanLeapfrogCoordinateCertificate` records bounded current/next gradient
evaluations and the rounded first half-kick, drift, and second half-kick.
Applying the affine lemma three times proves its output position and momentum
meet exactly the concrete recurrence budgets. The result converts to the
existing one-dimensional `LeapfrogStepCertificate`, so all trajectory and NUTS
adapters apply unchanged. Julia checks the same primitive expressions in
BigFloat and confirms its derived errors match the recurrence schedule. The
ideal gradients, Lipschitz constant, and local rounding budgets remain trusted
analytic/backend inputs.

The primitive construction is now dimension-generic and recurrence-indexed.
`VectorApproximates.ofFn` aggregates the coordinate theorems into a vector
endpoint certificate. `EuclideanLeapfrogVectorTrajectoryCertificate` stores
an initial endpoint plus a finite family of vector-step witnesses whose input
errors equal the preceding recurrence schedule; Lean forgets the primitive
details into `LeapfrogTrajectoryErrorCertificate`, then converts it directly
to `CertifiedLeapfrogPhaseTrajectory` for the NUTS decision layer. Julia's
vector checker validates every coordinate against the same schedule. This
error-only sequence remains useful as a projection, while the linked wrapper
below discharges its separate state-threading obligation.

## 2026-08-17: linked primitive leapfrog trajectories

Added the missing sequential invariant to primitive multi-step certificates.
`LinkedEuclideanLeapfrogVectorTrajectoryCertificate` requires each vector
step's computed and ideal position and momentum inputs to equal the preceding
stored endpoint. It retains the recurrence proof and has a direct adapter to
the phase trajectory consumed by bounded NUTS decisions. Julia mirrors this
as an exact replay check: a collection of individually valid primitive steps
is rejected if its initial state or any successive computed/ideal state does
not connect. Positive, wrong-initial-state, and broken-successor tests cover
the boundary. Concrete gradient callback, arithmetic-reduction, libm, and
platform-specific budgets remain explicit backend obligations.

## 2026-08-17: linked trajectory to recursive NUTS trace

Closed the theorem-level composition between bounded integration and recursive
stopping. Given one common certified phase trajectory, bounded leaf-energy
witnesses, and strict U-turn margins, Lean now proves equality of the complete
computed and ideal `NUTSBuildFlagTree`, not only its individual callback bits.
A direct wrapper starts from the primitive recurrence certificate with exact
successive-state linkage. This also clarifies the remaining boundary: finite
state-dependent auxiliary-slice reversibility and marginal stationarity are
already proved in `NUTSAugmentation`; what is still absent is a refinement
theorem identifying a production recursion's generated auxiliary distribution
with that finite completed-tree law, plus concrete callback/platform budgets.

## 2026-08-17: generated recursive direction law

Made the randomized recursion's auxiliary distribution part of the generated
contract instead of a Julia-side convention. IR version 18 adds the
`fair-direction-bits` trace policy; the Julia decoder and runtime reject any
other policy. `CheckedRecursiveDoublingProgram.interpret` denotes the exact
uniform distribution over all finite direction traces followed by the proved
global checked-or-identity row kernel. Lean expands its transition probability
to that literal finite mixture and proves stationarity for every candidate-row
builder. The remaining cross-language obligation is now narrower and explicit:
show that the runtime recursion produces the declared candidate function for
each trace (subject to its bounded numerical callback certificates).

## 2026-08-17: executable recursive candidate rows

Replaced the abstract recursive candidate function with an executable Lean
definition. It models zero-based closed intervals, depth-indexed powers-of-two
expansion, boundary stopping, recursive completed-subtree U-turn exclusion,
completed-join exclusion, and permanent early stopping. A native-decided Lean
regression recovers the same four-state row used by the seven-point Julia
boundary example. Julia Reference now contains a direct interpreter of these
rules; the generated runtime path uses it, while the previous manual builder
is retained independently for conformance checks. Boundary and curved U-turn
examples agree exactly. This is strong implementation evidence, but not a
machine-checked Julia extraction theorem; numerical dot-product agreement also
still depends on the existing strict-margin certificates and backend budgets.

## 2026-08-17: recursive candidate-row numerical refinement

Lifted bounded U-turn agreement through the newly executable recursive row
builder. `recursiveDoublingCandidateRow_congr` proves pointwise equality of
turn callbacks makes every interval expansion, early stop, and final candidate
row identical for every root and direction trace. The phase-trajectory theorem
then derives that callback equality from componentwise endpoint bounds and
strict dot-product margins. Consequently the computed and ideal recursive
candidate rows—not only their flag trees—are now machine-checked equal at the
declared numerical boundary. Concrete backend budgets and machine-checked
Julia extraction remain separate obligations.

## 2026-08-17: end-to-end recursive-kernel refinement

Lifted candidate-row agreement through the complete generated dynamic-tree
semantics. `CheckedRecursiveDoublingProgram.interpret_congr` transports exact
row-family equality through the fair direction-bit mixture, global reroot
check, checked endpoint selection, and identity fallback.
`CertifiedLeapfrogPhaseTrajectory.recursiveDoublingKernel_eq_ideal` then uses
the existing componentwise leapfrog bounds and strict endpoint margins to
identify the computed recursive kernel with its ideal-real counterpart. The
remaining production boundary is concrete backend budgets and a
machine-checked refinement/extraction argument for the Julia interpreter, not
an unproved gap between certified callback bits and the full Lean kernel.

## 2026-08-17: continuous history-dependent warmup certificates

Connected finite warmup to the general proxy/containment interface.
`proxyCertificate_of_freezesAfter` packages an arbitrary history-dependent
burn-in followed by a uniformly minorized frozen kernel: the exact frozen-tail
law has zero approximation error and its containment error is the explicit
geometric Doeblin remainder. The existing setwise convergence theorem now
factors through this certificate.

Added `ContinuousWarmupAdaptation`, a real-valued client whose tuning parameter
is `1 +` the empirical second moment of the complete trajectory during warmup
and a fixed production value afterward. Lean proves measurability, demonstrates
that distinct continuous histories select distinct scales, proves exact
freezing, constructs the proxy certificate for any jointly measurable sampler
family, and derives post-warmup setwise convergence when the frozen section
supplies invariant-target and minorization proofs. This is a concrete
continuous history-dependent warmup result; it does not discharge the stronger
never-freezing continuous adaptation milestone.

## 2026-08-17: partially mixing Feynman--Kac contraction

Added the first nondegenerate partial-refresh client alongside the existing
complete-refresh SMC model. Its mutation kernel refreshes from a fixed finite
law with probability `p` and otherwise retains the current state. Lean proves
stationarity, the exact one-step normalized Feynman--Kac update, and the exact
pointwise error identity with contraction factor `1 - p`; iteration gives the
closed form `(1 - p)^t` at every horizon. This supplies an actual strict model
contraction rather than assuming one abstractly. The corresponding bootstrap
population still contains multinomial-resampling and retained-ancestry
dependence, so deriving its affine MSE recursion and particle-count-uniform PG
mixing remains open.

## 2026-08-17: uniform particle bounds under partial refresh

Closed the population-level step left open above. For constant potential and
partial-refresh mutation, Lean derives the conditional observable mean, the
exact affine normalized-target expectation, and a conditional particle-average
MSE inequality. The inherited squared error contracts by `(1-p)^2`; fresh
multinomial-ancestry and propagation noise contributes at most
`8 ‖f‖∞²/N`. Integrating over the actual preceding bootstrap population gives
the required affine recurrence. For every positive `p`, the generic strict
contraction theorem now yields one explicit `C/N` bound simultaneously for
all time horizons and all particle counts. This population is not iid: the
proof retains both multinomial resampling and the identity mutation branch.
Particle-count-uniform particle-Gibbs mixing is still a separate kernel-level
obligation.

## 2026-08-17: particle-count-uniform particle-Gibbs mixing

Closed that kernel-level obligation at every fixed Feynman--Kac horizon.
`particleGibbsScheduleCoefficient_mono` proves that a fixed nonnegative
penalty schedule's refresh coefficient improves with the number of ordinary
particles. Consequently the backward-potential full-support certificate at
the smallest supported count supplies one geometric total-variation bound
simultaneously for every `N ≥ 2`; Lean also proves this common rate tends to
zero with the PG iteration count. This is uniformity in particle count for a
fixed model and horizon. The penalty list grows with the Feynman--Kac horizon,
so no horizon-uniform mixing rate or joint horizon/count asymptotic is claimed.

## 2026-08-17: multidimensional Gaussian BPS clock reduction

Started the concrete partial inverse clock for standard-Gaussian BPS in an
arbitrary finite dimension. The target normal is now packaged as measurable
bounce data. Along a linear ray, Lean proves the canonical rate is exactly
`max 0 (a + t b)`, where `a = ⟨v,x⟩` and `b = ‖v‖²`; nonzero velocity gives
`b > 0`. The closed-form wait
`(sqrt((max 0 a)^2 + 2 b h) - a) / b` is defined, proved positive for positive
hazard, transported to `NNReal`, and proved to satisfy the endpoint
positive-part-square identity. The remaining clock-instantiation step is the
scalar interval-integral identity equating accumulated `max 0 (a + tb)` with
that square increment. Almost-sure finite-horizon completion remains a later
nonexplosion argument and is not inferred from this algebra.

## 2026-08-17: exact multidimensional Gaussian BPS partial inverse

Closed the scalar calculus and clock-packaging obligations. Lean proves the
interval integral of `max 0 (a + bt)` for `b > 0` by splitting at its unique
zero and identifying the affine antiderivative. Substitution of the
closed-form wait gives exactly the supplied integrated-hazard mark.
`standardGaussianBPSPartialInverseHazardData` now packages the measurable
standard-Gaussian bounce, active predicate, wait, positivity, inverse, and
inactive proof in every finite dimension. Zero velocity with positive mark is
the certified no-event branch; the zero mark remains active, avoiding the
logically impossible strict inequality `0 < 0`. This completes the concrete
partial inverse clock, but not `CompletesFiniteHorizons`: almost-sure exclusion
of infinitely many bounces in finite time remains the separate nonexplosion
theorem.

## 2026-08-17: practical-slice stratum measure preservation

Upgraded allocation rerooting from a finite-sum identity to preservation of
counting measure on the discrete valid-allocation strata. Combined it with
Haar alignment translation and the accepted old/proposal affine reversal.
`successfulTraceStratumReverse_measurePreserving` now preserves the complete
restricted product law on a fixed successful stopped-bracket stratum, while
the weighted variant preserves any measurable symmetric old/new trace
likelihood, including the shape established by the shrink-trace symmetry
theorems. The remaining global step is a dependent sum over offset-derived
integer shifts, stopped brackets, and rejected-trace lengths; this commit does
not collapse those varying types into a fictitious ordinary product.

## 2026-08-17: offset-dependent practical-slice strata

Formalized the missing dependence between the continuous alignment and finite
allocation type. `alignmentShiftStratum` is the measurable set of Haar offsets
with one integer grid displacement. Lean proves these strata are disjoint,
cover the alignment circle, and their restricted measures sum to Haar volume.
Alignment reversal maps the `shift` stratum exactly onto `-shift`; composing
that restricted map with allocation rerooting and accepted-point reversal
gives both restricted-volume and symmetric-density preservation on the true
dependent stratum. The unresolved gluing is now confined to the sigma-type of
varying rejected-point sequence dimensions and stopped brackets, rather than
the offset/allocation dependence.

## 2026-08-17: variable-length rejected slice traces

Introduced the actual sigma type `RejectedSequence = Σ n, Fin n → ℝ`, so a
successful shrink trace retains its dimension instead of padding to a fixed
budget. The dependent stratum reversal is the identity on this sequence and
therefore preserves any s-finite rejected-sequence law while simultaneously
rerooting alignment, allocation, and accepted-point coordinates. A generalized
two-space density transport lemma attaches different forward and reverse
trace likelihoods whenever the target density after reversal equals the source
density. This is precisely the pointwise obligation supplied by the existing
successful stepping-out/shrinkage symmetry theorem. The remaining global
construction is the measure sum across integer shifts and stopped brackets,
followed by the auxiliary-kernel invariance wrapper.

## 2026-08-17: global practical-slice allocation law

Replaced the remaining countable shift/allocation gluing obligation by an
equivalent non-dependent ambient construction. The runtime integer alignment
shift is measurable and cancels exactly under rerooting. Translation of the
integer allocation by this offset-dependent shift is a skew product preserving
Haar alignment volume times counting measure. Lean restricts that ambient law
to exactly the event on which both allocations lie in the configured finite
range and proves reversal exchanges the forward and reverse restrictions.

`globalRejectedTraceReverse_measurePreserving` composes this result with an
arbitrary s-finite variable-length rejected-sequence law and the restricted
accepted-proposal reversal. Its density variant transports distinct forward
and reverse likelihoods from their pointwise reversal equality. This theorem
has genuinely combined every integer shift and allocation stratum; varying the
stopped bracket and connecting the resulting trace law to the auxiliary slice
kernel remain separate obligations.

## 2026-08-17: varying stopped brackets and dependent traces

Added the measurable carrier of nondegenerate stopped brackets and proved that
the bracket-dependent accepted old/proposal affine reversal preserves any
s-finite bracket law times planar Lebesgue measure. Its successful-slice event
is measurable and invariant under reversal, so the restricted law is also
preserved. Composing this fiber theorem with the global alignment/allocation
law and the variable-length rejected sequence yields one trace theorem across
all discrete shifts, allocations, rejected lengths, and varying brackets, plus
the corresponding forward/reverse density transport.

The slice-kernel infrastructure now supports a trace *kernel* depending on
height and current state, rather than only an independent constant trace law.
Preservation of the resulting dependent joint law implies horizontal
invariance and then weighted-target slice invariance; a guarded theorem gives
the checked identity fallback from preservation on the successful restriction.
This is the correct auxiliary-kernel bridge for practical stepping out. The
remaining client obligation is construction of the measurable runtime trace
kernel and equality of its joint law with the global trace density above.

## 2026-08-17: normalized practical trace-kernel carrier

Added a reusable normalized-density construction for state-dependent trace
kernels. A measurable everywhere-finite density integrating to one produces a
Markov kernel, and its composition product with the auxiliary state law is
definitionally identified with the product base measure carrying that density.
An end-to-end theorem feeds precisely that measure-preservation obligation into
the dependent-trace slice invariance wrapper.

Defined the correctly factored runtime practical trace: the current point
belongs only to the `(height, current)` auxiliary state, while the trace stores
the variable rejected sequence, grid alignment/allocation, stopped bracket,
and final uniform fraction. Its augmented reversal is measurable, turns that
fraction into the next state, records the reverse fraction, reroots the grid,
and is proved involutive. This avoids an invalid duplicated-current encoding,
which would impose equality on a planar Lebesgue coordinate and hence describe
a measure-zero event. The next client step is the concrete normalized runtime
density and the log-height coordinate law used by `run`.

## 2026-08-17: executable log-height auxiliary law

Formalized the exact auxiliary coordinate used by the runtime rather than
routing it indirectly through a positive raw-height variable. Conditional on
state `x`, the threshold density is `exp(t - logDensity x)` on
`t ≤ logDensity x`; Lean proves its Lebesgue integral is one and constructs the
corresponding Markov kernel. Multiplication by the target density cancels the
state log density, yielding the joint density `exp t` below the log graph.
Consequently any horizontal transition preserving the swapped log-under-graph
law preserves the target with density `exp ∘ logDensity`.

The normalized dependent-trace theorem now has a log-height specialization,
and `practicalSliceSampler` instantiates it with the non-duplicating runtime
trace and augmented reversal. Its final exact-invariance theorem exposes only
the concrete trace-density obligations: measurability, finiteness,
normalization, and preservation of the complete joint law.

## 2026-08-17: primitive practical trace density

Constructed the honest base measure for variable-length rejected sequences as
a countable sum of finite-dimensional Lebesgue fibers. Lean proves it is
s-finite and that nonnegative integration decomposes into the expected sum of
`Fin n → ℝ` integrals. The primitive runtime trace base adds Haar alignment,
integer counting measure, and the final real proposal coordinate.

Corrected the runtime factorization before claiming normalization: the stopped
bracket is a deterministic function of height, current state, alignment,
allocation, and target evaluations, so an independent Lebesgue bracket density
would be mathematically wrong. The new primitive carrier omits that bracket;
`runtimeSteppedBracket`, `runtimeFinalBracket`, and `runtimeAcceptedPoint`
derive it. `runtimeTraceDensity` now states the actual finite-allocation and
success guards and multiplies the successive rejected-point conditional
densities. It is proved everywhere finite and zero on invalid allocations.
Joint measurability, normalization, and the derived-bracket augmented reversal
remain the next proof obligations.

## 2026-08-17: exact finite-budget fallback mass

Corrected the normalization target for bounded shrinkage. The successful trace
density is generally only a subprobability: rejecting through the entire
finite attempt budget returns the current point and carries the missing mass.
The reusable `CompletedTrace` construction embeds successful traces into a sum
type and adds one exhaustion atom with density `1 - successfulTraceMass`.
Lean proves this completed density measurable whenever the success density is,
proves it integrates to one under the exact subprobability bound, and constructs
the resulting Markov trace kernel.

`completedRuntimeTraceKernel` instantiates that construction with the concrete
primitive practical trace base and density. Its remaining client hypotheses
are now accurately stated as joint measurability and success mass at most one;
normalization is no longer incorrectly demanded of the success branch alone.

## 2026-08-17: practical-trace measurability foundations

Started the concrete measurability proof at the recursive algorithm boundary.
For every fixed expansion budget, both left and right stepping-out scans are
proved jointly measurable in the log threshold and current endpoint under a
measurable log density. These lemmas compose with the measurable circle
coordinate to prove the derived stopped bracket measurable for every fixed
integer allocation. The remaining assembly uses the discrete allocation
partition and the finite-dimensional rejected-point recursion before lifting
through the variable-length sigma measure.

## 2026-08-17: fixed-fiber practical trace measurability

Introduced finite-vector versions of rejected-bracket replay and its successive
conditional likelihood. They are proved equal to the existing `List.ofFn`
semantics and jointly measurable in all continuous inputs by induction on the
rejected length. Combining these results with fixed-allocation stopped-bracket
measurability proves `runtimeTraceDensity` measurable on every pair of fixed
rejected dimension and integer allocation fibers. The remaining assembly is
now purely the countable/disjoint-union measurable-space lift.

## 2026-08-17: bounded-length successful trace kernel

Added the missing `maxShrink` guard to `runtimeTraceDensity`. Without
`rejectedLength < maxShrink`, the density incorrectly assigned success mass to
arbitrarily long rejection sequences and the desired subprobability statement
would generally be false.

Lifted fixed-fiber measurability across all integer allocations using their
discrete measurable structure. Rather than assuming a product/sigma
reassociation theorem, the actual successful runtime kernel is constructed as
the finite sum over `Fin maxShrink` of fixed-length density kernels, each
mapped into the variable-length carrier. Lean proves every component and the
finite sum s-finite. This gives a genuine measurable kernel for exactly the
allowed success lengths; the next obligation is its row mass at most one.

## 2026-08-17: practical trace mass-factor normalization

Closed the independent factors in the successful row-mass calculation. The
integer allocation density `1 / intervals` integrates exactly to one over
counting measure on `0,…,intervals-1` whenever `intervals > 0`; the proof
accounts explicitly for the integer interval cardinality and the nonzero
normalizer. Haar alignment was already a probability measure. A separate
Lebesgue lemma proves that intersecting the final uniform fraction with any
acceptance event contributes at most unit mass. The remaining mass proof is
therefore the telescoping finite shrink recursion: acceptance at one of the
allowed rejected lengths plus exhaustion has total mass one.

## 2026-08-17: abstract bounded-shrink telescoping foundation

Factored the remaining row-mass argument into an algorithm-independent finite
recursion and one-dimensional interval geometry. `boundedShrinkSuccessMass`
adds immediate acceptance to the integral of rejection followed by the
remaining budget; Lean proves by induction that it is at most one whenever
each one-step accept/reject partition has mass at most one. Separately, Lean
proves the exact pushforward identity taking Lebesgue measure on `[0,1)` under
`u ↦ left + (right-left)u` to normalized Lebesgue measure on every positive
bracket. The next step is to instantiate the one-step partition with the
target's superlevel set and identify the fixed-length trace sum with this
recursion.

## 2026-08-17: concrete shrink accept/reject partition

Instantiated the one-step mass law for practical shrinkage. Lean now defines
the normalized bracket law, proves it has unit mass, and proves exactly that
the target superlevel acceptance mass plus the integral of the strict-sublevel
rejection density is one on every positive bracket. A validity invariant says
that the current accepted point remains in the bracket; nonzero rejection
branches preserve it, while zero-density malformed coordinates require no
successor obligation. Stepping out from any circle alignment and integer
allocation establishes this invariant whenever `width > 0` and the sampled
height is below the current log density. Consequently the abstract bounded
recursion has successful mass at most one for every runtime stepping-out
bracket. Remaining is the finite-dimensional Fubini identification between
that recursion and the sum of the concrete `Fin n → ℝ` trace fibers.

## 2026-08-17: finite-dimensional shrink fibers equal the recursion

Closed the rejected-vector Fubini bridge. A reusable Tonelli theorem splits
`Fin (n+1) → ℝ` under product Lebesgue measure into its head and `Fin n`
tail. The runtime final-fraction indicator is measurable and its integral is
proved equal to normalized superlevel mass on every positive bracket. Lean
then proves the exact recurrence for `fixedShrinkSuccessMass`: the
`n+1`-rejection fiber is one rejected-point density times the `n`-tail fiber
in the updated bracket. Fixed masses are measurable in the bracket, so finite
sums commute with the rejection integral. Consequently, the sum of every
fiber `n < maxShrink` equals `boundedShrinkSuccessMass` exactly and is at most
one from every valid stepped-out bracket. Remaining for the concrete runtime
kernel is lifting this bound through the normalized integer allocation and
Haar alignment factors.

## 2026-08-17: completed practical runtime trace probability kernel

Lifted the finite shrink bound through every remaining runtime coordinate.
Lean integrates the final fraction, the rejected vector, the finite length
sum, integer allocation, and Haar alignment in their actual product measures;
Tonelli rearrangements are proved explicitly. The total mass of
`successfulRuntimeTraceKernel` is thereby at most one whenever the augmented
slice state is valid, `width > 0`, and `intervals > 0`. A measurable piecewise
guard makes success mass zero outside the valid height/state domain without
changing any trace emitted after the certified log-height draw.
`completedRuntimeTraceKernelFromFibers` then maps successful traces into the
left branch and assigns the exact missing mass to one right-branch exhaustion
atom. Lean proves this completed kernel is a Markov kernel on the full ambient
state space. Remaining practical-slice work is the primitive derived-bracket
reversal and completed joint-law preservation.

## 2026-08-17: bracket-free primitive runtime reversal

Defined `primitiveRuntimeAugmentedReverse` directly on the coordinates the
runtime consumes: rejected points, Haar alignment, integer allocation, and
the final unit fraction. It deterministically reconstructs the final bracket,
turns the fraction into the accepted state, reroots alignment/allocation, and
records the old state as the reverse fraction. The existing dependent
allocation theorem is specialized to the unrestricted runtime integer on the
global valid-allocation event. Together with same-side rejected replay, Lean
proves that the reverse execution derives exactly the same final bracket.
`PrimitiveRuntimeSuccess` packages the actual successful-trace obligations;
from it Lean derives reverse-fraction validity, involutivity of the primitive
rerooting, and exact forward/reverse equality of `runtimeTraceDensity`.
Remaining is lifting this pointwise certificate through the completed
successful/exhaustion joint law.

## 2026-08-17: primitive runtime success support

Closed the support side of the bracket-free reversal. Nonzero runtime trace
density now exposes the complete semantic rejected-point trace, while a
valid rejected trace preserves the old state in every shrinking bracket and
forces every rejected point to remain on the same side of the accepted state.
Finite stepping-out bounds prove that membership of the accepted state in the
stopped bracket yields a valid reverse integer allocation. New crossed-grid
lemmas show that every intervening grid endpoint passed the strict superlevel
test; this discharges all four signed interior hypotheses of stopped-bracket
rerooting. Consequently, for positive width and a valid current slice state,
nonzero density automatically constructs `PrimitiveRuntimeSuccess`—including
derived-bracket reversal, reverse-fraction validity, involution, and exact
forward/reverse density equality. The remaining obligation is measure-level
preservation of the successful joint law and its completion by the explicit
exhaustion atom.

## 2026-08-17: fixed-dimensional practical joint-law reduction

Lifted the intrinsic runtime support theorem to every fixed rejected-sequence
dimension. The derived final bracket, accepted state, primitive rerooting, and
successful support set are now all proved measurable on
`FixedRuntimeTrace n`. On that set the fixed transform is an involution and
preserves the exact runtime likelihood without any client-supplied replay
certificate. A generic guarded-with-density theorem proves that an identity
fallback automatically preserves the full weighted law once the raw base law
is preserved on the successful restriction; no separate exhaustion-mass
symmetry argument is needed. The resulting
`fixedGuardedRuntimeReverse_withDensity_measurePreserving` theorem isolates
the remaining core precisely as unweighted product-measure preservation of
the finite-dimensional rerooting. Summing those strata and connecting them to
the completed trace kernel remain subsequent steps.

## 2026-08-17: countable practical replay stratification

Added reusable measure-preservation gluing theorems for countable disjoint
restrictions, including a source/target version whose replay signatures may
change under reversal. Every bounded expansion endpoint is now proved to be
an integral number of widths from its initial endpoint, with a consumed count
within budget and uniqueness for nonzero width.

For each rejected length, `FixedRuntimeReplaySignature` records the integer
allocation and rerooting shift, actual left/right consumed counts, and every
rejected-point side decision. Lean proves that the associated replay pieces
are measurable, pairwise disjoint for positive width, and have union exactly
the successful support. Successful fixed rerooting maps support back into
support, translates allocation by the recorded shift, negates the reverse
shift, and preserves every rejected-side decision. The remaining stratum
calculation is the translated expansion-count formula and affine
product-volume preservation on each source/target replay pair; the countable
gluing theorem can then assemble the raw base law required by the prior
weighted lift.

The translated expansion-count formula is now closed. Rather than assuming
the signed counts are nonnegative, Lean extracts the natural-number counts
actually consumed by the reverse execution and uses stopped-bracket equality
plus nonzero width to identify them with `leftConsumed + shift` and
`rightConsumed - shift`. Thus rerooting maps every source replay piece into
its complete reversed signature, including both endpoint formulas. On every
inhabited piece signature reversal is involutive, and the runtime rerooting is
packaged as a measurable equivalence between the paired subtype carriers.
The remaining local obligation is equality of the restricted raw product
measures under this measurable equivalence; countable gluing and density
lifting are already available once that affine measure calculation is proved.

## 2026-08-17: accepted-point/grid skew-product volume law

Factored the local affine measure calculation into its two canonical pieces.
For a fixed nondegenerate bracket, `acceptedGridReverse` first applies the
unit-Jacobian old-point/fraction exchange and then reroots the Haar alignment
and integer allocation using the exchanged endpoints. Lean proves the
combined map preserves `Lebesgue² × Haar × count` by a parameterized
skew-product theorem—not by assuming independence of the state-dependent grid
translation. `contextualAcceptedGridReverse_measurePreserving` further lifts
this result through any measurable retained outer context supplying a
nondegenerate bracket.

The remaining replay-piece bridge is now geometric: introduce the invariant
maximal-left grid anchor, identify the original old/alignment/allocation chart
with the appropriate anchored cell restriction, and express the final bracket
as a function of the retained anchor, rejected vector, and replay signature.
The contextual skew-product law can then be restricted to the paired source
and reverse cells and glued over signatures.

## 2026-08-17: invariant practical grid-anchor chart

Introduced `maximalLeftGridAnchor`, the maximal-left endpoint of the infinite
aligned grid after absorbing the integer allocation coordinate.  The concrete
Haar-alignment/integer-allocation rerooting preserves this anchor exactly.
The fixed-dimensional primitive reversal inherits that invariant, and on each
replay signature Lean now rewrites the stopped stepping-out bracket as an
explicit affine function of only the anchor, allocation, and consumed left and
right expansion counts.

The coordinate map replacing the current state by this anchor is itself proved
measure preserving for `Lebesgue × Haar × count`.  The proof is a measurable
triangular translation, conjugated by product swaps, so it does not require an
unavailable special theorem for the `[0,1)` coordinate chart.  It is packaged
as a measurable equivalence with a measure-preserving inverse and lifted
through an arbitrary retained s-finite replay context.  What remains in the
local practical-slice argument is to identify each replay-piece restriction in
that contextual chart and conjugate the accepted/grid skew-product theorem
across the paired restrictions.

## 2026-08-17: signature-controlled practical shrink geometry

Separated shrink replay from the current-state comparison by introducing an
explicit Boolean side vector.  Lean proves that supplying the actual side of
every rejected point reproduces the original shrink recursion exactly, and
that the side-controlled recursion is measurable.  Therefore, on a fixed
replay signature, both the stopped bracket and final bracket are measurable
functions solely of the invariant grid anchor and retained rejected vector;
the old state and final fraction no longer enter the bracket family.

For every inhabited replay signature, its translated reverse signature now
defines exactly the same affine stopped bracket for every anchor, and hence the
same final bracket for every rejected vector.  This upgrades the prior
pointwise stopped-bracket equality into the context-wide identity required by
the paired restricted-measure proof.  The remaining local step is the explicit
reassociation/conjugacy of the raw runtime product measure with this anchor
context and the accepted-point/grid fiber.

## 2026-08-17: Haar/counting real-line tiling

Proved the missing measure identity behind the practical grid chart.  The
right-closed fundamental coordinate supplied by mathlib maps Haar volume to
Lebesgue measure on `(0,1]`; translating it by every integer tile and summing
counting measure gives all of real-line Lebesgue measure exactly.  The proof
uses the pairwise-disjoint `Ioc` tiling rather than an informal density
argument.

The executable semantics uses `[0,1)`, so Lean also proves that the two circle
coordinates agree away from the quotient origin, proves that origin is Haar
null from the right-closed measure-preserving chart itself, and transports the
map law across the resulting almost-everywhere equality.  Consequently
`alignmentCountingCoordinate_measurePreserving` now states the exact required
law for the actual runtime coordinate
`alignmentCoordinate offset + allocation`.  This tiling is also packaged as a
measurable equivalence whose inverse takes fractional part and floor.  Scaling
and translating it at a fixed grid anchor is proved to yield
`ofReal |width⁻¹| • Lebesgue`, and substituting the actual maximal-left anchor
recovers the current state exactly.  The next step is to conjugate the
signature-controlled accepted-point swap across the paired replay cells.

## 2026-08-17: anchored accepted-grid conjugacy

Completed the algebraic conjugacy underlying each practical replay cell.
Lean proves that alignment/allocation rerooting translates the tiled real
coordinate by exactly `(new-old)/width`.  The fixed-anchor grid coordinate is
packaged as a measurable equivalence to the real current state, and conjugating
the actual grid reroot/reverse-fraction transform through that equivalence is
exactly the already proved planar accepted-proposal reversal.  Hence the
actual fixed-anchor transform preserves `Haar × count × Lebesgue`, including
the width-dependent Lebesgue scaling factor rather than silently treating it
as one.

This preservation theorem is lifted through an arbitrary measurable s-finite
outer context with a measurable nondegenerate bracket family.  A separate
measurable runtime chart now reorganizes
`(threshold,current,rejected,grid,fraction)` as
`(threshold,rejected,anchor; grid,fraction)`.  On every successful replay
signature, Lean proves pointwise that charting the concrete primitive runtime
reversal equals the contextual anchored transform using the
signature-controlled final bracket.  The remaining local obligation is only
the exact product-measure reassociation law for this runtime chart, followed by
restriction and countable gluing.

## 2026-08-17: fixed-length practical joint-law closure

Closed the raw product-measure argument on every fixed rejected-vector length.
The full runtime anchor chart is proved measure preserving by an explicit
composition of product associators, a current/grid-to-anchor/grid triangular
map, and final reassociation.  A measurable globally nondegenerate bracket
extension uses `(0,1)` only outside ordered replay contexts and agrees exactly
with the derived final bracket on successful pieces.

Pulling the safe contextual transform back through the chart gives a global
measure-preserving involution.  Lean proves it equals the concrete primitive
runtime reversal on each successful replay piece, that forward and reverse
signatures induce the same surrogate, and that the preimage of each reversed
piece is exactly its source piece.  Thus the concrete reversal preserves raw
product measure between every inhabited pair.  Summing over the subtype of
inhabited signatures—where reversal is a genuine permutation—proves raw
preservation on the entire fixed-length success set.  The existing likelihood
symmetry then lifts this to the complete weighted fixed-length joint law.

The remaining practical measure assembly is now only the sigma-type sum over
rejected-vector lengths and identification with the already-defined
variable-length successful/completed runtime kernels; the within-length
affine and signature obligations are closed.

## 2026-08-17: finite-dimensional Gaussian BPS nonexplosion

Instantiated the exact partial inverse-integrated-hazard clock for the
finite-dimensional standard-Gaussian Bouncy Particle Sampler with a complete
finite-horizon nonexplosion proof. Lean proves reflection preserves speed,
linear flight controls position growth, and the rate is bounded by an explicit
finite-horizon envelope. The generic inverse-clock layer now proves iid
unit-exponential hazard prefix sums exceed every finite bound almost surely.

For deterministic replay, the potential “remaining time × current rate
envelope” pays every accepted hazard mark and cannot increase after a flight
and bounce. Consequently every finite horizon completes after a finite hazard
prefix almost surely. This proves `CompletesFiniteHorizons`; construction and
measurability of the totalized completed endpoint/kernel are now also closed:
the generic layer measurably selects the first completed prefix, proves the
fallback branch null under `CompletesFiniteHorizons`, and packages the result
as a Markov kernel. Its semigroup and stationarity laws and multidimensional
ergodicity remain separate milestones. The first semigroup boundary law is
closed separately: totalized execution at zero remaining time is pointwise the
initial state, hence the completed zero-horizon kernel is exactly `Kernel.id`.

The positive-time renewal foundation is now checked as well. Finite replay is
stable after its first completed prefix, the selected totalized endpoint
agrees with every completed prefix, and consing a head mark onto a tail is
exactly one capped step followed by tail replay. Reindexing the iid infinite
product proves the first mark and tail have the unit-exponential × iid law.
Together with almost-sure tail completion, these results yield generic
law-level and kernel-level first-step renewal equations, instantiated by the
finite-dimensional Gaussian BPS kernel. The remaining semigroup step is the
residual-clock memorylessness calculation across an arbitrary time split.

The deterministic half of that split is now explicit: the affine Gaussian-BPS
clock coefficients have exact flow-update laws, and Lean proves the integrated
hazard cocycle `A(x,t+u) = A(x,t) + A(flow t x,u)` in both nonzero- and
zero-velocity cases. The remaining local lemma is uniqueness of the positive
closed-form inverse, needed to identify the residual real-time wait after
subtracting the first interval's accumulated hazard.

That local clock obligation is now closed. Lean proves the closed-form
positive inverse is the unique nonnegative time attaining a positive hazard,
accumulation is nonnegative and strictly below the mark at every earlier time,
and the residual mark obtained by subtracting the first interval's accumulated
hazard has inverse wait exactly `originalWait - split` from the flowed state.
The remaining semigroup work is therefore a law-level endpoint decomposition,
not an unproved property of the Gaussian clock.

The boundary survival law is now explicit too. The canonical unit-hazard law
is positive almost surely. For nonzero Gaussian-BPS velocity, Lean proves the
accumulated clock is monotone and that `waitingTime ≤ horizon` is equivalent to
`hazard ≤ A(horizon)`. Consequently the probability of no event before the
horizon is exactly `exp (-A(horizon))`. The first-event renewal API is also
specialized to this full-measure positive-hazard branch, removing the
zero-mark and inactive cases from the remaining time-splice calculation.

The pre-event boundary coupling is now checked pointwise and in law. Explicit
consumed- and residual-hazard definitions identify the residual inverse wait;
flowing by it reaches exactly the same event location and reflected state as
the unsplit clock. Restricting the original mark to survival of the split and
mapping by hazard subtraction yields the unit-exponential law scaled by the
survival mass, and normalization recovers the unit law exactly. The remaining
composition proof must lift this coupling through the random completed-prefix
selector, but no local memorylessness or clock-geometry premise remains.

The random selector is now reduced to countable finite-prefix pieces. Generic
inverse-clock code defines measurable genuine-completion strata, proves them
pairwise disjoint and almost-surely exhaustive, and identifies the totalized
endpoint with the corresponding finite replay on each piece. Positive
horizons cannot occupy count zero; on stratum `n+1`, prefix `n` is still active
and its next capped step finishes. That terminal candidate is either the
no-event branch or has wait exactly equal to remaining time, isolating the
continuous-law boundary-null event needed before countwise gluing.

The base atomlessness input for that null event is now formalized. Every
singleton has zero mass under the canonical unit-exponential hazard law, which
is registered through mathlib's `NullSingletonClass`. Fubini then proves that
an independent head mark almost surely differs from any measurable threshold
computed from the iid tail. The next stratum step is to reindex an arbitrary
terminal coordinate as that independent head while retaining the finite
prefix context that determines its threshold.

That stratum step is now complete. The iid product coordinates are proved
mutually independent through mathlib's infinite-product API; consequently the
first `n` coordinates are independent of coordinate `n`, whose law is the
atomless unit exponential. Gaussian-BPS replay preserves nonzero velocity,
and its accumulated terminal-flight hazard is a measurable function of
exactly those first `n` coordinates. Lean identifies an exact wait at the
remaining horizon with equality to this accumulated-hazard threshold and
therefore proves that, on every genuine positive completion stratum, the
terminal candidate takes the no-event branch almost surely. The countwise
boundary-null obstruction to the time-split/semigroup gluing argument is thus
closed; constructing that gluing is the next step.

The deterministic input to that gluing is now complete. For any partial
inverse clock, Lean proves that enlarging the available horizon preserves every
event in a finite prefix that remained active under the shorter horizon: only
the residual-time coordinate increases, while the physical state and accepted
event sequence are unchanged. This specializes directly on every positive
Gaussian-BPS completion stratum. The shorter-horizon endpoint is almost surely
the terminal residual flow, and a measurable split-residual hazard stream is
now defined with the unspent terminal mark as its head and the untouched iid
suffix thereafter. Its head inverse wait and reflected event state are proved
pointwise identical to the unsplit terminal clock. What remains for the
semigroup law is the measure-level triangular change of variables on each
stratum and countable gluing over completion counts.

The measure-level factorization needed for that change of variables is now
formalized. An iid infinite hazard stream splits exactly into the product of
its first `n` coordinates, coordinate `n`, and the untouched infinite suffix.
Exponential memorylessness is lifted from a scalar residual mark to the stream
obtained by consing that residual onto the suffix: for every deterministic
threshold this is a fresh iid stream scaled by the exact survival mass. The
Gaussian-BPS split stream is proved equal to this block transformation, and
the fixed-prefix fiber law instantiates the generic result.

Lean also now characterizes each genuine `(n+1)` completion stratum almost
surely as an active finite prefix followed by a terminal mark strictly above
its accumulated-hazard threshold. Both implications are checked: the reverse
direction proves that the next no-event step finishes and that no earlier
prefix could have been selected. Remaining is to integrate the fixed-prefix
fiber identity over this active-prefix set, obtaining the stratum-level
product law, and then sum those laws over `n`.

The fiber integration is now complete in a reusable kernel form. A generic
prefix-dependent residual joint kernel restricts a unit-exponential head to
survival, subtracts the measurable threshold, and retains the prefix. Lean
proves this kernel equals a survival-weighted prefix kernel paired with an
explicitly fresh iid stream. Composition with any s-finite prefix measure and
measurable prefix restriction preserves that equality. The Gaussian-BPS
active-prefix law instantiates it directly. Remaining is to identify the
restriction of the original iid stream to each genuine completion stratum
with this integrated active-prefix kernel, then sum over completion counts.

The stratum identification is now closed. Mapping the original iid stream
restricted to a genuine `(n+1)` completion stratum into finite prefix and
residual stream is proved equal to the integrated fresh-stream kernel. The
fresh kernel is further evaluated explicitly: composition with a prefix law
is its survival-weighted prefix measure times the iid stream measure. Finally,
the finite prefix is pushed through the measurable deterministic terminal-flow
endpoint, and Lean proves that on each stratum the actual completed BPS
endpoint is independent of the fresh residual stream. Remaining is the
countable sum over pairwise-disjoint, almost-surely exhaustive completion
strata; this will yield the global strong-Markov/time-split law.

The countable measure assembly is now closed as well. A reusable theorem
identifies any almost-sure measurable disjoint partition with the sum of its
restricted measures; at positive horizons, the genuine Gaussian-BPS
completion strata are reindexed by their necessarily positive completion
counts and instantiate that theorem. Summing the countwise endpoint/residual
laws preserves the fresh iid residual factor, and projecting the result proves
that the mixture of the explicit survival-weighted endpoint strata is exactly
the law of the totalized completed-horizon endpoint. Finite-prefix replay now
also has a generic drop-prefix/restart identity. The remaining semigroup step
is the final pathwise identification between restarting from the completed
endpoint with the residual stream and direct execution at the summed horizon;
all measure-level countable gluing needed around that identification is now
proved.

The final pathwise identification and semigroup milestone are now complete.
Lean proves that extending the terminal no-event flight and applying its
original mark produces exactly the same capped candidate as restarting from
the short-horizon endpoint with the residual mark, in both the later-event and
continued-no-event branches. Generic prefix/suffix completion lemmas lift that
candidate equality through every completing untouched suffix. Countwise
almost-sure identification, the product-law gluing above, and a reusable
measure/kernel composition lemma then give the exact strong-Markov time-split
law. At kernel level,
`standardGaussianBPSHorizonKernel_semigroup` proves composition at `t` and
`u` equals the kernel at `t+u` for every state. The proof separately closes
zero time and proves that the inactive zero-velocity fiber is an exact Dirac
kernel. Multidimensional target stationarity and ergodicity remain separate
analytic milestones.

The multidimensional stationarity boundary is now represented directly in
Lean rather than only in prose. `standardGaussianBPSTarget` is the canonical
product of the standard Gaussian position and velocity laws.
`StandardGaussianBPSGeneratorTest` couples an observable to its coordinatewise
position derivative and stores the already-supported integrability and
Gaussian generator-cancellation facts. The target-started weak-forward
uniqueness obligation for the constructed semigroup is named
`StandardGaussianBPSTargetWeakForwardUniqueness`; once supplied,
`standardGaussianBPSHorizonKernel_invariant_of_targetWeakForwardUniqueness`
proves exact invariance at every horizon through the generic forward-equation
bridge. This is deliberately a conditional theorem: target-started
weak-forward uniqueness itself remains to be proved and is not inferred from
the generator identity or semigroup law alone.

That uniqueness boundary is now split into its two independent analytic
parts. `StandardGaussianBPSTargetWeakExpectationUniqueness` asks only for
uniqueness of scalar test expectations, while
`StandardGaussianBPSGeneratorTestFiniteRegularDetermining` asks that the
checked observables determine finite regular phase-space measures. Lean
automatically discharges regularity and finiteness for both probability-valued
weak solutions and the constructed Markov marginals, and the new split
invariance theorem assembles the two certificates. Neither certificate is
silently assumed: formalizing a determining smooth core and its backward or
resolvent uniqueness argument remains the active stationarity work.

The measure-determination foundation is now finite-dimensional and reusable.
`exists_contDiff_compactSupport_uniformApprox_finiteDimensional` smooths
compact continuous tests uniformly without losing compact support, and
`Measure.ext_of_integral_eq_on_contDiff_compactSupport_finiteDimensional`
proves that compact `C¹` tests determine finite regular measures on any
finite-dimensional real normed space. A generic representation theorem turns
coverage of those tests into the exact finite-regular determining certificate.

The Gaussian-BPS client now exposes `StandardGaussianBPSSmoothCore` and proves
that such a represented core discharges the determining half automatically.
For construction, `StandardGaussianBPSSmoothObservableCertificate` lists the
coordinatewise Gaussian-Stein and integrability premises for one observable;
its `toGeneratorTest` theorem invokes the existing multidimensional generator
balance result, and certificates for every compact `C¹` observable assemble
the full core. Discharging those fields uniformly from compact smoothness, and
then the scalar backward/resolvent uniqueness theorem, remain open.

The canonical coordinate derivative used by that construction is now fixed:
`standardGaussianBPSCoordinatePartial` evaluates the Fréchet derivative in a
unit position-coordinate direction. Lean proves that summing these partials
against velocity is exactly the Fréchet derivative in the physical streaming
direction `(velocity, 0)`. Thus the smooth-core transport term is tied to the
actual derivative of the supplied phase observable rather than an unrelated
coordinate oracle.

Compact-support regularity for that transport term is now discharged as
well. Each canonical coordinate partial is proved continuous and compactly
supported, hence integrable under the Gaussian phase target. The assembled
physical streaming derivative is likewise continuous, compactly supported,
and integrable, and its pointwise equality with the coordinate reconstruction
is exposed as a reusable theorem. The remaining smooth-certificate fields are
the fiberwise Gaussian moment bounds, reflected bounce-term integrability, and
the coordinate Gaussian integration-by-parts identity; none is inferred from
the new transport lemmas alone.

The fiberwise bounds are now substantially closed. Restriction to every fixed
position is proved to preserve compact support. This supplies both levels of
integrability for the coordinate derivative and position-flux terms: first on
each Gaussian velocity fiber and then for the velocity integral as a function
of Gaussian position. All three fixed-position bounce terms are integrable;
the incoming term is transported from the reflected-rate term by exact
Gaussian reflection invariance. The outgoing and reflected-rate terms are
also jointly integrable on phase space. A new certificate constructor fills
the four transport fields automatically from compact `C¹` regularity. The
remaining core obligations are joint incoming/full-generator integrability
and the coordinate Gaussian integration-by-parts identity.

Joint bounce and generator integrability are now closed. The state-dependent
phase reflection `(q,v) ↦ (q,R_q v)` is proved measurable and exactly
measure-preserving for the Gaussian product target by a skew-product argument
over positionwise reflection invariance. This transports the jointly
integrable reflected-rate term to the incoming term. Combining incoming and
outgoing bounce terms with the compactly supported streaming derivative proves
integrability of the complete phase generator. Consequently
`standardGaussianBPSSmoothObservableCertificate_of_coordinateStein` leaves
only the coordinate Gaussian integration-by-parts identity as input; all
integrability fields are constructed in Lean.

The coordinate identity and smooth core are now complete. Lean constructs a
measurable equivalence splitting any selected coordinate from a finite
standard-Gaussian product and proves it measure-preserving. Every resulting
scalar phase slice remains compactly supported and `C¹`; its ordinary
derivative is identified with the canonical Fréchet coordinate partial. The
reusable scalar Gaussian Stein theorem then proves integration by parts on
each slice, and two Fubini swaps lift it through the remaining position and
velocity coordinates. Therefore every compactly supported `C¹` phase
observable now receives a complete
`StandardGaussianBPSSmoothObservableCertificate`, and
`standardGaussianBPSSmoothCore_contDiffCompactSupport` supplies the actual
finite-regular determining core. The only remaining premise of the current
stationarity route is target-started scalar weak-expectation uniqueness; it is
not implied merely by generator cancellation.

The convergence boundary for multidimensional Gaussian BPS is now
machine-checked rather than only cautioned in prose. Lean defines the
antisymmetric angular-momentum coordinates `qᵢvⱼ-qⱼvᵢ` and proves that linear
flight and reflection in the current position normal both preserve them.
This invariant is lifted through capped inverse-clock steps, arbitrary finite
hazard replays, the totalized completed endpoint, and finally the exact
finite-horizon transition kernel: its row assigns mass one to the initial
angular-momentum level set. Consequently the present bounce-only process must
not receive an arbitrary-start ergodicity claim in multiple dimensions.
Future convergence work needs a continuous-time refresh mechanism or an
explicit invariant-component formulation; this obstruction does not negate
the still-open full-target stationarity theorem.

## 2026-08-18: multidimensional BPS endpoint parked

The remaining multidimensional Bouncy Particle Sampler stationarity and
refreshed-convergence endpoint is optional breadth and is deliberately parked
behind release-oriented refinement, target instantiation, generated-artifact,
and test work. The checked inverse-hazard clock, finite-horizon semigroup,
smooth generator core, and angular-momentum obstruction remain the stable
boundary. No unconditional multidimensional BPS stationarity or convergence
claim is added by this scheduling decision.

## 2026-08-18: reproducible Xu meeting-time experiment

The Julia Xu et al. coupling client now exposes
`coupled_meeting_diagnostic`, which runs a positive number of seeded
replicates and reports every observed meeting time, the explicitly censored
count, meeting fraction, observed mean, and finite-horizon restricted mean.
The checked edge cases include an already-met pair at horizon zero and invalid
replicate/horizon arguments. `make experiment-xu21` runs the documented
Gaussian command-line experiment, and `make experiment-xu21-logistic` runs a
finite-data `L²`-regularized logistic instance using stable Float64 callback
formulas. These outputs are empirical implementation diagnostics; the ideal
marginal identities and geometric meeting tails remain the separate Lean
results.

## 2026-08-18: exact generated-expression refinement instance

The restricted target-expression refinement layer now has concrete exact-real
primitive and recursive backends. Every rational, arithmetic, exponential,
sine, and cosine primitive carries a zero local-error proof; analytic
transport still propagates any declared input error. Lean proves by structural
induction that exact backend evaluation of every generated artifact equals its
compiled ideal semantics, and constructs a zero-error value and generated
symbolic-gradient certificate at an exact input. This is the proof-side oracle,
not a claim that Julia `Float64` or platform transcendental functions are exact.

## 2026-08-18: generated strongly convex quartic target

The restricted target artifact now includes `U(x)=x⁴/4+x²/2`. Lean proves
the generated ideal value, symbolic force `x³+x`, Hessian `3x²+1`, and strict
global Hessian positivity. The artifact generator emits this target alongside
the Gaussian and sinusoidal clients; Julia independently parses the generated
tree and tests its value, force, Hessian, and positive diagonal SoftAbs metric
entry at several inputs. This adds a nonconstant position-dependent polynomial
metric client without target-callback `libm` calls, while SoftAbs square root,
inverse, and logarithm remain explicitly bounded backend operations.

The quartic callback now also reaches the exact-rational cross-language
checker. Julia converts each finite Float64 input, value, force, and Hessian
to its exact dyadic rational, computes the exact errors against the three
ideal polynomial formulas, and serializes the record. The compiled Lean oracle
accepts exactly matching records; Lean proves that every valid record yields
real-valued approximation theorems for the generated value, derivative, and
second derivative. A deliberately corrupted error record is rejected in the
Julia suite. This certifies submitted callback artifacts, not the serializer,
SoftAbs transcendental primitives, or RNG implementation.

The checked quartic Hessian is now consumed directly by the guarded SoftAbs
layer. A generic generated-expression constructor propagates any restricted
backend's quartic Hessian error into a metric-entry certificate, while
`RestrictedQuarticRationalCertificate.softAbsMetricEntryCertificate` starts
from the compiled-oracle-validated dyadic record. The callback Hessian
obligation is therefore discharged artifact by artifact; positivity and error
bounds for SoftAbs, square root, reciprocal, and logarithm remain the precise
platform-specific premises.

The guarded metric layer now proves exact analytic transport bounds for the
three derived positive-domain primitives. Reciprocal transport uses the
algebraic denominator `|computed|·|ideal|`; square-root transport uses the
positive secant denominator `sqrt(computed)+sqrt(ideal)`; and a mean-value
argument bounds logarithm transport by `1/min(computed,ideal)`. Composition
lemmas add each backend's local rounding error. Thus backend contracts no
longer need to re-prove these analytic input-error effects; local primitive
error, SoftAbs-transform transport, solver arithmetic, and RNG semantics remain.

`SoftAbsLocalPrimitiveBackend` now exposes that reduced implementation
contract structurally. It asks for local positive-domain bounds for square
root, reciprocal, and logarithm, plus the complete SoftAbs-transform bound.
`toSoftAbsPrimitiveBackend` fills the full transport-aware errors and proofs
automatically. This prevents each platform client from restating the same
analysis and makes the remaining backend boundary mechanically visible.

## 2026-08-18: generated restricted-potential RWMH adapter

The public `restricted_potential_rwmh` constructor now turns a generated
restricted potential into the sign-correct log-density callback for the
maintained Gaussian random-walk MH runtime. `restricted_potential_hmc` also
supplies the generated symbolic derivative to scalar HMC, and
`restricted_potential_slice` supplies the sign-correct callback to practical
stepping-out slice sampling. The generated quartic target has seeded replay
regressions checking finite, nontrivial execution. This closes the
handwritten-callback gap for restricted artifacts across all three runtimes
while retaining the explicit Float64 arithmetic and RNG refinement boundary.

`make experiment-restricted-quartic` exposes the generated artifact as a
standalone seeded comparison across RWMH, scalar HMC, and practical slice
sampling. It reports each configuration, movement, and low empirical moments
after burn-in and accepts explicit seed, run length, burn-in, and RWMH-scale
controls. The output is diagnostic only: exact artifact semantics,
finite-precision refinement, asymptotic convergence, and cross-algorithm
efficiency remain distinct claims.

## 2026-08-18: standalone reversible-jump transport diagnostic

`make experiment-reversible-jump` now exercises both maintained nonlinear
birth/death clients under explicit seeds: the cubic planar shear and the
three-dimensional product transport. It reports empty-model occupancy plus
canonical-coordinate mean and variance errors, applying the explicit unshear
before summarizing the planar client. These checks cover runtime geometry and
replay behavior; Lean's pushforward-density and invariance theorems remain the
correctness argument.

## 2026-08-18: standalone warmup-only adaptation diagnostic

`make experiment-warmup-rwmh` now exposes the bounded Robbins--Monro scale
warmup under an explicit seed, followed by retained draws from the frozen
ordinary RWMH kernel. It reports the frozen scale, warmup acceptance frequency,
and retained normal moments. Warmup states are not included in those moments;
the diagnostic therefore preserves the formal distinction between a finite
adaptation phase and stationary sampling with the frozen kernel.

## 2026-08-18: standalone constrained-transform diagnostic

`make experiment-constrained-transforms` now runs the positive-log and
open-unit artanh-affine RWMH clients with explicit seeds. It reports support
violations and retained errors against the exponential and uniform target
moments. This activates a reproducible runtime view of both exact Lean
conjugation results without claiming that platform transcendental functions or
RNG draws have thereby been refined to exact reals.

## 2026-08-18: concrete generated PG--HMC experiment

`make experiment-ge-pg-hmc` now binds the Lean-generated Ge operator schedule
to a binary-latent Gaussian-mixture client. The first callback performs the
exact latent Gibbs update and the second performs scalar HMC for the selected
Gaussian conditional. Seeded output reports the latent frequency and
continuous marginal moments, whose ideal values are `1/2`, `0`, and `2`.
This exercises generated ordering and scoped callback binding; it does not
replace the formal common-target invariance premises or Float64 refinement.
The client is also an active regression with exact seeded replay and retained
tolerances for all three known marginal summaries.

## 2026-08-18: standalone Gaussian SoftAbs GR--HMC diagnostic

`make experiment-gaussian-softabs` now runs the maintained constant-Hessian
diagonal SoftAbs specialization under explicit seed, dimension, burn-in, and
draw-count controls. It reports movement plus maximum coordinate mean and
variance errors. This complements the exact invariance and one-dimensional
bare-chain convergence theorems without claiming a general-dimensional
Float64 convergence result.
The two-dimensional default tuning is also registered as a seeded moment
regression, complementing the existing replay and validation checks.

## 2026-08-18: explicit aggregate experiment target

The root `make experiments` target now runs every standalone seeded empirical
harness. It remains separate from `make test` and ordinary builds, preserving
the policy that reference generation and longer empirical reproduction require
explicit user actions.
The documented default aggregate run completes successfully. In particular it
makes the checked-recursive dynamic-HMC identity fallback visible with zero
movement while the other harnesses report their ordinary diagnostics; the
aggregate command imposes no hidden pass threshold on empirical summaries.

## 2026-08-18: fixed-horizon PG with varying particle count

The count-uniform positive-horizon PG rate now feeds an actual law-level limit
for arbitrary iteration-indexed particle-count schedules. Lean proves that at
one fixed Feynman--Kac horizon, total variation tends to zero as PG iterations
grow even if the count simultaneously grows, shrinks, or oscillates. Primitive
finite full support constructs the required certificate family automatically.
This is stronger than separate fixed-count mixing but does not assert a rate
uniform over growing model horizons or a joint growing-horizon/count theorem.
The result is now stated at its natural two-schedule strength: particle count
is arbitrary, while the number of PG iterations may be any separate sequence
tending to infinity. The earlier one-iteration-per-index statement is retained
as a direct specialization.
Lean now also states the underlying uniform convergence directly: for every
positive TV tolerance, eventually every PG iteration count beyond one common
threshold satisfies the tolerance for every particle count simultaneously.
Primitive full support instantiates this quantified theorem without an
external certificate family.

The Julia practical-slice certificate documentation now names the three Lean
comparison theorems that actually exist (`lt_threshold_eq`,
`le_threshold_eq`, and `ge_threshold_eq`) instead of a nonexistent aggregate
trace theorem. It also records the remaining runtime obligation: comparison
order and comparison kind must be linked before pointwise margins certify a
complete Float64 execution trace.

That order/kind linkage is now formalized. `SliceComparisonKind` distinguishes
strict-below, non-strict stop, and accept-above branches, and Lean's new
`decisionTrace_eq` theorem proves equality of the entire computed and ideal
Boolean traces for any finite supplied schedule. Julia's matching
`SliceDecisionTraceCertificate` stores the schedule, computed and ideal bits,
and exposes the common trace only when every margin is stable.
`trace_stepping_out_slice` now instruments the maintained Reference sampler
directly, recording the computed threshold and every ordered comparison before
returning the ordinary result. `certify_stepping_out_slice_trace` attaches the
ideal values and bounds to that observed record. Tests cover deterministic
observer order, seeded replay, stable lifting, and ambiguous fail-closed
behavior. Platform callback, threshold/logarithm, arithmetic, and RNG bounds
remain explicit inputs rather than inferred from self-reported values.

The sampled log-height now has its own compositional certificate.
`SliceThresholdCertificate.threshold_bound` proves that current-state callback
error, `log(u)` error, and final addition rounding add to the complete
threshold error. Julia's `certify_slice_threshold` checks the same three
operation-local witnesses, and the observed-trace overload rejects a
certificate whose computed threshold differs from the recorded execution.
This removes repeated threshold arithmetic from backend clients; obtaining
sound platform/libm and RNG bounds remains deliberately external.

Practical-slice traces now retain the current-state callback result, computed
`log(u)`, comparison positions, and comparison values. This enables the first
target-specific executable client: `certify_restricted_quartic_slice_trace`
checks the base and every comparison against the generated quartic's exact
rational value certificates, computes the rounded threshold-addition error
exactly as a dyadic rational, and feeds all of those bounds into the ordered
decision certificate. Tests reject a trace with a mismatched callback base.
The full suite also submits the base and every comparison callback record to
the compiled Lean oracle, closing the artifact-checking loop for that observed
trace rather than relying only on Julia's rational reconstruction.
For this polynomial client, only the ideal interpretation/error of platform
`log(u)` and the RNG draw remain external to the assembled certificate.

The raw unit-uniform draw is now retained alongside its computed logarithm.
Lean's `SliceLogUniformCertificate.log_bound` reuses the positive-domain
mean-value theorem to transport an RNG-input error through `log`, adding the
backend's local logarithm error with factor `1/lower`. Julia checks the same
uniform witness, local-log witness, and positive lower guard before feeding
the transported bound into the quartic slice certificate. Exact-real
logarithm oracle values and a sound RNG bound remain premises; no BigFloat or
`libm` computation is silently promoted to a proof.

Lean now joins these two layers with
`SliceThresholdCertificate.ofLogUniform`. The constructor fixes the threshold's
ideal logarithm and transported error directly from the guarded uniform
certificate, callback bound, and final addition bound. Its companion theorem
exposes the complete error expression, preventing a backend client from
silently substituting an unrelated intermediate log-error claim.
Julia's matching `certify_slice_threshold` overload consumes the guarded
log-uniform record directly; regression tests confirm that it produces the
same ideal threshold and bound as the fully assembled quartic trace client.

`SliceComparisonCertificate.ofThreshold` now carries that assembled threshold
into the callback-comparison layer with its exact error sum fixed by
construction. Julia's decision-trace overload likewise consumes the complete
threshold record directly. Thus the callback/log/RNG/addition error cannot be
silently changed between threshold certification and branch certification.

## 2026-08-18: standalone particle-Gibbs count experiment

The fixed-horizon finite-HMM particle-count diagnostic is now available as
`make experiment-particle-gibbs-count`, with configurable seed, repetitions,
and positive count grid. It reports the empirical one-step total-variation
distance from the exactly uniform four-path target for each particle count.
The registered test retains the deterministic regression thresholds. This
experiment illustrates the formal fixed-iteration count regime; it does not
assert empirical monotonicity as a theorem or cover joint growing horizon and
particle count.

## 2026-08-18: standalone checked dynamic-HMC comparison

`make experiment-dynamic-hmc` now runs the conservative spanning certificate,
checked first-stop, and checked randomized recursive-doubling interfaces on a
seeded standard-Gaussian target. The CSV output records configuration plus the
movement rate and maximum coordinate mean and variance errors after burn-in.
The movement field makes identity fallback visible: the current recursive
descriptor rejects all traces in this Gaussian configuration. This exposes
the three maintained runtime policies under one reproducible harness without
misrepresenting a fail-closed identity kernel as a mixing sampler. It remains
an empirical implementation diagnostic: no equivalence to ordinary NUTS,
convergence theorem, or efficiency ordering is inferred from these values.

## 2026-08-18: varying-horizon partial-refresh consistency

The particle-error recursion layer now packages two reusable schedule
theorems: a strict affine contraction yields consistency along an arbitrary
horizon schedule, and an already established uniform `C/N` estimate yields
the same conclusion directly. The concrete dependent partial-refresh
bootstrap-filter client instantiates the latter. Thus, for any time-index
schedule, if the particle-count schedule tends to infinity, its empirical
mean-square error tends to zero. A direct bootstrap-population Chebyshev lemma
and the model's uniform MSE estimate give an explicit time-uniform
`C/(N ε²)` deviation bound, hence convergence in probability along the same
schedules. This is a checked stability interface and client; it is not a claim
that every SMC model is horizon-uniform, nor a particle-MCMC theorem.

## 2026-08-18: reproducible Gaussian algorithmic-performance harness

`make experiment-gaussian-performance` now compares maintained scalar RWMH,
public reference-path HMC, and optimized HMC on a seeded standard-Gaussian
target. It emits movement rate, autocorrelation ESS, callback counts, and HMC
ESS per gradient evaluation as CSV. The aggregate `make experiments` target
includes it. The harness reports deterministic algorithmic-work metrics
rather than unstable wall-clock thresholds; the registered Julia tests
continue to enforce the associated ESS, differential replay, and exact
callback-count regressions. The standalone command itself also fails unless
the complete reference and optimized HMC chains agree under identical seeded
draws.

## 2026-08-18: all generated restricted targets reach sampler adapters

The cross-language regression layer no longer exercises only the quartic
artifact end to end. Generated Gaussian, sinusoidal, and quartic targets now
all drive the public restricted RWMH, scalar-HMC, and practical-slice adapters.
Seeded tests check deterministic replay, finite output, and nontrivial movement.
This broadens runtime integration coverage; only the polynomial Gaussian and
quartic clients carry exact-rational callback certificates, while sinusoidal
libm refinement remains an explicit premise.

## 2026-08-18: standalone indefinitely adaptive diagnostic

`make experiment-indefinite-adaptation` now runs the proved never-freezing
Boolean adaptive chain from both initial states and reports seeded tail true
frequencies and their absolute error from one half. It is included in
`make experiments`. Lean's common-Doeblin argument supplies the actual setwise
convergence theorem; the empirical tail frequencies are implementation
diagnostics only.

## 2026-08-18: vanishing-error history-adaptive convergence

`HistoryAdaptiveFamily.stateKernel_succ_eventwiseWithin` now proves that a
uniform eventwise bound on every complete-history-conditioned next-step law
passes unchanged through Ionescu--Tulcea marginalization. Its asymptotic
corollary proves setwise convergence when those one-step errors vanish. The
selected kernel may inspect the full history, need not reduce to a state-only
transition, and need not preserve the target at finite time. This supplies the
nonzero-error theorem needed by a never-freezing continuous client; a jointly
measurable variable-weight refresh instantiation remains to be constructed.

## 2026-08-18: continuous never-freezing adaptation client

`Examples.IndefiniteContinuousRefresh` closes that client obligation. Its
jointly measurable real-valued kernel retains the complete-history empirical
mean with weight `1/(n+2)` and otherwise draws independently from an arbitrary
probability target. Lean proves the selected parameter never freezes, every
conditional row is eventwise within the nonzero anchor weight of the target,
that weight tends to zero, and therefore the actual adaptive marginals
converge setwise. Julia implements the same schedule with an explicit target
draw callback; registered Gaussian moment/replay tests and
`make experiment-indefinite-continuous-adaptation` are active. This client
uses an exact target-refresh branch, so it does not claim that ordinary
history-tuned MCMC automatically satisfies the same bound.

## 2026-08-18: coherent dynamic-tree subrow foundation

`CertifiedDynamicTree.coherentSubrow` retains only leaves whose complete raw
candidate row equals the root's row. Lean proves it never adds candidates,
always forms a certified partition when every raw row retains its root,
preserves already-certified trees exactly, and yields stationary
target-weighted kernels, including fair randomized mixtures. Julia's
`coherent_dynamic_tree` implements the same canonicalization and has active
structural tests.

This is not recorded as production NUTS completion. For the current linear
recursive builder, a globally shared direction trace produces one-sided rows;
coherent subrows are therefore singletons. Productive correctness must use the
existing `RootedTrace` endpoint-dependent trace reversal and completed-tree
C.4 admissible-root semantics across paired fair directions, rather than
requiring each direction trace to be stationary by itself.

## 2026-08-18: executable completed-tree C.4 dynamic HMC

Julia now exposes `completed_tree_c4_candidates` and
`CompletedTreeC4DynamicHMC`. A completed orbit has power-of-two size. Each root
uses its unique least-significant-bit-first direction sequence to reconstruct
the common tree; roots whose recursive checks retain the full orbit form the
C.4 component, while other roots are explicit singleton components. The
resulting rows pass the reroot checker and target-weighted Reference/Optimized
selection agrees on fixed traces. The seeded Gaussian experiment includes the
new client and observes nonzero movement, unlike the intentionally retained
per-direction checked-or-identity diagnostic.

Lean already proves stationarity for the abstract completed-tree C.4 rooted
sampler. `doublingRootEquiv` is now a canonical recursive equivalence rather
than an arbitrary finite enumeration, and Lean proves that its value is exactly
the zero-based least-significant-bit-first sum in which grow-right contributes
zero and grow-left contributes `2^level`. It also proves that decoding
`directionTraceForRoot` recovers the requested root offset. Julia exposes
`completed_tree_direction_trace`, uses it in the C.4 builder, and exhaustively
checks the identical decoding equation through depth eight, including depth
zero and invalid roots. IR version 19 adds the
`lsb-first-grow-right-zero` tag, assigns that tag the proved decoder semantics
in Lean, and makes Julia's helper fail closed if the generated descriptor does
not match. A theorem about compiled Julia source beyond this generated metadata
and exhaustive regression boundary, floating-point callback bounds, and
equivalence to ordinary production stopping semantics remain explicit
refinement obligations.

## 2026-08-18: non-vacuous dynamic-tree U-turn budgets

The end-to-end recursive-row and checked-kernel refinement theorems formerly
required strict endpoint-dot separation for every pair, including a leaf
against itself. That premise is impossible: the self-displacement and both dot
products are zero. The theorems now prove self-pair callback equality directly
and require numerical separation only for distinct leaves.

Lean instantiates the repaired interface twice. The exact unit-momentum line
works at arbitrary finite count, and a four-leaf client carries positive
`1/10` position and momentum error bounds. Finite case analysis proves every
distinct pair clears the composed dot-product error budget, then the existing
refinement theorem identifies the complete randomized checked recursion with
its ideal-real kernel for every depth and positive finite target. Julia mirrors
the four-leaf budget through `certify_vector_uturn_decision`: all twelve ordered
distinct pairs certify, while the four self-pairs deliberately report an
ambiguous margin and are handled structurally. The new
`certify_recursive_doubling_uturn_matrix` adapter consumes a state-threaded
`LinkedLeapfrogVectorTrajectoryCertificate`, reconstructs every later endpoint
and recurrence budget, and certifies all ordered distinct endpoint pairs. Its
active two-endpoint regression checks both directions. Supplying sound local
operation bounds and ideal callback values for an actual sampled Float64
trajectory remains the platform obligation.

## 2026-08-18: time-inhomogeneous particle stability

`ParticleAsymptotics` now proves a uniform inverse-count theorem for genuinely
time-varying affine error recurrences. Each stage has its own contraction rate
and Monte Carlo noise coefficient; a common rate ceiling strictly below one,
a common noise ceiling, and nonnegative actual errors give one time-uniform
`C/N` bound. The resulting consistency theorem permits an arbitrary horizon
schedule while the particle count tends to infinity.

`UniformRefreshSMC` instantiates this interface with a sequence of partial-
refresh Feynman--Kac kernels whose refresh probability may change at every
stage. If all probabilities lie above one fixed positive minimum, the exact
dependent bootstrap-population MSE has the uniform bound
`(Var₀ + 8‖f‖∞² / (1 - (1-p_min)²)) / N` and tends to zero along arbitrary
horizon schedules. This extends the previous repeated single-kernel client;
it does not claim stability for arbitrary potentials or joint growing-horizon
particle-Gibbs limits.

`ParticleGibbsCount` now also isolates the exact joint-horizon closure that is
supportable without pretending that primitive full support is horizon-uniform.
A horizon-indexed client may package its actual TV distances—even when its
trajectory type changes with the horizon—into a scalar error sequence. A
certified geometric bound whose minorization coefficients share one positive
floor, together with any diverging PG-iteration schedule, implies that those
errors tend to zero. A second theorem accepts any directly proved vanishing
geometric-rate schedule. Establishing such a floor for a broad concrete model
family is still a model-stability obligation.

## 2026-08-18: exact-dyadic Float64 Gaussian leapfrog

Added `GaussianDyadicLeapfrogStepCertificate`, an executable Lean checker for
the exact rational kick--drift--kick equations of the scalar Gaussian target.
The Julia constructor converts finite Float64 inputs and every observed
intermediate to their exact binary rationals and succeeds only if all three
equations hold without rational discrepancy. Its wire format is checked by the
new `gaussian_dyadic_leapfrog` oracle command.

The active regression advances the maintained optimized leapfrog for eight
steps at dyadic step size `1/2`; each actual endpoint agrees with Julia's
certificate and the compiled Lean oracle. A deliberately altered momentum is
rejected by Lean, while a `0.1` execution is rejected by Julia because a rounded
operation leaves the exact subset. Thus this is assumption-free evidence for a
useful bounded platform fragment, while rounded IEEE arithmetic, libm, RNG
laws, and arbitrary callbacks retain their explicit refinement premises.

The same module now includes `GaussianRoundedLeapfrogStepCertificate`. Rather
than rejecting every rounded execution, Julia records each Float64 intermediate
as an exact rational and computes the exact rational residual of the half kick,
drift, and final kick. Lean checks those residuals and proves their real
embeddings are valid absolute-error bounds. The active `0.1`-step regression is
accepted with a nonzero final-kick residual, and a falsified zero residual is
rejected. This closes per-execution Gaussian arithmetic evidence; it is not an
a priori uniform IEEE bound and does not cover libm or RNG laws.

The residual checker is also target-independent now:
`RoundedLeapfrogRationalCertificate` takes the two observed gradient values as
explicit fields. `QuarticRoundedLeapfrogCertificate` formally composes that
arithmetic record with generated quartic certificates at the current and next
positions and enforces field linkage. Julia executes an optimized quartic
leapfrog step, checks both generated callback records and the generic arithmetic
record through Lean's oracle, and verifies the maintained optimized endpoint.
This expands sound per-execution coverage beyond the Gaussian identity-gradient
specialization without introducing transcendental assumptions.

The first four certified dyadic endpoints are additionally instantiated as a
Lean `CertifiedLeapfrogPhaseTrajectory`. Lean proves both endpoint dot products
are separated for every ordered distinct pair and therefore identifies its
complete checked recursive kernel with the ideal-real kernel at every tree
depth. Julia rebuilds the same four actual endpoints, checks all off-diagonal
U-turn certificates, and obtains one productive four-root C.4 component rather
than the identity fallback. This closes the concrete trajectory-to-tree path
for the exact-dyadic subset.

The same path now has a genuinely rounded client. Julia runs three maintained
Gaussian steps at `ε = 0.1`, checks every exact rational local residual, and
serializes the four linked phase endpoints. Lean embeds those actual binary
rationals, proves they lie within `10⁻¹⁴` of the exact rational Gaussian orbit,
proves both endpoint-dot margins for all twelve ordered distinct pairs, and
identifies the complete computed checked-recursion kernel with its ideal-real
counterpart at every depth. The oracle checks the complete endpoint array and
rejects a mutated coordinate. This is a concrete rounded trajectory theorem,
not a platform-wide IEEE bound or an arbitrary production-NUTS equivalence.

## 2026-08-19: HMC benchmark suite and published report

Added a local `benchmark/` Julia environment with BenchmarkTools and
AdvancedHMC. Its configurable 100-dimensional isotropic-Gaussian,
AR(1)-correlated-Gaussian, product-quartic, ill-conditioned-Gaussian, and
regularized-logistic workloads compare the maintained Reference and Optimized
endpoint-HMC transitions with AdvancedHMC's unit-metric
`Leapfrog`/`FixedNSteps`/`EndPointTS` transition.
All paths use analytic gradients, identical step size and trajectory length,
and warmed low-level transition loops; the benchmark therefore excludes AD,
compilation, and AdvancedHMC's optional retained-sample/diagnostic storage.
The harness also reports the analogous Reference, Optimized, and AdvancedHMC
fixed-length multinomial-trajectory timings. These share the target, metric,
step size, and integration budget, but no cross-package pathwise equivalence is
claimed for their different trajectory-selection mechanics.
An AdvancedHMC-only generalized multinomial-NUTS row records transition
throughput and its observed average leapfrog count. These stored measurements
predate the separately labelled production-shaped Julia NUTS runtime and are
not retroactively supplemented. That runtime's missing Lean transition
correspondence remains explicit, while the certified checked-tree interfaces
remain a distinct family.
The runner emits tidy CSV with median and interquartile timing, throughput,
memory, allocations, and mean integration work. A separate generator converts
those committed results into an absolute-throughput SVG and full Documenter report;
the site navigation and root index expose the new page without running noisy
performance measurements during an ordinary documentation build.
The full mode now uses ten fixed complete-chain timing repetitions per case
and commits every repetition alongside the aggregate CSV. The report replaces
normalized bars with a log-throughput dot-and-whisker chart: translucent points
show individual runs, large points show medians, and intervals show the IQR.
All three statistics are computed from the same raw timings. A three-repetition,
1,000-transition `--dev` mode writes ignored scratch CSV and supports harness
and layout iteration without replacing the published measurements.
The report groups its absolute-throughput distribution by target and then
algorithm. Each row compares libraries only for that common case, while the shared
logarithmic throughput axis still permits legitimate cross-row reading and
does not privilege one external library as a permanent baseline. Separate
per-algorithm tables present targets as rows and available libraries as columns,
so adding another comparison library extends the same structure naturally.
The target definitions live under `VerifiedSamplers.jl/test/support/`, not in
the installed sampler module. Registered Julia tests check every fixture's
gradient and symmetry, and add direct product-quartic and regularized-logistic
moment regressions. The benchmark includes those same fixtures, adds
AdvancedHMC-only preconditioned endpoint and multinomial cases on the two
geometry targets, and runs separate quality chains reporting moment error,
minimum coordinate ESS, ESS/s, movement, acceptance, divergences, and mean
integration work.

Sampling-quality work is deliberately split by cost and stability. Integrated
Julia tests own lightweight pass/fail contracts: target-gradient consistency,
known moments, and eventually full covariance checks for correlated Gaussians
and a few analytical marginal quantiles. The benchmark report owns heavier
diagnostics: multiple independent chains, split rank-normalized R-hat, bulk
and tail ESS (including ESS per gradient evaluation), covariance-error and
empirical-quantile/ECDF views, and Monte Carlo uncertainty for reported errors.
These benchmark diagnostics should gain visible warning thresholds after they
are calibrated, but should not become flaky CI gates merely by being added to
the report.

The stored CSV has a companion metadata record containing the producing
commit, Julia version, and CPU. Report regeneration reads that record rather
than stamping historical measurements with the current checkout or machine.

The first consolidation phase adds a copyable sampler-development obligation
record for researchers and agents. It preserves the existing Lean-first flow:
mathematical definitions and proofs can precede or omit executable lowering,
while later IR, Reference, optimized, and diagnostic obligations remain
explicit. Sampling-quality calculations are now shared test support rather
than benchmark-local formulas. The integrated suite and benchmark consume the
same ESS and known-moment implementation; covariance, marginal-quantile, and
batch-means standard-error helpers establish the next calibrated-test boundary.

A sampler-independent invariance lemma was also moved out of Hamiltonian HMC:
`Kernel.Invariant.smul` now lives in `Mcmc.Kernel.Invariant`, the public home
for reusable target-preservation closure facts. This is a structural cleanup,
not a new algorithm claim; existing HMC proofs consume the same theorem from
the lower layer.
