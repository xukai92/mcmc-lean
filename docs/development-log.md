# Development log

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

## 2026-08-13: paper coverage audit

Added `docs/xu21-coverage.md`, a claim-by-claim map from Algorithms 1--6,
Assumptions 1--2, Condition 1, Propositions 4.1--4.2, Lemmas 4.1--4.4, and
Theorem 4.1 of Xu et al. to the compiled Lean artifacts. The audit explicitly
requires the concrete RWMH and multinomial-HMC kernels and their marginal and
invariance proofs; abstract kernel implications alone are not counted as
algorithmic completion. It also records the exact boundary between proved
results, positive-window repairs to the printed Condition 1, conditional
optimal-transport conclusions, extensional rather than executable sampling,
and the fully instantiated scalar standard-Gaussian endpoint.

Expanded the README's paper-statement audit to state the two corrections and
their downstream implications explicitly. Condition 1 must use an integration
window bounded away from zero, with the proved general form selecting that
window after fixing a kinetic cutoff. The unconditional exponent-two route is
obstructed by first-order multinomial index mismatch; the conditional
exponent-two interface is retained, while the proved first-moment maximal-
coupling route supplies the local accessibility used for geometric meeting.
The audit also records that global drift is an independent premise and that
meeting alone is not marginal convergence from arbitrary starts.

Added `docs/architecture.md` to document the dependency layers from mathlib's
`Measure` and `ProbabilityTheory.Kernel` interfaces through the concrete RWMH
and multinomial-HMC branches to the coupled mixture, geometric meeting theorem,
and estimator consequences. A separate graph records that finite transport is
used internally for trajectory-index selection while the surrounding kernels
remain general-state.

The next substantive gap is additional target-specific HMC drift
certificates, preferably beginning with a nontrivial higher-dimensional
standard Gaussian and followed by an applied target. Unbiased-estimator
variance and expected-cost conclusions remain a downstream layer beyond the
geometric meeting-tail theorem.

## 2026-08-13: dimension-free Gaussian drift foundation

Added `standardQuadratic_leapfrog_sqrtTwo_energy_defect`. For every finite
dimension it computes the exact one-step defect at `ε = √2` as refreshed
kinetic energy minus half the incoming quadratic potential. This replaces the
scalar-coordinate identity at the first step of the existing Gaussian HMC
drift argument. The remaining extension is to lift the categorical retention
and Gaussian-envelope estimates from absolute values to Euclidean norms, then
reuse the dimension-generic Xu drift constructor.

## 2026-08-13: finite-dimensional Gaussian exact lag-one theorem

Completed the extension from the scalar Gaussian validation case to every
nonempty finite coordinate dimension. The proof derives radial positive- and
negative-time `ε = √2` energy defects, bounds the actual two-point multinomial
selection law for both randomized trajectory roots, integrates a
dimension-free capped-retention envelope against refreshed Gaussian momentum,
and obtains a strict affine drift inequality for the implemented `L = 1`
multinomial-HMC kernel. A finite-dimensional energy sublevel construction
then discharges Xu's Lyapunov containment and strict energy-range premises.

The public endpoint
`exists_geometric_exactLagOneMeetingTail_standardQuadratic_finite_sqrtTwo`
proves a geometric exact lag-one meeting tail from every deterministic
initial state for the concrete sticky multinomial-HMC/Gaussian-RWMH mixture.
No HMC, RWMH, coupling, drift, or level-set premise remains abstract in this
standard-Gaussian family.

## 2026-08-13: regularized logistic target and local HMC theorem

Added `Hamiltonian/LogisticRegression.lean`. The module defines softplus and
the logistic sigmoid and proves their scalar calculus, monotonicity, and
global Lipschitz bound. It then defines the actual finite-data binary logistic
negative log likelihood, adds positive `L²` regularization, and constructs the
exact gradient supplied to leapfrog.

Lean proves that this gradient is the Fréchet derivative of the potential,
is globally Lipschitz with coefficient equal to the regularization strength
plus the explicit sum of squared label/feature norms, and is globally
strongly monotone with the regularization modulus. Consequently every
positive-radius closed ball satisfies `LocalStrongConvexity`, and nested
closed balls yield a positive integration window and relaxed-entry bound for
the implemented maximal shared-momentum multinomial-HMC coupling.

This closes the paper's local analytic assumptions for a non-Gaussian applied
target. The same module now also proves a uniform bound on the finite-data
likelihood force, quadratic coercivity, and exact one-step leapfrog
cancellation at `ε² λ = 2`. Both endpoint components have explicit norm
envelopes, and the Hamiltonian defect is bounded above by fixed data and
momentum terms minus `(λ/8)‖q‖²`. This supplies the strict tail-energy margin
needed for drift.

The capped retention factor is now bounded by a scalar negative-quadratic
lemma, reduced to a function growing only linearly in refreshed momentum,
and integrated using the proved finite first Euclidean-norm moment of the
standard momentum measure. The resulting finite
`regularizedLogisticDriftAllowance` gives a strict affine drift inequality
with rate `1/2` for the actual `L = 1` position multinomial-HMC kernel at every
parameter satisfying `ε² λ = 2`. The categorical current-index probability,
non-current endpoint, randomized-root expectation, and kernel integral are
all connected explicitly. The remaining end-to-end logistic Theorem 4.1
packaging task is the compact energy-region infimum/supremum geometry, not
HMC drift.

## 2026-08-13: lagged estimator expectation and finite expected corrections

Added `Kernel/UnbiasedEstimator.lean`. The module proves the exact path
marginals for Algorithm 1's lagged initialization: paired time `n` has first
marginal equal to the ordinary chain at `n+1` and second marginal at `n`.
The finite lagged estimator, consisting of `h(Y₀)` plus corrections
`h(Xₙ₊₁)-h(Yₙ)`, therefore has expectation exactly equal to the ordinary
time-`N+1` marginal expectation. Marginal expectation convergence transfers
to estimator expectation convergence.

For an infinite stopped estimator, Lean first proves unbiasedness under the
exact required `L¹` convergence premise, making the limit/integral
interchange explicit. It now also discharges that premise for every bounded
measurable observable under a geometric exact-meeting tail: stopped
corrections have summable `L¹` norms. Their `L²` norms are bounded by the
square root of the meeting tail, whose geometric series is again summable;
the full estimator is consequently proved `MemLp ... 2`, hence has finite
variance. The bridge from the kernel-level `IsFaithful` certificate to
almost-everywhere faithful paths is now proved through mathlib's trajectory
law, so the main unbiasedness theorem accepts the concrete sticky-kernel
certificate directly. A stationary-start corollary removes any separate
marginal-convergence premise when the chain starts from its invariant target.
The boundedness restriction has also been removed through a paper-style
higher-moment theorem. A uniform path-coordinate `Lᵖ` bound with `p ≥ 2` and
positive Hölder gap `1/2 - 1/p`, together with a geometric meeting tail,
bounds each stopped correction by a summable positive power of that tail.
Lean consequently proves both unbiasedness and `MemLp ... 2` for these
possibly unbounded observables. In the stationary case, the path marginal
identities reduce all coordinate hypotheses to one `MemLp h p target`
certificate; invariance supplies integrability and constant marginal
expectations. For the fully instantiated Dirac-start Gaussian and logistic
meeting-tail endpoints, concrete marginal convergence remains separate and
unproved.
Separately, every geometric exact-meeting tail has
summable tail mass and hence finite `expectedCorrectionCount`, with bound
`C * (1-rate)⁻¹`.
The new pathwise `activeCorrectionCount` is the sum of the actual failure
indicators. Tonelli's theorem proves that its `lintegral` is exactly
`expectedCorrectionCount`; the geometric bound therefore gives both finite
expected correction work and almost-surely finite correction work.

The instantiated target modules expose this boundary directly through
`exists_standardQuadratic_boundedEstimator_of_marginal_convergence` and
`exists_regularizedLogistic_boundedEstimator_of_marginal_convergence`.
These select the actual mixture and geometric constants, discharge coupling,
faithfulness, integrability, and `L²`, and return estimator unbiasedness as an
implication from the remaining Dirac-start marginal-expectation convergence
statement.

That packaging task is now closed in
`Hamiltonian/LogisticRegressionXu.lean`. An explicit compact Euclidean region
contains the selected Lyapunov sublevel; the origin and a one-coordinate
witness establish potential values strictly below and above the chosen
energy. Lean assembles every field of `XuTheorem41DriftAssumptions` and proves
`exists_geometric_exactLagOneMeetingTail_regularizedLogistic` for arbitrary
finite data, positive regularization, any `ε² λ = 2`, nondegenerate Gaussian
RWMH variance, deterministic initialization, and nonempty finite dimension.

## 2026-08-13: general C² relative leapfrog error closed

The numerical half of repaired positive-window Condition 1 is now proved for
every `RegularPotential`. The proof differentiates the one-step Hamiltonian
defect in the initial phase, rewrites it using Hessian symmetry, and isolates
the trapezoidal-force cancellation. Compact-uniform continuity of the Hessian
makes that leading coefficient vanish with the step size; explicit global
Hessian, gradient, momentum, and phase-norm bounds control all remaining
quadratic terms. Lean concludes
`RegularPotential.locallyUniformVanishingPerTimeOneStepEnergyDefectFDeriv`,
then transfers it through the already proved mean-value, signed-trajectory,
and fixed-window bridges.

As a result,
`UniformOverlapWeightedMomentOneContractionOnIntegrationWindow.exists_maximalCondition_of_regularPotential`
derives repaired maximal-coupling Condition 1 from the aligned certificate
alone on a compact position set. The outstanding general contraction gap is
therefore no longer numerical leapfrog consistency; it is constructing that
overlap-weighted aligned certificate uniformly in the paper's kinetic-cutoff
quantifier.

## 2026-08-13: cutoff-wise aligned quantifiers isolated

An audit against Xu et al.'s printed Condition 1 confirms two distinct
issues. The printed condition lets its maximum integration time depend on the
kinetic cutoff, but requires contraction for every smaller trajectory length,
including the identity case already ruled out by the formal obstruction. The
repaired uniform positive-window interface removes that identity case but
places its window and rate outside the cutoff quantifier, which is stronger
than the current compact local-convexity proof.

The new
`CutoffWiseOverlapWeightedMomentOneContractionOnIntegrationWindow` records the
exact positive-window statement supported by that proof. Lean now derives it
from `RegularPotential`, compact local strong convexity, and the compact-core
hypotheses; for each kinetic cutoff it constructs a positive window, a
step-size threshold, and a subunit first-moment aligned rate. The stronger
uniform certificate implies this cutoff-wise one, formally documenting the
logical hierarchy. Closing the general repaired Condition 1 theorem still
requires either a genuinely cutoff-uniform dynamical argument, stronger
global curvature hypotheses, or a weaker repaired theorem whose parameter
order matches the downstream meeting proof.

## 2026-08-13: Assumptions 1--2 reach kernel relaxed accessibility

The cutoff-wise path is now carried through the full maximal-coupling
argument. General `RegularPotential` relative energy control discharges the
last premise of the existing fixed-cutoff assembly, yielding a subunit
expected-distance contraction for the maximal trajectory-index coupling and
then for the actual randomized-origin Markov kernel.

Lean fixes the positive-mass standard-Gaussian momentum event `K(p) ≤ 1`,
uses compactness to bound the diameter of the position core, applies the
first-moment Markov inequality, and integrates over momentum refresh. The
result,
`LocalStrongConvexity.exists_maximalSharedMomentum_isRelaxedMeetingAccessible`,
constructs a positive integration window, relaxed radius, entry constant, and
step-size threshold for which the implemented shared-momentum/maximal-index
HMC kernel is one-step `IsRelaxedMeetingAccessibleFrom`. This is exactly the
local kernel premise consumed by the abstract Xu drift-to-geometric-tail
theorem; uniformity over every possible kinetic cutoff is not needed for that
application.

## 2026-08-13: local convexity composed with Xu geometric tails

`LocalStrongConvexity.exists_xuGeometricRelaxedTailWindow` now composes the
new cutoff-wise kernel accessibility theorem with the abstract Xu
drift-to-tail result. It selects a positive integration window, relaxed
radius, entry probability, and numerical threshold. For every concrete
`ε,L` in that window, any `XuTheorem41DriftAssumptions` certificate concerning
the same verified multinomial-HMC kernel and verified Gaussian-RWMH kernel
produces a geometric relaxed-meeting tail for `coupledHmcRwmhMixture`.

The theorem installs and proves the maximal shared-momentum HMC and coupled
Gaussian-RWMH marginals and Markov properties internally. Consequently the
remaining general end-to-end premise is a drift certificate compatible with
one of the selected HMC parameter pairs; neither RWMH/HMC correctness nor
local HMC accessibility is left as an opaque assumption.

## 2026-08-13: fixed-cutoff first-moment Condition 1 assembly

A finite weighted Cauchy--Schwarz lemma now converts the proved
overlap-weighted squared aligned contraction into a first-moment contraction
with square-root rate. The relative centered-energy hypothesis now also
produces a first-moment cross-index bound. These estimates are assembled into
a subunit expected-distance contraction theorem for maximal multinomial
coupling at every fixed kinetic cutoff. The remaining general Condition 1 work
is to derive the relative centered-energy property from `RegularPotential`
and manage the paper's uniform-in-cutoff quantifier order. The latter gap is
now represented explicitly by
`UniformOverlapWeightedMomentOneContractionOnIntegrationWindow`. Together
with relative centered-energy control at every cutoff, this certificate is
proved to imply the full repaired positive-window Condition 1 with a single
subunit rate. The existing local-strong-convexity construction does not yet
supply this certificate: its exact-flow horizon, and hence its selected rate,
depends on the common phase bound.

The relative numerical gap now has two local interfaces. The qualitative
`LocallyUniformVanishingRelativeCenteredSignedLeapfrogEnergyError` asks that
the paired centered-defect Lipschitz modulus tend to zero with step size; this
is the appropriate remaining target under general `C²` regularity. The
stronger `LocallyUniformLinearRelativeCenteredSignedLeapfrogEnergyError`
supplies an explicit `O(|ε|)` modulus and implies the qualitative interface.
Either yields the compact-window relative property and, together with the
cutoff-uniform aligned certificate, repaired Condition 1. Ordinary absolute
energy consistency does not prove the required diagonal-vanishing estimate.
The actual general-potential obligation is now weakened further to the
shared-momentum version, matching the coupled-HMC construction exactly. The
arbitrary-phase vanishing and linear Gaussian interfaces imply it, while the
existing compact `C²` paired-phase machinery already uses this same
shared-momentum hypothesis.

The remaining shared-momentum estimate is now reduced to a one-step local
calculus statement,
`LocallyUniformVanishingPerTimePairedOneStepEnergyError`. Lean proves that
this vanishing per-unit-time defect modulus telescopes over positive and
negative leapfrog iterates using the existing phase-size and phase-separation
stability bounds. It therefore implies the signed shared-momentum criterion
and repaired Condition 1. The standard quadratic target satisfies this
one-step interface directly from its explicit cubic defect formula. For a
general `RegularPotential`, only this one-step paired defect lemma remains;
the fixed-horizon accumulation is no longer part of the gap.

The paired lemma is now reduced by a formal mean-value argument to the
derivative-level criterion
`LocallyUniformVanishingPerTimeOneStepEnergyDefectFDeriv`. It asks for
compact-uniform `o(|ε|)` control of the phase derivative of the one-step
energy defect. Lean proves that this criterion implies the paired one-step
bound and hence repaired Condition 1. Conversely, the paired estimate implies
the derivative criterion by applying mathlib's local
Lipschitz-to-Fréchet-derivative theorem on a phase ball, with all ambient and
Euclidean norm conversions discharged. Thus these are equivalent interfaces,
not different assumptions. The standard quadratic target now explicitly
instantiates both. Lean also proves that the defect and its
phase derivative are identically zero at `ε = 0`. Together with the existing
compact-uniform Hessian-continuity and four-point force lemmas, this isolates
the remaining general-potential calculation as the quantitative first-order
cancellation in that derivative.

The underlying scalar cancellation is now proved directly from the leapfrog
updates. At zero step size, the position derivative is the current momentum
and the momentum derivative is minus the certified gradient; differentiating
potential plus kinetic energy therefore gives two opposite Euclidean inner
products. Lean packages this as
`RegularPotential.hasDerivAt_oneStepEnergyDefect_zero` and derives the
pointwise little-o theorem `RegularPotential.isLittleO_oneStepEnergyDefect`.
This does not by itself settle the paired theorem: the remaining obligation is
to obtain the same cancellation after the phase derivative, uniformly over a
bounded phase family.

The step-size fundamental-theorem-of-calculus route is now formalized. The
explicit `leapfrogStepSizeTangent` includes the Hessian action arising from
the final kick, and `RegularPotential.hasDerivAt_leapfrog_stepSize` proves it
is the actual derivative for every step size. Lean then differentiates the
Hamiltonian along this tangent and proves that the difference of two
one-step defects is exactly the interval integral of the difference of those
Hamiltonian variations. The new smallest interface,
`LocallyUniformVanishingPairedStepSizeEnergyVariation`, asks that this
concrete integrand have a compact-uniform phase Lipschitz coefficient tending
to zero. Its integral bridge proves the paired one-step criterion and hence
repaired Condition 1. This is retained as a useful sufficient interface, but
is not asserted to follow from `C²`: differentiating this integrand in phase
may implicitly ask for a third derivative.

The sharper `C²` route now differentiates leapfrog in its initial phase before
estimating. `leapfrogPhaseTangent` records the two kick derivatives and drift
derivative explicitly, and Lean proves both
`RegularPotential.fderiv_leapfrog_apply` and
`RegularPotential.fderiv_oneStepEnergyDefect_apply`. The latter expresses the
outstanding operator norm using only the gradient and its first derivative at
the initial and drifted positions. A separate theorem derives symmetry of
`fderiv gradient` in the explicit Euclidean inner product from mathlib's
symmetry theorem for the second Fréchet derivative of a `C²` scalar function.
The remaining task is now to algebraically expose and bound the within-step
Hessian differences in this explicit phase-derivative expression.

That algebraic phase cancellation is now machine checked.
`RegularPotential.fderiv_oneStepEnergyDefect_apply_eq` expands the derivative,
and `RegularPotential.leapfrogEnergyPhaseLeadingCancellation_eq` rewrites its
leading terms as a trapezoidal Hessian approximation to the force increment
plus an explicitly quadratic correction. Uniform compactness has also been
specialized to leapfrog geometry:
`RegularPotential.exists_uniform_leapfrog_hessian_sub_le` proves that the
initial and drifted Hessians are uniformly arbitrarily close on every bounded
phase family. Finally,
`norm_leapfrog_trapezoidalForceRemainder_le` combines endpoint Hessian
closeness with a gradient linearization remainder to bound the trapezoidal
force term. What remains is to instantiate the existing compact-uniform
gradient-linearization theorem on the same automatically constructed phase
ball and sum the explicit lower-order terms into the desired operator norm.

The compact specialization is now discharged.
`RegularPotential.exists_uniform_leapfrog_gradient_linearization_le`
constructs a closed position ball containing both the initial and drifted
positions for every bounded phase point and sufficiently small step, then
applies the existing uniform gradient-linearization theorem there. A single
minimum threshold combines it with endpoint Hessian closeness in
`RegularPotential.exists_uniform_leapfrog_trapezoidalForceRemainder_le`.
Thus the leading, non-polynomial part of the phase derivative now has its
required uniformly vanishing coefficient. The residual task is bookkeeping:
bound the explicitly quadratic terms using the already proved global Hessian,
gradient-growth, and phase-size estimates, then convert the directional bound
to the Fréchet operator norm.

The quantitative interface is validated independently of the final coupling
statement for the standard quadratic target. A new generic paired-path
estimate telescopes the explicit one-step Gaussian defect while controlling
both phase separation and phase size. It proves
`standardQuadratic_locallyUniformLinearRelativeCenteredSignedEnergyError` for
arbitrary bounded phase pairs and signed offsets. The generic bridge then
gives the compact-window relative property for every nonnegative horizon,
not only the earlier unit-horizon shared-momentum instance.

The aligned Gaussian half is now modular as well.
`standardQuadratic_uniformOverlapWeightedMomentOneContraction` fixes the
positive integration window and subunit overlap-weighted rate outside the
kinetic-cutoff quantifier; only its step threshold depends on the cutoff.
Combining this theorem with the signed relative energy criterion through the
generic assembly proves
`standardQuadratic_exists_maximalCondition_via_signedEnergyError`. This is an
independent end-to-end route to repaired Gaussian Condition 1, separate from
the older monolithic pointwise mismatch-budget construction.

## 2026-08-13: general-potential endpoint-band weighting bridge

The compact positive-window endpoint theorem now applies directly to signed
leapfrog offsets, including negative-time indices in randomized multinomial
trajectories. Its constructed lower endpoint is small enough that four times
that endpoint remains below the upper horizon. A canonical endpoint band is
defined on the longer side of every randomized origin; it contains exactly
`L / 4 + 1` indices, hence at least one quarter of all indices, and every band
offset lies in the contraction window whenever the total integration horizon
lies in `[4*Tmin,Tmax]`.

Centered Hamiltonian-error control gives every atom of both trajectory laws a
common normalized Boltzmann floor. Combined with the quarter-band cardinality,
this proves an origin- and trajectory-length-independent overlap-mass floor

```text
(4 exp(2δ))⁻¹.
```

The finite transport layer now has a reusable two-rate weighted-band lemma:
if all aligned costs have rate `σ`, the endpoint band has the better rate
`ρ ≤ σ`, and the band carries overlap mass `η`, then the weighted aligned
cost recovers the explicit loss `η(σ-ρ)` from the global `σ` budget. This is
instantiated for the actual multinomial trajectory PMFs and squared-position
cost. Thus the endpoint result has been lifted through trajectory weighting;
the remaining aligned obligation at that stage was a sufficiently sharp
near-one global cost rate `σ` outside the band.

That final aligned obligation is now closed. Exact-flow contraction is first
weakened to nonexpansion over the entire short-time window, and the same
relative leapfrog error gives every aligned index the near-one rate
`(1+e)²`. The endpoint band retains rate `(r+e)²<1`. A scalar selection lemma
chooses `e>0` small enough that

```text
(1+e)² - (4 exp 2)⁻¹ ((1+e)² - (r+e)²) < 1.
```

The step threshold is simultaneously reduced so the signed fixed-horizon
energy defect is at most one on every trajectory index. Consequently
`exists_uniform_overlapWeightedAlignedContraction` constructs one subunit
rate for the actual overlap-weighted squared aligned cost, uniformly over all
trajectory lengths and randomized origins in the positive window. Global
Lipschitzness of the Hamiltonian vector field now supplies a global exact curve
from every initial phase via a proved uniform-local-to-global continuation
lemma. The initial-state contraction corollary constructs those curves
internally. Instantiating the repaired Condition 1 quantifiers therefore still
required a kinetic-cutoff-to-phase-size reduction on the aligned side. That
reduction is now proved generically: compactness bounds the position norm and
`kineticEnergy p ≤ k0` bounds the momentum norm by `sqrt (2*k0)`. The resulting
kinetic-cutoff contraction theorem discharges both phase-size and global-curve
premises internally. The absolute TV-weighted off-diagonal estimate is now
also closed uniformly on the same family: for every `η>0`, Lean chooses a
common threshold and one cross-index squared-cost bound whose TV product is
below `η`. This is assembled with the subunit aligned theorem under common
thresholds. The remaining gap is precisely relative rather than absolute:
Condition 1 requires the mismatch product to be bounded by a fixed coefficient
times the current separation at exponent one (or its square at exponent two).
The exact exponent-one numerical premise is now represented by
`UniformRelativeCenteredLeapfrogEnergyErrorOnCompactWindow`. Lean proves that
it supplies an arbitrarily small relative TV-weighted mismatch rate, including
all compact, kinetic-cutoff, horizon, length, and origin quantifiers. The
standard quadratic target validates the premise using its explicit
`O(ε²‖q₁-q₂‖)` centered-defect estimate. Deriving the premise from a general
`RegularPotential`, and completing the corresponding aligned first-moment
assembly, remain open. No claim of the full general-potential Condition 1 is
made yet.

## 2026-08-13: finite-horizon compact recurrence interface

The compact four-trajectory propagation and paired discrete Grönwall layers
now require their geometric, numerical-step, and local-truncation hypotheses
only at indices `k < n`. This matches the fixed integration horizon
`n |ε| ≤ T` and removes the unintended requirement that trajectories remain
inside one compact region for all future grid times. The supporting exact-flow
phase envelope, buffered compact region, and uniform bounded-initial-data
leapfrog containment theorem are also machine checked. The shared-momentum
specialization additionally proves, uniformly at every
grid point, that both the exact reference separation and the separation after
one reference leapfrog step are bounded by one explicit multiple of the
initial position distance. Thus the recurrence's two relative `A * Q`
premises no longer remain external assumptions.

The remaining geometry has now also been discharged. Explicit `O(|ε|)`
bounds control every shifted exact segment and every reference leapfrog
endpoint, while absolute fixed-horizon consistency controls both numerical
references and their propagated images. The theorem
`RegularPotential.exists_uniform_leapfrogN_pairedPhaseError_le` synchronizes
the compact propagation radius, local-truncation radius, exact-flow buffer,
and numerical-containment threshold. For every bounded shared-momentum pair
from the compact core it proves the full paired `leapfrogN` versus exact-grid
fixed-horizon estimate, with no caller-supplied grid geometry or local-error
premise.

The parameter-closing step is now machine checked as well. The propagation
forcing retains its genuine `ε²` term, so its zero-step limit is independent
of the compact Hessian bound. Global gradient Lipschitzness supplies an
explicit uniform operator-norm bound for the gradient derivative. Lean can
therefore choose `η` first and then one positive `ε` threshold making the
paired fixed-horizon error at most any prescribed `ρ ‖q₁-q₂‖`. Finally,
`RegularPotential.exists_uniform_leapfrogN_squaredContraction` transfers a
uniform exact squared factor `exactRate²` to the numerical factor
`(exactRate + errorRate)²`.

The exact certificate is now fully instantiated by
`LocalStrongConvexity.exists_uniform_leapfrogN_contraction_on_window`. Lean
constructs `0 < Tmin < Tmax`, a common Euclidean exact-flow envelope, a
positive step threshold, and exact/numerical NNReal rates whose combined
squared factor is strictly below one. For every bounded shared-momentum pair
from the compact core and every grid time satisfying
`Tmin ≤ n |ε| ≤ Tmax`, the leapfrog endpoint squared distance contracts at
that uniform subunit factor. The endpoint-band weighting bridge above now
lifts this result through a fixed positive fraction of the Boltzmann
trajectory weights.

## 2026-08-13: compact-uniform gradient linearization

The `C²` assumption on the potential now propagates to a machine-checked
`C¹` theorem for its certified gradient. Consequently the gradient's
Fréchet derivative is continuous and uniformly continuous on every compact
position region. On a compact convex region, Lean turns this into the
quantitative uniform Taylor estimate

```text
‖∇U(y) - ∇U(x) - D(∇U)(x)(y-x)‖ ≤ η ‖y-x‖
```

for all sufficiently close `x,y`, with an arbitrarily small common `η`.
This supplies the local Hessian-continuity ingredient for the paired force
modulus. The remaining step is a four-point estimate along corresponding
points of the moving segments joining the two coupled trajectories, followed
by discrete accumulation.

## 2026-08-13: compact-uniform paired force modulus

Lean now represents a force difference as the interval integral of the
gradient derivative along the segment joining the paired positions. Comparing
the two segment integrals proves the cancellation-preserving four-point bound

```text
‖(∇U(y₁)-∇U(x₁)) - (∇U(y₀)-∇U(x₀))‖
  ≤ η ‖y₀-x₀‖ + M ‖(y₁-x₁)-(y₀-x₀)‖.
```

Here `η` is supplied by compact-uniform Hessian continuity at corresponding
segment points, while `M` is a machine-checked common Hessian bound on the
compact region. Segment containment follows from convexity, and corresponding
segment points stay within `δ` whenever both endpoints do. In the project's
Euclidean norm this yields the relative modulus

```text
(d+1)(η + M R) ‖y₀-x₀‖
```

when the relative separation changes by at most `R ‖y₀-x₀‖`. Existing
short-time exact-flow estimates make both endpoint displacement and `R`
small. The remaining numerical work is to package that instantiation for the
exact and leapfrog endpoints and accumulate the resulting local phase error.

## 2026-08-13: exact and leapfrog force-modulus instantiations

The abstract paired force premises in the one-step phase-consistency theorem
are now discharged for both sides of the comparison. For exact Hamiltonian
curves, compact containment and small absolute displacement combine with the
proved relative rate

```text
Rexact(t) = (d+1)² β A(t) |t|²
```

to give a compact-uniform force modulus
`(d+1)(η + M Rexact(t))`. For the leapfrog endpoint, the exact
shared-momentum position identity gives relative displacement
`(β ε²/2)‖q₁-q₂‖`, hence modulus
`(d+1)(η + M β ε²/2)`. Both the exact and discrete moduli therefore become
arbitrarily small at short time under the paper's `C²` assumption. Remaining
are selection of one common compact modulus for the two estimates and stable
iteration of the resulting local phase error.

## 2026-08-13: automatic compact one-step phase consistency

The exact and leapfrog force estimates now share one displacement radius,
compact Hessian bound, and explicit dominating force rate. Substitution into
the paired quadrature theorem removes both caller-supplied force premises and
gives the complete one-step phase estimate

```text
phaseError ≤ |ε| · r(η,M,ε) · ‖q₁-q₂‖.
```

The per-time rate `r` is continuous in the signed step size and its value at
zero is `(d+3/2)(d+1)η`. Lean proves the required two-stage uniform selection:
for every positive per-time allowance, first choose `η>0` by compact Hessian
continuity; for every resulting finite compact Hessian bound `M`, one positive
symmetric step-size neighborhood then has `r<allowance`. Thus the local
relative phase error is now automatically `o(|ε|)` in the uniform
epsilon--delta sense needed for fixed-horizon accumulation. The remaining
general-potential numerical step is the discrete accumulation itself.

## 2026-08-13: fixed-horizon scalar error accumulation

Lean now proves the discrete Grönwall calculation needed after a paired
propagation recurrence is available. If `e₀=0` and

```text
eₖ₊₁ ≤ exp(C|ε|) eₖ + |ε| r Q,
```

then `n|ε|≤T` implies

```text
eₙ ≤ T r exp(C T) Q.
```

Thus an arbitrarily small local per-time rate stays arbitrarily small over a
fixed integration horizon. The remaining numerical obligation is now the
four-trajectory propagation inequality placing the actual paired
leapfrog-versus-exact error into this scalar recurrence. Ordinary two-state
leapfrog Lipschitz stability is not by itself enough: the proof must compare
two numerical states with two exact states while retaining cancellation in
their relative difference, so that the bound remains proportional to the
initial paired separation and vanishes on the diagonal.

## 2026-08-13: compact four-trajectory propagation

The missing algebraic propagation layer is now formalized. For numerical
states `z₁,z₂` and reference states `w₁,w₂`, Lean subtracts the two exact
leapfrog recurrences and bounds the updated relative phase error by the old
relative phase error plus paired force discrepancies at the initial and final
half-kicks. Compact `C²` segment estimates then control both force terms while
preserving cancellation:

```text
Ephase' ≤ (1+|ε|) Ephase
  + |ε|(d+1) [η Q₀ + M Eq
              + (η Q₁ + M Eq')/2].
```

Here `Q₀,Q₁` are the reference pair's position separations and `Eq,Eq'` are
the relative numerical-versus-reference position errors. The result uses one
compact displacement radius and Hessian bound and remains zero on the paired
diagonal. Because the endpoint half-kick introduces `Eq'` on the right, the
remaining induction must first close the explicit position-error recurrence,
then substitute it into this phase recurrence and apply the completed scalar
fixed-horizon theorem.

The endpoint position recurrence is now closed. Before the second half-kick,
compact Hessian continuity gives

```text
Eq' ≤ (1 + |ε| + ε²(d+1)M/2) Ephase
      + ε²(d+1)η Q/2.
```

Its relative-rate form is also proved: if `Ephase ≤ R Q`, then
`Eq' ≤ Rpos(η,M,ε,R) Q` for an explicit scalar `Rpos`. This removes the
endpoint-error circularity and supplies exactly the `R₁` input of the compact
four-trajectory phase theorem. Remaining are synchronization of the compact
constants in the position and phase bounds and induction over the grid.

The scalar phase recurrence is now closed as well. Substituting the endpoint
position rate removes the new error from the right-hand side and produces one
homogeneous coefficient plus explicit compact forcing. For `|ε|≤1`, Lean
proves that coefficient satisfies

```text
K(ε) ≤ 1 + C(D,M)|ε| ≤ exp(C(D,M)|ε|),
```

where `D=d+1` and `C(D,M)=1+2DM+(DM)²/4`. This is exactly the hypothesis of
the completed fixed-horizon scalar Grönwall theorem. The remaining grid
induction must combine this propagation step with the automatic local
leapfrog-versus-exact truncation term and verify uniform compact containment
and reference-separation bounds at every index.

Grid-time shifting of exact Hamiltonian curves is now formalized. The first
attempt to instantiate the existing local truncation theorem at every shifted
grid point exposed an essential restriction: equal momenta hold at time zero
but generally not at later exact times. Lean now supplies the needed
arbitrary-momentum reference invariant instead. For any two exact curves,
their full Euclidean phase separation is bounded by an explicit exponential
factor times the initial phase separation, uniformly at every intermediate
signed time.

The local numerical theorem has now been generalized from shared local
momentum to arbitrary paired phase differences. Lean proves the position
Taylor remainder after subtracting `t(p₁(0)-p₂(0))`, the corresponding
relative-momentum force-quadrature remainder, and their combined phase bound.
Compact Hessian continuity is instantiated for both arbitrary-paired exact
curves and arbitrary-paired leapfrog endpoints. Their relative displacement
rates contain the necessary linear `|ε|` term, and one common compact modulus
gives an automatic one-step bound proportional to the full initial phase
separation. This theorem is valid after every exact-flow time shift. The next
step is the actual grid induction combining it with the closed propagation
recurrence and the compact containment invariants.

The first grid layer is now complete. Exact reference phases are sampled by
`exactGridPhase`, and the compact local theorem is proved both at an arbitrary
real time shift and at every natural-number grid index. Its arbitrary-phase
rate is factored as `|ε|` times a continuous per-time coefficient; Lean proves
that coefficient can be made uniformly arbitrarily small by choosing the
compact Hessian tolerance and then the step size. A paired-phase triangle
lemma composes homogeneous four-trajectory propagation with this shifted
local truncation, and a finite-grid theorem accumulates the resulting error
over `n|ε|≤T` with the proved discrete Grönwall bound. A conversion lemma
turns the automatic compact local estimate into the constant-forcing form
using a uniform exact-reference phase bound.

The compact propagation constants are now synchronized. Lean exposes the raw
four-trajectory phase estimate in terms of the actual old and new position
errors, chooses one minimum displacement radius and maximum Hessian bound for
the position and phase estimates, and closes them into the recurrence

```text
Eₖ₊₁ ≤ exp(C|ε|) Eₖ + |ε| s Q.
```

Both `C` and the propagation forcing coefficient `s` are explicit and
nonnegative. A sequence-level theorem derives this recurrence from pointwise
compact membership, closeness, and reference-separation premises. The
fixed-horizon theorem combines that propagation forcing with shifted exact
local truncation, adding their rates before discrete Grönwall. Remaining are
to synchronize this package with the separately selected local-truncation
radius and Hessian constant and to prove numerical-grid containment and
closeness inductively from the buffered exact compact family.

The individual containment layer is now formalized. The paired relative
error cannot control either numerical path's distance from its own exact
reference, so Lean now separately proves absolute exact-flow integration
bounds, an automatic quadratic one-step leapfrog phase error on every bounded
exact phase family, and its fixed-horizon accumulation:

```text
‖zLFₖ-zexact(kε)‖phase ≤ T |ε| K(B) exp(Cβ T).
```

This estimate holds uniformly at every completed grid index, implies the
corresponding position-distance bound, tends uniformly to zero with the step
size, and turns a positive closed-ball buffer around the exact grid into
membership of the whole numerical grid. The remaining integration work is
to obtain the uniform exact phase bound and buffer simultaneously for the
paper's compact family, apply the result to both coupled trajectories, and
use these generated premises in the synchronized paired fixed-horizon
contraction theorem.

## 2026-08-13: momentum consistency reduced to paired force variation

Lean now preserves the leading-force cancellation in the exact relative
momentum equation. A uniform paired force-variation bound controls the error
of left-endpoint force quadrature, while leapfrog's two half-kicks give the
corresponding trapezoidal residual. Together they yield the explicit one-step
relative momentum estimate

```text
‖ΔpLF-Δpexact‖ ≤ (d+3/2)|ε|ω ‖q₁-q₂‖.
```

Combining this with the completed position estimate gives a full paired phase
local-consistency theorem. For a step-dependent force modulus `ω(ε)` that is
continuous and vanishes at zero, the phase error is `|ε| r(ε)‖q₁-q₂‖` with
`r(ε)→0`. Thus the remaining analytic obligation is sharply localized: derive
such a compact-uniform paired force modulus from the paper's `C²` potential
assumption, then accumulate the resulting local error over the fixed horizon.

## 2026-08-13: one-step relative leapfrog position consistency

For two exact Hamiltonian curves started from positions `q₁,q₂` with shared
momentum, Lean now compares their signed-time position difference directly
with one shared-momentum leapfrog update. The exact relative displacement
bound and leapfrog's explicit half-force term give a relative local position
error

```text
‖(LFε(q₁,p)-LFε(q₂,p))q - (q₁(ε)-q₂(ε))‖
  ≤ C(ε)|ε|² ‖q₁-q₂‖.
```

The explicit rate is nonnegative, continuous in the signed step size, and
zero at `ε=0`; hence every positive one-step relative allowance holds on one
symmetric small-step neighborhood. This closes the position component of
local consistency. The remaining numerical core is the corresponding
relative momentum/force-integral consistency and its stable accumulation over
`O(1/|ε|)` steps. That step must preserve cancellation near the diagonal and
cannot be replaced by two unrelated absolute trajectory errors.

## 2026-08-13: compact-uniform exact-flow contraction horizon

The curve-dependent absolute phase bound is now dominated by a common bound
whenever initial phase norm is at most `M`. Its position-displacement
allowance, the relative-displacement rate, and the squared relative-momentum
rate are continuous functions of signed time and vanish at zero where
required. Lean simultaneously selects `δ=1/2`, `κ=α/2`, and one positive
symmetric horizon satisfying containment and both contraction budgets.

Combining this scalar certificate with the compact-core buffer proves the
compact-uniform exact Hamiltonian-flow contraction theorem: every pair of
classical Hamiltonian curves with shared initial momentum, initial positions
in the compact core, and initial phase norms bounded by `M` contracts with one
common quadratic factor throughout the selected horizon. This completes the
continuous-flow analytic core of Lemma 4.2. The remaining general-potential
work is the compact-uniform relative numerical error transferring this result
to leapfrog trajectories.

## 2026-08-13: buffered compact-core exact-flow containment

Absolute exact Hamiltonian phase growth now has a two-sided Grönwall bound
with the affine forcing term `‖∇U(0)‖`. Integrating its momentum component
gives an explicit signed-horizon position-displacement allowance. Lean proves
that if this allowance fits inside a closed-ball buffer around the initial
position, the complete exact trajectory stays in the desired region.

The geometric buffer is also constructed uniformly. Every compact core
contained in the interior of the local strong-convexity region admits one
positive radius whose closed ball around every core point stays in that
region. Combining the buffer with the displacement estimate yields uniform
containment for any exact curve satisfying the corresponding scalar bound,
and the two-curve contraction theorem now consumes these explicit buffered
premises. The subsequent horizon-selection theorem above now discharges all
of those inequalities simultaneously.

## 2026-08-13: Grönwall exact-flow stability closes relative motion

The relative Hamiltonian phase state now satisfies a machine-checked
Grönwall bound under the paper's global gradient-Lipschitz assumption. Time
reversal extends the exponential estimate to signed integration times, and a
named finite-horizon factor uniformly controls position separation throughout
the unordered time interval.

This exponential upper bound feeds the previously proved force and
displacement integrations. Consequently the quantitative exact-flow
contraction theorem now derives upper separation, relative momentum, and
lower separation internally. Apart from explicit scalar short-time budgets,
its only remaining trajectory premise is containment in the local
strong-convexity region. The reduced theorem is also connected directly to
the aligned numerical trajectory-cost budget.

## 2026-08-13: lower exact-flow separation from short-time displacement

Integrating the relative-momentum estimate a second time now bounds the change
in relative position by `O(t²)` times the initial separation, uniformly for
either sign of time. An explicit short-time budget converts this displacement
bound into the uniform squared lower-separation factor `(1-δ)²`.

The exact-flow contraction and aligned trajectory-cost theorems now derive
both relative momentum and lower separation internally. Their remaining
geometric inputs are only a uniform upper position-separation bound and
containment in the local strong-convexity region. This removes another
independent analytic premise from the general Lemma 4.2 path.

## 2026-08-13: relative-momentum estimate from position control

For exact Hamiltonian curves with shared initial momentum, global gradient
Lipschitzness now integrates the relative force over either sign of time. A
uniform Euclidean position-separation bound therefore gives an explicit
`O(|t|)` relative-momentum bound, and its squared relative form is
`O(t²)` times the initial squared position separation.

The local-strong-convexity contraction theorem now consumes this estimate
directly. Given compact-uniform upper and lower position-separation bounds,
region containment, and an explicit scalar budget, it derives the momentum
premise and proves the two-sided contraction factor. The same reduced premise
surface is connected to the downstream aligned trajectory-cost theorem. Thus
relative momentum is no longer an independent open part of Lemma 4.2. The
subsequent displacement result above also derives lower separation.

## 2026-08-13: two-sided exact-flow contraction calculus

Hamiltonian time reversal is now formalized: reversing time and negating
momentum sends any classical Hamiltonian curve to another curve for the same
potential. Applying the positive-time second-variation theorem to the reversed
curves gives the quantitative squared-separation estimate for negative times,
and a single theorem now covers every signed integration time using the
unordered interval between zero and that time.

The local-strong-convexity specialization is likewise two-sided. Thus the
sign of the trajectory index is no longer an open part of Lemma 4.2. The
subsequent force-integration result above has also removed relative momentum
as an independent premise.

## 2026-08-13: unconditional scalar Gaussian exact lag-one tail

The remaining scalar HMC drift obligation is closed for the actual
standard-quadratic multinomial-HMC transition with `ε=√2` and `L=1`. Lean
proves the exact endpoint defect `p²/2-q²/4`, bounds the capped retention
contribution by splitting at `|q|=2|p|`, and integrates the resulting linear
moment bound against the standard Gaussian momentum law. This yields the
strict affine certificate `KV≤(1/2)V+b`, where `b` is an explicit finite
expression in the Gaussian first norm moment.

Consequently, for every nonzero Gaussian-RWMH variance and every deterministic
initial position, the verified sticky multinomial-HMC/RWMH mixture has finite
`C₀`, a rate `κ<1`, and the actual path-law exact lag-one bound
`P(τ>n)≤C₀κⁿ`. This is the first fully instantiated continuous-state meeting
theorem in the project: neither RWMH, multinomial HMC, their couplings, drift,
small-set access, nor the meeting-time recurrence is assumed as an external
kernel-level premise.

## 2026-08-13: exact implemented-HMC expectation interface

The position-space multinomial-HMC kernel now has an exact `lintegral`
formula that unfolds all of its algorithmic randomness: independent momentum
refresh, uniform trajectory rooting, multinomial trajectory-index selection,
and projection back to position. This is an equality for the implemented
mathlib kernel, rather than an estimate for an assumed HMC transition.

For the scalar drift validation route, the standard-quadratic leapfrog
position is now reduced algebraically to
`(1-ε²/2)q+εp`. At `ε=√2`, every selected point of the two-point randomly
rooted trajectory has position exactly `q`, `√2 p`, or `-√2 p`. The remaining
strict drift proof must control the multinomial probability of retaining `q`
and integrate that bound against the standard Gaussian momentum law; the
trajectory dynamics and kernel expectation are no longer opaque.

The scalar reduction now also proves that both randomized roots have the same
endpoint energy defect and bounds their current-index probability by
`min(1, exp(p²/2-q²/4))`. Summing over selected indices and roots gives a
drift-ready inequality for the actual position HMC kernel against one explicit
standard-Gaussian integral. A final bridge proves that any affine bound on
this displayed scalar envelope is exactly the ordinary HMC drift premise used
by the end-to-end Xu theorem. Thus the remaining Gaussian drift obligation is
now solely an elementary capped-exponential moment estimate; it no longer
contains PMFs, randomized roots, leapfrog trajectories, or kernel composition.

## 2026-08-13: one-dimensional Xu geometry and HMC-only closure

For the scalar standard quadratic potential, Lean identifies the image of the
energy sublevel `{q | U(q)≤E}` exactly as `[0,E]`. From every finite `ℓ₁>1`, it
constructs a larger energy region and intermediate `ℓ₀` satisfying all three
of Xu's sublevel-containment and strict energy-range conditions. This removes
the remaining geometric premise for the one-dimensional validation target.

The resulting public theorem starts from only a strict finite affine drift
inequality for the actual implemented standard-quadratic multinomial-HMC
kernel. It internally constructs the RWMH mixture weight, `ℓ₁`, `ℓ₀`, local
region, deterministic initial coupling, compact positive-volume proposal
region, and full `XuTheorem41DriftAssumptions`; it then invokes the verified
sticky HMC/RWMH theorem and concludes finite `C₀`, subunit `κ`, and the actual
exact lag-one tail `P(τ>n)≤C₀κⁿ`. Thus a single concrete HMC drift inequality
is now the only missing premise for an end-to-end continuous Gaussian instance.

## 2026-08-13: automatic Xu scalar parameter selection

Proved generically that any strict HMC drift rate `λ<1` and finite RWMH growth
coefficient admit a sufficiently small positive mixture probability `γ<1`
for which Xu's `λ₀<1`. Given that inequality and finite branch allowance,
Lean then selects a finite `ℓ₁>1` large enough to make the paper's final paired
rate strictly below one. The proof uses the actual `ENNReal` formulas and
convergence of reciprocal finite thresholds to zero.

The standard-Gaussian specialization combines both selections. From an HMC
rate below one, finite HMC allowance, and nondegenerate RWMH variance, Lean
constructs `γ` and `ℓ₁` satisfying both scalar fields. The selected `ℓ₁` must
still be connected to suitable geometry in higher dimensions; this is now
complete for the scalar validation target. The strict multinomial-HMC drift
remains the central unproved certificate.

## 2026-08-13: standard-Gaussian Xu certificate constructor

Every deterministic initial law `δ(q₀)` now has a proved finite moment for
`V(q)=1+dist(q,0)`. The public module `QuadraticGaussianXu` assembles a full
`XuTheorem41DriftAssumptions` value for the verified standard-quadratic
multinomial-HMC/Gaussian-RWMH kernels once supplied the remaining HMC affine
drift, sublevel-containment, energy-level, and selected scalar parameters. It
fills measurability, `V≥1`, RWMH growth, and the initial moment from proved
results.

The same module proves that any assembled certificate using this `V`
automatically has the compact, nonempty paired sublevel required by the
concrete sticky-mixture exact lag-one theorem. This removes the previous need
to pass those topological facts separately. The unresolved mathematical core
is now visibly the HMC drift and compatible geometric containment, not kernel
validity, RWMH growth, scalar selection, initialization, or topology.

## 2026-08-13: finite Gaussian moment and concrete RWMH growth

Proved that the finite-dimensional isotropic Gaussian density has a finite
first norm moment. The proof works directly with mathlib's `withDensity`,
product-volume, Gaussian `L¹`, and finite-product integrability APIs. A generic
MH lemma now bounds any nonnegative observable by its full proposal expectation
plus its retained current value; translation invariance specializes this to
additive random walks.

For `V(q)=1+dist(q,0)`, Lean proves the actual verified Gaussian RWMH kernel
satisfies
`QV(q) ≤ μ(V(q)+1)`, where
`μ = 2 + E‖Z‖` and `Z` is its isotropic Gaussian increment. The coefficient is
strictly positive and finite for every nondegenerate variance. This is also
instantiated on the standard-quadratic Boltzmann target, so the RWMH growth
field of Xu's drift assumptions is no longer open for that specialization.
The scalar validation target now requires only the HMC affine drift; compatible
sublevel containment remains for higher-dimensional specializations.

## 2026-08-13: canonical Lyapunov sublevel topology

Defined the finite-dimensional candidate `V(q)=1+dist(q,0)` as an
everywhere-finite measurable `ENNReal` function with `V≥1`. Its additive
paired sublevel is now proved compact at every finite threshold and nonempty
at every threshold at least two. Since Theorem 4.1 assumes `ℓ₁>1` and
`ℓ₁<∞`, its threshold `1+ℓ₁` automatically meets both conditions whenever
this candidate is used. This discharges only the topological side conditions;
the HMC affine drift and sublevel-containment hypotheses remain to be proved
for a concrete specialization. The Gaussian RWMH growth, deterministic
initial moment, and scalar selection have since been discharged above.

## 2026-08-13: exact lag-one Theorem 4.1 closure

The verbatim asymmetric Xu drift assumptions now imply a geometric tail for
the actual exact lag-one equality time, not only relaxed-diagonal entry,
provided the coupled mixture is faithful and has a positive exact-meeting
small-set bound on the paired Lyapunov sublevel. The proof uses Algorithm 1's
verified `laggedInitialMeasure`, so ordinary diagonal entry of the paired
Markov state is exactly `Xₙ = Yₙ₋₁`; its finite initial weighted moment follows
from the assumed one-chain moment and affine mixture drift. A separate generic
lemma composes Proposition-4.1-style relaxed accessibility with uniform
exact-diagonal accessibility, multiplying their constants and producing a
finite-step exact-meeting small set. Remaining work is to instantiate that
second access bound when following the paper's relaxed-entry route.

For the concrete verified algorithm, an even more direct closure is now
complete. On any compact nonempty paired Lyapunov sublevel, the localized
Gaussian proposal-density and simultaneous-acceptance floors give the sticky
HMC/RWMH mixture a positive one-step exact-meeting constant. The generalized
exact lag-one theorem accepts this sticky coupling directly, uses its proved
marginals and faithfulness, and returns finite `C₀` and subunit `κ` with the
actual tail bound `P(τ>n)≤C₀κⁿ`. What remains for an instantiated example is a
concrete Xu drift certificate. Compactness and nonemptiness are automatic for
the canonical distance Lyapunov candidate recorded above.

## 2026-08-13: Gaussian aligned squared-cost contraction

For shared-momentum standard-quadratic trajectories, the overlap-weighted
aligned exponent-two cost now factors exactly into the squared leapfrog
position coefficient and the initial squared separation. Since every stable
coefficient has modulus at most one, its square is bounded by the already
proved coefficient; the same explicit positive-window subunit rate therefore
controls the aligned squared cost. This closes the aligned part of the
Gaussian transport-coupling argument. A relative squared-cost bound for the
residual mismatched-index transport remains separate.

The finite transport layer now also proves the complementary lower bound.
Every coupling has mismatch mass at least the total variation of its
marginals, so a positive off-diagonal cost floor forces transport cost at
least `dTV` times that floor; the theorem is specialized to the selected
optimal transport coupling and includes an explicit contradiction criterion
for proposed smaller upper bounds. This identifies the precise danger in the
remaining Gaussian argument: a first-order TV estimate alone cannot yield a
second-order transport estimate on a fixed separated categorical support.
No Gaussian counterexample is claimed yet; the next step is to analyze whether
the trajectory geometry removes the positive-floor premise as the grid is
refined.

That audit is now instantiated at one concrete grid. In one dimension with
step size one, one leapfrog step, origin zero, and shared momentum one, Lean
derives the exact scalar leapfrog energy defect and proves that the actual
two-index `trajectoryIndexPMF` endpoint atom is its logistic Boltzmann
probability. Its derivative at coincident position zero is explicitly nonzero,
so the categorical TV distance has a first-order lower bound. Meanwhile both
unequal-index squared position costs converge to one and are locally at least
`1/2`. The general finite lower bound therefore proves that even the selected
optimal transport coupling costs at least half the TV discrepancy locally.

This is a machine-checked fixed-grid obstruction to a quadratic near-diagonal
bound. It is not yet a counterexample to the paper's quantified small-step
claim, because that claim may restrict to arbitrarily smaller positive step
sizes. The next audit must parameterize the calculation by `ε` and check
whether the same first-order/positive-floor mechanism persists for every
`ε > 0`.

The calculation is now parameterized by `ε`. For every `0 < ε ≤ 1`, Lean
derives the defect polynomial, proves the endpoint probability derivative at
zero is nonzero, identifies the actual `trajectoryIndexPMF` atom, and proves
both unequal-index squared costs are locally at least `ε²/2`. The optimal
finite transport cost is therefore lower-bounded by the linearly varying TV
distance times this strictly positive floor for every such fixed step size.

This closes the arbitrary-step `L=1` audit but still does not refute the
repaired positive-window Condition 1: with two indices the integration time is
only `ε`, whereas that condition requires `Tmin ≤ εL`. The next decisive
step is to carry the same finite-support analysis to lengths `L` satisfying a
fixed positive integration window.

The asymptotic implication is now a reusable finite-transport theorem. Given
a first-order TV lower bound and an eventually positive common off-diagonal
cost floor, Lean proves that optimal transport cost eventually exceeds
`R q²` for every prescribed real rate `R`. A separate finite-minimum lemma
constructs such a common positive floor from pointwise positivity on any
nontrivial finite index type. The arbitrary-step two-index Gaussian audit
instantiates the full theorem. For positive-window lengths, the remaining
geometric input was injectivity (or another positive-separation certificate)
for the finite Gaussian trajectory positions.

That geometric input is now discharged on horizons `Lε ≤ 1`. The scalar
momentum-to-position coefficients satisfy the leapfrog recurrence, have an
exact Chebyshev-`U` form, and obey the division-free sine identity
`bₙ sin θ = ε sin(nθ)` for `θ = arccos(1-ε²/2)`. The existing angle bounds
then make the coefficients strictly increasing for `0 < ε ≤ 1` through
physical time one. Lean connects these coefficients to the actual origin-
rooted offset trajectory, proves every unequal-index squared-position cost is
positive, and extracts a common positive floor by finiteness. The remaining
positive-window obstruction input was first-order variation of at least one
normalized multinomial trajectory weight.

That final input is now discharged without differentiating the whole
normalizer explicitly. For every `L ≥ 1`, the ratio of the normalized atoms at
indices one and zero cancels all trajectory-normalizer terms and equals the
exponential of the already verified one-step energy defect. Since this ratio
has nonzero derivative, both atom derivatives cannot vanish. The atoms are
identified with the real values of the actual `trajectoryIndexPMF`; Lean then
derives a first-order TV lower bound. Continuity of every finite squared-cost
entry makes half of the coincident-grid cost floor persist locally. Combining
these facts with the generic finite transport obstruction proves that for any
fixed `0 < ε ≤ 1`, `0 < L`, `Lε ≤ 1`, and real rate `R`, optimal squared index
transport eventually exceeds `R q²`. This result concerns a fixed unit-
momentum trajectory grid. A direct corollary in the exact exponent-two
Condition 1 cost language proves that no bound can hold uniformly over all
nearby positions on any one such grid. The repaired Condition 1 quantifies
pointwise over all momenta below its cutoff, so this obstruction arises before
momentum averaging. The full numerical quantifier theorem is now supplied for
every positive window with `Tmin ≤ 1`. From an arbitrary proposed `εbar`, Lean
chooses a natural `n` with `Tmin/n < min εbar 1`, then takes `L=n` and
`ε=Tmin/n`. This satisfies both window inequalities exactly at the lower
endpoint and falls under the controlled-horizon obstruction. Hence no
exponent-two transport `XuCondition1AtExponentOnIntegrationWindow` exists on
the full scalar position space for such a window, at any rate. The theorem
does not cover windows starting after physical time one.

## 2026-08-13: Algorithm 5 finite marginal repair

Added `Mcmc.Finite.MarginalRepair`. For an arbitrary joint PMF and desired
finite marginals, equation (20)'s retained coefficient is represented as the
finite minimum of one and all active target/candidate marginal ratios. Lean
proves that coefficient is admissible and maximal among every admissible
choice.

For a strict coefficient, subtracting the retained marginal mass leaves total
mass `1-α`; normalization produces residual PMFs. Mixing the original joint
with their independent coupling has exactly the target marginals. The
weight-one case is proved to mean the candidate was already a coupling, and
the full construction then returns it unchanged. The construction is also
specialized to approximate multinomial-HMC trajectory-index joints. Lean proves
that measurable candidate atoms give measurable repaired atoms, then lifts the
repaired family to phase-space and shared-momentum position-space Markov
couplings whose marginals are exactly the verified multinomial HMC kernel.

## 2026-08-13: quantitative exact-flow contraction margin

`Mcmc.Hamiltonian.ExactFlow` now differentiates the full first-variation
formula without assuming equal momentum at the comparison time. Two
applications of the derivative monotonicity theorem show that a uniform
second-variation margin `c` over `[0,t]`, together with shared initial
momentum, reduces squared position separation by at least `c t²`.

The result is specialized to local strong convexity: it is enough to keep
both exact trajectories in the convexity region, bound their relative kinetic
energy by `(α-κ)` times squared position separation, and retain a uniform
lower bound on that separation. This makes the remaining compact-uniform
content of Lemma 4.2 explicit instead of hiding it in an assumed contraction
factor. A primary-source check also clarified that Algorithm 2 and the paper's
theorems use shared momentum; reflection momentum is not a prerequisite.

The contraction is now connected to the downstream trajectory budget.
Squared exact contraction with factor `ρ²` and a relative displacement error
`δ` imply an aligned numerical squared-cost factor `(ρ+δ)²`. The composed
theorem accepts exact Hamiltonian curves, discharges their contraction from
the local-strong-convexity margin theorem, and produces the exact per-index
estimate that can be summed with the categorical overlap weights.

Finally, the positive-window scalar choice is machine checked. From
`0 < κ θ Tmin² ≤ 1`, Lean constructs NNReal `exactRate`, `errorRate`, and
`alignedRate`, proves `errorRate > 0`, proves `alignedRate < 1`, identifies it
with `(exactRate+errorRate)²`, and proves the exact rate works uniformly for
every `t ≥ Tmin`. The numerical analysis therefore has a concrete positive
error budget to target.

The exponent-two Condition 1 interface was then repaired at the categorical
aggregation level. The current-state trajectory index is unchanged, and Lean
now proves that any bound required at every aligned index forces the aligned
rate to be at least one on distinct starts. The new
`XuSharpRelativeMomentTwoBudgetOnIntegrationWindow` retains the actual
overlap-weighted aligned sum, combines it with the TV-weighted mismatch term,
and proves the maximal-coupling condition. Squared-cost optimality transfers
the result to the measurable greedy transport coupling with the same rate and
uniform thresholds.

## 2026-08-13: transport Condition 1 reaches the implemented kernel

The trajectory-index API now separates two logically independent facts about
a parameterized finite coupling: correctness of its two marginals and
measurability of every atom as the paired phase point varies.  The maximal
coupling family satisfies both properties under measurable potential and
gradient hypotheses.  The pointwise optimal-transport family has proved
marginals, while its atom-measurability remains the explicit selector
obligation.

For every measurable family, fixed-exponent positive-window Condition 1 now
implies the corresponding expected output-position moment bound for the
actual randomized-origin Markov kernel.  Specializing to exponent two gives
the implemented optimal-transport trajectory kernel its squared-distance
bound, and a squared-moment Markov inequality turns that bound into the
conditional relaxed-diagonal entry estimate used by the transport route.
This conditional estimate is now integrated through the shared standard
Gaussian momentum refresh.  The resulting full position-kernel lower bound
is the Gaussian kinetic-cutoff mass times the squared-moment Markov factor;
it is proved strictly positive whenever the squared-distance budget is below
the selected relaxed radius.  Thus no probabilistic kernel bridge remains
hidden behind the pointwise cost statement: completing this construction
requires a measurable finite optimal transport selector, followed by the
concrete exponent-two analytic budget.

The algorithmic scope remains unchanged.  RWMH and finite-dimensional
multinomial HMC are themselves defined as mathlib kernels and have proved
target-invariance results; they are not opaque assumptions to the final
coupled-mixture theorem.  Endpoint-only Metropolis HMC is a comparison method
discussed by the paper, not a substitute for the multinomial-HMC kernel that
its main results concern.

The selector interface has also been decoupled from the legacy pointwise
`Classical.choose` optimizer.  `IsOptimalTrajectoryIndexCouplingFamily`
records exact squared-cost minimality and marginal correctness, while
`IsMeasurableTrajectoryIndexCouplingFamily` records the independent kernel
regularity obligation.  Any family satisfying both now produces an actual
randomized-origin and shared-momentum Markov kernel, with proved multinomial
HMC marginals.  Maximal-family exponent-two Condition 1 transfers to any such
optimal family, and the full position-kernel relaxed-entry theorem is proved
at this abstract selector interface.  Therefore a constructive selector no
longer has to be propositionally equal to mathlib's arbitrary classical
choice; it only has to prove the mathematically relevant optimality,
marginal, and measurability properties.

The pinned mathlib source currently exposes no general measurable argmin
selection theorem; its Bayes-estimator module likewise leaves existence of a
measurable argmin as a separate hypothesis pending measurable-selection
infrastructure.  A concrete finite LP tie-breaking construction is therefore
still required rather than assuming measurability of `Classical.choose`.

The deterministic tie-breaking half of that construction is now available in
`Mcmc.Finite.MeasurableSelection`.  For any finite candidate type and
jointly measurable extended-nonnegative score, `fintypeArgmin` chooses an
actual minimum, is measurable, and preserves measurability when used to
evaluate a jointly measurable candidate family.  This avoids any measurable
selection theorem once the feasible optimal plans have been reduced to a
finite parameterized candidate family.  The remaining finite-LP step is to
enumerate a complete family of transportation-polytope vertices (or an
equivalent finite family), prove each candidate plan measurable in the two
marginals, and prove that at least one candidate attains the global transport
minimum.  The pinned mathlib source has no ready-made finite LP vertex theorem,
so that completeness argument remains to be formalized locally.

`Mcmc.Finite.GreedyTransport` now provides a measurable finite selector.
A complete edge order greedily allocates residual row and column masses;
conservation and exhaustion prove that every candidate is a PMF coupling.
Finite argmin measurably selects the least-cost candidate.

The analytic half of that combinatorial proof is now in
`Mcmc.Finite.TransportPolytope`. Finite ENNReal masses are embedded in a
real transport polytope, proved to be a nonempty closed subset of mathlib's
compact standard simplex. Hence linear transport cost attains a minimum, and
a quadratic concentration tie-breaker attains a maximum on the optimal face.
Lean proves that the resulting optimal plan admits no nonzero two-sided
feasible balanced perturbation, and therefore has no algebraic balanced
support cycle.

The cycle-perturbation side of that graph equivalence is now formalized too.
`transportSupportGraph` records exactly the positive entries as edges between
the row and column copies and is proved bipartite. An explicit finite
alternating-cycle presentation generates a balanced signed direction; Lean
proves row and column cancellation, nonzeroness, and the entrywise bound
needed for two-sided feasibility. A common positive amplitude is obtained as
the minimum of the finitely many cycle-edge masses. Every mathlib support
cycle is reindexed into this presentation, so the selected optimizer's
positive-support graph is acyclic.

The forest-to-greedy algebraic half is now complete in
`Mcmc.Finite.GreedyTransportCompleteness`. Remaining row and column masses
are defined relative to an unprocessed edge list, together with the precise
leaf-elimination predicate. Lean proves that greedy allocation at each leaf
is exactly its prescribed target mass and maintains an exact invariant for
all residual marginals and processed atoms through the entire fold. Thus any
complete duplicate-free leaf-elimination order reproduces a feasible
transport table exactly and determines an equal member of
`CompleteEdgeOrder`.

That forest lemma and the complete-order construction are now proved. A
finite acyclic graph containing an edge is reduced to its nontrivial connected
component, where mathlib's tree leaf theorem supplies a degree-one vertex.
Strong induction removes the corresponding transport edge and constructs a
leaf order for every positive support edge. All zero table cells are then
appended; Lean proves completeness, duplicate-freeness, and preservation of
the leaf predicate. Real feasible plans are converted coordinatewise through
`ENNReal.ofReal`, with feasibility and exact support-graph correspondence
proved. Consequently every feasible real plan with acyclic positive support
is represented exactly by a `CompleteEdgeOrder` greedy candidate. Exact
real/ENNReal transport-cost conversion closes
`greedyTransportCandidatesComplete` unconditionally. The trajectory-index
selector is therefore measurable and globally squared-cost optimal, and the
shared-momentum HMC relaxed-entry theorem no longer carries a finite selector
completeness premise.

## 2026-08-13: Xu Theorem 4.1 drift-to-lagged-tail closure

The paper's asymmetric drift hypotheses now imply the exact one-chain mixture
bound with rate `λ₀` and allowance `(1-γ)b+γμ`. Its displayed scalar
inequality selects a strict subunit paired rate, absorbs the doubled allowance
outside the `1+ℓ₁` additive Lyapunov sublevel, and places that paired sublevel
inside `S × S`.

For the probabilistic renewal step, Lean now treats an arbitrary measurable
target rather than assuming a relaxed diagonal is absorbing. A weighted
kernel killed on target entry contracts geometrically; its powers equal the
actual finite path-avoidance probabilities. Drift plus a positive one-step
target-entry bound on the sublevel automatically supplies a finite positive
weight scale and a subunit contraction rate.

Algorithm 1's indexing is represented explicitly: `laggedInitialMeasure`
first draws `X₁ ∼ K(X₀,·)` while retaining `Y₀`, so its marginals are `π₀K`
and `π₀`, and the subsequent paired path state is `(Xₙ,Yₙ₋₁)`. The finite
initial `V`-moment and affine mixture drift prove that this lagged initial law
has finite paired moment. Consequently
`exists_geometric_relaxedPairMeetingTail_initial` produces finite `C₀` and
`κ<1` with the path-law bound `C₀ κⁿ` from the encoded Theorem 4.1 assumptions,
verified branch couplings, and local HMC relaxed accessibility.

Remaining work is algorithm-specific: a concrete Lyapunov certificate,
alignment of its sublevel with the Gaussian accessibility region, and the
separate transport-coupling construction. The printed zero-time Condition 1
issue remains explicitly repaired by the positive integration-time window.

## 2026-08-13: full Gaussian HMC relaxed accessibility

The positive-window Gaussian maximal-coupling estimate is now integrated over
a positive-mass standard-Gaussian kinetic-energy cutoff. Lean proves that,
from every pair of positions in a fixed positive-radius ball, the complete
shared-momentum/maximal-index position HMC coupling enters one relaxed
Euclidean diagonal in one step with a single strictly positive lower bound,
uniformly over every sufficiently small step size whose integration time lies
in the prescribed positive window.

The Euclidean event is contained in mathlib's ambient-metric relaxed diagonal,
so `standardQuadratic_maximalSharedMomentum_isRelaxedMeetingAccessible`
packages the result directly as `IsRelaxedMeetingAccessibleFrom`. This closes
the conditional-kernel-to-full-kernel bridge for the Gaussian maximal route.
The corresponding deterministic-start path law is proved to have relaxed
failure probability at most `1 - entry` after that step.
It does not yet prove the paper's global meeting-time result: recurrence from
unbounded initial states under the verbatim drift assumptions and the separate
transport-coupling construction remain open.

The drift side also now reaches the actual one-chain mixture. A generic theorem
combines affine drift certificates under kernel mixtures, and
`XuTheorem41DriftAssumptions.mixture_hasAffineDrift` derives exactly the
paper's `λ₀` rate and `(1-γ)b+γμ` allowance from its asymmetric HMC and RWMH
premises. The remaining bridge is the repeated-return/lagged coupling argument,
not the elementary mixture algebra.

## 2026-08-13: finite transport costs lifted to kernel expectations

Finite `transportCost` is now proved equal to the Lebesgue integral of the
cost against a PMF's mathlib measure. Applying this identity to coupled
trajectory selection shows that the expected output position distance of a
fixed-origin coupled trajectory kernel is exactly its finite index transport
cost. Averaging over the shared uniform origin preserves any bound uniform in
that origin.

Consequently exponent-one positive-window Condition 1 now yields a genuine
conditional expected-distance theorem for the actual randomized-origin
maximal coupled trajectory Markov kernel. The standard Gaussian specialization
instantiates this theorem at one common rate below one, uniformly for starting
positions in a positive-radius ball and shared momenta under any fixed kinetic
cutoff. Every positive kinetic cutoff is now also proved to have strictly
positive standard-Gaussian momentum mass, using an explicit open ball inside
the cutoff event. The shared momentum lift row is identified as the
pushforward `p ↦ ((q₁,p),(q₂,p))`; the subsequent milestone above performs
the required integration and packages the resulting full-kernel accessibility
theorem.

## 2026-08-13: Gaussian positive-window Condition 1 instantiated

The sharp first-moment maximal-coupling budget is now instantiated on every
positive-radius closed ball for the standard Gaussian target. Lean derives a
uniform phase bound from the position ball and kinetic-energy cutoff, chooses
one positive step-size threshold for the absolute energy, relative energy,
and TV-weighted off-diagonal budgets, and reserves half of the explicit
aligned-rate gap for mismatch. The summed rate is proved strictly below one.

Consequently
`standardQuadratic_exists_maximal_xuCondition1OnIntegrationWindow` gives an
end-to-end specialization of the repaired positive-integration-window
Condition 1 for the maximal multinomial-index coupling. This is not a proof of
the paper's verbatim printed Condition 1: its quantification down to zero
integration time remains formally impossible on any set with two distinct
states. The remaining paper-level work is the relaxed small-set/drift/
lag-one-meeting chain and the distinct transport-coupling implementation.

## 2026-08-13: relative Gaussian centered-energy defect

For two standard-quadratic leapfrog trajectories started from positions
`q₁,q₂` with shared momentum, Lean now proves a one-step Hamiltonian-defect
Lipschitz estimate with the explicit cubic step-size rate. Phase separation
and phase size are propagated over a fixed horizon, and telescoping gives an
accumulated bound of order
`T |ε|² ‖q₁-q₂‖` times an explicit bounded-phase factor. The result covers
negative leapfrog time and every index of an offset randomized trajectory.

This supplies the baseline-canceling relative centered-energy hypothesis used
to control total variation between the two multinomial index laws. It is now
combined with uniform bounded-region constants and the overlap-weighted
aligned rate in the Gaussian positive-window Condition 1 theorem above.

## 2026-08-13: faithful first-moment maximal-coupling route

Added the exponent-one maximal-coupling decomposition and the relative
positive-window certificate
`XuSharpRelativeMomentOneMaximalBudgetOnIntegrationWindow`. Lean now proves
that the overlap-weighted aligned distance and the total-variation-weighted
off-diagonal distance add to establish repaired Condition 1 for maximal
coupling at exponent one. A positive aligned rate and subunit summed rate give
the full repaired interface. This matches both the moment and the weighted
decomposition used in the paper's maximal-coupling argument; the existing
exponent-two certificate remains the distinct squared-cost route relevant to
optimal-transport coupling.

The initially introduced uniform per-index certificate remains as a valid
sufficient interface, but it is not the intended analytic route. Lean proves
that its aligned rate must be at least one for distinct starts: the trajectory
always includes the current-state index, whose aligned cost equals the initial
distance exactly. The sharp interface retains `Σᵢ min(pᵢ,qᵢ) cost(i,i)` and
therefore permits average contraction even though that one index does not
contract.

The standard-quadratic specialization now reaches this corrected interface.
Every aligned exponent-one offset cost is exactly the absolute signed
leapfrog position coefficient times the initial distance, and the entire
overlap-weighted aligned term is factored as a dimensionless finite scalar sum
times that distance. The remaining Gaussian contraction proof is therefore a
uniform scalar-weight estimate over the positive integration-time window, not
an unresolved phase-space identity.

That scalar analysis now has an exact closed form. The Gaussian leapfrog
position coefficient satisfies the Chebyshev recurrence and equals
`cos(n·arccos(1-ε²/2))`; the same absolute formula holds for signed offsets.
For `0≤ε≤2`, the modified angle is machine-checked to lie between `ε` and
`(π/2)ε`. Consequently every offset whose physical time lies in `[τ,1]` has
absolute coefficient at most `cos τ`, which is strictly below one for
`0<τ≤π`. The remaining weighted contraction task is to show that a uniform
positive amount of overlap mass lies in such an interior offset band.

The overlap-mass reduction is now formalized. A generic finite lemma converts
band overlap weight and a subunit band coefficient into an explicit loss from
the unit weighted-cost budget. Centered trajectory-energy control gives every
multinomial atom the floor
`((L+1)·exp(2δ))⁻¹`, and hence gives any finite band its cardinality times that
floor in overlap mass. For every trajectory origin, a canonical endpoint band
on the longer side is constructed injectively with exactly `L/4+1` indices,
so it occupies at least one quarter of the trajectory. If the total physical
horizon lies in `[Tmin,1]`, every one of those indices has offset time in
`[Tmin/4,1]` and therefore coefficient at most `cos(Tmin/4)`. The remaining
step is ENNReal bookkeeping that turns the quarter-cardinality atom floor into
one uniform aligned rate below one.

That uniform aligned rate is now closed. Quarter-cardinality cancels the
`L+1` denominator in the atom floor, yielding overlap mass at least
`(4 exp(2δ))⁻¹`. The explicit loss
`(4 exp(2δ))⁻¹ · (1-cos(Tmin/4))` is positive, so
`standardQuadraticAlignedRate` is a fixed `NNReal` strictly below one,
independent of step size, length, origin, positions, and momentum. The actual
overlap-weighted exponent-one trajectory cost is proved bounded by this rate
times initial distance whenever the centered energy radius is `δ`.

The TV side is also corrected to use the right relative quantity. A new
baseline-canceling theorem proves `dTV≤4r` when the two centered energy-defect
profiles differ by at most `r≤1/2`; the corresponding relative mismatch
bridge is connected to the sharp budget. For the Gaussian specialization, the
remaining analytic estimate is now specifically a uniform
`O(ε²·initialDistance)` bound on the difference of leapfrog energy-defect
profiles, together with the already available trajectory-radius bound.

The aligned geometric bridge is now sharpened to the form this certificate
needs. Exact-reference contraction plus a numerical error bound on the
*relative displacement* gives multiplicative leapfrog contraction and hence
the aligned exponent-one trajectory-cost bound. This avoids the unnecessarily
strong requirement that each chain's absolute numerical error vanish at
coincident starts. Common position-ball containment also gives the matching
first-moment off-diagonal bound `2R`, and the resulting concrete maximal-cost
estimate is proved. The remaining analytic input is a compact-uniform
relative-displacement error estimate and sufficiently relative control of the
trajectory-law total variation.

The finite normalized-Boltzmann analysis now supplies that TV estimate in a
budget-ready form. For Hamiltonian discrepancy `0≤r≤1/2`, the exponential
envelope is proved to satisfy `dTV≤4r`. Consequently an energy discrepancy
bounded by `energyRate × initialDistance`, combined with an off-diagonal cost
bound, gives exactly the relative TV-mismatch term. A pointwise closure theorem
now combines exact-flow contraction, relative-displacement error, common-ball
containment, and relative energy discrepancy into one expected-distance bound
for maximal trajectory-index coupling. Uniform analytic proofs of those
hypotheses over the positive integration-time window remain required.

## 2026-08-13: obstruction in the printed Condition 1

Auditing the aligned-contraction target exposed an inconsistency in the
printed uniform quantifiers. Condition 1 demands a fixed rate strictly below
one for every `ε>0` and every `L` satisfying only an upper integration-time
bound. In the direct Lean interpretation with `L : ℕ`, `L=0` is admissible and
the sole trajectory point is the current state. Lean now proves
`XuCondition1AtExponent.one_le_rate_of_distinct`: if the contraction set
contains two distinct positions, any such certificate forces `1≤rate`.
Consequently `XuCondition1.not_of_distinct` proves that the printed Condition
1 cannot hold with its required subunit rate.

This is not hidden by weakening a proof obligation. The verbatim definition
and impossibility theorem remain in the API. A separately named repaired
interface, `XuCondition1OnIntegrationWindow`, requires integration time to lie
in a fixed interval bounded away from zero. It is not attributed verbatim to
the paper and will be used for the mathematically viable contraction
development. Even if the paper's convention for `ℕ` excludes zero, its
upper-only integration-time condition still permits times approaching zero;
the same identity-limit issue therefore requires clarification beyond the
specific `L=0` formal counterexample.

Added the non-vacuous coupling-algebra path for the repaired statement. The
initial `XuRelativeMomentTwoBudgetOnIntegrationWindow` is a useful but
too-strong per-index diagnostic: the anchored current-state index prevents a
subunit instance. The viable
`XuSharpRelativeMomentTwoBudgetOnIntegrationWindow` instead retains the
overlap-weighted aligned squared cost, a bounded off-diagonal cost, and the
TV-weighted mismatch contribution. Lean proves that the aligned and mismatch
rates add to give exponent-two repaired contractivity for maximal coupling,
that finite optimal-transport minimality transfers it unchanged to transport,
and that a positive subunit summed rate gives the full repaired condition for
both families. What remains is the geometric analysis needed to instantiate
this sharp budget.

## 2026-08-12: verbatim local-contractivity interface

Added `XuCondition1`, preserving the paper's uniform quantifier order over the
moment exponent, kinetic-energy cutoff, step size, trajectory length, shared
origin, starting positions, and momentum. Both maximal and optimal-transport
trajectory-index couplings are packaged as parameterized families of the
required type. For exponent two, Lean proves that the Condition 1 moment cost
is exactly the squared-position cost already controlled by the concrete
aligned-cost and total-variation estimates, and exposes the remaining error
budget as an explicit premise. Both parameterized families are proved to have
the required multinomial marginals. Condition 1 is factored through its
fixed-exponent core, and squared-cost optimality proves that every exponent-two
certificate for the maximal family transfers to the transport family with
unchanged rate and thresholds. The full uniform maximal-family analytic
budget remains unproved. This is a sufficient shared route; the paper itself
uses a first moment for the maximal argument and squared cost for transport,
so their original analytic routes remain distinct.

Added `XuMaximalMomentTwoBudget` to expose the exact remaining algebraic inputs
to Lemma 4.3: a bound for every aligned trajectory index, a bound for every
off-diagonal index pair, and enough total-variation control that their sum fits
inside the desired squared-distance contraction budget. Lean now proves that
this one uniform certificate establishes exponent-two—and, for a positive
subunit rate, full—Condition 1 for both maximal and transport couplings. Thus
the coupling algebra is closed; constructing the certificate uniformly from
the potential assumptions and leapfrog error estimates remains analytic work.

Refined this interface with `XuRelativeMomentTwoBudget`. Absolute numerical or
TV allowances cannot establish Condition 1 uniformly near the diagonal because
its right-hand side vanishes with initial separation. The new certificate
therefore requires both the aligned cost and TV-mismatch contribution to scale
with initial squared distance. Lean proves the two relative rates add, and a
positive aligned rate with subunit sum establishes full Condition 1 for both
coupling families. This identifies the precise relative error estimates still
needed from the leapfrog and trajectory-weight analysis.

The coincident-start edge case is now proved rather than hidden in the
relative certificate. Added reusable finite lemmas that overlap with itself is
one, canonical maximal self-coupling is diagonal, and diagonal coupling has
zero expected cost for a zero-diagonal cost function. Applied to identical HMC
trajectories, the aligned squared cost and total variation are zero; therefore
both maximal and optimal-transport trajectory couplings have exactly zero
exponent-two position cost at shared coincident starts.

Formalized Proposition 4.2's complete uniform numerical target rather than
only its filter-limit mechanism. `XuProposition42TVConclusion` chooses common
step-size and integration-length thresholds for every positive TV tolerance;
`XuProposition42MaximalMismatchConclusion` gives the equivalent unequal-index
probability statement for canonical maximal coupling. Lean proves their
equivalence and proves that a uniform Hamiltonian-discrepancy envelope implies
both. The general derivation of that envelope is completed below.

Corrected the numerical interface to respect softmax shift invariance. The two
trajectories need not have asymptotically equal absolute Hamiltonians; each
must be nearly constant around its own baseline. Added a direction-dependent
normalized-weight comparison in which the two baseline offsets cancel, then
`XuProposition42UniformCenteredEnergyError`, which proves both exact
Proposition 4.2 conclusions. The earlier cross-trajectory criterion remains a
valid but unnecessarily strong sufficient condition.

The centered property is now proved for standard-quadratic forward leapfrog
trajectories from arbitrary fixed initial positions and shared momentum. The
proof uses the uniform fixed-horizon `O(|ε|²)` energy defect and derives common
step-size/length thresholds, giving a fully validated nontrivial specialization
of Proposition 4.2. This specialization remains a useful exact test case for
the later general theorem.

Extended the quadratic specialization to the actual offset trajectory
construction. The fixed-horizon error bound now covers signed leapfrog powers,
including inverse steps, and every offset index. One set of numerical
thresholds works uniformly over all shared trajectory origins, so every
backward/forward origin-selection rule inherits the centered-energy property
and Proposition 4.2 conclusion.

Connected this conditional result to the randomized transition. Added an
origin-explicit trajectory-family interface, uniform-over-origin and
origin-averaged Proposition 4.2 conclusions, and a finite weighted-average
lemma for `PMF.uniformOfFintype`. A uniform conditional TV bound now provably
survives the actual origin draw. The standard-quadratic specialization proves
both the all-origin and averaged conclusions. The latent randomized selection
experiment is now packaged as an actual joint PMF: first draw the origin
uniformly and then draw the conditional coupled index pair. Lean proves its
unequal-index mass is the averaged conditional mismatch mass and, for maximal
coupling, exactly the averaged TV distance. Proposition 4.2 and its quadratic
specialization are therefore also exposed directly as a bound on the
probability that the concrete randomized-HMC selection chooses unequal
indices.

## 2026-08-13: general Proposition 4.2

Made the numerical-analysis premise used by the supplement explicit.
`LocallyUniformQuadraticLeapfrogEnergyError` asks for a locally uniform
quadratic one-step Hamiltonian defect. Lean telescopes this estimate and uses
the proved phase-size stability to obtain an `O(|ε|)` error over every bounded
integration horizon. The result covers signed leapfrog powers and hence every
randomized backward/forward origin. It implies the all-origin centered-energy
criterion, Proposition 4.2 in TV, and the actual uniform-origin maximal-
coupling mismatch statement. The standard quadratic Gaussian's explicit
cubic defect instantiates this interface.

The previously isolated analytic step is now discharged from Assumption 1.
Lean proves a quadratic first-order Taylor remainder from the globally
Lipschitz gradient, with explicit finite-dimensional norm conversion. An exact
leapfrog energy decomposition then cancels the first-order potential and
kinetic terms and bounds the remainder uniformly on every bounded phase
region. Thus every `RegularPotential` satisfies
`LocallyUniformQuadraticLeapfrogEnergyError`, and Proposition 4.2 now holds for
general regular potentials in its all-origin TV and actual randomized maximal-
mismatch forms. Local strong convexity is not needed for this numerical
statement; it enters Lemmas 4.2--4.4 through aligned contraction.

## 2026-08-12: weighted drift-to-meeting contraction

Defined the Lyapunov meeting weight `W=1+sV` and the one-step weighted
off-diagonal contraction predicate. Faithfulness propagates this predicate
through the finite-time laws, giving the explicit geometric estimate

```text
P(τ > n) ≤ ρ^n ∫ W(x) 1{x off diagonal} μ(dx)
```

for the actual Ionescu--Tulcea path law. The unweighted off-diagonal mass is
bounded by the weighted mass because `W≥1`.

The operator premise is also reduced to the existing Foster--Lyapunov drift
and exact-meeting small-set hypotheses. Lean proves it from separate scalar
inequalities inside and outside the drift set, retaining the allowance and
meeting constant explicitly. For a sublevel set `{V≤R}`, the statewise bounds
are automatic. The contraction rate is defined explicitly as the maximum of
the normalized outside budget and the inside budget, and their strict forms
are proved to imply `ρ<1` and the all-time path-tail estimate. The expanded
conditions are further reduced to `λ<1`, a positive finite threshold, and the
single budget `s(λR+b)<ε`. Positivity of `ε` and finiteness of `λR+b`
automatically produce such a positive finite scale. For deterministic starts
with finite Lyapunov value, the final constant is the explicit finite weight
`1+sV(x)`. This packages repeated meeting attempts without a global
minorization and completes the abstract sublevel-drift closure. It is not yet
the paper's final theorem: the HMC/RWMH mixture's concrete Lyapunov drift
certificate remains open.

## 2026-08-12: concrete mixture drift composition

Proved that Foster--Lyapunov certificates for two coupled kernels combine
under a convex kernel mixture with exactly the mixture-weighted rates and
allowances. Proved separately that sticky modification preserves a drift
certificate when its synchronous diagonal rows satisfy the same inequality.

Defined the additive paired Lyapunov lift `V(x,y)=v(x)+v(y)` and proved that
its expectation under any coupled kernel depends only on the two marginals.
Therefore the verified marginal identities make sticky modification preserve
additive drift automatically; no new diagonal analytic estimate is needed.

These results are instantiated for the exact verified maximal-index HMC and
Gaussian-RWMH mixture. Branchwise drift certificates now imply a drift
certificate for the concrete sticky mixture, and—using its proved compact
meeting constant—the explicit finite-constant geometric meeting tail
`P_x(τ>n) ≤ ρ^n(1+sV(x))`. The remaining work is mathematical rather than
architectural: prove the HMC and RWMH branch drift inequalities for the
paper's selected one-state Lyapunov function and verify the combined rate is
strictly below one.

The remaining coupled-branch premises have since been eliminated. Added an
ordinary single-chain affine drift interface `Pv≤λv+b` and proved that exact
marginals lift it through every self-coupling to additive paired drift.
Outside `{v(x)+v(y)≤R}`, the canonical rate `(λR+2b)/R` absorbs the doubled
allowance. Lean proves this rate is below one from `λR+2b<R`, and proves that
the actual HMC/RWMH weighted rate remains below one. The final concrete
meeting-tail wrapper now assumes only affine drift for the verified ordinary
HMC and ordinary RWMH kernels. Proving those two analytic inequalities for the
paper's Lyapunov function is the remaining drift task for this same-time
specialization.

Reviewing Xu et al.'s actual Theorem 4.1 exposed an important distinction. The
paper uses a relaxed lag-one meeting time and assumes asymmetric bounds
`K(V)≤λV+b` and `Q(V)≤μ(V+1)`, with
`λ₀=(1−γ)λ+γ(1+μ)`, initial integrability, sublevel containment, and a further
scalar condition. Added `XuTheorem41DriftAssumptions` to record this premise
verbatim, plus bridge lemmas to the generic affine interface. The additive
same-time closure above remains correct, but is not presented as Theorem 4.1.
Formalizing the lag-one Heng--Jacob implication is still required.

Added the correct path-space target for that implication. Exact lag-one and
relaxed lag-one failure events are measurable and identified with strict tails
of their `WithTop ℕ` hitting times. Their tail probabilities are antitone, and
a one-step tail recurrence is proved to imply a geometric bound. The relaxed
paired-state convention is now separated explicitly from an ordinary paired
path: when the Markov state is `(Xₙ,Yₙ₋₁)`, entry into the relaxed diagonal is
already the paper's lag-one event and must not shift the second coordinate a
second time. Defined `IsRelaxedMeetingAccessibleFrom` as the uniform
kernel-power conclusion of Proposition 4.1 and proved that it gives the
corresponding finite-horizon bound on the verified homogeneous path law.
Uniform accessibility now composes by Chapman--Kolmogorov, multiplying the
return and relaxed-entry constants. Added a kernel-level expected-distance
contraction interface, its reduction to a uniform bound on bounded paired
regions, and the Markov-inequality theorem turning that bound into positive
relaxed-diagonal mass. Combining these results gives an explicit lagged-state
path-tail bound from return plus contraction. This interface is documented as
a consequence of, not a replacement for, the paper's parameterized Condition
1.
The recurrence itself still has to be derived from local contractivity,
return control, and `XuTheorem41DriftAssumptions`.

## 2026-08-12: uniform exact-meeting small-set interface

Added the uniform notion that a paired set `C` has one common lower bound
`ε` on the next-step diagonal mass. For a Markov kernel, Lean proves that the
corresponding off-diagonal failure probability is at most `1 - ε`. The
constant may be weakened, and a kernel mixture inherits the second branch's
constant multiplied by that branch's mixture weight.

For shared-uniform coupled Metropolis--Hastings, a uniform diagonal proposal
bound and a uniform lower bound on simultaneous acceptance are now proved to
combine multiplicatively into a transition-level exact-meeting small-set
constant. Thus the remaining Gaussian RWMH obligation is exposed as two
quantitative analytic bounds rather than hidden inside the final theorem.

More concretely, a measurable proposal region `A` on which both Gaussian rows
have density at least `q₀` gives diagonal proposal mass at least
`q₀ · volume(A)`. With simultaneous acceptance at least `a₀`, the coupled
RWMH constant is `a₀ q₀ volume(A)`, and the full HMC/RWMH mixture constant is
`(1-p) a₀ q₀ volume(A)`. Lean proves this final expression strictly positive
when the RWMH branch, both floors, and the region volume are positive.

The concrete coupled multinomial-HMC/Gaussian-RWMH mixture now exposes this
transfer theorem directly: any uniform RWMH exact-meeting bound on `C`
becomes a bound `(1-p)ε` for the full mixture. The module also defines the
measurable Foster--Lyapunov drift inequality toward `C` and packages drift
with uniform exact meeting as a named hypothesis.

This milestone deliberately does not infer a uniform constant from merely
pointwise positive RWMH meeting probabilities. Remaining analytic work is to
choose the paper's concrete proposal region and prove positive density and
acceptance floors uniformly over the relevant compact/small set. The separate
path-level tail recurrence must then be derived from drift and return times.

## 2026-08-12: compact Gaussian proposal floors

Proved the reusable extreme-value lemma that a continuous, everywhere
positive `ENNReal`-valued function has a strictly positive common lower bound
on every nonempty compact set. The finite-dimensional isotropic Gaussian
density and its random-walk proposal density are now proved continuous.

Applying the extreme-value lemma to the minimum of the two proposal-row
densities shows that every nonempty compact paired-current set and nonempty
compact proposal region admit one strictly positive Gaussian density floor.
This discharges the proposal-density existence part of the explicit meeting
constant without choosing coordinates or an artificial box.

The accepted-mass theorem is now localized to the portion of the diagonal
lying over the chosen measurable proposal region. Maximal density coupling
mass on this restricted diagonal is bounded below by the common density
integral on the region, and a local simultaneous-acceptance floor converts it
to meeting mass. This localized result is threaded through finite-dimensional
Gaussian RWMH and the concrete HMC/RWMH mixture. No global acceptance floor is
required. The remaining compact step is to construct a positive local
acceptance floor from bounds on the Boltzmann target and Gaussian proposal.

## 2026-08-12: compact Boltzmann acceptance and uniform meeting

For every positive finite even random-walk density, proved that the symmetric
proposal cancels exactly from density-MH acceptance:

```text
α(x,z) = min(w(x), w(z)) / w(x).
```

For Boltzmann weights this is identified with an `ENNReal.ofReal` lift of a
strictly positive continuous real ratio whenever the potential is continuous.
The shared-uniform simultaneous acceptance of two chains proposing the same
point is therefore continuous and strictly positive. The extreme-value theorem
supplies one positive acceptance floor on nonempty compact current/proposal
regions.

Combining compact proposal and acceptance floors with localized accepted mass
now proves an end-to-end uniform statement: for any positive RWMH branch
weight, nondegenerate Gaussian variance, nonempty compact paired-current set,
and nonempty compact proposal region of positive volume, there exists a
strictly positive exact-meeting small-set constant for the concrete coupled
HMC/RWMH mixture. What remains for geometric tails is no longer meeting
minorization; it is the drift and return-time argument producing the path-tail
recurrence.

## 2026-08-12: faithful meeting persistence and geometric core

Defined kernel faithfulness as preservation of the diagonal with probability
one and pathwise faithfulness as persistence of equality at every subsequent
step. For a faithful path, Lean proves that failure to have met through time
`n` is equivalent to the time-`n` pair being off the diagonal.

Defined finite-time off-diagonal mass through the existing kernel-power law.
If a faithful coupled Markov kernel has one global exact-meeting lower bound
`ε`, its off-diagonal mass contracts in one step by `1-ε`; induction gives the
geometric bound `(1-ε)^n`. The proof explicitly uses zero escape from the
diagonal and does not conflate stationarity with convergence.

This is the return-free core of the meeting argument. The paper only supplies
the uniform meeting bound on a compact small set, so completing Theorem 4.1
still requires the Foster--Lyapunov/return-time theorem that guarantees enough
visits to this set.

Faithfulness of the concrete transition is now resolved generically. Defined
a measurable sticky modification of any coupled Markov kernel: off the
diagonal it uses the original coupling, while on diagonal inputs it samples
one marginal transition and copies the result. Lean proves this modification
is Markov, faithful, and has exactly the same two marginal kernels. It also
preserves every existing exact-meeting small-set constant.

Instantiating the construction gives a faithful coupled HMC/RWMH mixture with
the same verified single-chain mixture on both marginals and the same strictly
positive compact meeting constant. Only the drift-controlled return theorem
now separates this concrete kernel from the geometric-tail result.

## 2026-08-12: Lyapunov sublevel return bounds

Defined measurable `ENNReal` Lyapunov sublevel sets and proved the Markov
inequality needed to turn geometric drift into return control. If
`PV(x) ≤ λV(x)+b 1_C(x)` and `V(x) ≤ B` on a starting region, then one step
enters `{V ≤ R}` with probability at least `1-(λB+b)/R`, for finite nonzero
`R`. The bound is packaged as restricted uniform accessibility rather than a
false global uniform statement.

Restricted accessibility followed by a local exact-meeting bound now gives
an explicit skeleton minorization on the same starting region. In particular,
drift plus a meeting bound on `{V ≤ R}` yields a two-step meeting constant
`ε(1-(λB+b)/R)` on every `V ≤ B` region. What remains is the stopping-time or
renewal argument that iterates these state-dependent returns on an unbounded
space, plus a concrete drift certificate for the coupled HMC/RWMH mixture.

The Ionescu--Tulcea adapter is now checked at every time, not just time one:
the coordinate-`n` marginal of the homogeneous path kernel is exactly `P^n`,
and the corresponding path-law marginal is the previously defined finite-time
law. Since failure to meet through `n` implies being off diagonal at `n`, the
finite-time skeleton estimate now yields a theorem about the actual
meeting-time tail under the verified path law. Monotonicity of failure events
extends the skeleton-time result to every time `n`, with exponent
`⌊n/(m+1)⌋`. The concrete sticky HMC/RWMH mixture now exposes this all-time
path-law theorem and proves its geometric factor is strictly below one.

The bounded-Lyapunov case is now closed without an assumed accessibility
constant. If `V ≤ B` globally and `λB+b<R`, drift supplies global one-step
return to `{V≤R}`. A positive meeting constant on that set then gives an
all-time tail with two-step exponent `⌊n/2⌋`. The concrete sticky HMC/RWMH
mixture instantiates this theorem when the sublevel is nonempty and compact,
using its proved Gaussian-RWMH meeting minorization. This does not replace the
unbounded-state recurrence required by the paper.

For the unbounded-state route, defined the transition kernel killed whenever
the paired chain enters the drift set. Lean now proves the iterated estimate
`∫V dP_C^n(x,·) ≤ λ^n V(x)` for starting points outside the set. Under the
standard normalization `V≥1`, the killed mass is bounded by the same quantity
and converges to zero when `λ<1` and `V(x)<∞`. This is the analytic return-tail
core. Its path-space interpretation and renewal consequences are developed
below.

Defined the explicit event that the path avoids the drift set at times
`1,…,n`, together with its measurable finite-history counterpart. Mapping the
verified infinite path kernel to its first `n` coordinates is proved to give
mathlib's `partialTraj`, so the path-event probability is now exactly a
finite-history probability. Its agreement with killed-kernel mass is now
proved at every horizon. The proof uses a stronger invariant: integrating an
arbitrary measurable terminal test function over avoidance-weighted histories
equals integration against the corresponding killed-kernel power. Thus the
state-weighted `λ^nV(x)` bound and convergence to zero apply to the actual
path-space return-failure event. Repeated return/meeting renewal is the
remaining probabilistic step.

Packaged the first strictly positive return as mathlib's `hittingAfter` and
proved that its strict finite tails are exactly the avoidance events above.
The tail sum is bounded by `(1-λ)⁻¹V(x)` and is finite when `λ<1` and the
initial Lyapunov value is finite. Thus both return-tail decay and the finite
mean tail-sum estimate needed by renewal arguments are exposed on the verified
path law.

The finite avoidance events are proved antitone. Continuity from above,
together with their tail limit, shows that their infinite intersection has
zero probability. This intersection is proved equal to
`{firstReturnTime = ∞}`, so strict geometric drift now yields almost-sure
positive return from every outside state of finite Lyapunov value.

## 2026-08-12: finite-step return to skeleton minorization

Defined uniform `m`-step accessibility of a measurable paired set `C` with
return probability `η`. Chapman--Kolmogorov and localized integration prove
that accessibility followed by a one-step meeting bound `ε` yields a global
`(m+1)`-step skeleton minorization `εη`.

Faithfulness is proved closed under kernel composition and all kernel powers.
Consequently the skeleton's finite-time off-diagonal mass is bounded by
`(1-εη)^n` at original-chain times `(m+1)n`. This is instantiated for the
faithful concrete HMC/RWMH mixture and records strict positivity of `εη` when
the supplied return bound is positive.

This supplies a clean sufficient closure when a global uniform finite-step
return bound is available. Such a bound can be stronger than a general
Foster--Lyapunov conclusion on an unbounded state space, where constants may
depend on the initial Lyapunov value. The restricted, state-weighted one-step
return estimate is now proved separately; promoting it to the paper's full
meeting-time recurrence remains.

## 2026-08-12: concrete finite-dimensional HMC/RWMH mixture

Generalized the common-density/residual construction into a reusable
measurable maximal-coupling kernel for parameterized density families. It is
now instantiated with isotropic Gaussian random-walk proposals on every
finite-dimensional `ι → ℝ`. The proposal coupling is Markov, has exactly the
two Gaussian proposal rows as marginals, and gives positive diagonal mass
from every state pair. Shared-uniform accept/reject consequently yields a
finite-dimensional coupled Gaussian RWMH kernel with the already verified
single-chain RWMH kernel on both marginals and positive one-step exact-meeting
probability for every positive finite target density.

The paper-style maximal shared-momentum/index HMC coupling and this RWMH
coupling are now combined on the same `Position ι` state space. Lean proves
that the coupled mixture has the corresponding verified single-chain
HMC/RWMH mixture on both marginals and that this single-chain mixture
preserves the Boltzmann position target. Whenever the RWMH branch weight is
positive, the complete coupled mixture has positive one-step exact-meeting
probability from every state pair.

This does not yet prove geometric meeting tails: the required uniform
drift/small-set recurrence remains substantive and separate from pointwise
positive meeting probability.

## 2026-08-12: mixture transfer of exact-meeting mass

Proved that a normalized kernel mixture dominates the weighted mass of its
second branch on every measurable event. Hence, whenever the second branch
has positive weight, its positive event mass transfers to the full mixture.
For paired kernels on a measurable-equality state space, this specializes to
positive one-step exact-meeting probability on the diagonal event.

This structural bridge is now instantiated by the finite-dimensional
HMC/RWMH milestone above.

## 2026-08-12: exact-flow energy conservation

Proved that the Hamiltonian has derivative zero along every coordinatewise
classical Hamiltonian curve when the force is the gradient certified by
`RegularPotential`, and consequently that its energy is constant at all
times. A quantitative comparison lemma now bounds the energy discrepancy of
two numerical phase points by their respective errors against two exact
curves plus the exact curves' initial energy gap. This removes exact-flow
energy conservation from the outstanding numerical-analysis assumptions and
gives the energy bridge needed for the multinomial-weight TV argument.

The bridge is now lifted through the normalized multinomial trajectory law.
For two numerical trajectories approximating exact Hamiltonian curves with
shared initial momentum, initial potential gap `δ₀`, and respective numerical
energy errors `δ₁` and `δ₂`, Lean proves the explicit bound

```text
dTV ≤ exp(δ₁ + δ₀ + δ₂)² - 1.
```

This is the complete deterministic exact-reference reduction underlying
Proposition 4.2.

The remaining Proposition 4.2 obligation is a uniform leapfrog-versus-exact-
flow state or energy error over the fixed-integration-time regime; it is not
yet proved.

## 2026-08-12: aligned Gaussian recurrence and weighted coupling cost

Defined the exact two-scalar recurrence governing relative position and
momentum under standard-quadratic leapfrog. For every aligned step count,
Lean proves that both phase differences equal the corresponding scalar
coefficient times the initial position difference when momentum is shared.
The construction is extended to signed offsets, using `-ε` for inverse-time
steps, and each diagonal offset-trajectory cost is proved exactly equal to
the squared signed coefficient times the initial squared separation.

This exposed and repaired a loss in the generic maximal-coupling estimate.
The previous bound replaced every aligned cost by one maximum, which cannot
show strict contraction because the anchor index has coefficient one. The
finite transport layer now retains

```text
Σᵢ min(pᵢ,qᵢ) cost(i,i) + dTV(p,q) · mismatchBound.
```

The canonical maximal coupling has diagonal atom `min(pᵢ,qᵢ)`, and both the
maximal and optimal-transport trajectory couplings satisfy this refined
bound. The remaining Gaussian contraction task is to bound the resulting
finite weighted scalar-coefficient sum strictly below the initial cost under
the paper's trajectory-weight regime.

## 2026-08-12: measurable meeting tails and geometric closure

Added the measurable path event that exact meeting has failed at every time
through `n`, and proved it is exactly the strict tail event
`n < exactMeetingTime`. Its probability under an arbitrary path measure is
packaged as `exactMeetingTail`.

The final geometric induction is now machine checked: if these tail
probabilities satisfy `tail(n+1) ≤ r · tail(n)`, then `tail(n) ≤ rⁿ` for every
`n`. The theorem applies directly to probability path laws. What remains for
Theorem 4.1 is the substantive drift/small-set argument establishing such a
recurrence with `r < 1` for the coupled HMC/RWMH mixture; positivity of
one-step RWMH meeting alone is not a uniform recurrence.

## 2026-08-12: standard-Gaussian leapfrog energy specialization

Added the standard quadratic potential `U(q) = ‖q‖₂²/2` and identity gradient.
Lean derives exact coordinate formulas for a leapfrog step and an exact
polynomial identity for its Hamiltonian defect; every term has order at least
three in the step size. A reusable telescoping theorem expresses the energy
error of arbitrary `leapfrogN` iterates as the sum of their one-step errors,
and the Gaussian identity is lifted through that theorem.

The quadratic potential is now proved `C²`, its Fréchet derivative is certified
as Euclidean inner product with the identity gradient, and the gradient is
globally Lipschitz with constant one. It therefore instantiates the exact
`RegularPotential` interface used by the general theory.

The numerical bound is uniform as well. The exact defect polynomial is bounded
by an explicit scalar rate times squared phase size; the rate is at most
`|ε|³` for `|ε| ≤ 1`. Combining this with fixed-horizon phase stability gives

```text
|H(leapfrogN ε n z) - H(z)|
  ≤ T |ε|² (exp((13/4)T) phaseSize(z))²
```

whenever `n|ε| ≤ T`. Consequently, for an arbitrary varying step-count
function `n(ε)` satisfying that horizon bound eventually, Lean proves the
energy error tends to zero. This discharges the uniform numerical energy limit
for the standard Gaussian specialization; the corresponding general-potential
estimate remains open.

The bound is also connected to multinomial trajectory selection. For two
forward Gaussian leapfrog trajectories with shared initial momentum, Lean
proves that the total variation of their Boltzmann index laws is bounded by
`exp(r)² - 1`, where `r` is the initial potential gap plus the two explicit
uniform `O(|ε|²)` integration-error bounds. This is a direct validated
standard-Gaussian specialization of Proposition 4.2's deterministic content.

The standard quadratic gradient now also instantiates Assumption 2. Every
positive-radius ambient closed ball is proved compact, measurable, and of
positive Lebesgue volume; identity-gradient monotonicity supplies strong
convexity modulus one. Instantiating the generic shared-momentum leapfrog
theorems gives the explicit squared-distance factor

```text
1 - ε² + ε⁴/4,
```

and strict contraction for distinct positions whenever `ε ≠ 0` and `ε² < 4`.
This validates the one-step contraction ingredient on the Gaussian target;
the paper's aligned multi-index contraction and resulting full coupled-HMC
meeting theorem remain to be specialized.

## 2026-08-12: finite optimal transport and the trajectory `W₂` coupling

Represented a finite transport plan as an `ENNReal` joint mass function with
prescribed row and column sums. The feasible set is proved nonempty, closed,
and compact, and its finite nonnegative cost functional is continuous. Lean
therefore constructs an attained minimizer, packages it as a PMF, proves both
marginals exactly, and proves global minimality among all PMF couplings.

The generic theorem is specialized to the paper's equation (9), using squared
Euclidean distance between the positions at two selected leapfrog trajectory
indices. The resulting pointwise `W₂` coupling has the two Boltzmann index laws
as marginals and minimizes expected squared position distance. In particular,
its cost is proved no greater than that of the already formalized maximal
index coupling.

The optimizer currently uses classical choice. Its atoms have not yet been
proved measurable as the two phase points vary. The transport trajectory and
shared-momentum position HMC kernels are nevertheless packaged under this
explicit atom-measurability hypothesis; Lean proves they are Markov and that
both marginals are exactly the verified standard HMC kernel. A canonical
measurable finite-LP selector (or equivalent explicitly measurable
tie-breaking construction) remains the infrastructure obligation; pointwise
existence alone does not discharge it.

## 2026-08-12: analytic assumptions and explicit Euclidean geometry

Added explicit coordinatewise Euclidean inner product, norm, and squared norm
to the Hamiltonian foundation. This matters because the convenient raw type
`ι → ℝ` inherits mathlib's finite-product sup norm; relying on its ambient
`Norm` instance would state a norm-equivalent but quantitatively different
theorem. The trajectory `W₂` cost now uses the explicit squared Euclidean norm
required by equation (9).

Formalized Assumptions 1 and 2 of the paper. `RegularPotential` requires a
twice continuously differentiable potential, certifies the supplied leapfrog
gradient through the Fréchet derivative in Euclidean coordinates, and states
the exact global Euclidean Lipschitz bound with positive constant.
`LocalStrongConvexity` records a compact measurable positive-volume region and
the paper's strong gradient-monotonicity inequality with positive modulus.
The basic lower bound and strict positivity for distinct points are proved.
Exact-flow contraction and leapfrog error transfer remain to be established.

## 2026-08-12: pointwise exact-flow contraction calculus

Defined coordinatewise classical solutions of the unit-mass Hamilton
equations `q' = p` and `p' = -∇U(q)`. Proved a finite-dimensional product rule
for the explicit Euclidean pairing, the first-derivative formula for squared
position separation, and the derivative formula for the
displacement/relative-momentum pairing.

For two exact curves with shared momentum at a given time, Lean proves that
squared position separation has zero first derivative. If the two positions
are distinct and lie in the locally strongly convex region, the derivative of
that first-variation expression is strictly negative. This is the pointwise
negative second-variation core of Lemma 4.2. A uniform Taylor-remainder
argument over compact initial data is still needed to obtain the paper's
single positive contraction horizon.

The pointwise consequence is now complete as well. The derivative test shows
that the first variation is strictly negative immediately to the right of the
shared-momentum time. A mean-value/strict-antitonicity argument then produces
a positive interval on which every nonzero time strictly decreases squared
Euclidean position separation. The interval still depends on the initial
pair; extracting one horizon and one contraction factor uniformly over a
compact family is the remaining Lemma 4.2 obligation.

## 2026-08-12: quantitative one-step leapfrog contraction

Proved the exact position-difference identity for one leapfrog step started
from two positions with a shared momentum. Expanding the explicit squared
Euclidean norm and applying the paper's strong-monotonicity and gradient-
Lipschitz assumptions yields

```text
‖q₁' - q₂'‖₂² ≤ (1 - α ε² + β² ε⁴ / 4) ‖q₁ - q₂‖₂².
```

Lean further proves that the factor is strictly below one whenever `ε ≠ 0`
and `β² ε² < 4α`, hence the step strictly contracts any distinct pair in the
strong-convexity region. This is a quantitative discrete ingredient for
Proposition C.1; iterated leapfrog trajectories require control of the
changing momenta, exits from the region, and accumulated numerical error.

Added exact relative-state recurrences for arbitrary (not necessarily shared)
momenta. These are lifted to every successor index of two aligned `leapfrogN`
trajectories. The position recurrence contains current relative position,
relative momentum, and the current gradient difference; the momentum
recurrence contains gradient differences at both consecutive positions. They
form the algebraic input for the pending multi-step stability/Gronwall bound.

Proved coarse Euclidean three-term inequalities and applied global gradient
Lipschitzness to both recurrences. At every aligned index, Lean now bounds the
next squared relative position by the current squared position and momentum,
and bounds the next squared relative momentum by current momentum plus the
position separations at both ends of the step. These bounds are deliberately
valid without assuming the trajectories remain in the strong-convexity set.
A discrete Grönwall argument must now close the coupled inequalities and
sharpen them enough for the finite integration horizon used in Proposition
C.1.

The coupled inequalities are now closed into a single phase-separation bound.
An explicit nonnegative stability factor controls one step, and induction
proves that aligned phase separation after `n` steps is at most its `n`th
power times the initial separation. This is a genuine discrete Grönwall
closure. It is intentionally conservative: the use of a uniform three-term
square bound leaves a factor bounded away from one as `ε → 0`, so it cannot
yet support `n ≍ T/ε`. A weighted Young-inequality refinement with factor
`1 + O(|ε|)` remains necessary for Proposition C.1.

That refinement is now proved. Coordinatewise Cauchy--Schwarz establishes the
triangle inequality and homogeneity for the explicit Euclidean norm. Applying
these to the exact relative-state recurrences gives the one-step phase bound

```text
E₁ ≤ (1 + (1 + 2β + β²/4)|ε|) E₀        when |ε| ≤ 1,
```

where `E` is the sum of relative position and momentum norms. Induction gives
the corresponding `n`th-power bound for aligned trajectories. Unlike the
earlier coarse squared estimate, this has the correct `1 + O(|ε|)` scaling for
`n|ε|` bounded. The power bound is now converted to the fixed-horizon estimate

```text
Eₙ ≤ exp((1 + 2β + β²/4) T) E₀       when n|ε| ≤ T.
```

Combining this stability estimate with local strong convexity and a
leapfrog-versus-exact-flow error estimate remains. The geometric transfer
step is now isolated and proved: if two numerical positions are within errors
`δ₁, δ₂` of reference positions whose separation is at most `ρ` times the
initial separation, their separation is at most `ρ` times the initial
separation plus `δ₁ + δ₂`. Thus the remaining obligation is the analytic
uniform error estimate, not a hidden metric argument.

## 2026-08-12: categorical coupling lifted to HMC trajectories

Added a measurable kernel that shares the uniformly sampled trajectory origin
and accepts any input-dependent joint PMF for the two selected trajectory
indices. Its assumptions state pointwise categorical marginal correctness and
measurability of every joint atom. Lean proves the resulting phase-pair kernel
is Markov and that both marginals are exactly the previously verified
single-chain randomized multinomial trajectory kernel.

The lifting is independent of the categorical coupling algorithm, so maximal
and transport constructions can share the same marginal proof. A
conditionally independent index coupling is instantiated and proved
measurable as a compiled validation.

The kernel coupling calculus now also proves that coordinate-wise output maps
preserve marginal correctness. Using it, arbitrary coupled refresh and coupled
trajectory transitions compose into a coupled phase HMC kernel, and paired
position-to-phase lifts compose and project into a coupled position HMC
kernel. Independent Gaussian refresh/lift specializations are proved Markov;
both their phase and position marginals are exactly the verified standard
single-chain multinomial HMC kernels. At that point the paper-specific
momentum and maximal/transport categorical choices remained uninstantiated.

## 2026-08-12: quantitative finite total-variation bounds

Added the discrete analytic interface required by Proposition 4.2. For finite
PMFs, total variation is now bounded by the sum of any pointwise additive
upper bounds on the positive mass differences. A uniform error therefore
gives the category-count bound. More importantly for multinomial HMC, if
`p(i) ≤ c q(i)` for every category and `c ≥ 1`, Lean proves the
dimension-free estimate

```text
dTV(p, q) ≤ c - 1.
```

The trajectory-specific normalization step is now proved as well. If the
Hamiltonian values at corresponding trajectory indices differ by at most
`r ≥ 0`, each normalized multinomial probability is at most `exp(r)²` times
its counterpart. One factor comes from the atom's Boltzmann weight and the
second from the ratio of the two normalizers. Consequently Lean proves

```text
dTV(P_trajectory₁, P_trajectory₂) ≤ exp(r)² - 1.
```

Completing Proposition 4.2 now requires the analytic input showing that the
relevant aligned trajectory energies have a uniform discrepancy tending to
zero with the leapfrog step size.

The energy discrepancy itself is now reduced to explicit phase-space error
data. Lean proves the polarization identity for quadratic kinetic energy and
the bound

```text
|K(p₁)-K(p₂)| ≤ 1/2 · ‖p₁-p₂‖₂ · (‖p₁‖₂+‖p₂‖₂).
```

Combining this with a potential-value discrepancy gives a Hamiltonian bound.
At trajectory level, uniform potential error `δq`, momentum error `δp`, and
momentum-size bound `P` now imply the explicit total-variation estimate with
energy radius `δq + (1/2)δpP`. The remaining work is to derive these three
uniform bounds from the regularity assumptions and leapfrog approximation.

Regularity now supplies the potential part uniformly on compact sets. From
`ContDiff ℝ 2`, Lean derives continuity and then uniform continuity on every
compact region. This is packaged with the phase-error theorem in a public
analytic module: for every positive potential tolerance there is one position
radius that works simultaneously for all finite paired trajectories contained
in the compact set, with arbitrary trajectory length. Momentum error and size
remain explicit in the resulting TV estimate.

The compactness interface is now aligned with the rest of the analytic layer:
each coordinate difference is bounded by the explicit Euclidean norm, hence
Euclidean separation bounds the ambient finite-product metric. The uniform
potential-error radius and trajectory TV theorem therefore consume
`euclideanNorm (q₁-q₂)` directly, with no hidden switch of geometry.

The limiting step of the discrete argument is also machine checked. Lean
proves that the explicit ENNReal bound `exp(r)² - 1` tends to zero as `r → 0`.
For an arbitrary filter-indexed family of paired finite trajectories, if the
uniform Hamiltonian discrepancy tends to zero, then the corresponding
multinomial index PMFs converge in total variation. This is the normalization
and convergence mechanism of Proposition 4.2; proving the required leapfrog
energy-error limit remains the paper-specific analytic obligation.

The finite maximal-coupling cost decomposition needed by Lemma 4.3 is now
proved. For any finite joint PMF, diagonal mass plus unequal-pair mass is one;
for a maximal coupling, the unequal-pair mass is exactly total variation. If
the cost is at most `A` on aligned indices and at most `D` off diagonal, its
expectation under the maximal coupling is therefore bounded by

```text
A + dTV(p,q) · D.
```

This theorem is instantiated for the actual squared-position cost of the
maximal multinomial trajectory-index coupling. Analytic aligned contraction,
a uniform off-diagonal trajectory bound, and the established TV limit are the
remaining inputs to obtain the full local-contractivity statement.

The off-diagonal bound is now discharged from a standard bounded-trajectory
hypothesis. If every position in both trajectories has Euclidean norm at most
`R`, every cross-index squared distance is at most `4R²`. Consequently both
the maximal and optimal-transport trajectory couplings satisfy

```text
expected squared cost ≤ aligned bound + 4R² · dTV.
```

The transport result follows from its already-proved global optimality, so no
separate coupling argument is assumed. Uniform boundedness of the leapfrog
trajectories and the aligned contraction estimate are the remaining geometric
inputs.

Compact containment now discharges the boundedness input. The explicit
Euclidean norm and squared norm are proved continuous in the finite-product
topology, so every compact position region is contained in some positive
Euclidean ball. If both finite leapfrog trajectories remain in that compact
region, Lean produces one radius `R` and proves the `4R²` cost bound for every
pair of trajectory indices. What remains is to prove the required trajectory
containment and aligned contraction uniformly over the paper's step-size
regime.

Fixed-parameter containment is now derived rather than assumed. The explicit
gradient Lipschitz condition implies ordinary Lipschitz continuity in
mathlib's finite-product metric (with an explicit dimension factor), hence the
gradient is continuous. Leapfrog, its finite iterates, signed iterates, and
every offset-trajectory coordinate are therefore continuous. For fixed step
size, trajectory length, and origin, the union of all positions reachable
from a compact initial phase set is compact and has one uniform Euclidean
radius. The remaining containment problem is uniformity while step size and
trajectory length vary together at fixed integration time.

Absolute stability is now proved uniformly at fixed integration time. The
global gradient Lipschitz condition gives the affine growth bound
`‖∇U(q)‖₂ ≤ β‖q‖₂ + ‖∇U(0)‖₂`. Lean computes the image of the zero phase point
under leapfrog and bounds its phase size by
`(2+β)|ε|‖∇U(0)‖₂`. Combining this forcing term with sharp relative stability
gives an affine discrete Grönwall theorem and

```text
phaseSize(leapfrogN ε n z)
  ≤ exp(Cβ T) · (phaseSize(z) + (2+β)T‖∇U(0)‖₂)
```

whenever `|ε| ≤ 1` and `n|ε| ≤ T`. The bound is independent of the step
count. Extending it through the signed-iterate representation used by offset
trajectories is now complete. Negative indices are handled as positive
iterations with step `-ε`, and every offset index has signed distance at most
`L` from the origin. Compact initial phase data supplies a uniform initial
phase-size bound, so Lean obtains one radius that works simultaneously for all
step sizes, lengths, origins, indices, and initial states satisfying
`|ε| ≤ 1` and `L|ε| ≤ T`. The corresponding `4R²` cross-index cost bound is
therefore uniform over the full fixed-integration-time regime. Aligned
contraction and the leapfrog energy-error limit remain.

The common-random-number momentum choice is now instantiated as well. A
diagonal momentum measure copies one draw into both coordinates; Lean proves
both of its marginals equal the requested momentum law. Reassociation with the
two retained positions produces a Markov coupled momentum lift with exact
single-chain lift marginals. Composing this lift with the coupled trajectory
transition gives a complete shared-standard-Gaussian position HMC coupling,
again with the verified standard HMC kernel on both marginals. Reflection
momentum and maximal/transport index selection remain.

## 2026-08-12: measurable maximal coupled multinomial HMC

Derived a branch-free atom formula for the finite maximal coupling: each joint
atom is a diagonal common-mass term plus a normalized product of the two
residual masses. This formula is proved equivalent to the existing case-based
construction, including full-overlap and zero-overlap edge cases. It implies
that every maximal-coupling atom varies measurably whenever the two marginal
PMF atom families do.

The two trajectory-index PMFs now instantiate this theorem. Their maximal
coupling is proved measurable and maximal, is lifted to a Markov phase-pair
trajectory kernel, and has the verified randomized trajectory kernel on both
marginals. Composing it with the shared standard-Gaussian momentum lift gives
a complete paper-style position HMC coupling. Lean proves it is Markov and
that both marginals are exactly the verified standard position-space
multinomial HMC kernel. Transport-based selection now exists pointwise with a
proved optimality theorem, but its measurable parameterized selection remains
unproved.

## 2026-08-12: complete single-chain multinomial HMC

Factored the unnormalized phase Boltzmann measure exactly into position and
quadratic-kinetic Boltzmann measures. Lean also proves directly from mathlib's
Gaussian density formula that standard product Gaussian momentum is the
finite-dimensional scalar normalization of the kinetic factor.

Momentum refresh is now parameterized by an arbitrary probability momentum
law and proved to preserve its product with any s-finite position measure. It
is composed with the invariant randomized trajectory kernel to define a full
phase-space multinomial HMC transition. A position-space kernel samples fresh
momentum, performs the trajectory transition, and discards momentum. Both are
proved Markov. For standard Gaussian momentum, the phase kernel preserves the
extended Boltzmann target and the projected kernel preserves the unnormalized
position measure `exp (-U(q)) dq`. No normalizability of the position target is
needed for this invariance statement.

## 2026-08-12: multinomial trajectory selection

Added the probability layer that selects a phase point from a finite nonempty
trajectory with weight proportional to `exp (-H)`. Lean proves every
Boltzmann weight is nonzero and finite, the finite normalizer is nonzero and
finite, the normalized law is a PMF, and every trajectory index has nonzero
probability.

For a measurably input-dependent trajectory, the index law and its pushforward
to the selected phase point are packaged as measurable Markov kernels. The
construction is instantiated with the first `L + 1` states of a forward
leapfrog trajectory. This is a proved trajectory-selection component, not yet
the complete multinomial HMC kernel: target invariance requires momentum
refresh and an invariance-preserving randomized forward/backward trajectory
construction, together with the relevant volume/reversibility arguments.

## 2026-08-12: Gaussian momentum refresh

Defined standard finite-dimensional Gaussian momentum using the already
normalized product Gaussian density and proved it is a probability measure.
For any probability position target, its product with this momentum law is a
probability extended target with the expected position and momentum
marginals.

The momentum-refresh transition is constructed as the parallel composition of
the identity position kernel and the constant Gaussian momentum kernel. Lean
proves it is Markov, identifies each row as `δ_q × Gaussian`, proves both row
marginals exactly, and proves that it preserves every such product extended
target. This closes the refresh prerequisite but does not prove invariance of
the subsequent leapfrog/multinomial trajectory transition.

## 2026-08-12: forward/backward trajectory re-rooting

Packaged one leapfrog step as a permutation whose inverse is the negative
step, and defined signed leapfrog iteration using integer powers. Lean proves
signed iteration is measurable for every integer exponent.

The randomized-origin trajectory places the current state at any index in
`Fin (L + 1)` and reaches every other index by the corresponding signed number
of steps. Its origin evaluates exactly to the current state. Most importantly,
Lean proves the re-rooting identity: selecting any indexed point and rebuilding
the trajectory with that point at its own index recovers every original
indexed point. This is the orbit symmetry required by the later
multinomial-HMC balance proof; uniform origin sampling and target invariance
are not yet included.

## 2026-08-12: randomized multinomial leapfrog kernel

Combined the forward/backward trajectory with uniform origin selection and
conditional Boltzmann index selection. The joint origin/selected-index law and
the resulting phase-space output law are represented as finite mathlib PMFs.
The same transition is packaged directly as a measurable kernel by averaging
the fixed-origin selection kernels.

Lean proves every fixed-origin and randomized transition is Markov, exposes
the exact two-stage finite-sum row formula, and proves that every measure-kernel
row equals the measure associated with the finite PMF sampling program. This
establishes algorithmic semantics and normalization, but not target
invariance. At this milestone the missing input was leapfrog volume
preservation; the following milestone discharges it, leaving the balance
argument itself.

## 2026-08-12: leapfrog volume preservation

Defined product Lebesgue measure on phase space and expressed leapfrog as an
exact kick--drift--kick composition. The momentum kick is a measurable
translation in each fixed-position fiber; the position drift is the analogous
translation after swapping product coordinates. Mathlib's Haar translation
and skew-product theorems prove that both maps preserve product Lebesgue
measure.

Lean consequently proves volume preservation for one leapfrog step, every
finite iterate, every signed integer iterate, and every coordinate of every
offset forward/backward trajectory. The product phase volume is also proved
equal to the standard product-type `volume`. No Jacobian or differentiability
hypothesis is needed for this result. Differentiability remains necessary for
state and energy approximation-error bounds, while the immediate invariance
proof now has both of its structural inputs: volume preservation and exact
trajectory re-rooting.

## 2026-08-12: multinomial trajectory detailed balance and invariance

Defined the phase-space Boltzmann measure and the target-weighted flow for each
ordered origin/selected-index pair. Lean proves these flows are measurable,
that re-rooting preserves every trajectory weight and its normalizer, and that
the weighted forward selection probability equals the reverse probability
after re-rooting.

For each ordered pair, volume-preserving change of variables by the
corresponding signed leapfrog map swaps the initial/final events and turns the
forward flow integral into its reverse. The randomized kernel is proved equal
to the uniform finite sum of these component subkernels. Summing paired
component balance over both indices and transposing the finite sums proves
mathlib `Kernel.IsReversible`; its generic theorem then gives `Kernel.Invariant`
for the phase-space Boltzmann measure.

This is the trajectory-level balance theorem used by the later complete HMC
packaging. Normalization of a general potential's Boltzmann target is not
asserted; invariance is proved for the unnormalized measure.

## 2026-08-12: Hamiltonian and leapfrog foundation

Added finite-dimensional Euclidean position, momentum, and phase-space types,
unit-mass quadratic kinetic energy, Hamiltonian energy, and momentum reversal.
Defined the standard half-kick/drift/half-kick leapfrog map, arbitrary finite
iterates, and the resulting integer-indexed trajectory.

Lean proves measurability of momentum reversal, energy for measurable
potentials, leapfrog for measurable gradients, every finite iterate, and the
trajectory coordinates. It also proves momentum reversal is involutive, the
exact conjugacy `flip ∘ leapfrog(ε) ∘ flip = leapfrog(-ε)`, that a
negative-size step is the inverse of a positive-size step, and the analogous
identity for every finite iterate.

This is the deterministic algebraic foundation, not yet HMC invariance.
At this milestone volume preservation, the relationship between the supplied
gradient and an actual potential derivative, state and energy discretization-
error bounds, momentum refresh, and the invariant full HMC transition were
unproved. Volume preservation and momentum refresh have since been completed.

## 2026-08-12: shared-uniform coupled MH foundation

Added the measure-level shared-uniform accept/reject construction used by
coupled RWMH. For left and right acceptance probabilities `a` and `b`, the
four branch weights are `min a b`, `a - min a b`, `b - min a b`, and
`1 - max a b`. Lean proves that these weights partition one and that their
left/right accepting and rejecting sums recover `a`, `b`, `1-a`, and `1-b`.

Applying the four branches to any probability coupling of proposals now gives
a proved probability measure on the pair of next states. Both coordinate
marginals are now proved equal to the existing single-chain
`metropolisHastings` transition rows, using only the corresponding proposal
marginals. The construction is now lifted to a measurable kernel using an
input-dependent pushforward combinator. Lean proves that it is a Markov kernel
and that a coupled proposal kernel yields exactly the ordinary MH kernel on
both coordinates. A conditionally independent proposal specialization is also
proved correct; it validates the API but is not an exact-meeting construction
for continuous proposals. The maximal Gaussian proposal coupling needed for
positive exact-meeting probability remains to be constructed.

Connected this kernel directly to the meeting-time layer. The accepted mass
of coupled proposals already on `Set.diagonal` is proved to lower-bound the
one-step exact-meeting probability. More quantitatively, if simultaneous
acceptance is bounded below by `ε` on the diagonal, the transition's meeting
mass is at least `ε` times the proposal coupling's diagonal mass. A separate
corollary shows positivity from positive diagonal proposal mass and pointwise
positive simultaneous acceptance. Thus the future maximal-Gaussian theorem
has a precise interface: supply diagonal proposal mass, then verify acceptance
on that diagonal.

## 2026-08-12: continuous density and Gaussian proposal coupling

Added the general density-overlap decomposition for two normalized densities
against a common s-finite reference measure. The common density is their
pointwise minimum; Lean proves its mass is at most one, each residual measure
has mass exactly one minus the overlap, and common plus residual reconstructs
the corresponding original density measure.

Constructed the standard continuous coupling by mapping the common measure to
the diagonal and adding a correctly scaled independent product of the two
residual measures. The result is proved to be a probability measure with
exactly the requested two density-measure marginals. Its diagonal mass is
proved to be at least the common-density overlap. The sharper statement that
the residual product contributes zero diagonal mass, and hence equality with
the overlap, remains unproved.

Specialized the construction to every pair of one-dimensional nondegenerate
Gaussian random-walk proposal rows. Their density overlap is proved strictly
positive, so the coupled proposal has positive exact-agreement probability,
and its marginals are identified directly with the proposal kernel used by
the existing Gaussian RWMH definition.

Proved joint measurability in both current states by separately constructing
the common diagonal subkernel, the two residual density kernels, their
conditionally independent product, and the measurable reciprocal-overlap
scaling. Their sum is a Markov proposal coupling kernel whose rows equal the
measure-level construction. Feeding it into the shared-uniform accept/reject
kernel produces an end-to-end coupled Gaussian RWMH Markov kernel. Both
marginals are exactly the previously verified single-chain Gaussian RWMH
kernel. If the target density is everywhere positive and finite, every pair
of current states has strictly positive probability of exact meeting in one
step. This is a kernel-validity and meeting-accessibility result, not yet a
uniform minorization or geometric meeting-time theorem.

## 2026-08-12: general Metropolis--Hastings completion

Added the mathlib-native general-state Metropolis--Hastings completion. A
measurable acceptance function defines an accepted proposal kernel by
`Kernel.withDensity`; its missing mass is put at the current state by a
density-weighted identity kernel. Acceptance bounded by one is proved to make
the sum a Markov kernel. The rejection part is proved reversible for every
measure, so reversibility of the accepted flow implies reversibility and
target invariance of the completed transition.

For density-based MH, defined the zero-safe acceptance probability through the
symmetric flow `min (w(x) q(x,y)) (w(y) q(y,x))`. It is measurable, bounded by
one, invariant under swapping the accepted flow, and multiplying it by a
finite forward density recovers that flow exactly, including zero forward
mass. Target measures and proposal kernels are constructed from densities
against a common s-finite reference measure and proved normalized from their
integral hypotheses. Expanding both with-density layers and applying Tonelli
identifies the accepted flow in both directions with the symmetric minimum.
Consequently the complete density-based MH transition is proved Markov,
reversible, and target-invariant.

Specialized this construction to additive random walks. For an increment
density `noise`, the proposal density is `q(x,y) = noise (y-x)`. Translation
invariance proves every proposal row normalized from normalization of `noise`,
and an even increment density is proved to give a symmetric proposal. The
resulting RWMH kernel is proved Markov, reversible, and target-invariant. As a
validated non-discrete instance, centered Gaussian increments of arbitrary
nonzero variance on `ℝ` use mathlib's Gaussian density normalization and yield
a proved RWMH transition for every measurable pointwise-finite target density.

Extended the Gaussian instance to every finite-dimensional coordinate space
`ι → ℝ`. The isotropic increment density is the finite product of centered
one-dimensional Gaussian densities. Its measurability, normalization,
evenness, and pointwise finiteness are all proved; normalization uses mathlib's
finite-product Fubini theorem. The resulting Euclidean Gaussian RWMH kernel is
proved Markov, reversible, and target-invariant.

## 2026-08-12: general coupling foundation

Added a mathlib-native coupling interface for measures and Markov kernels.
Couplings are specified by exact first and second marginals. The module proves
the projection identities, normalization inherited from a probability
marginal, coordinate-swap correctness, and that the independent product of
two Markov kernels is a coupling. No parallel probability or kernel type is
introduced.

Added normalized convex mixtures of kernels, proved that a mixture of Markov
kernels is Markov, and proved that mixing two coupled kernels produces a
coupling of the corresponding marginal mixtures. This is the abstract
operation eventually used to combine the separately verified coupled HMC and
coupled RWMH transitions.

Proved linearity of measure evolution through these mixtures and used it to
show that a mixture of two kernels preserving the same target also preserves
that target. Combined this with marginal correctness into the precise
structural theorem required by the paper's eventual coupled HMC/RWMH mixture.
The theorem does not assume either component is correct: their invariant and
coupling proofs remain explicit premises that the RWMH and HMC developments
must discharge.

Proved closure under sequential composition and, by induction, under every
finite kernel power. Thus an iterated coupled transition has exactly the
iterated left and right marginal kernels; no independence assumption is used.
Applying a coupled transition to a coupled initial measure is also proved to
produce a coupling of the two evolved marginal measures.

Added exact and lag-one meeting events for paired paths. Fixed-time events are
proved measurable under mathlib's explicit `MeasurableEq` assumption. Their
first meeting times reuse mathlib's `hittingAfter`, take values in
`WithTop ℕ`, and are characterized by existence of a meeting within the
corresponding finite time interval. The lag-one time is proved to be at least
one. Stopping-time results relative to the eventual coupled path filtration
remain to be instantiated.

Added finite-time laws `P^n ∘ₘ μ`, their zero/successor identities, Markov
and probability instances for kernel powers and evolved laws, and the theorem
that the time-`n` law of a coupled chain couples the two time-`n` marginal
laws. Added a homogeneous adapter for mathlib's history-dependent
Ionescu--Tulcea interface and used it to construct a Markov path kernel on
`ℕ → State`. The time-one coordinate is proved to equal the original
transition kernel, and after integrating an initial distribution it equals
the usual one-step evolved law. Identifying every time-`n` coordinate with
the corresponding kernel power remains the next proof obligation; the
terminal-history projection needed for that induction is now isolated.

Added a PMF-native finite categorical coupling interface and proved that its
marginal equations imply the general `Measure` coupling predicate. Defined
common mass, finite total variation as one minus common mass, and maximality
as diagonal mass equal to common mass; this yields the standard diagonal
probability `1 - dTV`. For coincident marginals, the diagonal PMF is proved to
be a maximal coupling. For arbitrary unequal marginals, the standard
construction is now complete: the common and residual masses are normalized,
the two residual PMFs are proved to have disjoint support, and their independent
product is mixed with the diagonal common part. The resulting PMF has exactly
the requested marginals and diagonal mass equal to the overlap. Zero- and
full-overlap cases are handled explicitly.

## 2026-08-12: coupled multinomial HMC research target

The project goal is now to formalize the main theoretical results of Xu,
Fjelde, Sutton, and Ge, “Couplings for Multinomial Hamiltonian Monte Carlo”
(AISTATS 2021). The roadmap has been reorganized around the paper's actual
dependency chain: coupled measure kernels, meeting-time theory, Hamiltonian and
leapfrog foundations, multinomial HMC, categorical maximal and transport
couplings, local contractivity, and geometric meeting tails.

The target includes Lean counterparts of the paper's Lemmas 4.1--4.4,
Propositions 4.1--4.2, and Theorem 4.1, together with the assumptions imported
from Heng and Jacob (2019). Experimental performance comparisons are not
machine-checked theorem claims.

## 2026-08-12: general detailed-balance foundation

The first mathlib-native general-state module now defines the joint transition
law `π(dx) P(x,dy)` as mathlib's measure--kernel composition product. It proves
that:

- the joint law evaluates on measurable rectangles as the expected iterated
  integral;
- a Markov transition from a probability target has a probability joint law;
- mathlib's `Kernel.IsReversible` predicate is equivalent to invariance of the
  joint law under coordinate swap; and
- symmetry of the joint law therefore implies `Kernel.Invariant` for the
  target.

This module depends only on mathlib's measure and kernel APIs, not on the local
finite definitions. It establishes the representation needed by both the
density-based and Radon--Nikodym MH constructions; accepted flow and rejection
remain to be defined.

## 2026-08-12: kernel-first roadmap revision

The roadmap now prioritizes a mathlib-native general-state MH theorem before
additional finite dynamics or convergence infrastructure. New reusable theory
will use `Measure` and `ProbabilityTheory.Kernel` directly; `PMF` remains the
frontend for finite or countable probabilistic programs.

The completed elementary finite development is retained temporarily as a
verified baseline and regression oracle. It should not grow into a parallel
kernel theory. After density-based and Radon--Nikodym MH correctness are
available, the finite results will be recovered as specializations. The local
finite types can leave the public API only after replacements cover the
current detailed-balance, stationarity, acceptance-ratio, edge-case, matrix,
PMF-bind, and example results.

## 2026-08-11: one-step finite dynamics

The finite layer now describes how an arbitrary initial distribution changes
after one Markov transition. This milestone added:

- a normalized one-step evolution operation on finite distributions;
- identification of evolution with row-vector/matrix multiplication;
- identification of the evolved PMF with monadic bind by the transition-row
  PMFs;
- the equivalence between local stationarity and being a fixed point of
  one-step evolution; and
- a concrete theorem that one step of the two-state MH kernel leaves its
  target unchanged.

This is a one-step result. Kernel powers, multi-step laws, reachability, and
convergence remain unproved.

## 2026-08-11: finite stochastic-matrix interoperability

The elementary `MarkovKernel` is now equivalent to mathlib's subtype of real
row-stochastic matrices. This milestone added:

- the transition-matrix view and its row-stochasticity proof;
- conversions in both directions and an equivalence theorem;
- the characterization of local stationarity as the row-vector equation
  `pi * P = pi`;
- agreement between matrix entries and measure-kernel singleton transition
  probabilities; and
- a two-state MH instantiation of the row-stochastic matrix result.

Together with the preceding PMF, measure, and kernel bridge, this completes
the first roadmap phase. Matrix-based dynamics should now reuse mathlib rather
than grow into a parallel local theory.

## 2026-08-11: finite measure-kernel interoperability

The finite elementary interface now embeds into mathlib's measure-theoretic
probability APIs. This milestone added:

- conversion of a local finite `Distribution` to a mathlib `PMF` and
  probability `Measure`;
- conversion of every transition row to a `PMF`;
- conversion of a local `MarkovKernel` to a
  `ProbabilityTheory.Kernel`, with an `IsMarkovKernel` instance;
- singleton and finite-set evaluation lemmas connecting the embedded objects
  to their original real-valued masses and probabilities;
- a finite double-sum proof that local pointwise detailed balance implies
  mathlib's setwise `Kernel.IsReversible` predicate;
- invariance of the embedded target via mathlib's generic theorem that
  reversibility implies invariance; and
- a two-state MH instantiation of the measure-kernel invariance result.

This bridge does not add a convergence theorem. It makes mathlib's kernel
composition, powers, irreducibility, and trajectory infrastructure available
to subsequent phases.

## 2026-08-11: finite-state Metropolis--Hastings stationarity

The initial development added:

- a small finite-state interface for normalized distributions and
  row-stochastic Markov kernels;
- definitions of reversibility and stationarity;
- the finite theorem that detailed balance implies stationarity;
- the MH accepted flow, acceptance probability, move probability, rejection
  mass, and transition kernel;
- proofs that move, rejection, and transition probabilities are nonnegative;
- a proof that every transition row sums to one;
- equivalence between the usual MH acceptance ratio and the symmetric-flow
  construction;
- detailed balance and target stationarity for the resulting kernel; and
- a concrete two-state example with target masses `3/4` and `1/4`.

The symmetric-flow construction is

```text
min (π(x) * q(x,y)) (π(y) * q(y,x)).
```

It makes detailed balance direct and handles zero forward or reverse proposal
probabilities without extra cases in the kernel definition.

### Current limitations

- The state space is finite.
- The target mass is assumed strictly positive at every state.
- At this milestone the local finite kernel had not yet been embedded into
  mathlib; that limitation has since been removed by the interoperability
  modules.
- The result proves stationarity, not convergence from arbitrary starting
  states. No irreducibility or aperiodicity theorem has been added yet.

Supporting repository work in this milestone included the initial Lake
project, a related-work survey, and coding-agent workflow instructions.
