# Overall project roadmap

This roadmap integrates the two paper targets, executable sampler work, and
the broader [algorithm scope review](algorithm-scope-review.md). It is the
canonical ordering document; paper-specific roadmaps continue to record exact
claim repairs and theorem dependencies.

## Current position

The repository is already deep in three areas:

1. general-state MH, HMC, coupling, meeting-time, and unbiased-estimator
   mathematics;
2. corrected theorem coverage for Xu et al. (2021) and Xu and Ge (2024); and
3. generated executable finite MH, RWMH, endpoint HMC, unit/constant-metric
   multinomial HMC, and the Xu et al. coupled mixture, with explicit
   numerical-refinement boundaries.

The reusable surface combines mathlib composition with local invariant
mixtures, product/lift/project machinery, coupling marginals, finite/infinite
path semantics, and the completed elementary finite combinators.

## Track A: reusable sampler foundations

### A1. Consolidate kernel combinators and add finite Gibbs — complete

- inventoried and publicly re-exported composition, mixture, product,
  mapping, and stationary-marginal theorems;
- added the missing coordinate-lift and deterministic/random scan lemmas;
- defined finite product-state conditional laws, one-site/block Gibbs kernels,
  random scans, and systematic scans; and
- proved target invariance, while keeping irreducibility and convergence as
  separate optional theorems.

This supplies shared language for tempering, adaptation, particle methods,
and coupled multi-kernel algorithms.

### A2. Parallel tempering — complete for two finite temperatures

Coordinate-lifted invariant kernels and an ordinary MH transposition preserve
the two-temperature product target; its cold marginal is identified exactly.
No improved-mixing claim is made.

### A3. Finite pseudo-marginal MH — complete

A nonnegative unbiased estimator on a finite auxiliary space defines the
normalized extended target and an MH transition retaining the current
estimator on rejection. The desired marginal is proved, including zero
estimator values. MCWM remains explicitly separate.

### A4. First general-state convergence and proposal clients -- complete

The bounded-weight independence-MH `1 / M` minorization and exact residual
decomposition are machine checked. The residual preserves the target, every
finite-time law has an exact refresh-plus-residual representation, and the two
eventwise discrepancies from stationarity are bounded by `(1 - 1 / M)^n` for
`M > 1`. The `M = 1` exact-proposal boundary is intentionally separate.

The state-dependent Gaussian proposal is complete. ULA is a Markov kernel
with no target-exactness claim; its MH completion, MALA, is proved Markov,
reversible, and target-invariant. Roberts--Tweedie tail conditions and
geometric-ergodicity results remain a later convergence layer.

## Track B: paper-target execution

### B1. Executable Xu et al. (2021) coupling — complete

Version-9 shared-randomness commands cover coupled multinomial HMC, sticky
Gaussian RWMH, and their mixture. Lean proves both ideal marginals equal the
verified single-chain kernels, and Julia exposes replay-level meeting events.

### B2. Executable Xu and Ge (2024) sampler — complete at the exact and guarded-runtime levels

IR version 10 now contains a working corrected diagonal constant-metric
relativistic multinomial specialization, with Reference/Optimized Julia replay
tests. A position-dependent fixed-point solver now exists in Reference and
Optimized Julia with residual reporting, while Lean constructs its exact
Banach-fixed-point counterpart and proves uniqueness and convergence of the
finite loops. Lean now also has a fixed-step interface and a concrete
smooth momentum-even nonseparable instance: both implicit maps contract under
the explicit condition `|εa/2| < 1`, giving a measurable exact unique solve,
convergent finite loops, and momentum-flip reversal. The bilinear stress model
closes phase volume unconditionally in every finite dimension.

The bounded scalar client `2 + sin(q)` closes the actual-derivative solver:
for `3|ε|/2 < 1` Lean constructs the exact unique solver and proves finite-loop
convergence, measurability, reversal, differentiability, exact unit Jacobian,
and product-phase-volume preservation. Float64 loops retain measured residuals
and are not identified with the exact fixed point.

The mixed-partial and scalar determinant-cancellation portions of that
certificate are now machine checked. A reusable theorem proves continuity of
the fixed point of a jointly continuous uniformly contractive family, and the
bounded scalar client instantiates it for both implicit solves and the full
step. Four explicit triangular maps and three checked identities now expose
the solver as the incoming inverse, right/left position transfer, and outgoing
map used by the paper's Jacobian calculation. Both inverse selections are now
proved differentiable and the final derivative composition is closed.

The generic inverse-function wrapper needed for that upgrade is now proved:
an everywhere-nonsingular differentiable finite-dimensional map with a
continuous global left inverse has a differentiable inverse selection. The
bounded client also exposes scalar-coordinate callback maps on `ℝ × ℝ`; the
incoming derivative calculation and its transport across the `Unit → ℝ`
phase-space equivalence are now discharged.

The incoming half-momentum stage is complete. Its scalar-coordinate
Fréchet derivative is represented by an explicit `2×2` triangular matrix;
Lean proves the matrix is the actual derivative, computes its determinant,
identifies the diagonal entry with the one-variable derivative, bounds that
mixed derivative by three, and proves nonsingularity under `3|ε|/2 < 1`.
The global inverse theorem proves the actual continuous Banach-selected half
solve differentiable. The symmetric construction proves the position inverse
differentiable; all four determinant factors are computed and cancel by mixed-
partial equality. Linear conjugacy transfers determinant one to
`PhaseSpace Unit`, and the Haar theorem proves exact phase-volume preservation.
The restricted B2 numerical solver refinement is now complete as a
certificate-parametric theorem. Guarded operation-local SoftAbs certificates
compose Hessian error through the positive eigenvalue, square root, inverse
factor, and log determinant; residual/contraction bounds then propagate the
finite loops through position, final momentum, endpoint energy, stabilized
weights, cumulative boundaries, and multinomial selection. Instantiating the
remaining primitive Float64/libm/arithmetic/RNG error premises for a particular
Julia platform is deliberately separate from this real-valued certificate.
For the paper-style nonconstant metric, in addition to the removable-zero sinusoidal client, Lean
now has the nondegenerate target `U(q)=q²-sin(q)`, whose actual Hessian lies in
`[1,3]`. Its potential, force/Hessian relationship, measurability, Equation
(12) data, uniform ellipticity, a uniform SoftAbs derivative bound, and global
Lipschitz continuity of the resulting scalar metric eigenvalue are machine
checked. The slice transfer and solver are also complete: reusable scalar callback theorems identify both
coordinate derivatives, yield global contraction constants, and construct a
concrete nonzero-step exact solve with its negative-step inverse. The exact
target-specific theorem is now complete: the generic Banach construction
satisfies the same generalized-leapfrog equations, uniqueness identifies it
with the certified Hamiltonian solver, and its unit Jacobian yields exact
phase-volume preservation. The restricted finite-precision refinement chain is
complete conditionally on its explicit platform-operation and boundary-margin
witnesses.
The generic triangular-shear
derivative matrices, determinant formulas, and mixed-partial pairing are now
extracted from the earlier bounded client, and the SoftAbs callbacks satisfy
the required scalar mixed identity. Inverse-stage differentiability,
determinant composition, callback binding, and linear conjugation to
`PhaseSpace Unit` are complete. The constructed step is bijective and
differentiable with determinant one, and the Haar change-of-variables theorem
supplies exact measure preservation.

## Track C: later breadth branches

The pre-Xu dependency order is:

1. general-state MH and invariant-kernel combinators -- complete;
2. quantitative independence MH and state-dependent Gaussian MALA -- complete;
3. exact two-block auxiliary Gibbs and the abstract slice factorization --
   complete;
4. measurable uniform-under-the-graph and level-set kernels for a concrete
   exact slice sampler -- complete for finite under-graph measures on nonempty
   standard Borel state spaces via the disintegrated horizontal conditional;
5. tagged disjoint-union reference measures and transport-density certificates
   for reversible-jump MH -- complete at the abstract level and instantiated
   by a zero-to-one-dimensional Euclidean birth/death move with a checked
   scaling Jacobian; and
6. finite particle methods -- iid particle-average unbiasedness and its
   pseudo-marginal MH client are complete; multinomial resampling,
   heterogeneous propagation, and their one-step Feynman--Kac expectation
   identity are also complete. Iterated operators now prove the arbitrary
   finite-horizon homogeneous Feynman--Kac expectation identity under strictly
   positive potentials, and the same nested-expectation identity is complete
   for finite time-inhomogeneous sequences. A normalized law over explicit
   population/ancestry histories, its product-weight expectation theorem, and
   an exact pseudo-marginal client are complete. Initial laws, potentials, and
   transition kernels may all depend on the proposed state at a common finite
   horizon. Weighting histories by their estimator and uniformly selecting a
   terminal particle now has the exact normalized Feynman--Kac terminal
   marginal. Backward ancestry tracing, path length, and endpoint identities are
   complete. The full path-observable many-to-one identity, PIMH, and particle
   marginal MH were the next obligations. The arbitrary-horizon labeled
   many-to-one identity and its equivalence to backward genealogy tracing are
   now complete, as is a finite PIMH kernel with exact extended-target
   stationarity and selected-path expectation. A finite PMMH client is also
   complete for parameter-indexed initial laws and fixed-horizon schedules
   whose potentials and transitions may depend on the parameter, including its
   exact parameter marginal and joint parameter/path expectation. The exact
   conditional-history specification and particle-Gibbs stationarity
   are complete. The concrete recursive forced-lineage generator now has a
   pointwise density theorem and is proved equal to the exact conditional law
   on every positive supported path. The abstract total kernel retains its
   identity fallback on zero-mass fibers.
   Positive-horizon trajectory PG is additionally indexed by the concrete
   count `N` through particle labels `Fin N`. Under an explicit bounded-model
   pointwise minorization, Lean constructs the refresh residual and proves a
   uniform geometric TV rate with coefficient
   `((N-1)/(N-1+B))^(T+1)`, including monotonic improvement of that coefficient
   with particle count. Separately, primitive full-support assumptions now
   construct a conservative refresh certificate and TV convergence directly
   for every explicit `N ≥ 2`. Deriving the sharper displayed minorization from
   primitive potential and transition bounds for the recursive forced-lineage
   generator remains the next quantitative model-level obligation. The proof
   boundary is now narrower than a collapsed-kernel assumption:
   `ForcedLineageParticleGibbsBound` asks for one shared-history density bound,
   and its `toMinorization` constructor transports that bound through exact
   conditional lift, uniform terminal-index refresh, and trajectory projection.
   Primitive full support separately proves every trajectory fiber positive.
   Finite compactness now also constructs a count-specific positive uniform
   floor over the explicit shared-history edges, converts it to the displayed
   coefficient shape, and yields its geometric TV theorem. The exact aggregation identity is proved: the transition entry
   is the conditional expectation of the fraction of terminal indices whose
   genealogy equals the proposed trajectory. This replaces the inadequate
   single-history route for particle-count asymptotics. Primitive positive
   finite potentials now automatically construct count-independent
   oscillation penalties and the resampling estimate `wᵢ ≥ 1/(N B)`; the
   aggregate is also identified exactly with an expectation under the
   concrete recursive forced-lineage generator. The cumulative backward-potential
   induction now propagates the local bounds through that generator. Its
   base and one-step population algebra are now machine checked: initialization
   loses only the retained slot, and a forced resample--propagate stage carries
   the aggregate marked-lineage mass with the exact `(N-1)/N` child-count
   factor. The zero-step kernel-level aggregate certificate has exact
   coefficient `(N-1)/N`. Normalizer telescoping, finite path labels, and the
   arbitrary-horizon forced-cloud induction are complete. The primitive raw-potential candidate schedule was corrected
   after the one-step audit: a raw potential oscillation constant `B` incurs
   the conservative penalty `2B-1`, hence factor `(N-1)/(N-2+2B)`, because comparing
   the self-normalized ordinary cloud with the exact target is a second cost
   beyond the retained-particle denominator. The proved schedule uses the
   oscillation of each full remaining backward potential, supplies the refresh
   decomposition and geometric TV estimate, and proves the actual fixed-
   iteration particle-count limit without a worst-case constant reduction.
7. adaptive-MCMC boundary -- finite state-dependent kernel selection and a
   counterexample where two frozen target-invariant kernels combine into a
   non-invariant selected kernel are complete. Predetermined nonhomogeneous law
   evolution, common-stationarity preservation, row total variation, and a
   deterministic diminishing-schedule definition are also complete.
   Finite random parameter adaptation is now an augmented Markov kernel; its
   successive-kernel change probability and convergence-in-probability
   Diminishing Adaptation condition are defined, with frozen state kernels
   proved diminishing under arbitrary parameter updates. Finite distribution
   TV, uniform mixing by a horizon, adaptive mixing-failure probability, and
   Containment are complete; simultaneous uniform mixing implies Containment.
   Distribution-TV triangle and Markov contraction, one-step kernel
   perturbation, and a telescoping predetermined-schedule comparison are also
   complete. State/parameter marginals, the exact adaptive next-state mixture,
   and its weighted row-to-target TV bound are complete. The anchored-window
   comparison and finite Roberts--Rosenthal theorem are now machine checked:
   Diminishing Adaptation plus Containment implies TV convergence of state
   marginals. A separate general-state Ionescu--Tulcea layer now constructs
   infinite path laws for measurable selectors that inspect the entire finite
   history, without forcing that memory into a finite parameter state. The
   general-state diminishing-adaptation, containment, and convergence theorem
   over this path semantics remains open.

The general-state disintegrated slice client and an exact executable finite
integer slice client are complete. Reversible jump now includes both the
scalar zero-to-one-dimensional client and a product-Jacobian-certified
zero-to-two-dimensional planar birth/death client. The finite
particle-MCMC spine through conditional SMC and particle Gibbs is complete at
fixed particle count and finite horizon. Convergence, mixing rates, and
particle-count asymptotics remain separate later layers. The particle-count
layer now includes exact iid `1/N` MSE and convergence in probability, plus
the heterogeneous conditional identity `sum coordinate variances / N²` for
independently propagated populations. Uniformly variance-bounded triangular
arrays additionally have `V/N` MSE and converge in probability around their
count-specific means. This supplies the local variance term for sequential
SMC. The full fixed-horizon particle-count theorem is now complete. The exact
one-stage propagation/ancestry variance identity is combined with the
self-normalized-ratio bound; recursively generated bootstrap population laws
are compared with recursively generated exact normalized Feynman--Kac target
laws. Finite potential minima, observable sup norms, and stage-variance bounds
construct an observable-indexed coefficient `C`, and Lean proves
`MSE ≤ C/N` for every finite strictly-positive-potential schedule on a finite
nonempty state space. Count-indexed laws then converge in mean square and in
probability at every fixed horizon. Uniform-in-time consistency and a PG-chain
mixing theorem uniform in particle count remain distinct stability problems.
The recursively normalized target is proved equal both to the conventional
unnormalized Feynman--Kac ratio and to the selected terminal marginal of the
existing particle-MCMC extended target, so this asymptotic layer introduces no
competing target definition.

General-state composable inference is also complete at the common-target
stationarity layer. `Mcmc.Kernel.ComposableInference` supplies scoped
operators, arbitrary finite schedules, a named PG--HMC composition, and an
instantiation whose PG side is discharged by the exact auxiliary-variable
factorization theorem. `Examples.GeneralStatePgHmc` now closes a concrete
dependent Boolean/Gaussian client: the Boolean records the position's sign,
its reverse half-line conditional is constructed by standard-Borel
disintegration, and the actual Gaussian SoftAbs multinomial GR-HMC transition
supplies the continuous update. Its explicitly target-refresh-augmented form
now has direct setwise convergence from every initial probability law, while
the unaugmented composition is only claimed stationary. Portable schedule descriptors can also be
bound to their exact scoped kernels and invariance proofs; foreign callback
equality remains a language-semantics obligation.

That quantitative obligation now has a checked target interface. A finite
refresh decomposition yields an exact regenerative law and a uniform
geometric TV bound. Positive-horizon particle Gibbs now has a checked
trajectory-state kernel, target marginal, and stationarity theorem built by
exact conditional lift, terminal-index refresh, and projection. Its Doeblin
specialization is on this trajectory space rather than the more restrictive
retained-history space, and any pointwise minorization constructs the residual
certificate automatically. Deriving its minorization premise from concrete
bounded Feynman--Kac potentials remains model-specific work. Conditional on
that certificate, the count/horizon coefficient is explicit and its
large-particle asymptotics are now complete: constant and scheduled
coefficients tend to one, and fixed-positive-iteration geometric factors tend
to zero. Under a count-uniform family of those explicit model certificates,
Lean now transfers that scalar limit to the actual count-indexed PG laws:
their total-variation distance from the trajectory target tends to zero after
every fixed positive number of iterations. The intermediate support interface is now
machine checked: `ParticleGibbsFiberConnectivity` reduces positivity of each
collapsed trajectory transition to a positive selected-history witness and a
positive terminal-index edge between the corresponding fibers, and this
criterion implies total-variation convergence. The unconditional zero-horizon
`N⁻ᵏ` result and
the one-particle identity obstruction remain the exact particle-count anchors.
For the first positive-horizon model class, every finite particle index type
with at least two members now constructs a shared identity-ancestry history
containing any two requested trajectories. Positive initial mass and
full-support propagation therefore discharge fiber connectivity at every
finite horizon and give TV convergence from every initial law. The
count-indexed `Fin (extra+1)` wrapper constructs the conservative
strict-positivity refresh and its geometric bound for every `extra > 0`.
Sharper closed-form coefficients under bounded potentials remain open.
For finite clients, strict positivity of the complete trajectory transition
matrix already discharges convergence: the library constructs an explicit
positive product lower bound and proves TV convergence from every initial law.

After those foundations and the paper execution milestones, the optional
breadth branches are:

- numerical U-turn/subtree-exclusion construction beyond the completed finite
  certified-tree, executable checker, Julia certificate mirror, canonical
  barrier-partition builder, stopped-doubling selection theorems, and concrete
  scalar and arbitrary finite-dimensional adjacent-endpoint U-turn partitions.
  Recursive aggregation of completed binary subtrees is now checked in Lean
  and mirrored in Julia. Julia now refuses invalid row families and performs
  the formally specified target-weighted transition directly from a valid
  certificate. A total checked-or-identity wrapper is proved stationary for
  arbitrary rows and mirrored in Julia, where failed certification makes no
  move. The root-independent all-scales construction is now exposed as the
  end-to-end Julia `CertifiedDynamicHMC` sampler with differential selector and
  reproducibility tests. Equivalence with a root-dependent standard
  dynamic-NUTS builder remains;
- stepping-out/shrinkage beyond the exact disintegration, finite integer slice,
  and bounded-interval continuous rejection implementation. A practical
  Reference/Optimized real-line stepping-out sampler is now tested; its
  formal endpoint is now generalized correctly: Lean proves invariance for
  any height/current-state horizontal Markov update preserving the swapped
  under-the-graph law, rather than requiring an exact conditional redraw.
  Proving the guarded Julia stepping-out/shrinkage transition satisfies that
  joint-preservation premise remains;
- reversible-jump transports beyond the checked scalar and planar
  birth/death scaling clients. Product transport-density certificates now
  compose recursively and instantiate a three-dimensional scaling transport;
  a genuinely nonlinear non-product cubic triangular shear now has an explicit
  curved-strip pushforward density and a complete tagged MH invariance theorem.
  Broader nonlinear diffeomorphism families remain a further extension;
- particle MCMC after finite SMC and pseudo-marginal foundations;
- adaptive MCMC beyond the completed boundary counterexample only with
  the completed predetermined nonhomogeneous semantics and deterministic
  diminishing vocabulary, augmented random-adaptation semantics, and
  convergence-in-probability definition and completed finite
  Roberts--Rosenthal convergence theorem; and
- BPS/Zig-Zag path construction, general-state event simulation,
  state-dependent-rate nonexplosion, and convergence on top of the
  separate PDMP generator, jump-flux, finite bounded-rate uniformization, and
  completed Poissonized real-time semigroup, fixed-event path-skeleton, and
  finite continuous-time schedule/càdlàg foundations. General-state
  Poissonization of an arbitrary embedded mathlib Markov kernel is complete,
  including Markov validity, invariant-target preservation, and finite-count
  nonexplosion for the bounded homogeneous clock. The all-count horizon
  executor also has an adjacent-count flux cancellation theorem; concrete
  standard-Gaussian Zig-Zag generator balance is now checked for velocity and
  position-times-velocity observables, while Zig-Zag/BPS clients still need to
  derive the scheduler's full flux certificate. General bounded
  state-dependent pure-jump mechanisms now have a thinned embedded kernel and
  real-time transition, with rate-biased balanced flux transported through
  accepted/rejected clock decomposition to real-time invariance. Deterministic
  measurable semiflows, flow-then-jump segments, fixed-schedule execution, and
  schedule composition are now defined. Joint measurability supports random
  exponential waits, and globally bounded state-dependent intensities now have
  an exact per-candidate thinning kernel and fixed candidate-count iterates.
  A conditional fixed-horizon executor now consumes candidate waits, fills the
  residual horizon by deterministic flow, and is proved Markov; its bounded
  homogeneous-clock candidate count has the exact Poisson law and is almost
  surely finite. Conditional on a positive horizon and fixed count, the iid
  continuous-uniform timestamp product law is constructed and proved a
  probability measure. Certified measurable timestamp orderings induce ordered
  timestamp and inter-wait probability laws; the two-event `min/max` sorting
  network is checked. The one-candidate conditional law is fully connected to
  flow, thinning, and residual-horizon execution as a Markov kernel.
  The all-count ordering certificate is now constructed by measurable finite
  gluing. The resulting unconditional joint Poisson-count/padded-wait law is
  normalized and has the exact Poisson count marginal.
  Arbitrary-count measurable schedule execution is also complete: flow/jump
  steps retain the schedule, runtime-count selection is proved Markov, residual
  flow reaches the horizon, and the exact Poisson schedule drives a complete
  bounded positive-horizon transition kernel.
  A general independent-parameter mixture theorem now reduces stationarity of
  this kernel to invariance of every fixed-count schedule section, without
  asserting that generator cancellation alone has discharged that premise.
  Concrete one-dimensional Zig-Zag and finite-dimensional BPS clients provide
  their linear flows, event kernels, and bounded-thinning constructors. The
  one-dimensional Zig-Zag generator cancellation and finite-dimensional BPS
  reflection geometry are checked; semigroup/stationarity results for the
  flow-driven path kernel, unbounded-rate Lyapunov arguments,
  process-level stationarity, and convergence remain. A bounded constant-rate
  telegraph client now closes process-level stationarity for the actual
  arbitrary-count positive-horizon kernel, including the Poisson candidate
  count and continuous ordered event-time mixture. A reusable theorem derives
  this from separate invariance of every flow segment and the uniformized
  event. This sigma-finite example does not discharge the state-dependent
  spatial-flux or convergence obligations for Zig-Zag/BPS.
  The BPS client now includes a full independent velocity-refresh kernel,
  unified with the Hamiltonian momentum-refresh layer, with Markovness,
  product-target invariance, and exact retention of measurable position
  events proved. Under a global rate bound, it now also exposes the exact
  positive-horizon Poisson/ordered-time bounce kernel and a Markov
  refresh-then-bounce composition. Product invariance of that composition is
  reduced to the explicit bounce spatial-flux obligation. Removing the global
  bound for Gaussian BPS and proving that obligation and ergodicity remain
  open in general dimension. For the one-dimensional unit-speed Gaussian
  client, reflection, canonical rate, and flow are now proved identical to
  the exact Gaussian Zig-Zag representation. Its unbounded-rate horizon kernel
  and almost-sure nonexplosion therefore reuse the checked Zig-Zag path
  construction. The shared setwise forward equation and convergence remain
  open.
  Separately, the unbounded-rate standard-Gaussian Zig-Zag now has a genuine
  event kernel based on the closed-form inverse integrated hazard. Its unit
  exponential draw is positive almost surely, the inversion equation is
  machine checked almost surely, and fixed-event iterates are Markov. Turning
  those event iterates into a stationary finite-horizon process now has the
  stopping-kernel construction but still requires stationarity. A measurable
  first cumulative-time crossing selects the completed-event state and exact
  residual flow; the endpoint is jointly measurable and its kernel is Markov,
  with the fallback branch null by nonexplosion. Nonexplosion itself is now
  complete: the signed
  position after an event is an explicit negative square root of the fresh
  hazard, so every subsequent wait is at least `sqrt(2E)`; under the constructed
  infinite i.i.d. hazard product law, second Borel--Cantelli proves that this
  lower-bound series and hence cumulative event time diverge almost surely.
  A new setwise forward-equation bridge turns zero time derivative of every
  measurable-event transported mass into invariance of the whole Markov
  family. The Gaussian horizon kernel has the concrete consumer theorem; its
  remaining stationarity task is to derive that differential certificate from
  the checked Gaussian generator identity and the constructed path law. A
  reusable `GaussianSteinTest` certificate now packages arbitrary
  velocity-dependent observables with their integrability and Gaussian
  integration-by-parts proof and implies generator cancellation. The standard
  Gaussian density derivative and improper integration by parts are now
  checked, so differentiability, weighted integrability, and Gaussian boundary
  decay construct this certificate directly rather than assuming the Stein
  identity. Compactly supported `C¹` velocity differences now form an
  automatically certified core: all integrability and boundary hypotheses and
  the resulting generator cancellation are proved. A general stationarity
  bridge now proves regular measures equal from constant compactly supported
  continuous expectations, and the Gaussian horizon family consumes this
  compact-test forward certificate with concrete transported-measure
  regularity discharged automatically. It remains to derive time
  differentiability and the zero derivative for the constructed path law from
  the smooth generator core.
  In parallel, the weak-forward route is now factored precisely: a generic
  uniqueness theorem upgrades generator balance to invariance on an explicit
  differentiable test domain. The Gaussian smooth-test domain is instantiated,
  its full product-target generator expectation is zero, and exact horizon
  stationarity follows from one remaining weak-forward uniqueness theorem for
  the stopped path construction.
  The normalized Gaussian/equal-velocity target and exact zero-time identity
  are discharged, so the specialized certificate contains only
  differentiability and the zero-derivative forward equation.

Sequence-parallel evaluation is an execution-refinement project downstream of
exact seeded trace semantics. Full solver convergence may refine a sequential
trace; numerical tolerance and early stopping remain separate bias
obligations.

## Immediate plan

A1--A4, B1, and the exact/guarded B2 sampler construction are complete. The
remaining work is ordered by the missing mathematical dependency rather than
by paper date:

1. prove weak-forward uniqueness for the constructed Gaussian Zig-Zag stopped
   path, closing Gaussian Zig-Zag and one-dimensional unit-speed Gaussian BPS
   stationarity. The obligation is now split exactly into scalar weak-
   expectation uniqueness and measure determination by the certified smooth
   test family; Lean proves that these two statements reconstruct the full
   uniqueness interface. A separate target-started interface records the
   strictly weaker premise actually sufficient for stationarity, avoiding an
   unnecessary global well-posedness theorem. The target-started scalar
   uniqueness and measure-determination pair now feeds Gaussian Zig-Zag and
   unit-speed Gaussian BPS stationarity directly;
   the smooth test certificate now also requires each supplied derivative to
   be the actual derivative of its velocity-specific observable, and derives
   the difference identity rather than assuming it independently;
2. bare Gaussian SoftAbs GR-HMC convergence -- complete for the concrete
   one-dimensional `ε = 1`, `L = 1` chain. Lean proves affine drift, compact
   skeleton minorization, faithful geometric meeting, the normalized target's
   exponential moment, skeleton setwise convergence, and the finite-residue
   lift to every unthinned time index. Length zero and zero step size remain
   exact identity obstructions, so this result is deliberately not stated for
   arbitrary parameters;
3. count-uniform positive-horizon particle Gibbs -- complete with the
   cumulative backward-potential schedule, fixed-count geometric TV theorem,
   and fixed-positive-iteration particle-count limit. The raw-current-
   potential substitution remains explicitly stronger and unproved; and
4. finish the optional breadth clients: standard dynamic-NUTS tree recursion,
   ideal refinement of stepping-out slice sampling, indefinitely adapting
   general-state diminishing-adaptation/containment, and general-dimensional PDMP
   stationarity/convergence.

   The unbounded-history adaptive semantics now includes an exact finite-freeze
   theorem: arbitrary history-dependent burn-in followed by a fixed kernel
   inherits its homogeneous powers, two-sided Doeblin bounds, and setwise
   convergence. The remaining adaptation milestone is specifically the
   Roberts--Rosenthal regime where adaptation continues indefinitely.

   The general-dimensional BPS generator and its velocity-integrated
   transport-minus-normal-flux identity are now checked, including the
   zero-gradient case. The product-space mean-zero theorem is also checked and
   reduces full generator balance exactly to reflection invariance plus a
   multidimensional spatial integration-by-parts premise. Orthogonal
   reflection invariance of mathlib's finite-dimensional standard Gaussian is
   now proved coordinate-free and transported to `Position`; the coordinate
   Householder formula is proved equal to that conjugated reflection and hence
   preserves the transported probability law. The finite-product Gaussian
   density factorization is now proved, closing equality with the canonical
   density-defined `standardMomentumMeasure` and yielding its direct reflection
   preservation theorem. The remaining multidimensional integration-by-parts
   premise is now assembled from scalar coordinate identities, and the
   standard-Gaussian BPS theorem derives the finite-sum directional and flux
   conditions from component integrability. Proving those scalar identities
   from target-specific differentiability and boundary decay,
   construction of the unbounded-rate process,
   weak-forward uniqueness, and ergodicity remain.
   The standard-Gaussian specialization of the product generator theorem now
   discharges reflection invariance internally.

   The nonlinear reversible-jump branch is complete at the exact theorem and
   executable-client levels; only the shared Float64 primitive boundary
   remains, as for the other generated/runtime samplers.

These open items do not weaken the completed finite Gibbs, tempering,
pseudo-marginal, independence-MH, MALA, adaptive-boundary, Xu et al. coupling,
or corrected exact GR-HMC invariance claims.
