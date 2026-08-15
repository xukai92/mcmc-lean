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
The remaining B2 work is refinement rather than sampler construction:
finite-precision Julia iterations must be related to an exact selection, and
the paper's practical diagonal SoftAbs target class still needs its own
solver certificate.

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
   with particle count. Deriving the displayed minorization from primitive
   potential and transition bounds for the recursive forced-lineage generator
   remains the next model-level obligation.
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
   marginals. Unbounded-history adaptation still requires enlarging the finite
   parameter state.

The general-state disintegrated slice client and an exact executable finite
integer slice client are complete. Reversible jump now includes both the
scalar zero-to-one-dimensional client and a product-Jacobian-certified
zero-to-two-dimensional planar birth/death client. The finite
particle-MCMC spine through conditional SMC and particle Gibbs is complete at
fixed particle count and finite horizon. Convergence, mixing rates, and
particle-count asymptotics remain separate later layers.

General-state composable inference is also complete at the common-target
stationarity layer. `Mcmc.Kernel.ComposableInference` supplies scoped
operators, arbitrary finite schedules, a named PG--HMC composition, and an
instantiation whose PG side is discharged by the exact auxiliary-variable
factorization theorem. `Examples.GeneralStatePgHmc` now closes a concrete
mixed Boolean/Gaussian client using the actual Gaussian SoftAbs multinomial
GR-HMC transition. Portable schedule descriptors can also be bound to their
exact scoped kernels and invariance proofs; foreign callback equality remains
a language-semantics obligation.

That quantitative obligation now has a checked target interface. A finite
refresh decomposition yields an exact regenerative law and a uniform
geometric TV bound. Positive-horizon particle Gibbs now has a checked
trajectory-state kernel, target marginal, and stationarity theorem built by
exact conditional lift, terminal-index refresh, and projection. Its Doeblin
specialization is on this trajectory space rather than the more restrictive
retained-history space, and any pointwise minorization constructs the residual
certificate automatically. Deriving a positive coefficient from bounded
Feynman--Kac potentials, and its dependence on particle count and horizon,
remains model-specific work. The intermediate support interface is now
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
finite horizon and give TV convergence from every initial law. Sharper
coefficients under bounded potentials and
their explicit dependence on a general particle count remain open.
For finite clients, strict positivity of the complete trajectory transition
matrix already discharges convergence: the library constructs an explicit
positive product lower bound and proves TV convergence from every initial law.

After those foundations and the paper execution milestones, the optional
breadth branches are:

- numerical NUTS tree-building refinement beyond the completed finite
  certified-tree and stopped-doubling selection theorems;
- continuous stepping-out/shrinkage implementations beyond the exact
  disintegration and executable finite integer-slice clients;
- reversible-jump transports beyond the checked scalar and planar
  birth/death scaling clients;
- particle MCMC after finite SMC and pseudo-marginal foundations;
- adaptive MCMC beyond the completed boundary counterexample only with
  the completed predetermined nonhomogeneous semantics and deterministic
  diminishing vocabulary, augmented random-adaptation semantics, and
  convergence-in-probability definition and completed finite
  Roberts--Rosenthal convergence theorem; and
- BPS/Zig-Zag path construction, Chapman--Kolmogorov composition,
  general-state event simulation, nonexplosion, and convergence on top of the
  separate PDMP generator, jump-flux, finite bounded-rate uniformization, and
  completed Poissonized real-time transition-kernel foundations.

Sequence-parallel evaluation is an execution-refinement project downstream of
exact seeded trace semantics. Full solver convergence may refine a sequential
trace; numerical tolerance and early stopping remain separate bias
obligations.

## Immediate plan

A1--A4 and B1 are complete. Phase I is complete: fully state-indexed finite
PMMH, concrete conditional SMC, particle Gibbs, the consolidated particle-MCMC
surface, corrected relativistic execution, and its guarded implicit-solver
certificate interface are all present. Practical slice transitions and richer
reversible-jump clients are optional breadth branches. Subsequent work can
strengthen the B2 numerical refinement, particle convergence/asymptotics, and
the paper-specific theorem instances. None of these is needed to support the
completed finite Gibbs, tempering,
pseudo-marginal, independence-MH, MALA, adaptive-boundary, or Xu et al.
coupling claims.
