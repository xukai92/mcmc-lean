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

### B2. Executable Xu and Ge (2024) sampler

Implement the corrected radial/spherical momentum construction,
inverse-factor transport, and nonseparable multinomial transition. Approximate
implicit solves must return residual or integrator certificates consumed by
the existing conditional theorem; a fixed iteration count is insufficient.

IR version 10 now contains a working corrected diagonal constant-metric
relativistic multinomial specialization, with Reference/Optimized Julia replay
tests. A position-dependent fixed-point solver now exists in Reference and
Optimized Julia with residual reporting, while Lean constructs its exact
Banach-fixed-point counterpart and proves uniqueness and convergence of the
finite loops. Lean now also has a fixed-step interface and a concrete
smooth momentum-even nonseparable instance: both implicit maps contract under
the explicit condition `|εa/2| < 1`, giving a measurable exact unique solve,
convergent finite loops, and momentum-flip reversal. Proving phase-volume
preservation is now reduced to an explicit differentiability/unit-Jacobian
certificate: opposite-step uniqueness already supplies bijectivity, and Lean
proves that the certificate implies preservation of product phase volume.
The bilinear stress model now closes this argument unconditionally in every
finite dimension through its exact reciprocal-scaling formula. Proving the
certificate for the smooth momentum-even model, instantiating a solver with
the derivatives of the canonical globally positive nonconstant
`1 + ‖q‖²` metric Hamiltonian (whose factor-volume and measurability
obligations and Equations (12)--(13) derivative callbacks are now discharged),
proving contraction and phase volume for that actual derivative pair, and
refining Float64 residuals to that exact selection remain before B2 is
complete.

The bounded scalar client `2 + sin(q)` now closes the actual-derivative
contraction portion: for `3|ε|/2 < 1` Lean constructs the exact unique solver
and proves finite-loop convergence, measurability, and reversal. The remaining
formal endpoint is its unit-Jacobian/phase-volume certificate. Float64 loops
retain measured residuals and are not identified with the exact fixed point.

The mixed-partial and scalar determinant-cancellation portions of that
certificate are now machine checked. A reusable theorem proves continuity of
the fixed point of a jointly continuous uniformly contractive family, and the
bounded scalar client instantiates it for both implicit solves and the full
step. Four explicit triangular maps and three checked identities now expose
the solver as the incoming inverse, right/left position transfer, and outgoing
map used by the paper's Jacobian calculation. What remains is the
implicit-function step upgrading the two continuous, globally unique inverse
selections to differentiable maps, after which the existing Haar
change-of-variables theorem closes phase volume.

The generic inverse-function wrapper needed for that upgrade is now proved:
an everywhere-nonsingular differentiable finite-dimensional map with a
continuous global left inverse has a differentiable inverse selection. The
bounded client also exposes scalar-coordinate callback maps on `ℝ × ℝ`; the
remaining concrete calculation is their derivative nonsingularity and the
transport back across the `Unit → ℝ` phase-space equivalence.

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

The slice and first Euclidean reversible-jump clients are complete. The finite
particle-MCMC spine through conditional SMC and particle Gibbs is complete at
fixed particle count and finite horizon. Convergence, mixing rates, and
particle-count asymptotics remain separate later layers.

After those foundations and the paper execution milestones, select the
remaining branches based on research value and shared infrastructure:

- NUTS finite candidate trees before adaptation or modern multinomial NUTS;
- practical stepping-out/shrinkage slice kernels beyond the exact
  disintegration client;
- richer reversible-jump transports beyond the checked scalar birth/death
  scaling client;
- particle MCMC after finite SMC and pseudo-marginal foundations;
- adaptive MCMC beyond the completed boundary counterexample only with
  the completed predetermined nonhomogeneous semantics and deterministic
  diminishing vocabulary, augmented random-adaptation semantics, and
  convergence-in-probability definition and completed finite
  Roberts--Rosenthal convergence theorem; and
- BPS/Zig-Zag only in a separate continuous-time PDMP architecture.

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
