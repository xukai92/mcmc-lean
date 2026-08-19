# MCMC and HMC algorithm scope review

This note broadens the repository's algorithm map beyond its current paper
targets. It is a triage review, not a claim that every item should become an
implementation. Each paper below was independently reviewed from the primary
source. The review was completed on 2026-08-15; the requested 2025 paper was
checked at arXiv version 2, dated 2025-12-02.

The priorities mean:

- **P0 -- grounding or already central:** cite accurately and preserve the
  paper's theorem boundary in the current architecture;
- **P1 -- next reusable coverage:** a relatively direct extension that creates
  infrastructure shared by several algorithms;
- **P2 -- important later branch:** high-value coverage with substantial new
  measure-theoretic, asymptotic, trans-dimensional, adaptive, or continuous-time
  infrastructure; and
- **P3 -- execution research:** valuable after the corresponding exact sampler
  and deterministic trace semantics exist.

These priorities are about formalization order, not scientific importance.
Throughout, invariance or detailed balance is not described as convergence.

## Recommended coverage spine

| Layer | Near-term representative | What it unlocks |
|---|---|---|
| Kernel combinators | Gibbs scans and parallel tempering | composition, mixtures, coordinate lifts, product targets, stationary marginals |
| Extended-state MH | pseudo-marginal MH | particle MCMC and other auxiliary-variable exactness arguments |
| General-state convergence | Tierney's independence-MH minorization | a first explicit bridge from stationarity to a quantitative convergence theorem |
| Continuous proposals | MALA | state-dependent Gaussian proposals and a clean biased-ULA/exact-MALA distinction |
| HMC selection | NUTS candidate-tree kernel | dynamic trajectories once ordinary and multinomial HMC are stable |
| Nonreversible continuous time | BPS or Zig-Zag stationary generator identity | PDMP semantics, event simulation, thinning, and global rather than detailed balance |
| Nonhomogeneous chains | finite adaptation, then diminishing adaptation and containment | a sound basis for production warmup and tuning |
| Parallel execution | causal-recurrence scan equivalence | verified parallel evaluation without changing the seeded sequential chain |

The first two rows fit the repository especially well: they reuse the existing
MH and lift--evolve--project ideas rather than requiring convergence theory at
the outset. The general-state `ProbabilityTheory.Kernel` bridge remains the
main dependency for continuous algorithms. Continuous-time PDMPs and adaptive
chains are separate architectural branches and should not be forced into the
elementary finite interface.

## Foundations: Metropolis, Gibbs, and general-state chains

### Metropolis et al. (1953): symmetric Metropolis updates -- P0

[Metropolis, Rosenbluth, Rosenbluth, Teller, and Teller](https://doi.org/10.1063/1.1699114)
introduce symmetric local proposals, the acceptance rule
`min(1, exp(-ΔE / kT))`, and the essential rejection self-loop. Their finite
pairwise-flow argument is the historical core of Metropolis correctness, but
their reachability discussion is not a modern convergence theorem and the
paper does not quantify approach to equilibrium.

**Repository fit.** The current finite and general-state MH results already
subsume the correctness argument, including asymmetric and zero-probability
cases. Add at most a named symmetric-proposal/Boltzmann specialization and a
small periodic hard-disk example much later; do not formalize the historical
simulation as core infrastructure.

### Hastings (1970): general proposal correction -- P0

[Hastings](https://doi.org/10.1093/biomet/57.1.97) generalizes Metropolis to
asymmetric proposals, makes rejection mass explicit, and derives a family of
balanced acceptance rules containing Metropolis and Barker acceptance. He
separates irreducibility from detailed balance and also discusses component
updates and correlated-sample error estimation. The continuous-state passage
is informal by current measure-theoretic standards.

**Repository fit.** Existing accepted-flow MH is a machine-checked version of
the principal construction. A generic balanced-flow interface with a Barker
instance is optional. More useful is a reusable theorem that compositions and
mixtures of invariant kernels remain invariant; a deterministic scan need not
remain reversible.

### Geman and Geman (1984): Gibbs sampling and annealing -- P1

[Geman and Geman](https://doi.org/10.1109/TPAMI.1984.4767596) connect positive
finite Markov random fields with Gibbs distributions and use local heat-bath
updates for image restoration. At fixed temperature this is Gibbs sampling;
under a sufficiently slow logarithmic cooling schedule their finite,
time-inhomogeneous process concentrates on global energy minima. Posterior
sampling and cooling to a MAP solution are different objectives.

**Repository fit.** Define finite product-state conditional distributions,
one-site and block Gibbs kernels, random-scan mixtures, and systematic-scan
composition. Prove stationarity first, then add explicit positivity,
irreducibility, and a stated convergence mode. Simulated annealing belongs in
a later inhomogeneous-chain module with energy-barrier assumptions.

### Tierney (1994): general-state MCMC theory -- P0/P1

[Tierney](https://doi.org/10.1214/aos/1176325750) organizes general-state MH,
Gibbs, mixtures, and cycles around invariant kernels, then states the extra
irreducibility, aperiodicity, Harris recurrence, small-set, and drift
conditions needed for total-variation convergence, LLNs, CLTs, and geometric
ergodicity. In particular, a bounded target-to-proposal weight gives an
independence-MH minorization and uniform rate.

**Repository fit.** Use this as the boundary document for the kernel bridge.
Near term, add composition/mixture stationarity and the bounded-weight
independence-MH minorization. Harris recurrence, drift/small-set theory, and
limit theorems are later general-state infrastructure. When formalizing a
specific result, trace Tierney's synthesized theorem to its original source.

## Major MH extensions

### Roberts and Tweedie (1996): Langevin, ULA, and MALA -- P1/P2

[Roberts and Tweedie](https://projecteuclid.org/journals/bernoulli/volume-2/issue-4/Exponential-convergence-of-Langevin-distributions-and-their-discrete-approximations/bj/1178291835.full)
separate the Langevin diffusion, its biased fixed-step Euler approximation
(ULA), and Metropolis-adjusted Langevin (MALA). They show that target
invariance and geometric convergence are distinct: discretization may be
transient and MALA may fail geometric ergodicity for both heavy and very light
tails even when its Hastings correction preserves the target.

**Repository fit.** First define the Gaussian Langevin proposal and obtain
MALA validity, detailed balance, and stationarity from general MH; define ULA
separately and never label it exact at fixed step. Tail examples make good
regressions. The paper's rate results require diffusion generators,
irreducibility, small sets, and Foster--Lyapunov theory and are P2.

### Green (1995): reversible-jump MCMC -- P2

[Green](https://doi.org/10.1093/biomet/82.4.711) constructs MH moves on a
disjoint union of parameter spaces of different dimensions. Auxiliary
variables match dimensions, an invertible transformation pairs forward and
reverse moves, and the acceptance ratio includes move probabilities,
auxiliary densities, and the absolute Jacobian. This proves detailed balance,
not traversal or convergence across models.

**Repository fit.** The two-model tagged reference, density-level RJ-MH kernel,
Markov/reversibility/invariance theorems, and symmetric cross-model accepted
flow are now machine checked. A transport-density certificate states that the
auxiliary transport pushes forward to the claimed proposal density and proves
its normalization; this is the exact slot for a Jacobian theorem. The compiled
two-singleton-model example exercises cross-model movement but is periodic.
A second client now moves between `Unit` and `ℝ`: `u` uniform on `(-1,1]` is
transported by `y = 2u`, and Lean proves the resulting `1/4` density on
`(-2,2]`, including the inverse-Jacobian factor, before deriving RJ invariance.

### Roberts and Rosenthal (2007): adaptive MCMC -- P2

[Roberts and Rosenthal](https://doi.org/10.1239/jap/1183667414) prove marginal
total-variation convergence under Diminishing Adaptation plus either
Simultaneous Uniform Ergodicity or Containment. Their counterexamples show that
even when every frozen kernel is invariant and ergodic, state-dependent
adaptation can destroy convergence. Their main assumptions do not imply a
strong LLN or CLT.

**Repository fit.** Finite state-dependent selection and a small counterexample
are now machine checked: identity and flip kernels each preserve the uniform
two-state target, but selecting between them from the current state destroys
stationarity. Thus even common frozen-kernel invariance is insufficient before
one reaches the stronger question of adaptive convergence.

Predetermined nonhomogeneous finite-chain semantics are now machine checked:
Lean defines the law at every time and proves that if every scheduled kernel
preserves a common target, starting at that target preserves it at every finite
time. Finite row total variation lies in `[0,1]`, and deterministic uniform
diminishing schedules are defined; a frozen schedule is proved diminishing.
A finite random adaptive process is now formalized as a Markov kernel on state
and tuning parameter: the parameter selects the state kernel, then a
state-dependent conditional law updates the parameter. Lean defines the
probability, under the actual time-`n` augmented law, that successive selected
kernels differ by more than a row-TV threshold. Diminishing Adaptation is then
stated as convergence of this probability to zero. If every parameter selects
the same frozen state kernel, arbitrary random parameter updates are proved
diminishing.

Finite point-mass kernel iteration and distribution total variation now define
uniform mixing by a fixed horizon. Lean measures, under the actual augmented
law, the probability that the currently selected kernel has not reached a TV
tolerance by that horizon. Containment is formalized as boundedness of this
horizon in probability, and simultaneous uniform mixing of every parameter
kernel is proved sufficient for Containment.

This finite Markovian model can encode fixed finite adaptation memory but not
an unbounded history without enlarging the state type. The anchored random
finite-window comparison is now machine checked, and Diminishing Adaptation
plus Containment implies total-variation convergence of the deterministic
state-marginal laws. This is not an almost-sure path theorem, LLN, CLT, or
uniform convergence-rate result.

Its deterministic analytic core is now machine checked. Finite distribution TV
is symmetric and satisfies the triangle inequality; common-kernel evolution is
contractive; replacing a kernel costs at most its law-weighted row TV and hence
any uniform row bound; and two predetermined schedules differ by at most the
sum of their per-step row-TV bounds. The completed anchored argument turns the
change-probability tail bound into expected kernel variation, compares the
actual and frozen windows, and combines that comparison with Containment.
The random process now also exposes its exact state and parameter marginals.
Summing the parameter update out of an augmented transition is proved to give
the current-law mixture of selected state-kernel rows. Its next-state distance
to target is bounded by the augmented-law average of each selected row's
distance to target; this identifies the precise marginal quantity the final
convergence theorem must drive to zero.
Production warmup should be described as an inhomogeneous phase followed by a
frozen proved kernel.

### Andrieu and Roberts (2009): pseudo-marginal MH -- P1

[Andrieu and Roberts](https://doi.org/10.1214/07-AOS574) show that a
nonnegative unbiased target estimator can be retained as part of an extended
MH state. The extended target has the desired parameter marginal, so the
method is exact in the stationary-marginal sense. Refreshing both the current
and proposed estimates (MCWM) is generally biased, and unbounded estimator
weights can destroy geometric ergodicity.

**Repository fit.** This is the best next extended-state theorem: first use a
finite auxiliary type, prove normalization and the target marginal, and
instantiate existing finite MH with an estimator that may be zero. Then port
the construction to general kernels. This directly prepares particle MCMC.

### Andrieu, Doucet, and Holenstein (2010): particle MCMC -- P2

[Andrieu, Doucet, and Holenstein](https://doi.org/10.1111/j.1467-9868.2009.00736.x)
augment the state with particles, ancestry, and a selected trajectory. PIMH,
PMMH, and particle Gibbs preserve an extended target whose path/parameter
marginal is exact for fixed particle count under the stated support and
resampling assumptions. This exactness is not finite-particle independence or
automatic convergence; path degeneracy can still make the methods inefficient.

**Repository fit.** Finite iid particle populations and exact unbiasedness of
their average importance weight are now machine checked for every positive
particle count. They instantiate pseudo-marginal MH with exact extended
stationarity and the desired state marginal. Multinomial ancestry resampling,
heterogeneous propagation, and the one-step bootstrap expectation identity
are now machine checked as well. Iterated Feynman--Kac operators now prove the
product normalizing-constant expectation identity at every finite horizon for
strictly positive potentials, both for homogeneous iteration and finite
time-inhomogeneous sequences. A normalized finite law over explicit ancestry
and population histories now realizes those nested expectations, and its
normalized product weight instantiates pseudo-marginal MH with exact extended
stationarity and state marginal. The initial law, potential, and transition at
every step may now depend on the proposed state, provided all schedules share a
finite horizon and have positive normalizers. Weighting a history by its normalizing estimate and
selecting a terminal particle uniformly gives exactly the normalized
Feynman--Kac terminal marginal, for arbitrary observables and singleton events.
The terminal index is now traced backward through every stored ancestor map;
Lean proves the selected genealogy has one state per population and the exact
initial and terminal endpoints. A full path-observable many-to-one theorem is
required because terminal-marginal exactness alone does not identify the joint
trajectory law used by PIMH. The one-transition base is machine checked for
every parent--child observable: potential weighting cancels normalized
resampling, propagation supplies the exact transition expectation, and iid
initialization recovers the one-particle Feynman--Kac pair law. That identity is
now generalized to arbitrary inherited labels and iterated over every finite
horizon. Propagated singleton path prefixes are proved equal to backward
genealogy tracing. Consequently, the history-weighted selected-particle target
has the exact normalized Feynman--Kac expectation for every path observable.

Finite PIMH is now defined as independence MH proposing a fresh SMC history and
terminal index. Its extended target is stationary and its stationary selected
path is exact. This is not a convergence theorem: irreducibility, convergence
rates, and particle efficiency remain unproved. Conditional SMC is now
implemented by recursive forced-lineage sampling and proved equal to the exact
conditional selected-particle law on supported positive paths. Particle Gibbs
composes that refresh with uniform selected-index refresh and has proved
extended-target stationarity.

Finite PMMH is now complete for parameter-indexed initial particle laws and
fixed-horizon schedules whose potentials and transition kernels may also depend
on the parameter. Equal-length histories are transported into one common
auxiliary type; the estimator retains both the complete SMC history and selected
index. Lean proves extended-target stationarity, the exact requested parameter
marginal, and the correct joint parameter/selected-path expectation for the
corresponding parameter-specific Feynman--Kac model. Conditional SMC and
particle Gibbs are also complete at fixed finite horizon and particle count.
Stationarity is not asserted to imply convergence from arbitrary
initialization. Keep fixed-particle stationarity,
chain convergence, and consistency as particle count grows as separate theorem
families.

### Quantitative particle-Gibbs convergence -- P2

[Andrieu, Lee, and Vihola](https://doi.org/10.3150/15-BEJ785) derive
quantitative uniform-ergodicity bounds for iterated conditional SMC from
bounded potentials using a doubly conditional SMC argument. Independently,
[Lindsten, Douc, and Moulines](https://arxiv.org/abs/1401.0683) give a
time-inhomogeneous PG minorization whose coefficient is a product of
per-time factors involving model-specific future-likelihood bounds. These
results do not follow from stationarity or pointwise support alone.

**Repository fit.** The finite library now separates the exact steps needed
to formalize such a bound: a compatible shared-history density estimate, the
conditional-fiber normalization, uniform terminal-index refresh, trajectory
projection, and Doeblin convergence. `particleGibbsScheduleCoefficient`
records the product form for time-varying penalties; a constant penalty
specializes exactly to `particleGibbsCountCoefficient`. The doubly conditional
SMC density estimate that supplies the published model-dependent penalties is
still an open theorem, so the current generic `bound` must not be presented as
one paper's constant without an explicit instantiation.

## HMC foundations and practical variants

### Duane et al. (1987): hybrid/Hamiltonian Monte Carlo -- P0

[Duane, Kennedy, Pendleton, and Roweth](https://doi.org/10.1016/0370-2693(87)91197-X)
combine Gaussian momentum refreshment, a reversible volume-preserving
molecular-dynamics trajectory, and a global Metropolis correction. “No
discretization errors” means no ideal-arithmetic invariant-law bias after
correction, not exact energy conservation, floating-point exactness, or a
convergence theorem.

**Repository fit.** The repository already covers the relevant abstract
corrected deterministic proposal, leapfrog, momentum refresh, phase target,
projection, and invariance spine. Retain this as the founding citation and map
its assumptions to the existing endpoint-HMC theorems and executable
finite-precision boundary.

### Girolami and Calderhead (2011): manifold MALA and HMC -- P2

[Girolami and Calderhead](https://doi.org/10.1111/j.1467-9868.2010.00765.x)
use a position-dependent positive-definite metric for manifold MALA and a
nonseparable Hamiltonian for RMHMC. The generalized leapfrog is implicit;
reversibility and volume preservation presume exact solution of those
equations. Finite fixed-point truncation is therefore not automatically an
exact integrator. Density relative to Lebesgue versus Riemannian volume must
also be explicit, as clarified by [Xifara et al.](https://doi.org/10.1016/j.spl.2014.04.002).

**Repository fit.** Reuse the current measure-preserving phase-space and
Riemannian/relativistic work, but add state-dependent Gaussian proposal and
base-measure conventions before claiming MMALA coverage. Treat generalized
leapfrog through an exact-solver certificate or a reversibility/Jacobian-aware
failure policy; fixed iteration counts remain an executable refinement gap.

### Hoffman and Gelman (2014): NUTS -- P1/P2

[Hoffman and Gelman](https://www.jmlr.org/papers/v15/hoffman14a.html) replace a
fixed HMC path length with a randomized forward/backward doubling tree and a
U-turn stopping rule. Slice augmentation, subtree exclusion, and the special
candidate-selection construction are part of reversibility; simply stopping
at the first U-turn is not valid. Dual averaging is adaptive warmup, not part
of a fixed production kernel's invariance proof.

**Repository fit.** First formalize the finite tree/candidate-set kernel and
incremental uniform-selection equivalence on top of the existing HMC maps.
Then compose slice augmentation, dynamic tree construction, momentum refresh,
and projection. Freeze step size after warmup. Multinomial modern NUTS,
divergence thresholds, maximum depth, and floating-point behavior need
separate specifications.

The first dynamic balance layer is now complete: a finite target-weighted
candidate kernel is reversible whenever candidate membership is symmetric and
its normalizer is invariant under rerooting at any admitted point. Decidable
equivalence classes provide a nonconstant concrete client. This theorem states
the obligation a doubling/U-turn builder must discharge; it does not certify
first-U-turn stopping, subtree construction, or adaptation by itself.

### Beskos et al. (2013): optimal scaling of HMC -- P2

[Beskos, Pillai, Roberts, Sanz-Serna, and Stuart](https://doi.org/10.3150/12-BEJ414)
show for stationary iid product targets and fixed integration time that
leapfrog step size scales as `d^(-1/4)`, with a limiting acceptance formula and
an approximately 0.651 optimum for their cost-adjusted jump criterion. The
result is asymptotic and model/criterion dependent, not a universal tuning
rule or convergence theorem.

**Repository fit.** The reusable first target is the equilibrium energy-error
identity and cancellation that turns pointwise second-order error into a
fourth-order mean. Product decomposition, triangular-array CLT, acceptance
limit, and certified optimizer come later and should remain separate from
ordinary HMC invariance.

### Bou-Rabee and Sanz-Serna (2018): geometric integrators for HMC -- P0/P2

[Bou-Rabee and Sanz-Serna](https://doi.org/10.1017/S0962492917000101) survey
the reversible, volume-preserving map architecture behind corrected HMC and
derive a general equilibrium energy-error symmetry and mean-error bound. They
also organize high-dimensional product scaling and preconditioned/path-space
examples. The scaling results require stationarity, asymptotic expansions,
domination, and CLTs.

**Repository fit.** Use this as the geometric-integration source map. The
abstract corrected-map layer is already substantially present. Add the
measure-preserving energy-error change-of-variables identity next; defer iid
scaling and path-space preconditioning until asymptotic probability and
functional-analysis infrastructure exists.

## Other important sampler families

### Neal (2003): slice sampling -- P1/P2

[Neal](https://doi.org/10.1214/aos/1056562461) lifts an unnormalized density to
the uniform distribution under its graph, updates within a level set, and
projects back. Practical stepping-out/doubling and shrinkage algorithms depend
on trace-reversal details; doubling needs an acceptability test that tempting
simplifications can break. Invariance is proved for specified transitions,
while ergodicity remains separate.

**Repository fit.** The generic two-block lift--conditional-update--project
theorem is now machine checked: a vertical kernel and horizontal kernel
preserve the target whenever they give the two factorizations of the same
joint measure. The measurable uniform vertical-height kernel and its exact
Lebesgue-under-the-graph joint identity are also machine checked. For a finite
under-graph measure on a nonempty standard Borel state space, mathlib
disintegration now supplies a measurable horizontal conditional and Lean
proves invariance of the resulting exact slice sampler. On the real line,
measurable interval endpoints for all superlevel sets now give a fully explicit
total uniform horizontal kernel; null empty-level rows are handled without a
strict-width assumption, and Lean proves invariance of the resulting weighted-
Lebesgue sampler. Stepping-out/shrinkage and doubling are subsequent trace-
reversal targets. Crumb, reflective, and multivariate variants can wait. This completed
invariance interface does not by itself imply slice-chain convergence.

### Geyer (1991): Metropolis-coupled MCMC / parallel tempering -- P1

[Geyer](https://purl.umn.edu/58440) describes an ensemble with a product target
over temperatures, invariant within-level updates, and Metropolis-corrected
state swaps. The cold coordinate has the desired stationary marginal. It is
generally not an autonomous Markov chain after swaps, and stationarity alone
does not prove faster mixing. Geyer is the statistical MC³ source; replica
exchange has earlier statistical-physics antecedents.

**Repository fit.** Define finite product targets, coordinate-lifted kernels,
and transposition proposals; obtain swaps as ordinary MH and prove product
stationarity plus the cold marginal. This is a compact test of product,
composition, mixture, and marginal APIs. Temperature-ladder performance is a
later quantitative problem.

### Bouchard-Côté, Vollmer, and Doucet (2018): BPS -- P2

[Bouchard-Côté, Vollmer, and Doucet](https://doi.org/10.1080/01621459.2017.1294075)
define a nonreversible piecewise-deterministic process with linear motion,
gradient-triggered velocity reflection, and Poisson refreshment. A generator
cancellation proves invariance of target times Gaussian velocity. Positive
refreshment supports their uniqueness/ergodic-average result; without it even
a Gaussian example can fail ergodicity. Exact thinning requires certified
intensity bounds.

**Repository fit.** Create a separate continuous-time PDMP track: flow, event
rate/kernel, nonexplosion, reflection algebra, generator cancellation, then
refreshment and ergodicity. An executable event simulator needs explicit
integrated-hazard or thinning certificates. Do not encode BPS as a
discrete-time reversible kernel. The concrete one-dimensional unit-speed
standard-Gaussian client is now the completed exception: its exact path,
nonexplosion, and target stationarity transfer from the formally identified
Gaussian Zig-Zag construction. General dimension, refreshment-driven
ergodicity, and convergence remain separate milestones.

[Deligiannidis, Bouchard-Côté, and Doucet
(2019)](https://doi.org/10.1214/18-AOS1714) prove exponential ergodicity under
tail/curvature conditions using a Lyapunov function involving the reverse
bounce intensity. Their quantitative proof restricts velocity to the unit
sphere, whereas this repository's exact refreshed client uses an unbounded
standard-Gaussian velocity law. The published Lyapunov estimate therefore
cannot be imported verbatim. The reusable next step is the combined
flow/bounce plus refresh generator, followed by a Gaussian-velocity-specific
drift calculation or an explicitly proved comparison theorem.

[Durmus, Guillin, and Monmarché
(2020)](https://arxiv.org/abs/1807.05401) supply the directly relevant
unbounded-velocity result that the earlier audit omitted. Their Theorem 4
allows velocity laws with a Gaussian moment and proves geometric ergodicity
using a nonlinear carrier of the form
`exp(κ Ū(x)) φ(scaled radial velocity) + exp(H(‖v‖))`; the bounded monotone
profile `φ` separates inward transport, outward bounce decrease, and refresh
averaging. For a Gaussian target this is the appropriate architecture, not a
bare quadratic generator drift. The repository now defines its smooth radial
specialization, proves measurability/finiteness, exact sign reversal of the
normalized radial velocity, the complete bounce-change identity, and outward
bounce decrease. Quantitative profile construction, refresh integration, and
the generator drift inequality remain to instantiate.

### Bierkens, Fearnhead, and Roberts (2019): Zig-Zag -- P2

[Bierkens, Fearnhead, and Roberts](https://doi.org/10.1214/18-AOS1715) define a
nonreversible PDMP with coordinate velocity flips. A skew rate identity gives
the stationary target-times-uniform-velocity law. Exact subsampling uses
unbiased factor rates and valid Poisson-thinning bounds; the advertised
super-efficiency is an asymptotic heuristic under favorable control variates,
not a finite-sample mixing theorem.

**Repository fit.** Share PDMP construction and thinning infrastructure with
BPS, then formalize the flip-rate generator identity and a factorized-rate
specialization. Keep invariance, uniqueness, convergence, time-average
estimation, and computational scaling as distinct claims. A stationary
generator identity is the sensible first milestone for general targets. For
the one-dimensional standard-Gaussian client, the repository now goes further:
a regenerative suspension proof establishes target stationarity of the actual
exact stopped kernel at every nonnegative horizon. Its semigroup law and
convergence are not claimed.

### Jacob, O'Leary, and Atchadé (2020): unbiased coupled MCMC -- P0

[Jacob, O'Leary, and Atchadé](https://doi.org/10.1111/rssb.12336) combine a
faithful lag-one coupling, a meeting-time tail, marginal expectation
convergence, and moment assumptions to make a telescoping estimator unbiased
with finite expected cost and variance. Correct marginals alone do not suffice,
and unbiasedness does not itself prove that either marginal chain converges.

**Repository fit.** This is the grounding estimator layer beneath Xu et al.
(2021). The repository already covers much of the lagged path, meeting-tail,
telescoping, integrability, unbiasedness, and variance structure. Remaining
paper-level gaps include the averaged/tapered estimator, signed empirical
measure results, and a generic drift/small-set route. Concrete marginal
convergence for current targets is higher priority than duplicating the
existing core.

## Parallel evaluation of a chain

### Zoltowski et al. (2025): parallelizing across sequence length -- P3

[Zoltowski, Wu, Gonzalez, Kozachkov, and Linderman](https://arxiv.org/abs/2508.18413)
condition on all random inputs, write the MCMC state sequence as the solution
of a causal nonlinear recurrence, and use parallel Newton/DEER scans to solve
for the path. They demonstrate coordinate Gibbs, MALA, and fixed-step,
fixed-length HMC, and introduce diagonal/block quasi-Newton and sliding-window
variants to reduce memory and work.

At full nonlinear-solver convergence, the claim is pathwise reproduction of
the seeded sequential trace, not a new invariant distribution or MCMC
convergence result. Exact-arithmetic causal prefix progress gives an upper
bound of the sequence length in outer iterations, but practical speedup
requires far fewer iterations. Numerical tolerance, approximate Jacobians,
finite precision, and especially early stopping need separate analysis; an
early-stopped trace has no general exactness or stationarity guarantee. NUTS
and other dynamic-control-flow samplers are outside the paper's construction.

**Repository fit.** After deterministic seeded semantics exist for the desired
Gibbs/MALA/fixed-HMC transition, formalize an algorithm-independent causal
recurrence theorem: correctness of affine associative scans, uniqueness of the
path, prefix progress, and at-most-`T` exact-arithmetic termination for a
defined surrogate-Jacobian update. Then prove that a converged parallel
evaluator refines the sequential trace. Julia Reference can remain sequential
while Optimized implements the scan, with exact/random-trace differential
tests. Tolerance-based termination and early stopping must remain explicit
numeric/bias obligations. The paper depends on the parallel nonlinear
recurrence method of [Gonzalez et al. (2024)](https://arxiv.org/abs/2407.19115),
which should be reviewed in detail before this milestone is planned.

## Resulting roadmap

The integrated ordering, including an audit of combinators already present in
the repository and coordination with the two paper targets, lives in the
[overall project roadmap](project-roadmap.md). The list below is the literature
review's dependency recommendation rather than a claim that every first-layer
lemma is absent today.

The smallest coherent expansion is:

1. add invariant-kernel composition, mixtures, coordinate lifts, product
   targets, and stationary-marginal lemmas;
2. instantiate them with finite Gibbs scans and parallel tempering;
3. add finite pseudo-marginal MH as the canonical extended-state theorem;
4. complete the general-state kernel bridge and use MALA or independence-MH
   minorization as its first nontrivial client;
5. isolate the NUTS finite candidate-tree proof on top of existing HMC;
6. choose one separate breadth branch: particle MCMC, adaptive MCMC,
   trans-dimensional MH, slice sampling, or PDMPs; and
7. treat sequence-parallel evaluation as a refinement/execution project only
   after the corresponding sequential sampler has exact trace semantics.

This ordering grows reusable proof infrastructure while retaining the
repository's existing distinction between kernel validity, stationarity,
convergence, estimator correctness, and executable numerical refinement.
