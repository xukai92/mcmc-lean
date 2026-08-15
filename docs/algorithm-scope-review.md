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
Next add a nontrivial Euclidean birth/death transport and prove its
change-of-variables density rather than assuming a Jacobian factor.

### Roberts and Rosenthal (2007): adaptive MCMC -- P2

[Roberts and Rosenthal](https://doi.org/10.1239/jap/1183667414) prove marginal
total-variation convergence under Diminishing Adaptation plus either
Simultaneous Uniform Ergodicity or Containment. Their counterexamples show that
even when every frozen kernel is invariant and ergodic, state-dependent
adaptation can destroy convergence. Their main assumptions do not imply a
strong LLN or CLT.

**Repository fit.** Start with finite adaptation and a small counterexample.
Later define history-dependent kernel selection, kernel total variation,
diminishing adaptation, mixing times, and containment, then formalize the
finite-window coupling argument. Production warmup should be described as an
inhomogeneous phase followed by a frozen proved kernel.

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
are now machine checked as well. The next SMC obligation is the multi-time
product normalizing-constant estimator and explicit ancestry law before naming
a PIMH/PMMH client.
Conditional SMC and particle Gibbs follow. Keep fixed-particle stationarity,
chain convergence, and consistency as particle count grows as separate theorem
families.

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
Lebesgue-under-the-graph joint identity are also machine checked. The next
obligation is a measurable horizontal level-set conditional, first under
finite positive slice-mass assumptions. Stepping-out/shrinkage and doubling
are subsequent trace-reversal
targets. Crumb, reflective, and multivariate variants can wait. This completed
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
discrete-time reversible kernel.

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
generator identity is the sensible first milestone.

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
