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
3. generated executable finite MH, RWMH, endpoint HMC, and unit/constant-metric
   multinomial HMC, with explicit numerical-refinement boundaries.

Several combinators requested by the literature review already exist in
specialized or general form: kernel composition through mathlib, invariant
mixtures in `Mcmc.Kernel.Coupling`, product/lift/project machinery, coupling
marginals, and finite/infinite path semantics. The next foundation step is
therefore consolidation plus missing APIs, not a parallel replacement.

## Track A: reusable sampler foundations

### A1. Consolidate kernel combinators and add finite Gibbs

This is the next recommended milestone.

- inventory and publicly re-export existing composition, mixture, product,
  mapping, and stationary-marginal theorems;
- add only missing coordinate-lift and deterministic/random scan lemmas;
- define finite product-state conditional laws, one-site/block Gibbs kernels,
  random scans, and systematic scans; and
- prove target invariance, while keeping irreducibility and convergence as
  separate optional theorems.

This supplies shared language for tempering, adaptation, particle methods,
and coupled multi-kernel algorithms.

### A2. Parallel tempering

Use coordinate-lifted invariant kernels and ordinary MH transposition moves to
prove invariance of the product-temperature target and identify the cold
stationary marginal. Do not claim swaps improve mixing without an additional
quantitative theorem.

### A3. Finite pseudo-marginal MH

Formalize a nonnegative unbiased estimator on a finite auxiliary space, the
extended target, its desired marginal, and an MH transition that retains the
current estimator. Include zero estimator values. Keep MCWM, which refreshes
both estimates and is generally biased, explicitly separate.

### A4. First general-state convergence and proposal clients

Add bounded-weight independence-MH minorization as a compact quantitative
convergence result. Then define the state-dependent Gaussian proposal and
obtain MALA correctness from general MH, keeping fixed-step ULA separate and
not target-exact.

## Track B: paper-target execution

### B1. Executable Xu et al. (2021) coupling

Add generated shared-randomness commands for coupled multinomial HMC, sticky
Gaussian RWMH, and their mixture. Prove both executable marginals equal the
verified single-chain kernels and expose replay-level meeting events. This can
follow A1 so it uses the consolidated composition API.

### B2. Executable Xu and Ge (2024) sampler

Implement the corrected radial/spherical momentum construction,
inverse-factor transport, and nonseparable multinomial transition. Approximate
implicit solves must return residual or integrator certificates consumed by
the existing conditional theorem; a fixed iteration count is insufficient.

## Track C: later breadth branches

After A1--A4 and the paper execution milestones, select branches based on
research value and shared infrastructure:

- NUTS finite candidate trees before adaptation or modern multinomial NUTS;
- slice sampling via lift--update--project;
- reversible-jump MCMC after tagged-space change of variables;
- particle MCMC after finite SMC and pseudo-marginal foundations;
- adaptive MCMC only with explicit nonhomogeneous-chain semantics,
  diminishing adaptation, and containment; and
- BPS/Zig-Zag only in a separate continuous-time PDMP architecture.

Sequence-parallel evaluation is an execution-refinement project downstream of
exact seeded trace semantics. Full solver convergence may refine a sequential
trace; numerical tolerance and early stopping remain separate bias
obligations.

## Immediate plan

The selected next milestone is **A1: combinator consolidation and finite
Gibbs**. Its completion criteria are:

1. one documented public module surface for reusable kernel combinators;
2. no duplicate theorem when mathlib or an existing `Mcmc` module suffices;
3. finite one-site/block, random-scan, and systematic-scan Gibbs kernels;
4. exact invariance proofs and at least one concrete product target; and
5. documentation that does not infer convergence from invariance.

Then proceed to A2 and A3, followed by B1. A4 can develop alongside B1 when it
does not destabilize the executable artifact.
