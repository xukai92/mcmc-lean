# Parallel HMC integrator audit

## Scope and conclusion

This audit asks a narrow question: which numerical-integration techniques can
use parallel hardware **across HMC trajectory time**, rather than merely across
chains, coordinates, or likelihood terms? It surveys representative primary
sources through 28 August 2026. It is an architecture review, not an exhaustive
bibliography or a novelty claim.

The short conclusion is:

- parallel evaluation of nonlinear recurrences is the closest demonstrated
  route to parallel leapfrog and already includes HMC experiments;
- stage-parallel Gauss--Legendre integration has the cleanest geometric method
  underneath it, but solving its implicit stages only approximately creates an
  implementation-level correctness obligation;
- Parareal, PFASST, MGRIT, SDC, RIDC, and multiple shooting provide useful
  numerical templates, but ordinary finite iterates are not automatically
  reversible and volume preserving HMC proposals;
- affine recurrences admit exact associative scans and are the best restricted
  formal and implementation baseline; and
- force, target, coordinate, and chain parallelism should remain strong
  baselines, but they do not remove the dependency between successive general
  nonlinear trajectory states.

No surveyed source establishes the particular end-to-end result this project
would need: an accelerator implementation of a general nonlinear trajectory
solver whose **finite returned map**, including stopping and failure behavior,
is connected to a machine-checked HMC invariance theorem. That is a
search-scoped negative finding, not a claim that no such work exists.

## The HMC validity gate

For the standard deterministic-proposal proof used in HMC, let `R(q,p)=(q,-p)`
be momentum reversal and let `Phi` be the actually returned trajectory map. A
simple sufficient interface is:

```text
Phi^-1 = R o Phi o R                 reversibility
Phi preserves phase-space volume    unit Jacobian in Euclidean coordinates
alpha(z) = min(1, exp(-H(Phi(z)) + H(z)))
```

Symplectic maps supply volume preservation, but approximate energy conservation
alone supplies neither property. A more general invertible proposal can use a
Jacobian correction, but then the reverse map and determinant must be available
and its implemented failure cases must also be covered.

Three objects must not be conflated:

1. the mathematical collocation or fixed-point solution;
2. a finite number of nonlinear-solver or time-parallel iterations; and
3. the floating-point program, including convergence tests and fallbacks.

An iteration that converges to leapfrog need not itself be a reversible,
volume-preserving map before convergence. Likewise, stopping when a forward
residual is small can choose a different iteration count on the reversed path.
An MH energy correction cannot repair an unknown proposal-density or Jacobian
error.

The existing formal library already has the right destination interfaces:
`Mcmc.Hamiltonian.Leapfrog` proves momentum-flip reversibility for finite
leapfrog iterates, while `Mcmc.Hamiltonian.VolumePreservation` proves exact
phase-volume preservation. A parallel candidate should discharge analogous
obligations rather than only match a serial trajectory numerically.

## Taxonomy

The ODE literature distinguishes several independent axes of parallelism:

```text
across system       independent components, force terms, spatial domain
across method       stages or quadrature nodes inside one time step
across steps        several trajectory-time intervals concurrently
across iterations   batched residual/Jacobian work in a global solve
across chains       independent or coupled MCMC transitions
```

Only the middle three can shorten the critical path of one otherwise serial
trajectory. Their concurrency can multiply with batched force evaluation and
chain parallelism, so all comparisons must include those simpler baselines.

## Comparison matrix

`Exact finite map?` below means exact with respect to the mathematical method,
not bitwise real arithmetic. `Conditional` means that a converged implicit
system or an additional symmetric construction is required.

| Family | Parallel unit | Available concurrency | Extra work / memory | Geometric status | Exact finite-map HMC status | Assessment |
|---|---|---:|---|---|---|---|
| Affine associative scan | trajectory steps | up to path length, logarithmic reduction depth | linear work and stored summaries | inherits the composed affine maps | yes for exactly represented reversible, volume-preserving factors | best restricted baseline; quadratic targets or frozen linearizations |
| Nonlinear recurrence / quasi-DEER | all trajectory states | up to path length | repeated global passes; block variant has path-by-state storage | limit can equal serial leapfrog | not from residual convergence alone | best immediate general experiment; add exact trace verification and fallback |
| Multiple shooting / Newton | time subintervals | number of shooting intervals | interface unknowns, repeated subsolves | depends on converged subpropagators | conditional; stopped nonlinear solve is the issue | conceptual parent of recurrence solvers; useful correctness model |
| Parareal | time subintervals | number of intervals in fine sweep | coarse serial correction plus repeated fine solves | ordinary Parareal is not symplectic | generally no at a finite early iterate | useful predictor/fallback research, not first verified proposal |
| Symmetric/projected Parareal | time subintervals | number of intervals | more solves and projection/symmetrization | improves symmetry and long-time behavior | symmetry is promising; volume and finite solver semantics still need proof | research candidate after simpler methods |
| MGRIT | multilevel time grid | many time points | hierarchy, relaxation, restriction/prolongation | generic wrapper does not preserve Hamiltonian structure automatically | generally no before exact convergence | strongest for suitable evolution/PDE structure, risky for oscillatory HMC |
| PFASST | time slices and collocation nodes | both slice and node levels | multilevel SDC state and communication | collocation choice may be geometric; PFASST iteration need not be | conditional on solved collocation system | high concurrency, high implementation/proof complexity |
| Parallel SDC / iterated RK | collocation nodes | number of nodes, possibly also steps | several correction sweeps | limit inherits collocation method; sweeps need not | generally no for a fixed incomplete sweep count | valuable solver component, not by itself an HMC proposal theorem |
| RIDC | correction levels over staggered steps | method order / correction levels | pipeline startup and history | not symplectic or reversible by default | generally no | modest concurrency; low priority for HMC |
| Stage-parallel Gauss--Legendre IRK | stages in one step | number of stages | implicit stage solve and dense coupling | mathematical method is symmetric and symplectic | conditional on exact/symmetry-preserving solve | cleanest by-design geometric candidate; modest parallel width |
| Force splitting / multiple time scales | force components and subflows | model dependent | extra substeps and scheduling | symmetric compositions can be reversible and symplectic | yes when every subflow/composition is exact as specified | practical complementary direction, not generic across-step parallelism |
| Batched targets / chains | observations, particles, chains | workload dependent | batching buffers | leaves the integrator unchanged | inherits existing proof | mandatory performance baseline |

Parallel depth alone is misleading. A method can have logarithmic or
iteration-count depth but lose in wall time through redundant gradients,
global synchronization, memory traffic, or a cheap serial force function.

## Family-by-family findings

### Nonlinear recurrence solvers

Zoltowski et al. formulate a full state sequence as a nonlinear fixed-point
problem and apply parallel Newton-style methods. Their block quasi-DEER method
reduces memory and runtime relative to a dense formulation, and their reported
applications include Gibbs, MALA, and HMC. The paper demonstrates substantial
parallel depth reduction and empirical agreement with sequential chains.

For this repository, the important gap is not whether the iteration approaches
serial leapfrog. It is what transition is produced after the practical finite
stopping rule. A conservative route is:

```text
parallel candidate trajectory
        |
parallel verification of every serial recurrence edge
        |
exact match ----------------------> accept candidate trace
failure / mismatch ---------------> run deterministic serial fallback
```

This does not make an approximate trace valid. It uses parallel work as a
speculation that must reproduce the already-proved discrete map. Verification
must cover the arithmetic semantics desired by the runtime; tolerance-based
closeness is insufficient for an exact replay claim.

### Multiple shooting and Parareal

Multiple shooting exposes subinterval boundary values and solves their matching
conditions globally. Parareal is a predictor-corrector realization with a cheap
coarse serial propagator and concurrently evaluated fine propagators. These are
natural templates for treating all leapfrog states as unknowns.

Hamiltonian-specific studies are cautionary. Ordinary Parareal is not
symplectic even when its component propagators are, and convergence over long
Hamiltonian windows can be restricted. Symmetrization and projection variants
improve time symmetry and long-time behavior, but those properties do not
automatically prove that each finitely stopped map preserves phase volume.
Consequently, a symmetric Parareal experiment belongs after an exact replay
baseline, with its finite iteration count included in the state or made
reversal invariant by construction.

### MGRIT and PFASST

MGRIT applies multigrid reduction along the time dimension and can wrap an
existing stepper. PFASST combines time slices, multilevel correction, and SDC
collocation nodes. Both target far more concurrency than stage-level methods,
especially when spatial parallelism is saturated.

Their genericity is precisely the HMC problem: using a symplectic fine stepper
does not imply that an incomplete multilevel correction cycle is symplectic.
The hierarchy also introduces restriction, interpolation, coarse operators,
and data-dependent convergence decisions that need reverse semantics. MGRIT
convergence is known to be problem dependent and is harder for hyperbolic or
oscillatory behavior than for diffusion-like problems. These families are
therefore valuable sources of preconditioners and schedules, but not initial
verification targets.

### SDC, RIDC, and stage-parallel collocation

Parallel SDC uses diagonal or otherwise parallel preconditioners so collocation
nodes update simultaneously. Modern variants can provide competitive
small-scale parallelism, but efficiency depends strongly on the preconditioner
and sweep count. RIDC pipelines deferred-correction levels across nearby steps.

The fixed point of an SDC solve can be a Gauss collocation method; a fixed set
of incomplete sweeps is a different map. This suggests separating the method
from its solver. Gauss--Legendre implicit Runge--Kutta is symmetric and
symplectic as a mathematical method, and recent work shows that simultaneous
stage evaluation can exploit CPU SIMD effectively. It is the most attractive
geometry-first candidate when force evaluations are expensive enough to repay
the implicit solve. The research obligation is a solve procedure with exact
reversal semantics, or a proof for the finite iteration map actually used.

### Associative scans

For an affine recurrence

```text
x[i+1] = A[i] * x[i] + b[i],
```

each segment is summarized by `(A,b)`, with associative composition

```text
(A2,b2) o (A1,b1) = (A2*A1, A2*b1+b2).
```

A prefix scan then has linear total work and logarithmic ideal depth. Quadratic
Hamiltonians make leapfrog linear, so this yields an exact restricted parallel
trajectory and a clean theorem target. General nonlinear HMC only gets this
structure after linearization, at which point correction or exact replay is
needed. The restricted result is still important: it measures scan overhead,
tests accelerator plumbing, and isolates numerical from probabilistic issues.

### Model-structured parallelism

Splitting a Hamiltonian into exactly solvable pieces and composing them
symmetrically preserves a direct geometric proof. Multiple-time-scale HMC is a
well-established example. Independent force terms, observations, sparse
blocks, Hessian-vector probes, and coupled-chain forces may also be batched.
These optimizations can dominate on expensive models and combine with every
time-parallel family above. They should not be described as solving the general
across-leapfrog dependency, however.

## Recommended experimental order

### 1. Exact affine-scan baseline

Formalize composition of affine phase maps, prove scan/sequential equivalence,
and instantiate it for quadratic leapfrog. Implement CPU threaded and
accelerator-oriented scans. This is a bounded way to test whether trajectory
parallelism can beat optimized sequential stepping at all.

### 2. Quasi-DEER with exact replay certificate

Reproduce the general nonlinear approach, but make validity inherit from the
existing leapfrog theorem: verify the returned recurrence trace and fall back
to serial replay on any mismatch. Record iteration count, residual, verification
cost, fallback rate, total gradients, memory, and synchronization.

This version can be exact relative to the declared executable recurrence even
when the speculative solver is not independently proved. A later theorem can
replace replay with direct finite-iteration reasoning if worthwhile.

### 3. Stage-parallel Gauss--Legendre prototype

Implement a small even-stage method with a fixed, reversal-compatible solve
schedule. Separate tests for the ideal collocation map from tests of the finite
solver. Measure against leapfrog at matched acceptance and effective samples,
not at matched nominal step count.

### 4. Geometric time-parallel exploration

Only after the baselines, study symmetric/projected Parareal or PFASST with a
Gauss collocation fine problem. Before sampler benchmarking, derive the exact
finite-map reverse operation and either prove volume preservation or expose a
tractable Jacobian correction.

## Evaluation protocol

Every experiment should compare:

- optimized serial leapfrog;
- vectorized or batched force evaluation;
- several independent chains using the same processor budget;
- the proposed trajectory-parallel method; and
- where relevant, the same method with its verification/fallback disabled,
  clearly labeled as a numerical diagnostic rather than a valid sampler.

Report both sampler and systems quantities:

| Sampler evidence | Systems evidence | Correctness diagnostics |
|---|---|---|
| acceptance and movement | wall time and speedup | forward/reverse replay mismatch |
| bulk/tail ESS per second | gradient and target calls | recurrence-certificate failures |
| ESS per gradient | parallel depth and occupancy | empirical Jacobian/volume checks |
| divergences and energy error | synchronization and memory | fallback rate and failure path |

Empirical reversibility and Jacobian checks catch implementation bugs; they do
not replace proofs. Targets should range from quadratic controls through
expensive logistic/item-response models to funnels or hierarchical geometries.
Longer trajectories favor time parallelism, so results must show the selected
path length rather than hiding it in aggregate throughput.

## Decision

The parallel-integrator direction is not “done.” One strong general prototype
exists in the literature, and mature ODE families supply many components, but
none can simply replace leapfrog in the verified sampler pipeline. The best
project sequence is therefore:

```text
exact affine scan
    -> speculative nonlinear solve + exact recurrence certificate
    -> geometry-first stage-parallel implicit method
    -> multilevel geometric time-parallel methods only if measurements justify it
```

This order maximizes learning while keeping the invariant distribution tied to
an explicit finite computation.

## Implementation checkpoint (August 2026)

The first implementation pass now supplies:

- `Mcmc.Hamiltonian.ParallelIntegrators`, with machine-checked affine
  composition associativity and an edge-valid-trace theorem equating a
  speculative trajectory endpoint with serial iteration;
- Reference and Optimized Julia affine scans and exact replay gates;
- `Mcmc.Hamiltonian.GaussLegendre`, with the two-stage coefficients, a proof of
  the Runge--Kutta symplectic coefficient equations, and a proof that reversing
  an exact step swaps its stages and returns to the initial state;
- a versioned `vector_gauss_legendre_hmc_step!` program in the Lean-emitted IR;
  and
- allocation-transparent Reference plus generic serial and threaded Optimized
  Julia interpretations, parity tests, reverse-step diagnostics, and benchmark
  harness rows.

The public Julia surface is `GaussLegendreHMC`. For example:

```julia
using Random, VerifiedSamplers

logdensity(q) = -sum(abs2, q) / 2
gradient(q) = q

reference = GaussLegendreHMC(logdensity, gradient, 0.08, 10;
    stage_iterations=8)
threaded = GaussLegendreHMC(logdensity, gradient, 0.08, 10;
    stage_iterations=8, backend=:optimized, parallel=true)

reference_draws = sample(MersenneTwister(1), reference, zeros(100), 1_000)
threaded_draws = sample(MersenneTwister(1), threaded, zeros(100), 1_000)
```

Launch Julia with at least two threads for the second sampler.

For cheap gradients, the preferred spatial path is instead an explicit
two-column callback `batched_gradient!(output, positions)`, passed as the
`batched_gradient!` keyword with `backend=:optimized`. It evaluates both
Runge--Kutta stages as one batch and uses SIMD loops for the stage algebra.
Arbitrary scalar gradient callbacks retain the serial fallback because Julia
cannot soundly infer that they admit cross-stage vectorization.

The theorem boundary remains deliberate. Lean proves reversal of an **exact
stage witness** and the coefficient condition; the emitted executable uses a
declared finite fixed-point iteration count. A residual tolerance is not an
exact-stage witness. Consequently the current benchmark is numerical evidence
for the finite solver, not yet an invariance theorem for that finite solver.
Closing this gap requires either exact stage certification with fallback or a
direct proof about a reversal-compatible finite iteration map. Likewise, the
standard theorem taking the symplectic Runge--Kutta coefficient condition to
phase-volume preservation has not yet been developed in the local formal
library.

The initial two-thread, 100-dimensional development benchmark used 100 draws,
two seeds, ten integration steps, step size `0.08`, and eight stage iterations.
Median transitions per second were:

| Target | Leapfrog optimized | GL2 Reference | GL2 serial | GL2 threaded | GL2 SIMD/batched |
|---|---:|---:|---:|---:|---:|
| isotropic Gaussian | 153,931 | 1,079 | 3,665 | 1,008 | 38,090 |
| correlated Gaussian | 105,937 | 1,011 | 2,907 | 1,007 | 21,019 |
| product quartic | 99,153 | 982 | 2,762 | 989 | 18,053 |
| ill-conditioned Gaussian | 102,036 | 972 | 2,746 | 1,003 | 19,653 |
| regularized logistic | 46,391 | 796 | 2,071 | 946 | 6,717 |

The threaded path remains slower because these cheap targets do not amortize
task scheduling. The batched path is much faster even though this benchmark
merely adapts the ordinary target callbacks: its direct SIMD loops also remove
the concatenations and temporary vectors in the initial prototype. A genuinely
fused model callback provides further potential; the table must not be read as
isolating SIMD instruction effects. Ordinary leapfrog remains faster, and the
finite-stage correctness gate still precedes full benchmark evidence.

## Primary sources

- Zoltowski et al., [Parallelizing MCMC Across the Sequence
  Length](https://proceedings.neurips.cc/paper_files/paper/2025/hash/202886ee1c9ca735cb5bff3a00a69883-Abstract-Conference.html),
  NeurIPS 2025.
- Gander, [50 Years of Time Parallel Time
  Integration](https://archive-ouverte.unige.ch/unige:170025), 2015.
- Lions, Maday, and Turinici, [A "parareal" in time discretization of PDE's](https://doi.org/10.1016/S0764-4442(00)01793-6),
  2001.
- Dai, Le Bris, Legoll, and Maday, [Symmetric parareal algorithms for
  Hamiltonian systems](https://www.numdam.org/item/M2AN_2013__47_3_717_0/),
  2013.
- Gander and Hairer, [Analysis for parareal algorithms applied to Hamiltonian
  differential equations](https://doi.org/10.1016/j.cam.2013.01.011), 2014.
- Falgout et al., [Parallel time integration with
  multigrid](https://www.math.mun.ca/smaclachlan/research/mgrit.pdf), 2014.
- Emmett and Minion, [Toward an Efficient Parallel in Time Method for Partial
  Differential Equations](https://doi.org/10.2140/camcos.2012.7.105), 2012.
- Christlieb et al., [Revisionist integral deferred correction with adaptive
  step-size control](https://doi.org/10.2140/camcos.2015.10.1), 2015.
- Speck, [Parallelizing spectral deferred corrections across the
  method](https://arxiv.org/abs/1703.08079), 2018.
- Caklovic et al., [Improving Efficiency of Parallel Across the Method
  Spectral Deferred Corrections](https://doi.org/10.1137/24M1649800), 2025.
- Antonana, Makazaga, and Murua, [SIMD-vectorized implicit symplectic
  integrators can outperform explicit symplectic
  ones](https://doi.org/10.1007/s11075-026-02370-3), 2026.
