# Proposal: executable MCMC refinement and Julia code generation

## Status and purpose

This document proposes an executable layer for `verified-samplers`. The existing
library defines MCMC algorithms as mathematical `ProbabilityTheory.Kernel`
objects and proves properties such as kernel validity, reversibility,
invariance, coupling marginals, and meeting-time bounds.  Many of those
definitions are intentionally noncomputable.  The proposed layer would connect
selected mathematical kernels to executable programs and generate a clear
reference implementation in Julia.

The project should start from a small, auditable implementation rather than
using AdvancedHMC.jl as its implementation.  AdvancedHMC.jl is useful as an
API reference, performance comparison, and independent differential-testing
target.  It is not part of the verified core.

This proposal does not claim that code generation alone verifies Julia code.
It separates machine-checked results, trusted runtime assumptions, and tested
optimizations so that each resulting claim has a precise boundary.

## Goals

1. Define executable MCMC programs in Lean without attempting to execute
   arbitrary mathlib measures or kernels.
2. Give each executable program a mathematical semantics as a
   `ProbabilityTheory.Kernel` when an exact semantics is available.
3. Prove that selected executable programs refine the mathematical kernels
   already defined in the `formal/Mcmc` library.
4. Generate a simple Julia reference implementation from those programs.
5. Make randomness explicit so executions can be reproduced and compared.
6. Permit separately maintained, high-performance implementations to be
   tested against the generated reference.
7. Keep the executable intermediate representation independent of Julia so a
   Rust or other backend can be added later.

## Non-goals

- Translating arbitrary elaborated Lean expressions to Julia.
- Making `Measure` or `ProbabilityTheory.Kernel` computable in general.
- Verifying the Julia compiler, runtime, BLAS, or random-number generator.
- Initially proving end-to-end floating-point error bounds for HMC.
- Treating invariance as convergence from arbitrary initial states.
- Reimplementing the complete feature set of AdvancedHMC.jl.
- Calling a statistically tested optimized implementation formally verified.

## Proposed assurance levels

Artifacts should be described using three distinct levels.

### 1. Verified mathematical kernel

Lean proves properties of a mathematical kernel.  Depending on the theorem,
these may include that it is Markov, reversible, invariant, or has specified
coupling marginals.  These properties retain their current meanings and do not
imply convergence unless the required hypotheses and mode of convergence are
also present.

### 2. Generated executable reference

Lean proves that an executable DSL program has the intended kernel semantics,
or proves a stated approximation relation.  A small compiler emits Julia.  The
claim is conditional on the compiler and documented Julia primitives
implementing their specifications.

The intended description is "generated from a Lean-verified executable MCMC
program under explicit runtime assumptions," rather than an unconditional
claim that the Julia toolchain is verified.

### 3. Tested optimized implementation

An optimized Julia implementation is compared with the generated reference by
deterministic trace replay, property-based tests, numerical comparisons, and
statistical tests.  It may use mutation, preallocated workspaces, BLAS, GPU
arrays, or specialized package routines.  This provides strong conformance
evidence but not a formal equivalence proof.

An optimized implementation can later be promoted to level 2 by representing
it in the executable DSL or proving a refinement theorem for it.

## Architecture

```text
Existing mathematical layer
ProbabilityTheory.Kernel State State
  - Markov property
  - reversibility and invariance
  - coupling marginals and meeting results
                    ^
                    | Lean refinement theorem
                    |
Executable MCMC DSL and typed IR
  - deterministic numerical computations
  - primitive random draws
  - sequencing, branching, and bounded iteration
  - MCMC-specific combinators
                    |
                    +------ exact kernel semantics
                    |
                    +------ Julia reference backend
                    |          |
                    |          +-- deterministic trace mode
                    |          +-- production RNG mode
                    |
                    +------ future Rust/backend support

Optimized Julia implementation / AdvancedHMC.jl
                    ^
                    | differential and statistical testing
`VerifiedSamplers.Reference` compiler-emitted Julia submodule
```

The critical proof boundary is between the executable DSL and the mathematical
kernel.  Julia syntax generation is deliberately a separate concern.

## Executable language

The executable layer should be a shallow or deeply embedded DSL whose terms
contain only supported computational operations.  Unsupported operations must
be rejected explicitly; they must not silently become trusted Julia calls.

An initial language should support:

- scalar booleans, naturals, integers, and floating-point values;
- fixed-shape or dynamically sized vectors with an explicit element type;
- tuples and small records used for chain and phase-space state;
- pure computations, `let` bindings, conditionals, and finite loops;
- explicit failure for invalid parameters or numerical failures;
- scalar and vector arithmetic;
- potential and gradient evaluation through declared interfaces;
- uniform, standard-normal, Bernoulli, and finite-categorical draws;
- momentum refreshment;
- leapfrog steps and finite trajectory construction;
- endpoint or multinomial selection and accept/reject decisions; and
- coupled draws needed by the existing coupled-kernel developments.

The IR should distinguish mathematical reals from machine `Float64`.  Mapping
a mathematical real directly to `Float64` without an explicit refinement
boundary should be forbidden.

Proof arguments and measurability witnesses belong to the mathematical layer
and should normally be erased before code generation.  Runtime-relevant
preconditions, such as positive step sizes and dimension agreement, should
become checked inputs or construction invariants.

## Semantics and refinement

The primary semantic function should be language-independent.  Schematically:

```lean
def ExecKernel.denote (program : ExecKernel State) :
    ProbabilityTheory.Kernel State State
```

The first useful theorem targets should connect small executable components to
existing definitions:

```text
denote Gaussian random-walk proposal = mathematical Gaussian proposal kernel
denote MH accept/reject              = density Metropolis--Hastings kernel
denote position--momentum lift       = mathematical lift kernel
denote momentum refresh              = mathematical phase refresh kernel
denote exact-arithmetic leapfrog HMC = selected mathematical HMC kernel
```

Component theorems are preferable to one monolithic compiler theorem.  They
allow metrics, integrators, trajectory builders, selection rules, and
adaptation procedures to have separate specifications and proof obligations.

Exact equality is appropriate only when the executable primitives and numeric
model support it.  A `Float64` implementation of leapfrog is not literally the
same map as a real-valued leapfrog definition.  Floating-point work therefore
needs a separate relation, for example a deterministic state-error bound or a
distance between transition kernels.  The first milestone may leave that
relation as future work while proving the control-flow and exact-arithmetic
reference.

## Trusted Julia primitive boundary

The first version may assume a small allowlist of low-level Julia facilities is
correct relative to declared specifications.  Likely examples include:

- an explicit `AbstractRNG` implementation;
- `rand` for uniform values and `randn` for standard normal values;
- selected routines from `Random`, `LinearAlgebra`, and a named BLAS backend;
- a selected finite-categorical sampling routine;
- optionally, a named automatic-differentiation package and interface.

Every trusted primitive should have:

1. a Lean-side mathematical or operational specification;
2. an exact Julia symbol and supported version range;
3. documented parameter and failure behavior;
4. tests for important edge cases; and
5. a record of whether the assumption concerns exact values, floating-point
   behavior, or only a distributional law.

For example, the contract for `randn(rng)` is distributional, while a vector
addition contract concerns floating-point values and aliasing behavior.  These
should not be conflated.

Dependencies outside the allowlist must fail code generation.  This keeps the
trusted computing base visible even if it is not initially small.

## Randomness and deterministic replay

All generated functions should receive a random source explicitly.  No
generated program should depend on Julia's hidden global RNG state.

The runtime should provide at least two sources:

1. a production source backed by a Julia `AbstractRNG`; and
2. a trace source that returns predetermined draws and records their use.

A trace should record the primitive kind, parameters where relevant, returned
value, and position in the stream.  Reference and optimized implementations
can then be run from the same trace.

Trace comparison should verify more than the final sample:

- the order and number of random draws;
- proposed states and momenta;
- trajectory endpoints and selection weights;
- accept/reject thresholds and decisions;
- termination decisions; and
- the final state and diagnostics.

This is stronger and more diagnostic than comparing empirical histograms.
For coupled kernels, the trace representation must also preserve which draws
are shared and which are independent.

## Julia reference backend

The repository layout fixes the backend boundary:

```text
formal/                                  Lean source of truth
VerifiedSamplers.jl/src/Reference/       compiler-emitted Julia submodule
VerifiedSamplers.jl/src/Optimized/       maintained Julia implementations
```

Reference generation is an explicit development and release action exposed as
`make generate`; it is not a side effect of `lake build`, Julia package
installation, or ordinary tests. Emitted reference sources are committed so
Julia users do not need Lean. CI will regenerate into a temporary location and
reject stale committed output once the emitter exists.

The generated reference should prioritize readability and correspondence with
the DSL over peak speed.  Its expected properties are:

- explicit types where they make semantics or specialization clearer;
- explicit RNG/source arguments;
- straightforward loops and control flow;
- no reflection or run-time code generation;
- minimal mutation, with mutation permitted where it directly represents the
  DSL state;
- deterministic diagnostics and trace hooks; and
- a small runtime library with no dependency on AdvancedHMC.jl.

Reference code should still avoid pathologically slow choices.  A transparent
implementation can use preallocated vectors or in-place leapfrog updates if
those operations are represented directly in the DSL and tested independently.
"Reference" means semantically simple, not intentionally inefficient.

## Optimized implementations

Optimized implementations may be generated by a separate backend or written
by hand.  They may change data layout, fuse loops, reuse buffers, use BLAS,
specialize dimensions, parallelize chains, or target GPUs.

Testing should proceed in layers:

1. **Deterministic trace replay.** Compare intermediate and final results under
   the same supplied draws.
2. **Property-based differential testing.** Generate dimensions, valid
   parameters, initial states, potentials, and random traces, including edge
   cases.
3. **Floating-point comparison.** State tolerances per operation and record
   branch changes caused by small numerical differences.  A close numeric
   state is not sufficient when an accept/reject or categorical decision
   changes.
4. **Statistical testing.** Compare moments, acceptance rates, empirical
   distributions, autocorrelation summaries, and coupled meeting behavior.
5. **Benchmarking.** Measure allocations, compilation latency, transition
   throughput, gradient evaluations, and scaling with dimension and chain
   count.

Tests provide evidence, not proof.  Documentation and API names should retain
the distinction between a proved refinement and a tested optimization.

## Role of AdvancedHMC.jl

AdvancedHMC.jl should be treated only as related engineering work and an
external reference implementation.  Its modular decomposition into metrics,
Hamiltonians, integrators, trajectory samplers, termination criteria, kernels,
and adaptors is useful when designing interfaces.  The implementation itself
is not the source of semantics and should not be imported by the generated
reference runtime.

Possible uses are:

- compare public API decompositions;
- benchmark equivalent HMC configurations;
- run differential tests for shared algorithm variants;
- identify practical diagnostics and adaptation state that the DSL must make
  explicit; and
- test whether a verified configuration can be represented faithfully in a
  mature implementation.

A match with AdvancedHMC.jl is independent corroboration, not a verification
argument.  Differences must be classified rather than automatically treated
as defects: the algorithms, numerical conventions, or random-consumption order
may legitimately differ.

## Why Julia first, while retaining a language-neutral IR

Julia is the proposed first backend because it has mature numerical linear
algebra, random distributions, automatic differentiation, GPU support, and an
active MCMC ecosystem.  Its multiple-dispatch and parametric-type model also
fits the component structure of HMC and permits a readable reference to become
reasonably efficient through specialization.

Rust remains a plausible later production backend.  It offers strong memory
safety, predictable deployment, ahead-of-time compilation, and tighter control
over dependencies and allocation.  It also introduces ownership, borrowing,
trait, workspace, and numeric-generic decisions that are incidental to the
initial semantic problem, while its scientific-computing and automatic-
differentiation ecosystem is currently less integrated for this use case.

Neither language proves distributional correctness by itself.  The executable
IR and its Lean semantics should therefore not contain Julia-specific concepts
unless they are explicitly modeled runtime primitives.

## Adaptation and convergence boundaries

Warmup adaptation is a stateful stochastic algorithm and should not be hidden
inside a static HMC kernel configuration.  Step-size and mass-matrix adaptation
should eventually be represented as executable state transitions with their
own specifications.

Proving that a fixed post-warmup kernel preserves a target does not prove that
an adaptive chain is invariant or convergent.  Initial milestones should
therefore focus on fixed-parameter transitions.  Adaptation can be added after
its mathematical theorem boundary is chosen explicitly.

Likewise, an executable transition matching an invariant mathematical kernel
inherits only the properties proved for that kernel.  Invariance alone does
not imply convergence, mixing-rate guarantees, or unbiased finite-sample
estimation.

## Proposed milestones

### Milestone 0: design experiment

- Choose one finite-state MH example and one fixed-parameter Gaussian RWMH
  example.
- Prototype the minimum executable syntax and trace-source interface.
- Generate readable Julia and confirm deterministic replay.
- Record which primitives and numeric assumptions are required.

### Milestone 1: finite exact end-to-end slice

- Give the finite executable language exact PMF/kernel semantics.
- Implement finite categorical sampling through a declared primitive.
- Prove an executable finite MH step denotes the existing finite MH kernel or
  its measure-kernel embedding.
- Generate Julia and test all finite states and a bounded family of traces.

This milestone avoids floating-point and continuous-distribution issues while
testing the architecture end to end.

### Milestone 2: continuous RWMH reference

- Add real-vector state, a standard-normal primitive contract, and explicit
  target-density evaluation.
- Define the exact idealized semantics and an executable `Float64` boundary.
- Generate a fixed-parameter Gaussian RWMH reference implementation.
- Compare it with a small independent Julia implementation and, where
  configurations coincide, AdvancedHMC/AdvancedMH behavior.

### Milestone 3: fixed-trajectory HMC

- Add momentum refreshment, leapfrog, Hamiltonian evaluation, and endpoint
  acceptance.
- Prove component-level exact-arithmetic refinement results.
- Add trace-level comparisons for every leapfrog state and acceptance decision.
- Establish an explicit floating-point theorem statement or documented proof
  obligation rather than silently identifying real and `Float64` dynamics.

### Milestone 4: multinomial HMC and couplings

- Add finite trajectory-index distributions and multinomial selection.
- Connect the executable transition to the repository's multinomial-HMC
  kernel.
- Represent shared randomness and coupled categorical choices.
- Connect executable coupled transitions to the proved marginal kernels.

### Milestone 5: optimization and additional backends

- Establish benchmark suites and performance budgets.
- Add an optimized Julia backend or maintained optimized implementation.
- Evaluate an AdvancedHMC adapter solely as a tested external target.
- Reassess a Rust backend using the stable IR and the accumulated primitive
  contracts.

## Initial decisions to make

Before implementation, the project should settle these questions:

1. Is the first DSL deeply embedded, or a typed Lean API elaborated into a
   separate IR?
2. Does the exact semantic layer use probability kernels directly or first use
   a sampler monad with a proved kernel interpretation?
3. Which vector shapes and element types are admitted in the first version?
4. Is gradient evaluation generated from Lean, supplied as a trusted callback,
   or supported through both routes with distinct guarantees?
5. What is the exact random trace format, especially for vector Gaussian and
   coupled draws?
6. Which Julia versions, RNGs, numerical packages, and BLAS implementations
   form the initial trusted allowlist?
7. Which optimized transformations require exact trace agreement, and which
   are permitted to change floating-point evaluation or random-consumption
   order?

## Success criterion

The first convincing result is not a complete NUTS implementation.  It is a
small end-to-end example for which:

1. Lean proves an executable program denotes an existing mathematical MCMC
   kernel;
2. the program generates readable Julia using only documented trusted
   primitives;
3. its executions can be deterministically replayed;
4. an independent optimized implementation passes trace-level differential
   tests; and
5. the documentation states exactly which properties are proved, assumed, and
   tested.

That result would establish the architecture needed to scale toward HMC,
multinomial selection, couplings, and eventually adaptation without confusing
mathematical kernel correctness with floating-point implementation evidence.
