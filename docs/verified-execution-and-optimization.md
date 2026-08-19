# Verified execution and optimization paths

## Purpose

This note records the intended relationship among Lean sampler semantics, the
serialized IR, practical Julia execution, numerical certificates, and future
optimization work. It also distinguishes proof-preserving transformations from
independent handwritten or agent-produced implementations.

The central distinction is between:

- proving that an ideal sampler has a stated mathematical property;
- preserving that sampler's operational semantics across serialization and a
  backend interpreter;
- relating finite-precision numerical decisions to ideal-real decisions; and
- testing an independently optimized implementation.

These are separate assurance obligations. In particular, stationarity is not
convergence from arbitrary initial states, and empirical agreement is not a
proof of stationarity.

## Assurance legend

The diagrams below use symbols directly so that their meaning remains visible
in terminals and other renderers without Mermaid color support.

```text
✅  Machine-checked theorem in Lean
🔗  Cross-language refinement obligation
📜  Runtime certificate checked using a Lean-proved theorem
🧮  Floating-point approximation boundary
🎲  Randomness or distribution assumption
🛠️  Compiler, runtime, operating-system, or hardware assumption
🧪  Testing evidence rather than a formal proof
📦  Generated data artifact
🤖  Handwritten or agent-produced optimization
```

## Verified source and executable backends

The IR is constructed in Lean. It is not obtained by translating arbitrary
Lean source. Lean gives the IR exact mathematical semantics and deterministic
trace-replay semantics. A serializer then emits a versioned, backend-neutral
artifact interpreted by Julia Reference.

```text
                         ✅ Mathematical sampler
                                   │
                                   ▼
                              ✅ Typed IR
                                   │
                    ┌──────────────┴──────────────┐
                    ▼                             ▼
          ✅ Exact kernel semantics       ✅ Deterministic replay
                    │                             │
                    ▼                             │
       ✅ Proved sampler properties               │
       such as detailed balance and               │
       target stationarity                        │
                                                  │
                              🔗 Lean serializer  │
                                      │           │
                                      ▼           │
                               📦 Samplers.ir     │
                                      │           │
                                      ▼           │
                         🔗 Julia parser/interpreter
                                      │
                                      ▼
                           Practical Julia execution
```

The current Lean theorems connect the command-IR interpreter to established
replay specifications and connect executable finite samplers to their exact
PMF or kernel denotations. The maintained Julia parser and interpreter are not
currently connected to those Lean semantics by a machine-checked
cross-language preservation theorem. Their correspondence is supported by
canonical artifact validation, trace tests, differential tests, and audits.

### Why retain a Julia interpreter?

For exact finite samplers, Lean replay can itself serve as an executable oracle.
A Julia interpreter is therefore a deployment and ecosystem choice rather than
a mathematical necessity.

For continuous samplers, the Lean semantic path uses exact real numbers,
mathlib measures, and definitions that may be noncomputable. It can prove what
an ideal sampler means and replay supplied ideal events, but it is not a
practical source of exact Gaussian real draws, floating-point linear algebra,
automatic differentiation, or user callback execution. Julia supplies those
concrete runtime facilities and exposes the sampler through a usable package
API.

The Reference interpreter also remains useful as a simple backend anchor for
testing optimized implementations. It does not by itself transfer the Lean
proofs through the language boundary.

## How close are the Lean and Julia interpreters?

For the finite command IR, their algorithms are intentionally close:

| Concern | Lean interpreter | Julia Reference interpreter |
|---|---|---|
| IR representation | Typed `Expr : Ty -> Type` | Parsed S-expression nodes |
| Environment | Stores separated by IR type | `Dict{String,Any}` |
| Natural values | `Nat` | `BigInt` |
| Natural subtraction | Truncated `Nat.sub` | `max(0, x - y)` |
| Indexing | Zero-based list index | Explicit `+1` array lowering |
| Categorical choice | Exact natural weights | Exact `BigInt` weights |
| Random source | Immutable explicit trace | Mutable `AbstractRandomSource` |
| Errors | Typed `RuntimeError` | Julia exceptions |

Both finite interpreters sum exact weights, consume a bounded draw, scan the
weights in order, and return a zero-based selected index. A formal
correspondence proof is therefore plausible once the representation, source
state, indexing, and error relations are stated.

The continuous interpreters share control-flow structure, but their numerical
meanings differ materially. Lean uses exact `ℝ`; Julia uses `Float64`, platform
transcendentals, array operations, callbacks, and concrete RNGs. Direct
equality is generally the wrong statement for this boundary.

## Worked path: continuous Gaussian RWMH

Scalar Gaussian random-walk Metropolis--Hastings illustrates every maintained
layer without hiding the exact-real/`Float64` boundary:

```text
mathlib Measure + Kernel
          │
          ▼
verified Gaussian RWMH kernel and invariance
          │
          ▼
typed continuous command IR ──► ideal-real Lean trace interpreter
          │                                  │
          ▼                                  └── trace-refinement theorem
canonical S-expression artifact
          │
          ▼
Julia Reference parser/interpreter ──► public GaussianRWMH API
          │
          └── differential tests ──► handwritten Optimized step
```

The concrete source trail is:

| Layer | Definition or evidence | What is established |
|---|---|---|
| General-state mathematics | [`gaussianRandomWalkMetropolisHastings`](https://github.com/xukai92/mcmc-lean/blob/main/formal/Mcmc/Kernel/RandomWalkMetropolisHastings.lean#L271) | A mathlib `Kernel ℝ ℝ` built from Gaussian translation proposals and MH acceptance. Its nearby theorems prove the Markov, reversible, and invariant properties. |
| Executable kernel denotation | [`gaussianRwmhKernel` and `gaussianRwmhProgramKernel`](https://github.com/xukai92/mcmc-lean/blob/main/formal/Mcmc/Executable/Continuous/RWMH.lean#L129) | The verified kernel and the exact kernel meaning assigned to the command program. |
| Main refinement theorem | [`gaussianRwmhProgramKernel_refines`](https://github.com/xukai92/mcmc-lean/blob/main/formal/Mcmc/Executable/Continuous/RWMH.lean#L155) | The exact program denotation equals the verified Gaussian RWMH kernel. [`gaussianRwmhKernel_invariant`](https://github.com/xukai92/mcmc-lean/blob/main/formal/Mcmc/Executable/Continuous/RWMH.lean#L171) then gives target invariance. This is not a generic convergence theorem. |
| Typed IR | [`gaussianRwmhProgram`](https://github.com/xukai92/mcmc-lean/blob/main/formal/Mcmc/Executable/Continuous/CompilerIR.lean#L92) | Proposal, log-density evaluation, acceptance threshold, uniform draw, and accept/retain control flow as backend-neutral data. |
| Executable Lean semantics | [`runGaussianRwmh`](https://github.com/xukai92/mcmc-lean/blob/main/formal/Mcmc/Executable/Continuous/CompilerIR.lean#L370) and [`runGaussianRwmh_refines`](https://github.com/xukai92/mcmc-lean/blob/main/formal/Mcmc/Executable/Continuous/CompilerIR.lean#L386) | On an explicit ideal-real noise/uniform trace, the interpreter returns exactly the stated proposal-or-current result and the correct unused trace. |
| Serialization | [`IRFormat.render`](https://github.com/xukai92/mcmc-lean/blob/main/formal/Mcmc/Executable/IRFormat.lean#L264) | Inserts the typed RWMH program into the versioned canonical artifact. |
| Emitted IR data | [`Samplers.ir`](https://github.com/xukai92/mcmc-lean/blob/main/VerifiedSamplers.jl/src/Reference/Samplers.ir#L1) | Contains the serialized `gaussian_rwmh_step!` declaration consumed by Julia. Despite its location, this is backend-neutral IR data, not handwritten Julia code. |
| Julia reference execution | [`Reference.gaussian_rwmh_step!`](https://github.com/xukai92/mcmc-lean/blob/main/VerifiedSamplers.jl/src/Reference/Reference.jl#L951) | Validates inputs and invokes the generic artifact interpreter. Control flow follows the artifact, while arithmetic, `exp`, callbacks, and randomness use Julia `Float64` runtime semantics. |
| Public Julia API | [`GaussianRWMH`, `step`, and `sample`](https://github.com/xukai92/mcmc-lean/blob/main/VerifiedSamplers.jl/src/VerifiedSamplers.jl#L1224) | Wraps an `AbstractRNG` as a runtime source and repeatedly calls the Reference implementation. |
| Independent optimized implementation | [`Optimized.gaussian_rwmh_step!`](https://github.com/xukai92/mcmc-lean/blob/main/VerifiedSamplers.jl/src/Optimized/Optimized.jl#L544) | A direct handwritten step used as an independently maintained comparison path; it does not inherit the Lean theorem automatically. |
| Cross-path evidence | [continuous RWMH tests](https://github.com/xukai92/mcmc-lean/blob/main/VerifiedSamplers.jl/test/continuous.jl#L1166) | Fixed-trace accept/reject cases, Reference/Optimized differential tests, validation checks, and seeded diagnostics. These are tests, not a proof of Julia semantics. |

A user invokes the public path as ordinary Julia code:

```julia
using Random
using VerifiedSamplers

rng = MersenneTwister(42)
target_logdensity(x) = -x^2 / 2
sampler = GaussianRWMH(target_logdensity, 0.8)
draws = sample(rng, sampler, 0.0, 2_000)
```

The machine-checked statement is about the exact kernel and ideal-real command
semantics. The generated artifact and differential tests make the Julia path
auditable, but the remaining `Float64`, callback, Julia-interpreter, and RNG
assumptions are intentionally visible rather than folded into the theorem.

## Numerical certification is a parallel path

Numerical certification is not a layer through which the ideal sampler is
compiled. Ideal-real and numerical execution are parallel paths. A certificate
relates selected values or decisions from those paths.

```text
                          ✅ Typed IR
                              │
                ┌─────────────┴─────────────┐
                ▼                           ▼
       IDEAL MATHEMATICAL PATH      EXECUTABLE NUMERICAL PATH

       ✅ Exact-real semantics       🔗 Serialized/interpreted IR
                │                           │
                ▼                           ▼
       ✅ Exact kernel/result        🧮 Float64 computation
                                            │
                                            ├── 🎲 concrete RNG
                                            ├── 🛠️ Julia/runtime
                                            └── callbacks/libraries

                │                           │
                └──────────┐     ┌──────────┘
                           ▼     ▼
                       📜 Certificate
                   relates the two paths
                           │
                 ┌─────────┴─────────┐
                 ▼                   ▼
       ✅ Same discrete decision   Ambiguous boundary case:
          or proved error bound    no agreement certified
```

A typical Lean theorem has the form:

```text
|computed - ideal| <= error
and
distance(ideal, decision boundary) > error
imply
computed decision = ideal decision.
```

Examples include acceptance decisions, categorical cumulative boundaries,
slice and divergence comparisons, U-turn dot products, target and gradient
error bounds, and approximate implicit-solver results. When a computed value
does not safely clear its error band, the interface must report ambiguity or
take an independently proved safe fallback; it must not silently claim exact
agreement.

Backend-supplied primitive bounds remain obligations. A Lean theorem that
correctly composes error bounds does not prove that a platform supplied a
truthful bound for `exp`, `log`, a reduction, a callback, or an RNG.

## Strengthening cross-language confidence

The serializer, parser, and interpreter boundary can be strengthened in
stages:

1. Regenerate the artifact and compare it byte-for-byte with the committed
   artifact (`make check-generated`).
2. Compare Lean and Julia on identical inputs and deterministic traces,
   including results, consumed events, remaining events, and failures.
3. Define an artifact parser in Lean and prove a round-trip theorem such as
   `parse (serialize program) = some program`.
4. State a representation relation between Lean environments and Julia-side
   values, then prove an abstract interpreter-correspondence theorem for each
   IR constructor.
5. Connect actual executions more tightly by having the backend emit an
   execution witness checked by a small Lean checker.

Assuming primitive Julia operations satisfy explicit contracts makes step 4
manageable for the finite IR. It proves correctness of an abstract backend
model, however, unless the actual Julia source is also connected to that model.
A proof-producing execution witness can cover actual runs without requiring a
formal semantics for all of Julia.

Randomness remains separate: a witness can prove that, given a particular
event, the interpreter followed the IR correctly. The claim that production
events have the required distribution still depends on an RNG theorem or
documented assumption.

## Parallel optimization tracks

Two optimization paths are available, but they do not need equal project
investment. The maintained Julia `Optimized` layer already supplies the
practical independent path. Near-term formal work therefore prioritizes the
artifact trust boundary; optimization passes should be added only when a
measured use case justifies them.

```text
                          ✅ Verified source IR
                                   │
                    ┌──────────────┴──────────────┐
                    ▼                             ▼
       A. VERIFIED TRANSFORMATIONS       B. AGENTIC/HANDWRITTEN SEARCH

       ✅ Semantics-preserving pass      🤖 Independent implementation
                    │                             │
                    ▼                             ▼
       ✅ Optimized IR                    🧪 Trace/property tests
                    │                    📜 Numerical certificates
                    │                             │
                    └──────────────┬──────────────┘
                                   ▼
                          Comparative benchmarks
```

A hybrid path first applies every available verified transformation and then
allows an agentic optimization loop to improve the generated baseline:

```text
✅ Source IR
    │
    ▼
✅ Verified optimization passes
    │
    ▼
✅ Optimized generated baseline
    │
    ▼
🤖 Agentic handwritten optimization
    │
    ▼
🧪/📜 Tested and execution-certified implementation
```

The handwritten step after the verified baseline does not automatically retain
the proof chain. Its delta must be proved semantics-preserving, checked by an
execution certificate, or explicitly classified as test-supported.

### Julia transformation ecosystem

Program-transformation and diagnostic packages are tools available to the
optimization agent, not mandatory stages in a fixed compiler pipeline. An
optimization pass may begin with profiling, allocation inspection, compiler
IR, equality saturation, benchmark evidence, or direct code review. What
defines the loop is the propose–gate–measure discipline and the recorded
assurance class, not which discovery tool produced the candidate.

The project should not build a general transformation engine from scratch.
For transformations over the custom sampler term language,
[Metatheory.jl](https://juliasymbolics.github.io/Metatheory.jl/stable/) provides
term rewriting and equality saturation through `TermInterface.jl`. For
transformations of lowered Julia code,
[IRTools.jl](https://fluxml.ai/IRTools.jl/latest/) provides an IR manipulation
surface. These solve different problems: neither library proves that a rewrite
preserves the Lean sampler semantics.

No dependency is added until a concrete, benchmark-motivated transformation
needs it. At that point Lean should still state or check the semantic
equivalence; the Julia library is an implementation mechanism, not the source
of the proof.

### First measured transformation: owned NUTS phases

The first optimization-loop exercise was an agentic code-review pass. It
specializes `Optimized.NUTS` phase
construction when its inputs are already owned `Vector{Float64}` values. The
generic lowering performed `Float64.(position)` and `Float64.(momentum)` at
every tree leaf even though leapfrog had just produced values of exactly that
type. The specialization removes those dead conversions and retains the
generic conversion method for other input types.

This is a type-directed dead-copy elimination, not a change to tree semantics:
log density, kinetic energy, U-turn decisions, RNG consumption, and candidate
selection retain their order. The ordinary deterministic NUTS tests are the
conformance gate; statistical tests remain empirical protection rather than a
proof of Julia semantics. On the maintained 100-dimensional isotropic
Gaussian workload with five 10,000-draw chains, the median changed from
0.865 seconds before the rewrite to 0.755 seconds after it, about a 13%
improvement in this rerun. Run the post-transformation measurement with:

```sh
make benchmark-nuts-optimization
```

The experiment prints the transformation name, assurance class, complete
chain timings, median, and throughput. This deliberately small pass validates
the acceptance workflow without implying that Metatheory.jl, IRTools.jl, a
profiler, or a general search engine must occupy a particular phase. Those
remain optional tools for future agentic passes.

## Current directions

The project is prioritizing four connected directions without expanding the
sampler family:

1. **Consolidation.** Keep one canonical artifact, one maintained Julia
   reference interpreter, and a small public architecture. Historical
   execution experiments remain useful evidence but should not become parallel
   public APIs. Optimization work stays in the existing Julia `Optimized`
   layer and is driven by measured needs.
2. **Execution trust.** Reduce assumptions at the Lean--artifact--Julia
   boundary, starting with exact finite programs and extending only where a
   maintained consumer warrants it. Appropriate techniques include independent
   parsing and typed validation, shared deterministic traces, abstract
   interpreter correspondence, and compact execution witnesses.
3. **Backend-neutral execution.** Treat optimized Julia, parallel CPU, CUDA,
   and later accelerators as sibling consumers of one Reference contract.
   Backend work must make event/RNG scheduling, reductions, callback behavior,
   and supported IR primitives explicit. It should not duplicate the sampler's
   mathematical correctness proof.
4. **Controlled optimization search.** Maintain a small agentic loop that may
   use manual inspection, profilers, compiler diagnostics, transformation
   libraries, or other tools to propose Julia or IR changes, but accepts them
   only after compilation,
   deterministic conformance, applicable certificates, statistical diagnostics,
   and benchmark improvement. One measured exact transformation should precede
   any general transformation framework.

`Mcmc.Executable.IRParser` now validates the complete artifact envelope and
version, independently decodes the two registered exact finite programs, and
checks their canonical typed renderings. This removes serializer-format trust
for those declarations. It does not yet prove the Julia parser or interpreter
equivalent to Lean.

Continuous floating-point certification and new sampler families are not
required by these directions. Existing certificates remain an optional,
backend-neutral evidence path. A future benchmark-motivated transformation may
use an established Julia rewriting library, but only after the specific
semantic obligation is clear.

### Backend family and parallelism

The Reference interpreter is the operational comparison point for every
maintained backend:

```text
Lean theorem → typed IR → Julia Reference
                           ├─ Julia Optimized
                           ├─ parallel CPU
                           └─ CUDA / other accelerator
```

This is a shared-contract fan-out, not a compilation claim that all backends
are already proved equivalent. Exact finite programs can use exhaustive or
trace equality. Continuous programs normally combine shared event traces,
bounded numerical checks where useful, and explicitly empirical statistical
tests. A backend capability record should reject unsupported primitives rather
than silently fall back to different semantics.

Parallel development should proceed in two levels:

1. run independent chains concurrently with an explicit seed list and require
   each chain to reproduce its sequential backend result; then
2. parallelize within a chain only for algorithms whose recurrence has an
   associative scan or another proved decomposition.

Accelerators follow the same split. Batched independent chains and vectorized
fixed-step transitions are the first useful target. Device-specific floating
point, reductions, callbacks, and RNG streams remain backend obligations; the
existing numerical certificates may check selected executions without becoming
a mandatory layer between IR and execution.

### Feedback from search into verification

The independent track is valuable as an optimization-discovery engine:

```text
agent discovers a faster implementation
                │
                ▼
benchmarks demonstrate a material gain
                │
                ▼
extract the underlying semantic transformation
                │
                ▼
implement it as an IR pass
                │
                ▼
✅ prove preservation in Lean
                │
                └──── supplies the next verified baseline
```

Candidate exact transformations include constant folding, dead-binding
elimination, branch simplification, specialization, exact categorical binary
search, cached row totals, and fusion of duplicate traversals. Reassociation
of floating-point reductions, BLAS substitution, approximate solvers, and
similar numerical changes generally require error-refinement statements rather
than exact semantic equality.

### Auto-research acceptance gates

An automated optimization loop should maximize throughput, latency, memory
use, or scaling only subject to explicit correctness gates:

- compilation and ordinary validation succeed;
- deterministic trace consumption remains conformant;
- finite exact cases pass exhaustive equivalence where feasible;
- numerical certificates continue to validate;
- non-finite behavior is not introduced;
- reproducibility contracts remain explicit; and
- statistical diagnostics are reported only as empirical evidence.

Every benchmark result should identify its assurance class, for example:

```text
reference-interpreted
verified-transformed
generated-then-agent-optimized
independent-agent-optimized
```

This makes it possible to study both the performance frontier and how much of
an agent-discovered improvement can subsequently be recovered inside the
machine-checked transformation chain.

## Remaining trusted base

Even after proving serialization, parsing, interpreter correspondence, and
individual numerical refinements, execution normally retains a foundational
trusted base:

- the Lean kernel and machinery used to check proofs;
- the backend compiler and runtime;
- the operating system and hardware; and
- the production entropy source and RNG implementation.

The objective is not to describe this base as nonexistent. It is to make it
small, explicit, replaceable where practical, and separate from the sampler's
machine-checked mathematical claims.
