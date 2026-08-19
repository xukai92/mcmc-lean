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

## Revised near-term milestones

1. Parse the serialized S-expression syntax in Lean and decode the exact finite
   programs back into typed finite IR.
2. Prove byte-for-byte parse/decode/re-render round trips for categorical
   sampling and generic finite MH, including escaped strings and rejection of
   ill-typed input.
3. Extend the decoder toward the full top-level artifact only when another
   declaration class needs a checked consumer.
4. Keep the existing Julia `Optimized` implementations and comparative tests;
   do not create a separate optimizer project.
5. If profiling identifies a reusable IR transformation, implement the pass
   with an established Julia rewriting library where helpful and add the
   corresponding Lean semantic theorem or checked witness.

Milestones 1--2 are now implemented in `Mcmc.Executable.IRParser`. The parser
foundation is intentionally narrower than a proof about the Julia parser or
interpreter: it removes one serializer-format trust gap without claiming a
formal semantics for Julia.

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
