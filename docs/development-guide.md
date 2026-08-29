# Adding a sampler

This guide describes the recommended path for adding an algorithm to Verified
Samplers. The mathematical sampler comes first. The current executable IR is a
target for lowering; it does not define which algorithms belong in the formal
library.

## Development flow

```text
mathematical algorithm in Lean
            │
            ▼
kernel/law and stated correctness properties
            │
            ▼
executable presentation of the algorithm
            │
            ▼
lower into existing IR ── or ── justify a reusable IR extension
            │
            ▼
prove executable semantics refine the mathematical sampler
            │
            ▼
emit canonical artifact and run through Julia Reference
            │
            ▼
trace, differential, property, and statistical tests
            │
            ▼
optional benchmark-motivated Optimized implementation
```

The stages can inform one another. For example, an abstract proof may expose a
bounded-iteration or solver-validity assumption that belongs in the executable
interface. The direction of justification nevertheless remains

```text
executable representation ──refines──► mathematical sampler
```

The mathematical definition should not be weakened or reshaped merely because
the current IR lacks a construct.

Start each addition with a copy of the
[sampler development record](sampler-development-template.md). It keeps theorem,
execution, optimization, and diagnostic obligations visible to both researchers
and coding agents without making every stage mandatory. In particular, a
mathematics-only contribution can complete its declared formal obligations and
leave executable lowering explicitly pending.

## The recommended vertical slice

For an algorithm intended to become a maintained sampler, use this order. A
stage may be left explicitly pending, but it must not be silently replaced by
evidence from a later stage.

| Stage | Typical destination | Exit condition |
|---|---|---|
| Mathematical semantics | `formal/Mcmc/Kernel/`, `Finite/`, or another reusable formal layer | The transition and target are defined independently of execution |
| Correctness theorem | The same formal module, with a small client under `formal/Mcmc/Examples/` when useful | The exact proved property and hypotheses compile without placeholders |
| Executable presentation | `formal/Mcmc/Executable/` | One transition has typed ideal semantics, including draw order and failure behavior |
| IR lowering | `CompilerIR.lean` or a focused typed sub-IR | Existing constructs are reused, or each new construct has reusable semantics |
| Refinement | A focused `*Refinement.lean` module | The command law, kernel, or deterministic trace is connected to the mathematical sampler—or the remaining bridge is named explicitly |
| Generated Reference | `IRFormat.lean`, `IRParser.lean`, and `VerifiedSamplers.jl/src/Reference/` | The canonical artifact regenerates and the Julia interpreter exposes a narrow wrapper |
| Maintained implementation | `VerifiedSamplers.jl/src/Optimized/` | An independent, concretely typed implementation passes differential and edge-case tests |
| Public API | `VerifiedSamplers.jl/src/Public/` | `step(rng, ...)` and `sample(rng, ...)` route explicitly to Reference or Optimized |
| Evaluation | `VerifiedSamplers.jl/test/` and, when useful, `benchmark/` | Replay, statistical, and performance evidence are labelled as empirical |
| Coverage record | progress, obligation matrix, development log, and any paper audit | Readers can locate every theorem, implementation, and open boundary |

This order is about justification, not mandatory commit granularity. It is
often productive to prototype the executable form while proving the kernel,
but the prototype does not determine the mathematical statement.

### Before writing a new definition

Search the repository and pinned mathlib first. Many algorithms are clients of
an existing construction rather than new correctness proofs. For example, a
new proposal accepted with the general Metropolis--Hastings construction may
need a proposal normalization/measurability proof, not a second proof of the
abstract MH theorem.

```sh
rg -n "candidateName|relevantConcept" formal/Mcmc VerifiedSamplers.jl/src
rg -n "relevantMathlibLemma" formal/.lake/packages/mathlib/Mathlib
```

Decide up front:

- the mathematical state space and base measure;
- whether callback gradients mean `∇logπ` or the gradient of a potential;
- parameter conventions, such as variance versus standard deviation;
- the random-event order and rejection/failure fallback; and
- whether the desired theorem is validity, reversibility, invariance,
  convergence, or an execution-refinement statement.

## 1. Formalize the mathematical sampler

Start under `formal/Mcmc/` at the lowest reusable layer. Prefer mathlib
`Measure` and `ProbabilityTheory.Kernel` for general-state algorithms, and use
the local finite layer when exact finite combinatorics or execution is the
actual subject.

Define the proposal, transition kernel or law, target, and auxiliary state
separately. State every normalization, positivity, measurability,
irreducibility, or integrability hypothesis explicitly.

Prove only the properties supported by those hypotheses. In particular:

- detailed balance can establish stationarity;
- stationarity alone is not convergence from arbitrary initial states; and
- a convergence theorem must state its ergodicity assumptions and mode of
  convergence.

Examples under `formal/Mcmc/Examples/` should instantiate reusable results
rather than contain essential proofs.

## 2. Derive an executable presentation

Identify the algorithmic operations needed for one transition: random draws,
control flow, state updates, callbacks, bounded iteration, solvers, and
failure behavior. Give this presentation ideal mathematical semantics before
considering `Float64` behavior.

Then compare it with the existing IR:

1. **Use the core IR** when the required operation is already expressible.
2. **Extend the core IR** when a missing construct is small, recurring, and has
   clear backend-independent semantics.
3. **Introduce a typed sub-IR or certified primitive** when the operation is a
   coherent specialized domain, such as checked dynamic trees or an implicit
   solver.

Avoid opaque primitives named after whole algorithms. A primitive such as
`run-new-sampler` technically makes the algorithm executable but moves the
meaningful correctness obligation outside the IR. Prefer reusable concepts
whose interpretations can be stated and checked independently.

General recursion, data-dependent unbounded loops, automatic differentiation,
GPU execution, and arbitrary Julia callbacks are not implicit capabilities of
the current IR. Add support only with an explicit semantic contract.

Execution hardware is not part of the mathematical sampler definition. A CPU
optimized path, parallel evaluator, CUDA kernel, or later accelerator should
implement the same backend-neutral replay/refinement contract. Adding one
normally requires backend conformance evidence and numerical/reduction
assumptions, not a duplicate invariance theorem for the sampler.

## 3. Prove the lowering or refinement

Connect the executable presentation back to the mathematical definition. The
appropriate statement depends on the algorithm:

- equality of kernels or output laws;
- equality of deterministic replay results for every valid trace;
- preservation of an invariant target through a proved kernel equality; or
- a conditional theorem from an explicit solver, callback, or numerical
  certificate.

Keep serialization separate from semantics. A successful artifact round trip
shows that syntax was preserved; it does not prove the Julia interpreter
implements the Lean denotation.

For continuous algorithms, distinguish exact-real semantics from concrete
floating-point execution. Do not infer a `Float64`, `libm`, callback, or RNG
theorem from a result over Lean `ℝ`.

## 4. Add the maintained execution paths

Register the program in the canonical artifact only after its typed semantics
and refinement boundary are clear. Extend the Julia Reference interpreter with
the smallest required backend support, expose a stable public wrapper, and add
tests at the relevant boundaries.

Useful evidence includes:

- exact or deterministic trace replay;
- Reference/Optimized differential checks on shared traces;
- rejection and malformed-input cases;
- mathematical property tests where exact proof is not transported through
  Julia; and
- seeded statistical diagnostics for implementation regressions.

These tests audit the runtime; they do not replace Lean proofs. Add a separate
`Optimized` implementation only when usability or measurements justify it.
Prefer established Julia transformation libraries over building a general
optimizer, while keeping semantic preservation as a separate obligation.
Parallel and accelerator implementations should enter through the same path:
explicit seed/event scheduling, shared deterministic traces where applicable,
backend capability checks, statistical diagnostics, and comparative
benchmarks. Independent chains are the preferred first parallel primitive;
within-chain scans require an additional associative-recurrence argument.

## 5. Integrate and validate

Expose reusable Lean modules through `formal/Mcmc.lean`, document the exact
claim boundary, and update the progress or paper audit when public coverage
changes. From the repository root, run:

```sh
make test
make check-docs-generated
julia --project=docs docs/make.jl
```

During development, use a narrow Lean module check before the full build. Also
review `git diff --check` and the complete diff, and do not commit proof
placeholders.

## Worked vertical slice: isotropic MALA

MALA illustrates the complete repository shape without pretending that all
assurance layers are the same theorem.

```text
score and target weight
        │
        ▼
scoreMALA mathematical kernel
        │  Markov / reversible / invariant in Lean
        ▼
scalar_mala_step! and vector_mala_step! typed programs
        │  introduced in artifact version 24 (current format: 25)
        ▼
Reference interpreter ───── shared events ───── Optimized implementation
        │                                           │
        └──────── public MALA dispatch ──────────────┘
                              │
                              ▼
                replay + moments + benchmark rows
```

The mathematical layer is in
`formal/Mcmc/Kernel/Langevin.lean`. It defines the conventional drift
`ε²/2 ∇logπ(q)` and proves `scoreMALA_isMarkov`,
`scoreMALA_isReversible`, and `scoreMALA_invariant` under explicit hypotheses.
These are invariance results, not geometric-convergence results.

The executable programs are in
`formal/Mcmc/Executable/Continuous/CompilerIR.lean`. They declare `ε` as the
proposal standard deviation, draw Gaussian noise before the uniform decision,
evaluate the score at both endpoints, and include the forward/reverse Gaussian
proposal correction. `IRFormat.lean` emits the programs and `IRParser.lean`
checks their canonical syntax round trip.

The Reference wrapper in `VerifiedSamplers.jl/src/Reference/Reference.jl`
interprets that emitted program at the documented Float64 boundary. The
independent implementation in `src/Optimized/Optimized.jl` preserves a caller's
concrete `T<:AbstractFloat`; `src/Public/MALA.jl` selects the path explicitly.
Tests replay identical events through both paths, check malformed dimensions,
exercise `Float32`, and run normal-target moment diagnostics. The shared
benchmark adds `mala × verified-reference` and
`mala × verified-optimized` rows and records `MALA_STEP_SIZE` separately.

One boundary remains deliberately visible: the repository proves the
score-MALA kernel and separately gives the typed MALA command its ideal
formula, artifact round trip, and runtime conformance tests. A focused theorem
identifying the complete stochastic command denotation with `scoreMALA` would
strengthen this from the current explicit bridge boundary to the same kind of
closed command-kernel refinement available for scalar Gaussian RWMH. Artifact
generation or seeded equality alone does not prove that theorem.

### Definition of done for a maintained sampler

A sampler is end-to-end at its declared assurance level when:

1. its public mathematical theorem is named and its assumptions are documented;
2. one transition has an unambiguous typed executable presentation;
3. every new IR operation has semantics and its artifact round trip is checked;
4. the Reference path consumes the generated artifact rather than duplicating
   the algorithm in an unrelated handwritten implementation;
5. the Optimized path, if present, is independently maintained and generically
   typed;
6. shared-event tests cover acceptance, rejection, and invalid inputs;
7. statistical tests exercise a target with known behavior;
8. benchmark rows use the same declared algorithm and hyperparameters;
9. exact-real, floating-point, callback, RNG, and external-library boundaries
   are stated separately; and
10. the progress and obligation ledgers identify anything still open.

The phrase “end-to-end” must therefore be qualified by its bridge status. A
sampler can have every runtime layer and still have an open formal refinement
obligation; conversely, a complete mathematical theorem does not require a
Julia implementation.

## Review checklist

- Is the mathematical definition independent of the current IR?
- Are proposal, transition, target, and auxiliary objects kept distinct?
- Does the theorem claim stationarity, convergence, or execution equivalence
  at exactly the strength proved?
- Is every new IR construct reusable and independently meaningful?
- Is the executable-to-mathematical refinement theorem explicit?
- Are exact-real, artifact, Julia-interpreter, floating-point, callback, and
  RNG boundaries separately identified?
- Is optimization optional and supported by tests or measurements?

For a complete worked example, follow continuous Gaussian RWMH through the
[verified execution and optimization](verified-execution-and-optimization.md#worked-path-continuous-gaussian-rwmh)
page. Its [completed development record](rwmh-development-record.md) shows how
to fill the obligation template without overstating the execution boundary.
The [fixed-step HMC record](hmc-development-record.md) demonstrates the same
process when the existing formal and executable pieces do not yet have one
end-to-end kernel-equality theorem.
