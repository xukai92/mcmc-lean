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
