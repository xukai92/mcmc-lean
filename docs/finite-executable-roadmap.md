# Finite executable sampler roadmap

The component boundaries and dependency rules used by this roadmap are defined
in the [executable sampler architecture](executable-architecture.md).

## Goal

The first executable milestone is one exact, finite, end-to-end slice:

```text
Lean executable finite MH program
  -> exact PMF semantics
  -> refinement to Mcmc.Finite.MetropolisHastings
  -> deterministic trace interpreter
  -> compiled Lean conformance oracle
  -> emitted VerifiedSamplers.Generated Julia core
  -> exhaustive finite and trace-level tests
```

The delivered MVP is the existing two-state target and proposal.
Natural-weight data and categorical sampling are generic over `Fin n`; the
end-to-end MH refinement is deliberately the fixed two-state MVP. The
milestone does not include continuous sampling, floating point, HMC,
adaptation, or an optimized Julia implementation.

## Locked design decisions

### Exact numeric domain

Executable inputs use nonnegative integer weights. Normalization gives exact
rational probabilities mathematically, while execution needs only integer
arithmetic and a `drawBelow(total)` primitive. The generated core must use
arbitrary-precision integers or reject values outside a documented checked
range; silent overflow is forbidden.

The existing elementary finite theory remains unchanged: its distributions
and kernels use real-valued masses. New realization maps coerce normalized
integer weights to those existing definitions. This avoids creating a second
stationarity or detailed-balance theory.

### State space

The first IR uses `Fin n` as its state representation. This gives the emitter a
stable zero-based encoding and avoids making arbitrary Lean `Fintype`
enumerations part of the Julia contract. A later encoded-finite-state interface
may transport the result to enums and records.

### Random primitive

The only primitive random operation required initially is
`drawBelow(upper)`, returning an integer in `[0, upper)`. Categorical and
Bernoulli draws are derived by cumulative integer weights and thresholding.
This keeps the trusted distributional boundary small.

Every primitive call checks `upper > 0`. Trace replay additionally validates
that the supplied result is in range and reports exhaustion, kind mismatch, or
an invalid value explicitly.

### Three separate semantics

The implementation must not conflate:

1. **PMF semantics:** the ideal distribution of a program under uniform
   `drawBelow` primitives;
2. **trace semantics:** a deterministic evaluator consuming and recording
   concrete primitive results; and
3. **Julia execution:** emitted code calling a documented runtime interface.

The first two are defined and related in Lean. Julia correctness remains
conditional on the emitter and runtime primitive contracts until a compiler
correctness theorem is added.

### Embedding and compiler

The MVP emitter is a narrow deterministic template for the proved two-state
configuration; it does not claim to translate arbitrary Lean expressions. A
small deeply embedded, intrinsically typed finite IR is the intended route to
generalizing code generation after the MVP.

The emitter writes only under `VerifiedSamplers.jl/src/Generated/` and inserts
a compiler-emitted, do-not-edit header. Generation is invoked explicitly with
`make generate`; ordinary Lean builds, Julia installation, and tests never
rewrite source files.

## Delivered formal modules and executables

```text
formal/Mcmc/Executable/Finite/Weights.lean
  normalized natural-weight distributions and kernels

formal/Mcmc/Executable/Finite/Trace.lean
  trace events, deterministic evaluator, validation, and diagnostics

formal/Mcmc/Executable/Finite/Categorical.lean
  cumulative selector, exact PMF law, and trace replay

formal/Mcmc/Executable/Finite/MetropolisHastings.lean
  executable proposal/accept/reject program and refinement theorem

formal/Mcmc/Executable/Finite/TwoState.lean
  exact end-to-end instantiation of the existing example

formal/Mcmc/Oracle.lean
  compiled command-line conformance oracle

formal/Mcmc/GenerateJulia.lean
  deterministic finite-core generation entry point
```

Public reusable modules are imported by `formal/Mcmc.lean`. The generator is a
separate Lake executable so importing the mathematical library has no file
system effects.

The maintained Julia primitive interface should live outside the emitted
submodule, for example:

```text
VerifiedSamplers.jl/src/Runtime/Runtime.jl
```

Both the production RNG source and trace source implement `draw_below!`.
`VerifiedSamplers.Generated` depends on that interface.

## Required theorem chain

Names may change during implementation, but the completed milestone must prove
statements with the following content.

1. Normalizing positive-total natural weights produces the intended PMF.
2. Cumulative selection driven by a uniform `drawBelow(total)` has that PMF.
3. For the delivered two-state configuration, the executable proposal and
   integer acceptance control flow has the stated exact PMF.
4. For both two-state inputs, the complete executable MH step denotes
   `Mcmc.Finite.MetropolisHastings.kernel ... |>.rowPMF`.
6. Consequently, its measure-kernel denotation is the existing embedded
   mathlib kernel and inherits the proved detailed balance and invariance
   theorem.
7. A successful trace evaluation follows the same pure control flow used by
   the denotational program and consumes exactly its reported primitive events.

The refinement endpoint is equality of PMFs for each input state. Equality of
generated Julia behavior is not silently included in this theorem.

## Implementation phases

### Phase A: exact weighted sampling — complete

- Define positive-total natural weight vectors over `Fin n`.
- Define `drawBelow` syntax, trace events, and explicit failures.
- Implement cumulative categorical selection.
- Prove its exact PMF law, including zero-weight entries and boundary draws.

### Phase B: executable finite MH — complete for the MVP configuration

- Define natural-weight target and proposal representations and their
  realization into the existing real-valued finite definitions.
- Implement proposal sampling and exact integer accept/reject thresholding,
  retaining row-dependent proposal normalization totals in the Hastings ratio.
- Prove row-PMF refinement to the existing finite MH kernel.
- Instantiate the two-state example, including acceptance, rejection, and
  self-proposal traces.

### Phase C: Julia emission and runtime — complete for the MVP

- Use the deterministic finite-core emitter (a reusable restricted AST remains
  a post-MVP compiler extension).
- Add the production and trace `draw_below!` runtime implementations.
- Emit the two-state transition into the `Generated` submodule.
- Drive generation through the Lake generator and root Make target.
- Make `make check-generated` regenerate in a temporary directory and fail on
  any diff.

### Phase D: end-to-end validation — complete

- Exhaustively test every valid primitive draw for the two-state example.
- Test invalid bounds, exhausted traces, out-of-range draws, zero proposal
  probabilities, self proposals, acceptance, and rejection.
- Compare Lean trace fixtures with Julia trace diagnostics and final states.
- Run `make test` and the generated-source freshness check in CI.

## Completion criteria

The finite milestone is complete only when:

- no `sorry`, axiom, or trusted Lean evaluator replaces a refinement proof;
- Lean proves exact row-PMF equality with the existing finite MH kernel;
- the existing detailed-balance and invariance results are reached through
  that equality rather than reproved for a parallel algorithm;
- generated Julia is committed under `VerifiedSamplers.Generated` and can be
  reproduced by `make generate`;
- Julia installation does not require Lean;
- deterministic trace replay agrees across Lean fixtures and Julia;
- exhaustive two-state tests cover all finite random choices and specified
  failures; and
- documentation lists the Julia emitter and `draw_below!` implementation as
  trusted boundaries, distinct from the machine-checked PMF refinement.

## Explicitly deferred

- arbitrary finite Lean state encodings;
- generic arbitrary-size executable-MH refinement (the categorical PMF theorem
  is already generic, while the delivered end-to-end MH refinement is the
  two-state MVP);
- continuous distributions and Gaussian primitive contracts;
- `Float64` refinement and numerical error bounds;
- RWMH, leapfrog, endpoint HMC, multinomial HMC, and couplings;
- adaptation, NUTS, GPU execution, and optimized implementations; and
- a proof of semantic preservation for the Julia emitter itself.
