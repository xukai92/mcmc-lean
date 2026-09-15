# Factory workflows

Two automated workflows turn MCMC algorithm ideas into verified, optimized
implementations. They are portable workflow files at
`.factory/workflows/optimize.py` and `.factory/workflows/formalize.py`,
auto-discovered by the factory `WorkflowRegistry`.

## Overview

The intended pipeline chains both workflows:

```
Idea (algorithm spec)
  ↓  formalize
Lean 4 proofs + IR artifact + auto-generated Reference Julia
  ↓  optimize
Fast Optimized Julia with conformance gates
```

The formalize workflow produces correct-by-construction code: if `lake build`
compiles, the algorithm is formally verified. The optimize workflow takes that
Reference as ground truth and builds a fast implementation that must produce
identical outputs under deterministic replay.

## Architecture recap

Every sampler passes through four layers, each with a machine-checked link:

| Layer | What | Verified by |
|-------|------|-------------|
| Kernel theory | Lean 4 proofs (detailed balance, stationarity) | `lake build` |
| Executable refinement | Theorem: IR program = mathematical kernel | `lake build` |
| Compiler IR | Versioned S-expression artifact (`Samplers.ir`) | `make check-generated` |
| Reference Julia | Auto-generated from IR | IR interpreter |
| Optimized Julia | Generic, fast, hand-maintained | `Evaluation.replay_pair` conformance |

## Formalize workflow

**Purpose.** Take a well-specified algorithm description and produce Lean 4
kernel theory, executable refinement proofs, IR emission, and auto-generated
Reference Julia.

**Pipeline.** 22 nodes, 31 edges.

```
fork(3 researchers: patterns, mathlib, algorithm)
  → join → gate(CEO)
  → strategist → gate(USER approval)
  → builder_theory → lake build (max 5 retries) → gate(CEO review)
  → builder_ir → lake build (max 3 retries)
  → make generate
  → fork(3 QA: check-generated, make test, proof hygiene) → join → gate
  → archivist (async)
```

Two builder phases with separate retry budgets: 5 iterations for theory
(proof work is iterative — compile errors guide the next attempt) and 3 for
IR wiring (mechanical once theory compiles).

**Usage.**

```sh
factory ceo /path/to/verified-samplers \
  --mode formalize \
  --focus "Implement [algorithm]. [Math spec]. [What to prove]. [IR program spec]."
```

**Produces.** New `.lean` files under `formal/Mcmc/`, updated `CompilerIR.lean`
and `IRFormat.lean`, regenerated `Samplers.ir`, updated `Mcmc.lean` imports,
and a Reference interpreter handler in `Reference.jl`.

## Optimize workflow

**Purpose.** Take an existing Reference implementation and produce a fast
Optimized Julia version with conformance gates.

**Pipeline.** 18 nodes, 24 edges.

```
precondition_check (Reference must exist for --focus target)
  → fork(3 researchers: semantics, conventions, julia perf)
  → join → gate(CEO)
  → strategist → gate(USER approval)
  → builder (max 3 retries)
  → gate(CEO)
  → fork(3 QA: conformance, tests, benchmark) → join → gate (RELOOP to builder)
  → archivist (async)
```

**Precondition.** The named function must exist in
`VerifiedSamplers.jl/src/Reference/Reference.jl`. If an Optimized
implementation already exists, it becomes the baseline; otherwise the
Reference is the starting point.

**Usage.**

```sh
factory ceo /path/to/verified-samplers \
  --mode optimize \
  --focus "function_name!"
```

**Produces.** Updated `Optimized/Optimized.jl` with generic `T<:AbstractFloat`
implementation, conformance tests in `test/continuous.jl`, and an archival
record.

## Chaining the workflows

When running optimize after formalize, the optimize workflow needs access to
the Reference output from the formalize run. Two approaches:

**Option 1 (recommended).** Run optimize directly in the formalize worktree:

```sh
factory ceo /path/to/formalize-worktree \
  --mode optimize \
  --focus "function_name!" \
  --no-worktree
```

**Option 2.** Merge the formalize commits to main first, then run optimize
normally. The optimize workflow will create its own worktree from main.

If neither is done, the optimize workflow silently passes its conformance gate
without actually comparing against the Reference — the function doesn't exist
in the worktree, so no replay test runs.

## Lessons learned

**Use `make julia` for Julia-only changes.** The optimize workflow's builder
runs `make test` by default, which includes `lake build` of 4000+ Lean
modules (~20 minutes). For changes that only touch Julia files, `make julia`
(~3 minutes) is sufficient. Tell the builder explicitly.

**Worktree divergence.** Factory worktrees branch from main at dispatch time.
If the formalize output hasn't been merged to main yet, a new optimize
worktree won't have the Reference. Use `--no-worktree` in the formalize
worktree or merge first.

**Conformance gate scope.** The conformance gate only catches differences if
both Reference and Optimized implementations exist. When the Reference is
missing (e.g., wrong worktree), the gate passes vacuously. The precondition
check catches a missing Reference function, but not a stale one.

**IR version bumps require Julia updates.** When the formalize workflow bumps
the IR format version, the Julia Reference interpreter needs a handler for the
new program and an updated `IR_FORMAT_VERSION` constant. The CEO typically
catches this during QA and spawns an additional builder to fix it.

## Track record

| Algorithm | Formalize | Optimize | Lean lines | Speedup | Total |
|-----------|-----------|----------|------------|---------|-------|
| vector\_mala\_step! | pre-existing | 35m | — | 2.28× (ws) | 35m |
| Barker RWMH | 34m | 10m | 471 | 145× | 44m |
| DR-G-HMC | 1h 48m | 19m | 687 | 16.7× | 2h 7m |

Speedup is Optimized vs Reference (IR interpreter bypass). The Barker 145×
and DR-G-HMC 16.7× reflect interpreter overhead; the MALA 2.28× reflects
arithmetic optimization of an already-native Optimized function.

## Factory version

The factory version is pinned in `.factory/factory-version` for
reproducibility. The workflows were developed and tested with
`remote-factory==0.2.0`.
