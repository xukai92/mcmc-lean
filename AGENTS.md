# AGENTS.md

This file gives coding agents repository-specific instructions. It applies to
the entire repository.

## Project purpose

`mcmc-lean` develops machine-checked correctness results for Markov chain
Monte Carlo algorithms in Lean 4. The current result is a finite-state proof
of Metropolis--Hastings detailed balance and stationarity.

Be precise about theorem strength:

- A row-stochastic transition matrix is a Markov kernel in the local finite
  interface.
- Detailed balance implies stationarity.
- Stationarity does not by itself imply convergence from arbitrary initial
  states.
- Do not describe a result as a convergence theorem unless it states the
  required ergodicity assumptions and the mode of convergence.

Read `docs/related-work.md` before making novelty claims or choosing an
architecture for general-state kernels.

## Repository layout

- `McmcLean/Finite/MarkovKernel.lean`: elementary finite distributions,
  kernels, reversibility, and stationarity.
- `McmcLean/Finite/MetropolisHastings.lean`: finite-state MH construction and
  its correctness proof.
- `McmcLean/Examples/`: small concrete theorem instantiations.
- `McmcLean.lean`: library import surface.
- `docs/`: design and research notes.

Put reusable definitions and theorems under `McmcLean/`. Examples should
instantiate general results rather than contain essential library arguments.
Update `McmcLean.lean` when adding a public module.

## Toolchain and commands

The repository pins Lean and mathlib in `lean-toolchain` and `lakefile.toml`.
Use the pinned versions; do not update them incidentally.

From the repository root:

```sh
# Fetch dependencies and the mathlib binary cache when setting up a clone.
lake update
lake exe cache get

# Required validation for repository changes.
lake build

# Useful while iterating on one module.
lake env lean McmcLean/Finite/MetropolisHastings.lean
```

Run the narrow module check while developing, then run `lake build` before
finishing any code change. Documentation-only changes do not require a build
unless they alter commands, module names, or generated documentation inputs.

## Proof and code conventions

- Use namespaces matching the module path, currently rooted at `McmcLean`.
- Add module docstrings (`/-! ... -/`) and docstrings for public definitions
  and main theorems.
- Prefer small named lemmas with mathematically meaningful statements over a
  single large tactic proof.
- Reuse mathlib lemmas and existing local abstractions before adding custom
  tactics or parallel definitions.
- Keep the elementary finite layer independent of measure theory unless a
  change is explicitly implementing the bridge to
  `ProbabilityTheory.Kernel`.
- State assumptions explicitly. In particular, distinguish nonnegative,
  positive, normalized, irreducible, and aperiodic hypotheses.
- Avoid unnecessary `classical`; keep it local to the proof that needs it.
- Do not commit `sorry`, `admit`, `axiom`, or disabled linter workarounds as a
  substitute for a proof. If a theorem cannot yet be proved, leave a documented
  roadmap item rather than weakening it silently.
- Preserve the distinction between the proposal kernel, the MH transition
  kernel, accepted flow, acceptance probability, and stationary target.

For finite MH, the symmetric accepted-flow identity

```text
min (π(x) * q(x,y)) (π(y) * q(y,x))
```

is the preferred algebraic core. When presenting the usual acceptance-ratio
formula, prove its equivalence to this flow and account explicitly for zero
proposal probabilities.

## Workflow for agents

1. Inspect `README.md`, the relevant modules, and `git status` before editing.
2. Check for existing definitions and theorem names with `rg` before creating
   new ones. For mathlib APIs, inspect the pinned dependency source under
   `.lake/packages/mathlib/Mathlib` rather than guessing signatures.
3. Make the smallest coherent change that advances the requested theorem or
   infrastructure.
4. Compile the changed module early. Treat new warnings as defects unless a
   warning is clearly pre-existing and unrelated.
5. Run `lake build` for code changes.
6. Review `git diff --check` and `git diff` before handing off. Do not modify or
   discard unrelated user changes.
7. Report exactly what was proved and what remains unproved. Include the
   validation commands run.

When a proof attempt exposes a missing reusable lemma, add that lemma at the
lowest appropriate layer. Do not hide mathematical obligations behind a more
permissive definition merely to make the final theorem compile.

## Tests and examples

Lean compilation is the primary verification mechanism. Add a small example
when it demonstrates that a generic API is usable or protects an important
edge case. Examples must compile as part of the library build.

For changes to MH, consider at least these cases as applicable:

- an asymmetric proposal;
- a zero forward or reverse proposal probability;
- diagonal transitions and rejection mass;
- a concrete finite target with a direct stationarity instantiation.

## Documentation and citations

Use stable primary sources where possible: published papers, official
proof-assistant archives, mathlib documentation, and source repositories.
Separate machine-checked results from pen-and-paper formalizations. Qualify
negative literature-search claims with the date and scope of the search.

Update `README.md` when the public theorem surface, build procedure, or roadmap
changes. Update `docs/related-work.md` when adding work that materially affects
the project's novelty or design.
