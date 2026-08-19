# AGENTS.md

This file gives coding agents repository-specific instructions. It applies to
the entire repository.

## Project purpose

`verified-samplers` develops machine-checked MCMC algorithms and connects them
to auditable executable reference implementations. The formal layer is written
in Lean 4; the maintained runtime package is Julia.

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

- `formal/Mcmc/Finite/MarkovKernel.lean`: elementary finite distributions,
  kernels, reversibility, and stationarity.
- `formal/Mcmc/Finite/MetropolisHastings.lean`: finite-state MH construction and
  its correctness proof.
- `formal/Mcmc/Examples/`: small concrete theorem instantiations.
- `formal/Mcmc.lean`: library import surface.
- `VerifiedSamplers.jl/src/Reference/`: destination for compiler-emitted Julia.
- `VerifiedSamplers.jl/src/Optimized/`: maintained Julia implementations.
- `docs/development-log.md`: completed milestones, limitations, and roadmap.
- `docs/related-work.md`: literature survey and design implications.

Put reusable definitions and theorems under `formal/Mcmc/`. Examples should
instantiate general results rather than contain essential library arguments.
Update `formal/Mcmc.lean` when adding a public module.

## Toolchain and commands

The formal project pins Lean and mathlib in `formal/lean-toolchain` and
`formal/lakefile.toml`.
Use the pinned versions; do not update them incidentally.

From the repository root:

```sh
# Fetch dependencies and the mathlib binary cache when setting up a clone.
cd formal
lake update
lake exe cache get

# Required validation for repository changes.
lake build

# Useful while iterating on one module.
lake env lean Mcmc/Finite/MetropolisHastings.lean
```

The root `Makefile` provides `make formal`, `make julia`, and `make test`.
Reference generation is explicit through `make generate`; it must not occur as
an implicit side effect of an ordinary build.

The HMC benchmark has its own pinned Julia environment under `benchmark/`.
Use `make benchmark-dev` while changing the harness or report: it runs the
small workload and writes development results without replacing the committed
full-run measurements. Run `make benchmark-hmc` only when intentionally
refreshing the full benchmark evidence, then run `make benchmark-report` to
regenerate `docs/benchmarks.md` and its chart. Review changes to all files under
`benchmark/results/`, especially `metadata.csv`, before committing them; timing
results describe the recorded machine and producing commit and must not be
presented as measurements from another checkout. Benchmark diagnostics are
empirical evidence, not proofs or stable CI gates unless their calibration is
documented. See `benchmark/README.md` for workloads, environment overrides,
and interpretation.

CI runs `make test` and `make check-docs-generated` for ordinary changes.
The documentation workflow also builds Documenter after checking that the
committed Lean-generated page is current; it must not hide a stale generated
artifact by regenerating it implicitly.

Run the narrow module check while developing, then run `lake build` before
finishing any code change. Documentation-only changes do not require a build
unless they alter commands, module names, or generated documentation inputs.

## Proof and code conventions

- Use namespaces matching the module path, currently rooted at `Mcmc`.
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
changes. Record completed milestones and roadmap changes in
`docs/development-log.md`. Update `docs/related-work.md` when adding work that
materially affects the project's novelty or design.
