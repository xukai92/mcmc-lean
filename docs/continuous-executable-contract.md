# Continuous executable contract

## Purpose

This note fixes the semantic and runtime boundaries for continuous Gaussian
RWMH. It prevents three different objects from being described as though they
were the same implementation:

1. an exact mathlib probability measure and Markov kernel;
2. an ideal-real sampler program and mathematical trace replay; and
3. a Julia `Float64` program driven by a concrete `AbstractRNG`.

## Exact Lean layer

`Mcmc.Executable.IR` is an intrinsically typed, first-order syntax. Its binders
use typed de Bruijn variables; `letE` and `sample` contain syntax bodies rather
than opaque Lean continuations. Pure expressions currently cover real and
Boolean arithmetic sufficient for the initial accept/reject program, and the
primitive universe contains:

- positive bounded-natural draws;
- an ideal scalar standard normal; and
- an ideal unit uniform.

Every program has two interpretations:

- `Program.kernel`, a mathlib `ProbabilityTheory.Kernel` from typed
  environments to results; and
- `Program.replay`, deterministic consumption of kind-tagged trace events.

Lean proves every program kernel is Markov. A trace is an operational witness,
not a random measure, and replay failure is not assigned probability mass.
The ideal-real replay interpreter is intentionally `noncomputable`.

The first continuous refinement theorem is proposal-level. For every scalar
current state, `standardGaussianProposalProgram`:

- replays a normal event as `current + noise`;
- denotes `gaussianReal current 1`; and
- equals the proposal row built from
  `randomWalkProposalDensity (gaussianPDF 0 1)` in the existing RWMH theory.

The complete standard-Gaussian-target IR step now draws both proposal noise
and a unit uniform, and its trace theorem exposes the exact accept-or-retain
result. Lean proves that its real threshold is pointwise equal (after
`ENNReal.ofReal`) to the existing zero-safe `densityAcceptance`, and proves the
exact unit-uniform accept/reject integral. The remaining composition theorem
must assemble those facts into equality of the complete program measure and
the existing `randomWalkMetropolisHastings`; invariance will then be inherited
rather than reproved in the executable layer.

## Julia layer

Julia's `GaussianRWMH` is currently a maintained optimized implementation. It
uses:

```text
standard_normal!(RNGSource(rng)) = randn(rng)
uniform_unit!(RNGSource(rng))    = rand(rng)
```

and evaluates target log densities, proposals, ratios, and comparisons in
`Float64`. `FloatTraceSource` has distinct `NormalEvent` and `UniformEvent`
constructors and rejects kind mismatches and unit-uniform values outside
`[0,1)`. These events contain floating-point values; they are not encodings of
arbitrary Lean real numbers.

The Julia implementation is covered by deterministic accept/reject replay and
a normal-target moment test. These tests can expose implementation defects but
do not prove equality of probability laws.

## Required refinement assumptions

An eventual backend theorem or validated translation must account for each of
the following separately:

| Boundary | Required statement |
|---|---|
| Ideal standard normal to runtime RNG | The supported RNG and Julia version implement the documented `randn` distribution, or a quantified approximation bound is supplied. |
| Ideal unit uniform to runtime RNG | `rand` has the documented support/distribution and endpoint convention. |
| Real arithmetic to `Float64` | Overflow, underflow, `NaN`, infinities, rounding, and transcendental error are either excluded by preconditions or bounded. |
| Target expression to Julia callback | The callback implements the same log weight on the admitted domain, up to the stated numeric error. |
| IR to emitted Julia | The emitter preserves primitive order, control flow, and result conversion. |

Until these rows are discharged, the correct description is “an exact Lean
kernel with a proposal-level IR refinement, plus a tested Float64 Julia
implementation.” It is not an exact executable realization of mathlib's
continuous measure.
