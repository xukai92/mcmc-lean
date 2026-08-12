# mcmc-lean

Machine-checked correctness proofs for Markov chain Monte Carlo algorithms in
Lean 4.

> **Status:** early-stage research project. The current development proves
> finite-state Metropolis--Hastings stationarity, not convergence from an
> arbitrary initial distribution.

## What is formalized

For a finite state space, a strictly positive target distribution, and an
arbitrary proposal Markov kernel, the library constructs the corresponding
Metropolis--Hastings transition kernel and proves that it:

- is a valid Markov kernel;
- satisfies detailed balance; and
- has the target as a stationary distribution.

The proof uses the symmetric accepted flow

```text
min (π(x) q(x,y)) (π(y) q(y,x)),
```

and proves that it agrees with the usual acceptance-ratio formulation. A
[two-state example](McmcLean/Examples/TwoState.lean) instantiates the generic
result on `Bool`.

The elementary finite distributions and kernels also embed into mathlib's
`PMF`, `Measure`, and `ProbabilityTheory.Kernel` APIs. Under this embedding,
the local pointwise detailed-balance theorem gives mathlib's setwise
reversibility and hence kernel invariance.

## Status summary

| Area | Status | Current theorem surface or next goal |
|---|---|---|
| Finite Markov kernels | Proved | Normalization, detailed balance, stationarity, and detailed balance implies stationarity |
| Finite Metropolis--Hastings | Proved | Valid transition kernel, acceptance-ratio equivalence, detailed balance, and target stationarity |
| Mathlib interoperability | Proved | Bridges to PMFs, measures, measure kernels, and row-stochastic matrices |
| Finite-chain dynamics | In progress | One-step evolution and stationary fixed points proved; powers are next |
| Finite-chain convergence | Planned | Irreducibility, aperiodicity, total-variation convergence, and quantitative bounds |
| Further algorithms | Planned | Gibbs, independence MH, random-walk MH, block MH, mixtures, and compositions |
| General-state and executable MCMC | Long term | Measurable-state MH, executable refinement, approximation bounds, and statistical guarantees |

The full dependency-ordered plan, phase markers, and exit criteria are in the
[`roadmap`](docs/roadmap.md). In particular, the current stationarity result
is not yet a theorem of convergence from arbitrary initial distributions.

## Getting started

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake update
lake exe cache get
lake build
```

The repository pins Lean and mathlib to `v4.32.1`.

## Project guide

- [`McmcLean/Finite/MarkovKernel.lean`](McmcLean/Finite/MarkovKernel.lean):
  finite distributions, kernels, reversibility, and stationarity.
- [`McmcLean/Finite/MeasureKernel.lean`](McmcLean/Finite/MeasureKernel.lean):
  embeddings into mathlib PMFs, measures, and measure-theoretic kernels.
- [`McmcLean/Finite/MatrixKernel.lean`](McmcLean/Finite/MatrixKernel.lean):
  equivalence with mathlib row-stochastic matrices.
- [`McmcLean/Finite/Dynamics.lean`](McmcLean/Finite/Dynamics.lean): one-step
  distribution evolution and stationary fixed points.
- [`McmcLean/Finite/MetropolisHastings.lean`](McmcLean/Finite/MetropolisHastings.lean):
  the MH construction and correctness proof.
- [`docs/roadmap.md`](docs/roadmap.md): dependency-ordered research phases and
  current phase-level status.
- [`docs/development-log.md`](docs/development-log.md): completed results,
  current limitations, and roadmap.
- [`docs/related-work.md`](docs/related-work.md): related mathematical and
  mechanized work.
- [`AGENTS.md`](AGENTS.md): repository conventions for coding agents.

## License

[MIT](LICENSE)
