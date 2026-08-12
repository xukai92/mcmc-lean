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
- [`McmcLean/Finite/MetropolisHastings.lean`](McmcLean/Finite/MetropolisHastings.lean):
  the MH construction and correctness proof.
- [`docs/development-log.md`](docs/development-log.md): completed results,
  current limitations, and roadmap.
- [`docs/related-work.md`](docs/related-work.md): related mathematical and
  mechanized work.
- [`AGENTS.md`](AGENTS.md): repository conventions for coding agents.

## License

[MIT](LICENSE)
