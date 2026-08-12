# mcmc-lean

Machine-checked correctness proofs for Markov chain Monte Carlo algorithms in
Lean 4.

## Current result

`McmcLean.Finite.MetropolisHastings` defines finite-state
Metropolis–Hastings for a strictly positive target distribution and an
arbitrary proposal Markov kernel. It proves:

1. accepted and rejection probabilities are nonnegative;
2. every transition row sums to one;
3. the usual acceptance-ratio formula equals the symmetric-flow form;
4. the transition satisfies detailed balance; and
5. the target distribution is stationary.

The implementation uses the symmetric accepted-flow identity

```text
min (π(x) q(x,y)) (π(y) q(y,x)),
```

which is equivalent to the usual MH acceptance probability and avoids special
cases around zero proposal probabilities.

`McmcLean.Examples.TwoState` checks the generic result on a concrete Boolean
state space with target masses `3/4` and `1/4`.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake update
lake exe cache get
lake build
```

The repository pins Lean and mathlib to `v4.32.1`.

## Roadmap

- connect the finite algebraic kernel to `ProbabilityTheory.Kernel`;
- formalize finite-state irreducibility and aperiodicity;
- derive a finite-state convergence theorem;
- generalize the construction to measure-theoretic state spaces.
