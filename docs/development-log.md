# Development log

This file records completed milestones, current limitations, and likely next
steps. It is descriptive rather than a promise about release dates.

## Next steps

1. Connect the elementary finite kernel to mathlib's
   `ProbabilityTheory.Kernel` API.
2. Formalize finite-state irreducibility and aperiodicity.
3. Derive a finite-state convergence theorem with explicit ergodicity
   hypotheses and a specified mode of convergence.
4. Generalize the construction to measure-theoretic state spaces.

## 2026-08-11: finite-state Metropolis--Hastings stationarity

The initial development added:

- a small finite-state interface for normalized distributions and
  row-stochastic Markov kernels;
- definitions of reversibility and stationarity;
- the finite theorem that detailed balance implies stationarity;
- the MH accepted flow, acceptance probability, move probability, rejection
  mass, and transition kernel;
- proofs that move, rejection, and transition probabilities are nonnegative;
- a proof that every transition row sums to one;
- equivalence between the usual MH acceptance ratio and the symmetric-flow
  construction;
- detailed balance and target stationarity for the resulting kernel; and
- a concrete two-state example with target masses `3/4` and `1/4`.

The symmetric-flow construction is

```text
min (π(x) * q(x,y)) (π(y) * q(y,x)).
```

It makes detailed balance direct and handles zero forward or reverse proposal
probabilities without extra cases in the kernel definition.

### Current limitations

- The state space is finite.
- The target mass is assumed strictly positive at every state.
- The local finite kernel has not yet been embedded into mathlib's
  measure-theoretic kernel abstraction.
- The result proves stationarity, not convergence from arbitrary starting
  states. No irreducibility or aperiodicity theorem has been added yet.

Supporting repository work in this milestone included the initial Lake
project, a related-work survey, and coding-agent workflow instructions.
