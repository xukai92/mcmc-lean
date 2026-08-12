# Development log

This file records completed milestones, current limitations, and likely next
steps. It is descriptive rather than a promise about release dates.

## Next steps

1. Add finite distribution evolution, kernel powers, and stationarity under
   iteration.
2. Formalize finite-state irreducibility, primitivity, and aperiodicity.
3. Derive a finite-state convergence theorem with explicit ergodicity
   hypotheses and a specified mode of convergence.
4. Generalize the MH construction to measure-theoretic state spaces.

## 2026-08-11: finite stochastic-matrix interoperability

The elementary `MarkovKernel` is now equivalent to mathlib's subtype of real
row-stochastic matrices. This milestone added:

- the transition-matrix view and its row-stochasticity proof;
- conversions in both directions and an equivalence theorem;
- the characterization of local stationarity as the row-vector equation
  `pi * P = pi`;
- agreement between matrix entries and measure-kernel singleton transition
  probabilities; and
- a two-state MH instantiation of the row-stochastic matrix result.

Together with the preceding PMF, measure, and kernel bridge, this completes
the first roadmap phase. Matrix-based dynamics should now reuse mathlib rather
than grow into a parallel local theory.

## 2026-08-11: finite measure-kernel interoperability

The finite elementary interface now embeds into mathlib's measure-theoretic
probability APIs. This milestone added:

- conversion of a local finite `Distribution` to a mathlib `PMF` and
  probability `Measure`;
- conversion of every transition row to a `PMF`;
- conversion of a local `MarkovKernel` to a
  `ProbabilityTheory.Kernel`, with an `IsMarkovKernel` instance;
- singleton and finite-set evaluation lemmas connecting the embedded objects
  to their original real-valued masses and probabilities;
- a finite double-sum proof that local pointwise detailed balance implies
  mathlib's setwise `Kernel.IsReversible` predicate;
- invariance of the embedded target via mathlib's generic theorem that
  reversibility implies invariance; and
- a two-state MH instantiation of the measure-kernel invariance result.

This bridge does not add a convergence theorem. It makes mathlib's kernel
composition, powers, irreducibility, and trajectory infrastructure available
to subsequent phases.

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
- At this milestone the local finite kernel had not yet been embedded into
  mathlib; that limitation has since been removed by the interoperability
  modules.
- The result proves stationarity, not convergence from arbitrary starting
  states. No irreducibility or aperiodicity theorem has been added yet.

Supporting repository work in this milestone included the initial Lake
project, a related-work survey, and coding-agent workflow instructions.
