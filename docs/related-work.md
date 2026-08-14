# Related work

This note records related work for the formalization of Markov chain Monte
Carlo algorithms in Lean. It is a literature map, not a claim of novelty. The
search was last updated on 2026-08-11 and covered mathlib documentation,
Isabelle's Archive of Formal Proofs, Rocq/MathComp sources, conference papers,
arXiv, and public GitHub code.

## Summary

No substantive, public, machine-checked formalization of the
Metropolis--Hastings (MH) algorithm in Lean was found in this search. There is,
however, closely related work in three categories:

1. mathematical correctness proofs for MH and trace MCMC;
2. mechanized foundations for Markov chains, stochastic matrices, and
   probability kernels; and
3. verified probabilistic-program samplers that are not themselves MCMC
   formalizations.

This negative search result should be stated cautiously: it is evidence of a
gap in the public literature surveyed here, not proof that no formalization
exists.

## Direct mathematical precedents

### Couplings for multinomial Hamiltonian Monte Carlo

Xu, Fjelde, Sutton, and Ge construct maximal and transport-based couplings for
multinomial HMC and prove geometric tails for the meeting time of a mixture
with coupled random-walk Metropolis--Hastings. Their proof proceeds through
local contractivity under a globally Lipschitz gradient and local strong
convexity, a total-variation estimate for multinomial trajectory weights, and
drift/small-set results adapted from Heng and Jacob. This paper is the primary
long-term theorem target for this repository.

- Kai Xu, Tor Erlend Fjelde, Charles Sutton, and Hong Ge,
  [Couplings for Multinomial Hamiltonian Monte Carlo](https://proceedings.mlr.press/v130/xu21i.html),
  AISTATS 2021. The proceedings page includes the paper and supplementary
  proofs.

Formalizing its main results requires more than target invariance: coupled
kernels with correct marginals, Hamiltonian and leapfrog analysis, categorical
maximal and optimal-transport couplings, drift conditions, and a geometric
meeting-time theorem must all be connected explicitly.

The formalization also exposes a quantifier issue in the paper's printed
Condition 1. It asks for a fixed contraction rate below one uniformly over all
smaller integration times. With `L=0` admitted by the direct natural-number
encoding, the transition is the identity and the inequality forces the rate
to be at least one on every nontrivial set; this contradiction is proved in
Lean. If the authors intend positive natural numbers, integration times can
still approach zero through `ε→0` at fixed positive `L`, suggesting the same
identity-limit obstruction. The repository therefore distinguishes the
verbatim statement from an explicitly labeled positive-integration-window
repair rather than presenting the latter as the published theorem.
Within that repaired interface, the formalization preserves the paper's
different moment choices: maximal coupling is developed with first-moment
distance and its linearly scaling total-variation mismatch term, while the
optimal-transport construction uses squared distance and second-moment
optimality.

### Practical Hamiltonian Monte Carlo on Riemannian manifolds

Xu and Ge introduce general-relativistic HMC (GR-HMC), combining a
position-dependent Riemannian metric with relativistic momentum to obtain a
position-dependent velocity bound.  They derive a generalized Hamiltonian,
implicit generalized-leapfrog updates, efficient derivative expressions, and
a proposed multivariate momentum sampler.

- Kai Xu and Hong Ge,
  [Practical Hamiltonian Monte Carlo on Riemannian Manifolds via Relativity
  Theory](https://proceedings.mlr.press/v235/xu24i.html), ICML 2024.

The paper's validity discussion is informal and delegates generalized-
leapfrog and correction correctness to established techniques.  A
machine-checked development must expose solvability, measurability,
reversibility, and volume preservation of the selected implicit update before
deducing target invariance.

There is also a dimension-sensitive issue in the printed momentum sampler.
Equation (10) derives the two-dimensional radial Jacobian, while Algorithm 1
reuses that law in general dimension and samples spherical angles
independently and uniformly.  In dimensions greater than two the radial
Jacobian is `r^(d-1)`, and uniform spherical direction is not produced by
independent uniform coordinate angles.  The formalization roadmap therefore
separates the printed construction from a corrected radial/uniform-direction
pushforward whose distributional correctness must be proved.

Under the paper's stated factorization `AᵀA = G⁻¹`, the affine assignment at
the end of Algorithm 1 also requires an inverse: transporting an isotropic
draw `z` by `p=A⁻¹z` gives the desired quadratic form `‖Ap‖²=‖z‖²`.  The
printed `p=Aᵀz` is not equivalent for a general metric.  The corrected
formalization uses an invertible continuous factor and its inverse explicitly.

The initial algebra audit also distinguishes the mass argument and velocity
bound printed after Equation (9) from the derivative of Equation (8).  For a
factor `AᵀA = G⁻¹`, the kinetic quadratic form is `‖Ap‖²`, while the velocity
numerator is `G⁻¹p`; these cannot generally be collapsed to the printed norm
ratio for an anisotropic metric.  The formalization uses the direct bound
`c‖G⁻¹p‖/‖Ap‖` and reserves the paper's simpler expression for cases where
additional structure proves it.

### A categorical account of Metropolis--Hastings

Cornish and Wang give an abstract account of MH in Markov categories. They
formulate invariance and reversibility categorically and derive necessary and
sufficient conditions under which general MH-type samplers are reversible.
This is probably the closest conceptual precedent for a future abstract Lean
interface, especially for involutive variants of MH. The publication page does
not list a proof-assistant development.

- Robert Cornish and Yuyang Wang, [A Categorical Account of the
  Metropolis-Hastings Algorithm](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.LICS.2026.32),
  LICS 2026.

### Correct samplers for probabilistic programs

Hur, Nori, Rajamani, and Samuel prove correctness of an MCMC sampler for
probabilistic programs, including the bookkeeping required when executions
have changing sets of random choices. This is an algorithmic correctness
precedent, but the published result is a conventional mathematical proof
rather than a machine-checked artifact.

- Chung-Kil Hur, Aditya Nori, Sriram Rajamani, and Selva Samuel,
  [A Provably Correct Sampler for Probabilistic
  Programs](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSTTCS.2015.475),
  FSTTCS 2015.

Borgström, Dal Lago, Gordon, and Szymczak formalize trace MCMC for a
probabilistic lambda calculus. Their paper proves properties including
irreducibility and aperiodicity and then establishes convergence in total
variation to the target semantics. This is especially relevant when the
project moves beyond stationarity to convergence.

- Johannes Borgström, Ugo Dal Lago, Andrew D. Gordon, and Marcin Szymczak,
  [A Lambda-Calculus Foundation for Universal Probabilistic
  Programming](https://andrewdgordon.github.io/papers/lambda-calculus-foundation-universal-probabilistic-programming.pdf),
  ICFP 2016.

Ścibior and collaborators develop denotational semantics for higher-order
Bayesian inference using quasi-Borel spaces. Their validation includes a
general Metropolis--Hastings--Green result and trace-MH validity. It provides a
useful mathematical reference for a later general-state development involving
measures and Radon--Nikodym derivatives.

- Adam Ścibior et al., [Denotational Validation of Higher-Order Bayesian
  Inference](https://www.cs.ox.ac.uk/people/samuel.staton/papers/popl2018.pdf),
  POPL 2018.

## Mechanized foundations

### Lean and mathlib

Mathlib already has the measure-theoretic concepts that should eventually
receive the finite construction in this repository:

- [`ProbabilityTheory.Kernel.Invariant` and
  `ProbabilityTheory.Kernel.IsReversible`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Invariance.html),
  including the generic implication from reversibility to invariance;
- [irreducibility of probability
  kernels](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Irreducible.html),
  expressed using positivity of iterated kernels; and
- the general [kernel definitions and
  constructions](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Defs.html).

Etienne Marion's formalization of the Ionescu--Tulcea theorem constructs the
law of an infinite Markov trajectory in mathlib. It supplies relevant
infrastructure for reasoning about a chain as a stochastic process rather
than only about its one-step transition kernel.

- Etienne Marion, [A Formalization of the Ionescu--Tulcea Theorem in
  Mathlib](https://arxiv.org/abs/2506.18616), 2025.

The current finite interface deliberately proves the elementary algebra
directly. It overlaps with the concepts above but not with an existing Lean MH
correctness theorem found by this search. A bridge from the finite interface
to `ProbabilityTheory.Kernel` would let later results reuse mathlib's general
theory.

### Isabelle/HOL

The Isabelle Archive of Formal Proofs contains substantial Markov-chain
infrastructure, although the surveyed entries do not formalize MH itself:

- Hölzl and Nipkow's [Markov
  Models](https://isa-afp.org/entries/Markov_Models.html) develops discrete-time
  Markov chains, Markov decision processes, and classification of states.
- Thiemann's [Stochastic Matrices and the Perron--Frobenius
  Theorem](https://isa-afp.org/entries/Stochastic_Matrices.html) treats
  finite-state stochastic matrices and proves existence of stationary
  distributions and uniqueness under irreducibility.

These developments are close precedents for the finite algebraic layer and
for a future finite-state convergence theorem.

### Rocq/Coq

MathComp Analysis mechanizes measure theory for kernels, including s-finite
kernels used in semantics of probabilistic programs. It is relevant to the
architecture of a general-state formalization but does not provide an MH
correctness theorem.

- Affeldt, Cohen, and Saito, [`kernel.v` in MathComp
  Analysis](https://github.com/math-comp/analysis/blob/master/theories/kernel.v).

Bagnall, Stewart, and Banerjee's Zar compiler is a fully verified Coq pipeline
from probabilistic programs with loops and conditioning to executable
random-bit samplers. It is a useful precedent for end-to-end implementation
correctness and extraction, but it is not an MCMC algorithm.

- Alexander Bagnall, Gordon Stewart, and Anindya Banerjee,
  [Formally Verified Samplers from Probabilistic Programs with Loops and
  Conditioning](https://software.imdea.org/~ab/Publications/bagnallSB_pldi23.pdf),
  PLDI 2023.

## Implications for this repository

The current theorem establishes that the finite-state MH transition is a
Markov kernel, satisfies detailed balance, and has the requested target as a
stationary distribution. Detailed balance and stationarity alone do **not**
show that the chain converges to that distribution from every initial state.

A natural progression is:

1. retain the elementary finite proof as a transparent reference result;
2. embed finite distributions and transition matrices into mathlib's
   measure-theoretic `ProbabilityTheory.Kernel` API;
3. connect finite detailed balance to `Kernel.IsReversible` and obtain
   invariance using the library theorem;
4. add irreducibility and aperiodicity hypotheses and prove a finite-state
   convergence theorem; and
5. generalize MH to measurable state spaces using measures, densities, or
   Radon--Nikodym derivatives.

Accordingly, descriptions of the current result should use terms such as
"finite-state MH stationarity" or "detailed-balance correctness." Claims of
"MCMC convergence" should be reserved for a theorem that includes the needed
ergodicity hypotheses and a specified mode of convergence.
