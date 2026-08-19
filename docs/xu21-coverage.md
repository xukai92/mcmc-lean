# Xu et al. 2021 coverage audit

This document audits the compiled Lean development against Xu, Fjelde,
Sutton, and Ge, [“Couplings for Multinomial Hamiltonian Monte
Carlo”](https://proceedings.mlr.press/v130/xu21i.html) (AISTATS 2021). It
distinguishes definitions, conditional implications, fully discharged
theorems, corrected statements, and validated examples.

The target theorem surface is complete subject to the qualifications below:
the printed inconsistent or obstructed formulations are not silently
asserted, and convergence from a Dirac start is kept separate from the
paper's geometric meeting theorem. The final list records follow-on work
rather than hidden premises of the proved meeting result.

The paper's RWMH and HMC transitions are part of the formalization. They are
not opaque kernels whose correctness is assumed. An abstract kernel theorem
counts as a reusable intermediate result, but not as a completed algorithmic
instance until its hypotheses have been proved for the concrete transition.

Status terminology is shared with the 2024 audit:

- **proved**: represented by definitions and machine-checked theorems;
- **conditional**: proved from an explicit certificate still required of a
  concrete target or implementation;
- **corrected**: the printed statement cannot be used as written and Lean
  formalizes a labeled replacement;
- **obstructed**: Lean proves a counterexample or incompatibility under the
  audited quantifiers; and
- **out of scope**: empirical, floating-point, or implementation-engineering
  claims not promoted to mathematical theorems.

## Algorithms

| Paper item | Main Lean artifacts | Status and qualification |
| --- | --- | --- |
| Algorithm 1: coupled chains | `laggedInitialMeasure`, `lawAtTime`, `pathKernel`, and `pathLaw` in `Kernel/CoupledChain.lean`; meeting events and kernel-to-path faithfulness in `Kernel/MeetingDrift.lean`; stopped-estimator, moment, and pathwise-work theorems in `Kernel/UnbiasedEstimator.lean` | The initialization, separate first update, coupled evolution, marginals, and path laws are formalized measure-theoretically. Kernel-level faithfulness implies almost-everywhere faithful paths. A geometric exact-meeting tail gives bounded-observable marginal-expectation convergence, unbiasedness for the constructed limit, `MemLp ... 2` (finite variance), finite expected correction count, and almost-surely finite pathwise correction work. More generally, a uniform `Lᵖ` path-coordinate bound with positive Hölder gap proves unbiasedness and finite variance for unbounded observables. In the stationary theorem these hypotheses reduce to one `MemLp h p target` certificate. |
| Algorithm 2: coupled HMC | `positionMultinomialHMC` and its invariance theorem in `Hamiltonian/HMC.lean`; `maximalSharedMomentumCoupledPositionMultinomialHMC`, `transportSharedMomentumCoupledPositionMultinomialHMC`, and their coupling theorems in `Hamiltonian/CoupledMultinomialHMC.lean` | Proved for the full multinomial transition: Gaussian momentum refresh, shared randomized trajectory origin, forward/backward leapfrog trajectory, and coupled multinomial selection. Both marginals are the implemented invariant HMC kernel. |
| Algorithm 3: coupled RWMH | `gaussianRandomWalkMetropolisHastings` and its Markov, reversibility, and invariance theorems; `coupledGaussianRandomWalkMetropolisHastings_isCoupling` and the Euclidean analogue | Proved as mathlib kernels. The proposal is maximally coupled, the acceptance uniform is shared, and both marginals are the verified Gaussian RWMH kernel. Local exact-meeting lower bounds are also proved. |
| Algorithm 4: sample a discrete joint matrix | finite joint laws as `PMF (Fin m × Fin n)` and their pushforwards throughout `Finite/` and `CoupledMultinomialHMC.lean` | The mathematical operation is represented extensionally and used by the kernel constructions: drawing a pair from the joint PMF has exactly that law. The paper's executable flatten-matrix-and-call-`Cat` routine is not separately implemented or code-generated. |
| Algorithm 5: repair approximate marginals | `maximallyMarginalRepairedCoupling` and `maximallyMarginalRepairedCoupling_isCoupling` in `Finite/MarginalRepair.lean`; `repairedTrajectoryIndexCoupling_isCoupling` | Proved. The maximal admissible retained weight is constructed, the residual product coupling repairs both marginals exactly, and an already valid coupling is left unchanged. Measurability needed for kernel lifting is proved. |
| Algorithm 6: maximal categorical coupling | `maximalCoupling`, `maximalCoupling_isMaximal`, and `IsMaximalCoupling.mismatchMass_eq_totalVariation` in `Finite/Coupling.lean` | Proved. The construction has the requested categorical marginals and mismatch probability equal to total variation. Its atoms are measurable as a parameterized family, enabling the concrete HMC kernel. |

## Section 4 assumptions and results

| Paper item | Main Lean artifacts | Status and qualification |
| --- | --- | --- |
| Assumptions 1 and 2 | `RegularPotential` and `LocalStrongConvexity` in `Hamiltonian/Assumptions.lean` | Formalized. The hypotheses distinguish global regularity from local strong convexity on the selected region. |
| Condition 1 | `XuCondition1`, `XuCondition1AtExponent`, positive-window and cutoff-wise variants in `Hamiltonian/LocalContractivity.lean` | The printed discrete statement is formalized, and Lean proves it impossible on any region containing two distinct points because its quantifiers include `L = 0`. Nontrivial results therefore use explicitly named positive-integration-window repairs. Compact local strong convexity proves the cutoff-wise version, which is enough for the meeting argument. |
| Proposition 4.1 | `IsRelaxedMeetingAccessibleFrom` and its composition lemmas in `Kernel/MeetingDrift.lean`; `LocalStrongConvexity.exists_maximalSharedMomentum_isRelaxedMeetingAccessible` | The kernel-level relaxed-accessibility conclusion is proved for the actual maximal shared-momentum HMC kernel, using a positive-mass momentum cutoff and the repaired cutoff-wise contraction theorem. |
| Lemma 4.1 | maximal-coupling contraction and relaxed-entry results in `Hamiltonian/LocalContractivity.lean` | Proved with the corrected positive-window/cutoff-wise quantifiers. It is not claimed under the inconsistent printed Condition 1. |
| Lemma 4.2 | `LocalStrongConvexity.exists_uniform_exactFlow_contraction` in `Hamiltonian/ExactFlow.lean` and the leapfrog contraction theorems in `Hamiltonian/LocalContractivity.lean` | The exact-flow and numerical leapfrog arguments are proved on compact local regions, yielding the cutoff-wise positive integration window used downstream. |
| Proposition 4.2 | `RegularPotential.xuProposition42AllOrigins`, `RegularPotential.xuProposition42RandomizedMaximalMismatch`, and `RegularPotential.exists_uniform_offsetTrajectory_totalVariation_lt` in `Hamiltonian/TrajectoryWeightBounds.lean` | Proved for general regular potentials, uniformly on compact position and bounded-momentum families. Both the conditional all-origins TV statement and the actual randomized-origin maximal-mismatch statement are available. |
| Lemma 4.3: maximal coupling | `maximalTrajectoryIndexCoupling_cost_le_add_totalVariation_mul` and maximal-coupling contraction results in `Hamiltonian/LocalContractivity.lean` | The finite cost decomposition and the repaired first-moment contraction route are proved. The paper's exponent-two formulation is retained as a conditional interface; a scalar Gaussian short-time obstruction prevents presenting it as an unconditional theorem under the relevant broad quantifiers. |
| Lemma 4.4: optimal transport | `transportTrajectoryIndexCoupling_minimal` and `transportTrajectoryIndexCoupling_cost_le_add_totalVariation_mul`; measurable greedy transport selector and kernel lift | The finite optimality and inheritance of any established maximal-coupling cost bound are proved. A general unconditional exponent-two contraction theorem is not proved; it remains conditional, and the scalar Gaussian obstruction is documented. |
| Theorem 4.1 | `XuTheorem41DriftAssumptions` and `exists_geometric_exactLagOneMeetingTail_stickyHmcRwmh` in `Hamiltonian/CoupledMixture.lean` | The drift/small-set implication to a geometric exact lag-one meeting tail is proved for the concrete sticky HMC/RWMH mixture. For a general target it requires the paper's target-specific drift certificate for the same selected kernels. Local strong convexity alone does not imply that global drift premise. |

## Statement corrections and obstructions

### Condition 1 requires a positive integration-time window

The direct discrete reading of printed Condition 1 includes `L = 0`, for
which the HMC transition is the identity. On any region containing two
distinct positions, Lean proves this forces the proposed contraction rate to
be at least one. Merely writing `L > 0` is insufficient if `εL` may still
approach zero while one fixed subunit rate is required.

The corrected interfaces impose

```text
0 < T_min ≤ εL ≤ T_max
```

and distinguish a single-window statement from the cutoff-wise form actually
obtained from compact local strong convexity. One fixed positive-mass kinetic
cutoff suffices for the downstream relaxed-accessibility and meeting proof.

### The unconditional exponent-two route is obstructed

For the scalar Gaussian example in the audited short-time regime, nearby
chains can assign different multinomial index masses at first order in their
initial separation, while a squared-distance contraction budget is only
second order. Lean therefore does not promote the broad unconditional
exponent-two claim to a theorem.

The completed meeting argument uses a first-moment maximal coupling, whose
total-variation mismatch has the correct scaling, together with the paper's
separate global drift premise. This changes the justified proof route, not the
implemented HMC/RWMH algorithm or the final geometric meeting conclusion.

## Fully instantiated and conditional endpoints

The strongest fully instantiated endpoint currently concerns the standard
Gaussian in every nonempty finite dimension.
`Hamiltonian/QuadraticGaussianXu.lean` supplies the target-specific HMC and
RWMH drift data, energy-region geometry, compact small set, concrete kernels,
and initialization required by the exact lag-one theorem. Lean therefore
proves a geometric exact lag-one meeting tail for that actual algorithm at
`ε = √2`, `L = 1`.
For bounded measurable observables, geometric faithful meeting now proves
that the Dirac-start marginal expectations converge. The module packages the
actual mixture into an unconditional finite-variance estimator theorem whose
expectation is this constructed limit. The standard-Gaussian target is now
also normalized explicitly, proved invariant, and coupled to the Dirac-start
chain with a geometric same-time meeting tail. This yields two-sided
eventwise geometric convergence to the normalized target. A reusable
coupling-integral inequality now transports the meeting bound to arbitrary
bounded measurable observables. A shared-parameter theorem proves both the
lag-one and stationary-target tails for one selected mixture, so the final
Gaussian endpoint proves convergence to the normalized-target integral,
unbiasedness for that same integral, and finite variance.

The general-target endpoint is a composition theorem: regularity and local
strong convexity establish local HMC accessibility, while a supplied
`XuTheorem41DriftAssumptions` certificate establishes global return. This is
faithful to the logical role of the paper's drift hypothesis, but it is not a
proof that every regular locally strongly convex target satisfies the drift
condition.

As a non-Gaussian applied target, `Hamiltonian/LogisticRegression.lean`
defines the finite-data `L²`-regularized logistic potential and its exact
gradient. Lean proves the softplus/sigmoid calculus, an explicit global
gradient-Lipschitz constant, global strong monotonicity from positive
regularization, and relaxed accessibility of the concrete maximal coupled
HMC kernel on nested compact balls. At `ε² λ = 2`, it additionally proves
exact leapfrog cancellation and an explicit energy-defect bound whose
position dependence is `-(λ/8)‖q‖²`. Lean now also proves the corresponding
capped-retention inequality, Gaussian-momentum integration, finite allowance,
and strict affine drift for the actual `L = 1` HMC kernel.
`Hamiltonian/LogisticRegressionXu.lean` constructs the compact energy region,
verifies the strict infimum/supremum geometry, assembles Xu's complete drift
record, and proves the concrete exact lag-one geometric meeting tail.
It also proves the analogous unconditional bounded-observable marginal-limit
and finite-variance estimator endpoint for the concrete regularized-logistic
mixture.
Positive quadratic coercivity now additionally proves integrability and
nonzeroness of the unnormalized logistic Boltzmann measure. The normalized
posterior is constructed as a probability measure, and the concrete mixture
is proved invariant for it. The same coercive Gaussian envelope now proves a
finite first distance moment under that normalized posterior. Consequently a
Dirac-start/stationary-start pair has finite additive Lyapunov moment, and the
concrete sticky mixture has a same-time geometric meeting tail to the actual
normalized logistic target. A shared-parameter theorem obtains this tail and
the lag-one estimator tail from one drift record. The final logistic endpoint
therefore proves convergence to the normalized-posterior integral,
unbiasedness for that same integral, and finite variance.

The following follow-on work remains outside the completed theorem surface:

- target-specific drift certificates beyond the standard Gaussian and
  regularized-logistic families;
- full floating-point refinement and reproduction of every reported paper
  experiment. The generated Julia coupling implements shared-event HMC/RWMH
  mixture steps and checks exact-meeting faithfulness. Its public replicated
  meeting-time diagnostic now reports seeded, explicitly censored observations,
  meeting fraction, observed mean, and horizon-restricted mean; a command-line
  Gaussian and finite-data regularized-logistic experiments reproduce that
  diagnostic. These use stable `softplus` and logistic-gradient evaluations
  but remain ordinary Float64 programs. This is not yet a
  reproduction of every paper experiment; and
- an unconditional exponent-two optimal-transport contraction theorem in a
  parameter regime not ruled out by the formalized obstruction.
