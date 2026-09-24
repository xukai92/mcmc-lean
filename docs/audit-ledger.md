# Audit ledger

Machine-readable classified ledger of formal audits of published MCMC claims,
scoped to proposed contributions. The counts here track only each
paper's **proposed** contributions -- the algorithms, constructions, and
theorems the paper itself introduces. Two categories are excluded from the
counts and moved to the "Excluded" section below:

- **dependency**: a standard tool a paper merely builds on but did not propose
  (e.g. the generalized-leapfrog integrator in Xu & Ge 2024, imported from
  Riemannian HMC; a discrete joint-matrix categorical draw in Xu et al. 2021).
- **writing**: a typographical error or a prose/reasoning slip (e.g. a printed
  `∇q H` that should be `∇p H`).

Refinement rules applied:

- When a prose reasoning slip is **load-bearing for a proposed result**, the
  result is classified **proved-with-hypotheses** under the omitted hypothesis
  rather than listed as a separate correction (e.g. Xu & Ge 2024 Section 5.2
  "symmetry is sufficient" folds into the validity claim, which requires
  factor-volume compatibility).
- **De-duplication**: the same underlying issue stated in several
  equations/algorithms is ONE finding (e.g. Xu & Ge 2024 Eqs. (10)-(11) and
  Algorithm 1 are one polar-sampler correction).

Status codes are unchanged from the original ledger: **proved**,
**proved-with-hypotheses**, **corrected**, **obstructed**, **conditional**,
**out-of-scope**, **no-defect**.

Scope codes: **proposed** (retained, counted), **dependency** (excluded),
**writing** (excluded), **background/empirical** (out-of-scope, excluded).

## Ledger (proposed contributions only)

| paper | claim | lean_identifiers | file | classification | scope | note |
|-------|-------|-----------------|------|----------------|-------|------|
| xu2021 | Algorithm 1: coupled chain construction | `laggedInitialMeasure`, `lawAtTime`, `pathKernel`, `pathLaw` | Kernel/CoupledChain.lean | proved | proposed | Initialization, coupled evolution, marginals, path laws |
| xu2021 | Algorithm 2: coupled multinomial HMC | `maximalSharedMomentumCoupledPositionMultinomialHMC`, coupling theorem | Hamiltonian/CoupledMultinomialHMC.lean | proved | proposed | Both marginals are the invariant HMC kernel |
| xu2021 | Algorithm 3: coupled Gaussian RWMH | `coupledGaussianRandomWalkMetropolisHastings_isCoupling` | Kernel/GaussianProposalCoupling.lean | proved | proposed | Maximal coupling, shared uniform, both marginals verified |
| xu2021 | Algorithm 5: marginal repair | `maximallyMarginalRepairedCoupling_isCoupling` | Finite/MarginalRepair.lean | proved | proposed | Maximal retained weight, residual product, unchanged valid coupling |
| xu2021 | Algorithm 6: maximal categorical coupling | `maximalCoupling_isMaximal`, `IsMaximalCoupling.mismatchMass_eq_totalVariation` | Finite/Coupling.lean | proved | proposed | Mismatch probability = total variation |
| xu2021 | Assumptions 1-2: regular potential and local strong convexity | `RegularPotential`, `LocalStrongConvexity` | Hamiltonian/Assumptions.lean | proved | proposed | Formalized with distinguished hypotheses |
| xu2021 | Condition 1: contraction rate | `XuCondition1`, `XuCondition1AtExponent` | Hamiltonian/LocalContractivity.lean | corrected | proposed | Printed version includes L=0 making it trivially impossible; repaired with positive integration-time window |
| xu2021 | Proposition 4.1: relaxed meeting accessibility | `LocalStrongConvexity.exists_maximalSharedMomentum_isRelaxedMeetingAccessible` | Hamiltonian/LocalContractivity.lean | proved-with-hypotheses | proposed | Uses corrected cutoff-wise contraction, not printed Condition 1 |
| xu2021 | Lemma 4.1: maximal coupling contraction | contraction and relaxed-entry results | Hamiltonian/LocalContractivity.lean | proved-with-hypotheses | proposed | Uses corrected positive-window quantifiers |
| xu2021 | Lemma 4.2: leapfrog contraction | `LocalStrongConvexity.exists_uniform_exactFlow_contraction` | Hamiltonian/ExactFlow.lean | proved | proposed | Exact-flow and numerical leapfrog on compact regions |
| xu2021 | Proposition 4.2: trajectory weight bounds | `RegularPotential.xuProposition42AllOrigins`, `RegularPotential.xuProposition42RandomizedMaximalMismatch` | Hamiltonian/TrajectoryWeightBounds.lean | proved | proposed | Uniform on compact position and bounded-momentum families |
| xu2021 | Lemma 4.3: maximal coupling cost | `maximalTrajectoryIndexCoupling_cost_le_add_totalVariation_mul` | Hamiltonian/LocalContractivity.lean | conditional | proposed | Exponent-two route obstructed by scalar Gaussian short-time counterexample |
| xu2021 | Lemma 4.4: optimal transport cost | `transportTrajectoryIndexCoupling_minimal` | Hamiltonian/LocalContractivity.lean | conditional | proposed | Inherits maximal-coupling bound; unconditional exponent-two not proved |
| xu2021 | Theorem 4.1: geometric meeting tail | `XuTheorem41DriftAssumptions.exists_geometric_exactLagOneMeetingTail_stickyHmcRwmh` | Hamiltonian/CoupledMixture.lean:1661 | proved-with-hypotheses | proposed | Requires target-specific drift certificate for the concrete kernels |
| xu2024 | Eq. (8): GR kinetic energy | `riemannianRelativisticKineticEnergy`, `generalRelativisticHamiltonian` | Relativistic/Hamiltonian.lean | proved | proposed | Includes logDet/2 term and conditional density |
| xu2024 | Eq. (9): velocity and finite-speed bound | `riemannianRelativisticVelocity`, corrected euclidean-norm velocity bound, `printedEquation9_ratio_lt_correctedRatio` (2D counterexample) | Relativistic/Riemannian.lean, Relativistic/Hamiltonian.lean | proved-with-hypotheses | proposed | Corrected velocity `G⁻¹p/M` and its bound proved; printed anisotropic display superseded. (The `∇q H`→`∇p H` slip is a typo, excluded; the substantive finite-speed property holds in corrected form.) |
| xu2024 | Eqs. (10)-(11) + Algorithm 1: polar momentum sampler | `relativisticPolarMomentumMeasure_eq_cartesian`, `euclideanRelativisticPolarMomentumMeasure_eq`, `relativisticRadialWeight_three_at_two_ne_printed` | Relativistic/Momentum.lean | corrected | proposed | THE genuine correction (de-duplicated): radial Jacobian is `r^(d-1)` not `r` (printed `r` valid only for d=2); direction is uniform spherical, not independent angles; factor transport is `A⁻¹z` not `Aᵀz`. Corrected construction proved |
| xu2024 | Eq. (12): position derivative | `fderiv_riemannianRelativisticKineticEnergy_position_apply`, diagonal SoftAbs certificate | Relativistic/Derivatives.lean | proved | proposed | Two-term inverse-mass/trace formula |
| xu2024 | Eq. (13): momentum derivative | `fderiv_generalRelativisticHamiltonian_momentum_apply` | Relativistic/Derivatives.lean | proved-with-hypotheses | proposed | Requires bilinear form hypothesis AᵀA = G⁻¹ |
| xu2024 | Section 5.2: GR-HMC kernel invariance / validity | `endpointMetropolisGRHMC_isReversible`, `endpointMetropolisGRHMC_invariant`, `multinomialGRHMCPhase_invariant`, `positionEndpointMetropolisGRHMC_invariant` | Relativistic/EndpointMetropolis.lean, Relativistic/Multinomial.lean | proved-with-hypotheses | proposed | Folds the "symmetry is sufficient" reasoning slip: invariance requires factor-volume compatibility, measurable conditional momentum law, and a valid Metropolis/multinomial correction, not symmetry alone |
| xu2024 | Diagonal SoftAbs metric | `softAbs`, positivity, differentiability, AᵀA=G⁻¹ | Relativistic/SoftAbs.lean | proved | proposed | Implicit-solver certificate remains conditional |
| livingstone2022barker | Barker acceptance ratio satisfies detailed balance | `barkerAcceptedFlow_swap`, `barkerDensityAcceptedKernel_isReversible` | Kernel/BarkerAcceptance.lean | proved | proposed | Product-over-sum flow is manifestly symmetric |
| livingstone2022barker | Barker MH kernel is a valid Markov kernel | `barkerDensityMetropolisHastings_isMarkov` | Kernel/BarkerAcceptance.lean | proved | proposed | Markov property via completion framework |
| livingstone2022barker | Barker MH preserves target measure | `barkerDensityMetropolisHastings_invariant` | Kernel/BarkerAcceptance.lean | proved | proposed | Follows from reversibility |
| livingstone2022barker | Sigmoid bridge (log-space acceptance) | `barkerLogDensityAcceptance_eq_sigmoid` | Executable/Continuous/BarkerRWMH.lean | proved | proposed | r/(1+r) = 1/(1+exp(-log r)) |
| livingstone2022barker | Executable refinement | `gaussianBarkerRwmhProgramKernel_refines` | Executable/Continuous/BarkerRWMH.lean | proved | proposed | IR program = mathematical kernel |
| turok2025drghmc | AR(1) momentum refresh is a valid Markov kernel | `ar1MomentumKernel_isMarkov` | Hamiltonian/DelayedRejection.lean | proved | proposed | IsMarkovKernel when α²+β²=1; Gaussian invariance not proved |
| turok2025drghmc | Stage-1 proposal is an involution | `drStage1Endpoint_involutive` | Hamiltonian/DelayedRejection.lean | proved | proposed | momentumFlip ∘ leapfrog is involutive |
| turok2025drghmc | Stage-1 and stage-2 maps are volume-preserving | `measurePreserving_drStage1Endpoint`, `measurePreserving_drStage2Proposal` | Hamiltonian/DelayedRejection.lean | proved | proposed | Composition of existing volume-preservation results |
| turok2025drghmc | Ghost path reconstruction identity | `drGhostPath_of_drStage2Proposal` | Hamiltonian/DelayedRejection.lean | proved | proposed | Ghost path from stage-2 endpoint recovers original |
| turok2025drghmc | Stage-1 kernel preserves Boltzmann target | `drStage1PhaseKernel_invariant` | Hamiltonian/DelayedRejection.lean | proved | proposed | Via deterministic Metropolis + volume preservation |
| turok2025drghmc | DR acceptance correction (ghost factor) | `drStage2Acceptance` | Hamiltonian/DelayedRejection.lean | proved | proposed | (1-a₁_ghost)/(1-a₁) correction is well-defined |
| turok2025drghmc | Full DR-G-HMC preserves phase-space target | `drGhmc_stage1_invariant` | Hamiltonian/DelayedRejection.lean | proved-with-hypotheses | proposed | Stage-1 invariance proved; full two-stage composition documented as obligation |
| turok2025drghmc | Executable refinement | `scalarDrGhmcTransition_position_eq` | Executable/Continuous/DRGHMC.lean | proved | proposed | IR interpreter replay = mathematical transition |
| nishimura2020dhmc | Exact energy preservation (coordinatewise crossing/reflection) | `discontinuousCoordinateStep_energy` | Hamiltonian/Discontinuous.lean:61 | proved | proposed | Scalar Laplace-momentum coordinate update preserves total energy |
| nishimura2020dhmc | Reflection involutivity | `discontinuous_reflect_reflect` | Hamiltonian/Discontinuous.lean:75 | proved | proposed | Double reflection returns to original phase state |
| nishimura2020dhmc | Crossing probability = MH acceptance | `expMeasure_crossing_probability_eq_mh_acceptance` | Hamiltonian/DiscontinuousMetropolis.lean:54 | proved | proposed | Exponential-measure crossing probability equals the target ratio acceptance |
| nishimura2020dhmc | One-step kernel target invariance | `oneStepDiscontinuousKernel_stationary` | Hamiltonian/DiscontinuousMetropolis.lean:79 | proved | proposed | Single-coordinate discontinuous HMC kernel preserves target |
| nishimura2020dhmc | Volume preservation of the multi-coordinate integrator | — | — | conditional | proposed | Requires measure-theoretic volume-preservation theorem for the composed coordinatewise updates |
| nishimura2020dhmc | Full kernel invariance (all coordinates) | — | — | conditional | proposed | Requires composed multi-coordinate kernel + momentum refreshment formalization |
| zhou2020mixed | MH correction term (proceedings version) | — | — | corrected | proposed | Proceedings used incorrect MH correction due to supplementary lemma error; author acknowledged and fixed on arXiv |
| zhou2020mixed | MH correction term (arXiv/corrected version) | — | — | conditional | proposed | Corrected term needs formalization; classified as conditional pending Lean implementation |
| zhou2020mixed | Detailed balance of mixed discrete/continuous transition | — | — | conditional | proposed | Requires formalization of the embedded discrete/continuous target and the mixed HMC kernel |
| geyer1991 | Product-target invariance (finite, 2 temperatures) | `ParallelTempering.stationary` | Finite/ParallelTempering.lean | proved | proposed | Within-updates + MH swap preserves product distribution |
| geyer1991 | Cold marginal projection | `ParallelTempering.cold_marginal` | Finite/ParallelTempering.lean | proved | proposed | First marginal of product target is cold distribution |
| geyer1991 | Product-target invariance (general-state, K temperatures) | `pairSwapKernel_invariant` | Kernel/ParallelTempering.lean | proved-with-hypotheses | proposed | Pair swap kernel invariance proved; full SEO/DEO composition invariance blocked on pi-withDensity bridge lemma |
| geyer1991 | Swap kernel detailed balance (general-state) | `pairSwapKernel_isReversible` | Kernel/ParallelTempering.lean:198 | proved | proposed | Pairwise swap kernel satisfies detailed balance w.r.t. product target |
| geyer1991 | Swap coordinate involutivity | `swapCoord_involutive` | Kernel/ParallelTempering.lean:100 | proved | proposed | Swapping twice returns to original |
| geyer1991 | Swap coordinate measure preservation | `swapCoord_measurePreserving` | Kernel/ParallelTempering.lean:153 | proved | proposed | Swap preserves the product density target |
| syed2022nrpt | SEO kernel definition (stochastic even-odd) | `seoKernel` | Kernel/ParallelTempering.lean:321 | proved | proposed | 50-50 mixture of even and odd swap kernels, defined |
| syed2022nrpt | DEO kernel definition (deterministic even-odd) | `deoKernel` | Kernel/ParallelTempering.lean:329 | proved | proposed | Deterministic alternation even-odd, defined |
| syed2022nrpt | SEO/DEO invariance | — | — | conditional | proposed | Definitions complete; invariance proof blocked on pi-withDensity bridge lemma connecting Measure.pi to withDensity |
| syed2022nrpt | DEO non-reversibility | — | — | conditional | proposed | DEO kernel defined; non-reversibility proof requires the invariance bridge first |
| zoltowski2025parallel | Sequential-parallel equivalence of Newton fixed-point | — | — | conditional | proposed | Deterministic refinement claim; requires formalization of the Newton iteration and convergence proof |
| zoltowski2025parallel | Exact chain reproduction (no approximation error) | — | — | conditional | proposed | Requires proof that the fixed-point solver converges to the exact sequential solution |

## Excluded from proposed-contribution counts

### Dependencies (standard tools the paper builds on but did not propose)

| paper | claim | scope | reason |
|-------|-------|-------|--------|
| xu2021 | Algorithm 4: sample a discrete joint matrix | dependency | A standard categorical-sampling utility (flatten a joint matrix and call `Cat`), not a novel contribution of the paper. Represented extensionally as a joint PMF; no defect, but not a proposed result. Was counted no-defect (Conf.); now excluded |
| xu2024 | Eq. (3): multivariate special-relativistic kinetic energy | dependency | The special-relativistic kinetic energy is prior work (relativistic HMC, Lu et al. 2017); the paper's novelty is the general-relativistic/Riemannian extension (Eq. 8). Proved (`relativisticKineticEnergy`), but a building block, not proposed. Was counted Conf.; now excluded |
| xu2024 | Eqs. (6)-(7): generalized leapfrog integrator | dependency | The implicit generalized-leapfrog integrator is imported from Riemannian HMC (Girolami & Calderhead; Lan et al.), not proposed here. The "six fixed-point iterations need not solve the equations" observation (`finiteFixedPointGeneralizedLeapfrog_six_not_satisfies`) is a solver/implementation point about a dependency. Was counted Corr.; now excluded |

### Writing-level issues (typographical or prose slips)

| paper | claim | scope | reason |
|-------|-------|-------|--------|
| xu2024 | Eq. (9): printed `∇q H` velocity | writing | Typographical: the velocity is `∇p H`, not the printed `∇q H`. Excluded as a typo; the substantive finite-speed velocity bound is retained above as proved-with-hypotheses in corrected form. Was part of a Corr. row; the typo itself is now excluded |
| xu2024 | Section 5.2: "symmetry is sufficient" remark | writing (folded) | Load-bearing prose reasoning slip: rather than a separate correction, it is folded into the GR-HMC validity/invariance claim above, which is classified proved-with-hypotheses (needs factor-volume compatibility). Was counted Corr.; now folded |

### Background / empirical (out-of-scope, unchanged from original)

| paper | claim | scope |
|-------|-------|-------|
| xu2024 | Eq. (1): Hamilton's equations (continuous-time ODE) | background |
| xu2024 | Eq. (2): Gaussian RHMC kinetic energy | background |
| xu2024 | Eq. (4): dimension-wise kinetic energy | background/empirical |
| xu2024 | Eq. (5): Gaussian RHMC derivatives | background |
| zhou2020mixed | Q_i(x\|x)=0 requirement for correctness | design constraint, not a theorem |
| nishimura2020dhmc | Connection to zig-zag sampler | theoretical comparison |
| syed2022nrpt | Round-trip rate bounds | requires mixing-time analysis |
| zoltowski2025parallel | O(log T) parallel complexity | complexity claim, not correctness |
| surjanovic2022varpt | Variational/generalized PT | requires adaptation theory |
| surjanovic2025pigeons | Distributed parallelism invariance | systems claim |

## Re-scoped per-paper tallies (proposed contributions only)

| paper | claims | confirmed | refined | corrected | change vs. original |
|-------|--------|-----------|---------|-----------|---------------------|
| Xu et al. 2021 | 14 | 8 | 5 | 1 | 15/9/5/1 → 14/8/5/1 (Alg. 4 dependency removed) |
| Xu & Ge 2024 | 7 | 3 | 3 | 1 | 10/4/1/5 → 7/3/3/1 (Eq. 3 & leapfrog dependencies, ∇ typo, and validity slip removed/refolded; polar sampler de-duplicated to one) |
| Barker RWMH | 5 | 5 | 0 | 0 | unchanged |
| DR-G-HMC | 8 | 7 | 1 | 0 | unchanged |
| Discontinuous HMC | 6 | 4 | 2 | 0 | unchanged |
| Mixed HMC | 3 | 0 | 2 | 1 | unchanged |
| Parallel tempering (Geyer) | 6 | 5 | 1 | 0 | unchanged |
| Non-reversible PT (Syed) | 4 | 2 | 2 | 0 | unchanged |
| Parallel-across-length | 2 | 0 | 2 | 0 | unchanged |
| Variational / distributed PT | out of scope | — | — | — | unchanged |

Confirmed = proved or no-defect; Refined = proved-with-hypotheses or
conditional; Corrected = corrected or a proved counterexample/obstruction.
Corrections still span three distinct works (Xu et al. 2021, Xu & Ge 2024,
Mixed HMC), preserving the honest multi-author picture.
