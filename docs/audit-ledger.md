# Audit ledger

Machine-readable classified ledger of formal audits of published MCMC claims.
Each row maps a specific paper claim to the Lean identifier(s) that establish
or refute it and classifies the outcome. The paper's Table 1 is regenerable
from this file.

Status codes:
- **proved**: machine-checked theorem matches the published claim.
- **proved-with-hypotheses**: proved under added hypotheses not stated in the
  original publication.
- **corrected**: the published claim is false or inconsistent as stated; Lean
  formalizes a labeled correction.
- **obstructed**: Lean proves a counterexample or incompatibility.
- **conditional**: proved from an explicit certificate a concrete target or
  implementation must still discharge.
- **out-of-scope**: empirical, implementation, or floating-point claim not
  promoted to a mathematical theorem.
- **no-defect**: audited and found to match the published statement.

## Ledger

| paper | claim | lean_identifiers | file | classification | note |
|-------|-------|-----------------|------|----------------|------|
| xu2021 | Algorithm 1: coupled chain construction | `laggedInitialMeasure`, `lawAtTime`, `pathKernel`, `pathLaw` | Kernel/CoupledChain.lean | proved | Initialization, coupled evolution, marginals, path laws |
| xu2021 | Algorithm 2: coupled multinomial HMC | `maximalSharedMomentumCoupledPositionMultinomialHMC`, coupling theorem | Hamiltonian/CoupledMultinomialHMC.lean | proved | Both marginals are the invariant HMC kernel |
| xu2021 | Algorithm 3: coupled Gaussian RWMH | `coupledGaussianRandomWalkMetropolisHastings_isCoupling` | Kernel/GaussianProposalCoupling.lean | proved | Maximal coupling, shared uniform, both marginals verified |
| xu2021 | Algorithm 5: marginal repair | `maximallyMarginalRepairedCoupling_isCoupling` | Finite/MarginalRepair.lean | proved | Maximal retained weight, residual product, unchanged valid coupling |
| xu2021 | Algorithm 6: maximal categorical coupling | `maximalCoupling_isMaximal`, `IsMaximalCoupling.mismatchMass_eq_totalVariation` | Finite/Coupling.lean | proved | Mismatch probability = total variation |
| xu2021 | Assumptions 1-2: regular potential and local strong convexity | `RegularPotential`, `LocalStrongConvexity` | Hamiltonian/Assumptions.lean | proved | Formalized with distinguished hypotheses |
| xu2021 | Condition 1: contraction rate | `XuCondition1`, `XuCondition1AtExponent` | Hamiltonian/LocalContractivity.lean | corrected | Printed version includes L=0 making it trivially impossible; repaired with positive integration-time window |
| xu2021 | Proposition 4.1: relaxed meeting accessibility | `LocalStrongConvexity.exists_maximalSharedMomentum_isRelaxedMeetingAccessible` | Hamiltonian/LocalContractivity.lean | proved-with-hypotheses | Uses corrected cutoff-wise contraction, not printed Condition 1 |
| xu2021 | Lemma 4.1: maximal coupling contraction | contraction and relaxed-entry results | Hamiltonian/LocalContractivity.lean | proved-with-hypotheses | Uses corrected positive-window quantifiers |
| xu2021 | Lemma 4.2: leapfrog contraction | `LocalStrongConvexity.exists_uniform_exactFlow_contraction` | Hamiltonian/ExactFlow.lean | proved | Exact-flow and numerical leapfrog on compact regions |
| xu2021 | Proposition 4.2: trajectory weight bounds | `RegularPotential.xuProposition42AllOrigins`, `RegularPotential.xuProposition42RandomizedMaximalMismatch` | Hamiltonian/TrajectoryWeightBounds.lean | proved | Uniform on compact position and bounded-momentum families |
| xu2021 | Lemma 4.3: maximal coupling cost | `maximalTrajectoryIndexCoupling_cost_le_add_totalVariation_mul` | Hamiltonian/LocalContractivity.lean | conditional | Exponent-two route obstructed by scalar Gaussian short-time counterexample |
| xu2021 | Lemma 4.4: optimal transport cost | `transportTrajectoryIndexCoupling_minimal` | Hamiltonian/LocalContractivity.lean | conditional | Inherits maximal-coupling bound; unconditional exponent-two not proved |
| xu2021 | Theorem 4.1: geometric meeting tail | `XuTheorem41DriftAssumptions.exists_geometric_exactLagOneMeetingTail_stickyHmcRwmh` | Hamiltonian/CoupledMixture.lean:1661 | proved-with-hypotheses | Requires target-specific drift certificate for the concrete kernels |
| xu2021 | Algorithm 4: joint matrix sampling | finite joint laws as PMF | Finite/ | no-defect | Mathematical operation represented extensionally; executable routine out of scope |
| xu2024 | Eq. (3): relativistic kinetic energy | `relativisticKineticEnergy`, `relativisticMass` | Relativistic/Kinetic.lean | proved | Positivity and strict speed bound proved |
| xu2024 | Eq. (6)-(7): generalized leapfrog | `GeneralizedLeapfrogEquations`, `IsValid` | Relativistic/GeneralizedLeapfrog.lean | corrected | Exact interface proved; 6 iterations need not solve equations (`finiteFixedPointGeneralizedLeapfrog_six_not_satisfies`) |
| xu2024 | Eq. (8): GR kinetic energy | `riemannianRelativisticKineticEnergy`, `generalRelativisticHamiltonian` | Relativistic/Hamiltonian.lean | proved | Includes logDet/2 term and conditional density |
| xu2024 | Eq. (9): velocity and bound | `riemannianRelativisticVelocity`, `euclideanNorm_riemannianRelativisticVelocity_lt` | Relativistic/Derivatives.lean | corrected | Printed ∇q H should be ∇p H; displayed anisotropic bound does not follow; 2D counterexample proved |
| xu2024 | Eq. (10)-(11): polar momentum sampler | `relativisticPolarMomentumMeasure_eq_cartesian`, `euclideanRelativisticPolarMomentumMeasure_eq` | Relativistic/Momentum.lean | corrected | Radial Jacobian r^(d-1) not r; uniform spherical direction, not independent angles; corrected construction proved |
| xu2024 | Eq. (12): position derivative | `fderiv_riemannianRelativisticKineticEnergy_position_apply`, diagonal SoftAbs certificate | Relativistic/Derivatives.lean | proved | Two-term inverse-mass/trace formula |
| xu2024 | Eq. (13): momentum derivative | `fderiv_generalRelativisticHamiltonian_momentum_apply` | Relativistic/Derivatives.lean | proved-with-hypotheses | Requires bilinear form hypothesis AᵀA = G⁻¹ |
| xu2024 | Algorithm 1: momentum sampling | corrected polar construction | Relativistic/Momentum.lean | corrected | Three errors: missing r^(d-1), wrong direction sampling, wrong factor transport |
| xu2024 | Section 5.2: validity claim (symmetry sufficient) | invariance theorems | Relativistic/ | corrected | Symmetry necessary but not sufficient; factor-volume compatibility also required |
| xu2024 | Diagonal SoftAbs metric | `softAbs`, positivity, differentiability, AᵀA=G⁻¹ | Relativistic/SoftAbs.lean | proved | Implicit-solver certificate remains conditional |
| xu2024 | Eq. (1): Hamilton's equations | — | — | out-of-scope | Background; continuous-time ODE not needed for kernel validity |
| xu2024 | Eq. (4): dimension-wise kinetic energy | — | — | out-of-scope | Heuristic baseline for experiments |
| livingstone2022barker | Barker acceptance ratio satisfies detailed balance | `barkerAcceptedFlow_swap`, `barkerDensityAcceptedKernel_isReversible` | Kernel/BarkerAcceptance.lean | proved | Product-over-sum flow is manifestly symmetric |
| livingstone2022barker | Barker MH kernel is a valid Markov kernel | `barkerDensityMetropolisHastings_isMarkov` | Kernel/BarkerAcceptance.lean | proved | Markov property via completion framework |
| livingstone2022barker | Barker MH preserves target measure | `barkerDensityMetropolisHastings_invariant` | Kernel/BarkerAcceptance.lean | proved | Follows from reversibility |
| livingstone2022barker | Sigmoid bridge (log-space acceptance) | `barkerLogDensityAcceptance_eq_sigmoid` | Executable/Continuous/BarkerRWMH.lean | proved | r/(1+r) = 1/(1+exp(-log r)) |
| livingstone2022barker | Executable refinement | `gaussianBarkerRwmhProgramKernel_refines` | Executable/Continuous/BarkerRWMH.lean | proved | IR program = mathematical kernel |
| turok2025drghmc | AR(1) momentum refresh preserves Gaussian | `ar1MomentumKernel_isMarkov` | Hamiltonian/DelayedRejection.lean | proved | Valid Markov kernel when α²+β²=1 |
| turok2025drghmc | Stage-1 proposal is an involution | `drStage1Endpoint_involutive` | Hamiltonian/DelayedRejection.lean | proved | momentumFlip ∘ leapfrog is involutive |
| turok2025drghmc | Stage-1 and stage-2 maps are volume-preserving | `measurePreserving_drStage1Endpoint`, `measurePreserving_drStage2Proposal` | Hamiltonian/DelayedRejection.lean | proved | Composition of existing volume-preservation results |
| turok2025drghmc | Ghost path reconstruction identity | `drGhostPath_of_drStage2Proposal` | Hamiltonian/DelayedRejection.lean | proved | Ghost path from stage-2 endpoint recovers original |
| turok2025drghmc | Stage-1 kernel preserves Boltzmann target | `drStage1PhaseKernel_invariant` | Hamiltonian/DelayedRejection.lean | proved | Via deterministic Metropolis + volume preservation |
| turok2025drghmc | DR acceptance correction (ghost factor) | `drStage2Acceptance` | Hamiltonian/DelayedRejection.lean | proved | (1-a₁_ghost)/(1-a₁) correction is well-defined |
| turok2025drghmc | Full DR-G-HMC preserves phase-space target | `drGhmc_stage1_invariant` | Hamiltonian/DelayedRejection.lean | proved-with-hypotheses | Stage-1 invariance proved; full two-stage composition documented as obligation |
| turok2025drghmc | Executable refinement | `scalarDrGhmcTransition_position_eq` | Executable/Continuous/DRGHMC.lean | proved | IR interpreter replay = mathematical transition |
| geyer1991 | Product-target invariance (finite, 2 temperatures) | `ParallelTempering.stationary` | Finite/ParallelTempering.lean | proved | Within-updates + MH swap preserves product distribution |
| geyer1991 | Cold marginal projection | `ParallelTempering.cold_marginal` | Finite/ParallelTempering.lean | proved | First marginal of product target is cold distribution |
| geyer1991 | Product-target invariance (general-state, K temperatures) | `pairSwapKernel_invariant` | Kernel/ParallelTempering.lean | proved-with-hypotheses | Pair swap kernel invariance proved; full SEO/DEO composition invariance blocked on pi-withDensity bridge lemma |
| geyer1991 | Swap kernel detailed balance (general-state) | `pairSwapKernel_isReversible` | Kernel/ParallelTempering.lean:198 | proved | Pairwise swap kernel satisfies detailed balance w.r.t. product target |
| geyer1991 | Swap coordinate involutivity | `swapCoord_involutive` | Kernel/ParallelTempering.lean:100 | proved | Swapping twice returns to original |
| geyer1991 | Swap coordinate measure preservation | `swapCoord_measurePreserving` | Kernel/ParallelTempering.lean:153 | proved | Swap preserves the product density target |
| syed2022nrpt | SEO kernel definition (stochastic even-odd) | `seoKernel` | Kernel/ParallelTempering.lean:321 | proved | 50-50 mixture of even and odd swap kernels, defined |
| syed2022nrpt | DEO kernel definition (deterministic even-odd) | `deoKernel` | Kernel/ParallelTempering.lean:329 | proved | Deterministic alternation even-odd, defined |
| syed2022nrpt | SEO/DEO invariance | — | — | conditional | Definitions complete; invariance proof blocked on pi-withDensity bridge lemma connecting Measure.pi to withDensity |
| syed2022nrpt | DEO non-reversibility | — | — | conditional | DEO kernel defined; non-reversibility proof requires the invariance bridge first |
| syed2022nrpt | Round-trip rate bounds | — | — | out-of-scope | Requires mixing-time analysis beyond current scope |
| surjanovic2022varpt | Variational/generalized PT | — | — | out-of-scope | Requires adaptation theory beyond current scope |
| surjanovic2025pigeons | Distributed parallelism invariance | — | — | out-of-scope | Systems claim; requires distributed-execution formalization |
| zhou2020mixed | MH correction term (proceedings version) | — | — | corrected | Proceedings used incorrect MH correction due to supplementary lemma error; author acknowledged and fixed on arXiv |
| zhou2020mixed | MH correction term (arXiv/corrected version) | — | — | conditional | Corrected term needs formalization; classified as conditional pending Lean implementation |
| zhou2020mixed | Detailed balance of mixed discrete/continuous transition | — | — | conditional | Requires formalization of the embedded discrete/continuous target and the mixed HMC kernel |
| zhou2020mixed | Q_i(x\|x)=0 requirement for correctness | — | — | out-of-scope | Algorithmic design constraint, not a mathematical theorem |
| nishimura2020dhmc | Exact energy preservation (coordinatewise crossing/reflection) | `discontinuousCoordinateStep_energy` | Hamiltonian/Discontinuous.lean:61 | proved | Scalar Laplace-momentum coordinate update preserves total energy |
| nishimura2020dhmc | Reflection involutivity | `discontinuous_reflect_reflect` | Hamiltonian/Discontinuous.lean:75 | proved | Double reflection returns to original phase state |
| nishimura2020dhmc | Crossing probability = MH acceptance | `expMeasure_crossing_probability_eq_mh_acceptance` | Hamiltonian/DiscontinuousMetropolis.lean:54 | proved | Exponential-measure crossing probability equals the target ratio acceptance |
| nishimura2020dhmc | One-step kernel target invariance | `oneStepDiscontinuousKernel_stationary` | Hamiltonian/DiscontinuousMetropolis.lean:79 | proved | Single-coordinate discontinuous HMC kernel preserves target |
| nishimura2020dhmc | Volume preservation of the multi-coordinate integrator | — | — | conditional | Requires measure-theoretic volume-preservation theorem for the composed coordinatewise updates |
| nishimura2020dhmc | Full kernel invariance (all coordinates) | — | — | conditional | Requires composed multi-coordinate kernel + momentum refreshment formalization |
| nishimura2020dhmc | Connection to zig-zag sampler | — | — | out-of-scope | Theoretical comparison, not a correctness claim |
| zoltowski2025parallel | Sequential-parallel equivalence of Newton fixed-point | — | — | conditional | Deterministic refinement claim; requires formalization of the Newton iteration and convergence proof |
| zoltowski2025parallel | O(log T) parallel complexity | — | — | out-of-scope | Computational complexity claim, not a correctness/invariance result |
| zoltowski2025parallel | Exact chain reproduction (no approximation error) | — | — | conditional | Requires proof that the fixed-point solver converges to the exact sequential solution |
