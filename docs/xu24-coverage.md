# Xu and Ge 2024 coverage audit

This document maps the mathematical and algorithmic claims in Kai Xu and
Hong Ge, “Practical Hamiltonian Monte Carlo on Riemannian Manifolds via
Relativity Theory,” ICML 2024, to the Lean development. The source audited is
the [published PMLR paper](https://proceedings.mlr.press/v235/xu24i.html).

The paper contains no numbered theorem and no quantitative convergence
theorem. Its principal theoretical claim is the informal validity argument in
Section 5.2. Accordingly, the strongest machine-checked endpoint here is exact
Markov-kernel invariance (and, for the phase transition, detailed balance), not
convergence from arbitrary initial states or the empirical efficiency claims
of Section 6.

Status meanings:

- **proved**: represented by definitions and machine-checked theorems;
- **conditional**: proved from an explicit mathematical certificate that a
  numerical implementation must still discharge;
- **corrected**: the printed statement or algorithm is false or inconsistent
  as written, and Lean formalizes a corrected replacement;
- **obstructed**: Lean proves a counterexample or incompatibility under the
  audited quantifiers; and
- **out of scope**: background, implementation engineering, or an empirical
  claim rather than a correctness result of the GR-HMC kernel.

## Equations and constructions

| Paper item | Status | Lean coverage and qualification |
|---|---|---|
| Equation (1), Hamilton's equations | conditional | `GeneralizedLeapfrogEquations` consumes functions representing `∂H/∂q` and `∂H/∂p`. The continuous-time Hamiltonian ODE and existence of its exact flow are not needed for the numerical-kernel validity theorem and are not claimed. |
| Equation (2), Gaussian RHMC kinetic energy | out of scope | Background comparison only. The project already has Gaussian HMC infrastructure, but this equation is not a GR-HMC result. |
| Equation (3), multivariate special-relativistic kinetic energy | proved | `relativisticKineticEnergy`, `relativisticMass`, and `relativisticVelocity`; positivity and the strict speed bound are proved by `relativisticMass_pos` and `euclideanNorm_relativisticVelocity_lt`. |
| Equation (4), dimension-wise kinetic energy | out of scope | A heuristic baseline used in experiments, not the proposed GR-HMC law. |
| Equation (5), Gaussian RHMC derivatives | out of scope | Background formula. No correctness theorem later depends on formalizing the SoftAbs derivative implementation. |
| Equations (6)--(7), generalized leapfrog | exact interface proved; finite implementation obstructed | `GeneralizedLeapfrogEquations` states the equations and `IsValid` separates uniqueness, measurability, reversal, and volume preservation. `finiteFixedPointGeneralizedLeapfrog` formalizes the natural finite loops and characterizes their residuals. `finiteFixedPointGeneralizedLeapfrog_six_not_satisfies` proves that six iterations need not even solve the equations, so the experimental iteration count cannot supply the exact validity certificate without extra assumptions or a correction. |
| Equation (8), GR kinetic energy | proved | `riemannianRelativisticKineticEnergy` and `generalRelativisticHamiltonian` include the factor quadratic form and the `logDet/2` term. `riemannianRelativisticMomentumMeasure_eq_withDensity` proves the corresponding conditional density under the exact factor-volume certificate. |
| Equation (9), velocity and bound | corrected | Hamiltonian velocity is `∇p H`, not the printed `∇q H`. Its corrected value is `G⁻¹p/M`, represented by `riemannianRelativisticVelocity`. The paper's substitution inside `M_G(q,A_qp)` and its displayed anisotropic norm bound do not follow from `A_qᵀA_q=G_q⁻¹`. Lean proves the corrected bound `euclideanNorm_riemannianRelativisticVelocity_lt` and an explicit two-dimensional counterexample in `printedEquation9_ratio_lt_correctedRatio`. |
| Equations (10)--(11), polar momentum sampler | corrected | The correct dimension-`d` radial Jacobian is `r^(d-1)`, represented by `relativisticRadialWeight`; `relativisticRadialWeight_two` explains why the printed `r` is valid only in dimension two, and `relativisticRadialWeight_three_at_two_ne_printed` proves a concrete higher-dimensional mismatch. The corrected direction is uniform spherical measure, not independent uniform spherical angles. `relativisticPolarMomentumMeasure_eq_cartesian` and `euclideanRelativisticPolarMomentumMeasure_eq` prove that the corrected polar construction has the desired Cartesian density. |
| Equation (12), cached position derivative | proved for diagonal SoftAbs | `fderiv_riemannianRelativisticKineticEnergy_position_apply` proves the two-term inverse-mass/trace formula. `diagonalSoftAbsMetricEquation12CertificateOfDifferentiable` constructs the complete certificate from any coordinatewise differentiable Hessian diagonal, including at zero entries. |
| Equation (13), momentum derivative | proved under factor compatibility | `fderiv_generalRelativisticHamiltonian_momentum_apply` proves that the Fréchet momentum derivative applied to any direction is pairing with `G⁻¹p/M`. The explicit hypothesis is the bilinear form of `AᵀA = G⁻¹`. |
| Diagonal SoftAbs approximation, Section 5.4 | metric, measure, and diagonal calculus proved | `softAbs` implements `x coth(αx)` with value `1/α` at zero. Lean proves positivity, differentiability everywhere (including the removable zero branch), `AᵀA=G⁻¹`, Equations (12)--(13), and exact factor-volume compatibility. Its target-specific implicit-solver validity certificate remains conditional. The separate bounded nonconstant `2 + sin(q)` metric client now has a complete exact solver and phase-volume theorem. |

## Algorithm 1: momentum sampling

The printed algorithm is not correct in general dimension under its own
factor convention:

1. Its radial density omits the `r^(d-1)` Jacobian except when `d = 2`.
2. Independent uniform spherical angles do not give uniform direction on a
   sphere when `d > 2`.
3. Given `A_qᵀA_q = G_q⁻¹` and kinetic quadratic form `‖A_qp‖²`, an isotropic
   draw `z` must be transported as `p = A_q⁻¹z`; the printed
   `p = A_qᵀz` generally has the reciprocal scaling even in one dimension.

The corrected construction is fully measure-theoretic:

- `euclideanRelativisticMomentumProbability` is the normalized isotropic law;
- `riemannianRelativisticMomentumProbability` maps it through
  `(metric.factor q).symm`;
- `map_factor_riemannianRelativisticMomentumProbability` proves that applying
  the factor recovers the isotropic law;
- `riemannianMomentumKernel` packages the measurable position-dependent
  conditional distribution as a mathlib Markov kernel.

`HasCompatibleFactorVolume` states the exact Jacobian identity needed to
identify the transported law with the complete kinetic density. Together with
joint measurability of that density,
`isMeasurableRiemannianMomentumFamily_of_factorVolume` derives the measurable
normalized row family, and `isCompatibleGRPositionTarget_of_factorVolume`
derives the target/conditional disintegration equation. The certificate is
proved for the identity metric, a genuinely position-dependent scalar-factor
metric, and the diagonal SoftAbs metric.

## Section 5.2 validity claim

The paper says symmetry is the only requirement on the momentum distribution.
Symmetry is necessary for momentum reversal, but it is not sufficient for the
full position-dependent algorithm. Correctness also requires:

- correct normalization and measurable dependence of the conditional momentum
  law on position;
- reconstruction of the intended joint phase target from the position target
  and conditional momentum kernel;
- an exactly selected generalized-leapfrog map with the required
  measurability, inverse/time-reversal, and phase-volume properties; and
- a valid Metropolis or randomized multinomial correction.

These obligations are explicit in Lean. For endpoint Metropolis,
`endpointMetropolisGRHMC_isReversible` and `endpointMetropolisGRHMC_invariant`
prove phase correctness; `positionEndpointMetropolisGRHMC_invariant` proves
the refreshed and projected position transition correct under
`IsCompatibleGRPositionTarget`. For multinomial correction,
`multinomialGRHMCPhase_isReversible`, `multinomialGRHMCPhase_invariant`, and
`positionMultinomialGRHMC_invariant` prove the analogous results. The generic
algebraic core is `orbitMultinomialKernel_isReversible`.

The paper's practical statement that the implicit equations are “usually
solved by fixed-point iterations” does not close these obligations. The Lean
finite-iteration model uses the natural incoming momentum/position seeds and
proves that exact satisfaction is equivalent to both final iterates being
actual fixed points. A scalar example with the paper's experimental count of
six iterations returns an alternating non-fixed momentum. Thus a fixed count
is an approximation, not an exact generalized-leapfrog selection in general.
Under explicit contraction hypotheses,
`finiteHalfMomentum_tendsto_fixedPoint` and
`finiteNextPosition_tendsto_fixedPoint` prove convergence to the unique exact
implicit solutions; the corresponding `dist_*_fixedPoint_le` theorems give
geometric finite-iteration error bounds. This validates an approximation
claim under stated assumptions, but does not turn a finite iterate into an
exact HMC proposal.
`FiniteFixedPointIsValid` states the corrected claim: zero residual is needed
to construct `finiteFixedPointSelection`. Measurability of both derivative
fields now automatically proves measurability of every finite loop and of the
selected step; uniqueness, reversal, and volume preservation must still be
proved separately.

For the identity metric, `identity_positionEndpointMetropolisGRHMC_invariant`
and `identity_positionMultinomialGRHMC_invariant` discharge the momentum and
target compatibility calculation completely. Only the generalized-leapfrog
solver certificate remains conditional there.
The corresponding nonconstant results are
`scalar_positionEndpointMetropolisGRHMC_invariant` and
`scalar_positionMultinomialGRHMC_invariant`; Hamiltonian measurability follows
from measurable potential and positive measurable scale fields.
For the paper's diagonal SoftAbs metric,
`diagonalSoftAbs_positionEndpointMetropolisGRHMC_invariant` and
`diagonalSoftAbs_positionMultinomialGRHMC_invariant` discharge the measure,
refresh, and target-compatibility obligations from coordinatewise measurable
Hessian data. Their sole remaining numerical premise is the same explicit
generalized-leapfrog validity certificate.

## Claims not promoted to theorems

Section 6 reports finite numerical experiments about divergences, Hamiltonian
error, acceptance rates, effective sample size, and runtime. Those results are
empirical observations for particular code, datasets, seeds, and
hyperparameters; they are not universal mathematical consequences of the
velocity bound and are not represented as Lean theorems.

Likewise, the introductory statement that MCMC samples converge
asymptotically is not established by detailed balance or invariance alone.
No irreducibility, aperiodicity, recurrence, or quantitative convergence
conditions for GR-HMC are stated in the paper, so this development makes no
GR-HMC convergence claim.

## Remaining formal boundary

The main paper-level validity result is formalized, and the bounded
nonconstant metric supplies a fully valid exact generalized-leapfrog client.
The paper's practical diagonal SoftAbs implementation still requires
additional target hypotheses or an exact/corrected implicit solver satisfying
`GeneralizedLeapfrogSelection.IsValid`; the natural finite implementation is
defined, contraction certificates give convergence and quantitative
iteration-error bounds, `FiniteFixedPointIsValid` gives the corrected exact
interface, and six iterations are proved insufficient in general. Given a
coordinatewise differentiable and measurable Hessian diagonal, all remaining
SoftAbs obligations are therefore solver-specific rather than metric or
kernel-measure obligations.

Until those are discharged, the formalized kernels are mathematical GR-HMC
algorithms with exact conditional correctness theorems, not certification of
the finite-iteration AdvancedHMC.jl implementation used for the experiments.
