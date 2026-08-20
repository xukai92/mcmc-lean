# Girolami--Calderhead classical RMHMC coverage

This audit tracks the theoretical core of Mark Girolami and Ben Calderhead,
“Riemann manifold Langevin and Hamiltonian Monte Carlo methods,” JRSS B 73(2),
2011. It separates exact kernel correctness from numerical approximation and
from ergodic convergence.

## Machine-checked claims

| Claim | Status | Lean evidence |
|---|---|---|
| Conditional momentum is `N(0,G(q))` | Proved | `gaussianMomentumMeasure` transports a standard Gaussian by the inverse factor; `gaussianMomentumMeasure_eq_withDensity` proves the full density and determinant factor. |
| Hamiltonian contains `pᵀG(q)⁻¹p/2 + log det G(q)/2` | Proved | `gaussianKineticEnergy` and `hamiltonian`. |
| Density is proportional to `exp(-H)` | Proved | `phaseWeight_eq_prefactor_mul_hamiltonianWeight`; the proportionality factor is global and cancels from Metropolis ratios. |
| Generalized leapfrog gives an involutive endpoint proposal | Proved conditionally | `generalizedHmcEndpoint_involutive`, assuming the explicit `GeneralizedLeapfrogSelection.IsValid` certificate. |
| Endpoint proposal preserves phase volume | Proved conditionally | `measurePreserving_generalizedHmcEndpoint`, from the same certificate. |
| Metropolis transition is reversible and phase invariant | Proved | `endpointMetropolis_isReversible` and `endpointMetropolis_invariant`. |
| Momentum refresh, phase evolution, and position projection preserve the desired target | Proved | `positionEndpointMetropolis_invariant`. |
| Concrete API is usable | Proved | `identity_positionEndpointMetropolis_invariant` discharges the complete identity-metric instance with explicit leapfrog. |

The reusable correction theorem lives in `Mcmc.Hamiltonian.GeneralizedHMC`.
It is intentionally independent of Gaussian, relativistic, or any other
momentum law. Classical RMHMC is now the first position-dependent
specialization; the Xu--Ge relativistic law is a later specialization.

## Exact numerical-integrator boundary

The generalized-leapfrog equations are implicit. The paper describes fixed
point iteration run to convergence and reports that five or six iterations
were typically sufficient in its experiments. A fixed iteration count or a
positive residual tolerance does not by itself prove exact reversal or exact
volume preservation.

Accordingly, the formal theorem accepts a selected solver only with explicit
measurability, uniqueness, momentum-flip reversal, and phase-volume
preservation. Approximate runtime loops require a separate refinement or
correction argument; observed small residuals are not promoted to detailed
balance.

## Statement correction

Detailed balance gives stationarity, not general convergence from an
arbitrary initial state. The paper describes the resulting RMHMC chain as
ergodic, but a general theorem additionally needs suitable irreducibility,
aperiodicity/period handling, and recurrence assumptions. The repository
therefore claims target invariance for classical RMHMC. It does not claim a
paper-wide convergence theorem.

## Remaining implementation work

- expose a maintained Julia sampler for arbitrary classical Gaussian RMHMC;
- bind metric, derivative, and implicit-solver callbacks to the formal
  certificate interface;
- add classical RMHMC evaluation targets; and
- treat finite-precision fixed-point solves through an explicit guarded
  refinement layer rather than identifying them with exact solutions.
