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

## Julia execution

Artifact format version 21 registers `classical_rmhmc_step!`. The generated
Reference interpreter and independent Optimized implementation both use the
formal inverse-factor convention, require an exact implicit-solver
certificate at every generalized-leapfrog step, and apply endpoint Metropolis
correction. The public `ClassicalRMHMC` sampler selects either implementation;
Reference is the default.

```julia
using LinearAlgebra, Random, VerifiedSamplers

certificate = Certificates.certify_implicit_solve(0, 0, 0, 0;
    unique=true, reversible=true, volume_preserving=true)
factor(q) = Matrix{Float64}(I, length(q), length(q))
hamiltonian(q, p) = (sum(abs2, q) + sum(abs2, p)) / 2
integrator(q, p, step_size) = begin
    half = p .- (step_size / 2) .* q
    next_q = q .+ step_size .* half
    next_p = half .- (step_size / 2) .* next_q
    (next_q, next_p, certificate)
end

sampler = ClassicalRMHMC(hamiltonian, factor, integrator, 0.15, 8)
draws = sample(MersenneTwister(42), sampler, zeros(2), 2_000)
```

The example certificate is justified because the displayed integrator is the
explicit separable leapfrog. Users must not set its global witness flags for
an arbitrary finite-tolerance fixed-point loop.

## Remaining implementation work

- add classical RMHMC to the full comparative benchmark matrix; and
- treat finite-precision fixed-point solves through an explicit guarded
  refinement layer rather than identifying them with exact solutions.
