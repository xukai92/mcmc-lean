# Executable sampler roadmap

This roadmap tracks the cross-language implementation separately from the
mathematical paper proofs. A sampler can have a verified ideal kernel while
its Julia realization still carries explicit floating-point, callback, and RNG
assumptions.

## Completed vertical slices

The current version-10 artifact and Julia package provide:

| Slice | Exact Lean result | Julia evidence |
|---|---|---|
| Finite categorical and MH | Exact PMF and kernel-row refinement | Exhaustive traces against the Lean oracle and Optimized |
| Gaussian RWMH | Exact kernel equality and target invariance | Reference/Optimized replay, moments, and per-run decision certificates |
| Scalar and vector endpoint HMC | Exact trace semantics, phase-volume preservation, and position invariance | Differential, integrator-property, and moment tests |
| Diagonal and dense constant-metric HMC | Time reversal, volume and Boltzmann invariance, and Gaussian-factor transport | Generated Reference programs, Optimized comparison, and correlated-Gaussian tests |
| Randomized-origin multinomial HMC | Exact choice PMF, verified kernel row, and position invariance | Generated Reference program, independent Optimized trajectory, and moment tests |
| Constant-metric multinomial HMC | Orbit-kernel phase and refreshed-position invariance, including Cholesky refresh | Typed diagonal/dense programs, differential tests, and correlated-Gaussian moments |
| Xu et al. coupled HMC/RWMH | Each ideal coupled command has the verified single-chain kernel on both marginals | Version-9 Reference interpreter, shared-randomness replay, meeting flags, and faithfulness tests |
| Corrected relativistic/Riemannian HMC | Corrected momentum law, inverse-factor transport, guarded generalized leapfrog, and a bounded nonconstant exact solver with phase-volume preservation | Version-10 Reference/Optimized implementations, residual certificates, differential replay, and position-dependent reversal tests |
| Gaussian diagonal-SoftAbs GR-HMC | Actual Gaussian Hessian, non-identity SoftAbs metric, explicit valid generalized leapfrog, endpoint and multinomial position invariance | Public `GaussianSoftAbsGRHMC`, deterministic seeded replay, validation, and finite-output tests |

The finite implementation is exact. Continuous Julia execution uses
`Float64`, platform numerical libraries, callbacks, and concrete RNGs. Lean
proves conditional bounded-error composition; Julia checks supplied per-run
witnesses. A universal Julia/LLVM/libm/RNG refinement theorem is not claimed.

## Newly completed hardening

### Multinomial-selection numerical certificates

An end-to-end multinomial refinement must bound:

1. every computed trajectory state and Hamiltonian;
2. stabilized exponentials and their sum;
3. normalized or cumulative categorical weights; and
4. the uniform draw's distance from every cumulative selection boundary.

The implemented selection certificate consumes the resulting cumulative
boundary bound. Lean proves identical selected indices outside the union of
boundary bands and localizes any disagreement to at least one band. Julia
checks the matching execution-specific witness. Upstream trajectory, energy,
exponential, and cumulative-sum bounds remain explicit inputs rather than
runtime dependencies.

### Constant-metric multinomial HMC

Completed in version 8 for typed diagonal and dense inputs. The ideal command
uses the verified orbit kernel; phase, refresh–evolve–project, and
Cholesky-refreshed invariance are proved. Reference and Optimized share event
order while retaining independent trajectory construction.

### Callback and production hardening

Reference rejects nonfinite states, non-real or nonfinite log densities,
wrong-size gradients, and nonfinite gradients. Tests cover these failures.
Restricted callback expressions, adaptation, and performance benchmarking
remain future work.

## Prioritized next steps

### Completed: executable coupled samplers for Xu et al. (2021)

The explicit shared-randomness IR commands now cover the formalized coupled
multinomial-HMC and Gaussian-RWMH mixture:

- both ideal marginals equal the verified single-chain kernels;
- maximal index selection implements the existing coupling construction;
- sticky RWMH exposes shared proposal and acceptance randomness; and
- deterministic replay records exact equality as the meeting event.

The Float64 interpreter remains qualified by the numerical-refinement
boundary; the ideal marginal theorems are not silently transferred to Julia.

### 1. Refine executable relativistic/Riemannian HMC for Xu and Ge (2024)

The corrected runtime and the first target-derived diagonal SoftAbs client are
implemented. For a centered Gaussian target, Lean proves that the supplied
diagonal is the actual Hessian, the SoftAbs eigenvalue is non-identity, and the
explicit separable generalized leapfrog satisfies every validity obligation;
endpoint and multinomial position invariance follow. Julia exposes the same
constant-Hessian specialization as `GaussianSoftAbsGRHMC`.

The remaining work is the genuinely position-dependent paper-style SoftAbs
client and its restricted Float64 refinement: propagate bounded trajectory and
residual errors and certify decisions away from numerical boundaries. A fixed
iteration count alone remains insufficient as a correctness witness.

### 2. Restricted callbacks, adaptation, and performance

The first restricted scalar target surface is implemented. Its syntax admits
input, real constants, addition, multiplication, negation, and exponential.
Lean defines ideal-real evaluation and symbolic differentiation and proves the
derivative correct, differentiability, and measurability for every expression.
Julia mirrors the structural evaluator, computes value and derivative together,
and rejects non-finite intermediate results. A backend-facing certificate keeps
Float64 value/gradient error explicit; the Gaussian expression has a derived
end-to-end bound from an input bound.

The portable rational-literal subset is now serialized in generated IR version
11. The public Julia Gaussian expression is decoded from that artifact, and
Lean proves that the emitted portable tree compiles to the verified Gaussian
expression. Remaining work is recursive operation-level Float64 bounds
(especially `exp`), active
high-dimensional tests, and benchmarking against established Julia samplers.
Step-size or metric adaptation must remain an explicit stateful algorithm with
a separate specification.

## Assurance boundary

The immediate execution goal is restricted Riemannian refinement rather than
construction of the sampler. Cross-language semantic preservation, arbitrary
callback correctness, universal floating-point refinement, convergence rates,
and adaptation are distinct obligations and must not be inferred from target
invariance or statistical tests.
