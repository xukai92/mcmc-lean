# Executable sampler roadmap

This roadmap tracks the cross-language implementation separately from the
mathematical paper proofs. A sampler can have a verified ideal kernel while
its Julia realization still carries explicit floating-point, callback, and RNG
assumptions.

## Completed vertical slices

The committed version-7 artifact and Julia package currently provide:

| Slice | Exact Lean result | Julia evidence |
|---|---|---|
| Finite categorical and MH | Exact PMF and kernel-row refinement | Exhaustive traces against the Lean oracle and Optimized |
| Gaussian RWMH | Exact kernel equality and target invariance | Reference/Optimized replay, moments, and per-run decision certificates |
| Scalar and vector endpoint HMC | Exact trace semantics, phase-volume preservation, and position invariance | Differential, integrator-property, and moment tests |
| Diagonal and dense constant-metric HMC | Time reversal, volume and Boltzmann invariance, and Gaussian-factor transport | Generated Reference programs, Optimized comparison, and correlated-Gaussian tests |
| Randomized-origin multinomial HMC | Exact choice PMF, verified kernel row, and position invariance | Generated Reference program, independent Optimized trajectory, and moment tests |

The finite implementation is exact. Continuous Julia execution uses
`Float64`, platform numerical libraries, callbacks, and concrete RNGs. Lean
proves conditional bounded-error composition; Julia checks supplied per-run
witnesses. A universal Julia/LLVM/libm/RNG refinement theorem is not claimed.

## Prioritized next steps

### 1. Multinomial-selection numerical certificates

Extend the bounded-refinement layer from binary endpoint decisions to the
multinomial command. The certificate must bound:

1. every computed trajectory state and Hamiltonian;
2. stabilized exponentials and their sum;
3. normalized or cumulative categorical weights; and
4. the uniform draw's distance from every cumulative selection boundary.

The desired theorem says that the Float64 and ideal executions choose the same
trajectory index outside the resulting union of boundary bands. This closes
the largest numerical gap in the new executable multinomial slice.

### 2. Constant-metric multinomial HMC

Generalize the executable multinomial command from unit mass to the existing
typed diagonal and dense metric inputs. Reuse the proved Cholesky momentum law
and constant-metric trajectory results, then identify the ideal command with a
metric multinomial kernel and prove its refreshed position-target invariance.
Reference and Optimized should share event order but retain independent
trajectory construction.

### 3. Executable coupled samplers for Xu et al. (2021)

Add explicit shared-randomness IR commands for the already formalized coupled
multinomial-HMC and Gaussian-RWMH mixture. The Lean requirements are:

- both executable marginals equal the verified single-chain kernels;
- maximal or transport index selection matches the existing coupling PMFs;
- sticky RWMH exposes its shared proposal and acceptance events; and
- deterministic replay records the exact meeting event.

This is the most direct route from the single-chain runtime to an executable
version of the 2021 paper's verified estimator pipeline.

### 4. Executable relativistic/Riemannian HMC for Xu and Ge (2024)

Only after its runtime contract is fixed, add the corrected radial and
spherical momentum draws, inverse-factor transport, nonseparable integrator,
and multinomial selection. Approximate fixed-point solves must return a
residual or integrator certificate consumed by the existing conditional
kernel theorem; a fixed iteration count alone is not a correctness witness.

### 5. Callback and production hardening

Develop a restricted target/gradient expression surface or externally checked
callback certificates, add active edge-case and high-dimensional tests, and
benchmark against established Julia samplers. Step-size or metric adaptation
must remain an explicit stateful algorithm with a separate specification.

## Assurance boundary

The immediate recommended goal is step 1, followed by step 2. Steps 3 and 4
then connect executable work to the two paper targets. Cross-language semantic
preservation, arbitrary callback correctness, universal floating-point
refinement, convergence rates, and adaptation are distinct obligations and
must not be inferred from target invariance or statistical tests.
