# Executable sampler roadmap

This roadmap tracks the cross-language implementation separately from the
mathematical paper proofs. A sampler can have a verified ideal kernel while
its Julia realization still carries explicit floating-point, callback, and RNG
assumptions.

The dynamic-trajectory API now exposes both sides of its safety boundary.
Root-independent endpoint and all-scales barriers construct certified orbit
partitions directly. `first_stop_endpoint_uturn_candidates` instead builds
root-dependent first-stop rows and runs the reroot checker; its result is
theorem-backed only when `certificate.valid` is true. Equivalence with a
specific recursive production NUTS tree builder remains open. Lean now proves
measure-level detailed balance for measurable, orbit-covariant checked rows;
the concrete bounded `recursiveDoublingCandidateRow` interpreter is now proved
to construct orbit-covariant checked rows for each bounded direction trace when
its exact endpoint callback is orbit stable. The state-independent fair trace
mixture, momentum refresh, and position projection now have exact invariance
theorems, and the Euclidean endpoint predicate discharges the exact-real
measurability condition. The remaining boundary is numerical refinement of
the concrete floating trajectory and callback. The maintained Julia `NUTS`
(`VerifiedNUTS` compatibility alias) now uses the productive completed-tree
C.4 construction: every possible root receives its unique reconstruction
trace and selection is restricted to the common admissible component.
`CheckedRecursiveDynamicHMC` separately retains the fixed-trace decoded-program
experiment and its checked identity fallback. The production-shaped
`Optimized.NUTS` implementation remains a runtime-only comparator. A checked Lean
two-leaf counterexample now proves why this cannot follow from root retention
or first stopping alone: asymmetric rows fail reroot equality and the safe
wrapper becomes identity. The conservative
branch is now a public sampler: `CertifiedDynamicHMC` builds a complete
randomized-origin leapfrog orbit, applies the certified all-scales partition,
and uses a stable floating Boltzmann selector with Reference/Optimized trace
conformance. Its Float64 trajectory/refinement boundary remains the same as
the existing continuous HMC clients.

## Completed vertical slices

The current version-19 artifact and Julia package provide:

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
Restricted callback expressions, scoped adaptation clients, and performance
diagnostics are now implemented. Broader target coverage remains optional.

## Completed implementation tracks and parked refinements

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

The restricted refinement now reaches a guarded scalar SoftAbs metric entry:
Lean composes backend-local bounds through `tanh`, square root, reciprocal,
and log-determinant evaluation, and Julia evaluates the matching guarded
operations. The genuinely position-dependent implicit solver and its complete
residual-to-selection certificate chain are described below. Platform-specific
primitive Float64/libm/RNG bounds remain explicit inputs; a fixed iteration
count alone is still insufficient as a correctness witness.

The first solver-error link is complete: a certified computed residual and a
contraction rate now give an explicit a posteriori distance to the exact
Banach-selected solve for each implicit loop, with a matching checked Julia
calculation. This bound is now specialized to the nonconstant actual-Hessian
SoftAbs client: the finite half-momentum loop is compared directly with the
certified solver's half momentum, and the finite position loop at that exact
half momentum is compared directly with its exact next position. The coupled
perturbation is also complete: the metric factor is proved uniformly at most
one, hence the momentum callback is uniformly one-Lipschitz in momentum; a
generic contracting-fixed-point perturbation theorem transports the computed
half-momentum error into the position solve. The subsequent final-momentum,
energy, and multinomial links are now complete.

The final-kick algebra is now generic and checked: given explicit momentum-
and position-slice constants for the Hamiltonian position derivative, Lean
propagates the half-momentum and next-position budgets to the outgoing
momentum. For the nonconstant target the momentum-slice constant is global,
while Lean constructs the required position-slice and energy constants on the
bounded trajectory region because the quadratic target is not globally
Lipschitz. The generic bounded-region energy link is checked: a
`LipschitzOnWith` certificate transports phase-state error into endpoint-energy
error and adds backend evaluation error separately. A concrete compact-region
constant is now constructed for both the actual SoftAbs Hamiltonian and its
position callback: their continuous Fréchet-derivative norms attain maxima on
closed phase balls. Every computed/ideal scalar phase pair is automatically
enclosed in a canonical origin-centered ball, so coordinate errors and backend
Hamiltonian error produce an actual-target endpoint-energy certificate. The
existing multinomial boundary-stability theorem consumes the resulting
execution-specific cumulative-boundary error. The intervening arithmetic is
now checked end to end: a finite maximum preserves the uniform energy-error
budget; maximum shifting doubles it; `exp` is nonexpansive on the resulting
nonpositive arguments; cumulative and total errors grow linearly with the
trajectory count; and multiplication of the unit draw by total weight has an
explicit composed budget. Lean assembles these into the exact list-shaped
`MultinomialSelectionCertificate`. Platform `exp`, multiplication, summation,
RNG, and boundary-margin witnesses remain explicit, as intended.

### 2. Restricted callbacks, adaptation, and performance

The first restricted scalar target surface is implemented. Its syntax admits
input, real constants, addition, multiplication, negation, and exponential.
Lean defines ideal-real evaluation and symbolic differentiation and proves the
derivative correct, differentiability, and measurability for every expression.
Julia mirrors the structural evaluator, computes value and derivative together,
and rejects non-finite intermediate results. A backend-facing certificate keeps
Float64 value/gradient error explicit; the Gaussian expression has a derived
end-to-end bound from an input bound.

The portable rational-literal subset is serialized in generated IR. The public
Julia Gaussian expression is decoded from that artifact, and
Lean proves that the emitted portable tree compiles to the verified Gaussian
expression. A backend-generic recursive theorem now composes rational,
addition, multiplication, negation, and bounded-domain exponential certificates
into end-to-end value and symbolic-gradient bounds for every portable tree.
Version 13 extends that surface with sine and cosine. Lean proves their
symbolic differentiation rules and global one-Lipschitz argument transport,
while backend-local libm errors remain explicit. The generated sinusoidally
perturbed Gaussian tree is exactly the nonconstant SoftAbs potential and force.
For the polynomial Gaussian client, Julia serializes every finite Float64 as
an exact rational certificate; the compiled Lean oracle checks that artifact,
and checker soundness yields value, derivative, and second-derivative
approximation facts. The Hessian certificate reaches the input consumed by
the diagonal SoftAbs metric.
Optional platform work would instantiate primitive operation premises for
transcendental operations (`exp`, `sin`, and `cos`), extending the checked path
from target/force evaluation through the genuinely position-dependent SoftAbs
metric and solver, and benchmarking against
established Julia samplers.
Step-size or metric adaptation must remain an explicit stateful algorithm with
a separate specification.

## Assurance boundary

The sampler construction and restricted refinement interfaces are complete at
their documented exact/guarded boundaries. Universal cross-language semantic
preservation, arbitrary callback correctness, and generic floating-point
refinement are parked research extensions. Convergence and adaptation remain
distinct properties and must not be inferred from target invariance or
statistical tests.
