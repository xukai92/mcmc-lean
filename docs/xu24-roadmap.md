# Xu and Ge 2024 formalization roadmap

This document records the formalization of Kai Xu and Hong Ge, “Practical Hamiltonian Monte
Carlo on Riemannian Manifolds via Relativity Theory,” ICML 2024.  The paper is
primarily an algorithm and validity paper: Section 5.2 gives an informal
correctness argument rather than a numbered convergence theorem.  This
roadmap treats construction of the actual GR-HMC kernel and a proof of target
invariance as the principal endpoint.

## Intended dependency chain

```text
relativistic scalar/vector algebra
  -> position-dependent positive-definite metric
  -> conditional relativistic momentum measure
  -> nonseparable GR Hamiltonian and velocity bound
  -> generalized implicit leapfrog
  -> reversibility and volume preservation
  -> endpoint-MH and multinomial GR-HMC kernels
  -> target invariance
```

## Design implications from the statement audit

The canonical item-by-item corrections and theorem references are maintained
in the [2024 coverage audit](xu24-coverage.md). They led to four architectural
choices here:

- construct the corrected dimension-dependent momentum law and prove its
  pushforward before using it as a refresh kernel;
- keep the metric factor and inverse-metric action distinct;
- represent generalized leapfrog through an explicit exact-solution validity
  certificate; and
- separate mathematical invariance from empirical stability and efficiency.

## Milestones

1. Formalize relativistic mass, kinetic energy, velocity, symmetry, and the
   strict speed bound.
2. Define finite-dimensional positive-definite metrics and prove the
   Riemannian velocity-bound identity.
3. Construct the corrected radial/directional momentum measure and prove its
   density and affine transformation law.
4. Define generalized leapfrog through an explicit solution interface and
   isolate existence, measurability, reversibility, and Jacobian obligations.
5. Construct endpoint-MH GR-HMC and prove detailed balance/invariance.
6. Extend the existing multinomial-HMC infrastructure to the nonseparable
   Hamiltonian and prove invariance.
7. Add concrete constant-metric and position-dependent examples, then perform
   a claim-by-claim paper coverage audit.

## Current formal boundary

All seven roadmap milestones are implemented. The exact generalized-leapfrog
interface keeps existence, uniqueness, measurability, time reversal, and
phase-volume preservation explicit. Endpoint-Metropolis and randomized
multinomial corrections are proved reversible and invariant for the GR phase
target, and position-dependent momentum refresh followed by projection is
proved invariant for the intended position target.

The natural finite fixed-point implementation is now formalized separately.
Lean characterizes its exact residual and proves that six iterations can fail
to solve even the first implicit equation in one dimension. Therefore the
experimental implementation cannot be identified with the exact selection
interface merely from its iteration count.
With an explicit contraction constant below one, Lean proves that both loops
converge to their unique fixed points and supplies the standard a priori
geometric error bounds. Lean also proves the finite loops measurable whenever
the two derivative fields are measurable. These results justify controlled
approximation under stated hypotheses, while keeping exact kernel validity
separate.
The corrected statement is `FiniteFixedPointIsValid`: finite iteration must
first have exactly zero residual, and the resulting selection must separately
satisfy uniqueness, time reversal, and phase-volume preservation;
measurability follows automatically from measurable derivative fields.

`HasCompatibleFactorVolume` states the exact determinant/Jacobian identity
needed for the momentum density and position/phase disintegration. It is
proved for identity, nonconstant scalar-factor, and diagonal SoftAbs metrics.
The generic measure-theoretic development derives the normalized measurable
momentum kernel and target compatibility from this identity.

For the identity metric, the determinant compatibility equation is now fully
discharged. Lean tracks the relativistic momentum partition function, proves
the phase target factors into position and corrected Euclidean momentum
measures, and proves the resulting position-space endpoint GR-HMC kernel
preserves the scaled position Boltzmann target. Only the numerical-integrator
validity certificate remains conditional in this concrete theorem.
The identity metric also has a concrete position-space multinomial GR-HMC
invariance theorem with exactly the same remaining solver certificate.
The position-dependent scalar-factor metric likewise has endpoint and
multinomial position-invariance theorems. Measurability of its Hamiltonian is
derived from measurable potential and positive measurable scale fields, so
only the solver certificate remains as the numerical premise.
The diagonal SoftAbs metric now has the same endpoint and multinomial
position-invariance theorems. Coordinatewise measurable Hessian-diagonal data
discharges Hamiltonian measurability, normalized momentum refresh, factor
volume, and target compatibility. A concrete executable instance still needs
a valid exact or corrected implicit solver. SoftAbs differentiability through
zero is now proved by a second-order little-o argument, so coordinatewise
differentiable Hessian data supplies Equation (12) without a nonzero-entry
restriction.

Thus the remaining boundary is intentionally algorithmic rather than a gap in
the GR-HMC correctness proof: the paper's fixed six-iteration implementation
does not generally satisfy the exact implicit equations and therefore cannot
discharge `GeneralizedLeapfrogSelection.IsValid` as written. The coverage
audit records this obstruction and the precise corrected assumptions rather
than claiming certification of the experimental AdvancedHMC.jl code.
