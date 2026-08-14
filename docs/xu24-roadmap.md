# Xu and Ge 2024 formalization roadmap

The next theorem target is Kai Xu and Hong Ge, “Practical Hamiltonian Monte
Carlo on Riemannian Manifolds via Relativity Theory,” ICML 2024.  The paper is
primarily an algorithm and validity paper: Section 5.2 gives an informal
correctness argument rather than a numbered convergence theorem.  This
roadmap therefore treats construction of the actual GR-HMC kernel and a proof
of target invariance as the principal endpoint.

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

## Paper-statement audit

The completed item-by-item status table is maintained in
[the Xu--Ge coverage audit](xu24-coverage.md). This roadmap retains the design
rationale and milestone history.

### Multivariate momentum sampler

Equation (10) derives a radial density proportional to
`exp(-K(r)) * r` in two dimensions.  Algorithm 1 then applies that same radial
law in general dimension and samples the spherical-coordinate angles
independently and uniformly.  Those instructions require correction for
dimension greater than two: polar change of variables contributes the radial
Jacobian `r^(d-1)`, and independent uniform spherical angles do not produce a
uniform direction on a higher-dimensional sphere.

The formalization will preserve a faithful representation of the printed
algorithm where useful, but will not claim that it samples the stated
multivariate momentum law in arbitrary dimension.  The corrected construction
will use a uniform spherical direction (for example, normalized Gaussian
coordinates) and the dimension-dependent radial law.  Its pushforward must be
proved equal to the desired momentum measure before it is used by GR-HMC.

There is also a representation-level distinction inside Lean. The project
stores momentum as a finite function `ι → ℝ`; mathlib gives that type the
product/sup norm, while the Hamiltonian uses the Euclidean `L²` norm. A radial
density written directly as a function of mathlib's ambient `‖p‖` would
therefore be wrong in dimension greater than one. The corrected construction
now builds the polar law on `EuclideanSpace ℝ ι` and transports it through
mathlib's volume-preserving coordinate equivalence. Lean proves that the
transported density is exactly the Hamiltonian's Euclidean momentum density.

### Algorithm validity

Section 5.2 appeals informally to symmetry of the momentum distribution,
generalized leapfrog integration, and established Metropolis or multinomial
corrections.  In the formalization these become separate explicit obligations:

- the position-dependent momentum law has the claimed density and
  normalization;
- the implicit generalized leapfrog equations have a selected solution;
- the selected numerical map is measurable, reversible, and volume
  preserving; and
- the corrected transition preserves the intended joint and position
  targets.

No claim of target invariance will be made from momentum symmetry alone.

### Affine transformation in Algorithm 1

With the paper's factorization `A_qᵀ A_q = G_q⁻¹`, Equation (8) depends on
`‖A_q p‖²`.  Therefore an isotropic relativistic draw `z` must be transported
as

```text
p = A_q⁻¹ z,
```

which makes `A_q p = z`.  Algorithm 1 instead prints `p = A_qᵀ z`.  These maps
are not equal for a general metric; even in one dimension they have reciprocal
scales.  The formalized conditional momentum measure uses the inverse factor.
Any alternative convention must change the stated factorization consistently.

### Velocity formula and bound after Equation (9)

Let `A_qᵀ A_q = G_q⁻¹`.  Equation (8) depends on
`pᵀ G_q⁻¹ p = ‖A_q p‖²`, so direct differentiation with respect to momentum
gives

```text
v(q,p) = G_q⁻¹ p / M(q,p),
M(q,p) = m * sqrt(‖A_q p‖² / (m² c²) + 1).
```

The printed left-hand side `v_G := ∇q H` is also inconsistent with Hamilton's
equations: velocity is the momentum derivative `∇p H`. The Lean definition
uses the momentum derivative.

The printed Equation (9) instead writes `M_G(q, A_q p)` and then replaces its
quadratic form by `pᵀp`; that substitution does not follow from
`A_qᵀ A_q = G_q⁻¹`.  The following displayed bound
`‖A_q p‖ / ‖p‖ * c` is likewise not the general norm bound for an anisotropic
metric.  Without additional spectral or alignment assumptions, the direct
bound is

```text
‖v(q,p)‖ < c * ‖G_q⁻¹ p‖ / ‖A_q p‖.
```

The Lean interface keeps the factor `A_q` and inverse-metric action `G_q⁻¹`
separate and proves this corrected bound.  Lean also gives the explicit
two-dimensional counterexample `A = diag(2,1)`, `G⁻¹ = diag(4,1)`, and
`p = (1,1)`: the corrected ratio `‖G⁻¹p‖/‖Ap‖` is strictly larger than the
printed `‖Ap‖/‖p‖` ratio.

### Numerical stability

The paper's comparative stability and efficiency results are empirical.
Machine-checkable replacements require a specified error quantity and explicit
analytic assumptions.  The pointwise velocity-bound theorem is a precise
formal target; a universal claim that GR-HMC has smaller numerical error than
RHMC is not inferred from that bound alone.

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
