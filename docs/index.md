# Verified Samplers

Verified Samplers develops machine-checked correctness results for Markov
chain Monte Carlo algorithms in Lean 4, together with an auditable Julia
reference and runtime layer.

The formal development is built directly on mathlib's measure and
`ProbabilityTheory.Kernel` interfaces. It includes general-state
Metropolis--Hastings and Gaussian RWMH, multinomial HMC, coupling and meeting
arguments, and explicit audits of the targeted papers.

## Start here

- [Formalization architecture](architecture.md) explains how the mathematical
  layers fit together.
- [Lean-generated architecture graphs](generated/architecture-graphs.md) show
  dependencies and the executable assurance chain from data maintained in
  Lean.
- [Executable architecture](executable-architecture.md) explains the Lean IR,
  Julia reference interpreter, and optimized implementation.
- [Adding a sampler](development-guide.md) gives the contributor workflow from
  mathematical formalization through IR lowering, refinement, and Julia
  integration.
- [Non-adaptive AdvancedHMC parity](advancedhmc-parity.md) records the current
  fixed-parameter HMC/NUTS runtime-coverage goal and its exclusions.
- [Verified execution and optimization](verified-execution-and-optimization.md)
  separates serialization, execution witnesses, numerical certificates, and
  deliberately lightweight optimization paths.
- [Executable roadmap](executable-roadmap.md) records completed vertical
  slices, including the Xu et al. coupling and Riemannian execution, while
  separating parked platform refinements.
- [Testing strategy](testing.md) separates proved properties from executable,
  differential, and statistical tests.
- [Progress matrix](progress.md) summarizes method-by-property and paper-target
  coverage without hiding conditional or parked boundaries.
- [Core release audit](core-release-audit.md) maps each completed
  milestone to its formal or executable evidence and records its exact scope.
- [Project completion status](project-status.md) reconciles the expanded
  cross-paper goal into one evidence-backed matrix, defines the core release
  boundary, and separates parked research extensions.
- [Development log](development-log.md) records current completed work and
  remaining obligations; its [archive](development-log-archive.md) preserves
  older milestone detail.
- [Overall project roadmap](project-roadmap.md) integrates paper targets,
  executable work, and the broader algorithm scope review.
- [Ge et al. 2018 coverage](ge18-coverage.md) separates the checked
  composable-kernel core of Turing from its implementation and empirical claims.

## Scope boundary

Detailed balance implies stationarity, but stationarity alone does not imply
convergence from arbitrary initial states. The documentation distinguishes
kernel validity, invariance, convergence, meeting-time bounds, and estimator
properties throughout.

The dashed numerical-refinement edge in the generated executable graph is a
deliberately deferred proof obligation. It records the boundary between ideal
real-valued semantics and floating-point execution rather than assuming that
boundary away.
