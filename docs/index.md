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
- [Executable roadmap](executable-roadmap.md) records completed vertical
  slices and the prioritized path to coupled and Riemannian samplers.
- [Testing strategy](testing.md) separates proved properties from executable,
  differential, and statistical tests.
- [Development log](development-log.md) records completed work and remaining
  obligations.

## Scope boundary

Detailed balance implies stationarity, but stationarity alone does not imply
convergence from arbitrary initial states. The documentation distinguishes
kernel validity, invariance, convergence, meeting-time bounds, and estimator
properties throughout.

The dashed numerical-refinement edge in the generated executable graph is a
deliberately deferred proof obligation. It records the boundary between ideal
real-valued semantics and floating-point execution rather than assuming that
boundary away.
