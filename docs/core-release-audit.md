# Phase I core release audit

This audit records the evidence for the six Phase I milestones. “Complete”
means that the stated theorem or executable contract exists and passes the
repository checks; it does not silently promote stationarity to convergence or
a backend certificate to a proof about arbitrary floating-point code.

| Milestone | Status | Evidence | Exact boundary |
|---|---|---|---|
| M1. Finite conditional SMC | Complete | `forcedLineageSuffixLaw_mass`, `forcedLineageLaw_mass_eq_scaled_target`, `selectedTrajectoryMass_eq_pathDensity_div`, and `forcedLineageLaw_eq_conditionalSelectedParticleLaw` prove that recursive forced initialization, resampling, propagation, and lineage retention implement the exact conditional selected-particle law on positive supported paths. `conditionalSMCKernel_prob_eq_forcedLineageLaw` connects the implementation to the stationary kernel. | Potentials are strictly positive. The retained initial state and traversed transitions must have positive mass. Zero-mass fibers use the documented identity fallback in the abstract total kernel. |
| M2. Finite particle Gibbs | Complete | `particleGibbsKernel` composes conditional SMC with uniform terminal-index refresh; `particleGibbsKernel_stationary` and `particleGibbs_stationary_selectedTrajectory_expectation` prove extended-target stationarity and the exact normalized Feynman--Kac trajectory marginal. The zero-horizon specialization has exact `N⁻ᵏ` contraction. At positive horizon, primitive finite full support constructs a conservative geometric-TV certificate; scheduled pointwise minorizations retain explicit per-time penalties. The underlying bootstrap SMC population law separately has a fixed-horizon `C/N` MSE and in-probability consistency theorem. | The sharper published PG minorization still requires its model-specific doubly conditional/forced-lineage density estimate. SMC particle-count consistency does not imply particle-count-uniform mixing of the PG Markov chain. |
| M3. Particle-MCMC API consolidation | Complete | `Mcmc.Finite.ParticleMCMC` is the public import surface for pseudo-marginal MH, PIMH, state-indexed PMMH, conditional SMC, and particle Gibbs; `Mcmc.lean` exports it. | The APIs preserve the distinctions between proposal law, extended target, selected trajectory, and requested marginal. |
| M4. Corrected executable Xu--Ge sampler | Complete at the stated executable-contract level | IR version 10, `RelativisticCompilerIR`, and the Julia Reference/Optimized implementations provide corrected diagonal constant-metric relativistic multinomial HMC and a position-dependent certificate-gated client. The radial law includes the dimension Jacobian, spherical direction is Gaussian-normalized, and factor transport uses the inverse. The bounded `2 + sin(q)` formal client now supplies an exact solver with proved reversal and phase-volume preservation. | The constant-metric client is directly executable. Arbitrary position-dependent callbacks still require a valid implicit-solver certificate, and finite Float64 loops are not identified with the exact Banach solve. |
| M5. Certified implicit numerical execution | Complete as a guarded refinement interface | `RelativisticCertificates.lean`, `FiniteFixedPointIsExact`, `FiniteFixedPointIsValid`, and Julia `ImplicitSolveCertificate` expose the exact residual, uniqueness, reversibility, and volume-preservation obligations. Reference and Optimized reject missing or positive-residual certificates. | This is a parallel certification contract, not a completed theorem connecting IEEE floating-point arithmetic to real-valued Lean semantics. |
| M6. Core-project release validation | Complete | The release commands are `lake build`, Julia `Pkg.test()`, `make check-generated`, `make check-docs-generated`, and the Documenter build. The final validation result is recorded in the development log. | Generated IR and graph equality are checked byte-for-byte. Statistical tests remain implementation diagnostics, not mathematical proofs. |

## Claim discipline

- Detailed balance or invariance implies stationarity, not convergence from an
  arbitrary initialization.
- Particle Gibbs is exact for the finite extended target under the hypotheses
  above. Quantitative mixing is proved only for the zero-horizon
  specialization; no positive-horizon rate or particle-efficiency theorem is
  claimed.
- The bounded Xu--Ge position-dependent exact solver now has a machine-checked
  solver certificate. Executable Float64 paths remain conditional on their
  residual/refinement certificate; the deferred floating-point refinement
  layer is still explicit.
