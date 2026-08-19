# Core release audit

This audit records the evidence for the maintained core release. “Complete”
means that the stated theorem or executable contract exists and passes the
repository checks; it does not silently promote stationarity to convergence or
an exact-real theorem to arbitrary floating-point code. Optional numerical
certification and theorem-heavy research endpoints are classified separately
in [project completion status](project-status.md#core-completion-boundary).

| Milestone | Status | Evidence | Exact boundary |
|---|---|---|---|
| M1. Finite conditional SMC | Complete | `forcedLineageSuffixLaw_mass`, `forcedLineageLaw_mass_eq_scaled_target`, `selectedTrajectoryMass_eq_pathDensity_div`, and `forcedLineageLaw_eq_conditionalSelectedParticleLaw` prove that recursive forced initialization, resampling, propagation, and lineage retention implement the exact conditional selected-particle law on positive supported paths. `conditionalSMCKernel_prob_eq_forcedLineageLaw` connects the implementation to the stationary kernel. | Potentials are strictly positive. The retained initial state and traversed transitions must have positive mass. Zero-mass fibers use the documented identity fallback in the abstract total kernel. |
| M2. Finite particle Gibbs | Complete | `particleGibbsKernel` composes conditional SMC with uniform terminal-index refresh; `particleGibbsKernel_stationary` and `particleGibbs_stationary_selectedTrajectory_expectation` prove extended-target stationarity and the exact normalized Feynman--Kac trajectory marginal. The zero-horizon specialization has exact `N⁻ᵏ` contraction. At positive horizon, `backwardPotentialScheduledParticleGibbsMinorization` constructs a scheduled minorization from primitive finite full support, using cumulative backward-potential oscillations. It yields fixed-count geometric TV convergence, an actual fixed-iteration particle-count limit, and—by monotonicity of the schedule coefficient—one geometric rate uniform over all particle counts `N ≥ 2` at each fixed horizon. For the first positive horizon, `singletonRawPotentialScheduledParticleGibbsMinorization` proves that the raw-current and backward schedules coincide and supplies the raw-potential TV theorem. | At horizons greater than one, the proved schedule uses full remaining backward potentials; recursively replacing these by only raw current potentials remains a stronger candidate, not a theorem. No claim of a horizon-uniform rate, joint growing-horizon/count limit, or iteration-count-growing particle limit is made. |
| M3. Particle-MCMC API consolidation | Complete | `Mcmc.Finite.ParticleMCMC` is the public import surface for pseudo-marginal MH, PIMH, state-indexed PMMH, conditional SMC, and particle Gibbs; `Mcmc.lean` exports it. | The APIs preserve the distinctions between proposal law, extended target, selected trajectory, and requested marginal. |
| M4. Corrected executable Xu--Ge sampler | Complete at the stated executable-contract level | IR version 10, `RelativisticCompilerIR`, and the Julia Reference/Optimized implementations provide corrected diagonal constant-metric relativistic multinomial HMC and a position-dependent certificate-gated client. The radial law includes the dimension Jacobian, spherical direction is Gaussian-normalized, and factor transport uses the inverse. The bounded `2 + sin(q)` formal client now supplies an exact solver with proved reversal and phase-volume preservation. | The constant-metric client is directly executable. Arbitrary position-dependent callbacks still require a valid implicit-solver certificate, and finite Float64 loops are not identified with the exact Banach solve. |
| M5. Maintained executable integration | Complete | Public Julia paths cover finite MH, RWMH/HMC, corrected relativistic multinomial HMC, PG--HMC composition, particle Gibbs, practical slice, reversible jump, and checked dynamic-tree methods. The test runner exercises Reference/Optimized or trace/oracle agreement where those contracts exist, plus seeded diagnostics. | Runtime tests establish implementation conformance and catch regressions; statistical and finite-difference diagnostics are not mathematical proofs. |
| M6. Core-project release validation | Complete; documentation re-audited 2026-08-19 | The end-to-end `make test` gate passes: the full Lean library and compiled oracle build, generated IR agrees byte-for-byte, and every registered Julia suite passes. Generated docs, Documenter rendering, `git diff --check`, and a Lean-source scan for `sorry`/`admit`/`axiom` placeholders also pass. | Statistical diagnostics remain evidence about maintained implementations, not mathematical proofs. A later source change invalidates this evidence until the relevant gates are rerun. |

## Optional retained research layer

`RelativisticCertificates.lean`, the Julia `Certificates` module, and the Lean
oracle retain guarded per-execution numerical certificates. They are built and
tested because they are valuable audit infrastructure. Core completion does
not require extending them to generic IEEE-754, platform `libm`, serializer,
or RNG correctness, nor completing multi-step floating-point GR-HMC transport.
Likewise, the parked BPS, production-NUTS-equivalence, adaptation, and broad
particle-stability endpoints are not release blockers.

## Claim discipline

- Detailed balance or invariance implies stationarity, not convergence from an
  arbitrary initialization.
- Particle Gibbs is exact for the finite extended target under the hypotheses
  above. Primitive finite full-support models now have a conservative
  positive-horizon geometric-TV certificate, and scheduled pointwise
  minorization coefficients are explicit. The sharper published coefficient
  is not proved. Particle-count-uniform geometric mixing is proved only at
  each fixed horizon; horizon-uniform efficiency is not claimed.
- The bounded Xu--Ge position-dependent exact solver has machine-checked exact
  reversal, phase-volume, and invariance results. Optional executable
  certificates remain conditional records; no generic Float64 refinement is
  inferred or required by the core release.
