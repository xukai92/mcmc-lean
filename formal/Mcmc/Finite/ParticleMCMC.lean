import Mcmc.Finite.SequentialMonteCarlo

/-!
# Public finite particle-MCMC surface

This module is the stable import for the finite particle-MCMC stack. The
implementation remains layered in `ParticleEstimator` and
`SequentialMonteCarlo`; importing this module exposes:

* explicit SMC histories, normalizing estimates, and genealogy tracing;
* selected-particle targets and many-to-one identities;
* PIMH and fully state-indexed PMMH;
* exact trajectory-conditional refresh; and
* particle Gibbs with stationary selected-path exactness.

These are fixed-particle normalization and stationarity results. They do not
assert irreducibility, convergence from arbitrary initialization, mixing
rates, or consistency as the particle count grows.
-/

namespace Mcmc.Finite.ParticleMCMC

open MarkovKernel
open ParticleEstimator
open SequentialMonteCarlo

/-- Common auxiliary state retained by PIMH and particle Gibbs. -/
abbrev AuxiliaryState (Particle Sample : Type*) [Fintype Sample]
    (steps : List (FeynmanKacStep Sample)) :=
  History (Particle := Particle) steps × Particle

end Mcmc.Finite.ParticleMCMC
