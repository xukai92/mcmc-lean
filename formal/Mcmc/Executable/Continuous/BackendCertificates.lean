import Mcmc.Executable.Continuous.BoundedHMC

/-!
# Backend-facing numerical certificates

This module turns bounds for the individual operations performed by a
finite-precision backend into the end-to-end certificates consumed by the
RWMH and endpoint-HMC stability theorems.  It does not assert that an
arbitrary Julia callback, `exp`, or random-number implementation satisfies a
particular bound: those facts are deliberately fields of the certificate.
-/

namespace Mcmc.Executable.Continuous

/-- Operation-level evidence for one scalar RWMH execution.

The proposal bound is derived from the input, scale, and normal-draw bounds;
the log-ratio and threshold bounds are then composed by Lean. -/
structure BackendRwmhCertificate where
  idealCurrent : ℝ
  computedCurrent : ℝ
  idealScale : ℝ
  computedScale : ℝ
  idealNoise : ℝ
  computedNoise : ℝ
  idealCurrentLogDensity : ℝ
  computedCurrentLogDensity : ℝ
  idealProposalLogDensity : ℝ
  computedProposalLogDensity : ℝ
  computedExp : ℝ
  idealUniform : ℝ
  computedUniform : ℝ
  currentError : ℝ
  scaleError : ℝ
  noiseError : ℝ
  currentLogDensityError : ℝ
  proposalLogDensityError : ℝ
  expError : ℝ
  uniformError : ℝ
  current_bound : Approximates computedCurrent idealCurrent currentError
  scale_bound : Approximates computedScale idealScale scaleError
  noise_bound : Approximates computedNoise idealNoise noiseError
  current_logDensity_bound :
    Approximates computedCurrentLogDensity idealCurrentLogDensity
      currentLogDensityError
  proposal_logDensity_bound :
    Approximates computedProposalLogDensity idealProposalLogDensity
      proposalLogDensityError
  exp_bound : Approximates computedExp
    (Real.exp (min 0
      (computedProposalLogDensity - computedCurrentLogDensity))) expError
  uniform_bound : Approximates computedUniform idealUniform uniformError

def BackendRwmhCertificate.idealProposal
    (certificate : BackendRwmhCertificate) : ℝ :=
  certificate.idealCurrent + certificate.idealScale * certificate.idealNoise

def BackendRwmhCertificate.computedProposal
    (certificate : BackendRwmhCertificate) : ℝ :=
  certificate.computedCurrent +
    certificate.computedScale * certificate.computedNoise

def BackendRwmhCertificate.proposalError
    (certificate : BackendRwmhCertificate) : ℝ :=
  certificate.currentError +
    certificate.scaleError * |certificate.computedNoise| +
    |certificate.idealScale| * certificate.noiseError

def BackendRwmhCertificate.logRatioError
    (certificate : BackendRwmhCertificate) : ℝ :=
  certificate.proposalLogDensityError + certificate.currentLogDensityError

def BackendRwmhCertificate.thresholdError
    (certificate : BackendRwmhCertificate) : ℝ :=
  certificate.expError + certificate.logRatioError

/-- Compose primitive RWMH bounds into the certificate expected by the exact
interpreter-refinement theorem. -/
noncomputable def BackendRwmhCertificate.toErrorCertificate
    (certificate : BackendRwmhCertificate) : RwmhErrorCertificate where
  idealCurrent := certificate.idealCurrent
  computedCurrent := certificate.computedCurrent
  idealProposal := certificate.idealProposal
  computedProposal := certificate.computedProposal
  idealLogRatio :=
    certificate.idealProposalLogDensity - certificate.idealCurrentLogDensity
  computedLogRatio :=
    certificate.computedProposalLogDensity - certificate.computedCurrentLogDensity
  idealThreshold := Real.exp (min 0
    (certificate.idealProposalLogDensity - certificate.idealCurrentLogDensity))
  computedThreshold := certificate.computedExp
  idealUniform := certificate.idealUniform
  computedUniform := certificate.computedUniform
  currentError := certificate.currentError
  proposalError := certificate.proposalError
  logRatioError := certificate.logRatioError
  thresholdError := certificate.thresholdError
  uniformError := certificate.uniformError
  current_bound := certificate.current_bound
  proposal_bound := affineProposal_approximates certificate.current_bound
    certificate.scale_bound certificate.noise_bound
  logRatio_bound := logRatio_approximates certificate.proposal_logDensity_bound
    certificate.current_logDensity_bound
  threshold_bound := threshold_approximates_of_exp_error
    (logRatio_approximates certificate.proposal_logDensity_bound
      certificate.current_logDensity_bound) certificate.exp_bound
  uniform_bound := certificate.uniform_bound

/-- Backend-facing endpoint-HMC evidence. Trajectory and Hamiltonian analyses
supply endpoint-energy bounds; Lean composes their difference with the libm
exponential and uniform-draw bounds. -/
structure BackendHmcCertificate where
  computedCurrent : List ℝ
  idealCurrent : List ℝ
  computedProposal : List ℝ
  idealProposal : List ℝ
  computedCurrentEnergy : ℝ
  idealCurrentEnergy : ℝ
  computedProposalEnergy : ℝ
  idealProposalEnergy : ℝ
  computedExp : ℝ
  idealUniform : ℝ
  computedUniform : ℝ
  currentError : ℝ
  proposalError : ℝ
  currentEnergyError : ℝ
  proposalEnergyError : ℝ
  expError : ℝ
  uniformError : ℝ
  current_bound : VectorApproximates computedCurrent idealCurrent currentError
  proposal_bound : VectorApproximates computedProposal idealProposal proposalError
  current_energy_bound :
    Approximates computedCurrentEnergy idealCurrentEnergy currentEnergyError
  proposal_energy_bound :
    Approximates computedProposalEnergy idealProposalEnergy proposalEnergyError
  exp_bound : Approximates computedExp
    (Real.exp (min 0 (computedCurrentEnergy - computedProposalEnergy))) expError
  uniform_bound : Approximates computedUniform idealUniform uniformError

def BackendHmcCertificate.energyError
    (certificate : BackendHmcCertificate) : ℝ :=
  certificate.currentEnergyError + certificate.proposalEnergyError

def BackendHmcCertificate.thresholdError
    (certificate : BackendHmcCertificate) : ℝ :=
  certificate.expError + certificate.energyError

/-- Compose endpoint, energy, libm, and RNG bounds into an HMC decision
certificate. -/
noncomputable def BackendHmcCertificate.toErrorCertificate
    (certificate : BackendHmcCertificate) : HmcErrorCertificate where
  computedCurrent := certificate.computedCurrent
  idealCurrent := certificate.idealCurrent
  computedProposal := certificate.computedProposal
  idealProposal := certificate.idealProposal
  computedEnergyDifference :=
    certificate.computedCurrentEnergy - certificate.computedProposalEnergy
  idealEnergyDifference :=
    certificate.idealCurrentEnergy - certificate.idealProposalEnergy
  computedThreshold := certificate.computedExp
  idealThreshold := Real.exp (min 0
    (certificate.idealCurrentEnergy - certificate.idealProposalEnergy))
  computedUniform := certificate.computedUniform
  idealUniform := certificate.idealUniform
  currentError := certificate.currentError
  proposalError := certificate.proposalError
  energyError := certificate.energyError
  thresholdError := certificate.thresholdError
  uniformError := certificate.uniformError
  current_bound := certificate.current_bound
  proposal_bound := certificate.proposal_bound
  energy_bound := energyDifference_approximates certificate.current_energy_bound
    certificate.proposal_energy_bound
  threshold_bound := hmcThreshold_approximates
    (energyDifference_approximates certificate.current_energy_bound
      certificate.proposal_energy_bound) certificate.exp_bound
  uniform_bound := certificate.uniform_bound

end Mcmc.Executable.Continuous
