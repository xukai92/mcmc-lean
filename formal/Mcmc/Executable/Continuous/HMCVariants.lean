import Mcmc.Executable.Continuous.HMC
import Mcmc.Hamiltonian.DynamicInvariance

/-!
# State-independent endpoint-HMC schedules

This module packages a finite state-independent mixture of already verified
endpoint-HMC transitions. Both the step size and finite trajectory length may
depend on the independently sampled schedule index. The theorem is useful for
finite jitter and externally selected fixed-integration-time schedules; it does
not identify a continuously distributed floating-point jitter implementation
with this exact kernel.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace Mcmc.Executable.Continuous

open Mcmc.Hamiltonian

variable {ι Schedule : Type*} [Fintype ι] [Fintype Schedule]

/-- Independently choose a finite schedule entry and run its endpoint-HMC
position transition. Schedule weights do not depend on the current position. -/
noncomputable def finiteScheduledEndpointHmcKernel
    (weights : PMF Schedule)
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (stepSize : Schedule → ℝ) (steps : Schedule → Nat)
    (hpotential : Measurable potential) (hgradient : Measurable gradient) :
    Kernel (Position ι) (Position ι) :=
  finiteKernelMixture weights fun schedule =>
    endpointHmcNPositionKernel potential gradient
      (stepSize schedule) (steps schedule) hpotential hgradient

instance finiteScheduledEndpointHmcKernel_isMarkov
    (weights : PMF Schedule)
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (stepSize : Schedule → ℝ) (steps : Schedule → Nat)
    (hpotential : Measurable potential) (hgradient : Measurable gradient) :
    IsMarkovKernel (finiteScheduledEndpointHmcKernel weights potential gradient
      stepSize steps hpotential hgradient) := by
  unfold finiteScheduledEndpointHmcKernel
  infer_instance

/-- Every state-independent finite schedule mixture preserves a common
position target when each endpoint-HMC component has the same explicit
position/momentum factorization. -/
theorem finiteScheduledEndpointHmcKernel_invariant
    (weights : PMF Schedule)
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    (stepSize : Schedule → ℝ) (steps : Schedule → Nat)
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (positionTarget : Measure (Position ι)) [SFinite positionTarget]
    (hfactor : positionTarget.prod standardMomentumMeasure =
      phaseBoltzmannTarget potential) :
    (finiteScheduledEndpointHmcKernel weights potential gradient
      stepSize steps hpotential hgradient).Invariant positionTarget := by
  apply finiteKernelMixture_invariant
  intro schedule
  exact endpointHmcNPositionKernel_invariant hpotential hgradient
    (stepSize schedule) (steps schedule) positionTarget hfactor

end Mcmc.Executable.Continuous
