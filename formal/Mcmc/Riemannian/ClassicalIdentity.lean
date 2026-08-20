import Mcmc.Riemannian.Classical
import Mcmc.Executable.Continuous.SeparableGeneralizedLeapfrog

/-!
# Concrete identity-metric classical RMHMC client

The identity metric is a small compiled example of the classical RMHMC API.
It reduces to ordinary Gaussian-momentum HMC, but exercises the same
position-dependent augmentation, generalized-leapfrog, Metropolis, and
projection theorem used by nonconstant metrics.
-/

namespace Mcmc.Riemannian

open MeasureTheory ProbabilityTheory
open Mcmc.Hamiltonian
open Mcmc.Executable.Continuous

variable {ι : Type*} [Fintype ι]

@[simp]
theorem identity_gaussianMomentumMeasure (q : Position ι) :
    gaussianMomentumMeasure
        (identityFactoredMetric (ι := ι)) q =
      standardMomentumMeasure := by
  unfold gaussianMomentumMeasure
  exact Measure.map_id

theorem identity_isMeasurableGaussianMomentumFamily :
    IsMeasurableGaussianMomentumFamily
      (identityFactoredMetric (ι := ι)) := by
  intro s hs
  simp only [identity_gaussianMomentumMeasure]
  exact measurable_const

@[simp]
theorem identity_gaussianMomentumWeight (q : Position ι) (p : Momentum ι) :
    gaussianMomentumWeight (identityFactoredMetric (ι := ι)) q p =
      Mcmc.Kernel.isotropicGaussianPDF 1 p := by
  simp [gaussianMomentumWeight]

theorem identity_isMeasurableGaussianMomentumWeight :
    IsMeasurableGaussianMomentumWeight
      (identityFactoredMetric (ι := ι)) := by
  unfold IsMeasurableGaussianMomentumWeight
  rw [show Function.uncurry (gaussianMomentumWeight
      (identityFactoredMetric (ι := ι))) =
      fun z : PhaseSpace ι => Mcmc.Kernel.isotropicGaussianPDF 1 z.2 by
    funext z
    exact identity_gaussianMomentumWeight z.1 z.2]
  exact Mcmc.Kernel.measurable_isotropicGaussianPDF 1 |>.comp measurable_snd

/-- Unit inverse-mass velocity as a certified constant metric. -/
def unitConstantMetric : ConstantMetric ι where
  velocity p := p
  measurable_velocity := measurable_id
  velocity_odd _ := rfl

/-- Fully discharged classical identity-metric RMHMC invariance theorem. -/
theorem identity_positionEndpointMetropolis_invariant
    {potential : Position ι → ℝ} (hpotential : Measurable potential)
    (gradient : Position ι → Momentum ι) (hgradient : Measurable gradient)
    (ε : ℝ) :
    (positionEndpointMetropolis potential
      (identityFactoredMetric (ι := ι))
      identity_isMeasurableGaussianMomentumFamily
      (separableGeneralizedLeapfrogSelection
        (unitConstantMetric (ι := ι)).velocity gradient)
      (separableGeneralizedLeapfrogSelection_valid unitConstantMetric gradient
        hgradient) ε).Invariant (positionBoltzmannTarget potential) := by
  exact positionEndpointMetropolis_invariant hpotential
    identityFactoredMetric identityFactoredMetric_hasCompatibleFactorVolume
    identity_isMeasurableGaussianMomentumFamily
    identity_isMeasurableGaussianMomentumWeight
    (separableGeneralizedLeapfrogSelection unitConstantMetric.velocity gradient)
    (separableGeneralizedLeapfrogSelection_valid unitConstantMetric gradient
      hgradient) ε

end Mcmc.Riemannian
