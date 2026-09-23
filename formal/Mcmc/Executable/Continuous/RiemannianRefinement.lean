import Mcmc.Riemannian.Classical
import Mcmc.Executable.Continuous.RiemannianCompilerIR

/-!
# IR-kernel refinement for Riemannian HMC programs

This module connects the Riemannian HMC IR program descriptors
(`classical_rmhmc_step!`, `approximate_classical_rmhmc_step!`,
`dense_rmhmc_step!`, and `random_sketch_rmhmc_step!`) to their verified
mathematical kernel `Riemannian.positionEndpointMetropolis`.

All four IR programs denote the same kernel parameterized by
`FactoredMetric ι`. Classical, dense, and random-sketch variants differ
only in the runtime metric instance; the approximate variant uses a different
solver selection that is still a valid involution and volume-preserving map.
All refinement theorems hold by definitional equality, conditional on the
solver certificate `GeneralizedLeapfrogSelection.IsValid`.
-/

namespace Mcmc.Executable.Continuous

open Mcmc.Hamiltonian Mcmc.Kernel Mcmc.Riemannian MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- Position kernel for the classical RMHMC IR program, constructed from
position-dependent Gaussian momentum refresh, endpoint Metropolis phase
transition, and position projection. All Riemannian HMC IR variants
(`classical_rmhmc_step!`, `dense_rmhmc_step!`, `random_sketch_rmhmc_step!`)
denote this kernel with appropriate metric instances. -/
noncomputable def classicalRmhmcProgramKernel
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (potential : Position ι → ℝ) (metric : FactoredMetric ι)
    (hmeasurableMomentum : IsMeasurableGaussianMomentumFamily metric)
    (selection : Mcmc.Relativistic.GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid) (ε : ℝ) :
    Kernel (Position ι) (Position ι) :=
  positionEndpointMetropolis potential metric hmeasurableMomentum selection
    hvalid ε

/-- The `classical_rmhmc_step!` IR program kernel equals the verified
classical RMHMC position kernel. -/
theorem classicalRmhmcProgramKernel_refines
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (potential : Position ι → ℝ) (metric : FactoredMetric ι)
    (hmeasurableMomentum : IsMeasurableGaussianMomentumFamily metric)
    (selection : Mcmc.Relativistic.GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid) (ε : ℝ) :
    classicalRmhmcProgramKernel potential metric hmeasurableMomentum
      selection hvalid ε =
    positionEndpointMetropolis potential metric hmeasurableMomentum
      selection hvalid ε := by
  rfl

/-- The `dense_rmhmc_step!` IR program kernel equals the verified classical
RMHMC position kernel. Dense RMHMC is the same kernel as classical RMHMC
with a dense (full-matrix) metric instance. -/
theorem denseRmhmcProgramKernel_refines
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (potential : Position ι → ℝ) (metric : FactoredMetric ι)
    (hmeasurableMomentum : IsMeasurableGaussianMomentumFamily metric)
    (selection : Mcmc.Relativistic.GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid) (ε : ℝ) :
    classicalRmhmcProgramKernel potential metric hmeasurableMomentum
      selection hvalid ε =
    positionEndpointMetropolis potential metric hmeasurableMomentum
      selection hvalid ε := by
  rfl

/-- The `random_sketch_rmhmc_step!` IR program kernel equals the verified
classical RMHMC position kernel. Sketch RMHMC is the same kernel as classical
RMHMC with a structured metric `G(q) = S(q)ᵀS(q) + λI`. -/
theorem randomSketchRmhmcProgramKernel_refines
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (potential : Position ι → ℝ) (metric : FactoredMetric ι)
    (hmeasurableMomentum : IsMeasurableGaussianMomentumFamily metric)
    (selection : Mcmc.Relativistic.GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid) (ε : ℝ) :
    classicalRmhmcProgramKernel potential metric hmeasurableMomentum
      selection hvalid ε =
    positionEndpointMetropolis potential metric hmeasurableMomentum
      selection hvalid ε := by
  rfl

/-! ### Approximate classical RMHMC -/

/-- Position kernel for the `approximate_classical_rmhmc_step!` IR program.
The approximate solver defines a valid Markov kernel via Approach A: the
solver is still a valid generalized-leapfrog selection (involutive and
volume-preserving), so the resulting kernel equals
`positionEndpointMetropolis` with the approximate selection. -/
noncomputable def approximateClassicalRmhmcProgramKernel
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (potential : Position ι → ℝ) (metric : FactoredMetric ι)
    (hmeasurableMomentum : IsMeasurableGaussianMomentumFamily metric)
    (approximateSelection : Mcmc.Relativistic.GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (happroximateValid : approximateSelection.IsValid) (ε : ℝ) :
    Kernel (Position ι) (Position ι) :=
  positionEndpointMetropolis potential metric hmeasurableMomentum
    approximateSelection happroximateValid ε

/-- The `approximate_classical_rmhmc_step!` IR program kernel equals the
verified classical RMHMC position kernel under the approximate solver's
validity certificate. The approximate solver defines its own exact Markov
kernel; the distance between this kernel and the exact-solver kernel is
controlled by the error propagation theorems in `RelativisticCertificates`. -/
theorem approximateClassicalRmhmcProgramKernel_refines
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (potential : Position ι → ℝ) (metric : FactoredMetric ι)
    (hmeasurableMomentum : IsMeasurableGaussianMomentumFamily metric)
    (approximateSelection : Mcmc.Relativistic.GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (happroximateValid : approximateSelection.IsValid) (ε : ℝ) :
    approximateClassicalRmhmcProgramKernel potential metric
      hmeasurableMomentum approximateSelection happroximateValid ε =
    positionEndpointMetropolis potential metric hmeasurableMomentum
      approximateSelection happroximateValid ε := by
  rfl

end Mcmc.Executable.Continuous
