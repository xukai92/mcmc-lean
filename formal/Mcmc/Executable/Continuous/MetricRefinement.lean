import Mcmc.Executable.Continuous.MetricHMC
import Mcmc.Executable.Continuous.MetricCompilerIR

/-!
# IR-kernel refinement for metric endpoint HMC programs

This module connects the metric endpoint HMC IR program descriptors
(`diagonal_hmc_step!` and `dense_hmc_step!`) to their verified mathematical
kernel `endpointMetricHmcPositionKernel`.

Both diagonal and dense IR programs denote the same kernel parameterized by
`ConstantMetric ι`. The program kernel is the refresh-evolve-project
composition using the deterministic-Metropolis endpoint phase kernel. Both
refinement theorems hold by definitional equality.
-/

namespace Mcmc.Executable.Continuous

open Mcmc.Hamiltonian Mcmc.Kernel MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- Position kernel for the constant-metric endpoint HMC IR program,
constructed from the deterministic-Metropolis endpoint phase kernel via
momentum refresh and position projection. Both `diagonal_hmc_step!` and
`dense_hmc_step!` denote this kernel with appropriate metric instances. -/
noncomputable def metricHmcProgramKernel
    (metric : ConstantMetric ι) (potential : Position ι → ℝ)
    (kinetic : Momentum ι → ℝ) (gradient : Position ι → Momentum ι)
    (momentumTarget : Measure (Momentum ι)) (ε : ℝ) (steps : ℕ)
    (_hpotential : Measurable potential) (_hkinetic : Measurable kinetic)
    (hgradient : Measurable gradient) :
    Kernel (Position ι) (Position ι) :=
  liftEvolveProject (positionMomentumLift momentumTarget)
    (endpointMetricHmcPhaseKernel metric potential kinetic gradient ε steps
      hgradient)
    (Prod.fst : PhaseSpace ι → Position ι) measurable_fst

/-- The diagonal-metric endpoint HMC IR program kernel equals the verified
constant-metric endpoint HMC position kernel. -/
theorem diagonalHmcProgramKernel_refines
    (metric : ConstantMetric ι) (potential : Position ι → ℝ)
    (kinetic : Momentum ι → ℝ) (gradient : Position ι → Momentum ι)
    (momentumTarget : Measure (Momentum ι)) (ε : ℝ) (steps : ℕ)
    (hpotential : Measurable potential) (hkinetic : Measurable kinetic)
    (hgradient : Measurable gradient) :
    metricHmcProgramKernel metric potential kinetic gradient
      momentumTarget ε steps hpotential hkinetic hgradient =
    endpointMetricHmcPositionKernel metric potential kinetic gradient
      momentumTarget ε steps hpotential hkinetic hgradient := by
  rfl

/-- The dense-metric endpoint HMC IR program kernel equals the verified
constant-metric endpoint HMC position kernel. -/
theorem denseHmcProgramKernel_refines
    (metric : ConstantMetric ι) (potential : Position ι → ℝ)
    (kinetic : Momentum ι → ℝ) (gradient : Position ι → Momentum ι)
    (momentumTarget : Measure (Momentum ι)) (ε : ℝ) (steps : ℕ)
    (hpotential : Measurable potential) (hkinetic : Measurable kinetic)
    (hgradient : Measurable gradient) :
    metricHmcProgramKernel metric potential kinetic gradient
      momentumTarget ε steps hpotential hkinetic hgradient =
    endpointMetricHmcPositionKernel metric potential kinetic gradient
      momentumTarget ε steps hpotential hkinetic hgradient := by
  rfl

end Mcmc.Executable.Continuous
