import Mcmc.Relativistic.Multinomial
import Mcmc.Relativistic.ConstantMetric
import Mcmc.Executable.Continuous.RelativisticCompilerIR

/-!
# IR-kernel refinement for relativistic multinomial HMC programs

This module connects the relativistic multinomial HMC IR program descriptors
(`relativistic_multinomial_hmc_step!` and
`certified_relativistic_multinomial_hmc_step!`) to their verified mathematical
kernel `Relativistic.positionMultinomialGRHMC`.

The constant-metric program uses `identityFactoredRiemannianMetric`; the
certified position-dependent program takes a general
`FactoredRiemannianMetric ι`. Both refinement theorems hold by definitional
equality, conditional on the solver certificate
`GeneralizedLeapfrogSelection.IsValid`.
-/

namespace Mcmc.Executable.Continuous

open Mcmc.Hamiltonian Mcmc.Kernel Mcmc.Relativistic MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-! ### Constant-metric relativistic multinomial HMC -/

/-- Position kernel for the `relativistic_multinomial_hmc_step!` IR program,
using the constant identity metric. -/
noncomputable def relativisticMultinomialHmcProgramKernel
    [Nonempty ι] [DecidableEq ι]
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (potential : Position ι → ℝ) (m c : ℝ)
    (hm : 0 < m) (hc : 0 < c)
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid)
    (hH : Measurable
      (generalRelativisticHamiltonian potential
        (identityFactoredRiemannianMetric (ι := ι)) m c))
    (hmeasurableMomentum :
      IsMeasurableRiemannianMomentumFamily
        (identityFactoredRiemannianMetric (ι := ι)) m c hm hc)
    (ε : ℝ) (L : ℕ) :
    Kernel (Position ι) (Position ι) :=
  positionMultinomialGRHMC potential (identityFactoredRiemannianMetric (ι := ι))
    m c hm hc selection hvalid hH hmeasurableMomentum ε L

/-- The `relativistic_multinomial_hmc_step!` IR program kernel equals the
verified identity-metric multinomial GR-HMC position kernel. -/
theorem relativisticMultinomialHmcProgramKernel_refines
    [Nonempty ι] [DecidableEq ι]
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (potential : Position ι → ℝ) (m c : ℝ)
    (hm : 0 < m) (hc : 0 < c)
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid)
    (hH : Measurable
      (generalRelativisticHamiltonian potential
        (identityFactoredRiemannianMetric (ι := ι)) m c))
    (hmeasurableMomentum :
      IsMeasurableRiemannianMomentumFamily
        (identityFactoredRiemannianMetric (ι := ι)) m c hm hc)
    (ε : ℝ) (L : ℕ) :
    relativisticMultinomialHmcProgramKernel potential m c hm hc
      selection hvalid hH hmeasurableMomentum ε L =
    positionMultinomialGRHMC potential (identityFactoredRiemannianMetric (ι := ι))
      m c hm hc selection hvalid hH hmeasurableMomentum ε L := by
  rfl

/-! ### Certified position-dependent relativistic multinomial HMC -/

/-- Position kernel for the `certified_relativistic_multinomial_hmc_step!` IR
program, with a general position-dependent metric and solver certificate. -/
noncomputable def certifiedRelativisticMultinomialHmcProgramKernel
    [Nonempty ι] [DecidableEq ι]
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (potential : Position ι → ℝ)
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (hm : 0 < m) (hc : 0 < c)
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid)
    (hH : Measurable
      (generalRelativisticHamiltonian potential metric m c))
    (hmeasurableMomentum :
      IsMeasurableRiemannianMomentumFamily metric m c hm hc)
    (ε : ℝ) (L : ℕ) :
    Kernel (Position ι) (Position ι) :=
  positionMultinomialGRHMC potential metric m c hm hc
    selection hvalid hH hmeasurableMomentum ε L

/-- The `certified_relativistic_multinomial_hmc_step!` IR program kernel
equals the verified position-dependent multinomial GR-HMC position kernel. -/
theorem certifiedRelativisticMultinomialHmcProgramKernel_refines
    [Nonempty ι] [DecidableEq ι]
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (potential : Position ι → ℝ)
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (hm : 0 < m) (hc : 0 < c)
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid)
    (hH : Measurable
      (generalRelativisticHamiltonian potential metric m c))
    (hmeasurableMomentum :
      IsMeasurableRiemannianMomentumFamily metric m c hm hc)
    (ε : ℝ) (L : ℕ) :
    certifiedRelativisticMultinomialHmcProgramKernel potential metric m c
      hm hc selection hvalid hH hmeasurableMomentum ε L =
    positionMultinomialGRHMC potential metric m c hm hc
      selection hvalid hH hmeasurableMomentum ε L := by
  rfl

end Mcmc.Executable.Continuous
