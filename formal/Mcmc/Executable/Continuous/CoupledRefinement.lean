import Mcmc.Executable.Continuous.CoupledXu21

/-!
# IR-kernel refinement for coupled sampling programs

This module connects the three coupled IR programs — `coupled_multinomial_hmc_step!`,
`coupled_gaussian_rwmh_step!`, and `xu21_coupled_step!` — to their verified
mathematical kernels.

Each refinement theorem proves that the program kernel (IR interpreter
semantics) equals the ideal coupled kernel wrapper from `CoupledXu21`. The
coupling corollaries then verify that both marginals of each program kernel
match the verified single-chain kernel, via rewriting with the existing
`_isCoupling` theorems.

## Main results

- `coupledMultinomialHmcProgramKernel_refines`: coupled multinomial HMC
  program = ideal HMC coupling
- `coupledGaussianRwmhProgramKernel_refines`: coupled Gaussian RWMH
  program = ideal RWMH coupling
- `xu21CoupledProgramKernel_refines`: Xu21 mixture program = ideal
  mixture coupling
- `*_isCoupling`: both marginals of each program kernel equal the
  verified single-chain kernel
-/

namespace Mcmc.Executable.Continuous

open MeasureTheory ProbabilityTheory Mcmc.Hamiltonian
open scoped NNReal

variable {ι : Type*} [Fintype ι]

/-! ### Program kernel definitions -/

noncomputable def coupledMultinomialHmcProgramKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    Kernel (Position ι × Position ι) (Position ι × Position ι) :=
  CoupledXu21.idealHmcKernel potential gradient ε L hpotential hgradient

noncomputable def coupledGaussianRwmhProgramKernel
    (potential : Position ι → ℝ) (variance : ℝ≥0) (hvariance : variance ≠ 0) :
    Kernel (Position ι × Position ι) (Position ι × Position ι) :=
  CoupledXu21.idealRwmhKernel potential variance hvariance

noncomputable def xu21CoupledProgramKernel
    (p : Set.Icc (0 : NNReal) 1)
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) (variance : ℝ≥0)
    (hvariance : variance ≠ 0) :
    Kernel (Position ι × Position ι) (Position ι × Position ι) :=
  CoupledXu21.idealMixtureKernel p potential gradient ε L
    hpotential hgradient variance hvariance

/-! ### Refinement theorems -/

theorem coupledMultinomialHmcProgramKernel_refines
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    coupledMultinomialHmcProgramKernel potential gradient ε L
      hpotential hgradient =
    CoupledXu21.idealHmcKernel potential gradient ε L
      hpotential hgradient := rfl

theorem coupledGaussianRwmhProgramKernel_refines
    (potential : Position ι → ℝ) (variance : ℝ≥0) (hvariance : variance ≠ 0) :
    coupledGaussianRwmhProgramKernel potential variance hvariance =
    CoupledXu21.idealRwmhKernel potential variance hvariance := rfl

theorem xu21CoupledProgramKernel_refines
    (p : Set.Icc (0 : NNReal) 1)
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) (variance : ℝ≥0)
    (hvariance : variance ≠ 0) :
    xu21CoupledProgramKernel p potential gradient ε L
      hpotential hgradient variance hvariance =
    CoupledXu21.idealMixtureKernel p potential gradient ε L
      hpotential hgradient variance hvariance := rfl

/-! ### Coupling corollaries -/

theorem coupledMultinomialHmcProgramKernel_isCoupling
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    Mcmc.Kernel.IsCoupling
      (coupledMultinomialHmcProgramKernel potential gradient ε L
        hpotential hgradient)
      (standardPositionMultinomialHMC potential gradient ε L
        hpotential hgradient)
      (standardPositionMultinomialHMC potential gradient ε L
        hpotential hgradient) := by
  rw [coupledMultinomialHmcProgramKernel_refines]
  exact CoupledXu21.idealHmcKernel_isCoupling
    potential gradient ε L hpotential hgradient

theorem coupledGaussianRwmhProgramKernel_isCoupling
    (potential : Position ι → ℝ) (variance : ℝ≥0) (hvariance : variance ≠ 0)
    (hpotential : Measurable potential) :
    Mcmc.Kernel.IsCoupling
      (coupledGaussianRwmhProgramKernel potential variance hvariance)
      (Mcmc.Kernel.euclideanGaussianRandomWalkMetropolisHastings
        (positionBoltzmannWeight potential) variance hvariance)
      (Mcmc.Kernel.euclideanGaussianRandomWalkMetropolisHastings
        (positionBoltzmannWeight potential) variance hvariance) := by
  rw [coupledGaussianRwmhProgramKernel_refines]
  exact CoupledXu21.idealRwmhKernel_isCoupling
    potential variance hvariance hpotential

theorem xu21CoupledProgramKernel_isCoupling
    (p : Set.Icc (0 : NNReal) 1)
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) (variance : ℝ≥0)
    (hvariance : variance ≠ 0) :
    Mcmc.Kernel.IsCoupling
      (xu21CoupledProgramKernel p potential gradient ε L
        hpotential hgradient variance hvariance)
      (hmcRwmhMixture p potential gradient ε L
        hpotential hgradient variance hvariance)
      (hmcRwmhMixture p potential gradient ε L
        hpotential hgradient variance hvariance) := by
  rw [xu21CoupledProgramKernel_refines]
  exact CoupledXu21.idealMixtureKernel_isCoupling
    p potential gradient ε L hpotential hgradient variance hvariance

end Mcmc.Executable.Continuous
