import Mcmc.Hamiltonian.CoupledMixture

/-!
# Executable descriptors for the Xu et al. coupled sampler

The commands name the three shared-randomness transitions consumed by the
Julia IR interpreter. Their ideal denotations are the already verified
maximal-index HMC coupling, sticky Gaussian RWMH coupling, and their mixture.
Finite-precision execution remains subject to the repository's numerical
refinement boundary.
!-/

namespace Mcmc.Executable.Continuous.CoupledXu21

open MeasureTheory ProbabilityTheory Mcmc.Hamiltonian
open scoped NNReal

inductive Command where
  | coupledMultinomialHmc
  | coupledGaussianRwmh
  | coupledMixture

structure ReplayResult (ι : Type*) where
  left : Position ι
  right : Position ι

/-- A replay-level exact meeting event. -/
def ReplayResult.met {ι : Type*} (result : ReplayResult ι) : Prop :=
  result.left = result.right

theorem ReplayResult.met_iff_mem_diagonal {ι : Type*} (result : ReplayResult ι) :
    result.met ↔ (result.left, result.right) ∈ Set.diagonal (Position ι) := by
  simp [ReplayResult.met, Set.mem_diagonal_iff]

variable {ι : Type*} [Fintype ι]

/-- Ideal denotation of the generated coupled multinomial-HMC command. -/
noncomputable def idealHmcKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :=
  maximalSharedMomentumCoupledPositionMultinomialHMC
    potential gradient ε L hpotential hgradient

theorem idealHmcKernel_isCoupling
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    Mcmc.Kernel.IsCoupling
      (idealHmcKernel potential gradient ε L hpotential hgradient)
      (standardPositionMultinomialHMC potential gradient ε L hpotential hgradient)
      (standardPositionMultinomialHMC potential gradient ε L hpotential hgradient) :=
  maximalSharedMomentumCoupledPositionMultinomialHMC_isCoupling
    potential gradient ε L hpotential hgradient

/-- Ideal denotation of the generated sticky Gaussian-RWMH command. -/
noncomputable def idealRwmhKernel
    (potential : Position ι → ℝ) (variance : ℝ≥0) (hvariance : variance ≠ 0) :=
  Mcmc.Kernel.coupledEuclideanGaussianRandomWalkMetropolisHastings
    (positionBoltzmannWeight potential) variance hvariance

theorem idealRwmhKernel_isCoupling
    (potential : Position ι → ℝ) (variance : ℝ≥0) (hvariance : variance ≠ 0)
    (hpotential : Measurable potential) :
    Mcmc.Kernel.IsCoupling (idealRwmhKernel potential variance hvariance)
      (Mcmc.Kernel.euclideanGaussianRandomWalkMetropolisHastings
        (positionBoltzmannWeight potential) variance hvariance)
      (Mcmc.Kernel.euclideanGaussianRandomWalkMetropolisHastings
        (positionBoltzmannWeight potential) variance hvariance) :=
  Mcmc.Kernel.coupledEuclideanGaussianRandomWalkMetropolisHastings_isCoupling
    _ variance hvariance (measurable_positionBoltzmannWeight hpotential)

/-- Ideal denotation of the complete generated Xu et al. coupling command. -/
noncomputable def idealMixtureKernel
    (p : Set.Icc (0 : NNReal) 1)
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) (variance : ℝ≥0)
    (hvariance : variance ≠ 0) :
    Kernel (Position ι × Position ι) (Position ι × Position ι) :=
  coupledHmcRwmhMixture p potential gradient ε L hpotential hgradient
    variance hvariance

/-- Both ideal marginals of the generated coupled command are the verified
single-chain HMC/RWMH mixture. -/
theorem idealMixtureKernel_isCoupling
    (p : Set.Icc (0 : NNReal) 1)
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) (variance : ℝ≥0)
    (hvariance : variance ≠ 0) :
    Mcmc.Kernel.IsCoupling
      (idealMixtureKernel p potential gradient ε L hpotential hgradient
        variance hvariance)
      (hmcRwmhMixture p potential gradient ε L hpotential hgradient
        variance hvariance)
      (hmcRwmhMixture p potential gradient ε L hpotential hgradient
        variance hvariance) :=
  (coupledHmcRwmhMixture_isCoupling_and_invariant p potential gradient ε L
    hpotential hgradient variance hvariance).1

private def quote (value : String) : String := "\"" ++ value ++ "\""

def renderProgram (name operation : String) : String :=
  "(program " ++ quote name ++
    " (inputs (input source \"source\") (input log-density \"logdensity\")" ++
    " (input gradient \"gradient\") (input real \"step_size\")" ++
    " (input nat \"steps\") (input real \"scale\")" ++
    " (input real \"hmc_weight\") (input real-vector \"left\")" ++
    " (input real-vector \"right\")) (body (return (" ++ operation ++
    " (var source \"source\") (var real \"step_size\")" ++
    " (var nat \"steps\") (var real \"scale\")" ++
    " (var real \"hmc_weight\") (var real-vector \"left\")" ++
    " (var real-vector \"right\")))))"

def renderedPrograms : List String :=
  [renderProgram "coupled_multinomial_hmc_step!" "coupled-multinomial-hmc",
   renderProgram "coupled_gaussian_rwmh_step!" "coupled-gaussian-rwmh",
   renderProgram "xu21_coupled_step!" "xu21-coupled-mixture"]

end Mcmc.Executable.Continuous.CoupledXu21
