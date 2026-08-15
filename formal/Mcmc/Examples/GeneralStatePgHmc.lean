import Mcmc.Executable.Continuous.GaussianSoftAbsConvergence
import Mcmc.Kernel.ComposableInference
import Mathlib.Probability.Distributions.Uniform

/-!
# A mixed discrete/continuous general-state PG--HMC client

This example instantiates the composable-inference theorem with a continuous
Gaussian SoftAbs target and a finite Boolean auxiliary block.  The auxiliary
model is deliberately elementary (the Boolean variable is independent), but
the two engines are concrete: an exact two-block auxiliary refresh is followed
by the proved multinomial Gaussian SoftAbs GR-HMC transition.
-/

namespace Mcmc.Examples.GeneralStatePgHmc

open MeasureTheory ProbabilityTheory
open Mcmc.Executable.Continuous Mcmc.Hamiltonian

abbrev ContinuousState := Position Unit

/-- Normalized continuous target used by both engines. -/
noncomputable def target : Measure ContinuousState :=
  Mcmc.Kernel.finiteNormalize
    (gaussianSoftAbsPositionTarget (ι := Unit))

/-- Uniform two-state auxiliary law. -/
noncomputable def latentLaw : Measure Bool :=
  (PMF.uniformOfFintype Bool).toMeasure

instance target.instIsProbabilityMeasure : IsProbabilityMeasure target := by
  unfold target
  infer_instance

instance latentLaw.instIsProbabilityMeasure : IsProbabilityMeasure latentLaw := by
  unfold latentLaw
  infer_instance

/-- Draw the independent Boolean auxiliary. -/
noncomputable def particleForward : Kernel ContinuousState Bool :=
  Kernel.const ContinuousState latentLaw

/-- Redraw the continuous state from its exact conditional (the target itself
in this independent model). -/
noncomputable def particleReverse : Kernel Bool ContinuousState :=
  Kernel.const Bool target

instance : IsMarkovKernel particleForward := by
  unfold particleForward latentLaw
  infer_instance

instance : IsMarkovKernel particleReverse := by
  unfold particleReverse target
  infer_instance

/-- The independent mixed model satisfies the exact Bayes factorization used
by the auxiliary-variable PG theorem. -/
theorem auxiliary_factorization :
    Mcmc.Kernel.auxiliaryFirstJoint target particleForward =
      (particleForward ∘ₘ target) ⊗ₘ particleReverse := by
  unfold Mcmc.Kernel.auxiliaryFirstJoint particleForward particleReverse
    latentLaw target
  rw [Measure.compProd_const, Measure.compProd_const]
  rw [Measure.const_comp]
  simp only [measure_univ, one_smul]
  exact Measure.prod_swap

/-- Concrete mixed discrete/continuous PG--GR-HMC stationarity theorem. -/
theorem pg_grhmc_invariant (ε : ℝ) (L : ℕ) :
    (Mcmc.Kernel.ComposableInference.pgHmcKernel
      (Mcmc.Kernel.twoBlockConditional particleForward particleReverse)
      (gaussianSoftAbsMultinomialTransition (ι := Unit) ε L)).Invariant
      target := by
  apply Mcmc.Kernel.ComposableInference.pgHmc_of_auxiliaryFactorization_invariant
    target particleForward particleReverse
    (gaussianSoftAbsMultinomialTransition (ι := Unit) ε L)
  · exact auxiliary_factorization
  · apply Mcmc.Kernel.invariant_finiteNormalize
      (gaussianSoftAbsMultinomialTransition (ι := Unit) ε L)
      (gaussianSoftAbsPositionTarget (ι := Unit))
      gaussianSoftAbsPositionTarget_ne_zero
    exact gaussianSoftAbs_multinomialGRHMC_invariant ε L

end Mcmc.Examples.GeneralStatePgHmc
