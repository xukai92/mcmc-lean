import Mcmc.Executable.Continuous.GaussianSoftAbsConvergence
import Mcmc.Kernel.ComposableInference
import Mathlib.Probability.Distributions.Uniform

/-!
# A mixed discrete/continuous general-state PG--HMC client

This example instantiates the composable-inference theorem with a continuous
Gaussian SoftAbs target and a dependent Boolean auxiliary block. The Boolean
records the sign region of the current position; its reverse conditional is
the standard-Borel disintegration of the resulting joint law (equivalently, a
Gaussian restricted to the selected half-line). This exact two-block update is
followed by the proved multinomial Gaussian SoftAbs GR-HMC transition.
-/

namespace Mcmc.Examples.GeneralStatePgHmc

open MeasureTheory ProbabilityTheory
open Mcmc.Executable.Continuous Mcmc.Hamiltonian

abbrev ContinuousState := Position Unit

/-- Normalized continuous target used by both engines. -/
noncomputable def target : Measure ContinuousState :=
  Mcmc.Kernel.finiteNormalize
    (gaussianSoftAbsPositionTarget (ι := Unit))

instance target.instIsProbabilityMeasure : IsProbabilityMeasure target := by
  unfold target
  infer_instance

/-- Boolean sign region used by the dependent auxiliary block. -/
noncomputable def signRegion (q : ContinuousState) : Bool :=
  if q Unit.unit < 0 then false else true

theorem measurable_signRegion : Measurable signRegion := by
  unfold signRegion
  exact measurable_const.piecewise
    (measurableSet_lt (measurable_pi_apply Unit.unit) measurable_const)
    measurable_const

theorem signRegion_nonconstant :
    signRegion (fun _ => -1) ≠ signRegion (fun _ => 1) := by
  norm_num [signRegion]

/-- Deterministically augment the position with its sign region. -/
noncomputable def particleForward : Kernel ContinuousState Bool :=
  Kernel.deterministic signRegion measurable_signRegion

instance : IsMarkovKernel particleForward := by
  unfold particleForward
  infer_instance

/-- Exact reverse conditional supplied by standard-Borel disintegration. Its
two rows are the target restricted to the two sign regions. -/
noncomputable def particleReverse : Kernel Bool ContinuousState :=
  Mcmc.Kernel.disintegratedAuxiliaryReverse target particleForward

instance : IsMarkovKernel particleReverse := by
  unfold particleReverse
  infer_instance

/-- The dependent mixed model satisfies the exact Bayes factorization used by
the auxiliary-variable PG theorem. -/
theorem auxiliary_factorization :
    Mcmc.Kernel.auxiliaryFirstJoint target particleForward =
      (particleForward ∘ₘ target) ⊗ₘ particleReverse := by
  simpa [particleReverse] using
    Mcmc.Kernel.auxiliaryFirstJoint_eq_compProd_disintegratedAuxiliaryReverse
      target particleForward

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
