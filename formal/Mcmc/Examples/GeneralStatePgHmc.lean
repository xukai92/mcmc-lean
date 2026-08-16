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

/-- Explicit target-refresh augmentation of the mixed PG--GR-HMC schedule.
The weight `p` is assigned to the original composed transition. -/
noncomputable def pgGrhmcRefreshAugmented
    (p : Set.Icc (0 : NNReal) 1) (ε : ℝ) (L : ℕ) :
    Kernel ContinuousState ContinuousState :=
  Mcmc.Kernel.refreshAugmented p
    (Mcmc.Kernel.ComposableInference.pgHmcKernel
      (Mcmc.Kernel.twoBlockConditional particleForward particleReverse)
      (gaussianSoftAbsMultinomialTransition (ι := Unit) ε L)) target

instance pgGrhmcRefreshAugmented.instIsMarkovKernel
    (p : Set.Icc (0 : NNReal) 1) (ε : ℝ) (L : ℕ) :
    IsMarkovKernel (pgGrhmcRefreshAugmented p ε L) := by
  unfold pgGrhmcRefreshAugmented
  infer_instance

/-- The visibly refresh-augmented mixed sampler preserves the same normalized
continuous target. -/
theorem pgGrhmcRefreshAugmented_invariant
    (p : Set.Icc (0 : NNReal) 1) (ε : ℝ) (L : ℕ) :
    (pgGrhmcRefreshAugmented p ε L).Invariant target := by
  exact Mcmc.Kernel.refreshAugmented_invariant p _ target
    (pg_grhmc_invariant ε L)

/-- With both the composed and exact-refresh branches active, the concrete
mixed PG--GR-HMC chain converges setwise from every initial probability law.
No convergence claim is made here for the unaugmented composition. -/
theorem pgGrhmcRefreshAugmented_lawAtTime_apply_tendsto
    (p : Set.Icc (0 : NNReal) 1) (hp0 : 0 < p.1) (hp1 : p.1 < 1)
    (ε : ℝ) (L : ℕ) (initial : Measure ContinuousState)
    [IsProbabilityMeasure initial] {s : Set ContinuousState}
    (hs : MeasurableSet s) :
    Filter.Tendsto
      (fun n => Mcmc.Kernel.lawAtTime initial
        (pgGrhmcRefreshAugmented p ε L) n s)
      Filter.atTop (nhds (target s)) := by
  exact Mcmc.Kernel.refreshAugmented_lawAtTime_apply_tendsto
    p hp0 hp1 _ target initial (pg_grhmc_invariant ε L) hs

namespace QuadrantClient

abbrev Index := Fin 2
abbrev State := Position Index
abbrev Quadrant := Bool × Bool

/-- Normalized two-dimensional Gaussian target. -/
noncomputable def target : Measure State :=
  Mcmc.Kernel.finiteNormalize
    (gaussianSoftAbsPositionTarget (ι := Index))

instance target.instIsProbabilityMeasure : IsProbabilityMeasure target := by
  unfold target
  infer_instance

/-- Four-region discrete auxiliary determined by both coordinates. -/
noncomputable def quadrant (q : State) : Quadrant :=
  (if q (0 : Index) < 0 then false else true,
    if q (1 : Index) < 0 then false else true)

theorem measurable_quadrant : Measurable quadrant := by
  unfold quadrant
  apply Measurable.prodMk
  · exact measurable_const.piecewise
      (measurableSet_lt (measurable_pi_apply (0 : Index)) measurable_const)
      measurable_const
  · exact measurable_const.piecewise
      (measurableSet_lt (measurable_pi_apply (1 : Index)) measurable_const)
      measurable_const

theorem quadrant_uses_both_coordinates :
    quadrant (fun _ => -1) = (false, false) ∧
      quadrant (fun _ => 1) = (true, true) := by
  norm_num [quadrant]

noncomputable def particleForward : Kernel State Quadrant :=
  Kernel.deterministic quadrant measurable_quadrant

instance particleForward.instIsMarkovKernel : IsMarkovKernel particleForward := by
  unfold particleForward
  infer_instance

/-- Exact Gaussian-quadrant reverse conditional obtained by disintegration. -/
noncomputable def particleReverse : Kernel Quadrant State :=
  Mcmc.Kernel.disintegratedAuxiliaryReverse target particleForward

instance particleReverse.instIsMarkovKernel : IsMarkovKernel particleReverse := by
  unfold particleReverse
  infer_instance

theorem auxiliary_factorization :
    Mcmc.Kernel.auxiliaryFirstJoint target particleForward =
      (particleForward ∘ₘ target) ⊗ₘ particleReverse := by
  simpa [particleReverse] using
    Mcmc.Kernel.auxiliaryFirstJoint_eq_compProd_disintegratedAuxiliaryReverse
      target particleForward

/-- Multivariate mixed discrete/continuous PG--GR-HMC stationarity theorem. -/
theorem pg_grhmc_invariant (ε : ℝ) (L : ℕ) :
    (Mcmc.Kernel.ComposableInference.pgHmcKernel
      (Mcmc.Kernel.twoBlockConditional particleForward particleReverse)
      (gaussianSoftAbsMultinomialTransition (ι := Index) ε L)).Invariant
      target := by
  apply Mcmc.Kernel.ComposableInference.pgHmc_of_auxiliaryFactorization_invariant
    target particleForward particleReverse
    (gaussianSoftAbsMultinomialTransition (ι := Index) ε L)
  · exact auxiliary_factorization
  · apply Mcmc.Kernel.invariant_finiteNormalize
      (gaussianSoftAbsMultinomialTransition (ι := Index) ε L)
      (gaussianSoftAbsPositionTarget (ι := Index))
      gaussianSoftAbsPositionTarget_ne_zero
    exact gaussianSoftAbs_multinomialGRHMC_invariant ε L

end QuadrantClient

end Mcmc.Examples.GeneralStatePgHmc
