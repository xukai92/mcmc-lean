import Mcmc.Executable.Continuous.GaussianSoftAbs
import Mcmc.Kernel.RefreshAugmented

/-!
# Geometric convergence for refresh-augmented Gaussian SoftAbs GR-HMC

This module turns the exact invariance theorem for the concrete Gaussian
diagonal-SoftAbs multinomial GR-HMC transition into an eventwise geometric
convergence theorem by adding an independent draw from the normalized target.
The theorem concerns this explicitly augmented algorithm; it does not assert
a convergence rate for the unrefreshed GR-HMC transition.
-/

namespace Mcmc.Executable.Continuous

open Mcmc.Hamiltonian Mcmc.Relativistic MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- The unnormalized position target of the Gaussian SoftAbs client. -/
noncomputable abbrev gaussianSoftAbsPositionTarget : Measure (Position ι) :=
  generalRelativisticPositionTarget (gaussianSoftAbsPotential (ι := ι))
    1 1 (by norm_num) (by norm_num)

omit [DecidableEq ι] in
/-- The Gaussian SoftAbs target has positive mass. -/
theorem gaussianSoftAbsPositionTarget_ne_zero :
    gaussianSoftAbsPositionTarget (ι := ι) ≠ 0 := by
  unfold gaussianSoftAbsPositionTarget generalRelativisticPositionTarget
    positionBoltzmannTarget
  rw [← Measure.coe_nnreal_smul]
  intro hsmul
  rcases Measure.ennreal_smul_eq_zero.mp hsmul with hpartition | hzero
  · have hpartition_ne :
        ((euclideanRelativisticMomentumPartition ι 1 1
          (by norm_num) (by norm_num) : NNReal) : ENNReal) ≠ 0 := by
      exact_mod_cast euclideanRelativisticMomentumPartition_ne_zero ι 1 1
        (by norm_num) (by norm_num)
    exact hpartition_ne hpartition
  ·
    have hweight := (withDensity_eq_zero_iff
      (measurable_positionBoltzmannWeight
        (measurable_gaussianSoftAbsPotential (ι := ι))).aemeasurable).mp hzero
    haveI : (ae (volume : Measure (Position ι))).NeBot := inferInstance
    obtain ⟨q, hq⟩ := hweight.exists
    exact (positionBoltzmannWeight_pos
      (gaussianSoftAbsPotential (ι := ι)) q).ne' hq

/-- The concrete multinomial Gaussian SoftAbs GR-HMC transition. -/
noncomputable abbrev gaussianSoftAbsMultinomialTransition (ε : ℝ) (L : ℕ) :=
  positionMultinomialGRHMC (gaussianSoftAbsPotential (ι := ι))
    (gaussianSoftAbsMetric (ι := ι)) 1 1 (by norm_num) (by norm_num)
    (gaussianSoftAbsSelection (ι := ι)) gaussianSoftAbsSelection_valid
    (measurable_diagonalSoftAbs_generalRelativisticHamiltonian
      (gaussianSoftAbsPotential (ι := ι))
      (measurable_gaussianSoftAbsPotential (ι := ι))
      1 (by norm_num) (gaussianHessianDiagonal (ι := ι))
      (measurable_gaussianHessianDiagonal (ι := ι)) 1 1)
    (diagonalSoftAbs_isMeasurableRiemannianMomentumFamily
      1 (by norm_num) (gaussianHessianDiagonal (ι := ι)) 1 1
      (by norm_num) (by norm_num)
      (measurable_gaussianHessianDiagonal (ι := ι))) ε L

/-- Mix GR-HMC (weight `p`) with an exact independent normalized-target draw
(weight `1-p`). -/
noncomputable def gaussianSoftAbsRefreshAugmented
    [IsFiniteMeasure (gaussianSoftAbsPositionTarget (ι := ι))]
    (p : Set.Icc (0 : NNReal) 1) (ε : ℝ) (L : ℕ) :=
  Mcmc.Kernel.refreshAugmented p
    (gaussianSoftAbsMultinomialTransition (ι := ι) ε L)
    (Mcmc.Kernel.finiteNormalize
      (gaussianSoftAbsPositionTarget (ι := ι)))

instance gaussianSoftAbsRefreshAugmented.instIsMarkovKernel
    [IsFiniteMeasure (gaussianSoftAbsPositionTarget (ι := ι))]
    (p : Set.Icc (0 : NNReal) 1) (ε : ℝ) (L : ℕ) :
    IsMarkovKernel (gaussianSoftAbsRefreshAugmented (ι := ι) p ε L) := by
  unfold gaussianSoftAbsRefreshAugmented
  infer_instance

/-- The refresh-augmented transition preserves the normalized Gaussian
SoftAbs position target. -/
theorem gaussianSoftAbsRefreshAugmented_invariant
    [IsFiniteMeasure (gaussianSoftAbsPositionTarget (ι := ι))]
    (p : Set.Icc (0 : NNReal) 1) (ε : ℝ) (L : ℕ) :
    (gaussianSoftAbsRefreshAugmented (ι := ι) p ε L).Invariant
      (Mcmc.Kernel.finiteNormalize
        (gaussianSoftAbsPositionTarget (ι := ι))) := by
  apply Mcmc.Kernel.refreshAugmented_invariant
  apply Mcmc.Kernel.invariant_finiteNormalize _ _
    gaussianSoftAbsPositionTarget_ne_zero
  exact gaussianSoftAbs_multinomialGRHMC_invariant ε L

/-- Upper half of the eventwise geometric convergence certificate. -/
theorem gaussianSoftAbsRefreshAugmented_lawAtTime_apply_le
    [IsFiniteMeasure (gaussianSoftAbsPositionTarget (ι := ι))]
    (p : Set.Icc (0 : NNReal) 1) (hp0 : 0 < p.1)
    (ε : ℝ) (L n : ℕ) (initial : Measure (Position ι))
    [IsProbabilityMeasure initial] {s : Set (Position ι)}
    (hs : MeasurableSet s) :
    Mcmc.Kernel.lawAtTime initial
        (gaussianSoftAbsRefreshAugmented (ι := ι) p ε L) n s ≤
      Mcmc.Kernel.finiteNormalize
          (gaussianSoftAbsPositionTarget (ι := ι)) s +
        ((p.1 ^ n : NNReal) : ENNReal) := by
  apply Mcmc.Kernel.refreshAugmented_lawAtTime_apply_le
    p hp0 (gaussianSoftAbsMultinomialTransition (ι := ι) ε L)
    (Mcmc.Kernel.finiteNormalize
      (gaussianSoftAbsPositionTarget (ι := ι))) initial
  · apply Mcmc.Kernel.invariant_finiteNormalize _ _
      gaussianSoftAbsPositionTarget_ne_zero
    exact gaussianSoftAbs_multinomialGRHMC_invariant ε L
  · exact hs

/-- Lower half of the eventwise geometric convergence certificate. -/
theorem gaussianSoftAbsRefreshAugmented_target_apply_le_lawAtTime
    [IsFiniteMeasure (gaussianSoftAbsPositionTarget (ι := ι))]
    (p : Set.Icc (0 : NNReal) 1) (hp0 : 0 < p.1)
    (ε : ℝ) (L n : ℕ) (initial : Measure (Position ι))
    [IsProbabilityMeasure initial] {s : Set (Position ι)}
    (hs : MeasurableSet s) :
    Mcmc.Kernel.finiteNormalize
        (gaussianSoftAbsPositionTarget (ι := ι)) s ≤
      Mcmc.Kernel.lawAtTime initial
          (gaussianSoftAbsRefreshAugmented (ι := ι) p ε L) n s +
        ((p.1 ^ n : NNReal) : ENNReal) := by
  apply Mcmc.Kernel.refreshAugmented_target_apply_le_lawAtTime
    p hp0 (gaussianSoftAbsMultinomialTransition (ι := ι) ε L)
    (Mcmc.Kernel.finiteNormalize
      (gaussianSoftAbsPositionTarget (ι := ι))) initial
  · apply Mcmc.Kernel.invariant_finiteNormalize _ _
      gaussianSoftAbsPositionTarget_ne_zero
    exact gaussianSoftAbs_multinomialGRHMC_invariant ε L
  · exact hs

/-- When the refresh branch has positive weight (`p < 1`), the explicit
remainder in both eventwise bounds tends to zero. -/
theorem gaussianSoftAbsRefreshAugmented_rate_tendsto_zero
    (p : Set.Icc (0 : NNReal) 1) (hp : p.1 < 1) :
    Filter.Tendsto (fun n : ℕ => (((p.1 : NNReal) : ENNReal) ^ n))
      Filter.atTop (nhds 0) :=
  Mcmc.Kernel.refreshAugmented_rate_tendsto_zero p hp

end Mcmc.Executable.Continuous
