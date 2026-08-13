import McmcLean.Hamiltonian.Leapfrog
import McmcLean.Kernel.GaussianRandomWalk
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Invariance

/-!
# Gaussian momentum refresh

Hamiltonian Monte Carlo augments a position with an independent standard
Gaussian momentum. This module defines that momentum law in finite dimensions
and the Markov kernel which retains the position while resampling momentum.

The kernel is proved to have a Dirac position marginal, the standard Gaussian
momentum marginal, and to preserve every product of a probability position
measure with that momentum law. These facts are independent of the later
Hamiltonian trajectory transition.
-/

open MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace McmcLean.Hamiltonian

open ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- Retain the position coordinate and independently resample momentum from
`momentumTarget`.  This parameterized form separates the HMC construction
from the later choice of a Gaussian kinetic law. -/
noncomputable def momentumRefreshWith
    (momentumTarget : Measure (Momentum ι)) :
    Kernel (PhaseSpace ι) (PhaseSpace ι) :=
  Kernel.id ∥ₖ Kernel.const (Momentum ι) momentumTarget

instance momentumRefreshWith_isMarkovKernel
    (momentumTarget : Measure (Momentum ι))
    [IsProbabilityMeasure momentumTarget] :
    IsMarkovKernel (momentumRefreshWith momentumTarget) := by
  unfold momentumRefreshWith
  infer_instance

/-- Resampling from a probability momentum law preserves its product with
any s-finite position measure. -/
theorem momentumRefreshWith_invariant
    (positionTarget : Measure (Position ι)) [SFinite positionTarget]
    (momentumTarget : Measure (Momentum ι))
    [IsProbabilityMeasure momentumTarget] :
    (momentumRefreshWith momentumTarget).Invariant
      (positionTarget.prod momentumTarget) := by
  rw [Kernel.Invariant, momentumRefreshWith]
  rw [← Measure.prod_comp_right]
  rw [Measure.const_comp, measure_univ, one_smul]

/-- Independent standard Gaussian momentum coordinates. -/
noncomputable def standardMomentumMeasure : Measure (Momentum ι) :=
  McmcLean.Kernel.densityTarget volume
    (McmcLean.Kernel.isotropicGaussianPDF (ι := ι) 1)

instance standardMomentumMeasure_isProbabilityMeasure :
    IsProbabilityMeasure (standardMomentumMeasure (ι := ι)) :=
  McmcLean.Kernel.densityTarget_isProbability volume
    (McmcLean.Kernel.isotropicGaussianPDF (ι := ι) 1)
    (McmcLean.Kernel.lintegral_isotropicGaussianPDF_eq_one 1 (by norm_num))

/-- The standard finite-dimensional Gaussian momentum law has a finite first
ambient-norm moment. -/
theorem lintegral_norm_standardMomentumMeasure_ne_top :
    (∫⁻ p : Momentum ι, ENNReal.ofReal ‖p‖ ∂standardMomentumMeasure) ≠ ⊤ := by
  unfold standardMomentumMeasure McmcLean.Kernel.densityTarget
  have heq := lintegral_withDensity_eq_lintegral_mul
    (volume : Measure (Momentum ι))
    (McmcLean.Kernel.measurable_isotropicGaussianPDF 1)
    (show Measurable (fun p : Momentum ι ↦ ENNReal.ofReal ‖p‖) from
      (ENNReal.continuous_ofReal.comp continuous_norm).measurable)
  rw [heq]
  have h := McmcLean.Kernel.isotropicGaussianFirstNormMoment_ne_top
    (ι := ι) 1 (by norm_num)
  unfold McmcLean.Kernel.isotropicGaussianFirstNormMoment at h
  convert h using 1
  apply lintegral_congr
  intro p
  exact mul_comm _ _

/-- Every nonempty open momentum ball has positive standard Gaussian mass. -/
theorem standardMomentumMeasure_ball_pos (p : Momentum ι) {s : ℝ}
    (hs : 0 < s) :
    0 < standardMomentumMeasure (Metric.ball p s) := by
  rw [standardMomentumMeasure, McmcLean.Kernel.densityTarget,
    MeasureTheory.withDensity_apply _ measurableSet_ball]
  rw [MeasureTheory.setLIntegral_pos_iff
    (McmcLean.Kernel.measurable_isotropicGaussianPDF (ι := ι) 1)]
  have hsupp : Function.support
      (McmcLean.Kernel.isotropicGaussianPDF (ι := ι) 1) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact (McmcLean.Kernel.isotropicGaussianPDF_pos 1 (by norm_num) x).ne'
  rw [hsupp, Set.univ_inter]
  exact Metric.measure_ball_pos volume p hs

/-- Kinetic energy is one half the squared coordinate Euclidean norm. -/
theorem kineticEnergy_eq_half_euclideanNorm_sq (p : Momentum ι) :
    kineticEnergy p = (1 / 2 : ℝ) * euclideanNorm p ^ 2 := by
  rw [euclideanNorm_sq]
  unfold kineticEnergy squaredEuclideanNorm euclideanInner
  simp only [pow_two]

/-- A positive kinetic-energy cutoff has strictly positive standard Gaussian
momentum probability. -/
theorem standardMomentumMeasure_kineticEnergy_le_pos {k0 : ℝ}
    (hk0 : 0 < k0) :
    0 < standardMomentumMeasure {p : Momentum ι | kineticEnergy p ≤ k0} := by
  let s := Real.sqrt (2 * k0) / ((Fintype.card ι : ℝ) + 1)
  have hs : 0 < s := div_pos
    (Real.sqrt_pos.2 (mul_pos (by norm_num) hk0)) (by positivity)
  apply (standardMomentumMeasure_ball_pos (0 : Momentum ι) hs).trans_le
  apply measure_mono
  intro p hp
  have hdist : dist p 0 < s := by
    simpa [dist_comm] using (Metric.mem_ball.mp hp)
  have hnorm := euclideanNorm_sub_le_card_succ_mul_dist p 0
  have hnorm' : euclideanNorm p < Real.sqrt (2 * k0) := by
    apply lt_of_le_of_lt (by simpa using hnorm)
    dsimp [s] at hdist
    have hcard : 0 < (Fintype.card ι : ℝ) + 1 := by positivity
    apply (lt_div_iff₀ hcard).mp at hdist
    simpa only [dist_zero_right, mul_comm] using hdist
  have hsq : euclideanNorm p ^ 2 < 2 * k0 := by
    have hsqrt0 : 0 ≤ Real.sqrt (2 * k0) := Real.sqrt_nonneg _
    have := (sq_lt_sq₀ (euclideanNorm_nonneg p) hsqrt0).2 hnorm'
    rwa [Real.sq_sqrt (mul_nonneg (by norm_num) hk0.le)] at this
  change kineticEnergy p ≤ k0
  rw [kineticEnergy_eq_half_euclideanNorm_sq]
  nlinarith

/-- The extended target formed from a position law and independent standard
Gaussian momentum. -/
noncomputable def extendedTargetMeasure (positionTarget : Measure (Position ι)) :
    Measure (PhaseSpace ι) :=
  positionTarget.prod standardMomentumMeasure

instance extendedTargetMeasure_isProbabilityMeasure
    (positionTarget : Measure (Position ι))
    [IsProbabilityMeasure positionTarget] :
    IsProbabilityMeasure (extendedTargetMeasure positionTarget) := by
  unfold extendedTargetMeasure
  infer_instance

theorem extendedTargetMeasure_fst (positionTarget : Measure (Position ι)) :
    Measure.map Prod.fst (extendedTargetMeasure positionTarget) = positionTarget := by
  rw [extendedTargetMeasure, Measure.map_fst_prod, measure_univ, one_smul]

theorem extendedTargetMeasure_snd (positionTarget : Measure (Position ι))
    [IsProbabilityMeasure positionTarget] :
    Measure.map Prod.snd (extendedTargetMeasure positionTarget) =
      standardMomentumMeasure := by
  rw [extendedTargetMeasure, Measure.map_snd_prod, measure_univ, one_smul]

/-- Retain the position coordinate and independently resample standard
Gaussian momentum. -/
noncomputable def momentumRefresh :
    Kernel (PhaseSpace ι) (PhaseSpace ι) :=
  momentumRefreshWith standardMomentumMeasure

instance momentumRefresh_isMarkovKernel :
    IsMarkovKernel (momentumRefresh (ι := ι)) := by
  unfold momentumRefresh
  infer_instance

theorem momentumRefresh_apply (z : PhaseSpace ι) :
    momentumRefresh z =
      (Measure.dirac z.1).prod standardMomentumMeasure := by
  rw [momentumRefresh, momentumRefreshWith, Kernel.parallelComp_apply, Kernel.id_apply,
    Kernel.const_apply]

/-- Momentum refresh leaves the current position unchanged. -/
theorem momentumRefresh_fst (z : PhaseSpace ι) :
    Measure.map Prod.fst (momentumRefresh z) = Measure.dirac z.1 := by
  rw [momentumRefresh_apply, Measure.map_fst_prod, measure_univ, one_smul]

/-- Momentum refresh gives exactly the standard Gaussian momentum law. -/
theorem momentumRefresh_snd (z : PhaseSpace ι) :
    Measure.map Prod.snd (momentumRefresh z) = standardMomentumMeasure := by
  rw [momentumRefresh_apply, Measure.map_snd_prod]
  simp

/-- The refreshed row is the product of the retained position point mass and
the Gaussian momentum law. -/
theorem momentumRefresh_apply_prod (z : PhaseSpace ι)
    (s : Set (Position ι)) (t : Set (Momentum ι)) (hs : MeasurableSet s) :
    momentumRefresh z (s ×ˢ t) =
      s.indicator (fun _ => standardMomentumMeasure t) z.1 := by
  rw [momentumRefresh_apply, Measure.prod_prod, Measure.dirac_apply' _ hs]
  by_cases hz : z.1 ∈ s <;> simp [hz]

/-- Refreshing momentum preserves any probability position law paired with
the standard Gaussian momentum law. -/
theorem momentumRefresh_invariant (positionTarget : Measure (Position ι))
    [SFinite positionTarget] :
    (momentumRefresh (ι := ι)).Invariant
      (extendedTargetMeasure positionTarget) := by
  exact momentumRefreshWith_invariant positionTarget standardMomentumMeasure

end McmcLean.Hamiltonian
