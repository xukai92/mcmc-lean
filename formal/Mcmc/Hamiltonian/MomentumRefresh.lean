import Mcmc.Hamiltonian.Leapfrog
import Mcmc.Kernel.GaussianRandomWalk
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Distributions.Gaussian.Real

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

namespace Mcmc.Hamiltonian

open ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- Retain position while applying an arbitrary transition to momentum.  This
is the phase-space lifting used by full refreshment, partial refreshment, and
other momentum updates. -/
noncomputable def momentumTransition
    (momentumKernel : Kernel (Momentum ι) (Momentum ι)) :
    Kernel (PhaseSpace ι) (PhaseSpace ι) :=
  Kernel.id ∥ₖ momentumKernel

instance momentumTransition_isMarkovKernel
    (momentumKernel : Kernel (Momentum ι) (Momentum ι))
    [IsMarkovKernel momentumKernel] :
    IsMarkovKernel (momentumTransition momentumKernel) := by
  unfold momentumTransition
  infer_instance

omit [Fintype ι] in
/-- Any invariant momentum transition lifts to an invariant transition for
the product phase target.  The momentum transition need not be an independent
resampling step or reversible. -/
theorem momentumTransition_invariant
    (positionTarget : Measure (Position ι)) [SFinite positionTarget]
    (momentumTarget : Measure (Momentum ι)) [SFinite momentumTarget]
    (momentumKernel : Kernel (Momentum ι) (Momentum ι))
    [IsMarkovKernel momentumKernel]
    (hinvariant : momentumKernel.Invariant momentumTarget) :
    (momentumTransition momentumKernel).Invariant
      (positionTarget.prod momentumTarget) := by
  rw [ProbabilityTheory.Kernel.Invariant, momentumTransition,
    ← Measure.prod_comp_right, hinvariant]

/-- Retain the position coordinate and independently resample momentum from
`momentumTarget`.  This parameterized form separates the HMC construction
from the later choice of a Gaussian kinetic law. -/
noncomputable def momentumRefreshWith
    (momentumTarget : Measure (Momentum ι)) :
    Kernel (PhaseSpace ι) (PhaseSpace ι) :=
  momentumTransition (Kernel.const (Momentum ι) momentumTarget)

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
  unfold momentumRefreshWith
  apply momentumTransition_invariant positionTarget momentumTarget
  rw [Kernel.Invariant, Measure.const_comp, measure_univ, one_smul]

/-- Independent standard Gaussian momentum coordinates. -/
noncomputable def standardMomentumMeasure : Measure (Momentum ι) :=
  Mcmc.Kernel.densityTarget volume
    (Mcmc.Kernel.isotropicGaussianPDF (ι := ι) 1)

instance standardMomentumMeasure_isProbabilityMeasure :
    IsProbabilityMeasure (standardMomentumMeasure (ι := ι)) :=
  Mcmc.Kernel.densityTarget_isProbability volume
    (Mcmc.Kernel.isotropicGaussianPDF (ι := ι) 1)
    (Mcmc.Kernel.lintegral_isotropicGaussianPDF_eq_one 1 (by norm_num))

/-- In every positive finite dimension the standard Gaussian momentum law
has no point masses. -/
instance standardMomentumMeasure.instNullSingletonClass [Nonempty ι] :
    NullSingletonClass (standardMomentumMeasure (ι := ι)) where
  measure_singleton momentum := by
    unfold standardMomentumMeasure Mcmc.Kernel.densityTarget
    rw [withDensity_apply_eq_zero
      (Mcmc.Kernel.measurable_isotropicGaussianPDF 1)]
    exact measure_mono_null Set.inter_subset_right (measure_singleton momentum)

/-- The standard Gaussian law is absolutely continuous with respect to
finite-dimensional Lebesgue volume. -/
theorem standardMomentumMeasure_absolutelyContinuous_volume :
    standardMomentumMeasure (ι := ι) ≪ volume := by
  unfold standardMomentumMeasure Mcmc.Kernel.densityTarget
  exact withDensity_absolutelyContinuous volume _

/-- Conversely, the everywhere-positive standard Gaussian density makes
Lebesgue volume absolutely continuous with respect to the Gaussian law. Thus
the two measures have exactly the same null sets. -/
theorem volume_absolutelyContinuous_standardMomentumMeasure :
    (volume : Measure (Momentum ι)) ≪ standardMomentumMeasure := by
  unfold standardMomentumMeasure Mcmc.Kernel.densityTarget
  apply withDensity_absolutelyContinuous'
    (Mcmc.Kernel.measurable_isotropicGaussianPDF (ι := ι) 1).aemeasurable
  exact Filter.Eventually.of_forall fun momentum =>
    (Mcmc.Kernel.isotropicGaussianPDF_pos 1 (by norm_num) momentum).ne'

/-- Two independent standard Gaussian draws and product Lebesgue volume have
the same null sets. -/
theorem standardMomentumMeasure_prod_absolutelyContinuous_volume_prod :
    (standardMomentumMeasure (ι := ι)).prod
        (standardMomentumMeasure (ι := ι)) ≪
      (volume : Measure (Momentum ι)).prod
        (volume : Measure (Momentum ι)) :=
  standardMomentumMeasure_absolutelyContinuous_volume.prod
    standardMomentumMeasure_absolutelyContinuous_volume

theorem volume_prod_absolutelyContinuous_standardMomentumMeasure_prod :
    (volume : Measure (Momentum ι)).prod
        (volume : Measure (Momentum ι)) ≪
      (standardMomentumMeasure (ι := ι)).prod
        (standardMomentumMeasure (ι := ι)) :=
  volume_absolutelyContinuous_standardMomentumMeasure.prod
    volume_absolutelyContinuous_standardMomentumMeasure

/-- Gaussian and Lebesgue positivity agree on every measurable or
nonmeasurable set because their completed null ideals coincide. -/
theorem standardMomentumMeasure_pos_iff_volume_pos
    (event : Set (Momentum ι)) :
    0 < standardMomentumMeasure (ι := ι) event ↔
      0 < (volume : Measure (Momentum ι)) event := by
  rw [pos_iff_ne_zero, pos_iff_ne_zero]
  exact not_congr ⟨
    fun hzero => volume_absolutelyContinuous_standardMomentumMeasure hzero,
    fun hzero => standardMomentumMeasure_absolutelyContinuous_volume hzero⟩

theorem standardMomentumMeasure_prod_pos_iff_volume_prod_pos
    (event : Set (Momentum ι × Momentum ι)) :
    0 < ((standardMomentumMeasure (ι := ι)).prod
        (standardMomentumMeasure (ι := ι))) event ↔
      0 < ((volume : Measure (Momentum ι)).prod
        (volume : Measure (Momentum ι))) event := by
  rw [pos_iff_ne_zero, pos_iff_ne_zero]
  exact not_congr ⟨
    fun hzero =>
      volume_prod_absolutelyContinuous_standardMomentumMeasure_prod hzero,
    fun hzero =>
      standardMomentumMeasure_prod_absolutelyContinuous_volume_prod hzero⟩

/-- The standard finite-dimensional Gaussian momentum law has a finite first
ambient-norm moment. -/
theorem lintegral_norm_standardMomentumMeasure_ne_top :
    (∫⁻ p : Momentum ι, ENNReal.ofReal ‖p‖ ∂standardMomentumMeasure) ≠ ⊤ := by
  unfold standardMomentumMeasure Mcmc.Kernel.densityTarget
  have heq := lintegral_withDensity_eq_lintegral_mul
    (volume : Measure (Momentum ι))
    (Mcmc.Kernel.measurable_isotropicGaussianPDF 1)
    (show Measurable (fun p : Momentum ι ↦ ENNReal.ofReal ‖p‖) from
      (ENNReal.continuous_ofReal.comp continuous_norm).measurable)
  rw [heq]
  have h := Mcmc.Kernel.isotropicGaussianFirstNormMoment_ne_top
    (ι := ι) 1 (by norm_num)
  unfold Mcmc.Kernel.isotropicGaussianFirstNormMoment at h
  convert h using 1
  apply lintegral_congr
  intro p
  exact mul_comm _ _

/-- Every coordinate marginal of the finite-dimensional standard momentum
law is the one-dimensional centered unit Gaussian. -/
theorem standardMomentumMeasure_map_coordinate (i : ι) :
    Measure.map (fun p : Momentum ι => p i) standardMomentumMeasure =
      gaussianReal 0 1 := by
  classical
  rw [standardMomentumMeasure,
    Mcmc.Kernel.densityTarget_isotropicGaussianPDF_eq_pi 1 (by norm_num),
    MeasureTheory.Measure.pi_map_eval]
  simp

/-- Each standard momentum coordinate has mean zero. -/
theorem integral_standardMomentumMeasure_coordinate (i : ι) :
    (∫ p : Momentum ι, p i ∂standardMomentumMeasure) = 0 := by
  calc
    (∫ p : Momentum ι, p i ∂standardMomentumMeasure) =
        ∫ x : ℝ, x ∂Measure.map (fun p : Momentum ι => p i)
          standardMomentumMeasure := by
      symm
      exact integral_map (measurable_pi_apply i).aemeasurable
        measurable_id.aestronglyMeasurable
    _ = ∫ x : ℝ, x ∂gaussianReal 0 1 := by
      rw [standardMomentumMeasure_map_coordinate]
    _ = 0 := integral_id_gaussianReal

/-- Each standard momentum coordinate is integrable. -/
theorem integrable_standardMomentumMeasure_coordinate (i : ι) :
    Integrable (fun p : Momentum ι => p i) standardMomentumMeasure := by
  have hmap : Integrable id
      (Measure.map (fun p : Momentum ι => p i) standardMomentumMeasure) := by
    rw [standardMomentumMeasure_map_coordinate]
    exact (memLp_id_gaussianReal (p := 1)).integrable le_rfl
  have h := (integrable_map_measure
    (f := fun p : Momentum ι => p i) (g := id)
    (show AEStronglyMeasurable id
        (Measure.map (fun p : Momentum ι => p i) standardMomentumMeasure) from
      measurable_id.aestronglyMeasurable)
    (measurable_pi_apply i).aemeasurable).mp hmap
  simpa [Function.comp_def] using h

/-- The square of each standard momentum coordinate is integrable. -/
theorem integrable_standardMomentumMeasure_coordinate_sq (i : ι) :
    Integrable (fun p : Momentum ι => (p i) ^ 2) standardMomentumMeasure := by
  have hmap : Integrable (fun x : ℝ => x ^ 2)
      (Measure.map (fun p : Momentum ι => p i) standardMomentumMeasure) := by
    rw [standardMomentumMeasure_map_coordinate]
    exact (memLp_id_gaussianReal (p := 2)).integrable_sq
  have h := (integrable_map_measure
    (f := fun p : Momentum ι => p i) (g := fun x : ℝ => x ^ 2)
    (show AEStronglyMeasurable (fun x : ℝ => x ^ 2)
        (Measure.map (fun p : Momentum ι => p i) standardMomentumMeasure) from
      (measurable_id.pow_const 2).aestronglyMeasurable)
    (measurable_pi_apply i).aemeasurable).mp hmap
  simpa [Function.comp_def] using h

/-- Each standard momentum coordinate has second moment one. -/
theorem integral_standardMomentumMeasure_coordinate_sq (i : ι) :
    (∫ p : Momentum ι, (p i) ^ 2 ∂standardMomentumMeasure) = 1 := by
  have hvariance := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  change variance id (gaussianReal 0 1) = (1 : ℝ) at hvariance
  rw [variance_eq_integral measurable_id.aemeasurable] at hvariance
  have hsecond : (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1 := by
    simpa only [integral_id_gaussianReal, id_eq, sub_zero] using hvariance
  calc
    (∫ p : Momentum ι, (p i) ^ 2 ∂standardMomentumMeasure) =
        ∫ x : ℝ, x ^ 2 ∂Measure.map (fun p : Momentum ι => p i)
          standardMomentumMeasure := by
      symm
      exact integral_map (measurable_pi_apply i).aemeasurable
        (measurable_id.pow_const 2).aestronglyMeasurable
    _ = ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1 := by
      rw [standardMomentumMeasure_map_coordinate]
    _ = 1 := hsecond

/-- Standard Gaussian momentum has exact expected squared Euclidean norm
equal to the finite coordinate dimension. -/
theorem integral_squaredEuclideanNorm_standardMomentumMeasure :
    (∫ p : Momentum ι, squaredEuclideanNorm p
      ∂standardMomentumMeasure) = Fintype.card ι := by
  unfold squaredEuclideanNorm euclideanInner
  simp_rw [← pow_two]
  rw [integral_finsetSum Finset.univ]
  · simp only [integral_standardMomentumMeasure_coordinate_sq,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  · intro i _hi
    exact integrable_standardMomentumMeasure_coordinate_sq (ι := ι) i

/-- Squared Euclidean speed is integrable under standard Gaussian momentum. -/
theorem integrable_squaredEuclideanNorm_standardMomentumMeasure :
    Integrable (squaredEuclideanNorm : Momentum ι → ℝ)
      standardMomentumMeasure := by
  unfold squaredEuclideanNorm euclideanInner
  simpa using integrable_finsetSum Finset.univ (fun i _hi => by
    simpa [pow_two] using
      integrable_standardMomentumMeasure_coordinate_sq (ι := ι) i)

/-- The inner product with any fixed vector is integrable under standard
Gaussian momentum. -/
theorem integrable_euclideanInner_standardMomentumMeasure
    (fixed : Position ι) :
    Integrable (fun p : Momentum ι => euclideanInner fixed p)
      standardMomentumMeasure := by
  unfold euclideanInner
  simpa using integrable_finsetSum Finset.univ (fun i _hi =>
    (integrable_standardMomentumMeasure_coordinate (ι := ι) i).const_mul
      (fixed i))

/-- Centered standard Gaussian momentum has zero inner product in expectation
with every fixed vector. -/
theorem integral_euclideanInner_standardMomentumMeasure
    (fixed : Position ι) :
    (∫ p : Momentum ι, euclideanInner fixed p
      ∂standardMomentumMeasure) = 0 := by
  unfold euclideanInner
  rw [integral_finsetSum Finset.univ]
  · simp [integral_const_mul,
      integral_standardMomentumMeasure_coordinate]
  · intro i _hi
    exact (integrable_standardMomentumMeasure_coordinate (ι := ι) i).const_mul
      (fixed i)

/-- Every nonempty open momentum ball has positive standard Gaussian mass. -/
theorem standardMomentumMeasure_ball_pos (p : Momentum ι) {s : ℝ}
    (hs : 0 < s) :
    0 < standardMomentumMeasure (Metric.ball p s) := by
  rw [standardMomentumMeasure, Mcmc.Kernel.densityTarget,
    MeasureTheory.withDensity_apply _ measurableSet_ball]
  rw [MeasureTheory.setLIntegral_pos_iff
    (Mcmc.Kernel.measurable_isotropicGaussianPDF (ι := ι) 1)]
  have hsupp : Function.support
      (Mcmc.Kernel.isotropicGaussianPDF (ι := ι) 1) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact (Mcmc.Kernel.isotropicGaussianPDF_pos 1 (by norm_num) x).ne'
  rw [hsupp, Set.univ_inter]
  exact Metric.measure_ball_pos volume p hs

/-- The finite-dimensional standard Gaussian gives positive mass to every
nonempty open set. -/
instance standardMomentumMeasure.instIsOpenPosMeasure :
    Measure.IsOpenPosMeasure (standardMomentumMeasure (ι := ι)) where
  open_pos U hU hUne := by
    obtain ⟨p, hp⟩ := hUne
    obtain ⟨radius, hradius, hball⟩ := Metric.isOpen_iff.mp hU p hp
    exact (standardMomentumMeasure_ball_pos p hradius).trans_le
      (measure_mono hball) |>.ne'

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
  rw [momentumRefresh, momentumRefreshWith, momentumTransition,
    Kernel.parallelComp_apply, Kernel.id_apply, Kernel.const_apply]

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

end Mcmc.Hamiltonian
