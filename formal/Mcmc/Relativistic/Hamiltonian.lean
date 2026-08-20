import Mcmc.Relativistic.Riemannian
import Mcmc.Riemannian.Metric
import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# General-relativistic Hamiltonians

This module packages the position-dependent data used by Xu and Ge's
general-relativistic HMC Hamiltonian.  The inverse-metric factor, inverse-
metric action, and log determinant are kept as separate fields so later
calculus theorems must state their compatibility explicitly.

The first structural result is momentum-flip symmetry of the complete
nonseparable Hamiltonian.  This is a necessary ingredient of endpoint MH and
multinomial trajectory corrections, but it is not by itself a proof of kernel
invariance.
-/

namespace Mcmc.Relativistic

open Mcmc.Hamiltonian
open MeasureTheory
open ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- Backwards-compatible name for the neutral factored metric contract. -/
abbrev FactoredRiemannianMetric := Mcmc.Riemannian.FactoredMetric

/-- Relativistic kinetic term at a position, including the metric
normalization term from Xu and Ge's Equation (8). -/
noncomputable def riemannianRelativisticKineticEnergy
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (q : Position ι) (p : Momentum ι) : ℝ :=
  relativisticKineticEnergy m c (metric.factor q p) +
    (1 / 2 : ℝ) * metric.logDet q

/-- Conditional momentum density contributed by the complete Riemannian
kinetic term, including the log-determinant normalization. -/
noncomputable def riemannianRelativisticMomentumWeight
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (q : Position ι) (p : Momentum ι) : ENNReal :=
  ENNReal.ofReal (Real.exp
    (-riemannianRelativisticKineticEnergy metric m c q p))

/-- Full nonseparable GR Hamiltonian `U(q) + K(q,p)`. -/
noncomputable def generalRelativisticHamiltonian
    (potential : Position ι → ℝ)
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (z : PhaseSpace ι) : ℝ :=
  potential z.1 +
    riemannianRelativisticKineticEnergy metric m c z.1 z.2

/-- Position-dependent relativistic mass used by the momentum derivative of
the GR Hamiltonian. -/
noncomputable def riemannianRelativisticMass
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (q : Position ι) (p : Momentum ι) : ℝ :=
  generalRelativisticMass m c (metric.factor q).toLinearMap p

/-- Correct candidate for the momentum derivative of Equation (8), assuming
the factor and inverse metric satisfy their intended compatibility. -/
noncomputable def riemannianRelativisticVelocity
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
  (q : Position ι) (p : Momentum ι) : Momentum ι :=
  generalRelativisticVelocity m c (metric.factor q).toLinearMap
    (metric.inverseMetric q) p

/-- Corrected conditional momentum sampler at position `q`.  An isotropic
relativistic draw is transported by the inverse of the factor `A(q)`, because
the kinetic quadratic form is `‖A(q) p‖²`. -/
noncomputable def riemannianRelativisticMomentumMeasure
    [DecidableEq ι]
  (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (q : Position ι) : Measure (Momentum ι) :=
  (euclideanRelativisticMomentumMeasure ι m c).map
    (metric.factor q).symm

/-- Applying the factor to a draw from the corrected conditional momentum
measure recovers the isotropic relativistic measure exactly. -/
theorem map_factor_riemannianRelativisticMomentumMeasure
    [DecidableEq ι]
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (q : Position ι) :
      (riemannianRelativisticMomentumMeasure metric m c q).map
        (metric.factor q) =
      euclideanRelativisticMomentumMeasure ι m c := by
  rw [riemannianRelativisticMomentumMeasure,
    Measure.map_map (metric.factor q).continuous.measurable
      (metric.factor q).symm.continuous.measurable]
  simpa only [ContinuousLinearEquiv.self_comp_symm] using
    (Measure.map_id (μ :=
      euclideanRelativisticMomentumMeasure ι m c))

/-- Under the exact factor-Jacobian condition, inverse-factor transport of
the isotropic Euclidean law has precisely the complete Riemannian kinetic
density, including `exp(-logDet/2)`. -/
theorem riemannianRelativisticMomentumMeasure_eq_withDensity
    [DecidableEq ι]
    (metric : FactoredRiemannianMetric ι)
    (hvolume : metric.HasCompatibleFactorVolume)
    (m c : ℝ) (q : Position ι) :
    riemannianRelativisticMomentumMeasure metric m c q =
      (volume : Measure (Momentum ι)).withDensity
        (riemannianRelativisticMomentumWeight metric m c q) := by
  let f : Momentum ι → Momentum ι := (metric.factor q).symm
  let g : Momentum ι → ENNReal := fun p =>
    relativisticBoltzmannWeight m c
      (euclideanNorm (metric.factor q p))
  have hf : Measurable f := (metric.factor q).symm.continuous.measurable
  have hg : Measurable g :=
    (continuous_relativisticBoltzmannWeight m c).measurable.comp
      (continuous_euclideanNorm.comp (metric.factor q).continuous).measurable
  have hdensity :
      (fun z : Momentum ι =>
        relativisticBoltzmannWeight m c (euclideanNorm z)) = g ∘ f := by
    funext z
    simp [g, f]
  rw [riemannianRelativisticMomentumMeasure,
    euclideanRelativisticMomentumMeasure, hdensity,
    map_withDensity_comp f volume g hf hg, hvolume q,
    withDensity_smul_measure]
  rw [← withDensity_smul _ hg]
  congr 1
  funext p
  simp only [Pi.smul_apply, smul_eq_mul]
  dsimp only [g]
  unfold riemannianRelativisticMomentumWeight
    riemannianRelativisticKineticEnergy relativisticBoltzmannWeight
  rw [radialRelativisticKineticEnergy_euclideanNorm]
  rw [show -(relativisticKineticEnergy m c (metric.factor q p) +
      (1 / 2 : ℝ) * metric.logDet q) =
      (-(1 / 2 : ℝ) * metric.logDet q) +
        -relativisticKineticEnergy m c (metric.factor q p) by ring,
    Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]

section MomentumProbability

variable [Nonempty ι]

/-- Normalized position-dependent relativistic momentum law obtained by
transporting the normalized isotropic law through the inverse metric factor. -/
noncomputable def riemannianRelativisticMomentumProbability
    [DecidableEq ι]
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (hm : 0 < m) (hc : 0 < c) (q : Position ι) :
    ProbabilityMeasure (Momentum ι) :=
  (euclideanRelativisticMomentumProbability ι m c hm hc).map
    (metric.factor q).symm.continuous.measurable.aemeasurable

/-- Applying the factor to the normalized conditional law recovers the
normalized isotropic relativistic probability measure. -/
theorem map_factor_riemannianRelativisticMomentumProbability
    [DecidableEq ι]
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (hm : 0 < m) (hc : 0 < c) (q : Position ι) :
      (riemannianRelativisticMomentumProbability metric m c hm hc q).map
        (metric.factor q).continuous.measurable.aemeasurable =
      euclideanRelativisticMomentumProbability ι m c hm hc := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (metric.factor q)
      (Measure.map (metric.factor q).symm
        (euclideanRelativisticMomentumProbability ι m c hm hc : Measure _)) =
    (euclideanRelativisticMomentumProbability ι m c hm hc : Measure _)
  rw [Measure.map_map (metric.factor q).continuous.measurable
      (metric.factor q).symm.continuous.measurable]
  simpa only [ContinuousLinearEquiv.self_comp_symm] using
    (Measure.map_id (μ :=
      (euclideanRelativisticMomentumProbability ι m c hm hc :
        Measure (Momentum ι))))

/-- Every position-dependent normalized momentum row is the same inverse
partition scaling of its unnormalized inverse-factor transport. -/
theorem riemannianRelativisticMomentumProbability_toMeasure
    [DecidableEq ι]
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (hm : 0 < m) (hc : 0 < c) (q : Position ι) :
    (riemannianRelativisticMomentumProbability metric m c hm hc q :
      Measure (Momentum ι)) =
      ((euclideanRelativisticMomentumPartition ι m c hm hc)⁻¹ : NNReal) •
        riemannianRelativisticMomentumMeasure metric m c q := by
  rw [riemannianRelativisticMomentumProbability,
    ProbabilityMeasure.toMeasure_map,
    euclideanRelativisticMomentumProbability_toMeasure,
    Measure.map_smul]
  rfl

/-- Explicit kernel-measurability obligation for the position-dependent
momentum family. -/
def IsMeasurableRiemannianMomentumFamily
    [DecidableEq ι]
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (hm : 0 < m) (hc : 0 < c) : Prop :=
  ∀ s : Set (Momentum ι), MeasurableSet s →
    Measurable fun q : Position ι =>
      riemannianRelativisticMomentumProbability metric m c hm hc q s

/-- Position-dependent momentum refresh as a mathlib Markov kernel. -/
noncomputable def riemannianMomentumKernel
    [DecidableEq ι]
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (hm : 0 < m) (hc : 0 < c)
    (hmeasurable :
      IsMeasurableRiemannianMomentumFamily metric m c hm hc) :
    Kernel (Position ι) (Momentum ι) where
  toFun q := riemannianRelativisticMomentumProbability metric m c hm hc q
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simpa only [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
      (hmeasurable s hs).coe_nnreal_ennreal

instance riemannianMomentumKernel_isMarkovKernel
    [DecidableEq ι]
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (hm : 0 < m) (hc : 0 < c)
    (hmeasurable :
      IsMeasurableRiemannianMomentumFamily metric m c hm hc) :
    IsMarkovKernel
      (riemannianMomentumKernel metric m c hm hc hmeasurable) := by
  constructor
  intro q
  exact (riemannianRelativisticMomentumProbability metric m c hm hc q).property

/-- Augment a position by a draw from its position-dependent relativistic
momentum law. -/
noncomputable def riemannianPositionMomentumLift
    [DecidableEq ι]
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (hm : 0 < m) (hc : 0 < c)
    (hmeasurable :
      IsMeasurableRiemannianMomentumFamily metric m c hm hc) :
    Kernel (Position ι) (PhaseSpace ι) :=
  Kernel.id ×ₖ riemannianMomentumKernel metric m c hm hc hmeasurable

instance riemannianPositionMomentumLift_isMarkovKernel
    [DecidableEq ι]
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (hm : 0 < m) (hc : 0 < c)
    (hmeasurable :
      IsMeasurableRiemannianMomentumFamily metric m c hm hc) :
    IsMarkovKernel
      (riemannianPositionMomentumLift metric m c hm hc hmeasurable) := by
  unfold riemannianPositionMomentumLift
  infer_instance

end MomentumProbability

/-- The corrected inverse-factor transport reduces the position-dependent
quadratic kinetic term to its isotropic form. -/
theorem riemannianRelativisticKineticEnergy_factor_symm
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (q : Position ι) (z : Momentum ι) :
    riemannianRelativisticKineticEnergy metric m c q
        ((metric.factor q).symm z) =
      relativisticKineticEnergy m c z +
        (1 / 2 : ℝ) * metric.logDet q := by
  simp [riemannianRelativisticKineticEnergy]

@[simp]
theorem riemannianRelativisticKineticEnergy_neg
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (q : Position ι) (p : Momentum ι) :
    riemannianRelativisticKineticEnergy metric m c q (-p) =
      riemannianRelativisticKineticEnergy metric m c q p := by
  simp [riemannianRelativisticKineticEnergy]

@[simp]
theorem generalRelativisticHamiltonian_momentumFlip
    (potential : Position ι → ℝ)
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (z : PhaseSpace ι) :
    generalRelativisticHamiltonian potential metric m c
        (momentumFlip z) =
      generalRelativisticHamiltonian potential metric m c z := by
  simp [generalRelativisticHamiltonian, momentumFlip]

theorem riemannianRelativisticMass_pos
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (q : Position ι) (p : Momentum ι) (hm : 0 < m) (hc : 0 < c) :
    0 < riemannianRelativisticMass metric m c q p := by
  exact generalRelativisticMass_pos m c (metric.factor q).toLinearMap p hm hc

/-- Correct pointwise anisotropic speed bound for a position-dependent
factored metric. -/
theorem euclideanNorm_riemannianRelativisticVelocity_lt
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (q : Position ι) (p : Momentum ι) (hm : 0 < m) (hc : 0 < c)
    (hfactor : metric.factor q p ≠ 0)
    (hinverse : metric.inverseMetric q p ≠ 0) :
    euclideanNorm (riemannianRelativisticVelocity metric m c q p) <
      euclideanNorm (metric.inverseMetric q p) /
        (euclideanNorm (metric.factor q p) / c) := by
  exact euclideanNorm_generalRelativisticVelocity_lt m c
    (metric.factor q).toLinearMap (metric.inverseMetric q) p hm hc
      hfactor hinverse

end Mcmc.Relativistic
