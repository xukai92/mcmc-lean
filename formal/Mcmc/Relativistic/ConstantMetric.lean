import Mcmc.Relativistic.GeneralizedLeapfrog

/-!
# Constant identity-metric specialization

The identity metric is the first concrete specialization of the GR-HMC
interfaces.  It reduces the position-dependent construction exactly to
special-relativistic HMC, and its conditional momentum family is constant and
therefore measurable.
-/

namespace Mcmc.Relativistic

open Mcmc.Hamiltonian
open MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- Factored identity metric: `A=I`, `G⁻¹=I`, and `log det G=0`. -/
noncomputable def identityFactoredRiemannianMetric :
    FactoredRiemannianMetric ι where
  factor _ := ContinuousLinearEquiv.refl ℝ (Momentum ι)
  inverseMetric _ := LinearMap.id
  logDet _ := 0

@[simp]
theorem identityFactoredRiemannianMetric_factor_apply
    (q : Position ι) (p : Momentum ι) :
    identityFactoredRiemannianMetric.factor q p = p := rfl

@[simp]
theorem identityFactoredRiemannianMetric_inverseMetric_apply
    (q : Position ι) (p : Momentum ι) :
    identityFactoredRiemannianMetric.inverseMetric q p = p := rfl

@[simp]
theorem identityFactoredRiemannianMetric_logDet
    (q : Position ι) :
    identityFactoredRiemannianMetric.logDet q = 0 := rfl

/-- The identity factor satisfies the exact Lebesgue-Jacobian compatibility
condition. -/
theorem identity_hasCompatibleFactorVolume :
    (identityFactoredRiemannianMetric (ι := ι)).HasCompatibleFactorVolume := by
  intro q
  simp [identityFactoredRiemannianMetric]

/-- Identity-metric GR kinetic energy is exactly the special-relativistic
kinetic energy. -/
@[simp]
theorem identity_riemannianRelativisticKineticEnergy
    (m c : ℝ) (q : Position ι) (p : Momentum ι) :
    riemannianRelativisticKineticEnergy
        identityFactoredRiemannianMetric m c q p =
      relativisticKineticEnergy m c p := by
  simp [riemannianRelativisticKineticEnergy]

/-- Identity-metric GR velocity is exactly the special-relativistic velocity. -/
@[simp]
theorem identity_riemannianRelativisticVelocity
    (m c : ℝ) (q : Position ι) (p : Momentum ι) :
    riemannianRelativisticVelocity
        identityFactoredRiemannianMetric m c q p =
      relativisticVelocity m c p := by
  rfl

section MomentumProbability

variable [Nonempty ι]

/-- The identity-metric conditional momentum probability is the normalized
isotropic relativistic law. -/
theorem identity_riemannianRelativisticMomentumProbability
    [DecidableEq ι]
    (m c : ℝ) (hm : 0 < m) (hc : 0 < c) (q : Position ι) :
      riemannianRelativisticMomentumProbability
        identityFactoredRiemannianMetric m c hm hc q =
      euclideanRelativisticMomentumProbability ι m c hm hc := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [riemannianRelativisticMomentumProbability,
    ProbabilityMeasure.toMeasure_map]
  exact Measure.map_id

/-- The identity-metric momentum family satisfies the kernel measurability
obligation. -/
theorem identity_isMeasurableRiemannianMomentumFamily
    [DecidableEq ι]
    (m c : ℝ) (hm : 0 < m) (hc : 0 < c) :
    IsMeasurableRiemannianMomentumFamily
      (identityFactoredRiemannianMetric (ι := ι)) m c hm hc := by
  intro s hs
  simp_rw [identity_riemannianRelativisticMomentumProbability]
  exact measurable_const

/-- Concrete identity-metric position-dependent momentum kernel.  Its rows
are all the same normalized special-relativistic law. -/
noncomputable def identityRelativisticMomentumKernel
    [DecidableEq ι]
    (m c : ℝ) (hm : 0 < m) (hc : 0 < c) :
    Kernel (Position ι) (Momentum ι) :=
  riemannianMomentumKernel identityFactoredRiemannianMetric m c hm hc
    (identity_isMeasurableRiemannianMomentumFamily m c hm hc)

instance identityRelativisticMomentumKernel_isMarkovKernel
    [DecidableEq ι]
    (m c : ℝ) (hm : 0 < m) (hc : 0 < c) :
    IsMarkovKernel
      (identityRelativisticMomentumKernel (ι := ι) m c hm hc) := by
  unfold identityRelativisticMomentumKernel
  infer_instance

end MomentumProbability

end Mcmc.Relativistic
