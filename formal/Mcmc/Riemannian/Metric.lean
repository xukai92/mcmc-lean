import Mcmc.Hamiltonian.VolumePreservation

/-!
# Factored Riemannian metrics for Hamiltonian Monte Carlo

This neutral metric contract is shared by classical Gaussian-momentum RMHMC
and later alternative momentum laws.  It intentionally contains no
relativistic definitions.
-/

namespace Mcmc.Riemannian

open MeasureTheory Mcmc.Hamiltonian

variable {ι : Type*} [Fintype ι]

/-- Position-dependent factored metric data. In matrix notation the intended
relationship is `factor(q)ᵀ factor(q) = inverseMetric(q) = G(q)⁻¹`, while
`logDet(q) = log det G(q)`. -/
structure FactoredMetric (ι : Type*) [Fintype ι] where
  factor : Position ι → Momentum ι ≃L[ℝ] Momentum ι
  inverseMetric : Position ι → Momentum ι →ₗ[ℝ] Momentum ι
  logDet : Position ι → ℝ

/-- Exact Jacobian compatibility required of the factor convention. -/
def FactoredMetric.HasCompatibleFactorVolume
    (metric : FactoredMetric ι) : Prop :=
  ∀ q, Measure.map (metric.factor q).symm
      (volume : Measure (Momentum ι)) =
    ENNReal.ofReal (Real.exp (-(1 / 2 : ℝ) * metric.logDet q)) •
      (volume : Measure (Momentum ι))

/-- Factored identity metric: `A=I`, `G⁻¹=I`, and `log det G=0`. -/
noncomputable def identityFactoredMetric : FactoredMetric ι where
  factor _ := ContinuousLinearEquiv.refl ℝ (Momentum ι)
  inverseMetric _ := LinearMap.id
  logDet _ := 0

@[simp] theorem identityFactoredMetric_factor_apply
    (q : Position ι) (p : Momentum ι) :
    identityFactoredMetric.factor q p = p := rfl

@[simp] theorem identityFactoredMetric_inverseMetric_apply
    (q : Position ι) (p : Momentum ι) :
    identityFactoredMetric.inverseMetric q p = p := rfl

@[simp] theorem identityFactoredMetric_logDet (q : Position ι) :
    identityFactoredMetric.logDet q = 0 := rfl

theorem identityFactoredMetric_hasCompatibleFactorVolume :
    (identityFactoredMetric (ι := ι)).HasCompatibleFactorVolume := by
  intro q
  simp [identityFactoredMetric]

end Mcmc.Riemannian
