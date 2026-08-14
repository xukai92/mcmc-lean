import McmcLean.Relativistic.SoftAbs
import McmcLean.Relativistic.Multinomial

/-!
# GR-HMC kernels for diagonal SoftAbs metrics

This module connects the concrete diagonal SoftAbs metric to the general
endpoint-Metropolis and multinomial GR-HMC invariance theorems.
-/

namespace McmcLean.Relativistic

open MeasureTheory
open McmcLean.Hamiltonian

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- The diagonal SoftAbs metric has a measurable conditional momentum family
when its supplied Hessian diagonal is coordinatewise measurable. -/
theorem diagonalSoftAbs_isMeasurableRiemannianMomentumFamily
    (α : ℝ) (hα : 0 < α) (hessianDiagonal : Position ι → ι → ℝ)
    (m c : ℝ) (hm : 0 < m) (hc : 0 < c)
    (hhd : ∀ i, Measurable fun q => hessianDiagonal q i) :
    IsMeasurableRiemannianMomentumFamily
      (diagonalSoftAbsMetric α hα hessianDiagonal) m c hm hc :=
  isMeasurableRiemannianMomentumFamily_of_factorVolume
    (diagonalSoftAbsMetric α hα hessianDiagonal)
    (diagonalSoftAbsMetric_hasCompatibleFactorVolume α hα hessianDiagonal)
    m c hm hc
    (measurable_riemannianRelativisticMomentumWeight measurable_const
      (diagonalSoftAbsMetric α hα hessianDiagonal) m c
      (measurable_diagonalSoftAbs_generalRelativisticHamiltonian
        (potential := fun _ => 0) measurable_const α hα hessianDiagonal hhd m c))

/-- End-to-end position invariance for endpoint-Metropolis GR-HMC with the
diagonal SoftAbs metric. The remaining numerical premise is precisely the
generalized-leapfrog validity certificate. -/
theorem diagonalSoftAbs_positionEndpointMetropolisGRHMC_invariant
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    {potential : Position ι → ℝ} (hpotential : Measurable potential)
    (α : ℝ) (hα : 0 < α) (hessianDiagonal : Position ι → ι → ℝ)
    (hhd : ∀ i, Measurable fun q => hessianDiagonal q i)
    (m c : ℝ) (hm : 0 < m) (hc : 0 < c)
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid) (ε : ℝ) :
    (positionEndpointMetropolisGRHMC potential
      (diagonalSoftAbsMetric α hα hessianDiagonal) m c hm hc selection hvalid
      (diagonalSoftAbs_isMeasurableRiemannianMomentumFamily
        α hα hessianDiagonal m c hm hc hhd) ε).Invariant
        (generalRelativisticPositionTarget potential m c hm hc) := by
  letI : SFinite (generalRelativisticPositionTarget potential m c hm hc) := by
    unfold generalRelativisticPositionTarget positionBoltzmannTarget
    infer_instance
  exact positionEndpointMetropolisGRHMC_invariant potential
    (diagonalSoftAbsMetric α hα hessianDiagonal) m c hm hc selection hvalid
    (measurable_diagonalSoftAbs_generalRelativisticHamiltonian
      potential hpotential α hα hessianDiagonal hhd m c)
    (diagonalSoftAbs_isMeasurableRiemannianMomentumFamily
      α hα hessianDiagonal m c hm hc hhd) ε
    (generalRelativisticPositionTarget potential m c hm hc)
    (isCompatibleGRPositionTarget_of_factorVolume hpotential
      (diagonalSoftAbsMetric α hα hessianDiagonal)
      (diagonalSoftAbsMetric_hasCompatibleFactorVolume α hα hessianDiagonal)
      m c hm hc
      (measurable_diagonalSoftAbs_generalRelativisticHamiltonian
        potential hpotential α hα hessianDiagonal hhd m c)
      (diagonalSoftAbs_isMeasurableRiemannianMomentumFamily
        α hα hessianDiagonal m c hm hc hhd))

/-- End-to-end position invariance for multinomial GR-HMC with the diagonal
SoftAbs metric. -/
theorem diagonalSoftAbs_positionMultinomialGRHMC_invariant
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    {potential : Position ι → ℝ} (hpotential : Measurable potential)
    (α : ℝ) (hα : 0 < α) (hessianDiagonal : Position ι → ι → ℝ)
    (hhd : ∀ i, Measurable fun q => hessianDiagonal q i)
    (m c : ℝ) (hm : 0 < m) (hc : 0 < c)
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid) (ε : ℝ) (L : ℕ) :
    (positionMultinomialGRHMC potential
      (diagonalSoftAbsMetric α hα hessianDiagonal) m c hm hc selection hvalid
      (measurable_diagonalSoftAbs_generalRelativisticHamiltonian
        potential hpotential α hα hessianDiagonal hhd m c)
      (diagonalSoftAbs_isMeasurableRiemannianMomentumFamily
        α hα hessianDiagonal m c hm hc hhd) ε L).Invariant
        (generalRelativisticPositionTarget potential m c hm hc) := by
  letI : SFinite (generalRelativisticPositionTarget potential m c hm hc) := by
    unfold generalRelativisticPositionTarget positionBoltzmannTarget
    infer_instance
  exact positionMultinomialGRHMC_invariant potential
    (diagonalSoftAbsMetric α hα hessianDiagonal) m c hm hc selection hvalid
    (measurable_diagonalSoftAbs_generalRelativisticHamiltonian
      potential hpotential α hα hessianDiagonal hhd m c)
    (diagonalSoftAbs_isMeasurableRiemannianMomentumFamily
      α hα hessianDiagonal m c hm hc hhd) ε L
    (generalRelativisticPositionTarget potential m c hm hc)
    (isCompatibleGRPositionTarget_of_factorVolume hpotential
      (diagonalSoftAbsMetric α hα hessianDiagonal)
      (diagonalSoftAbsMetric_hasCompatibleFactorVolume α hα hessianDiagonal)
      m c hm hc
      (measurable_diagonalSoftAbs_generalRelativisticHamiltonian
        potential hpotential α hα hessianDiagonal hhd m c)
      (diagonalSoftAbs_isMeasurableRiemannianMomentumFamily
        α hα hessianDiagonal m c hm hc hhd))

end McmcLean.Relativistic
