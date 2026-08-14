import McmcLean.Relativistic.Multinomial
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Position-dependent scalar metrics

This module gives a genuinely position-dependent family of factored metrics
whose Jacobian compatibility can be proved directly.  It is a reusable
nonconstant test case for the GR-HMC measure layer.
-/

namespace McmcLean.Relativistic

open MeasureTheory
open McmcLean.Hamiltonian

variable {ι : Type*} [Fintype ι]

/-- Lebesgue scaling contributed by the inverse of multiplication by
`scale(q)`. -/
noncomputable def scalarFactorJacobian
    (scale : Position ι → ℝ) (q : Position ι) : ℝ :=
  |((scale q)⁻¹) ^ Module.finrank ℝ (Momentum ι)|⁻¹

omit [Fintype ι] in
theorem scalarFactorJacobian_pos
    (scale : Position ι → ℝ) (hscale : ∀ q, 0 < scale q)
    (q : Position ι) : 0 < scalarFactorJacobian scale q := by
  unfold scalarFactorJacobian
  apply inv_pos.mpr
  exact abs_pos.mpr (pow_ne_zero _ (inv_ne_zero (hscale q).ne'))

/-- A scalar factored metric.  Its factor is `scale(q) I`, its inverse metric
is `scale(q)² I`, and its log determinant is defined from the exact inverse-map
Lebesgue scaling. -/
noncomputable def scalarFactoredRiemannianMetric
    (scale : Position ι → ℝ) (hscale : ∀ q, 0 < scale q) :
    FactoredRiemannianMetric ι where
  factor q := ContinuousLinearEquiv.smulLeft
    (Units.mk0 (scale q) (hscale q).ne')
  inverseMetric q := (scale q) ^ 2 • LinearMap.id
  logDet q := -2 * Real.log (scalarFactorJacobian scale q)

@[simp]
theorem scalarFactoredRiemannianMetric_factor_apply
    (scale : Position ι → ℝ) (hscale : ∀ q, 0 < scale q)
    (q : Position ι) (p : Momentum ι) :
    (scalarFactoredRiemannianMetric scale hscale).factor q p =
      scale q • p := by
  rfl

@[simp]
theorem scalarFactoredRiemannianMetric_inverseMetric_apply
    (scale : Position ι → ℝ) (hscale : ∀ q, 0 < scale q)
    (q : Position ι) (p : Momentum ι) :
    (scalarFactoredRiemannianMetric scale hscale).inverseMetric q p =
      (scale q) ^ 2 • p := by
  simp [scalarFactoredRiemannianMetric]

/-- The scalar metric satisfies the exact factor-volume compatibility
condition, including when `scale` varies with position. -/
theorem scalarFactoredRiemannianMetric_hasCompatibleFactorVolume
    (scale : Position ι → ℝ) (hscale : ∀ q, 0 < scale q) :
    (scalarFactoredRiemannianMetric scale hscale).HasCompatibleFactorVolume := by
  intro q
  let r : ℝ := (scale q)⁻¹
  have hr : r ≠ 0 := inv_ne_zero (hscale q).ne'
  have hmap := Measure.map_addHaar_smul
    (volume : Measure (Momentum ι)) hr
  have hjac : 0 < scalarFactorJacobian scale q :=
    scalarFactorJacobian_pos scale hscale q
  have hexp : Real.exp
      (-(1 / 2 : ℝ) *
        (scalarFactoredRiemannianMetric scale hscale).logDet q) =
      scalarFactorJacobian scale q := by
    rw [scalarFactoredRiemannianMetric]
    rw [show -(1 / 2 : ℝ) * (-2 * Real.log
        (scalarFactorJacobian scale q)) =
        Real.log (scalarFactorJacobian scale q) by ring,
      Real.exp_log hjac]
  rw [hexp]
  change Measure.map (fun p : Momentum ι => r • p) volume = _
  simpa [r, scalarFactorJacobian] using hmap

/-- A measurable positive scalar field and measurable potential give a
measurable complete GR Hamiltonian for the scalar-factor metric. -/
theorem measurable_scalar_generalRelativisticHamiltonian
    {potential scale : Position ι → ℝ}
    (hpotential : Measurable potential) (hmeasurableScale : Measurable scale)
    (hscale : ∀ q, 0 < scale q) (m c : ℝ) :
    Measurable (generalRelativisticHamiltonian potential
      (scalarFactoredRiemannianMetric scale hscale) m c) := by
  have hfactor : Measurable fun z : PhaseSpace ι => scale z.1 • z.2 :=
    (hmeasurableScale.comp measurable_fst).smul measurable_snd
  have hkin : Measurable fun z : PhaseSpace ι =>
      relativisticKineticEnergy m c (scale z.1 • z.2) :=
    (continuous_relativisticKineticEnergy m c).measurable.comp hfactor
  have hjac : Measurable (scalarFactorJacobian scale) := by
    unfold scalarFactorJacobian
    fun_prop
  have hlogdet : Measurable fun q =>
      -2 * Real.log (scalarFactorJacobian scale q) :=
    measurable_const.mul (Real.measurable_log.comp hjac)
  rw [show generalRelativisticHamiltonian potential
      (scalarFactoredRiemannianMetric scale hscale) m c =
      fun z : PhaseSpace ι => potential z.1 +
        (relativisticKineticEnergy m c (scale z.1 • z.2) +
          (1 / 2 : ℝ) * (-2 * Real.log (scalarFactorJacobian scale z.1))) by
    funext z
    simp [generalRelativisticHamiltonian, riemannianRelativisticKineticEnergy,
      scalarFactoredRiemannianMetric]]
  exact (hpotential.comp measurable_fst).add
    (hkin.add (measurable_const.mul (hlogdet.comp measurable_fst)))

section PositionKernels

variable [Nonempty ι] [DecidableEq ι]

/-- The scalar-factor metric has a measurable conditional momentum family
whenever its complete kinetic density is jointly measurable. -/
theorem scalar_isMeasurableRiemannianMomentumFamily
    (scale : Position ι → ℝ) (hscale : ∀ q, 0 < scale q)
    (m c : ℝ) (hm : 0 < m) (hc : 0 < c)
    (hweight : Measurable (Function.uncurry
      (riemannianRelativisticMomentumWeight
        (scalarFactoredRiemannianMetric scale hscale) m c))) :
    IsMeasurableRiemannianMomentumFamily
      (scalarFactoredRiemannianMetric scale hscale) m c hm hc :=
  isMeasurableRiemannianMomentumFamily_of_factorVolume
    (scalarFactoredRiemannianMetric scale hscale)
    (scalarFactoredRiemannianMetric_hasCompatibleFactorVolume scale hscale)
    m c hm hc hweight

/-- End-to-end position invariance for endpoint-Metropolis GR-HMC with a
genuinely position-dependent scalar factor. The remaining numerical premise
is exactly the generalized-leapfrog validity certificate. -/
theorem scalar_positionEndpointMetropolisGRHMC_invariant
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    {potential : Position ι → ℝ} (hpotential : Measurable potential)
    (scale : Position ι → ℝ) (hmeasurableScale : Measurable scale)
    (hscale : ∀ q, 0 < scale q)
    (m c : ℝ) (hm : 0 < m) (hc : 0 < c)
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid) (ε : ℝ) :
    let hfamily := scalar_isMeasurableRiemannianMomentumFamily scale hscale
      m c hm hc
      (measurable_riemannianRelativisticMomentumWeight hpotential
        (scalarFactoredRiemannianMetric scale hscale) m c
        (measurable_scalar_generalRelativisticHamiltonian hpotential
          hmeasurableScale hscale m c))
    (positionEndpointMetropolisGRHMC potential
      (scalarFactoredRiemannianMetric scale hscale) m c hm hc selection hvalid
      hfamily ε).Invariant
        (generalRelativisticPositionTarget potential m c hm hc) := by
  let hweight := measurable_riemannianRelativisticMomentumWeight hpotential
    (scalarFactoredRiemannianMetric scale hscale) m c
    (measurable_scalar_generalRelativisticHamiltonian hpotential
      hmeasurableScale hscale m c)
  let hfamily := scalar_isMeasurableRiemannianMomentumFamily scale hscale
    m c hm hc hweight
  letI : SFinite (generalRelativisticPositionTarget potential m c hm hc) := by
    unfold generalRelativisticPositionTarget positionBoltzmannTarget
    infer_instance
  exact positionEndpointMetropolisGRHMC_invariant potential
    (scalarFactoredRiemannianMetric scale hscale) m c hm hc selection hvalid
    (measurable_scalar_generalRelativisticHamiltonian hpotential
      hmeasurableScale hscale m c)
    hfamily ε (generalRelativisticPositionTarget potential m c hm hc)
    (isCompatibleGRPositionTarget_of_factorVolume hpotential
      (scalarFactoredRiemannianMetric scale hscale)
      (scalarFactoredRiemannianMetric_hasCompatibleFactorVolume scale hscale)
      m c hm hc
      (measurable_scalar_generalRelativisticHamiltonian hpotential
        hmeasurableScale hscale m c) hfamily)

/-- End-to-end position invariance for multinomial GR-HMC with a
position-dependent scalar factor. -/
theorem scalar_positionMultinomialGRHMC_invariant
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    {potential : Position ι → ℝ} (hpotential : Measurable potential)
    (scale : Position ι → ℝ) (hmeasurableScale : Measurable scale)
    (hscale : ∀ q, 0 < scale q)
    (m c : ℝ) (hm : 0 < m) (hc : 0 < c)
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid) (ε : ℝ) (L : ℕ) :
    let hfamily := scalar_isMeasurableRiemannianMomentumFamily scale hscale
      m c hm hc
      (measurable_riemannianRelativisticMomentumWeight hpotential
        (scalarFactoredRiemannianMetric scale hscale) m c
        (measurable_scalar_generalRelativisticHamiltonian hpotential
          hmeasurableScale hscale m c))
    (positionMultinomialGRHMC potential
      (scalarFactoredRiemannianMetric scale hscale) m c hm hc selection hvalid
      (measurable_scalar_generalRelativisticHamiltonian hpotential
        hmeasurableScale hscale m c) hfamily ε L).Invariant
        (generalRelativisticPositionTarget potential m c hm hc) := by
  let hweight := measurable_riemannianRelativisticMomentumWeight hpotential
    (scalarFactoredRiemannianMetric scale hscale) m c
    (measurable_scalar_generalRelativisticHamiltonian hpotential
      hmeasurableScale hscale m c)
  let hfamily := scalar_isMeasurableRiemannianMomentumFamily scale hscale
    m c hm hc hweight
  letI : SFinite (generalRelativisticPositionTarget potential m c hm hc) := by
    unfold generalRelativisticPositionTarget positionBoltzmannTarget
    infer_instance
  exact positionMultinomialGRHMC_invariant potential
    (scalarFactoredRiemannianMetric scale hscale) m c hm hc selection hvalid
    (measurable_scalar_generalRelativisticHamiltonian hpotential
      hmeasurableScale hscale m c)
    hfamily ε L (generalRelativisticPositionTarget potential m c hm hc)
    (isCompatibleGRPositionTarget_of_factorVolume hpotential
      (scalarFactoredRiemannianMetric scale hscale)
      (scalarFactoredRiemannianMetric_hasCompatibleFactorVolume scale hscale)
      m c hm hc
      (measurable_scalar_generalRelativisticHamiltonian hpotential
        hmeasurableScale hscale m c) hfamily)

end PositionKernels

end McmcLean.Relativistic
