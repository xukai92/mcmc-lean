import Mcmc.Relativistic.Multinomial
import Mcmc.Relativistic.Derivatives
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Position-dependent scalar metrics

This module gives a genuinely position-dependent family of factored metrics
whose Jacobian compatibility can be proved directly.  It is a reusable
nonconstant test case for the GR-HMC measure layer.
-/

namespace Mcmc.Relativistic

open MeasureTheory
open Mcmc.Hamiltonian

variable {ι : Type*} [Fintype ι]

/-- A canonical smooth, globally positive, genuinely position-dependent
scalar factor. It supplies a concrete metric field rather than leaving the
positive scale as an abstract client parameter. -/
noncomputable def quadraticScalarScale (q : Position ι) : ℝ :=
  1 + squaredEuclideanNorm q

theorem quadraticScalarScale_pos (q : Position ι) :
    0 < quadraticScalarScale q := by
  unfold quadraticScalarScale
  exact add_pos_of_pos_of_nonneg zero_lt_one (squaredEuclideanNorm_nonneg q)

theorem measurable_quadraticScalarScale :
    Measurable (quadraticScalarScale : Position ι → ℝ) := by
  unfold quadraticScalarScale squaredEuclideanNorm euclideanInner
  fun_prop

theorem differentiable_quadraticScalarScale :
    Differentiable ℝ (quadraticScalarScale : Position ι → ℝ) := by
  unfold quadraticScalarScale squaredEuclideanNorm euclideanInner
  fun_prop

/-- Directional derivative of the canonical scale in one dimension. -/
theorem fderiv_quadraticScalarScale_unit_apply
    (q u : Position Unit) :
    fderiv ℝ (quadraticScalarScale : Position Unit → ℝ) q u =
      2 * q Unit.unit * u Unit.unit := by
  unfold quadraticScalarScale squaredEuclideanNorm euclideanInner
  rw [fderiv_const_add, fderiv_fun_sum]
  · simp only [Fintype.sum_unique]
    have happ : fderiv ℝ (fun q : Position Unit => q Unit.unit) q u =
        u Unit.unit := by
      have h := congrArg (fun L : Position Unit →L[ℝ] ℝ => L u)
        (hasFDerivAt_apply Unit.unit q).fderiv
      simpa using h
    change (fderiv ℝ (fun q : Position Unit =>
      q Unit.unit * q Unit.unit) q) u = _
    have hmul := fderiv_mul
      (by fun_prop : DifferentiableAt ℝ
        (fun q : Position Unit => q Unit.unit) q)
      (by fun_prop : DifferentiableAt ℝ
        (fun q : Position Unit => q Unit.unit) q)
    have hmulapp := congrArg
      (fun L : Position Unit →L[ℝ] ℝ => L u) hmul
    rw [show (fun q : Position Unit => q Unit.unit * q Unit.unit) =
      (fun q : Position Unit => q Unit.unit) *
        (fun q : Position Unit => q Unit.unit) by rfl, hmulapp]
    simp only [add_apply, smul_apply, smul_eq_mul, happ]
    ring
  · intro i hi
    fun_prop

/-- The canonical positive factor is not constant, already in one
dimension. -/
theorem quadraticScalarScale_nonconstant :
    quadraticScalarScale (fun _ : Unit => 0) ≠
      quadraticScalarScale (fun _ : Unit => 1) := by
  norm_num [quadraticScalarScale, squaredEuclideanNorm, euclideanInner]

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

/-- In one dimension the scalar-factor Jacobian is the positive scale itself. -/
theorem scalarFactorJacobian_unit_eq
    (scale : Position Unit → ℝ) (hscale : ∀ q, 0 < scale q)
    (q : Position Unit) : scalarFactorJacobian scale q = scale q := by
  unfold scalarFactorJacobian
  simp [abs_of_pos (hscale q)]

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

/-- Concrete globally positive nonconstant factored metric used as the target
for the remaining exact generalized-leapfrog derivative instantiation. -/
noncomputable def quadraticScalarRiemannianMetric :
    FactoredRiemannianMetric ι :=
  scalarFactoredRiemannianMetric quadraticScalarScale
    quadraticScalarScale_pos

theorem differentiableAt_quadraticScalar_factor_norm_sq_unit
    (q : Position Unit) (p : Momentum Unit) :
    DifferentiableAt ℝ (fun r => squaredEuclideanNorm
      (((quadraticScalarRiemannianMetric (ι := Unit)).factor r) p)) q := by
  rw [show (fun r => squaredEuclideanNorm
      (((quadraticScalarRiemannianMetric (ι := Unit)).factor r) p)) =
      fun r : Position Unit =>
        (quadraticScalarScale r * p Unit.unit) *
          (quadraticScalarScale r * p Unit.unit) by
    funext r
    simp [quadraticScalarRiemannianMetric,
      scalarFactoredRiemannianMetric_factor_apply,
      squaredEuclideanNorm, euclideanInner]]
  exact (differentiable_quadraticScalarScale.differentiableAt.mul_const _).mul
    (differentiable_quadraticScalarScale.differentiableAt.mul_const _)

theorem fderiv_quadraticScalar_factor_norm_sq_unit_apply
    (q : Position Unit) (p : Momentum Unit) (u : Position Unit) :
    fderiv ℝ (fun r => squaredEuclideanNorm
      (((quadraticScalarRiemannianMetric (ι := Unit)).factor r) p)) q u =
      4 * quadraticScalarScale q * q Unit.unit * u Unit.unit *
        p Unit.unit ^ 2 := by
  have hscale : DifferentiableAt ℝ
      (quadraticScalarScale : Position Unit → ℝ) q :=
    (differentiable_quadraticScalarScale (ι := Unit)).differentiableAt
  have hscaled : DifferentiableAt ℝ
      (fun r : Position Unit => quadraticScalarScale r * p Unit.unit) q :=
    hscale.mul_const _
  have hmul := fderiv_mul hscaled hscaled
  have hmulapp := congrArg
    (fun L : Position Unit →L[ℝ] ℝ => L u) hmul
  have hscaleMul := fderiv_mul_const hscale (p Unit.unit)
  have hscaleMulApp := congrArg
    (fun L : Position Unit →L[ℝ] ℝ => L u) hscaleMul
  rw [show (fun r => squaredEuclideanNorm
      (((quadraticScalarRiemannianMetric (ι := Unit)).factor r) p)) =
      fun r : Position Unit =>
        (quadraticScalarScale r * p Unit.unit) *
          (quadraticScalarScale r * p Unit.unit) by
    funext r
    simp [quadraticScalarRiemannianMetric,
      scalarFactoredRiemannianMetric_factor_apply,
      squaredEuclideanNorm, euclideanInner]]
  rw [show (fun r : Position Unit =>
      (quadraticScalarScale r * p Unit.unit) *
        (quadraticScalarScale r * p Unit.unit)) =
      (fun r => quadraticScalarScale r * p Unit.unit) *
        (fun r => quadraticScalarScale r * p Unit.unit) by rfl,
    hmulapp]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [hscaleMulApp]
  simp only [smul_apply, smul_eq_mul]
  rw [fderiv_quadraticScalarScale_unit_apply]
  ring

theorem quadraticScalarRiemannianMetric_logDet_unit (q : Position Unit) :
    (quadraticScalarRiemannianMetric (ι := Unit)).logDet q =
      -2 * Real.log (quadraticScalarScale q) := by
  simp [quadraticScalarRiemannianMetric, scalarFactoredRiemannianMetric,
    scalarFactorJacobian_unit_eq quadraticScalarScale
      quadraticScalarScale_pos]

theorem differentiableAt_quadraticScalarRiemannianMetric_logDet_unit
    (q : Position Unit) :
    DifferentiableAt ℝ
      (quadraticScalarRiemannianMetric (ι := Unit)).logDet q := by
  rw [show (quadraticScalarRiemannianMetric (ι := Unit)).logDet =
      fun r => -2 * Real.log (quadraticScalarScale r) by
    funext r
    exact quadraticScalarRiemannianMetric_logDet_unit r]
  exact ((Real.differentiableAt_log
    (quadraticScalarScale_pos q).ne').comp q
      (differentiable_quadraticScalarScale (ι := Unit)).differentiableAt).const_mul _

theorem fderiv_quadraticScalarRiemannianMetric_logDet_unit_apply
    (q u : Position Unit) :
    fderiv ℝ (quadraticScalarRiemannianMetric (ι := Unit)).logDet q u =
      -4 * q Unit.unit * u Unit.unit / quadraticScalarScale q := by
  let scale : Position Unit → ℝ := quadraticScalarScale
  have hscale : DifferentiableAt ℝ scale q :=
    (differentiable_quadraticScalarScale (ι := Unit)).differentiableAt
  have hlog : DifferentiableAt ℝ (Real.log ∘ scale) q :=
    (Real.differentiableAt_log (quadraticScalarScale_pos q).ne').comp q hscale
  rw [show (quadraticScalarRiemannianMetric (ι := Unit)).logDet =
      fun r => -2 * Real.log (scale r) by
    funext r
    exact quadraticScalarRiemannianMetric_logDet_unit r]
  have hconst := fderiv_const_mul hlog (-2 : ℝ)
  have hconstApp := congrArg
    (fun L : Position Unit →L[ℝ] ℝ => L u) hconst
  rw [show (fun r : Position Unit => -2 * Real.log (scale r)) =
      fun r => (-2 : ℝ) * (Real.log ∘ scale) r by rfl, hconstApp]
  simp only [smul_apply, smul_eq_mul]
  rw [fderiv_comp (f := scale) (g := Real.log) (x := q)
    (Real.differentiableAt_log (quadraticScalarScale_pos q).ne') hscale,
    ContinuousLinearMap.comp_apply,
    (Real.hasDerivAt_log
      (quadraticScalarScale_pos q).ne').hasFDerivAt.fderiv]
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  rw [fderiv_quadraticScalarScale_unit_apply]
  field_simp
  ring

/-- Directional derivative of the covariant metric
`G(q) = quadraticScalarScale(q)⁻² I` in one dimension. -/
noncomputable def quadraticScalarMetricVariationUnit
    (q u : Position Unit) : Momentum Unit →ₗ[ℝ] Momentum Unit :=
  (-4 * q Unit.unit * u Unit.unit / quadraticScalarScale q ^ 3) •
    ContinuousLinearMap.id ℝ (Momentum Unit)

@[simp]
theorem quadraticScalarMetricVariationUnit_apply
    (q u : Position Unit) (p : Momentum Unit) :
    quadraticScalarMetricVariationUnit q u p =
      (-4 * q Unit.unit * u Unit.unit / quadraticScalarScale q ^ 3) • p := by
  rfl

/-- Complete Equation (12) calculus certificate for the concrete positive
nonconstant scalar metric in one dimension. -/
noncomputable def quadraticScalarMetricEquation12CertificateUnit
    (q : Position Unit) :
    (quadraticScalarRiemannianMetric (ι := Unit)).Equation12Certificate q := by
  refine {
    metricVariation := quadraticScalarMetricVariationUnit q
    differentiableAt_quadratic :=
      differentiableAt_quadraticScalar_factor_norm_sq_unit q
    fderiv_quadratic := ?_
    differentiableAt_logDet :=
      differentiableAt_quadraticScalarRiemannianMetric_logDet_unit q
    fderiv_logDet := ?_ }
  · intro p u
    rw [fderiv_quadraticScalar_factor_norm_sq_unit_apply]
    unfold euclideanInner
    simp only [scalarFactoredRiemannianMetric_inverseMetric_apply,
      quadraticScalarRiemannianMetric, Finset.univ_unique,
      Finset.sum_singleton, Pi.smul_apply, smul_eq_mul,
      quadraticScalarMetricVariationUnit_apply]
    have hs : quadraticScalarScale q ≠ 0 :=
      (quadraticScalarScale_pos q).ne'
    field_simp [hs]
  · intro u
    rw [fderiv_quadraticScalarRiemannianMetric_logDet_unit_apply]
    unfold coordinateTrace
    simp only [Finset.univ_unique, Finset.sum_singleton,
      LinearMap.comp_apply,
      scalarFactoredRiemannianMetric_inverseMetric_apply,
      quadraticScalarRiemannianMetric, Pi.smul_apply, smul_eq_mul,
      quadraticScalarMetricVariationUnit_apply,
      Pi.single_eq_same]
    have hs : quadraticScalarScale q ≠ 0 :=
      (quadraticScalarScale_pos q).ne'
    field_simp [hs]

/-- The concrete scalar factor and inverse metric satisfy
`A(q)ᵀA(q) = G(q)⁻¹`. -/
theorem quadraticScalarRiemannianMetric_factor_compatible
    (q : Position Unit) (x y : Momentum Unit) :
    euclideanInner
        ((quadraticScalarRiemannianMetric (ι := Unit)).factor q x)
        ((quadraticScalarRiemannianMetric (ι := Unit)).factor q y) =
      euclideanInner
        ((quadraticScalarRiemannianMetric (ι := Unit)).inverseMetric q x) y := by
  simp only [quadraticScalarRiemannianMetric,
    scalarFactoredRiemannianMetric_factor_apply,
    scalarFactoredRiemannianMetric_inverseMetric_apply]
  rw [euclideanInner_smul_left, euclideanInner_smul_left,
    euclideanInner_smul_right]
  ring

/-- Equation (12) for the actual complete Hamiltonian of the concrete
nonconstant metric. -/
theorem fderiv_quadraticScalar_generalRelativisticHamiltonian_position_apply
    (potential : Position Unit → ℝ) (q : Position Unit)
    (p : Momentum Unit) (u : Position Unit) (m c : ℝ)
    (hm : 0 < m) (hc : 0 < c)
    (hpotential : DifferentiableAt ℝ potential q) :
    fderiv ℝ (fun r => generalRelativisticHamiltonian potential
      (quadraticScalarRiemannianMetric (ι := Unit)) m c (r, p)) q u =
      fderiv ℝ potential q u +
        (riemannianRelativisticMass quadraticScalarRiemannianMetric
          m c q p)⁻¹ *
          (-1 / 2 * euclideanInner
            ((quadraticScalarRiemannianMetric (ι := Unit)).inverseMetric q p)
            (quadraticScalarMetricVariationUnit q u
              ((quadraticScalarRiemannianMetric (ι := Unit)).inverseMetric q p))) +
        1 / 2 * coordinateTrace
          (((quadraticScalarRiemannianMetric (ι := Unit)).inverseMetric q).comp
            (quadraticScalarMetricVariationUnit q u)) := by
  exact fderiv_generalRelativisticHamiltonian_position_apply potential
    quadraticScalarRiemannianMetric
    (quadraticScalarMetricEquation12CertificateUnit q)
    m c p u hm hc hpotential

/-- Equation (13) for the momentum derivative of the same concrete complete
Hamiltonian. -/
theorem fderiv_quadraticScalar_generalRelativisticHamiltonian_momentum_apply
    (potential : Position Unit → ℝ) (q : Position Unit)
    (p h : Momentum Unit) (m c : ℝ) (hm : 0 < m) (hc : 0 < c) :
    fderiv ℝ (fun r => generalRelativisticHamiltonian potential
      (quadraticScalarRiemannianMetric (ι := Unit)) m c (q, r)) p h =
      euclideanInner
        (riemannianRelativisticVelocity quadraticScalarRiemannianMetric
          m c q p) h := by
  exact fderiv_generalRelativisticHamiltonian_momentum_apply potential
    quadraticScalarRiemannianMetric m c q p h hm hc
    (quadraticScalarRiemannianMetric_factor_compatible q)

/-- Coordinate Riesz representative of a scalar Fréchet derivative in the
one-dimensional function-space representation used by the executable model. -/
noncomputable def fderivGradientUnit
    (f : Position Unit → ℝ) (q : Position Unit) : Position Unit :=
  fun _ => fderiv ℝ f q (Pi.single Unit.unit 1)

theorem fderiv_eq_euclideanInner_fderivGradientUnit
    (f : Position Unit → ℝ) (q u : Position Unit) :
    fderiv ℝ f q u = euclideanInner (fderivGradientUnit f q) u := by
  have hu : u = u Unit.unit • (Pi.single Unit.unit 1 : Position Unit) := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Subsingleton.elim i Unit.unit]
    simp
  rw [hu, map_smul]
  simp [fderivGradientUnit, euclideanInner]
  ring

/-- Actual position derivative callback of the complete GR Hamiltonian for
the concrete nonconstant metric. -/
noncomputable def quadraticScalarGRPositionDerivative
    (potential : Position Unit → ℝ) (m c : ℝ) :
    PhaseSpace Unit → Position Unit := fun z =>
  fderivGradientUnit (fun q => generalRelativisticHamiltonian potential
    (quadraticScalarRiemannianMetric (ι := Unit)) m c (q, z.2)) z.1

/-- Actual momentum derivative callback of the same Hamiltonian. Equation
(13) identifies it with the Riemannian relativistic velocity. -/
noncomputable def quadraticScalarGRMomentumDerivative
    (m c : ℝ) : PhaseSpace Unit → Momentum Unit := fun z =>
  riemannianRelativisticVelocity
    (quadraticScalarRiemannianMetric (ι := Unit)) m c z.1 z.2

theorem quadraticScalarGRPositionDerivative_spec
    (potential : Position Unit → ℝ) (m c : ℝ)
    (z : PhaseSpace Unit) (u : Position Unit) :
    fderiv ℝ (fun q => generalRelativisticHamiltonian potential
      (quadraticScalarRiemannianMetric (ι := Unit)) m c (q, z.2)) z.1 u =
      euclideanInner (quadraticScalarGRPositionDerivative potential m c z) u :=
  fderiv_eq_euclideanInner_fderivGradientUnit _ _ _

theorem quadraticScalarGRMomentumDerivative_spec
    (potential : Position Unit → ℝ) (m c : ℝ)
    (hm : 0 < m) (hc : 0 < c) (z : PhaseSpace Unit)
    (h : Momentum Unit) :
    fderiv ℝ (fun p => generalRelativisticHamiltonian potential
      (quadraticScalarRiemannianMetric (ι := Unit)) m c (z.1, p)) z.2 h =
      euclideanInner (quadraticScalarGRMomentumDerivative m c z) h := by
  exact fderiv_quadraticScalar_generalRelativisticHamiltonian_momentum_apply
    potential z.1 z.2 h m c hm hc

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

/-- The concrete quadratic scalar metric has the exact factor/Jacobian
compatibility required by the GR momentum law. -/
theorem quadraticScalarRiemannianMetric_hasCompatibleFactorVolume :
    (quadraticScalarRiemannianMetric (ι := ι)).HasCompatibleFactorVolume :=
  scalarFactoredRiemannianMetric_hasCompatibleFactorVolume
    quadraticScalarScale quadraticScalarScale_pos

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

/-- Every measurable potential gives a measurable complete GR Hamiltonian for
the concrete globally positive nonconstant quadratic scalar metric. -/
theorem measurable_quadraticScalar_generalRelativisticHamiltonian
    {potential : Position ι → ℝ} (hpotential : Measurable potential)
    (m c : ℝ) :
    Measurable (generalRelativisticHamiltonian potential
      quadraticScalarRiemannianMetric m c) :=
  measurable_scalar_generalRelativisticHamiltonian hpotential
    measurable_quadraticScalarScale quadraticScalarScale_pos m c

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

end Mcmc.Relativistic
