import McmcLean.Relativistic.Derivatives
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Diagonal SoftAbs metric

Xu and Ge use the diagonal Hessian approximation
`G(q) = diag (h(q) ⊙ coth (α h(q)))` in Section 5.4.  This module defines
the scalar SoftAbs extension at zero, proves its positivity, and packages the
resulting diagonal factor, inverse metric, and log determinant in the general
GR-HMC metric interface.
-/

namespace McmcLean.Relativistic

open McmcLean.Hamiltonian
open Filter Topology Asymptotics

variable {ι : Type*} [Fintype ι]

/-- Scalar SoftAbs transform `x coth(αx)`, continuously extended at zero by
its limiting value `1/α`. -/
noncomputable def softAbs (α x : ℝ) : ℝ :=
  if x = 0 then α⁻¹ else x / Real.tanh (α * x)

theorem real_tanh_pos {x : ℝ} (hx : 0 < x) : 0 < Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  apply div_pos _ (Real.cosh_pos x)
  rw [Real.sinh_eq]
  have he : Real.exp (-x) < Real.exp x :=
    Real.exp_lt_exp.mpr (by linarith)
  linarith

theorem real_tanh_neg {x : ℝ} (hx : x < 0) : Real.tanh x < 0 := by
  rw [← neg_pos, ← Real.tanh_neg]
  exact real_tanh_pos (by linarith)

/-- SoftAbs eigenvalues are strictly positive for a positive smoothing
parameter, including at a zero Hessian eigenvalue. -/
theorem softAbs_pos (α : ℝ) (hα : 0 < α) (x : ℝ) :
    0 < softAbs α x := by
  unfold softAbs
  split_ifs with hx
  · exact inv_pos.mpr hα
  · rcases lt_or_gt_of_ne hx with hxneg | hxpos
    · exact div_pos_of_neg_of_neg hxneg
        (real_tanh_neg (mul_neg_of_pos_of_neg hα hxneg))
    · exact div_pos hxpos (real_tanh_pos (mul_pos hα hxpos))

/-- The zero-extended SoftAbs transform is measurable. -/
theorem measurable_softAbs (α : ℝ) : Measurable (softAbs α) := by
  unfold softAbs
  apply Measurable.ite
  · simpa only [Set.setOf_eq_eq_singleton] using
      measurableSet_singleton (0 : ℝ)
  · exact measurable_const
  · apply measurable_id.div
    rw [show (fun x : ℝ => Real.tanh (α * x)) = fun x =>
        (Real.exp (α * x) - Real.exp (-(α * x))) /
          (Real.exp (α * x) + Real.exp (-(α * x))) by
      funext x
      rw [Real.tanh_eq]]
    fun_prop

@[fun_prop]
theorem differentiableAt_real_tanh (x : ℝ) :
    DifferentiableAt ℝ Real.tanh x := by
  rw [show Real.tanh = fun y =>
      (Real.exp y - Real.exp (-y)) / (Real.exp y + Real.exp (-y)) by
    funext y
    rw [Real.tanh_eq]]
  apply DifferentiableAt.div
  · fun_prop
  · fun_prop
  · exact ne_of_gt (add_pos (Real.exp_pos _) (Real.exp_pos _))

/-- The numerator in the SoftAbs difference quotient vanishes to order
strictly greater than two at zero. -/
theorem softAbsNumerator_isLittleO_sq :
    (fun x : ℝ => x * Real.cosh x - Real.sinh x) =o[𝓝 0]
      fun x => x ^ 2 := by
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  let f : ℝ → ℝ := fun x => x * Real.cosh x - Real.sinh x
  let f' : ℝ → ℝ := fun x => x * Real.sinh x
  have hderiv : ∀ x : ℝ, HasDerivAt f (f' x) x := by
    intro x
    dsimp [f, f']
    convert ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub
      (Real.hasDerivAt_sinh x) using 1
    all_goals first | (funext y; simp [id_eq, mul_comm]) | simp [id_eq]
  have hsinhO : Real.sinh =O[𝓝 0] fun x : ℝ => x :=
    Real.isEquivalent_sinh.isBigO
  have hderivO : f' =O[𝓝 0] fun x : ℝ => x ^ 2 := by
    dsimp [f']
    simpa [pow_two] using
      (isBigO_refl (fun x : ℝ => x) (𝓝 0)).mul hsinhO
  have hderivo : f' =o[𝓝 0] fun x : ℝ => x :=
    hderivO.trans_isLittleO (isLittleO_pow_id (n := 2) (by omega))
  have h := convex_univ.isLittleO_pow_succ_real (Set.mem_univ (0 : ℝ))
    (n := 1) (fun x _ => (hderiv x).hasDerivWithinAt)
      (by simpa using hderivo)
  simpa [f] using h

/-- The difference quotient of the unit-parameter SoftAbs extension tends to
zero at its removable branch. -/
theorem tendsto_softAbsDifferenceQuotient_zero :
    Tendsto (fun x : ℝ =>
      (x * Real.cosh x - Real.sinh x) / (x * Real.sinh x))
      (𝓝 0) (𝓝 0) := by
  have hden : (fun x : ℝ => x * Real.sinh x) ~[𝓝 0]
      fun x => x ^ 2 := by
    have hraw := (IsEquivalent.refl :
      (fun x : ℝ => x) ~[𝓝 0] fun x => x).mul Real.isEquivalent_sinh
    convert hraw using 1 <;> funext x <;> simp [pow_two]
  exact (softAbsNumerator_isLittleO_sq.trans_isBigO
    hden.symm.isBigO).tendsto_div_nhds_zero

/-- The unit-parameter SoftAbs extension has derivative zero at the removable
singularity. -/
theorem hasDerivAt_softAbs_one_zero : HasDerivAt (softAbs 1) 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  refine (tendsto_softAbsDifferenceQuotient_zero.mono_left inf_le_left).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := hx
  have hsinh : Real.sinh x ≠ 0 := Real.sinh_ne_zero.mpr hx0
  simp [softAbs, hx0, Real.tanh_eq_sinh_div_cosh]
  field_simp [hx0, hsinh]

/-- Scaling reduces every positive-parameter SoftAbs transform to the unit
parameter transform. -/
theorem softAbs_eq_inv_mul_softAbs_one
    (α x : ℝ) (hα : α ≠ 0) :
    softAbs α x = α⁻¹ * softAbs 1 (α * x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [softAbs]
  · have hax : α * x ≠ 0 := mul_ne_zero hα hx
    simp [softAbs, hx, hax]
    field_simp [hα]

/-- SoftAbs has derivative zero at its removable branch for every positive
smoothing parameter. -/
theorem hasDerivAt_softAbs_zero
    (α : ℝ) (hα : 0 < α) : HasDerivAt (softAbs α) 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have ht0 : ContinuousAt (fun t : ℝ => α * t) 0 := by fun_prop
  have ht : Tendsto (fun t : ℝ => α * t) (𝓝[≠] 0) (𝓝 0) := by
    convert ht0.mono_left
      (show (𝓝[≠] (0 : ℝ)) ≤ 𝓝 0 from inf_le_left) using 1
    simp
  refine (tendsto_softAbsDifferenceQuotient_zero.comp ht).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht0
  have htne : t ≠ 0 := ht0
  have hatne : α * t ≠ 0 := mul_ne_zero hα.ne' htne
  simp only [zero_add, smul_eq_mul]
  rw [softAbs_eq_inv_mul_softAbs_one α t hα.ne']
  simp [softAbs, hatne, Real.tanh_eq_sinh_div_cosh]
  have hsinh : Real.sinh (α * t) ≠ 0 := Real.sinh_ne_zero.mpr hatne
  field_simp [hα.ne', htne, hsinh]

/-- SoftAbs is differentiable at its zero branch for every positive smoothing
parameter. -/
theorem differentiableAt_softAbs_zero
    (α : ℝ) (hα : 0 < α) : DifferentiableAt ℝ (softAbs α) 0 :=
  (hasDerivAt_softAbs_zero α hα).differentiableAt

/-- SoftAbs is differentiable away from its removable zero branch. -/
theorem differentiableAt_softAbs_of_ne_zero
    (α x : ℝ) (hα : 0 < α) (hx : x ≠ 0) :
    DifferentiableAt ℝ (softAbs α) x := by
  have hquot : DifferentiableAt ℝ
      (fun y => y / Real.tanh (α * y)) x := by
    have hden : Real.tanh (α * x) ≠ 0 := by
      rcases lt_or_gt_of_ne hx with hxneg | hxpos
      · exact ne_of_lt (real_tanh_neg (mul_neg_of_pos_of_neg hα hxneg))
      · exact ne_of_gt (real_tanh_pos (mul_pos hα hxpos))
    apply DifferentiableAt.div
    · fun_prop
    · fun_prop
    · exact hden
  apply hquot.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hx] with y hy
  simp [softAbs, hy]

/-- The positive-parameter SoftAbs transform is differentiable everywhere,
including at a zero Hessian eigenvalue. -/
theorem differentiableAt_softAbs
    (α x : ℝ) (hα : 0 < α) : DifferentiableAt ℝ (softAbs α) x := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact differentiableAt_softAbs_zero α hα
  · exact differentiableAt_softAbs_of_ne_zero α x hα hx

@[simp]
theorem softAbs_zero (α : ℝ) : softAbs α 0 = α⁻¹ := by
  simp [softAbs]

/-- Diagonal metric eigenvalues obtained by applying SoftAbs to the diagonal
of a supplied Hessian approximation. -/
noncomputable def diagonalSoftAbsEigenvalue
    (α : ℝ) (hessianDiagonal : Position ι → ι → ℝ)
    (q : Position ι) (i : ι) : ℝ :=
  softAbs α (hessianDiagonal q i)

omit [Fintype ι] in
theorem diagonalSoftAbsEigenvalue_pos
    (α : ℝ) (hα : 0 < α)
    (hessianDiagonal : Position ι → ι → ℝ) (q : Position ι) (i : ι) :
    0 < diagonalSoftAbsEigenvalue α hessianDiagonal q i :=
  softAbs_pos α hα _

omit [Fintype ι] in
theorem measurable_diagonalSoftAbsEigenvalue
    (α : ℝ) (hessianDiagonal : Position ι → ι → ℝ) (i : ι)
    (hessianMeasurable : Measurable fun q => hessianDiagonal q i) :
    Measurable fun q => diagonalSoftAbsEigenvalue α hessianDiagonal q i :=
  (measurable_softAbs α).comp hessianMeasurable

/-- The inverse-square-root diagonal factor `A(q)` satisfying
`A(q)ᵀA(q)=G(q)⁻¹`. -/
noncomputable def diagonalSoftAbsFactor
    (α : ℝ) (hα : 0 < α)
    (hessianDiagonal : Position ι → ι → ℝ) (q : Position ι) :
    Momentum ι ≃L[ℝ] Momentum ι :=
  ContinuousLinearEquiv.piCongrRight fun i =>
    ContinuousLinearEquiv.smulLeft (Units.mk0
      (Real.sqrt (diagonalSoftAbsEigenvalue α hessianDiagonal q i))⁻¹
      (inv_ne_zero (ne_of_gt (Real.sqrt_pos.2
        (diagonalSoftAbsEigenvalue_pos α hα hessianDiagonal q i)))))

omit [Fintype ι] in
@[simp]
theorem diagonalSoftAbsFactor_apply
    (α : ℝ) (hα : 0 < α)
    (hessianDiagonal : Position ι → ι → ℝ)
    (q : Position ι) (p : Momentum ι) (i : ι) :
    diagonalSoftAbsFactor α hα hessianDiagonal q p i =
      (Real.sqrt (diagonalSoftAbsEigenvalue α hessianDiagonal q i))⁻¹ * p i := by
  rfl

omit [Fintype ι] in
/-- The inverse factor multiplies coordinate `i` by the positive square root
of the corresponding SoftAbs metric eigenvalue. -/
theorem diagonalSoftAbsFactor_symm_apply
    (α : ℝ) (hα : 0 < α)
    (hessianDiagonal : Position ι → ι → ℝ)
    (q : Position ι) (p : Momentum ι) (i : ι) :
    (diagonalSoftAbsFactor α hα hessianDiagonal q).symm p i =
      Real.sqrt (diagonalSoftAbsEigenvalue α hessianDiagonal q i) * p i := by
  let A := diagonalSoftAbsFactor α hα hessianDiagonal q
  have hvec : A.symm p = fun j =>
      Real.sqrt (diagonalSoftAbsEigenvalue α hessianDiagonal q j) * p j := by
    apply A.injective
    ext j
    rw [A.apply_symm_apply]
    simp [A, diagonalSoftAbsFactor_apply]
    have hsj : Real.sqrt
        (diagonalSoftAbsEigenvalue α hessianDiagonal q j) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2
        (diagonalSoftAbsEigenvalue_pos α hα hessianDiagonal q j))
    field_simp
  exact congrFun hvec i

/-- Diagonal inverse-metric action for the SoftAbs metric. -/
noncomputable def diagonalSoftAbsInverseMetric
    (α : ℝ) (hessianDiagonal : Position ι → ι → ℝ)
    (q : Position ι) : Momentum ι →ₗ[ℝ] Momentum ι :=
  diagonalMomentumMap fun i =>
    (diagonalSoftAbsEigenvalue α hessianDiagonal q i)⁻¹

omit [Fintype ι] in
@[simp]
theorem diagonalSoftAbsInverseMetric_apply
    (α : ℝ) (hessianDiagonal : Position ι → ι → ℝ)
    (q : Position ι) (p : Momentum ι) (i : ι) :
    diagonalSoftAbsInverseMetric α hessianDiagonal q p i =
      (diagonalSoftAbsEigenvalue α hessianDiagonal q i)⁻¹ * p i := by
  rfl

/-- Factored metric corresponding exactly to the paper's diagonal SoftAbs
approximation. -/
noncomputable def diagonalSoftAbsMetric
    (α : ℝ) (hα : 0 < α)
    (hessianDiagonal : Position ι → ι → ℝ) :
    FactoredRiemannianMetric ι where
  factor := diagonalSoftAbsFactor α hα hessianDiagonal
  inverseMetric := diagonalSoftAbsInverseMetric α hessianDiagonal
  logDet q := ∑ i, Real.log
    (diagonalSoftAbsEigenvalue α hessianDiagonal q i)

/-- Coordinatewise measurable Hessian data and a measurable potential give a
jointly measurable complete diagonal-SoftAbs GR Hamiltonian. -/
theorem measurable_diagonalSoftAbs_generalRelativisticHamiltonian
    (potential : Position ι → ℝ) (hpotential : Measurable potential)
    (α : ℝ) (hα : 0 < α)
    (hessianDiagonal : Position ι → ι → ℝ)
    (hessianMeasurable : ∀ i, Measurable fun q => hessianDiagonal q i)
    (m c : ℝ) :
    Measurable (generalRelativisticHamiltonian potential
      (diagonalSoftAbsMetric α hα hessianDiagonal) m c) := by
  have heigen : ∀ i, Measurable fun q =>
      diagonalSoftAbsEigenvalue α hessianDiagonal q i := fun i =>
    measurable_diagonalSoftAbsEigenvalue α hessianDiagonal i
      (hessianMeasurable i)
  have hfactor : Measurable fun z : PhaseSpace ι =>
      (diagonalSoftAbsMetric α hα hessianDiagonal).factor z.1 z.2 := by
    apply measurable_pi_lambda
    intro i
    rw [show (fun z : PhaseSpace ι =>
        (diagonalSoftAbsMetric α hα hessianDiagonal).factor z.1 z.2 i) =
        fun z =>
          (Real.sqrt
            (diagonalSoftAbsEigenvalue α hessianDiagonal z.1 i))⁻¹ * z.2 i by
      funext z
      exact diagonalSoftAbsFactor_apply α hα hessianDiagonal z.1 z.2 i]
    exact ((((heigen i).comp measurable_fst).sqrt.inv).mul
      ((measurable_pi_apply i).comp measurable_snd))
  have hkinetic : Measurable fun z : PhaseSpace ι =>
      relativisticKineticEnergy m c
        ((diagonalSoftAbsMetric α hα hessianDiagonal).factor z.1 z.2) :=
    (continuous_relativisticKineticEnergy m c).measurable.comp hfactor
  have hlogDet : Measurable fun q : Position ι =>
      ∑ i, Real.log
        (diagonalSoftAbsEigenvalue α hessianDiagonal q i) := by
    fun_prop
  rw [show generalRelativisticHamiltonian potential
      (diagonalSoftAbsMetric α hα hessianDiagonal) m c = fun z =>
      potential z.1 +
        (relativisticKineticEnergy m c
          ((diagonalSoftAbsMetric α hα hessianDiagonal).factor z.1 z.2) +
          (1 / 2 : ℝ) * ∑ i,
            Real.log (diagonalSoftAbsEigenvalue α hessianDiagonal z.1 i)) by
    funext z
    rfl]
  exact (hpotential.comp measurable_fst).add
    (hkinetic.add
      (measurable_const.mul (hlogDet.comp measurable_fst)))

/-- The diagonal factor has the intended quadratic compatibility
`AᵀA=G⁻¹`, which discharges the hypothesis of Equation (13). -/
theorem diagonalSoftAbsMetric_factor_compatibility
    (α : ℝ) (hα : 0 < α)
    (hessianDiagonal : Position ι → ι → ℝ)
    (q : Position ι) (p r : Momentum ι) :
    euclideanInner
        ((diagonalSoftAbsMetric α hα hessianDiagonal).factor q p)
        ((diagonalSoftAbsMetric α hα hessianDiagonal).factor q r) =
      euclideanInner
        ((diagonalSoftAbsMetric α hα hessianDiagonal).inverseMetric q p) r := by
  unfold euclideanInner diagonalSoftAbsMetric
  apply Finset.sum_congr rfl
  intro i _
  rw [diagonalSoftAbsFactor_apply, diagonalSoftAbsFactor_apply,
    diagonalSoftAbsInverseMetric_apply]
  have hg := diagonalSoftAbsEigenvalue_pos α hα hessianDiagonal q i
  have hsqrt : Real.sqrt
      (diagonalSoftAbsEigenvalue α hessianDiagonal q i) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hg)
  have hsq := Real.sq_sqrt hg.le
  field_simp [hsqrt, hg.ne']
  rw [hsq]
  ring

/-- Fréchet derivative of the pointwise inverse of a scalar field. -/
theorem fderiv_inv_comp_apply {f : Position ι → ℝ} (q u : Position ι)
    (hf : DifferentiableAt ℝ f q) (hne : f q ≠ 0) :
    fderiv ℝ f⁻¹ q u =
      -(f q)⁻¹ * (f q)⁻¹ * fderiv ℝ f q u := by
  change fderiv ℝ (Inv.inv ∘ f) q u = _
  rw [fderiv_comp (f := f) (g := Inv.inv) (x := q)
    (differentiableAt_inv hne) hf, ContinuousLinearMap.comp_apply,
    fderiv_inv' hne]
  simp [ContinuousLinearMap.mulLeftRight_apply]
  ring

/-- The squared factor norm is the expected diagonal inverse-metric quadratic
form. -/
theorem squaredEuclideanNorm_diagonalSoftAbsFactor
    (α : ℝ) (hα : 0 < α)
    (hessianDiagonal : Position ι → ι → ℝ)
    (q : Position ι) (p : Momentum ι) :
    squaredEuclideanNorm
        (diagonalSoftAbsFactor α hα hessianDiagonal q p) =
      ∑ i, (diagonalSoftAbsEigenvalue α hessianDiagonal q i)⁻¹ *
        p i * p i := by
  unfold squaredEuclideanNorm euclideanInner
  apply Finset.sum_congr rfl
  intro i _
  rw [diagonalSoftAbsFactor_apply]
  have hg := diagonalSoftAbsEigenvalue_pos α hα hessianDiagonal q i
  have hs : Real.sqrt
      (diagonalSoftAbsEigenvalue α hessianDiagonal q i) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hg)
  have hsq := Real.sq_sqrt hg.le
  field_simp [hs, hg.ne']
  rw [hsq]
  ring

/-- Coordinate derivative data for a positive diagonal metric field at one
position.  For diagonal SoftAbs this is supplied by differentiating each
SoftAbs-transformed Hessian diagonal entry. -/
structure DiagonalEigenvalueDerivativeData
    (eigenvalue : Position ι → ι → ℝ) (q : Position ι) where
  derivative : Position ι → ι → ℝ
  differentiableAt : ∀ i,
    DifferentiableAt ℝ (fun r => eigenvalue r i) q
  fderiv_apply : ∀ i u,
    fderiv ℝ (fun r => eigenvalue r i) q u = derivative u i

/-- A coordinatewise differentiable Hessian diagonal supplies SoftAbs
eigenvalue derivative data at every position, including zero Hessian entries. -/
noncomputable def diagonalSoftAbsDerivativeData
    (α : ℝ) (hα : 0 < α)
    (hessianDiagonal : Position ι → ι → ℝ) (q : Position ι)
    (hdiff : ∀ i, DifferentiableAt ℝ (fun r => hessianDiagonal r i) q) :
    DiagonalEigenvalueDerivativeData
      (diagonalSoftAbsEigenvalue α hessianDiagonal) q where
  derivative u i := fderiv ℝ
    (fun r => diagonalSoftAbsEigenvalue α hessianDiagonal r i) q u
  differentiableAt i :=
    (differentiableAt_softAbs α (hessianDiagonal q i) hα).comp q (hdiff i)
  fderiv_apply _ _ := rfl

/-- Compatibility constructor retaining the older nonzero-entry interface.
The unrestricted `diagonalSoftAbsDerivativeData` should normally be used. -/
noncomputable def diagonalSoftAbsDerivativeDataOfNonzero
    (α : ℝ) (hα : 0 < α)
    (hessianDiagonal : Position ι → ι → ℝ) (q : Position ι)
    (hdiff : ∀ i, DifferentiableAt ℝ (fun r => hessianDiagonal r i) q)
    (hne : ∀ i, hessianDiagonal q i ≠ 0) :
    DiagonalEigenvalueDerivativeData
      (diagonalSoftAbsEigenvalue α hessianDiagonal) q where
  derivative u i := fderiv ℝ
    (fun r => diagonalSoftAbsEigenvalue α hessianDiagonal r i) q u
  differentiableAt i :=
    (differentiableAt_softAbs_of_ne_zero α (hessianDiagonal q i) hα (hne i)).comp
      q (hdiff i)
  fderiv_apply _ _ := rfl

/-- Coordinatewise differentiability of the SoftAbs eigenvalues constructs
the complete matrix-calculus certificate consumed by Equation (12). -/
noncomputable def diagonalSoftAbsMetricEquation12Certificate
    [DecidableEq ι] (α : ℝ) (hα : 0 < α)
    (hessianDiagonal : Position ι → ι → ℝ) (q : Position ι)
    (data : DiagonalEigenvalueDerivativeData
      (diagonalSoftAbsEigenvalue α hessianDiagonal) q) :
    (diagonalSoftAbsMetric α hα hessianDiagonal).Equation12Certificate q := by
  let g : Position ι → ι → ℝ :=
    diagonalSoftAbsEigenvalue α hessianDiagonal
  let variation : Position ι → Momentum ι →ₗ[ℝ] Momentum ι :=
    fun u => diagonalMomentumMap (data.derivative u)
  refine {
    metricVariation := variation
    differentiableAt_quadratic := ?_
    fderiv_quadratic := ?_
    differentiableAt_logDet := ?_
    fderiv_logDet := ?_ }
  · intro p
    have heq : (fun r => squaredEuclideanNorm
        ((diagonalSoftAbsMetric α hα hessianDiagonal).factor r p)) =
        fun r => ∑ i, (g r i)⁻¹ * p i * p i := by
      funext r
      exact squaredEuclideanNorm_diagonalSoftAbsFactor
        α hα hessianDiagonal r p
    rw [heq]
    apply DifferentiableAt.fun_sum
    intro i _
    have hne : g q i ≠ 0 :=
      (diagonalSoftAbsEigenvalue_pos α hα hessianDiagonal q i).ne'
    exact (((data.differentiableAt i).inv hne).mul_const (p i)).mul_const (p i)
  · intro p u
    have heq : (fun r => squaredEuclideanNorm
        ((diagonalSoftAbsMetric α hα hessianDiagonal).factor r p)) =
        fun r => ∑ i, (g r i)⁻¹ * p i * p i := by
      funext r
      exact squaredEuclideanNorm_diagonalSoftAbsFactor
        α hα hessianDiagonal r p
    rw [heq]
    have hterm : ∀ i, DifferentiableAt ℝ
        (fun r => (g r i)⁻¹ * p i * p i) q := fun i =>
      (((data.differentiableAt i).inv
        (diagonalSoftAbsEigenvalue_pos α hα hessianDiagonal q i).ne').mul_const
          (p i)).mul_const (p i)
    rw [fderiv_fun_sum (fun i _ => hterm i)]
    simp only [sum_apply]
    have hcoord : ∀ i,
        fderiv ℝ (fun r => (g r i)⁻¹ * p i * p i) q u =
          -(g q i)⁻¹ * (g q i)⁻¹ * data.derivative u i * p i * p i := by
      intro i
      dsimp [g]
      have hmul1 := fderiv_mul_const ((data.differentiableAt i).inv
        (diagonalSoftAbsEigenvalue_pos α hα hessianDiagonal q i).ne') (p i)
      have hmul2 := fderiv_mul_const
        (((data.differentiableAt i).inv
          (diagonalSoftAbsEigenvalue_pos α hα hessianDiagonal q i).ne').mul_const
            (p i)) (p i)
      have hmul1app := congrArg (fun L => L u) hmul1
      have hmul2app := congrArg (fun L => L u) hmul2
      have hfun2 : (fun r =>
          (diagonalSoftAbsEigenvalue α hessianDiagonal r i)⁻¹ * p i * p i) =
          (fun y => (fun r =>
            diagonalSoftAbsEigenvalue α hessianDiagonal r i)⁻¹ y * p i * p i) := by
        funext r
        rfl
      rw [hfun2, hmul2app]
      simp only [smul_apply, smul_eq_mul]
      rw [hmul1app]
      simp only [smul_apply, smul_eq_mul]
      rw [fderiv_inv_comp_apply q u (data.differentiableAt i)
        (diagonalSoftAbsEigenvalue_pos α hα hessianDiagonal q i).ne',
        data.fderiv_apply]
      ring
    simp_rw [hcoord]
    unfold euclideanInner variation diagonalSoftAbsMetric
    simp only [diagonalSoftAbsInverseMetric_apply]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [g]
    change _ = -((diagonalSoftAbsEigenvalue α hessianDiagonal q i)⁻¹ * p i *
      (data.derivative u i *
        (diagonalSoftAbsInverseMetric α hessianDiagonal q p i)))
    rw [diagonalSoftAbsInverseMetric_apply]
    ring
  · change DifferentiableAt ℝ (fun r => ∑ i,
      Real.log (diagonalSoftAbsEigenvalue α hessianDiagonal r i)) q
    apply DifferentiableAt.fun_sum
    intro i _
    exact (Real.differentiableAt_log
      (diagonalSoftAbsEigenvalue_pos α hα hessianDiagonal q i).ne').comp q
        (data.differentiableAt i)
  · intro u
    change fderiv ℝ (fun r => ∑ i,
      Real.log (diagonalSoftAbsEigenvalue α hessianDiagonal r i)) q u = _
    rw [fderiv_fun_sum]
    · simp only [sum_apply]
      have hlog : ∀ i, fderiv ℝ
          (fun r => Real.log
            (diagonalSoftAbsEigenvalue α hessianDiagonal r i)) q u =
          (diagonalSoftAbsEigenvalue α hessianDiagonal q i)⁻¹ *
            data.derivative u i := by
        intro i
        change fderiv ℝ (Real.log ∘ fun r =>
          diagonalSoftAbsEigenvalue α hessianDiagonal r i) q u = _
        rw [fderiv_comp
          (f := fun r => diagonalSoftAbsEigenvalue α hessianDiagonal r i)
          (g := Real.log) (x := q)
          (Real.differentiableAt_log
            (diagonalSoftAbsEigenvalue_pos α hα hessianDiagonal q i).ne')
          (data.differentiableAt i), ContinuousLinearMap.comp_apply,
          (Real.hasDerivAt_log
            (diagonalSoftAbsEigenvalue_pos α hα hessianDiagonal q i).ne').hasFDerivAt.fderiv]
        simp [ContinuousLinearMap.toSpanSingleton_apply, data.fderiv_apply]
        ring
      simp_rw [hlog]
      unfold coordinateTrace variation
      apply Finset.sum_congr rfl
      intro i _
      change (diagonalSoftAbsEigenvalue α hessianDiagonal q i)⁻¹ *
          data.derivative u i =
        diagonalSoftAbsInverseMetric α hessianDiagonal q
          (fun j => data.derivative u j *
            (Pi.single i (1 : ℝ) : Momentum ι) j) i
      rw [diagonalSoftAbsInverseMetric_apply]
      simp
    · intro i _
      exact (Real.differentiableAt_log
        (diagonalSoftAbsEigenvalue_pos α hα hessianDiagonal q i).ne').comp q
          (data.differentiableAt i)

/-- A coordinatewise differentiable Hessian diagonal automatically supplies
the complete Equation (12) certificate, with no nonzero-eigenvalue premise. -/
noncomputable def diagonalSoftAbsMetricEquation12CertificateOfDifferentiable
    [DecidableEq ι] (α : ℝ) (hα : 0 < α)
    (hessianDiagonal : Position ι → ι → ℝ) (q : Position ι)
    (hdiff : ∀ i, DifferentiableAt ℝ (fun r => hessianDiagonal r i) q) :
    (diagonalSoftAbsMetric α hα hessianDiagonal).Equation12Certificate q :=
  diagonalSoftAbsMetricEquation12Certificate α hα hessianDiagonal q
    (diagonalSoftAbsDerivativeData α hα hessianDiagonal q hdiff)

/-- Equation (12) instantiated for diagonal SoftAbs from coordinatewise
eigenvalue derivative data. -/
theorem fderiv_diagonalSoftAbsKineticEnergy_position_apply
    [DecidableEq ι] (α : ℝ) (hα : 0 < α)
    (hessianDiagonal : Position ι → ι → ℝ) (q : Position ι)
    (data : DiagonalEigenvalueDerivativeData
      (diagonalSoftAbsEigenvalue α hessianDiagonal) q)
    (m c : ℝ) (p : Momentum ι) (u : Position ι)
    (hm : 0 < m) (hc : 0 < c) :
    let cert := diagonalSoftAbsMetricEquation12Certificate
      α hα hessianDiagonal q data
    fderiv ℝ (fun r => riemannianRelativisticKineticEnergy
      (diagonalSoftAbsMetric α hα hessianDiagonal) m c r p) q u =
      (riemannianRelativisticMass
        (diagonalSoftAbsMetric α hα hessianDiagonal) m c q p)⁻¹ *
          (-1 / 2 * euclideanInner
            ((diagonalSoftAbsMetric α hα hessianDiagonal).inverseMetric q p)
            (cert.metricVariation u
              ((diagonalSoftAbsMetric α hα hessianDiagonal).inverseMetric q p))) +
        1 / 2 * coordinateTrace
          (((diagonalSoftAbsMetric α hα hessianDiagonal).inverseMetric q).comp
            (cert.metricVariation u)) :=
  fderiv_riemannianRelativisticKineticEnergy_position_apply
    (diagonalSoftAbsMetric α hα hessianDiagonal)
    (diagonalSoftAbsMetricEquation12Certificate
      α hα hessianDiagonal q data) m c p u hm hc

/-- The diagonal SoftAbs factor has exactly the Jacobian encoded by the sum
of log eigenvalues.  This closes the measure-theoretic compatibility needed
by momentum refresh and position-kernel invariance. -/
theorem diagonalSoftAbsMetric_hasCompatibleFactorVolume
    [DecidableEq ι] (α : ℝ) (hα : 0 < α)
    (hessianDiagonal : Position ι → ι → ℝ) :
    (diagonalSoftAbsMetric α hα hessianDiagonal).HasCompatibleFactorVolume := by
  intro q
  let D : ι → ℝ := fun i =>
    Real.sqrt (diagonalSoftAbsEigenvalue α hessianDiagonal q i)
  have hD : ∀ i, 0 < D i := fun i =>
    Real.sqrt_pos.2
      (diagonalSoftAbsEigenvalue_pos α hα hessianDiagonal q i)
  have hdet : Matrix.det (Matrix.diagonal D) ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (hD i).ne'
  have hmap : MeasureTheory.Measure.map
      ((diagonalSoftAbsMetric α hα hessianDiagonal).factor q).symm
      (MeasureTheory.volume : MeasureTheory.Measure (Momentum ι)) =
      MeasureTheory.Measure.map (Matrix.toLin' (Matrix.diagonal D))
        MeasureTheory.volume := by
    congr 1
    funext p
    ext i
    change (diagonalSoftAbsFactor α hα hessianDiagonal q).symm p i = _
    rw [diagonalSoftAbsFactor_symm_apply]
    simp [D, Matrix.diagonal_toLin']
  rw [hmap, Real.map_matrix_volume_pi_eq_smul_volume_pi hdet]
  congr 1
  rw [Matrix.det_diagonal]
  have hprod : 0 < ∏ i, D i := Finset.prod_pos fun i _ => hD i
  rw [abs_of_pos (inv_pos.mpr hprod)]
  apply congrArg ENNReal.ofReal
  rw [← Real.exp_log (inv_pos.mpr hprod)]
  congr 1
  rw [Real.log_inv, Real.log_prod (fun i _ => (hD i).ne')]
  simp_rw [D, Real.log_sqrt
    (diagonalSoftAbsEigenvalue_pos α hα hessianDiagonal q _).le]
  unfold diagonalSoftAbsMetric
  change -(∑ x, Real.log
      (diagonalSoftAbsEigenvalue α hessianDiagonal q x) / 2) =
    -(1 / 2) * ∑ x, Real.log
      (diagonalSoftAbsEigenvalue α hessianDiagonal q x)
  rw [← Finset.sum_div]
  ring

/-- Equation (13) for the concrete diagonal SoftAbs metric. -/
theorem fderiv_diagonalSoftAbsHamiltonian_momentum_apply
    (potential : Position ι → ℝ)
    (α : ℝ) (hα : 0 < α)
    (hessianDiagonal : Position ι → ι → ℝ)
    (m c : ℝ) (q : Position ι) (p h : Momentum ι)
    (hm : 0 < m) (hc : 0 < c) :
    fderiv ℝ (fun r => generalRelativisticHamiltonian potential
      (diagonalSoftAbsMetric α hα hessianDiagonal) m c (q, r)) p h =
      euclideanInner
        (riemannianRelativisticVelocity
          (diagonalSoftAbsMetric α hα hessianDiagonal) m c q p) h :=
  fderiv_generalRelativisticHamiltonian_momentum_apply potential
    (diagonalSoftAbsMetric α hα hessianDiagonal) m c q p h hm hc
    (diagonalSoftAbsMetric_factor_compatibility α hα hessianDiagonal q)

end McmcLean.Relativistic
