import Mcmc.Relativistic.SoftAbs
import Mcmc.Relativistic.ScalarSliceBounds

/-!
# A nondegenerate nonconstant diagonal-SoftAbs target

The zero-reaching sinusoidal client exercises the removable SoftAbs branch.
For the practical implicit-solver instance it is also useful to retain a
uniform gap from zero.  Here

`U(q) = q² - sin q`, `U'(q) = 2q - cos q`, `U''(q) = 2 + sin q ∈ [1,3]`.

Thus the metric is still the SoftAbs transform of the actual Hessian, while
all hyperbolic denominators live on a compact positive interval.
-/

namespace Mcmc.Relativistic

open Mcmc.Hamiltonian

noncomputable def shiftedSinusoidalPotential (q : Position Unit) : ℝ :=
  (q Unit.unit) ^ 2 - Real.sin (q Unit.unit)

noncomputable def shiftedSinusoidalGradient
    (q : Position Unit) : Momentum Unit :=
  fun _ => 2 * q Unit.unit - Real.cos (q Unit.unit)

noncomputable def shiftedSinusoidalHessianDiagonal
    (q : Position Unit) (_ : Unit) : ℝ :=
  2 + Real.sin (q Unit.unit)

theorem shiftedSinusoidalHessianDiagonal_mem_Icc (q : Position Unit) :
    shiftedSinusoidalHessianDiagonal q Unit.unit ∈ Set.Icc (1 : ℝ) 3 := by
  constructor
  · unfold shiftedSinusoidalHessianDiagonal
    linarith [Real.neg_one_le_sin (q Unit.unit)]
  · unfold shiftedSinusoidalHessianDiagonal
    linarith [Real.sin_le_one (q Unit.unit)]

theorem measurable_shiftedSinusoidalPotential :
    Measurable shiftedSinusoidalPotential := by
  unfold shiftedSinusoidalPotential
  fun_prop

theorem measurable_shiftedSinusoidalHessianDiagonal (i : Unit) :
    Measurable fun q : Position Unit => shiftedSinusoidalHessianDiagonal q i := by
  unfold shiftedSinusoidalHessianDiagonal
  fun_prop

theorem differentiable_shiftedSinusoidalHessianDiagonal (i : Unit) :
    Differentiable ℝ (fun q : Position Unit =>
      shiftedSinusoidalHessianDiagonal q i) := by
  unfold shiftedSinusoidalHessianDiagonal
  fun_prop

theorem shiftedSinusoidalHessianDiagonal_eq_fderiv_gradient
    (q : Position Unit) :
    shiftedSinusoidalHessianDiagonal q Unit.unit =
      fderiv ℝ (fun r : Position Unit =>
        shiftedSinusoidalGradient r Unit.unit) q
        (Pi.single Unit.unit 1) := by
  have hscalar : HasDerivAt (fun x : ℝ => 2 * x - Real.cos x)
      (2 + Real.sin (q Unit.unit)) (q Unit.unit) := by
    have hraw := ((hasDerivAt_id (q Unit.unit)).const_mul 2).sub
      (Real.hasDerivAt_cos (q Unit.unit))
    change HasDerivAt ((fun y : ℝ => 2 * y) - Real.cos)
      (2 + Real.sin (q Unit.unit)) (q Unit.unit)
    simpa only [id_eq, mul_one, sub_neg_eq_add] using hraw
  have hcomp := hscalar.comp_hasFDerivAt q
    (hasFDerivAt_apply (𝕜 := ℝ) Unit.unit q)
  have hf := congrArg
    (fun L : Position Unit →L[ℝ] ℝ => L (Pi.single Unit.unit 1))
    hcomp.fderiv
  have heq :
      ((fun x : ℝ => 2 * x - Real.cos x) ∘
          fun r : Position Unit => r Unit.unit) =
        (fun r : Position Unit => 2 * r Unit.unit - Real.cos (r Unit.unit)) := rfl
  rw [heq] at hf
  simpa [shiftedSinusoidalGradient, shiftedSinusoidalHessianDiagonal] using hf.symm

noncomputable abbrev shiftedSinusoidalSoftAbsMetric :
    FactoredRiemannianMetric Unit :=
  diagonalSoftAbsMetric 1 (by norm_num) shiftedSinusoidalHessianDiagonal

noncomputable def shiftedSinusoidalEquation12Certificate
    (q : Position Unit) :
    shiftedSinusoidalSoftAbsMetric.Equation12Certificate q :=
  diagonalSoftAbsMetricEquation12CertificateOfDifferentiable
    1 (by norm_num) shiftedSinusoidalHessianDiagonal q
      (fun i =>
        (differentiable_shiftedSinusoidalHessianDiagonal i).differentiableAt)

theorem measurable_shiftedSinusoidalSoftAbsHamiltonian (m c : ℝ) :
    Measurable (generalRelativisticHamiltonian shiftedSinusoidalPotential
      shiftedSinusoidalSoftAbsMetric m c) := by
  exact measurable_diagonalSoftAbs_generalRelativisticHamiltonian
    shiftedSinusoidalPotential measurable_shiftedSinusoidalPotential
    1 (by norm_num) shiftedSinusoidalHessianDiagonal
    measurable_shiftedSinusoidalHessianDiagonal m c

/-- The hyperbolic denominator has a uniform positive lower bound on the
actual Hessian range. -/
theorem exists_uniform_tanh_lower_shiftedSinusoidal :
    ∃ lower : ℝ, 0 < lower ∧ ∀ q : Position Unit,
      lower ≤ Real.tanh (shiftedSinusoidalHessianDiagonal q Unit.unit) := by
  have hcontinuous : Continuous Real.tanh := by
    rw [show Real.tanh = fun x => Real.sinh x / Real.cosh x by
      funext x; rw [Real.tanh_eq_sinh_div_cosh]]
    exact Real.continuous_sinh.div Real.continuous_cosh
      (fun x => ne_of_gt (Real.cosh_pos x))
  obtain ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.2 (by norm_num : (1 : ℝ) ≤ 3))
      hcontinuous.continuousOn
  refine ⟨Real.tanh x, real_tanh_pos (lt_of_lt_of_le (by norm_num) hx.1), ?_⟩
  intro q
  exact hmin (shiftedSinusoidalHessianDiagonal_mem_Icc q)

/-- Compact positive Hessian range gives global ellipticity for the practical
SoftAbs metric. -/
theorem exists_uniform_bounds_shiftedSinusoidalSoftAbsEigenvalue :
    ∃ lower upper : ℝ, 0 < lower ∧ lower ≤ upper ∧
      ∀ q : Position Unit,
        lower ≤ diagonalSoftAbsEigenvalue 1
          shiftedSinusoidalHessianDiagonal q Unit.unit ∧
        diagonalSoftAbsEigenvalue 1
          shiftedSinusoidalHessianDiagonal q Unit.unit ≤ upper := by
  have hc : Continuous (softAbs 1) := continuous_softAbs 1 (by norm_num)
  obtain ⟨xmin, hxmin, hmin⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.2 (by norm_num : (1 : ℝ) ≤ 3)) hc.continuousOn
  obtain ⟨xmax, hxmax, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.2 (by norm_num : (1 : ℝ) ≤ 3)) hc.continuousOn
  refine ⟨softAbs 1 xmin, softAbs 1 xmax,
    softAbs_pos 1 (by norm_num) xmin, hmin hxmax, ?_⟩
  intro q
  rw [diagonalSoftAbsEigenvalue]
  exact ⟨hmin (shiftedSinusoidalHessianDiagonal_mem_Icc q),
    hmax (shiftedSinusoidalHessianDiagonal_mem_Icc q)⟩

/-- Explicit derivative of real `tanh`, used to bound the nondegenerate
SoftAbs derivative on `[1,3]`. -/
theorem hasDerivAt_real_tanh_explicit (x : ℝ) :
    HasDerivAt Real.tanh ((Real.cosh x)⁻¹ ^ (2 : ℕ)) x := by
  have heq : Real.tanh = Real.sinh / Real.cosh := by
    funext y
    exact Real.tanh_eq_sinh_div_cosh y
  rw [heq]
  have hraw := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x)
    (ne_of_gt (Real.cosh_pos x))
  have hcoefficient :
      (Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) /
          Real.cosh x ^ 2 =
        (Real.cosh x)⁻¹ ^ (2 : ℕ) := by
    rw [inv_pow]
    field_simp [ne_of_gt (Real.cosh_pos x)]
    nlinarith [Real.cosh_sq_sub_sinh_sq x]
  rw [← hcoefficient]
  exact hraw

noncomputable def softAbsOneDerivativeAway (x : ℝ) : ℝ :=
  (Real.tanh x - x * ((Real.cosh x)⁻¹ ^ 2)) / (Real.tanh x) ^ 2

theorem deriv_softAbs_one_of_pos {x : ℝ} (hx : 0 < x) :
    deriv (softAbs 1) x = softAbsOneDerivativeAway x := by
  have hxne : x ≠ 0 := hx.ne'
  have htanh : Real.tanh x ≠ 0 := (real_tanh_pos hx).ne'
  have hevent : softAbs 1 =ᶠ[nhds x] id / Real.tanh := by
    filter_upwards [eventually_ne_nhds hxne] with y hy
    simp [softAbs, hy, id_eq]
  rw [hevent.deriv_eq]
  have hraw := (hasDerivAt_id x).div
    (hasDerivAt_real_tanh_explicit x) htanh
  rw [hraw.deriv]
  simp only [softAbsOneDerivativeAway, one_mul, id_eq]

theorem differentiableAt_softAbs_one_of_pos {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (softAbs 1) x := by
  have hxne : x ≠ 0 := hx.ne'
  have htanh : Real.tanh x ≠ 0 := (real_tanh_pos hx).ne'
  have hquot := (hasDerivAt_id x).div
    (hasDerivAt_real_tanh_explicit x) htanh
  apply (hquot.congr_of_eventuallyEq ?_).differentiableAt
  filter_upwards [eventually_ne_nhds hxne] with y hy
  simp [softAbs, hy, id_eq]

theorem continuous_softAbsOneDerivativeAway_on_Icc :
    ContinuousOn softAbsOneDerivativeAway (Set.Icc (1 : ℝ) 3) := by
  unfold softAbsOneDerivativeAway
  have htanh : Continuous Real.tanh := by
    rw [show Real.tanh = fun x => Real.sinh x / Real.cosh x by
      funext x; rw [Real.tanh_eq_sinh_div_cosh]]
    exact Real.continuous_sinh.div Real.continuous_cosh
      (fun x => ne_of_gt (Real.cosh_pos x))
  have hcoshInvSq : Continuous (fun x : ℝ => (Real.cosh x)⁻¹ ^ 2) := by
    exact (Real.continuous_cosh.inv₀
      (fun x => ne_of_gt (Real.cosh_pos x))).pow 2
  apply (htanh.continuousOn.sub
    (continuousOn_id.mul hcoshInvSq.continuousOn)).div
      (htanh.continuousOn.pow 2)
  intro x hx
  exact pow_ne_zero 2
    (real_tanh_pos (lt_of_lt_of_le (by norm_num) hx.1)).ne'

/-- On the actual Hessian range the SoftAbs derivative has a finite uniform
bound.  Keeping the witness existential avoids baking an arbitrary numerical
overestimate into clients. -/
theorem exists_uniform_deriv_bound_softAbs_one_Icc :
    ∃ C : NNReal, ∀ x ∈ Set.Icc (1 : ℝ) 3,
      ‖deriv (softAbs 1) x‖₊ ≤ C := by
  obtain ⟨xmax, hxmax, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.2 (by norm_num : (1 : ℝ) ≤ 3))
      continuous_softAbsOneDerivativeAway_on_Icc.abs
  let C : NNReal := ⟨|softAbsOneDerivativeAway xmax|, abs_nonneg _⟩
  refine ⟨C, ?_⟩
  intro x hx
  change ‖deriv (softAbs 1) x‖ ≤ |softAbsOneDerivativeAway xmax|
  rw [Real.norm_eq_abs,
    deriv_softAbs_one_of_pos (lt_of_lt_of_le (by norm_num) hx.1)]
  exact hmax hx

/-- The nondegenerate SoftAbs transform is Lipschitz on the full Hessian
range reached by the target. -/
theorem exists_lipschitzOn_softAbs_one_Icc :
    ∃ C : NNReal, LipschitzOnWith C (softAbs 1) (Set.Icc (1 : ℝ) 3) := by
  obtain ⟨C, hC⟩ := exists_uniform_deriv_bound_softAbs_one_Icc
  refine ⟨C, Convex.lipschitzOnWith_of_nnnorm_deriv_le ?_ hC
    (convex_Icc (1 : ℝ) 3)⟩
  intro x hx
  exact differentiableAt_softAbs_one_of_pos
    (lt_of_lt_of_le (by norm_num) hx.1)

/-- Consequently the actual scalar metric eigenvalue is globally Lipschitz as
a function of the scalar position. -/
theorem exists_lipschitz_shiftedSinusoidalSoftAbsEigenvalueReal :
    ∃ C : NNReal,
      LipschitzWith C (fun x : ℝ => softAbs 1 (2 + Real.sin x)) := by
  obtain ⟨C, hsoft⟩ := exists_lipschitzOn_softAbs_one_Icc
  have hhessian : LipschitzWith 1 (fun x : ℝ => 2 + Real.sin x) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      simpa only [NNReal.coe_one, one_mul, dist_add_left] using
        Real.lipschitzWith_sin.dist_le_mul x y
  have hmaps : Set.MapsTo (fun x : ℝ => 2 + Real.sin x) Set.univ
      (Set.Icc (1 : ℝ) 3) := by
    intro x _
    constructor
    · linarith [Real.neg_one_le_sin x]
    · linarith [Real.sin_le_one x]
  refine ⟨C, lipschitzOnWith_univ.mp ?_⟩
  change LipschitzOnWith C
    ((softAbs 1) ∘ fun x : ℝ => 2 + Real.sin x) Set.univ
  simpa only [mul_one] using hsoft.comp hhessian.lipschitzOnWith hmaps

/-- Inverse-square-root factor used by the diagonal SoftAbs Hamiltonian. -/
noncomputable def shiftedSinusoidalSoftAbsScaleReal (x : ℝ) : ℝ :=
  (Real.sqrt (softAbs 1 (2 + Real.sin x)))⁻¹

theorem shiftedSinusoidalSoftAbsScaleReal_pos (x : ℝ) :
    0 < shiftedSinusoidalSoftAbsScaleReal x := by
  unfold shiftedSinusoidalSoftAbsScaleReal
  exact inv_pos.2 (Real.sqrt_pos.2 (softAbs_pos 1 (by norm_num) _))

theorem differentiable_shiftedSinusoidalSoftAbsScaleReal :
    Differentiable ℝ shiftedSinusoidalSoftAbsScaleReal := by
  intro x
  unfold shiftedSinusoidalSoftAbsScaleReal
  have heigen : DifferentiableAt ℝ (fun y : ℝ =>
      softAbs 1 (2 + Real.sin y)) x :=
    by
      change DifferentiableAt ℝ
        ((softAbs 1) ∘ fun y : ℝ => 2 + Real.sin y) x
      exact (differentiableAt_softAbs_one_of_pos
        (show 0 < 2 + Real.sin x by
          linarith [Real.neg_one_le_sin x])).comp x
            (Real.differentiableAt_sin.const_add 2)
  have hsqrt : DifferentiableAt ℝ (fun y : ℝ =>
      Real.sqrt (softAbs 1 (2 + Real.sin y))) x :=
    heigen.sqrt (softAbs_pos 1 (by norm_num) _).ne'
  exact hsqrt.inv (ne_of_gt
    (Real.sqrt_pos.2 (softAbs_pos 1 (by norm_num) _)))

/-- Smooth positive-branch formula for the inverse square root of SoftAbs. -/
noncomputable def softAbsOneInverseSqrtAway (x : ℝ) : ℝ :=
  (Real.sqrt (x / Real.tanh x))⁻¹

theorem contDiffOn_softAbsOneInverseSqrtAway_Ioi :
    ContDiffOn ℝ 1 softAbsOneInverseSqrtAway (Set.Ioi 0) := by
  have htanh : ContDiff ℝ 1 Real.tanh := by
    rw [show Real.tanh = fun x => Real.sinh x / Real.cosh x by
      funext x; rw [Real.tanh_eq_sinh_div_cosh]]
    exact Real.contDiff_sinh.div Real.contDiff_cosh
      (fun x => ne_of_gt (Real.cosh_pos x))
  have hquot : ContDiffOn ℝ 1 (fun x : ℝ => x / Real.tanh x)
      (Set.Ioi 0) := by
    exact contDiffOn_id.div htanh.contDiffOn
      (fun x hx => (real_tanh_pos hx).ne')
  have hsqrt : ContDiffOn ℝ 1 (fun x : ℝ =>
      Real.sqrt (x / Real.tanh x)) (Set.Ioi 0) := by
    exact hquot.sqrt (fun x hx => ne_of_gt
      (div_pos hx (real_tanh_pos hx)))
  unfold softAbsOneInverseSqrtAway
  exact hsqrt.inv (fun x hx => ne_of_gt (Real.sqrt_pos.2
    (div_pos hx (real_tanh_pos hx))))

theorem softAbsOneInverseSqrtAway_eq (x : ℝ) (hx : 0 < x) :
    softAbsOneInverseSqrtAway x = (Real.sqrt (softAbs 1 x))⁻¹ := by
  simp [softAbsOneInverseSqrtAway, softAbs, hx.ne']

/-- The inverse-square-root outer transform is Lipschitz on the actual
positive Hessian range. -/
theorem exists_lipschitzOn_softAbsOneInverseSqrtAway_Icc :
    ∃ C : NNReal, LipschitzOnWith C softAbsOneInverseSqrtAway
      (Set.Icc (1 : ℝ) 3) := by
  have hcontinuous : ContinuousOn (fun x =>
      |deriv softAbsOneInverseSqrtAway x|) (Set.Icc (1 : ℝ) 3) :=
    ((contDiffOn_softAbsOneInverseSqrtAway_Ioi.continuousOn_deriv_of_isOpen
      isOpen_Ioi (by norm_num)).mono (fun x hx => by
        exact lt_of_lt_of_le (by norm_num) hx.1)).abs
  obtain ⟨xmax, hxmax, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.2 (by norm_num : (1 : ℝ) ≤ 3)) hcontinuous
  let C : NNReal := ⟨|deriv softAbsOneInverseSqrtAway xmax|, abs_nonneg _⟩
  refine ⟨C, Convex.lipschitzOnWith_of_nnnorm_deriv_le ?_ ?_
    (convex_Icc (1 : ℝ) 3)⟩
  · intro x hx
    exact (contDiffOn_softAbsOneInverseSqrtAway_Ioi.differentiableOn
      (by norm_num)).differentiableAt
        (Ioi_mem_nhds (lt_of_lt_of_le (by norm_num) hx.1))
  · intro x hx
    change ‖deriv softAbsOneInverseSqrtAway x‖ ≤
      |deriv softAbsOneInverseSqrtAway xmax|
    rw [Real.norm_eq_abs]
    exact hmax hx

/-- The actual inverse-square-root SoftAbs factor is globally Lipschitz, and
its ordinary derivative obeys the same uniform bound. -/
theorem exists_lipschitz_shiftedSinusoidalSoftAbsScaleReal :
    ∃ L : NNReal,
      LipschitzWith L shiftedSinusoidalSoftAbsScaleReal ∧
      ∀ x, |deriv shiftedSinusoidalSoftAbsScaleReal x| ≤ L := by
  obtain ⟨L, houter⟩ :=
    exists_lipschitzOn_softAbsOneInverseSqrtAway_Icc
  have hhessian : LipschitzWith 1 (fun x : ℝ => 2 + Real.sin x) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      simpa only [NNReal.coe_one, one_mul, dist_add_left] using
        Real.lipschitzWith_sin.dist_le_mul x y
  have hmaps : Set.MapsTo (fun x : ℝ => 2 + Real.sin x) Set.univ
      (Set.Icc (1 : ℝ) 3) := by
    intro x _
    constructor
    · linarith [Real.neg_one_le_sin x]
    · linarith [Real.sin_le_one x]
  have hcomp : LipschitzWith L
      (softAbsOneInverseSqrtAway ∘ fun x : ℝ => 2 + Real.sin x) := by
    rw [← lipschitzOnWith_univ]
    simpa only [mul_one] using
      houter.comp hhessian.lipschitzOnWith hmaps
  have heq :
      (softAbsOneInverseSqrtAway ∘ fun x : ℝ => 2 + Real.sin x) =
        shiftedSinusoidalSoftAbsScaleReal := by
    funext x
    exact softAbsOneInverseSqrtAway_eq _
      (by linarith [Real.neg_one_le_sin x])
  rw [heq] at hcomp
  refine ⟨L, hcomp, ?_⟩
  intro x
  simpa [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz
    (x₀ := x) hcomp

/-- The factor derivative used in the scalar Hamiltonian callback. -/
noncomputable def shiftedSinusoidalSoftAbsScaleDerivativeReal (x : ℝ) : ℝ :=
  deriv shiftedSinusoidalSoftAbsScaleReal x

/-- Position-only portion of the complete `m=c=1` SoftAbs Hamiltonian. -/
noncomputable def shiftedSinusoidalSoftAbsBaseReal (x : ℝ) : ℝ :=
  x ^ 2 - Real.sin x +
    (1 / 2 : ℝ) * Real.log (softAbs 1 (2 + Real.sin x))

theorem differentiable_shiftedSinusoidalSoftAbsBaseReal :
    Differentiable ℝ shiftedSinusoidalSoftAbsBaseReal := by
  intro x
  unfold shiftedSinusoidalSoftAbsBaseReal
  have heigen : DifferentiableAt ℝ (fun y : ℝ =>
      softAbs 1 (2 + Real.sin y)) x := by
    change DifferentiableAt ℝ
      ((softAbs 1) ∘ fun y : ℝ => 2 + Real.sin y) x
    exact (differentiableAt_softAbs_one_of_pos
      (by linarith [Real.neg_one_le_sin x])).comp x
        (Real.differentiableAt_sin.const_add 2)
  exact ((by fun_prop : DifferentiableAt ℝ
    (fun y : ℝ => y ^ 2 - Real.sin y) x)).add
      ((heigen.log (softAbs_pos 1 (by norm_num) _).ne').const_mul (1 / 2))

theorem generalRelativisticHamiltonian_shiftedSinusoidalSoftAbs_eq_real
    (q p : ℝ) :
    generalRelativisticHamiltonian shiftedSinusoidalPotential
      shiftedSinusoidalSoftAbsMetric 1 1
      ((fun _ => q), (fun _ => p)) =
      scalarGRHamiltonianReal shiftedSinusoidalSoftAbsBaseReal
        shiftedSinusoidalSoftAbsScaleReal (q, p) := by
  unfold generalRelativisticHamiltonian
    riemannianRelativisticKineticEnergy relativisticKineticEnergy
    shiftedSinusoidalPotential shiftedSinusoidalSoftAbsMetric
    shiftedSinusoidalSoftAbsBaseReal scalarGRHamiltonianReal
    shiftedSinusoidalSoftAbsScaleReal squaredEuclideanNorm euclideanInner
    diagonalSoftAbsMetric
  simp only [Finset.univ_unique, Finset.sum_singleton, one_mul, one_pow,
    diagonalSoftAbsFactor_apply, diagonalSoftAbsEigenvalue,
    shiftedSinusoidalHessianDiagonal]
  ring_nf

noncomputable def shiftedSinusoidalSoftAbsPositionDerivative :
    PhaseSpace Unit → Position Unit :=
  scalarGRPositionCallbackUnit
    (deriv shiftedSinusoidalSoftAbsBaseReal)
    shiftedSinusoidalSoftAbsScaleReal
    shiftedSinusoidalSoftAbsScaleDerivativeReal

noncomputable def shiftedSinusoidalSoftAbsMomentumDerivative :
    PhaseSpace Unit → Momentum Unit :=
  scalarGRMomentumCallbackUnit shiftedSinusoidalSoftAbsScaleReal

/-- The callbacks passed to the implicit solver are the actual two coordinate
derivatives of the complete nonconstant SoftAbs Hamiltonian. -/
theorem shiftedSinusoidalSoftAbsDerivative_callbacks_correct
    (z : PhaseSpace Unit) :
    deriv (fun q => generalRelativisticHamiltonian shiftedSinusoidalPotential
      shiftedSinusoidalSoftAbsMetric 1 1 ((fun _ => q), z.2))
        (z.1 Unit.unit) =
      shiftedSinusoidalSoftAbsPositionDerivative z Unit.unit ∧
    deriv (fun p => generalRelativisticHamiltonian shiftedSinusoidalPotential
      shiftedSinusoidalSoftAbsMetric 1 1 (z.1, (fun _ => p)))
        (z.2 Unit.unit) =
      shiftedSinusoidalSoftAbsMomentumDerivative z Unit.unit := by
  constructor
  · rw [show (fun q => generalRelativisticHamiltonian
        shiftedSinusoidalPotential shiftedSinusoidalSoftAbsMetric
        1 1 ((fun _ => q), z.2)) =
      fun q => scalarGRHamiltonianReal shiftedSinusoidalSoftAbsBaseReal
        shiftedSinusoidalSoftAbsScaleReal (q, z.2 Unit.unit) by
      funext q
      exact generalRelativisticHamiltonian_shiftedSinusoidalSoftAbs_eq_real
        q (z.2 Unit.unit)]
    change deriv _ _ = scalarGRPositionCallback
      (deriv shiftedSinusoidalSoftAbsBaseReal)
      shiftedSinusoidalSoftAbsScaleReal
      (deriv shiftedSinusoidalSoftAbsScaleReal)
      (z.1 Unit.unit, z.2 Unit.unit)
    exact deriv_scalarGRHamiltonianReal_fst
      shiftedSinusoidalSoftAbsBaseReal shiftedSinusoidalSoftAbsScaleReal
      differentiable_shiftedSinusoidalSoftAbsBaseReal
      differentiable_shiftedSinusoidalSoftAbsScaleReal
      shiftedSinusoidalSoftAbsScaleReal_pos _ _
  · rw [show (fun p => generalRelativisticHamiltonian
        shiftedSinusoidalPotential shiftedSinusoidalSoftAbsMetric
        1 1 (z.1, (fun _ => p))) =
      fun p => scalarGRHamiltonianReal shiftedSinusoidalSoftAbsBaseReal
        shiftedSinusoidalSoftAbsScaleReal (z.1 Unit.unit, p) by
      funext p
      exact generalRelativisticHamiltonian_shiftedSinusoidalSoftAbs_eq_real
        (z.1 Unit.unit) p]
    change deriv _ _ = scalarGRMomentumCallback
      shiftedSinusoidalSoftAbsScaleReal
      (z.1 Unit.unit, z.2 Unit.unit)
    exact deriv_scalarGRHamiltonianReal_snd
      shiftedSinusoidalSoftAbsBaseReal shiftedSinusoidalSoftAbsScaleReal _ _

/-- Both slice bounds needed by the generic implicit solver are available
with one finite factor constant.  The position-only drift is deliberately
arbitrary because it cancels in the first fixed-point comparison. -/
theorem exists_shiftedSinusoidalSoftAbs_slice_bounds (drift : ℝ → ℝ) :
    ∃ L : NNReal,
      (∀ q, LipschitzWith (3 * L) (fun p =>
        scalarGRPositionCallbackUnit drift
          shiftedSinusoidalSoftAbsScaleReal
          shiftedSinusoidalSoftAbsScaleDerivativeReal (q, p))) ∧
      (∀ p, LipschitzWith (2 * L) (fun q =>
        scalarGRMomentumCallbackUnit shiftedSinusoidalSoftAbsScaleReal
          (q, p))) := by
  obtain ⟨L, hlip, hderiv⟩ :=
    exists_lipschitz_shiftedSinusoidalSoftAbsScaleReal
  refine ⟨L, ?_, ?_⟩
  · intro q
    exact scalarGRPositionCallbackUnit_lipschitz_momentum
      drift shiftedSinusoidalSoftAbsScaleReal
      shiftedSinusoidalSoftAbsScaleDerivativeReal q L
      (shiftedSinusoidalSoftAbsScaleReal_pos _) (hderiv _)
  · intro p
    exact scalarGRMomentumCallbackUnit_lipschitz_position
      shiftedSinusoidalSoftAbsScaleReal p L hlip

noncomputable def shiftedSinusoidalSoftAbsScaleLipschitzConstant : NNReal :=
  Classical.choose exists_lipschitz_shiftedSinusoidalSoftAbsScaleReal

theorem shiftedSinusoidalSoftAbsScaleReal_lipschitz :
    LipschitzWith shiftedSinusoidalSoftAbsScaleLipschitzConstant
      shiftedSinusoidalSoftAbsScaleReal :=
  (Classical.choose_spec
    exists_lipschitz_shiftedSinusoidalSoftAbsScaleReal).1

theorem shiftedSinusoidalSoftAbsScaleDerivativeReal_bound (x : ℝ) :
    |shiftedSinusoidalSoftAbsScaleDerivativeReal x| ≤
      shiftedSinusoidalSoftAbsScaleLipschitzConstant := by
  exact (Classical.choose_spec
    exists_lipschitz_shiftedSinusoidalSoftAbsScaleReal).2 x

/-- Exact Banach-selected generalized-leapfrog solver for the nonconstant
SoftAbs scalar callbacks. The only remaining client choice is the
position-only drift and a step satisfying the two displayed bounds. -/
noncomputable def shiftedSinusoidalSoftAbsContractiveSolverAt
    (drift : ℝ → ℝ) (ε : ℝ)
    (hpositionStep : |ε / 2| *
      (3 * shiftedSinusoidalSoftAbsScaleLipschitzConstant) < 1)
    (hmomentumStep : |ε / 2| *
      (2 * shiftedSinusoidalSoftAbsScaleLipschitzConstant) < 1) :
    ContractiveGeneralizedLeapfrogSolverAt
      (scalarGRPositionCallbackUnit drift
        shiftedSinusoidalSoftAbsScaleReal
        shiftedSinusoidalSoftAbsScaleDerivativeReal)
      (scalarGRMomentumCallbackUnit shiftedSinusoidalSoftAbsScaleReal) ε := by
  apply contractiveGeneralizedLeapfrogSolverAtOfLipschitz
    _ _ ε
    (3 * shiftedSinusoidalSoftAbsScaleLipschitzConstant)
    (2 * shiftedSinusoidalSoftAbsScaleLipschitzConstant)
  · intro q
    exact scalarGRPositionCallbackUnit_lipschitz_momentum
      drift shiftedSinusoidalSoftAbsScaleReal
      shiftedSinusoidalSoftAbsScaleDerivativeReal q
      shiftedSinusoidalSoftAbsScaleLipschitzConstant
      (shiftedSinusoidalSoftAbsScaleReal_pos _)
      (shiftedSinusoidalSoftAbsScaleDerivativeReal_bound _)
  · intro p
    exact scalarGRMomentumCallbackUnit_lipschitz_position
      shiftedSinusoidalSoftAbsScaleReal p
      shiftedSinusoidalSoftAbsScaleLipschitzConstant
      shiftedSinusoidalSoftAbsScaleReal_lipschitz
  · exact hpositionStep
  · exact hmomentumStep

/-- The solver specialized to the callbacks just proved equal to the complete
SoftAbs Hamiltonian derivatives. -/
noncomputable def shiftedSinusoidalSoftAbsHamiltonianSolverAt
    (ε : ℝ)
    (hpositionStep : |ε / 2| *
      (3 * shiftedSinusoidalSoftAbsScaleLipschitzConstant) < 1)
    (hmomentumStep : |ε / 2| *
      (2 * shiftedSinusoidalSoftAbsScaleLipschitzConstant) < 1) :
    ContractiveGeneralizedLeapfrogSolverAt
      shiftedSinusoidalSoftAbsPositionDerivative
      shiftedSinusoidalSoftAbsMomentumDerivative ε := by
  exact shiftedSinusoidalSoftAbsContractiveSolverAt
    (deriv shiftedSinusoidalSoftAbsBaseReal) ε
      hpositionStep hmomentumStep

/-- The admissible step regime is nonvacuous: it contains an explicit
strictly positive step for whatever finite compactness witness was selected. -/
theorem exists_nonzero_shiftedSinusoidalSoftAbs_step :
    ∃ ε : ℝ, ε ≠ 0 ∧
      |ε / 2| * (3 * shiftedSinusoidalSoftAbsScaleLipschitzConstant) < 1 ∧
      |ε / 2| * (2 * shiftedSinusoidalSoftAbsScaleLipschitzConstant) < 1 := by
  let L : ℝ := shiftedSinusoidalSoftAbsScaleLipschitzConstant
  let ε : ℝ := 1 / (6 * (L + 1))
  have hL : 0 ≤ L := NNReal.zero_le_coe
  have hden : 0 < 6 * (L + 1) := mul_pos (by norm_num) (by linarith)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  refine ⟨ε, hε.ne', ?_, ?_⟩
  · rw [abs_of_pos (div_pos hε (by norm_num))]
    change ε / 2 * (3 * L) < 1
    dsimp [ε]
    rw [show 1 / (6 * (L + 1)) / 2 * (3 * L) =
      (3 * L) / (12 * (L + 1)) by
        field_simp [ne_of_gt (by linarith : 0 < L + 1)]; ring]
    rw [div_lt_iff₀ (mul_pos (by norm_num) (by linarith : 0 < L + 1))]
    nlinarith
  · rw [abs_of_pos (div_pos hε (by norm_num))]
    change ε / 2 * (2 * L) < 1
    dsimp [ε]
    rw [show 1 / (6 * (L + 1)) / 2 * (2 * L) =
      (2 * L) / (12 * (L + 1)) by
        field_simp [ne_of_gt (by linarith : 0 < L + 1)]; ring]
    rw [div_lt_iff₀ (mul_pos (by norm_num) (by linarith : 0 < L + 1))]
    nlinarith

noncomputable def shiftedSinusoidalSoftAbsCertifiedStep : ℝ :=
  Classical.choose exists_nonzero_shiftedSinusoidalSoftAbs_step

theorem shiftedSinusoidalSoftAbsCertifiedStep_ne_zero :
    shiftedSinusoidalSoftAbsCertifiedStep ≠ 0 :=
  (Classical.choose_spec exists_nonzero_shiftedSinusoidalSoftAbs_step).1

theorem shiftedSinusoidalSoftAbsCertifiedStep_position_bound :
    |shiftedSinusoidalSoftAbsCertifiedStep / 2| *
      (3 * shiftedSinusoidalSoftAbsScaleLipschitzConstant) < 1 :=
  (Classical.choose_spec exists_nonzero_shiftedSinusoidalSoftAbs_step).2.1

theorem shiftedSinusoidalSoftAbsCertifiedStep_momentum_bound :
    |shiftedSinusoidalSoftAbsCertifiedStep / 2| *
      (2 * shiftedSinusoidalSoftAbsScaleLipschitzConstant) < 1 :=
  (Classical.choose_spec exists_nonzero_shiftedSinusoidalSoftAbs_step).2.2

/-- A concrete nonzero-step exact solver, requiring no client-supplied
analytic premise. -/
noncomputable abbrev shiftedSinusoidalSoftAbsCertifiedSolver :
    ContractiveGeneralizedLeapfrogSolverAt
      shiftedSinusoidalSoftAbsPositionDerivative
      shiftedSinusoidalSoftAbsMomentumDerivative
      shiftedSinusoidalSoftAbsCertifiedStep :=
  shiftedSinusoidalSoftAbsHamiltonianSolverAt
    shiftedSinusoidalSoftAbsCertifiedStep
    shiftedSinusoidalSoftAbsCertifiedStep_position_bound
    shiftedSinusoidalSoftAbsCertifiedStep_momentum_bound

noncomputable abbrev shiftedSinusoidalSoftAbsCertifiedBackwardSolver :
    ContractiveGeneralizedLeapfrogSolverAt
      shiftedSinusoidalSoftAbsPositionDerivative
      shiftedSinusoidalSoftAbsMomentumDerivative
      (-shiftedSinusoidalSoftAbsCertifiedStep) :=
  shiftedSinusoidalSoftAbsHamiltonianSolverAt
    (-shiftedSinusoidalSoftAbsCertifiedStep)
    (by simpa [neg_div] using
      shiftedSinusoidalSoftAbsCertifiedStep_position_bound)
    (by simpa [neg_div] using
      shiftedSinusoidalSoftAbsCertifiedStep_momentum_bound)

/-- The certified negative-step solve is the exact inverse of the certified
positive-step solve. -/
theorem shiftedSinusoidalSoftAbsCertifiedSolver_inverse
    (z : PhaseSpace Unit) :
    shiftedSinusoidalSoftAbsCertifiedBackwardSolver.step
      (shiftedSinusoidalSoftAbsCertifiedSolver.step z) = z :=
  ContractiveGeneralizedLeapfrogSolverAt.step_neg_step
    shiftedSinusoidalSoftAbsCertifiedSolver
    shiftedSinusoidalSoftAbsCertifiedBackwardSolver z

end Mcmc.Relativistic
