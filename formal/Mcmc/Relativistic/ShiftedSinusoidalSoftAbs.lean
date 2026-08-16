import Mcmc.Relativistic.SoftAbs

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

end Mcmc.Relativistic
