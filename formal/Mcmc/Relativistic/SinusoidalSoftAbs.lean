import Mcmc.Relativistic.SoftAbs

/-!
# A nonconstant diagonal-SoftAbs target

This module supplies a concrete position-dependent target for the Xu--Ge
solver milestone. In one dimension the potential

`U(q) = q² / 2 - sin(q)`

has force `q - cos(q)` and Hessian diagonal `1 + sin(q)`. The Hessian reaches
the removable SoftAbs branch at `q = -π/2` and equals one at `q = 0`, so its
SoftAbs metric is genuinely nonconstant. No implicit-solver claim is made here;
that requires a separate nonzero-step contraction and volume certificate.
-/

namespace Mcmc.Relativistic

open Mcmc.Hamiltonian

/-- Gaussian potential with a bounded sinusoidal perturbation. -/
noncomputable def sinusoidalSoftAbsPotential (q : Position Unit) : ℝ :=
  (q Unit.unit) ^ 2 / 2 - Real.sin (q Unit.unit)

/-- Exact force of `sinusoidalSoftAbsPotential`. -/
noncomputable def sinusoidalSoftAbsGradient (q : Position Unit) : Momentum Unit :=
  fun _ => q Unit.unit - Real.cos (q Unit.unit)

/-- Exact one-dimensional Hessian diagonal. -/
noncomputable def sinusoidalHessianDiagonal
    (q : Position Unit) (_ : Unit) : ℝ :=
  1 + Real.sin (q Unit.unit)

theorem measurable_sinusoidalSoftAbsPotential :
    Measurable sinusoidalSoftAbsPotential := by
  unfold sinusoidalSoftAbsPotential
  fun_prop

theorem measurable_sinusoidalSoftAbsGradient :
    Measurable sinusoidalSoftAbsGradient := by
  unfold sinusoidalSoftAbsGradient
  fun_prop

theorem measurable_sinusoidalHessianDiagonal (i : Unit) :
    Measurable fun q : Position Unit => sinusoidalHessianDiagonal q i := by
  unfold sinusoidalHessianDiagonal
  fun_prop

theorem differentiable_sinusoidalHessianDiagonal (i : Unit) :
    Differentiable ℝ (fun q : Position Unit =>
      sinusoidalHessianDiagonal q i) := by
  unfold sinusoidalHessianDiagonal
  fun_prop

/-- Scalar force derivative, used to certify that the metric callback is the
actual Hessian rather than an unrelated positive field. -/
theorem hasDerivAt_sinusoidalForce (x : ℝ) :
    HasDerivAt (fun y : ℝ => y - Real.cos y) (1 + Real.sin x) x := by
  change HasDerivAt (id - Real.cos) (1 + Real.sin x) x
  simpa only [sub_neg_eq_add] using
    (hasDerivAt_id x).sub (Real.hasDerivAt_cos x)

theorem sinusoidalHessianDiagonal_eq_deriv_force
    (q : Position Unit) :
    sinusoidalHessianDiagonal q Unit.unit =
      deriv (fun x : ℝ => x - Real.cos x) (q Unit.unit) := by
  rw [(hasDerivAt_sinusoidalForce (q Unit.unit)).deriv]
  rfl

/-- Coordinate form required by the diagonal-SoftAbs Hamiltonian API: the
supplied Hessian diagonal is the Fréchet derivative of the actual force
component in its coordinate direction. -/
theorem sinusoidalHessianDiagonal_eq_fderiv_gradient
    (q : Position Unit) :
    sinusoidalHessianDiagonal q Unit.unit =
      fderiv ℝ (fun r : Position Unit =>
        sinusoidalSoftAbsGradient r Unit.unit) q
        (Pi.single Unit.unit 1) := by
  have hcomp := (hasDerivAt_sinusoidalForce
    (q Unit.unit)).comp_hasFDerivAt q
      (hasFDerivAt_apply (𝕜 := ℝ) Unit.unit q)
  have hf := congrArg
    (fun L : Position Unit →L[ℝ] ℝ => L (Pi.single Unit.unit 1))
    hcomp.fderiv
  have heq :
      ((fun y : ℝ => y - Real.cos y) ∘ fun r : Position Unit => r Unit.unit) =
        (fun r : Position Unit => r Unit.unit - Real.cos (r Unit.unit)) := rfl
  rw [heq] at hf
  simpa [sinusoidalSoftAbsGradient, sinusoidalHessianDiagonal] using hf.symm

theorem sinusoidalHessianDiagonal_nonneg (q : Position Unit) :
    0 ≤ sinusoidalHessianDiagonal q Unit.unit := by
  unfold sinusoidalHessianDiagonal
  linarith [Real.neg_one_le_sin (q Unit.unit)]

@[simp] theorem sinusoidalHessianDiagonal_neg_pi_div_two :
    sinusoidalHessianDiagonal (fun _ => -(Real.pi / 2)) Unit.unit = 0 := by
  simp [sinusoidalHessianDiagonal, Real.sin_neg, Real.sin_pi_div_two]

@[simp] theorem sinusoidalHessianDiagonal_zero :
    sinusoidalHessianDiagonal (fun _ => 0) Unit.unit = 1 := by
  simp [sinusoidalHessianDiagonal]

/-- The concrete position-dependent SoftAbs metric, with smoothing `α=1`. -/
noncomputable abbrev sinusoidalSoftAbsMetric : FactoredRiemannianMetric Unit :=
  diagonalSoftAbsMetric 1 (by norm_num) sinusoidalHessianDiagonal

/-- The concrete target supplies all metric-derivative data required by the
paper's Equation (12), including at its zero Hessian location. -/
noncomputable def sinusoidalSoftAbsEquation12Certificate
    (q : Position Unit) :
    sinusoidalSoftAbsMetric.Equation12Certificate q :=
  diagonalSoftAbsMetricEquation12CertificateOfDifferentiable
    1 (by norm_num) sinusoidalHessianDiagonal q
      (fun i => (differentiable_sinusoidalHessianDiagonal i).differentiableAt)

theorem measurable_sinusoidalSoftAbsHamiltonian (m c : ℝ) :
    Measurable (generalRelativisticHamiltonian sinusoidalSoftAbsPotential
      sinusoidalSoftAbsMetric m c) := by
  exact measurable_diagonalSoftAbs_generalRelativisticHamiltonian
    sinusoidalSoftAbsPotential measurable_sinusoidalSoftAbsPotential
    1 (by norm_num) sinusoidalHessianDiagonal
    measurable_sinusoidalHessianDiagonal m c

@[simp] theorem sinusoidalSoftAbsEigenvalue_neg_pi_div_two :
    diagonalSoftAbsEigenvalue 1 sinusoidalHessianDiagonal
      (fun _ => -(Real.pi / 2)) Unit.unit = 1 := by
  simp [diagonalSoftAbsEigenvalue, softAbs]

theorem sinusoidalSoftAbsEigenvalue_zero_gt_one :
    1 < diagonalSoftAbsEigenvalue 1 sinusoidalHessianDiagonal
      (fun _ => 0) Unit.unit := by
  rw [diagonalSoftAbsEigenvalue, sinusoidalHessianDiagonal_zero]
  simp only [softAbs, one_ne_zero, if_false, one_mul, one_div]
  rw [one_lt_inv₀ (real_tanh_pos (by norm_num))]
  exact Real.tanh_lt_one 1

/-- The SoftAbs eigenvalue field, and hence the diagonal metric, is genuinely
position dependent. -/
theorem sinusoidalSoftAbsEigenvalue_nonconstant :
    diagonalSoftAbsEigenvalue 1 sinusoidalHessianDiagonal
        (fun _ => -(Real.pi / 2)) Unit.unit ≠
      diagonalSoftAbsEigenvalue 1 sinusoidalHessianDiagonal
        (fun _ => 0) Unit.unit := by
  rw [sinusoidalSoftAbsEigenvalue_neg_pi_div_two]
  exact ne_of_lt sinusoidalSoftAbsEigenvalue_zero_gt_one

end Mcmc.Relativistic
