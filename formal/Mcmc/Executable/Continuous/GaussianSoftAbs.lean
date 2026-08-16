import Mcmc.Executable.Continuous.SeparableGeneralizedLeapfrog
import Mcmc.Relativistic.SoftAbsKernel
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Executable Gaussian diagonal-SoftAbs GR-HMC client

The standard Gaussian potential has constant Hessian diagonal `1`. Applying
SoftAbs therefore gives a genuine, non-identity diagonal SoftAbs metric that
is constant in position. The generalized implicit equations collapse to the
explicit separable metric leapfrog, whose measurability, uniqueness,
reversibility, and exact phase-volume preservation are already certified.
-/

namespace Mcmc.Executable.Continuous

open Mcmc.Hamiltonian Mcmc.Kernel Mcmc.Relativistic MeasureTheory
  ProbabilityTheory

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- Standard centered Gaussian potential, up to its normalization constant. -/
noncomputable def gaussianSoftAbsPotential (q : Position ι) : ℝ :=
  (1 / 2 : ℝ) * squaredEuclideanNorm q

/-- Its exact Hessian diagonal. -/
def gaussianHessianDiagonal (_q : Position ι) (_i : ι) : ℝ := 1

omit [Nonempty ι] [DecidableEq ι] in
theorem measurable_gaussianSoftAbsPotential :
    Measurable (gaussianSoftAbsPotential : Position ι → ℝ) := by
  exact (continuous_const.mul continuous_squaredEuclideanNorm).measurable

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] in
theorem measurable_gaussianHessianDiagonal (i : ι) :
    Measurable fun q : Position ι => gaussianHessianDiagonal q i :=
  measurable_const

/-- The concrete Gaussian SoftAbs metric (`α=1`). -/
noncomputable abbrev gaussianSoftAbsMetric : FactoredRiemannianMetric ι :=
  diagonalSoftAbsMetric 1 (by norm_num) gaussianHessianDiagonal

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] in
theorem gaussianSoftAbsEigenvalue_gt_one (q : Position ι) (i : ι) :
    1 < diagonalSoftAbsEigenvalue 1 gaussianHessianDiagonal q i := by
  change 1 < softAbs 1 1
  simp only [softAbs, one_ne_zero, if_false, one_mul, one_div]
  rw [one_lt_inv₀ (real_tanh_pos (by norm_num))]
  exact Real.tanh_lt_one 1

/-- A simple rational upper bound for the concrete SoftAbs eigenvalue. -/
theorem softAbs_one_one_lt_two : softAbs 1 1 < 2 := by
  have he : 2 < Real.exp 1 := Real.exp_one_gt_two
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have he2 : 3 < (Real.exp 1) ^ 2 := by nlinarith
  have hinv : 3 * (Real.exp 1)⁻¹ < Real.exp 1 := by
    rw [← div_eq_mul_inv, div_lt_iff₀ he0]
    nlinarith
  have htanh : (1 / 2 : ℝ) < Real.tanh 1 := by
    rw [Real.tanh_eq, Real.exp_neg]
    rw [lt_div_iff₀]
    · linarith
    · positivity
  simp only [softAbs, one_ne_zero, if_false, one_mul, one_div]
  rw [inv_lt_iff_one_lt_mul₀ (real_tanh_pos (by norm_num))]
  linarith

/-- Relativistic velocity for the constant Gaussian SoftAbs metric. -/
noncomputable def gaussianSoftAbsVelocity (p : Momentum ι) : Position ι :=
  riemannianRelativisticVelocity gaussianSoftAbsMetric 1 1 0 p

omit [Nonempty ι] [DecidableEq ι] in
theorem gaussianSoftAbsVelocity_eq (q : Position ι) (p : Momentum ι) :
    riemannianRelativisticVelocity gaussianSoftAbsMetric 1 1 q p =
      gaussianSoftAbsVelocity p := by
  rfl

omit [Nonempty ι] [DecidableEq ι] in
theorem measurable_gaussianSoftAbsVelocity :
    Measurable (gaussianSoftAbsVelocity : Momentum ι → Position ι) := by
  unfold gaussianSoftAbsVelocity riemannianRelativisticVelocity
    generalRelativisticVelocity generalRelativisticMass relativisticMass
    gaussianSoftAbsMetric gaussianHessianDiagonal diagonalSoftAbsMetric
    diagonalSoftAbsFactor diagonalSoftAbsInverseMetric diagonalMomentumMap
    squaredEuclideanNorm euclideanInner
  fun_prop

omit [Nonempty ι] [DecidableEq ι] in
theorem gaussianSoftAbsVelocity_odd (p : Momentum ι) :
    gaussianSoftAbsVelocity (-p) = -gaussianSoftAbsVelocity p := by
  unfold gaussianSoftAbsVelocity riemannianRelativisticVelocity
    generalRelativisticVelocity generalRelativisticMass
  have hfactor :
      (gaussianSoftAbsMetric.factor (0 : Position ι)).toLinearMap (-p) =
        -(gaussianSoftAbsMetric.factor (0 : Position ι)).toLinearMap p := by
    exact map_neg _ p
  have hinverse : gaussianSoftAbsMetric.inverseMetric (0 : Position ι) (-p) =
      -gaussianSoftAbsMetric.inverseMetric (0 : Position ι) p := by
    exact map_neg _ p
  rw [hfactor, relativisticMass_neg, hinverse]
  module

omit [Nonempty ι] [DecidableEq ι] in
/-- The Gaussian SoftAbs inverse metric is injective. -/
theorem gaussianSoftAbsInverseMetric_ne_zero {p : Momentum ι} (hp : p ≠ 0) :
    (gaussianSoftAbsMetric (ι := ι)).inverseMetric 0 p ≠ 0 := by
  intro hzero
  apply hp
  funext i
  have hi := congrFun hzero i
  change (diagonalSoftAbsEigenvalue 1 gaussianHessianDiagonal 0 i)⁻¹ * p i =
    0 at hi
  exact (mul_eq_zero.mp hi).resolve_left
    (inv_ne_zero (ne_of_gt
      (diagonalSoftAbsEigenvalue_pos 1 (by norm_num)
        gaussianHessianDiagonal 0 i)))

omit [Nonempty ι] [DecidableEq ι] in
/-- A nonzero momentum is also nonzero after applying the SoftAbs inverse-
square-root factor. -/
theorem gaussianSoftAbsFactor_ne_zero {p : Momentum ι} (hp : p ≠ 0) :
    (gaussianSoftAbsMetric (ι := ι)).factor 0 p ≠ 0 := by
  intro hmap
  apply hp
  apply ((gaussianSoftAbsMetric (ι := ι)).factor 0).injective
  simpa using hmap

omit [Nonempty ι] [DecidableEq ι] in
/-- Relativistic drift has nonzero velocity at every nonzero momentum for the
Gaussian SoftAbs metric. -/
theorem gaussianSoftAbsVelocity_ne_zero {p : Momentum ι} (hp : p ≠ 0) :
    gaussianSoftAbsVelocity p ≠ 0 := by
  unfold gaussianSoftAbsVelocity riemannianRelativisticVelocity
    generalRelativisticVelocity
  exact smul_ne_zero
    (inv_ne_zero (ne_of_gt (generalRelativisticMass_pos 1 1
      ((gaussianSoftAbsMetric (ι := ι)).factor 0).toLinearMap p
      (by norm_num) (by norm_num))))
    (gaussianSoftAbsInverseMetric_ne_zero hp)

omit [Nonempty ι] [DecidableEq ι] in
/-- Correct anisotropic speed bound specialized to the concrete constant
Gaussian SoftAbs metric. -/
theorem euclideanNorm_gaussianSoftAbsVelocity_lt {p : Momentum ι}
    (hp : p ≠ 0) :
    euclideanNorm (gaussianSoftAbsVelocity p) <
      euclideanNorm
          ((gaussianSoftAbsMetric (ι := ι)).inverseMetric 0 p) /
        euclideanNorm ((gaussianSoftAbsMetric (ι := ι)).factor 0 p) := by
  simpa [gaussianSoftAbsVelocity] using
    (euclideanNorm_riemannianRelativisticVelocity_lt
      (gaussianSoftAbsMetric (ι := ι)) 1 1 0 p (by norm_num) (by norm_num)
        (gaussianSoftAbsFactor_ne_zero hp)
        (gaussianSoftAbsInverseMetric_ne_zero hp))

omit [Nonempty ι] [DecidableEq ι] in
/-- Gaussian SoftAbs relativistic velocity is aligned nonnegatively with its
momentum. This is the directional fact needed to turn the half force kick into
inward position drift. -/
theorem gaussianSoftAbs_inner_velocity_nonneg (p : Momentum ι) :
    0 ≤ euclideanInner p (gaussianSoftAbsVelocity p) := by
  unfold gaussianSoftAbsVelocity riemannianRelativisticVelocity
    generalRelativisticVelocity euclideanInner
  apply Finset.sum_nonneg
  intro i _hi
  change 0 ≤ p i *
    ((generalRelativisticMass 1 1
      ((gaussianSoftAbsMetric (ι := ι)).factor 0).toLinearMap p)⁻¹ *
        ((diagonalSoftAbsEigenvalue 1 gaussianHessianDiagonal 0 i)⁻¹ * p i))
  have hmass : 0 < generalRelativisticMass 1 1
      ((gaussianSoftAbsMetric (ι := ι)).factor 0).toLinearMap p :=
    generalRelativisticMass_pos 1 1
      ((gaussianSoftAbsMetric (ι := ι)).factor 0).toLinearMap p
      (by norm_num) (by norm_num)
  have heigen : 0 < diagonalSoftAbsEigenvalue 1 gaussianHessianDiagonal 0 i :=
    diagonalSoftAbsEigenvalue_pos 1 (by norm_num) _ _ _
  calc
    p i * ((generalRelativisticMass 1 1
        ((gaussianSoftAbsMetric (ι := ι)).factor 0).toLinearMap p)⁻¹ *
          ((diagonalSoftAbsEigenvalue 1 gaussianHessianDiagonal 0 i)⁻¹ *
            p i)) =
        (generalRelativisticMass 1 1
          ((gaussianSoftAbsMetric (ι := ι)).factor 0).toLinearMap p)⁻¹ *
          (diagonalSoftAbsEigenvalue 1 gaussianHessianDiagonal 0 i)⁻¹ *
            (p i) ^ 2 := by ring
    _ ≥ 0 := mul_nonneg
      (mul_nonneg (inv_nonneg.mpr hmass.le) (inv_nonneg.mpr heigen.le))
      (sq_nonneg (p i))

/-- In one dimension the alignment is strict away from zero momentum. -/
theorem gaussianSoftAbsUnit_mul_velocity_pos (p : Momentum Unit)
    (hp : p ≠ 0) :
    0 < p Unit.unit * gaussianSoftAbsVelocity p Unit.unit := by
  have hnonneg := gaussianSoftAbs_inner_velocity_nonneg p
  have hnonneg' : 0 ≤ p Unit.unit * gaussianSoftAbsVelocity p Unit.unit := by
    simpa [euclideanInner] using hnonneg
  apply lt_of_le_of_ne hnonneg'
  intro hzero
  rcases mul_eq_zero.mp hzero.symm with hpzero | hvzero
  · apply hp
    funext i
    simpa [Subsingleton.elim i Unit.unit] using hpzero
  · apply gaussianSoftAbsVelocity_ne_zero hp
    funext i
    simpa [Subsingleton.elim i Unit.unit] using hvzero

theorem gaussianSoftAbsUnit_velocity_neg_of_momentum_neg
    (p : Momentum Unit) (hp : p Unit.unit < 0) :
    gaussianSoftAbsVelocity p Unit.unit < 0 := by
  have hp0 : p ≠ 0 := by
    intro hzero
    have := congrFun hzero Unit.unit
    simp at this
    linarith
  rcases (mul_pos_iff.mp (gaussianSoftAbsUnit_mul_velocity_pos p hp0)) with
    hpos | hneg
  · linarith
  · exact hneg.2

theorem gaussianSoftAbsUnit_velocity_pos_of_momentum_pos
    (p : Momentum Unit) (hp : 0 < p Unit.unit) :
    0 < gaussianSoftAbsVelocity p Unit.unit := by
  have hp0 : p ≠ 0 := by
    intro hzero
    have := congrFun hzero Unit.unit
    simp at this
    linarith
  rcases (mul_pos_iff.mp (gaussianSoftAbsUnit_mul_velocity_pos p hp0)) with
    hpos | hneg
  · exact hpos.2
  · linarith

/-- Exact scalar formula for the one-dimensional Gaussian SoftAbs velocity. -/
theorem gaussianSoftAbsUnit_velocity_eq (p : Momentum Unit) :
    gaussianSoftAbsVelocity p Unit.unit =
      (Real.sqrt
        ((((Real.sqrt (softAbs 1 1))⁻¹ * p Unit.unit) ^ 2) + 1))⁻¹ *
        ((softAbs 1 1)⁻¹ * p Unit.unit) := by
  unfold gaussianSoftAbsVelocity riemannianRelativisticVelocity
    generalRelativisticVelocity generalRelativisticMass relativisticMass
    gaussianSoftAbsMetric gaussianHessianDiagonal diagonalSoftAbsMetric
    diagonalSoftAbsFactor diagonalSoftAbsInverseMetric diagonalMomentumMap
    diagonalSoftAbsEigenvalue squaredEuclideanNorm euclideanInner
  simp [pow_two]

/-- Scalar form of the one-dimensional Gaussian SoftAbs velocity. -/
noncomputable def gaussianSoftAbsUnitScalarVelocity (x : ℝ) : ℝ :=
  (Real.sqrt ((((Real.sqrt (softAbs 1 1))⁻¹ * x) ^ 2) + 1))⁻¹ *
    ((softAbs 1 1)⁻¹ * x)

@[simp]
theorem gaussianSoftAbsUnit_velocity_coordinate (p : Momentum Unit) :
    gaussianSoftAbsVelocity p Unit.unit =
      gaussianSoftAbsUnitScalarVelocity (p Unit.unit) := by
  exact gaussianSoftAbsUnit_velocity_eq p

/-- The scalar velocity written without the inverse square-root factor. -/
theorem gaussianSoftAbsUnitScalarVelocity_eq (x : ℝ) :
    gaussianSoftAbsUnitScalarVelocity x =
      (x / softAbs 1 1) / Real.sqrt (x ^ 2 / softAbs 1 1 + 1) := by
  have hk : 0 < softAbs 1 1 := softAbs_pos 1 (by norm_num) 1
  have hsqrt : (Real.sqrt (softAbs 1 1))⁻¹ ^ 2 =
      (softAbs 1 1)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hk.le]
  have hinside :
      ((Real.sqrt (softAbs 1 1))⁻¹ * x) ^ 2 + 1 =
        x ^ 2 / softAbs 1 1 + 1 := by
    calc
      _ = (Real.sqrt (softAbs 1 1))⁻¹ ^ 2 * x ^ 2 + 1 := by ring
      _ = (softAbs 1 1)⁻¹ * x ^ 2 + 1 := by rw [hsqrt]
      _ = _ := by ring
  unfold gaussianSoftAbsUnitScalarVelocity
  rw [hinside]
  ring

@[simp]
theorem gaussianSoftAbsUnitScalarVelocity_neg (x : ℝ) :
    gaussianSoftAbsUnitScalarVelocity (-x) =
      -gaussianSoftAbsUnitScalarVelocity x := by
  rw [gaussianSoftAbsUnitScalarVelocity_eq,
    gaussianSoftAbsUnitScalarVelocity_eq]
  ring_nf

/-- The concrete one-dimensional relativistic velocity is uniformly bounded
by the speed parameter `c=1`. -/
theorem abs_gaussianSoftAbsUnitScalarVelocity_lt_one (x : ℝ) :
    |gaussianSoftAbsUnitScalarVelocity x| < 1 := by
  let k := softAbs 1 1
  let s := Real.sqrt (x ^ 2 / k + 1)
  have hk : 0 < k := softAbs_pos 1 (by norm_num) 1
  have hk1 : 1 < k := gaussianSoftAbsEigenvalue_gt_one
    (ι := Unit) 0 Unit.unit
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have hsSq : s ^ 2 = x ^ 2 / k + 1 := by
    dsimp [s]
    rw [Real.sq_sqrt]
    positivity
  have hsq : (x / k) ^ 2 < s ^ 2 := by
    rw [hsSq]
    field_simp [hk.ne']
    nlinarith [sq_nonneg x,
      mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hk1.le)]
  have habs : |x / k| < s := abs_lt_of_sq_lt_sq hsq hs.le
  rw [gaussianSoftAbsUnitScalarVelocity_eq]
  change |(x / k) / s| < 1
  rw [abs_div, abs_of_pos hs, div_lt_one hs]
  exact habs

/-- Exact scalar GR Hamiltonian for the one-dimensional Gaussian SoftAbs
client. The additive log-determinant term will cancel in every energy defect. -/
theorem gaussianSoftAbsUnit_hamiltonian_eq (q : Position Unit)
    (p : Momentum Unit) :
    generalRelativisticHamiltonian gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1 (q, p) =
      (q Unit.unit) ^ 2 / 2 +
        Real.sqrt ((p Unit.unit) ^ 2 / softAbs 1 1 + 1) +
          (1 / 2 : ℝ) * Real.log (softAbs 1 1) := by
  have hk : 0 < softAbs 1 1 := softAbs_pos 1 (by norm_num) 1
  have hsqrt : (Real.sqrt (softAbs 1 1))⁻¹ ^ 2 =
      (softAbs 1 1)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hk.le]
  unfold generalRelativisticHamiltonian gaussianSoftAbsPotential
    riemannianRelativisticKineticEnergy relativisticKineticEnergy
    gaussianSoftAbsMetric gaussianHessianDiagonal diagonalSoftAbsMetric
    diagonalSoftAbsFactor diagonalSoftAbsEigenvalue squaredEuclideanNorm
    euclideanInner
  simp [pow_two]
  have hinside :
      (Real.sqrt (softAbs 1 1))⁻¹ * p Unit.unit *
          ((Real.sqrt (softAbs 1 1))⁻¹ * p Unit.unit) + 1 =
        p Unit.unit * p Unit.unit / softAbs 1 1 + 1 := by
    calc
      _ = (Real.sqrt (softAbs 1 1))⁻¹ ^ 2 *
            (p Unit.unit) ^ 2 + 1 := by ring
      _ = (softAbs 1 1)⁻¹ * (p Unit.unit) ^ 2 + 1 := by rw [hsqrt]
      _ = _ := by ring
  rw [hinside]
  ring

/-- Elementary lower bound for a relativistic scalar ratio outside the unit
momentum interval. -/
theorem div_sqrt_sq_add_one_le_mul_div_sqrt_mul_sq_add_one
    (a b r : ℝ) (hb : 0 < b) (hr : 1 ≤ r) :
    b / Real.sqrt (a ^ 2 + 1) ≤
      (b * r) / Real.sqrt ((a * r) ^ 2 + 1) := by
  have hr0 : 0 ≤ r := by linarith
  have hr2 : 1 ≤ r ^ 2 := by nlinarith
  have hbase : 0 < a ^ 2 + 1 := by positivity
  have hrad : 0 < (a * r) ^ 2 + 1 := by positivity
  have hinside : (a * r) ^ 2 + 1 ≤ r ^ 2 * (a ^ 2 + 1) := by
    nlinarith [sq_nonneg a]
  have hsqrt : Real.sqrt ((a * r) ^ 2 + 1) ≤
      r * Real.sqrt (a ^ 2 + 1) := by
    calc
      Real.sqrt ((a * r) ^ 2 + 1) ≤
          Real.sqrt (r ^ 2 * (a ^ 2 + 1)) := Real.sqrt_le_sqrt hinside
      _ = Real.sqrt (r ^ 2) * Real.sqrt (a ^ 2 + 1) := by
        rw [Real.sqrt_mul (sq_nonneg r)]
      _ = r * Real.sqrt (a ^ 2 + 1) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hr0]
  rw [div_le_div_iff₀ (Real.sqrt_pos.2 hbase) (Real.sqrt_pos.2 hrad)]
  calc
    b * Real.sqrt ((a * r) ^ 2 + 1) ≤
        b * (r * Real.sqrt (a ^ 2 + 1)) := by gcongr
    _ = b * r * Real.sqrt (a ^ 2 + 1) := by ring

/-- Elementary upper tangent bound for `sqrt (t² + 1)` on the positive
half-line. -/
theorem sqrt_sq_add_one_le_add_inv_two_mul (t : ℝ) (ht : 0 < t) :
    Real.sqrt (t ^ 2 + 1) ≤ t + 1 / (2 * t) := by
  rw [Real.sqrt_le_left]
  · field_simp [ht.ne']
    nlinarith [sq_nonneg t]
  · positivity

/-- Algebraic core of the one-step tail-energy comparison.  The hypotheses
are the upper and lower square-root estimates used by the concrete SoftAbs
client below. -/
theorem mul_sub_half_le_mul_add_of_sqrt_bounds
    (r A p d s sNext sCurrent : ℝ)
    (hr : 0 < r) (hAr : r ≤ A) (hp : 0 ≤ p) (hd : 0 ≤ d)
    (hfactor : 0 ≤ 2 * A - d / 2)
    (hs : s ≤ A / r + r / (2 * A))
    (hnext : (2 * A + p - d / 2) / r ≤ sNext)
    (hcurrent : 1 ≤ sCurrent) :
    s * (2 * A - d / 2) ≤ A * (sNext + sCurrent) := by
  have hA : 0 < A := lt_of_lt_of_le hr hAr
  have hmain :
      (A / r + r / (2 * A)) * (2 * A - d / 2) ≤
        A * ((2 * A + p - d / 2) / r + 1) := by
    have hid :
        A * ((2 * A + p - d / 2) / r + 1) -
            (A / r + r / (2 * A)) * (2 * A - d / 2) =
          A * p / r + (A - r) + r * d / (4 * A) := by
      field_simp [hr.ne', hA.ne']
      ring
    have hnonneg : 0 ≤ A * p / r + (A - r) + r * d / (4 * A) := by
      positivity
    linarith
  calc
    s * (2 * A - d / 2) ≤
        (A / r + r / (2 * A)) * (2 * A - d / 2) := by gcongr
    _ ≤ A * ((2 * A + p - d / 2) / r + 1) := hmain
    _ ≤ A * (sNext + sCurrent) := by gcongr

/-- The square-root comparison controlling the kinetic-energy increment when
the half-kicked momentum has inward magnitude at least two. -/
theorem gaussianSoftAbsUnit_tail_sqrt_comparison_of_half_momentum
    (q p : ℝ) (hp0 : 0 ≤ p) (hhalf : 2 ≤ q / 2 - p) :
    let k := softAbs 1 1
    let A := q / 2 - p
    let s := Real.sqrt (A ^ 2 / k + 1)
    let d := A / k / s
    s * (2 * A - d / 2) ≤
      A * (Real.sqrt ((2 * A + p - d / 2) ^ 2 / k + 1) +
        Real.sqrt (p ^ 2 / k + 1)) := by
  dsimp only
  let k := softAbs 1 1
  let r := Real.sqrt k
  let A := q / 2 - p
  let s := Real.sqrt (A ^ 2 / k + 1)
  let d := A / k / s
  have hk : 0 < k := softAbs_pos 1 (by norm_num) 1
  have hk1 : 1 < k := by
    exact gaussianSoftAbsEigenvalue_gt_one (ι := Unit) 0 Unit.unit
  have hk2 : k < 2 := softAbs_one_one_lt_two
  have hr : 0 < r := Real.sqrt_pos.2 hk
  have hr1 : 1 < r := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) hk1
  have hrlt : r < 3 / 2 :=
    lt_trans (Real.sqrt_lt_sqrt hk.le hk2) Real.sqrt_two_lt_three_halves
  have hr2 : r ^ 2 = k := Real.sq_sqrt hk.le
  have hA : 2 ≤ A := by
    dsimp [A]
    exact hhalf
  have hAr : r ≤ A := by linarith
  have hAratio : 0 < A / r := div_pos (lt_of_lt_of_le (by norm_num) hA) hr
  have hrewrite (x : ℝ) : x ^ 2 / k = (x / r) ^ 2 := by
    rw [← hr2]
    field_simp [hr.ne']
  have hs_eq : s = Real.sqrt ((A / r) ^ 2 + 1) := by
    dsimp [s]
    rw [hrewrite]
  have hspos : 0 < s := by
    dsimp [s]
    positivity
  have hs_gt : A / r < s := by
    rw [hs_eq]
    calc
      A / r = Real.sqrt ((A / r) ^ 2) := by
        rw [Real.sqrt_sq hAratio.le]
      _ < Real.sqrt ((A / r) ^ 2 + 1) :=
        Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
  have hd0 : 0 ≤ d := by
    dsimp [d]
    positivity
  have hdlt : d < 1 := by
    have hrs : A < r * s := by
      have := mul_lt_mul_of_pos_left hs_gt hr
      field_simp [hr.ne'] at this
      simpa [mul_comm] using this
    have hdinv : d < 1 / r := by
      dsimp [d]
      rw [div_div, div_lt_div_iff₀ (mul_pos hk hspos) hr]
      rw [← hr2]
      nlinarith
    have hinvlt : 1 / r < 1 := by
      rw [div_lt_one hr]
      exact hr1
    exact lt_trans hdinv hinvlt
  have hfactor : 0 ≤ 2 * A - d / 2 := by linarith
  have hsupper : s ≤ A / r + r / (2 * A) := by
    rw [hs_eq]
    have h := sqrt_sq_add_one_le_add_inv_two_mul (A / r) hAratio
    calc
      Real.sqrt ((A / r) ^ 2 + 1) ≤
          A / r + 1 / (2 * (A / r)) := h
      _ = A / r + r / (2 * A) := by
        have hA0 : A ≠ 0 := (lt_of_lt_of_le (by norm_num) hA).ne'
        field_simp [hr.ne', hA0]
  have hx : 0 ≤ 2 * A + p - d / 2 := by linarith
  have hnext :
      (2 * A + p - d / 2) / r ≤
        Real.sqrt ((2 * A + p - d / 2) ^ 2 / k + 1) := by
    rw [hrewrite]
    calc
      (2 * A + p - d / 2) / r =
          Real.sqrt (((2 * A + p - d / 2) / r) ^ 2) := by
            rw [Real.sqrt_sq (div_nonneg hx hr.le)]
      _ ≤ Real.sqrt (((2 * A + p - d / 2) / r) ^ 2 + 1) :=
        Real.sqrt_le_sqrt (by linarith)
  have hcurrent : 1 ≤ Real.sqrt (p ^ 2 / k + 1) := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    have hdiv : 0 ≤ p ^ 2 / k := div_nonneg (sq_nonneg p) hk.le
    simpa using (show 1 ≤ p ^ 2 / k + 1 by linarith)
  exact mul_sub_half_le_mul_add_of_sqrt_bounds r A p d s
    (Real.sqrt ((2 * A + p - d / 2) ^ 2 / k + 1))
    (Real.sqrt (p ^ 2 / k + 1)) hr hAr hp0 hd0 hfactor hsupper hnext hcurrent

/-- Fixed central-event specialization of the half-momentum comparison. -/
theorem gaussianSoftAbsUnit_tail_sqrt_comparison
    (q p : ℝ) (hq : 6 ≤ q) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    let k := softAbs 1 1
    let A := q / 2 - p
    let s := Real.sqrt (A ^ 2 / k + 1)
    let d := A / k / s
    s * (2 * A - d / 2) ≤
      A * (Real.sqrt ((2 * A + p - d / 2) ^ 2 / k + 1) +
        Real.sqrt (p ^ 2 / k + 1)) := by
  apply gaussianSoftAbsUnit_tail_sqrt_comparison_of_half_momentum q p hp0
  linarith

/-- A unit leapfrog step does not increase the scalar Gaussian SoftAbs
Hamiltonian whenever the nonnegative refreshed momentum leaves an inward
half-kick of magnitude at least two. -/
theorem gaussianSoftAbsUnit_scalar_energy_decrease_of_half_momentum
    (q p : ℝ) (hp0 : 0 ≤ p) (hhalf : 2 ≤ q / 2 - p) :
    let k := softAbs 1 1
    let A := q / 2 - p
    let s := Real.sqrt (A ^ 2 / k + 1)
    let d := A / k / s
    (q - d) ^ 2 / 2 +
        Real.sqrt ((p - q + d / 2) ^ 2 / k + 1) ≤
      q ^ 2 / 2 + Real.sqrt (p ^ 2 / k + 1) := by
  dsimp only
  let k := softAbs 1 1
  let A := q / 2 - p
  let s := Real.sqrt (A ^ 2 / k + 1)
  let d := A / k / s
  let x := 2 * A + p - d / 2
  let sNext := Real.sqrt (x ^ 2 / k + 1)
  let sCurrent := Real.sqrt (p ^ 2 / k + 1)
  let B := q - d / 2
  have hk : 0 < k := softAbs_pos 1 (by norm_num) 1
  have hA : 2 ≤ A := by
    dsimp [A]
    exact hhalf
  have hspos : 0 < s := by
    dsimp [s]
    positivity
  have hd0 : 0 ≤ d := by
    dsimp [d]
    positivity
  have hdlt : d < 1 := by
    let r := Real.sqrt k
    have hr : 0 < r := Real.sqrt_pos.2 hk
    have hr1 : 1 < r := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt (by norm_num)
        (show 1 < k from gaussianSoftAbsEigenvalue_gt_one
          (ι := Unit) 0 Unit.unit)
    have hr2 : r ^ 2 = k := Real.sq_sqrt hk.le
    have hAratio : 0 < A / r := div_pos (lt_of_lt_of_le (by norm_num) hA) hr
    have hs_eq : s = Real.sqrt ((A / r) ^ 2 + 1) := by
      dsimp [s]
      congr 2
      rw [← hr2]
      field_simp [hr.ne']
    have hs_gt : A / r < s := by
      rw [hs_eq]
      calc
        A / r = Real.sqrt ((A / r) ^ 2) := by
          rw [Real.sqrt_sq hAratio.le]
        _ < Real.sqrt ((A / r) ^ 2 + 1) :=
          Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
    have hrs : A < r * s := by
      have := mul_lt_mul_of_pos_left hs_gt hr
      field_simp [hr.ne'] at this
      simpa [mul_comm] using this
    have hdinv : d < 1 / r := by
      dsimp [d]
      rw [div_div, div_lt_div_iff₀ (mul_pos hk hspos) hr]
      rw [← hr2]
      nlinarith
    have hinvlt : 1 / r < 1 := by
      rw [div_lt_one hr]
      exact hr1
    exact lt_trans hdinv hinvlt
  have hB : 0 < B := by
    dsimp [B]
    linarith
  have hsNext : 0 < sNext := by
    dsimp [sNext]
    positivity
  have hsCurrent : 0 < sCurrent := by
    dsimp [sCurrent]
    positivity
  have hcomparison :=
    gaussianSoftAbsUnit_tail_sqrt_comparison_of_half_momentum q p hp0 hhalf
  change s * (2 * A - d / 2) ≤ A * (sNext + sCurrent) at hcomparison
  have hAds : A = k * d * s := by
    dsimp [d]
    field_simp [hk.ne', hspos.ne']
  have hcore : 2 * A - d / 2 ≤ k * d * (sNext + sCurrent) := by
    have hdiv : 2 * A - d / 2 ≤
        (A * (sNext + sCurrent)) / s := by
      rw [le_div_iff₀ hspos]
      simpa [mul_comm] using hcomparison
    calc
      2 * A - d / 2 ≤ (A * (sNext + sCurrent)) / s := hdiv
      _ = k * d * (sNext + sCurrent) := by
        rw [hAds]
        field_simp [hspos.ne']
  have hproduct :
      B * (2 * A - d / 2) / k ≤ d * B * (sNext + sCurrent) := by
    rw [div_le_iff₀ hk]
    nlinarith
  have hsNextSq : sNext ^ 2 = x ^ 2 / k + 1 := by
    dsimp [sNext]
    rw [Real.sq_sqrt]
    positivity
  have hsCurrentSq : sCurrent ^ 2 = p ^ 2 / k + 1 := by
    dsimp [sCurrent]
    rw [Real.sq_sqrt]
    positivity
  have hx : x = B - p := by
    dsimp [x, B, A]
    ring
  have hdiffProduct :
      (sNext - sCurrent) * (sNext + sCurrent) =
        B * (2 * A - d / 2) / k := by
    calc
      (sNext - sCurrent) * (sNext + sCurrent) =
          sNext ^ 2 - sCurrent ^ 2 := by ring
      _ = (x ^ 2 / k + 1) - (p ^ 2 / k + 1) := by
        rw [hsNextSq, hsCurrentSq]
      _ = B * (2 * A - d / 2) / k := by
        rw [hx]
        dsimp [B, A]
        ring
  have hkinetic : sNext - sCurrent ≤ d * B := by
    have hsum : 0 < sNext + sCurrent := add_pos hsNext hsCurrent
    apply le_of_mul_le_mul_right _ hsum
    rw [hdiffProduct]
    exact hproduct
  have hsNextTarget :
      Real.sqrt ((p - q + d / 2) ^ 2 / k + 1) = sNext := by
    dsimp [sNext, x, A]
    congr 2
    ring
  change (q - d) ^ 2 / 2 +
      Real.sqrt ((p - q + d / 2) ^ 2 / k + 1) ≤
    q ^ 2 / 2 + sCurrent
  rw [hsNextTarget]
  dsimp [B] at hkinetic
  nlinarith

/-- Fixed central-event specialization of the scalar energy comparison. -/
theorem gaussianSoftAbsUnit_scalar_energy_decrease
    (q p : ℝ) (hq : 6 ≤ q) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    let k := softAbs 1 1
    let A := q / 2 - p
    let s := Real.sqrt (A ^ 2 / k + 1)
    let d := A / k / s
    (q - d) ^ 2 / 2 +
        Real.sqrt ((p - q + d / 2) ^ 2 / k + 1) ≤
      q ^ 2 / 2 + Real.sqrt (p ^ 2 / k + 1) := by
  apply gaussianSoftAbsUnit_scalar_energy_decrease_of_half_momentum q p hp0
  linarith

/-- Explicit positive lower speed attained once scalar momentum has magnitude
at least one. -/
noncomputable def gaussianSoftAbsUnitMinSpeed : ℝ :=
  (softAbs 1 1)⁻¹ /
    Real.sqrt (((Real.sqrt (softAbs 1 1))⁻¹) ^ 2 + 1)

theorem gaussianSoftAbsUnitMinSpeed_pos :
    0 < gaussianSoftAbsUnitMinSpeed := by
  unfold gaussianSoftAbsUnitMinSpeed
  have hk : 0 < softAbs 1 1 := softAbs_pos 1 (by norm_num) 1
  positivity

/-- Uniform positive velocity above unit momentum. -/
theorem gaussianSoftAbsUnitMinSpeed_le_velocity
    (p : Momentum Unit) (hp : 1 ≤ p Unit.unit) :
    gaussianSoftAbsUnitMinSpeed ≤ gaussianSoftAbsVelocity p Unit.unit := by
  rw [gaussianSoftAbsUnit_velocity_eq]
  unfold gaussianSoftAbsUnitMinSpeed
  have hk : 0 < softAbs 1 1 := softAbs_pos 1 (by norm_num) 1
  have h := div_sqrt_sq_add_one_le_mul_div_sqrt_mul_sq_add_one
    (Real.sqrt (softAbs 1 1))⁻¹ (softAbs 1 1)⁻¹ (p Unit.unit)
    (inv_pos.mpr hk) hp
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

theorem gaussianSoftAbsUnitMinSpeed_lt_one :
    gaussianSoftAbsUnitMinSpeed < 1 := by
  let p : Momentum Unit := fun _ => 1
  have hlower := gaussianSoftAbsUnitMinSpeed_le_velocity p (by simp [p])
  have habs := abs_gaussianSoftAbsUnitScalarVelocity_lt_one (p Unit.unit)
  rw [← gaussianSoftAbsUnit_velocity_coordinate] at habs
  exact lt_of_le_of_lt hlower (lt_of_le_of_lt (le_abs_self _) habs)

/-- Uniform negative velocity below minus unit momentum. -/
theorem gaussianSoftAbsUnit_velocity_le_neg_minSpeed
    (p : Momentum Unit) (hp : p Unit.unit ≤ -1) :
    gaussianSoftAbsVelocity p Unit.unit ≤ -gaussianSoftAbsUnitMinSpeed := by
  let pneg : Momentum Unit := -p
  have hpneg : 1 ≤ pneg Unit.unit := by
    dsimp [pneg]
    linarith
  have h := gaussianSoftAbsUnitMinSpeed_le_velocity pneg hpneg
  have hodd := gaussianSoftAbsVelocity_odd p
  have hcoord := congrFun hodd Unit.unit
  dsimp [pneg] at h hcoord
  rw [hcoord] at h
  linarith

/-- Constant-metric package consumed by the explicit leapfrog theorem. -/
noncomputable def gaussianSoftAbsConstantMetric : ConstantMetric ι where
  velocity := gaussianSoftAbsVelocity
  measurable_velocity := measurable_gaussianSoftAbsVelocity
  velocity_odd := gaussianSoftAbsVelocity_odd

/-- The actual Gaussian force callback. -/
def gaussianSoftAbsGradient (q : Position ι) : Momentum ι := q

omit [Fintype ι] [Nonempty ι] in
/-- The supplied diagonal is the actual coordinate Hessian of the Gaussian
potential, not an unrelated metric callback. -/
theorem gaussianHessianDiagonal_eq_fderiv_gradient
    (q : Position ι) (i : ι) :
    gaussianHessianDiagonal q i =
      fderiv ℝ (fun r : Position ι => gaussianSoftAbsGradient r i) q
        (Pi.single i 1) := by
  unfold gaussianHessianDiagonal gaussianSoftAbsGradient
  rw [(hasFDerivAt_apply i q).fderiv]
  simp

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] in
theorem measurable_gaussianSoftAbsGradient :
    Measurable (gaussianSoftAbsGradient : Position ι → Momentum ι) :=
  measurable_id

/-- Fully certified generalized-leapfrog selection for the Gaussian
diagonal-SoftAbs Hamiltonian. -/
noncomputable def gaussianSoftAbsSelection :
    GeneralizedLeapfrogSelection
      (separablePositionDerivative
        (gaussianSoftAbsGradient : Position ι → Momentum ι))
      (separableMomentumDerivative
        (gaussianSoftAbsVelocity : Momentum ι → Position ι)) :=
  separableGeneralizedLeapfrogSelection
    (gaussianSoftAbsVelocity : Momentum ι → Position ι)
    (gaussianSoftAbsGradient : Position ι → Momentum ι)

omit [Nonempty ι] [DecidableEq ι] in
theorem gaussianSoftAbsSelection_valid :
    (gaussianSoftAbsSelection (ι := ι)).IsValid := by
  exact separableGeneralizedLeapfrogSelection_valid
    (gaussianSoftAbsConstantMetric (ι := ι))
    (gaussianSoftAbsGradient (ι := ι))
    (measurable_gaussianSoftAbsGradient (ι := ι))

/-- Concrete phase-space multinomial transition for the Gaussian SoftAbs
client. -/
noncomputable abbrev gaussianSoftAbsPhaseTransition (ε : ℝ) (L : ℕ) :=
  multinomialGRHMCPhase (gaussianSoftAbsPotential (ι := ι))
    (gaussianSoftAbsMetric (ι := ι)) 1 1
    (gaussianSoftAbsSelection (ι := ι)) gaussianSoftAbsSelection_valid
    (measurable_diagonalSoftAbs_generalRelativisticHamiltonian
      (gaussianSoftAbsPotential (ι := ι))
      (measurable_gaussianSoftAbsPotential (ι := ι))
      1 (by norm_num) (gaussianHessianDiagonal (ι := ι))
      (measurable_gaussianHessianDiagonal (ι := ι)) 1 1) ε L

omit [Nonempty ι] [DecidableEq ι] in
/-- Exact one-step algebra for the concrete Gaussian SoftAbs solver.  The
relativistic velocity is evaluated at the force-kicked half momentum; this is
the nonquadratic term that a bare-kernel drift proof must control. -/
theorem gaussianSoftAbsSelection_step_eq (ε : ℝ) (z : PhaseSpace ι) :
    (gaussianSoftAbsSelection (ι := ι)).step ε z =
      let pHalf := z.2 - (ε / 2) • z.1
      let qNext := z.1 + ε • gaussianSoftAbsVelocity pHalf
      (qNext, pHalf - (ε / 2) • qNext) := by
  rfl

omit [Nonempty ι] [DecidableEq ι] in
/-- Position component of one concrete Gaussian SoftAbs generalized-leapfrog
step. -/
theorem gaussianSoftAbsSelection_step_fst (ε : ℝ) (z : PhaseSpace ι) :
    ((gaussianSoftAbsSelection (ι := ι)).step ε z).1 =
      z.1 + ε • gaussianSoftAbsVelocity (z.2 - (ε / 2) • z.1) := by
  rw [gaussianSoftAbsSelection_step_eq]

omit [Nonempty ι] [DecidableEq ι] in
/-- The concrete unit step is genuinely moving: from zero position and any
nonzero momentum, its proposed position is nonzero. -/
theorem gaussianSoftAbsSelection_step_one_fst_ne_zero
    {p : Momentum ι} (hp : p ≠ 0) :
    ((gaussianSoftAbsSelection (ι := ι)).step 1
      ((0 : Position ι), p)).1 ≠ 0 := by
  rw [gaussianSoftAbsSelection_step_fst]
  simpa using gaussianSoftAbsVelocity_ne_zero hp

/-- Every concrete unit step moves the one-dimensional position by strictly
less than one, independently of position and momentum. -/
theorem abs_gaussianSoftAbsSelection_step_one_fst_sub_lt_one
    (q : Position Unit) (p : Momentum Unit) :
    |((gaussianSoftAbsSelection (ι := Unit)).step 1 (q, p)).1 Unit.unit -
        q Unit.unit| < 1 := by
  rw [gaussianSoftAbsSelection_step_fst]
  simp only [Pi.add_apply, one_smul, add_sub_cancel_left]
  rw [gaussianSoftAbsUnit_velocity_coordinate]
  exact abs_gaussianSoftAbsUnitScalarVelocity_lt_one _

/-- The same finite-speed bound for every step size of magnitude at most one.
-/
theorem abs_gaussianSoftAbsSelection_step_fst_sub_lt_one
    (ε : ℝ) (hε : |ε| ≤ 1) (q : Position Unit) (p : Momentum Unit) :
    |((gaussianSoftAbsSelection (ι := Unit)).step ε (q, p)).1 Unit.unit -
        q Unit.unit| < 1 := by
  rw [gaussianSoftAbsSelection_step_fst]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]
  rw [gaussianSoftAbsUnit_velocity_coordinate, abs_mul]
  calc
    |ε| * |gaussianSoftAbsUnitScalarVelocity
        ((p - (ε / 2) • q) Unit.unit)| ≤
      1 * |gaussianSoftAbsUnitScalarVelocity
        ((p - (ε / 2) • q) Unit.unit)| := by gcongr
    _ < 1 := by
      simpa using abs_gaussianSoftAbsUnitScalarVelocity_lt_one
        ((p - (ε / 2) • q) Unit.unit)

/-- Every candidate in the two-point randomized orbit stays within one unit
of the current position, including the negative-time candidate. -/
theorem abs_gaussianSoftAbs_orbitPoint_fst_sub_lt_one
    (origin selected : Fin 2) (q : Position Unit) (p : Momentum Unit) :
    |(orbitPoint
        (generalizedLeapfrogPerm gaussianSoftAbsSelection
          gaussianSoftAbsSelection_valid.unique 1)
        origin (q, p) selected).1 Unit.unit - q Unit.unit| < 1 := by
  fin_cases origin <;> fin_cases selected
  · simp [orbitPoint]
  · simpa [orbitPoint] using
      abs_gaussianSoftAbsSelection_step_fst_sub_lt_one 1 (by norm_num) q p
  · simpa [orbitPoint] using
      abs_gaussianSoftAbsSelection_step_fst_sub_lt_one (-1) (by norm_num) q p
  · simp [orbitPoint]

/-- The complete two-point phase transition is supported inside the open
unit position neighborhood of its input, uniformly over momentum. -/
theorem gaussianSoftAbsPhaseTransition_unit_position_support
    (q : Position Unit) (p : Momentum Unit) :
    gaussianSoftAbsPhaseTransition 1 1 (q, p)
      {z | |z.1 Unit.unit - q Unit.unit| < 1} = 1 := by
  let s : Set (PhaseSpace Unit) :=
    {z | |z.1 Unit.unit - q Unit.unit| < 1}
  have hs : MeasurableSet s := by
    exact measurableSet_lt
      (((((measurable_pi_apply Unit.unit).comp measurable_fst).sub
        measurable_const).abs)) measurable_const
  change orbitMultinomialKernel
      (generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1)
      (generalizedLeapfrogPerm gaussianSoftAbsSelection
        gaussianSoftAbsSelection_valid.unique 1) 1
      (generalRelativisticBoltzmannWeight_ne_zero gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1)
      (generalRelativisticBoltzmannWeight_ne_top gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1)
      (measurable_generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1
        (measurable_diagonalSoftAbs_generalRelativisticHamiltonian
          gaussianSoftAbsPotential measurable_gaussianSoftAbsPotential
          1 (by norm_num) gaussianHessianDiagonal
          measurable_gaussianHessianDiagonal 1 1))
      (gaussianSoftAbsSelection_valid.measurable 1)
      (gaussianSoftAbsSelection_valid.measurable (-1)) (q, p) s = 1
  apply orbitMultinomialKernel_apply_eq_one_of_forall_mem
  · exact hs
  · intro origin selected
    exact abs_gaussianSoftAbs_orbitPoint_fst_sub_lt_one origin selected q p

/-- On the positive half-line, a half-kicked momentum pointing toward the
origin makes the unit Gaussian SoftAbs step move strictly inward. -/
theorem gaussianSoftAbsSelection_step_one_inward_of_pos
    (q : Position Unit) (p : Momentum Unit)
    (hp : p Unit.unit < q Unit.unit / 2) :
    ((gaussianSoftAbsSelection (ι := Unit)).step 1 (q, p)).1 Unit.unit <
      q Unit.unit := by
  rw [gaussianSoftAbsSelection_step_fst]
  have hhalf :
      (p - ((1 : ℝ) / 2) • q) Unit.unit < 0 := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have hvelocity := gaussianSoftAbsUnit_velocity_neg_of_momentum_neg
    (p - ((1 : ℝ) / 2) • q) hhalf
  simp only [Pi.add_apply, one_smul]
  linarith

/-- Exact scalar coordinates of the concrete unit leapfrog step. -/
theorem gaussianSoftAbsSelection_step_one_coordinates
    (q : Position Unit) (p : Momentum Unit) :
    let pHalf := p Unit.unit - q Unit.unit / 2
    let qNext := q Unit.unit + gaussianSoftAbsUnitScalarVelocity pHalf
    (((gaussianSoftAbsSelection (ι := Unit)).step 1 (q, p)).1 Unit.unit,
      ((gaussianSoftAbsSelection (ι := Unit)).step 1 (q, p)).2 Unit.unit) =
      (qNext, pHalf - qNext / 2) := by
  rw [gaussianSoftAbsSelection_step_eq]
  simp [gaussianSoftAbsUnit_velocity_coordinate]
  have hhalf : p Unit.unit - (2 : ℝ)⁻¹ * q Unit.unit =
      p Unit.unit - q Unit.unit / 2 := by ring
  constructor
  · rw [hhalf]
  · rw [hhalf]
    ring

/-- The actual selected Gaussian SoftAbs unit step has nonpositive complete
Hamiltonian defect under the expanding half-momentum condition. -/
theorem gaussianSoftAbsSelection_step_one_hamiltonian_le_of_half_momentum
    (q : Position Unit) (p : Momentum Unit)
    (hp0 : 0 ≤ p Unit.unit)
    (hhalf : 2 ≤ q Unit.unit / 2 - p Unit.unit) :
    generalRelativisticHamiltonian gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1
        ((gaussianSoftAbsSelection (ι := Unit)).step 1 (q, p)) ≤
      generalRelativisticHamiltonian gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1 (q, p) := by
  let q0 := q Unit.unit
  let p0 := p Unit.unit
  let k := softAbs 1 1
  let A := q0 / 2 - p0
  let s := Real.sqrt (A ^ 2 / k + 1)
  let d := A / k / s
  have henergy := gaussianSoftAbsUnit_scalar_energy_decrease_of_half_momentum
    q0 p0 hp0 hhalf
  change (q0 - d) ^ 2 / 2 +
      Real.sqrt ((p0 - q0 + d / 2) ^ 2 / k + 1) ≤
    q0 ^ 2 / 2 + Real.sqrt (p0 ^ 2 / k + 1) at henergy
  have hhalf : p0 - q0 / 2 = -A := by
    dsimp [A]
    ring
  have hvelocity : gaussianSoftAbsUnitScalarVelocity (p0 - q0 / 2) = -d := by
    rw [hhalf, gaussianSoftAbsUnitScalarVelocity_neg,
      gaussianSoftAbsUnitScalarVelocity_eq]
  have hcoordinates := gaussianSoftAbsSelection_step_one_coordinates q p
  change
    (((gaussianSoftAbsSelection (ι := Unit)).step 1 (q, p)).1 Unit.unit,
      ((gaussianSoftAbsSelection (ι := Unit)).step 1 (q, p)).2 Unit.unit) =
      (q0 + gaussianSoftAbsUnitScalarVelocity (p0 - q0 / 2),
        p0 - q0 / 2 -
          (q0 + gaussianSoftAbsUnitScalarVelocity (p0 - q0 / 2)) / 2)
    at hcoordinates
  rw [hvelocity] at hcoordinates
  have hqcoord := congrArg Prod.fst hcoordinates
  have hpcoord := congrArg Prod.snd hcoordinates
  simp only at hqcoord hpcoord
  rw [gaussianSoftAbsUnit_hamiltonian_eq,
    gaussianSoftAbsUnit_hamiltonian_eq]
  rw [hqcoord, hpcoord]
  have hqalg : q0 + -d = q0 - d := by ring
  have hpalg : p0 - q0 / 2 - (q0 - d) / 2 =
      p0 - q0 + d / 2 := by ring
  rw [hqalg, hpalg]
  dsimp [q0, p0, k] at henergy ⊢
  linarith

/-- Fixed central-event specialization of the complete-Hamiltonian defect
bound. -/
theorem gaussianSoftAbsSelection_step_one_hamiltonian_le_of_pos
    (q : Position Unit) (p : Momentum Unit)
    (hq : 6 ≤ q Unit.unit) (hp0 : 0 ≤ p Unit.unit)
    (hp1 : p Unit.unit ≤ 1) :
    generalRelativisticHamiltonian gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1
        ((gaussianSoftAbsSelection (ι := Unit)).step 1 (q, p)) ≤
      generalRelativisticHamiltonian gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1 (q, p) := by
  apply gaussianSoftAbsSelection_step_one_hamiltonian_le_of_half_momentum
    q p hp0
  linarith

/-- For nonpositive momentum, the symmetric expanding half-momentum
condition gives a nonpositive defect for the negative-time step. -/
theorem gaussianSoftAbsSelection_step_neg_one_hamiltonian_le_of_half_momentum
    (q : Position Unit) (p : Momentum Unit)
    (hp0 : p Unit.unit ≤ 0)
    (hhalf : 2 ≤ q Unit.unit / 2 + p Unit.unit) :
    generalRelativisticHamiltonian gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1
        ((gaussianSoftAbsSelection (ι := Unit)).step (-1) (q, p)) ≤
      generalRelativisticHamiltonian gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1 (q, p) := by
  have hforward :=
    gaussianSoftAbsSelection_step_one_hamiltonian_le_of_half_momentum
      q (-p) (by simpa using neg_nonneg.mpr hp0) (by simpa)
  have hflipInput : momentumFlip ((q, p) : PhaseSpace Unit) = (q, -p) := by
    rfl
  have hreversible :=
    gaussianSoftAbsSelection_valid.reversible 1 ((q, p) : PhaseSpace Unit)
  rw [hflipInput] at hreversible
  calc
    generalRelativisticHamiltonian gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1
        (gaussianSoftAbsSelection.step (-1) (q, p)) =
      generalRelativisticHamiltonian gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1
        (momentumFlip (gaussianSoftAbsSelection.step 1 (q, -p))) := by
          rw [hreversible]
    _ = generalRelativisticHamiltonian gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1
        (gaussianSoftAbsSelection.step 1 (q, -p)) :=
      generalRelativisticHamiltonian_momentumFlip _ _ _ _ _
    _ ≤ generalRelativisticHamiltonian gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1 (q, -p) := hforward
    _ = generalRelativisticHamiltonian gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1 (momentumFlip (q, p)) := by rw [hflipInput]
    _ = generalRelativisticHamiltonian gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1 (q, p) :=
      generalRelativisticHamiltonian_momentumFlip _ _ _ _ _

@[simp]
theorem gaussianSoftAbsUnit_hamiltonian_neg (z : PhaseSpace Unit) :
    generalRelativisticHamiltonian gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1 (-z) =
      generalRelativisticHamiltonian gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1 z := by
  rw [gaussianSoftAbsUnit_hamiltonian_eq,
    gaussianSoftAbsUnit_hamiltonian_eq]
  simp only [Prod.fst_neg, Prod.snd_neg, Pi.neg_apply, neg_sq]

@[simp]
theorem gaussianSoftAbsSelection_step_one_neg (z : PhaseSpace Unit) :
    (gaussianSoftAbsSelection (ι := Unit)).step 1 (-z) =
      -((gaussianSoftAbsSelection (ι := Unit)).step 1 z) := by
  rw [gaussianSoftAbsSelection_step_eq,
    gaussianSoftAbsSelection_step_eq]
  simp only [Prod.fst_neg, Prod.snd_neg, one_div, one_smul]
  rw [show -z.2 - (2 : ℝ)⁻¹ • -z.1 =
      -(z.2 - (2 : ℝ)⁻¹ • z.1) by module]
  rw [gaussianSoftAbsVelocity_odd]
  apply Prod.ext <;>
    simp only [Prod.fst_neg, Prod.snd_neg] <;>
    module

/-- Symmetric nonpositive Hamiltonian defect on the negative tail, using the
positive-probability momentum event `[-1,0]`. -/
theorem gaussianSoftAbsSelection_step_one_hamiltonian_le_of_neg
    (q : Position Unit) (p : Momentum Unit)
    (hq : q Unit.unit ≤ -6) (hp0 : p Unit.unit ≤ 0)
    (hp1 : -1 ≤ p Unit.unit) :
    generalRelativisticHamiltonian gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1
        ((gaussianSoftAbsSelection (ι := Unit)).step 1 (q, p)) ≤
      generalRelativisticHamiltonian gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1 (q, p) := by
  have hpos := gaussianSoftAbsSelection_step_one_hamiltonian_le_of_pos
    (-q) (-p) (by simpa using neg_le_neg hq)
      (by simpa using neg_nonneg.mpr hp0) (by simpa using neg_le_neg hp1)
  rw [show ((-q, -p) : PhaseSpace Unit) = -(q, p) by rfl,
    gaussianSoftAbsSelection_step_one_neg,
    gaussianSoftAbsUnit_hamiltonian_neg,
    gaussianSoftAbsUnit_hamiltonian_neg] at hpos
  exact hpos

/-- Expanding-band forward energy correction on the negative position tail
for nonpositive momentum. -/
theorem gaussianSoftAbsSelection_step_one_hamiltonian_le_of_neg_half_momentum
    (q : Position Unit) (p : Momentum Unit)
    (hp0 : p Unit.unit ≤ 0)
    (hhalf : 2 ≤ -q Unit.unit / 2 + p Unit.unit) :
    generalRelativisticHamiltonian gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1
        ((gaussianSoftAbsSelection (ι := Unit)).step 1 (q, p)) ≤
      generalRelativisticHamiltonian gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1 (q, p) := by
  have hpos :=
    gaussianSoftAbsSelection_step_one_hamiltonian_le_of_half_momentum
      (-q) (-p) (by simpa using neg_nonneg.mpr hp0) (by simpa)
  rw [show ((-q, -p) : PhaseSpace Unit) = -(q, p) by rfl,
    gaussianSoftAbsSelection_step_one_neg,
    gaussianSoftAbsUnit_hamiltonian_neg,
    gaussianSoftAbsUnit_hamiltonian_neg] at hpos
  exact hpos

/-- Expanding-band backward energy correction on the negative position tail
for nonnegative momentum. -/
theorem gaussianSoftAbsSelection_step_neg_one_hamiltonian_le_of_neg_half_momentum
    (q : Position Unit) (p : Momentum Unit)
    (hp0 : 0 ≤ p Unit.unit)
    (hhalf : 2 ≤ -q Unit.unit / 2 - p Unit.unit) :
    generalRelativisticHamiltonian gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1
        ((gaussianSoftAbsSelection (ι := Unit)).step (-1) (q, p)) ≤
      generalRelativisticHamiltonian gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1 (q, p) := by
  have hforward :=
    gaussianSoftAbsSelection_step_one_hamiltonian_le_of_neg_half_momentum
      q (-p) (by simpa using neg_nonpos.mpr hp0) (by dsimp; linarith)
  have hflipInput : momentumFlip ((q, p) : PhaseSpace Unit) = (q, -p) := by
    rfl
  have hreversible :=
    gaussianSoftAbsSelection_valid.reversible 1 ((q, p) : PhaseSpace Unit)
  rw [hflipInput] at hreversible
  calc
    generalRelativisticHamiltonian gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1
        (gaussianSoftAbsSelection.step (-1) (q, p)) =
      generalRelativisticHamiltonian gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1
        (momentumFlip (gaussianSoftAbsSelection.step 1 (q, -p))) := by
          rw [hreversible]
    _ = generalRelativisticHamiltonian gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1
        (gaussianSoftAbsSelection.step 1 (q, -p)) :=
      generalRelativisticHamiltonian_momentumFlip _ _ _ _ _
    _ ≤ generalRelativisticHamiltonian gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1 (q, -p) := hforward
    _ = generalRelativisticHamiltonian gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1 (momentumFlip (q, p)) := by rw [hflipInput]
    _ = generalRelativisticHamiltonian gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1 (q, p) :=
      generalRelativisticHamiltonian_momentumFlip _ _ _ _ _

/-- Under the expanding half-momentum condition, the forward endpoint gets at
least half of the two-point multinomial selection mass. -/
theorem half_le_gaussianSoftAbs_forward_indexProbability_of_half_momentum
    (q : Position Unit) (p : Momentum Unit)
    (hp0 : 0 ≤ p Unit.unit)
    (hhalf : 2 ≤ q Unit.unit / 2 - p Unit.unit) :
    (2 : ENNReal)⁻¹ ≤
      orbitIndexProbability
        (generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
          gaussianSoftAbsMetric 1 1)
        (generalizedLeapfrogPerm gaussianSoftAbsSelection
          gaussianSoftAbsSelection_valid.unique 1)
        (0 : Fin 2) (1 : Fin 2) (q, p) := by
  have hbound :=
    inv_card_exp_le_multinomialGRHMCPhase_indexProbability
      gaussianSoftAbsPotential gaussianSoftAbsMetric 1 1
      gaussianSoftAbsSelection gaussianSoftAbsSelection_valid
      1 (0 : Fin 2) (1 : Fin 2) (q, p) 0 (by
        intro i
        fin_cases i
        · simpa [orbitPoint] using
            gaussianSoftAbsSelection_step_one_hamiltonian_le_of_half_momentum
              q p hp0 hhalf
        · simp [orbitPoint])
  simpa using hbound

/-- Fixed central-event specialization of the forward-index floor. -/
theorem half_le_gaussianSoftAbs_forward_indexProbability_of_pos
    (q : Position Unit) (p : Momentum Unit)
    (hq : 6 ≤ q Unit.unit) (hp0 : 0 ≤ p Unit.unit)
    (hp1 : p Unit.unit ≤ 1) :
    (2 : ENNReal)⁻¹ ≤
      orbitIndexProbability
        (generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
          gaussianSoftAbsMetric 1 1)
        (generalizedLeapfrogPerm gaussianSoftAbsSelection
          gaussianSoftAbsSelection_valid.unique 1)
        (0 : Fin 2) (1 : Fin 2) (q, p) := by
  apply half_le_gaussianSoftAbs_forward_indexProbability_of_half_momentum
    q p hp0
  linarith

/-- For nonpositive momentum in the expanding central band, the backward
endpoint receives at least half of its two-point selection mass. -/
theorem half_le_gaussianSoftAbs_backward_indexProbability_of_half_momentum
    (q : Position Unit) (p : Momentum Unit)
    (hp0 : p Unit.unit ≤ 0)
    (hhalf : 2 ≤ q Unit.unit / 2 + p Unit.unit) :
    (2 : ENNReal)⁻¹ ≤
      orbitIndexProbability
        (generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
          gaussianSoftAbsMetric 1 1)
        (generalizedLeapfrogPerm gaussianSoftAbsSelection
          gaussianSoftAbsSelection_valid.unique 1)
        (1 : Fin 2) (0 : Fin 2) (q, p) := by
  have hbound :=
    inv_card_exp_le_multinomialGRHMCPhase_indexProbability
      gaussianSoftAbsPotential gaussianSoftAbsMetric 1 1
      gaussianSoftAbsSelection gaussianSoftAbsSelection_valid
      1 (1 : Fin 2) (0 : Fin 2) (q, p) 0 (by
        intro i
        fin_cases i
        · simp [orbitPoint]
        · simpa [orbitPoint] using
            gaussianSoftAbsSelection_step_neg_one_hamiltonian_le_of_half_momentum
              q p hp0 hhalf)
  simpa using hbound

/-- Negative-tail forward-index floor for nonpositive momentum. -/
theorem half_le_gaussianSoftAbs_forward_indexProbability_of_neg_half_momentum
    (q : Position Unit) (p : Momentum Unit)
    (hp0 : p Unit.unit ≤ 0)
    (hhalf : 2 ≤ -q Unit.unit / 2 + p Unit.unit) :
    (2 : ENNReal)⁻¹ ≤
      orbitIndexProbability
        (generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
          gaussianSoftAbsMetric 1 1)
        (generalizedLeapfrogPerm gaussianSoftAbsSelection
          gaussianSoftAbsSelection_valid.unique 1)
        (0 : Fin 2) (1 : Fin 2) (q, p) := by
  have hbound :=
    inv_card_exp_le_multinomialGRHMCPhase_indexProbability
      gaussianSoftAbsPotential gaussianSoftAbsMetric 1 1
      gaussianSoftAbsSelection gaussianSoftAbsSelection_valid
      1 (0 : Fin 2) (1 : Fin 2) (q, p) 0 (by
        intro i
        fin_cases i
        · simpa [orbitPoint] using
            gaussianSoftAbsSelection_step_one_hamiltonian_le_of_neg_half_momentum
              q p hp0 hhalf
        · simp [orbitPoint])
  simpa using hbound

/-- Negative-tail backward-index floor for nonnegative momentum. -/
theorem half_le_gaussianSoftAbs_backward_indexProbability_of_neg_half_momentum
    (q : Position Unit) (p : Momentum Unit)
    (hp0 : 0 ≤ p Unit.unit)
    (hhalf : 2 ≤ -q Unit.unit / 2 - p Unit.unit) :
    (2 : ENNReal)⁻¹ ≤
      orbitIndexProbability
        (generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
          gaussianSoftAbsMetric 1 1)
        (generalizedLeapfrogPerm gaussianSoftAbsSelection
          gaussianSoftAbsSelection_valid.unique 1)
        (1 : Fin 2) (0 : Fin 2) (q, p) := by
  have hbound :=
    inv_card_exp_le_multinomialGRHMCPhase_indexProbability
      gaussianSoftAbsPotential gaussianSoftAbsMetric 1 1
      gaussianSoftAbsSelection gaussianSoftAbsSelection_valid
      1 (1 : Fin 2) (0 : Fin 2) (q, p) 0 (by
        intro i
        fin_cases i
        · simp [orbitPoint]
        · simpa [orbitPoint] using
            gaussianSoftAbsSelection_step_neg_one_hamiltonian_le_of_neg_half_momentum
              q p hp0 hhalf)
  simpa using hbound

/-- Symmetric two-point multinomial selection floor on the negative tail. -/
theorem half_le_gaussianSoftAbs_forward_indexProbability_of_neg
    (q : Position Unit) (p : Momentum Unit)
    (hq : q Unit.unit ≤ -6) (hp0 : p Unit.unit ≤ 0)
    (hp1 : -1 ≤ p Unit.unit) :
    (2 : ENNReal)⁻¹ ≤
      orbitIndexProbability
        (generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
          gaussianSoftAbsMetric 1 1)
        (generalizedLeapfrogPerm gaussianSoftAbsSelection
          gaussianSoftAbsSelection_valid.unique 1)
        (0 : Fin 2) (1 : Fin 2) (q, p) := by
  have hbound :=
    inv_card_exp_le_multinomialGRHMCPhase_indexProbability
      gaussianSoftAbsPotential gaussianSoftAbsMetric 1 1
      gaussianSoftAbsSelection gaussianSoftAbsSelection_valid
      1 (0 : Fin 2) (1 : Fin 2) (q, p) 0 (by
        intro i
        fin_cases i
        · simpa [orbitPoint] using
            gaussianSoftAbsSelection_step_one_hamiltonian_le_of_neg
              q p hq hp0 hp1
        · simp [orbitPoint])
  simpa using hbound

/-- Common two-point bridge from a half-probability selected index to a
one-quarter phase-kernel event after uniform origin randomization. -/
theorem quarter_le_gaussianSoftAbsPhaseTransition_of_index
    (origin selected : Fin 2) (q : Position Unit) (p : Momentum Unit)
    {s : Set (PhaseSpace Unit)} (hs : MeasurableSet s)
    (hmem : orbitPoint
      (generalizedLeapfrogPerm gaussianSoftAbsSelection
        gaussianSoftAbsSelection_valid.unique 1)
      origin (q, p) selected ∈ s)
    (hindex : (2 : ENNReal)⁻¹ ≤
      orbitIndexProbability
        (generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
          gaussianSoftAbsMetric 1 1)
        (generalizedLeapfrogPerm gaussianSoftAbsSelection
          gaussianSoftAbsSelection_valid.unique 1)
        origin selected (q, p)) :
    (4 : ENNReal)⁻¹ ≤ gaussianSoftAbsPhaseTransition 1 1 (q, p) s := by
  have hbranch :=
    uniform_mul_indexProbability_le_orbitMultinomialKernel_apply
      (generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1)
      (generalizedLeapfrogPerm gaussianSoftAbsSelection
        gaussianSoftAbsSelection_valid.unique 1)
      (generalRelativisticBoltzmannWeight_ne_zero gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1)
      (generalRelativisticBoltzmannWeight_ne_top gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1)
      (measurable_generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1
        (measurable_diagonalSoftAbs_generalRelativisticHamiltonian
          gaussianSoftAbsPotential measurable_gaussianSoftAbsPotential
          1 (by norm_num) gaussianHessianDiagonal
          measurable_gaussianHessianDiagonal 1 1))
      (gaussianSoftAbsSelection_valid.measurable 1)
      (gaussianSoftAbsSelection_valid.measurable (-1))
      origin selected (q, p) hs hmem
  change (4 : ENNReal)⁻¹ ≤
    orbitMultinomialKernel
      (generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1)
      (generalizedLeapfrogPerm gaussianSoftAbsSelection
        gaussianSoftAbsSelection_valid.unique 1) 1
      (generalRelativisticBoltzmannWeight_ne_zero gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1)
      (generalRelativisticBoltzmannWeight_ne_top gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1)
      (measurable_generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1
        (measurable_diagonalSoftAbs_generalRelativisticHamiltonian
          gaussianSoftAbsPotential measurable_gaussianSoftAbsPotential
          1 (by norm_num) gaussianHessianDiagonal
          measurable_gaussianHessianDiagonal 1 1))
      (gaussianSoftAbsSelection_valid.measurable 1)
      (gaussianSoftAbsSelection_valid.measurable (-1)) (q, p) s
  calc
    (4 : ENNReal)⁻¹ =
        PMF.uniformOfFintype (Fin 2) origin * (2 : ENNReal)⁻¹ := by
      simp only [PMF.uniformOfFintype_apply, Fintype.card_fin,
        Nat.cast_ofNat]
      rw [show (4 : ENNReal) = 2 * 2 by norm_num,
        ENNReal.mul_inv (by simp) (by simp)]
    _ ≤ PMF.uniformOfFintype (Fin 2) origin *
        orbitIndexProbability
          (generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
            gaussianSoftAbsMetric 1 1)
          (generalizedLeapfrogPerm gaussianSoftAbsSelection
            gaussianSoftAbsSelection_valid.unique 1)
          origin selected (q, p) := by gcongr
    _ ≤ _ := hbranch

/-- Under the expanding half-momentum condition, random-origin selection
retains at least one-quarter probability for the inward endpoint. -/
theorem quarter_le_gaussianSoftAbsPhaseTransition_inward_of_half_momentum
    (q : Position Unit) (p : Momentum Unit)
    (hp0 : 0 ≤ p Unit.unit)
    (hhalfMomentum : 2 ≤ q Unit.unit / 2 - p Unit.unit) :
    (4 : ENNReal)⁻¹ ≤
      gaussianSoftAbsPhaseTransition 1 1 (q, p)
        {z | z.1 Unit.unit ≤
          q Unit.unit - gaussianSoftAbsUnitMinSpeed} := by
  let inward : Set (PhaseSpace Unit) :=
    {z | z.1 Unit.unit ≤ q Unit.unit - gaussianSoftAbsUnitMinSpeed}
  have hinward : MeasurableSet inward :=
    measurableSet_le
      ((measurable_pi_apply Unit.unit).comp measurable_fst) measurable_const
  have hmem : orbitPoint
      (generalizedLeapfrogPerm gaussianSoftAbsSelection
        gaussianSoftAbsSelection_valid.unique 1)
      (0 : Fin 2) (q, p) (1 : Fin 2) ∈ inward := by
    change
      ((gaussianSoftAbsSelection (ι := Unit)).step 1 (q, p)).1 Unit.unit ≤
        q Unit.unit - gaussianSoftAbsUnitMinSpeed
    rw [gaussianSoftAbsSelection_step_fst]
    have hhalf : (p - ((1 : ℝ) / 2) • q) Unit.unit ≤ -1 := by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    have hvelocity := gaussianSoftAbsUnit_velocity_le_neg_minSpeed
      (p - ((1 : ℝ) / 2) • q) hhalf
    simp only [Pi.add_apply, one_smul]
    linarith
  have hbranch :=
    uniform_mul_indexProbability_le_orbitMultinomialKernel_apply
      (generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1)
      (generalizedLeapfrogPerm gaussianSoftAbsSelection
        gaussianSoftAbsSelection_valid.unique 1)
      (generalRelativisticBoltzmannWeight_ne_zero gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1)
      (generalRelativisticBoltzmannWeight_ne_top gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1)
      (measurable_generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1
        (measurable_diagonalSoftAbs_generalRelativisticHamiltonian
          gaussianSoftAbsPotential measurable_gaussianSoftAbsPotential
          1 (by norm_num) gaussianHessianDiagonal
          measurable_gaussianHessianDiagonal 1 1))
      (gaussianSoftAbsSelection_valid.measurable 1)
      (gaussianSoftAbsSelection_valid.measurable (-1))
      (0 : Fin 2) (1 : Fin 2) (q, p) hinward hmem
  have hindex :=
    half_le_gaussianSoftAbs_forward_indexProbability_of_half_momentum
      q p hp0 hhalfMomentum
  change (4 : ENNReal)⁻¹ ≤
    orbitMultinomialKernel
      (generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1)
      (generalizedLeapfrogPerm gaussianSoftAbsSelection
        gaussianSoftAbsSelection_valid.unique 1) 1
      (generalRelativisticBoltzmannWeight_ne_zero gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1)
      (generalRelativisticBoltzmannWeight_ne_top gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1)
      (measurable_generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1
        (measurable_diagonalSoftAbs_generalRelativisticHamiltonian
          gaussianSoftAbsPotential measurable_gaussianSoftAbsPotential
          1 (by norm_num) gaussianHessianDiagonal
          measurable_gaussianHessianDiagonal 1 1))
      (gaussianSoftAbsSelection_valid.measurable 1)
      (gaussianSoftAbsSelection_valid.measurable (-1)) (q, p) inward
  calc
    (4 : ENNReal)⁻¹ =
        PMF.uniformOfFintype (Fin 2) (0 : Fin 2) * (2 : ENNReal)⁻¹ := by
      simp only [PMF.uniformOfFintype_apply, Fintype.card_fin,
        Nat.cast_ofNat]
      rw [show (4 : ENNReal) = 2 * 2 by norm_num,
        ENNReal.mul_inv (by simp) (by simp)]
    _ ≤ PMF.uniformOfFintype (Fin 2) (0 : Fin 2) *
        orbitIndexProbability
          (generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
            gaussianSoftAbsMetric 1 1)
          (generalizedLeapfrogPerm gaussianSoftAbsSelection
            gaussianSoftAbsSelection_valid.unique 1)
          (0 : Fin 2) (1 : Fin 2) (q, p) := by gcongr
    _ ≤ _ := hbranch

/-- Fixed central-event specialization of the random-origin inward floor. -/
theorem quarter_le_gaussianSoftAbsPhaseTransition_inward_of_pos
    (q : Position Unit) (p : Momentum Unit)
    (hq : 6 ≤ q Unit.unit) (hp0 : 0 ≤ p Unit.unit)
    (hp1 : p Unit.unit ≤ 1) :
    (4 : ENNReal)⁻¹ ≤
      gaussianSoftAbsPhaseTransition 1 1 (q, p)
        {z | z.1 Unit.unit ≤
          q Unit.unit - gaussianSoftAbsUnitMinSpeed} := by
  apply quarter_le_gaussianSoftAbsPhaseTransition_inward_of_half_momentum
    q p hp0
  linarith

/-- Nonpositive refreshed momentum in the expanding central band gives the
same one-quarter inward probability through the backward trajectory origin.
-/
theorem quarter_le_gaussianSoftAbsPhaseTransition_backward_inward_of_half_momentum
    (q : Position Unit) (p : Momentum Unit)
    (hp0 : p Unit.unit ≤ 0)
    (hhalfMomentum : 2 ≤ q Unit.unit / 2 + p Unit.unit) :
    (4 : ENNReal)⁻¹ ≤
      gaussianSoftAbsPhaseTransition 1 1 (q, p)
        {z | z.1 Unit.unit ≤
          q Unit.unit - gaussianSoftAbsUnitMinSpeed} := by
  let inward : Set (PhaseSpace Unit) :=
    {z | z.1 Unit.unit ≤ q Unit.unit - gaussianSoftAbsUnitMinSpeed}
  have hinward : MeasurableSet inward :=
    measurableSet_le
      ((measurable_pi_apply Unit.unit).comp measurable_fst) measurable_const
  have hmem : orbitPoint
      (generalizedLeapfrogPerm gaussianSoftAbsSelection
        gaussianSoftAbsSelection_valid.unique 1)
      (1 : Fin 2) (q, p) (0 : Fin 2) ∈ inward := by
    change
      ((gaussianSoftAbsSelection (ι := Unit)).step (-1) (q, p)).1 Unit.unit ≤
        q Unit.unit - gaussianSoftAbsUnitMinSpeed
    rw [gaussianSoftAbsSelection_step_fst]
    have hhalf : 1 ≤ (p - ((-1 : ℝ) / 2) • q) Unit.unit := by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    have hvelocity := gaussianSoftAbsUnitMinSpeed_le_velocity
      (p - ((-1 : ℝ) / 2) • q) hhalf
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have hbranch :=
    uniform_mul_indexProbability_le_orbitMultinomialKernel_apply
      (generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1)
      (generalizedLeapfrogPerm gaussianSoftAbsSelection
        gaussianSoftAbsSelection_valid.unique 1)
      (generalRelativisticBoltzmannWeight_ne_zero gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1)
      (generalRelativisticBoltzmannWeight_ne_top gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1)
      (measurable_generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1
        (measurable_diagonalSoftAbs_generalRelativisticHamiltonian
          gaussianSoftAbsPotential measurable_gaussianSoftAbsPotential
          1 (by norm_num) gaussianHessianDiagonal
          measurable_gaussianHessianDiagonal 1 1))
      (gaussianSoftAbsSelection_valid.measurable 1)
      (gaussianSoftAbsSelection_valid.measurable (-1))
      (1 : Fin 2) (0 : Fin 2) (q, p) hinward hmem
  have hindex :=
    half_le_gaussianSoftAbs_backward_indexProbability_of_half_momentum
      q p hp0 hhalfMomentum
  change (4 : ENNReal)⁻¹ ≤
    orbitMultinomialKernel
      (generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1)
      (generalizedLeapfrogPerm gaussianSoftAbsSelection
        gaussianSoftAbsSelection_valid.unique 1) 1
      (generalRelativisticBoltzmannWeight_ne_zero gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1)
      (generalRelativisticBoltzmannWeight_ne_top gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1)
      (measurable_generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1
        (measurable_diagonalSoftAbs_generalRelativisticHamiltonian
          gaussianSoftAbsPotential measurable_gaussianSoftAbsPotential
          1 (by norm_num) gaussianHessianDiagonal
          measurable_gaussianHessianDiagonal 1 1))
      (gaussianSoftAbsSelection_valid.measurable 1)
      (gaussianSoftAbsSelection_valid.measurable (-1)) (q, p) inward
  calc
    (4 : ENNReal)⁻¹ =
        PMF.uniformOfFintype (Fin 2) (1 : Fin 2) * (2 : ENNReal)⁻¹ := by
      simp only [PMF.uniformOfFintype_apply, Fintype.card_fin,
        Nat.cast_ofNat]
      rw [show (4 : ENNReal) = 2 * 2 by norm_num,
        ENNReal.mul_inv (by simp) (by simp)]
    _ ≤ PMF.uniformOfFintype (Fin 2) (1 : Fin 2) *
        orbitIndexProbability
          (generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
            gaussianSoftAbsMetric 1 1)
          (generalizedLeapfrogPerm gaussianSoftAbsSelection
            gaussianSoftAbsSelection_valid.unique 1)
          (1 : Fin 2) (0 : Fin 2) (q, p) := by gcongr
    _ ≤ _ := hbranch

/-- Every momentum in the expanding symmetric central band gives the same
one-quarter inward phase-transition probability. -/
theorem quarter_le_gaussianSoftAbsPhaseTransition_inward_of_abs_momentum
    (q : Position Unit) (p : Momentum Unit)
    (hp : |p Unit.unit| ≤ q Unit.unit / 2 - 2) :
    (4 : ENNReal)⁻¹ ≤
      gaussianSoftAbsPhaseTransition 1 1 (q, p)
        {z | z.1 Unit.unit ≤
          q Unit.unit - gaussianSoftAbsUnitMinSpeed} := by
  by_cases hp0 : 0 ≤ p Unit.unit
  · apply quarter_le_gaussianSoftAbsPhaseTransition_inward_of_half_momentum
      q p hp0
    rw [abs_of_nonneg hp0] at hp
    linarith
  · have hpnonpos : p Unit.unit ≤ 0 := le_of_not_ge hp0
    apply
      quarter_le_gaussianSoftAbsPhaseTransition_backward_inward_of_half_momentum
        q p hpnonpos
    rw [abs_of_nonpos hpnonpos] at hp
    linarith

/-- On the same central band, both the forward and backward trajectory
endpoints are non-outward, so the phase transition cannot increase position.
-/
theorem gaussianSoftAbsPhaseTransition_nonoutward_of_abs_momentum
    (q : Position Unit) (p : Momentum Unit)
    (hp : |p Unit.unit| ≤ q Unit.unit / 2 - 2) :
    gaussianSoftAbsPhaseTransition 1 1 (q, p)
      {z | z.1 Unit.unit ≤ q Unit.unit} = 1 := by
  let nonoutward : Set (PhaseSpace Unit) :=
    {z | z.1 Unit.unit ≤ q Unit.unit}
  have hnonoutward : MeasurableSet nonoutward :=
    measurableSet_le
      ((measurable_pi_apply Unit.unit).comp measurable_fst) measurable_const
  change orbitMultinomialKernel
      (generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1)
      (generalizedLeapfrogPerm gaussianSoftAbsSelection
        gaussianSoftAbsSelection_valid.unique 1) 1
      (generalRelativisticBoltzmannWeight_ne_zero gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1)
      (generalRelativisticBoltzmannWeight_ne_top gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1)
      (measurable_generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1
        (measurable_diagonalSoftAbs_generalRelativisticHamiltonian
          gaussianSoftAbsPotential measurable_gaussianSoftAbsPotential
          1 (by norm_num) gaussianHessianDiagonal
          measurable_gaussianHessianDiagonal 1 1))
      (gaussianSoftAbsSelection_valid.measurable 1)
      (gaussianSoftAbsSelection_valid.measurable (-1)) (q, p) nonoutward = 1
  apply orbitMultinomialKernel_apply_eq_one_of_forall_mem
  · exact hnonoutward
  · intro origin selected
    fin_cases origin <;> fin_cases selected
    · change q Unit.unit ≤ q Unit.unit
      exact le_rfl
    · change
        ((gaussianSoftAbsSelection (ι := Unit)).step 1 (q, p)).1 Unit.unit ≤
          q Unit.unit
      rw [gaussianSoftAbsSelection_step_fst]
      have hhalf : (p - ((1 : ℝ) / 2) • q) Unit.unit ≤ 0 := by
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        have hpUpper : p Unit.unit ≤ q Unit.unit / 2 - 2 :=
          le_trans (le_abs_self _) hp
        linarith
      by_cases hzero : (p - ((1 : ℝ) / 2) • q) Unit.unit = 0
      · simp only [Pi.add_apply, one_smul]
        rw [show p - ((1 : ℝ) / 2) • q = 0 by
          funext i
          simpa [Subsingleton.elim i Unit.unit] using hzero]
        rw [gaussianSoftAbsUnit_velocity_coordinate]
        simp [gaussianSoftAbsUnitScalarVelocity]
      · have hneg : (p - ((1 : ℝ) / 2) • q) Unit.unit < 0 :=
          lt_of_le_of_ne hhalf hzero
        have hv := gaussianSoftAbsUnit_velocity_neg_of_momentum_neg
          (p - ((1 : ℝ) / 2) • q) hneg
        simp only [Pi.add_apply, one_smul]
        linarith
    · change
        ((gaussianSoftAbsSelection (ι := Unit)).step (-1) (q, p)).1 Unit.unit ≤
          q Unit.unit
      rw [gaussianSoftAbsSelection_step_fst]
      have hhalf : 0 ≤ (p - ((-1 : ℝ) / 2) • q) Unit.unit := by
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        have hpLower : -(q Unit.unit / 2 - 2) ≤ p Unit.unit :=
          le_trans (neg_le_neg hp) (neg_abs_le _)
        linarith
      by_cases hzero : (p - ((-1 : ℝ) / 2) • q) Unit.unit = 0
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [show p - ((-1 : ℝ) / 2) • q = 0 by
          funext i
          simpa [Subsingleton.elim i Unit.unit] using hzero]
        rw [gaussianSoftAbsUnit_velocity_coordinate]
        simp [gaussianSoftAbsUnitScalarVelocity]
      · have hpos : 0 < (p - ((-1 : ℝ) / 2) • q) Unit.unit :=
          lt_of_le_of_ne hhalf (Ne.symm hzero)
        have hv := gaussianSoftAbsUnit_velocity_pos_of_momentum_pos
          (p - ((-1 : ℝ) / 2) • q) hpos
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        linarith
    · change q Unit.unit ≤ q Unit.unit
      exact le_rfl

/-- Expanding symmetric momentum band on the negative position tail gives a
one-quarter probability of moving rightward toward the origin. -/
theorem quarter_le_gaussianSoftAbsPhaseTransition_inward_of_neg_abs_momentum
    (q : Position Unit) (p : Momentum Unit)
    (hp : |p Unit.unit| ≤ -q Unit.unit / 2 - 2) :
    (4 : ENNReal)⁻¹ ≤
      gaussianSoftAbsPhaseTransition 1 1 (q, p)
        {z | q Unit.unit + gaussianSoftAbsUnitMinSpeed ≤ z.1 Unit.unit} := by
  let inward : Set (PhaseSpace Unit) :=
    {z | q Unit.unit + gaussianSoftAbsUnitMinSpeed ≤ z.1 Unit.unit}
  have hinward : MeasurableSet inward :=
    measurableSet_le measurable_const
      ((measurable_pi_apply Unit.unit).comp measurable_fst)
  by_cases hp0 : p Unit.unit ≤ 0
  · have hhalf : 2 ≤ -q Unit.unit / 2 + p Unit.unit := by
      rw [abs_of_nonpos hp0] at hp
      linarith
    apply quarter_le_gaussianSoftAbsPhaseTransition_of_index
      (0 : Fin 2) (1 : Fin 2) q p hinward
    · change q Unit.unit + gaussianSoftAbsUnitMinSpeed ≤
        ((gaussianSoftAbsSelection (ι := Unit)).step 1 (q, p)).1 Unit.unit
      rw [gaussianSoftAbsSelection_step_fst]
      have hhalf' : 1 ≤ (p - ((1 : ℝ) / 2) • q) Unit.unit := by
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        linarith
      have hv := gaussianSoftAbsUnitMinSpeed_le_velocity
        (p - ((1 : ℝ) / 2) • q) hhalf'
      simp only [Pi.add_apply, one_smul]
      linarith
    · exact
        half_le_gaussianSoftAbs_forward_indexProbability_of_neg_half_momentum
          q p hp0 hhalf
  · have hpnonneg : 0 ≤ p Unit.unit := le_of_not_ge hp0
    have hhalf : 2 ≤ -q Unit.unit / 2 - p Unit.unit := by
      rw [abs_of_nonneg hpnonneg] at hp
      linarith
    apply quarter_le_gaussianSoftAbsPhaseTransition_of_index
      (1 : Fin 2) (0 : Fin 2) q p hinward
    · change q Unit.unit + gaussianSoftAbsUnitMinSpeed ≤
        ((gaussianSoftAbsSelection (ι := Unit)).step (-1) (q, p)).1 Unit.unit
      rw [gaussianSoftAbsSelection_step_fst]
      have hhalf' : (p - ((-1 : ℝ) / 2) • q) Unit.unit ≤ -1 := by
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        linarith
      have hv := gaussianSoftAbsUnit_velocity_le_neg_minSpeed
        (p - ((-1 : ℝ) / 2) • q) hhalf'
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    · exact
        half_le_gaussianSoftAbs_backward_indexProbability_of_neg_half_momentum
          q p hpnonneg hhalf

/-- On the expanding central band of the negative tail, neither trajectory
direction can move farther left. -/
theorem gaussianSoftAbsPhaseTransition_nonoutward_of_neg_abs_momentum
    (q : Position Unit) (p : Momentum Unit)
    (hp : |p Unit.unit| ≤ -q Unit.unit / 2 - 2) :
    gaussianSoftAbsPhaseTransition 1 1 (q, p)
      {z | q Unit.unit ≤ z.1 Unit.unit} = 1 := by
  let nonoutward : Set (PhaseSpace Unit) :=
    {z | q Unit.unit ≤ z.1 Unit.unit}
  have hnonoutward : MeasurableSet nonoutward :=
    measurableSet_le measurable_const
      ((measurable_pi_apply Unit.unit).comp measurable_fst)
  change orbitMultinomialKernel
      (generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1)
      (generalizedLeapfrogPerm gaussianSoftAbsSelection
        gaussianSoftAbsSelection_valid.unique 1) 1
      (generalRelativisticBoltzmannWeight_ne_zero gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1)
      (generalRelativisticBoltzmannWeight_ne_top gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1)
      (measurable_generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1
        (measurable_diagonalSoftAbs_generalRelativisticHamiltonian
          gaussianSoftAbsPotential measurable_gaussianSoftAbsPotential
          1 (by norm_num) gaussianHessianDiagonal
          measurable_gaussianHessianDiagonal 1 1))
      (gaussianSoftAbsSelection_valid.measurable 1)
      (gaussianSoftAbsSelection_valid.measurable (-1)) (q, p) nonoutward = 1
  apply orbitMultinomialKernel_apply_eq_one_of_forall_mem
  · exact hnonoutward
  · intro origin selected
    fin_cases origin <;> fin_cases selected
    · change q Unit.unit ≤ q Unit.unit
      exact le_rfl
    · change q Unit.unit ≤
        ((gaussianSoftAbsSelection (ι := Unit)).step 1 (q, p)).1 Unit.unit
      rw [gaussianSoftAbsSelection_step_fst]
      have hhalf : 0 ≤ (p - ((1 : ℝ) / 2) • q) Unit.unit := by
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        have hpLower : -(-q Unit.unit / 2 - 2) ≤ p Unit.unit :=
          le_trans (neg_le_neg hp) (neg_abs_le _)
        linarith
      by_cases hzero : (p - ((1 : ℝ) / 2) • q) Unit.unit = 0
      · simp only [Pi.add_apply, one_smul]
        rw [show p - ((1 : ℝ) / 2) • q = 0 by
          funext i
          simpa [Subsingleton.elim i Unit.unit] using hzero]
        rw [gaussianSoftAbsUnit_velocity_coordinate]
        simp [gaussianSoftAbsUnitScalarVelocity]
      · have hpos : 0 < (p - ((1 : ℝ) / 2) • q) Unit.unit :=
          lt_of_le_of_ne hhalf (Ne.symm hzero)
        have hv := gaussianSoftAbsUnit_velocity_pos_of_momentum_pos
          (p - ((1 : ℝ) / 2) • q) hpos
        simp only [Pi.add_apply, one_smul]
        linarith
    · change q Unit.unit ≤
        ((gaussianSoftAbsSelection (ι := Unit)).step (-1) (q, p)).1 Unit.unit
      rw [gaussianSoftAbsSelection_step_fst]
      have hhalf : (p - ((-1 : ℝ) / 2) • q) Unit.unit ≤ 0 := by
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        have hpUpper : p Unit.unit ≤ -q Unit.unit / 2 - 2 :=
          le_trans (le_abs_self _) hp
        linarith
      by_cases hzero : (p - ((-1 : ℝ) / 2) • q) Unit.unit = 0
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [show p - ((-1 : ℝ) / 2) • q = 0 by
          funext i
          simpa [Subsingleton.elim i Unit.unit] using hzero]
        rw [gaussianSoftAbsUnit_velocity_coordinate]
        simp [gaussianSoftAbsUnitScalarVelocity]
      · have hneg : (p - ((-1 : ℝ) / 2) • q) Unit.unit < 0 :=
          lt_of_le_of_ne hhalf hzero
        have hv := gaussianSoftAbsUnit_velocity_neg_of_momentum_neg
          (p - ((-1 : ℝ) / 2) • q) hneg
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        linarith
    · change q Unit.unit ≤ q Unit.unit
      exact le_rfl

/-- Symmetric random-origin phase-space inward probability on the negative
tail. -/
theorem quarter_le_gaussianSoftAbsPhaseTransition_inward_of_neg
    (q : Position Unit) (p : Momentum Unit)
    (hq : q Unit.unit ≤ -6) (hp0 : p Unit.unit ≤ 0)
    (hp1 : -1 ≤ p Unit.unit) :
    (4 : ENNReal)⁻¹ ≤
      gaussianSoftAbsPhaseTransition 1 1 (q, p)
        {z | q Unit.unit + gaussianSoftAbsUnitMinSpeed ≤
          z.1 Unit.unit} := by
  let inward : Set (PhaseSpace Unit) :=
    {z | q Unit.unit + gaussianSoftAbsUnitMinSpeed ≤ z.1 Unit.unit}
  have hinward : MeasurableSet inward :=
    measurableSet_le measurable_const
      ((measurable_pi_apply Unit.unit).comp measurable_fst)
  have hmem : orbitPoint
      (generalizedLeapfrogPerm gaussianSoftAbsSelection
        gaussianSoftAbsSelection_valid.unique 1)
      (0 : Fin 2) (q, p) (1 : Fin 2) ∈ inward := by
    change q Unit.unit + gaussianSoftAbsUnitMinSpeed ≤
      ((gaussianSoftAbsSelection (ι := Unit)).step 1 (q, p)).1 Unit.unit
    rw [gaussianSoftAbsSelection_step_fst]
    have hhalf : 1 ≤ (p - ((1 : ℝ) / 2) • q) Unit.unit := by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    have hvelocity := gaussianSoftAbsUnitMinSpeed_le_velocity
      (p - ((1 : ℝ) / 2) • q) hhalf
    simp only [Pi.add_apply, one_smul]
    linarith
  have hbranch :=
    uniform_mul_indexProbability_le_orbitMultinomialKernel_apply
      (generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1)
      (generalizedLeapfrogPerm gaussianSoftAbsSelection
        gaussianSoftAbsSelection_valid.unique 1)
      (generalRelativisticBoltzmannWeight_ne_zero gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1)
      (generalRelativisticBoltzmannWeight_ne_top gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1)
      (measurable_generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1
        (measurable_diagonalSoftAbs_generalRelativisticHamiltonian
          gaussianSoftAbsPotential measurable_gaussianSoftAbsPotential
          1 (by norm_num) gaussianHessianDiagonal
          measurable_gaussianHessianDiagonal 1 1))
      (gaussianSoftAbsSelection_valid.measurable 1)
      (gaussianSoftAbsSelection_valid.measurable (-1))
      (0 : Fin 2) (1 : Fin 2) (q, p) hinward hmem
  have hindex := half_le_gaussianSoftAbs_forward_indexProbability_of_neg
    q p hq hp0 hp1
  change (4 : ENNReal)⁻¹ ≤
    orbitMultinomialKernel
      (generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1)
      (generalizedLeapfrogPerm gaussianSoftAbsSelection
        gaussianSoftAbsSelection_valid.unique 1) 1
      (generalRelativisticBoltzmannWeight_ne_zero gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1)
      (generalRelativisticBoltzmannWeight_ne_top gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1)
      (measurable_generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
        gaussianSoftAbsMetric 1 1
        (measurable_diagonalSoftAbs_generalRelativisticHamiltonian
          gaussianSoftAbsPotential measurable_gaussianSoftAbsPotential
          1 (by norm_num) gaussianHessianDiagonal
          measurable_gaussianHessianDiagonal 1 1))
      (gaussianSoftAbsSelection_valid.measurable 1)
      (gaussianSoftAbsSelection_valid.measurable (-1)) (q, p) inward
  calc
    (4 : ENNReal)⁻¹ =
        PMF.uniformOfFintype (Fin 2) (0 : Fin 2) * (2 : ENNReal)⁻¹ := by
      simp only [PMF.uniformOfFintype_apply, Fintype.card_fin,
        Nat.cast_ofNat]
      rw [show (4 : ENNReal) = 2 * 2 by norm_num,
        ENNReal.mul_inv (by simp) (by simp)]
    _ ≤ PMF.uniformOfFintype (Fin 2) (0 : Fin 2) *
        orbitIndexProbability
          (generalRelativisticBoltzmannWeight gaussianSoftAbsPotential
            gaussianSoftAbsMetric 1 1)
          (generalizedLeapfrogPerm gaussianSoftAbsSelection
            gaussianSoftAbsSelection_valid.unique 1)
          (0 : Fin 2) (1 : Fin 2) (q, p) := by gcongr
    _ ≤ _ := hbranch

/-- Symmetric inward movement on the negative half-line. -/
theorem gaussianSoftAbsSelection_step_one_inward_of_neg
    (q : Position Unit) (p : Momentum Unit)
    (hp : q Unit.unit / 2 < p Unit.unit) :
    q Unit.unit <
      ((gaussianSoftAbsSelection (ι := Unit)).step 1 (q, p)).1 Unit.unit := by
  rw [gaussianSoftAbsSelection_step_fst]
  have hhalf : 0 < (p - ((1 : ℝ) / 2) • q) Unit.unit := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have hvelocity := gaussianSoftAbsUnit_velocity_pos_of_momentum_pos
    (p - ((1 : ℝ) / 2) • q) hhalf
  simp only [Pi.add_apply, one_smul]
  linarith

/-- Quantitative inward displacement on the positive tail when refreshed
momentum lies in the fixed central event `p ≤ 1`. -/
theorem gaussianSoftAbsSelection_step_one_le_sub_minSpeed
    (q : Position Unit) (p : Momentum Unit)
    (hq : 4 ≤ q Unit.unit) (hp : p Unit.unit ≤ 1) :
    ((gaussianSoftAbsSelection (ι := Unit)).step 1 (q, p)).1 Unit.unit ≤
      q Unit.unit - gaussianSoftAbsUnitMinSpeed := by
  rw [gaussianSoftAbsSelection_step_fst]
  have hhalf : (p - ((1 : ℝ) / 2) • q) Unit.unit ≤ -1 := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have hvelocity := gaussianSoftAbsUnit_velocity_le_neg_minSpeed
    (p - ((1 : ℝ) / 2) • q) hhalf
  simp only [Pi.add_apply, one_smul]
  linarith

/-- Symmetric quantitative inward displacement on the negative tail under
the central event `-1 ≤ p`. -/
theorem add_minSpeed_le_gaussianSoftAbsSelection_step_one
    (q : Position Unit) (p : Momentum Unit)
    (hq : q Unit.unit ≤ -4) (hp : -1 ≤ p Unit.unit) :
    q Unit.unit + gaussianSoftAbsUnitMinSpeed ≤
      ((gaussianSoftAbsSelection (ι := Unit)).step 1 (q, p)).1 Unit.unit := by
  rw [gaussianSoftAbsSelection_step_fst]
  have hhalf : 1 ≤ (p - ((1 : ℝ) / 2) • q) Unit.unit := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have hvelocity := gaussianSoftAbsUnitMinSpeed_le_velocity
    (p - ((1 : ℝ) / 2) • q) hhalf
  simp only [Pi.add_apply, one_smul]
  linarith

/-- Coordinate description of an open interval agrees with the order
interval on one-dimensional momentum functions. -/
theorem unitMomentum_coordinate_Ioo_eq (a b : ℝ) :
    {p : Momentum Unit | a < p Unit.unit ∧ p Unit.unit < b} =
      Set.Ioo (fun _ : Unit => a) (fun _ : Unit => b) := by
  ext p
  change (a < p Unit.unit ∧ p Unit.unit < b) ↔
    ((fun _ : Unit => a) < p ∧ p < fun _ : Unit => b)
  constructor
  · rintro ⟨ha, hb⟩
    constructor
    · apply Pi.lt_def.2
      exact ⟨fun i => by simpa [Subsingleton.elim i Unit.unit] using ha.le,
        ⟨Unit.unit, ha⟩⟩
    · apply Pi.lt_def.2
      exact ⟨fun i => by simpa [Subsingleton.elim i Unit.unit] using hb.le,
        ⟨Unit.unit, hb⟩⟩
  · rintro ⟨ha, hb⟩
    rcases Pi.lt_def.1 ha with ⟨_hale, i, hai⟩
    rcases Pi.lt_def.1 hb with ⟨_hble, j, hjb⟩
    exact ⟨by simpa [Subsingleton.elim i Unit.unit] using hai,
      by simpa [Subsingleton.elim j Unit.unit] using hjb⟩

/-- The unnormalized one-dimensional Euclidean relativistic law gives
positive mass to every nonempty open coordinate interval. -/
theorem euclideanRelativisticMomentumMeasure_unit_Ioo_pos
    {a b : ℝ} (hab : a < b) :
    0 < euclideanRelativisticMomentumMeasure Unit 1 1
      (Set.Ioo (fun _ : Unit => a) (fun _ : Unit => b)) := by
  let s : Set (Momentum Unit) :=
    {p | a < p Unit.unit ∧ p Unit.unit < b}
  have hs : MeasurableSet s := by
    exact (measurableSet_lt measurable_const (measurable_pi_apply _)).inter
      (measurableSet_lt (measurable_pi_apply _) measurable_const)
  have hseq : s = Set.Ioo (fun _ : Unit => a) (fun _ : Unit => b) :=
    unitMomentum_coordinate_Ioo_eq a b
  have hdensity : Measurable (fun p : Momentum Unit =>
      relativisticBoltzmannWeight 1 1 (euclideanNorm p)) :=
    (continuous_relativisticBoltzmannWeight 1 1).measurable.comp
      continuous_euclideanNorm.measurable
  rw [← hseq]
  rw [euclideanRelativisticMomentumMeasure,
    withDensity_apply _ hs]
  rw [setLIntegral_pos_iff hdensity]
  have hsupport : Function.support (fun p : Momentum Unit =>
      relativisticBoltzmannWeight 1 1 (euclideanNorm p)) = Set.univ := by
    ext p
    simp [Function.mem_support,
      (relativisticBoltzmannWeight_pos 1 1 (euclideanNorm p)).ne']
  rw [hsupport, Set.univ_inter]
  have hbox : s =
      Set.pi Set.univ (fun _ : Unit => Set.Ioo a b) := by
    ext p
    change (a < p Unit.unit ∧ p Unit.unit < b) ↔
      ∀ i, i ∈ Set.univ → a < p i ∧ p i < b
    constructor
    · rintro hp i _hi
      simpa [Subsingleton.elim i Unit.unit] using hp
    · intro hp
      exact hp Unit.unit (Set.mem_univ _)
  rw [hbox, Real.volume_pi_Ioo]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_unit, pow_one]
  exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)

/-- Normalization preserves positivity of nonempty open momentum intervals. -/
theorem euclideanRelativisticMomentumProbability_unit_Ioo_pos
    {a b : ℝ} (hab : a < b) :
    0 < (euclideanRelativisticMomentumProbability Unit 1 1
      (by norm_num) (by norm_num) : Measure (Momentum Unit))
      (Set.Ioo (fun _ : Unit => a) (fun _ : Unit => b)) := by
  rw [euclideanRelativisticMomentumProbability_toMeasure]
  rw [Measure.coe_nnreal_smul_apply]
  have hpartition : 0 < euclideanRelativisticMomentumPartition Unit 1 1
      (by norm_num) (by norm_num) :=
    bot_lt_iff_ne_bot.mpr
      (euclideanRelativisticMomentumPartition_ne_zero Unit 1 1
        (by norm_num) (by norm_num))
  exact ENNReal.mul_pos
    (ENNReal.coe_pos.mpr (inv_pos.mpr hpartition)).ne'
    (euclideanRelativisticMomentumMeasure_unit_Ioo_pos hab).ne'

/-- Every nonempty open coordinate interval has positive probability under
the actual inverse-factor-transported one-dimensional Gaussian SoftAbs
momentum law. -/
theorem gaussianSoftAbsMomentumProbability_unit_Ioo_pos
    {a b : ℝ} (hab : a < b) :
    0 < (riemannianRelativisticMomentumProbability
      (gaussianSoftAbsMetric (ι := Unit)) 1 1 (by norm_num) (by norm_num) 0 :
        Measure (Momentum Unit))
      {p | a < p Unit.unit ∧ p Unit.unit < b} := by
  let k := softAbs 1 1
  let d := (Real.sqrt k)⁻¹
  let source : Set (Momentum Unit) :=
    {r | a * d < r Unit.unit ∧ r Unit.unit < b * d}
  let target : Set (Momentum Unit) :=
    {p | a < p Unit.unit ∧ p Unit.unit < b}
  have hk : 0 < k := softAbs_pos 1 (by norm_num) 1
  have hsqrt : 0 < Real.sqrt k := Real.sqrt_pos.2 hk
  have hd : 0 < d := inv_pos.mpr hsqrt
  have hsource : 0 <
      (euclideanRelativisticMomentumProbability Unit 1 1
        (by norm_num) (by norm_num) : Measure (Momentum Unit)) source := by
    change 0 <
      (euclideanRelativisticMomentumProbability Unit 1 1
        (by norm_num) (by norm_num) : Measure (Momentum Unit))
        {r | a * d < r Unit.unit ∧ r Unit.unit < b * d}
    rw [unitMomentum_coordinate_Ioo_eq]
    exact euclideanRelativisticMomentumProbability_unit_Ioo_pos
      (mul_lt_mul_of_pos_right hab hd)
  have htarget : MeasurableSet target := by
    exact (measurableSet_lt measurable_const (measurable_pi_apply _)).inter
      (measurableSet_lt (measurable_pi_apply _) measurable_const)
  change 0 < Measure.map
      ((gaussianSoftAbsMetric (ι := Unit)).factor 0).symm
      (euclideanRelativisticMomentumProbability Unit 1 1
        (by norm_num) (by norm_num) : Measure (Momentum Unit)) target
  rw [Measure.map_apply
    ((gaussianSoftAbsMetric (ι := Unit)).factor 0).symm.continuous.measurable
    htarget]
  apply lt_of_lt_of_le hsource
  apply measure_mono
  intro r hr
  change a <
      ((gaussianSoftAbsMetric (ι := Unit)).factor 0).symm r Unit.unit ∧
    ((gaussianSoftAbsMetric (ι := Unit)).factor 0).symm r Unit.unit < b
  change a <
      (diagonalSoftAbsFactor 1 (by norm_num) gaussianHessianDiagonal 0).symm
        r Unit.unit ∧
    (diagonalSoftAbsFactor 1 (by norm_num) gaussianHessianDiagonal 0).symm
        r Unit.unit < b
  rw [diagonalSoftAbsFactor_symm_apply]
  change a < Real.sqrt k * r Unit.unit ∧
    Real.sqrt k * r Unit.unit < b
  have hleft := mul_lt_mul_of_pos_left hr.1 hsqrt
  have hright := mul_lt_mul_of_pos_left hr.2 hsqrt
  dsimp [d] at hleft hright
  have ha : Real.sqrt k * (a * (Real.sqrt k)⁻¹) = a := by
    field_simp [hsqrt.ne']
  have hb : Real.sqrt k * (b * (Real.sqrt k)⁻¹) = b := by
    field_simp [hsqrt.ne']
  rw [ha] at hleft
  rw [hb] at hright
  exact ⟨hleft, hright⟩

/-- The actual inverse-factor-transported Gaussian SoftAbs momentum refresh
assigns positive probability to the central interval `(-1,1)`. The metric is
constant, so this probability is common to every position. -/
theorem gaussianSoftAbsMomentumProbability_central_pos :
    0 < (riemannianRelativisticMomentumProbability
      (gaussianSoftAbsMetric (ι := Unit)) 1 1 (by norm_num) (by norm_num) 0 :
        Measure (Momentum Unit))
      {p | -1 < p Unit.unit ∧ p Unit.unit < 1} := by
  let k := softAbs 1 1
  let d := (Real.sqrt k)⁻¹
  let source : Set (Momentum Unit) :=
    {r | -d < r Unit.unit ∧ r Unit.unit < d}
  let central : Set (Momentum Unit) :=
    {p | -1 < p Unit.unit ∧ p Unit.unit < 1}
  have hk : 0 < k := softAbs_pos 1 (by norm_num) 1
  have hsqrt : 0 < Real.sqrt k := Real.sqrt_pos.2 hk
  have hd : 0 < d := inv_pos.mpr hsqrt
  have hsource : 0 <
      (euclideanRelativisticMomentumProbability Unit 1 1
        (by norm_num) (by norm_num) : Measure (Momentum Unit)) source := by
    change 0 <
      (euclideanRelativisticMomentumProbability Unit 1 1
        (by norm_num) (by norm_num) : Measure (Momentum Unit))
        {r | -d < r Unit.unit ∧ r Unit.unit < d}
    rw [unitMomentum_coordinate_Ioo_eq]
    exact euclideanRelativisticMomentumProbability_unit_Ioo_pos
      (neg_lt_self hd)
  have hcentral : MeasurableSet central := by
    exact (measurableSet_lt measurable_const (measurable_pi_apply _)).inter
      (measurableSet_lt (measurable_pi_apply _) measurable_const)
  change 0 < Measure.map
      ((gaussianSoftAbsMetric (ι := Unit)).factor 0).symm
      (euclideanRelativisticMomentumProbability Unit 1 1
        (by norm_num) (by norm_num) : Measure (Momentum Unit)) central
  rw [Measure.map_apply
    ((gaussianSoftAbsMetric (ι := Unit)).factor 0).symm.continuous.measurable
    hcentral]
  apply lt_of_lt_of_le hsource
  apply measure_mono
  intro r hr
  change -1 <
      ((gaussianSoftAbsMetric (ι := Unit)).factor 0).symm r Unit.unit ∧
    ((gaussianSoftAbsMetric (ι := Unit)).factor 0).symm r Unit.unit < 1
  change -1 <
      (diagonalSoftAbsFactor 1 (by norm_num) gaussianHessianDiagonal 0).symm
        r Unit.unit ∧
    (diagonalSoftAbsFactor 1 (by norm_num) gaussianHessianDiagonal 0).symm
        r Unit.unit < 1
  rw [diagonalSoftAbsFactor_symm_apply]
  change -1 < Real.sqrt k * r Unit.unit ∧
    Real.sqrt k * r Unit.unit < 1
  have hleft := mul_lt_mul_of_pos_left hr.1 hsqrt
  have hright := mul_lt_mul_of_pos_left hr.2 hsqrt
  dsimp [d] at hleft hright
  rw [mul_neg, mul_inv_cancel₀ hsqrt.ne'] at hleft
  rw [mul_inv_cancel₀ hsqrt.ne'] at hright
  exact ⟨hleft, hright⟩

/-- The conditional momentum law is position-independent for the constant
Gaussian Hessian/SoftAbs metric. -/
theorem gaussianSoftAbsMomentumProbability_eq_zero
    (q : Position ι) :
    riemannianRelativisticMomentumProbability
        (gaussianSoftAbsMetric (ι := ι)) 1 1 (by norm_num) (by norm_num) q =
      riemannianRelativisticMomentumProbability
        (gaussianSoftAbsMetric (ι := ι)) 1 1 (by norm_num) (by norm_num) 0 := by
  rfl

/-- Every one-dimensional Gaussian SoftAbs momentum-refresh row assigns the
same strictly positive mass to the central interval. -/
theorem gaussianSoftAbsMomentumKernel_central_pos (q : Position Unit) :
    0 < riemannianMomentumKernel (gaussianSoftAbsMetric (ι := Unit)) 1 1
      (by norm_num) (by norm_num)
      (diagonalSoftAbs_isMeasurableRiemannianMomentumFamily
        1 (by norm_num) (gaussianHessianDiagonal (ι := Unit)) 1 1
        (by norm_num) (by norm_num)
        (measurable_gaussianHessianDiagonal (ι := Unit))) q
      {p | -1 < p Unit.unit ∧ p Unit.unit < 1} := by
  change 0 < (riemannianRelativisticMomentumProbability
    (gaussianSoftAbsMetric (ι := Unit)) 1 1 (by norm_num) (by norm_num) q :
      Measure (Momentum Unit)) {p | -1 < p Unit.unit ∧ p Unit.unit < 1}
  rw [gaussianSoftAbsMomentumProbability_eq_zero]
  exact gaussianSoftAbsMomentumProbability_central_pos

/-- End-to-end exact position invariance for endpoint-Metropolis GR-HMC on
the Gaussian target with its actual diagonal SoftAbs Hessian metric. -/
theorem gaussianSoftAbs_endpointGRHMC_invariant (ε : ℝ) :
    (positionEndpointMetropolisGRHMC (gaussianSoftAbsPotential (ι := ι))
      (gaussianSoftAbsMetric (ι := ι)) 1 1 (by norm_num) (by norm_num)
      (gaussianSoftAbsSelection (ι := ι)) gaussianSoftAbsSelection_valid
      (diagonalSoftAbs_isMeasurableRiemannianMomentumFamily
        1 (by norm_num) (gaussianHessianDiagonal (ι := ι)) 1 1
        (by norm_num) (by norm_num)
        (measurable_gaussianHessianDiagonal (ι := ι)))
      ε).Invariant
      (generalRelativisticPositionTarget (gaussianSoftAbsPotential (ι := ι))
        1 1 (by norm_num) (by norm_num)) := by
  exact diagonalSoftAbs_positionEndpointMetropolisGRHMC_invariant
    (measurable_gaussianSoftAbsPotential (ι := ι)) 1 (by norm_num)
    (gaussianHessianDiagonal (ι := ι))
    (measurable_gaussianHessianDiagonal (ι := ι))
    1 1 (by norm_num) (by norm_num)
    (gaussianSoftAbsSelection (ι := ι)) gaussianSoftAbsSelection_valid ε

/-- End-to-end exact position invariance for multinomial GR-HMC on the same
Gaussian diagonal-SoftAbs client. -/
theorem gaussianSoftAbs_multinomialGRHMC_invariant (ε : ℝ) (L : ℕ) :
    (positionMultinomialGRHMC (gaussianSoftAbsPotential (ι := ι))
      (gaussianSoftAbsMetric (ι := ι)) 1 1 (by norm_num) (by norm_num)
      (gaussianSoftAbsSelection (ι := ι)) gaussianSoftAbsSelection_valid
      (measurable_diagonalSoftAbs_generalRelativisticHamiltonian
        (gaussianSoftAbsPotential (ι := ι))
        (measurable_gaussianSoftAbsPotential (ι := ι))
        1 (by norm_num) (gaussianHessianDiagonal (ι := ι))
        (measurable_gaussianHessianDiagonal (ι := ι)) 1 1)
      (diagonalSoftAbs_isMeasurableRiemannianMomentumFamily
        1 (by norm_num) (gaussianHessianDiagonal (ι := ι)) 1 1
        (by norm_num) (by norm_num)
        (measurable_gaussianHessianDiagonal (ι := ι)))
      ε L).Invariant
      (generalRelativisticPositionTarget (gaussianSoftAbsPotential (ι := ι))
        1 1 (by norm_num) (by norm_num)) := by
  exact diagonalSoftAbs_positionMultinomialGRHMC_invariant
    (measurable_gaussianSoftAbsPotential (ι := ι)) 1 (by norm_num)
    (gaussianHessianDiagonal (ι := ι))
    (measurable_gaussianHessianDiagonal (ι := ι))
    1 1 (by norm_num) (by norm_num)
    (gaussianSoftAbsSelection (ι := ι)) gaussianSoftAbsSelection_valid ε L

end Mcmc.Executable.Continuous
