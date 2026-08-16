import Mcmc.Executable.Continuous.SeparableGeneralizedLeapfrog
import Mcmc.Relativistic.SoftAbsKernel

/-!
# Executable Gaussian diagonal-SoftAbs GR-HMC client

The standard Gaussian potential has constant Hessian diagonal `1`. Applying
SoftAbs therefore gives a genuine, non-identity diagonal SoftAbs metric that
is constant in position. The generalized implicit equations collapse to the
explicit separable metric leapfrog, whose measurability, uniqueness,
reversibility, and exact phase-volume preservation are already certified.
-/

namespace Mcmc.Executable.Continuous

open Mcmc.Hamiltonian Mcmc.Relativistic MeasureTheory ProbabilityTheory

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
