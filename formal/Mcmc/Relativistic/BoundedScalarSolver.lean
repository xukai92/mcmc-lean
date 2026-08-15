import Mcmc.Relativistic.ScalarMetric
import Mcmc.Relativistic.PositionDependentSolver
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# A bounded position-dependent GR-HMC solver model

The quadratic scalar metric is a useful exact calculus example, but its
derivatives grow at infinity and therefore do not give a global contraction
on the complete real phase space.  This module uses the bounded positive
factor `2 + sin q` in one dimension.  A compensating potential cancels the
metric log-determinant term, leaving the complete Hamiltonian

`H(q,p) = sqrt (1 + (scale(q) * p)^2)`.

Both generalized-leapfrog fixed-point derivatives are globally bounded, so
this is the concrete metric client for a nonzero-step exact solver.
-/

namespace Mcmc.Relativistic

open Mcmc.Hamiltonian MeasureTheory Filter Topology

/-- Smooth bounded scalar factor, globally between one and three. -/
noncomputable def boundedScalarScale (q : Position Unit) : ℝ :=
  2 + Real.sin (q Unit.unit)

theorem boundedScalarScale_pos (q : Position Unit) :
    0 < boundedScalarScale q := by
  unfold boundedScalarScale
  have h := Real.neg_one_le_sin (q Unit.unit)
  linarith

theorem boundedScalarScale_le_three (q : Position Unit) :
    boundedScalarScale q ≤ 3 := by
  unfold boundedScalarScale
  have h := Real.sin_le_one (q Unit.unit)
  linarith

theorem differentiable_boundedScalarScale :
    Differentiable ℝ boundedScalarScale := by
  unfold boundedScalarScale
  fun_prop

theorem measurable_boundedScalarScale : Measurable boundedScalarScale :=
  differentiable_boundedScalarScale.continuous.measurable

theorem boundedScalarScale_nonconstant :
    boundedScalarScale (fun _ => 0) ≠
      boundedScalarScale (fun _ => Real.pi / 2) := by
  simp [boundedScalarScale, Real.sin_pi_div_two]

/-- Globally positive, genuinely nonconstant scalar Riemannian metric. -/
noncomputable def boundedScalarRiemannianMetric :
    FactoredRiemannianMetric Unit :=
  scalarFactoredRiemannianMetric boundedScalarScale boundedScalarScale_pos

/-- Potential chosen to cancel the `logDet / 2` term of the scalar metric. -/
noncomputable def boundedScalarCompensatingPotential
    (q : Position Unit) : ℝ :=
  Real.log (boundedScalarScale q)

theorem differentiable_boundedScalarCompensatingPotential :
    Differentiable ℝ boundedScalarCompensatingPotential := by
  unfold boundedScalarCompensatingPotential
  exact Differentiable.log differentiable_boundedScalarScale
    (fun q => (boundedScalarScale_pos q).ne')

theorem measurable_boundedScalarCompensatingPotential :
    Measurable boundedScalarCompensatingPotential :=
  differentiable_boundedScalarCompensatingPotential.continuous.measurable

/-- The complete GR Hamiltonian after exact cancellation of the metric
normalization term. -/
noncomputable def boundedScalarHamiltonian (z : PhaseSpace Unit) : ℝ :=
  Real.sqrt (1 + (boundedScalarScale z.1 * z.2 Unit.unit) ^ 2)

theorem generalRelativisticHamiltonian_boundedScalar_eq
    (z : PhaseSpace Unit) :
    generalRelativisticHamiltonian boundedScalarCompensatingPotential
      boundedScalarRiemannianMetric 1 1 z = boundedScalarHamiltonian z := by
  unfold generalRelativisticHamiltonian
    riemannianRelativisticKineticEnergy boundedScalarCompensatingPotential
    boundedScalarRiemannianMetric boundedScalarHamiltonian
  rw [show (scalarFactoredRiemannianMetric boundedScalarScale
      boundedScalarScale_pos).logDet z.1 =
      -2 * Real.log (boundedScalarScale z.1) by
    simp [scalarFactoredRiemannianMetric,
      scalarFactorJacobian_unit_eq boundedScalarScale boundedScalarScale_pos]]
  simp only [scalarFactoredRiemannianMetric_factor_apply]
  unfold relativisticKineticEnergy squaredEuclideanNorm euclideanInner
  simp only [Finset.univ_unique, Finset.sum_singleton, Pi.smul_apply,
    smul_eq_mul, one_pow, one_mul]
  ring_nf

/-- Scalar relativistic velocity profile. -/
noncomputable def scalarVelocityProfile (x : ℝ) : ℝ :=
  x / scalarRelativisticProfile x

theorem abs_scalarVelocityProfile_le_one (x : ℝ) :
    |scalarVelocityProfile x| ≤ 1 :=
  abs_div_scalarRelativisticProfile_le_one x

theorem scalarRelativisticProfile_sq (x : ℝ) :
    scalarRelativisticProfile x ^ 2 = 1 + x ^ 2 := by
  unfold scalarRelativisticProfile
  exact Real.sq_sqrt (by positivity)

theorem differentiable_scalarRelativisticProfile :
    Differentiable ℝ scalarRelativisticProfile := by
  intro x
  unfold scalarRelativisticProfile
  apply HasDerivAt.differentiableAt
  apply HasDerivAt.sqrt ((((hasDerivAt_id x).pow 2).const_add 1))
  change 1 + x ^ 2 ≠ 0
  positivity

theorem deriv_scalarVelocityProfile (x : ℝ) :
    deriv scalarVelocityProfile x =
      1 / scalarRelativisticProfile x ^ 3 := by
  have hp : scalarRelativisticProfile x ≠ 0 :=
    (scalarRelativisticProfile_pos x).ne'
  unfold scalarVelocityProfile
  rw [show (fun y : ℝ => y / scalarRelativisticProfile y) =
      id / scalarRelativisticProfile by rfl]
  rw [deriv_div (differentiableAt_id) (by
    exact differentiable_scalarRelativisticProfile x) hp,
    deriv_scalarRelativisticProfile, deriv_id]
  simp only [id_eq]
  field_simp [hp]
  rw [scalarRelativisticProfile_sq]
  ring

/-- The scalar relativistic velocity is globally one-Lipschitz. -/
theorem scalarVelocityProfile_lipschitz :
    LipschitzWith 1 scalarVelocityProfile := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · exact differentiable_id.div differentiable_scalarRelativisticProfile
      (fun x => (scalarRelativisticProfile_pos x).ne')
  · intro x
    rw [deriv_scalarVelocityProfile]
    change |1 / scalarRelativisticProfile x ^ 3| ≤ 1
    rw [abs_div, abs_one, abs_pow,
      abs_of_pos (scalarRelativisticProfile_pos x)]
    rw [div_le_one (by
      exact pow_pos (scalarRelativisticProfile_pos x) 3)]
    have hp : 1 ≤ scalarRelativisticProfile x := by
      unfold scalarRelativisticProfile
      have hsquare := Real.sq_sqrt (show 0 ≤ 1 + x ^ 2 by positivity)
      have hnonneg := Real.sqrt_nonneg (1 + x ^ 2)
      nlinarith [sq_nonneg x]
    nlinarith [sq_nonneg (scalarRelativisticProfile x - 1)]

/-- Profile appearing in the position derivative. -/
noncomputable def scalarPositionProfile (x : ℝ) : ℝ :=
  x ^ 2 / scalarRelativisticProfile x

theorem deriv_scalarPositionProfile (x : ℝ) :
    deriv scalarPositionProfile x =
      2 * scalarVelocityProfile x - scalarVelocityProfile x ^ 3 := by
  have hp : scalarRelativisticProfile x ≠ 0 :=
    (scalarRelativisticProfile_pos x).ne'
  unfold scalarPositionProfile scalarVelocityProfile
  rw [show (fun y : ℝ => y ^ 2 / scalarRelativisticProfile y) =
      (fun y : ℝ => y ^ 2) / scalarRelativisticProfile by rfl]
  have hpow : deriv (fun y : ℝ => y ^ 2) x = 2 * x := by
    rw [show (fun y : ℝ => y ^ 2) = id ^ 2 by rfl,
      deriv_pow, deriv_id]
    simp [id_eq, mul_comm]
    fun_prop
  rw [deriv_div (by fun_prop) (by
    exact differentiable_scalarRelativisticProfile x) hp,
    hpow,
    deriv_scalarRelativisticProfile]
  field_simp [hp]

/-- A deliberately loose global bound is sufficient for the contraction
argument. -/
theorem scalarPositionProfile_lipschitz :
    LipschitzWith 3 scalarPositionProfile := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · exact (differentiable_id.pow 2).div
      differentiable_scalarRelativisticProfile
      (fun x => (scalarRelativisticProfile_pos x).ne')
  · intro x
    rw [deriv_scalarPositionProfile]
    change |2 * scalarVelocityProfile x - scalarVelocityProfile x ^ 3| ≤ 3
    calc
      _ ≤ 2 * |scalarVelocityProfile x| + |scalarVelocityProfile x| ^ 3 := by
        calc
          _ ≤ |2 * scalarVelocityProfile x| +
              |scalarVelocityProfile x ^ 3| := abs_sub _ _
          _ = _ := by
            rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_pow]
      _ ≤ 2 * 1 + 1 ^ 3 := by
        gcongr
        all_goals exact abs_scalarVelocityProfile_le_one x
      _ = 3 := by norm_num

theorem boundedScalarScale_lipschitz :
    LipschitzWith 1 (fun x : ℝ => 2 + Real.sin x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := Real.lipschitzWith_sin.dist_le_mul x y
  simpa [Real.dist_eq] using h

theorem differentiable_scalarVelocityProfile :
    Differentiable ℝ scalarVelocityProfile :=
  differentiable_id.div differentiable_scalarRelativisticProfile
    (fun x => (scalarRelativisticProfile_pos x).ne')

/-- Momentum derivative as a function of the positive scalar factor, with
momentum held fixed. -/
noncomputable def scaledVelocityProfile (p s : ℝ) : ℝ :=
  s * scalarVelocityProfile (s * p)

theorem deriv_scaledVelocityProfile (p s : ℝ) :
    deriv (scaledVelocityProfile p) s =
      scalarVelocityProfile (s * p) +
        (s * p) / scalarRelativisticProfile (s * p) ^ 3 := by
  let x := s * p
  have hvdiff : DifferentiableAt ℝ scalarVelocityProfile x :=
    differentiable_scalarVelocityProfile x
  have hv : HasDerivAt scalarVelocityProfile
      (1 / scalarRelativisticProfile x ^ 3) x := by
    rw [← deriv_scalarVelocityProfile x]
    exact hvdiff.hasDerivAt
  have hinner : HasDerivAt (fun t : ℝ => t * p) p s := by
    simpa using (hasDerivAt_id s).mul_const p
  have hcomp : HasDerivAt (fun t : ℝ => scalarVelocityProfile (t * p))
      ((1 / scalarRelativisticProfile x ^ 3) * p) s := by
    change HasDerivAt (scalarVelocityProfile ∘ fun t : ℝ => t * p)
      ((1 / scalarRelativisticProfile x ^ 3) * p) s
    exact hv.comp s hinner
  have hout := (hasDerivAt_id s).mul hcomp
  unfold scaledVelocityProfile
  have hout' : HasDerivAt (fun t : ℝ =>
      t * scalarVelocityProfile (t * p))
      (1 * scalarVelocityProfile (s * p) +
        s * ((1 / scalarRelativisticProfile x ^ 3) * p)) s := by
    exact hout.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => by simp)
  rw [hout'.deriv]
  dsimp [x]
  ring

theorem abs_div_scalarRelativisticProfile_cube_le_one (x : ℝ) :
    |x / scalarRelativisticProfile x ^ 3| ≤ 1 := by
  have hp : 0 < scalarRelativisticProfile x :=
    scalarRelativisticProfile_pos x
  have hprofile : 1 ≤ scalarRelativisticProfile x := by
    have hsquare := scalarRelativisticProfile_sq x
    nlinarith [sq_nonneg x, sq_nonneg (scalarRelativisticProfile x - 1)]
  rw [show x / scalarRelativisticProfile x ^ 3 =
      (x / scalarRelativisticProfile x) *
        (1 / scalarRelativisticProfile x ^ 2) by
    field_simp [hp.ne']]
  rw [abs_mul]
  calc
    _ ≤ 1 * 1 := mul_le_mul
      (abs_div_scalarRelativisticProfile_le_one x) ?_ (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1
  rw [abs_div, abs_one, abs_pow, abs_of_pos hp]
  rw [div_le_one (sq_pos_of_pos hp)]
  nlinarith [sq_nonneg (scalarRelativisticProfile x - 1)]

theorem scaledVelocityProfile_lipschitz (p : ℝ) :
    LipschitzWith 2 (scaledVelocityProfile p) := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro s
    unfold scaledVelocityProfile
    exact differentiableAt_id.mul
      (differentiable_scalarVelocityProfile.differentiableAt.comp s
        (by fun_prop))
  · intro s
    rw [deriv_scaledVelocityProfile]
    change |scalarVelocityProfile (s * p) +
      (s * p) / scalarRelativisticProfile (s * p) ^ 3| ≤ 2
    calc
      _ ≤ |scalarVelocityProfile (s * p)| +
          |(s * p) / scalarRelativisticProfile (s * p) ^ 3| := abs_add_le _ _
      _ ≤ 1 + 1 := add_le_add
        (abs_scalarVelocityProfile_le_one _) (abs_div_scalarRelativisticProfile_cube_le_one _)
      _ = 2 := by norm_num

/-- Actual position derivative of the bounded complete GR Hamiltonian. -/
noncomputable def boundedScalarPositionDerivative :
    PhaseSpace Unit → Position Unit := fun z _ =>
  Real.cos (z.1 Unit.unit) / boundedScalarScale z.1 *
    scalarPositionProfile
      (boundedScalarScale z.1 * z.2 Unit.unit)

/-- Actual momentum derivative of the bounded complete GR Hamiltonian. -/
noncomputable def boundedScalarMomentumDerivative :
    PhaseSpace Unit → Momentum Unit := fun z _ =>
  scaledVelocityProfile (z.2 Unit.unit) (boundedScalarScale z.1)

theorem hasDerivAt_boundedScalarHamiltonian_position (q p : ℝ) :
    HasDerivAt (fun x => scalarRelativisticProfile ((2 + Real.sin x) * p))
      (Real.cos q / (2 + Real.sin q) *
        scalarPositionProfile ((2 + Real.sin q) * p)) q := by
  let s := 2 + Real.sin q
  let y := s * p
  have hs : HasDerivAt (fun x : ℝ => 2 + Real.sin x) (Real.cos q) q := by
    simpa using (Real.hasDerivAt_sin q).const_add 2
  have hinner : HasDerivAt (fun x : ℝ => (2 + Real.sin x) * p)
      (Real.cos q * p) q := hs.mul_const p
  have hprofile : HasDerivAt scalarRelativisticProfile
      (y / scalarRelativisticProfile y) y := by
    rw [← deriv_scalarRelativisticProfile y]
    exact (differentiable_scalarRelativisticProfile y).hasDerivAt
  have hcomp := hprofile.comp q hinner
  apply hcomp.congr_deriv
  have hspos : 0 < s := by
    dsimp [s]
    have := Real.neg_one_le_sin q
    linarith
  unfold scalarPositionProfile
  dsimp [y, s]
  field_simp [hspos.ne']

theorem hasDerivAt_boundedScalarHamiltonian_momentum (q p : ℝ) :
    HasDerivAt (fun x => scalarRelativisticProfile ((2 + Real.sin q) * x))
      (scaledVelocityProfile p (2 + Real.sin q)) p := by
  let s := 2 + Real.sin q
  let y := s * p
  have hinner : HasDerivAt (fun x : ℝ => s * x) s p := by
    simpa [mul_comm] using (hasDerivAt_id p).const_mul s
  have hprofile : HasDerivAt scalarRelativisticProfile
      (y / scalarRelativisticProfile y) y := by
    rw [← deriv_scalarRelativisticProfile y]
    exact (differentiable_scalarRelativisticProfile y).hasDerivAt
  have hcomp := hprofile.comp p hinner
  rw [show (fun x => scalarRelativisticProfile ((2 + Real.sin q) * x)) =
      scalarRelativisticProfile ∘ (fun x : ℝ => s * x) by
    funext x
    rfl]
  apply hcomp.congr_deriv
  unfold scaledVelocityProfile scalarVelocityProfile
  dsimp [y, s]
  ring

/-- The callbacks consumed by the implicit solver are the true coordinate
derivatives of the complete bounded-metric GR Hamiltonian. -/
theorem boundedScalarDerivative_callbacks_correct (z : PhaseSpace Unit) :
    HasDerivAt
        (fun q => generalRelativisticHamiltonian
          boundedScalarCompensatingPotential boundedScalarRiemannianMetric
          1 1 ((fun _ => q), z.2))
        (boundedScalarPositionDerivative z Unit.unit) (z.1 Unit.unit) ∧
      HasDerivAt
        (fun p => generalRelativisticHamiltonian
          boundedScalarCompensatingPotential boundedScalarRiemannianMetric
          1 1 (z.1, (fun _ => p)))
        (boundedScalarMomentumDerivative z Unit.unit) (z.2 Unit.unit) := by
  constructor
  · rw [show (fun q => generalRelativisticHamiltonian
        boundedScalarCompensatingPotential boundedScalarRiemannianMetric
        1 1 ((fun _ => q), z.2)) =
      fun q => scalarRelativisticProfile
        ((2 + Real.sin q) * z.2 Unit.unit) by
      funext q
      rw [generalRelativisticHamiltonian_boundedScalar_eq]
      simp [boundedScalarHamiltonian, boundedScalarScale,
        scalarRelativisticProfile]]
    simpa [boundedScalarPositionDerivative, boundedScalarScale] using
      hasDerivAt_boundedScalarHamiltonian_position
        (z.1 Unit.unit) (z.2 Unit.unit)
  · rw [show (fun p => generalRelativisticHamiltonian
        boundedScalarCompensatingPotential boundedScalarRiemannianMetric
        1 1 (z.1, (fun _ => p))) =
      fun p => scalarRelativisticProfile
        ((2 + Real.sin (z.1 Unit.unit)) * p) by
      funext p
      rw [generalRelativisticHamiltonian_boundedScalar_eq]
      simp [boundedScalarHamiltonian, boundedScalarScale,
        scalarRelativisticProfile]]
    simpa [boundedScalarMomentumDerivative, boundedScalarScale] using
      hasDerivAt_boundedScalarHamiltonian_momentum
        (z.1 Unit.unit) (z.2 Unit.unit)

@[simp] theorem boundedScalarPositionDerivative_flip (z : PhaseSpace Unit) :
    boundedScalarPositionDerivative (momentumFlip z) =
      boundedScalarPositionDerivative z := by
  ext i
  simp [boundedScalarPositionDerivative, momentumFlip,
    scalarPositionProfile, scalarRelativisticProfile]

@[simp] theorem boundedScalarMomentumDerivative_flip (z : PhaseSpace Unit) :
    boundedScalarMomentumDerivative (momentumFlip z) =
      -boundedScalarMomentumDerivative z := by
  ext i
  simp [boundedScalarMomentumDerivative, momentumFlip,
    scaledVelocityProfile, scalarVelocityProfile,
    scalarRelativisticProfile]
  ring

@[simp] theorem boundedScalarPositionDerivative_neg_momentum
    (q : Position Unit) (p : Momentum Unit) :
    boundedScalarPositionDerivative (q, -p) =
      boundedScalarPositionDerivative (q, p) := by
  simpa [momentumFlip] using
    boundedScalarPositionDerivative_flip (q, p)

@[simp] theorem boundedScalarMomentumDerivative_neg_momentum
    (q : Position Unit) (p : Momentum Unit) :
    boundedScalarMomentumDerivative (q, -p) =
      -boundedScalarMomentumDerivative (q, p) := by
  simpa [momentumFlip] using
    boundedScalarMomentumDerivative_flip (q, p)

theorem boundedScalarPositionDerivative_lipschitz_momentum
    (q : Position Unit) :
    LipschitzWith 3 (fun p : Momentum Unit =>
      boundedScalarPositionDerivative (q, p)) := by
  apply LipschitzWith.of_dist_le_mul
  intro p r
  rw [dist_eq_norm, norm_pi_unit, dist_eq_norm, norm_pi_unit]
  change |Real.cos (q Unit.unit) / boundedScalarScale q *
      scalarPositionProfile (boundedScalarScale q * p Unit.unit) -
    Real.cos (q Unit.unit) / boundedScalarScale q *
      scalarPositionProfile (boundedScalarScale q * r Unit.unit)| ≤
    3 * |p Unit.unit - r Unit.unit|
  have hspos := boundedScalarScale_pos q
  have hprofile := scalarPositionProfile_lipschitz.dist_le_mul
    (boundedScalarScale q * p Unit.unit)
    (boundedScalarScale q * r Unit.unit)
  have hcos : |Real.cos (q Unit.unit)| ≤ 1 := Real.abs_cos_le_one _
  calc
    _ = |Real.cos (q Unit.unit) / boundedScalarScale q| *
        |scalarPositionProfile (boundedScalarScale q * p Unit.unit) -
          scalarPositionProfile (boundedScalarScale q * r Unit.unit)| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ |Real.cos (q Unit.unit) / boundedScalarScale q| *
        (3 * |(boundedScalarScale q * p Unit.unit) -
          (boundedScalarScale q * r Unit.unit)|) := by
      gcongr
      simpa [Real.dist_eq] using hprofile
    _ = 3 * |Real.cos (q Unit.unit)| *
        |p Unit.unit - r Unit.unit| := by
      rw [abs_div, abs_of_pos hspos]
      have hdiff : |boundedScalarScale q * p Unit.unit -
          boundedScalarScale q * r Unit.unit| =
          boundedScalarScale q * |p Unit.unit - r Unit.unit| := by
        rw [← mul_sub, abs_mul, abs_of_pos hspos]
      rw [hdiff]
      field_simp [hspos.ne']
    _ ≤ 3 * 1 * |p Unit.unit - r Unit.unit| := by gcongr
    _ = _ := by ring

theorem boundedScalarMomentumDerivative_lipschitz_position
    (p : Momentum Unit) :
    LipschitzWith 2 (fun q : Position Unit =>
      boundedScalarMomentumDerivative (q, p)) := by
  apply LipschitzWith.of_dist_le_mul
  intro q r
  rw [dist_eq_norm, norm_pi_unit, dist_eq_norm, norm_pi_unit]
  change |scaledVelocityProfile (p Unit.unit) (boundedScalarScale q) -
      scaledVelocityProfile (p Unit.unit) (boundedScalarScale r)| ≤
    2 * |q Unit.unit - r Unit.unit|
  have hv := (scaledVelocityProfile_lipschitz (p Unit.unit)).dist_le_mul
    (boundedScalarScale q) (boundedScalarScale r)
  have hs := boundedScalarScale_lipschitz.dist_le_mul
    (q Unit.unit) (r Unit.unit)
  calc
    _ ≤ 2 * |boundedScalarScale q - boundedScalarScale r| := by
      simpa [Real.dist_eq] using hv
    _ ≤ 2 * |q Unit.unit - r Unit.unit| := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa [boundedScalarScale, Real.dist_eq] using hs

noncomputable def boundedScalarHalfRate (ε : ℝ) : NNReal :=
  ⟨|ε / 2| * 3, mul_nonneg (abs_nonneg _) (by norm_num)⟩

noncomputable def boundedScalarPositionRate (ε : ℝ) : NNReal :=
  ⟨|ε / 2| * 2, mul_nonneg (abs_nonneg _) (by norm_num)⟩

theorem boundedScalar_halfMomentum_contracting (ε : ℝ)
    (hstep : |ε / 2| * 3 < 1) (z : PhaseSpace Unit) :
    ContractingWith (boundedScalarHalfRate ε)
      (halfMomentumFixedPointUpdate boundedScalarPositionDerivative ε z) := by
  constructor
  · exact hstep
  · apply LipschitzWith.of_dist_le_mul
    intro p r
    rw [dist_eq_norm, dist_eq_norm]
    change ‖(z.2 - (ε / 2) • boundedScalarPositionDerivative (z.1, p)) -
        (z.2 - (ε / 2) • boundedScalarPositionDerivative (z.1, r))‖ ≤
      (|ε / 2| * 3) * ‖p - r‖
    rw [show (z.2 - (ε / 2) • boundedScalarPositionDerivative (z.1, p)) -
        (z.2 - (ε / 2) • boundedScalarPositionDerivative (z.1, r)) =
      -(ε / 2) • (boundedScalarPositionDerivative (z.1, p) -
        boundedScalarPositionDerivative (z.1, r)) by module,
      norm_smul, Real.norm_eq_abs]
    rw [abs_neg]
    calc
      |ε / 2| * ‖boundedScalarPositionDerivative (z.1, p) -
          boundedScalarPositionDerivative (z.1, r)‖ ≤
        |ε / 2| * (3 * ‖p - r‖) := by
          gcongr
          exact (boundedScalarPositionDerivative_lipschitz_momentum z.1).dist_le_mul p r
      _ = _ := by ring

theorem boundedScalar_nextPosition_contracting (ε : ℝ)
    (hstep : |ε / 2| * 3 < 1) (q : Position Unit)
    (p : Momentum Unit) :
    ContractingWith (boundedScalarPositionRate ε)
      (positionFixedPointUpdate boundedScalarMomentumDerivative ε q p) := by
  constructor
  · change |ε / 2| * 2 < 1
    have hnonneg : 0 ≤ |ε / 2| := abs_nonneg _
    nlinarith
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    change ‖(q + (ε / 2) •
        (boundedScalarMomentumDerivative (q, p) +
          boundedScalarMomentumDerivative (x, p))) -
      (q + (ε / 2) •
        (boundedScalarMomentumDerivative (q, p) +
          boundedScalarMomentumDerivative (y, p)))‖ ≤
      (|ε / 2| * 2) * ‖x - y‖
    rw [show (q + (ε / 2) •
        (boundedScalarMomentumDerivative (q, p) +
          boundedScalarMomentumDerivative (x, p))) -
      (q + (ε / 2) •
        (boundedScalarMomentumDerivative (q, p) +
          boundedScalarMomentumDerivative (y, p))) =
      (ε / 2) • (boundedScalarMomentumDerivative (x, p) -
        boundedScalarMomentumDerivative (y, p)) by module,
      norm_smul, Real.norm_eq_abs]
    calc
      |ε / 2| * ‖boundedScalarMomentumDerivative (x, p) -
          boundedScalarMomentumDerivative (y, p)‖ ≤
        |ε / 2| * (2 * ‖x - y‖) := by
          gcongr
          exact (boundedScalarMomentumDerivative_lipschitz_position p).dist_le_mul x y
      _ = _ := by ring

/-- Exact Banach-selected generalized-leapfrog solver for an actual complete
position-dependent GR Hamiltonian at every nonzero step satisfying
`3 |ε| / 2 < 1`. -/
noncomputable def boundedScalarContractiveSolverAt (ε : ℝ)
    (hstep : |ε / 2| * 3 < 1) :
    ContractiveGeneralizedLeapfrogSolverAt
      boundedScalarPositionDerivative boundedScalarMomentumDerivative ε where
  halfRate _ := boundedScalarHalfRate ε
  halfContracting := boundedScalar_halfMomentum_contracting ε hstep
  positionRate _ _ := boundedScalarPositionRate ε
  positionContracting := boundedScalar_nextPosition_contracting ε hstep

theorem boundedScalar_finiteHalfMomentum_tendsto (ε : ℝ)
    (hstep : |ε / 2| * 3 < 1) (z : PhaseSpace Unit) :
    Tendsto (fun n => finiteHalfMomentum boundedScalarPositionDerivative n ε z)
      atTop (𝓝 ((boundedScalarContractiveSolverAt ε hstep).halfMomentum z)) := by
  let solver := boundedScalarContractiveSolverAt ε hstep
  change Tendsto _ _ (𝓝 ((solver.halfContracting z).fixedPoint
    (halfMomentumFixedPointUpdate boundedScalarPositionDerivative ε z)))
  exact finiteHalfMomentum_tendsto_fixedPoint boundedScalarPositionDerivative
    (solver.halfRate z) ε z (solver.halfContracting z)

theorem boundedScalar_finiteNextPosition_tendsto (ε : ℝ)
    (hstep : |ε / 2| * 3 < 1) (z : PhaseSpace Unit) :
    let solver := boundedScalarContractiveSolverAt ε hstep
    Tendsto (fun n => finiteNextPosition boundedScalarMomentumDerivative n ε
      z.1 (solver.halfMomentum z)) atTop (𝓝 (solver.nextPosition z)) := by
  dsimp only
  let solver := boundedScalarContractiveSolverAt ε hstep
  change Tendsto _ _ (𝓝 ((solver.positionContracting z.1
    (solver.halfMomentum z)).fixedPoint
      (positionFixedPointUpdate boundedScalarMomentumDerivative ε z.1
        (solver.halfMomentum z))))
  exact finiteNextPosition_tendsto_fixedPoint boundedScalarMomentumDerivative
    (solver.positionRate z.1 (solver.halfMomentum z)) ε z.1
    (solver.halfMomentum z)
    (solver.positionContracting z.1 (solver.halfMomentum z))

theorem measurable_boundedScalarPositionDerivative :
    Measurable boundedScalarPositionDerivative := by
  unfold boundedScalarPositionDerivative scalarPositionProfile
    scalarRelativisticProfile boundedScalarScale
  fun_prop

theorem measurable_boundedScalarMomentumDerivative :
    Measurable boundedScalarMomentumDerivative := by
  unfold boundedScalarMomentumDerivative scaledVelocityProfile
    scalarVelocityProfile scalarRelativisticProfile boundedScalarScale
  fun_prop

/-- The exact Banach-selected bounded-metric phase map is measurable. -/
theorem measurable_boundedScalarContractiveSolverAt_step (ε : ℝ)
    (hstep : |ε / 2| * 3 < 1) :
    Measurable (boundedScalarContractiveSolverAt ε hstep).step := by
  let solver := boundedScalarContractiveSolverAt ε hstep
  have hhalf : Measurable solver.halfMomentum := by
    refine measurable_of_tendsto_metrizable
      (f := fun n z => finiteHalfMomentum
        boundedScalarPositionDerivative n ε z)
      (g := solver.halfMomentum) ?_ ?_
    · intro n
      exact measurable_finiteHalfMomentum
        measurable_boundedScalarPositionDerivative n ε
    · rw [tendsto_pi_nhds]
      intro z
      exact boundedScalar_finiteHalfMomentum_tendsto ε hstep z
  have hnext : Measurable solver.nextPosition := by
    refine measurable_of_tendsto_metrizable
      (f := fun n z => finiteNextPosition boundedScalarMomentumDerivative n ε
        z.1 (solver.halfMomentum z))
      (g := solver.nextPosition) ?_ ?_
    · intro n
      exact (measurable_finiteNextPosition
        measurable_boundedScalarMomentumDerivative n ε).comp
          (measurable_fst.prodMk hhalf)
    · rw [tendsto_pi_nhds]
      intro z
      exact boundedScalar_finiteNextPosition_tendsto ε hstep z
  change Measurable fun z =>
    (solver.nextPosition z, solver.halfMomentum z - (ε / 2) •
      boundedScalarPositionDerivative
        (solver.nextPosition z, solver.halfMomentum z))
  exact hnext.prodMk (hhalf.sub
    ((measurable_const : Measurable (fun _ : PhaseSpace Unit => ε / 2)).smul
      (measurable_boundedScalarPositionDerivative.comp
        (hnext.prodMk hhalf))))

/-- Momentum parity plus uniqueness makes the exact bounded-metric solve
time-reversible across the certified `ε` and `-ε` steps. -/
theorem boundedScalarContractiveSolverAt_reversible (ε : ℝ)
    (hstep : |ε / 2| * 3 < 1) (z : PhaseSpace Unit) :
    let forward := boundedScalarContractiveSolverAt ε hstep
    let hbackward : |(-ε) / 2| * 3 < 1 := by
      simpa [neg_div] using hstep
    let backward := boundedScalarContractiveSolverAt (-ε) hbackward
    momentumFlip (forward.step (momentumFlip z)) = backward.step z := by
  dsimp only
  let hbackward : |(-ε) / 2| * 3 < 1 := by
    simpa [neg_div] using hstep
  let forward := boundedScalarContractiveSolverAt ε hstep
  let backward := boundedScalarContractiveSolverAt (-ε) hbackward
  let pHalf := forward.halfMomentum (momentumFlip z)
  have hforward := forward.satisfies (momentumFlip z)
  have hreverse : GeneralizedLeapfrogEquations boundedScalarPositionDerivative
      boundedScalarMomentumDerivative (-ε) z (-pHalf)
      (momentumFlip (forward.step (momentumFlip z))) := by
    rcases hforward with ⟨hp, hq, hpNext⟩
    constructor
    · ext i
      have hi := congrFun hp i
      simp [pHalf, momentumFlip] at hi ⊢
      linarith
    constructor
    · ext i
      have hi := congrFun hq i
      simp [pHalf, momentumFlip] at hi ⊢
      ring_nf at hi ⊢
      exact hi
    · ext i
      have hi := congrFun hpNext i
      simp [pHalf, momentumFlip] at hi ⊢
      linarith
  exact (backward.unique z (-pHalf)
    (momentumFlip (forward.step (momentumFlip z))) hreverse).2

/-- Remaining analytic certificate for promoting the actual bounded-metric
exact solver to a phase-volume-preserving generalized-leapfrog map. -/
structure BoundedScalarJacobianCertificate (ε : ℝ)
    (hstep : |ε / 2| * 3 < 1) : Prop where
  differentiable : Differentiable ℝ
    (boundedScalarContractiveSolverAt ε hstep).step
  absDetOne : ∀ z,
    |(fderiv ℝ (boundedScalarContractiveSolverAt ε hstep).step z).det| = 1

theorem BoundedScalarJacobianCertificate.volumePreserving
    {ε : ℝ} {hstep : |ε / 2| * 3 < 1}
    (certificate : BoundedScalarJacobianCertificate ε hstep) :
    MeasurePreserving (boundedScalarContractiveSolverAt ε hstep).step
      (phaseVolume : Measure (PhaseSpace Unit)) phaseVolume := by
  let hbackward : |(-ε) / 2| * 3 < 1 := by
    simpa [neg_div] using hstep
  let forward := boundedScalarContractiveSolverAt ε hstep
  let backward := boundedScalarContractiveSolverAt (-ε) hbackward
  letI : Measure.IsAddHaarMeasure
      (phaseVolume : Measure (PhaseSpace Unit)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  exact measurePreserving_of_bijective_differentiable_abs_det_one
    (phaseVolume : Measure (PhaseSpace Unit)) forward.step
    certificate.differentiable (forward.step_bijective backward)
    certificate.absDetOne

end Mcmc.Relativistic
