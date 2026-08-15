import Mcmc.Relativistic.ScalarMetric
import Mcmc.Relativistic.PositionDependentSolver
import Mcmc.Relativistic.FixedPointIteration
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

theorem continuous_scalarPositionProfile : Continuous scalarPositionProfile := by
  unfold scalarPositionProfile
  exact ((differentiable_id.pow 2).div differentiable_scalarRelativisticProfile
    (fun x => (scalarRelativisticProfile_pos x).ne')).continuous

theorem differentiable_scalarPositionProfile :
    Differentiable ℝ scalarPositionProfile := by
  unfold scalarPositionProfile
  exact (differentiable_id.pow 2).div differentiable_scalarRelativisticProfile
    (fun x => (scalarRelativisticProfile_pos x).ne')

/-- Momentum derivative as a function of the positive scalar factor, with
momentum held fixed. -/
noncomputable def scaledVelocityProfile (p s : ℝ) : ℝ :=
  s * scalarVelocityProfile (s * p)

theorem continuous_scaledVelocityProfile_uncurry :
    Continuous fun z : ℝ × ℝ => scaledVelocityProfile z.1 z.2 := by
  unfold scaledVelocityProfile
  exact continuous_snd.mul
    (differentiable_scalarVelocityProfile.continuous.comp
      (continuous_snd.mul continuous_fst))

theorem differentiable_scaledVelocityProfile_uncurry :
    Differentiable ℝ fun z : ℝ × ℝ => scaledVelocityProfile z.1 z.2 := by
  unfold scaledVelocityProfile
  exact differentiable_snd.mul
    (differentiable_scalarVelocityProfile.comp
      (differentiable_snd.mul differentiable_fst))

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

theorem continuous_boundedScalarPositionDerivative :
    Continuous boundedScalarPositionDerivative := by
  apply continuous_pi
  intro i
  have hq : Continuous fun z : PhaseSpace Unit => z.1 Unit.unit :=
    (continuous_apply Unit.unit).comp continuous_fst
  have hp : Continuous fun z : PhaseSpace Unit => z.2 Unit.unit :=
    (continuous_apply Unit.unit).comp continuous_snd
  have hs : Continuous fun z : PhaseSpace Unit => boundedScalarScale z.1 :=
    differentiable_boundedScalarScale.continuous.comp continuous_fst
  unfold boundedScalarPositionDerivative
  exact ((Real.continuous_cos.comp hq).div hs
      (fun z => (boundedScalarScale_pos z.1).ne')).mul
    (continuous_scalarPositionProfile.comp (hs.mul hp))

theorem continuous_boundedScalarMomentumDerivative :
    Continuous boundedScalarMomentumDerivative := by
  apply continuous_pi
  intro i
  have hp : Continuous fun z : PhaseSpace Unit => z.2 Unit.unit :=
    (continuous_apply Unit.unit).comp continuous_snd
  have hs : Continuous fun z : PhaseSpace Unit => boundedScalarScale z.1 :=
    differentiable_boundedScalarScale.continuous.comp continuous_fst
  unfold boundedScalarMomentumDerivative
  exact continuous_scaledVelocityProfile_uncurry.comp (hp.prodMk hs)

/-- Scalar-coordinate form of the position callback. Keeping this map on
`ℝ × ℝ` avoids elaboration blowups from differentiating through the
definitionally equivalent `Unit → ℝ` representation. -/
noncomputable def boundedScalarPositionDerivativeReal (z : ℝ × ℝ) : ℝ :=
  Real.cos z.1 / (2 + Real.sin z.1) *
    scalarPositionProfile ((2 + Real.sin z.1) * z.2)

noncomputable def boundedScalarLogDerivativeReal (q : ℝ) : ℝ :=
  Real.cos q / (2 + Real.sin q)

theorem differentiable_boundedScalarLogDerivativeReal :
    Differentiable ℝ boundedScalarLogDerivativeReal := by
  have hs : Differentiable ℝ fun q : ℝ => 2 + Real.sin q := by fun_prop
  unfold boundedScalarLogDerivativeReal
  exact Real.differentiable_cos.div hs
    (fun q => by
      have := Real.neg_one_le_sin q
      linarith)

/-- Scalar-coordinate form of the momentum callback. -/
noncomputable def boundedScalarMomentumDerivativeReal (z : ℝ × ℝ) : ℝ :=
  scaledVelocityProfile z.2 (2 + Real.sin z.1)

attribute [fun_prop] differentiable_scalarPositionProfile
  differentiable_scaledVelocityProfile_uncurry

theorem differentiable_boundedScalarPositionDerivativeReal :
    Differentiable ℝ boundedScalarPositionDerivativeReal := by
  rw [show boundedScalarPositionDerivativeReal = fun z : ℝ × ℝ =>
      boundedScalarLogDerivativeReal z.1 *
        scalarPositionProfile ((2 + Real.sin z.1) * z.2) by rfl]
  exact (differentiable_boundedScalarLogDerivativeReal.comp
      differentiable_fst).mul
    (differentiable_scalarPositionProfile.comp
      (((differentiable_const (c := (2 : ℝ))).add
        (Real.differentiable_sin.comp differentiable_fst)).mul
          differentiable_snd))

theorem differentiable_boundedScalarMomentumDerivativeReal :
    Differentiable ℝ boundedScalarMomentumDerivativeReal := by
  unfold boundedScalarMomentumDerivativeReal
  fun_prop

attribute [fun_prop] differentiable_boundedScalarPositionDerivativeReal
  differentiable_boundedScalarMomentumDerivativeReal

noncomputable def boundedScalarIncomingMapReal (ε : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1, z.2 + (ε / 2) * boundedScalarPositionDerivativeReal z)

noncomputable def boundedScalarRightMapReal (ε : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1 + (ε / 2) * boundedScalarMomentumDerivativeReal z, z.2)

noncomputable def boundedScalarLeftMapReal (ε : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1 - (ε / 2) * boundedScalarMomentumDerivativeReal z, z.2)

noncomputable def boundedScalarOutgoingMapReal (ε : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1, z.2 - (ε / 2) * boundedScalarPositionDerivativeReal z)

theorem differentiable_boundedScalarIncomingMapReal (ε : ℝ) :
    Differentiable ℝ (boundedScalarIncomingMapReal ε) := by
  unfold boundedScalarIncomingMapReal
  fun_prop

theorem differentiable_boundedScalarRightMapReal (ε : ℝ) :
    Differentiable ℝ (boundedScalarRightMapReal ε) := by
  unfold boundedScalarRightMapReal
  fun_prop

theorem differentiable_boundedScalarLeftMapReal (ε : ℝ) :
    Differentiable ℝ (boundedScalarLeftMapReal ε) := by
  unfold boundedScalarLeftMapReal
  fun_prop

theorem differentiable_boundedScalarOutgoingMapReal (ε : ℝ) :
    Differentiable ℝ (boundedScalarOutgoingMapReal ε) := by
  unfold boundedScalarOutgoingMapReal
  fun_prop

/-- Explicit two-by-two derivative of the incoming triangular map. -/
noncomputable def boundedScalarIncomingFDerivReal (ε : ℝ) (z : ℝ × ℝ) :
    ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![1, 0;
      (ε / 2) * fderiv ℝ boundedScalarPositionDerivativeReal z (1, 0),
      1 + (ε / 2) *
        fderiv ℝ boundedScalarPositionDerivativeReal z (0, 1)]).toContinuousLinearMap

theorem hasFDerivAt_boundedScalarIncomingMapReal (ε : ℝ) (z : ℝ × ℝ) :
    HasFDerivAt (boundedScalarIncomingMapReal ε)
      (boundedScalarIncomingFDerivReal ε z) z := by
  unfold boundedScalarIncomingFDerivReal boundedScalarIncomingMapReal
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  convert! HasFDerivAt.prodMk (𝕜 := ℝ) hasFDerivAt_fst
    (hasFDerivAt_snd.add
      ((differentiable_boundedScalarPositionDerivativeReal z).hasFDerivAt.const_mul
        (ε / 2))) using 2
  · simp
  · apply ContinuousLinearMap.ext
    intro v
    rcases v with ⟨v₁, v₂⟩
    have hv : fderiv ℝ boundedScalarPositionDerivativeReal z (v₁, v₂) =
        v₁ * fderiv ℝ boundedScalarPositionDerivativeReal z (1, 0) +
          v₂ * fderiv ℝ boundedScalarPositionDerivativeReal z (0, 1) := by
      have hvec : (v₁, v₂) = v₁ • (1, 0) + v₂ • (0, 1) := by
        ext <;> simp
      simpa only [map_add, map_smul, smul_eq_mul] using
        congrArg (fderiv ℝ boundedScalarPositionDerivativeReal z) hvec
    change (ε / 2 * fderiv ℝ boundedScalarPositionDerivativeReal z (1, 0)) * v₁ +
        (1 + ε / 2 * fderiv ℝ boundedScalarPositionDerivativeReal z (0, 1)) * v₂ =
      v₂ + ε / 2 * fderiv ℝ boundedScalarPositionDerivativeReal z (v₁, v₂)
    rw [hv]
    ring

theorem det_boundedScalarIncomingFDerivReal (ε : ℝ) (z : ℝ × ℝ) :
    (boundedScalarIncomingFDerivReal ε z).det =
      1 + (ε / 2) *
        fderiv ℝ boundedScalarPositionDerivativeReal z (0, 1) := by
  unfold boundedScalarIncomingFDerivReal
  simp only [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of]
  ring

theorem fderiv_boundedScalarPositionDerivativeReal_snd (q p : ℝ) :
    fderiv ℝ boundedScalarPositionDerivativeReal (q, p) (0, 1) =
      deriv (fun r => Real.cos q / (2 + Real.sin q) *
        scalarPositionProfile ((2 + Real.sin q) * r)) p := by
  have hcomp :=
    (differentiable_boundedScalarPositionDerivativeReal (q, p)).hasFDerivAt.comp
      p (hasFDerivAt_prodMk_right q p)
  have hderiv : HasDerivAt
      (fun r => Real.cos q / (2 + Real.sin q) *
        scalarPositionProfile ((2 + Real.sin q) * r))
      (fderiv ℝ boundedScalarPositionDerivativeReal (q, p) (0, 1)) p := by
    convert! hcomp.hasDerivAt using 1
  rw [hderiv.deriv]

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

theorem continuous_boundedScalarContractiveSolverAt_halfMomentum (ε : ℝ)
    (hstep : |ε / 2| * 3 < 1) :
    Continuous (boundedScalarContractiveSolverAt ε hstep).halfMomentum := by
  let K := boundedScalarHalfRate ε
  let update := halfMomentumFixedPointUpdate boundedScalarPositionDerivative ε
  have hin : Continuous fun z : PhaseSpace Unit × Momentum Unit =>
      (z.1.1, z.2) := continuous_fst.fst.prodMk continuous_snd
  have he : Continuous fun _ : PhaseSpace Unit × Momentum Unit => ε / 2 :=
    continuous_const
  have hjoint : Continuous fun z : PhaseSpace Unit × Momentum Unit =>
      update z.1 z.2 := by
    unfold update halfMomentumFixedPointUpdate
    exact continuous_fst.snd.sub
      (he.smul (continuous_boundedScalarPositionDerivative.comp hin))
  have hlip : ∀ z, LipschitzWith K (update z) := fun z =>
    (boundedScalar_halfMomentum_contracting ε hstep z).2
  exact continuous_fixedPoint_of_continuous_uniform_contracting
    K hstep update hjoint hlip

theorem continuous_boundedScalarContractiveSolverAt_nextPosition (ε : ℝ)
    (hstep : |ε / 2| * 3 < 1) :
    Continuous (boundedScalarContractiveSolverAt ε hstep).nextPosition := by
  let K := boundedScalarPositionRate ε
  let update : (Position Unit × Momentum Unit) → Position Unit → Position Unit :=
    fun z => positionFixedPointUpdate boundedScalarMomentumDerivative ε z.1 z.2
  have hK : (K : ℝ) < 1 := by
    change |ε / 2| * 2 < 1
    nlinarith [abs_nonneg (ε / 2)]
  have hleft : Continuous fun z :
      (Position Unit × Momentum Unit) × Position Unit => (z.1.1, z.1.2) :=
    continuous_fst.fst.prodMk continuous_fst.snd
  have hright : Continuous fun z :
      (Position Unit × Momentum Unit) × Position Unit => (z.2, z.1.2) :=
    continuous_snd.prodMk continuous_fst.snd
  have he : Continuous fun _ :
      (Position Unit × Momentum Unit) × Position Unit => ε / 2 := continuous_const
  have hjoint : Continuous fun z :
      (Position Unit × Momentum Unit) × Position Unit => update z.1 z.2 := by
    unfold update positionFixedPointUpdate
    exact continuous_fst.fst.add (he.smul
      ((continuous_boundedScalarMomentumDerivative.comp hleft).add
        (continuous_boundedScalarMomentumDerivative.comp hright)))
  have hlip : ∀ z, LipschitzWith K (update z) := fun z =>
    (boundedScalar_nextPosition_contracting ε hstep z.1 z.2).2
  have hbase := continuous_fixedPoint_of_continuous_uniform_contracting
    K hK update hjoint hlip
  let solver := boundedScalarContractiveSolverAt ε hstep
  exact hbase.comp (continuous_fst.prodMk
    (continuous_boundedScalarContractiveSolverAt_halfMomentum ε hstep))

theorem continuous_boundedScalarContractiveSolverAt_step (ε : ℝ)
    (hstep : |ε / 2| * 3 < 1) :
    Continuous (boundedScalarContractiveSolverAt ε hstep).step := by
  let solver := boundedScalarContractiveSolverAt ε hstep
  have hhalf := continuous_boundedScalarContractiveSolverAt_halfMomentum ε hstep
  have hnext := continuous_boundedScalarContractiveSolverAt_nextPosition ε hstep
  have he : Continuous fun _ : PhaseSpace Unit => ε / 2 := continuous_const
  change Continuous fun z =>
    (solver.nextPosition z, solver.halfMomentum z - (ε / 2) •
      boundedScalarPositionDerivative
        (solver.nextPosition z, solver.halfMomentum z))
  exact hnext.prodMk (hhalf.sub (he.smul
    (continuous_boundedScalarPositionDerivative.comp (hnext.prodMk hhalf))))

noncomputable def boundedScalarPhaseOfReal (z : ℝ × ℝ) : PhaseSpace Unit :=
  (fun _ => z.1, fun _ => z.2)

noncomputable def boundedScalarRealOfPhase (z : PhaseSpace Unit) : ℝ × ℝ :=
  (z.1 Unit.unit, z.2 Unit.unit)

@[simp] theorem boundedScalarRealOfPhase_phaseOfReal (z : ℝ × ℝ) :
    boundedScalarRealOfPhase (boundedScalarPhaseOfReal z) = z := by
  rcases z with ⟨q, p⟩
  rfl

@[simp] theorem boundedScalarPhaseOfReal_realOfPhase (z : PhaseSpace Unit) :
    boundedScalarPhaseOfReal (boundedScalarRealOfPhase z) = z := by
  ext i <;> cases i <;> rfl

theorem continuous_boundedScalarPhaseOfReal :
    Continuous boundedScalarPhaseOfReal := by
  unfold boundedScalarPhaseOfReal
  fun_prop

theorem continuous_boundedScalarRealOfPhase :
    Continuous boundedScalarRealOfPhase := by
  unfold boundedScalarRealOfPhase
  fun_prop

/-- Scalar-coordinate global inverse selected by the first Banach solve. -/
noncomputable def boundedScalarHalfSolveReal (ε : ℝ)
    (hstep : |ε / 2| * 3 < 1) (z : ℝ × ℝ) : ℝ × ℝ :=
  let solver := boundedScalarContractiveSolverAt ε hstep
  (z.1, solver.halfMomentum (boundedScalarPhaseOfReal z) Unit.unit)

theorem continuous_boundedScalarHalfSolveReal (ε : ℝ)
    (hstep : |ε / 2| * 3 < 1) :
    Continuous (boundedScalarHalfSolveReal ε hstep) := by
  unfold boundedScalarHalfSolveReal
  exact continuous_fst.prodMk
    (((continuous_apply Unit.unit).comp
      (continuous_boundedScalarContractiveSolverAt_halfMomentum ε hstep)).comp
        continuous_boundedScalarPhaseOfReal)

theorem boundedScalarIncomingMapReal_leftInverse_halfSolveReal
    (ε : ℝ) (hstep : |ε / 2| * 3 < 1) :
    Function.LeftInverse (boundedScalarIncomingMapReal ε)
      (boundedScalarHalfSolveReal ε hstep) := by
  intro z
  let solver := boundedScalarContractiveSolverAt ε hstep
  have hp := (solver.satisfies (boundedScalarPhaseOfReal z)).1
  ext
  · rfl
  · have hi := congrFun hp Unit.unit
    simp [boundedScalarHalfSolveReal, boundedScalarIncomingMapReal,
      boundedScalarPositionDerivativeReal, boundedScalarPositionDerivative,
      boundedScalarPhaseOfReal, boundedScalarScale, scalarPositionProfile] at hi ⊢
    linarith

/-! The four explicit triangular maps below expose the exact inverse-map
decomposition needed by the differentiability proof. -/

noncomputable def boundedScalarIncomingMap (ε : ℝ) :
    PhaseSpace Unit → PhaseSpace Unit := fun z =>
  (z.1, z.2 + (ε / 2) • boundedScalarPositionDerivative z)

noncomputable def boundedScalarRightMap (ε : ℝ) :
    PhaseSpace Unit → PhaseSpace Unit := fun z =>
  (z.1 + (ε / 2) • boundedScalarMomentumDerivative z, z.2)

noncomputable def boundedScalarLeftMap (ε : ℝ) :
    PhaseSpace Unit → PhaseSpace Unit := fun z =>
  (z.1 - (ε / 2) • boundedScalarMomentumDerivative z, z.2)

noncomputable def boundedScalarOutgoingMap (ε : ℝ) :
    PhaseSpace Unit → PhaseSpace Unit := fun z =>
  (z.1, z.2 - (ε / 2) • boundedScalarPositionDerivative z)

/-- The first implicit solve is a global right inverse of the incoming
triangular map. -/
theorem boundedScalarIncomingMap_halfMomentum
    (ε : ℝ) (hstep : |ε / 2| * 3 < 1) (z : PhaseSpace Unit) :
    boundedScalarIncomingMap ε
      (z.1, (boundedScalarContractiveSolverAt ε hstep).halfMomentum z) = z := by
  let solver := boundedScalarContractiveSolverAt ε hstep
  have hp := (solver.satisfies z).1
  ext i
  · rfl
  · have hi := congrFun hp i
    simp [boundedScalarIncomingMap] at hi ⊢
    linarith

/-- The implicit position equation says that the right explicit triangular
map followed by the selected solve lands in the left map's image. -/
theorem boundedScalarRightMap_eq_leftMap_nextPosition
    (ε : ℝ) (hstep : |ε / 2| * 3 < 1) (z : PhaseSpace Unit) :
    let solver := boundedScalarContractiveSolverAt ε hstep
    boundedScalarRightMap ε (z.1, solver.halfMomentum z) =
      boundedScalarLeftMap ε
        (solver.nextPosition z, solver.halfMomentum z) := by
  dsimp only
  let solver := boundedScalarContractiveSolverAt ε hstep
  have hq : solver.nextPosition z = z.1 + (ε / 2) •
      (boundedScalarMomentumDerivative (z.1, solver.halfMomentum z) +
        boundedScalarMomentumDerivative
          (solver.nextPosition z, solver.halfMomentum z)) := by
    simpa [ContractiveGeneralizedLeapfrogSolverAt.step] using
      (solver.satisfies z).2.1
  ext i
  · have hi := congrFun hq i
    simp [boundedScalarRightMap, boundedScalarLeftMap] at hi ⊢
    linarith
  · rfl

/-- The final explicit triangular map is definitionally the selected full
generalized-leapfrog step after the two implicit solves. -/
theorem boundedScalarOutgoingMap_nextPosition
    (ε : ℝ) (hstep : |ε / 2| * 3 < 1) (z : PhaseSpace Unit) :
    let solver := boundedScalarContractiveSolverAt ε hstep
    boundedScalarOutgoingMap ε
      (solver.nextPosition z, solver.halfMomentum z) = solver.step z := by
  dsimp only
  let solver := boundedScalarContractiveSolverAt ε hstep
  rfl

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

/-- Momentum derivative of the position-force callback at fixed position. -/
theorem deriv_boundedScalarPositionDerivative_momentum (q p : ℝ) :
    deriv (fun r => Real.cos q / (2 + Real.sin q) *
      scalarPositionProfile ((2 + Real.sin q) * r)) p =
      Real.cos q *
        (2 * scalarVelocityProfile ((2 + Real.sin q) * p) -
          scalarVelocityProfile ((2 + Real.sin q) * p) ^ 3) := by
  let s := 2 + Real.sin q
  let x := s * p
  have hs : s ≠ 0 := by
    dsimp [s]
    have := Real.neg_one_le_sin q
    linarith
  have hwDiff : DifferentiableAt ℝ scalarPositionProfile x :=
    ((differentiable_id.pow 2).div differentiable_scalarRelativisticProfile
      (fun y => (scalarRelativisticProfile_pos y).ne')) x
  have hw : HasDerivAt scalarPositionProfile
      (2 * scalarVelocityProfile x - scalarVelocityProfile x ^ 3) x := by
    rw [← deriv_scalarPositionProfile x]
    exact hwDiff.hasDerivAt
  have hinner : HasDerivAt (fun r : ℝ => s * r) s p := by
    simpa using (hasDerivAt_id p).const_mul s
  have hcomp := hw.comp p hinner
  have hout := hcomp.const_mul (Real.cos q / s)
  have hout' : HasDerivAt (fun r => Real.cos q / s *
      (scalarPositionProfile ∘ fun y : ℝ => s * y) r)
      (Real.cos q / s *
        ((2 * scalarVelocityProfile x - scalarVelocityProfile x ^ 3) * s)) p := by
    exact hout.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun r => by rfl)
  rw [show (fun r => Real.cos q / (2 + Real.sin q) *
      scalarPositionProfile ((2 + Real.sin q) * r)) =
      fun r => Real.cos q / s *
        (scalarPositionProfile ∘ fun y : ℝ => s * y) r by rfl,
    hout'.deriv]
  dsimp [x, s]
  have hs' : 2 + Real.sin q ≠ 0 := by simpa [s] using hs
  field_simp [hs']

/-- Position derivative of the velocity callback at fixed momentum. -/
theorem deriv_boundedScalarMomentumDerivative_position (q p : ℝ) :
    deriv (fun r => scaledVelocityProfile p (2 + Real.sin r)) q =
      Real.cos q *
        (scalarVelocityProfile ((2 + Real.sin q) * p) +
          ((2 + Real.sin q) * p) /
            scalarRelativisticProfile ((2 + Real.sin q) * p) ^ 3) := by
  let s := 2 + Real.sin q
  have houter : HasDerivAt (scaledVelocityProfile p)
      (scalarVelocityProfile (s * p) +
        (s * p) / scalarRelativisticProfile (s * p) ^ 3) s := by
    rw [← deriv_scaledVelocityProfile p s]
    exact ((differentiableAt_id.mul
      (differentiable_scalarVelocityProfile.differentiableAt.comp s
        (by fun_prop))).hasDerivAt)
  have hscale : HasDerivAt (fun r : ℝ => 2 + Real.sin r)
      (Real.cos q) q := by
    simpa using (Real.hasDerivAt_sin q).const_add 2
  have hcomp := houter.comp q hscale
  rw [show (fun r => scaledVelocityProfile p (2 + Real.sin r)) =
      scaledVelocityProfile p ∘ (fun r : ℝ => 2 + Real.sin r) by rfl,
    hcomp.deriv]
  dsimp [s]
  ring

/-- Equality of the two mixed partials used in the generalized-leapfrog
Jacobian cancellation. -/
theorem scalarProfile_mixed_identity (x : ℝ) :
    2 * scalarVelocityProfile x - scalarVelocityProfile x ^ 3 =
      scalarVelocityProfile x +
        x / scalarRelativisticProfile x ^ 3 := by
  have hp : scalarRelativisticProfile x ≠ 0 :=
    (scalarRelativisticProfile_pos x).ne'
  unfold scalarVelocityProfile
  rw [show scalarRelativisticProfile x ^ 3 =
      scalarRelativisticProfile x * scalarRelativisticProfile x ^ 2 by ring]
  field_simp [hp]
  rw [scalarRelativisticProfile_sq]
  ring

theorem boundedScalar_mixed_derivatives_eq (q p : ℝ) :
    deriv (fun r => Real.cos q / (2 + Real.sin q) *
      scalarPositionProfile ((2 + Real.sin q) * r)) p =
    deriv (fun r => scaledVelocityProfile p (2 + Real.sin r)) q := by
  rw [deriv_boundedScalarPositionDerivative_momentum,
    deriv_boundedScalarMomentumDerivative_position]
  rw [scalarProfile_mixed_identity]

theorem abs_deriv_boundedScalarPositionDerivative_momentum_le_three
    (q p : ℝ) :
    |deriv (fun r => Real.cos q / (2 + Real.sin q) *
      scalarPositionProfile ((2 + Real.sin q) * r)) p| ≤ 3 := by
  rw [deriv_boundedScalarPositionDerivative_momentum, abs_mul]
  calc
    |Real.cos q| *
        |2 * scalarVelocityProfile ((2 + Real.sin q) * p) -
          scalarVelocityProfile ((2 + Real.sin q) * p) ^ 3| ≤
        1 * 3 := by
      gcongr
      · exact Real.abs_cos_le_one q
      · calc
          _ ≤ 2 * |scalarVelocityProfile ((2 + Real.sin q) * p)| +
              |scalarVelocityProfile ((2 + Real.sin q) * p)| ^ 3 := by
                calc
                  _ ≤ |2 * scalarVelocityProfile ((2 + Real.sin q) * p)| +
                      |scalarVelocityProfile ((2 + Real.sin q) * p) ^ 3| :=
                    abs_sub _ _
                  _ = _ := by
                    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
                      abs_pow]
          _ ≤ 2 * 1 + 1 ^ 3 := by
                gcongr <;> exact abs_scalarVelocityProfile_le_one _
          _ = 3 := by norm_num
    _ = 3 := by norm_num

theorem abs_deriv_boundedScalarMomentumDerivative_position_le_two
    (q p : ℝ) :
    |deriv (fun r => scaledVelocityProfile p (2 + Real.sin r)) q| ≤ 2 := by
  rw [deriv_boundedScalarMomentumDerivative_position, abs_mul]
  calc
    |Real.cos q| *
        |scalarVelocityProfile ((2 + Real.sin q) * p) +
          ((2 + Real.sin q) * p) /
            scalarRelativisticProfile ((2 + Real.sin q) * p) ^ 3| ≤
        1 * 2 := by
      gcongr
      · exact Real.abs_cos_le_one q
      · calc
          _ ≤ |scalarVelocityProfile ((2 + Real.sin q) * p)| +
              |((2 + Real.sin q) * p) /
                scalarRelativisticProfile ((2 + Real.sin q) * p) ^ 3| :=
            abs_add_le _ _
          _ ≤ 1 + 1 := add_le_add (abs_scalarVelocityProfile_le_one _)
            (abs_div_scalarRelativisticProfile_cube_le_one _)
          _ = 2 := by norm_num
    _ = 2 := by norm_num

theorem boundedScalar_incoming_derivative_factor_ne_zero
    (ε : ℝ) (hstep : |ε / 2| * 3 < 1) (q p : ℝ) :
    1 + (ε / 2) * deriv (fun r => Real.cos q / (2 + Real.sin q) *
      scalarPositionProfile ((2 + Real.sin q) * r)) p ≠ 0 := by
  have hbound := abs_deriv_boundedScalarPositionDerivative_momentum_le_three q p
  have hsmall : |(ε / 2) * deriv (fun r => Real.cos q / (2 + Real.sin q) *
      scalarPositionProfile ((2 + Real.sin q) * r)) p| < 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hbound (abs_nonneg _)).trans_lt hstep
  intro hzero
  have : (ε / 2) * deriv (fun r => Real.cos q / (2 + Real.sin q) *
      scalarPositionProfile ((2 + Real.sin q) * r)) p = -1 := by linarith
  rw [this, abs_neg, abs_one] at hsmall
  exact (lt_irrefl 1 hsmall)

theorem boundedScalar_position_derivative_factor_ne_zero
    (ε : ℝ) (hstep : |ε / 2| * 3 < 1) (q p : ℝ) :
    1 - (ε / 2) * deriv (fun r => scaledVelocityProfile p (2 + Real.sin r)) q ≠ 0 := by
  have hbound := abs_deriv_boundedScalarMomentumDerivative_position_le_two q p
  have htwo : |ε / 2| * 2 < 1 := by
    nlinarith [abs_nonneg (ε / 2)]
  have hsmall : |(ε / 2) * deriv
      (fun r => scaledVelocityProfile p (2 + Real.sin r)) q| < 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hbound (abs_nonneg _)).trans_lt htwo
  intro hzero
  have : (ε / 2) * deriv
      (fun r => scaledVelocityProfile p (2 + Real.sin r)) q = 1 := by linarith
  rw [this, abs_one] at hsmall
  exact (lt_irrefl 1 hsmall)

theorem det_boundedScalarIncomingFDerivReal_ne_zero
    (ε : ℝ) (hstep : |ε / 2| * 3 < 1) (z : ℝ × ℝ) :
    (boundedScalarIncomingFDerivReal ε z).det ≠ 0 := by
  rw [det_boundedScalarIncomingFDerivReal,
    fderiv_boundedScalarPositionDerivativeReal_snd]
  exact boundedScalar_incoming_derivative_factor_ne_zero ε hstep z.1 z.2

theorem differentiable_boundedScalarHalfSolveReal
    (ε : ℝ) (hstep : |ε / 2| * 3 < 1) :
    Differentiable ℝ (boundedScalarHalfSolveReal ε hstep) := by
  apply differentiable_of_continuous_leftInverse_of_det_fderiv_ne_zero
    (boundedScalarIncomingMapReal ε)
      (boundedScalarHalfSolveReal ε hstep)
    (differentiable_boundedScalarIncomingMapReal ε)
    (continuous_boundedScalarHalfSolveReal ε hstep)
    (boundedScalarIncomingMapReal_leftInverse_halfSolveReal ε hstep)
  intro z
  rw [(hasFDerivAt_boundedScalarIncomingMapReal ε z).fderiv]
  exact det_boundedScalarIncomingFDerivReal_ne_zero ε hstep z

/-- Algebraic determinant cancellation behind generalized leapfrog: the
incoming and outgoing implicit-coordinate factors cancel separately once the
mixed partials agree. -/
theorem generalizedLeapfrog_scalar_jacobian_cancellation
    (h incomingMixed outgoingMixed : ℝ)
    (hin : 1 + h * incomingMixed ≠ 0)
    (hout : 1 - h * outgoingMixed ≠ 0) :
    (1 - h * outgoingMixed) * (1 - h * outgoingMixed)⁻¹ *
      (1 + h * incomingMixed) * (1 + h * incomingMixed)⁻¹ = 1 := by
  field_simp [hin, hout]

end Mcmc.Relativistic
