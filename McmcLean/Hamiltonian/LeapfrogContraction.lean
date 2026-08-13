import McmcLean.Hamiltonian.Assumptions
import McmcLean.Hamiltonian.ExactFlow
import Mathlib.Analysis.Complex.Exponential

/-!
# Shared-momentum leapfrog contraction

This module gives a quantitative discrete counterpart to the exact-flow
contraction calculation.  For one leapfrog step with common initial momentum,
the position difference is exactly

`d - (ε² / 2) • (∇U(q₁) - ∇U(q₂))`.

Expanding its squared Euclidean norm and applying local strong monotonicity and
global gradient Lipschitzness yields the explicit factor

`1 - α ε² + β² ε⁴ / 4`.

This is a one-step ingredient for the aligned-trajectory numerical argument;
the paper's multi-step compact-uniform proposition still requires accumulated
leapfrog error estimates.
-/

open scoped BigOperators

namespace McmcLean.Hamiltonian

variable {ι : Type*} [Fintype ι]

/-- Error between the relative phase differences of two paired phase-space
states. This is the quantity accumulated along the leapfrog grid. -/
noncomputable def pairedPhaseError
    (z₁ z₂ w₁ w₂ : PhaseSpace ι) : ℝ :=
  euclideanPhaseSize
    ((z₁.1 - z₂.1) - (w₁.1 - w₂.1),
      (z₁.2 - z₂.2) - (w₁.2 - w₂.2))

/-- Euclidean phase error between one numerical and one exact state. -/
noncomputable def absolutePhaseError
    (z w : PhaseSpace ι) : ℝ :=
  euclideanPhaseSize (z.1 - w.1, z.2 - w.2)

theorem absolutePhaseError_nonneg (z w : PhaseSpace ι) :
    0 ≤ absolutePhaseError z w := euclideanPhaseSize_nonneg _

@[simp]
theorem absolutePhaseError_self (z : PhaseSpace ι) :
    absolutePhaseError z z = 0 := by
  simp [absolutePhaseError, euclideanPhaseSize]

theorem absolutePhaseError_triangle
    (z w u : PhaseSpace ι) :
    absolutePhaseError z u ≤
      absolutePhaseError z w + absolutePhaseError w u := by
  unfold absolutePhaseError euclideanPhaseSize
  have hq : euclideanNorm (z.1 - u.1) ≤
      euclideanNorm (z.1 - w.1) + euclideanNorm (w.1 - u.1) := by
    rw [show z.1 - u.1 = (z.1 - w.1) + (w.1 - u.1) by abel]
    exact euclideanNorm_add_le _ _
  have hp : euclideanNorm (z.2 - u.2) ≤
      euclideanNorm (z.2 - w.2) + euclideanNorm (w.2 - u.2) := by
    rw [show z.2 - u.2 = (z.2 - w.2) + (w.2 - u.2) by abel]
    exact euclideanNorm_add_le _ _
  linarith

theorem dist_fst_le_absolutePhaseError (z w : PhaseSpace ι) :
    dist z.1 w.1 ≤ absolutePhaseError z w := by
  apply (dist_le_euclideanNorm_sub z.1 w.1).trans
  unfold absolutePhaseError euclideanPhaseSize
  exact le_add_of_nonneg_right (euclideanNorm_nonneg _)

omit [Fintype ι] in
theorem leapfrog_zero_position
    (gradient : Position ι → Position ι) (ε : ℝ) :
    (leapfrog gradient ε (0, 0)).1 =
      -(ε ^ 2 / 2) • gradient 0 := by
  funext i
  simp [leapfrog, halfKick, drift, Pi.smul_apply, smul_eq_mul,
    Pi.neg_apply]
  ring

omit [Fintype ι] in
theorem leapfrog_zero_momentum
    (gradient : Position ι → Position ι) (ε : ℝ) :
    (leapfrog gradient ε (0, 0)).2 =
      -(ε / 2) • gradient 0 -
        (ε / 2) • gradient (leapfrog gradient ε (0, 0)).1 := by
  funext i
  simp [leapfrog, halfKick, drift, Pi.smul_apply, smul_eq_mul,
    Pi.neg_apply]

/-- The image of the zero phase point supplies an affine forcing term of size
`O(|ε| ‖∇U(0)‖₂)` in absolute leapfrog stability. -/
theorem leapfrog_zero_euclideanPhaseSize_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {ε : ℝ} (hε : |ε| ≤ 1) :
    euclideanPhaseSize (leapfrog gradient ε (0, 0)) ≤
      (2 + (β : ℝ)) * |ε| * euclideanNorm (gradient 0) := by
  let q' := (leapfrog gradient ε (0, 0)).1
  let G := euclideanNorm (gradient 0)
  have ha : 0 ≤ |ε| := abs_nonneg ε
  have hG : 0 ≤ G := euclideanNorm_nonneg _
  have hβ : 0 ≤ (β : ℝ) := β.coe_nonneg
  have hqeq : q' = -(ε ^ 2 / 2) • gradient 0 :=
    leapfrog_zero_position gradient ε
  have hq : euclideanNorm q' ≤ |ε| * G := by
    rw [hqeq, euclideanNorm_smul, abs_neg,
      abs_of_nonneg (by positivity : 0 ≤ ε ^ 2 / 2)]
    have hsquare : ε ^ 2 = |ε| ^ 2 := (sq_abs ε).symm
    rw [hsquare]
    change |ε| ^ 2 / 2 * G ≤ |ε| * G
    apply mul_le_mul_of_nonneg_right _ hG
    nlinarith
  have hgq : euclideanNorm (gradient q') ≤
      (β : ℝ) * (|ε| * G) + G := by
    apply le_trans (hreg.euclideanNorm_gradient_le q')
    gcongr
  have hp : euclideanNorm (leapfrog gradient ε (0, 0)).2 ≤
      (1 + (β : ℝ)) * |ε| * G := by
    rw [leapfrog_zero_momentum]
    apply le_trans (euclideanNorm_sub_le _ _)
    rw [euclideanNorm_smul, euclideanNorm_smul, abs_neg, abs_div]
    have htwo : |(2 : ℝ)| = 2 := by norm_num
    rw [htwo]
    change |ε| / 2 * G + |ε| / 2 * euclideanNorm (gradient q') ≤
      (1 + (β : ℝ)) * |ε| * G
    have hcoeff : 0 ≤ |ε| / 2 := div_nonneg ha (by norm_num)
    have hmul := mul_le_mul_of_nonneg_left hgq hcoeff
    have haa : |ε| ^ 2 ≤ |ε| := by nlinarith
    have haaG := mul_le_mul_of_nonneg_right haa hG
    have hβhalf : 0 ≤ (β : ℝ) / 2 := div_nonneg hβ (by norm_num)
    have hsmall := mul_le_mul_of_nonneg_left haaG hβhalf
    calc
      |ε| / 2 * G + |ε| / 2 * euclideanNorm (gradient q') ≤
          |ε| / 2 * G + |ε| / 2 * ((β : ℝ) * (|ε| * G) + G) :=
        by simpa only [add_comm] using add_le_add_left hmul (|ε| / 2 * G)
      _ = |ε| * G + ((β : ℝ) / 2) * (|ε| ^ 2 * G) := by ring
      _ ≤ |ε| * G + ((β : ℝ) / 2) * (|ε| * G) :=
        by simpa only [add_comm] using add_le_add_left hsmall (|ε| * G)
      _ ≤ (1 + (β : ℝ)) * |ε| * G := by
        have hprod : 0 ≤ (β : ℝ) * (|ε| * G) := by positivity
        nlinarith
  unfold euclideanPhaseSize
  change euclideanNorm q' +
      euclideanNorm (leapfrog gradient ε (0, 0)).2 ≤ _
  nlinarith

/-- Conservative one-step factor for the sum of squared relative position and
relative momentum. -/
noncomputable def leapfrogRelativeStabilityFactor (β : NNReal) (ε : ℝ) : ℝ :=
  let A := 3 + 3 * (β : ℝ) ^ 2 * ε ^ 4 / 4
  let B := 3 * ε ^ 2
  let C := 3 * ε ^ 2 * (β : ℝ) ^ 2 / 4
  ((1 + C) * A + C) + ((1 + C) * B + 3)

theorem leapfrogRelativeStabilityFactor_nonneg (β : NNReal) (ε : ℝ) :
    0 ≤ leapfrogRelativeStabilityFactor β ε := by
  unfold leapfrogRelativeStabilityFactor
  positivity

omit [Fintype ι] in
/-- Exact relative-position recurrence for one leapfrog step with arbitrary
initial relative momentum. -/
theorem leapfrog_position_sub
    (gradient : Position ι → Position ι) (ε : ℝ)
    (z₁ z₂ : PhaseSpace ι) :
    (leapfrog gradient ε z₁).1 - (leapfrog gradient ε z₂).1 =
      (z₁.1 - z₂.1) + ε • (z₁.2 - z₂.2) -
        (ε ^ 2 / 2) • (gradient z₁.1 - gradient z₂.1) := by
  funext i
  simp only [leapfrog, drift, halfKick, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

omit [Fintype ι] in
/-- Exact relative-momentum recurrence for one leapfrog step. -/
theorem leapfrog_momentum_sub
    (gradient : Position ι → Position ι) (ε : ℝ)
    (z₁ z₂ : PhaseSpace ι) :
    (leapfrog gradient ε z₁).2 - (leapfrog gradient ε z₂).2 =
      (z₁.2 - z₂.2) - (ε / 2) • (gradient z₁.1 - gradient z₂.1) -
        (ε / 2) •
          (gradient (leapfrog gradient ε z₁).1 -
            gradient (leapfrog gradient ε z₂).1) := by
  funext i
  simp only [leapfrog, drift, halfKick, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

omit [Fintype ι] in
/-- Relative-position recurrence at step `n + 1` of two aligned leapfrog
trajectories. -/
theorem leapfrogN_position_sub_succ
    (gradient : Position ι → Position ι) (ε : ℝ) (n : ℕ)
    (z₁ z₂ : PhaseSpace ι) :
    (leapfrogN gradient ε (n + 1) z₁).1 -
        (leapfrogN gradient ε (n + 1) z₂).1 =
      ((leapfrogN gradient ε n z₁).1 -
          (leapfrogN gradient ε n z₂).1) +
        ε • ((leapfrogN gradient ε n z₁).2 -
          (leapfrogN gradient ε n z₂).2) -
        (ε ^ 2 / 2) •
          (gradient (leapfrogN gradient ε n z₁).1 -
            gradient (leapfrogN gradient ε n z₂).1) := by
  rw [show n + 1 = Nat.succ n by omega]
  simp only [leapfrogN, Function.iterate_succ_apply']
  exact leapfrog_position_sub gradient ε _ _

omit [Fintype ι] in
/-- Relative-momentum recurrence at step `n + 1` of two aligned leapfrog
trajectories. -/
theorem leapfrogN_momentum_sub_succ
    (gradient : Position ι → Position ι) (ε : ℝ) (n : ℕ)
    (z₁ z₂ : PhaseSpace ι) :
    (leapfrogN gradient ε (n + 1) z₁).2 -
        (leapfrogN gradient ε (n + 1) z₂).2 =
      ((leapfrogN gradient ε n z₁).2 -
          (leapfrogN gradient ε n z₂).2) -
        (ε / 2) •
          (gradient (leapfrogN gradient ε n z₁).1 -
            gradient (leapfrogN gradient ε n z₂).1) -
        (ε / 2) •
          (gradient (leapfrogN gradient ε (n + 1) z₁).1 -
            gradient (leapfrogN gradient ε (n + 1) z₂).1) := by
  rw [show n + 1 = Nat.succ n by omega]
  simp only [leapfrogN, Function.iterate_succ_apply']
  exact leapfrog_momentum_sub gradient ε _ _

/-- Squared form of the global Euclidean gradient-Lipschitz inequality. -/
theorem RegularPotential.squaredEuclideanNorm_gradient_sub_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (h : RegularPotential potential gradient β)
    (q₁ q₂ : Position ι) :
    squaredEuclideanNorm (gradient q₁ - gradient q₂) ≤
      (β : ℝ) ^ 2 * squaredEuclideanNorm (q₁ - q₂) := by
  have hlip := h.euclideanNorm_gradient_sub_le q₁ q₂
  have hβ : 0 ≤ (β : ℝ) := β.coe_nonneg
  have hq : 0 ≤ euclideanNorm (q₁ - q₂) := euclideanNorm_nonneg _
  have hg : 0 ≤ euclideanNorm (gradient q₁ - gradient q₂) :=
    euclideanNorm_nonneg _
  have hsq := sq_le_sq₀ hg (mul_nonneg hβ hq) |>.mpr hlip
  rw [euclideanNorm_sq, mul_pow, euclideanNorm_sq] at hsq
  exact hsq

/-- One-step relative-position stability bound for arbitrary initial relative
momentum. -/
theorem leapfrog_squaredPositionSub_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (ε : ℝ) (z₁ z₂ : PhaseSpace ι) :
    squaredEuclideanNorm
        ((leapfrog gradient ε z₁).1 - (leapfrog gradient ε z₂).1) ≤
      (3 + 3 * (β : ℝ) ^ 2 * ε ^ 4 / 4) *
          squaredEuclideanNorm (z₁.1 - z₂.1) +
        3 * ε ^ 2 * squaredEuclideanNorm (z₁.2 - z₂.2) := by
  rw [leapfrog_position_sub]
  apply le_trans (squaredEuclideanNorm_add_sub_le_three _ _ _)
  rw [squaredEuclideanNorm_smul, squaredEuclideanNorm_smul]
  have hlip := hreg.squaredEuclideanNorm_gradient_sub_le z₁.1 z₂.1
  have hcoef : 0 ≤ 3 * (ε ^ 2 / 2) ^ 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hlip hcoef
  nlinarith [sq_nonneg ε]

/-- One-step relative-momentum stability bound. It depends on relative
position at both ends of the step, matching the two half-kicks. -/
theorem leapfrog_squaredMomentumSub_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (ε : ℝ) (z₁ z₂ : PhaseSpace ι) :
    squaredEuclideanNorm
        ((leapfrog gradient ε z₁).2 - (leapfrog gradient ε z₂).2) ≤
      3 * squaredEuclideanNorm (z₁.2 - z₂.2) +
        (3 * ε ^ 2 * (β : ℝ) ^ 2 / 4) *
          (squaredEuclideanNorm (z₁.1 - z₂.1) +
            squaredEuclideanNorm
              ((leapfrog gradient ε z₁).1 -
                (leapfrog gradient ε z₂).1)) := by
  rw [leapfrog_momentum_sub]
  apply le_trans (squaredEuclideanNorm_sub_sub_le_three _ _ _)
  rw [squaredEuclideanNorm_smul, squaredEuclideanNorm_smul]
  have h₀ := hreg.squaredEuclideanNorm_gradient_sub_le z₁.1 z₂.1
  have h₁ := hreg.squaredEuclideanNorm_gradient_sub_le
    (leapfrog gradient ε z₁).1 (leapfrog gradient ε z₂).1
  have hcoef : 0 ≤ 3 * (ε / 2) ^ 2 := by positivity
  have h₀' := mul_le_mul_of_nonneg_left h₀ hcoef
  have h₁' := mul_le_mul_of_nonneg_left h₁ hcoef
  nlinarith [sq_nonneg ε]

/-- Sharp norm-level relative-position recurrence. Unlike the coarse squared
bound, its coefficients approach those of the identity as `ε → 0`. -/
theorem leapfrog_euclideanNorm_positionSub_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (ε : ℝ) (z₁ z₂ : PhaseSpace ι) :
    euclideanNorm
        ((leapfrog gradient ε z₁).1 - (leapfrog gradient ε z₂).1) ≤
      (1 + (β : ℝ) * ε ^ 2 / 2) * euclideanNorm (z₁.1 - z₂.1) +
        |ε| * euclideanNorm (z₁.2 - z₂.2) := by
  rw [leapfrog_position_sub]
  apply le_trans (euclideanNorm_sub_le _ _)
  apply le_trans (add_le_add (euclideanNorm_add_le _ _) (le_refl _))
  rw [euclideanNorm_smul, euclideanNorm_smul]
  have hlip := hreg.euclideanNorm_gradient_sub_le z₁.1 z₂.1
  have hc : |ε ^ 2 / 2| = ε ^ 2 / 2 := abs_of_nonneg (by positivity)
  rw [hc]
  have hscaled := mul_le_mul_of_nonneg_left hlip (by positivity : 0 ≤ ε ^ 2 / 2)
  nlinarith

/-- Sharp norm-level relative-momentum recurrence from the two half-kicks. -/
theorem leapfrog_euclideanNorm_momentumSub_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (ε : ℝ) (z₁ z₂ : PhaseSpace ι) :
    euclideanNorm
        ((leapfrog gradient ε z₁).2 - (leapfrog gradient ε z₂).2) ≤
      euclideanNorm (z₁.2 - z₂.2) +
        (|ε| * (β : ℝ) / 2) *
          (euclideanNorm (z₁.1 - z₂.1) +
            euclideanNorm
              ((leapfrog gradient ε z₁).1 -
                (leapfrog gradient ε z₂).1)) := by
  rw [leapfrog_momentum_sub]
  apply le_trans (euclideanNorm_sub_le _ _)
  apply le_trans (add_le_add (euclideanNorm_sub_le _ _) (le_refl _))
  rw [euclideanNorm_smul, euclideanNorm_smul]
  have h₀ := hreg.euclideanNorm_gradient_sub_le z₁.1 z₂.1
  have h₁ := hreg.euclideanNorm_gradient_sub_le
    (leapfrog gradient ε z₁).1 (leapfrog gradient ε z₂).1
  have hc : |ε / 2| = |ε| / 2 := by
    rw [abs_div]
    norm_num
  rw [hc]
  have hcoef : 0 ≤ |ε| / 2 := by positivity
  have h₀' := mul_le_mul_of_nonneg_left h₀ hcoef
  have h₁' := mul_le_mul_of_nonneg_left h₁ hcoef
  nlinarith

/-- Four-trajectory propagation inequality for paired relative errors. It
separates the homogeneous phase error from paired force discrepancies at the
two kick locations. -/
theorem leapfrog_pairedRelativePhaseError_le
    (gradient : Position ι → Position ι)
    {ε : ℝ} (hε : |ε| ≤ 1)
    (z₁ z₂ w₁ w₂ : PhaseSpace ι) :
    euclideanPhaseSize
        (((leapfrog gradient ε z₁).1 - (leapfrog gradient ε z₂).1) -
            ((leapfrog gradient ε w₁).1 - (leapfrog gradient ε w₂).1),
          ((leapfrog gradient ε z₁).2 - (leapfrog gradient ε z₂).2) -
            ((leapfrog gradient ε w₁).2 - (leapfrog gradient ε w₂).2)) ≤
      (1 + |ε|) *
          euclideanPhaseSize
            ((z₁.1 - z₂.1) - (w₁.1 - w₂.1),
              (z₁.2 - z₂.2) - (w₁.2 - w₂.2)) +
        |ε| * euclideanNorm
          ((gradient z₁.1 - gradient z₂.1) -
            (gradient w₁.1 - gradient w₂.1)) +
        (|ε| / 2) * euclideanNorm
          ((gradient (leapfrog gradient ε z₁).1 -
              gradient (leapfrog gradient ε z₂).1) -
            (gradient (leapfrog gradient ε w₁).1 -
              gradient (leapfrog gradient ε w₂).1)) := by
  let Eq : Position ι := (z₁.1 - z₂.1) - (w₁.1 - w₂.1)
  let Ep : Momentum ι := (z₁.2 - z₂.2) - (w₁.2 - w₂.2)
  let F0 : Position ι :=
    (gradient z₁.1 - gradient z₂.1) -
      (gradient w₁.1 - gradient w₂.1)
  let F1 : Position ι :=
    (gradient (leapfrog gradient ε z₁).1 -
        gradient (leapfrog gradient ε z₂).1) -
      (gradient (leapfrog gradient ε w₁).1 -
        gradient (leapfrog gradient ε w₂).1)
  have hqidentity :
      ((leapfrog gradient ε z₁).1 - (leapfrog gradient ε z₂).1) -
          ((leapfrog gradient ε w₁).1 - (leapfrog gradient ε w₂).1) =
        Eq + ε • Ep - (ε ^ 2 / 2) • F0 := by
    rw [leapfrog_position_sub, leapfrog_position_sub]
    dsimp [Eq, Ep, F0]
    module
  have hpidentity :
      ((leapfrog gradient ε z₁).2 - (leapfrog gradient ε z₂).2) -
          ((leapfrog gradient ε w₁).2 - (leapfrog gradient ε w₂).2) =
        Ep - (ε / 2) • F0 - (ε / 2) • F1 := by
    rw [leapfrog_momentum_sub, leapfrog_momentum_sub]
    dsimp [Ep, F0, F1]
    module
  have hq : euclideanNorm
      (((leapfrog gradient ε z₁).1 - (leapfrog gradient ε z₂).1) -
        ((leapfrog gradient ε w₁).1 - (leapfrog gradient ε w₂).1)) ≤
      euclideanNorm Eq + |ε| * euclideanNorm Ep +
        (ε ^ 2 / 2) * euclideanNorm F0 := by
    rw [hqidentity]
    have hadd := euclideanNorm_add_le Eq (ε • Ep)
    rw [euclideanNorm_smul] at hadd
    calc
      euclideanNorm (Eq + ε • Ep - (ε ^ 2 / 2) • F0) ≤
          euclideanNorm (Eq + ε • Ep) +
            euclideanNorm ((ε ^ 2 / 2) • F0) :=
        euclideanNorm_sub_le _ _
      _ ≤ (euclideanNorm Eq + |ε| * euclideanNorm Ep) +
          euclideanNorm ((ε ^ 2 / 2) • F0) := add_le_add hadd le_rfl
      _ = euclideanNorm Eq + |ε| * euclideanNorm Ep +
          (ε ^ 2 / 2) * euclideanNorm F0 := by
        rw [euclideanNorm_smul,
          abs_of_nonneg (by positivity : 0 ≤ ε ^ 2 / 2)]
  have hp' : euclideanNorm
      (((leapfrog gradient ε z₁).2 - (leapfrog gradient ε z₂).2) -
        ((leapfrog gradient ε w₁).2 - (leapfrog gradient ε w₂).2)) ≤
      euclideanNorm Ep + (|ε| / 2) * euclideanNorm F0 +
        (|ε| / 2) * euclideanNorm F1 := by
    rw [hpidentity]
    calc
      euclideanNorm (Ep - (ε / 2) • F0 - (ε / 2) • F1) ≤
          euclideanNorm (Ep - (ε / 2) • F0) +
            euclideanNorm ((ε / 2) • F1) := euclideanNorm_sub_le _ _
      _ ≤ (euclideanNorm Ep + euclideanNorm ((ε / 2) • F0)) +
          euclideanNorm ((ε / 2) • F1) :=
        add_le_add (euclideanNorm_sub_le _ _) le_rfl
      _ = euclideanNorm Ep + (|ε| / 2) * euclideanNorm F0 +
          (|ε| / 2) * euclideanNorm F1 := by
        rw [euclideanNorm_smul, euclideanNorm_smul]
        congr 2 <;> rw [abs_div] <;> norm_num
  have hεsq : ε ^ 2 ≤ |ε| := by
    rw [← sq_abs]
    nlinarith [abs_nonneg ε]
  have hF0 : 0 ≤ euclideanNorm F0 := euclideanNorm_nonneg _
  have hEp : 0 ≤ euclideanNorm Ep := euclideanNorm_nonneg _
  have hEq : 0 ≤ euclideanNorm Eq := euclideanNorm_nonneg _
  have hF1 : 0 ≤ euclideanNorm F1 := euclideanNorm_nonneg _
  have hε0 : 0 ≤ |ε| := abs_nonneg _
  unfold euclideanPhaseSize
  dsimp only [Eq, Ep, F0, F1] at hq hp' ⊢
  nlinarith

/-- Compact endpoint-position propagation. Because the drift is computed
before leapfrog's second half-kick, the new relative position error depends
only on the old phase error and the initial paired force discrepancy. -/
theorem RegularPotential.exists_compact_leapfrog_pairedRelativePositionError_bound
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ M ≥ 0,
      M ≤ ((β * (Fintype.card ι + 1 : NNReal) : NNReal) : ℝ) ∧
      ∀ {ε : ℝ} (z₁ z₂ w₁ w₂ : PhaseSpace ι),
        z₁.1 ∈ S → z₂.1 ∈ S → w₁.1 ∈ S → w₂.1 ∈ S →
        dist z₁.1 w₁.1 ≤ δ → dist z₂.1 w₂.1 ≤ δ →
        euclideanNorm
            (((leapfrog gradient ε z₁).1 -
                (leapfrog gradient ε z₂).1) -
              ((leapfrog gradient ε w₁).1 -
                (leapfrog gradient ε w₂).1)) ≤
          (1 + |ε| + ε ^ 2 / 2 *
              ((Fintype.card ι : ℝ) + 1) * M) *
              euclideanPhaseSize
                ((z₁.1 - z₂.1) - (w₁.1 - w₂.1),
                  (z₁.2 - z₂.2) - (w₁.2 - w₂.2)) +
            ε ^ 2 / 2 * ((Fintype.card ι : ℝ) + 1) * η *
              euclideanNorm (w₁.1 - w₂.1) := by
  obtain ⟨δ, hδ, M, hM, hMglobal, hforce⟩ :=
    hreg.exists_uniform_euclideanNorm_gradientSub_sub_gradientSub_bound
      hScompact hSconvex hη
  refine ⟨δ, hδ, M, hM, hMglobal, ?_⟩
  intro ε z₁ z₂ w₁ w₂ hz₁ hz₂ hw₁ hw₂ hz₁w₁ hz₂w₂
  let Eq : Position ι := (z₁.1 - z₂.1) - (w₁.1 - w₂.1)
  let Ep : Momentum ι := (z₁.2 - z₂.2) - (w₁.2 - w₂.2)
  let F0 : Position ι :=
    (gradient z₁.1 - gradient z₂.1) -
      (gradient w₁.1 - gradient w₂.1)
  have hF0 := hforce hw₂ hw₁ hz₂ hz₁ hz₂w₂ hz₁w₁
  have hidentity :
      ((leapfrog gradient ε z₁).1 - (leapfrog gradient ε z₂).1) -
          ((leapfrog gradient ε w₁).1 - (leapfrog gradient ε w₂).1) =
        Eq + ε • Ep - (ε ^ 2 / 2) • F0 := by
    rw [leapfrog_position_sub, leapfrog_position_sub]
    dsimp [Eq, Ep, F0]
    module
  have hraw : euclideanNorm
      (((leapfrog gradient ε z₁).1 - (leapfrog gradient ε z₂).1) -
        ((leapfrog gradient ε w₁).1 - (leapfrog gradient ε w₂).1)) ≤
      euclideanNorm Eq + |ε| * euclideanNorm Ep +
        ε ^ 2 / 2 * euclideanNorm F0 := by
    rw [hidentity]
    calc
      euclideanNorm (Eq + ε • Ep - (ε ^ 2 / 2) • F0) ≤
          euclideanNorm (Eq + ε • Ep) +
            euclideanNorm ((ε ^ 2 / 2) • F0) := euclideanNorm_sub_le _ _
      _ ≤ (euclideanNorm Eq + euclideanNorm (ε • Ep)) +
          euclideanNorm ((ε ^ 2 / 2) • F0) :=
        add_le_add (euclideanNorm_add_le _ _) le_rfl
      _ = euclideanNorm Eq + |ε| * euclideanNorm Ep +
          ε ^ 2 / 2 * euclideanNorm F0 := by
        rw [euclideanNorm_smul, euclideanNorm_smul,
          abs_of_nonneg (by positivity : 0 ≤ ε ^ 2 / 2)]
  apply hraw.trans
  have hEq : euclideanNorm Eq ≤ euclideanPhaseSize (Eq, Ep) := by
    unfold euclideanPhaseSize
    linarith [euclideanNorm_nonneg Ep]
  have hEp : euclideanNorm Ep ≤ euclideanPhaseSize (Eq, Ep) := by
    unfold euclideanPhaseSize
    linarith [euclideanNorm_nonneg Eq]
  have hcoef : 0 ≤ ε ^ 2 / 2 := by positivity
  have hscaledF := mul_le_mul_of_nonneg_left hF0 hcoef
  dsimp only [Eq, Ep, F0] at hEq hEp hscaledF ⊢
  have hε0 : 0 ≤ |ε| := abs_nonneg _
  have hD : 0 ≤ (Fintype.card ι : ℝ) + 1 := by positivity
  have hEpScaled := mul_le_mul_of_nonneg_left hEp hε0
  have hMEq := mul_le_mul_of_nonneg_left hEq hM
  have hreplace : ε ^ 2 / 2 *
      (((Fintype.card ι : ℝ) + 1) *
        (η * euclideanNorm (w₁.1 - w₂.1) +
          M * euclideanNorm (z₁.1 - z₂.1 - (w₁.1 - w₂.1)))) ≤
    ε ^ 2 / 2 * (((Fintype.card ι : ℝ) + 1) *
      (η * euclideanNorm (w₁.1 - w₂.1) +
        M * euclideanPhaseSize
          (z₁.1 - z₂.1 - (w₁.1 - w₂.1),
            z₁.2 - z₂.2 - (w₁.2 - w₂.2)))) := by
    gcongr
  calc
    euclideanNorm (z₁.1 - z₂.1 - (w₁.1 - w₂.1)) +
        |ε| * euclideanNorm (z₁.2 - z₂.2 - (w₁.2 - w₂.2)) +
        ε ^ 2 / 2 * euclideanNorm
          (gradient z₁.1 - gradient z₂.1 -
            (gradient w₁.1 - gradient w₂.1)) ≤
      euclideanPhaseSize
          (z₁.1 - z₂.1 - (w₁.1 - w₂.1),
            z₁.2 - z₂.2 - (w₁.2 - w₂.2)) +
        |ε| * euclideanPhaseSize
          (z₁.1 - z₂.1 - (w₁.1 - w₂.1),
            z₁.2 - z₂.2 - (w₁.2 - w₂.2)) +
        ε ^ 2 / 2 * (((Fintype.card ι : ℝ) + 1) *
          (η * euclideanNorm (w₁.1 - w₂.1) +
            M * euclideanNorm
              (z₁.1 - z₂.1 - (w₁.1 - w₂.1)))) := by
        exact add_le_add (add_le_add hEq hEpScaled) hscaledF
    _ ≤ euclideanPhaseSize
          (z₁.1 - z₂.1 - (w₁.1 - w₂.1),
            z₁.2 - z₂.2 - (w₁.2 - w₂.2)) +
        |ε| * euclideanPhaseSize
          (z₁.1 - z₂.1 - (w₁.1 - w₂.1),
            z₁.2 - z₂.2 - (w₁.2 - w₂.2)) +
        ε ^ 2 / 2 * (((Fintype.card ι : ℝ) + 1) *
          (η * euclideanNorm (w₁.1 - w₂.1) +
            M * euclideanPhaseSize
              (z₁.1 - z₂.1 - (w₁.1 - w₂.1),
                z₁.2 - z₂.2 - (w₁.2 - w₂.2)))) :=
      add_le_add le_rfl hreplace
    _ = (1 + |ε| + ε ^ 2 / 2 *
          ((Fintype.card ι : ℝ) + 1) * M) *
          euclideanPhaseSize
            (z₁.1 - z₂.1 - (w₁.1 - w₂.1),
              z₁.2 - z₂.2 - (w₁.2 - w₂.2)) +
        ε ^ 2 / 2 * ((Fintype.card ι : ℝ) + 1) * η *
          euclideanNorm (w₁.1 - w₂.1) := by ring

/-- Scalar relative-position propagation rate obtained from the closed
endpoint-position recurrence. -/
noncomputable def compactPairedPositionPropagationRate
    (η M ε R : ℝ) : ℝ :=
  (1 + |ε| + ε ^ 2 / 2 * ((Fintype.card ι : ℝ) + 1) * M) * R +
    ε ^ 2 / 2 * ((Fintype.card ι : ℝ) + 1) * η

/-- Relative form of compact endpoint-position propagation. If the old phase
error is `R` times the reference separation, the new position error is the
explicit propagated rate times that separation. -/
theorem RegularPotential.exists_compact_leapfrog_pairedRelativePositionRate_bound
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ M ≥ 0,
      M ≤ ((β * (Fintype.card ι + 1 : NNReal) : NNReal) : ℝ) ∧
      ∀ {ε R : ℝ} (z₁ z₂ w₁ w₂ : PhaseSpace ι),
        z₁.1 ∈ S → z₂.1 ∈ S → w₁.1 ∈ S → w₂.1 ∈ S →
        dist z₁.1 w₁.1 ≤ δ → dist z₂.1 w₂.1 ≤ δ →
        euclideanPhaseSize
            ((z₁.1 - z₂.1) - (w₁.1 - w₂.1),
              (z₁.2 - z₂.2) - (w₁.2 - w₂.2)) ≤
          R * euclideanNorm (w₁.1 - w₂.1) →
        euclideanNorm
            (((leapfrog gradient ε z₁).1 -
                (leapfrog gradient ε z₂).1) -
              ((leapfrog gradient ε w₁).1 -
                (leapfrog gradient ε w₂).1)) ≤
          compactPairedPositionPropagationRate (ι := ι) η M ε R *
            euclideanNorm (w₁.1 - w₂.1) := by
  obtain ⟨δ, hδ, M, hM, hMglobal, hposition⟩ :=
    hreg.exists_compact_leapfrog_pairedRelativePositionError_bound
      hScompact hSconvex hη
  refine ⟨δ, hδ, M, hM, hMglobal, ?_⟩
  intro ε R z₁ z₂ w₁ w₂ hz₁ hz₂ hw₁ hw₂ hz₁w₁ hz₂w₂ hrelative
  have hpos := hposition (ε := ε) z₁ z₂ w₁ w₂
    hz₁ hz₂ hw₁ hw₂ hz₁w₁ hz₂w₂
  apply hpos.trans
  have hcoef : 0 ≤ 1 + |ε| + ε ^ 2 / 2 *
      ((Fintype.card ι : ℝ) + 1) * M := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hrelative hcoef
  unfold compactPairedPositionPropagationRate
  nlinarith

/-- Compact `C²` specialization of the four-trajectory propagation step.
Relative position errors `R₀` and `R₁` at the two kick locations control the
two paired force discrepancies without losing the initial-separation factor. -/
theorem RegularPotential.exists_compact_leapfrog_pairedRelativePhaseError_bound
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ M ≥ 0,
      M ≤ ((β * (Fintype.card ι + 1 : NNReal) : NNReal) : ℝ) ∧
      ∀ {ε R₀ R₁ : ℝ} (_hε : |ε| ≤ 1)
        (z₁ z₂ w₁ w₂ : PhaseSpace ι),
        z₁.1 ∈ S → z₂.1 ∈ S → w₁.1 ∈ S → w₂.1 ∈ S →
        (leapfrog gradient ε z₁).1 ∈ S →
        (leapfrog gradient ε z₂).1 ∈ S →
        (leapfrog gradient ε w₁).1 ∈ S →
        (leapfrog gradient ε w₂).1 ∈ S →
        dist z₁.1 w₁.1 ≤ δ → dist z₂.1 w₂.1 ≤ δ →
        dist (leapfrog gradient ε z₁).1
          (leapfrog gradient ε w₁).1 ≤ δ →
        dist (leapfrog gradient ε z₂).1
          (leapfrog gradient ε w₂).1 ≤ δ →
        euclideanNorm
            ((z₁.1 - z₂.1) - (w₁.1 - w₂.1)) ≤
          R₀ * euclideanNorm (w₁.1 - w₂.1) →
        euclideanNorm
            (((leapfrog gradient ε z₁).1 -
                (leapfrog gradient ε z₂).1) -
              ((leapfrog gradient ε w₁).1 -
                (leapfrog gradient ε w₂).1)) ≤
          R₁ * euclideanNorm (w₁.1 - w₂.1) →
        euclideanPhaseSize
            (((leapfrog gradient ε z₁).1 -
                (leapfrog gradient ε z₂).1) -
              ((leapfrog gradient ε w₁).1 -
                (leapfrog gradient ε w₂).1),
              ((leapfrog gradient ε z₁).2 -
                (leapfrog gradient ε z₂).2) -
              ((leapfrog gradient ε w₁).2 -
                (leapfrog gradient ε w₂).2)) ≤
          (1 + |ε|) *
              euclideanPhaseSize
                ((z₁.1 - z₂.1) - (w₁.1 - w₂.1),
                  (z₁.2 - z₂.2) - (w₁.2 - w₂.2)) +
            |ε| * ((Fintype.card ι : ℝ) + 1) *
              ((η + M * R₀) * euclideanNorm (w₁.1 - w₂.1) +
                (η * euclideanNorm
                    ((leapfrog gradient ε w₁).1 -
                      (leapfrog gradient ε w₂).1) +
                  M * R₁ * euclideanNorm (w₁.1 - w₂.1)) / 2) := by
  obtain ⟨δ, hδ, M, hM, hMglobal, hforce⟩ :=
    hreg.exists_uniform_euclideanNorm_gradientSub_sub_gradientSub_bound
      hScompact hSconvex hη
  refine ⟨δ, hδ, M, hM, hMglobal, ?_⟩
  intro ε R₀ R₁ hε z₁ z₂ w₁ w₂ hz₁ hz₂ hw₁ hw₂
    hLz₁ hLz₂ hLw₁ hLw₂ hz₁w₁ hz₂w₂ hLz₁w₁ hLz₂w₂ hR₀ hR₁
  have hF0 := hforce hw₂ hw₁ hz₂ hz₁ hz₂w₂ hz₁w₁
  have hF1 := hforce hLw₂ hLw₁ hLz₂ hLz₁ hLz₂w₂ hLz₁w₁
  have hprop := leapfrog_pairedRelativePhaseError_le
    gradient hε z₁ z₂ w₁ w₂
  apply hprop.trans
  have hε0 : 0 ≤ |ε| := abs_nonneg _
  have hhalf : 0 ≤ |ε| / 2 := by positivity
  have hQ : 0 ≤ euclideanNorm (w₁.1 - w₂.1) := euclideanNorm_nonneg _
  have hQ1 : 0 ≤ euclideanNorm
      ((leapfrog gradient ε w₁).1 -
        (leapfrog gradient ε w₂).1) := euclideanNorm_nonneg _
  have hMR₀ := mul_le_mul_of_nonneg_left hR₀ hM
  have hMR₁ := mul_le_mul_of_nonneg_left hR₁ hM
  have hD : 0 ≤ (Fintype.card ι : ℝ) + 1 := by positivity
  have hF0' : euclideanNorm
      (gradient z₁.1 - gradient z₂.1 -
        (gradient w₁.1 - gradient w₂.1)) ≤
      ((Fintype.card ι : ℝ) + 1) * (η + M * R₀) *
        euclideanNorm (w₁.1 - w₂.1) := by
    apply hF0.trans
    calc
      ((Fintype.card ι : ℝ) + 1) *
          (η * euclideanNorm (w₁.1 - w₂.1) +
            M * euclideanNorm (z₁.1 - z₂.1 - (w₁.1 - w₂.1))) ≤
        ((Fintype.card ι : ℝ) + 1) *
          (η * euclideanNorm (w₁.1 - w₂.1) +
            M * (R₀ * euclideanNorm (w₁.1 - w₂.1))) := by
          gcongr
      _ = ((Fintype.card ι : ℝ) + 1) * (η + M * R₀) *
          euclideanNorm (w₁.1 - w₂.1) := by ring
  have hF1' : euclideanNorm
      (gradient (leapfrog gradient ε z₁).1 -
          gradient (leapfrog gradient ε z₂).1 -
        (gradient (leapfrog gradient ε w₁).1 -
          gradient (leapfrog gradient ε w₂).1)) ≤
      ((Fintype.card ι : ℝ) + 1) *
        (η * euclideanNorm
            ((leapfrog gradient ε w₁).1 -
              (leapfrog gradient ε w₂).1) +
          M * R₁ * euclideanNorm (w₁.1 - w₂.1)) := by
    apply hF1.trans
    apply mul_le_mul_of_nonneg_left ?_ hD
    linarith
  calc
    (1 + |ε|) *
          euclideanPhaseSize
            (z₁.1 - z₂.1 - (w₁.1 - w₂.1),
              z₁.2 - z₂.2 - (w₁.2 - w₂.2)) +
        |ε| * euclideanNorm
          (gradient z₁.1 - gradient z₂.1 -
            (gradient w₁.1 - gradient w₂.1)) +
        |ε| / 2 * euclideanNorm
          (gradient (leapfrog gradient ε z₁).1 -
              gradient (leapfrog gradient ε z₂).1 -
            (gradient (leapfrog gradient ε w₁).1 -
              gradient (leapfrog gradient ε w₂).1)) ≤
      (1 + |ε|) *
          euclideanPhaseSize
            (z₁.1 - z₂.1 - (w₁.1 - w₂.1),
              z₁.2 - z₂.2 - (w₁.2 - w₂.2)) +
        |ε| * (((Fintype.card ι : ℝ) + 1) *
          (η + M * R₀) * euclideanNorm (w₁.1 - w₂.1)) +
        |ε| / 2 * (((Fintype.card ι : ℝ) + 1) *
          (η * euclideanNorm
              ((leapfrog gradient ε w₁).1 -
                (leapfrog gradient ε w₂).1) +
            M * R₁ * euclideanNorm (w₁.1 - w₂.1))) := by
        gcongr
    _ = (1 + |ε|) *
          euclideanPhaseSize
            (z₁.1 - z₂.1 - (w₁.1 - w₂.1),
              z₁.2 - z₂.2 - (w₁.2 - w₂.2)) +
        |ε| * ((Fintype.card ι : ℝ) + 1) *
          ((η + M * R₀) * euclideanNorm (w₁.1 - w₂.1) +
            (η * euclideanNorm
                ((leapfrog gradient ε w₁).1 -
                  (leapfrog gradient ε w₂).1) +
              M * R₁ * euclideanNorm (w₁.1 - w₂.1)) / 2) := by ring

/-- Raw compact four-trajectory phase propagation, retaining the actual old
and new relative position errors. This is the form consumed by the closed
phase recurrence, before introducing scalar relative-error rates. -/
theorem RegularPotential.exists_compact_leapfrog_pairedPhaseRaw_bound
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ M ≥ 0,
      M ≤ ((β * (Fintype.card ι + 1 : NNReal) : NNReal) : ℝ) ∧
      ∀ {ε : ℝ} (_hε : |ε| ≤ 1)
        (z₁ z₂ w₁ w₂ : PhaseSpace ι),
        z₁.1 ∈ S → z₂.1 ∈ S → w₁.1 ∈ S → w₂.1 ∈ S →
        (leapfrog gradient ε z₁).1 ∈ S →
        (leapfrog gradient ε z₂).1 ∈ S →
        (leapfrog gradient ε w₁).1 ∈ S →
        (leapfrog gradient ε w₂).1 ∈ S →
        dist z₁.1 w₁.1 ≤ δ → dist z₂.1 w₂.1 ≤ δ →
        dist (leapfrog gradient ε z₁).1
          (leapfrog gradient ε w₁).1 ≤ δ →
        dist (leapfrog gradient ε z₂).1
          (leapfrog gradient ε w₂).1 ≤ δ →
        pairedPhaseError
            (leapfrog gradient ε z₁) (leapfrog gradient ε z₂)
            (leapfrog gradient ε w₁) (leapfrog gradient ε w₂) ≤
          (1 + |ε|) * pairedPhaseError z₁ z₂ w₁ w₂ +
            |ε| * ((Fintype.card ι : ℝ) + 1) *
              (η * euclideanNorm (w₁.1 - w₂.1) +
                M * euclideanNorm
                  ((z₁.1 - z₂.1) - (w₁.1 - w₂.1)) +
                (η * euclideanNorm
                    ((leapfrog gradient ε w₁).1 -
                      (leapfrog gradient ε w₂).1) +
                  M * euclideanNorm
                    (((leapfrog gradient ε z₁).1 -
                        (leapfrog gradient ε z₂).1) -
                      ((leapfrog gradient ε w₁).1 -
                        (leapfrog gradient ε w₂).1))) / 2) := by
  obtain ⟨δ, hδ, M, hM, hMglobal, hforce⟩ :=
    hreg.exists_uniform_euclideanNorm_gradientSub_sub_gradientSub_bound
      hScompact hSconvex hη
  refine ⟨δ, hδ, M, hM, hMglobal, ?_⟩
  intro ε hε z₁ z₂ w₁ w₂ hz₁ hz₂ hw₁ hw₂
    hLz₁ hLz₂ hLw₁ hLw₂ hz₁w₁ hz₂w₂ hLz₁w₁ hLz₂w₂
  have hF0 := hforce hw₂ hw₁ hz₂ hz₁ hz₂w₂ hz₁w₁
  have hF1 := hforce hLw₂ hLw₁ hLz₂ hLz₁ hLz₂w₂ hLz₁w₁
  have hprop := leapfrog_pairedRelativePhaseError_le
    gradient hε z₁ z₂ w₁ w₂
  unfold pairedPhaseError
  apply hprop.trans
  have hε0 : 0 ≤ |ε| := abs_nonneg _
  have hhalf : 0 ≤ |ε| / 2 := by positivity
  have hF0scaled := mul_le_mul_of_nonneg_left hF0 hε0
  have hF1scaled := mul_le_mul_of_nonneg_left hF1 hhalf
  calc
    (1 + |ε|) *
          euclideanPhaseSize
            (z₁.1 - z₂.1 - (w₁.1 - w₂.1),
              z₁.2 - z₂.2 - (w₁.2 - w₂.2)) +
        |ε| * euclideanNorm
          (gradient z₁.1 - gradient z₂.1 -
            (gradient w₁.1 - gradient w₂.1)) +
        |ε| / 2 * euclideanNorm
          (gradient (leapfrog gradient ε z₁).1 -
              gradient (leapfrog gradient ε z₂).1 -
            (gradient (leapfrog gradient ε w₁).1 -
              gradient (leapfrog gradient ε w₂).1)) ≤
      (1 + |ε|) *
          euclideanPhaseSize
            (z₁.1 - z₂.1 - (w₁.1 - w₂.1),
              z₁.2 - z₂.2 - (w₁.2 - w₂.2)) +
        |ε| * (((Fintype.card ι : ℝ) + 1) *
          (η * euclideanNorm (w₁.1 - w₂.1) +
            M * euclideanNorm
              (z₁.1 - z₂.1 - (w₁.1 - w₂.1)))) +
        |ε| / 2 * (((Fintype.card ι : ℝ) + 1) *
          (η * euclideanNorm
              ((leapfrog gradient ε w₁).1 -
                (leapfrog gradient ε w₂).1) +
            M * euclideanNorm
              ((leapfrog gradient ε z₁).1 -
                  (leapfrog gradient ε z₂).1 -
                ((leapfrog gradient ε w₁).1 -
                  (leapfrog gradient ε w₂).1)))) := by
      exact add_le_add (add_le_add le_rfl hF0scaled) hF1scaled
    _ = (1 + |ε|) *
          euclideanPhaseSize
            (z₁.1 - z₂.1 - (w₁.1 - w₂.1),
              z₁.2 - z₂.2 - (w₁.2 - w₂.2)) +
        |ε| * ((Fintype.card ι : ℝ) + 1) *
          (η * euclideanNorm (w₁.1 - w₂.1) +
            M * euclideanNorm
              (z₁.1 - z₂.1 - (w₁.1 - w₂.1)) +
            (η * euclideanNorm
                ((leapfrog gradient ε w₁).1 -
                  (leapfrog gradient ε w₂).1) +
              M * euclideanNorm
                ((leapfrog gradient ε z₁).1 -
                    (leapfrog gradient ε z₂).1 -
                  ((leapfrog gradient ε w₁).1 -
                    (leapfrog gradient ε w₂).1))) / 2) := by ring

/-- Rate appearing in the sharp norm-level phase stability factor. -/
noncomputable def leapfrogNormStabilityRate (β : NNReal) : ℝ :=
  1 + 2 * (β : ℝ) + (β : ℝ) ^ 2 / 4

theorem leapfrogNormStabilityRate_nonneg (β : NNReal) :
    0 ≤ leapfrogNormStabilityRate β := by
  unfold leapfrogNormStabilityRate
  positivity

/-- For `|ε| ≤ 1`, total Euclidean phase separation grows by at most a factor
`1 + Cβ |ε|`. This has the small-step form needed for fixed integration-time
stability. -/
theorem leapfrog_euclideanNorm_phaseSub_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {ε : ℝ} (hε : |ε| ≤ 1) (z₁ z₂ : PhaseSpace ι) :
    euclideanNorm
          ((leapfrog gradient ε z₁).1 - (leapfrog gradient ε z₂).1) +
        euclideanNorm
          ((leapfrog gradient ε z₁).2 - (leapfrog gradient ε z₂).2) ≤
      (1 + leapfrogNormStabilityRate β * |ε|) *
        (euclideanNorm (z₁.1 - z₂.1) +
          euclideanNorm (z₁.2 - z₂.2)) := by
  let Q := euclideanNorm (z₁.1 - z₂.1)
  let P := euclideanNorm (z₁.2 - z₂.2)
  let Q' := euclideanNorm
    ((leapfrog gradient ε z₁).1 - (leapfrog gradient ε z₂).1)
  let P' := euclideanNorm
    ((leapfrog gradient ε z₁).2 - (leapfrog gradient ε z₂).2)
  let e := |ε|
  let b := (β : ℝ)
  have he : 0 ≤ e := abs_nonneg ε
  have hb : 0 ≤ b := β.coe_nonneg
  have hQ0 : 0 ≤ Q := euclideanNorm_nonneg _
  have hP0 : 0 ≤ P := euclideanNorm_nonneg _
  have he2 : ε ^ 2 = e ^ 2 := by
    dsimp [e]
    exact (sq_abs ε).symm
  have hQ : Q' ≤ (1 + b * e ^ 2 / 2) * Q + e * P := by
    simpa only [Q, P, Q', e, b, he2] using
      leapfrog_euclideanNorm_positionSub_le hreg ε z₁ z₂
  have hP : P' ≤ P + (e * b / 2) * (Q + Q') := by
    simpa only [Q, P, Q', P', e, b] using
      leapfrog_euclideanNorm_momentumSub_le hreg ε z₁ z₂
  have he_sq : e ^ 2 ≤ e := by nlinarith
  have he_cube_step := mul_le_mul_of_nonneg_left he_sq he
  have he_cube : e ^ 3 ≤ e := by nlinarith
  have hscale : 0 ≤ 1 + e * b / 2 := by positivity
  have hQscaled := mul_le_mul_of_nonneg_left hQ hscale
  have heQb := mul_le_mul_of_nonneg_left he_sq (mul_nonneg hb hQ0)
  have heQ := mul_le_mul_of_nonneg_left he_cube (mul_nonneg (sq_nonneg b) hQ0)
  have heP := mul_le_mul_of_nonneg_left he_sq (mul_nonneg hb hP0)
  have heb2 := mul_le_mul_of_nonneg_left he_sq hb
  have hb2e3 := mul_le_mul_of_nonneg_left he_cube (sq_nonneg b)
  have hcombined : Q' + P' ≤
      (1 + e * b / 2) * ((1 + b * e ^ 2 / 2) * Q + e * P) +
        P + e * b / 2 * Q := by
    nlinarith
  let C := 1 + 2 * b + b ^ 2 / 4
  have hcoefQ :
      1 + b * e + b * e ^ 2 / 2 + b ^ 2 * e ^ 3 / 4 ≤ 1 + C * e := by
    dsimp [C]
    nlinarith
  have hcoefP : 1 + e + b * e ^ 2 / 2 ≤ 1 + C * e := by
    dsimp [C]
    nlinarith [mul_nonneg hb he]
  have hcoefQmul := mul_le_mul_of_nonneg_right hcoefQ hQ0
  have hcoefPmul := mul_le_mul_of_nonneg_right hcoefP hP0
  change Q' + P' ≤
    (1 + leapfrogNormStabilityRate β * e) * (Q + P)
  unfold leapfrogNormStabilityRate
  dsimp only [b] at *
  dsimp only [C] at *
  nlinarith [hcombined]

/-- One-step absolute phase-size recurrence. The homogeneous factor is the
sharp relative-stability factor and the affine term is generated by
`∇U(0)`. -/
theorem leapfrog_euclideanPhaseSize_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {ε : ℝ} (hε : |ε| ≤ 1) (z : PhaseSpace ι) :
    euclideanPhaseSize (leapfrog gradient ε z) ≤
      (1 + leapfrogNormStabilityRate β * |ε|) * euclideanPhaseSize z +
        (2 + (β : ℝ)) * |ε| * euclideanNorm (gradient 0) := by
  have hq := euclideanNorm_add_le
    ((leapfrog gradient ε z).1 - (leapfrog gradient ε (0, 0)).1)
    (leapfrog gradient ε (0, 0)).1
  have hp := euclideanNorm_add_le
    ((leapfrog gradient ε z).2 - (leapfrog gradient ε (0, 0)).2)
    (leapfrog gradient ε (0, 0)).2
  have hqsum :
      (leapfrog gradient ε z).1 - (leapfrog gradient ε (0, 0)).1 +
        (leapfrog gradient ε (0, 0)).1 = (leapfrog gradient ε z).1 := by
    abel
  have hpsum :
      (leapfrog gradient ε z).2 - (leapfrog gradient ε (0, 0)).2 +
        (leapfrog gradient ε (0, 0)).2 = (leapfrog gradient ε z).2 := by
    abel
  rw [hqsum] at hq
  rw [hpsum] at hp
  have hrelative := leapfrog_euclideanNorm_phaseSub_le
    hreg hε z (0, 0)
  have hzero := leapfrog_zero_euclideanPhaseSize_le hreg hε
  unfold euclideanPhaseSize at *
  apply le_trans (add_le_add hq hp)
  have hsum := add_le_add hrelative hzero
  simp only [sub_zero] at hsum
  linarith

/-- Sharp discrete Grönwall bound for aligned trajectories. The base is
`1 + Cβ |ε|`, so it remains controlled when `n |ε|` is bounded. -/
theorem leapfrogN_euclideanNorm_phaseSub_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {ε : ℝ} (hε : |ε| ≤ 1) (n : ℕ) (z₁ z₂ : PhaseSpace ι) :
    euclideanNorm
          ((leapfrogN gradient ε n z₁).1 -
            (leapfrogN gradient ε n z₂).1) +
        euclideanNorm
          ((leapfrogN gradient ε n z₁).2 -
            (leapfrogN gradient ε n z₂).2) ≤
      (1 + leapfrogNormStabilityRate β * |ε|) ^ n *
        (euclideanNorm (z₁.1 - z₂.1) +
          euclideanNorm (z₁.2 - z₂.2)) := by
  induction n with
  | zero => simp [leapfrogN]
  | succ n ih =>
      simp only [leapfrogN, Function.iterate_succ_apply']
      apply le_trans (leapfrog_euclideanNorm_phaseSub_le hreg hε _ _)
      have hfactor : 0 ≤ 1 + leapfrogNormStabilityRate β * |ε| := by
        have hrate := leapfrogNormStabilityRate_nonneg β
        exact add_nonneg zero_le_one (mul_nonneg hrate (abs_nonneg ε))
      have hmul := mul_le_mul_of_nonneg_left ih hfactor
      rw [pow_succ]
      simpa only [leapfrogN, mul_assoc, mul_comm, mul_left_comm] using hmul

/-- Affine discrete Grönwall bound for absolute phase size. -/
theorem leapfrogN_euclideanPhaseSize_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {ε : ℝ} (hε : |ε| ≤ 1) (n : ℕ) (z : PhaseSpace ι) :
    euclideanPhaseSize (leapfrogN gradient ε n z) ≤
      (1 + leapfrogNormStabilityRate β * |ε|) ^ n *
        (euclideanPhaseSize z +
          (n : ℝ) * ((2 + (β : ℝ)) * |ε| *
            euclideanNorm (gradient 0))) := by
  let A := 1 + leapfrogNormStabilityRate β * |ε|
  let B := (2 + (β : ℝ)) * |ε| * euclideanNorm (gradient 0)
  have hAone : 1 ≤ A := by
    dsimp [A]
    exact le_add_of_nonneg_right
      (mul_nonneg (leapfrogNormStabilityRate_nonneg β) (abs_nonneg ε))
  have hA : 0 ≤ A := zero_le_one.trans hAone
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg
      (mul_nonneg (add_nonneg (by norm_num) β.coe_nonneg) (abs_nonneg ε))
      (euclideanNorm_nonneg _)
  induction n with
  | zero => simp [leapfrogN]
  | succ n ih =>
      simp only [leapfrogN, Function.iterate_succ_apply']
      have hstep := leapfrog_euclideanPhaseSize_le hreg hε
        (leapfrogN gradient ε n z)
      change euclideanPhaseSize
          (leapfrog gradient ε (leapfrogN gradient ε n z)) ≤
        A ^ (n + 1) *
          (euclideanPhaseSize z + ((n + 1 : ℕ) : ℝ) * B)
      change euclideanPhaseSize (leapfrogN gradient ε n z) ≤
        A ^ n * (euclideanPhaseSize z + (n : ℝ) * B) at ih
      change euclideanPhaseSize
          (leapfrog gradient ε (leapfrogN gradient ε n z)) ≤
        A * euclideanPhaseSize (leapfrogN gradient ε n z) + B at hstep
      apply le_trans hstep
      have hscaled := mul_le_mul_of_nonneg_left ih hA
      have hpow : 1 ≤ A ^ (n + 1) := one_le_pow₀ hAone
      have hforcing : B ≤ A ^ (n + 1) * B := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow hB
      calc
        A * euclideanPhaseSize (leapfrogN gradient ε n z) + B ≤
            A * (A ^ n * (euclideanPhaseSize z + (n : ℝ) * B)) + B := by
          simpa only [add_comm] using add_le_add_right hscaled B
        _ = A ^ (n + 1) *
              (euclideanPhaseSize z + (n : ℝ) * B) + B := by
          rw [pow_succ]
          ring
        _ ≤ A ^ (n + 1) *
              (euclideanPhaseSize z + (n : ℝ) * B) + A ^ (n + 1) * B :=
          by
            have hx := add_le_add_left hforcing
              (A ^ (n + 1) * (euclideanPhaseSize z + (n : ℝ) * B))
            simpa only [add_comm] using hx
        _ = A ^ (n + 1) *
              (euclideanPhaseSize z + ((n + 1 : ℕ) : ℝ) * B) := by
          norm_num
          ring

/-- The sharp power factor is bounded by an exponential in total integration
time `n |ε|`. -/
theorem leapfrogNormStabilityFactor_pow_le_exp
    (β : NNReal) (ε : ℝ) (n : ℕ) :
    (1 + leapfrogNormStabilityRate β * |ε|) ^ n ≤
      Real.exp (leapfrogNormStabilityRate β * (n : ℝ) * |ε|) := by
  let x := leapfrogNormStabilityRate β * |ε|
  have hx : 0 ≤ x := mul_nonneg (leapfrogNormStabilityRate_nonneg β) (abs_nonneg ε)
  have hone : 1 + x ≤ Real.exp x := by
    simpa [add_comm] using Real.add_one_le_exp x
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + x) hone n
  rw [← Real.exp_nat_mul] at hpow
  simpa only [x, Nat.cast_ofNat, mul_assoc, mul_comm, mul_left_comm] using hpow

/-- Fixed-integration-time stability: if `n |ε| ≤ T`, aligned phase
separation is bounded by `exp(Cβ T)` times its initial value. -/
theorem leapfrogN_euclideanNorm_phaseSub_le_exp
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {ε : ℝ} (hε : |ε| ≤ 1) (n : ℕ) {T : ℝ}
    (horizon : (n : ℝ) * |ε| ≤ T) (z₁ z₂ : PhaseSpace ι) :
    euclideanNorm
          ((leapfrogN gradient ε n z₁).1 -
            (leapfrogN gradient ε n z₂).1) +
        euclideanNorm
          ((leapfrogN gradient ε n z₁).2 -
            (leapfrogN gradient ε n z₂).2) ≤
      Real.exp (leapfrogNormStabilityRate β * T) *
        (euclideanNorm (z₁.1 - z₂.1) +
          euclideanNorm (z₁.2 - z₂.2)) := by
  apply le_trans (leapfrogN_euclideanNorm_phaseSub_le hreg hε n z₁ z₂)
  have hpow := leapfrogNormStabilityFactor_pow_le_exp β ε n
  have hrate := leapfrogNormStabilityRate_nonneg β
  have hexp : Real.exp (leapfrogNormStabilityRate β * (n : ℝ) * |ε|) ≤
      Real.exp (leapfrogNormStabilityRate β * T) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hfactor := hpow.trans hexp
  have hphase : 0 ≤ euclideanNorm (z₁.1 - z₂.1) +
      euclideanNorm (z₁.2 - z₂.2) :=
    add_nonneg (euclideanNorm_nonneg _) (euclideanNorm_nonneg _)
  exact mul_le_mul_of_nonneg_right hfactor hphase

/-- Uniform absolute phase-size bound at fixed integration horizon. In
particular, it is independent of the number of leapfrog steps once
`n |ε| ≤ T`. -/
theorem leapfrogN_euclideanPhaseSize_le_exp
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {ε : ℝ} (hε : |ε| ≤ 1) (n : ℕ) {T : ℝ}
    (horizon : (n : ℝ) * |ε| ≤ T) (z : PhaseSpace ι) :
    euclideanPhaseSize (leapfrogN gradient ε n z) ≤
      Real.exp (leapfrogNormStabilityRate β * T) *
        (euclideanPhaseSize z +
          (2 + (β : ℝ)) * T * euclideanNorm (gradient 0)) := by
  apply le_trans (leapfrogN_euclideanPhaseSize_le hreg hε n z)
  have hpow := leapfrogNormStabilityFactor_pow_le_exp β ε n
  have hrate := leapfrogNormStabilityRate_nonneg β
  have hexp : Real.exp (leapfrogNormStabilityRate β * (n : ℝ) * |ε|) ≤
      Real.exp (leapfrogNormStabilityRate β * T) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hfactor := hpow.trans hexp
  have hD : 0 ≤ 2 + (β : ℝ) := add_nonneg (by norm_num) β.coe_nonneg
  have hG : 0 ≤ euclideanNorm (gradient 0) := euclideanNorm_nonneg _
  have hforcing :
      (n : ℝ) * ((2 + (β : ℝ)) * |ε| * euclideanNorm (gradient 0)) ≤
        (2 + (β : ℝ)) * T * euclideanNorm (gradient 0) := by
    have hmul := mul_le_mul_of_nonneg_left horizon (mul_nonneg hD hG)
    nlinarith
  have hinsmall : 0 ≤ euclideanPhaseSize z +
      (n : ℝ) * ((2 + (β : ℝ)) * |ε| * euclideanNorm (gradient 0)) := by
    exact add_nonneg (euclideanPhaseSize_nonneg z) (by positivity)
  have hin' := add_le_add_left hforcing (euclideanPhaseSize z)
  have hin : euclideanPhaseSize z +
      (n : ℝ) * ((2 + (β : ℝ)) * |ε| * euclideanNorm (gradient 0)) ≤
        euclideanPhaseSize z +
          (2 + (β : ℝ)) * T * euclideanNorm (gradient 0) := by
    simpa only [add_comm] using hin'
  apply le_trans (mul_le_mul_of_nonneg_right hfactor hinsmall)
  exact mul_le_mul_of_nonneg_left hin (Real.exp_pos _).le

/-- Quantitative relative-position recurrence at every aligned leapfrog
index. -/
theorem leapfrogN_squaredPositionSub_succ_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (ε : ℝ) (n : ℕ) (z₁ z₂ : PhaseSpace ι) :
    squaredEuclideanNorm
        ((leapfrogN gradient ε (n + 1) z₁).1 -
          (leapfrogN gradient ε (n + 1) z₂).1) ≤
      (3 + 3 * (β : ℝ) ^ 2 * ε ^ 4 / 4) *
          squaredEuclideanNorm
            ((leapfrogN gradient ε n z₁).1 -
              (leapfrogN gradient ε n z₂).1) +
        3 * ε ^ 2 * squaredEuclideanNorm
          ((leapfrogN gradient ε n z₁).2 -
            (leapfrogN gradient ε n z₂).2) := by
  rw [show n + 1 = Nat.succ n by omega]
  simp only [leapfrogN, Function.iterate_succ_apply']
  exact leapfrog_squaredPositionSub_le hreg ε _ _

/-- Quantitative relative-momentum recurrence at every aligned leapfrog
index. -/
theorem leapfrogN_squaredMomentumSub_succ_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (ε : ℝ) (n : ℕ) (z₁ z₂ : PhaseSpace ι) :
    squaredEuclideanNorm
        ((leapfrogN gradient ε (n + 1) z₁).2 -
          (leapfrogN gradient ε (n + 1) z₂).2) ≤
      3 * squaredEuclideanNorm
          ((leapfrogN gradient ε n z₁).2 -
            (leapfrogN gradient ε n z₂).2) +
        (3 * ε ^ 2 * (β : ℝ) ^ 2 / 4) *
          (squaredEuclideanNorm
              ((leapfrogN gradient ε n z₁).1 -
                (leapfrogN gradient ε n z₂).1) +
            squaredEuclideanNorm
              ((leapfrogN gradient ε (n + 1) z₁).1 -
                (leapfrogN gradient ε (n + 1) z₂).1)) := by
  rw [show n + 1 = Nat.succ n by omega]
  simp only [leapfrogN, Function.iterate_succ_apply']
  exact leapfrog_squaredMomentumSub_le hreg ε _ _

/-- The sum of squared relative position and momentum grows by at most the
conservative stability factor in one leapfrog step. -/
theorem leapfrog_squaredPhaseSub_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (ε : ℝ) (z₁ z₂ : PhaseSpace ι) :
    squaredEuclideanNorm
          ((leapfrog gradient ε z₁).1 - (leapfrog gradient ε z₂).1) +
        squaredEuclideanNorm
          ((leapfrog gradient ε z₁).2 - (leapfrog gradient ε z₂).2) ≤
      leapfrogRelativeStabilityFactor β ε *
        (squaredEuclideanNorm (z₁.1 - z₂.1) +
          squaredEuclideanNorm (z₁.2 - z₂.2)) := by
  let D := squaredEuclideanNorm (z₁.1 - z₂.1)
  let V := squaredEuclideanNorm (z₁.2 - z₂.2)
  let D' := squaredEuclideanNorm
    ((leapfrog gradient ε z₁).1 - (leapfrog gradient ε z₂).1)
  let V' := squaredEuclideanNorm
    ((leapfrog gradient ε z₁).2 - (leapfrog gradient ε z₂).2)
  let A := 3 + 3 * (β : ℝ) ^ 2 * ε ^ 4 / 4
  let B := 3 * ε ^ 2
  let C := 3 * ε ^ 2 * (β : ℝ) ^ 2 / 4
  have hD : D' ≤ A * D + B * V :=
    leapfrog_squaredPositionSub_le hreg ε z₁ z₂
  have hV : V' ≤ 3 * V + C * (D + D') :=
    leapfrog_squaredMomentumSub_le hreg ε z₁ z₂
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hD0 : 0 ≤ D := squaredEuclideanNorm_nonneg _
  have hV0 : 0 ≤ V := squaredEuclideanNorm_nonneg _
  have hDscaled := mul_le_mul_of_nonneg_left hD (by linarith : 0 ≤ 1 + C)
  change D' + V' ≤
    (((1 + C) * A + C) + ((1 + C) * B + 3)) * (D + V)
  have hKD : 0 ≤ (1 + C) * A + C := by positivity
  have hKV : 0 ≤ (1 + C) * B + 3 := by positivity
  have hcombined : D' + V' ≤
      ((1 + C) * A + C) * D + ((1 + C) * B + 3) * V := by
    nlinarith
  apply le_trans hcombined
  nlinarith [mul_nonneg hKD hV0, mul_nonneg hKV hD0]

/-- Discrete Grönwall bound for aligned leapfrog trajectories: phase
separation after `n` steps is bounded by the `n`th power of the one-step
stability factor. -/
theorem leapfrogN_squaredPhaseSub_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (ε : ℝ) (n : ℕ) (z₁ z₂ : PhaseSpace ι) :
    squaredEuclideanNorm
          ((leapfrogN gradient ε n z₁).1 -
            (leapfrogN gradient ε n z₂).1) +
        squaredEuclideanNorm
          ((leapfrogN gradient ε n z₁).2 -
            (leapfrogN gradient ε n z₂).2) ≤
      (leapfrogRelativeStabilityFactor β ε) ^ n *
        (squaredEuclideanNorm (z₁.1 - z₂.1) +
          squaredEuclideanNorm (z₁.2 - z₂.2)) := by
  induction n with
  | zero => simp [leapfrogN]
  | succ n ih =>
      simp only [leapfrogN, Function.iterate_succ_apply']
      apply le_trans (leapfrog_squaredPhaseSub_le hreg ε _ _)
      have hfactor := leapfrogRelativeStabilityFactor_nonneg β ε
      have hmul := mul_le_mul_of_nonneg_left ih hfactor
      rw [pow_succ]
      simpa only [leapfrogN, mul_assoc, mul_comm, mul_left_comm] using hmul

omit [Fintype ι] in
/-- Exact position-difference formula after one leapfrog update with a shared
initial momentum. -/
theorem leapfrog_sharedMomentum_position_sub
    (gradient : Position ι → Position ι) (ε : ℝ)
    (q₁ q₂ : Position ι) (p : Momentum ι) :
    (leapfrog gradient ε (q₁, p)).1 -
        (leapfrog gradient ε (q₂, p)).1 =
      (q₁ - q₂) - (ε ^ 2 / 2) • (gradient q₁ - gradient q₂) := by
  funext i
  simp only [leapfrog, drift, halfKick, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- Explicit relative local-position error rate comparing one shared-momentum
leapfrog step with exact Hamiltonian flow for the same signed time. The rate
is `O(ε²)`; the first term controls exact relative displacement and the second
is leapfrog's explicit half-force correction. -/
noncomputable def leapfrogExactOneStepRelativePositionErrorRate
    (β : NNReal) (ε : ℝ) : ℝ :=
  (((Fintype.card ι : ℝ) + 1) ^ 2 * (β : ℝ) *
      exactFlowPositionStabilityFactor (ι := ι) β ε + (β : ℝ) / 2) *
    |ε| ^ 2

/-- Relative local-position error rate for arbitrary paired initial phases.
It differs from the shared-momentum rate only by using full-phase exact-flow
stability. -/
noncomputable def leapfrogExactOneStepPhasePositionErrorRate
    (β : NNReal) (ε : ℝ) : ℝ :=
  (((Fintype.card ι : ℝ) + 1) ^ 2 * (β : ℝ) *
      exactFlowPhaseStabilityFactor (ι := ι) β ε + (β : ℝ) / 2) *
    |ε| ^ 2

theorem leapfrogExactOneStepRelativePositionErrorRate_nonneg
    (β : NNReal) (ε : ℝ) :
    0 ≤ leapfrogExactOneStepRelativePositionErrorRate (ι := ι) β ε := by
  unfold leapfrogExactOneStepRelativePositionErrorRate
  have hstability := exactFlowPositionStabilityFactor_pos (ι := ι) β ε
  have hsum : 0 ≤
      ((Fintype.card ι : ℝ) + 1) ^ 2 * (β : ℝ) *
          exactFlowPositionStabilityFactor (ι := ι) β ε + (β : ℝ) / 2 := by
    positivity
  exact mul_nonneg hsum (sq_nonneg _)

theorem continuous_leapfrogExactOneStepRelativePositionErrorRate
    (β : NNReal) :
    Continuous
      (leapfrogExactOneStepRelativePositionErrorRate (ι := ι) β) := by
  unfold leapfrogExactOneStepRelativePositionErrorRate
  exact (((continuous_const.mul continuous_const).mul
    (continuous_exactFlowPositionStabilityFactor β)).add
      continuous_const).mul (continuous_abs.pow 2)

@[simp]
theorem leapfrogExactOneStepRelativePositionErrorRate_zero (β : NNReal) :
    leapfrogExactOneStepRelativePositionErrorRate (ι := ι) β 0 = 0 := by
  simp [leapfrogExactOneStepRelativePositionErrorRate]

/-- Every positive relative position-error allowance holds for all signed
one-step sizes in one sufficiently small symmetric neighborhood of zero. -/
theorem exists_pos_forall_leapfrogExactOneStepRelativePositionErrorRate_lt
    (β : NNReal) {η : ℝ} (hη : 0 < η) :
    ∃ εbar > 0, ∀ ε, |ε| ≤ εbar →
      leapfrogExactOneStepRelativePositionErrorRate (ι := ι) β ε < η :=
  exists_pos_forall_abs_le_of_continuousAt_zero
    (continuous_leapfrogExactOneStepRelativePositionErrorRate
      (ι := ι) β).continuousAt
    (leapfrogExactOneStepRelativePositionErrorRate_zero (ι := ι) β) hη

/-- One shared-momentum leapfrog position difference approximates the exact
position difference with relative error bounded by the explicit quadratic
rate above. -/
theorem leapfrog_sharedMomentum_exactFlow_positionSub_error_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (hcurve₁ : IsHamiltonianCurve gradient q₁ p₁)
    (hcurve₂ : IsHamiltonianCurve gradient q₂ p₂)
    (hq₁ : q₁ 0 = q₁₀) (hq₂ : q₂ 0 = q₂₀)
    (hp₁ : p₁ 0 = p) (hp₂ : p₂ 0 = p) (ε : ℝ) :
    euclideanNorm
        (((leapfrog gradient ε (q₁₀, p)).1 -
            (leapfrog gradient ε (q₂₀, p)).1) -
          (q₁ ε - q₂ ε)) ≤
      leapfrogExactOneStepRelativePositionErrorRate (ι := ι) β ε *
        euclideanNorm (q₁₀ - q₂₀) := by
  have hp : p₁ 0 = p₂ 0 := hp₁.trans hp₂.symm
  have hupper := hreg.euclideanNorm_position_sub_le_on_uIcc
    hcurve₁ hcurve₂ hp (t := ε)
  have hexact := hreg.euclideanNorm_positionSub_sub_initial_le
    hcurve₁ hcurve₂
    (exactFlowPositionStabilityFactor_pos (ι := ι) β ε).le hp hupper
  rw [hq₁, hq₂] at hexact
  have hgradient := hreg.euclideanNorm_gradient_sub_le q₁₀ q₂₀
  have hhalf : 0 ≤ ε ^ 2 / 2 := by positivity
  have hdecomp :
      ((leapfrog gradient ε (q₁₀, p)).1 -
          (leapfrog gradient ε (q₂₀, p)).1) -
        (q₁ ε - q₂ ε) =
      -((q₁ ε - q₂ ε) - (q₁₀ - q₂₀)) -
        (ε ^ 2 / 2) • (gradient q₁₀ - gradient q₂₀) := by
    rw [leapfrog_sharedMomentum_position_sub]
    abel
  rw [hdecomp]
  apply (euclideanNorm_sub_le _ _).trans
  rw [euclideanNorm_neg, euclideanNorm_smul,
    abs_of_nonneg hhalf]
  unfold leapfrogExactOneStepRelativePositionErrorRate
  have hQ : 0 ≤ euclideanNorm (q₁₀ - q₂₀) := euclideanNorm_nonneg _
  have hεsq : ε ^ 2 = |ε| ^ 2 := (sq_abs ε).symm
  have hforce := mul_le_mul_of_nonneg_left hgradient hhalf
  calc
    euclideanNorm ((q₁ ε - q₂ ε) - (q₁₀ - q₂₀)) +
        ε ^ 2 / 2 * euclideanNorm (gradient q₁₀ - gradient q₂₀) ≤
      (((Fintype.card ι : ℝ) + 1) ^ 2 * (β : ℝ) *
          exactFlowPositionStabilityFactor β ε * |ε| ^ 2) *
          euclideanNorm (q₁₀ - q₂₀) +
        ε ^ 2 / 2 * ((β : ℝ) * euclideanNorm (q₁₀ - q₂₀)) := by
      exact add_le_add hexact hforce
    _ = ((((Fintype.card ι : ℝ) + 1) ^ 2 * (β : ℝ) *
          exactFlowPositionStabilityFactor β ε + (β : ℝ) / 2) *
        |ε| ^ 2) * euclideanNorm (q₁₀ - q₂₀) := by
      rw [hεsq]
      ring

/-- Relative-position displacement rate of one leapfrog step for arbitrary
paired initial phases. -/
noncomputable def leapfrogPhaseRelativeDisplacementRate
    (β : NNReal) (ε : ℝ) : ℝ :=
  |ε| + (β : ℝ) * ε ^ 2 / 2

theorem continuous_leapfrogPhaseRelativeDisplacementRate (β : NNReal) :
    Continuous (leapfrogPhaseRelativeDisplacementRate β) := by
  unfold leapfrogPhaseRelativeDisplacementRate
  fun_prop

@[simp]
theorem leapfrogPhaseRelativeDisplacementRate_zero (β : NNReal) :
    leapfrogPhaseRelativeDisplacementRate β 0 = 0 := by
  simp [leapfrogPhaseRelativeDisplacementRate]

/-- One arbitrary-paired-phase leapfrog position difference approximates the
corresponding exact position difference. The same quadratic scalar rate as
in the shared-momentum case now multiplies the full initial phase size. -/
theorem leapfrog_exactFlow_positionSub_error_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (hcurve₁ : IsHamiltonianCurve gradient q₁ p₁)
    (hcurve₂ : IsHamiltonianCurve gradient q₂ p₂)
    (hq₁ : q₁ 0 = q₁₀) (hq₂ : q₂ 0 = q₂₀)
    (hp₁ : p₁ 0 = p₁₀) (hp₂ : p₂ 0 = p₂₀) (ε : ℝ) :
    euclideanNorm
        (((leapfrog gradient ε (q₁₀, p₁₀)).1 -
            (leapfrog gradient ε (q₂₀, p₂₀)).1) -
          (q₁ ε - q₂ ε)) ≤
      leapfrogExactOneStepPhasePositionErrorRate (ι := ι) β ε *
        euclideanPhaseSize (q₁₀ - q₂₀, p₁₀ - p₂₀) := by
  let A := exactFlowPhaseStabilityFactor (ι := ι) β ε
  have hphase := hreg.euclideanPhaseSize_phaseSub_le_on_uIcc
    hcurve₁ hcurve₂ (t := ε)
  have hposition : ∀ s ∈ Set.uIcc (0 : ℝ) ε,
      euclideanNorm (q₁ s - q₂ s) ≤
        A * euclideanPhaseSize
          (q₁ 0 - q₂ 0, p₁ 0 - p₂ 0) := by
    intro s hs
    exact (euclideanNorm_fst_le_phaseSize _).trans (hphase s hs)
  have hexact :=
    hreg.euclideanNorm_positionSub_sub_initial_sub_time_smul_le
      hcurve₁ hcurve₂ (exactFlowPhaseStabilityFactor_pos
        (ι := ι) β ε).le hposition
  rw [hq₁, hq₂, hp₁, hp₂] at hexact
  have hgradient := hreg.euclideanNorm_gradient_sub_le q₁₀ q₂₀
  have hqphase : euclideanNorm (q₁₀ - q₂₀) ≤
      euclideanPhaseSize (q₁₀ - q₂₀, p₁₀ - p₂₀) :=
    by
      unfold euclideanPhaseSize
      exact le_add_of_nonneg_right (euclideanNorm_nonneg _)
  have hgradientPhase : euclideanNorm (gradient q₁₀ - gradient q₂₀) ≤
      (β : ℝ) * euclideanPhaseSize (q₁₀ - q₂₀, p₁₀ - p₂₀) :=
    hgradient.trans (mul_le_mul_of_nonneg_left hqphase β.coe_nonneg)
  have hhalf : 0 ≤ ε ^ 2 / 2 := by positivity
  have hdecomp :
      ((leapfrog gradient ε (q₁₀, p₁₀)).1 -
          (leapfrog gradient ε (q₂₀, p₂₀)).1) -
        (q₁ ε - q₂ ε) =
      -(((q₁ ε - q₂ ε) - (q₁₀ - q₂₀)) -
          ε • (p₁₀ - p₂₀)) -
        (ε ^ 2 / 2) • (gradient q₁₀ - gradient q₂₀) := by
    rw [leapfrog_position_sub]
    abel
  rw [hdecomp]
  apply (euclideanNorm_sub_le _ _).trans
  rw [euclideanNorm_neg, euclideanNorm_smul, abs_of_nonneg hhalf]
  unfold leapfrogExactOneStepPhasePositionErrorRate
  have hZ : 0 ≤ euclideanPhaseSize (q₁₀ - q₂₀, p₁₀ - p₂₀) :=
    euclideanPhaseSize_nonneg _
  have hεsq : ε ^ 2 = |ε| ^ 2 := (sq_abs ε).symm
  have hforce := mul_le_mul_of_nonneg_left hgradientPhase hhalf
  calc
    euclideanNorm
          (((q₁ ε - q₂ ε) - (q₁₀ - q₂₀)) -
            ε • (p₁₀ - p₂₀)) +
        ε ^ 2 / 2 * euclideanNorm (gradient q₁₀ - gradient q₂₀) ≤
      (((Fintype.card ι : ℝ) + 1) ^ 2 * (β : ℝ) *
          exactFlowPhaseStabilityFactor β ε * |ε| ^ 2) *
          euclideanPhaseSize (q₁₀ - q₂₀, p₁₀ - p₂₀) +
        ε ^ 2 / 2 * ((β : ℝ) *
          euclideanPhaseSize (q₁₀ - q₂₀, p₁₀ - p₂₀)) := by
      exact add_le_add hexact hforce
    _ = ((((Fintype.card ι : ℝ) + 1) ^ 2 * (β : ℝ) *
          exactFlowPhaseStabilityFactor β ε + (β : ℝ) / 2) *
        |ε| ^ 2) *
          euclideanPhaseSize (q₁₀ - q₂₀, p₁₀ - p₂₀) := by
      rw [hεsq]
      ring

/-- Compact-uniform paired force variation at one shared-momentum leapfrog
endpoint. This discharges the leapfrog endpoint force-modulus premise from
compact containment and small absolute endpoint displacement. -/
theorem RegularPotential.exists_uniform_leapfrog_forceVariation_bound
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ M ≥ 0,
      ∀ {q₁ q₂ : Position ι} {p : Momentum ι} {ε : ℝ},
        q₁ ∈ S → q₂ ∈ S →
        (leapfrog gradient ε (q₁, p)).1 ∈ S →
        (leapfrog gradient ε (q₂, p)).1 ∈ S →
        euclideanNorm ((leapfrog gradient ε (q₁, p)).1 - q₁) ≤ δ →
        euclideanNorm ((leapfrog gradient ε (q₂, p)).1 - q₂) ≤ δ →
        euclideanNorm
            ((gradient (leapfrog gradient ε (q₁, p)).1 -
                gradient (leapfrog gradient ε (q₂, p)).1) -
              (gradient q₁ - gradient q₂)) ≤
          ((Fintype.card ι : ℝ) + 1) *
              (η + M * ((β : ℝ) * ε ^ 2 / 2)) *
            euclideanNorm (q₁ - q₂) := by
  obtain ⟨δ, hδ, M, hM, hforce⟩ :=
    hreg.exists_uniform_relative_forceVariation_bound
      hScompact hSconvex hη
  refine ⟨δ, hδ, M, hM, ?_⟩
  intro q₁ q₂ p ε hq₁ hq₂ hlf₁ hlf₂ hdisp₁ hdisp₂
  have hgradient := hreg.euclideanNorm_gradient_sub_le q₁ q₂
  have hhalf : 0 ≤ ε ^ 2 / 2 := by positivity
  have hrelative : euclideanNorm
      (((leapfrog gradient ε (q₁, p)).1 -
          (leapfrog gradient ε (q₂, p)).1) - (q₁ - q₂)) ≤
        ((β : ℝ) * ε ^ 2 / 2) * euclideanNorm (q₁ - q₂) := by
    rw [leapfrog_sharedMomentum_position_sub]
    have hid :
        (q₁ - q₂ - (ε ^ 2 / 2) • (gradient q₁ - gradient q₂)) -
            (q₁ - q₂) =
          -(ε ^ 2 / 2) • (gradient q₁ - gradient q₂) := by
      funext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hid, euclideanNorm_smul, abs_neg, abs_of_nonneg hhalf]
    calc
      ε ^ 2 / 2 * euclideanNorm (gradient q₁ - gradient q₂) ≤
          ε ^ 2 / 2 * ((β : ℝ) * euclideanNorm (q₁ - q₂)) :=
        mul_le_mul_of_nonneg_left hgradient hhalf
      _ = ((β : ℝ) * ε ^ 2 / 2) * euclideanNorm (q₁ - q₂) := by ring
  apply hforce hq₂ hq₁ hlf₂ hlf₁
  · apply (dist_le_euclideanNorm_sub
      (leapfrog gradient ε (q₂, p)).1 q₂).trans
    exact hdisp₂
  · apply (dist_le_euclideanNorm_sub
      (leapfrog gradient ε (q₁, p)).1 q₁).trans
    exact hdisp₁
  · exact hrelative

/-- Compact-uniform paired force variation at one arbitrary-paired-phase
leapfrog endpoint. -/
theorem RegularPotential.exists_uniform_leapfrog_phaseForceVariation_bound
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ M ≥ 0,
      ∀ {q₁ q₂ : Position ι} {p₁ p₂ : Momentum ι} {ε : ℝ},
        q₁ ∈ S → q₂ ∈ S →
        (leapfrog gradient ε (q₁, p₁)).1 ∈ S →
        (leapfrog gradient ε (q₂, p₂)).1 ∈ S →
        euclideanNorm ((leapfrog gradient ε (q₁, p₁)).1 - q₁) ≤ δ →
        euclideanNorm ((leapfrog gradient ε (q₂, p₂)).1 - q₂) ≤ δ →
        euclideanNorm
            ((gradient (leapfrog gradient ε (q₁, p₁)).1 -
                gradient (leapfrog gradient ε (q₂, p₂)).1) -
              (gradient q₁ - gradient q₂)) ≤
          ((Fintype.card ι : ℝ) + 1) *
              (η + M * leapfrogPhaseRelativeDisplacementRate β ε) *
            euclideanPhaseSize (q₁ - q₂, p₁ - p₂) := by
  obtain ⟨δ, hδ, M, hM, _hMglobal, hforce⟩ :=
    hreg.exists_uniform_euclideanNorm_gradientSub_sub_gradientSub_bound
      hScompact hSconvex hη
  refine ⟨δ, hδ, M, hM, ?_⟩
  intro q₁ q₂ p₁ p₂ ε hq₁ hq₂ hlf₁ hlf₂ hdisp₁ hdisp₂
  let Z := euclideanPhaseSize (q₁ - q₂, p₁ - p₂)
  have hq : euclideanNorm (q₁ - q₂) ≤ Z := by
    dsimp [Z]
    unfold euclideanPhaseSize
    exact le_add_of_nonneg_right (euclideanNorm_nonneg _)
  have hp : euclideanNorm (p₁ - p₂) ≤ Z := by
    dsimp [Z]
    unfold euclideanPhaseSize
    exact le_add_of_nonneg_left (euclideanNorm_nonneg _)
  have hgradient := hreg.euclideanNorm_gradient_sub_le q₁ q₂
  have hhalf : 0 ≤ ε ^ 2 / 2 := by positivity
  have hrelative : euclideanNorm
      (((leapfrog gradient ε (q₁, p₁)).1 -
          (leapfrog gradient ε (q₂, p₂)).1) - (q₁ - q₂)) ≤
        leapfrogPhaseRelativeDisplacementRate β ε * Z := by
    rw [leapfrog_position_sub]
    have hid :
        (q₁ - q₂ + ε • (p₁ - p₂) -
            (ε ^ 2 / 2) • (gradient q₁ - gradient q₂)) - (q₁ - q₂) =
          ε • (p₁ - p₂) -
            (ε ^ 2 / 2) • (gradient q₁ - gradient q₂) := by abel
    rw [hid]
    apply (euclideanNorm_sub_le _ _).trans
    rw [euclideanNorm_smul, euclideanNorm_smul, abs_of_nonneg hhalf]
    have hpScaled := mul_le_mul_of_nonneg_left hp (abs_nonneg ε)
    have hgPhase := hgradient.trans
      (mul_le_mul_of_nonneg_left hq β.coe_nonneg)
    have hgScaled := mul_le_mul_of_nonneg_left hgPhase hhalf
    unfold leapfrogPhaseRelativeDisplacementRate
    nlinarith
  have hmain := hforce hq₂ hq₁ hlf₂ hlf₁
    ((dist_le_euclideanNorm_sub
      (leapfrog gradient ε (q₂, p₂)).1 q₂).trans hdisp₂)
    ((dist_le_euclideanNorm_sub
      (leapfrog gradient ε (q₁, p₁)).1 q₁).trans hdisp₁)
  apply hmain.trans
  have hMrelative := mul_le_mul_of_nonneg_left hrelative hM
  have hη : 0 ≤ η := hη.le
  calc
    ((Fintype.card ι : ℝ) + 1) *
        (η * euclideanNorm (q₁ - q₂) +
          M * euclideanNorm
            (((leapfrog gradient ε (q₁, p₁)).1 -
              (leapfrog gradient ε (q₂, p₂)).1) - (q₁ - q₂))) ≤
      ((Fintype.card ι : ℝ) + 1) *
        (η * Z + M * (leapfrogPhaseRelativeDisplacementRate β ε * Z)) := by
      gcongr
    _ = ((Fintype.card ι : ℝ) + 1) *
          (η + M * leapfrogPhaseRelativeDisplacementRate β ε) * Z := by ring

/-- One common compact force-variation rate dominating both the exact-curve
and leapfrog-endpoint estimates. -/
noncomputable def compactExactLeapfrogForceVariationRate
    (β : NNReal) (η M ε : ℝ) : ℝ :=
  ((Fintype.card ι : ℝ) + 1) *
    (η + M * (exactFlowRelativeDisplacementRate (ι := ι) β ε +
      (β : ℝ) * ε ^ 2 / 2))

theorem continuous_compactExactLeapfrogForceVariationRate
    (β : NNReal) (η M : ℝ) :
    Continuous
      (compactExactLeapfrogForceVariationRate (ι := ι) β η M) := by
  unfold compactExactLeapfrogForceVariationRate
  exact continuous_const.mul (continuous_const.add
    (continuous_const.mul
      ((continuous_exactFlowRelativeDisplacementRate
        (ι := ι) β).add
          ((continuous_const.mul (continuous_id.pow 2)).div_const 2))))

@[simp]
theorem compactExactLeapfrogForceVariationRate_zero
    (β : NNReal) (η M : ℝ) :
    compactExactLeapfrogForceVariationRate (ι := ι) β η M 0 =
      ((Fintype.card ι : ℝ) + 1) * η := by
  simp [compactExactLeapfrogForceVariationRate]

/-- The exact and leapfrog force estimates can be chosen with one common
compact displacement radius, Hessian bound, and scalar rate. -/
theorem RegularPotential.exists_common_exact_leapfrog_forceVariation_bound
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ M ≥ 0,
      ∀ {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι},
        IsHamiltonianCurve gradient q₁ p₁ →
        IsHamiltonianCurve gradient q₂ p₂ →
        p₁ 0 = p₂ 0 →
        ∀ {ε : ℝ},
          q₁ 0 ∈ S → q₂ 0 ∈ S →
          (∀ s ∈ Set.uIcc (0 : ℝ) ε, q₁ s ∈ S) →
          (∀ s ∈ Set.uIcc (0 : ℝ) ε, q₂ s ∈ S) →
          (∀ s ∈ Set.uIcc (0 : ℝ) ε,
            euclideanNorm (q₁ s - q₁ 0) ≤ δ) →
          (∀ s ∈ Set.uIcc (0 : ℝ) ε,
            euclideanNorm (q₂ s - q₂ 0) ≤ δ) →
          (leapfrog gradient ε (q₁ 0, p₁ 0)).1 ∈ S →
          (leapfrog gradient ε (q₂ 0, p₂ 0)).1 ∈ S →
          euclideanNorm
              ((leapfrog gradient ε (q₁ 0, p₁ 0)).1 - q₁ 0) ≤ δ →
          euclideanNorm
              ((leapfrog gradient ε (q₂ 0, p₂ 0)).1 - q₂ 0) ≤ δ →
          (∀ s ∈ Set.uIcc (0 : ℝ) ε,
            euclideanNorm
                ((gradient (q₁ s) - gradient (q₂ s)) -
                  (gradient (q₁ 0) - gradient (q₂ 0))) ≤
              compactExactLeapfrogForceVariationRate
                  (ι := ι) β η M ε *
                euclideanNorm (q₁ 0 - q₂ 0)) ∧
          euclideanNorm
              ((gradient (leapfrog gradient ε (q₁ 0, p₁ 0)).1 -
                  gradient (leapfrog gradient ε (q₂ 0, p₂ 0)).1) -
                (gradient (q₁ 0) - gradient (q₂ 0))) ≤
            compactExactLeapfrogForceVariationRate
                (ι := ι) β η M ε *
              euclideanNorm (q₁ 0 - q₂ 0) := by
  obtain ⟨δE, hδE, ME, hME, hExact⟩ :=
    hreg.exists_uniform_exact_forceVariation_bound hScompact hSconvex hη
  obtain ⟨δL, hδL, ML, hML, hLeapfrog⟩ :=
    hreg.exists_uniform_leapfrog_forceVariation_bound hScompact hSconvex hη
  let δ := min δE δL
  let M := max ME ML
  have hδ : 0 < δ := lt_min hδE hδL
  have hM : 0 ≤ M := hME.trans (le_max_left _ _)
  refine ⟨δ, hδ, M, hM, ?_⟩
  intro q₁ q₂ p₁ p₂ hcurve₁ hcurve₂ hp ε hq₁₀ hq₂₀
    hq₁S hq₂S hq₁disp hq₂disp hlf₁S hlf₂S hlf₁disp hlf₂disp
  have hq₁dispE : ∀ s ∈ Set.uIcc (0 : ℝ) ε,
      euclideanNorm (q₁ s - q₁ 0) ≤ δE := by
    intro s hs
    exact (hq₁disp s hs).trans (min_le_left _ _)
  have hq₂dispE : ∀ s ∈ Set.uIcc (0 : ℝ) ε,
      euclideanNorm (q₂ s - q₂ 0) ≤ δE := by
    intro s hs
    exact (hq₂disp s hs).trans (min_le_left _ _)
  have hExact' := hExact hcurve₁ hcurve₂ hp hq₁₀ hq₂₀
    hq₁S hq₂S hq₁dispE hq₂dispE
  have hlf₂S' : (leapfrog gradient ε (q₂ 0, p₁ 0)).1 ∈ S := by
    simpa only [hp] using hlf₂S
  have hlf₂disp' : euclideanNorm
      ((leapfrog gradient ε (q₂ 0, p₁ 0)).1 - q₂ 0) ≤ δ := by
    simpa only [hp] using hlf₂disp
  have hLeapfrog' := hLeapfrog hq₁₀ hq₂₀ hlf₁S hlf₂S'
    (hlf₁disp.trans (min_le_right _ _))
    (hlf₂disp'.trans (min_le_right _ _))
  have hD : 0 ≤ (Fintype.card ι : ℝ) + 1 := by positivity
  have hRexact : 0 ≤ exactFlowRelativeDisplacementRate (ι := ι) β ε := by
    unfold exactFlowRelativeDisplacementRate
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (sq_nonneg _) β.coe_nonneg)
        (exactFlowPositionStabilityFactor_pos (ι := ι) β ε).le)
      (sq_nonneg _)
  have hRlf : 0 ≤ (β : ℝ) * ε ^ 2 / 2 := by positivity
  have hMEle : ME ≤ M := le_max_left _ _
  have hMLle : ML ≤ M := le_max_right _ _
  have hQ : 0 ≤ euclideanNorm (q₁ 0 - q₂ 0) := euclideanNorm_nonneg _
  constructor
  · intro s hs
    apply (hExact' s hs).trans
    unfold compactExactLeapfrogForceVariationRate
    gcongr
    nlinarith [mul_le_mul_of_nonneg_right hMEle hRexact,
      mul_nonneg hM hRlf]
  · rw [← hp]
    apply hLeapfrog'.trans
    unfold compactExactLeapfrogForceVariationRate
    gcongr
    nlinarith [mul_le_mul_of_nonneg_right hMLle hRlf,
      mul_nonneg hM hRexact]

/-- One compact force-variation rate for arbitrary paired exact phases and
their arbitrary-paired leapfrog endpoints. -/
noncomputable def compactExactLeapfrogPhaseForceVariationRate
    (β : NNReal) (η M ε : ℝ) : ℝ :=
  ((Fintype.card ι : ℝ) + 1) *
    (η + M * (exactFlowPhaseRelativeDisplacementRate (ι := ι) β ε +
      leapfrogPhaseRelativeDisplacementRate β ε))

theorem continuous_compactExactLeapfrogPhaseForceVariationRate
    (β : NNReal) (η M : ℝ) :
    Continuous
      (compactExactLeapfrogPhaseForceVariationRate (ι := ι) β η M) := by
  unfold compactExactLeapfrogPhaseForceVariationRate
  exact continuous_const.mul (continuous_const.add
    (continuous_const.mul
      ((continuous_exactFlowPhaseRelativeDisplacementRate
        (ι := ι) β).add
          (continuous_leapfrogPhaseRelativeDisplacementRate β))))

@[simp]
theorem compactExactLeapfrogPhaseForceVariationRate_zero
    (β : NNReal) (η M : ℝ) :
    compactExactLeapfrogPhaseForceVariationRate (ι := ι) β η M 0 =
      ((Fintype.card ι : ℝ) + 1) * η := by
  simp [compactExactLeapfrogPhaseForceVariationRate]

/-- The exact and leapfrog force estimates for arbitrary paired phases can
be chosen with one compact displacement radius, Hessian bound, and rate. -/
theorem RegularPotential.exists_common_exact_leapfrog_phaseForceVariation_bound
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ M ≥ 0,
      ∀ {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι},
        IsHamiltonianCurve gradient q₁ p₁ →
        IsHamiltonianCurve gradient q₂ p₂ →
        ∀ {ε : ℝ},
          q₁ 0 ∈ S → q₂ 0 ∈ S →
          (∀ s ∈ Set.uIcc (0 : ℝ) ε, q₁ s ∈ S) →
          (∀ s ∈ Set.uIcc (0 : ℝ) ε, q₂ s ∈ S) →
          (∀ s ∈ Set.uIcc (0 : ℝ) ε,
            euclideanNorm (q₁ s - q₁ 0) ≤ δ) →
          (∀ s ∈ Set.uIcc (0 : ℝ) ε,
            euclideanNorm (q₂ s - q₂ 0) ≤ δ) →
          (leapfrog gradient ε (q₁ 0, p₁ 0)).1 ∈ S →
          (leapfrog gradient ε (q₂ 0, p₂ 0)).1 ∈ S →
          euclideanNorm
              ((leapfrog gradient ε (q₁ 0, p₁ 0)).1 - q₁ 0) ≤ δ →
          euclideanNorm
              ((leapfrog gradient ε (q₂ 0, p₂ 0)).1 - q₂ 0) ≤ δ →
          (∀ s ∈ Set.uIcc (0 : ℝ) ε,
            euclideanNorm
                ((gradient (q₁ s) - gradient (q₂ s)) -
                  (gradient (q₁ 0) - gradient (q₂ 0))) ≤
              compactExactLeapfrogPhaseForceVariationRate
                  (ι := ι) β η M ε *
                euclideanPhaseSize
                  (q₁ 0 - q₂ 0, p₁ 0 - p₂ 0)) ∧
          euclideanNorm
              ((gradient (leapfrog gradient ε (q₁ 0, p₁ 0)).1 -
                  gradient (leapfrog gradient ε (q₂ 0, p₂ 0)).1) -
                (gradient (q₁ 0) - gradient (q₂ 0))) ≤
            compactExactLeapfrogPhaseForceVariationRate
                (ι := ι) β η M ε *
              euclideanPhaseSize
                (q₁ 0 - q₂ 0, p₁ 0 - p₂ 0) := by
  obtain ⟨δE, hδE, ME, hME, hExact⟩ :=
    hreg.exists_uniform_exact_phaseForceVariation_bound
      hScompact hSconvex hη
  obtain ⟨δL, hδL, ML, hML, hLeapfrog⟩ :=
    hreg.exists_uniform_leapfrog_phaseForceVariation_bound
      hScompact hSconvex hη
  let δ := min δE δL
  let M := max ME ML
  have hδ : 0 < δ := lt_min hδE hδL
  have hM : 0 ≤ M := hME.trans (le_max_left _ _)
  refine ⟨δ, hδ, M, hM, ?_⟩
  intro q₁ q₂ p₁ p₂ hcurve₁ hcurve₂ ε hq₁₀ hq₂₀
    hq₁S hq₂S hq₁disp hq₂disp hlf₁S hlf₂S hlf₁disp hlf₂disp
  have hExact' := hExact hcurve₁ hcurve₂ hq₁₀ hq₂₀ hq₁S hq₂S
    (fun s hs ↦ (hq₁disp s hs).trans (min_le_left _ _))
    (fun s hs ↦ (hq₂disp s hs).trans (min_le_left _ _))
  have hLeapfrog' := hLeapfrog hq₁₀ hq₂₀ hlf₁S hlf₂S
    (hlf₁disp.trans (min_le_right _ _))
    (hlf₂disp.trans (min_le_right _ _))
  have hD : 0 ≤ (Fintype.card ι : ℝ) + 1 := by positivity
  have hRE : 0 ≤ exactFlowPhaseRelativeDisplacementRate
      (ι := ι) β ε := by
    unfold exactFlowPhaseRelativeDisplacementRate
    exact add_nonneg (abs_nonneg ε)
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (sq_nonneg _) β.coe_nonneg)
          (exactFlowPhaseStabilityFactor_pos (ι := ι) β ε).le)
        (sq_nonneg _))
  have hRL : 0 ≤ leapfrogPhaseRelativeDisplacementRate β ε := by
    unfold leapfrogPhaseRelativeDisplacementRate
    positivity
  have hMEle : ME ≤ M := le_max_left _ _
  have hMLle : ML ≤ M := le_max_right _ _
  have hZ : 0 ≤ euclideanPhaseSize
      (q₁ 0 - q₂ 0, p₁ 0 - p₂ 0) := euclideanPhaseSize_nonneg _
  constructor
  · intro s hs
    apply (hExact' s hs).trans
    unfold compactExactLeapfrogPhaseForceVariationRate
    gcongr
    nlinarith [mul_le_mul_of_nonneg_right hMEle hRE,
      mul_nonneg hM hRL]
  · apply hLeapfrog'.trans
    unfold compactExactLeapfrogPhaseForceVariationRate
    gcongr
    nlinarith [mul_le_mul_of_nonneg_right hMLle hRL,
      mul_nonneg hM hRE]

/-- Relative momentum-consistency rate obtained from a paired force-variation
allowance `ω`. -/
noncomputable def leapfrogExactOneStepRelativeMomentumErrorRate
    (ω ε : ℝ) : ℝ :=
  ((Fintype.card ι : ℝ) + 1 + 1 / 2) * |ε| * ω

/-- Automatic compact one-step paired phase-error rate after inserting the
common `C²` force modulus. -/
noncomputable def compactOneStepRelativePhaseErrorRate
    (β : NNReal) (η M ε : ℝ) : ℝ :=
  leapfrogExactOneStepRelativePositionErrorRate (ι := ι) β ε +
    leapfrogExactOneStepRelativeMomentumErrorRate (ι := ι)
      (compactExactLeapfrogForceVariationRate (ι := ι) β η M ε) ε

theorem continuous_compactOneStepRelativePhaseErrorRate
    (β : NNReal) (η M : ℝ) :
    Continuous (compactOneStepRelativePhaseErrorRate (ι := ι) β η M) := by
  unfold compactOneStepRelativePhaseErrorRate
  unfold leapfrogExactOneStepRelativeMomentumErrorRate
  exact (continuous_leapfrogExactOneStepRelativePositionErrorRate
    (ι := ι) β).add
      ((continuous_const.mul continuous_abs).mul
        (continuous_compactExactLeapfrogForceVariationRate
          (ι := ι) β η M))

@[simp]
theorem compactOneStepRelativePhaseErrorRate_zero
    (β : NNReal) (η M : ℝ) :
    compactOneStepRelativePhaseErrorRate (ι := ι) β η M 0 = 0 := by
  simp [compactOneStepRelativePhaseErrorRate,
    leapfrogExactOneStepRelativeMomentumErrorRate]

/-- Automatic compact one-step truncation rate for arbitrary paired initial
phases. -/
noncomputable def compactOneStepPhaseErrorRate
    (β : NNReal) (η M ε : ℝ) : ℝ :=
  leapfrogExactOneStepPhasePositionErrorRate (ι := ι) β ε +
    leapfrogExactOneStepRelativeMomentumErrorRate (ι := ι)
      (compactExactLeapfrogPhaseForceVariationRate
        (ι := ι) β η M ε) ε

theorem continuous_compactOneStepPhaseErrorRate
    (β : NNReal) (η M : ℝ) :
    Continuous (compactOneStepPhaseErrorRate (ι := ι) β η M) := by
  unfold compactOneStepPhaseErrorRate
  unfold leapfrogExactOneStepPhasePositionErrorRate
  unfold leapfrogExactOneStepRelativeMomentumErrorRate
  exact ((((continuous_const.mul continuous_const).mul
      (continuous_exactFlowPhaseStabilityFactor β)).add
        continuous_const).mul (continuous_abs.pow 2)).add
    ((continuous_const.mul continuous_abs).mul
      (continuous_compactExactLeapfrogPhaseForceVariationRate
        (ι := ι) β η M))

@[simp]
theorem compactOneStepPhaseErrorRate_zero
    (β : NNReal) (η M : ℝ) :
    compactOneStepPhaseErrorRate (ι := ι) β η M 0 = 0 := by
  simp [compactOneStepPhaseErrorRate,
    leapfrogExactOneStepPhasePositionErrorRate,
    leapfrogExactOneStepRelativeMomentumErrorRate]

/-- Paired exact-force quadrature cancellation and leapfrog's trapezoidal
force update reduce one-step relative momentum consistency to two explicit
force-variation bounds. -/
theorem leapfrog_sharedMomentum_exactFlow_momentumSub_error_le
    {gradient : Position ι → Position ι}
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (hcurve₁ : IsHamiltonianCurve gradient q₁ p₁)
    (hcurve₂ : IsHamiltonianCurve gradient q₂ p₂)
    (hq₁ : q₁ 0 = q₁₀) (hq₂ : q₂ 0 = q₂₀)
    (hp₁ : p₁ 0 = p) (hp₂ : p₂ 0 = p)
    {ω : ℝ} (ε : ℝ)
    (hforceExact : ∀ s ∈ Set.uIcc (0 : ℝ) ε,
      euclideanNorm
          ((gradient (q₁ s) - gradient (q₂ s)) -
            (gradient q₁₀ - gradient q₂₀)) ≤
        ω * euclideanNorm (q₁₀ - q₂₀))
    (hforceLeapfrog :
      euclideanNorm
          ((gradient (leapfrog gradient ε (q₁₀, p)).1 -
              gradient (leapfrog gradient ε (q₂₀, p)).1) -
            (gradient q₁₀ - gradient q₂₀)) ≤
        ω * euclideanNorm (q₁₀ - q₂₀)) :
    euclideanNorm
        (((leapfrog gradient ε (q₁₀, p)).2 -
            (leapfrog gradient ε (q₂₀, p)).2) -
          (p₁ ε - p₂ ε)) ≤
      leapfrogExactOneStepRelativeMomentumErrorRate (ι := ι) ω ε *
        euclideanNorm (q₁₀ - q₂₀) := by
  let dg0 : Position ι := gradient q₁₀ - gradient q₂₀
  let dgLF : Position ι :=
    gradient (leapfrog gradient ε (q₁₀, p)).1 -
      gradient (leapfrog gradient ε (q₂₀, p)).1
  have hp : p₁ 0 = p₂ 0 := hp₁.trans hp₂.symm
  have hexact := euclideanNorm_momentumSub_add_initialForce_le
    hcurve₁ hcurve₂ hp (t := ε) (ω := ω) (by
      intro s hs
      simpa only [hq₁, hq₂] using hforceExact s hs)
  rw [hq₁, hq₂] at hexact
  have hLFidentity :
      ((leapfrog gradient ε (q₁₀, p)).2 -
          (leapfrog gradient ε (q₂₀, p)).2) + ε • dg0 =
        -(ε / 2) • (dgLF - dg0) := by
    rw [leapfrog_momentum_sub]
    funext i
    simp only [dg0, dgLF, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  have hhalf : 0 ≤ |ε| / 2 := by positivity
  have hLF : euclideanNorm
      (((leapfrog gradient ε (q₁₀, p)).2 -
          (leapfrog gradient ε (q₂₀, p)).2) + ε • dg0) ≤
        (|ε| / 2) * ω * euclideanNorm (q₁₀ - q₂₀) := by
    rw [hLFidentity, euclideanNorm_smul, abs_neg, abs_div,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    change |ε| / 2 * euclideanNorm (dgLF - dg0) ≤ _
    exact (mul_le_mul_of_nonneg_left hforceLeapfrog hhalf).trans_eq (by ring)
  have hdecomp :
      ((leapfrog gradient ε (q₁₀, p)).2 -
          (leapfrog gradient ε (q₂₀, p)).2) - (p₁ ε - p₂ ε) =
        (((leapfrog gradient ε (q₁₀, p)).2 -
            (leapfrog gradient ε (q₂₀, p)).2) + ε • dg0) -
          ((p₁ ε - p₂ ε) + ε • dg0) := by abel
  rw [hdecomp]
  apply (euclideanNorm_sub_le _ _).trans
  unfold leapfrogExactOneStepRelativeMomentumErrorRate
  calc
    euclideanNorm
          ((leapfrog gradient ε (q₁₀, p)).2 -
            (leapfrog gradient ε (q₂₀, p)).2 + ε • dg0) +
        euclideanNorm (p₁ ε - p₂ ε + ε • dg0) ≤
      (|ε| / 2) * ω * euclideanNorm (q₁₀ - q₂₀) +
        ((Fintype.card ι : ℝ) + 1) * |ε| * ω *
          euclideanNorm (q₁₀ - q₂₀) := add_le_add hLF hexact
    _ = (((Fintype.card ι : ℝ) + 1 + 1 / 2) * |ε| * ω) *
        euclideanNorm (q₁₀ - q₂₀) := by ring

/-- Arbitrary-paired-phase momentum consistency. The leading initial
relative momentum cancels on both the exact and leapfrog sides, leaving the
same force-quadrature remainder as in the shared-momentum estimate. -/
theorem leapfrog_exactFlow_momentumSub_error_le
    {gradient : Position ι → Position ι}
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (hcurve₁ : IsHamiltonianCurve gradient q₁ p₁)
    (hcurve₂ : IsHamiltonianCurve gradient q₂ p₂)
    (hq₁ : q₁ 0 = q₁₀) (hq₂ : q₂ 0 = q₂₀)
    (hp₁ : p₁ 0 = p₁₀) (hp₂ : p₂ 0 = p₂₀)
    {ω : ℝ} (ε : ℝ)
    (hforceExact : ∀ s ∈ Set.uIcc (0 : ℝ) ε,
      euclideanNorm
          ((gradient (q₁ s) - gradient (q₂ s)) -
            (gradient q₁₀ - gradient q₂₀)) ≤
        ω * euclideanPhaseSize (q₁₀ - q₂₀, p₁₀ - p₂₀))
    (hforceLeapfrog :
      euclideanNorm
          ((gradient (leapfrog gradient ε (q₁₀, p₁₀)).1 -
              gradient (leapfrog gradient ε (q₂₀, p₂₀)).1) -
            (gradient q₁₀ - gradient q₂₀)) ≤
        ω * euclideanPhaseSize (q₁₀ - q₂₀, p₁₀ - p₂₀)) :
    euclideanNorm
        (((leapfrog gradient ε (q₁₀, p₁₀)).2 -
            (leapfrog gradient ε (q₂₀, p₂₀)).2) -
          (p₁ ε - p₂ ε)) ≤
      leapfrogExactOneStepRelativeMomentumErrorRate (ι := ι) ω ε *
        euclideanPhaseSize (q₁₀ - q₂₀, p₁₀ - p₂₀) := by
  let dp0 : Momentum ι := p₁₀ - p₂₀
  let dg0 : Position ι := gradient q₁₀ - gradient q₂₀
  let dgLF : Position ι :=
    gradient (leapfrog gradient ε (q₁₀, p₁₀)).1 -
      gradient (leapfrog gradient ε (q₂₀, p₂₀)).1
  have hexact :=
    euclideanNorm_momentumSub_sub_initial_add_initialForce_le
      hcurve₁ hcurve₂ (t := ε) (ω := ω) (by
        intro s hs
        simpa only [hq₁, hq₂, hp₁, hp₂] using hforceExact s hs)
  rw [hq₁, hq₂, hp₁, hp₂] at hexact
  have hLFidentity :
      (((leapfrog gradient ε (q₁₀, p₁₀)).2 -
          (leapfrog gradient ε (q₂₀, p₂₀)).2) - dp0) + ε • dg0 =
        -(ε / 2) • (dgLF - dg0) := by
    rw [leapfrog_momentum_sub]
    funext i
    simp only [dp0, dg0, dgLF, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  have hhalf : 0 ≤ |ε| / 2 := by positivity
  have hLF : euclideanNorm
      ((((leapfrog gradient ε (q₁₀, p₁₀)).2 -
          (leapfrog gradient ε (q₂₀, p₂₀)).2) - dp0) + ε • dg0) ≤
        (|ε| / 2) * ω *
          euclideanPhaseSize (q₁₀ - q₂₀, p₁₀ - p₂₀) := by
    rw [hLFidentity, euclideanNorm_smul, abs_neg, abs_div,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    change |ε| / 2 * euclideanNorm (dgLF - dg0) ≤ _
    exact (mul_le_mul_of_nonneg_left hforceLeapfrog hhalf).trans_eq (by ring)
  have hdecomp :
      ((leapfrog gradient ε (q₁₀, p₁₀)).2 -
          (leapfrog gradient ε (q₂₀, p₂₀)).2) - (p₁ ε - p₂ ε) =
        ((((leapfrog gradient ε (q₁₀, p₁₀)).2 -
            (leapfrog gradient ε (q₂₀, p₂₀)).2) - dp0) + ε • dg0) -
          (((p₁ ε - p₂ ε) - dp0) + ε • dg0) := by
    dsimp [dp0]
    abel
  rw [hdecomp]
  apply (euclideanNorm_sub_le _ _).trans
  unfold leapfrogExactOneStepRelativeMomentumErrorRate
  calc
    euclideanNorm
          (((leapfrog gradient ε (q₁₀, p₁₀)).2 -
            (leapfrog gradient ε (q₂₀, p₂₀)).2 - dp0) + ε • dg0) +
        euclideanNorm (((p₁ ε - p₂ ε) - dp0) + ε • dg0) ≤
      (|ε| / 2) * ω *
          euclideanPhaseSize (q₁₀ - q₂₀, p₁₀ - p₂₀) +
        ((Fintype.card ι : ℝ) + 1) * |ε| * ω *
          euclideanPhaseSize (q₁₀ - q₂₀, p₁₀ - p₂₀) :=
      add_le_add hLF hexact
    _ = (((Fintype.card ι : ℝ) + 1 + 1 / 2) * |ε| * ω) *
        euclideanPhaseSize (q₁₀ - q₂₀, p₁₀ - p₂₀) := by ring

/-- Complete arbitrary-paired-phase one-step consistency estimate. This is
the local truncation theorem that remains applicable after shifting exact
trajectories to any leapfrog grid point. -/
theorem leapfrog_exactFlow_phaseSub_error_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (hcurve₁ : IsHamiltonianCurve gradient q₁ p₁)
    (hcurve₂ : IsHamiltonianCurve gradient q₂ p₂)
    (hq₁ : q₁ 0 = q₁₀) (hq₂ : q₂ 0 = q₂₀)
    (hp₁ : p₁ 0 = p₁₀) (hp₂ : p₂ 0 = p₂₀)
    {ω : ℝ} (ε : ℝ)
    (hforceExact : ∀ s ∈ Set.uIcc (0 : ℝ) ε,
      euclideanNorm
          ((gradient (q₁ s) - gradient (q₂ s)) -
            (gradient q₁₀ - gradient q₂₀)) ≤
        ω * euclideanPhaseSize (q₁₀ - q₂₀, p₁₀ - p₂₀))
    (hforceLeapfrog :
      euclideanNorm
          ((gradient (leapfrog gradient ε (q₁₀, p₁₀)).1 -
              gradient (leapfrog gradient ε (q₂₀, p₂₀)).1) -
            (gradient q₁₀ - gradient q₂₀)) ≤
        ω * euclideanPhaseSize (q₁₀ - q₂₀, p₁₀ - p₂₀)) :
    euclideanPhaseSize
        (((leapfrog gradient ε (q₁₀, p₁₀)).1 -
              (leapfrog gradient ε (q₂₀, p₂₀)).1) -
            (q₁ ε - q₂ ε),
          ((leapfrog gradient ε (q₁₀, p₁₀)).2 -
              (leapfrog gradient ε (q₂₀, p₂₀)).2) -
            (p₁ ε - p₂ ε)) ≤
      (leapfrogExactOneStepPhasePositionErrorRate (ι := ι) β ε +
          leapfrogExactOneStepRelativeMomentumErrorRate (ι := ι) ω ε) *
        euclideanPhaseSize (q₁₀ - q₂₀, p₁₀ - p₂₀) := by
  have hq := leapfrog_exactFlow_positionSub_error_le
    hreg hcurve₁ hcurve₂ hq₁ hq₂ hp₁ hp₂ ε
  have hp := leapfrog_exactFlow_momentumSub_error_le
    hcurve₁ hcurve₂ hq₁ hq₂ hp₁ hp₂ ε hforceExact hforceLeapfrog
  unfold euclideanPhaseSize
  calc
    euclideanNorm
          ((leapfrog gradient ε (q₁₀, p₁₀)).1 -
            (leapfrog gradient ε (q₂₀, p₂₀)).1 - (q₁ ε - q₂ ε)) +
        euclideanNorm
          ((leapfrog gradient ε (q₁₀, p₁₀)).2 -
            (leapfrog gradient ε (q₂₀, p₂₀)).2 - (p₁ ε - p₂ ε)) ≤
      leapfrogExactOneStepPhasePositionErrorRate (ι := ι) β ε *
          (euclideanNorm (q₁₀ - q₂₀) + euclideanNorm (p₁₀ - p₂₀)) +
        leapfrogExactOneStepRelativeMomentumErrorRate (ι := ι) ω ε *
          (euclideanNorm (q₁₀ - q₂₀) + euclideanNorm (p₁₀ - p₂₀)) :=
      add_le_add hq hp
    _ = (leapfrogExactOneStepPhasePositionErrorRate (ι := ι) β ε +
          leapfrogExactOneStepRelativeMomentumErrorRate (ι := ι) ω ε) *
        (euclideanNorm (q₁₀ - q₂₀) + euclideanNorm (p₁₀ - p₂₀)) := by
      ring

/-- One-step absolute phase consistency of leapfrog against one exact
Hamiltonian trajectory, under uniform force and force-variation bounds. -/
theorem leapfrog_exactFlow_absolutePhaseError_le
    {gradient : Position ι → Position ι}
    {q : ℝ → Position ι} {p : ℝ → Momentum ι}
    (hcurve : IsHamiltonianCurve gradient q p)
    {G ω : ℝ} (ε : ℝ)
    (hgradient : ∀ s ∈ Set.uIcc (0 : ℝ) ε,
      euclideanNorm (gradient (q s)) ≤ G)
    (hforceExact : ∀ s ∈ Set.uIcc (0 : ℝ) ε,
      euclideanNorm (gradient (q s) - gradient (q 0)) ≤ ω)
    (hforceLeapfrog : euclideanNorm
      (gradient (leapfrog gradient ε (q 0, p 0)).1 -
        gradient (q 0)) ≤ ω) :
    euclideanPhaseSize
        ((leapfrog gradient ε (q 0, p 0)).1 - q ε,
          (leapfrog gradient ε (q 0, p 0)).2 - p ε) ≤
      (((Fintype.card ι : ℝ) + 1) ^ 2 + 1 / 2) * G * |ε| ^ 2 +
        ((Fintype.card ι : ℝ) + 1 + 1 / 2) * |ε| * ω := by
  let g0 : Position ι := gradient (q 0)
  let gLF : Position ι :=
    gradient (leapfrog gradient ε (q 0, p 0)).1
  have hpositionExact :=
    euclideanNorm_position_sub_initial_sub_time_smul_le_of_gradient_le
      hcurve hgradient
  have hG0 : euclideanNorm g0 ≤ G := by
    exact hgradient 0 Set.left_mem_uIcc
  have hpositionIdentity :
      (leapfrog gradient ε (q 0, p 0)).1 - q ε =
        -((q ε - q 0) - ε • p 0) -
          (ε ^ 2 / 2) • g0 := by
    funext i
    simp only [leapfrog, drift, halfKick, g0, Pi.sub_apply, Pi.add_apply,
      Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hposition : euclideanNorm
      ((leapfrog gradient ε (q 0, p 0)).1 - q ε) ≤
      (((Fintype.card ι : ℝ) + 1) ^ 2 + 1 / 2) * G * |ε| ^ 2 := by
    rw [hpositionIdentity]
    apply (euclideanNorm_sub_le _ _).trans
    rw [euclideanNorm_neg, euclideanNorm_smul]
    have hhalf : |ε ^ 2 / 2| = |ε| ^ 2 / 2 := by
      rw [abs_div, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hhalf]
    have hscaled := mul_le_mul_of_nonneg_left hG0 (by positivity : 0 ≤ |ε| ^ 2 / 2)
    apply (add_le_add hpositionExact hscaled).trans_eq
    ring
  have hmomentumExact :=
    euclideanNorm_momentum_sub_initial_add_initialForce_le
      hcurve hforceExact
  have hmomentumIdentity :
      ((leapfrog gradient ε (q 0, p 0)).2 - p 0) + ε • g0 =
        -(ε / 2) • (gLF - g0) := by
    funext i
    simp only [leapfrog, drift, halfKick, g0, gLF, Pi.sub_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hmomentumLF : euclideanNorm
      (((leapfrog gradient ε (q 0, p 0)).2 - p 0) + ε • g0) ≤
        (|ε| / 2) * ω := by
    rw [hmomentumIdentity, euclideanNorm_smul, abs_neg, abs_div,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left hforceLeapfrog (by positivity)
  have hmomentumDecomp :
      (leapfrog gradient ε (q 0, p 0)).2 - p ε =
        (((leapfrog gradient ε (q 0, p 0)).2 - p 0) + ε • g0) -
          ((p ε - p 0) + ε • g0) := by abel
  have hmomentum : euclideanNorm
      ((leapfrog gradient ε (q 0, p 0)).2 - p ε) ≤
      ((Fintype.card ι : ℝ) + 1 + 1 / 2) * |ε| * ω := by
    rw [hmomentumDecomp]
    apply (euclideanNorm_sub_le _ _).trans
    apply (add_le_add hmomentumLF hmomentumExact).trans_eq
    ring
  unfold euclideanPhaseSize
  exact add_le_add hposition hmomentum

/-- Uniform force bound obtained from a Euclidean phase-size bound. -/
noncomputable def exactFlowAbsoluteForceBound
    (β : NNReal) (gradient : Position ι → Position ι) (B : ℝ) : ℝ :=
  (β : ℝ) * B + euclideanNorm (gradient 0)

/-- Common exact/leapfrog force-variation allowance over one bounded step. -/
noncomputable def leapfrogExactAbsoluteForceVariationRate
    (β : NNReal) (gradient : Position ι → Position ι)
    (B ε : ℝ) : ℝ :=
  (β : ℝ) *
    (((Fintype.card ι : ℝ) + 1) * B + B +
      exactFlowAbsoluteForceBound (ι := ι) β gradient B / 2) * |ε|

/-- Explicit quadratic absolute local phase-error rate on a bounded exact
phase family. -/
noncomputable def leapfrogExactOneStepAbsolutePhaseErrorRate
    (β : NNReal) (gradient : Position ι → Position ι)
    (B ε : ℝ) : ℝ :=
  (((Fintype.card ι : ℝ) + 1) ^ 2 + 1 / 2) *
      exactFlowAbsoluteForceBound (ι := ι) β gradient B * |ε| ^ 2 +
    ((Fintype.card ι : ℝ) + 1 + 1 / 2) * |ε| *
      leapfrogExactAbsoluteForceVariationRate (ι := ι) β gradient B ε

/-- Step-independent coefficient of the quadratic absolute local error. -/
noncomputable def leapfrogExactAbsolutePhaseErrorCoefficient
    (β : NNReal) (gradient : Position ι → Position ι) (B : ℝ) : ℝ :=
  (((Fintype.card ι : ℝ) + 1) ^ 2 + 1 / 2) *
      exactFlowAbsoluteForceBound (ι := ι) β gradient B +
    ((Fintype.card ι : ℝ) + 1 + 1 / 2) * (β : ℝ) *
      (((Fintype.card ι : ℝ) + 1) * B + B +
        exactFlowAbsoluteForceBound (ι := ι) β gradient B / 2)

theorem leapfrogExactOneStepAbsolutePhaseErrorRate_eq
    (β : NNReal) (gradient : Position ι → Position ι) (B ε : ℝ) :
    leapfrogExactOneStepAbsolutePhaseErrorRate
        (ι := ι) β gradient B ε =
      |ε| ^ 2 * leapfrogExactAbsolutePhaseErrorCoefficient
        (ι := ι) β gradient B := by
  unfold leapfrogExactOneStepAbsolutePhaseErrorRate
  unfold leapfrogExactAbsoluteForceVariationRate
  unfold leapfrogExactAbsolutePhaseErrorCoefficient
  ring

theorem leapfrogExactAbsolutePhaseErrorCoefficient_nonneg
    (β : NNReal) (gradient : Position ι → Position ι)
    {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ leapfrogExactAbsolutePhaseErrorCoefficient
      (ι := ι) β gradient B := by
  have hG : 0 ≤ exactFlowAbsoluteForceBound (ι := ι) β gradient B := by
    unfold exactFlowAbsoluteForceBound
    exact add_nonneg (mul_nonneg β.coe_nonneg hB)
      (euclideanNorm_nonneg _)
  unfold leapfrogExactAbsolutePhaseErrorCoefficient
  positivity

/-- Uniform fixed-horizon absolute error allowance as a function of step
size. -/
noncomputable def leapfrogExactAbsoluteFixedHorizonErrorRate
    (β : NNReal) (gradient : Position ι → Position ι)
    (B T ε : ℝ) : ℝ :=
  T *
      (|ε| * leapfrogExactAbsolutePhaseErrorCoefficient
        (ι := ι) β gradient B) *
    Real.exp (leapfrogNormStabilityRate β * T)

theorem continuous_leapfrogExactAbsoluteFixedHorizonErrorRate
    (β : NNReal) (gradient : Position ι → Position ι) (B T : ℝ) :
    Continuous
      (leapfrogExactAbsoluteFixedHorizonErrorRate
        (ι := ι) β gradient B T) := by
  unfold leapfrogExactAbsoluteFixedHorizonErrorRate
  fun_prop

@[simp]
theorem leapfrogExactAbsoluteFixedHorizonErrorRate_zero
    (β : NNReal) (gradient : Position ι → Position ι) (B T : ℝ) :
    leapfrogExactAbsoluteFixedHorizonErrorRate
      (ι := ι) β gradient B T 0 = 0 := by
  simp [leapfrogExactAbsoluteFixedHorizonErrorRate]

theorem exists_pos_forall_leapfrogExactAbsoluteFixedHorizonErrorRate_lt
    (β : NNReal) (gradient : Position ι → Position ι) (B T : ℝ)
    {buffer : ℝ} (hbuffer : 0 < buffer) :
    ∃ εbar > 0, ∀ ε, |ε| ≤ εbar →
      leapfrogExactAbsoluteFixedHorizonErrorRate
        (ι := ι) β gradient B T ε < buffer :=
  exists_pos_forall_abs_le_of_continuousAt_zero
    (continuous_leapfrogExactAbsoluteFixedHorizonErrorRate
      (ι := ι) β gradient B T).continuousAt
    (leapfrogExactAbsoluteFixedHorizonErrorRate_zero
      (ι := ι) β gradient B T) hbuffer

/-- Automatic absolute one-step consistency under a uniform exact phase-size
bound. This supplies the individual numerical-versus-exact estimate needed
for compact-buffer containment. -/
theorem RegularPotential.leapfrog_exactFlow_absolutePhaseError_le_of_phaseSize_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q : ℝ → Position ι} {p : ℝ → Momentum ι}
    (hcurve : IsHamiltonianCurve gradient q p)
    {B : ℝ} (hB : 0 ≤ B) {ε : ℝ} (hε : |ε| ≤ 1)
    (hphase : ∀ s ∈ Set.uIcc (0 : ℝ) ε,
      euclideanPhaseSize (q s, p s) ≤ B) :
    euclideanPhaseSize
        ((leapfrog gradient ε (q 0, p 0)).1 - q ε,
          (leapfrog gradient ε (q 0, p 0)).2 - p ε) ≤
      leapfrogExactOneStepAbsolutePhaseErrorRate
        (ι := ι) β gradient B ε := by
  let D : ℝ := (Fintype.card ι : ℝ) + 1
  let G : ℝ := exactFlowAbsoluteForceBound (ι := ι) β gradient B
  let ω : ℝ := leapfrogExactAbsoluteForceVariationRate
    (ι := ι) β gradient B ε
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hG : 0 ≤ G := by
    dsimp [G, exactFlowAbsoluteForceBound]
    exact add_nonneg (mul_nonneg β.coe_nonneg hB)
      (euclideanNorm_nonneg _)
  have hqbound : ∀ s ∈ Set.uIcc (0 : ℝ) ε,
      euclideanNorm (q s) ≤ B := by
    intro s hs
    exact (euclideanNorm_fst_le_phaseSize _).trans (hphase s hs)
  have hp0 : euclideanNorm (p 0) ≤ B := by
    have := hphase 0 Set.left_mem_uIcc
    unfold euclideanPhaseSize at this
    linarith [euclideanNorm_nonneg (q 0)]
  have hgradient : ∀ s ∈ Set.uIcc (0 : ℝ) ε,
      euclideanNorm (gradient (q s)) ≤ G := by
    intro s hs
    apply (hreg.euclideanNorm_gradient_le (q s)).trans
    dsimp [G, exactFlowAbsoluteForceBound]
    gcongr
    exact hqbound s hs
  have hexactDisp : ∀ s ∈ Set.uIcc (0 : ℝ) ε,
      euclideanNorm (q s - q 0) ≤ D * B * |ε| := by
    intro s hs
    have hsub : Set.uIcc (0 : ℝ) s ⊆ Set.uIcc (0 : ℝ) ε :=
      Set.uIcc_subset_uIcc_left hs
    have hdisp := euclideanNorm_position_sub_initial_le_of_phaseSize_le
      hcurve (fun u hu ↦ hphase u (hsub hu))
    have hst : |s| ≤ |ε| := by
      simpa only [sub_zero] using Set.abs_sub_left_of_mem_uIcc hs
    dsimp [D]
    apply hdisp.trans
    gcongr
  have hforceExact : ∀ s ∈ Set.uIcc (0 : ℝ) ε,
      euclideanNorm (gradient (q s) - gradient (q 0)) ≤ ω := by
    intro s hs
    have hlip := hreg.euclideanNorm_gradient_sub_le (q s) (q 0)
    apply hlip.trans
    dsimp [ω, leapfrogExactAbsoluteForceVariationRate]
    have hnonneg : 0 ≤ B + G / 2 := by positivity
    have hsum : D * B ≤ D * B + B + G / 2 := by linarith
    have hscaled := mul_le_mul_of_nonneg_left (hexactDisp s hs) β.coe_nonneg
    calc
      (β : ℝ) * euclideanNorm (q s - q 0) ≤
          (β : ℝ) * (D * B * |ε|) := hscaled
      _ ≤ (β : ℝ) * ((D * B + B + G / 2) * |ε|) := by
        apply mul_le_mul_of_nonneg_left _ β.coe_nonneg
        exact mul_le_mul_of_nonneg_right hsum (abs_nonneg ε)
      _ = (β : ℝ) * (D * B + B + G / 2) * |ε| := by ring
  have hlfDisp : euclideanNorm
      ((leapfrog gradient ε (q 0, p 0)).1 - q 0) ≤
      |ε| * (B + G / 2) := by
    have hid : (leapfrog gradient ε (q 0, p 0)).1 - q 0 =
        ε • p 0 - (ε ^ 2 / 2) • gradient (q 0) := by
      funext i
      simp only [leapfrog, drift, halfKick, Pi.sub_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      ring
    rw [hid]
    apply (euclideanNorm_sub_le _ _).trans
    rw [euclideanNorm_smul, euclideanNorm_smul]
    have hgrad0 := hgradient 0 Set.left_mem_uIcc
    have hpScaled := mul_le_mul_of_nonneg_left hp0 (abs_nonneg ε)
    have hhalf : |ε ^ 2 / 2| = |ε| ^ 2 / 2 := by
      rw [abs_div, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hhalf]
    have hgScaled := mul_le_mul_of_nonneg_left hgrad0
      (by positivity : 0 ≤ |ε| ^ 2 / 2)
    have heSq : |ε| ^ 2 ≤ |ε| := by
      nlinarith [abs_nonneg ε]
    have hgTime : |ε| ^ 2 / 2 * G ≤ |ε| / 2 * G := by
      gcongr
    calc
      |ε| * euclideanNorm (p 0) +
          |ε| ^ 2 / 2 * euclideanNorm (gradient (q 0)) ≤
        |ε| * B + |ε| ^ 2 / 2 * G := add_le_add hpScaled hgScaled
      _ ≤ |ε| * B + |ε| / 2 * G := add_le_add le_rfl hgTime
      _ = |ε| * (B + G / 2) := by ring
  have hforceLeapfrog : euclideanNorm
      (gradient (leapfrog gradient ε (q 0, p 0)).1 - gradient (q 0)) ≤ ω := by
    have hlip := hreg.euclideanNorm_gradient_sub_le
      (leapfrog gradient ε (q 0, p 0)).1 (q 0)
    apply hlip.trans
    dsimp [ω, leapfrogExactAbsoluteForceVariationRate]
    have hscaled := mul_le_mul_of_nonneg_left hlfDisp β.coe_nonneg
    calc
      (β : ℝ) * euclideanNorm
          ((leapfrog gradient ε (q 0, p 0)).1 - q 0) ≤
        (β : ℝ) * (|ε| * (B + G / 2)) := hscaled
      _ ≤ (β : ℝ) * ((D * B + B + G / 2) * |ε|) := by
        have hDB : 0 ≤ D * B := mul_nonneg hD hB
        have hsum : B + G / 2 ≤ D * B + B + G / 2 := by linarith
        apply mul_le_mul_of_nonneg_left _ β.coe_nonneg
        rw [mul_comm |ε| (B + G / 2)]
        exact mul_le_mul_of_nonneg_right
          hsum (abs_nonneg ε)
      _ = (β : ℝ) * (D * B + B + G / 2) * |ε| := by ring
  have hraw := leapfrog_exactFlow_absolutePhaseError_le
    hcurve ε hgradient hforceExact hforceLeapfrog
  simpa only [leapfrogExactOneStepAbsolutePhaseErrorRate, G, ω] using hraw

/-- Complete one-step paired phase-consistency estimate. The position
component follows from global gradient Lipschitzness; the momentum component
is reduced to compact-uniform paired force variation. -/
theorem leapfrog_sharedMomentum_exactFlow_phaseSub_error_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (hcurve₁ : IsHamiltonianCurve gradient q₁ p₁)
    (hcurve₂ : IsHamiltonianCurve gradient q₂ p₂)
    (hq₁ : q₁ 0 = q₁₀) (hq₂ : q₂ 0 = q₂₀)
    (hp₁ : p₁ 0 = p) (hp₂ : p₂ 0 = p)
    {ω : ℝ} (ε : ℝ)
    (hforceExact : ∀ s ∈ Set.uIcc (0 : ℝ) ε,
      euclideanNorm
          ((gradient (q₁ s) - gradient (q₂ s)) -
            (gradient q₁₀ - gradient q₂₀)) ≤
        ω * euclideanNorm (q₁₀ - q₂₀))
    (hforceLeapfrog :
      euclideanNorm
          ((gradient (leapfrog gradient ε (q₁₀, p)).1 -
              gradient (leapfrog gradient ε (q₂₀, p)).1) -
            (gradient q₁₀ - gradient q₂₀)) ≤
        ω * euclideanNorm (q₁₀ - q₂₀)) :
    euclideanPhaseSize
        (((leapfrog gradient ε (q₁₀, p)).1 -
              (leapfrog gradient ε (q₂₀, p)).1) -
            (q₁ ε - q₂ ε),
          ((leapfrog gradient ε (q₁₀, p)).2 -
              (leapfrog gradient ε (q₂₀, p)).2) -
            (p₁ ε - p₂ ε)) ≤
      (leapfrogExactOneStepRelativePositionErrorRate (ι := ι) β ε +
          leapfrogExactOneStepRelativeMomentumErrorRate (ι := ι) ω ε) *
        euclideanNorm (q₁₀ - q₂₀) := by
  have hq := leapfrog_sharedMomentum_exactFlow_positionSub_error_le
    hreg hcurve₁ hcurve₂ hq₁ hq₂ hp₁ hp₂ ε
  have hp' := leapfrog_sharedMomentum_exactFlow_momentumSub_error_le
    hcurve₁ hcurve₂ hq₁ hq₂ hp₁ hp₂ ε hforceExact hforceLeapfrog
  unfold euclideanPhaseSize
  linarith

/-- Under compact containment and small exact/leapfrog displacement, the
complete paired one-step phase error follows automatically from `C²`
regularity, with no externally supplied force modulus. -/
theorem RegularPotential.exists_compact_oneStepRelativePhaseError_bound
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ M ≥ 0,
      ∀ {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι},
        IsHamiltonianCurve gradient q₁ p₁ →
        IsHamiltonianCurve gradient q₂ p₂ →
        p₁ 0 = p₂ 0 →
        ∀ {ε : ℝ},
          q₁ 0 ∈ S → q₂ 0 ∈ S →
          (∀ s ∈ Set.uIcc (0 : ℝ) ε, q₁ s ∈ S) →
          (∀ s ∈ Set.uIcc (0 : ℝ) ε, q₂ s ∈ S) →
          (∀ s ∈ Set.uIcc (0 : ℝ) ε,
            euclideanNorm (q₁ s - q₁ 0) ≤ δ) →
          (∀ s ∈ Set.uIcc (0 : ℝ) ε,
            euclideanNorm (q₂ s - q₂ 0) ≤ δ) →
          (leapfrog gradient ε (q₁ 0, p₁ 0)).1 ∈ S →
          (leapfrog gradient ε (q₂ 0, p₂ 0)).1 ∈ S →
          euclideanNorm
              ((leapfrog gradient ε (q₁ 0, p₁ 0)).1 - q₁ 0) ≤ δ →
          euclideanNorm
              ((leapfrog gradient ε (q₂ 0, p₂ 0)).1 - q₂ 0) ≤ δ →
          euclideanPhaseSize
              (((leapfrog gradient ε (q₁ 0, p₁ 0)).1 -
                    (leapfrog gradient ε (q₂ 0, p₂ 0)).1) -
                  (q₁ ε - q₂ ε),
                ((leapfrog gradient ε (q₁ 0, p₁ 0)).2 -
                    (leapfrog gradient ε (q₂ 0, p₂ 0)).2) -
                  (p₁ ε - p₂ ε)) ≤
            compactOneStepRelativePhaseErrorRate
                (ι := ι) β η M ε *
              euclideanNorm (q₁ 0 - q₂ 0) := by
  obtain ⟨δ, hδ, M, hM, hforce⟩ :=
    hreg.exists_common_exact_leapfrog_forceVariation_bound
      hScompact hSconvex hη
  refine ⟨δ, hδ, M, hM, ?_⟩
  intro q₁ q₂ p₁ p₂ hcurve₁ hcurve₂ hp ε hq₁₀ hq₂₀
    hq₁S hq₂S hq₁disp hq₂disp hlf₁S hlf₂S hlf₁disp hlf₂disp
  obtain ⟨hforceExact, hforceLeapfrog⟩ := hforce
    hcurve₁ hcurve₂ hp hq₁₀ hq₂₀ hq₁S hq₂S hq₁disp hq₂disp
      hlf₁S hlf₂S hlf₁disp hlf₂disp
  have hp₂ : p₂ 0 = p₁ 0 := hp.symm
  have hphase := leapfrog_sharedMomentum_exactFlow_phaseSub_error_le
    hreg hcurve₁ hcurve₂ rfl rfl rfl hp₂ ε hforceExact
      (by simpa only [hp] using hforceLeapfrog)
  simpa only [compactOneStepRelativePhaseErrorRate, hp] using hphase

/-- Under compact containment and small exact/leapfrog displacement, one-step
paired local truncation is controlled for arbitrary initial relative phase.
Unlike the shared-momentum specialization, this theorem can be applied after
every exact-flow time shift. -/
theorem RegularPotential.exists_compact_oneStepPhaseError_bound
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ M ≥ 0,
      ∀ {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι},
        IsHamiltonianCurve gradient q₁ p₁ →
        IsHamiltonianCurve gradient q₂ p₂ →
        ∀ {ε : ℝ},
          q₁ 0 ∈ S → q₂ 0 ∈ S →
          (∀ s ∈ Set.uIcc (0 : ℝ) ε, q₁ s ∈ S) →
          (∀ s ∈ Set.uIcc (0 : ℝ) ε, q₂ s ∈ S) →
          (∀ s ∈ Set.uIcc (0 : ℝ) ε,
            euclideanNorm (q₁ s - q₁ 0) ≤ δ) →
          (∀ s ∈ Set.uIcc (0 : ℝ) ε,
            euclideanNorm (q₂ s - q₂ 0) ≤ δ) →
          (leapfrog gradient ε (q₁ 0, p₁ 0)).1 ∈ S →
          (leapfrog gradient ε (q₂ 0, p₂ 0)).1 ∈ S →
          euclideanNorm
              ((leapfrog gradient ε (q₁ 0, p₁ 0)).1 - q₁ 0) ≤ δ →
          euclideanNorm
              ((leapfrog gradient ε (q₂ 0, p₂ 0)).1 - q₂ 0) ≤ δ →
          euclideanPhaseSize
              (((leapfrog gradient ε (q₁ 0, p₁ 0)).1 -
                    (leapfrog gradient ε (q₂ 0, p₂ 0)).1) -
                  (q₁ ε - q₂ ε),
                ((leapfrog gradient ε (q₁ 0, p₁ 0)).2 -
                    (leapfrog gradient ε (q₂ 0, p₂ 0)).2) -
                  (p₁ ε - p₂ ε)) ≤
            compactOneStepPhaseErrorRate (ι := ι) β η M ε *
              euclideanPhaseSize
                (q₁ 0 - q₂ 0, p₁ 0 - p₂ 0) := by
  obtain ⟨δ, hδ, M, hM, hforce⟩ :=
    hreg.exists_common_exact_leapfrog_phaseForceVariation_bound
      hScompact hSconvex hη
  refine ⟨δ, hδ, M, hM, ?_⟩
  intro q₁ q₂ p₁ p₂ hcurve₁ hcurve₂ ε hq₁₀ hq₂₀
    hq₁S hq₂S hq₁disp hq₂disp hlf₁S hlf₂S hlf₁disp hlf₂disp
  obtain ⟨hforceExact, hforceLeapfrog⟩ := hforce
    hcurve₁ hcurve₂ hq₁₀ hq₂₀ hq₁S hq₂S hq₁disp hq₂disp
      hlf₁S hlf₂S hlf₁disp hlf₂disp
  have hphase := leapfrog_exactFlow_phaseSub_error_le
    hreg hcurve₁ hcurve₂ rfl rfl rfl rfl ε hforceExact hforceLeapfrog
  simpa only [compactOneStepPhaseErrorRate] using hphase

/-- Exact Hamiltonian phase sampled on the signed leapfrog time grid. -/
def exactGridPhase
    (q : ℝ → Position ι) (p : ℝ → Momentum ι)
    (ε : ℝ) (k : ℕ) : PhaseSpace ι :=
  (q ((k : ℝ) * ε), p ((k : ℝ) * ε))

omit [Fintype ι] in
@[simp]
theorem exactGridPhase_zero
    (q : ℝ → Position ι) (p : ℝ → Momentum ι) (ε : ℝ) :
    exactGridPhase q p ε 0 = (q 0, p 0) := by
  simp [exactGridPhase]

omit [Fintype ι] in
theorem exactGridPhase_succ
    (q : ℝ → Position ι) (p : ℝ → Momentum ι) (ε : ℝ) (k : ℕ) :
    exactGridPhase q p ε (k + 1) =
      (q ((k : ℝ) * ε + ε), p ((k : ℝ) * ε + ε)) := by
  simp only [exactGridPhase, Nat.cast_add, Nat.cast_one]
  congr 2 <;> ring

/-- Time-shifted form of arbitrary-paired-phase compact local truncation.
This packages the exact theorem in the coordinates used at a leapfrog grid
point `τ`; no equality of the momenta at `τ` is required. -/
theorem RegularPotential.exists_compact_timeShift_oneStepPhaseError_bound
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ M ≥ 0,
      ∀ {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι},
        IsHamiltonianCurve gradient q₁ p₁ →
        IsHamiltonianCurve gradient q₂ p₂ →
        ∀ {τ ε : ℝ},
          q₁ τ ∈ S → q₂ τ ∈ S →
          (∀ s ∈ Set.uIcc (0 : ℝ) ε, q₁ (τ + s) ∈ S) →
          (∀ s ∈ Set.uIcc (0 : ℝ) ε, q₂ (τ + s) ∈ S) →
          (∀ s ∈ Set.uIcc (0 : ℝ) ε,
            euclideanNorm (q₁ (τ + s) - q₁ τ) ≤ δ) →
          (∀ s ∈ Set.uIcc (0 : ℝ) ε,
            euclideanNorm (q₂ (τ + s) - q₂ τ) ≤ δ) →
          (leapfrog gradient ε (q₁ τ, p₁ τ)).1 ∈ S →
          (leapfrog gradient ε (q₂ τ, p₂ τ)).1 ∈ S →
          euclideanNorm
              ((leapfrog gradient ε (q₁ τ, p₁ τ)).1 - q₁ τ) ≤ δ →
          euclideanNorm
              ((leapfrog gradient ε (q₂ τ, p₂ τ)).1 - q₂ τ) ≤ δ →
          pairedPhaseError
              (leapfrog gradient ε (q₁ τ, p₁ τ))
              (leapfrog gradient ε (q₂ τ, p₂ τ))
              (q₁ (τ + ε), p₁ (τ + ε))
              (q₂ (τ + ε), p₂ (τ + ε)) ≤
            compactOneStepPhaseErrorRate (ι := ι) β η M ε *
              euclideanPhaseSize
                (q₁ τ - q₂ τ, p₁ τ - p₂ τ) := by
  obtain ⟨δ, hδ, M, hM, hlocal⟩ :=
    hreg.exists_compact_oneStepPhaseError_bound hScompact hSconvex hη
  refine ⟨δ, hδ, M, hM, ?_⟩
  intro q₁ q₂ p₁ p₂ hcurve₁ hcurve₂ τ ε hq₁τ hq₂τ
    hq₁S hq₂S hq₁disp hq₂disp hlf₁S hlf₂S hlf₁disp hlf₂disp
  let qs₁ := timeShiftPosition q₁ τ
  let qs₂ := timeShiftPosition q₂ τ
  let ps₁ := timeShiftMomentum p₁ τ
  let ps₂ := timeShiftMomentum p₂ τ
  have hs₁ : IsHamiltonianCurve gradient qs₁ ps₁ := hcurve₁.timeShift τ
  have hs₂ : IsHamiltonianCurve gradient qs₂ ps₂ := hcurve₂.timeShift τ
  have hq₁τ' : qs₁ 0 ∈ S := by
    simpa [qs₁, timeShiftPosition] using hq₁τ
  have hq₂τ' : qs₂ 0 ∈ S := by
    simpa [qs₂, timeShiftPosition] using hq₂τ
  have hq₁S' : ∀ s ∈ Set.uIcc (0 : ℝ) ε, qs₁ s ∈ S := by
    simpa [qs₁, timeShiftPosition, add_comm] using hq₁S
  have hq₂S' : ∀ s ∈ Set.uIcc (0 : ℝ) ε, qs₂ s ∈ S := by
    simpa [qs₂, timeShiftPosition, add_comm] using hq₂S
  have hq₁disp' : ∀ s ∈ Set.uIcc (0 : ℝ) ε,
      euclideanNorm (qs₁ s - qs₁ 0) ≤ δ := by
    simpa [qs₁, timeShiftPosition, add_comm] using hq₁disp
  have hq₂disp' : ∀ s ∈ Set.uIcc (0 : ℝ) ε,
      euclideanNorm (qs₂ s - qs₂ 0) ≤ δ := by
    simpa [qs₂, timeShiftPosition, add_comm] using hq₂disp
  have hlf₁S' : (leapfrog gradient ε (qs₁ 0, ps₁ 0)).1 ∈ S := by
    simpa [qs₁, ps₁, timeShiftPosition, timeShiftMomentum] using hlf₁S
  have hlf₂S' : (leapfrog gradient ε (qs₂ 0, ps₂ 0)).1 ∈ S := by
    simpa [qs₂, ps₂, timeShiftPosition, timeShiftMomentum] using hlf₂S
  have hlf₁disp' : euclideanNorm
      ((leapfrog gradient ε (qs₁ 0, ps₁ 0)).1 - qs₁ 0) ≤ δ := by
    simpa [qs₁, ps₁, timeShiftPosition, timeShiftMomentum] using hlf₁disp
  have hlf₂disp' : euclideanNorm
      ((leapfrog gradient ε (qs₂ 0, ps₂ 0)).1 - qs₂ 0) ≤ δ := by
    simpa [qs₂, ps₂, timeShiftPosition, timeShiftMomentum] using hlf₂disp
  have h := hlocal hs₁ hs₂ hq₁τ' hq₂τ' hq₁S' hq₂S'
    hq₁disp' hq₂disp' hlf₁S' hlf₂S' hlf₁disp' hlf₂disp'
  simpa only [pairedPhaseError, qs₁, qs₂, ps₁, ps₂,
    timeShiftPosition, timeShiftMomentum, zero_add, add_zero, add_comm] using h

/-- Grid-indexed specialization of shifted compact local truncation for an
actual pair of exact Hamiltonian reference trajectories. -/
theorem RegularPotential.exists_compact_exactGrid_oneStepPhaseError_bound
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ M ≥ 0,
      ∀ {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι},
        IsHamiltonianCurve gradient q₁ p₁ →
        IsHamiltonianCurve gradient q₂ p₂ →
        ∀ {ε : ℝ} {k : ℕ},
          (exactGridPhase q₁ p₁ ε k).1 ∈ S →
          (exactGridPhase q₂ p₂ ε k).1 ∈ S →
          (∀ s ∈ Set.uIcc (0 : ℝ) ε,
            q₁ ((k : ℝ) * ε + s) ∈ S) →
          (∀ s ∈ Set.uIcc (0 : ℝ) ε,
            q₂ ((k : ℝ) * ε + s) ∈ S) →
          (∀ s ∈ Set.uIcc (0 : ℝ) ε,
            euclideanNorm
              (q₁ ((k : ℝ) * ε + s) - q₁ ((k : ℝ) * ε)) ≤ δ) →
          (∀ s ∈ Set.uIcc (0 : ℝ) ε,
            euclideanNorm
              (q₂ ((k : ℝ) * ε + s) - q₂ ((k : ℝ) * ε)) ≤ δ) →
          (leapfrog gradient ε (exactGridPhase q₁ p₁ ε k)).1 ∈ S →
          (leapfrog gradient ε (exactGridPhase q₂ p₂ ε k)).1 ∈ S →
          euclideanNorm
              ((leapfrog gradient ε (exactGridPhase q₁ p₁ ε k)).1 -
                (exactGridPhase q₁ p₁ ε k).1) ≤ δ →
          euclideanNorm
              ((leapfrog gradient ε (exactGridPhase q₂ p₂ ε k)).1 -
                (exactGridPhase q₂ p₂ ε k).1) ≤ δ →
          pairedPhaseError
              (leapfrog gradient ε (exactGridPhase q₁ p₁ ε k))
              (leapfrog gradient ε (exactGridPhase q₂ p₂ ε k))
              (exactGridPhase q₁ p₁ ε (k + 1))
              (exactGridPhase q₂ p₂ ε (k + 1)) ≤
            compactOneStepPhaseErrorRate (ι := ι) β η M ε *
              euclideanPhaseSize
                ((exactGridPhase q₁ p₁ ε k).1 -
                    (exactGridPhase q₂ p₂ ε k).1,
                  (exactGridPhase q₁ p₁ ε k).2 -
                    (exactGridPhase q₂ p₂ ε k).2) := by
  obtain ⟨δ, hδ, M, hM, hshift⟩ :=
    hreg.exists_compact_timeShift_oneStepPhaseError_bound
      hScompact hSconvex hη
  refine ⟨δ, hδ, M, hM, ?_⟩
  intro q₁ q₂ p₁ p₂ hcurve₁ hcurve₂ ε k hq₁ hq₂
    hq₁S hq₂S hq₁disp hq₂disp hlf₁S hlf₂S hlf₁disp hlf₂disp
  have h := hshift hcurve₁ hcurve₂ hq₁ hq₂ hq₁S hq₂S
    hq₁disp hq₂disp hlf₁S hlf₂S hlf₁disp hlf₂disp
  simp only [exactGridPhase_succ]
  simpa only [exactGridPhase] using h

/-- Absolute local consistency at every exact Hamiltonian grid phase, under
an indexed uniform exact phase-size bound. -/
theorem RegularPotential.exactGrid_absolutePhaseError_local_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q : ℝ → Position ι} {p : ℝ → Momentum ι}
    (hcurve : IsHamiltonianCurve gradient q p)
    {B : ℝ} (hB : 0 ≤ B) {ε : ℝ} (hε : |ε| ≤ 1)
    (k : ℕ)
    (hphase : ∀ s ∈ Set.uIcc (0 : ℝ) ε,
      euclideanPhaseSize
        (q ((k : ℝ) * ε + s), p ((k : ℝ) * ε + s)) ≤ B) :
    absolutePhaseError
        (leapfrog gradient ε (exactGridPhase q p ε k))
        (exactGridPhase q p ε (k + 1)) ≤
      |ε| ^ 2 * leapfrogExactAbsolutePhaseErrorCoefficient
        (ι := ι) β gradient B := by
  let qs := timeShiftPosition q ((k : ℝ) * ε)
  let ps := timeShiftMomentum p ((k : ℝ) * ε)
  have hcurveShift : IsHamiltonianCurve gradient qs ps :=
    hcurve.timeShift ((k : ℝ) * ε)
  have hphaseShift : ∀ s ∈ Set.uIcc (0 : ℝ) ε,
      euclideanPhaseSize (qs s, ps s) ≤ B := by
    intro s hs
    simpa only [qs, ps, timeShiftPosition, timeShiftMomentum, add_comm] using
      hphase s hs
  have hlocal :=
    hreg.leapfrog_exactFlow_absolutePhaseError_le_of_phaseSize_le
      hcurveShift hB hε hphaseShift
  rw [leapfrogExactOneStepAbsolutePhaseErrorRate_eq] at hlocal
  simp only [absolutePhaseError, exactGridPhase_succ]
  simpa only [exactGridPhase, qs, ps, timeShiftPosition, timeShiftMomentum,
    zero_add, add_zero, add_comm] using hlocal

/-- The uniform exact-flow growth theorem supplies the indexed phase bound
needed by every local grid step before a finite horizon. -/
theorem RegularPotential.exactGrid_phaseSize_le_uniform_of_horizon
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q : ℝ → Position ι} {p : ℝ → Momentum ι}
    (hcurve : IsHamiltonianCurve gradient q p)
    {M T ε : ℝ} {n : ℕ} (hM : 0 ≤ M)
    (hinitial : euclideanPhaseSize (q 0, p 0) ≤ M)
    (horizon : (n : ℝ) * |ε| ≤ T) :
    ∀ k < n, ∀ s ∈ Set.uIcc (0 : ℝ) ε,
      euclideanPhaseSize
          (q ((k : ℝ) * ε + s), p ((k : ℝ) * ε + s)) ≤
        exactFlowUniformEuclideanPhaseBound
          (ι := ι) β gradient M T := by
  intro k hk s hs
  have hsabs : |s| ≤ |ε| := by
    simpa only [sub_zero] using Set.abs_sub_left_of_mem_uIcc hs
  have hkcast : (k + 1 : ℕ) ≤ n := Nat.succ_le_iff.mpr hk
  have hkcastReal : ((k + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkcast
  have htime : |(k : ℝ) * ε + s| ≤ T := by
    calc
      |(k : ℝ) * ε + s| ≤ |(k : ℝ) * ε| + |s| := abs_add_le _ _
      _ = (k : ℝ) * |ε| + |s| := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
      _ ≤ (k : ℝ) * |ε| + |ε| := by gcongr
      _ = ((k + 1 : ℕ) : ℝ) * |ε| := by
        rw [Nat.cast_add, Nat.cast_one]
        ring
      _ ≤ (n : ℝ) * |ε| :=
        mul_le_mul_of_nonneg_right hkcastReal (abs_nonneg ε)
      _ ≤ T := horizon
  exact hreg.euclideanPhaseSize_le_uniform
    hcurve hM hinitial htime

/-- A uniform phase-size bound controls the displacement across any shifted
exact grid segment by an explicit quantity linear in the step size. -/
theorem exactGrid_segment_positionDisplacement_le
    {gradient : Position ι → Position ι}
    {q : ℝ → Position ι} {p : ℝ → Momentum ι}
    (hcurve : IsHamiltonianCurve gradient q p) {B ε : ℝ} (hB : 0 ≤ B) (k : ℕ)
    (hphase : ∀ s ∈ Set.uIcc (0 : ℝ) ε,
      euclideanPhaseSize
        (q ((k : ℝ) * ε + s), p ((k : ℝ) * ε + s)) ≤ B) :
    ∀ s ∈ Set.uIcc (0 : ℝ) ε,
      euclideanNorm
          (q ((k : ℝ) * ε + s) - q ((k : ℝ) * ε)) ≤
        ((Fintype.card ι : ℝ) + 1) * B * |ε| := by
  intro s hs
  let qs := timeShiftPosition q ((k : ℝ) * ε)
  let ps := timeShiftMomentum p ((k : ℝ) * ε)
  have hcurveShift : IsHamiltonianCurve gradient qs ps :=
    hcurve.timeShift ((k : ℝ) * ε)
  have hphaseShift : ∀ u ∈ Set.uIcc (0 : ℝ) s,
      euclideanPhaseSize (qs u, ps u) ≤ B := by
    intro u hu
    have hus : u ∈ Set.uIcc (0 : ℝ) ε :=
      Set.uIcc_subset_uIcc Set.left_mem_uIcc hs hu
    simpa only [qs, ps, timeShiftPosition, timeShiftMomentum, add_comm] using
      hphase u hus
  have hdisp := euclideanNorm_position_sub_initial_le_of_phaseSize_le
    hcurveShift hphaseShift
  have hsabs : |s| ≤ |ε| := by
    simpa only [sub_zero] using Set.abs_sub_left_of_mem_uIcc hs
  simpa only [qs, timeShiftPosition, zero_add, add_zero, add_comm] using
    hdisp.trans (mul_le_mul_of_nonneg_left hsabs (mul_nonneg (by positivity) hB))

omit [Fintype ι] in
theorem leapfrog_position_sub_initial
    (gradient : Position ι → Position ι) (ε : ℝ) (z : PhaseSpace ι) :
    (leapfrog gradient ε z).1 - z.1 =
      ε • z.2 - (ε ^ 2 / 2) • gradient z.1 := by
  funext i
  simp [leapfrog, drift, halfKick, Pi.smul_apply, smul_eq_mul]
  ring

/-- A bounded phase has an explicitly small leapfrog position displacement.
This is the endpoint-radius estimate needed by compact local truncation. -/
theorem RegularPotential.leapfrog_positionDisplacement_le_of_phaseSize_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {B ε : ℝ} (hε : |ε| ≤ 1) (z : PhaseSpace ι)
    (hphase : euclideanPhaseSize z ≤ B) :
    euclideanNorm ((leapfrog gradient ε z).1 - z.1) ≤
      |ε| * (B + ((β : ℝ) * B + euclideanNorm (gradient 0)) / 2) := by
  have hq : euclideanNorm z.1 ≤ B :=
    (euclideanNorm_fst_le_phaseSize z).trans hphase
  have hp : euclideanNorm z.2 ≤ B := by
    unfold euclideanPhaseSize at hphase
    exact (le_add_of_nonneg_left (euclideanNorm_nonneg z.1)).trans hphase
  have hg : euclideanNorm (gradient z.1) ≤
      (β : ℝ) * B + euclideanNorm (gradient 0) := by
    exact (hreg.euclideanNorm_gradient_le z.1).trans (by gcongr)
  rw [leapfrog_position_sub_initial]
  apply (euclideanNorm_sub_le _ _).trans
  rw [euclideanNorm_smul, euclideanNorm_smul, abs_div]
  norm_num
  have he2 : ε ^ 2 / 2 ≤ |ε| / 2 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg ε]
  calc
    |ε| * euclideanNorm z.2 + ε ^ 2 / 2 *
        euclideanNorm (gradient z.1) ≤
      |ε| * B + |ε| / 2 *
        ((β : ℝ) * B + euclideanNorm (gradient 0)) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hp (abs_nonneg ε)
          · exact (mul_le_mul_of_nonneg_right he2
              (euclideanNorm_nonneg _)).trans
              (mul_le_mul_of_nonneg_left hg (div_nonneg (abs_nonneg ε) (by norm_num)))
    _ = |ε| * (B + ((β : ℝ) * B +
        euclideanNorm (gradient 0)) / 2) := by ring

/-- One positive step threshold simultaneously controls two nonnegative
linear-in-`|ε|` error budgets and enforces `|ε| ≤ 1`. -/
theorem exists_pos_forall_abs_le_and_two_mul_le
    {a b δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hδ : 0 < δ) :
    ∃ εbar > 0, ∀ ε : ℝ, |ε| ≤ εbar →
      |ε| ≤ 1 ∧ |ε| * a ≤ δ ∧ |ε| * b ≤ δ := by
  let εbar := min 1 (min (δ / (a + 1)) (δ / (b + 1)))
  have ha1 : 0 < a + 1 := by linarith
  have hb1 : 0 < b + 1 := by linarith
  have hεbar : 0 < εbar := by
    dsimp [εbar]
    exact lt_min (by norm_num)
      (lt_min (div_pos hδ ha1) (div_pos hδ hb1))
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hε
  have hε1 : |ε| ≤ 1 := hε.trans (min_le_left _ _)
  have hεa : |ε| ≤ δ / (a + 1) :=
    hε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεb : |ε| ≤ δ / (b + 1) :=
    hε.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hmulA1 : |ε| * (a + 1) ≤ δ := (le_div_iff₀ ha1).mp hεa
  have hmulB1 : |ε| * (b + 1) ≤ δ := (le_div_iff₀ hb1).mp hεb
  refine ⟨hε1, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left (by linarith : a ≤ a + 1)
      (abs_nonneg ε)).trans hmulA1
  · exact (mul_le_mul_of_nonneg_left (by linarith : b ≤ b + 1)
      (abs_nonneg ε)).trans hmulB1

/-- Uniform phase control generates all exact-segment and reference-leapfrog
endpoint radius premises on a finite grid after one common step-size choice. -/
theorem RegularPotential.exists_pos_forall_exactGrid_displacements_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) :
    ∃ εbar > 0, ∀ {q : ℝ → Position ι} {p : ℝ → Momentum ι},
      IsHamiltonianCurve gradient q p →
      ∀ {ε : ℝ} {n : ℕ}, |ε| ≤ εbar →
        (∀ k < n, ∀ s ∈ Set.uIcc (0 : ℝ) ε,
          euclideanPhaseSize
            (q ((k : ℝ) * ε + s), p ((k : ℝ) * ε + s)) ≤ B) →
        |ε| ≤ 1 ∧
        (∀ k < n, ∀ s ∈ Set.uIcc (0 : ℝ) ε,
          euclideanNorm
              (q ((k : ℝ) * ε + s) - q ((k : ℝ) * ε)) ≤ δ) ∧
        (∀ k < n, euclideanNorm
            ((leapfrog gradient ε (exactGridPhase q p ε k)).1 -
              (exactGridPhase q p ε k).1) ≤ δ) := by
  let a := ((Fintype.card ι : ℝ) + 1) * B
  let b := B + ((β : ℝ) * B + euclideanNorm (gradient 0)) / 2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by
    dsimp [b]
    exact add_nonneg hB (div_nonneg
      (add_nonneg (mul_nonneg β.coe_nonneg hB) (euclideanNorm_nonneg _))
      (by norm_num))
  obtain ⟨εbar, hεbar, hsmall⟩ :=
    exists_pos_forall_abs_le_and_two_mul_le ha hb hδ
  refine ⟨εbar, hεbar, ?_⟩
  intro q p hcurve ε n hε hphase
  obtain ⟨hε1, hsmallA, hsmallB⟩ := hsmall ε hε
  refine ⟨hε1, ?_, ?_⟩
  · intro k hk s hs
    have hdisp := exactGrid_segment_positionDisplacement_le
      hcurve hB k (hphase k hk) s hs
    exact hdisp.trans (by simpa only [a, mul_comm, mul_left_comm, mul_assoc] using hsmallA)
  · intro k hk
    have hphase0 := hphase k hk 0 Set.left_mem_uIcc
    have hdisp := hreg.leapfrog_positionDisplacement_le_of_phaseSize_le
      hε1 (exactGridPhase q p ε k) (by
        simpa only [exactGridPhase, add_zero] using hphase0)
    exact hdisp.trans (by simpa only [b] using hsmallB)

/-- Shared initial momentum turns exact-flow phase stability into a bound
relative to the initial position separation, uniformly over a finite signed
time grid. -/
theorem RegularPotential.exactGrid_sharedMomentum_phaseSub_le_of_horizon
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (hcurve₁ : IsHamiltonianCurve gradient q₁ p₁)
    (hcurve₂ : IsHamiltonianCurve gradient q₂ p₂)
    (hmomentum : p₁ 0 = p₂ 0) {ε T : ℝ} {n : ℕ}
    (horizon : (n : ℝ) * |ε| ≤ T) :
    ∀ k ≤ n,
      euclideanPhaseSize
          ((exactGridPhase q₁ p₁ ε k).1 - (exactGridPhase q₂ p₂ ε k).1,
            (exactGridPhase q₁ p₁ ε k).2 - (exactGridPhase q₂ p₂ ε k).2) ≤
        exactFlowPhaseStabilityFactor (ι := ι) β T *
          euclideanNorm (q₁ 0 - q₂ 0) := by
  intro k hk
  have hkcast : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
  have htime : |(k : ℝ) * ε| ≤ T := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
    exact (mul_le_mul_of_nonneg_right hkcast (abs_nonneg ε)).trans horizon
  have hraw := hreg.euclideanPhaseSize_phaseSub_le_exp
    hcurve₁ hcurve₂ ((k : ℝ) * ε)
  have hrate : 0 ≤ 1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1) := by
    positivity
  have hfactor :
      exactFlowPhaseStabilityFactor (ι := ι) β ((k : ℝ) * ε) ≤
        exactFlowPhaseStabilityFactor (ι := ι) β T := by
    unfold exactFlowPhaseStabilityFactor
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hT : 0 ≤ T := (abs_nonneg ((k : ℝ) * ε)).trans htime
    rw [abs_of_nonneg hT]
    exact mul_le_mul_of_nonneg_left htime hrate
  have hQ : 0 ≤ euclideanNorm (q₁ 0 - q₂ 0) := euclideanNorm_nonneg _
  calc
    euclideanPhaseSize
        ((exactGridPhase q₁ p₁ ε k).1 - (exactGridPhase q₂ p₂ ε k).1,
          (exactGridPhase q₁ p₁ ε k).2 - (exactGridPhase q₂ p₂ ε k).2) =
      euclideanPhaseSize
        (q₁ ((k : ℝ) * ε) - q₂ ((k : ℝ) * ε),
          p₁ ((k : ℝ) * ε) - p₂ ((k : ℝ) * ε)) := by
        rfl
    _ ≤ exactFlowPhaseStabilityFactor (ι := ι) β ((k : ℝ) * ε) *
        euclideanPhaseSize (q₁ 0 - q₂ 0, p₁ 0 - p₂ 0) := hraw
    _ = exactFlowPhaseStabilityFactor (ι := ι) β ((k : ℝ) * ε) *
        euclideanNorm (q₁ 0 - q₂ 0) := by
          rw [hmomentum, sub_self]
          simp [euclideanPhaseSize]
    _ ≤ exactFlowPhaseStabilityFactor (ι := ι) β T *
        euclideanNorm (q₁ 0 - q₂ 0) :=
      mul_le_mul_of_nonneg_right hfactor hQ

/-- The exact reference phases and their one-step leapfrog images share one
explicit separation coefficient. This discharges the two `A * Q` premises of
compact paired propagation. -/
theorem RegularPotential.exactGrid_sharedMomentum_positionBounds
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (hcurve₁ : IsHamiltonianCurve gradient q₁ p₁)
    (hcurve₂ : IsHamiltonianCurve gradient q₂ p₂)
    (hmomentum : p₁ 0 = p₂ 0) {ε T : ℝ} {n : ℕ}
    (hε : |ε| ≤ 1) (horizon : (n : ℝ) * |ε| ≤ T) :
    let A := (1 + leapfrogNormStabilityRate β) *
      exactFlowPhaseStabilityFactor (ι := ι) β T
    let Q := euclideanNorm (q₁ 0 - q₂ 0)
    (∀ k < n, euclideanNorm
        ((exactGridPhase q₁ p₁ ε k).1 -
          (exactGridPhase q₂ p₂ ε k).1) ≤ A * Q) ∧
      (∀ k < n, euclideanNorm
        ((leapfrog gradient ε (exactGridPhase q₁ p₁ ε k)).1 -
          (leapfrog gradient ε (exactGridPhase q₂ p₂ ε k)).1) ≤ A * Q) := by
  dsimp only
  have hrate : 0 ≤ leapfrogNormStabilityRate β :=
    leapfrogNormStabilityRate_nonneg β
  have hfactor : 0 ≤ exactFlowPhaseStabilityFactor (ι := ι) β T := by
    unfold exactFlowPhaseStabilityFactor
    positivity
  constructor
  · intro k hk
    have hphase := hreg.exactGrid_sharedMomentum_phaseSub_le_of_horizon
      hcurve₁ hcurve₂ hmomentum horizon k (Nat.le_of_lt hk)
    have hfst : euclideanNorm
        ((exactGridPhase q₁ p₁ ε k).1 -
          (exactGridPhase q₂ p₂ ε k).1) ≤
        euclideanPhaseSize
          ((exactGridPhase q₁ p₁ ε k).1 -
              (exactGridPhase q₂ p₂ ε k).1,
            (exactGridPhase q₁ p₁ ε k).2 -
              (exactGridPhase q₂ p₂ ε k).2) := by
      unfold euclideanPhaseSize
      exact le_add_of_nonneg_right (euclideanNorm_nonneg _)
    apply hfst.trans
    apply hphase.trans
    have hQ : 0 ≤ euclideanNorm (q₁ 0 - q₂ 0) := euclideanNorm_nonneg _
    have hone : 1 ≤ 1 + leapfrogNormStabilityRate β := by linarith
    simpa only [mul_assoc] using
      le_mul_of_one_le_left (mul_nonneg hfactor hQ) hone
  · intro k hk
    have hphase := hreg.exactGrid_sharedMomentum_phaseSub_le_of_horizon
      hcurve₁ hcurve₂ hmomentum horizon k (Nat.le_of_lt hk)
    have hstep := leapfrog_euclideanNorm_phaseSub_le hreg hε
      (exactGridPhase q₁ p₁ ε k) (exactGridPhase q₂ p₂ ε k)
    have hfst : euclideanNorm
        ((leapfrog gradient ε (exactGridPhase q₁ p₁ ε k)).1 -
          (leapfrog gradient ε (exactGridPhase q₂ p₂ ε k)).1) ≤
        euclideanNorm
            ((leapfrog gradient ε (exactGridPhase q₁ p₁ ε k)).1 -
              (leapfrog gradient ε (exactGridPhase q₂ p₂ ε k)).1) +
          euclideanNorm
            ((leapfrog gradient ε (exactGridPhase q₁ p₁ ε k)).2 -
              (leapfrog gradient ε (exactGridPhase q₂ p₂ ε k)).2) :=
      le_add_of_nonneg_right (euclideanNorm_nonneg _)
    apply hfst.trans
    apply hstep.trans
    have habs : |ε| ≤ 1 := hε
    have hQ : 0 ≤ euclideanNorm (q₁ 0 - q₂ 0) := euclideanNorm_nonneg _
    have hcoef0 : 0 ≤ 1 + leapfrogNormStabilityRate β * |ε| := by
      positivity
    have hcoef : 1 + leapfrogNormStabilityRate β * |ε| ≤
        1 + leapfrogNormStabilityRate β := by
      have := mul_le_mul_of_nonneg_left habs hrate
      linarith
    calc
      (1 + leapfrogNormStabilityRate β * |ε|) *
          euclideanPhaseSize
            ((exactGridPhase q₁ p₁ ε k).1 -
                (exactGridPhase q₂ p₂ ε k).1,
              (exactGridPhase q₁ p₁ ε k).2 -
                (exactGridPhase q₂ p₂ ε k).2) ≤
        (1 + leapfrogNormStabilityRate β * |ε|) *
          (exactFlowPhaseStabilityFactor (ι := ι) β T *
            euclideanNorm (q₁ 0 - q₂ 0)) :=
        mul_le_mul_of_nonneg_left hphase hcoef0
      _ ≤ (1 + leapfrogNormStabilityRate β) *
          (exactFlowPhaseStabilityFactor (ι := ι) β T *
            euclideanNorm (q₁ 0 - q₂ 0)) :=
        mul_le_mul_of_nonneg_right hcoef (mul_nonneg hfactor hQ)
      _ = (1 + leapfrogNormStabilityRate β) *
          exactFlowPhaseStabilityFactor (ι := ι) β T *
            euclideanNorm (q₁ 0 - q₂ 0) := by ring

/-- Per-unit-time form of arbitrary-paired-phase compact local truncation. -/
noncomputable def compactOneStepPhaseErrorPerTimeRate
    (β : NNReal) (η M ε : ℝ) : ℝ :=
  (((Fintype.card ι : ℝ) + 1) ^ 2 * (β : ℝ) *
        exactFlowPhaseStabilityFactor (ι := ι) β ε + (β : ℝ) / 2) * |ε| +
    ((Fintype.card ι : ℝ) + 1 + 1 / 2) *
      compactExactLeapfrogPhaseForceVariationRate (ι := ι) β η M ε

theorem compactOneStepPhaseErrorRate_eq_abs_mul_perTime
    (β : NNReal) (η M ε : ℝ) :
    compactOneStepPhaseErrorRate (ι := ι) β η M ε =
      |ε| * compactOneStepPhaseErrorPerTimeRate
        (ι := ι) β η M ε := by
  unfold compactOneStepPhaseErrorRate
  unfold leapfrogExactOneStepPhasePositionErrorRate
  unfold leapfrogExactOneStepRelativeMomentumErrorRate
  unfold compactOneStepPhaseErrorPerTimeRate
  ring

theorem continuous_compactOneStepPhaseErrorPerTimeRate
    (β : NNReal) (η M : ℝ) :
    Continuous
      (compactOneStepPhaseErrorPerTimeRate (ι := ι) β η M) := by
  unfold compactOneStepPhaseErrorPerTimeRate
  exact (((((continuous_const.mul continuous_const).mul
    (continuous_exactFlowPhaseStabilityFactor β)).add
      continuous_const).mul continuous_abs).add
        (continuous_const.mul
          (continuous_compactExactLeapfrogPhaseForceVariationRate
            (ι := ι) β η M)))

theorem compactOneStepPhaseErrorPerTimeRate_nonneg
    (β : NNReal) {η M ε : ℝ} (hη : 0 ≤ η) (hM : 0 ≤ M) :
    0 ≤ compactOneStepPhaseErrorPerTimeRate (ι := ι) β η M ε := by
  have hphase : 0 ≤ exactFlowPhaseStabilityFactor (ι := ι) β ε :=
    (exactFlowPhaseStabilityFactor_pos (ι := ι) β ε).le
  have hRE : 0 ≤ exactFlowPhaseRelativeDisplacementRate
      (ι := ι) β ε := by
    unfold exactFlowPhaseRelativeDisplacementRate
    exact add_nonneg (abs_nonneg ε)
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (sq_nonneg _) β.coe_nonneg) hphase)
        (sq_nonneg _))
  have hRL : 0 ≤ leapfrogPhaseRelativeDisplacementRate β ε := by
    unfold leapfrogPhaseRelativeDisplacementRate
    positivity
  have hforce : 0 ≤ compactExactLeapfrogPhaseForceVariationRate
      (ι := ι) β η M ε := by
    unfold compactExactLeapfrogPhaseForceVariationRate
    positivity
  unfold compactOneStepPhaseErrorPerTimeRate
  positivity

/-- Convert the automatic local truncation estimate into the constant-forcing
form used by fixed-horizon grid accumulation. -/
theorem pairedPhaseError_local_le_uniform
    (β : NNReal) {η M ε r A Q Z : ℝ}
    {z₁ z₂ w₁ w₂ : PhaseSpace ι}
    (hη : 0 ≤ η) (hM : 0 ≤ M) (hr : 0 ≤ r)
    (hlocal : pairedPhaseError z₁ z₂ w₁ w₂ ≤
      compactOneStepPhaseErrorRate (ι := ι) β η M ε * Z)
    (hZ0 : 0 ≤ Z)
    (hZ : Z ≤ A * Q)
    (hrate : compactOneStepPhaseErrorPerTimeRate
      (ι := ι) β η M ε ≤ r) :
    pairedPhaseError z₁ z₂ w₁ w₂ ≤ |ε| * (r * A) * Q := by
  have hper : 0 ≤ compactOneStepPhaseErrorPerTimeRate
      (ι := ι) β η M ε :=
    compactOneStepPhaseErrorPerTimeRate_nonneg β hη hM
  calc
    pairedPhaseError z₁ z₂ w₁ w₂ ≤
        compactOneStepPhaseErrorRate (ι := ι) β η M ε * Z := hlocal
    _ = |ε| * compactOneStepPhaseErrorPerTimeRate
          (ι := ι) β η M ε * Z := by
      rw [compactOneStepPhaseErrorRate_eq_abs_mul_perTime]
    _ ≤ |ε| * r * (A * Q) := by gcongr
    _ = |ε| * (r * A) * Q := by ring

/-- Compact shifted local truncation on an exact grid, expressed relative to
the initial position separation under shared initial momentum. The caller no
longer supplies a per-step paired-error estimate. -/
theorem RegularPotential.exists_compact_exactGrid_local_le_initialSeparation
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ M ≥ 0,
      ∀ {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι},
        IsHamiltonianCurve gradient q₁ p₁ →
        IsHamiltonianCurve gradient q₂ p₂ →
        p₁ 0 = p₂ 0 →
        ∀ {ε T : ℝ} {n : ℕ},
          (n : ℝ) * |ε| ≤ T →
          (∀ k < n, (exactGridPhase q₁ p₁ ε k).1 ∈ S) →
          (∀ k < n, (exactGridPhase q₂ p₂ ε k).1 ∈ S) →
          (∀ k < n, ∀ s ∈ Set.uIcc (0 : ℝ) ε,
            q₁ ((k : ℝ) * ε + s) ∈ S) →
          (∀ k < n, ∀ s ∈ Set.uIcc (0 : ℝ) ε,
            q₂ ((k : ℝ) * ε + s) ∈ S) →
          (∀ k < n, ∀ s ∈ Set.uIcc (0 : ℝ) ε,
            euclideanNorm
              (q₁ ((k : ℝ) * ε + s) - q₁ ((k : ℝ) * ε)) ≤ δ) →
          (∀ k < n, ∀ s ∈ Set.uIcc (0 : ℝ) ε,
            euclideanNorm
              (q₂ ((k : ℝ) * ε + s) - q₂ ((k : ℝ) * ε)) ≤ δ) →
          (∀ k < n,
            (leapfrog gradient ε (exactGridPhase q₁ p₁ ε k)).1 ∈ S) →
          (∀ k < n,
            (leapfrog gradient ε (exactGridPhase q₂ p₂ ε k)).1 ∈ S) →
          (∀ k < n, euclideanNorm
            ((leapfrog gradient ε (exactGridPhase q₁ p₁ ε k)).1 -
              (exactGridPhase q₁ p₁ ε k).1) ≤ δ) →
          (∀ k < n, euclideanNorm
            ((leapfrog gradient ε (exactGridPhase q₂ p₂ ε k)).1 -
              (exactGridPhase q₂ p₂ ε k).1) ≤ δ) →
          ∀ k < n,
            pairedPhaseError
                (leapfrog gradient ε (exactGridPhase q₁ p₁ ε k))
                (leapfrog gradient ε (exactGridPhase q₂ p₂ ε k))
                (exactGridPhase q₁ p₁ ε (k + 1))
                (exactGridPhase q₂ p₂ ε (k + 1)) ≤
              |ε| *
                  (compactOneStepPhaseErrorPerTimeRate
                      (ι := ι) β η M ε *
                    exactFlowPhaseStabilityFactor (ι := ι) β T) *
                euclideanNorm (q₁ 0 - q₂ 0) := by
  obtain ⟨δ, hδ, M, hM, hlocal⟩ :=
    hreg.exists_compact_exactGrid_oneStepPhaseError_bound
      hScompact hSconvex hη
  refine ⟨δ, hδ, M, hM, ?_⟩
  intro q₁ q₂ p₁ p₂ hcurve₁ hcurve₂ hmomentum ε T n horizon
    hq₁ hq₂ hq₁S hq₂S hq₁disp hq₂disp hlf₁ hlf₂ hlf₁disp hlf₂disp k hk
  let Z := euclideanPhaseSize
    ((exactGridPhase q₁ p₁ ε k).1 - (exactGridPhase q₂ p₂ ε k).1,
      (exactGridPhase q₁ p₁ ε k).2 - (exactGridPhase q₂ p₂ ε k).2)
  let A := exactFlowPhaseStabilityFactor (ι := ι) β T
  let Q := euclideanNorm (q₁ 0 - q₂ 0)
  let r := compactOneStepPhaseErrorPerTimeRate (ι := ι) β η M ε
  have hraw := hlocal hcurve₁ hcurve₂
    (hq₁ k hk) (hq₂ k hk) (hq₁S k hk) (hq₂S k hk)
    (hq₁disp k hk) (hq₂disp k hk) (hlf₁ k hk) (hlf₂ k hk)
    (hlf₁disp k hk) (hlf₂disp k hk)
  have hZ : Z ≤ A * Q :=
    hreg.exactGrid_sharedMomentum_phaseSub_le_of_horizon
      hcurve₁ hcurve₂ hmomentum horizon k (Nat.le_of_lt hk)
  have hr : 0 ≤ r :=
    compactOneStepPhaseErrorPerTimeRate_nonneg β hη.le hM
  have hout := pairedPhaseError_local_le_uniform
    (ι := ι) β hη.le hM hr hraw (euclideanPhaseSize_nonneg _) hZ le_rfl
  simpa only [Z, A, Q, r] using hout

@[simp]
theorem compactOneStepPhaseErrorPerTimeRate_zero
    (β : NNReal) (η M : ℝ) :
    compactOneStepPhaseErrorPerTimeRate (ι := ι) β η M 0 =
      ((Fintype.card ι : ℝ) + 1 + 1 / 2) *
        (((Fintype.card ι : ℝ) + 1) * η) := by
  simp [compactOneStepPhaseErrorPerTimeRate]

theorem exists_pos_forall_compactOneStepPhaseErrorPerTimeRate_lt
    (β : NNReal) {η M ρ : ℝ}
    (hlimit : ((Fintype.card ι : ℝ) + 1 + 1 / 2) *
        (((Fintype.card ι : ℝ) + 1) * η) < ρ) :
    ∃ εbar > 0, ∀ ε, |ε| ≤ εbar →
      compactOneStepPhaseErrorPerTimeRate
        (ι := ι) β η M ε < ρ := by
  let f := compactOneStepPhaseErrorPerTimeRate (ι := ι) β η M
  have hf : ContinuousAt f 0 :=
    (continuous_compactOneStepPhaseErrorPerTimeRate
      (ι := ι) β η M).continuousAt
  have hzero : f 0 < ρ := by simpa [f] using hlimit
  have hev : ∀ᶠ ε in nhds (0 : ℝ), f ε < ρ :=
    hf.eventually_lt continuousAt_const hzero
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro ε hε
  apply hball
  rw [Metric.mem_ball, Real.dist_eq]
  have : |ε| < r := hε.trans_lt (half_lt_self hr)
  simpa only [sub_zero] using this

/-- Arbitrary-paired-phase local truncation has an arbitrarily small uniform
per-time coefficient after choosing the compact Hessian tolerance and then
the step size. -/
theorem exists_eta_forall_M_exists_pos_compactOneStepPhasePerTimeRate_lt
    (β : NNReal) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ η > 0, ∀ M : ℝ, ∃ εbar > 0, ∀ ε, |ε| ≤ εbar →
      compactOneStepPhaseErrorPerTimeRate
        (ι := ι) β η M ε < ρ := by
  let D : ℝ := (Fintype.card ι : ℝ) + 1
  let C : ℝ := D + 1 / 2
  let η : ℝ := ρ / (2 * C * D)
  have hD : 0 < D := by dsimp [D]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨η, hη, ?_⟩
  intro M
  apply exists_pos_forall_compactOneStepPhaseErrorPerTimeRate_lt
    (ι := ι) β
  have hCD : C * D ≠ 0 := mul_ne_zero hC.ne' hD.ne'
  have heq : C * (D * η) = ρ / 2 := by
    dsimp [η]
    field_simp
  change C * (D * η) < ρ
  rw [heq]
  linarith

/-- Per-unit-time form of the automatic compact one-step phase rate. -/
noncomputable def compactOneStepRelativePhaseErrorPerTimeRate
    (β : NNReal) (η M ε : ℝ) : ℝ :=
  (((Fintype.card ι : ℝ) + 1) ^ 2 * (β : ℝ) *
        exactFlowPositionStabilityFactor (ι := ι) β ε + (β : ℝ) / 2) * |ε| +
    ((Fintype.card ι : ℝ) + 1 + 1 / 2) *
      compactExactLeapfrogForceVariationRate (ι := ι) β η M ε

theorem compactOneStepRelativePhaseErrorRate_eq_abs_mul_perTime
    (β : NNReal) (η M ε : ℝ) :
    compactOneStepRelativePhaseErrorRate (ι := ι) β η M ε =
      |ε| * compactOneStepRelativePhaseErrorPerTimeRate
        (ι := ι) β η M ε := by
  unfold compactOneStepRelativePhaseErrorRate
  unfold leapfrogExactOneStepRelativePositionErrorRate
  unfold leapfrogExactOneStepRelativeMomentumErrorRate
  unfold compactOneStepRelativePhaseErrorPerTimeRate
  ring

theorem continuous_compactOneStepRelativePhaseErrorPerTimeRate
    (β : NNReal) (η M : ℝ) :
    Continuous
      (compactOneStepRelativePhaseErrorPerTimeRate (ι := ι) β η M) := by
  unfold compactOneStepRelativePhaseErrorPerTimeRate
  exact (((((continuous_const.mul continuous_const).mul
    (continuous_exactFlowPositionStabilityFactor β)).add
      continuous_const).mul continuous_abs).add
        (continuous_const.mul
          (continuous_compactExactLeapfrogForceVariationRate
            (ι := ι) β η M)))

@[simp]
theorem compactOneStepRelativePhaseErrorPerTimeRate_zero
    (β : NNReal) (η M : ℝ) :
    compactOneStepRelativePhaseErrorPerTimeRate (ι := ι) β η M 0 =
      ((Fintype.card ι : ℝ) + 1 + 1 / 2) *
        (((Fintype.card ι : ℝ) + 1) * η) := by
  simp [compactOneStepRelativePhaseErrorPerTimeRate]

/-- Once the compact Hessian-continuity tolerance makes the zero-step limit
smaller than `ρ`, one symmetric step-size neighborhood has per-time error
strictly below `ρ`. -/
theorem exists_pos_forall_compactOneStepRelativePhaseErrorPerTimeRate_lt
    (β : NNReal) {η M ρ : ℝ}
    (hlimit : ((Fintype.card ι : ℝ) + 1 + 1 / 2) *
        (((Fintype.card ι : ℝ) + 1) * η) < ρ) :
    ∃ εbar > 0, ∀ ε, |ε| ≤ εbar →
      compactOneStepRelativePhaseErrorPerTimeRate
        (ι := ι) β η M ε < ρ := by
  let f := compactOneStepRelativePhaseErrorPerTimeRate (ι := ι) β η M
  have hf : ContinuousAt f 0 :=
    (continuous_compactOneStepRelativePhaseErrorPerTimeRate
      (ι := ι) β η M).continuousAt
  have hzero : f 0 < ρ := by
    simpa [f] using hlimit
  have hev : ∀ᶠ ε in nhds (0 : ℝ), f ε < ρ :=
    hf.eventually_lt continuousAt_const hzero
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro ε hε
  apply hball
  rw [Metric.mem_ball, Real.dist_eq]
  have : |ε| < r := hε.trans_lt (half_lt_self hr)
  simpa only [sub_zero] using this

/-- Every positive per-time error allowance can be met by first choosing the
compact Hessian-continuity tolerance and then a sufficiently small step size.
The compact Hessian bound `M` may depend on that tolerance. -/
theorem exists_eta_forall_M_exists_pos_compactOneStepPerTimeRate_lt
    (β : NNReal) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ η > 0, ∀ M : ℝ, ∃ εbar > 0, ∀ ε, |ε| ≤ εbar →
      compactOneStepRelativePhaseErrorPerTimeRate
        (ι := ι) β η M ε < ρ := by
  let D : ℝ := (Fintype.card ι : ℝ) + 1
  let C : ℝ := D + 1 / 2
  let η : ℝ := ρ / (2 * C * D)
  have hD : 0 < D := by dsimp [D]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨η, hη, ?_⟩
  intro M
  apply exists_pos_forall_compactOneStepRelativePhaseErrorPerTimeRate_lt
    (ι := ι) β
  have hCD : C * D ≠ 0 := mul_ne_zero hC.ne' hD.ne'
  have heq : C * (D * η) = ρ / 2 := by
    dsimp [η]
    field_simp
  change C * (D * η) < ρ
  rw [heq]
  linarith

theorem pairedPhaseError_nonneg
    (z₁ z₂ w₁ w₂ : PhaseSpace ι) :
    0 ≤ pairedPhaseError z₁ z₂ w₁ w₂ :=
  euclideanPhaseSize_nonneg _

@[simp]
theorem pairedPhaseError_self (z₁ z₂ : PhaseSpace ι) :
    pairedPhaseError z₁ z₂ z₁ z₂ = 0 := by
  simp [pairedPhaseError, euclideanPhaseSize]

/-- Triangle inequality through an intermediate paired relative phase. -/
theorem pairedPhaseError_triangle
    (z₁ z₂ w₁ w₂ u₁ u₂ : PhaseSpace ι) :
    pairedPhaseError z₁ z₂ u₁ u₂ ≤
      pairedPhaseError z₁ z₂ w₁ w₂ +
        pairedPhaseError w₁ w₂ u₁ u₂ := by
  unfold pairedPhaseError euclideanPhaseSize
  have hq : euclideanNorm
      ((z₁.1 - z₂.1) - (u₁.1 - u₂.1)) ≤
      euclideanNorm ((z₁.1 - z₂.1) - (w₁.1 - w₂.1)) +
        euclideanNorm ((w₁.1 - w₂.1) - (u₁.1 - u₂.1)) := by
    rw [show (z₁.1 - z₂.1) - (u₁.1 - u₂.1) =
      ((z₁.1 - z₂.1) - (w₁.1 - w₂.1)) +
        ((w₁.1 - w₂.1) - (u₁.1 - u₂.1)) by abel]
    exact euclideanNorm_add_le _ _
  have hp : euclideanNorm
      ((z₁.2 - z₂.2) - (u₁.2 - u₂.2)) ≤
      euclideanNorm ((z₁.2 - z₂.2) - (w₁.2 - w₂.2)) +
        euclideanNorm ((w₁.2 - w₂.2) - (u₁.2 - u₂.2)) := by
    rw [show (z₁.2 - z₂.2) - (u₁.2 - u₂.2) =
      ((z₁.2 - z₂.2) - (w₁.2 - w₂.2)) +
        ((w₁.2 - w₂.2) - (u₁.2 - u₂.2)) by abel]
    exact euclideanNorm_add_le _ _
  linarith

/-- One grid step composes homogeneous four-trajectory propagation with the
local truncation of the shifted exact reference pair. -/
theorem pairedPhaseError_gridStep_le
    (gradient : Position ι → Position ι)
    {ε C r Q : ℝ}
    (z₁ z₂ w₁ w₂ : ℕ → PhaseSpace ι)
    (hnum₁ : ∀ k, z₁ (k + 1) = leapfrog gradient ε (z₁ k))
    (hnum₂ : ∀ k, z₂ (k + 1) = leapfrog gradient ε (z₂ k))
    (hprop : ∀ k,
      pairedPhaseError
          (leapfrog gradient ε (z₁ k))
          (leapfrog gradient ε (z₂ k))
          (leapfrog gradient ε (w₁ k))
          (leapfrog gradient ε (w₂ k)) ≤
        Real.exp (C * |ε|) *
          pairedPhaseError (z₁ k) (z₂ k) (w₁ k) (w₂ k))
    (hlocal : ∀ k,
      pairedPhaseError
          (leapfrog gradient ε (w₁ k))
          (leapfrog gradient ε (w₂ k))
          (w₁ (k + 1)) (w₂ (k + 1)) ≤
        |ε| * r * Q) :
    ∀ k, pairedPhaseError
        (z₁ (k + 1)) (z₂ (k + 1)) (w₁ (k + 1)) (w₂ (k + 1)) ≤
      Real.exp (C * |ε|) *
          pairedPhaseError (z₁ k) (z₂ k) (w₁ k) (w₂ k) +
        |ε| * r * Q := by
  intro k
  rw [hnum₁ k, hnum₂ k]
  apply (pairedPhaseError_triangle
    (leapfrog gradient ε (z₁ k))
    (leapfrog gradient ε (z₂ k))
    (leapfrog gradient ε (w₁ k))
    (leapfrog gradient ε (w₂ k))
    (w₁ (k + 1)) (w₂ (k + 1))).trans
  exact add_le_add (hprop k) (hlocal k)

/-- Grid-step composition when compact four-trajectory propagation itself
has a small forcing term. The propagation and shifted local-truncation rates
add. -/
theorem pairedPhaseError_gridStep_le_withPropagationForcing
    (gradient : Position ι → Position ι)
    {ε C s r Q : ℝ}
    (z₁ z₂ w₁ w₂ : ℕ → PhaseSpace ι) (k : ℕ)
    (hnum₁ : z₁ (k + 1) = leapfrog gradient ε (z₁ k))
    (hnum₂ : z₂ (k + 1) = leapfrog gradient ε (z₂ k))
    (hprop :
      pairedPhaseError
          (leapfrog gradient ε (z₁ k))
          (leapfrog gradient ε (z₂ k))
          (leapfrog gradient ε (w₁ k))
          (leapfrog gradient ε (w₂ k)) ≤
        Real.exp (C * |ε|) *
            pairedPhaseError (z₁ k) (z₂ k) (w₁ k) (w₂ k) +
          |ε| * s * Q)
    (hlocal :
      pairedPhaseError
          (leapfrog gradient ε (w₁ k))
          (leapfrog gradient ε (w₂ k))
          (w₁ (k + 1)) (w₂ (k + 1)) ≤
        |ε| * r * Q) :
    pairedPhaseError
        (z₁ (k + 1)) (z₂ (k + 1)) (w₁ (k + 1)) (w₂ (k + 1)) ≤
      Real.exp (C * |ε|) *
          pairedPhaseError (z₁ k) (z₂ k) (w₁ k) (w₂ k) +
        |ε| * (s + r) * Q := by
  rw [hnum₁, hnum₂]
  apply (pairedPhaseError_triangle
    (leapfrog gradient ε (z₁ k))
    (leapfrog gradient ε (z₂ k))
    (leapfrog gradient ε (w₁ k))
    (leapfrog gradient ε (w₂ k))
    (w₁ (k + 1)) (w₂ (k + 1))).trans
  apply (add_le_add hprop hlocal).trans_eq
  ring

/-- Scalar discrete Grönwall estimate for a nonnegative error recurrence with
constant local forcing. The deliberately coarse `n b aⁿ` form is convenient
for fixed-horizon numerical integration. -/
theorem error_le_nat_mul_pow_of_le_mul_add
    {e : ℕ → ℝ} {a b : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b)
    (he0 : e 0 = 0)
    (hstep : ∀ n, e (n + 1) ≤ a * e n + b) :
    ∀ n, e n ≤ (n : ℝ) * b * a ^ n := by
  intro n
  induction n with
  | zero => simp [he0]
  | succ n ih =>
      have ha0 : 0 ≤ a := zero_le_one.trans ha
      have hpow : 1 ≤ a ^ (n + 1) := one_le_pow₀ ha
      have hmul := mul_le_mul_of_nonneg_left ih ha0
      have hbpow : b ≤ b * a ^ (n + 1) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hb
      calc
        e (Nat.succ n) = e (n + 1) := by rw [Nat.succ_eq_add_one]
        _ ≤ a * e n + b := hstep n
        _ ≤ a * ((n : ℝ) * b * a ^ n) + b := add_le_add hmul le_rfl
        _ ≤ a * ((n : ℝ) * b * a ^ n) + b * a ^ (n + 1) :=
          add_le_add le_rfl hbpow
        _ = (Nat.succ n : ℝ) * b * a ^ (Nat.succ n) := by
          rw [Nat.cast_succ, pow_succ]
          ring

/-- Finite-index version of the scalar recurrence: only steps strictly before
the requested endpoint are required. -/
theorem error_le_nat_mul_pow_of_forall_lt
    {e : ℕ → ℝ} {a b : ℝ} {n : ℕ} (ha : 1 ≤ a) (hb : 0 ≤ b)
    (he0 : e 0 = 0)
    (hstep : ∀ k < n, e (k + 1) ≤ a * e k + b) :
    e n ≤ (n : ℝ) * b * a ^ n := by
  induction n with
  | zero => simp [he0]
  | succ n ih =>
      have ha0 : 0 ≤ a := zero_le_one.trans ha
      have hpow : 1 ≤ a ^ (n + 1) := one_le_pow₀ ha
      have ih' := ih (fun k hk ↦ hstep k (hk.trans (Nat.lt_succ_self n)))
      have hmul := mul_le_mul_of_nonneg_left ih' ha0
      have hbpow : b ≤ b * a ^ (n + 1) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hb
      calc
        e (Nat.succ n) = e (n + 1) := by rw [Nat.succ_eq_add_one]
        _ ≤ a * e n + b := hstep n (Nat.lt_succ_self n)
        _ ≤ a * ((n : ℝ) * b * a ^ n) + b := add_le_add hmul le_rfl
        _ ≤ a * ((n : ℝ) * b * a ^ n) + b * a ^ (n + 1) :=
          add_le_add le_rfl hbpow
        _ = (Nat.succ n : ℝ) * b * a ^ (Nat.succ n) := by
          rw [Nat.cast_succ, pow_succ]
          ring

/-- Fixed-horizon form of the scalar accumulation estimate. A local forcing
`|ε| r Q` accumulated over `n|ε| ≤ T` is at most
`T r exp(C T) Q`. -/
theorem error_le_fixedHorizon_of_le_exp_mul_add
    {e : ℕ → ℝ} {C r Q ε T : ℝ} {n : ℕ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hQ : 0 ≤ Q)
    (he0 : e 0 = 0)
    (hstep : ∀ k, e (k + 1) ≤
      Real.exp (C * |ε|) * e k + |ε| * r * Q)
    (horizon : (n : ℝ) * |ε| ≤ T) :
    e n ≤ T * r * Real.exp (C * T) * Q := by
  have ha : 1 ≤ Real.exp (C * |ε|) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonneg hC (abs_nonneg ε))
  have hb : 0 ≤ |ε| * r * Q := by positivity
  have hraw := error_le_nat_mul_pow_of_le_mul_add
    ha hb he0 hstep n
  have hT : 0 ≤ T :=
    (mul_nonneg (Nat.cast_nonneg n) (abs_nonneg ε)).trans horizon
  have hexpPow : Real.exp (C * |ε|) ^ n =
      Real.exp (C * ((n : ℝ) * |ε|)) := by
    calc
      Real.exp (C * |ε|) ^ n =
          Real.exp ((n : ℝ) * (C * |ε|)) :=
        (Real.exp_nat_mul (C * |ε|) n).symm
      _ = Real.exp (C * ((n : ℝ) * |ε|)) := by
        congr 1
        ring
  rw [hexpPow] at hraw
  have hexp : Real.exp (C * ((n : ℝ) * |ε|)) ≤ Real.exp (C * T) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left horizon hC
  calc
    e n ≤ (n : ℝ) * (|ε| * r * Q) *
        Real.exp (C * ((n : ℝ) * |ε|)) := hraw
    _ = ((n : ℝ) * |ε|) * r *
        Real.exp (C * ((n : ℝ) * |ε|)) * Q := by ring
    _ ≤ T * r * Real.exp (C * T) * Q := by gcongr

/-- Finite-index fixed-horizon accumulation, requiring the recurrence only
for grid steps before `n`. -/
theorem error_le_fixedHorizon_of_forall_lt
    {e : ℕ → ℝ} {C r Q ε T : ℝ} {n : ℕ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hQ : 0 ≤ Q)
    (he0 : e 0 = 0)
    (hstep : ∀ k < n, e (k + 1) ≤
      Real.exp (C * |ε|) * e k + |ε| * r * Q)
    (horizon : (n : ℝ) * |ε| ≤ T) :
    e n ≤ T * r * Real.exp (C * T) * Q := by
  have ha : 1 ≤ Real.exp (C * |ε|) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonneg hC (abs_nonneg ε))
  have hb : 0 ≤ |ε| * r * Q := by positivity
  have hraw := error_le_nat_mul_pow_of_forall_lt
    ha hb he0 hstep
  have hT : 0 ≤ T :=
    (mul_nonneg (Nat.cast_nonneg n) (abs_nonneg ε)).trans horizon
  have hexpPow : Real.exp (C * |ε|) ^ n =
      Real.exp (C * ((n : ℝ) * |ε|)) := by
    calc
      Real.exp (C * |ε|) ^ n =
          Real.exp ((n : ℝ) * (C * |ε|)) :=
        (Real.exp_nat_mul (C * |ε|) n).symm
      _ = Real.exp (C * ((n : ℝ) * |ε|)) := by
        congr 1
        ring
  rw [hexpPow] at hraw
  have hexp : Real.exp (C * ((n : ℝ) * |ε|)) ≤ Real.exp (C * T) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left horizon hC
  calc
    e n ≤ (n : ℝ) * (|ε| * r * Q) *
        Real.exp (C * ((n : ℝ) * |ε|)) := hraw
    _ = ((n : ℝ) * |ε|) * r *
        Real.exp (C * ((n : ℝ) * |ε|)) * Q := by ring
    _ ≤ T * r * Real.exp (C * T) * Q := by gcongr

/-- Fixed-horizon grid accumulation for paired numerical-versus-exact phase
error. All analytic and containment work is isolated in the per-step
propagation and local-truncation premises. -/
theorem pairedPhaseError_le_fixedHorizon
    (gradient : Position ι → Position ι)
    {ε C r Q T : ℝ} {n : ℕ}
    (z₁ z₂ w₁ w₂ : ℕ → PhaseSpace ι)
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hQ : 0 ≤ Q)
    (hinitial : pairedPhaseError (z₁ 0) (z₂ 0) (w₁ 0) (w₂ 0) = 0)
    (hnum₁ : ∀ k < n, z₁ (k + 1) = leapfrog gradient ε (z₁ k))
    (hnum₂ : ∀ k < n, z₂ (k + 1) = leapfrog gradient ε (z₂ k))
    (hprop : ∀ k < n,
      pairedPhaseError
          (leapfrog gradient ε (z₁ k))
          (leapfrog gradient ε (z₂ k))
          (leapfrog gradient ε (w₁ k))
          (leapfrog gradient ε (w₂ k)) ≤
        Real.exp (C * |ε|) *
          pairedPhaseError (z₁ k) (z₂ k) (w₁ k) (w₂ k))
    (hlocal : ∀ k < n,
      pairedPhaseError
          (leapfrog gradient ε (w₁ k))
          (leapfrog gradient ε (w₂ k))
          (w₁ (k + 1)) (w₂ (k + 1)) ≤
        |ε| * r * Q)
    (horizon : (n : ℝ) * |ε| ≤ T) :
    pairedPhaseError (z₁ n) (z₂ n) (w₁ n) (w₂ n) ≤
      T * r * Real.exp (C * T) * Q := by
  let e : ℕ → ℝ := fun k ↦
    pairedPhaseError (z₁ k) (z₂ k) (w₁ k) (w₂ k)
  apply error_le_fixedHorizon_of_forall_lt
    (e := e) hC hr hQ hinitial
  · intro k hk
    dsimp [e]
    rw [hnum₁ k hk, hnum₂ k hk]
    exact (pairedPhaseError_triangle
      (leapfrog gradient ε (z₁ k))
      (leapfrog gradient ε (z₂ k))
      (leapfrog gradient ε (w₁ k))
      (leapfrog gradient ε (w₂ k))
      (w₁ (k + 1)) (w₂ (k + 1))).trans
        (add_le_add (hprop k hk) (hlocal k hk))
  · exact horizon

/-- Fixed-horizon accumulation with both compact propagation forcing and
shifted exact-flow local truncation. -/
theorem pairedPhaseError_le_fixedHorizon_withPropagationForcing
    (gradient : Position ι → Position ι)
    {ε C s r Q T : ℝ} {n : ℕ}
    (z₁ z₂ w₁ w₂ : ℕ → PhaseSpace ι)
    (hC : 0 ≤ C) (hs : 0 ≤ s) (hr : 0 ≤ r) (hQ : 0 ≤ Q)
    (hinitial : pairedPhaseError (z₁ 0) (z₂ 0) (w₁ 0) (w₂ 0) = 0)
    (hnum₁ : ∀ k < n, z₁ (k + 1) = leapfrog gradient ε (z₁ k))
    (hnum₂ : ∀ k < n, z₂ (k + 1) = leapfrog gradient ε (z₂ k))
    (hprop : ∀ k < n,
      pairedPhaseError
          (leapfrog gradient ε (z₁ k))
          (leapfrog gradient ε (z₂ k))
          (leapfrog gradient ε (w₁ k))
          (leapfrog gradient ε (w₂ k)) ≤
        Real.exp (C * |ε|) *
            pairedPhaseError (z₁ k) (z₂ k) (w₁ k) (w₂ k) +
          |ε| * s * Q)
    (hlocal : ∀ k < n,
      pairedPhaseError
          (leapfrog gradient ε (w₁ k))
          (leapfrog gradient ε (w₂ k))
          (w₁ (k + 1)) (w₂ (k + 1)) ≤
        |ε| * r * Q)
    (horizon : (n : ℝ) * |ε| ≤ T) :
    pairedPhaseError (z₁ n) (z₂ n) (w₁ n) (w₂ n) ≤
      T * (s + r) * Real.exp (C * T) * Q := by
  let e : ℕ → ℝ := fun k ↦
    pairedPhaseError (z₁ k) (z₂ k) (w₁ k) (w₂ k)
  apply error_le_fixedHorizon_of_forall_lt
    (e := e) hC (add_nonneg hs hr) hQ hinitial
  · intro k hk
    exact pairedPhaseError_gridStep_le_withPropagationForcing
      gradient z₁ z₂ w₁ w₂ k (hnum₁ k hk) (hnum₂ k hk)
        (hprop k hk) (hlocal k hk)
  · exact horizon

/-- One absolute numerical-versus-exact grid step: leapfrog stability
propagates the old error and quadratic local consistency supplies the forcing. -/
theorem RegularPotential.absolutePhaseError_gridStep_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {ε K : ℝ} (hε : |ε| ≤ 1)
    (z w : ℕ → PhaseSpace ι) (k : ℕ)
    (hnum : z (k + 1) = leapfrog gradient ε (z k))
    (hlocal : absolutePhaseError
      (leapfrog gradient ε (w k)) (w (k + 1)) ≤ |ε| ^ 2 * K) :
    absolutePhaseError (z (k + 1)) (w (k + 1)) ≤
      Real.exp (leapfrogNormStabilityRate β * |ε|) *
          absolutePhaseError (z k) (w k) +
        |ε| * (|ε| * K) := by
  rw [hnum]
  apply (absolutePhaseError_triangle
    (leapfrog gradient ε (z k))
    (leapfrog gradient ε (w k)) (w (k + 1))).trans
  have hprop := leapfrog_euclideanNorm_phaseSub_le
    hreg hε (z k) (w k)
  have hfactor : 1 + leapfrogNormStabilityRate β * |ε| ≤
      Real.exp (leapfrogNormStabilityRate β * |ε|) := by
    simpa [add_comm] using Real.add_one_le_exp
      (leapfrogNormStabilityRate β * |ε|)
  have hfactorError := mul_le_mul_of_nonneg_right hfactor
    (absolutePhaseError_nonneg (z k) (w k))
  have hprop' : absolutePhaseError
      (leapfrog gradient ε (z k)) (leapfrog gradient ε (w k)) ≤
      Real.exp (leapfrogNormStabilityRate β * |ε|) *
        absolutePhaseError (z k) (w k) := by
    unfold absolutePhaseError euclideanPhaseSize
    exact hprop.trans hfactorError
  apply (add_le_add hprop' hlocal).trans_eq
  ring

/-- Absolute leapfrog-versus-exact error accumulated over a fixed horizon.
A quadratic local coefficient produces a global `O(|ε|)` bound. -/
theorem RegularPotential.absolutePhaseError_le_fixedHorizon
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {ε K T : ℝ} {n : ℕ} (hε : |ε| ≤ 1) (hK : 0 ≤ K)
    (z w : ℕ → PhaseSpace ι)
    (hinitial : absolutePhaseError (z 0) (w 0) = 0)
    (hnum : ∀ k, z (k + 1) = leapfrog gradient ε (z k))
    (hlocal : ∀ k < n, absolutePhaseError
      (leapfrog gradient ε (w k)) (w (k + 1)) ≤ |ε| ^ 2 * K)
    (horizon : (n : ℝ) * |ε| ≤ T) :
    absolutePhaseError (z n) (w n) ≤
      T * (|ε| * K) *
        Real.exp (leapfrogNormStabilityRate β * T) := by
  let e : ℕ → ℝ := fun k ↦ absolutePhaseError (z k) (w k)
  have hC := leapfrogNormStabilityRate_nonneg β
  have hr : 0 ≤ |ε| * K := mul_nonneg (abs_nonneg ε) hK
  have hstep' : ∀ k < n, e (k + 1) ≤
      Real.exp (leapfrogNormStabilityRate β * |ε|) * e k +
        |ε| * (|ε| * K) * 1 := by
    intro k hk
    have hstep := hreg.absolutePhaseError_gridStep_le
      hε z w k (hnum k) (hlocal k hk)
    simpa only [e, mul_one] using hstep
  have h := error_le_fixedHorizon_of_forall_lt
    (e := e) (Q := 1) hC hr (by norm_num) hinitial hstep' horizon
  simpa only [mul_one] using h

/-- Concrete fixed-horizon absolute error between an iterated leapfrog
trajectory and the exact Hamiltonian phase sampled on the same grid. -/
theorem RegularPotential.absolutePhaseError_leapfrogN_exactGrid_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q : ℝ → Position ι} {p : ℝ → Momentum ι}
    (hcurve : IsHamiltonianCurve gradient q p)
    {B : ℝ} (hB : 0 ≤ B) {ε T : ℝ} {n : ℕ} (hε : |ε| ≤ 1)
    (hphase : ∀ k < n, ∀ s ∈ Set.uIcc (0 : ℝ) ε,
      euclideanPhaseSize
        (q ((k : ℝ) * ε + s), p ((k : ℝ) * ε + s)) ≤ B)
    (horizon : (n : ℝ) * |ε| ≤ T) :
    absolutePhaseError
        (leapfrogN gradient ε n (q 0, p 0))
        (exactGridPhase q p ε n) ≤
      T *
          (|ε| * leapfrogExactAbsolutePhaseErrorCoefficient
            (ι := ι) β gradient B) *
        Real.exp (leapfrogNormStabilityRate β * T) := by
  let z : ℕ → PhaseSpace ι := fun k ↦
    leapfrogN gradient ε k (q 0, p 0)
  let w : ℕ → PhaseSpace ι := fun k ↦ exactGridPhase q p ε k
  let K := leapfrogExactAbsolutePhaseErrorCoefficient
    (ι := ι) β gradient B
  have hK : 0 ≤ K :=
    leapfrogExactAbsolutePhaseErrorCoefficient_nonneg β gradient hB
  have hinitial : absolutePhaseError (z 0) (w 0) = 0 := by
    simp [z, w, leapfrogN]
  have hnum : ∀ k, z (k + 1) = leapfrog gradient ε (z k) := by
    intro k
    simp only [z, leapfrogN, Function.iterate_succ_apply']
  have hlocal : ∀ k < n, absolutePhaseError
      (leapfrog gradient ε (w k)) (w (k + 1)) ≤ |ε| ^ 2 * K := by
    intro k hk
    exact hreg.exactGrid_absolutePhaseError_local_le
      hcurve hB hε k (hphase k hk)
  have h := hreg.absolutePhaseError_le_fixedHorizon
    hε hK z w hinitial hnum hlocal horizon
  simpa only [z, w, K] using h

/-- Fixed-horizon absolute error with the indexed exact phase bound generated
automatically from a bound on the initial phase. -/
theorem RegularPotential.absolutePhaseError_leapfrogN_exactGrid_le_of_initial
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q : ℝ → Position ι} {p : ℝ → Momentum ι}
    (hcurve : IsHamiltonianCurve gradient q p)
    {M T : ℝ} (hM : 0 ≤ M)
    (hinitial : euclideanPhaseSize (q 0, p 0) ≤ M)
    {ε : ℝ} {n : ℕ} (hε : |ε| ≤ 1)
    (horizon : (n : ℝ) * |ε| ≤ T) :
    absolutePhaseError
        (leapfrogN gradient ε n (q 0, p 0))
        (exactGridPhase q p ε n) ≤
      leapfrogExactAbsoluteFixedHorizonErrorRate
        (ι := ι) β gradient
          (exactFlowUniformEuclideanPhaseBound
            (ι := ι) β gradient M T) T ε := by
  let B := exactFlowUniformEuclideanPhaseBound
    (ι := ι) β gradient M T
  have hB : 0 ≤ B :=
    exactFlowUniformEuclideanPhaseBound_nonneg β gradient hM
  have hphase := hreg.exactGrid_phaseSize_le_uniform_of_horizon
    hcurve hM hinitial horizon
  have h := hreg.absolutePhaseError_leapfrogN_exactGrid_le
    hcurve hB hε hphase horizon
  simpa only [B, leapfrogExactAbsoluteFixedHorizonErrorRate] using h

/-- The absolute error estimate holds uniformly at every completed grid point
inside the requested horizon. -/
theorem RegularPotential.absolutePhaseError_leapfrogN_exactGrid_le_on_Iic
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q : ℝ → Position ι} {p : ℝ → Momentum ι}
    (hcurve : IsHamiltonianCurve gradient q p)
    {B : ℝ} (hB : 0 ≤ B) {ε T : ℝ} {n : ℕ} (hε : |ε| ≤ 1)
    (hphase : ∀ k < n, ∀ s ∈ Set.uIcc (0 : ℝ) ε,
      euclideanPhaseSize
        (q ((k : ℝ) * ε + s), p ((k : ℝ) * ε + s)) ≤ B)
    (horizon : (n : ℝ) * |ε| ≤ T) :
    ∀ k ≤ n,
      absolutePhaseError
          (leapfrogN gradient ε k (q 0, p 0))
          (exactGridPhase q p ε k) ≤
        T *
            (|ε| * leapfrogExactAbsolutePhaseErrorCoefficient
              (ι := ι) β gradient B) *
          Real.exp (leapfrogNormStabilityRate β * T) := by
  intro k hk
  have hkcast : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
  have hkhor : (k : ℝ) * |ε| ≤ T :=
    (mul_le_mul_of_nonneg_right hkcast (abs_nonneg ε)).trans horizon
  have hphase' : ∀ j < k, ∀ s ∈ Set.uIcc (0 : ℝ) ε,
      euclideanPhaseSize
        (q ((j : ℝ) * ε + s), p ((j : ℝ) * ε + s)) ≤ B := by
    intro j hj
    exact hphase j (hj.trans_le hk)
  exact hreg.absolutePhaseError_leapfrogN_exactGrid_le
    hcurve hB hε hphase' hkhor

/-- Uniform position closeness follows immediately from the absolute phase
error bound. -/
theorem RegularPotential.dist_leapfrogN_exactGrid_fst_le_on_Iic
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q : ℝ → Position ι} {p : ℝ → Momentum ι}
    (hcurve : IsHamiltonianCurve gradient q p)
    {B : ℝ} (hB : 0 ≤ B) {ε T : ℝ} {n : ℕ} (hε : |ε| ≤ 1)
    (hphase : ∀ k < n, ∀ s ∈ Set.uIcc (0 : ℝ) ε,
      euclideanPhaseSize
        (q ((k : ℝ) * ε + s), p ((k : ℝ) * ε + s)) ≤ B)
    (horizon : (n : ℝ) * |ε| ≤ T) :
    ∀ k ≤ n,
      dist (leapfrogN gradient ε k (q 0, p 0)).1
          (exactGridPhase q p ε k).1 ≤
        T *
            (|ε| * leapfrogExactAbsolutePhaseErrorCoefficient
              (ι := ι) β gradient B) *
          Real.exp (leapfrogNormStabilityRate β * T) := by
  intro k hk
  exact (dist_fst_le_absolutePhaseError _ _).trans
    (hreg.absolutePhaseError_leapfrogN_exactGrid_le_on_Iic
      hcurve hB hε hphase horizon k hk)

/-- A uniform closed-ball buffer around the exact grid converts absolute
position closeness into numerical-grid containment. -/
theorem RegularPotential.leapfrogN_position_mem_of_exactGrid_buffer
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q : ℝ → Position ι} {p : ℝ → Momentum ι}
    (hcurve : IsHamiltonianCurve gradient q p)
    {B : ℝ} (hB : 0 ≤ B) {ε T buffer : ℝ} {n : ℕ}
    (hε : |ε| ≤ 1)
    (hphase : ∀ k < n, ∀ s ∈ Set.uIcc (0 : ℝ) ε,
      euclideanPhaseSize
        (q ((k : ℝ) * ε + s), p ((k : ℝ) * ε + s)) ≤ B)
    (horizon : (n : ℝ) * |ε| ≤ T)
    {S : Set (Position ι)}
    (hbuffer : ∀ k ≤ n,
      Metric.closedBall (exactGridPhase q p ε k).1 buffer ⊆ S)
    (herrorBudget :
      T *
          (|ε| * leapfrogExactAbsolutePhaseErrorCoefficient
            (ι := ι) β gradient B) *
        Real.exp (leapfrogNormStabilityRate β * T) ≤ buffer) :
    ∀ k ≤ n, (leapfrogN gradient ε k (q 0, p 0)).1 ∈ S := by
  intro k hk
  apply hbuffer k hk
  rw [Metric.mem_closedBall]
  exact (hreg.dist_leapfrogN_exactGrid_fst_le_on_Iic
    hcurve hB hε hphase horizon k hk).trans herrorBudget

/-- Uniform compact-family numerical containment. A compact thickened exact
envelope inside `S` supplies a common buffer, and one common sufficiently
small step-size neighborhood keeps every bounded-initial-phase leapfrog grid
inside `S` over the fixed horizon. -/
theorem RegularPotential.exists_uniform_leapfrogN_position_mem
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {K S : Set (Position ι)} (hK : IsCompact K)
    {M T : ℝ} (hM : 0 ≤ M)
    (henvelope : Metric.cthickening
        (exactFlowUniformEuclideanPositionDisplacementBound
          (ι := ι) β gradient M T) K ⊆ interior S) :
    ∃ buffer εbar : ℝ, buffer > 0 ∧ εbar > 0 ∧
      ∀ {q : ℝ → Position ι} {p : ℝ → Momentum ι},
        IsHamiltonianCurve gradient q p →
        q 0 ∈ K → euclideanPhaseSize (q 0, p 0) ≤ M →
        ∀ {ε : ℝ} {n : ℕ}, |ε| ≤ min 1 εbar →
          (n : ℝ) * |ε| ≤ T →
          ∀ k ≤ n, (leapfrogN gradient ε k (q 0, p 0)).1 ∈ S := by
  obtain ⟨buffer, hbuffer, hexactBuffer⟩ :=
    hreg.exists_pos_uniform_exactFlow_envelope_buffer hK hM henvelope
  let B := exactFlowUniformEuclideanPhaseBound
    (ι := ι) β gradient M T
  obtain ⟨εbar, hεbar, herror⟩ :=
    exists_pos_forall_leapfrogExactAbsoluteFixedHorizonErrorRate_lt
      (ι := ι) β gradient B T hbuffer
  refine ⟨buffer, εbar, hbuffer, hεbar, ?_⟩
  intro q p hcurve hq₀ hphase₀ ε n hε horizon
  have hεone : |ε| ≤ 1 := hε.trans (min_le_left _ _)
  have hεsmall : |ε| ≤ εbar := hε.trans (min_le_right _ _)
  have hB : 0 ≤ B :=
    exactFlowUniformEuclideanPhaseBound_nonneg β gradient hM
  have hphase := hreg.exactGrid_phaseSize_le_uniform_of_horizon
    hcurve hM hphase₀ horizon
  have hgridBuffer : ∀ k ≤ n,
      Metric.closedBall (exactGridPhase q p ε k).1 buffer ⊆ S := by
    intro k hk
    have hkcast : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
    have htime : |(k : ℝ) * ε| ≤ T := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
      exact (mul_le_mul_of_nonneg_right hkcast (abs_nonneg ε)).trans horizon
    simpa only [exactGridPhase] using
      hexactBuffer hcurve hq₀ hphase₀ htime
  have herrorBudget :
      T *
          (|ε| * leapfrogExactAbsolutePhaseErrorCoefficient
            (ι := ι) β gradient B) *
        Real.exp (leapfrogNormStabilityRate β * T) ≤ buffer := by
    exact (herror ε hεsmall).le
  exact hreg.leapfrogN_position_mem_of_exactGrid_buffer
    hcurve hB hεone hphase horizon hgridBuffer herrorBudget

/-- Scalar closure of the endpoint half-kick recurrence. Substituting the
closed new-position error into the phase inequality removes all occurrences
of the new error from the right-hand side. -/
theorem close_pairedPhaseError_recurrence
    {e c D η M E E' Eq Eq' Q₀ Q₁ : ℝ}
    (he : 0 ≤ e) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hEq : Eq ≤ E)
    (hEq' : Eq' ≤ (1 + e + c * D * M) * E + c * D * η * Q₀)
    (hphase : E' ≤
      (1 + e) * E + e * D *
        (η * Q₀ + M * Eq + (η * Q₁ + M * Eq') / 2)) :
    E' ≤
      (1 + e + e * D * M *
          (1 + (1 + e + c * D * M) / 2)) * E +
        e * D * η *
          (Q₀ + Q₁ / 2 + M * c * D * Q₀ / 2) := by
  have hMEq := mul_le_mul_of_nonneg_left hEq hM
  have hMEq' := mul_le_mul_of_nonneg_left hEq' hM
  calc
    E' ≤ (1 + e) * E + e * D *
        (η * Q₀ + M * Eq + (η * Q₁ + M * Eq') / 2) := hphase
    _ ≤ (1 + e) * E + e * D *
        (η * Q₀ + M * E +
          (η * Q₁ + M *
            ((1 + e + c * D * M) * E + c * D * η * Q₀)) / 2) := by
      gcongr
    _ = (1 + e + e * D * M *
          (1 + (1 + e + c * D * M) / 2)) * E +
        e * D * η *
          (Q₀ + Q₁ / 2 + M * c * D * Q₀ / 2) := by ring

/-- Small-step homogeneous rate for compact paired phase propagation. -/
noncomputable def compactPairedPhasePropagationStabilityRate
    (D M : ℝ) : ℝ :=
  1 + 2 * D * M + (D * M) ^ 2 / 4

theorem compactPairedPhasePropagationStabilityRate_nonneg
    {D M : ℝ} (hD : 0 ≤ D) (hM : 0 ≤ M) :
    0 ≤ compactPairedPhasePropagationStabilityRate D M := by
  unfold compactPairedPhasePropagationStabilityRate
  positivity

theorem compactPairedPhasePropagationFactor_le
    {e D M : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hD : 0 ≤ D) (hM : 0 ≤ M) :
    1 + e + e * D * M *
        (1 + (1 + e + e ^ 2 / 2 * D * M) / 2) ≤
      1 + compactPairedPhasePropagationStabilityRate D M * e := by
  have heSq : e ^ 2 ≤ e := by nlinarith
  have hDM : 0 ≤ D * M := mul_nonneg hD hM
  have hscaled := mul_le_mul_of_nonneg_right heSq hDM
  unfold compactPairedPhasePropagationStabilityRate
  nlinarith [sq_nonneg (D * M)]

theorem compactPairedPhasePropagationFactor_le_exp
    {e D M : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hD : 0 ≤ D) (hM : 0 ≤ M) :
    1 + e + e * D * M *
        (1 + (1 + e + e ^ 2 / 2 * D * M) / 2) ≤
      Real.exp (compactPairedPhasePropagationStabilityRate D M * e) := by
  apply (compactPairedPhasePropagationFactor_le he0 he1 hD hM).trans
  simpa [add_comm] using Real.add_one_le_exp
    (compactPairedPhasePropagationStabilityRate D M * e)

/-- Synchronized compact propagation: one radius and one Hessian bound control
both the endpoint position recurrence and the raw phase recurrence, which are
then closed into a single scalar phase inequality. -/
theorem RegularPotential.exists_compact_leapfrog_pairedPhaseClosed_bound
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ M ≥ 0,
      M ≤ ((β * (Fintype.card ι + 1 : NNReal) : NNReal) : ℝ) ∧
      ∀ {ε : ℝ} (_hε : |ε| ≤ 1)
        (z₁ z₂ w₁ w₂ : PhaseSpace ι),
        z₁.1 ∈ S → z₂.1 ∈ S → w₁.1 ∈ S → w₂.1 ∈ S →
        (leapfrog gradient ε z₁).1 ∈ S →
        (leapfrog gradient ε z₂).1 ∈ S →
        (leapfrog gradient ε w₁).1 ∈ S →
        (leapfrog gradient ε w₂).1 ∈ S →
        dist z₁.1 w₁.1 ≤ δ → dist z₂.1 w₂.1 ≤ δ →
        dist (leapfrog gradient ε z₁).1
          (leapfrog gradient ε w₁).1 ≤ δ →
        dist (leapfrog gradient ε z₂).1
          (leapfrog gradient ε w₂).1 ≤ δ →
        pairedPhaseError
            (leapfrog gradient ε z₁) (leapfrog gradient ε z₂)
            (leapfrog gradient ε w₁) (leapfrog gradient ε w₂) ≤
          (1 + |ε| + |ε| * ((Fintype.card ι : ℝ) + 1) * M *
              (1 + (1 + |ε| + ε ^ 2 / 2 *
                ((Fintype.card ι : ℝ) + 1) * M) / 2)) *
              pairedPhaseError z₁ z₂ w₁ w₂ +
            |ε| * ((Fintype.card ι : ℝ) + 1) * η *
              (euclideanNorm (w₁.1 - w₂.1) +
                euclideanNorm
                  ((leapfrog gradient ε w₁).1 -
                    (leapfrog gradient ε w₂).1) / 2 +
                M * (ε ^ 2 / 2) *
                  ((Fintype.card ι : ℝ) + 1) *
                  euclideanNorm (w₁.1 - w₂.1) / 2) := by
  obtain ⟨δP, hδP, MP, hMP, hMPglobal, hposition⟩ :=
    hreg.exists_compact_leapfrog_pairedRelativePositionError_bound
      hScompact hSconvex hη
  obtain ⟨δH, hδH, MH, hMH, hMHglobal, hphase⟩ :=
    hreg.exists_compact_leapfrog_pairedPhaseRaw_bound
      hScompact hSconvex hη
  let δ := min δP δH
  let M := max MP MH
  have hδ : 0 < δ := lt_min hδP hδH
  have hM : 0 ≤ M := hMP.trans (le_max_left _ _)
  have hMglobal : M ≤ ((β * (Fintype.card ι + 1 : NNReal) : NNReal) : ℝ) :=
    max_le hMPglobal hMHglobal
  refine ⟨δ, hδ, M, hM, hMglobal, ?_⟩
  intro ε hε z₁ z₂ w₁ w₂ hz₁ hz₂ hw₁ hw₂
    hLz₁ hLz₂ hLw₁ hLw₂ hz₁w₁ hz₂w₂ hLz₁w₁ hLz₂w₂
  let E := pairedPhaseError z₁ z₂ w₁ w₂
  let E' := pairedPhaseError
    (leapfrog gradient ε z₁) (leapfrog gradient ε z₂)
    (leapfrog gradient ε w₁) (leapfrog gradient ε w₂)
  let Eq := euclideanNorm ((z₁.1 - z₂.1) - (w₁.1 - w₂.1))
  let Eq' := euclideanNorm
    (((leapfrog gradient ε z₁).1 - (leapfrog gradient ε z₂).1) -
      ((leapfrog gradient ε w₁).1 - (leapfrog gradient ε w₂).1))
  let Q₀ := euclideanNorm (w₁.1 - w₂.1)
  let Q₁ := euclideanNorm
    ((leapfrog gradient ε w₁).1 - (leapfrog gradient ε w₂).1)
  let e := |ε|
  let c := ε ^ 2 / 2
  let D := (Fintype.card ι : ℝ) + 1
  have he : 0 ≤ e := abs_nonneg _
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hE : 0 ≤ E := pairedPhaseError_nonneg _ _ _ _
  have hEq0 : 0 ≤ Eq := euclideanNorm_nonneg _
  have hEq'0 : 0 ≤ Eq' := euclideanNorm_nonneg _
  have hQ₀ : 0 ≤ Q₀ := euclideanNorm_nonneg _
  have hQ₁ : 0 ≤ Q₁ := euclideanNorm_nonneg _
  have hMPle : MP ≤ M := le_max_left _ _
  have hMHle : MH ≤ M := le_max_right _ _
  have hposP := hposition (ε := ε) z₁ z₂ w₁ w₂
    hz₁ hz₂ hw₁ hw₂
    (hz₁w₁.trans (min_le_left _ _))
    (hz₂w₂.trans (min_le_left _ _))
  have hpos : Eq' ≤
      (1 + e + c * D * M) * E + c * D * η * Q₀ := by
    have hposP' : Eq' ≤
        (1 + e + c * D * MP) * E + c * D * η * Q₀ := by
      simpa only [Eq', e, c, D, E, Q₀, pairedPhaseError] using hposP
    apply hposP'.trans
    gcongr
  have hphaseH := hphase hε z₁ z₂ w₁ w₂
    hz₁ hz₂ hw₁ hw₂ hLz₁ hLz₂ hLw₁ hLw₂
    (hz₁w₁.trans (min_le_right _ _))
    (hz₂w₂.trans (min_le_right _ _))
    (hLz₁w₁.trans (min_le_right _ _))
    (hLz₂w₂.trans (min_le_right _ _))
  have hphase' : E' ≤
      (1 + e) * E + e * D *
        (η * Q₀ + M * Eq + (η * Q₁ + M * Eq') / 2) := by
    have hphaseH' : E' ≤
        (1 + e) * E + e * D *
          (η * Q₀ + MH * Eq + (η * Q₁ + MH * Eq') / 2) := by
      simpa only [E', E, e, D, Q₀, Q₁, Eq, Eq', pairedPhaseError]
        using hphaseH
    apply hphaseH'.trans
    gcongr
  have hEq : Eq ≤ E := by
    dsimp [Eq, E, pairedPhaseError]
    unfold euclideanPhaseSize
    exact le_add_of_nonneg_right (euclideanNorm_nonneg _)
  exact close_pairedPhaseError_recurrence he hD hM hEq hpos hphase'

/-- Uniform forcing coefficient after bounding both reference position
separations by `A * Q`. -/
noncomputable def compactPairedPhasePropagationForcingRate
    (D η M A ε : ℝ) : ℝ :=
  D * η * A * (3 / 2 + M * ε ^ 2 * D / 4)

theorem compactPairedPhasePropagationForcingRate_nonneg
    {D η M A ε : ℝ} (hD : 0 ≤ D) (hη : 0 ≤ η)
    (hM : 0 ≤ M) (hA : 0 ≤ A) :
    0 ≤ compactPairedPhasePropagationForcingRate D η M A ε := by
  unfold compactPairedPhasePropagationForcingRate
  positivity

/-- The complete coefficient multiplying initial position distance in the
compact paired fixed-horizon consistency theorem. -/
noncomputable def compactPairedFixedHorizonConsistencyRate
    (β : NNReal) (D T A η Mprop Mlocal ε : ℝ) : ℝ :=
  T *
      (compactPairedPhasePropagationForcingRate D η Mprop A ε +
        compactOneStepPhaseErrorPerTimeRate
            (ι := ι) β η Mlocal ε *
          exactFlowPhaseStabilityFactor (ι := ι) β T) *
    Real.exp
      (compactPairedPhasePropagationStabilityRate D Mprop * T)

theorem continuous_compactPairedFixedHorizonConsistencyRate
    (β : NNReal) (D T A η Mprop Mlocal : ℝ) :
    Continuous (compactPairedFixedHorizonConsistencyRate
      (ι := ι) β D T A η Mprop Mlocal) := by
  unfold compactPairedFixedHorizonConsistencyRate
  have hforcing : Continuous (fun ε ↦
      compactPairedPhasePropagationForcingRate D η Mprop A ε) := by
    unfold compactPairedPhasePropagationForcingRate
    fun_prop
  have hlocal := continuous_compactOneStepPhaseErrorPerTimeRate
    (ι := ι) β η Mlocal
  exact (continuous_const.mul
    (hforcing.add (hlocal.mul continuous_const))).mul continuous_const

@[simp]
theorem compactPairedFixedHorizonConsistencyRate_zero
    (β : NNReal) (D T A η Mprop Mlocal : ℝ) :
    compactPairedFixedHorizonConsistencyRate
        (ι := ι) β D T A η Mprop Mlocal 0 =
      T *
          (D * η * A * (3 / 2) +
            ((Fintype.card ι : ℝ) + 1 + 1 / 2) *
                (((Fintype.card ι : ℝ) + 1) * η) *
              exactFlowPhaseStabilityFactor (ι := ι) β T) *
        Real.exp
          (compactPairedPhasePropagationStabilityRate D Mprop * T) := by
  simp [compactPairedFixedHorizonConsistencyRate,
    compactPairedPhasePropagationForcingRate]

theorem compactPairedPhasePropagationStabilityRate_mono
    {D M N : ℝ} (hD : 0 ≤ D) (hM : 0 ≤ M) (hMN : M ≤ N) :
    compactPairedPhasePropagationStabilityRate D M ≤
      compactPairedPhasePropagationStabilityRate D N := by
  have hN : 0 ≤ N := hM.trans hMN
  have hmul : D * M ≤ D * N := mul_le_mul_of_nonneg_left hMN hD
  have hmul0 : 0 ≤ D * M := mul_nonneg hD hM
  have hmulN0 : 0 ≤ D * N := mul_nonneg hD hN
  have hsq : (D * M) ^ 2 ≤ (D * N) ^ 2 :=
    (sq_le_sq₀ hmul0 hmulN0).mpr hmul
  unfold compactPairedPhasePropagationStabilityRate
  linarith

/-- With the propagation Hessian bound fixed uniformly, every positive
relative-error allowance can be met by choosing the compact Hessian tolerance
and then the leapfrog step size. The local Hessian bound may still depend on
the chosen tolerance because its contribution vanishes as `ε → 0`. -/
theorem exists_eta_forall_compactPairedFixedHorizonConsistencyRate_lt
    (β : NNReal) {T A G ρ : ℝ}
    (hT : 0 ≤ T) (hA : 0 ≤ A)
    (hρ : 0 < ρ) :
    ∃ η > 0, ∀ {Mprop : ℝ}, 0 ≤ Mprop → Mprop ≤ G →
      ∀ Mlocal : ℝ, ∃ εbar > 0, ∀ ε, |ε| ≤ εbar →
        compactPairedFixedHorizonConsistencyRate
          (ι := ι) β ((Fintype.card ι : ℝ) + 1) T A η
            Mprop Mlocal ε < ρ := by
  let D : ℝ := (Fintype.card ι : ℝ) + 1
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let C : ℝ := (Fintype.card ι : ℝ) + 1 + 1 / 2
  let F : ℝ := exactFlowPhaseStabilityFactor (ι := ι) β T
  let W : ℝ := T *
      (D * A * (3 / 2) + C * D * F) *
        Real.exp (compactPairedPhasePropagationStabilityRate D G * T)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hF : 0 ≤ F := by
    dsimp [F]
    exact (exactFlowPhaseStabilityFactor_pos (ι := ι) β T).le
  have hW : 0 ≤ W := by dsimp [W]; positivity
  let η : ℝ := ρ / (2 * (W + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨η, hη, ?_⟩
  intro Mprop hMprop hMpropG Mlocal
  let f : ℝ → ℝ := fun ε ↦
    compactPairedFixedHorizonConsistencyRate
      (ι := ι) β D T A η Mprop Mlocal ε
  have hf : ContinuousAt f 0 :=
    (continuous_compactPairedFixedHorizonConsistencyRate
      (ι := ι) β D T A η Mprop Mlocal).continuousAt
  have hstab := compactPairedPhasePropagationStabilityRate_mono
    hD hMprop hMpropG
  have hexp : Real.exp
        (compactPairedPhasePropagationStabilityRate D Mprop * T) ≤
      Real.exp
        (compactPairedPhasePropagationStabilityRate D G * T) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hstab hT
  have hf0W : f 0 ≤ η * W := by
    rw [show f 0 = compactPairedFixedHorizonConsistencyRate
      (ι := ι) β D T A η Mprop Mlocal 0 by rfl]
    rw [compactPairedFixedHorizonConsistencyRate_zero]
    dsimp only [C, F, W]
    have hinner : 0 ≤
        D * η * A * (3 / 2) +
          ((Fintype.card ι : ℝ) + 1 + 1 / 2) *
            (((Fintype.card ι : ℝ) + 1) * η) *
              exactFlowPhaseStabilityFactor (ι := ι) β T := by
      positivity
    calc
      T *
            (D * η * A * (3 / 2) +
              ((Fintype.card ι : ℝ) + 1 + 1 / 2) *
                (((Fintype.card ι : ℝ) + 1) * η) *
                  exactFlowPhaseStabilityFactor (ι := ι) β T) *
          Real.exp
            (compactPairedPhasePropagationStabilityRate D Mprop * T) ≤
        T *
            (D * η * A * (3 / 2) +
              ((Fintype.card ι : ℝ) + 1 + 1 / 2) *
                (((Fintype.card ι : ℝ) + 1) * η) *
                  exactFlowPhaseStabilityFactor (ι := ι) β T) *
          Real.exp
            (compactPairedPhasePropagationStabilityRate D G * T) := by
              gcongr
      _ = η *
          (T *
            (D * A * (3 / 2) +
              ((Fintype.card ι : ℝ) + 1 + 1 / 2) * D *
                exactFlowPhaseStabilityFactor (ι := ι) β T) *
            Real.exp
              (compactPairedPhasePropagationStabilityRate D G * T)) := by
            ring
  have hηW : η * W < ρ := by
    have hden : 0 < 2 * (W + 1) := by positivity
    have heq : η * (W + 1) = ρ / 2 := by
      dsimp [η]
      field_simp
    have hη0 : 0 ≤ η := hη.le
    have : η * W ≤ η * (W + 1) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hη0
    linarith
  have hf0 : f 0 < ρ := hf0W.trans_lt hηW
  have hev : ∀ᶠ ε in nhds (0 : ℝ), f ε < ρ :=
    hf.eventually_lt continuousAt_const hf0
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro ε hε
  apply hball
  rw [Metric.mem_ball, Real.dist_eq]
  have : |ε| < r := hε.trans_lt (half_lt_self hr)
  simpa only [sub_zero] using this

/-- Exponential compact propagation with a constant relative forcing term.
This is the exact per-grid-step shape required by discrete Grönwall. -/
theorem RegularPotential.exists_compact_leapfrog_pairedPhaseExp_bound
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ M ≥ 0,
      M ≤ ((β * (Fintype.card ι + 1 : NNReal) : NNReal) : ℝ) ∧
      ∀ {ε A Q : ℝ} (_hε : |ε| ≤ 1) (_hA : 0 ≤ A) (_hQ : 0 ≤ Q)
        (z₁ z₂ w₁ w₂ : PhaseSpace ι),
        z₁.1 ∈ S → z₂.1 ∈ S → w₁.1 ∈ S → w₂.1 ∈ S →
        (leapfrog gradient ε z₁).1 ∈ S →
        (leapfrog gradient ε z₂).1 ∈ S →
        (leapfrog gradient ε w₁).1 ∈ S →
        (leapfrog gradient ε w₂).1 ∈ S →
        dist z₁.1 w₁.1 ≤ δ → dist z₂.1 w₂.1 ≤ δ →
        dist (leapfrog gradient ε z₁).1
          (leapfrog gradient ε w₁).1 ≤ δ →
        dist (leapfrog gradient ε z₂).1
          (leapfrog gradient ε w₂).1 ≤ δ →
        euclideanNorm (w₁.1 - w₂.1) ≤ A * Q →
        euclideanNorm
            ((leapfrog gradient ε w₁).1 -
              (leapfrog gradient ε w₂).1) ≤ A * Q →
        pairedPhaseError
            (leapfrog gradient ε z₁) (leapfrog gradient ε z₂)
            (leapfrog gradient ε w₁) (leapfrog gradient ε w₂) ≤
          Real.exp
              (compactPairedPhasePropagationStabilityRate
                ((Fintype.card ι : ℝ) + 1) M * |ε|) *
            pairedPhaseError z₁ z₂ w₁ w₂ +
          |ε| * compactPairedPhasePropagationForcingRate
              ((Fintype.card ι : ℝ) + 1) η M A ε * Q := by
  obtain ⟨δ, hδ, M, hM, hMglobal, hclosed⟩ :=
    hreg.exists_compact_leapfrog_pairedPhaseClosed_bound
      hScompact hSconvex hη
  refine ⟨δ, hδ, M, hM, hMglobal, ?_⟩
  intro ε A Q hε hA hQ z₁ z₂ w₁ w₂ hz₁ hz₂ hw₁ hw₂
    hLz₁ hLz₂ hLw₁ hLw₂ hz₁w₁ hz₂w₂ hLz₁w₁ hLz₂w₂ hQ₀ hQ₁
  have hraw := hclosed hε z₁ z₂ w₁ w₂ hz₁ hz₂ hw₁ hw₂
    hLz₁ hLz₂ hLw₁ hLw₂ hz₁w₁ hz₂w₂ hLz₁w₁ hLz₂w₂
  let e := |ε|
  let D := (Fintype.card ι : ℝ) + 1
  let E := pairedPhaseError z₁ z₂ w₁ w₂
  let Q₀ := euclideanNorm (w₁.1 - w₂.1)
  let Q₁ := euclideanNorm
    ((leapfrog gradient ε w₁).1 - (leapfrog gradient ε w₂).1)
  have he0 : 0 ≤ e := abs_nonneg _
  have he1 : e ≤ 1 := hε
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hE : 0 ≤ E := pairedPhaseError_nonneg _ _ _ _
  have hfactor := compactPairedPhasePropagationFactor_le_exp
    he0 he1 hD hM
  have hfactorE := mul_le_mul_of_nonneg_right hfactor hE
  rw [sq_abs] at hfactorE
  have hMQ₀ := mul_le_mul_of_nonneg_left hQ₀ hM
  have hforcing :
      e * D * η * (Q₀ + Q₁ / 2 + M * (ε ^ 2 / 2) * D * Q₀ / 2) ≤
        e * compactPairedPhasePropagationForcingRate D η M A ε * Q := by
    have hη0 : 0 ≤ η := hη.le
    have hAQ : 0 ≤ A * Q := mul_nonneg hA hQ
    have hQ₀0 : 0 ≤ Q₀ := by dsimp [Q₀]; exact euclideanNorm_nonneg _
    have hQ₁0 : 0 ≤ Q₁ := by dsimp [Q₁]; exact euclideanNorm_nonneg _
    have hthird : M * (ε ^ 2 / 2) * D * Q₀ / 2 ≤
        M * (ε ^ 2 / 2) * D * (A * Q) / 2 := by
      gcongr
    have hinner : Q₀ + Q₁ / 2 + M * (ε ^ 2 / 2) * D * Q₀ / 2 ≤
        A * Q + (A * Q) / 2 + M * (ε ^ 2 / 2) * D * (A * Q) / 2 :=
      add_le_add (add_le_add hQ₀ (div_le_div_of_nonneg_right hQ₁ (by norm_num)))
        hthird
    have hscale : 0 ≤ e * D * η := by positivity
    apply (mul_le_mul_of_nonneg_left hinner hscale).trans_eq
    unfold compactPairedPhasePropagationForcingRate
    ring
  dsimp [e, D, E, Q₀, Q₁] at hraw hfactorE hforcing ⊢
  exact hraw.trans (add_le_add hfactorE hforcing)

/-- Sequence-level compact propagation premise for the fixed-horizon grid
theorem. Every geometric obligation is stated pointwise at the grid index. -/
theorem RegularPotential.exists_compact_gridPropagation_bound
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ M ≥ 0,
      M ≤ ((β * (Fintype.card ι + 1 : NNReal) : NNReal) : ℝ) ∧
      ∀ {ε A Q : ℝ} {n : ℕ} (_hε : |ε| ≤ 1) (_hA : 0 ≤ A) (_hQ : 0 ≤ Q)
        (z₁ z₂ w₁ w₂ : ℕ → PhaseSpace ι),
        (∀ k < n, (z₁ k).1 ∈ S) →
        (∀ k < n, (z₂ k).1 ∈ S) →
        (∀ k < n, (w₁ k).1 ∈ S) →
        (∀ k < n, (w₂ k).1 ∈ S) →
        (∀ k < n, (leapfrog gradient ε (z₁ k)).1 ∈ S) →
        (∀ k < n, (leapfrog gradient ε (z₂ k)).1 ∈ S) →
        (∀ k < n, (leapfrog gradient ε (w₁ k)).1 ∈ S) →
        (∀ k < n, (leapfrog gradient ε (w₂ k)).1 ∈ S) →
        (∀ k < n, dist (z₁ k).1 (w₁ k).1 ≤ δ) →
        (∀ k < n, dist (z₂ k).1 (w₂ k).1 ≤ δ) →
        (∀ k < n, dist (leapfrog gradient ε (z₁ k)).1
          (leapfrog gradient ε (w₁ k)).1 ≤ δ) →
        (∀ k < n, dist (leapfrog gradient ε (z₂ k)).1
          (leapfrog gradient ε (w₂ k)).1 ≤ δ) →
        (∀ k < n, euclideanNorm ((w₁ k).1 - (w₂ k).1) ≤ A * Q) →
        (∀ k < n, euclideanNorm
          ((leapfrog gradient ε (w₁ k)).1 -
            (leapfrog gradient ε (w₂ k)).1) ≤ A * Q) →
        ∀ k < n,
          pairedPhaseError
              (leapfrog gradient ε (z₁ k))
              (leapfrog gradient ε (z₂ k))
              (leapfrog gradient ε (w₁ k))
              (leapfrog gradient ε (w₂ k)) ≤
            Real.exp
                (compactPairedPhasePropagationStabilityRate
                  ((Fintype.card ι : ℝ) + 1) M * |ε|) *
              pairedPhaseError (z₁ k) (z₂ k) (w₁ k) (w₂ k) +
            |ε| * compactPairedPhasePropagationForcingRate
                ((Fintype.card ι : ℝ) + 1) η M A ε * Q := by
  obtain ⟨δ, hδ, M, hM, hMglobal, hstep⟩ :=
    hreg.exists_compact_leapfrog_pairedPhaseExp_bound
      hScompact hSconvex hη
  refine ⟨δ, hδ, M, hM, hMglobal, ?_⟩
  intro ε A Q n hε hA hQ z₁ z₂ w₁ w₂ hz₁ hz₂ hw₁ hw₂
    hLz₁ hLz₂ hLw₁ hLw₂ hz₁w₁ hz₂w₂ hLz₁w₁ hLz₂w₂ hQ₀ hQ₁ k hk
  exact hstep hε hA hQ (z₁ k) (z₂ k) (w₁ k) (w₂ k)
    (hz₁ k hk) (hz₂ k hk) (hw₁ k hk) (hw₂ k hk)
    (hLz₁ k hk) (hLz₂ k hk) (hLw₁ k hk) (hLw₂ k hk)
    (hz₁w₁ k hk) (hz₂w₂ k hk) (hLz₁w₁ k hk) (hLz₂w₂ k hk)
    (hQ₀ k hk) (hQ₁ k hk)

/-- Fixed-horizon numerical-versus-reference bound with compact propagation
fully discharged. The remaining caller premises are the grid geometry and the
shifted exact-reference local truncation estimate. -/
theorem RegularPotential.exists_compact_pairedPhaseError_le_fixedHorizon
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ M ≥ 0,
      M ≤ ((β * (Fintype.card ι + 1 : NNReal) : NNReal) : ℝ) ∧
      ∀ {ε A Q r T : ℝ} {n : ℕ}
        (_hε : |ε| ≤ 1) (_hA : 0 ≤ A) (_hQ : 0 ≤ Q) (_hr : 0 ≤ r)
        (z₁ z₂ w₁ w₂ : ℕ → PhaseSpace ι),
        (∀ k < n, (z₁ k).1 ∈ S) →
        (∀ k < n, (z₂ k).1 ∈ S) →
        (∀ k < n, (w₁ k).1 ∈ S) →
        (∀ k < n, (w₂ k).1 ∈ S) →
        (∀ k < n, (leapfrog gradient ε (z₁ k)).1 ∈ S) →
        (∀ k < n, (leapfrog gradient ε (z₂ k)).1 ∈ S) →
        (∀ k < n, (leapfrog gradient ε (w₁ k)).1 ∈ S) →
        (∀ k < n, (leapfrog gradient ε (w₂ k)).1 ∈ S) →
        (∀ k < n, dist (z₁ k).1 (w₁ k).1 ≤ δ) →
        (∀ k < n, dist (z₂ k).1 (w₂ k).1 ≤ δ) →
        (∀ k < n, dist (leapfrog gradient ε (z₁ k)).1
          (leapfrog gradient ε (w₁ k)).1 ≤ δ) →
        (∀ k < n, dist (leapfrog gradient ε (z₂ k)).1
          (leapfrog gradient ε (w₂ k)).1 ≤ δ) →
        (∀ k < n, euclideanNorm ((w₁ k).1 - (w₂ k).1) ≤ A * Q) →
        (∀ k < n, euclideanNorm
          ((leapfrog gradient ε (w₁ k)).1 -
            (leapfrog gradient ε (w₂ k)).1) ≤ A * Q) →
        pairedPhaseError (z₁ 0) (z₂ 0) (w₁ 0) (w₂ 0) = 0 →
        (∀ k < n, z₁ (k + 1) = leapfrog gradient ε (z₁ k)) →
        (∀ k < n, z₂ (k + 1) = leapfrog gradient ε (z₂ k)) →
        (∀ k < n, pairedPhaseError
          (leapfrog gradient ε (w₁ k))
          (leapfrog gradient ε (w₂ k))
          (w₁ (k + 1)) (w₂ (k + 1)) ≤ |ε| * r * Q) →
        (n : ℝ) * |ε| ≤ T →
        pairedPhaseError (z₁ n) (z₂ n) (w₁ n) (w₂ n) ≤
          T *
              (compactPairedPhasePropagationForcingRate
                  ((Fintype.card ι : ℝ) + 1) η M A ε + r) *
            Real.exp
              (compactPairedPhasePropagationStabilityRate
                ((Fintype.card ι : ℝ) + 1) M * T) * Q := by
  obtain ⟨δ, hδ, M, hM, hMglobal, hprop⟩ :=
    hreg.exists_compact_gridPropagation_bound hScompact hSconvex hη
  refine ⟨δ, hδ, M, hM, hMglobal, ?_⟩
  intro ε A Q r T n hε hA hQ hr z₁ z₂ w₁ w₂
    hz₁ hz₂ hw₁ hw₂ hLz₁ hLz₂ hLw₁ hLw₂
    hz₁w₁ hz₂w₂ hLz₁w₁ hLz₂w₂ hQ₀ hQ₁ hinitial hnum₁ hnum₂
    hlocal horizon
  let D := (Fintype.card ι : ℝ) + 1
  let C := compactPairedPhasePropagationStabilityRate D M
  let s := compactPairedPhasePropagationForcingRate D η M A ε
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hC : 0 ≤ C :=
    compactPairedPhasePropagationStabilityRate_nonneg hD hM
  have hs : 0 ≤ s :=
    compactPairedPhasePropagationForcingRate_nonneg hD hη.le hM hA
  have hprop' := hprop hε hA hQ z₁ z₂ w₁ w₂
    hz₁ hz₂ hw₁ hw₂ hLz₁ hLz₂ hLw₁ hLw₂
    hz₁w₁ hz₂w₂ hLz₁w₁ hLz₂w₂ hQ₀ hQ₁
  exact pairedPhaseError_le_fixedHorizon_withPropagationForcing
    gradient z₁ z₂ w₁ w₂ hC hs hr hQ hinitial hnum₁ hnum₂
      hprop' hlocal horizon

/-- Per-unit-time relative phase consistency rate. If the paired
force-variation modulus `ω(ε)` tends to zero, this entire rate tends to zero. -/
noncomputable def leapfrogExactOneStepRelativePhaseErrorPerTimeRate
    (β : NNReal) (ω : ℝ → ℝ) (ε : ℝ) : ℝ :=
  (((Fintype.card ι : ℝ) + 1) ^ 2 * (β : ℝ) *
        exactFlowPositionStabilityFactor (ι := ι) β ε + (β : ℝ) / 2) * |ε| +
    ((Fintype.card ι : ℝ) + 1 + 1 / 2) * ω ε

theorem continuousAt_leapfrogExactOneStepRelativePhaseErrorPerTimeRate
    (β : NNReal) {ω : ℝ → ℝ} (hω : ContinuousAt ω 0) :
    ContinuousAt
      (leapfrogExactOneStepRelativePhaseErrorPerTimeRate (ι := ι) β ω) 0 := by
  unfold leapfrogExactOneStepRelativePhaseErrorPerTimeRate
  exact (((((continuousAt_const.mul continuousAt_const).mul
    (continuous_exactFlowPositionStabilityFactor β).continuousAt).add
      continuousAt_const).mul continuous_abs.continuousAt).add
        (continuousAt_const.mul hω))

@[simp]
theorem leapfrogExactOneStepRelativePhaseErrorPerTimeRate_zero
    (β : NNReal) {ω : ℝ → ℝ} (hω0 : ω 0 = 0) :
    leapfrogExactOneStepRelativePhaseErrorPerTimeRate (ι := ι) β ω 0 = 0 := by
  simp [leapfrogExactOneStepRelativePhaseErrorPerTimeRate, hω0]

theorem tendsto_leapfrogExactOneStepRelativePhaseErrorPerTimeRate_zero
    (β : NNReal) {ω : ℝ → ℝ} (hω : ContinuousAt ω 0) (hω0 : ω 0 = 0) :
    Filter.Tendsto
      (leapfrogExactOneStepRelativePhaseErrorPerTimeRate (ι := ι) β ω)
      (nhds 0) (nhds 0) := by
  have hc := continuousAt_leapfrogExactOneStepRelativePhaseErrorPerTimeRate
    (ι := ι) β hω
  change Filter.Tendsto
    (leapfrogExactOneStepRelativePhaseErrorPerTimeRate (ι := ι) β ω)
    (nhds 0)
    (nhds (leapfrogExactOneStepRelativePhaseErrorPerTimeRate
      (ι := ι) β ω 0)) at hc
  rw [leapfrogExactOneStepRelativePhaseErrorPerTimeRate_zero
    (ι := ι) β hω0] at hc
  exact hc

/-- The complete paired one-step phase error is step size times the vanishing
per-time rate, once supplied a step-dependent force-variation modulus. -/
theorem leapfrog_sharedMomentum_exactFlow_phaseSub_error_le_perTimeRate
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (hcurve₁ : IsHamiltonianCurve gradient q₁ p₁)
    (hcurve₂ : IsHamiltonianCurve gradient q₂ p₂)
    (hq₁ : q₁ 0 = q₁₀) (hq₂ : q₂ 0 = q₂₀)
    (hp₁ : p₁ 0 = p) (hp₂ : p₂ 0 = p)
    (ω : ℝ → ℝ) (ε : ℝ)
    (hforceExact : ∀ s ∈ Set.uIcc (0 : ℝ) ε,
      euclideanNorm
          ((gradient (q₁ s) - gradient (q₂ s)) -
            (gradient q₁₀ - gradient q₂₀)) ≤
        ω ε * euclideanNorm (q₁₀ - q₂₀))
    (hforceLeapfrog :
      euclideanNorm
          ((gradient (leapfrog gradient ε (q₁₀, p)).1 -
              gradient (leapfrog gradient ε (q₂₀, p)).1) -
            (gradient q₁₀ - gradient q₂₀)) ≤
        ω ε * euclideanNorm (q₁₀ - q₂₀)) :
    euclideanPhaseSize
        (((leapfrog gradient ε (q₁₀, p)).1 -
              (leapfrog gradient ε (q₂₀, p)).1) -
            (q₁ ε - q₂ ε),
          ((leapfrog gradient ε (q₁₀, p)).2 -
              (leapfrog gradient ε (q₂₀, p)).2) -
            (p₁ ε - p₂ ε)) ≤
      |ε| * leapfrogExactOneStepRelativePhaseErrorPerTimeRate
          (ι := ι) β ω ε * euclideanNorm (q₁₀ - q₂₀) := by
  have h := leapfrog_sharedMomentum_exactFlow_phaseSub_error_le
    hreg hcurve₁ hcurve₂ hq₁ hq₂ hp₁ hp₂ ε hforceExact hforceLeapfrog
  apply h.trans_eq
  unfold leapfrogExactOneStepRelativePositionErrorRate
  unfold leapfrogExactOneStepRelativeMomentumErrorRate
  unfold leapfrogExactOneStepRelativePhaseErrorPerTimeRate
  ring

/-- Quantitative one-step squared-distance bound for shared-momentum
leapfrog. -/
theorem leapfrog_sharedMomentum_squaredDistance_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient S α)
    (ε : ℝ) {q₁ q₂ : Position ι} (hq₁ : q₁ ∈ S) (hq₂ : q₂ ∈ S)
    (p : Momentum ι) :
    squaredEuclideanNorm
        ((leapfrog gradient ε (q₁, p)).1 -
          (leapfrog gradient ε (q₂, p)).1) ≤
      (1 - α * ε ^ 2 + (β : ℝ) ^ 2 * ε ^ 4 / 4) *
        squaredEuclideanNorm (q₁ - q₂) := by
  rw [leapfrog_sharedMomentum_position_sub]
  rw [squaredEuclideanNorm_sub_smul]
  have hmono := hconv.inner_gradient_sub_lower hq₁ hq₂
  have hlip := hreg.squaredEuclideanNorm_gradient_sub_le q₁ q₂
  have hε2 : 0 ≤ ε ^ 2 := sq_nonneg ε
  have hε4 : 0 ≤ ε ^ 4 / 4 := by positivity
  have hmono' := mul_le_mul_of_nonneg_left hmono hε2
  have hlip' := mul_le_mul_of_nonneg_left hlip hε4
  nlinarith

/-- The explicit one-step factor is strictly below one whenever the nonzero
step size satisfies `β² ε² < 4 α`. -/
theorem leapfrog_contractionFactor_lt_one
    {β : NNReal} {α ε : ℝ} (hε : ε ≠ 0)
    (hsmall : (β : ℝ) ^ 2 * ε ^ 2 < 4 * α) :
    1 - α * ε ^ 2 + (β : ℝ) ^ 2 * ε ^ 4 / 4 < 1 := by
  have hε2 : 0 < ε ^ 2 := sq_pos_of_ne_zero hε
  have hmul := mul_lt_mul_of_pos_right hsmall
    (div_pos hε2 (show (0 : ℝ) < 4 by norm_num))
  have hpow : ε ^ 4 = (ε ^ 2) * (ε ^ 2) := by ring
  rw [hpow]
  nlinarith

/-- A sufficiently small nonzero shared-momentum leapfrog step strictly
contracts the squared Euclidean distance between two distinct positions in
the locally strongly convex region. -/
theorem leapfrog_sharedMomentum_squaredDistance_lt
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient S α)
    {ε : ℝ} (hε : ε ≠ 0)
    (hsmall : (β : ℝ) ^ 2 * ε ^ 2 < 4 * α)
    {q₁ q₂ : Position ι} (hq₁ : q₁ ∈ S) (hq₂ : q₂ ∈ S)
    (hne : q₁ ≠ q₂) (p : Momentum ι) :
    squaredEuclideanNorm
        ((leapfrog gradient ε (q₁, p)).1 -
          (leapfrog gradient ε (q₂, p)).1) <
      squaredEuclideanNorm (q₁ - q₂) := by
  apply lt_of_le_of_lt
    (leapfrog_sharedMomentum_squaredDistance_le hreg hconv ε hq₁ hq₂ p)
  have hfactor := leapfrog_contractionFactor_lt_one hε hsmall
  have hdist : 0 < squaredEuclideanNorm (q₁ - q₂) :=
    squaredEuclideanNorm_pos (sub_ne_zero.mpr hne)
  exact (mul_lt_iff_lt_one_left hdist).mpr hfactor

/-- Comparing two approximate positions through two reference positions costs
at most the reference separation plus the two approximation errors.  This is
the geometric interface used to transfer exact-flow contraction to leapfrog
trajectories once numerical error bounds are available. -/
theorem euclideanNorm_separation_le_of_reference
    (x₁ x₂ y₁ y₂ : Position ι) :
    euclideanNorm (x₁ - x₂) ≤
      euclideanNorm (y₁ - y₂) +
        euclideanNorm (x₁ - y₁) + euclideanNorm (x₂ - y₂) := by
  have hdecomp :
      x₁ - x₂ = (x₁ - y₁) + (y₁ - y₂) + (y₂ - x₂) := by
    abel
  rw [hdecomp]
  calc
    euclideanNorm ((x₁ - y₁) + (y₁ - y₂) + (y₂ - x₂)) ≤
        euclideanNorm ((x₁ - y₁) + (y₁ - y₂)) +
          euclideanNorm (y₂ - x₂) :=
      euclideanNorm_add_le _ _
    _ ≤ (euclideanNorm (x₁ - y₁) + euclideanNorm (y₁ - y₂)) +
          euclideanNorm (y₂ - x₂) := by
      gcongr
      exact euclideanNorm_add_le _ _
    _ = euclideanNorm (y₁ - y₂) +
          euclideanNorm (x₁ - y₁) + euclideanNorm (x₂ - y₂) := by
      rw [show y₂ - x₂ = -(x₂ - y₂) by abel, euclideanNorm_neg]
      ring

/-- An exact-flow contraction factor `ρ` transfers to approximate positions
with an additive loss equal to the two numerical errors. -/
theorem euclideanNorm_contraction_le_of_reference
    {x₁ x₂ y₁ y₂ q₁ q₂ : Position ι} {ρ δ₁ δ₂ : ℝ}
    (href : euclideanNorm (y₁ - y₂) ≤ ρ * euclideanNorm (q₁ - q₂))
    (herr₁ : euclideanNorm (x₁ - y₁) ≤ δ₁)
    (herr₂ : euclideanNorm (x₂ - y₂) ≤ δ₂) :
    euclideanNorm (x₁ - x₂) ≤
      ρ * euclideanNorm (q₁ - q₂) + δ₁ + δ₂ := by
  apply le_trans (euclideanNorm_separation_le_of_reference x₁ x₂ y₁ y₂)
  linarith

/-- Relative numerical errors preserve a multiplicative contraction bound.
This is the form needed uniformly near the diagonal: unlike an absolute error
allowance, its right-hand side vanishes when the two initial positions agree. -/
theorem euclideanNorm_relativeContraction_le_of_reference
    {x₁ x₂ y₁ y₂ q₁ q₂ : Position ι} {ρ δ₁ δ₂ : ℝ}
    (href : euclideanNorm (y₁ - y₂) ≤ ρ * euclideanNorm (q₁ - q₂))
    (herr₁ : euclideanNorm (x₁ - y₁) ≤
      δ₁ * euclideanNorm (q₁ - q₂))
    (herr₂ : euclideanNorm (x₂ - y₂) ≤
      δ₂ * euclideanNorm (q₁ - q₂)) :
    euclideanNorm (x₁ - x₂) ≤
      (ρ + δ₁ + δ₂) * euclideanNorm (q₁ - q₂) := by
  apply le_trans (euclideanNorm_separation_le_of_reference x₁ x₂ y₁ y₂)
  linarith

/-- A relative error bound on the *difference* of two approximate positions
is enough to transfer exact-flow contraction.  This is sharper than bounding
the two numerical errors separately and has the correct zero error when the
paired initial states coincide. -/
theorem euclideanNorm_relativeContraction_le_of_displacementError
    {x₁ x₂ y₁ y₂ q₁ q₂ : Position ι} {ρ δ : ℝ}
    (href : euclideanNorm (y₁ - y₂) ≤ ρ * euclideanNorm (q₁ - q₂))
    (herror : euclideanNorm ((x₁ - x₂) - (y₁ - y₂)) ≤
      δ * euclideanNorm (q₁ - q₂)) :
    euclideanNorm (x₁ - x₂) ≤
      (ρ + δ) * euclideanNorm (q₁ - q₂) := by
  have hdecomp : x₁ - x₂ = ((x₁ - x₂) - (y₁ - y₂)) + (y₁ - y₂) := by
    abel
  rw [hdecomp]
  apply le_trans (euclideanNorm_add_le _ _)
  linarith

/-- A squared-distance contraction with factor `ρ²` implies the corresponding
Euclidean-norm contraction with factor `ρ`. -/
theorem euclideanNorm_le_mul_of_squaredEuclideanNorm_le_mul_sq
    {x q : Position ι} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : squaredEuclideanNorm x ≤
      ρ ^ 2 * squaredEuclideanNorm q) :
    euclideanNorm x ≤ ρ * euclideanNorm q := by
  apply (sq_le_sq₀ (euclideanNorm_nonneg x)
    (mul_nonneg hρ (euclideanNorm_nonneg q))).mp
  rw [euclideanNorm_sq, mul_pow, euclideanNorm_sq]
  exact h

/-- Exact squared contraction plus a relative displacement error gives the
aligned squared-cost factor `(ρ+δ)²` used by the Condition 1 budget. -/
theorem squaredEuclideanNorm_relativeContraction_le_of_displacementError
    {x₁ x₂ y₁ y₂ q₁ q₂ : Position ι} {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ)
    (href : squaredEuclideanNorm (y₁ - y₂) ≤
      ρ ^ 2 * squaredEuclideanNorm (q₁ - q₂))
    (herror : euclideanNorm ((x₁ - x₂) - (y₁ - y₂)) ≤
      δ * euclideanNorm (q₁ - q₂)) :
    squaredEuclideanNorm (x₁ - x₂) ≤
      (ρ + δ) ^ 2 * squaredEuclideanNorm (q₁ - q₂) := by
  have hrefNorm :=
    euclideanNorm_le_mul_of_squaredEuclideanNorm_le_mul_sq hρ href
  have hnorm := euclideanNorm_relativeContraction_le_of_displacementError
    hrefNorm herror
  have hfactor : 0 ≤ ρ + δ := add_nonneg hρ hδ
  have hsquare := (sq_le_sq₀ (euclideanNorm_nonneg (x₁ - x₂))
    (mul_nonneg hfactor (euclideanNorm_nonneg (q₁ - q₂)))).mpr hnorm
  rw [euclideanNorm_sq, mul_pow, euclideanNorm_sq] at hsquare
  exact hsquare

/-- Uniform compact-family fixed-horizon consistency for a shared-momentum
pair. All finite-grid containment, closeness, separation, and shifted local
truncation premises are generated internally. -/
theorem RegularPotential.exists_uniform_leapfrogN_pairedPhaseError_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {K S : Set (Position ι)} (hK : IsCompact K)
    (hScompact : IsCompact S) (hSconvex : Convex ℝ S)
    {M₀ T η : ℝ} (hM₀ : 0 ≤ M₀) (hη : 0 < η)
    (henvelope : Metric.cthickening
        (exactFlowUniformEuclideanPositionDisplacementBound
          (ι := ι) β gradient M₀ T) K ⊆ interior S) :
    ∃ εbar > 0, ∃ Mprop ≥ 0,
      Mprop ≤ ((β * (Fintype.card ι + 1 : NNReal) : NNReal) : ℝ) ∧
      ∃ Mlocal ≥ 0,
      ∀ {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι},
        IsHamiltonianCurve gradient q₁ p₁ →
        IsHamiltonianCurve gradient q₂ p₂ →
        q₁ 0 ∈ K → q₂ 0 ∈ K →
        euclideanPhaseSize (q₁ 0, p₁ 0) ≤ M₀ →
        euclideanPhaseSize (q₂ 0, p₂ 0) ≤ M₀ →
        p₁ 0 = p₂ 0 →
        ∀ {ε : ℝ} {n : ℕ}, |ε| ≤ εbar →
          (n : ℝ) * |ε| ≤ T →
          pairedPhaseError
              (leapfrogN gradient ε n (q₁ 0, p₁ 0))
              (leapfrogN gradient ε n (q₂ 0, p₂ 0))
              (exactGridPhase q₁ p₁ ε n)
              (exactGridPhase q₂ p₂ ε n) ≤
            T *
                (compactPairedPhasePropagationForcingRate
                    ((Fintype.card ι : ℝ) + 1) η Mprop
                    ((1 + leapfrogNormStabilityRate β) *
                      exactFlowPhaseStabilityFactor (ι := ι) β T) ε +
                  compactOneStepPhaseErrorPerTimeRate
                      (ι := ι) β η Mlocal ε *
                    exactFlowPhaseStabilityFactor (ι := ι) β T) *
              Real.exp
                (compactPairedPhasePropagationStabilityRate
                  ((Fintype.card ι : ℝ) + 1) Mprop * T) *
              euclideanNorm (q₁ 0 - q₂ 0) := by
  obtain ⟨δprop, hδprop, Mprop, hMprop, hMpropGlobal, hfixed⟩ :=
    hreg.exists_compact_pairedPhaseError_le_fixedHorizon
      hScompact hSconvex hη
  obtain ⟨δlocal, hδlocal, Mlocal, hMlocal, hlocal⟩ :=
    hreg.exists_compact_exactGrid_local_le_initialSeparation
      hScompact hSconvex hη
  obtain ⟨buffer, hbuffer, hexactBuffer⟩ :=
    hreg.exists_pos_uniform_exactFlow_envelope_buffer hK hM₀ henvelope
  obtain ⟨_numBuffer, εnum, _hnumBuffer, hεnum, hnumContain⟩ :=
    hreg.exists_uniform_leapfrogN_position_mem hK hM₀ henvelope
  let B := exactFlowUniformEuclideanPhaseBound
    (ι := ι) β gradient M₀ T
  have hB : 0 ≤ B :=
    exactFlowUniformEuclideanPhaseBound_nonneg β gradient hM₀
  obtain ⟨εdisp, hεdisp, hdisp⟩ :=
    hreg.exists_pos_forall_exactGrid_displacements_le hB
      (lt_min hbuffer hδlocal)
  let L := 1 + leapfrogNormStabilityRate β
  have hL : 0 < L := by
    dsimp [L]
    have := leapfrogNormStabilityRate_nonneg β
    linarith
  have hLone : 1 ≤ L := by
    dsimp [L]
    exact le_add_of_nonneg_right (leapfrogNormStabilityRate_nonneg β)
  have htarget : 0 < δprop / L := div_pos hδprop hL
  obtain ⟨εerr, hεerr, herr⟩ :=
    exists_pos_forall_leapfrogExactAbsoluteFixedHorizonErrorRate_lt
      (ι := ι) β gradient B T htarget
  let εbar := min 1 (min εnum (min εdisp εerr))
  have hεbar : 0 < εbar := by
    dsimp [εbar]
    exact lt_min (by norm_num)
      (lt_min hεnum (lt_min hεdisp hεerr))
  refine ⟨εbar, hεbar, Mprop, hMprop, hMpropGlobal,
    Mlocal, hMlocal, ?_⟩
  intro q₁ q₂ p₁ p₂ hcurve₁ hcurve₂ hq₁₀ hq₂₀ hz₁₀ hz₂₀
    hmomentum ε n hε horizon
  have hε1 : |ε| ≤ 1 := hε.trans (min_le_left _ _)
  have hεnum' : |ε| ≤ min 1 εnum := by
    exact le_min hε1
      (hε.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεdisp' : |ε| ≤ εdisp :=
    hε.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hεerr' : |ε| ≤ εerr :=
    hε.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hphase₁ := hreg.exactGrid_phaseSize_le_uniform_of_horizon
    hcurve₁ hM₀ hz₁₀ horizon
  have hphase₂ := hreg.exactGrid_phaseSize_le_uniform_of_horizon
    hcurve₂ hM₀ hz₂₀ horizon
  have hdisp₁ := hdisp hcurve₁ hεdisp' hphase₁
  have hdisp₂ := hdisp hcurve₂ hεdisp' hphase₂
  have hz₁mem := hnumContain hcurve₁ hq₁₀ hz₁₀ hεnum' horizon
  have hz₂mem := hnumContain hcurve₂ hq₂₀ hz₂₀ hεnum' horizon
  let z₁ : ℕ → PhaseSpace ι := fun k ↦
    leapfrogN gradient ε k (q₁ 0, p₁ 0)
  let z₂ : ℕ → PhaseSpace ι := fun k ↦
    leapfrogN gradient ε k (q₂ 0, p₂ 0)
  let w₁ : ℕ → PhaseSpace ι := fun k ↦ exactGridPhase q₁ p₁ ε k
  let w₂ : ℕ → PhaseSpace ι := fun k ↦ exactGridPhase q₂ p₂ ε k
  let A := (1 + leapfrogNormStabilityRate β) *
    exactFlowPhaseStabilityFactor (ι := ι) β T
  let Q := euclideanNorm (q₁ 0 - q₂ 0)
  let r := compactOneStepPhaseErrorPerTimeRate
    (ι := ι) β η Mlocal ε *
      exactFlowPhaseStabilityFactor (ι := ι) β T
  have hT : 0 ≤ T :=
    (mul_nonneg (Nat.cast_nonneg n) (abs_nonneg ε)).trans horizon
  have htimeGrid : ∀ k ≤ n, |(k : ℝ) * ε| ≤ T := by
    intro k hk
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
    have hk' : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
    exact (mul_le_mul_of_nonneg_right hk' (abs_nonneg ε)).trans horizon
  have htimeSegment : ∀ k < n, ∀ s ∈ Set.uIcc (0 : ℝ) ε,
      |(k : ℝ) * ε + s| ≤ T := by
    intro k hk s hs
    have hsabs : |s| ≤ |ε| := by
      simpa only [sub_zero] using Set.abs_sub_left_of_mem_uIcc hs
    have hk' : ((k + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hk)
    calc
      |(k : ℝ) * ε + s| ≤ |(k : ℝ) * ε| + |s| := abs_add_le _ _
      _ ≤ (k : ℝ) * |ε| + |ε| := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
        gcongr
      _ = ((k + 1 : ℕ) : ℝ) * |ε| := by
        rw [Nat.cast_add, Nat.cast_one]
        ring
      _ ≤ (n : ℝ) * |ε| := mul_le_mul_of_nonneg_right hk' (abs_nonneg ε)
      _ ≤ T := horizon
  have hw₁mem : ∀ k < n, (w₁ k).1 ∈ S := by
    intro k hk
    apply hexactBuffer hcurve₁ hq₁₀ hz₁₀ (htimeGrid k (Nat.le_of_lt hk))
    exact Metric.mem_closedBall_self hbuffer.le
  have hw₂mem : ∀ k < n, (w₂ k).1 ∈ S := by
    intro k hk
    apply hexactBuffer hcurve₂ hq₂₀ hz₂₀ (htimeGrid k (Nat.le_of_lt hk))
    exact Metric.mem_closedBall_self hbuffer.le
  have hseg₁mem : ∀ k < n, ∀ s ∈ Set.uIcc (0 : ℝ) ε,
      q₁ ((k : ℝ) * ε + s) ∈ S := by
    intro k hk s hs
    apply hexactBuffer hcurve₁ hq₁₀ hz₁₀ (htimeSegment k hk s hs)
    exact Metric.mem_closedBall_self hbuffer.le
  have hseg₂mem : ∀ k < n, ∀ s ∈ Set.uIcc (0 : ℝ) ε,
      q₂ ((k : ℝ) * ε + s) ∈ S := by
    intro k hk s hs
    apply hexactBuffer hcurve₂ hq₂₀ hz₂₀ (htimeSegment k hk s hs)
    exact Metric.mem_closedBall_self hbuffer.le
  have hLw₁mem : ∀ k < n, (leapfrog gradient ε (w₁ k)).1 ∈ S := by
    intro k hk
    apply hexactBuffer hcurve₁ hq₁₀ hz₁₀ (htimeGrid k (Nat.le_of_lt hk))
    rw [Metric.mem_closedBall]
    exact (dist_le_euclideanNorm_sub _ _).trans
      ((hdisp₁.2.2 k hk).trans (min_le_left _ _))
  have hLw₂mem : ∀ k < n, (leapfrog gradient ε (w₂ k)).1 ∈ S := by
    intro k hk
    apply hexactBuffer hcurve₂ hq₂₀ hz₂₀ (htimeGrid k (Nat.le_of_lt hk))
    rw [Metric.mem_closedBall]
    exact (dist_le_euclideanNorm_sub _ _).trans
      ((hdisp₂.2.2 k hk).trans (min_le_left _ _))
  have hR : leapfrogExactAbsoluteFixedHorizonErrorRate
      (ι := ι) β gradient B T ε < δprop / L := herr ε hεerr'
  have habs₁ := hreg.absolutePhaseError_leapfrogN_exactGrid_le_on_Iic
    hcurve₁ hB hε1 hphase₁ horizon
  have habs₂ := hreg.absolutePhaseError_leapfrogN_exactGrid_le_on_Iic
    hcurve₂ hB hε1 hphase₂ horizon
  have hclose₁ : ∀ k < n, dist (z₁ k).1 (w₁ k).1 ≤ δprop := by
    intro k hk
    exact (dist_fst_le_absolutePhaseError _ _).trans
      ((habs₁ k (Nat.le_of_lt hk)).trans
        ((hR.le).trans (div_le_self hδprop.le hLone)))
  have hclose₂ : ∀ k < n, dist (z₂ k).1 (w₂ k).1 ≤ δprop := by
    intro k hk
    exact (dist_fst_le_absolutePhaseError _ _).trans
      ((habs₂ k (Nat.le_of_lt hk)).trans
        ((hR.le).trans (div_le_self hδprop.le hLone)))
  have hLclose₁ : ∀ k < n,
      dist (leapfrog gradient ε (z₁ k)).1
        (leapfrog gradient ε (w₁ k)).1 ≤ δprop := by
    intro k hk
    apply (dist_le_euclideanNorm_sub _ _).trans
    have hfst : euclideanNorm
        ((leapfrog gradient ε (z₁ k)).1 -
          (leapfrog gradient ε (w₁ k)).1) ≤
        euclideanNorm
            ((leapfrog gradient ε (z₁ k)).1 -
              (leapfrog gradient ε (w₁ k)).1) +
          euclideanNorm
            ((leapfrog gradient ε (z₁ k)).2 -
              (leapfrog gradient ε (w₁ k)).2) :=
      le_add_of_nonneg_right (euclideanNorm_nonneg _)
    apply hfst.trans
    have hs := leapfrog_euclideanNorm_phaseSub_le hreg hε1 (z₁ k) (w₁ k)
    apply hs.trans
    have hold := habs₁ k (Nat.le_of_lt hk)
    have hold' : absolutePhaseError (z₁ k) (w₁ k) ≤
        leapfrogExactAbsoluteFixedHorizonErrorRate
          (ι := ι) β gradient B T ε := by
      simpa only [z₁, w₁, leapfrogExactAbsoluteFixedHorizonErrorRate] using hold
    have hcoef : 1 + leapfrogNormStabilityRate β * |ε| ≤ L := by
      dsimp [L]
      have := mul_le_mul_of_nonneg_left hε1
        (leapfrogNormStabilityRate_nonneg β)
      linarith
    calc
      (1 + leapfrogNormStabilityRate β * |ε|) *
          absolutePhaseError (z₁ k) (w₁ k) ≤
        L * leapfrogExactAbsoluteFixedHorizonErrorRate
          (ι := ι) β gradient B T ε :=
        (mul_le_mul_of_nonneg_right hcoef
          (absolutePhaseError_nonneg _ _)).trans
          (mul_le_mul_of_nonneg_left hold' hL.le)
      _ ≤ L * (δprop / L) := mul_le_mul_of_nonneg_left hR.le hL.le
      _ = δprop := by field_simp
  have hLclose₂ : ∀ k < n,
      dist (leapfrog gradient ε (z₂ k)).1
        (leapfrog gradient ε (w₂ k)).1 ≤ δprop := by
    intro k hk
    apply (dist_le_euclideanNorm_sub _ _).trans
    have hfst : euclideanNorm
        ((leapfrog gradient ε (z₂ k)).1 -
          (leapfrog gradient ε (w₂ k)).1) ≤
        euclideanNorm
            ((leapfrog gradient ε (z₂ k)).1 -
              (leapfrog gradient ε (w₂ k)).1) +
          euclideanNorm
            ((leapfrog gradient ε (z₂ k)).2 -
              (leapfrog gradient ε (w₂ k)).2) :=
      le_add_of_nonneg_right (euclideanNorm_nonneg _)
    apply hfst.trans
    have hs := leapfrog_euclideanNorm_phaseSub_le hreg hε1 (z₂ k) (w₂ k)
    apply hs.trans
    have hold := habs₂ k (Nat.le_of_lt hk)
    have hold' : absolutePhaseError (z₂ k) (w₂ k) ≤
        leapfrogExactAbsoluteFixedHorizonErrorRate
          (ι := ι) β gradient B T ε := by
      simpa only [z₂, w₂, leapfrogExactAbsoluteFixedHorizonErrorRate] using hold
    have hcoef : 1 + leapfrogNormStabilityRate β * |ε| ≤ L := by
      dsimp [L]
      have := mul_le_mul_of_nonneg_left hε1
        (leapfrogNormStabilityRate_nonneg β)
      linarith
    calc
      (1 + leapfrogNormStabilityRate β * |ε|) *
          absolutePhaseError (z₂ k) (w₂ k) ≤
        L * leapfrogExactAbsoluteFixedHorizonErrorRate
          (ι := ι) β gradient B T ε :=
        (mul_le_mul_of_nonneg_right hcoef
          (absolutePhaseError_nonneg _ _)).trans
          (mul_le_mul_of_nonneg_left hold' hL.le)
      _ ≤ L * (δprop / L) := mul_le_mul_of_nonneg_left hR.le hL.le
      _ = δprop := by field_simp
  obtain ⟨hQ₀, hQ₁⟩ := hreg.exactGrid_sharedMomentum_positionBounds
    hcurve₁ hcurve₂ hmomentum hε1 horizon
  have hlocal' := hlocal hcurve₁ hcurve₂ hmomentum horizon
    hw₁mem hw₂mem hseg₁mem hseg₂mem
    (fun k hk s hs ↦ (hdisp₁.2.1 k hk s hs).trans (min_le_right _ _))
    (fun k hk s hs ↦ (hdisp₂.2.1 k hk s hs).trans (min_le_right _ _))
    hLw₁mem hLw₂mem
    (fun k hk ↦ (hdisp₁.2.2 k hk).trans (min_le_right _ _))
    (fun k hk ↦ (hdisp₂.2.2 k hk).trans (min_le_right _ _))
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (by linarith [leapfrogNormStabilityRate_nonneg β])
      (exactFlowPhaseStabilityFactor_pos (ι := ι) β T).le
  have hQ : 0 ≤ Q := by dsimp [Q]; exact euclideanNorm_nonneg _
  have hr : 0 ≤ r := by
    dsimp [r]
    exact mul_nonneg
      (compactOneStepPhaseErrorPerTimeRate_nonneg β hη.le hMlocal)
      (exactFlowPhaseStabilityFactor_pos (ι := ι) β T).le
  have hinitial : pairedPhaseError (z₁ 0) (z₂ 0) (w₁ 0) (w₂ 0) = 0 := by
    simp [z₁, z₂, w₁, w₂, leapfrogN, pairedPhaseError,
      euclideanPhaseSize]
  have hnum₁ : ∀ k < n, z₁ (k + 1) = leapfrog gradient ε (z₁ k) := by
    intro k hk
    simp [z₁, leapfrogN, Function.iterate_succ_apply']
  have hnum₂ : ∀ k < n, z₂ (k + 1) = leapfrog gradient ε (z₂ k) := by
    intro k hk
    simp [z₂, leapfrogN, Function.iterate_succ_apply']
  have hz₁S : ∀ k < n, (z₁ k).1 ∈ S := fun k hk ↦ hz₁mem k (Nat.le_of_lt hk)
  have hz₂S : ∀ k < n, (z₂ k).1 ∈ S := fun k hk ↦ hz₂mem k (Nat.le_of_lt hk)
  have hLz₁S : ∀ k < n, (leapfrog gradient ε (z₁ k)).1 ∈ S := by
    intro k hk
    rw [← hnum₁ k hk]
    exact hz₁mem (k + 1) (Nat.succ_le_iff.mpr hk)
  have hLz₂S : ∀ k < n, (leapfrog gradient ε (z₂ k)).1 ∈ S := by
    intro k hk
    rw [← hnum₂ k hk]
    exact hz₂mem (k + 1) (Nat.succ_le_iff.mpr hk)
  exact hfixed hε1 hA hQ hr z₁ z₂ w₁ w₂
    hz₁S hz₂S hw₁mem hw₂mem hLz₁S hLz₂S hLw₁mem hLw₂mem
    hclose₁ hclose₂ hLclose₁ hLclose₂ hQ₀ hQ₁ hinitial
    hnum₁ hnum₂ hlocal' horizon

/-- The compact-family paired leapfrog error can be made smaller than any
prescribed positive multiple of the initial position distance. This closes
the `η`-then-`ε` parameter choice required for transferring exact contraction
to the numerical integrator. -/
theorem RegularPotential.exists_uniform_leapfrogN_pairedPhaseError_le_mul
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {K S : Set (Position ι)} (hK : IsCompact K)
    (hScompact : IsCompact S) (hSconvex : Convex ℝ S)
    {M₀ T ρ : ℝ} (hM₀ : 0 ≤ M₀) (hT : 0 ≤ T) (hρ : 0 < ρ)
    (henvelope : Metric.cthickening
        (exactFlowUniformEuclideanPositionDisplacementBound
          (ι := ι) β gradient M₀ T) K ⊆ interior S) :
    ∃ εbar > 0,
      ∀ {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι},
        IsHamiltonianCurve gradient q₁ p₁ →
        IsHamiltonianCurve gradient q₂ p₂ →
        q₁ 0 ∈ K → q₂ 0 ∈ K →
        euclideanPhaseSize (q₁ 0, p₁ 0) ≤ M₀ →
        euclideanPhaseSize (q₂ 0, p₂ 0) ≤ M₀ →
        p₁ 0 = p₂ 0 →
        ∀ {ε : ℝ} {n : ℕ}, |ε| ≤ εbar →
          (n : ℝ) * |ε| ≤ T →
          pairedPhaseError
              (leapfrogN gradient ε n (q₁ 0, p₁ 0))
              (leapfrogN gradient ε n (q₂ 0, p₂ 0))
              (exactGridPhase q₁ p₁ ε n)
              (exactGridPhase q₂ p₂ ε n) ≤
            ρ * euclideanNorm (q₁ 0 - q₂ 0) := by
  let D : ℝ := (Fintype.card ι : ℝ) + 1
  let A : ℝ := (1 + leapfrogNormStabilityRate β) *
    exactFlowPhaseStabilityFactor (ι := ι) β T
  let G : ℝ := ((β * (Fintype.card ι + 1 : NNReal) : NNReal) : ℝ)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (by linarith [leapfrogNormStabilityRate_nonneg β])
      (exactFlowPhaseStabilityFactor_pos (ι := ι) β T).le
  obtain ⟨η, hη, hselect⟩ :=
    exists_eta_forall_compactPairedFixedHorizonConsistencyRate_lt
      (ι := ι) β hT hA hρ
  obtain ⟨εgeom, hεgeom, Mprop, hMprop, hMpropG,
      Mlocal, hMlocal, hmain⟩ :=
    hreg.exists_uniform_leapfrogN_pairedPhaseError_le
      hK hScompact hSconvex hM₀ hη henvelope
  obtain ⟨εrate, hεrate, hrate⟩ :=
    hselect hMprop hMpropG Mlocal
  let εbar := min εgeom εrate
  have hεbar : 0 < εbar := lt_min hεgeom hεrate
  refine ⟨εbar, hεbar, ?_⟩
  intro q₁ q₂ p₁ p₂ hcurve₁ hcurve₂ hq₁ hq₂ hz₁ hz₂
    hmomentum ε n hε horizon
  have hεgeom' : |ε| ≤ εgeom := hε.trans (min_le_left _ _)
  have hεrate' : |ε| ≤ εrate := hε.trans (min_le_right _ _)
  have hraw := hmain hcurve₁ hcurve₂ hq₁ hq₂ hz₁ hz₂
    hmomentum hεgeom' horizon
  have hrate' := hrate ε hεrate'
  have hQ : 0 ≤ euclideanNorm (q₁ 0 - q₂ 0) := euclideanNorm_nonneg _
  have hraw' : pairedPhaseError
        (leapfrogN gradient ε n (q₁ 0, p₁ 0))
        (leapfrogN gradient ε n (q₂ 0, p₂ 0))
        (exactGridPhase q₁ p₁ ε n)
        (exactGridPhase q₂ p₂ ε n) ≤
      compactPairedFixedHorizonConsistencyRate
          (ι := ι) β D T A η Mprop Mlocal ε *
        euclideanNorm (q₁ 0 - q₂ 0) := by
    simpa only [D, A, compactPairedFixedHorizonConsistencyRate] using hraw
  exact hraw'.trans (mul_le_mul_of_nonneg_right hrate'.le hQ)

/-- An exact endpoint contraction plus paired leapfrog consistency transfers
to the numerical endpoint with the additive norm factor `exactRate + errorRate`.
This is the deterministic contraction-closing step used by Condition 1. -/
theorem squaredEuclideanNorm_leapfrogN_le_of_exactGrid_and_pairedError
    {gradient : Position ι → Position ι}
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    {ε : ℝ} {n : ℕ} {exactRate errorRate : ℝ}
    (hexactRate : 0 ≤ exactRate) (herrorRate : 0 ≤ errorRate)
    (hexact : squaredEuclideanNorm
        ((exactGridPhase q₁ p₁ ε n).1 -
          (exactGridPhase q₂ p₂ ε n).1) ≤
      exactRate ^ 2 * squaredEuclideanNorm (q₁ 0 - q₂ 0))
    (hpaired : pairedPhaseError
        (leapfrogN gradient ε n (q₁ 0, p₁ 0))
        (leapfrogN gradient ε n (q₂ 0, p₂ 0))
        (exactGridPhase q₁ p₁ ε n)
        (exactGridPhase q₂ p₂ ε n) ≤
      errorRate * euclideanNorm (q₁ 0 - q₂ 0)) :
    squaredEuclideanNorm
        ((leapfrogN gradient ε n (q₁ 0, p₁ 0)).1 -
          (leapfrogN gradient ε n (q₂ 0, p₂ 0)).1) ≤
      (exactRate + errorRate) ^ 2 *
        squaredEuclideanNorm (q₁ 0 - q₂ 0) := by
  let x₁ := (leapfrogN gradient ε n (q₁ 0, p₁ 0)).1
  let x₂ := (leapfrogN gradient ε n (q₂ 0, p₂ 0)).1
  let y₁ := (exactGridPhase q₁ p₁ ε n).1
  let y₂ := (exactGridPhase q₂ p₂ ε n).1
  have hposition : euclideanNorm ((x₁ - x₂) - (y₁ - y₂)) ≤
      errorRate * euclideanNorm (q₁ 0 - q₂ 0) := by
    apply (euclideanNorm_fst_le_phaseSize
      ((x₁ - x₂) - (y₁ - y₂),
        ((leapfrogN gradient ε n (q₁ 0, p₁ 0)).2 -
            (leapfrogN gradient ε n (q₂ 0, p₂ 0)).2) -
          ((exactGridPhase q₁ p₁ ε n).2 -
            (exactGridPhase q₂ p₂ ε n).2))).trans
    simpa only [x₁, x₂, y₁, y₂, pairedPhaseError] using hpaired
  exact squaredEuclideanNorm_relativeContraction_le_of_displacementError
    hexactRate herrorRate (by simpa only [y₁, y₂] using hexact)
      (by simpa only [x₁, x₂, y₁, y₂] using hposition)

/-- Uniform numerical contraction transfer on a compact family. Once an
exact-grid endpoint has a common squared contraction factor, sufficiently
small leapfrog steps have factor `(exactRate + errorRate)²`. -/
theorem RegularPotential.exists_uniform_leapfrogN_squaredContraction
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {K S : Set (Position ι)} (hK : IsCompact K)
    (hScompact : IsCompact S) (hSconvex : Convex ℝ S)
    {M₀ T exactRate errorRate : ℝ}
    (hM₀ : 0 ≤ M₀) (hT : 0 ≤ T)
    (hexactRate : 0 ≤ exactRate) (herrorRate : 0 < errorRate)
    (henvelope : Metric.cthickening
        (exactFlowUniformEuclideanPositionDisplacementBound
          (ι := ι) β gradient M₀ T) K ⊆ interior S)
    (hexact : ∀ {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι},
      IsHamiltonianCurve gradient q₁ p₁ →
      IsHamiltonianCurve gradient q₂ p₂ →
      q₁ 0 ∈ K → q₂ 0 ∈ K →
      euclideanPhaseSize (q₁ 0, p₁ 0) ≤ M₀ →
      euclideanPhaseSize (q₂ 0, p₂ 0) ≤ M₀ →
      p₁ 0 = p₂ 0 →
      ∀ {ε : ℝ} {n : ℕ}, (n : ℝ) * |ε| ≤ T →
        squaredEuclideanNorm
            ((exactGridPhase q₁ p₁ ε n).1 -
              (exactGridPhase q₂ p₂ ε n).1) ≤
          exactRate ^ 2 * squaredEuclideanNorm (q₁ 0 - q₂ 0)) :
    ∃ εbar > 0,
      ∀ {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι},
        IsHamiltonianCurve gradient q₁ p₁ →
        IsHamiltonianCurve gradient q₂ p₂ →
        q₁ 0 ∈ K → q₂ 0 ∈ K →
        euclideanPhaseSize (q₁ 0, p₁ 0) ≤ M₀ →
        euclideanPhaseSize (q₂ 0, p₂ 0) ≤ M₀ →
        p₁ 0 = p₂ 0 →
        ∀ {ε : ℝ} {n : ℕ}, |ε| ≤ εbar →
          (n : ℝ) * |ε| ≤ T →
          squaredEuclideanNorm
              ((leapfrogN gradient ε n (q₁ 0, p₁ 0)).1 -
                (leapfrogN gradient ε n (q₂ 0, p₂ 0)).1) ≤
            (exactRate + errorRate) ^ 2 *
              squaredEuclideanNorm (q₁ 0 - q₂ 0) := by
  obtain ⟨εbar, hεbar, hpaired⟩ :=
    hreg.exists_uniform_leapfrogN_pairedPhaseError_le_mul
      hK hScompact hSconvex hM₀ hT herrorRate henvelope
  refine ⟨εbar, hεbar, ?_⟩
  intro q₁ q₂ p₁ p₂ hcurve₁ hcurve₂ hq₁ hq₂ hz₁ hz₂
    hmomentum ε n hε horizon
  exact squaredEuclideanNorm_leapfrogN_le_of_exactGrid_and_pairedError
    hexactRate herrorRate.le
    (hexact hcurve₁ hcurve₂ hq₁ hq₂ hz₁ hz₂ hmomentum horizon)
    (hpaired hcurve₁ hcurve₂ hq₁ hq₂ hz₁ hz₂ hmomentum hε horizon)

end McmcLean.Hamiltonian
