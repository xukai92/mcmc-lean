import Mcmc.Relativistic.BoundedScalarSolver

/-!
# Reusable scalar GR-Hamiltonian slice bounds

The implicit generalized-leapfrog contraction argument only compares the
position derivative at fixed position and the momentum derivative at fixed
momentum.  Consequently every position-only force term cancels.  This module
packages the remaining calculation for an arbitrary positive scalar factor.
-/

namespace Mcmc.Relativistic

open Mcmc.Hamiltonian

/-- Scalar-coordinate position callback for a complete one-dimensional
Hamiltonian. `drift` contains all position-only terms, while `scaleDerivative`
is the derivative of the positive inverse-square-root metric factor. -/
noncomputable def scalarGRPositionCallback
    (drift scale scaleDerivative : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  drift z.1 + scaleDerivative z.1 / scale z.1 *
    scalarPositionProfile (scale z.1 * z.2)

/-- Scalar-coordinate momentum callback for the same factor. -/
noncomputable def scalarGRMomentumCallback
    (scale : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  scaledVelocityProfile z.2 (scale z.1)

/-- Scalar-coordinate complete Hamiltonian after collecting all
position-only terms into `base`. -/
noncomputable def scalarGRHamiltonianReal
    (base scale : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  base z.1 + Real.sqrt (1 + (scale z.1 * z.2) ^ 2)

theorem deriv_scalarGRHamiltonianReal_fst
    (base scale : ℝ → ℝ) (hbase : Differentiable ℝ base)
    (hscale : Differentiable ℝ scale) (hscalePos : ∀ x, 0 < scale x)
    (q p : ℝ) :
    deriv (fun x => scalarGRHamiltonianReal base scale (x, p)) q =
      scalarGRPositionCallback (deriv base) scale (deriv scale) (q, p) := by
  have hinner : HasDerivAt (fun x => scale x * p) (deriv scale q * p) q :=
    (hscale q).hasDerivAt.mul_const p
  have hrad : 1 + (scale q * p) ^ 2 ≠ 0 := by positivity
  have hroot := ((hinner.pow 2).const_add 1).sqrt hrad
  have htotal := (hbase q).hasDerivAt.add hroot
  change deriv (base + fun x =>
    Real.sqrt (1 + (scale x * p) ^ 2)) q = _
  have heq : (base + fun y =>
      Real.sqrt (1 + ((fun x => scale x * p) ^ 2) y)) =
      (base + fun x => Real.sqrt (1 + (scale x * p) ^ 2)) := by
    funext x
    rfl
  rw [← heq]
  rw [htotal.deriv]
  simp only [Pi.pow_apply]
  unfold scalarGRPositionCallback
  unfold scalarPositionProfile scalarRelativisticProfile
  have hs : scale q ≠ 0 := (hscalePos q).ne'
  have hsqrt : Real.sqrt (1 + (scale q * p) ^ 2) ≠ 0 := by positivity
  field_simp [hs, hsqrt]
  ring

theorem deriv_scalarGRHamiltonianReal_snd
    (base scale : ℝ → ℝ) (q p : ℝ) :
    deriv (fun y => scalarGRHamiltonianReal base scale (q, y)) p =
      scalarGRMomentumCallback scale (q, p) := by
  have hinner : HasDerivAt (fun y => scale q * y) (scale q) p := by
    simpa using (hasDerivAt_id p).const_mul (scale q)
  have hrad : 1 + (scale q * p) ^ 2 ≠ 0 := by positivity
  have hroot := ((hinner.pow 2).const_add 1).sqrt hrad
  have htotal := (hasDerivAt_const p (base q)).add hroot
  change deriv ((fun _ => base q) + fun y =>
    Real.sqrt (1 + (scale q * y) ^ 2)) p = _
  have heq : ((fun _ => base q) + fun y =>
      Real.sqrt (1 + ((fun y => scale q * y) ^ 2) y)) =
      ((fun _ => base q) + fun y =>
        Real.sqrt (1 + (scale q * y) ^ 2)) := by
    funext y
    rfl
  rw [← heq]
  rw [htotal.deriv]
  simp only [Pi.pow_apply]
  unfold scalarGRMomentumCallback scaledVelocityProfile
    scalarVelocityProfile scalarRelativisticProfile
  have hsqrt : Real.sqrt (1 + (scale q * p) ^ 2) ≠ 0 := by positivity
  field_simp [hsqrt]
  ring

/-- At fixed position, the complete position callback is Lipschitz in
momentum.  Position-only force terms disappear exactly. -/
theorem scalarGRPositionCallback_lipschitz_snd
    (drift scale scaleDerivative : ℝ → ℝ) (q : ℝ) (D : NNReal)
    (hscale : 0 < scale q) (hderiv : |scaleDerivative q| ≤ D) :
    LipschitzWith (3 * D) (fun p =>
      scalarGRPositionCallback drift scale scaleDerivative (q, p)) := by
  apply LipschitzWith.of_dist_le_mul
  intro p r
  rw [Real.dist_eq]
  unfold scalarGRPositionCallback
  rw [add_sub_add_left_eq_sub]
  have hprofile := scalarPositionProfile_lipschitz.dist_le_mul
    (scale q * p) (scale q * r)
  calc
    _ = |scaleDerivative q / scale q| *
        |scalarPositionProfile (scale q * p) -
          scalarPositionProfile (scale q * r)| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ |scaleDerivative q / scale q| *
        (3 * |scale q * p - scale q * r|) := by
      gcongr
      simpa [Real.dist_eq] using hprofile
    _ = 3 * |scaleDerivative q| * |p - r| := by
      rw [abs_div, abs_of_pos hscale, ← mul_sub, abs_mul,
        abs_of_pos hscale]
      field_simp [hscale.ne']
    _ ≤ (3 * D : NNReal) * |p - r| := by
      rw [NNReal.coe_mul]
      norm_num only [NNReal.coe_ofNat]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hderiv (by norm_num)) (abs_nonneg _)

/-- At fixed momentum, the momentum callback inherits twice the factor's
global Lipschitz constant, uniformly over the momentum value. -/
theorem scalarGRMomentumCallback_lipschitz_fst
    (scale : ℝ → ℝ) (p : ℝ) (L : NNReal)
    (hscale : LipschitzWith L scale) :
    LipschitzWith (2 * L) (fun q => scalarGRMomentumCallback scale (q, p)) := by
  apply LipschitzWith.of_dist_le_mul
  intro q r
  rw [Real.dist_eq]
  unfold scalarGRMomentumCallback
  have hv := (scaledVelocityProfile_lipschitz p).dist_le_mul
    (scale q) (scale r)
  have hs := hscale.dist_le_mul q r
  calc
    _ ≤ 2 * |scale q - scale r| := by
      simpa [Real.dist_eq] using hv
    _ ≤ 2 * (L * |q - r|) := by
      gcongr
      simpa [Real.dist_eq] using hs
    _ = (2 * L : NNReal) * |q - r| := by
      rw [NNReal.coe_mul]
      norm_num only [NNReal.coe_ofNat]
      ring

/-- Function-space callbacks obtained from their scalar-coordinate forms. -/
noncomputable def scalarGRPositionCallbackUnit
    (drift scale scaleDerivative : ℝ → ℝ) :
    PhaseSpace Unit → Position Unit := fun z _ =>
  scalarGRPositionCallback drift scale scaleDerivative
    (z.1 Unit.unit, z.2 Unit.unit)

noncomputable def scalarGRMomentumCallbackUnit (scale : ℝ → ℝ) :
    PhaseSpace Unit → Momentum Unit := fun z _ =>
  scalarGRMomentumCallback scale (z.1 Unit.unit, z.2 Unit.unit)

theorem scalarGRPositionCallbackUnit_lipschitz_momentum
    (drift scale scaleDerivative : ℝ → ℝ) (q : Position Unit) (D : NNReal)
    (hscale : 0 < scale (q Unit.unit))
    (hderiv : |scaleDerivative (q Unit.unit)| ≤ D) :
    LipschitzWith (3 * D) (fun p : Momentum Unit =>
      scalarGRPositionCallbackUnit drift scale scaleDerivative (q, p)) := by
  apply LipschitzWith.of_dist_le_mul
  intro p r
  rw [dist_eq_norm, norm_pi_unit, dist_eq_norm, norm_pi_unit]
  exact (scalarGRPositionCallback_lipschitz_snd drift scale scaleDerivative
    (q Unit.unit) D hscale hderiv).dist_le_mul (p Unit.unit) (r Unit.unit)

theorem scalarGRMomentumCallbackUnit_lipschitz_position
    (scale : ℝ → ℝ) (p : Momentum Unit) (L : NNReal)
    (hscale : LipschitzWith L scale) :
    LipschitzWith (2 * L) (fun q : Position Unit =>
      scalarGRMomentumCallbackUnit scale (q, p)) := by
  apply LipschitzWith.of_dist_le_mul
  intro q r
  rw [dist_eq_norm, norm_pi_unit, dist_eq_norm, norm_pi_unit]
  exact (scalarGRMomentumCallback_lipschitz_fst scale (p Unit.unit) L hscale).dist_le_mul
    (q Unit.unit) (r Unit.unit)

end Mcmc.Relativistic
