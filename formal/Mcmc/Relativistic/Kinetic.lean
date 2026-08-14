import Mcmc.Hamiltonian.Leapfrog

/-!
# Relativistic kinetic energy

This module formalizes the position-independent algebraic core used by Xu and
Ge's general-relativistic HMC construction.  For a rest mass `m`, speed
parameter `c`, and momentum `p`, it defines the relativistic mass, kinetic
energy, and velocity.  The main result proves that the Euclidean speed is
strictly smaller than `c` when `m` and `c` are positive.

The later Riemannian layer will apply these definitions after transforming
momentum by a square root of the inverse position-dependent metric.
-/

namespace Mcmc.Relativistic

open Mcmc.Hamiltonian

variable {ι : Type*} [Fintype ι]

/-- Relativistic mass associated with momentum `p`, rest mass `m`, and speed
parameter `c`; this is `m * sqrt (‖p‖² / (m² c²) + 1)`. -/
noncomputable def relativisticMass (m c : ℝ) (p : Momentum ι) : ℝ :=
  m * Real.sqrt (squaredEuclideanNorm p / (m ^ 2 * c ^ 2) + 1)

/-- Special-relativistic kinetic energy, including the constant rest-energy
term, as used in Xu and Ge's Equation (3). -/
noncomputable def relativisticKineticEnergy
    (m c : ℝ) (p : Momentum ι) : ℝ :=
  m * c ^ 2 * Real.sqrt (squaredEuclideanNorm p / (m ^ 2 * c ^ 2) + 1)

theorem continuous_relativisticKineticEnergy (m c : ℝ) :
    Continuous (relativisticKineticEnergy m c : Momentum ι → ℝ) := by
  unfold relativisticKineticEnergy
  unfold squaredEuclideanNorm euclideanInner
  fun_prop

/-- Velocity is momentum divided by its relativistic mass. -/
noncomputable def relativisticVelocity
    (m c : ℝ) (p : Momentum ι) : Momentum ι :=
  (relativisticMass m c p)⁻¹ • p

@[simp]
theorem relativisticMass_neg (m c : ℝ) (p : Momentum ι) :
    relativisticMass m c (-p) = relativisticMass m c p := by
  simp [relativisticMass, squaredEuclideanNorm, euclideanInner]

@[simp]
theorem relativisticKineticEnergy_neg (m c : ℝ) (p : Momentum ι) :
    relativisticKineticEnergy m c (-p) =
      relativisticKineticEnergy m c p := by
  simp [relativisticKineticEnergy, squaredEuclideanNorm, euclideanInner]

/-- The quantity under the square root is strictly positive for positive
physical parameters. -/
theorem relativistic_radicand_pos (m c : ℝ) (p : Momentum ι)
    (hm : 0 < m) (hc : 0 < c) :
    0 < squaredEuclideanNorm p / (m ^ 2 * c ^ 2) + 1 := by
  have hden : 0 < m ^ 2 * c ^ 2 := mul_pos (sq_pos_of_pos hm) (sq_pos_of_pos hc)
  have hquot : 0 ≤ squaredEuclideanNorm p / (m ^ 2 * c ^ 2) :=
    div_nonneg (squaredEuclideanNorm_nonneg p) hden.le
  linarith

theorem relativisticMass_pos (m c : ℝ) (p : Momentum ι)
    (hm : 0 < m) (hc : 0 < c) :
    0 < relativisticMass m c p := by
  exact mul_pos hm (Real.sqrt_pos.2 (relativistic_radicand_pos m c p hm hc))

/-- Squaring the relativistic mass separates the classical momentum term from
the positive rest-mass term. -/
theorem relativisticMass_sq (m c : ℝ) (p : Momentum ι)
    (hm : 0 < m) (hc : 0 < c) :
    relativisticMass m c p ^ 2 =
      euclideanNorm p ^ 2 / c ^ 2 + m ^ 2 := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hrad : 0 ≤ squaredEuclideanNorm p / (m ^ 2 * c ^ 2) + 1 :=
    (relativistic_radicand_pos m c p hm hc).le
  rw [relativisticMass, mul_pow, Real.sq_sqrt hrad,
    euclideanNorm_sq]
  field_simp

/-- Relativistic mass strictly dominates `‖p‖ / c`. -/
theorem euclideanNorm_div_lt_relativisticMass
    (m c : ℝ) (p : Momentum ι) (hm : 0 < m) (hc : 0 < c) :
    euclideanNorm p / c < relativisticMass m c p := by
  have hleft : 0 ≤ euclideanNorm p / c :=
    div_nonneg (euclideanNorm_nonneg p) hc.le
  have hright := relativisticMass_pos m c p hm hc
  apply (sq_lt_sq₀ hleft hright.le).mp
  rw [relativisticMass_sq m c p hm hc]
  rw [div_pow]
  exact lt_add_of_pos_right _ (sq_pos_of_pos hm)

/-- The norm of relativistic velocity is strictly bounded by the speed
parameter.  This is the position-independent speed-bound statement underlying
Xu and Ge's Equation (9). -/
theorem euclideanNorm_relativisticVelocity_lt
    (m c : ℝ) (p : Momentum ι) (hm : 0 < m) (hc : 0 < c) :
    euclideanNorm (relativisticVelocity m c p) < c := by
  have hmass := relativisticMass_pos m c p hm hc
  have hdom := euclideanNorm_div_lt_relativisticMass m c p hm hc
  rw [relativisticVelocity, euclideanNorm_smul,
    abs_of_pos (inv_pos.mpr hmass)]
  rw [inv_mul_eq_div]
  rw [div_lt_iff₀ hmass]
  simpa only [mul_comm] using (div_lt_iff₀ hc).mp hdom

end Mcmc.Relativistic
