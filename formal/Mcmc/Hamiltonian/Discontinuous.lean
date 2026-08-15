import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Coordinate updates for discontinuous Hamiltonian dynamics

This module isolates the exact-energy algebra in Algorithm 1 of Nishimura,
Dunson, and Lu's discontinuous HMC integrator.  The scalar `kinetic` field is
the Laplace kinetic energy `|p| / m`; the sign of momentum is represented by
`forward`.  A proposed coordinate move either crosses the potential jump and
spends exactly that much kinetic energy, or stays put and reflects its
direction.

This is deliberately only the deterministic energy layer.  Volume
preservation, random-order reversibility, momentum refreshment, and invariance
of the resulting Markov kernel require separate measure-theoretic theorems.
-/

namespace Mcmc.Hamiltonian

/-- Scalar phase data needed by one Laplace-momentum coordinate update. -/
structure DiscontinuousPhase (α : Type*) where
  position : α
  kinetic : ℝ
  forward : Bool

/-- Potential plus scalar Laplace kinetic energy. -/
def discontinuousHamiltonian (potential : α → ℝ)
    (z : DiscontinuousPhase α) : ℝ :=
  potential z.position + z.kinetic

/-- One crossing-or-reflection update for a supplied candidate position.

The candidate incorporates the step size, mass, momentum direction, and any
boundary convention.  If its potential jump is strictly smaller than the
available Laplace kinetic energy, the move crosses and pays the jump.
Otherwise the position and kinetic energy stay fixed and momentum reflects.
-/
noncomputable def discontinuousCoordinateStep (potential : α → ℝ) (candidate : α)
    (z : DiscontinuousPhase α) : DiscontinuousPhase α :=
  let jump := potential candidate - potential z.position
  if jump < z.kinetic then
    { position := candidate
      kinetic := z.kinetic - jump
      forward := z.forward }
  else
    { z with forward := !z.forward }

/-- A successful coordinate crossing leaves nonnegative kinetic energy. -/
theorem discontinuousCoordinateStep_kinetic_nonneg_of_crosses
    (potential : α → ℝ) (candidate : α) (z : DiscontinuousPhase α)
    (hcross : potential candidate - potential z.position < z.kinetic) :
    0 ≤ (discontinuousCoordinateStep potential candidate z).kinetic := by
  simp [discontinuousCoordinateStep, hcross]
  linarith

/-- The coordinate update preserves the Hamiltonian exactly. -/
@[simp]
theorem discontinuousCoordinateStep_energy
    (potential : α → ℝ) (candidate : α) (z : DiscontinuousPhase α) :
    discontinuousHamiltonian potential
        (discontinuousCoordinateStep potential candidate z) =
      discontinuousHamiltonian potential z := by
  by_cases hcross : potential candidate - potential z.position < z.kinetic
  · rw [discontinuousCoordinateStep, if_pos hcross]
    simp only [discontinuousHamiltonian]
    ring
  · rw [discontinuousCoordinateStep, if_neg hcross]
    rfl

/-- Reflection is an involution on the momentum direction. -/
@[simp]
theorem discontinuous_reflect_reflect (z : DiscontinuousPhase α) :
    { { z with forward := !z.forward } with forward := !(!z.forward) } = z := by
  cases z
  simp

open MeasureTheory ProbabilityTheory Set

/-- With unit-rate exponential Laplace kinetic energy, the probability of
crossing a potential jump is the usual Metropolis acceptance probability. -/
theorem expMeasure_crossing_probability (jump : ℝ) :
    (expMeasure 1).real (Ioi jump) = min 1 (Real.exp (-jump)) := by
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  rw [show Ioi jump = (Iic jump)ᶜ by simp]
  rw [measureReal_compl measurableSet_Iic,
    ← cdf_eq_real, cdf_expMeasure_eq zero_lt_one]
  rw [probReal_univ]
  by_cases hjump : 0 ≤ jump
  · rw [if_pos hjump, min_eq_right]
    · ring_nf
    · exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hjump)
  · rw [if_neg hjump, sub_zero, min_eq_left]
    exact Real.one_le_exp_iff.mpr (neg_nonneg.mpr (le_of_not_ge hjump))

/-- Expressing a potential jump as a negative-log target ratio recovers the
standard Metropolis ratio exactly. -/
theorem exp_neg_logWeight_jump {current candidate : ℝ}
    (hcurrent : 0 < current) (hcandidate : 0 < candidate) :
    Real.exp (-(Real.log current - Real.log candidate)) =
      candidate / current := by
  rw [neg_sub, Real.exp_sub, Real.exp_log hcandidate,
    Real.exp_log hcurrent]

/-- Consequently, a Laplace coordinate crossing between two positive target
weights has probability `min 1 (candidate / current)`. -/
theorem expMeasure_logWeight_crossing_probability
    {current candidate : ℝ} (hcurrent : 0 < current)
    (hcandidate : 0 < candidate) :
    (expMeasure 1).real
        (Ioi (Real.log current - Real.log candidate)) =
      min 1 (candidate / current) := by
  rw [expMeasure_crossing_probability,
    exp_neg_logWeight_jump hcurrent hcandidate]

end Mcmc.Hamiltonian
