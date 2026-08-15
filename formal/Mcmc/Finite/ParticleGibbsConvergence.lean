import Mcmc.Finite.Adaptive
import Mcmc.Finite.Combinators

/-!
# An exact particle-count calculation for zero-horizon particle Gibbs

For a Feynman--Kac model with no transition times, conditional SMC retains one
copy of the current state, draws the other `N - 1` particles from the target,
and selects a terminal particle uniformly. Consequently its state kernel is
exactly `1/N` times the identity plus `1 - 1/N` times an independent refresh.

This specialization gives a fully explicit particle-count and convergence
result. It is deliberately not presented as a rate for positive-horizon
particle Gibbs, whose genealogy and potentials require additional hypotheses.
-/

open scoped BigOperators

namespace Mcmc.Finite.MarkovKernel

variable {State : Type*} [Fintype State]

/-- Ignore the current state and draw exactly from `target`. -/
def refresh (target : Distribution State) : MarkovKernel State where
  prob _ y := target.mass y
  nonneg _ y := target.nonneg y
  sum_prob _ := target.sum_mass

@[simp] theorem refresh_prob (target : Distribution State) (x y : State) :
    (refresh target).prob x y = target.mass y := rfl

theorem refresh_stationary (target : Distribution State) :
    (refresh target).Stationary target := by
  intro y
  simp [refresh, ← Finset.sum_mul, target.sum_mass]

/-- The state-level kernel induced by zero-horizon particle Gibbs with `N`
particles. One uniformly selected particle is the retained current state and
the remaining mass is an independent target refresh. -/
noncomputable def zeroHorizonParticleGibbs [DecidableEq State] (particles : ℕ)
    (hparticles : 0 < particles) (target : Distribution State) :
    MarkovKernel State :=
  mixture ((particles : ℝ)⁻¹)
    (inv_nonneg.mpr (Nat.cast_nonneg particles))
    (inv_le_one_of_one_le₀ (by exact_mod_cast hparticles))
    identity (refresh target)

@[simp] theorem zeroHorizonParticleGibbs_prob [DecidableEq State]
    (particles : ℕ) (hparticles : 0 < particles)
    (target : Distribution State) (x y : State) :
    (zeroHorizonParticleGibbs particles hparticles target).prob x y =
      (particles : ℝ)⁻¹ * (if x = y then 1 else 0) +
        (1 - (particles : ℝ)⁻¹) * target.mass y := rfl

theorem zeroHorizonParticleGibbs_stationary [DecidableEq State]
    (particles : ℕ) (hparticles : 0 < particles)
    (target : Distribution State) :
    (zeroHorizonParticleGibbs particles hparticles target).Stationary target :=
  mixture_stationary _ _ _ _ _ target
    (identity_stationary target) (refresh_stationary target)

@[simp] theorem zeroHorizonParticleGibbs_one [DecidableEq State]
    (target : Distribution State) :
    zeroHorizonParticleGibbs 1 (by decide) target = identity := by
  apply MarkovKernel.ext
  funext x y
  simp [zeroHorizonParticleGibbs, mixture, identity]

theorem evolve_zeroHorizonParticleGibbs_mass [DecidableEq State]
    (law target : Distribution State)
    (particles : ℕ) (hparticles : 0 < particles) (y : State) :
    (law.evolve (zeroHorizonParticleGibbs particles hparticles target)).mass y =
      (particles : ℝ)⁻¹ * law.mass y +
        (1 - (particles : ℝ)⁻¹) * target.mass y := by
  rw [Distribution.evolve_mass]
  simp_rw [zeroHorizonParticleGibbs_prob, mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  · simp [mul_comm]
  · rw [← Finset.sum_mul, law.sum_mass, one_mul]

/-- Exact pointwise law after any number of zero-horizon PG iterations. The
dependence on the initial state survives with probability `N⁻steps`. -/
theorem iterateLaw_zeroHorizonParticleGibbs_mass [DecidableEq State]
    (particles : ℕ) (hparticles : 0 < particles)
    (target : Distribution State) (initial y : State) (steps : ℕ) :
    (Nonhomogeneous.iterateLaw (Nonhomogeneous.pointMass initial)
      (zeroHorizonParticleGibbs particles hparticles target) steps).mass y =
      ((particles : ℝ)⁻¹) ^ steps * (if y = initial then 1 else 0) +
        (1 - ((particles : ℝ)⁻¹) ^ steps) * target.mass y := by
  induction steps generalizing y with
  | zero => simp [Nonhomogeneous.iterateLaw, Nonhomogeneous.pointMass]
  | succ steps ih =>
      rw [Nonhomogeneous.iterateLaw,
        evolve_zeroHorizonParticleGibbs_mass, ih, pow_succ]
      ring

/-- Exact total-variation contraction for the zero-horizon specialization. -/
theorem distributionTotalVariation_iterate_zeroHorizonParticleGibbs
    [DecidableEq State]
    (particles : ℕ) (hparticles : 0 < particles)
    (target : Distribution State) (initial : State) (steps : ℕ) :
    Nonhomogeneous.distributionTotalVariation
      (Nonhomogeneous.iterateLaw (Nonhomogeneous.pointMass initial)
        (zeroHorizonParticleGibbs particles hparticles target) steps) target =
      ((particles : ℝ)⁻¹) ^ steps *
        Nonhomogeneous.distributionTotalVariation
          (Nonhomogeneous.pointMass initial) target := by
  unfold Nonhomogeneous.distributionTotalVariation
  simp_rw [iterateLaw_zeroHorizonParticleGibbs_mass,
    Nonhomogeneous.pointMass]
  have hc : 0 ≤ ((particles : ℝ)⁻¹) ^ steps := pow_nonneg
    (inv_nonneg.mpr (Nat.cast_nonneg particles)) _
  rw [← mul_div_assoc]
  apply congrArg (fun z : ℝ => z / 2)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [show
      ((particles : ℝ)⁻¹ ^ steps * (if y = initial then 1 else 0) +
          (1 - (particles : ℝ)⁻¹ ^ steps) * target.mass y -
        target.mass y) =
        ((particles : ℝ)⁻¹) ^ steps *
          ((if y = initial then 1 else 0) - target.mass y) by ring,
    abs_mul, abs_of_nonneg hc]

/-- For at least two particles, the exact geometric factor tends to zero. -/
theorem zeroHorizonParticleGibbs_rate_tendsto_zero
    (particles : ℕ) (hparticles : 2 ≤ particles) :
    Filter.Tendsto (fun steps : ℕ => ((particles : ℝ)⁻¹) ^ steps)
      Filter.atTop (nhds 0) := by
  apply tendsto_pow_atTop_nhds_zero_of_lt_one
  · exact inv_nonneg.mpr (Nat.cast_nonneg particles)
  · rw [inv_lt_one₀ (by positivity)]
    exact_mod_cast hparticles

end Mcmc.Finite.MarkovKernel
