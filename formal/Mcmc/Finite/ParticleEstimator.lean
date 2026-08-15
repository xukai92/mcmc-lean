import Mcmc.Finite.PseudoMarginal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Finite iid particle estimators

This module supplies the first particle layer below pseudo-marginal MH.  An
iid cloud of any positive finite size averages nonnegative unit-mean weights;
Lean proves that the average remains nonnegative and unbiased, then packages
it as the estimator required by finite pseudo-marginal MH.

This is finite particle importance sampling.  Sequential propagation,
resampling, ancestry, and conditional SMC are deliberately later layers.
-/

open scoped BigOperators

namespace Mcmc.Finite.ParticleEstimator

open MarkovKernel PseudoMarginal

variable {State Sample Particle : Type*}
  [Fintype State] [Fintype Sample] [Fintype Particle]
  [DecidableEq State] [DecidableEq Sample] [DecidableEq Particle]
  [Nonempty Particle]

/-- Independent population drawn from a common finite distribution. -/
def iidPopulation (law : Distribution Sample) : Distribution (Particle → Sample) where
  mass samples := ∏ i, law.mass (samples i)
  nonneg samples := Finset.prod_nonneg fun i _ => law.nonneg (samples i)
  sum_mass := by
    rw [← Fintype.prod_sum]
    simp [law.sum_mass]

/-- Arithmetic mean of particle weights. -/
noncomputable def particleAverage (score : Sample → ℝ)
    (samples : Particle → Sample) : ℝ :=
  (∑ i, score (samples i)) / Fintype.card Particle

omit [Fintype Sample] [DecidableEq Sample] [DecidableEq Particle] in
theorem particleAverage_nonneg
    {score : Sample → ℝ} (hscore : ∀ s, 0 ≤ score s)
    (samples : Particle → Sample) :
    0 ≤ particleAverage score samples := by
  unfold particleAverage
  exact div_nonneg (Finset.sum_nonneg fun i _ => hscore (samples i)) (by positivity)

omit [DecidableEq Sample] [Nonempty Particle] in
/-- One coordinate of an iid population has the original weighted
expectation. -/
theorem iidPopulation_coordinate_expectation
    (law : Distribution Sample) (score : Sample → ℝ)
    (i : Particle) :
    ∑ samples, (iidPopulation law).mass samples * score (samples i) =
      ∑ s, law.mass s * score s := by
  classical
  calc
    ∑ samples, (iidPopulation law).mass samples * score (samples i) =
        ∑ samples : Particle → Sample,
          ∏ j, if j = i then law.mass (samples j) * score (samples j)
          else law.mass (samples j) := by
      apply Finset.sum_congr rfl
      intro samples _
      rw [iidPopulation]
      calc
        (∏ j, law.mass (samples j)) * score (samples i) =
            ∏ j, law.mass (samples j) * (if j = i then score (samples i) else 1) := by
          rw [Finset.prod_mul_distrib]
          simp
        _ = ∏ j, if j = i then law.mass (samples j) * score (samples j)
              else law.mass (samples j) := by
          apply Finset.prod_congr rfl
          intro j _
          by_cases hji : j = i <;> simp [hji]
    _ = ∏ j : Particle, ∑ s, if j = i then law.mass s * score s
          else law.mass s := by
      exact (Fintype.prod_sum
        (f := fun j : Particle => fun s : Sample =>
          if j = i then law.mass s * score s else law.mass s)).symm
    _ = ∑ s, law.mass s * score s := by
      simp [law.sum_mass]

omit [DecidableEq Sample] in
/-- The average of iid nonnegative unit-mean scores is again unit mean. -/
theorem iidPopulation_particleAverage_unbiased
    (law : Distribution Sample) (score : Sample → ℝ)
    (hunbiased : ∑ s, law.mass s * score s = 1) :
    ∑ samples : Particle → Sample, (iidPopulation law).mass samples *
        particleAverage score samples = 1 := by
  classical
  have hcard : (Fintype.card Particle : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold particleAverage
  calc
    ∑ samples : Particle → Sample, (iidPopulation law).mass samples *
          ((∑ i, score (samples i)) / Fintype.card Particle) =
        (∑ i, ∑ samples : Particle → Sample,
          (iidPopulation law).mass samples *
          score (samples i)) / Fintype.card Particle := by
      simp_rw [div_eq_mul_inv, ← mul_assoc, Finset.mul_sum]
      rw [← Finset.sum_mul]
      congr 1
      rw [Finset.sum_comm]
    _ = (∑ _i : Particle, 1) / Fintype.card Particle := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [iidPopulation_coordinate_expectation law score i, hunbiased]
    _ = 1 := by
      simp [hcard]

/-- Lift a state-indexed one-particle unbiased score into a finite iid particle
estimator usable by pseudo-marginal MH. -/
noncomputable def estimator
    (law : State → Distribution Sample)
    (score : State → Sample → ℝ)
    (hscore : ∀ x s, 0 ≤ score x s)
    (hunbiased : ∀ x, ∑ s, (law x).mass s * score x s = 1) :
    Estimator State (Particle → Sample) where
  law x := iidPopulation (law x)
  value x samples := particleAverage (score x) samples
  nonneg x samples := particleAverage_nonneg (hscore x) samples
  unbiased x := iidPopulation_particleAverage_unbiased
    (law x) (score x) (hunbiased x)

/-- Particle importance pseudo-marginal MH: propose a state and draw a fresh
iid cloud at the proposal, retaining the current cloud on rejection. -/
noncomputable def particleIndependentMH
    (target : Distribution State)
    (law : State → Distribution Sample)
    (score : State → Sample → ℝ)
    (hscore : ∀ x s, 0 ≤ score x s)
    (hunbiased : ∀ x, ∑ s, (law x).mass s * score x s = 1)
    (proposal : MarkovKernel State) :
    MarkovKernel (State × (Particle → Sample)) :=
  PseudoMarginal.kernel target
    (estimator (Particle := Particle) law score hscore hunbiased) proposal

/-- Exact stationarity of particle importance MH on its extended state. -/
theorem particleIndependentMH_stationary
    (target : Distribution State)
    (law : State → Distribution Sample)
    (score : State → Sample → ℝ)
    (hscore : ∀ x s, 0 ≤ score x s)
    (hunbiased : ∀ x, ∑ s, (law x).mass s * score x s = 1)
    (proposal : MarkovKernel State) :
    (particleIndependentMH (Particle := Particle) target law score hscore
      hunbiased proposal).Stationary
      (PseudoMarginal.extendedTarget target
        (estimator (Particle := Particle) law score hscore hunbiased)) :=
  PseudoMarginal.stationary target
    (estimator (Particle := Particle) law score hscore hunbiased) proposal

omit [DecidableEq State] [DecidableEq Sample] in
/-- The stationary state marginal of particle importance MH is exactly the
desired target for every positive finite particle count. -/
theorem particleIndependentMH_state_marginal
    (target : Distribution State)
    (law : State → Distribution Sample)
    (score : State → Sample → ℝ)
    (hscore : ∀ x s, 0 ≤ score x s)
    (hunbiased : ∀ x, ∑ s, (law x).mass s * score x s = 1)
    (x : State) :
    ∑ cloud, (PseudoMarginal.extendedTarget target
      (estimator (Particle := Particle) law score hscore hunbiased)).mass
        (x, cloud) = target.mass x :=
  PseudoMarginal.state_marginal target
    (estimator (Particle := Particle) law score hscore hunbiased) x

end Mcmc.Finite.ParticleEstimator
