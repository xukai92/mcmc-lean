import Mcmc.Finite.ParticleAsymptotics

/-!
# A concrete uniformly stable bootstrap particle filter

This example instantiates the time-uniform particle boundary with a finite
Feynman--Kac model whose mutation kernel completely refreshes from one fixed
law. Resampling may be arbitrarily state dependent through a positive
potential, but the subsequent refresh erases the ancestry. Hence every
positive-time particle cloud is exactly iid and its empirical MSE is exactly
the one-particle variance divided by particle count, uniformly in time.
-/

namespace Mcmc.Examples.UniformRefreshSMC

open Mcmc.Finite Mcmc.Finite.MarkovKernel
open Mcmc.Finite.ParticleEstimator
open Mcmc.Finite.SequentialMonteCarlo

variable {Sample Particle : Type*}
  [Fintype Sample] [DecidableEq Sample]
  [Fintype Particle] [DecidableEq Particle] [Nonempty Particle]

/-- Markov kernel whose every row is the same finite law. -/
def refreshKernel (law : Distribution Sample) : MarkovKernel Sample where
  prob _ next := law.mass next
  nonneg _ next := law.nonneg next
  sum_prob _ := law.sum_mass

omit [DecidableEq Sample] in
@[simp] theorem rowDistribution_refreshKernel
    (law : Distribution Sample) (current : Sample) :
    rowDistribution (refreshKernel law) current = law := by
  apply Distribution.ext
  rfl

/-- One positive-potential Feynman--Kac step followed by complete refresh. -/
def refreshStep (law : Distribution Sample) (potential : Sample → ℝ)
    (hpotential : ∀ x, 0 < potential x) : FeynmanKacStep Sample where
  potential := potential
  potential_pos := hpotential
  transition := refreshKernel law

omit [DecidableEq Sample] [Nonempty Particle] in
theorem propagatedPopulation_refreshKernel
    (law : Distribution Sample) (particles : Particle → Sample)
    (ancestors : Particle → Particle) :
    propagatedPopulation (refreshKernel law) particles ancestors =
      iidPopulation law := by
  unfold propagatedPopulation iidPopulation independentPopulation
  apply Distribution.ext
  rfl

omit [DecidableEq Sample] in
/-- Whatever population entered resampling, complete mutation refresh returns
the exact iid target population. -/
theorem bootstrapPopulationUpdate_refreshStep
    (law : Distribution Sample) (potential : Sample → ℝ)
    (hpotential : ∀ x, 0 < potential x) (particles : Particle → Sample) :
    bootstrapPopulationUpdate (refreshStep law potential hpotential) particles =
      iidPopulation law := by
  apply Distribution.ext
  funext next
  unfold bootstrapPopulationUpdate Distribution.bind
  change (∑ ancestors,
    (multinomialResampling
      (normalizedPotentialWeights potential hpotential particles)).mass ancestors *
      (propagatedPopulation (refreshKernel law) particles ancestors).mass next) = _
  simp_rw [propagatedPopulation_refreshKernel]
  rw [← Finset.sum_mul,
    (multinomialResampling
      (normalizedPotentialWeights potential hpotential particles)).sum_mass,
    one_mul]

omit [DecidableEq Sample] in
/-- The normalized one-particle Feynman--Kac target also becomes the refresh
law after one step, independently of its incoming law and potential. -/
theorem bootstrapTargetUpdate_refreshStep
    (current law : Distribution Sample) (potential : Sample → ℝ)
    (hpotential : ∀ x, 0 < potential x) :
    bootstrapTargetUpdate current (refreshStep law potential hpotential) = law := by
  apply Distribution.ext
  funext next
  unfold bootstrapTargetUpdate Distribution.evolve
  change (∑ x, (potentialReweight current potential hpotential).mass x *
    law.mass next) = law.mass next
  rw [← Finset.sum_mul, (potentialReweight current potential hpotential).sum_mass,
    one_mul]

omit [DecidableEq Sample] in
theorem bind_bootstrapPopulationUpdate_refreshStep
    (current : Distribution (Particle → Sample))
    (law : Distribution Sample) (potential : Sample → ℝ)
    (hpotential : ∀ x, 0 < potential x) :
    Distribution.bind current
      (bootstrapPopulationUpdate (refreshStep law potential hpotential)) =
        iidPopulation law := by
  apply Distribution.ext
  funext next
  simp only [Distribution.bind_mass,
    bootstrapPopulationUpdate_refreshStep]
  rw [← Finset.sum_mul, current.sum_mass, one_mul]

omit [DecidableEq Sample] in
/-- After any positive number of identical refresh stages, the actual
bootstrap population is exactly iid, independently of its incoming law. -/
theorem bootstrapPopulationLawFrom_replicate_refresh
    (current : Distribution (Particle → Sample))
    (law : Distribution Sample) (potential : Sample → ℝ)
    (hpotential : ∀ x, 0 < potential x) (time : ℕ) :
    bootstrapPopulationLawFrom current
      (List.replicate (time + 1) (refreshStep law potential hpotential)) =
        iidPopulation law := by
  induction time generalizing current with
  | zero =>
      simp [bootstrapPopulationLawFrom,
        bind_bootstrapPopulationUpdate_refreshStep]
  | succ time ih =>
      rw [show List.replicate (time + 1 + 1)
          (refreshStep law potential hpotential) =
        refreshStep law potential hpotential ::
          List.replicate (time + 1) (refreshStep law potential hpotential) by
            simp [List.replicate_succ]]
      rw [bootstrapPopulationLawFrom]
      exact ih _

omit [DecidableEq Sample] in
theorem bootstrapTargetLawFrom_replicate_refresh
    (current law : Distribution Sample) (potential : Sample → ℝ)
    (hpotential : ∀ x, 0 < potential x) (time : ℕ) :
    bootstrapTargetLawFrom current
      (List.replicate (time + 1) (refreshStep law potential hpotential)) = law := by
  induction time generalizing current with
  | zero => simp [bootstrapTargetLawFrom, bootstrapTargetUpdate_refreshStep]
  | succ time ih =>
      rw [show List.replicate (time + 1 + 1)
          (refreshStep law potential hpotential) =
        refreshStep law potential hpotential ::
          List.replicate (time + 1) (refreshStep law potential hpotential) by
            simp [List.replicate_succ]]
      rw [bootstrapTargetLawFrom]
      exact ih _

omit [DecidableEq Sample] in
/-- Concrete uniform-in-time particle result: at every positive horizon the
actual bootstrap empirical MSE is exactly `variance / N`, not merely bounded
by a horizon-dependent coefficient. -/
theorem bootstrapPopulation_replicate_refresh_mse
    (initial law : Distribution Sample) (potential : Sample → ℝ)
    (hpotential : ∀ x, 0 < potential x) (score : Sample → ℝ)
    (extra time : ℕ) :
    finiteExpectation
        (bootstrapPopulationLaw (Particle := Fin (extra + 1)) initial
          (List.replicate (time + 1) (refreshStep law potential hpotential)))
        (fun particles =>
          (particleAverage score particles - finiteExpectation law score) ^ 2) =
      finiteVariance law score / (extra + 1 : ℝ) := by
  unfold bootstrapPopulationLaw
  rw [bootstrapPopulationLawFrom_replicate_refresh]
  simpa using (iidPopulation_target_mse_eq_variance_div_count
    (Particle := Fin (extra + 1)) law score)

end Mcmc.Examples.UniformRefreshSMC
