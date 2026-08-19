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

/-! ### A genuinely partial-refresh Feynman--Kac model -/

/-- With probability `refreshProbability`, draw from `law`; otherwise retain
the current state. Unlike `refreshKernel`, this transition preserves ancestry
information whenever the identity branch is selected. -/
def partialRefreshKernel (refreshProbability : ℝ)
    (hprob0 : 0 ≤ refreshProbability) (hprob1 : refreshProbability ≤ 1)
    (law : Distribution Sample) : MarkovKernel Sample :=
  mixture refreshProbability hprob0 hprob1 (refreshKernel law) identity

omit [Nonempty Particle] in
@[simp] theorem partialRefreshKernel_prob
    (refreshProbability : ℝ)
    (hprob0 : 0 ≤ refreshProbability) (hprob1 : refreshProbability ≤ 1)
    (law : Distribution Sample) (current next : Sample) :
    (partialRefreshKernel refreshProbability hprob0 hprob1 law).prob current next =
      refreshProbability * law.mass next +
        (1 - refreshProbability) * (if current = next then 1 else 0) := rfl

omit [Nonempty Particle] in
theorem partialRefreshKernel_stationary
    (refreshProbability : ℝ)
    (hprob0 : 0 ≤ refreshProbability) (hprob1 : refreshProbability ≤ 1)
    (law : Distribution Sample) :
    (partialRefreshKernel refreshProbability hprob0 hprob1 law).Stationary law :=
  mixture_stationary refreshProbability hprob0 hprob1
    (refreshKernel law) identity law (by
      intro next
      change (∑ x, law.mass x * law.mass next) = law.mass next
      rw [← Finset.sum_mul, law.sum_mass, one_mul]) (identity_stationary law)

omit [Nonempty Particle] in
/-- Exact one-step contraction of every point mass toward the refresh law. -/
theorem evolve_partialRefreshKernel_mass
    (refreshProbability : ℝ)
    (hprob0 : 0 ≤ refreshProbability) (hprob1 : refreshProbability ≤ 1)
    (current law : Distribution Sample) (next : Sample) :
    (current.evolve
      (partialRefreshKernel refreshProbability hprob0 hprob1 law)).mass next =
      refreshProbability * law.mass next +
        (1 - refreshProbability) * current.mass next := by
  rw [Distribution.evolve_mass]
  simp_rw [partialRefreshKernel_prob, mul_add, Finset.sum_add_distrib]
  rw [show (∑ x, current.mass x * (refreshProbability * law.mass next)) =
      refreshProbability * law.mass next by
    rw [← Finset.sum_mul, current.sum_mass, one_mul]]
  rw [show (∑ x, current.mass x *
      ((1 - refreshProbability) * if x = next then 1 else 0)) =
      (1 - refreshProbability) * current.mass next by
    rw [show (∑ x, current.mass x *
        ((1 - refreshProbability) * if x = next then 1 else 0)) =
        (1 - refreshProbability) *
          ∑ x, current.mass x * (if x = next then 1 else 0) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring]
    simp]

/-- Constant potential isolates mutation, producing a nondegenerate
Feynman--Kac step whose normalized target contracts but does not refresh in one
step unless the refresh probability is one. -/
def partialRefreshStep (refreshProbability : ℝ)
    (hprob0 : 0 ≤ refreshProbability) (hprob1 : refreshProbability ≤ 1)
    (law : Distribution Sample) : FeynmanKacStep Sample where
  potential := fun _ => 1
  potential_pos := fun _ => by norm_num
  transition := partialRefreshKernel refreshProbability hprob0 hprob1 law

omit [Nonempty Particle] in
theorem bootstrapTargetUpdate_partialRefreshStep_mass
    (refreshProbability : ℝ)
    (hprob0 : 0 ≤ refreshProbability) (hprob1 : refreshProbability ≤ 1)
    (current law : Distribution Sample) (next : Sample) :
    (bootstrapTargetUpdate current
      (partialRefreshStep refreshProbability hprob0 hprob1 law)).mass next =
      refreshProbability * law.mass next +
        (1 - refreshProbability) * current.mass next := by
  have hone : finiteExpectation current (fun _ => 1) = 1 := by
    unfold finiteExpectation
    simpa using current.sum_mass
  have hreweight : potentialReweight current (fun _ => 1)
      (fun _ => by norm_num) = current := by
    apply Distribution.ext
    funext state
    simp [potentialReweight, hone]
  unfold bootstrapTargetUpdate partialRefreshStep
  rw [hreweight]
  exact evolve_partialRefreshKernel_mass refreshProbability hprob0 hprob1
    current law next

omit [Nonempty Particle] in
/-- The normalized Feynman--Kac error contracts by exactly the retained-mass
factor. This is the model-level strict contraction needed before deriving
uniform particle bounds for the partially mixing bootstrap population. -/
theorem bootstrapTargetUpdate_partialRefreshStep_error
    (refreshProbability : ℝ)
    (hprob0 : 0 ≤ refreshProbability) (hprob1 : refreshProbability ≤ 1)
    (current law : Distribution Sample) (next : Sample) :
    (bootstrapTargetUpdate current
      (partialRefreshStep refreshProbability hprob0 hprob1 law)).mass next -
        law.mass next =
      (1 - refreshProbability) * (current.mass next - law.mass next) := by
  rw [bootstrapTargetUpdate_partialRefreshStep_mass]
  ring

omit [Nonempty Particle] in
/-- Across an arbitrary horizon, the normalized target error is exactly the
retained-mass factor raised to the number of partial-refresh stages. -/
theorem bootstrapTargetLawFrom_replicate_partialRefresh_error
    (refreshProbability : ℝ)
    (hprob0 : 0 ≤ refreshProbability) (hprob1 : refreshProbability ≤ 1)
    (initial law : Distribution Sample) (time : ℕ) (next : Sample) :
    (bootstrapTargetLawFrom initial
      (List.replicate time
        (partialRefreshStep refreshProbability hprob0 hprob1 law))).mass next -
        law.mass next =
      (1 - refreshProbability) ^ time *
        (initial.mass next - law.mass next) := by
  induction time generalizing initial with
  | zero => simp [bootstrapTargetLawFrom]
  | succ time ih =>
      rw [List.replicate_succ, bootstrapTargetLawFrom, ih]
      rw [bootstrapTargetUpdate_partialRefreshStep_error]
      rw [pow_succ]
      ring

omit [Nonempty Particle] in
/-- The conditional observable mean under partial refresh is the same convex
combination of the refresh-law mean and the retained current score. -/
theorem partialRefreshKernel_expectation
    (refreshProbability : ℝ)
    (hprob0 : 0 ≤ refreshProbability) (hprob1 : refreshProbability ≤ 1)
    (law : Distribution Sample) (current : Sample) (score : Sample → ℝ) :
    finiteExpectation
      (rowDistribution
        (partialRefreshKernel refreshProbability hprob0 hprob1 law) current)
      score =
      refreshProbability * finiteExpectation law score +
        (1 - refreshProbability) * score current := by
  change (∑ x, (partialRefreshKernel refreshProbability hprob0 hprob1 law).prob
      current x * score x) =
    refreshProbability * (∑ x, law.mass x * score x) +
      (1 - refreshProbability) * score current
  simp_rw [partialRefreshKernel_prob, add_mul, Finset.sum_add_distrib]
  rw [show (∑ x, refreshProbability * law.mass x * score x) =
      refreshProbability * (∑ x, law.mass x * score x) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring]
  rw [show (∑ x, (1 - refreshProbability) *
      (if current = x then 1 else 0) * score x) =
      (1 - refreshProbability) * score current by
    rw [show (∑ x, (1 - refreshProbability) *
        (if current = x then 1 else 0) * score x) =
      (1 - refreshProbability) *
        ∑ x, (if current = x then 1 else 0) * score x by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring]
    simp]

omit [Nonempty Particle] in
/-- The normalized one-particle target expectation obeys the corresponding
partial-refresh affine update. -/
theorem bootstrapTargetUpdate_partialRefreshStep_expectation
    (refreshProbability : ℝ)
    (hprob0 : 0 ≤ refreshProbability) (hprob1 : refreshProbability ≤ 1)
    (current law : Distribution Sample) (score : Sample → ℝ) :
    finiteExpectation
      (bootstrapTargetUpdate current
        (partialRefreshStep refreshProbability hprob0 hprob1 law)) score =
      refreshProbability * finiteExpectation law score +
        (1 - refreshProbability) * finiteExpectation current score := by
  change (∑ x, (bootstrapTargetUpdate current
      (partialRefreshStep refreshProbability hprob0 hprob1 law)).mass x * score x) =
    refreshProbability * (∑ x, law.mass x * score x) +
      (1 - refreshProbability) * (∑ x, current.mass x * score x)
  simp_rw [bootstrapTargetUpdate_partialRefreshStep_mass, add_mul,
    Finset.sum_add_distrib]
  rw [show (∑ x, refreshProbability * law.mass x * score x) =
      refreshProbability * (∑ x, law.mass x * score x) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring]
  rw [show (∑ x, (1 - refreshProbability) * current.mass x * score x) =
      (1 - refreshProbability) * (∑ x, current.mass x * score x) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring]

/-- Conditional particle-average MSE for one partial-refresh bootstrap stage.
The inherited error contracts by `(1-p)^2`; all new propagation and ancestry
noise is bounded by the existing universal `8‖f‖∞²/N` term. -/
theorem partialRefreshStage_particleAverage_sq_error_le
    [Nonempty Sample]
    (refreshProbability : ℝ)
    (hprob0 : 0 ≤ refreshProbability) (hprob1 : refreshProbability ≤ 1)
    (current law : Distribution Sample) (particles : Particle → Sample)
    (score : Sample → ℝ) :
    ∑ outcome,
        (resamplePropagateLaw
          (normalizedPotentialWeights (fun _ => 1) (fun _ => by norm_num)
            particles)
          particles
          (partialRefreshKernel refreshProbability hprob0 hprob1 law)).mass
            outcome *
          (particleAverage score outcome.2 -
            finiteExpectation
              (bootstrapTargetUpdate current
                (partialRefreshStep refreshProbability hprob0 hprob1 law))
              score) ^ 2 ≤
      8 * finiteFunctionAbsMaximum score ^ 2 / Fintype.card Particle +
        (1 - refreshProbability) ^ 2 *
          (particleAverage score particles - finiteExpectation current score) ^ 2 := by
  rw [bootstrapStage_particleAverage_sq_error]
  have hfresh := bootstrapStage_freshVariance_le
    (Particle := Particle) (fun _ : Sample => 1) (fun _ => by norm_num)
    particles (partialRefreshKernel refreshProbability hprob0 hprob1 law) score
  have hcard : (0 : ℝ) < Fintype.card Particle := by
    exact_mod_cast Fintype.card_pos
  have hfreshDiv :
      (finiteExpectation
          (normalizedPotentialWeights (fun _ : Sample => 1)
            (fun _ => by norm_num) particles)
          (fun i => finiteVariance
            (rowDistribution
              (partialRefreshKernel refreshProbability hprob0 hprob1 law)
              (particles i)) score) +
        finiteVariance
          (normalizedPotentialWeights (fun _ : Sample => 1)
            (fun _ => by norm_num) particles)
          (fun i => finiteExpectation
            (rowDistribution
              (partialRefreshKernel refreshProbability hprob0 hprob1 law)
              (particles i)) score)) /
          Fintype.card Particle ≤
        8 * finiteFunctionAbsMaximum score ^ 2 / Fintype.card Particle := by
    exact div_le_div_of_nonneg_right hfresh hcard.le
  apply add_le_add hfreshDiv
  rw [bootstrapTargetUpdate_partialRefreshStep_expectation]
  have haverage :
      particleAverage
          (fun x => (1 : ℝ) * finiteExpectation
            (rowDistribution
              (partialRefreshKernel refreshProbability hprob0 hprob1 law) x)
            score) particles /
          particleAverage (fun _ : Sample => 1) particles -
          (refreshProbability * finiteExpectation law score +
            (1 - refreshProbability) * finiteExpectation current score) =
        (1 - refreshProbability) *
          (particleAverage score particles - finiteExpectation current score) := by
    simp_rw [one_mul, partialRefreshKernel_expectation]
    have hcardne : (Fintype.card Particle : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have havgOne : particleAverage (fun _ : Sample => 1) particles = 1 := by
      unfold particleAverage
      simp [hcardne]
    have havgAffine :
        particleAverage
            (fun x => refreshProbability * finiteExpectation law score +
              (1 - refreshProbability) * score x) particles =
          refreshProbability * finiteExpectation law score +
            (1 - refreshProbability) * particleAverage score particles := by
      unfold particleAverage
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [show (∑ x, (1 - refreshProbability) * score (particles x)) =
          (1 - refreshProbability) * ∑ x, score (particles x) by
        rw [Finset.mul_sum]]
      field_simp
    rw [havgOne, div_one, havgAffine]
    ring
  rw [haverage]
  rw [mul_pow]

/-- Integrated affine MSE recurrence for the actual dependent bootstrap
population. This is the model-specific premise needed by the generic
uniform-in-time inverse-particle-count theorem. -/
theorem bootstrapPopulationUpdate_partialRefresh_mse_le
    [Nonempty Sample]
    (refreshProbability : ℝ)
    (hprob0 : 0 ≤ refreshProbability) (hprob1 : refreshProbability ≤ 1)
    (currentPopulation : Distribution (Particle → Sample))
    (currentTarget law : Distribution Sample) (score : Sample → ℝ) :
    finiteExpectation
        (Distribution.bind currentPopulation
          (bootstrapPopulationUpdate
            (partialRefreshStep refreshProbability hprob0 hprob1 law)))
        (fun particles =>
          (particleAverage score particles -
            finiteExpectation
              (bootstrapTargetUpdate currentTarget
                (partialRefreshStep refreshProbability hprob0 hprob1 law))
              score) ^ 2) ≤
      (1 - refreshProbability) ^ 2 *
        finiteExpectation currentPopulation (fun particles =>
          (particleAverage score particles -
            finiteExpectation currentTarget score) ^ 2) +
      8 * finiteFunctionAbsMaximum score ^ 2 / Fintype.card Particle := by
  rw [finiteExpectation_bind]
  calc
    _ = ∑ particles, currentPopulation.mass particles *
        (∑ outcome,
          (resamplePropagateLaw
            (normalizedPotentialWeights (fun _ => 1) (fun _ => by norm_num)
              particles)
            particles
            (partialRefreshKernel refreshProbability hprob0 hprob1 law)).mass
              outcome *
            (particleAverage score outcome.2 -
              finiteExpectation
                (bootstrapTargetUpdate currentTarget
                  (partialRefreshStep refreshProbability hprob0 hprob1 law))
                score) ^ 2) := by
      apply Finset.sum_congr rfl
      intro particles _
      rw [bootstrapPopulationUpdate_expectation_eq_joint]
      rfl
    _ ≤ ∑ particles, currentPopulation.mass particles *
        (8 * finiteFunctionAbsMaximum score ^ 2 / Fintype.card Particle +
          (1 - refreshProbability) ^ 2 *
            (particleAverage score particles -
              finiteExpectation currentTarget score) ^ 2) := by
      apply Finset.sum_le_sum
      intro particles _
      exact mul_le_mul_of_nonneg_left
        (partialRefreshStage_particleAverage_sq_error_le
          refreshProbability hprob0 hprob1 currentTarget law particles score)
        (currentPopulation.nonneg particles)
    _ = (1 - refreshProbability) ^ 2 *
          finiteExpectation currentPopulation (fun particles =>
            (particleAverage score particles -
              finiteExpectation currentTarget score) ^ 2) +
        8 * finiteFunctionAbsMaximum score ^ 2 / Fintype.card Particle := by
      unfold finiteExpectation
      rw [show (∑ particles, currentPopulation.mass particles *
          (8 * finiteFunctionAbsMaximum score ^ 2 / Fintype.card Particle +
            (1 - refreshProbability) ^ 2 *
              (particleAverage score particles -
                ∑ x, currentTarget.mass x * score x) ^ 2)) =
          (∑ particles, currentPopulation.mass particles) *
              (8 * finiteFunctionAbsMaximum score ^ 2 /
                Fintype.card Particle) +
            (1 - refreshProbability) ^ 2 *
              ∑ particles, currentPopulation.mass particles *
                (particleAverage score particles -
                  ∑ x, currentTarget.mass x * score x) ^ 2 by
        simp_rw [mul_add, Finset.sum_add_distrib]
        rw [← Finset.sum_mul]
        rw [Finset.mul_sum]
        apply congrArg₂ (· + ·) rfl
        apply Finset.sum_congr rfl
        intro particles _
        ring]
      rw [currentPopulation.sum_mass, one_mul]
      ring

/-- Count-indexed empirical MSE for the actual partial-refresh bootstrap
particle filter at a given horizon. -/
noncomputable def partialRefreshPopulationMSEByExtra
    (refreshProbability : ℝ)
    (hprob0 : 0 ≤ refreshProbability) (hprob1 : refreshProbability ≤ 1)
    (initial law : Distribution Sample) (score : Sample → ℝ)
    (extra time : ℕ) : ℝ :=
  finiteExpectation
    (bootstrapPopulationLaw (Particle := Fin (extra + 1)) initial
      (List.replicate time
        (partialRefreshStep refreshProbability hprob0 hprob1 law)))
    (fun particles =>
      (particleAverage score particles -
        finiteExpectation
          (bootstrapTargetLaw initial
            (List.replicate time
              (partialRefreshStep refreshProbability hprob0 hprob1 law)))
          score) ^ 2)

/-- The empirical mean-square error is nonnegative at every count and time. -/
theorem partialRefreshPopulationMSEByExtra_nonneg
    (refreshProbability : ℝ)
    (hprob0 : 0 ≤ refreshProbability) (hprob1 : refreshProbability ≤ 1)
    (initial law : Distribution Sample) (score : Sample → ℝ)
    (extra time : ℕ) :
    0 ≤ partialRefreshPopulationMSEByExtra refreshProbability hprob0 hprob1
      initial law score extra time := by
  unfold partialRefreshPopulationMSEByExtra finiteExpectation
  apply Finset.sum_nonneg
  intro particles _
  exact mul_nonneg
    ((bootstrapPopulationLaw (Particle := Fin (extra + 1)) initial
      (List.replicate time
        (partialRefreshStep refreshProbability hprob0 hprob1 law))).nonneg particles)
    (sq_nonneg _)

/-- A positive partial-refresh probability makes the inherited squared-error
rate strictly contractive. -/
theorem partialRefresh_sq_rate_lt_one
    (refreshProbability : ℝ) (hprob0 : 0 < refreshProbability)
    (hprob1 : refreshProbability ≤ 1) :
    (1 - refreshProbability) ^ 2 < 1 := by
  nlinarith [sq_nonneg refreshProbability]

/-- Uniform-in-time `C/N` control for the actual dependent partial-refresh
bootstrap population. The proof combines the exact model contraction with
the resampling/propagation variance bound; it does not treat the population as
iid after the first step. -/
theorem partialRefreshPopulationMSEByExtra_le_uniform
    [Nonempty Sample]
    (refreshProbability : ℝ)
    (hprob0 : 0 < refreshProbability) (hprob1 : refreshProbability ≤ 1)
    (initial law : Distribution Sample) (score : Sample → ℝ)
    (extra time : ℕ) :
    partialRefreshPopulationMSEByExtra refreshProbability hprob0.le hprob1
        initial law score extra time ≤
      (finiteVariance initial score +
          (8 * finiteFunctionAbsMaximum score ^ 2) /
            (1 - (1 - refreshProbability) ^ 2)) /
        ((extra : ℝ) + 1) := by
  let step := partialRefreshStep refreshProbability hprob0.le hprob1 law
  let error : ℕ → ℕ → ℝ := fun extra time =>
    partialRefreshPopulationMSEByExtra refreshProbability hprob0.le hprob1
      initial law score extra time
  have hrate0 : 0 ≤ (1 - refreshProbability) ^ 2 := sq_nonneg _
  have hrate1 : (1 - refreshProbability) ^ 2 < 1 :=
    partialRefresh_sq_rate_lt_one refreshProbability hprob0 hprob1
  have hinitial0 : 0 ≤ finiteVariance initial score := finiteVariance_nonneg _ _
  have hnoise0 : 0 ≤ 8 * finiteFunctionAbsMaximum score ^ 2 := by positivity
  have hinitial : ∀ extra,
      error extra 0 ≤ finiteVariance initial score / ((extra : ℝ) + 1) := by
    intro count
    change partialRefreshPopulationMSEByExtra refreshProbability hprob0.le hprob1
      initial law score count 0 ≤ _
    unfold partialRefreshPopulationMSEByExtra
    change (∑ samples : Fin (count + 1) → Sample,
      (iidPopulation initial).mass samples *
        (particleAverage score samples - finiteExpectation initial score) ^ 2) ≤ _
    rw [iidPopulation_particleAverage_mse]
    simp
  have hstep : ∀ extra n,
      error extra (n + 1) ≤
        (1 - refreshProbability) ^ 2 * error extra n +
          (8 * finiteFunctionAbsMaximum score ^ 2) / ((extra : ℝ) + 1) := by
    intro count n
    let prior := List.replicate n step
    have hlist : List.replicate (n + 1) step = prior ++ [step] := by
      simp [prior, List.replicate_succ']
    change partialRefreshPopulationMSEByExtra refreshProbability hprob0.le hprob1
      initial law score count (n + 1) ≤ _
    unfold partialRefreshPopulationMSEByExtra
    change finiteExpectation
      (bootstrapPopulationLaw (Particle := Fin (count + 1)) initial
        (List.replicate (n + 1) step)) _ ≤ _
    rw [hlist, bootstrapPopulationLaw_append_singleton,
      bootstrapTargetLaw_append_singleton]
    have h := bootstrapPopulationUpdate_partialRefresh_mse_le
      (Particle := Fin (count + 1)) refreshProbability hprob0.le hprob1
      (bootstrapPopulationLaw initial prior)
      (bootstrapTargetLaw initial prior) law score
    simpa [error, prior, step, partialRefreshPopulationMSEByExtra] using h
  exact sequential_error_le_uniform_inverse_count error hrate0 hrate1
    hinitial0 hnoise0 hinitial hstep extra time

/-- Uniform-in-time consistency for the concrete dependent partial-refresh
bootstrap filter. The time horizon may vary arbitrarily; only the particle
count schedule must tend to infinity. -/
theorem partialRefreshPopulationMSEByExtra_tendsto_zero_varying_time_of_count_tendsto
    [Nonempty Sample]
    (refreshProbability : ℝ)
    (hprob0 : 0 < refreshProbability) (hprob1 : refreshProbability ≤ 1)
    (initial law : Distribution Sample) (score : Sample → ℝ)
    (extra time : ℕ → ℕ)
    (hextra : Filter.Tendsto extra Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun index =>
      partialRefreshPopulationMSEByExtra refreshProbability hprob0.le hprob1
        initial law score (extra index) (time index))
      Filter.atTop (nhds 0) := by
  exact tendsto_zero_varying_horizon_of_uniform_inverse_count
    (fun count horizon =>
      partialRefreshPopulationMSEByExtra refreshProbability hprob0.le hprob1
        initial law score count horizon)
    (finiteVariance initial score +
      (8 * finiteFunctionAbsMaximum score ^ 2) /
        (1 - (1 - refreshProbability) ^ 2))
    (partialRefreshPopulationMSEByExtra_nonneg
      refreshProbability hprob0.le hprob1 initial law score)
    (partialRefreshPopulationMSEByExtra_le_uniform
      refreshProbability hprob0 hprob1 initial law score)
    extra time hextra

/-- An explicit finite-count, uniform-in-time probability bound for the
dependent partial-refresh bootstrap filter. -/
theorem partialRefreshPopulationDeviationProbability_le_uniform
    [Nonempty Sample]
    (refreshProbability : ℝ)
    (hprob0 : 0 < refreshProbability) (hprob1 : refreshProbability ≤ 1)
    (initial law : Distribution Sample) (score : Sample → ℝ)
    (extra time : ℕ) {tolerance : ℝ} (htolerance : 0 < tolerance) :
    bootstrapPopulationDeviationProbability initial
        (List.replicate time
          (partialRefreshStep refreshProbability hprob0.le hprob1 law))
        score extra tolerance ≤
      ((finiteVariance initial score +
          (8 * finiteFunctionAbsMaximum score ^ 2) /
            (1 - (1 - refreshProbability) ^ 2)) /
        ((extra : ℝ) + 1)) / tolerance ^ 2 := by
  calc
    _ ≤ partialRefreshPopulationMSEByExtra refreshProbability hprob0.le hprob1
          initial law score extra time / tolerance ^ 2 := by
      simpa [partialRefreshPopulationMSEByExtra,
        bootstrapPopulationMSEByExtra] using
        bootstrapPopulationDeviationProbability_le_mse initial
          (List.replicate time
            (partialRefreshStep refreshProbability hprob0.le hprob1 law))
          score extra htolerance
    _ ≤ _ := div_le_div_of_nonneg_right
      (partialRefreshPopulationMSEByExtra_le_uniform
        refreshProbability hprob0 hprob1 initial law score extra time)
      (sq_nonneg tolerance)

/-- Uniform-in-time convergence in probability for the concrete dependent
partial-refresh bootstrap filter. The horizon schedule is arbitrary and the
particle-count schedule tends to infinity. -/
theorem partialRefreshPopulationDeviationProbability_tendsto_zero_varying_time_of_count_tendsto
    [Nonempty Sample]
    (refreshProbability : ℝ)
    (hprob0 : 0 < refreshProbability) (hprob1 : refreshProbability ≤ 1)
    (initial law : Distribution Sample) (score : Sample → ℝ)
    {tolerance : ℝ} (htolerance : 0 < tolerance)
    (extra time : ℕ → ℕ)
    (hextra : Filter.Tendsto extra Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun index =>
      bootstrapPopulationDeviationProbability initial
        (List.replicate (time index)
          (partialRefreshStep refreshProbability hprob0.le hprob1 law))
        score (extra index) tolerance)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero
    (g := fun index =>
      partialRefreshPopulationMSEByExtra refreshProbability hprob0.le hprob1
        initial law score (extra index) (time index) / tolerance ^ 2)
  · intro index
    exact bootstrapPopulationDeviationProbability_nonneg initial _ score _ _
  · intro index
    simpa [partialRefreshPopulationMSEByExtra,
      bootstrapPopulationMSEByExtra] using
      bootstrapPopulationDeviationProbability_le_mse initial
        (List.replicate (time index)
          (partialRefreshStep refreshProbability hprob0.le hprob1 law))
        score (extra index) htolerance
  · simpa using
      (partialRefreshPopulationMSEByExtra_tendsto_zero_varying_time_of_count_tendsto
        refreshProbability hprob0 hprob1 initial law score extra time hextra).div_const
          (tolerance ^ 2)

/-! ### Time-inhomogeneous partial refresh -/

/-- A genuinely time-varying finite Feynman--Kac schedule. Stage `n` refreshes
with probability `refreshProbability n`; constant potentials isolate the
effect of the inhomogeneous mutation kernels. -/
def varyingPartialRefreshSteps (refreshProbability : ℕ → ℝ)
    (hprob0 : ∀ n, 0 ≤ refreshProbability n)
    (hprob1 : ∀ n, refreshProbability n ≤ 1)
    (law : Distribution Sample) : ℕ → List (FeynmanKacStep Sample)
  | 0 => []
  | n + 1 => varyingPartialRefreshSteps refreshProbability hprob0 hprob1 law n ++
      [partialRefreshStep (refreshProbability n) (hprob0 n) (hprob1 n) law]

/-- Actual dependent-population MSE for the inhomogeneous schedule. -/
noncomputable def varyingPartialRefreshPopulationMSEByExtra
    (refreshProbability : ℕ → ℝ)
    (hprob0 : ∀ n, 0 ≤ refreshProbability n)
    (hprob1 : ∀ n, refreshProbability n ≤ 1)
    (initial law : Distribution Sample) (score : Sample → ℝ)
    (extra time : ℕ) : ℝ :=
  finiteExpectation
    (bootstrapPopulationLaw (Particle := Fin (extra + 1)) initial
      (varyingPartialRefreshSteps refreshProbability hprob0 hprob1 law time))
    (fun particles =>
      (particleAverage score particles -
        finiteExpectation
          (bootstrapTargetLaw initial
            (varyingPartialRefreshSteps refreshProbability hprob0 hprob1 law time))
          score) ^ 2)

theorem varyingPartialRefreshPopulationMSEByExtra_nonneg
    (refreshProbability : ℕ → ℝ)
    (hprob0 : ∀ n, 0 ≤ refreshProbability n)
    (hprob1 : ∀ n, refreshProbability n ≤ 1)
    (initial law : Distribution Sample) (score : Sample → ℝ)
    (extra time : ℕ) :
    0 ≤ varyingPartialRefreshPopulationMSEByExtra refreshProbability hprob0 hprob1
      initial law score extra time := by
  unfold varyingPartialRefreshPopulationMSEByExtra finiteExpectation
  apply Finset.sum_nonneg
  intro particles _
  exact mul_nonneg
    ((bootstrapPopulationLaw (Particle := Fin (extra + 1)) initial
      (varyingPartialRefreshSteps refreshProbability hprob0 hprob1 law time)).nonneg
        particles)
    (sq_nonneg _)

/-- Uniform `C/N` control for arbitrary time-inhomogeneous refresh schedules
whose refresh probabilities share one positive lower bound. -/
theorem varyingPartialRefreshPopulationMSEByExtra_le_uniform
    [Nonempty Sample]
    (refreshProbability : ℕ → ℝ) (minimumRefresh : ℝ)
    (hminimum0 : 0 < minimumRefresh)
    (hprobLower : ∀ n, minimumRefresh ≤ refreshProbability n)
    (hprob1 : ∀ n, refreshProbability n ≤ 1)
    (initial law : Distribution Sample) (score : Sample → ℝ)
    (extra time : ℕ) :
    varyingPartialRefreshPopulationMSEByExtra refreshProbability
        (fun n => (hminimum0.le.trans (hprobLower n))) hprob1
        initial law score extra time ≤
      (finiteVariance initial score +
          (8 * finiteFunctionAbsMaximum score ^ 2) /
            (1 - (1 - minimumRefresh) ^ 2)) /
        ((extra : ℝ) + 1) := by
  let hprob0 : ∀ n, 0 ≤ refreshProbability n :=
    fun n => hminimum0.le.trans (hprobLower n)
  let error : ℕ → ℕ → ℝ := fun extra time =>
    varyingPartialRefreshPopulationMSEByExtra refreshProbability hprob0 hprob1
      initial law score extra time
  let rate : ℕ → ℝ := fun n => (1 - refreshProbability n) ^ 2
  let noise : ℕ → ℝ := fun _ => 8 * finiteFunctionAbsMaximum score ^ 2
  have hminimum1 : minimumRefresh ≤ 1 :=
    (hprobLower 0).trans (hprob1 0)
  have hrateUpper : ∀ n, rate n ≤ (1 - minimumRefresh) ^ 2 := by
    intro n
    dsimp [rate]
    have hleft : 0 ≤ 1 - refreshProbability n := by linarith [hprob1 n]
    have hright : 1 - refreshProbability n ≤ 1 - minimumRefresh := by
      linarith [hprobLower n]
    nlinarith [sq_nonneg ((1 - minimumRefresh) -
      (1 - refreshProbability n))]
  have hrateUpperOne : (1 - minimumRefresh) ^ 2 < 1 :=
    partialRefresh_sq_rate_lt_one minimumRefresh hminimum0 hminimum1
  have hinitial : ∀ count,
      error count 0 ≤ finiteVariance initial score / ((count : ℝ) + 1) := by
    intro count
    unfold error varyingPartialRefreshPopulationMSEByExtra
    change (∑ samples : Fin (count + 1) → Sample,
      (iidPopulation initial).mass samples *
        (particleAverage score samples - finiteExpectation initial score) ^ 2) ≤ _
    rw [iidPopulation_particleAverage_mse]
    simp
  have hstep : ∀ count n,
      error count (n + 1) ≤ rate n * error count n +
        noise n / ((count : ℝ) + 1) := by
    intro count n
    let prior := varyingPartialRefreshSteps refreshProbability hprob0 hprob1 law n
    let step := partialRefreshStep (refreshProbability n) (hprob0 n) (hprob1 n) law
    change varyingPartialRefreshPopulationMSEByExtra refreshProbability hprob0 hprob1
      initial law score count (n + 1) ≤ _
    unfold varyingPartialRefreshPopulationMSEByExtra
    rw [varyingPartialRefreshSteps, bootstrapPopulationLaw_append_singleton,
      bootstrapTargetLaw_append_singleton]
    have h := bootstrapPopulationUpdate_partialRefresh_mse_le
      (Particle := Fin (count + 1)) (refreshProbability n) (hprob0 n) (hprob1 n)
      (bootstrapPopulationLaw initial prior) (bootstrapTargetLaw initial prior)
      law score
    simpa [error, rate, noise, prior, step,
      varyingPartialRefreshPopulationMSEByExtra] using h
  exact sequential_error_le_uniform_inverse_count_of_varying error rate noise
    hrateUpper (sq_nonneg _) hrateUpperOne (fun _ => le_rfl)
    (finiteVariance_nonneg _ _)
    (mul_nonneg (by norm_num) (sq_nonneg _))
    (varyingPartialRefreshPopulationMSEByExtra_nonneg refreshProbability hprob0
      hprob1 initial law score) hinitial hstep extra time

/-- Particle consistency holds along arbitrary horizon schedules even when the
refresh probability changes at every stage, provided its positive lower bound
is uniform and the particle count tends to infinity. -/
theorem varyingPartialRefreshPopulationMSEByExtra_tendsto_zero
    [Nonempty Sample]
    (refreshProbability : ℕ → ℝ) (minimumRefresh : ℝ)
    (hminimum0 : 0 < minimumRefresh)
    (hprobLower : ∀ n, minimumRefresh ≤ refreshProbability n)
    (hprob1 : ∀ n, refreshProbability n ≤ 1)
    (initial law : Distribution Sample) (score : Sample → ℝ)
    (extra time : ℕ → ℕ)
    (hextra : Filter.Tendsto extra Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun index =>
      varyingPartialRefreshPopulationMSEByExtra refreshProbability
        (fun n => hminimum0.le.trans (hprobLower n)) hprob1 initial law score
        (extra index) (time index)) Filter.atTop (nhds 0) := by
  exact tendsto_zero_varying_horizon_of_uniform_inverse_count _ _
    (varyingPartialRefreshPopulationMSEByExtra_nonneg refreshProbability
      (fun n => hminimum0.le.trans (hprobLower n)) hprob1 initial law score)
    (varyingPartialRefreshPopulationMSEByExtra_le_uniform refreshProbability
      minimumRefresh hminimum0 hprobLower hprob1 initial law score)
    extra time hextra

end Mcmc.Examples.UniformRefreshSMC
