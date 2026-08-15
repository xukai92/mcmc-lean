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
/-- The expected empirical average of an iid population equals the
single-particle expectation. -/
theorem iidPopulation_particleAverage_expectation
    (law : Distribution Sample) (score : Sample → ℝ) :
    ∑ samples : Particle → Sample, (iidPopulation law).mass samples *
        particleAverage score samples =
      ∑ s, law.mass s * score s := by
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
    _ = (∑ _i : Particle, ∑ s, law.mass s * score s) /
        Fintype.card Particle := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [iidPopulation_coordinate_expectation law score i]
    _ = ∑ s, law.mass s * score s := by
      simp [hcard]

omit [DecidableEq Sample] in
/-- The average of iid nonnegative unit-mean scores is again unit mean. -/
theorem iidPopulation_particleAverage_unbiased
    (law : Distribution Sample) (score : Sample → ℝ)
    (hunbiased : ∑ s, law.mass s * score s = 1) :
    ∑ samples : Particle → Sample, (iidPopulation law).mass samples *
        particleAverage score samples = 1 := by
  rw [iidPopulation_particleAverage_expectation law score, hunbiased]

/-- Multinomial resampling draws each new ancestor independently from the
normalized weights. -/
def multinomialResampling (weights : Distribution Particle) :
    Distribution (Particle → Particle) :=
  iidPopulation weights

omit [Fintype Sample] [DecidableEq Sample] in
/-- Conditional unbiasedness of multinomial resampling: the expected average
of any observable over the resampled population equals its current weighted
empirical average. -/
theorem multinomialResampling_unbiased
    (weights : Distribution Particle) (particles : Particle → Sample)
    (observable : Sample → ℝ) :
    ∑ ancestors, (multinomialResampling weights).mass ancestors *
        particleAverage (fun i => observable (particles i)) ancestors =
      ∑ i, weights.mass i * observable (particles i) := by
  exact iidPopulation_particleAverage_expectation weights
    (fun i => observable (particles i))

/-- Independent, not necessarily identically distributed, finite population.
This is the conditional propagation law after ancestor indices are fixed. -/
def independentPopulation (law : Particle → Distribution Sample) :
    Distribution (Particle → Sample) where
  mass samples := ∏ i, (law i).mass (samples i)
  nonneg samples := Finset.prod_nonneg fun i _ => (law i).nonneg (samples i)
  sum_mass := by
    rw [← Fintype.prod_sum]
    simp [Distribution.sum_mass]

/-- Point mass as an elementary finite distribution. -/
def pointDistribution (value : Sample) : Distribution Sample where
  mass sample := if sample = value then 1 else 0
  nonneg sample := by split <;> norm_num
  sum_mass := by simp

/-- Independent population with one distinguished coordinate forced to a
specified value. All other coordinates retain their supplied laws. This is
the elementary initialization/propagation law used by conditional SMC. -/
def forcedIndependentPopulation (law : Particle → Distribution Sample)
    (retained : Particle) (value : Sample) : Distribution (Particle → Sample) :=
  independentPopulation fun i =>
    if i = retained then pointDistribution value else law i

omit [Nonempty Particle] in
theorem forcedIndependentPopulation_incompatible_zero
    (law : Particle → Distribution Sample) (retained : Particle) (value : Sample)
    (samples : Particle → Sample) (h : samples retained ≠ value) :
    (forcedIndependentPopulation law retained value).mass samples = 0 := by
  unfold forcedIndependentPopulation independentPopulation
  apply Finset.prod_eq_zero (Finset.mem_univ retained)
  simp [pointDistribution, h]

omit [Nonempty Particle] in
/-- The forced coordinate equals the retained value almost surely. -/
theorem forcedIndependentPopulation_coordinate_probability
    (law : Particle → Distribution Sample) (retained : Particle) (value : Sample) :
    ∑ samples, (forcedIndependentPopulation law retained value).mass samples *
      (if samples retained = value then 1 else 0) = 1 := by
  rw [show (∑ samples, (forcedIndependentPopulation law retained value).mass samples *
      (if samples retained = value then 1 else 0)) =
      ∑ samples, (forcedIndependentPopulation law retained value).mass samples by
    apply Finset.sum_congr rfl
    intro samples _
    by_cases h : samples retained = value
    · simp [h]
    · rw [forcedIndependentPopulation_incompatible_zero law retained value samples h]
      simp]
  exact (forcedIndependentPopulation law retained value).sum_mass

omit [DecidableEq Sample] [Nonempty Particle] in
/-- Each coordinate of an independently propagated population has its
specified transition law. -/
theorem independentPopulation_coordinate_expectation
    (law : Particle → Distribution Sample) (score : Sample → ℝ)
    (i : Particle) :
    ∑ samples, (independentPopulation law).mass samples * score (samples i) =
      ∑ s, (law i).mass s * score s := by
  classical
  calc
    ∑ samples, (independentPopulation law).mass samples * score (samples i) =
        ∑ samples : Particle → Sample,
          ∏ j, if j = i then (law j).mass (samples j) * score (samples j)
          else (law j).mass (samples j) := by
      apply Finset.sum_congr rfl
      intro samples _
      rw [independentPopulation]
      calc
        (∏ j, (law j).mass (samples j)) * score (samples i) =
            ∏ j, (law j).mass (samples j) *
              (if j = i then score (samples i) else 1) := by
          rw [Finset.prod_mul_distrib]
          simp
        _ = ∏ j, if j = i then (law j).mass (samples j) * score (samples j)
              else (law j).mass (samples j) := by
          apply Finset.prod_congr rfl
          intro j _
          by_cases hji : j = i <;> simp [hji]
    _ = ∏ j : Particle, ∑ s, if j = i then (law j).mass s * score s
          else (law j).mass s := by
      exact (Fintype.prod_sum
        (f := fun j : Particle => fun s : Sample =>
          if j = i then (law j).mass s * score s else (law j).mass s)).symm
    _ = ∑ s, (law i).mass s * score s := by
      simp [Distribution.sum_mass]

omit [DecidableEq Sample] [Nonempty Particle] in
/-- Expected empirical average after independent heterogeneous propagation. -/
theorem independentPopulation_particleAverage_expectation
    (law : Particle → Distribution Sample) (score : Sample → ℝ) :
    ∑ samples, (independentPopulation law).mass samples *
        particleAverage score samples =
      (∑ i, ∑ s, (law i).mass s * score s) / Fintype.card Particle := by
  classical
  unfold particleAverage
  calc
    ∑ samples : Particle → Sample, (independentPopulation law).mass samples *
          ((∑ i, score (samples i)) / Fintype.card Particle) =
        (∑ i, ∑ samples : Particle → Sample,
          (independentPopulation law).mass samples * score (samples i)) /
            Fintype.card Particle := by
      simp_rw [div_eq_mul_inv, ← mul_assoc, Finset.mul_sum]
      rw [← Finset.sum_mul]
      congr 1
      rw [Finset.sum_comm]
    _ = (∑ i, ∑ s, (law i).mass s * score s) /
          Fintype.card Particle := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [independentPopulation_coordinate_expectation law score i]

/-- A row of a finite Markov kernel as a finite distribution. -/
def rowDistribution (transition : MarkovKernel Sample) (x : Sample) :
    Distribution Sample where
  mass y := transition.prob x y
  nonneg y := transition.nonneg x y
  sum_mass := transition.sum_prob x

/-- Conditional propagation law after a vector of ancestor indices has been
drawn. -/
def propagatedPopulation (transition : MarkovKernel Sample)
    (particles : Particle → Sample) (ancestors : Particle → Particle) :
    Distribution (Particle → Sample) :=
  independentPopulation fun j => rowDistribution transition (particles (ancestors j))

omit [DecidableEq Sample] in
/-- One-step bootstrap resample--propagate identity.  Conditional expectation
of the next empirical average is the current normalized weighted average of
the transition expectation. -/
theorem resamplePropagate_particleAverage_expectation
    (weights : Distribution Particle) (particles : Particle → Sample)
    (transition : MarkovKernel Sample) (observable : Sample → ℝ) :
    ∑ ancestors, (multinomialResampling weights).mass ancestors *
        (∑ next, (propagatedPopulation transition particles ancestors).mass next *
          particleAverage observable next) =
      ∑ i, weights.mass i *
        (∑ y, transition.prob (particles i) y * observable y) := by
  simp_rw [propagatedPopulation,
    independentPopulation_particleAverage_expectation]
  change ∑ ancestors, (multinomialResampling weights).mass ancestors *
      particleAverage
        (fun i => ∑ y, transition.prob (particles i) y * observable y)
        ancestors = _
  exact multinomialResampling_unbiased weights particles
    (fun x => ∑ y, transition.prob x y * observable y)

/-- Normalized empirical potential weights. Strict positivity is a convenient
finite prerequisite; support-sensitive zero handling can be added separately. -/
noncomputable def normalizedPotentialWeights
    (potential : Sample → ℝ) (hpotential : ∀ x, 0 < potential x)
    (particles : Particle → Sample) : Distribution Particle where
  mass i := potential (particles i) / ∑ j, potential (particles j)
  nonneg i := div_nonneg (le_of_lt (hpotential _))
    (Finset.sum_nonneg fun j _ => le_of_lt (hpotential (particles j)))
  sum_mass := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (Finset.sum_pos
      (fun j _ => hpotential (particles j)) Finset.univ_nonempty))

omit [DecidableEq Sample] in
/-- Multiplying the normalized resample--propagate expectation by the current
average potential cancels the empirical normalizer. This is the local
Feynman--Kac identity used in the multi-time induction. -/
theorem weighted_resamplePropagate_identity
    (potential : Sample → ℝ) (hpotential : ∀ x, 0 < potential x)
    (particles : Particle → Sample) (transition : MarkovKernel Sample)
    (observable : Sample → ℝ) :
    particleAverage potential particles *
        (∑ ancestors,
          (multinomialResampling
            (normalizedPotentialWeights potential hpotential particles)).mass ancestors *
          (∑ next, (propagatedPopulation transition particles ancestors).mass next *
            particleAverage observable next)) =
      particleAverage
        (fun x => potential x *
          ∑ y, transition.prob x y * observable y) particles := by
  rw [resamplePropagate_particleAverage_expectation]
  unfold particleAverage normalizedPotentialWeights
  have hsum : (∑ j, potential (particles j)) ≠ 0 :=
    ne_of_gt (Finset.sum_pos (fun j _ => hpotential (particles j))
      Finset.univ_nonempty)
  have hcard : (Fintype.card Particle : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  change ((∑ i, potential (particles i)) / Fintype.card Particle) *
      (∑ i, (potential (particles i) / ∑ j, potential (particles j)) *
        ∑ y, transition.prob (particles i) y * observable y) =
    (∑ i, potential (particles i) *
      ∑ y, transition.prob (particles i) y * observable y) /
        Fintype.card Particle
  field_simp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  field_simp

/-- One-particle unnormalized Feynman--Kac transform. -/
noncomputable def feynmanKacTransform (potential : Sample → ℝ)
    (transition : MarkovKernel Sample) (observable : Sample → ℝ) : Sample → ℝ :=
  fun x => potential x * ∑ y, transition.prob x y * observable y

/-- Particle Feynman--Kac transform: multiply the conditional expectation
after multinomial resample--propagate by the current average potential. -/
noncomputable def particleFeynmanKacTransform
    (potential : Sample → ℝ) (hpotential : ∀ x, 0 < potential x)
    (transition : MarkovKernel Sample)
    (observable : (Particle → Sample) → ℝ) : (Particle → Sample) → ℝ :=
  fun particles => particleAverage potential particles *
    ∑ ancestors,
      (multinomialResampling
        (normalizedPotentialWeights potential hpotential particles)).mass ancestors *
      ∑ next, (propagatedPopulation transition particles ancestors).mass next *
        observable next

omit [DecidableEq Sample] in
/-- The particle transform maps an empirical average to the empirical average
of the exact one-particle Feynman--Kac transform. -/
theorem particleFeynmanKacTransform_particleAverage
    (potential : Sample → ℝ) (hpotential : ∀ x, 0 < potential x)
    (transition : MarkovKernel Sample) (observable : Sample → ℝ)
    (particles : Particle → Sample) :
    particleFeynmanKacTransform potential hpotential transition
        (particleAverage observable) particles =
      particleAverage (feynmanKacTransform potential transition observable)
        particles := by
  exact weighted_resamplePropagate_identity potential hpotential particles
    transition observable

omit [DecidableEq Sample] in
/-- Arbitrary finite-horizon Feynman--Kac identity, conditional on the initial
particle cloud. Iteration expands to the usual product of successive average
potentials and nested resample--propagate expectations. -/
theorem particleFeynmanKacTransform_iterate
    (potential : Sample → ℝ) (hpotential : ∀ x, 0 < potential x)
    (transition : MarkovKernel Sample) (observable : Sample → ℝ)
    (n : ℕ) (particles : Particle → Sample) :
    (particleFeynmanKacTransform potential hpotential transition)^[n]
        (particleAverage observable) particles =
      particleAverage ((feynmanKacTransform potential transition)^[n] observable)
        particles := by
  induction n generalizing observable with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      have hmap :
          particleFeynmanKacTransform potential hpotential transition
              (particleAverage (Particle := Particle) observable) =
            particleAverage (Particle := Particle)
              (feynmanKacTransform potential transition observable) := by
        funext cloud
        exact particleFeynmanKacTransform_particleAverage potential hpotential
          transition observable cloud
      rw [hmap]
      exact ih (feynmanKacTransform potential transition observable)

omit [DecidableEq Sample] in
/-- After an iid initial cloud, the finite-horizon particle normalizing
estimator has exactly the corresponding one-particle Feynman--Kac expectation. -/
theorem iid_particleFeynmanKacTransform_iterate_expectation
    (initial : Distribution Sample) (potential : Sample → ℝ)
    (hpotential : ∀ x, 0 < potential x) (transition : MarkovKernel Sample)
    (observable : Sample → ℝ) (n : ℕ) :
    ∑ particles, (iidPopulation (Particle := Particle) initial).mass particles *
        ((particleFeynmanKacTransform potential hpotential transition)^[n]
          (particleAverage observable) particles) =
      ∑ x, initial.mass x *
        ((feynmanKacTransform potential transition)^[n] observable) x := by
  simp_rw [particleFeynmanKacTransform_iterate potential hpotential transition
    observable n]
  exact iidPopulation_particleAverage_expectation initial _

/-- One time step of a finite, possibly time-inhomogeneous Feynman--Kac
model. Strictly positive potentials make multinomial normalization total. -/
structure FeynmanKacStep (Sample : Type*) [Fintype Sample] where
  potential : Sample → ℝ
  potential_pos : ∀ x, 0 < potential x
  transition : MarkovKernel Sample

/-- Backward composition of a time-varying sequence of exact one-particle
Feynman--Kac transforms. -/
noncomputable def feynmanKacSequence :
    List (FeynmanKacStep Sample) → (Sample → ℝ) → Sample → ℝ
  | [], observable => observable
  | step :: steps, observable =>
      feynmanKacTransform step.potential step.transition
        (feynmanKacSequence steps observable)

/-- Matching time-varying particle transform, expressed as nested conditional
resample--propagate expectations. -/
noncomputable def particleFeynmanKacSequence :
    List (FeynmanKacStep Sample) →
      ((Particle → Sample) → ℝ) → (Particle → Sample) → ℝ
  | [], observable => observable
  | step :: steps, observable =>
      particleFeynmanKacTransform step.potential step.potential_pos
        step.transition (particleFeynmanKacSequence steps observable)

omit [DecidableEq Sample] in
/-- Time-inhomogeneous finite-horizon SMC expectation identity, conditional on
the initial cloud. -/
theorem particleFeynmanKacSequence_particleAverage
    (steps : List (FeynmanKacStep Sample)) (observable : Sample → ℝ) :
    particleFeynmanKacSequence (Particle := Particle) steps
        (particleAverage observable) =
      particleAverage (feynmanKacSequence steps observable) := by
  induction steps with
  | nil => rfl
  | cons step steps ih =>
      rw [particleFeynmanKacSequence, feynmanKacSequence, ih]
      funext particles
      exact particleFeynmanKacTransform_particleAverage step.potential
        step.potential_pos step.transition _ particles

omit [DecidableEq Sample] in
/-- An iid initial population turns the time-inhomogeneous particle sequence
into exactly the corresponding one-particle Feynman--Kac expectation. -/
theorem iid_particleFeynmanKacSequence_expectation
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (observable : Sample → ℝ) :
    ∑ particles, (iidPopulation (Particle := Particle) initial).mass particles *
        particleFeynmanKacSequence (Particle := Particle) steps
          (particleAverage observable) particles =
      ∑ x, initial.mass x * feynmanKacSequence steps observable x := by
  rw [particleFeynmanKacSequence_particleAverage steps observable]
  exact iidPopulation_particleAverage_expectation initial _

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
