import Mcmc.Finite.ParticleEstimator
import Mcmc.Finite.Conditional
import Mcmc.Finite.Gibbs
import Mathlib.Tactic

/-!
# Explicit finite sequential Monte Carlo histories

This module realizes the nested Feynman--Kac expectations from
`ParticleEstimator` as a finite distribution over every multinomial ancestor
choice and propagated population.  The construction is deliberately finite
and uses strictly positive potentials, matching the normalization assumptions
of the existing transform theorem.
-/

open scoped BigOperators

namespace Mcmc.Finite.SequentialMonteCarlo

open MarkovKernel ParticleEstimator

variable {Sample Particle : Type*}
  [Fintype Sample] [Fintype Particle]
  [DecidableEq Sample] [DecidableEq Particle] [Nonempty Particle]

abbrev Population := Particle → Sample
abbrev Ancestors := Particle → Particle

universe u v

instance uliftUnitDecidableEq.{w} : DecidableEq (ULift.{w} Unit) := fun x y => by
  cases x with
  | up x =>
      cases x
      cases y with
      | up y => cases y; exact isTrue rfl

instance uliftUnitFintype.{w} : Fintype (ULift.{w} Unit) where
  elems := {ULift.up ()}
  complete x := by rcases x with ⟨x⟩; cases x; simp

/-- The future ancestry and populations associated with a list of SMC steps.
The current population is supplied separately. -/
def Continuation (Particle : Type u) (Sample : Type v) [Fintype Sample] :
    List (FeynmanKacStep Sample) → Type (max u v)
  | [] => ULift Unit
  | _ :: steps => (Particle → Particle) × (Particle → Sample) ×
      Continuation Particle Sample steps

instance continuationFintype (steps : List (FeynmanKacStep Sample)) :
    Fintype (Continuation Particle Sample steps) := by
  induction steps with
  | nil => exact uliftUnitFintype
  | cons step steps ih =>
      simp only [Continuation]
      infer_instance

instance continuationDecidableEq (steps : List (FeynmanKacStep Sample)) :
    DecidableEq (Continuation Particle Sample steps) := by
  induction steps with
  | nil => exact uliftUnitDecidableEq
  | cons step steps ih =>
      simp only [Continuation]
      infer_instance

/-- Conditional law of all future ancestry choices and populations, given the
current population. -/
noncomputable def continuationLaw :
    (steps : List (FeynmanKacStep Sample)) → (Particle → Sample) →
      Distribution (Continuation Particle Sample steps)
  | [], _ =>
      { mass := fun _ => 1
        nonneg := fun _ => by norm_num
        sum_mass := by simp [Continuation] }
  | step :: steps, particles =>
      { mass := fun history =>
          (multinomialResampling
            (normalizedPotentialWeights step.potential step.potential_pos particles)).mass
              history.1 *
          (propagatedPopulation step.transition particles history.1).mass history.2.1 *
          (continuationLaw steps history.2.1).mass history.2.2
        nonneg := fun history => mul_nonneg
          (mul_nonneg
            ((multinomialResampling
              (normalizedPotentialWeights step.potential step.potential_pos particles)).nonneg
                history.1)
            ((propagatedPopulation step.transition particles history.1).nonneg history.2.1))
          ((continuationLaw steps history.2.1).nonneg history.2.2)
        sum_mass := by
          change ∑ history : (Particle → Particle) × (Particle → Sample) ×
              Continuation Particle Sample steps,
            (multinomialResampling
              (normalizedPotentialWeights step.potential step.potential_pos particles)).mass
                history.1 *
            (propagatedPopulation step.transition particles history.1).mass history.2.1 *
            (continuationLaw steps history.2.1).mass history.2.2 = 1
          rw [Fintype.sum_prod_type]
          simp_rw [Fintype.sum_prod_type]
          simp_rw [← Finset.mul_sum,
            (continuationLaw steps _).sum_mass, mul_one]
          simp_rw [← Finset.mul_sum,
            (propagatedPopulation step.transition particles _).sum_mass, mul_one]
          exact (multinomialResampling
            (normalizedPotentialWeights step.potential step.potential_pos particles)).sum_mass }

/-- Every propagation matrix in a finite Feynman--Kac schedule has full
support. Potentials are already strictly positive by construction. -/
def FeynmanKacFullSupport : List (FeynmanKacStep Sample) → Prop
  | [] => True
  | step :: steps =>
      (∀ x y, 0 < step.transition.prob x y) ∧ FeynmanKacFullSupport steps

omit [DecidableEq Sample] in
/-- Under full-support transitions, every explicit SMC continuation history
has positive probability. -/
theorem continuationLaw_mass_pos
    (steps : List (FeynmanKacStep Sample))
    (hsupport : FeynmanKacFullSupport steps)
    (particles : Particle → Sample)
    (history : Continuation Particle Sample steps) :
    0 < (continuationLaw steps particles).mass history := by
  induction steps generalizing particles with
  | nil => simp [continuationLaw]
  | cons step steps ih =>
      simp only [FeynmanKacFullSupport] at hsupport
      unfold continuationLaw
      exact mul_pos
        (mul_pos
          (multinomialResampling_mass_pos _
            (normalizedPotentialWeights_mass_pos step.potential
              step.potential_pos particles) history.1)
          (propagatedPopulation_mass_pos step.transition hsupport.1
            particles history.1 history.2.1))
        (ih hsupport.2 history.2.1 history.2.2)

/-- Product of average potentials along a concrete SMC history, followed by
the empirical terminal observable. -/
noncomputable def historyValue :
    (steps : List (FeynmanKacStep Sample)) → (Sample → ℝ) → (Particle → Sample) →
      Continuation Particle Sample steps → ℝ
  | [], observable, particles, _ => particleAverage observable particles
  | step :: steps, observable, particles, history =>
      particleAverage step.potential particles *
        historyValue steps observable history.2.1 history.2.2

omit [DecidableEq Sample] in
/-- The explicit ancestry-history law realizes the nested conditional particle
Feynman--Kac transform exactly. -/
theorem continuationLaw_historyValue_expectation
    (steps : List (FeynmanKacStep Sample)) (observable : Sample → ℝ)
    (particles : Particle → Sample) :
    ∑ history, (continuationLaw (Particle := Particle) steps particles).mass history *
        historyValue steps observable particles history =
      particleFeynmanKacSequence (Particle := Particle) steps
        (particleAverage observable) particles := by
  induction steps generalizing particles with
  | nil => simp [continuationLaw, historyValue, particleFeynmanKacSequence,
      Continuation]
  | cons step steps ih =>
      rw [particleFeynmanKacSequence]
      unfold particleFeynmanKacTransform
      change
        (∑ history : (Particle → Particle) × (Particle → Sample) ×
            Continuation Particle Sample steps,
          ((multinomialResampling
            (normalizedPotentialWeights step.potential step.potential_pos particles)).mass
              history.1 *
            (propagatedPopulation step.transition particles history.1).mass history.2.1 *
            (continuationLaw steps history.2.1).mass history.2.2) *
          (particleAverage step.potential particles *
            historyValue steps observable history.2.1 history.2.2)) = _
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      simp_rw [show ∀ (a : Particle → Particle) (next : Particle → Sample)
          (tail : Continuation Particle Sample steps),
          ((multinomialResampling
              (normalizedPotentialWeights step.potential step.potential_pos particles)).mass a *
            (propagatedPopulation step.transition particles a).mass next *
            (continuationLaw steps next).mass tail) *
            (particleAverage step.potential particles *
              historyValue steps observable next tail) =
          particleAverage step.potential particles *
            (multinomialResampling
              (normalizedPotentialWeights step.potential step.potential_pos particles)).mass a *
            ((propagatedPopulation step.transition particles a).mass next *
              ((continuationLaw steps next).mass tail *
                historyValue steps observable next tail)) by
            intro a next tail; ring]
      simp_rw [← Finset.mul_sum, ih]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ancestors _
      ring

/-- Complete finite SMC history: the iid initial population followed by all
ancestor choices and propagated populations. -/
abbrev History (steps : List (FeynmanKacStep Sample)) :=
  (Particle → Sample) × Continuation Particle Sample steps

/-- Continuation histories depend only on the number of steps, not on the
potential or transition values stored in those steps. -/
noncomputable def continuationEquivOfLength
    (left right : List (FeynmanKacStep Sample)) (hlen : left.length = right.length) :
    Continuation Particle Sample left ≃ Continuation Particle Sample right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => exact Equiv.refl _
      | cons step right => simp at hlen
  | cons step left ih =>
      cases right with
      | nil => simp at hlen
      | cons other right =>
          simp only [Continuation]
          exact Equiv.prodCongr (Equiv.refl _)
            (Equiv.prodCongr (Equiv.refl _) (ih right (by simpa using hlen)))

/-- Complete histories for schedules of equal length are canonically
equivalent. -/
noncomputable def historyEquivOfLength
    (left right : List (FeynmanKacStep Sample)) (hlen : left.length = right.length) :
    History (Particle := Particle) left ≃ History (Particle := Particle) right :=
  Equiv.prodCongr (Equiv.refl _)
    (continuationEquivOfLength (Particle := Particle) left right hlen)

/-- Relabel a finite distribution along an equivalence. -/
def relabelDistribution {α β : Type*} [Fintype α] [Fintype β]
    (law : Distribution α) (equiv : α ≃ β) : Distribution β where
  mass y := law.mass (equiv.symm y)
  nonneg y := law.nonneg (equiv.symm y)
  sum_mass := by
    rw [← law.sum_mass]
    exact (Fintype.sum_equiv equiv law.mass (fun y => law.mass (equiv.symm y))
      (fun x => by simp)).symm

/-- Probability law of a complete explicit SMC history. -/
noncomputable def historyLaw (initial : Distribution Sample)
    (steps : List (FeynmanKacStep Sample)) : Distribution (History (Particle := Particle) steps) where
  mass history := (iidPopulation (Particle := Particle) initial).mass history.1 *
    (continuationLaw steps history.1).mass history.2
  nonneg history := mul_nonneg
    ((iidPopulation (Particle := Particle) initial).nonneg history.1)
    ((continuationLaw steps history.1).nonneg history.2)
  sum_mass := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, (continuationLaw steps _).sum_mass, mul_one]
    exact (iidPopulation (Particle := Particle) initial).sum_mass

omit [DecidableEq Sample] in
/-- A full-support initial law and full-support propagation schedule give
positive probability to every explicit SMC history. -/
theorem historyLaw_mass_pos (initial : Distribution Sample)
    (hinitial : ∀ x, 0 < initial.mass x)
    (steps : List (FeynmanKacStep Sample))
    (hsupport : FeynmanKacFullSupport steps)
    (history : History (Particle := Particle) steps) :
    0 < (historyLaw (Particle := Particle) initial steps).mass history := by
  exact mul_pos (iidPopulation_mass_pos initial hinitial history.1)
    (continuationLaw_mass_pos steps hsupport history.1 history.2)

/-- Concrete product-of-average-potentials estimator with a terminal empirical
observable. -/
noncomputable def fullHistoryValue (steps : List (FeynmanKacStep Sample))
    (observable : Sample → ℝ) (history : History (Particle := Particle) steps) : ℝ :=
  historyValue steps observable history.1 history.2

omit [DecidableEq Sample] in
/-- Expectation under the explicit finite history law equals the exact
one-particle Feynman--Kac expectation. -/
theorem historyLaw_value_expectation (initial : Distribution Sample)
    (steps : List (FeynmanKacStep Sample)) (observable : Sample → ℝ) :
    ∑ history, (historyLaw (Particle := Particle) initial steps).mass history *
        fullHistoryValue steps observable history =
      ∑ x, initial.mass x * feynmanKacSequence steps observable x := by
  rw [Fintype.sum_prod_type]
  change ∑ particles, ∑ continuation,
      ((iidPopulation (Particle := Particle) initial).mass particles *
        (continuationLaw steps particles).mass continuation) *
        historyValue steps observable particles continuation = _
  simp_rw [show ∀ (particles : Particle → Sample)
      (continuation : Continuation Particle Sample steps),
      ((iidPopulation (Particle := Particle) initial).mass particles *
        (continuationLaw steps particles).mass continuation) *
          historyValue steps observable particles continuation =
        (iidPopulation (Particle := Particle) initial).mass particles *
          ((continuationLaw steps particles).mass continuation *
            historyValue steps observable particles continuation) by
      intro particles continuation; ring,
    ← Finset.mul_sum, continuationLaw_historyValue_expectation]
  exact iid_particleFeynmanKacSequence_expectation initial steps observable

/-- Exact normalizing constant represented by the finite Feynman--Kac model. -/
noncomputable def normalizingConstant (initial : Distribution Sample)
    (steps : List (FeynmanKacStep Sample)) : ℝ :=
  ∑ x, initial.mass x * feynmanKacSequence steps (fun _ => 1) x

/-- Concrete SMC normalizing-weight estimator on an explicit history. -/
noncomputable def normalizingWeight (steps : List (FeynmanKacStep Sample))
    (history : History (Particle := Particle) steps) : ℝ :=
  fullHistoryValue steps (fun _ => 1) history

omit [DecidableEq Sample] [DecidableEq Particle] in
theorem historyValue_nonneg
    (steps : List (FeynmanKacStep Sample)) (observable : Sample → ℝ)
    (hobservable : ∀ x, 0 ≤ observable x) (particles : Particle → Sample)
    (history : Continuation Particle Sample steps) :
    0 ≤ historyValue steps observable particles history := by
  induction steps generalizing particles with
  | nil => exact particleAverage_nonneg hobservable particles
  | cons step steps ih =>
      exact mul_nonneg (particleAverage_nonneg
        (fun x => le_of_lt (step.potential_pos x)) particles)
        (ih history.2.1 history.2.2)

omit [DecidableEq Sample] [DecidableEq Particle] in
theorem normalizingWeight_nonneg (steps : List (FeynmanKacStep Sample))
    (history : History (Particle := Particle) steps) :
    0 ≤ normalizingWeight steps history :=
  historyValue_nonneg steps (fun _ => 1) (fun _ => by norm_num)
    history.1 history.2

omit [DecidableEq Sample] [DecidableEq Particle] in
/-- Strictly positive potentials make every concrete SMC normalizing weight
positive. -/
theorem normalizingWeight_pos (steps : List (FeynmanKacStep Sample))
    (history : History (Particle := Particle) steps) :
    0 < normalizingWeight steps history := by
  unfold normalizingWeight fullHistoryValue
  induction steps with
  | nil =>
      exact particleAverage_pos (fun _ => by norm_num) history.1
  | cons step steps ih =>
      unfold historyValue
      exact mul_pos (particleAverage_pos step.potential_pos history.1)
        (ih (history.2.2.1, history.2.2.2))

omit [DecidableEq Sample] in
/-- The explicit SMC normalizing weight is unbiased for its exact finite
Feynman--Kac normalizing constant. -/
theorem normalizingWeight_expectation (initial : Distribution Sample)
    (steps : List (FeynmanKacStep Sample)) :
    ∑ history, (historyLaw (Particle := Particle) initial steps).mass history *
        normalizingWeight steps history = normalizingConstant initial steps := by
  exact historyLaw_value_expectation initial steps (fun _ => 1)

/-- Terminal population reached by a concrete ancestry/population history. -/
def terminalPopulation :
    (steps : List (FeynmanKacStep Sample)) → (Particle → Sample) →
      Continuation Particle Sample steps → Particle → Sample
  | [], particles, _ => particles
  | _ :: steps, _, history => terminalPopulation steps history.2.1 history.2.2

/-- Index in the current population ancestral to a selected terminal index. -/
def initialAncestor :
    (steps : List (FeynmanKacStep Sample)) →
      Continuation Particle Sample steps → Particle → Particle
  | [], _, terminal => terminal
  | _ :: steps, history, terminal =>
      history.1 (initialAncestor steps history.2.2 terminal)

/-- Full state trajectory obtained by tracing a selected terminal particle
backward through every stored ancestor map. -/
def selectedTrajectory :
    (steps : List (FeynmanKacStep Sample)) → (Particle → Sample) →
      Continuation Particle Sample steps → Particle → List Sample
  | [], particles, _, terminal => [particles terminal]
  | _ :: steps, particles, history, terminal =>
      particles (history.1 (initialAncestor steps history.2.2 terminal)) ::
        selectedTrajectory steps history.2.1 history.2.2 terminal

omit [Fintype Particle] [DecidableEq Sample] [DecidableEq Particle]
    [Nonempty Particle] in
/-- A selected genealogy contains one state per population. -/
theorem selectedTrajectory_length (steps : List (FeynmanKacStep Sample))
    (particles : Particle → Sample) (history : Continuation Particle Sample steps)
    (terminal : Particle) :
    (selectedTrajectory steps particles history terminal).length = steps.length + 1 := by
  induction steps generalizing particles with
  | nil => rfl
  | cons step steps ih =>
      simp only [selectedTrajectory, List.length_cons, List.length_cons]
      rw [ih]

omit [Fintype Particle] [DecidableEq Sample] [DecidableEq Particle]
    [Nonempty Particle] in
/-- The final state of the traced genealogy is the selected terminal particle. -/
theorem selectedTrajectory_getLast? (steps : List (FeynmanKacStep Sample))
    (particles : Particle → Sample) (history : Continuation Particle Sample steps)
    (terminal : Particle) :
    (selectedTrajectory steps particles history terminal).getLast? =
      some (terminalPopulation steps particles history terminal) := by
  induction steps generalizing particles with
  | nil => rfl
  | cons step steps ih =>
      unfold selectedTrajectory terminalPopulation
      have htail : selectedTrajectory steps history.2.1 history.2.2 terminal ≠ [] := by
        cases steps <;> simp [selectedTrajectory]
      rw [show particles (history.1 (initialAncestor steps history.2.2 terminal)) ::
          selectedTrajectory steps history.2.1 history.2.2 terminal =
        [particles (history.1 (initialAncestor steps history.2.2 terminal))] ++
          selectedTrajectory steps history.2.1 history.2.2 terminal by rfl,
        List.getLast?_append_of_ne_nil _ htail]
      exact ih history.2.1 history.2.2

omit [Fintype Particle] [DecidableEq Sample] [DecidableEq Particle]
    [Nonempty Particle] in
/-- The first state of the traced genealogy is the corresponding ancestor in
the initial population. -/
theorem selectedTrajectory_head? (steps : List (FeynmanKacStep Sample))
    (particles : Particle → Sample) (history : Continuation Particle Sample steps)
    (terminal : Particle) :
    (selectedTrajectory steps particles history terminal).head? =
      some (particles (initialAncestor steps history terminal)) := by
  cases steps <;> rfl

omit [DecidableEq Sample] in
/-- With exactly one particle, the selected genealogy determines the complete
SMC history and selected index.  This is the structural reason one-particle
particle Gibbs cannot move. -/
theorem selectedTrajectory_injective_unit
    (steps : List (FeynmanKacStep Sample)) :
    Function.Injective fun selected :
        History (Particle := Unit) steps × Unit =>
      selectedTrajectory steps selected.1.1 selected.1.2 selected.2 := by
  induction steps with
  | nil =>
      rintro ⟨⟨particles, continuation⟩, terminal⟩
        ⟨⟨particles', continuation'⟩, terminal'⟩ h
      have hparticles : particles = particles' := by
        funext i
        cases i
        simpa [selectedTrajectory] using congrArg List.head? h
      subst particles'
      have hcontinuation : continuation = continuation' := by
        rcases continuation with ⟨u⟩
        rcases continuation' with ⟨u'⟩
        cases u
        cases u'
        rfl
      have hterminal : terminal = terminal' := Subsingleton.elim _ _
      subst continuation'
      subst terminal'
      rfl
  | cons step steps ih =>
      rintro ⟨⟨particles, ancestors, nextParticles, tail⟩, terminal⟩
        ⟨⟨particles', ancestors', nextParticles', tail'⟩, terminal'⟩ h
      have hterminal : terminal = terminal' := Subsingleton.elim _ _
      subst terminal'
      have hancestors : ancestors = ancestors' := by
        funext i
        exact Subsingleton.elim _ _
      subst ancestors'
      have hparticles : particles = particles' := by
        funext i
        cases i
        have hhead := congrArg List.head? h
        simpa [selectedTrajectory, initialAncestor] using hhead
      subst particles'
      have htailTrajectory :
          selectedTrajectory steps nextParticles tail terminal =
            selectedTrajectory steps nextParticles' tail' terminal := by
        simpa [selectedTrajectory, initialAncestor] using congrArg List.tail h
      have hrest : ((nextParticles, tail), terminal) =
          ((nextParticles', tail'), terminal) := by
        apply ih
        exact htailTrajectory
      injection hrest with hhistory
      injection hhistory with hnext htail
      subst nextParticles'
      subst tail'
      rfl

omit [DecidableEq Sample] [Nonempty Particle] in
/-- Conditional propagation expectation for an observable of each selected
ancestor and its propagated child. -/
theorem propagatedPopulation_pairAverage_expectation
    (transition : MarkovKernel Sample) (particles : Particle → Sample)
    (ancestors : Particle → Particle) (observable : Sample → Sample → ℝ) :
    ∑ next, (propagatedPopulation transition particles ancestors).mass next *
        ((∑ i, observable (particles (ancestors i)) (next i)) /
          Fintype.card Particle) =
      (∑ i, ∑ y, transition.prob (particles (ancestors i)) y *
        observable (particles (ancestors i)) y) / Fintype.card Particle := by
  classical
  calc
    _ = (∑ i, ∑ next,
        (propagatedPopulation transition particles ancestors).mass next *
          observable (particles (ancestors i)) (next i)) /
        Fintype.card Particle := by
      simp_rw [div_eq_mul_inv, ← mul_assoc, Finset.mul_sum]
      rw [← Finset.sum_mul]
      congr 1
      rw [Finset.sum_comm]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact independentPopulation_coordinate_expectation
        (fun j => rowDistribution transition (particles (ancestors j)))
        (fun y => observable (particles (ancestors i)) y) i

omit [DecidableEq Sample] [Nonempty Particle] in
/-- Labeled form of conditional propagation: each ancestor may carry arbitrary
auxiliary data, such as its complete path prefix. -/
theorem propagatedPopulation_labeledAverage_expectation {Label : Type*}
    (transition : MarkovKernel Sample) (particles : Particle → Sample)
    (labels : Particle → Label) (ancestors : Particle → Particle)
    (observable : Label → Sample → ℝ) :
    ∑ next, (propagatedPopulation transition particles ancestors).mass next *
        ((∑ i, observable (labels (ancestors i)) (next i)) /
          Fintype.card Particle) =
      (∑ i, ∑ y, transition.prob (particles (ancestors i)) y *
        observable (labels (ancestors i)) y) / Fintype.card Particle := by
  classical
  calc
    _ = (∑ i, ∑ next,
        (propagatedPopulation transition particles ancestors).mass next *
          observable (labels (ancestors i)) (next i)) /
        Fintype.card Particle := by
      simp_rw [div_eq_mul_inv, ← mul_assoc, Finset.mul_sum]
      rw [← Finset.sum_mul]
      congr 1
      rw [Finset.sum_comm]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact independentPopulation_coordinate_expectation
        (fun j => rowDistribution transition (particles (ancestors j)))
        (fun y => observable (labels (ancestors i)) y) i

omit [DecidableEq Sample] in
/-- One-transition many-to-one identity conditional on the current population:
potential weighting, multinomial resampling, propagation, and uniform child
selection recover the exact empirical Feynman--Kac pair expectation. -/
theorem weighted_resamplePropagate_pair_identity
    (potential : Sample → ℝ) (hpotential : ∀ x, 0 < potential x)
    (particles : Particle → Sample) (transition : MarkovKernel Sample)
    (observable : Sample → Sample → ℝ) :
    particleAverage potential particles *
      (∑ ancestors,
        (multinomialResampling
          (normalizedPotentialWeights potential hpotential particles)).mass ancestors *
        (∑ next, (propagatedPopulation transition particles ancestors).mass next *
          ((∑ i, observable (particles (ancestors i)) (next i)) /
            Fintype.card Particle))) =
      particleAverage (fun x => potential x *
        ∑ y, transition.prob x y * observable x y) particles := by
  simp_rw [propagatedPopulation_pairAverage_expectation]
  change particleAverage potential particles *
      (∑ ancestors,
        (multinomialResampling
          (normalizedPotentialWeights potential hpotential particles)).mass ancestors *
        particleAverage
          (fun i => ∑ y, transition.prob (particles i) y * observable (particles i) y)
          ancestors) = _
  rw [multinomialResampling_unbiased
    (normalizedPotentialWeights potential hpotential particles)
    (fun i => i)
    (fun i => ∑ y, transition.prob (particles i) y * observable (particles i) y)]
  unfold particleAverage normalizedPotentialWeights
  have hsum : (∑ j, potential (particles j)) ≠ 0 :=
    ne_of_gt (Finset.sum_pos (fun j _ => hpotential (particles j))
      Finset.univ_nonempty)
  have hcard : (Fintype.card Particle : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  change ((∑ i, potential (particles i)) / Fintype.card Particle) *
      (∑ i, potential (particles i) / (∑ j, potential (particles j)) *
        (∑ y, transition.prob (particles i) y * observable (particles i) y)) =
    (∑ i, potential (particles i) *
      (∑ y, transition.prob (particles i) y * observable (particles i) y)) /
        Fintype.card Particle
  field_simp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  field_simp

omit [DecidableEq Sample] in
/-- Labeled one-transition many-to-one identity. Labels are inherited through
the selected ancestor and may be extended by the propagated child. -/
theorem weighted_resamplePropagate_labeled_identity {Label : Type*}
    (potential : Sample → ℝ) (hpotential : ∀ x, 0 < potential x)
    (particles : Particle → Sample) (labels : Particle → Label)
    (transition : MarkovKernel Sample) (observable : Label → Sample → ℝ) :
    particleAverage potential particles *
      (∑ ancestors,
        (multinomialResampling
          (normalizedPotentialWeights potential hpotential particles)).mass ancestors *
        (∑ next, (propagatedPopulation transition particles ancestors).mass next *
          ((∑ i, observable (labels (ancestors i)) (next i)) /
            Fintype.card Particle))) =
      particleAverage (fun i => potential (particles i) *
        ∑ y, transition.prob (particles i) y * observable (labels i) y)
        (fun i => i) := by
  simp_rw [propagatedPopulation_labeledAverage_expectation]
  change particleAverage potential particles *
      (∑ ancestors,
        (multinomialResampling
          (normalizedPotentialWeights potential hpotential particles)).mass ancestors *
        particleAverage
          (fun i => ∑ y, transition.prob (particles i) y * observable (labels i) y)
          ancestors) = _
  rw [multinomialResampling_unbiased
    (normalizedPotentialWeights potential hpotential particles)
    (fun i => i)
    (fun i => ∑ y, transition.prob (particles i) y * observable (labels i) y)]
  unfold particleAverage normalizedPotentialWeights
  have hsum : (∑ j, potential (particles j)) ≠ 0 :=
    ne_of_gt (Finset.sum_pos (fun j _ => hpotential (particles j))
      Finset.univ_nonempty)
  have hcard : (Fintype.card Particle : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  change ((∑ i, potential (particles i)) / Fintype.card Particle) *
      (∑ i, potential (particles i) / (∑ j, potential (particles j)) *
        (∑ y, transition.prob (particles i) y * observable (labels i) y)) =
    (∑ i, potential (particles i) *
      (∑ y, transition.prob (particles i) y * observable (labels i) y)) /
        Fintype.card Particle
  field_simp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  field_simp

omit [DecidableEq Sample] in
/-- One-transition many-to-one identity after an iid initial population. This
is the full unnormalized Feynman--Kac expectation for an arbitrary observable
of the parent--child path. -/
theorem iid_weighted_resamplePropagate_pair_identity
    (initial : Distribution Sample) (potential : Sample → ℝ)
    (hpotential : ∀ x, 0 < potential x) (transition : MarkovKernel Sample)
    (observable : Sample → Sample → ℝ) :
    ∑ particles, (iidPopulation (Particle := Particle) initial).mass particles *
      (particleAverage potential particles *
        (∑ ancestors,
          (multinomialResampling
            (normalizedPotentialWeights potential hpotential particles)).mass ancestors *
          (∑ next, (propagatedPopulation transition particles ancestors).mass next *
            ((∑ i, observable (particles (ancestors i)) (next i)) /
              Fintype.card Particle)))) =
      ∑ x, initial.mass x *
        (potential x * ∑ y, transition.prob x y * observable x y) := by
  simp_rw [weighted_resamplePropagate_pair_identity]
  exact iidPopulation_particleAverage_expectation initial _

/-- Exact one-particle Feynman--Kac value when each state carries an arbitrary
recursively updated label. -/
noncomputable def labeledFeynmanKacValue {Label : Type*}
    (extend : Label → Sample → Label) :
    List (FeynmanKacStep Sample) → (Label → ℝ) → Label → Sample → ℝ
  | [], observable, label, _ => observable label
  | step :: steps, observable, label, x =>
      step.potential x * ∑ y, step.transition.prob x y *
        labeledFeynmanKacValue extend steps observable (extend label y) y

omit [DecidableEq Sample] in
/-- Nonnegative terminal observables have nonnegative labeled continuation
values. -/
theorem labeledFeynmanKacValue_nonneg {Label : Type*}
    (extend : Label → Sample → Label)
    (steps : List (FeynmanKacStep Sample)) (observable : Label → ℝ)
    (hobservable : ∀ label, 0 ≤ observable label)
    (label : Label) (state : Sample) :
    0 ≤ labeledFeynmanKacValue extend steps observable label state := by
  induction steps generalizing label state with
  | nil => exact hobservable label
  | cons step steps ih =>
      unfold labeledFeynmanKacValue
      apply mul_nonneg (step.potential_pos state).le
      apply Finset.sum_nonneg
      intro y _
      exact mul_nonneg (step.transition.nonneg state y) (ih _ _)

omit [DecidableEq Sample] in
/-- With the constant-one terminal observable, every finite labeled
Feynman--Kac continuation value is strictly positive. -/
theorem labeledFeynmanKacValue_one_pos {Label : Type*}
    (extend : Label → Sample → Label)
    (steps : List (FeynmanKacStep Sample)) (label : Label) (state : Sample) :
    0 < labeledFeynmanKacValue extend steps (fun _ => 1) label state := by
  induction steps generalizing label state with
  | nil => simp [labeledFeynmanKacValue]
  | cons step steps ih =>
      unfold labeledFeynmanKacValue
      apply mul_pos (step.potential_pos state)
      have hexists : ∃ y, 0 < step.transition.prob state y := by
        by_contra h
        push Not at h
        have hzero : ∀ y, step.transition.prob state y = 0 := fun y =>
          le_antisymm (h y) (step.transition.nonneg state y)
        have : ∑ y, step.transition.prob state y = 0 := by simp [hzero]
        linarith [step.transition.sum_prob state]
      obtain ⟨y, hy⟩ := hexists
      apply Finset.sum_pos'
      · intro z _
        exact mul_nonneg (step.transition.nonneg state z) (ih _ _).le
      · exact ⟨y, Finset.mem_univ y, mul_pos hy (ih _ _)⟩

omit [DecidableEq Sample] in
/-- Constant-one labeled continuation values forget the label and coincide
with the ordinary finite Feynman--Kac sequence. -/
theorem labeledFeynmanKacValue_one_eq_feynmanKacSequence {Label : Type*}
    (extend : Label → Sample → Label)
    (steps : List (FeynmanKacStep Sample)) (label : Label) (state : Sample) :
    labeledFeynmanKacValue extend steps (fun _ => 1) label state =
      feynmanKacSequence steps (fun _ => 1) state := by
  induction steps generalizing label state with
  | nil => rfl
  | cons step steps ih =>
      unfold labeledFeynmanKacValue feynmanKacSequence feynmanKacTransform
      congr 1
      apply Finset.sum_congr rfl
      intro y _
      rw [ih]

/-- Unnormalized labeled Feynman--Kac integral from an arbitrary joint
initial law. -/
noncomputable def labeledFeynmanKacIntegral {Label : Type*}
    [Fintype Label] [DecidableEq Label]
    (extend : Label → Sample → Label) (law : Distribution (Label × Sample))
    (steps : List (FeynmanKacStep Sample)) (observable : Label → ℝ) : ℝ :=
  ∑ value, law.mass value *
    labeledFeynmanKacValue extend steps observable value.1 value.2

omit [DecidableEq Sample] in
/-- The constant-one unnormalized labeled integral is a valid strictly
positive normalizer. -/
theorem labeledFeynmanKacIntegral_one_pos {Label : Type*}
    [Fintype Label] [DecidableEq Label]
    (extend : Label → Sample → Label) (law : Distribution (Label × Sample))
    (steps : List (FeynmanKacStep Sample)) :
    0 < labeledFeynmanKacIntegral extend law steps (fun _ => 1) := by
  unfold labeledFeynmanKacIntegral
  have hexists : ∃ value, 0 < law.mass value := by
    by_contra h
    push Not at h
    have hzero : ∀ value, law.mass value = 0 := fun value =>
      le_antisymm (h value) (law.nonneg value)
    have : ∑ value, law.mass value = 0 := by simp [hzero]
    linarith [law.sum_mass]
  obtain ⟨value, hvalue⟩ := hexists
  apply Finset.sum_pos'
  · intro z _
    exact mul_nonneg (law.nonneg z)
      (labeledFeynmanKacValue_one_pos extend steps z.1 z.2).le
  · exact ⟨value, Finset.mem_univ value,
      mul_pos hvalue (labeledFeynmanKacValue_one_pos extend steps value.1 value.2)⟩

/-- One normalized labeled update divides the remaining unnormalized
Feynman--Kac integral by the current potential normalizer. -/
theorem labeledFeynmanKacIntegral_step {Label : Type*}
    [Fintype Label] [DecidableEq Label] [Nonempty Label] [Nonempty Sample]
    (extend : Label → Sample → Label) (law : Distribution (Label × Sample))
    (step : FeynmanKacStep Sample) (steps : List (FeynmanKacStep Sample))
    (observable : Label → ℝ) :
    labeledFeynmanKacIntegral extend
        (labeledFeynmanKacStepDistribution extend step law) steps observable =
      labeledFeynmanKacIntegral extend law (step :: steps) observable /
        ∑ value, law.mass value * step.potential value.2 := by
  unfold labeledFeynmanKacIntegral
  rw [labeledFeynmanKacStepDistribution_expectation]
  rfl

/-- Normalized backward continuation score after one transition. -/
noncomputable def labeledFeynmanKacContinuationScore {Label : Type*}
    (extend : Label → Sample → Label) (step : FeynmanKacStep Sample)
    (steps : List (FeynmanKacStep Sample)) (observable : Label → ℝ)
    (parent : Label × Sample) : ℝ :=
  (∑ y, step.transition.prob parent.2 y *
      labeledFeynmanKacValue extend steps observable (extend parent.1 y) y) /
    ∑ y, step.transition.prob parent.2 y *
      labeledFeynmanKacValue extend steps (fun _ => 1) (extend parent.1 y) y

omit [DecidableEq Sample] in
theorem labeledFeynmanKacContinuationScore_nonneg {Label : Type*}
    (extend : Label → Sample → Label) (step : FeynmanKacStep Sample)
    (steps : List (FeynmanKacStep Sample)) (observable : Label → ℝ)
    (hobservable : ∀ label, 0 ≤ observable label) (parent : Label × Sample) :
    0 ≤ labeledFeynmanKacContinuationScore extend step steps observable parent := by
  unfold labeledFeynmanKacContinuationScore
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro y _
    exact mul_nonneg (step.transition.nonneg _ _)
      (labeledFeynmanKacValue_nonneg extend steps observable hobservable _ _)
  · apply Finset.sum_nonneg
    intro y _
    exact mul_nonneg (step.transition.nonneg _ _)
      (labeledFeynmanKacValue_one_pos extend steps _ _).le

/-- A complete normalized labeled Feynman--Kac ratio is a one-step positive
reweighting by the full backward potential, evaluated at the normalized
continuation score. -/
theorem labeledFeynmanKacIntegral_ratio_eq_backwardReweight
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    (extend : Label → Sample → Label) (law : Distribution (Label × Sample))
    (step : FeynmanKacStep Sample) (steps : List (FeynmanKacStep Sample))
    (observable : Label → ℝ) :
    labeledFeynmanKacIntegral extend law (step :: steps) observable /
        labeledFeynmanKacIntegral extend law (step :: steps) (fun _ => 1) =
      ∑ parent,
        (positivePotentialReweight law
          (feynmanKacSequence (step :: steps) (fun _ => 1) ∘ Prod.snd)
          (fun parent => by
            change 0 < feynmanKacSequence (step :: steps) (fun _ => 1) parent.2
            rw [← labeledFeynmanKacValue_one_eq_feynmanKacSequence
              extend (step :: steps) parent.1 parent.2]
            exact labeledFeynmanKacValue_one_pos extend (step :: steps)
              parent.1 parent.2)).mass parent *
          labeledFeynmanKacContinuationScore extend step steps observable parent := by
  rw [positivePotentialReweight_expectation]
  unfold labeledFeynmanKacIntegral labeledFeynmanKacValue
  simp_rw [labeledFeynmanKacValue_one_eq_feynmanKacSequence]
  unfold Function.comp labeledFeynmanKacContinuationScore
  congr 1
  · apply Finset.sum_congr rfl
    intro parent _
    have hden : 0 < ∑ y, step.transition.prob parent.2 y *
        feynmanKacSequence steps (fun _ => 1) y := by
      have hexists : ∃ y, 0 < step.transition.prob parent.2 y := by
        by_contra h
        push Not at h
        have hzero : ∀ y, step.transition.prob parent.2 y = 0 := fun y =>
          le_antisymm (h y) (step.transition.nonneg parent.2 y)
        have : ∑ y, step.transition.prob parent.2 y = 0 := by simp [hzero]
        linarith [step.transition.sum_prob parent.2]
      obtain ⟨y, hy⟩ := hexists
      apply Finset.sum_pos'
      · intro z _
        exact mul_nonneg (step.transition.nonneg _ _)
          (by
            rw [← labeledFeynmanKacValue_one_eq_feynmanKacSequence
              (Label := Unit) (fun _ _ => ()) steps () z]
            exact (labeledFeynmanKacValue_one_pos
              (fun _ _ => ()) steps () z).le)
      · refine ⟨y, Finset.mem_univ y, mul_pos hy ?_⟩
        rw [← labeledFeynmanKacValue_one_eq_feynmanKacSequence
          (Label := Unit) (fun _ _ => ()) steps () y]
        exact labeledFeynmanKacValue_one_pos (fun _ _ => ()) steps () y
    simp_rw [labeledFeynmanKacValue_one_eq_feynmanKacSequence]
    rw [show feynmanKacSequence (step :: steps) (fun _ => 1) parent.2 =
      step.potential parent.2 *
        ∑ y, step.transition.prob parent.2 y *
          feynmanKacSequence steps (fun _ => 1) y by rfl]
    field_simp

/-- The iterated normalized labeled law is exactly the normalized
unnormalized Feynman--Kac integral. This identity exposes all intermediate
normalizers as a telescoping ratio. -/
theorem labeledFeynmanKacLawFrom_expectation_eq_integral_ratio
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    [Nonempty Label] [Nonempty Sample]
    (extend : Label → Sample → Label) (law : Distribution (Label × Sample))
    (steps : List (FeynmanKacStep Sample)) (observable : Label → ℝ) :
    (∑ value, (labeledFeynmanKacLawFrom extend law steps).mass value *
        observable value.1) =
      labeledFeynmanKacIntegral extend law steps observable /
        labeledFeynmanKacIntegral extend law steps (fun _ => 1) := by
  induction steps generalizing law with
  | nil =>
      simp [labeledFeynmanKacIntegral, labeledFeynmanKacValue, law.sum_mass]
  | cons step steps ih =>
      rw [labeledFeynmanKacLawFrom_cons, ih]
      rw [labeledFeynmanKacIntegral_step extend law step steps observable]
      rw [labeledFeynmanKacIntegral_step extend law step steps (fun _ => 1)]
      have hnormalizer : 0 < ∑ value, law.mass value * step.potential value.2 := by
        apply Finset.sum_pos'
        · intro value _
          exact mul_nonneg (law.nonneg value) (step.potential_pos value.2).le
        · have hexists : ∃ value, 0 < law.mass value := by
            by_contra h
            push Not at h
            have hzero : ∀ value, law.mass value = 0 := fun value =>
              le_antisymm (h value) (law.nonneg value)
            have : ∑ value, law.mass value = 0 := by simp [hzero]
            linarith [law.sum_mass]
          obtain ⟨value, hvalue⟩ := hexists
          exact ⟨value, Finset.mem_univ value,
            mul_pos hvalue (step.potential_pos value.2)⟩
      have hremaining :
          0 < labeledFeynmanKacIntegral extend law (step :: steps) (fun _ => 1) :=
        labeledFeynmanKacIntegral_one_pos extend law (step :: steps)
      field_simp

omit [DecidableEq Particle] in
/-- Exact continuation expectation from an empirical labeled child law is the
ratio of backward unnormalized scores over the parent population. -/
theorem labeledChildLaw_tail_expectation_eq_parent_ratio
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    [Nonempty Label] [Nonempty Sample]
    (extend : Label → Sample → Label) (step : FeynmanKacStep Sample)
    (steps : List (FeynmanKacStep Sample))
    (particles : Particle → Sample) (labels : Particle → Label)
    (observable : Label → ℝ) :
    (∑ value,
      (labeledFeynmanKacLawFrom extend
        (resamplePropagateLabelDistribution extend
          (normalizedPotentialWeights step.potential step.potential_pos particles)
          step.transition particles labels) steps).mass value *
        observable value.1) =
      (∑ i, step.potential (particles i) *
        ∑ y, step.transition.prob (particles i) y *
          labeledFeynmanKacValue extend steps observable (extend (labels i) y) y) /
      ∑ i, step.potential (particles i) *
        ∑ y, step.transition.prob (particles i) y *
          labeledFeynmanKacValue extend steps (fun _ => 1)
            (extend (labels i) y) y := by
  rw [labeledFeynmanKacLawFrom_expectation_eq_integral_ratio]
  unfold labeledFeynmanKacIntegral
  rw [resamplePropagateLabelDistribution_normalized_expectation]
  rw [resamplePropagateLabelDistribution_normalized_expectation]
  have hcurrent : 0 < ∑ i, step.potential (particles i) :=
    Finset.sum_pos (fun i _ => step.potential_pos (particles i))
      Finset.univ_nonempty
  have hfuture : 0 < ∑ i, step.potential (particles i) *
      ∑ y, step.transition.prob (particles i) y *
        labeledFeynmanKacValue extend steps (fun _ => 1)
          (extend (labels i) y) y := by
    apply Finset.sum_pos
    · intro i _
      apply mul_pos (step.potential_pos _)
      have hexists : ∃ y, 0 < step.transition.prob (particles i) y := by
        by_contra h
        push Not at h
        have hzero : ∀ y, step.transition.prob (particles i) y = 0 := fun y =>
          le_antisymm (h y) (step.transition.nonneg _ _)
        have : ∑ y, step.transition.prob (particles i) y = 0 := by simp [hzero]
        linarith [step.transition.sum_prob (particles i)]
      obtain ⟨y, hy⟩ := hexists
      apply Finset.sum_pos'
      · intro z _
        exact mul_nonneg (step.transition.nonneg _ _)
          (labeledFeynmanKacValue_one_pos extend steps _ _).le
      · exact ⟨y, Finset.mem_univ y,
          mul_pos hy (labeledFeynmanKacValue_one_pos extend steps _ _)⟩
    · exact Finset.univ_nonempty
  field_simp

/-- Attach an arbitrary deterministic initial label to a sampled initial
state. -/
def labeledInitialDistribution {Label : Type*}
    [Fintype Label] [DecidableEq Label]
    (initial : Distribution Sample) (initialLabel : Sample → Label) :
    Distribution (Label × Sample) :=
  Distribution.map initial fun state => (initialLabel state, state)

/-- Initial labels do not change the constant-one Feynman--Kac normalizer. -/
theorem labeledInitialDistribution_integral_one
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    (extend : Label → Sample → Label) (initial : Distribution Sample)
    (initialLabel : Sample → Label)
    (steps : List (FeynmanKacStep Sample)) :
    labeledFeynmanKacIntegral extend
        (labeledInitialDistribution initial initialLabel) steps (fun _ => 1) =
      normalizingConstant initial steps := by
  unfold labeledFeynmanKacIntegral labeledInitialDistribution normalizingConstant
  rw [Distribution.map_expectation]
  apply Finset.sum_congr rfl
  intro state _
  rw [labeledFeynmanKacValue_one_eq_feynmanKacSequence]

/-- Concrete product-weighted terminal label average along an explicit SMC
history. -/
noncomputable def labeledHistoryValue {Label : Type*}
    (extend : Label → Sample → Label) :
    (steps : List (FeynmanKacStep Sample)) → (Label → ℝ) →
      (Particle → Label) → (Particle → Sample) →
      Continuation Particle Sample steps → ℝ
  | [], observable, labels, _, _ =>
      (∑ i, observable (labels i)) / Fintype.card Particle
  | step :: steps, observable, labels, particles, history =>
      particleAverage step.potential particles *
        labeledHistoryValue extend steps observable
          (fun i => extend (labels (history.1 i)) (history.2.1 i))
          history.2.1 history.2.2

/-- Labels carried by the terminal population after following every ancestor
map and deterministic label extension. -/
def terminalLabels {Label : Type*} (extend : Label → Sample → Label) :
    (steps : List (FeynmanKacStep Sample)) → (Particle → Label) →
      Continuation Particle Sample steps → Particle → Label
  | [], labels, _ => labels
  | _ :: steps, labels, history =>
      terminalLabels extend steps
        (fun i => extend (labels (history.1 i)) (history.2.1 i)) history.2.2

omit [Fintype Particle] [DecidableEq Sample] [DecidableEq Particle]
    [Nonempty Particle] in
/-- Terminal label propagation is a left fold over the selected ancestral
trajectory after its initial state.  This is the generic bridge from forward
label transport to backward genealogy tracing. -/
theorem terminalLabels_eq_foldl_selectedTrajectory_tail {Label : Type*}
    (extend : Label → Sample → Label)
    (steps : List (FeynmanKacStep Sample)) (labels : Particle → Label)
    (particles : Particle → Sample) (history : Continuation Particle Sample steps)
    (terminal : Particle) :
    terminalLabels extend steps labels history terminal =
      (selectedTrajectory steps particles history terminal).tail.foldl extend
        (labels (initialAncestor steps history terminal)) := by
  induction steps generalizing labels particles with
  | nil => rfl
  | cons step steps ih =>
      unfold terminalLabels initialAncestor selectedTrajectory
      rw [ih]
      let j := initialAncestor steps history.2.2 terminal
      have hhead := selectedTrajectory_head? steps history.2.1 history.2.2 terminal
      have hnonempty :
          selectedTrajectory steps history.2.1 history.2.2 terminal ≠ [] := by
        cases steps <;> simp [selectedTrajectory]
      cases hpath : selectedTrajectory steps history.2.1 history.2.2 terminal with
      | nil => exact (hnonempty hpath).elim
      | cons first rest =>
          simp only [hpath, List.head?_cons, Option.some.injEq] at hhead
          subst first
          rfl

omit [Fintype Particle] [DecidableEq Sample] [DecidableEq Particle]
    [Nonempty Particle] in
/-- Forward propagation of arbitrary path prefixes agrees with backward
genealogy tracing, up to replacing the initial singleton by the supplied
prefix. -/
theorem terminalLabels_append_eq_prefix_append_selectedTail
    (steps : List (FeynmanKacStep Sample)) (labels : Particle → List Sample)
    (particles : Particle → Sample) (history : Continuation Particle Sample steps)
    (terminal : Particle) :
    terminalLabels (fun path y => path ++ [y]) steps labels history terminal =
      labels (initialAncestor steps history terminal) ++
        (selectedTrajectory steps particles history terminal).tail := by
  induction steps generalizing labels particles with
  | nil => simp [terminalLabels, initialAncestor, selectedTrajectory]
  | cons step steps ih =>
      unfold terminalLabels initialAncestor selectedTrajectory
      rw [ih]
      let j := initialAncestor steps history.2.2 terminal
      have hhead := selectedTrajectory_head? steps history.2.1 history.2.2 terminal
      have hnonempty : selectedTrajectory steps history.2.1 history.2.2 terminal ≠ [] := by
        cases steps <;> simp [selectedTrajectory]
      cases hpath : selectedTrajectory steps history.2.1 history.2.2 terminal with
      | nil => exact (hnonempty hpath).elim
      | cons first rest =>
          simp only [hpath, List.head?_cons, Option.some.injEq] at hhead
          subst first
          simp [List.append_assoc]

omit [Fintype Particle] [DecidableEq Sample] [DecidableEq Particle]
    [Nonempty Particle] in
/-- Prefix propagation from singleton initial paths is exactly the previously
defined selected ancestral trajectory. -/
theorem terminalLabels_singleton_eq_selectedTrajectory
    (steps : List (FeynmanKacStep Sample)) (particles : Particle → Sample)
    (history : Continuation Particle Sample steps) (terminal : Particle) :
    terminalLabels (fun path y => path ++ [y]) steps (fun i => [particles i])
        history terminal = selectedTrajectory steps particles history terminal := by
  rw [terminalLabels_append_eq_prefix_append_selectedTail]
  have hhead := selectedTrajectory_head? steps particles history terminal
  have hnonempty : selectedTrajectory steps particles history terminal ≠ [] := by
    cases steps <;> simp [selectedTrajectory]
  cases hpath : selectedTrajectory steps particles history terminal with
  | nil => exact (hnonempty hpath).elim
  | cons first rest =>
      simp only [hpath, List.head?_cons, Option.some.injEq] at hhead
      subst first
      simp

omit [DecidableEq Sample] [DecidableEq Particle] in
/-- The labeled history value factors into the ordinary normalizing weight and
the terminal empirical label observable. -/
theorem labeledHistoryValue_eq_normalizingWeight_mul_terminalAverage
    {Label : Type*} (extend : Label → Sample → Label)
    (steps : List (FeynmanKacStep Sample)) (observable : Label → ℝ)
    (labels : Particle → Label) (particles : Particle → Sample)
    (history : Continuation Particle Sample steps) :
    labeledHistoryValue extend steps observable labels particles history =
      historyValue steps (fun _ => 1) particles history *
        ((∑ i, observable (terminalLabels extend steps labels history i)) /
          Fintype.card Particle) := by
  induction steps generalizing labels particles with
  | nil =>
      unfold labeledHistoryValue historyValue terminalLabels particleAverage
      have hcard : (Fintype.card Particle : ℝ) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      simp [hcard]
  | cons step steps ih =>
      unfold labeledHistoryValue historyValue terminalLabels
      rw [ih]
      ring

omit [DecidableEq Sample] in
/-- Finite-horizon labeled many-to-one identity, conditional on the initial
particle cloud. This is the induction theorem needed for full path prefixes. -/
theorem continuationLaw_labeledHistoryValue_expectation {Label : Type*}
    (extend : Label → Sample → Label) (steps : List (FeynmanKacStep Sample))
    (observable : Label → ℝ) (labels : Particle → Label)
    (particles : Particle → Sample) :
    ∑ history, (continuationLaw (Particle := Particle) steps particles).mass history *
        labeledHistoryValue extend steps observable labels particles history =
      particleAverage
        (fun i => labeledFeynmanKacValue extend steps observable
          (labels i) (particles i)) (fun i => i) := by
  induction steps generalizing labels particles with
  | nil =>
      simp [continuationLaw, labeledHistoryValue, labeledFeynmanKacValue,
        particleAverage, Continuation]
  | cons step steps ih =>
      change
        (∑ history : (Particle → Particle) × (Particle → Sample) ×
            Continuation Particle Sample steps,
          ((multinomialResampling
            (normalizedPotentialWeights step.potential step.potential_pos particles)).mass
              history.1 *
            (propagatedPopulation step.transition particles history.1).mass history.2.1 *
            (continuationLaw steps history.2.1).mass history.2.2) *
          (particleAverage step.potential particles *
            labeledHistoryValue extend steps observable
              (fun i => extend (labels (history.1 i)) (history.2.1 i))
              history.2.1 history.2.2)) = _
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      simp_rw [show ∀ (ancestors : Particle → Particle) (next : Particle → Sample)
          (tail : Continuation Particle Sample steps),
          ((multinomialResampling
              (normalizedPotentialWeights step.potential step.potential_pos particles)).mass
                ancestors *
            (propagatedPopulation step.transition particles ancestors).mass next *
            (continuationLaw steps next).mass tail) *
            (particleAverage step.potential particles *
              labeledHistoryValue extend steps observable
                (fun i => extend (labels (ancestors i)) (next i)) next tail) =
          particleAverage step.potential particles *
            (multinomialResampling
              (normalizedPotentialWeights step.potential step.potential_pos particles)).mass
                ancestors *
            ((propagatedPopulation step.transition particles ancestors).mass next *
              ((continuationLaw steps next).mass tail *
                labeledHistoryValue extend steps observable
                  (fun i => extend (labels (ancestors i)) (next i)) next tail)) by
            intro ancestors next tail; ring]
      simp_rw [← Finset.mul_sum, ih]
      rw [show particleAverage
          (fun i => labeledFeynmanKacValue extend (step :: steps) observable
            (labels i) (particles i)) (fun i => i) =
        particleAverage (fun i => step.potential (particles i) *
          ∑ y, step.transition.prob (particles i) y *
            labeledFeynmanKacValue extend steps observable (extend (labels i) y) y)
          (fun i => i) by rfl]
      simp_rw [show ∀ (a b : ℝ),
          particleAverage step.potential particles * a * b =
            particleAverage step.potential particles * (a * b) by
        intro a b; ring]
      rw [← Finset.mul_sum]
      change particleAverage step.potential particles *
          (∑ ancestors,
            (multinomialResampling
              (normalizedPotentialWeights step.potential step.potential_pos particles)).mass
                ancestors *
            (∑ next,
              (propagatedPopulation step.transition particles ancestors).mass next *
              ((∑ i, labeledFeynmanKacValue extend steps observable
                (extend (labels (ancestors i)) (next i)) (next i)) /
                Fintype.card Particle))) = _
      exact weighted_resamplePropagate_labeled_identity step.potential
        step.potential_pos particles labels step.transition
        (fun label y => labeledFeynmanKacValue extend steps observable
          (extend label y) y)

/-- Generic labeled many-to-one identity after an iid initial population. -/
theorem iid_labeledHistoryValue_expectation
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    (extend : Label → Sample → Label) (initial : Distribution Sample)
    (initialLabel : Sample → Label) (steps : List (FeynmanKacStep Sample))
    (observable : Label → ℝ) :
    ∑ particles, (iidPopulation (Particle := Particle) initial).mass particles *
      (∑ history, (continuationLaw (Particle := Particle) steps particles).mass history *
        labeledHistoryValue extend steps observable
          (fun i => initialLabel (particles i)) particles history) =
      labeledFeynmanKacIntegral extend
        (labeledInitialDistribution initial initialLabel) steps observable := by
  simp_rw [continuationLaw_labeledHistoryValue_expectation]
  have havg (particles : Particle → Sample) :
      particleAverage
          (fun i => labeledFeynmanKacValue extend steps observable
            (initialLabel (particles i)) (particles i)) (fun i => i) =
        particleAverage
          (fun state => labeledFeynmanKacValue extend steps observable
            (initialLabel state) state) particles := rfl
  simp_rw [havg]
  rw [iidPopulation_particleAverage_expectation]
  unfold labeledFeynmanKacIntegral labeledInitialDistribution
  rw [Distribution.map_expectation]

/-- Complete-history form of the generic labeled many-to-one identity. -/
theorem historyLaw_labeledHistoryValue_expectation
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    (extend : Label → Sample → Label) (initial : Distribution Sample)
    (initialLabel : Sample → Label) (steps : List (FeynmanKacStep Sample))
    (observable : Label → ℝ) :
    ∑ history, (historyLaw (Particle := Particle) initial steps).mass history *
      labeledHistoryValue extend steps observable
        (fun i => initialLabel (history.1 i)) history.1 history.2 =
      labeledFeynmanKacIntegral extend
        (labeledInitialDistribution initial initialLabel) steps observable := by
  rw [Fintype.sum_prod_type]
  change ∑ particles, ∑ continuation,
      ((iidPopulation (Particle := Particle) initial).mass particles *
        (continuationLaw steps particles).mass continuation) *
      labeledHistoryValue extend steps observable
        (fun i => initialLabel (particles i)) particles continuation = _
  simp_rw [show ∀ (particles : Particle → Sample)
      (continuation : Continuation Particle Sample steps),
      ((iidPopulation (Particle := Particle) initial).mass particles *
        (continuationLaw steps particles).mass continuation) *
          labeledHistoryValue extend steps observable
            (fun i => initialLabel (particles i)) particles continuation =
        (iidPopulation (Particle := Particle) initial).mass particles *
          ((continuationLaw steps particles).mass continuation *
            labeledHistoryValue extend steps observable
              (fun i => initialLabel (particles i)) particles continuation) by
      intro particles continuation; ring,
    ← Finset.mul_sum]
  exact iid_labeledHistoryValue_expectation extend initial initialLabel steps observable

/-- Exact path-space Feynman--Kac value, represented by successively appending
states to a path prefix. -/
noncomputable def pathFeynmanKacValue (steps : List (FeynmanKacStep Sample))
    (observable : List Sample → ℝ) (initial : Sample) : ℝ :=
  labeledFeynmanKacValue (fun path y => path ++ [y]) steps observable [initial] initial

omit [DecidableEq Sample] in
/-- Arbitrary-horizon many-to-one identity for complete path observables after
an iid initial population. The left side uses the explicit ancestry history
and deterministic propagation of path-prefix labels. -/
theorem iid_labeledHistory_path_expectation
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (observable : List Sample → ℝ) :
    ∑ particles, (iidPopulation (Particle := Particle) initial).mass particles *
      (∑ history, (continuationLaw (Particle := Particle) steps particles).mass history *
        labeledHistoryValue (fun path y => path ++ [y]) steps observable
          (fun i => [particles i]) particles history) =
      ∑ x, initial.mass x * pathFeynmanKacValue steps observable x := by
  simp_rw [continuationLaw_labeledHistoryValue_expectation]
  exact iidPopulation_particleAverage_expectation (Particle := Particle) initial
    (fun x => pathFeynmanKacValue steps observable x)

omit [DecidableEq Sample] in
/-- Complete explicit-history form of the arbitrary path-observable
many-to-one identity. -/
theorem historyLaw_labeled_path_expectation
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (observable : List Sample → ℝ) :
    ∑ history, (historyLaw (Particle := Particle) initial steps).mass history *
      labeledHistoryValue (fun path y => path ++ [y]) steps observable
        (fun i => [history.1 i]) history.1 history.2 =
      ∑ x, initial.mass x * pathFeynmanKacValue steps observable x := by
  rw [Fintype.sum_prod_type]
  change ∑ particles, ∑ continuation,
      ((iidPopulation (Particle := Particle) initial).mass particles *
        (continuationLaw steps particles).mass continuation) *
      labeledHistoryValue (fun path y => path ++ [y]) steps observable
        (fun i => [particles i]) particles continuation = _
  simp_rw [show ∀ (particles : Particle → Sample)
      (continuation : Continuation Particle Sample steps),
      ((iidPopulation (Particle := Particle) initial).mass particles *
        (continuationLaw steps particles).mass continuation) *
          labeledHistoryValue (fun path y => path ++ [y]) steps observable
            (fun i => [particles i]) particles continuation =
        (iidPopulation (Particle := Particle) initial).mass particles *
          ((continuationLaw steps particles).mass continuation *
            labeledHistoryValue (fun path y => path ++ [y]) steps observable
              (fun i => [particles i]) particles continuation) by
      intro particles continuation; ring,
    ← Finset.mul_sum]
  exact iid_labeledHistory_path_expectation initial steps observable

omit [DecidableEq Sample] [DecidableEq Particle] in
/-- A concrete history value factors into its normalizing weight and the
terminal empirical observable. -/
theorem historyValue_eq_normalizingWeight_mul_terminalAverage
    (steps : List (FeynmanKacStep Sample)) (observable : Sample → ℝ)
    (particles : Particle → Sample) (history : Continuation Particle Sample steps) :
    historyValue steps observable particles history =
      historyValue steps (fun _ => 1) particles history *
        particleAverage observable (terminalPopulation steps particles history) := by
  induction steps generalizing particles with
  | nil =>
      unfold historyValue terminalPopulation particleAverage
      have hcard : (Fintype.card Particle : ℝ) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      simp [hcard]
  | cons step steps ih =>
      unfold historyValue terminalPopulation
      rw [ih]
      ring

/-- History-weighted SMC target augmented by a uniformly selected terminal
particle. Its selected state has the normalized Feynman--Kac terminal law. -/
noncomputable def selectedParticleTarget (initial : Distribution Sample)
    (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps) :
    Distribution (History (Particle := Particle) steps × Particle) where
  mass selected :=
    (historyLaw (Particle := Particle) initial steps).mass selected.1 *
      normalizingWeight steps selected.1 /
      normalizingConstant initial steps / Fintype.card Particle
  nonneg selected := div_nonneg
    (div_nonneg (mul_nonneg
      ((historyLaw (Particle := Particle) initial steps).nonneg selected.1)
      (normalizingWeight_nonneg steps selected.1)) (le_of_lt hnormalizer))
    (by positivity)
  sum_mass := by
    rw [Fintype.sum_prod_type]
    have hcard : (Fintype.card Particle : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have hcancel (a : ℝ) : (Fintype.card Particle : ℝ) *
        (a / Fintype.card Particle) = a := by field_simp
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp_rw [hcancel]
    rw [show (∑ history,
        (historyLaw (Particle := Particle) initial steps).mass history *
          normalizingWeight steps history / normalizingConstant initial steps) =
      (∑ history,
        (historyLaw (Particle := Particle) initial steps).mass history *
          normalizingWeight steps history) / normalizingConstant initial steps by
      rw [Finset.sum_div]]
    rw [normalizingWeight_expectation]
    exact div_self (ne_of_gt hnormalizer)

/-- The selected-particle extended target transports any finite deterministic
label process to the same normalized labeled Feynman--Kac law. -/
theorem selectedParticleTarget_terminalLabel_expectation
    {Label : Type*} [Fintype Label] [DecidableEq Label] [Nonempty Label]
    [Nonempty Sample]
    (extend : Label → Sample → Label) (initial : Distribution Sample)
    (initialLabel : Sample → Label) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps)
    (observable : Label → ℝ) :
    (∑ selected,
      (selectedParticleTarget (Particle := Particle)
        initial steps hnormalizer).mass selected *
        observable (terminalLabels extend steps
          (fun i => initialLabel (selected.1.1 i)) selected.1.2 selected.2)) =
      ∑ value,
        (labeledFeynmanKacLawFrom extend
          (labeledInitialDistribution initial initialLabel) steps).mass value *
          observable value.1 := by
  rw [labeledFeynmanKacLawFrom_expectation_eq_integral_ratio]
  rw [labeledInitialDistribution_integral_one]
  unfold selectedParticleTarget
  rw [Fintype.sum_prod_type]
  simp_rw [show ∀ (history : History (Particle := Particle) steps)
      (terminal : Particle),
      ((historyLaw (Particle := Particle) initial steps).mass history *
          normalizingWeight steps history /
          normalizingConstant initial steps / Fintype.card Particle) *
        observable (terminalLabels extend steps
          (fun i => initialLabel (history.1 i)) history.2 terminal) =
      ((historyLaw (Particle := Particle) initial steps).mass history /
          normalizingConstant initial steps) *
        (normalizingWeight steps history *
          observable (terminalLabels extend steps
            (fun i => initialLabel (history.1 i)) history.2 terminal) /
          Fintype.card Particle) by
      intro history terminal; ring]
  have hinner (history : History (Particle := Particle) steps) :
      (∑ terminal,
        normalizingWeight steps history *
          observable (terminalLabels extend steps
            (fun i => initialLabel (history.1 i)) history.2 terminal) /
          Fintype.card Particle) =
        labeledHistoryValue extend steps observable
          (fun i => initialLabel (history.1 i)) history.1 history.2 := by
    rw [labeledHistoryValue_eq_normalizingWeight_mul_terminalAverage]
    unfold normalizingWeight fullHistoryValue
    rw [← Finset.sum_div, ← Finset.mul_sum]
    ring
  simp_rw [← Finset.mul_sum]
  change (∑ history : History (Particle := Particle) steps,
      (historyLaw (Particle := Particle) initial steps).mass history /
          normalizingConstant initial steps *
        (∑ terminal : Particle,
          normalizingWeight steps history *
            observable (terminalLabels extend steps
              (fun i => initialLabel (history.1 i)) history.2 terminal) /
            Fintype.card Particle)) = _
  simp_rw [hinner]
  calc
    (∑ history,
      (historyLaw (Particle := Particle) initial steps).mass history /
          normalizingConstant initial steps *
        labeledHistoryValue extend steps observable
          (fun i => initialLabel (history.1 i)) history.1 history.2) =
      (∑ history,
        (historyLaw (Particle := Particle) initial steps).mass history *
          labeledHistoryValue extend steps observable
            (fun i => initialLabel (history.1 i)) history.1 history.2) /
        normalizingConstant initial steps := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro history _
      ring
    _ = _ := by rw [historyLaw_labeledHistoryValue_expectation]

omit [DecidableEq Sample] in
/-- With full-support initialization and propagation, every selected SMC
history/index pair has positive extended-target mass. -/
theorem selectedParticleTarget_mass_pos
    (initial : Distribution Sample) (hinitial : ∀ x, 0 < initial.mass x)
    (steps : List (FeynmanKacStep Sample))
    (hsupport : FeynmanKacFullSupport steps)
    (hnormalizer : 0 < normalizingConstant initial steps)
    (selected : History (Particle := Particle) steps × Particle) :
    0 < (selectedParticleTarget (Particle := Particle) initial steps
      hnormalizer).mass selected := by
  unfold selectedParticleTarget
  exact div_pos
    (div_pos
      (mul_pos (historyLaw_mass_pos initial hinitial steps hsupport selected.1)
        (normalizingWeight_pos steps selected.1))
      hnormalizer)
    (by positivity)

omit [DecidableEq Sample] in
/-- Exact selected-terminal expectation under the history-weighted SMC target. -/
theorem selectedParticleTarget_expectation (initial : Distribution Sample)
    (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps)
    (observable : Sample → ℝ) :
    ∑ selected, (selectedParticleTarget (Particle := Particle) initial steps
        hnormalizer).mass selected *
      observable (terminalPopulation steps selected.1.1 selected.1.2 selected.2) =
      (∑ x, initial.mass x * feynmanKacSequence steps observable x) /
        normalizingConstant initial steps := by
  rw [Fintype.sum_prod_type]
  have hcard : (Fintype.card Particle : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  change ∑ history, ∑ i,
      ((historyLaw (Particle := Particle) initial steps).mass history *
        normalizingWeight steps history / normalizingConstant initial steps /
        Fintype.card Particle) *
      observable (terminalPopulation steps history.1 history.2 i) = _
  calc
    _ = ∑ history,
        (historyLaw (Particle := Particle) initial steps).mass history /
          normalizingConstant initial steps *
        (normalizingWeight steps history *
          particleAverage observable
            (terminalPopulation steps history.1 history.2)) := by
      apply Finset.sum_congr rfl
      intro history _
      unfold particleAverage
      field_simp
      conv_lhs => rw [Finset.mul_sum]
      conv_rhs => rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      field_simp
    _ = ∑ history,
        (historyLaw (Particle := Particle) initial steps).mass history /
          normalizingConstant initial steps *
        fullHistoryValue steps observable history := by
      apply Finset.sum_congr rfl
      intro history _
      simp only [normalizingWeight, fullHistoryValue]
      congr 1
      exact (historyValue_eq_normalizingWeight_mul_terminalAverage steps observable
        history.1 history.2).symm
    _ = (∑ history,
        (historyLaw (Particle := Particle) initial steps).mass history *
          fullHistoryValue steps observable history) /
          normalizingConstant initial steps := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro history _
      ring
    _ = _ := by rw [historyLaw_value_expectation]

omit [DecidableEq Sample] in
/-- Full arbitrary-horizon path-observable exactness under the selected-particle
extended target, using the path prefixes propagated through stored ancestry. -/
theorem selectedParticleTarget_path_expectation (initial : Distribution Sample)
    (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps)
    (observable : List Sample → ℝ) :
    ∑ selected, (selectedParticleTarget (Particle := Particle) initial steps
        hnormalizer).mass selected *
      observable (terminalLabels (fun path y => path ++ [y]) steps
        (fun i => [selected.1.1 i]) selected.1.2 selected.2) =
      (∑ x, initial.mass x * pathFeynmanKacValue steps observable x) /
        normalizingConstant initial steps := by
  rw [Fintype.sum_prod_type]
  have hcard : (Fintype.card Particle : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  change ∑ history, ∑ i,
      ((historyLaw (Particle := Particle) initial steps).mass history *
        normalizingWeight steps history / normalizingConstant initial steps /
        Fintype.card Particle) *
      observable (terminalLabels (fun path y => path ++ [y]) steps
        (fun j => [history.1 j]) history.2 i) = _
  calc
    _ = ∑ history,
        (historyLaw (Particle := Particle) initial steps).mass history /
          normalizingConstant initial steps *
        (normalizingWeight steps history *
          ((∑ i, observable (terminalLabels (fun path y => path ++ [y]) steps
            (fun j => [history.1 j]) history.2 i)) / Fintype.card Particle)) := by
      apply Finset.sum_congr rfl
      intro history _
      field_simp
      conv_lhs => rw [Finset.mul_sum]
      conv_rhs => rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      field_simp
    _ = ∑ history,
        (historyLaw (Particle := Particle) initial steps).mass history /
          normalizingConstant initial steps *
        labeledHistoryValue (fun path y => path ++ [y]) steps observable
          (fun i => [history.1 i]) history.1 history.2 := by
      apply Finset.sum_congr rfl
      intro history _
      simp only [normalizingWeight]
      congr 1
      exact (labeledHistoryValue_eq_normalizingWeight_mul_terminalAverage
        (fun path y => path ++ [y]) steps observable (fun i => [history.1 i])
          history.1 history.2).symm
    _ = (∑ history,
        (historyLaw (Particle := Particle) initial steps).mass history *
          labeledHistoryValue (fun path y => path ++ [y]) steps observable
            (fun i => [history.1 i]) history.1 history.2) /
          normalizingConstant initial steps := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro history _
      ring
    _ = _ := by rw [historyLaw_labeled_path_expectation]

omit [DecidableEq Sample] in
/-- Full path-observable exactness stated directly for the backward-traced
selected genealogy. -/
theorem selectedParticleTarget_selectedTrajectory_expectation
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps)
    (observable : List Sample → ℝ) :
    ∑ selected, (selectedParticleTarget (Particle := Particle) initial steps
        hnormalizer).mass selected *
      observable (selectedTrajectory steps selected.1.1 selected.1.2 selected.2) =
      (∑ x, initial.mass x * pathFeynmanKacValue steps observable x) /
        normalizingConstant initial steps := by
  simp_rw [← terminalLabels_singleton_eq_selectedTrajectory]
  exact selectedParticleTarget_path_expectation initial steps hnormalizer observable

section ConditionalSMC

/-- Uniform law on the nonempty finite particle-index type. -/
noncomputable def uniformParticleDistribution : Distribution Particle where
  mass _ := 1 / Fintype.card Particle
  nonneg _ := by positivity
  sum_mass := by
    have hcard : (Fintype.card Particle : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp [hcard]

/-- Conditional-SMC continuation with a distinguished current lineage index.
At every step a new retained index is drawn uniformly, its ancestor is forced
to the previous retained index, and its propagated value is forced to the next
reference-path state. Other coordinates follow ordinary multinomial
resampling and propagation. -/
noncomputable def forcedLineageSuffixLaw :
    (steps : List (FeynmanKacStep Sample)) →
    (current : Sample) → (future : List Sample) →
    future.length = steps.length →
    (particles : Particle → Sample) → (retained : Particle) →
    Distribution (Continuation Particle Sample steps × Particle)
  | [], _, [], _, _, retained =>
      pointDistribution (ULift.up (), retained)
  | [], _, _ :: _, hlength, _, _ => by simp at hlength
  | _ :: _, _, [], hlength, _, _ => by simp at hlength
  | step :: steps, _, nextState :: future, hlength, particles, retained =>
      let tailLength : future.length = steps.length := by simpa using hlength
      Distribution.bind (uniformParticleDistribution (Particle := Particle))
        fun nextRetained =>
          Distribution.bind
            (forcedIndependentPopulation
              (fun _ => normalizedPotentialWeights step.potential
                step.potential_pos particles)
              nextRetained retained)
            fun ancestors =>
              Distribution.bind
                (forcedIndependentPopulation
                  (fun i => rowDistribution step.transition
                    (particles (ancestors i)))
                  nextRetained nextState)
                fun nextParticles =>
                  Distribution.map
                    (forcedLineageSuffixLaw steps nextState future tailLength
                      nextParticles nextRetained)
                    fun suffix =>
                      ((ancestors, nextParticles, suffix.1), suffix.2)

/-- Concrete forced-lineage conditional-SMC proposal for a reference path of
the required horizon. The initial retained coordinate and every subsequent
lineage index are chosen uniformly. -/
noncomputable def forcedLineageLaw (initial : Distribution Sample)
    (steps : List (FeynmanKacStep Sample)) (path : List Sample)
    (hlength : path.length = steps.length + 1) :
    Distribution (History (Particle := Particle) steps × Particle) := by
  cases path with
  | nil => simp at hlength
  | cons first future =>
      have hfuture : future.length = steps.length := by simpa using hlength
      exact Distribution.bind
        (uniformParticleDistribution (Particle := Particle)) fun retained =>
          Distribution.bind
            (forcedIndependentPopulation (fun _ => initial) retained first)
            fun particles =>
              Distribution.map
                (forcedLineageSuffixLaw steps first future hfuture particles retained)
                fun suffix => ((particles, suffix.1), suffix.2)

/-- Expected terminal empirical label observable under a forced-lineage
suffix. Labels may encode complete path prefixes; the definition deliberately
ignores the final retained index and aggregates all terminal genealogies. -/
noncomputable def forcedLineageSuffixLabelExpectation {Label : Type*}
    (extend : Label → Sample → Label)
    (steps : List (FeynmanKacStep Sample)) (current : Sample)
    (future : List Sample) (hlength : future.length = steps.length)
    (particles : Particle → Sample) (retained : Particle)
    (labels : Particle → Label) (observable : Label → ℝ) : ℝ :=
  ∑ suffix,
    (forcedLineageSuffixLaw steps current future hlength
      particles retained).mass suffix *
      particleAverage observable
        (terminalLabels extend steps labels suffix.1)

/-- A nonnegative terminal-label observable has nonnegative expectation under
every forced-lineage suffix law. -/
theorem forcedLineageSuffixLabelExpectation_nonneg {Label : Type*}
    (extend : Label → Sample → Label)
    (steps : List (FeynmanKacStep Sample)) (current : Sample)
    (future : List Sample) (hlength : future.length = steps.length)
    (particles : Particle → Sample) (retained : Particle)
    (labels : Particle → Label) (observable : Label → ℝ)
    (hobservable : ∀ label, 0 ≤ observable label) :
    0 ≤ forcedLineageSuffixLabelExpectation extend steps current future hlength
      particles retained labels observable := by
  unfold forcedLineageSuffixLabelExpectation
  apply Finset.sum_nonneg
  intro suffix _
  exact mul_nonneg
    ((forcedLineageSuffixLaw steps current future hlength particles retained).nonneg
      suffix)
    (particleAverage_nonneg (fun label => hobservable label) _)

/-- Recursive suffix expectation averaged over a joint `(label,state)` cloud
with one retained coordinate. This is the induction invariant used by sharp
aggregate conditional-SMC bounds: the ordinary coordinates have one common
law, while the retained label and state are fixed by the conditioned path. -/
noncomputable def forcedCloudLineageSuffixLabelExpectation
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    (extend : Label → Sample → Label)
    (steps : List (FeynmanKacStep Sample)) (future : List Sample)
    (hlength : future.length = steps.length)
    (law : Distribution (Label × Sample)) (extra : ℕ)
    (retained : Fin (extra + 1)) (retainedValue : Label × Sample)
    (observable : Label → ℝ) : ℝ :=
  ∑ population,
    (forcedIndependentPopulation
      (fun _ : Fin (extra + 1) => law) retained retainedValue).mass population *
      forcedLineageSuffixLabelExpectation extend steps retainedValue.2 future
        hlength (fun i => (population i).2) retained
        (fun i => (population i).1) observable

/-- The forced-cloud induction invariant is nonnegative for a nonnegative
terminal observable. -/
theorem forcedCloudLineageSuffixLabelExpectation_nonneg
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    (extend : Label → Sample → Label)
    (steps : List (FeynmanKacStep Sample)) (future : List Sample)
    (hlength : future.length = steps.length)
    (law : Distribution (Label × Sample)) (extra : ℕ)
    (retained : Fin (extra + 1)) (retainedValue : Label × Sample)
    (observable : Label → ℝ) (hobservable : ∀ label, 0 ≤ observable label) :
    0 ≤ forcedCloudLineageSuffixLabelExpectation extend steps future hlength
      law extra retained retainedValue observable := by
  unfold forcedCloudLineageSuffixLabelExpectation
  apply Finset.sum_nonneg
  intro population _
  exact mul_nonneg
    ((forcedIndependentPopulation
      (fun _ : Fin (extra + 1) => law) retained retainedValue).nonneg population)
    (forcedLineageSuffixLabelExpectation_nonneg extend steps retainedValue.2
      future hlength (fun i => (population i).2) retained
      (fun i => (population i).1) observable hobservable)

@[simp] theorem forcedLineageSuffixLabelExpectation_nil {Label : Type*}
    (extend : Label → Sample → Label) (current : Sample)
    (particles : Particle → Sample) (retained : Particle)
    (labels : Particle → Label) (observable : Label → ℝ)
    (hlength : [].length = ([] : List (FeynmanKacStep Sample)).length) :
    forcedLineageSuffixLabelExpectation extend [] current [] hlength
        particles retained labels observable =
      particleAverage observable labels := by
  simp [forcedLineageSuffixLabelExpectation, forcedLineageSuffixLaw,
    terminalLabels, pointDistribution]

/-- Terminal case of the forced-cloud suffix induction. Discarding the one
retained coordinate loses exactly the factor `(N-1)/N`; all ordinary
coordinates contribute the exact one-particle label expectation. -/
theorem forcedCloudLineageSuffixLabelExpectation_nil_lower_bound
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    (extend : Label → Sample → Label) (law : Distribution (Label × Sample))
    (extra : ℕ) (retained : Fin (extra + 1))
    (retainedValue : Label × Sample) (observable : Label → ℝ)
    (hobservable : ∀ label, 0 ≤ observable label) :
    (extra : ℝ) / (extra + 1) *
        (∑ value, law.mass value * observable value.1) ≤
      forcedCloudLineageSuffixLabelExpectation extend [] [] (by simp)
        law extra retained retainedValue observable := by
  have hbase :=
    forcedIndependentPopulation_particleAverage_expectation_ge_card
      (Particle := Fin (extra + 1))
      (law := fun _ : Fin (extra + 1) => law) retained retainedValue
      (fun value : Label × Sample => observable value.1)
      (∑ value, law.mass value * observable value.1)
      (hobservable retainedValue.1)
      (by
        intro i _hi
        exact le_rfl)
  unfold forcedCloudLineageSuffixLabelExpectation
  simp only [forcedLineageSuffixLabelExpectation_nil]
  simpa [particleAverage, Fintype.card_fin, Nat.add_comm, div_eq_mul_inv,
    mul_assoc, mul_left_comm, mul_comm] using hbase

/-- Recursive expansion of the aggregate label expectation through one
forced resample--propagate stage. This is the induction-facing equation for
quantitative conditional-SMC bounds. -/
theorem forcedLineageSuffixLabelExpectation_cons {Label : Type*}
    (extend : Label → Sample → Label)
    (step : FeynmanKacStep Sample) (steps : List (FeynmanKacStep Sample))
    (current nextState : Sample) (future : List Sample)
    (hlength : (nextState :: future).length = (step :: steps).length)
    (particles : Particle → Sample) (retained : Particle)
    (labels : Particle → Label) (observable : Label → ℝ) :
    forcedLineageSuffixLabelExpectation extend (step :: steps) current
        (nextState :: future) hlength particles retained labels observable =
      ∑ nextRetained,
        (uniformParticleDistribution (Particle := Particle)).mass nextRetained *
        ∑ ancestors,
          (forcedIndependentPopulation
            (fun _ => normalizedPotentialWeights step.potential
              step.potential_pos particles)
            nextRetained retained).mass ancestors *
          ∑ nextParticles,
            (forcedIndependentPopulation
              (fun i => rowDistribution step.transition
                (particles (ancestors i)))
              nextRetained nextState).mass nextParticles *
              forcedLineageSuffixLabelExpectation extend steps nextState future
                (by simpa using hlength) nextParticles nextRetained
                (fun i => extend (labels (ancestors i)) (nextParticles i))
                observable := by
  change (∑ suffix,
      (forcedLineageSuffixLaw (step :: steps) current (nextState :: future)
        hlength particles retained).mass suffix *
        particleAverage observable
          (terminalLabels extend (step :: steps) labels suffix.1)) = _
  rw [forcedLineageSuffixLaw]
  rw [Distribution.bind_expectation]
  apply Finset.sum_congr rfl
  intro nextRetained _
  rw [Distribution.bind_expectation]
  congr 1
  apply Finset.sum_congr rfl
  intro ancestors _
  rw [Distribution.bind_expectation]
  congr 1
  apply Finset.sum_congr rfl
  intro nextParticles _
  rw [Distribution.map_expectation]
  simp only [terminalLabels]
  rfl

/-- Joint-child form of the forced suffix recursion. Each stage is exposed as
a one-coordinate-forced iid population of `(updated label, next state)` pairs,
which is the form consumed by the sharp self-normalization theorem. -/
theorem forcedLineageSuffixLabelExpectation_cons_joint
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    (extend : Label → Sample → Label)
    (step : FeynmanKacStep Sample) (steps : List (FeynmanKacStep Sample))
    (current nextState : Sample) (future : List Sample)
    (hlength : (nextState :: future).length = (step :: steps).length)
    (particles : Particle → Sample) (retained : Particle)
    (labels : Particle → Label) (observable : Label → ℝ) :
    forcedLineageSuffixLabelExpectation extend (step :: steps) current
        (nextState :: future) hlength particles retained labels observable =
      ∑ nextRetained,
        (uniformParticleDistribution (Particle := Particle)).mass nextRetained *
        ∑ children,
          (forcedResamplePropagateLabelPopulation extend
            (normalizedPotentialWeights step.potential step.potential_pos particles)
            step.transition particles labels retained nextRetained nextState).mass
              children *
            forcedLineageSuffixLabelExpectation extend steps nextState future
              (by simpa using hlength)
              (fun i => (children i).2) nextRetained
              (fun i => (children i).1) observable := by
  rw [forcedLineageSuffixLabelExpectation_cons]
  apply Finset.sum_congr rfl
  intro nextRetained _
  congr 1
  exact forcedResamplePropagateLabelPopulation_expectation
    extend
    (normalizedPotentialWeights step.potential step.potential_pos particles)
    step.transition particles labels retained nextRetained nextState
    (fun children =>
      forcedLineageSuffixLabelExpectation extend steps nextState future
        (by simpa using hlength)
        (fun i => (children i).2) nextRetained
        (fun i => (children i).1) observable)

/-- Recursive expansion of the forced-cloud induction invariant. Conditional
on the present cloud and next retained index, the child cloud is again a
one-coordinate-forced iid cloud whose ordinary law is the labeled
resample--propagate distribution. -/
theorem forcedCloudLineageSuffixLabelExpectation_cons
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    (extend : Label → Sample → Label)
    (step : FeynmanKacStep Sample) (steps : List (FeynmanKacStep Sample))
    (nextState : Sample) (future : List Sample)
    (hlength : (nextState :: future).length = (step :: steps).length)
    (law : Distribution (Label × Sample)) (extra : ℕ)
    (retained : Fin (extra + 1)) (retainedValue : Label × Sample)
    (observable : Label → ℝ) :
    forcedCloudLineageSuffixLabelExpectation extend (step :: steps)
        (nextState :: future) hlength law extra retained retainedValue observable =
      ∑ population,
        (forcedIndependentPopulation
          (fun _ : Fin (extra + 1) => law) retained retainedValue).mass population *
        ∑ nextRetained,
          (uniformParticleDistribution (Particle := Fin (extra + 1))).mass
              nextRetained *
            forcedCloudLineageSuffixLabelExpectation extend steps future
              (by simpa using hlength)
              (resamplePropagateLabelDistribution extend
                (normalizedPotentialWeights step.potential step.potential_pos
                  (fun i => (population i).2))
                step.transition (fun i => (population i).2)
                (fun i => (population i).1))
              extra nextRetained
              (extend (population retained).1 nextState, nextState) observable := by
  unfold forcedCloudLineageSuffixLabelExpectation
  apply Finset.sum_congr rfl
  intro population _
  congr 1
  rw [forcedLineageSuffixLabelExpectation_cons_joint]
  apply Finset.sum_congr rfl
  intro nextRetained _
  congr 1
  rw [forcedResamplePropagateLabelPopulation_eq_forcedIndependent]

/-- For a single remaining propagation, terminal forced-cloud averaging
dominates the ordinary-child self-normalized score with the exact terminal
index factor. The retained parent contribution is discarded using
nonnegativity. -/
theorem forcedCloudLineageSuffixLabelExpectation_singleton_inner_lower_bound
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    (extend : Label → Sample → Label) (step : FeynmanKacStep Sample)
    (nextState : Sample) (extra : ℕ)
    (population : Fin (extra + 1) → (Label × Sample))
    (retained : Fin (extra + 1))
    (observable : Label → ℝ) (hobservable : ∀ label, 0 ≤ observable label) :
    (extra : ℝ) / (extra + 1) *
        ((∑ i : Fin (extra + 1), if i = retained then 0 else
            step.potential (population i).2 *
              ∑ y, step.transition.prob (population i).2 y *
                observable (extend (population i).1 y)) /
          ∑ i, step.potential (population i).2) ≤
      ∑ nextRetained,
        (uniformParticleDistribution (Particle := Fin (extra + 1))).mass
            nextRetained *
          forcedCloudLineageSuffixLabelExpectation extend [] [] (by simp)
            (resamplePropagateLabelDistribution extend
              (normalizedPotentialWeights step.potential step.potential_pos
                (fun i => (population i).2))
              step.transition (fun i => (population i).2)
              (fun i => (population i).1))
            extra nextRetained
            (extend (population retained).1 nextState, nextState) observable := by
  let childLaw := resamplePropagateLabelDistribution extend
    (normalizedPotentialWeights step.potential step.potential_pos
      (fun i => (population i).2))
    step.transition (fun i => (population i).2) (fun i => (population i).1)
  let childExpectation := ∑ child, childLaw.mass child * observable child.1
  have hexcluded :
      ((∑ i : Fin (extra + 1), if i = retained then 0 else
          step.potential (population i).2 *
            ∑ y, step.transition.prob (population i).2 y *
              observable (extend (population i).1 y)) /
        ∑ i, step.potential (population i).2) ≤ childExpectation := by
    exact unforcedNormalizedLabelScore_le_resamplePropagateExpectation
      extend step.potential step.potential_pos step.transition
      (fun i => (population i).2) (fun i => (population i).1) retained
      (fun label _state => observable label) (fun label _ => hobservable label)
  have hfactor : 0 ≤ (extra : ℝ) / (extra + 1) := by positivity
  calc
    (extra : ℝ) / (extra + 1) *
        ((∑ i : Fin (extra + 1), if i = retained then 0 else
            step.potential (population i).2 *
              ∑ y, step.transition.prob (population i).2 y *
                observable (extend (population i).1 y)) /
          ∑ i, step.potential (population i).2) ≤
        (extra : ℝ) / (extra + 1) * childExpectation :=
      mul_le_mul_of_nonneg_left hexcluded hfactor
    _ = ∑ nextRetained : Fin (extra + 1),
        (uniformParticleDistribution (Particle := Fin (extra + 1))).mass
            nextRetained *
          ((extra : ℝ) / (extra + 1) * childExpectation) := by
      rw [← Finset.sum_mul,
        (uniformParticleDistribution (Particle := Fin (extra + 1))).sum_mass,
        one_mul]
    _ ≤ ∑ nextRetained,
        (uniformParticleDistribution (Particle := Fin (extra + 1))).mass
            nextRetained *
          forcedCloudLineageSuffixLabelExpectation extend [] [] (by simp)
            childLaw extra nextRetained
            (extend (population retained).1 nextState, nextState) observable := by
      apply Finset.sum_le_sum
      intro nextRetained _
      apply mul_le_mul_of_nonneg_left
      · exact forcedCloudLineageSuffixLabelExpectation_nil_lower_bound
          extend childLaw extra nextRetained
          (extend (population retained).1 nextState, nextState)
          observable hobservable
      · exact (uniformParticleDistribution
          (Particle := Fin (extra + 1))).nonneg nextRetained

/-- Complete one-propagation instance of the sharp forced-cloud induction.
It composes the terminal-index loss with the `2B-1` self-normalization loss
and compares directly with the exact normalized labeled Feynman--Kac update. -/
theorem forcedCloudLineageSuffixLabelExpectation_singleton_lower_bound
    {Label : Type*} [Fintype Label] [DecidableEq Label] [Nonempty Label]
    [Nonempty Sample]
    (extend : Label → Sample → Label) (step : FeynmanKacStep Sample)
    (bound : ℝ) (certificate : PotentialOscillationBound step.potential bound)
    (nextState : Sample) (law : Distribution (Label × Sample))
    (extra : ℕ) (hextra : 0 < extra) (retained : Fin (extra + 1))
    (retainedValue : Label × Sample) (observable : Label → ℝ)
    (hobservable : ∀ label, 0 ≤ observable label) :
    ((extra : ℝ) / (extra + 1)) *
        ((extra : ℝ) / (((extra - 1 : ℕ) : ℝ) + 2 * bound)) *
        (∑ child,
          (labeledFeynmanKacStepDistribution extend step law).mass child *
            observable child.1) ≤
      forcedCloudLineageSuffixLabelExpectation extend [step] [nextState]
        (by simp) law extra retained retainedValue observable := by
  let score : Label × Sample → ℝ := fun parent =>
    ∑ y, step.transition.prob parent.2 y *
      observable (extend parent.1 y)
  have hscore : ∀ parent, 0 ≤ score parent := by
    intro parent
    apply Finset.sum_nonneg
    intro y _
    exact mul_nonneg (step.transition.nonneg _ _) (hobservable _)
  let exactExpectation := ∑ child,
    (labeledFeynmanKacStepDistribution extend step law).mass child *
      observable child.1
  have hexact : exactExpectation =
      ∑ parent,
        (positivePotentialReweight law (fun z : Label × Sample => step.potential z.2)
          (fun z => step.potential_pos z.2)).mass parent * score parent := by
    unfold exactExpectation labeledFeynmanKacStepDistribution
    simpa [score] using
      (resamplePropagateLabelDistribution_expectation
        (Particle := Label × Sample) extend
        (positivePotentialReweight law
          (fun z : Label × Sample => step.potential z.2)
          (fun z => step.potential_pos z.2))
        step.transition (fun z : Label × Sample => z.2)
        (fun z : Label × Sample => z.1)
        (fun label _state => observable label))
  have hsharp := forcedJointPopulation_normalizedTargetScore_lower_bound
    step.potential step.potential_pos bound certificate law extra hextra
    retained retainedValue score hscore
  have hterminal (population : Fin (extra + 1) → (Label × Sample)) :
      (extra : ℝ) / (extra + 1) *
          ((∑ i : Fin (extra + 1), if i = retained then 0 else
              step.potential (population i).2 * score (population i)) /
            ∑ i, step.potential (population i).2) ≤
        ∑ nextRetained,
          (uniformParticleDistribution (Particle := Fin (extra + 1))).mass
              nextRetained *
            forcedCloudLineageSuffixLabelExpectation extend [] [] (by simp)
              (resamplePropagateLabelDistribution extend
                (normalizedPotentialWeights step.potential step.potential_pos
                  (fun i => (population i).2))
                step.transition (fun i => (population i).2)
                (fun i => (population i).1))
              extra nextRetained
              (extend (population retained).1 nextState, nextState) observable := by
    exact forcedCloudLineageSuffixLabelExpectation_singleton_inner_lower_bound
      extend step nextState extra population retained observable hobservable
  rw [forcedCloudLineageSuffixLabelExpectation_cons]
  change ((extra : ℝ) / (extra + 1)) *
      ((extra : ℝ) / (((extra - 1 : ℕ) : ℝ) + 2 * bound)) *
      exactExpectation ≤ _
  rw [hexact]
  calc
    ((extra : ℝ) / (extra + 1)) *
        ((extra : ℝ) / (((extra - 1 : ℕ) : ℝ) + 2 * bound)) *
        (∑ parent,
          (positivePotentialReweight law
            (fun z : Label × Sample => step.potential z.2)
            (fun z => step.potential_pos z.2)).mass parent * score parent) ≤
      ((extra : ℝ) / (extra + 1)) *
        (∑ population,
          (forcedIndependentPopulation
            (fun _ : Fin (extra + 1) => law) retained retainedValue).mass population *
            ((∑ i : Fin (extra + 1), if i = retained then 0 else
                step.potential (population i).2 * score (population i)) /
              ∑ i, step.potential (population i).2)) := by
        calc
          _ = ((extra : ℝ) / (extra + 1)) *
              (((extra : ℝ) / (((extra - 1 : ℕ) : ℝ) + 2 * bound)) *
                ∑ parent,
                  (positivePotentialReweight law
                    (fun z : Label × Sample => step.potential z.2)
                    (fun z => step.potential_pos z.2)).mass parent *
                      score parent) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hsharp (by positivity)
    _ = ∑ population,
        (forcedIndependentPopulation
          (fun _ : Fin (extra + 1) => law) retained retainedValue).mass population *
          (((extra : ℝ) / (extra + 1)) *
            ((∑ i : Fin (extra + 1), if i = retained then 0 else
                step.potential (population i).2 * score (population i)) /
              ∑ i, step.potential (population i).2)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro population _
        ring
    _ ≤ ∑ population,
        (forcedIndependentPopulation
          (fun _ : Fin (extra + 1) => law) retained retainedValue).mass population *
          ∑ nextRetained,
            (uniformParticleDistribution (Particle := Fin (extra + 1))).mass
                nextRetained *
              forcedCloudLineageSuffixLabelExpectation extend [] [] (by simp)
                (resamplePropagateLabelDistribution extend
                  (normalizedPotentialWeights step.potential step.potential_pos
                    (fun i => (population i).2))
                  step.transition (fun i => (population i).2)
                  (fun i => (population i).1))
                extra nextRetained
                (extend (population retained).1 nextState, nextState)
                observable := by
        apply Finset.sum_le_sum
        intro population _
        apply mul_le_mul_of_nonneg_left
        · exact hterminal population
        · exact (forcedIndependentPopulation
            (fun _ : Fin (extra + 1) => law) retained retainedValue).nonneg population

/-- Unnormalized one-particle Feynman--Kac density of a fixed path suffix,
excluding the initial-state mass. -/
noncomputable def pathSuffixDensity :
    (steps : List (FeynmanKacStep Sample)) → Sample → List Sample → ℝ
  | [], _, [] => 1
  | [], _, _ :: _ => 0
  | _ :: _, _, [] => 0
  | step :: steps, current, next :: future =>
      step.potential current * step.transition.prob current next *
        pathSuffixDensity steps next future

/-- Support condition needed by conditional SMC: every transition traversed
by the retained reference path has positive probability. Potentials are
already strictly positive in `FeynmanKacStep`. -/
def PathSuffixSupported :
    (steps : List (FeynmanKacStep Sample)) → Sample → List Sample → Prop
  | [], _, [] => True
  | [], _, _ :: _ => False
  | _ :: _, _, [] => False
  | step :: steps, current, next :: future =>
      0 < step.transition.prob current next ∧
        PathSuffixSupported steps next future

omit [DecidableEq Sample] in
/-- Full-support propagation discharges the retained-path support condition
for every suffix of the required length. -/
theorem PathSuffixSupported.of_fullSupport
    (steps : List (FeynmanKacStep Sample))
    (hsupport : FeynmanKacFullSupport steps)
    (current : Sample) (future : List Sample)
    (hlength : future.length = steps.length) :
    PathSuffixSupported steps current future := by
  induction steps generalizing current future with
  | nil =>
      have : future = [] := by simpa using hlength
      subst future
      trivial
  | cons step steps ih =>
      cases future with
      | nil => simp at hlength
      | cons next future =>
          simp only [FeynmanKacFullSupport] at hsupport
          simp only [PathSuffixSupported]
          exact ⟨hsupport.1 current next,
            ih hsupport.2 next future (by simpa using hlength)⟩

omit [DecidableEq Sample] in
theorem pathSuffixDensity_pos
    (steps : List (FeynmanKacStep Sample)) (current : Sample)
    (future : List Sample) (hsupport : PathSuffixSupported steps current future) :
    0 < pathSuffixDensity steps current future := by
  induction steps generalizing current future with
  | nil =>
      cases future <;> simp_all [PathSuffixSupported, pathSuffixDensity]
  | cons step steps ih =>
      cases future with
      | nil => simp [PathSuffixSupported] at hsupport
      | cons next future =>
          simp only [PathSuffixSupported] at hsupport
          simp only [pathSuffixDensity]
          exact mul_pos (mul_pos (step.potential_pos current) hsupport.1)
            (ih next future hsupport.2)

/-- Pointwise density formula for the concrete forced-lineage suffix. This is
the algebraic core of its equivalence with exact conditional SMC. -/
theorem forcedLineageSuffixLaw_mass
    (steps : List (FeynmanKacStep Sample)) (current : Sample)
    (future : List Sample) (hlength : future.length = steps.length)
    (hsupport : PathSuffixSupported steps current future)
    (particles : Particle → Sample) (retained : Particle)
    (hretained : particles retained = current)
    (suffix : Continuation Particle Sample steps × Particle) :
    (forcedLineageSuffixLaw steps current future hlength particles retained).mass suffix =
      if initialAncestor steps suffix.1 suffix.2 = retained ∧
          selectedTrajectory steps particles suffix.1 suffix.2 = current :: future then
        (continuationLaw steps particles).mass suffix.1 *
          historyValue steps (fun _ => 1) particles suffix.1 /
            pathSuffixDensity steps current future
      else 0 := by
  induction steps generalizing current future particles retained with
  | nil =>
      cases future with
      | nil =>
          rcases suffix with ⟨continuation, terminal⟩
          rcases continuation with ⟨u⟩
          cases u
          by_cases hterminal : terminal = retained
          · subst terminal
            have hcard : (Fintype.card Particle : ℝ) ≠ 0 := by
              exact_mod_cast Fintype.card_ne_zero
            simp [forcedLineageSuffixLaw, pointDistribution, initialAncestor,
              selectedTrajectory, continuationLaw, historyValue,
              pathSuffixDensity, hretained, particleAverage, hcard]
          · simp [forcedLineageSuffixLaw, pointDistribution, initialAncestor,
              selectedTrajectory, hterminal]
      | cons next future => simp at hlength
  | cons step steps ih =>
      cases future with
      | nil => simp at hlength
      | cons next future =>
          rcases suffix with ⟨⟨ancestors, nextParticles, tail⟩, terminal⟩
          simp only [PathSuffixSupported] at hsupport
          have htailLength : future.length = steps.length := by simpa using hlength
          unfold forcedLineageSuffixLaw
          simp only [Distribution.bind_mass, Distribution.map]
          have heq (as : Particle → Particle) (ps : Particle → Sample)
              (rest : Continuation Particle Sample steps × Particle) :
              (((show Continuation Particle Sample (step :: steps) from
                    (ancestors, nextParticles, tail)), terminal) =
                  ((show Continuation Particle Sample (step :: steps) from
                    (as, ps, rest.1)), rest.2)) ↔
                as = ancestors ∧ ps = nextParticles ∧ rest = (tail, terminal) := by
            constructor
            · intro h
              cases h
              exact ⟨rfl, rfl, Prod.ext rfl rfl⟩
            · rintro ⟨rfl, rfl, rfl⟩
              rfl
          simp only [heq]
          simp
          have hinner (nextRetained : Particle) :
              (∑ as,
                (forcedIndependentPopulation
                  (fun _ => normalizedPotentialWeights step.potential
                    step.potential_pos particles)
                  nextRetained retained).mass as *
                ∑ ps,
                  (forcedIndependentPopulation
                    (fun i => rowDistribution step.transition (particles (as i)))
                    nextRetained next).mass ps *
                  ∑ rest,
                    if as = ancestors ∧ ps = nextParticles ∧
                        rest = (tail, terminal) then
                      (forcedLineageSuffixLaw steps next future htailLength
                        ps nextRetained).mass rest
                    else 0) =
                (forcedIndependentPopulation
                  (fun _ => normalizedPotentialWeights step.potential
                    step.potential_pos particles)
                  nextRetained retained).mass ancestors *
                (forcedIndependentPopulation
                  (fun i => rowDistribution step.transition (particles (ancestors i)))
                  nextRetained next).mass nextParticles *
                (forcedLineageSuffixLaw steps next future htailLength
                  nextParticles nextRetained).mass (tail, terminal) := by
            rw [Finset.sum_eq_single ancestors]
            · rw [Finset.sum_eq_single nextParticles]
              · rw [Finset.sum_eq_single (tail, terminal)]
                · simp only [true_and, ↓reduceIte]
                  ring
                · intro rest _ hrest
                  simp [hrest]
                · simp
              · intro ps _ hps
                simp [hps]
              · simp
            · intro as _ has
              simp [has]
            · simp
          simp_rw [hinner]
          let lineage := initialAncestor steps tail terminal
          by_cases htrajectory :
              selectedTrajectory steps nextParticles tail terminal = next :: future
          · have hnext : nextParticles lineage = next := by
              have hhead := congrArg List.head? htrajectory
              rw [selectedTrajectory_head?] at hhead
              simpa [lineage] using hhead
            by_cases hancestor : ancestors lineage = retained
            · have hweight : 0 <
                  (normalizedPotentialWeights step.potential step.potential_pos
                    particles).mass retained := by
                unfold normalizedPotentialWeights
                exact div_pos (by simpa [hretained] using step.potential_pos current)
                  (Finset.sum_pos (fun i _ => step.potential_pos (particles i))
                    Finset.univ_nonempty)
              have htransition : 0 <
                  (rowDistribution step.transition
                    (particles (ancestors lineage))).mass next := by
                simpa [rowDistribution, hancestor, hretained] using hsupport.1
              have hfullAncestor :
                  initialAncestor (step :: steps) (ancestors, nextParticles, tail)
                    terminal = retained := by
                simpa only [initialAncestor, lineage] using hancestor
              have hfullTrajectory :
                  selectedTrajectory (step :: steps) particles
                    (ancestors, nextParticles, tail) terminal =
                      current :: next :: future := by
                simp only [selectedTrajectory, lineage, hancestor, hretained,
                  htrajectory]
              rw [Finset.sum_eq_single lineage]
              · rw [forcedIndependentPopulation_mass_eq_div
                  (law := fun _ => normalizedPotentialWeights step.potential
                    step.potential_pos particles)
                  (retained := lineage) (value := retained) hweight ancestors]
                rw [forcedIndependentPopulation_mass_eq_div
                  (law := fun i => rowDistribution step.transition
                    (particles (ancestors i)))
                  (retained := lineage) (value := next) htransition nextParticles]
                rw [ih next future htailLength hsupport.2 nextParticles lineage
                  hnext (tail, terminal)]
                simp only [hancestor, hnext, htrajectory, lineage, true_and,
                  ↓reduceIte]
                simp only [hfullAncestor, hfullTrajectory, and_self, if_true]
                have hresample :
                    (independentPopulation
                      (fun _ => normalizedPotentialWeights step.potential
                        step.potential_pos particles)).mass ancestors =
                      (multinomialResampling
                        (normalizedPotentialWeights step.potential
                          step.potential_pos particles)).mass ancestors := by
                  rfl
                have hpropagate :
                    (independentPopulation
                      (fun i => rowDistribution step.transition
                        (particles (ancestors i)))).mass nextParticles =
                      (propagatedPopulation step.transition particles ancestors).mass
                        nextParticles := by
                  rfl
                rw [hresample, hpropagate]
                simp only [uniformParticleDistribution, continuationLaw, historyValue,
                  pathSuffixDensity, rowDistribution, hretained]
                change (1 / (Fintype.card Particle : ℝ)) *
                    ((multinomialResampling
                        (normalizedPotentialWeights step.potential
                          step.potential_pos particles)).mass ancestors /
                      (normalizedPotentialWeights step.potential
                        step.potential_pos particles).mass retained *
                    ((propagatedPopulation step.transition particles ancestors).mass
                          nextParticles /
                        step.transition.prob current next) *
                    ((continuationLaw steps nextParticles).mass tail *
                        historyValue steps (fun _ => 1) nextParticles tail /
                          pathSuffixDensity steps next future)) =
                  ((multinomialResampling
                      (normalizedPotentialWeights step.potential
                        step.potential_pos particles)).mass ancestors *
                    (propagatedPopulation step.transition particles ancestors).mass
                      nextParticles *
                    (continuationLaw steps nextParticles).mass tail) *
                  (((∑ i, step.potential (particles i)) /
                      (Fintype.card Particle : ℝ)) *
                    historyValue steps (fun _ => 1) nextParticles tail) /
                  (step.potential current * step.transition.prob current next *
                    pathSuffixDensity steps next future)
                have hcard : (Fintype.card Particle : ℝ) ≠ 0 := by
                  exact_mod_cast Fintype.card_ne_zero
                have hsum : (∑ i, step.potential (particles i)) ≠ 0 :=
                  ne_of_gt (Finset.sum_pos
                    (fun i _ => step.potential_pos (particles i))
                    Finset.univ_nonempty)
                have hpot : step.potential current ≠ 0 :=
                  ne_of_gt (step.potential_pos current)
                have htrans : step.transition.prob current next ≠ 0 :=
                  ne_of_gt hsupport.1
                simp only [normalizedPotentialWeights]
                rw [hretained]
                field_simp
              · intro other _ hother
                by_cases hotherNext : nextParticles other = next
                · rw [ih next future htailLength hsupport.2 nextParticles other
                    hotherNext (tail, terminal)]
                  have hlineage : initialAncestor steps tail terminal ≠ other := by
                    simpa [lineage, eq_comm] using hother
                  simp [hlineage]
                · rw [forcedIndependentPopulation_incompatible_zero _ other next
                    nextParticles hotherNext]
                  ring
              · simp
            · rw [show (∑ x,
                    uniformParticleDistribution.mass x *
                      ((forcedIndependentPopulation
                        (fun _ => normalizedPotentialWeights step.potential
                          step.potential_pos particles) x retained).mass ancestors *
                        (forcedIndependentPopulation
                          (fun i => rowDistribution step.transition
                            (particles (ancestors i))) x next).mass nextParticles *
                        (forcedLineageSuffixLaw steps next future htailLength
                          nextParticles x).mass (tail, terminal))) = 0 by
                  apply Finset.sum_eq_zero
                  intro other _
                  by_cases hotherNext : nextParticles other = next
                  · rw [ih next future htailLength hsupport.2 nextParticles other
                      hotherNext (tail, terminal)]
                    by_cases hotherLineage :
                        initialAncestor steps tail terminal = other
                    · subst other
                      rw [forcedIndependentPopulation_incompatible_zero _ lineage
                        retained ancestors hancestor]
                      ring
                    · simp [hotherLineage]
                  · rw [forcedIndependentPopulation_incompatible_zero _ other next
                      nextParticles hotherNext]
                    ring]
              simp [initialAncestor, selectedTrajectory, lineage, hancestor,
                htrajectory]
          · rw [show (∑ x,
                  uniformParticleDistribution.mass x *
                    ((forcedIndependentPopulation
                      (fun _ => normalizedPotentialWeights step.potential
                        step.potential_pos particles) x retained).mass ancestors *
                      (forcedIndependentPopulation
                        (fun i => rowDistribution step.transition
                          (particles (ancestors i))) x next).mass nextParticles *
                      (forcedLineageSuffixLaw steps next future htailLength
                        nextParticles x).mass (tail, terminal))) = 0 by
                apply Finset.sum_eq_zero
                intro other _
                by_cases hotherNext : nextParticles other = next
                · rw [ih next future htailLength hsupport.2 nextParticles other
                    hotherNext (tail, terminal)]
                  simp [htrajectory]
                · rw [forcedIndependentPopulation_incompatible_zero _ other next
                    nextParticles hotherNext]
                  ring]
            simp [initialAncestor, selectedTrajectory, htrajectory]

/-- The concrete forced-lineage construction is the selected-particle target
restricted to one supported path, up to the path-marginal normalizer. -/
theorem forcedLineageLaw_mass_eq_scaled_target
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps)
    (first : Sample) (future : List Sample)
    (hlength : future.length = steps.length)
    (hinitial : 0 < initial.mass first)
    (hsupport : PathSuffixSupported steps first future)
    (selected : History (Particle := Particle) steps × Particle) :
    (forcedLineageLaw (Particle := Particle) initial steps (first :: future)
      (by simpa using congrArg Nat.succ hlength)).mass selected =
      if selectedTrajectory steps selected.1.1 selected.1.2 selected.2 =
          first :: future then
        (selectedParticleTarget (Particle := Particle) initial steps
          hnormalizer).mass selected * normalizingConstant initial steps /
            (initial.mass first * pathSuffixDensity steps first future)
      else 0 := by
  rcases selected with ⟨⟨particles, continuation⟩, terminal⟩
  unfold forcedLineageLaw
  simp only [Distribution.bind_mass, Distribution.map]
  have heq (ps : Particle → Sample)
      (suffix : Continuation Particle Sample steps × Particle) :
      (((particles, continuation), terminal) = ((ps, suffix.1), suffix.2)) ↔
        ps = particles ∧ suffix = (continuation, terminal) := by
    constructor
    · intro h
      cases h
      exact ⟨rfl, Prod.ext rfl rfl⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  simp only [heq]
  have hinner (retained : Particle) :
      (∑ ps,
        (forcedIndependentPopulation (fun _ => initial) retained first).mass ps *
          ∑ suffix,
            (forcedLineageSuffixLaw steps first future hlength ps retained).mass
                suffix *
              if ps = particles ∧ suffix = (continuation, terminal) then 1 else 0) =
        (forcedIndependentPopulation (fun _ => initial) retained first).mass
            particles *
          (forcedLineageSuffixLaw steps first future hlength particles retained).mass
            (continuation, terminal) := by
    rw [Finset.sum_eq_single particles]
    · rw [Finset.sum_eq_single (continuation, terminal)]
      · simp
      · intro suffix _ hsuffix
        simp [hsuffix]
      · simp
    · intro ps _ hps
      simp [hps]
    · simp
  simp_rw [hinner]
  let lineage := initialAncestor steps continuation terminal
  by_cases htrajectory :
      selectedTrajectory steps particles continuation terminal = first :: future
  · have hfirst : particles lineage = first := by
      have hhead := congrArg List.head? htrajectory
      rw [selectedTrajectory_head?] at hhead
      simpa [lineage] using hhead
    rw [Finset.sum_eq_single lineage]
    · rw [forcedIndependentPopulation_mass_eq_div
        (law := fun _ => initial) (retained := lineage) (value := first)
        hinitial particles]
      rw [forcedLineageSuffixLaw_mass steps first future hlength hsupport
        particles lineage hfirst (continuation, terminal)]
      simp only [hfirst, htrajectory, lineage, true_and, if_true]
      simp only [uniformParticleDistribution, selectedParticleTarget, historyLaw,
        normalizingWeight, fullHistoryValue]
      have hcard : (Fintype.card Particle : ℝ) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      have hpathDensity :
          initial.mass first * pathSuffixDensity steps first future ≠ 0 :=
        mul_ne_zero (ne_of_gt hinitial)
          (ne_of_gt (pathSuffixDensity_pos steps first future hsupport))
      have hiid :
          (independentPopulation (fun _ : Particle => initial)).mass particles =
            (iidPopulation initial).mass particles := by
        rfl
      rw [hiid]
      field_simp
    · intro other _ hother
      by_cases hotherFirst : particles other = first
      · rw [forcedLineageSuffixLaw_mass steps first future hlength hsupport
          particles other hotherFirst (continuation, terminal)]
        have hlineage : initialAncestor steps continuation terminal ≠ other := by
          simpa [lineage, eq_comm] using hother
        simp [hlineage]
      · rw [forcedIndependentPopulation_incompatible_zero _ other first particles
          hotherFirst]
        ring
    · simp
  · rw [show (∑ retained,
          uniformParticleDistribution.mass retained *
            ((forcedIndependentPopulation (fun _ => initial) retained first).mass
                particles *
              (forcedLineageSuffixLaw steps first future hlength particles retained).mass
                (continuation, terminal))) = 0 by
        apply Finset.sum_eq_zero
        intro retained _
        by_cases hretained : particles retained = first
        · rw [forcedLineageSuffixLaw_mass steps first future hlength hsupport
            particles retained hretained (continuation, terminal)]
          simp [htrajectory]
        · rw [forcedIndependentPopulation_incompatible_zero _ retained first particles
            hretained]
          ring]
    simp [htrajectory]

/-- Marginal mass of one trajectory under the selected-particle extended
target. This is the finite normalizer for exact conditional SMC. -/
noncomputable def selectedTrajectoryMass (initial : Distribution Sample)
    (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps)
    (path : List Sample) : ℝ :=
  ∑ selected, if selectedTrajectory steps selected.1.1 selected.1.2 selected.2 = path
    then (selectedParticleTarget (Particle := Particle) initial steps
      hnormalizer).mass selected else 0

theorem selectedTrajectoryMass_nonneg (initial : Distribution Sample)
    (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps)
    (path : List Sample) :
    0 ≤ selectedTrajectoryMass (Particle := Particle) initial steps hnormalizer path := by
  unfold selectedTrajectoryMass
  apply Finset.sum_nonneg
  intro selected _
  by_cases htrajectory :
      selectedTrajectory steps selected.1.1 selected.1.2 selected.2 = path
  · simp only [htrajectory, if_true]
    exact (selectedParticleTarget (Particle := Particle) initial steps
      hnormalizer).nonneg selected
  · simp [htrajectory]

/-- The trajectory marginal of the selected-particle target is the normalized
finite Feynman--Kac path density. -/
theorem selectedTrajectoryMass_eq_pathDensity_div
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps)
    (first : Sample) (future : List Sample)
    (hlength : future.length = steps.length)
    (hinitial : 0 < initial.mass first)
    (hsupport : PathSuffixSupported steps first future) :
    selectedTrajectoryMass (Particle := Particle) initial steps hnormalizer
        (first :: future) =
      initial.mass first * pathSuffixDensity steps first future /
        normalizingConstant initial steps := by
  let hpathLength : (first :: future).length = steps.length + 1 := by
    simpa using congrArg Nat.succ hlength
  have hsum :=
    (forcedLineageLaw (Particle := Particle) initial steps (first :: future)
      hpathLength).sum_mass
  rw [show (∑ selected,
      (forcedLineageLaw (Particle := Particle) initial steps (first :: future)
        hpathLength).mass selected) =
      selectedTrajectoryMass (Particle := Particle) initial steps hnormalizer
          (first :: future) * normalizingConstant initial steps /
        (initial.mass first * pathSuffixDensity steps first future) by
    unfold selectedTrajectoryMass
    rw [Finset.sum_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro selected _
    rw [forcedLineageLaw_mass_eq_scaled_target initial steps hnormalizer first
      future hlength hinitial hsupport selected]
    by_cases htrajectory :
        selectedTrajectory steps selected.1.1 selected.1.2 selected.2 =
          first :: future
    · simp [htrajectory]
    · simp [htrajectory]] at hsum
  have hnormalizer_ne : normalizingConstant initial steps ≠ 0 :=
    ne_of_gt hnormalizer
  have hdensity_ne :
      initial.mass first * pathSuffixDensity steps first future ≠ 0 :=
    mul_ne_zero (ne_of_gt hinitial)
      (ne_of_gt (pathSuffixDensity_pos steps first future hsupport))
  have hsuffix_ne : pathSuffixDensity steps first future ≠ 0 :=
    ne_of_gt (pathSuffixDensity_pos steps first future hsupport)
  field_simp [hsuffix_ne] at hsum ⊢
  nlinarith

theorem selectedTrajectoryMass_pos_of_supported
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps)
    (first : Sample) (future : List Sample)
    (hlength : future.length = steps.length)
    (hinitial : 0 < initial.mass first)
    (hsupport : PathSuffixSupported steps first future) :
    0 < selectedTrajectoryMass (Particle := Particle) initial steps hnormalizer
      (first :: future) := by
  rw [selectedTrajectoryMass_eq_pathDensity_div initial steps hnormalizer first
    future hlength hinitial hsupport]
  exact div_pos (mul_pos hinitial
    (pathSuffixDensity_pos steps first future hsupport)) hnormalizer

/-- Exact conditional law of an SMC history and retained terminal index given
its selected ancestral trajectory. This is the specification that a concrete
forced-lineage conditional-SMC implementation must refine. -/
noncomputable def conditionalSelectedParticleLaw (initial : Distribution Sample)
    (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps)
    (path : List Sample)
    (hpath : 0 < selectedTrajectoryMass (Particle := Particle) initial steps
      hnormalizer path) :
    Distribution (History (Particle := Particle) steps × Particle) where
  mass selected :=
    if selectedTrajectory steps selected.1.1 selected.1.2 selected.2 = path then
      (selectedParticleTarget (Particle := Particle) initial steps
        hnormalizer).mass selected /
        selectedTrajectoryMass (Particle := Particle) initial steps hnormalizer path
    else 0
  nonneg selected := by
    split
    · exact div_nonneg
        ((selectedParticleTarget (Particle := Particle) initial steps
          hnormalizer).nonneg selected) (le_of_lt hpath)
    · exact le_rfl
  sum_mass := by
    rw [show (∑ selected,
        if selectedTrajectory steps selected.1.1 selected.1.2 selected.2 = path then
          (selectedParticleTarget (Particle := Particle) initial steps
            hnormalizer).mass selected /
            selectedTrajectoryMass (Particle := Particle) initial steps hnormalizer path
        else 0) =
      selectedTrajectoryMass (Particle := Particle) initial steps hnormalizer path /
        selectedTrajectoryMass (Particle := Particle) initial steps hnormalizer path by
      calc
        _ = ∑ selected,
            (if selectedTrajectory steps selected.1.1 selected.1.2 selected.2 = path then
              (selectedParticleTarget (Particle := Particle) initial steps
                hnormalizer).mass selected else 0) /
              selectedTrajectoryMass (Particle := Particle) initial steps
                hnormalizer path := by
            apply Finset.sum_congr rfl
            intro selected _
            split <;> simp_all
        _ = _ := by rw [← Finset.sum_div]; rfl]
    exact div_self (ne_of_gt hpath)

/-- Concrete forced-lineage conditional SMC exactly implements the abstract
conditional law on every positive, supported reference path. -/
theorem forcedLineageLaw_eq_conditionalSelectedParticleLaw
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps)
    (first : Sample) (future : List Sample)
    (hlength : future.length = steps.length)
    (hinitial : 0 < initial.mass first)
    (hsupport : PathSuffixSupported steps first future) :
    forcedLineageLaw (Particle := Particle) initial steps (first :: future)
        (by simpa using congrArg Nat.succ hlength) =
      conditionalSelectedParticleLaw (Particle := Particle) initial steps
        hnormalizer (first :: future)
        (selectedTrajectoryMass_pos_of_supported initial steps hnormalizer first
          future hlength hinitial hsupport) := by
  apply Distribution.ext
  funext selected
  rw [forcedLineageLaw_mass_eq_scaled_target initial steps hnormalizer first
    future hlength hinitial hsupport selected]
  simp only [conditionalSelectedParticleLaw]
  rw [selectedTrajectoryMass_eq_pathDensity_div initial steps hnormalizer first
    future hlength hinitial hsupport]
  by_cases htrajectory :
      selectedTrajectory steps selected.1.1 selected.1.2 selected.2 =
        first :: future
  · simp only [htrajectory, if_true]
    have hnormalizer_ne : normalizingConstant initial steps ≠ 0 :=
      ne_of_gt hnormalizer
    have hdensity_ne :
        initial.mass first * pathSuffixDensity steps first future ≠ 0 :=
      mul_ne_zero (ne_of_gt hinitial)
        (ne_of_gt (pathSuffixDensity_pos steps first future hsupport))
    field_simp
  · simp [htrajectory]

/-- Conditional SMC is supported entirely on histories whose retained
genealogy is the supplied reference trajectory. -/
theorem conditionalSelectedParticleLaw_compatible (initial : Distribution Sample)
    (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps)
    (path : List Sample)
    (hpath : 0 < selectedTrajectoryMass (Particle := Particle) initial steps
      hnormalizer path)
    (selected : History (Particle := Particle) steps × Particle)
    (hincompatible :
      selectedTrajectory steps selected.1.1 selected.1.2 selected.2 ≠ path) :
    (conditionalSelectedParticleLaw (Particle := Particle) initial steps
      hnormalizer path hpath).mass selected = 0 := by
  simp [conditionalSelectedParticleLaw, hincompatible]

/-- Finite conditional factorization of the selected-particle extended target
into its trajectory marginal and exact conditional-SMC law. -/
theorem selectedParticleTarget_conditional_factorization
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps)
    (path : List Sample)
    (hpath : 0 < selectedTrajectoryMass (Particle := Particle) initial steps
      hnormalizer path)
    (selected : History (Particle := Particle) steps × Particle)
    (hselected :
      selectedTrajectory steps selected.1.1 selected.1.2 selected.2 = path) :
    selectedTrajectoryMass (Particle := Particle) initial steps hnormalizer path *
        (conditionalSelectedParticleLaw (Particle := Particle) initial steps
          hnormalizer path hpath).mass selected =
      (selectedParticleTarget (Particle := Particle) initial steps
        hnormalizer).mass selected := by
  simp only [conditionalSelectedParticleLaw, hselected, if_true]
  field_simp

/-- Exact conditional-SMC specification kernel. It refreshes the complete
history and retained index conditionally on the currently selected trajectory;
zero-mass fibers use the generic identity fallback. -/
noncomputable def conditionalSMCKernel (initial : Distribution Sample)
    (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps) :
    MarkovKernel (History (Particle := Particle) steps × Particle) :=
  Conditional.kernel
    (selectedParticleTarget (Particle := Particle) initial steps hnormalizer)
    (fun selected =>
      selectedTrajectory steps selected.1.1 selected.1.2 selected.2)

/-- The exact conditional-SMC refresh preserves the selected-particle
extended target. -/
theorem conditionalSMCKernel_stationary (initial : Distribution Sample)
    (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps) :
    (conditionalSMCKernel (Particle := Particle) initial steps hnormalizer).Stationary
      (selectedParticleTarget (Particle := Particle) initial steps hnormalizer) :=
  Conditional.kernel_stationary _ _

/-- On a positive trajectory fiber, the conditional-SMC kernel row is exactly
the normalized compatible-history law. -/
theorem conditionalSMCKernel_prob_eq_law (initial : Distribution Sample)
    (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps)
    (current proposed : History (Particle := Particle) steps × Particle)
    (hpath : 0 < selectedTrajectoryMass (Particle := Particle) initial steps
      hnormalizer
      (selectedTrajectory steps current.1.1 current.1.2 current.2)) :
    (conditionalSMCKernel (Particle := Particle) initial steps hnormalizer).prob
        current proposed =
      (conditionalSelectedParticleLaw (Particle := Particle) initial steps
        hnormalizer
        (selectedTrajectory steps current.1.1 current.1.2 current.2)
        hpath).mass proposed := by
  change (if h : 0 < selectedTrajectoryMass (Particle := Particle) initial steps
      hnormalizer (selectedTrajectory steps current.1.1 current.1.2 current.2) then
      if selectedTrajectory steps proposed.1.1 proposed.1.2 proposed.2 =
          selectedTrajectory steps current.1.1 current.1.2 current.2 then
        (selectedParticleTarget (Particle := Particle) initial steps
          hnormalizer).mass proposed /
          selectedTrajectoryMass (Particle := Particle) initial steps hnormalizer
            (selectedTrajectory steps current.1.1 current.1.2 current.2)
      else 0
    else if proposed = current then 1 else 0) = _
  rw [dif_pos hpath]
  rfl

/-- On a supported current trajectory, the abstract conditional-SMC kernel
row is computed exactly by the recursive forced-lineage sampler. -/
theorem conditionalSMCKernel_prob_eq_forcedLineageLaw
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps)
    (current proposed : History (Particle := Particle) steps × Particle)
    (first : Sample) (future : List Sample)
    (hcurrent : selectedTrajectory steps current.1.1 current.1.2 current.2 =
      first :: future)
    (hinitial : 0 < initial.mass first)
    (hsupport : PathSuffixSupported steps first future) :
    (conditionalSMCKernel (Particle := Particle) initial steps hnormalizer).prob
        current proposed =
      (forcedLineageLaw (Particle := Particle) initial steps (first :: future)
        (by simpa [← hcurrent] using
          selectedTrajectory_length steps current.1.1 current.1.2 current.2)).mass
        proposed := by
  have hlength : future.length = steps.length := by
    have := selectedTrajectory_length steps current.1.1 current.1.2 current.2
    simpa [hcurrent] using this
  have hpath := selectedTrajectoryMass_pos_of_supported
    (Particle := Particle) initial steps hnormalizer first future hlength hinitial
      hsupport
  rw [conditionalSMCKernel_prob_eq_law initial steps hnormalizer current proposed
    (by simpa [hcurrent] using hpath)]
  rw [forcedLineageLaw_eq_conditionalSelectedParticleLaw initial steps hnormalizer
    first future hlength hinitial hsupport]
  simp only [hcurrent]

end ConditionalSMC

/-- Proposal law for PIMH: draw a fresh SMC history and then select one
terminal particle uniformly. -/
noncomputable def particleIndependentProposalLaw (initial : Distribution Sample)
    (steps : List (FeynmanKacStep Sample)) :
    Distribution (History (Particle := Particle) steps × Particle) where
  mass proposed := (historyLaw (Particle := Particle) initial steps).mass proposed.1 /
    Fintype.card Particle
  nonneg proposed := div_nonneg
    ((historyLaw (Particle := Particle) initial steps).nonneg proposed.1) (by positivity)
  sum_mass := by
    rw [Fintype.sum_prod_type]
    have hcard : (Fintype.card Particle : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp_rw [show ∀ a : ℝ, (Fintype.card Particle : ℝ) *
      (a / Fintype.card Particle) = a by intro a; field_simp]
    exact (historyLaw (Particle := Particle) initial steps).sum_mass

/-- Turn a finite distribution into the corresponding state-independent
proposal kernel. -/
def independentProposalKernel {α : Type*} [Fintype α]
    (law : Distribution α) : MarkovKernel α where
  prob _ proposed := law.mass proposed
  nonneg _ proposed := law.nonneg proposed
  sum_prob _ := law.sum_mass

/-- Finite particle independent Metropolis--Hastings. A fresh particle system
is proposed independently and MH-corrected toward the history-weighted target. -/
noncomputable def pimhKernel (initial : Distribution Sample)
    (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps) :
    MarkovKernel (History (Particle := Particle) steps × Particle) :=
  MetropolisHastings.kernelAllowZeros
    (selectedParticleTarget (Particle := Particle) initial steps hnormalizer)
    (independentProposalKernel
      (particleIndependentProposalLaw (Particle := Particle) initial steps))

/-- Exact extended-target stationarity of finite PIMH. -/
theorem pimhKernel_stationary (initial : Distribution Sample)
    (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps) :
    (pimhKernel (Particle := Particle) initial steps hnormalizer).Stationary
      (selectedParticleTarget (Particle := Particle) initial steps hnormalizer) :=
  MetropolisHastings.stationary_allowZeros _ _

omit [DecidableEq Sample] in
/-- At PIMH stationarity, every selected-path observable has the exact
normalized Feynman--Kac expectation. -/
theorem pimh_stationary_selectedTrajectory_expectation
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps)
    (observable : List Sample → ℝ) :
    ∑ selected, (selectedParticleTarget (Particle := Particle) initial steps
        hnormalizer).mass selected *
      observable (selectedTrajectory steps selected.1.1 selected.1.2 selected.2) =
      (∑ x, initial.mass x * pathFeynmanKacValue steps observable x) /
        normalizingConstant initial steps :=
  selectedParticleTarget_selectedTrajectory_expectation initial steps
    hnormalizer observable

section ParticleGibbs

/-- State-independent uniform refresh of a finite nonempty selected index. -/
noncomputable def uniformIndexKernel : MarkovKernel Particle where
  prob _ _ := 1 / Fintype.card Particle
  nonneg _ _ := by positivity
  sum_prob _ := by
    have hcard : (Fintype.card Particle : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp [hcard]

/-- Hold an SMC history fixed and choose a fresh terminal particle uniformly. -/
noncomputable def selectedIndexRefreshKernel
    (steps : List (FeynmanKacStep Sample)) :
    MarkovKernel (History (Particle := Particle) steps × Particle) :=
  liftSnd (fun _ => uniformIndexKernel (Particle := Particle))

/-- Uniform terminal-index refresh preserves the selected-particle extended
target because its mass is uniform in the selected index conditional on a
complete history. -/
theorem selectedIndexRefreshKernel_stationary (initial : Distribution Sample)
    (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps) :
    (selectedIndexRefreshKernel (Particle := Particle) steps).Stationary
      (selectedParticleTarget (Particle := Particle) initial steps hnormalizer) := by
  unfold selectedIndexRefreshKernel
  apply Gibbs.liftSnd_stationary
  intro history proposedIndex
  unfold selectedParticleTarget uniformIndexKernel
  have hcard : (Fintype.card Particle : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- With one particle there is no terminal-index choice, so index refresh is
the identity transition. -/
theorem selectedIndexRefreshKernel_unit_eq_identity
    (steps : List (FeynmanKacStep Sample)) :
    selectedIndexRefreshKernel (Particle := Unit) steps = identity := by
  apply MarkovKernel.ext
  funext current proposed
  rcases current with ⟨history, terminal⟩
  rcases proposed with ⟨history', terminal'⟩
  cases terminal
  cases terminal'
  simp [selectedIndexRefreshKernel, liftSnd, uniformIndexKernel, identity]

/-- Finite particle Gibbs: conditionally refresh the complete particle system
while retaining the current trajectory, then uniformly select a new terminal
particle from that system. -/
noncomputable def particleGibbsKernel (initial : Distribution Sample)
    (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps) :
    MarkovKernel (History (Particle := Particle) steps × Particle) :=
  comp (selectedIndexRefreshKernel (Particle := Particle) steps)
    (conditionalSMCKernel (Particle := Particle) initial steps hnormalizer)

/-- Exact extended-target stationarity of finite particle Gibbs. -/
theorem particleGibbsKernel_stationary (initial : Distribution Sample)
    (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps) :
    (particleGibbsKernel (Particle := Particle) initial steps hnormalizer).Stationary
      (selectedParticleTarget (Particle := Particle) initial steps hnormalizer) :=
  comp_stationary _ _ _
    (conditionalSMCKernel_stationary (Particle := Particle) initial steps hnormalizer)
    (selectedIndexRefreshKernel_stationary (Particle := Particle) initial steps
      hnormalizer)

/-- One-particle particle Gibbs is exactly the identity kernel.  Thus target
stationarity alone cannot imply convergence or useful mixing uniformly over
particle count; at least two particles and further support hypotheses are
genuinely necessary. -/
theorem particleGibbsKernel_unit_eq_identity (initial : Distribution Sample)
    (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps) :
    particleGibbsKernel (Particle := Unit) initial steps hnormalizer = identity := by
  have hconditional :
      conditionalSMCKernel (Particle := Unit) initial steps hnormalizer =
        identity := by
    unfold conditionalSMCKernel
    exact Conditional.kernel_eq_identity_of_injective _ _
      (selectedTrajectory_injective_unit steps)
  rw [particleGibbsKernel, hconditional,
    selectedIndexRefreshKernel_unit_eq_identity]
  simp

omit [DecidableEq Sample] in
/-- Particle Gibbs has the exact normalized Feynman--Kac trajectory marginal
at stationarity. -/
theorem particleGibbs_stationary_selectedTrajectory_expectation
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps)
    (observable : List Sample → ℝ) :
    ∑ selected, (selectedParticleTarget (Particle := Particle) initial steps
        hnormalizer).mass selected *
      observable (selectedTrajectory steps selected.1.1 selected.1.2 selected.2) =
      (∑ x, initial.mass x * pathFeynmanKacValue steps observable x) /
        normalizingConstant initial steps :=
  selectedParticleTarget_selectedTrajectory_expectation initial steps
    hnormalizer observable

end ParticleGibbs

/-- Eventwise form of the selected-terminal marginal identity. -/
theorem selectedParticleTarget_terminal_event (initial : Distribution Sample)
    (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps) (terminal : Sample) :
    ∑ selected, (selectedParticleTarget (Particle := Particle) initial steps
        hnormalizer).mass selected *
      (if terminalPopulation steps selected.1.1 selected.1.2 selected.2 = terminal
        then 1 else 0) =
      (∑ x, initial.mass x * feynmanKacSequence steps
        (fun y => if y = terminal then 1 else 0) x) /
          normalizingConstant initial steps :=
  selectedParticleTarget_expectation initial steps hnormalizer
    (fun y => if y = terminal then 1 else 0)

omit [DecidableEq Sample] in
/-- The terminal endpoint theorem restated directly through the extracted
ancestral trajectory. -/
theorem selectedTrajectory_terminal_expectation (initial : Distribution Sample)
    (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps)
    (observable : Option Sample → ℝ) :
    ∑ selected, (selectedParticleTarget (Particle := Particle) initial steps
        hnormalizer).mass selected *
      observable (selectedTrajectory steps selected.1.1 selected.1.2
        selected.2).getLast? =
      (∑ x, initial.mass x * feynmanKacSequence steps
        (fun y => observable (some y)) x) / normalizingConstant initial steps := by
  simp_rw [selectedTrajectory_getLast?]
  exact selectedParticleTarget_expectation initial steps hnormalizer
    (fun y => observable (some y))

section PseudoMarginalClient

variable {State : Type*} [Fintype State] [DecidableEq State]

/-- A state-indexed explicit SMC estimator. The transition/potential schedule
is shared, while the initial law may depend on the proposed state. Dividing by
the exact positive normalizer produces the unit-mean estimator interface used
by the finite pseudo-marginal theorem. -/
noncomputable def estimator (initial : State → Distribution Sample)
    (steps : List (FeynmanKacStep Sample))
    (hnormalizer : ∀ x, 0 < normalizingConstant (initial x) steps) :
    PseudoMarginal.Estimator State (History (Particle := Particle) steps) where
  law x := historyLaw (Particle := Particle) (initial x) steps
  value x history := normalizingWeight steps history /
    normalizingConstant (initial x) steps
  nonneg x history := div_nonneg (normalizingWeight_nonneg steps history)
    (le_of_lt (hnormalizer x))
  unbiased x := by
    rw [show (∑ history,
        (historyLaw (Particle := Particle) (initial x) steps).mass history *
          (normalizingWeight steps history / normalizingConstant (initial x) steps)) =
        (∑ history,
          (historyLaw (Particle := Particle) (initial x) steps).mass history *
            normalizingWeight steps history) /
          normalizingConstant (initial x) steps by
      simp_rw [div_eq_mul_inv, ← mul_assoc]
      rw [Finset.sum_mul]]
    rw [normalizingWeight_expectation]
    exact div_self (ne_of_gt (hnormalizer x))

/-- Pseudo-marginal MH driven by a complete finite SMC history, retaining that
history on rejection. -/
noncomputable def kernel (target : Distribution State)
    (initial : State → Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : ∀ x, 0 < normalizingConstant (initial x) steps)
    (proposal : MarkovKernel State) :
    MarkovKernel (State × History (Particle := Particle) steps) :=
  PseudoMarginal.kernel target
    (estimator (Particle := Particle) initial steps hnormalizer) proposal

/-- Exact stationarity of the explicit-history SMC pseudo-marginal kernel. -/
theorem kernel_stationary (target : Distribution State)
    (initial : State → Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : ∀ x, 0 < normalizingConstant (initial x) steps)
    (proposal : MarkovKernel State) :
    (kernel (Particle := Particle) target initial steps hnormalizer proposal).Stationary
      (PseudoMarginal.extendedTarget target
        (estimator (Particle := Particle) initial steps hnormalizer)) :=
  PseudoMarginal.stationary target
    (estimator (Particle := Particle) initial steps hnormalizer) proposal

omit [DecidableEq Sample] [DecidableEq State] in
/-- The stationary state marginal of explicit-history SMC pseudo-marginal MH
is exactly the requested target. -/
theorem kernel_state_marginal (target : Distribution State)
    (initial : State → Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : ∀ x, 0 < normalizingConstant (initial x) steps) (x : State) :
    ∑ history, (PseudoMarginal.extendedTarget target
      (estimator (Particle := Particle) initial steps hnormalizer)).mass
        (x, history) = target.mass x :=
  PseudoMarginal.state_marginal target
    (estimator (Particle := Particle) initial steps hnormalizer) x

/-- PMMH estimator state: a complete SMC history together with its selected
terminal-particle index. -/
noncomputable def pmmhEstimator (initial : State → Distribution Sample)
    (steps : List (FeynmanKacStep Sample))
    (hnormalizer : ∀ x, 0 < normalizingConstant (initial x) steps) :
    PseudoMarginal.Estimator State
      (History (Particle := Particle) steps × Particle) where
  law x := particleIndependentProposalLaw (Particle := Particle) (initial x) steps
  value x selected := normalizingWeight steps selected.1 /
    normalizingConstant (initial x) steps
  nonneg x selected := div_nonneg (normalizingWeight_nonneg steps selected.1)
    (le_of_lt (hnormalizer x))
  unbiased x := by
    rw [Fintype.sum_prod_type]
    have hcard : (Fintype.card Particle : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    change ∑ history, ∑ _i : Particle,
      ((historyLaw (Particle := Particle) (initial x) steps).mass history /
        Fintype.card Particle) *
      (normalizingWeight steps history / normalizingConstant (initial x) steps) = 1
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp_rw [show ∀ a b : ℝ, (Fintype.card Particle : ℝ) *
        ((a / Fintype.card Particle) * b) = a * b by
      intro a b; field_simp]
    rw [show (∑ history,
        (historyLaw (Particle := Particle) (initial x) steps).mass history *
          (normalizingWeight steps history / normalizingConstant (initial x) steps)) =
      (∑ history,
        (historyLaw (Particle := Particle) (initial x) steps).mass history *
          normalizingWeight steps history) / normalizingConstant (initial x) steps by
      simp_rw [div_eq_mul_inv, ← mul_assoc]
      rw [Finset.sum_mul]]
    rw [normalizingWeight_expectation]
    exact div_self (ne_of_gt (hnormalizer x))

/-- Finite particle marginal Metropolis--Hastings, retaining the parameter,
SMC history, and selected terminal index on rejection. -/
noncomputable def pmmhKernel (target : Distribution State)
    (initial : State → Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : ∀ x, 0 < normalizingConstant (initial x) steps)
    (proposal : MarkovKernel State) :
    MarkovKernel (State × (History (Particle := Particle) steps × Particle)) :=
  PseudoMarginal.kernel target
    (pmmhEstimator (Particle := Particle) initial steps hnormalizer) proposal

/-- Exact extended-target stationarity of finite PMMH. -/
theorem pmmhKernel_stationary (target : Distribution State)
    (initial : State → Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : ∀ x, 0 < normalizingConstant (initial x) steps)
    (proposal : MarkovKernel State) :
    (pmmhKernel (Particle := Particle) target initial steps hnormalizer proposal).Stationary
      (PseudoMarginal.extendedTarget target
        (pmmhEstimator (Particle := Particle) initial steps hnormalizer)) :=
  PseudoMarginal.stationary target
    (pmmhEstimator (Particle := Particle) initial steps hnormalizer) proposal

omit [DecidableEq Sample] [DecidableEq State] in
/-- PMMH has exactly the requested stationary parameter marginal. -/
theorem pmmhKernel_state_marginal (target : Distribution State)
    (initial : State → Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : ∀ x, 0 < normalizingConstant (initial x) steps) (x : State) :
    ∑ selected, (PseudoMarginal.extendedTarget target
      (pmmhEstimator (Particle := Particle) initial steps hnormalizer)).mass
        (x, selected) = target.mass x :=
  PseudoMarginal.state_marginal target
    (pmmhEstimator (Particle := Particle) initial steps hnormalizer) x

omit [DecidableEq Sample] [DecidableEq State] in
/-- A parameter slice of the PMMH extended target is the parameter mass times
the corresponding history-weighted selected-particle target. -/
theorem pmmh_extendedTarget_slice (target : Distribution State)
    (initial : State → Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : ∀ x, 0 < normalizingConstant (initial x) steps)
    (x : State) (selected : History (Particle := Particle) steps × Particle) :
    (PseudoMarginal.extendedTarget target
      (pmmhEstimator (Particle := Particle) initial steps hnormalizer)).mass
        (x, selected) =
      target.mass x *
        (selectedParticleTarget (Particle := Particle) (initial x) steps
          (hnormalizer x)).mass selected := by
  unfold PseudoMarginal.extendedTarget pmmhEstimator
    particleIndependentProposalLaw selectedParticleTarget
  ring

omit [DecidableEq Sample] [DecidableEq State] in
/-- At PMMH stationarity, the joint parameter/selected-path expectation is the
target-weighted normalized Feynman--Kac path expectation. -/
theorem pmmh_stationary_selectedTrajectory_expectation
    (target : Distribution State) (initial : State → Distribution Sample)
    (steps : List (FeynmanKacStep Sample))
    (hnormalizer : ∀ x, 0 < normalizingConstant (initial x) steps)
    (observable : State → List Sample → ℝ) :
    ∑ extended, (PseudoMarginal.extendedTarget target
        (pmmhEstimator (Particle := Particle) initial steps hnormalizer)).mass extended *
      observable extended.1
        (selectedTrajectory steps extended.2.1.1 extended.2.1.2 extended.2.2) =
      ∑ x, target.mass x *
        ((∑ y, (initial x).mass y *
          pathFeynmanKacValue steps (observable x) y) /
            normalizingConstant (initial x) steps) := by
  rw [Fintype.sum_prod_type]
  simp_rw [pmmh_extendedTarget_slice]
  simp_rw [show ∀ (x : State)
      (selected : History (Particle := Particle) steps × Particle),
      target.mass x *
          (selectedParticleTarget (Particle := Particle) (initial x) steps
            (hnormalizer x)).mass selected *
          observable x
            (selectedTrajectory steps selected.1.1 selected.1.2 selected.2) =
        target.mass x *
          ((selectedParticleTarget (Particle := Particle) (initial x) steps
            (hnormalizer x)).mass selected *
          observable x
            (selectedTrajectory steps selected.1.1 selected.1.2 selected.2)) by
      intro x selected; ring,
    ← Finset.mul_sum,
    selectedParticleTarget_selectedTrajectory_expectation]

section StateIndexedSchedule

variable [Nonempty State]

/-- A fixed-horizon schedule whose potential and transition may depend on the
pseudo-marginal state. The list shape is shared, so all states use the same
finite history type. -/
abbrev StateIndexedSchedule := List (State → FeynmanKacStep Sample)

/-- Instantiate a state-indexed schedule at one proposed state. -/
def stepsAt (schedule : StateIndexedSchedule (State := State) (Sample := Sample))
    (x : State) : List (FeynmanKacStep Sample) :=
  schedule.map fun step => step x

/-- Common explicit-history type for a state-indexed fixed-horizon schedule.
The anchor affects step values but not the recursively defined history shape. -/
abbrev StateIndexedHistory
    (schedule : StateIndexedSchedule (State := State) (Sample := Sample)) :=
  History (Particle := Particle) (stepsAt schedule (Classical.choice inferInstance))

/-- Explicit SMC estimator with state-indexed initial law, potentials, and
transition kernels at a common finite horizon. -/
noncomputable def stateIndexedEstimator
    (initial : State → Distribution Sample)
    (schedule : StateIndexedSchedule (State := State) (Sample := Sample))
    (hnormalizer : ∀ x,
      0 < normalizingConstant (initial x) (stepsAt schedule x)) :
    PseudoMarginal.Estimator State
      (StateIndexedHistory (Particle := Particle) schedule) where
  law x := relabelDistribution
    (historyLaw (Particle := Particle) (initial x) (stepsAt schedule x))
    (historyEquivOfLength (Particle := Particle) (stepsAt schedule x)
      (stepsAt schedule (Classical.choice inferInstance)) (by
        simp [stepsAt]))
  value x history := normalizingWeight (stepsAt schedule x)
      ((historyEquivOfLength (Particle := Particle) (stepsAt schedule x)
        (stepsAt schedule (Classical.choice inferInstance)) (by
          simp [stepsAt])).symm history) /
    normalizingConstant (initial x) (stepsAt schedule x)
  nonneg x history := div_nonneg
    (normalizingWeight_nonneg (stepsAt schedule x)
      ((historyEquivOfLength (Particle := Particle) (stepsAt schedule x)
        (stepsAt schedule (Classical.choice inferInstance)) (by
          simp [stepsAt])).symm history))
    (le_of_lt (hnormalizer x))
  unbiased x := by
    let e := historyEquivOfLength (Particle := Particle) (stepsAt schedule x)
      (stepsAt schedule (Classical.choice inferInstance)) (by simp [stepsAt])
    change ∑ history,
        (historyLaw (Particle := Particle) (initial x) (stepsAt schedule x)).mass
            (e.symm history) *
          (normalizingWeight (stepsAt schedule x) (e.symm history) /
            normalizingConstant (initial x) (stepsAt schedule x)) = 1
    rw [← Fintype.sum_equiv e
      (fun history =>
        (historyLaw (Particle := Particle) (initial x) (stepsAt schedule x)).mass history *
          (normalizingWeight (stepsAt schedule x) history /
            normalizingConstant (initial x) (stepsAt schedule x)))
      (fun history =>
        (historyLaw (Particle := Particle) (initial x) (stepsAt schedule x)).mass
            (e.symm history) *
          (normalizingWeight (stepsAt schedule x) (e.symm history) /
            normalizingConstant (initial x) (stepsAt schedule x))) (fun history => by simp)]
    rw [show (∑ history,
        (historyLaw (Particle := Particle) (initial x) (stepsAt schedule x)).mass history *
          (normalizingWeight (stepsAt schedule x) history /
            normalizingConstant (initial x) (stepsAt schedule x))) =
        (∑ history,
          (historyLaw (Particle := Particle) (initial x) (stepsAt schedule x)).mass history *
            normalizingWeight (stepsAt schedule x) history) /
          normalizingConstant (initial x) (stepsAt schedule x) by
      simp_rw [div_eq_mul_inv, ← mul_assoc]
      rw [Finset.sum_mul]]
    rw [normalizingWeight_expectation]
    exact div_self (ne_of_gt (hnormalizer x))

/-- Pseudo-marginal MH driven by state-indexed finite SMC schedules. -/
noncomputable def stateIndexedKernel (target : Distribution State)
    (initial : State → Distribution Sample)
    (schedule : StateIndexedSchedule (State := State) (Sample := Sample))
    (hnormalizer : ∀ x,
      0 < normalizingConstant (initial x) (stepsAt schedule x))
    (proposal : MarkovKernel State) :
    MarkovKernel (State × StateIndexedHistory (Particle := Particle) schedule) :=
  PseudoMarginal.kernel target
    (stateIndexedEstimator (Particle := Particle) initial schedule hnormalizer) proposal

/-- Exact extended-target stationarity with state-indexed potentials and
transition kernels. -/
theorem stateIndexedKernel_stationary (target : Distribution State)
    (initial : State → Distribution Sample)
    (schedule : StateIndexedSchedule (State := State) (Sample := Sample))
    (hnormalizer : ∀ x,
      0 < normalizingConstant (initial x) (stepsAt schedule x))
    (proposal : MarkovKernel State) :
    (stateIndexedKernel (Particle := Particle) target initial schedule
      hnormalizer proposal).Stationary
      (PseudoMarginal.extendedTarget target
        (stateIndexedEstimator (Particle := Particle) initial schedule hnormalizer)) :=
  PseudoMarginal.stationary target
    (stateIndexedEstimator (Particle := Particle) initial schedule hnormalizer) proposal

omit [DecidableEq Sample] [DecidableEq State] in
/-- The stationary state marginal remains exactly the requested target when
the entire fixed-horizon SMC schedule depends on state. -/
theorem stateIndexedKernel_state_marginal (target : Distribution State)
    (initial : State → Distribution Sample)
    (schedule : StateIndexedSchedule (State := State) (Sample := Sample))
    (hnormalizer : ∀ x,
      0 < normalizingConstant (initial x) (stepsAt schedule x)) (x : State) :
    ∑ history, (PseudoMarginal.extendedTarget target
      (stateIndexedEstimator (Particle := Particle) initial schedule hnormalizer)).mass
        (x, history) = target.mass x :=
  PseudoMarginal.state_marginal target
    (stateIndexedEstimator (Particle := Particle) initial schedule hnormalizer) x

/-- Relabel a state-specific SMC history and selected terminal index into the
common fixed-horizon PMMH auxiliary-state type. -/
noncomputable def stateIndexedSelectedEquiv
    (schedule : StateIndexedSchedule (State := State) (Sample := Sample))
    (x : State) :
    (History (Particle := Particle) (stepsAt schedule x) × Particle) ≃
      (StateIndexedHistory (Particle := Particle) schedule × Particle) :=
  Equiv.prodCongr
    (historyEquivOfLength (Particle := Particle) (stepsAt schedule x)
      (stepsAt schedule (Classical.choice inferInstance)) (by simp [stepsAt]))
    (Equiv.refl Particle)

/-- PMMH estimator with state-indexed initial law, potentials, and transition
kernels. The complete history and selected terminal index are transported to
one common auxiliary-state type using the shared schedule length. -/
noncomputable def stateIndexedPmmhEstimator
    (initial : State → Distribution Sample)
    (schedule : StateIndexedSchedule (State := State) (Sample := Sample))
    (hnormalizer : ∀ x,
      0 < normalizingConstant (initial x) (stepsAt schedule x)) :
    PseudoMarginal.Estimator State
      (StateIndexedHistory (Particle := Particle) schedule × Particle) where
  law x := relabelDistribution
    (particleIndependentProposalLaw (Particle := Particle) (initial x)
      (stepsAt schedule x))
    (stateIndexedSelectedEquiv (Particle := Particle) schedule x)
  value x selected :=
    normalizingWeight (stepsAt schedule x)
        ((stateIndexedSelectedEquiv (Particle := Particle) schedule x).symm selected).1 /
      normalizingConstant (initial x) (stepsAt schedule x)
  nonneg x selected := div_nonneg
    (normalizingWeight_nonneg (stepsAt schedule x)
      ((stateIndexedSelectedEquiv (Particle := Particle) schedule x).symm selected).1)
    (le_of_lt (hnormalizer x))
  unbiased x := by
    let e := stateIndexedSelectedEquiv (Particle := Particle) schedule x
    change ∑ selected,
        (particleIndependentProposalLaw (Particle := Particle) (initial x)
          (stepsAt schedule x)).mass (e.symm selected) *
        (normalizingWeight (stepsAt schedule x) (e.symm selected).1 /
          normalizingConstant (initial x) (stepsAt schedule x)) = 1
    rw [← Fintype.sum_equiv e
      (fun selected =>
        (particleIndependentProposalLaw (Particle := Particle) (initial x)
          (stepsAt schedule x)).mass selected *
        (normalizingWeight (stepsAt schedule x) selected.1 /
          normalizingConstant (initial x) (stepsAt schedule x)))
      (fun selected =>
        (particleIndependentProposalLaw (Particle := Particle) (initial x)
          (stepsAt schedule x)).mass (e.symm selected) *
        (normalizingWeight (stepsAt schedule x) (e.symm selected).1 /
          normalizingConstant (initial x) (stepsAt schedule x))) (fun selected => by simp)]
    exact (pmmhEstimator (Particle := Particle) (fun _ : State => initial x)
      (stepsAt schedule x) (fun _ => hnormalizer x)).unbiased x

/-- Finite PMMH with a complete parameter-indexed SMC schedule, retaining the
parameter, relabeled history, and selected terminal index on rejection. -/
noncomputable def stateIndexedPmmhKernel (target : Distribution State)
    (initial : State → Distribution Sample)
    (schedule : StateIndexedSchedule (State := State) (Sample := Sample))
    (hnormalizer : ∀ x,
      0 < normalizingConstant (initial x) (stepsAt schedule x))
    (proposal : MarkovKernel State) :
    MarkovKernel
      (State × (StateIndexedHistory (Particle := Particle) schedule × Particle)) :=
  PseudoMarginal.kernel target
    (stateIndexedPmmhEstimator (Particle := Particle) initial schedule hnormalizer)
    proposal

/-- Exact extended-target stationarity of finite PMMH with fully
state-indexed schedules. -/
theorem stateIndexedPmmhKernel_stationary (target : Distribution State)
    (initial : State → Distribution Sample)
    (schedule : StateIndexedSchedule (State := State) (Sample := Sample))
    (hnormalizer : ∀ x,
      0 < normalizingConstant (initial x) (stepsAt schedule x))
    (proposal : MarkovKernel State) :
    (stateIndexedPmmhKernel (Particle := Particle) target initial schedule
      hnormalizer proposal).Stationary
      (PseudoMarginal.extendedTarget target
        (stateIndexedPmmhEstimator (Particle := Particle) initial schedule
          hnormalizer)) :=
  PseudoMarginal.stationary target
    (stateIndexedPmmhEstimator (Particle := Particle) initial schedule hnormalizer)
    proposal

omit [DecidableEq Sample] [DecidableEq State] in
/-- Fully state-indexed PMMH has exactly the requested stationary parameter
marginal. -/
theorem stateIndexedPmmhKernel_state_marginal (target : Distribution State)
    (initial : State → Distribution Sample)
    (schedule : StateIndexedSchedule (State := State) (Sample := Sample))
    (hnormalizer : ∀ x,
      0 < normalizingConstant (initial x) (stepsAt schedule x)) (x : State) :
    ∑ selected, (PseudoMarginal.extendedTarget target
      (stateIndexedPmmhEstimator (Particle := Particle) initial schedule
        hnormalizer)).mass (x, selected) = target.mass x :=
  PseudoMarginal.state_marginal target
    (stateIndexedPmmhEstimator (Particle := Particle) initial schedule hnormalizer) x

/-- Extract the selected ancestral trajectory using the schedule belonging to
the retained parameter. -/
noncomputable def stateIndexedSelectedTrajectory
    (schedule : StateIndexedSchedule (State := State) (Sample := Sample))
    (x : State)
    (selected : StateIndexedHistory (Particle := Particle) schedule × Particle) :
    List Sample :=
  let source :=
    (stateIndexedSelectedEquiv (Particle := Particle) schedule x).symm selected
  selectedTrajectory (stepsAt schedule x) source.1.1 source.1.2 source.2

omit [DecidableEq Sample] [DecidableEq State] in
/-- At stationarity, fully state-indexed PMMH has the target-weighted exact
Feynman--Kac path expectation for each parameter-specific schedule. -/
theorem stateIndexedPmmh_stationary_selectedTrajectory_expectation
    (target : Distribution State) (initial : State → Distribution Sample)
    (schedule : StateIndexedSchedule (State := State) (Sample := Sample))
    (hnormalizer : ∀ x,
      0 < normalizingConstant (initial x) (stepsAt schedule x))
    (observable : State → List Sample → ℝ) :
    ∑ extended, (PseudoMarginal.extendedTarget target
        (stateIndexedPmmhEstimator (Particle := Particle) initial schedule
          hnormalizer)).mass extended *
      observable extended.1
        (stateIndexedSelectedTrajectory (Particle := Particle) schedule
          extended.1 extended.2) =
      ∑ x, target.mass x *
        ((∑ y, (initial x).mass y *
          pathFeynmanKacValue (stepsAt schedule x) (observable x) y) /
            normalizingConstant (initial x) (stepsAt schedule x)) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  let e := stateIndexedSelectedEquiv (Particle := Particle) schedule x
  simp only [PseudoMarginal.extendedTarget, stateIndexedPmmhEstimator,
    relabelDistribution, stateIndexedSelectedTrajectory]
  change ∑ selected,
      target.mass x *
          (particleIndependentProposalLaw (Particle := Particle) (initial x)
            (stepsAt schedule x)).mass (e.symm selected) *
          (normalizingWeight (stepsAt schedule x) (e.symm selected).1 /
            normalizingConstant (initial x) (stepsAt schedule x)) *
        observable x
          (selectedTrajectory (stepsAt schedule x) (e.symm selected).1.1
            (e.symm selected).1.2 (e.symm selected).2) = _
  rw [← Fintype.sum_equiv e
    (fun selected =>
      target.mass x *
          (particleIndependentProposalLaw (Particle := Particle) (initial x)
            (stepsAt schedule x)).mass selected *
          (normalizingWeight (stepsAt schedule x) selected.1 /
            normalizingConstant (initial x) (stepsAt schedule x)) *
        observable x
          (selectedTrajectory (stepsAt schedule x) selected.1.1 selected.1.2
            selected.2))
    (fun selected =>
      target.mass x *
          (particleIndependentProposalLaw (Particle := Particle) (initial x)
            (stepsAt schedule x)).mass (e.symm selected) *
          (normalizingWeight (stepsAt schedule x) (e.symm selected).1 /
            normalizingConstant (initial x) (stepsAt schedule x)) *
        observable x
          (selectedTrajectory (stepsAt schedule x) (e.symm selected).1.1
            (e.symm selected).1.2 (e.symm selected).2)) (fun selected => by simp)]
  rw [show (∑ selected,
      target.mass x *
          (particleIndependentProposalLaw (Particle := Particle) (initial x)
            (stepsAt schedule x)).mass selected *
          (normalizingWeight (stepsAt schedule x) selected.1 /
            normalizingConstant (initial x) (stepsAt schedule x)) *
        observable x
          (selectedTrajectory (stepsAt schedule x) selected.1.1 selected.1.2
            selected.2)) =
      target.mass x * ∑ selected,
        (selectedParticleTarget (Particle := Particle) (initial x)
          (stepsAt schedule x) (hnormalizer x)).mass selected *
        observable x
          (selectedTrajectory (stepsAt schedule x) selected.1.1 selected.1.2
            selected.2) by
    unfold particleIndependentProposalLaw selectedParticleTarget
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro selected _
    ring]
  rw [selectedParticleTarget_selectedTrajectory_expectation]

end StateIndexedSchedule

end PseudoMarginalClient

end Mcmc.Finite.SequentialMonteCarlo
