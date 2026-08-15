import Mcmc.Finite.ParticleEstimator
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

end StateIndexedSchedule

end PseudoMarginalClient

end Mcmc.Finite.SequentialMonteCarlo
