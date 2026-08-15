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
