import Mcmc.PDMP.Poissonization
import Mathlib.Data.Vector.Snoc
import Mathlib.Tactic

/-!
# Finite event-skeleton paths

For a finite uniformized jump kernel, this file constructs the exact law of
the state sequence after a fixed number of clock events. The terminal marginal
is proved equal to the corresponding kernel iterate. This is the finite path
skeleton beneath Poissonization; continuous event times and a càdlàg path-space
measure are deliberately separate.
-/

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace Mcmc.PDMP

open Mcmc.Finite MarkovKernel

variable {State : Type*} [Fintype State] [DecidableEq State]

omit [Fintype State] [DecidableEq State] in
@[simp] theorem vector_last_snoc {n : ℕ} (path : List.Vector State n)
    (next : State) : (path.snoc next).last = next := by
  rw [← List.Vector.reverse_get_zero]
  simp

/-- A point mass in the elementary finite distribution interface. -/
def pointLaw (x : State) : Distribution State where
  mass y := if y = x then 1 else 0
  nonneg y := by split <;> norm_num
  sum_mass := by simp

/-- One row of a finite Markov kernel as a distribution. -/
def transitionRow (transition : MarkovKernel State) (x : State) :
    Distribution State where
  mass y := transition.prob x y
  nonneg y := transition.nonneg x y
  sum_mass := transition.sum_prob x

/-- Exact state-sequence law after `events` transitions from a fixed initial
state. The vector includes the initial state, hence has length `events + 1`. -/
noncomputable def eventPathLaw (transition : MarkovKernel State) (initial : State) :
    (events : ℕ) → Distribution (List.Vector State (events + 1))
  | 0 => Distribution.map (pointLaw initial)
      (fun x => x ::ᵥ List.Vector.nil)
  | events + 1 =>
      Distribution.bind (eventPathLaw transition initial events) fun path =>
        Distribution.map (transitionRow transition path.last) path.snoc

/-- Fixed-event path expectation agrees with the corresponding iterated-kernel
expectation of the terminal state. -/
theorem eventPathLaw_terminal_expectation
    (transition : MarkovKernel State) (initial : State) (events : ℕ)
    (observable : State → ℝ) :
    ∑ path, (eventPathLaw transition initial events).mass path *
        observable path.last =
      ∑ terminal, (kernelIterate transition events).prob initial terminal *
        observable terminal := by
  induction events generalizing observable with
  | zero =>
      simp [eventPathLaw, pointLaw, kernelIterate,
        Distribution.map_expectation]
      rfl
  | succ events ih =>
      rw [eventPathLaw, Distribution.bind_expectation]
      simp_rw [Distribution.map_expectation]
      simp only [transitionRow, vector_last_snoc]
      rw [ih (fun state => ∑ terminal,
        transition.prob state terminal * observable terminal)]
      simp only [kernelIterate_succ, comp, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro terminal _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro state _
      ring

/-- The terminal marginal of the fixed-event path law is exactly the row of
the iterated transition kernel. -/
theorem eventPathLaw_terminal_mass
    (transition : MarkovKernel State) (initial terminal : State) (events : ℕ) :
    (Distribution.map (eventPathLaw transition initial events)
      List.Vector.last).mass terminal =
      (kernelIterate transition events).prob initial terminal := by
  have h := eventPathLaw_terminal_expectation transition initial events
    (fun state => if state = terminal then 1 else 0)
  change (∑ path, (eventPathLaw transition initial events).mass path *
      (if terminal = path.last then 1 else 0)) = _
  simpa [eq_comm] using h

/-- Mixing fixed-event skeletons by a Poisson count recovers the exact
Poissonized real-time transition probability. -/
theorem poissonizedKernel_prob_eq_eventPathIntegral
    (transition : MarkovKernel State) (r : NNReal)
    (initial terminal : State) :
    (poissonizedKernel transition r).prob initial terminal =
      ∫ events : ℕ,
        (Distribution.map (eventPathLaw transition initial events)
          List.Vector.last).mass terminal ∂poissonMeasure r := by
  unfold poissonizedKernel
  apply integral_congr_ae
  exact ae_of_all _ fun events =>
    (eventPathLaw_terminal_mass transition initial terminal events).symm

/-- Path-skeleton representation of a bounded finite-rate generator's
real-time transition probability. -/
theorem FiniteRateGenerator.timeKernel_prob_eq_eventPathIntegral
    (rates : FiniteRateGenerator State) (Λ : ℝ) (hΛ : 0 < Λ)
    (hbound : ∀ x, rates.exitRate x ≤ Λ) (t : NNReal)
    (initial terminal : State) :
    (rates.timeKernel Λ hΛ hbound t).prob initial terminal =
      ∫ events : ℕ,
        (Distribution.map
          (eventPathLaw (rates.uniformizedKernel Λ hΛ hbound) initial events)
          List.Vector.last).mass terminal
        ∂poissonMeasure (FiniteRateGenerator.clockIntensity Λ hΛ t) :=
  poissonizedKernel_prob_eq_eventPathIntegral _ _ _ _

end Mcmc.PDMP
