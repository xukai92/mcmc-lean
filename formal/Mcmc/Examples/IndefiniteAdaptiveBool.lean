import Mcmc.Kernel.HistoryAdaptive
import Mcmc.Finite.MeasureKernel

/-!
# A concrete indefinitely state-adaptive general-state chain

This example instantiates the history-adaptive path semantics with a parameter
chosen from the current state at every iteration. The chosen Bernoulli bias
changes forever but shrinks as `1/(4(n+1))`. After selection, the resulting
time-`n` state kernel has uniform `Bool` invariant and uniformly minorizes it
with coefficient `1/2`; the nonhomogeneous Doeblin theorem therefore gives
setwise convergence of the actual adaptive marginal.
-/

namespace Mcmc.Examples.IndefiniteAdaptiveBool

open MeasureTheory ProbabilityTheory
open Mcmc.Finite Mcmc.Finite.MarkovKernel Mcmc.Kernel

/-- Uniform target on the two-point state space. -/
noncomputable def target : Distribution Bool where
  mass _ := 1 / 2
  nonneg _ := by norm_num
  sum_mass := by norm_num [Fintype.sum_bool]

/-- Magnitude of the forever-changing state-selected bias. -/
noncomputable def bias (n : ℕ) : ℝ := 1 / (4 * (n + 1))

theorem bias_pos (n : ℕ) : 0 < bias n := by
  unfold bias
  positivity

theorem bias_le_quarter (n : ℕ) : bias n ≤ 1 / 4 := by
  unfold bias
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (n + 1))
    (by norm_num : (0 : ℝ) < 4)]
  norm_num

/-- The parameter chosen from `false` biases the next draw downward; the
parameter chosen from `true` biases it upward. -/
noncomputable def trueProbability (n : ℕ) (selected : Bool) : ℝ :=
  1 / 2 + if selected then bias n else -bias n

/-- Concrete state kernel after substituting the state-dependent parameter. -/
noncomputable def transition (n : ℕ) : MarkovKernel Bool where
  prob selected next :=
    if next then trueProbability n selected
    else 1 - trueProbability n selected
  nonneg selected next := by
    cases selected <;> cases next <;>
      simp [trueProbability] <;>
      have hpos := bias_pos n <;>
      have hle := bias_le_quarter n <;> linarith
  sum_prob selected := by
    cases selected <;>
      simp [trueProbability]

theorem transition_stationary (n : ℕ) :
    (transition n).Stationary target := by
  intro next
  cases next <;>
    simp [transition, target, trueProbability] <;> ring

theorem transition_reversible (n : ℕ) :
    (transition n).Reversible target := by
  intro left right
  cases left <;> cases right <;>
    simp [transition, target, trueProbability] <;> ring

theorem transition_invariant (n : ℕ) :
    (transition n).toMeasureKernel.Invariant target.toMeasure :=
  (transition_reversible n).invariantMeasure

theorem transition_prob_ge_quarter (n : ℕ) (current next : Bool) :
    1 / 4 ≤ (transition n).prob current next := by
  cases current <;> cases next <;>
    simp [transition, trueProbability] <;>
    have hpos := bias_pos n <;>
    have hle := bias_le_quarter n <;> linarith

/-- Every selected row retains at least half of the uniform target as a
Doeblin refresh component. -/
theorem transition_minorizes (n : ℕ) :
    UniformlyMinorizes (transition n).toMeasureKernel
      (1 / 2 : ENNReal) target.toMeasure := by
  classical
  intro current event hevent
  by_cases hfalse : false ∈ event
  · by_cases htrue : true ∈ event
    · have huniv : event = Set.univ := by
        ext value
        cases value <;> simp [hfalse, htrue]
      subst event
      rw [measure_univ, measure_univ]
      norm_num
    · have hsingleton : event = {false} := by
        ext value
        cases value <;> simp [hfalse, htrue]
      subst event
      rw [Distribution.toMeasure_apply_singleton,
        MarkovKernel.toMeasureKernel_apply_singleton]
      norm_num [target]
      calc
        2⁻¹ * ENNReal.ofReal (1 / 2) = ENNReal.ofReal (1 / 4) := by
          rw [show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num,
            ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2),
            show (2 : ℝ)⁻¹ = 1 / 2 by norm_num,
            ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          norm_num
        _ ≤ _ := ENNReal.ofReal_le_ofReal (transition_prob_ge_quarter n current false)
  · by_cases htrue : true ∈ event
    · have hsingleton : event = {true} := by
        ext value
        cases value <;> simp [hfalse, htrue]
      subst event
      rw [Distribution.toMeasure_apply_singleton,
        MarkovKernel.toMeasureKernel_apply_singleton]
      norm_num [target]
      calc
        2⁻¹ * ENNReal.ofReal (1 / 2) = ENNReal.ofReal (1 / 4) := by
          rw [show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num,
            ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2),
            show (2 : ℝ)⁻¹ = 1 / 2 by norm_num,
            ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          norm_num
        _ ≤ _ := ENNReal.ofReal_le_ofReal (transition_prob_ge_quarter n current true)
    · have hempty : event = ∅ := by
        ext value
        cases value <;> simp [hfalse, htrue]
      subst event
      simp

/-! The family parameter records the time and selected current state. -/

abbrev Parameter := ℕ × Bool

noncomputable def familyKernel : Kernel (Bool × Parameter) Bool :=
  Kernel.ofFunOfCountable fun input =>
    ((transition input.2.1).rowPMF input.2.2).toMeasure

instance familyKernel.instIsMarkovKernel : IsMarkovKernel familyKernel where
  isProbabilityMeasure input :=
    PMF.toMeasure.isProbabilityMeasure ((transition input.2.1).rowPMF input.2.2)

/-- At every time, select a parameter from the actual terminal state. This is
state-dependent and never freezes. -/
noncomputable def adaptive : HistoryAdaptiveFamily Bool Parameter where
  family := familyKernel
  select n history := (n, terminalHistory n history)
  measurable_select n := measurable_of_countable _

/-- Substituting the selected parameter gives the explicit changing state
kernel above. -/
theorem adaptive_next (n : ℕ) :
    adaptive.next n = homogeneousNext (transition n).toMeasureKernel n := by
  ext history event hevent
  rfl

/-- The common Doeblin coefficient, packaged with its unit-interval bounds. -/
noncomputable def epsilon : Set.Icc (0 : NNReal) 1 :=
  ⟨1 / 2, by constructor <;> norm_num⟩

/-- Despite changing its state-selected parameter forever, the actual adaptive
marginal converges setwise to the uniform target from either initial state. -/
theorem adaptive_stateKernel_apply_tendsto
    (initial : Bool) {event : Set Bool} (hevent : MeasurableSet event) :
    Filter.Tendsto (fun n ↦ adaptive.stateKernel n initial event)
      Filter.atTop (nhds (target.toMeasure event)) := by
  apply adaptive.stateKernel_apply_tendsto_of_predetermined_doeblin
    (fun n ↦ (transition n).toMeasureKernel) adaptive_next target.toMeasure epsilon
  · norm_num [epsilon]
  · norm_num [epsilon]
  · intro n
    simpa [epsilon] using transition_minorizes n
  · exact transition_invariant
  · exact hevent

/-- The selector is genuinely indefinite: no burn-in time and fixed parameter
can describe all its later choices. -/
theorem adaptive_not_freezes (burnIn : ℕ) (parameter : Parameter) :
    ¬ adaptive.FreezesAfter burnIn parameter := by
  intro hfreeze
  let n := burnIn + parameter.1 + 1
  let history : {k // k ∈ Finset.Iic n} → Bool := fun _ ↦ false
  have hselected := hfreeze n (by omega : burnIn ≤ n) history
  have htime := congrArg Prod.fst hselected
  simp [adaptive, n] at htime
  omega

end Mcmc.Examples.IndefiniteAdaptiveBool
