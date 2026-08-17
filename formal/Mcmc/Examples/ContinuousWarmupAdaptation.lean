import Mcmc.Kernel.HistoryAdaptive

/-!
# Continuous history-dependent warmup

This client selects a positive tuning parameter from the empirical second
moment of the complete real-valued trajectory during a finite warmup, then
freezes at a declared production value. The kernel family is abstract so the
result applies to any jointly measurable continuous sampler family; the final
section must separately supply the invariant-target and uniform-minorization
certificates needed for setwise convergence.
-/

namespace Mcmc.Examples.ContinuousWarmupAdaptation

open MeasureTheory ProbabilityTheory
open Mcmc.Kernel

/-- Empirical second moment of every state observed through time `n`. -/
noncomputable def empiricalSecondMoment (n : ℕ)
    (history : (i : Finset.Iic n) → ℝ) : ℝ :=
  (∑ i, (history i) ^ 2) / (n + 1)

theorem measurable_empiricalSecondMoment (n : ℕ) :
    Measurable (empiricalSecondMoment n) := by
  unfold empiricalSecondMoment
  fun_prop

/-- A production-shaped warmup rule: adapt to `1 +` the complete-history
second moment before `burnIn`, then use `frozen` forever. -/
noncomputable def selectScale (burnIn : ℕ) (frozen : ℝ) (n : ℕ)
    (history : (i : Finset.Iic n) → ℝ) : ℝ :=
  if n < burnIn then 1 + empiricalSecondMoment n history else frozen

theorem measurable_selectScale (burnIn : ℕ) (frozen : ℝ) (n : ℕ) :
    Measurable (selectScale burnIn frozen n) := by
  unfold selectScale
  split
  · exact measurable_const.add (measurable_empiricalSecondMoment n)
  · exact measurable_const

/-- Attach the warmup selector to any jointly measurable Markov family whose
parameter is a real tuning value. -/
noncomputable def adaptive (burnIn : ℕ) (frozen : ℝ)
    (family : Kernel (ℝ × ℝ) ℝ) [IsMarkovKernel family] :
    HistoryAdaptiveFamily ℝ ℝ where
  family := family
  select := selectScale burnIn frozen
  measurable_select := measurable_selectScale burnIn frozen

theorem adaptive_freezesAfter (burnIn : ℕ) (frozen : ℝ)
    (family : Kernel (ℝ × ℝ) ℝ) [IsMarkovKernel family] :
    (adaptive burnIn frozen family).FreezesAfter burnIn frozen := by
  intro n hn history
  simp [adaptive, selectScale, Nat.not_lt_of_ge hn]

/-- The rule really reads the continuous trajectory during warmup: at the
first stage, the all-zero and all-one histories select distinct scales. -/
theorem selectScale_zero_history_sensitive (frozen : ℝ) :
    selectScale 1 frozen 0 (fun _ => 0) = 1 ∧
      selectScale 1 frozen 0 (fun _ => 1) = 2 := by
  norm_num [selectScale, empiricalSecondMoment]

/-- Finite continuous warmup automatically yields the general
proxy/containment certificate once the frozen sampler section supplies a
Doeblin minorization and preserves its target. -/
noncomputable def proxyCertificate
    (burnIn : ℕ) (frozen : ℝ)
    (family : Kernel (ℝ × ℝ) ℝ) [IsMarkovKernel family]
    (target : Measure ℝ) [IsProbabilityMeasure target]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1) (hεpos : 0 < ε.1)
    (hminor : UniformlyMinorizes (fixedParameterSection family frozen)
      ε.1 target)
    (hinvariant : (fixedParameterSection family frozen).Invariant target)
    (initial : ℝ) :
    ProxyConvergenceCertificate
      (fun steps => (adaptive burnIn frozen family).stateKernel
        (burnIn + steps) initial) target :=
  (adaptive burnIn frozen family).proxyCertificate_of_freezesAfter burnIn
    frozen (adaptive_freezesAfter burnIn frozen family) target ε hε hεpos
    hminor hinvariant initial

/-- The actual post-warmup marginals converge setwise to the frozen sampler's
target. No convergence claim is made for a frozen section lacking the stated
minorization certificate. -/
theorem stateKernel_apply_tendsto
    (burnIn : ℕ) (frozen : ℝ)
    (family : Kernel (ℝ × ℝ) ℝ) [IsMarkovKernel family]
    (target : Measure ℝ) [IsProbabilityMeasure target]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1) (hεpos : 0 < ε.1)
    (hminor : UniformlyMinorizes (fixedParameterSection family frozen)
      ε.1 target)
    (hinvariant : (fixedParameterSection family frozen).Invariant target)
    (initial : ℝ) {event : Set ℝ} (hevent : MeasurableSet event) :
    Filter.Tendsto
      (fun steps => (adaptive burnIn frozen family).stateKernel
        (burnIn + steps) initial event)
      Filter.atTop (nhds (target event)) :=
  (proxyCertificate burnIn frozen family target ε hε hεpos hminor hinvariant
    initial).tendsto_apply hevent

end Mcmc.Examples.ContinuousWarmupAdaptation
