import Mcmc.Kernel.HistoryAdaptive

/-!
# A never-freezing continuous history-adaptive refresh client

This example selects a real anchor from the complete observed history.  At
stage `n`, the next law is a mixture of a point mass at that anchor with weight
`1/(n+2)` and an independent target refresh with the remaining weight.  The
selector and transition therefore change forever, while the actual marginal
converges setwise because the nonzero anchor error vanishes uniformly.
-/

namespace Mcmc.Examples.IndefiniteContinuousRefresh

open MeasureTheory ProbabilityTheory
open Mcmc.Kernel
open scoped ENNReal

/-- Vanishing weight of the history-selected point mass. -/
noncomputable def anchorWeight (n : ℕ) : NNReal :=
  1 / (n + 2 : NNReal)

theorem anchorWeight_le_one (n : ℕ) : anchorWeight n ≤ 1 := by
  unfold anchorWeight
  apply (div_le_one (by positivity : (0 : NNReal) < (n + 2 : NNReal))).2
  calc
    (1 : NNReal) ≤ 2 := by norm_num
    _ ≤ n + 2 := by
      simpa only [zero_add, add_zero, add_comm] using
        add_le_add_right (show (0 : NNReal) ≤ n by positivity) 2

/-- Complete-history empirical mean used as the moving anchor. -/
noncomputable def historyAnchor (n : ℕ)
    (history : (i : Finset.Iic n) → ℝ) : ℝ :=
  (∑ i, history i) / (n + 1)

theorem measurable_historyAnchor (n : ℕ) : Measurable (historyAnchor n) := by
  unfold historyAnchor
  fun_prop

abbrev Parameter := ℕ × ℝ

/-- A jointly measurable family mixing the selected anchor with an independent
draw from `target`. The current state is present only to fit the adaptive
family interface; the complete history controls the selected parameter. -/
noncomputable def familyKernel (target : Measure ℝ)
    [IsProbabilityMeasure target] : Kernel (ℝ × Parameter) ℝ where
  toFun input :=
    (anchorWeight input.2.1 : ENNReal) • Measure.dirac input.2.2 +
      ((1 - anchorWeight input.2.1 : NNReal) : ENNReal) • target
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun event hevent => ?_
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ hevent]
    fun_prop

instance familyKernel.instIsMarkovKernel (target : Measure ℝ)
    [IsProbabilityMeasure target] : IsMarkovKernel (familyKernel target) where
  isProbabilityMeasure input := by
    constructor
    change (((anchorWeight input.2.1 : ENNReal) •
      Measure.dirac input.2.2 +
      ((1 - anchorWeight input.2.1 : NNReal) : ENNReal) • target)
        Set.univ) = 1
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ,
      smul_eq_mul, mul_one]
    rw [← ENNReal.coe_add, add_tsub_cancel_of_le
      (anchorWeight_le_one input.2.1)]
    rfl

/-- Every family row is uniformly within its nonzero anchor weight of the
target, independently of the selected anchor. -/
theorem familyKernel_eventwiseWithin (target : Measure ℝ)
    [IsProbabilityMeasure target] (input : ℝ × Parameter) :
    EventwiseWithin (familyKernel target input) target
      (anchorWeight input.2.1 : ENNReal) := by
  intro event hevent
  let w := anchorWeight input.2.1
  let anchorMass := Measure.dirac input.2.2 event
  let targetMass := target event
  have hw : w ≤ 1 := anchorWeight_le_one input.2.1
  have hanchor : anchorMass ≤ 1 := by
    calc
      anchorMass ≤ Measure.dirac input.2.2 Set.univ :=
        measure_mono (Set.subset_univ event)
      _ = 1 := measure_univ
  have htarget : targetMass ≤ 1 := by
    calc
      targetMass ≤ target Set.univ := measure_mono (Set.subset_univ event)
      _ = 1 := measure_univ
  change ((w : ENNReal) * anchorMass +
      ((1 - w : NNReal) : ENNReal) * targetMass ≤
        targetMass + (w : ENNReal)) ∧
    (targetMass ≤ (w : ENNReal) * anchorMass +
      ((1 - w : NNReal) : ENNReal) * targetMass + (w : ENNReal))
  constructor
  · calc
      (w : ENNReal) * anchorMass +
          ((1 - w : NNReal) : ENNReal) * targetMass ≤
        (w : ENNReal) * 1 + 1 * targetMass := by
          gcongr
          exact_mod_cast (show (1 - w : NNReal) ≤ 1 from tsub_le_self)
      _ = targetMass + (w : ENNReal) := by ac_rfl
  · calc
      targetMass = (w : ENNReal) * targetMass +
          ((1 - w : NNReal) : ENNReal) * targetMass := by
        rw [← add_mul, ← ENNReal.coe_add,
          add_tsub_cancel_of_le hw, ENNReal.coe_one, one_mul]
      _ ≤ (w : ENNReal) * 1 +
          ((1 - w : NNReal) : ENNReal) * targetMass := by gcongr
      _ = ((1 - w : NNReal) : ENNReal) * targetMass + (w : ENNReal) := by
        ac_rfl
      _ ≤ ((w : ENNReal) * anchorMass +
          ((1 - w : NNReal) : ENNReal) * targetMass) + (w : ENNReal) := by
        gcongr
        exact le_add_left le_rfl

/-- The selector reads the full history and changes its time component at
every stage. -/
noncomputable def adaptive (target : Measure ℝ)
    [IsProbabilityMeasure target] : HistoryAdaptiveFamily ℝ Parameter where
  family := familyKernel target
  select n history := (n, historyAnchor n history)
  measurable_select n := measurable_const.prodMk (measurable_historyAnchor n)

theorem adaptive_next_eventwiseWithin (target : Measure ℝ)
    [IsProbabilityMeasure target] (n : ℕ)
    (history : (i : Finset.Iic n) → ℝ) :
    EventwiseWithin ((adaptive target).next n history) target
      (anchorWeight n : ENNReal) := by
  simpa [adaptive, HistoryAdaptiveFamily.next,
    ProbabilityTheory.Kernel.comap_apply] using
    familyKernel_eventwiseWithin target
      (terminalHistory n history, (n, historyAnchor n history))

theorem anchorWeight_tendsto_zero :
    Filter.Tendsto (fun n ↦ (anchorWeight n : ENNReal))
      Filter.atTop (nhds 0) := by
  have hshift : Filter.Tendsto (fun n : ℕ ↦ n + 2)
      Filter.atTop Filter.atTop := Filter.tendsto_add_atTop_nat 2
  apply (ENNReal.tendsto_inv_nat_nhds_zero.comp hshift).congr'
  filter_upwards with n
  simp [anchorWeight]

/-- The actual continuously valued, complete-history-adaptive marginals
converge setwise despite a nonzero finite-time anchor bias and no freezing. -/
theorem adaptive_stateKernel_apply_tendsto (target : Measure ℝ)
    [IsProbabilityMeasure target] (initial : ℝ)
    {event : Set ℝ} (hevent : MeasurableSet event) :
    Filter.Tendsto
      (fun n ↦ (adaptive target).stateKernel (n + 1) initial event)
      Filter.atTop (nhds (target event)) := by
  exact (adaptive target).stateKernel_succ_apply_tendsto_of_next_eventwise
    initial target (fun n ↦ (anchorWeight n : ENNReal))
    anchorWeight_tendsto_zero
    (fun n history ↦ adaptive_next_eventwiseWithin target n history) hevent

/-- The selected parameter never becomes constant. -/
theorem adaptive_not_freezes (target : Measure ℝ)
    [IsProbabilityMeasure target] (burnIn : ℕ) (parameter : Parameter) :
    ¬ (adaptive target).FreezesAfter burnIn parameter := by
  intro hfreeze
  let n := burnIn + parameter.1 + 1
  let history : (i : Finset.Iic n) → ℝ := fun _ ↦ 0
  have hselected := hfreeze n (by omega : burnIn ≤ n) history
  have htime := congrArg Prod.fst hselected
  simp [adaptive, n] at htime
  omega

end Mcmc.Examples.IndefiniteContinuousRefresh
