import Mcmc.PDMP.EventSimulation
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

/-!
# Conditional candidate times for a homogeneous Poisson clock

Conditional on exactly `n` clock candidates in a positive horizon, their
unordered timestamps are iid uniform on that horizon. This module constructs
that continuous probability law. Sorting these timestamps and coupling the
conditional laws to the Poisson count is the next path-law layer.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace Mcmc.PDMP

/-- A finite horizon with strictly positive duration. -/
structure PositiveHorizon where
  duration : NNReal
  positive : 0 < duration

/-- Continuous uniform probability measure on `(0, horizon]`. -/
noncomputable def PositiveHorizon.uniformTimeMeasure
    (horizon : PositiveHorizon) : Measure ℝ :=
  (ENNReal.ofReal (horizon.duration : ℝ))⁻¹ •
    volume.restrict (Set.Ioc 0 (horizon.duration : ℝ))

instance PositiveHorizon.uniformTimeMeasure.instIsProbabilityMeasure
    (horizon : PositiveHorizon) :
    IsProbabilityMeasure horizon.uniformTimeMeasure := by
  constructor
  rw [PositiveHorizon.uniformTimeMeasure, Measure.smul_apply,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Ioc]
  simp only [sub_zero, smul_eq_mul]
  exact ENNReal.inv_mul_cancel
    (ne_of_gt (ENNReal.ofReal_pos.2 (by exact_mod_cast horizon.positive)))
    ENNReal.ofReal_ne_top

/-- The same uniform timestamp law represented directly in nonnegative time. -/
noncomputable def PositiveHorizon.uniformNNRealTimeMeasure
    (horizon : PositiveHorizon) : Measure NNReal :=
  Measure.map Real.toNNReal horizon.uniformTimeMeasure

instance PositiveHorizon.uniformNNRealTimeMeasure.instIsProbabilityMeasure
    (horizon : PositiveHorizon) :
    IsProbabilityMeasure horizon.uniformNNRealTimeMeasure := by
  unfold PositiveHorizon.uniformNNRealTimeMeasure
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- Iid unordered candidate timestamps conditional on a fixed candidate
count. -/
noncomputable def PositiveHorizon.candidateTimesMeasure
    (horizon : PositiveHorizon) (candidateCount : ℕ) :
    Measure (Fin candidateCount → ℝ) :=
  Measure.pi fun _ => horizon.uniformTimeMeasure

instance PositiveHorizon.candidateTimesMeasure.instIsProbabilityMeasure
    (horizon : PositiveHorizon) (candidateCount : ℕ) :
    IsProbabilityMeasure (horizon.candidateTimesMeasure candidateCount) := by
  unfold PositiveHorizon.candidateTimesMeasure
  infer_instance

/-- A certified measurable ordering of a fixed-size timestamp vector. The
permutation field ensures no candidate is added or lost. -/
structure TimestampOrdering (n : ℕ) where
  order : (Fin n → ℝ) → (Fin n → ℝ)
  measurable_order : Measurable order
  monotone_order : ∀ times, Monotone (order times)
  permutes : ∀ times, ∃ permutation : Equiv.Perm (Fin n),
    order times = times ∘ permutation

/-- Conditional law of ordered candidate timestamps obtained by pushing iid
uniform times through a certified measurable ordering. -/
noncomputable def PositiveHorizon.orderedCandidateTimesMeasure
    (horizon : PositiveHorizon) (ordering : TimestampOrdering n) :
    Measure (Fin n → ℝ) :=
  Measure.map ordering.order (horizon.candidateTimesMeasure n)

instance PositiveHorizon.orderedCandidateTimesMeasure.instIsProbabilityMeasure
    (horizon : PositiveHorizon) (ordering : TimestampOrdering n) :
    IsProbabilityMeasure
      (horizon.orderedCandidateTimesMeasure ordering) := by
  unfold PositiveHorizon.orderedCandidateTimesMeasure
  exact Measure.isProbabilityMeasure_map ordering.measurable_order.aemeasurable

/-- Sorting network for two timestamps. -/
def orderTwoTimestamps (times : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then min (times 0) (times 1)
    else max (times 0) (times 1)

/-- The two-input `min/max` sorting network is a certified measurable
timestamp ordering. -/
noncomputable def timestampOrderingTwo : TimestampOrdering 2 where
  order := orderTwoTimestamps
  measurable_order := by
    apply measurable_pi_lambda
    intro i
    unfold orderTwoTimestamps
    split_ifs
    · exact (measurable_pi_apply 0).min (measurable_pi_apply 1)
    · exact (measurable_pi_apply 0).max (measurable_pi_apply 1)
  monotone_order := by
    intro times i j hij
    fin_cases i <;> fin_cases j
    · exact le_rfl
    · simp [orderTwoTimestamps]
    · simp at hij
    · exact le_rfl
  permutes := by
    intro times
    by_cases h : times 0 ≤ times 1
    · refine ⟨Equiv.refl _, ?_⟩
      funext i
      fin_cases i <;> simp [orderTwoTimestamps, h]
    · refine ⟨Equiv.swap 0 1, ?_⟩
      funext i
      fin_cases i <;> simp [orderTwoTimestamps, le_of_not_ge h]

/-- Convert ordered absolute timestamps to inter-candidate waits. The first
wait is measured from time zero. `toNNReal` makes this a total measurable map;
on timestamps in `(0,T]` with monotone order it agrees with ordinary
nonnegative subtraction. -/
def orderedTimestampsToWaits (times : Fin n → ℝ) : Fin n → NNReal :=
  fun i => if _hzero : i.val = 0 then Real.toNNReal (times i)
    else
      let previous : Fin n := ⟨i.val - 1,
        lt_of_le_of_lt (Nat.sub_le i.val 1) i.isLt⟩
      Real.toNNReal (times i - times previous)

theorem measurable_orderedTimestampsToWaits (n : ℕ) :
    Measurable (orderedTimestampsToWaits (n := n)) := by
  apply measurable_pi_lambda
  intro i
  by_cases hzero : i.val = 0
  · simp only [orderedTimestampsToWaits, dif_pos hzero]
    fun_prop
  · simp only [orderedTimestampsToWaits, dif_neg hzero]
    fun_prop

/-- Conditional law of inter-candidate waits induced by a certified timestamp
ordering. -/
noncomputable def PositiveHorizon.candidateWaitsMeasure
    (horizon : PositiveHorizon) (ordering : TimestampOrdering n) :
    Measure (Fin n → NNReal) :=
  Measure.map orderedTimestampsToWaits
    (horizon.orderedCandidateTimesMeasure ordering)

instance PositiveHorizon.candidateWaitsMeasure.instIsProbabilityMeasure
    (horizon : PositiveHorizon) (ordering : TimestampOrdering n) :
    IsProbabilityMeasure (horizon.candidateWaitsMeasure ordering) := by
  unfold PositiveHorizon.candidateWaitsMeasure
  exact Measure.isProbabilityMeasure_map
    (measurable_orderedTimestampsToWaits n).aemeasurable

end Mcmc.PDMP
