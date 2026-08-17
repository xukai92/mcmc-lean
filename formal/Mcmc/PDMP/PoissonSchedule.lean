import Mcmc.PDMP.EventSimulation
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Fin.Tuple.Sort
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

/-- Region on which a particular index permutation orders the timestamp
values monotonically. -/
def monotonePermutationRegion (permutation : Equiv.Perm (Fin n)) :
    Set (Fin n → ℝ) :=
  {times | Monotone (times ∘ permutation)}

theorem measurableSet_monotonePermutationRegion
    (permutation : Equiv.Perm (Fin n)) :
    MeasurableSet (monotonePermutationRegion permutation) := by
  rw [show monotonePermutationRegion permutation =
      ⋂ i : Fin n, ⋂ j : Fin n,
        if i < j then
          {times : Fin n → ℝ | times (permutation i) ≤ times (permutation j)}
        else Set.univ by
    ext times
    simp only [monotonePermutationRegion, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · rw [monotone_iff_forall_lt]
      intro h i j
      split_ifs with hij
      · exact h hij
      · exact Set.mem_univ times
    · intro h i j hij
      rcases eq_or_lt_of_le hij with rfl | hijlt
      · exact le_rfl
      · have hij' := h i j
        rw [if_pos hijlt] at hij'
        simpa [Function.comp_apply] using hij']
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  split
  · exact measurableSet_le (measurable_pi_apply (permutation i))
      (measurable_pi_apply (permutation j))
  · exact MeasurableSet.univ

/-- Sorting the values of a finite real tuple is measurable. The proof glues
the finitely many coordinate permutations over their measurable monotonicity
regions; `Tuple.unique_monotone` proves agreement on overlaps. -/
theorem measurable_tupleSortValues (n : ℕ) :
    Measurable (fun times : Fin n → ℝ => times ∘ Tuple.sort times) := by
  let region : Equiv.Perm (Fin n) → Set (Fin n → ℝ) :=
    monotonePermutationRegion
  let permute : Equiv.Perm (Fin n) → (Fin n → ℝ) → (Fin n → ℝ) :=
    fun permutation times => times ∘ permutation
  have hregion : ∀ permutation, MeasurableSet (region permutation) :=
    measurableSet_monotonePermutationRegion
  have hpermute : ∀ permutation, Measurable (permute permutation) := by
    intro permutation
    apply measurable_pi_lambda
    intro i
    exact measurable_pi_apply (permutation i)
  have hagree : Pairwise fun first second =>
      Set.EqOn (permute first) (permute second)
        (region first ∩ region second) := by
    intro first second _ times htimes
    exact Tuple.unique_monotone htimes.1 htimes.2
  obtain ⟨ordered, hordered, hagrees⟩ :=
    exists_measurable_piecewise region hregion permute hpermute hagree
  have heq : ordered = fun times : Fin n → ℝ =>
      times ∘ Tuple.sort times := by
    funext times
    exact hagrees (Tuple.sort times)
      (show times ∈ region (Tuple.sort times) from Tuple.monotone_sort times)
  rwa [← heq]

/-- Certified measurable timestamp ordering at every finite count. -/
noncomputable def timestampOrdering (n : ℕ) : TimestampOrdering n where
  order := fun times => times ∘ Tuple.sort times
  measurable_order := measurable_tupleSortValues n
  monotone_order := Tuple.monotone_sort
  permutes := fun times => ⟨Tuple.sort times, rfl⟩

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

/-- Inter-candidate waits telescope back to the last absolute timestamp for a
nonnegative monotone timestamp vector. -/
theorem sum_orderedTimestampsToWaits
    (times : Fin (n + 1) → ℝ) (hmono : Monotone times)
    (hzero : 0 ≤ times 0) :
    ((∑ i, orderedTimestampsToWaits times i : NNReal) : ℝ) =
      times (Fin.last n) := by
  let f : ℕ → ℝ := fun k => times ⟨min k n,
    lt_of_le_of_lt (Nat.min_le_right k n) (Nat.lt_succ_self n)⟩
  let g : ℕ → ℝ := fun k =>
    if hk : k < n + 1 then
      (orderedTimestampsToWaits times ⟨k, hk⟩ : ℝ)
    else 0
  rw [NNReal.coe_sum]
  calc
    ∑ i, (orderedTimestampsToWaits times i : ℝ) = ∑ i : Fin (n + 1), g i := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp [g]
      split_ifs with h
      · rfl
      · exact (h i.isLt).elim
    _ = ∑ k ∈ Finset.range (n + 1), g k :=
      Fin.sum_univ_eq_sum_range g (n + 1)
    _ =
        ∑ k ∈ Finset.range (n + 1),
          if k = 0 then f 0 else f k - f (k - 1) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hklt : k < n + 1 := Finset.mem_range.mp hk
      have hkle : k ≤ n := Nat.lt_succ_iff.mp hklt
      have hg : g k =
          (orderedTimestampsToWaits times ⟨k, hklt⟩ : ℝ) := by
        dsimp [g]
        split_ifs
        rfl
      have hf : f k = times ⟨k, hklt⟩ := by
        simp [f, Nat.min_eq_left hkle]
      by_cases hk0 : k = 0
      · subst k
        simp [hg, orderedTimestampsToWaits, f, hzero]
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        have hprevlt : k - 1 < n + 1 :=
          lt_of_le_of_lt (Nat.sub_le k 1) hklt
        have hprevle : k - 1 ≤ n := Nat.lt_succ_iff.mp hprevlt
        have hfprev : f (k - 1) = times ⟨k - 1, hprevlt⟩ := by
          simp [f, Nat.min_eq_left hprevle]
        have hle : times ⟨k - 1, hprevlt⟩ ≤ times ⟨k, hklt⟩ := by
          apply hmono
          exact Fin.mk_le_mk.mpr (Nat.sub_le k 1)
        rw [hg]
        simp [orderedTimestampsToWaits, hk0, hf, hfprev,
          Real.toNNReal_of_nonneg (sub_nonneg.mpr hle)]
    _ = f n := (Finset.eq_sum_range_sub' f n).symm
    _ = times (Fin.last n) := by
      apply congrArg times
      apply Fin.ext
      simp

/-- Ordered timestamps contained in a horizon produce waits whose total does
not exceed that horizon. -/
theorem sum_orderedTimestampsToWaits_le
    (times : Fin n → ℝ) (hmono : Monotone times) (horizon : NNReal)
    (hinside : ∀ i, times i ∈ Set.Ioc 0 (horizon : ℝ)) :
    (∑ i, orderedTimestampsToWaits times i) ≤ horizon := by
  cases n with
  | zero => simp
  | succ n =>
      rw [← NNReal.coe_le_coe]
      rw [sum_orderedTimestampsToWaits times hmono
        (le_of_lt (hinside 0).1)]
      exact (hinside (Fin.last n)).2

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

/-- Common measurable carrier for schedules of every finite size. Coordinates
past `candidateCount` are padding and carry no semantic events. -/
abbrev CandidateScheduleSample := ℕ × (ℕ → NNReal)

/-- Embed a fixed-size wait vector into the common schedule carrier. -/
def padCandidateWaits (n : ℕ) (waits : Fin n → NNReal) :
    CandidateScheduleSample :=
  (n, fun k => if h : k < n then waits ⟨k, h⟩ else 0)

/-- Padding does not change the elapsed time represented by the active wait
coordinates. -/
theorem scheduleElapsed_padCandidateWaits (n : ℕ) (waits : Fin n → NNReal) :
    (∑ index ∈ Finset.range n, (padCandidateWaits n waits).2 index) =
      ∑ index, waits index := by
  let g : ℕ → NNReal := fun index =>
    if h : index < n then waits ⟨index, h⟩ else 0
  calc
    (∑ index ∈ Finset.range n, (padCandidateWaits n waits).2 index) =
        ∑ index ∈ Finset.range n, g index := by rfl
    _ = ∑ index : Fin n, g index :=
      (Fin.sum_univ_eq_sum_range g n).symm
    _ = ∑ index, waits index := by
      apply Finset.sum_congr rfl
      intro index _
      dsimp [g]
      split_ifs with h
      · rfl
      · exact (h index.isLt).elim

theorem measurable_padCandidateWaits (n : ℕ) :
    Measurable (padCandidateWaits n) := by
  apply measurable_const.prodMk
  apply measurable_pi_lambda
  intro k
  change Measurable (fun waits : Fin n → NNReal =>
    if h : k < n then waits ⟨k, h⟩ else 0)
  by_cases h : k < n
  · simp only [h, dite_true]
    exact measurable_pi_apply (⟨k, h⟩ : Fin n)
  · simp only [h, dite_false]
    exact measurable_const

/-- Conditional schedule law on the common carrier at a fixed count. -/
noncomputable def PositiveHorizon.fixedScheduleMeasure
    (horizon : PositiveHorizon) (ordering : TimestampOrdering n) :
    Measure CandidateScheduleSample :=
  Measure.map (padCandidateWaits n)
    (horizon.candidateWaitsMeasure ordering)

instance PositiveHorizon.fixedScheduleMeasure.instIsProbabilityMeasure
    (horizon : PositiveHorizon) (ordering : TimestampOrdering n) :
    IsProbabilityMeasure (horizon.fixedScheduleMeasure ordering) := by
  unfold PositiveHorizon.fixedScheduleMeasure
  exact Measure.isProbabilityMeasure_map
    (measurable_padCandidateWaits n).aemeasurable

/-- The singleton masses of a Poisson law sum to one. -/
theorem tsum_poisson_singletons (intensity : NNReal) :
    ∑' n : ℕ, poissonMeasure intensity {n} = 1 := by
  rw [← measure_iUnion]
  · rw [show (⋃ n : ℕ, ({n} : Set ℕ)) = Set.univ by ext; simp]
    simp
  · intro i j hij
    exact Set.disjoint_singleton.2 hij
  · exact fun i => MeasurableSet.singleton i

/-- Adjacent Poisson count weights satisfy the birth/death recurrence used by
cross-count generator cancellation. -/
theorem poissonMeasure_real_singleton_succ_flux
    (intensity : NNReal) (count : ℕ) :
    ((count + 1 : ℕ) : ℝ) * (poissonMeasure intensity).real {count + 1} =
      (intensity : ℝ) * (poissonMeasure intensity).real {count} := by
  rw [poissonMeasure_real_singleton, poissonMeasure_real_singleton]
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  field_simp

/-- Joint law of a Poisson candidate count and its conditional ordered wait
sequence. The family argument makes the measurable-sorting obligation
explicit at every count. -/
noncomputable def poissonCandidateScheduleMeasure
    (intensity : NNReal) (horizon : PositiveHorizon)
    (orderings : ∀ n, TimestampOrdering n) :
    Measure CandidateScheduleSample :=
  Measure.sum fun n : ℕ =>
    poissonMeasure intensity {n} •
      horizon.fixedScheduleMeasure (orderings n)

instance poissonCandidateScheduleMeasure.instIsProbabilityMeasure
    (intensity : NNReal) (horizon : PositiveHorizon)
    (orderings : ∀ n, TimestampOrdering n) :
    IsProbabilityMeasure
      (poissonCandidateScheduleMeasure intensity horizon orderings) := by
  constructor
  rw [poissonCandidateScheduleMeasure, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  exact tsum_poisson_singletons intensity

/-- The count marginal of the joint schedule law is exactly the supplied
Poisson law. -/
theorem poissonCandidateScheduleMeasure_map_fst
    (intensity : NNReal) (horizon : PositiveHorizon)
    (orderings : ∀ n, TimestampOrdering n) :
    Measure.map Prod.fst
        (poissonCandidateScheduleMeasure intensity horizon orderings) =
      poissonMeasure intensity := by
  rw [Measure.ext_iff_singleton]
  intro k
  rw [Measure.map_apply measurable_fst (MeasurableSet.singleton k),
    poissonCandidateScheduleMeasure,
    Measure.sum_apply _ (MeasurableSet.singleton k |>.preimage measurable_fst)]
  rw [tsum_eq_single k]
  · unfold PositiveHorizon.fixedScheduleMeasure
    rw [Measure.smul_apply, Measure.map_apply (measurable_padCandidateWaits k)
      (MeasurableSet.singleton k |>.preimage measurable_fst)]
    have hpre : padCandidateWaits k ⁻¹' (Prod.fst ⁻¹' {k}) = Set.univ := by
      ext waits
      simp [padCandidateWaits]
    rw [hpre, measure_univ]
    simp
  · intro n hne
    unfold PositiveHorizon.fixedScheduleMeasure
    rw [Measure.smul_apply, Measure.map_apply (measurable_padCandidateWaits n)
      (MeasurableSet.singleton k |>.preimage measurable_fst)]
    have hpre : padCandidateWaits n ⁻¹' (Prod.fst ⁻¹' {k}) = ∅ := by
      ext waits
      simp [padCandidateWaits, hne]
    rw [hpre, measure_empty]
    simp

/-- Unconditional homogeneous-clock schedule law using the certified
all-count tuple ordering. -/
noncomputable def poissonCandidateSchedule
    (intensity : NNReal) (horizon : PositiveHorizon) :
    Measure CandidateScheduleSample :=
  poissonCandidateScheduleMeasure intensity horizon timestampOrdering

instance poissonCandidateSchedule.instIsProbabilityMeasure
    (intensity : NNReal) (horizon : PositiveHorizon) :
    IsProbabilityMeasure (poissonCandidateSchedule intensity horizon) := by
  unfold poissonCandidateSchedule
  infer_instance

/-- The concrete unconditional schedule retains the exact Poisson count
marginal. -/
theorem poissonCandidateSchedule_map_fst
    (intensity : NNReal) (horizon : PositiveHorizon) :
    Measure.map Prod.fst (poissonCandidateSchedule intensity horizon) =
      poissonMeasure intensity :=
  poissonCandidateScheduleMeasure_map_fst intensity horizon timestampOrdering

end Mcmc.PDMP
