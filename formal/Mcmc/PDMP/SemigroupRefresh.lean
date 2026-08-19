import Mcmc.PDMP.ScheduledExecutionKernel
import Mcmc.Kernel.GeneralConvergence
import Mcmc.Kernel.LocalMinorizationCoupling
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Random refresh schedules for jointly timed Markov transitions

This module interleaves a jointly measurable time-indexed Markov transition
with an independent refresh kernel.  A padded schedule supplies chronological
waiting times; after every scheduled wait the refresh fires, and the executor
then runs the timed transition through the residual horizon.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory

namespace Mcmc.PDMP

variable {State : Type*} [MeasurableSpace State]

/-- Append two absolute timestamp vectors, translating the second vector to
the adjacent interval. -/
def shiftAppendTimestamps (firstHorizon : NNReal)
    (first : Fin firstCount → ℝ) (second : Fin secondCount → ℝ) :
    Fin (firstCount + secondCount) → ℝ :=
  Fin.append first (fun i => (firstHorizon : ℝ) + second i)

theorem measurable_shiftAppendTimestamps (firstHorizon : NNReal)
    (firstCount secondCount : ℕ) :
    Measurable (fun pair : (Fin firstCount → ℝ) × (Fin secondCount → ℝ) =>
      shiftAppendTimestamps firstHorizon pair.1 pair.2) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.addCases (motive := fun i =>
    Measurable (fun pair : (Fin firstCount → ℝ) ×
      (Fin secondCount → ℝ) =>
      shiftAppendTimestamps firstHorizon pair.1 pair.2 i)) ?_ ?_ i
  · intro left
    simp only [shiftAppendTimestamps, Fin.append_left]
    fun_prop
  · intro right
    simp only [shiftAppendTimestamps, Fin.append_right]
    fun_prop

/-- Appending monotone timestamp blocks in adjacent intervals remains
monotone when the first block ends by the boundary and the second starts
nonnegatively. -/
theorem monotone_shiftAppendTimestamps
    (firstHorizon : NNReal) (first : Fin firstCount → ℝ)
    (second : Fin secondCount → ℝ)
    (hfirstMono : Monotone first) (hsecondMono : Monotone second)
    (hfirstLe : ∀ i, first i ≤ (firstHorizon : ℝ))
    (hsecondNonneg : ∀ i, 0 ≤ second i) :
    Monotone (shiftAppendTimestamps firstHorizon first second) := by
  intro i j hij
  by_cases hi : i.val < firstCount
  · let firstI : Fin firstCount := ⟨i.val, hi⟩
    have hiEq : i = Fin.castAdd secondCount firstI := by
      apply Fin.ext
      rfl
    by_cases hj : j.val < firstCount
    · let firstJ : Fin firstCount := ⟨j.val, hj⟩
      have hjEq : j = Fin.castAdd secondCount firstJ := by
        apply Fin.ext
        rfl
      rw [hiEq, hjEq, shiftAppendTimestamps, Fin.append_left,
        Fin.append_left]
      exact hfirstMono (Fin.mk_le_mk.mpr hij)
    · have hjOffset : j.val - firstCount < secondCount := by omega
      let secondJ : Fin secondCount := ⟨j.val - firstCount, hjOffset⟩
      have hjEq : j = Fin.natAdd firstCount secondJ := by
        apply Fin.ext
        simp [secondJ]
        omega
      rw [hiEq, hjEq, shiftAppendTimestamps, Fin.append_left,
        Fin.append_right]
      exact (hfirstLe firstI).trans
        (le_add_of_nonneg_right (hsecondNonneg secondJ))
  · have hiOffset : i.val - firstCount < secondCount := by omega
    have hjOffset : j.val - firstCount < secondCount := by omega
    let secondI : Fin secondCount := ⟨i.val - firstCount, hiOffset⟩
    let secondJ : Fin secondCount := ⟨j.val - firstCount, hjOffset⟩
    have hiEq : i = Fin.natAdd firstCount secondI := by
      apply Fin.ext
      simp [secondI]
      omega
    have hjEq : j = Fin.natAdd firstCount secondJ := by
      apply Fin.ext
      simp [secondJ]
      omega
    rw [hiEq, hjEq, shiftAppendTimestamps, Fin.append_right,
      Fin.append_right]
    have hIJ : secondI ≤ secondJ := Fin.mk_le_mk.mpr (by omega)
    simpa [add_comm] using
      (add_le_add_left (hsecondMono hIJ) (firstHorizon : ℝ))

/-- Block-diagonal permutation that sorts each side of an appended timestamp
vector without mixing the two adjacent intervals. -/
noncomputable def shiftAppendSortPermutation
    (first : Fin firstCount → ℝ) (second : Fin secondCount → ℝ) :
    Equiv.Perm (Fin (firstCount + secondCount)) :=
  finSumFinEquiv.symm |>.trans
    ((Tuple.sort first).sumCongr (Tuple.sort second) |>.trans finSumFinEquiv)

theorem shiftAppend_comp_shiftAppendSortPermutation
    (firstHorizon : NNReal) (first : Fin firstCount → ℝ)
    (second : Fin secondCount → ℝ) :
    shiftAppendTimestamps firstHorizon first second ∘
        shiftAppendSortPermutation first second =
      shiftAppendTimestamps firstHorizon
        (first ∘ Tuple.sort first) (second ∘ Tuple.sort second) := by
  funext i
  refine Fin.addCases (motive := fun i =>
    (shiftAppendTimestamps firstHorizon first second ∘
        shiftAppendSortPermutation first second) i =
      shiftAppendTimestamps firstHorizon
        (first ∘ Tuple.sort first) (second ∘ Tuple.sort second) i) ?_ ?_ i
  · intro left
    simp [shiftAppendSortPermutation, shiftAppendTimestamps,
      Function.comp_apply]
  · intro right
    simp [shiftAppendSortPermutation, shiftAppendTimestamps,
      Function.comp_apply]

/-- Sorting a concatenation of timestamp blocks from adjacent intervals is
the same as sorting each block separately and then appending them. -/
theorem tupleSortValues_shiftAppend
    (firstHorizon : NNReal) (first : Fin firstCount → ℝ)
    (second : Fin secondCount → ℝ)
    (hfirstLe : ∀ i, first i ≤ (firstHorizon : ℝ))
    (hsecondNonneg : ∀ i, 0 ≤ second i) :
    shiftAppendTimestamps firstHorizon first second ∘
        Tuple.sort (shiftAppendTimestamps firstHorizon first second) =
      shiftAppendTimestamps firstHorizon
        (first ∘ Tuple.sort first) (second ∘ Tuple.sort second) := by
  have hcandMono := monotone_shiftAppendTimestamps firstHorizon
    (first ∘ Tuple.sort first) (second ∘ Tuple.sort second)
    (Tuple.monotone_sort first) (Tuple.monotone_sort second)
    (fun i => hfirstLe (Tuple.sort first i))
    (fun i => hsecondNonneg (Tuple.sort second i))
  rw [← shiftAppend_comp_shiftAppendSortPermutation] at hcandMono
  have hunique := Tuple.unique_monotone hcandMono
    (Tuple.monotone_sort
      (shiftAppendTimestamps firstHorizon first second))
  rw [shiftAppend_comp_shiftAppendSortPermutation] at hunique
  exact hunique.symm

/-- Wait conversion on coordinates in the first timestamp block is unchanged
by appending an adjacent block. -/
theorem orderedTimestampsToWaits_shiftAppend_castAdd
    (firstHorizon : NNReal) (first : Fin firstCount → ℝ)
    (second : Fin secondCount → ℝ) (i : Fin firstCount) :
    orderedTimestampsToWaits
        (shiftAppendTimestamps firstHorizon first second)
        (Fin.castAdd secondCount i) =
      orderedTimestampsToWaits first i := by
  unfold orderedTimestampsToWaits
  by_cases hzero : i.val = 0
  · rw [dif_pos hzero, dif_pos (by simpa using hzero)]
    rw [shiftAppendTimestamps, Fin.append_left]
  · rw [dif_neg hzero, dif_neg (by simpa using hzero)]
    rw [shiftAppendTimestamps, Fin.append_left]
    let previousCombined : Fin (firstCount + secondCount) :=
      ⟨(Fin.castAdd secondCount i).val - 1,
        lt_of_le_of_lt (Nat.sub_le _ _) (Fin.castAdd secondCount i).isLt⟩
    let previousFirst : Fin firstCount :=
      ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
    have hprevious : previousCombined =
        Fin.castAdd secondCount previousFirst := by
      apply Fin.ext
      rfl
    change Real.toNNReal
      (first i - shiftAppendTimestamps firstHorizon first second
        previousCombined) = Real.toNNReal (first i - first previousFirst)
    rw [hprevious, shiftAppendTimestamps, Fin.append_left]

/-- Away from the first coordinate of the second block, translating and
appending timestamps leaves its inter-event waits unchanged. -/
theorem orderedTimestampsToWaits_shiftAppend_natAdd_succ
    (firstHorizon : NNReal) (first : Fin firstCount → ℝ)
    (second : Fin (secondCount + 1) → ℝ) (i : Fin secondCount) :
    orderedTimestampsToWaits
        (shiftAppendTimestamps firstHorizon first second)
        (Fin.natAdd firstCount i.succ) =
      orderedTimestampsToWaits second i.succ := by
  unfold orderedTimestampsToWaits
  rw [dif_neg (by simp), dif_neg (by simp)]
  rw [shiftAppendTimestamps, Fin.append_right]
  let previousCombined : Fin (firstCount + (secondCount + 1)) :=
    ⟨(Fin.natAdd firstCount i.succ).val - 1,
      lt_of_le_of_lt (Nat.sub_le _ _) (Fin.natAdd firstCount i.succ).isLt⟩
  let previousSecond : Fin (secondCount + 1) :=
    ⟨i.succ.val - 1,
      lt_of_le_of_lt (Nat.sub_le _ _) i.succ.isLt⟩
  have hprevious : previousCombined =
      Fin.natAdd firstCount previousSecond := by
    apply Fin.ext
    simp [previousCombined, previousSecond]
  change Real.toNNReal
      (((firstHorizon : ℝ) + second i.succ) -
        shiftAppendTimestamps firstHorizon first second previousCombined) =
    Real.toNNReal (second i.succ - second previousSecond)
  rw [hprevious, shiftAppendTimestamps, Fin.append_right]
  apply congrArg Real.toNNReal
  ring

/-- The first wait in the translated second block is exactly its original
first wait plus the unused residual of the first horizon. -/
theorem orderedTimestampsToWaits_shiftAppend_bridge
    (firstHorizon : NNReal) (first : Fin firstCount → ℝ)
    (second : Fin (secondCount + 1) → ℝ)
    (hfirstMono : Monotone first)
    (hfirstNonneg : ∀ i, 0 ≤ first i)
    (hfirstLe : ∀ i, first i ≤ (firstHorizon : ℝ))
    (hsecondZero : 0 ≤ second 0) :
    orderedTimestampsToWaits
        (shiftAppendTimestamps firstHorizon first second)
        (Fin.natAdd firstCount 0) =
      (firstHorizon - ∑ i, orderedTimestampsToWaits first i) +
        orderedTimestampsToWaits second 0 := by
  cases firstCount with
  | zero =>
      have hzeroIndex : Fin.natAdd 0 (0 : Fin (secondCount + 1)) = 0 := by
        apply Fin.ext
        simp
      rw [hzeroIndex]
      apply NNReal.eq
      rw [orderedTimestampsToWaits_zero,
        orderedTimestampsToWaits_zero]
      simp only [shiftAppendTimestamps,
        Finset.univ_eq_empty, Finset.sum_empty, tsub_zero, NNReal.coe_add]
      rw [Fin.append_left_nil first
        (fun i => (firstHorizon : ℝ) + second i) rfl]
      simp [Real.toNNReal_of_nonneg hsecondZero,
        Real.toNNReal_of_nonneg
          (add_nonneg (NNReal.coe_nonneg firstHorizon) hsecondZero)]
  | succ n =>
      have hsumReal := sum_orderedTimestampsToWaits first hfirstMono
        (hfirstNonneg 0)
      have hsumLe : (∑ i, orderedTimestampsToWaits first i) ≤
          firstHorizon := by
        rw [← NNReal.coe_le_coe, hsumReal]
        exact hfirstLe (Fin.last n)
      let previousCombined : Fin ((n + 1) + (secondCount + 1)) :=
        ⟨(Fin.natAdd (n + 1) (0 : Fin (secondCount + 1))).val - 1,
          lt_of_le_of_lt (Nat.sub_le _ _)
            (Fin.natAdd (n + 1) (0 : Fin (secondCount + 1))).isLt⟩
      have hprevious : previousCombined =
          Fin.castAdd (secondCount + 1) (Fin.last n) := by
        apply Fin.ext
        simp [previousCombined]
      have hbridgeWait :
          orderedTimestampsToWaits
              (shiftAppendTimestamps firstHorizon first second)
              (Fin.natAdd (n + 1) 0) =
            Real.toNNReal ((firstHorizon : ℝ) + second 0 -
              first (Fin.last n)) := by
        unfold orderedTimestampsToWaits
        rw [dif_neg (by simp)]
        change Real.toNNReal
          (shiftAppendTimestamps firstHorizon first second
              (Fin.natAdd (n + 1) 0) -
            shiftAppendTimestamps firstHorizon first second previousCombined) = _
        rw [hprevious, shiftAppendTimestamps, Fin.append_right,
          Fin.append_left]
      rw [hbridgeWait, orderedTimestampsToWaits_zero]
      apply NNReal.eq
      rw [NNReal.coe_add, NNReal.coe_sub hsumLe, hsumReal]
      simp only [Real.coe_toNNReal _ hsecondZero]
      have hdiff : 0 ≤ (firstHorizon : ℝ) + second 0 - first (Fin.last n) := by
        linarith [hfirstLe (Fin.last n)]
      rw [Real.coe_toNNReal _ hdiff]
      ring

/-- Concatenate padded wait schedules across adjacent horizons. The first
wait of the second schedule is joined to the unused residual of the first
horizon, because no refresh occurs at the deterministic horizon boundary. -/
def concatenateRefreshSchedules (firstHorizon : NNReal)
    (firstCount secondCount : ℕ)
    (schedules : CandidateScheduleSample × CandidateScheduleSample) :
    CandidateScheduleSample :=
  let first := schedules.1
  let second := schedules.2
  (firstCount + secondCount, fun index =>
    if _hfirst : index < firstCount then first.2 index
    else if _hsecond : index - firstCount < secondCount then
      if index = firstCount then
        (firstHorizon - scheduleElapsed firstCount first) + second.2 0
      else second.2 (index - firstCount)
    else 0)

theorem concatenateRefreshSchedules_fst (firstHorizon : NNReal)
    (firstCount secondCount : ℕ)
    (first second : CandidateScheduleSample) :
    (concatenateRefreshSchedules firstHorizon firstCount secondCount
      (first, second)).1 = firstCount + secondCount := rfl

/-- Schedule concatenation is measurable jointly in both padded schedules. -/
theorem measurable_concatenateRefreshSchedules (firstHorizon : NNReal)
    (firstCount secondCount : ℕ) :
    Measurable
      (concatenateRefreshSchedules firstHorizon firstCount secondCount) := by
  apply measurable_const.prodMk
  apply measurable_pi_lambda
  intro index
  have hbridge : Measurable (fun schedules :
      CandidateScheduleSample × CandidateScheduleSample =>
      (firstHorizon - scheduleElapsed firstCount schedules.1) +
        schedules.2.2 0) :=
    (measurable_const.sub
      ((measurable_scheduleElapsed firstCount).comp measurable_fst)).add
        ((measurable_pi_apply 0).comp (measurable_snd.comp measurable_snd))
  split_ifs
  · fun_prop
  · exact hbridge
  · fun_prop
  · fun_prop

/-- Concatenate two schedules using the counts stored in the schedules
themselves. -/
def concatenateAdjacentRefreshSchedules (firstHorizon : NNReal)
    (schedules : CandidateScheduleSample × CandidateScheduleSample) :
    CandidateScheduleSample :=
  concatenateRefreshSchedules firstHorizon schedules.1.1 schedules.2.1 schedules

/-- Stored-count schedule concatenation is measurable. -/
theorem measurable_concatenateAdjacentRefreshSchedules
    (firstHorizon : NNReal) :
    Measurable (concatenateAdjacentRefreshSchedules firstHorizon) := by
  intro event hevent
  rw [show concatenateAdjacentRefreshSchedules firstHorizon ⁻¹' event =
      ⋃ firstCount : ℕ, ⋃ secondCount : ℕ,
        ({schedules | schedules.1.1 = firstCount ∧
            schedules.2.1 = secondCount} ∩
          concatenateRefreshSchedules firstHorizon firstCount secondCount ⁻¹'
            event) by
    ext schedules
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_setOf_eq]
    constructor
    · intro hschedules
      exact ⟨schedules.1.1, schedules.2.1, ⟨rfl, rfl⟩, hschedules⟩
    · rintro ⟨firstCount, secondCount, ⟨hfirst, hsecond⟩, hschedules⟩
      simpa [concatenateAdjacentRefreshSchedules, hfirst, hsecond] using
        hschedules]
  apply MeasurableSet.iUnion
  intro firstCount
  apply MeasurableSet.iUnion
  intro secondCount
  exact ((measurableSet_eq_fun (measurable_fst.comp measurable_fst)
      measurable_const).inter
    (measurableSet_eq_fun (measurable_fst.comp measurable_snd)
      measurable_const)).inter
    ((measurable_concatenateRefreshSchedules firstHorizon firstCount
      secondCount) hevent)

/-- For already ordered timestamp blocks in adjacent intervals, conversion to
padded waits commutes exactly with schedule concatenation. -/
theorem padCandidateWaits_orderedTimestampsToWaits_shiftAppend
    (firstHorizon : NNReal) (first : Fin firstCount → ℝ)
    (second : Fin secondCount → ℝ)
    (hfirstMono : Monotone first)
    (hfirstNonneg : ∀ i, 0 ≤ first i)
    (hfirstLe : ∀ i, first i ≤ (firstHorizon : ℝ))
    (hsecondNonneg : ∀ i, 0 ≤ second i) :
    padCandidateWaits (firstCount + secondCount)
        (orderedTimestampsToWaits
          (shiftAppendTimestamps firstHorizon first second)) =
      concatenateRefreshSchedules firstHorizon firstCount secondCount
        (padCandidateWaits firstCount (orderedTimestampsToWaits first),
          padCandidateWaits secondCount (orderedTimestampsToWaits second)) := by
  apply Prod.ext
  · rfl
  · funext index
    by_cases hfirstIndex : index < firstCount
    · have htotal : index < firstCount + secondCount := by omega
      simp only [padCandidateWaits, htotal, dite_true,
        concatenateRefreshSchedules, hfirstIndex]
      exact orderedTimestampsToWaits_shiftAppend_castAdd firstHorizon first
        second ⟨index, hfirstIndex⟩
    · by_cases hsecondIndex : index - firstCount < secondCount
      · have htotal : index < firstCount + secondCount := by omega
        rw [show (padCandidateWaits (firstCount + secondCount)
            (orderedTimestampsToWaits
              (shiftAppendTimestamps firstHorizon first second))).2 index =
            orderedTimestampsToWaits
              (shiftAppendTimestamps firstHorizon first second) ⟨index, htotal⟩ by
          simp [padCandidateWaits, htotal]]
        change orderedTimestampsToWaits
            (shiftAppendTimestamps firstHorizon first second) ⟨index, htotal⟩ =
          (concatenateRefreshSchedules firstHorizon firstCount secondCount
            (padCandidateWaits firstCount (orderedTimestampsToWaits first),
              padCandidateWaits secondCount
                (orderedTimestampsToWaits second))).2 index
        by_cases hbridge : index = firstCount
        · subst index
          have hsecondPos : 0 < secondCount := by omega
          obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
            (Nat.ne_of_gt hsecondPos)
          simp only [concatenateRefreshSchedules, lt_irrefl, ↓reduceDIte,
            Nat.sub_self, Nat.zero_lt_succ, ↓reduceIte]
          unfold scheduleElapsed
          rw [scheduleElapsed_padCandidateWaits]
          have hbridgeIndex :
              (⟨firstCount, htotal⟩ : Fin (firstCount + (remaining + 1))) =
                Fin.natAdd firstCount 0 := by
            apply Fin.ext
            simp
          rw [hbridgeIndex]
          rw [show (padCandidateWaits (remaining + 1)
              (orderedTimestampsToWaits second)).2 0 =
              orderedTimestampsToWaits second 0 by
            simp [padCandidateWaits]]
          exact orderedTimestampsToWaits_shiftAppend_bridge firstHorizon
            first second hfirstMono hfirstNonneg hfirstLe
              (hsecondNonneg 0)
        ·
          have hoffsetPos : 0 < index - firstCount := by omega
          obtain ⟨offset, hoffset⟩ := Nat.exists_eq_succ_of_ne_zero
            (Nat.ne_of_gt hoffsetPos)
          have hfirstLeIndex : firstCount ≤ index := by omega
          have hindexValue : index = firstCount + offset + 1 := by
            have hcancel := Nat.sub_add_cancel hfirstLeIndex
            omega
          have hsecondCountPos : 0 < secondCount := by omega
          obtain ⟨remaining, hremaining⟩ := Nat.exists_eq_succ_of_ne_zero
            (Nat.ne_of_gt hsecondCountPos)
          subst secondCount
          have hoffsetFin : offset < remaining := by omega
          have hindexEq :
              (⟨index, htotal⟩ : Fin (firstCount + (remaining + 1))) =
                Fin.natAdd firstCount
                  (⟨offset, hoffsetFin⟩ : Fin remaining).succ := by
            apply Fin.ext
            change index = firstCount + (offset + 1)
            omega
          rw [hindexEq]
          simp only [concatenateRefreshSchedules, hindexValue,
            show ¬firstCount + offset + 1 < firstCount by omega,
            ↓reduceDIte,
            show firstCount + offset + 1 - firstCount = offset + 1 by omega,
            show offset + 1 < remaining + 1 by omega, ↓reduceDIte,
            show firstCount + offset + 1 ≠ firstCount by omega,
            ↓reduceIte]
          rw [show (padCandidateWaits (remaining + 1)
              (orderedTimestampsToWaits second)).2 (offset + 1) =
              orderedTimestampsToWaits second
                (⟨offset, hoffsetFin⟩ : Fin remaining).succ by
            unfold padCandidateWaits
            change (if h : offset + 1 < remaining + 1 then
              orderedTimestampsToWaits second ⟨offset + 1, h⟩ else 0) = _
            rw [dif_pos (by omega)]
            congr 2]
          simpa [padCandidateWaits] using
            (orderedTimestampsToWaits_shiftAppend_natAdd_succ
              firstHorizon first second ⟨offset, hoffsetFin⟩)
      · have htotalNot : ¬index < firstCount + secondCount := by omega
        simp [padCandidateWaits, concatenateRefreshSchedules, hfirstIndex,
          hsecondIndex, htotalNot]

/-- On the adjacent-horizon support, the complete raw-timestamp-to-schedule
map commutes with translating/appending the raw blocks and concatenating the
resulting schedules. -/
theorem timestampsToSchedule_shiftAppend
    (first : PositiveHorizon) (second : PositiveHorizon)
    (firstTimes : Fin firstCount → ℝ)
    (secondTimes : Fin secondCount → ℝ)
    (hfirstInside : ∀ i,
      firstTimes i ∈ Set.Ioc 0 (first.duration : ℝ))
    (hsecondInside : ∀ i,
      secondTimes i ∈ Set.Ioc 0 (second.duration : ℝ)) :
    timestampsToSchedule (firstCount + secondCount)
        (shiftAppendTimestamps first.duration firstTimes secondTimes) =
      concatenateRefreshSchedules first.duration firstCount secondCount
        (timestampsToSchedule firstCount firstTimes,
          timestampsToSchedule secondCount secondTimes) := by
  unfold timestampsToSchedule
  rw [tupleSortValues_shiftAppend first.duration firstTimes secondTimes
    (fun i => (hfirstInside i).2)
    (fun i => le_of_lt (hsecondInside i).1)]
  exact padCandidateWaits_orderedTimestampsToWaits_shiftAppend first.duration
    (firstTimes ∘ Tuple.sort firstTimes)
    (secondTimes ∘ Tuple.sort secondTimes)
    (Tuple.monotone_sort firstTimes)
    (fun i => le_of_lt (hfirstInside (Tuple.sort firstTimes i)).1)
    (fun i => (hfirstInside (Tuple.sort firstTimes i)).2)
    (fun i => le_of_lt (hsecondInside (Tuple.sort secondTimes i)).1)

/-- Law-level version of timestamp/schedule concatenation for two independent
uniform timestamp blocks. -/
theorem map_timestampsToSchedule_shiftAppend_prod
    (first second : PositiveHorizon) (firstCount secondCount : ℕ) :
    Measure.map (timestampsToSchedule (firstCount + secondCount))
        (Measure.map
          (fun pair : (Fin firstCount → ℝ) × (Fin secondCount → ℝ) =>
            shiftAppendTimestamps first.duration pair.1 pair.2)
          ((first.candidateTimesMeasure firstCount).prod
            (second.candidateTimesMeasure secondCount))) =
      Measure.map
        (concatenateRefreshSchedules first.duration firstCount secondCount)
        ((first.fixedScheduleMeasure (timestampOrdering firstCount)).prod
          (second.fixedScheduleMeasure
            (timestampOrdering secondCount))) := by
  rw [first.fixedScheduleMeasure_timestampOrdering,
    second.fixedScheduleMeasure_timestampOrdering]
  rw [Measure.map_prod_map _ _
    (measurable_timestampsToSchedule firstCount)
    (measurable_timestampsToSchedule secondCount)]
  rw [Measure.map_map (measurable_timestampsToSchedule
      (firstCount + secondCount))
    (measurable_shiftAppendTimestamps first.duration firstCount secondCount)]
  rw [Measure.map_map
    (measurable_concatenateRefreshSchedules first.duration firstCount
      secondCount)
    ((measurable_timestampsToSchedule firstCount).prodMap
      (measurable_timestampsToSchedule secondCount))]
  apply Measure.map_congr
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun
      ((measurable_timestampsToSchedule (firstCount + secondCount)).comp
        (measurable_shiftAppendTimestamps first.duration firstCount
          secondCount))
      ((measurable_concatenateRefreshSchedules first.duration firstCount
          secondCount).comp
        ((measurable_timestampsToSchedule firstCount).prodMap
          (measurable_timestampsToSchedule secondCount))))).2
  filter_upwards [first.ae_candidateTimesMeasure_mem firstCount] with
      firstTimes hfirst
  filter_upwards [second.ae_candidateTimesMeasure_mem secondCount] with
      secondTimes hsecond
  exact timestampsToSchedule_shiftAppend first second firstTimes secondTimes
    hfirst hsecond

/-- Generic law-level timestamp concatenation for any two tuple laws supported
on their respective adjacent horizons. -/
theorem map_timestampsToSchedule_shiftAppend_prod_of_ae
    (first second : PositiveHorizon) (firstCount secondCount : ℕ)
    (firstLaw : Measure (Fin firstCount → ℝ))
    (secondLaw : Measure (Fin secondCount → ℝ))
    [SFinite firstLaw] [SFinite secondLaw]
    (hfirst : ∀ᵐ times ∂firstLaw,
      ∀ i, times i ∈ Set.Ioc 0 (first.duration : ℝ))
    (hsecond : ∀ᵐ times ∂secondLaw,
      ∀ i, times i ∈ Set.Ioc 0 (second.duration : ℝ)) :
    Measure.map (timestampsToSchedule (firstCount + secondCount))
        (Measure.map
          (fun pair : (Fin firstCount → ℝ) × (Fin secondCount → ℝ) =>
            shiftAppendTimestamps first.duration pair.1 pair.2)
          (firstLaw.prod secondLaw)) =
      Measure.map
        (concatenateRefreshSchedules first.duration firstCount secondCount)
        ((Measure.map (timestampsToSchedule firstCount) firstLaw).prod
          (Measure.map (timestampsToSchedule secondCount) secondLaw)) := by
  rw [Measure.map_prod_map _ _
    (measurable_timestampsToSchedule firstCount)
    (measurable_timestampsToSchedule secondCount)]
  rw [Measure.map_map (measurable_timestampsToSchedule
      (firstCount + secondCount))
    (measurable_shiftAppendTimestamps first.duration firstCount secondCount)]
  rw [Measure.map_map
    (measurable_concatenateRefreshSchedules first.duration firstCount
      secondCount)
    ((measurable_timestampsToSchedule firstCount).prodMap
      (measurable_timestampsToSchedule secondCount))]
  apply Measure.map_congr
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun
      ((measurable_timestampsToSchedule (firstCount + secondCount)).comp
        (measurable_shiftAppendTimestamps first.duration firstCount
          secondCount))
      ((measurable_concatenateRefreshSchedules first.duration firstCount
          secondCount).comp
        ((measurable_timestampsToSchedule firstCount).prodMap
          (measurable_timestampsToSchedule secondCount))))).2
  filter_upwards [hfirst] with firstTimes hfirstTimes
  filter_upwards [hsecond] with secondTimes hsecondTimes
  exact timestampsToSchedule_shiftAppend first second firstTimes secondTimes
    hfirstTimes hsecondTimes

/-- Translating and appending independent timestamp-mass tuples produces the
canonical first-block/second-block product measure on absolute timestamps. -/
theorem map_shiftAppend_pi_timestampMass_prod
    (first second : PositiveHorizon) (firstCount secondCount : ℕ) :
    Measure.map
        (fun pair : (Fin firstCount → ℝ) × (Fin secondCount → ℝ) =>
          shiftAppendTimestamps first.duration pair.1 pair.2)
        ((Measure.pi fun _ : Fin firstCount =>
            first.timestampMassMeasure).prod
          (Measure.pi fun _ : Fin secondCount =>
            second.timestampMassMeasure)) =
      Measure.pi fun i : Fin (firstCount + secondCount) =>
        if canonicalBoolAssignment (firstCount + secondCount) firstCount i
        then first.timestampMassMeasure
        else Measure.map
          (fun time : ℝ => (first.duration : ℝ) + time)
          second.timestampMassMeasure := by
  let shift : ℝ → ℝ := fun time => (first.duration : ℝ) + time
  let shiftTuple : (Fin secondCount → ℝ) → (Fin secondCount → ℝ) :=
    fun times i => shift (times i)
  have hshift : Measurable shift := by
    dsimp [shift]
    fun_prop
  have hshiftTuple : Measurable shiftTuple := by
    dsimp [shiftTuple]
    fun_prop
  have hpi : Measure.map shiftTuple
      (Measure.pi fun _ : Fin secondCount => second.timestampMassMeasure) =
      Measure.pi fun _ : Fin secondCount =>
        Measure.map shift second.timestampMassMeasure := by
    exact Measure.pi_map_pi (fun _ => hshift.aemeasurable)
  rw [← map_prod_pi_pi_finAppend first.timestampMassMeasure
    (Measure.map shift second.timestampMassMeasure) firstCount secondCount]
  rw [← hpi]
  have hprod :
      (Measure.pi fun _ : Fin firstCount => first.timestampMassMeasure).prod
          (Measure.map shiftTuple
            (Measure.pi fun _ : Fin secondCount =>
              second.timestampMassMeasure)) =
        Measure.map (Prod.map id shiftTuple)
          ((Measure.pi fun _ : Fin firstCount =>
              first.timestampMassMeasure).prod
            (Measure.pi fun _ : Fin secondCount =>
              second.timestampMassMeasure)) := by
    simpa using Measure.map_prod_map
      (Measure.pi fun _ : Fin firstCount => first.timestampMassMeasure)
      (Measure.pi fun _ : Fin secondCount => second.timestampMassMeasure)
      measurable_id hshiftTuple
  rw [hprod]
  rw [Measure.map_map (by fun_prop)
    (measurable_id.prodMap hshiftTuple)]
  apply congrArg (fun map => Measure.map map
    ((Measure.pi fun _ : Fin firstCount => first.timestampMassMeasure).prod
      (Measure.pi fun _ : Fin secondCount => second.timestampMassMeasure)))
  funext pair
  rfl

/-- Each canonical count split in the adjacent timestamp expansion is exactly
the pushforward of the product of the two unnormalized schedule masses by
schedule concatenation. -/
theorem map_timestampsToSchedule_canonical_eq_concatenate_mass
    (first second : PositiveHorizon) (firstCount secondCount : ℕ) :
    Measure.map (timestampsToSchedule (firstCount + secondCount))
        (Measure.pi fun i : Fin (firstCount + secondCount) =>
          if canonicalBoolAssignment (firstCount + secondCount) firstCount i
          then first.timestampMassMeasure
          else Measure.map
            (fun time : ℝ => (first.duration : ℝ) + time)
            second.timestampMassMeasure) =
      Measure.map
        (concatenateRefreshSchedules first.duration firstCount secondCount)
        ((first.timestampScheduleMass firstCount).prod
          (second.timestampScheduleMass secondCount)) := by
  rw [← map_shiftAppend_pi_timestampMass_prod first second firstCount
    secondCount]
  rw [Measure.map_map (measurable_timestampsToSchedule
      (firstCount + secondCount))
    (measurable_shiftAppendTimestamps first.duration firstCount secondCount)]
  unfold PositiveHorizon.timestampScheduleMass
  rw [← Measure.map_map (measurable_timestampsToSchedule
      (firstCount + secondCount))
    (measurable_shiftAppendTimestamps first.duration firstCount secondCount)]
  exact map_timestampsToSchedule_shiftAppend_prod_of_ae first second
    firstCount secondCount
    (Measure.pi fun _ : Fin firstCount => first.timestampMassMeasure)
    (Measure.pi fun _ : Fin secondCount => second.timestampMassMeasure)
    (first.ae_pi_timestampMassMeasure_mem firstCount)
    (second.ae_pi_timestampMassMeasure_mem secondCount)

/-- The schedule law on an adjacent horizon is a double Janossy sum over the
two interval counts, with each term obtained by concatenating the corresponding
unnormalized schedule masses. -/
theorem poissonCandidateSchedule_add_eq_sum_concatenate_mass
    (refreshRate : NNReal) (first second : PositiveHorizon) :
    poissonCandidateSchedule
        (refreshRate * (first.add second).duration) (first.add second) =
      Measure.sum fun counts : ℕ × ℕ =>
        (poissonScheduleMassWeight refreshRate first counts.1 *
            poissonScheduleMassWeight refreshRate second counts.2) •
          Measure.map
            (concatenateRefreshSchedules first.duration counts.1 counts.2)
            ((first.timestampScheduleMass counts.1).prod
              (second.timestampScheduleMass counts.2)) := by
  rw [poissonCandidateSchedule_eq_sum_timestampMass]
  rw [show (Measure.sum fun n : ℕ =>
      poissonScheduleMassWeight refreshRate (first.add second) n •
        (first.add second).timestampScheduleMass n) =
      Measure.sum (fun n : ℕ =>
        ∑ k ∈ Finset.range (n + 1),
          (poissonScheduleMassWeight refreshRate (first.add second) n *
            (Nat.choose n k : ENNReal)) •
          Measure.map (timestampsToSchedule n)
            (Measure.pi fun i =>
              if canonicalBoolAssignment n k i then
                first.timestampMassMeasure
              else Measure.map
                (fun time : ℝ => (first.duration : ℝ) + time)
                second.timestampMassMeasure)) by
    apply Measure.sum_congr
    intro n
    rw [first.timestampScheduleMass_add_eq_sum_count second n]
    simp_rw [← Nat.cast_smul_eq_nsmul ENNReal]
    rw [Finset.smul_sum]
    simp_rw [smul_smul]]
  rw [show (Measure.sum fun n : ℕ =>
      ∑ k ∈ Finset.range (n + 1),
        (poissonScheduleMassWeight refreshRate (first.add second) n *
          (Nat.choose n k : ENNReal)) •
        Measure.map (timestampsToSchedule n)
          (Measure.pi fun i =>
            if canonicalBoolAssignment n k i then
              first.timestampMassMeasure
            else Measure.map
              (fun time : ℝ => (first.duration : ℝ) + time)
              second.timestampMassMeasure)) =
      Measure.sum fun n : ℕ =>
        ∑ k ∈ Finset.range (n + 1),
          (poissonScheduleMassWeight refreshRate (first.add second)
              (k + (n - k)) *
            (Nat.choose (k + (n - k)) k : ENNReal)) •
          Measure.map (timestampsToSchedule (k + (n - k)))
            (Measure.pi fun i =>
              if canonicalBoolAssignment (k + (n - k)) k i then
                first.timestampMassMeasure
              else Measure.map
                (fun time : ℝ => (first.duration : ℝ) + time)
                second.timestampMassMeasure) by
    apply Measure.sum_congr
    intro n
    apply Finset.sum_congr rfl
    intro k hk
    rw [Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]]
  refine (measureSum_sum_range_succ_sub_eq_sum_prod
    (fun k m =>
      (poissonScheduleMassWeight refreshRate (first.add second) (k + m) *
        (Nat.choose (k + m) k : ENNReal)) •
      Measure.map (timestampsToSchedule (k + m))
        (Measure.pi fun i =>
          if canonicalBoolAssignment (k + m) k i then
            first.timestampMassMeasure
          else Measure.map
            (fun time : ℝ => (first.duration : ℝ) + time)
            second.timestampMassMeasure))).trans ?_
  congr 1
  funext counts
  rw [map_timestampsToSchedule_canonical_eq_concatenate_mass first second
    counts.1 counts.2]
  rw [poissonScheduleMassWeight_add_mul_choose refreshRate first second
    counts.1 counts.2]

/-- On a fixed pair of Janossy count strata, stored-count concatenation agrees
with the corresponding fixed-count concatenation, including independent
scalar weights. -/
theorem map_concatenateAdjacent_smul_timestampMass_prod
    (first second : PositiveHorizon) (firstCount secondCount : ℕ)
    (firstWeight secondWeight : ENNReal) :
    Measure.map (concatenateAdjacentRefreshSchedules first.duration)
        ((firstWeight • first.timestampScheduleMass firstCount).prod
          (secondWeight • second.timestampScheduleMass secondCount)) =
      (firstWeight * secondWeight) •
        Measure.map
          (concatenateRefreshSchedules first.duration firstCount secondCount)
          ((first.timestampScheduleMass firstCount).prod
            (second.timestampScheduleMass secondCount)) := by
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    Measure.map_smul]
  congr 1
  apply Measure.map_congr
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun
      ((measurable_concatenateAdjacentRefreshSchedules first.duration))
      (measurable_concatenateRefreshSchedules first.duration firstCount
        secondCount))).2
  filter_upwards [first.ae_timestampScheduleMass_fst firstCount] with
      firstSchedule hfirst
  filter_upwards [second.ae_timestampScheduleMass_fst secondCount] with
      secondSchedule hsecond
  simp [concatenateAdjacentRefreshSchedules, hfirst, hsecond]

/-- Two independent homogeneous Poisson schedules on adjacent horizons,
concatenated using their stored counts, have exactly the homogeneous Poisson
schedule law on the combined horizon. -/
theorem map_concatenateAdjacent_poissonCandidateSchedule_prod
    (refreshRate : NNReal) (first second : PositiveHorizon) :
    Measure.map (concatenateAdjacentRefreshSchedules first.duration)
        ((poissonCandidateSchedule (refreshRate * first.duration) first).prod
          (poissonCandidateSchedule (refreshRate * second.duration) second)) =
      poissonCandidateSchedule
        (refreshRate * (first.add second).duration) (first.add second) := by
  rw [poissonCandidateSchedule_eq_sum_timestampMass,
    poissonCandidateSchedule_eq_sum_timestampMass]
  rw [Measure.prod_sum]
  rw [Measure.map_sum
    (measurable_concatenateAdjacentRefreshSchedules first.duration).aemeasurable]
  simp_rw [map_concatenateAdjacent_smul_timestampMass_prod first second]
  exact (poissonCandidateSchedule_add_eq_sum_concatenate_mass refreshRate
    first second).symm

theorem concatenateRefreshSchedules_first
    (firstHorizon : NNReal) (firstCount secondCount index : ℕ)
    (first second : CandidateScheduleSample) (hindex : index < firstCount) :
    (concatenateRefreshSchedules firstHorizon firstCount secondCount
      (first, second)).2 index = first.2 index := by
  simp [concatenateRefreshSchedules, hindex]

theorem concatenateRefreshSchedules_bridge
    (firstHorizon : NNReal) (firstCount secondCount : ℕ)
    (first second : CandidateScheduleSample) (hsecond : 0 < secondCount) :
    (concatenateRefreshSchedules firstHorizon firstCount secondCount
      (first, second)).2 firstCount =
        (firstHorizon - scheduleElapsed firstCount first) + second.2 0 := by
  simp [concatenateRefreshSchedules, hsecond]

theorem concatenateRefreshSchedules_second_succ
    (firstHorizon : NNReal) (firstCount secondCount index : ℕ)
    (first second : CandidateScheduleSample)
    (hindex : index + 1 < secondCount) :
    (concatenateRefreshSchedules firstHorizon firstCount secondCount
      (first, second)).2 (firstCount + index + 1) =
        second.2 (index + 1) := by
  simp only [concatenateRefreshSchedules]
  split_ifs with hfirst hactive hbridge
  · omega
  · omega
  · rw [show firstCount + index + 1 = firstCount + (index + 1) by omega,
      Nat.add_sub_cancel_left]
  · omega

/-- On valid schedules with a nonempty second block, concatenation consumes
exactly the first horizon plus the elapsed part of the second schedule. -/
theorem scheduleElapsed_concatenateRefreshSchedules_of_pos
    (firstHorizon : NNReal) (firstCount secondCount : ℕ)
    (first second : CandidateScheduleSample)
    (hsecond : 0 < secondCount)
    (hfirst : scheduleElapsed firstCount first ≤ firstHorizon) :
    scheduleElapsed (firstCount + secondCount)
      (concatenateRefreshSchedules firstHorizon firstCount secondCount
        (first, second)) =
      firstHorizon + scheduleElapsed secondCount second := by
  obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hsecond)
  unfold scheduleElapsed
  rw [Finset.sum_range_add]
  have hfirstSum :
      (∑ index ∈ Finset.range firstCount,
        (concatenateRefreshSchedules firstHorizon firstCount (remaining + 1)
          (first, second)).2 index) =
        ∑ index ∈ Finset.range firstCount, first.2 index := by
    apply Finset.sum_congr rfl
    intro index hindex
    exact concatenateRefreshSchedules_first _ _ _ _ _ _
      (Finset.mem_range.mp hindex)
  rw [hfirstSum, Finset.sum_range_succ']
  rw [show firstCount + 0 = firstCount by omega,
    concatenateRefreshSchedules_bridge _ _ _ _ _ (by omega)]
  have htailSum :
      (∑ index ∈ Finset.range remaining,
        (concatenateRefreshSchedules firstHorizon firstCount (remaining + 1)
          (first, second)).2 (firstCount + (index + 1))) =
        ∑ index ∈ Finset.range remaining, second.2 (index + 1) := by
    apply Finset.sum_congr rfl
    intro index hindex
    rw [show firstCount + (index + 1) = firstCount + index + 1 by omega]
    exact concatenateRefreshSchedules_second_succ _ _ _ _ _ _
      (Nat.succ_lt_succ (Finset.mem_range.mp hindex))
  rw [htailSum, Finset.sum_range_succ']
  have hfirst' :
      (∑ index ∈ Finset.range firstCount, first.2 index) ≤ firstHorizon := by
    simpa only [scheduleElapsed] using hfirst
  calc
    (∑ index ∈ Finset.range firstCount, first.2 index) +
        ((∑ index ∈ Finset.range remaining, second.2 (index + 1)) +
          ((firstHorizon - scheduleElapsed firstCount first) + second.2 0)) =
      ((∑ index ∈ Finset.range firstCount, first.2 index) +
        (firstHorizon - scheduleElapsed firstCount first)) +
          ((∑ index ∈ Finset.range remaining, second.2 (index + 1)) +
            second.2 0) := by ac_rfl
    _ = firstHorizon +
          ((∑ index ∈ Finset.range remaining, second.2 (index + 1)) +
            second.2 0) := by
      rw [show scheduleElapsed firstCount first =
        ∑ index ∈ Finset.range firstCount, first.2 index by rfl]
      rw [add_tsub_cancel_of_le hfirst']

theorem scheduleElapsed_concatenateRefreshSchedules_zero
    (firstHorizon : NNReal) (firstCount : ℕ)
    (first second : CandidateScheduleSample) :
    scheduleElapsed (firstCount + 0)
      (concatenateRefreshSchedules firstHorizon firstCount 0
        (first, second)) = scheduleElapsed firstCount first := by
  unfold scheduleElapsed
  apply Finset.sum_congr
  · simp
  · intro index hindex
    exact concatenateRefreshSchedules_first _ _ _ _ _ _
      (Finset.mem_range.mp hindex)

/-- A jointly timed Markov transition and the refresh applied at scheduled
times.  Semigroup laws are intentionally separate: schedule execution only
needs joint measurability and Markovness. -/
structure TimedRefreshProcess (State : Type*) [MeasurableSpace State] where
  evolve : Kernel (State × NNReal) State
  refresh : Kernel State State
  evolve_markov : IsMarkovKernel evolve := by infer_instance
  refresh_markov : IsMarkovKernel refresh := by infer_instance

attribute [instance] TimedRefreshProcess.evolve_markov
  TimedRefreshProcess.refresh_markov

/-- Fixed-time section of a jointly timed transition. -/
noncomputable def TimedRefreshProcess.section
    (process : TimedRefreshProcess State) (time : NNReal) :
    Kernel State State :=
  Kernel.comap process.evolve (fun state => (state, time))
    (measurable_id.prodMk measurable_const)

instance TimedRefreshProcess.section.instIsMarkovKernel
    (process : TimedRefreshProcess State) (time : NNReal) :
    IsMarkovKernel (process.section time) := by
  unfold TimedRefreshProcess.section
  infer_instance

/-- Chapman--Kolmogorov law for the timed transition before refreshment. -/
def TimedRefreshProcess.HasSemigroup
    (process : TimedRefreshProcess State) : Prop :=
  ∀ first second : NNReal,
    process.section second ∘ₖ process.section first =
      process.section (first + second)

/-- Evolve by one schedule coordinate and then refresh, retaining the padded
schedule for subsequent coordinates. -/
noncomputable def TimedRefreshProcess.scheduledCoordinateStep
    (process : TimedRefreshProcess State) (index : ℕ) :
    Kernel (ScheduledState State) (ScheduledState State) :=
  Kernel.prod
    (process.refresh ∘ₖ
      Kernel.comap process.evolve
        (fun p => (p.1, p.2.2 index))
        (measurable_fst.prodMk
          ((measurable_pi_apply index).comp
            (measurable_snd.comp measurable_snd))))
    (Kernel.deterministic Prod.snd measurable_snd)

instance TimedRefreshProcess.scheduledCoordinateStep.instIsMarkovKernel
    (process : TimedRefreshProcess State) (index : ℕ) :
    IsMarkovKernel (process.scheduledCoordinateStep index) := by
  unfold TimedRefreshProcess.scheduledCoordinateStep
  infer_instance

/-- State-only step obtained by fixing a padded schedule. -/
noncomputable def TimedRefreshProcess.fixedCoordinateStep
    (process : TimedRefreshProcess State)
    (schedule : CandidateScheduleSample) (index : ℕ) : Kernel State State :=
  process.refresh ∘ₖ
    process.section (schedule.2 index)

instance TimedRefreshProcess.fixedCoordinateStep.instIsMarkovKernel
    (process : TimedRefreshProcess State)
    (schedule : CandidateScheduleSample) (index : ℕ) :
    IsMarkovKernel (process.fixedCoordinateStep schedule index) := by
  unfold TimedRefreshProcess.fixedCoordinateStep
  infer_instance

theorem TimedRefreshProcess.fixedCoordinateStep_concatenate_first
    (process : TimedRefreshProcess State) (firstHorizon : NNReal)
    (firstCount secondCount index : ℕ)
    (first second : CandidateScheduleSample) (hindex : index < firstCount) :
    process.fixedCoordinateStep
      (concatenateRefreshSchedules firstHorizon firstCount secondCount
        (first, second)) index =
      process.fixedCoordinateStep first index := by
  unfold TimedRefreshProcess.fixedCoordinateStep
  rw [concatenateRefreshSchedules_first _ _ _ _ _ _ hindex]

theorem TimedRefreshProcess.fixedCoordinateStep_concatenate_second_succ
    (process : TimedRefreshProcess State) (firstHorizon : NNReal)
    (firstCount secondCount index : ℕ)
    (first second : CandidateScheduleSample)
    (hindex : index + 1 < secondCount) :
    process.fixedCoordinateStep
      (concatenateRefreshSchedules firstHorizon firstCount secondCount
        (first, second)) (firstCount + index + 1) =
      process.fixedCoordinateStep second (index + 1) := by
  unfold TimedRefreshProcess.fixedCoordinateStep
  rw [concatenateRefreshSchedules_second_succ _ _ _ _ _ _ hindex]

theorem TimedRefreshProcess.scheduledCoordinateStep_fixed
    (process : TimedRefreshProcess State)
    (schedule : CandidateScheduleSample) (index : ℕ) (state : State) :
    process.scheduledCoordinateStep index (state, schedule) =
      Measure.map (fun next => (next, schedule))
        (process.fixedCoordinateStep schedule index state) := by
  ext event hevent
  unfold TimedRefreshProcess.scheduledCoordinateStep
    TimedRefreshProcess.fixedCoordinateStep
  rw [Kernel.prod_apply, Kernel.deterministic_apply, Measure.prod_dirac]
  rfl

/-- Execute `count` scheduled refreshes beginning at coordinate `start`. -/
noncomputable def TimedRefreshProcess.executeScheduledRange
    (process : TimedRefreshProcess State) :
    ℕ → ℕ → Kernel (ScheduledState State) (ScheduledState State)
  | _, 0 => Kernel.id
  | start, count + 1 =>
      process.executeScheduledRange (start + 1) count ∘ₖ
        process.scheduledCoordinateStep start

instance TimedRefreshProcess.executeScheduledRange.instIsMarkovKernel
    (process : TimedRefreshProcess State) (start count : ℕ) :
    IsMarkovKernel (process.executeScheduledRange start count) := by
  induction count generalizing start with
  | zero =>
      simp only [TimedRefreshProcess.executeScheduledRange]
      infer_instance
  | succ count ih =>
      simp only [TimedRefreshProcess.executeScheduledRange]
      letI : IsMarkovKernel
          (process.executeScheduledRange (start + 1) count) := ih (start + 1)
      infer_instance

/-- State-only execution of a fixed range of refresh waits. -/
noncomputable def TimedRefreshProcess.executeFixedRange
    (process : TimedRefreshProcess State)
    (schedule : CandidateScheduleSample) : ℕ → ℕ → Kernel State State
  | _, 0 => Kernel.id
  | start, count + 1 =>
      process.executeFixedRange schedule (start + 1) count ∘ₖ
        process.fixedCoordinateStep schedule start

instance TimedRefreshProcess.executeFixedRange.instIsMarkovKernel
    (process : TimedRefreshProcess State)
    (schedule : CandidateScheduleSample) (start count : ℕ) :
    IsMarkovKernel (process.executeFixedRange schedule start count) := by
  induction count generalizing start with
  | zero =>
      simp only [TimedRefreshProcess.executeFixedRange]
      infer_instance
  | succ count ih =>
      simp only [TimedRefreshProcess.executeFixedRange]
      letI : IsMarkovKernel
          (process.executeFixedRange schedule (start + 1) count) :=
        ih (start + 1)
      infer_instance

/-- Fixed-schedule execution composes when adjacent coordinate ranges are
concatenated. -/
theorem TimedRefreshProcess.executeFixedRange_add
    (process : TimedRefreshProcess State)
    (schedule : CandidateScheduleSample) (start first second : ℕ) :
    process.executeFixedRange schedule start (first + second) =
      process.executeFixedRange schedule (start + first) second ∘ₖ
        process.executeFixedRange schedule start first := by
  induction first generalizing start with
  | zero => simp [TimedRefreshProcess.executeFixedRange]
  | succ first ih =>
      rw [Nat.succ_add]
      simp only [TimedRefreshProcess.executeFixedRange]
      rw [ih (start + 1), Kernel.comp_assoc]
      congr 2
      omega

/-- Every range wholly inside the first block of a concatenated schedule
executes exactly as the original first schedule. -/
theorem TimedRefreshProcess.executeFixedRange_concatenate_first
    (process : TimedRefreshProcess State) (firstHorizon : NNReal)
    (firstCount secondCount start count : ℕ)
    (first second : CandidateScheduleSample)
    (hbound : start + count ≤ firstCount) :
    process.executeFixedRange
      (concatenateRefreshSchedules firstHorizon firstCount secondCount
        (first, second)) start count =
      process.executeFixedRange first start count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      simp only [TimedRefreshProcess.executeFixedRange]
      rw [ih (start + 1) (by omega)]
      rw [process.fixedCoordinateStep_concatenate_first
        firstHorizon firstCount secondCount start first second (by omega)]

/-- Every positive-offset range inside the second block of a concatenated
schedule executes exactly as the correspondingly indexed second schedule. -/
theorem TimedRefreshProcess.executeFixedRange_concatenate_second
    (process : TimedRefreshProcess State) (firstHorizon : NNReal)
    (firstCount secondCount offset count : ℕ)
    (first second : CandidateScheduleSample) (hoffset : 0 < offset)
    (hbound : offset + count ≤ secondCount) :
    process.executeFixedRange
      (concatenateRefreshSchedules firstHorizon firstCount secondCount
        (first, second)) (firstCount + offset) count =
      process.executeFixedRange second offset count := by
  induction count generalizing offset with
  | zero => rfl
  | succ count ih =>
      simp only [TimedRefreshProcess.executeFixedRange]
      rw [show firstCount + offset + 1 = firstCount + (offset + 1) by omega]
      rw [ih (offset + 1) (by omega) (by omega)]
      have hindex : offset - 1 + 1 < secondCount := by omega
      have hcoordinate :=
        process.fixedCoordinateStep_concatenate_second_succ
          firstHorizon firstCount secondCount (offset - 1) first second hindex
      rw [show firstCount + (offset - 1) + 1 = firstCount + offset by omega,
        show offset - 1 + 1 = offset by omega] at hcoordinate
      rw [hcoordinate]

/-- Scheduled execution retains its fixed schedule and has exactly the
state-only fixed-range law. -/
theorem TimedRefreshProcess.executeScheduledRange_apply_fixed
    (process : TimedRefreshProcess State)
    (schedule : CandidateScheduleSample) (start count : ℕ) (state : State) :
    process.executeScheduledRange start count (state, schedule) =
      Measure.map (fun next => (next, schedule))
        (process.executeFixedRange schedule start count state) := by
  induction count generalizing start state with
  | zero =>
      simp only [TimedRefreshProcess.executeScheduledRange,
        TimedRefreshProcess.executeFixedRange, Kernel.id_apply]
      rw [Measure.map_dirac' (by fun_prop)]
  | succ count ih =>
      have hembed : Measurable (fun next : State => (next, schedule)) :=
        measurable_id.prodMk measurable_const
      rw [TimedRefreshProcess.executeScheduledRange,
        TimedRefreshProcess.executeFixedRange, Kernel.comp_apply,
        process.scheduledCoordinateStep_fixed]
      rw [← Measure.deterministic_comp_eq_map hembed,
        Measure.comp_assoc, Kernel.comp_deterministic_eq_comap]
      have houter : Kernel.comap
          (process.executeScheduledRange (start + 1) count)
          (fun next => (next, schedule)) hembed =
          (process.executeFixedRange schedule (start + 1) count).map
            (fun next => (next, schedule)) := by
        ext next
        rw [Kernel.comap_apply, Kernel.map_apply _ hembed]
        exact congrArg (fun measure => measure ‹_›) (ih (start + 1) next)
      rw [houter, ← Measure.map_comp _ _ hembed]
      congr 1

/-- Evolve through the horizon remaining after the scheduled waits. -/
noncomputable def TimedRefreshProcess.scheduledResidual
    (process : TimedRefreshProcess State) (horizon : NNReal) (count : ℕ) :
    Kernel (ScheduledState State) State :=
  Kernel.comap process.evolve
    (fun p => (p.1, horizon - scheduleElapsed count p.2))
    (measurable_fst.prodMk
      (measurable_const.sub
        ((measurable_scheduleElapsed count).comp measurable_snd)))

instance TimedRefreshProcess.scheduledResidual.instIsMarkovKernel
    (process : TimedRefreshProcess State) (horizon : NNReal) (count : ℕ) :
    IsMarkovKernel (process.scheduledResidual horizon count) := by
  unfold TimedRefreshProcess.scheduledResidual
  infer_instance

/-- Residual timed transition after fixing the padded schedule. -/
noncomputable def TimedRefreshProcess.fixedResidual
    (process : TimedRefreshProcess State) (horizon : NNReal)
    (schedule : CandidateScheduleSample) : Kernel State State :=
  process.section (horizon - scheduleElapsed schedule.1 schedule)

instance TimedRefreshProcess.fixedResidual.instIsMarkovKernel
    (process : TimedRefreshProcess State) (horizon : NNReal)
    (schedule : CandidateScheduleSample) :
    IsMarkovKernel (process.fixedResidual horizon schedule) := by
  unfold TimedRefreshProcess.fixedResidual
  infer_instance

/-- The bridge coordinate of a concatenated schedule exactly combines the
first residual evolution with the first evolution-and-refresh step of the
second schedule. -/
theorem TimedRefreshProcess.fixedCoordinateStep_concatenate_bridge
    (process : TimedRefreshProcess State) (hsemigroup : process.HasSemigroup)
    (firstHorizon : NNReal) (firstCount secondCount : ℕ)
    (first second : CandidateScheduleSample) (hsecond : 0 < secondCount)
    (hfirstCount : first.1 = firstCount) :
    process.fixedCoordinateStep
      (concatenateRefreshSchedules firstHorizon firstCount secondCount
        (first, second)) firstCount =
      process.fixedCoordinateStep second 0 ∘ₖ
        process.fixedResidual firstHorizon first := by
  unfold TimedRefreshProcess.fixedCoordinateStep
    TimedRefreshProcess.fixedResidual
  rw [hfirstCount]
  rw [concatenateRefreshSchedules_bridge _ _ _ _ _ hsecond,
    Kernel.comp_assoc, hsemigroup]

/-- Execute a fixed count of scheduled refreshes and the residual evolution. -/
noncomputable def TimedRefreshProcess.executeScheduledCount
    (process : TimedRefreshProcess State) (horizon : NNReal) (count : ℕ) :
    Kernel (ScheduledState State) State :=
  process.scheduledResidual horizon count ∘ₖ
    process.executeScheduledRange 0 count

instance TimedRefreshProcess.executeScheduledCount.instIsMarkovKernel
    (process : TimedRefreshProcess State) (horizon : NNReal) (count : ℕ) :
    IsMarkovKernel (process.executeScheduledCount horizon count) := by
  unfold TimedRefreshProcess.executeScheduledCount
  infer_instance

/-- State-only section of the executor at one fixed padded schedule. -/
noncomputable def TimedRefreshProcess.executeFixedCount
    (process : TimedRefreshProcess State) (horizon : NNReal)
    (schedule : CandidateScheduleSample) : Kernel State State :=
  process.fixedResidual horizon schedule ∘ₖ
    process.executeFixedRange schedule 0 schedule.1

instance TimedRefreshProcess.executeFixedCount.instIsMarkovKernel
    (process : TimedRefreshProcess State) (horizon : NNReal)
    (schedule : CandidateScheduleSample) :
    IsMarkovKernel (process.executeFixedCount horizon schedule) := by
  unfold TimedRefreshProcess.executeFixedCount
  infer_instance

/-- A one-refresh padded schedule is exactly “evolve to the refresh time,
refresh, then evolve through the residual horizon.” -/
theorem TimedRefreshProcess.executeFixedCount_one
    (process : TimedRefreshProcess State) (horizon : NNReal)
    (waits : ℕ → NNReal) :
    process.executeFixedCount horizon (1, waits) =
      process.section (horizon - waits 0) ∘ₖ process.refresh ∘ₖ
        process.section (waits 0) := by
  simp [TimedRefreshProcess.executeFixedCount,
    TimedRefreshProcess.fixedResidual, TimedRefreshProcess.executeFixedRange,
    TimedRefreshProcess.fixedCoordinateStep, scheduleElapsed,
    Kernel.comp_assoc]

/-- A two-refresh schedule exposes the phase-space minorization structure:
the first refreshed velocity can randomize the reached position, while the
second independently randomizes the terminal velocity. -/
theorem TimedRefreshProcess.executeFixedCount_two
    (process : TimedRefreshProcess State) (horizon : NNReal)
    (waits : ℕ → NNReal) :
    process.executeFixedCount horizon (2, waits) =
      process.section (horizon - (waits 0 + waits 1)) ∘ₖ process.refresh ∘ₖ
        process.section (waits 1) ∘ₖ process.refresh ∘ₖ
          process.section (waits 0) := by
  simp [TimedRefreshProcess.executeFixedCount,
    TimedRefreshProcess.fixedResidual, TimedRefreshProcess.executeFixedRange,
    TimedRefreshProcess.fixedCoordinateStep, scheduleElapsed,
    Finset.sum_range_succ, Kernel.comp_assoc]

theorem TimedRefreshProcess.executeScheduledCount_apply_fixed
    (process : TimedRefreshProcess State) (horizon : NNReal)
    (schedule : CandidateScheduleSample) (state : State) :
    process.executeScheduledCount horizon schedule.1 (state, schedule) =
      process.executeFixedCount horizon schedule state := by
  unfold TimedRefreshProcess.executeScheduledCount
    TimedRefreshProcess.executeFixedCount
  rw [Kernel.comp_apply,
    process.executeScheduledRange_apply_fixed schedule 0 schedule.1]
  rw [← Measure.deterministic_comp_eq_map (by fun_prop),
    Measure.comp_assoc, Kernel.comp_deterministic_eq_comap]
  congr 1

/-- Concatenating two valid fixed schedules gives exactly sequential execution
across the adjacent horizons. -/
theorem TimedRefreshProcess.executeFixedCount_concatenate
    (process : TimedRefreshProcess State) (hsemigroup : process.HasSemigroup)
    (firstHorizon secondHorizon : NNReal) (firstCount secondCount : ℕ)
    (first second : CandidateScheduleSample)
    (hfirstCount : first.1 = firstCount)
    (hsecondCount : second.1 = secondCount)
    (hfirstValid : scheduleElapsed firstCount first ≤ firstHorizon) :
    process.executeFixedCount (firstHorizon + secondHorizon)
      (concatenateRefreshSchedules firstHorizon firstCount secondCount
        (first, second)) =
      process.executeFixedCount secondHorizon second ∘ₖ
        process.executeFixedCount firstHorizon first := by
  cases secondCount with
  | zero =>
      unfold TimedRefreshProcess.executeFixedCount
      rw [hfirstCount, hsecondCount]
      rw [concatenateRefreshSchedules_fst]
      simp only [Nat.add_zero]
      simp only [TimedRefreshProcess.executeFixedRange]
      rw [process.executeFixedRange_concatenate_first
        firstHorizon firstCount 0 0 firstCount first second (by omega)]
      unfold TimedRefreshProcess.fixedResidual
      simp only [concatenateRefreshSchedules_fst, Nat.add_zero]
      have helapsed := scheduleElapsed_concatenateRefreshSchedules_zero
        firstHorizon firstCount first second
      simp only [Nat.add_zero] at helapsed
      rw [helapsed]
      simp only [hsecondCount, scheduleElapsed, Finset.range_zero,
        Finset.sum_empty, tsub_zero]
      simp only [Kernel.comp_id, hfirstCount]
      rw [← Kernel.comp_assoc, hsemigroup]
      congr 2
      simpa only [scheduleElapsed, add_comm] using
        (add_tsub_assoc_of_le hfirstValid secondHorizon)
  | succ remaining =>
      unfold TimedRefreshProcess.executeFixedCount
      rw [hfirstCount, hsecondCount]
      rw [concatenateRefreshSchedules_fst]
      rw [process.executeFixedRange_add _ 0 firstCount (remaining + 1)]
      rw [process.executeFixedRange_concatenate_first
        firstHorizon firstCount (remaining + 1) 0 firstCount first second
          (by omega)]
      simp only [TimedRefreshProcess.executeFixedRange]
      simp only [zero_add]
      rw [process.executeFixedRange_concatenate_second
        firstHorizon firstCount (remaining + 1) 1 remaining first second
          (by omega) (by omega)]
      rw [process.fixedCoordinateStep_concatenate_bridge hsemigroup
        firstHorizon firstCount (remaining + 1) first second (by omega)
          hfirstCount]
      unfold TimedRefreshProcess.fixedResidual
      simp only [concatenateRefreshSchedules_fst, hfirstCount, hsecondCount]
      rw [scheduleElapsed_concatenateRefreshSchedules_of_pos
        firstHorizon firstCount (remaining + 1) first second (by omega)
          hfirstValid]
      rw [show firstHorizon + secondHorizon -
          (firstHorizon + scheduleElapsed (remaining + 1) second) =
          secondHorizon - scheduleElapsed (remaining + 1) second by
        exact add_tsub_add_eq_tsub_left _ _ _]
      simp only [Kernel.comp_assoc]

private theorem measurableSet_timedRefreshScheduleCount
    (count : ℕ) :
    MeasurableSet {p : ScheduledState State | p.2.1 = count} :=
  (measurable_fst.comp measurable_snd) (MeasurableSet.singleton count)

/-- Mask a fixed-count executor to schedules carrying that count. -/
noncomputable def TimedRefreshProcess.maskedScheduledCount
    (process : TimedRefreshProcess State) (horizon : NNReal) (count : ℕ) :
    Kernel (ScheduledState State) State :=
  Kernel.piecewise (measurableSet_timedRefreshScheduleCount count)
    (process.executeScheduledCount horizon count) 0

/-- Execute the count stored in a padded schedule. -/
noncomputable def TimedRefreshProcess.executeScheduled
    (process : TimedRefreshProcess State) (horizon : NNReal) :
    Kernel (ScheduledState State) State :=
  Kernel.sum fun count : ℕ => process.maskedScheduledCount horizon count

theorem TimedRefreshProcess.executeScheduled_apply
    (process : TimedRefreshProcess State) (horizon : NNReal)
    (input : ScheduledState State) :
    process.executeScheduled horizon input =
      process.executeScheduledCount horizon input.2.1 input := by
  rw [TimedRefreshProcess.executeScheduled, Kernel.sum_apply]
  ext event hevent
  rw [Measure.sum_apply _ hevent, tsum_eq_single input.2.1]
  · simp [TimedRefreshProcess.maskedScheduledCount,
      Kernel.piecewise_apply']
  · intro count hne
    have hne' : input.2.1 ≠ count := Ne.symm hne
    simp [TimedRefreshProcess.maskedScheduledCount,
      Kernel.piecewise_apply', hne']

instance TimedRefreshProcess.executeScheduled.instIsMarkovKernel
    (process : TimedRefreshProcess State) (horizon : NNReal) :
    IsMarkovKernel (process.executeScheduled horizon) := by
  constructor
  intro input
  constructor
  rw [process.executeScheduled_apply horizon input, measure_univ]

/-- Fixing a schedule in the dynamic executor recovers its state-only
execution exactly. -/
theorem TimedRefreshProcess.comap_executeScheduled
    (process : TimedRefreshProcess State) (horizon : NNReal)
    (schedule : CandidateScheduleSample) :
    Kernel.comap (process.executeScheduled horizon)
      (fun state => (state, schedule))
      (measurable_id.prodMk measurable_const) =
        process.executeFixedCount horizon schedule := by
  ext state
  rw [Kernel.comap_apply, process.executeScheduled_apply,
    process.executeScheduledCount_apply_fixed]

/-- Poisson-refresh finite-horizon kernel. The event count is Poisson with
mean `refreshRate * horizon`, conditional event times are ordered uniforms,
and the timed transition fills every inter-refresh interval. -/
noncomputable def TimedRefreshProcess.poissonHorizonKernel
    (process : TimedRefreshProcess State) (refreshRate : NNReal)
    (horizon : PositiveHorizon) : Kernel State State :=
  Mcmc.Kernel.independentParameterMixture
    (process.executeScheduled horizon.duration)
    (poissonCandidateSchedule (refreshRate * horizon.duration) horizon)

instance TimedRefreshProcess.poissonHorizonKernel.instIsMarkovKernel
    (process : TimedRefreshProcess State) (refreshRate : NNReal)
    (horizon : PositiveHorizon) :
    IsMarkovKernel (process.poissonHorizonKernel refreshRate horizon) := by
  unfold TimedRefreshProcess.poissonHorizonKernel
  infer_instance

/-- Conditional horizon kernel given an exact refresh count. The conditional
wait law is the ordered-uniform Poisson schedule at that count. -/
noncomputable def TimedRefreshProcess.countHorizonKernel
    (process : TimedRefreshProcess State) (horizon : PositiveHorizon)
    (count : ℕ) : Kernel State State :=
  Mcmc.Kernel.independentParameterMixture
    (process.executeScheduled horizon.duration)
    (horizon.fixedScheduleMeasure (timestampOrdering count))

instance TimedRefreshProcess.countHorizonKernel.instIsMarkovKernel
    (process : TimedRefreshProcess State) (horizon : PositiveHorizon)
    (count : ℕ) :
    IsMarkovKernel (process.countHorizonKernel horizon count) := by
  unfold TimedRefreshProcess.countHorizonKernel
  infer_instance

/-- A fixed-schedule lower bound that is uniform on a measurable schedule
region integrates to a local minorization of the corresponding conditional
refresh-count kernel. The coefficient records the exact conditional mass of
the selected schedule region. -/
theorem TimedRefreshProcess.countHorizonKernel_locallyMinorizes_on
    (process : TimedRefreshProcess State) (horizon : PositiveHorizon)
    (count : ℕ) (D : Set State) (schedules : Set CandidateScheduleSample)
    (hschedules : MeasurableSet schedules) (floor : ENNReal)
    (reference : Measure State)
    (hminor : ∀ state ∈ D, ∀ schedule ∈ schedules, ∀ event,
      MeasurableSet event →
        floor * reference event ≤
          process.executeFixedCount horizon.duration schedule state event) :
    Mcmc.Kernel.LocallyMinorizes
      (process.countHorizonKernel horizon count) D
      (horizon.fixedScheduleMeasure (timestampOrdering count) schedules *
        floor) reference := by
  unfold TimedRefreshProcess.countHorizonKernel
  apply Mcmc.Kernel.independentParameterMixture_locallyMinorizes_on
    (process.executeScheduled horizon.duration)
    (horizon.fixedScheduleMeasure (timestampOrdering count))
    D schedules hschedules floor reference
  intro state hstate schedule hschedule event hevent
  rw [process.executeScheduled_apply,
    process.executeScheduledCount_apply_fixed]
  exact hminor state hstate schedule hschedule event hevent

/-- Exact decomposition of every transported law by the Poisson number of
refreshes. This retains the zero-refresh and positive-refresh strata needed
by later semigroup and minorization arguments. -/
theorem TimedRefreshProcess.poissonHorizonKernel_comp_eq_sum_count
    (process : TimedRefreshProcess State) (refreshRate : NNReal)
    (horizon : PositiveHorizon) (source : Measure State) [SFinite source] :
    process.poissonHorizonKernel refreshRate horizon ∘ₘ source =
      Measure.sum fun count : ℕ =>
        poissonMeasure (refreshRate * horizon.duration) {count} •
          (process.countHorizonKernel horizon count ∘ₘ source) := by
  unfold TimedRefreshProcess.poissonHorizonKernel
    TimedRefreshProcess.countHorizonKernel poissonCandidateSchedule
    poissonCandidateScheduleMeasure
  exact Mcmc.Kernel.measure_comp_independentParameterMixture_measureSum
    (process.executeScheduled horizon.duration) source
    (fun count : ℕ =>
      poissonMeasure (refreshRate * horizon.duration) {count})
    (fun count : ℕ =>
      horizon.fixedScheduleMeasure (timestampOrdering count))

/-- Every exact refresh-count stratum is a genuine submeasure of the
unconditional refreshed transition. This is the direct bridge from a
fixed-count minorization to the actual Poisson-clock kernel. -/
theorem TimedRefreshProcess.poisson_count_weight_mul_le
    (process : TimedRefreshProcess State) (refreshRate : NNReal)
    (horizon : PositiveHorizon) (count : ℕ) (state : State)
    (event : Set State) (hevent : MeasurableSet event) :
    poissonMeasure (refreshRate * horizon.duration) {count} *
        process.countHorizonKernel horizon count state event ≤
      process.poissonHorizonKernel refreshRate horizon state event := by
  have hdecomp := congrArg (fun measure : Measure State => measure event)
    (process.poissonHorizonKernel_comp_eq_sum_count refreshRate horizon
      (Measure.dirac state))
  rw [Measure.dirac_bind (Kernel.measurable _), Measure.sum_apply _ hevent]
    at hdecomp
  rw [hdecomp]
  simpa only [Measure.smul_apply, smul_eq_mul,
    Measure.dirac_bind (Kernel.measurable _)] using
      (ENNReal.le_tsum count :
        (poissonMeasure (refreshRate * horizon.duration) {count} •
          (process.countHorizonKernel horizon count ∘ₘ Measure.dirac state))
            event ≤
        ∑' n : ℕ,
          (poissonMeasure (refreshRate * horizon.duration) {n} •
            (process.countHorizonKernel horizon n ∘ₘ Measure.dirac state))
              event)

/-- At positive refresh rate, positivity of any fixed-count transition event
lifts to positivity under the genuine Poisson-refresh transition. -/
theorem TimedRefreshProcess.poissonHorizonKernel_pos_of_count
    (process : TimedRefreshProcess State) {refreshRate : NNReal}
    (hrefreshRate : 0 < refreshRate) (horizon : PositiveHorizon)
    (count : ℕ) (state : State) (event : Set State)
    (hevent : MeasurableSet event)
    (hcount : 0 < process.countHorizonKernel horizon count state event) :
    0 < process.poissonHorizonKernel refreshRate horizon state event := by
  apply lt_of_lt_of_le _
    (process.poisson_count_weight_mul_le refreshRate horizon count state event
      hevent)
  apply ENNReal.mul_pos
  · rw [poissonMeasure_singleton]
    apply ENNReal.ofReal_ne_zero_iff.mpr
    have hintensity : 0 < refreshRate * horizon.duration :=
      mul_pos hrefreshRate horizon.positive
    positivity
  · exact hcount.ne'

/-- A uniform minorization proved on one conditional count stratum lifts to
the actual Poisson-refresh kernel, with the exact Poisson singleton factor. -/
theorem TimedRefreshProcess.poissonHorizonKernel_uniformlyMinorizes_of_count
    (process : TimedRefreshProcess State) (refreshRate : NNReal)
    (horizon : PositiveHorizon) (count : ℕ) (ε : ENNReal)
    (reference : Measure State)
    (hminor : Mcmc.Kernel.UniformlyMinorizes
      (process.countHorizonKernel horizon count) ε reference) :
    Mcmc.Kernel.UniformlyMinorizes
      (process.poissonHorizonKernel refreshRate horizon)
      (poissonMeasure (refreshRate * horizon.duration) {count} * ε)
      reference := by
  intro state event hevent
  calc
    (poissonMeasure (refreshRate * horizon.duration) {count} * ε) *
          reference event =
        poissonMeasure (refreshRate * horizon.duration) {count} *
          (ε * reference event) := by ring
    _ ≤ poissonMeasure (refreshRate * horizon.duration) {count} *
          process.countHorizonKernel horizon count state event := by
        gcongr
        exact hminor state event hevent
    _ ≤ process.poissonHorizonKernel refreshRate horizon state event :=
      process.poisson_count_weight_mul_le refreshRate horizon count state
        event hevent

/-- The analogous local bridge retains the same state set. Consequently the
geometric work for refreshed BPS may be carried out entirely on a convenient
fixed-count stratum and then transferred without changing that set. -/
theorem TimedRefreshProcess.poissonHorizonKernel_locallyMinorizes_of_count
    (process : TimedRefreshProcess State) (refreshRate : NNReal)
    (horizon : PositiveHorizon) (count : ℕ) (D : Set State) (ε : ENNReal)
    (reference : Measure State)
    (hminor : Mcmc.Kernel.LocallyMinorizes
      (process.countHorizonKernel horizon count) D ε reference) :
    Mcmc.Kernel.LocallyMinorizes
      (process.poissonHorizonKernel refreshRate horizon) D
      (poissonMeasure (refreshRate * horizon.duration) {count} * ε)
      reference := by
  intro state hstate event hevent
  calc
    (poissonMeasure (refreshRate * horizon.duration) {count} * ε) *
          reference event =
        poissonMeasure (refreshRate * horizon.duration) {count} *
          (ε * reference event) := by ring
    _ ≤ poissonMeasure (refreshRate * horizon.duration) {count} *
          process.countHorizonKernel horizon count state event := by
        gcongr
        exact hminor state hstate event hevent
    _ ≤ process.poissonHorizonKernel refreshRate horizon state event :=
      process.poisson_count_weight_mul_le refreshRate horizon count state
        event hevent

/-- A uniform lower bound on a measurable region of fixed-count schedules
lifts all the way to the genuine Poisson-refresh kernel. The resulting
coefficient exposes both independent losses: conditional schedule-region
mass and the exact Poisson count probability. -/
theorem TimedRefreshProcess.poissonHorizonKernel_locallyMinorizes_on_schedules
    (process : TimedRefreshProcess State) (refreshRate : NNReal)
    (horizon : PositiveHorizon) (count : ℕ) (D : Set State)
    (schedules : Set CandidateScheduleSample)
    (hschedules : MeasurableSet schedules) (floor : ENNReal)
    (reference : Measure State)
    (hminor : ∀ state ∈ D, ∀ schedule ∈ schedules, ∀ event,
      MeasurableSet event →
        floor * reference event ≤
          process.executeFixedCount horizon.duration schedule state event) :
    Mcmc.Kernel.LocallyMinorizes
      (process.poissonHorizonKernel refreshRate horizon) D
      (poissonMeasure (refreshRate * horizon.duration) {count} *
        (horizon.fixedScheduleMeasure (timestampOrdering count) schedules *
          floor)) reference := by
  apply process.poissonHorizonKernel_locallyMinorizes_of_count
    refreshRate horizon count D
    (horizon.fixedScheduleMeasure (timestampOrdering count) schedules * floor)
    reference
  exact process.countHorizonKernel_locallyMinorizes_on
    horizon count D schedules hschedules floor reference hminor

/-- A schedule carrying zero refreshes executes only the residual timed
transition, independently of its unused padding coordinates. -/
theorem TimedRefreshProcess.executeScheduled_zero
    (process : TimedRefreshProcess State) (horizon : NNReal)
    (padding : ℕ → NNReal) (state : State) :
    process.executeScheduled horizon (state, (0, padding)) =
      process.evolve (state, horizon) := by
  rw [process.executeScheduled_apply]
  simp only [TimedRefreshProcess.executeScheduledCount,
    TimedRefreshProcess.executeScheduledRange, Kernel.comp_apply,
    Kernel.id_apply, TimedRefreshProcess.scheduledResidual,
    scheduleElapsed, Finset.range_zero, Finset.sum_empty,
    tsub_zero]
  rw [Measure.dirac_bind (Kernel.measurable _), Kernel.comap_apply]

/-- Every fixed coordinate preserves a common target when both the timed
evolution section and refresh do. -/
theorem TimedRefreshProcess.fixedCoordinateStep_invariant
    (process : TimedRefreshProcess State) (target : Measure State)
    (schedule : CandidateScheduleSample) (index : ℕ)
    (hevolve : ∀ time : NNReal,
      (Kernel.comap process.evolve (fun state => (state, time))
        (measurable_id.prodMk measurable_const)).Invariant target)
    (hrefresh : process.refresh.Invariant target) :
    (process.fixedCoordinateStep schedule index).Invariant target := by
  unfold TimedRefreshProcess.fixedCoordinateStep
  exact hrefresh.comp (hevolve (schedule.2 index))

/-- Every fixed schedule preserves a common target. -/
theorem TimedRefreshProcess.executeFixedCount_invariant
    (process : TimedRefreshProcess State) (target : Measure State)
    (horizon : NNReal) (schedule : CandidateScheduleSample)
    (hevolve : ∀ time : NNReal,
      (Kernel.comap process.evolve (fun state => (state, time))
        (measurable_id.prodMk measurable_const)).Invariant target)
    (hrefresh : process.refresh.Invariant target) :
    (process.executeFixedCount horizon schedule).Invariant target := by
  have hrange : ∀ start count,
      (process.executeFixedRange schedule start count).Invariant target := by
    intro start count
    induction count generalizing start with
    | zero => simp [TimedRefreshProcess.executeFixedRange, Kernel.Invariant]
    | succ count ih =>
        simp only [TimedRefreshProcess.executeFixedRange]
        exact (ih (start + 1)).comp
          (process.fixedCoordinateStep_invariant target schedule start
            hevolve hrefresh)
  unfold TimedRefreshProcess.executeFixedCount
    TimedRefreshProcess.fixedResidual
  exact (hevolve (horizon - scheduleElapsed schedule.1 schedule)).comp
    (hrange 0 schedule.1)

/-- Integrating the Poisson refresh schedule preserves every common invariant
target of the timed evolution and refresh kernel. -/
theorem TimedRefreshProcess.poissonHorizonKernel_invariant
    (process : TimedRefreshProcess State) (target : Measure State)
    [SFinite target] (refreshRate : NNReal) (horizon : PositiveHorizon)
    (hevolve : ∀ time : NNReal,
      (Kernel.comap process.evolve (fun state => (state, time))
        (measurable_id.prodMk measurable_const)).Invariant target)
    (hrefresh : process.refresh.Invariant target) :
    (process.poissonHorizonKernel refreshRate horizon).Invariant target := by
  unfold TimedRefreshProcess.poissonHorizonKernel
  apply Mcmc.Kernel.independentParameterMixture_invariant
  intro schedule
  rw [process.comap_executeScheduled]
  exact process.executeFixedCount_invariant target horizon.duration schedule
    hevolve hrefresh

/-- Independent homogeneous refresh clocks inherit the Chapman--Kolmogorov
law from the timed process. -/
theorem TimedRefreshProcess.poissonHorizonKernel_add
    (process : TimedRefreshProcess State) (hsemigroup : process.HasSemigroup)
    (refreshRate : NNReal) (first second : PositiveHorizon) :
    process.poissonHorizonKernel refreshRate (first.add second) =
      process.poissonHorizonKernel refreshRate second ∘ₖ
        process.poissonHorizonKernel refreshRate first := by
  ext state event hevent
  unfold TimedRefreshProcess.poissonHorizonKernel
    Mcmc.Kernel.independentParameterMixture
  rw [Kernel.comp_apply]
  repeat' rw [Kernel.comp_apply]
  simp only [Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
    Measure.dirac_prod]
  rw [Measure.bind_apply hevent
    (process.executeScheduled (first.add second).duration).aemeasurable]
  rw [Measure.bind_apply hevent
    (process.executeScheduled second.duration ∘ₖ
      (Kernel.id ×ₖ Kernel.const State
        (poissonCandidateSchedule (refreshRate * second.duration) second))).aemeasurable]
  rw [← map_concatenateAdjacent_poissonCandidateSchedule_prod refreshRate
    first second]
  rw [show Measure.map (Prod.mk state)
      (Measure.map (concatenateAdjacentRefreshSchedules first.duration)
        ((poissonCandidateSchedule (refreshRate * first.duration) first).prod
          (poissonCandidateSchedule (refreshRate * second.duration) second))) =
      Measure.map
        (fun schedules =>
          (state, concatenateAdjacentRefreshSchedules first.duration schedules))
        ((poissonCandidateSchedule (refreshRate * first.duration) first).prod
          (poissonCandidateSchedule (refreshRate * second.duration) second)) by
    rw [Measure.map_map (by fun_prop)
      (measurable_concatenateAdjacentRefreshSchedules first.duration)]
    rfl]
  rw [MeasureTheory.lintegral_map
    (Kernel.measurable_coe
      (process.executeScheduled (first.add second).duration) hevent)
    (measurable_const.prodMk
      (measurable_concatenateAdjacentRefreshSchedules first.duration))]
  rw [Measure.lintegral_bind
    (process.executeScheduled first.duration).aemeasurable
    (Kernel.measurable_coe
      (process.executeScheduled second.duration ∘ₖ
        (Kernel.id ×ₖ Kernel.const State
          (poissonCandidateSchedule (refreshRate * second.duration) second)))
      hevent).aemeasurable]
  have hrhsMeas : Measurable (fun input : ScheduledState State =>
      ∫⁻ middle,
        (process.executeScheduled second.duration ∘ₖ
          (Kernel.id ×ₖ Kernel.const State
          (poissonCandidateSchedule (refreshRate * second.duration) second)))
          middle event ∂process.executeScheduled first.duration input) := by
    apply Measurable.lintegral_kernel_prod_right
    exact (Kernel.measurable_coe
        (process.executeScheduled second.duration ∘ₖ
          (Kernel.id ×ₖ Kernel.const State
            (poissonCandidateSchedule (refreshRate * second.duration) second)))
        hevent).comp measurable_snd
  rw [MeasureTheory.lintegral_map hrhsMeas
    (by fun_prop : Measurable (Prod.mk state))]
  have hleftMeas : AEMeasurable
      (fun schedules : CandidateScheduleSample × CandidateScheduleSample =>
        process.executeScheduled (first.add second).duration
          (state, concatenateAdjacentRefreshSchedules first.duration schedules)
          event)
      ((poissonCandidateSchedule (refreshRate * first.duration) first).prod
        (poissonCandidateSchedule (refreshRate * second.duration) second)) := by
    exact ((Kernel.measurable_coe
      (process.executeScheduled (first.add second).duration) hevent).comp
        (measurable_const.prodMk
          (measurable_concatenateAdjacentRefreshSchedules first.duration))).aemeasurable
  rw [MeasureTheory.lintegral_prod _ hleftMeas]
  simp_rw [Kernel.comp_apply, Kernel.prod_apply, Kernel.id_apply,
    Kernel.const_apply, Measure.dirac_prod]
  simp_rw [Measure.bind_apply hevent
    (process.executeScheduled second.duration).aemeasurable]
  have hmapSecond (middle : State) :
      (∫⁻ input : ScheduledState State,
        process.executeScheduled second.duration input event
          ∂Measure.map (Prod.mk middle)
            (poissonCandidateSchedule (refreshRate * second.duration) second)) =
      ∫⁻ secondSchedule,
        process.executeScheduled second.duration (middle, secondSchedule) event
          ∂poissonCandidateSchedule (refreshRate * second.duration) second := by
    rw [MeasureTheory.lintegral_map
      (Kernel.measurable_coe (process.executeScheduled second.duration) hevent)
      (by fun_prop : Measurable (Prod.mk middle))]
  simp_rw [hmapSecond]
  apply lintegral_congr_ae
  filter_upwards [ae_poissonCandidateSchedule_elapsed_le
      (refreshRate * first.duration) first] with firstSchedule hfirstValid
  have hswapMeas : AEMeasurable
      (fun pair : State × CandidateScheduleSample =>
        process.executeScheduled second.duration pair event)
      ((process.executeScheduled first.duration (state, firstSchedule)).prod
        (poissonCandidateSchedule (refreshRate * second.duration) second)) :=
    (Kernel.measurable_coe (process.executeScheduled second.duration) hevent).aemeasurable
  rw [← MeasureTheory.lintegral_prod _ hswapMeas]
  rw [MeasureTheory.lintegral_prod_symm _ hswapMeas]
  apply lintegral_congr
  intro secondSchedule
  simp_rw [process.executeScheduled_apply]
  simp_rw [process.executeScheduledCount_apply_fixed]
  rw [← Measure.bind_apply hevent
    (process.executeFixedCount second.duration secondSchedule).aemeasurable]
  rw [← Kernel.comp_apply]
  rw [PositiveHorizon.add_duration]
  unfold concatenateAdjacentRefreshSchedules
  exact congrArg (fun kernel : Kernel State State => kernel state event)
    (process.executeFixedCount_concatenate hsemigroup first.duration
      second.duration firstSchedule.1 secondSchedule.1 firstSchedule
      secondSchedule rfl rfl hfirstValid)

/-- A positive-time refreshed skeleton iterated `n + 1` times is exactly the
continuous-time transition over `n + 1` adjacent copies of that horizon. -/
theorem TimedRefreshProcess.poissonHorizonKernel_pow_succ
    (process : TimedRefreshProcess State) (hsemigroup : process.HasSemigroup)
    (refreshRate : NNReal) (horizon : PositiveHorizon) (n : ℕ) :
    (process.poissonHorizonKernel refreshRate horizon) ^ (n + 1) =
      process.poissonHorizonKernel refreshRate (horizon.repeatSucc n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih]
      exact (process.poissonHorizonKernel_add hsemigroup refreshRate horizon
        (horizon.repeatSucc n)).symm

end Mcmc.PDMP
