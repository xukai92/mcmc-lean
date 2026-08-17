import Mcmc.PDMP.ScheduledExecutionKernel

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

end Mcmc.PDMP
