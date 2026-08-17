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
    Kernel.comap process.evolve (fun state => (state, schedule.2 index))
      (measurable_id.prodMk measurable_const)

instance TimedRefreshProcess.fixedCoordinateStep.instIsMarkovKernel
    (process : TimedRefreshProcess State)
    (schedule : CandidateScheduleSample) (index : ℕ) :
    IsMarkovKernel (process.fixedCoordinateStep schedule index) := by
  unfold TimedRefreshProcess.fixedCoordinateStep
  infer_instance

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
  Kernel.comap process.evolve
    (fun state =>
      (state, horizon - scheduleElapsed schedule.1 schedule))
    (measurable_id.prodMk measurable_const)

instance TimedRefreshProcess.fixedResidual.instIsMarkovKernel
    (process : TimedRefreshProcess State) (horizon : NNReal)
    (schedule : CandidateScheduleSample) :
    IsMarkovKernel (process.fixedResidual horizon schedule) := by
  unfold TimedRefreshProcess.fixedResidual
  infer_instance

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
