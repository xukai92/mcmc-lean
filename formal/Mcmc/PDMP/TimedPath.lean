import Mcmc.PDMP.Path
import Mcmc.Finite.MeasureKernel
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Tactic

/-!
# Finite paths with continuous event times

The Poissonized finite-state construction first samples a finite state
skeleton.  This module supplies the next deterministic layer: an ordered
finite schedule of real event times and the associated right-value step path.
The active state is indexed by the number of events whose timestamps have
occurred.

This constructs exact continuous-time path evaluation for every finite event
schedule and the product law of independent exponential waits. Combining the
Poisson event count, skeleton law, and waiting-time law into one path-space
measure is a separate subsequent layer.
-/

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace Mcmc.PDMP

/-- An ordered schedule of `n` nonnegative real event times. Equal timestamps
are allowed; all simultaneous events take effect at that time. -/
structure EventSchedule (n : ℕ) where
  time : Fin n → ℝ
  nonneg : ∀ i, 0 ≤ time i
  monotone : Monotone time

/-- Strictly positive inter-event waiting times. Independent exponential
draws are the probabilistic instance used by a homogeneous event clock. -/
structure WaitingTimes (n : ℕ) where
  wait : Fin n → ℝ
  positive : ∀ i, 0 < wait i

/-- Cumulative event time obtained by summing all waits through index `i`. -/
def WaitingTimes.cumulativeTime (waits : WaitingTimes n) (i : Fin n) : ℝ :=
  ∑ j, if j ≤ i then waits.wait j else 0

/-- Positive waits produce an ordered nonnegative event schedule. -/
def WaitingTimes.toEventSchedule (waits : WaitingTimes n) : EventSchedule n where
  time := waits.cumulativeTime
  nonneg i := Finset.sum_nonneg fun j _ => by
    split_ifs
    · exact (waits.positive j).le
    · exact le_rfl
  monotone := by
    intro i k hik
    unfold WaitingTimes.cumulativeTime
    apply Finset.sum_le_sum
    intro j _
    by_cases hji : j ≤ i
    · rw [if_pos hji, if_pos (hji.trans hik)]
    · rw [if_neg hji]
      split_ifs
      · exact (waits.positive j).le
      · exact le_rfl

/-- Every cumulative event time from positive waits is strictly positive. -/
theorem WaitingTimes.cumulativeTime_pos (waits : WaitingTimes n) (i : Fin n) :
    0 < waits.cumulativeTime i := by
  unfold WaitingTimes.cumulativeTime
  apply Finset.sum_pos'
  · intro j _
    by_cases hji : j ≤ i
    · simp [hji, (waits.positive j).le]
    · simp [hji]
  · exact ⟨i, Finset.mem_univ i, by simp [waits.positive i]⟩

/-- Product law of independent rate-`rate` exponential waiting times for a
fixed finite event count. -/
noncomputable def exponentialWaitingMeasure (rate : ℝ) (n : ℕ) :
    Measure (Fin n → ℝ) :=
  Measure.pi fun _ => expMeasure rate

/-- Positive-rate independent exponential waits form a probability law. -/
theorem exponentialWaitingMeasure_isProbability (rate : ℝ) (n : ℕ)
    (hrate : 0 < rate) :
    IsProbabilityMeasure (exponentialWaitingMeasure rate n) := by
  letI (i : Fin n) : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hrate
  unfold exponentialWaitingMeasure
  infer_instance

/-- State skeleton and real waiting-time vector at one fixed event count. -/
abbrev FixedTimedPathSample (State : Type*) (n : ℕ) :=
  List.Vector State (n + 1) × (Fin n → ℝ)

/-- Joint law of a finite Markov skeleton and independent exponential waits,
conditional on a fixed number of clock events. -/
noncomputable def fixedTimedPathMeasure
    {State : Type*} {n : ℕ} [Fintype State] [DecidableEq State]
    [MeasurableSpace (List.Vector State (n + 1))]
    (transition : Mcmc.Finite.MarkovKernel State) (initial : State)
    (rate : ℝ) : Measure (FixedTimedPathSample State n) :=
  (Mcmc.Finite.MarkovKernel.Distribution.toMeasure
    (eventPathLaw transition initial n)).prod
      (exponentialWaitingMeasure rate n)

/-- The fixed-count timed path law is a probability measure. -/
theorem fixedTimedPathMeasure_isProbability
    {State : Type*} {n : ℕ} [Fintype State] [DecidableEq State]
    [MeasurableSpace (List.Vector State (n + 1))]
    (transition : Mcmc.Finite.MarkovKernel State) (initial : State)
    (rate : ℝ) (hrate : 0 < rate) :
    IsProbabilityMeasure
      (fixedTimedPathMeasure (n := n) transition initial rate) := by
  letI : IsProbabilityMeasure (exponentialWaitingMeasure rate n) :=
    exponentialWaitingMeasure_isProbability rate n hrate
  unfold fixedTimedPathMeasure
  infer_instance

/-- Adding independent event times leaves the finite state-skeleton law
unchanged. -/
theorem fixedTimedPathMeasure_map_fst
    {State : Type*} {n : ℕ} [Fintype State] [DecidableEq State]
    [MeasurableSpace (List.Vector State (n + 1))]
    (transition : Mcmc.Finite.MarkovKernel State) (initial : State)
    (rate : ℝ) (hrate : 0 < rate) :
    Measure.map Prod.fst
        (fixedTimedPathMeasure (n := n) transition initial rate) =
      Mcmc.Finite.MarkovKernel.Distribution.toMeasure
        (eventPathLaw transition initial n) := by
  letI : IsProbabilityMeasure (exponentialWaitingMeasure rate n) :=
    exponentialWaitingMeasure_isProbability rate n hrate
  unfold fixedTimedPathMeasure
  simp

/-- The waiting-time marginal of the fixed-count joint law is the independent
exponential product law. -/
theorem fixedTimedPathMeasure_map_snd
    {State : Type*} {n : ℕ} [Fintype State] [DecidableEq State]
    [MeasurableSpace (List.Vector State (n + 1))]
    (transition : Mcmc.Finite.MarkovKernel State) (initial : State)
    (rate : ℝ) (hrate : 0 < rate) :
    Measure.map Prod.snd
        (fixedTimedPathMeasure (n := n) transition initial rate) =
      exponentialWaitingMeasure rate n := by
  letI : IsProbabilityMeasure (exponentialWaitingMeasure rate n) :=
    exponentialWaitingMeasure_isProbability rate n hrate
  unfold fixedTimedPathMeasure
  simp

/-- Number of scheduled events that have occurred by time `t`. -/
noncomputable def EventSchedule.eventCount (schedule : EventSchedule n) (t : ℝ) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun i => schedule.time i ≤ t).card

/-- The occurred-event count never exceeds the schedule length. -/
theorem EventSchedule.eventCount_le (schedule : EventSchedule n) (t : ℝ) :
    schedule.eventCount t ≤ n := by
  simpa [EventSchedule.eventCount] using
    Finset.card_le_card
      (Finset.filter_subset (fun i : Fin n => schedule.time i ≤ t) Finset.univ)

/-- More elapsed time cannot decrease the event count. -/
theorem EventSchedule.eventCount_mono (schedule : EventSchedule n) :
    Monotone schedule.eventCount := by
  intro t u htu
  unfold EventSchedule.eventCount
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hi.trans htu

/-- A real-time function is locally constant immediately to the right. This
elementary property is stronger than right continuity and avoids imposing a
topology on its codomain. -/
def IsRightLocallyConstant (f : ℝ → α) : Prop :=
  ∀ t, ∃ ε > 0, ∀ u, t ≤ u → u < t + ε → f u = f t

/-- A function has a locally constant value immediately to the left of every
time. For finite-state step paths this is a concrete left-limit interface. -/
def HasLocallyConstantLeftLimits (f : ℝ → α) : Prop :=
  ∀ t, ∃ ε > 0, ∃ limit, ∀ u, t - ε < u → u < t → f u = limit

/-- A finite event-count process is locally constant immediately to the
right, including at event times (where all simultaneous events have already
occurred). -/
theorem EventSchedule.eventCount_rightLocallyConstant
    (schedule : EventSchedule n) :
    IsRightLocallyConstant schedule.eventCount := by
  intro t
  let future := (Finset.univ : Finset (Fin n)).filter fun i =>
    t < schedule.time i
  by_cases hempty : future = ∅
  · refine ⟨1, zero_lt_one, fun u htu hu => ?_⟩
    unfold EventSchedule.eventCount
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hiu
      by_contra hit
      have hfuture : i ∈ future := by
        simp [future, lt_of_not_ge hit]
      simp [hempty] at hfuture
    · exact fun hit => hit.trans htu
  · have hnonempty : future.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨first, hfirst, hminimal⟩ :=
      future.exists_min_image schedule.time hnonempty
    have htfirst : t < schedule.time first := by
      simpa [future] using hfirst
    refine ⟨schedule.time first - t, sub_pos.mpr htfirst,
      fun u htu hu => ?_⟩
    unfold EventSchedule.eventCount
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hiu
      by_contra hit
      have hti : t < schedule.time i := lt_of_not_ge hit
      have hifuture : i ∈ future := by simp [future, hti]
      have hmin := hminimal i hifuture
      have hufirst : u < schedule.time first := by linarith
      linarith
    · exact fun hit => hit.trans htu

/-- A finite event-count process has locally constant left limits. -/
theorem EventSchedule.eventCount_hasLeftLimits
    (schedule : EventSchedule n) :
    HasLocallyConstantLeftLimits schedule.eventCount := by
  intro t
  let past := (Finset.univ : Finset (Fin n)).filter fun i =>
    schedule.time i < t
  let limit := past.card
  by_cases hempty : past = ∅
  · refine ⟨1, zero_lt_one, 0, fun u htu hut => ?_⟩
    unfold EventSchedule.eventCount
    have hnone :
        (Finset.univ.filter fun i : Fin n => schedule.time i ≤ u) = ∅ := by
      ext i
      have hnot : ¬schedule.time i ≤ u := by
        intro hiu
        have hipast : i ∈ past := by simp [past, hiu.trans_lt hut]
        simp [hempty] at hipast
      simp [hnot]
    rw [hnone]
    simp
  · have hnonempty : past.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨last, hlast, hmaximal⟩ :=
      past.exists_max_image schedule.time hnonempty
    have hlastt : schedule.time last < t := by
      simpa [past] using hlast
    refine ⟨t - schedule.time last, sub_pos.mpr hlastt, limit,
      fun u htu hut => ?_⟩
    unfold EventSchedule.eventCount limit
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hiu
      simpa [past] using hiu.trans_lt hut
    · intro hit
      have hipast : i ∈ past := by simp [past, hit]
      have himax := hmaximal i hipast
      have hlastu : schedule.time last < u := by linarith
      exact himax.trans hlastu.le
/-- Before every event time, the occurred-event count is zero. -/
theorem EventSchedule.eventCount_eq_zero_of_before
    (schedule : EventSchedule n) (t : ℝ)
    (hbefore : ∀ i, t < schedule.time i) :
    schedule.eventCount t = 0 := by
  unfold EventSchedule.eventCount
  have hempty :
      (Finset.univ.filter fun i : Fin n => schedule.time i ≤ t) = ∅ := by
    ext i
    simp [not_le.mpr (hbefore i)]
  rw [hempty]
  simp

/-- Once every event time has passed, all scheduled events have occurred. -/
theorem EventSchedule.eventCount_eq_length_of_after
    (schedule : EventSchedule n) (t : ℝ)
    (hafter : ∀ i, schedule.time i ≤ t) :
    schedule.eventCount t = n := by
  unfold EventSchedule.eventCount
  rw [Finset.filter_eq_self.mpr]
  · simp
  · intro i _
    exact hafter i

/-- A finite state skeleton paired with its continuous event schedule. The
state vector includes the initial state and therefore has length `n + 1`. -/
structure TimedEventPath (State : Type*) (n : ℕ) where
  states : List.Vector State (n + 1)
  schedule : EventSchedule n

/-- State active at real time `t`; events at exactly `t` have taken effect. -/
noncomputable def TimedEventPath.valueAt
    (path : TimedEventPath State n) (t : ℝ) : State :=
  path.states.get ⟨path.schedule.eventCount t,
    Nat.lt_succ_iff.mpr (path.schedule.eventCount_le t)⟩

/-- The active state index is monotone in elapsed time. -/
theorem TimedEventPath.activeIndex_mono (path : TimedEventPath State n) :
    Monotone (fun t => path.schedule.eventCount t) :=
  path.schedule.eventCount_mono

/-- Every finite timed path is locally constant immediately to the right. In
particular it is right-continuous for any topology on the finite state space. -/
theorem TimedEventPath.valueAt_rightLocallyConstant
    (path : TimedEventPath State n) :
    IsRightLocallyConstant path.valueAt := by
  intro t
  obtain ⟨ε, hε, hcount⟩ := path.schedule.eventCount_rightLocallyConstant t
  refine ⟨ε, hε, fun u htu hu => ?_⟩
  unfold TimedEventPath.valueAt
  have hindex :
      (⟨path.schedule.eventCount u,
        Nat.lt_succ_iff.mpr (path.schedule.eventCount_le u)⟩ : Fin (n + 1)) =
      ⟨path.schedule.eventCount t,
        Nat.lt_succ_iff.mpr (path.schedule.eventCount_le t)⟩ :=
    Fin.ext (hcount u htu hu)
  exact congrArg path.states.get hindex

/-- Every finite timed path has a locally constant left limit at every real
time. Together with right-local constancy, this is the finite-state càdlàg
property without requiring a separate Skorokhod path-space library. -/
theorem TimedEventPath.valueAt_hasLeftLimits
    (path : TimedEventPath State n) :
    HasLocallyConstantLeftLimits path.valueAt := by
  intro t
  obtain ⟨ε, hε, count, hcount⟩ := path.schedule.eventCount_hasLeftLimits t
  have hcount_le : count ≤ n := by
    obtain ⟨u, htu, hut⟩ : ∃ u, t - ε < u ∧ u < t := by
      refine ⟨t - ε / 2, ?_, ?_⟩ <;> linarith
    rw [← hcount u htu hut]
    exact path.schedule.eventCount_le u
  let limit := path.states.get
    (⟨count, Nat.lt_succ_iff.mpr hcount_le⟩ : Fin (n + 1))
  refine ⟨ε, hε, limit, fun u htu hut => ?_⟩
  unfold TimedEventPath.valueAt limit
  have hindex :
      (⟨path.schedule.eventCount u,
        Nat.lt_succ_iff.mpr (path.schedule.eventCount_le u)⟩ : Fin (n + 1)) =
      ⟨count, Nat.lt_succ_iff.mpr hcount_le⟩ :=
    Fin.ext (hcount u htu hut)
  exact congrArg path.states.get hindex

/-- Before the first event, path evaluation returns the initial state. -/
theorem TimedEventPath.valueAt_eq_initial_of_before
    (path : TimedEventPath State n) (t : ℝ)
    (hbefore : ∀ i, t < path.schedule.time i) :
    path.valueAt t = path.states.get ⟨0, Nat.zero_lt_succ n⟩ := by
  unfold TimedEventPath.valueAt
  have hcount := path.schedule.eventCount_eq_zero_of_before t hbefore
  have hindex :
      (⟨path.schedule.eventCount t,
        Nat.lt_succ_iff.mpr (path.schedule.eventCount_le t)⟩ : Fin (n + 1)) =
        ⟨0, Nat.zero_lt_succ n⟩ := Fin.ext hcount
  exact congrArg path.states.get hindex

/-- After the last event, path evaluation returns the skeleton's terminal
state. -/
theorem TimedEventPath.valueAt_eq_terminal_of_after
    (path : TimedEventPath State n) (t : ℝ)
    (hafter : ∀ i, path.schedule.time i ≤ t) :
    path.valueAt t = path.states.last := by
  unfold TimedEventPath.valueAt
  have hcount := path.schedule.eventCount_eq_length_of_after t hafter
  have hindex :
      (⟨path.schedule.eventCount t,
        Nat.lt_succ_iff.mpr (path.schedule.eventCount_le t)⟩ : Fin (n + 1)) =
        Fin.last n := Fin.ext hcount
  rw [hindex]
  rfl

/-- A zero-event path is constant at its sole state. -/
@[simp] theorem TimedEventPath.valueAt_zero_events
    (path : TimedEventPath State 0) (t : ℝ) :
    path.valueAt t = path.states.last := by
  apply path.valueAt_eq_terminal_of_after
  intro i
  exact Fin.elim0 i

/-- Translate every event time by a nonnegative delay. -/
def EventSchedule.shift (schedule : EventSchedule n) (delay : ℝ)
    (hdelay : 0 ≤ delay) : EventSchedule n where
  time i := schedule.time i + delay
  nonneg i := add_nonneg (schedule.nonneg i) hdelay
  monotone := by
    simpa [add_comm] using schedule.monotone.const_add delay

/-- Translating a schedule translates its event-count process. -/
@[simp] theorem EventSchedule.eventCount_shift (schedule : EventSchedule n)
    (delay : ℝ) (hdelay : 0 ≤ delay) (t : ℝ) :
    (schedule.shift delay hdelay).eventCount (t + delay) =
      schedule.eventCount t := by
  unfold EventSchedule.eventCount EventSchedule.shift
  congr 1
  ext i
  simp

end Mcmc.PDMP
