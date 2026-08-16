import Mcmc.PDMP.PoissonSchedule
import Mcmc.Kernel.ParameterMixture
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Tactic

/-!
# Integrating scheduled PDMP execution

This module gives the first fully integrated fixed-horizon path-law client: a
single conditional candidate time is sampled from its continuous law, the
process flows to that time, applies bounded thinning, and flows through the
remaining horizon. Keeping the sampled time in the augmented state makes every
step a standard mathlib kernel composition.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace Mcmc.PDMP

variable {State : Type*} [MeasurableSpace State]

/-- Adjacent-count flux certificate for a count mixture. Each transported
count stratum and the corresponding weighted target stratum share a core;
their remaining flux is shifted by one count. The explicit sum identity is
the nonnegative-measure form of cross-count cancellation. -/
structure AdjacentCountFluxBalance
    (weights : ℕ → ENNReal) (target : Measure State)
    (transported : ℕ → Measure State) where
  core : ℕ → Measure State
  flux : ℕ → Measure State
  transported_eq : ∀ count,
    transported count = core count + flux (count + 1)
  target_eq : ∀ count,
    weights count • target = core count + flux count
  flux_shift : Measure.sum (fun count => flux (count + 1)) = Measure.sum flux

/-- The cross-count boundary condition has a simpler client-facing form:
there is no incoming flux below count zero. Reindexing the remaining positive
counts then supplies `flux_shift` automatically. -/
noncomputable def AdjacentCountFluxBalance.of_zeroInitialFlux
    {weights : ℕ → ENNReal} {target : Measure State}
    {transported core flux : ℕ → Measure State}
    (htransported : ∀ count,
      transported count = core count + flux (count + 1))
    (htarget : ∀ count,
      weights count • target = core count + flux count)
    (hflux0 : flux 0 = 0) :
    AdjacentCountFluxBalance weights target transported where
  core := core
  flux := flux
  transported_eq := htransported
  target_eq := htarget
  flux_shift := by
    let positive : ℕ ≃ {n : ℕ // n ∈ ({0} : Set ℕ)ᶜ} :=
      { toFun := fun n => ⟨n + 1, by simp⟩
        invFun := fun n => n.1 - 1
        left_inv := fun n => by simp
        right_inv := fun n => by
          apply Subtype.ext
          have hn : n.1 ≠ 0 := by
            simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using n.2
          exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hn) }
    have hpositive : Measure.sum (fun count => flux (count + 1)) =
        Measure.sum (fun n : {n : ℕ // n ∈ ({0} : Set ℕ)ᶜ} => flux n) := by
      rw [← Measure.sum_comp_equiv positive
        (fun n : {n : ℕ // n ∈ ({0} : Set ℕ)ᶜ} => flux n)]
      rfl
    rw [hpositive]
    have hsplit := Measure.sum_add_sum_compl ({0} : Set ℕ) flux
    have hzero : Measure.sum (fun n : ({0} : Set ℕ) => flux n) = 0 := by
      ext s hs
      rw [Measure.sum_apply _ hs]
      simp [hflux0]
    rw [hzero, zero_add] at hsplit
    exact hsplit

/-- Adjacent-count flux balance turns normalized count weights into exact
mixture invariance. -/
theorem AdjacentCountFluxBalance.sum_transported_eq_target
    {weights : ℕ → ENNReal} {target : Measure State}
    {transported : ℕ → Measure State}
    (balance : AdjacentCountFluxBalance weights target transported)
    (hweights : ∑' count, weights count = 1) :
    Measure.sum transported = target := by
  have htransport : Measure.sum transported =
      Measure.sum balance.core +
        Measure.sum (fun count => balance.flux (count + 1)) := by
    ext s hs
    rw [Measure.sum_apply _ hs, Measure.add_apply,
      Measure.sum_apply _ hs, Measure.sum_apply _ hs]
    simp_rw [balance.transported_eq, Measure.add_apply]
    exact ENNReal.tsum_add
  have htarget : Measure.sum (fun count => weights count • target) =
      Measure.sum balance.core + Measure.sum balance.flux := by
    ext s hs
    rw [Measure.sum_apply _ hs, Measure.add_apply,
      Measure.sum_apply _ hs, Measure.sum_apply _ hs]
    simp_rw [balance.target_eq, Measure.add_apply]
    exact ENNReal.tsum_add
  have hweighted : Measure.sum (fun count => weights count • target) = target := by
    ext s hs
    rw [Measure.sum_apply _ hs]
    simp_rw [Measure.smul_apply, smul_eq_mul]
    rw [ENNReal.tsum_mul_right, hweights, one_mul]
  rw [htransport, balance.flux_shift, ← htarget, hweighted]

/-- Deterministically flow to the timestamp while retaining it. -/
noncomputable def ThinnedFlowSimulator.flowToTimestamp
    (simulator : ThinnedFlowSimulator State) :
    Kernel (State × NNReal) (State × NNReal) :=
  Kernel.deterministic
    (fun p => (simulator.semiflow.flow p.2 p.1, p.2))
    (simulator.semiflow.jointly_measurable_flow.comp
      (measurable_snd.prodMk measurable_fst) |>.prodMk measurable_snd)

instance ThinnedFlowSimulator.flowToTimestamp.instIsMarkovKernel
    (simulator : ThinnedFlowSimulator State) :
    IsMarkovKernel simulator.flowToTimestamp := by
  unfold ThinnedFlowSimulator.flowToTimestamp
  infer_instance

/-- Apply the accepted/virtual event to the state while retaining its
timestamp. -/
noncomputable def ThinnedFlowSimulator.jumpKeepTimestamp
    (simulator : ThinnedFlowSimulator State) :
    Kernel (State × NNReal) (State × NNReal) :=
  Kernel.prod
    (Kernel.prodMkRight NNReal
      (simulator.mechanism.uniformizedKernel simulator.clock.rate))
    (Kernel.deterministic Prod.snd measurable_snd)

instance ThinnedFlowSimulator.jumpKeepTimestamp.instIsMarkovKernel
    (simulator : ThinnedFlowSimulator State) :
    IsMarkovKernel simulator.jumpKeepTimestamp := by
  letI : IsMarkovKernel
      (simulator.mechanism.uniformizedKernel simulator.clock.rate) :=
    simulator.mechanism.uniformizedKernel_isMarkov simulator.clock.rate
      simulator.clock.positive simulator.rate_le_clock
  unfold ThinnedFlowSimulator.jumpKeepTimestamp
  infer_instance

/-- Flow from a retained timestamp through the residual horizon. -/
noncomputable def ThinnedFlowSimulator.flowResidual
    (simulator : ThinnedFlowSimulator State) (horizon : NNReal) :
    Kernel (State × NNReal) State :=
  Kernel.deterministic
    (fun p => simulator.semiflow.flow (horizon - p.2) p.1)
    (simulator.semiflow.jointly_measurable_flow.comp
      ((measurable_const.sub measurable_snd).prodMk measurable_fst))

instance ThinnedFlowSimulator.flowResidual.instIsMarkovKernel
    (simulator : ThinnedFlowSimulator State) (horizon : NNReal) :
    IsMarkovKernel (simulator.flowResidual horizon) := by
  unfold ThinnedFlowSimulator.flowResidual
  infer_instance

/-- Execute one supplied candidate timestamp inside a fixed horizon. -/
noncomputable def ThinnedFlowSimulator.oneTimestampKernel
    (simulator : ThinnedFlowSimulator State) (horizon : NNReal) :
    Kernel (State × NNReal) State :=
  simulator.flowResidual horizon ∘ₖ
    (simulator.jumpKeepTimestamp ∘ₖ simulator.flowToTimestamp)

instance ThinnedFlowSimulator.oneTimestampKernel.instIsMarkovKernel
    (simulator : ThinnedFlowSimulator State) (horizon : NNReal) :
    IsMarkovKernel (simulator.oneTimestampKernel horizon) := by
  unfold ThinnedFlowSimulator.oneTimestampKernel
  infer_instance

/-- Sample one timestamp from an arbitrary probability law and execute its
fixed-horizon flow/thinning path. -/
noncomputable def ThinnedFlowSimulator.oneRandomTimestampKernel
    (simulator : ThinnedFlowSimulator State) (horizon : NNReal)
    (timestampLaw : Measure NNReal) : Kernel State State :=
  simulator.oneTimestampKernel horizon ∘ₖ
    Kernel.prod Kernel.id (Kernel.const State timestampLaw)

instance ThinnedFlowSimulator.oneRandomTimestampKernel.instIsMarkovKernel
    (simulator : ThinnedFlowSimulator State) (horizon : NNReal)
    (timestampLaw : Measure NNReal) [IsProbabilityMeasure timestampLaw] :
    IsMarkovKernel
      (simulator.oneRandomTimestampKernel horizon timestampLaw) := by
  unfold ThinnedFlowSimulator.oneRandomTimestampKernel
  infer_instance

/-- Fully integrated execution conditional on exactly one homogeneous-clock
candidate in a positive horizon. Its timestamp has the standard continuous
uniform conditional law. -/
noncomputable def ThinnedFlowSimulator.oneConditionalCandidateKernel
    (simulator : ThinnedFlowSimulator State) (horizon : PositiveHorizon) :
    Kernel State State :=
  simulator.oneRandomTimestampKernel horizon.duration
    horizon.uniformNNRealTimeMeasure

instance ThinnedFlowSimulator.oneConditionalCandidateKernel.instIsMarkovKernel
    (simulator : ThinnedFlowSimulator State) (horizon : PositiveHorizon) :
    IsMarkovKernel (simulator.oneConditionalCandidateKernel horizon) := by
  unfold ThinnedFlowSimulator.oneConditionalCandidateKernel
  infer_instance

/-- State augmented with a finite-count padded candidate schedule. -/
abbrev ScheduledState (State : Type*) := State × CandidateScheduleSample

/-- Flow by candidate wait coordinate `index`, retaining the whole schedule. -/
noncomputable def ThinnedFlowSimulator.flowScheduledCoordinate
    (simulator : ThinnedFlowSimulator State) (index : ℕ) :
    Kernel (ScheduledState State) (ScheduledState State) :=
  Kernel.deterministic
    (fun p => (simulator.semiflow.flow (p.2.2 index) p.1, p.2))
    (by
      have htime : Measurable (fun p : ScheduledState State => p.2.2 index) :=
        (measurable_pi_apply index).comp (measurable_snd.comp measurable_snd)
      exact (simulator.semiflow.jointly_measurable_flow.comp
        (htime.prodMk measurable_fst)).prodMk measurable_snd)

instance ThinnedFlowSimulator.flowScheduledCoordinate.instIsMarkovKernel
    (simulator : ThinnedFlowSimulator State) (index : ℕ) :
    IsMarkovKernel (simulator.flowScheduledCoordinate index) := by
  unfold ThinnedFlowSimulator.flowScheduledCoordinate
  infer_instance

/-- Apply thinning to the state while retaining the whole schedule. -/
noncomputable def ThinnedFlowSimulator.jumpKeepSchedule
    (simulator : ThinnedFlowSimulator State) :
    Kernel (ScheduledState State) (ScheduledState State) :=
  Kernel.prod
    (Kernel.prodMkRight CandidateScheduleSample
      (simulator.mechanism.uniformizedKernel simulator.clock.rate))
    (Kernel.deterministic Prod.snd measurable_snd)

instance ThinnedFlowSimulator.jumpKeepSchedule.instIsMarkovKernel
    (simulator : ThinnedFlowSimulator State) :
    IsMarkovKernel simulator.jumpKeepSchedule := by
  letI : IsMarkovKernel
      (simulator.mechanism.uniformizedKernel simulator.clock.rate) :=
    simulator.mechanism.uniformizedKernel_isMarkov simulator.clock.rate
      simulator.clock.positive simulator.rate_le_clock
  unfold ThinnedFlowSimulator.jumpKeepSchedule
  infer_instance

/-- One scheduled candidate coordinate: flow, then accept or reject the
candidate, retaining the remaining schedule. -/
noncomputable def ThinnedFlowSimulator.scheduledCoordinateStep
    (simulator : ThinnedFlowSimulator State) (index : ℕ) :
    Kernel (ScheduledState State) (ScheduledState State) :=
  simulator.jumpKeepSchedule ∘ₖ simulator.flowScheduledCoordinate index

instance ThinnedFlowSimulator.scheduledCoordinateStep.instIsMarkovKernel
    (simulator : ThinnedFlowSimulator State) (index : ℕ) :
    IsMarkovKernel (simulator.scheduledCoordinateStep index) := by
  unfold ThinnedFlowSimulator.scheduledCoordinateStep
  infer_instance

/-- Execute `count` schedule coordinates beginning at `start`. -/
noncomputable def ThinnedFlowSimulator.executeScheduledRange
    (simulator : ThinnedFlowSimulator State) :
    ℕ → ℕ → Kernel (ScheduledState State) (ScheduledState State)
  | _, 0 => Kernel.id
  | start, count + 1 =>
      simulator.executeScheduledRange (start + 1) count ∘ₖ
        simulator.scheduledCoordinateStep start

instance ThinnedFlowSimulator.executeScheduledRange.instIsMarkovKernel
    (simulator : ThinnedFlowSimulator State) (start count : ℕ) :
    IsMarkovKernel (simulator.executeScheduledRange start count) := by
  induction count generalizing start with
  | zero =>
      simp only [ThinnedFlowSimulator.executeScheduledRange]
      infer_instance
  | succ count ih =>
      simp only [ThinnedFlowSimulator.executeScheduledRange]
      letI : IsMarkovKernel
          (simulator.executeScheduledRange (start + 1) count) := ih (start + 1)
      infer_instance

/-- Total elapsed time represented by the first `count` wait coordinates. -/
def scheduleElapsed (count : ℕ) (schedule : CandidateScheduleSample) : NNReal :=
  ∑ index ∈ Finset.range count, schedule.2 index

theorem measurable_scheduleElapsed (count : ℕ) :
    Measurable (scheduleElapsed count) := by
  unfold scheduleElapsed
  fun_prop

/-- After all scheduled candidates, flow through the residual horizon. -/
noncomputable def ThinnedFlowSimulator.flowScheduledResidual
    (simulator : ThinnedFlowSimulator State) (horizon : NNReal)
    (count : ℕ) : Kernel (ScheduledState State) State :=
  Kernel.deterministic
    (fun p => simulator.semiflow.flow
      (horizon - scheduleElapsed count p.2) p.1)
    (simulator.semiflow.jointly_measurable_flow.comp
      ((measurable_const.sub
        ((measurable_scheduleElapsed count).comp measurable_snd)).prodMk
          measurable_fst))

instance ThinnedFlowSimulator.flowScheduledResidual.instIsMarkovKernel
    (simulator : ThinnedFlowSimulator State) (horizon : NNReal)
    (count : ℕ) :
    IsMarkovKernel (simulator.flowScheduledResidual horizon count) := by
  unfold ThinnedFlowSimulator.flowScheduledResidual
  infer_instance

/-- Execute exactly `count` scheduled candidates and then the residual flow. -/
noncomputable def ThinnedFlowSimulator.executeScheduledCount
    (simulator : ThinnedFlowSimulator State) (horizon : NNReal)
    (count : ℕ) : Kernel (ScheduledState State) State :=
  simulator.flowScheduledResidual horizon count ∘ₖ
    simulator.executeScheduledRange 0 count

instance ThinnedFlowSimulator.executeScheduledCount.instIsMarkovKernel
    (simulator : ThinnedFlowSimulator State) (horizon : NNReal)
    (count : ℕ) :
    IsMarkovKernel (simulator.executeScheduledCount horizon count) := by
  unfold ThinnedFlowSimulator.executeScheduledCount
  infer_instance

private theorem measurableSet_scheduleCount
    (count : ℕ) :
    MeasurableSet {p : ScheduledState State | p.2.1 = count} :=
  (measurable_fst.comp measurable_snd) (MeasurableSet.singleton count)

/-- Mask a fixed-count executor to augmented inputs carrying that count. -/
noncomputable def ThinnedFlowSimulator.maskedScheduledCount
    (simulator : ThinnedFlowSimulator State) (horizon : NNReal)
    (count : ℕ) : Kernel (ScheduledState State) State :=
  Kernel.piecewise (measurableSet_scheduleCount count)
    (simulator.executeScheduledCount horizon count) 0

/-- Execute the runtime count stored in a padded schedule. Exactly one summand
is active at every input. -/
noncomputable def ThinnedFlowSimulator.executeScheduled
    (simulator : ThinnedFlowSimulator State) (horizon : NNReal) :
    Kernel (ScheduledState State) State :=
  Kernel.sum fun count : ℕ => simulator.maskedScheduledCount horizon count

theorem ThinnedFlowSimulator.executeScheduled_apply
    (simulator : ThinnedFlowSimulator State) (horizon : NNReal)
    (input : ScheduledState State) :
    simulator.executeScheduled horizon input =
      simulator.executeScheduledCount horizon input.2.1 input := by
  rw [ThinnedFlowSimulator.executeScheduled, Kernel.sum_apply]
  ext s hs
  rw [Measure.sum_apply _ hs, tsum_eq_single input.2.1]
  · simp [ThinnedFlowSimulator.maskedScheduledCount,
      Kernel.piecewise_apply']
  · intro count hne
    have hne' : input.2.1 ≠ count := Ne.symm hne
    simp [ThinnedFlowSimulator.maskedScheduledCount,
      Kernel.piecewise_apply', hne']

instance ThinnedFlowSimulator.executeScheduled.instIsMarkovKernel
    (simulator : ThinnedFlowSimulator State) (horizon : NNReal) :
    IsMarkovKernel (simulator.executeScheduled horizon) := by
  constructor
  intro input
  constructor
  rw [simulator.executeScheduled_apply horizon input, measure_univ]

/-- Full bounded-rate fixed-horizon PDMP transition. It samples the exact
Poisson candidate count and conditional ordered times, executes every thinned
candidate in chronological order, and fills the residual horizon by flow. -/
noncomputable def ThinnedFlowSimulator.horizonKernel
    (simulator : ThinnedFlowSimulator State) (horizon : PositiveHorizon) :
    Kernel State State :=
  simulator.executeScheduled horizon.duration ∘ₖ
    Kernel.prod Kernel.id
      (Kernel.const State (poissonCandidateSchedule
        (simulator.clock.rate * horizon.duration) horizon))

instance ThinnedFlowSimulator.horizonKernel.instIsMarkovKernel
    (simulator : ThinnedFlowSimulator State) (horizon : PositiveHorizon) :
    IsMarkovKernel (simulator.horizonKernel horizon) := by
  unfold ThinnedFlowSimulator.horizonKernel
  infer_instance

/-- The horizon kernel is exactly an independent mixture of its fixed-schedule
sections. -/
theorem ThinnedFlowSimulator.horizonKernel_eq_independentParameterMixture
    (simulator : ThinnedFlowSimulator State) (horizon : PositiveHorizon) :
    simulator.horizonKernel horizon =
      Mcmc.Kernel.independentParameterMixture
        (simulator.executeScheduled horizon.duration)
        (poissonCandidateSchedule
          (simulator.clock.rate * horizon.duration) horizon) := rfl

/-- A fixed-horizon sampler is target invariant whenever every deterministic
schedule section of its executor is target invariant. -/
theorem ThinnedFlowSimulator.horizonKernel_invariant_of_sections
    (simulator : ThinnedFlowSimulator State) (horizon : PositiveHorizon)
    (target : Measure State) [SFinite target]
    (hsection : ∀ schedule : CandidateScheduleSample,
      (Kernel.comap (simulator.executeScheduled horizon.duration)
        (fun state => (state, schedule))
        (measurable_id.prodMk measurable_const)).Invariant target) :
    (simulator.horizonKernel horizon).Invariant target := by
  rw [simulator.horizonKernel_eq_independentParameterMixture horizon]
  exact Mcmc.Kernel.independentParameterMixture_invariant
    (simulator.executeScheduled horizon.duration) target
    (poissonCandidateSchedule
      (simulator.clock.rate * horizon.duration) horizon) hsection

/-- For a continuously distributed Poisson schedule it is enough that fixed
schedule sections preserve the target almost everywhere. -/
theorem ThinnedFlowSimulator.horizonKernel_invariant_of_ae_sections
    (simulator : ThinnedFlowSimulator State) (horizon : PositiveHorizon)
    (target : Measure State) [SFinite target]
    (hsection : ∀ᵐ schedule ∂(poissonCandidateSchedule
        (simulator.clock.rate * horizon.duration) horizon),
      (Kernel.comap (simulator.executeScheduled horizon.duration)
        (fun state => (state, schedule))
        (measurable_id.prodMk measurable_const)).Invariant target) :
    (simulator.horizonKernel horizon).Invariant target := by
  rw [simulator.horizonKernel_eq_independentParameterMixture horizon]
  exact Mcmc.Kernel.independentParameterMixture_invariant_ae
    (simulator.executeScheduled horizon.duration) target
    (poissonCandidateSchedule
      (simulator.clock.rate * horizon.duration) horizon) hsection

/-- A sufficient count-conditional stationarity criterion. Unlike fixed
schedule invariance, it permits continuous averaging over ordered event times.
For transport PDMPs this can still be too strong (the zero-event component is
pure flow), so the exact cross-count decomposition below is the general route. -/
theorem ThinnedFlowSimulator.horizonKernel_invariant_of_count_mixtures
    (simulator : ThinnedFlowSimulator State) (horizon : PositiveHorizon)
    (target : Measure State) [SFinite target]
    (hcount : ∀ count : ℕ,
      (Mcmc.Kernel.independentParameterMixture
        (simulator.executeScheduled horizon.duration)
        (horizon.fixedScheduleMeasure (timestampOrdering count))).Invariant
          target) :
    (simulator.horizonKernel horizon).Invariant target := by
  rw [simulator.horizonKernel_eq_independentParameterMixture horizon]
  unfold poissonCandidateSchedule poissonCandidateScheduleMeasure
  exact Mcmc.Kernel.independentParameterMixture_measureSum_invariant
    (simulator.executeScheduled horizon.duration) target
    (fun count : ℕ => poissonMeasure
      (simulator.clock.rate * horizon.duration) {count})
    (fun count : ℕ =>
      horizon.fixedScheduleMeasure (timestampOrdering count))
    (tsum_poisson_singletons
      (simulator.clock.rate * horizon.duration)) hcount

/-- Exact decomposition of the transported state law by Poisson candidate
count. This is the correct interface for a generator proof: individual count
components need not preserve the target, and cancellation may occur between
adjacent event-count strata in their weighted sum. -/
theorem ThinnedFlowSimulator.horizonKernel_comp_eq_sum_count_mixtures
    (simulator : ThinnedFlowSimulator State) (horizon : PositiveHorizon)
    (source : Measure State) [SFinite source] :
    simulator.horizonKernel horizon ∘ₘ source =
      Measure.sum fun count : ℕ =>
        poissonMeasure (simulator.clock.rate * horizon.duration) {count} •
          (Mcmc.Kernel.independentParameterMixture
            (simulator.executeScheduled horizon.duration)
            (horizon.fixedScheduleMeasure (timestampOrdering count)) ∘ₘ
              source) := by
  rw [simulator.horizonKernel_eq_independentParameterMixture horizon]
  unfold poissonCandidateSchedule poissonCandidateScheduleMeasure
  exact Mcmc.Kernel.measure_comp_independentParameterMixture_measureSum
    (simulator.executeScheduled horizon.duration) source
    (fun count : ℕ => poissonMeasure
      (simulator.clock.rate * horizon.duration) {count})
    (fun count : ℕ =>
      horizon.fixedScheduleMeasure (timestampOrdering count))

/-- Weighted transported target measure in one Poisson count stratum. -/
noncomputable def ThinnedFlowSimulator.countTransportedTarget
    (simulator : ThinnedFlowSimulator State) (horizon : PositiveHorizon)
    (target : Measure State) (count : ℕ) : Measure State :=
  poissonMeasure (simulator.clock.rate * horizon.duration) {count} •
    (Mcmc.Kernel.independentParameterMixture
      (simulator.executeScheduled horizon.duration)
      (horizon.fixedScheduleMeasure (timestampOrdering count)) ∘ₘ target)

/-- Cross-count flux cancellation is sufficient for exact fixed-horizon PDMP
stationarity. Unlike countwise stationarity, this permits the zero-event flow
stratum to exchange mass with adjacent event-count strata. -/
theorem ThinnedFlowSimulator.horizonKernel_invariant_of_adjacentCountFlux
    (simulator : ThinnedFlowSimulator State) (horizon : PositiveHorizon)
    (target : Measure State) [SFinite target]
    (balance : AdjacentCountFluxBalance
      (fun count => poissonMeasure
        (simulator.clock.rate * horizon.duration) {count})
      target (simulator.countTransportedTarget horizon target)) :
    (simulator.horizonKernel horizon).Invariant target := by
  rw [ProbabilityTheory.Kernel.Invariant]
  rw [simulator.horizonKernel_comp_eq_sum_count_mixtures horizon target]
  exact balance.sum_transported_eq_target
    (tsum_poisson_singletons
      (simulator.clock.rate * horizon.duration))

/-- Client-facing form of cross-count invariance. A concrete spatial-flux
calculation only needs to split each transported and target count stratum and
show that the incoming count-zero boundary flux vanishes; the infinite
reindexing is discharged here. -/
theorem ThinnedFlowSimulator.horizonKernel_invariant_of_zeroInitialAdjacentFlux
    (simulator : ThinnedFlowSimulator State) (horizon : PositiveHorizon)
    (target : Measure State) [SFinite target]
    (core flux : ℕ → Measure State)
    (htransported : ∀ count,
      simulator.countTransportedTarget horizon target count =
        core count + flux (count + 1))
    (htarget : ∀ count,
      poissonMeasure (simulator.clock.rate * horizon.duration) {count} •
        target = core count + flux count)
    (hflux0 : flux 0 = 0) :
    (simulator.horizonKernel horizon).Invariant target := by
  apply simulator.horizonKernel_invariant_of_adjacentCountFlux horizon target
  exact AdjacentCountFluxBalance.of_zeroInitialFlux
    htransported htarget hflux0

/-- It suffices to prove invariance of the executor selected by each schedule's
stored count. -/
theorem ThinnedFlowSimulator.horizonKernel_invariant_of_count_sections
    (simulator : ThinnedFlowSimulator State) (horizon : PositiveHorizon)
    (target : Measure State) [SFinite target]
    (hsection : ∀ schedule : CandidateScheduleSample,
      (Kernel.comap
        (simulator.executeScheduledCount horizon.duration schedule.1)
        (fun state => (state, schedule))
        (measurable_id.prodMk measurable_const)).Invariant target) :
    (simulator.horizonKernel horizon).Invariant target := by
  apply simulator.horizonKernel_invariant_of_sections horizon target
  intro schedule
  have heq : Kernel.comap (simulator.executeScheduled horizon.duration)
      (fun state => (state, schedule))
      (measurable_id.prodMk measurable_const) =
      Kernel.comap
        (simulator.executeScheduledCount horizon.duration schedule.1)
        (fun state => (state, schedule))
        (measurable_id.prodMk measurable_const) := by
    ext state s hs
    simp only [Kernel.comap_apply]
    rw [simulator.executeScheduled_apply horizon.duration (state, schedule)]
  rw [heq]
  exact hsection schedule

end Mcmc.PDMP
