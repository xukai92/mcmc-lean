import Mcmc.PDMP.Flow
import Mcmc.PDMP.TimedPath
import Mathlib.Tactic

/-!
# Executing finite PDMP event schedules

This module connects finite waiting-time schedules to the general-state PDMP
flow and jump interfaces.  Each waiting time first advances the deterministic
semiflow and then applies the event kernel.  The resulting list executor is a
Markov kernel, composes across concatenated schedules, and preserves any
target preserved by every event segment.

This is conditional fixed-schedule execution.  A state-dependent event-time
simulator and its path-space law remain separate constructions.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory

namespace Mcmc.PDMP

variable {State : Type*} [MeasurableSpace State]

/-- Execute a finite list of waiting times, flowing and jumping after each
wait. The head of the list is executed first. -/
noncomputable def MeasurableSemiflow.executeSchedule
    (semiflow : MeasurableSemiflow State) (jump : Kernel State State) :
    List NNReal → Kernel State State
  | [] => Kernel.id
  | wait :: waits =>
      semiflow.executeSchedule jump waits ∘ₖ
        semiflow.flowThenJump jump wait

instance MeasurableSemiflow.executeSchedule.instIsMarkovKernel
    (semiflow : MeasurableSemiflow State) (jump : Kernel State State)
    [IsMarkovKernel jump] (waits : List NNReal) :
    IsMarkovKernel (semiflow.executeSchedule jump waits) := by
  induction waits with
  | nil =>
      simp only [MeasurableSemiflow.executeSchedule]
      infer_instance
  | cons wait waits ih =>
      simp only [MeasurableSemiflow.executeSchedule]
      letI : IsMarkovKernel (semiflow.executeSchedule jump waits) := ih
      infer_instance

@[simp] theorem MeasurableSemiflow.executeSchedule_nil
    (semiflow : MeasurableSemiflow State) (jump : Kernel State State) :
    semiflow.executeSchedule jump [] = Kernel.id := rfl

/-- Concatenating two schedules is the same as executing the first and then
the second. -/
theorem MeasurableSemiflow.executeSchedule_append
    (semiflow : MeasurableSemiflow State) (jump : Kernel State State)
    (first second : List NNReal) :
    semiflow.executeSchedule jump (first ++ second) =
      semiflow.executeSchedule jump second ∘ₖ
        semiflow.executeSchedule jump first := by
  induction first with
  | nil => simp
  | cons wait waits ih =>
      simp only [List.cons_append, MeasurableSemiflow.executeSchedule, ih]
      rw [Kernel.comp_assoc]

/-- A target invariant under every flow segment and under the jump remains
invariant after any fixed finite schedule. -/
theorem MeasurableSemiflow.executeSchedule_invariant
    (semiflow : MeasurableSemiflow State) (jump : Kernel State State)
    (target : Measure State)
    (hflow : ∀ t, (semiflow.kernel t).Invariant target)
    (hjump : jump.Invariant target) :
    ∀ waits : List NNReal,
      (semiflow.executeSchedule jump waits).Invariant target
  | [] => Measure.id_comp
  | wait :: waits =>
      (executeSchedule_invariant semiflow jump target hflow hjump waits).comp
        (semiflow.flowThenJump_invariant jump target hflow hjump wait)

/-- Convert the positive real waits used by `WaitingTimes` into the
nonnegative-time schedule accepted by the general-state executor. -/
def WaitingTimes.toNNRealList (waits : WaitingTimes n) : List NNReal :=
  List.ofFn fun i => ⟨waits.wait i, (waits.positive i).le⟩

/-- Execute a fixed vector of strictly positive waiting times. -/
noncomputable def MeasurableSemiflow.executeWaitingTimes
    (semiflow : MeasurableSemiflow State) (jump : Kernel State State)
    (waits : WaitingTimes n) : Kernel State State :=
  semiflow.executeSchedule jump waits.toNNRealList

instance MeasurableSemiflow.executeWaitingTimes.instIsMarkovKernel
    (semiflow : MeasurableSemiflow State) (jump : Kernel State State)
    [IsMarkovKernel jump] (waits : WaitingTimes n) :
    IsMarkovKernel (semiflow.executeWaitingTimes jump waits) := by
  unfold MeasurableSemiflow.executeWaitingTimes
  infer_instance

end Mcmc.PDMP
