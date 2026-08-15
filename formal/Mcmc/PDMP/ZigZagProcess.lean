import Mcmc.PDMP.EventExecution
import Mcmc.PDMP.ZigZag
import Mathlib.Tactic

/-!
# One-dimensional Zig-Zag process semantics

This module instantiates the generic PDMP flow and jump interfaces for the
one-dimensional Zig-Zag state `(position, velocity)`.  It supplies the exact
linear semiflow, deterministic velocity flip, and fixed-event execution
kernel.  Sampling the state-dependent event times remains a separate layer.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory

namespace Mcmc.PDMP

/-- Position and two-valued velocity for the one-dimensional Zig-Zag process. -/
abbrev ZigZagState := ℝ × Bool

/-- Exact linear Zig-Zag motion between velocity-switching events. -/
def zigZagFlow (t : NNReal) (state : ZigZagState) : ZigZagState :=
  (state.1 + (t : ℝ) * zigZagVelocity state.2, state.2)

/-- The linear Zig-Zag motion is a measurable semiflow. -/
noncomputable def zigZagSemiflow : MeasurableSemiflow ZigZagState where
  flow := zigZagFlow
  measurable_flow t := by
    unfold zigZagFlow
    fun_prop
  flow_zero := by
    funext state
    simp [zigZagFlow]
  flow_add := by
    intro t u
    funext state
    apply Prod.ext
    · simp only [zigZagFlow, Function.comp_apply, NNReal.coe_add]
      ring
    · rfl

/-- A Zig-Zag event keeps position fixed and flips the velocity sign. -/
def zigZagFlip (state : ZigZagState) : ZigZagState :=
  (state.1, !state.2)

/-- Deterministic Markov kernel for a Zig-Zag velocity switch. -/
noncomputable def zigZagJumpKernel : Kernel ZigZagState ZigZagState :=
  Kernel.deterministic zigZagFlip (by
    unfold zigZagFlip
    fun_prop)

instance zigZagJumpKernel.instIsMarkovKernel :
    IsMarkovKernel zigZagJumpKernel := by
  unfold zigZagJumpKernel
  infer_instance

@[simp] theorem zigZagFlip_involutive (state : ZigZagState) :
    zigZagFlip (zigZagFlip state) = state := by
  rcases state with ⟨q, v⟩
  simp [zigZagFlip]

/-- Kernel for executing a fixed list of Zig-Zag inter-event waits. -/
noncomputable def zigZagExecuteSchedule (waits : List NNReal) :
    Kernel ZigZagState ZigZagState :=
  zigZagSemiflow.executeSchedule zigZagJumpKernel waits

instance zigZagExecuteSchedule.instIsMarkovKernel (waits : List NNReal) :
    IsMarkovKernel (zigZagExecuteSchedule waits) := by
  unfold zigZagExecuteSchedule
  infer_instance

/-- The canonical event intensity evaluated on a Zig-Zag process state. -/
def zigZagStateRate (potentialGradient : ℝ → ℝ)
    (state : ZigZagState) : ℝ :=
  zigZagRate potentialGradient state.1 state.2

theorem zigZagStateRate_nonneg (potentialGradient : ℝ → ℝ)
    (state : ZigZagState) :
    0 ≤ zigZagStateRate potentialGradient state :=
  zigZagRate_nonneg potentialGradient state.1 state.2

end Mcmc.PDMP
