import Mcmc.Finite.ProbabilisticProgram

/-!
# Suspend/resume semantics for finite probabilistic traces

This is a small-step counterpart of `Model.traceWeight`. It records the
accumulated observation weight and the unconsumed factors, and proves that
arbitrary pause boundaries refine the completed-trace semantics.
-/

namespace Mcmc.Finite.ProbabilisticProgram

variable {State : Type*} [Fintype State]

/-- Runtime state at an observation suspension point. -/
structure CoroutineState (State : Type*) where
  state : State
  accumulatedWeight : ℝ
  remaining : List (Factor State)

/-- Begin executing the observation portion of a model after its assumed state
has been selected. -/
def Model.start (model : Model State) (state : State) : CoroutineState State :=
  ⟨state, 1, model.observations⟩

/-- Consume at most one observation factor. `none` means the trace was already
complete; `some` is the next suspended state (which may itself be complete). -/
def CoroutineState.resume (cursor : CoroutineState State) :
    Option (CoroutineState State) :=
  match cursor.remaining with
  | [] => none
  | factor :: remaining => some
      ⟨cursor.state, cursor.accumulatedWeight * factor.weight cursor.state,
        remaining⟩

/-- Consume exactly the requested number of available observation factors. -/
def CoroutineState.run (cursor : CoroutineState State) :
    ℕ → CoroutineState State
  | 0 => cursor
  | fuel + 1 =>
      match cursor.resume with
      | none => cursor
      | some next => next.run fuel

omit [Fintype State] in
@[simp] theorem CoroutineState.run_zero (cursor : CoroutineState State) :
    cursor.run 0 = cursor := rfl

omit [Fintype State] in
/-- Closed form after a prefix: consumed weights multiply onto the accumulator
and the suffix is retained verbatim. -/
theorem CoroutineState.run_append (state : State) (weight : ℝ)
    (consumed suffix : List (Factor State)) :
    (CoroutineState.mk state weight (consumed ++ suffix)).run consumed.length =
      ⟨state,
        weight * (consumed.map fun factor => factor.weight state).prod,
        suffix⟩ := by
  induction consumed generalizing weight with
  | nil => simp
  | cons factor consumed ih =>
      simp only [List.cons_append, List.length_cons, CoroutineState.run,
        CoroutineState.resume]
      rw [ih]
      simp only [List.map_cons, List.prod_cons]
      congr 1
      ring

/-- Resuming to completion gives exactly the batch completed-trace weight. -/
theorem Model.run_to_completion (model : Model State) (state : State) :
    (model.start state).run model.observations.length =
      ⟨state, model.traceWeight state, []⟩ := by
  simpa [Model.start, Model.traceWeight] using
    (CoroutineState.run_append state 1 model.observations [])

omit [Fintype State] in
/-- Pausing after any prefix and later resuming the suffix is observationally
equivalent to uninterrupted execution. -/
theorem CoroutineState.pause_resume_refines (state : State) (weight : ℝ)
    (consumed suffix : List (Factor State)) :
    let paused :=
      (CoroutineState.mk state weight (consumed ++ suffix)).run consumed.length
    paused.run suffix.length =
      (CoroutineState.mk state weight (consumed ++ suffix)).run
        (consumed.length + suffix.length) := by
  dsimp
  rw [CoroutineState.run_append]
  have hleft := CoroutineState.run_append state
    (weight * (consumed.map fun factor => factor.weight state).prod) suffix []
  have hright :
      (CoroutineState.mk state weight (consumed ++ suffix)).run
          (consumed ++ suffix).length =
        ⟨state,
          weight * ((consumed ++ suffix).map
            fun factor => factor.weight state).prod,
          []⟩ := by
    simpa using
      (CoroutineState.run_append state weight (consumed ++ suffix) [])
  calc
    (CoroutineState.mk state
        (weight * (consumed.map fun factor => factor.weight state).prod)
        suffix).run suffix.length =
        ⟨state,
          weight * (consumed.map fun factor => factor.weight state).prod *
            (suffix.map fun factor => factor.weight state).prod,
          []⟩ := by simpa using hleft
    _ = (CoroutineState.mk state weight (consumed ++ suffix)).run
        (consumed.length + suffix.length) := by
      rw [show consumed.length + suffix.length = (consumed ++ suffix).length by simp]
      rw [hright]
      simp only [List.map_append, List.prod_append]
      congr 1
      ring

end Mcmc.Finite.ProbabilisticProgram
