import Mcmc.Executable.Finite.Weights

/-!
# Deterministic traces for finite sampler primitives

Trace replay is an operational interpretation, separate from the PMF
semantics of a primitive draw.  Every event records both the requested bound
and returned value, so mismatched or invalid traces fail explicitly.
-/

namespace Mcmc.Executable.Finite

/-- Failures exposed by the finite executable primitive layer. -/
inductive ExecError where
  | invalidBound (upper : ℕ)
  | exhaustedTrace
  | boundMismatch (expected actual : ℕ)
  | outOfRange (upper value : ℕ)
  deriving DecidableEq, Repr

/-- One recorded uniform-natural primitive call. -/
structure DrawEvent where
  upper : ℕ
  value : ℕ
  deriving DecidableEq, Repr

/-- Successful result of consuming one trace event. -/
structure DrawResult where
  value : ℕ
  remaining : List DrawEvent
  deriving DecidableEq, Repr

/-- Consume and validate one `drawBelow` event. -/
def replayDraw (upper : ℕ) (trace : List DrawEvent) :
    Except ExecError DrawResult :=
  if upper = 0 then
    .error (.invalidBound upper)
  else
    match trace with
    | [] => .error .exhaustedTrace
    | event :: rest =>
        if event.upper != upper then
          .error (.boundMismatch upper event.upper)
        else if event.value < upper then
          .ok ⟨event.value, rest⟩
        else
          .error (.outOfRange upper event.value)

theorem replayDraw_eq_ok_iff {upper : ℕ} {trace : List DrawEvent}
    {result : DrawResult} :
    replayDraw upper trace = .ok result ↔
      0 < upper ∧
      ∃ rest, trace = ⟨upper, result.value⟩ :: rest ∧
        result.remaining = rest ∧ result.value < upper := by
  constructor
  · intro h
    unfold replayDraw at h
    split at h <;> rename_i hupper
    · simp at h
    · have hupperPos : 0 < upper := Nat.pos_of_ne_zero hupper
      cases trace with
      | nil => simp at h
      | cons event rest =>
          simp only at h
          split at h <;> rename_i hbound
          · simp at h
          · split at h <;> rename_i hvalue
            · simp only [Except.ok.injEq] at h
              subst result
              have heq : event.upper = upper := by
                simpa only [bne_iff_ne, ne_eq, not_not] using hbound
              subst heq
              exact ⟨hupperPos, rest, rfl, rfl, hvalue⟩
            · simp at h
  · rintro ⟨hupper, rest, rfl, rfl, hvalue⟩
    unfold replayDraw
    simp [Nat.ne_of_gt hupper, hvalue]

theorem replayDraw_success_value_lt {upper : ℕ} {trace : List DrawEvent}
    {result : DrawResult} (h : replayDraw upper trace = .ok result) :
    result.value < upper :=
  (replayDraw_eq_ok_iff.mp h).2.choose_spec.2.2

@[simp]
theorem replayDraw_zero (trace : List DrawEvent) :
    replayDraw 0 trace = .error (.invalidBound 0) := by
  simp [replayDraw]

@[simp]
theorem replayDraw_nil {upper : ℕ} (hupper : 0 < upper) :
    replayDraw upper [] = .error .exhaustedTrace := by
  simp [replayDraw, Nat.ne_of_gt hupper]

end Mcmc.Executable.Finite
