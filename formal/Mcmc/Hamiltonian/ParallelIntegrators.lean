import Mathlib.Tactic

/-!
# Foundations for parallel trajectory integrators

This module isolates two exact, finite-computation facts needed by speculative
parallel HMC implementations. Associative affine summaries admit a prefix-scan
evaluation, and a candidate trace that is checked edge by edge is exactly the
serial recurrence. Neither result treats numerical closeness as equality.
-/

namespace Mcmc.Hamiltonian.ParallelIntegrators

/-- A scalar affine map, stored in the representation used by an associative
prefix scan. -/
structure ScalarAffine where
  slope : ℝ
  intercept : ℝ

namespace ScalarAffine

def apply (map : ScalarAffine) (x : ℝ) : ℝ :=
  map.slope * x + map.intercept

/-- `later.comp earlier` first applies `earlier`, then `later`. -/
def comp (later earlier : ScalarAffine) : ScalarAffine :=
  ⟨later.slope * earlier.slope,
    later.slope * earlier.intercept + later.intercept⟩

def identity : ScalarAffine := ⟨1, 0⟩

@[simp] theorem apply_identity (x : ℝ) : identity.apply x = x := by
  simp [identity, apply]

@[simp] theorem apply_comp (later earlier : ScalarAffine) (x : ℝ) :
    (later.comp earlier).apply x = later.apply (earlier.apply x) := by
  simp [comp, apply]
  ring

theorem comp_assoc (third second first : ScalarAffine) :
    (third.comp second).comp first = third.comp (second.comp first) := by
  cases third
  cases second
  cases first
  simp [comp]
  constructor <;> ring

@[simp] theorem comp_identity (map : ScalarAffine) :
    map.comp identity = map := by
  cases map
  simp [comp, identity]

@[simp] theorem identity_comp (map : ScalarAffine) :
    identity.comp map = map := by
  cases map
  simp [comp, identity]

end ScalarAffine

/-- Inclusive prefix summaries. A parallel scan may evaluate this same list
using any tree reassociation justified by `ScalarAffine.comp_assoc`. -/
def affinePrefixes : List ScalarAffine → List ScalarAffine
  | [] => []
  | first :: rest =>
      first :: (affinePrefixes rest).map (fun summary => summary.comp first)

theorem affinePrefixes_length (segments : List ScalarAffine) :
    (affinePrefixes segments).length = segments.length := by
  induction segments with
  | nil => rfl
  | cons first rest ih => simp [affinePrefixes, ih]

/-- Serial evaluation of a sequence of affine recurrence segments. -/
def runAffine (initial : ℝ) : List ScalarAffine → ℝ
  | [] => initial
  | segment :: rest => runAffine (segment.apply initial) rest

theorem runAffine_eq_foldl (initial : ℝ) (segments : List ScalarAffine) :
    runAffine initial segments =
      (segments.foldl (fun value segment => segment.apply value) initial) := by
  induction segments generalizing initial with
  | nil => rfl
  | cons segment rest ih => simp [runAffine, ih]

/-- A purported sequence of states after `initial` follows a deterministic
recurrence edge by edge. -/
def TraceValid (step : α → α) : α → List α → Prop
  | _, [] => True
  | current, next :: rest => next = step current ∧ TraceValid step next rest

def traceEndpoint : α → List α → α
  | initial, [] => initial
  | _, next :: rest => traceEndpoint next rest

/-- The endpoint of every edge-valid trace is the corresponding serial
iterate. This is the logical core of the speculative-solve/replay gate. -/
theorem TraceValid.endpoint_eq_iterate (step : α → α) (initial : α)
    {trace : List α} (valid : TraceValid step initial trace) :
    traceEndpoint initial trace = (step^[trace.length]) initial := by
  induction trace generalizing initial with
  | nil => simp [traceEndpoint]
  | cons next rest ih =>
      rcases valid with ⟨rfl, valid⟩
      simpa [traceEndpoint, Function.iterate_succ_apply] using
        ih (initial := step initial) valid

/-- Executable Boolean counterpart of `TraceValid`. -/
def traceValid [BEq α] (step : α → α) (initial : α) : List α → Bool
  | [] => true
  | next :: rest => next == step initial && traceValid step next rest

end Mcmc.Hamiltonian.ParallelIntegrators
