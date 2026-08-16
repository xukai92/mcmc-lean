import Mcmc.Kernel.Slice
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Concrete finite stepping-out and shrinkage semantics

This module gives ideal-real semantics to the bounded practical real-line
slice implementation. Random choices are exposed as a finite trace. Exhausting
the configured shrink budget returns the current point, whereas exhausting the
provided trace early is an error; this matches the Julia Reference and
Optimized implementations.

The definitions are the concrete algorithmic object for the subsequent joint
trace-reversal proof. This module proves only deterministic safety facts and
does not by itself assert stationarity.
-/

namespace Mcmc.Kernel.PracticalSlice

open MeasureTheory

/-- Coordinate-free law for the random initial-bracket alignment. Haar volume
on the unit additive circle is a probability measure. -/
abbrev Alignment := AddCircle (1 : ℝ)

instance alignment.instIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure Alignment) :=
  ⟨by simp [AddCircle.measure_univ]⟩

/-- Neal's offset reversal before choosing the `[0,1)` coordinate chart. -/
noncomputable def reverseAlignment (width old new : ℝ) (offset : Alignment) :
    Alignment :=
  ((new - old) / width : ℝ) + offset

/-- Translation of the circle preserves the exact uniform alignment law. -/
theorem reverseAlignment_measurePreserving (width old new : ℝ) :
    MeasurePreserving (reverseAlignment width old new)
      (volume : Measure Alignment) volume := by
  exact measurePreserving_add_left volume (((new - old) / width : ℝ) : Alignment)

/-- Canonical runtime coordinate for a circle-valued alignment. -/
noncomputable def alignmentCoordinate (offset : Alignment) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) 0 offset).1

theorem alignmentCoordinate_mem (offset : Alignment) :
    alignmentCoordinate offset ∈ Set.Ico (0 : ℝ) 1 := by
  simpa [alignmentCoordinate] using
    (AddCircle.equivIco (1 : ℝ) 0 offset).2

/-- Random choices consumed before shrinkage. `offset` positions the initial
width-sized bracket and `leftSteps` allocates the finite expansion budget. -/
structure BracketTrace where
  logHeightOffset : ℝ
  offset : ℝ
  leftSteps : ℕ

/-- All random choices for a bounded stepping-out/shrinkage update. -/
structure Trace extends BracketTrace where
  shrinkFractions : List ℝ

/-- Neal's alignment reversal (equation (5)): move the initial-bracket offset
to the new current point while retaining the same width-grid alignment. -/
noncomputable def reverseOffset (width old new offset : ℝ) : ℝ :=
  Int.fract (offset + (new - old) / width)

theorem reverseOffset_mem_Ico (width old new offset : ℝ) :
    reverseOffset width old new offset ∈ Set.Ico (0 : ℝ) 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- The coordinate-free Haar translation is exactly the fractional-part
formula used by the concrete real-valued semantics. -/
theorem alignmentCoordinate_reverseAlignment
    (width old new : ℝ) (offset : Alignment) :
    alignmentCoordinate (reverseAlignment width old new offset) =
      reverseOffset width old new (alignmentCoordinate offset) := by
  change (AddCircle.equivIco (1 : ℝ) 0
      (((new - old) / width : ℝ) + offset)).1 = _
  rw [show offset = ((alignmentCoordinate offset : ℝ) : Alignment) by
    exact (AddCircle.coe_equivIco
      (p := (1 : ℝ)) (a := 0) (y := offset)).symm]
  rw [show (((new - old) / width : ℝ) : Alignment) +
        ((alignmentCoordinate offset : ℝ) : Alignment) =
      (((new - old) / width + alignmentCoordinate offset : ℝ) : Alignment) by
    exact (AddCircle.coe_add (p := (1 : ℝ)) _ _).symm]
  have hcoordinate :
      alignmentCoordinate
          ((alignmentCoordinate offset : ℝ) : Alignment) =
        alignmentCoordinate offset := by
    unfold alignmentCoordinate
    rw [AddCircle.equivIco_coe_of_mem
      (show (AddCircle.equivIco (1 : ℝ) 0 offset).1 ∈
          Set.Ico (0 : ℝ) (0 + 1) from
        (AddCircle.equivIco (1 : ℝ) 0 offset).2)]
  simpa [reverseOffset, hcoordinate, add_comm] using
    (AddCircle.coe_equivIco_mk_apply
      (p := (1 : ℝ)) (x := (new - old) / width + alignmentCoordinate offset))

theorem measurable_reverseOffset (width old new : ℝ) :
    Measurable (reverseOffset width old new) := by
  exact measurable_fract.comp
    (measurable_id.add measurable_const)

/-- Reversing the alignment a second time recovers the original uniform
offset. Endpoint `1` is excluded exactly as for the continuous uniform draw. -/
theorem reverseOffset_reverseOffset
    {width old new offset : ℝ} (hwidth : width ≠ 0)
    (hoffset : offset ∈ Set.Ico (0 : ℝ) 1) :
    reverseOffset width new old (reverseOffset width old new offset) = offset := by
  unfold reverseOffset
  rw [Int.fract_eq_iff]
  refine ⟨hoffset.1, hoffset.2, -⌊offset + (new - old) / width⌋, ?_⟩
  rw [Int.fract]
  push_cast
  field_simp
  ring

/-- Real-valued form of Neal's integer grid displacement in equation (6).
Its integrality is recorded separately below; this form makes the alignment
identity independent of integer coercion bookkeeping. -/
noncomputable def alignmentShift (width old new offset : ℝ) : ℝ :=
  (new / width - reverseOffset width old new offset) -
    (old / width - offset)

/-- Adjusting the left expansion allocation by the alignment shift gives the
same maximal left endpoint when the start point is changed. -/
theorem maximalLeftEndpoint_reverse
    {width old new offset allocation : ℝ} (hwidth : width ≠ 0) :
    new - width * reverseOffset width old new offset -
        width * (allocation + alignmentShift width old new offset) =
      old - width * offset - width * allocation := by
  unfold alignmentShift
  field_simp
  ring

/-- The alignment displacement is in fact the floor appearing in Neal's
formula, hence an integer despite its real-valued presentation. -/
theorem alignmentShift_eq_floor
    {width old new offset : ℝ} (hwidth : width ≠ 0) :
    alignmentShift width old new offset =
      (⌊offset + (new - old) / width⌋ : ℤ) := by
  unfold alignmentShift reverseOffset
  rw [Int.fract]
  field_simp
  ring

/-- The reverse displacement cancels the forward displacement. -/
theorem alignmentShift_reverse
    {width old new offset : ℝ} (hwidth : width ≠ 0)
    (hoffset : offset ∈ Set.Ico (0 : ℝ) 1) :
    alignmentShift width new old (reverseOffset width old new offset) =
      -alignmentShift width old new offset := by
  unfold alignmentShift
  rw [reverseOffset_reverseOffset hwidth hoffset]
  field_simp
  ring

/-- Expansion allocations for which Neal's integer displacement stays inside
the finite uniform allocation range. This is exactly the allocation component
of the successful reversible-trace event. -/
def ValidAllocation (intervals : ℕ) (shift : ℤ) :=
  {allocation : ℤ //
    0 ≤ allocation ∧ allocation < intervals ∧
    0 ≤ allocation + shift ∧ allocation + shift < intervals}

/-- On the restricted success event, adding the grid displacement is a
bijection; the reverse trace uses the negated displacement. -/
def reverseAllocation (intervals : ℕ) (shift : ℤ) :
    ValidAllocation intervals shift ≃ ValidAllocation intervals (-shift) where
  toFun allocation :=
    ⟨allocation.1 + shift,
      allocation.2.2.2.1,
      allocation.2.2.2.2,
      by simpa [add_assoc] using allocation.2.1,
      by simpa [add_assoc] using allocation.2.2.1⟩
  invFun allocation :=
    ⟨allocation.1 - shift,
      by simpa [sub_eq_add_neg] using allocation.2.2.2.1,
      by simpa [sub_eq_add_neg] using allocation.2.2.2.2,
      by simpa [sub_eq_add_neg, add_assoc] using allocation.2.1,
      by simpa [sub_eq_add_neg, add_assoc] using allocation.2.2.1⟩
  left_inv allocation := by
    apply Subtype.ext
    simp
  right_inv allocation := by
    apply Subtype.ext
    simp

/-- Expand the left endpoint by at most `steps` widths, stopping once the
endpoint is outside the strict superlevel set. -/
noncomputable def expandLeft (logDensity : ℝ → ℝ) (threshold width : ℝ) : ℕ → ℝ → ℝ
  | 0, left => left
  | steps + 1, left =>
      if logDensity left ≤ threshold then left
      else expandLeft logDensity threshold width steps (left - width)

/-- Expand the right endpoint by at most `steps` widths. -/
noncomputable def expandRight (logDensity : ℝ → ℝ) (threshold width : ℝ) : ℕ → ℝ → ℝ
  | 0, right => right
  | steps + 1, right =>
      if logDensity right ≤ threshold then right
      else expandRight logDensity threshold width steps (right + width)

/-- Bounded shrinkage driven by uniform fractions. An empty list before the
budget is exhausted denotes a malformed trace; consuming the whole attempt
budget without acceptance is the checked identity fallback. -/
noncomputable def shrink (logDensity : ℝ → ℝ) (current threshold : ℝ) :
    ℕ → List ℝ → ℝ → ℝ → Except Unit ℝ
  | 0, _, _, _ => .ok current
  | _ + 1, [], _, _ => .error ()
  | attempts + 1, fraction :: remaining, left, right =>
      let proposal := left + (right - left) * fraction
      if threshold ≤ logDensity proposal then .ok proposal
      else if proposal < current then
        shrink logDensity current threshold attempts remaining proposal right
      else
        shrink logDensity current threshold attempts remaining left proposal

/-- Bracket update induced by one rejected point. -/
noncomputable def shrinkBracket (current rejected : ℝ) (bracket : ℝ × ℝ) :
    ℝ × ℝ :=
  if rejected < current then (rejected, bracket.2) else (bracket.1, rejected)

/-- Apply a recorded sequence of rejected points, independently of how their
uniform fractions were represented. -/
noncomputable def shrinkRejectedPoints (current : ℝ) :
    List ℝ → (ℝ × ℝ) → (ℝ × ℝ)
  | [], bracket => bracket
  | rejected :: remaining, bracket =>
      shrinkRejectedPoints current remaining
        (shrinkBracket current rejected bracket)

/-- If a rejected point lies on the same side of the old and new states, both
directions perform exactly the same bracket update. -/
theorem shrinkBracket_eq_of_sameSide
    {old new rejected : ℝ} {bracket : ℝ × ℝ}
    (hsame : (rejected < old) = (rejected < new)) :
    shrinkBracket old rejected bracket = shrinkBracket new rejected bracket := by
  unfold shrinkBracket
  by_cases hold : rejected < old <;>
    by_cases hnew : rejected < new <;>
      simp only [hold, hnew, if_true, if_false] <;> simp_all

/-- Neal's shrinkage-reversal core: replaying the same rejected points gives
the same successive bracket from either endpoint whenever no rejected point
separates the two possible states. -/
theorem shrinkRejectedPoints_eq_of_sameSide
    {old new : ℝ} {rejected : List ℝ} {bracket : ℝ × ℝ}
    (hsame : ∀ point ∈ rejected, (point < old) = (point < new)) :
    shrinkRejectedPoints old rejected bracket =
      shrinkRejectedPoints new rejected bracket := by
  induction rejected generalizing bracket with
  | nil => rfl
  | cons point remaining ih =>
      simp only [shrinkRejectedPoints]
      rw [shrinkBracket_eq_of_sameSide (hsame point (by simp))]
      apply ih
      intro candidate hcandidate
      exact hsame candidate (by simp [hcandidate])

/-- Literal ideal-real execution of one bounded practical slice update. The
precondition `trace.leftSteps ≤ maxSteps` is checked rather than silently
truncating a malformed expansion-allocation trace. -/
noncomputable def run (logDensity : ℝ → ℝ) (width current : ℝ)
    (maxSteps maxShrink : ℕ) (trace : Trace) : Except Unit ℝ := do
  if trace.leftSteps ≤ maxSteps then
    let threshold := logDensity current + trace.logHeightOffset
    let initialLeft := current - width * trace.offset
    let initialRight := initialLeft + width
    let left := expandLeft logDensity threshold width trace.leftSteps initialLeft
    let right := expandRight logDensity threshold width
      (maxSteps - trace.leftSteps) initialRight
    shrink logDensity current threshold maxShrink trace.shrinkFractions left right
  else
    .error ()

@[simp] theorem shrink_zero (logDensity : ℝ → ℝ) (current threshold : ℝ)
    (trace : List ℝ) (left right : ℝ) :
    shrink logDensity current threshold 0 trace left right = .ok current := rfl

@[simp] theorem shrink_positive_nil (logDensity : ℝ → ℝ)
    (current threshold left right : ℝ) (attempts : ℕ) :
    shrink logDensity current threshold (attempts + 1) [] left right =
      .error () := rfl

/-- A successful shrink execution either takes the explicit identity fallback
or returns a point whose log density is at least the sampled threshold. -/
theorem shrink_ok_eq_current_or_mem
    (logDensity : ℝ → ℝ) (current threshold result : ℝ)
    (attempts : ℕ) (trace : List ℝ) (left right : ℝ)
    (hrun : shrink logDensity current threshold attempts trace left right =
      .ok result) :
    result = current ∨ threshold ≤ logDensity result := by
  induction attempts generalizing trace left right with
  | zero =>
      simp only [shrink, Except.ok.injEq] at hrun
      exact Or.inl hrun.symm
  | succ attempts ih =>
      cases trace with
      | nil => simp [shrink] at hrun
      | cons fraction remaining =>
          let proposal := left + (right - left) * fraction
          by_cases haccept : threshold ≤ logDensity proposal
          · simp only [shrink, proposal, haccept, if_true,
              Except.ok.injEq] at hrun
            exact Or.inr (hrun ▸ haccept)
          · simp only [shrink, proposal, haccept, if_false] at hrun
            by_cases hleft : left + (right - left) * fraction < current
            · simp only [hleft, if_true] at hrun
              exact ih remaining proposal right hrun
            · simp only [hleft, if_false] at hrun
              exact ih remaining left proposal hrun

/-- A zero shrink budget makes every well-formed expansion trace an identity
update, independent of the bracket construction. -/
theorem run_zeroShrink_of_wellFormed
    (logDensity : ℝ → ℝ) (width current : ℝ) (maxSteps : ℕ) (trace : Trace)
    (htrace : trace.leftSteps ≤ maxSteps) :
    run logDensity width current maxSteps 0 trace = .ok current := by
  simp [run, htrace]

@[simp] theorem run_error_of_excessLeftSteps
    (logDensity : ℝ → ℝ) (width current : ℝ)
    (maxSteps maxShrink : ℕ) (trace : Trace)
    (htrace : maxSteps < trace.leftSteps) :
    run logDensity width current maxSteps maxShrink trace = .error () := by
  simp [run, Nat.not_le.mpr htrace]

/-- Every successful complete update returns the current point or a point in
the sampled superlevel set. This includes identity fallback on shrink-budget
exhaustion and rules out treating malformed trace exhaustion as success. -/
theorem run_ok_eq_current_or_mem
    (logDensity : ℝ → ℝ) (width current result : ℝ)
    (maxSteps maxShrink : ℕ) (trace : Trace)
    (hrun : run logDensity width current maxSteps maxShrink trace = .ok result) :
    result = current ∨
      logDensity current + trace.logHeightOffset ≤ logDensity result := by
  unfold run at hrun
  split at hrun
  · exact shrink_ok_eq_current_or_mem logDensity current
      (logDensity current + trace.logHeightOffset) result maxShrink
      trace.shrinkFractions _ _ hrun
  · simp at hrun

/-- Small executable-by-reduction witness for the concrete semantics: one
left and one right expansion followed by an accepted midpoint proposal. -/
example :
    run (fun x : ℝ ↦ -(x ^ 2) / 2) 1 0 2 20
      { logHeightOffset := -1, offset := 1 / 4, leftSteps := 1,
        shrinkFractions := [1 / 2] } = .ok (1 / 4) := by
  norm_num [run, expandLeft, expandRight, shrink]

end Mcmc.Kernel.PracticalSlice
