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

/-! ### Accepted-proposal affine reversal -/

/-- Reciprocal scaling of two real coordinates. Its Jacobian determinant is
one: the first coordinate is scaled by `scale`, the second by its inverse. -/
noncomputable def reciprocalScale (scale : ℝ) (point : ℝ × ℝ) : ℝ × ℝ :=
  (scale * point.1, scale⁻¹ * point.2)

theorem reciprocalScale_measurePreserving {scale : ℝ} (hscale : scale ≠ 0) :
    MeasurePreserving (reciprocalScale scale)
      ((volume : Measure ℝ).prod volume) (volume.prod volume) := by
  refine ⟨(measurable_const.mul measurable_fst).prodMk
    (measurable_const.mul measurable_snd), ?_⟩
  rw [show reciprocalScale scale = Prod.map (scale * ·) (scale⁻¹ * ·) by
    funext point
    rfl]
  rw [← Measure.map_prod_map volume volume
    (measurable_const_mul scale) (measurable_const_mul scale⁻¹)]
  rw [Real.map_volume_mul_left hscale,
    Real.map_volume_mul_left (inv_ne_zero hscale)]
  rw [Measure.prod_smul_right, Measure.prod_smul_left, smul_smul]
  simp only [inv_inv, abs_inv]
  rw [ENNReal.ofReal_inv_of_pos (abs_pos.mpr hscale)]
  have hcoeff : ENNReal.ofReal |scale| ≠ 0 := by simp [hscale]
  rw [ENNReal.mul_inv_cancel hcoeff (by simp)]
  exact one_smul _ _

/-- Reversal of the final accepted proposal in a fixed bracket. The first
coordinate is the current point and the second is its proposal fraction. -/
noncomputable def acceptedProposalReverse (left right : ℝ)
    (point : ℝ × ℝ) : ℝ × ℝ :=
  let width := right - left
  (left + width * point.2, (point.1 - left) / width)

/-- The accepted-proposal reversal preserves planar Lebesgue measure for every
nondegenerate bracket. This is the exact unit-Jacobian statement used in the
joint practical-slice trace reversal. -/
theorem acceptedProposalReverse_measurePreserving
    {left right : ℝ} (hwidth : right - left ≠ 0) :
    MeasurePreserving (acceptedProposalReverse left right)
      ((volume : Measure ℝ).prod volume) (volume.prod volume) := by
  let translateDown : ℝ × ℝ → ℝ × ℝ :=
    Prod.map id (fun x : ℝ ↦ -left + x)
  let translateUp : ℝ × ℝ → ℝ × ℝ :=
    Prod.map (fun x : ℝ ↦ left + x) id
  have hdown : MeasurePreserving translateDown
      ((volume : Measure ℝ).prod volume) (volume.prod volume) :=
    (MeasurePreserving.id volume).prod
      (measurePreserving_add_left volume (-left))
  have hup : MeasurePreserving translateUp
      ((volume : Measure ℝ).prod volume) (volume.prod volume) :=
    (measurePreserving_add_left volume left).prod
      (MeasurePreserving.id volume)
  have hall := hup.comp ((reciprocalScale_measurePreserving hwidth).comp
    (hdown.comp (Measure.measurePreserving_swap
      (μ := (volume : Measure ℝ)) (ν := volume))))
  convert hall using 1
  funext point
  simp [acceptedProposalReverse, translateDown, translateUp,
    reciprocalScale, Function.comp_def, div_eq_inv_mul]
  constructor
  all_goals ring

theorem acceptedProposalReverse_involutive
    {left right : ℝ} (hwidth : right - left ≠ 0) :
    Function.Involutive (acceptedProposalReverse left right) := by
  intro point
  apply Prod.ext
  · simp [acceptedProposalReverse]
    field_simp
    ring
  · simp [acceptedProposalReverse]
    field_simp

/-- The forward coordinate encodes the accepted point and the reverse
coordinate encodes the old point in the same fixed bracket. -/
theorem acceptedProposalReverse_fst (left right : ℝ) (point : ℝ × ℝ) :
    (acceptedProposalReverse left right point).1 =
      left + (right - left) * point.2 := rfl

theorem acceptedProposalReverse_snd (left right : ℝ) (point : ℝ × ℝ) :
    (acceptedProposalReverse left right point).2 =
      (point.1 - left) / (right - left) := rfl

theorem affineProposal_mem_Ico
    {left right fraction : ℝ} (hwidth : left < right)
    (hfraction : fraction ∈ Set.Ico (0 : ℝ) 1) :
    left + (right - left) * fraction ∈ Set.Ico left right := by
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hwidth.le) hfraction.1]
  · have hmul := mul_lt_mul_of_pos_left hfraction.2 (sub_pos.mpr hwidth)
    nlinarith

theorem reverseFraction_mem_Ico
    {left right point : ℝ} (hwidth : left < right)
    (hpoint : point ∈ Set.Ico left right) :
    (point - left) / (right - left) ∈ Set.Ico (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (sub_nonneg.mpr hpoint.1) (sub_nonneg.mpr hwidth.le)
  · exact (div_lt_one (sub_pos.mpr hwidth)).mpr (sub_lt_sub_right hpoint.2 left)

/-- Successful accepted-proposal coordinates: both the old and proposed point
lie in the fixed bracket and in the sampled superlevel set. -/
def acceptedProposalSuccess (logDensity : ℝ → ℝ) (threshold left right : ℝ) :
    Set (ℝ × ℝ) :=
  {point |
    point.1 ∈ Set.Ico left right ∧
    threshold ≤ logDensity point.1 ∧
    point.2 ∈ Set.Ico (0 : ℝ) 1 ∧
    threshold ≤ logDensity (left + (right - left) * point.2)}

theorem acceptedProposalSuccess_preimage
    (logDensity : ℝ → ℝ) (threshold : ℝ)
    {left right : ℝ} (hwidth : left < right) :
    acceptedProposalReverse left right ⁻¹'
        acceptedProposalSuccess logDensity threshold left right =
      acceptedProposalSuccess logDensity threshold left right := by
  ext point
  simp only [Set.mem_preimage, acceptedProposalSuccess, Set.mem_setOf_eq]
  let reversed := acceptedProposalReverse left right point
  have hinvolutive := acceptedProposalReverse_involutive
    (sub_ne_zero.mpr hwidth.ne') point
  have hpointRecover :
      left + (right - left) * ((point.1 - left) / (right - left)) = point.1 := by
    field_simp [sub_ne_zero.mpr hwidth.ne']
    ring
  have hfractionRecover :
      (right - left) * point.2 / (right - left) = point.2 := by
    field_simp [sub_ne_zero.mpr hwidth.ne']
  constructor
  · rintro ⟨hreversedBracket, hreversedSlice, hreversedFraction,
      holdSlice⟩
    have holdBracket : point.1 ∈ Set.Ico left right := by
      have := affineProposal_mem_Ico hwidth hreversedFraction
      simpa [reversed, acceptedProposalReverse, hpointRecover] using this
    have hfraction : point.2 ∈ Set.Ico (0 : ℝ) 1 := by
      have := reverseFraction_mem_Ico hwidth hreversedBracket
      simpa [reversed, acceptedProposalReverse, hfractionRecover] using this
    refine ⟨holdBracket, ?_, hfraction, ?_⟩
    · simpa [reversed, acceptedProposalReverse, hpointRecover] using holdSlice
    · simpa [reversed, acceptedProposalReverse] using hreversedSlice
  · rintro ⟨holdBracket, holdSlice, hfraction, hnewSlice⟩
    have hnewBracket := affineProposal_mem_Ico hwidth hfraction
    have hreverseFraction := reverseFraction_mem_Ico hwidth holdBracket
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [reversed, acceptedProposalReverse] using hnewBracket
    · simpa [reversed, acceptedProposalReverse] using hnewSlice
    · simpa [reversed, acceptedProposalReverse] using hreverseFraction
    · simpa [reversed, acceptedProposalReverse, hpointRecover] using holdSlice

theorem measurableSet_acceptedProposalSuccess
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (threshold left right : ℝ) :
    MeasurableSet (acceptedProposalSuccess logDensity threshold left right) := by
  unfold acceptedProposalSuccess
  measurability

/-- The final accepted-proposal reversal preserves the planar law restricted
to successful old/new slice points. -/
theorem acceptedProposalReverse_restrict_measurePreserving
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (threshold : ℝ) {left right : ℝ} (hwidth : left < right) :
    MeasurePreserving (acceptedProposalReverse left right)
      (((volume : Measure ℝ).prod volume).restrict
        (acceptedProposalSuccess logDensity threshold left right))
      (((volume : Measure ℝ).prod volume).restrict
        (acceptedProposalSuccess logDensity threshold left right)) := by
  apply measurePreserving_restrict_of_preimage_eq
    (acceptedProposalReverse_measurePreserving (sub_ne_zero.mpr hwidth.ne'))
    (measurableSet_acceptedProposalSuccess hlogDensity threshold left right)
  exact acceptedProposalSuccess_preimage logDensity threshold hwidth

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
