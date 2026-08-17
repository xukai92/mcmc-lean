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

/-- A measure-preserving map also preserves a measurable reweighting whenever
the density is pointwise invariant. This packages the likelihood-factor step
needed after constructing a volume-preserving trace reversal. -/
theorem measurePreserving_withDensity_of_invariant
    {Space : Type*} [MeasurableSpace Space]
    {measure : Measure Space} {transform : Space → Space}
    {density : Space → ENNReal}
    (htransform : MeasurePreserving transform measure measure)
    (hdensity : Measurable density)
    (hinvariant : ∀ point, density (transform point) = density point) :
    MeasurePreserving transform (measure.withDensity density)
      (measure.withDensity density) := by
  refine ⟨htransform.measurable, ?_⟩
  ext event hevent
  rw [Measure.map_apply htransform.measurable hevent,
    withDensity_apply _ (htransform.measurable hevent),
    withDensity_apply _ hevent,
    ← lintegral_indicator (htransform.measurable hevent),
    ← lintegral_indicator hevent,
    ← htransform.lintegral_comp (hdensity.indicator hevent)]
  apply lintegral_congr
  intro point
  by_cases hmem : transform point ∈ event
  · have hpreimage : point ∈ transform ⁻¹' event := hmem
    simp [Set.indicator, hmem, hpreimage, hinvariant]
  · have hpreimage : point ∉ transform ⁻¹' event := hmem
    simp [Set.indicator, hmem, hpreimage]

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

/-- Runtime natural-number representation of a valid integer allocation. -/
def allocationSteps {intervals : ℕ} {shift : ℤ}
    (allocation : ValidAllocation intervals shift) : ℕ :=
  allocation.1.toNat

theorem intCast_allocationSteps {intervals : ℕ} {shift : ℤ}
    (allocation : ValidAllocation intervals shift) :
    (allocationSteps allocation : ℤ) = allocation.1 := by
  exact Int.toNat_of_nonneg allocation.2.1

/-- For a nonnegative grid displacement, rerooting adds that many left
expansion steps. -/
theorem allocationSteps_reverse_of_nonneg
    {intervals : ℕ} {shift : ℤ} (hshift : 0 ≤ shift)
    (allocation : ValidAllocation intervals shift) :
    allocationSteps (reverseAllocation intervals shift allocation) =
      allocationSteps allocation + shift.toNat := by
  apply Int.ofNat_injective
  change (allocationSteps (reverseAllocation intervals shift allocation) : ℤ) =
    (allocationSteps allocation : ℤ) + (shift.toNat : ℤ)
  rw [intCast_allocationSteps, intCast_allocationSteps,
    Int.toNat_of_nonneg hshift]
  rfl

/-- For a nonpositive displacement, the forward allocation has the extra
left expansion steps relative to its rerooting. -/
theorem allocationSteps_eq_reverse_add_of_nonpos
    {intervals : ℕ} {shift : ℤ} (hshift : shift ≤ 0)
    (allocation : ValidAllocation intervals shift) :
    allocationSteps allocation =
      allocationSteps (reverseAllocation intervals shift allocation) +
        (-shift).toNat := by
  apply Int.ofNat_injective
  change (allocationSteps allocation : ℤ) =
    (allocationSteps (reverseAllocation intervals shift allocation) : ℤ) +
      ((-shift).toNat : ℤ)
  rw [intCast_allocationSteps, intCast_allocationSteps,
    Int.toNat_of_nonneg (neg_nonneg.mpr hshift)]
  simp [reverseAllocation]

theorem allocationSteps_lt {intervals : ℕ} {shift : ℤ}
    (allocation : ValidAllocation intervals shift) :
    allocationSteps allocation < intervals := by
  have hcast := intCast_allocationSteps allocation
  have hbound := allocation.2.2.1
  omega

/-- Finite-index presentation of the valid integer allocation stratum. -/
abbrev FiniteValidAllocation (intervals : ℕ) (shift : ℤ) :=
  {allocation : Fin intervals //
    0 ≤ (allocation.1 : ℤ) + shift ∧
      (allocation.1 : ℤ) + shift < intervals}

/-- Valid integer allocations are a genuinely finite type, despite being
defined as a bounded subtype of `ℤ`. -/
def validAllocationEquivFinite (intervals : ℕ) (shift : ℤ) :
    ValidAllocation intervals shift ≃ FiniteValidAllocation intervals shift where
  toFun allocation :=
    ⟨⟨allocationSteps allocation, allocationSteps_lt allocation⟩,
      by
        rw [intCast_allocationSteps]
        exact ⟨allocation.2.2.2.1, allocation.2.2.2.2⟩⟩
  invFun allocation :=
    ⟨(allocation.1.1 : ℤ), by
      exact ⟨by positivity, by exact_mod_cast allocation.1.2,
        allocation.2.1, allocation.2.2⟩⟩
  left_inv allocation := by
    apply Subtype.ext
    change (allocationSteps allocation : ℤ) = allocation.1
    exact intCast_allocationSteps allocation
  right_inv allocation := by
    apply Subtype.ext
    apply Fin.ext
    change Int.toNat (allocation.1.1 : ℤ) = allocation.1.1
    simp

noncomputable instance validAllocation.instFintype
    (intervals : ℕ) (shift : ℤ) : Fintype (ValidAllocation intervals shift) :=
  Fintype.ofEquiv (FiniteValidAllocation intervals shift)
    (validAllocationEquivFinite intervals shift).symm

/-- Allocation strata carry the discrete measurable structure. -/
instance validAllocation.instMeasurableSpace
    (intervals : ℕ) (shift : ℤ) : MeasurableSpace (ValidAllocation intervals shift) :=
  ⊤

/-- Allocation rerooting preserves every finite counting sum exactly. This is
the discrete measure-preservation component of successful trace reversal. -/
theorem sum_reverseAllocation
    {Value : Type*} [AddCommMonoid Value]
    (intervals : ℕ) (shift : ℤ)
    (weight : ValidAllocation intervals (-shift) → Value) :
    (∑ allocation : ValidAllocation intervals shift,
      weight (reverseAllocation intervals shift allocation)) =
      ∑ allocation, weight allocation :=
  Equiv.sum_comp (reverseAllocation intervals shift) weight

/-- The finite allocation bijection preserves counting measure, upgrading the
sum identity to the measure-theoretic interface needed for product trace
spaces. The source and target are the opposite displacement strata. -/
theorem reverseAllocation_measurePreserving
    (intervals : ℕ) (shift : ℤ) :
    MeasurePreserving (reverseAllocation intervals shift)
      (Measure.count : Measure (ValidAllocation intervals shift))
      (Measure.count : Measure (ValidAllocation intervals (-shift))) := by
  let equivalence := reverseAllocation intervals shift
  have hmeasurable : Measurable equivalence := measurable_of_finite _
  refine ⟨hmeasurable, ?_⟩
  ext event hevent
  rw [Measure.map_apply hmeasurable hevent,
    Measure.count_apply (hevent.preimage hmeasurable),
    Measure.count_apply hevent,
    Set.encard_preimage_of_bijective equivalence.bijective]

/-- Integration rule for a pair of forward/reverse allocation-stratum
weights. Pointwise trace reversal plus this theorem yields equality of the
full finite allocation sums. -/
theorem sum_validAllocation_eq_of_reverse
    {Value : Type*} [AddCommMonoid Value]
    (intervals : ℕ) (shift : ℤ)
    (forward : ValidAllocation intervals shift → Value)
    (reverse : ValidAllocation intervals (-shift) → Value)
    (hpointwise : ∀ allocation,
      forward allocation =
        reverse (reverseAllocation intervals shift allocation)) :
    (∑ allocation, forward allocation) = ∑ allocation, reverse allocation := by
  calc
    (∑ allocation, forward allocation) =
        ∑ allocation,
          reverse (reverseAllocation intervals shift allocation) := by
      apply Finset.sum_congr rfl
      intro allocation _
      exact hpointwise allocation
    _ = _ := sum_reverseAllocation intervals shift reverse

/-- Remaining right-expansion budget when `intervals` possible allocations
split a total budget of `intervals - 1`. -/
def allocationRightSteps {intervals : ℕ} {shift : ℤ}
    (allocation : ValidAllocation intervals shift) : ℕ :=
  intervals - 1 - allocationSteps allocation

theorem allocationRightSteps_eq_reverse_add_of_nonneg
    {intervals : ℕ} {shift : ℤ} (hshift : 0 ≤ shift)
    (allocation : ValidAllocation intervals shift) :
    allocationRightSteps allocation = shift.toNat +
      allocationRightSteps (reverseAllocation intervals shift allocation) := by
  have hleft := allocationSteps_reverse_of_nonneg hshift allocation
  have hold := allocationSteps_lt allocation
  have hnew := allocationSteps_lt
    (reverseAllocation intervals shift allocation)
  unfold allocationRightSteps
  omega

theorem allocationRightSteps_reverse_eq_add_of_nonpos
    {intervals : ℕ} {shift : ℤ} (hshift : shift ≤ 0)
    (allocation : ValidAllocation intervals shift) :
    allocationRightSteps (reverseAllocation intervals shift allocation) =
      (-shift).toNat + allocationRightSteps allocation := by
  have hleft := allocationSteps_eq_reverse_add_of_nonpos hshift allocation
  have hold := allocationSteps_lt allocation
  have hnew := allocationSteps_lt
    (reverseAllocation intervals shift allocation)
  unfold allocationRightSteps
  omega

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

/-- A prefix of grid points known to lie strictly inside the slice can be
discarded from a leftward stepping-out scan. This is the recursion lemma used
when rerooting an aligned bracket at another accepted slice point. -/
theorem expandLeft_add_consumed (logDensity : ℝ → ℝ) (threshold width left : ℝ)
    (consumed steps : ℕ)
    (hinside : ∀ index < consumed,
      threshold < logDensity (left - (index : ℝ) * width)) :
    expandLeft logDensity threshold width (consumed + steps) left =
      expandLeft logDensity threshold width steps
        (left - (consumed : ℝ) * width) := by
  induction consumed generalizing left with
  | zero => simp
  | succ consumed ih =>
      rw [Nat.succ_add]
      simp only [expandLeft]
      rw [if_neg (not_le.mpr (by simpa using hinside 0 (Nat.zero_lt_succ _)))]
      have htail : ∀ index < consumed,
          threshold < logDensity
            ((left - width) - (index : ℝ) * width) := by
        intro index hindex
        convert hinside (index + 1) (Nat.succ_lt_succ hindex) using 1
        push_cast
        ring_nf
      convert ih (left := left - width) htail using 1
      push_cast
      ring_nf

/-- Rightward counterpart of `expandLeft_add_consumed`. -/
theorem expandRight_add_consumed (logDensity : ℝ → ℝ) (threshold width right : ℝ)
    (consumed steps : ℕ)
    (hinside : ∀ index < consumed,
      threshold < logDensity (right + (index : ℝ) * width)) :
    expandRight logDensity threshold width (consumed + steps) right =
      expandRight logDensity threshold width steps
        (right + (consumed : ℝ) * width) := by
  induction consumed generalizing right with
  | zero => simp
  | succ consumed ih =>
      rw [Nat.succ_add]
      simp only [expandRight]
      rw [if_neg (not_le.mpr (by simpa using hinside 0 (Nat.zero_lt_succ _)))]
      have htail : ∀ index < consumed,
          threshold < logDensity
            ((right + width) + (index : ℝ) * width) := by
        intro index hindex
        convert hinside (index + 1) (Nat.succ_lt_succ hindex) using 1
        push_cast
        ring_nf
      convert ih (right := right + width) htail using 1
      push_cast
      ring_nf

/-- Two left expansions with shifted aligned starts and correspondingly
shifted budgets stop at the same endpoint once the extra intervening grid
points are certified inside the slice. -/
theorem expandLeft_eq_of_aligned_shift
    (logDensity : ℝ → ℝ) (threshold width oldLeft newLeft : ℝ)
    (extra oldSteps newSteps : ℕ)
    (hstart : newLeft = oldLeft - (extra : ℝ) * width)
    (hsteps : oldSteps = extra + newSteps)
    (hinside : ∀ index < extra,
      threshold < logDensity (oldLeft - (index : ℝ) * width)) :
    expandLeft logDensity threshold width oldSteps oldLeft =
      expandLeft logDensity threshold width newSteps newLeft := by
  subst oldSteps
  subst newLeft
  exact expandLeft_add_consumed logDensity threshold width oldLeft
    extra newSteps hinside

/-- Right-expansion counterpart of `expandLeft_eq_of_aligned_shift`. -/
theorem expandRight_eq_of_aligned_shift
    (logDensity : ℝ → ℝ) (threshold width oldRight newRight : ℝ)
    (extra oldSteps newSteps : ℕ)
    (hstart : newRight = oldRight + (extra : ℝ) * width)
    (hsteps : oldSteps = extra + newSteps)
    (hinside : ∀ index < extra,
      threshold < logDensity (oldRight + (index : ℝ) * width)) :
    expandRight logDensity threshold width oldSteps oldRight =
      expandRight logDensity threshold width newSteps newRight := by
  subst oldSteps
  subst newRight
  exact expandRight_add_consumed logDensity threshold width oldRight
    extra newSteps hinside

/-! ### Stopped stepping-out under allocation rerooting -/

/-- Left endpoint of the initial width-sized aligned bracket. -/
noncomputable def initialLeft (width current offset : ℝ) : ℝ :=
  current - width * offset

/-- Right endpoint of the initial width-sized aligned bracket. -/
noncomputable def initialRight (width current offset : ℝ) : ℝ :=
  initialLeft width current offset + width

/-- Rerooting translates the initial left endpoint by exactly the integer grid
shift encoded by Neal's fractional offset reversal. -/
theorem initialLeft_reverseOffset
    {width old new offset : ℝ} (hwidth : width ≠ 0) :
    initialLeft width new (reverseOffset width old new offset) =
      initialLeft width old offset +
        width * alignmentShift width old new offset := by
  have hmax := maximalLeftEndpoint_reverse
    (width := width) (old := old) (new := new) (offset := offset)
    (allocation := 0) hwidth
  simp only [initialLeft]
  linarith

theorem initialRight_reverseOffset
    {width old new offset : ℝ} (hwidth : width ≠ 0) :
    initialRight width new (reverseOffset width old new offset) =
      initialRight width old offset +
        width * alignmentShift width old new offset := by
  rw [initialRight, initialRight, initialLeft_reverseOffset hwidth]
  ring

/-- The actually stopped left endpoint is unchanged by rerooting a valid
allocation. The two hypotheses are the exact interior-grid obligations for
the two possible signs of the integer displacement. -/
theorem expandLeft_reverseAllocation
    (logDensity : ℝ → ℝ) (threshold : ℝ)
    {width old new offset : ℝ} (hwidth : width ≠ 0)
    {intervals : ℕ} {shift : ℤ}
    (hshift : shift = ⌊offset + (new - old) / width⌋)
    (allocation : ValidAllocation intervals shift)
    (hinsideNonneg : 0 ≤ shift → ∀ index < shift.toNat,
      threshold < logDensity
        (initialLeft width new (reverseOffset width old new offset) -
          (index : ℝ) * width))
    (hinsideNonpos : shift ≤ 0 → ∀ index < (-shift).toNat,
      threshold < logDensity
        (initialLeft width old offset - (index : ℝ) * width)) :
    expandLeft logDensity threshold width (allocationSteps allocation)
        (initialLeft width old offset) =
      expandLeft logDensity threshold width
        (allocationSteps (reverseAllocation intervals shift allocation))
        (initialLeft width new (reverseOffset width old new offset)) := by
  have hshiftReal : (shift : ℝ) = alignmentShift width old new offset := by
    rw [alignmentShift_eq_floor hwidth, hshift]
  have hstart := initialLeft_reverseOffset
    (width := width) (old := old) (new := new) (offset := offset) hwidth
  by_cases hsign : 0 ≤ shift
  · symm
    apply expandLeft_eq_of_aligned_shift logDensity threshold width
      (initialLeft width new (reverseOffset width old new offset))
      (initialLeft width old offset) shift.toNat
      (allocationSteps (reverseAllocation intervals shift allocation))
      (allocationSteps allocation)
    · rw [hstart, ← hshiftReal]
      have hshiftNat : (shift.toNat : ℝ) = (shift : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hsign
      rw [hshiftNat]
      ring
    · rw [allocationSteps_reverse_of_nonneg hsign]
      omega
    · exact hinsideNonneg hsign
  · have hsign' : shift ≤ 0 := le_of_not_ge hsign
    apply expandLeft_eq_of_aligned_shift logDensity threshold width
      (initialLeft width old offset)
      (initialLeft width new (reverseOffset width old new offset))
      (-shift).toNat (allocationSteps allocation)
      (allocationSteps (reverseAllocation intervals shift allocation))
    · rw [hstart, ← hshiftReal]
      have hshiftNat : ((-shift).toNat : ℝ) = ((-shift : ℤ) : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg (neg_nonneg.mpr hsign')
      rw [hshiftNat]
      push_cast
      ring
    · simpa [add_comm] using
        allocationSteps_eq_reverse_add_of_nonpos hsign' allocation
    · exact hinsideNonpos hsign'

/-- The actually stopped right endpoint is likewise unchanged. Its budget
changes oppositely because the valid allocation splits one fixed total number
of expansion steps between the two bracket sides. -/
theorem expandRight_reverseAllocation
    (logDensity : ℝ → ℝ) (threshold : ℝ)
    {width old new offset : ℝ} (hwidth : width ≠ 0)
    {intervals : ℕ} {shift : ℤ}
    (hshift : shift = ⌊offset + (new - old) / width⌋)
    (allocation : ValidAllocation intervals shift)
    (hinsideNonneg : 0 ≤ shift → ∀ index < shift.toNat,
      threshold < logDensity
        (initialRight width old offset + (index : ℝ) * width))
    (hinsideNonpos : shift ≤ 0 → ∀ index < (-shift).toNat,
      threshold < logDensity
        (initialRight width new (reverseOffset width old new offset) +
          (index : ℝ) * width)) :
    expandRight logDensity threshold width
        (allocationRightSteps allocation) (initialRight width old offset) =
      expandRight logDensity threshold width
        (allocationRightSteps (reverseAllocation intervals shift allocation))
        (initialRight width new (reverseOffset width old new offset)) := by
  have hshiftReal : (shift : ℝ) = alignmentShift width old new offset := by
    rw [alignmentShift_eq_floor hwidth, hshift]
  have hstart := initialRight_reverseOffset
    (width := width) (old := old) (new := new) (offset := offset) hwidth
  by_cases hsign : 0 ≤ shift
  · apply expandRight_eq_of_aligned_shift logDensity threshold width
      (initialRight width old offset)
      (initialRight width new (reverseOffset width old new offset))
      shift.toNat (allocationRightSteps allocation)
      (allocationRightSteps (reverseAllocation intervals shift allocation))
    · rw [hstart, ← hshiftReal]
      have hshiftNat : (shift.toNat : ℝ) = (shift : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hsign
      rw [hshiftNat]
      ring
    · exact allocationRightSteps_eq_reverse_add_of_nonneg hsign allocation
    · exact hinsideNonneg hsign
  · have hsign' : shift ≤ 0 := le_of_not_ge hsign
    symm
    apply expandRight_eq_of_aligned_shift logDensity threshold width
      (initialRight width new (reverseOffset width old new offset))
      (initialRight width old offset) (-shift).toNat
      (allocationRightSteps (reverseAllocation intervals shift allocation))
      (allocationRightSteps allocation)
    · rw [hstart, ← hshiftReal]
      have hshiftNat : ((-shift).toNat : ℝ) = ((-shift : ℤ) : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg (neg_nonneg.mpr hsign')
      rw [hshiftNat]
      push_cast
      ring
    · exact allocationRightSteps_reverse_eq_add_of_nonpos hsign' allocation
    · exact hinsideNonpos hsign'

/-- The complete stopped stepping-out bracket for a valid allocation. -/
noncomputable def steppedBracket (logDensity : ℝ → ℝ) (threshold width current offset : ℝ)
    {intervals : ℕ} {shift : ℤ} (allocation : ValidAllocation intervals shift) :
    ℝ × ℝ :=
  (expandLeft logDensity threshold width (allocationSteps allocation)
      (initialLeft width current offset),
    expandRight logDensity threshold width (allocationRightSteps allocation)
      (initialRight width current offset))

/-- Neal's offset/allocation rerooting produces exactly the same actually
stopped bracket, provided the finite intervening aligned endpoints are inside
the sampled slice. This closes the recursive stepping-out equality itself;
the hypotheses are subsequently packaged into the successful-trace set. -/
theorem steppedBracket_reverseAllocation
    (logDensity : ℝ → ℝ) (threshold : ℝ)
    {width old new offset : ℝ} (hwidth : width ≠ 0)
    {intervals : ℕ} {shift : ℤ}
    (hshift : shift = ⌊offset + (new - old) / width⌋)
    (allocation : ValidAllocation intervals shift)
    (hleftNonneg : 0 ≤ shift → ∀ index < shift.toNat,
      threshold < logDensity
        (initialLeft width new (reverseOffset width old new offset) -
          (index : ℝ) * width))
    (hleftNonpos : shift ≤ 0 → ∀ index < (-shift).toNat,
      threshold < logDensity
        (initialLeft width old offset - (index : ℝ) * width))
    (hrightNonneg : 0 ≤ shift → ∀ index < shift.toNat,
      threshold < logDensity
        (initialRight width old offset + (index : ℝ) * width))
    (hrightNonpos : shift ≤ 0 → ∀ index < (-shift).toNat,
      threshold < logDensity
        (initialRight width new (reverseOffset width old new offset) +
          (index : ℝ) * width)) :
    steppedBracket logDensity threshold width old offset allocation =
      steppedBracket logDensity threshold width new
        (reverseOffset width old new offset)
        (reverseAllocation intervals shift allocation) := by
  apply Prod.ext
  · exact expandLeft_reverseAllocation logDensity threshold hwidth hshift
      allocation hleftNonneg hleftNonpos
  · exact expandRight_reverseAllocation logDensity threshold hwidth hshift
      allocation hrightNonneg hrightNonpos

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

/-- Lebesgue density of a finite sequence of rejected shrink points. Each
point must lie in the current bracket and below the sampled log height; its
conditional uniform density is the reciprocal bracket width. -/
noncomputable def rejectedTraceWeight (logDensity : ℝ → ℝ) (threshold current : ℝ) :
    List ℝ → (ℝ × ℝ) → ENNReal
  | [], _ => 1
  | rejected :: remaining, bracket =>
      if rejected ∈ Set.Ico bracket.1 bracket.2 ∧
          logDensity rejected < threshold then
        ENNReal.ofReal (bracket.2 - bracket.1)⁻¹ *
          rejectedTraceWeight logDensity threshold current remaining
            (shrinkBracket current rejected bracket)
      else 0

/-- Replaying same-side rejected points from either possible endpoint has
exactly the same finite conditional density. -/
theorem rejectedTraceWeight_eq_of_sameSide
    (logDensity : ℝ → ℝ) (threshold : ℝ)
    {old new : ℝ} {rejected : List ℝ} {bracket : ℝ × ℝ}
    (hsame : ∀ point ∈ rejected, (point < old) = (point < new)) :
    rejectedTraceWeight logDensity threshold old rejected bracket =
      rejectedTraceWeight logDensity threshold new rejected bracket := by
  induction rejected generalizing bracket with
  | nil => rfl
  | cons point remaining ih =>
      simp only [rejectedTraceWeight]
      split
      · congr 1
        rw [shrinkBracket_eq_of_sameSide (hsame point (by simp))]
        apply ih
        intro candidate hcandidate
        exact hsame candidate (by simp [hcandidate])
      · rfl

/-- The bracket and density after all rejected points agree simultaneously in
the two directions. -/
theorem rejectedTrace_reversal_data
    (logDensity : ℝ → ℝ) (threshold : ℝ)
    {old new : ℝ} {rejected : List ℝ} {bracket : ℝ × ℝ}
    (hsame : ∀ point ∈ rejected, (point < old) = (point < new)) :
    shrinkRejectedPoints old rejected bracket =
        shrinkRejectedPoints new rejected bracket ∧
      rejectedTraceWeight logDensity threshold old rejected bracket =
        rejectedTraceWeight logDensity threshold new rejected bracket :=
  ⟨shrinkRejectedPoints_eq_of_sameSide hsame,
    rejectedTraceWeight_eq_of_sameSide logDensity threshold hsame⟩

/-- Conditional density of the final accepted point after shrinkage. -/
noncomputable def acceptedPointWeight (logDensity : ℝ → ℝ) (threshold point : ℝ)
    (bracket : ℝ × ℝ) : ENNReal :=
  if point ∈ Set.Ico bracket.1 bracket.2 ∧ threshold ≤ logDensity point then
    ENNReal.ofReal (bracket.2 - bracket.1)⁻¹
  else 0

/-- Joint point-coordinate density of all rejected points followed by one
accepted point. -/
noncomputable def shrinkTraceWeight (logDensity : ℝ → ℝ) (threshold current : ℝ)
    (rejected : List ℝ) (accepted : ℝ) (bracket : ℝ × ℝ) : ENNReal :=
  rejectedTraceWeight logDensity threshold current rejected bracket *
    acceptedPointWeight logDensity threshold accepted
      (shrinkRejectedPoints current rejected bracket)

/-- Complete finite shrink-trace likelihood is symmetric between its old and
new accepted endpoints whenever no rejected point separates them. -/
theorem shrinkTraceWeight_symmetric
    (logDensity : ℝ → ℝ) (threshold : ℝ)
    {old new : ℝ} {rejected : List ℝ} {bracket : ℝ × ℝ}
    (hsame : ∀ point ∈ rejected, (point < old) = (point < new))
    (hold : old ∈ Set.Ico
        (shrinkRejectedPoints old rejected bracket).1
        (shrinkRejectedPoints old rejected bracket).2 ∧
      threshold ≤ logDensity old)
    (hnew : new ∈ Set.Ico
        (shrinkRejectedPoints old rejected bracket).1
        (shrinkRejectedPoints old rejected bracket).2 ∧
      threshold ≤ logDensity new) :
    shrinkTraceWeight logDensity threshold old rejected new bracket =
      shrinkTraceWeight logDensity threshold new rejected old bracket := by
  have hbracket := shrinkRejectedPoints_eq_of_sameSide
    (bracket := bracket) hsame
  have hweight := rejectedTraceWeight_eq_of_sameSide
    logDensity threshold (bracket := bracket) hsame
  unfold shrinkTraceWeight acceptedPointWeight
  rw [hweight, ← hbracket]
  simp [hold, hnew]

/-- End-to-end pointwise likelihood symmetry for a successful bounded
stepping-out/shrinkage trace. The stopped-bracket theorem discharges the only
algorithmic mismatch between the two rerootings; the rejected and accepted
point densities then agree exactly. -/
theorem successfulSteppingShrinkTraceWeight_symmetric
    (logDensity : ℝ → ℝ) (threshold : ℝ)
    {width old new offset : ℝ} (hwidth : width ≠ 0)
    {intervals : ℕ} {shift : ℤ}
    (hshift : shift = ⌊offset + (new - old) / width⌋)
    (allocation : ValidAllocation intervals shift)
    (hleftNonneg : 0 ≤ shift → ∀ index < shift.toNat,
      threshold < logDensity
        (initialLeft width new (reverseOffset width old new offset) -
          (index : ℝ) * width))
    (hleftNonpos : shift ≤ 0 → ∀ index < (-shift).toNat,
      threshold < logDensity
        (initialLeft width old offset - (index : ℝ) * width))
    (hrightNonneg : 0 ≤ shift → ∀ index < shift.toNat,
      threshold < logDensity
        (initialRight width old offset + (index : ℝ) * width))
    (hrightNonpos : shift ≤ 0 → ∀ index < (-shift).toNat,
      threshold < logDensity
        (initialRight width new (reverseOffset width old new offset) +
          (index : ℝ) * width))
    {rejected : List ℝ}
    (hsame : ∀ point ∈ rejected, (point < old) = (point < new))
    (hold : old ∈ Set.Ico
        (shrinkRejectedPoints old rejected
          (steppedBracket logDensity threshold width old offset allocation)).1
        (shrinkRejectedPoints old rejected
          (steppedBracket logDensity threshold width old offset allocation)).2 ∧
      threshold ≤ logDensity old)
    (hnew : new ∈ Set.Ico
        (shrinkRejectedPoints old rejected
          (steppedBracket logDensity threshold width old offset allocation)).1
        (shrinkRejectedPoints old rejected
          (steppedBracket logDensity threshold width old offset allocation)).2 ∧
      threshold ≤ logDensity new) :
    shrinkTraceWeight logDensity threshold old rejected new
        (steppedBracket logDensity threshold width old offset allocation) =
      shrinkTraceWeight logDensity threshold new rejected old
        (steppedBracket logDensity threshold width new
          (reverseOffset width old new offset)
          (reverseAllocation intervals shift allocation)) := by
  have hbracket := steppedBracket_reverseAllocation logDensity threshold
    hwidth hshift allocation hleftNonneg hleftNonpos hrightNonneg hrightNonpos
  rw [← hbracket]
  exact shrinkTraceWeight_symmetric logDensity threshold hsame hold hnew

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

/-- Reversal on one successful trace stratum: translate the Haar alignment,
reroot the finite expansion allocation, and swap old/accepted proposal
coordinates inside their common stopped bracket. -/
noncomputable def successfulTraceStratumReverse
    (intervals : ℕ) (shift : ℤ) (width old new left right : ℝ)
    (trace : (Alignment × ValidAllocation intervals shift) × (ℝ × ℝ)) :
    (Alignment × ValidAllocation intervals (-shift)) × (ℝ × ℝ) :=
  ((reverseAlignment width old new trace.1.1,
      reverseAllocation intervals shift trace.1.2),
    acceptedProposalReverse left right trace.2)

/-- The complete alignment/allocation/accepted-point reversal preserves the
restricted product law on each fixed stopped-bracket stratum. This combines
the continuous Haar, discrete counting, and planar restricted-volume pieces
that were previously available only as separate lemmas. -/
theorem successfulTraceStratumReverse_measurePreserving
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (threshold : ℝ) (intervals : ℕ) (shift : ℤ)
    (width old new : ℝ) {left right : ℝ} (hwidth : left < right) :
    MeasurePreserving
      (successfulTraceStratumReverse intervals shift width old new left right)
      (((volume : Measure Alignment).prod
          (Measure.count : Measure (ValidAllocation intervals shift))).prod
        (((volume : Measure ℝ).prod volume).restrict
          (acceptedProposalSuccess logDensity threshold left right)))
      (((volume : Measure Alignment).prod
          (Measure.count : Measure (ValidAllocation intervals (-shift)))).prod
        (((volume : Measure ℝ).prod volume).restrict
          (acceptedProposalSuccess logDensity threshold left right))) := by
  have hfirst := (reverseAlignment_measurePreserving width old new).prod
    (reverseAllocation_measurePreserving intervals shift)
  have hall := hfirst.prod
    (acceptedProposalReverse_restrict_measurePreserving hlogDensity threshold hwidth)
  convert hall using 1
  funext trace
  rfl

/-- Lift any density on the old/proposed pair to current-point/uniform-fraction
coordinates in a fixed bracket. -/
noncomputable def acceptedProposalPairDensity (left right : ℝ)
    (pairDensity : ℝ × ℝ → ENNReal) (point : ℝ × ℝ) : ENNReal :=
  pairDensity (point.1, left + (right - left) * point.2)

theorem measurable_acceptedProposalPairDensity
    {pairDensity : ℝ × ℝ → ENNReal} (hpairDensity : Measurable pairDensity)
    (left right : ℝ) :
    Measurable (acceptedProposalPairDensity left right pairDensity) := by
  exact hpairDensity.comp <|
    measurable_fst.prodMk
      (measurable_const.add
        ((measurable_const.sub measurable_const).mul measurable_snd))

theorem acceptedProposalPairDensity_invariant
    {left right : ℝ} (hwidth : left < right)
    (pairDensity : ℝ × ℝ → ENNReal)
    (hsymmetric : ∀ old new, pairDensity (old, new) = pairDensity (new, old))
    (point : ℝ × ℝ) :
    acceptedProposalPairDensity left right pairDensity
        (acceptedProposalReverse left right point) =
      acceptedProposalPairDensity left right pairDensity point := by
  have hrecover :
      left + (right - left) * ((point.1 - left) / (right - left)) = point.1 := by
    field_simp [sub_ne_zero.mpr hwidth.ne']
    ring
  simp only [acceptedProposalPairDensity, acceptedProposalReverse_fst,
    acceptedProposalReverse_snd]
  rw [hrecover]
  exact hsymmetric _ _

/-- Consequently the accepted-proposal reversal preserves every measurable
symmetric old/new density, not only unweighted planar volume. -/
theorem acceptedProposalReverse_withDensity_measurePreserving
    {left right : ℝ} (hwidth : left < right)
    {pairDensity : ℝ × ℝ → ENNReal} (hpairDensity : Measurable pairDensity)
    (hsymmetric : ∀ old new, pairDensity (old, new) = pairDensity (new, old)) :
    MeasurePreserving (acceptedProposalReverse left right)
      (((volume : Measure ℝ).prod volume).withDensity
        (acceptedProposalPairDensity left right pairDensity))
      (((volume : Measure ℝ).prod volume).withDensity
        (acceptedProposalPairDensity left right pairDensity)) := by
  apply measurePreserving_withDensity_of_invariant
    (acceptedProposalReverse_measurePreserving (sub_ne_zero.mpr hwidth.ne'))
    (measurable_acceptedProposalPairDensity hpairDensity left right)
  exact acceptedProposalPairDensity_invariant hwidth pairDensity hsymmetric

/-- Weighted successful-trace stratum theorem. Any measurable old/new trace
likelihood proved symmetric by the stepping-out/shrinkage lemmas can be used
as `pairDensity`; the Haar alignment and finite allocation law are then
preserved simultaneously with that likelihood. -/
theorem successfulTraceStratumReverse_withDensity_measurePreserving
    (intervals : ℕ) (shift : ℤ) (width old new : ℝ)
    {left right : ℝ} (hwidth : left < right)
    {pairDensity : ℝ × ℝ → ENNReal} (hpairDensity : Measurable pairDensity)
    (hsymmetric : ∀ old new, pairDensity (old, new) = pairDensity (new, old)) :
    MeasurePreserving
      (successfulTraceStratumReverse intervals shift width old new left right)
      (((volume : Measure Alignment).prod
          (Measure.count : Measure (ValidAllocation intervals shift))).prod
        (((volume : Measure ℝ).prod volume).withDensity
          (acceptedProposalPairDensity left right pairDensity)))
      (((volume : Measure Alignment).prod
          (Measure.count : Measure (ValidAllocation intervals (-shift)))).prod
        (((volume : Measure ℝ).prod volume).withDensity
          (acceptedProposalPairDensity left right pairDensity))) := by
  have hfirst := (reverseAlignment_measurePreserving width old new).prod
    (reverseAllocation_measurePreserving intervals shift)
  have hall := hfirst.prod
    (acceptedProposalReverse_withDensity_measurePreserving hwidth hpairDensity
      hsymmetric)
  convert hall using 1
  funext trace
  rfl

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
