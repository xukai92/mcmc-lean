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
open Function

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

/-- A measure-preserving map between different spaces transports two
measurable densities when their values agree pointwise along the map. -/
theorem measurePreserving_withDensity_of_map_invariant
    {Source Target : Type*} [MeasurableSpace Source] [MeasurableSpace Target]
    {sourceMeasure : Measure Source} {targetMeasure : Measure Target}
    {transform : Source → Target}
    {sourceDensity : Source → ENNReal} {targetDensity : Target → ENNReal}
    (htransform : MeasurePreserving transform sourceMeasure targetMeasure)
    (htargetDensity : Measurable targetDensity)
    (hinvariant : ∀ point, targetDensity (transform point) = sourceDensity point) :
    MeasurePreserving transform
      (sourceMeasure.withDensity sourceDensity)
      (targetMeasure.withDensity targetDensity) := by
  refine ⟨htransform.measurable, ?_⟩
  ext event hevent
  rw [Measure.map_apply htransform.measurable hevent,
    withDensity_apply _ (htransform.measurable hevent),
    withDensity_apply _ hevent,
    ← lintegral_indicator (htransform.measurable hevent),
    ← lintegral_indicator hevent,
    ← htransform.lintegral_comp (htargetDensity.indicator hevent)]
  apply lintegral_congr
  intro point
  by_cases hmem : transform point ∈ event
  · have hpreimage : point ∈ transform ⁻¹' event := hmem
    simp [Set.indicator, hmem, hpreimage, hinvariant]
  · have hpreimage : point ∉ transform ⁻¹' event := hmem
    simp [Set.indicator, hmem, hpreimage]

/-- A checked identity fallback can be lifted through a density without any
separate argument for the failure branch. It suffices that the raw base law is
preserved on the success restriction and that the density agrees there; off
the success set both state and density are unchanged definitionally. -/
theorem guardedTraceTransform_withDensity_measurePreserving
    {Space : Type*} [MeasurableSpace Space]
    (measure : Measure Space) (success : Set Space)
    (hsuccess : MeasurableSet success) (transform : Space → Space)
    (htransform : Measurable transform) (density : Space → ENNReal)
    (hdensity : Measurable density)
    (hbase : MeasurePreserving transform
      (measure.restrict success) (measure.restrict success))
    (hinvariant : ∀ point ∈ success,
      density (transform point) = density point) :
    MeasurePreserving (Mcmc.Kernel.guardedTraceTransform success transform)
      (measure.withDensity density) (measure.withDensity density) := by
  have hguardedBase := Mcmc.Kernel.guardedTraceTransform_measurePreserving
    measure success hsuccess transform htransform hbase
  apply measurePreserving_withDensity_of_invariant hguardedBase hdensity
  intro point
  by_cases hpoint : point ∈ success
  · simpa [Mcmc.Kernel.guardedTraceTransform, hpoint] using
      hinvariant point hpoint
  · simp [Mcmc.Kernel.guardedTraceTransform, hpoint]

/-- Glue a countable disjoint family of restricted preservation theorems.
This is the measure-theoretic engine for algorithms whose execution trace
selects one of countably many affine replay strata. -/
theorem measurePreserving_restrict_iUnion
    {Space Index : Type*} [MeasurableSpace Space] [Countable Index]
    (measure : Measure Space) (pieces : Index → Set Space)
    (hmeasurable : ∀ index, MeasurableSet (pieces index))
    (hdisjoint : Pairwise (Disjoint on pieces))
    (transform : Space → Space) (htransform : Measurable transform)
    (hpiece : ∀ index, MeasurePreserving transform
      (measure.restrict (pieces index)) (measure.restrict (pieces index))) :
    MeasurePreserving transform (measure.restrict (⋃ index, pieces index))
      (measure.restrict (⋃ index, pieces index)) := by
  refine ⟨htransform, ?_⟩
  rw [Measure.restrict_iUnion hdisjoint hmeasurable]
  rw [Measure.map_sum htransform.aemeasurable]
  apply congrArg Measure.sum
  funext index
  exact (hpiece index).map_eq

/-- Source/target version of `measurePreserving_restrict_iUnion`. The same
index may describe different forward and reverse replay signatures, provided
both families disjointly cover their respective successful domains. -/
theorem measurePreserving_restrict_iUnion₂
    {Source Target Index : Type*}
    [MeasurableSpace Source] [MeasurableSpace Target] [Countable Index]
    (sourceMeasure : Measure Source) (targetMeasure : Measure Target)
    (sourcePieces : Index → Set Source) (targetPieces : Index → Set Target)
    (hsourceMeasurable : ∀ index, MeasurableSet (sourcePieces index))
    (htargetMeasurable : ∀ index, MeasurableSet (targetPieces index))
    (hsourceDisjoint : Pairwise (Disjoint on sourcePieces))
    (htargetDisjoint : Pairwise (Disjoint on targetPieces))
    (transform : Source → Target) (htransform : Measurable transform)
    (hpiece : ∀ index, MeasurePreserving transform
      (sourceMeasure.restrict (sourcePieces index))
      (targetMeasure.restrict (targetPieces index))) :
    MeasurePreserving transform
      (sourceMeasure.restrict (⋃ index, sourcePieces index))
      (targetMeasure.restrict (⋃ index, targetPieces index)) := by
  refine ⟨htransform, ?_⟩
  rw [Measure.restrict_iUnion hsourceDisjoint hsourceMeasurable,
    Measure.restrict_iUnion htargetDisjoint htargetMeasurable]
  rw [Measure.map_sum htransform.aemeasurable]
  apply congrArg Measure.sum
  funext index
  exact (hpiece index).map_eq

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

theorem measurable_alignmentCoordinate : Measurable alignmentCoordinate := by
  exact measurable_subtype_coe.comp
    (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable

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

/-- Haar offsets whose rerooting displacement is one fixed integer. These
sets are the genuine dependent indices for the finite allocation types. -/
def alignmentShiftStratum (width old new : ℝ) (shift : ℤ) : Set Alignment :=
  {offset | alignmentShift width old new (alignmentCoordinate offset) = shift}

theorem measurable_alignmentShift (width old new : ℝ) :
    Measurable (alignmentShift width old new) := by
  unfold alignmentShift
  exact (measurable_const.div measurable_const |>.sub
      (measurable_reverseOffset width old new)).sub
    ((measurable_const.div measurable_const).sub measurable_id)

theorem measurableSet_alignmentShiftStratum
    (width old new : ℝ) (shift : ℤ) :
    MeasurableSet (alignmentShiftStratum width old new shift) := by
  exact measurableSet_eq_fun
    ((measurable_alignmentShift width old new).comp measurable_alignmentCoordinate)
    measurable_const

/-- Alignment reversal exchanges the shift stratum with its negation. -/
theorem reverseAlignment_preimage_alignmentShiftStratum
    {width old new : ℝ} (hwidth : width ≠ 0) (shift : ℤ) :
    reverseAlignment width old new ⁻¹'
        alignmentShiftStratum width new old (-shift) =
      alignmentShiftStratum width old new shift := by
  ext offset
  simp only [Set.mem_preimage, alignmentShiftStratum, Set.mem_setOf_eq,
    alignmentCoordinate_reverseAlignment]
  rw [alignmentShift_reverse hwidth (alignmentCoordinate_mem offset)]
  push_cast
  constructor <;> intro h
  · linarith
  · linarith

/-- Haar translation preserves the restricted alignment law while changing
the dependent allocation index from `shift` to `-shift`. -/
theorem reverseAlignment_restrict_stratum_measurePreserving
    {width old new : ℝ} (hwidth : width ≠ 0) (shift : ℤ) :
    MeasurePreserving (reverseAlignment width old new)
      ((volume : Measure Alignment).restrict
        (alignmentShiftStratum width old new shift))
      ((volume : Measure Alignment).restrict
        (alignmentShiftStratum width new old (-shift))) := by
  have h := (reverseAlignment_measurePreserving width old new).restrict_preimage
    (measurableSet_alignmentShiftStratum width new old (-shift))
  simpa [reverseAlignment_preimage_alignmentShiftStratum hwidth shift] using h

/-- The integer alignment-shift strata are a measurable partition of Haar
alignment space. Hence summing their restricted laws recovers the original
uniform alignment law exactly. -/
theorem sum_restrict_alignmentShiftStratum
    {width old new : ℝ} (hwidth : width ≠ 0) :
    Measure.sum (fun shift : ℤ =>
      (volume : Measure Alignment).restrict
        (alignmentShiftStratum width old new shift)) = volume := by
  have hdisjoint : Pairwise (Disjoint on
      fun shift : ℤ => alignmentShiftStratum width old new shift) := by
    intro first second hne
    change Disjoint (alignmentShiftStratum width old new first)
      (alignmentShiftStratum width old new second)
    rw [Set.disjoint_left]
    intro offset hfirst hsecond
    have heq : (first : ℝ) = (second : ℝ) := by
      exact hfirst.symm.trans hsecond
    exact hne (Int.cast_injective heq)
  have hcover : (⋃ shift : ℤ,
      alignmentShiftStratum width old new shift) = Set.univ := by
    ext offset
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    refine ⟨⌊alignmentCoordinate offset + (new - old) / width⌋, ?_⟩
    exact alignmentShift_eq_floor hwidth
  rw [← Measure.restrict_iUnion hdisjoint
    (measurableSet_alignmentShiftStratum width old new), hcover,
    Measure.restrict_univ]

/-- The integer grid displacement attached to a circle-valued alignment.
Unlike `alignmentShift`, this is the runtime index used to translate the
counting-measure allocation coordinate. -/
noncomputable def integerAlignmentShift
    (width old new : ℝ) (offset : Alignment) : ℤ :=
  ⌊alignmentCoordinate offset + (new - old) / width⌋

theorem measurable_integerAlignmentShift (width old new : ℝ) :
    Measurable (integerAlignmentShift width old new) := by
  exact Int.measurable_floor.comp
    (measurable_alignmentCoordinate.add measurable_const)

theorem cast_integerAlignmentShift
    {width old new : ℝ} (hwidth : width ≠ 0) (offset : Alignment) :
    (integerAlignmentShift width old new offset : ℝ) =
      alignmentShift width old new (alignmentCoordinate offset) := by
  exact (alignmentShift_eq_floor hwidth).symm

/-- Rerooting reverses the integer displacement, not merely its real-valued
embedding. This is the cancellation law needed by the global allocation
coordinate. -/
theorem integerAlignmentShift_reverse
    {width old new : ℝ} (hwidth : width ≠ 0) (offset : Alignment) :
    integerAlignmentShift width new old
        (reverseAlignment width old new offset) =
      -integerAlignmentShift width old new offset := by
  apply Int.cast_injective (α := ℝ)
  rw [cast_integerAlignmentShift hwidth
      (reverseAlignment width old new offset),
    Int.cast_neg, cast_integerAlignmentShift hwidth offset,
    alignmentCoordinate_reverseAlignment,
    alignmentShift_reverse hwidth (alignmentCoordinate_mem offset)]

/-- Simultaneously reroot the uniform grid alignment and translate its
unbounded integer allocation coordinate. Restricting this ambient map to the
finite valid-allocation event will recover the practical algorithm. -/
noncomputable def alignmentAllocationReverse
    (width old new : ℝ) (point : Alignment × ℤ) : Alignment × ℤ :=
  (reverseAlignment width old new point.1,
    point.2 + integerAlignmentShift width old new point.1)

/-- Haar alignment volume times integer counting measure is invariant under
the state-dependent grid rerooting. This global theorem packages the
countable shift-stratum sum as a single skew-product statement. -/
theorem alignmentAllocationReverse_measurePreserving (width old new : ℝ) :
    MeasurePreserving (alignmentAllocationReverse width old new)
      ((volume : Measure Alignment).prod (Measure.count : Measure ℤ))
      ((volume : Measure Alignment).prod (Measure.count : Measure ℤ)) := by
  refine (reverseAlignment_measurePreserving width old new).skew_product
    (g := fun offset allocation =>
      allocation + integerAlignmentShift width old new offset) ?_ ?_
  · exact measurable_snd.add
      ((measurable_integerAlignmentShift width old new).comp measurable_fst)
  · filter_upwards [] with offset
    exact map_add_right_eq_self Measure.count
      (integerAlignmentShift width old new offset)

/-- Joint measurability when both endpoint states vary. This is needed by the
actual augmented slice transform, where the proposed endpoint is computed
from the accepted fraction. -/
theorem measurable_alignmentAllocationReverse_parameterized (width : ℝ) :
    Measurable (fun point : (ℝ × ℝ) × (Alignment × ℤ) =>
      alignmentAllocationReverse width point.1.1 point.1.2 point.2) := by
  have htranslation : Measurable (fun point : (ℝ × ℝ) × (Alignment × ℤ) =>
      ((((point.1.2 - point.1.1) / width : ℝ) : Alignment) + point.2.1)) := by
    exact (AddCircle.measurable_mk'.comp
      ((measurable_snd.comp measurable_fst).sub
        (measurable_fst.comp measurable_fst) |>.div measurable_const)).add
      (measurable_fst.comp measurable_snd)
  have hshift : Measurable (fun point : (ℝ × ℝ) × (Alignment × ℤ) =>
      integerAlignmentShift width point.1.1 point.1.2 point.2.1) := by
    unfold integerAlignmentShift
    exact Int.measurable_floor.comp
      (((measurable_alignmentCoordinate.comp
          (measurable_fst.comp measurable_snd)).add
        (((measurable_snd.comp measurable_fst).sub
          (measurable_fst.comp measurable_fst)).div measurable_const)))
  exact htranslation.prodMk
    ((measurable_snd.comp measurable_snd).add hshift)

/-- The ambient grid rerooting is an involution after exchanging the old and
new states. -/
theorem alignmentAllocationReverse_reverse
    {width old new : ℝ} (hwidth : width ≠ 0) (point : Alignment × ℤ) :
    alignmentAllocationReverse width new old
        (alignmentAllocationReverse width old new point) = point := by
  apply Prod.ext
  · apply (AddCircle.measurableEquivIco (1 : ℝ) 0).injective
    apply Subtype.ext
    change alignmentCoordinate
        (reverseAlignment width new old
          (reverseAlignment width old new point.1)) =
      alignmentCoordinate point.1
    rw [alignmentCoordinate_reverseAlignment,
      alignmentCoordinate_reverseAlignment,
      reverseOffset_reverseOffset hwidth (alignmentCoordinate_mem point.1)]
  · simp [alignmentAllocationReverse,
      integerAlignmentShift_reverse hwidth]

/-- The measurable part of the ambient alignment/allocation space on which
both the forward allocation and its rerooting lie in the configured finite
range. This is the non-dependent presentation of `ValidAllocation`. -/
def globalValidAllocation
    (intervals : ℕ) (width old new : ℝ) : Set (Alignment × ℤ) :=
  {point |
    0 ≤ point.2 ∧ point.2 < intervals ∧
    0 ≤ point.2 + integerAlignmentShift width old new point.1 ∧
      point.2 + integerAlignmentShift width old new point.1 < intervals}

theorem measurableSet_globalValidAllocation
    (intervals : ℕ) (width old new : ℝ) :
    MeasurableSet (globalValidAllocation intervals width old new) := by
  let shifted : Alignment × ℤ → ℤ := fun point =>
    point.2 + integerAlignmentShift width old new point.1
  have hshifted : Measurable shifted :=
    measurable_snd.add
      ((measurable_integerAlignmentShift width old new).comp measurable_fst)
  have hallocation : Measurable (fun point : Alignment × ℤ => point.2) :=
    measurable_snd
  have hzero : Measurable (fun _ : Alignment × ℤ => (0 : ℤ)) :=
    measurable_const
  have hbound : Measurable (fun _ : Alignment × ℤ => (intervals : ℤ)) :=
    measurable_const
  exact (measurableSet_le hzero hallocation).inter
    ((measurableSet_lt hallocation hbound).inter
      ((measurableSet_le hzero hshifted).inter
        (measurableSet_lt hshifted hbound)))

/-- The valid finite allocation event is exchanged exactly when old and new
states are exchanged. -/
theorem alignmentAllocationReverse_preimage_globalValidAllocation
    {intervals : ℕ} {width old new : ℝ} (hwidth : width ≠ 0) :
    alignmentAllocationReverse width old new ⁻¹'
        globalValidAllocation intervals width new old =
      globalValidAllocation intervals width old new := by
  ext point
  simp only [Set.mem_preimage, globalValidAllocation, Set.mem_setOf_eq,
    alignmentAllocationReverse]
  rw [integerAlignmentShift_reverse hwidth]
  omega

/-- Global grid rerooting preserves Haar × counting measure after restriction
to the bounded successful-allocation event. This is the summed counterpart of
the separate fixed-shift allocation equivalences. -/
theorem alignmentAllocationReverse_restrict_measurePreserving
    {intervals : ℕ} {width old new : ℝ} (hwidth : width ≠ 0) :
    MeasurePreserving (alignmentAllocationReverse width old new)
      (((volume : Measure Alignment).prod (Measure.count : Measure ℤ)).restrict
        (globalValidAllocation intervals width old new))
      (((volume : Measure Alignment).prod (Measure.count : Measure ℤ)).restrict
        (globalValidAllocation intervals width new old)) := by
  have h := (alignmentAllocationReverse_measurePreserving width old new).restrict_preimage
    (measurableSet_globalValidAllocation intervals width new old)
  simpa [alignmentAllocationReverse_preimage_globalValidAllocation hwidth] using h

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

/-- With nonnegative width, left stepping-out never moves its endpoint to the
right. -/
theorem expandLeft_le (logDensity : ℝ → ℝ) (threshold : ℝ)
    {width : ℝ} (hwidth : 0 ≤ width) (steps : ℕ) (left : ℝ) :
    expandLeft logDensity threshold width steps left ≤ left := by
  induction steps generalizing left with
  | zero => rfl
  | succ steps ih =>
      simp only [expandLeft]
      split
      · exact le_rfl
      · exact (ih (left - width)).trans (sub_le_self left hwidth)

/-- With nonnegative width, right stepping-out never moves its endpoint to the
left. -/
theorem le_expandRight (logDensity : ℝ → ℝ) (threshold : ℝ)
    {width : ℝ} (hwidth : 0 ≤ width) (steps : ℕ) (right : ℝ) :
    right ≤ expandRight logDensity threshold width steps right := by
  induction steps generalizing right with
  | zero => rfl
  | succ steps ih =>
      simp only [expandRight]
      split
      · exact le_rfl
      · exact (le_add_of_nonneg_right hwidth).trans (ih (right + width))

/-- Left stepping-out moves by at most its configured number of widths. -/
theorem sub_steps_mul_width_le_expandLeft
    (logDensity : ℝ → ℝ) (threshold : ℝ)
    {width : ℝ} (hwidth : 0 ≤ width) (steps : ℕ) (left : ℝ) :
    left - (steps : ℝ) * width ≤
      expandLeft logDensity threshold width steps left := by
  induction steps generalizing left with
  | zero =>
      simp [expandLeft]
  | succ steps ih =>
      simp only [expandLeft]
      split
      · push_cast
        nlinarith
      · convert ih (left - width) using 1
        push_cast
        ring

/-- Right stepping-out moves by at most its configured number of widths. -/
theorem expandRight_le_add_steps_mul_width
    (logDensity : ℝ → ℝ) (threshold : ℝ)
    {width : ℝ} (hwidth : 0 ≤ width) (steps : ℕ) (right : ℝ) :
    expandRight logDensity threshold width steps right ≤
      right + (steps : ℝ) * width := by
  induction steps generalizing right with
  | zero =>
      simp [expandRight]
  | succ steps ih =>
      simp only [expandRight]
      split
      · push_cast
        nlinarith
      · convert ih (right + width) using 1
        push_cast
        ring

/-- Reaching at least `consumed` grid cells to the left certifies that every
endpoint crossed on the way was in the strict superlevel set. -/
theorem expandLeft_crossed_inside
    (logDensity : ℝ → ℝ) (threshold : ℝ)
    {width : ℝ} (hwidth : 0 < width) {steps consumed : ℕ} (left : ℝ)
    (hconsumed : consumed ≤ steps)
    (hreached : expandLeft logDensity threshold width steps left ≤
      left - (consumed : ℝ) * width) :
    ∀ index < consumed,
      threshold < logDensity (left - (index : ℝ) * width) := by
  induction consumed generalizing steps left with
  | zero => simp
  | succ consumed ih =>
      cases steps with
      | zero =>
          omega
      | succ steps =>
          simp only [expandLeft] at hreached
          by_cases hstop : logDensity left ≤ threshold
          · rw [if_pos hstop] at hreached
            have : (0 : ℝ) < (consumed + 1) * width := by positivity
            push_cast at hreached
            nlinarith
          · rw [if_neg hstop] at hreached
            have htail : expandLeft logDensity threshold width
                steps (left - width) ≤
                (left - width) - (consumed : ℝ) * width := by
              push_cast at hreached ⊢
              nlinarith
            intro index hindex
            cases index with
            | zero => simpa using lt_of_not_ge hstop
            | succ index =>
                have hi := ih (steps := steps) (left := left - width)
                  (by omega) htail index (by omega)
                convert hi using 1
                push_cast
                ring_nf

/-- Rightward counterpart of `expandLeft_crossed_inside`. -/
theorem expandRight_crossed_inside
    (logDensity : ℝ → ℝ) (threshold : ℝ)
    {width : ℝ} (hwidth : 0 < width) {steps consumed : ℕ} (right : ℝ)
    (hconsumed : consumed ≤ steps)
    (hreached : right + (consumed : ℝ) * width ≤
      expandRight logDensity threshold width steps right) :
    ∀ index < consumed,
      threshold < logDensity (right + (index : ℝ) * width) := by
  induction consumed generalizing steps right with
  | zero => simp
  | succ consumed ih =>
      cases steps with
      | zero =>
          omega
      | succ steps =>
          simp only [expandRight] at hreached
          by_cases hstop : logDensity right ≤ threshold
          · rw [if_pos hstop] at hreached
            have : (0 : ℝ) < (consumed + 1) * width := by positivity
            push_cast at hreached
            nlinarith
          · rw [if_neg hstop] at hreached
            have htail : (right + width) + (consumed : ℝ) * width ≤
                expandRight logDensity threshold width
                  steps (right + width) := by
              push_cast at hreached ⊢
              nlinarith
            intro index hindex
            cases index with
            | zero => simpa using lt_of_not_ge hstop
            | succ index =>
                have hi := ih (steps := steps) (right := right + width)
                  (by omega) htail index (by omega)
                convert hi using 1
                push_cast
                ring_nf

/-- If a point lies strictly beyond the stopped left endpoint and at least
`consumed + 1` checked grid points to the left of the start, all those grid
points passed the superlevel test. -/
theorem expandLeft_crossed_inside_of_lt
    (logDensity : ℝ → ℝ) (threshold : ℝ)
    {width : ℝ} (hwidth : 0 < width) {steps consumed : ℕ} (left target : ℝ)
    (hsteps : consumed + 1 ≤ steps)
    (hreached : expandLeft logDensity threshold width steps left < target)
    (htarget : target ≤ left - (consumed : ℝ) * width) :
    ∀ index < consumed + 1,
      threshold < logDensity (left - (index : ℝ) * width) := by
  induction consumed generalizing steps left with
  | zero =>
      cases steps with
      | zero => omega
      | succ steps =>
          simp only [expandLeft] at hreached
          by_cases hstop : logDensity left ≤ threshold
          · rw [if_pos hstop] at hreached
            nlinarith
          · intro index hindex
            have hindexZero : index = 0 := by omega
            subst index
            simpa using lt_of_not_ge hstop
  | succ consumed ih =>
      cases steps with
      | zero => omega
      | succ steps =>
          simp only [expandLeft] at hreached
          by_cases hstop : logDensity left ≤ threshold
          · rw [if_pos hstop] at hreached
            nlinarith
          · rw [if_neg hstop] at hreached
            have htailTarget : target ≤
                (left - width) - (consumed : ℝ) * width := by
              push_cast at htarget ⊢
              nlinarith
            have htail := ih (steps := steps) (left := left - width)
              (by omega) hreached htailTarget
            intro index hindex
            cases index with
            | zero => simpa using lt_of_not_ge hstop
            | succ index =>
                have hi := htail index (by omega)
                convert hi using 1
                push_cast
                ring_nf

/-- Rightward counterpart of `expandLeft_crossed_inside_of_lt`. -/
theorem expandRight_crossed_inside_of_lt
    (logDensity : ℝ → ℝ) (threshold : ℝ)
    {width : ℝ} (hwidth : 0 < width) {steps consumed : ℕ} (right target : ℝ)
    (hsteps : consumed + 1 ≤ steps)
    (htarget : right + (consumed : ℝ) * width ≤ target)
    (hreached : target < expandRight logDensity threshold width steps right) :
    ∀ index < consumed + 1,
      threshold < logDensity (right + (index : ℝ) * width) := by
  induction consumed generalizing steps right with
  | zero =>
      cases steps with
      | zero => omega
      | succ steps =>
          simp only [expandRight] at hreached
          by_cases hstop : logDensity right ≤ threshold
          · rw [if_pos hstop] at hreached
            nlinarith
          · intro index hindex
            have hindexZero : index = 0 := by omega
            subst index
            simpa using lt_of_not_ge hstop
  | succ consumed ih =>
      cases steps with
      | zero => omega
      | succ steps =>
          simp only [expandRight] at hreached
          by_cases hstop : logDensity right ≤ threshold
          · rw [if_pos hstop] at hreached
            nlinarith
          · rw [if_neg hstop] at hreached
            have htailTarget :
                (right + width) + (consumed : ℝ) * width ≤ target := by
              push_cast at htarget ⊢
              nlinarith
            have htail := ih (steps := steps) (right := right + width)
              (by omega) htailTarget hreached
            intro index hindex
            cases index with
            | zero => simpa using lt_of_not_ge hstop
            | succ index =>
                have hi := htail index (by omega)
                convert hi using 1
                push_cast
                ring_nf

/-- Every bounded left expansion endpoint is an integral number of widths
from its start; the witness also records that the consumed count is within
the supplied budget. -/
theorem exists_expandLeft_eq_sub_nat_mul
    (logDensity : ℝ → ℝ) (threshold width left : ℝ) (steps : ℕ) :
    ∃ consumed ≤ steps,
      expandLeft logDensity threshold width steps left =
        left - (consumed : ℝ) * width := by
  induction steps generalizing left with
  | zero => exact ⟨0, le_rfl, by simp [expandLeft]⟩
  | succ steps ih =>
      simp only [expandLeft]
      by_cases hstop : logDensity left ≤ threshold
      · rw [if_pos hstop]
        exact ⟨0, Nat.zero_le _, by simp⟩
      · rw [if_neg hstop]
        obtain ⟨consumed, hconsumed, heq⟩ := ih (left - width)
        refine ⟨consumed + 1, by omega, ?_⟩
        rw [heq]
        push_cast
        ring

/-- Rightward counterpart of `exists_expandLeft_eq_sub_nat_mul`. -/
theorem exists_expandRight_eq_add_nat_mul
    (logDensity : ℝ → ℝ) (threshold width right : ℝ) (steps : ℕ) :
    ∃ consumed ≤ steps,
      expandRight logDensity threshold width steps right =
        right + (consumed : ℝ) * width := by
  induction steps generalizing right with
  | zero => exact ⟨0, le_rfl, by simp [expandRight]⟩
  | succ steps ih =>
      simp only [expandRight]
      by_cases hstop : logDensity right ≤ threshold
      · rw [if_pos hstop]
        exact ⟨0, Nat.zero_le _, by simp⟩
      · rw [if_neg hstop]
        obtain ⟨consumed, hconsumed, heq⟩ := ih (right + width)
        refine ⟨consumed + 1, by omega, ?_⟩
        rw [heq]
        push_cast
        ring

theorem nat_mul_width_injective {width : ℝ} (hwidth : width ≠ 0)
    {first second : ℕ}
    (heq : (first : ℝ) * width = (second : ℝ) * width) : first = second := by
  have hcast : (first : ℝ) = second := by
    exact mul_right_cancel₀ hwidth heq
  exact_mod_cast hcast

/-- Fixed-budget left expansion is jointly measurable in threshold and its
current endpoint. -/
theorem measurable_expandLeft
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (width : ℝ) (steps : ℕ) :
    Measurable (fun point : ℝ × ℝ =>
      expandLeft logDensity point.1 width steps point.2) := by
  induction steps with
  | zero => exact measurable_snd
  | succ steps ih =>
      simp only [expandLeft]
      exact Measurable.ite
        (measurableSet_le (hlogDensity.comp measurable_snd) measurable_fst)
        measurable_snd
        (ih.comp (measurable_fst.prodMk
          (measurable_snd.sub measurable_const)))

/-- Fixed-budget right expansion is jointly measurable in threshold and its
current endpoint. -/
theorem measurable_expandRight
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (width : ℝ) (steps : ℕ) :
    Measurable (fun point : ℝ × ℝ =>
      expandRight logDensity point.1 width steps point.2) := by
  induction steps with
  | zero => exact measurable_snd
  | succ steps ih =>
      simp only [expandRight]
      exact Measurable.ite
        (measurableSet_le (hlogDensity.comp measurable_snd) measurable_fst)
        measurable_snd
        (ih.comp (measurable_fst.prodMk
          (measurable_snd.add measurable_const)))

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

/-- Finite-dimensional presentation of rejected-point replay. This avoids a
list measurable-space detour on each fiber `Fin n → ℝ`. -/
noncomputable def shrinkRejectedVector (current : ℝ) :
    (length : ℕ) → (Fin length → ℝ) → (ℝ × ℝ) → (ℝ × ℝ)
  | 0, _, bracket => bracket
  | length + 1, rejected, bracket =>
      shrinkRejectedVector current length (fun index => rejected index.succ)
        (shrinkBracket current (rejected 0) bracket)

theorem shrinkRejectedVector_eq_shrinkRejectedPoints
    (current : ℝ) (length : ℕ) (rejected : Fin length → ℝ)
    (bracket : ℝ × ℝ) :
    shrinkRejectedVector current length rejected bracket =
      shrinkRejectedPoints current (List.ofFn rejected) bracket := by
  induction length generalizing bracket with
  | zero => simp [shrinkRejectedVector, shrinkRejectedPoints]
  | succ length ih =>
      rw [List.ofFn_succ]
      simp only [shrinkRejectedVector, shrinkRejectedPoints]
      exact ih (fun index => rejected index.succ) _

theorem measurable_shrinkBracket :
    Measurable (fun point : (ℝ × ℝ) × (ℝ × ℝ) =>
      shrinkBracket point.1.1 point.1.2 point.2) := by
  unfold shrinkBracket
  exact Measurable.ite
    (measurableSet_lt
      (measurable_snd.comp measurable_fst)
      (measurable_fst.comp measurable_fst))
    ((measurable_snd.comp measurable_fst).prodMk
      (measurable_snd.comp measurable_snd))
    ((measurable_fst.comp measurable_snd).prodMk
      (measurable_snd.comp measurable_fst))

/-- Replaying a fixed-dimensional rejected vector is jointly measurable in
the current point, rejected coordinates, and starting bracket. -/
theorem measurable_shrinkRejectedVector (length : ℕ) :
    Measurable (fun point : (ℝ × (Fin length → ℝ)) × (ℝ × ℝ) =>
      shrinkRejectedVector point.1.1 length point.1.2 point.2) := by
  induction length with
  | zero => exact measurable_snd
  | succ length ih =>
      have hcurrent : Measurable
          (fun point : (ℝ × (Fin (length + 1) → ℝ)) × (ℝ × ℝ) => point.1.1) :=
        measurable_fst.comp measurable_fst
      have hrejected : Measurable
          (fun point : (ℝ × (Fin (length + 1) → ℝ)) × (ℝ × ℝ) => point.1.2) :=
        measurable_snd.comp measurable_fst
      have hhead : Measurable
          (fun point : (ℝ × (Fin (length + 1) → ℝ)) × (ℝ × ℝ) => point.1.2 0) :=
        (measurable_pi_apply 0).comp hrejected
      have htail : Measurable
          (fun point : (ℝ × (Fin (length + 1) → ℝ)) × (ℝ × ℝ) =>
            fun index : Fin length => point.1.2 index.succ) := by
        exact measurable_pi_lambda _ fun index =>
          (measurable_pi_apply index.succ).comp hrejected
      have hupdated : Measurable
          (fun point : (ℝ × (Fin (length + 1) → ℝ)) × (ℝ × ℝ) =>
            shrinkBracket point.1.1 (point.1.2 0) point.2) :=
        measurable_shrinkBracket.comp
          ((hcurrent.prodMk hhead).prodMk measurable_snd)
      simp only [shrinkRejectedVector]
      exact ih.comp ((hcurrent.prodMk htail).prodMk hupdated)

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

/-- Finite-dimensional form of the rejected-point likelihood. -/
noncomputable def rejectedTraceVectorWeight
    (logDensity : ℝ → ℝ) (threshold current : ℝ) :
    (length : ℕ) → (Fin length → ℝ) → (ℝ × ℝ) → ENNReal
  | 0, _, _ => 1
  | length + 1, rejected, bracket =>
      if rejected 0 ∈ Set.Ico bracket.1 bracket.2 ∧
          logDensity (rejected 0) < threshold then
        ENNReal.ofReal (bracket.2 - bracket.1)⁻¹ *
          rejectedTraceVectorWeight logDensity threshold current length
            (fun index => rejected index.succ)
            (shrinkBracket current (rejected 0) bracket)
      else 0

theorem rejectedTraceVectorWeight_eq_rejectedTraceWeight
    (logDensity : ℝ → ℝ) (threshold current : ℝ)
    (length : ℕ) (rejected : Fin length → ℝ) (bracket : ℝ × ℝ) :
    rejectedTraceVectorWeight logDensity threshold current length rejected bracket =
      rejectedTraceWeight logDensity threshold current (List.ofFn rejected) bracket := by
  induction length generalizing bracket with
  | zero => simp [rejectedTraceVectorWeight, rejectedTraceWeight]
  | succ length ih =>
      rw [List.ofFn_succ]
      simp only [rejectedTraceVectorWeight, rejectedTraceWeight]
      split
      · congr 1
        exact ih (fun index => rejected index.succ) _
      · rfl

/-- On each fixed rejected length, the full successive conditional likelihood
is jointly measurable in threshold, current point, rejected coordinates, and
starting bracket. -/
theorem measurable_rejectedTraceVectorWeight
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (length : ℕ) :
    Measurable (fun point : ((ℝ × ℝ) × (Fin length → ℝ)) × (ℝ × ℝ) =>
      rejectedTraceVectorWeight logDensity point.1.1.1 point.1.1.2
        length point.1.2 point.2) := by
  induction length with
  | zero => exact measurable_const
  | succ length ih =>
      have hstate : Measurable
          (fun point : ((ℝ × ℝ) × (Fin (length + 1) → ℝ)) × (ℝ × ℝ) =>
            point.1.1) := measurable_fst.comp measurable_fst
      have hthreshold := measurable_fst.comp hstate
      have hcurrent := measurable_snd.comp hstate
      have hrejected : Measurable
          (fun point : ((ℝ × ℝ) × (Fin (length + 1) → ℝ)) × (ℝ × ℝ) =>
            point.1.2) := measurable_snd.comp measurable_fst
      have hhead := (measurable_pi_apply (0 : Fin (length + 1))).comp hrejected
      have htail : Measurable
          (fun point : ((ℝ × ℝ) × (Fin (length + 1) → ℝ)) × (ℝ × ℝ) =>
            fun index : Fin length => point.1.2 index.succ) := by
        exact measurable_pi_lambda _ fun index =>
          (measurable_pi_apply index.succ).comp hrejected
      have hupdated : Measurable
          (fun point : ((ℝ × ℝ) × (Fin (length + 1) → ℝ)) × (ℝ × ℝ) =>
            shrinkBracket point.1.1.2 (point.1.2 0) point.2) :=
        measurable_shrinkBracket.comp
          ((hcurrent.prodMk hhead).prodMk measurable_snd)
      have hcondition : MeasurableSet
          {point : ((ℝ × ℝ) × (Fin (length + 1) → ℝ)) × (ℝ × ℝ) |
            point.1.2 0 ∈ Set.Ico point.2.1 point.2.2 ∧
              logDensity (point.1.2 0) < point.1.1.1} := by
        exact ((measurableSet_le (measurable_fst.comp measurable_snd) hhead).inter
          (measurableSet_lt hhead (measurable_snd.comp measurable_snd))).inter
            (measurableSet_lt (hlogDensity.comp hhead) hthreshold)
      simp only [rejectedTraceVectorWeight]
      apply Measurable.ite hcondition
      · exact (ENNReal.measurable_ofReal.comp
          (((measurable_snd.comp measurable_snd).sub
            (measurable_fst.comp measurable_snd)).inv)).mul
          (ih.comp (((hthreshold.prodMk hcurrent).prodMk htail).prodMk hupdated))
      · exact measurable_const

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

/-- Measurable carrier of nondegenerate stopped brackets. Keeping the order
proof in the carrier makes every fiber accepted-proposal reversal
measure-preserving without an additional exceptional branch. -/
abbrev StoppedBracket := {bracket : ℝ × ℝ // bracket.1 < bracket.2}

/-- Leave a stopped bracket unchanged and reverse the accepted old/proposal
coordinates in its fiber. -/
noncomputable def stoppedBracketAcceptedReverse
    (point : StoppedBracket × (ℝ × ℝ)) : StoppedBracket × (ℝ × ℝ) :=
  (point.1,
    acceptedProposalReverse point.1.1.1 point.1.1.2 point.2)

theorem measurable_stoppedBracketAcceptedReverse :
    Measurable stoppedBracketAcceptedReverse := by
  unfold stoppedBracketAcceptedReverse acceptedProposalReverse
  fun_prop

/-- For any s-finite law of stopped brackets, the bracket-dependent affine
accepted-proposal reversal preserves that law times planar volume. No
independence or explicit bracket density is required. -/
theorem stoppedBracketAcceptedReverse_measurePreserving
    (bracketLaw : Measure StoppedBracket) [SFinite bracketLaw] :
    MeasurePreserving stoppedBracketAcceptedReverse
      (bracketLaw.prod ((volume : Measure ℝ).prod volume))
      (bracketLaw.prod ((volume : Measure ℝ).prod volume)) := by
  refine (MeasurePreserving.id bracketLaw).skew_product
    (g := fun bracket point =>
      acceptedProposalReverse bracket.1.1 bracket.1.2 point)
    (by
      unfold acceptedProposalReverse
      fun_prop) ?_
  filter_upwards [] with bracket
  exact (acceptedProposalReverse_measurePreserving
    (sub_ne_zero.mpr bracket.2.ne')).map_eq

/-- Successful accepted coordinates in a varying stopped bracket. -/
def stoppedBracketAcceptedSuccess
    (logDensity : ℝ → ℝ) (threshold : ℝ) :
    Set (StoppedBracket × (ℝ × ℝ)) :=
  {point | point.2 ∈ acceptedProposalSuccess logDensity threshold
    point.1.1.1 point.1.1.2}

theorem measurableSet_stoppedBracketAcceptedSuccess
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (threshold : ℝ) :
    MeasurableSet (stoppedBracketAcceptedSuccess logDensity threshold) := by
  unfold stoppedBracketAcceptedSuccess acceptedProposalSuccess
  measurability

theorem stoppedBracketAcceptedReverse_preimage_success
    (logDensity : ℝ → ℝ) (threshold : ℝ) :
    stoppedBracketAcceptedReverse ⁻¹'
        stoppedBracketAcceptedSuccess logDensity threshold =
      stoppedBracketAcceptedSuccess logDensity threshold := by
  ext point
  change acceptedProposalReverse point.1.1.1 point.1.1.2 point.2 ∈
      acceptedProposalSuccess logDensity threshold point.1.1.1 point.1.1.2 ↔
    point.2 ∈
      acceptedProposalSuccess logDensity threshold point.1.1.1 point.1.1.2
  exact Set.ext_iff.mp
    (acceptedProposalSuccess_preimage logDensity threshold point.1.2) point.2

/-- The varying-bracket accepted-proposal law remains measure preserving after
restriction to successful slice coordinates. -/
theorem stoppedBracketAcceptedReverse_restrict_measurePreserving
    {bracketLaw : Measure StoppedBracket} [SFinite bracketLaw]
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (threshold : ℝ) :
    MeasurePreserving stoppedBracketAcceptedReverse
      ((bracketLaw.prod ((volume : Measure ℝ).prod volume)).restrict
        (stoppedBracketAcceptedSuccess logDensity threshold))
      ((bracketLaw.prod ((volume : Measure ℝ).prod volume)).restrict
        (stoppedBracketAcceptedSuccess logDensity threshold)) := by
  apply measurePreserving_restrict_of_preimage_eq
    (stoppedBracketAcceptedReverse_measurePreserving bracketLaw)
    (measurableSet_stoppedBracketAcceptedSuccess hlogDensity threshold)
  exact stoppedBracketAcceptedReverse_preimage_success logDensity threshold

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

/-- Variable-dimensional rejected shrink sequences. The length is retained as
part of the trace instead of padding to an artificial global budget. -/
abbrev RejectedSequence := Σ length : ℕ, Fin length → ℝ

/-- Lebesgue measure on one fixed rejected-sequence dimension, embedded into
the variable-dimensional sigma type. -/
noncomputable def rejectedSequenceFiberMeasure (length : ℕ) :
    Measure RejectedSequence :=
  (Measure.pi fun _ : Fin length => (volume : Measure ℝ)).map
    (fun values => Sigma.mk length values)

theorem measurable_rejectedSequenceMk (length : ℕ) :
    Measurable (fun values : Fin length → ℝ =>
      (Sigma.mk length values : RejectedSequence)) := by
  apply Measurable.of_le_map
  exact iInf_le _ length

/-- A function out of the coproduct measurable space on a sigma type is
measurable exactly when every fiber restriction is measurable. -/
theorem measurable_sigma_of_measurable_mk
    {Index : Type*} {Fiber : Index → Type*} {Target : Type*}
    [∀ index, MeasurableSpace (Fiber index)] [MeasurableSpace Target]
    (f : (Σ index, Fiber index) → Target)
    (hf : ∀ index, Measurable (fun value => f (Sigma.mk index value))) :
    Measurable f := by
  apply Measurable.of_le_map
  change _ ≤ (⨅ index,
    (inferInstance : MeasurableSpace (Fiber index)).map (Sigma.mk index)).map f
  rw [MeasurableSpace.map_iInf]
  refine le_iInf fun index => ?_
  rw [MeasurableSpace.map_comp]
  exact (hf index).le_map

/-- Honest base measure for variable-length rejected traces: counting over
the length and finite-dimensional Lebesgue measure within each fiber. -/
noncomputable def rejectedSequenceLebesgue : Measure RejectedSequence :=
  Measure.sum rejectedSequenceFiberMeasure

instance rejectedSequenceLebesgue.instSFinite :
    SFinite rejectedSequenceLebesgue := by
  unfold rejectedSequenceLebesgue rejectedSequenceFiberMeasure
  infer_instance

/-- Primitive random coordinates actually consumed by a successful practical
slice execution. The stopped bracket is absent because it is deterministically
derived from height, current state, alignment, allocation, and the target. -/
abbrev RuntimeRandomTrace :=
  RejectedSequence × ((Alignment × ℤ) × ℝ)

/-- Common s-finite base for primitive runtime traces: variable-dimensional
Lebesgue measure, Haar grid alignment, integer counting measure, and one final
real proposal coordinate. Valid ranges and conditional widths are supplied by
the concrete trace density. -/
noncomputable def runtimeRandomTraceBase : Measure RuntimeRandomTrace :=
  rejectedSequenceLebesgue.prod
    (((volume : Measure Alignment).prod (Measure.count : Measure ℤ)).prod
      (volume : Measure ℝ))

instance runtimeRandomTraceBase.instSFinite :
    SFinite runtimeRandomTraceBase := by
  unfold runtimeRandomTraceBase
  infer_instance

/-- Stopped stepping-out bracket computed directly from the runtime integer
allocation. Invalid allocations are still assigned deterministic semantics;
the trace density gives them zero mass. -/
noncomputable def runtimeSteppedBracket
    (logDensity : ℝ → ℝ) (threshold width current : ℝ)
    (intervals : ℕ) (allocation : ℤ) (offset : Alignment) : ℝ × ℝ :=
  let leftSteps := allocation.toNat
  (expandLeft logDensity threshold width leftSteps
      (initialLeft width current (alignmentCoordinate offset)),
    expandRight logDensity threshold width (intervals - 1 - leftSteps)
      (initialRight width current (alignmentCoordinate offset)))

theorem measurable_runtimeSteppedBracket_fixedAllocation
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (width : ℝ) (intervals : ℕ) (allocation : ℤ) :
    Measurable (fun point : (ℝ × ℝ) × Alignment =>
      runtimeSteppedBracket logDensity point.1.1 width point.1.2
        intervals allocation point.2) := by
  have hthreshold : Measurable (fun point : (ℝ × ℝ) × Alignment => point.1.1) :=
    measurable_fst.comp measurable_fst
  have hcurrent : Measurable (fun point : (ℝ × ℝ) × Alignment => point.1.2) :=
    measurable_snd.comp measurable_fst
  have hoffset : Measurable (fun point : (ℝ × ℝ) × Alignment =>
      alignmentCoordinate point.2) :=
    measurable_alignmentCoordinate.comp measurable_snd
  have hinitialLeft : Measurable (fun point : (ℝ × ℝ) × Alignment =>
      initialLeft width point.1.2 (alignmentCoordinate point.2)) := by
    unfold initialLeft
    exact hcurrent.sub (measurable_const.mul hoffset)
  have hinitialRight : Measurable (fun point : (ℝ × ℝ) × Alignment =>
      initialRight width point.1.2 (alignmentCoordinate point.2)) := by
    unfold initialRight
    exact hinitialLeft.add measurable_const
  unfold runtimeSteppedBracket
  exact ((measurable_expandLeft hlogDensity width allocation.toNat).comp
      (hthreshold.prodMk hinitialLeft)).prodMk
    ((measurable_expandRight hlogDensity width
      (intervals - 1 - allocation.toNat)).comp
        (hthreshold.prodMk hinitialRight))

/-- After replaying the actual rejected points, this is the bracket from which
the final proposal coordinate is interpreted. -/
noncomputable def runtimeFinalBracket
    (logDensity : ℝ → ℝ) (threshold width current : ℝ)
    (intervals : ℕ) (trace : RuntimeRandomTrace) : ℝ × ℝ :=
  shrinkRejectedPoints current (List.ofFn trace.1.2)
    (runtimeSteppedBracket logDensity threshold width current intervals
      trace.2.1.2 trace.2.1.1)

/-- Proposed state encoded by the final primitive real coordinate after all
recorded shrink rejections. -/
noncomputable def runtimeAcceptedPoint
    (logDensity : ℝ → ℝ) (threshold width current : ℝ)
    (intervals : ℕ) (trace : RuntimeRandomTrace) : ℝ :=
  let bracket := runtimeFinalBracket logDensity threshold width current intervals trace
  bracket.1 + (bracket.2 - bracket.1) * trace.2.2

/-- On a valid dependent allocation stratum, the raw runtime bracket agrees
definitionally with the proof-oriented `steppedBracket`. -/
theorem runtimeSteppedBracket_eq_steppedBracket
    (logDensity : ℝ → ℝ) (threshold width current : ℝ)
    {intervals : ℕ} {shift : ℤ}
    (allocation : ValidAllocation intervals shift) (offset : Alignment) :
    runtimeSteppedBracket logDensity threshold width current intervals
        allocation.1 offset =
      steppedBracket logDensity threshold width current
        (alignmentCoordinate offset) allocation := by
  unfold runtimeSteppedBracket steppedBracket allocationRightSteps
    allocationSteps
  rfl

/-- Concrete density of the primitive stepping-out/shrinkage trace. The grid
allocation is uniform on its configured finite range; rejected points carry
their successive reciprocal-bracket-width densities; and the final primitive
coordinate is uniform on `[0,1)`. -/
noncomputable def runtimeTraceDensity
    (logDensity : ℝ → ℝ) (width : ℝ) (intervals maxShrink : ℕ)
    (state : ℝ × ℝ) (trace : RuntimeRandomTrace) : ENNReal :=
  let threshold := state.1
  let current := state.2
  let allocation := trace.2.1.2
  let rejected := List.ofFn trace.1.2
  let stepped := runtimeSteppedBracket logDensity threshold width current
    intervals allocation trace.2.1.1
  let finalBracket := shrinkRejectedPoints current rejected stepped
  let accepted := finalBracket.1 +
    (finalBracket.2 - finalBracket.1) * trace.2.2
  if trace.1.1 < maxShrink ∧ 0 ≤ allocation ∧ allocation < intervals ∧
      trace.2.2 ∈ Set.Ico (0 : ℝ) 1 ∧
      threshold ≤ logDensity accepted then
    ENNReal.ofReal ((intervals : ℝ)⁻¹) *
      rejectedTraceWeight logDensity threshold current rejected stepped
  else 0

/-- Density of the uniform finite allocation, represented on integer counting
measure. -/
noncomputable def allocationWeight (intervals : ℕ) (allocation : ℤ) : ENNReal :=
  if 0 ≤ allocation ∧ allocation < intervals then
    ENNReal.ofReal ((intervals : ℝ)⁻¹)
  else 0

theorem allocationWeight_lintegral
    {intervals : ℕ} (hintervals : 0 < intervals) :
    ∫⁻ allocation : ℤ, allocationWeight intervals allocation ∂Measure.count = 1 := by
  rw [show allocationWeight intervals =
      (Set.Ico (0 : ℤ) intervals).indicator
        (fun _ => ENNReal.ofReal ((intervals : ℝ)⁻¹)) by
    funext allocation
    by_cases h : allocation ∈ Set.Ico (0 : ℤ) intervals
    · rw [Set.indicator_of_mem h]
      simp only [Set.mem_Ico] at h
      rw [allocationWeight, if_pos h]
    · rw [Set.indicator_of_notMem h]
      simp only [Set.mem_Ico] at h
      rw [allocationWeight, if_neg h]]
  rw [lintegral_indicator measurableSet_Ico,
    MeasureTheory.lintegral_const, Measure.restrict_apply_univ,
    Measure.count_apply measurableSet_Ico]
  have hcard : (Set.Ico (0 : ℤ) intervals).toFinset.card = intervals := by
    rw [Set.toFinset_Ico, Int.card_Ico]
    simp
  have hencard : (Set.Ico (0 : ℤ) intervals).encard = intervals := by
    rw [Set.encard_eq_coe_toFinset_card, hcard]
  rw [hencard]
  rw [ENNReal.ofReal_inv_of_pos (by positivity : 0 < (intervals : ℝ))]
  simp only [ENNReal.ofReal_natCast]
  apply ENNReal.inv_mul_cancel
  · exact_mod_cast hintervals.ne'
  · simp

/-- Adding any measurable acceptance condition to a uniform final fraction
cannot contribute more than unit mass. -/
theorem lintegral_finalFraction_accept_le
    (accepted : Set ℝ) (coefficient : ENNReal) :
    (∫⁻ fraction : ℝ,
      ((Set.Ico (0 : ℝ) 1) ∩ accepted).indicator
        (fun _ => coefficient) fraction ∂volume) ≤ coefficient := by
  classical
  calc
    (∫⁻ fraction : ℝ,
      ((Set.Ico (0 : ℝ) 1) ∩ accepted).indicator
        (fun _ => coefficient) fraction ∂volume) ≤
        ∫⁻ fraction : ℝ, (Set.Ico (0 : ℝ) 1).indicator
          (fun _ => coefficient) fraction ∂volume := by
      apply lintegral_mono
      intro fraction
      by_cases hfraction : fraction ∈ Set.Ico (0 : ℝ) 1 <;>
        by_cases haccept : fraction ∈ accepted <;>
          simp [hfraction, haccept]
    _ = coefficient := by
      rw [lintegral_indicator measurableSet_Ico,
        MeasureTheory.lintegral_const, Measure.restrict_apply_univ,
        Real.volume_Ico]
      simp

/-! ### Bounded shrink-recursion mass -/

/-- Tonelli decomposition of a finite real vector into its zeroth coordinate
and its remaining coordinates. This is the measurable bridge between concrete
`Fin n → ℝ` trace fibers and the recursive shrink calculation. -/
theorem lintegral_piFinSucc_zero (length : ℕ)
    (weight : (Fin (length + 1) → ℝ) → ENNReal)
    (hweight : Measurable weight) :
    (∫⁻ values : Fin (length + 1) → ℝ, weight values
        ∂(Measure.pi fun _ : Fin (length + 1) => (volume : Measure ℝ))) =
      ∫⁻ head : ℝ, ∫⁻ tail : Fin length → ℝ,
        weight (Fin.cons head tail)
          ∂(Measure.pi fun _ : Fin length => (volume : Measure ℝ)) ∂volume := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (length + 1) => ℝ) (0 : Fin (length + 1))
  have hpreserving := MeasureTheory.measurePreserving_piFinSuccAbove
    (fun _ : Fin (length + 1) => (volume : Measure ℝ))
    (0 : Fin (length + 1))
  calc
    (∫⁻ values : Fin (length + 1) → ℝ, weight values
        ∂(Measure.pi fun _ : Fin (length + 1) => (volume : Measure ℝ))) =
        ∫⁻ pair : ℝ × (Fin length → ℝ), weight (e.symm pair)
          ∂((volume : Measure ℝ).prod
            (Measure.pi fun _ : Fin length => (volume : Measure ℝ))) :=
      (hpreserving.symm.lintegral_comp hweight).symm
    _ = ∫⁻ head : ℝ, ∫⁻ tail : Fin length → ℝ,
          weight (e.symm (head, tail))
            ∂(Measure.pi fun _ : Fin length => (volume : Measure ℝ)) ∂volume := by
      change (∫⁻ pair : ℝ × (Fin length → ℝ),
        (weight ∘ e.symm) pair
          ∂((volume : Measure ℝ).prod
            (Measure.pi fun _ : Fin length => (volume : Measure ℝ)))) = _
      rw [MeasureTheory.lintegral_prod _
        ((hweight.comp e.symm.measurable).aemeasurable)]
      rfl
    _ = ∫⁻ head : ℝ, ∫⁻ tail : Fin length → ℝ,
          weight (Fin.cons head tail)
            ∂(Measure.pi fun _ : Fin length => (volume : Measure ℝ)) ∂volume := by
      congr with head
      congr with tail
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv]

/-- Lebesgue measure under the affine coordinate used to turn a unit fraction
into a point of a nondegenerate bracket. -/
theorem map_volume_bracketAffine (left width : ℝ) (hwidth : width ≠ 0) :
    Measure.map (fun fraction : ℝ => left + width * fraction) volume =
      ENNReal.ofReal |width⁻¹| • volume := by
  rw [show (fun fraction : ℝ => left + width * fraction) =
      (fun point : ℝ => left + point) ∘ (fun fraction : ℝ => width * fraction) by
    funext fraction
    rfl]
  rw [← Measure.map_map (measurable_const_add left)
    (measurable_const_mul width), Real.map_volume_mul_left hwidth,
    Measure.map_smul, map_add_left_eq_self]

/-- A uniform unit fraction, affinely interpreted in a positive bracket, is
normalized Lebesgue measure on that bracket. -/
theorem map_restrict_unitIco_bracketAffine
    {left right : ℝ} (hlt : left < right) :
    Measure.map (fun fraction : ℝ => left + (right - left) * fraction)
        (volume.restrict (Set.Ico (0 : ℝ) 1)) =
      ENNReal.ofReal ((right - left) : ℝ)⁻¹ •
        volume.restrict (Set.Ico left right) := by
  let width := right - left
  have hwidth : 0 < width := sub_pos.mpr hlt
  let e : ℝ ≃ᵐ ℝ := (affineHomeomorph width left hwidth.ne').toMeasurableEquiv
  have himage : e '' Set.Ico (0 : ℝ) 1 = Set.Ico left right := by
    simpa [e, width, sub_add_cancel] using
      (affineHomeomorph_image_Ico width left (0 : ℝ) 1 hwidth)
  have hpreimage : e ⁻¹' Set.Ico left right = Set.Ico (0 : ℝ) 1 := by
    rw [← himage, e.preimage_image]
  have hmap : Measure.map e volume =
      ENNReal.ofReal width⁻¹ • volume := by
    change Measure.map (fun fraction : ℝ => width * fraction + left) volume = _
    simpa [add_comm, abs_of_pos (inv_pos.mpr hwidth)] using
      map_volume_bracketAffine left width hwidth.ne'
  rw [show (fun fraction : ℝ => left + (right - left) * fraction) = e by
    funext fraction
    simp [e, width, add_comm]]
  rw [← hpreimage, ← e.restrict_map, hmap, Measure.restrict_smul]

/-- The normalized Lebesgue law on a real bracket. Degenerate or reversed
brackets carry the zero measure; the practical algorithm maintains positive
brackets. -/
noncomputable def normalizedBracketMeasure (bracket : ℝ × ℝ) : Measure ℝ :=
  ENNReal.ofReal (bracket.2 - bracket.1)⁻¹ •
    volume.restrict (Set.Ico bracket.1 bracket.2)

theorem normalizedBracketMeasure_eq_map
    {bracket : ℝ × ℝ} (hlt : bracket.1 < bracket.2) :
    normalizedBracketMeasure bracket =
      Measure.map
        (fun fraction : ℝ => bracket.1 +
          (bracket.2 - bracket.1) * fraction)
        (volume.restrict (Set.Ico (0 : ℝ) 1)) := by
  exact (map_restrict_unitIco_bracketAffine hlt).symm

/-- A positive normalized bracket has total mass one. -/
theorem normalizedBracketMeasure_apply_univ
    {bracket : ℝ × ℝ} (hlt : bracket.1 < bracket.2) :
    normalizedBracketMeasure bracket Set.univ = 1 := by
  rw [normalizedBracketMeasure_eq_map hlt,
    Measure.map_apply (by fun_prop) MeasurableSet.univ]
  simp [Real.volume_Ico]

/-- Any measurable accept/reject partition of a positive bracket has total
mass one. This is the measure-theoretic one-step telescoping identity. -/
theorem normalizedBracketMeasure_accept_add_reject
    {bracket : ℝ × ℝ} (hlt : bracket.1 < bracket.2)
    {accepted : Set ℝ} (haccepted : MeasurableSet accepted) :
    normalizedBracketMeasure bracket accepted +
      normalizedBracketMeasure bracket acceptedᶜ = 1 := by
  rw [measure_add_measure_compl haccepted,
    normalizedBracketMeasure_apply_univ hlt]

/-- Target superlevel set selected by a sampled log height. -/
def shrinkAcceptedSet (logDensity : ℝ → ℝ) (threshold : ℝ) : Set ℝ :=
  {point | threshold ≤ logDensity point}

theorem measurableSet_shrinkAcceptedSet
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (threshold : ℝ) :
    MeasurableSet (shrinkAcceptedSet logDensity threshold) := by
  exact measurableSet_le measurable_const hlogDensity

/-- Probability that the next uniform proposal in a bracket is accepted. -/
noncomputable def shrinkAcceptMass (logDensity : ℝ → ℝ)
    (threshold : ℝ) (bracket : ℝ × ℝ) : ENNReal :=
  normalizedBracketMeasure bracket (shrinkAcceptedSet logDensity threshold)

/-- Acceptance indicator in the primitive unit-fraction coordinate. -/
noncomputable def finalFractionAcceptWeight (logDensity : ℝ → ℝ)
    (threshold : ℝ) (bracket : ℝ × ℝ) (fraction : ℝ) : ENNReal :=
  if fraction ∈ Set.Ico (0 : ℝ) 1 ∧
      threshold ≤ logDensity
        (bracket.1 + (bracket.2 - bracket.1) * fraction) then 1 else 0

theorem measurable_finalFractionAcceptWeight
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (threshold : ℝ) :
    Measurable (Function.uncurry
      (finalFractionAcceptWeight logDensity threshold)) := by
  have hproposal : Measurable (fun point : (ℝ × ℝ) × ℝ =>
      point.1.1 + (point.1.2 - point.1.1) * point.2) := by fun_prop
  unfold Function.uncurry finalFractionAcceptWeight
  exact Measurable.ite
    (((measurableSet_Ico.mem.comp measurable_snd).and
      (measurableSet_le measurable_const (hlogDensity.comp hproposal)).mem).setOf)
    measurable_const measurable_const

/-- Acceptance mass expressed directly in the runtime fraction coordinate. -/
noncomputable def finalFractionAcceptMass (logDensity : ℝ → ℝ)
    (threshold : ℝ) (bracket : ℝ × ℝ) : ENNReal :=
  ∫⁻ fraction, finalFractionAcceptWeight logDensity threshold bracket fraction ∂volume

theorem measurable_finalFractionAcceptMass
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (threshold : ℝ) :
    Measurable (finalFractionAcceptMass logDensity threshold) := by
  exact (measurable_finalFractionAcceptWeight hlogDensity threshold).lintegral_prod_right

/-- On a positive bracket, the runtime fraction-coordinate acceptance mass is
the normalized superlevel-set mass. -/
theorem finalFractionAcceptMass_eq_shrinkAcceptMass
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (threshold : ℝ) {bracket : ℝ × ℝ} (hlt : bracket.1 < bracket.2) :
    finalFractionAcceptMass logDensity threshold bracket =
      shrinkAcceptMass logDensity threshold bracket := by
  let accepted := shrinkAcceptedSet logDensity threshold
  let affine := fun fraction : ℝ =>
    bracket.1 + (bracket.2 - bracket.1) * fraction
  have haccepted : MeasurableSet accepted :=
    measurableSet_shrinkAcceptedSet hlogDensity threshold
  have haffine : Measurable affine := by fun_prop
  have hset : MeasurableSet (Set.Ico (0 : ℝ) 1 ∩ affine ⁻¹' accepted) :=
    measurableSet_Ico.inter (haffine haccepted)
  have hmap := congrArg (fun measure : Measure ℝ => measure accepted)
    (map_restrict_unitIco_bracketAffine hlt)
  rw [Measure.map_apply haffine haccepted,
    Measure.restrict_apply (haffine haccepted), Measure.smul_apply,
    Measure.restrict_apply haccepted] at hmap
  rw [finalFractionAcceptMass, show
      (fun fraction => finalFractionAcceptWeight logDensity threshold bracket fraction) =
        (Set.Ico (0 : ℝ) 1 ∩ affine ⁻¹' accepted).indicator (fun _ => 1) by
    funext fraction
    by_cases hfraction : fraction ∈ Set.Ico (0 : ℝ) 1 ∩ affine ⁻¹' accepted
    · rw [Set.indicator_of_mem hfraction]
      simp only [Set.mem_inter_iff, Set.mem_preimage, accepted,
        shrinkAcceptedSet, Set.mem_setOf_eq] at hfraction
      rw [finalFractionAcceptWeight, if_pos hfraction]
    · rw [Set.indicator_of_notMem hfraction]
      simp only [Set.mem_inter_iff, Set.mem_preimage, accepted,
        shrinkAcceptedSet, Set.mem_setOf_eq] at hfraction
      rw [finalFractionAcceptWeight, if_neg hfraction]]
  rw [lintegral_indicator hset, MeasureTheory.lintegral_const,
    Measure.restrict_apply_univ]
  rw [shrinkAcceptMass, normalizedBracketMeasure, Measure.smul_apply,
    Measure.restrict_apply haccepted]
  simpa only [one_mul, smul_eq_mul, accepted, affine,
    Set.inter_comm] using hmap

/-- Point-coordinate density of drawing a proposal in the current bracket and
rejecting it. -/
noncomputable def shrinkRejectDensity (logDensity : ℝ → ℝ)
    (threshold : ℝ) (bracket : ℝ × ℝ) (point : ℝ) : ENNReal :=
  if point ∈ Set.Ico bracket.1 bracket.2 ∧ logDensity point < threshold then
    ENNReal.ofReal (bracket.2 - bracket.1)⁻¹
  else 0

theorem measurable_shrinkRejectDensity
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (threshold : ℝ) (bracket : ℝ × ℝ) :
    Measurable (shrinkRejectDensity logDensity threshold bracket) := by
  unfold shrinkRejectDensity
  exact Measurable.ite
    ((measurableSet_Ico.mem.and
      (measurableSet_lt hlogDensity measurable_const).mem).setOf)
    measurable_const measurable_const

/-- Integrating the rejected-point density gives the normalized mass of the
complement of the target superlevel set. -/
theorem lintegral_shrinkRejectDensity
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (threshold : ℝ) (bracket : ℝ × ℝ) :
    (∫⁻ point, shrinkRejectDensity logDensity threshold bracket point ∂volume) =
      normalizedBracketMeasure bracket
        (shrinkAcceptedSet logDensity threshold)ᶜ := by
  let rejected := Set.Ico bracket.1 bracket.2 ∩
    (shrinkAcceptedSet logDensity threshold)ᶜ
  have hrejected : MeasurableSet rejected :=
    measurableSet_Ico.inter
      (measurableSet_shrinkAcceptedSet hlogDensity threshold).compl
  have hdensity : shrinkRejectDensity logDensity threshold bracket =
      rejected.indicator
        (fun _ => ENNReal.ofReal (bracket.2 - bracket.1)⁻¹) := by
    funext point
    by_cases hpoint : point ∈ rejected
    · rw [Set.indicator_of_mem hpoint]
      simp only [rejected, Set.mem_inter_iff, Set.mem_compl_iff,
        shrinkAcceptedSet, Set.mem_setOf_eq, not_le] at hpoint
      rw [shrinkRejectDensity, if_pos hpoint]
    · rw [Set.indicator_of_notMem hpoint]
      simp only [rejected, Set.mem_inter_iff, Set.mem_compl_iff,
        shrinkAcceptedSet, Set.mem_setOf_eq, not_le] at hpoint
      rw [shrinkRejectDensity, if_neg hpoint]
  rw [hdensity, lintegral_indicator hrejected,
    MeasureTheory.lintegral_const, Measure.restrict_apply_univ]
  rw [normalizedBracketMeasure, Measure.smul_apply,
    Measure.restrict_apply
      (measurableSet_shrinkAcceptedSet hlogDensity threshold).compl]
  simp only [rejected, Set.inter_comm, smul_eq_mul]

/-- Concrete one-step shrinkage acceptance and rejection masses sum to one in
every positive bracket. -/
theorem shrinkAcceptMass_add_lintegral_reject
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (threshold : ℝ) {bracket : ℝ × ℝ} (hlt : bracket.1 < bracket.2) :
    shrinkAcceptMass logDensity threshold bracket +
        ∫⁻ point, shrinkRejectDensity logDensity threshold bracket point ∂volume = 1 := by
  rw [shrinkAcceptMass, lintegral_shrinkRejectDensity hlogDensity]
  exact normalizedBracketMeasure_accept_add_reject hlt
    (measurableSet_shrinkAcceptedSet hlogDensity threshold)

/-- Bracket invariant maintained during shrinkage: the current accepted state
lies in the half-open bracket, and its log density is above the sampled
height. -/
def ValidShrinkBracket (logDensity : ℝ → ℝ) (threshold current : ℝ)
    (bracket : ℝ × ℝ) : Prop :=
  bracket.1 ≤ current ∧ current < bracket.2 ∧ threshold ≤ logDensity current

theorem ValidShrinkBracket.lt
    {logDensity : ℝ → ℝ} {threshold current : ℝ} {bracket : ℝ × ℝ}
    (hbracket : ValidShrinkBracket logDensity threshold current bracket) :
    bracket.1 < bracket.2 :=
  hbracket.1.trans_lt hbracket.2.1

/-- A nonzero-probability rejection preserves the valid-bracket invariant. -/
theorem ValidShrinkBracket.preserved_by_shrinkBracket
    {logDensity : ℝ → ℝ} {threshold current point : ℝ}
    {bracket : ℝ × ℝ}
    (hbracket : ValidShrinkBracket logDensity threshold current bracket)
    (hnonzero : shrinkRejectDensity logDensity threshold bracket point ≠ 0) :
    ValidShrinkBracket logDensity threshold current
      (shrinkBracket current point bracket) := by
  have hpoint : point ∈ Set.Ico bracket.1 bracket.2 ∧
      logDensity point < threshold := by
    by_contra hcondition
    rw [shrinkRejectDensity, if_neg hcondition] at hnonzero
    exact hnonzero rfl
  unfold Mcmc.Kernel.PracticalSlice.shrinkBracket
  by_cases hside : point < current
  · rw [if_pos hside]
    exact ⟨hside.le, hbracket.2.1, hbracket.2.2⟩
  · rw [if_neg hside]
    have hne : point ≠ current := by
      intro heq
      subst point
      exact (not_lt_of_ge hbracket.2.2) hpoint.2
    have hcurrentPoint : current < point := lt_of_le_of_ne (not_lt.mp hside) hne.symm
    exact ⟨hbracket.1, hcurrentPoint, hbracket.2.2⟩

/-- Total probability of accepting within a bounded number of shrink
attempts.  `acceptMass bracket` is the probability of accepting at the next
attempt, while `rejectDensity bracket point` is the density of a rejection
that continues from `nextBracket bracket point`.  A zero budget contributes
no successful trace mass. -/
noncomputable def boundedShrinkSuccessMass
    {Bracket Point : Type*} [MeasurableSpace Point]
    (base : Measure Point) (acceptMass : Bracket → ENNReal)
    (rejectDensity : Bracket → Point → ENNReal)
    (nextBracket : Bracket → Point → Bracket) : ℕ → Bracket → ENNReal
  | 0, _ => 0
  | attempts + 1, bracket =>
      acceptMass bracket + ∫⁻ point,
        rejectDensity bracket point *
          boundedShrinkSuccessMass base acceptMass rejectDensity nextBracket
            attempts (nextBracket bracket point) ∂base

/-- If acceptance and rejection-continuation partition at most unit mass at
every bracket, then the probability of a successful trace before any finite
budget is at most one.  This is the abstract telescoping argument needed by
bounded practical shrinkage. -/
theorem boundedShrinkSuccessMass_le_one
    {Bracket Point : Type*} [MeasurableSpace Point]
    (base : Measure Point) (acceptMass : Bracket → ENNReal)
    (rejectDensity : Bracket → Point → ENNReal)
    (nextBracket : Bracket → Point → Bracket)
    (hone : ∀ bracket,
      acceptMass bracket + ∫⁻ point, rejectDensity bracket point ∂base ≤ 1) :
    ∀ attempts bracket,
      boundedShrinkSuccessMass base acceptMass rejectDensity nextBracket
        attempts bracket ≤ 1 := by
  intro attempts
  induction attempts with
  | zero => simp [boundedShrinkSuccessMass]
  | succ attempts ih =>
      intro bracket
      rw [boundedShrinkSuccessMass]
      calc
        acceptMass bracket + ∫⁻ point,
            rejectDensity bracket point *
              boundedShrinkSuccessMass base acceptMass rejectDensity
                nextBracket attempts (nextBracket bracket point) ∂base ≤
            acceptMass bracket +
              ∫⁻ point, rejectDensity bracket point ∂base := by
          gcongr with point
          calc
            rejectDensity bracket point *
                boundedShrinkSuccessMass base acceptMass rejectDensity
                  nextBracket attempts (nextBracket bracket point) ≤
                rejectDensity bracket point * 1 :=
              mul_le_mul_right (ih (nextBracket bracket point)) _
            _ = rejectDensity bracket point := mul_one _
        _ ≤ 1 := hone bracket

/-- Invariant-aware form of the bounded telescoping argument. Only branches
with nonzero rejection density must preserve the invariant, so zero-density
coordinates need no artificial valid successor state. -/
theorem boundedShrinkSuccessMass_le_one_of_invariant
    {Bracket Point : Type*} [MeasurableSpace Point]
    (base : Measure Point) (acceptMass : Bracket → ENNReal)
    (rejectDensity : Bracket → Point → ENNReal)
    (nextBracket : Bracket → Point → Bracket)
    (Invariant : Bracket → Prop)
    (hone : ∀ bracket, Invariant bracket →
      acceptMass bracket + ∫⁻ point, rejectDensity bracket point ∂base ≤ 1)
    (hnext : ∀ bracket point, Invariant bracket →
      rejectDensity bracket point ≠ 0 → Invariant (nextBracket bracket point)) :
    ∀ attempts bracket, Invariant bracket →
      boundedShrinkSuccessMass base acceptMass rejectDensity nextBracket
        attempts bracket ≤ 1 := by
  intro attempts
  induction attempts with
  | zero => simp [boundedShrinkSuccessMass]
  | succ attempts ih =>
      intro bracket hbracket
      rw [boundedShrinkSuccessMass]
      calc
        acceptMass bracket + ∫⁻ point,
            rejectDensity bracket point *
              boundedShrinkSuccessMass base acceptMass rejectDensity
                nextBracket attempts (nextBracket bracket point) ∂base ≤
            acceptMass bracket +
              ∫⁻ point, rejectDensity bracket point ∂base := by
          gcongr with point
          by_cases hzero : rejectDensity bracket point = 0
          · simp [hzero]
          · calc
              rejectDensity bracket point *
                  boundedShrinkSuccessMass base acceptMass rejectDensity
                    nextBracket attempts (nextBracket bracket point) ≤
                  rejectDensity bracket point * 1 :=
                mul_le_mul_right
                  (ih (nextBracket bracket point) (hnext bracket point hbracket hzero)) _
              _ = rejectDensity bracket point := mul_one _
        _ ≤ 1 := hone bracket hbracket

/-- Every runtime stepping-out bracket starts with the current accepted point
inside it and can only expand outward. -/
theorem validShrinkBracket_runtimeSteppedBracket
    (logDensity : ℝ → ℝ) (threshold current : ℝ)
    {width : ℝ} (hwidth : 0 < width) (intervals : ℕ)
    (allocation : ℤ) (offset : Alignment)
    (hcurrent : threshold ≤ logDensity current) :
    ValidShrinkBracket logDensity threshold current
      (runtimeSteppedBracket logDensity threshold width current intervals
        allocation offset) := by
  rcases alignmentCoordinate_mem offset with ⟨hoffsetNonneg, hoffsetLt⟩
  have hinitialLeft : initialLeft width current (alignmentCoordinate offset) ≤
      current := by
    unfold initialLeft
    exact sub_le_self current (mul_nonneg hwidth.le hoffsetNonneg)
  have hcurrentInitialRight : current <
      initialRight width current (alignmentCoordinate offset) := by
    unfold initialRight initialLeft
    have hremaining : 0 < width * (1 - alignmentCoordinate offset) :=
      mul_pos hwidth (sub_pos.mpr hoffsetLt)
    nlinarith
  unfold runtimeSteppedBracket
  exact ⟨
    (expandLeft_le logDensity threshold hwidth.le allocation.toNat
      (initialLeft width current (alignmentCoordinate offset))).trans hinitialLeft,
    hcurrentInitialRight.trans_le
      (le_expandRight logDensity threshold hwidth.le
        (intervals - 1 - allocation.toNat)
        (initialRight width current (alignmentCoordinate offset))),
    hcurrent⟩

/-- Bounded practical shrinkage has successful mass at most one from every
valid initial bracket. -/
theorem practicalBoundedShrinkSuccessMass_le_one
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (threshold current : ℝ) (attempts : ℕ) (bracket : ℝ × ℝ)
    (hbracket : ValidShrinkBracket logDensity threshold current bracket) :
    boundedShrinkSuccessMass volume
      (shrinkAcceptMass logDensity threshold)
      (shrinkRejectDensity logDensity threshold)
      (fun bracket point => shrinkBracket current point bracket)
      attempts bracket ≤ 1 := by
  apply boundedShrinkSuccessMass_le_one_of_invariant volume
    (shrinkAcceptMass logDensity threshold)
    (shrinkRejectDensity logDensity threshold)
    (fun candidate point => shrinkBracket current point candidate)
    (ValidShrinkBracket logDensity threshold current)
  · intro candidate hcandidate
    exact (shrinkAcceptMass_add_lintegral_reject hlogDensity threshold
      hcandidate.lt).le
  · intro candidate point hcandidate hnonzero
    exact hcandidate.preserved_by_shrinkBracket hnonzero
  · exact hbracket

/-- Runtime-coordinate version of the bounded mass bound. Its immediate
acceptance term is literally the integral over the final unit fraction used
by `runtimeTraceDensity`. -/
theorem practicalBoundedFinalFractionMass_le_one
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (threshold current : ℝ) (attempts : ℕ) (bracket : ℝ × ℝ)
    (hbracket : ValidShrinkBracket logDensity threshold current bracket) :
    boundedShrinkSuccessMass volume
      (finalFractionAcceptMass logDensity threshold)
      (shrinkRejectDensity logDensity threshold)
      (fun candidate point => shrinkBracket current point candidate)
      attempts bracket ≤ 1 := by
  apply boundedShrinkSuccessMass_le_one_of_invariant volume
    (finalFractionAcceptMass logDensity threshold)
    (shrinkRejectDensity logDensity threshold)
    (fun candidate point => shrinkBracket current point candidate)
    (ValidShrinkBracket logDensity threshold current)
  · intro candidate hcandidate
    rw [finalFractionAcceptMass_eq_shrinkAcceptMass hlogDensity threshold
      hcandidate.lt]
    exact (shrinkAcceptMass_add_lintegral_reject hlogDensity threshold
      hcandidate.lt).le
  · intro candidate point hcandidate hnonzero
    exact hcandidate.preserved_by_shrinkBracket hnonzero
  · exact hbracket

/-- Successful mass on exactly one fixed rejected-point fiber, after
integrating the final primitive unit fraction. -/
noncomputable def fixedShrinkSuccessMass
    (logDensity : ℝ → ℝ) (threshold current : ℝ)
    (length : ℕ) (bracket : ℝ × ℝ) : ENNReal :=
  ∫⁻ rejected : Fin length → ℝ,
    rejectedTraceVectorWeight logDensity threshold current length rejected bracket *
      finalFractionAcceptMass logDensity threshold
        (shrinkRejectedVector current length rejected bracket)
      ∂(Measure.pi fun _ : Fin length => (volume : Measure ℝ))

theorem measurable_fixedShrinkSuccessWeight
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (threshold current : ℝ) (length : ℕ) (bracket : ℝ × ℝ) :
    Measurable (fun rejected : Fin length → ℝ =>
      rejectedTraceVectorWeight logDensity threshold current length rejected bracket *
        finalFractionAcceptMass logDensity threshold
          (shrinkRejectedVector current length rejected bracket)) := by
  have hpackWeight : Measurable (fun rejected : Fin length → ℝ =>
      ((((threshold, current), rejected), bracket) :
        ((ℝ × ℝ) × (Fin length → ℝ)) × (ℝ × ℝ))) := by
    fun_prop
  have hweight := (measurable_rejectedTraceVectorWeight hlogDensity length).comp
    hpackWeight
  have hpackFinal : Measurable (fun rejected : Fin length → ℝ =>
      (((current, rejected), bracket) :
        (ℝ × (Fin length → ℝ)) × (ℝ × ℝ))) := by
    fun_prop
  have hfinal := (measurable_shrinkRejectedVector length).comp
    hpackFinal
  exact hweight.mul
    ((measurable_finalFractionAcceptMass hlogDensity threshold).comp hfinal)

/-- Fixed-length successful mass is measurable as the starting bracket
varies. -/
theorem measurable_fixedShrinkSuccessMass
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (threshold current : ℝ) (length : ℕ) :
    Measurable (fixedShrinkSuccessMass logDensity threshold current length) := by
  have hweight : Measurable (fun point : (ℝ × ℝ) × (Fin length → ℝ) =>
      rejectedTraceVectorWeight logDensity threshold current length point.2 point.1) := by
    have hpack : Measurable (fun point : (ℝ × ℝ) × (Fin length → ℝ) =>
        ((((threshold, current), point.2), point.1) :
          ((ℝ × ℝ) × (Fin length → ℝ)) × (ℝ × ℝ))) := by
      fun_prop
    exact (measurable_rejectedTraceVectorWeight hlogDensity length).comp hpack
  have hfinal : Measurable (fun point : (ℝ × ℝ) × (Fin length → ℝ) =>
      shrinkRejectedVector current length point.2 point.1) := by
    have hpack : Measurable (fun point : (ℝ × ℝ) × (Fin length → ℝ) =>
        (((current, point.2), point.1) :
          (ℝ × (Fin length → ℝ)) × (ℝ × ℝ))) := by
      fun_prop
    exact (measurable_shrinkRejectedVector length).comp hpack
  have hintegrand : Measurable
      (Function.uncurry (fun bracket rejected =>
        rejectedTraceVectorWeight logDensity threshold current length rejected bracket *
          finalFractionAcceptMass logDensity threshold
            (shrinkRejectedVector current length rejected bracket))) :=
    hweight.mul
      ((measurable_finalFractionAcceptMass hlogDensity threshold).comp hfinal)
  exact hintegrand.lintegral_prod_right

@[simp] theorem fixedShrinkSuccessMass_zero
    (logDensity : ℝ → ℝ) (threshold current : ℝ) (bracket : ℝ × ℝ) :
    fixedShrinkSuccessMass logDensity threshold current 0 bracket =
      finalFractionAcceptMass logDensity threshold bracket := by
  simp [fixedShrinkSuccessMass, rejectedTraceVectorWeight,
    shrinkRejectedVector]

/-- Adding one rejected coordinate gives the expected first-rejection
factor followed by the fixed mass of the remaining tail. -/
theorem fixedShrinkSuccessMass_succ
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (threshold current : ℝ) (length : ℕ) (bracket : ℝ × ℝ) :
    fixedShrinkSuccessMass logDensity threshold current (length + 1) bracket =
      ∫⁻ point : ℝ,
        shrinkRejectDensity logDensity threshold bracket point *
          fixedShrinkSuccessMass logDensity threshold current length
            (shrinkBracket current point bracket) ∂volume := by
  rw [fixedShrinkSuccessMass,
    lintegral_piFinSucc_zero length _
      (measurable_fixedShrinkSuccessWeight hlogDensity threshold current
        (length + 1) bracket)]
  congr with point
  by_cases hpoint : point ∈ Set.Ico bracket.1 bracket.2 ∧
      logDensity point < threshold
  · have hcondition : (bracket.1 ≤ point ∧ point < bracket.2) ∧
        logDensity point < threshold := by
      simpa only [Set.mem_Ico] using hpoint
    simp only [rejectedTraceVectorWeight, Fin.cons_zero, hcondition,
      shrinkRejectedVector, Fin.cons_succ, shrinkRejectDensity,
      fixedShrinkSuccessMass]
    rw [← MeasureTheory.lintegral_const_mul]
    · apply lintegral_congr
      intro tail
      simp [hpoint.1, mul_assoc]
    · exact measurable_fixedShrinkSuccessWeight hlogDensity threshold current
        length (shrinkBracket current point bracket)
  · have hcondition : ¬((bracket.1 ≤ point ∧ point < bracket.2) ∧
        logDensity point < threshold) := by
      simpa only [Set.mem_Ico] using hpoint
    simp [rejectedTraceVectorWeight, shrinkRejectedVector,
      shrinkRejectDensity, hcondition]

/-- Summing all fixed rejected lengths below a budget is exactly the abstract
bounded recursion. -/
theorem sum_fixedShrinkSuccessMass_eq_bounded
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (threshold current : ℝ) (attempts : ℕ) (bracket : ℝ × ℝ) :
    (∑ length : Fin attempts,
      fixedShrinkSuccessMass logDensity threshold current length bracket) =
      boundedShrinkSuccessMass volume
        (finalFractionAcceptMass logDensity threshold)
        (shrinkRejectDensity logDensity threshold)
        (fun candidate point => shrinkBracket current point candidate)
        attempts bracket := by
  induction attempts generalizing bracket with
  | zero => simp [boundedShrinkSuccessMass]
  | succ attempts ih =>
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ]
      rw [fixedShrinkSuccessMass_zero,
        boundedShrinkSuccessMass]
      congr 1
      simp_rw [fixedShrinkSuccessMass_succ hlogDensity]
      rw [← MeasureTheory.lintegral_finsetSum Finset.univ]
      · apply lintegral_congr
        intro point
        rw [← Finset.mul_sum]
        congr 1
        exact ih (shrinkBracket current point bracket)
      · intro length _
        have hupdate : Measurable (fun point : ℝ =>
            shrinkBracket current point bracket) := by
          have hpack : Measurable (fun point : ℝ =>
              (((current, point), bracket) : (ℝ × ℝ) × (ℝ × ℝ))) := by
            fun_prop
          exact measurable_shrinkBracket.comp hpack
        exact (measurable_shrinkRejectDensity hlogDensity threshold bracket).mul
          ((measurable_fixedShrinkSuccessMass hlogDensity threshold current length).comp
            hupdate)

/-- The concrete sum over every allowed rejected length is a subprobability
from a valid starting bracket. -/
theorem sum_fixedShrinkSuccessMass_le_one
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (threshold current : ℝ) (attempts : ℕ) (bracket : ℝ × ℝ)
    (hbracket : ValidShrinkBracket logDensity threshold current bracket) :
    (∑ length : Fin attempts,
      fixedShrinkSuccessMass logDensity threshold current length bracket) ≤ 1 := by
  rw [sum_fixedShrinkSuccessMass_eq_bounded hlogDensity]
  exact practicalBoundedFinalFractionMass_le_one hlogDensity threshold current
    attempts bracket hbracket

theorem rejectedTraceWeight_ne_top
    (logDensity : ℝ → ℝ) (threshold current : ℝ)
    (rejected : List ℝ) (bracket : ℝ × ℝ) :
    rejectedTraceWeight logDensity threshold current rejected bracket ≠ ⊤ := by
  induction rejected generalizing bracket with
  | nil => simp [rejectedTraceWeight]
  | cons point remaining ih =>
      simp only [rejectedTraceWeight]
      split
      · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ih _)
      · simp

theorem runtimeTraceDensity_ne_top
    (logDensity : ℝ → ℝ) (width : ℝ) (intervals maxShrink : ℕ)
    (state : ℝ × ℝ) (trace : RuntimeRandomTrace) :
    runtimeTraceDensity logDensity width intervals maxShrink state trace ≠ ⊤ := by
  simp only [runtimeTraceDensity]
  split
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (rejectedTraceWeight_ne_top logDensity state.1 state.2 _ _)
  · simp

/-- The concrete successful density is measurable on every fixed rejected
dimension and integer-allocation fiber. -/
theorem measurable_runtimeTraceDensity_fixedFiber
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (width : ℝ) (intervals maxShrink length : ℕ) (allocation : ℤ) :
    Measurable (fun point : ((ℝ × ℝ) × (Fin length → ℝ)) × (Alignment × ℝ) =>
      runtimeTraceDensity logDensity width intervals maxShrink point.1.1
        (Sigma.mk length point.1.2,
          ((point.2.1, allocation), point.2.2))) := by
  have hstate : Measurable
      (fun point : ((ℝ × ℝ) × (Fin length → ℝ)) × (Alignment × ℝ) =>
        point.1.1) := measurable_fst.comp measurable_fst
  have hthreshold := measurable_fst.comp hstate
  have hcurrent := measurable_snd.comp hstate
  have hvalues : Measurable
      (fun point : ((ℝ × ℝ) × (Fin length → ℝ)) × (Alignment × ℝ) =>
        point.1.2) := measurable_snd.comp measurable_fst
  have halignment : Measurable
      (fun point : ((ℝ × ℝ) × (Fin length → ℝ)) × (Alignment × ℝ) =>
        point.2.1) := measurable_fst.comp measurable_snd
  have hfraction : Measurable
      (fun point : ((ℝ × ℝ) × (Fin length → ℝ)) × (Alignment × ℝ) =>
        point.2.2) := measurable_snd.comp measurable_snd
  have hstepped : Measurable
      (fun point : ((ℝ × ℝ) × (Fin length → ℝ)) × (Alignment × ℝ) =>
        runtimeSteppedBracket logDensity point.1.1.1 width point.1.1.2
          intervals allocation point.2.1) :=
    (measurable_runtimeSteppedBracket_fixedAllocation hlogDensity width
      intervals allocation).comp (hstate.prodMk halignment)
  have hfinal : Measurable
      (fun point : ((ℝ × ℝ) × (Fin length → ℝ)) × (Alignment × ℝ) =>
        shrinkRejectedVector point.1.1.2 length point.1.2
          (runtimeSteppedBracket logDensity point.1.1.1 width point.1.1.2
            intervals allocation point.2.1)) :=
    (measurable_shrinkRejectedVector length).comp
      ((hcurrent.prodMk hvalues).prodMk hstepped)
  have haccepted : Measurable
      (fun point : ((ℝ × ℝ) × (Fin length → ℝ)) × (Alignment × ℝ) =>
        let bracket := shrinkRejectedVector point.1.1.2 length point.1.2
          (runtimeSteppedBracket logDensity point.1.1.1 width point.1.1.2
            intervals allocation point.2.1)
        bracket.1 + (bracket.2 - bracket.1) * point.2.2) :=
    (measurable_fst.comp hfinal).add
      (((measurable_snd.comp hfinal).sub
        (measurable_fst.comp hfinal)).mul hfraction)
  have hweight : Measurable
      (fun point : ((ℝ × ℝ) × (Fin length → ℝ)) × (Alignment × ℝ) =>
        rejectedTraceVectorWeight logDensity point.1.1.1 point.1.1.2
          length point.1.2
          (runtimeSteppedBracket logDensity point.1.1.1 width point.1.1.2
            intervals allocation point.2.1)) :=
    (measurable_rejectedTraceVectorWeight hlogDensity length).comp
      (((hstate.prodMk hvalues).prodMk hstepped))
  have hcondition : Measurable
      (fun point : ((ℝ × ℝ) × (Fin length → ℝ)) × (Alignment × ℝ) =>
        length < maxShrink ∧ 0 ≤ allocation ∧ allocation < intervals ∧
          point.2.2 ∈ Set.Ico (0 : ℝ) 1 ∧
          point.1.1.1 ≤ logDensity
            (let bracket := shrinkRejectedVector point.1.1.2 length point.1.2
              (runtimeSteppedBracket logDensity point.1.1.1 width point.1.1.2
                intervals allocation point.2.1)
             bracket.1 + (bracket.2 - bracket.1) * point.2.2)) := by
    exact measurable_const.and (measurable_const.and (measurable_const.and
      ((measurableSet_Ico.mem.comp hfraction).and
        (measurableSet_le hthreshold (hlogDensity.comp haccepted)).mem)))
  have hall : Measurable
      (fun point : ((ℝ × ℝ) × (Fin length → ℝ)) × (Alignment × ℝ) =>
        if length < maxShrink ∧ 0 ≤ allocation ∧ allocation < intervals ∧
            point.2.2 ∈ Set.Ico (0 : ℝ) 1 ∧
            point.1.1.1 ≤ logDensity
              (let bracket := shrinkRejectedVector point.1.1.2 length point.1.2
                (runtimeSteppedBracket logDensity point.1.1.1 width point.1.1.2
                  intervals allocation point.2.1)
               bracket.1 + (bracket.2 - bracket.1) * point.2.2) then
          ENNReal.ofReal ((intervals : ℝ)⁻¹) *
            rejectedTraceVectorWeight logDensity point.1.1.1 point.1.1.2
              length point.1.2
              (runtimeSteppedBracket logDensity point.1.1.1 width point.1.1.2
                intervals allocation point.2.1)
        else 0) :=
    Measurable.ite hcondition.setOf (measurable_const.mul hweight)
      measurable_const
  simpa only [runtimeTraceDensity,
    shrinkRejectedVector_eq_shrinkRejectedPoints,
    rejectedTraceVectorWeight_eq_rejectedTraceWeight] using hall

/-- Primitive trace carrier at one fixed rejected length. -/
abbrev FixedRuntimeTrace (length : ℕ) :=
  (Fin length → ℝ) × ((Alignment × ℤ) × ℝ)

/-- After using the discrete measurable structure on integers, the density is
jointly measurable in state and all trace coordinates at a fixed length. -/
theorem measurable_uncurry_runtimeTraceDensity_fixedLength
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (width : ℝ) (intervals maxShrink length : ℕ) :
    Measurable (Function.uncurry
      (fun state (trace : FixedRuntimeTrace length) =>
        runtimeTraceDensity logDensity width intervals maxShrink state
          (Sigma.mk length trace.1, trace.2))) := by
  let DenseDomain := ((ℝ × ℝ) × (Fin length → ℝ)) × (Alignment × ℝ)
  have hallocation : Measurable (fun point : DenseDomain × ℤ =>
      runtimeTraceDensity logDensity width intervals maxShrink point.1.1.1
        (Sigma.mk length point.1.1.2,
          ((point.1.2.1, point.2), point.1.2.2))) := by
    apply measurable_from_prod_countable_left
    intro allocation
    exact measurable_runtimeTraceDensity_fixedFiber hlogDensity width
      intervals maxShrink length allocation
  have hpack : Measurable (fun point : (ℝ × ℝ) × FixedRuntimeTrace length =>
      ((((point.1, point.2.1), (point.2.2.1.1, point.2.2.2)),
        point.2.2.1.2) : DenseDomain × ℤ)) := by
    fun_prop
  exact hallocation.comp hpack

/-- Common base measure at one rejected length. -/
noncomputable def fixedRuntimeTraceBase (length : ℕ) :
    Measure (FixedRuntimeTrace length) :=
  (Measure.pi fun _ : Fin length => (volume : Measure ℝ)).prod
    (((volume : Measure Alignment).prod (Measure.count : Measure ℤ)).prod
      (volume : Measure ℝ))

instance fixedRuntimeTraceBase.instSFinite (length : ℕ) :
    SFinite (fixedRuntimeTraceBase length) := by
  unfold fixedRuntimeTraceBase
  infer_instance

/-- Successful subkernel on one rejected-length fiber. -/
noncomputable def fixedSuccessfulRuntimeTraceKernel
    (logDensity : ℝ → ℝ) (width : ℝ) (intervals maxShrink length : ℕ) :
    ProbabilityTheory.Kernel (ℝ × ℝ) (FixedRuntimeTrace length) :=
  (ProbabilityTheory.Kernel.const (ℝ × ℝ)
    (fixedRuntimeTraceBase length)).withDensity
      (fun state trace =>
        runtimeTraceDensity logDensity width intervals maxShrink state
          (Sigma.mk length trace.1, trace.2))

theorem fixedSuccessfulRuntimeTraceKernel_isSFinite
    (logDensity : ℝ → ℝ)
    (width : ℝ) (intervals maxShrink length : ℕ) :
    ProbabilityTheory.IsSFiniteKernel
      (fixedSuccessfulRuntimeTraceKernel logDensity width intervals
        maxShrink length) := by
  unfold fixedSuccessfulRuntimeTraceKernel
  apply ProbabilityTheory.Kernel.IsSFiniteKernel.withDensity
  intro state trace
  exact runtimeTraceDensity_ne_top logDensity width intervals maxShrink state
    (Sigma.mk length trace.1, trace.2)

/-- Embed one fixed-length trace into the variable-length runtime carrier. -/
def runtimeTraceOfFixed (length : ℕ) (trace : FixedRuntimeTrace length) :
    RuntimeRandomTrace :=
  (Sigma.mk length trace.1, trace.2)

theorem measurable_runtimeTraceOfFixed (length : ℕ) :
    Measurable (runtimeTraceOfFixed length) := by
  exact (measurable_rejectedSequenceMk length).comp measurable_fst |>.prodMk
    measurable_snd

/-- Measurable successful trace subkernel summed over exactly the allowed
rejected lengths. -/
noncomputable def successfulRuntimeTraceKernel
    (logDensity : ℝ → ℝ) (width : ℝ) (intervals maxShrink : ℕ) :
    ProbabilityTheory.Kernel (ℝ × ℝ) RuntimeRandomTrace :=
  ∑ length : Fin maxShrink,
    (fixedSuccessfulRuntimeTraceKernel logDensity width intervals maxShrink
      length).map (runtimeTraceOfFixed length)

theorem successfulRuntimeTraceKernel_isSFinite
    (logDensity : ℝ → ℝ)
    (width : ℝ) (intervals maxShrink : ℕ) :
    ProbabilityTheory.IsSFiniteKernel
      (successfulRuntimeTraceKernel logDensity width intervals maxShrink) := by
  unfold successfulRuntimeTraceKernel
  apply ProbabilityTheory.Kernel.IsSFiniteKernel.finsetSum
  intro length _
  letI : ProbabilityTheory.IsSFiniteKernel
      (fixedSuccessfulRuntimeTraceKernel logDensity width intervals maxShrink
        length) :=
    fixedSuccessfulRuntimeTraceKernel_isSFinite logDensity width intervals
      maxShrink length
  infer_instance

theorem runtimeTraceDensity_zero_of_allocation_invalid
    (logDensity : ℝ → ℝ) (width : ℝ) (intervals maxShrink : ℕ)
    (state : ℝ × ℝ) (trace : RuntimeRandomTrace)
    (hinvalid : ¬(0 ≤ trace.2.1.2 ∧ trace.2.1.2 < intervals)) :
    runtimeTraceDensity logDensity width intervals maxShrink state trace = 0 := by
  unfold runtimeTraceDensity
  simp only
  split
  · next h => exact False.elim (hinvalid ⟨h.2.1, h.2.2.1⟩)
  · rfl

theorem runtimeTraceDensity_zero_of_length_ge
    (logDensity : ℝ → ℝ) (width : ℝ) (intervals maxShrink : ℕ)
    (state : ℝ × ℝ) (trace : RuntimeRandomTrace)
    (hlength : maxShrink ≤ trace.1.1) :
    runtimeTraceDensity logDensity width intervals maxShrink state trace = 0 := by
  simp only [runtimeTraceDensity]
  split
  · next h => omega
  · rfl

/-- Integrating the primitive final fraction leaves the allocation weight
times the fixed rejected-vector success integrand. -/
theorem lintegral_runtimeTraceDensity_fraction
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (width : ℝ) (intervals maxShrink length : ℕ)
    (state : ℝ × ℝ) (rejected : Fin length → ℝ)
    (offset : Alignment) (allocation : ℤ) :
    (∫⁻ fraction : ℝ,
      runtimeTraceDensity logDensity width intervals maxShrink state
        (Sigma.mk length rejected, ((offset, allocation), fraction)) ∂volume) =
      if length < maxShrink then
        allocationWeight intervals allocation *
          rejectedTraceVectorWeight logDensity state.1 state.2 length rejected
            (runtimeSteppedBracket logDensity state.1 width state.2 intervals
              allocation offset) *
          finalFractionAcceptMass logDensity state.1
            (shrinkRejectedVector state.2 length rejected
              (runtimeSteppedBracket logDensity state.1 width state.2 intervals
                allocation offset))
      else 0 := by
  by_cases hlength : length < maxShrink
  · rw [if_pos hlength]
    by_cases hallocation : 0 ≤ allocation ∧ allocation < intervals
    · have hdensity : (fun fraction : ℝ =>
          runtimeTraceDensity logDensity width intervals maxShrink state
            (Sigma.mk length rejected, ((offset, allocation), fraction))) =
          fun fraction =>
            ENNReal.ofReal ((intervals : ℝ)⁻¹) *
              rejectedTraceVectorWeight logDensity state.1 state.2 length rejected
                (runtimeSteppedBracket logDensity state.1 width state.2 intervals
                  allocation offset) *
              finalFractionAcceptWeight logDensity state.1
                (shrinkRejectedVector state.2 length rejected
                  (runtimeSteppedBracket logDensity state.1 width state.2 intervals
                    allocation offset)) fraction := by
        funext fraction
        simp only [runtimeTraceDensity,
          shrinkRejectedVector_eq_shrinkRejectedPoints,
          rejectedTraceVectorWeight_eq_rejectedTraceWeight,
          finalFractionAcceptWeight]
        by_cases haccept : fraction ∈ Set.Ico (0 : ℝ) 1 ∧
            state.1 ≤ logDensity
              ((shrinkRejectedVector state.2 length rejected
                (runtimeSteppedBracket logDensity state.1 width state.2 intervals
                  allocation offset)).1 +
               ((shrinkRejectedVector state.2 length rejected
                (runtimeSteppedBracket logDensity state.1 width state.2 intervals
                  allocation offset)).2 -
                (shrinkRejectedVector state.2 length rejected
                (runtimeSteppedBracket logDensity state.1 width state.2 intervals
                  allocation offset)).1) * fraction)
        · simp [hlength, hallocation, haccept]
        · simp [hlength, hallocation]
      rw [hdensity, allocationWeight, if_pos hallocation,
        finalFractionAcceptMass, MeasureTheory.lintegral_const_mul]
      exact (measurable_finalFractionAcceptWeight hlogDensity state.1).of_uncurry_left
    · rw [allocationWeight, if_neg hallocation]
      have hzero : (fun fraction : ℝ =>
          runtimeTraceDensity logDensity width intervals maxShrink state
            (Sigma.mk length rejected, ((offset, allocation), fraction))) = 0 := by
        funext fraction
        exact runtimeTraceDensity_zero_of_allocation_invalid logDensity width
          intervals maxShrink state _ hallocation
      rw [hzero, lintegral_zero_fun]
      simp
  · rw [if_neg hlength]
    have hge : maxShrink ≤ length := Nat.le_of_not_gt hlength
    have hzero : (fun fraction : ℝ =>
        runtimeTraceDensity logDensity width intervals maxShrink state
          (Sigma.mk length rejected, ((offset, allocation), fraction))) = 0 := by
      funext fraction
      exact runtimeTraceDensity_zero_of_length_ge logDensity width intervals
        maxShrink state _ hge
    rw [hzero, lintegral_zero_fun]

/-- Integrating a fixed rejected vector and its final fraction yields the
allocation weight times `fixedShrinkSuccessMass` in the derived stepped-out
bracket. -/
theorem lintegral_runtimeTraceDensity_rejected_fraction
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (width : ℝ) (intervals maxShrink length : ℕ)
    (state : ℝ × ℝ) (offset : Alignment) (allocation : ℤ) :
    (∫⁻ rejected : Fin length → ℝ, ∫⁻ fraction : ℝ,
      runtimeTraceDensity logDensity width intervals maxShrink state
        (Sigma.mk length rejected, ((offset, allocation), fraction))
        ∂volume
      ∂(Measure.pi fun _ : Fin length => (volume : Measure ℝ))) =
      if length < maxShrink then
        allocationWeight intervals allocation *
          fixedShrinkSuccessMass logDensity state.1 state.2 length
            (runtimeSteppedBracket logDensity state.1 width state.2 intervals
              allocation offset)
      else 0 := by
  simp_rw [lintegral_runtimeTraceDensity_fraction hlogDensity]
  by_cases hlength : length < maxShrink
  · simp only [hlength, if_true, fixedShrinkSuccessMass]
    simp_rw [mul_assoc]
    rw [MeasureTheory.lintegral_const_mul]
    exact measurable_fixedShrinkSuccessWeight hlogDensity state.1 state.2 length
      (runtimeSteppedBracket logDensity state.1 width state.2 intervals
        allocation offset)
  · simp only [hlength, if_false, lintegral_zero]

/-- For fixed alignment and allocation, summing all successful rejected
lengths costs at most the allocation's own probability weight. -/
theorem sum_lintegral_runtimeTraceDensity_rejected_fraction_le
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    {width : ℝ} (hwidth : 0 < width) (intervals maxShrink : ℕ)
    (state : ℝ × ℝ) (hcurrent : state.1 ≤ logDensity state.2)
    (offset : Alignment) (allocation : ℤ) :
    (∑ length : Fin maxShrink,
      ∫⁻ rejected : Fin length → ℝ, ∫⁻ fraction : ℝ,
        runtimeTraceDensity logDensity width intervals maxShrink state
          (Sigma.mk length rejected, ((offset, allocation), fraction))
          ∂volume
        ∂(Measure.pi fun _ : Fin length => (volume : Measure ℝ))) ≤
      allocationWeight intervals allocation := by
  simp_rw [lintegral_runtimeTraceDensity_rejected_fraction hlogDensity,
    Fin.isLt, if_true]
  rw [← Finset.mul_sum]
  apply mul_le_of_le_one_right (by simp)
  exact sum_fixedShrinkSuccessMass_le_one hlogDensity state.1 state.2 maxShrink
    (runtimeSteppedBracket logDensity state.1 width state.2 intervals allocation offset)
    (validShrinkBracket_runtimeSteppedBracket logDensity state.1 state.2
      hwidth intervals allocation offset hcurrent)

/-- After integrating the normalized allocation and Haar alignment, the sum
of all successful fixed-length trace fibers remains a subprobability. -/
theorem lintegral_alignment_allocation_sum_runtimeTraceDensity_le_one
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    {width : ℝ} (hwidth : 0 < width) {intervals : ℕ}
    (hintervals : 0 < intervals) (maxShrink : ℕ)
    (state : ℝ × ℝ) (hcurrent : state.1 ≤ logDensity state.2) :
    (∫⁻ offset : Alignment, ∫⁻ allocation : ℤ,
      ∑ length : Fin maxShrink,
        ∫⁻ rejected : Fin length → ℝ, ∫⁻ fraction : ℝ,
          runtimeTraceDensity logDensity width intervals maxShrink state
            (Sigma.mk length rejected, ((offset, allocation), fraction))
            ∂volume
          ∂(Measure.pi fun _ : Fin length => (volume : Measure ℝ))
        ∂Measure.count ∂(volume : Measure Alignment)) ≤ 1 := by
  calc
    (∫⁻ offset : Alignment, ∫⁻ allocation : ℤ,
      ∑ length : Fin maxShrink,
        ∫⁻ rejected : Fin length → ℝ, ∫⁻ fraction : ℝ,
          runtimeTraceDensity logDensity width intervals maxShrink state
            (Sigma.mk length rejected, ((offset, allocation), fraction))
            ∂volume
          ∂(Measure.pi fun _ : Fin length => (volume : Measure ℝ))
        ∂Measure.count ∂(volume : Measure Alignment)) ≤
        ∫⁻ _offset : Alignment, (1 : ENNReal) ∂volume := by
      apply lintegral_mono
      intro offset
      calc
        (∫⁻ allocation : ℤ,
          ∑ length : Fin maxShrink,
            ∫⁻ rejected : Fin length → ℝ, ∫⁻ fraction : ℝ,
              runtimeTraceDensity logDensity width intervals maxShrink state
                (Sigma.mk length rejected, ((offset, allocation), fraction))
                ∂volume
              ∂(Measure.pi fun _ : Fin length => (volume : Measure ℝ))
            ∂Measure.count) ≤
            ∫⁻ allocation : ℤ, allocationWeight intervals allocation
              ∂Measure.count := by
          apply lintegral_mono
          intro allocation
          exact sum_lintegral_runtimeTraceDensity_rejected_fraction_le
            hlogDensity hwidth intervals maxShrink state hcurrent offset allocation
        _ = 1 := allocationWeight_lintegral hintervals
    _ = 1 := by simp

/-- Tonelli reorders one fixed runtime-trace base into alignment, allocation,
rejected-vector, and final-fraction order. -/
theorem lintegral_fixedRuntimeTraceBase_runtimeTraceDensity
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (width : ℝ) (intervals maxShrink length : ℕ) (state : ℝ × ℝ) :
    (∫⁻ trace : FixedRuntimeTrace length,
      runtimeTraceDensity logDensity width intervals maxShrink state
        (Sigma.mk length trace.1, trace.2) ∂fixedRuntimeTraceBase length) =
      ∫⁻ offset : Alignment, ∫⁻ allocation : ℤ,
        ∫⁻ rejected : Fin length → ℝ, ∫⁻ fraction : ℝ,
          runtimeTraceDensity logDensity width intervals maxShrink state
            (Sigma.mk length rejected, ((offset, allocation), fraction))
            ∂volume
          ∂(Measure.pi fun _ : Fin length => (volume : Measure ℝ))
        ∂Measure.count ∂(volume : Measure Alignment) := by
  let density : FixedRuntimeTrace length → ENNReal := fun trace =>
    runtimeTraceDensity logDensity width intervals maxShrink state
      (Sigma.mk length trace.1, trace.2)
  have hdensity : Measurable density :=
    (measurable_uncurry_runtimeTraceDensity_fixedLength hlogDensity width
      intervals maxShrink length).of_uncurry_left
  let restMeasure :=
    (((volume : Measure Alignment).prod (Measure.count : Measure ℤ)).prod
      (volume : Measure ℝ))
  let rejectedMeasure :=
    Measure.pi fun _ : Fin length => (volume : Measure ℝ)
  have hrest : Measurable (fun rest : (Alignment × ℤ) × ℝ =>
      ∫⁻ rejected : Fin length → ℝ,
        density (rejected, rest) ∂rejectedMeasure) :=
    hdensity.lintegral_prod_left'
  have halignmentAllocation : Measurable (fun pair : Alignment × ℤ =>
      ∫⁻ fraction : ℝ, ∫⁻ rejected : Fin length → ℝ,
        density (rejected, (pair, fraction)) ∂rejectedMeasure ∂volume) :=
    hrest.lintegral_prod_right
  unfold fixedRuntimeTraceBase
  change (∫⁻ trace, density trace ∂rejectedMeasure.prod restMeasure) = _
  calc
    (∫⁻ trace, density trace ∂rejectedMeasure.prod restMeasure) =
        ∫⁻ rest, ∫⁻ rejected,
          density (rejected, rest) ∂rejectedMeasure ∂restMeasure := by
      exact MeasureTheory.lintegral_prod_symm' density hdensity
    _ = ∫⁻ pair : Alignment × ℤ, ∫⁻ fraction : ℝ,
          ∫⁻ rejected : Fin length → ℝ,
            density (rejected, (pair, fraction)) ∂rejectedMeasure ∂volume
          ∂((volume : Measure Alignment).prod Measure.count) := by
      exact MeasureTheory.lintegral_prod _ hrest.aemeasurable
    _ = ∫⁻ offset : Alignment, ∫⁻ allocation : ℤ,
          ∫⁻ fraction : ℝ, ∫⁻ rejected : Fin length → ℝ,
            density (rejected, ((offset, allocation), fraction))
              ∂rejectedMeasure ∂volume ∂Measure.count ∂volume := by
      exact MeasureTheory.lintegral_prod _ halignmentAllocation.aemeasurable
    _ = ∫⁻ offset : Alignment, ∫⁻ allocation : ℤ,
          ∫⁻ rejected : Fin length → ℝ, ∫⁻ fraction : ℝ,
            density (rejected, ((offset, allocation), fraction))
              ∂volume ∂rejectedMeasure ∂Measure.count ∂volume := by
      apply lintegral_congr
      intro offset
      apply lintegral_congr
      intro allocation
      have hswap : Measurable (Function.uncurry
          (fun fraction : ℝ => fun rejected : Fin length → ℝ =>
            density (rejected, ((offset, allocation), fraction)))) := by
        exact hdensity.comp (by fun_prop)
      exact MeasureTheory.lintegral_lintegral_swap hswap.aemeasurable
    _ = _ := rfl

/-- Total mass of one fixed-length successful trace kernel in the reordered
runtime coordinates. -/
theorem fixedSuccessfulRuntimeTraceKernel_apply_univ
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (width : ℝ) (intervals maxShrink length : ℕ) (state : ℝ × ℝ) :
    fixedSuccessfulRuntimeTraceKernel logDensity width intervals maxShrink length
        state Set.univ =
      ∫⁻ offset : Alignment, ∫⁻ allocation : ℤ,
        ∫⁻ rejected : Fin length → ℝ, ∫⁻ fraction : ℝ,
          runtimeTraceDensity logDensity width intervals maxShrink state
            (Sigma.mk length rejected, ((offset, allocation), fraction))
            ∂volume
          ∂(Measure.pi fun _ : Fin length => (volume : Measure ℝ))
        ∂Measure.count ∂(volume : Measure Alignment) := by
  rw [fixedSuccessfulRuntimeTraceKernel,
    ProbabilityTheory.Kernel.withDensity_apply' _
      (measurable_uncurry_runtimeTraceDensity_fixedLength hlogDensity width
        intervals maxShrink length),
    ProbabilityTheory.Kernel.const_apply, Measure.restrict_univ]
  exact lintegral_fixedRuntimeTraceBase_runtimeTraceDensity hlogDensity width
    intervals maxShrink length state

/-- The rejected-vector/final-fraction mass is measurable jointly in
alignment and integer allocation. -/
theorem measurable_lintegral_runtimeTraceDensity_rejected_fraction
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (width : ℝ) (intervals maxShrink length : ℕ) (state : ℝ × ℝ) :
    Measurable (fun pair : Alignment × ℤ =>
      ∫⁻ rejected : Fin length → ℝ, ∫⁻ fraction : ℝ,
        runtimeTraceDensity logDensity width intervals maxShrink state
          (Sigma.mk length rejected, ((pair.1, pair.2), fraction))
          ∂volume
        ∂(Measure.pi fun _ : Fin length => (volume : Measure ℝ))) := by
  have hdensity : Measurable (fun point :
      ((Alignment × ℤ) × (Fin length → ℝ)) × ℝ =>
      runtimeTraceDensity logDensity width intervals maxShrink state
        (Sigma.mk length point.1.2, ((point.1.1.1, point.1.1.2), point.2))) := by
    have hfixed : Measurable (fun trace : FixedRuntimeTrace length =>
        runtimeTraceDensity logDensity width intervals maxShrink state
          (Sigma.mk length trace.1, trace.2)) :=
      (measurable_uncurry_runtimeTraceDensity_fixedLength hlogDensity width
        intervals maxShrink length).of_uncurry_left
    have hpack : Measurable (fun point :
        ((Alignment × ℤ) × (Fin length → ℝ)) × ℝ =>
        ((point.1.2, (point.1.1, point.2)) : FixedRuntimeTrace length)) := by
      fun_prop
    exact hfixed.comp hpack
  exact hdensity.lintegral_prod_right.lintegral_prod_right

/-- After integrating allocation as well, fixed-length mass is measurable in
the Haar alignment. -/
theorem measurable_lintegral_allocation_runtimeTraceDensity_rejected_fraction
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (width : ℝ) (intervals maxShrink length : ℕ) (state : ℝ × ℝ) :
    Measurable (fun offset : Alignment => ∫⁻ allocation : ℤ,
      ∫⁻ rejected : Fin length → ℝ, ∫⁻ fraction : ℝ,
        runtimeTraceDensity logDensity width intervals maxShrink state
          (Sigma.mk length rejected, ((offset, allocation), fraction))
          ∂volume
        ∂(Measure.pi fun _ : Fin length => (volume : Measure ℝ))
      ∂Measure.count) := by
  exact (measurable_lintegral_runtimeTraceDensity_rejected_fraction
    hlogDensity width intervals maxShrink length state).lintegral_prod_right

/-- The total mass of the finite sum kernel is the nested integral whose
pointwise length sum was bounded above. -/
theorem successfulRuntimeTraceKernel_apply_univ
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (width : ℝ) (intervals maxShrink : ℕ) (state : ℝ × ℝ) :
    successfulRuntimeTraceKernel logDensity width intervals maxShrink state Set.univ =
      ∫⁻ offset : Alignment, ∫⁻ allocation : ℤ,
        ∑ length : Fin maxShrink,
          ∫⁻ rejected : Fin length → ℝ, ∫⁻ fraction : ℝ,
            runtimeTraceDensity logDensity width intervals maxShrink state
              (Sigma.mk length rejected, ((offset, allocation), fraction))
              ∂volume
            ∂(Measure.pi fun _ : Fin length => (volume : Measure ℝ))
        ∂Measure.count ∂(volume : Measure Alignment) := by
  rw [successfulRuntimeTraceKernel,
    ProbabilityTheory.Kernel.finsetSum_apply' Finset.univ]
  simp_rw [ProbabilityTheory.Kernel.map_apply' _
    (measurable_runtimeTraceOfFixed _) _ MeasurableSet.univ,
    Set.preimage_univ,
    fixedSuccessfulRuntimeTraceKernel_apply_univ hlogDensity]
  rw [← MeasureTheory.lintegral_finsetSum Finset.univ]
  · apply lintegral_congr
    intro offset
    rw [← MeasureTheory.lintegral_finsetSum Finset.univ]
    intro length _
    exact (measurable_lintegral_runtimeTraceDensity_rejected_fraction
      hlogDensity width intervals maxShrink length state).comp
        (measurable_const.prodMk measurable_id)
  · intro length _
    exact measurable_lintegral_allocation_runtimeTraceDensity_rejected_fraction
      hlogDensity width intervals maxShrink length state

theorem successfulRuntimeTraceKernel_apply_univ_le_one
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    {width : ℝ} (hwidth : 0 < width) {intervals : ℕ}
    (hintervals : 0 < intervals) (maxShrink : ℕ)
    (state : ℝ × ℝ) (hcurrent : state.1 ≤ logDensity state.2) :
    successfulRuntimeTraceKernel logDensity width intervals maxShrink
      state Set.univ ≤ 1 := by
  rw [successfulRuntimeTraceKernel_apply_univ hlogDensity]
  exact lintegral_alignment_allocation_sum_runtimeTraceDensity_le_one
    hlogDensity hwidth hintervals maxShrink state hcurrent

/-- Valid augmented slice states are those whose sampled log height lies
below the current state's log density. -/
def runtimeSliceDomain (logDensity : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {state | state.1 ≤ logDensity state.2}

theorem measurableSet_runtimeSliceDomain
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity) :
    MeasurableSet (runtimeSliceDomain logDensity) :=
  measurableSet_le measurable_fst (hlogDensity.comp measurable_snd)

/-- Successful runtime kernel guarded to zero outside the valid augmented
slice domain. This makes the trace construction a subkernel on the full
ambient state space while agreeing literally with the executable density on
every state emitted by the log-height kernel. -/
noncomputable def guardedSuccessfulRuntimeTraceKernel
    (logDensity : ℝ → ℝ) (hlogDensity : Measurable logDensity)
    (width : ℝ) (intervals maxShrink : ℕ) :
    ProbabilityTheory.Kernel (ℝ × ℝ) RuntimeRandomTrace :=
  by
    classical
    exact ProbabilityTheory.Kernel.piecewise
      (measurableSet_runtimeSliceDomain hlogDensity)
      (successfulRuntimeTraceKernel logDensity width intervals maxShrink) 0

theorem guardedSuccessfulRuntimeTraceKernel_isSFinite
    (logDensity : ℝ → ℝ) (hlogDensity : Measurable logDensity)
    (width : ℝ) (intervals maxShrink : ℕ) :
    ProbabilityTheory.IsSFiniteKernel
      (guardedSuccessfulRuntimeTraceKernel logDensity hlogDensity width intervals
        maxShrink) := by
  classical
  letI : ProbabilityTheory.IsSFiniteKernel
      (successfulRuntimeTraceKernel logDensity width intervals maxShrink) :=
    successfulRuntimeTraceKernel_isSFinite logDensity width intervals maxShrink
  unfold guardedSuccessfulRuntimeTraceKernel
  infer_instance

theorem guardedSuccessfulRuntimeTraceKernel_apply_univ_le_one
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    {width : ℝ} (hwidth : 0 < width) {intervals : ℕ}
    (hintervals : 0 < intervals) (maxShrink : ℕ) (state : ℝ × ℝ) :
    guardedSuccessfulRuntimeTraceKernel logDensity hlogDensity width intervals
      maxShrink state Set.univ ≤ 1 := by
  classical
  rw [guardedSuccessfulRuntimeTraceKernel,
    ProbabilityTheory.Kernel.piecewise_apply']
  split_ifs with hstate
  · exact successfulRuntimeTraceKernel_apply_univ_le_one hlogDensity hwidth
      hintervals maxShrink state hstate
  · simp

/-- Complete probability kernel obtained from the certified finite-fiber
successful subkernel by adjoining one exhaustion/identity atom. -/
noncomputable def completedRuntimeTraceKernelFromFibers
    (logDensity : ℝ → ℝ) (hlogDensity : Measurable logDensity)
    (width : ℝ) (intervals maxShrink : ℕ) :
    ProbabilityTheory.Kernel (ℝ × ℝ)
      (Mcmc.Kernel.CompletedTrace RuntimeRandomTrace) :=
  let successful := guardedSuccessfulRuntimeTraceKernel logDensity hlogDensity
    width intervals maxShrink
  successful.map Sum.inl +
    (ProbabilityTheory.Kernel.const (ℝ × ℝ)
      (Measure.dirac (Sum.inr ()))).withDensity
        (fun state _ => 1 - successful state Set.univ)

theorem completedRuntimeTraceKernelFromFibers_isMarkovKernel
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    {width : ℝ} (hwidth : 0 < width) {intervals : ℕ}
    (hintervals : 0 < intervals) (maxShrink : ℕ) :
    ProbabilityTheory.IsMarkovKernel
      (completedRuntimeTraceKernelFromFibers logDensity hlogDensity width intervals
        maxShrink) := by
  let successful := guardedSuccessfulRuntimeTraceKernel logDensity hlogDensity
    width intervals maxShrink
  letI : ProbabilityTheory.IsSFiniteKernel successful :=
    guardedSuccessfulRuntimeTraceKernel_isSFinite logDensity hlogDensity width
      intervals maxShrink
  have hmass : Measurable (fun state : ℝ × ℝ => successful state Set.univ) :=
    ProbabilityTheory.Kernel.measurable_coe successful MeasurableSet.univ
  have hfailureDensity : Measurable (Function.uncurry
      (fun state : ℝ × ℝ => fun _ : Mcmc.Kernel.CompletedTrace RuntimeRandomTrace =>
        1 - successful state Set.univ)) :=
    measurable_const.sub (hmass.comp measurable_fst)
  constructor
  intro state
  constructor
  rw [completedRuntimeTraceKernelFromFibers,
    ProbabilityTheory.Kernel.add_apply, Measure.add_apply,
    ProbabilityTheory.Kernel.map_apply' successful measurable_inl state
      MeasurableSet.univ,
    Set.preimage_univ,
    ProbabilityTheory.Kernel.withDensity_apply' _ hfailureDensity,
    ProbabilityTheory.Kernel.const_apply, Measure.restrict_univ]
  rw [MeasureTheory.lintegral_dirac']
  · exact add_tsub_cancel_of_le
      (guardedSuccessfulRuntimeTraceKernel_apply_univ_le_one hlogDensity hwidth
        hintervals maxShrink state)
  · exact measurable_const

/-- Complete finite-budget trace kernel. Successful traces use the concrete
density above; all missing mass is one explicit exhaustion outcome that the
sampler interprets as the identity update. -/
noncomputable def completedRuntimeTraceKernel
    (logDensity : ℝ → ℝ) (width : ℝ) (intervals maxShrink : ℕ) :
    ProbabilityTheory.Kernel (ℝ × ℝ)
      (Mcmc.Kernel.CompletedTrace RuntimeRandomTrace) :=
  Mcmc.Kernel.completedTraceKernel runtimeRandomTraceBase
    (runtimeTraceDensity logDensity width intervals maxShrink)

theorem completedRuntimeTraceKernel_isMarkovKernel
    (logDensity : ℝ → ℝ) (width : ℝ) (intervals maxShrink : ℕ)
    (hmeasurable : Measurable (Function.uncurry
      (runtimeTraceDensity logDensity width intervals maxShrink)))
    (hsubprobability : ∀ state,
      Mcmc.Kernel.successfulTraceMass runtimeRandomTraceBase
        (runtimeTraceDensity logDensity width intervals maxShrink) state ≤ 1) :
    ProbabilityTheory.IsMarkovKernel
      (completedRuntimeTraceKernel logDensity width intervals maxShrink) := by
  exact Mcmc.Kernel.completedTraceKernel_isMarkovKernel
    runtimeRandomTraceBase
      (runtimeTraceDensity logDensity width intervals maxShrink)
    hmeasurable hsubprobability

/-! ### Primitive runtime-trace reversal -/

/-- Reroot a primitive successful runtime trace without storing its stopped
bracket. The bracket is derived from the old augmented state and trace,
the accepted fraction becomes the new state, and the reverse fraction records
the old state in that same bracket. -/
noncomputable def primitiveRuntimeAugmentedReverse
    (logDensity : ℝ → ℝ) (width : ℝ) (intervals : ℕ)
    (point : (ℝ × ℝ) × RuntimeRandomTrace) :
    (ℝ × ℝ) × RuntimeRandomTrace :=
  let bracket := runtimeFinalBracket logDensity point.1.1 width point.1.2
    intervals point.2
  let accepted := acceptedProposalReverse bracket.1 bracket.2
    (point.1.2, point.2.2.2)
  ((point.1.1, accepted.1),
    (point.2.1,
      (alignmentAllocationReverse width point.1.2 accepted.1 point.2.2.1,
        accepted.2)))

theorem primitiveRuntimeAugmentedReverse_newState
    (logDensity : ℝ → ℝ) (width : ℝ) (intervals : ℕ)
    (point : (ℝ × ℝ) × RuntimeRandomTrace) :
    (primitiveRuntimeAugmentedReverse logDensity width intervals point).1 =
      (point.1.1,
        runtimeAcceptedPoint logDensity point.1.1 width point.1.2 intervals
          point.2) := by
  rfl

theorem primitiveRuntimeAugmentedReverse_rejected
    (logDensity : ℝ → ℝ) (width : ℝ) (intervals : ℕ)
    (point : (ℝ × ℝ) × RuntimeRandomTrace) :
    (primitiveRuntimeAugmentedReverse logDensity width intervals point).2.1 =
      point.2.1 := by
  rfl

theorem primitiveRuntimeAugmentedReverse_grid
    (logDensity : ℝ → ℝ) (width : ℝ) (intervals : ℕ)
    (point : (ℝ × ℝ) × RuntimeRandomTrace) :
    (primitiveRuntimeAugmentedReverse logDensity width intervals point).2.2.1 =
      alignmentAllocationReverse width point.1.2
        (runtimeAcceptedPoint logDensity point.1.1 width point.1.2 intervals
          point.2) point.2.2.1 := by
  rfl

theorem primitiveRuntimeAugmentedReverse_fraction
    (logDensity : ℝ → ℝ) (width : ℝ) (intervals : ℕ)
    (point : (ℝ × ℝ) × RuntimeRandomTrace) :
    (primitiveRuntimeAugmentedReverse logDensity width intervals point).2.2.2 =
      (point.1.2 -
        (runtimeFinalBracket logDensity point.1.1 width point.1.2 intervals
          point.2).1) /
        ((runtimeFinalBracket logDensity point.1.1 width point.1.2 intervals
          point.2).2 -
        (runtimeFinalBracket logDensity point.1.1 width point.1.2 intervals
          point.2).1) := by
  rfl

/-- If rerooting gives the same stepped-out bracket and no rejected point
separates the old and accepted states, replaying the primitive rejected trace
derives exactly the same final bracket in reverse. -/
theorem primitiveRuntimeFinalBracket_reverse
    (logDensity : ℝ → ℝ) (threshold width old : ℝ) (intervals : ℕ)
    (trace : RuntimeRandomTrace)
    (hstepped :
      runtimeSteppedBracket logDensity threshold width old intervals
          trace.2.1.2 trace.2.1.1 =
        runtimeSteppedBracket logDensity threshold width
          (runtimeAcceptedPoint logDensity threshold width old intervals trace)
          intervals
          (alignmentAllocationReverse width old
            (runtimeAcceptedPoint logDensity threshold width old intervals trace)
            trace.2.1).2
          (alignmentAllocationReverse width old
            (runtimeAcceptedPoint logDensity threshold width old intervals trace)
            trace.2.1).1)
    (hsame : ∀ rejected ∈ List.ofFn trace.1.2,
      (rejected < old) =
        (rejected < runtimeAcceptedPoint logDensity threshold width old intervals trace)) :
    runtimeFinalBracket logDensity threshold width old intervals trace =
      runtimeFinalBracket logDensity threshold width
        (runtimeAcceptedPoint logDensity threshold width old intervals trace)
        intervals
        (primitiveRuntimeAugmentedReverse logDensity width intervals
          ((threshold, old), trace)).2 := by
  unfold runtimeFinalBracket
  rw [primitiveRuntimeAugmentedReverse_rejected,
    primitiveRuntimeAugmentedReverse_grid]
  rw [← hstepped]
  exact shrinkRejectedPoints_eq_of_sameSide hsame

/-- The proof-oriented dependent-allocation stepping-out reversal specializes
to the primitive runtime's unrestricted integer allocation on the global
valid-allocation event. -/
theorem runtimeSteppedBracket_reverse
    (logDensity : ℝ → ℝ) (threshold : ℝ) (intervals : ℕ)
    {width old new : ℝ} (hwidth : width ≠ 0) (grid : Alignment × ℤ)
    (hgrid : grid ∈ globalValidAllocation intervals width old new)
    (hleftNonneg : 0 ≤ integerAlignmentShift width old new grid.1 →
      ∀ index < (integerAlignmentShift width old new grid.1).toNat,
        threshold < logDensity
          (initialLeft width new
            (reverseOffset width old new (alignmentCoordinate grid.1)) -
              (index : ℝ) * width))
    (hleftNonpos : integerAlignmentShift width old new grid.1 ≤ 0 →
      ∀ index < (-integerAlignmentShift width old new grid.1).toNat,
        threshold < logDensity
          (initialLeft width old (alignmentCoordinate grid.1) -
            (index : ℝ) * width))
    (hrightNonneg : 0 ≤ integerAlignmentShift width old new grid.1 →
      ∀ index < (integerAlignmentShift width old new grid.1).toNat,
        threshold < logDensity
          (initialRight width old (alignmentCoordinate grid.1) +
            (index : ℝ) * width))
    (hrightNonpos : integerAlignmentShift width old new grid.1 ≤ 0 →
      ∀ index < (-integerAlignmentShift width old new grid.1).toNat,
        threshold < logDensity
          (initialRight width new
            (reverseOffset width old new (alignmentCoordinate grid.1)) +
              (index : ℝ) * width)) :
    runtimeSteppedBracket logDensity threshold width old intervals grid.2 grid.1 =
      runtimeSteppedBracket logDensity threshold width new intervals
        (alignmentAllocationReverse width old new grid).2
        (alignmentAllocationReverse width old new grid).1 := by
  let shift := integerAlignmentShift width old new grid.1
  have hvalid : 0 ≤ grid.2 ∧ grid.2 < intervals ∧
      0 ≤ grid.2 + shift ∧ grid.2 + shift < intervals := by
    simpa only [globalValidAllocation, Set.mem_setOf_eq, shift] using hgrid
  let allocation : ValidAllocation intervals shift := ⟨grid.2, hvalid⟩
  have hproof := steppedBracket_reverseAllocation logDensity threshold hwidth
    (show shift =
      ⌊alignmentCoordinate grid.1 + (new - old) / width⌋ by
        rfl)
    allocation hleftNonneg hleftNonpos hrightNonneg hrightNonpos
  rw [runtimeSteppedBracket_eq_steppedBracket logDensity threshold width old
    allocation grid.1]
  let reversed := reverseAllocation intervals shift allocation
  change steppedBracket logDensity threshold width old
      (alignmentCoordinate grid.1) allocation =
    runtimeSteppedBracket logDensity threshold width new intervals
      reversed.1 (reverseAlignment width old new grid.1)
  rw [runtimeSteppedBracket_eq_steppedBracket logDensity threshold width new
    reversed (reverseAlignment width old new grid.1)]
  rw [alignmentCoordinate_reverseAlignment]
  exact hproof

/-- End-to-end derived-bracket equality for the primitive runtime trace,
with the stepping-out interior obligations exposed explicitly. -/
theorem primitiveRuntimeFinalBracket_reverse_of_success
    (logDensity : ℝ → ℝ) (threshold : ℝ) (intervals : ℕ)
    {width old : ℝ} (hwidth : width ≠ 0) (trace : RuntimeRandomTrace)
    (hgrid : trace.2.1 ∈ globalValidAllocation intervals width old
      (runtimeAcceptedPoint logDensity threshold width old intervals trace))
    (hleftNonneg : 0 ≤ integerAlignmentShift width old
        (runtimeAcceptedPoint logDensity threshold width old intervals trace)
        trace.2.1.1 →
      ∀ index < (integerAlignmentShift width old
        (runtimeAcceptedPoint logDensity threshold width old intervals trace)
        trace.2.1.1).toNat,
        threshold < logDensity
          (initialLeft width
            (runtimeAcceptedPoint logDensity threshold width old intervals trace)
            (reverseOffset width old
              (runtimeAcceptedPoint logDensity threshold width old intervals trace)
              (alignmentCoordinate trace.2.1.1)) - (index : ℝ) * width))
    (hleftNonpos : integerAlignmentShift width old
        (runtimeAcceptedPoint logDensity threshold width old intervals trace)
        trace.2.1.1 ≤ 0 →
      ∀ index < (-integerAlignmentShift width old
        (runtimeAcceptedPoint logDensity threshold width old intervals trace)
        trace.2.1.1).toNat,
        threshold < logDensity
          (initialLeft width old (alignmentCoordinate trace.2.1.1) -
            (index : ℝ) * width))
    (hrightNonneg : 0 ≤ integerAlignmentShift width old
        (runtimeAcceptedPoint logDensity threshold width old intervals trace)
        trace.2.1.1 →
      ∀ index < (integerAlignmentShift width old
        (runtimeAcceptedPoint logDensity threshold width old intervals trace)
        trace.2.1.1).toNat,
        threshold < logDensity
          (initialRight width old (alignmentCoordinate trace.2.1.1) +
            (index : ℝ) * width))
    (hrightNonpos : integerAlignmentShift width old
        (runtimeAcceptedPoint logDensity threshold width old intervals trace)
        trace.2.1.1 ≤ 0 →
      ∀ index < (-integerAlignmentShift width old
        (runtimeAcceptedPoint logDensity threshold width old intervals trace)
        trace.2.1.1).toNat,
        threshold < logDensity
          (initialRight width
            (runtimeAcceptedPoint logDensity threshold width old intervals trace)
            (reverseOffset width old
              (runtimeAcceptedPoint logDensity threshold width old intervals trace)
              (alignmentCoordinate trace.2.1.1)) + (index : ℝ) * width))
    (hsame : ∀ rejected ∈ List.ofFn trace.1.2,
      (rejected < old) =
        (rejected < runtimeAcceptedPoint logDensity threshold width old intervals trace)) :
    runtimeFinalBracket logDensity threshold width old intervals trace =
      runtimeFinalBracket logDensity threshold width
        (runtimeAcceptedPoint logDensity threshold width old intervals trace)
        intervals
        (primitiveRuntimeAugmentedReverse logDensity width intervals
          ((threshold, old), trace)).2 := by
  apply primitiveRuntimeFinalBracket_reverse logDensity threshold width old
    intervals trace
  · exact runtimeSteppedBracket_reverse logDensity threshold intervals hwidth
      trace.2.1 hgrid hleftNonneg hleftNonpos hrightNonneg hrightNonpos
  · exact hsame

/-- Once the deterministically derived bracket agrees in reverse, the
bracket-free primitive runtime rerooting is an involution. -/
theorem primitiveRuntimeAugmentedReverse_involutive_of_finalBracket
    (logDensity : ℝ → ℝ) {width : ℝ} (hwidth : width ≠ 0)
    (intervals : ℕ) (point : (ℝ × ℝ) × RuntimeRandomTrace)
    (hbracket :
      (runtimeFinalBracket logDensity point.1.1 width point.1.2 intervals
        point.2).1 <
      (runtimeFinalBracket logDensity point.1.1 width point.1.2 intervals
        point.2).2)
    (hreverse :
      runtimeFinalBracket logDensity point.1.1 width
          (runtimeAcceptedPoint logDensity point.1.1 width point.1.2 intervals
            point.2) intervals
          (primitiveRuntimeAugmentedReverse logDensity width intervals point).2 =
        runtimeFinalBracket logDensity point.1.1 width point.1.2 intervals
          point.2) :
    primitiveRuntimeAugmentedReverse logDensity width intervals
        (primitiveRuntimeAugmentedReverse logDensity width intervals point) = point := by
  rcases point with ⟨⟨threshold, old⟩, trace⟩
  let bracket := runtimeFinalBracket logDensity threshold width old intervals trace
  let accepted := acceptedProposalReverse bracket.1 bracket.2
    (old, trace.2.2)
  have haccepted := acceptedProposalReverse_involutive
    (sub_ne_zero.mpr hbracket.ne') (old, trace.2.2)
  have hgrid := alignmentAllocationReverse_reverse
    (old := old) (new := accepted.1) hwidth trace.2.1
  change primitiveRuntimeAugmentedReverse logDensity width intervals
      ((threshold, accepted.1),
        (trace.1,
          (alignmentAllocationReverse width old accepted.1 trace.2.1,
            accepted.2))) = ((threshold, old), trace)
  unfold primitiveRuntimeAugmentedReverse
  simp only
  have hreverse' : runtimeFinalBracket logDensity threshold width accepted.1 intervals
      (trace.1,
        (alignmentAllocationReverse width old accepted.1 trace.2.1,
          accepted.2)) = bracket := by
    exact hreverse
  rw [hreverse']
  rw [show acceptedProposalReverse bracket.1 bracket.2
      (accepted.1, accepted.2) = (old, trace.2.2) by exact haccepted]
  rw [hgrid]

/-- Replaying a primitive reverse trace whose derived bracket agrees recovers
the old state as its accepted point. -/
theorem primitiveRuntimeAcceptedPoint_reverse
    (logDensity : ℝ → ℝ) {width : ℝ} (intervals : ℕ)
    (point : (ℝ × ℝ) × RuntimeRandomTrace)
    (hbracket :
      (runtimeFinalBracket logDensity point.1.1 width point.1.2 intervals
        point.2).1 <
      (runtimeFinalBracket logDensity point.1.1 width point.1.2 intervals
        point.2).2)
    (hreverse :
      runtimeFinalBracket logDensity point.1.1 width
          (runtimeAcceptedPoint logDensity point.1.1 width point.1.2 intervals
            point.2) intervals
          (primitiveRuntimeAugmentedReverse logDensity width intervals point).2 =
        runtimeFinalBracket logDensity point.1.1 width point.1.2 intervals
          point.2) :
    runtimeAcceptedPoint logDensity point.1.1 width
        (runtimeAcceptedPoint logDensity point.1.1 width point.1.2 intervals
          point.2) intervals
        (primitiveRuntimeAugmentedReverse logDensity width intervals point).2 =
      point.1.2 := by
  let bracket := runtimeFinalBracket logDensity point.1.1 width point.1.2
    intervals point.2
  change
    (runtimeFinalBracket logDensity point.1.1 width
      (runtimeAcceptedPoint logDensity point.1.1 width point.1.2 intervals point.2)
      intervals
      (primitiveRuntimeAugmentedReverse logDensity width intervals point).2).1 +
      ((runtimeFinalBracket logDensity point.1.1 width
        (runtimeAcceptedPoint logDensity point.1.1 width point.1.2 intervals point.2)
        intervals
        (primitiveRuntimeAugmentedReverse logDensity width intervals point).2).2 -
       (runtimeFinalBracket logDensity point.1.1 width
        (runtimeAcceptedPoint logDensity point.1.1 width point.1.2 intervals point.2)
        intervals
        (primitiveRuntimeAugmentedReverse logDensity width intervals point).2).1) *
      (primitiveRuntimeAugmentedReverse logDensity width intervals point).2.2.2 =
      point.1.2
  rw [hreverse, primitiveRuntimeAugmentedReverse_fraction]
  have hne : bracket.2 - bracket.1 ≠ 0 := sub_ne_zero.mpr hbracket.ne'
  change bracket.1 + (bracket.2 - bracket.1) *
      ((point.1.2 - bracket.1) / (bracket.2 - bracket.1)) = point.1.2
  field_simp
  ring

/-- If the old point lies in the derived final bracket, the primitive reverse
fraction is again a valid unit fraction. -/
theorem primitiveRuntimeAugmentedReverse_fraction_mem
    (logDensity : ℝ → ℝ) (width : ℝ) (intervals : ℕ)
    (point : (ℝ × ℝ) × RuntimeRandomTrace)
    (hold : point.1.2 ∈ Set.Ico
      (runtimeFinalBracket logDensity point.1.1 width point.1.2 intervals
        point.2).1
      (runtimeFinalBracket logDensity point.1.1 width point.1.2 intervals
        point.2).2) :
    (primitiveRuntimeAugmentedReverse logDensity width intervals point).2.2.2 ∈
      Set.Ico (0 : ℝ) 1 := by
  rw [primitiveRuntimeAugmentedReverse_fraction]
  let bracket := runtimeFinalBracket logDensity point.1.1 width point.1.2
    intervals point.2
  have hbracketlt : bracket.1 < bracket.2 := by
    exact lt_of_le_of_lt hold.1 hold.2
  have hwidth : 0 < bracket.2 - bracket.1 := sub_pos.mpr hbracketlt
  constructor
  · exact div_nonneg (sub_nonneg.mpr hold.1) hwidth.le
  · rw [div_lt_one hwidth]
    linarith [hold.2]

/-- The primitive successful density is pointwise invariant under rerooting
once the derived-bracket, allocation, and accepted-coordinate replay
conditions are established. -/
theorem runtimeTraceDensity_primitiveReverse
    (logDensity : ℝ → ℝ) {width : ℝ} (intervals maxShrink : ℕ)
    (point : (ℝ × ℝ) × RuntimeRandomTrace)
    (hwidth : width ≠ 0)
    (hlength : point.2.1.1 < maxShrink)
    (hgrid : point.2.2.1 ∈ globalValidAllocation intervals width point.1.2
      (runtimeAcceptedPoint logDensity point.1.1 width point.1.2 intervals
        point.2))
    (hfraction : point.2.2.2 ∈ Set.Ico (0 : ℝ) 1)
    (hnew : point.1.1 ≤ logDensity
      (runtimeAcceptedPoint logDensity point.1.1 width point.1.2 intervals
        point.2))
    (hold : point.1.1 ≤ logDensity point.1.2)
    (hreverseFraction :
      (primitiveRuntimeAugmentedReverse logDensity width intervals point).2.2.2 ∈
        Set.Ico (0 : ℝ) 1)
    (hstepped :
      runtimeSteppedBracket logDensity point.1.1 width point.1.2 intervals
          point.2.2.1.2 point.2.2.1.1 =
        runtimeSteppedBracket logDensity point.1.1 width
          (runtimeAcceptedPoint logDensity point.1.1 width point.1.2 intervals
            point.2) intervals
          (primitiveRuntimeAugmentedReverse logDensity width intervals point).2.2.1.2
          (primitiveRuntimeAugmentedReverse logDensity width intervals point).2.2.1.1)
    (hsame : ∀ rejected ∈ List.ofFn point.2.1.2,
      (rejected < point.1.2) =
        (rejected < runtimeAcceptedPoint logDensity point.1.1 width point.1.2
          intervals point.2))
    (hbracket :
      (runtimeFinalBracket logDensity point.1.1 width point.1.2 intervals
        point.2).1 <
      (runtimeFinalBracket logDensity point.1.1 width point.1.2 intervals
        point.2).2)
    (hfinal :
      runtimeFinalBracket logDensity point.1.1 width
          (runtimeAcceptedPoint logDensity point.1.1 width point.1.2 intervals
            point.2) intervals
          (primitiveRuntimeAugmentedReverse logDensity width intervals point).2 =
        runtimeFinalBracket logDensity point.1.1 width point.1.2 intervals
          point.2) :
    runtimeTraceDensity logDensity width intervals maxShrink
        (primitiveRuntimeAugmentedReverse logDensity width intervals point).1
        (primitiveRuntimeAugmentedReverse logDensity width intervals point).2 =
      runtimeTraceDensity logDensity width intervals maxShrink point.1 point.2 := by
  let new := runtimeAcceptedPoint logDensity point.1.1 width point.1.2 intervals
    point.2
  have hreverseGrid :
      (primitiveRuntimeAugmentedReverse logDensity width intervals point).2.2.1 ∈
        globalValidAllocation intervals width new point.1.2 := by
    have hmembership := hgrid
    rw [← alignmentAllocationReverse_preimage_globalValidAllocation hwidth]
      at hmembership
    simpa [new, primitiveRuntimeAugmentedReverse_grid] using hmembership
  have hrecover : runtimeAcceptedPoint logDensity point.1.1 width new intervals
      (primitiveRuntimeAugmentedReverse logDensity width intervals point).2 =
      point.1.2 :=
    primitiveRuntimeAcceptedPoint_reverse logDensity intervals point hbracket hfinal
  have hweight :
      rejectedTraceWeight logDensity point.1.1 new
          (List.ofFn point.2.1.2)
          (runtimeSteppedBracket logDensity point.1.1 width new intervals
            (primitiveRuntimeAugmentedReverse logDensity width intervals point).2.2.1.2
            (primitiveRuntimeAugmentedReverse logDensity width intervals point).2.2.1.1) =
        rejectedTraceWeight logDensity point.1.1 point.1.2
          (List.ofFn point.2.1.2)
          (runtimeSteppedBracket logDensity point.1.1 width point.1.2 intervals
            point.2.2.1.2 point.2.2.1.1) := by
    rw [← hstepped]
    exact (rejectedTraceWeight_eq_of_sameSide logDensity point.1.1 hsame).symm
  have hforwardAllocation : 0 ≤ point.2.2.1.2 ∧
      point.2.2.1.2 < intervals := ⟨hgrid.1, hgrid.2.1⟩
  have hreverseAllocation :
      0 ≤ (primitiveRuntimeAugmentedReverse logDensity width intervals point).2.2.1.2 ∧
      (primitiveRuntimeAugmentedReverse logDensity width intervals point).2.2.1.2 <
        intervals := ⟨hreverseGrid.1, hreverseGrid.2.1⟩
  have hrejectedSequence := primitiveRuntimeAugmentedReverse_rejected
    logDensity width intervals point
  have hreverseLength :
      (primitiveRuntimeAugmentedReverse logDensity width intervals point).2.1.1 =
        point.2.1.1 := congrArg Sigma.fst hrejectedSequence
  have hrejectedList :
      List.ofFn
          (primitiveRuntimeAugmentedReverse logDensity width intervals point).2.1.2 =
        List.ofFn point.2.1.2 :=
    congrArg (fun sequence : RejectedSequence => List.ofFn sequence.2)
      hrejectedSequence
  have hforwardAccepted : point.1.1 ≤ logDensity
      (let bracket := shrinkRejectedPoints point.1.2 (List.ofFn point.2.1.2)
        (runtimeSteppedBracket logDensity point.1.1 width point.1.2 intervals
          point.2.2.1.2 point.2.2.1.1)
       bracket.1 + (bracket.2 - bracket.1) * point.2.2.2) := by
    exact hnew
  have hreverseAccepted : point.1.1 ≤ logDensity
      (let reverseTrace :=
          (primitiveRuntimeAugmentedReverse logDensity width intervals point).2
       let bracket := shrinkRejectedPoints new (List.ofFn reverseTrace.1.2)
        (runtimeSteppedBracket logDensity point.1.1 width new intervals
          reverseTrace.2.1.2 reverseTrace.2.1.1)
       bracket.1 + (bracket.2 - bracket.1) * reverseTrace.2.2) := by
    change point.1.1 ≤ logDensity
      (runtimeAcceptedPoint logDensity point.1.1 width new intervals
        (primitiveRuntimeAugmentedReverse logDensity width intervals point).2)
    rw [hrecover]
    exact hold
  have hforwardCondition : point.2.1.1 < maxShrink ∧
      0 ≤ point.2.2.1.2 ∧ point.2.2.1.2 < intervals ∧
      point.2.2.2 ∈ Set.Ico (0 : ℝ) 1 ∧
      point.1.1 ≤ logDensity
        (let bracket := shrinkRejectedPoints point.1.2 (List.ofFn point.2.1.2)
          (runtimeSteppedBracket logDensity point.1.1 width point.1.2 intervals
            point.2.2.1.2 point.2.2.1.1)
         bracket.1 + (bracket.2 - bracket.1) * point.2.2.2) :=
    ⟨hlength, hforwardAllocation.1, hforwardAllocation.2, hfraction,
      hforwardAccepted⟩
  have hreverseCondition :
      (primitiveRuntimeAugmentedReverse logDensity width intervals point).2.1.1 <
          maxShrink ∧
      0 ≤ (primitiveRuntimeAugmentedReverse logDensity width intervals point).2.2.1.2 ∧
      (primitiveRuntimeAugmentedReverse logDensity width intervals point).2.2.1.2 <
          intervals ∧
      (primitiveRuntimeAugmentedReverse logDensity width intervals point).2.2.2 ∈
          Set.Ico (0 : ℝ) 1 ∧
      point.1.1 ≤ logDensity
        (let reverseTrace :=
          (primitiveRuntimeAugmentedReverse logDensity width intervals point).2
         let bracket := shrinkRejectedPoints new (List.ofFn reverseTrace.1.2)
          (runtimeSteppedBracket logDensity point.1.1 width new intervals
            reverseTrace.2.1.2 reverseTrace.2.1.1)
         bracket.1 + (bracket.2 - bracket.1) * reverseTrace.2.2) :=
    ⟨hreverseLength.symm ▸ hlength, hreverseAllocation.1,
      hreverseAllocation.2, hreverseFraction, hreverseAccepted⟩
  simp only [runtimeTraceDensity, primitiveRuntimeAugmentedReverse_newState]
  rw [if_pos hreverseCondition, if_pos hforwardCondition]
  rw [hrejectedList, hweight]

/-- Exact certificate carried by a successful primitive runtime trace. It
contains only properties of coordinates the algorithm actually consumes; the
stopped and final brackets remain derived data. -/
structure PrimitiveRuntimeSuccess
    (logDensity : ℝ → ℝ) (width : ℝ) (intervals maxShrink : ℕ)
    (point : (ℝ × ℝ) × RuntimeRandomTrace) : Prop where
  length_lt : point.2.1.1 < maxShrink
  grid_valid : point.2.2.1 ∈ globalValidAllocation intervals width point.1.2
    (runtimeAcceptedPoint logDensity point.1.1 width point.1.2 intervals point.2)
  fraction_mem : point.2.2.2 ∈ Set.Ico (0 : ℝ) 1
  old_mem : point.1.2 ∈ Set.Ico
    (runtimeFinalBracket logDensity point.1.1 width point.1.2 intervals point.2).1
    (runtimeFinalBracket logDensity point.1.1 width point.1.2 intervals point.2).2
  old_in_slice : point.1.1 ≤ logDensity point.1.2
  new_in_slice : point.1.1 ≤ logDensity
    (runtimeAcceptedPoint logDensity point.1.1 width point.1.2 intervals point.2)
  stepped_reverse :
    runtimeSteppedBracket logDensity point.1.1 width point.1.2 intervals
        point.2.2.1.2 point.2.2.1.1 =
      runtimeSteppedBracket logDensity point.1.1 width
        (runtimeAcceptedPoint logDensity point.1.1 width point.1.2 intervals point.2)
        intervals
        (primitiveRuntimeAugmentedReverse logDensity width intervals point).2.2.1.2
        (primitiveRuntimeAugmentedReverse logDensity width intervals point).2.2.1.1
  rejected_same_side : ∀ rejected ∈ List.ofFn point.2.1.2,
    (rejected < point.1.2) =
      (rejected < runtimeAcceptedPoint logDensity point.1.1 width point.1.2
        intervals point.2)

theorem PrimitiveRuntimeSuccess.finalBracket_reverse
    {logDensity : ℝ → ℝ} {width : ℝ} {intervals maxShrink : ℕ}
    {point : (ℝ × ℝ) × RuntimeRandomTrace}
    (hsuccess : PrimitiveRuntimeSuccess logDensity width intervals maxShrink point) :
    runtimeFinalBracket logDensity point.1.1 width
        (runtimeAcceptedPoint logDensity point.1.1 width point.1.2 intervals point.2)
        intervals
        (primitiveRuntimeAugmentedReverse logDensity width intervals point).2 =
      runtimeFinalBracket logDensity point.1.1 width point.1.2 intervals point.2 := by
  exact (primitiveRuntimeFinalBracket_reverse logDensity point.1.1 width
    point.1.2 intervals point.2 hsuccess.stepped_reverse
      hsuccess.rejected_same_side).symm

theorem PrimitiveRuntimeSuccess.reverse_fraction_mem
    {logDensity : ℝ → ℝ} {width : ℝ} {intervals maxShrink : ℕ}
    {point : (ℝ × ℝ) × RuntimeRandomTrace}
    (hsuccess : PrimitiveRuntimeSuccess logDensity width intervals maxShrink point) :
    (primitiveRuntimeAugmentedReverse logDensity width intervals point).2.2.2 ∈
      Set.Ico (0 : ℝ) 1 :=
  primitiveRuntimeAugmentedReverse_fraction_mem logDensity width intervals point
    hsuccess.old_mem

theorem PrimitiveRuntimeSuccess.reverse_involutive
    {logDensity : ℝ → ℝ} {width : ℝ} {intervals maxShrink : ℕ}
    {point : (ℝ × ℝ) × RuntimeRandomTrace}
    (hsuccess : PrimitiveRuntimeSuccess logDensity width intervals maxShrink point)
    (hwidth : width ≠ 0) :
    primitiveRuntimeAugmentedReverse logDensity width intervals
        (primitiveRuntimeAugmentedReverse logDensity width intervals point) = point := by
  exact primitiveRuntimeAugmentedReverse_involutive_of_finalBracket logDensity
    hwidth intervals point (lt_of_le_of_lt hsuccess.old_mem.1 hsuccess.old_mem.2)
    hsuccess.finalBracket_reverse

theorem PrimitiveRuntimeSuccess.density_invariant
    {logDensity : ℝ → ℝ} {width : ℝ} {intervals maxShrink : ℕ}
    {point : (ℝ × ℝ) × RuntimeRandomTrace}
    (hsuccess : PrimitiveRuntimeSuccess logDensity width intervals maxShrink point)
    (hwidth : width ≠ 0) :
    runtimeTraceDensity logDensity width intervals maxShrink
        (primitiveRuntimeAugmentedReverse logDensity width intervals point).1
        (primitiveRuntimeAugmentedReverse logDensity width intervals point).2 =
      runtimeTraceDensity logDensity width intervals maxShrink point.1 point.2 := by
  exact runtimeTraceDensity_primitiveReverse logDensity intervals maxShrink point
    hwidth hsuccess.length_lt hsuccess.grid_valid hsuccess.fraction_mem
    hsuccess.new_in_slice hsuccess.old_in_slice hsuccess.reverse_fraction_mem
    hsuccess.stepped_reverse hsuccess.rejected_same_side
    (lt_of_le_of_lt hsuccess.old_mem.1 hsuccess.old_mem.2)
    hsuccess.finalBracket_reverse

/-! ### Successful-density support -/

/-- Recursive semantic validity of a rejected-point trace: each point lies in
the then-current bracket, is strictly below the sampled height, and the tail
is valid in the shrunken bracket. -/
def ValidRejectedTrace (logDensity : ℝ → ℝ) (threshold current : ℝ) :
    List ℝ → (ℝ × ℝ) → Prop
  | [], _ => True
  | rejected :: remaining, bracket =>
      rejected ∈ Set.Ico bracket.1 bracket.2 ∧
        logDensity rejected < threshold ∧
        ValidRejectedTrace logDensity threshold current remaining
          (shrinkBracket current rejected bracket)

/-- Nonzero rejected-trace likelihood exposes every recursive rejection
condition used by the operational shrinker. -/
theorem validRejectedTrace_of_rejectedTraceWeight_ne_zero
    (logDensity : ℝ → ℝ) (threshold current : ℝ)
    (rejected : List ℝ) (bracket : ℝ × ℝ)
    (hnonzero : rejectedTraceWeight logDensity threshold current rejected bracket ≠ 0) :
    ValidRejectedTrace logDensity threshold current rejected bracket := by
  induction rejected generalizing bracket with
  | nil => trivial
  | cons point remaining ih =>
      simp only [rejectedTraceWeight] at hnonzero
      by_cases hpoint : point ∈ Set.Ico bracket.1 bracket.2 ∧
          logDensity point < threshold
      · rw [if_pos hpoint] at hnonzero
        have htail : rejectedTraceWeight logDensity threshold current remaining
            (shrinkBracket current point bracket) ≠ 0 := by
          exact right_ne_zero_of_mul hnonzero
        exact ⟨hpoint.1, hpoint.2, ih _ htail⟩
      · rw [if_neg hpoint] at hnonzero
        exact False.elim (hnonzero rfl)

/-- A point surviving all later shrink updates also lay in the bracket before
the first update. -/
theorem ValidRejectedTrace.final_mem_initial
    {logDensity : ℝ → ℝ} {threshold current candidate : ℝ}
    {rejected : List ℝ} {bracket : ℝ × ℝ}
    (hvalid : ValidRejectedTrace logDensity threshold current rejected bracket)
    (hfinal : candidate ∈ Set.Ico
      (shrinkRejectedPoints current rejected bracket).1
      (shrinkRejectedPoints current rejected bracket).2) :
    candidate ∈ Set.Ico bracket.1 bracket.2 := by
  induction rejected generalizing bracket with
  | nil => exact hfinal
  | cons point remaining ih =>
      rcases hvalid with ⟨hpoint, _hbelow, htail⟩
      have hupdated : candidate ∈ Set.Ico
          (shrinkBracket current point bracket).1
          (shrinkBracket current point bracket).2 :=
        ih htail hfinal
      unfold shrinkBracket at hupdated
      by_cases hside : point < current
      · rw [if_pos hside] at hupdated
        exact ⟨hpoint.1.trans hupdated.1, hupdated.2⟩
      · rw [if_neg hside] at hupdated
        exact ⟨hupdated.1, hupdated.2.trans_le hpoint.2.le⟩

/-- A semantically valid rejected trace preserves the current-state bracket
invariant through every recursive update. -/
theorem ValidRejectedTrace.validShrinkBracket_final
    {logDensity : ℝ → ℝ} {threshold current : ℝ}
    {rejected : List ℝ} {bracket : ℝ × ℝ}
    (hvalid : ValidRejectedTrace logDensity threshold current rejected bracket)
    (hbracket : ValidShrinkBracket logDensity threshold current bracket) :
    ValidShrinkBracket logDensity threshold current
      (shrinkRejectedPoints current rejected bracket) := by
  induction rejected generalizing bracket with
  | nil => exact hbracket
  | cons point remaining ih =>
      rcases hvalid with ⟨hpoint, hbelow, htail⟩
      have hupdated : ValidShrinkBracket logDensity threshold current
          (shrinkBracket current point bracket) := by
        unfold shrinkBracket
        by_cases hside : point < current
        · rw [if_pos hside]
          exact ⟨hside.le, hbracket.2.1, hbracket.2.2⟩
        · rw [if_neg hside]
          have hne : point ≠ current := by
            intro heq
            subst point
            exact (not_lt_of_ge hbracket.2.2) hbelow
          exact ⟨hbracket.1, lt_of_le_of_ne (not_lt.mp hside) hne.symm,
            hbracket.2.2⟩
      exact ih htail hupdated

/-- Affine interpretation of a unit fraction lies in every positive
half-open bracket. -/
theorem bracketAffine_mem_Ico
    {left right fraction : ℝ} (hbracket : left < right)
    (hfraction : fraction ∈ Set.Ico (0 : ℝ) 1) :
    left + (right - left) * fraction ∈ Set.Ico left right := by
  have hwidth : 0 < right - left := sub_pos.mpr hbracket
  constructor
  · nlinarith [mul_nonneg hwidth.le hfraction.1]
  · have hremaining : 0 < (right - left) * (1 - fraction) :=
      mul_pos hwidth (sub_pos.mpr hfraction.2)
    nlinarith

/-- Every condition encoded by the primitive successful density can be
recovered from a proof that the density is nonzero. -/
theorem runtimeTraceDensity_support
    (logDensity : ℝ → ℝ) (width : ℝ) (intervals maxShrink : ℕ)
    (state : ℝ × ℝ) (trace : RuntimeRandomTrace)
    (hnonzero : runtimeTraceDensity logDensity width intervals maxShrink
      state trace ≠ 0) :
    trace.1.1 < maxShrink ∧
      0 ≤ trace.2.1.2 ∧ trace.2.1.2 < intervals ∧
      trace.2.2 ∈ Set.Ico (0 : ℝ) 1 ∧
      state.1 ≤ logDensity
        (runtimeAcceptedPoint logDensity state.1 width state.2 intervals trace) ∧
      ValidRejectedTrace logDensity state.1 state.2 (List.ofFn trace.1.2)
        (runtimeSteppedBracket logDensity state.1 width state.2 intervals
          trace.2.1.2 trace.2.1.1) := by
  simp only [runtimeTraceDensity] at hnonzero
  split at hnonzero
  · next hcondition =>
      have hweight : rejectedTraceWeight logDensity state.1 state.2
          (List.ofFn trace.1.2)
          (runtimeSteppedBracket logDensity state.1 width state.2 intervals
            trace.2.1.2 trace.2.1.1) ≠ 0 :=
        right_ne_zero_of_mul hnonzero
      exact ⟨hcondition.1, hcondition.2.1, hcondition.2.2.1,
        hcondition.2.2.2.1, hcondition.2.2.2.2,
        validRejectedTrace_of_rejectedTraceWeight_ne_zero logDensity state.1
          state.2 _ _ hweight⟩
  · simp at hnonzero

/-- Any point lying in the actually stepped-out bracket induces a reverse
integer allocation that remains within the configured finite range. -/
theorem globalValidAllocation_of_mem_runtimeSteppedBracket
    (logDensity : ℝ → ℝ) (threshold : ℝ)
    {width : ℝ} (hwidth : 0 < width) (intervals : ℕ)
    (old new : ℝ) (grid : Alignment × ℤ)
    (hallocation : 0 ≤ grid.2 ∧ grid.2 < intervals)
    (hnew : new ∈ Set.Ico
      (runtimeSteppedBracket logDensity threshold width old intervals
        grid.2 grid.1).1
      (runtimeSteppedBracket logDensity threshold width old intervals
        grid.2 grid.1).2) :
    grid ∈ globalValidAllocation intervals width old new := by
  let leftSteps := grid.2.toNat
  let rightSteps := intervals - 1 - leftSteps
  have hleftCast : (leftSteps : ℤ) = grid.2 :=
    Int.toNat_of_nonneg hallocation.1
  have hleftNat : leftSteps < intervals := by omega
  have hpartition : rightSteps + 1 + leftSteps = intervals := by
    omega
  have hleftBound :
      initialLeft width old (alignmentCoordinate grid.1) -
          (leftSteps : ℝ) * width ≤ new := by
    exact (sub_steps_mul_width_le_expandLeft logDensity threshold hwidth.le
      leftSteps (initialLeft width old (alignmentCoordinate grid.1))).trans
        hnew.1
  have hrightBound : new <
      initialRight width old (alignmentCoordinate grid.1) +
        (rightSteps : ℝ) * width := by
    exact hnew.2.trans_le
      (expandRight_le_add_steps_mul_width logDensity threshold hwidth.le
        rightSteps (initialRight width old (alignmentCoordinate grid.1)))
  let coordinate := alignmentCoordinate grid.1 + (new - old) / width
  have hcoordinateLower : (-(grid.2 : ℝ)) ≤ coordinate := by
    unfold coordinate
    have hdivLower :
        (-(grid.2 : ℝ)) - alignmentCoordinate grid.1 ≤ (new - old) / width := by
      rw [le_div_iff₀ hwidth]
      unfold initialLeft at hleftBound
      have hleftReal : (leftSteps : ℝ) = (grid.2 : ℝ) := by
        exact_mod_cast hleftCast
      rw [hleftReal] at hleftBound
      nlinarith
    linarith
  have hcoordinateUpper : coordinate < (intervals : ℝ) - grid.2 := by
    unfold coordinate
    have hdivUpper : (new - old) / width <
        (intervals : ℝ) - grid.2 - alignmentCoordinate grid.1 := by
      rw [div_lt_iff₀ hwidth]
      unfold initialRight initialLeft at hrightBound
      have hpartitionReal : (rightSteps : ℝ) + 1 + (leftSteps : ℝ) =
          intervals := by exact_mod_cast hpartition
      have hleftReal : (leftSteps : ℝ) = (grid.2 : ℝ) := by
        exact_mod_cast hleftCast
      nlinarith
    linarith
  have hshiftLower : -grid.2 ≤ integerAlignmentShift width old new grid.1 := by
    unfold integerAlignmentShift
    exact (Int.le_floor).2 (by exact_mod_cast hcoordinateLower)
  have hshiftUpper : integerAlignmentShift width old new grid.1 <
      (intervals : ℤ) - grid.2 := by
    unfold integerAlignmentShift
    exact (Int.floor_lt).2 (by exact_mod_cast hcoordinateUpper)
  exact ⟨hallocation.1, hallocation.2,
    by omega, by omega⟩

/-- Membership of the proposed endpoint in the stopped bracket supplies the
interior-grid hypotheses required by allocation rerooting.  The proof uses
the floor cell containing `new`: for a positive displacement the right
expansion crossed every intervening grid point, while for a negative
displacement the left expansion did so. -/
theorem runtimeSteppedBracket_reverse_of_mem
    (logDensity : ℝ → ℝ) (threshold : ℝ) (intervals : ℕ)
    {width old new : ℝ} (hwidth : 0 < width) (grid : Alignment × ℤ)
    (hgrid : grid ∈ globalValidAllocation intervals width old new)
    (hnew : new ∈ Set.Ico
      (runtimeSteppedBracket logDensity threshold width old intervals
        grid.2 grid.1).1
      (runtimeSteppedBracket logDensity threshold width old intervals
        grid.2 grid.1).2) :
    runtimeSteppedBracket logDensity threshold width old intervals grid.2 grid.1 =
      runtimeSteppedBracket logDensity threshold width new intervals
        (alignmentAllocationReverse width old new grid).2
        (alignmentAllocationReverse width old new grid).1 := by
  let offset := alignmentCoordinate grid.1
  let shift := integerAlignmentShift width old new grid.1
  have hshift : shift = ⌊offset + (new - old) / width⌋ := rfl
  have hshiftLower : (shift : ℝ) ≤ offset + (new - old) / width := by
    rw [hshift]
    exact_mod_cast Int.floor_le (offset + (new - old) / width)
  have hshiftUpper : offset + (new - old) / width < (shift : ℝ) + 1 := by
    rw [hshift]
    exact_mod_cast Int.lt_floor_add_one (offset + (new - old) / width)
  have hquotient : (new - old) / width * width = new - old := by
    exact div_mul_cancel₀ (new - old) hwidth.ne'
  have hnewExpanded :
      expandLeft logDensity threshold width grid.2.toNat
          (initialLeft width old offset) ≤ new ∧
        new < expandRight logDensity threshold width
          (intervals - 1 - grid.2.toNat) (initialRight width old offset) := by
    simpa [runtimeSteppedBracket, offset] using hnew
  apply runtimeSteppedBracket_reverse logDensity threshold intervals hwidth.ne'
    grid hgrid
  · intro hnonneg index hindex
    have hshiftCast : (shift.toNat : ℝ) = (shift : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hnonneg
    have hbudget : shift.toNat ≤ intervals - 1 - grid.2.toNat := by
      simp only [globalValidAllocation, Set.mem_setOf_eq] at hgrid
      omega
    have hpositive : 0 < shift.toNat := Nat.pos_of_ne_zero (by
      intro hz
      omega)
    let reflected := shift.toNat - 1 - index
    have hreflected : reflected < shift.toNat := by
      dsimp [reflected]
      omega
    have htarget : initialRight width old offset +
          ((shift.toNat - 1 : ℕ) : ℝ) * width ≤ new := by
      unfold initialRight initialLeft
      have hpred : shift.toNat - 1 + 1 = shift.toNat := by omega
      have hpredCast : ((shift.toNat - 1 : ℕ) : ℝ) + 1 = shift.toNat := by
        exact_mod_cast hpred
      rw [← hshiftCast] at hshiftLower
      have hscaled := mul_le_mul_of_nonneg_right hshiftLower hwidth.le
      nlinarith
    have hcrossed := expandRight_crossed_inside_of_lt logDensity threshold
      hwidth (steps := intervals - 1 - grid.2.toNat)
      (consumed := shift.toNat - 1) (initialRight width old offset)
      (initialRight width old offset +
        ((shift.toNat - 1 : ℕ) : ℝ) * width)
      (by omega) le_rfl (htarget.trans_lt hnewExpanded.2)
    have hinterior := hcrossed reflected (by omega)
    rw [initialLeft_reverseOffset hwidth.ne']
    rw [alignmentShift_eq_floor hwidth.ne', ← hshift, ← hshiftCast]
    dsimp [reflected] at hinterior
    have harg :
        initialLeft width old (alignmentCoordinate grid.1) +
            width * (shift.toNat : ℝ) - (index : ℝ) * width =
          initialRight width old offset + (reflected : ℝ) * width := by
      unfold initialRight
      dsimp [offset]
      have hnat : reflected + index + 1 = shift.toNat := by
        dsimp [reflected]
        omega
      have hcast : (reflected : ℝ) + index + 1 = shift.toNat := by
        exact_mod_cast hnat
      nlinarith
    rw [harg]
    exact hinterior
  · intro hnonpos index hindex
    have hnegNonneg : 0 ≤ -shift := neg_nonneg.mpr hnonpos
    have hnegCast : ((-shift).toNat : ℝ) = -(shift : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hnegNonneg
    have hbudget : (-shift).toNat ≤ grid.2.toNat := by
      simp only [globalValidAllocation, Set.mem_setOf_eq] at hgrid
      omega
    have hpositive : 0 < (-shift).toNat := Nat.pos_of_ne_zero (by
      intro hz
      omega)
    have htarget : new < initialLeft width old offset -
          (((-shift).toNat - 1 : ℕ) : ℝ) * width := by
      unfold initialLeft
      have hpred : (-shift).toNat - 1 + 1 = (-shift).toNat := by omega
      have hpredCast : (((-shift).toNat - 1 : ℕ) : ℝ) + 1 =
          (-shift).toNat := by exact_mod_cast hpred
      have hshiftCastNeg : (shift : ℝ) = -((-shift).toNat : ℝ) := by
        linarith [hnegCast]
      rw [hshiftCastNeg] at hshiftUpper
      have hscaled := mul_lt_mul_of_pos_right hshiftUpper hwidth
      nlinarith
    exact expandLeft_crossed_inside_of_lt logDensity threshold hwidth
      (steps := grid.2.toNat) (consumed := (-shift).toNat - 1)
      (initialLeft width old offset)
      (initialLeft width old offset -
        (((-shift).toNat - 1 : ℕ) : ℝ) * width)
      (by omega) (hnewExpanded.1.trans_lt htarget) le_rfl index (by omega)
  · intro hnonneg index hindex
    have hshiftCast : (shift.toNat : ℝ) = (shift : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hnonneg
    have hbudget : shift.toNat ≤ intervals - 1 - grid.2.toNat := by
      simp only [globalValidAllocation, Set.mem_setOf_eq] at hgrid
      omega
    have hpositive : 0 < shift.toNat := Nat.pos_of_ne_zero (by
      intro hz
      omega)
    have htarget : initialRight width old offset +
          ((shift.toNat - 1 : ℕ) : ℝ) * width ≤ new := by
      unfold initialRight initialLeft
      have hpred : shift.toNat - 1 + 1 = shift.toNat := by omega
      have hpredCast : ((shift.toNat - 1 : ℕ) : ℝ) + 1 = shift.toNat := by
        exact_mod_cast hpred
      rw [← hshiftCast] at hshiftLower
      have hscaled := mul_le_mul_of_nonneg_right hshiftLower hwidth.le
      nlinarith
    exact expandRight_crossed_inside_of_lt logDensity threshold hwidth
      (steps := intervals - 1 - grid.2.toNat)
      (consumed := shift.toNat - 1) (initialRight width old offset)
      (initialRight width old offset +
        ((shift.toNat - 1 : ℕ) : ℝ) * width)
      (by omega) le_rfl (htarget.trans_lt hnewExpanded.2) index (by omega)
  · intro hnonpos index hindex
    have hnegNonneg : 0 ≤ -shift := neg_nonneg.mpr hnonpos
    have hnegCast : ((-shift).toNat : ℝ) = -(shift : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hnegNonneg
    have hbudget : (-shift).toNat ≤ grid.2.toNat := by
      simp only [globalValidAllocation, Set.mem_setOf_eq] at hgrid
      omega
    have hpositive : 0 < (-shift).toNat := Nat.pos_of_ne_zero (by
      intro hz
      omega)
    let reflected := (-shift).toNat - 1 - index
    have hreflected : reflected < (-shift).toNat := by
      dsimp [reflected]
      omega
    have htarget : new < initialLeft width old offset -
          (((-shift).toNat - 1 : ℕ) : ℝ) * width := by
      unfold initialLeft
      have hpred : (-shift).toNat - 1 + 1 = (-shift).toNat := by omega
      have hpredCast : (((-shift).toNat - 1 : ℕ) : ℝ) + 1 =
          (-shift).toNat := by exact_mod_cast hpred
      have hshiftCastNeg : (shift : ℝ) = -((-shift).toNat : ℝ) := by
        linarith [hnegCast]
      rw [hshiftCastNeg] at hshiftUpper
      have hscaled := mul_lt_mul_of_pos_right hshiftUpper hwidth
      nlinarith
    have hcrossed := expandLeft_crossed_inside_of_lt logDensity threshold hwidth
      (steps := grid.2.toNat) (consumed := (-shift).toNat - 1)
      (initialLeft width old offset)
      (initialLeft width old offset -
        (((-shift).toNat - 1 : ℕ) : ℝ) * width)
      (by omega) (hnewExpanded.1.trans_lt htarget) le_rfl
    have hinterior := hcrossed reflected (by omega)
    rw [initialRight_reverseOffset hwidth.ne']
    rw [alignmentShift_eq_floor hwidth.ne', ← hshift]
    dsimp [reflected] at hinterior
    have harg :
        initialRight width old (alignmentCoordinate grid.1) +
            width * (shift : ℝ) + (index : ℝ) * width =
          initialLeft width old offset - (reflected : ℝ) * width := by
      unfold initialRight
      dsimp [offset]
      have hnat : reflected + index + 1 = (-shift).toNat := by
        dsimp [reflected]
        omega
      have hcast : (reflected : ℝ) + index + 1 = (-shift).toNat := by
        exact_mod_cast hnat
      nlinarith
    rw [harg]
    exact hinterior

/-- If the eventual accepted point survives a valid rejected trace and lies
above the sampled height, no rejected point can separate it from the old
accepted state. -/
theorem ValidRejectedTrace.sameSide_of_final_mem
    {logDensity : ℝ → ℝ} {threshold old new : ℝ}
    {rejected : List ℝ} {bracket : ℝ × ℝ}
    (hvalid : ValidRejectedTrace logDensity threshold old rejected bracket)
    (hnewSlice : threshold ≤ logDensity new)
    (hnewFinal : new ∈ Set.Ico
      (shrinkRejectedPoints old rejected bracket).1
      (shrinkRejectedPoints old rejected bracket).2) :
    ∀ point ∈ rejected, (point < old) = (point < new) := by
  induction rejected generalizing bracket with
  | nil => simp
  | cons point remaining ih =>
      rcases hvalid with ⟨hpoint, hbelow, htail⟩
      have hnewUpdated : new ∈ Set.Ico
          (shrinkBracket old point bracket).1
          (shrinkBracket old point bracket).2 :=
        htail.final_mem_initial hnewFinal
      have hhead : (point < old) = (point < new) := by
        unfold shrinkBracket at hnewUpdated
        by_cases hside : point < old
        · rw [if_pos hside] at hnewUpdated
          have hnew : point < new := lt_of_le_of_ne hnewUpdated.1 (by
            intro heq
            subst new
            exact (not_lt_of_ge hnewSlice) hbelow)
          simp [hside, hnew]
        · rw [if_neg hside] at hnewUpdated
          have hnew : ¬ point < new := not_lt_of_ge hnewUpdated.2.le
          simp [hside, hnew]
      intro candidate hcandidate
      simp only [List.mem_cons] at hcandidate
      rcases hcandidate with rfl | hremaining
      · exact hhead
      · exact ih htail hnewFinal candidate hremaining

/-- Every field of the primitive success certificate follows automatically
from nonzero successful density and validity of the current slice state. -/
theorem primitiveRuntimeSuccess_of_density_ne_zero
    (logDensity : ℝ → ℝ) {width : ℝ} (hwidth : 0 < width)
    (intervals maxShrink : ℕ) (point : (ℝ × ℝ) × RuntimeRandomTrace)
    (hold : point.1.1 ≤ logDensity point.1.2)
    (hnonzero : runtimeTraceDensity logDensity width intervals maxShrink
      point.1 point.2 ≠ 0) :
    PrimitiveRuntimeSuccess logDensity width intervals maxShrink point := by
  rcases runtimeTraceDensity_support logDensity width intervals maxShrink
      point.1 point.2 hnonzero with
    ⟨hlength, hallocationNonneg, hallocationLt, hfraction, hnewSlice, htrace⟩
  let stepped := runtimeSteppedBracket logDensity point.1.1 width point.1.2
    intervals point.2.2.1.2 point.2.2.1.1
  let final := shrinkRejectedPoints point.1.2 (List.ofFn point.2.1.2) stepped
  let new := runtimeAcceptedPoint logDensity point.1.1 width point.1.2 intervals
    point.2
  have hsteppedValid : ValidShrinkBracket logDensity point.1.1 point.1.2
      stepped := by
    exact validShrinkBracket_runtimeSteppedBracket logDensity point.1.1
      point.1.2 hwidth intervals point.2.2.1.2 point.2.2.1.1 hold
  have hfinalValid : ValidShrinkBracket logDensity point.1.1 point.1.2 final :=
    htrace.validShrinkBracket_final hsteppedValid
  have hfinalLt : final.1 < final.2 := hfinalValid.lt
  have hnewFinal : new ∈ Set.Ico final.1 final.2 := by
    apply bracketAffine_mem_Ico hfinalLt hfraction
  have hnewStepped : new ∈ Set.Ico stepped.1 stepped.2 :=
    htrace.final_mem_initial hnewFinal
  have hgrid : point.2.2.1 ∈ globalValidAllocation intervals width point.1.2
      new := by
    exact globalValidAllocation_of_mem_runtimeSteppedBracket logDensity
      point.1.1 hwidth intervals point.1.2 new point.2.2.1
      ⟨hallocationNonneg, hallocationLt⟩ hnewStepped
  have hstepped := runtimeSteppedBracket_reverse_of_mem logDensity point.1.1
    intervals hwidth point.2.2.1 hgrid hnewStepped
  refine ⟨hlength, ?_, hfraction, ?_, hold, hnewSlice, hstepped, ?_⟩
  · simpa [new] using hgrid
  · simpa [runtimeFinalBracket, stepped, final] using
      (show point.1.2 ∈ Set.Ico final.1 final.2 from
        ⟨hfinalValid.1, hfinalValid.2.1⟩)
  · simpa [new] using htrace.sameSide_of_final_mem hnewSlice hnewFinal

/-- Runtime likelihood symmetry now requires no separately supplied replay
certificate: every nonzero forward-density point carries its own proof. -/
theorem runtimeTraceDensity_primitiveReverse_of_ne_zero
    (logDensity : ℝ → ℝ) {width : ℝ} (hwidth : 0 < width)
    (intervals maxShrink : ℕ) (point : (ℝ × ℝ) × RuntimeRandomTrace)
    (hold : point.1.1 ≤ logDensity point.1.2)
    (hnonzero : runtimeTraceDensity logDensity width intervals maxShrink
      point.1 point.2 ≠ 0) :
    runtimeTraceDensity logDensity width intervals maxShrink
        (primitiveRuntimeAugmentedReverse logDensity width intervals point).1
        (primitiveRuntimeAugmentedReverse logDensity width intervals point).2 =
      runtimeTraceDensity logDensity width intervals maxShrink point.1 point.2 := by
  exact (primitiveRuntimeSuccess_of_density_ne_zero logDensity hwidth intervals
    maxShrink point hold hnonzero).density_invariant hwidth.ne'

/-- The same intrinsic support proof makes the primitive rerooting an
involution at every nonzero-density point in the valid slice domain. -/
theorem primitiveRuntimeAugmentedReverse_involutive_of_density_ne_zero
    (logDensity : ℝ → ℝ) {width : ℝ} (hwidth : 0 < width)
    (intervals maxShrink : ℕ) (point : (ℝ × ℝ) × RuntimeRandomTrace)
    (hold : point.1.1 ≤ logDensity point.1.2)
    (hnonzero : runtimeTraceDensity logDensity width intervals maxShrink
      point.1 point.2 ≠ 0) :
    primitiveRuntimeAugmentedReverse logDensity width intervals
        (primitiveRuntimeAugmentedReverse logDensity width intervals point) =
      point := by
  exact (primitiveRuntimeSuccess_of_density_ne_zero logDensity hwidth intervals
    maxShrink point hold hnonzero).reverse_involutive hwidth.ne'

/-! ### Fixed-length successful reversal strata -/

/-- Primitive rerooting restricted to one rejected-sequence dimension. The
rejected vector is definitionally retained, so the result stays in the same
finite-dimensional carrier. -/
noncomputable def fixedPrimitiveRuntimeAugmentedReverse
    (logDensity : ℝ → ℝ) (width : ℝ) (intervals length : ℕ)
    (point : (ℝ × ℝ) × FixedRuntimeTrace length) :
    (ℝ × ℝ) × FixedRuntimeTrace length :=
  let reversed := primitiveRuntimeAugmentedReverse logDensity width intervals
    (point.1, (Sigma.mk length point.2.1, point.2.2))
  (reversed.1, (point.2.1, reversed.2.2))

/-- Successful support on a fixed rejected length, including validity of the
current height/state pair. -/
def fixedRuntimeSuccessSet
    (logDensity : ℝ → ℝ) (width : ℝ) (intervals maxShrink length : ℕ) :
    Set ((ℝ × ℝ) × FixedRuntimeTrace length) :=
  {point | point.1.1 ≤ logDensity point.1.2 ∧
    runtimeTraceDensity logDensity width intervals maxShrink point.1
      (Sigma.mk length point.2.1, point.2.2) ≠ 0}

/-- The bracket derived by a fixed-dimensional runtime trace is jointly
measurable in the augmented state and every trace coordinate. -/
theorem measurable_runtimeFinalBracket_fixedLength
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (width : ℝ) (intervals length : ℕ) :
    Measurable (fun point : (ℝ × ℝ) × FixedRuntimeTrace length =>
      runtimeFinalBracket logDensity point.1.1 width point.1.2 intervals
        (Sigma.mk length point.2.1, point.2.2)) := by
  let DenseDomain := ((ℝ × ℝ) × (Fin length → ℝ)) × (Alignment × ℝ)
  have hallocation : Measurable (fun point : DenseDomain × ℤ =>
      shrinkRejectedVector point.1.1.1.2 length point.1.1.2
        (runtimeSteppedBracket logDensity point.1.1.1.1 width point.1.1.1.2
          intervals point.2 point.1.2.1)) := by
    apply measurable_from_prod_countable_left
    intro allocation
    have hstate : Measurable (fun point : DenseDomain => point.1.1) :=
      measurable_fst.comp measurable_fst
    have hvalues : Measurable (fun point : DenseDomain => point.1.2) :=
      measurable_snd.comp measurable_fst
    have halignment : Measurable (fun point : DenseDomain => point.2.1) :=
      measurable_fst.comp measurable_snd
    have hstepped : Measurable (fun point : DenseDomain =>
        runtimeSteppedBracket logDensity point.1.1.1 width point.1.1.2
          intervals allocation point.2.1) :=
      (measurable_runtimeSteppedBracket_fixedAllocation hlogDensity width
        intervals allocation).comp (hstate.prodMk halignment)
    exact (measurable_shrinkRejectedVector length).comp
      (((measurable_snd.comp hstate).prodMk hvalues).prodMk hstepped)
  have hpack : Measurable (fun point : (ℝ × ℝ) × FixedRuntimeTrace length =>
      ((((point.1, point.2.1), (point.2.2.1.1, point.2.2.2)),
        point.2.2.1.2) : DenseDomain × ℤ)) := by
    fun_prop
  convert hallocation.comp hpack using 1
  funext point
  simp only [runtimeFinalBracket, Function.comp_apply]
  exact (shrinkRejectedVector_eq_shrinkRejectedPoints point.1.2 length
    point.2.1
    (runtimeSteppedBracket logDensity point.1.1 width point.1.2 intervals
      point.2.2.1.2 point.2.2.1.1)).symm

theorem measurable_runtimeAcceptedPoint_fixedLength
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (width : ℝ) (intervals length : ℕ) :
    Measurable (fun point : (ℝ × ℝ) × FixedRuntimeTrace length =>
      runtimeAcceptedPoint logDensity point.1.1 width point.1.2 intervals
        (Sigma.mk length point.2.1, point.2.2)) := by
  have hbracket := measurable_runtimeFinalBracket_fixedLength hlogDensity width
    intervals length
  have hfraction : Measurable
      (fun point : (ℝ × ℝ) × FixedRuntimeTrace length => point.2.2.2) := by
    fun_prop
  exact (measurable_fst.comp hbracket).add
    (((measurable_snd.comp hbracket).sub
      (measurable_fst.comp hbracket)).mul
        hfraction)

theorem measurable_runtimeSteppedBracket_fixedLength
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (width : ℝ) (intervals length : ℕ) :
    Measurable (fun point : (ℝ × ℝ) × FixedRuntimeTrace length =>
      runtimeSteppedBracket logDensity point.1.1 width point.1.2 intervals
        point.2.2.1.2 point.2.2.1.1) := by
  have hallocation : Measurable (fun point :
      (((ℝ × ℝ) × Alignment) × ℝ) × ℤ =>
      runtimeSteppedBracket logDensity point.1.1.1.1 width point.1.1.1.2
        intervals point.2 point.1.1.2) := by
    apply measurable_from_prod_countable_left
    intro allocation
    exact (measurable_runtimeSteppedBracket_fixedAllocation hlogDensity width
      intervals allocation).comp (by fun_prop)
  have hpack : Measurable (fun point :
      (ℝ × ℝ) × FixedRuntimeTrace length =>
      ((((point.1, point.2.2.1.1), point.2.2.2), point.2.2.1.2) :
        (((ℝ × ℝ) × Alignment) × ℝ) × ℤ)) := by
    fun_prop
  exact hallocation.comp hpack

theorem measurable_fixedPrimitiveRuntimeAugmentedReverse
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (width : ℝ) (intervals length : ℕ) :
    Measurable
      (fixedPrimitiveRuntimeAugmentedReverse logDensity width intervals length) := by
  have hbracket := measurable_runtimeFinalBracket_fixedLength hlogDensity width
    intervals length
  have haccepted := measurable_runtimeAcceptedPoint_fixedLength hlogDensity width
    intervals length
  have hold : Measurable (fun point : (ℝ × ℝ) × FixedRuntimeTrace length =>
      point.1.2) := measurable_snd.comp measurable_fst
  have hgridInput : Measurable (fun point :
      (ℝ × ℝ) × FixedRuntimeTrace length =>
      ((point.1.2,
          runtimeAcceptedPoint logDensity point.1.1 width point.1.2 intervals
            (Sigma.mk length point.2.1, point.2.2)), point.2.2.1)) :=
    (hold.prodMk haccepted).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hgrid : Measurable (fun point :
      (ℝ × ℝ) × FixedRuntimeTrace length =>
      alignmentAllocationReverse width point.1.2
        (runtimeAcceptedPoint logDensity point.1.1 width point.1.2 intervals
          (Sigma.mk length point.2.1, point.2.2)) point.2.2.1) :=
    (measurable_alignmentAllocationReverse_parameterized width).comp hgridInput
  have hfraction : Measurable (fun point :
      (ℝ × ℝ) × FixedRuntimeTrace length =>
      (point.1.2 -
        (runtimeFinalBracket logDensity point.1.1 width point.1.2 intervals
          (Sigma.mk length point.2.1, point.2.2)).1) /
        ((runtimeFinalBracket logDensity point.1.1 width point.1.2 intervals
          (Sigma.mk length point.2.1, point.2.2)).2 -
        (runtimeFinalBracket logDensity point.1.1 width point.1.2 intervals
          (Sigma.mk length point.2.1, point.2.2)).1)) :=
    (hold.sub (measurable_fst.comp hbracket)).div
      ((measurable_snd.comp hbracket).sub (measurable_fst.comp hbracket))
  exact ((measurable_fst.comp measurable_fst).prodMk haccepted).prodMk
    ((measurable_fst.comp measurable_snd).prodMk (hgrid.prodMk hfraction))

theorem measurableSet_fixedRuntimeSuccessSet
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (width : ℝ) (intervals maxShrink length : ℕ) :
    MeasurableSet
      (fixedRuntimeSuccessSet logDensity width intervals maxShrink length) := by
  have hdensity := measurable_uncurry_runtimeTraceDensity_fixedLength
    hlogDensity width intervals maxShrink length
  exact (measurableSet_le (measurable_fst.comp measurable_fst)
      (hlogDensity.comp (measurable_snd.comp measurable_fst))).inter
    (measurableSet_singleton (0 : ENNReal) |>.preimage hdensity).compl

/-- Countable combinatorial data that makes one fixed-length practical replay
affine: allocation and rerooting shift, the two consumed expansion counts,
and every shrink-side decision. -/
structure FixedRuntimeReplaySignature (length : ℕ) where
  allocation : ℤ
  shift : ℤ
  leftConsumed : ℕ
  rightConsumed : ℕ
  rejectedLeft : Fin length → Bool

instance (length : ℕ) : Countable (FixedRuntimeReplaySignature length) := by
  let encode : FixedRuntimeReplaySignature length →
      ℤ × ℤ × ℕ × ℕ × (Fin length → Bool) := fun signature =>
    (signature.allocation, signature.shift, signature.leftConsumed,
      signature.rightConsumed, signature.rejectedLeft)
  exact (show Function.Injective encode by
    intro first second heq
    cases first
    cases second
    simp only [encode, Prod.mk.injEq] at heq
    simp_all).countable

/-- Combinatorial signature expected after rerooting. Expansion counts are
translated by the integer grid displacement; `toNat` is justified on actual
successful pieces by stopped-bracket membership. -/
def reverseFixedRuntimeReplaySignature {length : ℕ}
    (signature : FixedRuntimeReplaySignature length) :
    FixedRuntimeReplaySignature length :=
  { allocation := signature.allocation + signature.shift
    shift := -signature.shift
    leftConsumed := ((signature.leftConsumed : ℤ) + signature.shift).toNat
    rightConsumed := ((signature.rightConsumed : ℤ) - signature.shift).toNat
    rejectedLeft := signature.rejectedLeft }

/-- Measurable replay stratum selected by a complete combinatorial signature. -/
def fixedRuntimeReplayPiece
    (logDensity : ℝ → ℝ) (width : ℝ) (intervals maxShrink length : ℕ)
    (signature : FixedRuntimeReplaySignature length) :
    Set ((ℝ × ℝ) × FixedRuntimeTrace length) :=
  {point |
    point ∈ fixedRuntimeSuccessSet logDensity width intervals maxShrink length ∧
    point.2.2.1.2 = signature.allocation ∧
    integerAlignmentShift width point.1.2
      (runtimeAcceptedPoint logDensity point.1.1 width point.1.2 intervals
        (Sigma.mk length point.2.1, point.2.2)) point.2.2.1.1 = signature.shift ∧
    (runtimeSteppedBracket logDensity point.1.1 width point.1.2 intervals
      point.2.2.1.2 point.2.2.1.1).1 =
        initialLeft width point.1.2 (alignmentCoordinate point.2.2.1.1) -
          (signature.leftConsumed : ℝ) * width ∧
    (runtimeSteppedBracket logDensity point.1.1 width point.1.2 intervals
      point.2.2.1.2 point.2.2.1.1).2 =
        initialRight width point.1.2 (alignmentCoordinate point.2.2.1.1) +
          (signature.rightConsumed : ℝ) * width ∧
    ∀ index, (point.2.1 index < point.1.2) = signature.rejectedLeft index}

theorem measurableSet_fixedRuntimeReplayPiece
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (width : ℝ) (intervals maxShrink length : ℕ)
    (signature : FixedRuntimeReplaySignature length) :
    MeasurableSet (fixedRuntimeReplayPiece logDensity width intervals maxShrink
      length signature) := by
  have haccepted := measurable_runtimeAcceptedPoint_fixedLength hlogDensity width
    intervals length
  have hstepped := measurable_runtimeSteppedBracket_fixedLength hlogDensity width
    intervals length
  have hold : Measurable (fun point : (ℝ × ℝ) × FixedRuntimeTrace length =>
      point.1.2) := by fun_prop
  have hoffset : Measurable (fun point :
      (ℝ × ℝ) × FixedRuntimeTrace length => point.2.2.1.1) := by fun_prop
  have hshift : Measurable (fun point :
      (ℝ × ℝ) × FixedRuntimeTrace length =>
      integerAlignmentShift width point.1.2
        (runtimeAcceptedPoint logDensity point.1.1 width point.1.2 intervals
          (Sigma.mk length point.2.1, point.2.2)) point.2.2.1.1) := by
    unfold integerAlignmentShift
    exact Int.measurable_floor.comp
      ((measurable_alignmentCoordinate.comp hoffset).add
        ((haccepted.sub hold).div measurable_const))
  have hinitialLeft : Measurable (fun point :
      (ℝ × ℝ) × FixedRuntimeTrace length =>
      initialLeft width point.1.2 (alignmentCoordinate point.2.2.1.1)) := by
    unfold initialLeft
    exact hold.sub (measurable_const.mul
      (measurable_alignmentCoordinate.comp hoffset))
  have hinitialRight : Measurable (fun point :
      (ℝ × ℝ) × FixedRuntimeTrace length =>
      initialRight width point.1.2 (alignmentCoordinate point.2.2.1.1)) := by
    unfold initialRight
    exact hinitialLeft.add measurable_const
  have hleftTarget : Measurable (fun point :
      (ℝ × ℝ) × FixedRuntimeTrace length =>
      initialLeft width point.1.2 (alignmentCoordinate point.2.2.1.1) -
        (signature.leftConsumed : ℝ) * width) :=
    hinitialLeft.sub measurable_const
  have hrightTarget : Measurable (fun point :
      (ℝ × ℝ) × FixedRuntimeTrace length =>
      initialRight width point.1.2 (alignmentCoordinate point.2.2.1.1) +
        (signature.rightConsumed : ℝ) * width) :=
    hinitialRight.add measurable_const
  have hvalues : Measurable (fun point :
      (ℝ × ℝ) × FixedRuntimeTrace length => point.2.1) := by fun_prop
  have hallocation : Measurable (fun point :
      (ℝ × ℝ) × FixedRuntimeTrace length => point.2.2.1.2) := by fun_prop
  have hrejected : MeasurableSet {point :
      (ℝ × ℝ) × FixedRuntimeTrace length |
      ∀ index, (point.2.1 index < point.1.2) = signature.rejectedLeft index} := by
    rw [show {point : (ℝ × ℝ) × FixedRuntimeTrace length |
        ∀ index, (point.2.1 index < point.1.2) = signature.rejectedLeft index} =
        ⋂ index, {point | (point.2.1 index < point.1.2) =
          signature.rejectedLeft index} by
      ext point
      simp]
    apply MeasurableSet.iInter
    intro index
    cases hvalue : signature.rejectedLeft index with
    | false =>
        simpa [Function.comp_apply] using measurableSet_le hold
          ((measurable_pi_apply index).comp hvalues)
    | true =>
        simpa [Function.comp_apply] using measurableSet_lt
          ((measurable_pi_apply index).comp hvalues) hold
  unfold fixedRuntimeReplayPiece
  exact ((measurableSet_fixedRuntimeSuccessSet hlogDensity width intervals
      maxShrink length).mem.and
    ((hallocation.eq measurable_const).and
      ((hshift.eq measurable_const).and
        (((measurable_fst.comp hstepped).eq hleftTarget).and
          (((measurable_snd.comp hstepped).eq hrightTarget).and
            hrejected.mem))))).setOf

theorem iUnion_fixedRuntimeReplayPiece
    (logDensity : ℝ → ℝ) (width : ℝ) (intervals maxShrink length : ℕ) :
    (⋃ signature : FixedRuntimeReplaySignature length,
      fixedRuntimeReplayPiece logDensity width intervals maxShrink length
        signature) =
      fixedRuntimeSuccessSet logDensity width intervals maxShrink length := by
  ext point
  constructor
  · intro hpoint
    rcases Set.mem_iUnion.mp hpoint with ⟨signature, hsignature⟩
    exact hsignature.1
  · intro hpoint
    obtain ⟨leftConsumed, _hleftBudget, hleft⟩ :=
      exists_expandLeft_eq_sub_nat_mul logDensity point.1.1 width
        (initialLeft width point.1.2 (alignmentCoordinate point.2.2.1.1))
        point.2.2.1.2.toNat
    obtain ⟨rightConsumed, _hrightBudget, hright⟩ :=
      exists_expandRight_eq_add_nat_mul logDensity point.1.1 width
        (initialRight width point.1.2 (alignmentCoordinate point.2.2.1.1))
        (intervals - 1 - point.2.2.1.2.toNat)
    let signature : FixedRuntimeReplaySignature length :=
      { allocation := point.2.2.1.2
        shift := integerAlignmentShift width point.1.2
          (runtimeAcceptedPoint logDensity point.1.1 width point.1.2 intervals
            (Sigma.mk length point.2.1, point.2.2)) point.2.2.1.1
        leftConsumed := leftConsumed
        rightConsumed := rightConsumed
        rejectedLeft := fun index => decide (point.2.1 index < point.1.2) }
    apply Set.mem_iUnion.mpr
    refine ⟨signature, hpoint, rfl, rfl, ?_, ?_, ?_⟩
    · exact hleft
    · exact hright
    · intro index
      simp [signature]

theorem pairwise_disjoint_fixedRuntimeReplayPiece
    (logDensity : ℝ → ℝ) {width : ℝ} (hwidth : width ≠ 0)
    (intervals maxShrink length : ℕ) :
    Pairwise (Disjoint on fun signature : FixedRuntimeReplaySignature length =>
      fixedRuntimeReplayPiece logDensity width intervals maxShrink length
        signature) := by
  intro first second hne
  change Disjoint
    (fixedRuntimeReplayPiece logDensity width intervals maxShrink length first)
    (fixedRuntimeReplayPiece logDensity width intervals maxShrink length second)
  rw [Set.disjoint_left]
  intro point hfirst hsecond
  apply hne
  have hallocation : first.allocation = second.allocation :=
    hfirst.2.1.symm.trans hsecond.2.1
  have hshift : first.shift = second.shift :=
    hfirst.2.2.1.symm.trans hsecond.2.2.1
  have hleft : first.leftConsumed = second.leftConsumed := by
    apply nat_mul_width_injective hwidth
    have hfirstEq := hfirst.2.2.2.1
    have hsecondEq := hsecond.2.2.2.1
    nlinarith
  have hright : first.rightConsumed = second.rightConsumed := by
    apply nat_mul_width_injective hwidth
    have hfirstEq := hfirst.2.2.2.2.1
    have hsecondEq := hsecond.2.2.2.2.1
    nlinarith
  have hsides : first.rejectedLeft = second.rejectedLeft := by
    funext index
    have hfirstSide := hfirst.2.2.2.2.2 index
    have hsecondSide := hsecond.2.2.2.2.2 index
    cases hfirstBool : first.rejectedLeft index <;>
      cases hsecondBool : second.rejectedLeft index <;> simp_all
  cases first
  cases second
  simp_all

/-- The fixed-length rerooting is exactly the primitive rerooting after
embedding the rejected vector into the variable-length carrier. -/
theorem fixedPrimitiveRuntimeAugmentedReverse_embed
    (logDensity : ℝ → ℝ) (width : ℝ) (intervals length : ℕ)
    (point : (ℝ × ℝ) × FixedRuntimeTrace length) :
    let reversed := fixedPrimitiveRuntimeAugmentedReverse logDensity width
      intervals length point
    primitiveRuntimeAugmentedReverse logDensity width intervals
        (point.1, (Sigma.mk length point.2.1, point.2.2)) =
      (reversed.1, (Sigma.mk length reversed.2.1, reversed.2.2)) := by
  let embedded : (ℝ × ℝ) × RuntimeRandomTrace :=
    (point.1, (Sigma.mk length point.2.1, point.2.2))
  let reversed := primitiveRuntimeAugmentedReverse logDensity width intervals embedded
  change reversed = (reversed.1, (Sigma.mk length point.2.1, reversed.2.2))
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact primitiveRuntimeAugmentedReverse_rejected logDensity width intervals embedded
    · rfl

/-- Pointwise likelihood symmetry on a fixed successful stratum. -/
theorem fixedRuntimeTraceDensity_reverse
    (logDensity : ℝ → ℝ) {width : ℝ} (hwidth : 0 < width)
    (intervals maxShrink length : ℕ)
    (point : (ℝ × ℝ) × FixedRuntimeTrace length)
    (hpoint : point ∈ fixedRuntimeSuccessSet logDensity width intervals
      maxShrink length) :
    runtimeTraceDensity logDensity width intervals maxShrink
        (fixedPrimitiveRuntimeAugmentedReverse logDensity width intervals length
          point).1
        (Sigma.mk length
          (fixedPrimitiveRuntimeAugmentedReverse logDensity width intervals length
            point).2.1,
          (fixedPrimitiveRuntimeAugmentedReverse logDensity width intervals length
            point).2.2) =
      runtimeTraceDensity logDensity width intervals maxShrink point.1
        (Sigma.mk length point.2.1, point.2.2) := by
  have hinvariant := runtimeTraceDensity_primitiveReverse_of_ne_zero logDensity
    hwidth intervals maxShrink
    (point.1, (Sigma.mk length point.2.1, point.2.2)) hpoint.1 hpoint.2
  rw [fixedPrimitiveRuntimeAugmentedReverse_embed logDensity width intervals
    length point] at hinvariant
  exact hinvariant

/-- Successful support is carried to successful support by the fixed-length
rerooting; this includes validity of the newly accepted slice state. -/
theorem fixedRuntimeSuccessSet_reverse_mem
    (logDensity : ℝ → ℝ) {width : ℝ} (hwidth : 0 < width)
    (intervals maxShrink length : ℕ)
    (point : (ℝ × ℝ) × FixedRuntimeTrace length)
    (hpoint : point ∈ fixedRuntimeSuccessSet logDensity width intervals
      maxShrink length) :
    fixedPrimitiveRuntimeAugmentedReverse logDensity width intervals length
        point ∈
      fixedRuntimeSuccessSet logDensity width intervals maxShrink length := by
  let embedded : (ℝ × ℝ) × RuntimeRandomTrace :=
    (point.1, (Sigma.mk length point.2.1, point.2.2))
  have hsuccess := primitiveRuntimeSuccess_of_density_ne_zero logDensity hwidth
    intervals maxShrink embedded hpoint.1 hpoint.2
  constructor
  · exact hsuccess.new_in_slice
  · rw [fixedRuntimeTraceDensity_reverse logDensity hwidth intervals maxShrink
      length point hpoint]
    exact hpoint.2

/-- The reverse allocation and integer alignment shift carried by a fixed
successful point are the expected translated and negated values. -/
theorem fixedRuntimeReverse_allocation_shift
    (logDensity : ℝ → ℝ) {width : ℝ} (hwidth : 0 < width)
    (intervals maxShrink length : ℕ)
    (signature : FixedRuntimeReplaySignature length)
    (point : (ℝ × ℝ) × FixedRuntimeTrace length)
    (hpoint : point ∈ fixedRuntimeReplayPiece logDensity width intervals
      maxShrink length signature) :
    let reversed := fixedPrimitiveRuntimeAugmentedReverse logDensity width
      intervals length point
    reversed.2.2.1.2 = signature.allocation + signature.shift ∧
      integerAlignmentShift width reversed.1.2
        (runtimeAcceptedPoint logDensity reversed.1.1 width reversed.1.2 intervals
          (Sigma.mk length reversed.2.1, reversed.2.2)) reversed.2.2.1.1 =
        -signature.shift := by
  let embedded : (ℝ × ℝ) × RuntimeRandomTrace :=
    (point.1, (Sigma.mk length point.2.1, point.2.2))
  let reversed := fixedPrimitiveRuntimeAugmentedReverse logDensity width
    intervals length point
  have hembed := fixedPrimitiveRuntimeAugmentedReverse_embed logDensity width
    intervals length point
  have hsuccess := primitiveRuntimeSuccess_of_density_ne_zero logDensity hwidth
    intervals maxShrink embedded hpoint.1.1 hpoint.1.2
  have hinvolution := hsuccess.reverse_involutive hwidth.ne'
  have hallocation : reversed.2.2.1.2 =
      signature.allocation + signature.shift := by
    change (primitiveRuntimeAugmentedReverse logDensity width intervals
      embedded).2.2.1.2 = _
    rw [primitiveRuntimeAugmentedReverse_grid]
    exact congrArg₂ (· + ·) hpoint.2.1 hpoint.2.2.1
  refine ⟨hallocation, ?_⟩
  have hrecover := primitiveRuntimeAcceptedPoint_reverse logDensity intervals
    embedded (lt_of_le_of_lt hsuccess.old_mem.1 hsuccess.old_mem.2)
    hsuccess.finalBracket_reverse
  have hreverseShift := integerAlignmentShift_reverse
    (width := width) (old := point.1.2)
    (new := runtimeAcceptedPoint logDensity point.1.1 width point.1.2 intervals
      embedded.2) hwidth.ne' point.2.2.1.1
  change integerAlignmentShift width
      (runtimeAcceptedPoint logDensity point.1.1 width point.1.2 intervals
        embedded.2)
      (runtimeAcceptedPoint logDensity point.1.1 width
        (runtimeAcceptedPoint logDensity point.1.1 width point.1.2 intervals
          embedded.2) intervals
        (primitiveRuntimeAugmentedReverse logDensity width intervals embedded).2)
      (reverseAlignment width point.1.2
        (runtimeAcceptedPoint logDensity point.1.1 width point.1.2 intervals
          embedded.2) point.2.2.1.1) = _
  rw [hrecover, hreverseShift, hpoint.2.2.1]

/-- Rerooting preserves every recorded shrink-side decision. -/
theorem fixedRuntimeReverse_rejectedSides
    (logDensity : ℝ → ℝ) {width : ℝ} (hwidth : 0 < width)
    (intervals maxShrink length : ℕ)
    (signature : FixedRuntimeReplaySignature length)
    (point : (ℝ × ℝ) × FixedRuntimeTrace length)
    (hpoint : point ∈ fixedRuntimeReplayPiece logDensity width intervals
      maxShrink length signature) :
    let reversed := fixedPrimitiveRuntimeAugmentedReverse logDensity width
      intervals length point
    ∀ index, (reversed.2.1 index < reversed.1.2) =
      (reverseFixedRuntimeReplaySignature signature).rejectedLeft index := by
  let embedded : (ℝ × ℝ) × RuntimeRandomTrace :=
    (point.1, (Sigma.mk length point.2.1, point.2.2))
  have hsuccess := primitiveRuntimeSuccess_of_density_ne_zero logDensity hwidth
    intervals maxShrink embedded hpoint.1.1 hpoint.1.2
  simp only [fixedPrimitiveRuntimeAugmentedReverse,
    reverseFixedRuntimeReplaySignature]
  intro index
  have hsame := hsuccess.rejected_same_side (point.2.1 index)
    (List.mem_ofFn.mpr ⟨index, rfl⟩)
  change (point.2.1 index <
      runtimeAcceptedPoint logDensity point.1.1 width point.1.2 intervals
        embedded.2) = signature.rejectedLeft index
  rw [← hsame]
  exact hpoint.2.2.2.2.2 index

/-- The fixed-dimensional successful rerooting is an involution. -/
theorem fixedPrimitiveRuntimeAugmentedReverse_involutive
    (logDensity : ℝ → ℝ) {width : ℝ} (hwidth : 0 < width)
    (intervals maxShrink length : ℕ)
    (point : (ℝ × ℝ) × FixedRuntimeTrace length)
    (hpoint : point ∈ fixedRuntimeSuccessSet logDensity width intervals
      maxShrink length) :
    fixedPrimitiveRuntimeAugmentedReverse logDensity width intervals length
        (fixedPrimitiveRuntimeAugmentedReverse logDensity width intervals length
          point) = point := by
  have hinvolution :=
    primitiveRuntimeAugmentedReverse_involutive_of_density_ne_zero logDensity
      hwidth intervals maxShrink
      (point.1, (Sigma.mk length point.2.1, point.2.2)) hpoint.1 hpoint.2
  let reverse := fixedPrimitiveRuntimeAugmentedReverse logDensity width intervals
    length
  let embed : ((ℝ × ℝ) × FixedRuntimeTrace length) →
      ((ℝ × ℝ) × RuntimeRandomTrace) := fun value =>
    (value.1, (Sigma.mk length value.2.1, value.2.2))
  have hfirst : primitiveRuntimeAugmentedReverse logDensity width intervals
      (embed point) = embed (reverse point) := by
    exact fixedPrimitiveRuntimeAugmentedReverse_embed logDensity width intervals
      length point
  have hsecond : primitiveRuntimeAugmentedReverse logDensity width intervals
      (embed (reverse point)) = embed (reverse (reverse point)) := by
    exact fixedPrimitiveRuntimeAugmentedReverse_embed logDensity width intervals
      length (reverse point)
  have hembed : embed (reverse (reverse point)) = embed point := by
    rw [← hsecond, ← hfirst]
    exact hinvolution
  apply Prod.ext
  · exact congrArg (fun value => value.1) hembed
  · apply Prod.ext
    · have hsigma := congrArg (fun value => value.2.1) hembed
      exact eq_of_heq (Sigma.mk.inj_iff.mp hsigma |>.2)
    · exact congrArg (fun value => value.2.2) hembed

/-- On each finite rejected-length stratum, the already-proved likelihood
symmetry lifts any raw restricted-base preservation theorem to preservation of
the complete weighted successful/fallback law. Thus the sole remaining
change-of-variables obligation is explicitly the unweighted product measure. -/
theorem fixedGuardedRuntimeReverse_withDensity_measurePreserving
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    {width : ℝ} (hwidth : 0 < width) (intervals maxShrink length : ℕ)
    (stateBase : Measure (ℝ × ℝ))
    (hbase : MeasurePreserving
      (fixedPrimitiveRuntimeAugmentedReverse logDensity width intervals length)
      ((stateBase.prod (fixedRuntimeTraceBase length)).restrict
        (fixedRuntimeSuccessSet logDensity width intervals maxShrink length))
      ((stateBase.prod (fixedRuntimeTraceBase length)).restrict
        (fixedRuntimeSuccessSet logDensity width intervals maxShrink length))) :
    MeasurePreserving
      (Mcmc.Kernel.guardedTraceTransform
        (fixedRuntimeSuccessSet logDensity width intervals maxShrink length)
        (fixedPrimitiveRuntimeAugmentedReverse logDensity width intervals length))
      ((stateBase.prod (fixedRuntimeTraceBase length)).withDensity
        (fun point => runtimeTraceDensity logDensity width intervals maxShrink
          point.1 (Sigma.mk length point.2.1, point.2.2)))
      ((stateBase.prod (fixedRuntimeTraceBase length)).withDensity
        (fun point => runtimeTraceDensity logDensity width intervals maxShrink
          point.1 (Sigma.mk length point.2.1, point.2.2))) := by
  apply guardedTraceTransform_withDensity_measurePreserving
    (stateBase.prod (fixedRuntimeTraceBase length))
    (fixedRuntimeSuccessSet logDensity width intervals maxShrink length)
    (measurableSet_fixedRuntimeSuccessSet hlogDensity width intervals maxShrink
      length)
    (fixedPrimitiveRuntimeAugmentedReverse logDensity width intervals length)
    (measurable_fixedPrimitiveRuntimeAugmentedReverse hlogDensity width intervals
      length)
    (fun point => runtimeTraceDensity logDensity width intervals maxShrink
      point.1 (Sigma.mk length point.2.1, point.2.2))
    (measurable_uncurry_runtimeTraceDensity_fixedLength hlogDensity width
      intervals maxShrink length) hbase
  intro point hpoint
  exact fixedRuntimeTraceDensity_reverse logDensity hwidth intervals maxShrink
    length point hpoint

/-- Integration against the variable-length base decomposes into the sum of
finite-dimensional Lebesgue integrals. -/
theorem lintegral_rejectedSequenceLebesgue
    (weight : RejectedSequence → ENNReal) (hweight : Measurable weight) :
    ∫⁻ rejected, weight rejected ∂rejectedSequenceLebesgue =
      ∑' length : ℕ, ∫⁻ values : Fin length → ℝ,
        weight (Sigma.mk length values)
          ∂(Measure.pi fun _ : Fin length => (volume : Measure ℝ)) := by
  rw [rejectedSequenceLebesgue, lintegral_sum_measure]
  congr with length
  rw [rejectedSequenceFiberMeasure, MeasureTheory.lintegral_map hweight
    (measurable_rejectedSequenceMk length)]

abbrev RejectedTraceStratum (intervals : ℕ) (shift : ℤ) :=
  RejectedSequence ×
    ((Alignment × ValidAllocation intervals shift) × (ℝ × ℝ))

/-- A non-dependent carrier for the complete variable-length practical-slice
trace. The integer allocation is unrestricted in the carrier and bounded by
`globalValidAllocation` in its measure. -/
abbrev GlobalRejectedTrace :=
  RejectedSequence × ((Alignment × ℤ) × (ℝ × ℝ))

/-- Global successful-trace reversal, simultaneously covering every integer
alignment-shift stratum and every valid finite allocation. -/
noncomputable def globalRejectedTraceReverse
    (width old new left right : ℝ) (trace : GlobalRejectedTrace) :
    GlobalRejectedTrace :=
  (trace.1,
    (alignmentAllocationReverse width old new trace.2.1,
      acceptedProposalReverse left right trace.2.2))

/-- The global variable-length trace law is preserved between the forward and
reverse bounded-allocation events. Unlike the fixed-stratum theorem, this
single statement has already summed over all integer alignment shifts. -/
theorem globalRejectedTraceReverse_measurePreserving
    {rejectedLaw : Measure RejectedSequence} [SFinite rejectedLaw]
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (threshold : ℝ) (intervals : ℕ)
    {width old new : ℝ} (hgridWidth : width ≠ 0)
    {left right : ℝ} (hbracketWidth : left < right) :
    MeasurePreserving
      (globalRejectedTraceReverse width old new left right)
      (rejectedLaw.prod
        ((((volume : Measure Alignment).prod (Measure.count : Measure ℤ)).restrict
            (globalValidAllocation intervals width old new)).prod
          (((volume : Measure ℝ).prod volume).restrict
            (acceptedProposalSuccess logDensity threshold left right))))
      (rejectedLaw.prod
        ((((volume : Measure Alignment).prod (Measure.count : Measure ℤ)).restrict
            (globalValidAllocation intervals width new old)).prod
          (((volume : Measure ℝ).prod volume).restrict
            (acceptedProposalSuccess logDensity threshold left right)))) := by
  have hinner :=
    (alignmentAllocationReverse_restrict_measurePreserving
      (intervals := intervals) (old := old) (new := new) hgridWidth).prod
      (acceptedProposalReverse_restrict_measurePreserving hlogDensity threshold
        hbracketWidth)
  have hall := (MeasurePreserving.id rejectedLaw).prod hinner
  convert hall using 1
  funext trace
  rfl

/-- A measurable forward/reverse likelihood can be attached after the global
shift/allocation sum. This is the interface used by the stopped-bracket and
shrink-trace likelihood calculation. -/
theorem globalRejectedTraceReverse_withDensity_measurePreserving
    {rejectedLaw : Measure RejectedSequence} [SFinite rejectedLaw]
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (threshold : ℝ) (intervals : ℕ)
    {width old new : ℝ} (hgridWidth : width ≠ 0)
    {left right : ℝ} (hbracketWidth : left < right)
    (sourceDensity targetDensity : GlobalRejectedTrace → ENNReal)
    (htargetDensity : Measurable targetDensity)
    (hinvariant : ∀ trace,
      targetDensity
          (globalRejectedTraceReverse width old new left right trace) =
        sourceDensity trace) :
    MeasurePreserving
      (globalRejectedTraceReverse width old new left right)
      ((rejectedLaw.prod
        ((((volume : Measure Alignment).prod (Measure.count : Measure ℤ)).restrict
            (globalValidAllocation intervals width old new)).prod
          (((volume : Measure ℝ).prod volume).restrict
            (acceptedProposalSuccess logDensity threshold left right)))).withDensity
        sourceDensity)
      ((rejectedLaw.prod
        ((((volume : Measure Alignment).prod (Measure.count : Measure ℤ)).restrict
            (globalValidAllocation intervals width new old)).prod
          (((volume : Measure ℝ).prod volume).restrict
            (acceptedProposalSuccess logDensity threshold left right)))).withDensity
        targetDensity) :=
  measurePreserving_withDensity_of_map_invariant
    (globalRejectedTraceReverse_measurePreserving hlogDensity threshold intervals
      hgridWidth hbracketWidth)
    htargetDensity hinvariant

/-- Complete non-dependent trace carrier with a varying stopped bracket. -/
abbrev GlobalStoppedTrace :=
  RejectedSequence ×
    ((Alignment × ℤ) × (StoppedBracket × (ℝ × ℝ)))

/-- Global reversal across rejected-sequence lengths, integer alignment
shifts, finite valid allocations, and arbitrary nondegenerate stopped
brackets. -/
noncomputable def globalStoppedTraceReverse
    (width old new : ℝ) (trace : GlobalStoppedTrace) : GlobalStoppedTrace :=
  (trace.1,
    (alignmentAllocationReverse width old new trace.2.1,
      stoppedBracketAcceptedReverse trace.2.2))

/-- The complete practical-slice trace reversal preserves the successful
product law while simultaneously summing all shift/allocation strata and
integrating against any s-finite stopped-bracket law. -/
theorem globalStoppedTraceReverse_measurePreserving
    {rejectedLaw : Measure RejectedSequence} [SFinite rejectedLaw]
    {bracketLaw : Measure StoppedBracket} [SFinite bracketLaw]
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (threshold : ℝ) (intervals : ℕ)
    {width old new : ℝ} (hgridWidth : width ≠ 0) :
    MeasurePreserving (globalStoppedTraceReverse width old new)
      (rejectedLaw.prod
        ((((volume : Measure Alignment).prod (Measure.count : Measure ℤ)).restrict
            (globalValidAllocation intervals width old new)).prod
          ((bracketLaw.prod ((volume : Measure ℝ).prod volume)).restrict
            (stoppedBracketAcceptedSuccess logDensity threshold))))
      (rejectedLaw.prod
        ((((volume : Measure Alignment).prod (Measure.count : Measure ℤ)).restrict
            (globalValidAllocation intervals width new old)).prod
          ((bracketLaw.prod ((volume : Measure ℝ).prod volume)).restrict
            (stoppedBracketAcceptedSuccess logDensity threshold)))) := by
  have hinner :=
    (alignmentAllocationReverse_restrict_measurePreserving
      (intervals := intervals) (old := old) (new := new) hgridWidth).prod
      (stoppedBracketAcceptedReverse_restrict_measurePreserving
        (bracketLaw := bracketLaw) hlogDensity threshold)
  have hall := (MeasurePreserving.id rejectedLaw).prod hinner
  convert hall using 1
  funext trace
  rfl

/-- Attach the stopped-bracket and shrink-trace likelihood after every
discrete and continuous trace stratum has been combined. -/
theorem globalStoppedTraceReverse_withDensity_measurePreserving
    {rejectedLaw : Measure RejectedSequence} [SFinite rejectedLaw]
    {bracketLaw : Measure StoppedBracket} [SFinite bracketLaw]
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (threshold : ℝ) (intervals : ℕ)
    {width old new : ℝ} (hgridWidth : width ≠ 0)
    (sourceDensity targetDensity : GlobalStoppedTrace → ENNReal)
    (htargetDensity : Measurable targetDensity)
    (hinvariant : ∀ trace,
      targetDensity (globalStoppedTraceReverse width old new trace) =
        sourceDensity trace) :
    MeasurePreserving (globalStoppedTraceReverse width old new)
      ((rejectedLaw.prod
        ((((volume : Measure Alignment).prod (Measure.count : Measure ℤ)).restrict
            (globalValidAllocation intervals width old new)).prod
          ((bracketLaw.prod ((volume : Measure ℝ).prod volume)).restrict
            (stoppedBracketAcceptedSuccess logDensity threshold)))).withDensity
        sourceDensity)
      ((rejectedLaw.prod
        ((((volume : Measure Alignment).prod (Measure.count : Measure ℤ)).restrict
            (globalValidAllocation intervals width new old)).prod
          ((bracketLaw.prod ((volume : Measure ℝ).prod volume)).restrict
            (stoppedBracketAcceptedSuccess logDensity threshold)))).withDensity
        targetDensity) :=
  measurePreserving_withDensity_of_map_invariant
    (globalStoppedTraceReverse_measurePreserving hlogDensity threshold intervals
      hgridWidth)
    htargetDensity hinvariant

/-- Runtime trace carrier for the auxiliary slice kernel. The current point
is deliberately absent: it is the state coordinate of `(height, current)`.
The final real coordinate is only the accepted uniform fraction. -/
abbrev PracticalTrace :=
  RejectedSequence ×
    ((Alignment × ℤ) × (StoppedBracket × ℝ))

/-- Actual augmented-state reversal for practical slice sampling. It retains
the sampled height, turns the accepted fraction into the new current point,
reroots the grid allocation, and records the reverse fraction. -/
noncomputable def practicalAugmentedReverse (width : ℝ)
    (point : (ℝ × ℝ) × PracticalTrace) : (ℝ × ℝ) × PracticalTrace :=
  let bracket := point.2.2.2.1
  let accepted := acceptedProposalReverse bracket.1.1 bracket.1.2
    (point.1.2, point.2.2.2.2)
  ((point.1.1, accepted.1),
    (point.2.1,
      (alignmentAllocationReverse width point.1.2 accepted.1 point.2.2.1,
        (bracket, accepted.2))))

theorem measurable_practicalAugmentedReverse (width : ℝ) :
    Measurable (practicalAugmentedReverse width) := by
  let accepted : ((ℝ × ℝ) × PracticalTrace) → ℝ × ℝ := fun point =>
    acceptedProposalReverse point.2.2.2.1.1.1 point.2.2.2.1.1.2
      (point.1.2, point.2.2.2.2)
  have haccepted : Measurable accepted := by
    unfold accepted acceptedProposalReverse
    fun_prop
  have hgridInput : Measurable (fun point : (ℝ × ℝ) × PracticalTrace =>
      ((point.1.2, (accepted point).1), point.2.2.1)) :=
    (measurable_snd.comp measurable_fst).prodMk
      (measurable_fst.comp haccepted) |>.prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hgrid : Measurable (fun point : (ℝ × ℝ) × PracticalTrace =>
      alignmentAllocationReverse width point.1.2 (accepted point).1
        point.2.2.1) :=
    (measurable_alignmentAllocationReverse_parameterized width).comp hgridInput
  exact ((measurable_fst.comp measurable_fst).prodMk
      (measurable_fst.comp haccepted)).prodMk
    ((measurable_fst.comp measurable_snd).prodMk
      (hgrid.prodMk
        ((measurable_fst.comp (measurable_snd.comp
            (measurable_snd.comp measurable_snd))).prodMk
          (measurable_snd.comp haccepted))))

/-- The runtime augmented reversal is a genuine involution. This establishes
the exact checked-trace replay law before attaching the joint trace density. -/
theorem practicalAugmentedReverse_involutive
    {width : ℝ} (hwidth : width ≠ 0) :
    Function.Involutive (practicalAugmentedReverse width) := by
  intro point
  rcases point with ⟨⟨threshold, old⟩,
    ⟨rejected, ⟨grid, ⟨bracket, fraction⟩⟩⟩⟩
  let accepted := acceptedProposalReverse bracket.1.1 bracket.1.2
    (old, fraction)
  have haccepted := acceptedProposalReverse_involutive
    (sub_ne_zero.mpr bracket.2.ne') (old, fraction)
  have hgrid := alignmentAllocationReverse_reverse
    (old := old) (new := accepted.1) hwidth grid
  change practicalAugmentedReverse width
      ((threshold, accepted.1),
        (rejected,
          (alignmentAllocationReverse width old accepted.1 grid,
            (bracket, accepted.2)))) =
      ((threshold, old), (rejected, (grid, (bracket, fraction))))
  unfold practicalAugmentedReverse
  simp only
  rw [show acceptedProposalReverse bracket.1.1 bracket.1.2
      (accepted.1, accepted.2) = (old, fraction) by
    exact haccepted]
  rw [hgrid]

/-- Practical log-slice transition assembled from a normalized runtime trace
density and the exact augmented reversal. The density carries the concrete
stepping-out/shrinkage probability calculation. -/
noncomputable def practicalSliceSampler
    (logDensity : ℝ → ℝ) (hlogDensity : Measurable logDensity)
    (width : ℝ) (traceBase : Measure PracticalTrace) [SFinite traceBase]
    (traceDensity : (ℝ × ℝ) → PracticalTrace → ENNReal) :
    ProbabilityTheory.Kernel ℝ ℝ :=
  Mcmc.Kernel.logWithinSliceSampler logDensity hlogDensity
    (Mcmc.Kernel.dependentTraceDrivenHorizontalKernel
      (Mcmc.Kernel.normalizedTraceKernel traceBase traceDensity)
      (practicalAugmentedReverse width)
      (measurable_practicalAugmentedReverse width))

/-- End-to-end exact invariance theorem for the practical runtime carrier.
The remaining concrete client obligations are precisely measurability,
normalization, finiteness, and preservation of the displayed joint density. -/
theorem practicalSliceSampler_invariant
    (logDensity : ℝ → ℝ) (hlogDensity : Measurable logDensity)
    [SFinite (Mcmc.Kernel.logSliceUnderGraph
      (volume : Measure ℝ) logDensity)]
    (width : ℝ) (traceBase : Measure PracticalTrace) [SFinite traceBase]
    (traceDensity : (ℝ × ℝ) → PracticalTrace → ENNReal)
    (htraceDensity : Measurable (Function.uncurry traceDensity))
    (hfinite : ∀ state trace, traceDensity state trace ≠ ⊤)
    (hnormalized : ∀ state,
      ∫⁻ trace, traceDensity state trace ∂traceBase = 1)
    (hpreserving : MeasurePreserving (practicalAugmentedReverse width)
      (((((Mcmc.Kernel.logSliceUnderGraph
        (volume : Measure ℝ) logDensity).map Prod.swap).prod
        traceBase).withDensity (Function.uncurry traceDensity)))
      (((((Mcmc.Kernel.logSliceUnderGraph
        (volume : Measure ℝ) logDensity).map Prod.swap).prod
        traceBase).withDensity (Function.uncurry traceDensity)))) :
    (practicalSliceSampler logDensity hlogDensity width traceBase
      traceDensity).Invariant
      ((volume : Measure ℝ).withDensity
        (fun x => ENNReal.ofReal (Real.exp (logDensity x)))) := by
  exact Mcmc.Kernel.normalizedTraceDrivenLogSliceSampler_invariant_underGraph
    (volume : Measure ℝ) logDensity hlogDensity traceBase traceDensity
    htraceDensity hfinite hnormalized (practicalAugmentedReverse width)
    (measurable_practicalAugmentedReverse width) hpreserving

/-- Successful trace reversal leaves every rejected point and its length
unchanged; only alignment, allocation, and accepted coordinates are rerooted. -/
noncomputable def rejectedSequenceTraceReverse
    (intervals : ℕ) (shift : ℤ) (width old new left right : ℝ)
    (trace : RejectedSequence ×
      ((Alignment × ValidAllocation intervals shift) × (ℝ × ℝ))) :
    RejectedSequence ×
      ((Alignment × ValidAllocation intervals (-shift)) × (ℝ × ℝ)) :=
  (trace.1,
    successfulTraceStratumReverse intervals shift width old new left right trace.2)

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

/-- The genuinely dependent shift stratum: the alignment is restricted to
exactly those offsets whose grid displacement indexes the accompanying valid
allocation type. Reversal maps this law to the `-shift` stratum. -/
theorem dependentSuccessfulTraceStratumReverse_measurePreserving
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (threshold : ℝ) (intervals : ℕ) (shift : ℤ)
    {width old new : ℝ} (hgridWidth : width ≠ 0)
    {left right : ℝ} (hbracketWidth : left < right) :
    MeasurePreserving
      (successfulTraceStratumReverse intervals shift width old new left right)
      ((((volume : Measure Alignment).restrict
          (alignmentShiftStratum width old new shift)).prod
          (Measure.count : Measure (ValidAllocation intervals shift))).prod
        (((volume : Measure ℝ).prod volume).restrict
          (acceptedProposalSuccess logDensity threshold left right)))
      ((((volume : Measure Alignment).restrict
          (alignmentShiftStratum width new old (-shift))).prod
          (Measure.count : Measure (ValidAllocation intervals (-shift)))).prod
        (((volume : Measure ℝ).prod volume).restrict
          (acceptedProposalSuccess logDensity threshold left right))) := by
  have hfirst :=
    (reverseAlignment_restrict_stratum_measurePreserving
      (old := old) (new := new) hgridWidth shift).prod
      (reverseAllocation_measurePreserving intervals shift)
  have hall := hfirst.prod
    (acceptedProposalReverse_restrict_measurePreserving hlogDensity threshold
      hbracketWidth)
  convert hall using 1
  funext trace
  rfl

/-- Add the full variable-length rejected sequence to a dependent successful
stratum. Any chosen law on that sigma type is preserved because reversal
replays the sequence exactly. -/
theorem rejectedSequenceTraceReverse_measurePreserving
    {rejectedLaw : Measure RejectedSequence}
    [SFinite rejectedLaw]
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (threshold : ℝ) (intervals : ℕ) (shift : ℤ)
    {width old new : ℝ} (hgridWidth : width ≠ 0)
    {left right : ℝ} (hbracketWidth : left < right) :
    MeasurePreserving
      (rejectedSequenceTraceReverse intervals shift width old new left right)
      (rejectedLaw.prod
        ((((volume : Measure Alignment).restrict
            (alignmentShiftStratum width old new shift)).prod
            (Measure.count : Measure (ValidAllocation intervals shift))).prod
          (((volume : Measure ℝ).prod volume).restrict
            (acceptedProposalSuccess logDensity threshold left right))))
      (rejectedLaw.prod
        ((((volume : Measure Alignment).restrict
            (alignmentShiftStratum width new old (-shift))).prod
            (Measure.count : Measure (ValidAllocation intervals (-shift)))).prod
          (((volume : Measure ℝ).prod volume).restrict
            (acceptedProposalSuccess logDensity threshold left right)))) := by
  have hall := (MeasurePreserving.id rejectedLaw).prod
    (dependentSuccessfulTraceStratumReverse_measurePreserving hlogDensity
      threshold intervals shift (old := old) (new := new) hgridWidth
      hbracketWidth)
  convert hall using 1
  funext trace
  rfl

/-- Attach the complete successful shrink-trace likelihood to the
variable-length dependent stratum. Forward and reverse densities may live on
different allocation types; pointwise reversal equality is the exact
likelihood obligation discharged by the stepping-out/shrinkage symmetry
lemmas. -/
theorem rejectedSequenceTraceReverse_withDensity_measurePreserving
    {rejectedLaw : Measure RejectedSequence} [SFinite rejectedLaw]
    {logDensity : ℝ → ℝ} (hlogDensity : Measurable logDensity)
    (threshold : ℝ) (intervals : ℕ) (shift : ℤ)
    {width old new : ℝ} (hgridWidth : width ≠ 0)
    {left right : ℝ} (hbracketWidth : left < right)
    (sourceDensity : RejectedTraceStratum intervals shift → ENNReal)
    (targetDensity : RejectedTraceStratum intervals (-shift) → ENNReal)
    (htargetDensity : Measurable targetDensity)
    (hinvariant : ∀ trace,
      targetDensity
          (rejectedSequenceTraceReverse intervals shift width old new left right
            trace) = sourceDensity trace) :
    MeasurePreserving
      (rejectedSequenceTraceReverse intervals shift width old new left right)
      ((rejectedLaw.prod
        ((((volume : Measure Alignment).restrict
            (alignmentShiftStratum width old new shift)).prod
            (Measure.count : Measure (ValidAllocation intervals shift))).prod
          (((volume : Measure ℝ).prod volume).restrict
            (acceptedProposalSuccess logDensity threshold left right)))).withDensity
        sourceDensity)
      ((rejectedLaw.prod
        ((((volume : Measure Alignment).restrict
            (alignmentShiftStratum width new old (-shift))).prod
            (Measure.count : Measure (ValidAllocation intervals (-shift)))).prod
          (((volume : Measure ℝ).prod volume).restrict
            (acceptedProposalSuccess logDensity threshold left right)))).withDensity
        targetDensity) :=
  measurePreserving_withDensity_of_map_invariant
    (rejectedSequenceTraceReverse_measurePreserving hlogDensity threshold
      intervals shift (old := old) (new := new) hgridWidth hbracketWidth)
    htargetDensity hinvariant

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

/-- Weighted version on the true offset-dependent allocation stratum. -/
theorem dependentSuccessfulTraceStratumReverse_withDensity_measurePreserving
    (intervals : ℕ) (shift : ℤ) {width old new : ℝ}
    (hgridWidth : width ≠ 0) {left right : ℝ} (hbracketWidth : left < right)
    {pairDensity : ℝ × ℝ → ENNReal} (hpairDensity : Measurable pairDensity)
    (hsymmetric : ∀ old new, pairDensity (old, new) = pairDensity (new, old)) :
    MeasurePreserving
      (successfulTraceStratumReverse intervals shift width old new left right)
      ((((volume : Measure Alignment).restrict
          (alignmentShiftStratum width old new shift)).prod
          (Measure.count : Measure (ValidAllocation intervals shift))).prod
        (((volume : Measure ℝ).prod volume).withDensity
          (acceptedProposalPairDensity left right pairDensity)))
      ((((volume : Measure Alignment).restrict
          (alignmentShiftStratum width new old (-shift))).prod
          (Measure.count : Measure (ValidAllocation intervals (-shift)))).prod
        (((volume : Measure ℝ).prod volume).withDensity
          (acceptedProposalPairDensity left right pairDensity))) := by
  have hfirst :=
    (reverseAlignment_restrict_stratum_measurePreserving
      (old := old) (new := new) hgridWidth shift).prod
      (reverseAllocation_measurePreserving intervals shift)
  have hall := hfirst.prod
    (acceptedProposalReverse_withDensity_measurePreserving hbracketWidth
      hpairDensity hsymmetric)
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
