import Mathlib.MeasureTheory.Integral.Prod

/-!
# Stationary suspension foundations

This module develops the measure-theoretic occupation law for a special flow
over a measurable base transformation.  It is the reusable renewal layer
between event-epoch invariance and fixed-real-time stationarity for PDMPs.
-/

open MeasureTheory Set

namespace Mcmc.PDMP

variable {Base : Type*} [MeasurableSpace Base]

/-- Fundamental domain below a nonnegative real-valued roof. -/
def suspensionFundamentalDomain (roof : Base → ℝ) : Set (Base × ℝ) :=
  {point | point.2 ∈ Set.Ico 0 (roof point.1)}

theorem measurableSet_suspensionFundamentalDomain
    {roof : Base → ℝ} (hroof : Measurable roof) :
    MeasurableSet (suspensionFundamentalDomain roof) := by
  unfold suspensionFundamentalDomain
  exact (measurableSet_le measurable_const measurable_snd).inter
    (measurableSet_lt measurable_snd (hroof.comp measurable_fst))

/-- Unnormalized Lebesgue occupation below the roof over a base measure. -/
noncomputable def suspensionOccupationMeasure
    (base : Measure Base) (roof : Base → ℝ) : Measure (Base × ℝ) :=
  (base.prod volume).restrict (suspensionFundamentalDomain roof)

/-- Total suspension mass is the base expectation of the nonnegative roof. -/
theorem suspensionOccupationMeasure_apply_univ
    (base : Measure Base) [SFinite base]
    {roof : Base → ℝ} (hroof : Measurable roof) :
    suspensionOccupationMeasure base roof Set.univ =
      ∫⁻ point, ENNReal.ofReal (roof point) ∂base := by
  unfold suspensionOccupationMeasure
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Measure.prod_apply (measurableSet_suspensionFundamentalDomain hroof)]
  apply lintegral_congr
  intro point
  change volume (Set.Ico 0 (roof point)) = _
  rw [Real.volume_Ico]
  simp

/-- Mean roof mass used to normalize stationary suspension occupation. -/
noncomputable def suspensionMeanRoof
    (base : Measure Base) (roof : Base → ℝ) : ENNReal :=
  ∫⁻ point, ENNReal.ofReal (roof point) ∂base

/-- Normalized stationary occupation candidate for the suspension. -/
noncomputable def normalizedSuspensionOccupationMeasure
    (base : Measure Base) (roof : Base → ℝ) : Measure (Base × ℝ) :=
  (suspensionMeanRoof base roof)⁻¹ •
    suspensionOccupationMeasure base roof

theorem normalizedSuspensionOccupationMeasure_apply_univ
    (base : Measure Base) [SFinite base]
    {roof : Base → ℝ} (hroof : Measurable roof)
    (hmeanZero : suspensionMeanRoof base roof ≠ 0)
    (hmeanTop : suspensionMeanRoof base roof ≠ ⊤) :
    normalizedSuspensionOccupationMeasure base roof Set.univ = 1 := by
  unfold normalizedSuspensionOccupationMeasure
  rw [Measure.smul_apply, smul_eq_mul,
    suspensionOccupationMeasure_apply_univ base hroof]
  change (suspensionMeanRoof base roof)⁻¹ *
      suspensionMeanRoof base roof = 1
  exact ENNReal.inv_mul_cancel hmeanZero hmeanTop

/-- Lebesgue occupation that survives a nonnegative time shift is translated
from the initial roof segment to the corresponding terminal segment. -/
theorem map_add_restrict_Ico (shift roof : ℝ) :
    Measure.map (fun age : ℝ => shift + age)
        (volume.restrict (Set.Ico 0 (roof - shift))) =
      volume.restrict (Set.Ico shift roof) := by
  ext event hevent
  have hmap : Measurable (fun age : ℝ => shift + age) := by fun_prop
  have hsource : MeasurableSet (Set.Ico 0 (roof - shift)) := measurableSet_Ico
  have htarget : MeasurableSet (Set.Ico shift roof) := measurableSet_Ico
  rw [Measure.map_apply hmap hevent,
    Measure.restrict_apply (hmap hevent),
    Measure.restrict_apply hevent]
  have htranslated := congrArg (fun measure : Measure ℝ =>
      measure (event ∩ Set.Ico shift roof))
    (Measure.IsAddLeftInvariant.map_add_left_eq_self
      (μ := (volume : Measure ℝ)) shift)
  rw [Measure.map_apply hmap (hevent.inter htarget)] at htranslated
  have hpre : (fun age : ℝ => shift + age) ⁻¹'
      (event ∩ Set.Ico shift roof) =
      (fun age : ℝ => shift + age) ⁻¹' event ∩
        Set.Ico 0 (roof - shift) := by
    ext age
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ico]
    constructor
    · rintro ⟨heventAge, hlower, hupper⟩
      exact ⟨heventAge, by constructor <;> linarith⟩
    · rintro ⟨heventAge, hzero, hupper⟩
      exact ⟨heventAge, by constructor <;> linarith⟩
  rw [hpre] at htranslated
  exact htranslated

/-- Initial ages that remain below the same roof after a supplied shift. -/
def suspensionSurvivorDomain (roof : Base → ℝ) (shift : ℝ) :
    Set (Base × ℝ) :=
  {point | point.2 ∈ Set.Ico 0 (roof point.1 - shift)}

/-- Terminal part of the same roof reached by translating survivor ages. -/
def suspensionTerminalDomain (roof : Base → ℝ) (shift : ℝ) :
    Set (Base × ℝ) :=
  {point | point.2 ∈ Set.Ico shift (roof point.1)}

/-- Ages whose supplied shift reaches the current roof boundary. -/
def suspensionCrossingDomain (roof : Base → ℝ) (shift : ℝ) :
    Set (Base × ℝ) :=
  {point | point.2 ∈ Set.Ico (max 0 (roof point.1 - shift))
    (roof point.1)}

theorem measurableSet_suspensionSurvivorDomain
    {roof : Base → ℝ} (hroof : Measurable roof) (shift : ℝ) :
    MeasurableSet (suspensionSurvivorDomain roof shift) := by
  unfold suspensionSurvivorDomain
  exact (measurableSet_le measurable_const measurable_snd).inter
    (measurableSet_lt measurable_snd
      ((hroof.comp measurable_fst).sub measurable_const))

theorem measurableSet_suspensionTerminalDomain
    {roof : Base → ℝ} (hroof : Measurable roof) (shift : ℝ) :
    MeasurableSet (suspensionTerminalDomain roof shift) := by
  unfold suspensionTerminalDomain
  exact (measurableSet_le measurable_const measurable_snd).inter
    (measurableSet_lt measurable_snd (hroof.comp measurable_fst))

theorem measurableSet_suspensionCrossingDomain
    {roof : Base → ℝ} (hroof : Measurable roof) (shift : ℝ) :
    MeasurableSet (suspensionCrossingDomain roof shift) := by
  unfold suspensionCrossingDomain
  have hlower : Measurable (fun point : Base × ℝ =>
      max 0 (roof point.1 - shift)) := by fun_prop
  exact (measurableSet_le hlower measurable_snd).inter
    (measurableSet_lt measurable_snd (hroof.comp measurable_fst))

omit [MeasurableSpace Base] in
/-- A nonnegative horizon partitions every roof fiber into the no-boundary
survivor segment and the segment that reaches the next event. -/
theorem suspensionFundamentalDomain_eq_survivor_union_crossing
    (roof : Base → ℝ) {shift : ℝ} (hshift : 0 ≤ shift) :
    suspensionFundamentalDomain roof =
      suspensionSurvivorDomain roof shift ∪
        suspensionCrossingDomain roof shift := by
  ext point
  simp only [suspensionFundamentalDomain, suspensionSurvivorDomain,
    suspensionCrossingDomain, Set.mem_setOf_eq, Set.mem_Ico,
    Set.mem_union]
  constructor
  · intro hfundamental
    by_cases hsurvive : point.2 < roof point.1 - shift
    · exact Or.inl ⟨hfundamental.1, hsurvive⟩
    · exact Or.inr ⟨by
        rw [max_le_iff]
        exact ⟨hfundamental.1, le_of_not_gt hsurvive⟩,
          hfundamental.2⟩
  · rintro (hsurvive | hcross)
    · exact ⟨hsurvive.1, by linarith⟩
    · exact ⟨(le_max_left _ _).trans hcross.1, hcross.2⟩

omit [MeasurableSpace Base] in
theorem disjoint_suspensionSurvivorDomain_crossing
    (roof : Base → ℝ) (shift : ℝ) :
    Disjoint (suspensionSurvivorDomain roof shift)
      (suspensionCrossingDomain roof shift) := by
  rw [Set.disjoint_left]
  intro point hsurvive hcross
  change point.2 ∈ Set.Ico 0 (roof point.1 - shift) at hsurvive
  change point.2 ∈ Set.Ico (max 0 (roof point.1 - shift))
    (roof point.1) at hcross
  exact (not_lt_of_ge ((le_max_right _ _).trans hcross.1)) hsurvive.2

/-- Measure-level survivor/crossing decomposition of stationary roof
occupation. -/
theorem suspensionOccupationMeasure_eq_survivor_add_crossing
    (base : Measure Base) {roof : Base → ℝ} (hroof : Measurable roof)
    {shift : ℝ} (hshift : 0 ≤ shift) :
    suspensionOccupationMeasure base roof =
      (base.prod volume).restrict (suspensionSurvivorDomain roof shift) +
        (base.prod volume).restrict
          (suspensionCrossingDomain roof shift) := by
  unfold suspensionOccupationMeasure
  rw [suspensionFundamentalDomain_eq_survivor_union_crossing roof hshift,
    Measure.restrict_union
      (disjoint_suspensionSurvivorDomain_crossing roof shift)
      (measurableSet_suspensionCrossingDomain hroof shift)]

/-- The no-boundary branch of a suspension shift preserves Lebesgue
occupation exactly, translating the surviving initial segment to the terminal
segment of each roof fiber. -/
theorem map_suspensionSurvivorDomain
    (base : Measure Base) [SFinite base]
    {roof : Base → ℝ} (hroof : Measurable roof) (shift : ℝ) :
    Measure.map (fun point : Base × ℝ => (point.1, shift + point.2))
        ((base.prod volume).restrict
          (suspensionSurvivorDomain roof shift)) =
      (base.prod volume).restrict
        (suspensionTerminalDomain roof shift) := by
  let translate : Base × ℝ → Base × ℝ :=
    fun point => (point.1, shift + point.2)
  have htranslate : Measurable translate := by
    unfold translate
    fun_prop
  have hsurvivor := measurableSet_suspensionSurvivorDomain hroof shift
  have hterminal := measurableSet_suspensionTerminalDomain hroof shift
  ext event hevent
  rw [Measure.map_apply htranslate hevent,
    Measure.restrict_apply (htranslate hevent),
    Measure.restrict_apply hevent,
    Measure.prod_apply ((htranslate hevent).inter hsurvivor),
    Measure.prod_apply (hevent.inter hterminal)]
  apply lintegral_congr
  intro point
  have hsection : MeasurableSet (Prod.mk point ⁻¹' event) :=
    measurable_prodMk_left hevent
  have hfiber := congrArg (fun measure : Measure ℝ =>
      measure (Prod.mk point ⁻¹' event))
    (map_add_restrict_Ico shift (roof point))
  have hadd : Measurable (fun age : ℝ => shift + age) := by fun_prop
  have hpreSection : MeasurableSet
      ((fun age : ℝ => shift + age) ⁻¹' (Prod.mk point ⁻¹' event)) :=
    hadd hsection
  rw [Measure.map_apply hadd hsection,
    Measure.restrict_apply hpreSection,
    Measure.restrict_apply hsection] at hfiber
  have hleft : Prod.mk point ⁻¹'
      (translate ⁻¹' event ∩ suspensionSurvivorDomain roof shift) =
      (fun age : ℝ => shift + age) ⁻¹' (Prod.mk point ⁻¹' event) ∩
        Set.Ico 0 (roof point - shift) := by
    ext age
    simp [translate, suspensionSurvivorDomain]
  have hright : Prod.mk point ⁻¹'
      (event ∩ suspensionTerminalDomain roof shift) =
      (Prod.mk point ⁻¹' event) ∩ Set.Ico shift (roof point) := by
    ext age
    simp [suspensionTerminalDomain]
  rw [hleft, hright]
  exact hfiber

/-! ### Countable special-flow execution -/

/-- Cumulative roof length over the first `eventCount` base iterates. -/
noncomputable def suspensionRoofElapsed
    (baseMap : Base → Base) (roof : Base → ℝ)
    (initial : Base) (eventCount : ℕ) : ℝ :=
  ∑ index ∈ Finset.range eventCount,
    roof ((baseMap^[index]) initial)

theorem measurable_suspensionRoofElapsed
    {baseMap : Base → Base} (hbaseMap : Measurable baseMap)
    {roof : Base → ℝ} (hroof : Measurable roof)
    (eventCount : ℕ) :
    Measurable (fun initial =>
      suspensionRoofElapsed baseMap roof initial eventCount) := by
  unfold suspensionRoofElapsed
  fun_prop

/-- The shifted age lies before the end of the cycle indexed by
`eventCount`. -/
def suspensionCrossed
    (baseMap : Base → Base) (roof : Base → ℝ)
    (initial : Base) (age shift : ℝ) (eventCount : ℕ) : Prop :=
  age + shift < suspensionRoofElapsed baseMap roof initial (eventCount + 1)

theorem measurableSet_suspensionCrossed
    {baseMap : Base → Base} (hbaseMap : Measurable baseMap)
    {roof : Base → ℝ} (hroof : Measurable roof)
    (shift : ℝ) (eventCount : ℕ) :
    MeasurableSet {input : Base × ℝ |
      suspensionCrossed baseMap roof input.1 input.2 shift eventCount} := by
  unfold suspensionCrossed
  exact measurableSet_lt (measurable_snd.add measurable_const)
    ((measurable_suspensionRoofElapsed hbaseMap hroof
      (eventCount + 1)).comp measurable_fst)

/-- Total search predicate, using index zero as a fallback when cumulative
roof length never crosses the shifted age. -/
def suspensionCrossingSearchPredicate
    (baseMap : Base → Base) (roof : Base → ℝ)
    (shift : ℝ) (input : Base × ℝ) (eventCount : ℕ) : Prop :=
  suspensionCrossed baseMap roof input.1 input.2 shift eventCount ∨
    (eventCount = 0 ∧ ¬∃ count,
      suspensionCrossed baseMap roof input.1 input.2 shift count)

omit [MeasurableSpace Base] in
theorem suspensionCrossingSearchPredicate_exists
    (baseMap : Base → Base) (roof : Base → ℝ)
    (shift : ℝ) (input : Base × ℝ) :
    ∃ eventCount,
      suspensionCrossingSearchPredicate baseMap roof shift input eventCount := by
  classical
  by_cases hcross : ∃ eventCount,
      suspensionCrossed baseMap roof input.1 input.2 shift eventCount
  · obtain ⟨eventCount, heventCount⟩ := hcross
    exact ⟨eventCount, Or.inl heventCount⟩
  · exact ⟨0, Or.inr ⟨rfl, hcross⟩⟩

theorem measurableSet_suspensionCrossingSearchPredicate
    {baseMap : Base → Base} (hbaseMap : Measurable baseMap)
    {roof : Base → ℝ} (hroof : Measurable roof)
    (shift : ℝ) (eventCount : ℕ) :
    MeasurableSet {input : Base × ℝ |
      suspensionCrossingSearchPredicate
        baseMap roof shift input eventCount} := by
  classical
  by_cases hzero : eventCount = 0
  · subst eventCount
    simp only [suspensionCrossingSearchPredicate, true_and]
    apply MeasurableSet.union
    · exact measurableSet_suspensionCrossed hbaseMap hroof shift 0
    · have hexists : MeasurableSet {input : Base × ℝ | ∃ count,
          suspensionCrossed baseMap roof input.1 input.2 shift count} := by
        rw [show {input : Base × ℝ | ∃ count,
            suspensionCrossed baseMap roof input.1 input.2 shift count} =
            ⋃ count, {input | suspensionCrossed
              baseMap roof input.1 input.2 shift count} by
          ext input
          simp]
        exact MeasurableSet.iUnion fun count =>
          measurableSet_suspensionCrossed hbaseMap hroof shift count
      exact hexists.compl
  · simp only [suspensionCrossingSearchPredicate, hzero, false_and,
      or_false]
    exact measurableSet_suspensionCrossed hbaseMap hroof shift eventCount

/-- First base index whose roof endpoint lies strictly after the shifted age,
with a total fallback at zero outside the nonexplosive domain. -/
noncomputable def suspensionCrossingIndex
    (baseMap : Base → Base) (roof : Base → ℝ)
    (shift : ℝ) (input : Base × ℝ) : ℕ := by
  classical
  exact Nat.find
    (suspensionCrossingSearchPredicate_exists baseMap roof shift input)

theorem measurable_suspensionCrossingIndex
    {baseMap : Base → Base} (hbaseMap : Measurable baseMap)
    {roof : Base → ℝ} (hroof : Measurable roof)
    (shift : ℝ) :
    Measurable (suspensionCrossingIndex baseMap roof shift) := by
  unfold suspensionCrossingIndex
  classical
  apply measurable_find
  exact measurableSet_suspensionCrossingSearchPredicate
    hbaseMap hroof shift

/-- Total measurable special-flow endpoint after a nonnegative age shift. On
the nonexplosive domain it selects the containing future roof fiber and its
residual age. -/
noncomputable def suspensionEndpoint
    (baseMap : Base → Base) (roof : Base → ℝ)
    (shift : ℝ) (input : Base × ℝ) : Base × ℝ :=
  let eventCount := suspensionCrossingIndex baseMap roof shift input
  ((baseMap^[eventCount]) input.1,
    input.2 + shift -
      suspensionRoofElapsed baseMap roof input.1 eventCount)

theorem measurable_suspensionEndpoint
    {baseMap : Base → Base} (hbaseMap : Measurable baseMap)
    {roof : Base → ℝ} (hroof : Measurable roof)
    (shift : ℝ) :
    Measurable (suspensionEndpoint baseMap roof shift) := by
  classical
  let searchExists : ∀ input : Base × ℝ, ∃ eventCount,
      suspensionCrossingSearchPredicate
        baseMap roof shift input eventCount :=
    suspensionCrossingSearchPredicate_exists baseMap roof shift
  have hfamily : ∀ eventCount, Measurable
      (fun input : Base × ℝ =>
        ((baseMap^[eventCount]) input.1,
          input.2 + shift - suspensionRoofElapsed
            baseMap roof input.1 eventCount)) := by
    intro eventCount
    exact ((hbaseMap.iterate eventCount).comp measurable_fst).prodMk
      ((measurable_snd.add measurable_const).sub
        ((measurable_suspensionRoofElapsed hbaseMap hroof eventCount).comp
          measurable_fst))
  change Measurable (fun input =>
    (fun eventCount input =>
      ((baseMap^[eventCount]) input.1,
        input.2 + shift - suspensionRoofElapsed
          baseMap roof input.1 eventCount))
      (Nat.find (searchExists input)) input)
  exact Measurable.find hfamily
    (measurableSet_suspensionCrossingSearchPredicate
      hbaseMap hroof shift)
    searchExists

omit [MeasurableSpace Base] in
theorem suspensionRoofElapsed_succ
    (baseMap : Base → Base) (roof : Base → ℝ)
    (initial : Base) (eventCount : ℕ) :
    suspensionRoofElapsed baseMap roof initial (eventCount + 1) =
      suspensionRoofElapsed baseMap roof initial eventCount +
        roof ((baseMap^[eventCount]) initial) := by
  unfold suspensionRoofElapsed
  rw [Finset.sum_range_succ]

omit [MeasurableSpace Base] in
theorem suspensionCrossingIndex_crossed
    (baseMap : Base → Base) (roof : Base → ℝ)
    (shift : ℝ) (input : Base × ℝ)
    (hexists : ∃ eventCount,
      suspensionCrossed baseMap roof input.1 input.2 shift eventCount) :
    suspensionCrossed baseMap roof input.1 input.2 shift
      (suspensionCrossingIndex baseMap roof shift input) := by
  classical
  unfold suspensionCrossingIndex
  let searchExists :=
    suspensionCrossingSearchPredicate_exists baseMap roof shift input
  have hspec := Nat.find_spec searchExists
  rcases hspec with hcrossed | hfallback
  · exact hcrossed
  · exact False.elim (hfallback.2 hexists)

omit [MeasurableSpace Base] in
theorem suspensionCrossingIndex_not_crossed_of_lt
    (baseMap : Base → Base) (roof : Base → ℝ)
    (shift : ℝ) (input : Base × ℝ) {eventCount : ℕ}
    (hlt : eventCount <
      suspensionCrossingIndex baseMap roof shift input) :
    ¬suspensionCrossed baseMap roof input.1 input.2 shift eventCount := by
  classical
  unfold suspensionCrossingIndex at hlt
  let searchExists :=
    suspensionCrossingSearchPredicate_exists baseMap roof shift input
  intro hcrossed
  have hminimal := Nat.find_min' searchExists (Or.inl hcrossed)
  omega

omit [MeasurableSpace Base] in
/-- On every terminating nonnegative shift from a nonnegative age, the
special-flow endpoint lies in the fundamental domain of its selected roof. -/
theorem suspensionEndpoint_mem_fundamentalDomain
    (baseMap : Base → Base) (roof : Base → ℝ)
    {shift : ℝ} (hshift : 0 ≤ shift) (input : Base × ℝ)
    (hage : 0 ≤ input.2)
    (hexists : ∃ eventCount,
      suspensionCrossed baseMap roof input.1 input.2 shift eventCount) :
    suspensionEndpoint baseMap roof shift input ∈
      suspensionFundamentalDomain roof := by
  let eventCount := suspensionCrossingIndex baseMap roof shift input
  have hcrossed := suspensionCrossingIndex_crossed
    baseMap roof shift input hexists
  have hupper : input.2 + shift -
      suspensionRoofElapsed baseMap roof input.1 eventCount <
      roof ((baseMap^[eventCount]) input.1) := by
    unfold suspensionCrossed at hcrossed
    rw [suspensionRoofElapsed_succ] at hcrossed
    linarith
  have hlower : 0 ≤ input.2 + shift -
      suspensionRoofElapsed baseMap roof input.1 eventCount := by
    by_cases hzero : eventCount = 0
    · rw [hzero]
      simpa [suspensionRoofElapsed] using add_nonneg hage hshift
    · have hpred : eventCount - 1 < eventCount :=
        Nat.sub_one_lt hzero
      have hnot := suspensionCrossingIndex_not_crossed_of_lt
        baseMap roof shift input hpred
      unfold suspensionCrossed at hnot
      have heq : eventCount - 1 + 1 = eventCount :=
        Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hzero)
      rw [heq] at hnot
      exact sub_nonneg.mpr (le_of_not_gt hnot)
  exact ⟨hlower, hupper⟩

omit [MeasurableSpace Base] in
theorem suspensionCrossingIndex_eq_zero_of_lt_roof
    (baseMap : Base → Base) (roof : Base → ℝ)
    (shift : ℝ) (input : Base × ℝ)
    (hbefore : input.2 + shift < roof input.1) :
    suspensionCrossingIndex baseMap roof shift input = 0 := by
  classical
  change Nat.find (suspensionCrossingSearchPredicate_exists
    baseMap roof shift input) = 0
  apply (Nat.find_eq_zero _).2
  exact Or.inl (by
    simpa [suspensionCrossed, suspensionRoofElapsed] using hbefore)

omit [MeasurableSpace Base] in
/-- Before the first roof boundary, the countable executor is ordinary
vertical translation in the current fiber. -/
theorem suspensionEndpoint_eq_translate_of_lt_roof
    (baseMap : Base → Base) (roof : Base → ℝ)
    (shift : ℝ) (input : Base × ℝ)
    (hbefore : input.2 + shift < roof input.1) :
    suspensionEndpoint baseMap roof shift input =
      (input.1, input.2 + shift) := by
  unfold suspensionEndpoint
  rw [suspensionCrossingIndex_eq_zero_of_lt_roof
    baseMap roof shift input hbefore]
  simp [suspensionRoofElapsed]

omit [MeasurableSpace Base] in
/-- Cumulative roofs split into the current roof and the elapsed roofs of the
base-shifted environment. -/
theorem suspensionRoofElapsed_succ_eq_first_add_tail
    (baseMap : Base → Base) (roof : Base → ℝ)
    (initial : Base) (eventCount : ℕ) :
    suspensionRoofElapsed baseMap roof initial (eventCount + 1) =
      roof initial + suspensionRoofElapsed baseMap roof
        (baseMap initial) eventCount := by
  induction eventCount with
  | zero => simp [suspensionRoofElapsed]
  | succ eventCount ih =>
      have hit : (baseMap^[eventCount + 1]) initial =
          (baseMap^[eventCount]) (baseMap initial) := by
        rw [Function.iterate_succ_apply]
      calc
        suspensionRoofElapsed baseMap roof initial (eventCount + 2) =
            suspensionRoofElapsed baseMap roof initial (eventCount + 1) +
              roof ((baseMap^[eventCount + 1]) initial) :=
          suspensionRoofElapsed_succ _ _ _ _
        _ = (roof initial + suspensionRoofElapsed baseMap roof
              (baseMap initial) eventCount) +
              roof ((baseMap^[eventCount + 1]) initial) := by rw [ih]
        _ = roof initial +
            (suspensionRoofElapsed baseMap roof (baseMap initial) eventCount +
              roof ((baseMap^[eventCount]) (baseMap initial))) := by
          rw [hit]
          ring
        _ = roof initial + suspensionRoofElapsed baseMap roof
            (baseMap initial) (eventCount + 1) := by
          rw [suspensionRoofElapsed_succ]

omit [MeasurableSpace Base] in
/-- Once the first roof is reached, later crossing is exactly crossing of the
shifted base environment with the residual horizon. -/
theorem suspensionCrossed_succ_iff_tail
    (baseMap : Base → Base) (roof : Base → ℝ)
    (input : Base × ℝ) (shift : ℝ)
    (eventCount : ℕ) :
    suspensionCrossed baseMap roof input.1 input.2 shift
        (eventCount + 1) ↔
      suspensionCrossed baseMap roof (baseMap input.1) 0
        (input.2 + shift - roof input.1) eventCount := by
  unfold suspensionCrossed
  rw [suspensionRoofElapsed_succ_eq_first_add_tail]
  constructor <;> intro h <;> linarith

omit [MeasurableSpace Base] in
theorem suspensionEndpoint_crossing_recursion
    (baseMap : Base → Base) (roof : Base → ℝ)
    (input : Base × ℝ) (shift : ℝ)
    (hcrossFirst : roof input.1 ≤ input.2 + shift)
    (hexists : ∃ eventCount,
      suspensionCrossed baseMap roof input.1 input.2 shift eventCount) :
    suspensionEndpoint baseMap roof shift input =
      suspensionEndpoint baseMap roof
        (input.2 + shift - roof input.1) (baseMap input.1, 0) := by
  let residual := input.2 + shift - roof input.1
  have hresidual : 0 ≤ residual := sub_nonneg.mpr hcrossFirst
  have htailExists : ∃ eventCount,
      suspensionCrossed baseMap roof (baseMap input.1) 0 residual eventCount := by
    obtain ⟨eventCount, hcrossed⟩ := hexists
    cases eventCount with
    | zero =>
        unfold suspensionCrossed suspensionRoofElapsed at hcrossed
        simp at hcrossed
        linarith
    | succ eventCount =>
        exact ⟨eventCount,
          (suspensionCrossed_succ_iff_tail
            baseMap roof input shift eventCount).mp hcrossed⟩
  let originalIndex := suspensionCrossingIndex baseMap roof shift input
  let tailIndex := suspensionCrossingIndex baseMap roof residual
    (baseMap input.1, 0)
  have horiginalCrossed : suspensionCrossed baseMap roof input.1 input.2
      shift originalIndex :=
    suspensionCrossingIndex_crossed baseMap roof shift input hexists
  have horiginalPos : 0 < originalIndex := by
    by_contra hnot
    have hzero : originalIndex = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero] at horiginalCrossed
    have hbefore : input.2 + shift < roof input.1 := by
      simpa [suspensionCrossed, suspensionRoofElapsed] using horiginalCrossed
    linarith
  have htailCrossed : suspensionCrossed baseMap roof (baseMap input.1) 0
      residual tailIndex :=
    suspensionCrossingIndex_crossed baseMap roof residual
      (baseMap input.1, 0) htailExists
  have horiginalFromTail : suspensionCrossed baseMap roof input.1 input.2
      shift (tailIndex + 1) :=
    (suspensionCrossed_succ_iff_tail
      baseMap roof input shift tailIndex).mpr htailCrossed
  have horiginalLe : originalIndex ≤ tailIndex + 1 := by
    by_contra hnot
    have hlt : tailIndex + 1 < originalIndex := Nat.lt_of_not_ge hnot
    exact (suspensionCrossingIndex_not_crossed_of_lt
      baseMap roof shift input hlt) horiginalFromTail
  have htailFromOriginal : suspensionCrossed baseMap roof
      (baseMap input.1) 0 residual (originalIndex - 1) := by
    have heq : originalIndex - 1 + 1 = originalIndex :=
      Nat.sub_add_cancel horiginalPos
    apply (suspensionCrossed_succ_iff_tail
      baseMap roof input shift (originalIndex - 1)).mp
    rwa [heq]
  have htailLe : tailIndex ≤ originalIndex - 1 := by
    by_contra hnot
    have hlt : originalIndex - 1 < tailIndex := Nat.lt_of_not_ge hnot
    exact (suspensionCrossingIndex_not_crossed_of_lt
      baseMap roof residual (baseMap input.1, 0) hlt) htailFromOriginal
  have hindex : originalIndex = tailIndex + 1 := by omega
  have hiterate : (baseMap^[tailIndex + 1]) input.1 =
      (baseMap^[tailIndex]) (baseMap input.1) := by
    rw [Function.iterate_succ_apply]
  have hfinal : ((baseMap^[originalIndex]) input.1,
        input.2 + shift - suspensionRoofElapsed
          baseMap roof input.1 originalIndex) =
      ((baseMap^[tailIndex]) (baseMap input.1),
        residual - suspensionRoofElapsed
          baseMap roof (baseMap input.1) tailIndex) := by
    rw [hindex, suspensionRoofElapsed_succ_eq_first_add_tail,
      hiterate]
    unfold residual
    congr 1
    ring
  simpa [suspensionEndpoint, originalIndex, tailIndex, residual] using hfinal

omit [MeasurableSpace Base] in
theorem suspensionCrossingIndex_congr_total
    (baseMap : Base → Base) (roof : Base → ℝ)
    (input₁ input₂ : Base × ℝ) (shift₁ shift₂ : ℝ)
    (hbase : input₁.1 = input₂.1)
    (htotal : input₁.2 + shift₁ = input₂.2 + shift₂) :
    suspensionCrossingIndex baseMap roof shift₁ input₁ =
      suspensionCrossingIndex baseMap roof shift₂ input₂ := by
  classical
  rcases input₁ with ⟨base₁, age₁⟩
  rcases input₂ with ⟨base₂, age₂⟩
  simp only at hbase htotal
  subst base₂
  unfold suspensionCrossingIndex
  congr 1
  funext eventCount
  apply propext
  unfold suspensionCrossingSearchPredicate suspensionCrossed
  rw [htotal]

omit [MeasurableSpace Base] in
/-- Starting from an age inside a roof and shifting by a horizon is exactly
the same pathwise operation as starting at age zero and running for their
sum. -/
theorem suspensionEndpoint_eq_from_zero
    (baseMap : Base → Base) (roof : Base → ℝ)
    (shift : ℝ) (input : Base × ℝ) :
    suspensionEndpoint baseMap roof shift input =
      suspensionEndpoint baseMap roof (input.2 + shift) (input.1, 0) := by
  have hindex := suspensionCrossingIndex_congr_total
    baseMap roof input (input.1, 0) shift (input.2 + shift) rfl (by ring)
  unfold suspensionEndpoint
  rw [hindex]
  simp

/-- The orbit map with variable elapsed time is jointly measurable; it is the
zero-fixed-horizon endpoint with elapsed time stored as the initial age. -/
theorem measurable_suspensionOrbit
    {baseMap : Base → Base} (hbaseMap : Measurable baseMap)
    {roof : Base → ℝ} (hroof : Measurable roof) :
    Measurable (fun input : Base × ℝ =>
      suspensionEndpoint baseMap roof input.2 (input.1, 0)) := by
  have heq : (fun input : Base × ℝ =>
      suspensionEndpoint baseMap roof input.2 (input.1, 0)) =
      suspensionEndpoint baseMap roof 0 := by
    funext input
    simpa using (suspensionEndpoint_eq_from_zero
      baseMap roof 0 input).symm
  rw [heq]
  exact measurable_suspensionEndpoint hbaseMap hroof 0

omit [MeasurableSpace Base] in
/-- After exactly one roof duration, the orbit restarts from the shifted base
at age zero. -/
theorem suspensionEndpoint_roof_add
    (baseMap : Base → Base) (roof : Base → ℝ)
    (initial : Base) {shift : ℝ} (hshift : 0 ≤ shift)
    (htailExists : ∃ eventCount,
      suspensionCrossed baseMap roof (baseMap initial) 0 shift eventCount) :
    suspensionEndpoint baseMap roof (roof initial + shift) (initial, 0) =
      suspensionEndpoint baseMap roof shift (baseMap initial, 0) := by
  have hexists : ∃ eventCount,
      suspensionCrossed baseMap roof initial 0 (roof initial + shift)
        eventCount := by
    obtain ⟨eventCount, hcrossed⟩ := htailExists
    exact ⟨eventCount + 1,
      (suspensionCrossed_succ_iff_tail baseMap roof
        (initial, 0) (roof initial + shift) eventCount).mpr (by
          simpa using hcrossed)⟩
  have hrecursion := suspensionEndpoint_crossing_recursion
    baseMap roof (initial, 0) (roof initial + shift) (by linarith) hexists
  simpa using hrecursion

/-- Two decompositions of a translated finite interval give the telescoping
Lebesgue-measure identity used by stationary suspension occupation. -/
theorem restrict_Ico_shift_add_telescope (shift roof : ℝ)
    (hshift : 0 ≤ shift) (hroof : 0 ≤ roof) :
    volume.restrict (Set.Ico shift (shift + roof)) +
        volume.restrict (Set.Ico 0 shift) =
      volume.restrict (Set.Ico 0 roof) +
        volume.restrict (Set.Ico roof (roof + shift)) := by
  have hdisjointLeft : Disjoint (Set.Ico 0 shift) (Set.Ico shift
      (shift + roof)) := by
    rw [Set.disjoint_left]
    intro value hleft hright
    exact (not_lt_of_ge hright.1) hleft.2
  have hdisjointRight : Disjoint (Set.Ico 0 roof) (Set.Ico roof
      (roof + shift)) := by
    rw [Set.disjoint_left]
    intro value hleft hright
    exact (not_lt_of_ge hright.1) hleft.2
  rw [add_comm (volume.restrict (Set.Ico shift (shift + roof))),
    ← Measure.restrict_union hdisjointLeft measurableSet_Ico,
    Set.Ico_union_Ico_eq_Ico hshift (by linarith),
    ← Measure.restrict_union hdisjointRight measurableSet_Ico,
    Set.Ico_union_Ico_eq_Ico hroof (by linarith)]
  ring_nf

/-- Setwise interval telescope for any measurable suspension orbit. -/
theorem suspensionOrbit_interval_telescope
    {baseMap : Base → Base} (hbaseMap : Measurable baseMap)
    {roof : Base → ℝ} (hroof : Measurable roof)
    (initial : Base) (shift : ℝ) (hshift : 0 ≤ shift)
    (hroofNonneg : 0 ≤ roof initial) (event : Set (Base × ℝ))
    (hevent : MeasurableSet event) :
    (volume.restrict (Set.Ico shift (shift + roof initial)))
          ((fun elapsed => suspensionEndpoint baseMap roof elapsed
            (initial, 0)) ⁻¹' event) +
        (volume.restrict (Set.Ico 0 shift))
          ((fun elapsed => suspensionEndpoint baseMap roof elapsed
            (initial, 0)) ⁻¹' event) =
      (volume.restrict (Set.Ico 0 (roof initial)))
          ((fun elapsed => suspensionEndpoint baseMap roof elapsed
            (initial, 0)) ⁻¹' event) +
        (volume.restrict (Set.Ico (roof initial)
          (roof initial + shift)))
          ((fun elapsed => suspensionEndpoint baseMap roof elapsed
            (initial, 0)) ⁻¹' event) := by
  have horbit : Measurable (fun elapsed =>
      suspensionEndpoint baseMap roof elapsed (initial, 0)) :=
    (measurable_suspensionOrbit hbaseMap hroof).comp
      (measurable_const.prodMk measurable_id)
  have hset := horbit hevent
  exact congrArg (fun measure : Measure ℝ =>
    measure ((fun elapsed => suspensionEndpoint baseMap roof elapsed
      (initial, 0)) ⁻¹' event))
    (restrict_Ico_shift_add_telescope shift (roof initial)
      hshift hroofNonneg)

/-- Terminal orbit occupation above the current roof equals initial orbit
occupation above the shifted base. -/
theorem suspensionOrbit_terminal_eq_shifted_initial
    {baseMap : Base → Base} (hbaseMap : Measurable baseMap)
    {roof : Base → ℝ} (hroof : Measurable roof)
    (initial : Base) (shift : ℝ)
    (hnonexplosive : ∀ elapsed ∈ Set.Ico 0 shift,
      ∃ eventCount, suspensionCrossed baseMap roof
        (baseMap initial) 0 elapsed eventCount)
    (event : Set (Base × ℝ)) (hevent : MeasurableSet event) :
    (volume.restrict (Set.Ico (roof initial) (roof initial + shift)))
          ((fun elapsed => suspensionEndpoint baseMap roof elapsed
            (initial, 0)) ⁻¹' event) =
      (volume.restrict (Set.Ico 0 shift))
          ((fun elapsed => suspensionEndpoint baseMap roof elapsed
            (baseMap initial, 0)) ⁻¹' event) := by
  let addRoof : ℝ → ℝ := fun elapsed => roof initial + elapsed
  have haddRoof : Measurable addRoof := by
    unfold addRoof
    fun_prop
  have horbit : Measurable (fun elapsed =>
      suspensionEndpoint baseMap roof elapsed (initial, 0)) :=
    (measurable_suspensionOrbit hbaseMap hroof).comp
      (measurable_const.prodMk measurable_id)
  have hset : MeasurableSet ((fun elapsed =>
      suspensionEndpoint baseMap roof elapsed (initial, 0)) ⁻¹' event) :=
    horbit hevent
  have htranslated := congrArg (fun measure : Measure ℝ =>
      measure ((fun elapsed => suspensionEndpoint baseMap roof elapsed
        (initial, 0)) ⁻¹' event))
    (map_add_restrict_Ico (roof initial) (roof initial + shift))
  rw [Measure.map_apply haddRoof hset] at htranslated
  have hsource : addRoof ⁻¹'
      ((fun elapsed => suspensionEndpoint baseMap roof elapsed
        (initial, 0)) ⁻¹' event) =ᵐ[
          volume.restrict (Set.Ico 0 shift)]
      ((fun elapsed => suspensionEndpoint baseMap roof elapsed
        (baseMap initial, 0)) ⁻¹' event) := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with elapsed helapsed
    change (suspensionEndpoint baseMap roof
        (roof initial + elapsed) (initial, 0) ∈ event) =
      (suspensionEndpoint baseMap roof elapsed
        (baseMap initial, 0) ∈ event)
    rw [suspensionEndpoint_roof_add baseMap roof initial
      helapsed.1 (hnonexplosive elapsed helapsed)]
  have hlength : roof initial + shift - roof initial = shift := by ring
  rw [hlength] at htranslated
  rw [measure_congr hsource] at htranslated
  simpa [addRoof] using htranslated.symm

/-- Orbit occupation of a measurable event over a base-dependent half-open
elapsed-time interval. -/
noncomputable def suspensionOrbitIntervalMass
    (baseMap : Base → Base) (roof : Base → ℝ)
    (lower upper : Base → ℝ) (event : Set (Base × ℝ))
    (initial : Base) : ENNReal :=
  (volume.restrict (Set.Ico (lower initial) (upper initial)))
    ((fun elapsed => suspensionEndpoint baseMap roof elapsed
      (initial, 0)) ⁻¹' event)

theorem measurable_suspensionOrbitIntervalMass
    {baseMap : Base → Base} (hbaseMap : Measurable baseMap)
    {roof : Base → ℝ} (hroof : Measurable roof)
    {lower upper : Base → ℝ} (hlower : Measurable lower)
    (hupper : Measurable upper) {event : Set (Base × ℝ)}
    (hevent : MeasurableSet event) :
    Measurable (suspensionOrbitIntervalMass
      baseMap roof lower upper event) := by
  let orbit : Base × ℝ → Base × ℝ := fun input =>
    suspensionEndpoint baseMap roof input.2 (input.1, 0)
  have horbit : Measurable orbit :=
    measurable_suspensionOrbit hbaseMap hroof
  let orbitSet : Set (Base × ℝ) :=
    {input | lower input.1 ≤ input.2 ∧ input.2 < upper input.1} ∩
      orbit ⁻¹' event
  have horbitSet : MeasurableSet orbitSet := by
    apply MeasurableSet.inter
    · exact (measurableSet_le (hlower.comp measurable_fst) measurable_snd).inter
        (measurableSet_lt measurable_snd (hupper.comp measurable_fst))
    · exact horbit hevent
  have hsection : (fun initial =>
      volume (Prod.mk initial ⁻¹' orbitSet)) =
      suspensionOrbitIntervalMass baseMap roof lower upper event := by
    funext initial
    unfold suspensionOrbitIntervalMass orbitSet orbit
    rw [Measure.restrict_apply]
    · congr 1
      ext elapsed
      simp [and_comm, and_assoc]
    · exact hevent.preimage (horbit.comp
        (measurable_const.prodMk measurable_id))
  rw [← hsection]
  exact measurable_measure_prodMk_left horbitSet

/-- Integrated orbit occupation over a shifted roof interval equals ordinary
roof occupation. This is the stationary-suspension telescoping theorem at the
base-integral level. -/
theorem lintegral_suspensionOrbitIntervalMass_shift
    (base : Measure Base) [IsProbabilityMeasure base]
    {baseMap : Base → Base} (hbaseMap : Measurable baseMap)
    (hbaseInvariant : Measure.map baseMap base = base)
    {roof : Base → ℝ} (hroof : Measurable roof)
    (hroofNonneg : ∀ᵐ initial ∂base, 0 ≤ roof initial)
    (hnonexplosive : ∀ᵐ initial ∂base, ∀ shift, 0 ≤ shift →
      ∃ eventCount, suspensionCrossed baseMap roof initial 0 shift eventCount)
    (shift : ℝ) (hshift : 0 ≤ shift)
    (event : Set (Base × ℝ)) (hevent : MeasurableSet event) :
    (∫⁻ initial, suspensionOrbitIntervalMass baseMap roof
        (fun _ => shift) (fun initial => shift + roof initial)
        event initial ∂base) =
      ∫⁻ initial, suspensionOrbitIntervalMass baseMap roof
        (fun _ => 0) roof event initial ∂base := by
  let shiftedMass := suspensionOrbitIntervalMass baseMap roof
    (fun _ => shift) (fun initial => shift + roof initial) event
  let initialMass := suspensionOrbitIntervalMass baseMap roof
    (fun _ => 0) roof event
  let earlyMass := suspensionOrbitIntervalMass baseMap roof
    (fun _ => 0) (fun _ => shift) event
  let terminalMass := suspensionOrbitIntervalMass baseMap roof
    roof (fun initial => roof initial + shift) event
  have hshiftedMass : Measurable shiftedMass :=
    measurable_suspensionOrbitIntervalMass hbaseMap hroof
      measurable_const (measurable_const.add hroof) hevent
  have hinitialMass : Measurable initialMass :=
    measurable_suspensionOrbitIntervalMass hbaseMap hroof
      measurable_const hroof hevent
  have hearlyMass : Measurable earlyMass :=
    measurable_suspensionOrbitIntervalMass hbaseMap hroof
      measurable_const measurable_const hevent
  have hterminalMass : Measurable terminalMass :=
    measurable_suspensionOrbitIntervalMass hbaseMap hroof
      hroof (hroof.add measurable_const) hevent
  have hnonexplosiveShifted : ∀ᵐ initial ∂base,
      ∀ elapsed, 0 ≤ elapsed → ∃ eventCount,
        suspensionCrossed baseMap roof (baseMap initial) 0 elapsed eventCount :=
    (MeasurePreserving.quasiMeasurePreserving
      ⟨hbaseMap, hbaseInvariant⟩).ae hnonexplosive
  have htelescope : ∀ᵐ initial ∂base,
      shiftedMass initial + earlyMass initial =
        initialMass initial + terminalMass initial := by
    filter_upwards [hroofNonneg] with initial hroofInitial
    simpa [shiftedMass, initialMass, earlyMass, terminalMass,
      suspensionOrbitIntervalMass] using
      suspensionOrbit_interval_telescope hbaseMap hroof initial shift
        hshift hroofInitial event hevent
  have hterminal : ∀ᵐ initial ∂base,
      terminalMass initial = earlyMass (baseMap initial) := by
    filter_upwards [hnonexplosiveShifted] with initial hnonexplosiveInitial
    apply suspensionOrbit_terminal_eq_shifted_initial
      hbaseMap hroof initial shift
    · intro elapsed helapsed
      exact hnonexplosiveInitial elapsed helapsed.1
    · exact hevent
  have hterminalIntegral :
      (∫⁻ initial, terminalMass initial ∂base) =
        ∫⁻ initial, earlyMass initial ∂base := by
    calc
      (∫⁻ initial, terminalMass initial ∂base) =
          ∫⁻ initial, earlyMass (baseMap initial) ∂base :=
        lintegral_congr_ae hterminal
      _ = ∫⁻ initial, earlyMass initial ∂Measure.map baseMap base := by
        exact (lintegral_map hearlyMass hbaseMap).symm
      _ = ∫⁻ initial, earlyMass initial ∂base := by rw [hbaseInvariant]
  have hintegrated := lintegral_congr_ae htelescope
  rw [lintegral_add_left hshiftedMass,
    lintegral_add_left hinitialMass, hterminalIntegral] at hintegrated
  have hearlyLe (initial : Base) : earlyMass initial ≤
      ENNReal.ofReal shift := by
    unfold earlyMass suspensionOrbitIntervalMass
    calc
      (volume.restrict (Set.Ico 0 shift))
          ((fun elapsed => suspensionEndpoint baseMap roof elapsed
            (initial, 0)) ⁻¹' event) ≤
          (volume.restrict (Set.Ico 0 shift)) Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = ENNReal.ofReal shift := by
        rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          Real.volume_Ico]
        simp
  have hearlyIntegralLe : (∫⁻ initial, earlyMass initial ∂base) ≤
      ENNReal.ofReal shift := by
    calc
      (∫⁻ initial, earlyMass initial ∂base) ≤
          ∫⁻ _ : Base, ENNReal.ofReal shift ∂base :=
        lintegral_mono hearlyLe
      _ = ENNReal.ofReal shift := by simp [lintegral_const]
  have hearlyIntegralNeTop :
      (∫⁻ initial, earlyMass initial ∂base) ≠ ⊤ := by
    exact ne_of_lt (hearlyIntegralLe.trans_lt ENNReal.ofReal_lt_top)
  have hcancel := congrArg (fun mass : ENNReal =>
      mass - ∫⁻ initial, earlyMass initial ∂base) hintegrated
  simpa [ENNReal.add_sub_cancel_right hearlyIntegralNeTop,
    shiftedMass, initialMass] using hcancel

/-- Main stationary-suspension theorem: a measurable, nonexplosive special
flow over an invariant probability base preserves its roof-occupation
measure at every nonnegative time. -/
theorem suspensionEndpoint_map_occupation
    (base : Measure Base) [IsProbabilityMeasure base]
    {baseMap : Base → Base} (hbaseMap : Measurable baseMap)
    (hbaseInvariant : Measure.map baseMap base = base)
    {roof : Base → ℝ} (hroof : Measurable roof)
    (hroofNonneg : ∀ᵐ initial ∂base, 0 ≤ roof initial)
    (hnonexplosive : ∀ᵐ initial ∂base, ∀ shift, 0 ≤ shift →
      ∃ eventCount, suspensionCrossed baseMap roof initial 0 shift eventCount)
    (shift : ℝ) (hshift : 0 ≤ shift) :
    Measure.map (suspensionEndpoint baseMap roof shift)
        (suspensionOccupationMeasure base roof) =
      suspensionOccupationMeasure base roof := by
  have hendpoint := measurable_suspensionEndpoint hbaseMap hroof shift
  have hdomain := measurableSet_suspensionFundamentalDomain hroof
  ext event hevent
  unfold suspensionOccupationMeasure
  rw [Measure.map_apply hendpoint hevent,
    Measure.restrict_apply (hendpoint hevent),
    Measure.restrict_apply hevent,
    Measure.prod_apply ((hendpoint hevent).inter hdomain),
    Measure.prod_apply (hevent.inter hdomain)]
  have hintegral := lintegral_suspensionOrbitIntervalMass_shift
    base hbaseMap hbaseInvariant hroof hroofNonneg hnonexplosive
    shift hshift event hevent
  have hleft : ∀ᵐ initial ∂base,
      volume (Prod.mk initial ⁻¹'
        (suspensionEndpoint baseMap roof shift ⁻¹' event ∩
          suspensionFundamentalDomain roof)) =
      suspensionOrbitIntervalMass baseMap roof
        (fun _ => shift) (fun initial => shift + roof initial)
        event initial := by
    filter_upwards [hroofNonneg] with initial hroofInitial
    unfold suspensionOrbitIntervalMass
    have horbit : Measurable (fun elapsed =>
        suspensionEndpoint baseMap roof elapsed (initial, 0)) :=
      (measurable_suspensionOrbit hbaseMap hroof).comp
        (measurable_const.prodMk measurable_id)
    have hset : MeasurableSet ((fun elapsed =>
        suspensionEndpoint baseMap roof elapsed (initial, 0)) ⁻¹' event) :=
      horbit hevent
    have htranslated := congrArg (fun measure : Measure ℝ =>
        measure ((fun elapsed => suspensionEndpoint baseMap roof elapsed
          (initial, 0)) ⁻¹' event))
      (map_add_restrict_Ico shift (shift + roof initial))
    rw [Measure.map_apply (by fun_prop) hset] at htranslated
    have hlength : shift + roof initial - shift = roof initial := by ring
    rw [hlength] at htranslated
    change volume (Prod.mk initial ⁻¹'
        (suspensionEndpoint baseMap roof shift ⁻¹' event ∩
          suspensionFundamentalDomain roof)) =
      (volume.restrict (Set.Ico shift (shift + roof initial)))
        ((fun elapsed => suspensionEndpoint baseMap roof elapsed
          (initial, 0)) ⁻¹' event)
    rw [← htranslated]
    have hshiftSet : MeasurableSet
        ((fun age => shift + age) ⁻¹'
          ((fun elapsed => suspensionEndpoint baseMap roof elapsed
            (initial, 0)) ⁻¹' event)) :=
      (measurable_const.add measurable_id) hset
    rw [Measure.restrict_apply hshiftSet]
    congr 1
    ext age
    simp only [Set.mem_inter_iff, Set.mem_preimage,
      suspensionFundamentalDomain, Set.mem_setOf_eq, Set.mem_Ico]
    constructor
    · rintro ⟨heventAge, hage⟩
      refine ⟨?_, hage⟩
      rw [suspensionEndpoint_eq_from_zero] at heventAge
      simpa [add_comm] using heventAge
    · rintro ⟨horbitAge, hage⟩
      refine ⟨?_, hage⟩
      rw [suspensionEndpoint_eq_from_zero]
      simpa [add_comm] using horbitAge
  have hright : ∀ᵐ initial ∂base,
      suspensionOrbitIntervalMass baseMap roof (fun _ => 0) roof
          event initial =
        volume (Prod.mk initial ⁻¹'
          (event ∩ suspensionFundamentalDomain roof)) := by
    filter_upwards [hroofNonneg] with initial hroofInitial
    unfold suspensionOrbitIntervalMass
    have horbit : Measurable (fun elapsed =>
        suspensionEndpoint baseMap roof elapsed (initial, 0)) :=
      (measurable_suspensionOrbit hbaseMap hroof).comp
        (measurable_const.prodMk measurable_id)
    have hset : MeasurableSet ((fun elapsed =>
        suspensionEndpoint baseMap roof elapsed (initial, 0)) ⁻¹' event) :=
      horbit hevent
    rw [Measure.restrict_apply hset]
    congr 1
    ext age
    simp only [Set.mem_inter_iff, Set.mem_preimage,
      suspensionFundamentalDomain, Set.mem_setOf_eq, Set.mem_Ico]
    constructor
    · rintro ⟨horbitEvent, hage⟩
      have hbefore : (initial, 0).2 + age < roof (initial, 0).1 := by
        simpa using hage.2
      rw [suspensionEndpoint_eq_translate_of_lt_roof
        baseMap roof age (initial, 0) hbefore] at horbitEvent
      have heventAge : (initial, age) ∈ event := by
        simpa using horbitEvent
      exact ⟨heventAge, hage⟩
    · rintro ⟨heventAge, hage⟩
      refine ⟨?_, hage⟩
      have hbefore : (initial, 0).2 + age < roof (initial, 0).1 := by
        simpa using hage.2
      rw [suspensionEndpoint_eq_translate_of_lt_roof
        baseMap roof age (initial, 0) hbefore]
      simpa using heventAge
  calc
    _ = ∫⁻ initial, suspensionOrbitIntervalMass baseMap roof
        (fun _ => shift) (fun initial => shift + roof initial)
        event initial ∂base := lintegral_congr_ae hleft
    _ = ∫⁻ initial, suspensionOrbitIntervalMass baseMap roof
        (fun _ => 0) roof event initial ∂base := hintegral
    _ = _ := lintegral_congr_ae hright

end Mcmc.PDMP
