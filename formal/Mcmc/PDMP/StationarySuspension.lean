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

end Mcmc.PDMP
