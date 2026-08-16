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

end Mcmc.PDMP
