import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import McmcLean.Kernel.Coupling

/-!
# Couplings of probability densities

This module develops the density-overlap algebra used by maximal couplings on
general measurable spaces. Two probability densities `f` and `g` relative to
a common reference measure split into the common density `min f g` and two
residual densities. The common mass is at most one, both residual measures
have mass one minus the overlap, and common plus residual reconstructs each
original density measure.

These identities are the measure-theoretic core of the maximal Gaussian
proposal coupling needed by coupled random-walk Metropolis--Hastings.
-/

open MeasureTheory
open scoped ENNReal

namespace McmcLean.Kernel

variable {State : Type*} [MeasurableSpace State]

/-- The part of the diagonal lying over a specified state-space region. -/
def diagonalOver (A : Set State) : Set (State × State) :=
  Set.diagonal State ∩ Prod.fst ⁻¹' A

/-- A region-restricted diagonal is measurable. -/
theorem measurableSet_diagonalOver [MeasurableEq State]
    {A : Set State} (hA : MeasurableSet A) :
    MeasurableSet (diagonalOver A) :=
  measurableSet_diagonal.inter (measurable_fst hA)

omit [MeasurableSpace State] in
theorem diagonal_preimage_diagonalOver (A : Set State) :
    (fun x : State => (x, x)) ⁻¹' diagonalOver A = A := by
  ext x
  simp [diagonalOver]

/-- Total common mass of two densities relative to the same reference
measure. -/
noncomputable def densityOverlap (reference : Measure State)
    (f g : State → ENNReal) : ENNReal :=
  ∫⁻ x, min (f x) (g x) ∂reference

/-- The measure carried by the pointwise common part of two densities. -/
noncomputable def commonDensityMeasure (reference : Measure State)
    (f g : State → ENNReal) : Measure State :=
  reference.withDensity fun x => min (f x) (g x)

/-- The part of the first density left after removing its common part. -/
noncomputable def leftResidualDensityMeasure (reference : Measure State)
    (f g : State → ENNReal) : Measure State :=
  reference.withDensity fun x => f x - min (f x) (g x)

/-- The part of the second density left after removing its common part. -/
noncomputable def rightResidualDensityMeasure (reference : Measure State)
    (f g : State → ENNReal) : Measure State :=
  reference.withDensity fun x => g x - min (f x) (g x)

theorem measurable_min_density {f g : State → ENNReal}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => min (f x) (g x) :=
  hf.min hg

/-- The overlap of two normalized densities is at most one. -/
theorem densityOverlap_le_one
    (reference : Measure State) {f g : State → ENNReal}
    (hfNorm : ∫⁻ x, f x ∂reference = 1) :
    densityOverlap reference f g ≤ 1 := by
  rw [densityOverlap, ← hfNorm]
  exact lintegral_mono fun x => min_le_left (f x) (g x)

theorem densityOverlap_ne_top
    (reference : Measure State) {f g : State → ENNReal}
    (hfNorm : ∫⁻ x, f x ∂reference = 1) :
    densityOverlap reference f g ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top
    (densityOverlap_le_one reference hfNorm)

/-- Strictly positive densities over a nonzero reference measure have positive
overlap. -/
theorem densityOverlap_pos
    (reference : Measure State) {f g : State → ENNReal}
    (hf : Measurable f) (hg : Measurable g)
    (hreference : 0 < reference Set.univ)
    (hfPos : ∀ x, 0 < f x) (hgPos : ∀ x, 0 < g x) :
    0 < densityOverlap reference f g := by
  rw [densityOverlap, lintegral_pos_iff_support (hf.min hg)]
  have hsupp : Function.support (fun x => min (f x) (g x)) = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (lt_min (hfPos x) (hgPos x)).ne'
  rw [hsupp]
  exact hreference

/-- A common pointwise density floor on a measurable region gives a
quantitative lower bound on density overlap. -/
theorem densityFloor_mul_measure_le_densityOverlap
    (reference : Measure State) {f g : State → ENNReal}
    {A : Set State} (hA : MeasurableSet A) (floor : ENNReal)
    (hfloorF : ∀ x ∈ A, floor ≤ f x)
    (hfloorG : ∀ x ∈ A, floor ≤ g x) :
    floor * reference A ≤ densityOverlap reference f g := by
  rw [densityOverlap]
  calc
    floor * reference A = ∫⁻ _x in A, floor ∂reference :=
      (setLIntegral_const A floor).symm
    _ ≤ ∫⁻ x in A, min (f x) (g x) ∂reference := by
      apply setLIntegral_mono' hA
      intro x hx
      exact le_min (hfloorF x hx) (hfloorG x hx)
    _ ≤ ∫⁻ x, min (f x) (g x) ∂reference :=
      setLIntegral_le_lintegral A _

/-- The common measure has total mass equal to the density overlap. -/
theorem commonDensityMeasure_apply_univ
    (reference : Measure State) (f g : State → ENNReal) :
    commonDensityMeasure reference f g Set.univ =
      densityOverlap reference f g := by
  rw [commonDensityMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, densityOverlap]

/-- The first residual measure has exactly the missing overlap mass. -/
theorem leftResidualDensityMeasure_apply_univ
    (reference : Measure State) {f g : State → ENNReal}
    (hf : Measurable f) (hg : Measurable g)
    (hfNorm : ∫⁻ x, f x ∂reference = 1) :
    leftResidualDensityMeasure reference f g Set.univ =
      1 - densityOverlap reference f g := by
  rw [leftResidualDensityMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  rw [lintegral_sub (measurable_min_density hf hg)
    (densityOverlap_ne_top reference hfNorm)
    (ae_of_all reference fun x => min_le_left (f x) (g x))]
  rw [hfNorm, densityOverlap]

/-- The second residual measure has exactly the missing overlap mass. -/
theorem rightResidualDensityMeasure_apply_univ
    (reference : Measure State) {f g : State → ENNReal}
    (hf : Measurable f) (hg : Measurable g)
    (hgNorm : ∫⁻ x, g x ∂reference = 1) :
    rightResidualDensityMeasure reference f g Set.univ =
      1 - densityOverlap reference f g := by
  rw [rightResidualDensityMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  have hoverlap_ne_top : densityOverlap reference f g ≠ ∞ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    rw [densityOverlap, ← hgNorm]
    exact lintegral_mono fun x => min_le_right (f x) (g x)
  rw [lintegral_sub (measurable_min_density hf hg)
    hoverlap_ne_top
    (ae_of_all reference fun x => min_le_right (f x) (g x))]
  rw [hgNorm, densityOverlap]

/-- Common plus first residual reconstructs the first density measure. -/
theorem common_add_leftResidual
    (reference : Measure State) {f g : State → ENNReal}
    (hf : Measurable f) (hg : Measurable g) :
    commonDensityMeasure reference f g +
        leftResidualDensityMeasure reference f g =
      reference.withDensity f := by
  ext s hs
  rw [Measure.add_apply, commonDensityMeasure, leftResidualDensityMeasure,
    withDensity_apply _ hs, withDensity_apply _ hs, withDensity_apply _ hs,
    ← lintegral_add_left (measurable_min_density hf hg)]
  apply lintegral_congr
  intro x
  simpa only [add_comm] using
    tsub_add_cancel_of_le (min_le_left (f x) (g x))

/-- Common plus second residual reconstructs the second density measure. -/
theorem common_add_rightResidual
    (reference : Measure State) {f g : State → ENNReal}
    (hf : Measurable f) (hg : Measurable g) :
    commonDensityMeasure reference f g +
        rightResidualDensityMeasure reference f g =
      reference.withDensity g := by
  ext s hs
  rw [Measure.add_apply, commonDensityMeasure, rightResidualDensityMeasure,
    withDensity_apply _ hs, withDensity_apply _ hs, withDensity_apply _ hs,
    ← lintegral_add_left (measurable_min_density hf hg)]
  apply lintegral_congr
  intro x
  simpa only [add_comm] using
    tsub_add_cancel_of_le (min_le_right (f x) (g x))

section MaximalConstruction

variable (reference : Measure State) [SFinite reference]

/-- Maximal coupling of two normalized densities. The common density is sent
to the diagonal. Unless the overlap is already one, the two residual measures
are coupled independently and scaled by the reciprocal residual mass. -/
noncomputable def maximalDensityCoupling (f g : State → ENNReal) :
    Measure (State × State) :=
  if densityOverlap reference f g = 1 then
    (commonDensityMeasure reference f g).map fun x => (x, x)
  else
    (commonDensityMeasure reference f g).map (fun x => (x, x)) +
      (1 - densityOverlap reference f g)⁻¹ •
        ((leftResidualDensityMeasure reference f g).prod
          (rightResidualDensityMeasure reference f g))

omit [SFinite reference] in
private theorem residualMass_ne_zero
    {f g : State → ENNReal}
    (hfNorm : ∫⁻ x, f x ∂reference = 1)
    (hoverlap : densityOverlap reference f g ≠ 1) :
    1 - densityOverlap reference f g ≠ 0 := by
  rw [ne_eq, tsub_eq_zero_iff_le, not_le]
  exact lt_of_le_of_ne (densityOverlap_le_one reference hfNorm) hoverlap

omit [SFinite reference] in
private theorem residualMass_ne_top (f g : State → ENNReal) :
    1 - densityOverlap reference f g ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self

/-- The maximal density coupling has total mass one. -/
theorem maximalDensityCoupling_apply_univ
    {f g : State → ENNReal}
    (hf : Measurable f) (hg : Measurable g)
    (hfNorm : ∫⁻ x, f x ∂reference = 1)
    (hgNorm : ∫⁻ x, g x ∂reference = 1) :
    maximalDensityCoupling reference f g Set.univ = 1 := by
  letI : SFinite (leftResidualDensityMeasure reference f g) := by
    unfold leftResidualDensityMeasure
    infer_instance
  letI : SFinite (rightResidualDensityMeasure reference f g) := by
    unfold rightResidualDensityMeasure
    infer_instance
  have hdiag : Measurable (fun x : State => (x, x)) :=
    measurable_id.prodMk measurable_id
  rw [maximalDensityCoupling]
  split_ifs with hoverlap
  · rw [Measure.map_apply hdiag
      MeasurableSet.univ, Set.preimage_univ,
      commonDensityMeasure_apply_univ, hoverlap]
  · rw [Measure.add_apply, Measure.map_apply
      hdiag MeasurableSet.univ,
      Set.preimage_univ, Measure.smul_apply]
    rw [← Set.univ_prod_univ, Measure.prod_prod,
      commonDensityMeasure_apply_univ,
      leftResidualDensityMeasure_apply_univ reference hf hg hfNorm,
      rightResidualDensityMeasure_apply_univ reference hf hg hgNorm]
    let d := 1 - densityOverlap reference f g
    have hd0 : d ≠ 0 := residualMass_ne_zero reference hfNorm hoverlap
    have hdtop : d ≠ ∞ := residualMass_ne_top reference f g
    change densityOverlap reference f g + d⁻¹ * (d * d) = 1
    calc
      densityOverlap reference f g + d⁻¹ * (d * d) =
          densityOverlap reference f g + d := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hd0 hdtop, one_mul]
      _ = 1 := by
        simpa only [d, add_comm] using
          tsub_add_cancel_of_le (densityOverlap_le_one reference hfNorm)

/-- The maximal density coupling is a probability measure. -/
theorem maximalDensityCoupling_isProbability
    {f g : State → ENNReal}
    (hf : Measurable f) (hg : Measurable g)
    (hfNorm : ∫⁻ x, f x ∂reference = 1)
    (hgNorm : ∫⁻ x, g x ∂reference = 1) :
    IsProbabilityMeasure (maximalDensityCoupling reference f g) :=
  ⟨maximalDensityCoupling_apply_univ reference hf hg hfNorm hgNorm⟩

/-- The first marginal of the maximal density coupling is the first density
measure. -/
theorem maximalDensityCoupling_fst
    {f g : State → ENNReal}
    (hf : Measurable f) (hg : Measurable g)
    (hfNorm : ∫⁻ x, f x ∂reference = 1)
    (hgNorm : ∫⁻ x, g x ∂reference = 1) :
    (maximalDensityCoupling reference f g).fst =
      reference.withDensity f := by
  letI : SFinite (leftResidualDensityMeasure reference f g) := by
    unfold leftResidualDensityMeasure
    infer_instance
  letI : SFinite (rightResidualDensityMeasure reference f g) := by
    unfold rightResidualDensityMeasure
    infer_instance
  have hdiag : Measurable (fun x : State => (x, x)) :=
    measurable_id.prodMk measurable_id
  ext s hs
  rw [Measure.fst_apply hs, maximalDensityCoupling]
  split_ifs with hoverlap
  · rw [Measure.map_apply hdiag
      (measurable_fst hs)]
    have hpre : (fun x : State => (x, x)) ⁻¹' (Prod.fst ⁻¹' s) = s := by
      ext x
      rfl
    rw [hpre]
    have hresidual : leftResidualDensityMeasure reference f g = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      rw [leftResidualDensityMeasure_apply_univ reference hf hg hfNorm,
        hoverlap, tsub_self]
    have hdecomp := common_add_leftResidual reference hf hg
    rw [hresidual, add_zero] at hdecomp
    rw [hdecomp]
  · rw [Measure.add_apply,
      Measure.map_apply hdiag (measurable_fst hs),
      Measure.smul_apply]
    have hpre : (fun x : State => (x, x)) ⁻¹' (Prod.fst ⁻¹' s) = s := by
      ext x
      rfl
    rw [hpre, ← Set.prod_univ, Measure.prod_prod s Set.univ,
      rightResidualDensityMeasure_apply_univ reference hf hg hgNorm]
    let d := 1 - densityOverlap reference f g
    have hd0 : d ≠ 0 := residualMass_ne_zero reference hfNorm hoverlap
    have hdtop : d ≠ ∞ := residualMass_ne_top reference f g
    change commonDensityMeasure reference f g s + d⁻¹ *
        (leftResidualDensityMeasure reference f g s * d) =
      reference.withDensity f s
    rw [mul_comm (leftResidualDensityMeasure reference f g s) d,
      ← mul_assoc, ENNReal.inv_mul_cancel hd0 hdtop, one_mul]
    exact congrArg (fun μ : Measure State => μ s)
      (common_add_leftResidual reference hf hg)

/-- The second marginal of the maximal density coupling is the second density
measure. -/
theorem maximalDensityCoupling_snd
    {f g : State → ENNReal}
    (hf : Measurable f) (hg : Measurable g)
    (hfNorm : ∫⁻ x, f x ∂reference = 1)
    (hgNorm : ∫⁻ x, g x ∂reference = 1) :
    (maximalDensityCoupling reference f g).snd =
      reference.withDensity g := by
  letI : SFinite (leftResidualDensityMeasure reference f g) := by
    unfold leftResidualDensityMeasure
    infer_instance
  letI : SFinite (rightResidualDensityMeasure reference f g) := by
    unfold rightResidualDensityMeasure
    infer_instance
  have hdiag : Measurable (fun x : State => (x, x)) :=
    measurable_id.prodMk measurable_id
  ext s hs
  rw [Measure.snd_apply hs, maximalDensityCoupling]
  split_ifs with hoverlap
  · rw [Measure.map_apply hdiag
      (measurable_snd hs)]
    have hpre : (fun x : State => (x, x)) ⁻¹' (Prod.snd ⁻¹' s) = s := by
      ext x
      rfl
    rw [hpre]
    have hresidual : rightResidualDensityMeasure reference f g = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      rw [rightResidualDensityMeasure_apply_univ reference hf hg hgNorm,
        hoverlap, tsub_self]
    have hdecomp := common_add_rightResidual reference hf hg
    rw [hresidual, add_zero] at hdecomp
    rw [hdecomp]
  · rw [Measure.add_apply,
      Measure.map_apply hdiag (measurable_snd hs),
      Measure.smul_apply]
    have hpre : (fun x : State => (x, x)) ⁻¹' (Prod.snd ⁻¹' s) = s := by
      ext x
      rfl
    rw [hpre, ← Set.univ_prod, Measure.prod_prod Set.univ s,
      leftResidualDensityMeasure_apply_univ reference hf hg hfNorm]
    let d := 1 - densityOverlap reference f g
    have hd0 : d ≠ 0 := residualMass_ne_zero reference hfNorm hoverlap
    have hdtop : d ≠ ∞ := residualMass_ne_top reference f g
    change commonDensityMeasure reference f g s + d⁻¹ *
        (d * rightResidualDensityMeasure reference f g s) =
      reference.withDensity g s
    rw [← mul_assoc, ENNReal.inv_mul_cancel hd0 hdtop, one_mul]
    exact congrArg (fun μ : Measure State => μ s)
      (common_add_rightResidual reference hf hg)

/-- The maximal density construction is a coupling of the requested density
measures. -/
theorem maximalDensityCoupling_isCoupling
    {f g : State → ENNReal}
    (hf : Measurable f) (hg : Measurable g)
    (hfNorm : ∫⁻ x, f x ∂reference = 1)
    (hgNorm : ∫⁻ x, g x ∂reference = 1) :
    IsMeasureCoupling (maximalDensityCoupling reference f g)
      (reference.withDensity f) (reference.withDensity g) :=
  ⟨maximalDensityCoupling_fst reference hf hg hfNorm hgNorm,
    maximalDensityCoupling_snd reference hf hg hfNorm hgNorm⟩

omit [SFinite reference] in
/-- The maximal density construction places at least the full common density
mass on the diagonal. The residual-product term is nonnegative; proving it
adds no diagonal mass is a separate maximality characterization. -/
theorem densityOverlap_le_maximalDensityCoupling_diagonal
    [MeasurableEq State] (f g : State → ENNReal) :
    densityOverlap reference f g ≤
      maximalDensityCoupling reference f g (Set.diagonal State) := by
  have hdiag : Measurable (fun x : State => (x, x)) :=
    measurable_id.prodMk measurable_id
  rw [maximalDensityCoupling]
  split_ifs with hoverlap
  · rw [Measure.map_apply hdiag measurableSet_diagonal]
    have hpre : (fun x : State => (x, x)) ⁻¹' Set.diagonal State = Set.univ := by
      ext x
      simp
    rw [hpre, commonDensityMeasure_apply_univ, hoverlap]
  · rw [Measure.add_apply, Measure.map_apply hdiag measurableSet_diagonal]
    have hpre : (fun x : State => (x, x)) ⁻¹' Set.diagonal State = Set.univ := by
      ext x
      simp
    rw [hpre, commonDensityMeasure_apply_univ]
    exact le_add_right le_rfl

omit [SFinite reference] in
/-- The maximal density coupling places at least the common density mass from
`A` on the portion of the diagonal lying over `A`. -/
theorem commonDensityOn_le_maximalDensityCoupling_diagonalOver
    [MeasurableEq State] {f g : State → ENNReal}
    {A : Set State} (hA : MeasurableSet A) :
    (∫⁻ x in A, min (f x) (g x) ∂reference) ≤
      maximalDensityCoupling reference f g (diagonalOver A) := by
  have hdiag : Measurable (fun x : State => (x, x)) :=
    measurable_id.prodMk measurable_id
  have hdiagOver := measurableSet_diagonalOver hA
  have hcommon : commonDensityMeasure reference f g A =
      ∫⁻ x in A, min (f x) (g x) ∂reference := by
    rw [commonDensityMeasure, withDensity_apply _ hA]
  rw [maximalDensityCoupling]
  split_ifs
  · rw [Measure.map_apply hdiag hdiagOver,
      diagonal_preimage_diagonalOver, hcommon]
  · rw [Measure.add_apply, Measure.map_apply hdiag hdiagOver,
      diagonal_preimage_diagonalOver, hcommon]
    exact le_add_right le_rfl

omit [SFinite reference] in
/-- A common density floor on `A` lower-bounds maximal-coupling mass on the
corresponding restricted diagonal. -/
theorem densityFloor_mul_measure_le_maximalDensityCoupling_diagonalOver
    [MeasurableEq State] {f g : State → ENNReal}
    {A : Set State} (hA : MeasurableSet A) (floor : ENNReal)
    (hfloorF : ∀ x ∈ A, floor ≤ f x)
    (hfloorG : ∀ x ∈ A, floor ≤ g x) :
    floor * reference A ≤
      maximalDensityCoupling reference f g (diagonalOver A) := by
  calc
    floor * reference A ≤
        ∫⁻ x in A, min (f x) (g x) ∂reference := by
      rw [← setLIntegral_const A floor]
      exact setLIntegral_mono' hA fun x hx =>
        le_min (hfloorF x hx) (hfloorG x hx)
    _ ≤ maximalDensityCoupling reference f g (diagonalOver A) :=
      commonDensityOn_le_maximalDensityCoupling_diagonalOver reference hA

omit [SFinite reference] in
/-- Positive density overlap gives positive exact-agreement probability under
the maximal density coupling. -/
theorem maximalDensityCoupling_diagonal_pos
    [MeasurableEq State] {f g : State → ENNReal}
    (hoverlap : 0 < densityOverlap reference f g) :
    0 < maximalDensityCoupling reference f g (Set.diagonal State) :=
  hoverlap.trans_le
    (densityOverlap_le_maximalDensityCoupling_diagonal reference f g)

end MaximalConstruction

end McmcLean.Kernel
