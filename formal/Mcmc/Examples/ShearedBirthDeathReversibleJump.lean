import Mcmc.Examples.PlanarBirthDeathReversibleJump
import Mathlib.MeasureTheory.Group.Prod

/-!
# A non-product reversible-jump transport

This client postcomposes the certified planar scaling birth move with the
nonlinear volume-preserving shear `(x,y) ↦ (x+y³,y)`. The resulting triangular
map `(u₁,u₂) ↦ (2u₁+8u₂³,2u₂)` is genuinely nonlinear and
non-product. Its pushforward density is `1/16` on a curved strip, and the
certificate feeds a complete tagged reversible-jump Metropolis--Hastings
invariance theorem.
-/

open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

namespace Mcmc.Examples.ShearedBirthDeathReversibleJump

open ProbabilityTheory Mcmc.Kernel
open Mcmc.Examples.EuclideanBirthDeathReversibleJump
open Mcmc.Examples.PlanarBirthDeathReversibleJump

abbrev Plane := ℝ × ℝ
abbrev State := Unit ⊕ Plane

/-- Nonlinear unit-determinant triangular shear. -/
def shear (y : Plane) : Plane := (y.1 + y.2 ^ 3, y.2)

/-- Explicit inverse of `shear`. -/
def unshear (y : Plane) : Plane := (y.1 - y.2 ^ 3, y.2)

@[simp] theorem unshear_shear (y : Plane) : unshear (shear y) = y := by
  ext <;> simp [shear, unshear]

@[simp] theorem shear_unshear (y : Plane) : shear (unshear y) = y := by
  ext <;> simp [shear, unshear]

theorem measurable_shear : Measurable shear := by
  unfold shear
  fun_prop

theorem measurable_unshear : Measurable unshear := by
  unfold unshear
  fun_prop

/-- Scaling followed by shear; both output coordinates depend on the second
auxiliary coordinate. -/
def shearedTransport (_ : Unit) (u : Plane) : Plane :=
  shear (planarTransport () u)

/-- The inverse-Jacobian-corrected density on the sheared square. -/
noncomputable def shearedDensity (_ : Unit) (y : Plane) : ENNReal :=
  planarDensity () (unshear y)

theorem measurable_shearedDensity_fixed : Measurable (shearedDensity ()) :=
  measurable_planarDensity_fixed.comp measurable_unshear

theorem measurable_shearedDensity :
    Measurable (Function.uncurry shearedDensity) := by
  exact measurable_shearedDensity_fixed.comp measurable_snd

/-- The nonlinear shear preserves two-dimensional Lebesgue measure. -/
theorem shear_measurePreserving :
    MeasurePreserving shear (volume.prod volume) (volume.prod volume) := by
  let swap : ℝ × ℝ → ℝ × ℝ := fun z => (z.2, z.1)
  have hswap : MeasurePreserving swap
      (volume.prod volume) (volume.prod volume) :=
    Measure.measurePreserving_swap
  have hskew : MeasurePreserving (fun z : ℝ × ℝ =>
      (z.1, z.2 + z.1 ^ 3)) (volume.prod volume) (volume.prod volume) := by
    refine MeasurePreserving.skew_product
      (g := fun y x : ℝ => x + y ^ 3)
      (MeasurePreserving.id (volume : Measure ℝ)) ?_ ?_
    · fun_prop
    · filter_upwards [] with y
      exact map_add_right_eq_self volume (y ^ 3)
  change MeasurePreserving (fun z : ℝ × ℝ =>
    (z.1 + z.2 ^ 3, z.2)) (volume.prod volume) (volume.prod volume)
  simpa [swap, Function.comp_def] using hswap.comp (hskew.comp hswap)

private def square : Set Plane := Ioc (-2) 2 ×ˢ Ioc (-2) 2

private def curvedStrip : Set Plane := unshear ⁻¹' square

private theorem measurableSet_square : MeasurableSet square :=
  measurableSet_Ioc.prod measurableSet_Ioc

private theorem measurableSet_curvedStrip : MeasurableSet curvedStrip :=
  measurableSet_square.preimage measurable_unshear

private theorem shear_preimage_curvedStrip : shear ⁻¹' curvedStrip = square := by
  ext y
  simp only [mem_preimage, curvedStrip, unshear_shear]

private theorem planarDensity_eq_indicator : planarDensity () =
    square.indicator (fun _ => (16 : ENNReal)⁻¹) := by
  funext y
  by_cases h₁ : y.1 ∈ Ioc (-2) 2 <;>
    by_cases h₂ : y.2 ∈ Ioc (-2) 2 <;>
    simp [planarDensity, birthDensity, square, h₁, h₂]
  calc
    (4 : ENNReal)⁻¹ * 4⁻¹ = ((4 : ENNReal)⁻¹) ^ 2 := by rw [pow_two]
    _ = ((4 : ENNReal) ^ 2)⁻¹ := ENNReal.inv_pow.symm
    _ = (16 : ENNReal)⁻¹ := by norm_num

private theorem planar_withDensity_eq :
    (volume.prod volume).withDensity (planarDensity ()) =
      (16 : ENNReal)⁻¹ • (volume.prod volume).restrict square := by
  rw [planarDensity_eq_indicator,
    withDensity_indicator measurableSet_square, withDensity_const]

private theorem sheared_withDensity_eq :
    (volume.prod volume).withDensity (shearedDensity ()) =
      (16 : ENNReal)⁻¹ • (volume.prod volume).restrict curvedStrip := by
  have hdensity : shearedDensity () =
      curvedStrip.indicator (fun _ => (16 : ENNReal)⁻¹) := by
    funext y
    unfold shearedDensity
    rw [planarDensity_eq_indicator]
    by_cases h : unshear y ∈ square <;>
      simp [curvedStrip, h]
  rw [hdensity, withDensity_indicator measurableSet_curvedStrip,
    withDensity_const]

/-- Exact non-product change-of-variables identity. -/
theorem map_planarAuxiliary_sheared :
    planarAuxiliary.map (shearedTransport ()) =
      (volume.prod volume).withDensity (shearedDensity ()) := by
  rw [show shearedTransport () = shear ∘ planarTransport () by rfl,
    ← Measure.map_map measurable_shear
      (planarCertificate.measurableTransport ()),
    map_planarAuxiliary, planar_withDensity_eq, Measure.map_smul]
  have hrestrict :
      (Measure.map shear (volume.prod volume)).restrict curvedStrip =
        Measure.map shear
          ((volume.prod volume).restrict (shear ⁻¹' curvedStrip)) :=
    Measure.restrict_map (measurable_shear) measurableSet_curvedStrip
  rw [shear_preimage_curvedStrip] at hrestrict
  rw [← hrestrict, shear_measurePreserving.map_eq, sheared_withDensity_eq]

/-- Machine-checked transport-density certificate for the triangular birth
move. -/
theorem shearedCertificate :
    TransportDensityCertificate (fun _ : Unit => planarAuxiliary)
      (volume.prod volume) shearedTransport shearedDensity where
  measurableTransport _ := measurable_shear.comp
    (planarCertificate.measurableTransport ())
  pushforward_eq _ := map_planarAuxiliary_sheared

noncomputable def reference : Measure State :=
  twoModelReference (Measure.dirac ()) (volume.prod volume)

instance reference.instSFinite : SFinite reference := by
  unfold reference
  infer_instance

/-- Half the target mass is on the empty model and half has the transported
curved-strip density on the planar model. -/
noncomputable def weight : State → ENNReal
  | Sum.inl _ => (2 : ENNReal)⁻¹
  | Sum.inr y => (2 : ENNReal)⁻¹ * shearedDensity () y

/-- Always propose the opposite model. Birth proposals use the certified
sheared density and death proposals return to the unique empty state. -/
noncomputable def proposalDensity : State → State → ENNReal
  | Sum.inl _, Sum.inr y => shearedDensity () y
  | Sum.inr _, Sum.inl _ => 1
  | _, _ => 0

theorem shearedDensity_ne_top (y : Plane) : shearedDensity () y ≠ ∞ := by
  unfold shearedDensity
  exact planarDensity_ne_top (unshear y)

theorem weight_ne_top (x : State) : weight x ≠ ∞ := by
  cases x with
  | inl x => simp [weight]
  | inr x => exact ENNReal.mul_ne_top (by norm_num) (shearedDensity_ne_top x)

theorem proposalDensity_ne_top (x y : State) : proposalDensity x y ≠ ∞ := by
  cases x <;> cases y <;> simp [proposalDensity, shearedDensity_ne_top]

theorem measurable_weight : Measurable weight := by
  apply Measurable.sumElim
  · exact measurable_const
  · exact measurable_const.mul measurable_shearedDensity_fixed

theorem measurable_uncurry_proposalDensity :
    Measurable (Function.uncurry proposalDensity) := by
  classical
  let rightValue : State → Plane := Sum.elim (fun _ => (0, 0)) id
  have hrightValue : Measurable rightValue :=
    measurable_const.sumElim measurable_id
  have hform : Function.uncurry proposalDensity = fun p =>
      if p.1 ∈ range (Sum.inl : Unit → State) ∧
          p.2 ∈ range (Sum.inr : Plane → State) then
        shearedDensity () (rightValue p.2)
      else if p.1 ∈ range (Sum.inr : Plane → State) ∧
          p.2 ∈ range (Sum.inl : Unit → State) then 1 else 0 := by
    funext p
    rcases p with ⟨x, y⟩
    cases x <;> cases y <;> simp [proposalDensity, rightValue]
  rw [hform]
  apply Measurable.ite
  · exact (measurableSet_range_inl.preimage measurable_fst).inter
      (measurableSet_range_inr.preimage measurable_snd)
  · exact measurable_shearedDensity_fixed.comp
      (hrightValue.comp measurable_snd)
  · apply Measurable.ite
    · exact (measurableSet_range_inr.preimage measurable_fst).inter
        (measurableSet_range_inl.preimage measurable_snd)
    · exact measurable_const
    · exact measurable_const

theorem proposalDensity_normalized (x : State) :
    ∫⁻ y, proposalDensity x y ∂reference = 1 := by
  cases x with
  | inl x =>
      simp only [reference, twoModelReference, lintegral_add_measure]
      have hmeas : Measurable (proposalDensity (Sum.inl x)) :=
        measurable_uncurry_proposalDensity.comp
          (measurable_const.prodMk measurable_id)
      rw [lintegral_map hmeas measurable_inl,
        lintegral_map hmeas measurable_inr]
      simp only [proposalDensity, lintegral_zero, zero_add]
      exact shearedCertificate.lintegral_crossDensity_eq_one
        (fun _ : Unit => planarAuxiliary) (volume.prod volume)
        shearedTransport shearedDensity x
  | inr x =>
      simp only [reference, twoModelReference, lintegral_add_measure]
      have hmeas : Measurable (proposalDensity (Sum.inr x)) :=
        measurable_uncurry_proposalDensity.comp
          (measurable_const.prodMk measurable_id)
      rw [lintegral_map hmeas measurable_inl,
        lintegral_map hmeas measurable_inr]
      simp [proposalDensity]

noncomputable def spec : ReversibleJumpSpec reference weight where
  proposalDensity := proposalDensity
  measurableProposal := measurable_uncurry_proposalDensity
  normalized := proposalDensity_normalized
  finiteFlow := by
    intro x y
    exact ENNReal.mul_ne_top (weight_ne_top x) (proposalDensity_ne_top x y)

/-- The triangular-Jacobian-corrected birth/death transition preserves the
tagged target. -/
theorem invariant :
    (reversibleJumpMetropolisHastings reference weight spec).Invariant
      (densityTarget reference weight) :=
  reversibleJumpMetropolisHastings_invariant reference weight measurable_weight spec

end Mcmc.Examples.ShearedBirthDeathReversibleJump
