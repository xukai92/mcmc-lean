import Mcmc.Examples.EuclideanBirthDeathReversibleJump

/-!
# A zero-to-two-dimensional reversible-jump client

This client births two independent auxiliary coordinates and transports
`(u₁,u₂) ↦ (2u₁,2u₂)`.  The source density `1/4` and inverse determinant
`|det(2I₂)|⁻¹ = 1/4` produce destination density `1/16` on the square.  The
product change-of-variables proof is then used in a complete tagged MH
invariance theorem.
-/

open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

namespace Mcmc.Examples.PlanarBirthDeathReversibleJump

open ProbabilityTheory Mcmc.Kernel
open Mcmc.Examples.EuclideanBirthDeathReversibleJump

abbrev Plane := ℝ × ℝ
abbrev State := Unit ⊕ Plane

/-- Two independent uniform auxiliary coordinates. -/
noncomputable def planarAuxiliary : Measure Plane :=
  birthAuxiliary.prod birthAuxiliary

instance birthAuxiliary.instIsProbabilityMeasure :
    IsProbabilityMeasure birthAuxiliary := by
  constructor
  unfold birthAuxiliary
  rw [Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Ioc]
  norm_num [ENNReal.smul_def]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

instance planarAuxiliary.instIsProbabilityMeasure :
    IsProbabilityMeasure planarAuxiliary := by
  unfold planarAuxiliary
  infer_instance

/-- Coordinatewise dimension-matching transport. -/
def planarTransport (_ : Unit) (u : Plane) : Plane := (2 * u.1, 2 * u.2)

/-- Product transported density, equal to `1/16` on `(-2,2]²`. -/
noncomputable def planarDensity (_ : Unit) (y : Plane) : ENNReal :=
  birthDensity () y.1 * birthDensity () y.2

theorem measurable_planarDensity :
    Measurable (Function.uncurry planarDensity) := by
  have hbirth : Measurable (birthDensity ()) := by
    unfold birthDensity
    exact Measurable.ite measurableSet_Ioc measurable_const measurable_const
  exact (hbirth.comp measurable_snd.fst).mul
    (hbirth.comp measurable_snd.snd)

theorem measurable_planarDensity_fixed : Measurable (planarDensity ()) := by
  have hbirth : Measurable (birthDensity ()) := by
    unfold birthDensity
    exact Measurable.ite measurableSet_Ioc measurable_const measurable_const
  exact (hbirth.comp measurable_fst).mul (hbirth.comp measurable_snd)

theorem map_planarAuxiliary :
    planarAuxiliary.map (planarTransport ()) =
      (volume.prod volume).withDensity (planarDensity ()) := by
  have hscale : Measurable (fun u : ℝ => 2 * u) := measurable_const_mul 2
  unfold planarAuxiliary
  rw [show planarTransport () = Prod.map (fun u : ℝ => 2 * u)
      (fun u : ℝ => 2 * u) by rfl]
  rw [← Measure.map_prod_map birthAuxiliary birthAuxiliary hscale hscale]
  change (birthAuxiliary.map (birthTransport ())).prod
      (birthAuxiliary.map (birthTransport ())) = _
  rw [map_birthAuxiliary]
  have hbirth : Measurable (birthDensity ()) := by
    unfold birthDensity
    exact Measurable.ite measurableSet_Ioc measurable_const measurable_const
  exact prod_withDensity hbirth hbirth

theorem planarCertificate :
    TransportDensityCertificate (fun _ : Unit => planarAuxiliary)
      (volume.prod volume) planarTransport planarDensity := by
  have hbirth : ∀ _ : Unit, Measurable (birthDensity ()) := fun _ => by
    unfold birthDensity
    exact Measurable.ite measurableSet_Ioc measurable_const measurable_const
  convert birthCertificate.prod birthCertificate hbirth hbirth using 1 <;>
    funext x <;> cases x <;> rfl

/-- Three-dimensional product transport, demonstrating that certified
Jacobian factors now scale compositionally beyond the handwritten planar
client. -/
abbrev Space3 := Plane × ℝ

noncomputable def spatialAuxiliary : Measure Space3 :=
  planarAuxiliary.prod birthAuxiliary

instance spatialAuxiliary.instIsProbabilityMeasure :
    IsProbabilityMeasure spatialAuxiliary := by
  unfold spatialAuxiliary
  infer_instance

def spatialTransport (_ : Unit) (u : Space3) : Space3 :=
  (planarTransport () u.1, birthTransport () u.2)

noncomputable def spatialDensity (_ : Unit) (y : Space3) : ENNReal :=
  planarDensity () y.1 * birthDensity () y.2

theorem spatialCertificate :
    TransportDensityCertificate (fun _ : Unit => spatialAuxiliary)
      ((volume.prod volume).prod volume) spatialTransport spatialDensity := by
  have hplanar : ∀ _ : Unit, Measurable (planarDensity ()) :=
    fun _ => measurable_planarDensity_fixed
  have hbirth : ∀ _ : Unit, Measurable (birthDensity ()) := fun _ => by
    unfold birthDensity
    exact Measurable.ite measurableSet_Ioc measurable_const measurable_const
  convert planarCertificate.prod birthCertificate hplanar hbirth using 1 <;>
    funext x <;> cases x <;> rfl

/-- The same one-coordinate scaling certificate generates a certified
transport in every finite nested product dimension. The existing planar and
spatial clients use convenient pair aliases; this theorem is the reusable
dimension-generic foundation for further clients. -/
theorem finiteScalingCertificate (dimension : ℕ) :
    TransportDensityCertificate
      (fun _ : Unit => transportPowerMeasure birthAuxiliary dimension)
      (transportPowerMeasure (volume : Measure ℝ) dimension)
      (fun _ => transportPowerMap (birthTransport ()) dimension)
      (fun _ => transportPowerDensity (birthDensity ()) dimension) := by
  apply birthCertificate.power birthAuxiliary (volume : Measure ℝ)
    (birthTransport ()) (birthDensity ())
  unfold birthDensity
  exact Measurable.ite measurableSet_Ioc measurable_const measurable_const

noncomputable def reference : Measure State :=
  twoModelReference (Measure.dirac ()) (volume.prod volume)

instance reference.instSFinite : SFinite reference := by
  unfold reference
  infer_instance

noncomputable def weight : State → ENNReal
  | Sum.inl _ => (2 : ENNReal)⁻¹
  | Sum.inr y => (2 : ENNReal)⁻¹ * planarDensity () y

noncomputable def proposalDensity : State → State → ENNReal
  | Sum.inl _, Sum.inr y => planarDensity () y
  | Sum.inr _, Sum.inl _ => 1
  | _, _ => 0

theorem planarDensity_ne_top (y : Plane) : planarDensity () y ≠ ∞ := by
  unfold planarDensity birthDensity
  split_ifs
  · exact ENNReal.mul_ne_top (by norm_num) (by norm_num)
  all_goals simp

theorem weight_ne_top (x : State) : weight x ≠ ∞ := by
  cases x with
  | inl x => simp [weight]
  | inr x => exact ENNReal.mul_ne_top (by norm_num) (planarDensity_ne_top x)

theorem proposalDensity_ne_top (x y : State) : proposalDensity x y ≠ ∞ := by
  cases x <;> cases y <;> simp [proposalDensity, planarDensity_ne_top]

theorem measurable_weight : Measurable weight := by
  apply Measurable.sumElim
  · exact measurable_const
  · exact measurable_const.mul measurable_planarDensity_fixed

theorem measurable_uncurry_proposalDensity :
    Measurable (Function.uncurry proposalDensity) := by
  classical
  let rightValue : State → Plane := Sum.elim (fun _ => (0, 0)) id
  have hrightValue : Measurable rightValue :=
    measurable_const.sumElim measurable_id
  have hform : Function.uncurry proposalDensity = fun p =>
      if p.1 ∈ range (Sum.inl : Unit → State) ∧
          p.2 ∈ range (Sum.inr : Plane → State) then
        planarDensity () (rightValue p.2)
      else if p.1 ∈ range (Sum.inr : Plane → State) ∧
          p.2 ∈ range (Sum.inl : Unit → State) then 1 else 0 := by
    funext p
    rcases p with ⟨x, y⟩
    cases x <;> cases y <;> simp [proposalDensity, rightValue]
  rw [hform]
  apply Measurable.ite
  · exact (measurableSet_range_inl.preimage measurable_fst).inter
      (measurableSet_range_inr.preimage measurable_snd)
  · exact measurable_planarDensity_fixed.comp
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
      exact planarCertificate.lintegral_crossDensity_eq_one
        (fun _ : Unit => planarAuxiliary) (volume.prod volume)
        planarTransport planarDensity x
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

/-- The determinant-corrected planar birth/death transition preserves its
tagged target. -/
theorem invariant :
    (reversibleJumpMetropolisHastings reference weight spec).Invariant
      (densityTarget reference weight) :=
  reversibleJumpMetropolisHastings_invariant reference weight measurable_weight spec

/-! ### Fully instantiated three-dimensional client -/

abbrev SpatialState := Sum Unit Space3

theorem measurable_spatialDensity_fixed : Measurable (spatialDensity ()) := by
  unfold spatialDensity
  exact measurable_planarDensity_fixed.comp measurable_fst |>.mul
    (by
      unfold birthDensity
      exact (Measurable.ite measurableSet_Ioc measurable_const
        measurable_const).comp measurable_snd)

theorem spatialDensity_ne_top (y : Space3) : spatialDensity () y ≠ ∞ := by
  unfold spatialDensity
  exact ENNReal.mul_ne_top (planarDensity_ne_top y.1) (by
    unfold birthDensity
    split_ifs <;> simp)

noncomputable def spatialReference : Measure SpatialState :=
  twoModelReference (Measure.dirac ()) ((volume.prod volume).prod volume)

instance spatialReference.instSFinite : SFinite spatialReference := by
  unfold spatialReference
  infer_instance

noncomputable def spatialWeight : SpatialState → ENNReal
  | Sum.inl _ => (2 : ENNReal)⁻¹
  | Sum.inr y => (2 : ENNReal)⁻¹ * spatialDensity () y

noncomputable def spatialProposalDensity : SpatialState → SpatialState → ENNReal
  | Sum.inl _, Sum.inr y => spatialDensity () y
  | Sum.inr _, Sum.inl _ => 1
  | _, _ => 0

theorem spatialWeight_ne_top (x : SpatialState) : spatialWeight x ≠ ∞ := by
  cases x with
  | inl x => simp [spatialWeight]
  | inr x => exact ENNReal.mul_ne_top (by norm_num) (spatialDensity_ne_top x)

theorem spatialProposalDensity_ne_top (x y : SpatialState) :
    spatialProposalDensity x y ≠ ∞ := by
  cases x <;> cases y <;> simp [spatialProposalDensity, spatialDensity_ne_top]

theorem measurable_spatialWeight : Measurable spatialWeight := by
  apply Measurable.sumElim
  · exact measurable_const
  · exact measurable_const.mul measurable_spatialDensity_fixed

theorem measurable_uncurry_spatialProposalDensity :
    Measurable (Function.uncurry spatialProposalDensity) := by
  classical
  let rightValue : SpatialState → Space3 := Sum.elim (fun _ => ((0, 0), 0)) id
  have hrightValue : Measurable rightValue :=
    measurable_const.sumElim measurable_id
  have hform : Function.uncurry spatialProposalDensity = fun p =>
      if p.1 ∈ range (Sum.inl : Unit → SpatialState) ∧
          p.2 ∈ range (Sum.inr : Space3 → SpatialState) then
        spatialDensity () (rightValue p.2)
      else if p.1 ∈ range (Sum.inr : Space3 → SpatialState) ∧
          p.2 ∈ range (Sum.inl : Unit → SpatialState) then 1 else 0 := by
    funext p
    rcases p with ⟨x, y⟩
    cases x <;> cases y <;> simp [spatialProposalDensity, rightValue]
  rw [hform]
  apply Measurable.ite
  · exact (measurableSet_range_inl.preimage measurable_fst).inter
      (measurableSet_range_inr.preimage measurable_snd)
  · exact measurable_spatialDensity_fixed.comp
      (hrightValue.comp measurable_snd)
  · apply Measurable.ite
    · exact (measurableSet_range_inr.preimage measurable_fst).inter
        (measurableSet_range_inl.preimage measurable_snd)
    · exact measurable_const
    · exact measurable_const

theorem spatialProposalDensity_normalized (x : SpatialState) :
    ∫⁻ y, spatialProposalDensity x y ∂spatialReference = 1 := by
  cases x with
  | inl x =>
      simp only [spatialReference, twoModelReference, lintegral_add_measure]
      have hmeas : Measurable (spatialProposalDensity (Sum.inl x)) :=
        measurable_uncurry_spatialProposalDensity.comp
          (measurable_const.prodMk measurable_id)
      rw [lintegral_map hmeas measurable_inl,
        lintegral_map hmeas measurable_inr]
      simp only [spatialProposalDensity, lintegral_zero, zero_add]
      exact spatialCertificate.lintegral_crossDensity_eq_one
        (fun _ : Unit => spatialAuxiliary) ((volume.prod volume).prod volume)
        spatialTransport spatialDensity x
  | inr x =>
      simp only [spatialReference, twoModelReference, lintegral_add_measure]
      have hmeas : Measurable (spatialProposalDensity (Sum.inr x)) :=
        measurable_uncurry_spatialProposalDensity.comp
          (measurable_const.prodMk measurable_id)
      rw [lintegral_map hmeas measurable_inl,
        lintegral_map hmeas measurable_inr]
      simp [spatialProposalDensity]

noncomputable def spatialSpec :
    ReversibleJumpSpec spatialReference spatialWeight where
  proposalDensity := spatialProposalDensity
  measurableProposal := measurable_uncurry_spatialProposalDensity
  normalized := spatialProposalDensity_normalized
  finiteFlow := by
    intro x y
    exact ENNReal.mul_ne_top (spatialWeight_ne_top x)
      (spatialProposalDensity_ne_top x y)

/-- Product-composed Jacobian certificates feed a complete three-dimensional
birth/death Metropolis--Hastings transition, not merely a normalized proposal. -/
theorem spatialInvariant :
    (reversibleJumpMetropolisHastings spatialReference spatialWeight
      spatialSpec).Invariant (densityTarget spatialReference spatialWeight) :=
  reversibleJumpMetropolisHastings_invariant spatialReference spatialWeight
    measurable_spatialWeight spatialSpec

end Mcmc.Examples.PlanarBirthDeathReversibleJump
