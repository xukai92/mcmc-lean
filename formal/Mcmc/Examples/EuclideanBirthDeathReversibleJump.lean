import Mcmc.Kernel.ReversibleJump
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# A dimension-changing Euclidean reversible-jump client

This example moves between a zero-dimensional model and a one-dimensional
real model.  A birth move draws `u` uniformly on `(-1, 1]` and applies the
transport `y = 2u`.  Lean checks that the pushforward density is `1/4` on
`(-2, 2]`: the source density `1/2` is multiplied by the inverse-Jacobian
factor `1/2`.  The reverse death move forgets the real coordinate.
-/

open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

namespace Mcmc.Examples.EuclideanBirthDeathReversibleJump

open ProbabilityTheory Mcmc.Kernel

abbrev State := Unit ⊕ ℝ

/-- Uniform auxiliary probability measure on `(-1, 1]`. -/
noncomputable def birthAuxiliary : Measure ℝ :=
  (2 : ENNReal)⁻¹ • volume.restrict (Ioc (-1) 1)

/-- The dimension-matching birth transport. -/
def birthTransport (_ : Unit) (u : ℝ) : ℝ := 2 * u

/-- Pushforward density after `y = 2u`; `1/4 = (1/2) · |2|⁻¹`. -/
noncomputable def birthDensity (_ : Unit) (y : ℝ) : ENNReal :=
  if y ∈ Ioc (-2) 2 then (4 : ENNReal)⁻¹ else 0

theorem measurable_birthDensity :
    Measurable (Function.uncurry birthDensity) := by
  apply Measurable.ite
  · exact measurableSet_Ioc.preimage measurable_snd
  · exact measurable_const
  · exact measurable_const

theorem map_birthAuxiliary :
    birthAuxiliary.map (birthTransport ()) =
      volume.withDensity (birthDensity ()) := by
  have hpreimage : (fun u : ℝ => 2 * u) ⁻¹' Ioc (-2) 2 = Ioc (-1) 1 := by
    ext u
    simp only [mem_preimage, mem_Ioc]
    constructor <;> intro h <;> constructor <;> linarith
  have hrestrict :
      (Measure.map (fun u : ℝ => 2 * u) volume).restrict (Ioc (-2) 2) =
        Measure.map (fun u : ℝ => 2 * u)
          (volume.restrict ((fun u : ℝ => 2 * u) ⁻¹' Ioc (-2) 2)) :=
    Measure.restrict_map (μ := (volume : Measure ℝ))
      (measurable_const_mul 2) measurableSet_Ioc
  rw [hpreimage] at hrestrict
  unfold birthAuxiliary birthTransport birthDensity
  rw [Measure.map_smul, ← hrestrict, Real.map_volume_mul_left (by norm_num : (2 : ℝ) ≠ 0),
    Measure.restrict_smul]
  rw [show (fun y : ℝ => if y ∈ Ioc (-2) 2 then (4 : ENNReal)⁻¹ else 0) =
      (Ioc (-2) 2).indicator (fun _ => (4 : ENNReal)⁻¹) by
    funext y
    by_cases hy : y ∈ Ioc (-2) 2 <;> simp [hy]]
  rw [withDensity_indicator measurableSet_Ioc, withDensity_const]
  rw [smul_smul]
  congr 1
  simp only [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2⁻¹)]
  rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
  have htwo : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  rw [htwo]
  rw [← pow_two]
  have hfour : (4 : ENNReal) = (2 : ENNReal) ^ 2 := by norm_num
  rw [hfour]
  exact ENNReal.inv_pow.symm

/-- Machine-checked transport/Jacobian certificate for the birth move. -/
theorem birthCertificate :
    TransportDensityCertificate (fun _ : Unit => birthAuxiliary) volume
      birthTransport birthDensity where
  measurableTransport _ := measurable_const_mul 2
  pushforward_eq _ := map_birthAuxiliary

/-- Tagged reference: counting mass for the zero-dimensional model and
Lebesgue measure for the scalar model. -/
noncomputable def reference : Measure State :=
  twoModelReference (Measure.dirac ()) volume

instance reference.instSFinite : SFinite reference := by
  unfold reference
  infer_instance

/-- A normalized target with half its mass on the empty model and half
uniformly spread over the scalar interval `(-2, 2]`. -/
noncomputable def weight : State → ENNReal
  | Sum.inl _ => (2 : ENNReal)⁻¹
  | Sum.inr y => if y ∈ Ioc (-2) 2 then (8 : ENNReal)⁻¹ else 0

/-- Always propose a birth or death.  Births use the certified transported
density; deaths return to the unique zero-dimensional state. -/
noncomputable def proposalDensity : State → State → ENNReal
  | Sum.inl _, Sum.inr y => birthDensity () y
  | Sum.inr _, Sum.inl _ => 1
  | _, _ => 0

theorem measurable_weight : Measurable weight := by
  apply Measurable.sumElim
  · exact measurable_const
  · apply Measurable.ite measurableSet_Ioc measurable_const measurable_const

theorem measurable_uncurry_proposalDensity :
    Measurable (Function.uncurry proposalDensity) := by
  classical
  let rightValue : State → ℝ := Sum.elim (fun _ => 0) id
  have hrightValue : Measurable rightValue :=
    measurable_const.sumElim measurable_id
  have hform : Function.uncurry proposalDensity = fun p =>
      if p.1 ∈ range (Sum.inl : Unit → State) ∧
          p.2 ∈ range (Sum.inr : ℝ → State) then
        birthDensity () (rightValue p.2)
      else if p.1 ∈ range (Sum.inr : ℝ → State) ∧
          p.2 ∈ range (Sum.inl : Unit → State) then 1 else 0 := by
    funext p
    rcases p with ⟨x, y⟩
    cases x <;> cases y <;> simp [proposalDensity, rightValue]
  rw [hform]
  apply Measurable.ite
  · exact (measurableSet_range_inl.preimage measurable_fst).inter
      (measurableSet_range_inr.preimage measurable_snd)
  · exact (show Measurable (birthDensity ()) from by
      apply Measurable.ite measurableSet_Ioc measurable_const measurable_const).comp
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
      have hmeas : Measurable (proposalDensity (Sum.inl x)) := by
        change Measurable (fun y =>
          Function.uncurry proposalDensity (Sum.inl x, y))
        exact measurable_uncurry_proposalDensity.comp
          (measurable_const.prodMk measurable_id)
      rw [lintegral_map hmeas measurable_inl,
        lintegral_map hmeas measurable_inr]
      simp only [proposalDensity, lintegral_zero, zero_add]
      rw [show birthDensity x = (Ioc (-2) 2).indicator
          (fun _ => (4 : ENNReal)⁻¹) by
        funext y
        by_cases hy : y ∈ Ioc (-2) 2 <;> simp [birthDensity, hy],
        lintegral_indicator measurableSet_Ioc, lintegral_const,
        Measure.restrict_apply_univ, Real.volume_Ioc]
      have hlength : ENNReal.ofReal ((2 : ℝ) - -2) = 4 := by norm_num
      rw [hlength]
      exact ENNReal.inv_mul_cancel
        (show (4 : ENNReal) ≠ 0 by norm_num)
        (show (4 : ENNReal) ≠ ∞ by norm_num)
  | inr x =>
      simp only [reference, twoModelReference, lintegral_add_measure]
      have hmeas : Measurable (proposalDensity (Sum.inr x)) := by
        change Measurable (fun y =>
          Function.uncurry proposalDensity (Sum.inr x, y))
        exact measurable_uncurry_proposalDensity.comp
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
    cases x <;> cases y <;>
      simp only [forwardDensityFlow, weight, proposalDensity, birthDensity]
    all_goals
      apply ENNReal.mul_ne_top
      · aesop
      · aesop

/-- The Jacobian-certified birth/death reversible-jump transition preserves
the tagged target.  Periodicity and convergence are deliberately not claimed. -/
theorem invariant :
    (reversibleJumpMetropolisHastings reference weight spec).Invariant
      (densityTarget reference weight) :=
  reversibleJumpMetropolisHastings_invariant reference weight measurable_weight spec

end Mcmc.Examples.EuclideanBirthDeathReversibleJump
