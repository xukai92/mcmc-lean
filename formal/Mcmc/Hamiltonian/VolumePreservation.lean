import Mcmc.Hamiltonian.RandomizedTrajectory
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Volume preservation of leapfrog integration

The leapfrog map is a composition of two triangular shears: a momentum kick
at fixed position and a position drift at fixed momentum. Translation
invariance of finite-dimensional Lebesgue measure makes each shear preserve
product phase-space volume. Consequently one leapfrog step, every natural
iterate, and every signed iterate preserve volume.

This argument only requires measurability of the supplied gradient. The
separate claim that it is the derivative of a potential is needed for
Hamiltonian approximation bounds, not for volume preservation.
-/

open MeasureTheory

namespace Mcmc.Hamiltonian

variable {ι : Type*} [Fintype ι]

/-- A bijective differentiable map with unit absolute Jacobian determinant
preserves any finite-dimensional additive Haar measure. This packages the
change-of-variables step needed when volume preservation is established by a
Jacobian calculation rather than by shear decomposition. -/
theorem measurePreserving_of_bijective_differentiable_abs_det_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (f : E → E) (hf : Differentiable ℝ f) (hbijective : Function.Bijective f)
    (hdet : ∀ x, |(fderiv ℝ f x).det| = 1) :
    MeasurePreserving f μ μ := by
  have hmeasurable : Measurable f := hf.continuous.measurable
  refine ⟨hmeasurable, ?_⟩
  ext s hs
  rw [Measure.map_apply hmeasurable hs]
  let t := f ⁻¹' s
  have ht : MeasurableSet t := hs.preimage hmeasurable
  have hformula := lintegral_abs_det_fderiv_eq_addHaar_image
    (μ := μ) (f := f) (f' := fun x => fderiv ℝ f x) ht
    (fun x _ => (hf x).hasFDerivAt.hasFDerivWithinAt)
    hbijective.injective.injOn
  have himage : f '' t = s := Set.image_preimage_eq s hbijective.surjective
  rw [himage] at hformula
  simpa [t, hdet] using hformula

/-- Product Lebesgue measure on position-momentum phase space. -/
noncomputable def phaseVolume : Measure (PhaseSpace ι) :=
  (volume : Measure (Position ι)).prod (volume : Measure (Momentum ι))

theorem phaseVolume_eq_volume :
    phaseVolume (ι := ι) = (volume : Measure (PhaseSpace ι)) := by
  exact (Measure.volume_eq_prod (Position ι) (Momentum ι)).symm

/-- Negating momentum while retaining position preserves product phase-space
Lebesgue measure. -/
theorem measurePreserving_momentumFlip :
    MeasurePreserving (momentumFlip : PhaseSpace ι → PhaseSpace ι)
      phaseVolume phaseVolume := by
  unfold momentumFlip phaseVolume
  have hneg : MeasurePreserving (fun p : Momentum ι => -p)
      (volume : Measure (Momentum ι)) volume := by
    refine ⟨measurable_neg, ?_⟩
    simpa [abs_pow] using
      (Measure.map_addHaar_smul (volume : Measure (Momentum ι))
        (r := (-1 : ℝ)) (by norm_num))
  exact (MeasurePreserving.id (volume : Measure (Position ι))).prod
    hneg

/-- Momentum half-kick as a map of the full phase space. -/
noncomputable def kickPhase (gradient : Position ι → Position ι) (ε : ℝ)
    (z : PhaseSpace ι) : PhaseSpace ι :=
  (z.1, halfKick gradient ε z.1 z.2)

/-- Position drift as a map of the full phase space. -/
def driftPhase (ε : ℝ) (z : PhaseSpace ι) : PhaseSpace ι :=
  (drift ε z.1 z.2, z.2)

omit [Fintype ι] in
theorem measurable_kickPhase
    {gradient : Position ι → Position ι} (hgradient : Measurable gradient)
    (ε : ℝ) : Measurable (kickPhase gradient ε) := by
  unfold kickPhase halfKick
  fun_prop

omit [Fintype ι] in
theorem measurable_driftPhase (ε : ℝ) :
    Measurable (driftPhase (ι := ι) ε) := by
  unfold driftPhase drift
  fun_prop

/-- A momentum kick is a translation in each position fiber and therefore
preserves product Lebesgue measure. -/
theorem measurePreserving_kickPhase
    {gradient : Position ι → Position ι} (hgradient : Measurable gradient)
    (ε : ℝ) :
    MeasurePreserving (kickPhase gradient ε) phaseVolume phaseVolume := by
  unfold kickPhase phaseVolume
  apply (MeasurePreserving.id (volume : Measure (Position ι))).skew_product
  · exact measurable_halfKick hgradient ε
  · apply ae_of_all
    intro q
    change Measure.map (fun p => p - (ε / 2) • gradient q) volume = volume
    simpa only [sub_eq_add_neg] using
      map_add_right_eq_self (volume : Measure (Momentum ι))
        (-((ε / 2) • gradient q))

/-- A position drift is a translation in each momentum fiber and therefore
preserves product Lebesgue measure. -/
theorem measurePreserving_driftPhase (ε : ℝ) :
    MeasurePreserving (driftPhase (ι := ι) ε) phaseVolume phaseVolume := by
  let shear : Momentum ι × Position ι → Momentum ι × Position ι :=
    fun z => (z.1, z.2 + ε • z.1)
  have hshear : MeasurePreserving shear
      ((volume : Measure (Momentum ι)).prod (volume : Measure (Position ι)))
      ((volume : Measure (Momentum ι)).prod (volume : Measure (Position ι))) := by
    simpa only [shear, id_eq] using
      (MeasurePreserving.id (volume : Measure (Momentum ι))).skew_product
        (g := fun p q => q + ε • p) (by fun_prop)
        (ae_of_all _ fun p =>
          map_add_right_eq_self (volume : Measure (Position ι)) (ε • p))
  have hswapForward : MeasurePreserving
      (Prod.swap : PhaseSpace ι → Momentum ι × Position ι)
      phaseVolume
      ((volume : Measure (Momentum ι)).prod (volume : Measure (Position ι))) := by
    exact Measure.measurePreserving_swap
  have hswapBackward : MeasurePreserving
      (Prod.swap : Momentum ι × Position ι → PhaseSpace ι)
      ((volume : Measure (Momentum ι)).prod (volume : Measure (Position ι)))
      phaseVolume := by
    exact Measure.measurePreserving_swap
  have h := hswapBackward.comp (hshear.comp hswapForward)
  change MeasurePreserving (driftPhase (ι := ι) ε) phaseVolume phaseVolume
  apply h.congr (measurable_driftPhase ε)
  filter_upwards [] with z
  ext i <;> rfl

omit [Fintype ι] in
/-- Leapfrog is exactly kick--drift--kick. -/
theorem leapfrog_eq_kickPhase_comp_driftPhase_comp_kickPhase
    (gradient : Position ι → Position ι) (ε : ℝ) :
    leapfrog gradient ε =
      kickPhase gradient ε ∘ driftPhase ε ∘ kickPhase gradient ε := by
  funext z
  rfl

/-- One leapfrog step preserves phase-space Lebesgue measure. -/
theorem measurePreserving_leapfrog
    {gradient : Position ι → Position ι} (hgradient : Measurable gradient)
    (ε : ℝ) :
    MeasurePreserving (leapfrog gradient ε) phaseVolume phaseVolume := by
  rw [leapfrog_eq_kickPhase_comp_driftPhase_comp_kickPhase]
  exact (measurePreserving_kickPhase hgradient ε).comp
    ((measurePreserving_driftPhase ε).comp
      (measurePreserving_kickPhase hgradient ε))

/-- Every finite leapfrog iterate preserves phase-space volume. -/
theorem measurePreserving_leapfrogN
    {gradient : Position ι → Position ι} (hgradient : Measurable gradient)
    (ε : ℝ) (n : ℕ) :
    MeasurePreserving (leapfrogN gradient ε n) phaseVolume phaseVolume := by
  change MeasurePreserving ((leapfrog gradient ε)^[n]) phaseVolume phaseVolume
  exact (measurePreserving_leapfrog hgradient ε).iterate n

/-- Every signed leapfrog iterate preserves phase-space volume. -/
theorem measurePreserving_signedLeapfrog
    {gradient : Position ι → Position ι} (hgradient : Measurable gradient)
    (ε : ℝ) (n : ℤ) :
    MeasurePreserving (signedLeapfrog gradient ε n) phaseVolume phaseVolume := by
  cases n with
  | ofNat n =>
      change MeasurePreserving (fun z => ((leapfrogPerm gradient ε) ^ n) z)
        phaseVolume phaseVolume
      simpa only [Equiv.Perm.coe_pow, coe_leapfrogPerm] using
        (measurePreserving_leapfrog hgradient ε).iterate n
  | negSucc n =>
      change MeasurePreserving
        (fun z => (((leapfrogPerm gradient ε) ^ (n + 1))⁻¹) z)
        phaseVolume phaseVolume
      rw [← inv_pow]
      simpa only [Equiv.Perm.coe_pow, coe_leapfrogPerm_inv] using
        (measurePreserving_leapfrog hgradient (-ε)).iterate (n + 1)

/-- Every coordinate of every offset trajectory is a volume-preserving map of
the initial phase point. -/
theorem measurePreserving_offsetLeapfrogTrajectory
    {gradient : Position ι → Position ι} (hgradient : Measurable gradient)
    (ε : ℝ) {L : ℕ} (origin i : Fin (L + 1)) :
    MeasurePreserving
      (fun z => offsetLeapfrogTrajectory gradient ε origin z i)
      phaseVolume phaseVolume :=
  measurePreserving_signedLeapfrog hgradient ε
    ((i.val : ℤ) - (origin.val : ℤ))

end Mcmc.Hamiltonian
