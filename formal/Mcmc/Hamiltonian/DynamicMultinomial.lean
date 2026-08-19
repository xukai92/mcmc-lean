import Mcmc.Hamiltonian.MultinomialHMC

/-!
# Multinomial selection from a dynamic trajectory subset

This module isolates the algebraic obligation behind dynamic multinomial
trajectory methods such as NUTS.  A Boolean candidate mask may depend on the
phase point and on the chosen trajectory origin.  It is safe for multinomial
selection when it retains the origin and, after rerooting at any admitted
candidate, exposes exactly the same mask.

The measure-level invariance theorem additionally needs measurability of the
mask.  The definitions and pointwise flow theorem here deliberately separate
that analytic obligation from the reroot algebra.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace Mcmc.Hamiltonian

variable {ι : Type*} [Fintype ι]

/-- A phase-dependent family of candidate subsets of an offset trajectory. -/
abbrev TrajectoryCandidateMask (ι : Type*) (L : ℕ) :=
  PhaseSpace ι → Fin (L + 1) → Fin (L + 1) → Bool

/-- Boltzmann weight restricted to admitted points of an actual leapfrog
trajectory. -/
noncomputable def dynamicTrajectoryWeight
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (mask : TrajectoryCandidateMask ι L)
    (z : PhaseSpace ι) (origin selected : Fin (L + 1)) : ℝ≥0∞ :=
  if mask z origin selected then
    boltzmannWeight potential
      (offsetLeapfrogTrajectory gradient ε origin z selected)
  else 0

/-- Sum of admitted Boltzmann weights. -/
noncomputable def dynamicTrajectoryNormalizer
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (mask : TrajectoryCandidateMask ι L)
    (z : PhaseSpace ι) (origin : Fin (L + 1)) : ℝ≥0∞ :=
  ∑ selected, dynamicTrajectoryWeight potential gradient ε mask z origin selected

theorem dynamicTrajectoryNormalizer_ne_zero
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (mask : TrajectoryCandidateMask ι L)
    (hroot : ∀ z origin, mask z origin origin = true)
    (z : PhaseSpace ι) (origin : Fin (L + 1)) :
    dynamicTrajectoryNormalizer potential gradient ε mask z origin ≠ 0 := by
  apply ne_of_gt
  have horigin : dynamicTrajectoryWeight potential gradient ε mask z origin origin =
      boltzmannWeight potential
        (offsetLeapfrogTrajectory gradient ε origin z origin) := by
    simp [dynamicTrajectoryWeight, hroot z origin]
  refine lt_of_lt_of_le
    (bot_lt_iff_ne_bot.mpr
      (boltzmannWeight_ne_zero potential
        (offsetLeapfrogTrajectory gradient ε origin z origin))) ?_
  rw [← horigin]
  exact Finset.single_le_sum
    (s := Finset.univ)
    (f := fun selected =>
      dynamicTrajectoryWeight potential gradient ε mask z origin selected)
    (fun i hi => bot_le) (Finset.mem_univ origin)

theorem dynamicTrajectoryNormalizer_ne_top
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (mask : TrajectoryCandidateMask ι L)
    (z : PhaseSpace ι) (origin : Fin (L + 1)) :
    dynamicTrajectoryNormalizer potential gradient ε mask z origin ≠ ∞ := by
  unfold dynamicTrajectoryNormalizer
  apply (ENNReal.sum_lt_top.mpr ?_).ne
  intro selected hselected
  exact by
    unfold dynamicTrajectoryWeight
    split
    · exact (boltzmannWeight_ne_top potential
        (offsetLeapfrogTrajectory gradient ε origin z selected)).lt_top
    · simp

/-- Multinomial selection normalized over a root-retaining dynamic subset. -/
noncomputable def dynamicTrajectoryIndexPMF
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (mask : TrajectoryCandidateMask ι L)
    (hroot : ∀ z origin, mask z origin origin = true)
    (z : PhaseSpace ι) (origin : Fin (L + 1)) : PMF (Fin (L + 1)) :=
  PMF.normalize
    (dynamicTrajectoryWeight potential gradient ε mask z origin)
    (by
      rw [tsum_fintype]
      exact dynamicTrajectoryNormalizer_ne_zero potential gradient ε mask hroot z origin)
    (by
      rw [tsum_fintype]
      exact dynamicTrajectoryNormalizer_ne_top potential gradient ε mask z origin)

@[simp]
theorem dynamicTrajectoryIndexPMF_apply
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (mask : TrajectoryCandidateMask ι L)
    (hroot : ∀ z origin, mask z origin origin = true)
    (z : PhaseSpace ι) (origin selected : Fin (L + 1)) :
    dynamicTrajectoryIndexPMF potential gradient ε mask hroot z origin selected =
      dynamicTrajectoryWeight potential gradient ε mask z origin selected *
        (dynamicTrajectoryNormalizer potential gradient ε mask z origin)⁻¹ := by
  simp [dynamicTrajectoryIndexPMF, dynamicTrajectoryNormalizer]

/-- Rerooting at an admitted candidate preserves the masked normalizer when
the complete candidate row is reroot invariant. -/
theorem dynamicTrajectoryNormalizer_reroot
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (mask : TrajectoryCandidateMask ι L)
    (hreroot : ∀ z origin selected, mask z origin selected = true →
      ∀ i, mask (offsetLeapfrogTrajectory gradient ε origin z selected) selected i =
        mask z origin i)
    (z : PhaseSpace ι) (origin selected : Fin (L + 1))
    (hselected : mask z origin selected = true) :
    dynamicTrajectoryNormalizer potential gradient ε mask
        (offsetLeapfrogTrajectory gradient ε origin z selected) selected =
      dynamicTrajectoryNormalizer potential gradient ε mask z origin := by
  unfold dynamicTrajectoryNormalizer dynamicTrajectoryWeight
  apply Finset.sum_congr rfl
  intro i hi
  rw [hreroot z origin selected hselected i]
  rw [offsetLeapfrogTrajectory_reroot]

/-- Target-weighted dynamic multinomial flow is symmetric after rerooting at
an admitted candidate. -/
theorem boltzmann_dynamicTrajectoryIndexPMF_flow_reroot
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (mask : TrajectoryCandidateMask ι L)
    (hroot : ∀ z origin, mask z origin origin = true)
    (hreroot : ∀ z origin selected, mask z origin selected = true →
      ∀ i, mask (offsetLeapfrogTrajectory gradient ε origin z selected) selected i =
        mask z origin i)
    (hpair : ∀ z origin selected,
      mask (offsetLeapfrogTrajectory gradient ε origin z selected) selected origin =
        mask z origin selected)
    (z : PhaseSpace ι) (origin selected : Fin (L + 1)) :
    boltzmannWeight potential z *
        dynamicTrajectoryIndexPMF potential gradient ε mask hroot z origin selected =
      boltzmannWeight potential
          (offsetLeapfrogTrajectory gradient ε origin z selected) *
        dynamicTrajectoryIndexPMF potential gradient ε mask hroot
          (offsetLeapfrogTrajectory gradient ε origin z selected) selected origin := by
  by_cases hselected : mask z origin selected = true
  · rw [dynamicTrajectoryIndexPMF_apply, dynamicTrajectoryIndexPMF_apply]
    rw [dynamicTrajectoryNormalizer_reroot potential gradient ε mask hreroot
      z origin selected hselected]
    simp only [dynamicTrajectoryWeight, hselected, if_true]
    rw [hpair z origin selected, hselected]
    simp only [if_true]
    rw [offsetLeapfrogTrajectory_reroot, offsetLeapfrogTrajectory_origin]
    ac_rfl
  · have hforward : mask z origin selected = false := Bool.eq_false_of_not_eq_true hselected
    have hreverse :
        mask (offsetLeapfrogTrajectory gradient ε origin z selected) selected origin = false := by
      rw [hpair z origin selected]
      exact hforward
    rw [dynamicTrajectoryIndexPMF_apply, dynamicTrajectoryIndexPMF_apply]
    simp [dynamicTrajectoryWeight, hforward, hreverse]

end Mcmc.Hamiltonian
