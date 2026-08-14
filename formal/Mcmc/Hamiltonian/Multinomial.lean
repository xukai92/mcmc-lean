import Mcmc.Hamiltonian.Leapfrog
import Mcmc.Finite.Coupling
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.Complex.Exponential

/-!
# Multinomial selection along Hamiltonian trajectories

This module defines the categorical selection law used by multinomial HMC.
For a nonempty trajectory indexed by `Fin (L + 1)`, the index at phase point
`zᵢ` receives Boltzmann weight `exp (-H(zᵢ))`.  The weights are finite and
strictly positive, so their normalization is a probability mass function
without a fallback case.

The construction is also packaged as a measurable Markov kernel when the
finite family of trajectory points depends measurably on an input.  Mapping
that index kernel through an input-dependent trajectory is developed in the
next layer; ordinary `Kernel.map` is not sufficient for that dependent map.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace Mcmc.Hamiltonian

variable {ι α : Type*} [Fintype ι]

/-- Unnormalized Boltzmann weight `exp (-H(z))`, represented in `ℝ≥0∞`. -/
noncomputable def boltzmannWeight (potential : Position ι → ℝ)
    (z : PhaseSpace ι) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-energy potential z))

@[simp]
theorem boltzmannWeight_ne_zero (potential : Position ι → ℝ)
    (z : PhaseSpace ι) : boltzmannWeight potential z ≠ 0 := by
  simp [boltzmannWeight, Real.exp_pos]

@[simp]
theorem boltzmannWeight_ne_top (potential : Position ι → ℝ)
    (z : PhaseSpace ι) : boltzmannWeight potential z ≠ ∞ := by
  simp [boltzmannWeight]

theorem measurable_boltzmannWeight {potential : Position ι → ℝ}
    (hpotential : Measurable potential) :
    Measurable (boltzmannWeight potential : PhaseSpace ι → ℝ≥0∞) := by
  exact ENNReal.measurable_ofReal.comp
    ((measurable_energy hpotential).neg.exp)

/-- Sum of the Boltzmann weights on a finite nonempty trajectory. -/
noncomputable def trajectoryNormalizer (potential : Position ι → ℝ) {L : ℕ}
    (trajectory : Fin (L + 1) → PhaseSpace ι) : ℝ≥0∞ :=
  ∑ i, boltzmannWeight potential (trajectory i)

theorem trajectoryNormalizer_ne_zero (potential : Position ι → ℝ) {L : ℕ}
    (trajectory : Fin (L + 1) → PhaseSpace ι) :
    trajectoryNormalizer potential trajectory ≠ 0 := by
  apply ne_of_gt
  refine lt_of_lt_of_le
    (bot_lt_iff_ne_bot.mpr
      (boltzmannWeight_ne_zero potential (trajectory (0 : Fin (L + 1))))) ?_
  exact Finset.single_le_sum
    (s := Finset.univ)
    (f := fun i : Fin (L + 1) => boltzmannWeight potential (trajectory i))
    (fun i hi => bot_le) (Finset.mem_univ (0 : Fin (L + 1)))

theorem trajectoryNormalizer_ne_top (potential : Position ι → ℝ) {L : ℕ}
    (trajectory : Fin (L + 1) → PhaseSpace ι) :
    trajectoryNormalizer potential trajectory ≠ ∞ := by
  simp [trajectoryNormalizer]

/-- The multinomial-HMC categorical law on trajectory indices. -/
noncomputable def trajectoryIndexPMF (potential : Position ι → ℝ) {L : ℕ}
    (trajectory : Fin (L + 1) → PhaseSpace ι) : PMF (Fin (L + 1)) :=
  PMF.normalize (fun i => boltzmannWeight potential (trajectory i))
    (by
      rw [tsum_fintype]
      exact trajectoryNormalizer_ne_zero potential trajectory)
    (by
      rw [tsum_fintype]
      exact trajectoryNormalizer_ne_top potential trajectory)

@[simp]
theorem trajectoryIndexPMF_apply (potential : Position ι → ℝ) {L : ℕ}
    (trajectory : Fin (L + 1) → PhaseSpace ι) (i : Fin (L + 1)) :
    trajectoryIndexPMF potential trajectory i =
      boltzmannWeight potential (trajectory i) *
        (trajectoryNormalizer potential trajectory)⁻¹ := by
  simp [trajectoryIndexPMF, trajectoryNormalizer]

theorem trajectoryIndexPMF_apply_ne_zero (potential : Position ι → ℝ) {L : ℕ}
    (trajectory : Fin (L + 1) → PhaseSpace ι) (i : Fin (L + 1)) :
    trajectoryIndexPMF potential trajectory i ≠ 0 := by
  simp [trajectoryIndexPMF_apply, trajectoryNormalizer_ne_top]

/-- A one-sided energy discrepancy gives multiplicative domination of the
corresponding unnormalized Boltzmann weights. -/
theorem boltzmannWeight_le_exp_mul_of_energy_sub_le
    (potential : Position ι → ℝ) (z₁ z₂ : PhaseSpace ι) {r : ℝ}
    (h : energy potential z₂ - energy potential z₁ ≤ r) :
    boltzmannWeight potential z₁ ≤
      ENNReal.ofReal (Real.exp r) * boltzmannWeight potential z₂ := by
  unfold boltzmannWeight
  rw [← ENNReal.ofReal_mul (Real.exp_pos r).le]
  apply ENNReal.ofReal_le_ofReal
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-- The probability of one trajectory index is at most the Boltzmann-weight
ratio against any comparison index. Equivalently, it is bounded by the
exponential of their energy difference. -/
theorem trajectoryIndexPMF_le_exp_energy_sub
    (potential : Position ι → ℝ) {L : ℕ}
    (trajectory : Fin (L + 1) → PhaseSpace ι)
    (i j : Fin (L + 1)) :
    trajectoryIndexPMF potential trajectory i ≤
      ENNReal.ofReal (Real.exp
        (energy potential (trajectory j) - energy potential (trajectory i))) := by
  let wi := boltzmannWeight potential (trajectory i)
  let wj := boltzmannWeight potential (trajectory j)
  let N := trajectoryNormalizer potential trajectory
  let c := ENNReal.ofReal (Real.exp
    (energy potential (trajectory j) - energy potential (trajectory i)))
  have hwjN : wj ≤ N := by
    dsimp only [wj, N, trajectoryNormalizer]
    exact Finset.single_le_sum
      (s := Finset.univ)
      (f := fun k : Fin (L + 1) ↦ boltzmannWeight potential (trajectory k))
      (fun _ _ ↦ bot_le) (Finset.mem_univ j)
  have hweight : wi ≤ c * wj := by
    exact boltzmannWeight_le_exp_mul_of_energy_sub_le potential _ _ le_rfl
  have hwj0 : wj ≠ 0 := boltzmannWeight_ne_zero potential _
  have hwjTop : wj ≠ ⊤ := boltzmannWeight_ne_top potential _
  rw [trajectoryIndexPMF_apply]
  change wi * N⁻¹ ≤ c
  calc
    wi * N⁻¹ ≤ wi * wj⁻¹ := by gcongr
    _ ≤ (c * wj) * wj⁻¹ := by gcongr
    _ = c := by
      rw [mul_assoc, ENNReal.mul_inv_cancel hwj0 hwjTop, mul_one]

/-- Uniform one-sided energy discrepancy controls the ratio of trajectory
normalizers. -/
theorem trajectoryNormalizer_le_exp_mul_of_energy_sub_le
    (potential : Position ι → ℝ) {L : ℕ}
    (trajectory₁ trajectory₂ : Fin (L + 1) → PhaseSpace ι) {r : ℝ}
    (h : ∀ i, energy potential (trajectory₂ i) -
      energy potential (trajectory₁ i) ≤ r) :
    trajectoryNormalizer potential trajectory₁ ≤
      ENNReal.ofReal (Real.exp r) *
        trajectoryNormalizer potential trajectory₂ := by
  unfold trajectoryNormalizer
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi =>
    boltzmannWeight_le_exp_mul_of_energy_sub_le potential _ _ (h i)

/-- If both directional energy discrepancies are at most `r`, normalized
trajectory probabilities are dominated by the square of the raw Boltzmann
ratio factor. One factor controls an atom and the other its normalizer. -/
theorem trajectoryIndexPMF_le_exp_sq_mul_of_energy_sub_le
    (potential : Position ι → ℝ) {L : ℕ}
    (trajectory₁ trajectory₂ : Fin (L + 1) → PhaseSpace ι) {r : ℝ}
    (h₁₂ : ∀ i, energy potential (trajectory₂ i) -
      energy potential (trajectory₁ i) ≤ r)
    (h₂₁ : ∀ i, energy potential (trajectory₁ i) -
      energy potential (trajectory₂ i) ≤ r) (i : Fin (L + 1)) :
    trajectoryIndexPMF potential trajectory₁ i ≤
      (ENNReal.ofReal (Real.exp r)) ^ 2 *
        trajectoryIndexPMF potential trajectory₂ i := by
  let c : ENNReal := ENNReal.ofReal (Real.exp r)
  let N₁ := trajectoryNormalizer potential trajectory₁
  let N₂ := trajectoryNormalizer potential trajectory₂
  have hN₁0 : N₁ ≠ 0 := trajectoryNormalizer_ne_zero potential trajectory₁
  have hN₁top : N₁ ≠ ∞ := trajectoryNormalizer_ne_top potential trajectory₁
  have hN₂0 : N₂ ≠ 0 := trajectoryNormalizer_ne_zero potential trajectory₂
  have hN₂top : N₂ ≠ ∞ := trajectoryNormalizer_ne_top potential trajectory₂
  have hnormalizer : N₂ ≤ c * N₁ :=
    trajectoryNormalizer_le_exp_mul_of_energy_sub_le potential
      trajectory₂ trajectory₁ h₂₁
  have hinv : N₁⁻¹ ≤ c * N₂⁻¹ := by
    calc
      N₁⁻¹ = (N₁⁻¹ * N₂⁻¹) * N₂ := by
        rw [mul_assoc, ENNReal.inv_mul_cancel hN₂0 hN₂top, mul_one]
      _ ≤ (N₁⁻¹ * N₂⁻¹) * (c * N₁) :=
        mul_le_mul_right hnormalizer _
      _ = c * N₂⁻¹ := by
        rw [show (N₁⁻¹ * N₂⁻¹) * (c * N₁) =
          c * (N₁⁻¹ * N₁) * N₂⁻¹ by ac_rfl,
          ENNReal.inv_mul_cancel hN₁0 hN₁top, mul_one]
  have hweight : boltzmannWeight potential (trajectory₁ i) ≤
      c * boltzmannWeight potential (trajectory₂ i) :=
    boltzmannWeight_le_exp_mul_of_energy_sub_le potential _ _ (h₁₂ i)
  rw [trajectoryIndexPMF_apply, trajectoryIndexPMF_apply]
  change boltzmannWeight potential (trajectory₁ i) * N₁⁻¹ ≤
    c ^ 2 * (boltzmannWeight potential (trajectory₂ i) * N₂⁻¹)
  apply le_trans (mul_le_mul_left hweight N₁⁻¹)
  apply le_trans (mul_le_mul_right hinv
    (c * boltzmannWeight potential (trajectory₂ i)))
  exact le_of_eq (by simp only [pow_two]; ac_rfl)

/-- Direction-dependent energy offsets cancel after normalization. If the two
directional discrepancies have bounds `r₁₂` and `r₂₁`, the normalized atom
ratio only retains their sum. This is essential when the two trajectories
have different constant baseline energies. -/
theorem trajectoryIndexPMF_le_exp_add_mul_of_energy_sub_le
    (potential : Position ι → ℝ) {L : ℕ}
    (trajectory₁ trajectory₂ : Fin (L + 1) → PhaseSpace ι)
    {r₁₂ r₂₁ : ℝ}
    (h₁₂ : ∀ i, energy potential (trajectory₂ i) -
      energy potential (trajectory₁ i) ≤ r₁₂)
    (h₂₁ : ∀ i, energy potential (trajectory₁ i) -
      energy potential (trajectory₂ i) ≤ r₂₁)
    (i : Fin (L + 1)) :
    trajectoryIndexPMF potential trajectory₁ i ≤
      ENNReal.ofReal (Real.exp (r₁₂ + r₂₁)) *
        trajectoryIndexPMF potential trajectory₂ i := by
  let c₁₂ : ENNReal := ENNReal.ofReal (Real.exp r₁₂)
  let c₂₁ : ENNReal := ENNReal.ofReal (Real.exp r₂₁)
  let N₁ := trajectoryNormalizer potential trajectory₁
  let N₂ := trajectoryNormalizer potential trajectory₂
  have hN₁0 : N₁ ≠ 0 := trajectoryNormalizer_ne_zero potential trajectory₁
  have hN₁top : N₁ ≠ ∞ := trajectoryNormalizer_ne_top potential trajectory₁
  have hN₂0 : N₂ ≠ 0 := trajectoryNormalizer_ne_zero potential trajectory₂
  have hN₂top : N₂ ≠ ∞ := trajectoryNormalizer_ne_top potential trajectory₂
  have hnormalizer : N₂ ≤ c₂₁ * N₁ :=
    trajectoryNormalizer_le_exp_mul_of_energy_sub_le potential
      trajectory₂ trajectory₁ h₂₁
  have hinv : N₁⁻¹ ≤ c₂₁ * N₂⁻¹ := by
    calc
      N₁⁻¹ = (N₁⁻¹ * N₂⁻¹) * N₂ := by
        rw [mul_assoc, ENNReal.inv_mul_cancel hN₂0 hN₂top, mul_one]
      _ ≤ (N₁⁻¹ * N₂⁻¹) * (c₂₁ * N₁) :=
        mul_le_mul_right hnormalizer _
      _ = c₂₁ * N₂⁻¹ := by
        rw [show (N₁⁻¹ * N₂⁻¹) * (c₂₁ * N₁) =
          c₂₁ * (N₁⁻¹ * N₁) * N₂⁻¹ by ac_rfl,
          ENNReal.inv_mul_cancel hN₁0 hN₁top, mul_one]
  have hweight : boltzmannWeight potential (trajectory₁ i) ≤
      c₁₂ * boltzmannWeight potential (trajectory₂ i) :=
    boltzmannWeight_le_exp_mul_of_energy_sub_le potential _ _ (h₁₂ i)
  rw [trajectoryIndexPMF_apply, trajectoryIndexPMF_apply]
  change boltzmannWeight potential (trajectory₁ i) * N₁⁻¹ ≤
    ENNReal.ofReal (Real.exp (r₁₂ + r₂₁)) *
      (boltzmannWeight potential (trajectory₂ i) * N₂⁻¹)
  apply le_trans (mul_le_mul_left hweight N₁⁻¹)
  apply le_trans (mul_le_mul_right hinv
    (c₁₂ * boltzmannWeight potential (trajectory₂ i)))
  have hc : c₁₂ * c₂₁ =
      ENNReal.ofReal (Real.exp (r₁₂ + r₂₁)) := by
    dsimp [c₁₂, c₂₁]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  rw [← hc]
  exact le_of_eq (by ac_rfl)

/-- Separate constant baseline energies cancel from the normalized trajectory
laws. Only the two within-trajectory defect radii remain. -/
theorem trajectoryIndexPMF_le_exp_sq_mul_of_centered_energy_le
    (potential : Position ι → ℝ) {L : ℕ}
    (trajectory₁ trajectory₂ : Fin (L + 1) → PhaseSpace ι)
    (center₁ center₂ δ₁ δ₂ : ℝ)
    (h₁ : ∀ i, |energy potential (trajectory₁ i) - center₁| ≤ δ₁)
    (h₂ : ∀ i, |energy potential (trajectory₂ i) - center₂| ≤ δ₂)
    (i : Fin (L + 1)) :
    trajectoryIndexPMF potential trajectory₁ i ≤
      (ENNReal.ofReal (Real.exp (δ₁ + δ₂))) ^ 2 *
        trajectoryIndexPMF potential trajectory₂ i := by
  have h := trajectoryIndexPMF_le_exp_add_mul_of_energy_sub_le potential
    trajectory₁ trajectory₂
    (r₁₂ := center₂ - center₁ + (δ₁ + δ₂))
    (r₂₁ := center₁ - center₂ + (δ₁ + δ₂))
    (fun j => by
      have hleft := (abs_le.mp (h₁ j)).1
      have hright := (abs_le.mp (h₂ j)).2
      linarith)
    (fun j => by
      have hleft := (abs_le.mp (h₂ j)).1
      have hright := (abs_le.mp (h₁ j)).2
      linarith) i
  convert h using 1
  rw [pow_two, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← Real.exp_add]
  congr 2
  ring_nf

/-- Quantitative centered-energy form of Proposition 4.2: if each trajectory
is nearly energy-conserving around its own baseline, their normalized index
laws are close regardless of the gap between those baselines. -/
theorem trajectoryIndexPMF_totalVariation_le_of_centered_energy
    (potential : Position ι → ℝ) {L : ℕ}
    (trajectory₁ trajectory₂ : Fin (L + 1) → PhaseSpace ι)
    (center₁ center₂ δ₁ δ₂ : ℝ) (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂)
    (h₁ : ∀ i, |energy potential (trajectory₁ i) - center₁| ≤ δ₁)
    (h₂ : ∀ i, |energy potential (trajectory₂ i) - center₂| ≤ δ₂) :
    Mcmc.Finite.totalVariation
        (trajectoryIndexPMF potential trajectory₁)
        (trajectoryIndexPMF potential trajectory₂) ≤
      (ENNReal.ofReal (Real.exp (δ₁ + δ₂))) ^ 2 - 1 := by
  apply Mcmc.Finite.totalVariation_le_tsub_one_of_le_mul
  · exact one_le_pow₀ (ENNReal.one_le_ofReal.mpr
      (Real.one_le_exp (add_nonneg hδ₁ hδ₂)))
  · exact trajectoryIndexPMF_le_exp_sq_mul_of_centered_energy_le
      potential trajectory₁ trajectory₂ center₁ center₂ δ₁ δ₂ h₁ h₂

/-- If the two *centered* energy-defect profiles differ by at most `r`, their
normalized trajectory laws are close independently of the baseline-energy
gap. On the local range `0 ≤ r ≤ 1/2`, total variation is at most `4r`. -/
theorem trajectoryIndexPMF_totalVariation_le_four_mul_of_centeredDifference
    (potential : Position ι → ℝ) {L : ℕ}
    (trajectory₁ trajectory₂ : Fin (L + 1) → PhaseSpace ι)
    (center₁ center₂ : ℝ) {r : ℝ} (hr0 : 0 ≤ r) (hrsmall : r ≤ 1 / 2)
    (hdefect : ∀ i,
      |(energy potential (trajectory₁ i) - center₁) -
        (energy potential (trajectory₂ i) - center₂)| ≤ r) :
    Mcmc.Finite.totalVariation
        (trajectoryIndexPMF potential trajectory₁)
        (trajectoryIndexPMF potential trajectory₂) ≤ ENNReal.ofReal (4 * r) := by
  have hdom : ∀ i, trajectoryIndexPMF potential trajectory₁ i ≤
      ENNReal.ofReal (Real.exp (2 * r)) *
        trajectoryIndexPMF potential trajectory₂ i := by
    intro i
    have h := trajectoryIndexPMF_le_exp_add_mul_of_energy_sub_le
      potential trajectory₁ trajectory₂
      (r₁₂ := center₂ - center₁ + r)
      (r₂₁ := center₁ - center₂ + r)
      (fun j => by
        have := (abs_le.mp (hdefect j)).1
        linarith)
      (fun j => by
        have := (abs_le.mp (hdefect j)).2
        linarith) i
    convert h using 1
    congr 3
    ring
  apply le_trans (Mcmc.Finite.totalVariation_le_tsub_one_of_le_mul
    _ _ (ENNReal.ofReal (Real.exp (2 * r)))
    (ENNReal.one_le_ofReal.mpr (Real.one_le_exp (by positivity))) hdom)
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ zero_le_one]
  apply ENNReal.ofReal_le_ofReal
  have habs : |2 * r| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg (by norm_num) hr0)]
    linarith
  have hexp := Real.abs_exp_sub_one_le habs
  have hexp_nonneg : 0 ≤ Real.exp (2 * r) - 1 := by
    exact sub_nonneg.mpr (Real.one_le_exp (mul_nonneg (by norm_num) hr0))
  have hr_nonneg : 0 ≤ 2 * r := mul_nonneg (by norm_num) hr0
  rw [abs_of_nonneg hexp_nonneg, abs_of_nonneg hr_nonneg] at hexp
  linarith

/-- Uniform absolute Hamiltonian error gives the normalized multiplicative
domination used in the total-variation argument. -/
theorem trajectoryIndexPMF_le_exp_sq_mul_of_abs_energy_sub_le
    (potential : Position ι → ℝ) {L : ℕ}
    (trajectory₁ trajectory₂ : Fin (L + 1) → PhaseSpace ι) {r : ℝ}
    (h : ∀ i, |energy potential (trajectory₁ i) -
      energy potential (trajectory₂ i)| ≤ r) (i : Fin (L + 1)) :
    trajectoryIndexPMF potential trajectory₁ i ≤
      (ENNReal.ofReal (Real.exp r)) ^ 2 *
        trajectoryIndexPMF potential trajectory₂ i := by
  apply trajectoryIndexPMF_le_exp_sq_mul_of_energy_sub_le potential
    trajectory₁ trajectory₂
  · intro j
    have := (abs_le.mp (h j)).1
    linarith
  · intro j
    exact (abs_le.mp (h j)).2

/-- Quantitative trajectory-weight bound: uniform Hamiltonian discrepancy
`r ≥ 0` implies total variation at most `exp(r)² - 1` between the two
multinomial index laws. -/
theorem trajectoryIndexPMF_totalVariation_le_of_abs_energy_sub_le
    (potential : Position ι → ℝ) {L : ℕ}
    (trajectory₁ trajectory₂ : Fin (L + 1) → PhaseSpace ι) {r : ℝ}
    (hr : 0 ≤ r)
    (h : ∀ i, |energy potential (trajectory₁ i) -
      energy potential (trajectory₂ i)| ≤ r) :
    Mcmc.Finite.totalVariation
        (trajectoryIndexPMF potential trajectory₁)
        (trajectoryIndexPMF potential trajectory₂) ≤
      (ENNReal.ofReal (Real.exp r)) ^ 2 - 1 := by
  apply Mcmc.Finite.totalVariation_le_tsub_one_of_le_mul
  · have hc : (1 : ENNReal) ≤ ENNReal.ofReal (Real.exp r) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (Real.one_le_exp hr)
    exact one_le_pow₀ hc
  · exact trajectoryIndexPMF_le_exp_sq_mul_of_abs_energy_sub_le
      potential trajectory₁ trajectory₂ h

/-- On the local range `0 ≤ r ≤ 1/2`, the exponential envelope in the
normalized-Boltzmann TV estimate is at most `4r`.  This linear form is what
allows the maximal-coupling mismatch probability to scale with the initial
separation. -/
theorem trajectoryIndexPMF_totalVariation_le_four_mul_of_abs_energy_sub_le
    (potential : Position ι → ℝ) {L : ℕ}
    (trajectory₁ trajectory₂ : Fin (L + 1) → PhaseSpace ι) {r : ℝ}
    (hr0 : 0 ≤ r) (hrsmall : r ≤ 1 / 2)
    (h : ∀ i, |energy potential (trajectory₁ i) -
      energy potential (trajectory₂ i)| ≤ r) :
    Mcmc.Finite.totalVariation
        (trajectoryIndexPMF potential trajectory₁)
        (trajectoryIndexPMF potential trajectory₂) ≤
      ENNReal.ofReal (4 * r) := by
  apply (trajectoryIndexPMF_totalVariation_le_of_abs_energy_sub_le
    potential trajectory₁ trajectory₂ hr0 h).trans
  rw [← ENNReal.ofReal_pow (Real.exp_pos r).le,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ zero_le_one]
  apply ENNReal.ofReal_le_ofReal
  have habs : |2 * r| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg (by norm_num) hr0)]
    linarith
  have hexp := Real.abs_exp_sub_one_le habs
  have hexp_nonneg : 0 ≤ Real.exp (2 * r) - 1 := by
    exact sub_nonneg.mpr (Real.one_le_exp (mul_nonneg (by norm_num) hr0))
  have hr_nonneg : 0 ≤ 2 * r := mul_nonneg (by norm_num) hr0
  rw [abs_of_nonneg hexp_nonneg, abs_of_nonneg hr_nonneg] at hexp
  calc
    Real.exp r ^ 2 - 1 = Real.exp (2 * r) - 1 := by
      rw [show (2 : ℝ) * r = r + r by ring, Real.exp_add, pow_two]
    _ ≤ 4 * r := by linarith

/-- Centered energy control gives a uniform lower bound on every normalized
trajectory atom.  The floor is the inverse of the number of indices times the
worst Boltzmann ratio `exp(2δ)`. -/
theorem trajectoryIndexPMF_atomFloor_of_centered_energy
    (potential : Position ι → ℝ) {L : ℕ}
    (trajectory : Fin (L + 1) → PhaseSpace ι)
    (center δ : ℝ)
    (henergy : ∀ i, |energy potential (trajectory i) - center| ≤ δ)
    (i : Fin (L + 1)) :
    (((L + 1 : ℕ) : ENNReal) * ENNReal.ofReal (Real.exp (2 * δ)))⁻¹ ≤
      trajectoryIndexPMF potential trajectory i := by
  let c : ENNReal := ENNReal.ofReal (Real.exp (2 * δ))
  have hc0 : c ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have hpoint : ∀ j, trajectoryIndexPMF potential trajectory j ≤
      c * trajectoryIndexPMF potential trajectory i := by
    intro j
    have hEiUpper := (abs_le.mp (henergy i)).2
    have hEjLower := (abs_le.mp (henergy j)).1
    have hdiff : energy potential (trajectory i) -
        energy potential (trajectory j) ≤ 2 * δ := by
      linarith
    have hw := boltzmannWeight_le_exp_mul_of_energy_sub_le
      potential (trajectory j) (trajectory i) hdiff
    rw [trajectoryIndexPMF_apply, trajectoryIndexPMF_apply]
    change boltzmannWeight potential (trajectory j) * _ ≤
      c * (boltzmannWeight potential (trajectory i) * _)
    simpa only [c, mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_right hw (trajectoryNormalizer potential trajectory)⁻¹
  have hsum : (1 : ENNReal) ≤
      ((L + 1 : ℕ) : ENNReal) * c *
        trajectoryIndexPMF potential trajectory i := by
    calc
      (1 : ENNReal) = ∑ j, trajectoryIndexPMF potential trajectory j := by
        rw [show ∑ j, trajectoryIndexPMF potential trajectory j =
            ∑' j, trajectoryIndexPMF potential trajectory j by rw [tsum_fintype],
          PMF.tsum_coe]
      _ ≤ ∑ _j : Fin (L + 1),
          c * trajectoryIndexPMF potential trajectory i :=
        Finset.sum_le_sum fun j hj => hpoint j
      _ = ((L + 1 : ℕ) : ENNReal) * c *
          trajectoryIndexPMF potential trajectory i := by
        simp [mul_assoc]
  let factor : ENNReal := ((L + 1 : ℕ) : ENNReal) * c
  have hfactor0 : factor ≠ 0 := mul_ne_zero (by simp) hc0
  change factor⁻¹ ≤ trajectoryIndexPMF potential trajectory i
  apply (ENNReal.inv_le_iff_le_mul
    (fun _ => hfactor0)
    (fun _ => trajectoryIndexPMF_apply_ne_zero potential trajectory i)).2
  simpa only [factor, mul_assoc] using hsum

/-- Two centered-energy bounds give a common atom floor for the overlap of
their multinomial trajectory laws. -/
theorem trajectoryIndexPMF_overlap_atomFloor_of_centered_energy
    (potential : Position ι → ℝ) {L : ℕ}
    (trajectory₁ trajectory₂ : Fin (L + 1) → PhaseSpace ι)
    (center₁ center₂ δ : ℝ)
    (henergy₁ : ∀ i, |energy potential (trajectory₁ i) - center₁| ≤ δ)
    (henergy₂ : ∀ i, |energy potential (trajectory₂ i) - center₂| ≤ δ)
    (i : Fin (L + 1)) :
    (((L + 1 : ℕ) : ENNReal) * ENNReal.ofReal (Real.exp (2 * δ)))⁻¹ ≤
      min (trajectoryIndexPMF potential trajectory₁ i)
        (trajectoryIndexPMF potential trajectory₂ i) := by
  apply le_min
  · exact trajectoryIndexPMF_atomFloor_of_centered_energy
      potential trajectory₁ center₁ δ henergy₁ i
  · exact trajectoryIndexPMF_atomFloor_of_centered_energy
      potential trajectory₂ center₂ δ henergy₂ i

/-- Hence a finite band of indices carries at least its cardinality times the
common overlap-atom floor. -/
theorem trajectoryIndexPMF_overlap_bandMass_ge_of_centered_energy
    (potential : Position ι → ℝ) {L : ℕ}
    (trajectory₁ trajectory₂ : Fin (L + 1) → PhaseSpace ι)
    (center₁ center₂ δ : ℝ)
    (henergy₁ : ∀ i, |energy potential (trajectory₁ i) - center₁| ≤ δ)
    (henergy₂ : ∀ i, |energy potential (trajectory₂ i) - center₂| ≤ δ)
    (band : Finset (Fin (L + 1))) :
    ((band.card : ℕ) : ENNReal) *
        (((L + 1 : ℕ) : ENNReal) * ENNReal.ofReal (Real.exp (2 * δ)))⁻¹ ≤
      ∑ i ∈ band, min (trajectoryIndexPMF potential trajectory₁ i)
        (trajectoryIndexPMF potential trajectory₂ i) := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  simpa only [Nat.cast_one, one_mul] using
    trajectoryIndexPMF_overlap_atomFloor_of_centered_energy
      potential trajectory₁ trajectory₂ center₁ center₂ δ
        henergy₁ henergy₂ i

/-- Position-potential error, momentum error, and a momentum-size bound give
an explicit total-variation estimate for two multinomial trajectory laws. -/
theorem trajectoryIndexPMF_totalVariation_le_of_phase_error
    (potential : Position ι → ℝ) {L : ℕ}
    (trajectory₁ trajectory₂ : Fin (L + 1) → PhaseSpace ι)
    {δq δp P : ℝ}
    (hpotential : ∀ i,
      |potential (trajectory₁ i).1 - potential (trajectory₂ i).1| ≤ δq)
    (hmomentum : ∀ i,
      euclideanNorm ((trajectory₁ i).2 - (trajectory₂ i).2) ≤ δp)
    (hmomentumSize : ∀ i,
      euclideanNorm (trajectory₁ i).2 + euclideanNorm (trajectory₂ i).2 ≤ P) :
    Mcmc.Finite.totalVariation
        (trajectoryIndexPMF potential trajectory₁)
        (trajectoryIndexPMF potential trajectory₂) ≤
      (ENNReal.ofReal (Real.exp (δq + (1 / 2 : ℝ) * δp * P))) ^ 2 - 1 := by
  have hδq : 0 ≤ δq := le_trans (abs_nonneg _) (hpotential 0)
  have hδp : 0 ≤ δp :=
    le_trans (euclideanNorm_nonneg _) (hmomentum 0)
  have hP : 0 ≤ P := by
    apply le_trans _ (hmomentumSize 0)
    exact add_nonneg (euclideanNorm_nonneg _) (euclideanNorm_nonneg _)
  apply trajectoryIndexPMF_totalVariation_le_of_abs_energy_sub_le
    potential trajectory₁ trajectory₂
  · positivity
  · intro i
    apply le_trans (abs_energy_sub_le potential _ _ (hpotential i))
    have hmul := mul_le_mul (hmomentum i) (hmomentumSize i)
      (add_nonneg (euclideanNorm_nonneg _) (euclideanNorm_nonneg _)) hδp
    nlinarith

/-- A measurable family of multinomial trajectory-index distributions. -/
noncomputable def trajectoryIndexKernel [MeasurableSpace α]
    (potential : Position ι → ℝ) {L : ℕ}
    (trajectory : α → Fin (L + 1) → PhaseSpace ι)
    (hpotential : Measurable potential)
    (hmeas : ∀ i, Measurable fun x => trajectory x i) :
    ProbabilityTheory.Kernel α (Fin (L + 1)) where
  toFun x := (trajectoryIndexPMF potential (trajectory x)).toMeasure
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp_rw [PMF.toMeasure_apply_fintype]
    apply Finset.measurable_sum
    intro i hi
    by_cases his : i ∈ s
    · simp only [Set.indicator_of_mem his]
      simp only [trajectoryIndexPMF_apply]
      apply Measurable.mul
      · exact (measurable_boltzmannWeight (ι := ι) hpotential).comp (hmeas i)
      · apply Measurable.inv
        apply Finset.measurable_sum
        intro j hj
        exact (measurable_boltzmannWeight (ι := ι) hpotential).comp (hmeas j)
    · simp [his]

instance trajectoryIndexKernel_isMarkovKernel [MeasurableSpace α]
    (potential : Position ι → ℝ) {L : ℕ}
    (trajectory : α → Fin (L + 1) → PhaseSpace ι)
    (hpotential : Measurable potential)
    (hmeas : ∀ i, Measurable fun x => trajectory x i) :
    ProbabilityTheory.IsMarkovKernel
      (trajectoryIndexKernel potential trajectory hpotential hmeas) where
  isProbabilityMeasure x :=
    PMF.toMeasure.isProbabilityMeasure
      (trajectoryIndexPMF potential (trajectory x))

/-- Select the phase point at a multinomially sampled trajectory index. -/
noncomputable def trajectorySelectionKernel [MeasurableSpace α]
    (potential : Position ι → ℝ) {L : ℕ}
    (trajectory : α → Fin (L + 1) → PhaseSpace ι)
    (hpotential : Measurable potential)
    (hmeas : ∀ i, Measurable fun x => trajectory x i) :
    ProbabilityTheory.Kernel α (PhaseSpace ι) where
  toFun x := (trajectoryIndexPMF potential (trajectory x)).toMeasure.map (trajectory x)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp_rw [Measure.map_apply (measurable_of_countable _) hs]
    simp_rw [PMF.toMeasure_apply_fintype]
    apply Finset.measurable_sum
    intro i hi
    change Measurable fun x =>
      (trajectory x ⁻¹' s).indicator
        (trajectoryIndexPMF potential (trajectory x)) i
    apply Measurable.indicator
    · simp only [trajectoryIndexPMF_apply]
      apply Measurable.mul
      · exact (measurable_boltzmannWeight (ι := ι) hpotential).comp (hmeas i)
      · apply Measurable.inv
        apply Finset.measurable_sum
        intro j hj
        exact (measurable_boltzmannWeight (ι := ι) hpotential).comp (hmeas j)
    · exact hmeas i hs

instance trajectorySelectionKernel_isMarkovKernel [MeasurableSpace α]
    (potential : Position ι → ℝ) {L : ℕ}
    (trajectory : α → Fin (L + 1) → PhaseSpace ι)
    (hpotential : Measurable potential)
    (hmeas : ∀ i, Measurable fun x => trajectory x i) :
    ProbabilityTheory.IsMarkovKernel
      (trajectorySelectionKernel potential trajectory hpotential hmeas) where
  isProbabilityMeasure x := by
    change IsProbabilityMeasure
      ((trajectoryIndexPMF potential (trajectory x)).toMeasure.map (trajectory x))
    exact Measure.isProbabilityMeasure_map
      (measurable_of_countable (trajectory x)).aemeasurable

theorem trajectorySelectionKernel_apply [MeasurableSpace α]
    (potential : Position ι → ℝ) {L : ℕ}
    (trajectory : α → Fin (L + 1) → PhaseSpace ι)
    (hpotential : Measurable potential)
    (hmeas : ∀ i, Measurable fun x => trajectory x i)
    (x : α) (s : Set (PhaseSpace ι)) (hs : MeasurableSet s) :
    trajectorySelectionKernel potential trajectory hpotential hmeas x s =
      ∑ i, (trajectory x ⁻¹' s).indicator
        (trajectoryIndexPMF potential (trajectory x)) i := by
  rw [trajectorySelectionKernel]
  change (trajectoryIndexPMF potential (trajectory x)).toMeasure.map
    (trajectory x) s = _
  rw [Measure.map_apply (measurable_of_countable _) hs]
  rw [PMF.toMeasure_apply_fintype]

/-- A finite PMF's `ENNReal` expectation is its finite weighted sum. -/
theorem lintegral_pmf_toMeasure_fintype
    {β : Type*} [Fintype β] [MeasurableSpace β]
    [MeasurableSingletonClass β] (p : PMF β) (f : β → ENNReal)
    (hf : Measurable f) :
    (∫⁻ x, f x ∂p.toMeasure) = ∑ x, p x * f x := by
  have hmeasure : p.toMeasure =
      ∑ x : β, (p x) • Measure.dirac x := by
    ext s hs
    rw [PMF.toMeasure_apply_fintype]
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro x _hx
    rw [Measure.dirac_apply' _ hs]
    by_cases hxs : x ∈ s <;> simp [hxs]
  rw [hmeasure, lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [lintegral_smul_measure, lintegral_dirac' x hf]
  rfl

/-- Exact finite-sum expectation under multinomial trajectory selection. -/
theorem lintegral_trajectorySelectionKernel [MeasurableSpace α]
    (potential : Position ι → ℝ) {L : ℕ}
    (trajectory : α → Fin (L + 1) → PhaseSpace ι)
    (hpotential : Measurable potential)
    (hmeas : ∀ i, Measurable fun x => trajectory x i)
    (f : PhaseSpace ι → ENNReal) (hf : Measurable f) (x : α) :
    (∫⁻ z, f z ∂trajectorySelectionKernel potential trajectory
      hpotential hmeas x) =
      ∑ i, trajectoryIndexPMF potential (trajectory x) i * f (trajectory x i) := by
  unfold trajectorySelectionKernel
  change (∫⁻ z, f z ∂(trajectoryIndexPMF potential
    (trajectory x)).toMeasure.map (trajectory x)) = _
  rw [MeasureTheory.lintegral_map hf (measurable_of_countable (trajectory x))]
  exact lintegral_pmf_toMeasure_fintype _ _ (measurable_of_countable _)

/-- The first `L + 1` states of a forward leapfrog trajectory. -/
noncomputable def finiteLeapfrogTrajectory
    (gradient : Position ι → Position ι) (ε : ℝ) (L : ℕ)
    (z : PhaseSpace ι) (i : Fin (L + 1)) : PhaseSpace ι :=
  leapfrogTrajectory gradient ε z i

omit [Fintype ι] in
theorem measurable_finiteLeapfrogTrajectory
    {gradient : Position ι → Position ι} (hgradient : Measurable gradient)
    (ε : ℝ) (L : ℕ) (i : Fin (L + 1)) :
    Measurable fun z => finiteLeapfrogTrajectory gradient ε L z i := by
  exact measurable_leapfrogN hgradient ε i

/-- Multinomial selection from the first `L + 1` points of a forward
leapfrog trajectory. This is the trajectory-selection component of
multinomial HMC; momentum refresh and the invariance-preserving randomized
trajectory construction are separate layers. -/
noncomputable def multinomialLeapfrogKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    ProbabilityTheory.Kernel (PhaseSpace ι) (PhaseSpace ι) :=
  trajectorySelectionKernel potential
    (finiteLeapfrogTrajectory gradient ε L) hpotential
    (measurable_finiteLeapfrogTrajectory hgradient ε L)

instance multinomialLeapfrogKernel_isMarkovKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    ProbabilityTheory.IsMarkovKernel
      (multinomialLeapfrogKernel potential gradient ε L hpotential hgradient) :=
  trajectorySelectionKernel_isMarkovKernel potential
    (finiteLeapfrogTrajectory gradient ε L) hpotential
    (measurable_finiteLeapfrogTrajectory hgradient ε L)

end Mcmc.Hamiltonian
