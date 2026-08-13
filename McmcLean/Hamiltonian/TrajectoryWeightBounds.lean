import McmcLean.Hamiltonian.Assumptions
import McmcLean.Hamiltonian.CoupledMultinomialHMC
import McmcLean.Hamiltonian.ExactFlow
import McmcLean.Hamiltonian.LeapfrogContraction

/-!
# Analytic bounds for multinomial trajectory weights

This module connects compact-uniform continuity of a regular potential to the
deterministic total-variation bounds for normalized Boltzmann trajectory
weights.  It isolates the analytic interface needed by Proposition 4.2 of
Xu, Fjelde, Sutton, and Ge (2021).
-/

open scoped ENNReal

namespace McmcLean.Hamiltonian

variable {ι : Type*} [Fintype ι]

/-- A locally uniform one-step energy-defect estimate strong enough for the
fixed-integration-time argument in equation (18) of the supplement to Xu et
al.  Quadratic local error is sufficient here; the usual second-order
leapfrog analysis provides the stronger cubic local error under appropriate
smoothness bounds. -/
def LocallyUniformQuadraticLeapfrogEnergyError
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι) : Prop :=
  ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (ε : ℝ) (z : PhaseSpace ι), |ε| ≤ 1 →
      euclideanPhaseSize z ≤ R →
      |energy potential (leapfrog gradient ε z) - energy potential z| ≤
        C * |ε| ^ 2

/-- Assumption 1 itself supplies the locally uniform quadratic one-step
energy defect. The bound is deliberately coarse: only its quadratic step-size
scaling and locality in phase size are needed by the fixed-horizon argument. -/
theorem RegularPotential.locallyUniformQuadraticLeapfrogEnergyError
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β) :
    LocallyUniformQuadraticLeapfrogEnergyError potential gradient := by
  intro R
  let S := max R 0
  let D : ℝ := (Fintype.card ι : ℝ) + 1
  let G := (β : ℝ) * S + euclideanNorm (gradient 0)
  let P := S + G
  let G₁ := G + (β : ℝ) * P
  let C := (β : ℝ) * D ^ 2 * P ^ 2 +
    ((β : ℝ) / 2) * P ^ 2 + (1 / 8 : ℝ) * (G₁ ^ 2 + G ^ 2)
  have hS : 0 ≤ S := le_max_right _ _
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hG : 0 ≤ G := by
    dsimp [G]
    exact add_nonneg (mul_nonneg β.coe_nonneg hS)
      (euclideanNorm_nonneg _)
  have hP : 0 ≤ P := add_nonneg hS hG
  have hG₁ : 0 ≤ G₁ := by
    dsimp [G₁]
    exact add_nonneg hG (mul_nonneg β.coe_nonneg hP)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg
      (add_nonneg
        (mul_nonneg (mul_nonneg β.coe_nonneg (sq_nonneg D)) (sq_nonneg P))
        (mul_nonneg (div_nonneg β.coe_nonneg (by norm_num)) (sq_nonneg P)))
      (mul_nonneg (by norm_num) (add_nonneg (sq_nonneg G₁) (sq_nonneg G)))
  refine ⟨C, hC, ?_⟩
  intro ε z hε hz
  let pHalf := halfKick gradient ε z.1 z.2
  let qNext := drift ε z.1 pHalf
  have hR : R ≤ S := le_max_left _ _
  have hq : euclideanNorm z.1 ≤ S :=
    (euclideanNorm_fst_le_phaseSize z).trans (hz.trans hR)
  have hp : euclideanNorm z.2 ≤ S := by
    unfold euclideanPhaseSize at hz
    nlinarith [euclideanNorm_nonneg z.1]
  have hg : euclideanNorm (gradient z.1) ≤ G := by
    apply (hreg.euclideanNorm_gradient_le z.1).trans
    dsimp [G]
    gcongr
  have hpHalf : euclideanNorm pHalf ≤ P := by
    dsimp [pHalf, halfKick]
    apply (euclideanNorm_sub_le z.2 ((ε / 2) • gradient z.1)).trans
    rw [euclideanNorm_smul]
    have habs : |ε / 2| ≤ 1 := by
      rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [abs_nonneg ε]
    dsimp [P]
    nlinarith [euclideanNorm_nonneg z.2, euclideanNorm_nonneg (gradient z.1)]
  have hqdiff : euclideanNorm (qNext - z.1) ≤ |ε| * P := by
    have hqeq : qNext - z.1 = ε • pHalf := by
      dsimp [qNext, drift]
      abel
    rw [hqeq, euclideanNorm_smul]
    exact mul_le_mul_of_nonneg_left hpHalf (abs_nonneg ε)
  have hgdiff : euclideanNorm (gradient qNext - gradient z.1) ≤
      (β : ℝ) * (|ε| * P) :=
    (hreg.euclideanNorm_gradient_sub_le qNext z.1).trans
      (mul_le_mul_of_nonneg_left hqdiff β.coe_nonneg)
  have hgNext : euclideanNorm (gradient qNext) ≤ G₁ := by
    have htri := euclideanNorm_add_le
      (gradient qNext - gradient z.1) (gradient z.1)
    have heq : gradient qNext - gradient z.1 + gradient z.1 = gradient qNext := by
      abel
    rw [heq] at htri
    have habsP : |ε| * P ≤ P := by
      calc
        |ε| * P ≤ 1 * P := mul_le_mul_of_nonneg_right hε hP
        _ = P := one_mul P
    calc
      euclideanNorm (gradient qNext) ≤
          euclideanNorm (gradient qNext - gradient z.1) +
            euclideanNorm (gradient z.1) := htri
      _ ≤ (β : ℝ) * (|ε| * P) + G := add_le_add hgdiff hg
      _ ≤ (β : ℝ) * P + G :=
        add_le_add (mul_le_mul_of_nonneg_left habsP β.coe_nonneg) le_rfl
      _ = G₁ := by dsimp [G₁]; ring
  rw [energy_leapfrog_sub_eq_taylorRemainder]
  change |(potential qNext - potential z.1 -
      euclideanInner (gradient z.1) (qNext - z.1)) +
    (ε / 2) * euclideanInner pHalf (gradient z.1 - gradient qNext) +
    (ε ^ 2 / 8) * (squaredEuclideanNorm (gradient qNext) -
      squaredEuclideanNorm (gradient z.1))| ≤ _
  apply le_trans (abs_add_le _ _)
  apply le_trans (add_le_add (abs_add_le _ _) le_rfl)
  have htaylor := hreg.abs_potential_sub_linearization_le z.1 qNext
  have htaylor' :
      |potential qNext - potential z.1 -
          euclideanInner (gradient z.1) (qNext - z.1)| ≤
        ((β : ℝ) * D ^ 2 * P ^ 2) * |ε| ^ 2 := by
    apply htaylor.trans
    dsimp [D]
    have hsquare := (sq_le_sq₀ (euclideanNorm_nonneg _)
      (mul_nonneg (abs_nonneg ε) hP)).mpr hqdiff
    nlinarith [mul_nonneg β.coe_nonneg (sq_nonneg D)]
  have hmiddle :
      |(ε / 2) * euclideanInner pHalf
          (gradient z.1 - gradient qNext)| ≤
        (((β : ℝ) / 2) * P ^ 2) * |ε| ^ 2 := by
    rw [abs_mul, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    apply le_trans (mul_le_mul_of_nonneg_left
      (abs_euclideanInner_le_norm_mul_norm pHalf
        (gradient z.1 - gradient qNext)) (by positivity))
    have hgd : euclideanNorm (gradient z.1 - gradient qNext) ≤
        (β : ℝ) * (|ε| * P) := by
      have heq : gradient z.1 - gradient qNext =
          -(gradient qNext - gradient z.1) := by abel
      rw [heq, euclideanNorm_neg]
      exact hgdiff
    calc
      |ε| / 2 *
          (euclideanNorm pHalf *
            euclideanNorm (gradient z.1 - gradient qNext)) ≤
        |ε| / 2 * (P * ((β : ℝ) * (|ε| * P))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul hpHalf hgd (euclideanNorm_nonneg _) hP)
            (div_nonneg (abs_nonneg ε) (by norm_num))
      _ = ((β : ℝ) / 2 * P ^ 2) * |ε| ^ 2 := by ring
  have hlast :
      |(ε ^ 2 / 8) *
          (squaredEuclideanNorm (gradient qNext) -
            squaredEuclideanNorm (gradient z.1))| ≤
        ((1 / 8 : ℝ) * (G₁ ^ 2 + G ^ 2)) * |ε| ^ 2 := by
    rw [abs_mul, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8), abs_pow]
    have hsqNext : squaredEuclideanNorm (gradient qNext) ≤ G₁ ^ 2 := by
      rw [← euclideanNorm_sq]
      exact (sq_le_sq₀ (euclideanNorm_nonneg _) hG₁).mpr hgNext
    have hsq : squaredEuclideanNorm (gradient z.1) ≤ G ^ 2 := by
      rw [← euclideanNorm_sq]
      exact (sq_le_sq₀ (euclideanNorm_nonneg _) hG).mpr hg
    have habsdiff := abs_sub_le
      (squaredEuclideanNorm (gradient qNext))
      0 (squaredEuclideanNorm (gradient z.1))
    have habsdiff0 :
        |squaredEuclideanNorm (gradient qNext) -
          squaredEuclideanNorm (gradient z.1)| ≤
        squaredEuclideanNorm (gradient qNext) +
          squaredEuclideanNorm (gradient z.1) := by
      simpa only [sub_zero, zero_sub, abs_neg,
        abs_of_nonneg (squaredEuclideanNorm_nonneg _)]
        using habsdiff
    have habsdiff' :
        |squaredEuclideanNorm (gradient qNext) -
          squaredEuclideanNorm (gradient z.1)| ≤ G₁ ^ 2 + G ^ 2 :=
      habsdiff0.trans (add_le_add hsqNext hsq)
    calc
      |ε| ^ 2 / 8 *
          |squaredEuclideanNorm (gradient qNext) -
            squaredEuclideanNorm (gradient z.1)| ≤
        |ε| ^ 2 / 8 * (G₁ ^ 2 + G ^ 2) := by
          gcongr
      _ = (1 / 8 * (G₁ ^ 2 + G ^ 2)) * |ε| ^ 2 := by ring
  apply (add_le_add (add_le_add htaylor' hmiddle) hlast).trans_eq
  dsimp [C]
  ring

/-- A locally uniform quadratic one-step defect telescopes to a uniform
`O(|ε|)` energy error over every bounded integration horizon. -/
theorem abs_energy_leapfrogN_sub_le_of_horizon
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (herror : LocallyUniformQuadraticLeapfrogEnergyError potential gradient)
    {R T : ℝ} :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ε : ℝ}, |ε| ≤ 1 → ∀ (n : ℕ),
        (n : ℝ) * |ε| ≤ T → ∀ (z : PhaseSpace ι),
          euclideanPhaseSize z ≤ R →
          |energy potential (leapfrogN gradient ε n z) - energy potential z| ≤
            C * T * |ε| := by
  let B := Real.exp (leapfrogNormStabilityRate β * T) *
    (R + (2 + (β : ℝ)) * T * euclideanNorm (gradient 0))
  rcases herror B with ⟨C, hC, hstep⟩
  refine ⟨C, hC, ?_⟩
  intro ε hε n horizon z hz
  rw [energy_leapfrogN_sub_eq_sum_step_errors]
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  calc
    (∑ k ∈ Finset.range n,
        |energy potential (leapfrog gradient ε
            (leapfrogN gradient ε k z)) -
          energy potential (leapfrogN gradient ε k z)|) ≤
        ∑ k ∈ Finset.range n, C * |ε| ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      apply hstep ε (leapfrogN gradient ε k z) hε
      apply le_trans
        (leapfrogN_euclideanPhaseSize_le_exp hreg hε k ?_ z)
      · dsimp [B]
        gcongr
      · have hkn : k ≤ n := Nat.le_of_lt (Finset.mem_range.mp hk)
        have hcast : (k : ℝ) ≤ n := by exact_mod_cast hkn
        exact (mul_le_mul_of_nonneg_right hcast (abs_nonneg ε)).trans horizon
    _ = (n : ℝ) * (C * |ε| ^ 2) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ C * T * |ε| := by
      have habs : 0 ≤ |ε| := abs_nonneg ε
      have hmul := mul_le_mul_of_nonneg_left horizon hC
      nlinarith

/-- Fixed-horizon absolute stability for signed leapfrog iterates. Negative
indices are positive iterates of the inverse, i.e. leapfrog with step `-ε`. -/
theorem signedLeapfrog_euclideanPhaseSize_le_exp
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {ε : ℝ} (hε : |ε| ≤ 1) (k : ℤ) {T : ℝ}
    (horizon : (Int.natAbs k : ℝ) * |ε| ≤ T) (z : PhaseSpace ι) :
    euclideanPhaseSize (signedLeapfrog gradient ε k z) ≤
      Real.exp (leapfrogNormStabilityRate β * T) *
        (euclideanPhaseSize z +
          (2 + (β : ℝ)) * T * euclideanNorm (gradient 0)) := by
  cases k with
  | ofNat n =>
      change euclideanPhaseSize (((leapfrogPerm gradient ε) ^ n) z) ≤ _
      simpa only [Equiv.Perm.coe_pow, coe_leapfrogPerm, leapfrogN] using
        leapfrogN_euclideanPhaseSize_le_exp hreg hε n horizon z
  | negSucc n =>
      change euclideanPhaseSize
        ((((leapfrogPerm gradient ε) ^ (n + 1))⁻¹) z) ≤ _
      rw [← inv_pow]
      have hεneg : |-ε| ≤ 1 := by simpa only [abs_neg] using hε
      have hhor : ((n + 1 : ℕ) : ℝ) * |-ε| ≤ T := by
        simpa only [Int.natAbs_negSucc, abs_neg] using horizon
      simpa only [Equiv.Perm.coe_pow, coe_leapfrogPerm_inv, leapfrogN,
        abs_neg] using
        leapfrogN_euclideanPhaseSize_le_exp hreg hεneg (n + 1) hhor z

/-- The fixed-horizon energy bound also covers negative trajectory offsets,
which are positive iterates with step size `-ε`. -/
theorem abs_energy_signedLeapfrog_sub_le_of_horizon
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (herror : LocallyUniformQuadraticLeapfrogEnergyError potential gradient)
    {R T : ℝ} :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ε : ℝ}, |ε| ≤ 1 → ∀ (k : ℤ),
        (Int.natAbs k : ℝ) * |ε| ≤ T → ∀ (z : PhaseSpace ι),
          euclideanPhaseSize z ≤ R →
          |energy potential (signedLeapfrog gradient ε k z) -
            energy potential z| ≤ C * T * |ε| := by
  rcases abs_energy_leapfrogN_sub_le_of_horizon hreg herror (R := R) (T := T) with
    ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro ε hε k horizon z hz
  cases k with
  | ofNat n =>
      change |energy potential (leapfrogN gradient ε n z) -
        energy potential z| ≤ _
      exact hbound hε n horizon z hz
  | negSucc n =>
      change |energy potential (leapfrogN gradient (-ε) (n + 1) z) -
        energy potential z| ≤ _
      have hεneg : |-ε| ≤ 1 := by simpa only [abs_neg] using hε
      have hhor : ((n + 1 : ℕ) : ℝ) * |-ε| ≤ T := by
        simpa only [Int.natAbs_negSucc, abs_neg] using horizon
      simpa only [abs_neg] using hbound hεneg (n + 1) hhor z hz

/-- Every coordinate of a length-`L+1` offset trajectory satisfies the same
absolute bound when the total trajectory horizon obeys `L |ε| ≤ T`. -/
theorem offsetLeapfrogTrajectory_euclideanPhaseSize_le_exp
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {ε : ℝ} (hε : |ε| ≤ 1) {L : ℕ} (origin i : Fin (L + 1))
    {T : ℝ} (horizon : (L : ℝ) * |ε| ≤ T) (z : PhaseSpace ι) :
    euclideanPhaseSize
        (offsetLeapfrogTrajectory gradient ε origin z i) ≤
      Real.exp (leapfrogNormStabilityRate β * T) *
        (euclideanPhaseSize z +
          (2 + (β : ℝ)) * T * euclideanNorm (gradient 0)) := by
  apply signedLeapfrog_euclideanPhaseSize_le_exp hreg hε
  have hindex : Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) ≤ L := by
    omega
  have hcast : (Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) : ℝ) ≤ L := by
    exact_mod_cast hindex
  exact (mul_le_mul_of_nonneg_right hcast (abs_nonneg ε)).trans horizon

/-- For fixed step size and trajectory length, all offset-leapfrog positions
started in a compact phase set share one Euclidean radius. -/
theorem IsCompact.exists_uniform_offsetLeapfrog_positionNorm_bound
    {K : Set (PhaseSpace ι)} (hK : IsCompact K)
    {gradient : Position ι → Position ι} (hgradient : Continuous gradient)
    (ε : ℝ) {L : ℕ} (origin : Fin (L + 1)) :
    ∃ R > 0, ∀ z ∈ K, ∀ i,
      euclideanNorm (offsetLeapfrogTrajectory gradient ε origin z i).1 ≤ R := by
  have hpositions :=
    McmcLean.Hamiltonian.IsCompact.offsetLeapfrogPositionSet
      hgradient ε origin hK
  rcases McmcLean.Hamiltonian.IsCompact.exists_euclideanNorm_bound hpositions with
    ⟨R, hR, hbound⟩
  refine ⟨R, hR, ?_⟩
  intro z hz i
  exact hbound _
    (offsetLeapfrogTrajectory_position_mem_positionSet
      gradient ε origin i hz)

/-- Specialization of compact trajectory boundedness to the paper's regular
potential assumption; no separate continuity hypothesis on the gradient is
needed. -/
theorem RegularPotential.exists_uniform_offsetLeapfrog_positionNorm_bound
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {K : Set (PhaseSpace ι)} (hK : IsCompact K)
    (ε : ℝ) {L : ℕ} (origin : Fin (L + 1)) :
    ∃ R > 0, ∀ z ∈ K, ∀ i,
      euclideanNorm (offsetLeapfrogTrajectory gradient ε origin z i).1 ≤ R :=
  McmcLean.Hamiltonian.IsCompact.exists_uniform_offsetLeapfrog_positionNorm_bound
    hK hreg.continuous_gradient ε origin

/-- A single phase-size radius works uniformly over the fixed-integration-time
regime `|ε| ≤ 1`, `L |ε| ≤ T`, all origins and indices, and all initial phase
points in a compact set. -/
theorem RegularPotential.exists_uniform_offsetLeapfrog_phaseSize_bound_of_horizon
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {K : Set (PhaseSpace ι)} (hK : IsCompact K)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ R > 0, ∀ {ε : ℝ}, |ε| ≤ 1 → ∀ {L : ℕ}
      (origin i : Fin (L + 1)), (L : ℝ) * |ε| ≤ T →
      ∀ z ∈ K,
        euclideanPhaseSize
          (offsetLeapfrogTrajectory gradient ε origin z i) ≤ R := by
  rcases McmcLean.Hamiltonian.IsCompact.exists_euclideanPhaseSize_bound hK with
    ⟨M, hM, hMbound⟩
  let R := Real.exp (leapfrogNormStabilityRate β * T) *
    (M + (2 + (β : ℝ)) * T * euclideanNorm (gradient 0))
  have hforcing : 0 ≤
      (2 + (β : ℝ)) * T * euclideanNorm (gradient 0) :=
    mul_nonneg
      (mul_nonneg (add_nonneg (by norm_num) β.coe_nonneg) hT)
      (euclideanNorm_nonneg _)
  have hR : 0 < R := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le hM (le_add_of_nonneg_right hforcing))
  refine ⟨R, hR, ?_⟩
  intro ε hε L origin i horizon z hz
  apply le_trans
    (offsetLeapfrogTrajectory_euclideanPhaseSize_le_exp
      hreg hε origin i horizon z)
  dsimp [R]
  gcongr
  exact hMbound z hz

/-- Uniform off-diagonal squared-position cost over the entire
fixed-integration-time regime and compact initial phase set. -/
theorem RegularPotential.exists_uniform_trajectorySquaredPositionCost_bound_of_horizon
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {K : Set (PhaseSpace ι)} (hK : IsCompact K)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ R > 0, ∀ {ε : ℝ}, |ε| ≤ 1 → ∀ {L : ℕ}
      (origin : Fin (L + 1)), (L : ℝ) * |ε| ≤ T →
      ∀ (z : PhaseSpace ι × PhaseSpace ι), z.1 ∈ K → z.2 ∈ K →
        ∀ i j,
          trajectorySquaredPositionCost gradient ε z origin i j ≤
            ⟨4 * R ^ 2, by positivity⟩ := by
  rcases hreg.exists_uniform_offsetLeapfrog_phaseSize_bound_of_horizon hK hT with
    ⟨R, hR, hbound⟩
  refine ⟨R, hR, ?_⟩
  intro ε hε L origin horizon z hz₁ hz₂ i j
  apply trajectorySquaredPositionCost_le_of_positionNorm_le
    gradient ε z origin hR.le
  · intro k
    exact (euclideanNorm_fst_le_phaseSize _).trans
      (hbound hε origin k horizon z.1 hz₁)
  · intro k
    exact (euclideanNorm_fst_le_phaseSize _).trans
      (hbound hε origin k horizon z.2 hz₂)

/-- If both leapfrog trajectories remain in one compact position region,
compactness supplies a common Euclidean radius and hence a uniform bound for
every cross-index squared-position cost. -/
theorem IsCompact.exists_trajectorySquaredPositionCost_bound
    {S : Set (Position ι)} (hS : IsCompact S)
    (gradient : Position ι → Position ι) (ε : ℝ) {L : ℕ}
    (z : PhaseSpace ι × PhaseSpace ι) (origin : Fin (L + 1))
    (hleft : ∀ i,
      (offsetLeapfrogTrajectory gradient ε origin z.1 i).1 ∈ S)
    (hright : ∀ j,
      (offsetLeapfrogTrajectory gradient ε origin z.2 j).1 ∈ S) :
    ∃ R > 0, ∀ i j,
      trajectorySquaredPositionCost gradient ε z origin i j ≤
        ⟨4 * R ^ 2, by positivity⟩ := by
  rcases McmcLean.Hamiltonian.IsCompact.exists_euclideanNorm_bound hS with
    ⟨R, hR, hbound⟩
  refine ⟨R, hR, ?_⟩
  intro i j
  exact trajectorySquaredPositionCost_le_of_positionNorm_le
    gradient ε z origin hR.le
      (fun k => hbound _ (hleft k)) (fun k => hbound _ (hright k)) i j

/-- The explicit normalized-Boltzmann total-variation bound vanishes with the
uniform energy discrepancy. -/
theorem expSqTotalVariationBound_tendsto_zero :
    Filter.Tendsto
      (fun r : ℝ => (ENNReal.ofReal (Real.exp r)) ^ 2 - 1)
      (nhds 0) (nhds 0) := by
  have hcontinuous : ContinuousAt
      (fun r : ℝ => ENNReal.ofReal ((Real.exp r) ^ 2 - 1)) 0 := by
    change ContinuousAt
      (ENNReal.ofReal ∘ fun r : ℝ => (Real.exp r) ^ 2 - 1) 0
    exact ENNReal.continuous_ofReal.continuousAt.comp (by fun_prop)
  have heq : (fun r : ℝ => (ENNReal.ofReal (Real.exp r)) ^ 2 - 1) =
      fun r : ℝ => ENNReal.ofReal ((Real.exp r) ^ 2 - 1) := by
    funext r
    rw [ENNReal.ofReal_sub _ zero_le_one,
      ENNReal.ofReal_pow (Real.exp_pos r).le, ENNReal.ofReal_one]
  rw [heq]
  simpa using hcontinuous.tendsto

/-- Every positive TV tolerance contains the normalized-Boltzmann envelope
of some positive Hamiltonian-error radius. -/
theorem exists_pos_expSqTotalVariationBound_lt
    {δ : ENNReal} (hδ : 0 < δ) :
    ∃ radius : ℝ, 0 < radius ∧
      (ENNReal.ofReal (Real.exp radius)) ^ 2 - 1 < δ := by
  have heventually : ∀ᶠ radius : ℝ in nhds 0,
      (ENNReal.ofReal (Real.exp radius)) ^ 2 - 1 < δ :=
    expSqTotalVariationBound_tendsto_zero.eventually
      (Iio_mem_nhds hδ)
  rcases Metric.mem_nhds_iff.mp heventually with
    ⟨ε, hε, hball⟩
  refine ⟨ε / 2, half_pos hε, hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero,
    abs_of_pos (half_pos hε)]
  linarith

/-- Any family of finite categorical laws satisfying the energy-radius bound
converges in total variation when that radius tends to zero. -/
theorem totalVariation_tendsto_zero_of_le_expSqBound
    {κ α : Type*} [Fintype α] {l : Filter κ}
    (p q : κ → PMF α) (radius : κ → ℝ)
    (hradius : Filter.Tendsto radius l (nhds 0))
    (hbound : ∀ᶠ k in l,
      McmcLean.Finite.totalVariation (p k) (q k) ≤
        (ENNReal.ofReal (Real.exp (radius k))) ^ 2 - 1) :
    Filter.Tendsto
      (fun k => McmcLean.Finite.totalVariation (p k) (q k))
      l (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds
    (expSqTotalVariationBound_tendsto_zero.comp hradius)
  · exact Filter.Eventually.of_forall fun k => bot_le
  · exact hbound

/-- A step-size/trajectory-length parameterized family of finite phase-space
trajectories. -/
abbrev ParameterizedTrajectoryFamily (ι : Type*) [Fintype ι] :=
  (ε : ℝ) → (L : ℕ) → Fin (L + 1) → PhaseSpace ι

/-- A trajectory family retaining the uniformly sampled backward/forward
origin as an explicit parameter. -/
abbrev ParameterizedOriginTrajectoryFamily (ι : Type*) [Fintype ι] :=
  (ε : ℝ) → (L : ℕ) → Fin (L + 1) → Fin (L + 1) → PhaseSpace ι

/-- The actual backward/forward leapfrog trajectory family from a fixed
phase point, with the randomized origin retained as a parameter. -/
noncomputable def offsetLeapfrogOriginTrajectoryFamily
    (gradient : Position ι → Position ι) (z : PhaseSpace ι) :
    ParameterizedOriginTrajectoryFamily ι :=
  fun ε _ origin i => offsetLeapfrogTrajectory gradient ε origin z i

/-- Uniform-origin average of the conditional trajectory-index TV distances. -/
noncomputable def originAveragedTrajectoryIndexTotalVariation
    (potential : Position ι → ℝ)
    (trajectory₁ trajectory₂ : ParameterizedOriginTrajectoryFamily ι)
    (ε : ℝ) (L : ℕ) : ENNReal :=
  ∑ origin : Fin (L + 1),
    PMF.uniformOfFintype (Fin (L + 1)) origin *
      McmcLean.Finite.totalVariation
        (trajectoryIndexPMF potential (trajectory₁ ε L origin))
        (trajectoryIndexPMF potential (trajectory₂ ε L origin))

/-- The actual joint selected-index law for uniform-origin randomized HMC
when each conditional categorical pair is sampled by the canonical maximal
coupling. -/
noncomputable def randomizedMaximalTrajectoryIndexCoupling
    (potential : Position ι → ℝ)
    (trajectory₁ trajectory₂ : ParameterizedOriginTrajectoryFamily ι)
    (ε : ℝ) (L : ℕ) : PMF (Fin (L + 1) × Fin (L + 1)) :=
  randomizedTrajectoryIndexCoupling fun origin =>
    McmcLean.Finite.maximalCoupling
      (trajectoryIndexPMF potential (trajectory₁ ε L origin))
      (trajectoryIndexPMF potential (trajectory₂ ε L origin))

/-- Under uniform-origin maximal selection, the probability of unequal
selected indices is exactly the averaged conditional total variation. -/
theorem randomizedMaximalTrajectoryIndexCoupling_mismatchMass
    (potential : Position ι → ℝ)
    (trajectory₁ trajectory₂ : ParameterizedOriginTrajectoryFamily ι)
    (ε : ℝ) (L : ℕ) :
    McmcLean.Finite.mismatchMass
        (randomizedMaximalTrajectoryIndexCoupling
          potential trajectory₁ trajectory₂ ε L) =
      originAveragedTrajectoryIndexTotalVariation
        potential trajectory₁ trajectory₂ ε L := by
  rw [randomizedMaximalTrajectoryIndexCoupling,
    randomizedTrajectoryIndexCoupling_mismatchMass]
  unfold originAveragedTrajectoryIndexTotalVariation
  apply Finset.sum_congr rfl
  intro origin horigin
  congr 1
  exact McmcLean.Finite.IsMaximalCoupling.mismatchMass_eq_totalVariation
    (McmcLean.Finite.maximalCoupling_isMaximal _ _)

/-- A uniform weighted average is bounded by every common pointwise bound. -/
theorem originAveragedTrajectoryIndexTotalVariation_le
    (potential : Position ι → ℝ)
    (trajectory₁ trajectory₂ : ParameterizedOriginTrajectoryFamily ι)
    (ε : ℝ) (L : ℕ) {bound : ENNReal}
    (hbound : ∀ origin,
      McmcLean.Finite.totalVariation
        (trajectoryIndexPMF potential (trajectory₁ ε L origin))
        (trajectoryIndexPMF potential (trajectory₂ ε L origin)) ≤ bound) :
    originAveragedTrajectoryIndexTotalVariation
      potential trajectory₁ trajectory₂ ε L ≤ bound := by
  unfold originAveragedTrajectoryIndexTotalVariation
  calc
    ∑ origin : Fin (L + 1),
        PMF.uniformOfFintype (Fin (L + 1)) origin *
          McmcLean.Finite.totalVariation
            (trajectoryIndexPMF potential (trajectory₁ ε L origin))
            (trajectoryIndexPMF potential (trajectory₂ ε L origin)) ≤
      ∑ origin : Fin (L + 1),
        PMF.uniformOfFintype (Fin (L + 1)) origin * bound := by
          apply Finset.sum_le_sum
          intro origin horigin
          exact mul_le_mul_right (hbound origin) _
    _ = (∑ origin : Fin (L + 1),
          PMF.uniformOfFintype (Fin (L + 1)) origin) * bound := by
      rw [Finset.sum_mul]
    _ = bound := by
      have hsum : ∑ origin : Fin (L + 1),
          PMF.uniformOfFintype (Fin (L + 1)) origin = 1 := by
        calc
          ∑ origin : Fin (L + 1),
              PMF.uniformOfFintype (Fin (L + 1)) origin =
            ∑' origin : Fin (L + 1),
              PMF.uniformOfFintype (Fin (L + 1)) origin := by
                rw [tsum_fintype]
          _ = 1 := (PMF.uniformOfFintype (Fin (L + 1))).tsum_coe
      rw [hsum, one_mul]

/-- Proposition 4.2 uniformly conditional on every shared trajectory origin. -/
def XuProposition42AllOriginsTVConclusion
    (potential : Position ι → ℝ)
    (trajectory₁ trajectory₂ : ParameterizedOriginTrajectoryFamily ι) : Prop :=
  ∀ δ : ENNReal, 0 < δ →
    ∃ ε0 : ℝ, 0 < ε0 ∧
      ∃ L0 : ℕ, 1 ≤ L0 ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 →
          ∀ L : ℕ, ε * (L : ℝ) < ε0 * (L0 : ℝ) →
            ∀ origin,
              McmcLean.Finite.totalVariation
                (trajectoryIndexPMF potential (trajectory₁ ε L origin))
                (trajectoryIndexPMF potential (trajectory₂ ε L origin)) < δ

/-- The shift-invariant numerical premise for Proposition 4.2, uniformly over
the shared randomized trajectory origin. -/
def XuProposition42AllOriginsCenteredEnergyError
    (potential : Position ι → ℝ)
    (trajectory₁ trajectory₂ : ParameterizedOriginTrajectoryFamily ι) : Prop :=
  ∀ radius : ℝ, 0 < radius →
    ∃ ε0 : ℝ, 0 < ε0 ∧
      ∃ L0 : ℕ, 1 ≤ L0 ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 →
          ∀ L : ℕ, ε * (L : ℝ) < ε0 * (L0 : ℝ) →
            ∀ origin,
              ∃ center₁ center₂ : ℝ,
                (∀ i, |energy potential (trajectory₁ ε L origin i) - center₁| ≤
                  radius) ∧
                (∀ i, |energy potential (trajectory₂ ε L origin i) - center₂| ≤
                  radius)

/-- Proposition 4.2 after averaging over the actual uniform origin draw. -/
def XuProposition42AveragedOriginTVConclusion
    (potential : Position ι → ℝ)
    (trajectory₁ trajectory₂ : ParameterizedOriginTrajectoryFamily ι) : Prop :=
  ∀ δ : ENNReal, 0 < δ →
    ∃ ε0 : ℝ, 0 < ε0 ∧
      ∃ L0 : ℕ, 1 ≤ L0 ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 →
          ∀ L : ℕ, ε * (L : ℝ) < ε0 * (L0 : ℝ) →
            originAveragedTrajectoryIndexTotalVariation
              potential trajectory₁ trajectory₂ ε L < δ

/-- Proposition 4.2 stated as the probability that the concrete
uniform-origin, maximal-coupling experiment selects unequal indices. -/
def XuProposition42RandomizedMaximalMismatchConclusion
    (potential : Position ι → ℝ)
    (trajectory₁ trajectory₂ : ParameterizedOriginTrajectoryFamily ι) : Prop :=
  ∀ δ : ENNReal, 0 < δ →
    ∃ ε0 : ℝ, 0 < ε0 ∧
      ∃ L0 : ℕ, 1 ≤ L0 ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 →
          ∀ L : ℕ, ε * (L : ℝ) < ε0 * (L0 : ℝ) →
            McmcLean.Finite.mismatchMass
              (randomizedMaximalTrajectoryIndexCoupling
                potential trajectory₁ trajectory₂ ε L) < δ

/-- The averaged-TV and concrete randomized maximal-mismatch formulations of
Proposition 4.2 are definitionally linked by the exact mismatch identity. -/
theorem xuProposition42AveragedOriginTVConclusion_iff_randomizedMaximalMismatch
    (potential : Position ι → ℝ)
    (trajectory₁ trajectory₂ : ParameterizedOriginTrajectoryFamily ι) :
    XuProposition42AveragedOriginTVConclusion
        potential trajectory₁ trajectory₂ ↔
      XuProposition42RandomizedMaximalMismatchConclusion
        potential trajectory₁ trajectory₂ := by
  constructor <;> intro h δ hδ <;>
    rcases h δ hδ with ⟨ε0, hε0, L0, hL0, h⟩ <;>
    refine ⟨ε0, hε0, L0, hL0, ?_⟩ <;>
    intro ε hεpos hε L hlength
  · rw [randomizedMaximalTrajectoryIndexCoupling_mismatchMass]
    exact h ε hεpos hε L hlength
  · rw [← randomizedMaximalTrajectoryIndexCoupling_mismatchMass]
    exact h ε hεpos hε L hlength

/-- A bound uniform over origins survives averaging over the uniform origin
law with the same requested tolerance. -/
theorem XuProposition42AllOriginsTVConclusion.averagedOrigin
    (potential : Position ι → ℝ)
    (trajectory₁ trajectory₂ : ParameterizedOriginTrajectoryFamily ι)
    (h : XuProposition42AllOriginsTVConclusion
      potential trajectory₁ trajectory₂) :
    XuProposition42AveragedOriginTVConclusion
      potential trajectory₁ trajectory₂ := by
  intro δ hδ
  by_cases hδtop : δ = ∞
  · rcases h 1 zero_lt_one with ⟨ε0, hε0, L0, hL0, hbound⟩
    refine ⟨ε0, hε0, L0, hL0, ?_⟩
    intro ε hεpos hε L hlength
    rw [hδtop]
    apply lt_of_le_of_lt
      (originAveragedTrajectoryIndexTotalVariation_le
        potential trajectory₁ trajectory₂ ε L
        (fun origin => (hbound ε hεpos hε L hlength origin).le))
    exact ENNReal.one_lt_top
  · have hhalf0 : 0 < δ / 2 := ENNReal.div_pos hδ.ne' (by norm_num)
    have hhalf : δ / 2 < δ := ENNReal.half_lt_self hδ.ne' hδtop
    rcases h (δ / 2) hhalf0 with ⟨ε0, hε0, L0, hL0, hbound⟩
    refine ⟨ε0, hε0, L0, hL0, ?_⟩
    intro ε hεpos hε L hlength
    exact (originAveragedTrajectoryIndexTotalVariation_le
      potential trajectory₁ trajectory₂ ε L
      (fun origin => (hbound ε hεpos hε L hlength origin).le)).trans_lt hhalf

/-- Uniform vanishing of the paired trajectories' Hamiltonian discrepancy in
the numerical regime used by Proposition 4.2. This is the direct numerical-
analysis obligation left after the finite normalized-Boltzmann argument. -/
def XuProposition42UniformEnergyError
    (potential : Position ι → ℝ)
    (trajectory₁ trajectory₂ : ParameterizedTrajectoryFamily ι) : Prop :=
  ∀ radius : ℝ, 0 < radius →
    ∃ ε0 : ℝ, 0 < ε0 ∧
      ∃ L0 : ℕ, 1 ≤ L0 ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 →
          ∀ L : ℕ, ε * (L : ℝ) < ε0 * (L0 : ℝ) →
            ∀ i,
              |energy potential (trajectory₁ ε L i) -
                energy potential (trajectory₂ ε L i)| ≤ radius

/-- The shift-invariant numerical premise actually used by Proposition 4.2:
each trajectory becomes uniformly energy-conserving around its own (possibly
different) baseline. -/
def XuProposition42UniformCenteredEnergyError
    (potential : Position ι → ℝ)
    (trajectory₁ trajectory₂ : ParameterizedTrajectoryFamily ι) : Prop :=
  ∀ radius : ℝ, 0 < radius →
    ∃ ε0 : ℝ, 0 < ε0 ∧
      ∃ L0 : ℕ, 1 ≤ L0 ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 →
          ∀ L : ℕ, ε * (L : ℝ) < ε0 * (L0 : ℝ) →
            ∃ center₁ center₂ : ℝ,
              (∀ i, |energy potential (trajectory₁ ε L i) - center₁| ≤
                radius) ∧
              (∀ i, |energy potential (trajectory₂ ε L i) - center₂| ≤
                radius)

/-- The quantitative conclusion of Proposition 4.2: for every positive TV
tolerance, one pair of numerical thresholds works for every smaller step size
and every trajectory length below the resulting integration-time horizon. -/
def XuProposition42TVConclusion
    (potential : Position ι → ℝ)
    (trajectory₁ trajectory₂ : ParameterizedTrajectoryFamily ι) : Prop :=
  ∀ δ : ENNReal, 0 < δ →
    ∃ ε0 : ℝ, 0 < ε0 ∧
      ∃ L0 : ℕ, 1 ≤ L0 ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 →
          ∀ L : ℕ, ε * (L : ℝ) < ε0 * (L0 : ℝ) →
            McmcLean.Finite.totalVariation
                (trajectoryIndexPMF potential (trajectory₁ ε L))
                (trajectoryIndexPMF potential (trajectory₂ ε L)) < δ

/-- Proposition 4.2 in the equivalent maximal-coupling form used by Lemma
4.3: the probability of selecting unequal trajectory indices is uniformly
smaller than every prescribed positive tolerance. -/
def XuProposition42MaximalMismatchConclusion
    (potential : Position ι → ℝ)
    (trajectory₁ trajectory₂ : ParameterizedTrajectoryFamily ι) : Prop :=
  ∀ δ : ENNReal, 0 < δ →
    ∃ ε0 : ℝ, 0 < ε0 ∧
      ∃ L0 : ℕ, 1 ≤ L0 ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 →
          ∀ L : ℕ, ε * (L : ℝ) < ε0 * (L0 : ℝ) →
            McmcLean.Finite.mismatchMass
                (McmcLean.Finite.maximalCoupling
                  (trajectoryIndexPMF potential (trajectory₁ ε L))
                  (trajectoryIndexPMF potential (trajectory₂ ε L))) < δ

/-- For the canonical maximal coupling, the TV and unequal-index formulations
of Proposition 4.2 are equivalent with identical thresholds. -/
theorem xuProposition42TVConclusion_iff_maximalMismatch
    (potential : Position ι → ℝ)
    (trajectory₁ trajectory₂ : ParameterizedTrajectoryFamily ι) :
    XuProposition42TVConclusion potential trajectory₁ trajectory₂ ↔
      XuProposition42MaximalMismatchConclusion
        potential trajectory₁ trajectory₂ := by
  classical
  constructor
  · intro h δ hδ
    rcases h δ hδ with ⟨ε0, hε0, L0, hL0, hbound⟩
    refine ⟨ε0, hε0, L0, hL0, ?_⟩
    intro ε hεpos hε L hlength
    have hmax := McmcLean.Finite.maximalCoupling_isMaximal
      (trajectoryIndexPMF potential (trajectory₁ ε L))
      (trajectoryIndexPMF potential (trajectory₂ ε L))
    rw [hmax.mismatchMass_eq_totalVariation]
    exact hbound ε hεpos hε L hlength
  · intro h δ hδ
    rcases h δ hδ with ⟨ε0, hε0, L0, hL0, hbound⟩
    refine ⟨ε0, hε0, L0, hL0, ?_⟩
    intro ε hεpos hε L hlength
    have hmax := McmcLean.Finite.maximalCoupling_isMaximal
      (trajectoryIndexPMF potential (trajectory₁ ε L))
      (trajectoryIndexPMF potential (trajectory₂ ε L))
    rw [← hmax.mismatchMass_eq_totalVariation]
    exact hbound ε hεpos hε L hlength

/-- A uniform Hamiltonian-error criterion sufficient for Proposition 4.2.
The remaining numerical analysis may choose a different error radius for each
admissible `(ε,L)`, but its normalized-Boltzmann envelope must fit inside the
requested TV tolerance uniformly under common thresholds. -/
def XuProposition42EnergyCriterion
    (potential : Position ι → ℝ)
    (trajectory₁ trajectory₂ : ParameterizedTrajectoryFamily ι) : Prop :=
  ∀ δ : ENNReal, 0 < δ →
    ∃ ε0 : ℝ, 0 < ε0 ∧
      ∃ L0 : ℕ, 1 ≤ L0 ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 →
          ∀ L : ℕ, ε * (L : ℝ) < ε0 * (L0 : ℝ) →
            ∃ radius : ℝ, 0 ≤ radius ∧
              (ENNReal.ofReal (Real.exp radius)) ^ 2 - 1 < δ ∧
              ∀ i,
                |energy potential (trajectory₁ ε L i) -
                  energy potential (trajectory₂ ε L i)| ≤ radius

/-- Uniformly vanishing Hamiltonian error supplies the envelope-valued energy
criterion. -/
theorem XuProposition42UniformEnergyError.energyCriterion
    (potential : Position ι → ℝ)
    (trajectory₁ trajectory₂ : ParameterizedTrajectoryFamily ι)
    (h : XuProposition42UniformEnergyError potential trajectory₁ trajectory₂) :
    XuProposition42EnergyCriterion potential trajectory₁ trajectory₂ := by
  intro δ hδ
  rcases exists_pos_expSqTotalVariationBound_lt hδ with
    ⟨radius, hradius, henvelope⟩
  rcases h radius hradius with ⟨ε0, hε0, L0, hL0, herror⟩
  refine ⟨ε0, hε0, L0, hL0, ?_⟩
  intro ε hεpos hε L hlength
  exact ⟨radius, hradius.le, henvelope,
    herror ε hεpos hε L hlength⟩

/-- Uniform Hamiltonian error control implies the exact TV conclusion of
Proposition 4.2. -/
theorem XuProposition42EnergyCriterion.tvConclusion
    (potential : Position ι → ℝ)
    (trajectory₁ trajectory₂ : ParameterizedTrajectoryFamily ι)
    (h : XuProposition42EnergyCriterion potential trajectory₁ trajectory₂) :
    XuProposition42TVConclusion potential trajectory₁ trajectory₂ := by
  intro δ hδ
  rcases h δ hδ with ⟨ε0, hε0, L0, hL0, hbound⟩
  refine ⟨ε0, hε0, L0, hL0, ?_⟩
  intro ε hεpos hε L hlength
  rcases hbound ε hεpos hε L hlength with
    ⟨radius, hradius, henvelope, henergy⟩
  exact (trajectoryIndexPMF_totalVariation_le_of_abs_energy_sub_le
    potential (trajectory₁ ε L) (trajectory₂ ε L) hradius henergy).trans_lt
      henvelope

/-- Therefore uniform vanishing of the trajectory-energy discrepancy proves
the exact TV conclusion of Proposition 4.2. -/
theorem XuProposition42UniformEnergyError.tvConclusion
    (potential : Position ι → ℝ)
    (trajectory₁ trajectory₂ : ParameterizedTrajectoryFamily ι)
    (h : XuProposition42UniformEnergyError potential trajectory₁ trajectory₂) :
    XuProposition42TVConclusion potential trajectory₁ trajectory₂ :=
  (h.energyCriterion potential trajectory₁ trajectory₂).tvConclusion
    potential trajectory₁ trajectory₂

/-- The same numerical error property proves the maximal coupling's uniform
unequal-index probability bound. -/
theorem XuProposition42UniformEnergyError.maximalMismatchConclusion
    (potential : Position ι → ℝ)
    (trajectory₁ trajectory₂ : ParameterizedTrajectoryFamily ι)
    (h : XuProposition42UniformEnergyError potential trajectory₁ trajectory₂) :
    XuProposition42MaximalMismatchConclusion
      potential trajectory₁ trajectory₂ :=
  (xuProposition42TVConclusion_iff_maximalMismatch
    potential trajectory₁ trajectory₂).mp
      (h.tvConclusion potential trajectory₁ trajectory₂)

/-- Uniform centered energy conservation proves Proposition 4.2 without any
assumption that the two baseline Hamiltonians approach each other. -/
theorem XuProposition42UniformCenteredEnergyError.tvConclusion
    (potential : Position ι → ℝ)
    (trajectory₁ trajectory₂ : ParameterizedTrajectoryFamily ι)
    (h : XuProposition42UniformCenteredEnergyError
      potential trajectory₁ trajectory₂) :
    XuProposition42TVConclusion potential trajectory₁ trajectory₂ := by
  intro δ hδ
  rcases exists_pos_expSqTotalVariationBound_lt hδ with
    ⟨envelopeRadius, henvelopeRadius, henvelope⟩
  have hhalf : 0 < envelopeRadius / 2 := half_pos henvelopeRadius
  rcases h (envelopeRadius / 2) hhalf with
    ⟨ε0, hε0, L0, hL0, herror⟩
  refine ⟨ε0, hε0, L0, hL0, ?_⟩
  intro ε hεpos hε L hlength
  rcases herror ε hεpos hε L hlength with
    ⟨center₁, center₂, herror₁, herror₂⟩
  apply (trajectoryIndexPMF_totalVariation_le_of_centered_energy
    potential (trajectory₁ ε L) (trajectory₂ ε L)
      center₁ center₂ (envelopeRadius / 2) (envelopeRadius / 2)
      hhalf.le hhalf.le herror₁ herror₂).trans_lt
  simpa only [add_halves] using henvelope

/-- The centered numerical premise also proves the equivalent maximal
unequal-index statement. -/
theorem XuProposition42UniformCenteredEnergyError.maximalMismatchConclusion
    (potential : Position ι → ℝ)
    (trajectory₁ trajectory₂ : ParameterizedTrajectoryFamily ι)
    (h : XuProposition42UniformCenteredEnergyError
      potential trajectory₁ trajectory₂) :
    XuProposition42MaximalMismatchConclusion
      potential trajectory₁ trajectory₂ :=
  (xuProposition42TVConclusion_iff_maximalMismatch
    potential trajectory₁ trajectory₂).mp
      (h.tvConclusion potential trajectory₁ trajectory₂)

/-- Uniform centered energy conservation for every shared origin proves the
origin-uniform TV conclusion. -/
theorem XuProposition42AllOriginsCenteredEnergyError.tvConclusion
    (potential : Position ι → ℝ)
    (trajectory₁ trajectory₂ : ParameterizedOriginTrajectoryFamily ι)
    (h : XuProposition42AllOriginsCenteredEnergyError
      potential trajectory₁ trajectory₂) :
    XuProposition42AllOriginsTVConclusion
      potential trajectory₁ trajectory₂ := by
  intro δ hδ
  rcases exists_pos_expSqTotalVariationBound_lt hδ with
    ⟨envelopeRadius, henvelopeRadius, henvelope⟩
  have hhalf : 0 < envelopeRadius / 2 := half_pos henvelopeRadius
  rcases h (envelopeRadius / 2) hhalf with
    ⟨ε0, hε0, L0, hL0, herror⟩
  refine ⟨ε0, hε0, L0, hL0, ?_⟩
  intro ε hεpos hε L hlength origin
  rcases herror ε hεpos hε L hlength origin with
    ⟨center₁, center₂, herror₁, herror₂⟩
  apply (trajectoryIndexPMF_totalVariation_le_of_centered_energy
    potential (trajectory₁ ε L origin) (trajectory₂ ε L origin)
      center₁ center₂ (envelopeRadius / 2) (envelopeRadius / 2)
      hhalf.le hhalf.le herror₁ herror₂).trans_lt
  simpa only [add_halves] using henvelope

/-- The supplement's locally uniform leapfrog energy estimate implies the
uniform centered-energy premise for the actual randomized-origin trajectories
from any two fixed phase points. -/
theorem LocallyUniformQuadraticLeapfrogEnergyError.allOriginsCenteredEnergy
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (herror : LocallyUniformQuadraticLeapfrogEnergyError potential gradient)
    (z₁ z₂ : PhaseSpace ι) :
    XuProposition42AllOriginsCenteredEnergyError potential
      (offsetLeapfrogOriginTrajectoryFamily gradient z₁)
      (offsetLeapfrogOriginTrajectoryFamily gradient z₂) := by
  intro radius hradius
  let R := max (euclideanPhaseSize z₁) (euclideanPhaseSize z₂)
  rcases abs_energy_signedLeapfrog_sub_le_of_horizon hreg herror
      (R := R) (T := 1) with ⟨C, hC, hbound⟩
  have hdenom : 0 < C + 1 := by linarith
  let ε0 := min 1 (radius / (C + 1))
  have hε0 : 0 < ε0 := by
    dsimp [ε0]
    exact lt_min zero_lt_one (div_pos hradius hdenom)
  refine ⟨ε0, hε0, 1, by simp, ?_⟩
  intro ε hεpos hε L hlength origin
  refine ⟨energy potential z₁, energy potential z₂, ?_, ?_⟩
  · intro i
    have hεone : |ε| ≤ 1 := by
      rw [abs_of_pos hεpos]
      exact hε.le.trans (min_le_left _ _)
    have hindex : Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) ≤ L := by
      have hi : i.val ≤ L := by omega
      have ho : origin.val ≤ L := by omega
      omega
    have hcast :
        (Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) : ℝ) ≤ L := by
      exact_mod_cast hindex
    have hhor :
        (Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) : ℝ) * |ε| ≤ 1 := by
      rw [abs_of_pos hεpos]
      have hε0one : ε0 ≤ 1 := min_le_left _ _
      calc
        _ ≤ (L : ℝ) * ε := mul_le_mul_of_nonneg_right hcast hεpos.le
        _ = ε * (L : ℝ) := mul_comm _ _
        _ ≤ ε0 := by simpa using hlength.le
        _ ≤ 1 := hε0one
    apply (hbound hεone ((i.val : ℤ) - (origin.val : ℤ)) hhor z₁
      (le_max_left _ _)).trans
    simp only [abs_of_pos hεpos, mul_one]
    have hsmall : ε < radius / (C + 1) :=
      hε.trans_le (min_le_right _ _)
    have hproduct : ε * (C + 1) < radius :=
      (lt_div_iff₀ hdenom).mp hsmall
    nlinarith

  · intro i
    have hεone : |ε| ≤ 1 := by
      rw [abs_of_pos hεpos]
      exact hε.le.trans (min_le_left _ _)
    have hindex : Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) ≤ L := by
      have hi : i.val ≤ L := by omega
      have ho : origin.val ≤ L := by omega
      omega
    have hcast :
        (Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) : ℝ) ≤ L := by
      exact_mod_cast hindex
    have hhor :
        (Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) : ℝ) * |ε| ≤ 1 := by
      rw [abs_of_pos hεpos]
      have hε0one : ε0 ≤ 1 := min_le_left _ _
      calc
        _ ≤ (L : ℝ) * ε := mul_le_mul_of_nonneg_right hcast hεpos.le
        _ = ε * (L : ℝ) := mul_comm _ _
        _ ≤ ε0 := by simpa using hlength.le
        _ ≤ 1 := hε0one
    apply (hbound hεone ((i.val : ℤ) - (origin.val : ℤ)) hhor z₂
      (le_max_right _ _)).trans
    simp only [abs_of_pos hεpos, mul_one]
    have hsmall : ε < radius / (C + 1) :=
      hε.trans_le (min_le_right _ _)
    have hproduct : ε * (C + 1) < radius :=
      (lt_div_iff₀ hdenom).mp hsmall
    nlinarith

/-- Equation (18)'s uniform local numerical estimate discharges Proposition
4.2 for every shared origin. -/
theorem LocallyUniformQuadraticLeapfrogEnergyError.allOriginsTVConclusion
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (herror : LocallyUniformQuadraticLeapfrogEnergyError potential gradient)
    (z₁ z₂ : PhaseSpace ι) :
    XuProposition42AllOriginsTVConclusion potential
      (offsetLeapfrogOriginTrajectoryFamily gradient z₁)
      (offsetLeapfrogOriginTrajectoryFamily gradient z₂) :=
  (herror.allOriginsCenteredEnergy hreg z₁ z₂).tvConclusion _ _ _

/-- Consequently, the actual uniform-origin maximal selection law chooses
unequal indices with probability tending uniformly to zero. -/
theorem LocallyUniformQuadraticLeapfrogEnergyError.randomizedMaximalMismatch
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (herror : LocallyUniformQuadraticLeapfrogEnergyError potential gradient)
    (z₁ z₂ : PhaseSpace ι) :
    XuProposition42RandomizedMaximalMismatchConclusion potential
      (offsetLeapfrogOriginTrajectoryFamily gradient z₁)
      (offsetLeapfrogOriginTrajectoryFamily gradient z₂) :=
  (xuProposition42AveragedOriginTVConclusion_iff_randomizedMaximalMismatch
    potential (offsetLeapfrogOriginTrajectoryFamily gradient z₁)
      (offsetLeapfrogOriginTrajectoryFamily gradient z₂)).mp
    ((herror.allOriginsTVConclusion hreg z₁ z₂).averagedOrigin _ _ _)

/-- General-potential Proposition 4.2, uniformly conditional on every shared
trajectory origin. Assumption 1 is sufficient for this numerical statement;
the paper's local strong-convexity Assumption 2 enters the later contraction
argument. -/
theorem RegularPotential.xuProposition42AllOrigins
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (z₁ z₂ : PhaseSpace ι) :
    XuProposition42AllOriginsTVConclusion potential
      (offsetLeapfrogOriginTrajectoryFamily gradient z₁)
      (offsetLeapfrogOriginTrajectoryFamily gradient z₂) :=
  hreg.locallyUniformQuadraticLeapfrogEnergyError.allOriginsTVConclusion
    hreg z₁ z₂

/-- General-potential Proposition 4.2 in the concrete randomized maximal-
coupling form: the probability of unequal selected indices tends uniformly to
zero in the paper's step-size/integration-length regime. -/
theorem RegularPotential.xuProposition42RandomizedMaximalMismatch
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (z₁ z₂ : PhaseSpace ι) :
    XuProposition42RandomizedMaximalMismatchConclusion potential
      (offsetLeapfrogOriginTrajectoryFamily gradient z₁)
      (offsetLeapfrogOriginTrajectoryFamily gradient z₂) :=
  hreg.locallyUniformQuadraticLeapfrogEnergyError.randomizedMaximalMismatch
    hreg z₁ z₂

/-- Proposition 4.2's convergence mechanism in trajectory form: if the
uniform Hamiltonian discrepancy of paired finite trajectories tends to zero,
then their multinomial index laws converge in total variation. -/
theorem trajectoryIndexPMF_totalVariation_tendsto_zero_of_energy
    {κ : Type*} {l : Filter κ} (potential : Position ι → ℝ) {L : ℕ}
    (trajectory₁ trajectory₂ : κ → Fin (L + 1) → PhaseSpace ι)
    (radius : κ → ℝ)
    (hradius : Filter.Tendsto radius l (nhds 0))
    (henergy : ∀ᶠ k in l, ∀ i,
      |energy potential (trajectory₁ k i) -
        energy potential (trajectory₂ k i)| ≤ radius k) :
    Filter.Tendsto
      (fun k => McmcLean.Finite.totalVariation
        (trajectoryIndexPMF potential (trajectory₁ k))
        (trajectoryIndexPMF potential (trajectory₂ k)))
      l (nhds 0) := by
  apply totalVariation_tendsto_zero_of_le_expSqBound
    (fun k => trajectoryIndexPMF potential (trajectory₁ k))
    (fun k => trajectoryIndexPMF potential (trajectory₂ k)) radius hradius
  filter_upwards [henergy] with k hk
  apply trajectoryIndexPMF_totalVariation_le_of_abs_energy_sub_le
  · exact le_trans (abs_nonneg _) (hk 0)
  · exact hk

/-- Proposition 4.2 reduced to numerical energy error against exact
Hamiltonian reference curves. With shared reference momentum at the initial
time, the exact curves' initial Hamiltonian gap is exactly their potential
gap. Thus the two numerical errors and the initial potential discrepancy give
an explicit total-variation bound for the multinomial trajectory laws. -/
theorem trajectoryIndexPMF_totalVariation_le_of_exact_curve_errors
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (hcurve₁ : IsHamiltonianCurve gradient q₁ p₁)
    (hcurve₂ : IsHamiltonianCurve gradient q₂ p₂)
    {L : ℕ} (trajectory₁ trajectory₂ : Fin (L + 1) → PhaseSpace ι)
    (time : Fin (L + 1) → ℝ) (initialTime : ℝ)
    {δ₁ δ₀ δ₂ : ℝ} (hδ₁ : 0 ≤ δ₁) (hδ₀ : 0 ≤ δ₀) (hδ₂ : 0 ≤ δ₂)
    (hshared : p₁ initialTime = p₂ initialTime)
    (hinitial : |potential (q₁ initialTime) - potential (q₂ initialTime)| ≤ δ₀)
    (herror₁ : ∀ i,
      |energy potential (trajectory₁ i) -
        energy potential (q₁ (time i), p₁ (time i))| ≤ δ₁)
    (herror₂ : ∀ i,
      |energy potential (q₂ (time i), p₂ (time i)) -
        energy potential (trajectory₂ i)| ≤ δ₂) :
    McmcLean.Finite.totalVariation
        (trajectoryIndexPMF potential trajectory₁)
        (trajectoryIndexPMF potential trajectory₂) ≤
      (ENNReal.ofReal (Real.exp (δ₁ + δ₀ + δ₂))) ^ 2 - 1 := by
  apply trajectoryIndexPMF_totalVariation_le_of_abs_energy_sub_le
  · positivity
  · intro i
    apply le_trans
      (abs_energy_sub_le_of_exact_curve_errors hreg hcurve₁ hcurve₂
        (trajectory₁ i) (trajectory₂ i) (time i) initialTime δ₁ δ₂
        (herror₁ i) (herror₂ i))
    have hexact :
        |energy potential (q₁ initialTime, p₁ initialTime) -
          energy potential (q₂ initialTime, p₂ initialTime)| =
        |potential (q₁ initialTime) - potential (q₂ initialTime)| := by
      simp only [energy, hshared]
      congr 1
      ring
    rw [hexact]
    gcongr

/-- On a compact position region, sufficiently close paired positions give a
uniform total-variation bound for multinomial trajectory selection. Momentum
errors enter through the exact quadratic kinetic-energy estimate. -/
theorem exists_uniform_trajectoryIndexPMF_totalVariation_bound
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} (hS : IsCompact S)
    {η : ℝ} (hη : 0 < η) {δp P : ℝ} :
    ∃ δ > 0, ∀ {L : ℕ}
      (trajectory₁ trajectory₂ : Fin (L + 1) → PhaseSpace ι),
      (∀ i, (trajectory₁ i).1 ∈ S) →
      (∀ i, (trajectory₂ i).1 ∈ S) →
      (∀ i, euclideanNorm ((trajectory₁ i).1 - (trajectory₂ i).1) ≤ δ) →
      (∀ i, euclideanNorm ((trajectory₁ i).2 - (trajectory₂ i).2) ≤ δp) →
      (∀ i, euclideanNorm (trajectory₁ i).2 +
        euclideanNorm (trajectory₂ i).2 ≤ P) →
      McmcLean.Finite.totalVariation
          (trajectoryIndexPMF potential trajectory₁)
          (trajectoryIndexPMF potential trajectory₂) ≤
        (ENNReal.ofReal
          (Real.exp (η + (1 / 2 : ℝ) * δp * P))) ^ 2 - 1 := by
  rcases hreg.exists_uniform_potential_error_euclidean hS hη with
    ⟨δ, hδ, hpotential⟩
  refine ⟨δ, hδ, ?_⟩
  intro L trajectory₁ trajectory₂ hmem₁ hmem₂ hposition hmomentum hsize
  apply trajectoryIndexPMF_totalVariation_le_of_phase_error
    potential trajectory₁ trajectory₂
  · intro i
    exact hpotential _ (hmem₁ i) _ (hmem₂ i) (hposition i)
  · exact hmomentum
  · exact hsize

/-- Compact-uniform form of Proposition 4.2 for the actual randomized-origin
leapfrog trajectories. For positions in a compact set and shared momentum
below a kinetic-energy cutoff, one step-size threshold makes every conditional
trajectory-index total variation smaller than an arbitrary positive tolerance,
uniformly over all origins and lengths in a bounded integration horizon. -/
theorem RegularPotential.exists_uniform_offsetTrajectory_totalVariation_lt
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {K : Set (Position ι)} (hK : IsCompact K)
    {k0 T : ℝ} (hk0 : 0 ≤ k0) (hT : 0 ≤ T)
    {δ : ENNReal} (hδ : 0 < δ) :
    ∃ εbar > 0, ∀ {ε : ℝ}, 0 < ε → ε < εbar →
      ∀ {L : ℕ}, ε * (L : ℝ) ≤ T →
        ∀ (origin : Fin (L + 1)), ∀ q₁ ∈ K, ∀ q₂ ∈ K,
          ∀ p : Momentum ι, kineticEnergy p ≤ k0 →
            McmcLean.Finite.totalVariation
                (trajectoryIndexPMF potential
                  (offsetLeapfrogTrajectory gradient ε origin (q₁, p)))
                (trajectoryIndexPMF potential
                  (offsetLeapfrogTrajectory gradient ε origin (q₂, p))) < δ := by
  obtain ⟨M, hM, hphase⟩ :=
    McmcLean.Hamiltonian.IsCompact.exists_euclideanPhaseSize_bound_of_kineticEnergy_le
      hK hk0
  obtain ⟨C, hC, henergy⟩ :=
    abs_energy_signedLeapfrog_sub_le_of_horizon hreg
      hreg.locallyUniformQuadraticLeapfrogEnergyError (R := M) (T := T)
  obtain ⟨radius, hradius, henvelope⟩ :=
    exists_pos_expSqTotalVariationBound_lt hδ
  have hden : 0 < 2 * (C * T + 1) := by
    have hCT : 0 ≤ C * T := mul_nonneg hC hT
    positivity
  let εbar := min 1 (radius / (2 * (C * T + 1)))
  have hεbar : 0 < εbar := by
    dsimp [εbar]
    exact lt_min zero_lt_one (div_pos hradius hden)
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hεpos hε L horizon origin q₁ hq₁ q₂ hq₂ p hp
  have hεone : |ε| ≤ 1 := by
    rw [abs_of_pos hεpos]
    exact hε.le.trans (min_le_left _ _)
  have hsmall : ε < radius / (2 * (C * T + 1)) :=
    hε.trans_le (min_le_right _ _)
  have hproduct : ε * (2 * (C * T + 1)) < radius :=
    (lt_div_iff₀ hden).mp hsmall
  have herrorRadius : C * T * |ε| ≤ radius / 2 := by
    rw [abs_of_pos hεpos]
    have hCT : 0 ≤ C * T := mul_nonneg hC hT
    nlinarith
  have hindexHorizon : ∀ i : Fin (L + 1),
      (Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) : ℝ) * |ε| ≤ T := by
    intro i
    have hindex : Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) ≤ L := by
      omega
    have hcast :
        (Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) : ℝ) ≤ L := by
      exact_mod_cast hindex
    rw [abs_of_pos hεpos]
    exact (mul_le_mul_of_nonneg_right hcast hεpos.le).trans
      (by simpa only [mul_comm] using horizon)
  have henergy₁ : ∀ i,
      |energy potential
          (offsetLeapfrogTrajectory gradient ε origin (q₁, p) i) -
        energy potential (q₁, p)| ≤ radius / 2 := by
    intro i
    exact (henergy hεone ((i.val : ℤ) - (origin.val : ℤ))
      (hindexHorizon i) (q₁, p) (hphase q₁ hq₁ p hp)).trans herrorRadius
  have henergy₂ : ∀ i,
      |energy potential
          (offsetLeapfrogTrajectory gradient ε origin (q₂, p) i) -
        energy potential (q₂, p)| ≤ radius / 2 := by
    intro i
    exact (henergy hεone ((i.val : ℤ) - (origin.val : ℤ))
      (hindexHorizon i) (q₂, p) (hphase q₂ hq₂ p hp)).trans herrorRadius
  apply (trajectoryIndexPMF_totalVariation_le_of_centered_energy
    potential
    (offsetLeapfrogTrajectory gradient ε origin (q₁, p))
    (offsetLeapfrogTrajectory gradient ε origin (q₂, p))
    (energy potential (q₁, p)) (energy potential (q₂, p))
    (radius / 2) (radius / 2) (by positivity) (by positivity)
    henergy₁ henergy₂).trans_lt
  simpa only [add_halves] using henvelope

end McmcLean.Hamiltonian
