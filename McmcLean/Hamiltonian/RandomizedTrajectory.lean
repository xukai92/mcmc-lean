import McmcLean.Hamiltonian.Leapfrog
import Mathlib.Algebra.Group.End

/-!
# Randomized forward/backward leapfrog trajectories

Multinomial HMC first chooses the location of the current state in a finite
trajectory, then integrates backward and forward around that location. This
module represents the construction using integer powers of the leapfrog
permutation. The representation makes the essential re-rooting symmetry an
algebraic identity: choosing any trajectory point as the new current state and
its index as the new origin recovers the same indexed trajectory.
-/

namespace McmcLean.Hamiltonian

variable {ι : Type*}

/-- One leapfrog step as a permutation, with the negative step as inverse. -/
noncomputable def leapfrogPerm (gradient : Position ι → Position ι) (ε : ℝ) :
    Equiv.Perm (PhaseSpace ι) where
  toFun := leapfrog gradient ε
  invFun := leapfrog gradient (-ε)
  left_inv := leapfrog_neg_comp_leapfrog gradient ε
  right_inv z := by
    simpa only [neg_neg] using leapfrog_neg_comp_leapfrog gradient (-ε) z

@[simp]
theorem coe_leapfrogPerm (gradient : Position ι → Position ι) (ε : ℝ) :
    ⇑(leapfrogPerm gradient ε) = leapfrog gradient ε :=
  rfl

@[simp]
theorem coe_leapfrogPerm_inv (gradient : Position ι → Position ι) (ε : ℝ) :
    ⇑((leapfrogPerm gradient ε)⁻¹) = leapfrog gradient (-ε) :=
  rfl

@[simp]
theorem leapfrogPerm_apply (gradient : Position ι → Position ι) (ε : ℝ)
    (z : PhaseSpace ι) :
    leapfrogPerm gradient ε z = leapfrog gradient ε z :=
  rfl

@[simp]
theorem leapfrogPerm_symm_apply (gradient : Position ι → Position ι) (ε : ℝ)
    (z : PhaseSpace ι) :
    (leapfrogPerm gradient ε).symm z = leapfrog gradient (-ε) z :=
  rfl

/-- The phase point reached after a signed number of leapfrog steps. -/
noncomputable def signedLeapfrog
    (gradient : Position ι → Position ι) (ε : ℝ) (n : ℤ)
    (z : PhaseSpace ι) : PhaseSpace ι :=
  (leapfrogPerm gradient ε ^ n) z

@[simp]
theorem signedLeapfrog_zero (gradient : Position ι → Position ι) (ε : ℝ)
    (z : PhaseSpace ι) :
    signedLeapfrog gradient ε 0 z = z := by
  simp [signedLeapfrog]

@[simp]
theorem signedLeapfrog_one (gradient : Position ι → Position ι) (ε : ℝ)
    (z : PhaseSpace ι) :
    signedLeapfrog gradient ε 1 z = leapfrog gradient ε z := by
  simp [signedLeapfrog]

@[simp]
theorem signedLeapfrog_neg_one (gradient : Position ι → Position ι) (ε : ℝ)
    (z : PhaseSpace ι) :
    signedLeapfrog gradient ε (-1) z = leapfrog gradient (-ε) z := by
  simp [signedLeapfrog]

theorem signedLeapfrog_add (gradient : Position ι → Position ι) (ε : ℝ)
    (m n : ℤ) (z : PhaseSpace ι) :
    signedLeapfrog gradient ε (m + n) z =
      signedLeapfrog gradient ε m (signedLeapfrog gradient ε n z) := by
  simp only [signedLeapfrog, zpow_add, Equiv.Perm.mul_apply]

theorem measurable_signedLeapfrog
    {gradient : Position ι → Position ι} (hgradient : Measurable gradient)
    (ε : ℝ) (n : ℤ) :
    Measurable (signedLeapfrog gradient ε n) := by
  cases n with
  | ofNat n =>
      change Measurable fun z => ((leapfrogPerm gradient ε) ^ n) z
      simpa only [Equiv.Perm.coe_pow, coe_leapfrogPerm] using
        (measurable_leapfrog hgradient ε).iterate n
  | negSucc n =>
      change Measurable fun z =>
        (((leapfrogPerm gradient ε) ^ (n + 1))⁻¹) z
      rw [← inv_pow]
      simpa only [Equiv.Perm.coe_pow, coe_leapfrogPerm_inv] using
        (measurable_leapfrog hgradient (-ε)).iterate (n + 1)

/-- Signed leapfrog iteration is continuous when the gradient is continuous. -/
theorem continuous_signedLeapfrog
    {gradient : Position ι → Position ι} (hgradient : Continuous gradient)
    (ε : ℝ) (n : ℤ) :
    Continuous (signedLeapfrog gradient ε n) := by
  cases n with
  | ofNat n =>
      change Continuous fun z => ((leapfrogPerm gradient ε) ^ n) z
      simpa only [Equiv.Perm.coe_pow, coe_leapfrogPerm] using
        (continuous_leapfrog hgradient ε).iterate n
  | negSucc n =>
      change Continuous fun z =>
        (((leapfrogPerm gradient ε) ^ (n + 1))⁻¹) z
      rw [← inv_pow]
      simpa only [Equiv.Perm.coe_pow, coe_leapfrogPerm_inv] using
        (continuous_leapfrog hgradient (-ε)).iterate (n + 1)

/-- A length-`L + 1` leapfrog trajectory whose current state is placed at
`origin`. Indices below the origin are negative-time steps and indices above
it are positive-time steps. -/
noncomputable def offsetLeapfrogTrajectory
    (gradient : Position ι → Position ι) (ε : ℝ) {L : ℕ}
    (origin : Fin (L + 1)) (z : PhaseSpace ι) (i : Fin (L + 1)) :
    PhaseSpace ι :=
  signedLeapfrog gradient ε ((i.val : ℤ) - (origin.val : ℤ)) z

theorem measurable_offsetLeapfrogTrajectory
    {gradient : Position ι → Position ι} (hgradient : Measurable gradient)
    (ε : ℝ) {L : ℕ} (origin i : Fin (L + 1)) :
    Measurable fun z => offsetLeapfrogTrajectory gradient ε origin z i :=
  measurable_signedLeapfrog hgradient ε _

/-- Every fixed coordinate of an offset leapfrog trajectory is continuous in
the initial phase point when the gradient is continuous. -/
theorem continuous_offsetLeapfrogTrajectory
    {gradient : Position ι → Position ι} (hgradient : Continuous gradient)
    (ε : ℝ) {L : ℕ} (origin i : Fin (L + 1)) :
    Continuous fun z => offsetLeapfrogTrajectory gradient ε origin z i :=
  continuous_signedLeapfrog hgradient ε _

/-- Positions reached at any index of an offset trajectory from initial phase
points in `K`. -/
def offsetLeapfrogPositionSet
    (gradient : Position ι → Position ι) (ε : ℝ) {L : ℕ}
    (origin : Fin (L + 1)) (K : Set (PhaseSpace ι)) : Set (Position ι) :=
  ⋃ i, (fun z => (offsetLeapfrogTrajectory gradient ε origin z i).1) '' K

/-- For fixed numerical parameters, trajectories started in a compact phase
set have a compact finite union of reachable positions. -/
theorem IsCompact.offsetLeapfrogPositionSet
    {gradient : Position ι → Position ι} (hgradient : Continuous gradient)
    (ε : ℝ) {L : ℕ} (origin : Fin (L + 1))
    {K : Set (PhaseSpace ι)} (hK : IsCompact K) :
    IsCompact (offsetLeapfrogPositionSet gradient ε origin K) := by
  apply isCompact_iUnion
  intro i
  exact hK.image
    (continuous_fst.comp
      (continuous_offsetLeapfrogTrajectory hgradient ε origin i))

theorem offsetLeapfrogTrajectory_position_mem_positionSet
    (gradient : Position ι → Position ι) (ε : ℝ) {L : ℕ}
    (origin i : Fin (L + 1)) {K : Set (PhaseSpace ι)}
    {z : PhaseSpace ι} (hz : z ∈ K) :
    (offsetLeapfrogTrajectory gradient ε origin z i).1 ∈
      offsetLeapfrogPositionSet gradient ε origin K := by
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_image_of_mem _ hz⟩

@[simp]
theorem offsetLeapfrogTrajectory_origin
    (gradient : Position ι → Position ι) (ε : ℝ) {L : ℕ}
    (origin : Fin (L + 1)) (z : PhaseSpace ι) :
    offsetLeapfrogTrajectory gradient ε origin z origin = z := by
  simp [offsetLeapfrogTrajectory]

/-- Re-rooting a trajectory at one of its points leaves every indexed point
unchanged. This is the discrete orbit symmetry used in multinomial-HMC
detailed-balance arguments. -/
theorem offsetLeapfrogTrajectory_reroot
    (gradient : Position ι → Position ι) (ε : ℝ) {L : ℕ}
    (origin selected i : Fin (L + 1)) (z : PhaseSpace ι) :
    offsetLeapfrogTrajectory gradient ε selected
        (offsetLeapfrogTrajectory gradient ε origin z selected) i =
      offsetLeapfrogTrajectory gradient ε origin z i := by
  rw [offsetLeapfrogTrajectory, offsetLeapfrogTrajectory,
    offsetLeapfrogTrajectory, ← signedLeapfrog_add]
  congr 1
  omega

end McmcLean.Hamiltonian
