import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring

/-!
# Hamiltonian phase space and leapfrog integration

This module introduces the finite-dimensional deterministic layer required by
Hamiltonian Monte Carlo. Positions and momenta live in `ι → ℝ`; a phase point
is their product. For a supplied potential gradient, it defines the standard
unit-mass leapfrog update, momentum reversal, finite iterates, and trajectories.

The leapfrog map is proved measurable from measurability of the gradient and
is proved exactly reversible under momentum flip:

`flip (leapfrog ε (flip z)) = leapfrog (-ε) z`.

No energy-error or volume-preservation claim is made here. Those analytic
properties require differentiability and Jacobian hypotheses developed in a
later layer.
-/

open scoped BigOperators

namespace Mcmc.Hamiltonian

variable {ι : Type*} [Fintype ι]

/-- Finite-dimensional Euclidean position space. -/
abbrev Position (ι : Type*) := ι → ℝ

/-- Momentum uses the same Euclidean coordinate space. -/
abbrev Momentum (ι : Type*) := ι → ℝ

/-- Hamiltonian phase space of position/momentum pairs. -/
abbrev PhaseSpace (ι : Type*) := Position ι × Momentum ι

/-- Coordinatewise Euclidean inner product.  This is explicit because the
function-space topology on `ι → ℝ` uses the equivalent sup norm. -/
noncomputable def euclideanInner (x y : Position ι) : ℝ :=
  ∑ i, x i * y i

@[simp]
theorem euclideanInner_zero_left (x : Position ι) :
    euclideanInner 0 x = 0 := by simp [euclideanInner]

@[simp]
theorem euclideanInner_zero_right (x : Position ι) :
    euclideanInner x 0 = 0 := by simp [euclideanInner]

theorem euclideanInner_comm (x y : Position ι) :
    euclideanInner x y = euclideanInner y x := by
  unfold euclideanInner
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem euclideanInner_add_left (x y z : Position ι) :
    euclideanInner (x + y) z = euclideanInner x z + euclideanInner y z := by
  unfold euclideanInner
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem euclideanInner_add_right (x y z : Position ι) :
    euclideanInner x (y + z) = euclideanInner x y + euclideanInner x z := by
  rw [euclideanInner_comm, euclideanInner_add_left,
    euclideanInner_comm x y, euclideanInner_comm x z]

theorem euclideanInner_sub_left (x y z : Position ι) :
    euclideanInner (x - y) z = euclideanInner x z - euclideanInner y z := by
  unfold euclideanInner
  simp only [Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem euclideanInner_sub_right (x y z : Position ι) :
    euclideanInner x (y - z) = euclideanInner x y - euclideanInner x z := by
  rw [euclideanInner_comm, euclideanInner_sub_left,
    euclideanInner_comm x y, euclideanInner_comm x z]

theorem euclideanInner_smul_left (c : ℝ) (x y : Position ι) :
    euclideanInner (c • x) y = c * euclideanInner x y := by
  unfold euclideanInner
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem euclideanInner_smul_right (c : ℝ) (x y : Position ι) :
    euclideanInner x (c • y) = c * euclideanInner x y := by
  rw [euclideanInner_comm, euclideanInner_smul_left,
    euclideanInner_comm x y]

@[simp]
theorem euclideanInner_neg_right (x y : Position ι) :
    euclideanInner x (-y) = -euclideanInner x y := by
  simp [euclideanInner, Finset.sum_neg_distrib]

/-- Squared Euclidean norm in coordinates. -/
noncomputable def squaredEuclideanNorm (x : Position ι) : ℝ :=
  euclideanInner x x

/-- Euclidean norm in coordinates. -/
noncomputable def euclideanNorm (x : Position ι) : ℝ :=
  Real.sqrt (squaredEuclideanNorm x)

theorem squaredEuclideanNorm_nonneg (x : Position ι) :
    0 ≤ squaredEuclideanNorm x := by
  unfold squaredEuclideanNorm euclideanInner
  exact Finset.sum_nonneg fun i hi => mul_self_nonneg (x i)

@[simp]
theorem squaredEuclideanNorm_eq_zero {x : Position ι} :
    squaredEuclideanNorm x = 0 ↔ x = 0 := by
  unfold squaredEuclideanNorm euclideanInner
  exact (Finset.sum_eq_zero_iff_of_nonneg
    fun i hi => mul_self_nonneg (x i)).trans (by simp [funext_iff])

theorem squaredEuclideanNorm_pos {x : Position ι} (hx : x ≠ 0) :
    0 < squaredEuclideanNorm x :=
  lt_of_le_of_ne (squaredEuclideanNorm_nonneg x)
    (Ne.symm (squaredEuclideanNorm_eq_zero.not.mpr hx))

theorem euclideanNorm_nonneg (x : Position ι) : 0 ≤ euclideanNorm x :=
  Real.sqrt_nonneg _

@[simp]
theorem euclideanNorm_zero : euclideanNorm (0 : Position ι) = 0 := by
  simp [euclideanNorm, squaredEuclideanNorm, euclideanInner]

theorem euclideanNorm_sq (x : Position ι) :
    euclideanNorm x ^ 2 = squaredEuclideanNorm x := by
  unfold euclideanNorm
  exact Real.sq_sqrt (squaredEuclideanNorm_nonneg x)

/-- Every coordinate is bounded by the explicit Euclidean norm. -/
theorem abs_apply_le_euclideanNorm (x : Position ι) (i : ι) :
    |x i| ≤ euclideanNorm x := by
  rw [← sq_le_sq₀ (abs_nonneg _) (euclideanNorm_nonneg _), sq_abs,
    euclideanNorm_sq]
  unfold squaredEuclideanNorm euclideanInner
  simpa only [pow_two] using Finset.single_le_sum
    (s := Finset.univ) (f := fun j : ι => x j * x j)
    (fun j hj => mul_self_nonneg (x j)) (Finset.mem_univ i)

/-- Euclidean separation controls the ambient metric used by compactness and
uniform continuity. -/
theorem dist_le_euclideanNorm_sub (x y : Position ι) :
    dist x y ≤ euclideanNorm (x - y) := by
  rw [dist_pi_le_iff (euclideanNorm_nonneg _)]
  intro i
  rw [Real.dist_eq]
  simpa only [Pi.sub_apply] using abs_apply_le_euclideanNorm (x - y) i

/-- In the other direction, explicit Euclidean separation is bounded by a
dimension-dependent multiple of the finite-product metric. -/
theorem euclideanNorm_sub_le_card_succ_mul_dist (x y : Position ι) :
    euclideanNorm (x - y) ≤ ((Fintype.card ι : ℝ) + 1) * dist x y := by
  have hcoord : ∀ i : ι, |x i - y i| ≤ dist x y := by
    intro i
    simpa only [Real.dist_eq] using dist_le_pi_dist x y i
  have hsum : squaredEuclideanNorm (x - y) ≤
      (Fintype.card ι : ℝ) * dist x y ^ 2 := by
    unfold squaredEuclideanNorm euclideanInner
    calc
      ∑ i, (x - y) i * (x - y) i ≤ ∑ _i : ι, dist x y ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hsquare := (sq_le_sq₀ (abs_nonneg (x i - y i))
          (dist_nonneg)).mpr (hcoord i)
        simp only [Pi.sub_apply]
        calc
          (x i - y i) * (x i - y i) = (x i - y i) ^ 2 := by ring
          _ = |x i - y i| ^ 2 := (sq_abs _).symm
          _ ≤ dist x y ^ 2 := hsquare
      _ = (Fintype.card ι : ℝ) * dist x y ^ 2 := by simp
  rw [← sq_le_sq₀ (euclideanNorm_nonneg _)
    (mul_nonneg (by positivity) dist_nonneg), euclideanNorm_sq]
  have hcard : 0 ≤ (Fintype.card ι : ℝ) := by positivity
  have hdist : 0 ≤ dist x y := dist_nonneg
  nlinarith

/-- The explicit squared Euclidean norm is continuous for the finite-product
topology on positions. -/
theorem continuous_squaredEuclideanNorm :
    Continuous (squaredEuclideanNorm : Position ι → ℝ) := by
  unfold squaredEuclideanNorm euclideanInner
  fun_prop

/-- The explicit Euclidean norm is continuous for the finite-product
topology on positions. -/
theorem continuous_euclideanNorm :
    Continuous (euclideanNorm : Position ι → ℝ) := by
  unfold euclideanNorm
  exact Real.continuous_sqrt.comp continuous_squaredEuclideanNorm

theorem squaredEuclideanNorm_add (x y : Position ι) :
    squaredEuclideanNorm (x + y) =
      squaredEuclideanNorm x + 2 * euclideanInner x y +
        squaredEuclideanNorm y := by
  unfold squaredEuclideanNorm euclideanInner
  simp only [Pi.add_apply]
  calc
    ∑ i, (x i + y i) * (x i + y i) =
        ∑ i, (x i * x i + 2 * (x i * y i) + y i * y i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      rw [← Finset.mul_sum]

/-- Coordinatewise Cauchy--Schwarz inequality. -/
theorem euclideanInner_le_norm_mul_norm (x y : Position ι) :
    euclideanInner x y ≤ euclideanNorm x * euclideanNorm y := by
  unfold euclideanInner euclideanNorm squaredEuclideanNorm
  simpa only [euclideanInner, pow_two] using
    Real.sum_mul_le_sqrt_mul_sqrt Finset.univ x y

/-- Triangle inequality for the explicit Euclidean norm. -/
theorem euclideanNorm_add_le (x y : Position ι) :
    euclideanNorm (x + y) ≤ euclideanNorm x + euclideanNorm y := by
  unfold euclideanNorm
  rw [Real.sqrt_le_iff]
  constructor
  · exact add_nonneg (euclideanNorm_nonneg x) (euclideanNorm_nonneg y)
  · rw [squaredEuclideanNorm_add]
    have hinner := euclideanInner_le_norm_mul_norm x y
    unfold euclideanNorm at hinner
    have hx : (Real.sqrt (squaredEuclideanNorm x)) ^ 2 =
        squaredEuclideanNorm x :=
      Real.sq_sqrt (squaredEuclideanNorm_nonneg x)
    have hy : (Real.sqrt (squaredEuclideanNorm y)) ^ 2 =
        squaredEuclideanNorm y :=
      Real.sq_sqrt (squaredEuclideanNorm_nonneg y)
    nlinarith

/-- Homogeneity of the explicit Euclidean norm. -/
theorem euclideanNorm_smul (c : ℝ) (x : Position ι) :
    euclideanNorm (c • x) = |c| * euclideanNorm x := by
  unfold euclideanNorm squaredEuclideanNorm euclideanInner
  simp only [Pi.smul_apply, smul_eq_mul]
  have hsum : (∑ i, c * x i * (c * x i)) =
      c ^ 2 * ∑ i, x i * x i := by
    calc
      _ = ∑ i, c ^ 2 * (x i * x i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by rw [← Finset.mul_sum]
  rw [hsum]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

@[simp]
theorem euclideanNorm_neg (x : Position ι) :
    euclideanNorm (-x) = euclideanNorm x := by
  unfold euclideanNorm squaredEuclideanNorm euclideanInner
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp

/-- Absolute-value form of coordinatewise Cauchy--Schwarz. -/
theorem abs_euclideanInner_le_norm_mul_norm (x y : Position ι) :
    |euclideanInner x y| ≤ euclideanNorm x * euclideanNorm y := by
  apply abs_le.mpr
  constructor
  · have h := euclideanInner_le_norm_mul_norm x (-y)
    rw [euclideanInner_neg_right, euclideanNorm_neg] at h
    linarith
  · exact euclideanInner_le_norm_mul_norm x y

theorem euclideanNorm_sub_le (x y : Position ι) :
    euclideanNorm (x - y) ≤ euclideanNorm x + euclideanNorm y := by
  simpa only [sub_eq_add_neg, euclideanNorm_neg] using
    euclideanNorm_add_le x (-y)

/-- Polarized expansion of squared Euclidean norm. -/
theorem squaredEuclideanNorm_sub_smul (x y : Position ι) (c : ℝ) :
    squaredEuclideanNorm (x - c • y) =
      squaredEuclideanNorm x - 2 * c * euclideanInner x y +
        c ^ 2 * squaredEuclideanNorm y := by
  unfold squaredEuclideanNorm euclideanInner
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  calc
    ∑ i, (x i - c * y i) * (x i - c * y i) =
        ∑ i, (x i * x i - 2 * c * (x i * y i) +
          c ^ 2 * (y i * y i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [← Finset.mul_sum, ← Finset.mul_sum]

theorem squaredEuclideanNorm_smul (c : ℝ) (x : Position ι) :
    squaredEuclideanNorm (c • x) = c ^ 2 * squaredEuclideanNorm x := by
  unfold squaredEuclideanNorm euclideanInner
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    ∑ i, c * x i * (c * x i) = ∑ i, c ^ 2 * (x i * x i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by rw [← Finset.mul_sum]

@[simp]
theorem squaredEuclideanNorm_neg (x : Position ι) :
    squaredEuclideanNorm (-x) = squaredEuclideanNorm x := by
  unfold squaredEuclideanNorm euclideanInner
  simp

/-- Three-term squared Euclidean bound, in the `x + y - z` form used by the
relative-position leapfrog recurrence. -/
theorem squaredEuclideanNorm_add_sub_le_three
    (x y z : Position ι) :
    squaredEuclideanNorm (x + y - z) ≤
      3 * (squaredEuclideanNorm x + squaredEuclideanNorm y +
        squaredEuclideanNorm z) := by
  unfold squaredEuclideanNorm euclideanInner
  simp only [Pi.add_apply, Pi.sub_apply]
  calc
    ∑ i, (x i + y i - z i) * (x i + y i - z i) ≤
        ∑ i, 3 * (x i * x i + y i * y i + z i * z i) := by
      apply Finset.sum_le_sum
      intro i hi
      nlinarith [sq_nonneg (x i - y i), sq_nonneg (x i + z i),
        sq_nonneg (y i + z i)]
    _ = _ := by
      rw [← Finset.mul_sum]
      simp only [Finset.sum_add_distrib]

/-- Three-term squared Euclidean bound, in the `x - y - z` form used by the
relative-momentum leapfrog recurrence. -/
theorem squaredEuclideanNorm_sub_sub_le_three
    (x y z : Position ι) :
    squaredEuclideanNorm (x - y - z) ≤
      3 * (squaredEuclideanNorm x + squaredEuclideanNorm y +
        squaredEuclideanNorm z) := by
  simpa only [sub_eq_add_neg, squaredEuclideanNorm_neg] using
    squaredEuclideanNorm_add_sub_le_three x (-y) z

/-- Unit-mass quadratic kinetic energy. -/
noncomputable def kineticEnergy (p : Momentum ι) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, (p i) ^ 2

/-- A kinetic-energy cutoff gives the corresponding Euclidean momentum
radius. -/
theorem euclideanNorm_le_sqrt_two_mul_of_kineticEnergy_le
    {p : Momentum ι} {k0 : ℝ} (hk0 : 0 ≤ k0)
    (hp : kineticEnergy p ≤ k0) :
    euclideanNorm p ≤ Real.sqrt (2 * k0) := by
  apply (sq_le_sq₀ (euclideanNorm_nonneg p) (Real.sqrt_nonneg _)).mp
  rw [euclideanNorm_sq, Real.sq_sqrt (mul_nonneg (by norm_num) hk0)]
  unfold kineticEnergy at hp
  unfold squaredEuclideanNorm euclideanInner
  simp only [pow_two] at hp
  nlinarith

/-- Hamiltonian energy associated with a potential `potential`. -/
noncomputable def energy (potential : Position ι → ℝ)
    (z : PhaseSpace ι) : ℝ :=
  potential z.1 + kineticEnergy z.2

/-- Sum of explicit Euclidean position and momentum norms. -/
noncomputable def euclideanPhaseSize (z : PhaseSpace ι) : ℝ :=
  euclideanNorm z.1 + euclideanNorm z.2

theorem euclideanPhaseSize_nonneg (z : PhaseSpace ι) :
    0 ≤ euclideanPhaseSize z :=
  add_nonneg (euclideanNorm_nonneg _) (euclideanNorm_nonneg _)

theorem euclideanNorm_fst_le_phaseSize (z : PhaseSpace ι) :
    euclideanNorm z.1 ≤ euclideanPhaseSize z := by
  unfold euclideanPhaseSize
  exact le_add_of_nonneg_right (euclideanNorm_nonneg _)

theorem continuous_euclideanPhaseSize :
    Continuous (euclideanPhaseSize : PhaseSpace ι → ℝ) :=
  (continuous_euclideanNorm.comp continuous_fst).add
    (continuous_euclideanNorm.comp continuous_snd)

/-- Difference of quadratic kinetic energies in polarized form. -/
theorem kineticEnergy_sub (p₁ p₂ : Momentum ι) :
    kineticEnergy p₁ - kineticEnergy p₂ =
      (1 / 2 : ℝ) * euclideanInner (p₁ - p₂) (p₁ + p₂) := by
  unfold kineticEnergy euclideanInner
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Kinetic energy is locally Lipschitz with the explicit quadratic bound. -/
theorem abs_kineticEnergy_sub_le (p₁ p₂ : Momentum ι) :
    |kineticEnergy p₁ - kineticEnergy p₂| ≤
      (1 / 2 : ℝ) * euclideanNorm (p₁ - p₂) *
        (euclideanNorm p₁ + euclideanNorm p₂) := by
  rw [kineticEnergy_sub, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  apply le_trans (mul_le_mul_of_nonneg_left
    (abs_euclideanInner_le_norm_mul_norm (p₁ - p₂) (p₁ + p₂))
    (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have htriangle := euclideanNorm_add_le p₁ p₂
  nlinarith [euclideanNorm_nonneg (p₁ - p₂)]

/-- Hamiltonian discrepancy is controlled by a potential discrepancy and the
explicit quadratic kinetic-energy error. -/
theorem abs_energy_sub_le
    (potential : Position ι → ℝ) (z₁ z₂ : PhaseSpace ι) {δq : ℝ}
    (hpotential : |potential z₁.1 - potential z₂.1| ≤ δq) :
    |energy potential z₁ - energy potential z₂| ≤
      δq + (1 / 2 : ℝ) * euclideanNorm (z₁.2 - z₂.2) *
        (euclideanNorm z₁.2 + euclideanNorm z₂.2) := by
  unfold energy
  rw [show potential z₁.1 + kineticEnergy z₁.2 -
      (potential z₂.1 + kineticEnergy z₂.2) =
      (potential z₁.1 - potential z₂.1) +
        (kineticEnergy z₁.2 - kineticEnergy z₂.2) by ring]
  apply le_trans (abs_add_le _ _)
  exact add_le_add hpotential (abs_kineticEnergy_sub_le z₁.2 z₂.2)

/-- Negate momentum while retaining position. -/
def momentumFlip (z : PhaseSpace ι) : PhaseSpace ι :=
  (z.1, -z.2)

@[simp]
theorem kineticEnergy_neg (p : Momentum ι) :
    kineticEnergy (-p) = kineticEnergy p := by
  unfold kineticEnergy
  simp only [Pi.neg_apply, neg_sq]

@[simp]
theorem energy_momentumFlip (potential : Position ι → ℝ)
    (z : PhaseSpace ι) :
    energy potential (momentumFlip z) = energy potential z := by
  simp [energy, momentumFlip]

/-- Half momentum update used by leapfrog. -/
noncomputable def halfKick (gradient : Position ι → Position ι) (ε : ℝ)
    (q : Position ι) (p : Momentum ι) : Momentum ι :=
  p - (ε / 2) • gradient q

/-- Full position update at fixed momentum. -/
def drift (ε : ℝ) (q : Position ι) (p : Momentum ι) : Position ι :=
  q + ε • p

/-- One unit-mass velocity-Verlet/leapfrog update. -/
noncomputable def leapfrog (gradient : Position ι → Position ι) (ε : ℝ)
    (z : PhaseSpace ι) : PhaseSpace ι :=
  let pHalf := halfKick gradient ε z.1 z.2
  let qNext := drift ε z.1 pHalf
  let pNext := halfKick gradient ε qNext pHalf
  (qNext, pNext)

/-- Exact kinetic-energy change under an additive momentum kick. -/
theorem kineticEnergy_sub_smul_sub
    (p g : Momentum ι) (c : ℝ) :
    kineticEnergy (p - c • g) - kineticEnergy p =
      -c * euclideanInner p g +
        (c ^ 2 / 2) * squaredEuclideanNorm g := by
  unfold kineticEnergy euclideanInner squaredEuclideanNorm
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  calc
    (1 / 2 : ℝ) * ∑ i, (p i - c * g i) ^ 2 -
        (1 / 2 : ℝ) * ∑ i, p i ^ 2 =
      ∑ i, (-c * (p i * g i) + (c ^ 2 / 2) * (g i * g i)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
    _ = -c * ∑ i, p i * g i +
        (c ^ 2 / 2) * ∑ i, g i * g i := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- Exact decomposition of one leapfrog energy defect into the potential's
first-order Taylor remainder, a gradient-difference term, and a difference of
squared gradient norms. This exposes the cancellation responsible for the
quadratic local defect under a Lipschitz-gradient assumption. -/
theorem energy_leapfrog_sub_eq_taylorRemainder
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (z : PhaseSpace ι) :
    let pHalf := halfKick gradient ε z.1 z.2
    let qNext := drift ε z.1 pHalf
    energy potential (leapfrog gradient ε z) - energy potential z =
      (potential qNext - potential z.1 -
        euclideanInner (gradient z.1) (qNext - z.1)) +
      (ε / 2) * euclideanInner pHalf
        (gradient z.1 - gradient qNext) +
      (ε ^ 2 / 8) *
        (squaredEuclideanNorm (gradient qNext) -
          squaredEuclideanNorm (gradient z.1)) := by
  let pHalf := halfKick gradient ε z.1 z.2
  let qNext := drift ε z.1 pHalf
  change energy potential
      (qNext, halfKick gradient ε qNext pHalf) - energy potential z = _
  have hk₁ := kineticEnergy_sub_smul_sub pHalf (gradient qNext) (ε / 2)
  have hk₀ := kineticEnergy_sub_smul_sub z.2 (gradient z.1) (ε / 2)
  have hp : z.2 = pHalf + (ε / 2) • gradient z.1 := by
    dsimp [pHalf, halfKick]
    abel
  have hq : qNext - z.1 = ε • pHalf := by
    dsimp [qNext, drift]
    abel
  unfold energy
  change potential qNext + kineticEnergy (halfKick gradient ε qNext pHalf) -
      (potential z.1 + kineticEnergy z.2) =
    (potential qNext - potential z.1 -
        euclideanInner (gradient z.1) (qNext - z.1)) +
      (ε / 2) * euclideanInner pHalf
        (gradient z.1 - gradient qNext) +
      (ε ^ 2 / 8) *
        (squaredEuclideanNorm (gradient qNext) -
          squaredEuclideanNorm (gradient z.1))
  rw [show potential qNext + kineticEnergy (halfKick gradient ε qNext pHalf) -
      (potential z.1 + kineticEnergy z.2) =
      (potential qNext - potential z.1) +
        (kineticEnergy (halfKick gradient ε qNext pHalf) -
          kineticEnergy z.2) by ring]
  rw [show kineticEnergy (halfKick gradient ε qNext pHalf) -
      kineticEnergy z.2 =
      (kineticEnergy (halfKick gradient ε qNext pHalf) -
        kineticEnergy pHalf) + (kineticEnergy pHalf - kineticEnergy z.2) by ring]
  have hk₁' : kineticEnergy (halfKick gradient ε qNext pHalf) -
      kineticEnergy pHalf =
      -(ε / 2) * euclideanInner pHalf (gradient qNext) +
        ((ε / 2) ^ 2 / 2) * squaredEuclideanNorm (gradient qNext) := by
    simpa only [halfKick] using hk₁
  rw [hk₁']
  have hk₀' : kineticEnergy pHalf - kineticEnergy z.2 =
      -(ε / 2) * euclideanInner z.2 (gradient z.1) +
        ((ε / 2) ^ 2 / 2) * squaredEuclideanNorm (gradient z.1) := by
    simpa only [pHalf, halfKick] using hk₀
  rw [hk₀', hq, hp]
  unfold squaredEuclideanNorm euclideanInner
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  ring_nf
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  ring_nf
  have hsum :
      (∑ x, (ε * pHalf x * gradient qNext x * (-1 / 2) +
          ε ^ 2 * gradient qNext x ^ 2 * (1 / 8) +
          (ε * pHalf x * gradient z.1 x * (-1 / 2) +
            ε ^ 2 * gradient z.1 x ^ 2 * (-1 / 4)) +
          ε ^ 2 * gradient z.1 x ^ 2 * (1 / 8))) =
        ∑ x, (ε ^ 2 * gradient qNext x ^ 2 * (1 / 8) +
          ε ^ 2 * gradient z.1 x ^ 2 * (-1 / 8) -
          ε * gradient z.1 x * pHalf x +
          (ε * pHalf x * gradient z.1 x * (1 / 2) +
            ε * pHalf x * gradient qNext x * (-1 / 2))) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
  simpa only [Finset.sum_add_distrib, Finset.sum_sub_distrib, add_assoc,
    sub_eq_add_neg] using
    congrArg (fun t : ℝ => potential qNext - potential z.1 + t) hsum

/-- `n` successive leapfrog updates. -/
noncomputable def leapfrogN (gradient : Position ι → Position ι) (ε : ℝ) (n : ℕ)
    (z : PhaseSpace ι) : PhaseSpace ι :=
  (leapfrog gradient ε)^[n] z

/-- The phase point at each integer time along a finite leapfrog trajectory.
The definition is total on `ℕ`; consumers restrict it to their chosen finite
index set. -/
noncomputable def leapfrogTrajectory (gradient : Position ι → Position ι) (ε : ℝ)
    (z : PhaseSpace ι) (n : ℕ) : PhaseSpace ι :=
  leapfrogN gradient ε n z

omit [Fintype ι] in
theorem measurable_momentumFlip : Measurable (momentumFlip : PhaseSpace ι → PhaseSpace ι) := by
  unfold momentumFlip
  fun_prop

theorem measurable_kineticEnergy : Measurable (kineticEnergy : Momentum ι → ℝ) := by
  unfold kineticEnergy
  fun_prop

theorem measurable_energy {potential : Position ι → ℝ}
    (hpotential : Measurable potential) :
    Measurable (energy potential : PhaseSpace ι → ℝ) := by
  exact (hpotential.comp measurable_fst).add
    (measurable_kineticEnergy.comp measurable_snd)

omit [Fintype ι] in
theorem continuous_halfKick
    {gradient : Position ι → Position ι} (hgradient : Continuous gradient)
    (ε : ℝ) :
    Continuous (Function.uncurry (halfKick gradient ε)) := by
  unfold halfKick
  fun_prop

omit [Fintype ι] in
theorem continuous_drift (ε : ℝ) :
    Continuous (Function.uncurry (drift (ι := ι) ε)) := by
  unfold drift
  fun_prop

omit [Fintype ι] in
theorem continuous_leapfrog
    {gradient : Position ι → Position ι} (hgradient : Continuous gradient)
    (ε : ℝ) : Continuous (leapfrog gradient ε) := by
  unfold leapfrog halfKick drift
  fun_prop

omit [Fintype ι] in
theorem continuous_leapfrogN
    {gradient : Position ι → Position ι} (hgradient : Continuous gradient)
    (ε : ℝ) (n : ℕ) : Continuous (leapfrogN gradient ε n) := by
  change Continuous ((leapfrog gradient ε)^[n])
  exact (continuous_leapfrog hgradient ε).iterate n

omit [Fintype ι] in
theorem measurable_halfKick
    {gradient : Position ι → Position ι} (hgradient : Measurable gradient)
    (ε : ℝ) :
    Measurable (Function.uncurry (halfKick gradient ε)) := by
  unfold halfKick
  fun_prop

omit [Fintype ι] in
theorem measurable_drift (ε : ℝ) :
    Measurable (Function.uncurry (drift (ι := ι) ε)) := by
  unfold drift
  fun_prop

omit [Fintype ι] in
theorem measurable_leapfrog
    {gradient : Position ι → Position ι} (hgradient : Measurable gradient)
    (ε : ℝ) : Measurable (leapfrog gradient ε) := by
  unfold leapfrog halfKick drift
  fun_prop

omit [Fintype ι] in
theorem measurable_leapfrogN
    {gradient : Position ι → Position ι} (hgradient : Measurable gradient)
    (ε : ℝ) (n : ℕ) : Measurable (leapfrogN gradient ε n) := by
  change Measurable ((leapfrog gradient ε)^[n])
  exact (measurable_leapfrog hgradient ε).iterate n

omit [Fintype ι] in
@[simp]
theorem momentumFlip_involutive (z : PhaseSpace ι) :
    momentumFlip (momentumFlip z) = z := by
  ext i <;> simp [momentumFlip]

omit [Fintype ι] in
@[simp]
theorem leapfrogN_zero (gradient : Position ι → Position ι) (ε : ℝ)
    (z : PhaseSpace ι) :
    leapfrogN gradient ε 0 z = z := by
  simp [leapfrogN]

omit [Fintype ι] in
theorem leapfrogN_succ (gradient : Position ι → Position ι) (ε : ℝ)
    (n : ℕ) (z : PhaseSpace ι) :
    leapfrogN gradient ε (n + 1) z =
      leapfrog gradient ε (leapfrogN gradient ε n z) := by
  simp [leapfrogN, Function.iterate_succ_apply']

/-- The energy error of an iterated leapfrog trajectory is the telescoping
sum of its one-step energy errors. -/
theorem energy_leapfrogN_sub_eq_sum_step_errors
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (n : ℕ) (z : PhaseSpace ι) :
    energy potential (leapfrogN gradient ε n z) - energy potential z =
      ∑ k ∈ Finset.range n,
        (energy potential
            (leapfrog gradient ε (leapfrogN gradient ε k z)) -
          energy potential (leapfrogN gradient ε k z)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [leapfrogN_succ, Finset.sum_range_succ, ← ih]
      ring

omit [Fintype ι] in
/-- Momentum flip conjugates a forward leapfrog step to a step of the
opposite size. -/
theorem momentumFlip_leapfrog_momentumFlip
    (gradient : Position ι → Position ι) (ε : ℝ) (z : PhaseSpace ι) :
    momentumFlip (leapfrog gradient ε (momentumFlip z)) =
      leapfrog gradient (-ε) z := by
  let pForward : Momentum ι := halfKick gradient (-ε) z.1 z.2
  have hp : halfKick gradient ε z.1 (-z.2) = -pForward := by
    ext i
    simp only [halfKick, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply]
    dsimp [pForward, halfKick]
    ring
  have hq : drift ε z.1 (-pForward) = drift (-ε) z.1 pForward := by
    ext i
    simp only [drift, Pi.add_apply, Pi.smul_apply, Pi.neg_apply]
    ring
  rw [leapfrog, leapfrog, momentumFlip, momentumFlip]
  dsimp only
  rw [hp, hq]
  apply Prod.ext
  · rfl
  · change -(halfKick gradient ε (drift (-ε) z.1 pForward) (-pForward)) =
      halfKick gradient (-ε) (drift (-ε) z.1 pForward) pForward
    ext i
    simp only [halfKick, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply]
    ring

omit [Fintype ι] in
/-- A leapfrog step is inverted by a negative-size step. -/
theorem leapfrog_neg_comp_leapfrog
    (gradient : Position ι → Position ι) (ε : ℝ) (z : PhaseSpace ι) :
    leapfrog gradient (-ε) (leapfrog gradient ε z) = z := by
  let pHalf := halfKick gradient ε z.1 z.2
  let qNext := drift ε z.1 pHalf
  have hfirst : halfKick gradient (-ε) qNext
      (halfKick gradient ε qNext pHalf) = pHalf := by
    ext i
    simp only [halfKick, Pi.sub_apply, Pi.smul_apply]
    ring
  have hposition : drift (-ε) qNext pHalf = z.1 := by
    ext i
    simp only [drift, Pi.add_apply, Pi.smul_apply]
    dsimp [qNext, drift]
    ring
  rw [leapfrog, leapfrog]
  dsimp only
  change (drift (-ε) qNext
      (halfKick gradient (-ε) qNext (halfKick gradient ε qNext pHalf)),
    halfKick gradient (-ε)
      (drift (-ε) qNext
        (halfKick gradient (-ε) qNext (halfKick gradient ε qNext pHalf)))
      (halfKick gradient (-ε) qNext (halfKick gradient ε qNext pHalf))) = z
  rw [hfirst, hposition]
  apply Prod.ext
  · rfl
  · ext i
    simp only [halfKick, Pi.sub_apply, Pi.smul_apply]
    dsimp [pHalf, halfKick]
    ring

omit [Fintype ι] in
/-- Iterating the negative-size map inverts the same number of positive-size
leapfrog steps. -/
theorem leapfrogN_neg_comp_leapfrogN
    (gradient : Position ι → Position ι) (ε : ℝ) (n : ℕ)
    (z : PhaseSpace ι) :
    leapfrogN gradient (-ε) n (leapfrogN gradient ε n z) = z := by
  exact (Function.LeftInverse.iterate
    (fun z => leapfrog_neg_comp_leapfrog gradient ε z) n) z

omit [Fintype ι] in
@[simp]
theorem leapfrogTrajectory_zero
    (gradient : Position ι → Position ι) (ε : ℝ) (z : PhaseSpace ι) :
    leapfrogTrajectory gradient ε z 0 = z := by
  simp [leapfrogTrajectory]

omit [Fintype ι] in
theorem leapfrogTrajectory_succ
    (gradient : Position ι → Position ι) (ε : ℝ) (z : PhaseSpace ι) (n : ℕ) :
    leapfrogTrajectory gradient ε z (n + 1) =
      leapfrog gradient ε (leapfrogTrajectory gradient ε z n) := by
  exact leapfrogN_succ gradient ε n z

end Mcmc.Hamiltonian
