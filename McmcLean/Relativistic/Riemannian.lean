import McmcLean.Relativistic.Momentum

/-!
# Riemannian relativistic mass and velocity

This module separates two linear maps that coincide only in special cases:

* a factor `A` used by the quadratic form in the relativistic mass, so the
  kinetic term depends on `‖A p‖²`; and
* the inverse metric `B`, which sends momentum to the numerator `B p` of the
  Hamiltonian velocity.

For the paper's matrix notation, `B = G⁻¹` and `Aᵀ A = B`.  Differentiating
the kinetic energy gives velocity `B p / M(A p)`.  Its generally valid bound
is therefore `‖B p‖ / (‖A p‖ / c)`, not the ratio printed after Equation (9)
without further assumptions on the metric and momentum direction.
-/

namespace McmcLean.Relativistic

open McmcLean.Hamiltonian

variable {ι : Type*} [Fintype ι]

/-- General-relativistic mass expressed through a factor of the inverse
metric's quadratic form. -/
noncomputable def generalRelativisticMass
    (m c : ℝ) (factor : Momentum ι →ₗ[ℝ] Momentum ι)
    (p : Momentum ι) : ℝ :=
  relativisticMass m c (factor p)

/-- Correct velocity associated with a factored quadratic kinetic energy:
the inverse metric acts in the numerator, while mass is computed from the
factor-transformed momentum. -/
noncomputable def generalRelativisticVelocity
    (m c : ℝ) (factor inverseMetric : Momentum ι →ₗ[ℝ] Momentum ι)
    (p : Momentum ι) : Momentum ι :=
  (generalRelativisticMass m c factor p)⁻¹ • inverseMetric p

theorem generalRelativisticMass_pos
    (m c : ℝ) (factor : Momentum ι →ₗ[ℝ] Momentum ι)
    (p : Momentum ι) (hm : 0 < m) (hc : 0 < c) :
    0 < generalRelativisticMass m c factor p := by
  exact relativisticMass_pos m c (factor p) hm hc

/-- The factor norm divided by `c` is strictly smaller than the relativistic
mass. -/
theorem factorNorm_div_lt_generalRelativisticMass
    (m c : ℝ) (factor : Momentum ι →ₗ[ℝ] Momentum ι)
    (p : Momentum ι) (hm : 0 < m) (hc : 0 < c) :
    euclideanNorm (factor p) / c <
      generalRelativisticMass m c factor p := by
  exact euclideanNorm_div_lt_relativisticMass m c (factor p) hm hc

/-- Correct anisotropic velocity bound.  It exposes both the inverse-metric
numerator and the factor norm controlling relativistic mass. -/
theorem euclideanNorm_generalRelativisticVelocity_lt
    (m c : ℝ) (factor inverseMetric : Momentum ι →ₗ[ℝ] Momentum ι)
    (p : Momentum ι) (hm : 0 < m) (hc : 0 < c)
    (hfactor : factor p ≠ 0) (hinverse : inverseMetric p ≠ 0) :
    euclideanNorm
        (generalRelativisticVelocity m c factor inverseMetric p) <
      euclideanNorm (inverseMetric p) /
        (euclideanNorm (factor p) / c) := by
  have hmass := generalRelativisticMass_pos m c factor p hm hc
  have hfactorNorm : 0 < euclideanNorm (factor p) := by
    exact Real.sqrt_pos.2 (squaredEuclideanNorm_pos hfactor)
  have hden : 0 < euclideanNorm (factor p) / c :=
    div_pos hfactorNorm hc
  have hinverseNorm : 0 < euclideanNorm (inverseMetric p) := by
    exact Real.sqrt_pos.2 (squaredEuclideanNorm_pos hinverse)
  have hdom := factorNorm_div_lt_generalRelativisticMass
    m c factor p hm hc
  rw [generalRelativisticVelocity, euclideanNorm_smul,
    abs_of_pos (inv_pos.mpr hmass), inv_mul_eq_div]
  exact div_lt_div_of_pos_left hinverseNorm hden hdom

/-- Coordinatewise diagonal linear map, used for explicit metric examples. -/
def diagonalMomentumMap (d : ι → ℝ) :
    Momentum ι →ₗ[ℝ] Momentum ι where
  toFun p i := d i * p i
  map_add' p r := by
    funext i
    simp only [Pi.add_apply]
    ring
  map_smul' a p := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- Test momentum used by the anisotropic Equation (9) audit. -/
def anisotropicTestMomentum : Momentum (Fin 2) := fun _ => 1

/-- A factor `A = diag(2,1)`. -/
def anisotropicTestFactor :
    Momentum (Fin 2) →ₗ[ℝ] Momentum (Fin 2) :=
  diagonalMomentumMap (fun i => if i = 0 then 2 else 1)

/-- The corresponding inverse metric `AᵀA = diag(4,1)`. -/
def anisotropicTestInverseMetric :
    Momentum (Fin 2) →ₗ[ℝ] Momentum (Fin 2) :=
  diagonalMomentumMap (fun i => if i = 0 then 4 else 1)

@[simp]
theorem squaredEuclideanNorm_anisotropicTestMomentum :
    squaredEuclideanNorm anisotropicTestMomentum = 2 := by
  simp [squaredEuclideanNorm, euclideanInner, anisotropicTestMomentum]

@[simp]
theorem squaredEuclideanNorm_anisotropicTestFactor :
    squaredEuclideanNorm
      (anisotropicTestFactor anisotropicTestMomentum) = 5 := by
  norm_num [squaredEuclideanNorm, euclideanInner, anisotropicTestFactor,
    anisotropicTestMomentum, diagonalMomentumMap, Fin.sum_univ_two]

@[simp]
theorem squaredEuclideanNorm_anisotropicTestInverseMetric :
    squaredEuclideanNorm
      (anisotropicTestInverseMetric anisotropicTestMomentum) = 17 := by
  norm_num [squaredEuclideanNorm, euclideanInner, anisotropicTestInverseMetric,
    anisotropicTestMomentum, diagonalMomentumMap, Fin.sum_univ_two]

/-- Concrete obstruction to the norm-ratio simplification printed after
Equation (9).  For `A = diag(2,1)`, `G⁻¹ = AᵀA = diag(4,1)`, and `p=(1,1)`,
the corrected anisotropic ratio is strictly larger than the printed ratio. -/
theorem printedEquation9_ratio_lt_correctedRatio :
    euclideanNorm
          (anisotropicTestFactor anisotropicTestMomentum) /
        euclideanNorm anisotropicTestMomentum <
      euclideanNorm
          (anisotropicTestInverseMetric anisotropicTestMomentum) /
        euclideanNorm
          (anisotropicTestFactor anisotropicTestMomentum) := by
  have hpSq : euclideanNorm anisotropicTestMomentum ^ 2 = 2 := by
    rw [euclideanNorm_sq, squaredEuclideanNorm_anisotropicTestMomentum]
  have hASq :
      euclideanNorm (anisotropicTestFactor anisotropicTestMomentum) ^ 2 = 5 := by
    rw [euclideanNorm_sq, squaredEuclideanNorm_anisotropicTestFactor]
  have hBSq :
      euclideanNorm
          (anisotropicTestInverseMetric anisotropicTestMomentum) ^ 2 = 17 := by
    rw [euclideanNorm_sq, squaredEuclideanNorm_anisotropicTestInverseMetric]
  have hp : 0 < euclideanNorm anisotropicTestMomentum := by
    nlinarith [euclideanNorm_nonneg anisotropicTestMomentum]
  have hA :
      0 < euclideanNorm (anisotropicTestFactor anisotropicTestMomentum) := by
    nlinarith [euclideanNorm_nonneg
      (anisotropicTestFactor anisotropicTestMomentum)]
  rw [div_lt_div_iff₀ hp hA]
  have hleft :
      0 ≤ euclideanNorm (anisotropicTestFactor anisotropicTestMomentum) *
        euclideanNorm (anisotropicTestFactor anisotropicTestMomentum) :=
    mul_self_nonneg _
  have hright :
      0 ≤ euclideanNorm
          (anisotropicTestInverseMetric anisotropicTestMomentum) *
        euclideanNorm anisotropicTestMomentum :=
    mul_nonneg (euclideanNorm_nonneg _) hp.le
  apply (sq_lt_sq₀ hleft hright).mp
  nlinarith

end McmcLean.Relativistic
