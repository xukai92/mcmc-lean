import Mcmc.Relativistic.Hamiltonian
import Mcmc.Hamiltonian.ExactFlow

/-!
# Derivatives of relativistic Hamiltonians

This module formalizes the momentum derivative in Xu and Ge's Equation (13).
The metric compatibility assumption is stated as the bilinear identity
`⟪A x, A y⟫ = ⟪G⁻¹ x, y⟫`, which is the coordinate-free content of
`Aᵀ A = G⁻¹` needed by the calculation.
-/

namespace Mcmc.Relativistic

open Mcmc.Hamiltonian

variable {ι : Type*} [Fintype ι]

/-- Directional derivative of the special-relativistic kinetic energy. -/
theorem hasDerivAt_relativisticKineticEnergy_line
    (m c : ℝ) (p h : Momentum ι) (hm : 0 < m) (hc : 0 < c) :
    HasDerivAt (fun t : ℝ => relativisticKineticEnergy m c (p + t • h))
      (euclideanInner (relativisticVelocity m c p) h) 0 := by
  have hm0 : m ≠ 0 := hm.ne'
  have hc0 : c ≠ 0 := hc.ne'
  have hrad := relativistic_radicand_pos m c p hm hc
  unfold relativisticKineticEnergy
  have hinner : HasDerivAt
      (fun t : ℝ => squaredEuclideanNorm (p + t • h))
      (2 * euclideanInner p h) 0 := by
    have hline : ∀ i, HasDerivAt (fun t : ℝ => (p + t • h) i) (h i) 0 := by
      intro i
      change HasDerivAt (fun t : ℝ => p i + t * h i) (h i) 0
      simpa only [id_eq, one_mul] using
        ((hasDerivAt_id (0 : ℝ)).mul_const (h i)).const_add (p i)
    have hbase := hasDerivAt_euclideanInner hline hline
    convert hbase using 1
    · rfl
    · simp [euclideanInner_comm, two_mul]
  have hsqrt := ((hinner.div_const (m ^ 2 * c ^ 2)).const_add 1).sqrt
    (by simpa [add_comm] using ne_of_gt hrad)
  have hout := hsqrt.const_mul (m * c ^ 2)
  have hfun : (fun t : ℝ => m * c ^ 2 *
      Real.sqrt (1 + squaredEuclideanNorm (p + t • h) / (m ^ 2 * c ^ 2))) =
      (fun t : ℝ => m * c ^ 2 *
      Real.sqrt (squaredEuclideanNorm (p + t • h) / (m ^ 2 * c ^ 2) + 1)) := by
    funext t
    rw [add_comm]
  rw [hfun] at hout
  apply hout.congr_deriv
  simp only [zero_smul, add_zero]
  have hsqrt0 : Real.sqrt
      (squaredEuclideanNorm p / (m ^ 2 * c ^ 2) + 1) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hrad)
  rw [add_comm 1 (squaredEuclideanNorm p / (m ^ 2 * c ^ 2))]
  unfold relativisticVelocity relativisticMass
  change
    m * c ^ 2 *
        ((2 * euclideanInner p h / (m ^ 2 * c ^ 2)) /
          (2 * Real.sqrt
            (squaredEuclideanNorm p / (m ^ 2 * c ^ 2) + 1))) =
      euclideanInner
        ((m * Real.sqrt
          (squaredEuclideanNorm p / (m ^ 2 * c ^ 2) + 1))⁻¹ • p) h
  rw [euclideanInner_smul_left]
  field_simp [hm0, hc0, hsqrt0]

/-- The Fréchet momentum derivative of special-relativistic kinetic energy. -/
theorem fderiv_relativisticKineticEnergy_apply
    (m c : ℝ) (p h : Momentum ι) (hm : 0 < m) (hc : 0 < c) :
    fderiv ℝ (relativisticKineticEnergy m c) p h =
      euclideanInner (relativisticVelocity m c p) h := by
  let line : ℝ → Momentum ι := fun t => p + t • h
  have hline : HasDerivAt line h 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    change HasDerivAt (fun t : ℝ => p i + t * h i) (h i) 0
    simpa only [id_eq, one_mul] using
      ((hasDerivAt_id (0 : ℝ)).mul_const (h i)).const_add (p i)
  have hdiff : DifferentiableAt ℝ (relativisticKineticEnergy m c) p := by
    unfold relativisticKineticEnergy
    apply DifferentiableAt.const_mul
    apply DifferentiableAt.sqrt
    · unfold squaredEuclideanNorm euclideanInner
      fun_prop
    · exact ne_of_gt (relativistic_radicand_pos m c p hm hc)
  dsimp [line] at hline
  have hdiff0 : DifferentiableAt ℝ (relativisticKineticEnergy m c)
      (p + (0 : ℝ) • h) := by simpa using hdiff
  have hfrom := hdiff0.hasFDerivAt.comp_hasDerivAt 0 hline
  have hfrom' : HasDerivAt
      (fun t : ℝ => relativisticKineticEnergy m c (p + t • h))
      (fderiv ℝ (relativisticKineticEnergy m c) p h) 0 := by
    have hfrom0 : HasDerivAt
        (relativisticKineticEnergy m c ∘ fun t : ℝ => p + t • h)
        (fderiv ℝ (relativisticKineticEnergy m c) p h) (0 : ℝ) :=
      hfrom.congr_deriv (by simp)
    apply hfrom0.congr_of_eventuallyEq
    filter_upwards [] with t
    rfl
  exact HasDerivAt.unique hfrom'
    (hasDerivAt_relativisticKineticEnergy_line m c p h hm hc)

/-- Derivative of relativistic energy viewed as a scalar function of its
nonnegative quadratic argument.  Its coefficient is `1 / (2M)`. -/
theorem fderiv_relativisticEnergyOfQuadratic_apply
    (m c s ds : ℝ) (hm : 0 < m) (hc : 0 < c) (hs : 0 ≤ s) :
    fderiv ℝ (fun x : ℝ => m * c ^ 2 *
      Real.sqrt (x / (m ^ 2 * c ^ 2) + 1)) s ds =
      (m * Real.sqrt (s / (m ^ 2 * c ^ 2) + 1))⁻¹ / 2 * ds := by
  have hden : 0 < m ^ 2 * c ^ 2 :=
    mul_pos (sq_pos_of_pos hm) (sq_pos_of_pos hc)
  have hrad : 0 < s / (m ^ 2 * c ^ 2) + 1 := by
    have : 0 ≤ s / (m ^ 2 * c ^ 2) := div_nonneg hs hden.le
    linarith
  have hd := (((hasDerivAt_id s).div_const (m ^ 2 * c ^ 2)).const_add 1).sqrt
    (by simpa [add_comm] using ne_of_gt hrad)
  have hout := hd.const_mul (m * c ^ 2)
  have hfun : (fun y : ℝ => m * c ^ 2 *
      Real.sqrt (1 + id y / (m ^ 2 * c ^ 2))) =
      (fun x : ℝ => m * c ^ 2 *
      Real.sqrt (x / (m ^ 2 * c ^ 2) + 1)) := by
    funext x
    simp [add_comm]
  rw [hfun] at hout
  rw [hout.hasFDerivAt.fderiv]
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, id_eq]
  have hm0 := hm.ne'
  have hc0 := hc.ne'
  have hsqrt0 := ne_of_gt (Real.sqrt_pos.2 hrad)
  field_simp [hm0, hc0, hsqrt0]
  ring_nf

/-- Coordinate trace of an endomorphism of the project's finite function
space.  This is the matrix trace in the standard coordinate basis. -/
noncomputable def coordinateTrace [DecidableEq ι]
    (L : Momentum ι →ₗ[ℝ] Momentum ι) : ℝ :=
  ∑ i, L (Pi.single i 1) i

/-- Pointwise differentiability certificate needed for Xu and Ge's Equation
(12). `metricVariation u` represents the directional metric derivative
`dG(q)[u]`.  The two identities are, in matrix notation,

* `d(pᵀG⁻¹p)[u] = -pᵀG⁻¹ dG[u] G⁻¹p`; and
* `d(log det G)[u] = tr(G⁻¹ dG[u])`.

Keeping these obligations explicit prevents a raw factor, inverse action, and
log determinant that are unrelated to one another from satisfying Equation
(12) accidentally. -/
structure FactoredRiemannianMetric.Equation12Certificate
    [DecidableEq ι] (metric : FactoredRiemannianMetric ι)
    (q : Position ι) where
  metricVariation : Position ι → Momentum ι →ₗ[ℝ] Momentum ι
  differentiableAt_quadratic : ∀ p, DifferentiableAt ℝ
    (fun r => squaredEuclideanNorm (metric.factor r p)) q
  fderiv_quadratic : ∀ p u,
    fderiv ℝ (fun r => squaredEuclideanNorm (metric.factor r p)) q u =
      -euclideanInner (metric.inverseMetric q p)
        (metricVariation u (metric.inverseMetric q p))
  differentiableAt_logDet : DifferentiableAt ℝ metric.logDet q
  fderiv_logDet : ∀ u, fderiv ℝ metric.logDet q u =
    coordinateTrace ((metric.inverseMetric q).comp (metricVariation u))

/-- Equation (12), in directional Fréchet-derivative form.  The first term is
the inverse-mass-scaled metric variation and the second is the log-determinant
trace correction. -/
theorem fderiv_riemannianRelativisticKineticEnergy_position_apply
    [DecidableEq ι] (metric : FactoredRiemannianMetric ι)
    (cert : metric.Equation12Certificate q) (m c : ℝ) (p : Momentum ι)
    (u : Position ι) (hm : 0 < m) (hc : 0 < c) :
    fderiv ℝ (fun r =>
      riemannianRelativisticKineticEnergy metric m c r p) q u =
      (riemannianRelativisticMass metric m c q p)⁻¹ *
          (-1 / 2 * euclideanInner (metric.inverseMetric q p)
            (cert.metricVariation u (metric.inverseMetric q p))) +
        1 / 2 * coordinateTrace
          ((metric.inverseMetric q).comp (cert.metricVariation u)) := by
  let Q : Position ι → ℝ := fun r =>
    squaredEuclideanNorm (metric.factor r p)
  let E : ℝ → ℝ := fun s =>
    m * c ^ 2 * Real.sqrt (s / (m ^ 2 * c ^ 2) + 1)
  have hQnonneg : 0 ≤ Q q := squaredEuclideanNorm_nonneg _
  have hEdiff : DifferentiableAt ℝ E (Q q) := by
    unfold E
    apply DifferentiableAt.const_mul
    apply DifferentiableAt.sqrt
    · fun_prop
    · have hden : 0 < m ^ 2 * c ^ 2 :=
        mul_pos (sq_pos_of_pos hm) (sq_pos_of_pos hc)
      exact ne_of_gt (by positivity)
  unfold riemannianRelativisticKineticEnergy
  change fderiv ℝ ((E ∘ Q) + fun r =>
    1 / 2 * metric.logDet r) q u = _
  rw [fderiv_add (hEdiff.comp q (cert.differentiableAt_quadratic p))
    (cert.differentiableAt_logDet.const_mul (1 / 2))]
  simp only [add_apply]
  change fderiv ℝ (E ∘ Q) q u + _ = _
  rw [fderiv_comp (f := Q) (g := E) (x := q) hEdiff
    (cert.differentiableAt_quadratic p), ContinuousLinearMap.comp_apply]
  rw [fderiv_relativisticEnergyOfQuadratic_apply m c (Q q)
    (fderiv ℝ Q q u) hm hc hQnonneg]
  rw [cert.fderiv_quadratic,
    fderiv_const_mul cert.differentiableAt_logDet (1 / 2 : ℝ)]
  simp only [smul_apply, smul_eq_mul]
  rw [cert.fderiv_logDet]
  unfold riemannianRelativisticMass generalRelativisticMass relativisticMass Q
  let a := (m * Real.sqrt
    (squaredEuclideanNorm (metric.factor q p) / (m ^ 2 * c ^ 2) + 1))⁻¹
  let b := euclideanInner (metric.inverseMetric q p)
    (cert.metricVariation u (metric.inverseMetric q p))
  let t := coordinateTrace
    ((metric.inverseMetric q).comp (cert.metricVariation u))
  change a / 2 * -b + 1 / 2 * t = a * (-1 / 2 * b) + 1 / 2 * t
  ring

/-- Position derivative of the complete GR Hamiltonian: the potential force
plus the two terms from Equation (12). -/
theorem fderiv_generalRelativisticHamiltonian_position_apply
    [DecidableEq ι] (potential : Position ι → ℝ)
    (metric : FactoredRiemannianMetric ι)
    (cert : metric.Equation12Certificate q) (m c : ℝ)
    (p : Momentum ι) (u : Position ι) (hm : 0 < m) (hc : 0 < c)
    (hpotential : DifferentiableAt ℝ potential q) :
    fderiv ℝ (fun r =>
      generalRelativisticHamiltonian potential metric m c (r, p)) q u =
      fderiv ℝ potential q u +
        (riemannianRelativisticMass metric m c q p)⁻¹ *
            (-1 / 2 * euclideanInner (metric.inverseMetric q p)
              (cert.metricVariation u (metric.inverseMetric q p))) +
          1 / 2 * coordinateTrace
            ((metric.inverseMetric q).comp (cert.metricVariation u)) := by
  unfold generalRelativisticHamiltonian
  change fderiv ℝ (potential + fun r =>
    riemannianRelativisticKineticEnergy metric m c r p) q u = _
  have hkinetic : DifferentiableAt ℝ (fun r =>
      riemannianRelativisticKineticEnergy metric m c r p) q := by
    unfold riemannianRelativisticKineticEnergy
    let Q : Position ι → ℝ := fun r =>
      squaredEuclideanNorm (metric.factor r p)
    let E : ℝ → ℝ := fun s =>
      m * c ^ 2 * Real.sqrt (s / (m ^ 2 * c ^ 2) + 1)
    have hEdiff : DifferentiableAt ℝ E (Q q) := by
      unfold E
      apply DifferentiableAt.const_mul
      apply DifferentiableAt.sqrt
      · fun_prop
      · have hden : 0 < m ^ 2 * c ^ 2 :=
          mul_pos (sq_pos_of_pos hm) (sq_pos_of_pos hc)
        have hnonneg : 0 ≤ Q q := squaredEuclideanNorm_nonneg _
        exact ne_of_gt (by positivity)
    exact (hEdiff.comp q (cert.differentiableAt_quadratic p)).add
      (cert.differentiableAt_logDet.const_mul (1 / 2))
  rw [fderiv_add hpotential hkinetic]
  simp only [add_apply]
  rw [fderiv_riemannianRelativisticKineticEnergy_position_apply
    metric cert m c p u hm hc]
  ring

/-- Equation (13): differentiating the factored relativistic kinetic term in
momentum gives the inverse-metric velocity, provided `AᵀA = G⁻¹` in bilinear
form. -/
theorem fderiv_factoredRelativisticKineticEnergy_apply
    (m c : ℝ) (A : Momentum ι ≃L[ℝ] Momentum ι)
    (B : Momentum ι →ₗ[ℝ] Momentum ι) (p h : Momentum ι)
    (hm : 0 < m) (hc : 0 < c)
    (hcompat : ∀ x y, euclideanInner (A x) (A y) =
      euclideanInner (B x) y) :
    fderiv ℝ (fun x => relativisticKineticEnergy m c (A x)) p h =
      euclideanInner (generalRelativisticVelocity m c A.toLinearMap B p) h := by
  change fderiv ℝ (relativisticKineticEnergy m c ∘ A) p h = _
  rw [fderiv_comp (f := A) (g := relativisticKineticEnergy m c) (x := p) ((by
      unfold relativisticKineticEnergy
      apply DifferentiableAt.const_mul
      apply DifferentiableAt.sqrt
      · unfold squaredEuclideanNorm euclideanInner
        fun_prop
      · exact ne_of_gt (relativistic_radicand_pos m c (A p) hm hc)))
    A.differentiableAt]
  simp only [ContinuousLinearEquiv.fderiv, ContinuousLinearMap.comp_apply]
  have hbase := fderiv_relativisticKineticEnergy_apply m c (A p) (A h) hm hc
  change fderiv ℝ (relativisticKineticEnergy m c) (A p) (A h) = _
  rw [hbase]
  unfold relativisticVelocity generalRelativisticVelocity generalRelativisticMass
  rw [euclideanInner_smul_left, euclideanInner_smul_left, hcompat]
  rfl

/-- Equation (13) specialized to the momentum derivative of the complete GR
Hamiltonian at a fixed position. -/
theorem fderiv_generalRelativisticHamiltonian_momentum_apply
    (potential : Position ι → ℝ) (metric : FactoredRiemannianMetric ι)
    (m c : ℝ) (q : Position ι) (p h : Momentum ι)
    (hm : 0 < m) (hc : 0 < c)
    (hcompat : ∀ x y,
      euclideanInner (metric.factor q x) (metric.factor q y) =
        euclideanInner (metric.inverseMetric q x) y) :
    fderiv ℝ
        (fun r => generalRelativisticHamiltonian potential metric m c (q, r))
        p h =
      euclideanInner (riemannianRelativisticVelocity metric m c q p) h := by
  unfold generalRelativisticHamiltonian riemannianRelativisticKineticEnergy
  change fderiv ℝ (fun r => potential q +
      (relativisticKineticEnergy m c (metric.factor q r) +
        (1 / 2 : ℝ) * metric.logDet q)) p h = _
  rw [fderiv_const_add, fderiv_add_const]
  exact fderiv_factoredRelativisticKineticEnergy_apply m c
    (metric.factor q) (metric.inverseMetric q) p h hm hc hcompat

end Mcmc.Relativistic
