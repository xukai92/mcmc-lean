import Mcmc.Hamiltonian.Leapfrog
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Analytic assumptions for coupled Hamiltonian Monte Carlo

This module records Assumptions 1 and 2 of Xu, Fjelde, Sutton, and Ge (2021)
in the finite-dimensional Euclidean state space used by the Hamiltonian
development.  The gradient is kept as an explicit function because it is an
input to the executable leapfrog map, but `RegularPotential.fderiv_apply`
certifies that it represents the derivative of the potential in Euclidean
coordinates.

The paper states local strong convexity through strong monotonicity of the
gradient.  `LocalStrongConvexity` uses that statement verbatim, avoiding any
normalization ambiguity in alternative definitions of strong convexity.
-/

open MeasureTheory
open scoped ENNReal

namespace Mcmc.Hamiltonian

variable {ι : Type*} [Fintype ι]

/-- Every compact position region is contained in an explicit Euclidean ball. -/
theorem IsCompact.exists_euclideanNorm_bound
    {S : Set (Position ι)} (hS : IsCompact S) :
    ∃ R > 0, ∀ q ∈ S, euclideanNorm q ≤ R := by
  have hbdd : BddAbove (euclideanNorm '' S) :=
    hS.bddAbove_image continuous_euclideanNorm.continuousOn
  rcases bddAbove_def.mp hbdd with ⟨a, ha⟩
  refine ⟨max a 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro q hq
  exact (ha _ (Set.mem_image_of_mem euclideanNorm hq)).trans (le_max_left _ _)

/-- Every compact phase region has a uniform explicit Euclidean phase-size
bound. -/
theorem IsCompact.exists_euclideanPhaseSize_bound
    {K : Set (PhaseSpace ι)} (hK : IsCompact K) :
    ∃ M > 0, ∀ z ∈ K, euclideanPhaseSize z ≤ M := by
  have hbdd : BddAbove (euclideanPhaseSize '' K) :=
    hK.bddAbove_image continuous_euclideanPhaseSize.continuousOn
  rcases bddAbove_def.mp hbdd with ⟨a, ha⟩
  refine ⟨max a 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro z hz
  exact (ha _ (Set.mem_image_of_mem euclideanPhaseSize hz)).trans
    (le_max_left _ _)

/-- Compact positions and a finite kinetic-energy cutoff give one uniform
bound on the full position-momentum phase size. -/
theorem IsCompact.exists_euclideanPhaseSize_bound_of_kineticEnergy_le
    {K : Set (Position ι)} (hK : IsCompact K)
    {k0 : ℝ} (hk0 : 0 ≤ k0) :
    ∃ M > 0, ∀ q ∈ K, ∀ p : Momentum ι,
      kineticEnergy p ≤ k0 → euclideanPhaseSize (q, p) ≤ M := by
  obtain ⟨R, hR, hbound⟩ :=
    Mcmc.Hamiltonian.IsCompact.exists_euclideanNorm_bound hK
  let M := R + Real.sqrt (2 * k0)
  have hM : 0 < M := lt_of_lt_of_le hR (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  refine ⟨M, hM, ?_⟩
  intro q hq p hp
  unfold euclideanPhaseSize
  exact add_le_add (hbound q hq)
    (euclideanNorm_le_sqrt_two_mul_of_kineticEnergy_le hk0 hp)

/-- A compact core contained in the interior of a region has one positive
closed-ball buffer radius that works around every point of the core. -/
theorem IsCompact.exists_pos_forall_closedBall_subset
    {K S : Set (Position ι)} (hK : IsCompact K)
    (hKS : K ⊆ interior S) :
    ∃ r > 0, ∀ q ∈ K, Metric.closedBall q r ⊆ S := by
  rcases hK.exists_cthickening_subset_open isOpen_interior hKS with
    ⟨r, hr, hthick⟩
  refine ⟨r, hr, ?_⟩
  intro q hq
  exact (Metric.closedBall_subset_cthickening hq r).trans
    (hthick.trans interior_subset)

/-- Assumption 1: a twice continuously differentiable potential whose actual
gradient is globally Lipschitz with a positive constant. -/
structure RegularPotential
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (β : NNReal) : Prop where
  beta_pos : 0 < β
  contDiff_two : ContDiff ℝ 2 potential
  fderiv_apply : ∀ q h,
    fderiv ℝ potential q h = euclideanInner (gradient q) h
  gradient_lipschitz : ∀ q₁ q₂,
    euclideanNorm (gradient q₁ - gradient q₂) ≤
      (β : ℝ) * euclideanNorm (q₁ - q₂)

/-- Assumption 2: on a compact measurable set of positive Lebesgue volume,
the gradient is strongly monotone with positive modulus `α`. -/
structure LocalStrongConvexity
    (gradient : Position ι → Position ι) (S : Set (Position ι))
    (α : ℝ) : Prop where
  alpha_pos : 0 < α
  compact : IsCompact S
  measurableSet : MeasurableSet S
  volume_pos : 0 < volume S
  strongMonotone : ∀ q₁ ∈ S, ∀ q₂ ∈ S,
    α * squaredEuclideanNorm (q₁ - q₂) ≤
      euclideanInner (q₁ - q₂) (gradient q₁ - gradient q₂)

/-- The supplied gradient represents the Fréchet derivative through the
coordinatewise Euclidean inner product. -/
theorem RegularPotential.fderiv_eq_euclideanInner
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (h : RegularPotential potential gradient β) :
    fderiv ℝ potential q v = euclideanInner (gradient q) v :=
  h.fderiv_apply q v

/-- Pointwise form of the paper's global Euclidean gradient-Lipschitz bound. -/
theorem RegularPotential.euclideanNorm_gradient_sub_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (h : RegularPotential potential gradient β)
    (q₁ q₂ : Position ι) :
    euclideanNorm (gradient q₁ - gradient q₂) ≤
      (β : ℝ) * euclideanNorm (q₁ - q₂) :=
  h.gradient_lipschitz q₁ q₂

/-- Global affine growth bound for the gradient, based at the origin. -/
theorem RegularPotential.euclideanNorm_gradient_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (h : RegularPotential potential gradient β)
    (q : Position ι) :
    euclideanNorm (gradient q) ≤
      (β : ℝ) * euclideanNorm q + euclideanNorm (gradient 0) := by
  have htriangle := euclideanNorm_add_le (gradient q - gradient 0) (gradient 0)
  have hsum : gradient q - gradient 0 + gradient 0 = gradient q := by abel
  rw [hsum] at htriangle
  apply le_trans htriangle
  gcongr
  simpa only [sub_zero] using h.euclideanNorm_gradient_sub_le q 0

/-- A globally Euclidean-Lipschitz gradient gives a quadratic first-order
Taylor remainder. The dimension-dependent constant only reconciles the
explicit Euclidean geometry with the ambient finite-product norm used by
mathlib's mean-value theorem. -/
theorem RegularPotential.abs_potential_sub_linearization_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (h : RegularPotential potential gradient β)
    (q₁ q₂ : Position ι) :
    |potential q₂ - potential q₁ -
        euclideanInner (gradient q₁) (q₂ - q₁)| ≤
      (β : ℝ) * ((Fintype.card ι : ℝ) + 1) ^ 2 *
        euclideanNorm (q₂ - q₁) ^ 2 := by
  let D : ℝ := (Fintype.card ι : ℝ) + 1
  let r : ℝ := dist q₁ q₂
  let C : ℝ := (β : ℝ) * D ^ 2 * r
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hC : 0 ≤ C :=
    mul_nonneg (mul_nonneg β.coe_nonneg (sq_nonneg D)) dist_nonneg
  have hdiff : ∀ x ∈ Metric.closedBall q₁ r,
      DifferentiableAt ℝ potential x := by
    intro x hx
    exact h.contDiff_two.differentiable
      (by norm_num : (2 : WithTop ℕ∞) ≠ 0) x
  have hderiv : ∀ x ∈ Metric.closedBall q₁ r,
      ‖fderiv ℝ potential x - fderiv ℝ potential q₁‖ ≤ C := by
    intro x hx
    apply ContinuousLinearMap.opNorm_le_bound _ hC
    intro v
    rw [sub_apply, h.fderiv_apply, h.fderiv_apply, Real.norm_eq_abs]
    have hinner :
        euclideanInner (gradient x) v - euclideanInner (gradient q₁) v =
          euclideanInner (gradient x - gradient q₁) v := by
      unfold euclideanInner
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Pi.sub_apply]
      ring
    rw [hinner]
    apply le_trans
      (abs_euclideanInner_le_norm_mul_norm (gradient x - gradient q₁) v)
    have hgrad : euclideanNorm (gradient x - gradient q₁) ≤
        (β : ℝ) * D * r := by
      apply (h.euclideanNorm_gradient_sub_le x q₁).trans
      have heuc : euclideanNorm (x - q₁) ≤ D * dist x q₁ := by
        simpa only [D] using euclideanNorm_sub_le_card_succ_mul_dist x q₁
      have hxr : dist x q₁ ≤ r := Metric.mem_closedBall.mp hx
      calc
        (β : ℝ) * euclideanNorm (x - q₁) ≤
            (β : ℝ) * (D * dist x q₁) :=
          mul_le_mul_of_nonneg_left heuc β.coe_nonneg
        _ ≤ (β : ℝ) * (D * r) := by gcongr
        _ = (β : ℝ) * D * r := by ring
    have hv : euclideanNorm v ≤ D * ‖v‖ := by
      have hv' := euclideanNorm_sub_le_card_succ_mul_dist v 0
      simpa only [sub_zero, dist_zero_right, D] using hv'
    have hgradNonneg : 0 ≤ (β : ℝ) * D * r :=
      mul_nonneg (mul_nonneg β.coe_nonneg hD) dist_nonneg
    calc
      euclideanNorm (gradient x - gradient q₁) * euclideanNorm v ≤
          ((β : ℝ) * D * r) * (D * ‖v‖) :=
        mul_le_mul hgrad hv (euclideanNorm_nonneg _) hgradNonneg
      _ = C * ‖v‖ := by dsimp [C]; ring
  have hq₁ : q₁ ∈ Metric.closedBall q₁ r :=
    Metric.mem_closedBall_self dist_nonneg
  have hq₂ : q₂ ∈ Metric.closedBall q₁ r := by
    rw [Metric.mem_closedBall, dist_comm]
  have hm := (convex_closedBall q₁ r).norm_image_sub_le_of_norm_fderiv_le'
    hdiff hderiv hq₁ hq₂
  rw [h.fderiv_apply, Real.norm_eq_abs] at hm
  apply hm.trans
  have hdist : dist q₂ q₁ ≤ euclideanNorm (q₂ - q₁) :=
    dist_le_euclideanNorm_sub q₂ q₁
  have hnorm : ‖q₂ - q₁‖ = dist q₂ q₁ := by
    simp only [dist_eq_norm]
  rw [hnorm]
  dsimp [C, r, D]
  rw [dist_comm q₁ q₂]
  have hfactor : 0 ≤ (β : ℝ) * ((Fintype.card ι : ℝ) + 1) ^ 2 :=
    mul_nonneg β.coe_nonneg (sq_nonneg _)
  have hsquare : dist q₂ q₁ ^ 2 ≤ euclideanNorm (q₂ - q₁) ^ 2 :=
    (sq_le_sq₀ dist_nonneg (euclideanNorm_nonneg _)).mpr hdist
  nlinarith

/-- The explicit Euclidean Lipschitz assumption implies ordinary Lipschitz
continuity for mathlib's finite-product metric. -/
theorem RegularPotential.lipschitzWith_gradient
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (h : RegularPotential potential gradient β) :
    LipschitzWith (β * (Fintype.card ι + 1 : NNReal)) gradient := by
  apply LipschitzWith.of_dist_le_mul
  intro q₁ q₂
  calc
    dist (gradient q₁) (gradient q₂) ≤
        euclideanNorm (gradient q₁ - gradient q₂) :=
      dist_le_euclideanNorm_sub _ _
    _ ≤ (β : ℝ) * euclideanNorm (q₁ - q₂) :=
      h.euclideanNorm_gradient_sub_le q₁ q₂
    _ ≤ (β : ℝ) * (((Fintype.card ι : ℝ) + 1) * dist q₁ q₂) :=
      mul_le_mul_of_nonneg_left
        (euclideanNorm_sub_le_card_succ_mul_dist q₁ q₂) β.coe_nonneg
    _ = (↑(β * (Fintype.card ι + 1 : NNReal)) : ℝ) * dist q₁ q₂ := by
      push_cast
      ring

/-- In particular, the gradient supplied to leapfrog is continuous. -/
theorem RegularPotential.continuous_gradient
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (h : RegularPotential potential gradient β) :
    Continuous gradient :=
  h.lipschitzWith_gradient.continuous

/-- The certified gradient inherits one continuous derivative from the
twice-continuously differentiable potential. -/
theorem RegularPotential.contDiff_one_gradient
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (h : RegularPotential potential gradient β) :
    ContDiff ℝ 1 gradient := by
  classical
  rw [contDiff_pi]
  intro i
  let e : Position ι := Pi.single i 1
  have hcoord : (fun q ↦ gradient q i) =
      fun q ↦ fderiv ℝ potential q e := by
    funext q
    rw [h.fderiv_apply]
    unfold euclideanInner e
    simp [Pi.single_apply]
  rw [hcoord]
  have hfderiv : ContDiff ℝ 1 (fderiv ℝ potential) :=
    h.contDiff_two.fderiv_right (by norm_num)
  exact hfderiv.clm_apply contDiff_const

/-- In particular, the derivative of the supplied gradient is continuous. -/
theorem RegularPotential.continuous_fderiv_gradient
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (h : RegularPotential potential gradient β) :
    Continuous (fderiv ℝ gradient) :=
  h.contDiff_one_gradient.continuous_fderiv (by norm_num)

/-- The Hamiltonian is continuously differentiable on phase space. -/
theorem RegularPotential.contDiff_one_energy
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (h : RegularPotential potential gradient β) :
    ContDiff ℝ 1 (energy potential : PhaseSpace ι → ℝ) := by
  have hpotential : ContDiff ℝ 1 potential := h.contDiff_two.of_le (by norm_num)
  unfold energy kineticEnergy
  fun_prop

/-- For every fixed step size, leapfrog is continuously differentiable as a
phase-space map under the paper's `C²` potential assumption. -/
theorem RegularPotential.contDiff_one_leapfrog
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (h : RegularPotential potential gradient β) (ε : ℝ) :
    ContDiff ℝ 1 (leapfrog gradient ε : PhaseSpace ι → PhaseSpace ι) := by
  have hgradient : ContDiff ℝ 1 gradient := h.contDiff_one_gradient
  unfold leapfrog halfKick drift
  fun_prop

/-- On a compact position region, the derivative of the supplied gradient is
uniformly continuous in operator norm. This is the compact-uniform Hessian
continuity needed for the leapfrog consistency argument. -/
theorem RegularPotential.uniformContinuousOn_fderiv_gradient
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (h : RegularPotential potential gradient β)
    {S : Set (Position ι)} (hS : IsCompact S) :
    UniformContinuousOn (fderiv ℝ gradient) S :=
  hS.uniformContinuousOn_of_continuous
    h.continuous_fderiv_gradient.continuousOn

/-- Epsilon--delta form of compact-uniform Hessian continuity, including the
operator application estimate used in first-order gradient remainders. -/
theorem RegularPotential.exists_uniform_fderiv_gradient_apply_error
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (h : RegularPotential potential gradient β)
    {S : Set (Position ι)} (hS : IsCompact S)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ δ →
      ∀ v : Position ι,
        ‖(fderiv ℝ gradient x - fderiv ℝ gradient y) v‖ ≤ η * ‖v‖ := by
  obtain ⟨δ, hδ, hderiv⟩ :=
    Metric.uniformContinuousOn_iff_le.mp
      (h.uniformContinuousOn_fderiv_gradient hS) η hη
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy hxy v
  have hop : ‖fderiv ℝ gradient x - fderiv ℝ gradient y‖ ≤ η := by
    simpa only [dist_eq_norm] using hderiv x hx y hy hxy
  exact ((fderiv ℝ gradient x - fderiv ℝ gradient y).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hop (norm_nonneg v))

/-- Uniform first-order Taylor remainder for the gradient on a compact convex
region. Its coefficient can be made arbitrarily small uniformly over nearby
base points, using only the certified `C²` regularity of the potential. -/
theorem RegularPotential.exists_uniform_gradient_linearization_error
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (h : RegularPotential potential gradient β)
    {S : Set (Position ι)} (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ δ →
      ‖gradient y - gradient x - fderiv ℝ gradient x (y - x)‖ ≤
        η * ‖y - x‖ := by
  obtain ⟨δ, hδ, hderiv⟩ :=
    Metric.uniformContinuousOn_iff_le.mp
      (h.uniformContinuousOn_fderiv_gradient hScompact) η hη
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy hxy
  apply (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le'
    (φ := fderiv ℝ gradient x)
  · intro z hz
    exact h.contDiff_one_gradient.differentiable (by norm_num) z
  · intro z hz
    have hzS : z ∈ S := hSconvex.segment_subset hx hy hz
    have hzx : dist z x ≤ δ := by
      exact (Metric.mem_closedBall.mp (segment_subset_closedBall_left x y hz)).trans hxy
    simpa only [dist_eq_norm] using hderiv z hzS x hx hzx
  · exact left_mem_segment ℝ x y
  · exact right_mem_segment ℝ x y

/-- A force difference is the integral of the gradient derivative along the
line segment joining its two arguments. This representation preserves the
paired cancellation needed in relative leapfrog error estimates. -/
theorem RegularPotential.intervalIntegral_fderiv_gradient_lineMap
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (h : RegularPotential potential gradient β)
    (x y : Position ι) :
    (∫ r in (0 : ℝ)..1,
        fderiv ℝ gradient (AffineMap.lineMap x y r) (y - x)) =
      gradient y - gradient x := by
  let F : ℝ → Position ι := fun r ↦ gradient (AffineMap.lineMap x y r)
  let F' : ℝ → Position ι := fun r ↦
    fderiv ℝ gradient (AffineMap.lineMap x y r) (y - x)
  have hFderiv : ∀ r : ℝ, HasDerivAt F (F' r) r := by
    intro r
    exact (h.contDiff_one_gradient.differentiable (by norm_num)
      (AffineMap.lineMap x y r)).hasFDerivAt.comp_hasDerivAt r
        AffineMap.hasDerivAt_lineMap
  have hderiv : deriv F = F' := by
    funext r
    exact (hFderiv r).deriv
  have hcont : Continuous F' := by
    exact (h.continuous_fderiv_gradient.comp
      (continuous_iff_continuousAt.mpr fun _ ↦
        AffineMap.hasDerivAt_lineMap.continuousAt)).clm_apply continuous_const
  have hFTC := intervalIntegral.integral_deriv_eq_sub'
    (a := (0 : ℝ)) (b := 1) F hderiv
      (fun r hr ↦ (hFderiv r).differentiableAt) hcont.continuousOn
  simpa [F, F'] using hFTC

/-- Four-point force variation obtained by comparing the derivative of the
gradient at corresponding points of two line segments. The first term records
motion of the segment, while the second records change of its direction. -/
theorem RegularPotential.norm_gradientSub_sub_gradientSub_le_of_lineMap
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (h : RegularPotential potential gradient β)
    {x₀ y₀ x₁ y₁ : Position ι} {η M : ℝ}
    (hderivDiff : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ gradient (AffineMap.lineMap x₁ y₁ r) -
          fderiv ℝ gradient (AffineMap.lineMap x₀ y₀ r)‖ ≤ η)
    (hderivBound : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ gradient (AffineMap.lineMap x₁ y₁ r)‖ ≤ M) :
    ‖(gradient y₁ - gradient x₁) -
        (gradient y₀ - gradient x₀)‖ ≤
      η * ‖y₀ - x₀‖ + M * ‖(y₁ - x₁) - (y₀ - x₀)‖ := by
  let A : ℝ → Position ι := fun r ↦
    fderiv ℝ gradient (AffineMap.lineMap x₁ y₁ r) (y₁ - x₁)
  let B : ℝ → Position ι := fun r ↦
    fderiv ℝ gradient (AffineMap.lineMap x₀ y₀ r) (y₀ - x₀)
  have hlineContinuous (x y : Position ι) :
      Continuous (AffineMap.lineMap (k := ℝ) x y) :=
    continuous_iff_continuousAt.mpr fun _ ↦
      AffineMap.hasDerivAt_lineMap.continuousAt
  have hAcont : Continuous A :=
    (h.continuous_fderiv_gradient.comp
      (hlineContinuous x₁ y₁)).clm_apply continuous_const
  have hBcont : Continuous B :=
    (h.continuous_fderiv_gradient.comp
      (hlineContinuous x₀ y₀)).clm_apply continuous_const
  have hAint : IntervalIntegrable A MeasureTheory.volume 0 1 :=
    hAcont.continuousOn.intervalIntegrable_of_Icc zero_le_one
  have hBint : IntervalIntegrable B MeasureTheory.volume 0 1 :=
    hBcont.continuousOn.intervalIntegrable_of_Icc zero_le_one
  have hbound : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      ‖A r - B r‖ ≤
        η * ‖y₀ - x₀‖ + M * ‖(y₁ - x₁) - (y₀ - x₀)‖ := by
    intro r hr
    let D₁ := fderiv ℝ gradient (AffineMap.lineMap x₁ y₁ r)
    let D₀ := fderiv ℝ gradient (AffineMap.lineMap x₀ y₀ r)
    have hid : A r - B r =
        (D₁ - D₀) (y₀ - x₀) +
          D₁ ((y₁ - x₁) - (y₀ - x₀)) := by
      dsimp [A, B, D₁, D₀]
      simp only [sub_apply, map_sub]
      abel
    rw [hid]
    apply (norm_add_le _ _).trans
    have hfirst := (D₁ - D₀).le_opNorm (y₀ - x₀)
    have hsecond := D₁.le_opNorm ((y₁ - x₁) - (y₀ - x₀))
    exact add_le_add
      (hfirst.trans (mul_le_mul_of_nonneg_right
        (hderivDiff r hr) (norm_nonneg _)))
      (hsecond.trans (mul_le_mul_of_nonneg_right
        (hderivBound r hr) (norm_nonneg _)))
  rw [← h.intervalIntegral_fderiv_gradient_lineMap x₁ y₁,
    ← h.intervalIntegral_fderiv_gradient_lineMap x₀ y₀,
    ← intervalIntegral.integral_sub hAint hBint]
  exact (intervalIntegral.norm_integral_le_of_norm_le_const fun r hr ↦
    hbound r (by
      rw [Set.uIoc_of_le zero_le_one] at hr
      exact Set.mem_Icc.mpr ⟨hr.1.le, hr.2⟩)).trans_eq (by ring)

/-- The derivative of the gradient has a common operator-norm bound on every
compact position region. -/
theorem RegularPotential.exists_compact_fderiv_gradient_bound
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (h : RegularPotential potential gradient β)
    {S : Set (Position ι)} (hS : IsCompact S) :
    ∃ M ≥ 0, ∀ x ∈ S, ‖fderiv ℝ gradient x‖ ≤ M := by
  obtain ⟨C, hC⟩ := hS.bddAbove_image
    h.continuous_fderiv_gradient.norm.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx
  exact (hC (Set.mem_image_of_mem _ hx)).trans (le_max_left _ _)

/-- The global gradient Lipschitz certificate gives an explicit global
operator-norm bound for its derivative in mathlib's ambient norm. -/
theorem RegularPotential.norm_fderiv_gradient_le_global
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (h : RegularPotential potential gradient β) (x : Position ι) :
    ‖fderiv ℝ gradient x‖ ≤
      ((β * (Fintype.card ι + 1 : NNReal) : NNReal) : ℝ) := by
  simpa only [NNReal.coe_mul, Nat.cast_add, Nat.cast_one,
    NNReal.coe_natCast] using
      norm_fderiv_le_of_lipschitz ℝ h.lipschitzWith_gradient

/-- Compact-uniform four-point force modulus. If corresponding points of two
position segments are uniformly close, their force differences differ by an
arbitrarily small multiple of the old separation, plus a bounded multiple of
the change in separation. -/
theorem RegularPotential.exists_uniform_gradientSub_sub_gradientSub_bound
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (h : RegularPotential potential gradient β)
    {S : Set (Position ι)} (hS : IsCompact S)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ M ≥ 0,
      M ≤ ((β * (Fintype.card ι + 1 : NNReal) : NNReal) : ℝ) ∧
      ∀ {x₀ y₀ x₁ y₁ : Position ι},
        (∀ r ∈ Set.Icc (0 : ℝ) 1,
          AffineMap.lineMap x₀ y₀ r ∈ S) →
        (∀ r ∈ Set.Icc (0 : ℝ) 1,
          AffineMap.lineMap x₁ y₁ r ∈ S) →
        (∀ r ∈ Set.Icc (0 : ℝ) 1,
          dist (AffineMap.lineMap x₁ y₁ r)
            (AffineMap.lineMap x₀ y₀ r) ≤ δ) →
        ‖(gradient y₁ - gradient x₁) -
            (gradient y₀ - gradient x₀)‖ ≤
          η * ‖y₀ - x₀‖ +
            M * ‖(y₁ - x₁) - (y₀ - x₀)‖ := by
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff_le.mp
    (h.uniformContinuousOn_fderiv_gradient hS) η hη
  let M : ℝ := ((β * (Fintype.card ι + 1 : NNReal) : NNReal) : ℝ)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨δ, hδ, M, hM, le_rfl, ?_⟩
  intro x₀ y₀ x₁ y₁ hseg₀ hseg₁ hsegmentsClose
  apply h.norm_gradientSub_sub_gradientSub_le_of_lineMap
  · intro r hr
    simpa only [dist_eq_norm] using hclose _ (hseg₁ r hr) _ (hseg₀ r hr)
      (hsegmentsClose r hr)
  · intro r hr
    exact h.norm_fderiv_gradient_le_global _

/-- Corresponding points of two line segments are no farther apart than a
common endpoint-displacement bound. -/
theorem dist_lineMap_lineMap_le_of_endpoints
    {x₀ y₀ x₁ y₁ : Position ι} {δ r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (hx : dist x₁ x₀ ≤ δ) (hy : dist y₁ y₀ ≤ δ) :
    dist (AffineMap.lineMap x₁ y₁ r)
        (AffineMap.lineMap x₀ y₀ r) ≤ δ := by
  rw [dist_eq_norm]
  have hid :
      AffineMap.lineMap x₁ y₁ r - AffineMap.lineMap x₀ y₀ r =
        (1 - r) • (x₁ - x₀) + r • (y₁ - y₀) := by
    simp only [AffineMap.lineMap_apply_module]
    module
  rw [hid]
  apply (norm_add_le _ _).trans
  rw [norm_smul, norm_smul]
  change |1 - r| * ‖x₁ - x₀‖ + |r| * ‖y₁ - y₀‖ ≤ δ
  rw [abs_of_nonneg hr.1, abs_of_nonneg (sub_nonneg.mpr hr.2)]
  have hx' : ‖x₁ - x₀‖ ≤ δ := by simpa only [dist_eq_norm] using hx
  have hy' : ‖y₁ - y₀‖ ≤ δ := by simpa only [dist_eq_norm] using hy
  calc
    (1 - r) * ‖x₁ - x₀‖ + r * ‖y₁ - y₀‖ ≤
        (1 - r) * δ + r * δ :=
      add_le_add
        (mul_le_mul_of_nonneg_left hx' (sub_nonneg.mpr hr.2))
        (mul_le_mul_of_nonneg_left hy' hr.1)
    _ = δ := by ring

/-- Euclidean-norm form of the compact-uniform four-point force estimate,
with segment containment and correspondence reduced to endpoint conditions. -/
theorem RegularPotential.exists_uniform_euclideanNorm_gradientSub_sub_gradientSub_bound
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (h : RegularPotential potential gradient β)
    {S : Set (Position ι)} (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ M ≥ 0,
      M ≤ ((β * (Fintype.card ι + 1 : NNReal) : NNReal) : ℝ) ∧
      ∀ {x₀ y₀ x₁ y₁ : Position ι},
        x₀ ∈ S → y₀ ∈ S → x₁ ∈ S → y₁ ∈ S →
        dist x₁ x₀ ≤ δ → dist y₁ y₀ ≤ δ →
        euclideanNorm
            ((gradient y₁ - gradient x₁) -
              (gradient y₀ - gradient x₀)) ≤
          ((Fintype.card ι : ℝ) + 1) *
            (η * euclideanNorm (y₀ - x₀) +
              M * euclideanNorm ((y₁ - x₁) - (y₀ - x₀))) := by
  obtain ⟨δ, hδ, M, hM, hMglobal, hfour⟩ :=
    h.exists_uniform_gradientSub_sub_gradientSub_bound hScompact hη
  refine ⟨δ, hδ, M, hM, hMglobal, ?_⟩
  intro x₀ y₀ x₁ y₁ hx₀ hy₀ hx₁ hy₁ hxclose hyclose
  have hambient := hfour
    (fun r hr ↦ hSconvex.lineMap_mem hx₀ hy₀ hr)
    (fun r hr ↦ hSconvex.lineMap_mem hx₁ hy₁ hr)
    (fun r hr ↦ dist_lineMap_lineMap_le_of_endpoints hr hxclose hyclose)
  have heuc := euclideanNorm_sub_le_card_succ_mul_dist
    ((gradient y₁ - gradient x₁) - (gradient y₀ - gradient x₀)) 0
  simp only [sub_zero, dist_zero_right] at heuc
  apply heuc.trans
  have hD : 0 ≤ (Fintype.card ι : ℝ) + 1 := by positivity
  apply (mul_le_mul_of_nonneg_left hambient hD).trans
  have hbase : ‖y₀ - x₀‖ ≤ euclideanNorm (y₀ - x₀) := by
    simpa only [dist_eq_norm] using dist_le_euclideanNorm_sub y₀ x₀
  have hchange : ‖(y₁ - x₁) - (y₀ - x₀)‖ ≤
      euclideanNorm ((y₁ - x₁) - (y₀ - x₀)) := by
    have hdist := dist_le_euclideanNorm_sub
      ((y₁ - x₁) - (y₀ - x₀)) 0
    simpa only [sub_zero, dist_zero_right] using hdist
  have hηnonneg : 0 ≤ η := hη.le
  calc
    ((Fintype.card ι : ℝ) + 1) *
        (η * ‖y₀ - x₀‖ + M * ‖(y₁ - x₁) - (y₀ - x₀)‖) ≤
      ((Fintype.card ι : ℝ) + 1) *
        (η * euclideanNorm (y₀ - x₀) +
          M * euclideanNorm ((y₁ - x₁) - (y₀ - x₀))) := by
      gcongr
    _ = _ := rfl

/-- Relative form of the compact-uniform four-point force estimate. A relative
change `R` in the paired separation produces the force modulus
`(d+1)(η + M R)`. -/
theorem RegularPotential.exists_uniform_relative_forceVariation_bound
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (h : RegularPotential potential gradient β)
    {S : Set (Position ι)} (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ M ≥ 0,
      ∀ {x₀ y₀ x₁ y₁ : Position ι} {R : ℝ},
        x₀ ∈ S → y₀ ∈ S → x₁ ∈ S → y₁ ∈ S →
        dist x₁ x₀ ≤ δ → dist y₁ y₀ ≤ δ →
        euclideanNorm ((y₁ - x₁) - (y₀ - x₀)) ≤
          R * euclideanNorm (y₀ - x₀) →
        euclideanNorm
            ((gradient y₁ - gradient x₁) -
              (gradient y₀ - gradient x₀)) ≤
          ((Fintype.card ι : ℝ) + 1) * (η + M * R) *
            euclideanNorm (y₀ - x₀) := by
  obtain ⟨δ, hδ, M, hM, _hMglobal, hfour⟩ :=
    h.exists_uniform_euclideanNorm_gradientSub_sub_gradientSub_bound
      hScompact hSconvex hη
  refine ⟨δ, hδ, M, hM, ?_⟩
  intro x₀ y₀ x₁ y₁ R hx₀ hy₀ hx₁ hy₁ hxclose hyclose hrelative
  have hbase : 0 ≤ euclideanNorm (y₀ - x₀) := euclideanNorm_nonneg _
  have hmain := hfour hx₀ hy₀ hx₁ hy₁ hxclose hyclose
  apply hmain.trans
  have hMrelative := mul_le_mul_of_nonneg_left hrelative hM
  calc
    ((Fintype.card ι : ℝ) + 1) *
        (η * euclideanNorm (y₀ - x₀) +
          M * euclideanNorm ((y₁ - x₁) - (y₀ - x₀))) ≤
      ((Fintype.card ι : ℝ) + 1) *
        (η * euclideanNorm (y₀ - x₀) +
          M * (R * euclideanNorm (y₀ - x₀))) := by
      gcongr
    _ = ((Fintype.card ι : ℝ) + 1) * (η + M * R) *
        euclideanNorm (y₀ - x₀) := by ring

/-- A regular potential is uniformly continuous on every compact region. -/
theorem RegularPotential.uniformContinuousOn
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (h : RegularPotential potential gradient β)
    {S : Set (Position ι)} (hS : IsCompact S) :
    UniformContinuousOn potential S :=
  hS.uniformContinuousOn_of_continuous h.contDiff_two.continuous.continuousOn

/-- Metric epsilon--delta form of compact-uniform continuity, ready for
uniform trajectory approximation arguments. -/
theorem RegularPotential.exists_uniform_potential_error
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (h : RegularPotential potential gradient β)
    {S : Set (Position ι)} (hS : IsCompact S) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ q₁ ∈ S, ∀ q₂ ∈ S,
      dist q₁ q₂ ≤ δ → |potential q₁ - potential q₂| ≤ η := by
  rcases Metric.uniformContinuousOn_iff_le.mp (h.uniformContinuousOn hS)
      η hη with ⟨δ, hδ, hbound⟩
  refine ⟨δ, hδ, ?_⟩
  intro q₁ hq₁ q₂ hq₂ hdist
  simpa only [Real.dist_eq] using hbound q₁ hq₁ q₂ hq₂ hdist

/-- Compact-uniform continuity expressed in the explicit Euclidean geometry
used by the leapfrog estimates. -/
theorem RegularPotential.exists_uniform_potential_error_euclidean
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (h : RegularPotential potential gradient β)
    {S : Set (Position ι)} (hS : IsCompact S) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ q₁ ∈ S, ∀ q₂ ∈ S,
      euclideanNorm (q₁ - q₂) ≤ δ →
        |potential q₁ - potential q₂| ≤ η := by
  rcases h.exists_uniform_potential_error hS hη with ⟨δ, hδ, hpotential⟩
  refine ⟨δ, hδ, ?_⟩
  intro q₁ hq₁ q₂ hq₂ hdist
  exact hpotential q₁ hq₁ q₂ hq₂
    (le_trans (dist_le_euclideanNorm_sub q₁ q₂) hdist)

/-- The local strong-convexity inequality in the orientation used by the
shared-momentum difference dynamics. -/
theorem LocalStrongConvexity.inner_gradient_sub_lower
    {gradient : Position ι → Position ι} {S : Set (Position ι)} {α : ℝ}
    (h : LocalStrongConvexity gradient S α) {q₁ q₂ : Position ι}
    (hq₁ : q₁ ∈ S) (hq₂ : q₂ ∈ S) :
    α * squaredEuclideanNorm (q₁ - q₂) ≤
      euclideanInner (q₁ - q₂) (gradient q₁ - gradient q₂) :=
  h.strongMonotone q₁ hq₁ q₂ hq₂

/-- At two distinct points in the strongly convex region, the Euclidean
gradient pairing with their displacement is strictly positive. -/
theorem LocalStrongConvexity.inner_gradient_sub_pos
    {gradient : Position ι → Position ι} {S : Set (Position ι)} {α : ℝ}
    (h : LocalStrongConvexity gradient S α) {q₁ q₂ : Position ι}
    (hq₁ : q₁ ∈ S) (hq₂ : q₂ ∈ S) (hne : q₁ ≠ q₂) :
    0 < euclideanInner (q₁ - q₂) (gradient q₁ - gradient q₂) := by
  apply lt_of_lt_of_le _ (h.inner_gradient_sub_lower hq₁ hq₂)
  exact mul_pos h.alpha_pos
    (squaredEuclideanNorm_pos (sub_ne_zero.mpr hne))

end Mcmc.Hamiltonian
