import Mcmc.Hamiltonian.Assumptions
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Transform

/-!
# Exact Hamiltonian curves and separation calculus

This module supplies the differential core of the shared-momentum contraction
argument.  An `IsHamiltonianCurve` is a coordinatewise classical solution of
the unit-mass Hamilton equations `q' = p`, `p' = -∇U(q)`.  The main results
differentiate squared Euclidean separation and show that, when two curves
start with the same momentum in the locally strongly convex region, its
second variation is strictly negative.

This is the pointwise calculus component of Lemma 4.2 of Xu et al. Time
reversal extends the quantitative contraction estimate to both signs of the
integration time. The compact-uniform exact-flow component of Lemma 4.2 is
now complete. Global
gradient Lipschitzness and Grönwall stability derive relative motion and
absolute phase growth; a compact core inside the strong-convexity-region
interior supplies a uniform containment buffer; continuity at time zero then
selects one common positive contraction horizon. A normed-space continuation
argument also constructs a global exact curve from every initial phase.
-/

open scoped BigOperators Pointwise
open Set Topology
open Filter SignType

namespace Mcmc.Hamiltonian

variable {ι : Type*} [Fintype ι]

section GlobalIntegralCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {v : E → E} {K : NNReal} {γ γ' : ℝ → E} {t₀ : ℝ}

/-- Two autonomous integral curves with a common value agree throughout an
overlapping open interval when the vector field is globally Lipschitz. -/
lemma integralCurveOn_Ioo_eqOn
    (hv : LipschitzWith K v)
    {a b a' b' : ℝ}
    (hγ : IsIntegralCurveOn γ (fun _ => v) (Ioo a b))
    (hγ' : IsIntegralCurveOn γ' (fun _ => v) (Ioo a' b'))
    (ht₀ : t₀ ∈ Ioo a b ∩ Ioo a' b') (h : γ t₀ = γ' t₀) :
    EqOn γ γ' (Ioo (max a a') (min b b')) := by
  apply ODE_solution_unique_of_mem_Ioo
      (K := K) (s := fun _ => Set.univ)
      (v := fun _ => v) (t₀ := t₀)
  · intro t ht
    exact hv.lipschitzOnWith
  · exact ⟨max_lt ht₀.1.1 ht₀.2.1, lt_min ht₀.1.2 ht₀.2.2⟩
  · intro t ht
    have ht' : t ∈ Ioo a b :=
      ⟨lt_of_le_of_lt (le_max_left _ _) ht.1,
        lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
    exact ⟨(hγ t ht').hasDerivAt (isOpen_Ioo.mem_nhds ht'), Set.mem_univ _⟩
  · intro t ht
    have ht' : t ∈ Ioo a' b' :=
      ⟨lt_of_le_of_lt (le_max_right _ _) ht.1,
        lt_of_lt_of_le ht.2 (min_le_right _ _)⟩
    exact ⟨(hγ' t ht').hasDerivAt (isOpen_Ioo.mem_nhds ht'), Set.mem_univ _⟩
  · exact h

/-- Patching two overlapping autonomous integral curves gives an integral
curve on the union of their domains. -/
lemma integralCurveOn_piecewise
    (hv : LipschitzWith K v)
    {a b a' b' : ℝ}
    (hγ : IsIntegralCurveOn γ (fun _ => v) (Ioo a b))
    (hγ' : IsIntegralCurveOn γ' (fun _ => v) (Ioo a' b'))
    (ht₀ : t₀ ∈ Ioo a b ∩ Ioo a' b') (h : γ t₀ = γ' t₀) :
    IsIntegralCurveOn (Set.piecewise (Ioo a b) γ γ') (fun _ => v)
      (Ioo a b ∪ Ioo a' b') := by
  have heq : EqOn γ γ' (Ioo (max a a') (min b b')) :=
    integralCurveOn_Ioo_eqOn hv hγ hγ' ht₀ h
  intro t ht
  by_cases hmem : t ∈ Ioo a b
  · rw [Set.piecewise, if_pos hmem]
    apply (hγ t hmem).hasDerivAt (isOpen_Ioo.mem_nhds hmem) |>.hasDerivWithinAt
      |>.congr_of_eventuallyEq _ (by rw [Set.piecewise, if_pos hmem])
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Ioo a b, ?_, fun _ hs => by rw [Set.piecewise, if_pos hs]⟩
    rw [(isOpen_Ioo.union isOpen_Ioo).nhdsWithin_eq ht]
    exact isOpen_Ioo.mem_nhds hmem
  · have ht' : t ∈ Ioo a' b' := (Set.mem_union _ _ _).mp ht |>.resolve_left hmem
    rw [Set.piecewise, if_neg hmem]
    apply (hγ' t ht').hasDerivAt (isOpen_Ioo.mem_nhds ht') |>.hasDerivWithinAt
      |>.congr_of_eventuallyEq _ (by rw [Set.piecewise, if_neg hmem])
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Ioo a' b', ?_, ?_⟩
    · rw [(isOpen_Ioo.union isOpen_Ioo).nhdsWithin_eq ht]
      exact isOpen_Ioo.mem_nhds ht'
    · intro s hs
      by_cases hs' : s ∈ Ioo a b
      · rw [Set.piecewise, if_pos hs']
        apply heq
        exact ⟨max_lt hs'.1 hs.1, lt_min hs'.2 hs.2⟩
      · rw [Set.piecewise, if_neg hs']

/-- Uniform positive local existence plus global Lipschitz uniqueness implies
global existence for an autonomous ODE on a normed vector space. -/
theorem exists_globalIntegralCurve_of_uniform_local
    (hv : LipschitzWith K v)
    {ε : ℝ} (hε : 0 < ε)
    (hloc : ∀ x : E, ∃ γ : ℝ → E, γ 0 = x ∧
      IsIntegralCurveOn γ (fun _ => v) (Ioo (-ε) ε))
    (x : E) : ∃ γ : ℝ → E, γ 0 = x ∧ IsIntegralCurve γ (fun _ => v) := by
  let s : Set ℝ := {a | ∃ γ : ℝ → E, γ 0 = x ∧
    IsIntegralCurveOn γ (fun _ => v) (Ioo (-a) a)}
  suffices hbdd : ¬ BddAbove s by
    rw [not_bddAbove_iff] at hbdd
    have hfamily : ∀ r : ℝ, ∃ γ : ℝ → E, γ 0 = x ∧
        IsIntegralCurveOn γ (fun _ => v) (Ioo (-r) r) := by
      intro r
      obtain ⟨a, ⟨γ, hγ0, hγ⟩, hra⟩ := hbdd r
      exact ⟨γ, hγ0, hγ.mono (Ioo_subset_Ioo (neg_le_neg hra.le) hra.le)⟩
    choose γ hγ0 hγ using hfamily
    let Γ : ℝ → E := fun t => γ (|t| + 1) t
    refine ⟨Γ, hγ0 (|0| + 1), ?_⟩
    intro t
    have ht : t ∈ Ioo (-(|t| + 1)) (|t| + 1) := by
      rw [Set.mem_Ioo, ← abs_lt]
      exact lt_add_one _
    have hlocal := hγ (|t| + 1)
    apply HasDerivAt.congr_of_eventuallyEq
        ((hlocal t ht).hasDerivAt (isOpen_Ioo.mem_nhds ht))
    · rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨Ioo (-(|t| + 1)) (|t| + 1), isOpen_Ioo.mem_nhds ht, ?_⟩
      intro u hu
      dsimp [Γ]
      have huSelf : u ∈ Ioo (-(|u| + 1)) (|u| + 1) := by
        rw [Set.mem_Ioo, ← abs_lt]
        exact lt_add_one _
      have hposu : 0 < |u| + 1 := by linarith [abs_nonneg u]
      have hpost : 0 < |t| + 1 := by linarith [abs_nonneg t]
      by_cases hle : |u| + 1 ≤ |t| + 1
      · exact (integralCurveOn_Ioo_eqOn (t₀ := 0) hv
          (hγ (|u| + 1)) hlocal
          ⟨⟨neg_lt_zero.mpr hposu, hposu⟩,
            ⟨neg_lt_zero.mpr hpost, hpost⟩⟩
          (by rw [hγ0, hγ0]))
          ⟨max_lt huSelf.1 hu.1, lt_min huSelf.2 hu.2⟩
      · exact ((integralCurveOn_Ioo_eqOn (t₀ := 0) hv hlocal
          (hγ (|u| + 1))
          ⟨⟨neg_lt_zero.mpr hpost, hpost⟩,
            ⟨neg_lt_zero.mpr hposu, hposu⟩⟩
          (by rw [hγ0, hγ0]))
          ⟨max_lt hu.1 huSelf.1, lt_min hu.2 huSelf.2⟩).symm
  intro hbdd
  set asup := sSup s with hasup
  obtain ⟨a, ha, hlt⟩ := Real.add_neg_lt_sSup
      (⟨ε, hloc x⟩ : Set.Nonempty s) (ε := -(ε / 2))
      (by rw [neg_lt, neg_zero]; exact half_pos hε)
  rw [Set.mem_setOf] at ha
  rw [← hasup, ← sub_eq_add_neg] at hlt
  obtain ⟨γ, h0, hγ⟩ := ha
  obtain ⟨γ1aux, h1, hγ1⟩ := hloc (γ (-(asup - ε / 2)))
  rw [← isIntegralCurveOn_comp_add (dt := asup - ε / 2)] at hγ1
  let γ1 := γ1aux ∘ (· + (asup - ε / 2))
  have heq1 : γ1 (-(asup - ε / 2)) = γ (-(asup - ε / 2)) := by
    simp [γ1, h1]
  obtain ⟨γ2aux, h2, hγ2⟩ := hloc (γ (asup - ε / 2))
  rw [← isIntegralCurveOn_comp_sub (dt := asup - ε / 2)] at hγ2
  let γ2 := γ2aux ∘ (· - (asup - ε / 2))
  have heq2 : γ2 (asup - ε / 2) = γ (asup - ε / 2) := by
    simp [γ2, h2]
  have hγ1I : IsIntegralCurveOn γ1 (fun _ => v)
      (Ioo (-(asup + ε / 2)) (-(asup - 3 * ε / 2))) := by
    simpa only [γ1, Function.comp_def] using hγ1.mono (by
      intro t ht
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      simp only [vadd_eq_add, neg_neg, Set.mem_Ioo]
      constructor <;> linarith [ht.1, ht.2])
  have hγ2I : IsIntegralCurveOn γ2 (fun _ => v)
      (Ioo (asup - 3 * ε / 2) (asup + ε / 2)) := by
    simpa only [γ2, Function.comp_def] using hγ2.mono (by
      intro t ht
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      simp only [vadd_eq_add, Set.mem_Ioo]
      constructor <;> linarith [ht.1, ht.2])
  have hεle : ε ≤ asup := le_csSup hbdd (hloc x)
  let γext : ℝ → E := Set.piecewise (Ioo (-(asup + ε / 2)) a)
    (Set.piecewise (Ioo (-a) a) γ γ1) γ2
  have heqext : γext 0 = x := by
    dsimp [γext]
    rw [Set.piecewise, if_pos ⟨by linarith, by linarith⟩,
      Set.piecewise, if_pos ⟨by linarith, by linarith⟩, h0]
  suffices hext : IsIntegralCurveOn γext (fun _ => v)
      (Ioo (-(asup + ε / 2)) (asup + ε / 2)) from
    (not_lt.mpr (le_csSup hbdd ⟨γext, heqext, hext⟩))
      (lt_add_of_pos_right asup (half_pos hε))
  apply (integralCurveOn_piecewise (t₀ := asup - ε / 2) hv _ hγ2I
      ⟨⟨by linarith, hlt⟩, ⟨by linarith, by linarith⟩⟩
      (by rw [Set.piecewise, if_pos ⟨by linarith, hlt⟩, ← heq2])).mono
    (Ioo_subset_Ioo_union_Ioo le_rfl (by linarith) (by linarith))
  exact (integralCurveOn_piecewise (t₀ := -(asup - ε / 2)) hv hγ hγ1I
      ⟨⟨neg_lt_neg hlt, by linarith⟩, ⟨by linarith, by linarith⟩⟩ heq1.symm).mono
    (union_comm _ _ ▸ Ioo_subset_Ioo_union_Ioo (by linarith) (by linarith) le_rfl)

end GlobalIntegralCurve

/-- The autonomous unit-mass Hamiltonian vector field on phase space. -/
def hamiltonianVectorField
    (gradient : Position ι → Position ι) (z : PhaseSpace ι) : PhaseSpace ι :=
  (z.2, -gradient z.1)

/-- The ordinary mathlib Lipschitz constant of the Hamiltonian phase vector
field.  The dimension factor reconciles the explicit Euclidean norm in the
paper's assumption with the ambient finite-product norm. -/
noncomputable def hamiltonianVectorFieldLipschitzConstant
    (β : NNReal) : NNReal :=
  max 1 (β * (Fintype.card ι + 1 : NNReal))

theorem RegularPotential.lipschitzWith_hamiltonianVectorField
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β) :
    LipschitzWith (hamiltonianVectorFieldLipschitzConstant (ι := ι) β)
      (hamiltonianVectorField gradient) := by
  have hposition : LipschitzWith (1 : NNReal)
      (fun z : PhaseSpace ι => z.2) := LipschitzWith.prod_snd
  have hfst : LipschitzWith (1 : NNReal)
      (fun z : PhaseSpace ι => z.1) := LipschitzWith.prod_fst
  have hforce : LipschitzWith (β * (Fintype.card ι + 1 : NNReal))
      (fun z : PhaseSpace ι => -gradient z.1) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    rw [dist_neg_neg]
    simpa only [Function.comp_apply, one_mul, mul_one] using
      (hreg.lipschitzWith_gradient.comp hfst).dist_le_mul z w
  exact hposition.prodMk hforce

theorem hamiltonianVectorFieldLipschitzConstant_pos (β : NNReal) :
    0 < hamiltonianVectorFieldLipschitzConstant (ι := ι) β := by
  exact zero_lt_one.trans_le (le_max_left _ _)

/-- A globally Lipschitz Hamiltonian field has affine norm growth about the
origin.  This is the continuation bound needed to turn local Picard solutions
into global Hamiltonian curves. -/
theorem RegularPotential.norm_hamiltonianVectorField_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (z : PhaseSpace ι) :
    ‖hamiltonianVectorField gradient z‖ ≤
      (hamiltonianVectorFieldLipschitzConstant (ι := ι) β : ℝ) * ‖z‖ +
        ‖hamiltonianVectorField gradient 0‖ := by
  have hdist := hreg.lipschitzWith_hamiltonianVectorField.dist_le_mul z 0
  have htriangle := norm_le_norm_sub_add
    (hamiltonianVectorField gradient z) (hamiltonianVectorField gradient 0)
  apply htriangle.trans
  exact add_le_add
    (by simpa only [dist_eq_norm, dist_zero_right, sub_zero] using hdist) le_rfl

/-- A coordinatewise classical solution of the unit-mass Hamilton equations. -/
structure IsHamiltonianCurve
    (gradient : Position ι → Position ι)
    (q : ℝ → Position ι) (p : ℝ → Momentum ι) : Prop where
  position_deriv : ∀ t i, HasDerivAt (fun s => q s i) (p t i) t
  momentum_deriv : ∀ t i,
    HasDerivAt (fun s => p s i) (-(gradient (q t) i)) t

/-- A phase-space integral curve of the autonomous Hamiltonian vector field
is a coordinatewise Hamiltonian curve. -/
theorem IsIntegralCurve.isHamiltonianCurve
    {gradient : Position ι → Position ι} {z : ℝ → PhaseSpace ι}
    (hz : IsIntegralCurve z (fun _ => hamiltonianVectorField gradient)) :
    IsHamiltonianCurve gradient (fun t => (z t).1) (fun t => (z t).2) := by
  constructor
  · intro t
    have hfst : HasDerivAt (fun s => (z s).1) (z t).2 t := by
      have h := hasFDerivAt_fst.comp_hasDerivAt t (hz t)
      exact h
    exact hasDerivAt_pi.mp hfst
  · intro t
    have hsnd : HasDerivAt (fun s => (z s).2) (-gradient (z t).1) t := by
      have h := hasFDerivAt_snd.comp_hasDerivAt t (hz t)
      exact h
    exact hasDerivAt_pi.mp hsnd

/-- Conversely, the paired coordinate curves of a Hamiltonian solution form
an integral curve of the autonomous phase vector field. -/
theorem IsHamiltonianCurve.isIntegralCurve
    {gradient : Position ι → Position ι}
    {q : ℝ → Position ι} {p : ℝ → Momentum ι}
    (h : IsHamiltonianCurve gradient q p) :
    IsIntegralCurve (fun t => (q t, p t))
      (fun _ => hamiltonianVectorField gradient) := by
  intro t
  apply HasDerivAt.prodMk
  · exact hasDerivAt_pi.mpr (h.position_deriv t)
  · exact hasDerivAt_pi.mpr (h.momentum_deriv t)

/-- Global Lipschitzness gives one positive local existence time that is
uniform over all initial phase points.  The spatial Picard ball and vector
field bound may grow with the initial norm, but their ratio has a common
positive lower bound because the field has affine growth. -/
theorem RegularPotential.exists_uniform_local_hamiltonianIntegralCurve
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β) :
    ∃ ε > 0, ∀ z₀ : PhaseSpace ι, ∃ z : ℝ → PhaseSpace ι,
      z 0 = z₀ ∧
        IsIntegralCurveOn z (fun _ => hamiltonianVectorField gradient)
          (Set.Ioo (-ε) ε) := by
  let K := hamiltonianVectorFieldLipschitzConstant (ι := ι) β
  let b : NNReal := ⟨‖hamiltonianVectorField gradient 0‖, norm_nonneg _⟩
  let εn : NNReal := (2 * K + K + b + 1)⁻¹
  have hden : 0 < 2 * K + K + b + 1 := by positivity
  have hεn : 0 < εn := inv_pos.mpr hden
  refine ⟨(εn : ℝ), by exact_mod_cast hεn, ?_⟩
  intro z₀
  let zn : NNReal := ⟨‖z₀‖, norm_nonneg _⟩
  let a : NNReal := zn + 1
  let L : NNReal := K * (2 * zn + 1) + b
  have ha : 0 < a := by dsimp [a]; positivity
  have hL : 0 < L := by
    dsimp [L]
    have hK : 0 < K := hamiltonianVectorFieldLipschitzConstant_pos β
    positivity
  have hnorm : ∀ x ∈ Metric.closedBall z₀ (a : ℝ),
      ‖hamiltonianVectorField gradient x‖ ≤ (L : ℝ) := by
    intro x hx
    have hdist : dist x z₀ ≤ (a : ℝ) := Metric.mem_closedBall.mp hx
    have hlip := hreg.lipschitzWith_hamiltonianVectorField.dist_le_mul x z₀
    have htri := norm_le_norm_sub_add
      (hamiltonianVectorField gradient x)
      (hamiltonianVectorField gradient z₀)
    have hz₀ := hreg.norm_hamiltonianVectorField_le z₀
    apply htri.trans
    calc
      ‖hamiltonianVectorField gradient x -
          hamiltonianVectorField gradient z₀‖ +
          ‖hamiltonianVectorField gradient z₀‖ ≤
        (K : ℝ) * dist x z₀ +
          ((K : ℝ) * ‖z₀‖ + (b : ℝ)) :=
        add_le_add (by simpa only [dist_eq_norm] using hlip) hz₀
      _ ≤ (K : ℝ) * (a : ℝ) +
          ((K : ℝ) * ‖z₀‖ + (b : ℝ)) := by gcongr
      _ = (L : ℝ) := by
        change (K : ℝ) * (‖z₀‖ + 1) +
            ((K : ℝ) * ‖z₀‖ + (b : ℝ)) =
          (K : ℝ) * (2 * ‖z₀‖ + 1) + (b : ℝ)
        ring
  have hmul : L * εn ≤ a := by
    apply NNReal.coe_le_coe.mp
    change ((K : ℝ) * (2 * ‖z₀‖ + 1) + (b : ℝ)) *
        (2 * (K : ℝ) + (K : ℝ) + (b : ℝ) + 1)⁻¹ ≤
      ‖z₀‖ + 1
    have hdenR : 0 <
        2 * (K : ℝ) + (K : ℝ) + (b : ℝ) + 1 := by
      exact_mod_cast hden
    rw [inv_eq_one_div]
    field_simp
    have hextra : 0 ≤
        (K : ℝ) * ‖z₀‖ + 2 * (K : ℝ) +
          (b : ℝ) * ‖z₀‖ + ‖z₀‖ + 1 := by
      exact add_nonneg
        (add_nonneg
          (add_nonneg
            (add_nonneg (mul_nonneg K.coe_nonneg (norm_nonneg z₀))
              (mul_nonneg (by norm_num) K.coe_nonneg))
            (mul_nonneg b.coe_nonneg (norm_nonneg z₀)))
          (norm_nonneg z₀)) zero_le_one
    calc
      (K : ℝ) * (2 * ‖z₀‖ + 1) + (b : ℝ) ≤
          (K : ℝ) * (2 * ‖z₀‖ + 1) + (b : ℝ) +
            ((K : ℝ) * ‖z₀‖ + 2 * (K : ℝ) +
              (b : ℝ) * ‖z₀‖ + ‖z₀‖ + 1) :=
        le_add_of_nonneg_right hextra
      _ = (2 * (K : ℝ) + (K : ℝ) + (b : ℝ) + 1) *
          (‖z₀‖ + 1) := by ring
      _ = ((K : ℝ) * (2 + 1) + (b : ℝ) + 1) *
          (‖z₀‖ + 1) := by ring
  let t₀ : Set.Icc (-(εn : ℝ)) (εn : ℝ) :=
    ⟨0, by
      constructor
      · exact neg_nonpos.mpr (by exact_mod_cast hεn.le)
      · exact_mod_cast hεn.le⟩
  have hpicard : IsPicardLindelof
      (fun _ => hamiltonianVectorField gradient) t₀ z₀ a 0 L K := by
    apply IsPicardLindelof.of_time_independent hnorm
      hreg.lipschitzWith_hamiltonianVectorField.lipschitzOnWith
    change (L : ℝ) *
        max ((εn : ℝ) - 0) (0 - (-(εn : ℝ))) ≤
      (a : ℝ) - (0 : ℝ)
    simpa only [sub_zero, zero_sub, neg_neg, max_self] using
      (show (L : ℝ) * (εn : ℝ) ≤ (a : ℝ) by exact_mod_cast hmul)
  obtain ⟨z, hz0, hz⟩ :=
    hpicard.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨z, hz0, ?_⟩
  intro t ht
  exact (hz t (Set.Ioo_subset_Icc_self ht)).mono Set.Ioo_subset_Icc_self

/-- Every initial phase point has a global exact Hamiltonian integral curve
when the potential has a globally Lipschitz certified gradient. -/
theorem RegularPotential.exists_hamiltonianIntegralCurve
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (z₀ : PhaseSpace ι) :
    ∃ z : ℝ → PhaseSpace ι, z 0 = z₀ ∧
      IsIntegralCurve z (fun _ => hamiltonianVectorField gradient) := by
  obtain ⟨ε, hε, hlocal⟩ :=
    hreg.exists_uniform_local_hamiltonianIntegralCurve
  exact exists_globalIntegralCurve_of_uniform_local
    hreg.lipschitzWith_hamiltonianVectorField hε hlocal z₀

/-- Every initial position and momentum determine at least one global exact
Hamiltonian curve.  Global Lipschitzness also gives uniqueness, although the
downstream contraction theory only needs this existence interface. -/
theorem RegularPotential.exists_hamiltonianCurve
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (q₀ : Position ι) (p₀ : Momentum ι) :
    ∃ q : ℝ → Position ι, ∃ p : ℝ → Momentum ι,
      q 0 = q₀ ∧ p 0 = p₀ ∧ IsHamiltonianCurve gradient q p := by
  obtain ⟨z, hz0, hz⟩ := hreg.exists_hamiltonianIntegralCurve (q₀, p₀)
  refine ⟨fun t => (z t).1, fun t => (z t).2, ?_, ?_,
    IsIntegralCurve.isHamiltonianCurve hz⟩
  · exact congrArg Prod.fst hz0
  · exact congrArg Prod.snd hz0

/-- Reverse a Hamiltonian curve in time, reversing momentum as required by
the Hamilton equations. -/
def timeReversePosition (q : ℝ → Position ι) : ℝ → Position ι :=
  fun t ↦ q (-t)

def timeReverseMomentum (p : ℝ → Momentum ι) : ℝ → Momentum ι :=
  fun t ↦ -p (-t)

/-- Translate an exact position curve by a reference time. -/
def timeShiftPosition (q : ℝ → Position ι) (τ : ℝ) : ℝ → Position ι :=
  fun t ↦ q (t + τ)

/-- Translate an exact momentum curve by a reference time. -/
def timeShiftMomentum (p : ℝ → Momentum ι) (τ : ℝ) : ℝ → Momentum ι :=
  fun t ↦ p (t + τ)

omit [Fintype ι] in
/-- Hamiltonian curves remain Hamiltonian after translating the time origin.
This is the exact-curve interface used at each numerical grid point. -/
theorem IsHamiltonianCurve.timeShift
    {gradient : Position ι → Position ι}
    {q : ℝ → Position ι} {p : ℝ → Momentum ι}
    (h : IsHamiltonianCurve gradient q p) (τ : ℝ) :
    IsHamiltonianCurve gradient (timeShiftPosition q τ)
      (timeShiftMomentum p τ) where
  position_deriv t i := by
    exact (h.position_deriv (t + τ) i).comp_add_const t τ
  momentum_deriv t i := by
    exact (h.momentum_deriv (t + τ) i).comp_add_const t τ

omit [Fintype ι] in
/-- Hamiltonian dynamics are invariant under simultaneous time and momentum
reversal. This supplies the negative-time half of exact-flow contraction from
the corresponding positive-time argument. -/
theorem IsHamiltonianCurve.timeReverse
    {gradient : Position ι → Position ι}
    {q : ℝ → Position ι} {p : ℝ → Momentum ι}
    (h : IsHamiltonianCurve gradient q p) :
    IsHamiltonianCurve gradient (timeReversePosition q)
      (timeReverseMomentum p) where
  position_deriv t i := by
    have hcomp := (h.position_deriv (-t) i).comp t (hasDerivAt_neg t)
    apply hcomp.congr_deriv
    simp [timeReverseMomentum]
  momentum_deriv t i := by
    have hcomp := (h.momentum_deriv (-t) i).comp t (hasDerivAt_neg t)
    have hneg := hcomp.neg
    apply hneg.congr_deriv
    simp [timeReversePosition]

/-- Product rule for the explicit finite-dimensional Euclidean pairing. -/
theorem hasDerivAt_euclideanInner
    {x y : ℝ → Position ι} {x' y' : Position ι} {t : ℝ}
    (hx : ∀ i, HasDerivAt (fun s => x s i) (x' i) t)
    (hy : ∀ i, HasDerivAt (fun s => y s i) (y' i) t) :
    HasDerivAt (fun s => euclideanInner (x s) (y s))
      (euclideanInner x' (y t) + euclideanInner (x t) y') t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i hi => (hx i).mul (hy i))
  convert h using 1 <;> try rfl
  simp only [euclideanInner, Finset.sum_add_distrib]

/-- The Hamiltonian has zero derivative along every classical Hamiltonian
curve whose force is the certified gradient of the potential. -/
theorem IsHamiltonianCurve.hasDerivAt_energy_zero
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q : ℝ → Position ι} {p : ℝ → Momentum ι}
    (hcurve : IsHamiltonianCurve gradient q p) (t : ℝ) :
    HasDerivAt (fun s => energy potential (q s, p s)) 0 t := by
  have hq : HasDerivAt q (p t) t :=
    hasDerivAt_pi.mpr (hcurve.position_deriv t)
  have hpotential : HasDerivAt (fun s => potential (q s))
      (euclideanInner (gradient (q t)) (p t)) t := by
    have hcomp :=
      (hreg.contDiff_two.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
        (q t)).hasFDerivAt.comp_hasDerivAt t hq
    rw [hreg.fderiv_apply] at hcomp
    exact hcomp
  have hkinetic : HasDerivAt (fun s => kineticEnergy (p s))
      (-euclideanInner (gradient (q t)) (p t)) t := by
    have hsum := HasDerivAt.fun_sum (u := Finset.univ)
      (fun i hi => (hcurve.momentum_deriv t i).pow 2)
    have hhalf := hsum.const_mul (1 / 2 : ℝ)
    unfold kineticEnergy
    apply hhalf.congr_deriv
    simp only [euclideanInner, Finset.mul_sum]
    simp [mul_comm]
    ring_nf
  change HasDerivAt
    ((fun s => potential (q s)) + fun s => kineticEnergy (p s)) 0 t
  exact (hpotential.add hkinetic).congr_deriv (add_neg_cancel _)

/-- Exact Hamiltonian dynamics conserve the Hamiltonian at all times. -/
theorem IsHamiltonianCurve.energy_eq
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q : ℝ → Position ι} {p : ℝ → Momentum ι}
    (hcurve : IsHamiltonianCurve gradient q p) (s t : ℝ) :
    energy potential (q s, p s) = energy potential (q t, p t) := by
  let H : ℝ → ℝ := fun u => energy potential (q u, p u)
  have hdiff : Differentiable ℝ H := fun u =>
    (hcurve.hasDerivAt_energy_zero hreg u).differentiableAt
  have hderiv : ∀ u, fderiv ℝ H u = fderiv ℝ (fun _ : ℝ => H t) u := by
    intro u
    rw [(hcurve.hasDerivAt_energy_zero hreg u).hasFDerivAt.fderiv]
    simp
  have hconst : H = fun _ : ℝ => H t :=
    eq_of_fderiv_eq hdiff (differentiable_const (c := H t)) hderiv t rfl
  exact congrFun hconst s

/-- Energy discrepancies between two numerical states are controlled by their
errors relative to exact Hamiltonian curves and the exact curves' initial
energy gap.  Energy conservation makes this bound independent of the
comparison time. -/
theorem abs_energy_sub_le_of_exact_curve_errors
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (hcurve₁ : IsHamiltonianCurve gradient q₁ p₁)
    (hcurve₂ : IsHamiltonianCurve gradient q₂ p₂)
    (z₁ z₂ : PhaseSpace ι) (s t δ₁ δ₂ : ℝ)
    (herror₁ : |energy potential z₁ - energy potential (q₁ s, p₁ s)| ≤ δ₁)
    (herror₂ : |energy potential (q₂ s, p₂ s) - energy potential z₂| ≤ δ₂) :
    |energy potential z₁ - energy potential z₂| ≤
      δ₁ + |energy potential (q₁ t, p₁ t) -
        energy potential (q₂ t, p₂ t)| + δ₂ := by
  rw [← hcurve₁.energy_eq hreg s t, ← hcurve₂.energy_eq hreg s t]
  rw [show energy potential z₁ - energy potential z₂ =
      (energy potential z₁ - energy potential (q₁ s, p₁ s)) +
      (energy potential (q₁ s, p₁ s) - energy potential (q₂ s, p₂ s)) +
      (energy potential (q₂ s, p₂ s) - energy potential z₂) by ring]
  exact (abs_add_le _ _).trans
    (add_le_add (abs_add_le _ _) herror₂) |>.trans
      (add_le_add (add_le_add herror₁ le_rfl) le_rfl)

/-- First derivative of squared Euclidean separation of two position curves. -/
theorem hasDerivAt_squaredEuclideanSeparation
    {q₁ q₂ p₁ p₂ : ℝ → Position ι} {t : ℝ}
    (hq₁ : ∀ i, HasDerivAt (fun s => q₁ s i) (p₁ t i) t)
    (hq₂ : ∀ i, HasDerivAt (fun s => q₂ s i) (p₂ t i) t) :
    HasDerivAt
      (fun s => squaredEuclideanNorm (q₁ s - q₂ s))
      (2 * euclideanInner (q₁ t - q₂ t) (p₁ t - p₂ t)) t := by
  have hsub : ∀ i, HasDerivAt (fun s => (q₁ s - q₂ s) i)
      ((p₁ t - p₂ t) i) t := by
    intro i
    have h := (hq₁ i).sub (hq₂ i)
    convert h using 1 <;> try rfl
  have h := hasDerivAt_euclideanInner hsub hsub
  convert h using 1
  · rfl
  · simp only [euclideanInner, two_mul]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring

/-- Derivative of the displacement/relative-momentum Euclidean pairing along
two Hamiltonian curves. -/
theorem hasDerivAt_separationMomentumPairing
    {gradient : Position ι → Position ι}
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι} {t : ℝ}
    (h₁ : IsHamiltonianCurve gradient q₁ p₁)
    (h₂ : IsHamiltonianCurve gradient q₂ p₂) :
    HasDerivAt
      (fun s => euclideanInner (q₁ s - q₂ s) (p₁ s - p₂ s))
      (euclideanInner (p₁ t - p₂ t) (p₁ t - p₂ t) -
        euclideanInner (q₁ t - q₂ t)
          (gradient (q₁ t) - gradient (q₂ t))) t := by
  have hq : ∀ i, HasDerivAt (fun s => (q₁ s - q₂ s) i)
      ((p₁ t - p₂ t) i) t := by
    intro i
    have h := (h₁.position_deriv t i).sub (h₂.position_deriv t i)
    convert h using 1 <;> try rfl
  have hp : ∀ i, HasDerivAt (fun s => (p₁ s - p₂ s) i)
      ((-(gradient (q₁ t) - gradient (q₂ t))) i) t := by
    intro i
    have h := (h₁.momentum_deriv t i).sub (h₂.momentum_deriv t i)
    convert h using 1 <;> try rfl
    simp only [Pi.sub_apply, Pi.neg_apply]
    ring
  convert hasDerivAt_euclideanInner hq hp using 1
  rw [euclideanInner_neg_right]
  ring

/-- With shared momentum, squared position separation has zero first
derivative at the shared initial time. -/
theorem hasDerivAt_squaredEuclideanSeparation_sharedMomentum
    {gradient : Position ι → Position ι}
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι} {t : ℝ}
    (h₁ : IsHamiltonianCurve gradient q₁ p₁)
    (h₂ : IsHamiltonianCurve gradient q₂ p₂)
    (hp : p₁ t = p₂ t) :
    HasDerivAt (fun s => squaredEuclideanNorm (q₁ s - q₂ s)) 0 t := by
  convert hasDerivAt_squaredEuclideanSeparation
    (h₁.position_deriv t) (h₂.position_deriv t) using 1
  simp [hp, euclideanInner]

/-- At a shared-momentum time, the derivative of the first-variation formula
is minus twice the gradient/displacement pairing. -/
theorem hasDerivAt_firstVariation_sharedMomentum
    {gradient : Position ι → Position ι}
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι} {t : ℝ}
    (h₁ : IsHamiltonianCurve gradient q₁ p₁)
    (h₂ : IsHamiltonianCurve gradient q₂ p₂)
    (hp : p₁ t = p₂ t) :
    HasDerivAt
      (fun s => 2 * euclideanInner (q₁ s - q₂ s) (p₁ s - p₂ s))
      (-2 * euclideanInner (q₁ t - q₂ t)
        (gradient (q₁ t) - gradient (q₂ t))) t := by
  have h := (hasDerivAt_separationMomentumPairing (t := t) h₁ h₂).const_mul 2
  convert h using 1 <;> try rfl
  simp [hp]

/-- The first variation of squared position separation has derivative twice
the relative kinetic term minus twice the gradient/displacement pairing. -/
theorem hasDerivAt_firstVariation
    {gradient : Position ι → Position ι}
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι} {t : ℝ}
    (h₁ : IsHamiltonianCurve gradient q₁ p₁)
    (h₂ : IsHamiltonianCurve gradient q₂ p₂) :
    HasDerivAt
      (fun s => 2 * euclideanInner (q₁ s - q₂ s) (p₁ s - p₂ s))
      (2 * (squaredEuclideanNorm (p₁ t - p₂ t) -
        euclideanInner (q₁ t - q₂ t)
          (gradient (q₁ t) - gradient (q₂ t)))) t := by
  have h := (hasDerivAt_separationMomentumPairing (t := t) h₁ h₂).const_mul 2
  simpa [squaredEuclideanNorm] using h

/-- Quantitative exact-flow contraction from a uniform second-variation
margin.  The margin says that throughout the time interval the strong-force
pairing dominates relative kinetic energy by at least `c`.  Shared initial
momentum then gives the quadratic loss `c t²` in squared separation. -/
theorem squaredEuclideanSeparation_le_sub_sq_of_secondVariationMargin
    {gradient : Position ι → Position ι}
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (h₁ : IsHamiltonianCurve gradient q₁ p₁)
    (h₂ : IsHamiltonianCurve gradient q₂ p₂)
    {c t : ℝ} (ht : 0 ≤ t) (hp : p₁ 0 = p₂ 0)
    (hmargin : ∀ s ∈ Icc (0 : ℝ) t,
      c ≤ euclideanInner (q₁ s - q₂ s)
          (gradient (q₁ s) - gradient (q₂ s)) -
        squaredEuclideanNorm (p₁ s - p₂ s)) :
    squaredEuclideanNorm (q₁ t - q₂ t) ≤
      squaredEuclideanNorm (q₁ 0 - q₂ 0) - c * t ^ 2 := by
  let f : ℝ → ℝ := fun s => squaredEuclideanNorm (q₁ s - q₂ s)
  let g : ℝ → ℝ := fun s =>
    2 * euclideanInner (q₁ s - q₂ s) (p₁ s - p₂ s)
  let G : ℝ → ℝ := fun s => g s + 2 * c * s
  let F : ℝ → ℝ := fun s => f s + c * s ^ 2
  have hf : ∀ s, HasDerivAt f (g s) s := by
    intro s
    exact hasDerivAt_squaredEuclideanSeparation
      (h₁.position_deriv s) (h₂.position_deriv s)
  have hg : ∀ s, HasDerivAt g
      (2 * (squaredEuclideanNorm (p₁ s - p₂ s) -
        euclideanInner (q₁ s - q₂ s)
          (gradient (q₁ s) - gradient (q₂ s)))) s := by
    intro s
    exact hasDerivAt_firstVariation h₁ h₂
  have hG : ∀ s, HasDerivAt G
      (2 * (squaredEuclideanNorm (p₁ s - p₂ s) -
        euclideanInner (q₁ s - q₂ s)
          (gradient (q₁ s) - gradient (q₂ s))) + 2 * c) s := by
    intro s
    dsimp [G]
    have hlinear : HasDerivAt (fun y : ℝ => 2 * c * y) (2 * c) s :=
      hasDerivAt_const_mul (2 * c)
    have hsum := (hg s).add hlinear
    have heq : g + (fun y : ℝ => 2 * c * y) =
        fun y => g y + 2 * c * y := by
      funext y
      rfl
    rw [heq] at hsum
    exact hsum
  have hGanti : AntitoneOn G (Icc (0 : ℝ) t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) t)
    · exact (continuous_iff_continuousAt.mpr
        fun s => (hG s).continuousAt).continuousOn
    · intro s hs
      exact (hG s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [(hG s).deriv]
      have hm := hmargin s (interior_subset hs)
      linarith
  have hgBound : ∀ s ∈ Icc (0 : ℝ) t, g s ≤ -2 * c * s := by
    intro s hs
    have hle := hGanti (left_mem_Icc.mpr ht) hs hs.1
    have hGzero : G 0 = 0 := by simp [G, g, hp]
    rw [hGzero] at hle
    dsimp [G] at hle
    linarith
  have hF : ∀ s, HasDerivAt F (g s + 2 * c * s) s := by
    intro s
    dsimp [F]
    have hquad : HasDerivAt (fun y : ℝ => c * y ^ 2) (2 * c * s) s := by
      exact (((hasDerivAt_id s).pow 2).const_mul c).congr_deriv (by
        simp [id]
        ring)
    have hsum := (hf s).add hquad
    have heq : f + (fun y : ℝ => c * y ^ 2) =
        fun y => f y + c * y ^ 2 := by
      funext y
      rfl
    rw [heq] at hsum
    exact hsum
  have hFanti : AntitoneOn F (Icc (0 : ℝ) t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) t)
    · exact (continuous_iff_continuousAt.mpr
        fun s => (hF s).continuousAt).continuousOn
    · intro s hs
      exact (hF s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [(hF s).deriv]
      linarith [hgBound s (interior_subset hs)]
  have hfinal := hFanti (left_mem_Icc.mpr ht) (right_mem_Icc.mpr ht) ht
  dsimp [F, f] at hfinal ⊢
  nlinarith

/-- Negative-time form of the quantitative exact-flow contraction theorem,
obtained by applying the positive-time theorem to the time-reversed
Hamiltonian curves. -/
theorem squaredEuclideanSeparation_le_sub_sq_of_secondVariationMargin_neg
    {gradient : Position ι → Position ι}
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (h₁ : IsHamiltonianCurve gradient q₁ p₁)
    (h₂ : IsHamiltonianCurve gradient q₂ p₂)
    {c t : ℝ} (ht : t ≤ 0) (hp : p₁ 0 = p₂ 0)
    (hmargin : ∀ s ∈ Icc t (0 : ℝ),
      c ≤ euclideanInner (q₁ s - q₂ s)
          (gradient (q₁ s) - gradient (q₂ s)) -
        squaredEuclideanNorm (p₁ s - p₂ s)) :
    squaredEuclideanNorm (q₁ t - q₂ t) ≤
      squaredEuclideanNorm (q₁ 0 - q₂ 0) - c * t ^ 2 := by
  let qr₁ := timeReversePosition q₁
  let qr₂ := timeReversePosition q₂
  let pr₁ := timeReverseMomentum p₁
  let pr₂ := timeReverseMomentum p₂
  have hrev₁ : IsHamiltonianCurve gradient qr₁ pr₁ := h₁.timeReverse
  have hrev₂ : IsHamiltonianCurve gradient qr₂ pr₂ := h₂.timeReverse
  have hpRev : pr₁ 0 = pr₂ 0 := by
    dsimp [pr₁, pr₂, timeReverseMomentum]
    simpa only [neg_zero] using congrArg Neg.neg hp
  have hmarginRev : ∀ s ∈ Icc (0 : ℝ) (-t),
      c ≤ euclideanInner (qr₁ s - qr₂ s)
          (gradient (qr₁ s) - gradient (qr₂ s)) -
        squaredEuclideanNorm (pr₁ s - pr₂ s) := by
    intro s hs
    have hnegMem : -s ∈ Icc t (0 : ℝ) := by
      constructor <;> linarith [hs.1, hs.2]
    have hm := hmargin (-s) hnegMem
    dsimp [qr₁, qr₂, pr₁, pr₂, timeReversePosition,
      timeReverseMomentum]
    rw [show -p₁ (-s) - -p₂ (-s) = -(p₁ (-s) - p₂ (-s)) by abel,
      squaredEuclideanNorm_neg]
    simpa only [neg_neg] using hm
  have h := squaredEuclideanSeparation_le_sub_sq_of_secondVariationMargin
    hrev₁ hrev₂ (neg_nonneg.mpr ht) hpRev hmarginRev
  dsimp [qr₁, qr₂, timeReversePosition] at h
  simpa only [neg_neg, neg_zero, neg_sq] using h

/-- Two-sided exact-flow contraction on the unordered interval between zero
and the requested integration time. This matches the positive/negative-time
surface of Xu et al.'s Lemma 4.2. -/
theorem squaredEuclideanSeparation_le_sub_sq_of_secondVariationMargin_twoSided
    {gradient : Position ι → Position ι}
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (h₁ : IsHamiltonianCurve gradient q₁ p₁)
    (h₂ : IsHamiltonianCurve gradient q₂ p₂)
    {c t : ℝ} (hp : p₁ 0 = p₂ 0)
    (hmargin : ∀ s ∈ uIcc (0 : ℝ) t,
      c ≤ euclideanInner (q₁ s - q₂ s)
          (gradient (q₁ s) - gradient (q₂ s)) -
        squaredEuclideanNorm (p₁ s - p₂ s)) :
    squaredEuclideanNorm (q₁ t - q₂ t) ≤
      squaredEuclideanNorm (q₁ 0 - q₂ 0) - c * t ^ 2 := by
  rcases le_total 0 t with ht | ht
  · apply squaredEuclideanSeparation_le_sub_sq_of_secondVariationMargin
      h₁ h₂ ht hp
    intro s hs
    exact hmargin s (by simpa [uIcc_of_le ht] using hs)
  · apply squaredEuclideanSeparation_le_sub_sq_of_secondVariationMargin_neg
      h₁ h₂ ht hp
    intro s hs
    exact hmargin s (by simpa [uIcc_of_ge ht] using hs)

/-- A uniform bound on exact-flow position separation gives a linear-in-time
bound on relative momentum. With shared initial momentum, global Lipschitzness
of the gradient makes the relative force uniformly bounded; the mean-value
inequality then integrates that force over the unordered time interval.

The dimension factor only converts mathlib's ambient finite-product norm back
to the explicit Euclidean norm used by the Hamiltonian estimates. -/
theorem RegularPotential.euclideanNorm_momentum_sub_le_of_position_sub_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (h₁ : IsHamiltonianCurve gradient q₁ p₁)
    (h₂ : IsHamiltonianCurve gradient q₂ p₂)
    {R t : ℝ} (hp : p₁ 0 = p₂ 0)
    (hposition : ∀ s ∈ uIcc (0 : ℝ) t,
      euclideanNorm (q₁ s - q₂ s) ≤ R) :
    euclideanNorm (p₁ t - p₂ t) ≤
      ((Fintype.card ι : ℝ) + 1) * (β : ℝ) * R * |t| := by
  let r : ℝ → Momentum ι := fun s ↦ p₁ s - p₂ s
  have hr : ∀ s, HasDerivAt r
      (-(gradient (q₁ s) - gradient (q₂ s))) s := by
    intro s
    rw [hasDerivAt_pi]
    intro i
    have h := (h₁.momentum_deriv s i).sub (h₂.momentum_deriv s i)
    convert h using 1
    · funext x
      rfl
    · simp only [Pi.neg_apply, Pi.sub_apply]
      ring
  have hforce : ∀ s ∈ uIcc (0 : ℝ) t,
      ‖-(gradient (q₁ s) - gradient (q₂ s))‖ ≤ (β : ℝ) * R := by
    intro s hs
    have hambient : ‖-(gradient (q₁ s) - gradient (q₂ s))‖ ≤
        euclideanNorm (-(gradient (q₁ s) - gradient (q₂ s))) := by
      have hdist := dist_le_euclideanNorm_sub
        (-(gradient (q₁ s) - gradient (q₂ s))) 0
      simpa only [dist_zero_right, sub_zero] using hdist
    calc
      ‖-(gradient (q₁ s) - gradient (q₂ s))‖ ≤
          euclideanNorm (-(gradient (q₁ s) - gradient (q₂ s))) := hambient
      _ = euclideanNorm (gradient (q₁ s) - gradient (q₂ s)) :=
        euclideanNorm_neg _
      _ ≤ (β : ℝ) * euclideanNorm (q₁ s - q₂ s) :=
        hreg.euclideanNorm_gradient_sub_le _ _
      _ ≤ (β : ℝ) * R :=
        mul_le_mul_of_nonneg_left (hposition s hs) β.coe_nonneg
  have hmean : ‖r t - r 0‖ ≤ (β : ℝ) * R * ‖t - 0‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (fun s hs ↦ (hr s).differentiableAt)
      (fun s hs ↦ by rw [(hr s).deriv]; exact hforce s hs)
      (convex_uIcc (0 : ℝ) t) left_mem_uIcc right_mem_uIcc
  have hrzero : r 0 = 0 := by simp [r, hp]
  have hambient : ‖p₁ t - p₂ t‖ ≤ (β : ℝ) * R * |t| := by
    simpa only [r, hrzero, sub_zero, Real.norm_eq_abs, sub_zero] using hmean
  calc
    euclideanNorm (p₁ t - p₂ t) ≤
        ((Fintype.card ι : ℝ) + 1) * dist (p₁ t - p₂ t) 0 :=
      by simpa only [sub_zero] using
        euclideanNorm_sub_le_card_succ_mul_dist (p₁ t - p₂ t) 0
    _ = ((Fintype.card ι : ℝ) + 1) * ‖p₁ t - p₂ t‖ := by
      rw [dist_zero_right]
    _ ≤ ((Fintype.card ι : ℝ) + 1) * ((β : ℝ) * R * |t|) := by
      gcongr
    _ = ((Fintype.card ι : ℝ) + 1) * (β : ℝ) * R * |t| := by ring

/-- Arbitrary-initial-momentum version of relative momentum integration.
The change in relative momentum, rather than relative momentum itself, is
linear in time under a uniform position-separation bound. -/
theorem RegularPotential.euclideanNorm_momentumSub_sub_initial_le_of_position_sub_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (h₁ : IsHamiltonianCurve gradient q₁ p₁)
    (h₂ : IsHamiltonianCurve gradient q₂ p₂)
    {R t : ℝ}
    (hposition : ∀ s ∈ uIcc (0 : ℝ) t,
      euclideanNorm (q₁ s - q₂ s) ≤ R) :
    euclideanNorm
        ((p₁ t - p₂ t) - (p₁ 0 - p₂ 0)) ≤
      ((Fintype.card ι : ℝ) + 1) * (β : ℝ) * R * |t| := by
  let r : ℝ → Momentum ι := fun s ↦ p₁ s - p₂ s
  have hr : ∀ s, HasDerivAt r
      (-(gradient (q₁ s) - gradient (q₂ s))) s := by
    intro s
    rw [hasDerivAt_pi]
    intro i
    have h := (h₁.momentum_deriv s i).sub (h₂.momentum_deriv s i)
    convert h using 1
    · funext x
      rfl
    · simp only [Pi.neg_apply, Pi.sub_apply]
      ring
  have hforce : ∀ s ∈ uIcc (0 : ℝ) t,
      ‖-(gradient (q₁ s) - gradient (q₂ s))‖ ≤ (β : ℝ) * R := by
    intro s hs
    have hambient : ‖-(gradient (q₁ s) - gradient (q₂ s))‖ ≤
        euclideanNorm (-(gradient (q₁ s) - gradient (q₂ s))) := by
      have hdist := dist_le_euclideanNorm_sub
        (-(gradient (q₁ s) - gradient (q₂ s))) 0
      simpa only [dist_zero_right, sub_zero] using hdist
    calc
      ‖-(gradient (q₁ s) - gradient (q₂ s))‖ ≤
          euclideanNorm (-(gradient (q₁ s) - gradient (q₂ s))) := hambient
      _ = euclideanNorm (gradient (q₁ s) - gradient (q₂ s)) :=
        euclideanNorm_neg _
      _ ≤ (β : ℝ) * euclideanNorm (q₁ s - q₂ s) :=
        hreg.euclideanNorm_gradient_sub_le _ _
      _ ≤ (β : ℝ) * R :=
        mul_le_mul_of_nonneg_left (hposition s hs) β.coe_nonneg
  have hmean : ‖r t - r 0‖ ≤ (β : ℝ) * R * ‖t - 0‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (fun s hs ↦ (hr s).differentiableAt)
      (fun s hs ↦ by rw [(hr s).deriv]; exact hforce s hs)
      (convex_uIcc (0 : ℝ) t) left_mem_uIcc right_mem_uIcc
  have hambient : ‖(p₁ t - p₂ t) - (p₁ 0 - p₂ 0)‖ ≤
      (β : ℝ) * R * |t| := by
    simpa only [r, Real.norm_eq_abs, sub_zero] using hmean
  calc
    euclideanNorm ((p₁ t - p₂ t) - (p₁ 0 - p₂ 0)) ≤
        ((Fintype.card ι : ℝ) + 1) *
          dist ((p₁ t - p₂ t) - (p₁ 0 - p₂ 0)) 0 := by
      simpa only [sub_zero] using euclideanNorm_sub_le_card_succ_mul_dist
        ((p₁ t - p₂ t) - (p₁ 0 - p₂ 0)) 0
    _ = ((Fintype.card ι : ℝ) + 1) *
        ‖(p₁ t - p₂ t) - (p₁ 0 - p₂ 0)‖ := by rw [dist_zero_right]
    _ ≤ ((Fintype.card ι : ℝ) + 1) * ((β : ℝ) * R * |t|) := by
      gcongr
    _ = ((Fintype.card ι : ℝ) + 1) * (β : ℝ) * R * |t| := by ring

/-- Integrating a uniformly bounded force controls the absolute momentum
change of one exact Hamiltonian trajectory. -/
theorem euclideanNorm_momentum_sub_initial_le_of_gradient_le
    {gradient : Position ι → Position ι}
    {q : ℝ → Position ι} {p : ℝ → Momentum ι}
    (hcurve : IsHamiltonianCurve gradient q p)
    {G t : ℝ}
    (hgradient : ∀ s ∈ uIcc (0 : ℝ) t,
      euclideanNorm (gradient (q s)) ≤ G) :
    euclideanNorm (p t - p 0) ≤
      ((Fintype.card ι : ℝ) + 1) * G * |t| := by
  have hpderiv : ∀ s, HasDerivAt p (-gradient (q s)) s := by
    intro s
    exact hasDerivAt_pi.mpr (hcurve.momentum_deriv s)
  have hforce : ∀ s ∈ uIcc (0 : ℝ) t, ‖-gradient (q s)‖ ≤ G := by
    intro s hs
    have hambient : ‖-gradient (q s)‖ ≤
        euclideanNorm (-gradient (q s)) := by
      have hdist := dist_le_euclideanNorm_sub (-gradient (q s)) 0
      simpa only [dist_zero_right, sub_zero] using hdist
    rw [euclideanNorm_neg] at hambient
    exact hambient.trans (hgradient s hs)
  have hmean : ‖p t - p 0‖ ≤ G * ‖t - 0‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (fun s hs ↦ (hpderiv s).differentiableAt)
      (fun s hs ↦ by rw [(hpderiv s).deriv]; exact hforce s hs)
      (convex_uIcc (0 : ℝ) t) left_mem_uIcc right_mem_uIcc
  calc
    euclideanNorm (p t - p 0) ≤
        ((Fintype.card ι : ℝ) + 1) * dist (p t - p 0) 0 := by
      simpa only [sub_zero] using
        euclideanNorm_sub_le_card_succ_mul_dist (p t - p 0) 0
    _ = ((Fintype.card ι : ℝ) + 1) * ‖p t - p 0‖ := by
      rw [dist_zero_right]
    _ ≤ ((Fintype.card ι : ℝ) + 1) * (G * |t|) := by
      gcongr
      simpa only [Real.norm_eq_abs, sub_zero] using hmean
    _ = ((Fintype.card ι : ℝ) + 1) * G * |t| := by ring

/-- Paired force variation controls the error of the left-endpoint force
quadrature for relative exact momentum. This retains the cancellation of the
leading term `-t(∇U(q₁(0))-∇U(q₂(0)))`. -/
theorem euclideanNorm_momentumSub_add_initialForce_le
    {gradient : Position ι → Position ι}
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (h₁ : IsHamiltonianCurve gradient q₁ p₁)
    (h₂ : IsHamiltonianCurve gradient q₂ p₂)
    {ω t : ℝ} (hp : p₁ 0 = p₂ 0)
    (hforce : ∀ s ∈ uIcc (0 : ℝ) t,
      euclideanNorm
          ((gradient (q₁ s) - gradient (q₂ s)) -
            (gradient (q₁ 0) - gradient (q₂ 0))) ≤
        ω * euclideanNorm (q₁ 0 - q₂ 0)) :
    euclideanNorm
        ((p₁ t - p₂ t) +
          t • (gradient (q₁ 0) - gradient (q₂ 0))) ≤
      ((Fintype.card ι : ℝ) + 1) * |t| * ω *
        euclideanNorm (q₁ 0 - q₂ 0) := by
  let dg0 : Position ι := gradient (q₁ 0) - gradient (q₂ 0)
  let r : ℝ → Momentum ι := fun s ↦ (p₁ s - p₂ s) + s • dg0
  have hr : ∀ s, HasDerivAt r
      (-((gradient (q₁ s) - gradient (q₂ s)) - dg0)) s := by
    intro s
    rw [hasDerivAt_pi]
    intro i
    have hpder := (h₁.momentum_deriv s i).sub (h₂.momentum_deriv s i)
    have hlinear : HasDerivAt (fun x : ℝ ↦ x * dg0 i) (dg0 i) s :=
      by simpa only [id_eq, one_mul] using
        (hasDerivAt_id s).mul_const (dg0 i)
    have hsum := hpder.add hlinear
    convert hsum using 1
    · funext x
      simp only [r, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    · simp only [dg0, Pi.neg_apply, Pi.sub_apply]
      ring
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) t,
      ‖-((gradient (q₁ s) - gradient (q₂ s)) - dg0)‖ ≤
        ω * euclideanNorm (q₁ 0 - q₂ 0) := by
    intro s hs
    have hambient :
        ‖-((gradient (q₁ s) - gradient (q₂ s)) - dg0)‖ ≤
          euclideanNorm
            (-((gradient (q₁ s) - gradient (q₂ s)) - dg0)) := by
      have hdist := dist_le_euclideanNorm_sub
        (-((gradient (q₁ s) - gradient (q₂ s)) - dg0)) 0
      simpa only [dist_zero_right, sub_zero] using hdist
    rw [euclideanNorm_neg] at hambient
    exact hambient.trans (hforce s hs)
  have hmean : ‖r t - r 0‖ ≤
      (ω * euclideanNorm (q₁ 0 - q₂ 0)) * ‖t - 0‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (fun s hs ↦ (hr s).differentiableAt)
      (fun s hs ↦ by rw [(hr s).deriv]; exact hderiv s hs)
      (convex_uIcc (0 : ℝ) t) left_mem_uIcc right_mem_uIcc
  have hrzero : r 0 = 0 := by simp [r, hp]
  have hmean' : ‖r t - r 0‖ ≤
      (ω * euclideanNorm (q₁ 0 - q₂ 0)) * |t| := by
    simpa only [sub_zero, Real.norm_eq_abs] using hmean
  have hambient : ‖(p₁ t - p₂ t) + t • dg0‖ ≤
      |t| * ω * euclideanNorm (q₁ 0 - q₂ 0) := by
    rw [show |t| * ω * euclideanNorm (q₁ 0 - q₂ 0) =
      (ω * euclideanNorm (q₁ 0 - q₂ 0)) * |t| by ring]
    simpa only [r, hrzero, sub_zero] using hmean'
  calc
    euclideanNorm
        ((p₁ t - p₂ t) + t • (gradient (q₁ 0) - gradient (q₂ 0))) =
      euclideanNorm ((p₁ t - p₂ t) + t • dg0) := rfl
    _ ≤ ((Fintype.card ι : ℝ) + 1) *
        dist ((p₁ t - p₂ t) + t • dg0) 0 := by
      simpa only [sub_zero] using euclideanNorm_sub_le_card_succ_mul_dist
        ((p₁ t - p₂ t) + t • dg0) 0
    _ = ((Fintype.card ι : ℝ) + 1) *
        ‖(p₁ t - p₂ t) + t • dg0‖ := by rw [dist_zero_right]
    _ ≤ ((Fintype.card ι : ℝ) + 1) *
        (|t| * ω * euclideanNorm (q₁ 0 - q₂ 0)) := by gcongr
    _ = ((Fintype.card ι : ℝ) + 1) * |t| * ω *
        euclideanNorm (q₁ 0 - q₂ 0) := by ring

/-- Arbitrary-initial-momentum force-quadrature estimate. Subtracting the
initial relative momentum makes the same paired-force cancellation available
without a shared-momentum hypothesis. -/
theorem euclideanNorm_momentumSub_sub_initial_add_initialForce_le
    {gradient : Position ι → Position ι}
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (h₁ : IsHamiltonianCurve gradient q₁ p₁)
    (h₂ : IsHamiltonianCurve gradient q₂ p₂)
    {ω t : ℝ}
    (hforce : ∀ s ∈ uIcc (0 : ℝ) t,
      euclideanNorm
          ((gradient (q₁ s) - gradient (q₂ s)) -
            (gradient (q₁ 0) - gradient (q₂ 0))) ≤
        ω * euclideanPhaseSize
          (q₁ 0 - q₂ 0, p₁ 0 - p₂ 0)) :
    euclideanNorm
        (((p₁ t - p₂ t) - (p₁ 0 - p₂ 0)) +
          t • (gradient (q₁ 0) - gradient (q₂ 0))) ≤
      ((Fintype.card ι : ℝ) + 1) * |t| * ω *
        euclideanPhaseSize
          (q₁ 0 - q₂ 0, p₁ 0 - p₂ 0) := by
  let dp0 : Momentum ι := p₁ 0 - p₂ 0
  let dg0 : Position ι := gradient (q₁ 0) - gradient (q₂ 0)
  let Z : ℝ := euclideanPhaseSize
    (q₁ 0 - q₂ 0, p₁ 0 - p₂ 0)
  let r : ℝ → Momentum ι := fun s ↦
    ((p₁ s - p₂ s) - dp0) + s • dg0
  have hr : ∀ s, HasDerivAt r
      (-((gradient (q₁ s) - gradient (q₂ s)) - dg0)) s := by
    intro s
    rw [hasDerivAt_pi]
    intro i
    have hpder := (h₁.momentum_deriv s i).sub (h₂.momentum_deriv s i)
    have hconst : HasDerivAt (fun _ : ℝ ↦ dp0 i) 0 s :=
      hasDerivAt_const s _
    have hlinear : HasDerivAt (fun x : ℝ ↦ x * dg0 i) (dg0 i) s := by
      simpa only [id_eq, one_mul] using
        (hasDerivAt_id s).mul_const (dg0 i)
    have hsum := (hpder.sub hconst).add hlinear
    convert hsum using 1
    · funext x
      simp only [r, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    · simp only [dg0, Pi.neg_apply, Pi.sub_apply]
      ring
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) t,
      ‖-((gradient (q₁ s) - gradient (q₂ s)) - dg0)‖ ≤ ω * Z := by
    intro s hs
    have hambient :
        ‖-((gradient (q₁ s) - gradient (q₂ s)) - dg0)‖ ≤
          euclideanNorm
            (-((gradient (q₁ s) - gradient (q₂ s)) - dg0)) := by
      have hdist := dist_le_euclideanNorm_sub
        (-((gradient (q₁ s) - gradient (q₂ s)) - dg0)) 0
      simpa only [dist_zero_right, sub_zero] using hdist
    rw [euclideanNorm_neg] at hambient
    exact hambient.trans (hforce s hs)
  have hmean : ‖r t - r 0‖ ≤ (ω * Z) * ‖t - 0‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (fun s hs ↦ (hr s).differentiableAt)
      (fun s hs ↦ by rw [(hr s).deriv]; exact hderiv s hs)
      (convex_uIcc (0 : ℝ) t) left_mem_uIcc right_mem_uIcc
  have hrzero : r 0 = 0 := by
    dsimp [r, dp0]
    rw [zero_smul]
    abel
  have hambient : ‖((p₁ t - p₂ t) - dp0) + t • dg0‖ ≤
      |t| * ω * Z := by
    rw [show |t| * ω * Z = (ω * Z) * |t| by ring]
    simpa only [r, hrzero, sub_zero, Real.norm_eq_abs] using hmean
  calc
    euclideanNorm
        (((p₁ t - p₂ t) - (p₁ 0 - p₂ 0)) +
          t • (gradient (q₁ 0) - gradient (q₂ 0))) =
      euclideanNorm (((p₁ t - p₂ t) - dp0) + t • dg0) := rfl
    _ ≤ ((Fintype.card ι : ℝ) + 1) *
        dist (((p₁ t - p₂ t) - dp0) + t • dg0) 0 := by
      simpa only [sub_zero] using euclideanNorm_sub_le_card_succ_mul_dist
        (((p₁ t - p₂ t) - dp0) + t • dg0) 0
    _ = ((Fintype.card ι : ℝ) + 1) *
        ‖((p₁ t - p₂ t) - dp0) + t • dg0‖ := by rw [dist_zero_right]
    _ ≤ ((Fintype.card ι : ℝ) + 1) * (|t| * ω * Z) := by gcongr
    _ = ((Fintype.card ι : ℝ) + 1) * |t| * ω * Z := by ring

/-- Absolute left-endpoint force-quadrature error for one exact Hamiltonian
trajectory. -/
theorem euclideanNorm_momentum_sub_initial_add_initialForce_le
    {gradient : Position ι → Position ι}
    {q : ℝ → Position ι} {p : ℝ → Momentum ι}
    (hcurve : IsHamiltonianCurve gradient q p)
    {ω t : ℝ}
    (hforce : ∀ s ∈ uIcc (0 : ℝ) t,
      euclideanNorm (gradient (q s) - gradient (q 0)) ≤ ω) :
    euclideanNorm ((p t - p 0) + t • gradient (q 0)) ≤
      ((Fintype.card ι : ℝ) + 1) * |t| * ω := by
  let g0 : Position ι := gradient (q 0)
  let r : ℝ → Momentum ι := fun s ↦ (p s - p 0) + s • g0
  have hr : ∀ s, HasDerivAt r (-(gradient (q s) - g0)) s := by
    intro s
    rw [hasDerivAt_pi]
    intro i
    have hconst : HasDerivAt (fun _ : ℝ ↦ p 0 i) 0 s :=
      hasDerivAt_const s _
    have hlinear : HasDerivAt (fun x : ℝ ↦ x * g0 i) (g0 i) s := by
      simpa only [id_eq, one_mul] using
        (hasDerivAt_id s).mul_const (g0 i)
    have hsum := ((hcurve.momentum_deriv s i).sub hconst).add hlinear
    convert hsum using 1
    · funext x
      simp only [r, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    · simp only [g0, Pi.neg_apply, Pi.sub_apply]
      ring
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) t,
      ‖-(gradient (q s) - g0)‖ ≤ ω := by
    intro s hs
    have hambient : ‖-(gradient (q s) - g0)‖ ≤
        euclideanNorm (-(gradient (q s) - g0)) := by
      have hdist := dist_le_euclideanNorm_sub
        (-(gradient (q s) - g0)) 0
      simpa only [dist_zero_right, sub_zero] using hdist
    rw [euclideanNorm_neg] at hambient
    exact hambient.trans (hforce s hs)
  have hmean : ‖r t - r 0‖ ≤ ω * ‖t - 0‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (fun s hs ↦ (hr s).differentiableAt)
      (fun s hs ↦ by rw [(hr s).deriv]; exact hderiv s hs)
      (convex_uIcc (0 : ℝ) t) left_mem_uIcc right_mem_uIcc
  have hrzero : r 0 = 0 := by
    dsimp [r]
    rw [zero_smul]
    abel
  have hambient : ‖(p t - p 0) + t • g0‖ ≤ |t| * ω := by
    rw [show |t| * ω = ω * |t| by ring]
    simpa only [r, hrzero, sub_zero, Real.norm_eq_abs] using hmean
  calc
    euclideanNorm ((p t - p 0) + t • gradient (q 0)) =
        euclideanNorm ((p t - p 0) + t • g0) := rfl
    _ ≤ ((Fintype.card ι : ℝ) + 1) *
        dist ((p t - p 0) + t • g0) 0 := by
      simpa only [sub_zero] using euclideanNorm_sub_le_card_succ_mul_dist
        ((p t - p 0) + t • g0) 0
    _ = ((Fintype.card ι : ℝ) + 1) *
        ‖(p t - p 0) + t • g0‖ := by rw [dist_zero_right]
    _ ≤ ((Fintype.card ι : ℝ) + 1) * (|t| * ω) := by gcongr
    _ = ((Fintype.card ι : ℝ) + 1) * |t| * ω := by ring

/-- Relative squared-momentum form of the exact-flow force-integration
estimate. A multiplicative upper bound on position separation is converted
into the quadratic-in-time hypothesis used by the strong-convexity
contraction theorem. -/
theorem RegularPotential.squaredEuclideanNorm_momentum_sub_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (h₁ : IsHamiltonianCurve gradient q₁ p₁)
    (h₂ : IsHamiltonianCurve gradient q₂ p₂)
    {A t : ℝ} (hA : 0 ≤ A) (hp : p₁ 0 = p₂ 0)
    (hposition : ∀ s ∈ uIcc (0 : ℝ) t,
      euclideanNorm (q₁ s - q₂ s) ≤
        A * euclideanNorm (q₁ 0 - q₂ 0)) :
    squaredEuclideanNorm (p₁ t - p₂ t) ≤
      (((Fintype.card ι : ℝ) + 1) * (β : ℝ) * A * |t|) ^ 2 *
        squaredEuclideanNorm (q₁ 0 - q₂ 0) := by
  have hnorm := hreg.euclideanNorm_momentum_sub_le_of_position_sub_le
    h₁ h₂ hp hposition
  have hfactor : 0 ≤
      ((Fintype.card ι : ℝ) + 1) * (β : ℝ) * A * |t| := by positivity
  have hsquare := (sq_le_sq₀ (euclideanNorm_nonneg (p₁ t - p₂ t))
    (mul_nonneg hfactor (euclideanNorm_nonneg (q₁ 0 - q₂ 0)))).mpr
      (by
        apply hnorm.trans_eq
        ring)
  rw [euclideanNorm_sq, mul_pow, euclideanNorm_sq] at hsquare
  exact hsquare

/-- Integrating the relative-momentum estimate gives quadratic-in-time
control of the displacement of the position difference from its initial
value. This is the quantitative bridge from an upper separation bound to the
lower separation bound required by exact-flow contraction. -/
theorem RegularPotential.euclideanNorm_positionSub_sub_initial_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (h₁ : IsHamiltonianCurve gradient q₁ p₁)
    (h₂ : IsHamiltonianCurve gradient q₂ p₂)
    {A t : ℝ} (hA : 0 ≤ A) (hp : p₁ 0 = p₂ 0)
    (hposition : ∀ s ∈ uIcc (0 : ℝ) t,
      euclideanNorm (q₁ s - q₂ s) ≤
        A * euclideanNorm (q₁ 0 - q₂ 0)) :
    euclideanNorm
        ((q₁ t - q₂ t) - (q₁ 0 - q₂ 0)) ≤
      (((Fintype.card ι : ℝ) + 1) ^ 2 * (β : ℝ) * A * |t| ^ 2) *
        euclideanNorm (q₁ 0 - q₂ 0) := by
  let r : ℝ → Position ι := fun s ↦ q₁ s - q₂ s
  let D : ℝ := (Fintype.card ι : ℝ) + 1
  let Q : ℝ := euclideanNorm (q₁ 0 - q₂ 0)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hQ : 0 ≤ Q := by exact euclideanNorm_nonneg _
  have hr : ∀ s, HasDerivAt r (p₁ s - p₂ s) s := by
    intro s
    rw [hasDerivAt_pi]
    intro i
    have h := (h₁.position_deriv s i).sub (h₂.position_deriv s i)
    convert h using 1
    · funext x
      rfl
    · simp only [Pi.sub_apply]
  have hmomentum : ∀ s ∈ uIcc (0 : ℝ) t,
      euclideanNorm (p₁ s - p₂ s) ≤ D * (β : ℝ) * A * Q * |t| := by
    intro s hs
    have hsub : uIcc (0 : ℝ) s ⊆ uIcc (0 : ℝ) t :=
      uIcc_subset_uIcc_left hs
    have hmom := hreg.euclideanNorm_momentum_sub_le_of_position_sub_le
      h₁ h₂ hp (fun u hu ↦ hposition u (hsub hu))
    have hst : |s| ≤ |t| := by
      simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hs
    dsimp [D, Q]
    calc
      euclideanNorm (p₁ s - p₂ s) ≤
          ((Fintype.card ι : ℝ) + 1) * (β : ℝ) *
            (A * euclideanNorm (q₁ 0 - q₂ 0)) * |s| := hmom
      _ ≤ ((Fintype.card ι : ℝ) + 1) * (β : ℝ) * A *
            euclideanNorm (q₁ 0 - q₂ 0) * |t| := by
        have hcoef : 0 ≤
            ((Fintype.card ι : ℝ) + 1) * (β : ℝ) * A *
              euclideanNorm (q₁ 0 - q₂ 0) := by positivity
        calc
          _ = ((Fintype.card ι : ℝ) + 1) * (β : ℝ) * A *
                euclideanNorm (q₁ 0 - q₂ 0) * |s| := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hst hcoef
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) t,
      ‖p₁ s - p₂ s‖ ≤ D * (β : ℝ) * A * Q * |t| := by
    intro s hs
    have hambient : ‖p₁ s - p₂ s‖ ≤
        euclideanNorm (p₁ s - p₂ s) := by
      have hdist := dist_le_euclideanNorm_sub (p₁ s - p₂ s) 0
      simpa only [dist_zero_right, sub_zero] using hdist
    exact hambient.trans (hmomentum s hs)
  have hmean : ‖r t - r 0‖ ≤
      (D * (β : ℝ) * A * Q * |t|) * ‖t - 0‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (fun s hs ↦ (hr s).differentiableAt)
      (fun s hs ↦ by rw [(hr s).deriv]; exact hderiv s hs)
      (convex_uIcc (0 : ℝ) t) left_mem_uIcc right_mem_uIcc
  have hambient : ‖r t - r 0‖ ≤
      D * (β : ℝ) * A * Q * |t| ^ 2 := by
    calc
      ‖r t - r 0‖ ≤ D * (β : ℝ) * A * Q * |t| * |t| := by
        simpa only [Real.norm_eq_abs, sub_zero] using hmean
      _ = D * (β : ℝ) * A * Q * |t| ^ 2 := by ring
  calc
    euclideanNorm ((q₁ t - q₂ t) - (q₁ 0 - q₂ 0)) =
        euclideanNorm (r t - r 0) := rfl
    _ ≤ D * dist (r t - r 0) 0 := by
      simpa only [sub_zero] using
        euclideanNorm_sub_le_card_succ_mul_dist (r t - r 0) 0
    _ = D * ‖r t - r 0‖ := by rw [dist_zero_right]
    _ ≤ D * (D * (β : ℝ) * A * Q * |t| ^ 2) := by gcongr
    _ = (D ^ 2 * (β : ℝ) * A * |t| ^ 2) * Q := by ring

/-- Arbitrary-initial-momentum version of the relative position Taylor
remainder. After removing the initial relative velocity, the remaining
displacement is quadratic in time and controlled by the initial phase size.

This is the form needed after shifting two exact trajectories to an
intermediate leapfrog grid time, where their momenta need not agree. -/
theorem RegularPotential.euclideanNorm_positionSub_sub_initial_sub_time_smul_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (h₁ : IsHamiltonianCurve gradient q₁ p₁)
    (h₂ : IsHamiltonianCurve gradient q₂ p₂)
    {A t : ℝ} (hA : 0 ≤ A)
    (hposition : ∀ s ∈ uIcc (0 : ℝ) t,
      euclideanNorm (q₁ s - q₂ s) ≤
        A * euclideanPhaseSize
          (q₁ 0 - q₂ 0, p₁ 0 - p₂ 0)) :
    euclideanNorm
        (((q₁ t - q₂ t) - (q₁ 0 - q₂ 0)) -
          t • (p₁ 0 - p₂ 0)) ≤
      (((Fintype.card ι : ℝ) + 1) ^ 2 * (β : ℝ) * A * |t| ^ 2) *
        euclideanPhaseSize (q₁ 0 - q₂ 0, p₁ 0 - p₂ 0) := by
  let dp0 : Momentum ι := p₁ 0 - p₂ 0
  let r : ℝ → Position ι := fun s ↦
    (q₁ s - q₂ s) - s • dp0
  let D : ℝ := (Fintype.card ι : ℝ) + 1
  let Z : ℝ := euclideanPhaseSize
    (q₁ 0 - q₂ 0, p₁ 0 - p₂ 0)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hZ : 0 ≤ Z := by exact euclideanPhaseSize_nonneg _
  have hr : ∀ s, HasDerivAt r ((p₁ s - p₂ s) - dp0) s := by
    intro s
    rw [hasDerivAt_pi]
    intro i
    have hpositionDeriv :=
      (h₁.position_deriv s i).sub (h₂.position_deriv s i)
    have hlinear : HasDerivAt (fun x : ℝ ↦ x * dp0 i) (dp0 i) s := by
      simpa only [id_eq, one_mul] using
        (hasDerivAt_id s).mul_const (dp0 i)
    have hsub := hpositionDeriv.sub hlinear
    convert hsub using 1
    · funext x
      simp only [r, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    · simp only [Pi.sub_apply]
  have hmomentum : ∀ s ∈ uIcc (0 : ℝ) t,
      euclideanNorm ((p₁ s - p₂ s) - dp0) ≤
        D * (β : ℝ) * A * Z * |t| := by
    intro s hs
    have hsub : uIcc (0 : ℝ) s ⊆ uIcc (0 : ℝ) t :=
      uIcc_subset_uIcc_left hs
    have hmom :=
      hreg.euclideanNorm_momentumSub_sub_initial_le_of_position_sub_le
        h₁ h₂ (fun u hu ↦ hposition u (hsub hu))
    have hst : |s| ≤ |t| := by
      simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hs
    dsimp [D, Z, dp0]
    calc
      euclideanNorm ((p₁ s - p₂ s) - (p₁ 0 - p₂ 0)) ≤
          ((Fintype.card ι : ℝ) + 1) * (β : ℝ) *
            (A * euclideanPhaseSize
              (q₁ 0 - q₂ 0, p₁ 0 - p₂ 0)) * |s| := hmom
      _ ≤ ((Fintype.card ι : ℝ) + 1) * (β : ℝ) * A *
            euclideanPhaseSize (q₁ 0 - q₂ 0, p₁ 0 - p₂ 0) * |t| := by
        have hcoef : 0 ≤
            ((Fintype.card ι : ℝ) + 1) * (β : ℝ) * A *
              euclideanPhaseSize (q₁ 0 - q₂ 0, p₁ 0 - p₂ 0) := by
          positivity
        calc
          _ = ((Fintype.card ι : ℝ) + 1) * (β : ℝ) * A *
                euclideanPhaseSize
                  (q₁ 0 - q₂ 0, p₁ 0 - p₂ 0) * |s| := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hst hcoef
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) t,
      ‖(p₁ s - p₂ s) - dp0‖ ≤
        D * (β : ℝ) * A * Z * |t| := by
    intro s hs
    have hambient : ‖(p₁ s - p₂ s) - dp0‖ ≤
        euclideanNorm ((p₁ s - p₂ s) - dp0) := by
      have hdist := dist_le_euclideanNorm_sub
        ((p₁ s - p₂ s) - dp0) 0
      simpa only [dist_zero_right, sub_zero] using hdist
    exact hambient.trans (hmomentum s hs)
  have hmean : ‖r t - r 0‖ ≤
      (D * (β : ℝ) * A * Z * |t|) * ‖t - 0‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (fun s hs ↦ (hr s).differentiableAt)
      (fun s hs ↦ by rw [(hr s).deriv]; exact hderiv s hs)
      (convex_uIcc (0 : ℝ) t) left_mem_uIcc right_mem_uIcc
  have hambient : ‖r t - r 0‖ ≤
      D * (β : ℝ) * A * Z * |t| ^ 2 := by
    calc
      ‖r t - r 0‖ ≤ D * (β : ℝ) * A * Z * |t| * |t| := by
        simpa only [Real.norm_eq_abs, sub_zero] using hmean
      _ = D * (β : ℝ) * A * Z * |t| ^ 2 := by ring
  calc
    euclideanNorm
        (((q₁ t - q₂ t) - (q₁ 0 - q₂ 0)) -
          t • (p₁ 0 - p₂ 0)) = euclideanNorm (r t - r 0) := by
      congr 1
      simp only [r, dp0, zero_smul, sub_zero]
      abel
    _ ≤ D * dist (r t - r 0) 0 := by
      simpa only [sub_zero] using
        euclideanNorm_sub_le_card_succ_mul_dist (r t - r 0) 0
    _ = D * ‖r t - r 0‖ := by rw [dist_zero_right]
    _ ≤ D * (D * (β : ℝ) * A * Z * |t| ^ 2) := by gcongr
    _ = (D ^ 2 * (β : ℝ) * A * |t| ^ 2) * Z := by ring

/-- Absolute second-order position remainder for one exact trajectory under a
uniform force bound. -/
theorem euclideanNorm_position_sub_initial_sub_time_smul_le_of_gradient_le
    {gradient : Position ι → Position ι}
    {q : ℝ → Position ι} {p : ℝ → Momentum ι}
    (hcurve : IsHamiltonianCurve gradient q p)
    {G t : ℝ}
    (hgradient : ∀ s ∈ uIcc (0 : ℝ) t,
      euclideanNorm (gradient (q s)) ≤ G) :
    euclideanNorm ((q t - q 0) - t • p 0) ≤
      ((Fintype.card ι : ℝ) + 1) ^ 2 * G * |t| ^ 2 := by
  let r : ℝ → Position ι := fun s ↦ q s - s • p 0
  let D : ℝ := (Fintype.card ι : ℝ) + 1
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hr : ∀ s, HasDerivAt r (p s - p 0) s := by
    intro s
    rw [hasDerivAt_pi]
    intro i
    have hlinear : HasDerivAt (fun x : ℝ ↦ x * p 0 i) (p 0 i) s := by
      simpa only [id_eq, one_mul] using
        (hasDerivAt_id s).mul_const (p 0 i)
    have h := (hcurve.position_deriv s i).sub hlinear
    convert h using 1
    · funext x
      simp only [r, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    · simp only [Pi.sub_apply]
  have hmomentum : ∀ s ∈ uIcc (0 : ℝ) t,
      euclideanNorm (p s - p 0) ≤ D * G * |t| := by
    intro s hs
    have hsub : uIcc (0 : ℝ) s ⊆ uIcc (0 : ℝ) t :=
      uIcc_subset_uIcc_left hs
    have hmom := euclideanNorm_momentum_sub_initial_le_of_gradient_le
      hcurve (fun u hu ↦ hgradient u (hsub hu))
    have hst : |s| ≤ |t| := by
      simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hs
    have hG : 0 ≤ G := by
      have := hgradient 0 left_mem_uIcc
      exact (euclideanNorm_nonneg _).trans this
    dsimp [D]
    calc
      euclideanNorm (p s - p 0) ≤
          ((Fintype.card ι : ℝ) + 1) * G * |s| := hmom
      _ ≤ ((Fintype.card ι : ℝ) + 1) * G * |t| := by gcongr
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) t,
      ‖p s - p 0‖ ≤ D * G * |t| := by
    intro s hs
    have hambient : ‖p s - p 0‖ ≤ euclideanNorm (p s - p 0) := by
      have hdist := dist_le_euclideanNorm_sub (p s - p 0) 0
      simpa only [dist_zero_right, sub_zero] using hdist
    exact hambient.trans (hmomentum s hs)
  have hmean : ‖r t - r 0‖ ≤ (D * G * |t|) * ‖t - 0‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (fun s hs ↦ (hr s).differentiableAt)
      (fun s hs ↦ by rw [(hr s).deriv]; exact hderiv s hs)
      (convex_uIcc (0 : ℝ) t) left_mem_uIcc right_mem_uIcc
  have hambient : ‖r t - r 0‖ ≤ D * G * |t| ^ 2 := by
    calc
      ‖r t - r 0‖ ≤ D * G * |t| * |t| := by
        simpa only [Real.norm_eq_abs, sub_zero] using hmean
      _ = D * G * |t| ^ 2 := by ring
  calc
    euclideanNorm ((q t - q 0) - t • p 0) =
        euclideanNorm (r t - r 0) := by
      congr 1
      simp only [r, zero_smul, sub_zero]
      abel
    _ ≤ D * dist (r t - r 0) 0 := by
      simpa only [sub_zero] using
        euclideanNorm_sub_le_card_succ_mul_dist (r t - r 0) 0
    _ = D * ‖r t - r 0‖ := by rw [dist_zero_right]
    _ ≤ D * (D * G * |t| ^ 2) := by gcongr
    _ = D ^ 2 * G * |t| ^ 2 := by ring

/-- A short-time displacement budget turns the quadratic relative-position
error into a uniform lower bound on separation throughout the whole unordered
time interval. -/
theorem RegularPotential.squaredEuclideanNorm_position_sub_lower
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (h₁ : IsHamiltonianCurve gradient q₁ p₁)
    (h₂ : IsHamiltonianCurve gradient q₂ p₂)
    {A δ t : ℝ} (hA : 0 ≤ A) (hδone : δ ≤ 1)
    (hp : p₁ 0 = p₂ 0)
    (hbudget :
      ((Fintype.card ι : ℝ) + 1) ^ 2 * (β : ℝ) * A * |t| ^ 2 ≤ δ)
    (hposition : ∀ s ∈ uIcc (0 : ℝ) t,
      euclideanNorm (q₁ s - q₂ s) ≤
        A * euclideanNorm (q₁ 0 - q₂ 0)) :
    ∀ s ∈ uIcc (0 : ℝ) t,
      (1 - δ) ^ 2 * squaredEuclideanNorm (q₁ 0 - q₂ 0) ≤
        squaredEuclideanNorm (q₁ s - q₂ s) := by
  intro s hs
  have hsub : uIcc (0 : ℝ) s ⊆ uIcc (0 : ℝ) t :=
    uIcc_subset_uIcc_left hs
  have hdisp := hreg.euclideanNorm_positionSub_sub_initial_le
    h₁ h₂ hA hp (fun u hu ↦ hposition u (hsub hu))
  have hst : |s| ≤ |t| := by
    simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hs
  have htimeSq : |s| ^ 2 ≤ |t| ^ 2 :=
    (sq_le_sq₀ (abs_nonneg s) (abs_nonneg t)).mpr hst
  have hcoefNonneg : 0 ≤
      ((Fintype.card ι : ℝ) + 1) ^ 2 * (β : ℝ) * A := by positivity
  have hcoef :
      ((Fintype.card ι : ℝ) + 1) ^ 2 * (β : ℝ) * A * |s| ^ 2 ≤ δ :=
    (mul_le_mul_of_nonneg_left htimeSq hcoefNonneg).trans hbudget
  have hQ : 0 ≤ euclideanNorm (q₁ 0 - q₂ 0) := euclideanNorm_nonneg _
  have herr : euclideanNorm
      ((q₁ s - q₂ s) - (q₁ 0 - q₂ 0)) ≤
        δ * euclideanNorm (q₁ 0 - q₂ 0) := by
    apply hdisp.trans
    exact mul_le_mul_of_nonneg_right hcoef hQ
  have htriangle : euclideanNorm (q₁ 0 - q₂ 0) ≤
      euclideanNorm (q₁ s - q₂ s) +
        euclideanNorm ((q₁ s - q₂ s) - (q₁ 0 - q₂ 0)) := by
    have hadd := euclideanNorm_add_le
      ((q₁ 0 - q₂ 0) - (q₁ s - q₂ s)) (q₁ s - q₂ s)
    rw [show (q₁ 0 - q₂ 0) - (q₁ s - q₂ s) + (q₁ s - q₂ s) =
        q₁ 0 - q₂ 0 by abel] at hadd
    rw [show (q₁ 0 - q₂ 0) - (q₁ s - q₂ s) =
        -((q₁ s - q₂ s) - (q₁ 0 - q₂ 0)) by abel,
      euclideanNorm_neg] at hadd
    linarith
  have hnorm : (1 - δ) * euclideanNorm (q₁ 0 - q₂ 0) ≤
      euclideanNorm (q₁ s - q₂ s) := by linarith
  have hleftNonneg : 0 ≤
      (1 - δ) * euclideanNorm (q₁ 0 - q₂ 0) :=
    mul_nonneg (sub_nonneg.mpr hδone) hQ
  have hsquare := (sq_le_sq₀ hleftNonneg
    (euclideanNorm_nonneg (q₁ s - q₂ s))).mpr hnorm
  rw [mul_pow, euclideanNorm_sq, euclideanNorm_sq] at hsquare
  exact hsquare

/-- Global Lipschitzness of the gradient gives exponential stability of the
full relative Hamiltonian phase state for nonnegative times. This is the
standard Grönwall estimate for the first-order system `(q',p')=(p,-∇U(q))` in
mathlib's finite-product norm. -/
theorem RegularPotential.norm_phaseSub_le_exp_of_nonneg
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (h₁ : IsHamiltonianCurve gradient q₁ p₁)
    (h₂ : IsHamiltonianCurve gradient q₂ p₂)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖(q₁ t - q₂ t, p₁ t - p₂ t)‖ ≤
      ‖(q₁ 0 - q₂ 0, p₁ 0 - p₂ 0)‖ *
        Real.exp ((1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1)) * t) := by
  let f : ℝ → PhaseSpace ι := fun s ↦
    (q₁ s - q₂ s, p₁ s - p₂ s)
  let f' : ℝ → PhaseSpace ι := fun s ↦
    (p₁ s - p₂ s, -(gradient (q₁ s) - gradient (q₂ s)))
  let K : ℝ := 1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1)
  have hK : 1 ≤ K := by
    dsimp [K]
    have : 0 ≤ (β : ℝ) * ((Fintype.card ι : ℝ) + 1) := by positivity
    linarith
  have hfderiv : ∀ s, HasDerivAt f (f' s) s := by
    intro s
    have hq : HasDerivAt (fun x ↦ q₁ x - q₂ x) (p₁ s - p₂ s) s := by
      rw [hasDerivAt_pi]
      intro i
      have h := (h₁.position_deriv s i).sub (h₂.position_deriv s i)
      convert h using 1
      · funext x
        rfl
      · simp only [Pi.sub_apply]
    have hp' : HasDerivAt (fun x ↦ p₁ x - p₂ x)
        (-(gradient (q₁ s) - gradient (q₂ s))) s := by
      rw [hasDerivAt_pi]
      intro i
      have h := (h₁.momentum_deriv s i).sub (h₂.momentum_deriv s i)
      convert h using 1
      · funext x
        rfl
      · simp only [Pi.neg_apply, Pi.sub_apply]
        ring
    exact hq.prodMk hp'
  have hbound : ∀ s,
      ‖f' s‖ ≤ K * ‖f s‖ := by
    intro s
    have hqAmbient : ‖q₁ s - q₂ s‖ ≤ ‖f s‖ := by
      simp only [f, Prod.norm_def]
      exact le_max_left _ _
    have hpAmbient : ‖p₁ s - p₂ s‖ ≤ ‖f s‖ := by
      simp only [f, Prod.norm_def]
      exact le_max_right _ _
    have hgradAmbient : ‖gradient (q₁ s) - gradient (q₂ s)‖ ≤
        (β : ℝ) * ((Fintype.card ι : ℝ) + 1) * ‖f s‖ := by
      have h₀ : ‖gradient (q₁ s) - gradient (q₂ s)‖ ≤
          euclideanNorm (gradient (q₁ s) - gradient (q₂ s)) := by
        have hdist := dist_le_euclideanNorm_sub
          (gradient (q₁ s) - gradient (q₂ s)) 0
        simpa only [dist_zero_right, sub_zero] using hdist
      have h₁' := hreg.euclideanNorm_gradient_sub_le (q₁ s) (q₂ s)
      have h₂' := euclideanNorm_sub_le_card_succ_mul_dist (q₁ s) (q₂ s)
      have hdist : dist (q₁ s) (q₂ s) = ‖q₁ s - q₂ s‖ :=
        dist_eq_norm _ _
      calc
        ‖gradient (q₁ s) - gradient (q₂ s)‖ ≤
            euclideanNorm (gradient (q₁ s) - gradient (q₂ s)) := h₀
        _ ≤ (β : ℝ) * euclideanNorm (q₁ s - q₂ s) := h₁'
        _ ≤ (β : ℝ) *
            (((Fintype.card ι : ℝ) + 1) * dist (q₁ s) (q₂ s)) := by
          gcongr
        _ = (β : ℝ) * ((Fintype.card ι : ℝ) + 1) *
            ‖q₁ s - q₂ s‖ := by rw [hdist]; ring
        _ ≤ (β : ℝ) * ((Fintype.card ι : ℝ) + 1) * ‖f s‖ := by
          gcongr
    have hfirst : ‖p₁ s - p₂ s‖ ≤ K * ‖f s‖ :=
      hpAmbient.trans (by
        have hnorm : 0 ≤ ‖f s‖ := norm_nonneg _
        nlinarith)
    have hsecond : ‖-(gradient (q₁ s) - gradient (q₂ s))‖ ≤
        K * ‖f s‖ := by
      rw [norm_neg]
      apply hgradAmbient.trans
      have hnorm : 0 ≤ ‖f s‖ := norm_nonneg _
      dsimp [K]
      nlinarith
    simp only [f', Prod.norm_def]
    exact max_le hfirst hsecond
  have hfcont : Continuous f :=
    continuous_iff_continuousAt.mpr fun s ↦ (hfderiv s).continuousAt
  have hgronwall := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := f) (f' := f') (δ := ‖f 0‖) (K := K) (ε := 0)
    (a := 0) (b := t) hfcont.continuousOn
    (fun s hs ↦ (hfderiv s).hasDerivWithinAt)
    (le_refl _) (fun s hs ↦ by simpa using hbound s) t
    (right_mem_Icc.mpr ht)
  rw [gronwallBound_ε0] at hgronwall
  simpa only [f, K, sub_zero] using hgronwall

/-- Two-sided exponential stability of the relative Hamiltonian phase state,
obtained from the nonnegative-time Grönwall estimate by time reversal. -/
theorem RegularPotential.norm_phaseSub_le_exp
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (h₁ : IsHamiltonianCurve gradient q₁ p₁)
    (h₂ : IsHamiltonianCurve gradient q₂ p₂) (t : ℝ) :
    ‖(q₁ t - q₂ t, p₁ t - p₂ t)‖ ≤
      ‖(q₁ 0 - q₂ 0, p₁ 0 - p₂ 0)‖ *
        Real.exp
          ((1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1)) * |t|) := by
  rcases le_total 0 t with ht | ht
  · have h := hreg.norm_phaseSub_le_exp_of_nonneg h₁ h₂ ht
    simpa [abs_of_nonneg ht] using h
  · let qr₁ := timeReversePosition q₁
    let qr₂ := timeReversePosition q₂
    let pr₁ := timeReverseMomentum p₁
    let pr₂ := timeReverseMomentum p₂
    have h := hreg.norm_phaseSub_le_exp_of_nonneg
      h₁.timeReverse h₂.timeReverse (neg_nonneg.mpr ht)
      (t := -t)
    dsimp [qr₁, qr₂, pr₁, pr₂, timeReversePosition,
      timeReverseMomentum] at h
    simp only [neg_neg, neg_zero] at h
    rw [show -p₁ t - -p₂ t = -(p₁ t - p₂ t) by abel,
      show -p₁ 0 - -p₂ 0 = -(p₁ 0 - p₂ 0) by abel,
      norm_neg, norm_neg] at h
    simpa [abs_of_nonpos ht, Prod.norm_def] using h

/-- Explicit Euclidean phase-size stability factor for arbitrary paired
initial momenta. -/
noncomputable def exactFlowPhaseStabilityFactor
    (β : NNReal) (t : ℝ) : ℝ :=
  2 * ((Fintype.card ι : ℝ) + 1) *
    Real.exp
      ((1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1)) * |t|)

theorem exactFlowPhaseStabilityFactor_pos (β : NNReal) (t : ℝ) :
    0 < exactFlowPhaseStabilityFactor (ι := ι) β t := by
  unfold exactFlowPhaseStabilityFactor
  positivity

theorem continuous_exactFlowPhaseStabilityFactor (β : NNReal) :
    Continuous (exactFlowPhaseStabilityFactor (ι := ι) β) := by
  unfold exactFlowPhaseStabilityFactor
  fun_prop

/-- Arbitrary paired exact Hamiltonian curves are stable in the project's
explicit Euclidean phase size. Unlike the position-only specialization, this
theorem does not assume equal initial momenta. -/
theorem RegularPotential.euclideanPhaseSize_phaseSub_le_exp
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (h₁ : IsHamiltonianCurve gradient q₁ p₁)
    (h₂ : IsHamiltonianCurve gradient q₂ p₂) (t : ℝ) :
    euclideanPhaseSize (q₁ t - q₂ t, p₁ t - p₂ t) ≤
      exactFlowPhaseStabilityFactor (ι := ι) β t *
        euclideanPhaseSize (q₁ 0 - q₂ 0, p₁ 0 - p₂ 0) := by
  let D : ℝ := (Fintype.card ι : ℝ) + 1
  let zt : PhaseSpace ι := (q₁ t - q₂ t, p₁ t - p₂ t)
  let z0 : PhaseSpace ι := (q₁ 0 - q₂ 0, p₁ 0 - p₂ 0)
  have hphase := hreg.norm_phaseSub_le_exp h₁ h₂ t
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hq : euclideanNorm zt.1 ≤ D * ‖zt‖ := by
    have heuc := euclideanNorm_sub_le_card_succ_mul_dist zt.1 0
    simp only [sub_zero, dist_zero_right] at heuc
    apply heuc.trans
    exact mul_le_mul_of_nonneg_left (le_max_left ‖zt.1‖ ‖zt.2‖) hD
  have hp : euclideanNorm zt.2 ≤ D * ‖zt‖ := by
    have heuc := euclideanNorm_sub_le_card_succ_mul_dist zt.2 0
    simp only [sub_zero, dist_zero_right] at heuc
    apply heuc.trans
    exact mul_le_mul_of_nonneg_left (le_max_right ‖zt.1‖ ‖zt.2‖) hD
  have hz0 : ‖z0‖ ≤ euclideanPhaseSize z0 := by
    rw [Prod.norm_def]
    apply max_le
    · have hamb : ‖z0.1‖ ≤ euclideanNorm z0.1 := by
        have := dist_le_euclideanNorm_sub z0.1 0
        simpa only [dist_zero_right, sub_zero] using this
      exact hamb.trans (euclideanNorm_fst_le_phaseSize z0)
    · have hamb : ‖z0.2‖ ≤ euclideanNorm z0.2 := by
        have := dist_le_euclideanNorm_sub z0.2 0
        simpa only [dist_zero_right, sub_zero] using this
      unfold euclideanPhaseSize
      exact hamb.trans (le_add_of_nonneg_left (euclideanNorm_nonneg z0.1))
  have hexp : 0 ≤ Real.exp
      ((1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1)) * |t|) :=
    (Real.exp_pos _).le
  have hzt : ‖zt‖ ≤ ‖z0‖ * Real.exp
      ((1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1)) * |t|) := hphase
  change euclideanPhaseSize zt ≤
    exactFlowPhaseStabilityFactor (ι := ι) β t * euclideanPhaseSize z0
  unfold euclideanPhaseSize exactFlowPhaseStabilityFactor
  calc
    euclideanNorm zt.1 + euclideanNorm zt.2 ≤ D * ‖zt‖ + D * ‖zt‖ :=
      add_le_add hq hp
    _ ≤ D * (‖z0‖ * Real.exp
        ((1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1)) * |t|)) +
      D * (‖z0‖ * Real.exp
        ((1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1)) * |t|)) := by
      gcongr
    _ = 2 * D * (‖z0‖ * Real.exp
        ((1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1)) * |t|)) := by ring
    _ ≤ 2 * D * (euclideanPhaseSize z0 * Real.exp
        ((1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1)) * |t|)) := by
      gcongr
    _ = _ := by
      dsimp [D]
      unfold euclideanPhaseSize
      ring

/-- The arbitrary-momentum Euclidean phase factor controls every intermediate
signed time in a requested horizon. -/
theorem RegularPotential.euclideanPhaseSize_phaseSub_le_on_uIcc
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (h₁ : IsHamiltonianCurve gradient q₁ p₁)
    (h₂ : IsHamiltonianCurve gradient q₂ p₂) {t : ℝ} :
    ∀ s ∈ uIcc (0 : ℝ) t,
      euclideanPhaseSize (q₁ s - q₂ s, p₁ s - p₂ s) ≤
        exactFlowPhaseStabilityFactor (ι := ι) β t *
          euclideanPhaseSize (q₁ 0 - q₂ 0, p₁ 0 - p₂ 0) := by
  intro s hs
  have h := hreg.euclideanPhaseSize_phaseSub_le_exp h₁ h₂ s
  have hst : |s| ≤ |t| := by
    simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hs
  have hK : 0 ≤ 1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1) := by positivity
  have hexp : Real.exp
      ((1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1)) * |s|) ≤
    Real.exp
      ((1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1)) * |t|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hst hK)
  apply h.trans
  unfold exactFlowPhaseStabilityFactor
  have hfactor : 0 ≤ 2 * ((Fintype.card ι : ℝ) + 1) := by positivity
  have hinitial : 0 ≤
      euclideanPhaseSize (q₁ 0 - q₂ 0, p₁ 0 - p₂ 0) :=
    euclideanPhaseSize_nonneg _
  gcongr

/-- Absolute phase growth for an exact Hamiltonian curve at nonnegative time.
The affine forcing term is the gradient at the origin. -/
theorem RegularPotential.norm_phase_le_gronwallBound_of_nonneg
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q : ℝ → Position ι} {p : ℝ → Momentum ι}
    (hcurve : IsHamiltonianCurve gradient q p)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖(q t, p t)‖ ≤
      gronwallBound ‖(q 0, p 0)‖
        (1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1))
        (euclideanNorm (gradient 0)) t := by
  let f : ℝ → PhaseSpace ι := fun s ↦ (q s, p s)
  let f' : ℝ → PhaseSpace ι := fun s ↦ (p s, -gradient (q s))
  let K : ℝ := 1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1)
  let G : ℝ := euclideanNorm (gradient 0)
  have hK : 1 ≤ K := by
    dsimp [K]
    have : 0 ≤ (β : ℝ) * ((Fintype.card ι : ℝ) + 1) := by positivity
    linarith
  have hfderiv : ∀ s, HasDerivAt f (f' s) s := by
    intro s
    have hq : HasDerivAt q (p s) s :=
      hasDerivAt_pi.mpr (hcurve.position_deriv s)
    have hp' : HasDerivAt p (-gradient (q s)) s :=
      hasDerivAt_pi.mpr (hcurve.momentum_deriv s)
    exact hq.prodMk hp'
  have hbound : ∀ s, ‖f' s‖ ≤ K * ‖f s‖ + G := by
    intro s
    have hqAmbient : ‖q s‖ ≤ ‖f s‖ := by
      simp only [f, Prod.norm_def]
      exact le_max_left _ _
    have hpAmbient : ‖p s‖ ≤ ‖f s‖ := by
      simp only [f, Prod.norm_def]
      exact le_max_right _ _
    have hgradAmbient : ‖gradient (q s)‖ ≤
        (β : ℝ) * ((Fintype.card ι : ℝ) + 1) * ‖f s‖ + G := by
      have h₀ : ‖gradient (q s)‖ ≤ euclideanNorm (gradient (q s)) := by
        have hdist := dist_le_euclideanNorm_sub (gradient (q s)) 0
        simpa only [dist_zero_right, sub_zero] using hdist
      have h₁' := hreg.euclideanNorm_gradient_le (q s)
      have h₂' : euclideanNorm (q s) ≤
          ((Fintype.card ι : ℝ) + 1) * ‖q s‖ := by
        have h := euclideanNorm_sub_le_card_succ_mul_dist (q s) 0
        simpa only [sub_zero, dist_zero_right] using h
      calc
        ‖gradient (q s)‖ ≤ euclideanNorm (gradient (q s)) := h₀
        _ ≤ (β : ℝ) * euclideanNorm (q s) + G := h₁'
        _ ≤ (β : ℝ) *
              (((Fintype.card ι : ℝ) + 1) * ‖q s‖) + G := by
          gcongr
        _ = (β : ℝ) * ((Fintype.card ι : ℝ) + 1) * ‖q s‖ + G := by
          ring
        _ ≤ (β : ℝ) * ((Fintype.card ι : ℝ) + 1) * ‖f s‖ + G := by
          gcongr
    have hfirst : ‖p s‖ ≤ K * ‖f s‖ + G := by
      have hG : 0 ≤ G := by dsimp [G]; exact euclideanNorm_nonneg _
      have hnorm : 0 ≤ ‖f s‖ := norm_nonneg _
      exact hpAmbient.trans (by nlinarith)
    have hsecond : ‖-gradient (q s)‖ ≤ K * ‖f s‖ + G := by
      rw [norm_neg]
      apply hgradAmbient.trans
      have hnorm : 0 ≤ ‖f s‖ := norm_nonneg _
      dsimp [K]
      nlinarith
    simp only [f', Prod.norm_def]
    exact max_le hfirst hsecond
  have hfcont : Continuous f :=
    continuous_iff_continuousAt.mpr fun s ↦ (hfderiv s).continuousAt
  have hgronwall := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := f) (f' := f') (δ := ‖f 0‖) (K := K) (ε := G)
    (a := 0) (b := t) hfcont.continuousOn
    (fun s hs ↦ (hfderiv s).hasDerivWithinAt)
    (le_refl _) (fun s hs ↦ hbound s) t (right_mem_Icc.mpr ht)
  simpa only [f, K, G, sub_zero] using hgronwall

/-- Two-sided absolute phase growth, obtained by time reversal. -/
theorem RegularPotential.norm_phase_le_gronwallBound
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q : ℝ → Position ι} {p : ℝ → Momentum ι}
    (hcurve : IsHamiltonianCurve gradient q p) (t : ℝ) :
    ‖(q t, p t)‖ ≤
      gronwallBound ‖(q 0, p 0)‖
        (1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1))
        (euclideanNorm (gradient 0)) |t| := by
  rcases le_total 0 t with ht | ht
  · simpa [abs_of_nonneg ht] using
      hreg.norm_phase_le_gronwallBound_of_nonneg hcurve ht
  · have h := hreg.norm_phase_le_gronwallBound_of_nonneg
      hcurve.timeReverse (neg_nonneg.mpr ht) (t := -t)
    dsimp [timeReversePosition, timeReverseMomentum] at h
    simp only [neg_neg, neg_zero] at h
    simp only [norm_neg] at h
    simpa [abs_of_nonpos ht, Prod.norm_def] using h

/-- Absolute phase bound over the horizon `|t|`, based on the initial phase
state and the affine force at the origin. -/
noncomputable def exactFlowAbsolutePhaseBound
    (β : NNReal) (gradient : Position ι → Position ι)
    (z : PhaseSpace ι) (t : ℝ) : ℝ :=
  gronwallBound ‖z‖
    (1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1))
    (euclideanNorm (gradient 0)) |t|

theorem exactFlowAbsolutePhaseBound_nonneg
    (β : NNReal) (gradient : Position ι → Position ι)
    (z : PhaseSpace ι) (t : ℝ) :
    0 ≤ exactFlowAbsolutePhaseBound β gradient z t := by
  unfold exactFlowAbsolutePhaseBound
  have hδ : 0 ≤ ‖z‖ := norm_nonneg _
  have hK : 0 ≤ 1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1) := by positivity
  have hG : 0 ≤ euclideanNorm (gradient 0) := euclideanNorm_nonneg _
  have hmono := gronwallBound_mono hδ hG hK
  have hzero := hmono (abs_nonneg t)
  rw [gronwallBound_x0] at hzero
  exact hδ.trans hzero

/-- Exact position displacement is at most time times the uniform absolute
phase bound. -/
theorem RegularPotential.euclideanNorm_position_sub_initial_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q : ℝ → Position ι} {p : ℝ → Momentum ι}
    (hcurve : IsHamiltonianCurve gradient q p) (t : ℝ) :
    euclideanNorm (q t - q 0) ≤
      ((Fintype.card ι : ℝ) + 1) *
        exactFlowAbsolutePhaseBound β gradient (q 0, p 0) t * |t| := by
  let B : ℝ := exactFlowAbsolutePhaseBound β gradient (q 0, p 0) t
  have hK : 0 ≤ 1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1) := by positivity
  have hG : 0 ≤ euclideanNorm (gradient 0) := euclideanNorm_nonneg _
  have hmono := gronwallBound_mono (norm_nonneg (q 0, p 0)) hG hK
  have hpbound : ∀ s ∈ uIcc (0 : ℝ) t, ‖p s‖ ≤ B := by
    intro s hs
    have hphase := hreg.norm_phase_le_gronwallBound hcurve s
    have hpPhase : ‖p s‖ ≤ ‖(q s, p s)‖ := by
      simp only [Prod.norm_def]
      exact le_max_right _ _
    have hst : |s| ≤ |t| := by
      simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hs
    exact hpPhase.trans (hphase.trans (by
      dsimp [B, exactFlowAbsolutePhaseBound]
      exact hmono hst))
  have hqderiv : ∀ s, HasDerivAt q (p s) s := fun s ↦
    hasDerivAt_pi.mpr (hcurve.position_deriv s)
  have hmean : ‖q t - q 0‖ ≤ B * ‖t - 0‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (fun s hs ↦ (hqderiv s).differentiableAt)
      (fun s hs ↦ by rw [(hqderiv s).deriv]; exact hpbound s hs)
      (convex_uIcc (0 : ℝ) t) left_mem_uIcc right_mem_uIcc
  calc
    euclideanNorm (q t - q 0) ≤
        ((Fintype.card ι : ℝ) + 1) * dist (q t - q 0) 0 := by
      simpa only [sub_zero] using
        euclideanNorm_sub_le_card_succ_mul_dist (q t - q 0) 0
    _ = ((Fintype.card ι : ℝ) + 1) * ‖q t - q 0‖ := by
      rw [dist_zero_right]
    _ ≤ ((Fintype.card ι : ℝ) + 1) * (B * |t|) := by
      gcongr
      simpa only [Real.norm_eq_abs, sub_zero] using hmean
    _ = ((Fintype.card ι : ℝ) + 1) * B * |t| := by ring

/-- A direct Euclidean phase-size bound controls exact position displacement
without introducing the global Grönwall expression. -/
theorem euclideanNorm_position_sub_initial_le_of_phaseSize_le
    {gradient : Position ι → Position ι}
    {q : ℝ → Position ι} {p : ℝ → Momentum ι}
    (hcurve : IsHamiltonianCurve gradient q p) {B t : ℝ}
    (hphase : ∀ s ∈ uIcc (0 : ℝ) t,
      euclideanPhaseSize (q s, p s) ≤ B) :
    euclideanNorm (q t - q 0) ≤
      ((Fintype.card ι : ℝ) + 1) * B * |t| := by
  have hpbound : ∀ s ∈ uIcc (0 : ℝ) t, ‖p s‖ ≤ B := by
    intro s hs
    have hambient : ‖p s‖ ≤ euclideanNorm (p s) := by
      have hdist := dist_le_euclideanNorm_sub (p s) 0
      simpa only [dist_zero_right, sub_zero] using hdist
    have heuc : euclideanNorm (p s) ≤ euclideanPhaseSize (q s, p s) := by
      unfold euclideanPhaseSize
      exact le_add_of_nonneg_left (euclideanNorm_nonneg _)
    exact hambient.trans (heuc.trans (hphase s hs))
  have hqderiv : ∀ s, HasDerivAt q (p s) s := fun s ↦
    hasDerivAt_pi.mpr (hcurve.position_deriv s)
  have hmean : ‖q t - q 0‖ ≤ B * ‖t - 0‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (fun s hs ↦ (hqderiv s).differentiableAt)
      (fun s hs ↦ by rw [(hqderiv s).deriv]; exact hpbound s hs)
      (convex_uIcc (0 : ℝ) t) left_mem_uIcc right_mem_uIcc
  calc
    euclideanNorm (q t - q 0) ≤
        ((Fintype.card ι : ℝ) + 1) * dist (q t - q 0) 0 := by
      simpa only [sub_zero] using
        euclideanNorm_sub_le_card_succ_mul_dist (q t - q 0) 0
    _ = ((Fintype.card ι : ℝ) + 1) * ‖q t - q 0‖ := by
      rw [dist_zero_right]
    _ ≤ ((Fintype.card ι : ℝ) + 1) * (B * |t|) := by
      gcongr
      simpa only [Real.norm_eq_abs, sub_zero] using hmean
    _ = ((Fintype.card ι : ℝ) + 1) * B * |t| := by ring

/-- Uniform absolute position-displacement allowance over a signed horizon. -/
noncomputable def exactFlowPositionDisplacementBound
    (β : NNReal) (gradient : Position ι → Position ι)
    (z : PhaseSpace ι) (t : ℝ) : ℝ :=
  ((Fintype.card ι : ℝ) + 1) *
    exactFlowAbsolutePhaseBound β gradient z t * |t|

theorem exactFlowPositionDisplacementBound_nonneg
    (β : NNReal) (gradient : Position ι → Position ι)
    (z : PhaseSpace ι) (t : ℝ) :
    0 ≤ exactFlowPositionDisplacementBound β gradient z t := by
  unfold exactFlowPositionDisplacementBound
  exact mul_nonneg
    (mul_nonneg (by positivity)
      (exactFlowAbsolutePhaseBound_nonneg β gradient z t)) (abs_nonneg t)

/-- Absolute phase bound uniform over initial states of ambient norm at most
`M`. -/
noncomputable def exactFlowUniformAbsolutePhaseBound
    (β : NNReal) (gradient : Position ι → Position ι)
    (M t : ℝ) : ℝ :=
  gronwallBound M
    (1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1))
    (euclideanNorm (gradient 0)) |t|

/-- Uniform bound in the explicit Euclidean phase size used by the numerical
analysis. -/
noncomputable def exactFlowUniformEuclideanPhaseBound
    (β : NNReal) (gradient : Position ι → Position ι)
    (M T : ℝ) : ℝ :=
  2 * ((Fintype.card ι : ℝ) + 1) *
    exactFlowUniformAbsolutePhaseBound β gradient M T

/-- Position-displacement allowance obtained by integrating the uniform
Euclidean phase bound over a signed horizon. -/
noncomputable def exactFlowUniformEuclideanPositionDisplacementBound
    (β : NNReal) (gradient : Position ι → Position ι)
    (M T : ℝ) : ℝ :=
  ((Fintype.card ι : ℝ) + 1) *
    exactFlowUniformEuclideanPhaseBound (ι := ι) β gradient M T * |T|

theorem exactFlowUniformEuclideanPhaseBound_nonneg
    (β : NNReal) (gradient : Position ι → Position ι)
    {M T : ℝ} (hM : 0 ≤ M) :
    0 ≤ exactFlowUniformEuclideanPhaseBound
      (ι := ι) β gradient M T := by
  unfold exactFlowUniformEuclideanPhaseBound
  unfold exactFlowUniformAbsolutePhaseBound
  have hK : 0 ≤ 1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1) := by positivity
  have hG : 0 ≤ euclideanNorm (gradient 0) := euclideanNorm_nonneg _
  have hbound := gronwallBound_mono hM hG hK (abs_nonneg T)
  rw [gronwallBound_x0] at hbound
  have hb0 : 0 ≤ gronwallBound M
      (1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1))
      (euclideanNorm (gradient 0)) |T| := hM.trans hbound
  exact mul_nonneg (by positivity) hb0

theorem continuous_exactFlowUniformEuclideanPositionDisplacementBound
    (β : NNReal) (gradient : Position ι → Position ι) (M : ℝ) :
    Continuous (exactFlowUniformEuclideanPositionDisplacementBound
      (ι := ι) β gradient M) := by
  let K : ℝ := 1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1)
  let G : ℝ := euclideanNorm (gradient 0)
  have hgronwall : Continuous (gronwallBound M K G) :=
    continuous_iff_continuousAt.mpr fun x ↦
      (hasDerivAt_gronwallBound M K G x).continuousAt
  unfold exactFlowUniformEuclideanPositionDisplacementBound
  unfold exactFlowUniformEuclideanPhaseBound
  unfold exactFlowUniformAbsolutePhaseBound
  exact (continuous_const.mul
    (continuous_const.mul (hgronwall.comp continuous_abs))).mul continuous_abs

@[simp]
theorem exactFlowUniformEuclideanPositionDisplacementBound_zero
    (β : NNReal) (gradient : Position ι → Position ι) (M : ℝ) :
    exactFlowUniformEuclideanPositionDisplacementBound
      (ι := ι) β gradient M 0 = 0 := by
  simp [exactFlowUniformEuclideanPositionDisplacementBound]

/-- A compact core inside an open region admits one positive signed horizon
whose explicit Euclidean exact-flow envelope remains in that region. -/
theorem exists_pos_exactFlowUniformEuclidean_envelope
    (β : NNReal) (gradient : Position ι → Position ι)
    {K S : Set (Position ι)} (hK : IsCompact K) (hKS : K ⊆ interior S)
    (M : ℝ) {H : ℝ} (hH : 0 < H) :
    ∃ T > 0, T ≤ H ∧ Metric.cthickening
        (exactFlowUniformEuclideanPositionDisplacementBound
          (ι := ι) β gradient M T) K ⊆ interior S := by
  obtain ⟨r, hr, hthick⟩ :=
    hK.exists_cthickening_subset_open isOpen_interior hKS
  let f := exactFlowUniformEuclideanPositionDisplacementBound
    (ι := ι) β gradient M
  have hf : ContinuousAt f 0 :=
    (continuous_exactFlowUniformEuclideanPositionDisplacementBound
      (ι := ι) β gradient M).continuousAt
  have hev : ∀ᶠ t in nhds (0 : ℝ), f t < r :=
    hf.eventually_lt continuousAt_const (by simpa [f] using hr)
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp hev
  let T := min (a / 2) H
  have hT : 0 < T := lt_min (half_pos ha) hH
  have hTH : T ≤ H := min_le_right _ _
  have hTr : f T < r := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    have : |T| < a := by
      rw [abs_of_pos hT]
      exact (min_le_left _ _).trans_lt (half_lt_self ha)
    simpa only [sub_zero] using this
  refine ⟨T, hT, hTH, ?_⟩
  exact (Metric.cthickening_mono hTr.le K).trans hthick

/-- Uniform exact Euclidean phase growth from an initial Euclidean phase-size
bound, valid at every signed time within `T`. -/
theorem RegularPotential.euclideanPhaseSize_le_uniform
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q : ℝ → Position ι} {p : ℝ → Momentum ι}
    (hcurve : IsHamiltonianCurve gradient q p)
    {M T t : ℝ} (hM : 0 ≤ M)
    (hinitial : euclideanPhaseSize (q 0, p 0) ≤ M)
    (ht : |t| ≤ T) :
    euclideanPhaseSize (q t, p t) ≤
      exactFlowUniformEuclideanPhaseBound
        (ι := ι) β gradient M T := by
  let D : ℝ := (Fintype.card ι : ℝ) + 1
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hinitialAmbient : ‖(q 0, p 0)‖ ≤ M := by
    apply (show ‖(q 0, p 0)‖ ≤ euclideanPhaseSize (q 0, p 0) by
      rw [Prod.norm_def]
      apply max_le
      · have hambient : ‖q 0‖ ≤ euclideanNorm (q 0) := by
          have h := dist_le_euclideanNorm_sub (q 0) 0
          simpa only [dist_zero_right, sub_zero] using h
        unfold euclideanPhaseSize
        exact hambient.trans (le_add_of_nonneg_right (euclideanNorm_nonneg _))
      · have hambient : ‖p 0‖ ≤ euclideanNorm (p 0) := by
          have h := dist_le_euclideanNorm_sub (p 0) 0
          simpa only [dist_zero_right, sub_zero] using h
        unfold euclideanPhaseSize
        exact hambient.trans (le_add_of_nonneg_left (euclideanNorm_nonneg _))) |>.trans
      hinitial
  have hnorm := hreg.norm_phase_le_gronwallBound hcurve t
  have huniformTime : gronwallBound M
      (1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1))
      (euclideanNorm (gradient 0)) |t| ≤
      exactFlowUniformAbsolutePhaseBound β gradient M T := by
    unfold exactFlowUniformAbsolutePhaseBound
    have hK : 0 ≤ 1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1) := by positivity
    have hG : 0 ≤ euclideanNorm (gradient 0) := euclideanNorm_nonneg _
    have hT : 0 ≤ T := (abs_nonneg t).trans ht
    simpa [abs_of_nonneg hT] using gronwallBound_mono hM hG hK ht
  have hnorm' : ‖(q t, p t)‖ ≤
      exactFlowUniformAbsolutePhaseBound β gradient M T := by
    have habsolute : ‖(q t, p t)‖ ≤
        exactFlowAbsolutePhaseBound β gradient (q 0, p 0) t := by
      simpa only [exactFlowAbsolutePhaseBound] using hnorm
    have hinitUniform : exactFlowAbsolutePhaseBound β gradient
        (q 0, p 0) t ≤ exactFlowUniformAbsolutePhaseBound β gradient M t := by
      let K : ℝ := 1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1)
      have hK : K ≠ 0 := by
        have : 0 < K := by dsimp [K]; positivity
        exact this.ne'
      unfold exactFlowAbsolutePhaseBound exactFlowUniformAbsolutePhaseBound
      rw [gronwallBound_of_K_ne_0 hK, gronwallBound_of_K_ne_0 hK]
      change ‖(q 0, p 0)‖ * Real.exp (K * |t|) + _ ≤
        M * Real.exp (K * |t|) + _
      gcongr
    exact habsolute.trans (hinitUniform.trans huniformTime)
  have hq : euclideanNorm (q t) ≤ D * ‖(q t, p t)‖ := by
    have h := euclideanNorm_sub_le_card_succ_mul_dist (q t) 0
    simp only [sub_zero, dist_zero_right] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (le_max_left ‖q t‖ ‖p t‖) hD)
  have hp : euclideanNorm (p t) ≤ D * ‖(q t, p t)‖ := by
    have h := euclideanNorm_sub_le_card_succ_mul_dist (p t) 0
    simp only [sub_zero, dist_zero_right] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (le_max_right ‖q t‖ ‖p t‖) hD)
  unfold euclideanPhaseSize exactFlowUniformEuclideanPhaseBound
  calc
    euclideanNorm (q t) + euclideanNorm (p t) ≤
        D * ‖(q t, p t)‖ + D * ‖(q t, p t)‖ := add_le_add hq hp
    _ ≤ D * exactFlowUniformAbsolutePhaseBound β gradient M T +
        D * exactFlowUniformAbsolutePhaseBound β gradient M T := by gcongr
    _ = 2 * ((Fintype.card ι : ℝ) + 1) *
        exactFlowUniformAbsolutePhaseBound β gradient M T := by
      dsimp [D]
      ring

theorem RegularPotential.euclideanNorm_position_sub_initial_le_uniform
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q : ℝ → Position ι} {p : ℝ → Momentum ι}
    (hcurve : IsHamiltonianCurve gradient q p)
    {M T t : ℝ} (hM : 0 ≤ M)
    (hinitial : euclideanPhaseSize (q 0, p 0) ≤ M)
    (ht : |t| ≤ T) :
    euclideanNorm (q t - q 0) ≤
      exactFlowUniformEuclideanPositionDisplacementBound
        (ι := ι) β gradient M T := by
  have hT : 0 ≤ T := (abs_nonneg t).trans ht
  have hphase : ∀ s ∈ uIcc (0 : ℝ) t,
      euclideanPhaseSize (q s, p s) ≤
        exactFlowUniformEuclideanPhaseBound
          (ι := ι) β gradient M T := by
    intro s hs
    have hst : |s| ≤ |t| := by
      simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hs
    exact hreg.euclideanPhaseSize_le_uniform
      hcurve hM hinitial (hst.trans ht)
  have hdisp := euclideanNorm_position_sub_initial_le_of_phaseSize_le
    hcurve hphase
  unfold exactFlowUniformEuclideanPositionDisplacementBound
  apply hdisp.trans
  have hB := exactFlowUniformEuclideanPhaseBound_nonneg
    (ι := ι) β gradient (T := T) hM
  have hcoef : 0 ≤ ((Fintype.card ι : ℝ) + 1) *
      exactFlowUniformEuclideanPhaseBound
        (ι := ι) β gradient M T := by positivity
  apply mul_le_mul_of_nonneg_left _ hcoef
  simpa [abs_of_nonneg hT] using ht

/-- A compact initial-position core and the explicit uniform displacement
radius generate a compact exact-flow envelope with one positive buffer inside
the requested region. -/
theorem RegularPotential.exists_pos_uniform_exactFlow_envelope_buffer
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {K S : Set (Position ι)} (hK : IsCompact K)
    {M T : ℝ} (hM : 0 ≤ M)
    (henvelope : Metric.cthickening
        (exactFlowUniformEuclideanPositionDisplacementBound
          (ι := ι) β gradient M T) K ⊆ interior S) :
    ∃ buffer > 0,
      ∀ {q : ℝ → Position ι} {p : ℝ → Momentum ι},
        IsHamiltonianCurve gradient q p →
        q 0 ∈ K → euclideanPhaseSize (q 0, p 0) ≤ M →
        ∀ {t : ℝ}, |t| ≤ T → Metric.closedBall (q t) buffer ⊆ S := by
  let R := exactFlowUniformEuclideanPositionDisplacementBound
    (ι := ι) β gradient M T
  have hEnvelopeCompact : IsCompact (Metric.cthickening R K) :=
    hK.cthickening
  obtain ⟨buffer, hbuffer, hballs⟩ :=
    Mcmc.Hamiltonian.IsCompact.exists_pos_forall_closedBall_subset
      hEnvelopeCompact henvelope
  refine ⟨buffer, hbuffer, ?_⟩
  intro q p hcurve hq₀ hphase₀ t ht
  apply hballs (q t)
  apply Metric.mem_cthickening_of_dist_le (q t) (q 0) R K hq₀
  apply (dist_le_euclideanNorm_sub (q t) (q 0)).trans
  exact hreg.euclideanNorm_position_sub_initial_le_uniform
    hcurve hM hphase₀ ht

/-- Uniform position-displacement allowance for initial phase norm at most
`M`. -/
noncomputable def exactFlowUniformPositionDisplacementBound
    (β : NNReal) (gradient : Position ι → Position ι)
    (M t : ℝ) : ℝ :=
  ((Fintype.card ι : ℝ) + 1) *
    exactFlowUniformAbsolutePhaseBound β gradient M t * |t|

theorem exactFlowAbsolutePhaseBound_le_uniform
    (β : NNReal) (gradient : Position ι → Position ι)
    (z : PhaseSpace ι) {M t : ℝ} (hz : ‖z‖ ≤ M) :
    exactFlowAbsolutePhaseBound β gradient z t ≤
      exactFlowUniformAbsolutePhaseBound β gradient M t := by
  let K : ℝ := 1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1)
  have hK : K ≠ 0 := by
    have : 0 < K := by dsimp [K]; positivity
    exact this.ne'
  unfold exactFlowAbsolutePhaseBound exactFlowUniformAbsolutePhaseBound
  rw [gronwallBound_of_K_ne_0 hK, gronwallBound_of_K_ne_0 hK]
  change ‖z‖ * Real.exp (K * |t|) + _ ≤
    M * Real.exp (K * |t|) + _
  gcongr

theorem exactFlowPositionDisplacementBound_le_uniform
    (β : NNReal) (gradient : Position ι → Position ι)
    (z : PhaseSpace ι) {M t : ℝ} (hz : ‖z‖ ≤ M) :
    exactFlowPositionDisplacementBound β gradient z t ≤
      exactFlowUniformPositionDisplacementBound β gradient M t := by
  unfold exactFlowPositionDisplacementBound
  unfold exactFlowUniformPositionDisplacementBound
  have hD : 0 ≤ (Fintype.card ι : ℝ) + 1 := by positivity
  have ht : 0 ≤ |t| := abs_nonneg t
  gcongr
  exact exactFlowAbsolutePhaseBound_le_uniform β gradient z hz

theorem continuous_exactFlowUniformPositionDisplacementBound
    (β : NNReal) (gradient : Position ι → Position ι) (M : ℝ) :
    Continuous
      (exactFlowUniformPositionDisplacementBound (ι := ι) β gradient M) := by
  let K : ℝ := 1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1)
  let G : ℝ := euclideanNorm (gradient 0)
  have hgronwall : Continuous (gronwallBound M K G) :=
    continuous_iff_continuousAt.mpr fun x ↦
      (hasDerivAt_gronwallBound M K G x).continuousAt
  unfold exactFlowUniformPositionDisplacementBound
  unfold exactFlowUniformAbsolutePhaseBound
  exact (continuous_const.mul (hgronwall.comp continuous_abs)).mul continuous_abs

@[simp]
theorem exactFlowUniformPositionDisplacementBound_zero
    (β : NNReal) (gradient : Position ι → Position ι) (M : ℝ) :
    exactFlowUniformPositionDisplacementBound (ι := ι) β gradient M 0 = 0 := by
  simp [exactFlowUniformPositionDisplacementBound]

/-- The horizon displacement allowance controls every intermediate signed
time. -/
theorem RegularPotential.euclideanNorm_position_sub_initial_le_on_uIcc
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q : ℝ → Position ι} {p : ℝ → Momentum ι}
    (hcurve : IsHamiltonianCurve gradient q p) {t : ℝ} :
    ∀ s ∈ uIcc (0 : ℝ) t,
      euclideanNorm (q s - q 0) ≤
        exactFlowPositionDisplacementBound β gradient (q 0, p 0) t := by
  intro s hs
  have hdisp := hreg.euclideanNorm_position_sub_initial_le hcurve s
  have hst : |s| ≤ |t| := by
    simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hs
  have hK : 0 ≤ 1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1) := by positivity
  have hG : 0 ≤ euclideanNorm (gradient 0) := euclideanNorm_nonneg _
  have hmono := gronwallBound_mono (norm_nonneg (q 0, p 0)) hG hK hst
  apply hdisp.trans
  unfold exactFlowPositionDisplacementBound
  have hBmono : exactFlowAbsolutePhaseBound β gradient (q 0, p 0) s ≤
      exactFlowAbsolutePhaseBound β gradient (q 0, p 0) t := by
    unfold exactFlowAbsolutePhaseBound
    exact hmono
  have hBs := exactFlowAbsolutePhaseBound_nonneg β gradient (q 0, p 0) s
  have hBt := exactFlowAbsolutePhaseBound_nonneg β gradient (q 0, p 0) t
  gcongr

/-- A buffered initial position remains in a target region throughout the
signed horizon whenever the explicit displacement allowance fits inside the
buffer radius. -/
theorem RegularPotential.position_mem_of_closedBall_subset
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q : ℝ → Position ι} {p : ℝ → Momentum ι}
    (hcurve : IsHamiltonianCurve gradient q p)
    {S : Set (Position ι)} {r t : ℝ}
    (hbudget : exactFlowPositionDisplacementBound β gradient (q 0, p 0) t ≤ r)
    (hball : Metric.closedBall (q 0) r ⊆ S) :
    ∀ s ∈ uIcc (0 : ℝ) t, q s ∈ S := by
  intro s hs
  apply hball
  rw [Metric.mem_closedBall]
  exact (dist_le_euclideanNorm_sub (q s) (q 0)).trans
    ((hreg.euclideanNorm_position_sub_initial_le_on_uIcc hcurve s hs).trans
      hbudget)

/-- A compact core inside the region interior admits one uniform positive
buffer for every exact curve started in that core. -/
theorem RegularPotential.exists_pos_uniform_exactFlow_region_buffer
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {K S : Set (Position ι)} (hK : IsCompact K)
    (hKS : K ⊆ interior S) :
    ∃ r > 0, ∀ (q : ℝ → Position ι) (p : ℝ → Momentum ι)
      (_hcurve : IsHamiltonianCurve gradient q p) (t : ℝ),
      q 0 ∈ K →
      exactFlowPositionDisplacementBound β gradient (q 0, p 0) t ≤ r →
      ∀ s ∈ uIcc (0 : ℝ) t, q s ∈ S := by
  rcases Mcmc.Hamiltonian.IsCompact.exists_pos_forall_closedBall_subset
    hK hKS with ⟨r, hr, hball⟩
  refine ⟨r, hr, ?_⟩
  intro q p hcurve t hq hbudget
  exact hreg.position_mem_of_closedBall_subset hcurve hbudget (hball _ hq)

/-- Shared initial momentum specializes phase stability to an explicit
uniform upper bound on position separation. This supplies the final
relative-motion estimate needed by the quantitative exact-flow contraction
pipeline. -/
theorem RegularPotential.euclideanNorm_position_sub_le_exp
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (h₁ : IsHamiltonianCurve gradient q₁ p₁)
    (h₂ : IsHamiltonianCurve gradient q₂ p₂)
    (hp : p₁ 0 = p₂ 0) (t : ℝ) :
    euclideanNorm (q₁ t - q₂ t) ≤
      (((Fintype.card ι : ℝ) + 1) *
        Real.exp
          ((1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1)) * |t|)) *
        euclideanNorm (q₁ 0 - q₂ 0) := by
  let D : ℝ := (Fintype.card ι : ℝ) + 1
  let z : PhaseSpace ι := (q₁ t - q₂ t, p₁ t - p₂ t)
  have hphase := hreg.norm_phaseSub_le_exp h₁ h₂ t
  have hpositionAmbient : ‖q₁ t - q₂ t‖ ≤ ‖z‖ := by
    simp only [z, Prod.norm_def]
    exact le_max_left _ _
  have hinitial : ‖(q₁ 0 - q₂ 0, p₁ 0 - p₂ 0)‖ ≤
      euclideanNorm (q₁ 0 - q₂ 0) := by
    rw [hp, sub_self, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
    have hdist := dist_le_euclideanNorm_sub (q₁ 0 - q₂ 0) 0
    simpa only [dist_zero_right, sub_zero] using hdist
  have hexp : 0 ≤ Real.exp
      ((1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1)) * |t|) :=
    Real.exp_pos _ |>.le
  calc
    euclideanNorm (q₁ t - q₂ t) ≤ D * dist (q₁ t - q₂ t) 0 := by
      simpa only [D, sub_zero] using
        euclideanNorm_sub_le_card_succ_mul_dist (q₁ t - q₂ t) 0
    _ = D * ‖q₁ t - q₂ t‖ := by rw [dist_zero_right]
    _ ≤ D * ‖z‖ := by gcongr
    _ ≤ D * (‖(q₁ 0 - q₂ 0, p₁ 0 - p₂ 0)‖ *
        Real.exp
          ((1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1)) * |t|)) := by
      gcongr
    _ ≤ D * (euclideanNorm (q₁ 0 - q₂ 0) *
        Real.exp
          ((1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1)) * |t|)) := by
      gcongr
    _ = (D * Real.exp
          ((1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1)) * |t|)) *
        euclideanNorm (q₁ 0 - q₂ 0) := by ring

/-- Explicit finite-horizon position stability factor for exact Hamiltonian
flow under a globally `β`-Lipschitz gradient. -/
noncomputable def exactFlowPositionStabilityFactor (β : NNReal) (t : ℝ) : ℝ :=
  ((Fintype.card ι : ℝ) + 1) *
    Real.exp ((1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1)) * |t|)

theorem exactFlowPositionStabilityFactor_pos (β : NNReal) (t : ℝ) :
    0 < exactFlowPositionStabilityFactor (ι := ι) β t := by
  unfold exactFlowPositionStabilityFactor
  positivity

/-- Scalar relative-position displacement rate appearing in the exact-flow
short-time budget. -/
noncomputable def exactFlowRelativeDisplacementRate (β : NNReal) (t : ℝ) : ℝ :=
  ((Fintype.card ι : ℝ) + 1) ^ 2 * (β : ℝ) *
    exactFlowPositionStabilityFactor (ι := ι) β t * |t| ^ 2

/-- Relative-position displacement rate for arbitrary paired initial phases.
The linear term is transport by the initial relative momentum; the quadratic
term is the force-induced Taylor remainder. -/
noncomputable def exactFlowPhaseRelativeDisplacementRate
    (β : NNReal) (t : ℝ) : ℝ :=
  |t| + ((Fintype.card ι : ℝ) + 1) ^ 2 * (β : ℝ) *
    exactFlowPhaseStabilityFactor (ι := ι) β t * |t| ^ 2

/-- Scalar squared relative-momentum rate appearing in the exact-flow
short-time budget. -/
noncomputable def exactFlowRelativeMomentumRate (β : NNReal) (t : ℝ) : ℝ :=
  (((Fintype.card ι : ℝ) + 1) * (β : ℝ) *
    exactFlowPositionStabilityFactor (ι := ι) β t * |t|) ^ 2

theorem continuous_exactFlowPositionStabilityFactor (β : NNReal) :
    Continuous (exactFlowPositionStabilityFactor (ι := ι) β) := by
  unfold exactFlowPositionStabilityFactor
  fun_prop

theorem continuous_exactFlowRelativeDisplacementRate (β : NNReal) :
    Continuous (exactFlowRelativeDisplacementRate (ι := ι) β) := by
  unfold exactFlowRelativeDisplacementRate
  exact ((continuous_const.mul continuous_const).mul
    (continuous_exactFlowPositionStabilityFactor β)).mul
      (continuous_abs.pow 2)

theorem continuous_exactFlowPhaseRelativeDisplacementRate (β : NNReal) :
    Continuous (exactFlowPhaseRelativeDisplacementRate (ι := ι) β) := by
  unfold exactFlowPhaseRelativeDisplacementRate
  exact continuous_abs.add
    ((((continuous_const.mul continuous_const).mul
      (continuous_exactFlowPhaseStabilityFactor β)).mul
        (continuous_abs.pow 2)))

theorem continuous_exactFlowRelativeMomentumRate (β : NNReal) :
    Continuous (exactFlowRelativeMomentumRate (ι := ι) β) := by
  unfold exactFlowRelativeMomentumRate
  exact (((continuous_const.mul continuous_const).mul
    (continuous_exactFlowPositionStabilityFactor β)).mul continuous_abs).pow 2

@[simp]
theorem exactFlowRelativeDisplacementRate_zero (β : NNReal) :
    exactFlowRelativeDisplacementRate (ι := ι) β 0 = 0 := by
  simp [exactFlowRelativeDisplacementRate]

@[simp]
theorem exactFlowPhaseRelativeDisplacementRate_zero (β : NNReal) :
    exactFlowPhaseRelativeDisplacementRate (ι := ι) β 0 = 0 := by
  simp [exactFlowPhaseRelativeDisplacementRate]

@[simp]
theorem exactFlowRelativeMomentumRate_zero (β : NNReal) :
    exactFlowRelativeMomentumRate (ι := ι) β 0 = 0 := by
  simp [exactFlowRelativeMomentumRate]

/-- A continuous scalar budget vanishing at zero lies below every positive
threshold on one symmetric positive horizon. -/
theorem exists_pos_forall_abs_le_of_continuousAt_zero
    {f : ℝ → ℝ} (hf : ContinuousAt f 0) (hf0 : f 0 = 0)
    {b : ℝ} (hb : 0 < b) :
    ∃ T > 0, ∀ t, |t| ≤ T → f t < b := by
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), f t < b :=
    hf.eventually_lt continuousAt_const (by simpa [hf0] using hb)
  rcases Metric.mem_nhds_iff.mp hev with ⟨ε, hε, hball⟩
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro t ht
  apply hball
  rw [Metric.mem_ball, Real.dist_eq]
  have : |t| < ε := ht.trans_lt (half_lt_self hε)
  simpa only [sub_zero] using this

/-- Simultaneous scalar certificate for exact-flow containment and relative
contraction on one symmetric positive horizon. -/
structure ExactFlowHorizonCertificate
    (β : NNReal) (gradient : Position ι → Position ι)
    (α M r : ℝ) : Type where
  delta : ℝ
  kappa : ℝ
  horizon : ℝ
  delta_lt_one : delta < 1
  kappa_pos : 0 < kappa
  horizon_pos : 0 < horizon
  containment : ∀ t, |t| ≤ horizon →
    exactFlowUniformPositionDisplacementBound β gradient M t ≤ r
  relativeDisplacement : ∀ t, |t| ≤ horizon →
    exactFlowRelativeDisplacementRate (ι := ι) β t ≤ delta
  relativeMomentum : ∀ t, |t| ≤ horizon →
    exactFlowRelativeMomentumRate (ι := ι) β t ≤
      (α - kappa) * (1 - delta) ^ 2

/-- A positive local strong-convexity modulus and positive containment buffer
yield one common horizon satisfying every scalar exact-flow budget. -/
theorem exists_exactFlowHorizonCertificate
    (β : NNReal) (gradient : Position ι → Position ι)
    {α M r : ℝ} (hα : 0 < α) (hr : 0 < r) :
    Nonempty (ExactFlowHorizonCertificate (ι := ι) β gradient α M r) := by
  let δ : ℝ := 1 / 2
  let κ : ℝ := α / 2
  have hδ : δ < 1 := by dsimp [δ]; norm_num
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have htarget : 0 < (α - κ) * (1 - δ) ^ 2 := by
    dsimp [κ, δ]
    nlinarith
  rcases exists_pos_forall_abs_le_of_continuousAt_zero
      (continuous_exactFlowUniformPositionDisplacementBound β gradient M).continuousAt
      (exactFlowUniformPositionDisplacementBound_zero β gradient M) hr with
    ⟨T₁, hT₁, hcontain⟩
  rcases exists_pos_forall_abs_le_of_continuousAt_zero
      (continuous_exactFlowRelativeDisplacementRate (ι := ι) β).continuousAt
      (exactFlowRelativeDisplacementRate_zero (ι := ι) β)
      (show 0 < δ by dsimp [δ]; norm_num) with
    ⟨T₂, hT₂, hrelative⟩
  rcases exists_pos_forall_abs_le_of_continuousAt_zero
      (continuous_exactFlowRelativeMomentumRate (ι := ι) β).continuousAt
      (exactFlowRelativeMomentumRate_zero (ι := ι) β) htarget with
    ⟨T₃, hT₃, hmomentum⟩
  let T := min T₁ (min T₂ T₃)
  have hT : 0 < T := by
    dsimp [T]
    exact lt_min hT₁ (lt_min hT₂ hT₃)
  refine ⟨⟨δ, κ, T, hδ, hκ, hT, ?_, ?_, ?_⟩⟩
  · intro t ht
    exact (hcontain t (ht.trans (min_le_left _ _))).le
  · intro t ht
    have hTT₂ : T ≤ T₂ := (min_le_right _ _).trans (min_le_left _ _)
    exact (hrelative t (ht.trans hTT₂)).le
  · intro t ht
    have hTT₃ : T ≤ T₃ := (min_le_right _ _).trans (min_le_right _ _)
    exact (hmomentum t (ht.trans hTT₃)).le

/-- The exponential stability factor controls position separation uniformly
over the unordered interval from zero to the requested integration time. -/
theorem RegularPotential.euclideanNorm_position_sub_le_on_uIcc
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (h₁ : IsHamiltonianCurve gradient q₁ p₁)
    (h₂ : IsHamiltonianCurve gradient q₂ p₂)
    (hp : p₁ 0 = p₂ 0) {t : ℝ} :
    ∀ s ∈ uIcc (0 : ℝ) t,
      euclideanNorm (q₁ s - q₂ s) ≤
        exactFlowPositionStabilityFactor (ι := ι) β t *
          euclideanNorm (q₁ 0 - q₂ 0) := by
  intro s hs
  have h := hreg.euclideanNorm_position_sub_le_exp h₁ h₂ hp s
  have hst : |s| ≤ |t| := by
    simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hs
  have hK : 0 ≤ 1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1) := by
    positivity
  have hexp : Real.exp
      ((1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1)) * |s|) ≤
      Real.exp
        ((1 + (β : ℝ) * ((Fintype.card ι : ℝ) + 1)) * |t|) := by
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hst hK)
  apply h.trans
  unfold exactFlowPositionStabilityFactor
  have hD : 0 ≤ (Fintype.card ι : ℝ) + 1 := by positivity
  have hQ : 0 ≤ euclideanNorm (q₁ 0 - q₂ 0) := euclideanNorm_nonneg _
  gcongr

/-- Compact-uniform paired force variation along exact Hamiltonian curves.
The abstract force-modulus premise is discharged by compact containment,
small absolute displacement, and the explicit relative exact-flow rate. -/
theorem RegularPotential.exists_uniform_exact_forceVariation_bound
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ M ≥ 0,
      ∀ {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι},
        IsHamiltonianCurve gradient q₁ p₁ →
        IsHamiltonianCurve gradient q₂ p₂ →
        p₁ 0 = p₂ 0 →
        ∀ {t : ℝ},
          q₁ 0 ∈ S → q₂ 0 ∈ S →
          (∀ s ∈ uIcc (0 : ℝ) t, q₁ s ∈ S) →
          (∀ s ∈ uIcc (0 : ℝ) t, q₂ s ∈ S) →
          (∀ s ∈ uIcc (0 : ℝ) t,
            euclideanNorm (q₁ s - q₁ 0) ≤ δ) →
          (∀ s ∈ uIcc (0 : ℝ) t,
            euclideanNorm (q₂ s - q₂ 0) ≤ δ) →
          ∀ s ∈ uIcc (0 : ℝ) t,
            euclideanNorm
                ((gradient (q₁ s) - gradient (q₂ s)) -
                  (gradient (q₁ 0) - gradient (q₂ 0))) ≤
              ((Fintype.card ι : ℝ) + 1) *
                  (η + M * exactFlowRelativeDisplacementRate
                    (ι := ι) β t) *
                euclideanNorm (q₁ 0 - q₂ 0) := by
  obtain ⟨δ, hδ, M, hM, hforce⟩ :=
    hreg.exists_uniform_relative_forceVariation_bound
      hScompact hSconvex hη
  refine ⟨δ, hδ, M, hM, ?_⟩
  intro q₁ q₂ p₁ p₂ hcurve₁ hcurve₂ hp t
    hq₁₀ hq₂₀ hq₁S hq₂S hq₁disp hq₂disp s hs
  have hupper := hreg.euclideanNorm_position_sub_le_on_uIcc
    hcurve₁ hcurve₂ hp (t := t)
  have hsub : uIcc (0 : ℝ) s ⊆ uIcc (0 : ℝ) t :=
    uIcc_subset_uIcc_left hs
  have hrelativeRaw := hreg.euclideanNorm_positionSub_sub_initial_le
    hcurve₁ hcurve₂
      (exactFlowPositionStabilityFactor_pos (ι := ι) β t).le hp
      (fun u hu ↦ hupper u (hsub hu))
  have hst : |s| ≤ |t| := by
    simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hs
  have htimeSq : |s| ^ 2 ≤ |t| ^ 2 :=
    (sq_le_sq₀ (abs_nonneg s) (abs_nonneg t)).mpr hst
  have hcoefNonneg : 0 ≤
      ((Fintype.card ι : ℝ) + 1) ^ 2 * (β : ℝ) *
        exactFlowPositionStabilityFactor (ι := ι) β t :=
    mul_nonneg (mul_nonneg (sq_nonneg _) β.coe_nonneg)
      (exactFlowPositionStabilityFactor_pos (ι := ι) β t).le
  have hrelative : euclideanNorm
      ((q₁ s - q₂ s) - (q₁ 0 - q₂ 0)) ≤
        exactFlowRelativeDisplacementRate (ι := ι) β t *
          euclideanNorm (q₁ 0 - q₂ 0) := by
    apply hrelativeRaw.trans
    unfold exactFlowRelativeDisplacementRate
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left htimeSq hcoefNonneg)
      (euclideanNorm_nonneg _)
  apply hforce hq₂₀ hq₁₀ (hq₂S s hs) (hq₁S s hs)
  · apply (dist_le_euclideanNorm_sub (q₂ s) (q₂ 0)).trans
    exact hq₂disp s hs
  · apply (dist_le_euclideanNorm_sub (q₁ s) (q₁ 0)).trans
    exact hq₁disp s hs
  · exact hrelative

/-- Compact-uniform paired force variation for exact Hamiltonian curves with
arbitrary initial relative momentum. The bound scales with full initial phase
size and uses the linear-plus-quadratic phase displacement rate. -/
theorem RegularPotential.exists_uniform_exact_phaseForceVariation_bound
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ M ≥ 0,
      ∀ {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι},
        IsHamiltonianCurve gradient q₁ p₁ →
        IsHamiltonianCurve gradient q₂ p₂ →
        ∀ {t : ℝ},
          q₁ 0 ∈ S → q₂ 0 ∈ S →
          (∀ s ∈ uIcc (0 : ℝ) t, q₁ s ∈ S) →
          (∀ s ∈ uIcc (0 : ℝ) t, q₂ s ∈ S) →
          (∀ s ∈ uIcc (0 : ℝ) t,
            euclideanNorm (q₁ s - q₁ 0) ≤ δ) →
          (∀ s ∈ uIcc (0 : ℝ) t,
            euclideanNorm (q₂ s - q₂ 0) ≤ δ) →
          ∀ s ∈ uIcc (0 : ℝ) t,
            euclideanNorm
                ((gradient (q₁ s) - gradient (q₂ s)) -
                  (gradient (q₁ 0) - gradient (q₂ 0))) ≤
              ((Fintype.card ι : ℝ) + 1) *
                  (η + M * exactFlowPhaseRelativeDisplacementRate
                    (ι := ι) β t) *
                euclideanPhaseSize
                  (q₁ 0 - q₂ 0, p₁ 0 - p₂ 0) := by
  obtain ⟨δ, hδ, M, hM, _hMglobal, hforce⟩ :=
    hreg.exists_uniform_euclideanNorm_gradientSub_sub_gradientSub_bound
      hScompact hSconvex hη
  refine ⟨δ, hδ, M, hM, ?_⟩
  intro q₁ q₂ p₁ p₂ hcurve₁ hcurve₂ t
    hq₁₀ hq₂₀ hq₁S hq₂S hq₁disp hq₂disp s hs
  let A := exactFlowPhaseStabilityFactor (ι := ι) β t
  let Z := euclideanPhaseSize (q₁ 0 - q₂ 0, p₁ 0 - p₂ 0)
  have hphase := hreg.euclideanPhaseSize_phaseSub_le_on_uIcc
    hcurve₁ hcurve₂ (t := t)
  have hsub : uIcc (0 : ℝ) s ⊆ uIcc (0 : ℝ) t :=
    uIcc_subset_uIcc_left hs
  have hposition : ∀ u ∈ uIcc (0 : ℝ) s,
      euclideanNorm (q₁ u - q₂ u) ≤ A * Z := by
    intro u hu
    exact (euclideanNorm_fst_le_phaseSize _).trans (hphase u (hsub hu))
  have hremainder :=
    hreg.euclideanNorm_positionSub_sub_initial_sub_time_smul_le
      hcurve₁ hcurve₂ (exactFlowPhaseStabilityFactor_pos
        (ι := ι) β t).le hposition
  have hst : |s| ≤ |t| := by
    simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hs
  have htimeSq : |s| ^ 2 ≤ |t| ^ 2 :=
    (sq_le_sq₀ (abs_nonneg s) (abs_nonneg t)).mpr hst
  have hdp : euclideanNorm (p₁ 0 - p₂ 0) ≤ Z := by
    dsimp [Z]
    unfold euclideanPhaseSize
    exact le_add_of_nonneg_left (euclideanNorm_nonneg _)
  have hrelative : euclideanNorm
      ((q₁ s - q₂ s) - (q₁ 0 - q₂ 0)) ≤
        exactFlowPhaseRelativeDisplacementRate (ι := ι) β t * Z := by
    have hdecomp :
        (q₁ s - q₂ s) - (q₁ 0 - q₂ 0) =
          (((q₁ s - q₂ s) - (q₁ 0 - q₂ 0)) -
            s • (p₁ 0 - p₂ 0)) + s • (p₁ 0 - p₂ 0) := by abel
    rw [hdecomp]
    apply (euclideanNorm_add_le _ _).trans
    rw [euclideanNorm_smul]
    have htransport := mul_le_mul_of_nonneg_left hdp (abs_nonneg s)
    apply (add_le_add hremainder htransport).trans
    unfold exactFlowPhaseRelativeDisplacementRate
    dsimp [A, Z] at hremainder ⊢
    have hcoef : 0 ≤
        ((Fintype.card ι : ℝ) + 1) ^ 2 * (β : ℝ) *
          exactFlowPhaseStabilityFactor (ι := ι) β t :=
      mul_nonneg (mul_nonneg (sq_nonneg _) β.coe_nonneg)
        (exactFlowPhaseStabilityFactor_pos (ι := ι) β t).le
    have hquad := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left htimeSq hcoef)
      (euclideanPhaseSize_nonneg
        (q₁ 0 - q₂ 0, p₁ 0 - p₂ 0))
    have hlinear := mul_le_mul_of_nonneg_right hst
      (euclideanPhaseSize_nonneg
        (q₁ 0 - q₂ 0, p₁ 0 - p₂ 0))
    nlinarith
  have hmain := hforce hq₂₀ hq₁₀ (hq₂S s hs) (hq₁S s hs)
    ((dist_le_euclideanNorm_sub (q₂ s) (q₂ 0)).trans (hq₂disp s hs))
    ((dist_le_euclideanNorm_sub (q₁ s) (q₁ 0)).trans (hq₁disp s hs))
  apply hmain.trans
  have hMrelative := mul_le_mul_of_nonneg_left hrelative hM
  have hZ : 0 ≤ Z := euclideanPhaseSize_nonneg _
  calc
    ((Fintype.card ι : ℝ) + 1) *
        (η * euclideanNorm (q₁ 0 - q₂ 0) +
          M * euclideanNorm
            ((q₁ s - q₂ s) - (q₁ 0 - q₂ 0))) ≤
      ((Fintype.card ι : ℝ) + 1) *
        (η * euclideanPhaseSize
            (q₁ 0 - q₂ 0, p₁ 0 - p₂ 0) +
          M * (exactFlowPhaseRelativeDisplacementRate (ι := ι) β t *
            euclideanPhaseSize
              (q₁ 0 - q₂ 0, p₁ 0 - p₂ 0))) := by
      gcongr
      unfold euclideanPhaseSize
      exact le_add_of_nonneg_right (euclideanNorm_nonneg _)
    _ = ((Fintype.card ι : ℝ) + 1) *
          (η + M * exactFlowPhaseRelativeDisplacementRate
            (ι := ι) β t) *
        euclideanPhaseSize (q₁ 0 - q₂ 0, p₁ 0 - p₂ 0) := by ring

/-- Local strong convexity supplies the second-variation margin once relative
momentum and loss of position separation are controlled uniformly.  This
isolates the two compact-uniform estimates still needed in Lemma 4.2. -/
theorem LocalStrongConvexity.squaredEuclideanSeparation_le_sub_sq
    {gradient : Position ι → Position ι} {S : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient S α)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (h₁ : IsHamiltonianCurve gradient q₁ p₁)
    (h₂ : IsHamiltonianCurve gradient q₂ p₂)
    {κ d t : ℝ} (hκ : 0 ≤ κ) (ht : 0 ≤ t) (hp : p₁ 0 = p₂ 0)
    (hregion : ∀ s ∈ Icc (0 : ℝ) t, q₁ s ∈ S ∧ q₂ s ∈ S)
    (hmomentum : ∀ s ∈ Icc (0 : ℝ) t,
      squaredEuclideanNorm (p₁ s - p₂ s) ≤
        (α - κ) * squaredEuclideanNorm (q₁ s - q₂ s))
    (hseparation : ∀ s ∈ Icc (0 : ℝ) t,
      d ≤ squaredEuclideanNorm (q₁ s - q₂ s)) :
    squaredEuclideanNorm (q₁ t - q₂ t) ≤
      squaredEuclideanNorm (q₁ 0 - q₂ 0) - κ * d * t ^ 2 := by
  apply squaredEuclideanSeparation_le_sub_sq_of_secondVariationMargin
    h₁ h₂ ht hp
  intro s hs
  have hforce := hconv.inner_gradient_sub_lower
    (hregion s hs).1 (hregion s hs).2
  have hmomentum' := hmomentum s hs
  have hsep := mul_le_mul_of_nonneg_left (hseparation s hs) hκ
  nlinarith

/-- Two-sided local-strong-convexity specialization. All containment and
relative-momentum hypotheses are required on the unordered interval between
the initial time and `t`. -/
theorem LocalStrongConvexity.squaredEuclideanSeparation_le_sub_sq_twoSided
    {gradient : Position ι → Position ι} {S : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient S α)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (h₁ : IsHamiltonianCurve gradient q₁ p₁)
    (h₂ : IsHamiltonianCurve gradient q₂ p₂)
    {κ d t : ℝ} (hκ : 0 ≤ κ) (hp : p₁ 0 = p₂ 0)
    (hregion : ∀ s ∈ uIcc (0 : ℝ) t, q₁ s ∈ S ∧ q₂ s ∈ S)
    (hmomentum : ∀ s ∈ uIcc (0 : ℝ) t,
      squaredEuclideanNorm (p₁ s - p₂ s) ≤
        (α - κ) * squaredEuclideanNorm (q₁ s - q₂ s))
    (hseparation : ∀ s ∈ uIcc (0 : ℝ) t,
      d ≤ squaredEuclideanNorm (q₁ s - q₂ s)) :
    squaredEuclideanNorm (q₁ t - q₂ t) ≤
      squaredEuclideanNorm (q₁ 0 - q₂ 0) - κ * d * t ^ 2 := by
  apply squaredEuclideanSeparation_le_sub_sq_of_secondVariationMargin_twoSided
    h₁ h₂ hp
  intro s hs
  have hforce := hconv.inner_gradient_sub_lower
    (hregion s hs).1 (hregion s hs).2
  have hmomentum' := hmomentum s hs
  have hsep := mul_le_mul_of_nonneg_left (hseparation s hs) hκ
  nlinarith

/-- Relative form of the quantitative exact-flow estimate. If squared
separation stays above a fraction `θ` of its initial value, the output has the
explicit multiplicative factor `1 - κ θ t²`. This is the form consumed by the
aligned-cost component of the multinomial-coupling budgets. -/
theorem LocalStrongConvexity.squaredEuclideanSeparation_le_mul
    {gradient : Position ι → Position ι} {S : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient S α)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (h₁ : IsHamiltonianCurve gradient q₁ p₁)
    (h₂ : IsHamiltonianCurve gradient q₂ p₂)
    {κ θ t : ℝ} (hκ : 0 ≤ κ) (ht : 0 ≤ t) (hp : p₁ 0 = p₂ 0)
    (hregion : ∀ s ∈ Icc (0 : ℝ) t, q₁ s ∈ S ∧ q₂ s ∈ S)
    (hmomentum : ∀ s ∈ Icc (0 : ℝ) t,
      squaredEuclideanNorm (p₁ s - p₂ s) ≤
        (α - κ) * squaredEuclideanNorm (q₁ s - q₂ s))
    (hseparation : ∀ s ∈ Icc (0 : ℝ) t,
      θ * squaredEuclideanNorm (q₁ 0 - q₂ 0) ≤
        squaredEuclideanNorm (q₁ s - q₂ s)) :
    squaredEuclideanNorm (q₁ t - q₂ t) ≤
      (1 - κ * θ * t ^ 2) *
        squaredEuclideanNorm (q₁ 0 - q₂ 0) := by
  have h := hconv.squaredEuclideanSeparation_le_sub_sq h₁ h₂ hκ ht hp
    hregion hmomentum hseparation
  nlinarith

/-- Two-sided relative exact-flow contraction with the same explicit
quadratic factor in the signed integration time. -/
theorem LocalStrongConvexity.squaredEuclideanSeparation_le_mul_twoSided
    {gradient : Position ι → Position ι} {S : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient S α)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (h₁ : IsHamiltonianCurve gradient q₁ p₁)
    (h₂ : IsHamiltonianCurve gradient q₂ p₂)
    {κ θ t : ℝ} (hκ : 0 ≤ κ) (hp : p₁ 0 = p₂ 0)
    (hregion : ∀ s ∈ uIcc (0 : ℝ) t, q₁ s ∈ S ∧ q₂ s ∈ S)
    (hmomentum : ∀ s ∈ uIcc (0 : ℝ) t,
      squaredEuclideanNorm (p₁ s - p₂ s) ≤
        (α - κ) * squaredEuclideanNorm (q₁ s - q₂ s))
    (hseparation : ∀ s ∈ uIcc (0 : ℝ) t,
      θ * squaredEuclideanNorm (q₁ 0 - q₂ 0) ≤
        squaredEuclideanNorm (q₁ s - q₂ s)) :
    squaredEuclideanNorm (q₁ t - q₂ t) ≤
      (1 - κ * θ * t ^ 2) *
        squaredEuclideanNorm (q₁ 0 - q₂ 0) := by
  have h := hconv.squaredEuclideanSeparation_le_sub_sq_twoSided
    h₁ h₂ hκ hp hregion hmomentum hseparation
  nlinarith

/-- Two-sided exact-flow contraction with the relative-momentum premise
derived from global gradient Lipschitzness. It remains enough to supply
uniform upper and lower position-separation bounds and containment in the
strong-convexity region; relative momentum is no longer an independent
analytic hypothesis. -/
theorem LocalStrongConvexity.squaredEuclideanSeparation_le_mul_of_positionBounds
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient S α)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (h₁ : IsHamiltonianCurve gradient q₁ p₁)
    (h₂ : IsHamiltonianCurve gradient q₂ p₂)
    {A κ θ t : ℝ} (hA : 0 ≤ A) (hκ : 0 ≤ κ) (hθ : 0 < θ)
    (hp : p₁ 0 = p₂ 0)
    (hbudget :
      (((Fintype.card ι : ℝ) + 1) * (β : ℝ) * A * |t|) ^ 2 ≤
        (α - κ) * θ)
    (hregion : ∀ s ∈ uIcc (0 : ℝ) t, q₁ s ∈ S ∧ q₂ s ∈ S)
    (hupper : ∀ s ∈ uIcc (0 : ℝ) t,
      euclideanNorm (q₁ s - q₂ s) ≤
        A * euclideanNorm (q₁ 0 - q₂ 0))
    (hlower : ∀ s ∈ uIcc (0 : ℝ) t,
      θ * squaredEuclideanNorm (q₁ 0 - q₂ 0) ≤
        squaredEuclideanNorm (q₁ s - q₂ s)) :
    squaredEuclideanNorm (q₁ t - q₂ t) ≤
      (1 - κ * θ * t ^ 2) *
        squaredEuclideanNorm (q₁ 0 - q₂ 0) := by
  apply hconv.squaredEuclideanSeparation_le_mul_twoSided
    h₁ h₂ hκ hp hregion
  · intro s hs
    have hsub : uIcc (0 : ℝ) s ⊆ uIcc (0 : ℝ) t :=
      uIcc_subset_uIcc_left hs
    have hmom := hreg.squaredEuclideanNorm_momentum_sub_le
      h₁ h₂ hA hp (fun u hu ↦ hupper u (hsub hu))
    have hst : |s| ≤ |t| := by
      simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hs
    have hcoef_nonneg : 0 ≤
        ((Fintype.card ι : ℝ) + 1) * (β : ℝ) * A := by positivity
    have hcoef :
        (((Fintype.card ι : ℝ) + 1) * (β : ℝ) * A * |s|) ^ 2 ≤
          (((Fintype.card ι : ℝ) + 1) * (β : ℝ) * A * |t|) ^ 2 := by
      apply (sq_le_sq₀ (mul_nonneg hcoef_nonneg (abs_nonneg s))
        (mul_nonneg hcoef_nonneg (abs_nonneg t))).mpr
      gcongr
    have hακ : 0 ≤ α - κ := by
      by_contra hneg
      have : (α - κ) * θ < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hθ
      have hleft : 0 ≤
          (((Fintype.card ι : ℝ) + 1) * (β : ℝ) * A * |t|) ^ 2 :=
        sq_nonneg _
      linarith
    have hinit : 0 ≤ squaredEuclideanNorm (q₁ 0 - q₂ 0) :=
      squaredEuclideanNorm_nonneg _
    have hcurrent : 0 ≤ squaredEuclideanNorm (q₁ s - q₂ s) :=
      squaredEuclideanNorm_nonneg _
    calc
      squaredEuclideanNorm (p₁ s - p₂ s) ≤
          (((Fintype.card ι : ℝ) + 1) * (β : ℝ) * A * |s|) ^ 2 *
            squaredEuclideanNorm (q₁ 0 - q₂ 0) := hmom
      _ ≤ (((Fintype.card ι : ℝ) + 1) * (β : ℝ) * A * |t|) ^ 2 *
            squaredEuclideanNorm (q₁ 0 - q₂ 0) := by gcongr
      _ ≤ ((α - κ) * θ) *
            squaredEuclideanNorm (q₁ 0 - q₂ 0) := by gcongr
      _ ≤ (α - κ) * squaredEuclideanNorm (q₁ s - q₂ s) := by
        have := mul_le_mul_of_nonneg_left (hlower s hs) hακ
        nlinarith
  · exact hlower

/-- Two-sided exact-flow contraction from only a uniform upper separation
bound and region containment. The first short-time budget derives a lower
separation factor `(1-δ)²`; the second ensures that the integrated relative
momentum fits inside the strong-convexity margin. -/
theorem LocalStrongConvexity.squaredEuclideanSeparation_le_mul_of_upperBound
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient S α)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (h₁ : IsHamiltonianCurve gradient q₁ p₁)
    (h₂ : IsHamiltonianCurve gradient q₂ p₂)
    {A δ κ t : ℝ} (hA : 0 ≤ A) (hδ : δ < 1) (hκ : 0 ≤ κ)
    (hp : p₁ 0 = p₂ 0)
    (hdisplacementBudget :
      ((Fintype.card ι : ℝ) + 1) ^ 2 * (β : ℝ) * A * |t| ^ 2 ≤ δ)
    (hmomentumBudget :
      (((Fintype.card ι : ℝ) + 1) * (β : ℝ) * A * |t|) ^ 2 ≤
        (α - κ) * (1 - δ) ^ 2)
    (hregion : ∀ s ∈ uIcc (0 : ℝ) t, q₁ s ∈ S ∧ q₂ s ∈ S)
    (hupper : ∀ s ∈ uIcc (0 : ℝ) t,
      euclideanNorm (q₁ s - q₂ s) ≤
        A * euclideanNorm (q₁ 0 - q₂ 0)) :
    squaredEuclideanNorm (q₁ t - q₂ t) ≤
      (1 - κ * (1 - δ) ^ 2 * t ^ 2) *
        squaredEuclideanNorm (q₁ 0 - q₂ 0) := by
  have hθ : 0 < (1 - δ) ^ 2 := sq_pos_of_pos (sub_pos.mpr hδ)
  have hlower := hreg.squaredEuclideanNorm_position_sub_lower
    h₁ h₂ hA hδ.le hp hdisplacementBudget hupper
  exact hconv.squaredEuclideanSeparation_le_mul_of_positionBounds
    hreg h₁ h₂ hA hκ hθ hp hmomentumBudget hregion hupper hlower

/-- Quantitative two-sided exact-flow contraction with every relative-motion
estimate discharged from global gradient Lipschitzness. Apart from the scalar
short-time budgets, the only trajectory hypothesis left is containment in the
local strong-convexity region. -/
theorem LocalStrongConvexity.squaredEuclideanSeparation_le_mul_of_region
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient S α)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (h₁ : IsHamiltonianCurve gradient q₁ p₁)
    (h₂ : IsHamiltonianCurve gradient q₂ p₂)
    {δ κ t : ℝ} (hδ : δ < 1) (hκ : 0 ≤ κ)
    (hp : p₁ 0 = p₂ 0)
    (hdisplacementBudget :
      ((Fintype.card ι : ℝ) + 1) ^ 2 * (β : ℝ) *
          exactFlowPositionStabilityFactor (ι := ι) β t * |t| ^ 2 ≤ δ)
    (hmomentumBudget :
      (((Fintype.card ι : ℝ) + 1) * (β : ℝ) *
          exactFlowPositionStabilityFactor (ι := ι) β t * |t|) ^ 2 ≤
        (α - κ) * (1 - δ) ^ 2)
    (hregion : ∀ s ∈ uIcc (0 : ℝ) t, q₁ s ∈ S ∧ q₂ s ∈ S) :
    squaredEuclideanNorm (q₁ t - q₂ t) ≤
      (1 - κ * (1 - δ) ^ 2 * t ^ 2) *
        squaredEuclideanNorm (q₁ 0 - q₂ 0) := by
  apply hconv.squaredEuclideanSeparation_le_mul_of_upperBound
    hreg h₁ h₂ (exactFlowPositionStabilityFactor_pos β t).le hδ hκ hp
      hdisplacementBudget hmomentumBudget hregion
  exact hreg.euclideanNorm_position_sub_le_on_uIcc h₁ h₂ hp

/-- Exact-flow contraction from explicit buffered initial positions. Absolute
phase growth proves containment of both trajectories, while the remaining
budgets are scalar short-time inequalities. -/
theorem LocalStrongConvexity.squaredEuclideanSeparation_le_mul_of_buffers
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient S α)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (h₁ : IsHamiltonianCurve gradient q₁ p₁)
    (h₂ : IsHamiltonianCurve gradient q₂ p₂)
    {r₁ r₂ δ κ t : ℝ} (hδ : δ < 1) (hκ : 0 ≤ κ)
    (hp : p₁ 0 = p₂ 0)
    (hball₁ : Metric.closedBall (q₁ 0) r₁ ⊆ S)
    (hball₂ : Metric.closedBall (q₂ 0) r₂ ⊆ S)
    (habsolute₁ :
      exactFlowPositionDisplacementBound β gradient (q₁ 0, p₁ 0) t ≤ r₁)
    (habsolute₂ :
      exactFlowPositionDisplacementBound β gradient (q₂ 0, p₂ 0) t ≤ r₂)
    (hdisplacementBudget :
      ((Fintype.card ι : ℝ) + 1) ^ 2 * (β : ℝ) *
          exactFlowPositionStabilityFactor (ι := ι) β t * |t| ^ 2 ≤ δ)
    (hmomentumBudget :
      (((Fintype.card ι : ℝ) + 1) * (β : ℝ) *
          exactFlowPositionStabilityFactor (ι := ι) β t * |t|) ^ 2 ≤
        (α - κ) * (1 - δ) ^ 2) :
    squaredEuclideanNorm (q₁ t - q₂ t) ≤
      (1 - κ * (1 - δ) ^ 2 * t ^ 2) *
        squaredEuclideanNorm (q₁ 0 - q₂ 0) := by
  apply hconv.squaredEuclideanSeparation_le_mul_of_region
    hreg h₁ h₂ hδ hκ hp hdisplacementBudget hmomentumBudget
  intro s hs
  exact ⟨hreg.position_mem_of_closedBall_subset h₁ habsolute₁ hball₁ s hs,
    hreg.position_mem_of_closedBall_subset h₂ habsolute₂ hball₂ s hs⟩

/-- Compact-uniform exact-flow contraction, the continuous-flow analytic core
of Xu et al.'s Lemma 4.2. A compact initial-position core lies inside the
interior of the local strong-convexity region, and the initial phase states
have one common norm bound. Lean constructs a positive symmetric horizon and
uniform contraction parameters that work for every pair of exact curves in
that family. -/
theorem LocalStrongConvexity.exists_uniform_exactFlow_contraction
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient S α)
    {K : Set (Position ι)} (hK : IsCompact K)
    (hKS : K ⊆ interior S) (M : ℝ) :
    ∃ r > 0,
      ∃ cert : ExactFlowHorizonCertificate (ι := ι) β gradient α M r,
      ∀ (q₁ q₂ : ℝ → Position ι) (p₁ p₂ : ℝ → Momentum ι)
        (_h₁ : IsHamiltonianCurve gradient q₁ p₁)
        (_h₂ : IsHamiltonianCurve gradient q₂ p₂),
        q₁ 0 ∈ K → q₂ 0 ∈ K →
        ‖(q₁ 0, p₁ 0)‖ ≤ M → ‖(q₂ 0, p₂ 0)‖ ≤ M →
        p₁ 0 = p₂ 0 →
        ∀ t, |t| ≤ cert.horizon →
          squaredEuclideanNorm (q₁ t - q₂ t) ≤
            (1 - cert.kappa * (1 - cert.delta) ^ 2 * t ^ 2) *
              squaredEuclideanNorm (q₁ 0 - q₂ 0) := by
  rcases Mcmc.Hamiltonian.IsCompact.exists_pos_forall_closedBall_subset
    hK hKS with ⟨r, hr, hball⟩
  obtain ⟨cert⟩ := exists_exactFlowHorizonCertificate
    (ι := ι) β gradient hconv.alpha_pos hr
  refine ⟨r, hr, cert, ?_⟩
  intro q₁ q₂ p₁ p₂ h₁ h₂ hq₁ hq₂ hM₁ hM₂ hp t ht
  apply hconv.squaredEuclideanSeparation_le_mul_of_buffers
    hreg h₁ h₂ cert.delta_lt_one cert.kappa_pos.le hp
      (hball _ hq₁) (hball _ hq₂)
  · exact (exactFlowPositionDisplacementBound_le_uniform
      β gradient (q₁ 0, p₁ 0) hM₁).trans (cert.containment t ht)
  · exact (exactFlowPositionDisplacementBound_le_uniform
      β gradient (q₂ 0, p₂ 0) hM₂).trans (cert.containment t ht)
  · simpa only [exactFlowRelativeDisplacementRate] using
      cert.relativeDisplacement t ht
  · simpa only [exactFlowRelativeMomentumRate] using
      cert.relativeMomentum t ht

/-- A positive relative second-variation budget gives strict exact-flow
contraction for distinct initial positions. -/
theorem LocalStrongConvexity.squaredEuclideanSeparation_lt
    {gradient : Position ι → Position ι} {S : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient S α)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    (h₁ : IsHamiltonianCurve gradient q₁ p₁)
    (h₂ : IsHamiltonianCurve gradient q₂ p₂)
    {κ θ t : ℝ} (hκ : 0 < κ) (hθ : 0 < θ) (ht : 0 < t)
    (hp : p₁ 0 = p₂ 0) (hne : q₁ 0 ≠ q₂ 0)
    (hregion : ∀ s ∈ Icc (0 : ℝ) t, q₁ s ∈ S ∧ q₂ s ∈ S)
    (hmomentum : ∀ s ∈ Icc (0 : ℝ) t,
      squaredEuclideanNorm (p₁ s - p₂ s) ≤
        (α - κ) * squaredEuclideanNorm (q₁ s - q₂ s))
    (hseparation : ∀ s ∈ Icc (0 : ℝ) t,
      θ * squaredEuclideanNorm (q₁ 0 - q₂ 0) ≤
        squaredEuclideanNorm (q₁ s - q₂ s)) :
    squaredEuclideanNorm (q₁ t - q₂ t) <
      squaredEuclideanNorm (q₁ 0 - q₂ 0) := by
  apply lt_of_le_of_lt
    (hconv.squaredEuclideanSeparation_le_mul h₁ h₂ hκ.le ht.le hp
      hregion hmomentum hseparation)
  have hdist : 0 < squaredEuclideanNorm (q₁ 0 - q₂ 0) :=
    squaredEuclideanNorm_pos (sub_ne_zero.mpr hne)
  have hloss : 0 < κ * θ * t ^ 2 := by positivity
  nlinarith

/-- Pointwise negative second variation of squared separation for two
distinct positions in the strongly convex region with shared momentum. -/
theorem sharedMomentum_secondVariation_neg
    {gradient : Position ι → Position ι} {S : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient S α)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι} {t : ℝ}
    (h₁ : IsHamiltonianCurve gradient q₁ p₁)
    (h₂ : IsHamiltonianCurve gradient q₂ p₂)
    (hq₁ : q₁ t ∈ S) (hq₂ : q₂ t ∈ S)
    (hne : q₁ t ≠ q₂ t) (hp : p₁ t = p₂ t) :
    ∃ second : ℝ,
      HasDerivAt
        (fun s => 2 * euclideanInner (q₁ s - q₂ s) (p₁ s - p₂ s))
        second t ∧ second < 0 := by
  refine ⟨-2 * euclideanInner (q₁ t - q₂ t)
    (gradient (q₁ t) - gradient (q₂ t)),
    hasDerivAt_firstVariation_sharedMomentum h₁ h₂ hp, ?_⟩
  have hpos := hconv.inner_gradient_sub_pos hq₁ hq₂ hne
  nlinarith

/-- Immediately to the right of a shared-momentum time in the strongly convex
region, the first variation of squared separation is strictly negative. -/
theorem eventually_firstVariation_neg_right
    {gradient : Position ι → Position ι} {S : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient S α)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι} {t : ℝ}
    (h₁ : IsHamiltonianCurve gradient q₁ p₁)
    (h₂ : IsHamiltonianCurve gradient q₂ p₂)
    (hq₁ : q₁ t ∈ S) (hq₂ : q₂ t ∈ S)
    (hne : q₁ t ≠ q₂ t) (hp : p₁ t = p₂ t) :
    ∀ᶠ s in 𝓝[>] t,
      2 * euclideanInner (q₁ s - q₂ s) (p₁ s - p₂ s) < 0 := by
  let g : ℝ → ℝ := fun s =>
    2 * euclideanInner (q₁ s - q₂ s) (p₁ s - p₂ s)
  obtain ⟨second, hsecond, hsecond_neg⟩ :=
    sharedMomentum_secondVariation_neg hconv h₁ h₂ hq₁ hq₂ hne hp
  have hderiv_neg : deriv g t < 0 := by
    rw [hsecond.deriv]
    exact hsecond_neg
  have hg_zero : g t = 0 := by
    simp [g, hp]
  have hsign : ∀ᶠ s in 𝓝 t, sign (g s) = sign (t - s) :=
    eventually_nhdsWithin_sign_eq_of_deriv_neg hderiv_neg hg_zero
  have hsign' : ∀ᶠ s in 𝓝[>] t, sign (g s) = sign (t - s) :=
    hsign.filter_mono inf_le_left
  filter_upwards [hsign', self_mem_nhdsWithin] with s hs hts
  have hsign_neg : sign (g s) = -1 := by
    rw [hs, sign_eq_neg_one_iff]
    exact sub_neg.mpr hts
  exact sign_eq_neg_one_iff.mp hsign_neg

/-- Pointwise short-time contraction of squared Euclidean position distance
for exact Hamiltonian curves started with shared momentum. -/
theorem exists_shortTime_squaredEuclideanSeparation_lt
    {gradient : Position ι → Position ι} {S : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient S α)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι} {t : ℝ}
    (h₁ : IsHamiltonianCurve gradient q₁ p₁)
    (h₂ : IsHamiltonianCurve gradient q₂ p₂)
    (hq₁ : q₁ t ∈ S) (hq₂ : q₂ t ∈ S)
    (hne : q₁ t ≠ q₂ t) (hp : p₁ t = p₂ t) :
    ∃ u > t, ∀ s ∈ Ioc t u,
      squaredEuclideanNorm (q₁ s - q₂ s) <
        squaredEuclideanNorm (q₁ t - q₂ t) := by
  let f : ℝ → ℝ := fun s => squaredEuclideanNorm (q₁ s - q₂ s)
  let g : ℝ → ℝ := fun s =>
    2 * euclideanInner (q₁ s - q₂ s) (p₁ s - p₂ s)
  have hf : ∀ s, HasDerivAt f (g s) s := by
    intro s
    exact hasDerivAt_squaredEuclideanSeparation
      (h₁.position_deriv s) (h₂.position_deriv s)
  have hneg : ∀ᶠ s in 𝓝[>] t, g s < 0 :=
    eventually_firstVariation_neg_right hconv h₁ h₂ hq₁ hq₂ hne hp
  obtain ⟨u, htu, hu⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp hneg
  refine ⟨u, htu, ?_⟩
  have hcont : Continuous f :=
    continuous_iff_continuousAt.mpr fun s => (hf s).continuousAt
  have hanti : StrictAntiOn f (Icc t u) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc t u) hcont.continuousOn
    intro s hs
    rw [interior_Icc] at hs
    rw [(hf s).deriv]
    exact hu hs
  intro s hs
  exact hanti (left_mem_Icc.mpr htu.le) ⟨hs.1.le, hs.2⟩ hs.1

end Mcmc.Hamiltonian
