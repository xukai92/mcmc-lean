import Mcmc.Relativistic.GeneralizedLeapfrog
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Finite fixed-point approximations for generalized leapfrog

Xu and Ge state that the two implicit updates are solved by a fixed number of
fixed-point iterations (six in their experiments), but do not specify an
initialization or prove that the finite iterate solves the implicit equations.
This module formalizes the natural incoming-state initialization, identifies
the exact residual obligations, and gives a one-dimensional six-iteration
counterexample: finite iteration need not define a
`GeneralizedLeapfrogSelection`.
-/

namespace Mcmc.Relativistic

open Mcmc.Hamiltonian
open MeasureTheory
open Filter
open Topology

variable {ι : Type*} [Fintype ι]

/-- A uniformly contractive family with jointly continuous update has a
continuous Banach-selected fixed point. This is the parameter-dependence lemma
needed before applying the inverse/implicit-function theorem to exact
generalized-leapfrog solves. -/
theorem continuous_fixedPoint_of_continuous_uniform_contracting
    {X Y : Type*} [PseudoMetricSpace X] [MetricSpace Y] [CompleteSpace Y]
    [Nonempty Y]
    (K : NNReal) (hK : (K : ℝ) < 1) (update : X → Y → Y)
    (hupdate : Continuous fun z : X × Y => update z.1 z.2)
    (hlipschitz : ∀ x, LipschitzWith K (update x)) :
    Continuous fun x =>
      (show ContractingWith K (update x) from ⟨hK, hlipschitz x⟩).fixedPoint
        (update x) := by
  let fixed : X → Y := fun x =>
    (show ContractingWith K (update x) from ⟨hK, hlipschitz x⟩).fixedPoint
      (update x)
  have hfixed (x : X) : update x (fixed x) = fixed x :=
    (show ContractingWith K (update x) from
      ⟨hK, hlipschitz x⟩).fixedPoint_isFixedPt
  change Continuous fixed
  rw [continuous_iff_continuousAt]
  intro x
  rw [Metric.continuousAt_iff]
  intro ε hε
  let c : ℝ := 1 - K
  have hc : 0 < c := by dsimp [c]; linarith
  have hparam : ContinuousAt (fun y => update y (fixed x)) x :=
    hupdate.continuousAt.comp
      (continuousAt_id.prodMk continuousAt_const)
  rw [Metric.continuousAt_iff] at hparam
  obtain ⟨δ, hδ, hcontrol⟩ := hparam (ε * c) (mul_pos hε hc)
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  have htriangle := dist_triangle (fixed y) (update y (fixed x)) (fixed x)
  have hcontract := (hlipschitz y).dist_le_mul (fixed y) (fixed x)
  have hsmall := hcontrol hy
  have hfirst : dist (fixed y) (update y (fixed x)) =
      dist (update y (fixed y)) (update y (fixed x)) := by
    rw [hfixed y]
  rw [hfirst] at htriangle
  rw [hfixed x] at hsmall
  have hbound : dist (fixed y) (fixed x) ≤
      (K : ℝ) * dist (fixed y) (fixed x) + ε * c := by
    exact htriangle.trans (add_le_add hcontract hsmall.le)
  dsimp [c] at hc hbound
  have hdist : 0 ≤ dist (fixed y) (fixed x) := dist_nonneg
  nlinarith

/-- A continuous global inverse of an everywhere nonsingular differentiable
finite-dimensional map is differentiable. This packages the easy direction
of the inverse-function theorem in the form needed by implicit integrators,
where contraction supplies the inverse and its continuity separately. -/
theorem differentiable_of_continuous_leftInverse_of_det_fderiv_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f g : E → E) (hf : Differentiable ℝ f) (hg : Continuous g)
    (hleft : Function.LeftInverse f g)
    (hdet : ∀ x, (fderiv ℝ f x).det ≠ 0) : Differentiable ℝ g := by
  intro x
  let linearEquiv : E ≃ₗ[ℝ] E :=
    (fderiv ℝ f (g x)).toLinearMap.equivOfDetNeZero (hdet (g x))
  let continuousEquiv : E ≃L[ℝ] E :=
    linearEquiv.toContinuousLinearEquiv
  have heq : (continuousEquiv : E →L[ℝ] E) = fderiv ℝ f (g x) := by
    ext v
    rfl
  have hfAt : HasFDerivAt f (continuousEquiv : E →L[ℝ] E) (g x) := by
    rw [heq]
    exact (hf (g x)).hasFDerivAt
  exact (hfAt.of_local_left_inverse hg.continuousAt
    (Filter.Eventually.of_forall hleft)).differentiableAt

/-- Determinants of the derivatives of differentiable global inverse maps
multiply to one at corresponding points. -/
theorem det_fderiv_mul_det_fderiv_of_leftInverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f g : E → E) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hleft : Function.LeftInverse f g) (x : E) :
    (fderiv ℝ f (g x)).det * (fderiv ℝ g x).det = 1 := by
  have hcomp := fderiv_comp (𝕜 := ℝ) (f := g) (g := f) (x := x)
    (hf (g x)) (hg x)
  have hfun : f ∘ g = id := funext hleft
  rw [hfun] at hcomp
  have hdet := congrArg ContinuousLinearMap.det hcomp
  simpa [ContinuousLinearMap.det, LinearMap.det_comp, LinearMap.det_id] using hdet.symm

/-- Determinant multiplicativity specialized to continuous endomorphisms. -/
theorem det_continuousLinearMap_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f g : E →L[ℝ] E) :
    (f.comp g).det = f.det * g.det := by
  change LinearMap.det (f.toLinearMap.comp g.toLinearMap) =
    LinearMap.det f.toLinearMap * LinearMap.det g.toLinearMap
  exact LinearMap.det_comp _ _

/-- Fixed-point update for the implicit first momentum half-step. -/
noncomputable def halfMomentumFixedPointUpdate
    (positionDerivative : PhaseSpace ι → Position ι)
    (ε : ℝ) (z : PhaseSpace ι) (p : Momentum ι) : Momentum ι :=
  z.2 - (ε / 2) • positionDerivative (z.1, p)

/-- Natural finite iteration initialized at the incoming momentum. -/
noncomputable def finiteHalfMomentum
    (positionDerivative : PhaseSpace ι → Position ι)
    (iterations : ℕ) (ε : ℝ) (z : PhaseSpace ι) : Momentum ι :=
  (halfMomentumFixedPointUpdate positionDerivative ε z)^[iterations] z.2

/-- Fixed-point update for the implicit position step after choosing the half
momentum. -/
noncomputable def positionFixedPointUpdate
    (momentumDerivative : PhaseSpace ι → Position ι)
    (ε : ℝ) (q : Position ι) (pHalf : Momentum ι)
    (qNext : Position ι) : Position ι :=
  q + (ε / 2) •
    (momentumDerivative (q, pHalf) + momentumDerivative (qNext, pHalf))

/-- Natural finite position iteration initialized at the incoming position. -/
noncomputable def finiteNextPosition
    (momentumDerivative : PhaseSpace ι → Position ι)
    (iterations : ℕ) (ε : ℝ) (q : Position ι) (pHalf : Momentum ι) :
    Position ι :=
  (positionFixedPointUpdate momentumDerivative ε q pHalf)^[iterations] q

/-- Under a genuine contraction hypothesis, the finite half-momentum
iterations converge to the unique exact implicit solution. This is the
mathematically valid replacement for treating a fixed iteration count as an
exact solve. -/
theorem finiteHalfMomentum_tendsto_fixedPoint
    (positionDerivative : PhaseSpace ι → Position ι)
    (K : NNReal) (ε : ℝ) (z : PhaseSpace ι)
    (hcontract : ContractingWith K
      (halfMomentumFixedPointUpdate positionDerivative ε z)) :
    Tendsto (fun n => finiteHalfMomentum positionDerivative n ε z) atTop
      (𝓝 (hcontract.fixedPoint
        (halfMomentumFixedPointUpdate positionDerivative ε z))) := by
  simpa only [finiteHalfMomentum] using
    hcontract.tendsto_iterate_fixedPoint z.2

/-- A priori geometric error bound for the implicit half-momentum iteration
under the same contraction certificate. -/
theorem dist_finiteHalfMomentum_fixedPoint_le
    (positionDerivative : PhaseSpace ι → Position ι)
    (K : NNReal) (iterations : ℕ) (ε : ℝ) (z : PhaseSpace ι)
    (hcontract : ContractingWith K
      (halfMomentumFixedPointUpdate positionDerivative ε z)) :
    dist (finiteHalfMomentum positionDerivative iterations ε z)
        (hcontract.fixedPoint
          (halfMomentumFixedPointUpdate positionDerivative ε z)) ≤
      dist z.2 (halfMomentumFixedPointUpdate positionDerivative ε z z.2) *
        (K : ℝ) ^ iterations / (1 - K) := by
  simpa only [finiteHalfMomentum] using
    hcontract.apriori_dist_iterate_fixedPoint_le z.2 iterations

/-- Under a contraction hypothesis, the finite position iterations converge
to the unique exact solution of the second implicit equation. -/
theorem finiteNextPosition_tendsto_fixedPoint
    (momentumDerivative : PhaseSpace ι → Position ι)
    (K : NNReal) (ε : ℝ) (q : Position ι) (pHalf : Momentum ι)
    (hcontract : ContractingWith K
      (positionFixedPointUpdate momentumDerivative ε q pHalf)) :
    Tendsto (fun n => finiteNextPosition momentumDerivative n ε q pHalf) atTop
      (𝓝 (hcontract.fixedPoint
        (positionFixedPointUpdate momentumDerivative ε q pHalf))) := by
  simpa only [finiteNextPosition] using
    hcontract.tendsto_iterate_fixedPoint q

/-- A priori geometric error bound for the implicit position iteration. -/
theorem dist_finiteNextPosition_fixedPoint_le
    (momentumDerivative : PhaseSpace ι → Position ι)
    (K : NNReal) (iterations : ℕ) (ε : ℝ)
    (q : Position ι) (pHalf : Momentum ι)
    (hcontract : ContractingWith K
      (positionFixedPointUpdate momentumDerivative ε q pHalf)) :
    dist (finiteNextPosition momentumDerivative iterations ε q pHalf)
        (hcontract.fixedPoint
          (positionFixedPointUpdate momentumDerivative ε q pHalf)) ≤
      dist q (positionFixedPointUpdate momentumDerivative ε q pHalf q) *
        (K : ℝ) ^ iterations / (1 - K) := by
  simpa only [finiteNextPosition] using
    hcontract.apriori_dist_iterate_fixedPoint_le q iterations

/-- Contraction certificates for both implicit equations at every incoming
state and step size.  This is sufficient to construct an exact generalized
leapfrog solution; measurability and volume preservation of the resulting
state-dependent fixed-point map remain separate analytic obligations. -/
structure ContractiveGeneralizedLeapfrogSolver
    (positionDerivative momentumDerivative : PhaseSpace ι → Position ι) where
  halfRate : ℝ → PhaseSpace ι → NNReal
  halfContracting : ∀ ε z, ContractingWith (halfRate ε z)
    (halfMomentumFixedPointUpdate positionDerivative ε z)
  positionRate : ℝ → Position ι → Momentum ι → NNReal
  positionContracting : ∀ ε q pHalf,
    ContractingWith (positionRate ε q pHalf)
      (positionFixedPointUpdate momentumDerivative ε q pHalf)

/-- Contraction data at one fixed step size. Unlike the global solver above,
this is usable for genuinely nonseparable Hamiltonians whose fixed-point maps
contract only under a step-size restriction. -/
structure ContractiveGeneralizedLeapfrogSolverAt
    (positionDerivative momentumDerivative : PhaseSpace ι → Position ι)
    (ε : ℝ) where
  halfRate : PhaseSpace ι → NNReal
  halfContracting : ∀ z, ContractingWith (halfRate z)
    (halfMomentumFixedPointUpdate positionDerivative ε z)
  positionRate : Position ι → Momentum ι → NNReal
  positionContracting : ∀ q pHalf,
    ContractingWith (positionRate q pHalf)
      (positionFixedPointUpdate momentumDerivative ε q pHalf)

/-- Contraction rate induced by a global slice-Lipschitz bound and one half
step. -/
noncomputable def generalizedLeapfrogSliceRate (ε : ℝ) (L : NNReal) : NNReal :=
  ⟨|ε / 2| * L, mul_nonneg (abs_nonneg _) L.2⟩

theorem halfMomentum_contracting_of_lipschitz
    (positionDerivative : PhaseSpace ι → Position ι)
    (ε : ℝ) (L : NNReal)
    (hlipschitz : ∀ q, LipschitzWith L
      (fun p => positionDerivative (q, p)))
    (hstep : |ε / 2| * L < 1) (z : PhaseSpace ι) :
    ContractingWith (generalizedLeapfrogSliceRate ε L)
      (halfMomentumFixedPointUpdate positionDerivative ε z) := by
  constructor
  · exact hstep
  · apply LipschitzWith.of_dist_le_mul
    intro p r
    rw [dist_eq_norm, dist_eq_norm]
    change ‖(z.2 - (ε / 2) • positionDerivative (z.1, p)) -
        (z.2 - (ε / 2) • positionDerivative (z.1, r))‖ ≤
      (|ε / 2| * L) * ‖p - r‖
    rw [show (z.2 - (ε / 2) • positionDerivative (z.1, p)) -
        (z.2 - (ε / 2) • positionDerivative (z.1, r)) =
      -(ε / 2) • (positionDerivative (z.1, p) -
        positionDerivative (z.1, r)) by module,
      norm_smul, Real.norm_eq_abs, abs_neg]
    calc
      |ε / 2| * ‖positionDerivative (z.1, p) -
          positionDerivative (z.1, r)‖ ≤
        |ε / 2| * (L * ‖p - r‖) := by
          gcongr
          exact (hlipschitz z.1).dist_le_mul p r
      _ = _ := by ring

theorem nextPosition_contracting_of_lipschitz
    (momentumDerivative : PhaseSpace ι → Position ι)
    (ε : ℝ) (L : NNReal)
    (hlipschitz : ∀ p, LipschitzWith L
      (fun q => momentumDerivative (q, p)))
    (hstep : |ε / 2| * L < 1) (q : Position ι) (p : Momentum ι) :
    ContractingWith (generalizedLeapfrogSliceRate ε L)
      (positionFixedPointUpdate momentumDerivative ε q p) := by
  constructor
  · exact hstep
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    change ‖(q + (ε / 2) •
        (momentumDerivative (q, p) + momentumDerivative (x, p))) -
      (q + (ε / 2) •
        (momentumDerivative (q, p) + momentumDerivative (y, p)))‖ ≤
      (|ε / 2| * L) * ‖x - y‖
    rw [show (q + (ε / 2) •
        (momentumDerivative (q, p) + momentumDerivative (x, p))) -
      (q + (ε / 2) •
        (momentumDerivative (q, p) + momentumDerivative (y, p))) =
      (ε / 2) • (momentumDerivative (x, p) -
        momentumDerivative (y, p)) by module,
      norm_smul, Real.norm_eq_abs]
    calc
      |ε / 2| * ‖momentumDerivative (x, p) -
          momentumDerivative (y, p)‖ ≤
        |ε / 2| * (L * ‖x - y‖) := by
          gcongr
          exact (hlipschitz p).dist_le_mul x y
      _ = _ := by ring

/-- Global slice-Lipschitz constants construct both exact implicit solves at
a fixed sufficiently small step. This is the client-facing route for the
actual SoftAbs derivative fields once their analytic constants are bounded. -/
noncomputable def contractiveGeneralizedLeapfrogSolverAtOfLipschitz
    (positionDerivative momentumDerivative : PhaseSpace ι → Position ι)
    (ε : ℝ) (positionLipschitz momentumLipschitz : NNReal)
    (hposition : ∀ q, LipschitzWith positionLipschitz
      (fun p => positionDerivative (q, p)))
    (hmomentum : ∀ p, LipschitzWith momentumLipschitz
      (fun q => momentumDerivative (q, p)))
    (hpositionStep : |ε / 2| * positionLipschitz < 1)
    (hmomentumStep : |ε / 2| * momentumLipschitz < 1) :
    ContractiveGeneralizedLeapfrogSolverAt positionDerivative
      momentumDerivative ε where
  halfRate _ := generalizedLeapfrogSliceRate ε positionLipschitz
  halfContracting := halfMomentum_contracting_of_lipschitz
    positionDerivative ε positionLipschitz hposition hpositionStep
  positionRate _ _ := generalizedLeapfrogSliceRate ε momentumLipschitz
  positionContracting := nextPosition_contracting_of_lipschitz
    momentumDerivative ε momentumLipschitz hmomentum hmomentumStep

/-- Exact half momentum at the certified fixed step size. -/
noncomputable def ContractiveGeneralizedLeapfrogSolverAt.halfMomentum
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    {ε : ℝ}
    (solver : ContractiveGeneralizedLeapfrogSolverAt positionDerivative
      momentumDerivative ε) (z : PhaseSpace ι) : Momentum ι :=
  (solver.halfContracting z).fixedPoint
    (halfMomentumFixedPointUpdate positionDerivative ε z)

/-- Exact next position at the certified fixed step size. -/
noncomputable def ContractiveGeneralizedLeapfrogSolverAt.nextPosition
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    {ε : ℝ}
    (solver : ContractiveGeneralizedLeapfrogSolverAt positionDerivative
      momentumDerivative ε) (z : PhaseSpace ι) : Position ι :=
  (solver.positionContracting z.1 (solver.halfMomentum z)).fixedPoint
    (positionFixedPointUpdate momentumDerivative ε z.1
      (solver.halfMomentum z))

/-- Complete phase point returned by the two exact fixed-step solves. -/
noncomputable def ContractiveGeneralizedLeapfrogSolverAt.step
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    {ε : ℝ}
    (solver : ContractiveGeneralizedLeapfrogSolverAt positionDerivative
      momentumDerivative ε) (z : PhaseSpace ι) : PhaseSpace ι :=
  let pHalf := solver.halfMomentum z
  let qNext := solver.nextPosition z
  (qNext, pHalf - (ε / 2) • positionDerivative (qNext, pHalf))

/-- A fixed-step contraction solve satisfies all generalized-leapfrog
equations exactly. -/
theorem ContractiveGeneralizedLeapfrogSolverAt.satisfies
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    {ε : ℝ}
    (solver : ContractiveGeneralizedLeapfrogSolverAt positionDerivative
      momentumDerivative ε) (z : PhaseSpace ι) :
    GeneralizedLeapfrogEquations positionDerivative momentumDerivative ε z
      (solver.halfMomentum z) (solver.step z) := by
  exact ⟨(solver.halfContracting z).fixedPoint_isFixedPt.symm,
    (solver.positionContracting z.1
      (solver.halfMomentum z)).fixedPoint_isFixedPt.symm, rfl⟩

/-- The fixed-step solution is unique. -/
theorem ContractiveGeneralizedLeapfrogSolverAt.unique
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    {ε : ℝ}
    (solver : ContractiveGeneralizedLeapfrogSolverAt positionDerivative
      momentumDerivative ε) (z : PhaseSpace ι) (pHalf : Momentum ι)
    (zNext : PhaseSpace ι)
    (h : GeneralizedLeapfrogEquations positionDerivative momentumDerivative
      ε z pHalf zNext) :
    pHalf = solver.halfMomentum z ∧ zNext = solver.step z := by
  rcases h with ⟨hp, hq, hpNext⟩
  have hpEq := (solver.halfContracting z).fixedPoint_unique hp.symm
  subst pHalf
  have hqEq := (solver.positionContracting z.1
    (solver.halfMomentum z)).fixedPoint_unique hq.symm
  constructor
  · rfl
  · apply Prod.ext
    · exact hqEq
    · change zNext.2 = solver.halfMomentum z - (ε / 2) •
        positionDerivative (solver.nextPosition z, solver.halfMomentum z)
      rw [hpNext, hqEq]
      rfl

/-- The exact contraction-selected solve at `-ε` is the inverse of the solve
at `ε`, provided both fixed-step certificates are available. -/
theorem ContractiveGeneralizedLeapfrogSolverAt.step_neg_step
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    {ε : ℝ}
    (forward : ContractiveGeneralizedLeapfrogSolverAt positionDerivative
      momentumDerivative ε)
    (backward : ContractiveGeneralizedLeapfrogSolverAt positionDerivative
      momentumDerivative (-ε)) (z : PhaseSpace ι) :
    backward.step (forward.step z) = z := by
  let pHalf := forward.halfMomentum z
  have hforward := forward.satisfies z
  rcases hforward with ⟨hp, hq, hpNext⟩
  have hreverse : GeneralizedLeapfrogEquations positionDerivative
      momentumDerivative (-ε) (forward.step z) pHalf z := by
    constructor
    · dsimp only [pHalf]
      ext i
      have hi := congrFun hpNext i
      simp only [Pi.sub_apply, Pi.smul_apply, neg_div,
        smul_eq_mul] at hi ⊢
      linarith
    constructor
    · dsimp only [pHalf]
      ext i
      have hi := congrFun hq i
      simp only [Pi.add_apply, Pi.smul_apply, neg_div,
        smul_eq_mul] at hi ⊢
      linarith
    · dsimp only [pHalf]
      ext i
      have hi := congrFun hp i
      simp only [Pi.sub_apply, Pi.smul_apply, neg_div,
        smul_eq_mul] at hi ⊢
      linarith
  exact (backward.unique (forward.step z) pHalf z hreverse).2.symm

/-- Contraction certificates may carry different proof data, but their exact
selected steps agree because the implicit solution is unique. -/
theorem ContractiveGeneralizedLeapfrogSolverAt.step_eq
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    {ε : ℝ}
    (first second : ContractiveGeneralizedLeapfrogSolverAt positionDerivative
      momentumDerivative ε) : first.step = second.step := by
  funext z
  exact (first.unique z (second.halfMomentum z) (second.step z)
    (second.satisfies z)).2.symm

/-- A pair of certified opposite-step solves are mutual inverses. -/
theorem ContractiveGeneralizedLeapfrogSolverAt.step_bijective
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    {ε : ℝ}
    (forward : ContractiveGeneralizedLeapfrogSolverAt positionDerivative
      momentumDerivative ε)
    (backward : ContractiveGeneralizedLeapfrogSolverAt positionDerivative
      momentumDerivative (-ε)) : Function.Bijective forward.step := by
  have hleft : Function.LeftInverse backward.step forward.step :=
    forward.step_neg_step backward
  let forward' : ContractiveGeneralizedLeapfrogSolverAt positionDerivative
      momentumDerivative (-(-ε)) := by
    rw [neg_neg]
    exact forward
  have hforward' : forward'.step = forward.step := by
    apply funext
    intro z
    have hsatisfies : GeneralizedLeapfrogEquations positionDerivative
        momentumDerivative ε z (forward'.halfMomentum z) (forward'.step z) := by
      simpa only [neg_neg] using forward'.satisfies z
    exact (forward.unique z (forward'.halfMomentum z) (forward'.step z)
      hsatisfies).2
  have hright : Function.RightInverse backward.step forward.step := by
    rw [← hforward']
    exact backward.step_neg_step forward'
  exact ⟨hleft.injective, hright.surjective⟩

/-- A genuinely nonseparable bilinear Hamiltonian derivative:
`∂H/∂q = a p`. -/
def bilinearPositionDerivative (a : ℝ) : PhaseSpace ι → Position ι :=
  fun z => a • z.2

/-- The companion derivative `∂H/∂p = a q`. Both implicit equations therefore
depend on their unknowns. -/
def bilinearMomentumDerivative (a : ℝ) : PhaseSpace ι → Position ι :=
  fun z => a • z.1

/-- Exact Lipschitz rate of both bilinear fixed-point maps. -/
noncomputable def bilinearFixedPointRate (a ε : ℝ) : NNReal :=
  ⟨|ε / 2 * a|, abs_nonneg _⟩

theorem bilinear_halfMomentum_contracting (a ε : ℝ)
    (hstep : |ε / 2 * a| < 1) (z : PhaseSpace ι) :
    ContractingWith (bilinearFixedPointRate a ε)
      (halfMomentumFixedPointUpdate (bilinearPositionDerivative a) ε z) := by
  constructor
  · exact hstep
  · apply LipschitzWith.of_dist_le_mul
    intro p q
    rw [dist_eq_norm, dist_eq_norm]
    change ‖(z.2 - (ε / 2) • a • p) -
        (z.2 - (ε / 2) • a • q)‖ ≤
      (bilinearFixedPointRate a ε : ℝ) * ‖p - q‖
    change ‖(z.2 - (ε / 2) • a • p) -
        (z.2 - (ε / 2) • a • q)‖ ≤ |ε / 2 * a| * ‖p - q‖
    rw [show (z.2 - (ε / 2) • a • p) -
        (z.2 - (ε / 2) • a • q) =
      -(ε / 2 * a) • (p - q) by module]
    norm_num [norm_smul, abs_mul, abs_div]

theorem bilinear_nextPosition_contracting (a ε : ℝ)
    (hstep : |ε / 2 * a| < 1) (q : Position ι) (p : Momentum ι) :
    ContractingWith (bilinearFixedPointRate a ε)
      (positionFixedPointUpdate (bilinearMomentumDerivative a) ε q p) := by
  constructor
  · exact hstep
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    change ‖(q + (ε / 2) • (a • q + a • x)) -
        (q + (ε / 2) • (a • q + a • y))‖ ≤
      (bilinearFixedPointRate a ε : ℝ) * ‖x - y‖
    change ‖(q + (ε / 2) • (a • q + a • x)) -
        (q + (ε / 2) • (a • q + a • y))‖ ≤
      |ε / 2 * a| * ‖x - y‖
    rw [show (q + (ε / 2) • (a • q + a • x)) -
        (q + (ε / 2) • (a • q + a • y)) =
      (ε / 2 * a) • (x - y) by module]
    norm_num [norm_smul, abs_mul, abs_div]

/-- Concrete exact implicit solver for the bilinear nonseparable Hamiltonian,
valid precisely in the natural contraction regime `|εa/2| < 1`. -/
noncomputable def bilinearContractiveSolverAt (a ε : ℝ)
    (hstep : |ε / 2 * a| < 1) :
    ContractiveGeneralizedLeapfrogSolverAt
      (bilinearPositionDerivative (ι := ι) a)
      (bilinearMomentumDerivative (ι := ι) a) ε where
  halfRate _ := bilinearFixedPointRate a ε
  halfContracting := bilinear_halfMomentum_contracting a ε hstep
  positionRate _ _ := bilinearFixedPointRate a ε
  positionContracting := bilinear_nextPosition_contracting a ε hstep

/-- Closed-form half momentum for the bilinear implicit equation. -/
noncomputable def bilinearExactHalfMomentum (a ε : ℝ)
    (z : PhaseSpace ι) : Momentum ι :=
  (1 / (1 + ε / 2 * a)) • z.2

/-- Closed-form phase map selected by the bilinear implicit solver. -/
noncomputable def bilinearExactStep (a ε : ℝ)
    (z : PhaseSpace ι) : PhaseSpace ι :=
  (((1 + ε / 2 * a) / (1 - ε / 2 * a)) • z.1,
    ((1 - ε / 2 * a) / (1 + ε / 2 * a)) • z.2)

theorem bilinearContractiveSolverAt_halfMomentum_eq (a ε : ℝ)
    (hstep : |ε / 2 * a| < 1) (z : PhaseSpace ι) :
    (bilinearContractiveSolverAt (ι := ι) a ε hstep).halfMomentum z =
      bilinearExactHalfMomentum a ε z := by
  rw [ContractiveGeneralizedLeapfrogSolverAt.halfMomentum]
  symm
  apply (bilinear_halfMomentum_contracting (ι := ι) a ε hstep z).fixedPoint_unique
  have hdenom : 1 + ε / 2 * a ≠ 0 := by
    have := (abs_lt.mp hstep).1
    linarith
  have hscalar :
      1 - (ε / 2 * a) * (1 / (1 + ε / 2 * a)) =
        1 / (1 + ε / 2 * a) := by
    have hdenom' : 2 + ε * a ≠ 0 := by
      intro hzero
      apply hdenom
      linarith
    field_simp [hdenom']
    ring
  ext i
  simp only [halfMomentumFixedPointUpdate, bilinearPositionDerivative,
    bilinearExactHalfMomentum, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  change z.2 i - ε / 2 *
      (a * ((1 / (1 + ε / 2 * a)) * z.2 i)) =
    (1 / (1 + ε / 2 * a)) * z.2 i
  calc
    _ = (1 - (ε / 2 * a) * (1 / (1 + ε / 2 * a))) * z.2 i := by ring
    _ = _ := by rw [hscalar]

theorem bilinearContractiveSolverAt_nextPosition_eq (a ε : ℝ)
    (hstep : |ε / 2 * a| < 1) (z : PhaseSpace ι) :
    (bilinearContractiveSolverAt (ι := ι) a ε hstep).nextPosition z =
      ((1 + ε / 2 * a) / (1 - ε / 2 * a)) • z.1 := by
  rw [ContractiveGeneralizedLeapfrogSolverAt.nextPosition]
  symm
  apply (bilinear_nextPosition_contracting (ι := ι) a ε hstep z.1
    ((bilinearContractiveSolverAt (ι := ι) a ε hstep).halfMomentum z)).fixedPoint_unique
  have hdenom : 1 - ε / 2 * a ≠ 0 := by
    have := (abs_lt.mp hstep).2
    linarith
  have hscalar :
      1 + (ε / 2 * a) *
          (1 + (1 + ε / 2 * a) / (1 - ε / 2 * a)) =
        (1 + ε / 2 * a) / (1 - ε / 2 * a) := by
    have hdenom' : 2 - ε * a ≠ 0 := by
      intro hzero
      apply hdenom
      linarith
    field_simp [hdenom']
    ring
  ext i
  simp only [positionFixedPointUpdate, bilinearMomentumDerivative,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change z.1 i + ε / 2 *
      (a * z.1 i + a *
        (((1 + ε / 2 * a) / (1 - ε / 2 * a)) * z.1 i)) =
    ((1 + ε / 2 * a) / (1 - ε / 2 * a)) * z.1 i
  calc
    _ = (1 + (ε / 2 * a) *
        (1 + (1 + ε / 2 * a) / (1 - ε / 2 * a))) * z.1 i := by ring
    _ = _ := by rw [hscalar]

/-- The contraction-selected solve agrees exactly with the closed-form
symplectic scaling map. -/
theorem bilinearContractiveSolverAt_step_eq (a ε : ℝ)
    (hstep : |ε / 2 * a| < 1) :
    (bilinearContractiveSolverAt (ι := ι) a ε hstep).step =
      bilinearExactStep a ε := by
  funext z
  apply Prod.ext
  · exact bilinearContractiveSolverAt_nextPosition_eq a ε hstep z
  · rw [ContractiveGeneralizedLeapfrogSolverAt.step,
      bilinearContractiveSolverAt_halfMomentum_eq,
      bilinearContractiveSolverAt_nextPosition_eq]
    ext i
    simp [bilinearPositionDerivative, bilinearExactHalfMomentum,
      bilinearExactStep, Pi.smul_apply]
    field_simp

/-- In every finite dimension the exact bilinear implicit step preserves product phase
volume. This is an analytic theorem about the exact Banach-selected map, not a
finite-difference test of a truncated iteration. -/
theorem bilinearContractiveSolverAt_volumePreserving (a ε : ℝ)
    (hstep : |ε / 2 * a| < 1) :
    MeasurePreserving
      (bilinearContractiveSolverAt (ι := ι) a ε hstep).step
      (phaseVolume : Measure (PhaseSpace ι)) phaseVolume := by
  let r : ℝ := (1 + ε / 2 * a) / (1 - ε / 2 * a)
  let s : ℝ := (1 - ε / 2 * a) / (1 + ε / 2 * a)
  have hr : r ≠ 0 := by
    have hneg := (abs_lt.mp hstep).1
    have hpos := (abs_lt.mp hstep).2
    dsimp [r]
    apply div_ne_zero <;> linarith
  have hs : s ≠ 0 := by
    have hneg := (abs_lt.mp hstep).1
    have hpos := (abs_lt.mp hstep).2
    dsimp [s]
    apply div_ne_zero <;> linarith
  have hrs : r * s = 1 := by
    have hnum : 1 + ε / 2 * a ≠ 0 := by
      have := (abs_lt.mp hstep).1
      linarith
    have hden : 1 - ε / 2 * a ≠ 0 := by
      have := (abs_lt.mp hstep).2
      linarith
    dsimp [r, s]
    rw [div_mul_div_comm]
    convert div_self (mul_ne_zero hnum hden) using 1
    all_goals ring
  rw [bilinearContractiveSolverAt_step_eq a ε hstep]
  refine ⟨by unfold bilinearExactStep; fun_prop, ?_⟩
  change Measure.map (Prod.map (r • ·) (s • ·))
      ((volume : Measure (Position ι)).prod
        (volume : Measure (Momentum ι))) = _
  rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_addHaar_smul (volume : Measure (Position ι)) hr,
    Measure.map_addHaar_smul (volume : Measure (Momentum ι)) hs,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  let d := Module.finrank ℝ (Position ι)
  change (ENNReal.ofReal |(r ^ d)⁻¹| * ENNReal.ofReal |(s ^ d)⁻¹|) •
      ((volume : Measure (Position ι)).prod
        (volume : Measure (Momentum ι))) = phaseVolume
  rw [← ENNReal.ofReal_mul (abs_nonneg ((r ^ d)⁻¹)), ← abs_mul]
  have hinv : (r ^ d)⁻¹ * (s ^ d)⁻¹ = ((r * s) ^ d)⁻¹ := by
    rw [mul_pow, mul_inv_rev]
    exact mul_comm _ _
  rw [hinv, hrs]
  simp [phaseVolume]

/-- Both practical fixed-point loops converge for the concrete bilinear
solver whenever the explicit step-size condition holds. -/
theorem bilinear_finiteHalfMomentum_tendsto (a ε : ℝ)
    (hstep : |ε / 2 * a| < 1) (z : PhaseSpace ι) :
    Tendsto (fun n => finiteHalfMomentum (bilinearPositionDerivative a) n ε z)
      atTop (𝓝 (bilinearExactHalfMomentum a ε z)) := by
  rw [← bilinearContractiveSolverAt_halfMomentum_eq a ε hstep z]
  let solver := bilinearContractiveSolverAt (ι := ι) a ε hstep
  change Tendsto
    (fun n => finiteHalfMomentum (bilinearPositionDerivative a) n ε z) atTop
    (𝓝 ((solver.halfContracting z).fixedPoint
      (halfMomentumFixedPointUpdate (bilinearPositionDerivative a) ε z)))
  exact
    finiteHalfMomentum_tendsto_fixedPoint
      (bilinearPositionDerivative (ι := ι) a)
      (solver.halfRate z) ε z (solver.halfContracting z)

/-- The concrete position loop converges to its closed-form exact position
once the exact half momentum is fixed. -/
theorem bilinear_finiteNextPosition_tendsto (a ε : ℝ)
    (hstep : |ε / 2 * a| < 1) (z : PhaseSpace ι) :
    Tendsto (fun n => finiteNextPosition (bilinearMomentumDerivative a) n ε
      z.1 ((bilinearContractiveSolverAt (ι := ι) a ε hstep).halfMomentum z))
      atTop (𝓝 (((1 + ε / 2 * a) / (1 - ε / 2 * a)) • z.1)) := by
  rw [← bilinearContractiveSolverAt_nextPosition_eq a ε hstep z]
  let solver := bilinearContractiveSolverAt (ι := ι) a ε hstep
  change Tendsto
    (fun n => finiteNextPosition (bilinearMomentumDerivative a) n ε z.1
      (solver.halfMomentum z)) atTop
    (𝓝 ((solver.positionContracting z.1 (solver.halfMomentum z)).fixedPoint
      (positionFixedPointUpdate (bilinearMomentumDerivative a) ε z.1
        (solver.halfMomentum z))))
  exact finiteNextPosition_tendsto_fixedPoint
    (bilinearMomentumDerivative (ι := ι) a)
    (solver.positionRate z.1 (solver.halfMomentum z)) ε z.1
    (solver.halfMomentum z)
    (solver.positionContracting z.1 (solver.halfMomentum z))

/-- Exact first half-momentum obtained from the Banach fixed point selected by
the supplied contraction certificate. -/
noncomputable def ContractiveGeneralizedLeapfrogSolver.halfMomentum
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (solver : ContractiveGeneralizedLeapfrogSolver positionDerivative
      momentumDerivative) (ε : ℝ) (z : PhaseSpace ι) : Momentum ι :=
  (solver.halfContracting ε z).fixedPoint
    (halfMomentumFixedPointUpdate positionDerivative ε z)

/-- Exact implicit position obtained after the exact half-momentum solve. -/
noncomputable def ContractiveGeneralizedLeapfrogSolver.nextPosition
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (solver : ContractiveGeneralizedLeapfrogSolver positionDerivative
      momentumDerivative) (ε : ℝ) (z : PhaseSpace ι) : Position ι :=
  (solver.positionContracting ε z.1 (solver.halfMomentum ε z)).fixedPoint
    (positionFixedPointUpdate momentumDerivative ε z.1
      (solver.halfMomentum ε z))

/-- Exact generalized-leapfrog selection constructed from the two contraction
mapping fixed points and the explicit final momentum update. -/
noncomputable def ContractiveGeneralizedLeapfrogSolver.selection
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (solver : ContractiveGeneralizedLeapfrogSolver positionDerivative
      momentumDerivative) :
    GeneralizedLeapfrogSelection positionDerivative momentumDerivative where
  halfMomentum := solver.halfMomentum
  step ε z :=
    let pHalf := solver.halfMomentum ε z
    let qNext := solver.nextPosition ε z
    (qNext, pHalf - (ε / 2) • positionDerivative (qNext, pHalf))
  satisfies ε z := by
    let pHalf := solver.halfMomentum ε z
    let qNext := solver.nextPosition ε z
    have hpFixed :
        halfMomentumFixedPointUpdate positionDerivative ε z pHalf = pHalf :=
      (solver.halfContracting ε z).fixedPoint_isFixedPt
    have hqFixed :
        positionFixedPointUpdate momentumDerivative ε z.1 pHalf qNext = qNext :=
      (solver.positionContracting ε z.1 pHalf).fixedPoint_isFixedPt
    exact ⟨hpFixed.symm, hqFixed.symm, rfl⟩

/-- The contraction-built generalized-leapfrog solution is the unique solution
of both implicit equations. -/
theorem ContractiveGeneralizedLeapfrogSolver.selection_isUnique
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (solver : ContractiveGeneralizedLeapfrogSolver positionDerivative
      momentumDerivative) : solver.selection.IsUnique := by
  intro ε z pHalf zNext hequations
  rcases hequations with ⟨hp, hq, hpNext⟩
  have hpEq : pHalf = solver.halfMomentum ε z := by
    exact (solver.halfContracting ε z).fixedPoint_unique hp.symm
  subst pHalf
  have hqEq : zNext.1 = solver.nextPosition ε z := by
    exact (solver.positionContracting ε z.1
      (solver.halfMomentum ε z)).fixedPoint_unique hq.symm
  apply And.intro rfl
  apply Prod.ext
  · exact hqEq
  · change zNext.2 = solver.halfMomentum ε z - (ε / 2) •
        positionDerivative (solver.nextPosition ε z,
          solver.halfMomentum ε z)
    rw [hpNext, hqEq]

/-- Remaining analytic obligations for the contraction-built exact solver.
Existence and uniqueness are already consequences of contraction and therefore
are not repeated as assumptions here. -/
structure ContractiveGeneralizedLeapfrogSolver.IsValid
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (solver : ContractiveGeneralizedLeapfrogSolver positionDerivative
      momentumDerivative) : Prop where
  measurable : solver.selection.IsMeasurable
  reversible : solver.selection.IsReversible
  volumePreserving : solver.selection.IsVolumePreserving

/-- A contraction solver plus the three remaining analytic fields supplies the
complete validity certificate consumed by endpoint and multinomial GR-HMC. -/
theorem ContractiveGeneralizedLeapfrogSolver.IsValid.selectionValid
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    {solver : ContractiveGeneralizedLeapfrogSolver positionDerivative
      momentumDerivative} (h : solver.IsValid) : solver.selection.IsValid where
  measurable := h.measurable
  unique := solver.selection_isUnique
  reversible := h.reversible
  volumePreserving := h.volumePreserving

/-- Practical half-momentum iteration converges to the exact contraction-built
solver, rather than becoming exact after an arbitrary fixed iteration count. -/
theorem ContractiveGeneralizedLeapfrogSolver.tendsto_finiteHalfMomentum
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (solver : ContractiveGeneralizedLeapfrogSolver positionDerivative
      momentumDerivative) (ε : ℝ) (z : PhaseSpace ι) :
    Tendsto (fun n => finiteHalfMomentum positionDerivative n ε z) atTop
      (𝓝 (solver.halfMomentum ε z)) := by
  simpa only [ContractiveGeneralizedLeapfrogSolver.halfMomentum] using
    finiteHalfMomentum_tendsto_fixedPoint positionDerivative
      (solver.halfRate ε z) ε z (solver.halfContracting ε z)

/-- With the exact half momentum fixed, practical position iteration converges
to the exact contraction-built position solve. -/
theorem ContractiveGeneralizedLeapfrogSolver.tendsto_finiteNextPosition
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (solver : ContractiveGeneralizedLeapfrogSolver positionDerivative
      momentumDerivative) (ε : ℝ) (z : PhaseSpace ι) :
    Tendsto (fun n => finiteNextPosition momentumDerivative n ε z.1
      (solver.halfMomentum ε z)) atTop (𝓝 (solver.nextPosition ε z)) := by
  simpa only [ContractiveGeneralizedLeapfrogSolver.nextPosition] using
    finiteNextPosition_tendsto_fixedPoint momentumDerivative
      (solver.positionRate ε z.1 (solver.halfMomentum ε z)) ε z.1
      (solver.halfMomentum ε z)
      (solver.positionContracting ε z.1 (solver.halfMomentum ε z))

/-- The practical finite-iteration approximation: perform the two finite
fixed-point loops and then the explicit final momentum half-step. -/
noncomputable def finiteFixedPointGeneralizedLeapfrog
    (positionDerivative momentumDerivative : PhaseSpace ι → Position ι)
    (iterations : ℕ) (ε : ℝ) (z : PhaseSpace ι) :
    Momentum ι × PhaseSpace ι :=
  let pHalf := finiteHalfMomentum positionDerivative iterations ε z
  let qNext := finiteNextPosition momentumDerivative iterations ε z.1 pHalf
  let pNext := pHalf - (ε / 2) • positionDerivative (qNext, pHalf)
  (pHalf, (qNext, pNext))

omit [Fintype ι] in
/-- The finite first implicit loop is measurable in the incoming phase point
when the position derivative is measurable. -/
theorem measurable_finiteHalfMomentum
    {positionDerivative : PhaseSpace ι → Position ι}
    (hposition : Measurable positionDerivative)
    (iterations : ℕ) (ε : ℝ) :
    Measurable (finiteHalfMomentum positionDerivative iterations ε) := by
  induction iterations with
  | zero =>
      change Measurable fun z : PhaseSpace ι => z.2
      exact measurable_snd
  | succ n ih =>
      rw [show finiteHalfMomentum positionDerivative (n + 1) ε = fun z =>
        halfMomentumFixedPointUpdate positionDerivative ε z
          (finiteHalfMomentum positionDerivative n ε z) by
        funext z
        simp only [finiteHalfMomentum, Function.iterate_succ_apply']]
      unfold halfMomentumFixedPointUpdate
      fun_prop

omit [Fintype ι] in
/-- The finite position loop is jointly measurable in its incoming position
and chosen half momentum. -/
theorem measurable_finiteNextPosition
    {momentumDerivative : PhaseSpace ι → Position ι}
    (hmomentum : Measurable momentumDerivative)
    (iterations : ℕ) (ε : ℝ) :
    Measurable fun qp : Position ι × Momentum ι =>
      finiteNextPosition momentumDerivative iterations ε qp.1 qp.2 := by
  induction iterations with
  | zero =>
      simpa [finiteNextPosition] using
        (measurable_fst : Measurable
          (Prod.fst : Position ι × Momentum ι → Position ι))
  | succ n ih =>
      rw [show (fun qp : Position ι × Momentum ι =>
          finiteNextPosition momentumDerivative (n + 1) ε qp.1 qp.2) =
        fun qp => positionFixedPointUpdate momentumDerivative ε qp.1 qp.2
          (finiteNextPosition momentumDerivative n ε qp.1 qp.2) by
        funext qp
        simp only [finiteNextPosition, Function.iterate_succ_apply']]
      unfold positionFixedPointUpdate
      fun_prop

omit [Fintype ι] in
/-- The complete practical finite-iteration generalized-leapfrog update is
measurable whenever both derivative fields are measurable. -/
theorem measurable_finiteFixedPointGeneralizedLeapfrog
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (hposition : Measurable positionDerivative)
    (hmomentum : Measurable momentumDerivative)
    (iterations : ℕ) (ε : ℝ) :
    Measurable (finiteFixedPointGeneralizedLeapfrog positionDerivative
      momentumDerivative iterations ε) := by
  let pHalf : PhaseSpace ι → Momentum ι :=
    finiteHalfMomentum positionDerivative iterations ε
  let qNext : PhaseSpace ι → Position ι := fun z =>
    finiteNextPosition momentumDerivative iterations ε z.1 (pHalf z)
  have hp : Measurable pHalf :=
    measurable_finiteHalfMomentum hposition iterations ε
  have hq : Measurable qNext :=
    (measurable_finiteNextPosition hmomentum iterations ε).comp
      (measurable_fst.prodMk hp)
  rw [show finiteFixedPointGeneralizedLeapfrog positionDerivative
      momentumDerivative iterations ε = fun z =>
      (pHalf z, (qNext z, pHalf z - (ε / 2) •
        positionDerivative (qNext z, pHalf z))) by
    funext z
    rfl]
  fun_prop

omit [Fintype ι] in
/-- A finite approximation satisfies the exact generalized-leapfrog equations
iff the last values returned by both loops are actual fixed points.  The final
explicit momentum update has no residual. -/
theorem finiteFixedPointGeneralizedLeapfrog_satisfies_iff
    (positionDerivative momentumDerivative : PhaseSpace ι → Position ι)
    (iterations : ℕ) (ε : ℝ) (z : PhaseSpace ι) :
    let result := finiteFixedPointGeneralizedLeapfrog
      positionDerivative momentumDerivative iterations ε z
    GeneralizedLeapfrogEquations positionDerivative momentumDerivative
        ε z result.1 result.2 ↔
      result.1 = halfMomentumFixedPointUpdate positionDerivative ε z result.1 ∧
      result.2.1 = positionFixedPointUpdate momentumDerivative
        ε z.1 result.1 result.2.1 := by
  simp only [finiteFixedPointGeneralizedLeapfrog,
    GeneralizedLeapfrogEquations, halfMomentumFixedPointUpdate,
    positionFixedPointUpdate]
  tauto

/-- Exact-residual condition needed before a finite fixed-point implementation
can even be regarded as a selected generalized-leapfrog solution. -/
def FiniteFixedPointIsExact
    (positionDerivative momentumDerivative : PhaseSpace ι → Position ι)
    (iterations : ℕ) : Prop :=
  ∀ ε z,
    let result := finiteFixedPointGeneralizedLeapfrog
      positionDerivative momentumDerivative iterations ε z
    result.1 = halfMomentumFixedPointUpdate positionDerivative ε z result.1 ∧
    result.2.1 = positionFixedPointUpdate momentumDerivative
      ε z.1 result.1 result.2.1

/-- Zero metric residuals are sufficient to discharge the exact finite-solver
obligation. This is the bridge used by backend residual certificates. -/
theorem finiteFixedPointIsExact_of_dist_eq_zero
    (positionDerivative momentumDerivative : PhaseSpace ι → Position ι)
    (iterations : ℕ)
    (hhalf : ∀ ε z,
      let result := finiteFixedPointGeneralizedLeapfrog positionDerivative
        momentumDerivative iterations ε z
      dist result.1
        (halfMomentumFixedPointUpdate positionDerivative ε z result.1) = 0)
    (hposition : ∀ ε z,
      let result := finiteFixedPointGeneralizedLeapfrog positionDerivative
        momentumDerivative iterations ε z
      dist result.2.1
        (positionFixedPointUpdate momentumDerivative ε z.1 result.1 result.2.1) = 0) :
    FiniteFixedPointIsExact positionDerivative momentumDerivative iterations := by
  intro ε z
  exact ⟨dist_eq_zero.mp (hhalf ε z), dist_eq_zero.mp (hposition ε z)⟩

/-- Under an exact-residual proof, the finite implementation becomes a
`GeneralizedLeapfrogSelection`.  Measurability, uniqueness, reversal, and
volume preservation remain the separate fields of `selection.IsValid`. -/
noncomputable def finiteFixedPointSelection
    (positionDerivative momentumDerivative : PhaseSpace ι → Position ι)
    (iterations : ℕ)
    (hexact : FiniteFixedPointIsExact
      positionDerivative momentumDerivative iterations) :
    GeneralizedLeapfrogSelection positionDerivative momentumDerivative where
  halfMomentum ε z := (finiteFixedPointGeneralizedLeapfrog
    positionDerivative momentumDerivative iterations ε z).1
  step ε z := (finiteFixedPointGeneralizedLeapfrog
    positionDerivative momentumDerivative iterations ε z).2
  satisfies ε z :=
    (finiteFixedPointGeneralizedLeapfrog_satisfies_iff
      positionDerivative momentumDerivative iterations ε z).mpr
        (hexact ε z)

omit [Fintype ι] in
/-- Measurability of a finite selected solver follows automatically from
measurability of the two derivative fields; it is not an additional numerical
solver assumption. -/
theorem finiteFixedPointSelection_isMeasurable
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (hposition : Measurable positionDerivative)
    (hmomentum : Measurable momentumDerivative)
    (iterations : ℕ)
    (hexact : FiniteFixedPointIsExact
      positionDerivative momentumDerivative iterations) :
    (finiteFixedPointSelection positionDerivative momentumDerivative
      iterations hexact).IsMeasurable := by
  intro ε
  exact measurable_snd.comp
    (measurable_finiteFixedPointGeneralizedLeapfrog
      hposition hmomentum iterations ε)

/-- Minimal corrected numerical statement for the finite implementation: it
must have zero implicit residual; measurable derivative fields automatically
make the induced step measurable, while uniqueness, time reversal, and volume
preservation remain independent obligations. -/
structure FiniteFixedPointIsValid
    (positionDerivative momentumDerivative : PhaseSpace ι → Position ι)
    (iterations : ℕ) : Prop where
  exact : FiniteFixedPointIsExact
    positionDerivative momentumDerivative iterations
  measurablePositionDerivative : Measurable positionDerivative
  measurableMomentumDerivative : Measurable momentumDerivative
  unique : (finiteFixedPointSelection positionDerivative momentumDerivative
    iterations exact).IsUnique
  reversible : (finiteFixedPointSelection positionDerivative momentumDerivative
    iterations exact).IsReversible
  volumePreserving : (finiteFixedPointSelection positionDerivative
    momentumDerivative iterations exact).IsVolumePreserving

/-- The corrected finite-solver certificate supplies the complete validity
interface consumed by the GR-HMC kernels. -/
theorem FiniteFixedPointIsValid.valid
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    {iterations : ℕ}
    (h : FiniteFixedPointIsValid positionDerivative momentumDerivative
      iterations) :
    (finiteFixedPointSelection positionDerivative momentumDerivative
      iterations h.exact).IsValid where
  measurable := finiteFixedPointSelection_isMeasurable
    h.measurablePositionDerivative h.measurableMomentumDerivative
      iterations h.exact
  unique := h.unique
  reversible := h.reversible
  volumePreserving := h.volumePreserving

section SixIterationCounterexample

/-- Scalar position derivative `∂H/∂q = p` used to expose the finite-iteration
residual. -/
def alternatingPositionDerivative : PhaseSpace Unit → Position Unit :=
  fun z => z.2

/-- Zero momentum derivative keeps the position loop exact, isolating the
failure in the first implicit update. -/
def zeroMomentumDerivative : PhaseSpace Unit → Position Unit := fun _ => 0

/-- Test phase point with zero position and unit momentum. -/
def fixedPointCounterexampleState : PhaseSpace Unit :=
  (0, fun _ => 1)

@[simp]
theorem halfMomentumFixedPointUpdate_counterexample
    (p : Momentum Unit) :
    halfMomentumFixedPointUpdate alternatingPositionDerivative 2
      fixedPointCounterexampleState p = fun i => 1 - p i := by
  funext i
  simp [halfMomentumFixedPointUpdate, alternatingPositionDerivative,
    fixedPointCounterexampleState]

/-- Six iterations, as used in the experiments, return unit momentum, but one
more fixed-point update returns zero.  Hence the returned value is not a
solution of the implicit half-step equation. -/
theorem finiteHalfMomentum_six_not_fixed :
    finiteHalfMomentum alternatingPositionDerivative 6 2
        fixedPointCounterexampleState ≠
      halfMomentumFixedPointUpdate alternatingPositionDerivative 2
        fixedPointCounterexampleState
        (finiteHalfMomentum alternatingPositionDerivative 6 2
          fixedPointCounterexampleState) := by
  intro h
  have hi := congrFun h Unit.unit
  simp only [finiteHalfMomentum, Function.iterate_succ_apply] at hi
  simp only [halfMomentumFixedPointUpdate_counterexample] at hi
  norm_num [fixedPointCounterexampleState] at hi

/-- Consequently the natural six-iteration practical update does not satisfy
the generalized-leapfrog equations in general. -/
theorem finiteFixedPointGeneralizedLeapfrog_six_not_satisfies :
    let result := finiteFixedPointGeneralizedLeapfrog
      alternatingPositionDerivative zeroMomentumDerivative 6 2
      fixedPointCounterexampleState
    ¬ GeneralizedLeapfrogEquations alternatingPositionDerivative
      zeroMomentumDerivative 2 fixedPointCounterexampleState result.1 result.2 := by
  dsimp only
  intro h
  have hfixed :=
    (finiteFixedPointGeneralizedLeapfrog_satisfies_iff
      alternatingPositionDerivative zeroMomentumDerivative 6 2
        fixedPointCounterexampleState).mp h
  exact finiteHalfMomentum_six_not_fixed hfixed.1

/-- The counterexample rules out the corrected zero-residual premise itself,
not merely one downstream reversibility proof. -/
theorem sixIterationCounterexample_not_exact :
    ¬ FiniteFixedPointIsExact alternatingPositionDerivative
      zeroMomentumDerivative 6 := by
  intro hexact
  exact finiteHalfMomentum_six_not_fixed (hexact 2 fixedPointCounterexampleState).1

end SixIterationCounterexample

end Mcmc.Relativistic
