import McmcLean.Relativistic.GeneralizedLeapfrog
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

namespace McmcLean.Relativistic

open McmcLean.Hamiltonian
open Filter
open Topology

variable {ι : Type*} [Fintype ι]

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

end McmcLean.Relativistic
