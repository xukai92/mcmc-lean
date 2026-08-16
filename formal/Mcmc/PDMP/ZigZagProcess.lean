import Mcmc.PDMP.EventSimulation
import Mcmc.PDMP.SemigroupStationarity
import Mcmc.PDMP.StationarySuspension
import Mcmc.PDMP.ZigZag
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Tactic

/-!
# One-dimensional Zig-Zag process semantics

This module instantiates the generic PDMP flow and jump interfaces for the
one-dimensional Zig-Zag state `(position, velocity)`.  It supplies the exact
linear semiflow, deterministic velocity flip, and fixed-event execution
kernel.  Sampling the state-dependent event times remains a separate layer.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory BigOperators

namespace Mcmc.PDMP

/-- Position and two-valued velocity for the one-dimensional Zig-Zag process. -/
abbrev ZigZagState := ℝ × Bool

/-- Equal probability on the two Zig-Zag velocities. -/
noncomputable def zigZagVelocityProbability : Measure Bool :=
  (2 : ENNReal)⁻¹ • Measure.dirac false +
    (2 : ENNReal)⁻¹ • Measure.dirac true

instance zigZagVelocityProbability.instIsProbabilityMeasure :
    IsProbabilityMeasure zigZagVelocityProbability := by
  constructor
  simp only [zigZagVelocityProbability, Measure.add_apply,
    Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.inv_two_add_inv_two

/-- Flipping the two-valued velocity preserves its uniform law. -/
theorem zigZagVelocityProbability_map_not :
    zigZagVelocityProbability.map Bool.not = zigZagVelocityProbability := by
  unfold zigZagVelocityProbability
  rw [Measure.map_add _ _ (by fun_prop), Measure.map_smul,
    Measure.map_smul]
  simp
  ac_rfl

/-- Normalized position--velocity target of the standard-Gaussian Zig-Zag
process. -/
noncomputable def gaussianZigZagTarget : Measure ZigZagState :=
  (gaussianReal 0 1).prod zigZagVelocityProbability

instance gaussianZigZagTarget.instIsProbabilityMeasure :
    IsProbabilityMeasure gaussianZigZagTarget := by
  unfold gaussianZigZagTarget
  infer_instance

/-! ### Smooth weak-generator domain -/

/-- Compactly supported `C¹` Gaussian Zig-Zag generator test, including the
integrability of the full phase-space generator needed for the weak forward
equation. -/
structure GaussianZigZagSmoothTest where
  observable : ℝ → Bool → ℝ
  derivative : ℝ → Bool → ℝ
  hasDerivAt_observable : ∀ q v,
    HasDerivAt (fun x => observable x v) (derivative q v) q
  difference : ℝ → ℝ
  difference_eq : difference =
    fun q => observable q true - observable q false
  contDiff_difference : ContDiff ℝ 1 difference
  compact_difference : HasCompactSupport difference
  generator_integrable : Integrable
    (fun state : ZigZagState =>
      zigZagGenerator id derivative observable state.1 state.2)
    gaussianZigZagTarget

/-- Observable represented by a smooth Zig-Zag generator test. -/
def GaussianZigZagSmoothTest.observe
    (test : GaussianZigZagSmoothTest) : ZigZagState → ℝ :=
  fun state => test.observable state.1 state.2

/-- Generator represented by a smooth Zig-Zag generator test. -/
def GaussianZigZagSmoothTest.generator
    (test : GaussianZigZagSmoothTest) : ZigZagState → ℝ :=
  fun state => zigZagGenerator id test.derivative test.observable
    state.1 state.2

/-- The Gaussian Zig-Zag generator of a compact `C¹` observable placed on one
velocity fiber is automatically integrable. -/
theorem gaussianZigZagGenerator_integrable_ofFiber
    (velocity : Bool) (observable derivative : ℝ → ℝ)
    (hderiv : ∀ q, HasDerivAt observable (derivative q) q)
    (hsmooth : ContDiff ℝ 1 observable)
    (hcompact : HasCompactSupport observable) :
    Integrable
      (fun state : ZigZagState =>
        zigZagGenerator id
          (fun q v => if v = velocity then derivative q else 0)
          (fun q v => if v = velocity then observable q else 0)
          state.1 state.2)
      gaussianZigZagTarget := by
  have hderivative : derivative = deriv observable := by
    funext q
    exact (hderiv q).deriv.symm
  have hcontinuousDerivative : Continuous derivative := by
    rw [hderivative]
    exact hsmooth.continuous_deriv le_rfl
  have hfiber : IsClopen
      {state : ZigZagState | state.2 = velocity} := by
    change IsClopen (Prod.snd ⁻¹' ({velocity} : Set Bool))
    exact (isClopen_discrete _).preimage continuous_snd
  have hfiberFrontier : frontier
      {state : ZigZagState | state.2 = velocity} = ∅ :=
    hfiber.frontier_eq
  have hderivativeFiber : Continuous
      (fun state : ZigZagState =>
        if state.2 = velocity then derivative state.1 else 0) := by
    apply Continuous.if
    · intro state hstate
      rw [hfiberFrontier] at hstate
      exact hstate.elim
    · exact hcontinuousDerivative.comp continuous_fst
    · exact continuous_const
  have hobservableFiber : Continuous
      (fun state : ZigZagState =>
        if state.2 = velocity then observable state.1 else 0) := by
    apply Continuous.if
    · intro state hstate
      rw [hfiberFrontier] at hstate
      exact hstate.elim
    · exact hsmooth.continuous.comp continuous_fst
    · exact continuous_const
  have hflip : Continuous (fun state : ZigZagState =>
      (state.1, !state.2)) := by
    have hnot : Continuous (fun value : Bool => !value) :=
      continuous_of_discreteTopology
    exact continuous_fst.prodMk (hnot.comp continuous_snd)
  have hvelocity : Continuous (fun state : ZigZagState =>
      zigZagVelocity state.2) := by
    have hz : Continuous zigZagVelocity := continuous_of_discreteTopology
    exact hz.comp continuous_snd
  have hcontinuous : Continuous
      (fun state : ZigZagState =>
        zigZagGenerator id
          (fun q v => if v = velocity then derivative q else 0)
          (fun q v => if v = velocity then observable q else 0)
          state.1 state.2) := by
    unfold zigZagGenerator zigZagRate zigZagVelocity
    exact (hvelocity.mul hderivativeFiber).add
      ((continuous_const.max (hvelocity.mul continuous_fst)).mul
        ((hobservableFiber.comp hflip).sub hobservableFiber))
  apply hcontinuous.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (hcompact.prod isCompact_univ)
  intro state hstate
  have hq : state.1 ∉ tsupport observable := by
    simpa using hstate
  have hobs : observable state.1 = 0 := by
    by_contra hne
    exact hq (subset_tsupport _ hne)
  have hderivZero : derivative state.1 = 0 := by
    rw [hderivative, deriv_of_notMem_tsupport hq]
  unfold zigZagGenerator
  simp [hobs, hderivZero]

/-- Embed one compactly supported `C¹` real-line observable into a chosen
velocity fiber. This exposes the fiberwise smooth test family needed for the
remaining regular-measure determination proof on `ℝ × Bool`. Generator
integrability is explicit because it is also a required field of the weak
forward domain. -/
noncomputable def GaussianZigZagSmoothTest.ofFiber
    (velocity : Bool) (observable derivative : ℝ → ℝ)
    (hderiv : ∀ q, HasDerivAt observable (derivative q) q)
    (hsmooth : ContDiff ℝ 1 observable)
    (hcompact : HasCompactSupport observable)
    (hgenerator : Integrable
      (fun state : ZigZagState =>
        zigZagGenerator id
          (fun q v => if v = velocity then derivative q else 0)
          (fun q v => if v = velocity then observable q else 0)
          state.1 state.2)
      gaussianZigZagTarget) : GaussianZigZagSmoothTest where
  observable q v := if v = velocity then observable q else 0
  derivative q v := if v = velocity then derivative q else 0
  hasDerivAt_observable q v := by
    by_cases hv : v = velocity
    · simpa [hv] using hderiv q
    · simpa [hv] using (hasDerivAt_const q (0 : ℝ))
  difference q := if velocity then observable q else -observable q
  difference_eq := by
    funext q
    cases velocity <;> simp
  contDiff_difference := by
    cases velocity with
    | false => simpa using hsmooth.neg
    | true => simpa using hsmooth
  compact_difference := by
    cases velocity with
    | false =>
        change HasCompactSupport (-observable)
        exact hcompact.neg
    | true => simpa using hcompact
  generator_integrable := hgenerator

/-- Fully automatic compact-fiber constructor: compact `C¹` support supplies
the generator-integrability field required by the weak-forward domain. -/
noncomputable def GaussianZigZagSmoothTest.ofFiberCompact
    (velocity : Bool) (observable derivative : ℝ → ℝ)
    (hderiv : ∀ q, HasDerivAt observable (derivative q) q)
    (hsmooth : ContDiff ℝ 1 observable)
    (hcompact : HasCompactSupport observable) : GaussianZigZagSmoothTest :=
  GaussianZigZagSmoothTest.ofFiber velocity observable derivative hderiv
    hsmooth hcompact
    (gaussianZigZagGenerator_integrable_ofFiber velocity observable derivative
      hderiv hsmooth hcompact)

/-- Continuous compact real-line observables admit uniformly close smooth
compact approximants whose support stays inside the original support. This is
the analytic density input for upgrading fiberwise smooth-test equality to
regular-measure equality. -/
theorem exists_contDiff_compactSupport_uniformApprox
    (observable : ℝ → ℝ) (hcontinuous : Continuous observable)
    (hcompact : HasCompactSupport observable)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ smooth : ℝ → ℝ, ContDiff ℝ 1 smooth ∧
      HasCompactSupport smooth ∧
      ∀ q, |smooth q - observable q| < ε := by
  obtain ⟨smooth, hsmooth, hclose, hsupport⟩ :=
    hcontinuous.exists_contDiff_approx 1
      (ε := fun _ => ε) continuous_const (fun _ => hε)
  refine ⟨smooth, hsmooth,
    hcompact.mono' (hsupport.trans (subset_tsupport observable)), ?_⟩
  intro q
  simpa [Real.dist_eq] using hclose q

/-- Finite regular real-line measures are determined by compactly supported
`C¹` test functions. The proof smooths each compact continuous Riesz test
uniformly and controls the two integral errors by total mass. -/
theorem Measure.ext_of_integral_eq_on_contDiff_compactSupport
    (left right : Measure ℝ) [IsFiniteMeasure left] [IsFiniteMeasure right]
    [left.Regular] [right.Regular]
    (heq : ∀ test : ℝ → ℝ, ContDiff ℝ 1 test →
      HasCompactSupport test →
      (∫ q, test q ∂left) = ∫ q, test q ∂right) :
    left = right := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro test
  apply eq_of_abs_sub_le_all
  intro ε hε
  let mass : ℝ := left.real Set.univ + right.real Set.univ
  have hmass : 0 ≤ mass := by
    dsimp [mass]
    positivity
  have hmassOne : 0 < mass + 1 := by linarith
  let tolerance : ℝ := ε / (mass + 1)
  have htolerance : 0 < tolerance := div_pos hε hmassOne
  obtain ⟨smooth, hsmooth, hcompact, hclose⟩ :=
    exists_contDiff_compactSupport_uniformApprox test test.continuous
      test.hasCompactSupport htolerance
  have htestLeft : Integrable test left :=
    test.continuous.integrable_of_hasCompactSupport test.hasCompactSupport
  have htestRight : Integrable test right :=
    test.continuous.integrable_of_hasCompactSupport test.hasCompactSupport
  have hsmoothLeft : Integrable smooth left :=
    hsmooth.continuous.integrable_of_hasCompactSupport hcompact
  have hsmoothRight : Integrable smooth right :=
    hsmooth.continuous.integrable_of_hasCompactSupport hcompact
  have hleft : |(∫ q, test q ∂left) - ∫ q, smooth q ∂left| ≤
      left.real Set.univ * tolerance := by
    rw [← integral_sub htestLeft hsmoothLeft]
    calc
      |∫ q, test q - smooth q ∂left| ≤
          ∫ q, |test q - smooth q| ∂left :=
        abs_integral_le_integral_abs
      _ ≤ ∫ _q, tolerance ∂left := by
        apply integral_mono_ae (htestLeft.sub hsmoothLeft).abs
          (integrable_const tolerance)
        filter_upwards [] with q
        simpa [abs_sub_comm] using (hclose q).le
      _ = left.real Set.univ * tolerance := by
        rw [integral_const]
        simp [smul_eq_mul]
  have hright : |(∫ q, smooth q ∂right) - ∫ q, test q ∂right| ≤
      right.real Set.univ * tolerance := by
    rw [← integral_sub hsmoothRight htestRight]
    calc
      |∫ q, smooth q - test q ∂right| ≤
          ∫ q, |smooth q - test q| ∂right :=
        abs_integral_le_integral_abs
      _ ≤ ∫ _q, tolerance ∂right := by
        apply integral_mono_ae (hsmoothRight.sub htestRight).abs
          (integrable_const tolerance)
        filter_upwards [] with q
        exact (hclose q).le
      _ = right.real Set.univ * tolerance := by
        rw [integral_const]
        simp [smul_eq_mul]
  have hsmoothEq := heq smooth hsmooth hcompact
  have hfirst := abs_sub_le (∫ q, test q ∂left)
    (∫ q, smooth q ∂left) (∫ q, test q ∂right)
  have htotal : |(∫ q, test q ∂left) - ∫ q, test q ∂right| ≤
      mass * tolerance := by
    rw [hsmoothEq] at hfirst hleft
    dsimp [mass]
    nlinarith
  calc
    |(∫ q, test q ∂left) - ∫ q, test q ∂right| ≤
        mass * tolerance := htotal
    _ ≤ (mass + 1) * tolerance := by
      exact mul_le_mul_of_nonneg_right (by linarith) htolerance.le
    _ = ε := by
      dsimp [tolerance]
      field_simp

/-- Position measure carried by one Boolean velocity fiber. -/
noncomputable def zigZagFiberMeasure
    (measure : Measure ZigZagState) (velocity : Bool) : Measure ℝ :=
  (measure.restrict {state | state.2 = velocity}).map Prod.fst

instance zigZagFiberMeasure.instIsFiniteMeasure
    (measure : Measure ZigZagState) [IsFiniteMeasure measure]
    (velocity : Bool) : IsFiniteMeasure (zigZagFiberMeasure measure velocity) := by
  unfold zigZagFiberMeasure
  infer_instance

instance zigZagFiberMeasure.instRegular
    (measure : Measure ZigZagState) [IsFiniteMeasure measure] [measure.Regular]
    (velocity : Bool) : (zigZagFiberMeasure measure velocity).Regular := by
  unfold zigZagFiberMeasure
  infer_instance

/-- Integrating on a fiber is the same as integrating the corresponding
zero-extended observable on the full Zig-Zag state space. -/
theorem integral_zigZagFiberMeasure
    (measure : Measure ZigZagState) [IsFiniteMeasure measure]
    (velocity : Bool) (test : ℝ → ℝ) (htest : Continuous test) :
    (∫ q, test q ∂zigZagFiberMeasure measure velocity) =
      ∫ state, (if state.2 = velocity then test state.1 else 0) ∂measure := by
  let fiber : Set ZigZagState := {state | state.2 = velocity}
  have hfiber : MeasurableSet fiber := by
    change MeasurableSet (Prod.snd ⁻¹' ({velocity} : Set Bool))
    exact (measurableSet_singleton velocity).preimage measurable_snd
  have hstrong : AEStronglyMeasurable test
      (zigZagFiberMeasure measure velocity) :=
    htest.aestronglyMeasurable
  rw [zigZagFiberMeasure, integral_map measurable_fst.aemeasurable hstrong]
  rw [← integral_indicator hfiber]
  apply integral_congr_ae
  filter_upwards [] with state
  by_cases hstate : state ∈ fiber
  · have heq : state.2 = velocity := hstate
    simp [Set.indicator_of_mem hstate, heq]
  · have hne : state.2 ≠ velocity := by simpa [fiber] using hstate
    simp [Set.indicator_of_notMem hstate, hne]

/-- Mapping a fiber position back to its tagged velocity reconstructs the
restricted joint measure exactly. -/
theorem map_zigZagFiberMeasure_embed
    (measure : Measure ZigZagState) (velocity : Bool) :
    (zigZagFiberMeasure measure velocity).map (fun q => (q, velocity)) =
      measure.restrict {state | state.2 = velocity} := by
  let fiber : Set ZigZagState := {state | state.2 = velocity}
  have hfiber : MeasurableSet fiber := by
    change MeasurableSet (Prod.snd ⁻¹' ({velocity} : Set Bool))
    exact (measurableSet_singleton velocity).preimage measurable_snd
  change ((measure.restrict fiber).map Prod.fst).map
      (fun q => (q, velocity)) = measure.restrict fiber
  rw [Measure.map_map (μ := measure.restrict fiber)
    (g := fun q => (q, velocity)) (f := Prod.fst)
    (measurable_id.prodMk measurable_const) measurable_fst]
  calc
    (measure.restrict fiber).map
        ((fun q => (q, velocity)) ∘ Prod.fst) =
      (measure.restrict fiber).map id := by
        apply Measure.map_congr
        filter_upwards [ae_restrict_mem hfiber] with state hstate
        simp [fiber] at hstate
        exact Prod.ext rfl hstate.symm
    _ = measure.restrict fiber := Measure.map_id

/-- The two velocity fibers determine a measure on `ℝ × Bool`. -/
theorem measure_eq_of_zigZagFiberMeasure_eq
    (left right : Measure ZigZagState)
    (hfibers : ∀ velocity,
      zigZagFiberMeasure left velocity = zigZagFiberMeasure right velocity) :
    left = right := by
  have hrestrict : ∀ velocity,
      left.restrict {state | state.2 = velocity} =
        right.restrict {state | state.2 = velocity} := by
    intro velocity
    have hmap := congrArg
      (fun fiber : Measure ℝ => fiber.map (fun q => (q, velocity)))
      (hfibers velocity)
    simpa [map_zigZagFiberMeasure_embed] using hmap
  let falseFiber : Set ZigZagState := {state | state.2 = false}
  have hfalse : MeasurableSet falseFiber := by
    change MeasurableSet (Prod.snd ⁻¹' ({false} : Set Bool))
    exact (measurableSet_singleton false).preimage measurable_snd
  have hcompl : falseFiberᶜ = {state : ZigZagState | state.2 = true} := by
    ext state
    cases state.2 <;> simp [falseFiber]
  rw [← Measure.restrict_add_restrict_compl (μ := left) hfalse,
    ← Measure.restrict_add_restrict_compl (μ := right) hfalse,
    hrestrict false, hcompl, hrestrict true]

@[simp] theorem GaussianZigZagSmoothTest.ofFiber_observe_same
    (velocity : Bool) (observable derivative : ℝ → ℝ)
    (hderiv : ∀ q, HasDerivAt observable (derivative q) q)
    (hsmooth : ContDiff ℝ 1 observable)
    (hcompact : HasCompactSupport observable)
    (hgenerator) (q : ℝ) :
    (GaussianZigZagSmoothTest.ofFiber velocity observable derivative hderiv
      hsmooth hcompact hgenerator).observe (q, velocity) = observable q := by
  simp [GaussianZigZagSmoothTest.observe,
    GaussianZigZagSmoothTest.ofFiber]

@[simp] theorem GaussianZigZagSmoothTest.ofFiber_observe_other
    (velocity other : Bool) (hother : other ≠ velocity)
    (observable derivative : ℝ → ℝ)
    (hderiv : ∀ q, HasDerivAt observable (derivative q) q)
    (hsmooth : ContDiff ℝ 1 observable)
    (hcompact : HasCompactSupport observable)
    (hgenerator) (q : ℝ) :
    (GaussianZigZagSmoothTest.ofFiber velocity observable derivative hderiv
      hsmooth hcompact hgenerator).observe (q, other) = 0 := by
  simp [GaussianZigZagSmoothTest.observe,
    GaussianZigZagSmoothTest.ofFiber, hother]

/-- The derivative-difference identity is derived from the two genuine
observable derivatives; it is not an independent certificate field. -/
theorem GaussianZigZagSmoothTest.derivative_sub_eq_deriv
    (test : GaussianZigZagSmoothTest) (q : ℝ) :
    test.derivative q true - test.derivative q false =
      deriv test.difference q := by
  have h := (test.hasDerivAt_observable q true).sub
    (test.hasDerivAt_observable q false)
  have heq : ((fun x => test.observable x true) -
      fun x => test.observable x false) =
      fun x => test.observable x true - test.observable x false := by
    funext x
    rfl
  rw [heq] at h
  have hd : HasDerivAt test.difference
      (test.derivative q true - test.derivative q false) q := by
    rw [test.difference_eq]
    exact h
  exact hd.deriv.symm

/-- Integration against the equal-sign velocity law averages the two Boolean
values. -/
theorem integral_zigZagVelocityProbability (f : Bool → ℝ) :
    (∫ v, f v ∂zigZagVelocityProbability) =
      (2 : ℝ)⁻¹ * f false + (2 : ℝ)⁻¹ * f true := by
  have hfalse : Integrable f ((2 : ENNReal)⁻¹ • Measure.dirac false) :=
    (integrable_dirac (by simp)).smul_measure (by simp)
  have htrue : Integrable f ((2 : ENNReal)⁻¹ • Measure.dirac true) :=
    (integrable_dirac (by simp)).smul_measure (by simp)
  rw [zigZagVelocityProbability, integral_add_measure hfalse htrue,
    integral_smul_measure, integral_smul_measure]
  simp

/-- Every smooth-core test has zero generator expectation under the full
Gaussian position/equal-velocity target. -/
theorem GaussianZigZagSmoothTest.generator_mean_zero
    (test : GaussianZigZagSmoothTest) :
    (∫ state, test.generator state ∂gaussianZigZagTarget) = 0 := by
  unfold GaussianZigZagSmoothTest.generator
  rw [gaussianZigZagTarget,
    integral_prod _ test.generator_integrable]
  simp_rw [integral_zigZagVelocityProbability]
  have hcore :=
    gaussian_zigZagGenerator_mean_zero_of_contDiff_compactSupport
      test.derivative test.observable test.difference test.difference_eq
      test.contDiff_difference test.compact_difference
      test.derivative_sub_eq_deriv
  have heq : (fun q =>
      (2 : ℝ)⁻¹ * zigZagGenerator id test.derivative test.observable q false +
      (2 : ℝ)⁻¹ * zigZagGenerator id test.derivative test.observable q true) =
      fun q => (2 : ℝ)⁻¹ *
        (∑ v : Bool, zigZagGenerator id test.derivative test.observable q v) := by
    funext q
    rw [Fintype.sum_bool]
    ring
  rw [heq, integral_const_mul, hcore, mul_zero]

/-- Exact linear Zig-Zag motion between velocity-switching events. -/
def zigZagFlow (t : NNReal) (state : ZigZagState) : ZigZagState :=
  (state.1 + (t : ℝ) * zigZagVelocity state.2, state.2)

/-- The linear Zig-Zag motion is a measurable semiflow. -/
noncomputable def zigZagSemiflow : MeasurableSemiflow ZigZagState where
  flow := zigZagFlow
  measurable_flow t := by
    unfold zigZagFlow
    fun_prop
  flow_zero := by
    funext state
    simp [zigZagFlow]
  flow_add := by
    intro t u
    funext state
    apply Prod.ext
    · simp only [zigZagFlow, Function.comp_apply, NNReal.coe_add]
      ring
    · rfl

/-- Joint measurability needed to sample a random inter-event wait. -/
noncomputable def zigZagJointlyMeasurableSemiflow :
    JointlyMeasurableSemiflow ZigZagState where
  toMeasurableSemiflow := zigZagSemiflow
  jointly_measurable_flow := by
    change Measurable (fun p : NNReal × ZigZagState => zigZagFlow p.1 p.2)
    unfold zigZagFlow
    fun_prop

/-- A Zig-Zag event keeps position fixed and flips the velocity sign. -/
def zigZagFlip (state : ZigZagState) : ZigZagState :=
  (state.1, !state.2)

/-- Deterministic Markov kernel for a Zig-Zag velocity switch. -/
noncomputable def zigZagJumpKernel : Kernel ZigZagState ZigZagState :=
  Kernel.deterministic zigZagFlip (by
    unfold zigZagFlip
    fun_prop)

instance zigZagJumpKernel.instIsMarkovKernel :
    IsMarkovKernel zigZagJumpKernel := by
  unfold zigZagJumpKernel
  infer_instance

@[simp] theorem zigZagFlip_involutive (state : ZigZagState) :
    zigZagFlip (zigZagFlip state) = state := by
  rcases state with ⟨q, v⟩
  simp [zigZagFlip]

/-- Kernel for executing a fixed list of Zig-Zag inter-event waits. -/
noncomputable def zigZagExecuteSchedule (waits : List NNReal) :
    Kernel ZigZagState ZigZagState :=
  zigZagSemiflow.executeSchedule zigZagJumpKernel waits

instance zigZagExecuteSchedule.instIsMarkovKernel (waits : List NNReal) :
    IsMarkovKernel (zigZagExecuteSchedule waits) := by
  unfold zigZagExecuteSchedule
  infer_instance

/-- The canonical event intensity evaluated on a Zig-Zag process state. -/
def zigZagStateRate (potentialGradient : ℝ → ℝ)
    (state : ZigZagState) : ℝ :=
  zigZagRate potentialGradient state.1 state.2

theorem zigZagStateRate_nonneg (potentialGradient : ℝ → ℝ)
    (state : ZigZagState) :
    0 ≤ zigZagStateRate potentialGradient state :=
  zigZagRate_nonneg potentialGradient state.1 state.2

/-- State-dependent Zig-Zag jump mechanism in the general thinning
interface. -/
noncomputable def zigZagJumpMechanism (potentialGradient : ℝ → ℝ)
    (hmeasurable : Measurable potentialGradient) : JumpMechanism ZigZagState where
  rate := fun state => ENNReal.ofReal (zigZagStateRate potentialGradient state)
  measurable_rate := by
    unfold zigZagStateRate zigZagRate
    fun_prop
  jump := zigZagJumpKernel
  isMarkov := by infer_instance

/-- Exact homogeneous-clock thinning simulator for a globally bounded
one-dimensional Zig-Zag intensity. -/
noncomputable def zigZagThinnedSimulator
    (potentialGradient : ℝ → ℝ) (hmeasurable : Measurable potentialGradient)
    (clock : HomogeneousClock)
    (hbound : ∀ state, ENNReal.ofReal (zigZagStateRate potentialGradient state) ≤
      clock.rate) : ThinnedFlowSimulator ZigZagState where
  semiflow := zigZagJointlyMeasurableSemiflow
  mechanism := zigZagJumpMechanism potentialGradient hmeasurable
  clock := clock
  rate_le_clock := hbound

/-! ### Exact standard-Gaussian event clock -/

/-- Unit exponential hazard law, represented on nonnegative reals. -/
noncomputable def gaussianZigZagHazardMeasure : Measure NNReal :=
  (HomogeneousClock.mk 1 zero_lt_one).waitMeasure

instance gaussianZigZagHazardMeasure.instIsProbabilityMeasure :
    IsProbabilityMeasure gaussianZigZagHazardMeasure := by
  unfold gaussianZigZagHazardMeasure
  infer_instance

/-- Nonnegative inverse-hazard waiting time for the standard-Gaussian
Zig-Zag process. -/
noncomputable def gaussianZigZagWaitingNNReal
    (state : ZigZagState) (hazard : NNReal) : NNReal :=
  Real.toNNReal
    (gaussianZigZagWaitingTime state.1 state.2 (hazard : ℝ))

theorem measurable_gaussianZigZagWaitingNNReal :
    Measurable (fun input : ZigZagState × NNReal =>
      gaussianZigZagWaitingNNReal input.1 input.2) := by
  unfold gaussianZigZagWaitingNNReal gaussianZigZagWaitingTime
  apply measurable_real_toNNReal.comp
  let a : ZigZagState × NNReal → ℝ := fun input =>
    zigZagVelocity input.1.2 * input.1.1
  have ha : Measurable a := by
    unfold a zigZagVelocity
    fun_prop
  apply Measurable.ite (measurableSet_le measurable_const ha)
  · exact (((ha.pow_const 2).add
      (measurable_const.mul (measurable_coe_nnreal_real.comp measurable_snd))).sqrt).sub ha
  · exact ha.neg.add
      ((measurable_const.mul
        (measurable_coe_nnreal_real.comp measurable_snd)).sqrt)

/-- Deterministic state update driven by one exponential hazard draw. -/
noncomputable def gaussianZigZagEventUpdate
    (state : ZigZagState) (hazard : NNReal) : ZigZagState :=
  zigZagFlip (zigZagFlow (gaussianZigZagWaitingNNReal state hazard) state)

/-- One exact standard-Gaussian Zig-Zag event: draw unit exponential hazard,
invert the integrated rate, flow to that time, and flip velocity. -/
noncomputable def gaussianZigZagEventKernel :
    Kernel ZigZagState ZigZagState :=
  Kernel.map
    (Kernel.prod Kernel.id
      (Kernel.const ZigZagState gaussianZigZagHazardMeasure))
    (fun input => gaussianZigZagEventUpdate input.1 input.2)

instance gaussianZigZagEventKernel.instIsMarkovKernel :
    IsMarkovKernel gaussianZigZagEventKernel := by
  unfold gaussianZigZagEventKernel
  apply Kernel.IsMarkovKernel.map
  have hwait : Measurable (fun input : ZigZagState × NNReal =>
      gaussianZigZagWaitingNNReal input.1 input.2) :=
    measurable_gaussianZigZagWaitingNNReal
  have hvelocity : Measurable (fun input : ZigZagState × NNReal =>
      zigZagVelocity input.1.2) := by
    unfold zigZagVelocity
    fun_prop
  unfold gaussianZigZagEventUpdate zigZagFlip zigZagFlow
  exact ((measurable_fst.comp measurable_fst).add
    (hwait.coe_nnreal_real.mul hvelocity)).prodMk (by fun_prop)

/-- The nonnegative representation of the inverse clock does not alter the
closed-form waiting time. -/
theorem coe_gaussianZigZagWaitingNNReal
    (state : ZigZagState) (hazard : NNReal) :
    (gaussianZigZagWaitingNNReal state hazard : ℝ) =
      gaussianZigZagWaitingTime state.1 state.2 (hazard : ℝ) := by
  unfold gaussianZigZagWaitingNNReal
  rw [Real.coe_toNNReal _
    (gaussianZigZagWaitingTime_nonneg state.1 state.2 hazard.coe_nonneg)]

/-- Every positive hazard draw is inverted exactly by the event kernel's
waiting-time calculation. -/
theorem gaussianZigZagIntegratedRate_waitingNNReal
    (state : ZigZagState) {hazard : NNReal} (hhazard : 0 < hazard) :
    gaussianZigZagIntegratedRate state.1 state.2
      (gaussianZigZagWaitingNNReal state hazard : ℝ) = (hazard : ℝ) := by
  rw [coe_gaussianZigZagWaitingNNReal]
  exact gaussianZigZagIntegratedRate_waitingTime state.1 state.2
    (by exact_mod_cast hhazard)

theorem gaussianZigZagWaitingNNReal_pos
    (state : ZigZagState) {hazard : NNReal} (hhazard : 0 < hazard) :
    0 < gaussianZigZagWaitingNNReal state hazard := by
  rw [← NNReal.coe_pos, coe_gaussianZigZagWaitingNNReal]
  have hnonneg := gaussianZigZagWaitingTime_nonneg
    state.1 state.2 hazard.coe_nonneg
  by_contra hnot
  have hzero : gaussianZigZagWaitingTime state.1 state.2 (hazard : ℝ) = 0 :=
    le_antisymm (le_of_not_gt hnot) hnonneg
  have hinverse := gaussianZigZagIntegratedRate_waitingTime
    state.1 state.2 (by exact_mod_cast hhazard)
  have hzeroRate : gaussianZigZagIntegratedRate state.1 state.2 0 =
      (hazard : ℝ) := by
    calc
      _ = gaussianZigZagIntegratedRate state.1 state.2
          (gaussianZigZagWaitingTime state.1 state.2 (hazard : ℝ)) :=
        congrArg (gaussianZigZagIntegratedRate state.1 state.2) hzero.symm
      _ = _ := hinverse
  have hintegratedZero : gaussianZigZagIntegratedRate state.1 state.2 0 = 0 := by
    let a := zigZagVelocity state.2 * state.1
    by_cases ha : 0 ≤ a
    · simp [gaussianZigZagIntegratedRate, a, ha]
    · have hle : a ≤ 0 := le_of_not_ge ha
      simp [gaussianZigZagIntegratedRate, a, ha, hle]
  have hhazardReal : (hazard : ℝ) ≠ 0 := by exact_mod_cast hhazard.ne'
  exact hhazardReal (hintegratedZero ▸ hzeroRate).symm

/-- Position with the velocity sign folded into it. Along a linear segment it
increases at unit speed. -/
def zigZagSignedPosition (state : ZigZagState) : ℝ :=
  zigZagVelocity state.2 * state.1

/-- Fold the velocity sign into position while retaining the velocity label.
This is an involutive measurable coordinate change. -/
def zigZagSignedCoordinate (state : ZigZagState) : ZigZagState :=
  (zigZagSignedPosition state, state.2)

@[simp] theorem zigZagSignedCoordinate_involutive (state : ZigZagState) :
    zigZagSignedCoordinate (zigZagSignedCoordinate state) = state := by
  rcases state with ⟨position, velocity⟩
  unfold zigZagSignedCoordinate zigZagSignedPosition
  apply Prod.ext
  · change zigZagVelocity velocity *
        (zigZagVelocity velocity * position) = position
    cases velocity <;> norm_num [zigZagVelocity]
  · rfl

/-- Measurable equivalence between physical and signed-position
coordinates. -/
def zigZagSignedCoordinateEquiv : ZigZagState ≃ᵐ ZigZagState where
  toFun := zigZagSignedCoordinate
  invFun := zigZagSignedCoordinate
  left_inv := zigZagSignedCoordinate_involutive
  right_inv := zigZagSignedCoordinate_involutive
  measurable_toFun := show Measurable zigZagSignedCoordinate by
    unfold zigZagSignedCoordinate zigZagSignedPosition zigZagVelocity
    fun_prop
  measurable_invFun := show Measurable zigZagSignedCoordinate by
    unfold zigZagSignedCoordinate zigZagSignedPosition zigZagVelocity
    fun_prop

theorem measurable_zigZagSignedCoordinate :
    Measurable zigZagSignedCoordinate := by
  exact zigZagSignedCoordinateEquiv.measurable

@[simp] theorem zigZagSignedPosition_signedCoordinate
    (state : ZigZagState) :
    zigZagSignedPosition (zigZagSignedCoordinate state) = state.1 := by
  have h := congrArg Prod.fst (zigZagSignedCoordinate_involutive state)
  exact h

/-- Folding the velocity sign into position preserves the normalized
Gaussian/equal-velocity target. -/
theorem gaussianZigZagTarget_map_signedCoordinate :
    gaussianZigZagTarget.map zigZagSignedCoordinate =
      gaussianZigZagTarget := by
  unfold gaussianZigZagTarget zigZagVelocityProbability
  rw [Measure.prod_add,
    Measure.prod_smul_right, Measure.prod_smul_right,
    Measure.map_add _ _ (by
      exact zigZagSignedCoordinateEquiv.measurable),
    Measure.map_smul, Measure.map_smul]
  have hfalse : Measure.map zigZagSignedCoordinate
      ((gaussianReal 0 1).prod (Measure.dirac false)) =
      (gaussianReal 0 1).prod (Measure.dirac false) := by
    rw [Measure.prod_dirac, Measure.map_map
      (g := zigZagSignedCoordinate)
      (f := fun position : ℝ => (position, false))
      zigZagSignedCoordinateEquiv.measurable (by fun_prop)]
    rw [show zigZagSignedCoordinate ∘ (fun position : ℝ =>
        (position, false)) = (fun position => (-position, false)) by
      funext position
      simp [zigZagSignedCoordinate, zigZagSignedPosition, zigZagVelocity]]
    rw [show (fun position : ℝ => (-position, false)) =
        (fun position : ℝ => (position, false)) ∘ (fun position => -position) by
      rfl]
    rw [← Measure.map_map (g := fun position : ℝ => (position, false))
      (f := fun position : ℝ => -position)
      (by fun_prop) (by fun_prop), gaussianReal_map_neg]
    simp only [neg_zero]
  have htrue : Measure.map zigZagSignedCoordinate
      ((gaussianReal 0 1).prod (Measure.dirac true)) =
      (gaussianReal 0 1).prod (Measure.dirac true) := by
    rw [Measure.prod_dirac, Measure.map_map
      (g := zigZagSignedCoordinate)
      (f := fun position : ℝ => (position, true))
      zigZagSignedCoordinateEquiv.measurable (by fun_prop)]
    rw [show zigZagSignedCoordinate ∘ (fun position : ℝ =>
        (position, true)) = (fun position => (position, true)) by
      funext position
      simp [zigZagSignedCoordinate, zigZagSignedPosition, zigZagVelocity]]
  rw [hfalse, htrue]
/-- In signed coordinates every deterministic segment moves right at unit
speed, independently of velocity. -/
theorem zigZagSignedCoordinate_flow (time : NNReal) (state : ZigZagState) :
    zigZagSignedCoordinate (zigZagFlow time state) =
      (zigZagSignedPosition state + (time : ℝ), state.2) := by
  rcases state with ⟨position, velocity⟩
  unfold zigZagSignedCoordinate zigZagSignedPosition zigZagFlow
  apply Prod.ext
  · change zigZagVelocity velocity *
        (position + (time : ℝ) * zigZagVelocity velocity) =
        zigZagVelocity velocity * position + (time : ℝ)
    cases velocity <;> norm_num [zigZagVelocity]
    ring
  · rfl

@[simp] theorem zigZagVelocity_not (velocity : Bool) :
    zigZagVelocity (!velocity) = -zigZagVelocity velocity := by
  cases velocity <;> simp [zigZagVelocity]

@[simp] theorem zigZagVelocity_sq (velocity : Bool) :
    zigZagVelocity velocity ^ 2 = 1 := by
  cases velocity <;> norm_num [zigZagVelocity]

/-- Exact post-event recurrence for the Gaussian clock. Once the signed
position is negative, the next event resets it to `-sqrt (2E)` independently
of its previous magnitude. -/
theorem zigZagSignedPosition_gaussianZigZagEventUpdate
    (state : ZigZagState) (hazard : NNReal) :
    zigZagSignedPosition (gaussianZigZagEventUpdate state hazard) =
      if 0 ≤ zigZagSignedPosition state then
        -Real.sqrt (zigZagSignedPosition state ^ 2 + 2 * (hazard : ℝ))
      else -Real.sqrt (2 * (hazard : ℝ)) := by
  let a := zigZagSignedPosition state
  have hflow (time : ℝ) :
      zigZagVelocity state.2 *
        (state.1 + time * zigZagVelocity state.2) = a + time := by
    unfold a zigZagSignedPosition
    calc
      _ = zigZagVelocity state.2 * state.1 +
          time * zigZagVelocity state.2 ^ 2 := by ring
      _ = zigZagVelocity state.2 * state.1 + time := by
        rw [zigZagVelocity_sq]
        ring
  unfold gaussianZigZagEventUpdate zigZagSignedPosition zigZagFlip zigZagFlow
  rw [show (gaussianZigZagWaitingNNReal state hazard : ℝ) =
      gaussianZigZagWaitingTime state.1 state.2 (hazard : ℝ) from
    coe_gaussianZigZagWaitingNNReal state hazard]
  simp only [zigZagVelocity_not, neg_mul]
  change -(zigZagVelocity state.2 *
      (state.1 + gaussianZigZagWaitingTime state.1 state.2 (hazard : ℝ) *
        zigZagVelocity state.2)) = _
  rw [hflow]
  unfold gaussianZigZagWaitingTime
  change -(a + if 0 ≤ a then Real.sqrt (a ^ 2 + 2 * (hazard : ℝ)) - a
    else -a + Real.sqrt (2 * (hazard : ℝ))) =
      if 0 ≤ a then -Real.sqrt (a ^ 2 + 2 * (hazard : ℝ))
      else -Real.sqrt (2 * (hazard : ℝ))
  split_ifs <;> ring

/-- In signed coordinates, an event maps to an explicit negative square-root
location and flips the retained velocity label. -/
theorem zigZagSignedCoordinate_gaussianZigZagEventUpdate
    (state : ZigZagState) (hazard : NNReal) :
    zigZagSignedCoordinate (gaussianZigZagEventUpdate state hazard) =
      (if 0 ≤ zigZagSignedPosition state then
          -Real.sqrt (zigZagSignedPosition state ^ 2 + 2 * (hazard : ℝ))
        else -Real.sqrt (2 * (hazard : ℝ)), !state.2) := by
  apply Prod.ext
  · exact zigZagSignedPosition_gaussianZigZagEventUpdate state hazard
  · rfl

/-- Canonical Gaussian Zig-Zag generator in signed-position coordinates. Its
transport speed is identically one and its event rate is `max 0 signed`. -/
def gaussianZigZagSignedGenerator
    (derivative observable : ℝ → Bool → ℝ)
    (signed : ℝ) (velocity : Bool) : ℝ :=
  derivative signed velocity + max 0 signed *
    (observable (-signed) (!velocity) - observable signed velocity)

/-- The physical Gaussian Zig-Zag generator is conjugate to the canonical
unit-speed signed-coordinate generator. -/
theorem gaussianZigZagGenerator_signedCoordinate
    (derivative observable : ℝ → Bool → ℝ)
    (state : ZigZagState) :
    zigZagGenerator id
        (fun position velocity => zigZagVelocity velocity *
          derivative (zigZagVelocity velocity * position) velocity)
        (fun position velocity =>
          observable (zigZagVelocity velocity * position) velocity)
        state.1 state.2 =
      gaussianZigZagSignedGenerator derivative observable
        (zigZagSignedPosition state) state.2 := by
  rcases state with ⟨position, velocity⟩
  cases velocity <;>
    simp [zigZagGenerator, zigZagRate, zigZagSignedPosition,
      zigZagVelocity, gaussianZigZagSignedGenerator]

theorem zigZagSignedPosition_gaussianZigZagEventUpdate_neg
    (state : ZigZagState) {hazard : NNReal} (hhazard : 0 < hazard) :
    zigZagSignedPosition (gaussianZigZagEventUpdate state hazard) < 0 := by
  rw [zigZagSignedPosition_gaussianZigZagEventUpdate]
  split_ifs
  · exact neg_lt_zero.mpr (Real.sqrt_pos.2 (by
      have : 0 < (2 : ℝ) * (hazard : ℝ) := by positivity
      nlinarith [sq_nonneg (zigZagSignedPosition state)]))
  · exact neg_lt_zero.mpr (Real.sqrt_pos.2 (by positivity))

/-- From a negative signed position, the next waiting time dominates the
square root of its fresh exponential hazard. -/
theorem sqrt_hazard_le_gaussianZigZagWaitingNNReal_of_signedPosition_neg
    (state : ZigZagState) (hazard : NNReal)
    (hstate : zigZagSignedPosition state < 0) :
    Real.sqrt (2 * (hazard : ℝ)) ≤
      (gaussianZigZagWaitingNNReal state hazard : ℝ) := by
  rw [coe_gaussianZigZagWaitingNNReal]
  unfold gaussianZigZagWaitingTime
  change Real.sqrt (2 * (hazard : ℝ)) ≤
    if 0 ≤ zigZagSignedPosition state then
      Real.sqrt (zigZagSignedPosition state ^ 2 + 2 * (hazard : ℝ)) -
        zigZagSignedPosition state
    else -zigZagSignedPosition state + Real.sqrt (2 * (hazard : ℝ))
  rw [if_neg (not_le.mpr hstate)]
  linarith

/-- Every waiting time after the first genuine event has a fresh positive
`sqrt(2E)` lower bound. This is the deterministic reduction needed for a
future i.i.d.-series nonexplosion proof. -/
theorem sqrt_hazard_le_gaussianZigZagWaitingNNReal_after_event
    (state : ZigZagState) {previousHazard : NNReal}
    (hprevious : 0 < previousHazard) (hazard : NNReal) :
    Real.sqrt (2 * (hazard : ℝ)) ≤
      (gaussianZigZagWaitingNNReal
        (gaussianZigZagEventUpdate state previousHazard) hazard : ℝ) :=
  sqrt_hazard_le_gaussianZigZagWaitingNNReal_of_signedPosition_neg _ _
    (zigZagSignedPosition_gaussianZigZagEventUpdate_neg state hprevious)

theorem gaussianZigZagHazardMeasure_singleton_zero :
    gaussianZigZagHazardMeasure {0} = 0 := by
  unfold gaussianZigZagHazardMeasure HomogeneousClock.waitMeasure
  rw [Measure.map_apply measurable_real_toNNReal
    (MeasurableSet.singleton 0)]
  have hpre : Real.toNNReal ⁻¹' ({0} : Set NNReal) = Set.Iic 0 := by
    ext x
    simp [Real.toNNReal_eq_zero]
  rw [hpre]
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  have hcdf := cdf_expMeasure_eq (r := (1 : ℝ)) zero_lt_one 0
  rw [cdf_eq_real] at hcdf
  norm_num at hcdf
  rcases (ENNReal.toReal_eq_zero_iff _).mp hcdf with hzero | htop
  · exact hzero
  · exact (measure_ne_top (expMeasure (1 : ℝ)) (Set.Iic 0) htop).elim

theorem gaussianZigZagHazardMeasure_positive_ae :
    ∀ᵐ hazard ∂gaussianZigZagHazardMeasure, 0 < hazard := by
  have hne : ∀ᵐ hazard ∂gaussianZigZagHazardMeasure, hazard ≠ 0 := by
    rw [ae_iff]
    rw [show {hazard : NNReal | ¬hazard ≠ 0} = {0} by
      ext hazard
      simp]
    exact gaussianZigZagHazardMeasure_singleton_zero
  filter_upwards [hne] with hazard hhazard
  exact bot_lt_iff_ne_bot.mpr hhazard

theorem gaussianZigZagHazardMeasure_Iic_one_toReal :
    (gaussianZigZagHazardMeasure (Set.Iic 1)).toReal =
      1 - Real.exp (-1) := by
  unfold gaussianZigZagHazardMeasure HomogeneousClock.waitMeasure
  rw [Measure.map_apply measurable_real_toNNReal measurableSet_Iic]
  have hpre : Real.toNNReal ⁻¹' (Set.Iic 1 : Set NNReal) = Set.Iic 1 := by
    ext x
    simp [Real.toNNReal_le_one]
  rw [hpre]
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  have hcdf := cdf_expMeasure_eq (r := (1 : ℝ)) zero_lt_one 1
  rw [cdf_eq_real] at hcdf
  norm_num at hcdf ⊢
  exact hcdf

/-- Closed form of the unit-exponential hazard CDF on `NNReal`. -/
theorem gaussianZigZagHazardMeasure_Iic (time : NNReal) :
    gaussianZigZagHazardMeasure (Set.Iic time) =
      ENNReal.ofReal (1 - Real.exp (-(time : ℝ))) := by
  unfold gaussianZigZagHazardMeasure HomogeneousClock.waitMeasure
  change (Measure.map Real.toNNReal (expMeasure (1 : ℝ)))
    (Set.Iic time) = _
  rw [Measure.map_apply measurable_real_toNNReal measurableSet_Iic]
  have hpre : Real.toNNReal ⁻¹' (Set.Iic time : Set NNReal) =
      Set.Iic (time : ℝ) := by
    ext value
    simp only [Set.mem_preimage, Set.mem_Iic, Real.toNNReal_le_iff_le_coe]
  rw [hpre]
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  have hcdf := cdf_expMeasure_eq (r := (1 : ℝ)) zero_lt_one (time : ℝ)
  rw [cdf_eq_real] at hcdf
  simp only [NNReal.coe_nonneg, if_pos, one_mul] at hcdf
  apply (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal]
  · exact hcdf
  · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr time.coe_nonneg))

/-- Unnormalized memorylessness of the unit-exponential hazard law. Restrict
to clocks strictly larger than `elapsed`, subtract `elapsed`, and the result
is the original law scaled by the survival probability `exp (-elapsed)`. -/
theorem gaussianZigZagHazardMeasure_residual_memoryless
    (elapsed : NNReal) :
    Measure.map (fun hazard : NNReal => hazard - elapsed)
        (gaussianZigZagHazardMeasure.restrict (Set.Ioi elapsed)) =
      ENNReal.ofReal (Real.exp (-(elapsed : ℝ))) •
        gaussianZigZagHazardMeasure := by
  apply Measure.ext_of_Iic
  intro residual
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic,
    Measure.restrict_apply (measurableSet_Iic.preimage (by fun_prop))]
  have hpre :
      (fun hazard : NNReal => hazard - elapsed) ⁻¹' Set.Iic residual ∩
          Set.Ioi elapsed =
        Set.Ioc elapsed (elapsed + residual) := by
    ext hazard
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_Ioi,
      Set.mem_Ioc]
    rw [tsub_le_iff_right]
    simp [add_comm, and_comm]
  rw [hpre]
  have hsubset : Set.Iic elapsed ⊆ Set.Iic (elapsed + residual) :=
    Set.Iic_subset_Iic.mpr (le_add_right le_rfl)
  rw [show Set.Ioc elapsed (elapsed + residual) =
      Set.Iic (elapsed + residual) \ Set.Iic elapsed by
    ext hazard
    simp]
  rw [measure_sdiff hsubset nullMeasurableSet_Iic (measure_ne_top _ _),
    gaussianZigZagHazardMeasure_Iic,
    gaussianZigZagHazardMeasure_Iic]
  rw [Measure.smul_apply]
  simp only [smul_eq_mul]
  rw [gaussianZigZagHazardMeasure_Iic]
  have hexp :
      Real.exp (-((elapsed + residual : NNReal) : ℝ)) =
        Real.exp (-(elapsed : ℝ)) * Real.exp (-(residual : ℝ)) := by
    push_cast
    rw [neg_add_rev, Real.exp_add]
    ac_rfl
  have hnonneg : 0 ≤ 1 - Real.exp (-(elapsed : ℝ)) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr elapsed.coe_nonneg))
  rw [← ENNReal.ofReal_sub _ hnonneg, ← ENNReal.ofReal_mul
    (Real.exp_nonneg (-(elapsed : ℝ)))]
  congr 1
  rw [hexp]
  ring

/-- Survival function of the unit-exponential hazard law. -/
theorem gaussianZigZagHazardMeasure_Ioi (elapsed : NNReal) :
    gaussianZigZagHazardMeasure (Set.Ioi elapsed) =
      ENNReal.ofReal (Real.exp (-(elapsed : ℝ))) := by
  rw [← Set.compl_Iic,
    measure_compl measurableSet_Iic (measure_ne_top _ _),
    measure_univ, gaussianZigZagHazardMeasure_Iic]
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _
    (sub_nonneg.mpr (Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr elapsed.coe_nonneg)))]
  congr 1
  ring

/-- Conditional memorylessness in normalized probability-law form. -/
theorem gaussianZigZagHazardMeasure_conditional_residual
    (elapsed : NNReal) :
    (ENNReal.ofReal (Real.exp (-(elapsed : ℝ))))⁻¹ •
        Measure.map (fun hazard : NNReal => hazard - elapsed)
          (gaussianZigZagHazardMeasure.restrict (Set.Ioi elapsed)) =
      gaussianZigZagHazardMeasure := by
  rw [gaussianZigZagHazardMeasure_residual_memoryless, smul_smul]
  have hne : ENNReal.ofReal (Real.exp (-(elapsed : ℝ))) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  rw [ENNReal.inv_mul_cancel hne ENNReal.ofReal_ne_top, one_smul]

theorem gaussianZigZagHazardMeasure_Ioi_one_pos :
    0 < gaussianZigZagHazardMeasure (Set.Ioi 1) := by
  rw [pos_iff_ne_zero]
  intro hzero
  have hunion : gaussianZigZagHazardMeasure
      (Set.Iic (1 : NNReal) ∪ Set.Ioi 1) =
      gaussianZigZagHazardMeasure (Set.Iic 1) +
        gaussianZigZagHazardMeasure (Set.Ioi 1) :=
    measure_union (Set.disjoint_left.2 fun x hx hy =>
      (not_lt_of_ge (show x ≤ 1 from hx)) (show 1 < x from hy))
      measurableSet_Ioi
  have hfull : gaussianZigZagHazardMeasure (Set.Iic 1) = 1 := by
    rw [Set.Iic_union_Ioi, measure_univ, hzero, add_zero] at hunion
    exact hunion.symm
  have hlt : (gaussianZigZagHazardMeasure (Set.Iic 1)).toReal < 1 := by
    rw [gaussianZigZagHazardMeasure_Iic_one_toReal]
    linarith [Real.exp_pos (-1)]
  rw [hfull] at hlt
  norm_num at hlt

/-- Infinite independent hazard stream used to construct the exact event
sequence. -/
noncomputable def gaussianZigZagHazardSequenceMeasure :
    Measure (ℕ → NNReal) :=
  Measure.infinitePi (fun _ : ℕ => gaussianZigZagHazardMeasure)

instance gaussianZigZagHazardSequenceMeasure.instIsProbabilityMeasure :
    IsProbabilityMeasure gaussianZigZagHazardSequenceMeasure := by
  unfold gaussianZigZagHazardSequenceMeasure
  infer_instance

/-- Removing the first coordinate from the iid hazard stream leaves the same
infinite-product law. -/
theorem gaussianZigZagHazardSequenceMeasure_map_tail :
    gaussianZigZagHazardSequenceMeasure.map
        (fun hazards index => hazards (index + 1)) =
      gaussianZigZagHazardSequenceMeasure := by
  unfold gaussianZigZagHazardSequenceMeasure
  simpa using Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ => gaussianZigZagHazardMeasure)
    (f := fun index : ℕ => index + 1) (by
      intro left right heq
      exact Nat.add_right_cancel heq)

/-- The hazard-stream tail operation is measure preserving. -/
theorem gaussianZigZagHazardSequenceMeasure_preserving_tail :
    MeasurePreserving (fun hazards : ℕ → NNReal =>
      fun index => hazards (index + 1))
      gaussianZigZagHazardSequenceMeasure
      gaussianZigZagHazardSequenceMeasure where
  measurable := by fun_prop
  map_eq := gaussianZigZagHazardSequenceMeasure_map_tail

/-- Two-block index used to split an infinite hazard stream into its head and
tail coordinates. -/
abbrev GaussianZigZagHeadTailIndex : Bool → Type
  | false => PUnit
  | true => ℕ

private def gaussianZigZagHeadTailIndexToNat :
    (block : Bool) → GaussianZigZagHeadTailIndex block → ℕ
  | false, _ => 0
  | true, index => index + 1

/-- The head block represents index zero and the tail block represents the
strictly positive natural indices. -/
def gaussianZigZagHeadTailIndexEquiv :
    (Σ block, GaussianZigZagHeadTailIndex block) ≃ ℕ where
  toFun value := gaussianZigZagHeadTailIndexToNat value.1 value.2
  invFun
    | 0 => ⟨false, PUnit.unit⟩
    | index + 1 => ⟨true, index⟩
  left_inv value := by
    rcases value with ⟨block, index⟩
    cases block
    · change (⟨false, PUnit.unit⟩ :
        Σ block, GaussianZigZagHeadTailIndex block) = ⟨false, index⟩
      cases index
      rfl
    · simp [gaussianZigZagHeadTailIndexToNat]
  right_inv index := by
    cases index <;> simp [gaussianZigZagHeadTailIndexToNat]

/-- Measurable head/tail coordinate map for the iid hazard stream. -/
def gaussianZigZagHazardHeadTail
    (hazards : ℕ → NNReal) : NNReal × (ℕ → NNReal) :=
  (hazards 0, fun index => hazards (index + 1))

/-- Reconstruct an infinite stream from its head and tail. -/
def gaussianZigZagHazardCons
    (headTail : NNReal × (ℕ → NNReal)) : ℕ → NNReal
  | 0 => headTail.1
  | index + 1 => headTail.2 index

theorem measurable_gaussianZigZagHazardCons :
    Measurable gaussianZigZagHazardCons := by
  rw [measurable_pi_iff]
  intro index
  cases index with
  | zero => exact measurable_fst
  | succ index => exact (measurable_pi_apply index).comp measurable_snd

@[simp] theorem gaussianZigZagHazardCons_headTail
    (hazards : ℕ → NNReal) :
    gaussianZigZagHazardCons (gaussianZigZagHazardHeadTail hazards) =
      hazards := by
  funext index
  cases index <;> rfl

theorem measurable_gaussianZigZagHazardHeadTail :
    Measurable gaussianZigZagHazardHeadTail := by
  unfold gaussianZigZagHazardHeadTail
  fun_prop

/-- Reindexing and currying group the iid hazard product into its singleton
head block and infinite tail block. -/
theorem gaussianZigZagHazardSequenceMeasure_map_grouped :
    gaussianZigZagHazardSequenceMeasure.map
        (fun hazards block index => hazards
          (gaussianZigZagHeadTailIndexEquiv ⟨block, index⟩)) =
      Measure.infinitePi (fun block : Bool =>
        Measure.infinitePi (fun _ : GaussianZigZagHeadTailIndex block =>
          gaussianZigZagHazardMeasure)) := by
  let reindex := MeasurableEquiv.piCongrLeft
    (fun _ : (Σ block, GaussianZigZagHeadTailIndex block) => NNReal)
    gaussianZigZagHeadTailIndexEquiv.symm
  let regroup := MeasurableEquiv.piCurry
    (fun block (index : GaussianZigZagHeadTailIndex block) => NNReal)
  rw [show (fun hazards block index => hazards
      (gaussianZigZagHeadTailIndexEquiv ⟨block, index⟩)) =
      regroup ∘ reindex by
    funext hazards block index
    have h := MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : (Σ block, GaussianZigZagHeadTailIndex block) => NNReal)
      gaussianZigZagHeadTailIndexEquiv.symm hazards
      (gaussianZigZagHeadTailIndexEquiv ⟨block, index⟩)
    change hazards (gaussianZigZagHeadTailIndexEquiv ⟨block, index⟩) =
      reindex hazards ⟨block, index⟩
    simpa [reindex] using h.symm]
  rw [← Measure.map_map regroup.measurable reindex.measurable]
  unfold gaussianZigZagHazardSequenceMeasure
  dsimp [reindex]
  rw [Measure.infinitePi_map_piCongrLeft
    (μ := fun _ : (Σ block, GaussianZigZagHeadTailIndex block) =>
      gaussianZigZagHazardMeasure)
    gaussianZigZagHeadTailIndexEquiv.symm]
  dsimp [regroup]
  convert Measure.infinitePi_map_piCurry
    (fun block (index : GaussianZigZagHeadTailIndex block) =>
      gaussianZigZagHazardMeasure) using 1

/-- The first hazard and the remaining hazard stream have the exact product
law. This is the measure-level independence statement needed by first-event
recursion. -/
theorem gaussianZigZagHazardSequenceMeasure_map_headTail :
    gaussianZigZagHazardSequenceMeasure.map
        gaussianZigZagHazardHeadTail =
      gaussianZigZagHazardMeasure.prod
        gaussianZigZagHazardSequenceMeasure := by
  let groupedMeasure := Measure.infinitePi (fun block : Bool =>
    Measure.infinitePi (fun _ : GaussianZigZagHeadTailIndex block =>
      gaussianZigZagHazardMeasure))
  let ungroup := fun grouped :
      (block : Bool) → GaussianZigZagHeadTailIndex block → NNReal =>
    (grouped false PUnit.unit, grouped true)
  have hungroup : Measurable ungroup := by
    unfold ungroup
    fun_prop
  have hfactor : Measure.map ungroup groupedMeasure =
      gaussianZigZagHazardMeasure.prod
        gaussianZigZagHazardSequenceMeasure := by
    symm
    apply Measure.prod_eq
    intro headSet tailSet hhead htail
    rw [Measure.map_apply hungroup (hhead.prod htail)]
    let coordinateSet : (block : Bool) →
        Set (GaussianZigZagHeadTailIndex block → NNReal)
      | false => (fun head => head PUnit.unit) ⁻¹' headSet
      | true => tailSet
    have hpre : ungroup ⁻¹' (headSet ×ˢ tailSet) =
        Set.pi (↑(Finset.univ : Finset Bool)) coordinateSet := by
      ext grouped
      simp [ungroup, coordinateSet, and_comm]
    rw [hpre]
    have hcoordinate : ∀ block, MeasurableSet (coordinateSet block) := by
      intro block
      cases block
      · exact hhead.preimage (measurable_pi_apply PUnit.unit)
      · exact htail
    rw [Measure.infinitePi_pi _ (fun block _ => hcoordinate block)]
    have hheadMeasure :
        Measure.infinitePi (fun _ : PUnit => gaussianZigZagHazardMeasure)
            ((fun head => head PUnit.unit) ⁻¹' headSet) =
          gaussianZigZagHazardMeasure headSet := by
      rw [← Measure.map_apply (measurable_pi_apply PUnit.unit) hhead,
        Measure.infinitePi_map_eval]
    rw [Fintype.prod_bool]
    change gaussianZigZagHazardSequenceMeasure tailSet *
        Measure.infinitePi (fun _ : PUnit => gaussianZigZagHazardMeasure)
          ((fun head => head PUnit.unit) ⁻¹' headSet) = _
    rw [hheadMeasure]
    ac_rfl
  rw [show gaussianZigZagHazardHeadTail = ungroup ∘
      (fun hazards block index => hazards
        (gaussianZigZagHeadTailIndexEquiv ⟨block, index⟩)) by
    funext hazards
    rfl]
  rw [← Measure.map_map hungroup (by fun_prop),
    gaussianZigZagHazardSequenceMeasure_map_grouped]
  exact hfactor

/-- Reconstructing a stream from an independent head and iid tail recovers
the iid hazard-sequence law. -/
theorem gaussianZigZagHazardMeasure_prod_sequence_map_cons :
    Measure.map gaussianZigZagHazardCons
        (gaussianZigZagHazardMeasure.prod
          gaussianZigZagHazardSequenceMeasure) =
      gaussianZigZagHazardSequenceMeasure := by
  rw [← gaussianZigZagHazardSequenceMeasure_map_headTail,
    Measure.map_map measurable_gaussianZigZagHazardCons
      measurable_gaussianZigZagHazardHeadTail]
  rw [show gaussianZigZagHazardCons ∘ gaussianZigZagHazardHeadTail = id by
    funext hazards
    exact gaussianZigZagHazardCons_headTail hazards,
    Measure.map_id]

def gaussianZigZagLargeHazardEvent (index : ℕ) : Set (ℕ → NNReal) :=
  (fun hazards => hazards index) ⁻¹' Set.Ioi (1 : NNReal)

theorem measurableSet_gaussianZigZagLargeHazardEvent (index : ℕ) :
    MeasurableSet (gaussianZigZagLargeHazardEvent index) := by
  unfold gaussianZigZagLargeHazardEvent
  exact (measurableSet_Ioi : MeasurableSet (Set.Ioi (1 : NNReal))).preimage
    (measurable_pi_apply index)

theorem gaussianZigZagHazardSequenceMeasure_largeHazardEvent
    (index : ℕ) :
    gaussianZigZagHazardSequenceMeasure
      (gaussianZigZagLargeHazardEvent index) =
        gaussianZigZagHazardMeasure (Set.Ioi 1) := by
  unfold gaussianZigZagHazardSequenceMeasure
    gaussianZigZagLargeHazardEvent
  have hmap := Measure.infinitePi_map_eval
    (μ := fun _ : ℕ => gaussianZigZagHazardMeasure) index
  calc
    _ = (Measure.map (fun hazards : ℕ → NNReal => hazards index)
        (Measure.infinitePi fun _ : ℕ => gaussianZigZagHazardMeasure))
        (Set.Ioi 1) := by
      rw [Measure.map_apply (by fun_prop) measurableSet_Ioi]
    _ = _ := congrArg (fun measure : Measure NNReal => measure (Set.Ioi 1)) hmap

theorem gaussianZigZagLargeHazardEvent_iIndepSet :
    iIndepSet gaussianZigZagLargeHazardEvent
      gaussianZigZagHazardSequenceMeasure := by
  apply (iIndepSet_iff_meas_biInter
    measurableSet_gaussianZigZagLargeHazardEvent).2
  intro indices
  have hset : (⋂ index ∈ indices, gaussianZigZagLargeHazardEvent index) =
      Set.pi (indices : Set ℕ) (fun _ => Set.Ioi (1 : NNReal)) := by
    ext hazards
    simp [gaussianZigZagLargeHazardEvent]
  rw [hset]
  change (Measure.infinitePi fun _ : ℕ => gaussianZigZagHazardMeasure)
      (Set.pi (indices : Set ℕ) (fun _ => Set.Ioi (1 : NNReal))) = _
  rw [Measure.infinitePi_pi
    (μ := fun _ : ℕ => gaussianZigZagHazardMeasure)
    (s := indices) (t := fun _ => Set.Ioi (1 : NNReal))
    (fun _ _ => measurableSet_Ioi)]
  simp_rw [gaussianZigZagHazardSequenceMeasure_largeHazardEvent]

/-- A unit-exponential hazard stream exceeds one infinitely often with
probability one. -/
theorem gaussianZigZagLargeHazardEvent_limsup_measure_eq_one :
    gaussianZigZagHazardSequenceMeasure
      (Filter.limsup gaussianZigZagLargeHazardEvent Filter.atTop) = 1 := by
  apply measure_limsup_eq_one
    measurableSet_gaussianZigZagLargeHazardEvent
    gaussianZigZagLargeHazardEvent_iIndepSet
  simp_rw [gaussianZigZagHazardSequenceMeasure_largeHazardEvent]
  exact ENNReal.tsum_const_eq_top_of_ne_zero
    gaussianZigZagHazardMeasure_Ioi_one_pos.ne'

noncomputable def gaussianZigZagSqrtHazardTerm
    (hazards : ℕ → NNReal) (index : ℕ) : ENNReal :=
  ENNReal.ofReal (Real.sqrt (2 * (hazards index : ℝ)))

theorem one_le_gaussianZigZagSqrtHazardTerm_of_large
    {hazards : ℕ → NNReal} {index : ℕ}
    (hlarge : hazards ∈ gaussianZigZagLargeHazardEvent index) :
    1 ≤ gaussianZigZagSqrtHazardTerm hazards index := by
  rw [gaussianZigZagSqrtHazardTerm, ENNReal.one_le_ofReal,
    Real.one_le_sqrt]
  change 1 < hazards index at hlarge
  exact_mod_cast (show (1 : ℝ) ≤ 2 * (hazards index : ℝ) by
    have : (1 : ℝ) < (hazards index : ℝ) := by exact_mod_cast hlarge
    linarith)

theorem gaussianZigZagSqrtHazard_tsum_eq_top_of_mem_limsup
    (hazards : ℕ → NNReal)
    (hlimsup : hazards ∈
      Filter.limsup gaussianZigZagLargeHazardEvent Filter.atTop) :
    (∑' index, gaussianZigZagSqrtHazardTerm hazards index) = ∞ := by
  have hfrequent : ∃ᶠ index in Filter.atTop,
      hazards ∈ gaussianZigZagLargeHazardEvent index :=
    (Filter.mem_limsup_iff_frequently_mem.mp hlimsup)
  have hinfiniteLarge : Set.Infinite
      {index | hazards ∈ gaussianZigZagLargeHazardEvent index} :=
    Nat.frequently_atTop_iff_infinite.mp hfrequent
  have hinfiniteTerm : Set.Infinite
      {index | 1 ≤ gaussianZigZagSqrtHazardTerm hazards index} :=
    hinfiniteLarge.mono fun index hindex =>
      one_le_gaussianZigZagSqrtHazardTerm_of_large hindex
  by_contra hfiniteSum
  exact hinfiniteTerm (ENNReal.finite_const_le_of_tsum_ne_top
    hfiniteSum one_ne_zero)

theorem gaussianZigZagLargeHazardEvent_mem_limsup_ae :
    ∀ᵐ hazards ∂gaussianZigZagHazardSequenceMeasure,
      hazards ∈ Filter.limsup gaussianZigZagLargeHazardEvent Filter.atTop := by
  rw [ae_iff]
  have hmeasurable : MeasurableSet
      (Filter.limsup gaussianZigZagLargeHazardEvent Filter.atTop) :=
    MeasurableSet.measurableSet_limsup
      measurableSet_gaussianZigZagLargeHazardEvent
  have hset : {hazards | ¬hazards ∈
      Filter.limsup gaussianZigZagLargeHazardEvent Filter.atTop} =
      (Filter.limsup gaussianZigZagLargeHazardEvent Filter.atTop)ᶜ := by
    rfl
  rw [hset, measure_compl hmeasurable (measure_ne_top _ _),
    gaussianZigZagLargeHazardEvent_limsup_measure_eq_one,
    measure_univ, tsub_self]

/-- The pathwise lower-bound series for exact Gaussian Zig-Zag waits diverges
almost surely under the infinite i.i.d. hazard law. -/
theorem gaussianZigZagSqrtHazard_tsum_eq_top_ae :
    ∀ᵐ hazards ∂gaussianZigZagHazardSequenceMeasure,
      (∑' index, gaussianZigZagSqrtHazardTerm hazards index) = ∞ := by
  filter_upwards [gaussianZigZagLargeHazardEvent_mem_limsup_ae]
    with hazards hlimsup
  exact gaussianZigZagSqrtHazard_tsum_eq_top_of_mem_limsup hazards hlimsup

theorem gaussianZigZagHazardSequence_positive_ae :
    ∀ᵐ hazards ∂gaussianZigZagHazardSequenceMeasure,
      ∀ index, 0 < hazards index := by
  rw [ae_all_iff]
  intro index
  have heval := measurePreserving_eval_infinitePi
    (μ := fun _ : ℕ => gaussianZigZagHazardMeasure) index
  simpa only [gaussianZigZagHazardSequenceMeasure] using
    heval.quasiMeasurePreserving.ae
      gaussianZigZagHazardMeasure_positive_ae

/-- State immediately before the event indexed by `eventCount`. -/
noncomputable def gaussianZigZagEventState
    (initial : ZigZagState) (hazards : ℕ → NNReal) : ℕ → ZigZagState
  | 0 => initial
  | eventCount + 1 => gaussianZigZagEventUpdate
      (gaussianZigZagEventState initial hazards eventCount)
      (hazards eventCount)

/-- Inter-event wait generated from the current state and fresh hazard. -/
noncomputable def gaussianZigZagEventWait
    (initial : ZigZagState) (hazards : ℕ → NNReal)
    (eventCount : ℕ) : NNReal :=
  gaussianZigZagWaitingNNReal
    (gaussianZigZagEventState initial hazards eventCount)
    (hazards eventCount)

noncomputable def gaussianZigZagEventWaitTerm
    (initial : ZigZagState) (hazards : ℕ → NNReal)
    (eventCount : ℕ) : ENNReal :=
  ENNReal.ofReal (gaussianZigZagEventWait initial hazards eventCount : ℝ)

theorem gaussianZigZagSqrtHazardTerm_le_eventWaitTerm_succ
    (initial : ZigZagState) (hazards : ℕ → NNReal)
    (eventCount : ℕ) (hpositive : 0 < hazards eventCount) :
    gaussianZigZagSqrtHazardTerm hazards (eventCount + 1) ≤
      gaussianZigZagEventWaitTerm initial hazards (eventCount + 1) := by
  unfold gaussianZigZagEventWaitTerm gaussianZigZagEventWait
  apply ENNReal.ofReal_le_ofReal
  exact sqrt_hazard_le_gaussianZigZagWaitingNNReal_after_event
    (gaussianZigZagEventState initial hazards eventCount) hpositive
    (hazards (eventCount + 1))

/-- For every positive hazard stream whose `sqrt(2E)` series diverges, the
sum of exact Gaussian Zig-Zag inter-event waits is infinite. -/
theorem gaussianZigZagEventWait_tsum_eq_top
    (initial : ZigZagState) (hazards : ℕ → NNReal)
    (hpositive : ∀ index, 0 < hazards index)
    (hdiverges : (∑' index,
      gaussianZigZagSqrtHazardTerm hazards index) = ∞) :
    (∑' index, gaussianZigZagEventWaitTerm initial hazards index) = ∞ := by
  have hsqrtTail : (∑' index,
      gaussianZigZagSqrtHazardTerm hazards (index + 1)) = ∞ :=
    ENNReal.tsum_add_one_eq_top hdiverges (by
      exact ENNReal.ofReal_ne_top)
  have htail : (∑' index,
      gaussianZigZagEventWaitTerm initial hazards (index + 1)) = ∞ := by
    apply top_unique
    rw [← hsqrtTail]
    exact ENNReal.tsum_le_tsum fun index =>
      gaussianZigZagSqrtHazardTerm_le_eventWaitTerm_succ
        initial hazards index (hpositive index)
  rw [tsum_eq_zero_add' ENNReal.summable, htail]
  simp

/-- Exact standard-Gaussian Zig-Zag event times are nonexplosive: under the
infinite i.i.d. exponential-hazard law, their total elapsed time is infinite
almost surely. -/
theorem gaussianZigZagEventWait_tsum_eq_top_ae
    (initial : ZigZagState) :
    ∀ᵐ hazards ∂gaussianZigZagHazardSequenceMeasure,
      (∑' index,
        gaussianZigZagEventWaitTerm initial hazards index) = ∞ := by
  filter_upwards [gaussianZigZagHazardSequence_positive_ae,
    gaussianZigZagSqrtHazard_tsum_eq_top_ae] with hazards hpositive hdiverges
  exact gaussianZigZagEventWait_tsum_eq_top initial hazards
    hpositive hdiverges

noncomputable def gaussianZigZagEventElapsed
    (initial : ZigZagState) (hazards : ℕ → NNReal)
    (eventCount : ℕ) : ENNReal :=
  ∑ index ∈ Finset.range eventCount,
    gaussianZigZagEventWaitTerm initial hazards index

theorem gaussianZigZagEventElapsed_ne_top
    (initial : ZigZagState) (hazards : ℕ → NNReal) (eventCount : ℕ) :
    gaussianZigZagEventElapsed initial hazards eventCount ≠ ∞ := by
  unfold gaussianZigZagEventElapsed gaussianZigZagEventWaitTerm
  rw [ENNReal.sum_ne_top]
  intro index _
  exact ENNReal.ofReal_ne_top

/-- Dropping the first hazard and restarting from the first post-event state
reproduces every later pre-event state. -/
theorem gaussianZigZagEventState_succ_eq_tail
    (initial : ZigZagState) (hazards : ℕ → NNReal) (eventCount : ℕ) :
    gaussianZigZagEventState initial hazards (eventCount + 1) =
      gaussianZigZagEventState
        (gaussianZigZagEventUpdate initial (hazards 0))
        (fun index => hazards (index + 1)) eventCount := by
  induction eventCount with
  | zero => simp [gaussianZigZagEventState]
  | succ eventCount ih =>
      change gaussianZigZagEventUpdate
          (gaussianZigZagEventState initial hazards (eventCount + 1))
          (hazards (eventCount + 1)) =
        gaussianZigZagEventUpdate
          (gaussianZigZagEventState
            (gaussianZigZagEventUpdate initial (hazards 0))
            (fun index => hazards (index + 1)) eventCount)
          (hazards (eventCount + 1))
      exact congrArg
        (fun state => gaussianZigZagEventUpdate state (hazards (eventCount + 1))) ih

theorem gaussianZigZagEventState_eq_tail_pred
    (initial : ZigZagState) (hazards : ℕ → NNReal)
    {eventCount : ℕ} (hpositive : 0 < eventCount) :
    gaussianZigZagEventState initial hazards eventCount =
      gaussianZigZagEventState
        (gaussianZigZagEventUpdate initial (hazards 0))
        (fun index => hazards (index + 1)) (eventCount - 1) := by
  obtain ⟨eventCount, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpositive.ne'
  simpa using gaussianZigZagEventState_succ_eq_tail initial hazards eventCount

/-- Inter-event waits shift with the hazard stream after the first event. -/
theorem gaussianZigZagEventWait_succ_eq_tail
    (initial : ZigZagState) (hazards : ℕ → NNReal) (eventCount : ℕ) :
    gaussianZigZagEventWait initial hazards (eventCount + 1) =
      gaussianZigZagEventWait
        (gaussianZigZagEventUpdate initial (hazards 0))
        (fun index => hazards (index + 1)) eventCount := by
  unfold gaussianZigZagEventWait
  rw [gaussianZigZagEventState_succ_eq_tail]

theorem gaussianZigZagEventWaitTerm_succ_eq_tail
    (initial : ZigZagState) (hazards : ℕ → NNReal) (eventCount : ℕ) :
    gaussianZigZagEventWaitTerm initial hazards (eventCount + 1) =
      gaussianZigZagEventWaitTerm
        (gaussianZigZagEventUpdate initial (hazards 0))
        (fun index => hazards (index + 1)) eventCount := by
  unfold gaussianZigZagEventWaitTerm
  rw [gaussianZigZagEventWait_succ_eq_tail]

/-- Cumulative event time splits into the first wait plus the cumulative time
of the restarted tail process. -/
theorem gaussianZigZagEventElapsed_succ_eq_first_add_tail
    (initial : ZigZagState) (hazards : ℕ → NNReal) (eventCount : ℕ) :
    gaussianZigZagEventElapsed initial hazards (eventCount + 1) =
      gaussianZigZagEventWaitTerm initial hazards 0 +
        gaussianZigZagEventElapsed
          (gaussianZigZagEventUpdate initial (hazards 0))
          (fun index => hazards (index + 1)) eventCount := by
  induction eventCount with
  | zero => simp [gaussianZigZagEventElapsed]
  | succ eventCount ih =>
      rw [show gaussianZigZagEventElapsed initial hazards (eventCount + 2) =
          gaussianZigZagEventElapsed initial hazards (eventCount + 1) +
            gaussianZigZagEventWaitTerm initial hazards (eventCount + 1) by
        simp [gaussianZigZagEventElapsed, Finset.sum_range_succ]]
      rw [ih, gaussianZigZagEventWaitTerm_succ_eq_tail]
      rw [show gaussianZigZagEventElapsed
          (gaussianZigZagEventUpdate initial (hazards 0))
          (fun index => hazards (index + 1)) (eventCount + 1) =
          gaussianZigZagEventElapsed
            (gaussianZigZagEventUpdate initial (hazards 0))
            (fun index => hazards (index + 1)) eventCount +
          gaussianZigZagEventWaitTerm
            (gaussianZigZagEventUpdate initial (hazards 0))
            (fun index => hazards (index + 1)) eventCount by
        simp [gaussianZigZagEventElapsed, Finset.sum_range_succ]]
      ac_rfl

theorem gaussianZigZagEventElapsed_eq_first_add_tail_pred
    (initial : ZigZagState) (hazards : ℕ → NNReal)
    {eventCount : ℕ} (hpositive : 0 < eventCount) :
    gaussianZigZagEventElapsed initial hazards eventCount =
      gaussianZigZagEventWaitTerm initial hazards 0 +
        gaussianZigZagEventElapsed
          (gaussianZigZagEventUpdate initial (hazards 0))
          (fun index => hazards (index + 1)) (eventCount - 1) := by
  obtain ⟨eventCount, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpositive.ne'
  simpa using gaussianZigZagEventElapsed_succ_eq_first_add_tail
    initial hazards eventCount

/-- Equivalent finite-horizon form of nonexplosion: almost surely, cumulative
event time tends to infinity as the event count grows. -/
theorem gaussianZigZagEventElapsed_tendsto_atTop_ae
    (initial : ZigZagState) :
    ∀ᵐ hazards ∂gaussianZigZagHazardSequenceMeasure,
      Filter.Tendsto (gaussianZigZagEventElapsed initial hazards)
        Filter.atTop (nhds (∞ : ENNReal)) := by
  filter_upwards [gaussianZigZagEventWait_tsum_eq_top_ae initial]
    with hazards hsum
  have htendsto := ENNReal.tendsto_nat_tsum
    (gaussianZigZagEventWaitTerm initial hazards)
  rw [hsum] at htendsto
  change Filter.Tendsto (fun eventCount =>
    ∑ index ∈ Finset.range eventCount,
      gaussianZigZagEventWaitTerm initial hazards index)
    Filter.atTop (nhds (∞ : ENNReal))
  exact htendsto

theorem measurable_gaussianZigZagEventUpdate :
    Measurable (fun input : ZigZagState × NNReal =>
      gaussianZigZagEventUpdate input.1 input.2) := by
  have hwait : Measurable (fun input : ZigZagState × NNReal =>
      gaussianZigZagWaitingNNReal input.1 input.2) :=
    measurable_gaussianZigZagWaitingNNReal
  have hvelocity : Measurable (fun input : ZigZagState × NNReal =>
      zigZagVelocity input.1.2) := by
    unfold zigZagVelocity
    fun_prop
  unfold gaussianZigZagEventUpdate zigZagFlip zigZagFlow
  exact ((measurable_fst.comp measurable_fst).add
    (hwait.coe_nnreal_real.mul hvelocity)).prodMk (by fun_prop)

theorem measurable_gaussianZigZagEventState
    (initial : ZigZagState) (eventCount : ℕ) :
    Measurable (fun hazards : ℕ → NNReal =>
      gaussianZigZagEventState initial hazards eventCount) := by
  induction eventCount with
  | zero => exact measurable_const
  | succ eventCount ih =>
      exact measurable_gaussianZigZagEventUpdate.comp
        (ih.prodMk (measurable_pi_apply eventCount))

theorem measurable_gaussianZigZagEventWait
    (initial : ZigZagState) (eventCount : ℕ) :
    Measurable (fun hazards : ℕ → NNReal =>
      gaussianZigZagEventWait initial hazards eventCount) := by
  unfold gaussianZigZagEventWait
  exact measurable_gaussianZigZagWaitingNNReal.comp
    ((measurable_gaussianZigZagEventState initial eventCount).prodMk
      (measurable_pi_apply eventCount))

theorem measurable_gaussianZigZagEventWaitTerm
    (initial : ZigZagState) (eventCount : ℕ) :
    Measurable (fun hazards : ℕ → NNReal =>
      gaussianZigZagEventWaitTerm initial hazards eventCount) := by
  unfold gaussianZigZagEventWaitTerm
  exact (measurable_gaussianZigZagEventWait initial eventCount).coe_nnreal_real.ennreal_ofReal

theorem measurable_gaussianZigZagEventElapsed
    (initial : ZigZagState) (eventCount : ℕ) :
    Measurable (fun hazards : ℕ → NNReal =>
      gaussianZigZagEventElapsed initial hazards eventCount) := by
  unfold gaussianZigZagEventElapsed
  exact Finset.measurable_sum _ fun index _ =>
    measurable_gaussianZigZagEventWaitTerm initial index

def gaussianZigZagEventCrossed
    (initial : ZigZagState) (horizon : NNReal)
    (hazards : ℕ → NNReal) (eventCount : ℕ) : Prop :=
  (horizon : ENNReal) <
    gaussianZigZagEventElapsed initial hazards eventCount

/-- After the first event wait has elapsed, cumulative-time crossing is
exactly crossing by the restarted tail process over the residual horizon. -/
theorem gaussianZigZagEventCrossed_succ_iff_tail
    (initial : ZigZagState) (horizon : NNReal) (hazards : ℕ → NNReal)
    (hwait : gaussianZigZagEventWait initial hazards 0 ≤ horizon)
    (eventCount : ℕ) :
    gaussianZigZagEventCrossed initial horizon hazards (eventCount + 1) ↔
      gaussianZigZagEventCrossed
        (gaussianZigZagEventUpdate initial (hazards 0))
        (horizon - gaussianZigZagEventWait initial hazards 0)
        (fun index => hazards (index + 1)) eventCount := by
  unfold gaussianZigZagEventCrossed
  rw [gaussianZigZagEventElapsed_succ_eq_first_add_tail]
  unfold gaussianZigZagEventWaitTerm
  rw [ENNReal.ofReal_coe_nnreal]
  rw [ENNReal.coe_sub]
  have hwait' :
      (gaussianZigZagEventWait initial hazards 0 : ENNReal) ≤
        (horizon : ENNReal) := by exact_mod_cast hwait
  exact (ENNReal.sub_lt_iff_lt_left ENNReal.coe_ne_top hwait').symm

theorem measurableSet_gaussianZigZagEventCrossed
    (initial : ZigZagState) (horizon : NNReal)
    (eventCount : ℕ) :
    MeasurableSet {hazards | gaussianZigZagEventCrossed
      initial horizon hazards eventCount} := by
  unfold gaussianZigZagEventCrossed
  exact measurableSet_lt measurable_const
    (measurable_gaussianZigZagEventElapsed initial eventCount)

def gaussianZigZagCrossingSearchPredicate
    (initial : ZigZagState) (horizon : NNReal)
    (hazards : ℕ → NNReal) (eventCount : ℕ) : Prop :=
  gaussianZigZagEventCrossed initial horizon hazards eventCount ∨
    (eventCount = 0 ∧
      ¬∃ count, gaussianZigZagEventCrossed initial horizon hazards count)

theorem gaussianZigZagCrossingSearchPredicate_exists
    (initial : ZigZagState) (horizon : NNReal)
    (hazards : ℕ → NNReal) :
    ∃ eventCount, gaussianZigZagCrossingSearchPredicate
      initial horizon hazards eventCount := by
  classical
  by_cases hcrossing : ∃ eventCount,
      gaussianZigZagEventCrossed initial horizon hazards eventCount
  · obtain ⟨eventCount, heventCount⟩ := hcrossing
    exact ⟨eventCount, Or.inl heventCount⟩
  · exact ⟨0, Or.inr ⟨rfl, hcrossing⟩⟩

theorem measurableSet_gaussianZigZagCrossingSearchPredicate
    (initial : ZigZagState) (horizon : NNReal)
    (eventCount : ℕ) :
    MeasurableSet {hazards | gaussianZigZagCrossingSearchPredicate
      initial horizon hazards eventCount} := by
  classical
  by_cases hzero : eventCount = 0
  · subst eventCount
    simp only [gaussianZigZagCrossingSearchPredicate, true_and]
    apply MeasurableSet.union
    · exact measurableSet_gaussianZigZagEventCrossed initial horizon 0
    · have hexists : MeasurableSet {hazards : ℕ → NNReal |
          ∃ count, gaussianZigZagEventCrossed
            initial horizon hazards count} := by
        rw [show {hazards : ℕ → NNReal | ∃ count,
            gaussianZigZagEventCrossed initial horizon hazards count} =
            ⋃ count, {hazards | gaussianZigZagEventCrossed
              initial horizon hazards count} by
          ext hazards
          simp]
        exact MeasurableSet.iUnion fun count =>
          measurableSet_gaussianZigZagEventCrossed initial horizon count
      exact hexists.compl
  · simp only [gaussianZigZagCrossingSearchPredicate, hzero, false_and,
      or_false]
    exact measurableSet_gaussianZigZagEventCrossed initial horizon eventCount

/-- First event count whose cumulative time exceeds the horizon, with a total
fallback value `0` on the null set where no crossing exists. -/
noncomputable def gaussianZigZagCrossingIndex
    (initial : ZigZagState) (horizon : NNReal)
    (hazards : ℕ → NNReal) : ℕ := by
  classical
  exact Nat.find (gaussianZigZagCrossingSearchPredicate_exists
    initial horizon hazards)

theorem measurable_gaussianZigZagCrossingIndex
    (initial : ZigZagState) (horizon : NNReal) :
    Measurable (gaussianZigZagCrossingIndex initial horizon) := by
  unfold gaussianZigZagCrossingIndex
  classical
  apply measurable_find
  exact measurableSet_gaussianZigZagCrossingSearchPredicate initial horizon

theorem gaussianZigZagEventCrossed_exists_ae
    (initial : ZigZagState) (horizon : NNReal) :
    ∀ᵐ hazards ∂gaussianZigZagHazardSequenceMeasure,
      ∃ eventCount, gaussianZigZagEventCrossed
        initial horizon hazards eventCount := by
  filter_upwards [gaussianZigZagEventElapsed_tendsto_atTop_ae initial]
    with hazards htendsto
  have hneighborhood : Set.Ioi (horizon : ENNReal) ∈ nhds (∞ : ENNReal) :=
    Ioi_mem_nhds (ENNReal.coe_lt_top)
  have heventually : ∀ᶠ eventCount in Filter.atTop,
      (horizon : ENNReal) <
        gaussianZigZagEventElapsed initial hazards eventCount :=
    htendsto.eventually hneighborhood
  obtain ⟨eventCount, heventCount⟩ := heventually.exists
  exact ⟨eventCount, heventCount⟩

/-- The stream conditions used in the nonexplosion proof imply a crossing at
every finite horizon, uniformly over the initial state. -/
theorem gaussianZigZagEventCrossed_exists_of_positive_of_sqrt_tsum
    (initial : ZigZagState) (horizon : NNReal) (hazards : ℕ → NNReal)
    (hpositive : ∀ index, 0 < hazards index)
    (hdiverges : (∑' index,
      gaussianZigZagSqrtHazardTerm hazards index) = ∞) :
    ∃ eventCount, gaussianZigZagEventCrossed
      initial horizon hazards eventCount := by
  have hsum := gaussianZigZagEventWait_tsum_eq_top
    initial hazards hpositive hdiverges
  have htendsto := ENNReal.tendsto_nat_tsum
    (gaussianZigZagEventWaitTerm initial hazards)
  rw [hsum] at htendsto
  have hneighborhood : Set.Ioi (horizon : ENNReal) ∈ nhds (∞ : ENNReal) :=
    Ioi_mem_nhds (ENNReal.coe_lt_top)
  have heventually : ∀ᶠ eventCount in Filter.atTop,
      (horizon : ENNReal) <
        gaussianZigZagEventElapsed initial hazards eventCount := by
    apply htendsto.eventually hneighborhood
  exact heventually.exists

theorem gaussianZigZagCrossingIndex_crossed
    (initial : ZigZagState) (horizon : NNReal) (hazards : ℕ → NNReal)
    (hexists : ∃ eventCount,
      gaussianZigZagEventCrossed initial horizon hazards eventCount) :
    gaussianZigZagEventCrossed initial horizon hazards
      (gaussianZigZagCrossingIndex initial horizon hazards) := by
  classical
  have hspec := Nat.find_spec
    (gaussianZigZagCrossingSearchPredicate_exists initial horizon hazards)
  rcases hspec with hcrossed | ⟨_, hnone⟩
  · exact hcrossed
  · exact (hnone hexists).elim

theorem gaussianZigZagCrossingIndex_pos
    (initial : ZigZagState) (horizon : NNReal) (hazards : ℕ → NNReal)
    (hexists : ∃ eventCount,
      gaussianZigZagEventCrossed initial horizon hazards eventCount) :
    0 < gaussianZigZagCrossingIndex initial horizon hazards := by
  have hcrossed := gaussianZigZagCrossingIndex_crossed
    initial horizon hazards hexists
  by_contra hnot
  have hzero : gaussianZigZagCrossingIndex initial horizon hazards = 0 :=
    Nat.eq_zero_of_not_pos hnot
  rw [hzero] at hcrossed
  unfold gaussianZigZagEventCrossed gaussianZigZagEventElapsed at hcrossed
  simp at hcrossed

theorem gaussianZigZagCrossingIndex_not_crossed_of_lt
    (initial : ZigZagState) (horizon : NNReal) (hazards : ℕ → NNReal)
    {eventCount : ℕ}
    (hlt : eventCount <
      gaussianZigZagCrossingIndex initial horizon hazards) :
    ¬gaussianZigZagEventCrossed initial horizon hazards eventCount := by
  classical
  intro hcrossed
  unfold gaussianZigZagCrossingIndex at hlt
  exact Nat.find_min
    (gaussianZigZagCrossingSearchPredicate_exists initial horizon hazards)
    hlt (Or.inl hcrossed)

/-- Once the first wait is completed, the first-crossing index is one plus
the crossing index of the restarted tail process. -/
theorem gaussianZigZagCrossingIndex_eq_tail_add_one
    (initial : ZigZagState) (horizon : NNReal) (hazards : ℕ → NNReal)
    (hwait : gaussianZigZagEventWait initial hazards 0 ≤ horizon)
    (htailExists : ∃ eventCount, gaussianZigZagEventCrossed
      (gaussianZigZagEventUpdate initial (hazards 0))
      (horizon - gaussianZigZagEventWait initial hazards 0)
      (fun index => hazards (index + 1)) eventCount) :
    gaussianZigZagCrossingIndex initial horizon hazards =
      gaussianZigZagCrossingIndex
        (gaussianZigZagEventUpdate initial (hazards 0))
        (horizon - gaussianZigZagEventWait initial hazards 0)
        (fun index => hazards (index + 1)) + 1 := by
  classical
  let restarted := gaussianZigZagEventUpdate initial (hazards 0)
  let residual := horizon - gaussianZigZagEventWait initial hazards 0
  let tail := fun index => hazards (index + 1)
  let tailIndex := gaussianZigZagCrossingIndex restarted residual tail
  have htailCrossed :
      gaussianZigZagEventCrossed restarted residual tail tailIndex :=
    gaussianZigZagCrossingIndex_crossed restarted residual tail htailExists
  have horiginalCrossed : gaussianZigZagEventCrossed initial horizon hazards
      (tailIndex + 1) :=
    (gaussianZigZagEventCrossed_succ_iff_tail initial horizon hazards hwait
      tailIndex).mpr htailCrossed
  have horiginalExists : ∃ eventCount,
      gaussianZigZagEventCrossed initial horizon hazards eventCount :=
    ⟨tailIndex + 1, horiginalCrossed⟩
  change Nat.find
      (gaussianZigZagCrossingSearchPredicate_exists initial horizon hazards) =
    tailIndex + 1
  apply (Nat.find_eq_iff
    (gaussianZigZagCrossingSearchPredicate_exists initial horizon hazards)).2
  constructor
  · exact Or.inl horiginalCrossed
  · intro eventCount hlt
    simp only [gaussianZigZagCrossingSearchPredicate]
    push Not
    constructor
    · cases eventCount with
      | zero =>
          unfold gaussianZigZagEventCrossed gaussianZigZagEventElapsed
          simp
      | succ eventCount =>
          apply (gaussianZigZagEventCrossed_succ_iff_tail
            initial horizon hazards hwait eventCount).not.mpr
          apply gaussianZigZagCrossingIndex_not_crossed_of_lt
          have heq : gaussianZigZagCrossingIndex
              (gaussianZigZagEventUpdate initial (hazards 0))
              (horizon - gaussianZigZagEventWait initial hazards 0)
              (fun index => hazards (index + 1)) = tailIndex := by
            simp only [tailIndex, restarted, residual, tail]
          rw [heq]
          omega
    · intro _
      exact horiginalExists

theorem gaussianZigZagCrossingIndex_crossed_ae
    (initial : ZigZagState) (horizon : NNReal) :
    ∀ᵐ hazards ∂gaussianZigZagHazardSequenceMeasure,
      gaussianZigZagEventCrossed initial horizon hazards
        (gaussianZigZagCrossingIndex initial horizon hazards) := by
  filter_upwards [gaussianZigZagEventCrossed_exists_ae initial horizon]
    with hazards hexists
  exact gaussianZigZagCrossingIndex_crossed initial horizon hazards hexists

/-- Exact state at a fixed horizon, obtained by retaining all events strictly
before the first crossing and flowing through the residual interval. -/
noncomputable def gaussianZigZagHorizonEndpoint
    (initial : ZigZagState) (horizon : NNReal)
    (hazards : ℕ → NNReal) : ZigZagState :=
  let completed := gaussianZigZagCrossingIndex initial horizon hazards - 1
  zigZagFlow
    (horizon -
      (gaussianZigZagEventElapsed initial hazards completed).toNNReal)
    (gaussianZigZagEventState initial hazards completed)

/-- If the first event occurs by the horizon, the stopped endpoint is exactly
the endpoint of the post-event state driven by the fresh hazard tail over the
residual horizon. -/
theorem gaussianZigZagHorizonEndpoint_eq_tail_of_firstWait_le
    (initial : ZigZagState) (horizon : NNReal) (hazards : ℕ → NNReal)
    (hwait : gaussianZigZagEventWait initial hazards 0 ≤ horizon)
    (htailExists : ∃ eventCount, gaussianZigZagEventCrossed
      (gaussianZigZagEventUpdate initial (hazards 0))
      (horizon - gaussianZigZagEventWait initial hazards 0)
      (fun index => hazards (index + 1)) eventCount) :
    gaussianZigZagHorizonEndpoint initial horizon hazards =
      gaussianZigZagHorizonEndpoint
        (gaussianZigZagEventUpdate initial (hazards 0))
        (horizon - gaussianZigZagEventWait initial hazards 0)
        (fun index => hazards (index + 1)) := by
  let restarted := gaussianZigZagEventUpdate initial (hazards 0)
  let residual := horizon - gaussianZigZagEventWait initial hazards 0
  let tail := fun index => hazards (index + 1)
  let tailIndex := gaussianZigZagCrossingIndex restarted residual tail
  have htailPositive : 0 < tailIndex :=
    gaussianZigZagCrossingIndex_pos restarted residual tail htailExists
  have hindex : gaussianZigZagCrossingIndex initial horizon hazards =
      tailIndex + 1 :=
    gaussianZigZagCrossingIndex_eq_tail_add_one
      initial horizon hazards hwait htailExists
  have hstate : gaussianZigZagEventState initial hazards tailIndex =
      gaussianZigZagEventState restarted tail (tailIndex - 1) := by
    simpa [restarted, tail] using
      gaussianZigZagEventState_eq_tail_pred initial hazards htailPositive
  have helapsed : gaussianZigZagEventElapsed initial hazards tailIndex =
      (gaussianZigZagEventWait initial hazards 0 : ENNReal) +
        gaussianZigZagEventElapsed restarted tail (tailIndex - 1) := by
    simpa [restarted, tail, gaussianZigZagEventWaitTerm,
      ENNReal.ofReal_coe_nnreal] using
      gaussianZigZagEventElapsed_eq_first_add_tail_pred
        initial hazards htailPositive
  have helapsedNN := congrArg ENNReal.toNNReal helapsed
  have htailFinite :
      gaussianZigZagEventElapsed restarted tail (tailIndex - 1) ≠ ∞ :=
    gaussianZigZagEventElapsed_ne_top restarted tail (tailIndex - 1)
  rw [ENNReal.toNNReal_add ENNReal.coe_ne_top htailFinite,
    ENNReal.toNNReal_coe] at helapsedNN
  unfold gaussianZigZagHorizonEndpoint
  rw [hindex]
  simp only [Nat.add_sub_cancel]
  change zigZagFlow
      (horizon -
        (gaussianZigZagEventElapsed initial hazards tailIndex).toNNReal)
      (gaussianZigZagEventState initial hazards tailIndex) =
    zigZagFlow
      (residual -
        (gaussianZigZagEventElapsed restarted tail (tailIndex - 1)).toNNReal)
      (gaussianZigZagEventState restarted tail (tailIndex - 1))
  rw [hstate, helapsedNN, tsub_add_eq_tsub_tsub]

/-- First-event decomposition of a stopped endpoint on an explicit
`(head, tail)` hazard pair. -/
noncomputable def gaussianZigZagFirstEventEndpoint
    (initial : ZigZagState) (horizon : NNReal)
    (headTail : NNReal × (ℕ → NNReal)) : ZigZagState :=
  let wait := gaussianZigZagWaitingNNReal initial headTail.1
  if horizon < wait then
    zigZagFlow horizon initial
  else
    gaussianZigZagHorizonEndpoint
      (gaussianZigZagEventUpdate initial headTail.1)
      (horizon - wait) headTail.2

theorem gaussianZigZagCrossingIndex_zero_eq_one
    (initial : ZigZagState) (hazards : ℕ → NNReal)
    (hhazard : 0 < hazards 0) :
    gaussianZigZagCrossingIndex initial 0 hazards = 1 := by
  classical
  have hwait : 0 < gaussianZigZagEventWaitTerm initial hazards 0 := by
    unfold gaussianZigZagEventWaitTerm gaussianZigZagEventWait
    rw [ENNReal.ofReal_pos]
    exact_mod_cast (gaussianZigZagWaitingNNReal_pos initial hhazard)
  have hcrossing : gaussianZigZagEventCrossed initial 0 hazards 1 := by
    unfold gaussianZigZagEventCrossed gaussianZigZagEventElapsed
    simp only [ENNReal.coe_zero, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add]
    exact hwait
  unfold gaussianZigZagCrossingIndex
  apply (Nat.find_eq_iff
    (gaussianZigZagCrossingSearchPredicate_exists initial 0 hazards)).2
  constructor
  · exact Or.inl hcrossing
  · intro eventCount heventCount
    have heq : eventCount = 0 := Nat.lt_one_iff.mp heventCount
    subst eventCount
    simp only [gaussianZigZagCrossingSearchPredicate, true_and]
    push Not
    constructor
    · unfold gaussianZigZagEventCrossed gaussianZigZagEventElapsed
      simp
    · exact ⟨1, hcrossing⟩

/-- If the first event wait lies strictly beyond the requested horizon, the
first cumulative-time crossing occurs at index one.  This is the no-event
branch of the stopped-path first-event decomposition. -/
theorem gaussianZigZagCrossingIndex_eq_one_of_lt_firstWait
    (initial : ZigZagState) (horizon : NNReal) (hazards : ℕ → NNReal)
    (hbefore : horizon < gaussianZigZagEventWait initial hazards 0) :
    gaussianZigZagCrossingIndex initial horizon hazards = 1 := by
  classical
  have hcrossing : gaussianZigZagEventCrossed initial horizon hazards 1 := by
    unfold gaussianZigZagEventCrossed gaussianZigZagEventElapsed
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    unfold gaussianZigZagEventWaitTerm
    rw [ENNReal.ofReal_coe_nnreal]
    exact_mod_cast hbefore
  unfold gaussianZigZagCrossingIndex
  apply (Nat.find_eq_iff
    (gaussianZigZagCrossingSearchPredicate_exists initial horizon hazards)).2
  constructor
  · exact Or.inl hcrossing
  · intro eventCount heventCount
    have heq : eventCount = 0 := Nat.lt_one_iff.mp heventCount
    subst eventCount
    simp only [gaussianZigZagCrossingSearchPredicate, true_and]
    push Not
    constructor
    · unfold gaussianZigZagEventCrossed gaussianZigZagEventElapsed
      simp
    · exact ⟨1, hcrossing⟩

/-- Before the first event, the stopped construction is exactly deterministic
linear flow.  This pointwise lemma is the base branch needed before applying
the exponential clock's law-level memoryless property. -/
theorem gaussianZigZagHorizonEndpoint_eq_flow_of_lt_firstWait
    (initial : ZigZagState) (horizon : NNReal) (hazards : ℕ → NNReal)
    (hbefore : horizon < gaussianZigZagEventWait initial hazards 0) :
    gaussianZigZagHorizonEndpoint initial horizon hazards =
      zigZagFlow horizon initial := by
  unfold gaussianZigZagHorizonEndpoint
  rw [gaussianZigZagCrossingIndex_eq_one_of_lt_firstWait
    initial horizon hazards hbefore]
  simp [gaussianZigZagEventElapsed, gaussianZigZagEventState]

/-- Under the exact head/tail product law, direct stopped execution agrees
almost surely with the first-event decomposition. The common full-measure
tail conditions work uniformly for every sampled first hazard. -/
theorem gaussianZigZagHorizonEndpoint_cons_ae_eq_firstEvent
    (initial : ZigZagState) (horizon : NNReal) :
    (fun headTail => gaussianZigZagHorizonEndpoint initial horizon
        (gaussianZigZagHazardCons headTail)) =ᵐ[
      gaussianZigZagHazardMeasure.prod gaussianZigZagHazardSequenceMeasure]
      gaussianZigZagFirstEventEndpoint initial horizon := by
  have hgood : ∀ᵐ tail ∂gaussianZigZagHazardSequenceMeasure,
      (∀ index, 0 < tail index) ∧
        (∑' index, gaussianZigZagSqrtHazardTerm tail index) = ∞ := by
    filter_upwards [gaussianZigZagHazardSequence_positive_ae,
      gaussianZigZagSqrtHazard_tsum_eq_top_ae] with tail hpositive hdiverges
    exact ⟨hpositive, hdiverges⟩
  have hgoodProduct : ∀ᵐ headTail ∂
      gaussianZigZagHazardMeasure.prod gaussianZigZagHazardSequenceMeasure,
      (∀ index, 0 < headTail.2 index) ∧
        (∑' index,
          gaussianZigZagSqrtHazardTerm headTail.2 index) = ∞ :=
    (Measure.quasiMeasurePreserving_snd
      (μ := gaussianZigZagHazardMeasure)
      (ν := gaussianZigZagHazardSequenceMeasure)).ae hgood
  filter_upwards [hgoodProduct] with headTail hgoodTail
  by_cases hbefore : horizon <
      gaussianZigZagWaitingNNReal initial headTail.1
  · have hpoint := gaussianZigZagHorizonEndpoint_eq_flow_of_lt_firstWait
      initial horizon (gaussianZigZagHazardCons headTail)
      (by simpa [gaussianZigZagEventWait, gaussianZigZagEventState,
        gaussianZigZagHazardCons] using hbefore)
    simpa [gaussianZigZagFirstEventEndpoint, hbefore] using hpoint
  · have hwait : gaussianZigZagEventWait initial
        (gaussianZigZagHazardCons headTail) 0 ≤ horizon := by
      simpa [gaussianZigZagEventWait, gaussianZigZagEventState,
        gaussianZigZagHazardCons] using not_lt.mp hbefore
    have htailExists : ∃ eventCount, gaussianZigZagEventCrossed
        (gaussianZigZagEventUpdate initial headTail.1)
        (horizon - gaussianZigZagWaitingNNReal initial headTail.1)
        headTail.2 eventCount :=
      gaussianZigZagEventCrossed_exists_of_positive_of_sqrt_tsum
        _ _ _ hgoodTail.1 hgoodTail.2
    have hpoint := gaussianZigZagHorizonEndpoint_eq_tail_of_firstWait_le
      initial horizon (gaussianZigZagHazardCons headTail) hwait
      (by simpa [gaussianZigZagEventWait, gaussianZigZagEventState,
        gaussianZigZagHazardCons] using htailExists)
    simpa [gaussianZigZagFirstEventEndpoint, hbefore,
      gaussianZigZagEventWait, gaussianZigZagEventState,
      gaussianZigZagHazardCons] using hpoint

theorem gaussianZigZagHorizonEndpoint_zero
    (initial : ZigZagState) (hazards : ℕ → NNReal)
    (hhazard : 0 < hazards 0) :
    gaussianZigZagHorizonEndpoint initial 0 hazards = initial := by
  unfold gaussianZigZagHorizonEndpoint
  rw [gaussianZigZagCrossingIndex_zero_eq_one initial hazards hhazard]
  simp [gaussianZigZagEventElapsed, gaussianZigZagEventState, zigZagFlow]

theorem gaussianZigZagHorizonEndpoint_zero_ae (initial : ZigZagState) :
    ∀ᵐ hazards ∂gaussianZigZagHazardSequenceMeasure,
      gaussianZigZagHorizonEndpoint initial 0 hazards = initial := by
  filter_upwards [gaussianZigZagHazardSequence_positive_ae] with hazards hpositive
  exact gaussianZigZagHorizonEndpoint_zero initial hazards (hpositive 0)

theorem measurable_gaussianZigZagHorizonEndpoint
    (initial : ZigZagState) (horizon : NNReal) :
    Measurable (gaussianZigZagHorizonEndpoint initial horizon) := by
  classical
  let predicate := gaussianZigZagCrossingSearchPredicate initial horizon
  let existsPredicate := gaussianZigZagCrossingSearchPredicate_exists initial horizon
  have hfamily : ∀ eventCount, Measurable (fun hazards : ℕ → NNReal =>
      zigZagFlow
        (horizon -
          (gaussianZigZagEventElapsed initial hazards (eventCount - 1)).toNNReal)
        (gaussianZigZagEventState initial hazards (eventCount - 1))) := by
    intro eventCount
    have hstate := measurable_gaussianZigZagEventState initial (eventCount - 1)
    have helapsed := measurable_gaussianZigZagEventElapsed initial (eventCount - 1)
    have htime : Measurable (fun hazards : ℕ → NNReal =>
        horizon - (gaussianZigZagEventElapsed initial hazards
          (eventCount - 1)).toNNReal) :=
      measurable_const.sub helapsed.ennreal_toNNReal
    unfold zigZagFlow
    have hvelocity : Measurable (fun hazards : ℕ → NNReal =>
        zigZagVelocity (gaussianZigZagEventState initial hazards
          (eventCount - 1)).2) := by
      unfold zigZagVelocity
      fun_prop
    exact ((hstate.fst).add
      (htime.coe_nnreal_real.mul hvelocity)).prodMk hstate.snd
  change Measurable (fun hazards =>
    (fun eventCount hazards => zigZagFlow
      (horizon -
        (gaussianZigZagEventElapsed initial hazards (eventCount - 1)).toNNReal)
      (gaussianZigZagEventState initial hazards (eventCount - 1)))
      (Nat.find (existsPredicate hazards)) hazards)
  exact Measurable.find hfamily
    (measurableSet_gaussianZigZagCrossingSearchPredicate initial horizon)
    existsPredicate

/-- The first-event branch is measurable modulo the actual head/tail hazard
law. This is the exact strength needed for law-level renewal calculations;
the branch agrees almost surely with the already measurable direct stopped
execution. -/
theorem aemeasurable_gaussianZigZagFirstEventEndpoint
    (initial : ZigZagState) (horizon : NNReal) :
    AEMeasurable (gaussianZigZagFirstEventEndpoint initial horizon)
      (gaussianZigZagHazardMeasure.prod
        gaussianZigZagHazardSequenceMeasure) := by
  have hdirect : Measurable (fun headTail =>
      gaussianZigZagHorizonEndpoint initial horizon
        (gaussianZigZagHazardCons headTail)) :=
    (measurable_gaussianZigZagHorizonEndpoint initial horizon).comp
      measurable_gaussianZigZagHazardCons
  exact hdirect.aemeasurable.congr
    (gaussianZigZagHorizonEndpoint_cons_ae_eq_firstEvent
      initial horizon)

/-- Law-level first-event equation for the stopped Gaussian Zig-Zag path.
The left side is the original infinite-stream construction; the right side
draws an independent first hazard and fresh tail, then executes the explicit
first-event branch. -/
theorem gaussianZigZagHorizonEndpoint_firstEventLaw
    (initial : ZigZagState) (horizon : NNReal) :
    Measure.map (gaussianZigZagHorizonEndpoint initial horizon)
        gaussianZigZagHazardSequenceMeasure =
      Measure.map (gaussianZigZagFirstEventEndpoint initial horizon)
        (gaussianZigZagHazardMeasure.prod
          gaussianZigZagHazardSequenceMeasure) := by
  calc
    Measure.map (gaussianZigZagHorizonEndpoint initial horizon)
        gaussianZigZagHazardSequenceMeasure =
        Measure.map
          ((fun headTail => gaussianZigZagHorizonEndpoint initial horizon
            (gaussianZigZagHazardCons headTail)))
          (gaussianZigZagHazardMeasure.prod
            gaussianZigZagHazardSequenceMeasure) := by
      rw [← gaussianZigZagHazardSequenceMeasure_map_headTail]
      symm
      change Measure.map
          (gaussianZigZagHorizonEndpoint initial horizon ∘
            gaussianZigZagHazardCons)
          (Measure.map gaussianZigZagHazardHeadTail
            gaussianZigZagHazardSequenceMeasure) = _
      rw [Measure.map_map
        ((measurable_gaussianZigZagHorizonEndpoint initial horizon).comp
          measurable_gaussianZigZagHazardCons)
        measurable_gaussianZigZagHazardHeadTail]
      congr 1
      funext hazards
      simp [Function.comp_def]
    _ = Measure.map (gaussianZigZagFirstEventEndpoint initial horizon)
          (gaussianZigZagHazardMeasure.prod
            gaussianZigZagHazardSequenceMeasure) :=
      Measure.map_congr
        (gaussianZigZagHorizonEndpoint_cons_ae_eq_firstEvent initial horizon)

theorem measurable_gaussianZigZagEventState_joint (eventCount : ℕ) :
    Measurable (fun input : ZigZagState × (ℕ → NNReal) =>
      gaussianZigZagEventState input.1 input.2 eventCount) := by
  induction eventCount with
  | zero => exact measurable_fst
  | succ eventCount ih =>
      exact measurable_gaussianZigZagEventUpdate.comp
        (ih.prodMk ((measurable_pi_apply eventCount).comp measurable_snd))

theorem measurable_gaussianZigZagEventWaitTerm_joint (eventCount : ℕ) :
    Measurable (fun input : ZigZagState × (ℕ → NNReal) =>
      gaussianZigZagEventWaitTerm input.1 input.2 eventCount) := by
  unfold gaussianZigZagEventWaitTerm gaussianZigZagEventWait
  exact (measurable_gaussianZigZagWaitingNNReal.comp
    ((measurable_gaussianZigZagEventState_joint eventCount).prodMk
      ((measurable_pi_apply eventCount).comp measurable_snd))).coe_nnreal_real.ennreal_ofReal

theorem measurable_gaussianZigZagEventElapsed_joint (eventCount : ℕ) :
    Measurable (fun input : ZigZagState × (ℕ → NNReal) =>
      gaussianZigZagEventElapsed input.1 input.2 eventCount) := by
  unfold gaussianZigZagEventElapsed
  exact Finset.measurable_sum _ fun index _ =>
    measurable_gaussianZigZagEventWaitTerm_joint index

theorem measurableSet_gaussianZigZagEventCrossed_joint
    (horizon : NNReal) (eventCount : ℕ) :
    MeasurableSet {input : ZigZagState × (ℕ → NNReal) |
      gaussianZigZagEventCrossed input.1 horizon input.2 eventCount} := by
  unfold gaussianZigZagEventCrossed
  exact measurableSet_lt measurable_const
    (measurable_gaussianZigZagEventElapsed_joint eventCount)

theorem measurableSet_gaussianZigZagCrossingSearchPredicate_joint
    (horizon : NNReal) (eventCount : ℕ) :
    MeasurableSet {input : ZigZagState × (ℕ → NNReal) |
      gaussianZigZagCrossingSearchPredicate
        input.1 horizon input.2 eventCount} := by
  classical
  by_cases hzero : eventCount = 0
  · subst eventCount
    simp only [gaussianZigZagCrossingSearchPredicate, true_and]
    apply MeasurableSet.union
    · exact measurableSet_gaussianZigZagEventCrossed_joint horizon 0
    · have hexists : MeasurableSet
          {input : ZigZagState × (ℕ → NNReal) | ∃ count,
            gaussianZigZagEventCrossed input.1 horizon input.2 count} := by
        rw [show {input : ZigZagState × (ℕ → NNReal) | ∃ count,
            gaussianZigZagEventCrossed input.1 horizon input.2 count} =
            ⋃ count, {input | gaussianZigZagEventCrossed
              input.1 horizon input.2 count} by
          ext input
          simp]
        exact MeasurableSet.iUnion fun count =>
          measurableSet_gaussianZigZagEventCrossed_joint horizon count
      exact hexists.compl
  · simp only [gaussianZigZagCrossingSearchPredicate, hzero, false_and,
      or_false]
    exact measurableSet_gaussianZigZagEventCrossed_joint horizon eventCount

theorem measurable_gaussianZigZagHorizonEndpoint_joint (horizon : NNReal) :
    Measurable (fun input : ZigZagState × (ℕ → NNReal) =>
      gaussianZigZagHorizonEndpoint input.1 horizon input.2) := by
  classical
  let searchExists : ∀ input : ZigZagState × (ℕ → NNReal),
      ∃ eventCount, gaussianZigZagCrossingSearchPredicate
        input.1 horizon input.2 eventCount := fun input =>
    gaussianZigZagCrossingSearchPredicate_exists input.1 horizon input.2
  have hfamily : ∀ eventCount, Measurable
      (fun input : ZigZagState × (ℕ → NNReal) =>
        zigZagFlow
          (horizon - (gaussianZigZagEventElapsed input.1 input.2
            (eventCount - 1)).toNNReal)
          (gaussianZigZagEventState input.1 input.2 (eventCount - 1))) := by
    intro eventCount
    have hstate := measurable_gaussianZigZagEventState_joint (eventCount - 1)
    have helapsed := measurable_gaussianZigZagEventElapsed_joint (eventCount - 1)
    have htime : Measurable (fun input : ZigZagState × (ℕ → NNReal) =>
        horizon - (gaussianZigZagEventElapsed input.1 input.2
          (eventCount - 1)).toNNReal) :=
      measurable_const.sub helapsed.ennreal_toNNReal
    unfold zigZagFlow
    have hvelocity : Measurable
        (fun input : ZigZagState × (ℕ → NNReal) =>
          zigZagVelocity (gaussianZigZagEventState input.1 input.2
            (eventCount - 1)).2) := by
      unfold zigZagVelocity
      fun_prop
    exact hstate.fst.add (htime.coe_nnreal_real.mul hvelocity) |>.prodMk hstate.snd
  change Measurable (fun input =>
    (fun eventCount input => zigZagFlow
      (horizon - (gaussianZigZagEventElapsed input.1 input.2
        (eventCount - 1)).toNNReal)
      (gaussianZigZagEventState input.1 input.2 (eventCount - 1)))
      (Nat.find (searchExists input)) input)
  exact Measurable.find hfamily
    (measurableSet_gaussianZigZagCrossingSearchPredicate_joint horizon)
    searchExists

/-- Exact fixed-horizon standard-Gaussian Zig-Zag transition obtained by
sampling the infinite hazard stream and applying the nonexplosive stopping
construction. -/
noncomputable def gaussianZigZagHorizonKernel
    (horizon : NNReal) : Kernel ZigZagState ZigZagState :=
  Kernel.map
    (Kernel.prod Kernel.id
      (Kernel.const ZigZagState gaussianZigZagHazardSequenceMeasure))
    (fun input => gaussianZigZagHorizonEndpoint input.1 horizon input.2)

instance gaussianZigZagHorizonKernel.instIsMarkovKernel
    (horizon : NNReal) :
    IsMarkovKernel (gaussianZigZagHorizonKernel horizon) := by
  unfold gaussianZigZagHorizonKernel
  apply Kernel.IsMarkovKernel.map
  exact measurable_gaussianZigZagHorizonEndpoint_joint horizon

/-- Exact Gaussian Zig-Zag horizon transition expressed in signed-position
coordinates.  The same involution converts the signed input to physical
coordinates and the physical output back to signed coordinates. -/
noncomputable def gaussianZigZagSignedHorizonKernel
    (horizon : NNReal) : Kernel ZigZagState ZigZagState :=
  Kernel.map
    (Kernel.comap (gaussianZigZagHorizonKernel horizon)
      zigZagSignedCoordinate measurable_zigZagSignedCoordinate)
    zigZagSignedCoordinate

instance gaussianZigZagSignedHorizonKernel.instIsMarkovKernel
    (horizon : NNReal) :
    IsMarkovKernel (gaussianZigZagSignedHorizonKernel horizon) := by
  unfold gaussianZigZagSignedHorizonKernel
  apply Kernel.IsMarkovKernel.map
  exact measurable_zigZagSignedCoordinate

/-- A row of the signed horizon kernel is the signed pushforward of the
physical row started from the corresponding physical state. -/
theorem gaussianZigZagSignedHorizonKernel_apply
    (horizon : NNReal) (initial : ZigZagState) :
    gaussianZigZagSignedHorizonKernel horizon initial =
      (gaussianZigZagHorizonKernel horizon
        (zigZagSignedCoordinate initial)).map zigZagSignedCoordinate := by
  unfold gaussianZigZagSignedHorizonKernel
  rw [Kernel.map_apply _ measurable_zigZagSignedCoordinate,
    Kernel.comap_apply]

/-- Waiting time viewed from signed coordinates. -/
noncomputable def gaussianZigZagSignedWaitingNNReal
    (initial : ZigZagState) (hazard : NNReal) : NNReal :=
  gaussianZigZagWaitingNNReal (zigZagSignedCoordinate initial) hazard

/-- Accumulated event hazard over a signed-coordinate horizon. -/
noncomputable def gaussianZigZagSignedIntegratedRate
    (initial : ZigZagState) (horizon : NNReal) : NNReal :=
  ⟨gaussianZigZagIntegratedRate
      (zigZagSignedCoordinate initial).1
      (zigZagSignedCoordinate initial).2 (horizon : ℝ),
    gaussianZigZagIntegratedRate_nonneg _ _ horizon.coe_nonneg⟩

/-- Closed scalar form of the signed accumulated hazard. -/
theorem coe_gaussianZigZagSignedIntegratedRate
    (initial : ZigZagState) (horizon : NNReal) :
    (gaussianZigZagSignedIntegratedRate initial horizon : ℝ) =
      if 0 ≤ initial.1 then
        initial.1 * (horizon : ℝ) + (horizon : ℝ) ^ 2 / 2
      else if (horizon : ℝ) ≤ -initial.1 then 0
      else (initial.1 + (horizon : ℝ)) ^ 2 / 2 := by
  change gaussianZigZagIntegratedRate
      (zigZagSignedCoordinate initial).1
      (zigZagSignedCoordinate initial).2 (horizon : ℝ) = _
  unfold gaussianZigZagIntegratedRate
  change (if 0 ≤ zigZagSignedPosition (zigZagSignedCoordinate initial) then
      zigZagSignedPosition (zigZagSignedCoordinate initial) * (horizon : ℝ) +
        (horizon : ℝ) ^ 2 / 2
    else if (horizon : ℝ) ≤
        -zigZagSignedPosition (zigZagSignedCoordinate initial) then 0
    else (zigZagSignedPosition (zigZagSignedCoordinate initial) +
      (horizon : ℝ)) ^ 2 / 2) = _
  rw [zigZagSignedPosition_signedCoordinate]

/-- Accumulated signed hazard is the increase of the positive-half quadratic
potential along unit-speed translation. -/
theorem coe_gaussianZigZagSignedIntegratedRate_eq_positivePart
    (initial : ZigZagState) (horizon : NNReal) :
    (gaussianZigZagSignedIntegratedRate initial horizon : ℝ) =
      (max 0 (initial.1 + (horizon : ℝ))) ^ 2 / 2 -
        (max 0 initial.1) ^ 2 / 2 := by
  rw [coe_gaussianZigZagSignedIntegratedRate]
  by_cases hs : 0 ≤ initial.1
  · rw [if_pos hs, max_eq_right hs]
    have hsum : 0 ≤ initial.1 + (horizon : ℝ) :=
      add_nonneg hs horizon.coe_nonneg
    rw [max_eq_right hsum]
    ring
  · rw [if_neg hs]
    have hsNeg : initial.1 < 0 := lt_of_not_ge hs
    rw [max_eq_left (le_of_lt hsNeg)]
    by_cases hflat : (horizon : ℝ) ≤ -initial.1
    · rw [if_pos hflat]
      have hsum : initial.1 + (horizon : ℝ) ≤ 0 := by linarith
      rw [max_eq_left hsum]
      ring
    · rw [if_neg hflat]
      have hsum : 0 ≤ initial.1 + (horizon : ℝ) := by linarith
      rw [max_eq_right hsum]
      ring

/-- The canonical signed clock is before its event exactly while the fresh
exponential hazard exceeds the accumulated event rate. -/
theorem gaussianZigZagSignedIntegratedRate_lt_iff_horizon_lt_waiting
    (initial : ZigZagState) (horizon : NNReal) {hazard : NNReal}
    (hhazard : 0 < hazard) :
    gaussianZigZagSignedIntegratedRate initial horizon < hazard ↔
      horizon < gaussianZigZagSignedWaitingNNReal initial hazard := by
  change gaussianZigZagIntegratedRate
      (zigZagSignedCoordinate initial).1
      (zigZagSignedCoordinate initial).2 (horizon : ℝ) < (hazard : ℝ) ↔
    (horizon : ℝ) <
      (gaussianZigZagWaitingNNReal
        (zigZagSignedCoordinate initial) hazard : ℝ)
  rw [coe_gaussianZigZagWaitingNNReal]
  exact gaussianZigZagIntegratedRate_lt_iff_lt_waitingTime _ _
    horizon.coe_nonneg (by exact_mod_cast hhazard)

/-- Exact no-event probability for the canonical signed clock. -/
theorem gaussianZigZagSignedWaitingNNReal_survival
    (initial : ZigZagState) (horizon : NNReal) :
    gaussianZigZagHazardMeasure
        {hazard | horizon <
          gaussianZigZagSignedWaitingNNReal initial hazard} =
      ENNReal.ofReal
        (Real.exp (-(gaussianZigZagSignedIntegratedRate
          initial horizon : ℝ))) := by
  have hsets : {hazard | horizon <
        gaussianZigZagSignedWaitingNNReal initial hazard} =ᵐ[
      gaussianZigZagHazardMeasure]
      (Set.Ioi (gaussianZigZagSignedIntegratedRate initial horizon) :
        Set NNReal) := by
    filter_upwards [gaussianZigZagHazardMeasure_positive_ae]
      with hazard hhazard
    change (horizon < gaussianZigZagSignedWaitingNNReal initial hazard) =
      (gaussianZigZagSignedIntegratedRate initial horizon < hazard)
    exact propext
      (gaussianZigZagSignedIntegratedRate_lt_iff_horizon_lt_waiting
        initial horizon hhazard).symm
  rw [measure_congr hsets]
  exact gaussianZigZagHazardMeasure_Ioi
    (gaussianZigZagSignedIntegratedRate initial horizon)

/-- Event update viewed from signed coordinates. -/
noncomputable def gaussianZigZagSignedEventUpdate
    (initial : ZigZagState) (hazard : NNReal) : ZigZagState :=
  zigZagSignedCoordinate
    (gaussianZigZagEventUpdate (zigZagSignedCoordinate initial) hazard)

/-- Closed-form canonical event reset. It depends only on the current signed
position and the fresh exponential hazard, and flips the velocity label. -/
theorem gaussianZigZagSignedEventUpdate_eq
    (initial : ZigZagState) (hazard : NNReal) :
    gaussianZigZagSignedEventUpdate initial hazard =
      (if 0 ≤ initial.1 then
          -Real.sqrt (initial.1 ^ 2 + 2 * (hazard : ℝ))
        else -Real.sqrt (2 * (hazard : ℝ)), !initial.2) := by
  unfold gaussianZigZagSignedEventUpdate
  rw [zigZagSignedCoordinate_gaussianZigZagEventUpdate,
    zigZagSignedPosition_signedCoordinate]
  rfl

/-- At every genuine event epoch the signed position is negative, so the next
event reset depends only on the fresh hazard draw and flips velocity. -/
theorem gaussianZigZagSignedEventUpdate_eq_of_neg
    (initial : ZigZagState) (hazard : NNReal) (hinitial : initial.1 < 0) :
    gaussianZigZagSignedEventUpdate initial hazard =
      (-Real.sqrt (2 * (hazard : ℝ)), !initial.2) := by
  rw [gaussianZigZagSignedEventUpdate_eq, if_neg (not_le.mpr hinitial)]

/-- Embedded event-to-event kernel in canonical signed coordinates. -/
noncomputable def gaussianZigZagSignedEventKernel :
    Kernel ZigZagState ZigZagState :=
  Kernel.map
    (Kernel.prod Kernel.id
      (Kernel.const ZigZagState gaussianZigZagHazardMeasure))
    (fun input => gaussianZigZagSignedEventUpdate input.1 input.2)

instance gaussianZigZagSignedEventKernel.instIsMarkovKernel :
    IsMarkovKernel gaussianZigZagSignedEventKernel := by
  unfold gaussianZigZagSignedEventKernel
  apply Kernel.IsMarkovKernel.map
  unfold gaussianZigZagSignedEventUpdate
  exact measurable_zigZagSignedCoordinate.comp
    (measurable_gaussianZigZagEventUpdate.comp
      (measurable_zigZagSignedCoordinate.comp measurable_fst |>.prodMk
        measurable_snd))

/-- A signed event-kernel row is the pushforward of one fresh exponential
hazard through the canonical reset. -/
theorem gaussianZigZagSignedEventKernel_apply
    (initial : ZigZagState) :
    gaussianZigZagSignedEventKernel initial =
      Measure.map (gaussianZigZagSignedEventUpdate initial)
        gaussianZigZagHazardMeasure := by
  have hupdate : Measurable (fun input : ZigZagState × NNReal =>
      gaussianZigZagSignedEventUpdate input.1 input.2) := by
    unfold gaussianZigZagSignedEventUpdate
    exact measurable_zigZagSignedCoordinate.comp
      (measurable_gaussianZigZagEventUpdate.comp
        (measurable_zigZagSignedCoordinate.comp measurable_fst |>.prodMk
          measurable_snd))
  have hmk : Measurable (Prod.mk initial : NNReal → ZigZagState × NNReal) :=
    measurable_const.prodMk measurable_id
  unfold gaussianZigZagSignedEventKernel
  rw [Kernel.map_apply _ hupdate,
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
    Measure.dirac_prod, Measure.map_map hupdate hmk]
  rfl

/-- From a negative event-start position, the embedded row forgets that
position completely. -/
theorem gaussianZigZagSignedEventKernel_apply_of_neg
    (initial : ZigZagState) (hinitial : initial.1 < 0) :
    gaussianZigZagSignedEventKernel initial =
      Measure.map (fun hazard : NNReal =>
        (-Real.sqrt (2 * (hazard : ℝ)), !initial.2))
        gaussianZigZagHazardMeasure := by
  rw [gaussianZigZagSignedEventKernel_apply]
  apply Measure.map_congr
  filter_upwards [] with hazard
  exact gaussianZigZagSignedEventUpdate_eq_of_neg initial hazard hinitial

/-- Negative event-start position generated by one unit-exponential hazard. -/
noncomputable def gaussianZigZagNegativeRayleighReset (hazard : NNReal) : ℝ :=
  -Real.sqrt (2 * (hazard : ℝ))

theorem measurable_gaussianZigZagNegativeRayleighReset :
    Measurable gaussianZigZagNegativeRayleighReset := by
  unfold gaussianZigZagNegativeRayleighReset
  fun_prop

/-- Event-epoch signed-position law. -/
noncomputable def gaussianZigZagNegativeRayleighMeasure : Measure ℝ :=
  gaussianZigZagHazardMeasure.map gaussianZigZagNegativeRayleighReset

instance gaussianZigZagNegativeRayleighMeasure.instIsProbabilityMeasure :
    IsProbabilityMeasure gaussianZigZagNegativeRayleighMeasure := by
  constructor
  unfold gaussianZigZagNegativeRayleighMeasure
  rw [Measure.map_apply measurable_gaussianZigZagNegativeRayleighReset
    MeasurableSet.univ, Set.preimage_univ, measure_univ]

/-- Event-epoch positions are strictly negative almost surely. -/
theorem gaussianZigZagNegativeRayleighMeasure_negative_ae :
    ∀ᵐ position ∂gaussianZigZagNegativeRayleighMeasure, position < 0 := by
  unfold gaussianZigZagNegativeRayleighMeasure
  rw [ae_map_iff measurable_gaussianZigZagNegativeRayleighReset.aemeasurable
    measurableSet_Iio]
  filter_upwards [gaussianZigZagHazardMeasure_positive_ae]
    with hazard hhazard
  unfold gaussianZigZagNegativeRayleighReset
  exact neg_lt_zero.mpr (Real.sqrt_pos.2 (by positivity))

/-- Quadratic energy carried by a negative-Rayleigh reset position. -/
noncomputable def gaussianZigZagNegativeRayleighEnergy
    (position : ℝ) : NNReal :=
  Real.toNNReal (position ^ 2 / 2)

theorem measurable_gaussianZigZagNegativeRayleighEnergy :
    Measurable gaussianZigZagNegativeRayleighEnergy := by
  unfold gaussianZigZagNegativeRayleighEnergy
  fun_prop

/-- The reset transformation and quadratic-energy map are exact inverses on
nonnegative hazard draws. -/
@[simp] theorem gaussianZigZagNegativeRayleighEnergy_reset
    (hazard : NNReal) :
    gaussianZigZagNegativeRayleighEnergy
      (gaussianZigZagNegativeRayleighReset hazard) = hazard := by
  apply NNReal.eq
  unfold gaussianZigZagNegativeRayleighEnergy
    gaussianZigZagNegativeRayleighReset
  rw [Real.coe_toNNReal]
  · rw [neg_sq, Real.sq_sqrt (by positivity)]
    ring
  · positivity

/-- Pushing the negative-Rayleigh event position back through its quadratic
energy recovers the original unit-exponential hazard law. -/
theorem gaussianZigZagNegativeRayleighMeasure_map_energy :
    gaussianZigZagNegativeRayleighMeasure.map
        gaussianZigZagNegativeRayleighEnergy =
      gaussianZigZagHazardMeasure := by
  unfold gaussianZigZagNegativeRayleighMeasure
  rw [Measure.map_map measurable_gaussianZigZagNegativeRayleighEnergy
    measurable_gaussianZigZagNegativeRayleighReset]
  rw [show gaussianZigZagNegativeRayleighEnergy ∘
      gaussianZigZagNegativeRayleighReset = id by
    funext hazard
    exact gaussianZigZagNegativeRayleighEnergy_reset hazard,
    Measure.map_id]

/-- Quadratic energy threshold corresponding to a nonnegative signed
position radius. -/
noncomputable def gaussianZigZagRadiusEnergy (radius : NNReal) : NNReal :=
  ⟨(radius : ℝ) ^ 2 / 2, by positivity⟩

theorem gaussianZigZagNegativeRayleighReset_preimage_Iio_neg
    (radius : NNReal) :
    gaussianZigZagNegativeRayleighReset ⁻¹' Set.Iio (-(radius : ℝ)) =
      Set.Ioi (gaussianZigZagRadiusEnergy radius) := by
  ext hazard
  simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_Ioi]
  unfold gaussianZigZagNegativeRayleighReset gaussianZigZagRadiusEnergy
  have hradius : 0 ≤ (radius : ℝ) := radius.coe_nonneg
  have hrad : 0 ≤ 2 * (hazard : ℝ) := by positivity
  have hsqrtNonneg := Real.sqrt_nonneg (2 * (hazard : ℝ))
  have hsqrtSq : (Real.sqrt (2 * (hazard : ℝ))) ^ 2 =
      2 * (hazard : ℝ) := Real.sq_sqrt hrad
  constructor <;> intro h
  · have hlt : (radius : ℝ) < Real.sqrt (2 * (hazard : ℝ)) := by
      linarith
    change (radius : ℝ) ^ 2 / 2 < (hazard : ℝ)
    nlinarith
  · change (radius : ℝ) ^ 2 / 2 < (hazard : ℝ) at h
    nlinarith

/-- Conditional on a cycle extending beyond positive radius `r`, subtracting
the spent quadratic energy `r²/2` from its right-reset energy leaves a fresh
unit exponential law, scaled by the survival probability. -/
theorem gaussianZigZagNegativeRayleighMeasure_residual_energy
    (radius : NNReal) :
    Measure.map
        (fun position => gaussianZigZagNegativeRayleighEnergy position -
          gaussianZigZagRadiusEnergy radius)
        (gaussianZigZagNegativeRayleighMeasure.restrict
          (Set.Iio (-(radius : ℝ)))) =
      ENNReal.ofReal
          (Real.exp (-(gaussianZigZagRadiusEnergy radius : ℝ))) •
        gaussianZigZagHazardMeasure := by
  have hresidual : Measurable (fun position : ℝ =>
      gaussianZigZagNegativeRayleighEnergy position -
        gaussianZigZagRadiusEnergy radius) :=
    measurable_gaussianZigZagNegativeRayleighEnergy.sub measurable_const
  unfold gaussianZigZagNegativeRayleighMeasure
  rw [Measure.restrict_map measurable_gaussianZigZagNegativeRayleighReset
      measurableSet_Iio,
    gaussianZigZagNegativeRayleighReset_preimage_Iio_neg]
  rw [Measure.map_map hresidual
    measurable_gaussianZigZagNegativeRayleighReset]
  rw [show (fun position => gaussianZigZagNegativeRayleighEnergy position -
      gaussianZigZagRadiusEnergy radius) ∘
        gaussianZigZagNegativeRayleighReset =
      (fun hazard => hazard - gaussianZigZagRadiusEnergy radius) by
    funext hazard
    simp]
  exact gaussianZigZagHazardMeasure_residual_memoryless
    (gaussianZigZagRadiusEnergy radius)

/-- At a nonpositive occupied signed position the right reset is unconstrained
almost surely, so its quadratic energy is already a fresh unit exponential. -/
theorem gaussianZigZagNegativeRayleighMeasure_future_energy_of_nonpos
    (signed : ℝ) (hsigned : signed ≤ 0) :
    Measure.map gaussianZigZagNegativeRayleighEnergy
        (gaussianZigZagNegativeRayleighMeasure.restrict
          {right | signed < -right}) =
      gaussianZigZagHazardMeasure := by
  have hset : {right : ℝ | signed < -right} =ᵐ[
      gaussianZigZagNegativeRayleighMeasure] Set.univ := by
    filter_upwards [gaussianZigZagNegativeRayleighMeasure_negative_ae]
      with right hright
    change (signed < -right) = True
    exact propext ⟨fun _ => trivial, fun _ => by linarith⟩
  rw [Measure.restrict_congr_set hset, Measure.restrict_univ,
    gaussianZigZagNegativeRayleighMeasure_map_energy]

/-- Residual integrated hazard from an occupied signed position to the right
reset endpoint of its current regenerative cycle. -/
noncomputable def gaussianZigZagCycleResidualHazard
    (signed rightReset : ℝ) : NNReal :=
  gaussianZigZagNegativeRayleighEnergy rightReset -
    Real.toNNReal ((max 0 signed) ^ 2 / 2)

theorem measurable_gaussianZigZagCycleResidualHazard (signed : ℝ) :
    Measurable (gaussianZigZagCycleResidualHazard signed) := by
  unfold gaussianZigZagCycleResidualHazard
  exact measurable_gaussianZigZagNegativeRayleighEnergy.sub measurable_const

/-- On a genuine cycle interval, the nonnegative residual-clock definition
has the expected real quadratic-energy difference. -/
theorem coe_gaussianZigZagCycleResidualHazard
    (signed rightReset : ℝ) (hcover : signed < -rightReset) :
    (gaussianZigZagCycleResidualHazard signed rightReset : ℝ) =
      rightReset ^ 2 / 2 - (max 0 signed) ^ 2 / 2 := by
  unfold gaussianZigZagCycleResidualHazard
    gaussianZigZagNegativeRayleighEnergy
  have henergy : 0 ≤ rightReset ^ 2 / 2 := by positivity
  have hspent : 0 ≤ (max 0 signed) ^ 2 / 2 := by positivity
  have hle : (max 0 signed) ^ 2 / 2 ≤ rightReset ^ 2 / 2 := by
    by_cases hsigned : signed ≤ 0
    · rw [max_eq_left hsigned]
      simpa using henergy
    · rw [max_eq_right (le_of_not_ge hsigned)]
      have hright : signed < -rightReset := hcover
      have hsignedPos : 0 < signed := lt_of_not_ge hsigned
      nlinarith
  rw [NNReal.coe_sub]
  · rw [Real.coe_toNNReal _ henergy, Real.coe_toNNReal _ hspent]
  · exact Real.toNNReal_le_toNNReal hle

/-- The residual hazard stored by a covering cycle drives the canonical event
update exactly to that cycle's right reset. -/
theorem gaussianZigZagSignedEventUpdate_cycleResidual
    (signed rightReset : ℝ) (velocity : Bool)
    (hcover : signed < -rightReset) (hright : rightReset < 0) :
    gaussianZigZagSignedEventUpdate (signed, velocity)
        (gaussianZigZagCycleResidualHazard signed rightReset) =
      (rightReset, !velocity) := by
  rw [gaussianZigZagSignedEventUpdate_eq]
  change ((if 0 ≤ signed then
      -Real.sqrt (signed ^ 2 + 2 *
        (gaussianZigZagCycleResidualHazard signed rightReset : ℝ))
    else
      -Real.sqrt (2 *
        (gaussianZigZagCycleResidualHazard signed rightReset : ℝ))), !velocity) =
      (rightReset, !velocity)
  have hresidual := coe_gaussianZigZagCycleResidualHazard
    signed rightReset hcover
  by_cases hsigned : 0 ≤ signed
  · rw [if_pos hsigned]
    rw [max_eq_right hsigned] at hresidual
    congr 1
    rw [hresidual]
    have : signed ^ 2 + 2 * (rightReset ^ 2 / 2 - signed ^ 2 / 2) =
        rightReset ^ 2 := by ring
    rw [this, Real.sqrt_sq_eq_abs, abs_of_neg hright]
    simp
  · rw [if_neg hsigned]
    rw [max_eq_left (le_of_not_ge hsigned)] at hresidual
    congr 1
    rw [hresidual]
    have : 2 * (rightReset ^ 2 / 2 - 0 ^ 2 / 2) =
        rightReset ^ 2 := by ring
    rw [this, Real.sqrt_sq_eq_abs, abs_of_neg hright]
    simp

/-- The same residual clock rings after exactly the remaining geometric
distance to the right endpoint of the covering cycle. -/
theorem coe_gaussianZigZagSignedWaitingNNReal_cycleResidual
    (signed rightReset : ℝ) (velocity : Bool)
    (hcover : signed < -rightReset) (hright : rightReset < 0) :
    (gaussianZigZagSignedWaitingNNReal (signed, velocity)
        (gaussianZigZagCycleResidualHazard signed rightReset) : ℝ) =
      -rightReset - signed := by
  unfold gaussianZigZagSignedWaitingNNReal
  rw [coe_gaussianZigZagWaitingNNReal]
  unfold gaussianZigZagWaitingTime
  rw [show zigZagVelocity (zigZagSignedCoordinate (signed, velocity)).2 *
      (zigZagSignedCoordinate (signed, velocity)).1 = signed by
    exact zigZagSignedPosition_signedCoordinate (signed, velocity)]
  change (if 0 ≤ signed then
      Real.sqrt (signed ^ 2 + 2 *
        (gaussianZigZagCycleResidualHazard signed rightReset : ℝ)) - signed
    else -signed + Real.sqrt (2 *
      (gaussianZigZagCycleResidualHazard signed rightReset : ℝ))) = _
  have hresidual := coe_gaussianZigZagCycleResidualHazard
    signed rightReset hcover
  by_cases hsigned : 0 ≤ signed
  · rw [if_pos hsigned]
    rw [max_eq_right hsigned] at hresidual
    rw [hresidual]
    have : signed ^ 2 + 2 *
        (rightReset ^ 2 / 2 - signed ^ 2 / 2) = rightReset ^ 2 := by ring
    rw [this, Real.sqrt_sq_eq_abs, abs_of_neg hright]
  · rw [if_neg hsigned]
    rw [max_eq_left (le_of_not_ge hsigned)] at hresidual
    rw [hresidual]
    have : 2 * (rightReset ^ 2 / 2 - 0 ^ 2 / 2) =
        rightReset ^ 2 := by ring
    rw [this, Real.sqrt_sq_eq_abs, abs_of_neg hright]
    ring

/-- Remaining unit-speed time from an occupied cycle position to its right
endpoint. -/
noncomputable def gaussianZigZagCycleRemainingTime
    (signed rightReset : ℝ) : NNReal :=
  Real.toNNReal (-rightReset - signed)

theorem coe_gaussianZigZagCycleRemainingTime
    (signed rightReset : ℝ) (hcover : signed < -rightReset) :
    (gaussianZigZagCycleRemainingTime signed rightReset : ℝ) =
      -rightReset - signed := by
  unfold gaussianZigZagCycleRemainingTime
  rw [Real.coe_toNNReal]
  linarith

/-- Residual integrated hazard and remaining geometric cycle time describe
the same next-event clock. -/
theorem gaussianZigZagSignedWaitingNNReal_cycleResidual
    (signed rightReset : ℝ) (velocity : Bool)
    (hcover : signed < -rightReset) (hright : rightReset < 0) :
    gaussianZigZagSignedWaitingNNReal (signed, velocity)
        (gaussianZigZagCycleResidualHazard signed rightReset) =
      gaussianZigZagCycleRemainingTime signed rightReset := by
  apply NNReal.eq
  rw [coe_gaussianZigZagSignedWaitingNNReal_cycleResidual
      signed rightReset velocity hcover hright,
    coe_gaussianZigZagCycleRemainingTime signed rightReset hcover]
/-- Exact left tail of the negative-Rayleigh event-start position. -/
theorem gaussianZigZagNegativeRayleighMeasure_Iio_neg
    (radius : NNReal) :
    gaussianZigZagNegativeRayleighMeasure
        (Set.Iio (-(radius : ℝ))) =
      ENNReal.ofReal (Real.exp (-((radius : ℝ) ^ 2 / 2))) := by
  unfold gaussianZigZagNegativeRayleighMeasure
  rw [Measure.map_apply measurable_gaussianZigZagNegativeRayleighReset
    measurableSet_Iio]
  let threshold : NNReal := ⟨(radius : ℝ) ^ 2 / 2, by positivity⟩
  have hpre : gaussianZigZagNegativeRayleighReset ⁻¹'
      Set.Iio (-(radius : ℝ)) = Set.Ioi threshold := by
    ext hazard
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_Ioi]
    unfold gaussianZigZagNegativeRayleighReset threshold
    have hradius : 0 ≤ (radius : ℝ) := radius.coe_nonneg
    have hrad : 0 ≤ 2 * (hazard : ℝ) := by positivity
    have hsqrtNonneg := Real.sqrt_nonneg (2 * (hazard : ℝ))
    have hsqrtSq : (Real.sqrt (2 * (hazard : ℝ))) ^ 2 =
        2 * (hazard : ℝ) := Real.sq_sqrt hrad
    constructor <;> intro h
    · have hlt : (radius : ℝ) < Real.sqrt (2 * (hazard : ℝ)) := by
        linarith
      change (radius : ℝ) ^ 2 / 2 < (hazard : ℝ)
      nlinarith
    · change (radius : ℝ) ^ 2 / 2 < (hazard : ℝ) at h
      nlinarith
  rw [hpre, gaussianZigZagHazardMeasure_Ioi]
  rfl

/-- Pairs of consecutive negative-Rayleigh resets whose intervening
unit-speed cycle visits a supplied signed position. -/
def gaussianZigZagCycleCoverageSet (signed : ℝ) : Set (ℝ × ℝ) :=
  Set.Iio signed ×ˢ {right | signed < -right}

/-- A cycle covers a negative signed position with the Gaussian tail weight
at its magnitude. -/
theorem gaussianZigZagCycleCoverageMeasure_neg (radius : NNReal) :
    (gaussianZigZagNegativeRayleighMeasure.prod
      gaussianZigZagNegativeRayleighMeasure)
        (gaussianZigZagCycleCoverageSet (-(radius : ℝ))) =
      ENNReal.ofReal (Real.exp (-((radius : ℝ) ^ 2 / 2))) := by
  unfold gaussianZigZagCycleCoverageSet
  rw [Measure.prod_prod]
  have hright : {right : ℝ | -(radius : ℝ) < -right} =ᵐ[
      gaussianZigZagNegativeRayleighMeasure] Set.univ := by
    filter_upwards [gaussianZigZagNegativeRayleighMeasure_negative_ae]
      with right hright
    change (-(radius : ℝ) < -right) = True
    exact propext ⟨fun _ => trivial, fun _ => by linarith [radius.coe_nonneg]⟩
  rw [measure_congr hright, measure_univ, mul_one,
    gaussianZigZagNegativeRayleighMeasure_Iio_neg]

/-- A cycle covers a positive signed position with the same Gaussian tail
weight. -/
theorem gaussianZigZagCycleCoverageMeasure_pos (radius : NNReal) :
    (gaussianZigZagNegativeRayleighMeasure.prod
      gaussianZigZagNegativeRayleighMeasure)
        (gaussianZigZagCycleCoverageSet (radius : ℝ)) =
      ENNReal.ofReal (Real.exp (-((radius : ℝ) ^ 2 / 2))) := by
  unfold gaussianZigZagCycleCoverageSet
  rw [Measure.prod_prod]
  have hleft : Set.Iio (radius : ℝ) =ᵐ[
      gaussianZigZagNegativeRayleighMeasure] Set.univ := by
    filter_upwards [gaussianZigZagNegativeRayleighMeasure_negative_ae]
      with left hleft
    change (left < (radius : ℝ)) = True
    exact propext ⟨fun _ => trivial, fun _ => by linarith [radius.coe_nonneg]⟩
  have hright : {right : ℝ | (radius : ℝ) < -right} =
      Set.Iio (-(radius : ℝ)) := by
    ext right
    simp only [Set.mem_setOf_eq, Set.mem_Iio]
    constructor <;> intro h <;> linarith
  rw [measure_congr hleft, measure_univ, one_mul, hright,
    gaussianZigZagNegativeRayleighMeasure_Iio_neg]

/-- Unified cycle-coverage identity: the probability that a regenerative
cycle visits `signed` is exactly the unnormalized standard-Gaussian density. -/
theorem gaussianZigZagCycleCoverageMeasure (signed : ℝ) :
    (gaussianZigZagNegativeRayleighMeasure.prod
      gaussianZigZagNegativeRayleighMeasure)
        (gaussianZigZagCycleCoverageSet signed) =
      ENNReal.ofReal (Real.exp (-(signed ^ 2 / 2))) := by
  by_cases hs : 0 ≤ signed
  · let radius : NNReal := Real.toNNReal signed
    have hradius : (radius : ℝ) = signed := by
      exact Real.coe_toNNReal signed hs
    simpa [radius, hradius] using
      gaussianZigZagCycleCoverageMeasure_pos radius
  · let radius : NNReal := Real.toNNReal (-signed)
    have hneg : 0 ≤ -signed := neg_nonneg.mpr (le_of_not_ge hs)
    have hradius : (radius : ℝ) = -signed := by
      exact Real.coe_toNNReal (-signed) hneg
    simpa [radius, hradius] using
      gaussianZigZagCycleCoverageMeasure_neg radius

/-- Coverage density of a stationary regenerative cycle. The preceding
theorem identifies this with the probability that two consecutive event
resets straddle the supplied signed position. -/
noncomputable def gaussianZigZagCycleCoverageDensity (signed : ℝ) : ENNReal :=
  ENNReal.ofReal (Real.exp (-(signed ^ 2 / 2)))

theorem gaussianZigZagCycleCoverageDensity_eq_measure (signed : ℝ) :
    gaussianZigZagCycleCoverageDensity signed =
      (gaussianZigZagNegativeRayleighMeasure.prod
        gaussianZigZagNegativeRayleighMeasure)
          (gaussianZigZagCycleCoverageSet signed) := by
  exact (gaussianZigZagCycleCoverageMeasure signed).symm

/-- Pointwise Palm residual-clock identity. Restrict two independent resets
to cycles covering `signed`, then map the right reset to its residual hazard:
the result is the Gaussian coverage weight at `signed` times a fresh unit
exponential law. -/
theorem gaussianZigZagCycleResidualHazard_fiber (signed : ℝ) :
    Measure.map
        (fun resets : ℝ × ℝ =>
          gaussianZigZagCycleResidualHazard signed resets.2)
        ((gaussianZigZagNegativeRayleighMeasure.prod
          gaussianZigZagNegativeRayleighMeasure).restrict
            (gaussianZigZagCycleCoverageSet signed)) =
      gaussianZigZagCycleCoverageDensity signed •
        gaussianZigZagHazardMeasure := by
  let leftSet : Set ℝ := Set.Iio signed
  let rightSet : Set ℝ := {right | signed < -right}
  have hcoverage : gaussianZigZagCycleCoverageSet signed =
      leftSet ×ˢ rightSet := rfl
  rw [hcoverage, ← Measure.prod_restrict]
  change Measure.map
      (gaussianZigZagCycleResidualHazard signed ∘ Prod.snd)
      ((gaussianZigZagNegativeRayleighMeasure.restrict leftSet).prod
        (gaussianZigZagNegativeRayleighMeasure.restrict rightSet)) = _
  rw [← Measure.map_map
      (measurable_gaussianZigZagCycleResidualHazard signed) measurable_snd,
    Measure.map_snd_prod, Measure.map_smul]
  by_cases hsigned : signed ≤ 0
  · have hresidual : gaussianZigZagCycleResidualHazard signed =
        gaussianZigZagNegativeRayleighEnergy := by
      funext right
      unfold gaussianZigZagCycleResidualHazard
      rw [max_eq_left hsigned]
      simp
    rw [hresidual,
      gaussianZigZagNegativeRayleighMeasure_future_energy_of_nonpos
        signed hsigned]
    have hleft : gaussianZigZagNegativeRayleighMeasure leftSet =
        gaussianZigZagCycleCoverageDensity signed := by
      let radius : NNReal := Real.toNNReal (-signed)
      have hneg : 0 ≤ -signed := neg_nonneg.mpr hsigned
      have hradius : (radius : ℝ) = -signed :=
        Real.coe_toNNReal (-signed) hneg
      unfold leftSet gaussianZigZagCycleCoverageDensity
      simpa [radius, hradius] using
        gaussianZigZagNegativeRayleighMeasure_Iio_neg radius
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, hleft]
  · have hsignedPos : 0 < signed := lt_of_not_ge hsigned
    let radius : NNReal := Real.toNNReal signed
    have hradius : (radius : ℝ) = signed :=
      Real.coe_toNNReal signed (le_of_lt hsignedPos)
    have hright : rightSet = Set.Iio (-(radius : ℝ)) := by
      ext right
      simp only [rightSet, Set.mem_setOf_eq, Set.mem_Iio]
      rw [hradius]
      constructor <;> intro h <;> linarith
    have hresidual : gaussianZigZagCycleResidualHazard signed =
        fun right => gaussianZigZagNegativeRayleighEnergy right -
          gaussianZigZagRadiusEnergy radius := by
      funext right
      unfold gaussianZigZagCycleResidualHazard
      rw [max_eq_right (le_of_lt hsignedPos)]
      congr 1
      apply NNReal.eq
      calc
        (Real.toNNReal (signed ^ 2 / 2) : ℝ) = signed ^ 2 / 2 :=
          Real.coe_toNNReal _ (by positivity)
        _ = (gaussianZigZagRadiusEnergy radius : ℝ) := by
          change signed ^ 2 / 2 = (radius : ℝ) ^ 2 / 2
          rw [hradius]
    rw [hresidual, hright,
      gaussianZigZagNegativeRayleighMeasure_residual_energy radius]
    have hleftAE : leftSet =ᵐ[gaussianZigZagNegativeRayleighMeasure]
        Set.univ := by
      filter_upwards [gaussianZigZagNegativeRayleighMeasure_negative_ae]
        with left hleft
      change (left < signed) = True
      exact propext ⟨fun _ => trivial, fun _ => by linarith⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      measure_congr hleftAE, measure_univ, one_smul]
    unfold gaussianZigZagCycleCoverageDensity
    congr 2
    rw [show (gaussianZigZagRadiusEnergy radius : ℝ) = signed ^ 2 / 2 by
      change (radius : ℝ) ^ 2 / 2 = signed ^ 2 / 2
      rw [hradius]]

/-- Unnormalized position-occupation measure of a regenerative cycle. -/
noncomputable def gaussianZigZagCycleOccupationMeasure : Measure ℝ :=
  volume.withDensity gaussianZigZagCycleCoverageDensity

/-- The regenerative cycle occupation measure is `sqrt(2π)` times the
standard Gaussian probability law. -/
theorem gaussianZigZagCycleOccupationMeasure_eq_gaussian :
    gaussianZigZagCycleOccupationMeasure =
      ENNReal.ofReal (Real.sqrt (2 * Real.pi)) • gaussianReal 0 1 := by
  let normalizer : ℝ := Real.sqrt (2 * Real.pi)
  have hnormalizerPos : 0 < normalizer := Real.sqrt_pos.2 (by positivity)
  have hnormalizerNonneg : 0 ≤ normalizer := le_of_lt hnormalizerPos
  have hnormalizerNe : normalizer ≠ 0 := ne_of_gt hnormalizerPos
  have hdensity : gaussianZigZagCycleCoverageDensity =
      ENNReal.ofReal normalizer • gaussianPDF 0 1 := by
    funext signed
    simp only [gaussianZigZagCycleCoverageDensity, Pi.smul_apply,
      smul_eq_mul, gaussianPDF, gaussianPDFReal, NNReal.coe_one,
      mul_one, sub_zero]
    rw [← ENNReal.ofReal_mul hnormalizerNonneg]
    congr 1
    change Real.exp (-(signed ^ 2 / 2)) =
      normalizer * ((Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp (-signed ^ 2 / 2))
    change Real.exp (-(signed ^ 2 / 2)) =
      normalizer * (normalizer⁻¹ * Real.exp (-signed ^ 2 / 2))
    rw [← mul_assoc, mul_inv_cancel₀ hnormalizerNe, one_mul]
    congr 2
    ring
  unfold gaussianZigZagCycleOccupationMeasure
  rw [hdensity, withDensity_smul,
    ← gaussianReal_of_var_ne_zero (0 : ℝ) (by norm_num : (1 : NNReal) ≠ 0)]
  exact measurable_gaussianPDF 0 1

/-- Mean regenerative-cycle duration, equivalently the total mass of the
unnormalized cycle occupation measure. -/
noncomputable def gaussianZigZagCycleMeanDuration : ENNReal :=
  ENNReal.ofReal (Real.sqrt (2 * Real.pi))

theorem gaussianZigZagCycleMeanDuration_ne_zero :
    gaussianZigZagCycleMeanDuration ≠ 0 := by
  unfold gaussianZigZagCycleMeanDuration
  exact ne_of_gt (ENNReal.ofReal_pos.mpr
    (Real.sqrt_pos.2 (by positivity)))

theorem gaussianZigZagCycleMeanDuration_ne_top :
    gaussianZigZagCycleMeanDuration ≠ ∞ := by
  unfold gaussianZigZagCycleMeanDuration
  exact ENNReal.ofReal_ne_top

/-- Normalized regenerative position-occupation law. -/
noncomputable def gaussianZigZagNormalizedCycleOccupation : Measure ℝ :=
  gaussianZigZagCycleMeanDuration⁻¹ •
    gaussianZigZagCycleOccupationMeasure

theorem gaussianZigZagNormalizedCycleOccupation_eq_gaussian :
    gaussianZigZagNormalizedCycleOccupation = gaussianReal 0 1 := by
  unfold gaussianZigZagNormalizedCycleOccupation
  rw [gaussianZigZagCycleOccupationMeasure_eq_gaussian]
  change gaussianZigZagCycleMeanDuration⁻¹ •
      (gaussianZigZagCycleMeanDuration • gaussianReal 0 1) = _
  rw [smul_smul]
  rw [ENNReal.inv_mul_cancel
    gaussianZigZagCycleMeanDuration_ne_zero
    gaussianZigZagCycleMeanDuration_ne_top, one_smul]

/-- Adding the independent uniform velocity label to normalized cycle
occupation recovers the exact Gaussian Zig-Zag target. -/
theorem gaussianZigZagNormalizedCycleOccupation_phase_eq_target :
    gaussianZigZagNormalizedCycleOccupation.prod
        zigZagVelocityProbability = gaussianZigZagTarget := by
  rw [gaussianZigZagNormalizedCycleOccupation_eq_gaussian]
  rfl

/-- Unit-density literal time occupation of the interval between two
consecutive negative-Rayleigh reset positions. -/
noncomputable def gaussianZigZagCycleIntervalDensity
    (resets : ℝ × ℝ) (signed : ℝ) : ENNReal :=
  if signed ∈ Set.Ioo resets.1 (-resets.2) then 1 else 0

theorem measurable_uncurry_gaussianZigZagCycleIntervalDensity :
    Measurable (Function.uncurry gaussianZigZagCycleIntervalDensity) := by
  unfold gaussianZigZagCycleIntervalDensity Function.uncurry
  apply Measurable.ite
  · exact (measurableSet_lt (measurable_fst.fst) measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_fst.snd.neg))
  · exact measurable_const
  · exact measurable_const

/-- Kernel whose row is unnormalized Lebesgue time occupation of one
unit-speed regenerative cycle. Invalid endpoint pairs give the zero measure;
they are null under the negative-Rayleigh reset law. -/
noncomputable def gaussianZigZagCycleIntervalKernel :
    Kernel (ℝ × ℝ) ℝ :=
  (Kernel.const (ℝ × ℝ) (volume : Measure ℝ)).withDensity
    gaussianZigZagCycleIntervalDensity

instance gaussianZigZagCycleIntervalKernel.instIsSFiniteKernel :
    IsSFiniteKernel gaussianZigZagCycleIntervalKernel := by
  unfold gaussianZigZagCycleIntervalKernel
  apply Kernel.IsSFiniteKernel.withDensity
  intro resets signed
  unfold gaussianZigZagCycleIntervalDensity
  split_ifs <;> simp

/-- Each literal cycle-occupation row is Lebesgue measure restricted to the
cycle interval. -/
theorem gaussianZigZagCycleIntervalKernel_apply (resets : ℝ × ℝ) :
    gaussianZigZagCycleIntervalKernel resets =
      volume.restrict (Set.Ioo resets.1 (-resets.2)) := by
  unfold gaussianZigZagCycleIntervalKernel
  rw [Kernel.withDensity_apply _
    measurable_uncurry_gaussianZigZagCycleIntervalDensity,
    Kernel.const_apply]
  rw [show gaussianZigZagCycleIntervalDensity resets =
      (Set.Ioo resets.1 (-resets.2)).indicator (fun _ => 1) by
    funext signed
    by_cases hsigned : signed ∈ Set.Ioo resets.1 (-resets.2) <;>
      simp [gaussianZigZagCycleIntervalDensity, hsigned],
    withDensity_indicator measurableSet_Ioo]
  change (volume.restrict (Set.Ioo resets.1 (-resets.2))).withDensity
      (1 : ℝ → ENNReal) = _
  exact withDensity_one

/-- Integrating literal interval membership over two independent resets gives
the previously computed cycle-coverage density. -/
theorem lintegral_gaussianZigZagCycleIntervalDensity (signed : ℝ) :
    (∫⁻ resets, gaussianZigZagCycleIntervalDensity resets signed
      ∂gaussianZigZagNegativeRayleighMeasure.prod
        gaussianZigZagNegativeRayleighMeasure) =
      gaussianZigZagCycleCoverageDensity signed := by
  rw [show (fun resets => gaussianZigZagCycleIntervalDensity resets signed) =
      (gaussianZigZagCycleCoverageSet signed).indicator (fun _ => 1) by
    funext resets
    by_cases hresets : resets.1 < signed ∧ signed < -resets.2 <;>
      simp [gaussianZigZagCycleIntervalDensity,
        gaussianZigZagCycleCoverageSet, hresets]]
  rw [lintegral_indicator]
  · simp [gaussianZigZagCycleCoverageDensity_eq_measure]
  · unfold gaussianZigZagCycleCoverageSet
    exact measurableSet_Iio.prod
      (measurableSet_lt measurable_const measurable_id.neg)

/-- Set-integral form of the pointwise Palm fiber identity. -/
theorem setLIntegral_gaussianZigZagCycleResidualHazard
    (signed : ℝ) {event : Set NNReal} (hevent : MeasurableSet event) :
    (∫⁻ resets in
        (fun resets : ℝ × ℝ =>
          gaussianZigZagCycleResidualHazard signed resets.2) ⁻¹' event,
        gaussianZigZagCycleIntervalDensity resets signed
      ∂gaussianZigZagNegativeRayleighMeasure.prod
        gaussianZigZagNegativeRayleighMeasure) =
      gaussianZigZagCycleCoverageDensity signed *
        gaussianZigZagHazardMeasure event := by
  let resetPairs := gaussianZigZagNegativeRayleighMeasure.prod
    gaussianZigZagNegativeRayleighMeasure
  have hpre : MeasurableSet
      ((fun resets : ℝ × ℝ =>
        gaussianZigZagCycleResidualHazard signed resets.2) ⁻¹' event) :=
    ((measurable_gaussianZigZagCycleResidualHazard signed).comp
      (measurable_snd : Measurable (Prod.snd : ℝ × ℝ → ℝ))) hevent
  have hmeas : Measurable (fun resets : ℝ × ℝ =>
      gaussianZigZagCycleResidualHazard signed resets.2) :=
    (measurable_gaussianZigZagCycleResidualHazard signed).comp
      (measurable_snd : Measurable (Prod.snd : ℝ × ℝ → ℝ))
  have hfiber := congrArg (fun measure : Measure NNReal => measure event)
    (gaussianZigZagCycleResidualHazard_fiber signed)
  rw [Measure.map_apply hmeas hevent,
    Measure.restrict_apply hpre, Measure.smul_apply, smul_eq_mul] at hfiber
  rw [show (fun resets => gaussianZigZagCycleIntervalDensity resets signed) =
      (gaussianZigZagCycleCoverageSet signed).indicator (fun _ => 1) by
    funext resets
    by_cases hresets : resets.1 < signed ∧ signed < -resets.2 <;>
      simp [gaussianZigZagCycleIntervalDensity,
        gaussianZigZagCycleCoverageSet, hresets]]
  have hcoverage : MeasurableSet (gaussianZigZagCycleCoverageSet signed) := by
    unfold gaussianZigZagCycleCoverageSet
    exact measurableSet_Iio.prod
      (measurableSet_lt measurable_const measurable_id.neg)
  rw [lintegral_indicator hcoverage]
  simp only [lintegral_one]
  simpa [Measure.restrict_apply, hcoverage, hpre, Set.inter_comm] using hfiber

/-- Tonelli identifies the average literal interval-time occupation of two
independent consecutive resets with the coverage-density occupation measure. -/
theorem gaussianZigZagCycleIntervalKernel_comp_eq_occupation :
    gaussianZigZagCycleIntervalKernel ∘ₘ
        (gaussianZigZagNegativeRayleighMeasure.prod
          gaussianZigZagNegativeRayleighMeasure) =
      gaussianZigZagCycleOccupationMeasure := by
  let resetPairs := gaussianZigZagNegativeRayleighMeasure.prod
    gaussianZigZagNegativeRayleighMeasure
  ext event hevent
  rw [Measure.bind_apply hevent (Kernel.aemeasurable _)]
  simp_rw [gaussianZigZagCycleIntervalKernel,
    Kernel.withDensity_apply'
      (Kernel.const (ℝ × ℝ) (volume : Measure ℝ))
      measurable_uncurry_gaussianZigZagCycleIntervalDensity,
    Kernel.const_apply]
  unfold gaussianZigZagCycleOccupationMeasure
  rw [withDensity_apply _ hevent]
  have htonelli :
      (∫⁻ resets, ∫⁻ signed in event,
          gaussianZigZagCycleIntervalDensity resets signed ∂volume
        ∂resetPairs) =
        ∫⁻ signed in event, ∫⁻ resets,
          gaussianZigZagCycleIntervalDensity resets signed ∂resetPairs
          ∂volume := by
    let density : ((ℝ × ℝ) × ℝ) → ENNReal := fun input =>
      gaussianZigZagCycleIntervalDensity input.1 input.2
    have hdensity : Measurable density :=
      measurable_uncurry_gaussianZigZagCycleIntervalDensity
    calc
      (∫⁻ resets, ∫⁻ signed in event,
          gaussianZigZagCycleIntervalDensity resets signed ∂volume
        ∂resetPairs) =
          ∫⁻ input in Set.univ ×ˢ event, density input
            ∂resetPairs.prod volume := by
          rw [setLIntegral_prod density
            (hdensity.aemeasurable.restrict)]
          simp [density]
      _ = ∫⁻ signed in event, ∫⁻ resets in Set.univ,
          density (resets, signed) ∂resetPairs ∂volume :=
        setLIntegral_prod_symm density (hdensity.aemeasurable.restrict)
      _ = ∫⁻ signed in event, ∫⁻ resets,
          gaussianZigZagCycleIntervalDensity resets signed ∂resetPairs
          ∂volume := by simp [density]
  rw [htonelli]
  apply setLIntegral_congr_fun hevent
  intro signed _
  exact lintegral_gaussianZigZagCycleIntervalDensity signed

/-- The averaged literal cycle interval has total mass equal to the mean
cycle duration `sqrt(2π)`. -/
theorem gaussianZigZagCycleIntervalKernel_comp_apply_univ :
    (gaussianZigZagCycleIntervalKernel ∘ₘ
      (gaussianZigZagNegativeRayleighMeasure.prod
        gaussianZigZagNegativeRayleighMeasure)) Set.univ =
      gaussianZigZagCycleMeanDuration := by
  rw [gaussianZigZagCycleIntervalKernel_comp_eq_occupation,
    gaussianZigZagCycleOccupationMeasure_eq_gaussian,
    Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rfl

/-- Normalizing the averaged literal cycle-time measure gives the standard
Gaussian position law. -/
theorem gaussianZigZagNormalizedLiteralCycleOccupation_eq_gaussian :
    gaussianZigZagCycleMeanDuration⁻¹ •
        (gaussianZigZagCycleIntervalKernel ∘ₘ
          (gaussianZigZagNegativeRayleighMeasure.prod
            gaussianZigZagNegativeRayleighMeasure)) =
      gaussianReal 0 1 := by
  rw [gaussianZigZagCycleIntervalKernel_comp_eq_occupation]
  exact gaussianZigZagNormalizedCycleOccupation_eq_gaussian

/-- The normalized literal regenerative-cycle law, with its independent
uniform velocity label, is exactly the signed Gaussian Zig-Zag target. -/
theorem gaussianZigZagNormalizedLiteralCycleOccupation_phase_eq_target :
    (gaussianZigZagCycleMeanDuration⁻¹ •
        (gaussianZigZagCycleIntervalKernel ∘ₘ
          (gaussianZigZagNegativeRayleighMeasure.prod
            gaussianZigZagNegativeRayleighMeasure))).prod
      zigZagVelocityProbability = gaussianZigZagTarget := by
  rw [gaussianZigZagNormalizedLiteralCycleOccupation_eq_gaussian]
  rfl

/-- Length-biased stationary regenerative cycle with a literal uniformly
time-occupied signed position, represented as a normalized composition
product. -/
noncomputable def gaussianZigZagStationaryCycleMeasure :
    Measure ((ℝ × ℝ) × ℝ) :=
  gaussianZigZagCycleMeanDuration⁻¹ •
    ((gaussianZigZagNegativeRayleighMeasure.prod
      gaussianZigZagNegativeRayleighMeasure) ⊗ₘ
        gaussianZigZagCycleIntervalKernel)

/-- The occupied-position marginal of the stationary regenerative cycle is
the standard Gaussian law. -/
theorem gaussianZigZagStationaryCycleMeasure_snd :
    gaussianZigZagStationaryCycleMeasure.snd = gaussianReal 0 1 := by
  unfold gaussianZigZagStationaryCycleMeasure Measure.snd
  rw [Measure.map_smul, ← Measure.snd,
    Measure.snd_compProd]
  exact gaussianZigZagNormalizedLiteralCycleOccupation_eq_gaussian

instance gaussianZigZagStationaryCycleMeasure.instIsProbabilityMeasure :
    IsProbabilityMeasure gaussianZigZagStationaryCycleMeasure := by
  constructor
  have hmarginal := congrArg (fun measure : Measure ℝ => measure Set.univ)
    gaussianZigZagStationaryCycleMeasure_snd
  simpa [Measure.snd_apply MeasurableSet.univ] using hmarginal

/-- Read the occupied signed position and its remaining integrated hazard
from a stationary length-biased regenerative cycle. -/
noncomputable def gaussianZigZagStationaryCycleResidualMap
    (sample : (ℝ × ℝ) × ℝ) : ℝ × NNReal :=
  (sample.2,
    gaussianZigZagCycleResidualHazard sample.2 sample.1.2)

theorem measurable_gaussianZigZagStationaryCycleResidualMap :
    Measurable gaussianZigZagStationaryCycleResidualMap := by
  unfold gaussianZigZagStationaryCycleResidualMap
    gaussianZigZagCycleResidualHazard
  have henergy : Measurable (fun sample : (ℝ × ℝ) × ℝ =>
      gaussianZigZagNegativeRayleighEnergy sample.1.2) :=
    measurable_gaussianZigZagNegativeRayleighEnergy.comp
      measurable_fst.snd
  have hspent : Measurable (fun sample : (ℝ × ℝ) × ℝ =>
      Real.toNNReal ((max 0 sample.2) ^ 2 / 2)) := by
    fun_prop
  exact measurable_snd.prodMk (henergy.sub hspent)

/-- Position/residual-hazard Palm pushforward of the stationary cycle law. -/
noncomputable def gaussianZigZagStationaryPositionResidualMeasure :
    Measure (ℝ × NNReal) :=
  gaussianZigZagStationaryCycleMeasure.map
    gaussianZigZagStationaryCycleResidualMap

instance gaussianZigZagStationaryPositionResidualMeasure.instIsProbabilityMeasure :
    IsProbabilityMeasure gaussianZigZagStationaryPositionResidualMeasure := by
  constructor
  unfold gaussianZigZagStationaryPositionResidualMeasure
  rw [Measure.map_apply
    measurable_gaussianZigZagStationaryCycleResidualMap
    MeasurableSet.univ, Set.preimage_univ, measure_univ]

set_option maxHeartbeats 1600000 in
/-- Under stationary length-biased cycle occupation, signed position and
remaining integrated hazard are independent, with standard Gaussian and unit
exponential laws respectively. -/
theorem gaussianZigZagStationaryPositionResidualMeasure_eq_prod :
    gaussianZigZagStationaryPositionResidualMeasure =
      (gaussianReal 0 1).prod gaussianZigZagHazardMeasure := by
  apply Measure.ext_prod
  intro positions hazards hpositions hhazards
  let resetPairs := gaussianZigZagNegativeRayleighMeasure.prod
    gaussianZigZagNegativeRayleighMeasure
  let jointEvent : Set ((ℝ × ℝ) × ℝ) :=
    gaussianZigZagStationaryCycleResidualMap ⁻¹' (positions ×ˢ hazards)
  have hjointEvent : MeasurableSet jointEvent :=
    measurable_gaussianZigZagStationaryCycleResidualMap
      (hpositions.prod hhazards)
  rw [Measure.prod_prod]
  unfold gaussianZigZagStationaryPositionResidualMeasure
  rw [Measure.map_apply measurable_gaussianZigZagStationaryCycleResidualMap
    (hpositions.prod hhazards)]
  unfold gaussianZigZagStationaryCycleMeasure
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.compProd_apply hjointEvent]
  have hrow (resets : ℝ × ℝ) :
      gaussianZigZagCycleIntervalKernel resets
          (Prod.mk resets ⁻¹' jointEvent) =
        ∫⁻ signed in positions ∩
            (fun signed : ℝ =>
              gaussianZigZagCycleResidualHazard signed resets.2) ⁻¹' hazards,
          gaussianZigZagCycleIntervalDensity resets signed ∂volume := by
    rw [gaussianZigZagCycleIntervalKernel,
      Kernel.withDensity_apply'
        (Kernel.const (ℝ × ℝ) (volume : Measure ℝ))
        measurable_uncurry_gaussianZigZagCycleIntervalDensity,
      Kernel.const_apply]
    congr 1
  simp_rw [hrow]
  have htonelli :
      (∫⁻ resets, ∫⁻ signed in positions ∩
          (fun signed : ℝ =>
            gaussianZigZagCycleResidualHazard signed resets.2) ⁻¹' hazards,
          gaussianZigZagCycleIntervalDensity resets signed ∂volume
        ∂resetPairs) =
        ∫⁻ signed in positions,
          ∫⁻ resets in
            (fun resets : ℝ × ℝ =>
              gaussianZigZagCycleResidualHazard signed resets.2) ⁻¹' hazards,
            gaussianZigZagCycleIntervalDensity resets signed ∂resetPairs
          ∂volume := by
    let density : ((ℝ × ℝ) × ℝ) → ENNReal := fun input =>
      gaussianZigZagCycleIntervalDensity input.1 input.2
    have hdensity : Measurable density :=
      measurable_uncurry_gaussianZigZagCycleIntervalDensity
    have hresidual : Measurable (fun input : (ℝ × ℝ) × ℝ =>
        gaussianZigZagCycleResidualHazard input.2 input.1.2) := by
      unfold gaussianZigZagCycleResidualHazard
      have henergy : Measurable (fun input : (ℝ × ℝ) × ℝ =>
          gaussianZigZagNegativeRayleighEnergy input.1.2) :=
        measurable_gaussianZigZagNegativeRayleighEnergy.comp
          measurable_fst.snd
      have hspent : Measurable (fun input : (ℝ × ℝ) × ℝ =>
          Real.toNNReal ((max 0 input.2) ^ 2 / 2)) := by
        fun_prop
      exact henergy.sub hspent
    let event : Set ((ℝ × ℝ) × ℝ) :=
      {input | input.2 ∈ positions ∧
        gaussianZigZagCycleResidualHazard input.2 input.1.2 ∈ hazards}
    have hevent : MeasurableSet event :=
      (hpositions.preimage measurable_snd).inter
        (hhazards.preimage hresidual)
    let integrand : ((ℝ × ℝ) × ℝ) → ENNReal :=
      event.indicator density
    have hintegrand : Measurable integrand :=
      hdensity.indicator hevent
    have hswap := lintegral_lintegral_swap
      (μ := resetPairs) (ν := (volume : Measure ℝ))
      (f := fun resets signed => integrand (resets, signed))
      hintegrand.aemeasurable
    have hleft :
        (∫⁻ resets, ∫⁻ signed in positions ∩
            (fun signed : ℝ =>
              gaussianZigZagCycleResidualHazard signed resets.2) ⁻¹' hazards,
            gaussianZigZagCycleIntervalDensity resets signed ∂volume
          ∂resetPairs) =
          ∫⁻ resets, ∫⁻ signed, integrand (resets, signed) ∂volume
            ∂resetPairs := by
      apply lintegral_congr
      intro resets
      have hfixed : Measurable (fun signed : ℝ =>
          gaussianZigZagCycleResidualHazard signed resets.2) :=
        hresidual.comp
          ((measurable_const : Measurable (fun _ : ℝ => resets)).prodMk
            measurable_id)
      have hset : MeasurableSet (positions ∩
          (fun signed : ℝ =>
            gaussianZigZagCycleResidualHazard signed resets.2) ⁻¹' hazards) :=
        hpositions.inter (hhazards.preimage hfixed)
      rw [← lintegral_indicator hset]
      apply lintegral_congr
      intro signed
      by_cases hsigned : signed ∈ positions <;>
        by_cases hresidualMem :
          gaussianZigZagCycleResidualHazard signed resets.2 ∈ hazards <;>
        simp [integrand, event, density, hsigned, hresidualMem]
    have hright :
        (∫⁻ signed, ∫⁻ resets, integrand (resets, signed) ∂resetPairs
          ∂volume) =
        ∫⁻ signed in positions,
          ∫⁻ resets in
            (fun resets : ℝ × ℝ =>
              gaussianZigZagCycleResidualHazard signed resets.2) ⁻¹' hazards,
            gaussianZigZagCycleIntervalDensity resets signed ∂resetPairs
          ∂volume := by
      rw [← lintegral_indicator hpositions]
      apply lintegral_congr
      intro signed
      by_cases hsigned : signed ∈ positions
      · simp only [Set.indicator_of_mem hsigned]
        have hset : MeasurableSet
            ((fun resets : ℝ × ℝ =>
              gaussianZigZagCycleResidualHazard signed resets.2) ⁻¹' hazards) :=
          hhazards.preimage
            ((measurable_gaussianZigZagCycleResidualHazard signed).comp
              (measurable_snd : Measurable (Prod.snd : ℝ × ℝ → ℝ)))
        rw [← lintegral_indicator hset]
        apply lintegral_congr
        intro resets
        by_cases hresidualMem :
            gaussianZigZagCycleResidualHazard signed resets.2 ∈ hazards <;>
          simp [integrand, event, density, hsigned, hresidualMem]
      · simp [integrand, event, density, hsigned]
    calc
      _ = ∫⁻ resets, ∫⁻ signed, integrand (resets, signed) ∂volume
          ∂resetPairs := hleft
      _ = ∫⁻ signed, ∫⁻ resets, integrand (resets, signed) ∂resetPairs
          ∂volume := hswap
      _ = _ := hright
  rw [htonelli]
  dsimp [resetPairs]
  simp_rw [setLIntegral_gaussianZigZagCycleResidualHazard _ hhazards]
  rw [lintegral_mul_const _ (by
    unfold gaussianZigZagCycleCoverageDensity
    fun_prop)]
  have hcoverage :
      (∫⁻ signed in positions,
        gaussianZigZagCycleCoverageDensity signed ∂volume) =
        gaussianZigZagCycleOccupationMeasure positions := by
    unfold gaussianZigZagCycleOccupationMeasure
    rw [withDensity_apply _ hpositions]
  rw [hcoverage]
  rw [gaussianZigZagCycleOccupationMeasure_eq_gaussian,
    Measure.smul_apply, smul_eq_mul]
  change gaussianZigZagCycleMeanDuration⁻¹ *
      ((gaussianZigZagCycleMeanDuration * gaussianReal 0 1 positions) *
        gaussianZigZagHazardMeasure hazards) = _
  calc
    _ = (gaussianZigZagCycleMeanDuration⁻¹ *
          gaussianZigZagCycleMeanDuration) *
        (gaussianReal 0 1 positions *
          gaussianZigZagHazardMeasure hazards) := by ac_rfl
    _ = _ := by
      rw [ENNReal.inv_mul_cancel
        gaussianZigZagCycleMeanDuration_ne_zero
        gaussianZigZagCycleMeanDuration_ne_top, one_mul]

/-- Reordering position, residual hazard, and velocity turns the Palm product
law into the exact phase-target/fresh-clock product law. -/
theorem gaussianZigZagStationaryPositionResidualVelocity_reorder :
    Measure.map
        (fun input : (ℝ × NNReal) × Bool =>
          ((input.1.1, input.2), input.1.2))
        (gaussianZigZagStationaryPositionResidualMeasure.prod
          zigZagVelocityProbability) =
      gaussianZigZagTarget.prod gaussianZigZagHazardMeasure := by
  rw [gaussianZigZagStationaryPositionResidualMeasure_eq_prod]
  let assoc₁ : ((ℝ × NNReal) × Bool) ≃ᵐ (ℝ × (NNReal × Bool)) :=
    MeasurableEquiv.prodAssoc
  let swap₂ : (ℝ × (NNReal × Bool)) → (ℝ × (Bool × NNReal)) :=
    Prod.map id Prod.swap
  let assoc₃ : (ℝ × (Bool × NNReal)) ≃ᵐ ((ℝ × Bool) × NNReal) :=
    MeasurableEquiv.prodAssoc.symm
  have hassoc₁ : Measure.map assoc₁
      (((gaussianReal 0 1).prod gaussianZigZagHazardMeasure).prod
        zigZagVelocityProbability) =
      (gaussianReal 0 1).prod
        (gaussianZigZagHazardMeasure.prod zigZagVelocityProbability) :=
    (MeasureTheory.measurePreserving_prodAssoc
      (gaussianReal 0 1) gaussianZigZagHazardMeasure
      zigZagVelocityProbability).map_eq
  have hswap₂ : Measure.map swap₂
      ((gaussianReal 0 1).prod
        (gaussianZigZagHazardMeasure.prod zigZagVelocityProbability)) =
      (gaussianReal 0 1).prod
        (zigZagVelocityProbability.prod gaussianZigZagHazardMeasure) := by
    unfold swap₂
    rw [← Measure.map_prod_map (gaussianReal 0 1)
      (gaussianZigZagHazardMeasure.prod zigZagVelocityProbability)
      measurable_id measurable_swap, Measure.map_id, Measure.prod_swap]
  have hassoc₃ : Measure.map assoc₃
      ((gaussianReal 0 1).prod
        (zigZagVelocityProbability.prod gaussianZigZagHazardMeasure)) =
      ((gaussianReal 0 1).prod zigZagVelocityProbability).prod
        gaussianZigZagHazardMeasure :=
    (MeasureTheory.measurePreserving_prodAssoc
      (gaussianReal 0 1) zigZagVelocityProbability
      gaussianZigZagHazardMeasure).symm.map_eq
  have hcomposition :
      (fun input : (ℝ × NNReal) × Bool =>
        ((input.1.1, input.2), input.1.2)) =
      assoc₃ ∘ swap₂ ∘ assoc₁ := rfl
  rw [hcomposition]
  calc
    Measure.map (assoc₃ ∘ swap₂ ∘ assoc₁)
        (((gaussianReal 0 1).prod gaussianZigZagHazardMeasure).prod
          zigZagVelocityProbability) =
      Measure.map assoc₃ (Measure.map swap₂ (Measure.map assoc₁
        (((gaussianReal 0 1).prod gaussianZigZagHazardMeasure).prod
          zigZagVelocityProbability))) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop),
          Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
    _ = Measure.map assoc₃ (Measure.map swap₂
        ((gaussianReal 0 1).prod
          (gaussianZigZagHazardMeasure.prod zigZagVelocityProbability))) := by
      rw [hassoc₁]
    _ = Measure.map assoc₃ ((gaussianReal 0 1).prod
        (zigZagVelocityProbability.prod gaussianZigZagHazardMeasure)) := by
      rw [hswap₂]
    _ = ((gaussianReal 0 1).prod zigZagVelocityProbability).prod
        gaussianZigZagHazardMeasure := hassoc₃
    _ = gaussianZigZagTarget.prod gaussianZigZagHazardMeasure := rfl

/-- Read an exact signed initial state and its residual first-event hazard
directly from a length-biased stationary cycle and an independent velocity
label. -/
noncomputable def gaussianZigZagStationaryCycleClockMap
    (input : ((ℝ × ℝ) × ℝ) × Bool) : ZigZagState × NNReal :=
  ((input.1.2, input.2),
    gaussianZigZagCycleResidualHazard input.1.2 input.1.1.2)

theorem measurable_gaussianZigZagStationaryCycleClockMap :
    Measurable gaussianZigZagStationaryCycleClockMap := by
  have hresidual : Measurable (fun input : ((ℝ × ℝ) × ℝ) × Bool =>
      gaussianZigZagStationaryCycleResidualMap input.1) :=
    measurable_gaussianZigZagStationaryCycleResidualMap.comp
      (measurable_fst : Measurable
        (Prod.fst : (((ℝ × ℝ) × ℝ) × Bool) → ((ℝ × ℝ) × ℝ)))
  unfold gaussianZigZagStationaryCycleClockMap
  exact (hresidual.fst.prodMk measurable_snd).prodMk hresidual.snd

/-- The clocked initial state extracted from stationary cycle occupation has
exactly the Gaussian phase target and an independent fresh exponential clock. -/
theorem gaussianZigZagStationaryCycleClockMap_map :
    Measure.map gaussianZigZagStationaryCycleClockMap
        (gaussianZigZagStationaryCycleMeasure.prod
          zigZagVelocityProbability) =
      gaussianZigZagTarget.prod gaussianZigZagHazardMeasure := by
  let residualVelocityMap : ((ℝ × ℝ) × ℝ) × Bool →
      (ℝ × NNReal) × Bool :=
    Prod.map gaussianZigZagStationaryCycleResidualMap id
  let reorder : (ℝ × NNReal) × Bool → ZigZagState × NNReal :=
    fun input => ((input.1.1, input.2), input.1.2)
  have hresidualVelocityMap : Measurable residualVelocityMap :=
    measurable_gaussianZigZagStationaryCycleResidualMap.prodMap measurable_id
  have hreorder : Measurable reorder := by
    unfold reorder
    fun_prop
  have hfactor : gaussianZigZagStationaryCycleClockMap =
      reorder ∘ residualVelocityMap := rfl
  rw [hfactor]
  calc
    Measure.map (reorder ∘ residualVelocityMap)
        (gaussianZigZagStationaryCycleMeasure.prod
          zigZagVelocityProbability) =
      Measure.map reorder (Measure.map residualVelocityMap
        (gaussianZigZagStationaryCycleMeasure.prod
          zigZagVelocityProbability)) := by
        rw [Measure.map_map hreorder hresidualVelocityMap]
    _ = Measure.map reorder
        (gaussianZigZagStationaryPositionResidualMeasure.prod
          zigZagVelocityProbability) := by
      congr 1
      unfold residualVelocityMap
      rw [← Measure.map_prod_map gaussianZigZagStationaryCycleMeasure
        zigZagVelocityProbability
        measurable_gaussianZigZagStationaryCycleResidualMap measurable_id,
        Measure.map_id]
      rfl
    _ = _ := gaussianZigZagStationaryPositionResidualVelocity_reorder

/-- Add an independent future hazard tail to the stationary cycle clock and
reassociate it into the exact first-event input shape. -/
noncomputable def gaussianZigZagStationaryCycleHeadTailMap
    (input : (((ℝ × ℝ) × ℝ) × Bool) × (ℕ → NNReal)) :
    ZigZagState × (NNReal × (ℕ → NNReal)) :=
  (gaussianZigZagStationaryCycleClockMap input.1 |>.1,
    (gaussianZigZagStationaryCycleClockMap input.1 |>.2, input.2))

theorem measurable_gaussianZigZagStationaryCycleHeadTailMap :
    Measurable gaussianZigZagStationaryCycleHeadTailMap := by
  unfold gaussianZigZagStationaryCycleHeadTailMap
  have hclock := measurable_gaussianZigZagStationaryCycleClockMap.comp
    (measurable_fst : Measurable
      (Prod.fst : ((((ℝ × ℝ) × ℝ) × Bool) × (ℕ → NNReal)) →
        (((ℝ × ℝ) × ℝ) × Bool)))
  exact hclock.fst.prodMk (hclock.snd.prodMk measurable_snd)

theorem gaussianZigZagStationaryCycleHeadTailMap_map :
    Measure.map gaussianZigZagStationaryCycleHeadTailMap
        ((gaussianZigZagStationaryCycleMeasure.prod
          zigZagVelocityProbability).prod
            gaussianZigZagHazardSequenceMeasure) =
      gaussianZigZagTarget.prod
        (gaussianZigZagHazardMeasure.prod
          gaussianZigZagHazardSequenceMeasure) := by
  let clockTailMap : ((((ℝ × ℝ) × ℝ) × Bool) × (ℕ → NNReal)) →
      ((ZigZagState × NNReal) × (ℕ → NNReal)) :=
    Prod.map gaussianZigZagStationaryCycleClockMap id
  have hclockTailMap : Measurable clockTailMap :=
    measurable_gaussianZigZagStationaryCycleClockMap.prodMap measurable_id
  have hfactor : gaussianZigZagStationaryCycleHeadTailMap =
      MeasurableEquiv.prodAssoc ∘ clockTailMap := rfl
  rw [hfactor]
  calc
    Measure.map (MeasurableEquiv.prodAssoc ∘ clockTailMap)
        ((gaussianZigZagStationaryCycleMeasure.prod
          zigZagVelocityProbability).prod
            gaussianZigZagHazardSequenceMeasure) =
      Measure.map MeasurableEquiv.prodAssoc
        (Measure.map clockTailMap
          ((gaussianZigZagStationaryCycleMeasure.prod
            zigZagVelocityProbability).prod
              gaussianZigZagHazardSequenceMeasure)) := by
        rw [Measure.map_map MeasurableEquiv.prodAssoc.measurable hclockTailMap]
    _ = Measure.map MeasurableEquiv.prodAssoc
        ((gaussianZigZagTarget.prod gaussianZigZagHazardMeasure).prod
          gaussianZigZagHazardSequenceMeasure) := by
      congr 1
      unfold clockTailMap
      rw [← Measure.map_prod_map
        (gaussianZigZagStationaryCycleMeasure.prod
          zigZagVelocityProbability)
        gaussianZigZagHazardSequenceMeasure
        measurable_gaussianZigZagStationaryCycleClockMap measurable_id,
        Measure.map_id, gaussianZigZagStationaryCycleClockMap_map]
    _ = _ := (MeasureTheory.measurePreserving_prodAssoc
      gaussianZigZagTarget gaussianZigZagHazardMeasure
      gaussianZigZagHazardSequenceMeasure).map_eq

/-- Convert the stationary cycle's residual head and an independent future
tail into the exact infinite hazard stream consumed by the stopped executor. -/
noncomputable def gaussianZigZagStationaryCycleStreamMap
    (input : (((ℝ × ℝ) × ℝ) × Bool) × (ℕ → NNReal)) :
    ZigZagState × (ℕ → NNReal) :=
  let clocked := gaussianZigZagStationaryCycleHeadTailMap input
  (clocked.1, gaussianZigZagHazardCons clocked.2)

theorem measurable_gaussianZigZagStationaryCycleStreamMap :
    Measurable gaussianZigZagStationaryCycleStreamMap := by
  unfold gaussianZigZagStationaryCycleStreamMap
  have hclocked := measurable_gaussianZigZagStationaryCycleHeadTailMap
  exact hclocked.fst.prodMk
    (measurable_gaussianZigZagHazardCons.comp hclocked.snd)

/-- Stationary cycle occupation, a velocity label, and a fresh future tail
produce exactly the target-started input law of the stopped signed executor. -/
theorem gaussianZigZagStationaryCycleStreamMap_map :
    Measure.map gaussianZigZagStationaryCycleStreamMap
        ((gaussianZigZagStationaryCycleMeasure.prod
          zigZagVelocityProbability).prod
            gaussianZigZagHazardSequenceMeasure) =
      gaussianZigZagTarget.prod gaussianZigZagHazardSequenceMeasure := by
  let consMap : ZigZagState × (NNReal × (ℕ → NNReal)) →
      ZigZagState × (ℕ → NNReal) :=
    Prod.map id gaussianZigZagHazardCons
  have hconsMap : Measurable consMap :=
    measurable_id.prodMap measurable_gaussianZigZagHazardCons
  have hfactor : gaussianZigZagStationaryCycleStreamMap =
      consMap ∘ gaussianZigZagStationaryCycleHeadTailMap := rfl
  rw [hfactor]
  calc
    Measure.map (consMap ∘ gaussianZigZagStationaryCycleHeadTailMap)
        ((gaussianZigZagStationaryCycleMeasure.prod
          zigZagVelocityProbability).prod
            gaussianZigZagHazardSequenceMeasure) =
      Measure.map consMap (Measure.map
        gaussianZigZagStationaryCycleHeadTailMap
        ((gaussianZigZagStationaryCycleMeasure.prod
          zigZagVelocityProbability).prod
            gaussianZigZagHazardSequenceMeasure)) := by
        rw [Measure.map_map hconsMap
          measurable_gaussianZigZagStationaryCycleHeadTailMap]
    _ = Measure.map consMap (gaussianZigZagTarget.prod
        (gaussianZigZagHazardMeasure.prod
          gaussianZigZagHazardSequenceMeasure)) := by
      rw [gaussianZigZagStationaryCycleHeadTailMap_map]
    _ = (Measure.map id gaussianZigZagTarget).prod
        (Measure.map gaussianZigZagHazardCons
          (gaussianZigZagHazardMeasure.prod
            gaussianZigZagHazardSequenceMeasure)) := by
      symm
      exact Measure.map_prod_map gaussianZigZagTarget
        (gaussianZigZagHazardMeasure.prod
          gaussianZigZagHazardSequenceMeasure)
        measurable_id measurable_gaussianZigZagHazardCons
    _ = _ := by
      rw [Measure.map_id,
        gaussianZigZagHazardMeasure_prod_sequence_map_cons]

/-- Base environment for the regenerative suspension: two consecutive reset
positions and the iid hazard tail generating all later resets. -/
noncomputable def gaussianZigZagCycleEnvironmentMeasure :
    Measure ((ℝ × ℝ) × (ℕ → NNReal)) :=
  (gaussianZigZagNegativeRayleighMeasure.prod
    gaussianZigZagNegativeRayleighMeasure).prod
      gaussianZigZagHazardSequenceMeasure

instance gaussianZigZagCycleEnvironmentMeasure.instIsProbabilityMeasure :
    IsProbabilityMeasure gaussianZigZagCycleEnvironmentMeasure := by
  unfold gaussianZigZagCycleEnvironmentMeasure
  infer_instance

/-- Event shift of the regenerative environment. The consumed left reset is
dropped, the old right reset becomes the new left reset, and the tail head
generates the new right reset. -/
noncomputable def gaussianZigZagCycleEnvironmentShift
    (environment : (ℝ × ℝ) × (ℕ → NNReal)) :
    (ℝ × ℝ) × (ℕ → NNReal) :=
  ((environment.1.2,
      gaussianZigZagNegativeRayleighReset (environment.2 0)),
    fun index => environment.2 (index + 1))

theorem measurable_gaussianZigZagCycleEnvironmentShift :
    Measurable gaussianZigZagCycleEnvironmentShift := by
  unfold gaussianZigZagCycleEnvironmentShift
  exact (measurable_fst.snd.prodMk
    (measurable_gaussianZigZagNegativeRayleighReset.comp
      ((measurable_pi_apply 0).comp measurable_snd))).prodMk
        (by fun_prop)

/-- The iid reset/hazard base law is invariant under one regenerative event
shift. This is the base-map invariance required by the stationary suspension. -/
theorem gaussianZigZagCycleEnvironmentShift_map :
    Measure.map gaussianZigZagCycleEnvironmentShift
        gaussianZigZagCycleEnvironmentMeasure =
      gaussianZigZagCycleEnvironmentMeasure := by
  let resetLaw := gaussianZigZagNegativeRayleighMeasure
  let tailLaw := gaussianZigZagHazardSequenceMeasure
  let dropLeft : ((ℝ × ℝ) × (ℕ → NNReal)) →
      (ℝ × (ℕ → NNReal)) := fun input => (input.1.2, input.2)
  let splitTail : (ℝ × (ℕ → NNReal)) →
      (ℝ × (NNReal × (ℕ → NNReal))) :=
    Prod.map id gaussianZigZagHazardHeadTail
  let reassoc : (ℝ × (NNReal × (ℕ → NNReal))) →
      ((ℝ × NNReal) × (ℕ → NNReal)) := MeasurableEquiv.prodAssoc.symm
  let resetHead : ((ℝ × NNReal) × (ℕ → NNReal)) →
      ((ℝ × ℝ) × (ℕ → NNReal)) :=
    Prod.map (Prod.map id gaussianZigZagNegativeRayleighReset) id
  have hdropLeft : Measurable dropLeft := by
    unfold dropLeft
    fun_prop
  have hsplitTail : Measurable splitTail :=
    measurable_id.prodMap measurable_gaussianZigZagHazardHeadTail
  have hreassoc : Measurable reassoc :=
    MeasurableEquiv.prodAssoc.symm.measurable
  have hresetHead : Measurable resetHead :=
    (measurable_id.prodMap
      measurable_gaussianZigZagNegativeRayleighReset).prodMap measurable_id
  have hdropLaw : Measure.map dropLeft
      ((resetLaw.prod resetLaw).prod tailLaw) = resetLaw.prod tailLaw := by
    let assoc : ((ℝ × ℝ) × (ℕ → NNReal)) ≃ᵐ
        (ℝ × (ℝ × (ℕ → NNReal))) := MeasurableEquiv.prodAssoc
    have hfactor : dropLeft = Prod.snd ∘ assoc := rfl
    rw [hfactor]
    calc
      Measure.map (Prod.snd ∘ assoc)
          ((resetLaw.prod resetLaw).prod tailLaw) =
        Measure.map Prod.snd (Measure.map assoc
          ((resetLaw.prod resetLaw).prod tailLaw)) := by
          rw [Measure.map_map measurable_snd assoc.measurable]
      _ = Measure.map Prod.snd
          (resetLaw.prod (resetLaw.prod tailLaw)) := by
        rw [(MeasureTheory.measurePreserving_prodAssoc
          resetLaw resetLaw tailLaw).map_eq]
      _ = resetLaw.prod tailLaw := by
        rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hsplitLaw : Measure.map splitTail (resetLaw.prod tailLaw) =
      resetLaw.prod
        (gaussianZigZagHazardMeasure.prod tailLaw) := by
    unfold splitTail
    rw [← Measure.map_prod_map resetLaw tailLaw measurable_id
      measurable_gaussianZigZagHazardHeadTail,
      Measure.map_id,
      gaussianZigZagHazardSequenceMeasure_map_headTail]
  have hreassocLaw : Measure.map reassoc
      (resetLaw.prod (gaussianZigZagHazardMeasure.prod tailLaw)) =
      (resetLaw.prod gaussianZigZagHazardMeasure).prod tailLaw :=
    (MeasureTheory.measurePreserving_prodAssoc resetLaw
      gaussianZigZagHazardMeasure tailLaw).symm.map_eq
  have hresetLaw : Measure.map resetHead
      ((resetLaw.prod gaussianZigZagHazardMeasure).prod tailLaw) =
      (resetLaw.prod resetLaw).prod tailLaw := by
    unfold resetHead
    rw [← Measure.map_prod_map
      (resetLaw.prod gaussianZigZagHazardMeasure) tailLaw
      (measurable_id.prodMap
        measurable_gaussianZigZagNegativeRayleighReset) measurable_id,
      ← Measure.map_prod_map resetLaw gaussianZigZagHazardMeasure
        measurable_id measurable_gaussianZigZagNegativeRayleighReset,
      Measure.map_id, Measure.map_id]
    rfl
  have hfactor : gaussianZigZagCycleEnvironmentShift =
      resetHead ∘ reassoc ∘ splitTail ∘ dropLeft := rfl
  unfold gaussianZigZagCycleEnvironmentMeasure
  change Measure.map gaussianZigZagCycleEnvironmentShift
      ((resetLaw.prod resetLaw).prod tailLaw) = _
  rw [hfactor]
  calc
    Measure.map (resetHead ∘ reassoc ∘ splitTail ∘ dropLeft)
        ((resetLaw.prod resetLaw).prod tailLaw) =
      Measure.map resetHead (Measure.map reassoc
        (Measure.map splitTail (Measure.map dropLeft
          ((resetLaw.prod resetLaw).prod tailLaw)))) := by
        rw [Measure.map_map hresetHead hreassoc,
          Measure.map_map (hresetHead.comp hreassoc) hsplitTail,
          Measure.map_map ((hresetHead.comp hreassoc).comp hsplitTail)
            hdropLeft]
        rfl
    _ = Measure.map resetHead (Measure.map reassoc
        (Measure.map splitTail (resetLaw.prod tailLaw))) := by rw [hdropLaw]
    _ = Measure.map resetHead (Measure.map reassoc
        (resetLaw.prod
          (gaussianZigZagHazardMeasure.prod tailLaw))) := by rw [hsplitLaw]
    _ = Measure.map resetHead
        ((resetLaw.prod gaussianZigZagHazardMeasure).prod tailLaw) := by
      rw [hreassocLaw]
    _ = (resetLaw.prod resetLaw).prod tailLaw := hresetLaw

/-- Duration of the current regenerative signed interval. -/
noncomputable def gaussianZigZagCycleEnvironmentRoof
    (environment : (ℝ × ℝ) × (ℕ → NNReal)) : NNReal :=
  Real.toNNReal (-environment.1.2 - environment.1.1)

theorem measurable_gaussianZigZagCycleEnvironmentRoof :
    Measurable gaussianZigZagCycleEnvironmentRoof := by
  unfold gaussianZigZagCycleEnvironmentRoof
  fun_prop

theorem gaussianZigZagCycleEnvironment_resets_negative_ae :
    ∀ᵐ environment ∂gaussianZigZagCycleEnvironmentMeasure,
      environment.1.1 < 0 ∧ environment.1.2 < 0 := by
  have hpairFst := (Measure.quasiMeasurePreserving_fst
    (μ := gaussianZigZagNegativeRayleighMeasure)
    (ν := gaussianZigZagNegativeRayleighMeasure)).ae
      gaussianZigZagNegativeRayleighMeasure_negative_ae
  have hpairSnd := (Measure.quasiMeasurePreserving_snd
    (μ := gaussianZigZagNegativeRayleighMeasure)
    (ν := gaussianZigZagNegativeRayleighMeasure)).ae
      gaussianZigZagNegativeRayleighMeasure_negative_ae
  have hpair : ∀ᵐ resets ∂
      gaussianZigZagNegativeRayleighMeasure.prod
        gaussianZigZagNegativeRayleighMeasure,
      resets.1 < 0 ∧ resets.2 < 0 := by
    filter_upwards [hpairFst, hpairSnd] with resets hleft hright
    exact ⟨hleft, hright⟩
  unfold gaussianZigZagCycleEnvironmentMeasure
  exact (Measure.quasiMeasurePreserving_fst
    (μ := gaussianZigZagNegativeRayleighMeasure.prod
      gaussianZigZagNegativeRayleighMeasure)
    (ν := gaussianZigZagHazardSequenceMeasure)).ae hpair

theorem gaussianZigZagCycleEnvironmentRoof_pos_ae :
    ∀ᵐ environment ∂gaussianZigZagCycleEnvironmentMeasure,
      0 < gaussianZigZagCycleEnvironmentRoof environment := by
  filter_upwards [gaussianZigZagCycleEnvironment_resets_negative_ae]
    with environment hnegative
  rw [← NNReal.coe_pos]
  unfold gaussianZigZagCycleEnvironmentRoof
  rw [Real.coe_toNNReal]
  · linarith
  · linarith

/-- Add the alternating velocity label to the regenerative base shift. -/
noncomputable def gaussianZigZagCyclePhaseEnvironmentShift
    (input : ((ℝ × ℝ) × (ℕ → NNReal)) × Bool) :
    ((ℝ × ℝ) × (ℕ → NNReal)) × Bool :=
  (gaussianZigZagCycleEnvironmentShift input.1, !input.2)

theorem measurable_gaussianZigZagCyclePhaseEnvironmentShift :
    Measurable gaussianZigZagCyclePhaseEnvironmentShift :=
  measurable_gaussianZigZagCycleEnvironmentShift.prodMap (by fun_prop)

theorem gaussianZigZagCyclePhaseEnvironmentShift_map :
    Measure.map gaussianZigZagCyclePhaseEnvironmentShift
        (gaussianZigZagCycleEnvironmentMeasure.prod
          zigZagVelocityProbability) =
      gaussianZigZagCycleEnvironmentMeasure.prod
        zigZagVelocityProbability := by
  unfold gaussianZigZagCyclePhaseEnvironmentShift
  change Measure.map
      (Prod.map gaussianZigZagCycleEnvironmentShift Bool.not)
      (gaussianZigZagCycleEnvironmentMeasure.prod
        zigZagVelocityProbability) = _
  rw [← Measure.map_prod_map gaussianZigZagCycleEnvironmentMeasure
    zigZagVelocityProbability
    measurable_gaussianZigZagCycleEnvironmentShift (by fun_prop),
    gaussianZigZagCycleEnvironmentShift_map,
    zigZagVelocityProbability_map_not]

/-- Invariant event-epoch base law including the alternating velocity label. -/
noncomputable def gaussianZigZagCyclePhaseEnvironmentMeasure :
    Measure (((ℝ × ℝ) × (ℕ → NNReal)) × Bool) :=
  gaussianZigZagCycleEnvironmentMeasure.prod zigZagVelocityProbability

instance gaussianZigZagCyclePhaseEnvironmentMeasure.instIsProbabilityMeasure :
    IsProbabilityMeasure gaussianZigZagCyclePhaseEnvironmentMeasure := by
  unfold gaussianZigZagCyclePhaseEnvironmentMeasure
  infer_instance

/-- Roof function on the phase-environment base. -/
noncomputable def gaussianZigZagCyclePhaseEnvironmentRoof
    (input : ((ℝ × ℝ) × (ℕ → NNReal)) × Bool) : ℝ :=
  gaussianZigZagCycleEnvironmentRoof input.1

theorem measurable_gaussianZigZagCyclePhaseEnvironmentRoof :
    Measurable gaussianZigZagCyclePhaseEnvironmentRoof :=
  (measurable_gaussianZigZagCycleEnvironmentRoof.comp
    measurable_fst).coe_nnreal_real

theorem gaussianZigZagCyclePhaseEnvironmentRoof_pos_ae :
    ∀ᵐ input ∂gaussianZigZagCyclePhaseEnvironmentMeasure,
      0 < gaussianZigZagCyclePhaseEnvironmentRoof input := by
  unfold gaussianZigZagCyclePhaseEnvironmentMeasure
  exact (Measure.quasiMeasurePreserving_fst
    (μ := gaussianZigZagCycleEnvironmentMeasure)
    (ν := zigZagVelocityProbability)).ae
      gaussianZigZagCycleEnvironmentRoof_pos_ae

omit [MeasurableSpace ZigZagState] in
/-- After `eventCount` regenerative shifts, the remaining hazard stream is
the corresponding tail of the original stream. -/
theorem gaussianZigZagCyclePhaseEnvironmentShift_iterate_tail
    (input : ((ℝ × ℝ) × (ℕ → NNReal)) × Bool)
    (eventCount index : ℕ) :
    ((gaussianZigZagCyclePhaseEnvironmentShift^[eventCount]) input).1.2 index =
      input.1.2 (index + eventCount) := by
  induction eventCount with
  | zero => simp
  | succ eventCount ih =>
      rw [Function.iterate_succ_apply']
      simp only [gaussianZigZagCyclePhaseEnvironmentShift,
        gaussianZigZagCycleEnvironmentShift]
      rw [ih]
      congr 1
      omega

omit [MeasurableSpace ZigZagState] in
/-- The right reset after the next regenerative shift is generated by the
hazard currently at the head of the advanced stream. -/
theorem gaussianZigZagCyclePhaseEnvironmentShift_iterate_succ_right
    (input : (((ℝ × ℝ) × (ℕ → NNReal)) × Bool))
    (eventCount : ℕ) :
    ((gaussianZigZagCyclePhaseEnvironmentShift^[eventCount + 1]) input).1.1.2 =
      gaussianZigZagNegativeRayleighReset (input.1.2 eventCount) := by
  rw [show eventCount + 1 = eventCount.succ by omega,
    Function.iterate_succ_apply']
  simp only [gaussianZigZagCyclePhaseEnvironmentShift,
    gaussianZigZagCycleEnvironmentShift]
  rw [gaussianZigZagCyclePhaseEnvironmentShift_iterate_tail]
  simp

omit [MeasurableSpace ZigZagState] in
/-- Every future regenerative roof dominates the square-root term generated
by the hazard which created its right reset. -/
theorem gaussianZigZagSqrtHazard_le_phaseRoof_iterate_succ
    (input : (((ℝ × ℝ) × (ℕ → NNReal)) × Bool))
    (hright : input.1.1.2 < 0) (eventCount : ℕ) :
    Real.sqrt (2 * (input.1.2 eventCount : ℝ)) ≤
      gaussianZigZagCyclePhaseEnvironmentRoof
        ((gaussianZigZagCyclePhaseEnvironmentShift^[eventCount + 1]) input) := by
  let advanced :=
    (gaussianZigZagCyclePhaseEnvironmentShift^[eventCount + 1]) input
  have hadvancedRight : advanced.1.1.2 =
      gaussianZigZagNegativeRayleighReset (input.1.2 eventCount) := by
    exact gaussianZigZagCyclePhaseEnvironmentShift_iterate_succ_right
      input eventCount
  have hadvancedLeft : advanced.1.1.1 ≤ 0 := by
    rw [show eventCount + 1 = eventCount.succ by omega,
      Function.iterate_succ_apply']
    simp only [gaussianZigZagCyclePhaseEnvironmentShift,
      gaussianZigZagCycleEnvironmentShift]
    cases eventCount with
    | zero => simpa using hright.le
    | succ eventCount =>
        rw [gaussianZigZagCyclePhaseEnvironmentShift_iterate_succ_right]
        unfold gaussianZigZagNegativeRayleighReset
        exact neg_nonpos.mpr (Real.sqrt_nonneg _)
  have hroofNonneg : 0 ≤ -advanced.1.1.2 - advanced.1.1.1 := by
    rw [hadvancedRight]
    unfold gaussianZigZagNegativeRayleighReset
    linarith [Real.sqrt_nonneg (2 * (input.1.2 eventCount : ℝ))]
  unfold gaussianZigZagCyclePhaseEnvironmentRoof
    gaussianZigZagCycleEnvironmentRoof
  rw [NNReal.coe_toNNReal _ hroofNonneg, hadvancedRight]
  unfold gaussianZigZagNegativeRayleighReset
  linarith

/-- The concrete regenerative suspension is nonexplosive almost surely: the
iid square-root hazard lower-bound series forces cumulative roofs to exceed
every finite horizon. -/
theorem gaussianZigZagCyclePhaseEnvironment_nonexplosive_ae :
    ∀ᵐ input ∂gaussianZigZagCyclePhaseEnvironmentMeasure,
      ∀ shift, 0 ≤ shift → ∃ eventCount,
        suspensionCrossed gaussianZigZagCyclePhaseEnvironmentShift
          gaussianZigZagCyclePhaseEnvironmentRoof input 0 shift eventCount := by
  unfold gaussianZigZagCyclePhaseEnvironmentMeasure
  have hdiverges := (Measure.quasiMeasurePreserving_fst
    (μ := gaussianZigZagCycleEnvironmentMeasure)
    (ν := zigZagVelocityProbability)).ae
      ((Measure.quasiMeasurePreserving_snd
        (μ := gaussianZigZagNegativeRayleighMeasure.prod
          gaussianZigZagNegativeRayleighMeasure)
        (ν := gaussianZigZagHazardSequenceMeasure)).ae
          gaussianZigZagSqrtHazard_tsum_eq_top_ae)
  have hnegative := (Measure.quasiMeasurePreserving_fst
    (μ := gaussianZigZagCycleEnvironmentMeasure)
    (ν := zigZagVelocityProbability)).ae
      gaussianZigZagCycleEnvironment_resets_negative_ae
  filter_upwards [hdiverges, hnegative] with input hsum hnegativeInput
  intro shift hshift
  have htendsto := ENNReal.tendsto_nat_tsum
    (gaussianZigZagSqrtHazardTerm input.1.2)
  rw [hsum] at htendsto
  have heventually : ∀ᵐ eventCount in Filter.atTop,
      ENNReal.ofReal shift < ∑ index ∈ Finset.range eventCount,
        gaussianZigZagSqrtHazardTerm input.1.2 index :=
    (tendsto_order.1 htendsto).1 _ ENNReal.ofReal_lt_top
  obtain ⟨eventCount, hpartial⟩ := heventually.exists
  refine ⟨eventCount, ?_⟩
  unfold suspensionCrossed
  simp only [zero_add]
  have hsqrtSum : shift < ∑ index ∈ Finset.range eventCount,
      Real.sqrt (2 * (input.1.2 index : ℝ)) := by
    rw [gaussianZigZagSqrtHazardTerm,
      ← ENNReal.ofReal_sum_of_nonneg (fun index _ => Real.sqrt_nonneg _)] at hpartial
    exact (ENNReal.ofReal_lt_ofReal_iff (by
      by_contra hnonpos
      have : ∑ index ∈ Finset.range eventCount,
          Real.sqrt (2 * (input.1.2 index : ℝ)) = 0 := by
        have hle : ∑ index ∈ Finset.range eventCount,
            Real.sqrt (2 * (input.1.2 index : ℝ)) ≤ 0 := le_of_not_gt hnonpos
        exact le_antisymm hle (Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _)
      simp [this] at hpartial)).mp hpartial
  have hlower : (∑ index ∈ Finset.range eventCount,
      Real.sqrt (2 * (input.1.2 index : ℝ))) ≤
      suspensionRoofElapsed gaussianZigZagCyclePhaseEnvironmentShift
        gaussianZigZagCyclePhaseEnvironmentRoof input (eventCount + 1) := by
    unfold suspensionRoofElapsed
    rw [Finset.sum_range_succ']
    apply le_add_of_nonneg_right
    · exact Finset.sum_le_sum fun index _ =>
        gaussianZigZagSqrtHazard_le_phaseRoof_iterate_succ
          input hnegativeInput.2 index
    · unfold gaussianZigZagCyclePhaseEnvironmentRoof
        gaussianZigZagCycleEnvironmentRoof
      positivity
  exact hsqrtSum.trans_le hlower

/-- The concrete unnormalized stationary suspension occupation law for the
Gaussian Zig-Zag regenerative environment. -/
noncomputable def gaussianZigZagSuspensionOccupationMeasure :
    Measure ((((ℝ × ℝ) × (ℕ → NNReal)) × Bool) × ℝ) :=
  suspensionOccupationMeasure gaussianZigZagCyclePhaseEnvironmentMeasure
    gaussianZigZagCyclePhaseEnvironmentRoof

/-- Every nonnegative-time endpoint of the concrete Gaussian regenerative
suspension preserves its roof-occupation law. -/
theorem gaussianZigZagSuspensionEndpoint_map_occupation
    (horizon : NNReal) :
    Measure.map
        (suspensionEndpoint gaussianZigZagCyclePhaseEnvironmentShift
          gaussianZigZagCyclePhaseEnvironmentRoof (horizon : ℝ))
        gaussianZigZagSuspensionOccupationMeasure =
      gaussianZigZagSuspensionOccupationMeasure := by
  apply suspensionEndpoint_map_occupation
    gaussianZigZagCyclePhaseEnvironmentMeasure
    measurable_gaussianZigZagCyclePhaseEnvironmentShift
    gaussianZigZagCyclePhaseEnvironmentShift_map
    measurable_gaussianZigZagCyclePhaseEnvironmentRoof
  · filter_upwards [gaussianZigZagCyclePhaseEnvironmentRoof_pos_ae]
      with input hroof
    exact hroof.le
  · exact gaussianZigZagCyclePhaseEnvironment_nonexplosive_ae
  · exact_mod_cast horizon.2

/-- Translate suspension age into the signed position of the current literal
cycle while retaining velocity and the future hazard tail. -/
noncomputable def gaussianZigZagSuspensionDecode
    (input : ((((ℝ × ℝ) × (ℕ → NNReal)) × Bool) × ℝ)) :
    ((((ℝ × ℝ) × ℝ) × Bool) × (ℕ → NNReal)) :=
  (((input.1.1.1, input.1.1.1.1 + input.2), input.1.2), input.1.1.2)

/-- Signed phase state represented by a regenerative suspension point. -/
noncomputable def gaussianZigZagSuspensionState
    (input : ((((ℝ × ℝ) × (ℕ → NNReal)) × Bool) × ℝ)) :
    ZigZagState :=
  (input.1.1.1.1 + input.2, input.1.2)

/-- Exact residual-head/future-tail stream represented by a regenerative
suspension point. -/
noncomputable def gaussianZigZagSuspensionHazardStream
    (input : ((((ℝ × ℝ) × (ℕ → NNReal)) × Bool) × ℝ)) :
    ℕ → NNReal :=
  gaussianZigZagHazardCons
    (gaussianZigZagCycleResidualHazard
      (gaussianZigZagSuspensionState input).1 input.1.1.1.2,
      input.1.1.2)

theorem gaussianZigZagStationaryCycleStreamMap_decode
    (input : ((((ℝ × ℝ) × (ℕ → NNReal)) × Bool) × ℝ)) :
    gaussianZigZagStationaryCycleStreamMap
        (gaussianZigZagSuspensionDecode input) =
      (gaussianZigZagSuspensionState input,
        gaussianZigZagSuspensionHazardStream input) := by
  rfl

theorem measurable_gaussianZigZagSuspensionDecode :
    Measurable gaussianZigZagSuspensionDecode := by
  unfold gaussianZigZagSuspensionDecode
  fun_prop

/-- For a genuine reset environment, translating Lebesgue age by the left
reset gives exactly the literal signed cycle-interval kernel. -/
theorem gaussianZigZagSuspension_ageFiber_map
    (environment : (ℝ × ℝ) × (ℕ → NNReal))
    (hleft : environment.1.1 < 0) (hright : environment.1.2 < 0) :
    Measure.map (fun age : ℝ => environment.1.1 + age)
        (volume.restrict (Set.Ico 0
          (gaussianZigZagCycleEnvironmentRoof environment : ℝ))) =
      gaussianZigZagCycleIntervalKernel environment.1 := by
  have hroof : (gaussianZigZagCycleEnvironmentRoof environment : ℝ) =
      -environment.1.2 - environment.1.1 := by
    unfold gaussianZigZagCycleEnvironmentRoof
    rw [Real.coe_toNNReal]
    linarith
  rw [hroof, show -environment.1.2 - environment.1.1 =
      (-environment.1.2) - environment.1.1 by ring]
  rw [map_add_restrict_Ico environment.1.1 (-environment.1.2)]
  rw [gaussianZigZagCycleIntervalKernel_apply]
  exact Measure.restrict_congr_set Ioo_ae_eq_Ico.symm

/-- Integrating the age-fiber translation over two independent event resets
gives exactly the literal regenerative-cycle composition product. -/
theorem gaussianZigZagCycleAgeOccupation_map :
    Measure.map
        (fun input : (ℝ × ℝ) × ℝ =>
          (input.1, input.1.1 + input.2))
        (((gaussianZigZagNegativeRayleighMeasure.prod
            gaussianZigZagNegativeRayleighMeasure).prod volume).restrict
          {input | input.2 ∈ Set.Ico 0
            (gaussianZigZagCycleEnvironmentRoof (input.1, fun _ => 0) : ℝ)}) =
      (gaussianZigZagNegativeRayleighMeasure.prod
        gaussianZigZagNegativeRayleighMeasure) ⊗ₘ
          gaussianZigZagCycleIntervalKernel := by
  let resetMeasure := gaussianZigZagNegativeRayleighMeasure.prod
    gaussianZigZagNegativeRayleighMeasure
  have hmap : Measurable (fun input : (ℝ × ℝ) × ℝ =>
      (input.1, input.1.1 + input.2)) := by fun_prop
  have hdomain : MeasurableSet
      {input : (ℝ × ℝ) × ℝ | input.2 ∈ Set.Ico 0
        (gaussianZigZagCycleEnvironmentRoof (input.1, fun _ => 0) : ℝ)} := by
    exact (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd
        (measurable_gaussianZigZagCycleEnvironmentRoof.coe_nnreal_real.comp
          (measurable_fst.prodMk measurable_const)))
  ext event hevent
  rw [Measure.map_apply hmap hevent,
    Measure.restrict_apply (hmap hevent),
    Measure.prod_apply ((hmap hevent).inter hdomain),
    Measure.compProd_apply hevent]
  apply lintegral_congr_ae
  filter_upwards [gaussianZigZagCycleEnvironment_resets_negative_ae]
      with resets hnegative
  have hfiber := congrArg (fun measure : Measure ℝ =>
      measure (Prod.mk resets ⁻¹' event))
    (gaussianZigZagSuspension_ageFiber_map
      (resets, fun _ => 0) hnegative.1 hnegative.2)
  rw [Measure.map_apply (by fun_prop) (hevent.preimage measurable_prodMk_left),
    Measure.restrict_apply ((hmap.comp measurable_prodMk_left) hevent)] at hfiber
  simpa [resetMeasure] using hfiber

/-- Decoding the full suspension occupation, including the independent phase
and future hazard tail, gives the unnormalized stationary-cycle source law. -/
theorem gaussianZigZagSuspensionDecode_map_occupation :
    Measure.map gaussianZigZagSuspensionDecode
        gaussianZigZagSuspensionOccupationMeasure =
      (((gaussianZigZagNegativeRayleighMeasure.prod
          gaussianZigZagNegativeRayleighMeasure) ⊗ₘ
            gaussianZigZagCycleIntervalKernel).prod
        zigZagVelocityProbability).prod
          gaussianZigZagHazardSequenceMeasure := by
  let resetMeasure := gaussianZigZagNegativeRayleighMeasure.prod
    gaussianZigZagNegativeRayleighMeasure
  let hazardMeasure := gaussianZigZagHazardSequenceMeasure
  let velocityMeasure := zigZagVelocityProbability
  let permute : (((ℝ × ℝ) × (ℕ → NNReal)) × Bool) × ℝ →
      ((((ℝ × ℝ) × ℝ) × Bool) × (ℕ → NNReal)) :=
    fun input => (((input.1.1.1, input.2), input.1.2), input.1.1.2)
  let translate : ((((ℝ × ℝ) × ℝ) × Bool) × (ℕ → NNReal)) →
      ((((ℝ × ℝ) × ℝ) × Bool) × (ℕ → NNReal)) :=
    fun input => (((input.1.1.1, input.1.1.1.1 + input.1.1.2),
      input.1.2), input.2)
  have hpermute : Measurable permute := by unfold permute; fun_prop
  have htranslate : Measurable translate := by unfold translate; fun_prop
  have hpermuteMeasure : Measure.map permute
      (((resetMeasure.prod hazardMeasure).prod velocityMeasure).prod volume) =
      (((resetMeasure.prod volume).prod velocityMeasure).prod hazardMeasure) := by
    let p₁ := (MeasurableEquiv.prodAssoc :
      (((ℝ × ℝ) × (ℕ → NNReal)) × Bool) × ℝ ≃ᵐ
        ((ℝ × ℝ) × (ℕ → NNReal)) × (Bool × ℝ))
    let p₂ := (MeasurableEquiv.prodAssoc :
      ((ℝ × ℝ) × (ℕ → NNReal)) × (Bool × ℝ) ≃ᵐ
        (ℝ × ℝ) × ((ℕ → NNReal) × (Bool × ℝ)))
    let p₃ : (ℝ × ℝ) × ((ℕ → NNReal) × (Bool × ℝ)) →
        (ℝ × ℝ) × ((Bool × ℝ) × (ℕ → NNReal)) :=
      Prod.map id Prod.swap
    let p₄ : (ℝ × ℝ) × ((Bool × ℝ) × (ℕ → NNReal)) →
        (ℝ × ℝ) × ((ℝ × Bool) × (ℕ → NNReal)) :=
      Prod.map id (Prod.map Prod.swap id)
    let p₅ := (MeasurableEquiv.prodAssoc.symm :
      (ℝ × ℝ) × ((ℝ × Bool) × (ℕ → NNReal)) ≃ᵐ
        ((ℝ × ℝ) × (ℝ × Bool)) × (ℕ → NNReal))
    let p₆ : ((ℝ × ℝ) × (ℝ × Bool)) × (ℕ → NNReal) →
        ((((ℝ × ℝ) × ℝ) × Bool) × (ℕ → NNReal)) :=
      Prod.map MeasurableEquiv.prodAssoc.symm id
    have hp₁ := measurePreserving_prodAssoc
      (resetMeasure.prod hazardMeasure) velocityMeasure (volume : Measure ℝ)
    have hp₂ := measurePreserving_prodAssoc
      resetMeasure hazardMeasure (velocityMeasure.prod (volume : Measure ℝ))
    have hp₃ := (MeasurePreserving.id resetMeasure).prod
      (Measure.measurePreserving_swap
        (μ := hazardMeasure) (ν := velocityMeasure.prod (volume : Measure ℝ)))
    have hp₄ := (MeasurePreserving.id resetMeasure).prod
      ((Measure.measurePreserving_swap
        (μ := velocityMeasure) (ν := (volume : Measure ℝ))).prod
          (MeasurePreserving.id hazardMeasure))
    have hp₅ := (measurePreserving_prodAssoc resetMeasure
      (volume.prod velocityMeasure) hazardMeasure).symm
        MeasurableEquiv.prodAssoc
    have hp₆ := ((measurePreserving_prodAssoc resetMeasure
      (volume : Measure ℝ) velocityMeasure).symm
        MeasurableEquiv.prodAssoc).prod (MeasurePreserving.id hazardMeasure)
    have hp := hp₆.comp (hp₅.comp (hp₄.comp
      (hp₃.comp (hp₂.comp hp₁))))
    have hfun : permute = p₆ ∘ p₅ ∘ p₄ ∘ p₃ ∘ p₂ ∘ p₁ := by
      funext input
      rfl
    rw [hfun]
    exact hp.map_eq
  have hdomain : MeasurableSet
      (suspensionFundamentalDomain gaussianZigZagCyclePhaseEnvironmentRoof) :=
    measurableSet_suspensionFundamentalDomain
      measurable_gaussianZigZagCyclePhaseEnvironmentRoof
  let ageDomain : Set ((ℝ × ℝ) × ℝ) :=
    {input | input.2 ∈ Set.Ico 0
      (gaussianZigZagCycleEnvironmentRoof (input.1, fun _ => 0) : ℝ)}
  have hageDomain : MeasurableSet ageDomain := by
    unfold ageDomain
    exact (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd
        (measurable_gaussianZigZagCycleEnvironmentRoof.coe_nnreal_real.comp
          (measurable_fst.prodMk measurable_const)))
  have hpre : permute ⁻¹'
      ((ageDomain ×ˢ Set.univ) ×ˢ Set.univ) =
      suspensionFundamentalDomain gaussianZigZagCyclePhaseEnvironmentRoof := by
    ext input
    simp [permute, ageDomain, suspensionFundamentalDomain,
      gaussianZigZagCyclePhaseEnvironmentRoof]
  have hpermutedOccupation : Measure.map permute
      gaussianZigZagSuspensionOccupationMeasure =
      ((((resetMeasure.prod volume).restrict ageDomain).prod velocityMeasure).prod
        hazardMeasure) := by
    unfold gaussianZigZagSuspensionOccupationMeasure
      suspensionOccupationMeasure
      gaussianZigZagCyclePhaseEnvironmentMeasure
      gaussianZigZagCycleEnvironmentMeasure
    change Measure.map permute
        ((((resetMeasure.prod hazardMeasure).prod velocityMeasure).prod volume).restrict
          (suspensionFundamentalDomain gaussianZigZagCyclePhaseEnvironmentRoof)) = _
    rw [← hpre, ← Measure.restrict_map hpermute
      ((hageDomain.prod MeasurableSet.univ).prod MeasurableSet.univ),
      hpermuteMeasure]
    rw [Measure.prod_restrict, Measure.prod_restrict]
    simp
  have hfactor : gaussianZigZagSuspensionDecode = translate ∘ permute := by
    funext input
    rfl
  rw [hfactor, Measure.map_map htranslate hpermute,
    hpermutedOccupation]
  have htranslateFactor : translate =
      Prod.map (Prod.map
        (fun input : (ℝ × ℝ) × ℝ =>
          (input.1, input.1.1 + input.2)) id) id := rfl
  rw [htranslateFactor, ← Measure.map_prod_map,
    ← Measure.map_prod_map, Measure.map_id, Measure.map_id,
    gaussianZigZagCycleAgeOccupation_map]
  rfl

/-- The preceding unnormalized decoder law is the mean cycle duration times
the normalized stationary-cycle source used by the stopped executor. -/
theorem gaussianZigZagSuspensionDecode_map_occupation_eq_smul :
    Measure.map gaussianZigZagSuspensionDecode
        gaussianZigZagSuspensionOccupationMeasure =
      gaussianZigZagCycleMeanDuration •
        ((gaussianZigZagStationaryCycleMeasure.prod
          zigZagVelocityProbability).prod
            gaussianZigZagHazardSequenceMeasure) := by
  rw [gaussianZigZagSuspensionDecode_map_occupation]
  unfold gaussianZigZagStationaryCycleMeasure
  rw [Measure.prod_smul_left, Measure.prod_smul_left, smul_smul]
  rw [ENNReal.mul_inv_cancel gaussianZigZagCycleMeanDuration_ne_zero
    gaussianZigZagCycleMeanDuration_ne_top, one_smul]

/-- Probability-normalized version of the concrete suspension occupation. -/
noncomputable def gaussianZigZagNormalizedSuspensionOccupationMeasure :
    Measure (((((ℝ × ℝ) × (ℕ → NNReal)) × Bool) × ℝ)) :=
  gaussianZigZagCycleMeanDuration⁻¹ •
    gaussianZigZagSuspensionOccupationMeasure

instance gaussianZigZagNormalizedSuspensionOccupationMeasure.instIsProbabilityMeasure :
    IsProbabilityMeasure gaussianZigZagNormalizedSuspensionOccupationMeasure := by
  constructor
  unfold gaussianZigZagNormalizedSuspensionOccupationMeasure
  rw [Measure.smul_apply, smul_eq_mul]
  have hmass := suspensionOccupationMeasure_apply_univ
    gaussianZigZagCyclePhaseEnvironmentMeasure
    measurable_gaussianZigZagCyclePhaseEnvironmentRoof
  rw [hmass]
  have hmean : suspensionMeanRoof
      gaussianZigZagCyclePhaseEnvironmentMeasure
      gaussianZigZagCyclePhaseEnvironmentRoof =
      gaussianZigZagCycleMeanDuration := by
    apply ENNReal.eq_of_inv_eq_inv
    have hdecoderMass := congrArg (fun measure : Measure
        ((((ℝ × ℝ) × ℝ) × Bool) × (ℕ → NNReal)) =>
          measure Set.univ)
      gaussianZigZagSuspensionDecode_map_occupation_eq_smul
    simpa [Measure.map_apply measurable_gaussianZigZagSuspensionDecode
      MeasurableSet.univ] using hdecoderMass
  rw [hmean]
  exact ENNReal.inv_mul_cancel gaussianZigZagCycleMeanDuration_ne_zero
    gaussianZigZagCycleMeanDuration_ne_top

theorem gaussianZigZagSuspensionDecode_map_normalized :
    Measure.map gaussianZigZagSuspensionDecode
        gaussianZigZagNormalizedSuspensionOccupationMeasure =
      (gaussianZigZagStationaryCycleMeasure.prod
        zigZagVelocityProbability).prod
          gaussianZigZagHazardSequenceMeasure := by
  unfold gaussianZigZagNormalizedSuspensionOccupationMeasure
  rw [Measure.map_smul,
    gaussianZigZagSuspensionDecode_map_occupation_eq_smul, smul_smul,
    ENNReal.inv_mul_cancel gaussianZigZagCycleMeanDuration_ne_zero
      gaussianZigZagCycleMeanDuration_ne_top,
    one_smul]

theorem gaussianZigZagSuspensionEndpoint_map_normalized
    (horizon : NNReal) :
    Measure.map
        (suspensionEndpoint gaussianZigZagCyclePhaseEnvironmentShift
          gaussianZigZagCyclePhaseEnvironmentRoof (horizon : ℝ))
        gaussianZigZagNormalizedSuspensionOccupationMeasure =
      gaussianZigZagNormalizedSuspensionOccupationMeasure := by
  unfold gaussianZigZagNormalizedSuspensionOccupationMeasure
  rw [Measure.map_smul,
    gaussianZigZagSuspensionEndpoint_map_occupation]

/-- Regenerative event-epoch law: negative-Rayleigh signed position and an
independent uniform velocity label. -/
noncomputable def gaussianZigZagSignedEventTarget : Measure ZigZagState :=
  gaussianZigZagNegativeRayleighMeasure.prod zigZagVelocityProbability

instance gaussianZigZagSignedEventTarget.instIsProbabilityMeasure :
    IsProbabilityMeasure gaussianZigZagSignedEventTarget := by
  unfold gaussianZigZagSignedEventTarget
  infer_instance

theorem gaussianZigZagSignedEventTarget_negative_ae :
    ∀ᵐ state ∂gaussianZigZagSignedEventTarget, state.1 < 0 := by
  unfold gaussianZigZagSignedEventTarget
  exact (Measure.quasiMeasurePreserving_fst
    (μ := gaussianZigZagNegativeRayleighMeasure)
    (ν := zigZagVelocityProbability)).ae
      gaussianZigZagNegativeRayleighMeasure_negative_ae

/-- Product-form event reset: independently redraw the negative-Rayleigh
position and deterministically flip the velocity label. -/
noncomputable def gaussianZigZagSignedResetKernel :
    Kernel ZigZagState ZigZagState :=
  (Kernel.const ℝ gaussianZigZagNegativeRayleighMeasure) ∥ₖ
    (Kernel.deterministic Bool.not (by fun_prop))

instance gaussianZigZagSignedResetKernel.instIsMarkovKernel :
    IsMarkovKernel gaussianZigZagSignedResetKernel := by
  unfold gaussianZigZagSignedResetKernel
  infer_instance

/-- The product-form reset preserves the regenerative event-epoch law. -/
theorem gaussianZigZagSignedResetKernel_invariant :
    gaussianZigZagSignedResetKernel.Invariant
      gaussianZigZagSignedEventTarget := by
  rw [Kernel.Invariant]
  unfold gaussianZigZagSignedResetKernel gaussianZigZagSignedEventTarget
  have hdecomp :
      (Kernel.const ℝ gaussianZigZagNegativeRayleighMeasure ∥ₖ
          Kernel.deterministic Bool.not (by fun_prop)) =
        ((Kernel.const ℝ gaussianZigZagNegativeRayleighMeasure ∥ₖ Kernel.id) ∘ₖ
          (Kernel.id ∥ₖ Kernel.deterministic Bool.not (by fun_prop))) := by
    rw [Kernel.parallelComp_comp_parallelComp]
    simp
  rw [hdecomp, ← Measure.comp_assoc]
  rw [← Measure.prod_comp_right]
  rw [← Measure.prod_comp_left]
  rw [Measure.const_comp, measure_univ, one_smul,
    Measure.deterministic_comp_eq_map, zigZagVelocityProbability_map_not]

theorem gaussianZigZagSignedResetKernel_apply (initial : ZigZagState) :
    gaussianZigZagSignedResetKernel initial =
      Measure.map (fun hazard : NNReal =>
        (gaussianZigZagNegativeRayleighReset hazard, !initial.2))
        gaussianZigZagHazardMeasure := by
  unfold gaussianZigZagSignedResetKernel
  rw [Kernel.parallelComp_apply, Kernel.const_apply,
    Kernel.deterministic_apply, Measure.prod_dirac,
    gaussianZigZagNegativeRayleighMeasure, Measure.map_map
      (by fun_prop) measurable_gaussianZigZagNegativeRayleighReset]
  rfl

/-- On the event-epoch law, the concrete inverse-clock event kernel agrees
almost surely with the abstract independent-redraw reset kernel. -/
theorem gaussianZigZagSignedEventKernel_ae_eq_resetKernel :
    (fun state => gaussianZigZagSignedEventKernel state) =ᵐ[
      gaussianZigZagSignedEventTarget]
      (fun state => gaussianZigZagSignedResetKernel state) := by
  filter_upwards [gaussianZigZagSignedEventTarget_negative_ae]
    with initial hinitial
  rw [gaussianZigZagSignedEventKernel_apply_of_neg initial hinitial,
    gaussianZigZagSignedResetKernel_apply]
  rfl

/-- The actual embedded signed event kernel preserves the negative-Rayleigh
position and independent uniform-velocity event-epoch law. -/
theorem gaussianZigZagSignedEventKernel_invariant :
    gaussianZigZagSignedEventKernel.Invariant
      gaussianZigZagSignedEventTarget := by
  rw [Kernel.Invariant]
  calc
    gaussianZigZagSignedEventKernel ∘ₘ gaussianZigZagSignedEventTarget =
        gaussianZigZagSignedResetKernel ∘ₘ
          gaussianZigZagSignedEventTarget :=
      Measure.bind_congr_right
        gaussianZigZagSignedEventKernel_ae_eq_resetKernel
    _ = gaussianZigZagSignedEventTarget :=
      gaussianZigZagSignedResetKernel_invariant

/-- Exact stopped endpoint viewed from signed coordinates. -/
noncomputable def gaussianZigZagSignedHorizonEndpoint
    (initial : ZigZagState) (horizon : NNReal)
    (hazards : ℕ → NNReal) : ZigZagState :=
  zigZagSignedCoordinate
    (gaussianZigZagHorizonEndpoint
      (zigZagSignedCoordinate initial) horizon hazards)

theorem measurable_gaussianZigZagSignedHorizonEndpoint_joint
    (horizon : NNReal) :
    Measurable (fun input : ZigZagState × (ℕ → NNReal) =>
      gaussianZigZagSignedHorizonEndpoint input.1 horizon input.2) := by
  unfold gaussianZigZagSignedHorizonEndpoint
  exact measurable_zigZagSignedCoordinate.comp
    (measurable_gaussianZigZagHorizonEndpoint_joint horizon |>.comp
      ((measurable_zigZagSignedCoordinate.comp measurable_fst).prodMk
        measurable_snd))

/-- A signed horizon row is the pushforward of the iid hazard stream through
the jointly measurable signed stopped endpoint. -/
theorem gaussianZigZagSignedHorizonKernel_apply_endpoint
    (horizon : NNReal) (initial : ZigZagState) :
    gaussianZigZagSignedHorizonKernel horizon initial =
      Measure.map (fun hazards =>
        gaussianZigZagSignedHorizonEndpoint initial horizon hazards)
        gaussianZigZagHazardSequenceMeasure := by
  have hmk : Measurable
      (Prod.mk (zigZagSignedCoordinate initial) :
        (ℕ → NNReal) → ZigZagState × (ℕ → NNReal)) :=
    measurable_const.prodMk measurable_id
  have hinner : Measurable
      ((fun input : ZigZagState × (ℕ → NNReal) =>
        gaussianZigZagHorizonEndpoint input.1 horizon input.2) ∘
          Prod.mk (zigZagSignedCoordinate initial)) :=
    (measurable_gaussianZigZagHorizonEndpoint_joint horizon).comp hmk
  rw [gaussianZigZagSignedHorizonKernel_apply]
  unfold gaussianZigZagHorizonKernel
  rw [Kernel.map_apply _
      (measurable_gaussianZigZagHorizonEndpoint_joint horizon),
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
    Measure.dirac_prod]
  rw [Measure.map_map
    (measurable_gaussianZigZagHorizonEndpoint_joint horizon)
    hmk]
  rw [Measure.map_map measurable_zigZagSignedCoordinate
    hinner]
  rfl

/-- Sampling form of the signed horizon kernel: retain the initial state,
draw an iid hazard stream, and evaluate the exact stopped endpoint. -/
noncomputable def gaussianZigZagSignedHorizonSamplingKernel
    (horizon : NNReal) : Kernel ZigZagState ZigZagState :=
  Kernel.map
    (Kernel.prod Kernel.id
      (Kernel.const ZigZagState gaussianZigZagHazardSequenceMeasure))
    (fun input =>
      gaussianZigZagSignedHorizonEndpoint input.1 horizon input.2)

instance gaussianZigZagSignedHorizonSamplingKernel.instIsMarkovKernel
    (horizon : NNReal) :
    IsMarkovKernel (gaussianZigZagSignedHorizonSamplingKernel horizon) := by
  unfold gaussianZigZagSignedHorizonSamplingKernel
  apply Kernel.IsMarkovKernel.map
  exact measurable_gaussianZigZagSignedHorizonEndpoint_joint horizon

theorem gaussianZigZagSignedHorizonSamplingKernel_eq
    (horizon : NNReal) :
    gaussianZigZagSignedHorizonSamplingKernel horizon =
      gaussianZigZagSignedHorizonKernel horizon := by
  ext initial
  have hmk : Measurable
      (Prod.mk initial : (ℕ → NNReal) → ZigZagState × (ℕ → NNReal)) :=
    measurable_const.prodMk measurable_id
  unfold gaussianZigZagSignedHorizonSamplingKernel
  rw [Kernel.map_apply _
      (measurable_gaussianZigZagSignedHorizonEndpoint_joint horizon),
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
    Measure.dirac_prod]
  rw [Measure.map_map
    (measurable_gaussianZigZagSignedHorizonEndpoint_joint horizon)
    hmk]
  rw [show ((fun input : ZigZagState × (ℕ → NNReal) =>
      gaussianZigZagSignedHorizonEndpoint input.1 horizon input.2) ∘
        Prod.mk initial) =
      (fun hazards =>
        gaussianZigZagSignedHorizonEndpoint initial horizon hazards) by rfl]
  rw [gaussianZigZagSignedHorizonKernel_apply_endpoint]

/-- Target-started signed horizon execution is the joint pushforward of an
initial target state and an independent iid hazard stream. -/
theorem gaussianZigZagSignedHorizonKernel_comp_target_eq_map
    (horizon : NNReal) :
    gaussianZigZagSignedHorizonKernel horizon ∘ₘ gaussianZigZagTarget =
      Measure.map
        (fun input : ZigZagState × (ℕ → NNReal) =>
          gaussianZigZagSignedHorizonEndpoint input.1 horizon input.2)
        (gaussianZigZagTarget.prod gaussianZigZagHazardSequenceMeasure) := by
  rw [← gaussianZigZagSignedHorizonSamplingKernel_eq horizon]
  unfold gaussianZigZagSignedHorizonSamplingKernel
  rw [← Measure.map_comp gaussianZigZagTarget
    (Kernel.prod Kernel.id
      (Kernel.const ZigZagState gaussianZigZagHazardSequenceMeasure))
    (measurable_gaussianZigZagSignedHorizonEndpoint_joint horizon)]
  congr 1
  rw [← Measure.compProd_eq_comp_prod gaussianZigZagTarget
    (Kernel.const ZigZagState gaussianZigZagHazardSequenceMeasure),
    Measure.compProd_const]

/-- Exact stopped-horizon identification: target-started execution can be
realized from stationary length-biased cycle occupation, an independent
velocity label, and an independent future hazard tail. -/
theorem gaussianZigZagSignedHorizonKernel_comp_target_eq_stationaryCycle
    (horizon : NNReal) :
    gaussianZigZagSignedHorizonKernel horizon ∘ₘ gaussianZigZagTarget =
      Measure.map
        (fun input : ((((ℝ × ℝ) × ℝ) × Bool) × (ℕ → NNReal)) =>
          let clocked := gaussianZigZagStationaryCycleStreamMap input
          gaussianZigZagSignedHorizonEndpoint clocked.1 horizon clocked.2)
        ((gaussianZigZagStationaryCycleMeasure.prod
          zigZagVelocityProbability).prod
            gaussianZigZagHazardSequenceMeasure) := by
  rw [gaussianZigZagSignedHorizonKernel_comp_target_eq_map,
    ← gaussianZigZagStationaryCycleStreamMap_map]
  rw [Measure.map_map
    (measurable_gaussianZigZagSignedHorizonEndpoint_joint horizon)
    measurable_gaussianZigZagStationaryCycleStreamMap]
  rfl

/-- Explicit first-event renewal branch in signed coordinates. Before the
first event the signed position translates at unit speed; after the event the
same signed stopped construction restarts from the canonical event update. -/
noncomputable def gaussianZigZagSignedFirstEventEndpoint
    (initial : ZigZagState) (horizon : NNReal)
    (headTail : NNReal × (ℕ → NNReal)) : ZigZagState :=
  let wait := gaussianZigZagSignedWaitingNNReal initial headTail.1
  if horizon < wait then
    (initial.1 + (horizon : ℝ), initial.2)
  else
    gaussianZigZagSignedHorizonEndpoint
      (gaussianZigZagSignedEventUpdate initial headTail.1)
      (horizon - wait) headTail.2

/-- Pathwise bridge from stationary-cycle coordinates to the exact signed
first-event recursion: the stored right reset is precisely the next event and
the geometric residual is precisely its waiting time. -/
theorem gaussianZigZagSignedFirstEventEndpoint_cycleResidual
    (signed rightReset : ℝ) (velocity : Bool) (horizon : NNReal)
    (tail : ℕ → NNReal) (hcover : signed < -rightReset)
    (hright : rightReset < 0) :
    gaussianZigZagSignedFirstEventEndpoint (signed, velocity) horizon
        (gaussianZigZagCycleResidualHazard signed rightReset, tail) =
      if horizon < gaussianZigZagCycleRemainingTime signed rightReset then
        (signed + (horizon : ℝ), velocity)
      else
        gaussianZigZagSignedHorizonEndpoint (rightReset, !velocity)
          (horizon - gaussianZigZagCycleRemainingTime signed rightReset) tail := by
  unfold gaussianZigZagSignedFirstEventEndpoint
  rw [gaussianZigZagSignedWaitingNNReal_cycleResidual
      signed rightReset velocity hcover hright,
    gaussianZigZagSignedEventUpdate_cycleResidual
      signed rightReset velocity hcover hright]

/-- The physical first-event branch, conjugated by the signed involution, is
the explicit unit-speed signed renewal branch. -/
theorem zigZagSignedCoordinate_gaussianZigZagFirstEventEndpoint
    (initial : ZigZagState) (horizon : NNReal)
    (headTail : NNReal × (ℕ → NNReal)) :
    zigZagSignedCoordinate
        (gaussianZigZagFirstEventEndpoint
          (zigZagSignedCoordinate initial) horizon headTail) =
      gaussianZigZagSignedFirstEventEndpoint initial horizon headTail := by
  simp only [gaussianZigZagFirstEventEndpoint,
    gaussianZigZagSignedFirstEventEndpoint,
    gaussianZigZagSignedWaitingNNReal]
  split_ifs with hbefore
  · rw [zigZagSignedCoordinate_flow,
      zigZagSignedPosition_signedCoordinate]
    rfl
  · unfold gaussianZigZagSignedHorizonEndpoint
      gaussianZigZagSignedEventUpdate
    rw [zigZagSignedCoordinate_involutive]

/-- Pointwise first-event equation for the signed stopped executor under the
explicit positive, divergent-tail conditions used in the nonexplosion proof. -/
theorem gaussianZigZagSignedHorizonEndpoint_eq_firstEvent_of_goodTail
    (initial : ZigZagState) (horizon : NNReal)
    (headTail : NNReal × (ℕ → NNReal))
    (htailPositive : ∀ index, 0 < headTail.2 index)
    (htailDiverges : (∑' index,
      gaussianZigZagSqrtHazardTerm headTail.2 index) = ∞) :
    gaussianZigZagSignedHorizonEndpoint initial horizon
        (gaussianZigZagHazardCons headTail) =
      gaussianZigZagSignedFirstEventEndpoint initial horizon headTail := by
  have hphysical : gaussianZigZagHorizonEndpoint
      (zigZagSignedCoordinate initial) horizon
      (gaussianZigZagHazardCons headTail) =
      gaussianZigZagFirstEventEndpoint
        (zigZagSignedCoordinate initial) horizon headTail := by
    by_cases hbefore : horizon <
        gaussianZigZagWaitingNNReal (zigZagSignedCoordinate initial) headTail.1
    · have hpoint := gaussianZigZagHorizonEndpoint_eq_flow_of_lt_firstWait
        (zigZagSignedCoordinate initial) horizon
        (gaussianZigZagHazardCons headTail)
        (by simpa [gaussianZigZagEventWait, gaussianZigZagEventState,
          gaussianZigZagHazardCons] using hbefore)
      simpa [gaussianZigZagFirstEventEndpoint, hbefore] using hpoint
    · have hwait : gaussianZigZagEventWait
          (zigZagSignedCoordinate initial)
          (gaussianZigZagHazardCons headTail) 0 ≤ horizon := by
        simpa [gaussianZigZagEventWait, gaussianZigZagEventState,
          gaussianZigZagHazardCons] using not_lt.mp hbefore
      have htailExists : ∃ eventCount, gaussianZigZagEventCrossed
          (gaussianZigZagEventUpdate
            (zigZagSignedCoordinate initial) headTail.1)
          (horizon - gaussianZigZagWaitingNNReal
            (zigZagSignedCoordinate initial) headTail.1)
          headTail.2 eventCount :=
        gaussianZigZagEventCrossed_exists_of_positive_of_sqrt_tsum
          _ _ _ htailPositive htailDiverges
      have hpoint := gaussianZigZagHorizonEndpoint_eq_tail_of_firstWait_le
        (zigZagSignedCoordinate initial) horizon
        (gaussianZigZagHazardCons headTail) hwait
        (by simpa [gaussianZigZagEventWait, gaussianZigZagEventState,
          gaussianZigZagHazardCons] using htailExists)
      simpa [gaussianZigZagFirstEventEndpoint, hbefore,
        gaussianZigZagEventWait, gaussianZigZagEventState,
        gaussianZigZagHazardCons] using hpoint
  unfold gaussianZigZagSignedHorizonEndpoint
  rw [hphysical,
    zigZagSignedCoordinate_gaussianZigZagFirstEventEndpoint]

omit [MeasurableSpace ZigZagState] in
theorem gaussianZigZagCycleResidualHazard_reset_of_nonpos
    (signed : ℝ) (hazard : NNReal) (hsigned : signed ≤ 0) :
    gaussianZigZagCycleResidualHazard signed
        (gaussianZigZagNegativeRayleighReset hazard) = hazard := by
  unfold gaussianZigZagCycleResidualHazard
  rw [max_eq_left hsigned]
  simp

/-- On every terminating good regenerative input, exact stopped execution
commutes with the suspension endpoint and its signed-state decoder. -/
theorem gaussianZigZagSignedHorizonEndpoint_suspensionState
    (eventCount : ℕ) :
    ∀ (input : ((((ℝ × ℝ) × (ℕ → NNReal)) × Bool) × ℝ))
      (horizon : NNReal),
      input.1.1.1.1 < 0 ∧ input.1.1.1.2 < 0 →
      0 ≤ input.2 →
      input.2 < gaussianZigZagCyclePhaseEnvironmentRoof input.1 →
      (∀ index, 0 < input.1.1.2 index) →
      (∑' index, gaussianZigZagSqrtHazardTerm input.1.1.2 index) = ∞ →
      suspensionCrossed gaussianZigZagCyclePhaseEnvironmentShift
        gaussianZigZagCyclePhaseEnvironmentRoof input.1 input.2
          (horizon : ℝ) eventCount →
      gaussianZigZagSignedHorizonEndpoint
          (gaussianZigZagSuspensionState input) horizon
          (gaussianZigZagSuspensionHazardStream input) =
        gaussianZigZagSuspensionState
          (suspensionEndpoint gaussianZigZagCyclePhaseEnvironmentShift
            gaussianZigZagCyclePhaseEnvironmentRoof (horizon : ℝ) input) := by
  induction eventCount with
  | zero =>
      intro input horizon hresets hage hbelow hpositive hdiverges hcrossed
      have hroof : gaussianZigZagCyclePhaseEnvironmentRoof input.1 =
          -input.1.1.1.2 - input.1.1.1.1 := by
        unfold gaussianZigZagCyclePhaseEnvironmentRoof
          gaussianZigZagCycleEnvironmentRoof
        rw [NNReal.coe_toNNReal]
        linarith
      have hcover : (gaussianZigZagSuspensionState input).1 <
          -input.1.1.1.2 := by
        unfold gaussianZigZagSuspensionState
        rw [hroof] at hbelow
        linarith
      have hbefore : input.2 + (horizon : ℝ) <
          gaussianZigZagCyclePhaseEnvironmentRoof input.1 := by
        simpa [suspensionCrossed, suspensionRoofElapsed] using hcrossed
      have hremaining : horizon < gaussianZigZagCycleRemainingTime
          (gaussianZigZagSuspensionState input).1 input.1.1.1.2 := by
        apply NNReal.coe_lt_coe.mp
        rw [coe_gaussianZigZagCycleRemainingTime _ _ hcover, hroof]
        unfold gaussianZigZagSuspensionState
        linarith
      rw [show gaussianZigZagSuspensionHazardStream input =
          gaussianZigZagHazardCons
            (gaussianZigZagCycleResidualHazard
              (gaussianZigZagSuspensionState input).1 input.1.1.1.2,
              input.1.1.2) by rfl,
        gaussianZigZagSignedHorizonEndpoint_eq_firstEvent_of_goodTail
          _ _ _ hpositive hdiverges,
        gaussianZigZagSignedFirstEventEndpoint_cycleResidual
          _ _ _ _ _ hcover hresets.2,
        if_pos hremaining,
        suspensionEndpoint_eq_translate_of_lt_roof
          gaussianZigZagCyclePhaseEnvironmentShift
          gaussianZigZagCyclePhaseEnvironmentRoof (horizon : ℝ) input hbefore]
      unfold gaussianZigZagSuspensionState
      congr 1
      ring
  | succ eventCount ih =>
      intro input horizon hresets hage hbelow hpositive hdiverges hcrossed
      have hroof : gaussianZigZagCyclePhaseEnvironmentRoof input.1 =
          -input.1.1.1.2 - input.1.1.1.1 := by
        unfold gaussianZigZagCyclePhaseEnvironmentRoof
          gaussianZigZagCycleEnvironmentRoof
        rw [NNReal.coe_toNNReal]
        linarith
      have hcover : (gaussianZigZagSuspensionState input).1 <
          -input.1.1.1.2 := by
        unfold gaussianZigZagSuspensionState
        rw [hroof] at hbelow
        linarith
      let remaining := gaussianZigZagCycleRemainingTime
        (gaussianZigZagSuspensionState input).1 input.1.1.1.2
      have hremainingCoe : (remaining : ℝ) =
          gaussianZigZagCyclePhaseEnvironmentRoof input.1 - input.2 := by
        unfold remaining
        rw [coe_gaussianZigZagCycleRemainingTime _ _ hcover, hroof]
        unfold gaussianZigZagSuspensionState
        ring
      rw [show gaussianZigZagSuspensionHazardStream input =
          gaussianZigZagHazardCons
            (gaussianZigZagCycleResidualHazard
              (gaussianZigZagSuspensionState input).1 input.1.1.1.2,
              input.1.1.2) by rfl,
        gaussianZigZagSignedHorizonEndpoint_eq_firstEvent_of_goodTail
          _ _ _ hpositive hdiverges,
        gaussianZigZagSignedFirstEventEndpoint_cycleResidual
          _ _ _ _ _ hcover hresets.2]
      by_cases hbefore : horizon < remaining
      · rw [if_pos hbefore]
        have hbeforeReal : input.2 + (horizon : ℝ) <
            gaussianZigZagCyclePhaseEnvironmentRoof input.1 := by
          exact_mod_cast hbefore
          rw [hremainingCoe]
          linarith
        rw [suspensionEndpoint_eq_translate_of_lt_roof
          gaussianZigZagCyclePhaseEnvironmentShift
          gaussianZigZagCyclePhaseEnvironmentRoof (horizon : ℝ) input
          hbeforeReal]
        unfold gaussianZigZagSuspensionState
        congr 1
        ring
      · rw [if_neg hbefore]
        have hreach : gaussianZigZagCyclePhaseEnvironmentRoof input.1 ≤
            input.2 + (horizon : ℝ) := by
          have := not_lt.mp hbefore
          exact_mod_cast this
          rw [hremainingCoe]
          linarith
        let shiftedInput :=
          (gaussianZigZagCyclePhaseEnvironmentShift input.1, (0 : ℝ))
        let residual := horizon - remaining
        have hresidualCoe : (residual : ℝ) =
            input.2 + (horizon : ℝ) -
              gaussianZigZagCyclePhaseEnvironmentRoof input.1 := by
          unfold residual
          rw [NNReal.coe_sub (not_lt.mp hbefore), hremainingCoe]
          ring
        have htailCrossed : suspensionCrossed
            gaussianZigZagCyclePhaseEnvironmentShift
            gaussianZigZagCyclePhaseEnvironmentRoof shiftedInput.1 shiftedInput.2
              (residual : ℝ) eventCount := by
          apply (suspensionCrossed_succ_iff_tail
            gaussianZigZagCyclePhaseEnvironmentShift
            gaussianZigZagCyclePhaseEnvironmentRoof input (horizon : ℝ)
              eventCount).mp at hcrossed
          simpa [shiftedInput, hresidualCoe] using hcrossed
        have hshiftedResets : shiftedInput.1.1.1.1 < 0 ∧
            shiftedInput.1.1.1.2 < 0 := by
          unfold shiftedInput gaussianZigZagCyclePhaseEnvironmentShift
            gaussianZigZagCycleEnvironmentShift
          exact ⟨hresets.2, by
            unfold gaussianZigZagNegativeRayleighReset
            exact neg_lt_zero.mpr (Real.sqrt_pos.2 (by positivity))⟩
        have hshiftedBelow : shiftedInput.2 <
            gaussianZigZagCyclePhaseEnvironmentRoof shiftedInput.1 := by
          unfold shiftedInput gaussianZigZagCyclePhaseEnvironmentShift
            gaussianZigZagCycleEnvironmentShift
            gaussianZigZagCyclePhaseEnvironmentRoof
            gaussianZigZagCycleEnvironmentRoof
          rw [NNReal.coe_toNNReal]
          · linarith [Real.sqrt_pos.2 (show 0 <
                2 * (input.1.1.2 0 : ℝ) by positivity)]
          · positivity
        have hshiftedPositive : ∀ index, 0 < shiftedInput.1.1.2 index := by
          intro index
          simpa [shiftedInput, gaussianZigZagCyclePhaseEnvironmentShift,
            gaussianZigZagCycleEnvironmentShift] using hpositive (index + 1)
        have hshiftedDiverges : (∑' index,
            gaussianZigZagSqrtHazardTerm shiftedInput.1.1.2 index) = ∞ := by
          have htail := ENNReal.tsum_add_one_eq_top hdiverges
            (by exact ENNReal.ofReal_ne_top)
          simpa [shiftedInput, gaussianZigZagCyclePhaseEnvironmentShift,
            gaussianZigZagCycleEnvironmentShift,
            gaussianZigZagSqrtHazardTerm] using htail
        have hstream : gaussianZigZagSuspensionHazardStream shiftedInput =
            input.1.1.2 := by
          funext index
          cases index with
          | zero =>
              simp only [gaussianZigZagSuspensionHazardStream,
                gaussianZigZagHazardCons]
              rw [gaussianZigZagCycleResidualHazard_reset_of_nonpos]
              exact hresets.2.le
          | succ index =>
              simp [gaussianZigZagSuspensionHazardStream,
                gaussianZigZagHazardCons, shiftedInput,
                gaussianZigZagCyclePhaseEnvironmentShift,
                gaussianZigZagCycleEnvironmentShift]
        have hrecursive := ih shiftedInput residual hshiftedResets
          (by simp [shiftedInput]) hshiftedBelow hshiftedPositive
          hshiftedDiverges htailCrossed
        rw [hstream] at hrecursive
        rw [hrecursive]
        have hendpoint := suspensionEndpoint_crossing_recursion
          gaussianZigZagCyclePhaseEnvironmentShift
          gaussianZigZagCyclePhaseEnvironmentRoof input (horizon : ℝ)
          hreach ⟨eventCount + 1, hcrossed⟩
        rw [hendpoint]
        congr 1
        exact hresidualCoe

/-- The pathwise commuting equation holds almost surely under normalized
stationary suspension occupation. -/
theorem gaussianZigZagSignedHorizonEndpoint_suspensionState_ae
    (horizon : NNReal) :
    (fun input => gaussianZigZagSignedHorizonEndpoint
        (gaussianZigZagSuspensionState input) horizon
        (gaussianZigZagSuspensionHazardStream input)) =ᵐ[
      gaussianZigZagNormalizedSuspensionOccupationMeasure]
    (fun input => gaussianZigZagSuspensionState
      (suspensionEndpoint gaussianZigZagCyclePhaseEnvironmentShift
        gaussianZigZagCyclePhaseEnvironmentRoof (horizon : ℝ) input)) := by
  have hbaseGood : ∀ᵐ base ∂gaussianZigZagCyclePhaseEnvironmentMeasure,
      (base.1.1.1 < 0 ∧ base.1.1.2 < 0) ∧
      (∀ index, 0 < base.1.2 index) ∧
      (∑' index, gaussianZigZagSqrtHazardTerm base.1.2 index) = ∞ ∧
      (∀ shift, 0 ≤ shift → ∃ eventCount,
        suspensionCrossed gaussianZigZagCyclePhaseEnvironmentShift
          gaussianZigZagCyclePhaseEnvironmentRoof base 0 shift eventCount) := by
    have hresets := (Measure.quasiMeasurePreserving_fst
      (μ := gaussianZigZagCycleEnvironmentMeasure)
      (ν := zigZagVelocityProbability)).ae
        gaussianZigZagCycleEnvironment_resets_negative_ae
    have hpositive := (Measure.quasiMeasurePreserving_fst
      (μ := gaussianZigZagCycleEnvironmentMeasure)
      (ν := zigZagVelocityProbability)).ae
        ((Measure.quasiMeasurePreserving_snd
          (μ := gaussianZigZagNegativeRayleighMeasure.prod
            gaussianZigZagNegativeRayleighMeasure)
          (ν := gaussianZigZagHazardSequenceMeasure)).ae
            gaussianZigZagHazardSequence_positive_ae)
    have hdiverges := (Measure.quasiMeasurePreserving_fst
      (μ := gaussianZigZagCycleEnvironmentMeasure)
      (ν := zigZagVelocityProbability)).ae
        ((Measure.quasiMeasurePreserving_snd
          (μ := gaussianZigZagNegativeRayleighMeasure.prod
            gaussianZigZagNegativeRayleighMeasure)
          (ν := gaussianZigZagHazardSequenceMeasure)).ae
            gaussianZigZagSqrtHazard_tsum_eq_top_ae)
    filter_upwards [hresets, hpositive, hdiverges,
      gaussianZigZagCyclePhaseEnvironment_nonexplosive_ae]
      with base hresets hpositive hdiverges hnonexplosive
    exact ⟨hresets, hpositive, hdiverges, hnonexplosive⟩
  have hproductGood : ∀ᵐ input ∂
      gaussianZigZagCyclePhaseEnvironmentMeasure.prod volume,
      (input.1.1.1.1 < 0 ∧ input.1.1.1.2 < 0) ∧
      (∀ index, 0 < input.1.1.2 index) ∧
      (∑' index, gaussianZigZagSqrtHazardTerm input.1.1.2 index) = ∞ ∧
      (∀ shift, 0 ≤ shift → ∃ eventCount,
        suspensionCrossed gaussianZigZagCyclePhaseEnvironmentShift
          gaussianZigZagCyclePhaseEnvironmentRoof input.1 0 shift eventCount) :=
    (Measure.quasiMeasurePreserving_fst
      (μ := gaussianZigZagCyclePhaseEnvironmentMeasure)
      (ν := (volume : Measure ℝ))).ae hbaseGood
  have hdomain := measurableSet_suspensionFundamentalDomain
    measurable_gaussianZigZagCyclePhaseEnvironmentRoof
  have hoccupation : ∀ᵐ input ∂gaussianZigZagSuspensionOccupationMeasure,
      (input.1.1.1.1 < 0 ∧ input.1.1.1.2 < 0) ∧
      (∀ index, 0 < input.1.1.2 index) ∧
      (∑' index, gaussianZigZagSqrtHazardTerm input.1.1.2 index) = ∞ ∧
      input ∈ suspensionFundamentalDomain
        gaussianZigZagCyclePhaseEnvironmentRoof ∧
      (∀ shift, 0 ≤ shift → ∃ eventCount,
        suspensionCrossed gaussianZigZagCyclePhaseEnvironmentShift
          gaussianZigZagCyclePhaseEnvironmentRoof input.1 0 shift eventCount) := by
    unfold gaussianZigZagSuspensionOccupationMeasure
      suspensionOccupationMeasure
    rw [ae_restrict_iff' hdomain]
    filter_upwards [hproductGood] with input hgood hmem
    exact ⟨hgood.1, hgood.2.1, hgood.2.2.1, hmem, hgood.2.2.2⟩
  unfold gaussianZigZagNormalizedSuspensionOccupationMeasure
  rw [ae_smul_measure]
  filter_upwards [hoccupation] with input hgood
  have hage : 0 ≤ input.2 := hgood.2.2.2.1.1
  have hbelow : input.2 <
      gaussianZigZagCyclePhaseEnvironmentRoof input.1 :=
    hgood.2.2.2.1.2
  obtain ⟨eventCount, hcrossedZero⟩ := hgood.2.2.2.2
    (input.2 + (horizon : ℝ)) (by positivity)
  have hcrossed : suspensionCrossed
      gaussianZigZagCyclePhaseEnvironmentShift
      gaussianZigZagCyclePhaseEnvironmentRoof input.1 input.2
        (horizon : ℝ) eventCount := by
    simpa [suspensionCrossed] using hcrossedZero
  exact gaussianZigZagSignedHorizonEndpoint_suspensionState eventCount
    input horizon hgood.1 hage hbelow hgood.2.1 hgood.2.2.1 hcrossed

/-- The signed-state marginal of normalized stationary suspension occupation
is exactly the Gaussian phase target. -/
theorem gaussianZigZagSuspensionState_map_normalized :
    Measure.map gaussianZigZagSuspensionState
        gaussianZigZagNormalizedSuspensionOccupationMeasure =
      gaussianZigZagTarget := by
  have hstate : Measurable gaussianZigZagSuspensionState := by
    unfold gaussianZigZagSuspensionState
    fun_prop
  have hfactor : gaussianZigZagSuspensionState =
      Prod.fst ∘ gaussianZigZagStationaryCycleStreamMap ∘
        gaussianZigZagSuspensionDecode := by
    funext input
    rw [gaussianZigZagStationaryCycleStreamMap_decode]
    rfl
  rw [hfactor, ← Measure.map_map measurable_fst
    measurable_gaussianZigZagStationaryCycleStreamMap,
    ← Measure.map_map
      (measurable_fst.comp measurable_gaussianZigZagStationaryCycleStreamMap)
      measurable_gaussianZigZagSuspensionDecode,
    gaussianZigZagSuspensionDecode_map_normalized,
    gaussianZigZagStationaryCycleStreamMap_map,
    Measure.map_fst_prod, measure_univ, one_smul]

/-- The exact stopped signed Gaussian Zig-Zag kernel preserves the Gaussian
phase target at every nonnegative horizon. -/
theorem gaussianZigZagSignedHorizonKernel_invariant
    (horizon : NNReal) :
    (gaussianZigZagSignedHorizonKernel horizon).Invariant
      gaussianZigZagTarget := by
  rw [Kernel.Invariant,
    gaussianZigZagSignedHorizonKernel_comp_target_eq_stationaryCycle]
  let execute := fun input : ((((ℝ × ℝ) × ℝ) × Bool) ×
      (ℕ → NNReal)) =>
    let clocked := gaussianZigZagStationaryCycleStreamMap input
    gaussianZigZagSignedHorizonEndpoint clocked.1 horizon clocked.2
  have hexecute : Measurable execute := by
    unfold execute
    exact (measurable_gaussianZigZagSignedHorizonEndpoint_joint horizon).comp
      measurable_gaussianZigZagStationaryCycleStreamMap
  rw [← gaussianZigZagSuspensionDecode_map_normalized,
    Measure.map_map hexecute measurable_gaussianZigZagSuspensionDecode]
  have hcomposition : execute ∘ gaussianZigZagSuspensionDecode =
      fun input => gaussianZigZagSignedHorizonEndpoint
        (gaussianZigZagSuspensionState input) horizon
        (gaussianZigZagSuspensionHazardStream input) := by
    funext input
    unfold execute Function.comp_def
    rw [gaussianZigZagStationaryCycleStreamMap_decode]
  rw [hcomposition]
  rw [Measure.map_congr
    (gaussianZigZagSignedHorizonEndpoint_suspensionState_ae horizon)]
  have hstate : Measurable gaussianZigZagSuspensionState := by
    unfold gaussianZigZagSuspensionState
    fun_prop
  have hendpoint := measurable_suspensionEndpoint
    measurable_gaussianZigZagCyclePhaseEnvironmentShift
    measurable_gaussianZigZagCyclePhaseEnvironmentRoof (horizon : ℝ)
  rw [← Measure.map_map hstate hendpoint,
    gaussianZigZagSuspensionEndpoint_map_normalized,
    gaussianZigZagSuspensionState_map_normalized]

/-- Signed-coordinate conjugation is involutive at the kernel level. -/
theorem gaussianZigZagHorizonKernel_eq_signed_conjugate
    (horizon : NNReal) :
    gaussianZigZagHorizonKernel horizon =
      Kernel.map
        (Kernel.comap (gaussianZigZagSignedHorizonKernel horizon)
          zigZagSignedCoordinate measurable_zigZagSignedCoordinate)
        zigZagSignedCoordinate := by
  ext initial event hevent
  rw [Kernel.map_apply' _ measurable_zigZagSignedCoordinate _ hevent,
    Kernel.comap_apply', gaussianZigZagSignedHorizonKernel_apply]
  rw [Measure.map_apply measurable_zigZagSignedCoordinate
    (measurable_zigZagSignedCoordinate hevent)]
  rw [zigZagSignedCoordinate_involutive]
  congr 1
  have hcomp : zigZagSignedCoordinate ∘ zigZagSignedCoordinate = id := by
    funext state
    exact zigZagSignedCoordinate_involutive state
  change event = (zigZagSignedCoordinate ∘ zigZagSignedCoordinate) ⁻¹' event
  rw [hcomp, Set.preimage_id]

/-- The physical and signed horizon kernels preserve the Gaussian target
simultaneously.  This is an exact coordinate-transport equivalence, not an
additional generator or process-uniqueness premise. -/
theorem gaussianZigZagSignedHorizonKernel_invariant_iff
    (horizon : NNReal) :
    (gaussianZigZagSignedHorizonKernel horizon).Invariant
        gaussianZigZagTarget ↔
      (gaussianZigZagHorizonKernel horizon).Invariant
        gaussianZigZagTarget := by
  have transported (kernel : Kernel ZigZagState ZigZagState) :
      (Kernel.map
          (Kernel.comap kernel zigZagSignedCoordinate
            measurable_zigZagSignedCoordinate)
          zigZagSignedCoordinate) ∘ₘ gaussianZigZagTarget =
        (kernel ∘ₘ
          (gaussianZigZagTarget.map zigZagSignedCoordinate)).map
            zigZagSignedCoordinate := by
    rw [← Measure.map_comp gaussianZigZagTarget
      (Kernel.comap kernel zigZagSignedCoordinate
        measurable_zigZagSignedCoordinate)
      measurable_zigZagSignedCoordinate]
    congr 1
    rw [← Kernel.comp_deterministic_eq_comap,
      ← Measure.comp_assoc, Measure.deterministic_comp_eq_map]
  constructor
  · intro hsigned
    rw [gaussianZigZagHorizonKernel_eq_signed_conjugate]
    rw [Kernel.Invariant] at hsigned ⊢
    rw [transported, gaussianZigZagTarget_map_signedCoordinate,
      hsigned, gaussianZigZagTarget_map_signedCoordinate]
  · intro hphysical
    unfold gaussianZigZagSignedHorizonKernel
    rw [Kernel.Invariant] at hphysical ⊢
    rw [transported, gaussianZigZagTarget_map_signedCoordinate,
      hphysical, gaussianZigZagTarget_map_signedCoordinate]

/-- The production physical-coordinate stopped Gaussian Zig-Zag kernel
preserves its Gaussian phase target at every nonnegative horizon. -/
theorem gaussianZigZagHorizonKernel_invariant (horizon : NNReal) :
    (gaussianZigZagHorizonKernel horizon).Invariant
      gaussianZigZagTarget :=
  (gaussianZigZagSignedHorizonKernel_invariant_iff horizon).mp
    (gaussianZigZagSignedHorizonKernel_invariant horizon)

/-- Kernel-level first-event equation. From a fixed state, the exact horizon
transition can equivalently sample one exponential hazard and an independent
fresh tail, then execute the explicit no-event/event branch. -/
theorem gaussianZigZagHorizonKernel_apply_firstEvent
    (horizon : NNReal) (initial : ZigZagState) :
    gaussianZigZagHorizonKernel horizon initial =
      Measure.map (gaussianZigZagFirstEventEndpoint initial horizon)
        (gaussianZigZagHazardMeasure.prod
          gaussianZigZagHazardSequenceMeasure) := by
  unfold gaussianZigZagHorizonKernel
  rw [Kernel.map_apply _
      (measurable_gaussianZigZagHorizonEndpoint_joint horizon),
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
    Measure.dirac_prod, Measure.map_map
      (measurable_gaussianZigZagHorizonEndpoint_joint horizon) (by fun_prop)]
  change Measure.map (gaussianZigZagHorizonEndpoint initial horizon)
      gaussianZigZagHazardSequenceMeasure = _
  exact gaussianZigZagHorizonEndpoint_firstEventLaw initial horizon

/-- Kernel-level first-event renewal equation in canonical signed
coordinates. -/
theorem gaussianZigZagSignedHorizonKernel_apply_firstEvent
    (horizon : NNReal) (initial : ZigZagState) :
    gaussianZigZagSignedHorizonKernel horizon initial =
      Measure.map
        (gaussianZigZagSignedFirstEventEndpoint initial horizon)
        (gaussianZigZagHazardMeasure.prod
          gaussianZigZagHazardSequenceMeasure) := by
  rw [gaussianZigZagSignedHorizonKernel_apply,
    gaussianZigZagHorizonKernel_apply_firstEvent]
  rw [AEMeasurable.map_map_of_aemeasurable
    measurable_zigZagSignedCoordinate.aemeasurable
    (aemeasurable_gaussianZigZagFirstEventEndpoint
      (zigZagSignedCoordinate initial) horizon)]
  congr 1
  funext headTail
  exact zigZagSignedCoordinate_gaussianZigZagFirstEventEndpoint
    initial horizon headTail

@[simp] theorem gaussianZigZagHorizonKernel_zero :
    gaussianZigZagHorizonKernel 0 = Kernel.id := by
  ext initial event hevent
  unfold gaussianZigZagHorizonKernel
  rw [Kernel.map_apply _ (measurable_gaussianZigZagHorizonEndpoint_joint 0),
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
    Measure.dirac_prod, Measure.map_map
      (measurable_gaussianZigZagHorizonEndpoint_joint 0) (by fun_prop)]
  have hae : (fun hazards => gaussianZigZagHorizonEndpoint initial 0 hazards) =ᵐ[
      gaussianZigZagHazardSequenceMeasure] (fun _ => initial) :=
    gaussianZigZagHorizonEndpoint_zero_ae initial
  have hae' : ((fun input => gaussianZigZagHorizonEndpoint input.1 0 input.2) ∘
      Prod.mk initial) =ᵐ[gaussianZigZagHazardSequenceMeasure]
      (fun _ => initial) := hae
  rw [Measure.map_congr hae']
  simp [hevent]

/-- The sole remaining setwise forward-equation data for the exact Gaussian
Zig-Zag path law. Zero-time conservativity is already proved by
`gaussianZigZagHorizonKernel_zero`. -/
structure GaussianZigZagForwardEquation : Prop where
  differentiable : ∀ event, MeasurableSet event →
    DifferentiableOn ℝ
      (transportedRealMass gaussianZigZagHorizonKernel
        gaussianZigZagTarget event) (Set.Ici 0)
  fderivWithin_eq_zero : ∀ event, MeasurableSet event →
    ∀ time ∈ Set.Ici (0 : ℝ),
      fderivWithin ℝ
        (transportedRealMass gaussianZigZagHorizonKernel
        gaussianZigZagTarget event) (Set.Ici 0) time = 0

/-- Compact-test alternative to the setwise Gaussian forward equation. It is
the natural process-level consumer of the compactly supported smooth generator
core. Regularity of the transported measures is kept as a separate premise of
the invariance theorem below. -/
abbrev GaussianZigZagCompactForwardEquation :=
  CompactTestForwardStationarityCertificate
    gaussianZigZagHorizonKernel gaussianZigZagTarget

/-- Weak-forward uniqueness statement for the exact Gaussian Zig-Zag path law
on the certified compact `C¹` generator domain. -/
abbrev GaussianZigZagWeakForwardUniqueness :=
  CompactTestWeakForwardUniqueness gaussianZigZagHorizonKernel
    GaussianZigZagSmoothTest.observe GaussianZigZagSmoothTest.generator

/-- Target-started uniqueness, the minimal process-level premise needed for
Gaussian stationarity. -/
abbrev GaussianZigZagTargetWeakForwardUniqueness :=
  CompactTestTargetWeakForwardUniqueness gaussianZigZagHorizonKernel
    GaussianZigZagSmoothTest.observe GaussianZigZagSmoothTest.generator
    gaussianZigZagTarget

/-- Scalar-expectation part of Gaussian Zig-Zag weak-forward uniqueness. -/
abbrev GaussianZigZagWeakExpectationUniqueness :=
  CompactTestWeakExpectationUniqueness gaussianZigZagHorizonKernel
    GaussianZigZagSmoothTest.observe GaussianZigZagSmoothTest.generator

/-- Target-started scalar-expectation uniqueness, the minimal scalar ODE
premise for Gaussian stationarity. -/
abbrev GaussianZigZagTargetWeakExpectationUniqueness :=
  CompactTestTargetWeakExpectationUniqueness gaussianZigZagHorizonKernel
    GaussianZigZagSmoothTest.observe GaussianZigZagSmoothTest.generator
    gaussianZigZagTarget

/-- Measure-determination part of the Gaussian smooth-core obligation. -/
abbrev GaussianZigZagSmoothTestDetermining :=
  CompactTestExpectationDetermining GaussianZigZagSmoothTest.observe

/-- Natural regular-measure version of smooth-test determination. This is the
appropriate obligation for finite Borel laws on the locally compact Zig-Zag
state space. -/
abbrev GaussianZigZagSmoothTestRegularDetermining :=
  CompactTestRegularExpectationDetermining GaussianZigZagSmoothTest.observe

/-- Finite regular determination is the exact strength used by
probability-valued weak-forward curves. -/
abbrev GaussianZigZagSmoothTestFiniteRegularDetermining :=
  CompactTestFiniteRegularExpectationDetermining
    GaussianZigZagSmoothTest.observe

/-- Compact `C¹` fiber tests determine every finite regular measure on the
Gaussian Zig-Zag state space. -/
theorem gaussianZigZagSmoothTest_finiteRegularDetermining :
    GaussianZigZagSmoothTestFiniteRegularDetermining where
  eq_of_expectations left right hleftRegular hrightRegular
      hleftFinite hrightFinite heq := by
    letI : left.Regular := hleftRegular
    letI : right.Regular := hrightRegular
    letI : IsFiniteMeasure left := hleftFinite
    letI : IsFiniteMeasure right := hrightFinite
    apply measure_eq_of_zigZagFiberMeasure_eq
    intro velocity
    apply Measure.ext_of_integral_eq_on_contDiff_compactSupport
    intro test hsmooth hcompact
    have hderiv : ∀ q, HasDerivAt test (deriv test q) q := by
      intro q
      exact (hsmooth.differentiable (by norm_num)).differentiableAt.hasDerivAt
    let fiberTest := GaussianZigZagSmoothTest.ofFiberCompact velocity test
      (deriv test) hderiv hsmooth hcompact
    have hfull := heq fiberTest
    rw [integral_zigZagFiberMeasure left velocity test hsmooth.continuous,
      integral_zigZagFiberMeasure right velocity test hsmooth.continuous]
    simpa [fiberTest, GaussianZigZagSmoothTest.ofFiberCompact,
      GaussianZigZagSmoothTest.ofFiber,
      GaussianZigZagSmoothTest.observe] using hfull

theorem GaussianZigZagForwardEquation.toSetwiseCertificate
    (forward : GaussianZigZagForwardEquation) :
    SetwiseForwardStationarityCertificate
      gaussianZigZagHorizonKernel gaussianZigZagTarget where
  zero := gaussianZigZagHorizonKernel_zero
  differentiable := forward.differentiable
  fderivWithin_eq_zero := forward.fderivWithin_eq_zero

/-- The exact Gaussian Zig-Zag horizon family is stationary once its
constructed path law is shown to solve the setwise forward equation. This is
the precise analytic consumer of generator cancellation; infinitesimal balance
alone is not silently upgraded to stationarity. -/
theorem gaussianZigZagHorizonKernel_invariant_of_forwardCertificate
    (certificate : SetwiseForwardStationarityCertificate
      gaussianZigZagHorizonKernel gaussianZigZagTarget)
    (horizon : NNReal) :
    (gaussianZigZagHorizonKernel horizon).Invariant gaussianZigZagTarget :=
  certificate.invariant gaussianZigZagHorizonKernel gaussianZigZagTarget horizon

theorem gaussianZigZagHorizonKernel_invariant_of_forwardEquation
    (forward : GaussianZigZagForwardEquation) (horizon : NNReal) :
    (gaussianZigZagHorizonKernel horizon).Invariant gaussianZigZagTarget :=
  gaussianZigZagHorizonKernel_invariant_of_forwardCertificate
    forward.toSetwiseCertificate horizon

/-- Compactly supported continuous expectation equations also imply exact
Gaussian Zig-Zag stationarity, by regular-measure determination. -/
theorem gaussianZigZagHorizonKernel_invariant_of_compactForwardEquation
    (forward : GaussianZigZagCompactForwardEquation)
    (horizon : NNReal) :
    (gaussianZigZagHorizonKernel horizon).Invariant gaussianZigZagTarget :=
  forward.invariant gaussianZigZagHorizonKernel gaussianZigZagTarget horizon

/-- Once weak-forward uniqueness is proved for the constructed stopped path,
the checked smooth-core generator balance yields exact stationarity. -/
theorem gaussianZigZagHorizonKernel_invariant_of_weakForwardUniqueness
    (uniqueness : GaussianZigZagWeakForwardUniqueness)
    (horizon : NNReal) :
    (gaussianZigZagHorizonKernel horizon).Invariant gaussianZigZagTarget := by
  apply invariant_of_compactTest_generatorBalance_and_weakUniqueness
    gaussianZigZagHorizonKernel GaussianZigZagSmoothTest.observe
    GaussianZigZagSmoothTest.generator gaussianZigZagTarget uniqueness
  · intro test
    exact test.generator_integrable
  · intro test
    exact test.generator_mean_zero

/-- Target-started weak-forward uniqueness already suffices; no theorem about
arbitrary initial measures is needed for stationarity. -/
theorem gaussianZigZagHorizonKernel_invariant_of_targetWeakForwardUniqueness
    (uniqueness : GaussianZigZagTargetWeakForwardUniqueness)
    (horizon : NNReal) :
    (gaussianZigZagHorizonKernel horizon).Invariant gaussianZigZagTarget := by
  apply invariant_of_compactTest_generatorBalance_and_targetWeakUniqueness
    gaussianZigZagHorizonKernel GaussianZigZagSmoothTest.observe
    GaussianZigZagSmoothTest.generator gaussianZigZagTarget uniqueness
  · intro test
    exact test.generator_integrable
  · intro test
    exact test.generator_mean_zero

/-- The split weak-forward obligations—scalar expectation uniqueness and
measure determination—suffice for exact Gaussian Zig-Zag stationarity. -/
theorem gaussianZigZagHorizonKernel_invariant_of_weakExpectationUniqueness
    (scalar : GaussianZigZagWeakExpectationUniqueness)
    (determining : GaussianZigZagSmoothTestDetermining)
    (horizon : NNReal) :
    (gaussianZigZagHorizonKernel horizon).Invariant gaussianZigZagTarget :=
  gaussianZigZagHorizonKernel_invariant_of_weakForwardUniqueness
    (scalar.toWeakForwardUniqueness gaussianZigZagHorizonKernel
      GaussianZigZagSmoothTest.observe GaussianZigZagSmoothTest.generator
      determining)
    horizon

/-- The minimal split premises—target-started scalar uniqueness and measure
determination—yield exact Gaussian Zig-Zag stationarity. -/
theorem gaussianZigZagHorizonKernel_invariant_of_targetWeakExpectationUniqueness
    (scalar : GaussianZigZagTargetWeakExpectationUniqueness)
    (determining : GaussianZigZagSmoothTestDetermining)
    (horizon : NNReal) :
    (gaussianZigZagHorizonKernel horizon).Invariant gaussianZigZagTarget :=
  gaussianZigZagHorizonKernel_invariant_of_targetWeakForwardUniqueness
    (scalar.toTargetWeakForwardUniqueness gaussianZigZagHorizonKernel
      GaussianZigZagSmoothTest.observe GaussianZigZagSmoothTest.generator
      gaussianZigZagTarget determining)
    horizon

/-- Regular-measure version of the minimal split stationarity theorem. It
requires smooth-test scalar uniqueness, determination only among regular
measures, and derives regularity of candidate and transported probability laws
from the Gaussian state-space topology. -/
theorem gaussianZigZagHorizonKernel_invariant_of_targetWeakExpectationUniqueness_regular
    (scalar : GaussianZigZagTargetWeakExpectationUniqueness)
    (determining : GaussianZigZagSmoothTestRegularDetermining)
    (horizon : NNReal) :
    (gaussianZigZagHorizonKernel horizon).Invariant gaussianZigZagTarget := by
  have hcurve : ∀ (curve : NNReal → Measure ZigZagState),
      CompactTestWeakForwardSolution GaussianZigZagSmoothTest.observe
        GaussianZigZagSmoothTest.generator gaussianZigZagTarget curve →
      ∀ time, (curve time).Regular := by
    intro curve solution time
    letI := solution.probability time
    infer_instance
  have htransport : ∀ time,
      ((gaussianZigZagHorizonKernel time) ∘ₘ gaussianZigZagTarget).Regular := by
    intro time
    infer_instance
  exact gaussianZigZagHorizonKernel_invariant_of_targetWeakForwardUniqueness
    (scalar.toTargetWeakForwardUniqueness_of_regular
      gaussianZigZagHorizonKernel GaussianZigZagSmoothTest.observe
      GaussianZigZagSmoothTest.generator gaussianZigZagTarget determining
      hcurve htransport)
    horizon

/-- The measure-determination half is now discharged internally. Exact
Gaussian Zig-Zag stationarity therefore requires only target-started scalar
weak-expectation uniqueness for the constructed stopped path. -/
theorem gaussianZigZagHorizonKernel_invariant_of_targetWeakExpectationUniqueness_finiteRegular
    (scalar : GaussianZigZagTargetWeakExpectationUniqueness)
    (horizon : NNReal) :
    (gaussianZigZagHorizonKernel horizon).Invariant gaussianZigZagTarget := by
  have hcurve : ∀ (curve : NNReal → Measure ZigZagState),
      CompactTestWeakForwardSolution GaussianZigZagSmoothTest.observe
        GaussianZigZagSmoothTest.generator gaussianZigZagTarget curve →
      ∀ time, (curve time).Regular := by
    intro curve solution time
    letI := solution.probability time
    infer_instance
  have htransport : ∀ time,
      ((gaussianZigZagHorizonKernel time) ∘ₘ gaussianZigZagTarget).Regular := by
    intro time
    infer_instance
  exact gaussianZigZagHorizonKernel_invariant_of_targetWeakForwardUniqueness
    (scalar.toTargetWeakForwardUniqueness_of_finiteRegular
      gaussianZigZagHorizonKernel GaussianZigZagSmoothTest.observe
      GaussianZigZagSmoothTest.generator gaussianZigZagTarget
      gaussianZigZagSmoothTest_finiteRegularDetermining hcurve htransport)
    horizon

/-- Under the event kernel's actual exponential-hazard law, inverse-clock
execution satisfies the integrated-hazard equation almost surely. -/
theorem gaussianZigZagIntegratedRate_waitingNNReal_ae
    (state : ZigZagState) :
    ∀ᵐ hazard ∂gaussianZigZagHazardMeasure,
      gaussianZigZagIntegratedRate state.1 state.2
        (gaussianZigZagWaitingNNReal state hazard : ℝ) = (hazard : ℝ) := by
  filter_upwards [gaussianZigZagHazardMeasure_positive_ae] with hazard hhazard
  exact gaussianZigZagIntegratedRate_waitingNNReal state hhazard

/-- Exact standard-Gaussian Zig-Zag state after a fixed number of genuine
events. Fixed-event iteration is well defined even though proving finite-time
nonexplosion requires an additional pathwise argument. -/
noncomputable def gaussianZigZagEventIterate (eventCount : ℕ) :
    Kernel ZigZagState ZigZagState :=
  gaussianZigZagEventKernel ^ eventCount

instance gaussianZigZagEventIterate.instIsMarkovKernel (eventCount : ℕ) :
    IsMarkovKernel (gaussianZigZagEventIterate eventCount) := by
  unfold gaussianZigZagEventIterate
  infer_instance

theorem gaussianZigZagEventIterate_add (m n : ℕ) :
    gaussianZigZagEventIterate (m + n) =
      gaussianZigZagEventIterate m ∘ₖ gaussianZigZagEventIterate n := by
  exact Kernel.pow_add gaussianZigZagEventKernel m n

end Mcmc.PDMP
