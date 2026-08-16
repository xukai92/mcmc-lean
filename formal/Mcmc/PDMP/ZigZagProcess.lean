import Mcmc.PDMP.EventSimulation
import Mcmc.PDMP.SemigroupStationarity
import Mcmc.PDMP.ZigZag
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
  difference : ℝ → ℝ
  difference_eq : difference =
    fun q => observable q true - observable q false
  contDiff_difference : ContDiff ℝ 1 difference
  compact_difference : HasCompactSupport difference
  derivative_eq : ∀ q,
    derivative q true - derivative q false = deriv difference q
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
      test.contDiff_difference test.compact_difference test.derivative_eq
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
