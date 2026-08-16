import Mcmc.PDMP.EventSimulation
import Mcmc.PDMP.ZigZag
import Mathlib.Tactic

/-!
# One-dimensional Zig-Zag process semantics

This module instantiates the generic PDMP flow and jump interfaces for the
one-dimensional Zig-Zag state `(position, velocity)`.  It supplies the exact
linear semiflow, deterministic velocity flip, and fixed-event execution
kernel.  Sampling the state-dependent event times remains a separate layer.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory

namespace Mcmc.PDMP

/-- Position and two-valued velocity for the one-dimensional Zig-Zag process. -/
abbrev ZigZagState := ℝ × Bool

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

/-- One exact standard-Gaussian Zig-Zag event: draw unit exponential hazard,
invert the integrated rate, flow to that time, and flip velocity. -/
noncomputable def gaussianZigZagEventKernel :
    Kernel ZigZagState ZigZagState :=
  Kernel.map
    (Kernel.prod Kernel.id
      (Kernel.const ZigZagState gaussianZigZagHazardMeasure))
    (fun input => zigZagFlip (zigZagFlow
      (gaussianZigZagWaitingNNReal input.1 input.2) input.1))

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
  unfold zigZagFlip zigZagFlow
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
