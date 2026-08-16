import Mcmc.PDMP.ScheduledExecutionKernel
import Mathlib.MeasureTheory.Group.Prod

/-!
# A stationary bounded-rate telegraph PDMP

This is a concrete nontrivial flow-driven PDMP client. The state is a Boolean
velocity and a real position. Between homogeneous Poisson events the position
moves linearly; every event flips velocity. The product of equal mass on both
velocities and Lebesgue position measure is preserved by every flow segment,
the flip, and consequently every supplied finite-candidate horizon execution.

The target is sigma-finite rather than a probability measure, so this module
proves stationarity, not convergence. It complements the adjacent-count flux
interface needed for non-volume-preserving Zig-Zag/BPS targets.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace Mcmc.PDMP

abbrev TelegraphState := Bool × ℝ

def telegraphVelocity (velocity : Bool) : ℝ := if velocity then 1 else -1

theorem measurable_telegraphVelocity : Measurable telegraphVelocity := by
  unfold telegraphVelocity
  exact Measurable.ite (MeasurableSet.singleton true)
    measurable_const measurable_const

def telegraphFlow (time : NNReal) (state : TelegraphState) : TelegraphState :=
  (state.1, state.2 + (time : ℝ) * telegraphVelocity state.1)

noncomputable def telegraphSemiflow : MeasurableSemiflow TelegraphState where
  flow := telegraphFlow
  measurable_flow time := by
    unfold telegraphFlow telegraphVelocity
    exact measurable_fst.prodMk
      (measurable_snd.add (measurable_const.mul
        (measurable_telegraphVelocity.comp measurable_fst)))
  flow_zero := by
    funext state
    simp [telegraphFlow]
  flow_add := by
    intro time duration
    funext state
    apply Prod.ext
    · rfl
    · simp only [telegraphFlow, Function.comp_apply, NNReal.coe_add]
      ring

noncomputable def telegraphJointlyMeasurableSemiflow :
    JointlyMeasurableSemiflow TelegraphState where
  toMeasurableSemiflow := telegraphSemiflow
  jointly_measurable_flow := by
    change Measurable (fun p : NNReal × TelegraphState =>
      telegraphFlow p.1 p.2)
    unfold telegraphFlow
    have htime : Measurable (fun p : NNReal × TelegraphState => (p.1 : ℝ)) := by
      fun_prop
    exact (measurable_fst.comp measurable_snd).prodMk
      ((measurable_snd.comp measurable_snd).add
        (htime.mul
          (measurable_telegraphVelocity.comp
            (measurable_fst.comp measurable_snd))))

def telegraphFlip (state : TelegraphState) : TelegraphState :=
  (!state.1, state.2)

noncomputable def telegraphJumpKernel : Kernel TelegraphState TelegraphState :=
  Kernel.deterministic telegraphFlip (by
    unfold telegraphFlip
    fun_prop)

instance telegraphJumpKernel.instIsMarkovKernel :
    IsMarkovKernel telegraphJumpKernel := by
  unfold telegraphJumpKernel
  infer_instance

/-- Equal (unnormalized) mass on the two velocities. -/
noncomputable def telegraphVelocityMeasure : Measure Bool :=
  Measure.dirac false + Measure.dirac true

/-- Sigma-finite invariant reference for the telegraph process. -/
noncomputable def telegraphTarget : Measure TelegraphState :=
  telegraphVelocityMeasure.prod volume

instance telegraphTarget.instSFinite : SFinite telegraphTarget := by
  unfold telegraphTarget telegraphVelocityMeasure
  infer_instance

theorem telegraphVelocityFlip_measurePreserving :
    MeasurePreserving (fun velocity : Bool => !velocity)
      telegraphVelocityMeasure telegraphVelocityMeasure := by
  constructor
  · fun_prop
  · unfold telegraphVelocityMeasure
    have hflip : Measurable (fun velocity : Bool => !velocity) := by fun_prop
    rw [Measure.map_add _ _ hflip, Measure.map_dirac false,
      Measure.map_dirac true]
    simp [add_comm]

theorem telegraphFlow_measurePreserving (time : NNReal) :
    MeasurePreserving (telegraphFlow time) telegraphTarget telegraphTarget := by
  unfold telegraphTarget telegraphFlow
  have h := (MeasurePreserving.id telegraphVelocityMeasure).skew_product
    (g := fun velocity position =>
      position + (time : ℝ) * telegraphVelocity velocity)
    (measurable_snd.add (measurable_const.mul
      (measurable_telegraphVelocity.comp measurable_fst)))
    (Filter.Eventually.of_forall fun velocity => by
      simpa only [add_comm] using map_add_left_eq_self volume
        ((time : ℝ) * telegraphVelocity velocity))
  simpa only [id_eq] using h

theorem telegraphSemiflow_invariant (time : NNReal) :
    (telegraphSemiflow.kernel time).Invariant telegraphTarget :=
  telegraphSemiflow.kernel_invariant telegraphTarget
    telegraphFlow_measurePreserving time

theorem telegraphFlip_measurePreserving :
    MeasurePreserving telegraphFlip telegraphTarget telegraphTarget := by
  unfold telegraphFlip telegraphTarget
  have h := telegraphVelocityFlip_measurePreserving.skew_product
    (μc := (volume : Measure ℝ)) (μd := (volume : Measure ℝ))
    (g := fun (_ : Bool) (position : ℝ) => position) measurable_snd
    (Filter.Eventually.of_forall fun _ => Measure.map_id)
  exact h

theorem telegraphJumpKernel_invariant :
    telegraphJumpKernel.Invariant telegraphTarget :=
  Mcmc.Kernel.deterministic_invariant_of_measurePreserving telegraphTarget
    (by unfold telegraphFlip; fun_prop) telegraphFlip_measurePreserving

noncomputable def telegraphJumpMechanism (rate : NNReal) :
    JumpMechanism TelegraphState where
  rate := fun _ => rate
  measurable_rate := measurable_const
  jump := telegraphJumpKernel
  isMarkov := by infer_instance

noncomputable def telegraphSimulator (rate : NNReal) (hrate : 0 < rate) :
    ThinnedFlowSimulator TelegraphState where
  semiflow := telegraphJointlyMeasurableSemiflow
  mechanism := telegraphJumpMechanism rate
  clock := ⟨rate, hrate⟩
  rate_le_clock := fun _ => le_rfl

theorem telegraph_clockAcceptance_eq_one
    (rate : NNReal) (hrate : 0 < rate) (state : TelegraphState) :
    (telegraphJumpMechanism rate).clockAcceptance rate state = 1 := by
  unfold JumpMechanism.clockAcceptance telegraphJumpMechanism
  change (rate : ENNReal) / (rate : ENNReal) = 1
  exact ENNReal.div_self (by exact_mod_cast hrate.ne') (by simp)

theorem telegraph_uniformizedKernel_eq_jump
    (rate : NNReal) (hrate : 0 < rate) :
    (telegraphJumpMechanism rate).uniformizedKernel rate =
      telegraphJumpKernel := by
  ext state event hevent
  rw [JumpMechanism.uniformizedKernel_apply _ _ _ hevent,
    telegraph_clockAcceptance_eq_one rate hrate]
  simp [telegraphJumpMechanism]

/-- Every supplied finite candidate schedule, stopped at an arbitrary finite
horizon, preserves the telegraph target. -/
theorem telegraph_executeUntil_invariant
    (rate : NNReal) (hrate : 0 < rate)
    (horizon : NNReal) (waits : List NNReal) :
    ((telegraphSimulator rate hrate).executeUntil horizon waits).Invariant
      telegraphTarget := by
  apply (telegraphSimulator rate hrate).executeUntil_invariant telegraphTarget
  · exact telegraphSemiflow_invariant
  · change ((telegraphJumpMechanism rate).uniformizedKernel rate).Invariant
      telegraphTarget
    rw [telegraph_uniformizedKernel_eq_jump rate hrate]
    exact telegraphJumpKernel_invariant

end Mcmc.PDMP
