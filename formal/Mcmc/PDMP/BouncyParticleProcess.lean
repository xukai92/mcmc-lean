import Mcmc.PDMP.BouncyParticle
import Mcmc.PDMP.EventSimulation
import Mathlib.Tactic

/-!
# Bouncy Particle process semantics

This module instantiates the generic deterministic PDMP flow for Euclidean
position--velocity states and packages a measurable, position-dependent
bounce normal into an event kernel.  The measurability certificate is explicit
because differentiability of a potential and treatment of zero gradients
belong to concrete target models.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory

namespace Mcmc.PDMP

open Mcmc.Hamiltonian

variable {ι : Type*} [Fintype ι]

/-- Position and velocity state of a finite-dimensional Bouncy Particle
process. -/
abbrev BouncyParticleState (ι : Type*) := Position ι × Position ι

/-- Linear motion between Bouncy Particle events. -/
def bouncyParticleFlow (t : NNReal) (state : BouncyParticleState ι) :
    BouncyParticleState ι :=
  (fun i => state.1 i + (t : ℝ) * state.2 i, state.2)

/-- Linear position--velocity motion is a measurable semiflow. -/
noncomputable def bouncyParticleSemiflow :
    MeasurableSemiflow (BouncyParticleState ι) where
  flow := bouncyParticleFlow
  measurable_flow t := by
    unfold bouncyParticleFlow
    fun_prop
  flow_zero := by
    funext state
    apply Prod.ext
    · funext i
      simp [bouncyParticleFlow]
    · rfl
  flow_add := by
    intro t u
    funext state
    apply Prod.ext
    · funext i
      simp only [bouncyParticleFlow, Function.comp_apply, NNReal.coe_add]
      ring
    · rfl

/-- Jointly measurable linear motion for random inter-event waits. -/
noncomputable def bouncyParticleJointlyMeasurableSemiflow :
    JointlyMeasurableSemiflow (BouncyParticleState ι) where
  toMeasurableSemiflow := bouncyParticleSemiflow
  jointly_measurable_flow := by
    change Measurable (fun p : NNReal × BouncyParticleState ι =>
      bouncyParticleFlow p.1 p.2)
    unfold bouncyParticleFlow
    fun_prop

/-- Target-specific data needed to turn the algebraic bounce reflection into
a general-state deterministic event kernel. -/
structure BouncyParticleBounceData (ι : Type*) [Fintype ι] where
  normal : Position ι → Position ι
  measurable_bounce : Measurable (fun state : BouncyParticleState ι =>
    (state.1, bouncyReflection (normal state.1) state.2))

/-- Position-dependent deterministic bounce kernel. -/
noncomputable def BouncyParticleBounceData.jumpKernel
    (data : BouncyParticleBounceData ι) :
    Kernel (BouncyParticleState ι) (BouncyParticleState ι) :=
  Kernel.deterministic
    (fun state => (state.1, bouncyReflection (data.normal state.1) state.2))
    data.measurable_bounce

instance BouncyParticleBounceData.jumpKernel.instIsMarkovKernel
    (data : BouncyParticleBounceData ι) :
    IsMarkovKernel data.jumpKernel := by
  unfold BouncyParticleBounceData.jumpKernel
  infer_instance

/-- Execute a fixed list of Bouncy Particle inter-event waits and bounces. -/
noncomputable def BouncyParticleBounceData.executeSchedule
    (data : BouncyParticleBounceData ι) (waits : List NNReal) :
    Kernel (BouncyParticleState ι) (BouncyParticleState ι) :=
  bouncyParticleSemiflow.executeSchedule data.jumpKernel waits

instance BouncyParticleBounceData.executeSchedule.instIsMarkovKernel
    (data : BouncyParticleBounceData ι) (waits : List NNReal) :
    IsMarkovKernel (data.executeSchedule waits) := by
  unfold BouncyParticleBounceData.executeSchedule
  infer_instance

/-- Canonical position-dependent bounce intensity. -/
noncomputable def BouncyParticleBounceData.stateRate
    (data : BouncyParticleBounceData ι) (state : BouncyParticleState ι) : ℝ :=
  bouncyRate (data.normal state.1) state.2

theorem BouncyParticleBounceData.stateRate_nonneg
    (data : BouncyParticleBounceData ι) (state : BouncyParticleState ι) :
    0 ≤ data.stateRate state :=
  bouncyRate_nonneg (data.normal state.1) state.2

/-- Bouncy Particle jump mechanism, given the target-specific measurability of
its canonical rate. -/
noncomputable def BouncyParticleBounceData.jumpMechanism
    (data : BouncyParticleBounceData ι)
    (hmeasurableRate : Measurable (fun state : BouncyParticleState ι =>
      ENNReal.ofReal (data.stateRate state))) :
    JumpMechanism (BouncyParticleState ι) where
  rate := fun state => ENNReal.ofReal (data.stateRate state)
  measurable_rate := hmeasurableRate
  jump := data.jumpKernel
  isMarkov := by infer_instance

/-- Exact homogeneous-clock thinning simulator for a globally bounded Bouncy
Particle event intensity. -/
noncomputable def BouncyParticleBounceData.thinnedSimulator
    (data : BouncyParticleBounceData ι)
    (hmeasurableRate : Measurable (fun state : BouncyParticleState ι =>
      ENNReal.ofReal (data.stateRate state)))
    (clock : HomogeneousClock)
    (hbound : ∀ state, ENNReal.ofReal (data.stateRate state) ≤ clock.rate) :
    ThinnedFlowSimulator (BouncyParticleState ι) where
  semiflow := bouncyParticleJointlyMeasurableSemiflow
  mechanism := data.jumpMechanism hmeasurableRate
  clock := clock
  rate_le_clock := hbound

end Mcmc.PDMP
