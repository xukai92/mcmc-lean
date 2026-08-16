import Mcmc.PDMP.BouncyParticle
import Mcmc.PDMP.EventSimulation
import Mcmc.PDMP.InverseHazard
import Mcmc.PDMP.ScheduledExecutionKernel
import Mcmc.Hamiltonian.MomentumRefresh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
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

/-! ### Velocity refreshment -/

/-- Independently redraw the Bouncy Particle velocity while retaining its
current position.  This is the refresh transition used by practical BPS
implementations and by many ergodicity arguments. -/
noncomputable def bouncyParticleVelocityRefresh
    (velocityLaw : Measure (Position ι)) :
    Kernel (BouncyParticleState ι) (BouncyParticleState ι) :=
  Mcmc.Hamiltonian.momentumRefreshWith velocityLaw

instance bouncyParticleVelocityRefresh.instIsMarkovKernel
    (velocityLaw : Measure (Position ι)) [IsProbabilityMeasure velocityLaw] :
    IsMarkovKernel (bouncyParticleVelocityRefresh velocityLaw) := by
  unfold bouncyParticleVelocityRefresh
  infer_instance

/-- Full velocity refresh preserves the product of any s-finite position
target with the refresh law. -/
theorem bouncyParticleVelocityRefresh_invariant
    (positionTarget velocityTarget : Measure (Position ι))
    [SFinite positionTarget] [IsProbabilityMeasure velocityTarget] :
    (bouncyParticleVelocityRefresh velocityTarget).Invariant
      (positionTarget.prod velocityTarget) := by
  exact Mcmc.Hamiltonian.momentumRefreshWith_invariant
    positionTarget velocityTarget

/-- Refreshment leaves every measurable position event unchanged. -/
theorem bouncyParticleVelocityRefresh_position_event
    (velocityLaw : Measure (Position ι)) [IsProbabilityMeasure velocityLaw]
    (state : BouncyParticleState ι) (s : Set (Position ι))
    (hs : MeasurableSet s) :
    bouncyParticleVelocityRefresh velocityLaw state (s ×ˢ Set.univ) =
      s.indicator 1 state.1 := by
  unfold bouncyParticleVelocityRefresh
  unfold Mcmc.Hamiltonian.momentumRefreshWith
  unfold Mcmc.Hamiltonian.momentumTransition
  rw [Kernel.parallelComp_apply_prod]
  simp only [Kernel.const_apply, measure_univ, mul_one]
  rw [Kernel.id_apply, Measure.dirac_apply' _ hs]

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

/-- Exact fixed-positive-horizon BPS transition for a globally bounded bounce
rate. Candidate counts are Poisson and candidate times are continuous ordered
uniform times; thinning selects genuine bounces. -/
noncomputable def BouncyParticleBounceData.horizonKernel
    (data : BouncyParticleBounceData ι)
    (hmeasurableRate : Measurable (fun state : BouncyParticleState ι =>
      ENNReal.ofReal (data.stateRate state)))
    (clock : HomogeneousClock)
    (hbound : ∀ state, ENNReal.ofReal (data.stateRate state) ≤ clock.rate)
    (horizon : PositiveHorizon) :
    Kernel (BouncyParticleState ι) (BouncyParticleState ι) :=
  (data.thinnedSimulator hmeasurableRate clock hbound).horizonKernel horizon

instance BouncyParticleBounceData.horizonKernel.instIsMarkovKernel
    (data : BouncyParticleBounceData ι)
    (hmeasurableRate : Measurable (fun state : BouncyParticleState ι =>
      ENNReal.ofReal (data.stateRate state)))
    (clock : HomogeneousClock)
    (hbound : ∀ state, ENNReal.ofReal (data.stateRate state) ≤ clock.rate)
    (horizon : PositiveHorizon) :
    IsMarkovKernel
      (data.horizonKernel hmeasurableRate clock hbound horizon) := by
  unfold BouncyParticleBounceData.horizonKernel
  infer_instance

/-- A practical bounded-rate BPS step: independently refresh velocity, then
run the exact thinned bounce process for a positive horizon. -/
noncomputable def BouncyParticleBounceData.refreshedHorizonKernel
    (data : BouncyParticleBounceData ι)
    (velocityLaw : Measure (Position ι))
    (hmeasurableRate : Measurable (fun state : BouncyParticleState ι =>
      ENNReal.ofReal (data.stateRate state)))
    (clock : HomogeneousClock)
    (hbound : ∀ state, ENNReal.ofReal (data.stateRate state) ≤ clock.rate)
    (horizon : PositiveHorizon) :
    Kernel (BouncyParticleState ι) (BouncyParticleState ι) :=
  data.horizonKernel hmeasurableRate clock hbound horizon ∘ₖ
    bouncyParticleVelocityRefresh velocityLaw

instance BouncyParticleBounceData.refreshedHorizonKernel.instIsMarkovKernel
    (data : BouncyParticleBounceData ι)
    (velocityLaw : Measure (Position ι)) [IsProbabilityMeasure velocityLaw]
    (hmeasurableRate : Measurable (fun state : BouncyParticleState ι =>
      ENNReal.ofReal (data.stateRate state)))
    (clock : HomogeneousClock)
    (hbound : ∀ state, ENNReal.ofReal (data.stateRate state) ≤ clock.rate)
    (horizon : PositiveHorizon) :
    IsMarkovKernel (data.refreshedHorizonKernel velocityLaw hmeasurableRate
      clock hbound horizon) := by
  unfold BouncyParticleBounceData.refreshedHorizonKernel
  infer_instance

/-- Refresh-then-bounce preserves a compatible product target whenever the
exact horizon bounce transition preserves it. This theorem keeps the spatial-
flux obligation explicit rather than deriving it from reflection algebra. -/
theorem BouncyParticleBounceData.refreshedHorizonKernel_invariant
    (data : BouncyParticleBounceData ι)
    (positionTarget velocityTarget : Measure (Position ι))
    [SFinite positionTarget] [IsProbabilityMeasure velocityTarget]
    (hmeasurableRate : Measurable (fun state : BouncyParticleState ι =>
      ENNReal.ofReal (data.stateRate state)))
    (clock : HomogeneousClock)
    (hbound : ∀ state, ENNReal.ofReal (data.stateRate state) ≤ clock.rate)
    (horizon : PositiveHorizon)
    (hbounce : (data.horizonKernel hmeasurableRate clock hbound horizon).Invariant
      (positionTarget.prod velocityTarget)) :
    (data.refreshedHorizonKernel velocityTarget hmeasurableRate clock hbound
      horizon).Invariant (positionTarget.prod velocityTarget) := by
  exact hbounce.comp
    (bouncyParticleVelocityRefresh_invariant positionTarget velocityTarget)

/-! ### Exact unbounded-rate inverse clocks -/

/-- Target-specific exact inverse of the integrated BPS rate. This is the
proof boundary needed when no finite homogeneous thinning bound exists. The
integral is tied directly to the canonical BPS rate along linear motion, so an
arbitrary waiting-time oracle cannot masquerade as the BPS clock. -/
structure BouncyParticleInverseHazardData (ι : Type*) [Fintype ι] where
  bounce : BouncyParticleBounceData ι
  waitingTime : BouncyParticleState ι → NNReal → NNReal
  measurable_waitingTime : Measurable
    (fun input : BouncyParticleState ι × NNReal =>
      waitingTime input.1 input.2)
  waitingTime_pos : ∀ state {hazard}, 0 < hazard →
    0 < waitingTime state hazard
  inverse : ∀ state {hazard}, 0 < hazard →
    (∫ time in (0 : ℝ)..(waitingTime state hazard : ℝ),
      bounce.stateRate (bouncyParticleFlow (Real.toNNReal time) state)) =
        (hazard : ℝ)

/-- The general inverse-hazard interface instantiated by exact BPS clock
data. -/
noncomputable def BouncyParticleInverseHazardData.clock
    (data : BouncyParticleInverseHazardData ι) :
    InverseHazardClock (BouncyParticleState ι) where
  semiflow := bouncyParticleJointlyMeasurableSemiflow
  accumulated state time :=
    ∫ elapsed in (0 : ℝ)..(time : ℝ),
      data.bounce.stateRate
        (bouncyParticleFlow (Real.toNNReal elapsed) state)
  waitingTime := data.waitingTime
  measurable_waitingTime := data.measurable_waitingTime
  waitingTime_pos := data.waitingTime_pos
  inverse := data.inverse

/-- One exact event of a possibly unbounded-rate finite-dimensional BPS. -/
noncomputable def BouncyParticleInverseHazardData.eventKernel
    (data : BouncyParticleInverseHazardData ι) :
    Kernel (BouncyParticleState ι) (BouncyParticleState ι) :=
  data.clock.eventKernel data.bounce.jumpKernel

instance BouncyParticleInverseHazardData.eventKernel.instIsMarkovKernel
    (data : BouncyParticleInverseHazardData ι) :
    IsMarkovKernel data.eventKernel := by
  unfold BouncyParticleInverseHazardData.eventKernel
  infer_instance

/-- Exact finite event skeleton for an unbounded-rate BPS. A stopped
finite-horizon process additionally requires nonexplosion and residual-time
execution; neither is inferred from existence of the inverse clock. -/
noncomputable def BouncyParticleInverseHazardData.eventIterate
    (data : BouncyParticleInverseHazardData ι) (events : ℕ) :
    Kernel (BouncyParticleState ι) (BouncyParticleState ι) :=
  data.clock.eventIterate data.bounce.jumpKernel events

instance BouncyParticleInverseHazardData.eventIterate.instIsMarkovKernel
    (data : BouncyParticleInverseHazardData ι) (events : ℕ) :
    IsMarkovKernel (data.eventIterate events) := by
  unfold BouncyParticleInverseHazardData.eventIterate
  infer_instance

theorem BouncyParticleInverseHazardData.eventIterate_add
    (data : BouncyParticleInverseHazardData ι) (first second : ℕ) :
    data.eventIterate (first + second) =
      data.eventIterate first ∘ₖ data.eventIterate second :=
  data.clock.eventIterate_add data.bounce.jumpKernel first second

end Mcmc.PDMP
