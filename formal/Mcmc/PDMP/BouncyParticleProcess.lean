import Mcmc.PDMP.BouncyParticle
import Mcmc.PDMP.EventSimulation
import Mcmc.PDMP.InverseHazard
import Mcmc.PDMP.ScheduledExecutionKernel
import Mcmc.PDMP.SemigroupStationarity
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

/-! ### Standard-Gaussian finite-dimensional clock algebra -/

/-- Elementary affine interval integral, recorded locally for the Gaussian
clock calculation. -/
theorem intervalIntegral_affine (a b left right : ℝ) :
    (∫ time in left..right, (a + b * time)) =
      a * (right - left) + b * (right ^ 2 - left ^ 2) / 2 := by
  let primitive : ℝ → ℝ := fun time => a * time + b * time ^ 2 / 2
  have hderiv : ∀ time : ℝ,
      HasDerivAt primitive (a + b * time) time := by
    intro time
    dsimp [primitive]
    have hraw := ((hasDerivAt_id time).const_mul a).add
      ((((hasDerivAt_id time).pow 2).const_mul b).div_const 2)
    have hderiv' := hraw.congr_deriv (show
      a * 1 + b * (2 * time ^ (2 - 1) * 1) / 2 = a + b * time by
        norm_num
        ring)
    apply hderiv'.congr_of_eventuallyEq
    filter_upwards [] with y
    rfl
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun time _ => hderiv time)]
  · dsimp [primitive]
    ring
  · exact (continuous_const.add
      (continuous_const.mul continuous_id)).intervalIntegrable left right

/-- On an interval where an affine function is nonnegative, taking its
positive part does not change its integral. -/
theorem intervalIntegral_max_zero_affine_of_nonneg
    (a b left right : ℝ)
    (hnonneg : ∀ time ∈ Set.uIcc left right, 0 ≤ a + b * time) :
    (∫ time in left..right, max 0 (a + b * time)) =
      a * (right - left) + b * (right ^ 2 - left ^ 2) / 2 := by
  rw [intervalIntegral.integral_congr (fun time htime =>
    max_eq_right (hnonneg time htime)), intervalIntegral_affine]

/-- On an interval where an affine function is nonpositive, its positive-part
integral vanishes. -/
theorem intervalIntegral_max_zero_affine_of_nonpos
    (a b left right : ℝ)
    (hnonpos : ∀ time ∈ Set.uIcc left right, a + b * time ≤ 0) :
    (∫ time in left..right, max 0 (a + b * time)) = 0 := by
  rw [intervalIntegral.integral_congr (fun time htime =>
    max_eq_left (hnonpos time htime)), intervalIntegral.integral_zero]

/-- Closed form for accumulated positive affine hazard on a nonnegative time
horizon. -/
theorem intervalIntegral_max_zero_affine
    (a b horizon : ℝ) (hb : 0 < b) (hhorizon : 0 ≤ horizon) :
    (∫ time in (0 : ℝ)..horizon, max 0 (a + b * time)) =
      ((max 0 (a + b * horizon)) ^ 2 - (max 0 a) ^ 2) / (2 * b) := by
  by_cases ha : 0 ≤ a
  · rw [intervalIntegral_max_zero_affine_of_nonneg]
    · rw [max_eq_right ha]
      have hend : 0 ≤ a + b * horizon := by positivity
      rw [max_eq_right hend]
      field_simp
      ring
    · intro time htime
      have ht : 0 ≤ time := by
        rw [Set.uIcc_of_le hhorizon] at htime
        exact htime.1
      positivity
  · have ha' : a < 0 := lt_of_not_ge ha
    by_cases hend : a + b * horizon ≤ 0
    · rw [intervalIntegral_max_zero_affine_of_nonpos]
      · rw [max_eq_left hend, max_eq_left ha'.le]
        simp
      · intro time htime
        have ht : time ≤ horizon := by
          rw [Set.uIcc_of_le hhorizon] at htime
          exact htime.2
        nlinarith
    · have hend' : 0 < a + b * horizon := lt_of_not_ge hend
      let crossing : ℝ := -a / b
      have hcrossing0 : 0 ≤ crossing := by
        dsimp [crossing]
        exact div_nonneg (neg_nonneg.mpr ha'.le) hb.le
      have hcrossingH : crossing ≤ horizon := by
        dsimp [crossing]
        rw [div_le_iff₀ hb]
        nlinarith
      have hint : IntervalIntegrable (fun time : ℝ => max 0 (a + b * time))
          volume (0 : ℝ) crossing :=
        (continuous_const.max
          (continuous_const.add (continuous_const.mul continuous_id))).intervalIntegrable
            0 crossing
      have hint' : IntervalIntegrable (fun time : ℝ => max 0 (a + b * time))
          volume crossing horizon :=
        (continuous_const.max
          (continuous_const.add (continuous_const.mul continuous_id))).intervalIntegrable
            crossing horizon
      rw [← intervalIntegral.integral_add_adjacent_intervals hint hint']
      rw [intervalIntegral_max_zero_affine_of_nonpos,
        intervalIntegral_max_zero_affine_of_nonneg]
      · rw [max_eq_left ha'.le, max_eq_right hend'.le]
        dsimp [crossing]
        field_simp
        ring
      · intro time htime
        have ht : crossing ≤ time := by
          rw [Set.uIcc_of_le hcrossingH] at htime
          exact htime.1
        dsimp [crossing] at ht
        rw [div_le_iff₀ hb] at ht
        nlinarith
      · intro time htime
        have ht : time ≤ crossing := by
          rw [Set.uIcc_of_le hcrossing0] at htime
          exact htime.2
        dsimp [crossing] at ht
        rw [le_div_iff₀ hb] at ht
        nlinarith

/-- For the standard Gaussian position target, the BPS event normal is the
current position itself. -/
noncomputable def standardGaussianBouncyParticleBounceData :
    BouncyParticleBounceData ι where
  normal := id
  measurable_bounce := by
    unfold bouncyReflection squaredEuclideanNorm euclideanInner
    fun_prop

/-- Initial directional derivative `⟨v,x⟩` along a Gaussian BPS ray. -/
noncomputable def gaussianBPSLinearCoefficient
    (state : BouncyParticleState ι) : ℝ :=
  euclideanInner state.2 state.1

/-- Nonnegative slope `‖v‖²` of the directional derivative along the ray. -/
noncomputable def gaussianBPSQuadraticCoefficient
    (state : BouncyParticleState ι) : ℝ :=
  squaredEuclideanNorm state.2

theorem gaussianBPSQuadraticCoefficient_nonneg
    (state : BouncyParticleState ι) :
    0 ≤ gaussianBPSQuadraticCoefficient state :=
  squaredEuclideanNorm_nonneg state.2

theorem gaussianBPSQuadraticCoefficient_pos
    (state : BouncyParticleState ι) (hvelocity : state.2 ≠ 0) :
    0 < gaussianBPSQuadraticCoefficient state :=
  squaredEuclideanNorm_pos hvelocity

/-- Along linear motion, the Gaussian directional derivative is affine in
time. This is the finite-dimensional reduction behind the exact inverse
integrated-hazard formula. -/
theorem euclideanInner_velocity_gaussianFlow
    (state : BouncyParticleState ι) (time : NNReal) :
    euclideanInner state.2 (bouncyParticleFlow time state).1 =
      gaussianBPSLinearCoefficient state +
        (time : ℝ) * gaussianBPSQuadraticCoefficient state := by
  unfold bouncyParticleFlow gaussianBPSLinearCoefficient
    gaussianBPSQuadraticCoefficient squaredEuclideanNorm
  change euclideanInner state.2 (state.1 + (time : ℝ) • state.2) = _
  rw [euclideanInner_add_right, euclideanInner_smul_right]

/-- Hence the canonical standard-Gaussian BPS rate is a positive part of one
affine scalar function. -/
theorem standardGaussianBPS_stateRate_flow
    (state : BouncyParticleState ι) (time : NNReal) :
    standardGaussianBouncyParticleBounceData.stateRate
        (bouncyParticleFlow time state) =
      max 0 (gaussianBPSLinearCoefficient state +
        (time : ℝ) * gaussianBPSQuadraticCoefficient state) := by
  unfold BouncyParticleBounceData.stateRate
    standardGaussianBouncyParticleBounceData bouncyRate
  change max 0 (euclideanInner state.2 (bouncyParticleFlow time state).1) = _
  rw [euclideanInner_velocity_gaussianFlow]

/-- The affine Gaussian clock coefficients update exactly under linear
flight. -/
theorem gaussianBPSLinearCoefficient_flow
    (state : BouncyParticleState ι) (time : NNReal) :
    gaussianBPSLinearCoefficient (bouncyParticleFlow time state) =
      gaussianBPSLinearCoefficient state +
        (time : ℝ) * gaussianBPSQuadraticCoefficient state := by
  unfold gaussianBPSLinearCoefficient gaussianBPSQuadraticCoefficient
  exact euclideanInner_velocity_gaussianFlow state time

@[simp] theorem gaussianBPSQuadraticCoefficient_flow
    (state : BouncyParticleState ι) (time : NNReal) :
    gaussianBPSQuadraticCoefficient (bouncyParticleFlow time state) =
      gaussianBPSQuadraticCoefficient state := by
  unfold gaussianBPSQuadraticCoefficient
  rfl

/-- Bouncy reflection preserves speed even at a zero normal, where the map is
the identity. -/
theorem squaredEuclideanNorm_bouncyReflection_total
    (normal velocity : Position ι) :
    squaredEuclideanNorm (bouncyReflection normal velocity) =
      squaredEuclideanNorm velocity := by
  by_cases hnormal : normal = 0
  · subst normal
    simp
  · exact squaredEuclideanNorm_bouncyReflection normal velocity hnormal

/-- Bouncy reflection preserves the Euclidean speed. -/
theorem euclideanNorm_bouncyReflection_total
    (normal velocity : Position ι) :
    euclideanNorm (bouncyReflection normal velocity) =
      euclideanNorm velocity := by
  unfold euclideanNorm
  rw [squaredEuclideanNorm_bouncyReflection_total]

/-- Every standard-Gaussian bounce preserves the squared velocity norm. -/
theorem standardGaussianBPS_bounce_speed
    (state : BouncyParticleState ι) :
    squaredEuclideanNorm
        (bouncyReflection state.1 state.2) =
      squaredEuclideanNorm state.2 :=
  squaredEuclideanNorm_bouncyReflection_total state.1 state.2

omit [Fintype ι] in
/-- Linear flight keeps velocity fixed. -/
@[simp] theorem bouncyParticleFlow_velocity
    (time : NNReal) (state : BouncyParticleState ι) :
    (bouncyParticleFlow time state).2 = state.2 := rfl

/-- Position norm grows by at most elapsed time times the fixed speed during
one linear flight. -/
theorem bouncyParticleFlow_position_norm_le
    (time : NNReal) (state : BouncyParticleState ι) :
    euclideanNorm (bouncyParticleFlow time state).1 ≤
      euclideanNorm state.1 + (time : ℝ) * euclideanNorm state.2 := by
  unfold bouncyParticleFlow
  calc
    euclideanNorm (state.1 + (time : ℝ) • state.2) ≤
        euclideanNorm state.1 + euclideanNorm ((time : ℝ) • state.2) :=
      euclideanNorm_add_le _ _
    _ = _ := by rw [euclideanNorm_smul, abs_of_nonneg (by positivity)]

/-- The standard-Gaussian BPS rate is bounded by position norm times speed. -/
theorem standardGaussianBPS_stateRate_le_norm_mul_norm
    (state : BouncyParticleState ι) :
    standardGaussianBouncyParticleBounceData.stateRate state ≤
      euclideanNorm state.2 * euclideanNorm state.1 := by
  unfold BouncyParticleBounceData.stateRate
    standardGaussianBouncyParticleBounceData bouncyRate
  have habs := abs_euclideanInner_le_norm_mul_norm state.2 state.1
  exact (max_le (abs_nonneg _) (le_abs_self _)).trans habs

/-- Combining the preceding estimates gives a deterministic rate envelope
over one flight from a fixed state. -/
theorem standardGaussianBPS_stateRate_flow_le
    (state : BouncyParticleState ι) (time : NNReal) :
    standardGaussianBouncyParticleBounceData.stateRate
        (bouncyParticleFlow time state) ≤
      euclideanNorm state.2 *
        (euclideanNorm state.1 + (time : ℝ) * euclideanNorm state.2) := by
  calc
    _ ≤ euclideanNorm (bouncyParticleFlow time state).2 *
        euclideanNorm (bouncyParticleFlow time state).1 :=
      standardGaussianBPS_stateRate_le_norm_mul_norm _
    _ ≤ _ := by
      rw [bouncyParticleFlow_velocity]
      exact mul_le_mul_of_nonneg_left
        (bouncyParticleFlow_position_norm_le time state)
        (euclideanNorm_nonneg state.2)

/-- Deterministic Gaussian-BPS jump map used by repeated inverse-clock
execution. -/
noncomputable def standardGaussianBPSJump
    (state : BouncyParticleState ι) : BouncyParticleState ι :=
  (state.1, bouncyReflection state.1 state.2)

theorem measurable_standardGaussianBPSJump :
    Measurable (standardGaussianBPSJump :
      BouncyParticleState ι → BouncyParticleState ι) := by
  change Measurable (fun state : Position ι × Position ι =>
    (state.1, bouncyReflection state.1 state.2))
  exact (standardGaussianBouncyParticleBounceData
    (ι := ι)).measurable_bounce

/-- Uniform rate envelope over all flight time still available from a capped
state. -/
noncomputable def standardGaussianBPSRateEnvelope
    (remainingState : NNReal × BouncyParticleState ι) : NNReal :=
  Real.toNNReal
    (euclideanNorm remainingState.2.2 *
      (euclideanNorm remainingState.2.1 +
        (remainingState.1 : ℝ) * euclideanNorm remainingState.2.2))

theorem standardGaussianBPSRateEnvelope_coe
    (remainingState : NNReal × BouncyParticleState ι) :
    (standardGaussianBPSRateEnvelope remainingState : ℝ) =
      euclideanNorm remainingState.2.2 *
        (euclideanNorm remainingState.2.1 +
          (remainingState.1 : ℝ) * euclideanNorm remainingState.2.2) := by
  rw [standardGaussianBPSRateEnvelope, Real.coe_toNNReal]
  exact mul_nonneg (euclideanNorm_nonneg _)
    (add_nonneg (euclideanNorm_nonneg _)
      (mul_nonneg remainingState.1.coe_nonneg (euclideanNorm_nonneg _)))

/-- After an accepted flight and bounce, the rate envelope for the residual
horizon cannot increase. -/
theorem standardGaussianBPSRateEnvelope_after_event_le
    (remaining : NNReal) (state : BouncyParticleState ι) (wait : NNReal)
    (hwait : wait ≤ remaining) :
    standardGaussianBPSRateEnvelope
        (remaining - wait,
          standardGaussianBPSJump (bouncyParticleFlow wait state)) ≤
      standardGaussianBPSRateEnvelope (remaining, state) := by
  rw [← NNReal.coe_le_coe, standardGaussianBPSRateEnvelope_coe,
    standardGaussianBPSRateEnvelope_coe]
  have hspeed : euclideanNorm
      (standardGaussianBPSJump (bouncyParticleFlow wait state)).2 =
      euclideanNorm state.2 := by
    unfold standardGaussianBPSJump
    rw [euclideanNorm_bouncyReflection_total,
      bouncyParticleFlow_velocity]
  have hposition : euclideanNorm
      (standardGaussianBPSJump (bouncyParticleFlow wait state)).1 ≤
      euclideanNorm state.1 + (wait : ℝ) * euclideanNorm state.2 := by
    exact bouncyParticleFlow_position_norm_le wait state
  rw [hspeed, NNReal.coe_sub hwait]
  apply mul_le_mul_of_nonneg_left _ (euclideanNorm_nonneg state.2)
  calc
    euclideanNorm
          (standardGaussianBPSJump (bouncyParticleFlow wait state)).1 +
        ((remaining : ℝ) - (wait : ℝ)) * euclideanNorm state.2 ≤
      euclideanNorm state.1 + (wait : ℝ) * euclideanNorm state.2 +
        ((remaining : ℝ) - (wait : ℝ)) * euclideanNorm state.2 := by
          gcongr
    _ = euclideanNorm state.1 +
        (remaining : ℝ) * euclideanNorm state.2 := by ring

/-- Integrated Gaussian-BPS rate over any available subflight is bounded by
elapsed time times the envelope of the original capped state. -/
theorem standardGaussianBPS_accumulated_le_wait_mul_envelope
    (remaining : NNReal) (state : BouncyParticleState ι) (wait : NNReal)
    (hwait : wait ≤ remaining) :
    (∫ elapsed in (0 : ℝ)..(wait : ℝ),
      standardGaussianBouncyParticleBounceData.stateRate
        (bouncyParticleFlow (Real.toNNReal elapsed) state)) ≤
      (wait : ℝ) *
        (standardGaussianBPSRateEnvelope (remaining, state) : ℝ) := by
  let rate : ℝ → ℝ := fun elapsed =>
    standardGaussianBouncyParticleBounceData.stateRate
      (bouncyParticleFlow (Real.toNNReal elapsed) state)
  have hpoint : ∀ elapsed ∈ Set.uIoc (0 : ℝ) (wait : ℝ),
      ‖rate elapsed‖ ≤
        (standardGaussianBPSRateEnvelope (remaining, state) : ℝ) := by
    intro elapsed helapsed
    rw [Set.uIoc_of_le (by positivity)] at helapsed
    have helapsed0 : 0 ≤ elapsed := helapsed.1.le
    have helapsedWait : Real.toNNReal elapsed ≤ wait := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ helapsed0]
      exact helapsed.2
    have helapsedRemaining : Real.toNNReal elapsed ≤ remaining :=
      helapsedWait.trans hwait
    have hrate := standardGaussianBPS_stateRate_flow_le state
      (Real.toNNReal elapsed)
    have hnonneg : 0 ≤ rate elapsed := by
      unfold rate BouncyParticleBounceData.stateRate bouncyRate
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    calc
      rate elapsed ≤ euclideanNorm state.2 *
          (euclideanNorm state.1 +
            (Real.toNNReal elapsed : ℝ) * euclideanNorm state.2) := hrate
      _ ≤ euclideanNorm state.2 *
          (euclideanNorm state.1 +
            (remaining : ℝ) * euclideanNorm state.2) := by
        apply mul_le_mul_of_nonneg_left _ (euclideanNorm_nonneg _)
        simpa [add_comm] using add_le_add_left
          (mul_le_mul_of_nonneg_right (by exact_mod_cast helapsedRemaining)
            (euclideanNorm_nonneg state.2)) (euclideanNorm state.1)
      _ = (standardGaussianBPSRateEnvelope (remaining, state) : ℝ) := by
        rw [standardGaussianBPSRateEnvelope_coe]
  calc
    (∫ elapsed in (0 : ℝ)..(wait : ℝ), rate elapsed) ≤
        ‖∫ elapsed in (0 : ℝ)..(wait : ℝ), rate elapsed‖ :=
      le_trans (le_abs_self _) (by rw [Real.norm_eq_abs])
    _ ≤ (standardGaussianBPSRateEnvelope (remaining, state) : ℝ) *
        |(wait : ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = (wait : ℝ) *
        (standardGaussianBPSRateEnvelope (remaining, state) : ℝ) := by
      rw [sub_zero, abs_of_nonneg wait.coe_nonneg]
      ring

/-- Real-valued closed-form candidate solving the Gaussian integrated-hazard
equation when velocity is nonzero. The outer `toNNReal` used by the clock is
introduced separately after positivity is established. -/
noncomputable def gaussianBPSWaitingTimeReal
    (state : BouncyParticleState ι) (hazard : NNReal) : ℝ :=
  let a := gaussianBPSLinearCoefficient state
  let b := gaussianBPSQuadraticCoefficient state
  (Real.sqrt ((max 0 a) ^ 2 + 2 * b * (hazard : ℝ)) - a) / b

theorem gaussianBPSWaitingTimeReal_pos
    (state : BouncyParticleState ι) {hazard : NNReal}
    (hvelocity : state.2 ≠ 0) (hhazard : 0 < hazard) :
    0 < gaussianBPSWaitingTimeReal state hazard := by
  let a := gaussianBPSLinearCoefficient state
  let b := gaussianBPSQuadraticCoefficient state
  have hb : 0 < b := gaussianBPSQuadraticCoefficient_pos state hvelocity
  have hh : 0 < (hazard : ℝ) := by exact_mod_cast hhazard
  have hsqrt : a < Real.sqrt ((max 0 a) ^ 2 + 2 * b * (hazard : ℝ)) := by
    have hnonneg : 0 ≤ (max 0 a) ^ 2 + 2 * b * (hazard : ℝ) := by positivity
    by_cases ha : 0 ≤ a
    · have hinside : a ^ 2 < (max 0 a) ^ 2 + 2 * b * (hazard : ℝ) := by
        rw [max_eq_right ha]
        nlinarith
      nlinarith [Real.sq_sqrt hnonneg,
        Real.sqrt_nonneg ((max 0 a) ^ 2 + 2 * b * (hazard : ℝ))]
    · have ha' : a < 0 := lt_of_not_ge ha
      exact lt_of_lt_of_le ha' (Real.sqrt_nonneg _)
  unfold gaussianBPSWaitingTimeReal
  dsimp only
  exact div_pos (sub_pos.mpr hsqrt) hb

/-- Nonnegative clock-valued version of the closed-form Gaussian wait. -/
noncomputable def gaussianBPSWaitingTime
    (state : BouncyParticleState ι) (hazard : NNReal) : NNReal :=
  Real.toNNReal (gaussianBPSWaitingTimeReal state hazard)

theorem gaussianBPSWaitingTime_coe
    (state : BouncyParticleState ι) {hazard : NNReal}
    (hvelocity : state.2 ≠ 0) (hhazard : 0 < hazard) :
    (gaussianBPSWaitingTime state hazard : ℝ) =
      gaussianBPSWaitingTimeReal state hazard := by
  rw [gaussianBPSWaitingTime, Real.coe_toNNReal]
  exact (gaussianBPSWaitingTimeReal_pos state hvelocity hhazard).le

theorem gaussianBPSWaitingTime_pos
    (state : BouncyParticleState ι) {hazard : NNReal}
    (hvelocity : state.2 ≠ 0) (hhazard : 0 < hazard) :
    0 < gaussianBPSWaitingTime state hazard := by
  rw [← NNReal.coe_pos, gaussianBPSWaitingTime_coe state hvelocity hhazard]
  exact gaussianBPSWaitingTimeReal_pos state hvelocity hhazard

/-- At the closed-form wait, the affine directional derivative reaches the
positive square-root endpoint used to invert accumulated hazard. -/
theorem gaussianBPS_affine_at_waitingTimeReal
    (state : BouncyParticleState ι) {hazard : NNReal}
    (hvelocity : state.2 ≠ 0) :
    gaussianBPSLinearCoefficient state +
        gaussianBPSQuadraticCoefficient state *
          gaussianBPSWaitingTimeReal state hazard =
      Real.sqrt
        ((max 0 (gaussianBPSLinearCoefficient state)) ^ 2 +
          2 * gaussianBPSQuadraticCoefficient state * (hazard : ℝ)) := by
  have hb : gaussianBPSQuadraticCoefficient state ≠ 0 :=
    ne_of_gt (gaussianBPSQuadraticCoefficient_pos state hvelocity)
  unfold gaussianBPSWaitingTimeReal
  dsimp only
  field_simp
  ring

/-- Algebraic inverse-hazard identity. Once the scalar integral of the
positive affine part is identified with this positive-part square increment,
the exact clock inverse follows immediately. -/
theorem gaussianBPS_positivePartSquare_waitingTimeReal
    (state : BouncyParticleState ι) {hazard : NNReal}
    (hvelocity : state.2 ≠ 0) :
    (max 0 (gaussianBPSLinearCoefficient state +
        gaussianBPSQuadraticCoefficient state *
          gaussianBPSWaitingTimeReal state hazard)) ^ 2 -
      (max 0 (gaussianBPSLinearCoefficient state)) ^ 2 =
        2 * gaussianBPSQuadraticCoefficient state * (hazard : ℝ) := by
  rw [gaussianBPS_affine_at_waitingTimeReal state hvelocity]
  have hb : 0 ≤ gaussianBPSQuadraticCoefficient state :=
    gaussianBPSQuadraticCoefficient_nonneg state
  have hinside : 0 ≤
      (max 0 (gaussianBPSLinearCoefficient state)) ^ 2 +
        2 * gaussianBPSQuadraticCoefficient state * (hazard : ℝ) := by
    positivity
  rw [max_eq_right (Real.sqrt_nonneg _), Real.sq_sqrt hinside]
  ring

/-- Exact accumulated standard-Gaussian BPS hazard over any nonnegative
duration, expressed by the positive-part square increment. -/
theorem standardGaussianBPS_accumulated
    (state : BouncyParticleState ι) (time : NNReal)
    (hvelocity : state.2 ≠ 0) :
    (∫ elapsed in (0 : ℝ)..(time : ℝ),
      standardGaussianBouncyParticleBounceData.stateRate
        (bouncyParticleFlow (Real.toNNReal elapsed) state)) =
      ((max 0 (gaussianBPSLinearCoefficient state +
          (time : ℝ) * gaussianBPSQuadraticCoefficient state)) ^ 2 -
        (max 0 (gaussianBPSLinearCoefficient state)) ^ 2) /
          (2 * gaussianBPSQuadraticCoefficient state) := by
  calc
    (∫ elapsed in (0 : ℝ)..(time : ℝ),
      standardGaussianBouncyParticleBounceData.stateRate
        (bouncyParticleFlow (Real.toNNReal elapsed) state)) =
        ∫ elapsed in (0 : ℝ)..(time : ℝ),
          max 0 (gaussianBPSLinearCoefficient state +
            gaussianBPSQuadraticCoefficient state * elapsed) := by
      apply intervalIntegral.integral_congr
      intro elapsed helapsed
      change standardGaussianBouncyParticleBounceData.stateRate
        (bouncyParticleFlow (Real.toNNReal elapsed) state) = _
      rw [standardGaussianBPS_stateRate_flow]
      have helapsed0 : 0 ≤ elapsed := by
        rw [Set.uIcc_of_le (show (0 : ℝ) ≤ (time : ℝ) by positivity)] at helapsed
        exact helapsed.1
      rw [Real.coe_toNNReal _ helapsed0]
      simp only [mul_comm]
    _ = _ := by
      simpa [mul_comm] using intervalIntegral_max_zero_affine
        (gaussianBPSLinearCoefficient state)
        (gaussianBPSQuadraticCoefficient state) (time : ℝ)
        (gaussianBPSQuadraticCoefficient_pos state hvelocity) (by positivity)

/-- Integrated Gaussian-BPS hazard is an additive cocycle over linear flight. -/
theorem standardGaussianBPS_accumulated_add
    (state : BouncyParticleState ι) (first second : NNReal) :
    (∫ elapsed in (0 : ℝ)..((first + second : NNReal) : ℝ),
      standardGaussianBouncyParticleBounceData.stateRate
        (bouncyParticleFlow (Real.toNNReal elapsed) state)) =
      (∫ elapsed in (0 : ℝ)..(first : ℝ),
        standardGaussianBouncyParticleBounceData.stateRate
          (bouncyParticleFlow (Real.toNNReal elapsed) state)) +
      ∫ elapsed in (0 : ℝ)..(second : ℝ),
        standardGaussianBouncyParticleBounceData.stateRate
          (bouncyParticleFlow (Real.toNNReal elapsed)
            (bouncyParticleFlow first state)) := by
  by_cases hvelocity : state.2 = 0
  · have hrate : ∀ (base : BouncyParticleState ι) (hbase : base.2 = 0)
        (elapsed : ℝ),
        standardGaussianBouncyParticleBounceData.stateRate
          (bouncyParticleFlow (Real.toNNReal elapsed) base) = 0 := by
      intro base hbase elapsed
      unfold BouncyParticleBounceData.stateRate
        standardGaussianBouncyParticleBounceData bouncyRate
      simp [bouncyParticleFlow, hbase, euclideanInner]
    rw [intervalIntegral.integral_congr
        (fun elapsed _ => hrate state hvelocity elapsed),
      intervalIntegral.integral_congr
        (fun elapsed _ => hrate state hvelocity elapsed),
      intervalIntegral.integral_congr (fun elapsed _ =>
        hrate (bouncyParticleFlow first state) (by simp [hvelocity]) elapsed)]
    simp
  · have hflowVelocity : (bouncyParticleFlow first state).2 ≠ 0 := by
      simpa using hvelocity
    rw [standardGaussianBPS_accumulated state (first + second) hvelocity,
      standardGaussianBPS_accumulated state first hvelocity,
      standardGaussianBPS_accumulated (bouncyParticleFlow first state)
        second hflowVelocity,
      gaussianBPSLinearCoefficient_flow,
      gaussianBPSQuadraticCoefficient_flow]
    have haffine : gaussianBPSLinearCoefficient state +
        ((first + second : NNReal) : ℝ) *
          gaussianBPSQuadraticCoefficient state =
      gaussianBPSLinearCoefficient state +
          (first : ℝ) * gaussianBPSQuadraticCoefficient state +
        (second : ℝ) * gaussianBPSQuadraticCoefficient state := by
      push_cast
      ring
    rw [haffine]
    ring

/-- The closed-form nonzero-velocity wait exactly inverts the integrated
canonical Gaussian BPS rate. -/
theorem standardGaussianBPS_waitingTime_inverse
    (state : BouncyParticleState ι) {hazard : NNReal}
    (hvelocity : state.2 ≠ 0) (hhazard : 0 < hazard) :
    (∫ elapsed in (0 : ℝ)..(gaussianBPSWaitingTime state hazard : ℝ),
      standardGaussianBouncyParticleBounceData.stateRate
        (bouncyParticleFlow (Real.toNNReal elapsed) state)) =
      (hazard : ℝ) := by
  rw [standardGaussianBPS_accumulated state
    (gaussianBPSWaitingTime state hazard) hvelocity]
  rw [gaussianBPSWaitingTime_coe state hvelocity hhazard]
  rw [show gaussianBPSLinearCoefficient state +
      gaussianBPSWaitingTimeReal state hazard *
        gaussianBPSQuadraticCoefficient state =
      gaussianBPSLinearCoefficient state +
        gaussianBPSQuadraticCoefficient state *
          gaussianBPSWaitingTimeReal state hazard by ring]
  rw [gaussianBPS_positivePartSquare_waitingTimeReal state hvelocity]
  have hb : gaussianBPSQuadraticCoefficient state ≠ 0 :=
    ne_of_gt (gaussianBPSQuadraticCoefficient_pos state hvelocity)
  apply (div_eq_iff (mul_ne_zero (by norm_num) hb)).2
  ring

/-- The closed-form positive Gaussian-BPS inverse clock is the unique
nonnegative time accumulating a prescribed positive hazard. -/
theorem gaussianBPSWaitingTime_unique
    (state : BouncyParticleState ι) (hvelocity : state.2 ≠ 0)
    (hazard : NNReal) (hhazard : 0 < hazard) (time : NNReal)
    (htime : (∫ elapsed in (0 : ℝ)..(time : ℝ),
      standardGaussianBouncyParticleBounceData.stateRate
        (bouncyParticleFlow (Real.toNNReal elapsed) state)) =
          (hazard : ℝ)) :
    time = gaussianBPSWaitingTime state hazard := by
  let a := gaussianBPSLinearCoefficient state
  let b := gaussianBPSQuadraticCoefficient state
  let wait := gaussianBPSWaitingTime state hazard
  have hb : 0 < b := gaussianBPSQuadraticCoefficient_pos state hvelocity
  have hbne : 2 * b ≠ 0 := mul_ne_zero (by norm_num) hb.ne'
  have htimeFormula := standardGaussianBPS_accumulated state time hvelocity
  rw [htimeFormula] at htime
  have htimeSquare :
      (max 0 (a + (time : ℝ) * b)) ^ 2 - (max 0 a) ^ 2 =
        2 * b * (hazard : ℝ) := by
    dsimp [a, b] at htime ⊢
    apply (div_eq_iff hbne).mp at htime
    nlinarith
  have hwaitSquare :
      (max 0 (a + (wait : ℝ) * b)) ^ 2 - (max 0 a) ^ 2 =
        2 * b * (hazard : ℝ) := by
    have hcoerce := gaussianBPSWaitingTime_coe state hvelocity hhazard
    have hsquare := gaussianBPS_positivePartSquare_waitingTimeReal
      (hazard := hazard) state hvelocity
    dsimp [a, b, wait]
    rw [hcoerce]
    simpa [mul_comm] using hsquare
  have hsquares :
      (max 0 (a + (time : ℝ) * b)) ^ 2 =
        (max 0 (a + (wait : ℝ) * b)) ^ 2 := by
    linarith
  have hmax : max 0 (a + (time : ℝ) * b) =
      max 0 (a + (wait : ℝ) * b) := by
    nlinarith [le_max_left 0 (a + (time : ℝ) * b),
      le_max_left 0 (a + (wait : ℝ) * b)]
  have hwaitMaxPos : 0 < max 0 (a + (wait : ℝ) * b) := by
    have hhazardReal : 0 < (hazard : ℝ) := by exact_mod_cast hhazard
    have hproduct : 0 < 2 * b * (hazard : ℝ) := by positivity
    have hnonneg : 0 ≤ max 0 (a + (wait : ℝ) * b) :=
      le_max_left _ _
    nlinarith [sq_nonneg (max 0 a), hwaitSquare]
  have htimeAffinePos : 0 < a + (time : ℝ) * b := by
    have : 0 < max 0 (a + (time : ℝ) * b) := hmax ▸ hwaitMaxPos
    rw [lt_max_iff] at this
    exact this.resolve_left (lt_irrefl 0)
  have hwaitAffinePos : 0 < a + (wait : ℝ) * b := by
    rw [lt_max_iff] at hwaitMaxPos
    exact hwaitMaxPos.resolve_left (lt_irrefl 0)
  rw [max_eq_right htimeAffinePos.le,
    max_eq_right hwaitAffinePos.le] at hmax
  have hcoe : (time : ℝ) = (wait : ℝ) := by
    nlinarith
  exact_mod_cast hcoe

theorem standardGaussianBPS_accumulated_nonneg
    (state : BouncyParticleState ι) (hvelocity : state.2 ≠ 0)
    (time : NNReal) :
    0 ≤ (∫ elapsed in (0 : ℝ)..(time : ℝ),
      standardGaussianBouncyParticleBounceData.stateRate
        (bouncyParticleFlow (Real.toNNReal elapsed) state)) := by
  rw [standardGaussianBPS_accumulated state time hvelocity]
  have hb : 0 < gaussianBPSQuadraticCoefficient state :=
    gaussianBPSQuadraticCoefficient_pos state hvelocity
  have haffine : gaussianBPSLinearCoefficient state ≤
      gaussianBPSLinearCoefficient state +
        (time : ℝ) * gaussianBPSQuadraticCoefficient state := by
    nlinarith [mul_nonneg time.coe_nonneg hb.le]
  have hmax := max_le_max_left 0 haffine
  have hsquare :
      (max 0 (gaussianBPSLinearCoefficient state)) ^ 2 ≤
        (max 0 (gaussianBPSLinearCoefficient state +
          (time : ℝ) * gaussianBPSQuadraticCoefficient state)) ^ 2 := by
    nlinarith [le_max_left 0 (gaussianBPSLinearCoefficient state),
      le_max_left 0 (gaussianBPSLinearCoefficient state +
        (time : ℝ) * gaussianBPSQuadraticCoefficient state)]
  positivity

theorem standardGaussianBPS_accumulated_mono
    (state : BouncyParticleState ι) (hvelocity : state.2 ≠ 0)
    {first second : NNReal} (htime : first ≤ second) :
    (∫ elapsed in (0 : ℝ)..(first : ℝ),
      standardGaussianBouncyParticleBounceData.stateRate
        (bouncyParticleFlow (Real.toNNReal elapsed) state)) ≤
    ∫ elapsed in (0 : ℝ)..(second : ℝ),
      standardGaussianBouncyParticleBounceData.stateRate
        (bouncyParticleFlow (Real.toNNReal elapsed) state) := by
  rw [standardGaussianBPS_accumulated state first hvelocity,
    standardGaussianBPS_accumulated state second hvelocity]
  have hb : 0 < gaussianBPSQuadraticCoefficient state :=
    gaussianBPSQuadraticCoefficient_pos state hvelocity
  have htimeReal : (first : ℝ) ≤ (second : ℝ) := by exact_mod_cast htime
  have haffine : gaussianBPSLinearCoefficient state +
      (first : ℝ) * gaussianBPSQuadraticCoefficient state ≤
    gaussianBPSLinearCoefficient state +
      (second : ℝ) * gaussianBPSQuadraticCoefficient state := by
    nlinarith
  have hmax := max_le_max_left 0 haffine
  have hsquare :
      (max 0 (gaussianBPSLinearCoefficient state +
        (first : ℝ) * gaussianBPSQuadraticCoefficient state)) ^ 2 ≤
      (max 0 (gaussianBPSLinearCoefficient state +
        (second : ℝ) * gaussianBPSQuadraticCoefficient state)) ^ 2 := by
    nlinarith [le_max_left 0 (gaussianBPSLinearCoefficient state +
      (first : ℝ) * gaussianBPSQuadraticCoefficient state),
      le_max_left 0 (gaussianBPSLinearCoefficient state +
        (second : ℝ) * gaussianBPSQuadraticCoefficient state)]
  exact (div_le_div_iff_of_pos_right (by positivity)).2 (by linarith)

/-- Before the unique positive inverse-clock time, accumulated hazard is
strictly below the requested mark. -/
theorem standardGaussianBPS_accumulated_lt_hazard_of_lt_waitingTime
    (state : BouncyParticleState ι) (hvelocity : state.2 ≠ 0)
    (hazard : NNReal) (hhazard : 0 < hazard) (time : NNReal)
    (htime : time < gaussianBPSWaitingTime state hazard) :
    (∫ elapsed in (0 : ℝ)..(time : ℝ),
      standardGaussianBouncyParticleBounceData.stateRate
        (bouncyParticleFlow (Real.toNNReal elapsed) state)) <
      (hazard : ℝ) := by
  let wait := gaussianBPSWaitingTime state hazard
  let a := gaussianBPSLinearCoefficient state
  let b := gaussianBPSQuadraticCoefficient state
  have hb : 0 < b := gaussianBPSQuadraticCoefficient_pos state hvelocity
  have htimeReal : (time : ℝ) < (wait : ℝ) := by exact_mod_cast htime
  have haffine : a + (time : ℝ) * b ≤ a + (wait : ℝ) * b := by
    nlinarith
  have hmax : max 0 (a + (time : ℝ) * b) ≤
      max 0 (a + (wait : ℝ) * b) :=
    max_le_max_left 0 haffine
  have hsquare : (max 0 (a + (time : ℝ) * b)) ^ 2 ≤
      (max 0 (a + (wait : ℝ) * b)) ^ 2 := by
    nlinarith [le_max_left 0 (a + (time : ℝ) * b),
      le_max_left 0 (a + (wait : ℝ) * b)]
  have hformula := standardGaussianBPS_accumulated state time hvelocity
  have hinverse := standardGaussianBPS_waitingTime_inverse
    state hvelocity hhazard
  have hwaitFormula := standardGaussianBPS_accumulated state wait hvelocity
  rw [hwaitFormula] at hinverse
  have hle :
      (∫ elapsed in (0 : ℝ)..(time : ℝ),
        standardGaussianBouncyParticleBounceData.stateRate
          (bouncyParticleFlow (Real.toNNReal elapsed) state)) ≤
        (hazard : ℝ) := by
    rw [hformula]
    dsimp [a, b, wait] at hsquare ⊢
    rw [← hinverse]
    exact (div_le_div_iff_of_pos_right (by positivity)).2 (by linarith)
  exact lt_of_le_of_ne hle fun heq =>
    htime.ne (gaussianBPSWaitingTime_unique state hvelocity hazard hhazard time
      heq)

/-- The inverse wait lies within a horizon exactly when the requested mark is
at most the hazard accumulated over that horizon. -/
theorem gaussianBPSWaitingTime_le_iff
    (state : BouncyParticleState ι) (hvelocity : state.2 ≠ 0)
    (hazard : NNReal) (hhazard : 0 < hazard) (horizon : NNReal) :
    gaussianBPSWaitingTime state hazard ≤ horizon ↔
      (hazard : ℝ) ≤
        ∫ elapsed in (0 : ℝ)..(horizon : ℝ),
          standardGaussianBouncyParticleBounceData.stateRate
            (bouncyParticleFlow (Real.toNNReal elapsed) state) := by
  constructor
  · intro hwait
    rw [← standardGaussianBPS_waitingTime_inverse
      state hvelocity hhazard]
    exact standardGaussianBPS_accumulated_mono state hvelocity hwait
  · intro haccumulated
    by_contra hwait
    have hhorizon : horizon < gaussianBPSWaitingTime state hazard :=
      lt_of_not_ge hwait
    have hstrict :=
      standardGaussianBPS_accumulated_lt_hazard_of_lt_waitingTime
        state hvelocity hazard hhazard horizon hhorizon
    linarith

/-- Integrated hazard consumed before a finite split. -/
noncomputable def gaussianBPSConsumedHazard
    (state : BouncyParticleState ι) (time : NNReal) : NNReal :=
  Real.toNNReal
    (∫ elapsed in (0 : ℝ)..(time : ℝ),
      standardGaussianBouncyParticleBounceData.stateRate
        (bouncyParticleFlow (Real.toNNReal elapsed) state))

theorem measurable_gaussianBPSConsumedHazard :
    Measurable (fun input : BouncyParticleState ι × NNReal =>
      gaussianBPSConsumedHazard input.1 input.2) := by
  let formula : BouncyParticleState ι × NNReal → NNReal := fun input =>
    if input.1.2 = 0 then 0 else Real.toNNReal
      (((max 0 (gaussianBPSLinearCoefficient input.1 +
          (input.2 : ℝ) * gaussianBPSQuadraticCoefficient input.1)) ^ 2 -
        (max 0 (gaussianBPSLinearCoefficient input.1)) ^ 2) /
          (2 * gaussianBPSQuadraticCoefficient input.1))
  have hformula : (fun input : BouncyParticleState ι × NNReal =>
      gaussianBPSConsumedHazard input.1 input.2) = formula := by
    funext input
    by_cases hvelocity : input.1.2 = 0
    · unfold gaussianBPSConsumedHazard formula
      simp only [hvelocity, if_pos]
      have hrate : ∀ elapsed : ℝ,
          standardGaussianBouncyParticleBounceData.stateRate
            (bouncyParticleFlow (Real.toNNReal elapsed) input.1) = 0 := by
        intro elapsed
        unfold BouncyParticleBounceData.stateRate
          standardGaussianBouncyParticleBounceData bouncyRate
        simp [bouncyParticleFlow, hvelocity, euclideanInner]
      simp_rw [hrate]
      simp
    · unfold gaussianBPSConsumedHazard formula
      rw [if_neg hvelocity,
        standardGaussianBPS_accumulated input.1 input.2 hvelocity]
  rw [hformula]
  unfold formula gaussianBPSLinearCoefficient gaussianBPSQuadraticCoefficient
    squaredEuclideanNorm euclideanInner
  apply Measurable.ite
  · exact (measurableSet_singleton (0 : Position ι)).preimage
      (measurable_snd.comp measurable_fst)
  · exact measurable_const
  · fun_prop

/-- Residual integrated-hazard mark after a finite split. -/
noncomputable def gaussianBPSResidualHazard
    (state : BouncyParticleState ι) (hazard time : NNReal) : NNReal :=
  hazard - gaussianBPSConsumedHazard state time

/-- Exact-boundary ringing is equivalently equality of the sampled mark with
the accumulated hazard threshold. -/
theorem gaussianBPSWaitingTime_eq_iff
    (state : BouncyParticleState ι) (hvelocity : state.2 ≠ 0)
    (hazard : NNReal) (hhazard : 0 < hazard) (horizon : NNReal) :
    gaussianBPSWaitingTime state hazard = horizon ↔
      hazard = gaussianBPSConsumedHazard state horizon := by
  have hnonneg := standardGaussianBPS_accumulated_nonneg
    state hvelocity horizon
  constructor
  · intro hwait
    have hinverse := standardGaussianBPS_waitingTime_inverse
      state hvelocity hhazard
    rw [hwait] at hinverse
    apply NNReal.eq
    unfold gaussianBPSConsumedHazard
    rw [Real.coe_toNNReal _ hnonneg]
    exact hinverse.symm
  · intro hhazardEq
    have htime :
        (∫ elapsed in (0 : ℝ)..(horizon : ℝ),
          standardGaussianBouncyParticleBounceData.stateRate
            (bouncyParticleFlow (Real.toNNReal elapsed) state)) =
          (hazard : ℝ) := by
      have hcoe := congrArg (fun value : NNReal => (value : ℝ)) hhazardEq
      unfold gaussianBPSConsumedHazard at hcoe
      rw [Real.coe_toNNReal _ hnonneg] at hcoe
      exact hcoe.symm
    exact (gaussianBPSWaitingTime_unique state hvelocity hazard hhazard
      horizon htime).symm

/-- Exact no-event survival probability over a finite Gaussian-BPS flight. -/
theorem unitHazardMeasure_gaussianBPSWaitingTime_gt
    (state : BouncyParticleState ι) (hvelocity : state.2 ≠ 0)
    (horizon : NNReal) :
    unitHazardMeasure
        {hazard | horizon < gaussianBPSWaitingTime state hazard} =
      ENNReal.ofReal (Real.exp
        (-(∫ elapsed in (0 : ℝ)..(horizon : ℝ),
          standardGaussianBouncyParticleBounceData.stateRate
            (bouncyParticleFlow (Real.toNNReal elapsed) state)))) := by
  let accumulated := ∫ elapsed in (0 : ℝ)..(horizon : ℝ),
    standardGaussianBouncyParticleBounceData.stateRate
      (bouncyParticleFlow (Real.toNNReal elapsed) state)
  let consumed := Real.toNNReal accumulated
  have haccumulated : 0 ≤ accumulated :=
    standardGaussianBPS_accumulated_nonneg state hvelocity horizon
  calc
    unitHazardMeasure
        {hazard | horizon < gaussianBPSWaitingTime state hazard} =
      unitHazardMeasure (Set.Ioi consumed) := by
        apply measure_congr
        filter_upwards [unitHazardMeasure_positive_ae] with hazard hhazard
        apply propext
        change (horizon < gaussianBPSWaitingTime state hazard) ↔
          consumed < hazard
        rw [← not_iff_not]
        simp only [not_lt]
        rw [gaussianBPSWaitingTime_le_iff state hvelocity hazard hhazard horizon]
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ haccumulated]
    _ = ENNReal.ofReal (Real.exp (-(consumed : ℝ))) :=
      unitHazardMeasure_Ioi consumed
    _ = ENNReal.ofReal (Real.exp (-accumulated)) := by
      rw [Real.coe_toNNReal _ haccumulated]
    _ = _ := rfl

/-- Conditional on no event before a split, subtracting the consumed
integrated hazard leaves a fresh unit-exponential residual mark, in
unnormalized measure form. -/
theorem unitHazardMeasure_gaussianBPSResidual_memoryless
    (state : BouncyParticleState ι) (hvelocity : state.2 ≠ 0)
    (first : NNReal) :
    Measure.map (fun hazard => gaussianBPSResidualHazard state hazard first)
        (unitHazardMeasure.restrict
          {hazard | first < gaussianBPSWaitingTime state hazard}) =
      ENNReal.ofReal (Real.exp
        (-(∫ elapsed in (0 : ℝ)..(first : ℝ),
          standardGaussianBouncyParticleBounceData.stateRate
            (bouncyParticleFlow (Real.toNNReal elapsed) state)))) •
        unitHazardMeasure := by
  let accumulated := ∫ elapsed in (0 : ℝ)..(first : ℝ),
    standardGaussianBouncyParticleBounceData.stateRate
      (bouncyParticleFlow (Real.toNNReal elapsed) state)
  let consumed := gaussianBPSConsumedHazard state first
  have haccumulated : 0 ≤ accumulated :=
    standardGaussianBPS_accumulated_nonneg state hvelocity first
  have hsets : {hazard | first < gaussianBPSWaitingTime state hazard} =ᵐ[
      unitHazardMeasure] Set.Ioi consumed := by
    filter_upwards [unitHazardMeasure_positive_ae] with hazard hhazard
    apply propext
    change (first < gaussianBPSWaitingTime state hazard) ↔ consumed < hazard
    rw [← not_iff_not]
    simp only [not_lt]
    rw [gaussianBPSWaitingTime_le_iff state hvelocity hazard hhazard first]
    change (hazard : ℝ) ≤ accumulated ↔ hazard ≤ consumed
    rw [← NNReal.coe_le_coe]
    unfold consumed gaussianBPSConsumedHazard
    rw [Real.coe_toNNReal _ haccumulated]
  rw [Measure.restrict_congr_set hsets]
  change Measure.map (fun hazard : NNReal => hazard - consumed)
      (unitHazardMeasure.restrict (Set.Ioi consumed)) = _
  rw [unitHazardMeasure_residual_memoryless]
  congr 2
  unfold consumed gaussianBPSConsumedHazard
  rw [Real.coe_toNNReal _ haccumulated]

/-- Normalized conditional form of the Gaussian-BPS residual-mark law. -/
theorem unitHazardMeasure_gaussianBPSResidual_conditional
    (state : BouncyParticleState ι) (hvelocity : state.2 ≠ 0)
    (first : NNReal) :
    (ENNReal.ofReal (Real.exp
      (-(∫ elapsed in (0 : ℝ)..(first : ℝ),
        standardGaussianBouncyParticleBounceData.stateRate
          (bouncyParticleFlow (Real.toNNReal elapsed) state)))))⁻¹ •
      Measure.map (fun hazard => gaussianBPSResidualHazard state hazard first)
        (unitHazardMeasure.restrict
          {hazard | first < gaussianBPSWaitingTime state hazard}) =
      unitHazardMeasure := by
  rw [unitHazardMeasure_gaussianBPSResidual_memoryless state hvelocity first,
    smul_smul]
  have hne : ENNReal.ofReal (Real.exp
      (-(∫ elapsed in (0 : ℝ)..(first : ℝ),
        standardGaussianBouncyParticleBounceData.stateRate
          (bouncyParticleFlow (Real.toNNReal elapsed) state)))) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  rw [ENNReal.inv_mul_cancel hne ENNReal.ofReal_ne_top, one_smul]

/-- If a finite split occurs before the next event, subtracting the hazard
accumulated up to the split gives exactly the residual inverse-clock wait from
the flowed state. -/
theorem gaussianBPSWaitingTime_residual
    (state : BouncyParticleState ι) (hvelocity : state.2 ≠ 0)
    (hazard : NNReal) (hhazard : 0 < hazard) (first : NNReal)
    (hfirst : first < gaussianBPSWaitingTime state hazard) :
    gaussianBPSWaitingTime (bouncyParticleFlow first state)
        (hazard - Real.toNNReal
          (∫ elapsed in (0 : ℝ)..(first : ℝ),
            standardGaussianBouncyParticleBounceData.stateRate
              (bouncyParticleFlow (Real.toNNReal elapsed) state))) =
      gaussianBPSWaitingTime state hazard - first := by
  let wait := gaussianBPSWaitingTime state hazard
  let accumulated := ∫ elapsed in (0 : ℝ)..(first : ℝ),
    standardGaussianBouncyParticleBounceData.stateRate
      (bouncyParticleFlow (Real.toNNReal elapsed) state)
  let consumed := Real.toNNReal accumulated
  let residual := hazard - consumed
  have haccumulatedNonneg : 0 ≤ accumulated :=
    standardGaussianBPS_accumulated_nonneg state hvelocity first
  have haccumulatedLt : accumulated < (hazard : ℝ) :=
    standardGaussianBPS_accumulated_lt_hazard_of_lt_waitingTime
      state hvelocity hazard hhazard first hfirst
  have hconsumedLt : consumed < hazard := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ haccumulatedNonneg]
    exact haccumulatedLt
  have hresidualPos : 0 < residual := tsub_pos_iff_lt.mpr hconsumedLt
  have hflowVelocity : (bouncyParticleFlow first state).2 ≠ 0 := by
    simpa using hvelocity
  have hcocycle := standardGaussianBPS_accumulated_add state first
    (wait - first)
  have hfirstLe : first ≤ wait := hfirst.le
  rw [add_tsub_cancel_of_le hfirstLe] at hcocycle
  have hinverse := standardGaussianBPS_waitingTime_inverse
    state hvelocity hhazard
  have hresidualIntegral :
      (∫ elapsed in (0 : ℝ)..((wait - first : NNReal) : ℝ),
        standardGaussianBouncyParticleBounceData.stateRate
          (bouncyParticleFlow (Real.toNNReal elapsed)
            (bouncyParticleFlow first state))) = (residual : ℝ) := by
    have hconsumedCoe : (consumed : ℝ) = accumulated := by
      exact Real.coe_toNNReal accumulated haccumulatedNonneg
    have hresidualCoe : (residual : ℝ) = (hazard : ℝ) - accumulated := by
      rw [show residual = hazard - consumed from rfl,
        NNReal.coe_sub hconsumedLt.le, hconsumedCoe]
    rw [hresidualCoe]
    linarith
  have hunique := gaussianBPSWaitingTime_unique
    (bouncyParticleFlow first state) hflowVelocity residual hresidualPos
    (wait - first) hresidualIntegral
  exact hunique.symm

theorem gaussianBPSWaitingTime_residualHazard
    (state : BouncyParticleState ι) (hvelocity : state.2 ≠ 0)
    (hazard : NNReal) (hhazard : 0 < hazard) (first : NNReal)
    (hfirst : first < gaussianBPSWaitingTime state hazard) :
    gaussianBPSWaitingTime (bouncyParticleFlow first state)
        (gaussianBPSResidualHazard state hazard first) =
      gaussianBPSWaitingTime state hazard - first := by
  exact gaussianBPSWaitingTime_residual state hvelocity hazard hhazard
    first hfirst

/-- Splitting a pre-event flight and carrying the residual hazard reaches
exactly the same event location as the unsplit clock. -/
theorem gaussianBPSEventLocation_residualHazard
    (state : BouncyParticleState ι) (hvelocity : state.2 ≠ 0)
    (hazard : NNReal) (hhazard : 0 < hazard) (first : NNReal)
    (hfirst : first < gaussianBPSWaitingTime state hazard) :
    bouncyParticleFlow
        (gaussianBPSWaitingTime (bouncyParticleFlow first state)
          (gaussianBPSResidualHazard state hazard first))
        (bouncyParticleFlow first state) =
      bouncyParticleFlow (gaussianBPSWaitingTime state hazard) state := by
  rw [gaussianBPSWaitingTime_residualHazard state hvelocity hazard hhazard
    first hfirst]
  have hfirstLe : first ≤ gaussianBPSWaitingTime state hazard := hfirst.le
  apply Prod.ext
  · funext index
    simp only [bouncyParticleFlow]
    rw [NNReal.coe_sub hfirstLe]
    ring
  · rfl

/-- The bounce following the residual clock is therefore exactly the same
bounce as in unsplit execution. -/
theorem gaussianBPSJump_residualHazard
    (state : BouncyParticleState ι) (hvelocity : state.2 ≠ 0)
    (hazard : NNReal) (hhazard : 0 < hazard) (first : NNReal)
    (hfirst : first < gaussianBPSWaitingTime state hazard) :
    standardGaussianBPSJump
        (bouncyParticleFlow
          (gaussianBPSWaitingTime (bouncyParticleFlow first state)
            (gaussianBPSResidualHazard state hazard first))
          (bouncyParticleFlow first state)) =
      standardGaussianBPSJump
        (bouncyParticleFlow (gaussianBPSWaitingTime state hazard) state) := by
  rw [gaussianBPSEventLocation_residualHazard state hvelocity hazard hhazard
    first hfirst]

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

/-- Inverse-clock data with an explicit inactive branch. This is the correct
interface for Gaussian BPS at exactly zero velocity, where no positive hazard
can be reached at any finite time. -/
structure BouncyParticlePartialInverseHazardData (ι : Type*) [Fintype ι] where
  bounce : BouncyParticleBounceData ι
  active : BouncyParticleState ι → NNReal → Bool
  waitingTime : BouncyParticleState ι → NNReal → NNReal
  measurable_active : Measurable
    (fun input : BouncyParticleState ι × NNReal => active input.1 input.2)
  measurable_waitingTime : Measurable
    (fun input : BouncyParticleState ι × NNReal =>
      waitingTime input.1 input.2)
  waitingTime_pos : ∀ state {hazard}, 0 < hazard → active state hazard = true →
    0 < waitingTime state hazard
  inverse : ∀ state {hazard}, 0 < hazard → active state hazard = true →
    (∫ time in (0 : ℝ)..(waitingTime state hazard : ℝ),
      bounce.stateRate (bouncyParticleFlow (Real.toNNReal time) state)) =
        (hazard : ℝ)
  inactive : ∀ state {hazard}, active state hazard = false → ∀ time : NNReal,
    (∫ elapsed in (0 : ℝ)..(time : ℝ),
      bounce.stateRate
        (bouncyParticleFlow (Real.toNNReal elapsed) state)) < (hazard : ℝ)

/-- Exact partial inverse clock data for finite-dimensional standard-Gaussian
BPS. Nonzero velocity reaches every positive hazard at the closed-form wait;
zero velocity is the genuine inactive no-event state. -/
noncomputable def standardGaussianBPSPartialInverseHazardData :
    BouncyParticlePartialInverseHazardData ι where
  bounce := standardGaussianBouncyParticleBounceData
  active state hazard := if hazard = 0 then true
    else if state.2 = 0 then false else true
  waitingTime := gaussianBPSWaitingTime
  measurable_active := by
    apply Measurable.ite
    · exact (measurableSet_singleton (0 : NNReal)).preimage measurable_snd
    · exact measurable_const
    · apply Measurable.ite
      · exact (measurableSet_singleton (0 : Position ι)).preimage
          (measurable_snd.comp measurable_fst)
      · exact measurable_const
      · exact measurable_const
  measurable_waitingTime := by
    unfold gaussianBPSWaitingTime gaussianBPSWaitingTimeReal
      gaussianBPSLinearCoefficient gaussianBPSQuadraticCoefficient
      squaredEuclideanNorm euclideanInner
    fun_prop
  waitingTime_pos := by
    intro state hazard hhazard hactive
    have hvelocity : state.2 ≠ 0 := by
      simpa [ne_of_gt hhazard] using hactive
    exact gaussianBPSWaitingTime_pos state hvelocity hhazard
  inverse := by
    intro state hazard hhazard hactive
    have hvelocity : state.2 ≠ 0 := by
      simpa [ne_of_gt hhazard] using hactive
    exact standardGaussianBPS_waitingTime_inverse state hvelocity hhazard
  inactive := by
    intro state hazard hactive time
    have hhazard : hazard ≠ 0 := by
      intro heq
      subst hazard
      simp at hactive
    have hvelocity : state.2 = 0 := by
      by_contra hne
      simp [hhazard, hne] at hactive
    have hrate : ∀ elapsed : ℝ,
        standardGaussianBouncyParticleBounceData.stateRate
          (bouncyParticleFlow (Real.toNNReal elapsed) state) = 0 := by
      intro elapsed
      unfold BouncyParticleBounceData.stateRate
        standardGaussianBouncyParticleBounceData bouncyRate
      simp [bouncyParticleFlow, hvelocity, euclideanInner]
    rw [intervalIntegral.integral_congr (fun elapsed _ => hrate elapsed),
      intervalIntegral.integral_zero]
    exact_mod_cast (pos_iff_ne_zero.mpr hhazard)

/-- Every accepted inverse-clock mark is paid for by elapsed time times the
finite-horizon Gaussian rate envelope. The zero mark is included explicitly,
although it is a null event under the exponential law. -/
theorem standardGaussianBPS_hazard_le_wait_mul_envelope
    (remaining : NNReal) (state : BouncyParticleState ι) (hazard : NNReal)
    (hactive : standardGaussianBPSPartialInverseHazardData.active
      state hazard = true)
    (hwait : standardGaussianBPSPartialInverseHazardData.waitingTime
      state hazard ≤ remaining) :
    hazard ≤
      standardGaussianBPSPartialInverseHazardData.waitingTime state hazard *
        standardGaussianBPSRateEnvelope (remaining, state) := by
  by_cases hhazard : hazard = 0
  · subst hazard
    exact bot_le
  · have hhazardPos : 0 < hazard := pos_iff_ne_zero.mpr hhazard
    rw [← NNReal.coe_le_coe]
    rw [← standardGaussianBPSPartialInverseHazardData.inverse state
      hhazardPos hactive]
    exact standardGaussianBPS_accumulated_le_wait_mul_envelope remaining state
      (standardGaussianBPSPartialInverseHazardData.waitingTime state hazard)
      hwait

/-- Remaining time multiplied by its current rate envelope is a finite
potential that pays for every accepted Gaussian-BPS hazard mark. -/
noncomputable def standardGaussianBPSReplayPotential
    (remainingState : NNReal × BouncyParticleState ι) : NNReal :=
  remainingState.1 * standardGaussianBPSRateEnvelope remainingState

noncomputable def BouncyParticlePartialInverseHazardData.clock
    (data : BouncyParticlePartialInverseHazardData ι) :
    PartialInverseHazardClock (BouncyParticleState ι) where
  semiflow := bouncyParticleJointlyMeasurableSemiflow
  accumulated state time :=
    ∫ elapsed in (0 : ℝ)..(time : ℝ),
      data.bounce.stateRate
        (bouncyParticleFlow (Real.toNNReal elapsed) state)
  active := data.active
  waitingTime := data.waitingTime
  measurable_active := data.measurable_active
  measurable_waitingTime := data.measurable_waitingTime
  waitingTime_pos := data.waitingTime_pos
  inverse := data.inverse
  inactive := data.inactive

theorem standardGaussianBPS_clock_accumulated_add
    (state : BouncyParticleState ι) (first second : NNReal) :
    (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock.accumulated
        state (first + second) =
      (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock.accumulated
          state first +
        (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock.accumulated
          (bouncyParticleFlow first state) second := by
  exact standardGaussianBPS_accumulated_add state first second

/-- Every capped Gaussian-BPS step preserves nonzero velocity, whether it
takes an event branch or finishes by residual flow. -/
theorem standardGaussianBPS_cappedStep_velocity_ne_zero
    (remainingState : NNReal × BouncyParticleState ι) (hazard : NNReal)
    (hvelocity : remainingState.2.2 ≠ 0) :
    ((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
      |>.cappedStepUpdate (standardGaussianBPSJump (ι := ι))
        (remainingState, hazard)).2.2 ≠ 0 := by
  unfold PartialInverseHazardClock.cappedStepUpdate
  dsimp only [Prod.fst, Prod.snd]
  split_ifs with hcondition
  · dsimp only [Prod.snd]
    intro hzero
    change bouncyReflection
      (bouncyParticleFlow
        (gaussianBPSWaitingTime remainingState.2 hazard)
        remainingState.2).1
      (bouncyParticleFlow
        (gaussianBPSWaitingTime remainingState.2 hazard)
        remainingState.2).2 = 0 at hzero
    have hnorm := squaredEuclideanNorm_bouncyReflection_total
      (bouncyParticleFlow
        (gaussianBPSWaitingTime remainingState.2 hazard)
        remainingState.2).1
      (bouncyParticleFlow
        (gaussianBPSWaitingTime remainingState.2 hazard)
        remainingState.2).2
    rw [hzero, squaredEuclideanNorm_eq_zero.mpr rfl,
      bouncyParticleFlow_velocity] at hnorm
    exact hvelocity (squaredEuclideanNorm_eq_zero.mp hnorm.symm)
  · change remainingState.2.2 ≠ 0
    exact hvelocity

/-- Hence every finite Gaussian-BPS replay prefix preserves nonzero
velocity. -/
theorem standardGaussianBPS_replayPrefix_velocity_ne_zero
    (count : ℕ)
    (input : (NNReal × BouncyParticleState ι) × (ℕ → NNReal))
    (hvelocity : input.1.2.2 ≠ 0) :
    (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
      |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count input).2.2) ≠
      0 := by
  induction count with
  | zero => exact hvelocity
  | succ count ih =>
      exact standardGaussianBPS_cappedStep_velocity_ne_zero _ _ ih

/-- Extend a finite hazard prefix by zero.  Only the first `count`
coordinates are inspected when replaying `count` candidates. -/
def finiteHazardPrefixExtension (count : ℕ) (marks : Fin count → NNReal) :
    ℕ → NNReal := fun index =>
  if hindex : index < count then marks ⟨index, hindex⟩ else 0

theorem measurable_finiteHazardPrefixExtension (count : ℕ) :
    Measurable (finiteHazardPrefixExtension count) := by
  apply measurable_pi_lambda
  intro index
  by_cases hindex : index < count
  · simpa [finiteHazardPrefixExtension, hindex] using
      (measurable_pi_apply (⟨index, hindex⟩ : Fin count))
  · simp [finiteHazardPrefixExtension, hindex]

/-- Accumulated terminal-flight hazard as a measurable function of exactly
the preceding finite iid prefix. -/
noncomputable def standardGaussianBPSTerminalThreshold
    (horizon : NNReal) (initial : BouncyParticleState ι) (count : ℕ)
    (marks : Fin count → NNReal) : NNReal :=
  let before :=
    (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
      |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
        ((horizon, initial), finiteHazardPrefixExtension count marks)
  gaussianBPSConsumedHazard before.2 before.1

set_option maxHeartbeats 800000 in
theorem measurable_standardGaussianBPSTerminalThreshold
    (horizon : NNReal) (initial : BouncyParticleState ι) (count : ℕ) :
    Measurable
      (standardGaussianBPSTerminalThreshold (ι := ι) horizon initial count) := by
  unfold standardGaussianBPSTerminalThreshold
  let before : (Fin count → NNReal) → NNReal × BouncyParticleState ι :=
    fun marks =>
      (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
        |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
          ((horizon, initial), finiteHazardPrefixExtension count marks)
  have hbefore : Measurable before :=
    ((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
      |>.measurable_replayPrefix measurable_standardGaussianBPSJump count).comp
        ((measurable_const.prodMk measurable_const).prodMk
          (measurable_finiteHazardPrefixExtension count))
  exact measurable_gaussianBPSConsumedHazard.comp
    (hbefore.snd.prodMk hbefore.fst)

theorem standardGaussianBPSTerminalThreshold_apply
    (horizon : NNReal) (initial : BouncyParticleState ι) (count : ℕ)
    (hazards : ℕ → NNReal) :
    standardGaussianBPSTerminalThreshold (ι := ι) horizon initial count
        (fun index : Fin count => hazards index) =
      gaussianBPSConsumedHazard
        (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
          |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
            ((horizon, initial), hazards)).2)
        (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
          |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
            ((horizon, initial), hazards)).1) := by
  unfold standardGaussianBPSTerminalThreshold
  rw [(standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
    |>.replayPrefix_eq_executeHazards]
  rw [(standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
    |>.replayPrefix_eq_executeHazards]
  simp [hazardPrefix, finiteHazardPrefixExtension]

/-- The next iid hazard mark almost surely misses the accumulated-hazard
threshold determined by all preceding Gaussian-BPS candidates. -/
theorem standardGaussianBPS_terminal_boundary_ae
    (horizon : NNReal) (initial : BouncyParticleState ι) (count : ℕ) :
    ∀ᵐ hazards ∂unitHazardSequenceMeasure,
      hazards count ≠ gaussianBPSConsumedHazard
        (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
          |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
            ((horizon, initial), hazards)).2)
        (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
          |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
            ((horizon, initial), hazards)).1) := by
  have hcoordinateLaw : unitHazardSequenceMeasure.map
      (fun hazards : ℕ → NNReal => hazards count) = unitHazardMeasure := by
    unfold unitHazardSequenceMeasure
    simpa using Measure.infinitePi_map_eval
      (fun _ : ℕ => unitHazardMeasure) count
  filter_upwards [unitHazard_independent_ne_measurable_ae
      unitHazardSequenceMeasure
      (fun hazards : ℕ → NNReal => fun index : Fin count => hazards index)
      (fun hazards : ℕ → NNReal => hazards count)
      (by fun_prop) (by fun_prop)
      (unitHazardSequence_prefix_indep_coordinate count)
      hcoordinateLaw
      (standardGaussianBPSTerminalThreshold (ι := ι) horizon initial count)
      (measurable_standardGaussianBPSTerminalThreshold horizon initial count)]
      with hazards havoid
  rwa [standardGaussianBPSTerminalThreshold_apply] at havoid

/-- On a positive completion stratum, the exceptional exact-boundary branch
forces the terminal hazard coordinate to equal the measurable accumulated
hazard threshold determined by the preceding prefix. -/
theorem standardGaussianBPS_terminal_noEvent_or_hazard_eq_consumed
    (horizon : NNReal) (initial : BouncyParticleState ι)
    (hvelocity : initial.2 ≠ 0) (count : ℕ)
    {hazards : ℕ → NNReal}
    (hmem : hazards ∈
      ((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
        |>.genuineCompletionStratum (standardGaussianBPSJump (ι := ι))
          horizon initial (count + 1)))
    (hhazard : 0 < hazards count) :
    (¬(0 < (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
            |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
              ((horizon, initial), hazards)).1) ∧
        (standardGaussianBPSPartialInverseHazardData (ι := ι)).active
            (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
              |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
                ((horizon, initial), hazards)).2)
            (hazards count) = true ∧
        gaussianBPSWaitingTime
            (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
              |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
                ((horizon, initial), hazards)).2)
            (hazards count) ≤
          (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
            |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
              ((horizon, initial), hazards)).1))) ∨
      hazards count = gaussianBPSConsumedHazard
        (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
          |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
            ((horizon, initial), hazards)).2)
        (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
          |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
            ((horizon, initial), hazards)).1) := by
  let clock := (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
  let jump := standardGaussianBPSJump (ι := ι)
  let before := clock.replayPrefix jump count ((horizon, initial), hazards)
  rcases clock.terminal_noEvent_or_wait_eq_remaining jump horizon initial count
      hmem with hnoevent | hwait
  · exact Or.inl hnoevent
  · right
    have hbeforeVelocity : before.2.2 ≠ 0 :=
      standardGaussianBPS_replayPrefix_velocity_ne_zero count
        ((horizon, initial), hazards) hvelocity
    exact (gaussianBPSWaitingTime_eq_iff before.2 hbeforeVelocity
      (hazards count) hhazard before.1).mp hwait

/-- On every genuine positive completion stratum, the capped terminal
candidate takes the no-event branch almost surely.  Thus exact ringing at the
horizon is removed from subsequent semigroup arguments, rather than resolved
by an arbitrary tie convention. -/
theorem standardGaussianBPS_terminal_noEvent_ae
    (horizon : NNReal) (initial : BouncyParticleState ι)
    (hvelocity : initial.2 ≠ 0) (count : ℕ) :
    ∀ᵐ hazards ∂unitHazardSequenceMeasure,
      hazards ∈
          ((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
            |>.genuineCompletionStratum (standardGaussianBPSJump (ι := ι))
              horizon initial (count + 1)) →
        ¬(0 < (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
                |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
                  ((horizon, initial), hazards)).1) ∧
            (standardGaussianBPSPartialInverseHazardData (ι := ι)).active
                (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
                  |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
                    ((horizon, initial), hazards)).2)
                (hazards count) = true ∧
            gaussianBPSWaitingTime
                (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
                  |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
                    ((horizon, initial), hazards)).2)
                (hazards count) ≤
              (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
                |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
                  ((horizon, initial), hazards)).1)) := by
  filter_upwards [standardGaussianBPS_terminal_boundary_ae
      (ι := ι) horizon initial count,
    unitHazardSequence_coordinate_pos_ae count] with hazards hboundary hpositive
  intro hmem
  rcases standardGaussianBPS_terminal_noEvent_or_hazard_eq_consumed
      horizon initial hvelocity count hmem hpositive with hnoevent | hequal
  · exact hnoevent
  · exact (hboundary hequal).elim

/-- Consequently, on every positive completion stratum the selected endpoint
is almost surely the deterministic residual flow from the preterminal replay
state. -/
theorem standardGaussianBPS_completedEndpoint_eq_flow_on_stratum_ae
    (horizon : NNReal) (initial : BouncyParticleState ι)
    (hvelocity : initial.2 ≠ 0) (count : ℕ) :
    ∀ᵐ hazards ∂unitHazardSequenceMeasure,
      hazards ∈
          ((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
            |>.genuineCompletionStratum (standardGaussianBPSJump (ι := ι))
              horizon initial (count + 1)) →
        ((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
            |>.completedReplayEndpoint (standardGaussianBPSJump (ι := ι))
              ((horizon, initial), hazards)) =
          bouncyParticleFlow
            (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
              |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
                ((horizon, initial), hazards)).1)
            (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
              |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
                ((horizon, initial), hazards)).2) := by
  filter_upwards [standardGaussianBPS_terminal_noEvent_ae
      (ι := ι) horizon initial hvelocity count] with hazards hnoevent
  intro hmem
  exact (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
    |>.completedReplayEndpoint_eq_flow_on_succ_stratum
      (standardGaussianBPSJump (ι := ι)) horizon initial count hmem
        (hnoevent hmem)

/-- Hazard stream used to restart Gaussian BPS after splitting inside the
terminal no-event flight of a completion stratum.  Its head is the residual
of the unspent terminal mark and its tail is the untouched original suffix. -/
noncomputable def standardGaussianBPSSplitResidualStream
    (horizon : NNReal) (initial : BouncyParticleState ι) (count : ℕ)
    (hazards : ℕ → NNReal) : ℕ → NNReal
  | 0 =>
      let before :=
        (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
          |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
            ((horizon, initial), hazards)
      gaussianBPSResidualHazard before.2 (hazards count) before.1
  | index + 1 => hazards (count + index + 1)

set_option maxHeartbeats 800000 in
theorem measurable_standardGaussianBPSSplitResidualStream
    (horizon : NNReal) (initial : BouncyParticleState ι) (count : ℕ) :
    Measurable
      (standardGaussianBPSSplitResidualStream (ι := ι) horizon initial count) := by
  apply measurable_pi_lambda
  intro index
  cases index with
  | zero =>
      unfold standardGaussianBPSSplitResidualStream gaussianBPSResidualHazard
      let before : (ℕ → NNReal) → NNReal × BouncyParticleState ι :=
        fun hazards =>
          (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
            |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
              ((horizon, initial), hazards)
      have hbefore : Measurable before :=
        ((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
          |>.measurable_replayPrefix measurable_standardGaussianBPSJump count)
          |>.comp ((measurable_const.prodMk measurable_const).prodMk
            measurable_id)
      exact (measurable_pi_apply count).sub
        (measurable_gaussianBPSConsumedHazard.comp
          (hbefore.snd.prodMk hbefore.fst))
  | succ index =>
      unfold standardGaussianBPSSplitResidualStream
      exact measurable_pi_apply (count + index + 1)

/-- Block-coordinate form of the split residual stream: retain the finite
prefix as context, subtract its terminal-flight threshold from the next mark,
and cons that residual onto the untouched suffix. -/
noncomputable def standardGaussianBPSSplitResidualFromBlocks
    (horizon : NNReal) (initial : BouncyParticleState ι) (count : ℕ)
    (blocks : (Fin count → NNReal) × (NNReal × (ℕ → NNReal))) :
    ℕ → NNReal :=
  unitHazardCons
    (blocks.2.1 - standardGaussianBPSTerminalThreshold
      (ι := ι) horizon initial count blocks.1, blocks.2.2)

set_option maxHeartbeats 800000 in
theorem measurable_standardGaussianBPSSplitResidualFromBlocks
    (horizon : NNReal) (initial : BouncyParticleState ι) (count : ℕ) :
    Measurable (standardGaussianBPSSplitResidualFromBlocks
      (ι := ι) horizon initial count) := by
  unfold standardGaussianBPSSplitResidualFromBlocks
  apply measurable_unitHazardCons.comp
  exact ((measurable_fst.comp measurable_snd).sub
      ((measurable_standardGaussianBPSTerminalThreshold horizon initial count)
        |>.comp measurable_fst)).prodMk
    (measurable_snd.comp measurable_snd)

/-- The stream-level splice is exactly the finite-prefix/terminal/suffix block
transformation under the deterministic iid factorization. -/
theorem standardGaussianBPSSplitResidualStream_eq_fromBlocks
    (horizon : NNReal) (initial : BouncyParticleState ι) (count : ℕ)
    (hazards : ℕ → NNReal) :
    standardGaussianBPSSplitResidualStream (ι := ι)
        horizon initial count hazards =
      standardGaussianBPSSplitResidualFromBlocks (ι := ι)
        horizon initial count (unitHazardPrefixHeadTail count hazards) := by
  funext index
  cases index with
  | zero =>
      change gaussianBPSResidualHazard
          (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
            |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
              ((horizon, initial), hazards)).2)
          (hazards count)
          (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
            |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
              ((horizon, initial), hazards)).1) =
        hazards count - standardGaussianBPSTerminalThreshold (ι := ι)
          horizon initial count (fun index : Fin count => hazards index)
      rw [standardGaussianBPSTerminalThreshold_apply]
      rfl
  | succ index =>
      change hazards (count + index + 1) = hazards (count + (index + 1))
      congr 1

/-- Finite-prefix block on which the first `count` candidates have all rung
before the horizon, so the replay is still active immediately before the
terminal candidate. -/
def standardGaussianBPSActivePrefixSet
    (horizon : NNReal) (initial : BouncyParticleState ι) (count : ℕ) :
    Set (Fin count → NNReal) :=
  {marks |
    (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
      |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
        ((horizon, initial), finiteHazardPrefixExtension count marks)).1) ≠ 0}

theorem measurableSet_standardGaussianBPSActivePrefixSet
    (horizon : NNReal) (initial : BouncyParticleState ι) (count : ℕ) :
    MeasurableSet
      (standardGaussianBPSActivePrefixSet (ι := ι) horizon initial count) := by
  change MeasurableSet
    ({marks |
      (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
        |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
          ((horizon, initial), finiteHazardPrefixExtension count marks)).1) =
        0}ᶜ)
  apply MeasurableSet.compl
  exact (measurableSet_singleton (0 : NNReal)).preimage
    (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
      |>.measurable_replayPrefix measurable_standardGaussianBPSJump count).fst
      |>.comp ((measurable_const.prodMk measurable_const).prodMk
        (measurable_finiteHazardPrefixExtension count)))

theorem standardGaussianBPSActivePrefixSet_apply
    (horizon : NNReal) (initial : BouncyParticleState ι) (count : ℕ)
    (hazards : ℕ → NNReal) :
    (fun index : Fin count => hazards index) ∈
        standardGaussianBPSActivePrefixSet (ι := ι) horizon initial count ↔
      (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
        |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
          ((horizon, initial), hazards)).1) ≠ 0 := by
  unfold standardGaussianBPSActivePrefixSet
  change
    (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
      |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
        ((horizon, initial), finiteHazardPrefixExtension count
          (fun index : Fin count => hazards index))).1 ≠ 0) ↔ _
  rw [(standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
    |>.replayPrefix_eq_executeHazards]
  rw [(standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
    |>.replayPrefix_eq_executeHazards]
  simp [hazardPrefix, finiteHazardPrefixExtension]

/-- Up to the already excluded zero-mark and exact-boundary null sets, a
genuine `(count+1)` completion stratum is exactly an active finite prefix
followed by a terminal mark above its accumulated-hazard threshold. -/
theorem standardGaussianBPS_mem_stratum_iff_prefix_survival_ae
    (horizon : NNReal) (initial : BouncyParticleState ι)
    (hvelocity : initial.2 ≠ 0) (count : ℕ) :
    ∀ᵐ hazards ∂unitHazardSequenceMeasure,
      (hazards ∈
          ((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
            |>.genuineCompletionStratum (standardGaussianBPSJump (ι := ι))
              horizon initial (count + 1)) ↔
        (fun index : Fin count => hazards index) ∈
            standardGaussianBPSActivePrefixSet (ι := ι)
              horizon initial count ∧
          standardGaussianBPSTerminalThreshold (ι := ι)
              horizon initial count
                (fun index : Fin count => hazards index) < hazards count) := by
  filter_upwards [unitHazardSequence_coordinate_pos_ae count,
    standardGaussianBPS_terminal_noEvent_ae
      (ι := ι) horizon initial hvelocity count] with hazards hpositive hterminal
  let clock := (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
  let jump := standardGaussianBPSJump (ι := ι)
  let before := clock.replayPrefix jump count ((horizon, initial), hazards)
  have hbeforeVelocity : before.2.2 ≠ 0 :=
    standardGaussianBPS_replayPrefix_velocity_ne_zero count
      ((horizon, initial), hazards) hvelocity
  have hactiveMark :
      (standardGaussianBPSPartialInverseHazardData (ι := ι)).active
        before.2 (hazards count) = true := by
    simp [standardGaussianBPSPartialInverseHazardData,
      hpositive.ne', hbeforeVelocity]
  constructor
  · intro hmem
    have hbeforeNe := clock.replayPrefix_fst_ne_zero_on_succ_stratum jump
      horizon initial count hmem
    refine ⟨(standardGaussianBPSActivePrefixSet_apply
      horizon initial count hazards).2 hbeforeNe, ?_⟩
    have hremaining : 0 < before.1 := (pos_iff_ne_zero).2 hbeforeNe
    have hnle : ¬gaussianBPSWaitingTime before.2 (hazards count) ≤ before.1 :=
      fun hle => hterminal hmem ⟨hremaining, hactiveMark, hle⟩
    have hthresholdNotGe : ¬hazards count ≤
        gaussianBPSConsumedHazard before.2 before.1 := by
      intro hle
      have hnonneg := standardGaussianBPS_accumulated_nonneg
        before.2 hbeforeVelocity before.1
      have hleReal : (hazards count : ℝ) ≤
          (∫ elapsed in (0 : ℝ)..(before.1 : ℝ),
            standardGaussianBouncyParticleBounceData.stateRate
              (bouncyParticleFlow (Real.toNNReal elapsed) before.2)) := by
        have hleCoe : (hazards count : ℝ) ≤
            (gaussianBPSConsumedHazard before.2 before.1 : ℝ) := by
          exact_mod_cast hle
        unfold gaussianBPSConsumedHazard at hleCoe
        rwa [Real.coe_toNNReal _ hnonneg] at hleCoe
      have hwait := (gaussianBPSWaitingTime_le_iff before.2
        hbeforeVelocity (hazards count) hpositive before.1).2 (by
          exact hleReal)
      exact hnle hwait
    rw [standardGaussianBPSTerminalThreshold_apply]
    exact lt_of_not_ge hthresholdNotGe
  · rintro ⟨hprefix, hsurvival⟩
    have hbeforeNe := (standardGaussianBPSActivePrefixSet_apply
      horizon initial count hazards).1 hprefix
    have hremaining : 0 < before.1 := (pos_iff_ne_zero).2 hbeforeNe
    rw [standardGaussianBPSTerminalThreshold_apply] at hsurvival
    change gaussianBPSConsumedHazard before.2 before.1 < hazards count
      at hsurvival
    have hnle : ¬gaussianBPSWaitingTime before.2 (hazards count) ≤ before.1 := by
      rw [gaussianBPSWaitingTime_le_iff before.2 hbeforeVelocity
        (hazards count) hpositive before.1]
      have hnonneg := standardGaussianBPS_accumulated_nonneg
        before.2 hbeforeVelocity before.1
      have hsurvivalReal :
          (∫ elapsed in (0 : ℝ)..(before.1 : ℝ),
            standardGaussianBouncyParticleBounceData.stateRate
              (bouncyParticleFlow (Real.toNNReal elapsed) before.2)) <
            (hazards count : ℝ) := by
        have hcoe : (gaussianBPSConsumedHazard before.2 before.1 : ℝ) <
            (hazards count : ℝ) := by
          exact_mod_cast hsurvival
        unfold gaussianBPSConsumedHazard at hcoe
        rwa [Real.coe_toNNReal _ hnonneg] at hcoe
      exact not_le_of_gt hsurvivalReal
    have hnoevent : ¬(0 < before.1 ∧
        (standardGaussianBPSPartialInverseHazardData (ι := ι)).active
          before.2 (hazards count) = true ∧
        gaussianBPSWaitingTime before.2 (hazards count) ≤ before.1) := by
      exact fun condition => hnle condition.2.2
    have hfinished : (clock.replayPrefix jump (count + 1)
        ((horizon, initial), hazards)).1 = 0 := by
      change (clock.cappedStepUpdate jump
        (before, hazards count)).1 = 0
      rw [clock.cappedStepUpdate_of_no_event jump hnoevent]
    exact clock.mem_genuineCompletionStratum_of_prefix_active jump horizon
      initial count hbeforeNe hfinished

/-- Conditional on a fixed finite replay prefix and survival of its terminal
mark, the transformed residual head plus untouched suffix is a fresh iid
hazard stream, scaled by the exact Gaussian-BPS survival mass. -/
theorem standardGaussianBPSSplitResidualFromBlocks_fiberLaw
    (horizon : NNReal) (initial : BouncyParticleState ι) (count : ℕ)
    (marks : Fin count → NNReal) :
    Measure.map
        (fun headTail : NNReal × (ℕ → NNReal) =>
          standardGaussianBPSSplitResidualFromBlocks (ι := ι)
            horizon initial count (marks, headTail))
        ((unitHazardMeasure.prod unitHazardSequenceMeasure).restrict
          {headTail |
            standardGaussianBPSTerminalThreshold (ι := ι)
              horizon initial count marks < headTail.1}) =
      ENNReal.ofReal (Real.exp
          (-(standardGaussianBPSTerminalThreshold (ι := ι)
            horizon initial count marks : ℝ))) •
        unitHazardSequenceMeasure := by
  simpa [standardGaussianBPSSplitResidualFromBlocks] using
    unitHazardMeasure_prod_sequence_residual_map_cons
      (standardGaussianBPSTerminalThreshold (ι := ι)
        horizon initial count marks)

/-- The fixed-prefix fiber laws integrate over the complete active-prefix
region.  The resulting joint law retains the survival-weighted prefix and has
an explicitly fresh iid residual hazard stream. -/
theorem standardGaussianBPSActivePrefixResidualJointMeasure_eq_fresh
    (horizon : NNReal) (initial : BouncyParticleState ι) (count : ℕ) :
    ((unitHazardPrefixMeasure count).restrict
        (standardGaussianBPSActivePrefixSet (ι := ι)
          horizon initial count)) ⊗ₘ
      unitHazardPrefixResidualJointKernel
        (standardGaussianBPSTerminalThreshold (ι := ι)
          horizon initial count) =
    ((unitHazardPrefixMeasure count).restrict
        (standardGaussianBPSActivePrefixSet (ι := ι)
          horizon initial count)) ⊗ₘ
      unitHazardPrefixFreshJointKernel
        (standardGaussianBPSTerminalThreshold (ι := ι)
          horizon initial count) := by
  exact unitHazardPrefixResidualJointMeasure_eq_fresh
    (unitHazardPrefixMeasure count)
    (standardGaussianBPSActivePrefixSet (ι := ι) horizon initial count)
    (standardGaussianBPSTerminalThreshold (ι := ι) horizon initial count)
    (measurable_standardGaussianBPSTerminalThreshold horizon initial count)

/-- Exact block-coordinate stratum law: restrict the factorized iid input to
an active prefix and a surviving terminal mark, transform to prefix plus
residual stream, and obtain the survival-weighted prefix with a fresh iid
stream. -/
theorem standardGaussianBPSActivePrefixResidualBlockLaw
    (horizon : NNReal) (initial : BouncyParticleState ι) (count : ℕ) :
    Measure.map
        (fun blocks : (Fin count → NNReal) ×
            (NNReal × (ℕ → NNReal)) =>
          (blocks.1,
            standardGaussianBPSSplitResidualFromBlocks (ι := ι)
              horizon initial count blocks))
        ((((unitHazardPrefixMeasure count).restrict
            (standardGaussianBPSActivePrefixSet (ι := ι)
              horizon initial count)).prod
            (unitHazardMeasure.prod unitHazardSequenceMeasure)).restrict
          {blocks |
            standardGaussianBPSTerminalThreshold (ι := ι)
              horizon initial count blocks.1 < blocks.2.1}) =
      unitHazardPrefixFreshJointKernel
          (standardGaussianBPSTerminalThreshold (ι := ι)
            horizon initial count) ∘ₘ
        ((unitHazardPrefixMeasure count).restrict
          (standardGaussianBPSActivePrefixSet (ι := ι)
            horizon initial count)) := by
  let threshold := standardGaussianBPSTerminalThreshold (ι := ι)
    horizon initial count
  let active := standardGaussianBPSActivePrefixSet (ι := ι)
    horizon initial count
  have hsource := unitHazardPrefixResidualJointKernel_comp_eq_map_restrict
    (unitHazardPrefixMeasure count) active threshold
      (measurable_standardGaussianBPSTerminalThreshold horizon initial count)
  have hfresh := unitHazardPrefixResidualJointComp_eq_fresh
    (unitHazardPrefixMeasure count) active threshold
      (measurable_standardGaussianBPSTerminalThreshold horizon initial count)
  calc
    _ = unitHazardPrefixResidualJointKernel threshold ∘ₘ
        ((unitHazardPrefixMeasure count).restrict active) := by
      simpa [threshold, active,
        standardGaussianBPSSplitResidualFromBlocks] using hsource
    _ = _ := hfresh

/-- Prefix together with the residual stream produced by splitting on a fixed
completion stratum. -/
noncomputable def standardGaussianBPSSplitPrefixStream
    (horizon : NNReal) (initial : BouncyParticleState ι) (count : ℕ)
    (hazards : ℕ → NNReal) : (Fin count → NNReal) × (ℕ → NNReal) :=
  (fun index => hazards index,
    standardGaussianBPSSplitResidualStream (ι := ι)
      horizon initial count hazards)

theorem measurable_standardGaussianBPSSplitPrefixStream
    (horizon : NNReal) (initial : BouncyParticleState ι) (count : ℕ) :
    Measurable (standardGaussianBPSSplitPrefixStream
      (ι := ι) horizon initial count) := by
  unfold standardGaussianBPSSplitPrefixStream
  apply Measurable.prodMk
  · exact measurable_pi_lambda _ fun index =>
      (show Measurable (fun hazards : ℕ → NNReal => hazards index) from
        measurable_pi_apply (index : ℕ))
  · exact measurable_standardGaussianBPSSplitResidualStream
      horizon initial count

/-- The original iid stream restricted to one genuine completion stratum,
mapped to finite prefix plus residual stream, has exactly the integrated fresh
block law. -/
theorem standardGaussianBPSSplitPrefixStream_stratumLaw
    (horizon : NNReal) (initial : BouncyParticleState ι)
    (hvelocity : initial.2 ≠ 0) (count : ℕ) :
    Measure.map
        (standardGaussianBPSSplitPrefixStream (ι := ι)
          horizon initial count)
        (unitHazardSequenceMeasure.restrict
          ((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
            |>.genuineCompletionStratum (standardGaussianBPSJump (ι := ι))
              horizon initial (count + 1))) =
      unitHazardPrefixFreshJointKernel
          (standardGaussianBPSTerminalThreshold (ι := ι)
            horizon initial count) ∘ₘ
        ((unitHazardPrefixMeasure count).restrict
          (standardGaussianBPSActivePrefixSet (ι := ι)
            horizon initial count)) := by
  let factor := unitHazardPrefixHeadTail count
  let active := standardGaussianBPSActivePrefixSet (ι := ι)
    horizon initial count
  let threshold := standardGaussianBPSTerminalThreshold (ι := ι)
    horizon initial count
  let blockEvent : Set ((Fin count → NNReal) ×
      (NNReal × (ℕ → NNReal))) :=
    {blocks | blocks.1 ∈ active ∧ threshold blocks.1 < blocks.2.1}
  let transform : ((Fin count → NNReal) ×
      (NNReal × (ℕ → NNReal))) →
      ((Fin count → NNReal) × (ℕ → NNReal)) := fun blocks =>
    (blocks.1, standardGaussianBPSSplitResidualFromBlocks (ι := ι)
      horizon initial count blocks)
  have hfactor : Measurable factor := measurable_unitHazardPrefixHeadTail count
  have htransform : Measurable transform := by
    unfold transform
    exact measurable_fst.prodMk
      (measurable_standardGaussianBPSSplitResidualFromBlocks
        horizon initial count)
  have hblockEvent : MeasurableSet blockEvent := by
    unfold blockEvent
    exact (measurableSet_standardGaussianBPSActivePrefixSet
      horizon initial count).preimage measurable_fst |>.inter
        (measurableSet_lt
          (measurable_standardGaussianBPSTerminalThreshold
            horizon initial count |>.comp measurable_fst |>.coe_nnreal_real)
          ((measurable_fst.comp measurable_snd).coe_nnreal_real))
  have hsets :
      ((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
        |>.genuineCompletionStratum (standardGaussianBPSJump (ι := ι))
          horizon initial (count + 1)) =ᵐ[unitHazardSequenceMeasure]
        factor ⁻¹' blockEvent := by
    filter_upwards [standardGaussianBPS_mem_stratum_iff_prefix_survival_ae
      (ι := ι) horizon initial hvelocity count] with hazards hhazards
    apply propext
    change (hazards ∈
      ((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
        |>.genuineCompletionStratum (standardGaussianBPSJump (ι := ι))
          horizon initial (count + 1)) ↔
      (fun index : Fin count => hazards index) ∈ active ∧
        threshold (fun index : Fin count => hazards index) < hazards count)
    exact hhazards
  rw [Measure.restrict_congr_set hsets]
  have hcomposition :
      standardGaussianBPSSplitPrefixStream (ι := ι)
          horizon initial count = transform ∘ factor := by
    funext hazards
    apply Prod.ext
    · rfl
    · exact standardGaussianBPSSplitResidualStream_eq_fromBlocks
        horizon initial count hazards
  rw [hcomposition, ← Measure.map_map htransform hfactor]
  rw [map_restrict_preimage_eq_restrict_map
    unitHazardSequenceMeasure factor hfactor blockEvent hblockEvent]
  rw [unitHazardSequenceMeasure_map_prefixHeadTail]
  have hactive : MeasurableSet active :=
    measurableSet_standardGaussianBPSActivePrefixSet horizon initial count
  let survival : Set ((Fin count → NNReal) ×
      (NNReal × (ℕ → NNReal))) :=
    {blocks | threshold blocks.1 < blocks.2.1}
  have hsurvival : MeasurableSet survival :=
    measurableSet_lt
      (measurable_standardGaussianBPSTerminalThreshold horizon initial count
        |>.comp measurable_fst)
      (measurable_fst.comp measurable_snd)
  have hmeasure :
      ((unitHazardPrefixMeasure count).prod
          (unitHazardMeasure.prod unitHazardSequenceMeasure)).restrict
          blockEvent =
        (((unitHazardPrefixMeasure count).restrict active).prod
          (unitHazardMeasure.prod unitHazardSequenceMeasure)).restrict
            survival := by
    rw [Measure.restrict_prod_eq_prod_univ,
      Measure.restrict_restrict hsurvival]
    congr 2
    ext blocks
    simp [blockEvent, survival, and_comm]
  rw [hmeasure]
  exact standardGaussianBPSActivePrefixResidualBlockLaw
    horizon initial count

/-- Product form of the stratum law: its survival-weighted finite-prefix
measure is independent of a fresh iid residual stream. -/
theorem standardGaussianBPSSplitPrefixStream_stratumLaw_eq_prod
    (horizon : NNReal) (initial : BouncyParticleState ι)
    (hvelocity : initial.2 ≠ 0) (count : ℕ) :
    Measure.map
        (standardGaussianBPSSplitPrefixStream (ι := ι)
          horizon initial count)
        (unitHazardSequenceMeasure.restrict
          ((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
            |>.genuineCompletionStratum (standardGaussianBPSJump (ι := ι))
              horizon initial (count + 1))) =
      (((unitHazardPrefixMeasure count).restrict
          (standardGaussianBPSActivePrefixSet (ι := ι)
            horizon initial count)).withDensity
        (fun marks =>
          (Real.toNNReal (Real.exp
            (-(standardGaussianBPSTerminalThreshold (ι := ι)
              horizon initial count marks : ℝ))) : ENNReal))).prod
        unitHazardSequenceMeasure := by
  rw [standardGaussianBPSSplitPrefixStream_stratumLaw
    horizon initial hvelocity count]
  exact unitHazardPrefixFreshJointKernel_comp_eq_prod
    ((unitHazardPrefixMeasure count).restrict
      (standardGaussianBPSActivePrefixSet (ι := ι)
        horizon initial count))
    (standardGaussianBPSTerminalThreshold (ι := ι)
      horizon initial count)
    (measurable_standardGaussianBPSTerminalThreshold horizon initial count)

/-- Endpoint determined solely by an active finite prefix: flow through the
remaining part of its terminal no-event flight. -/
noncomputable def standardGaussianBPSPrefixEndpoint
    (horizon : NNReal) (initial : BouncyParticleState ι) (count : ℕ)
    (marks : Fin count → NNReal) : BouncyParticleState ι :=
  let before :=
    (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
      |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
        ((horizon, initial), finiteHazardPrefixExtension count marks)
  bouncyParticleFlow before.1 before.2

set_option maxHeartbeats 800000 in
theorem measurable_standardGaussianBPSPrefixEndpoint
    (horizon : NNReal) (initial : BouncyParticleState ι) (count : ℕ) :
    Measurable (standardGaussianBPSPrefixEndpoint
      (ι := ι) horizon initial count) := by
  unfold standardGaussianBPSPrefixEndpoint
  let before : (Fin count → NNReal) → NNReal × BouncyParticleState ι :=
    fun marks =>
      (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
        |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
          ((horizon, initial), finiteHazardPrefixExtension count marks)
  have hbefore : Measurable before :=
    ((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
      |>.measurable_replayPrefix measurable_standardGaussianBPSJump count).comp
        ((measurable_const.prodMk measurable_const).prodMk
          (measurable_finiteHazardPrefixExtension count))
  exact bouncyParticleJointlyMeasurableSemiflow.jointly_measurable_flow.comp
    (hbefore.fst.prodMk hbefore.snd)

theorem standardGaussianBPSPrefixEndpoint_apply
    (horizon : NNReal) (initial : BouncyParticleState ι) (count : ℕ)
    (hazards : ℕ → NNReal) :
    standardGaussianBPSPrefixEndpoint (ι := ι) horizon initial count
        (fun index : Fin count => hazards index) =
      bouncyParticleFlow
        (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
          |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
            ((horizon, initial), hazards)).1)
        (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
          |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
            ((horizon, initial), hazards)).2) := by
  unfold standardGaussianBPSPrefixEndpoint
  rw [(standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
    |>.replayPrefix_eq_executeHazards]
  rw [(standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
    |>.replayPrefix_eq_executeHazards]
  simp [hazardPrefix, finiteHazardPrefixExtension]

/-- Completed first-interval endpoint paired with the stratum-specific
residual hazard stream. -/
noncomputable def standardGaussianBPSCompletedSplitPair
    (horizon : NNReal) (initial : BouncyParticleState ι) (count : ℕ)
    (hazards : ℕ → NNReal) : BouncyParticleState ι × (ℕ → NNReal) :=
  ((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
      |>.completedReplayEndpoint (standardGaussianBPSJump (ι := ι))
        ((horizon, initial), hazards),
    standardGaussianBPSSplitResidualStream (ι := ι)
      horizon initial count hazards)

theorem measurable_standardGaussianBPSCompletedSplitPair
    (horizon : NNReal) (initial : BouncyParticleState ι) (count : ℕ) :
    Measurable (standardGaussianBPSCompletedSplitPair
      (ι := ι) horizon initial count) := by
  unfold standardGaussianBPSCompletedSplitPair
  exact (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
    |>.measurable_completedReplayEndpoint measurable_standardGaussianBPSJump)
      |>.comp ((measurable_const.prodMk measurable_const).prodMk
        measurable_id)).prodMk
    (measurable_standardGaussianBPSSplitResidualStream horizon initial count)

/-- On each completion stratum, the completed endpoint is independent of the
fresh residual iid stream.  Its first marginal is the survival-weighted prefix
law pushed through the deterministic prefix endpoint. -/
theorem standardGaussianBPSCompletedSplitPair_stratumLaw_eq_prod
    (horizon : NNReal) (initial : BouncyParticleState ι)
    (hvelocity : initial.2 ≠ 0) (count : ℕ) :
    Measure.map
        (standardGaussianBPSCompletedSplitPair (ι := ι)
          horizon initial count)
        (unitHazardSequenceMeasure.restrict
          ((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
            |>.genuineCompletionStratum (standardGaussianBPSJump (ι := ι))
              horizon initial (count + 1))) =
      (Measure.map
        (standardGaussianBPSPrefixEndpoint (ι := ι)
          horizon initial count)
        (((unitHazardPrefixMeasure count).restrict
          (standardGaussianBPSActivePrefixSet (ι := ι)
            horizon initial count)).withDensity
        (fun marks =>
          (Real.toNNReal (Real.exp
            (-(standardGaussianBPSTerminalThreshold (ι := ι)
              horizon initial count marks : ℝ))) : ENNReal)))).prod
        unitHazardSequenceMeasure := by
  let stratum :=
    (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
      |>.genuineCompletionStratum (standardGaussianBPSJump (ι := ι))
        horizon initial (count + 1)
  let prefixLaw :=
    ((unitHazardPrefixMeasure count).restrict
      (standardGaussianBPSActivePrefixSet (ι := ι)
        horizon initial count)).withDensity
      (fun marks =>
        (Real.toNNReal (Real.exp
          (-(standardGaussianBPSTerminalThreshold (ι := ι)
            horizon initial count marks : ℝ))) : ENNReal))
  let mapPair := Prod.map
    (standardGaussianBPSPrefixEndpoint (ι := ι) horizon initial count)
    (id : (ℕ → NNReal) → ℕ → NNReal)
  have hmapPair : Measurable mapPair :=
    (measurable_standardGaussianBPSPrefixEndpoint horizon initial count).prodMap
      measurable_id
  have hstratum : MeasurableSet stratum :=
    (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
      |>.measurableSet_genuineCompletionStratum
        measurable_standardGaussianBPSJump horizon initial (count + 1)
  have heq :
      mapPair ∘ standardGaussianBPSSplitPrefixStream (ι := ι)
          horizon initial count =ᵐ[unitHazardSequenceMeasure.restrict stratum]
        standardGaussianBPSCompletedSplitPair (ι := ι)
          horizon initial count := by
    change ∀ᵐ hazards ∂unitHazardSequenceMeasure.restrict stratum,
      (mapPair ∘ standardGaussianBPSSplitPrefixStream (ι := ι)
        horizon initial count) hazards =
        standardGaussianBPSCompletedSplitPair (ι := ι)
          horizon initial count hazards
    rw [ae_restrict_iff' hstratum]
    filter_upwards [standardGaussianBPS_completedEndpoint_eq_flow_on_stratum_ae
      (ι := ι) horizon initial hvelocity count] with hazards hendpoint hmem
    apply Prod.ext
    · exact (standardGaussianBPSPrefixEndpoint_apply
        horizon initial count hazards).trans (hendpoint hmem).symm
    · rfl
  calc
    Measure.map
        (standardGaussianBPSCompletedSplitPair (ι := ι)
          horizon initial count)
        (unitHazardSequenceMeasure.restrict stratum) =
      Measure.map
        (mapPair ∘ standardGaussianBPSSplitPrefixStream (ι := ι)
          horizon initial count)
        (unitHazardSequenceMeasure.restrict stratum) :=
      (Measure.map_congr heq).symm
    _ = Measure.map mapPair
        (Measure.map
          (standardGaussianBPSSplitPrefixStream (ι := ι)
            horizon initial count)
          (unitHazardSequenceMeasure.restrict stratum)) := by
      rw [Measure.map_map hmapPair
        (measurable_standardGaussianBPSSplitPrefixStream
          horizon initial count)]
    _ = Measure.map mapPair
        (prefixLaw.prod unitHazardSequenceMeasure) := by
      rw [standardGaussianBPSSplitPrefixStream_stratumLaw_eq_prod
        horizon initial hvelocity count]
    _ = (Measure.map
          (standardGaussianBPSPrefixEndpoint (ι := ι)
            horizon initial count) prefixLaw).prod
          unitHazardSequenceMeasure := by
      rw [← Measure.map_prod_map prefixLaw unitHazardSequenceMeasure
        (measurable_standardGaussianBPSPrefixEndpoint horizon initial count)
        (measurable_id : Measurable (id : (ℕ → NNReal) → ℕ → NNReal)),
        Measure.map_id]
    _ = _ := rfl

/-- First marginal appearing in the completed-endpoint/fresh-residual product
law on the genuine `(count+1)` completion stratum. -/
noncomputable def standardGaussianBPSCompletionEndpointStratumMeasure
    (horizon : NNReal) (initial : BouncyParticleState ι) (count : ℕ) :
    Measure (BouncyParticleState ι) :=
  Measure.map
    (standardGaussianBPSPrefixEndpoint (ι := ι) horizon initial count)
    (((unitHazardPrefixMeasure count).restrict
      (standardGaussianBPSActivePrefixSet (ι := ι)
        horizon initial count)).withDensity
      (fun marks =>
        (Real.toNNReal (Real.exp
          (-(standardGaussianBPSTerminalThreshold (ι := ι)
            horizon initial count marks : ℝ))) : ENNReal)))

/-- Summing the countwise completion laws preserves the fresh iid residual
factor: the completed endpoint mixture is globally independent of that fresh
stream at the level of the successor-stratum decomposition. -/
theorem standardGaussianBPSCompletedSplitPair_sum_stratumLaw_eq_prod
    (horizon : NNReal) (initial : BouncyParticleState ι)
    (hvelocity : initial.2 ≠ 0) :
    Measure.sum (fun count => Measure.map
      (standardGaussianBPSCompletedSplitPair (ι := ι)
        horizon initial count)
      (unitHazardSequenceMeasure.restrict
        ((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
          |>.genuineCompletionStratum (standardGaussianBPSJump (ι := ι))
            horizon initial (count + 1)))) =
      (Measure.sum (fun count =>
        standardGaussianBPSCompletionEndpointStratumMeasure
          (ι := ι) horizon initial count)).prod
        unitHazardSequenceMeasure := by
  rw [Measure.prod_sum_left]
  congr 1
  funext count
  simpa [standardGaussianBPSCompletionEndpointStratumMeasure] using
    standardGaussianBPSCompletedSplitPair_stratumLaw_eq_prod
      (ι := ι) horizon initial hvelocity count

/-- On a genuine no-event terminal branch, the residual stream's head clock
is exactly the unused portion of the original terminal clock. -/
theorem standardGaussianBPSSplitResidualStream_waitingTime
    (horizon : NNReal) (initial : BouncyParticleState ι)
    (hvelocity : initial.2 ≠ 0) (count : ℕ) (hazards : ℕ → NNReal)
    (hmem : hazards ∈
      ((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
        |>.genuineCompletionStratum (standardGaussianBPSJump (ι := ι))
          horizon initial (count + 1)))
    (hpositive : 0 < hazards count)
    (hnoevent : ¬(0 <
          (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
            |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
              ((horizon, initial), hazards)).1) ∧
        (standardGaussianBPSPartialInverseHazardData (ι := ι)).active
            (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
              |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
                ((horizon, initial), hazards)).2)
            (hazards count) = true ∧
        gaussianBPSWaitingTime
            (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
              |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
                ((horizon, initial), hazards)).2)
            (hazards count) ≤
          (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
            |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
              ((horizon, initial), hazards)).1))) :
    let before :=
      (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
        |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
          ((horizon, initial), hazards)
    gaussianBPSWaitingTime (bouncyParticleFlow before.1 before.2)
        (standardGaussianBPSSplitResidualStream (ι := ι)
          horizon initial count hazards 0) =
      gaussianBPSWaitingTime before.2 (hazards count) - before.1 := by
  dsimp only
  let before :=
    (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
      |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
        ((horizon, initial), hazards)
  have hremainingNe : before.1 ≠ 0 :=
    (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
      |>.replayPrefix_fst_ne_zero_on_succ_stratum
        (standardGaussianBPSJump (ι := ι)) horizon initial count hmem
  have hremaining : 0 < before.1 := (pos_iff_ne_zero).2 hremainingNe
  have hbeforeVelocity : before.2.2 ≠ 0 :=
    standardGaussianBPS_replayPrefix_velocity_ne_zero count
      ((horizon, initial), hazards) hvelocity
  have hactive :
      (standardGaussianBPSPartialInverseHazardData (ι := ι)).active
        before.2 (hazards count) = true := by
    simp [standardGaussianBPSPartialInverseHazardData,
      hpositive.ne', hbeforeVelocity]
  have hstrict : before.1 < gaussianBPSWaitingTime before.2
      (hazards count) := by
    have hnle : ¬gaussianBPSWaitingTime before.2 (hazards count) ≤ before.1 :=
      fun hle => hnoevent ⟨hremaining, hactive, hle⟩
    exact lt_of_not_ge hnle
  change gaussianBPSWaitingTime (bouncyParticleFlow before.1 before.2)
      (gaussianBPSResidualHazard before.2 (hazards count) before.1) = _
  exact gaussianBPSWaitingTime_residualHazard before.2 hbeforeVelocity
    (hazards count) hpositive before.1 hstrict

/-- The event and reflection reached from the residual stream are likewise
identical to those reached by the original unsplit terminal mark. -/
theorem standardGaussianBPSSplitResidualStream_jump
    (horizon : NNReal) (initial : BouncyParticleState ι)
    (hvelocity : initial.2 ≠ 0) (count : ℕ) (hazards : ℕ → NNReal)
    (hmem : hazards ∈
      ((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
        |>.genuineCompletionStratum (standardGaussianBPSJump (ι := ι))
          horizon initial (count + 1)))
    (hpositive : 0 < hazards count)
    (hnoevent : ¬(0 <
          (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
            |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
              ((horizon, initial), hazards)).1) ∧
        (standardGaussianBPSPartialInverseHazardData (ι := ι)).active
            (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
              |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
                ((horizon, initial), hazards)).2)
            (hazards count) = true ∧
        gaussianBPSWaitingTime
            (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
              |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
                ((horizon, initial), hazards)).2)
            (hazards count) ≤
          (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
            |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
              ((horizon, initial), hazards)).1))) :
    let before :=
      (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
        |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
          ((horizon, initial), hazards)
    standardGaussianBPSJump
        (bouncyParticleFlow
          (gaussianBPSWaitingTime (bouncyParticleFlow before.1 before.2)
            (standardGaussianBPSSplitResidualStream (ι := ι)
              horizon initial count hazards 0))
          (bouncyParticleFlow before.1 before.2)) =
      standardGaussianBPSJump
        (bouncyParticleFlow
          (gaussianBPSWaitingTime before.2 (hazards count)) before.2) := by
  dsimp only
  let before :=
    (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
      |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
        ((horizon, initial), hazards)
  have hremainingNe : before.1 ≠ 0 :=
    (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
      |>.replayPrefix_fst_ne_zero_on_succ_stratum
        (standardGaussianBPSJump (ι := ι)) horizon initial count hmem
  have hremaining : 0 < before.1 := (pos_iff_ne_zero).2 hremainingNe
  have hbeforeVelocity : before.2.2 ≠ 0 :=
    standardGaussianBPS_replayPrefix_velocity_ne_zero count
      ((horizon, initial), hazards) hvelocity
  have hactive :
      (standardGaussianBPSPartialInverseHazardData (ι := ι)).active
        before.2 (hazards count) = true := by
    simp [standardGaussianBPSPartialInverseHazardData,
      hpositive.ne', hbeforeVelocity]
  have hstrict : before.1 < gaussianBPSWaitingTime before.2
      (hazards count) := by
    have hnle : ¬gaussianBPSWaitingTime before.2 (hazards count) ≤ before.1 :=
      fun hle => hnoevent ⟨hremaining, hactive, hle⟩
    exact lt_of_not_ge hnle
  change standardGaussianBPSJump
      (bouncyParticleFlow
        (gaussianBPSWaitingTime (bouncyParticleFlow before.1 before.2)
          (gaussianBPSResidualHazard before.2 (hazards count) before.1))
        (bouncyParticleFlow before.1 before.2)) = _
  exact gaussianBPSJump_residualHazard before.2 hbeforeVelocity
    (hazards count) hpositive before.1 hstrict

/-- Extending the original terminal flight by `extra` and applying its
terminal mark is exactly the same capped candidate as restarting after the
short horizon with the residual mark. -/
theorem standardGaussianBPSSplitResidualStream_cappedStepUpdate
    (horizon extra : NNReal) (initial : BouncyParticleState ι)
    (hvelocity : initial.2 ≠ 0) (count : ℕ) (hazards : ℕ → NNReal)
    (hmem : hazards ∈
      ((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
        |>.genuineCompletionStratum (standardGaussianBPSJump (ι := ι))
          horizon initial (count + 1)))
    (hpositive : 0 < hazards count)
    (hnoevent : ¬(0 <
          (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
            |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
              ((horizon, initial), hazards)).1) ∧
        (standardGaussianBPSPartialInverseHazardData (ι := ι)).active
            (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
              |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
                ((horizon, initial), hazards)).2)
            (hazards count) = true ∧
        gaussianBPSWaitingTime
            (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
              |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
                ((horizon, initial), hazards)).2)
            (hazards count) ≤
          (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
            |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
              ((horizon, initial), hazards)).1))) :
    let before :=
      (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
        |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
          ((horizon, initial), hazards)
    PartialInverseHazardClock.cappedStepUpdate
        (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
        (standardGaussianBPSJump (ι := ι))
        ((extra, bouncyParticleFlow before.1 before.2),
          standardGaussianBPSSplitResidualStream (ι := ι)
            horizon initial count hazards 0) =
      PartialInverseHazardClock.cappedStepUpdate
        (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
        (standardGaussianBPSJump (ι := ι))
        ((before.1 + extra, before.2), hazards count) := by
  dsimp only
  let clock :=
    (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
  let jump := standardGaussianBPSJump (ι := ι)
  let before := clock.replayPrefix jump count ((horizon, initial), hazards)
  let residual := standardGaussianBPSSplitResidualStream (ι := ι)
    horizon initial count hazards 0
  let wait := gaussianBPSWaitingTime before.2 (hazards count)
  let residualWait := gaussianBPSWaitingTime
    (bouncyParticleFlow before.1 before.2) residual
  have hremaining : 0 < before.1 := (pos_iff_ne_zero).2 <|
    clock.replayPrefix_fst_ne_zero_on_succ_stratum jump
      horizon initial count hmem
  have hbeforeVelocity : before.2.2 ≠ 0 :=
    standardGaussianBPS_replayPrefix_velocity_ne_zero count
      ((horizon, initial), hazards) hvelocity
  have hactive : clock.active before.2 (hazards count) = true := by
    change (standardGaussianBPSPartialInverseHazardData (ι := ι)).active
      before.2 (hazards count) = true
    simp [standardGaussianBPSPartialInverseHazardData,
      hpositive.ne', hbeforeVelocity]
  have hstrict : before.1 < wait := by
    have hnle : ¬wait ≤ before.1 :=
      fun hle => hnoevent ⟨hremaining, hactive, hle⟩
    exact lt_of_not_ge hnle
  have hresidualPos : 0 < residual := by
    let accumulated := ∫ elapsed in (0 : ℝ)..(before.1 : ℝ),
      standardGaussianBouncyParticleBounceData.stateRate
        (bouncyParticleFlow (Real.toNNReal elapsed) before.2)
    have haccumulatedNonneg : 0 ≤ accumulated :=
      standardGaussianBPS_accumulated_nonneg before.2 hbeforeVelocity before.1
    have haccumulatedLt : accumulated < (hazards count : ℝ) :=
      standardGaussianBPS_accumulated_lt_hazard_of_lt_waitingTime
        before.2 hbeforeVelocity (hazards count) hpositive before.1 hstrict
    have hconsumedLt : Real.toNNReal accumulated < hazards count := by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ haccumulatedNonneg]
      exact haccumulatedLt
    change 0 < hazards count - Real.toNNReal accumulated
    exact tsub_pos_iff_lt.mpr hconsumedLt
  have hactiveResidual :
      clock.active (bouncyParticleFlow before.1 before.2) residual = true := by
    change (standardGaussianBPSPartialInverseHazardData (ι := ι)).active
      (bouncyParticleFlow before.1 before.2) residual = true
    simp [standardGaussianBPSPartialInverseHazardData,
      hresidualPos.ne', hbeforeVelocity]
  have hwait : residualWait = wait - before.1 := by
    exact standardGaussianBPSSplitResidualStream_waitingTime
      horizon initial hvelocity count hazards hmem hpositive hnoevent
  have hjump : jump
      (bouncyParticleFlow residualWait
        (bouncyParticleFlow before.1 before.2)) =
      jump (bouncyParticleFlow wait before.2) := by
    exact standardGaussianBPSSplitResidualStream_jump
      horizon initial hvelocity count hazards hmem hpositive hnoevent
  by_cases hevent : residualWait ≤ extra
  · have hextra : 0 < extra := lt_of_lt_of_le
      (by rw [hwait]; exact tsub_pos_iff_lt.mpr hstrict) hevent
    have horiginalEvent : wait ≤ before.1 + extra := by
      rw [← tsub_le_iff_left, ← hwait]
      exact hevent
    rw [clock.cappedStepUpdate_of_event jump hextra hactiveResidual hevent,
      clock.cappedStepUpdate_of_event jump
        (lt_of_lt_of_le hremaining (self_le_add_right before.1 extra))
        hactive horiginalEvent]
    apply Prod.ext
    · change extra - residualWait = before.1 + extra - wait
      apply NNReal.eq
      rw [NNReal.coe_sub hevent, NNReal.coe_sub horiginalEvent, hwait,
        NNReal.coe_sub hstrict.le]
      push_cast
      ring
    · exact hjump
  · have horiginalNoEvent : ¬wait ≤ before.1 + extra := by
      intro horiginalEvent
      apply hevent
      rw [hwait, tsub_le_iff_left]
      exact horiginalEvent
    rw [clock.cappedStepUpdate_of_no_event jump
        (fun h => hevent h.2.2),
      clock.cappedStepUpdate_of_no_event jump
        (fun h => horiginalNoEvent h.2.2)]
    apply Prod.ext
    · rfl
    · exact (congrFun ((bouncyParticleSemiflow (ι := ι)).flow_add
        before.1 extra) before.2).symm

/-- On a genuine short-horizon completion stratum, direct execution for the
summed horizon agrees pathwise with restart from the short-horizon endpoint
using the residual terminal mark and untouched suffix, whenever the direct
summed-horizon stream completes. -/
theorem standardGaussianBPS_completedReplayEndpoint_add_on_stratum
    (horizon extra : NNReal) (initial : BouncyParticleState ι)
    (hvelocity : initial.2 ≠ 0) (count : ℕ) (hazards : ℕ → NNReal)
    (hmem : hazards ∈
      ((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
        |>.genuineCompletionStratum (standardGaussianBPSJump (ι := ι))
          horizon initial (count + 1)))
    (hpositive : 0 < hazards count)
    (hnoevent : ¬(0 <
          (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
            |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
              ((horizon, initial), hazards)).1) ∧
        (standardGaussianBPSPartialInverseHazardData (ι := ι)).active
            (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
              |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
                ((horizon, initial), hazards)).2)
            (hazards count) = true ∧
        gaussianBPSWaitingTime
            (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
              |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
                ((horizon, initial), hazards)).2)
            (hazards count) ≤
          (((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
            |>.replayPrefix (standardGaussianBPSJump (ι := ι)) count
              ((horizon, initial), hazards)).1)))
    (hcomplete : ∃ direct,
      (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
        |>.replayFinished (standardGaussianBPSJump (ι := ι))
          ((horizon + extra, initial), hazards) direct) :
    PartialInverseHazardClock.completedReplayEndpoint
        (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
        (standardGaussianBPSJump (ι := ι))
        ((horizon + extra, initial), hazards) =
      PartialInverseHazardClock.completedReplayEndpoint
        (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
        (standardGaussianBPSJump (ι := ι))
        ((extra,
          PartialInverseHazardClock.completedReplayEndpoint
            (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
            (standardGaussianBPSJump (ι := ι))
            ((horizon, initial), hazards)),
          standardGaussianBPSSplitResidualStream (ι := ι)
            horizon initial count hazards) := by
  let clock :=
    (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
  let jump := standardGaussianBPSJump (ι := ι)
  let before := clock.replayPrefix jump count ((horizon, initial), hazards)
  let residualStream := standardGaussianBPSSplitResidualStream (ι := ι)
    horizon initial count hazards
  let suffix : ℕ → NNReal := fun index => hazards (count + index + 1)
  let originalHeadTail : NNReal × (ℕ → NNReal) := (hazards count, suffix)
  let residualHeadTail : NNReal × (ℕ → NNReal) :=
    (residualStream 0, suffix)
  have horiginalTail : (unitHazardPrefixTail count hazards).2 =
      unitHazardCons originalHeadTail := by
    funext index
    cases index with
    | zero => rfl
    | succ index => rfl
  have hresidualCons : residualStream = unitHazardCons residualHeadTail := by
    funext index
    cases index with
    | zero => rfl
    | succ index => rfl
  have hprefixAdd : clock.replayPrefix jump count
      ((horizon + extra, initial), hazards) =
        (before.1 + extra, before.2) := by
    simpa [before, Prod.map, Function.id_def] using
      clock.replayPrefix_add_horizon_on_succ_stratum
      jump horizon extra initial count hmem
  have hshortEndpoint : clock.completedReplayEndpoint jump
      ((horizon, initial), hazards) =
        bouncyParticleFlow before.1 before.2 :=
    clock.completedReplayEndpoint_eq_flow_on_succ_stratum
      jump horizon initial count hmem hnoevent
  have htailOriginal := clock.exists_replayFinished_tail_of_exists
    jump count ((horizon + extra, initial), hazards) hcomplete
  have htailOriginal' : ∃ tailCount, clock.replayFinished jump
      ((before.1 + extra, before.2),
        unitHazardCons originalHeadTail) tailCount := by
    simpa [hprefixAdd, horiginalTail] using htailOriginal
  have hremainingAdd : (before.1 + extra) ≠ 0 := by
    exact (lt_of_lt_of_le
      ((pos_iff_ne_zero).2 <| clock.replayPrefix_fst_ne_zero_on_succ_stratum
        jump horizon initial count hmem)
      (self_le_add_right before.1 extra)).ne'
  have hafterOriginal := clock.exists_replayFinished_after_head
    jump (before.1 + extra, before.2) originalHeadTail
      hremainingAdd htailOriginal'
  have hcapped : clock.cappedStepUpdate jump
      ((extra, bouncyParticleFlow before.1 before.2), residualStream 0) =
    clock.cappedStepUpdate jump
      ((before.1 + extra, before.2), hazards count) := by
    exact standardGaussianBPSSplitResidualStream_cappedStepUpdate
      horizon extra initial hvelocity count hazards hmem hpositive hnoevent
  have hafterResidual : ∃ tailCount, clock.replayFinished jump
      (clock.cappedStepUpdate jump
        ((extra, bouncyParticleFlow before.1 before.2), residualStream 0),
          suffix) tailCount := by
    simpa [originalHeadTail, residualHeadTail, hcapped] using hafterOriginal
  calc
    clock.completedReplayEndpoint jump
        ((horizon + extra, initial), hazards) =
      clock.completedReplayEndpoint jump
        (clock.replayPrefix jump count
          ((horizon + extra, initial), hazards),
          (unitHazardPrefixTail count hazards).2) :=
      clock.completedReplayEndpoint_eq_tail jump count _ htailOriginal
    _ = clock.completedReplayEndpoint jump
        ((before.1 + extra, before.2),
          unitHazardCons originalHeadTail) := by rw [hprefixAdd, horiginalTail]
    _ = clock.completedReplayEndpoint jump
        (clock.cappedStepUpdate jump
          ((before.1 + extra, before.2), originalHeadTail.1),
          originalHeadTail.2) :=
      clock.completedReplayEndpoint_cons jump
        (before.1 + extra, before.2) originalHeadTail hafterOriginal
    _ = clock.completedReplayEndpoint jump
        (clock.cappedStepUpdate jump
          ((extra, bouncyParticleFlow before.1 before.2), residualHeadTail.1),
          residualHeadTail.2) := by
      change clock.completedReplayEndpoint jump
          (clock.cappedStepUpdate jump
            ((before.1 + extra, before.2), hazards count), suffix) =
        clock.completedReplayEndpoint jump
          (clock.cappedStepUpdate jump
            ((extra, bouncyParticleFlow before.1 before.2), residualStream 0),
              suffix)
      rw [hcapped]
    _ = clock.completedReplayEndpoint jump
        ((extra, bouncyParticleFlow before.1 before.2),
          unitHazardCons residualHeadTail) :=
      (clock.completedReplayEndpoint_cons jump
        (extra, bouncyParticleFlow before.1 before.2)
          residualHeadTail hafterResidual).symm
    _ = clock.completedReplayEndpoint jump
        ((extra, clock.completedReplayEndpoint jump
          ((horizon, initial), hazards)), residualStream) := by
      rw [hshortEndpoint, hresidualCons]

/-- The Gaussian replay potential satisfies the accepted-step payment
inequality required by the generic inverse-clock nonexplosion theorem. -/
theorem standardGaussianBPSReplayPotential_step
    (remainingState : NNReal × BouncyParticleState ι) (hazard : NNReal)
    (hcondition :
      0 < remainingState.1 ∧
        standardGaussianBPSPartialInverseHazardData.clock.active
            remainingState.2 hazard = true ∧
        standardGaussianBPSPartialInverseHazardData.clock.waitingTime
            remainingState.2 hazard ≤ remainingState.1) :
    hazard + standardGaussianBPSReplayPotential
        (standardGaussianBPSPartialInverseHazardData.clock.cappedStepUpdate
          standardGaussianBPSJump (remainingState, hazard)) ≤
      standardGaussianBPSReplayPotential remainingState := by
  rcases hcondition with ⟨hremaining, hactive, hwait⟩
  have hupdate :=
    standardGaussianBPSPartialInverseHazardData.clock.cappedStepUpdate_of_event
      standardGaussianBPSJump hremaining hactive hwait
  rw [hupdate]
  let wait := standardGaussianBPSPartialInverseHazardData.waitingTime
    remainingState.2 hazard
  change wait ≤ remainingState.1 at hwait
  have hhazard : hazard ≤ wait *
      standardGaussianBPSRateEnvelope remainingState := by
    apply standardGaussianBPS_hazard_le_wait_mul_envelope
    · exact hactive
    · exact hwait
  have henvelope : standardGaussianBPSRateEnvelope
      (remainingState.1 - wait,
        standardGaussianBPSJump
          (bouncyParticleFlow wait remainingState.2)) ≤
      standardGaussianBPSRateEnvelope remainingState :=
    standardGaussianBPSRateEnvelope_after_event_le
      remainingState.1 remainingState.2 wait hwait
  unfold standardGaussianBPSReplayPotential
  dsimp only [Prod.fst, Prod.snd]
  calc
    hazard + (remainingState.1 - wait) *
        standardGaussianBPSRateEnvelope
          (remainingState.1 - wait,
            standardGaussianBPSJump
              (bouncyParticleFlow wait remainingState.2)) ≤
      wait * standardGaussianBPSRateEnvelope remainingState +
        (remainingState.1 - wait) *
          standardGaussianBPSRateEnvelope remainingState := by
            exact add_le_add hhazard
              (mul_le_mul_of_nonneg_left henvelope bot_le)
    _ = remainingState.1 *
        standardGaussianBPSRateEnvelope remainingState := by
      rw [← add_mul, add_comm, tsub_add_cancel_of_le hwait]

/-- Every still-active finite Gaussian-BPS replay prefix has bounded total
integrated hazard. -/
theorem standardGaussianBPS_hasBoundedActivePrefixHazard :
    (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
      |>.HasBoundedActivePrefixHazard (standardGaussianBPSJump (ι := ι)) :=
  (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
    |>.hasBoundedActivePrefixHazard_of_potential
      (standardGaussianBPSJump (ι := ι))
      (standardGaussianBPSReplayPotential (ι := ι))
        (standardGaussianBPSReplayPotential_step (ι := ι))

/-- Exact finite-dimensional standard-Gaussian BPS replay is nonexplosive:
at every finite horizon and from every initial state, almost every iid
unit-exponential hazard stream completes after a finite prefix. -/
theorem standardGaussianBPS_completesFiniteHorizons :
    (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
      |>.CompletesFiniteHorizons (standardGaussianBPSJump (ι := ι)) :=
  (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
    |>.completesFiniteHorizons_of_boundedActivePrefixHazard
      (standardGaussianBPSJump (ι := ι))
        (standardGaussianBPS_hasBoundedActivePrefixHazard (ι := ι))

/-- The mixture of the successor-stratum endpoint marginals is exactly the
law of the totalized completed endpoint.  This is the countable-gluing step
that turns the countwise product laws into a global first marginal. -/
theorem standardGaussianBPSCompletionEndpointStratumMeasure_sum_eq
    {horizon : NNReal} (hhorizon : 0 < horizon)
    (initial : BouncyParticleState ι) (hvelocity : initial.2 ≠ 0) :
    Measure.sum (fun count =>
      standardGaussianBPSCompletionEndpointStratumMeasure
        (ι := ι) horizon initial count) =
      Measure.map
        (fun hazards =>
          (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
            |>.completedReplayEndpoint (standardGaussianBPSJump (ι := ι))
              ((horizon, initial), hazards))
        unitHazardSequenceMeasure := by
  let clock :=
    (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
  let endpoint := fun hazards => clock.completedReplayEndpoint
    (standardGaussianBPSJump (ι := ι)) ((horizon, initial), hazards)
  let stratum := fun count => clock.genuineCompletionStratum
    (standardGaussianBPSJump (ι := ι)) horizon initial (count + 1)
  have hendpoint : Measurable endpoint :=
    (clock.measurable_completedReplayEndpoint
      measurable_standardGaussianBPSJump).comp
        ((measurable_const.prodMk measurable_const).prodMk measurable_id)
  have hpartition :
      Measure.sum (fun count =>
        unitHazardSequenceMeasure.restrict (stratum count)) =
          unitHazardSequenceMeasure := by
    exact clock.sum_restrict_genuineCompletionStratum_succ_eq
      measurable_standardGaussianBPSJump
      (standardGaussianBPS_completesFiniteHorizons (ι := ι))
      hhorizon initial
  have hpair := standardGaussianBPSCompletedSplitPair_sum_stratumLaw_eq_prod
    (ι := ι) horizon initial hvelocity
  calc
    Measure.sum (fun count =>
        standardGaussianBPSCompletionEndpointStratumMeasure
          (ι := ι) horizon initial count) =
      Measure.map Prod.fst
        ((Measure.sum (fun count =>
          standardGaussianBPSCompletionEndpointStratumMeasure
            (ι := ι) horizon initial count)).prod
          unitHazardSequenceMeasure) := by
            rw [Measure.map_fst_prod, measure_univ, one_smul]
    _ = Measure.map Prod.fst
        (Measure.sum (fun count => Measure.map
          (standardGaussianBPSCompletedSplitPair (ι := ι)
            horizon initial count)
          (unitHazardSequenceMeasure.restrict (stratum count)))) := by
            rw [hpair]
    _ = Measure.sum (fun count => Measure.map endpoint
        (unitHazardSequenceMeasure.restrict (stratum count))) := by
          rw [Measure.map_sum measurable_fst.aemeasurable]
          congr 1
          funext count
          rw [Measure.map_map measurable_fst
            (measurable_standardGaussianBPSCompletedSplitPair
              horizon initial count)]
          rfl
    _ = Measure.map endpoint
        (Measure.sum (fun count =>
          unitHazardSequenceMeasure.restrict (stratum count))) := by
            rw [Measure.map_sum hendpoint.aemeasurable]
    _ = Measure.map endpoint unitHazardSequenceMeasure := by rw [hpartition]
    _ = _ := rfl

/-- Positive-time Gaussian-BPS execution has the exact strong-Markov split
law: the endpoint at `horizon + extra` is obtained by drawing the endpoint at
`horizon`, then running for `extra` with a fresh iid hazard stream. -/
theorem standardGaussianBPS_completedReplayEndpoint_add_law
    {horizon : NNReal} (hhorizon : 0 < horizon) (extra : NNReal)
    (initial : BouncyParticleState ι) (hvelocity : initial.2 ≠ 0) :
    Measure.map
        (fun hazards =>
          (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
            |>.completedReplayEndpoint (standardGaussianBPSJump (ι := ι))
              ((horizon + extra, initial), hazards))
        unitHazardSequenceMeasure =
      Measure.map
        (fun pair : BouncyParticleState ι × (ℕ → NNReal) =>
          (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
            |>.completedReplayEndpoint (standardGaussianBPSJump (ι := ι))
              ((extra, pair.1), pair.2))
        ((Measure.map
          (fun hazards =>
            (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
              |>.completedReplayEndpoint (standardGaussianBPSJump (ι := ι))
                ((horizon, initial), hazards))
          unitHazardSequenceMeasure).prod unitHazardSequenceMeasure) := by
  let clock :=
    (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
  let jump := standardGaussianBPSJump (ι := ι)
  let direct := fun hazards => clock.completedReplayEndpoint jump
    ((horizon + extra, initial), hazards)
  let short := fun hazards => clock.completedReplayEndpoint jump
    ((horizon, initial), hazards)
  let restart := fun pair : BouncyParticleState ι × (ℕ → NNReal) =>
    clock.completedReplayEndpoint jump ((extra, pair.1), pair.2)
  let stratum := fun count =>
    clock.genuineCompletionStratum jump horizon initial (count + 1)
  have hdirect : Measurable direct :=
    (clock.measurable_completedReplayEndpoint
      measurable_standardGaussianBPSJump).comp
        ((measurable_const.prodMk measurable_const).prodMk measurable_id)
  have hrestart : Measurable restart :=
    (clock.measurable_completedReplayEndpoint
      measurable_standardGaussianBPSJump).comp
        ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hpartition : Measure.sum (fun count =>
      unitHazardSequenceMeasure.restrict (stratum count)) =
        unitHazardSequenceMeasure :=
    clock.sum_restrict_genuineCompletionStratum_succ_eq
      measurable_standardGaussianBPSJump
      (standardGaussianBPS_completesFiniteHorizons (ι := ι))
      hhorizon initial
  have hcount (count : ℕ) :
      Measure.map direct
          (unitHazardSequenceMeasure.restrict (stratum count)) =
        Measure.map restart
          (Measure.map
            (standardGaussianBPSCompletedSplitPair (ι := ι)
              horizon initial count)
            (unitHazardSequenceMeasure.restrict (stratum count))) := by
    rw [Measure.map_map hrestart
      (measurable_standardGaussianBPSCompletedSplitPair
        horizon initial count)]
    apply Measure.map_congr
    have hstratum : MeasurableSet (stratum count) :=
      clock.measurableSet_genuineCompletionStratum
        measurable_standardGaussianBPSJump horizon initial (count + 1)
    change ∀ᵐ hazards ∂unitHazardSequenceMeasure.restrict (stratum count),
      direct hazards =
        (restart ∘ standardGaussianBPSCompletedSplitPair
          (ι := ι) horizon initial count) hazards
    rw [ae_restrict_iff' hstratum]
    filter_upwards [unitHazardSequence_coordinate_pos_ae count,
      standardGaussianBPS_terminal_noEvent_ae
        (ι := ι) horizon initial hvelocity count,
      standardGaussianBPS_completesFiniteHorizons (ι := ι)
        (horizon + extra) initial] with hazards hpositive hnoevent hcomplete
    intro hmem
    apply standardGaussianBPS_completedReplayEndpoint_add_on_stratum
      horizon extra initial hvelocity count hazards hmem hpositive
        (hnoevent hmem)
    obtain ⟨directCount, terminal, hdirectCount⟩ := hcomplete
    refine ⟨directCount, ?_⟩
    unfold PartialInverseHazardClock.replayFinished
    rw [clock.replayPrefix_eq_executeHazards, hdirectCount]
  have hpair := standardGaussianBPSCompletedSplitPair_sum_stratumLaw_eq_prod
    (ι := ι) horizon initial hvelocity
  have hendpoint :=
    standardGaussianBPSCompletionEndpointStratumMeasure_sum_eq
      (ι := ι) hhorizon initial hvelocity
  calc
    Measure.map direct unitHazardSequenceMeasure =
      Measure.map direct (Measure.sum (fun count =>
        unitHazardSequenceMeasure.restrict (stratum count))) := by rw [hpartition]
    _ = Measure.sum (fun count => Measure.map direct
        (unitHazardSequenceMeasure.restrict (stratum count))) := by
          rw [Measure.map_sum hdirect.aemeasurable]
    _ = Measure.sum (fun count => Measure.map restart
        (Measure.map
          (standardGaussianBPSCompletedSplitPair (ι := ι)
            horizon initial count)
          (unitHazardSequenceMeasure.restrict (stratum count)))) := by
            congr 1
            funext count
            exact hcount count
    _ = Measure.map restart (Measure.sum (fun count => Measure.map
        (standardGaussianBPSCompletedSplitPair (ι := ι)
          horizon initial count)
        (unitHazardSequenceMeasure.restrict (stratum count)))) := by
          rw [Measure.map_sum hrestart.aemeasurable]
    _ = Measure.map restart
        ((Measure.sum (fun count =>
          standardGaussianBPSCompletionEndpointStratumMeasure
            (ι := ι) horizon initial count)).prod
          unitHazardSequenceMeasure) := by rw [hpair]
    _ = Measure.map restart
        ((Measure.map short unitHazardSequenceMeasure).prod
          unitHazardSequenceMeasure) := by rw [hendpoint]
    _ = _ := rfl

/-- Exact totalized finite-horizon kernel for finite-dimensional
standard-Gaussian BPS. The nonexplosion theorem above proves that the
totalization fallback is unused almost surely. -/
noncomputable def standardGaussianBPSHorizonKernel (horizon : NNReal) :
    Kernel (BouncyParticleState ι) (BouncyParticleState ι) :=
  (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
    |>.completedHorizonKernel (standardGaussianBPSJump (ι := ι))
      measurable_standardGaussianBPSJump horizon

instance standardGaussianBPSHorizonKernel.instIsMarkovKernel
    (horizon : NNReal) :
    IsMarkovKernel (standardGaussianBPSHorizonKernel (ι := ι) horizon) := by
  unfold standardGaussianBPSHorizonKernel
  infer_instance

@[simp] theorem standardGaussianBPSHorizonKernel_zero :
    standardGaussianBPSHorizonKernel (ι := ι) 0 = Kernel.id := by
  unfold standardGaussianBPSHorizonKernel
  exact PartialInverseHazardClock.completedHorizonKernel_zero _ _ _

/-- Pointwise positive-time semigroup law away from the inactive zero-velocity
fiber. The latter fiber is handled separately when promoting this result to a
global kernel identity. -/
theorem standardGaussianBPSHorizonKernel_comp_apply_of_pos_of_velocity_ne_zero
    {horizon : NNReal} (hhorizon : 0 < horizon) (extra : NNReal)
    (initial : BouncyParticleState ι) (hvelocity : initial.2 ≠ 0) :
    (standardGaussianBPSHorizonKernel (ι := ι) extra ∘ₖ
      standardGaussianBPSHorizonKernel (ι := ι) horizon) initial =
        standardGaussianBPSHorizonKernel (ι := ι) (horizon + extra) initial := by
  rw [Kernel.comp_apply]
  unfold standardGaussianBPSHorizonKernel
  rw [(standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
      |>.completedHorizonKernel_comp_measure
        measurable_standardGaussianBPSJump,
    (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
      |>.completedHorizonKernel_apply measurable_standardGaussianBPSJump,
    (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
      |>.completedHorizonKernel_apply measurable_standardGaussianBPSJump]
  exact (standardGaussianBPS_completedReplayEndpoint_add_law
    (ι := ι) hhorizon extra initial hvelocity).symm

/-- The completion count used by the exact Gaussian-BPS horizon kernel is a
genuine finished prefix almost surely. -/
theorem standardGaussianBPS_completionCount_finished_ae
    (horizon : NNReal) (initial : BouncyParticleState ι) :
    ∀ᵐ hazards ∂unitHazardSequenceMeasure,
      (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
        |>.replayFinished (standardGaussianBPSJump (ι := ι))
          ((horizon, initial), hazards)
          ((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
            |>.completionCount (standardGaussianBPSJump (ι := ι))
              ((horizon, initial), hazards)) :=
  (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
    |>.replayFinished_completionCount_ae
      (standardGaussianBPSJump (ι := ι))
        (standardGaussianBPS_completesFiniteHorizons (ι := ι)) horizon initial

/-- Exact first-step renewal equation for the completed finite-dimensional
Gaussian-BPS horizon kernel. -/
theorem standardGaussianBPSHorizonKernel_apply_firstStep
    (horizon : NNReal) (initial : BouncyParticleState ι) :
    standardGaussianBPSHorizonKernel (ι := ι) horizon initial =
      Measure.map
        (fun headTail =>
          (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
            |>.completedReplayEndpoint (standardGaussianBPSJump (ι := ι))
              ((standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
                |>.cappedStepUpdate (standardGaussianBPSJump (ι := ι))
                  ((horizon, initial), headTail.1), headTail.2))
        (unitHazardMeasure.prod unitHazardSequenceMeasure) := by
  unfold standardGaussianBPSHorizonKernel
  exact (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
    |>.completedHorizonKernel_apply_firstStep
      measurable_standardGaussianBPSJump
      (standardGaussianBPS_completesFiniteHorizons (ι := ι)) horizon initial

/-- Explicit first-event renewal branch for the completed Gaussian-BPS
horizon process. -/
noncomputable def standardGaussianBPSFirstEventEndpoint
    (horizon : NNReal) (initial : BouncyParticleState ι)
    (headTail : NNReal × (ℕ → NNReal)) : BouncyParticleState ι :=
  let wait := gaussianBPSWaitingTime initial headTail.1
  if 0 < horizon ∧
      (standardGaussianBPSPartialInverseHazardData (ι := ι)).active
        initial headTail.1 = true ∧ wait ≤ horizon then
    (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
      |>.completedReplayEndpoint (standardGaussianBPSJump (ι := ι))
        ((horizon - wait,
          standardGaussianBPSJump (bouncyParticleFlow wait initial)),
          headTail.2)
  else
    bouncyParticleFlow horizon initial

theorem standardGaussianBPSFirstEventEndpoint_eq_firstStep
    (horizon : NNReal) (initial : BouncyParticleState ι)
    (headTail : NNReal × (ℕ → NNReal)) :
    standardGaussianBPSFirstEventEndpoint horizon initial headTail =
      PartialInverseHazardClock.completedReplayEndpoint
        (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
        (standardGaussianBPSJump (ι := ι))
        (PartialInverseHazardClock.cappedStepUpdate
          (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
          (standardGaussianBPSJump (ι := ι))
          ((horizon, initial), headTail.1), headTail.2) := by
  unfold standardGaussianBPSFirstEventEndpoint
  by_cases hcondition : 0 < horizon ∧
      (standardGaussianBPSPartialInverseHazardData (ι := ι)).active
        initial headTail.1 = true ∧
      gaussianBPSWaitingTime initial headTail.1 ≤ horizon
  · rw [if_pos hcondition]
    rw [(standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
      |>.cappedStepUpdate_of_event (standardGaussianBPSJump (ι := ι))
        hcondition.1 hcondition.2.1 hcondition.2.2]
    rfl
  · rw [if_neg hcondition]
    rw [(standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
      |>.cappedStepUpdate_of_no_event (standardGaussianBPSJump (ι := ι))
        hcondition]
    symm
    exact (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
      |>.completedReplayEndpoint_zero
        (standardGaussianBPSJump (ι := ι))
        (bouncyParticleFlow horizon initial) headTail.2

/-- Simplified first-event branch on the full-measure positive-hazard set for
a nonzero-velocity state. -/
noncomputable def standardGaussianBPSPositiveFirstEventEndpoint
    (horizon : NNReal) (initial : BouncyParticleState ι)
    (headTail : NNReal × (ℕ → NNReal)) : BouncyParticleState ι :=
  let wait := gaussianBPSWaitingTime initial headTail.1
  if wait ≤ horizon then
    (standardGaussianBPSPartialInverseHazardData (ι := ι)).clock
      |>.completedReplayEndpoint (standardGaussianBPSJump (ι := ι))
        ((horizon - wait,
          standardGaussianBPSJump (bouncyParticleFlow wait initial)),
          headTail.2)
  else
    bouncyParticleFlow horizon initial

theorem standardGaussianBPSFirstEventEndpoint_eq_positive
    (horizon : NNReal) (initial : BouncyParticleState ι)
    (hvelocity : initial.2 ≠ 0)
    (headTail : NNReal × (ℕ → NNReal)) (hhazard : 0 < headTail.1) :
    standardGaussianBPSFirstEventEndpoint horizon initial headTail =
      standardGaussianBPSPositiveFirstEventEndpoint horizon initial headTail := by
  unfold standardGaussianBPSFirstEventEndpoint
    standardGaussianBPSPositiveFirstEventEndpoint
  have hactive :
      (standardGaussianBPSPartialInverseHazardData (ι := ι)).active
        initial headTail.1 = true := by
    simp [standardGaussianBPSPartialInverseHazardData,
      ne_of_gt hhazard, hvelocity]
  by_cases hwait : gaussianBPSWaitingTime initial headTail.1 ≤ horizon
  · have hwaitPos := gaussianBPSWaitingTime_pos initial hvelocity hhazard
    have hhorizon : 0 < horizon := hwaitPos.trans_le hwait
    rw [if_pos ⟨hhorizon, hactive, hwait⟩, if_pos hwait]
  · rw [if_neg hwait]
    have hcondition : ¬(0 < horizon ∧
        (standardGaussianBPSPartialInverseHazardData (ι := ι)).active
          initial headTail.1 = true ∧
        gaussianBPSWaitingTime initial headTail.1 ≤ horizon) := by
      aesop
    rw [if_neg hcondition]

/-- Kernel-level Gaussian-BPS renewal equation in explicit event/no-event
form. -/
theorem standardGaussianBPSHorizonKernel_apply_firstEvent
    (horizon : NNReal) (initial : BouncyParticleState ι) :
    standardGaussianBPSHorizonKernel (ι := ι) horizon initial =
      Measure.map
        (standardGaussianBPSFirstEventEndpoint (ι := ι) horizon initial)
        (unitHazardMeasure.prod unitHazardSequenceMeasure) := by
  rw [standardGaussianBPSHorizonKernel_apply_firstStep]
  apply Measure.map_congr
  filter_upwards [] with headTail
  exact (standardGaussianBPSFirstEventEndpoint_eq_firstStep
    horizon initial headTail).symm

/-- A zero-velocity Gaussian-BPS state is inactive and therefore remains
fixed for every finite horizon. -/
theorem standardGaussianBPSHorizonKernel_apply_of_velocity_eq_zero
    (horizon : NNReal) (initial : BouncyParticleState ι)
    (hvelocity : initial.2 = 0) :
    standardGaussianBPSHorizonKernel (ι := ι) horizon initial =
      Measure.dirac initial := by
  rw [standardGaussianBPSHorizonKernel_apply_firstEvent]
  calc
    Measure.map
        (standardGaussianBPSFirstEventEndpoint (ι := ι) horizon initial)
        (unitHazardMeasure.prod unitHazardSequenceMeasure) =
      Measure.map (fun _ : NNReal × (ℕ → NNReal) => initial)
        (unitHazardMeasure.prod unitHazardSequenceMeasure) := by
      apply Measure.map_congr
      have hpositive : ∀ᵐ headTail ∂
          unitHazardMeasure.prod unitHazardSequenceMeasure,
          0 < headTail.1 :=
        (Measure.quasiMeasurePreserving_fst
          (μ := unitHazardMeasure) (ν := unitHazardSequenceMeasure)).ae
            unitHazardMeasure_positive_ae
      filter_upwards [hpositive] with headTail hhazard
      unfold standardGaussianBPSFirstEventEndpoint
      have hactive :
          (standardGaussianBPSPartialInverseHazardData (ι := ι)).active
            initial headTail.1 = false := by
        simp [standardGaussianBPSPartialInverseHazardData,
          hhazard.ne', hvelocity]
      rw [if_neg (fun hcondition => by
        rw [hactive] at hcondition
        exact Bool.false_ne_true hcondition.2.1)]
      apply Prod.ext
      · funext index
        simp [bouncyParticleFlow, hvelocity]
      · rfl
    _ = Measure.dirac initial := by
      rw [MeasureTheory.Measure.map_const, measure_univ, one_smul]

/-- Exact semigroup law for the finite-dimensional standard-Gaussian BPS
horizon kernels, including zero time and the inactive zero-velocity fiber. -/
theorem standardGaussianBPSHorizonKernel_semigroup
    (horizon extra : NNReal) :
    standardGaussianBPSHorizonKernel (ι := ι) extra ∘ₖ
      standardGaussianBPSHorizonKernel (ι := ι) horizon =
        standardGaussianBPSHorizonKernel (ι := ι) (horizon + extra) := by
  ext initial event hevent
  by_cases hhorizon : horizon = 0
  · subst horizon
    simp
  have hhorizonPos : 0 < horizon := pos_iff_ne_zero.mpr hhorizon
  by_cases hvelocity : initial.2 = 0
  · rw [Kernel.comp_apply,
      standardGaussianBPSHorizonKernel_apply_of_velocity_eq_zero
        horizon initial hvelocity,
      Measure.dirac_bind
        (standardGaussianBPSHorizonKernel (ι := ι) extra).measurable,
      standardGaussianBPSHorizonKernel_apply_of_velocity_eq_zero
        extra initial hvelocity,
      standardGaussianBPSHorizonKernel_apply_of_velocity_eq_zero
        (horizon + extra) initial hvelocity]
  · rw [standardGaussianBPSHorizonKernel_comp_apply_of_pos_of_velocity_ne_zero
      (ι := ι) hhorizonPos extra initial hvelocity]

/-! ### Multidimensional Gaussian-BPS stationarity boundary -/

/-- Canonical standard-Gaussian position/velocity target for the
finite-dimensional BPS semigroup. -/
noncomputable def standardGaussianBPSTarget :
    Measure (BouncyParticleState ι) :=
  standardMomentumMeasure.prod standardMomentumMeasure

instance standardGaussianBPSTarget.instIsProbabilityMeasure :
    IsProbabilityMeasure (standardGaussianBPSTarget (ι := ι)) := by
  unfold standardGaussianBPSTarget
  infer_instance

/-- A test observable equipped with its coordinatewise position derivative
and the two exact analytic facts consumed by the weak-forward stationarity
bridge. The Gaussian integration-by-parts theorem constructs the
`generator_mean_zero` field from coordinatewise hypotheses. -/
structure StandardGaussianBPSGeneratorTest (ι : Type*) [Fintype ι] where
  observable : BouncyParticleState ι → ℝ
  coordinatePartial : Position ι → ι → Position ι → ℝ
  generator_integrable : Integrable
    (bouncyPhaseGenerator id
      (coordinateDirectionalDerivative coordinatePartial)
      (fun position velocity => observable (position, velocity)))
    (standardGaussianBPSTarget (ι := ι))
  generator_mean_zero :
    (∫ state,
      bouncyPhaseGenerator id
        (coordinateDirectionalDerivative coordinatePartial)
        (fun position velocity => observable (position, velocity)) state
      ∂standardGaussianBPSTarget (ι := ι)) = 0

namespace StandardGaussianBPSGeneratorTest

/-- Observable component of the Gaussian-BPS generator test domain. -/
def observe (test : StandardGaussianBPSGeneratorTest ι) :
    BouncyParticleState ι → ℝ :=
  test.observable

/-- Exact BPS generator on the checked coordinatewise derivative supplied by
the test. -/
noncomputable def generator (test : StandardGaussianBPSGeneratorTest ι) :
    BouncyParticleState ι → ℝ :=
  bouncyPhaseGenerator id
    (coordinateDirectionalDerivative test.coordinatePartial)
    (fun position velocity => test.observable (position, velocity))

theorem integrable_generator (test : StandardGaussianBPSGeneratorTest ι) :
    Integrable test.generator (standardGaussianBPSTarget (ι := ι)) :=
  test.generator_integrable

theorem integral_generator_eq_zero (test : StandardGaussianBPSGeneratorTest ι) :
    (∫ state, test.generator state
      ∂standardGaussianBPSTarget (ι := ι)) = 0 :=
  test.generator_mean_zero

end StandardGaussianBPSGeneratorTest

/-- Unit phase direction that varies position coordinate `i` and leaves
velocity fixed. -/
noncomputable def standardGaussianBPSPositionDirection (i : ι) :
    BouncyParticleState ι := by
  classical
  exact (Pi.single i 1, 0)

/-- Coordinate position derivative extracted from the Fréchet derivative of
a phase observable. -/
noncomputable def standardGaussianBPSCoordinatePartial
    (function : BouncyParticleState ι → ℝ)
    (position : Position ι) (i : ι) (velocity : Position ι) : ℝ :=
  fderiv ℝ function (position, velocity)
    (standardGaussianBPSPositionDirection i)

/-- The coordinatewise directional derivative assembled from these partials
is exactly the Fréchet derivative in the physical streaming direction
`(velocity, 0)`. -/
theorem coordinateDirectionalDerivative_standardGaussianBPSCoordinatePartial
    (function : BouncyParticleState ι → ℝ)
    (position velocity : Position ι) :
    coordinateDirectionalDerivative
        (standardGaussianBPSCoordinatePartial function) position velocity =
      fderiv ℝ function (position, velocity) (velocity, 0) := by
  classical
  have hdecomp : (velocity, (0 : Position ι)) =
      ∑ i, velocity i • standardGaussianBPSPositionDirection i := by
    apply Prod.ext
    · funext coordinate
      simp only [Prod.fst_sum, standardGaussianBPSPositionDirection,
        Prod.smul_mk, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
      rw [Finset.sum_eq_single coordinate]
      · simp
      · intro other _ hne
        simp [hne]
      · simp
    · simp [Prod.snd_sum, standardGaussianBPSPositionDirection,
        Prod.smul_mk]
  unfold coordinateDirectionalDerivative
    standardGaussianBPSCoordinatePartial
  rw [hdecomp, map_sum]
  simp [smul_eq_mul]

/-- Concrete analytic certificate for one smooth phase observable. Its fields
are exactly the coordinatewise Gaussian-Stein and integrability premises of
`integral_standardGaussian_bouncyPhaseGenerator_of_coordinatewise_eq_zero`. -/
structure StandardGaussianBPSSmoothObservableCertificate
    (function : BouncyParticleState ι → ℝ) where
  coordinatePartial : Position ι → ι → Position ι → ℝ
  partial_velocity : ∀ position i, Integrable
    (fun velocity => velocity i * coordinatePartial position i velocity)
    standardMomentumMeasure
  partial_position : ∀ i, Integrable (fun position =>
    ∫ velocity, velocity i * coordinatePartial position i velocity
      ∂standardMomentumMeasure) standardMomentumMeasure
  position_velocity : ∀ position i, Integrable
    (fun velocity => velocity i * position i * function (position, velocity))
    standardMomentumMeasure
  position_position : ∀ i, Integrable (fun position =>
    ∫ velocity, velocity i * position i * function (position, velocity)
      ∂standardMomentumMeasure) standardMomentumMeasure
  incoming : ∀ position, Integrable (fun velocity =>
    bouncyRate position velocity *
      function (position, bouncyReflection position velocity))
    standardMomentumMeasure
  outgoing : ∀ position, Integrable (fun velocity =>
    bouncyRate position velocity * function (position, velocity))
    standardMomentumMeasure
  reflected : ∀ position, Integrable (fun velocity =>
    bouncyRate position (bouncyReflection position velocity) *
      function (position, velocity)) standardMomentumMeasure
  phase : Integrable
    (bouncyPhaseGenerator id
      (coordinateDirectionalDerivative coordinatePartial)
      (fun position velocity => function (position, velocity)))
    (standardMomentumMeasure.prod standardMomentumMeasure)
  coordinate_stein : ∀ i,
    (∫ position, ∫ velocity,
      velocity i * coordinatePartial position i velocity
        ∂standardMomentumMeasure ∂standardMomentumMeasure) =
      ∫ position, ∫ velocity,
        velocity i * position i * function (position, velocity)
          ∂standardMomentumMeasure ∂standardMomentumMeasure

/-- Package one fully discharged smooth-observable certificate as an element
of the generator test domain. -/
noncomputable def StandardGaussianBPSSmoothObservableCertificate.toGeneratorTest
    {function : BouncyParticleState ι → ℝ}
    (certificate : StandardGaussianBPSSmoothObservableCertificate
      (ι := ι) function) :
    StandardGaussianBPSGeneratorTest ι where
  observable := function
  coordinatePartial := certificate.coordinatePartial
  generator_integrable := by
    simpa [standardGaussianBPSTarget] using certificate.phase
  generator_mean_zero := by
    unfold standardGaussianBPSTarget
    exact integral_standardGaussian_bouncyPhaseGenerator_of_coordinatewise_eq_zero
      certificate.coordinatePartial
      (fun position velocity => function (position, velocity))
      certificate.partial_velocity certificate.partial_position
      certificate.position_velocity certificate.position_position
      certificate.incoming certificate.outgoing certificate.reflected
      certificate.phase certificate.coordinate_stein

/-- Target-started weak-forward uniqueness for the constructed exact
Gaussian-BPS semigroup on its checked generator test domain. This is the
remaining process-level analytic obligation between generator cancellation
and target stationarity. -/
abbrev StandardGaussianBPSTargetWeakForwardUniqueness :=
  CompactTestTargetWeakForwardUniqueness
    (standardGaussianBPSHorizonKernel (ι := ι))
    StandardGaussianBPSGeneratorTest.observe
    StandardGaussianBPSGeneratorTest.generator
    (standardGaussianBPSTarget (ι := ι))

/-- Scalar-expectation half of target-started weak-forward uniqueness. -/
abbrev StandardGaussianBPSTargetWeakExpectationUniqueness :=
  CompactTestTargetWeakExpectationUniqueness
    (standardGaussianBPSHorizonKernel (ι := ι))
    StandardGaussianBPSGeneratorTest.observe
    StandardGaussianBPSGeneratorTest.generator
    (standardGaussianBPSTarget (ι := ι))

/-- Measure-determination half of the Gaussian-BPS weak-forward obligation,
restricted to the finite regular measures that actually occur as Markov
marginals on the finite-dimensional phase space. -/
abbrev StandardGaussianBPSGeneratorTestFiniteRegularDetermining :=
  CompactTestFiniteRegularExpectationDetermining
    (StandardGaussianBPSGeneratorTest.observe (ι := ι))

/-- A complete smooth generator core represents every compactly supported
`C¹` phase observable by a checked Gaussian-BPS generator test. Establishing
this certificate consists precisely of the multivariate Gaussian
integration-by-parts and compact-support integrability calculations. -/
structure StandardGaussianBPSSmoothCore (ι : Type*) [Fintype ι] : Prop where
  represent : ∀ function : BouncyParticleState ι → ℝ,
    ContDiff ℝ 1 function → HasCompactSupport function →
      ∃ test : StandardGaussianBPSGeneratorTest ι,
        test.observable = function

/-- Building the coordinatewise Gaussian-Stein certificate for every compact
`C¹` phase observable constructs the represented smooth core automatically. -/
theorem standardGaussianBPSSmoothCore_of_observableCertificates
    (certify : ∀ function : BouncyParticleState ι → ℝ,
      ContDiff ℝ 1 function → HasCompactSupport function →
        StandardGaussianBPSSmoothObservableCertificate (ι := ι) function) :
    StandardGaussianBPSSmoothCore ι where
  represent function hsmooth hcompact :=
    ⟨(certify function hsmooth hcompact).toGeneratorTest, rfl⟩

/-- A complete smooth Gaussian-BPS core is automatically measure determining
for all finite regular phase-space measures. -/
theorem StandardGaussianBPSSmoothCore.finiteRegularDetermining
    (core : StandardGaussianBPSSmoothCore ι) :
    StandardGaussianBPSGeneratorTestFiniteRegularDetermining (ι := ι) := by
  apply compactTestFiniteRegularExpectationDetermining_of_represents_contDiff
  intro function hsmooth hcompact
  obtain ⟨test, htest⟩ := core.represent function hsmooth hcompact
  exact ⟨test, htest⟩

/-- Once target-started weak-forward uniqueness is established, the exact
generator balance stored by every test proves target invariance of the
constructed horizon kernel at every time. -/
theorem standardGaussianBPSHorizonKernel_invariant_of_targetWeakForwardUniqueness
    (uniqueness : StandardGaussianBPSTargetWeakForwardUniqueness (ι := ι))
    (horizon : NNReal) :
    (standardGaussianBPSHorizonKernel (ι := ι) horizon).Invariant
      (standardGaussianBPSTarget (ι := ι)) := by
  apply invariant_of_compactTest_generatorBalance_and_targetWeakUniqueness
    (standardGaussianBPSHorizonKernel (ι := ι))
    StandardGaussianBPSGeneratorTest.observe
    StandardGaussianBPSGeneratorTest.generator
    (standardGaussianBPSTarget (ι := ι)) uniqueness
  · exact StandardGaussianBPSGeneratorTest.integrable_generator
  · exact StandardGaussianBPSGeneratorTest.integral_generator_eq_zero

/-- The split analytic obligations—scalar weak-expectation uniqueness and
finite-regular measure determination—already imply exact Gaussian-BPS
stationarity. Regularity and finiteness of both candidate curves and the
constructed semigroup marginals are discharged from the finite-dimensional
Borel probability setting. -/
theorem standardGaussianBPSHorizonKernel_invariant_of_targetWeakExpectationUniqueness
    (scalar :
      StandardGaussianBPSTargetWeakExpectationUniqueness (ι := ι))
    (determining :
      StandardGaussianBPSGeneratorTestFiniteRegularDetermining (ι := ι))
    (horizon : NNReal) :
    (standardGaussianBPSHorizonKernel (ι := ι) horizon).Invariant
      (standardGaussianBPSTarget (ι := ι)) := by
  apply standardGaussianBPSHorizonKernel_invariant_of_targetWeakForwardUniqueness
  apply scalar.toTargetWeakForwardUniqueness_of_finiteRegular
    (standardGaussianBPSHorizonKernel (ι := ι))
    StandardGaussianBPSGeneratorTest.observe
    StandardGaussianBPSGeneratorTest.generator
    (standardGaussianBPSTarget (ι := ι)) determining
  · intro curve solution time
    letI : IsProbabilityMeasure (curve time) := solution.probability time
    infer_instance
  · intro time
    infer_instance

/-- With a represented smooth core, scalar weak-expectation uniqueness is the
only remaining stationarity premise. -/
theorem standardGaussianBPSHorizonKernel_invariant_of_smoothCore
    (core : StandardGaussianBPSSmoothCore ι)
    (scalar :
      StandardGaussianBPSTargetWeakExpectationUniqueness (ι := ι))
    (horizon : NNReal) :
    (standardGaussianBPSHorizonKernel (ι := ι) horizon).Invariant
      (standardGaussianBPSTarget (ι := ι)) :=
  standardGaussianBPSHorizonKernel_invariant_of_targetWeakExpectationUniqueness
    scalar core.finiteRegularDetermining horizon

theorem standardGaussianBPSHorizonKernel_apply_positiveFirstEvent
    (horizon : NNReal) (initial : BouncyParticleState ι)
    (hvelocity : initial.2 ≠ 0) :
    standardGaussianBPSHorizonKernel (ι := ι) horizon initial =
      Measure.map
        (standardGaussianBPSPositiveFirstEventEndpoint
          (ι := ι) horizon initial)
        (unitHazardMeasure.prod unitHazardSequenceMeasure) := by
  rw [standardGaussianBPSHorizonKernel_apply_firstEvent]
  apply Measure.map_congr
  have hpositive : ∀ᵐ headTail ∂
      unitHazardMeasure.prod unitHazardSequenceMeasure,
      0 < headTail.1 :=
    (Measure.quasiMeasurePreserving_fst
      (μ := unitHazardMeasure) (ν := unitHazardSequenceMeasure)).ae
        unitHazardMeasure_positive_ae
  filter_upwards [hpositive] with headTail hhazard
  exact standardGaussianBPSFirstEventEndpoint_eq_positive
    horizon initial hvelocity headTail hhazard

/-- First-event-or-residual-flow BPS kernel on a finite horizon. This kernel
handles a certified inactive state without imposing a fictitious event. It is
the one-event recursion component, not yet the complete repeatedly restarted
nonexplosive horizon process. -/
noncomputable def BouncyParticlePartialInverseHazardData.firstEventKernel
    (data : BouncyParticlePartialInverseHazardData ι) (horizon : NNReal) :
    Kernel (BouncyParticleState ι) (BouncyParticleState ι) :=
  data.clock.firstEventKernel
    (fun state =>
      (state.1, bouncyReflection (data.bounce.normal state.1) state.2))
    data.bounce.measurable_bounce horizon

instance BouncyParticlePartialInverseHazardData.firstEventKernel.instIsMarkovKernel
    (data : BouncyParticlePartialInverseHazardData ι) (horizon : NNReal) :
    IsMarkovKernel (data.firstEventKernel horizon) := by
  unfold BouncyParticlePartialInverseHazardData.firstEventKernel
  infer_instance

/-- Exact BPS horizon execution truncated after a fixed number of reachable
events. Every candidate uses a fresh unit-exponential hazard; an inactive or
beyond-horizon mark completes residual flow, and exhausting the budget also
fills the remaining time by flow. -/
noncomputable def BouncyParticlePartialInverseHazardData.truncatedHorizonKernel
    (data : BouncyParticlePartialInverseHazardData ι)
    (horizon : NNReal) (eventBudget : ℕ) :
    Kernel (BouncyParticleState ι) (BouncyParticleState ι) :=
  data.clock.truncatedHorizonKernel
    (fun state =>
      (state.1, bouncyReflection (data.bounce.normal state.1) state.2))
    data.bounce.measurable_bounce horizon eventBudget

instance BouncyParticlePartialInverseHazardData.truncatedHorizonKernel.instIsMarkovKernel
    (data : BouncyParticlePartialInverseHazardData ι)
    (horizon : NNReal) (eventBudget : ℕ) :
    IsMarkovKernel (data.truncatedHorizonKernel horizon eventBudget) := by
  unfold BouncyParticlePartialInverseHazardData.truncatedHorizonKernel
  infer_instance

@[simp] theorem BouncyParticlePartialInverseHazardData.truncatedHorizonKernel_zero
    (data : BouncyParticlePartialInverseHazardData ι) (horizon : NNReal) :
    data.truncatedHorizonKernel horizon 0 =
      bouncyParticleSemiflow.kernel horizon :=
  data.clock.truncatedHorizonKernel_zero _
    data.bounce.measurable_bounce horizon

end Mcmc.PDMP
