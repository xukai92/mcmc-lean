import Mcmc.PDMP.BouncyParticleProcess
import Mcmc.PDMP.ZigZagProcess
import Mathlib.Tactic

/-!
# One-dimensional Gaussian BPS / Zig-Zag bridge

At unit speed, one-dimensional Bouncy Particle dynamics are exactly Zig-Zag
dynamics: the standard-Gaussian normal is position, a nonzero bounce negates
velocity, and the canonical rates and linear flows coincide.  This module
records that identification so the exact Zig-Zag clock, nonexplosion proof,
and stopped horizon construction can later be transferred to BPS without a
second path construction.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace Mcmc.PDMP

open Mcmc.Hamiltonian

/-- Embed a scalar Zig-Zag state into one-dimensional Euclidean BPS phase
space. -/
def gaussianBouncyEmbedding (state : ZigZagState) :
    BouncyParticleState (Fin 1) :=
  (fun _ => state.1, fun _ => zigZagVelocity state.2)

theorem gaussianBouncyEmbedding_injective :
    Function.Injective gaussianBouncyEmbedding := by
  intro x y hxy
  apply Prod.ext
  · have h := congrFun (congrArg Prod.fst hxy) 0
    simpa [gaussianBouncyEmbedding] using h
  · have h := congrFun (congrArg Prod.snd hxy) 0
    change zigZagVelocity x.2 = zigZagVelocity y.2 at h
    cases hx : x.2 <;> cases hy : y.2 <;>
      simp [hx, hy, zigZagVelocity] at h ⊢ <;> norm_num at h

/-- Reflection in one dimension negates velocity whenever the event normal is
nonzero. -/
theorem bouncyReflection_fin_one
    (normal velocity : Position (Fin 1)) (hnormal : normal ≠ 0) :
    bouncyReflection normal velocity = -velocity := by
  have hnormal0 : normal 0 ≠ 0 := by
    intro hzero
    apply hnormal
    funext i
    fin_cases i
    exact hzero
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp only [bouncyReflection, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    euclideanInner, squaredEuclideanNorm, Fin.sum_univ_succ, Fin.sum_univ_zero,
    add_zero, Pi.neg_apply]
  field_simp [hnormal0]
  ring

/-- The standard-Gaussian BPS normal at an embedded state. -/
def gaussianBouncyNormal (q : ℝ) : Position (Fin 1) := fun _ => q

/-- Canonical BPS and Zig-Zag rates coincide under the embedding. -/
theorem gaussianBouncyRate_embedding (state : ZigZagState) :
    bouncyRate (gaussianBouncyNormal state.1)
      (gaussianBouncyEmbedding state).2 =
      zigZagRate id state.1 state.2 := by
  simp [bouncyRate, gaussianBouncyNormal, gaussianBouncyEmbedding,
    euclideanInner, zigZagRate]

/-- Away from the zero-gradient point, a BPS bounce is exactly the embedded
Zig-Zag velocity flip. The event intensity is zero at the excluded point. -/
theorem gaussianBouncyReflection_embedding (state : ZigZagState)
    (hposition : state.1 ≠ 0) :
    bouncyReflection (gaussianBouncyNormal state.1)
      (gaussianBouncyEmbedding state).2 =
      (gaussianBouncyEmbedding (zigZagFlip state)).2 := by
  have hnormal : gaussianBouncyNormal state.1 ≠ 0 := by
    intro hzero
    apply hposition
    have h := congrFun hzero 0
    simpa [gaussianBouncyNormal] using h
  rw [bouncyReflection_fin_one _ _ hnormal]
  funext i
  fin_cases i
  cases hv : state.2 <;>
    simp [gaussianBouncyEmbedding, zigZagFlip, zigZagVelocity, hv]

/-- The linear BPS flow is exactly the embedded Zig-Zag flow. -/
theorem gaussianBouncyFlow_embedding (time : NNReal) (state : ZigZagState) :
    bouncyParticleFlow time (gaussianBouncyEmbedding state) =
      gaussianBouncyEmbedding (zigZagFlow time state) := by
  apply Prod.ext
  · funext i
    fin_cases i
    simp [bouncyParticleFlow, gaussianBouncyEmbedding, zigZagFlow]
  · rfl

/-! ### Exact unit-speed Gaussian BPS process -/

/-- Sign-coordinate representation of one-dimensional unit-speed Gaussian
BPS. The preceding theorems prove that this representation has the actual BPS
flow, rate, and nonzero-normal reflection. -/
abbrev GaussianUnitBouncyState := ZigZagState

/-- Normalized Gaussian-position/equal-sign target for unit-speed Gaussian
BPS. -/
noncomputable def gaussianUnitBouncyTarget : Measure GaussianUnitBouncyState :=
  gaussianZigZagTarget

instance gaussianUnitBouncyTarget.instIsProbabilityMeasure :
    IsProbabilityMeasure gaussianUnitBouncyTarget := by
  unfold gaussianUnitBouncyTarget
  infer_instance

/-- Exact finite-horizon unit-speed Gaussian BPS transition, reusing the
closed-form event clock and measurable nonexplosive stopping construction
through the proved one-dimensional BPS/Zig-Zag identification. -/
noncomputable def gaussianUnitBouncyHorizonKernel (horizon : NNReal) :
    Kernel GaussianUnitBouncyState GaussianUnitBouncyState :=
  gaussianZigZagHorizonKernel horizon

instance gaussianUnitBouncyHorizonKernel.instIsMarkovKernel
    (horizon : NNReal) :
    IsMarkovKernel (gaussianUnitBouncyHorizonKernel horizon) := by
  unfold gaussianUnitBouncyHorizonKernel
  infer_instance

@[simp] theorem gaussianUnitBouncyHorizonKernel_zero :
    gaussianUnitBouncyHorizonKernel 0 = Kernel.id :=
  gaussianZigZagHorizonKernel_zero

/-- Exact unit-speed Gaussian BPS has no finite accumulation of bounce events:
cumulative event time tends to infinity almost surely. -/
theorem gaussianUnitBouncyEventElapsed_tendsto_atTop_ae
    (initial : GaussianUnitBouncyState) :
    ∀ᵐ hazards ∂gaussianZigZagHazardSequenceMeasure,
      Filter.Tendsto (gaussianZigZagEventElapsed initial hazards)
        Filter.atTop (nhds (∞ : ENNReal)) :=
  gaussianZigZagEventElapsed_tendsto_atTop_ae initial

/-- The unit-speed Gaussian BPS stationarity obligation is exactly the same
setwise forward equation as in its Zig-Zag representation. -/
abbrev GaussianUnitBouncyForwardEquation := GaussianZigZagForwardEquation

/-- Weak-forward uniqueness for unit-speed one-dimensional Gaussian BPS is
the same obligation as for its proved Zig-Zag representation. -/
abbrev GaussianUnitBouncyWeakForwardUniqueness :=
  GaussianZigZagWeakForwardUniqueness

abbrev GaussianUnitBouncyTargetWeakForwardUniqueness :=
  GaussianZigZagTargetWeakForwardUniqueness

abbrev GaussianUnitBouncyWeakExpectationUniqueness :=
  GaussianZigZagWeakExpectationUniqueness

abbrev GaussianUnitBouncyTargetWeakExpectationUniqueness :=
  GaussianZigZagTargetWeakExpectationUniqueness

/-- A proof of the shared forward equation yields target preservation for the
exact unit-speed Gaussian BPS horizon kernel. -/
theorem gaussianUnitBouncyHorizonKernel_invariant_of_forwardEquation
    (forward : GaussianUnitBouncyForwardEquation) (horizon : NNReal) :
    (gaussianUnitBouncyHorizonKernel horizon).Invariant
      gaussianUnitBouncyTarget :=
  gaussianZigZagHorizonKernel_invariant_of_forwardEquation forward horizon

/-- The split scalar-uniqueness and measure-determination obligations also
yield exact unit-speed Gaussian BPS stationarity. -/
theorem gaussianUnitBouncyHorizonKernel_invariant_of_weakExpectationUniqueness
    (scalar : GaussianUnitBouncyWeakExpectationUniqueness)
    (determining : GaussianZigZagSmoothTestDetermining)
    (horizon : NNReal) :
    (gaussianUnitBouncyHorizonKernel horizon).Invariant
      gaussianUnitBouncyTarget :=
  gaussianZigZagHorizonKernel_invariant_of_weakExpectationUniqueness
    scalar determining horizon

/-- Target-started weak-forward uniqueness is the minimal remaining premise
for exact unit-speed Gaussian BPS stationarity. -/
theorem gaussianUnitBouncyHorizonKernel_invariant_of_targetWeakForwardUniqueness
    (uniqueness : GaussianUnitBouncyTargetWeakForwardUniqueness)
    (horizon : NNReal) :
    (gaussianUnitBouncyHorizonKernel horizon).Invariant
      gaussianUnitBouncyTarget :=
  gaussianZigZagHorizonKernel_invariant_of_targetWeakForwardUniqueness
    uniqueness horizon

/-- The minimal split target-started premises also yield exact unit-speed
Gaussian BPS stationarity. -/
theorem gaussianUnitBouncyHorizonKernel_invariant_of_targetWeakExpectationUniqueness
    (scalar : GaussianUnitBouncyTargetWeakExpectationUniqueness)
    (determining : GaussianZigZagSmoothTestDetermining)
    (horizon : NNReal) :
    (gaussianUnitBouncyHorizonKernel horizon).Invariant
      gaussianUnitBouncyTarget :=
  gaussianZigZagHorizonKernel_invariant_of_targetWeakExpectationUniqueness
    scalar determining horizon

/-- Regular-measure form of the minimal split theorem, transferred through
the exact unit-speed Gaussian BPS/Zig-Zag identification. -/
theorem gaussianUnitBouncyHorizonKernel_invariant_of_targetWeakExpectationUniqueness_regular
    (scalar : GaussianUnitBouncyTargetWeakExpectationUniqueness)
    (determining : GaussianZigZagSmoothTestRegularDetermining)
    (horizon : NNReal) :
    (gaussianUnitBouncyHorizonKernel horizon).Invariant
      gaussianUnitBouncyTarget :=
  gaussianZigZagHorizonKernel_invariant_of_targetWeakExpectationUniqueness_regular
    scalar determining horizon

end Mcmc.PDMP
