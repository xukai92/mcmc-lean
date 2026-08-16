import Mcmc.PDMP.Flow
import Mcmc.Hamiltonian.Leapfrog
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Bouncy-particle reflection algebra

This module defines the deterministic velocity reflection used by the Bouncy
Particle Sampler in finite-dimensional Euclidean space. For a nonzero event
normal it proves reversal of the normal velocity component, preservation of
kinetic norm, and involutivity. These are the geometric inputs to the jump-
flux argument; event-time construction and convergence remain separate.
-/

namespace Mcmc.PDMP

open Mcmc.Hamiltonian
open MeasureTheory

variable {ι : Type*} [Fintype ι]

/-- Reflect velocity across the hyperplane orthogonal to `normal`. -/
noncomputable def bouncyReflection (normal velocity : Position ι) : Position ι :=
  velocity - (2 * euclideanInner velocity normal /
    squaredEuclideanNorm normal) • normal

/-- A bounce reverses the velocity component along the event normal. -/
theorem euclideanInner_bouncyReflection_normal
    (normal velocity : Position ι) (hnormal : normal ≠ 0) :
    euclideanInner (bouncyReflection normal velocity) normal =
      -euclideanInner velocity normal := by
  have hnorm : squaredEuclideanNorm normal ≠ 0 :=
    ne_of_gt (squaredEuclideanNorm_pos hnormal)
  have hinner : euclideanInner normal normal ≠ 0 := by
    simpa [squaredEuclideanNorm] using hnorm
  unfold bouncyReflection squaredEuclideanNorm
  rw [euclideanInner_sub_left, euclideanInner_smul_left]
  field_simp [hinner]
  ring

/-- Bouncy reflection preserves squared Euclidean kinetic norm. -/
theorem squaredEuclideanNorm_bouncyReflection
    (normal velocity : Position ι) (hnormal : normal ≠ 0) :
    squaredEuclideanNorm (bouncyReflection normal velocity) =
      squaredEuclideanNorm velocity := by
  have hnorm : squaredEuclideanNorm normal ≠ 0 :=
    ne_of_gt (squaredEuclideanNorm_pos hnormal)
  unfold bouncyReflection
  rw [squaredEuclideanNorm_sub_smul]
  field_simp [hnorm]
  ring

/-- Reflecting twice across the same nonzero normal returns the velocity. -/
@[simp] theorem bouncyReflection_involutive
    (normal velocity : Position ι) (hnormal : normal ≠ 0) :
    bouncyReflection normal (bouncyReflection normal velocity) = velocity := by
  change bouncyReflection normal velocity -
      (2 * euclideanInner (bouncyReflection normal velocity) normal /
        squaredEuclideanNorm normal) • normal = velocity
  rw [euclideanInner_bouncyReflection_normal normal velocity hnormal]
  unfold bouncyReflection
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Canonical BPS event rate, the positive normal velocity component. -/
noncomputable def bouncyRate (normal velocity : Position ι) : ℝ :=
  max 0 (euclideanInner velocity normal)

@[simp] theorem bouncyReflection_zero (velocity : Position ι) :
    bouncyReflection (0 : Position ι) velocity = velocity := by
  simp [bouncyReflection, squaredEuclideanNorm, euclideanInner]

@[simp] theorem bouncyRate_zero (velocity : Position ι) :
    bouncyRate (0 : Position ι) velocity = 0 := by
  simp [bouncyRate, euclideanInner]

theorem bouncyRate_nonneg (normal velocity : Position ι) :
    0 ≤ bouncyRate normal velocity :=
  le_max_left _ _

/-- After a bounce the canonical event rate uses the opposite normal
component. -/
theorem bouncyRate_reflection
    (normal velocity : Position ι) (hnormal : normal ≠ 0) :
    bouncyRate normal (bouncyReflection normal velocity) =
      max 0 (-euclideanInner velocity normal) := by
  rw [bouncyRate, euclideanInner_bouncyReflection_normal normal velocity hnormal]

/-- Positive and negative normal flux differ by the signed normal velocity.
This is the pointwise cancellation between the BPS transport generator and
its bounce generator. -/
theorem bouncyRate_sub_reflectedRate
    (normal velocity : Position ι) (hnormal : normal ≠ 0) :
    bouncyRate normal velocity -
        bouncyRate normal (bouncyReflection normal velocity) =
      euclideanInner velocity normal := by
  rw [bouncyRate_reflection normal velocity hnormal]
  unfold bouncyRate
  let flux := euclideanInner velocity normal
  by_cases hflux : 0 ≤ flux
  · rw [max_eq_right hflux, max_eq_left (by linarith)]
    ring
  · have hflux' : flux ≤ 0 := le_of_not_ge hflux
    rw [max_eq_left hflux', max_eq_right (by linarith)]
    ring

/-- Equivalent incoming-minus-outgoing form of the BPS flux identity. -/
theorem reflectedRate_sub_bouncyRate
    (normal velocity : Position ι) (hnormal : normal ≠ 0) :
    bouncyRate normal (bouncyReflection normal velocity) -
        bouncyRate normal velocity =
      -euclideanInner velocity normal := by
  linarith [bouncyRate_sub_reflectedRate normal velocity hnormal]

/-- Pairing a bounce-generator term at a velocity with the corresponding term
at its reflection collapses to signed transport flux times the test-function
jump. This is the finite algebra used after a reflection-invariant velocity
measure changes variables. -/
theorem bouncyJump_pair
    (normal velocity : Position ι) (hnormal : normal ≠ 0)
    (test : Position ι → ℝ) :
    bouncyRate normal velocity *
          (test (bouncyReflection normal velocity) - test velocity) +
        bouncyRate normal (bouncyReflection normal velocity) *
          (test (bouncyReflection normal
              (bouncyReflection normal velocity)) -
            test (bouncyReflection normal velocity)) =
      euclideanInner velocity normal *
        (test (bouncyReflection normal velocity) - test velocity) := by
  rw [bouncyReflection_involutive normal velocity hnormal]
  have hflux := bouncyRate_sub_reflectedRate normal velocity hnormal
  rw [← hflux]
  ring

/-- For a fixed nonzero normal, bounce reflection is a measurable involutive
equivalence of velocity space. -/
noncomputable def bouncyReflectionMeasurableEquiv
    (normal : Position ι) (hnormal : normal ≠ 0) :
    Position ι ≃ᵐ Position ι where
  toEquiv :=
    { toFun := bouncyReflection normal
      invFun := bouncyReflection normal
      left_inv := fun velocity =>
        bouncyReflection_involutive normal velocity hnormal
      right_inv := fun velocity =>
        bouncyReflection_involutive normal velocity hnormal }
  measurable_toFun := by
    change Measurable (bouncyReflection normal)
    unfold bouncyReflection squaredEuclideanNorm euclideanInner
    fun_prop
  measurable_invFun := by
    change Measurable (bouncyReflection normal)
    unfold bouncyReflection squaredEuclideanNorm euclideanInner
    fun_prop

/-- Under any reflection-invariant velocity law, the integrated BPS jump term
equals minus the signed normal transport term. This is the measure-level
change-of-variables bridge from reflection geometry to generator balance. -/
theorem integral_bouncyJump_eq_neg_integral_normalFlux
    (normal : Position ι) (hnormal : normal ≠ 0)
    (velocityLaw : Measure (Position ι)) (test : Position ι → ℝ)
    (hpreserve : MeasurePreserving
      (bouncyReflectionMeasurableEquiv normal hnormal) velocityLaw velocityLaw)
    (hincoming : Integrable (fun velocity =>
      bouncyRate normal velocity *
        test (bouncyReflection normal velocity)) velocityLaw)
    (houtgoing : Integrable (fun velocity =>
      bouncyRate normal velocity * test velocity) velocityLaw)
    (hreflected : Integrable (fun velocity =>
      bouncyRate normal (bouncyReflection normal velocity) *
        test velocity) velocityLaw) :
    (∫ velocity,
      bouncyRate normal velocity *
        (test (bouncyReflection normal velocity) - test velocity)
        ∂velocityLaw) =
      -∫ velocity, euclideanInner velocity normal * test velocity
        ∂velocityLaw := by
  let reflection := bouncyReflectionMeasurableEquiv normal hnormal
  have hchange := hpreserve.integral_comp'
    (fun velocity =>
      bouncyRate normal (bouncyReflection normal velocity) * test velocity)
  have hchange' :
      (∫ velocity,
        bouncyRate normal velocity *
          test (bouncyReflection normal velocity) ∂velocityLaw) =
      ∫ velocity,
        bouncyRate normal (bouncyReflection normal velocity) * test velocity
          ∂velocityLaw := by
    rw [← hchange]
    apply integral_congr_ae
    filter_upwards [] with velocity
    simp [bouncyReflectionMeasurableEquiv,
      bouncyReflection_involutive normal velocity hnormal]
  have hintegrand : (fun velocity => bouncyRate normal velocity *
      (test (bouncyReflection normal velocity) - test velocity)) =
      fun velocity => bouncyRate normal velocity *
          test (bouncyReflection normal velocity) -
        bouncyRate normal velocity * test velocity := by
    funext velocity
    ring
  rw [hintegrand, integral_sub hincoming houtgoing]
  rw [hchange']
  rw [← integral_sub hreflected houtgoing]
  calc
    (∫ velocity,
        bouncyRate normal (bouncyReflection normal velocity) * test velocity -
          bouncyRate normal velocity * test velocity ∂velocityLaw) =
        ∫ velocity, -(euclideanInner velocity normal * test velocity)
          ∂velocityLaw := by
      apply integral_congr_ae
      filter_upwards [] with velocity
      calc
        bouncyRate normal (bouncyReflection normal velocity) * test velocity -
            bouncyRate normal velocity * test velocity =
          (bouncyRate normal (bouncyReflection normal velocity) -
            bouncyRate normal velocity) * test velocity := by ring
        _ = (-euclideanInner velocity normal) * test velocity := by
          rw [reflectedRate_sub_bouncyRate normal velocity hnormal]
        _ = -(euclideanInner velocity normal * test velocity) := by ring
    _ = -∫ velocity, euclideanInner velocity normal * test velocity
          ∂velocityLaw := by rw [integral_neg]

/-- Finite-dimensional BPS generator at a fixed position, with the spatial
directional derivative supplied by the caller. -/
noncomputable def bouncyGenerator (normal : Position ι)
    (directionalDerivative observable : Position ι → ℝ)
    (velocity : Position ι) : ℝ :=
  directionalDerivative velocity +
    bouncyRate normal velocity *
      (observable (bouncyReflection normal velocity) - observable velocity)

/-- After integrating over a reflection-invariant velocity law, the bounce
part of the BPS generator is exactly the negative normal transport flux. This
is the pointwise-in-position algebra needed before spatial integration by
parts. -/
theorem integral_bouncyGenerator_eq_transport_sub_normalFlux
    (normal : Position ι) (hnormal : normal ≠ 0)
    (velocityLaw : Measure (Position ι))
    (directionalDerivative observable : Position ι → ℝ)
    (hpreserve : MeasurePreserving
      (bouncyReflectionMeasurableEquiv normal hnormal) velocityLaw velocityLaw)
    (htransport : Integrable directionalDerivative velocityLaw)
    (hincoming : Integrable (fun velocity =>
      bouncyRate normal velocity *
        observable (bouncyReflection normal velocity)) velocityLaw)
    (houtgoing : Integrable (fun velocity =>
      bouncyRate normal velocity * observable velocity) velocityLaw)
    (hreflected : Integrable (fun velocity =>
      bouncyRate normal (bouncyReflection normal velocity) *
        observable velocity) velocityLaw) :
    (∫ velocity,
      bouncyGenerator normal directionalDerivative observable velocity
        ∂velocityLaw) =
      (∫ velocity, directionalDerivative velocity ∂velocityLaw) -
        ∫ velocity, euclideanInner velocity normal * observable velocity
          ∂velocityLaw := by
  have hjump : Integrable (fun velocity =>
      bouncyRate normal velocity *
        (observable (bouncyReflection normal velocity) - observable velocity))
      velocityLaw := by
    convert hincoming.sub houtgoing using 1
    funext velocity
    simp only [Pi.sub_apply]
    ring
  rw [show (fun velocity =>
      bouncyGenerator normal directionalDerivative observable velocity) =
      fun velocity => directionalDerivative velocity +
        bouncyRate normal velocity *
          (observable (bouncyReflection normal velocity) - observable velocity)
      by rfl]
  rw [integral_add htransport hjump,
    integral_bouncyJump_eq_neg_integral_normalFlux normal hnormal velocityLaw
      observable hpreserve hincoming houtgoing hreflected]
  ring

/-- Zero-gradient positions are covered as well: the reflection is the
identity and the bounce rate vanishes. The preservation premise is therefore
needed only for nonzero normals. -/
theorem integral_bouncyGenerator_eq_transport_sub_normalFlux'
    (normal : Position ι)
    (velocityLaw : Measure (Position ι))
    (directionalDerivative observable : Position ι → ℝ)
    (hpreserve : ∀ hnormal : normal ≠ 0, MeasurePreserving
      (bouncyReflectionMeasurableEquiv normal hnormal) velocityLaw velocityLaw)
    (htransport : Integrable directionalDerivative velocityLaw)
    (hincoming : Integrable (fun velocity =>
      bouncyRate normal velocity *
        observable (bouncyReflection normal velocity)) velocityLaw)
    (houtgoing : Integrable (fun velocity =>
      bouncyRate normal velocity * observable velocity) velocityLaw)
    (hreflected : Integrable (fun velocity =>
      bouncyRate normal (bouncyReflection normal velocity) *
        observable velocity) velocityLaw) :
    (∫ velocity,
      bouncyGenerator normal directionalDerivative observable velocity
        ∂velocityLaw) =
      (∫ velocity, directionalDerivative velocity ∂velocityLaw) -
        ∫ velocity, euclideanInner velocity normal * observable velocity
          ∂velocityLaw := by
  by_cases hnormal : normal = 0
  · subst normal
    simp [bouncyGenerator]
  · exact integral_bouncyGenerator_eq_transport_sub_normalFlux normal hnormal
      velocityLaw directionalDerivative observable (hpreserve hnormal)
      htransport hincoming houtgoing hreflected

end Mcmc.PDMP
