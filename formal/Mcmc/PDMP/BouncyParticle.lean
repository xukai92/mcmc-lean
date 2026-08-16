import Mcmc.PDMP.Flow
import Mcmc.Hamiltonian.Leapfrog
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Probability.Distributions.Gaussian.Multivariate
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

/-! ### Product-space generator balance -/

/-- Full BPS phase-space generator with position-dependent event normal,
directional derivative, and observable. -/
noncomputable def bouncyPhaseGenerator
    (normal : Position ι → Position ι)
    (directionalDerivative observable : Position ι → Position ι → ℝ)
    (state : Position ι × Position ι) : ℝ :=
  bouncyGenerator (normal state.1) (directionalDerivative state.1)
    (observable state.1) state.2

/-- Reflection invariance of the velocity law and spatial integration by parts
imply mean-zero of the full finite-dimensional BPS generator under the product
target. This is an infinitesimal balance theorem; it does not infer existence,
stationarity, or convergence of a BPS process. -/
theorem integral_bouncyPhaseGenerator_eq_zero
    (positionLaw velocityLaw : Measure (Position ι))
    [SFinite positionLaw] [SFinite velocityLaw]
    (normal : Position ι → Position ι)
    (directionalDerivative observable : Position ι → Position ι → ℝ)
    (hpreserve : ∀ position (hnormal : normal position ≠ 0),
      MeasurePreserving
        (bouncyReflectionMeasurableEquiv (normal position) hnormal)
        velocityLaw velocityLaw)
    (htransport : ∀ position,
      Integrable (directionalDerivative position) velocityLaw)
    (hincoming : ∀ position, Integrable (fun velocity =>
      bouncyRate (normal position) velocity *
        observable position
          (bouncyReflection (normal position) velocity)) velocityLaw)
    (houtgoing : ∀ position, Integrable (fun velocity =>
      bouncyRate (normal position) velocity * observable position velocity)
        velocityLaw)
    (hreflected : ∀ position, Integrable (fun velocity =>
      bouncyRate (normal position)
          (bouncyReflection (normal position) velocity) *
        observable position velocity) velocityLaw)
    (hphase : Integrable
      (bouncyPhaseGenerator normal directionalDerivative observable)
      (positionLaw.prod velocityLaw))
    (htransportIntegrated : Integrable (fun position =>
      ∫ velocity, directionalDerivative position velocity ∂velocityLaw)
      positionLaw)
    (hfluxIntegrated : Integrable (fun position =>
      ∫ velocity, euclideanInner velocity (normal position) *
        observable position velocity ∂velocityLaw) positionLaw)
    (hibp :
      (∫ position, ∫ velocity, directionalDerivative position velocity
          ∂velocityLaw ∂positionLaw) =
        ∫ position, ∫ velocity,
          euclideanInner velocity (normal position) *
            observable position velocity ∂velocityLaw ∂positionLaw) :
    (∫ state,
      bouncyPhaseGenerator normal directionalDerivative observable state
        ∂(positionLaw.prod velocityLaw)) = 0 := by
  rw [integral_prod _ hphase]
  have hpointwise : (fun position =>
      ∫ velocity,
        bouncyPhaseGenerator normal directionalDerivative observable
          (position, velocity) ∂velocityLaw) =
      fun position =>
        (∫ velocity, directionalDerivative position velocity ∂velocityLaw) -
          ∫ velocity, euclideanInner velocity (normal position) *
            observable position velocity ∂velocityLaw := by
    funext position
    exact integral_bouncyGenerator_eq_transport_sub_normalFlux'
      (normal position) velocityLaw (directionalDerivative position)
      (observable position) (hpreserve position) (htransport position)
      (hincoming position) (houtgoing position) (hreflected position)
  rw [hpointwise, integral_sub htransportIntegrated hfluxIntegrated, hibp,
    sub_self]

/-! ### Standard-Gaussian reflection invariance -/

section GaussianReflection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- Every orthogonal reflection preserves the finite-dimensional standard
Gaussian law. This is the coordinate-free Gaussian premise needed by BPS; a
client using `Position ι` must additionally identify its Householder map with
such a reflection through the Euclidean-space equivalence. -/
theorem stdGaussian_reflection_measurePreserving
    (subspace : Submodule ℝ E) :
    MeasurePreserving subspace.reflection
      (ProbabilityTheory.stdGaussian E)
      (ProbabilityTheory.stdGaussian E) := by
  refine ⟨subspace.reflection.continuous.measurable, ?_⟩
  exact ProbabilityTheory.stdGaussian_map subspace.reflection

end GaussianReflection

/-- Standard Gaussian on the repository's coordinate `Position` space,
transported from mathlib's Euclidean-space Gaussian through `ofLp`. -/
noncomputable def l2StandardGaussianPosition : Measure (Position ι) :=
  (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)).map
    (MeasurableEquiv.toLp 2 (Position ι)).symm

instance l2StandardGaussianPosition.instIsProbabilityMeasure :
    IsProbabilityMeasure (l2StandardGaussianPosition (ι := ι)) := by
  constructor
  rw [l2StandardGaussianPosition, Measure.map_apply
    (MeasurableEquiv.toLp 2 (Position ι)).symm.measurable MeasurableSet.univ]
  simp

/-- Transporting the Euclidean standard Gaussian back to coordinates recovers
the independent product of one-dimensional standard Gaussians exactly. -/
theorem l2StandardGaussianPosition_eq_pi :
    l2StandardGaussianPosition (ι := ι) =
      Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1) := by
  rw [l2StandardGaussianPosition,
    ← ProbabilityTheory.map_pi_eq_stdGaussian]
  rw [Measure.map_map]
  · convert Measure.map_id
    funext x
    exact (MeasurableEquiv.toLp 2 (Position ι)).symm_apply_apply x
  · exact (MeasurableEquiv.toLp 2 (Position ι)).symm.measurable
  · exact (MeasurableEquiv.toLp 2 (Position ι)).measurable

/-- Conjugate a Euclidean reflection back to the coordinate `Position` space. -/
noncomputable def conjugatedEuclideanReflection
    (subspace : Submodule ℝ (EuclideanSpace ℝ ι)) : Position ι → Position ι :=
  fun velocity => (MeasurableEquiv.toLp 2 (Position ι)).symm
    (subspace.reflection (MeasurableEquiv.toLp 2 (Position ι) velocity))

/-- Every conjugated Euclidean reflection preserves the transported standard
Gaussian on coordinate positions. -/
theorem l2StandardGaussianPosition_reflection_measurePreserving
    (subspace : Submodule ℝ (EuclideanSpace ℝ ι)) :
    MeasurePreserving (conjugatedEuclideanReflection subspace)
      (l2StandardGaussianPosition (ι := ι))
      (l2StandardGaussianPosition (ι := ι)) := by
  let equiv := MeasurableEquiv.toLp 2 (Position ι)
  have hofLp : MeasurePreserving equiv.symm
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι))
      (l2StandardGaussianPosition (ι := ι)) := by
    refine ⟨equiv.symm.measurable, ?_⟩
    rfl
  have htoLp : MeasurePreserving equiv
      (l2StandardGaussianPosition (ι := ι))
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) :=
    hofLp.symm
  have hreflection := stdGaussian_reflection_measurePreserving subspace
  exact hofLp.comp (hreflection.comp htoLp)

/-- The coordinate Householder bounce is the Euclidean reflection across the
hyperplane orthogonal to its nonzero normal, conjugated through `toLp/ofLp`. -/
theorem bouncyReflection_eq_conjugatedEuclideanReflection
    (normal : Position ι) (hnormal : normal ≠ 0) :
    bouncyReflection normal = conjugatedEuclideanReflection
      ((ℝ ∙ (MeasurableEquiv.toLp 2 (Position ι) normal))ᗮ) := by
  funext velocity
  have hsum : (∑ x, normal x * normal x) ≠ 0 := by
    simpa [squaredEuclideanNorm, euclideanInner] using
      ne_of_gt (squaredEuclideanNorm_pos hnormal)
  have hinner : inner ℝ (MeasurableEquiv.toLp 2 (Position ι) normal)
      (MeasurableEquiv.toLp 2 (Position ι) velocity) =
      ∑ x, velocity x * normal x := by
    rw [EuclideanSpace.inner_toLp_toLp]
    rfl
  have hnormsq : ‖MeasurableEquiv.toLp 2 (Position ι) normal‖ ^ 2 =
      ∑ x, normal x * normal x := by
    rw [← real_inner_self_eq_norm_sq,
      EuclideanSpace.inner_toLp_toLp]
    rfl
  have hcoordinate (x : Position ι) (i : ι) :
      ((MeasurableEquiv.toLp 2 (Position ι) x).ofLp) i = x i := rfl
  unfold conjugatedEuclideanReflection
  rw [Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply]
  unfold bouncyReflection squaredEuclideanNorm euclideanInner
  ext i
  rw [hinner]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  rw [hnormsq]
  simp only [MeasurableEquiv.coe_toLp_symm]
  simp only [WithLp.ofLp_neg, WithLp.ofLp_sub, WithLp.ofLp_smul,
    WithLp.ofLp_add,
    Pi.neg_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    two_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hcoordinate normal i, hcoordinate velocity i]
  simp only [div_eq_mul_inv]
  ring

/-- Therefore the repository's nonzero-normal Householder bounce preserves the
transported standard Gaussian velocity law on `Position`. -/
theorem bouncyReflection_l2StandardGaussian_measurePreserving
    (normal : Position ι) (hnormal : normal ≠ 0) :
    MeasurePreserving (bouncyReflection normal)
      (l2StandardGaussianPosition (ι := ι))
      (l2StandardGaussianPosition (ι := ι)) := by
  rw [bouncyReflection_eq_conjugatedEuclideanReflection normal hnormal]
  exact l2StandardGaussianPosition_reflection_measurePreserving
    ((ℝ ∙ (MeasurableEquiv.toLp 2 (Position ι) normal))ᗮ)

/-- Standard-Gaussian velocity specialization of the product-space BPS
generator theorem. Reflection invariance is discharged internally; clients
provide only the analytic integrability and spatial integration-by-parts
premises. -/
theorem integral_bouncyPhaseGenerator_l2StandardGaussian_eq_zero
    (positionLaw : Measure (Position ι)) [SFinite positionLaw]
    (normal : Position ι → Position ι)
    (directionalDerivative observable : Position ι → Position ι → ℝ)
    (htransport : ∀ position,
      Integrable (directionalDerivative position)
        (l2StandardGaussianPosition (ι := ι)))
    (hincoming : ∀ position, Integrable (fun velocity =>
      bouncyRate (normal position) velocity *
        observable position
          (bouncyReflection (normal position) velocity))
        (l2StandardGaussianPosition (ι := ι)))
    (houtgoing : ∀ position, Integrable (fun velocity =>
      bouncyRate (normal position) velocity * observable position velocity)
        (l2StandardGaussianPosition (ι := ι)))
    (hreflected : ∀ position, Integrable (fun velocity =>
      bouncyRate (normal position)
          (bouncyReflection (normal position) velocity) *
        observable position velocity)
        (l2StandardGaussianPosition (ι := ι)))
    (hphase : Integrable
      (bouncyPhaseGenerator normal directionalDerivative observable)
      (positionLaw.prod (l2StandardGaussianPosition (ι := ι))))
    (htransportIntegrated : Integrable (fun position =>
      ∫ velocity, directionalDerivative position velocity
        ∂l2StandardGaussianPosition) positionLaw)
    (hfluxIntegrated : Integrable (fun position =>
      ∫ velocity, euclideanInner velocity (normal position) *
        observable position velocity ∂l2StandardGaussianPosition) positionLaw)
    (hibp :
      (∫ position, ∫ velocity, directionalDerivative position velocity
          ∂l2StandardGaussianPosition ∂positionLaw) =
        ∫ position, ∫ velocity,
          euclideanInner velocity (normal position) *
            observable position velocity
          ∂l2StandardGaussianPosition ∂positionLaw) :
    (∫ state,
      bouncyPhaseGenerator normal directionalDerivative observable state
        ∂(positionLaw.prod (l2StandardGaussianPosition (ι := ι)))) = 0 := by
  apply integral_bouncyPhaseGenerator_eq_zero positionLaw
    (l2StandardGaussianPosition (ι := ι)) normal directionalDerivative
    observable
  · intro position hnormal
    exact bouncyReflection_l2StandardGaussian_measurePreserving
      (normal position) hnormal
  · exact htransport
  · exact hincoming
  · exact houtgoing
  · exact hreflected
  · exact hphase
  · exact htransportIntegrated
  · exact hfluxIntegrated
  · exact hibp

end Mcmc.PDMP
