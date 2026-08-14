import McmcLean.Relativistic.ConstantMetric
import McmcLean.Relativistic.EndpointMetropolis
import McmcLean.Relativistic.Multinomial
import McmcLean.Hamiltonian.HMC

/-!
# Identity-metric endpoint GR-HMC

This module discharges the phase/conditional compatibility equation for the
identity metric.  It also records the momentum partition factor that is needed
because the phase Boltzmann target is unnormalized while the refresh kernel
uses a normalized momentum probability.
-/

namespace McmcLean.Relativistic

open MeasureTheory ProbabilityTheory
open McmcLean.Hamiltonian
open scoped ENNReal ProbabilityTheory

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

omit [Nonempty ι] [DecidableEq ι] in
/-- For the identity metric, the GR Boltzmann density factors into the usual
position density and the corrected Euclidean relativistic momentum density. -/
theorem identity_generalRelativisticBoltzmannWeight_eq_mul
    (potential : Position ι → ℝ) (m c : ℝ) (z : PhaseSpace ι) :
    generalRelativisticBoltzmannWeight potential
        identityFactoredRiemannianMetric m c z =
      positionBoltzmannWeight potential z.1 *
        relativisticBoltzmannWeight m c (euclideanNorm z.2) := by
  rw [generalRelativisticBoltzmannWeight, positionBoltzmannWeight,
    relativisticBoltzmannWeight]
  rw [show generalRelativisticHamiltonian potential
      identityFactoredRiemannianMetric m c z =
        potential z.1 + relativisticKineticEnergy m c z.2 by
    simp [generalRelativisticHamiltonian]]
  rw [radialRelativisticKineticEnergy_euclideanNorm]
  rw [show -(potential z.1 + relativisticKineticEnergy m c z.2) =
      -potential z.1 + -relativisticKineticEnergy m c z.2 by ring,
    Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]

omit [Nonempty ι] [DecidableEq ι] in
/-- The identity-metric phase target is the product of the unnormalized
position target and the corrected unnormalized momentum target. -/
theorem identity_generalRelativisticPhaseTarget_eq_prod
    {potential : Position ι → ℝ} (hpotential : Measurable potential)
    (m c : ℝ) :
    generalRelativisticPhaseTarget potential
        identityFactoredRiemannianMetric m c =
      (positionBoltzmannTarget potential).prod
        (euclideanRelativisticMomentumMeasure ι m c) := by
  unfold positionBoltzmannTarget euclideanRelativisticMomentumMeasure
  change generalRelativisticPhaseTarget potential
      identityFactoredRiemannianMetric m c =
    (volume.withDensity (positionBoltzmannWeight potential)).prod
      (volume.withDensity
        (relativisticBoltzmannWeight m c ∘ euclideanNorm))
  rw [prod_withDensity
      (measurable_positionBoltzmannWeight hpotential)
      ((continuous_relativisticBoltzmannWeight m c).measurable.comp
        continuous_euclideanNorm.measurable)]
  unfold generalRelativisticPhaseTarget phaseVolume
  congr 1
  funext z
  exact identity_generalRelativisticBoltzmannWeight_eq_mul potential m c z

/-- In the identity metric, the position-dependent momentum kernel is the
constant corrected Euclidean relativistic momentum probability. -/
theorem identityRelativisticMomentumKernel_eq_const
    (m c : ℝ) (hm : 0 < m) (hc : 0 < c) :
    identityRelativisticMomentumKernel (ι := ι) m c hm hc =
      Kernel.const (Position ι)
        (euclideanRelativisticMomentumProbability ι m c hm hc :
          Measure (Momentum ι)) := by
  ext q s hs
  rw [Kernel.const_apply]
  change (riemannianRelativisticMomentumProbability
      identityFactoredRiemannianMetric m c hm hc q : Measure (Momentum ι)) s = _
  rw [identity_riemannianRelativisticMomentumProbability]

/-- Position target scaled by the relativistic momentum partition function.
Scaling is necessary only because the phase target is left unnormalized. -/
noncomputable def identityRelativisticPositionTarget
    (potential : Position ι → ℝ) (m c : ℝ)
    (hm : 0 < m) (hc : 0 < c) : Measure (Position ι) :=
  euclideanRelativisticMomentumPartition ι m c hm hc •
    positionBoltzmannTarget potential

/-- The identity metric satisfies the complete target/conditional
compatibility equation used by the position-space GR-HMC invariance theorem. -/
theorem identity_isCompatibleGRPositionTarget
    {potential : Position ι → ℝ} (hpotential : Measurable potential)
    (m c : ℝ) (hm : 0 < m) (hc : 0 < c) :
    IsCompatibleGRPositionTarget potential
      (identityFactoredRiemannianMetric (ι := ι)) m c hm hc
      (identity_isMeasurableRiemannianMomentumFamily m c hm hc)
      (identityRelativisticPositionTarget potential m c hm hc) := by
  let Z := euclideanRelativisticMomentumPartition ι m c hm hc
  let momentumMeasure := euclideanRelativisticMomentumMeasure ι m c
  have hZ : Z ≠ 0 :=
    euclideanRelativisticMomentumPartition_ne_zero ι m c hm hc
  letI : IsFiniteMeasure
      (relativisticCartesianMomentumMeasure (EuclideanSpace ℝ ι) m c) :=
    isFiniteMeasure_relativisticCartesianMomentumMeasure
      (EuclideanSpace ℝ ι) m c hm hc
  letI : IsFiniteMeasure momentumMeasure := by
    dsimp only [momentumMeasure]
    rw [← map_euclideanRelativisticMomentumMeasure]
    infer_instance
  letI : SFinite (identityRelativisticPositionTarget potential m c hm hc) := by
    unfold identityRelativisticPositionTarget positionBoltzmannTarget
    infer_instance
  unfold IsCompatibleGRPositionTarget
  rw [show riemannianMomentumKernel identityFactoredRiemannianMetric m c hm hc
      (identity_isMeasurableRiemannianMomentumFamily m c hm hc) =
        Kernel.const (Position ι)
          (euclideanRelativisticMomentumProbability ι m c hm hc :
            Measure (Momentum ι)) by
    exact identityRelativisticMomentumKernel_eq_const m c hm hc]
  rw [Measure.compProd_const,
    euclideanRelativisticMomentumProbability_toMeasure]
  change (Z • positionBoltzmannTarget potential).prod
      (Z⁻¹ • momentumMeasure) = _
  rw [Measure.prod_smul_right, Measure.prod_smul_left, smul_smul]
  rw [inv_mul_cancel₀ hZ, one_smul]
  exact (identity_generalRelativisticPhaseTarget_eq_prod hpotential m c).symm

omit [Nonempty ι] [DecidableEq ι] in
theorem measurable_identity_generalRelativisticHamiltonian
    {potential : Position ι → ℝ} (hpotential : Measurable potential)
    (m c : ℝ) :
    Measurable (generalRelativisticHamiltonian potential
      identityFactoredRiemannianMetric m c) := by
  have h : Measurable fun z : PhaseSpace ι =>
      potential z.1 + relativisticKineticEnergy m c z.2 :=
    (hpotential.comp measurable_fst).add
      ((continuous_relativisticKineticEnergy m c).measurable.comp measurable_snd)
  rw [show generalRelativisticHamiltonian potential
      identityFactoredRiemannianMetric m c =
      (fun z : PhaseSpace ι =>
        potential z.1 + relativisticKineticEnergy m c z.2) by
    funext z
    simp [generalRelativisticHamiltonian]]
  exact h

/-- Concrete position-target invariance for identity-metric endpoint GR-HMC.
Only the generalized-leapfrog validity certificate remains conditional. -/
theorem identity_positionEndpointMetropolisGRHMC_invariant
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    {potential : Position ι → ℝ} (hpotential : Measurable potential)
    (m c : ℝ) (hm : 0 < m) (hc : 0 < c)
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid) (ε : ℝ) :
    (positionEndpointMetropolisGRHMC potential
      (identityFactoredRiemannianMetric (ι := ι)) m c hm hc selection hvalid
      (identity_isMeasurableRiemannianMomentumFamily m c hm hc) ε).Invariant
        (identityRelativisticPositionTarget potential m c hm hc) := by
  letI : SFinite (identityRelativisticPositionTarget potential m c hm hc) := by
    unfold identityRelativisticPositionTarget positionBoltzmannTarget
    infer_instance
  exact positionEndpointMetropolisGRHMC_invariant potential
    identityFactoredRiemannianMetric m c hm hc selection hvalid
    (measurable_identity_generalRelativisticHamiltonian hpotential m c)
    (identity_isMeasurableRiemannianMomentumFamily m c hm hc) ε
    (identityRelativisticPositionTarget potential m c hm hc)
    (identity_isCompatibleGRPositionTarget hpotential m c hm hc)

/-- Concrete position-target invariance for identity-metric multinomial
GR-HMC. Only the generalized-leapfrog validity certificate remains
conditional. -/
theorem identity_positionMultinomialGRHMC_invariant
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    {potential : Position ι → ℝ} (hpotential : Measurable potential)
    (m c : ℝ) (hm : 0 < m) (hc : 0 < c)
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid) (ε : ℝ) (L : ℕ) :
    (positionMultinomialGRHMC potential
      (identityFactoredRiemannianMetric (ι := ι)) m c hm hc selection hvalid
      (measurable_identity_generalRelativisticHamiltonian hpotential m c)
      (identity_isMeasurableRiemannianMomentumFamily m c hm hc) ε L).Invariant
        (identityRelativisticPositionTarget potential m c hm hc) := by
  letI : SFinite (identityRelativisticPositionTarget potential m c hm hc) := by
    unfold identityRelativisticPositionTarget positionBoltzmannTarget
    infer_instance
  exact positionMultinomialGRHMC_invariant potential
    identityFactoredRiemannianMetric m c hm hc selection hvalid
    (measurable_identity_generalRelativisticHamiltonian hpotential m c)
    (identity_isMeasurableRiemannianMomentumFamily m c hm hc) ε L
    (identityRelativisticPositionTarget potential m c hm hc)
    (identity_isCompatibleGRPositionTarget hpotential m c hm hc)

end McmcLean.Relativistic
