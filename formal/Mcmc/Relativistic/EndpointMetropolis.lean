import Mcmc.Relativistic.GeneralizedLeapfrog
import Mcmc.Kernel.DeterministicMetropolis
import Mcmc.Kernel.LiftEvolveProject
import Mcmc.Hamiltonian.HMC
import Mathlib.Probability.Kernel.CompProdEqIff

/-!
# Endpoint-Metropolis correction for GR-HMC

This module connects a certified generalized-leapfrog implementation to the
generic deterministic Metropolis theorem.  The proposal first takes an
implicit generalized-leapfrog step and then flips momentum.  Uniqueness and
time reversal make that proposal an involution; phase-volume preservation of
the step and flip make it measure preserving.  Metropolis correction therefore
preserves the GR Boltzmann target exactly.

The theorem is conditional on the explicit numerical-integrator certificate.
Writing the implicit equations, or approximately solving them to an
unspecified tolerance, does not supply that certificate.
-/

namespace Mcmc.Relativistic

open MeasureTheory
open ProbabilityTheory
open Mcmc.Hamiltonian
open Mcmc.Kernel
open scoped ENNReal ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- Endpoint proposal used by generalized HMC: one selected integrator step
followed by momentum negation. -/
def generalizedLeapfrogEndpoint
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (ε : ℝ) : PhaseSpace ι → PhaseSpace ι :=
  momentumFlip ∘ selection.step ε

omit [Fintype ι] in
theorem measurable_generalizedLeapfrogEndpoint
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hmeasurable : selection.IsMeasurable) (ε : ℝ) :
    Measurable (generalizedLeapfrogEndpoint selection ε) := by
  exact measurable_momentumFlip.comp (hmeasurable ε)

theorem generalizedLeapfrogEndpoint_involutive
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid) (ε : ℝ) :
    Function.Involutive (generalizedLeapfrogEndpoint selection ε) := by
  exact selection.momentumFlip_step_involutive hvalid.unique
    hvalid.reversible ε

theorem measurePreserving_generalizedLeapfrogEndpoint
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid) (ε : ℝ) :
    MeasurePreserving (generalizedLeapfrogEndpoint selection ε)
      phaseVolume phaseVolume := by
  exact measurePreserving_momentumFlip.comp (hvalid.volumePreserving ε)

/-- Unnormalized density `exp (-H_GR(q,p))` with respect to phase-space
Lebesgue measure. -/
noncomputable def generalRelativisticBoltzmannWeight
    (potential : Position ι → ℝ)
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (z : PhaseSpace ι) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp
    (-generalRelativisticHamiltonian potential metric m c z))

/-- A one-sided GR-Hamiltonian discrepancy gives multiplicative domination
of the corresponding unnormalized Boltzmann weights. -/
theorem generalRelativisticBoltzmannWeight_le_exp_mul_of_sub_le
    (potential : Position ι → ℝ)
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (z₁ z₂ : PhaseSpace ι) {r : ℝ}
    (h : generalRelativisticHamiltonian potential metric m c z₂ -
      generalRelativisticHamiltonian potential metric m c z₁ ≤ r) :
    generalRelativisticBoltzmannWeight potential metric m c z₁ ≤
      ENNReal.ofReal (Real.exp r) *
        generalRelativisticBoltzmannWeight potential metric m c z₂ := by
  unfold generalRelativisticBoltzmannWeight
  rw [← ENNReal.ofReal_mul (Real.exp_pos r).le]
  apply ENNReal.ofReal_le_ofReal
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

@[simp]
theorem generalRelativisticBoltzmannWeight_ne_zero
    (potential : Position ι → ℝ)
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (z : PhaseSpace ι) :
    generalRelativisticBoltzmannWeight potential metric m c z ≠ 0 := by
  simp [generalRelativisticBoltzmannWeight, Real.exp_pos]

@[simp]
theorem generalRelativisticBoltzmannWeight_ne_top
    (potential : Position ι → ℝ)
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (z : PhaseSpace ι) :
    generalRelativisticBoltzmannWeight potential metric m c z ≠ ∞ := by
  simp [generalRelativisticBoltzmannWeight]

theorem measurable_generalRelativisticBoltzmannWeight
    (potential : Position ι → ℝ)
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (hH : Measurable
      (generalRelativisticHamiltonian potential metric m c)) :
    Measurable (generalRelativisticBoltzmannWeight potential metric m c) := by
  exact ENNReal.measurable_ofReal.comp (hH.neg.exp)

/-- The GR Boltzmann density factors pointwise into its position density and
complete conditional momentum density. -/
theorem generalRelativisticBoltzmannWeight_eq_position_mul_momentum
    (potential : Position ι → ℝ)
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (z : PhaseSpace ι) :
    generalRelativisticBoltzmannWeight potential metric m c z =
      positionBoltzmannWeight potential z.1 *
        riemannianRelativisticMomentumWeight metric m c z.1 z.2 := by
  unfold generalRelativisticBoltzmannWeight positionBoltzmannWeight
    riemannianRelativisticMomentumWeight generalRelativisticHamiltonian
  rw [show -(potential z.1 +
      riemannianRelativisticKineticEnergy metric m c z.1 z.2) =
      -potential z.1 +
        -riemannianRelativisticKineticEnergy metric m c z.1 z.2 by ring,
    Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]

theorem measurable_riemannianRelativisticMomentumWeight
    {potential : Position ι → ℝ} (hpotential : Measurable potential)
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (hH : Measurable
      (generalRelativisticHamiltonian potential metric m c)) :
    Measurable (Function.uncurry
      (riemannianRelativisticMomentumWeight metric m c)) := by
  have hkinetic : Measurable fun z : PhaseSpace ι =>
      riemannianRelativisticKineticEnergy metric m c z.1 z.2 := by
    have := hH.sub (hpotential.comp measurable_fst)
    rw [show (fun z : PhaseSpace ι =>
        riemannianRelativisticKineticEnergy metric m c z.1 z.2) =
        generalRelativisticHamiltonian potential metric m c -
          potential ∘ Prod.fst by
      funext z
      simp [generalRelativisticHamiltonian]]
    exact this
  exact ENNReal.measurable_ofReal.comp (hkinetic.neg.exp)

/-- The (possibly unnormalized) joint GR-HMC target on phase space. -/
noncomputable def generalRelativisticPhaseTarget
    (potential : Position ι → ℝ)
    (metric : FactoredRiemannianMetric ι) (m c : ℝ) :
    Measure (PhaseSpace ι) :=
  phaseVolume.withDensity
    (generalRelativisticBoltzmannWeight potential metric m c)

/-- The GR phase target is the position Boltzmann measure augmented by the
unnormalized conditional momentum density. -/
theorem generalRelativisticPhaseTarget_eq_position_withDensity
    {potential : Position ι → ℝ} (hpotential : Measurable potential)
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (hH : Measurable
      (generalRelativisticHamiltonian potential metric m c)) :
    generalRelativisticPhaseTarget potential metric m c =
      ((positionBoltzmannTarget potential).prod
        (volume : Measure (Momentum ι))).withDensity
          (Function.uncurry
            (riemannianRelativisticMomentumWeight metric m c)) := by
  let positionOnPhase : PhaseSpace ι → ENNReal :=
    fun z => positionBoltzmannWeight potential z.1
  let momentumOnPhase : PhaseSpace ι → ENNReal :=
    Function.uncurry (riemannianRelativisticMomentumWeight metric m c)
  have hp : Measurable positionOnPhase :=
    (measurable_positionBoltzmannWeight hpotential).comp measurable_fst
  have hm : Measurable momentumOnPhase :=
    measurable_riemannianRelativisticMomentumWeight hpotential metric m c hH
  rw [positionBoltzmannTarget,
    prod_withDensity_left (measurable_positionBoltzmannWeight hpotential)]
  change generalRelativisticPhaseTarget potential metric m c =
    (phaseVolume.withDensity positionOnPhase).withDensity momentumOnPhase
  rw [← withDensity_mul phaseVolume hp hm]
  unfold generalRelativisticPhaseTarget
  congr 1
  funext z
  exact generalRelativisticBoltzmannWeight_eq_position_mul_momentum
    potential metric m c z

/-- Endpoint-Metropolis generalized HMC on phase space. -/
noncomputable def endpointMetropolisGRHMC
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (potential : Position ι → ℝ)
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hmeasurable : selection.IsMeasurable) (ε : ℝ) :
    Kernel (PhaseSpace ι) (PhaseSpace ι) :=
  deterministicMetropolis
    (generalRelativisticBoltzmannWeight potential metric m c)
    (generalizedLeapfrogEndpoint selection ε)
    (measurable_generalizedLeapfrogEndpoint selection hmeasurable ε)

theorem endpointMetropolisGRHMC_isMarkov
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (potential : Position ι → ℝ)
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid)
    (hH : Measurable
      (generalRelativisticHamiltonian potential metric m c))
    (ε : ℝ) :
    IsMarkovKernel
      (endpointMetropolisGRHMC potential metric m c selection
        hvalid.measurable ε) := by
  exact deterministicMetropolis_isMarkov _ _
    (measurable_generalRelativisticBoltzmannWeight potential metric m c hH)
    (measurable_generalizedLeapfrogEndpoint selection hvalid.measurable ε)

/-- A valid generalized-leapfrog endpoint Metropolis kernel is reversible
with respect to the full, position-dependent GR Boltzmann target. -/
theorem endpointMetropolisGRHMC_isReversible
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (potential : Position ι → ℝ)
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid)
    (hH : Measurable
      (generalRelativisticHamiltonian potential metric m c))
    (ε : ℝ) :
    (endpointMetropolisGRHMC potential metric m c selection
      hvalid.measurable ε).IsReversible
        (generalRelativisticPhaseTarget potential metric m c) := by
  exact deterministicMetropolis_isReversible phaseVolume _ _ _
    (measurable_generalRelativisticBoltzmannWeight potential metric m c hH)
    (generalRelativisticBoltzmannWeight_ne_zero potential metric m c)
    (generalRelativisticBoltzmannWeight_ne_top potential metric m c)
    (generalizedLeapfrogEndpoint_involutive selection hvalid ε)
    (measurePreserving_generalizedLeapfrogEndpoint selection hvalid ε)

/-- Exact joint-target invariance of endpoint-Metropolis GR-HMC, conditional
on the complete generalized-leapfrog validity certificate. -/
theorem endpointMetropolisGRHMC_invariant
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (potential : Position ι → ℝ)
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid)
    (hH : Measurable
      (generalRelativisticHamiltonian potential metric m c))
    (ε : ℝ) :
    (endpointMetropolisGRHMC potential metric m c selection
      hvalid.measurable ε).Invariant
        (generalRelativisticPhaseTarget potential metric m c) := by
  exact deterministicMetropolis_invariant phaseVolume _ _ _
    (measurable_generalRelativisticBoltzmannWeight potential metric m c hH)
    (generalRelativisticBoltzmannWeight_ne_zero potential metric m c)
    (generalRelativisticBoltzmannWeight_ne_top potential metric m c)
    (generalizedLeapfrogEndpoint_involutive selection hvalid ε)
    (measurePreserving_generalizedLeapfrogEndpoint selection hvalid ε)

/-- The user-facing endpoint-corrected GR-HMC kernel: draw momentum from the
position-dependent conditional law, perform the phase transition, and discard
momentum. -/
noncomputable def positionEndpointMetropolisGRHMC
    [Nonempty ι] [DecidableEq ι]
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (potential : Position ι → ℝ)
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (hm : 0 < m) (hc : 0 < c)
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid)
    (hmeasurableMomentum :
      IsMeasurableRiemannianMomentumFamily metric m c hm hc)
    (ε : ℝ) : Kernel (Position ι) (Position ι) :=
  (endpointMetropolisGRHMC potential metric m c selection
      hvalid.measurable ε ∘ₖ
    riemannianPositionMomentumLift metric m c hm hc hmeasurableMomentum).map
      (Prod.fst : PhaseSpace ι → Position ι)

theorem positionEndpointMetropolisGRHMC_isMarkov
    [Nonempty ι] [DecidableEq ι]
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (potential : Position ι → ℝ)
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (hm : 0 < m) (hc : 0 < c)
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid)
    (hH : Measurable
      (generalRelativisticHamiltonian potential metric m c))
    (hmeasurableMomentum :
      IsMeasurableRiemannianMomentumFamily metric m c hm hc)
    (ε : ℝ) :
    IsMarkovKernel
      (positionEndpointMetropolisGRHMC potential metric m c hm hc selection
        hvalid hmeasurableMomentum ε) := by
  unfold positionEndpointMetropolisGRHMC
  letI : IsMarkovKernel
      (endpointMetropolisGRHMC potential metric m c selection
        hvalid.measurable ε) :=
    endpointMetropolisGRHMC_isMarkov potential metric m c selection hvalid hH ε
  exact Kernel.IsMarkovKernel.map _ measurable_fst

/-- Compatibility equation identifying the normalized conditional momentum
kernel and a position target with the GR Boltzmann phase measure. This is the
measure-theoretic form of the metric determinant/Jacobian calculation. -/
def IsCompatibleGRPositionTarget
    [Nonempty ι] [DecidableEq ι]
    (potential : Position ι → ℝ)
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (hm : 0 < m) (hc : 0 < c)
    (hmeasurableMomentum :
      IsMeasurableRiemannianMomentumFamily metric m c hm hc)
    (positionTarget : Measure (Position ι)) : Prop :=
  positionTarget ⊗ₘ
      riemannianMomentumKernel metric m c hm hc hmeasurableMomentum =
    generalRelativisticPhaseTarget potential metric m c

/-- The natural unnormalized position target paired with normalized
relativistic momentum.  The partition factor compensates for normalizing the
momentum rows while leaving the phase Boltzmann measure unnormalized. -/
noncomputable def generalRelativisticPositionTarget
    [Nonempty ι]
    (potential : Position ι → ℝ) (m c : ℝ)
    (hm : 0 < m) (hc : 0 < c) : Measure (Position ι) :=
  euclideanRelativisticMomentumPartition ι m c hm hc •
    positionBoltzmannTarget potential

/-- Under factor-volume compatibility, every normalized conditional momentum
probability has density `Z⁻¹ exp(-K_G(q,p))` with respect to momentum volume. -/
theorem riemannianRelativisticMomentumProbability_eq_withDensity
    [Nonempty ι] [DecidableEq ι]
    (metric : FactoredRiemannianMetric ι)
    (hvolume : metric.HasCompatibleFactorVolume)
    (m c : ℝ) (hm : 0 < m) (hc : 0 < c)
    (hweight : Measurable (Function.uncurry
      (riemannianRelativisticMomentumWeight metric m c)))
    (q : Position ι) :
    (riemannianRelativisticMomentumProbability metric m c hm hc q :
      Measure (Momentum ι)) =
      (volume : Measure (Momentum ι)).withDensity
        (fun p =>
          (euclideanRelativisticMomentumPartition ι m c hm hc : ENNReal)⁻¹ *
            riemannianRelativisticMomentumWeight metric m c q p) := by
  rw [riemannianRelativisticMomentumProbability_toMeasure,
    riemannianRelativisticMomentumMeasure_eq_withDensity metric hvolume]
  let a : ENNReal :=
    (euclideanRelativisticMomentumPartition ι m c hm hc : ENNReal)⁻¹
  have ha :
      (((euclideanRelativisticMomentumPartition ι m c hm hc)⁻¹ : NNReal) :
        ENNReal) = a := by
    simp [a, euclideanRelativisticMomentumPartition_ne_zero]
  rw [ENNReal.smul_def, ha]
  change a • (volume : Measure (Momentum ι)).withDensity
      (riemannianRelativisticMomentumWeight metric m c q) =
    (volume : Measure (Momentum ι)).withDensity
      (a • riemannianRelativisticMomentumWeight metric m c q)
  exact (withDensity_smul a
    (hweight.comp measurable_prodMk_left)).symm

/-- The factor-volume identity and joint measurability of the kinetic density
imply measurability of the normalized conditional momentum family. -/
theorem isMeasurableRiemannianMomentumFamily_of_factorVolume
    [Nonempty ι] [DecidableEq ι]
    (metric : FactoredRiemannianMetric ι)
    (hvolume : metric.HasCompatibleFactorVolume)
    (m c : ℝ) (hm : 0 < m) (hc : 0 < c)
    (hweight : Measurable (Function.uncurry
      (riemannianRelativisticMomentumWeight metric m c))) :
    IsMeasurableRiemannianMomentumFamily metric m c hm hc := by
  intro s hs
  let a : ENNReal :=
    (euclideanRelativisticMomentumPartition ι m c hm hc : ENNReal)⁻¹
  let densityKernel :=
    (Kernel.const (Position ι) (volume : Measure (Momentum ι))).withDensity
      (fun q p => a * riemannianRelativisticMomentumWeight metric m c q p)
  have had : Measurable (Function.uncurry (fun q p =>
      a * riemannianRelativisticMomentumWeight metric m c q p)) :=
    measurable_const.mul hweight
  have hENN : Measurable fun q : Position ι =>
      ((riemannianRelativisticMomentumProbability metric m c hm hc q s :
        NNReal) : ENNReal) := by
    rw [show (fun q : Position ι =>
        ((riemannianRelativisticMomentumProbability metric m c hm hc q s :
          NNReal) : ENNReal)) = fun q => densityKernel q s by
      funext q
      rw [Kernel.withDensity_apply _ had]
      change ((riemannianRelativisticMomentumProbability metric m c hm hc q s :
          NNReal) : ENNReal) =
        ((volume : Measure (Momentum ι)).withDensity (fun p =>
          (euclideanRelativisticMomentumPartition ι m c hm hc : ENNReal)⁻¹ *
            riemannianRelativisticMomentumWeight metric m c q p)) s
      simpa only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
        congrArg (fun μ : Measure (Momentum ι) => μ s)
          (riemannianRelativisticMomentumProbability_eq_withDensity metric
            hvolume m c hm hc hweight q)]
    exact densityKernel.measurable_coe hs
  have hNN := ENNReal.measurable_toNNReal.comp hENN
  convert hNN using 1
  funext q
  rw [← ENNReal.coe_inj]
  simp

/-- Kernel-level restatement of the normalized conditional density theorem. -/
theorem riemannianMomentumKernel_apply_eq_withDensity
    [Nonempty ι] [DecidableEq ι]
    (metric : FactoredRiemannianMetric ι)
    (hvolume : metric.HasCompatibleFactorVolume)
    (m c : ℝ) (hm : 0 < m) (hc : 0 < c)
    (hmeasurableMomentum :
      IsMeasurableRiemannianMomentumFamily metric m c hm hc)
    (hweight : Measurable (Function.uncurry
      (riemannianRelativisticMomentumWeight metric m c)))
    (q : Position ι) :
    riemannianMomentumKernel metric m c hm hc hmeasurableMomentum q =
      (volume : Measure (Momentum ι)).withDensity
        (fun p =>
          (euclideanRelativisticMomentumPartition ι m c hm hc : ENNReal)⁻¹ *
            riemannianRelativisticMomentumWeight metric m c q p) := by
  exact riemannianRelativisticMomentumProbability_eq_withDensity metric hvolume
    m c hm hc hweight q

/-- The exact factor-volume certificate discharges the general
position/conditional-momentum compatibility equation. -/
theorem isCompatibleGRPositionTarget_of_factorVolume
    [Nonempty ι] [DecidableEq ι]
    {potential : Position ι → ℝ} (hpotential : Measurable potential)
    (metric : FactoredRiemannianMetric ι)
    (hvolume : metric.HasCompatibleFactorVolume)
    (m c : ℝ) (hm : 0 < m) (hc : 0 < c)
    (hH : Measurable
      (generalRelativisticHamiltonian potential metric m c))
    (hmeasurableMomentum :
      IsMeasurableRiemannianMomentumFamily metric m c hm hc) :
    IsCompatibleGRPositionTarget potential metric m c hm hc
      hmeasurableMomentum
      (generalRelativisticPositionTarget potential m c hm hc) := by
  let Z : ENNReal :=
    euclideanRelativisticMomentumPartition ι m c hm hc
  let a : ENNReal := Z⁻¹
  let weight := riemannianRelativisticMomentumWeight metric m c
  have hw : Measurable (Function.uncurry weight) :=
    measurable_riemannianRelativisticMomentumWeight hpotential metric m c hH
  let densityKernel :=
    (Kernel.const (Position ι) (volume : Measure (Momentum ι))).withDensity
      (fun q p => a * weight q p)
  have had : Measurable (Function.uncurry (fun q p => a * weight q p)) :=
    measurable_const.mul hw
  have hrows :
      (riemannianMomentumKernel metric m c hm hc hmeasurableMomentum :
        Position ι → Measure (Momentum ι)) = densityKernel := by
    funext q
    rw [Kernel.withDensity_apply _ had]
    exact riemannianMomentumKernel_apply_eq_withDensity metric hvolume m c
      hm hc hmeasurableMomentum hw q
  letI : SFinite (positionBoltzmannTarget potential) := by
    unfold positionBoltzmannTarget
    infer_instance
  have hk : riemannianMomentumKernel metric m c hm hc hmeasurableMomentum =
      densityKernel := by
    ext q s hs
    have hq := congrFun hrows q
    rw [hq]
  letI : IsMarkovKernel densityKernel := by
    rw [← hk]
    infer_instance
  unfold IsCompatibleGRPositionTarget generalRelativisticPositionTarget
  rw [hk]
  change (Z • positionBoltzmannTarget potential) ⊗ₘ densityKernel = _
  rw [Measure.compProd_smul_left, Measure.compProd_withDensity had,
    Measure.compProd_const]
  change Z • ((positionBoltzmannTarget potential).prod
      (volume : Measure (Momentum ι))).withDensity
        (Function.uncurry (fun q p => a * weight q p)) = _
  rw [← withDensity_smul Z had]
  rw [generalRelativisticPhaseTarget_eq_position_withDensity
    hpotential metric m c hH]
  congr 1
  funext z
  change Z * (a * weight z.1 z.2) = weight z.1 z.2
  rw [← mul_assoc]
  have hZ0 : Z ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr
      (euclideanRelativisticMomentumPartition_ne_zero ι m c hm hc)
  have hZtop : Z ≠ ∞ := ENNReal.coe_ne_top
  rw [ENNReal.mul_inv_cancel hZ0 hZtop, one_mul]

/-- Under the explicit target/conditional compatibility equation, the full
position-space endpoint GR-HMC algorithm preserves the intended position
target. -/
theorem positionEndpointMetropolisGRHMC_invariant
    [Nonempty ι] [DecidableEq ι]
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (potential : Position ι → ℝ)
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (hm : 0 < m) (hc : 0 < c)
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid)
    (hH : Measurable
      (generalRelativisticHamiltonian potential metric m c))
    (hmeasurableMomentum :
      IsMeasurableRiemannianMomentumFamily metric m c hm hc)
    (ε : ℝ)
    (positionTarget : Measure (Position ι)) [SFinite positionTarget]
    (hcompat : IsCompatibleGRPositionTarget potential metric m c hm hc
      hmeasurableMomentum positionTarget) :
    (positionEndpointMetropolisGRHMC potential metric m c hm hc selection
      hvalid hmeasurableMomentum ε).Invariant positionTarget := by
  let momentumKernel :=
    riemannianMomentumKernel metric m c hm hc hmeasurableMomentum
  let phaseKernel := endpointMetropolisGRHMC potential metric m c selection
    hvalid.measurable ε
  letI : IsMarkovKernel phaseKernel :=
    endpointMetropolisGRHMC_isMarkov potential metric m c selection hvalid hH ε
  change (Mcmc.Kernel.liftEvolveProject
    (riemannianPositionMomentumLift metric m c hm hc hmeasurableMomentum)
    phaseKernel (Prod.fst : PhaseSpace ι → Position ι)
    measurable_fst).Invariant positionTarget
  have hphase := endpointMetropolisGRHMC_invariant potential metric m c
    selection hvalid hH ε
  change phaseKernel.Invariant
    (generalRelativisticPhaseTarget potential metric m c) at hphase
  change positionTarget ⊗ₘ momentumKernel =
    generalRelativisticPhaseTarget potential metric m c at hcompat
  rw [← hcompat] at hphase
  unfold riemannianPositionMomentumLift
  exact Mcmc.Kernel.compProdEvolveFst_invariant positionTarget
    momentumKernel phaseKernel hphase

end Mcmc.Relativistic
