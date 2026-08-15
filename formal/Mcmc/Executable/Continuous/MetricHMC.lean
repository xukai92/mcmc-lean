import Mcmc.Executable.Continuous.HMC

/-!
# Constant-metric endpoint HMC

Exact finite-dimensional foundations for diagonal and dense constant mass
matrices. The proofs use only that velocity is measurable and odd; matrix
positive-definiteness is needed separately to construct its Gaussian momentum
law and is checked by the Julia public API.
-/

namespace Mcmc.Executable.Continuous

open Mcmc.Hamiltonian MeasureTheory

variable {ι : Type*} [Fintype ι]

def metricDrift (velocity : Momentum ι → Position ι) (ε : ℝ)
    (q : Position ι) (p : Momentum ι) : Position ι :=
  q + ε • velocity p

noncomputable def metricLeapfrog (velocity : Momentum ι → Position ι)
    (gradient : Position ι → Momentum ι) (ε : ℝ) (z : PhaseSpace ι) :
    PhaseSpace ι :=
  let pHalf := z.2 - (ε / 2) • gradient z.1
  let qNext := metricDrift velocity ε z.1 pHalf
  (qNext, pHalf - (ε / 2) • gradient qNext)

noncomputable def metricLeapfrogN (velocity : Momentum ι → Position ι)
    (gradient : Position ι → Momentum ι) (ε : ℝ) : Nat → PhaseSpace ι → PhaseSpace ι
  | 0, z => z
  | n + 1, z => metricLeapfrog velocity gradient ε
      (metricLeapfrogN velocity gradient ε n z)

noncomputable def metricDriftPhase (velocity : Momentum ι → Position ι)
    (ε : ℝ) (z : PhaseSpace ι) : PhaseSpace ι :=
  (metricDrift velocity ε z.1 z.2, z.2)

omit [Fintype ι] in theorem measurable_metricDriftPhase {velocity : Momentum ι → Position ι}
    (hvelocity : Measurable velocity) (ε : ℝ) :
    Measurable (metricDriftPhase velocity ε) := by
  unfold metricDriftPhase metricDrift
  fun_prop

theorem measurePreserving_metricDriftPhase
    {velocity : Momentum ι → Position ι} (hvelocity : Measurable velocity)
    (ε : ℝ) :
    MeasurePreserving (metricDriftPhase velocity ε) phaseVolume phaseVolume := by
  let shear : Momentum ι × Position ι → Momentum ι × Position ι :=
    fun z => (z.1, z.2 + ε • velocity z.1)
  have hshear : MeasurePreserving shear
      ((volume : Measure (Momentum ι)).prod (volume : Measure (Position ι)))
      ((volume : Measure (Momentum ι)).prod (volume : Measure (Position ι))) := by
    exact (MeasurePreserving.id (volume : Measure (Momentum ι))).skew_product
      (g := fun p q => q + ε • velocity p) (by fun_prop)
      (ae_of_all _ fun p =>
        map_add_right_eq_self (volume : Measure (Position ι)) (ε • velocity p))
  have h := (Measure.measurePreserving_swap (μ := (volume : Measure (Momentum ι)))
    (ν := (volume : Measure (Position ι)))).comp
      (hshear.comp Measure.measurePreserving_swap)
  apply h.congr (measurable_metricDriftPhase hvelocity ε)
  filter_upwards [] with z
  rfl

theorem measurePreserving_metricLeapfrog
    {velocity : Momentum ι → Position ι} {gradient : Position ι → Momentum ι}
    (hvelocity : Measurable velocity) (hgradient : Measurable gradient) (ε : ℝ) :
    MeasurePreserving (metricLeapfrog velocity gradient ε) phaseVolume phaseVolume := by
  change MeasurePreserving
    (Mcmc.Hamiltonian.kickPhase gradient ε ∘ metricDriftPhase velocity ε ∘
      Mcmc.Hamiltonian.kickPhase gradient ε) phaseVolume phaseVolume
  exact (measurePreserving_kickPhase hgradient ε).comp
    ((measurePreserving_metricDriftPhase hvelocity ε).comp
      (measurePreserving_kickPhase hgradient ε))

theorem measurePreserving_metricLeapfrogN
    {velocity : Momentum ι → Position ι} {gradient : Position ι → Momentum ι}
    (hvelocity : Measurable velocity) (hgradient : Measurable gradient)
    (ε : ℝ) (steps : Nat) :
    MeasurePreserving (metricLeapfrogN velocity gradient ε steps)
      phaseVolume phaseVolume := by
  induction steps with
  | zero => exact MeasurePreserving.id _
  | succ steps ih =>
      exact (measurePreserving_metricLeapfrog hvelocity hgradient ε).comp ih

/-- A dense constant inverse-mass operator is represented abstractly as a
measurable odd linear velocity map; matrix multiplication is one instance. -/
structure ConstantMetric (ι : Type*) [Fintype ι] where
  velocity : Momentum ι → Position ι
  measurable_velocity : Measurable velocity
  velocity_odd : ∀ p, velocity (-p) = -velocity p

theorem metricLeapfrog_neg_comp (metric : ConstantMetric ι)
    (gradient : Position ι → Momentum ι) (ε : ℝ) (z : PhaseSpace ι) :
    metricLeapfrog metric.velocity gradient (-ε)
        (metricLeapfrog metric.velocity gradient ε z) = z := by
  rcases z with ⟨q, p⟩
  simp only [metricLeapfrog, metricDrift]
  let pHalf := p - (ε / 2) • gradient q
  let qNext := q + ε • metric.velocity pHalf
  have hpHalf :
      pHalf - (ε / 2) • gradient qNext - ((-ε) / 2) • gradient qNext =
        pHalf := by module
  rw [hpHalf]
  have hq : qNext + (-ε) • metric.velocity pHalf = q := by
    dsimp [qNext]
    module
  rw [hq]
  dsimp [pHalf]
  congr 1
  module

theorem momentumFlip_metricLeapfrog_momentumFlip
    (metric : ConstantMetric ι) (gradient : Position ι → Momentum ι)
    (ε : ℝ) (z : PhaseSpace ι) :
    momentumFlip (metricLeapfrog metric.velocity gradient ε (momentumFlip z)) =
      metricLeapfrog metric.velocity gradient (-ε) z := by
  rcases z with ⟨q, p⟩
  simp only [momentumFlip, metricLeapfrog, metricDrift]
  let pReverse := p - ((-ε) / 2) • gradient q
  have hhalf : -p - (ε / 2) • gradient q = -pReverse := by
    dsimp [pReverse]
    module
  rw [hhalf, metric.velocity_odd]
  have hposition : q + ε • -metric.velocity pReverse =
      q + (-ε) • metric.velocity pReverse := by module
  rw [hposition]
  dsimp [pReverse]
  congr 1
  module

/-- Constant-metric leapfrog as an exact permutation, with negative step as
its inverse. -/
noncomputable def metricLeapfrogPerm (metric : ConstantMetric ι)
    (gradient : Position ι → Momentum ι) (ε : ℝ) : Equiv.Perm (PhaseSpace ι) where
  toFun := metricLeapfrog metric.velocity gradient ε
  invFun := metricLeapfrog metric.velocity gradient (-ε)
  left_inv := metricLeapfrog_neg_comp metric gradient ε
  right_inv := by
    intro z
    simpa only [neg_neg] using metricLeapfrog_neg_comp metric gradient (-ε) z

theorem metricLeapfrogN_eq_pow (metric : ConstantMetric ι)
    (gradient : Position ι → Momentum ι) (ε : ℝ) (steps : Nat) :
    metricLeapfrogN metric.velocity gradient ε steps =
      ⇑((metricLeapfrogPerm metric gradient ε) ^ steps) := by
  funext z
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [pow_succ']
      simp only [metricLeapfrogN, Equiv.Perm.coe_mul, Function.comp_apply,
        metricLeapfrogPerm]
      rw [ih]
      rfl

theorem momentumFlip_metricLeapfrogN_momentumFlip
    (metric : ConstantMetric ι) (gradient : Position ι → Momentum ι)
    (ε : ℝ) (steps : Nat) (z : PhaseSpace ι) :
    momentumFlip
        (metricLeapfrogN metric.velocity gradient ε steps (momentumFlip z)) =
      metricLeapfrogN metric.velocity gradient (-ε) steps z := by
  induction steps generalizing z with
  | zero => simp [metricLeapfrogN, momentumFlip]
  | succ steps ih =>
      simp only [metricLeapfrogN]
      have h := momentumFlip_metricLeapfrog_momentumFlip metric gradient ε
        (momentumFlip
          (metricLeapfrogN metric.velocity gradient ε steps (momentumFlip z)))
      simp only [momentumFlip_involutive] at h
      rw [h, ih]

/-- Momentum-flipped constant-metric trajectory proposal. -/
noncomputable def endpointMetricLeapfrogNProposal
    (metric : ConstantMetric ι) (gradient : Position ι → Momentum ι)
    (ε : ℝ) (steps : Nat) (z : PhaseSpace ι) : PhaseSpace ι :=
  momentumFlip (metricLeapfrogN metric.velocity gradient ε steps z)

theorem endpointMetricLeapfrogNProposal_involutive
    (metric : ConstantMetric ι) (gradient : Position ι → Momentum ι)
    (ε : ℝ) (steps : Nat) :
    Function.Involutive
      (endpointMetricLeapfrogNProposal metric gradient ε steps) := by
  intro z
  simp only [endpointMetricLeapfrogNProposal]
  rw [momentumFlip_metricLeapfrogN_momentumFlip]
  rw [metricLeapfrogN_eq_pow, metricLeapfrogN_eq_pow]
  change (((metricLeapfrogPerm metric gradient ε) ^ steps)⁻¹)
      (((metricLeapfrogPerm metric gradient ε) ^ steps) z) = z
  exact Equiv.apply_symm_apply _ _

theorem measurable_metricLeapfrog
    (metric : ConstantMetric ι) {gradient : Position ι → Momentum ι}
    (hgradient : Measurable gradient) (ε : ℝ) :
    Measurable (metricLeapfrog metric.velocity gradient ε) := by
  change Measurable
    (Mcmc.Hamiltonian.kickPhase gradient ε ∘ metricDriftPhase metric.velocity ε ∘
      Mcmc.Hamiltonian.kickPhase gradient ε)
  exact (measurable_kickPhase hgradient ε).comp
    ((measurable_metricDriftPhase metric.measurable_velocity ε).comp
      (measurable_kickPhase hgradient ε))

theorem measurable_metricLeapfrogN
    (metric : ConstantMetric ι) {gradient : Position ι → Momentum ι}
    (hgradient : Measurable gradient) (ε : ℝ) (steps : Nat) :
    Measurable (metricLeapfrogN metric.velocity gradient ε steps) := by
  induction steps with
  | zero => exact measurable_id
  | succ steps ih =>
      exact (measurable_metricLeapfrog metric hgradient ε).comp ih

theorem measurable_endpointMetricLeapfrogNProposal
    (metric : ConstantMetric ι) {gradient : Position ι → Momentum ι}
    (hgradient : Measurable gradient) (ε : ℝ) (steps : Nat) :
    Measurable (endpointMetricLeapfrogNProposal metric gradient ε steps) :=
  measurable_momentumFlip.comp
    (measurable_metricLeapfrogN metric hgradient ε steps)

theorem measurePreserving_endpointMetricLeapfrogNProposal
    (metric : ConstantMetric ι) {gradient : Position ι → Momentum ι}
    (hgradient : Measurable gradient) (ε : ℝ) (steps : Nat) :
    MeasurePreserving (endpointMetricLeapfrogNProposal metric gradient ε steps)
      phaseVolume phaseVolume :=
  measurePreserving_momentumFlip.comp
    (measurePreserving_metricLeapfrogN metric.measurable_velocity hgradient ε steps)

noncomputable def metricBoltzmannWeight
    (potential : Position ι → ℝ) (kinetic : Momentum ι → ℝ)
    (z : PhaseSpace ι) : ENNReal :=
  ENNReal.ofReal (Real.exp (-(potential z.1 + kinetic z.2)))

noncomputable def metricPositionBoltzmannWeight
    (potential : Position ι → ℝ) (q : Position ι) : ENNReal :=
  ENNReal.ofReal (Real.exp (-potential q))

noncomputable def metricKineticBoltzmannWeight
    (kinetic : Momentum ι → ℝ) (p : Momentum ι) : ENNReal :=
  ENNReal.ofReal (Real.exp (-kinetic p))

noncomputable def metricPositionBoltzmannTarget
    (potential : Position ι → ℝ) : Measure (Position ι) :=
  volume.withDensity (metricPositionBoltzmannWeight potential)

noncomputable def metricKineticBoltzmannTarget
    (kinetic : Momentum ι → ℝ) : Measure (Momentum ι) :=
  volume.withDensity (metricKineticBoltzmannWeight kinetic)

omit [Fintype ι] in theorem metricBoltzmannWeight_eq_mul
    (potential : Position ι → ℝ) (kinetic : Momentum ι → ℝ)
    (z : PhaseSpace ι) :
    metricBoltzmannWeight potential kinetic z =
      metricPositionBoltzmannWeight potential z.1 *
        metricKineticBoltzmannWeight kinetic z.2 := by
  rw [metricBoltzmannWeight, metricPositionBoltzmannWeight,
    metricKineticBoltzmannWeight]
  rw [show -(potential z.1 + kinetic z.2) =
    -potential z.1 + -kinetic z.2 by ring, Real.exp_add,
    ENNReal.ofReal_mul (Real.exp_nonneg _)]

theorem metricPhaseBoltzmannTarget_eq_prod
    {potential : Position ι → ℝ} {kinetic : Momentum ι → ℝ}
    (hpotential : Measurable potential) (hkinetic : Measurable kinetic) :
    phaseVolume.withDensity (metricBoltzmannWeight potential kinetic) =
      (metricPositionBoltzmannTarget potential).prod
        (metricKineticBoltzmannTarget kinetic) := by
  rw [metricPositionBoltzmannTarget, metricKineticBoltzmannTarget,
    prod_withDensity
      (f := metricPositionBoltzmannWeight potential)
      (g := metricKineticBoltzmannWeight kinetic)
      (by exact ENNReal.measurable_ofReal.comp hpotential.neg.exp)
      (by exact ENNReal.measurable_ofReal.comp hkinetic.neg.exp)]
  unfold phaseVolume
  congr 1
  funext z
  exact metricBoltzmannWeight_eq_mul potential kinetic z

omit [Fintype ι] in theorem measurable_metricBoltzmannWeight
    {potential : Position ι → ℝ} {kinetic : Momentum ι → ℝ}
    (hpotential : Measurable potential) (hkinetic : Measurable kinetic) :
    Measurable (metricBoltzmannWeight potential kinetic) := by
  exact ENNReal.measurable_ofReal.comp
    (((hpotential.comp measurable_fst).add
      (hkinetic.comp measurable_snd)).neg.exp)

noncomputable def endpointMetricHmcPhaseKernel
    (metric : ConstantMetric ι) (potential : Position ι → ℝ)
    (kinetic : Momentum ι → ℝ) (gradient : Position ι → Momentum ι)
    (ε : ℝ) (steps : Nat) (hgradient : Measurable gradient) :
    ProbabilityTheory.Kernel (PhaseSpace ι) (PhaseSpace ι) :=
  Mcmc.Kernel.deterministicMetropolis (metricBoltzmannWeight potential kinetic)
    (endpointMetricLeapfrogNProposal metric gradient ε steps)
    (measurable_endpointMetricLeapfrogNProposal metric hgradient ε steps)

theorem endpointMetricHmcPhaseKernel_isMarkov
    (metric : ConstantMetric ι) (potential : Position ι → ℝ)
    (kinetic : Momentum ι → ℝ) (gradient : Position ι → Momentum ι)
    (ε : ℝ) (steps : Nat) (hpotential : Measurable potential)
    (hkinetic : Measurable kinetic) (hgradient : Measurable gradient) :
    ProbabilityTheory.IsMarkovKernel
      (endpointMetricHmcPhaseKernel metric potential kinetic gradient ε steps
        hgradient) := by
  unfold endpointMetricHmcPhaseKernel
  exact Mcmc.Kernel.deterministicMetropolis_isMarkov _ _
    (measurable_metricBoltzmannWeight hpotential hkinetic)
    (measurable_endpointMetricLeapfrogNProposal metric hgradient ε steps)

theorem endpointMetricHmcPhaseKernel_invariant
    (metric : ConstantMetric ι)
    {potential : Position ι → ℝ} {kinetic : Momentum ι → ℝ}
    {gradient : Position ι → Momentum ι}
    (hpotential : Measurable potential) (hkinetic : Measurable kinetic)
    (hgradient : Measurable gradient) (ε : ℝ) (steps : Nat) :
    (endpointMetricHmcPhaseKernel metric potential kinetic gradient ε steps
      hgradient).Invariant
      (phaseVolume.withDensity (metricBoltzmannWeight potential kinetic)) := by
  unfold endpointMetricHmcPhaseKernel
  apply Mcmc.Kernel.deterministicMetropolis_invariant
  · exact measurable_metricBoltzmannWeight hpotential hkinetic
  · intro z
    exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  · intro z
    simp [metricBoltzmannWeight]
  · exact endpointMetricLeapfrogNProposal_involutive metric gradient ε steps
  · exact measurePreserving_endpointMetricLeapfrogNProposal metric hgradient ε steps

noncomputable def endpointMetricHmcPositionKernel
    (metric : ConstantMetric ι) (potential : Position ι → ℝ)
    (kinetic : Momentum ι → ℝ) (gradient : Position ι → Momentum ι)
    (momentumTarget : Measure (Momentum ι)) (ε : ℝ) (steps : Nat)
    (_hpotential : Measurable potential) (_hkinetic : Measurable kinetic)
    (hgradient : Measurable gradient) :
    ProbabilityTheory.Kernel (Position ι) (Position ι) := by
  letI := endpointMetricHmcPhaseKernel_isMarkov metric potential kinetic gradient
    ε steps _hpotential _hkinetic hgradient
  exact Mcmc.Kernel.liftEvolveProject
    (positionMomentumLift momentumTarget)
    (endpointMetricHmcPhaseKernel metric potential kinetic gradient ε steps hgradient)
    (Prod.fst : PhaseSpace ι → Position ι) measurable_fst

/-- Refresh–evolve–project invariance for any momentum law whose product with
the position target is the metric Boltzmann phase measure. -/
theorem endpointMetricHmcPositionKernel_invariant
    (metric : ConstantMetric ι)
    {potential : Position ι → ℝ} {kinetic : Momentum ι → ℝ}
    {gradient : Position ι → Momentum ι}
    (hpotential : Measurable potential) (hkinetic : Measurable kinetic)
    (hgradient : Measurable gradient) (momentumTarget : Measure (Momentum ι))
    [IsProbabilityMeasure momentumTarget]
    (positionTarget : Measure (Position ι)) [SFinite positionTarget]
    (ε : ℝ) (steps : Nat)
    (hfactor : positionTarget.prod momentumTarget =
      phaseVolume.withDensity (metricBoltzmannWeight potential kinetic)) :
    (endpointMetricHmcPositionKernel metric potential kinetic gradient
      momentumTarget ε steps hpotential hkinetic hgradient).Invariant
      positionTarget := by
  change (Mcmc.Kernel.liftEvolveProject
    (positionMomentumLift momentumTarget)
    (endpointMetricHmcPhaseKernel metric potential kinetic gradient ε steps hgradient)
    (Prod.fst : PhaseSpace ι → Position ι) measurable_fst).Invariant positionTarget
  have hphase := endpointMetricHmcPhaseKernel_invariant metric hpotential
    hkinetic hgradient ε steps
  rw [← hfactor] at hphase
  unfold positionMomentumLift
  apply Mcmc.Kernel.compProdEvolveFst_invariant
  rw [Measure.compProd_const]
  exact hphase

/-- Diagonal inverse-mass velocity, covering the executable diagonal metric. -/
def diagonalVelocity (inverseMass : ι → ℝ) (p : Momentum ι) : Position ι :=
  fun i => inverseMass i * p i

omit [Fintype ι] in theorem measurable_diagonalVelocity (inverseMass : ι → ℝ) :
    Measurable (diagonalVelocity inverseMass) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_const.mul (measurable_pi_apply i)

omit [Fintype ι] in theorem diagonalVelocity_odd (inverseMass : ι → ℝ) (p : Momentum ι) :
    diagonalVelocity inverseMass (-p) = -diagonalVelocity inverseMass p := by
  funext i
  simp [diagonalVelocity]

def diagonalMetric (inverseMass : ι → ℝ) : ConstantMetric ι where
  velocity := diagonalVelocity inverseMass
  measurable_velocity := measurable_diagonalVelocity inverseMass
  velocity_odd := diagonalVelocity_odd inverseMass

/-- Dense inverse-mass matrix-vector multiplication. -/
noncomputable def denseVelocity (inverseMass : ι → ι → ℝ)
    (p : Momentum ι) : Position ι :=
  fun i => ∑ j, inverseMass i j * p j

theorem measurable_denseVelocity (inverseMass : ι → ι → ℝ) :
    Measurable (denseVelocity inverseMass) := by
  apply measurable_pi_lambda
  intro i
  exact Finset.measurable_sum _ fun j _ =>
    measurable_const.mul (measurable_pi_apply j)

theorem denseVelocity_odd (inverseMass : ι → ι → ℝ)
    (p : Momentum ι) :
    denseVelocity inverseMass (-p) = -denseVelocity inverseMass p := by
  funext i
  simp [denseVelocity]

noncomputable def denseMetric (inverseMass : ι → ι → ℝ) : ConstantMetric ι where
  velocity := denseVelocity inverseMass
  measurable_velocity := measurable_denseVelocity inverseMass
  velocity_odd := denseVelocity_odd inverseMass

end Mcmc.Executable.Continuous
