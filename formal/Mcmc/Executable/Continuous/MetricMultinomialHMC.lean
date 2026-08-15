import Mcmc.Executable.Continuous.MetricHMC
import Mcmc.Kernel.OrbitMultinomial

/-!
# Constant-metric multinomial HMC

This instantiates the generic verified orbit-multinomial construction with the
constant-metric leapfrog permutation.
-/

namespace Mcmc.Executable.Continuous

open MeasureTheory ProbabilityTheory Mcmc.Hamiltonian Mcmc.Kernel

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in theorem metricBoltzmannWeight_ne_zero
    (potential : Position ι → ℝ) (kinetic : Momentum ι → ℝ) (z : PhaseSpace ι) :
    metricBoltzmannWeight potential kinetic z ≠ 0 := by
  exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)

omit [Fintype ι] in theorem metricBoltzmannWeight_ne_top
    (potential : Position ι → ℝ) (kinetic : Momentum ι → ℝ) (z : PhaseSpace ι) :
    metricBoltzmannWeight potential kinetic z ≠ ⊤ := ENNReal.ofReal_ne_top

/-- Random-origin multinomial selection along a constant-metric leapfrog
orbit. -/
noncomputable def metricMultinomialHmcPhaseKernel
    (metric : ConstantMetric ι) (potential : Position ι → ℝ)
    (kinetic : Momentum ι → ℝ) (gradient : Position ι → Momentum ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hkinetic : Measurable kinetic) (hgradient : Measurable gradient) :
    Kernel (PhaseSpace ι) (PhaseSpace ι) :=
  orbitMultinomialKernel (metricBoltzmannWeight potential kinetic)
    (metricLeapfrogPerm metric gradient ε) L
    (metricBoltzmannWeight_ne_zero potential kinetic)
    (metricBoltzmannWeight_ne_top potential kinetic)
    (measurable_metricBoltzmannWeight hpotential hkinetic)
    (measurable_metricLeapfrog metric hgradient ε)
    (measurable_metricLeapfrog metric hgradient (-ε))

instance metricMultinomialHmcPhaseKernel_isMarkovKernel
    (metric : ConstantMetric ι) (potential : Position ι → ℝ)
    (kinetic : Momentum ι → ℝ) (gradient : Position ι → Momentum ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hkinetic : Measurable kinetic) (hgradient : Measurable gradient) :
    IsMarkovKernel (metricMultinomialHmcPhaseKernel metric potential kinetic
      gradient ε L hpotential hkinetic hgradient) := by
  unfold metricMultinomialHmcPhaseKernel
  infer_instance

/-- Exact constant-metric phase invariance. -/
theorem metricMultinomialHmcPhaseKernel_invariant
    (metric : ConstantMetric ι) {potential : Position ι → ℝ}
    {kinetic : Momentum ι → ℝ} {gradient : Position ι → Momentum ι}
    (hpotential : Measurable potential) (hkinetic : Measurable kinetic)
    (hgradient : Measurable gradient) (ε : ℝ) (L : ℕ) :
    (metricMultinomialHmcPhaseKernel metric potential kinetic gradient ε L
      hpotential hkinetic hgradient).Invariant
      (phaseVolume.withDensity (metricBoltzmannWeight potential kinetic)) := by
  unfold metricMultinomialHmcPhaseKernel
  apply orbitMultinomialKernel_invariant
  · exact measurePreserving_metricLeapfrog metric.measurable_velocity hgradient ε
  · change MeasurePreserving
      (metricLeapfrog metric.velocity gradient (-ε)) phaseVolume phaseVolume
    exact measurePreserving_metricLeapfrog metric.measurable_velocity hgradient (-ε)

/-- Refresh momentum, run the metric multinomial orbit transition, and project
back to position. -/
noncomputable def metricMultinomialHmcPositionKernel
    (metric : ConstantMetric ι) (potential : Position ι → ℝ)
    (kinetic : Momentum ι → ℝ) (gradient : Position ι → Momentum ι)
    (momentumTarget : Measure (Momentum ι)) (ε : ℝ) (L : ℕ)
    (hpotential : Measurable potential) (hkinetic : Measurable kinetic)
    (hgradient : Measurable gradient) : Kernel (Position ι) (Position ι) := by
  letI := metricMultinomialHmcPhaseKernel_isMarkovKernel metric potential kinetic
    gradient ε L hpotential hkinetic hgradient
  exact Mcmc.Kernel.liftEvolveProject
    (positionMomentumLift momentumTarget)
    (metricMultinomialHmcPhaseKernel metric potential kinetic gradient ε L
      hpotential hkinetic hgradient)
    (Prod.fst : PhaseSpace ι → Position ι) measurable_fst

theorem metricMultinomialHmcPositionKernel_invariant
    (metric : ConstantMetric ι) {potential : Position ι → ℝ}
    {kinetic : Momentum ι → ℝ} {gradient : Position ι → Momentum ι}
    (hpotential : Measurable potential) (hkinetic : Measurable kinetic)
    (hgradient : Measurable gradient) (momentumTarget : Measure (Momentum ι))
    [IsProbabilityMeasure momentumTarget]
    (positionTarget : Measure (Position ι)) [SFinite positionTarget]
    (ε : ℝ) (L : ℕ)
    (hfactor : positionTarget.prod momentumTarget =
      phaseVolume.withDensity (metricBoltzmannWeight potential kinetic)) :
    (metricMultinomialHmcPositionKernel metric potential kinetic gradient
      momentumTarget ε L hpotential hkinetic hgradient).Invariant positionTarget := by
  change (Mcmc.Kernel.liftEvolveProject
    (positionMomentumLift momentumTarget)
    (metricMultinomialHmcPhaseKernel metric potential kinetic gradient ε L
      hpotential hkinetic hgradient)
    (Prod.fst : PhaseSpace ι → Position ι) measurable_fst).Invariant positionTarget
  have hphase := metricMultinomialHmcPhaseKernel_invariant metric hpotential
    hkinetic hgradient ε L
  rw [← hfactor] at hphase
  unfold positionMomentumLift
  apply Mcmc.Kernel.compProdEvolveFst_invariant
  rw [Measure.compProd_const]
  exact hphase

end Mcmc.Executable.Continuous
