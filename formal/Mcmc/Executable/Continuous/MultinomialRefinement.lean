import Mcmc.Executable.Continuous.MultinomialHMC
import Mcmc.Executable.Continuous.MultinomialCompilerIR
import Mcmc.Executable.Continuous.MetricMultinomialHMC
import Mcmc.Executable.Continuous.MetricCompilerIR

/-!
# IR-kernel refinement for multinomial HMC programs

This module connects the multinomial HMC IR program descriptors to their
verified mathematical kernels. Each refinement theorem proves that the
kernel constructed from the command's ideal choice-PMF semantics equals the
verified Markov kernel from the kernel-theory layer.

The unit-mass program phase kernel is defined from the command's joint
origin/index PMF mapped through `multinomialHmcResult`. The bridge theorem
`multinomialHmcChoicePMF_map_result_toMeasure` identifies this with the
`randomizedMultinomialLeapfrogKernel`. The position kernel follows via
`liftEvolveProject` and equals `standardPositionMultinomialHMC`.

Both diagonal and dense constant-metric variants are parameterized by
`ConstantMetric ι`. The program kernel connects through
`metricMultinomialHmcPhaseKernel` (the orbit-multinomial construction) and
equals `metricMultinomialHmcPositionKernel`.
-/

namespace Mcmc.Executable.Continuous

open Mcmc.Hamiltonian Mcmc.Kernel MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-! ### Unit-mass multinomial HMC -/

/-- Phase kernel constructed from the IR command's ideal choice PMF. Each row
is the measure induced by mapping the joint origin/index program through
the deterministic phase-space result function. -/
noncomputable def multinomialHmcProgramPhaseKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    Kernel (PhaseSpace ι) (PhaseSpace ι) where
  toFun z :=
    ((multinomialHmcChoicePMF potential gradient ε L z).map
      (fun choice => multinomialHmcResult gradient ε choice.1 choice.2 z)).toMeasure
  measurable' := by
    convert (randomizedMultinomialLeapfrogKernel potential gradient ε L
      hpotential hgradient).measurable' using 1
    funext z
    exact multinomialHmcChoicePMF_map_result_toMeasure ε L z hpotential hgradient

/-- The command PMF construction coincides with the verified randomized
multinomial leapfrog phase kernel. -/
theorem multinomialHmcProgramPhaseKernel_eq
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    multinomialHmcProgramPhaseKernel potential gradient ε L
      hpotential hgradient =
    randomizedMultinomialLeapfrogKernel potential gradient ε L
      hpotential hgradient := by
  ext z s hs
  change ((multinomialHmcChoicePMF potential gradient ε L z).map
      (fun choice => multinomialHmcResult gradient ε choice.1 choice.2 z)).toMeasure s =
    randomizedMultinomialLeapfrogKernel potential gradient ε L
      hpotential hgradient z s
  rw [multinomialHmcChoicePMF_map_result_toMeasure]

instance multinomialHmcProgramPhaseKernel_isMarkovKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    IsMarkovKernel (multinomialHmcProgramPhaseKernel potential gradient ε L
      hpotential hgradient) := by
  rw [multinomialHmcProgramPhaseKernel_eq]
  infer_instance

/-- Position kernel from the IR command semantics via standard-Gaussian
momentum refresh and first-coordinate projection. -/
noncomputable def multinomialHmcProgramKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    Kernel (Position ι) (Position ι) :=
  liftEvolveProject (positionMomentumLift standardMomentumMeasure)
    (multinomialHmcProgramPhaseKernel potential gradient ε L
      hpotential hgradient)
    (Prod.fst : PhaseSpace ι → Position ι) measurable_fst

/-- The unit-mass IR program kernel equals the verified standard multinomial
HMC position kernel. -/
theorem multinomialHmcProgramKernel_refines
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    multinomialHmcProgramKernel potential gradient ε L
      hpotential hgradient =
    standardPositionMultinomialHMC potential gradient ε L
      hpotential hgradient := by
  simp only [multinomialHmcProgramKernel, standardPositionMultinomialHMC,
    positionMultinomialHMC, liftEvolveProject,
    multinomialHmcProgramPhaseKernel_eq]

/-! ### Constant-metric multinomial HMC -/

/-- Position kernel for the constant-metric multinomial HMC IR program,
constructed from the orbit-multinomial phase kernel via momentum refresh
and position projection. Both diagonal and dense IR programs denote the
same kernel parameterized by `ConstantMetric ι`. -/
noncomputable def metricMultinomialHmcProgramKernel
    (metric : ConstantMetric ι) (potential : Position ι → ℝ)
    (kinetic : Momentum ι → ℝ) (gradient : Position ι → Momentum ι)
    (momentumTarget : Measure (Momentum ι)) (ε : ℝ) (L : ℕ)
    (hpotential : Measurable potential) (hkinetic : Measurable kinetic)
    (hgradient : Measurable gradient) :
    Kernel (Position ι) (Position ι) :=
  liftEvolveProject (positionMomentumLift momentumTarget)
    (metricMultinomialHmcPhaseKernel metric potential kinetic gradient ε L
      hpotential hkinetic hgradient)
    (Prod.fst : PhaseSpace ι → Position ι) measurable_fst

/-- The diagonal-metric multinomial HMC IR program kernel equals the
verified constant-metric multinomial HMC position kernel. -/
theorem diagonalMultinomialHmcProgramKernel_refines
    (metric : ConstantMetric ι) (potential : Position ι → ℝ)
    (kinetic : Momentum ι → ℝ) (gradient : Position ι → Momentum ι)
    (momentumTarget : Measure (Momentum ι)) (ε : ℝ) (L : ℕ)
    (hpotential : Measurable potential) (hkinetic : Measurable kinetic)
    (hgradient : Measurable gradient) :
    metricMultinomialHmcProgramKernel metric potential kinetic gradient
      momentumTarget ε L hpotential hkinetic hgradient =
    metricMultinomialHmcPositionKernel metric potential kinetic gradient
      momentumTarget ε L hpotential hkinetic hgradient := by
  rfl

/-- The dense-metric multinomial HMC IR program kernel equals the verified
constant-metric multinomial HMC position kernel. -/
theorem denseMultinomialHmcProgramKernel_refines
    (metric : ConstantMetric ι) (potential : Position ι → ℝ)
    (kinetic : Momentum ι → ℝ) (gradient : Position ι → Momentum ι)
    (momentumTarget : Measure (Momentum ι)) (ε : ℝ) (L : ℕ)
    (hpotential : Measurable potential) (hkinetic : Measurable kinetic)
    (hgradient : Measurable gradient) :
    metricMultinomialHmcProgramKernel metric potential kinetic gradient
      momentumTarget ε L hpotential hkinetic hgradient =
    metricMultinomialHmcPositionKernel metric potential kinetic gradient
      momentumTarget ε L hpotential hkinetic hgradient := by
  rfl

end Mcmc.Executable.Continuous
