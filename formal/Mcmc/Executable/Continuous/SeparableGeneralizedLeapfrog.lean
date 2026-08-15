import Mcmc.Executable.Continuous.MetricHMC
import Mcmc.Relativistic.GeneralizedLeapfrog

/-!
# Explicit generalized leapfrog for separable Hamiltonians

When `∂H/∂q` depends only on position and `∂H/∂p` only on momentum, the two
implicit generalized-leapfrog equations collapse to the ordinary
velocity-Verlet update. This module packages the existing measurable,
reversible, volume-preserving metric leapfrog as a fully valid generalized
selection. It is the solver used by constant-Hessian SoftAbs clients.
-/

namespace Mcmc.Executable.Continuous

open Mcmc.Hamiltonian Mcmc.Relativistic MeasureTheory

variable {ι : Type*} [Fintype ι]

def separablePositionDerivative (gradient : Position ι → Momentum ι) :
    PhaseSpace ι → Position ι := fun z => gradient z.1

def separableMomentumDerivative (velocity : Momentum ι → Position ι) :
    PhaseSpace ι → Position ι := fun z => velocity z.2

/-- The explicit metric leapfrog, viewed as a solution of the generalized
equations. -/
noncomputable def separableGeneralizedLeapfrogSelection
    (velocity : Momentum ι → Position ι)
    (gradient : Position ι → Momentum ι) :
    GeneralizedLeapfrogSelection
      (separablePositionDerivative gradient)
      (separableMomentumDerivative velocity) where
  halfMomentum ε z := z.2 - (ε / 2) • gradient z.1
  step ε z := metricLeapfrog velocity gradient ε z
  satisfies ε z := by
    unfold GeneralizedLeapfrogEquations separablePositionDerivative
      separableMomentumDerivative metricLeapfrog metricDrift
    dsimp only
    constructor
    · rfl
    constructor
    · module
    · rfl

omit [Fintype ι] in
theorem separableGeneralizedLeapfrogSelection_unique
    (velocity : Momentum ι → Position ι)
    (gradient : Position ι → Momentum ι) :
    (separableGeneralizedLeapfrogSelection velocity gradient).IsUnique := by
  intro ε z pHalf zNext h
  rcases h with ⟨hp, hq, hpNext⟩
  simp only [separablePositionDerivative, separableMomentumDerivative] at hp hq hpNext
  have hq' : zNext.1 = z.1 + ε • velocity pHalf := by
    rw [hq]
    module
  constructor
  · exact hp
  · apply Prod.ext
    · simpa [separableGeneralizedLeapfrogSelection, metricLeapfrog,
        metricDrift, hp] using hq'
    · simpa [separableGeneralizedLeapfrogSelection, metricLeapfrog,
        metricDrift, hp, hq'] using hpNext

/-- Every measurable odd separable velocity and measurable force callback
gives a complete generalized-leapfrog validity certificate. -/
theorem separableGeneralizedLeapfrogSelection_valid
    (metric : ConstantMetric ι) (gradient : Position ι → Momentum ι)
    (hgradient : Measurable gradient) :
    (separableGeneralizedLeapfrogSelection metric.velocity gradient).IsValid where
  measurable ε := measurable_metricLeapfrog metric hgradient ε
  unique := separableGeneralizedLeapfrogSelection_unique metric.velocity gradient
  reversible ε z :=
    momentumFlip_metricLeapfrog_momentumFlip metric gradient ε z
  volumePreserving ε :=
    measurePreserving_metricLeapfrog metric.measurable_velocity hgradient ε

end Mcmc.Executable.Continuous
