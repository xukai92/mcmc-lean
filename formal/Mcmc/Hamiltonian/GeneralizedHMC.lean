import Mcmc.Relativistic.GeneralizedLeapfrog
import Mcmc.Kernel.DeterministicMetropolis
import Mcmc.Kernel.LiftEvolveProject

/-!
# Generic endpoint-corrected generalized Hamiltonian Monte Carlo

This module isolates the correctness argument shared by classical Riemannian
HMC and later nonseparable Hamiltonian variants.  It deliberately knows
nothing about the momentum law or the formula for the Hamiltonian: a valid
generalized-leapfrog selection, an everywhere positive finite phase weight,
and compatibility of the position-dependent momentum kernel with that phase
target are the complete inputs.
-/

namespace Mcmc.Hamiltonian

open MeasureTheory ProbabilityTheory Mcmc.Kernel
open scoped ENNReal ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- One selected generalized-leapfrog step followed by momentum negation. -/
def generalizedHmcEndpoint
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (selection : Mcmc.Relativistic.GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (ε : ℝ) : PhaseSpace ι → PhaseSpace ι :=
  momentumFlip ∘ selection.step ε

omit [Fintype ι] in
theorem measurable_generalizedHmcEndpoint
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (selection : Mcmc.Relativistic.GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hmeasurable : selection.IsMeasurable) (ε : ℝ) :
    Measurable (generalizedHmcEndpoint selection ε) :=
  measurable_momentumFlip.comp (hmeasurable ε)

theorem generalizedHmcEndpoint_involutive
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (selection : Mcmc.Relativistic.GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid) (ε : ℝ) :
    Function.Involutive (generalizedHmcEndpoint selection ε) :=
  selection.momentumFlip_step_involutive hvalid.unique hvalid.reversible ε

theorem measurePreserving_generalizedHmcEndpoint
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (selection : Mcmc.Relativistic.GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid) (ε : ℝ) :
    MeasurePreserving (generalizedHmcEndpoint selection ε)
      phaseVolume phaseVolume :=
  measurePreserving_momentumFlip.comp (hvalid.volumePreserving ε)

/-- Endpoint Metropolis correction for an arbitrary nonseparable phase
weight. -/
noncomputable def generalizedHmcMetropolis
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (weight : PhaseSpace ι → ℝ≥0∞)
    (selection : Mcmc.Relativistic.GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hmeasurable : selection.IsMeasurable) (ε : ℝ) :
    Kernel (PhaseSpace ι) (PhaseSpace ι) :=
  deterministicMetropolis weight (generalizedHmcEndpoint selection ε)
    (measurable_generalizedHmcEndpoint selection hmeasurable ε)

theorem generalizedHmcMetropolis_isMarkov
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (weight : PhaseSpace ι → ℝ≥0∞) (hweight : Measurable weight)
    (selection : Mcmc.Relativistic.GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid) (ε : ℝ) :
    IsMarkovKernel
      (generalizedHmcMetropolis weight selection hvalid.measurable ε) :=
  deterministicMetropolis_isMarkov _ _ hweight
    (measurable_generalizedHmcEndpoint selection hvalid.measurable ε)

/-- A valid generalized-leapfrog endpoint kernel is reversible for every
positive finite measurable phase weight. -/
theorem generalizedHmcMetropolis_isReversible
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (weight : PhaseSpace ι → ℝ≥0∞) (hweight : Measurable weight)
    (hpositive : ∀ z, weight z ≠ 0) (hfinite : ∀ z, weight z ≠ ∞)
    (selection : Mcmc.Relativistic.GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid) (ε : ℝ) :
    (generalizedHmcMetropolis weight selection hvalid.measurable ε).IsReversible
      (phaseVolume.withDensity weight) :=
  deterministicMetropolis_isReversible phaseVolume _ _ _ hweight hpositive
    hfinite (generalizedHmcEndpoint_involutive selection hvalid ε)
    (measurePreserving_generalizedHmcEndpoint selection hvalid ε)

/-- Exact phase-target invariance of generic endpoint-corrected generalized
HMC. -/
theorem generalizedHmcMetropolis_invariant
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (weight : PhaseSpace ι → ℝ≥0∞) (hweight : Measurable weight)
    (hpositive : ∀ z, weight z ≠ 0) (hfinite : ∀ z, weight z ≠ ∞)
    (selection : Mcmc.Relativistic.GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid) (ε : ℝ) :
    (generalizedHmcMetropolis weight selection hvalid.measurable ε).Invariant
      (phaseVolume.withDensity weight) :=
  deterministicMetropolis_invariant phaseVolume _ _ _ hweight hpositive
    hfinite (generalizedHmcEndpoint_involutive selection hvalid ε)
    (measurePreserving_generalizedHmcEndpoint selection hvalid ε)

/-- Lift a position through a position-dependent momentum kernel. -/
noncomputable def positionDependentMomentumLift
    (momentumKernel : Kernel (Position ι) (Momentum ι)) :
    Kernel (Position ι) (PhaseSpace ι) :=
  Kernel.id ×ₖ momentumKernel

instance positionDependentMomentumLift_isMarkov
    (momentumKernel : Kernel (Position ι) (Momentum ι))
    [IsMarkovKernel momentumKernel] :
    IsMarkovKernel (positionDependentMomentumLift momentumKernel) := by
  unfold positionDependentMomentumLift
  infer_instance

/-- Refresh position-dependent momentum, evolve on phase space, and project
back to position. -/
noncomputable def positionGeneralizedHmc
    (momentumKernel : Kernel (Position ι) (Momentum ι))
    (phaseKernel : Kernel (PhaseSpace ι) (PhaseSpace ι)) :
    Kernel (Position ι) (Position ι) :=
  (phaseKernel ∘ₖ positionDependentMomentumLift momentumKernel).map Prod.fst

omit [Fintype ι] in
/-- If augmentation identifies the position target with an invariant phase
target, lift/evolve/project preserves the position target. -/
theorem positionGeneralizedHmc_invariant
    (positionTarget : Measure (Position ι)) [SFinite positionTarget]
    (momentumKernel : Kernel (Position ι) (Momentum ι))
    [IsMarkovKernel momentumKernel]
    (phaseKernel : Kernel (PhaseSpace ι) (PhaseSpace ι))
    [IsMarkovKernel phaseKernel]
    (phaseTarget : Measure (PhaseSpace ι))
    (hcompat : positionTarget ⊗ₘ momentumKernel = phaseTarget)
    (hphase : phaseKernel.Invariant phaseTarget) :
    (positionGeneralizedHmc momentumKernel phaseKernel).Invariant
      positionTarget := by
  rw [← hcompat] at hphase
  unfold positionGeneralizedHmc positionDependentMomentumLift
  exact Mcmc.Kernel.compProdEvolveFst_invariant positionTarget momentumKernel
    phaseKernel hphase

end Mcmc.Hamiltonian
