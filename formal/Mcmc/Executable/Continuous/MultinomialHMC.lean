import Mcmc.Hamiltonian.HMC

/-!
# Ideal executable semantics for multinomial HMC

The executable choice surface consists of a uniformly distributed trajectory
origin followed by an index distributed according to the trajectory's
Boltzmann weights. This module identifies that finite probabilistic program
exactly with the already verified multinomial-HMC PMF and kernel.
-/

namespace Mcmc.Executable.Continuous

open Mcmc.Hamiltonian
open ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- Deterministic result after the momentum, origin, and selected-index events
of one ideal multinomial-HMC phase transition have been supplied. -/
noncomputable def multinomialHmcResult
    (gradient : Position ι → Position ι) (ε : ℝ) {L : ℕ}
    (origin selected : Fin (L + 1)) (phase : PhaseSpace ι) : PhaseSpace ι :=
  offsetLeapfrogTrajectory gradient ε origin phase selected

/-- Joint law of the two finite choices made after momentum refresh. -/
noncomputable def multinomialHmcChoicePMF
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (phase : PhaseSpace ι) :
    PMF (Fin (L + 1) × Fin (L + 1)) :=
  originSelectedIndexPMF potential gradient ε L phase

/-- The typed choice program returns exactly the verified randomized-origin
multinomial trajectory law. -/
theorem multinomialHmcChoicePMF_map_result
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (phase : PhaseSpace ι) :
    (multinomialHmcChoicePMF potential gradient ε L phase).map
        (fun choice => multinomialHmcResult gradient ε choice.1 choice.2 phase) =
      randomizedMultinomialLeapfrogPMF potential gradient ε L phase := by
  unfold multinomialHmcChoicePMF originSelectedIndexPMF
    randomizedMultinomialLeapfrogPMF
  rw [PMF.map_bind]
  congr 1
  funext origin
  rw [PMF.map_comp]
  rfl

/-- The law of the ideal executable choice program is the row of the verified
invariant phase kernel. -/
theorem multinomialHmcChoicePMF_map_result_toMeasure
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    (ε : ℝ) (L : ℕ) (phase : PhaseSpace ι)
    (hpotential : Measurable potential) (hgradient : Measurable gradient) :
    ((multinomialHmcChoicePMF potential gradient ε L phase).map
        (fun choice => multinomialHmcResult gradient ε choice.1 choice.2 phase)).toMeasure =
      randomizedMultinomialLeapfrogKernel potential gradient ε L
        hpotential hgradient phase := by
  rw [multinomialHmcChoicePMF_map_result]
  exact (randomizedMultinomialLeapfrogKernel_apply_eq_toMeasure
    potential gradient ε L hpotential hgradient phase).symm

/-- Exact measure semantics assigned to the complete executable command:
standard-Gaussian momentum refresh, the typed origin/index program above, and
position projection. -/
noncomputable def executableMultinomialHmcKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) : Kernel (Position ι) (Position ι) :=
  standardPositionMultinomialHMC potential gradient ε L hpotential hgradient

instance executableMultinomialHmcKernel_isMarkovKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    IsMarkovKernel (executableMultinomialHmcKernel potential gradient ε L
      hpotential hgradient) := by
  unfold executableMultinomialHmcKernel
  infer_instance

/-- The exact executable multinomial-HMC semantics preserves its position
Boltzmann target. -/
theorem executableMultinomialHmcKernel_invariant
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) (L : ℕ) :
    (executableMultinomialHmcKernel potential gradient ε L
      hpotential hgradient).Invariant (positionBoltzmannTarget potential) :=
  standardPositionMultinomialHMC_invariant hpotential hgradient ε L

end Mcmc.Executable.Continuous
