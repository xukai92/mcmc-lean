import Mcmc.Executable.Continuous.CompilerIR
import Mcmc.Hamiltonian.VolumePreservation
import Mcmc.Hamiltonian.HMC
import Mcmc.Kernel.DeterministicMetropolis

/-!
# Executable scalar HMC refinement

This module connects the scalar command program's deterministic integrator
formula to the existing mathematical leapfrog map. The stochastic program
uses the same ideal normal and uniform primitives as executable RWMH.
-/

namespace Mcmc.Executable.Continuous

open Mcmc.Hamiltonian
open MeasureTheory

/-- Embed a scalar phase point in the one-coordinate phase-space interface. -/
def scalarPhase (q p : ℝ) : PhaseSpace Unit :=
  (fun _ => q, fun _ => p)

/-- Lift a scalar gradient into the one-coordinate Hamiltonian interface. -/
def scalarGradient (gradient : ℝ → ℝ) : Position Unit → Position Unit :=
  fun q _ => gradient (q ())

theorem measurable_scalarGradient {gradient : ℝ → ℝ}
    (hgradient : Measurable gradient) : Measurable (scalarGradient gradient) := by
  apply measurable_pi_lambda
  intro i
  exact hgradient.comp (measurable_pi_apply i)

/-- The position and momentum expressions serialized by `scalarHmcProgram`
are exactly the existing unit-mass leapfrog definition. -/
theorem leapfrog_scalarPhase (gradient : ℝ → ℝ) (ε q p : ℝ) :
    leapfrog (scalarGradient gradient) ε (scalarPhase q p) =
      scalarPhase
        (q + ε * (p - ε * gradient q / 2))
        (p - ε * gradient q / 2 -
          ε * gradient (q + ε * (p - ε * gradient q / 2)) / 2) := by
  apply Prod.ext <;> funext i
  cases i
  · simp only [leapfrog, halfKick, drift, scalarGradient, scalarPhase,
      Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  · simp only [leapfrog, halfKick, drift, scalarGradient, scalarPhase,
      Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    have hposition :
        q + ε * (p - ε / 2 * gradient q) =
          q + ε * (p - ε * gradient q / 2) := by ring
    rw [hposition]
    ring

/-- Consequently the ideal integrator used by the executable scalar HMC
slice inherits the existing exact phase-volume-preservation theorem. -/
theorem measurePreserving_scalarLeapfrog {gradient : ℝ → ℝ}
    (hgradient : Measurable gradient) (ε : ℝ) :
    MeasurePreserving (leapfrog (scalarGradient gradient) ε)
      phaseVolume phaseVolume :=
  measurePreserving_leapfrog (measurable_scalarGradient hgradient) ε

/-- Momentum-flipped leapfrog proposal used by endpoint Metropolis HMC. The
flip does not change the returned position or Hamiltonian. -/
noncomputable def endpointLeapfrogProposal (gradient : Position Unit → Position Unit)
    (ε : ℝ) (z : PhaseSpace Unit) : PhaseSpace Unit :=
  momentumFlip (leapfrog gradient ε z)

theorem measurable_endpointLeapfrogProposal {gradient : Position Unit → Position Unit}
    (hgradient : Measurable gradient) (ε : ℝ) :
    Measurable (endpointLeapfrogProposal gradient ε) :=
  measurable_momentumFlip.comp (measurable_leapfrog hgradient ε)

theorem endpointLeapfrogProposal_involutive
    (gradient : Position Unit → Position Unit) (ε : ℝ) :
    Function.Involutive (endpointLeapfrogProposal gradient ε) := by
  intro z
  simp only [endpointLeapfrogProposal]
  rw [momentumFlip_leapfrog_momentumFlip, leapfrog_neg_comp_leapfrog]

theorem measurePreserving_endpointLeapfrogProposal
    {gradient : Position Unit → Position Unit} (hgradient : Measurable gradient)
    (ε : ℝ) :
    MeasurePreserving (endpointLeapfrogProposal gradient ε)
      phaseVolume phaseVolume :=
  measurePreserving_momentumFlip.comp (measurePreserving_leapfrog hgradient ε)

/-- Exact phase-space kernel denoted by one endpoint-corrected leapfrog step. -/
noncomputable def endpointHmcPhaseKernel
    (potential : Position Unit → ℝ) (gradient : Position Unit → Position Unit)
    (ε : ℝ) (hgradient : Measurable gradient) :
    ProbabilityTheory.Kernel (PhaseSpace Unit) (PhaseSpace Unit) :=
  Mcmc.Kernel.deterministicMetropolis (boltzmannWeight potential)
    (endpointLeapfrogProposal gradient ε)
    (measurable_endpointLeapfrogProposal hgradient ε)

/-- The exact endpoint kernel is Markov. -/
theorem endpointHmcPhaseKernel_isMarkov
    (potential : Position Unit → ℝ) (gradient : Position Unit → Position Unit)
    (ε : ℝ) (hpotential : Measurable potential) (hgradient : Measurable gradient) :
    ProbabilityTheory.IsMarkovKernel
      (endpointHmcPhaseKernel potential gradient ε hgradient) := by
  unfold endpointHmcPhaseKernel
  exact Mcmc.Kernel.deterministicMetropolis_isMarkov _ _
    (measurable_boltzmannWeight hpotential)
    (measurable_endpointLeapfrogProposal hgradient ε)

/-- Endpoint-corrected leapfrog preserves the exact Boltzmann phase target. -/
theorem endpointHmcPhaseKernel_invariant
    {potential : Position Unit → ℝ} {gradient : Position Unit → Position Unit}
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) :
    (endpointHmcPhaseKernel potential gradient ε hgradient).Invariant
      (phaseBoltzmannTarget potential) := by
  letI : ProbabilityTheory.IsMarkovKernel
      (endpointHmcPhaseKernel potential gradient ε hgradient) :=
    endpointHmcPhaseKernel_isMarkov potential gradient ε hpotential hgradient
  unfold endpointHmcPhaseKernel phaseBoltzmannTarget
  exact Mcmc.Kernel.deterministicMetropolis_invariant phaseVolume
    (boltzmannWeight potential) (endpointLeapfrogProposal gradient ε)
    (measurable_endpointLeapfrogProposal hgradient ε)
    (measurable_boltzmannWeight hpotential)
    (boltzmannWeight_ne_zero potential) (boltzmannWeight_ne_top potential)
    (endpointLeapfrogProposal_involutive gradient ε)
    (measurePreserving_endpointLeapfrogProposal hgradient ε)

end Mcmc.Executable.Continuous
