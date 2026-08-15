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

/-- The multi-step scalar IR integrator is exactly the existing iterated
Hamiltonian leapfrog map. -/
theorem leapfrogN_scalarPhase (gradient : ℝ → ℝ) (ε : ℝ)
    (steps : Nat) (q p : ℝ) :
    leapfrogN (scalarGradient gradient) ε steps (scalarPhase q p) =
      scalarPhase
        (CompilerIR.scalarLeapfrogN gradient ε steps q p).1
        (CompilerIR.scalarLeapfrogN gradient ε steps q p).2 := by
  induction steps with
  | zero => simp [leapfrogN, CompilerIR.scalarLeapfrogN, scalarPhase]
  | succ steps ih =>
      rw [leapfrogN_succ, ih]
      rw [leapfrog_scalarPhase]
      simp only [CompilerIR.scalarLeapfrogN]

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

/-- Momentum-flipped `steps`-fold leapfrog proposal used by practical HMC. -/
noncomputable def endpointLeapfrogNProposal
    (gradient : Position Unit → Position Unit) (ε : ℝ) (steps : Nat)
    (z : PhaseSpace Unit) : PhaseSpace Unit :=
  momentumFlip (leapfrogN gradient ε steps z)

theorem momentumFlip_leapfrogN_momentumFlip
    (gradient : Position Unit → Position Unit) (ε : ℝ) (steps : Nat)
    (z : PhaseSpace Unit) :
    momentumFlip (leapfrogN gradient ε steps (momentumFlip z)) =
      leapfrogN gradient (-ε) steps z := by
  induction steps generalizing z with
  | zero => simp [leapfrogN]
  | succ steps ih =>
      rw [leapfrogN_succ]
      have h := momentumFlip_leapfrog_momentumFlip gradient ε
        (momentumFlip (leapfrogN gradient ε steps (momentumFlip z)))
      simp only [momentumFlip_involutive] at h
      rw [h, ih]
      rw [leapfrogN_succ]

theorem endpointLeapfrogNProposal_involutive
    (gradient : Position Unit → Position Unit) (ε : ℝ) (steps : Nat) :
    Function.Involutive (endpointLeapfrogNProposal gradient ε steps) := by
  intro z
  simp only [endpointLeapfrogNProposal]
  rw [momentumFlip_leapfrogN_momentumFlip,
    leapfrogN_neg_comp_leapfrogN]

theorem measurable_endpointLeapfrogNProposal
    {gradient : Position Unit → Position Unit} (hgradient : Measurable gradient)
    (ε : ℝ) (steps : Nat) :
    Measurable (endpointLeapfrogNProposal gradient ε steps) :=
  measurable_momentumFlip.comp (measurable_leapfrogN hgradient ε steps)

theorem measurePreserving_endpointLeapfrogNProposal
    {gradient : Position Unit → Position Unit} (hgradient : Measurable gradient)
    (ε : ℝ) (steps : Nat) :
    MeasurePreserving (endpointLeapfrogNProposal gradient ε steps)
      phaseVolume phaseVolume :=
  measurePreserving_momentumFlip.comp
    (measurePreserving_leapfrogN hgradient ε steps)

/-- Exact phase-space kernel denoted by multi-step endpoint-corrected HMC. -/
noncomputable def endpointHmcNPhaseKernel
    (potential : Position Unit → ℝ) (gradient : Position Unit → Position Unit)
    (ε : ℝ) (steps : Nat) (hgradient : Measurable gradient) :
    ProbabilityTheory.Kernel (PhaseSpace Unit) (PhaseSpace Unit) :=
  Mcmc.Kernel.deterministicMetropolis (boltzmannWeight potential)
    (endpointLeapfrogNProposal gradient ε steps)
    (measurable_endpointLeapfrogNProposal hgradient ε steps)

theorem endpointHmcNPhaseKernel_isMarkov
    (potential : Position Unit → ℝ) (gradient : Position Unit → Position Unit)
    (ε : ℝ) (steps : Nat) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    ProbabilityTheory.IsMarkovKernel
      (endpointHmcNPhaseKernel potential gradient ε steps hgradient) := by
  unfold endpointHmcNPhaseKernel
  exact Mcmc.Kernel.deterministicMetropolis_isMarkov _ _
    (measurable_boltzmannWeight hpotential)
    (measurable_endpointLeapfrogNProposal hgradient ε steps)

/-- Every finite trajectory length gives an invariant exact endpoint-HMC
phase kernel. -/
theorem endpointHmcNPhaseKernel_invariant
    {potential : Position Unit → ℝ} {gradient : Position Unit → Position Unit}
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) (steps : Nat) :
    (endpointHmcNPhaseKernel potential gradient ε steps hgradient).Invariant
      (phaseBoltzmannTarget potential) := by
  letI : ProbabilityTheory.IsMarkovKernel
      (endpointHmcNPhaseKernel potential gradient ε steps hgradient) :=
    endpointHmcNPhaseKernel_isMarkov potential gradient ε steps
      hpotential hgradient
  unfold endpointHmcNPhaseKernel phaseBoltzmannTarget
  exact Mcmc.Kernel.deterministicMetropolis_invariant phaseVolume
    (boltzmannWeight potential) (endpointLeapfrogNProposal gradient ε steps)
    (measurable_endpointLeapfrogNProposal hgradient ε steps)
    (measurable_boltzmannWeight hpotential)
    (boltzmannWeight_ne_zero potential) (boltzmannWeight_ne_top potential)
    (endpointLeapfrogNProposal_involutive gradient ε steps)
    (measurePreserving_endpointLeapfrogNProposal hgradient ε steps)

/-- Complete multi-step endpoint HMC position transition: refresh standard
Gaussian momentum, evolve with the corrected phase kernel, then project. -/
noncomputable def endpointHmcNPositionKernel
    (potential : Position Unit → ℝ) (gradient : Position Unit → Position Unit)
    (ε : ℝ) (steps : Nat) (_hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    ProbabilityTheory.Kernel (Position Unit) (Position Unit) := by
  letI : ProbabilityTheory.IsMarkovKernel
      (endpointHmcNPhaseKernel potential gradient ε steps hgradient) :=
    endpointHmcNPhaseKernel_isMarkov potential gradient ε steps
      _hpotential hgradient
  exact Mcmc.Kernel.liftEvolveProject
    (positionMomentumLift standardMomentumMeasure)
    (endpointHmcNPhaseKernel potential gradient ε steps hgradient)
    (Prod.fst : PhaseSpace Unit → Position Unit) measurable_fst

instance endpointHmcNPositionKernel_isMarkov
    (potential : Position Unit → ℝ) (gradient : Position Unit → Position Unit)
    (ε : ℝ) (steps : Nat) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    ProbabilityTheory.IsMarkovKernel
      (endpointHmcNPositionKernel potential gradient ε steps
        hpotential hgradient) := by
  letI : ProbabilityTheory.IsMarkovKernel
      (endpointHmcNPhaseKernel potential gradient ε steps hgradient) :=
    endpointHmcNPhaseKernel_isMarkov potential gradient ε steps
      hpotential hgradient
  unfold endpointHmcNPositionKernel
  infer_instance

/-- The full refreshed/projected position sampler preserves any position
target whose product with standard momentum is the Boltzmann phase target. -/
theorem endpointHmcNPositionKernel_invariant
    {potential : Position Unit → ℝ} {gradient : Position Unit → Position Unit}
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) (steps : Nat)
    (positionTarget : MeasureTheory.Measure (Position Unit)) [SFinite positionTarget]
    (hfactor : positionTarget.prod standardMomentumMeasure =
      phaseBoltzmannTarget potential) :
    (endpointHmcNPositionKernel potential gradient ε steps
      hpotential hgradient).Invariant positionTarget := by
  change (Mcmc.Kernel.liftEvolveProject
    (positionMomentumLift standardMomentumMeasure)
    (endpointHmcNPhaseKernel potential gradient ε steps hgradient)
    (Prod.fst : PhaseSpace Unit → Position Unit) measurable_fst).Invariant
      positionTarget
  have hphase := endpointHmcNPhaseKernel_invariant hpotential hgradient ε steps
  rw [← hfactor] at hphase
  unfold positionMomentumLift
  apply Mcmc.Kernel.compProdEvolveFst_invariant
  rw [MeasureTheory.Measure.compProd_const]
  exact hphase

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
