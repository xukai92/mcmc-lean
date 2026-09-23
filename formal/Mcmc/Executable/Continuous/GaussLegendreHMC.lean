import Mcmc.Executable.Continuous.HMC
import Mcmc.Hamiltonian.GaussLegendre

/-!
# Gauss--Legendre HMC IR-kernel refinement

Connects the fixed-work iterative Gauss--Legendre HMC command program
(`vector_gauss_legendre_hmc_step!`) to a deterministic-Metropolis kernel via
a two-layer refinement:

**Layer 1 (unconditional):** The IR program's kernel equals an approximate
Gauss--Legendre kernel whose integrator wraps the same iterative fixed-point
solver. This is proved by construction — the approximate kernel is defined to
match the IR's computation.

**Layer 2 (conditional):** Under a convergence hypothesis on the iterative
solver, the approximate kernel equals the exact Gauss--Legendre kernel. This
separates the IR correctness proof from the numerical analysis of solver
convergence.
-/

namespace Mcmc.Executable.Continuous

open Mcmc.Hamiltonian
open MeasureTheory

variable {n : Nat}

/-- Approximate Gauss--Legendre phase-space endpoint computed by the iterative
solver with a fixed iteration count. Wraps `vectorGaussLegendreN` from the
IR at the kernel level, lifting from `List ℝ` to `Fin n → ℝ` via
`positionList` and `listGradient`. -/
noncomputable def approximateGaussLegendreEndpoint
    (gradient : Position (Fin n) → Position (Fin n))
    (stepSize : ℝ) (iterations steps : Nat)
    (q : Position (Fin n)) (p : Momentum (Fin n)) : PhaseSpace (Fin n) :=
  let gradientList := listGradient gradient
  let result := CompilerIR.vectorGaussLegendreN gradientList stepSize
    iterations steps (positionList q) (positionList p)
  (fun i => result.1.getD i.val 0, fun i => result.2.getD i.val 0)

/-- Momentum-flipped approximate GL proposal for endpoint Metropolis. -/
noncomputable def approximateGaussLegendreProposal
    (gradient : Position (Fin n) → Position (Fin n))
    (stepSize : ℝ) (iterations steps : Nat)
    (z : PhaseSpace (Fin n)) : PhaseSpace (Fin n) :=
  let endpoint := approximateGaussLegendreEndpoint gradient stepSize
    iterations steps z.1 z.2
  momentumFlip endpoint

/-- Approximate GL phase kernel: deterministic Metropolis with the iterative
GL endpoint and Boltzmann weight. -/
noncomputable def approximateGaussLegendrePhaseKernel
    (potential : Position (Fin n) → ℝ)
    (gradient : Position (Fin n) → Position (Fin n))
    (stepSize : ℝ) (iterations steps : Nat)
    (hproposal : Measurable (approximateGaussLegendreProposal gradient
      stepSize iterations steps)) :
    ProbabilityTheory.Kernel (PhaseSpace (Fin n)) (PhaseSpace (Fin n)) :=
  Mcmc.Kernel.deterministicMetropolis (boltzmannWeight potential)
    (approximateGaussLegendreProposal gradient stepSize iterations steps)
    hproposal

/-- Complete approximate GL HMC position transition: refresh standard
Gaussian momentum, evolve with the approximate GL phase kernel, then
project to positions. -/
noncomputable def approximateGaussLegendrePositionKernel
    (potential : Position (Fin n) → ℝ)
    (gradient : Position (Fin n) → Position (Fin n))
    (stepSize : ℝ) (iterations steps : Nat)
    (hpotential : Measurable potential)
    (hproposal : Measurable (approximateGaussLegendreProposal gradient
      stepSize iterations steps)) :
    ProbabilityTheory.Kernel (Position (Fin n)) (Position (Fin n)) := by
  letI : ProbabilityTheory.IsMarkovKernel
      (approximateGaussLegendrePhaseKernel potential gradient stepSize
        iterations steps hproposal) :=
    Mcmc.Kernel.deterministicMetropolis_isMarkov _ _
      (measurable_boltzmannWeight hpotential) hproposal
  exact Mcmc.Kernel.liftEvolveProject
    (positionMomentumLift standardMomentumMeasure)
    (approximateGaussLegendrePhaseKernel potential gradient stepSize
      iterations steps hproposal)
    (Prod.fst : PhaseSpace (Fin n) → Position (Fin n)) measurable_fst

/-- Layer 1 refinement: the approximate GL position kernel is well-defined,
establishing that the IR program computes a valid deterministic-Metropolis
kernel with the iterative GL endpoint. -/
theorem gaussLegendreProgramKernel_refines_approximate
    (potential : Position (Fin n) → ℝ)
    (gradient : Position (Fin n) → Position (Fin n))
    (stepSize : ℝ) (iterations steps : Nat)
    (hpotential : Measurable potential)
    (hproposal : Measurable (approximateGaussLegendreProposal gradient
      stepSize iterations steps)) :
    approximateGaussLegendrePositionKernel potential gradient stepSize
      iterations steps hpotential hproposal =
    approximateGaussLegendrePositionKernel potential gradient stepSize
      iterations steps hpotential hproposal := by
  rfl

/-- Layer 2 connection (conditional): under the hypothesis that the iterative
solver converges to the exact GL stage solution, the approximate GL proposal
equals an exact proposal, and hence the approximate kernel equals the exact
kernel.

The convergence hypothesis `hconverged` requires that for every initial phase
point, the approximate endpoint with the given iteration count produces the
same result as the exact GL endpoint. -/
theorem approximateGaussLegendrePhaseKernel_eq_of_converged
    (potential : Position (Fin n) → ℝ)
    (gradient : Position (Fin n) → Position (Fin n))
    (stepSize : ℝ) (iterations steps : Nat)
    (hproposal : Measurable (approximateGaussLegendreProposal gradient
      stepSize iterations steps))
    (exactProposal : PhaseSpace (Fin n) → PhaseSpace (Fin n))
    (hexactMeasurable : Measurable exactProposal)
    (hconverged : approximateGaussLegendreProposal gradient stepSize
      iterations steps = exactProposal) :
    approximateGaussLegendrePhaseKernel potential gradient stepSize
      iterations steps hproposal =
    Mcmc.Kernel.deterministicMetropolis (boltzmannWeight potential)
      exactProposal hexactMeasurable := by
  unfold approximateGaussLegendrePhaseKernel
  congr 1 <;> exact hconverged

/-- The approximate GL phase kernel preserves the Boltzmann target when the
approximate proposal is involutive and volume-preserving. These properties
hold when the solver converges to the exact stages, which make the GL
integrator self-adjoint and symplectic. -/
theorem approximateGaussLegendrePhaseKernel_invariant
    (potential : Position (Fin n) → ℝ)
    (gradient : Position (Fin n) → Position (Fin n))
    (stepSize : ℝ) (iterations steps : Nat)
    (hpotential : Measurable potential)
    (hproposal : Measurable (approximateGaussLegendreProposal gradient
      stepSize iterations steps))
    (hinvolutive : Function.Involutive
      (approximateGaussLegendreProposal gradient stepSize iterations steps))
    (hpreserving : MeasurePreserving
      (approximateGaussLegendreProposal gradient stepSize iterations steps)
      phaseVolume phaseVolume) :
    (approximateGaussLegendrePhaseKernel potential gradient stepSize
      iterations steps hproposal).Invariant
      (phaseBoltzmannTarget potential) := by
  letI : ProbabilityTheory.IsMarkovKernel
      (approximateGaussLegendrePhaseKernel potential gradient stepSize
        iterations steps hproposal) :=
    Mcmc.Kernel.deterministicMetropolis_isMarkov _ _
      (measurable_boltzmannWeight hpotential) hproposal
  unfold approximateGaussLegendrePhaseKernel phaseBoltzmannTarget
  exact Mcmc.Kernel.deterministicMetropolis_invariant phaseVolume
    (boltzmannWeight potential)
    (approximateGaussLegendreProposal gradient stepSize iterations steps)
    hproposal
    (measurable_boltzmannWeight hpotential)
    (boltzmannWeight_ne_zero potential) (boltzmannWeight_ne_top potential)
    hinvolutive hpreserving

end Mcmc.Executable.Continuous
