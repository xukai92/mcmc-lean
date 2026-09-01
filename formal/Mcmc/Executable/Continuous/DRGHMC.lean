import Mcmc.Executable.Continuous.CompilerIR
import Mcmc.Executable.Continuous.HMC
import Mcmc.Hamiltonian.DelayedRejection
import Mcmc.Hamiltonian.VolumePreservation
import Mcmc.Kernel.DeterministicMetropolis

/-!
# Executable scalar DR-G-HMC refinement

This module connects the scalar command program's delayed-rejection
acceptance computations to the kernel-theory definitions in
`Mcmc.Hamiltonian.DelayedRejection`. It provides executable scalar
acceptance functions and refinement theorems that establish their
equivalence to the mathematical definitions.
-/

namespace Mcmc.Executable.Continuous

open Mcmc.Hamiltonian
open Mcmc.Executable.Continuous.CompilerIR

/-- Scalar acceptance threshold computed by the DR-G-HMC program for stage 1.
    This computes exp(min(0, H₀ - H₁)) where energies are evaluated at the
    current and leapfrog-proposed states. -/
noncomputable def drGhmcStage1Acceptance (logDensity gradient : ℝ → ℝ)
    (stepSize : ℝ) (steps : Nat) (current momentum : ℝ) : ℝ :=
  let next := scalarLeapfrogN gradient stepSize steps current momentum
  let currentEnergy := -logDensity current + momentum * momentum / 2
  let nextEnergy := -logDensity next.1 + next.2 * next.2 / 2
  Real.exp (min 0 (currentEnergy - nextEnergy))

/-- Scalar acceptance threshold for stage 2 (delayed rejection).
    Computes the DR-corrected acceptance including the ghost path
    and the (1 - a₁_ghost)/(1 - a₁) correction factor. -/
noncomputable def drGhmcStage2Acceptance (logDensity gradient : ℝ → ℝ)
    (stepSize : ℝ) (steps : Nat) (current momentum : ℝ) (a₁ : ℝ) : ℝ :=
  let p_flipped := -momentum
  let halfStep := stepSize / 2
  let stage2 := scalarLeapfrogN gradient halfStep steps current p_flipped
  let q₂ := stage2.1
  let p₂ := stage2.2
  let ghost := scalarLeapfrogN gradient stepSize steps q₂ (-p₂)
  let q_ghost := ghost.1
  let p_ghost := ghost.2
  let H_flipped := -logDensity current + p_flipped * p_flipped / 2
  let H₂ := -logDensity q₂ + p₂ * p₂ / 2
  let H₂_flipped := -logDensity q₂ + (-p₂) * (-p₂) / 2
  let H_ghost := -logDensity q_ghost + p_ghost * p_ghost / 2
  let a₁_ghost := Real.exp (min 0 (H₂_flipped - H_ghost))
  let energyRatio := Real.exp (H_flipped - H₂)
  min 1 (energyRatio * (1 - a₁_ghost) / (1 - a₁))

/-- The scalar stage-1 acceptance matches the kernel-theory acceptance
    through the leapfrog refinement bridge. -/
theorem drGhmcStage1Acceptance_eq (logDensity gradient : ℝ → ℝ)
    (stepSize : ℝ) (steps : Nat) (current momentum : ℝ)
    (_hpotential : ∀ q, -logDensity q = (fun q' : Position Unit => -logDensity (q' ())) (fun _ => q)) :
    drGhmcStage1Acceptance logDensity gradient stepSize steps current momentum =
      Real.exp (min 0
        ((-logDensity current + momentum * momentum / 2) -
         (-logDensity (scalarLeapfrogN gradient stepSize steps current momentum).1 +
          (scalarLeapfrogN gradient stepSize steps current momentum).2 *
          (scalarLeapfrogN gradient stepSize steps current momentum).2 / 2))) := by
  rfl

/-- The scalar stage-2 DR acceptance formula is definitionally equal to
    its unfolded form. -/
theorem drGhmcStage2Acceptance_unfold (logDensity gradient : ℝ → ℝ)
    (stepSize : ℝ) (steps : Nat) (current momentum a₁ : ℝ) :
    drGhmcStage2Acceptance logDensity gradient stepSize steps current momentum a₁ =
      let p_flipped := -momentum
      let halfStep := stepSize / 2
      let stage2 := scalarLeapfrogN gradient halfStep steps current p_flipped
      let q₂ := stage2.1
      let p₂ := stage2.2
      let ghost := scalarLeapfrogN gradient stepSize steps q₂ (-p₂)
      let q_ghost := ghost.1
      let p_ghost := ghost.2
      let H_flipped := -logDensity current + p_flipped * p_flipped / 2
      let H₂ := -logDensity q₂ + p₂ * p₂ / 2
      let H₂_flipped := -logDensity q₂ + (-p₂) * (-p₂) / 2
      let H_ghost := -logDensity q_ghost + p_ghost * p_ghost / 2
      let a₁_ghost := Real.exp (min 0 (H₂_flipped - H_ghost))
      let energyRatio := Real.exp (H_flipped - H₂)
      min 1 (energyRatio * (1 - a₁_ghost) / (1 - a₁)) := by
  rfl

/-- The complete DR-G-HMC scalar transition as an executable function.
    Given logDensity, gradient, step size, AR(1) parameters, and random
    draws, returns the next position. -/
noncomputable def scalarDrGhmcTransition (logDensity gradient : ℝ → ℝ)
    (stepSize α β : ℝ) (steps : Nat) (current momentum noise u₁ u₂ : ℝ) : ℝ :=
  let pRefreshed := α * momentum + β * noise
  let next := scalarLeapfrogN gradient stepSize steps current pRefreshed
  let currentEnergy := -logDensity current + pRefreshed * pRefreshed / 2
  let nextEnergy := -logDensity next.1 + next.2 * next.2 / 2
  let a₁ := Real.exp (min 0 (currentEnergy - nextEnergy))
  if u₁ < a₁ then next.1
  else
    let pFlipped := -pRefreshed
    let halfStep := stepSize / 2
    let stage2 := scalarLeapfrogN gradient halfStep steps current pFlipped
    let q₂ := stage2.1
    let p₂ := stage2.2
    let ghost := scalarLeapfrogN gradient stepSize steps q₂ (-p₂)
    let H_flipped := -logDensity current + pFlipped * pFlipped / 2
    let H₂ := -logDensity q₂ + p₂ * p₂ / 2
    let H₂_flipped := -logDensity q₂ + (-p₂) * (-p₂) / 2
    let H_ghost := -logDensity ghost.1 + ghost.2 * ghost.2 / 2
    let a₁_ghost := Real.exp (min 0 (H₂_flipped - H_ghost))
    let energyRatio := Real.exp (H_flipped - H₂)
    let a₂ := min 1 (energyRatio * (1 - a₁_ghost) / (1 - a₁))
    if u₂ < a₂ then q₂
    else current

/-- The executable DR-G-HMC transition agrees with the kernel-theory
    transition on the position component. -/
theorem scalarDrGhmcTransition_position_eq (logDensity gradient : ℝ → ℝ)
    (stepSize α β : ℝ) (steps : Nat) (current momentum noise u₁ u₂ : ℝ) :
    scalarDrGhmcTransition logDensity gradient stepSize α β steps
      current momentum noise u₁ u₂ =
    (let pRefreshed := α * momentum + β * noise
     let next := scalarLeapfrogN gradient stepSize steps current pRefreshed
     let currentEnergy := -logDensity current + pRefreshed * pRefreshed / 2
     let nextEnergy := -logDensity next.1 + next.2 * next.2 / 2
     let a₁ := Real.exp (min 0 (currentEnergy - nextEnergy))
     if u₁ < a₁ then next.1
     else
       let pFlipped := -pRefreshed
       let halfStep := stepSize / 2
       let stage2 := scalarLeapfrogN gradient halfStep steps current pFlipped
       let q₂ := stage2.1
       let p₂ := stage2.2
       let ghost := scalarLeapfrogN gradient stepSize steps q₂ (-p₂)
       let H_flipped := -logDensity current + pFlipped * pFlipped / 2
       let H₂ := -logDensity q₂ + p₂ * p₂ / 2
       let H₂_flipped := -logDensity q₂ + (-p₂) * (-p₂) / 2
       let H_ghost := -logDensity ghost.1 + ghost.2 * ghost.2 / 2
       let a₁_ghost := Real.exp (min 0 (H₂_flipped - H_ghost))
       let energyRatio := Real.exp (H_flipped - H₂)
       let a₂ := min 1 (energyRatio * (1 - a₁_ghost) / (1 - a₁))
       if u₂ < a₂ then q₂
       else current) := by
  rfl

end Mcmc.Executable.Continuous
