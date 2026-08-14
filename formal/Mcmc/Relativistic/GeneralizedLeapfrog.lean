import Mcmc.Relativistic.Hamiltonian
import Mcmc.Hamiltonian.VolumePreservation

/-!
# Generalized implicit leapfrog

Xu and Ge use the generalized leapfrog integrator for their nonseparable
Hamiltonian.  Its first momentum half-step and position step are implicit.
Writing these equations does not by itself define a function: solutions may
fail to exist, or there may be several solutions and an implementation may
select them inconsistently.

This module therefore separates:

* the three generalized-leapfrog equations;
* a selected solution of those equations; and
* the independent measurability, uniqueness, reversibility, and
  phase-volume-preservation properties required by HMC correctness.
-/

namespace Mcmc.Relativistic

open MeasureTheory
open Mcmc.Hamiltonian

variable {ι : Type*} [Fintype ι]

/-- The generalized-leapfrog equations for a nonseparable Hamiltonian.
`positionDerivative` is `∂H/∂q` and `momentumDerivative` is `∂H/∂p`. -/
def GeneralizedLeapfrogEquations
    (positionDerivative momentumDerivative :
      PhaseSpace ι → Position ι)
    (ε : ℝ) (z : PhaseSpace ι) (pHalf : Momentum ι)
    (zNext : PhaseSpace ι) : Prop :=
  pHalf = z.2 - (ε / 2) • positionDerivative (z.1, pHalf) ∧
  zNext.1 = z.1 + (ε / 2) •
    (momentumDerivative (z.1, pHalf) +
      momentumDerivative (zNext.1, pHalf)) ∧
  zNext.2 = pHalf - (ε / 2) •
    positionDerivative (zNext.1, pHalf)

/-- A concrete selection of solutions to the implicit generalized-leapfrog
equations.  This packages existence only; it deliberately does not assert
uniqueness, measurability, reversibility, or volume preservation. -/
structure GeneralizedLeapfrogSelection
    (positionDerivative momentumDerivative :
      PhaseSpace ι → Position ι) where
  halfMomentum : ℝ → PhaseSpace ι → Momentum ι
  step : ℝ → PhaseSpace ι → PhaseSpace ι
  satisfies : ∀ ε z,
    GeneralizedLeapfrogEquations positionDerivative momentumDerivative
      ε z (halfMomentum ε z) (step ε z)

/-- The selected generalized-leapfrog step is measurable for every step
size. -/
def GeneralizedLeapfrogSelection.IsMeasurable
    {positionDerivative momentumDerivative :
      PhaseSpace ι → Position ι}
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative) : Prop :=
  ∀ ε, Measurable (selection.step ε)

/-- The implicit equations have no solution other than the one selected by
`selection`. -/
def GeneralizedLeapfrogSelection.IsUnique
    {positionDerivative momentumDerivative :
      PhaseSpace ι → Position ι}
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative) : Prop :=
  ∀ ε z pHalf zNext,
    GeneralizedLeapfrogEquations positionDerivative momentumDerivative
      ε z pHalf zNext →
    pHalf = selection.halfMomentum ε z ∧ zNext = selection.step ε z

/-- Time reversal under momentum flip.  This is the generalized counterpart
of the exact identity proved for the explicit ordinary leapfrog map. -/
def GeneralizedLeapfrogSelection.IsReversible
    {positionDerivative momentumDerivative :
      PhaseSpace ι → Position ι}
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative) : Prop :=
  ∀ ε z,
    momentumFlip (selection.step ε (momentumFlip z)) =
      selection.step (-ε) z

/-- The selected step preserves the ambient phase-space volume for every
step size. -/
def GeneralizedLeapfrogSelection.IsVolumePreserving
    {positionDerivative momentumDerivative :
      PhaseSpace ι → Position ι}
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative) : Prop :=
  ∀ ε, MeasurePreserving (selection.step ε) phaseVolume phaseVolume

/-- Combined numerical-integrator certificate required by the later GR-HMC
kernel proof.  Each mathematical obligation remains available as a named
field. -/
structure GeneralizedLeapfrogSelection.IsValid
    {positionDerivative momentumDerivative :
      PhaseSpace ι → Position ι}
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative) : Prop where
  measurable : selection.IsMeasurable
  unique : selection.IsUnique
  reversible : selection.IsReversible
  volumePreserving : selection.IsVolumePreserving

omit [Fintype ι] in
/-- At zero step size, any solution of the generalized-leapfrog equations is
the identity transition with unchanged half momentum. -/
theorem GeneralizedLeapfrogEquations.zero
    (positionDerivative momentumDerivative : PhaseSpace ι → Position ι)
    (z : PhaseSpace ι) (pHalf : Momentum ι) (zNext : PhaseSpace ι)
    (h : GeneralizedLeapfrogEquations positionDerivative momentumDerivative
      0 z pHalf zNext) :
    pHalf = z.2 ∧ zNext = z := by
  rcases h with ⟨hp, hq, hpNext⟩
  simp only [zero_div, zero_smul, sub_zero] at hp hpNext
  simp only [zero_div, zero_smul, add_zero] at hq
  constructor
  · exact hp
  · apply Prod.ext
    · exact hq
    · simpa [hp] using hpNext

omit [Fintype ι] in
/-- Every selected generalized-leapfrog implementation is forced to be the
identity at step size zero. -/
theorem GeneralizedLeapfrogSelection.step_zero
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative) (z : PhaseSpace ι) :
    selection.step 0 z = z := by
  exact (GeneralizedLeapfrogEquations.zero positionDerivative
    momentumDerivative z (selection.halfMomentum 0 z)
      (selection.step 0 z) (selection.satisfies 0 z)).2

omit [Fintype ι] in
/-- Reversing the step size reverses every solution of the generalized
leapfrog equations.  Uniqueness therefore makes the selected negative step
the inverse of the selected positive step. -/
theorem GeneralizedLeapfrogSelection.step_neg_step
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hunique : selection.IsUnique) (ε : ℝ) (z : PhaseSpace ι) :
    selection.step (-ε) (selection.step ε z) = z := by
  let pHalf := selection.halfMomentum ε z
  have hforward := selection.satisfies ε z
  rcases hforward with ⟨hp, hq, hpNext⟩
  have hreverse : GeneralizedLeapfrogEquations positionDerivative
      momentumDerivative (-ε) (selection.step ε z) pHalf z := by
    constructor
    · dsimp only [pHalf]
      ext i
      have hi := congrFun hpNext i
      simp only [Pi.sub_apply, Pi.smul_apply, neg_div, smul_eq_mul] at hi ⊢
      linarith
    constructor
    · dsimp only [pHalf]
      ext i
      have hi := congrFun hq i
      simp only [Pi.add_apply, Pi.smul_apply, neg_div, smul_eq_mul] at hi ⊢
      linarith
    · dsimp only [pHalf]
      ext i
      have hi := congrFun hp i
      simp only [Pi.sub_apply, Pi.smul_apply, neg_div, smul_eq_mul] at hi ⊢
      linarith
  exact (hunique (-ε) (selection.step ε z) pHalf z hreverse).2.symm

omit [Fintype ι] in
/-- Momentum flip after a reversible, uniquely selected generalized-leapfrog
step is an involution, as required by endpoint Metropolis correction. -/
theorem GeneralizedLeapfrogSelection.momentumFlip_step_involutive
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hunique : selection.IsUnique) (hreversible : selection.IsReversible)
    (ε : ℝ) :
    Function.Involutive (momentumFlip ∘ selection.step ε) := by
  intro z
  simp only [Function.comp_apply]
  rw [hreversible ε (selection.step ε z)]
  exact selection.step_neg_step hunique ε z

end Mcmc.Relativistic
