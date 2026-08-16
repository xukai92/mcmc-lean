import Mcmc.Kernel.OrbitMultinomial
import Mcmc.Relativistic.EndpointMetropolis

/-!
# Multinomial general-relativistic HMC

This module instantiates the generic measure-preserving-orbit multinomial
kernel with a valid selected generalized-leapfrog step.  It formalizes the
multinomial correction described by Xu and Ge without assuming a separable
Hamiltonian or reusing the explicit Euclidean leapfrog formula.
-/

namespace Mcmc.Relativistic

open MeasureTheory
open Mcmc.Hamiltonian
open Mcmc.Kernel
open ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- A uniquely selected generalized-leapfrog step as a permutation, with the
negative step as its inverse. -/
noncomputable def generalizedLeapfrogPerm
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hunique : selection.IsUnique) (ε : ℝ) : Equiv.Perm (PhaseSpace ι) where
  toFun := selection.step ε
  invFun := selection.step (-ε)
  left_inv := selection.step_neg_step hunique ε
  right_inv z := by
    simpa only [neg_neg] using selection.step_neg_step hunique (-ε) z

omit [Fintype ι] in
@[simp]
theorem generalizedLeapfrogPerm_apply
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hunique : selection.IsUnique) (ε : ℝ) (z : PhaseSpace ι) :
    generalizedLeapfrogPerm selection hunique ε z = selection.step ε z :=
  rfl

omit [Fintype ι] in
@[simp]
theorem generalizedLeapfrogPerm_symm_apply
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hunique : selection.IsUnique) (ε : ℝ) (z : PhaseSpace ι) :
    (generalizedLeapfrogPerm selection hunique ε).symm z =
      selection.step (-ε) z :=
  rfl

omit [Fintype ι] in
/-- The selected generalized-leapfrog permutation is identity at zero step
size. -/
theorem generalizedLeapfrogPerm_zero
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hunique : selection.IsUnique) :
    generalizedLeapfrogPerm selection hunique 0 = 1 := by
  apply Equiv.ext
  intro z
  exact selection.step_zero z

/-- Random-origin, Boltzmann-weighted multinomial selection along a
generalized-leapfrog orbit. -/
noncomputable def multinomialGRHMCPhase
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (potential : Position ι → ℝ)
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid)
    (hH : Measurable
      (generalRelativisticHamiltonian potential metric m c))
    (ε : ℝ) (L : ℕ) : Kernel (PhaseSpace ι) (PhaseSpace ι) :=
  orbitMultinomialKernel
    (generalRelativisticBoltzmannWeight potential metric m c)
    (generalizedLeapfrogPerm selection hvalid.unique ε) L
    (generalRelativisticBoltzmannWeight_ne_zero potential metric m c)
    (generalRelativisticBoltzmannWeight_ne_top potential metric m c)
    (measurable_generalRelativisticBoltzmannWeight potential metric m c hH)
    (hvalid.measurable ε) (hvalid.measurable (-ε))

instance multinomialGRHMCPhase_isMarkovKernel
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (potential : Position ι → ℝ)
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid)
    (hH : Measurable
      (generalRelativisticHamiltonian potential metric m c))
    (ε : ℝ) (L : ℕ) :
    IsMarkovKernel
      (multinomialGRHMCPhase potential metric m c selection hvalid hH ε L) := by
  unfold multinomialGRHMCPhase
  infer_instance

/-- With no trajectory steps, phase-space multinomial GR-HMC is exactly the
identity kernel, independently of the selected solver. -/
theorem multinomialGRHMCPhase_zero
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (potential : Position ι → ℝ)
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid)
    (hH : Measurable
      (generalRelativisticHamiltonian potential metric m c))
    (ε : ℝ) :
    multinomialGRHMCPhase potential metric m c selection hvalid hH ε 0 =
      Kernel.id := by
  unfold multinomialGRHMCPhase
  exact orbitMultinomialKernel_zero _ _ _ _ _ _ _

/-- At zero step size every orbit point is the current state, so phase-space
multinomial GR-HMC is identity for every nominal trajectory length. -/
theorem multinomialGRHMCPhase_step_zero
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (potential : Position ι → ℝ)
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid)
    (hH : Measurable
      (generalRelativisticHamiltonian potential metric m c))
    (L : ℕ) :
    multinomialGRHMCPhase potential metric m c selection hvalid hH 0 L =
      Kernel.id := by
  unfold multinomialGRHMCPhase
  apply orbitMultinomialKernel_eq_id_of_eq_one
  exact generalizedLeapfrogPerm_zero selection hvalid.unique

/-- The multinomial generalized-leapfrog transition satisfies detailed
balance for the complete GR phase target. -/
theorem multinomialGRHMCPhase_isReversible
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (potential : Position ι → ℝ)
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid)
    (hH : Measurable
      (generalRelativisticHamiltonian potential metric m c))
    (ε : ℝ) (L : ℕ) :
    (multinomialGRHMCPhase potential metric m c selection hvalid hH ε L).IsReversible
      (generalRelativisticPhaseTarget potential metric m c) := by
  unfold multinomialGRHMCPhase generalRelativisticPhaseTarget
  have hforward : MeasurePreserving
      (generalizedLeapfrogPerm selection hvalid.unique ε)
      phaseVolume phaseVolume :=
    hvalid.volumePreserving ε
  have hreverse : MeasurePreserving
      (generalizedLeapfrogPerm selection hvalid.unique ε).symm
      phaseVolume phaseVolume :=
    hvalid.volumePreserving (-ε)
  exact orbitMultinomialKernel_isReversible
    (generalRelativisticBoltzmannWeight_ne_zero potential metric m c)
    (generalRelativisticBoltzmannWeight_ne_top potential metric m c)
    (measurable_generalRelativisticBoltzmannWeight potential metric m c hH)
    hforward hreverse L

/-- Exact phase-target invariance of multinomial GR-HMC, conditional on the
generalized-leapfrog validity certificate. -/
theorem multinomialGRHMCPhase_invariant
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (potential : Position ι → ℝ)
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid)
    (hH : Measurable
      (generalRelativisticHamiltonian potential metric m c))
    (ε : ℝ) (L : ℕ) :
    (multinomialGRHMCPhase potential metric m c selection hvalid hH ε L).Invariant
      (generalRelativisticPhaseTarget potential metric m c) :=
  (multinomialGRHMCPhase_isReversible potential metric m c selection hvalid
    hH ε L).invariant

/-- User-facing multinomial GR-HMC: refresh the position-dependent momentum,
run the randomized multinomial phase transition, and project to position. -/
noncomputable def positionMultinomialGRHMC
    [Nonempty ι] [DecidableEq ι]
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (potential : Position ι → ℝ)
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (hm : 0 < m) (hc : 0 < c)
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid)
    (hH : Measurable
      (generalRelativisticHamiltonian potential metric m c))
    (hmeasurableMomentum :
      IsMeasurableRiemannianMomentumFamily metric m c hm hc)
    (ε : ℝ) (L : ℕ) : Kernel (Position ι) (Position ι) :=
  (multinomialGRHMCPhase potential metric m c selection hvalid hH ε L ∘ₖ
    riemannianPositionMomentumLift metric m c hm hc hmeasurableMomentum).map
      (Prod.fst : PhaseSpace ι → Position ι)

instance positionMultinomialGRHMC_isMarkovKernel
    [Nonempty ι] [DecidableEq ι]
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (potential : Position ι → ℝ)
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (hm : 0 < m) (hc : 0 < c)
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid)
    (hH : Measurable
      (generalRelativisticHamiltonian potential metric m c))
    (hmeasurableMomentum :
      IsMeasurableRiemannianMomentumFamily metric m c hm hc)
    (ε : ℝ) (L : ℕ) :
    IsMarkovKernel (positionMultinomialGRHMC potential metric m c hm hc
      selection hvalid hH hmeasurableMomentum ε L) := by
  unfold positionMultinomialGRHMC
  exact Kernel.IsMarkovKernel.map _ measurable_fst

/-- Momentum refresh cannot create position movement when the multinomial
orbit has length zero: the user-facing position transition is identity. -/
theorem positionMultinomialGRHMC_zero
    [Nonempty ι] [DecidableEq ι]
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (potential : Position ι → ℝ)
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (hm : 0 < m) (hc : 0 < c)
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid)
    (hH : Measurable
      (generalRelativisticHamiltonian potential metric m c))
    (hmeasurableMomentum :
      IsMeasurableRiemannianMomentumFamily metric m c hm hc)
    (ε : ℝ) :
    positionMultinomialGRHMC potential metric m c hm hc selection hvalid hH
      hmeasurableMomentum ε 0 = Kernel.id := by
  unfold positionMultinomialGRHMC
  rw [multinomialGRHMCPhase_zero]
  ext q s hs
  rw [Kernel.map_apply'
    (Kernel.id ∘ₖ riemannianPositionMomentumLift metric m c hm hc
      hmeasurableMomentum) measurable_fst q hs]
  rw [Kernel.id_comp]
  rw [riemannianPositionMomentumLift, Kernel.prod_apply, Kernel.id_apply]
  rw [show Prod.fst ⁻¹' s = s ×ˢ (Set.univ : Set (Momentum ι)) by ext; simp,
    Measure.prod_prod, Measure.dirac_apply' _ hs, measure_univ]
  by_cases hq : q ∈ s <;> simp [hq]

/-- The user-facing position transition is also identity at zero step size,
regardless of its nominal trajectory length. -/
theorem positionMultinomialGRHMC_step_zero
    [Nonempty ι] [DecidableEq ι]
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (potential : Position ι → ℝ)
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (hm : 0 < m) (hc : 0 < c)
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid)
    (hH : Measurable
      (generalRelativisticHamiltonian potential metric m c))
    (hmeasurableMomentum :
      IsMeasurableRiemannianMomentumFamily metric m c hm hc)
    (L : ℕ) :
    positionMultinomialGRHMC potential metric m c hm hc selection hvalid hH
      hmeasurableMomentum 0 L = Kernel.id := by
  unfold positionMultinomialGRHMC
  rw [multinomialGRHMCPhase_step_zero]
  ext q s hs
  rw [Kernel.map_apply'
    (Kernel.id ∘ₖ riemannianPositionMomentumLift metric m c hm hc
      hmeasurableMomentum) measurable_fst q hs]
  rw [Kernel.id_comp]
  rw [riemannianPositionMomentumLift, Kernel.prod_apply, Kernel.id_apply]
  rw [show Prod.fst ⁻¹' s = s ×ˢ (Set.univ : Set (Momentum ι)) by ext; simp,
    Measure.prod_prod, Measure.dirac_apply' _ hs, measure_univ]
  by_cases hq : q ∈ s <;> simp [hq]

/-- Under the same explicit disintegration compatibility equation as endpoint
GR-HMC, the full position-space multinomial algorithm preserves its target. -/
theorem positionMultinomialGRHMC_invariant
    [Nonempty ι] [DecidableEq ι]
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (potential : Position ι → ℝ)
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (hm : 0 < m) (hc : 0 < c)
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid)
    (hH : Measurable
      (generalRelativisticHamiltonian potential metric m c))
    (hmeasurableMomentum :
      IsMeasurableRiemannianMomentumFamily metric m c hm hc)
    (ε : ℝ) (L : ℕ)
    (positionTarget : Measure (Position ι)) [SFinite positionTarget]
    (hcompat : IsCompatibleGRPositionTarget potential metric m c hm hc
      hmeasurableMomentum positionTarget) :
    (positionMultinomialGRHMC potential metric m c hm hc selection hvalid hH
      hmeasurableMomentum ε L).Invariant positionTarget := by
  let momentumKernel :=
    riemannianMomentumKernel metric m c hm hc hmeasurableMomentum
  let phaseKernel :=
    multinomialGRHMCPhase potential metric m c selection hvalid hH ε L
  change (Mcmc.Kernel.liftEvolveProject
    (riemannianPositionMomentumLift metric m c hm hc hmeasurableMomentum)
    phaseKernel (Prod.fst : PhaseSpace ι → Position ι)
    measurable_fst).Invariant positionTarget
  have hphase := multinomialGRHMCPhase_invariant potential metric m c selection
    hvalid hH ε L
  change phaseKernel.Invariant
    (generalRelativisticPhaseTarget potential metric m c) at hphase
  change positionTarget ⊗ₘ momentumKernel =
    generalRelativisticPhaseTarget potential metric m c at hcompat
  rw [← hcompat] at hphase
  unfold riemannianPositionMomentumLift
  exact Mcmc.Kernel.compProdEvolveFst_invariant positionTarget
    momentumKernel phaseKernel hphase

end Mcmc.Relativistic
