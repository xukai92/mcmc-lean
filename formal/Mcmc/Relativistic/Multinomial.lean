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

/-- A uniform one-sided Hamiltonian-error bound over an orbit gives an
explicit floor for selecting a designated index. -/
theorem inv_card_exp_le_multinomialGRHMCPhase_indexProbability
    {positionDerivative momentumDerivative : PhaseSpace ι → Position ι}
    (potential : Position ι → ℝ)
    (metric : FactoredRiemannianMetric ι) (m c : ℝ)
    (selection : GeneralizedLeapfrogSelection
      positionDerivative momentumDerivative)
    (hvalid : selection.IsValid) (ε : ℝ) {L : ℕ}
    (origin selected : Fin (L + 1)) (z : PhaseSpace ι) (D : ℝ)
    (henergy : ∀ i : Fin (L + 1),
      generalRelativisticHamiltonian potential metric m c
          (orbitPoint (generalizedLeapfrogPerm selection hvalid.unique ε)
            origin z selected) -
        generalRelativisticHamiltonian potential metric m c
          (orbitPoint (generalizedLeapfrogPerm selection hvalid.unique ε)
            origin z i) ≤ D) :
    (((L + 1 : ℕ) : ENNReal) * ENNReal.ofReal (Real.exp D))⁻¹ ≤
      orbitIndexProbability
        (generalRelativisticBoltzmannWeight potential metric m c)
        (generalizedLeapfrogPerm selection hvalid.unique ε)
        origin selected z := by
  apply inv_card_mul_le_orbitIndexProbability
    (generalRelativisticBoltzmannWeight_ne_zero potential metric m c)
    (generalRelativisticBoltzmannWeight_ne_top potential metric m c)
  intro i
  exact generalRelativisticBoltzmannWeight_le_exp_mul_of_sub_le
    potential metric m c _ _ (henergy i)

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

/-- Exact nested-integral semantics of the user-facing position-space
multinomial GR-HMC transition. -/
theorem lintegral_positionMultinomialGRHMC
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
    (ε : ℝ) (L : ℕ) (f : Position ι → ENNReal) (hf : Measurable f)
    (q : Position ι) :
    (∫⁻ y, f y ∂positionMultinomialGRHMC potential metric m c hm hc
      selection hvalid hH hmeasurableMomentum ε L q) =
      ∫⁻ p, ∫⁻ z, f z.1
          ∂multinomialGRHMCPhase potential metric m c selection hvalid hH ε L
            (q, p)
        ∂riemannianMomentumKernel metric m c hm hc hmeasurableMomentum q := by
  let g : PhaseSpace ι → ENNReal := fun z => f z.1
  have hg : Measurable g := hf.comp measurable_fst
  rw [positionMultinomialGRHMC,
    Kernel.lintegral_map _ measurable_fst _ hf,
    Kernel.lintegral_comp _ _ _ hg]
  unfold riemannianPositionMomentumLift
  rw [Kernel.prod_apply, Kernel.id_apply]
  change (∫⁻ z, ∫⁻ w, g w
      ∂multinomialGRHMCPhase potential metric m c selection hvalid hH ε L z
      ∂(Measure.dirac q).prod
        (riemannianMomentumKernel metric m c hm hc hmeasurableMomentum q)) = _
  rw [MeasureTheory.lintegral_prod _ hg.lintegral_kernel.aemeasurable,
    lintegral_dirac' q hg.lintegral_kernel.lintegral_prod_right]

/-- A phase-kernel event floor on a measurable momentum subset propagates
through momentum refresh and position projection. -/
theorem momentumMeasure_mul_le_positionMultinomialGRHMC_apply
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
    (ε : ℝ) (L : ℕ) (q : Position ι)
    {momentumSet : Set (Momentum ι)} (hmomentumSet : MeasurableSet momentumSet)
    {positionSet : Set (Position ι)} (hpositionSet : MeasurableSet positionSet)
    (a : ENNReal)
    (hphase : ∀ p ∈ momentumSet, a ≤
      multinomialGRHMCPhase potential metric m c selection hvalid hH ε L
        (q, p) (Prod.fst ⁻¹' positionSet)) :
    riemannianMomentumKernel metric m c hm hc hmeasurableMomentum q
        momentumSet * a ≤
      positionMultinomialGRHMC potential metric m c hm hc selection hvalid hH
        hmeasurableMomentum ε L q positionSet := by
  rw [← lintegral_indicator_one hpositionSet]
  change riemannianMomentumKernel metric m c hm hc hmeasurableMomentum q
      momentumSet * a ≤
    ∫⁻ y, positionSet.indicator (fun _ => (1 : ENNReal)) y
      ∂positionMultinomialGRHMC potential metric m c hm hc selection hvalid hH
        hmeasurableMomentum ε L q
  rw [lintegral_positionMultinomialGRHMC potential metric m c hm hc
    selection hvalid hH hmeasurableMomentum ε L
    (positionSet.indicator fun _ => (1 : ENNReal))
    (measurable_const.indicator hpositionSet) q]
  change riemannianMomentumKernel metric m c hm hc hmeasurableMomentum q
      momentumSet * a ≤
    ∫⁻ p, ∫⁻ z, positionSet.indicator (fun _ => (1 : ENNReal)) z.1
      ∂multinomialGRHMCPhase potential metric m c selection hvalid hH ε L
        (q, p)
      ∂riemannianMomentumKernel metric m c hm hc hmeasurableMomentum q
  calc
    riemannianMomentumKernel metric m c hm hc hmeasurableMomentum q
        momentumSet * a =
      ∫⁻ p, momentumSet.indicator (fun _ => a) p
        ∂riemannianMomentumKernel metric m c hm hc hmeasurableMomentum q := by
          rw [lintegral_indicator_const hmomentumSet]
          ac_rfl
    _ ≤ _ := by
      apply lintegral_mono
      intro p
      by_cases hp : p ∈ momentumSet
      · rw [Set.indicator_of_mem hp]
        change a ≤
          ∫⁻ z, (Prod.fst ⁻¹' positionSet).indicator
            (1 : PhaseSpace ι → ENNReal) z
            ∂multinomialGRHMCPhase potential metric m c selection hvalid hH
              ε L (q, p)
        rw [lintegral_indicator_one (measurable_fst hpositionSet)]
        exact hphase p hp
      · simp [Set.indicator, hp]

/-- A uniform selected-index floor pushes the refreshed momentum mass of all
momenta whose selected endpoint lands in a position event into the
position-space transition. This is the integral-level selected-branch bridge
used by local-minorization arguments. -/
theorem uniform_mul_floor_mul_selectedMomentumSet_le_positionMultinomialGRHMC_apply
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
    (ε : ℝ) {L : ℕ} (origin selected : Fin (L + 1))
    (q : Position ι) {momentumSet : Set (Momentum ι)}
    (hmomentumSet : MeasurableSet momentumSet)
    (hcandidate : Measurable (fun p : Momentum ι =>
      (orbitPoint (generalizedLeapfrogPerm selection hvalid.unique ε)
        origin (q, p) selected).1))
    {positionSet : Set (Position ι)}
    (hpositionSet : MeasurableSet positionSet) (floor : ENNReal)
    (hfloor : ∀ p ∈ momentumSet, floor ≤
      orbitIndexProbability
        (generalRelativisticBoltzmannWeight potential metric m c)
        (generalizedLeapfrogPerm selection hvalid.unique ε)
        origin selected (q, p)) :
    riemannianMomentumKernel metric m c hm hc hmeasurableMomentum q
        (momentumSet ∩ {p | (orbitPoint
          (generalizedLeapfrogPerm selection hvalid.unique ε)
          origin (q, p) selected).1 ∈ positionSet}) *
          (PMF.uniformOfFintype (Fin (L + 1)) origin * floor) ≤
      positionMultinomialGRHMC potential metric m c hm hc selection hvalid hH
        hmeasurableMomentum ε L q positionSet := by
  let selectedMomentumSet : Set (Momentum ι) :=
    momentumSet ∩ {p | (orbitPoint
      (generalizedLeapfrogPerm selection hvalid.unique ε)
      origin (q, p) selected).1 ∈ positionSet}
  have hselectedMomentumSet : MeasurableSet selectedMomentumSet :=
    hmomentumSet.inter (hpositionSet.preimage hcandidate)
  apply momentumMeasure_mul_le_positionMultinomialGRHMC_apply
    potential metric m c hm hc selection hvalid hH hmeasurableMomentum
    ε L q hselectedMomentumSet hpositionSet
  intro p hp
  have hbranch :=
    uniform_mul_indexProbability_le_orbitMultinomialKernel_apply
      (generalRelativisticBoltzmannWeight potential metric m c)
      (generalizedLeapfrogPerm selection hvalid.unique ε)
      (generalRelativisticBoltzmannWeight_ne_zero potential metric m c)
      (generalRelativisticBoltzmannWeight_ne_top potential metric m c)
      (measurable_generalRelativisticBoltzmannWeight potential metric m c hH)
      (hvalid.measurable ε) (hvalid.measurable (-ε))
      origin selected (q, p) (measurable_fst hpositionSet) hp.2
  exact (mul_le_mul_right (hfloor p hp.1)
    (PMF.uniformOfFintype (Fin (L + 1)) origin)).trans hbranch

/-- Pushforward form of the selected-branch lower bound. If every momentum
whose selected endpoint lands in the requested event belongs to the region
where the index floor holds, the selected endpoint's pushforward law is
dominated by the complete position transition. -/
theorem map_selectedEndpoint_mul_uniform_mul_floor_le_positionMultinomialGRHMC_apply
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
    (ε : ℝ) {L : ℕ} (origin selected : Fin (L + 1))
    (q : Position ι) {momentumSet : Set (Momentum ι)}
    (hmomentumSet : MeasurableSet momentumSet)
    (hcandidate : Measurable (fun p : Momentum ι =>
      (orbitPoint (generalizedLeapfrogPerm selection hvalid.unique ε)
        origin (q, p) selected).1))
    {positionSet : Set (Position ι)}
    (hpositionSet : MeasurableSet positionSet) (floor : ENNReal)
    (hfloor : ∀ p ∈ momentumSet, floor ≤
      orbitIndexProbability
        (generalRelativisticBoltzmannWeight potential metric m c)
        (generalizedLeapfrogPerm selection hvalid.unique ε)
        origin selected (q, p))
    (hpreimage : ∀ p, (orbitPoint
      (generalizedLeapfrogPerm selection hvalid.unique ε)
      origin (q, p) selected).1 ∈ positionSet → p ∈ momentumSet) :
    Measure.map (fun p : Momentum ι =>
        (orbitPoint (generalizedLeapfrogPerm selection hvalid.unique ε)
          origin (q, p) selected).1)
        (riemannianMomentumKernel metric m c hm hc hmeasurableMomentum q)
        positionSet *
          (PMF.uniformOfFintype (Fin (L + 1)) origin * floor) ≤
      positionMultinomialGRHMC potential metric m c hm hc selection hvalid hH
        hmeasurableMomentum ε L q positionSet := by
  rw [Measure.map_apply hcandidate hpositionSet]
  have h :=
    uniform_mul_floor_mul_selectedMomentumSet_le_positionMultinomialGRHMC_apply
      potential metric m c hm hc selection hvalid hH hmeasurableMomentum
      ε origin selected q hmomentumSet hcandidate hpositionSet floor hfloor
  have hinter : momentumSet ∩ {p | (orbitPoint
      (generalizedLeapfrogPerm selection hvalid.unique ε)
      origin (q, p) selected).1 ∈ positionSet} =
      {p | (orbitPoint
        (generalizedLeapfrogPerm selection hvalid.unique ε)
        origin (q, p) selected).1 ∈ positionSet} := by
    apply Set.inter_eq_right.mpr
    intro p hp
    exact hpreimage p hp
  rw [hinter] at h
  change riemannianMomentumKernel metric m c hm hc hmeasurableMomentum q
      {p | (orbitPoint
        (generalizedLeapfrogPerm selection hvalid.unique ε)
        origin (q, p) selected).1 ∈ positionSet} *
        (PMF.uniformOfFintype (Fin (L + 1)) origin * floor) ≤
      positionMultinomialGRHMC potential metric m c hm hc selection hvalid hH
        hmeasurableMomentum ε L q positionSet
  exact h

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
