import Mcmc.Finite.MarginalRepair
import Mcmc.Finite.Transport
import Mcmc.Hamiltonian.HMC
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Coupled multinomial trajectory transitions

This module lifts a measurable coupling of the two categorical trajectory-index
laws to a coupling of multinomial HMC trajectory transitions.  Both chains use
the same uniformly sampled trajectory origin.  Conditional on that origin, an
arbitrary joint index PMF may be used, provided its marginals are the two
Boltzmann index PMFs and its point probabilities depend measurably on the input
phase-point pair.

The construction is deliberately independent of how the categorical coupling
is obtained.  Maximal and transport couplings can therefore instantiate the
same kernel and marginal-correctness theorem.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace Mcmc.Hamiltonian

open ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- Copy one momentum draw into both momentum coordinates. -/
noncomputable def diagonalMomentumMeasure
    (momentumTarget : Measure (Momentum ι)) :
    Measure (Momentum ι × Momentum ι) :=
  momentumTarget.map fun p => (p, p)

instance diagonalMomentumMeasure_isProbabilityMeasure
    (momentumTarget : Measure (Momentum ι))
    [IsProbabilityMeasure momentumTarget] :
    IsProbabilityMeasure (diagonalMomentumMeasure momentumTarget) := by
  unfold diagonalMomentumMeasure
  exact Measure.isProbabilityMeasure_map
    (measurable_id.prodMk measurable_id).aemeasurable

omit [Fintype ι] in
theorem diagonalMomentumMeasure_fst
    (momentumTarget : Measure (Momentum ι)) :
    Measure.map Prod.fst (diagonalMomentumMeasure momentumTarget) =
      momentumTarget := by
  unfold diagonalMomentumMeasure
  rw [Measure.map_map measurable_fst (by fun_prop)]
  change Measure.map id momentumTarget = momentumTarget
  exact Measure.map_id

omit [Fintype ι] in
theorem diagonalMomentumMeasure_snd
    (momentumTarget : Measure (Momentum ι)) :
    Measure.map Prod.snd (diagonalMomentumMeasure momentumTarget) =
      momentumTarget := by
  unfold diagonalMomentumMeasure
  rw [Measure.map_map measurable_snd (by fun_prop)]
  change Measure.map id momentumTarget = momentumTarget
  exact Measure.map_id

/-- Reassociate a pair of positions and a pair of momenta into a pair of phase
points. -/
def reassociatePhasePair
    (x : (Position ι × Position ι) × (Momentum ι × Momentum ι)) :
    PhaseSpace ι × PhaseSpace ι :=
  ((x.1.1, x.2.1), (x.1.2, x.2.2))

omit [Fintype ι] in
theorem measurable_reassociatePhasePair :
    Measurable (reassociatePhasePair (ι := ι)) := by
  unfold reassociatePhasePair
  fun_prop

/-- Retain both positions and augment them with one shared momentum draw. -/
noncomputable def sharedPositionMomentumLift
    (momentumTarget : Measure (Momentum ι)) :
    Kernel (Position ι × Position ι) (PhaseSpace ι × PhaseSpace ι) :=
  (Kernel.id ×ₖ Kernel.const (Position ι × Position ι)
    (diagonalMomentumMeasure momentumTarget)).map reassociatePhasePair

instance sharedPositionMomentumLift_isMarkovKernel
    (momentumTarget : Measure (Momentum ι))
    [IsProbabilityMeasure momentumTarget] :
    IsMarkovKernel (sharedPositionMomentumLift momentumTarget) := by
  unfold sharedPositionMomentumLift
  exact Kernel.IsMarkovKernel.map _ measurable_reassociatePhasePair

omit [Fintype ι] in
/-- A shared position-to-phase lift is the pushforward of the momentum law by
the map that inserts the same momentum into both position coordinates. -/
theorem sharedPositionMomentumLift_apply
    (momentumTarget : Measure (Momentum ι)) [SFinite momentumTarget]
    (q : Position ι × Position ι) :
    sharedPositionMomentumLift momentumTarget q =
      momentumTarget.map fun p => ((q.1, p), (q.2, p)) := by
  unfold sharedPositionMomentumLift diagonalMomentumMeasure
  rw [Kernel.map_apply _ measurable_reassociatePhasePair,
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
    Measure.dirac_prod]
  rw [Measure.map_map measurable_reassociatePhasePair
      (by fun_prop : Measurable (Prod.mk q)),
    Measure.map_map (measurable_reassociatePhasePair.comp (by fun_prop))
      (by fun_prop)]
  congr 1

/-- Shared momentum augmentation is a coupling of the ordinary one-chain
position-to-phase momentum lifts. -/
theorem sharedPositionMomentumLift_isCoupling
    (momentumTarget : Measure (Momentum ι))
    [IsProbabilityMeasure momentumTarget] :
    Mcmc.Kernel.IsCoupling
      (sharedPositionMomentumLift momentumTarget)
      (positionMomentumLift momentumTarget)
      (positionMomentumLift momentumTarget) := by
  constructor
  · ext q : 1
    rw [Kernel.comap_apply, Kernel.fst_apply]
    unfold sharedPositionMomentumLift
    rw [Kernel.map_apply _ measurable_reassociatePhasePair]
    rw [Measure.map_map measurable_fst measurable_reassociatePhasePair]
    rw [Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply]
    change Measure.map (Prod.map Prod.fst Prod.fst)
        ((Measure.dirac q).prod (diagonalMomentumMeasure momentumTarget)) = _
    rw [← Measure.map_prod_map _ _ measurable_fst measurable_fst]
    rw [Measure.map_dirac, diagonalMomentumMeasure_fst]
    rw [positionMomentumLift, Kernel.prod_apply, Kernel.id_apply,
      Kernel.const_apply]
  · ext q : 1
    rw [Kernel.comap_apply, Kernel.snd_apply]
    unfold sharedPositionMomentumLift
    rw [Kernel.map_apply _ measurable_reassociatePhasePair]
    rw [Measure.map_map measurable_snd measurable_reassociatePhasePair]
    rw [Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply]
    change Measure.map (Prod.map Prod.snd Prod.snd)
        ((Measure.dirac q).prod (diagonalMomentumMeasure momentumTarget)) = _
    rw [← Measure.map_prod_map _ _ measurable_snd measurable_snd]
    rw [Measure.map_dirac, diagonalMomentumMeasure_snd]
    rw [positionMomentumLift, Kernel.prod_apply, Kernel.id_apply,
      Kernel.const_apply]

/-- Map a coupled pair of selected trajectory indices to the corresponding
pair of phase points. -/
noncomputable def coupledTrajectoryOutput
    (gradient : Position ι → Position ι) (ε : ℝ) {L : ℕ}
    (origin : Fin (L + 1)) (z : PhaseSpace ι × PhaseSpace ι)
    (selected : Fin (L + 1) × Fin (L + 1)) :
    PhaseSpace ι × PhaseSpace ι :=
  (offsetLeapfrogTrajectory gradient ε origin z.1 selected.1,
    offsetLeapfrogTrajectory gradient ε origin z.2 selected.2)

/-- The `m`-th Euclidean position-distance cost between two selected points
of offset leapfrog trajectories. This lives with the coupled trajectory
construction so both finite transport and kernel-expectation results can use
the same cost definition. -/
noncomputable def trajectoryPositionMomentCost
    (gradient : Position ι → Position ι) (m : ℕ) (ε : ℝ) {L : ℕ}
    (z : PhaseSpace ι × PhaseSpace ι) (origin : Fin (L + 1))
    (i j : Fin (L + 1)) : NNReal :=
  ⟨euclideanNorm
      ((offsetLeapfrogTrajectory gradient ε origin z.1 i).1 -
        (offsetLeapfrogTrajectory gradient ε origin z.2 j).1) ^ m,
    pow_nonneg (euclideanNorm_nonneg _) _⟩

omit [Fintype ι] in
theorem measurable_coupledTrajectoryOutput
    {gradient : Position ι → Position ι} (hgradient : Measurable gradient)
    (ε : ℝ) {L : ℕ} (origin : Fin (L + 1))
    (selected : Fin (L + 1) × Fin (L + 1)) :
    Measurable fun z : PhaseSpace ι × PhaseSpace ι =>
      coupledTrajectoryOutput gradient ε origin z selected := by
  unfold coupledTrajectoryOutput
  exact ((measurable_offsetLeapfrogTrajectory hgradient ε origin selected.1).comp
    measurable_fst).prodMk
      ((measurable_offsetLeapfrogTrajectory hgradient ε origin selected.2).comp
        measurable_snd)

/-- For a fixed shared origin, push a coupled categorical index law forward
to the corresponding pair of phase points. -/
noncomputable def coupledOffsetMultinomialKernel
    (gradient : Position ι → Position ι) (ε : ℝ) (L : ℕ)
    (origin : Fin (L + 1))
    (indexCoupling :
      (PhaseSpace ι × PhaseSpace ι) → Fin (L + 1) →
        PMF (Fin (L + 1) × Fin (L + 1)))
    (hgradient : Measurable gradient)
    (hmeas : ∀ selected, Measurable fun z =>
      indexCoupling z origin selected) :
    Kernel (PhaseSpace ι × PhaseSpace ι) (PhaseSpace ι × PhaseSpace ι) where
  toFun z := ((indexCoupling z origin).map
    (coupledTrajectoryOutput gradient ε origin z)).toMeasure
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp_rw [PMF.toMeasure_map_apply _ _ s (measurable_of_countable _) hs]
    simp_rw [PMF.toMeasure_apply_fintype]
    apply Finset.measurable_sum
    intro selected hselected
    change Measurable fun z =>
      ((coupledTrajectoryOutput gradient ε origin z) ⁻¹' s).indicator
        (indexCoupling z origin) selected
    apply Measurable.indicator
    · exact hmeas selected
    · exact measurable_coupledTrajectoryOutput hgradient ε origin selected hs

instance coupledOffsetMultinomialKernel_isMarkovKernel
    (gradient : Position ι → Position ι) (ε : ℝ) (L : ℕ)
    (origin : Fin (L + 1))
    (indexCoupling :
      (PhaseSpace ι × PhaseSpace ι) → Fin (L + 1) →
        PMF (Fin (L + 1) × Fin (L + 1)))
    (hgradient : Measurable gradient)
    (hmeas : ∀ selected, Measurable fun z =>
      indexCoupling z origin selected) :
    IsMarkovKernel (coupledOffsetMultinomialKernel gradient ε L origin
      indexCoupling hgradient hmeas) where
  isProbabilityMeasure _ := PMF.toMeasure.isProbabilityMeasure _

/-- The expected first-moment position separation under a fixed-origin
coupled trajectory kernel is exactly the finite transport cost of its index
coupling. -/
theorem coupledOffsetMultinomialKernel_lintegral_positionDistance_eq
    (gradient : Position ι → Position ι) (ε : ℝ) (L : ℕ)
    (origin : Fin (L + 1))
    (indexCoupling :
      (PhaseSpace ι × PhaseSpace ι) → Fin (L + 1) →
        PMF (Fin (L + 1) × Fin (L + 1)))
    (hgradient : Measurable gradient)
    (hmeas : ∀ selected, Measurable fun z =>
      indexCoupling z origin selected)
    (z : PhaseSpace ι × PhaseSpace ι) :
    (∫⁻ y, ENNReal.ofReal (euclideanNorm (y.1.1 - y.2.1))
        ∂coupledOffsetMultinomialKernel gradient ε L origin
          indexCoupling hgradient hmeas z) =
      Mcmc.Finite.transportCost
        (trajectoryPositionMomentCost gradient 1 ε z origin)
        (indexCoupling z origin) := by
  change (∫⁻ y, ENNReal.ofReal (euclideanNorm (y.1.1 - y.2.1))
      ∂((indexCoupling z origin).map
        (coupledTrajectoryOutput gradient ε origin z)).toMeasure) = _
  rw [← PMF.toMeasure_map
    (f := coupledTrajectoryOutput gradient ε origin z)
    (indexCoupling z origin) (measurable_of_countable _)]
  have hcost : Measurable fun y : PhaseSpace ι × PhaseSpace ι =>
      ENNReal.ofReal (euclideanNorm (y.1.1 - y.2.1)) := by
    apply ENNReal.measurable_ofReal.comp
    exact continuous_euclideanNorm.measurable.comp
      ((measurable_fst.comp measurable_fst).sub
        (measurable_fst.comp measurable_snd))
  rw [MeasureTheory.lintegral_map hcost (measurable_of_countable _)]
  have hintegrand :
      (fun selected : Fin (L + 1) × Fin (L + 1) =>
        ENNReal.ofReal
          (euclideanNorm
            ((coupledTrajectoryOutput gradient ε origin z selected).1.1 -
              (coupledTrajectoryOutput gradient ε origin z selected).2.1))) =
        fun selected =>
          (trajectoryPositionMomentCost gradient 1 ε z origin
            selected.1 selected.2 : ENNReal) := by
    funext selected
    simp only [coupledTrajectoryOutput]
    rw [ENNReal.coe_nnreal_eq]
    change ENNReal.ofReal _ = ENNReal.ofReal (_ ^ 1)
    rw [pow_one]
  rw [hintegrand,
    Mcmc.Finite.lintegral_toMeasure_eq_transportCost]

/-- General position-moment form of the fixed-origin transport identity. In
particular, exponent two is the kernel-level bridge needed by the paper's
`W₂` trajectory coupling. -/
theorem coupledOffsetMultinomialKernel_lintegral_positionMoment_eq
    (gradient : Position ι → Position ι) (m : ℕ) (ε : ℝ) (L : ℕ)
    (origin : Fin (L + 1))
    (indexCoupling :
      (PhaseSpace ι × PhaseSpace ι) → Fin (L + 1) →
        PMF (Fin (L + 1) × Fin (L + 1)))
    (hgradient : Measurable gradient)
    (hmeas : ∀ selected, Measurable fun z =>
      indexCoupling z origin selected)
    (z : PhaseSpace ι × PhaseSpace ι) :
    (∫⁻ y, ENNReal.ofReal
        (euclideanNorm (y.1.1 - y.2.1) ^ m)
        ∂coupledOffsetMultinomialKernel gradient ε L origin
          indexCoupling hgradient hmeas z) =
      Mcmc.Finite.transportCost
        (trajectoryPositionMomentCost gradient m ε z origin)
        (indexCoupling z origin) := by
  change (∫⁻ y, ENNReal.ofReal
      (euclideanNorm (y.1.1 - y.2.1) ^ m)
      ∂((indexCoupling z origin).map
        (coupledTrajectoryOutput gradient ε origin z)).toMeasure) = _
  rw [← PMF.toMeasure_map
    (f := coupledTrajectoryOutput gradient ε origin z)
    (indexCoupling z origin) (measurable_of_countable _)]
  have hcost : Measurable fun y : PhaseSpace ι × PhaseSpace ι =>
      ENNReal.ofReal (euclideanNorm (y.1.1 - y.2.1) ^ m) := by
    apply ENNReal.measurable_ofReal.comp
    exact (continuous_euclideanNorm.comp
      ((continuous_fst.comp continuous_fst).sub
        (continuous_fst.comp continuous_snd))).pow m |>.measurable
  rw [MeasureTheory.lintegral_map hcost (measurable_of_countable _)]
  have hintegrand :
      (fun selected : Fin (L + 1) × Fin (L + 1) =>
        ENNReal.ofReal
          (euclideanNorm
            ((coupledTrajectoryOutput gradient ε origin z selected).1.1 -
              (coupledTrajectoryOutput gradient ε origin z selected).2.1) ^ m)) =
        fun selected =>
          (trajectoryPositionMomentCost gradient m ε z origin
            selected.1 selected.2 : ENNReal) := by
    funext selected
    simp only [coupledTrajectoryOutput]
    rw [ENNReal.coe_nnreal_eq]
    change ENNReal.ofReal _ = ENNReal.ofReal
      (euclideanNorm
        ((offsetLeapfrogTrajectory gradient ε origin z.1 selected.1).1 -
          (offsetLeapfrogTrajectory gradient ε origin z.2 selected.2).1) ^ m)
    rfl
  rw [hintegrand,
    Mcmc.Finite.lintegral_toMeasure_eq_transportCost]

/-- A correctly coupled categorical index law gives exactly the two fixed-
origin multinomial transition marginals. -/
theorem coupledOffsetMultinomialKernel_isCoupling
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (origin : Fin (L + 1))
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (indexCoupling :
      (PhaseSpace ι × PhaseSpace ι) → Fin (L + 1) →
        PMF (Fin (L + 1) × Fin (L + 1)))
    (hmeas : ∀ selected, Measurable fun z =>
      indexCoupling z origin selected)
    (hcoupling : ∀ z,
      Mcmc.Finite.IsPMFCoupling (indexCoupling z origin)
        (trajectoryIndexPMF potential
          (offsetLeapfrogTrajectory gradient ε origin z.1))
        (trajectoryIndexPMF potential
          (offsetLeapfrogTrajectory gradient ε origin z.2))) :
    Mcmc.Kernel.IsCoupling
      (coupledOffsetMultinomialKernel gradient ε L origin
        indexCoupling hgradient hmeas)
      (offsetMultinomialKernel potential gradient ε L origin
        hpotential hgradient)
      (offsetMultinomialKernel potential gradient ε L origin
        hpotential hgradient) := by
  constructor
  · ext z : 1
    rw [Kernel.comap_apply]
    rw [Kernel.fst_apply]
    change Measure.map Prod.fst
      (((indexCoupling z origin).map
        (coupledTrajectoryOutput gradient ε origin z)).toMeasure) =
      (trajectoryIndexPMF potential
        (offsetLeapfrogTrajectory gradient ε origin z.1)).toMeasure.map
          (offsetLeapfrogTrajectory gradient ε origin z.1)
    rw [PMF.toMeasure_map Prod.fst _ measurable_fst]
    rw [PMF.map_comp]
    have hout : Prod.fst ∘ coupledTrajectoryOutput gradient ε origin z =
        (offsetLeapfrogTrajectory gradient ε origin z.1) ∘ Prod.fst := by
      funext selected
      rfl
    rw [hout, ← PMF.map_comp]
    rw [(hcoupling z).fst]
    rw [PMF.toMeasure_map _ _ (measurable_of_countable _)]
  · ext z : 1
    rw [Kernel.comap_apply]
    rw [Kernel.snd_apply]
    change Measure.map Prod.snd
      (((indexCoupling z origin).map
        (coupledTrajectoryOutput gradient ε origin z)).toMeasure) =
      (trajectoryIndexPMF potential
        (offsetLeapfrogTrajectory gradient ε origin z.2)).toMeasure.map
          (offsetLeapfrogTrajectory gradient ε origin z.2)
    rw [PMF.toMeasure_map Prod.snd _ measurable_snd]
    rw [PMF.map_comp]
    have hout : Prod.snd ∘ coupledTrajectoryOutput gradient ε origin z =
        (offsetLeapfrogTrajectory gradient ε origin z.2) ∘ Prod.snd := by
      funext selected
      rfl
    rw [hout, ← PMF.map_comp]
    rw [(hcoupling z).snd]
    rw [PMF.toMeasure_map _ _ (measurable_of_countable _)]

/-- Average the fixed-origin coupled transitions over one shared uniform
origin. -/
noncomputable def coupledRandomizedMultinomialLeapfrogKernel
    (gradient : Position ι → Position ι) (ε : ℝ) (L : ℕ)
    (indexCoupling :
      (PhaseSpace ι × PhaseSpace ι) → Fin (L + 1) →
        PMF (Fin (L + 1) × Fin (L + 1)))
    (hgradient : Measurable gradient)
    (hmeas : ∀ origin selected, Measurable fun z =>
      indexCoupling z origin selected) :
    Kernel (PhaseSpace ι × PhaseSpace ι) (PhaseSpace ι × PhaseSpace ι) where
  toFun z := ∑ origin : Fin (L + 1),
    PMF.uniformOfFintype (Fin (L + 1)) origin •
      coupledOffsetMultinomialKernel gradient ε L origin indexCoupling
        hgradient (hmeas origin) z
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    apply Finset.measurable_sum
    intro origin horigin
    exact measurable_const.mul
      ((coupledOffsetMultinomialKernel gradient ε L origin indexCoupling
        hgradient (hmeas origin)).measurable_coe hs)

instance coupledRandomizedMultinomialLeapfrogKernel_isMarkovKernel
    (gradient : Position ι → Position ι) (ε : ℝ) (L : ℕ)
    (indexCoupling :
      (PhaseSpace ι × PhaseSpace ι) → Fin (L + 1) →
        PMF (Fin (L + 1) × Fin (L + 1)))
    (hgradient : Measurable gradient)
    (hmeas : ∀ origin selected, Measurable fun z =>
      indexCoupling z origin selected) :
    IsMarkovKernel (coupledRandomizedMultinomialLeapfrogKernel gradient ε L
      indexCoupling hgradient hmeas) where
  isProbabilityMeasure z := by
    constructor
    rw [coupledRandomizedMultinomialLeapfrogKernel]
    change (∑ origin : Fin (L + 1),
      PMF.uniformOfFintype (Fin (L + 1)) origin •
        coupledOffsetMultinomialKernel gradient ε L origin indexCoupling
          hgradient (hmeas origin) z) Set.univ = 1
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
      measure_univ, mul_one]
    exact (tsum_fintype _).symm.trans (PMF.tsum_coe _)

/-- Averaging over the shared uniform trajectory origin averages the finite
first-moment transport costs with the same weights. -/
theorem coupledRandomizedMultinomialLeapfrogKernel_lintegral_positionDistance_eq
    (gradient : Position ι → Position ι) (ε : ℝ) (L : ℕ)
    (indexCoupling :
      (PhaseSpace ι × PhaseSpace ι) → Fin (L + 1) →
        PMF (Fin (L + 1) × Fin (L + 1)))
    (hgradient : Measurable gradient)
    (hmeas : ∀ origin selected, Measurable fun z =>
      indexCoupling z origin selected)
    (z : PhaseSpace ι × PhaseSpace ι) :
    (∫⁻ y, ENNReal.ofReal (euclideanNorm (y.1.1 - y.2.1))
        ∂coupledRandomizedMultinomialLeapfrogKernel gradient ε L
          indexCoupling hgradient hmeas z) =
      ∑ origin : Fin (L + 1),
        PMF.uniformOfFintype (Fin (L + 1)) origin *
          Mcmc.Finite.transportCost
            (trajectoryPositionMomentCost gradient 1 ε z origin)
            (indexCoupling z origin) := by
  change (∫⁻ y, ENNReal.ofReal (euclideanNorm (y.1.1 - y.2.1))
      ∂(∑ origin : Fin (L + 1),
        PMF.uniformOfFintype (Fin (L + 1)) origin •
          coupledOffsetMultinomialKernel gradient ε L origin indexCoupling
            hgradient (hmeas origin) z)) = _
  simp only [MeasureTheory.lintegral_finsetSum_measure,
    MeasureTheory.lintegral_smul_measure, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro origin horigin
  congr 1
  exact coupledOffsetMultinomialKernel_lintegral_positionDistance_eq
    gradient ε L origin indexCoupling hgradient (hmeas origin) z

/-- A transport-cost bound uniform in the randomized trajectory origin gives
the same expected-distance bound for the averaged coupled kernel. -/
theorem coupledRandomizedMultinomialLeapfrogKernel_lintegral_positionDistance_le
    (gradient : Position ι → Position ι) (ε : ℝ) (L : ℕ)
    (indexCoupling :
      (PhaseSpace ι × PhaseSpace ι) → Fin (L + 1) →
        PMF (Fin (L + 1) × Fin (L + 1)))
    (hgradient : Measurable gradient)
    (hmeas : ∀ origin selected, Measurable fun z =>
      indexCoupling z origin selected)
    (z : PhaseSpace ι × PhaseSpace ι) (bound : ENNReal)
    (hbound : ∀ origin,
      Mcmc.Finite.transportCost
          (trajectoryPositionMomentCost gradient 1 ε z origin)
          (indexCoupling z origin) ≤ bound) :
    (∫⁻ y, ENNReal.ofReal (euclideanNorm (y.1.1 - y.2.1))
        ∂coupledRandomizedMultinomialLeapfrogKernel gradient ε L
          indexCoupling hgradient hmeas z) ≤ bound := by
  rw [coupledRandomizedMultinomialLeapfrogKernel_lintegral_positionDistance_eq]
  calc
    (∑ origin : Fin (L + 1),
        PMF.uniformOfFintype (Fin (L + 1)) origin *
          Mcmc.Finite.transportCost
            (trajectoryPositionMomentCost gradient 1 ε z origin)
            (indexCoupling z origin)) ≤
      ∑ origin : Fin (L + 1),
        PMF.uniformOfFintype (Fin (L + 1)) origin * bound := by
      apply Finset.sum_le_sum
      intro origin horigin
      simpa only [mul_comm] using mul_le_mul_right (hbound origin)
        (PMF.uniformOfFintype (Fin (L + 1)) origin)
    _ = (∑ origin : Fin (L + 1),
        PMF.uniformOfFintype (Fin (L + 1)) origin) * bound := by
      rw [Finset.sum_mul]
    _ = bound := by
      have hsum : (∑ origin : Fin (L + 1),
          PMF.uniformOfFintype (Fin (L + 1)) origin) = 1 :=
        (tsum_fintype _).symm.trans (PMF.tsum_coe _)
      rw [hsum]
      exact one_mul bound

/-- Averaging over the shared origin also preserves every finite position
moment transport cost, including the squared cost used by `W₂`. -/
theorem coupledRandomizedMultinomialLeapfrogKernel_lintegral_positionMoment_eq
    (gradient : Position ι → Position ι) (m : ℕ) (ε : ℝ) (L : ℕ)
    (indexCoupling :
      (PhaseSpace ι × PhaseSpace ι) → Fin (L + 1) →
        PMF (Fin (L + 1) × Fin (L + 1)))
    (hgradient : Measurable gradient)
    (hmeas : ∀ origin selected, Measurable fun z =>
      indexCoupling z origin selected)
    (z : PhaseSpace ι × PhaseSpace ι) :
    (∫⁻ y, ENNReal.ofReal
        (euclideanNorm (y.1.1 - y.2.1) ^ m)
        ∂coupledRandomizedMultinomialLeapfrogKernel gradient ε L
          indexCoupling hgradient hmeas z) =
      ∑ origin : Fin (L + 1),
        PMF.uniformOfFintype (Fin (L + 1)) origin *
          Mcmc.Finite.transportCost
            (trajectoryPositionMomentCost gradient m ε z origin)
            (indexCoupling z origin) := by
  change (∫⁻ y, ENNReal.ofReal
      (euclideanNorm (y.1.1 - y.2.1) ^ m)
      ∂(∑ origin : Fin (L + 1),
        PMF.uniformOfFintype (Fin (L + 1)) origin •
          coupledOffsetMultinomialKernel gradient ε L origin indexCoupling
            hgradient (hmeas origin) z)) = _
  simp only [MeasureTheory.lintegral_finsetSum_measure,
    MeasureTheory.lintegral_smul_measure, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro origin horigin
  congr 1
  exact coupledOffsetMultinomialKernel_lintegral_positionMoment_eq
    gradient m ε L origin indexCoupling hgradient (hmeas origin) z

/-- A uniform conditional `m`-th moment transport bound lifts to the actual
randomized-origin coupled trajectory kernel. -/
theorem coupledRandomizedMultinomialLeapfrogKernel_lintegral_positionMoment_le
    (gradient : Position ι → Position ι) (m : ℕ) (ε : ℝ) (L : ℕ)
    (indexCoupling :
      (PhaseSpace ι × PhaseSpace ι) → Fin (L + 1) →
        PMF (Fin (L + 1) × Fin (L + 1)))
    (hgradient : Measurable gradient)
    (hmeas : ∀ origin selected, Measurable fun z =>
      indexCoupling z origin selected)
    (z : PhaseSpace ι × PhaseSpace ι) (bound : ENNReal)
    (hbound : ∀ origin,
      Mcmc.Finite.transportCost
          (trajectoryPositionMomentCost gradient m ε z origin)
          (indexCoupling z origin) ≤ bound) :
    (∫⁻ y, ENNReal.ofReal
        (euclideanNorm (y.1.1 - y.2.1) ^ m)
        ∂coupledRandomizedMultinomialLeapfrogKernel gradient ε L
          indexCoupling hgradient hmeas z) ≤ bound := by
  rw [coupledRandomizedMultinomialLeapfrogKernel_lintegral_positionMoment_eq]
  calc
    (∑ origin : Fin (L + 1),
        PMF.uniformOfFintype (Fin (L + 1)) origin *
          Mcmc.Finite.transportCost
            (trajectoryPositionMomentCost gradient m ε z origin)
            (indexCoupling z origin)) ≤
      ∑ origin : Fin (L + 1),
        PMF.uniformOfFintype (Fin (L + 1)) origin * bound := by
      apply Finset.sum_le_sum
      intro origin horigin
      simpa only [mul_comm] using mul_le_mul_right (hbound origin)
        (PMF.uniformOfFintype (Fin (L + 1)) origin)
    _ = (∑ origin : Fin (L + 1),
        PMF.uniformOfFintype (Fin (L + 1)) origin) * bound := by
      rw [Finset.sum_mul]
    _ = bound := by
      have hsum : (∑ origin : Fin (L + 1),
          PMF.uniformOfFintype (Fin (L + 1)) origin) = 1 :=
        (tsum_fintype _).symm.trans (PMF.tsum_coe _)
      rw [hsum, one_mul]

/-- Phase-pair outputs whose position coordinates are within an explicit
Euclidean radius. -/
def phasePositionRelaxedDiagonal (δ : ℝ) : Set (PhaseSpace ι × PhaseSpace ι) :=
  {z | euclideanNorm (z.1.1 - z.2.1) < δ}

/-- The relaxed position diagonal is measurable. -/
theorem measurableSet_phasePositionRelaxedDiagonal (δ : ℝ) :
    MeasurableSet (phasePositionRelaxedDiagonal (ι := ι) δ) := by
  change MeasurableSet ((fun z : PhaseSpace ι × PhaseSpace ι =>
    euclideanNorm (z.1.1 - z.2.1)) ⁻¹' Set.Iio δ)
  apply MeasurableSet.preimage measurableSet_Iio
  exact continuous_euclideanNorm.measurable.comp
    ((measurable_fst.comp measurable_fst).sub
      (measurable_fst.comp measurable_snd))

/-- Markov's inequality converts a conditional expected Euclidean position
distance bound into a lower bound for entering the relaxed position diagonal. -/
theorem measure_phasePositionRelaxedDiagonal_ge_of_lintegral_le
    (kernel : Kernel (PhaseSpace ι × PhaseSpace ι)
      (PhaseSpace ι × PhaseSpace ι)) [IsMarkovKernel kernel]
    (z : PhaseSpace ι × PhaseSpace ι) {bound : ENNReal}
    (hbound : (∫⁻ y, ENNReal.ofReal (euclideanNorm (y.1.1 - y.2.1))
      ∂kernel z) ≤ bound)
    {δ : ℝ} (hδ : 0 < δ) :
    1 - bound / ENNReal.ofReal δ ≤
      kernel z (phasePositionRelaxedDiagonal δ) := by
  have hd0 : ENNReal.ofReal δ ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hδ
  have hmul : ENNReal.ofReal δ *
      kernel z (phasePositionRelaxedDiagonal δ)ᶜ ≤ bound := by
    calc
      ENNReal.ofReal δ * kernel z (phasePositionRelaxedDiagonal δ)ᶜ =
          ∫⁻ _y in (phasePositionRelaxedDiagonal δ)ᶜ,
            ENNReal.ofReal δ ∂kernel z := by
        rw [setLIntegral_const]
      _ ≤ ∫⁻ y in (phasePositionRelaxedDiagonal δ)ᶜ,
          ENNReal.ofReal (euclideanNorm (y.1.1 - y.2.1)) ∂kernel z := by
        apply setLIntegral_mono'
          (measurableSet_phasePositionRelaxedDiagonal δ).compl
        intro y hy
        exact ENNReal.ofReal_le_ofReal (le_of_not_gt hy)
      _ ≤ ∫⁻ y, ENNReal.ofReal
          (euclideanNorm (y.1.1 - y.2.1)) ∂kernel z :=
        setLIntegral_le_lintegral _ _
      _ ≤ bound := hbound
  have hcomp : kernel z (phasePositionRelaxedDiagonal δ)ᶜ ≤
      bound / ENNReal.ofReal δ := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hd0)
      (Or.inl ENNReal.ofReal_ne_top)]
    simpa only [mul_comm] using hmul
  rw [← compl_compl (phasePositionRelaxedDiagonal δ),
    measure_compl (measurableSet_phasePositionRelaxedDiagonal δ).compl
      (measure_ne_top _ _), measure_univ]
  exact tsub_le_tsub_left hcomp 1

/-- Squared-moment Markov inequality used by the transport/`W₂` route. -/
theorem measure_phasePositionRelaxedDiagonal_ge_of_lintegral_sq_le
    (kernel : Kernel (PhaseSpace ι × PhaseSpace ι)
      (PhaseSpace ι × PhaseSpace ι)) [IsMarkovKernel kernel]
    (z : PhaseSpace ι × PhaseSpace ι) {bound : ENNReal}
    (hbound : (∫⁻ y, ENNReal.ofReal
      (euclideanNorm (y.1.1 - y.2.1) ^ 2) ∂kernel z) ≤ bound)
    {δ : ℝ} (hδ : 0 < δ) :
    1 - bound / ENNReal.ofReal (δ ^ 2) ≤
      kernel z (phasePositionRelaxedDiagonal δ) := by
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hd0 : ENNReal.ofReal (δ ^ 2) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hδsq
  have hmul : ENNReal.ofReal (δ ^ 2) *
      kernel z (phasePositionRelaxedDiagonal δ)ᶜ ≤ bound := by
    calc
      ENNReal.ofReal (δ ^ 2) *
          kernel z (phasePositionRelaxedDiagonal δ)ᶜ =
          ∫⁻ _y in (phasePositionRelaxedDiagonal δ)ᶜ,
            ENNReal.ofReal (δ ^ 2) ∂kernel z := by
        rw [setLIntegral_const]
      _ ≤ ∫⁻ y in (phasePositionRelaxedDiagonal δ)ᶜ,
          ENNReal.ofReal (euclideanNorm (y.1.1 - y.2.1) ^ 2)
            ∂kernel z := by
        apply setLIntegral_mono'
          (measurableSet_phasePositionRelaxedDiagonal δ).compl
        intro y hy
        apply ENNReal.ofReal_le_ofReal
        have hsep : δ ≤ euclideanNorm (y.1.1 - y.2.1) := le_of_not_gt hy
        nlinarith [euclideanNorm_nonneg (y.1.1 - y.2.1)]
      _ ≤ ∫⁻ y, ENNReal.ofReal
          (euclideanNorm (y.1.1 - y.2.1) ^ 2) ∂kernel z :=
        setLIntegral_le_lintegral _ _
      _ ≤ bound := hbound
  have hcomp : kernel z (phasePositionRelaxedDiagonal δ)ᶜ ≤
      bound / ENNReal.ofReal (δ ^ 2) := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hd0)
      (Or.inl ENNReal.ofReal_ne_top)]
    simpa only [mul_comm] using hmul
  rw [← compl_compl (phasePositionRelaxedDiagonal δ),
    measure_compl (measurableSet_phasePositionRelaxedDiagonal δ).compl
      (measure_ne_top _ _), measure_univ]
  exact tsub_le_tsub_left hcomp 1

/-- Sharing the origin and coupling the conditional categorical selections
couples the two randomized multinomial trajectory kernels. -/
theorem coupledRandomizedMultinomialLeapfrogKernel_isCoupling
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ)
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (indexCoupling :
      (PhaseSpace ι × PhaseSpace ι) → Fin (L + 1) →
        PMF (Fin (L + 1) × Fin (L + 1)))
    (hmeas : ∀ origin selected, Measurable fun z =>
      indexCoupling z origin selected)
    (hcoupling : ∀ z origin,
      Mcmc.Finite.IsPMFCoupling (indexCoupling z origin)
        (trajectoryIndexPMF potential
          (offsetLeapfrogTrajectory gradient ε origin z.1))
        (trajectoryIndexPMF potential
          (offsetLeapfrogTrajectory gradient ε origin z.2))) :
    Mcmc.Kernel.IsCoupling
      (coupledRandomizedMultinomialLeapfrogKernel gradient ε L
        indexCoupling hgradient hmeas)
      (randomizedMultinomialLeapfrogKernel potential gradient ε L
        hpotential hgradient)
      (randomizedMultinomialLeapfrogKernel potential gradient ε L
        hpotential hgradient) := by
  constructor
  · ext z s hs
    rw [Kernel.fst_apply' _ _ hs, Kernel.comap_apply]
    change (∑ origin : Fin (L + 1),
      PMF.uniformOfFintype (Fin (L + 1)) origin •
        coupledOffsetMultinomialKernel gradient ε L origin indexCoupling
          hgradient (hmeas origin) z) (Prod.fst ⁻¹' s) =
      (∑ origin : Fin (L + 1),
        PMF.uniformOfFintype (Fin (L + 1)) origin •
          offsetMultinomialKernel potential gradient ε L origin
            hpotential hgradient z.1) s
    simp only [Measure.finsetSum_apply, Measure.smul_apply]
    apply Finset.sum_congr rfl
    intro origin horigin
    congr 1
    have h := (coupledOffsetMultinomialKernel_isCoupling potential gradient ε L
      origin hpotential hgradient indexCoupling (hmeas origin)
      (fun z => hcoupling z origin)).fst_apply z
    calc
      _ = (coupledOffsetMultinomialKernel gradient ε L origin indexCoupling
          hgradient (hmeas origin)).fst z s :=
        (Kernel.fst_apply' _ z hs).symm
      _ = _ := congrArg (fun μ : Measure (PhaseSpace ι) => μ s) h
  · ext z s hs
    rw [Kernel.snd_apply' _ _ hs, Kernel.comap_apply]
    change (∑ origin : Fin (L + 1),
      PMF.uniformOfFintype (Fin (L + 1)) origin •
        coupledOffsetMultinomialKernel gradient ε L origin indexCoupling
          hgradient (hmeas origin) z) (Prod.snd ⁻¹' s) =
      (∑ origin : Fin (L + 1),
        PMF.uniformOfFintype (Fin (L + 1)) origin •
          offsetMultinomialKernel potential gradient ε L origin
            hpotential hgradient z.2) s
    simp only [Measure.finsetSum_apply, Measure.smul_apply]
    apply Finset.sum_congr rfl
    intro origin horigin
    congr 1
    have h := (coupledOffsetMultinomialKernel_isCoupling potential gradient ε L
      origin hpotential hgradient indexCoupling (hmeas origin)
      (fun z => hcoupling z origin)).snd_apply z
    calc
      _ = (coupledOffsetMultinomialKernel gradient ε L origin indexCoupling
          hgradient (hmeas origin)).snd z s :=
        (Kernel.snd_apply' _ z hs).symm
      _ = _ := congrArg (fun μ : Measure (PhaseSpace ι) => μ s) h

/-- Conditionally independent coupling of the two Boltzmann trajectory-index
laws.  This validates the generic lifting interface without imposing the
stronger maximal or transport constructions used later in the paper. -/
noncomputable def independentTrajectoryIndexCoupling
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (z : PhaseSpace ι × PhaseSpace ι)
    (origin : Fin (L + 1)) : PMF (Fin (L + 1) × Fin (L + 1)) :=
  Mcmc.Finite.independentCoupling
    (trajectoryIndexPMF potential
      (offsetLeapfrogTrajectory gradient ε origin z.1))
    (trajectoryIndexPMF potential
      (offsetLeapfrogTrajectory gradient ε origin z.2))

theorem independentTrajectoryIndexCoupling_isCoupling
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (z : PhaseSpace ι × PhaseSpace ι)
    (origin : Fin (L + 1)) :
    Mcmc.Finite.IsPMFCoupling
      (independentTrajectoryIndexCoupling potential gradient ε z origin)
      (trajectoryIndexPMF potential
        (offsetLeapfrogTrajectory gradient ε origin z.1))
      (trajectoryIndexPMF potential
        (offsetLeapfrogTrajectory gradient ε origin z.2)) :=
  Mcmc.Finite.independentCoupling_isCoupling _ _

theorem measurable_independentTrajectoryIndexCoupling_apply
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) {L : ℕ} (origin : Fin (L + 1))
    (selected : Fin (L + 1) × Fin (L + 1)) :
    Measurable fun z : PhaseSpace ι × PhaseSpace ι =>
      independentTrajectoryIndexCoupling potential gradient ε z origin selected := by
  change Measurable fun z : PhaseSpace ι × PhaseSpace ι =>
    Mcmc.Finite.independentCoupling
      (trajectoryIndexPMF potential
        (offsetLeapfrogTrajectory gradient ε origin z.1))
      (trajectoryIndexPMF potential
        (offsetLeapfrogTrajectory gradient ε origin z.2))
      (selected.1, selected.2)
  simp_rw [Mcmc.Finite.independentCoupling_apply]
  exact ((measurable_trajectoryIndexProbability hpotential hgradient ε
    origin selected.1).comp measurable_fst).mul
      ((measurable_trajectoryIndexProbability hpotential hgradient ε
        origin selected.2).comp measurable_snd)

/-- Randomized multinomial trajectory coupling with conditionally independent
categorical selections and a shared uniform origin. -/
noncomputable def independentCoupledRandomizedMultinomialLeapfrogKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    Kernel (PhaseSpace ι × PhaseSpace ι) (PhaseSpace ι × PhaseSpace ι) :=
  coupledRandomizedMultinomialLeapfrogKernel gradient ε L
    (independentTrajectoryIndexCoupling potential gradient ε)
    hgradient
    (fun origin selected =>
      measurable_independentTrajectoryIndexCoupling_apply
        hpotential hgradient ε origin selected)

instance independentCoupledRandomizedMultinomialLeapfrogKernel_isMarkovKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    IsMarkovKernel
      (independentCoupledRandomizedMultinomialLeapfrogKernel potential gradient
        ε L hpotential hgradient) := by
  unfold independentCoupledRandomizedMultinomialLeapfrogKernel
  infer_instance

/-- The independent categorical specialization has the verified randomized
multinomial trajectory kernel on both marginals. -/
theorem independentCoupledRandomizedMultinomialLeapfrogKernel_isCoupling
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    Mcmc.Kernel.IsCoupling
      (independentCoupledRandomizedMultinomialLeapfrogKernel potential gradient
        ε L hpotential hgradient)
      (randomizedMultinomialLeapfrogKernel potential gradient ε L
        hpotential hgradient)
      (randomizedMultinomialLeapfrogKernel potential gradient ε L
        hpotential hgradient) := by
  apply coupledRandomizedMultinomialLeapfrogKernel_isCoupling
  intro z origin
  exact independentTrajectoryIndexCoupling_isCoupling
    potential gradient ε z origin

/-- Compose any coupled momentum refresh with any coupled multinomial
trajectory transition. -/
noncomputable def coupledPhaseMultinomialHMC
    (coupledTrajectory coupledRefresh :
      Kernel (PhaseSpace ι × PhaseSpace ι) (PhaseSpace ι × PhaseSpace ι)) :
    Kernel (PhaseSpace ι × PhaseSpace ι) (PhaseSpace ι × PhaseSpace ι) :=
  coupledTrajectory ∘ₖ coupledRefresh

instance coupledPhaseMultinomialHMC_isMarkovKernel
    (coupledTrajectory coupledRefresh :
      Kernel (PhaseSpace ι × PhaseSpace ι) (PhaseSpace ι × PhaseSpace ι))
    [IsMarkovKernel coupledTrajectory] [IsMarkovKernel coupledRefresh] :
    IsMarkovKernel (coupledPhaseMultinomialHMC coupledTrajectory coupledRefresh) := by
  unfold coupledPhaseMultinomialHMC
  infer_instance

omit [Fintype ι] in
/-- Marginal correctness of the two components implies marginal correctness
of the complete coupled phase-space HMC step. -/
theorem coupledPhaseMultinomialHMC_isCoupling
    (coupledTrajectory coupledRefresh :
      Kernel (PhaseSpace ι × PhaseSpace ι) (PhaseSpace ι × PhaseSpace ι))
    (trajectory refresh : Kernel (PhaseSpace ι) (PhaseSpace ι))
    (hTrajectory : Mcmc.Kernel.IsCoupling
      coupledTrajectory trajectory trajectory)
    (hRefresh : Mcmc.Kernel.IsCoupling
      coupledRefresh refresh refresh) :
    Mcmc.Kernel.IsCoupling
      (coupledPhaseMultinomialHMC coupledTrajectory coupledRefresh)
      (trajectory ∘ₖ refresh) (trajectory ∘ₖ refresh) := by
  exact Mcmc.Kernel.comp_isCoupling coupledRefresh coupledTrajectory
    refresh trajectory refresh trajectory hRefresh hTrajectory

/-- A complete coupled phase-space multinomial HMC transition using
conditionally independent Gaussian refreshes and conditionally independent
categorical selections, while sharing the randomized trajectory origin. -/
noncomputable def independentCoupledPhaseMultinomialHMC
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    Kernel (PhaseSpace ι × PhaseSpace ι) (PhaseSpace ι × PhaseSpace ι) :=
  coupledPhaseMultinomialHMC
    (independentCoupledRandomizedMultinomialLeapfrogKernel potential gradient
      ε L hpotential hgradient)
    (Mcmc.Kernel.independentCoupling
      (momentumRefresh (ι := ι)) momentumRefresh)

instance independentCoupledPhaseMultinomialHMC_isMarkovKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    IsMarkovKernel (independentCoupledPhaseMultinomialHMC potential gradient
      ε L hpotential hgradient) := by
  unfold independentCoupledPhaseMultinomialHMC
  infer_instance

/-- Both marginals of the independent specialization are exactly the verified
standard-Gaussian phase-space multinomial HMC kernel. -/
theorem independentCoupledPhaseMultinomialHMC_isCoupling
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    Mcmc.Kernel.IsCoupling
      (independentCoupledPhaseMultinomialHMC potential gradient ε L
        hpotential hgradient)
      (standardPhaseMultinomialHMC potential gradient ε L
        hpotential hgradient)
      (standardPhaseMultinomialHMC potential gradient ε L
        hpotential hgradient) := by
  unfold independentCoupledPhaseMultinomialHMC standardPhaseMultinomialHMC
    phaseMultinomialHMC
  apply coupledPhaseMultinomialHMC_isCoupling
  · exact independentCoupledRandomizedMultinomialLeapfrogKernel_isCoupling
      potential gradient ε L hpotential hgradient
  · exact Mcmc.Kernel.independentCoupling_isCoupling _ _

/-- Couple position-to-phase momentum augmentation, apply a coupled trajectory
transition, and discard both output momenta. -/
noncomputable def coupledPositionMultinomialHMC
    (coupledTrajectory :
      Kernel (PhaseSpace ι × PhaseSpace ι) (PhaseSpace ι × PhaseSpace ι))
    (coupledLift :
      Kernel (Position ι × Position ι) (PhaseSpace ι × PhaseSpace ι)) :
    Kernel (Position ι × Position ι) (Position ι × Position ι) :=
  (coupledTrajectory ∘ₖ coupledLift).map
    (Prod.map (Prod.fst : PhaseSpace ι → Position ι)
      (Prod.fst : PhaseSpace ι → Position ι))

/-- Position pairs within an explicit coordinate-Euclidean radius. -/
def positionEuclideanRelaxedDiagonal (δ : ℝ) :
    Set (Position ι × Position ι) :=
  {q | euclideanNorm (q.1 - q.2) < δ}

/-- The coordinate-Euclidean relaxed position diagonal is measurable. -/
theorem measurableSet_positionEuclideanRelaxedDiagonal (δ : ℝ) :
    MeasurableSet (positionEuclideanRelaxedDiagonal (ι := ι) δ) := by
  change MeasurableSet ((fun q : Position ι × Position ι =>
    euclideanNorm (q.1 - q.2)) ⁻¹' Set.Iio δ)
  apply MeasurableSet.preimage measurableSet_Iio
  exact continuous_euclideanNorm.measurable.comp
    (measurable_fst.sub measurable_snd)

/-- The full coupled position kernel's relaxed-diagonal probability is the
conditional trajectory probability integrated against its coupled momentum
lift. -/
theorem coupledPositionMultinomialHMC_apply_positionEuclideanRelaxedDiagonal
    (coupledTrajectory :
      Kernel (PhaseSpace ι × PhaseSpace ι) (PhaseSpace ι × PhaseSpace ι))
    (coupledLift :
      Kernel (Position ι × Position ι) (PhaseSpace ι × PhaseSpace ι))
    [IsSFiniteKernel coupledTrajectory] [IsSFiniteKernel coupledLift]
    (q : Position ι × Position ι) (δ : ℝ) :
    coupledPositionMultinomialHMC coupledTrajectory coupledLift q
        (positionEuclideanRelaxedDiagonal δ) =
      ∫⁻ z, coupledTrajectory z (phasePositionRelaxedDiagonal δ) ∂coupledLift q := by
  unfold coupledPositionMultinomialHMC
  rw [Kernel.map_apply'
    (coupledTrajectory ∘ₖ coupledLift)
    (measurable_fst.prodMap measurable_fst) q
    (measurableSet_positionEuclideanRelaxedDiagonal δ)]
  rw [show Prod.map (Prod.fst : PhaseSpace ι → Position ι)
      (Prod.fst : PhaseSpace ι → Position ι) ⁻¹'
        positionEuclideanRelaxedDiagonal δ =
      phasePositionRelaxedDiagonal δ by rfl,
    Kernel.comp_apply' coupledTrajectory coupledLift q
      (measurableSet_phasePositionRelaxedDiagonal δ)]

/-- A conditional relaxed-entry bound on a measurable momentum event lifts
through shared momentum refresh. The full position-kernel entry probability
is at least event mass times the conditional bound. -/
theorem coupledPositionMultinomialHMC_positionRelaxedDiagonal_ge_of_sharedMomentum
    (coupledTrajectory :
      Kernel (PhaseSpace ι × PhaseSpace ι) (PhaseSpace ι × PhaseSpace ι))
    [IsMarkovKernel coupledTrajectory]
    (momentumTarget : Measure (Momentum ι)) [IsProbabilityMeasure momentumTarget]
    (q : Position ι × Position ι) (cutoff : Set (Momentum ι))
    (hcutoff : MeasurableSet cutoff) (δ : ℝ) (c : ENNReal)
    (hconditional : ∀ p ∈ cutoff,
      c ≤ coupledTrajectory ((q.1, p), (q.2, p))
        (phasePositionRelaxedDiagonal δ)) :
    momentumTarget cutoff * c ≤
      coupledPositionMultinomialHMC coupledTrajectory
        (sharedPositionMomentumLift momentumTarget) q
        (positionEuclideanRelaxedDiagonal δ) := by
  rw [coupledPositionMultinomialHMC_apply_positionEuclideanRelaxedDiagonal,
    sharedPositionMomentumLift_apply]
  have hinsert : Measurable fun p : Momentum ι =>
      ((q.1, p), (q.2, p)) := by fun_prop
  have hrow : Measurable fun z : PhaseSpace ι × PhaseSpace ι =>
      coupledTrajectory z (phasePositionRelaxedDiagonal δ) :=
    coupledTrajectory.measurable_coe
      (measurableSet_phasePositionRelaxedDiagonal δ)
  rw [MeasureTheory.lintegral_map hrow hinsert]
  calc
    momentumTarget cutoff * c =
        ∫⁻ _p in cutoff, c ∂momentumTarget := by
      rw [setLIntegral_const]
      exact mul_comm _ _
    _ ≤ ∫⁻ p in cutoff,
        coupledTrajectory ((q.1, p), (q.2, p))
          (phasePositionRelaxedDiagonal δ) ∂momentumTarget := by
      apply setLIntegral_mono' hcutoff
      intro p hp
      exact hconditional p hp
    _ ≤ ∫⁻ p,
        coupledTrajectory ((q.1, p), (q.2, p))
          (phasePositionRelaxedDiagonal δ) ∂momentumTarget :=
      setLIntegral_le_lintegral _ _

instance coupledPositionMultinomialHMC_isMarkovKernel
    (coupledTrajectory :
      Kernel (PhaseSpace ι × PhaseSpace ι) (PhaseSpace ι × PhaseSpace ι))
    (coupledLift :
      Kernel (Position ι × Position ι) (PhaseSpace ι × PhaseSpace ι))
    [IsMarkovKernel coupledTrajectory] [IsMarkovKernel coupledLift] :
    IsMarkovKernel (coupledPositionMultinomialHMC coupledTrajectory coupledLift) := by
  unfold coupledPositionMultinomialHMC
  exact Kernel.IsMarkovKernel.map _ (measurable_fst.prodMap measurable_fst)

omit [Fintype ι] in
/-- A coupled lift and coupled trajectory transition induce a coupled
position-space HMC kernel. -/
theorem coupledPositionMultinomialHMC_isCoupling
    (coupledTrajectory :
      Kernel (PhaseSpace ι × PhaseSpace ι) (PhaseSpace ι × PhaseSpace ι))
    (coupledLift :
      Kernel (Position ι × Position ι) (PhaseSpace ι × PhaseSpace ι))
    (trajectory : Kernel (PhaseSpace ι) (PhaseSpace ι))
    (lift : Kernel (Position ι) (PhaseSpace ι))
    (hTrajectory : Mcmc.Kernel.IsCoupling
      coupledTrajectory trajectory trajectory)
    (hLift : Mcmc.Kernel.IsCoupling coupledLift lift lift) :
    Mcmc.Kernel.IsCoupling
      (coupledPositionMultinomialHMC coupledTrajectory coupledLift)
      ((trajectory ∘ₖ lift).map Prod.fst)
      ((trajectory ∘ₖ lift).map Prod.fst) := by
  unfold coupledPositionMultinomialHMC
  exact Mcmc.Kernel.map_isCoupling _ _ _
    (Mcmc.Kernel.comp_isCoupling coupledLift coupledTrajectory
      lift trajectory lift trajectory hLift hTrajectory)
    Prod.fst Prod.fst measurable_fst measurable_fst

/-- Complete position-space multinomial HMC coupling with independent Gaussian
momenta and independent conditional index selections. -/
noncomputable def independentCoupledPositionMultinomialHMC
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    Kernel (Position ι × Position ι) (Position ι × Position ι) :=
  coupledPositionMultinomialHMC
    (independentCoupledRandomizedMultinomialLeapfrogKernel potential gradient
      ε L hpotential hgradient)
    (Mcmc.Kernel.independentCoupling
      (positionMomentumLift (standardMomentumMeasure (ι := ι)))
      (positionMomentumLift standardMomentumMeasure))

instance independentCoupledPositionMultinomialHMC_isMarkovKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    IsMarkovKernel (independentCoupledPositionMultinomialHMC potential gradient
      ε L hpotential hgradient) := by
  unfold independentCoupledPositionMultinomialHMC
  infer_instance

/-- The complete position-pair transition has the verified standard
position-space HMC kernel on both marginals. -/
theorem independentCoupledPositionMultinomialHMC_isCoupling
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    Mcmc.Kernel.IsCoupling
      (independentCoupledPositionMultinomialHMC potential gradient ε L
        hpotential hgradient)
      (standardPositionMultinomialHMC potential gradient ε L
        hpotential hgradient)
      (standardPositionMultinomialHMC potential gradient ε L
        hpotential hgradient) := by
  unfold independentCoupledPositionMultinomialHMC
    standardPositionMultinomialHMC positionMultinomialHMC
  apply coupledPositionMultinomialHMC_isCoupling
  · exact independentCoupledRandomizedMultinomialLeapfrogKernel_isCoupling
      potential gradient ε L hpotential hgradient
  · exact Mcmc.Kernel.independentCoupling_isCoupling _ _

/-- Complete position-space multinomial HMC coupling using one shared standard
Gaussian momentum and conditionally independent categorical selections. -/
noncomputable def sharedMomentumCoupledPositionMultinomialHMC
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    Kernel (Position ι × Position ι) (Position ι × Position ι) :=
  coupledPositionMultinomialHMC
    (independentCoupledRandomizedMultinomialLeapfrogKernel potential gradient
      ε L hpotential hgradient)
    (sharedPositionMomentumLift (standardMomentumMeasure (ι := ι)))

instance sharedMomentumCoupledPositionMultinomialHMC_isMarkovKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    IsMarkovKernel (sharedMomentumCoupledPositionMultinomialHMC potential gradient
      ε L hpotential hgradient) := by
  unfold sharedMomentumCoupledPositionMultinomialHMC
  infer_instance

/-- The shared-momentum position-pair transition still has the verified
standard HMC kernel on both marginals. -/
theorem sharedMomentumCoupledPositionMultinomialHMC_isCoupling
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    Mcmc.Kernel.IsCoupling
      (sharedMomentumCoupledPositionMultinomialHMC potential gradient ε L
        hpotential hgradient)
      (standardPositionMultinomialHMC potential gradient ε L
        hpotential hgradient)
      (standardPositionMultinomialHMC potential gradient ε L
        hpotential hgradient) := by
  unfold sharedMomentumCoupledPositionMultinomialHMC
    standardPositionMultinomialHMC positionMultinomialHMC
  apply coupledPositionMultinomialHMC_isCoupling
  · exact independentCoupledRandomizedMultinomialLeapfrogKernel_isCoupling
      potential gradient ε L hpotential hgradient
  · exact sharedPositionMomentumLift_isCoupling standardMomentumMeasure

/-- Maximal coupling of the two conditional Boltzmann trajectory-index laws. -/
noncomputable def maximalTrajectoryIndexCoupling
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (z : PhaseSpace ι × PhaseSpace ι)
    (origin : Fin (L + 1)) : PMF (Fin (L + 1) × Fin (L + 1)) :=
  Mcmc.Finite.maximalCoupling
    (trajectoryIndexPMF potential
      (offsetLeapfrogTrajectory gradient ε origin z.1))
    (trajectoryIndexPMF potential
      (offsetLeapfrogTrajectory gradient ε origin z.2))

theorem maximalTrajectoryIndexCoupling_isMaximal
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (z : PhaseSpace ι × PhaseSpace ι)
    (origin : Fin (L + 1)) :
    Mcmc.Finite.IsMaximalCoupling
      (maximalTrajectoryIndexCoupling potential gradient ε z origin)
      (trajectoryIndexPMF potential
        (offsetLeapfrogTrajectory gradient ε origin z.1))
      (trajectoryIndexPMF potential
        (offsetLeapfrogTrajectory gradient ε origin z.2)) :=
  Mcmc.Finite.maximalCoupling_isMaximal _ _

/-- Algorithm 5 applied to an arbitrary approximate joint trajectory-index
law. The maximal admissible portion of the candidate is retained and the
remaining mass is repaired independently. -/
noncomputable def repairedTrajectoryIndexCoupling
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (z : PhaseSpace ι × PhaseSpace ι)
    (origin : Fin (L + 1))
    (candidate : PMF (Fin (L + 1) × Fin (L + 1))) :
    PMF (Fin (L + 1) × Fin (L + 1)) :=
  Mcmc.Finite.maximallyMarginalRepairedCoupling candidate
    (trajectoryIndexPMF potential
      (offsetLeapfrogTrajectory gradient ε origin z.1))
    (trajectoryIndexPMF potential
      (offsetLeapfrogTrajectory gradient ε origin z.2))

/-- The debiased trajectory-index law has the exact Boltzmann marginals
required by the coupled multinomial-HMC lift. -/
theorem repairedTrajectoryIndexCoupling_isCoupling
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (z : PhaseSpace ι × PhaseSpace ι)
    (origin : Fin (L + 1))
    (candidate : PMF (Fin (L + 1) × Fin (L + 1))) :
    Mcmc.Finite.IsPMFCoupling
      (repairedTrajectoryIndexCoupling potential gradient ε z origin candidate)
      (trajectoryIndexPMF potential
        (offsetLeapfrogTrajectory gradient ε origin z.1))
      (trajectoryIndexPMF potential
        (offsetLeapfrogTrajectory gradient ε origin z.2)) :=
  Mcmc.Finite.maximallyMarginalRepairedCoupling_isCoupling _ _ _

/-- If the approximate solver already returned a proper coupling, Algorithm 5
retains it with coefficient one. -/
theorem repairedTrajectoryIndexCoupling_eq_of_isCoupling
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (z : PhaseSpace ι × PhaseSpace ι)
    (origin : Fin (L + 1))
    {candidate : PMF (Fin (L + 1) × Fin (L + 1))}
    (hcandidate : Mcmc.Finite.IsPMFCoupling candidate
      (trajectoryIndexPMF potential
        (offsetLeapfrogTrajectory gradient ε origin z.1))
      (trajectoryIndexPMF potential
        (offsetLeapfrogTrajectory gradient ε origin z.2))) :
    repairedTrajectoryIndexCoupling potential gradient ε z origin candidate =
      candidate :=
  Mcmc.Finite.maximallyMarginalRepairedCoupling_eq_of_isCoupling hcandidate

/-- The joint law of the two selected trajectory indices after sampling the
shared trajectory origin uniformly and then using the specified conditional
index coupling.  This is the latent categorical experiment implemented by
`coupledRandomizedMultinomialLeapfrogKernel`, with the origin marginalized
out. -/
noncomputable def randomizedTrajectoryIndexCoupling
    {L : ℕ}
    (indexCoupling : Fin (L + 1) →
      PMF (Fin (L + 1) × Fin (L + 1))) :
    PMF (Fin (L + 1) × Fin (L + 1)) :=
  (PMF.uniformOfFintype (Fin (L + 1))).bind indexCoupling

/-- The unequal-index probability of randomized trajectory selection is the
uniform-origin average of its conditional unequal-index probabilities. -/
theorem randomizedTrajectoryIndexCoupling_mismatchMass
    {L : ℕ}
    (indexCoupling : Fin (L + 1) →
      PMF (Fin (L + 1) × Fin (L + 1))) :
    Mcmc.Finite.mismatchMass
        (randomizedTrajectoryIndexCoupling indexCoupling) =
      ∑ origin : Fin (L + 1),
        PMF.uniformOfFintype (Fin (L + 1)) origin *
          Mcmc.Finite.mismatchMass (indexCoupling origin) := by
  exact Mcmc.Finite.mismatchMass_bind _ _

/-- Squared Euclidean distance between the positions at two selected
trajectory indices.  This is the `W₂` cost matrix used in equation (9) of Xu
et al. -/
noncomputable def trajectorySquaredPositionCost
    (gradient : Position ι → Position ι) (ε : ℝ) {L : ℕ}
    (z : PhaseSpace ι × PhaseSpace ι) (origin : Fin (L + 1))
    (i j : Fin (L + 1)) : NNReal :=
  ⟨squaredEuclideanNorm
      ((offsetLeapfrogTrajectory gradient ε origin z.1 i).1 -
        (offsetLeapfrogTrajectory gradient ε origin z.2 j).1),
    squaredEuclideanNorm_nonneg _⟩

/-- If both trajectories remain in the Euclidean ball of radius `R`, every
cross-index squared-position cost is at most `4 R²`. -/
theorem trajectorySquaredPositionCost_le_of_positionNorm_le
    (gradient : Position ι → Position ι) (ε : ℝ) {L : ℕ}
    (z : PhaseSpace ι × PhaseSpace ι) (origin : Fin (L + 1))
    {R : ℝ} (hR : 0 ≤ R)
    (hleft : ∀ i,
      euclideanNorm
        (offsetLeapfrogTrajectory gradient ε origin z.1 i).1 ≤ R)
    (hright : ∀ j,
      euclideanNorm
        (offsetLeapfrogTrajectory gradient ε origin z.2 j).1 ≤ R)
    (i j : Fin (L + 1)) :
    trajectorySquaredPositionCost gradient ε z origin i j ≤
      ⟨4 * R ^ 2, by positivity⟩ := by
  change squaredEuclideanNorm
      ((offsetLeapfrogTrajectory gradient ε origin z.1 i).1 -
        (offsetLeapfrogTrajectory gradient ε origin z.2 j).1) ≤ 4 * R ^ 2
  rw [← euclideanNorm_sq]
  have htriangle := euclideanNorm_sub_le
    (offsetLeapfrogTrajectory gradient ε origin z.1 i).1
    (offsetLeapfrogTrajectory gradient ε origin z.2 j).1
  have hnorm : euclideanNorm
      ((offsetLeapfrogTrajectory gradient ε origin z.1 i).1 -
        (offsetLeapfrogTrajectory gradient ε origin z.2 j).1) ≤ 2 * R := by
    linarith [hleft i, hright j]
  have hnonneg := euclideanNorm_nonneg
    ((offsetLeapfrogTrajectory gradient ε origin z.1 i).1 -
      (offsetLeapfrogTrajectory gradient ε origin z.2 j).1)
  nlinarith

/-- A pointwise optimal-transport coupling of the two conditional trajectory
index laws for squared position distance. -/
noncomputable def transportTrajectoryIndexCoupling
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (z : PhaseSpace ι × PhaseSpace ι)
    (origin : Fin (L + 1)) : PMF (Fin (L + 1) × Fin (L + 1)) :=
  Mcmc.Finite.optimalTransportCoupling
    (trajectoryIndexPMF potential
      (offsetLeapfrogTrajectory gradient ε origin z.1))
    (trajectoryIndexPMF potential
      (offsetLeapfrogTrajectory gradient ε origin z.2))
    (trajectorySquaredPositionCost gradient ε z origin)

/-- The pointwise transport optimizer has exactly the two required
trajectory-index marginals. -/
theorem transportTrajectoryIndexCoupling_isCoupling
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (z : PhaseSpace ι × PhaseSpace ι)
    (origin : Fin (L + 1)) :
    Mcmc.Finite.IsPMFCoupling
      (transportTrajectoryIndexCoupling potential gradient ε z origin)
      (trajectoryIndexPMF potential
        (offsetLeapfrogTrajectory gradient ε origin z.1))
      (trajectoryIndexPMF potential
        (offsetLeapfrogTrajectory gradient ε origin z.2)) :=
  Mcmc.Finite.optimalTransportCoupling_isCoupling _ _ _

/-- The selected trajectory-index coupling minimizes expected squared
position distance among all couplings of the same two conditional laws. -/
theorem transportTrajectoryIndexCoupling_minimal
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (z : PhaseSpace ι × PhaseSpace ι)
    (origin : Fin (L + 1)) (joint : PMF (Fin (L + 1) × Fin (L + 1)))
    (hjoint : Mcmc.Finite.IsPMFCoupling joint
      (trajectoryIndexPMF potential
        (offsetLeapfrogTrajectory gradient ε origin z.1))
      (trajectoryIndexPMF potential
        (offsetLeapfrogTrajectory gradient ε origin z.2))) :
    Mcmc.Finite.transportCost
        (trajectorySquaredPositionCost gradient ε z origin)
        (transportTrajectoryIndexCoupling potential gradient ε z origin) ≤
      Mcmc.Finite.transportCost
        (trajectorySquaredPositionCost gradient ε z origin) joint :=
  Mcmc.Finite.optimalTransportCoupling_minimal _ _ _ joint hjoint

/-- In particular, the squared-position cost of the transport coupling is no
greater than that of the maximal trajectory-index coupling. -/
theorem transportTrajectoryIndexCoupling_cost_le_maximal
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (z : PhaseSpace ι × PhaseSpace ι)
    (origin : Fin (L + 1)) :
    Mcmc.Finite.transportCost
        (trajectorySquaredPositionCost gradient ε z origin)
        (transportTrajectoryIndexCoupling potential gradient ε z origin) ≤
      Mcmc.Finite.transportCost
        (trajectorySquaredPositionCost gradient ε z origin)
        (maximalTrajectoryIndexCoupling potential gradient ε z origin) :=
  transportTrajectoryIndexCoupling_minimal potential gradient ε z origin _
    (maximalTrajectoryIndexCoupling_isMaximal potential gradient ε z origin).1

/-- Refined maximal-trajectory cost decomposition retaining the full
overlap-weighted aligned cost at each index. This avoids losing contraction by
replacing all aligned costs with their maximum. -/
theorem maximalTrajectoryIndexCoupling_cost_le_weightedDiagonal_add_tv
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (z : PhaseSpace ι × PhaseSpace ι)
    (origin : Fin (L + 1)) (mismatchBound : NNReal)
    (hmismatch : ∀ i j, i ≠ j →
      trajectorySquaredPositionCost gradient ε z origin i j ≤ mismatchBound) :
    Mcmc.Finite.transportCost
        (trajectorySquaredPositionCost gradient ε z origin)
        (maximalTrajectoryIndexCoupling potential gradient ε z origin) ≤
      (∑ i, min
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.1) i)
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.2) i) *
          (trajectorySquaredPositionCost gradient ε z origin i i : ENNReal)) +
        Mcmc.Finite.totalVariation
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.1))
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.2)) *
          (mismatchBound : ENNReal) := by
  unfold maximalTrajectoryIndexCoupling
  exact Mcmc.Finite.maximalCoupling_transportCost_le_diagonal_add_totalVariation_mul
    _ _ _ mismatchBound hmismatch

/-- The optimal-transport trajectory coupling inherits the refined weighted
diagonal bound from the maximal coupling. -/
theorem transportTrajectoryIndexCoupling_cost_le_weightedDiagonal_add_tv
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (z : PhaseSpace ι × PhaseSpace ι)
    (origin : Fin (L + 1)) (mismatchBound : NNReal)
    (hmismatch : ∀ i j, i ≠ j →
      trajectorySquaredPositionCost gradient ε z origin i j ≤ mismatchBound) :
    Mcmc.Finite.transportCost
        (trajectorySquaredPositionCost gradient ε z origin)
        (transportTrajectoryIndexCoupling potential gradient ε z origin) ≤
      (∑ i, min
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.1) i)
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.2) i) *
          (trajectorySquaredPositionCost gradient ε z origin i i : ENNReal)) +
        Mcmc.Finite.totalVariation
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.1))
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.2)) *
          (mismatchBound : ENNReal) := by
  apply le_trans
    (transportTrajectoryIndexCoupling_cost_le_maximal
      potential gradient ε z origin)
  exact maximalTrajectoryIndexCoupling_cost_le_weightedDiagonal_add_tv
    potential gradient ε z origin mismatchBound hmismatch

/-- Expected squared position cost under maximal trajectory-index coupling is
the aligned-index cost bound plus total variation times an off-diagonal bound.
This is the finite coupling decomposition in Lemma 4.3. -/
theorem maximalTrajectoryIndexCoupling_cost_le_add_totalVariation_mul
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (z : PhaseSpace ι × PhaseSpace ι)
    (origin : Fin (L + 1)) (diagonalBound mismatchBound : NNReal)
    (hdiagonal : ∀ i,
      trajectorySquaredPositionCost gradient ε z origin i i ≤ diagonalBound)
    (hmismatch : ∀ i j, i ≠ j →
      trajectorySquaredPositionCost gradient ε z origin i j ≤ mismatchBound) :
    Mcmc.Finite.transportCost
        (trajectorySquaredPositionCost gradient ε z origin)
        (maximalTrajectoryIndexCoupling potential gradient ε z origin) ≤
      (diagonalBound : ENNReal) +
        Mcmc.Finite.totalVariation
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.1))
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.2)) *
          (mismatchBound : ENNReal) := by
  exact (maximalTrajectoryIndexCoupling_isMaximal
    potential gradient ε z origin).transportCost_le_add_totalVariation_mul
      _ diagonalBound mismatchBound hdiagonal hmismatch

/-- The transport trajectory coupling inherits the same aligned-plus-TV cost
bound because its expected squared position cost is no larger than that of
the maximal coupling. This is the finite optimization step in Lemma 4.4. -/
theorem transportTrajectoryIndexCoupling_cost_le_add_totalVariation_mul
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (z : PhaseSpace ι × PhaseSpace ι)
    (origin : Fin (L + 1)) (diagonalBound mismatchBound : NNReal)
    (hdiagonal : ∀ i,
      trajectorySquaredPositionCost gradient ε z origin i i ≤ diagonalBound)
    (hmismatch : ∀ i j, i ≠ j →
      trajectorySquaredPositionCost gradient ε z origin i j ≤ mismatchBound) :
    Mcmc.Finite.transportCost
        (trajectorySquaredPositionCost gradient ε z origin)
        (transportTrajectoryIndexCoupling potential gradient ε z origin) ≤
      (diagonalBound : ENNReal) +
        Mcmc.Finite.totalVariation
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.1))
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.2)) *
          (mismatchBound : ENNReal) := by
  apply le_trans
    (transportTrajectoryIndexCoupling_cost_le_maximal
      potential gradient ε z origin)
  exact maximalTrajectoryIndexCoupling_cost_le_add_totalVariation_mul
    potential gradient ε z origin diagonalBound mismatchBound
      hdiagonal hmismatch

/-- Concrete maximal-coupling bound when both trajectories lie in a common
Euclidean ball. Only the aligned-index contraction bound remains abstract. -/
theorem maximalTrajectoryIndexCoupling_cost_le_of_positionNorm_le
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (z : PhaseSpace ι × PhaseSpace ι)
    (origin : Fin (L + 1)) (diagonalBound : NNReal)
    {R : ℝ} (hR : 0 ≤ R)
    (hleft : ∀ i,
      euclideanNorm
        (offsetLeapfrogTrajectory gradient ε origin z.1 i).1 ≤ R)
    (hright : ∀ j,
      euclideanNorm
        (offsetLeapfrogTrajectory gradient ε origin z.2 j).1 ≤ R)
    (hdiagonal : ∀ i,
      trajectorySquaredPositionCost gradient ε z origin i i ≤ diagonalBound) :
    Mcmc.Finite.transportCost
        (trajectorySquaredPositionCost gradient ε z origin)
        (maximalTrajectoryIndexCoupling potential gradient ε z origin) ≤
      (diagonalBound : ENNReal) +
        Mcmc.Finite.totalVariation
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.1))
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.2)) *
          ENNReal.ofNNReal (⟨4 * R ^ 2, by positivity⟩ : NNReal) := by
  apply maximalTrajectoryIndexCoupling_cost_le_add_totalVariation_mul
    potential gradient ε z origin diagonalBound
      ⟨4 * R ^ 2, by positivity⟩ hdiagonal
  intro i j hij
  exact trajectorySquaredPositionCost_le_of_positionNorm_le
    gradient ε z origin hR hleft hright i j

/-- The optimal-transport trajectory coupling satisfies the same common-ball
bound as the maximal coupling. -/
theorem transportTrajectoryIndexCoupling_cost_le_of_positionNorm_le
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (z : PhaseSpace ι × PhaseSpace ι)
    (origin : Fin (L + 1)) (diagonalBound : NNReal)
    {R : ℝ} (hR : 0 ≤ R)
    (hleft : ∀ i,
      euclideanNorm
        (offsetLeapfrogTrajectory gradient ε origin z.1 i).1 ≤ R)
    (hright : ∀ j,
      euclideanNorm
        (offsetLeapfrogTrajectory gradient ε origin z.2 j).1 ≤ R)
    (hdiagonal : ∀ i,
      trajectorySquaredPositionCost gradient ε z origin i i ≤ diagonalBound) :
    Mcmc.Finite.transportCost
        (trajectorySquaredPositionCost gradient ε z origin)
        (transportTrajectoryIndexCoupling potential gradient ε z origin) ≤
      (diagonalBound : ENNReal) +
        Mcmc.Finite.totalVariation
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.1))
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.2)) *
          ENNReal.ofNNReal (⟨4 * R ^ 2, by positivity⟩ : NNReal) := by
  apply le_trans
    (transportTrajectoryIndexCoupling_cost_le_maximal
      potential gradient ε z origin)
  exact maximalTrajectoryIndexCoupling_cost_le_of_positionNorm_le
    potential gradient ε z origin diagonalBound hR hleft hright hdiagonal

/-- If the aligned and TV-mismatch terms fit inside a prescribed contraction
budget, the maximal trajectory coupling satisfies that budget. -/
theorem maximalTrajectoryIndexCoupling_cost_le_of_contractionBudget
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (z : PhaseSpace ι × PhaseSpace ι)
    (origin : Fin (L + 1)) (diagonalBound : NNReal)
    {R : ℝ} (hR : 0 ≤ R)
    (hleft : ∀ i,
      euclideanNorm
        (offsetLeapfrogTrajectory gradient ε origin z.1 i).1 ≤ R)
    (hright : ∀ j,
      euclideanNorm
        (offsetLeapfrogTrajectory gradient ε origin z.2 j).1 ≤ R)
    (hdiagonal : ∀ i,
      trajectorySquaredPositionCost gradient ε z origin i i ≤ diagonalBound)
    (contractionBudget : ENNReal)
    (hbudget : (diagonalBound : ENNReal) +
      Mcmc.Finite.totalVariation
        (trajectoryIndexPMF potential
          (offsetLeapfrogTrajectory gradient ε origin z.1))
        (trajectoryIndexPMF potential
          (offsetLeapfrogTrajectory gradient ε origin z.2)) *
        ENNReal.ofNNReal (⟨4 * R ^ 2, by positivity⟩ : NNReal) ≤
      contractionBudget) :
    Mcmc.Finite.transportCost
        (trajectorySquaredPositionCost gradient ε z origin)
        (maximalTrajectoryIndexCoupling potential gradient ε z origin) ≤
      contractionBudget := by
  exact (maximalTrajectoryIndexCoupling_cost_le_of_positionNorm_le
    potential gradient ε z origin diagonalBound hR hleft hright hdiagonal).trans
      hbudget

/-- The optimal-transport trajectory coupling inherits any contraction budget
proved for the maximal coupling. -/
theorem transportTrajectoryIndexCoupling_cost_le_of_contractionBudget
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (z : PhaseSpace ι × PhaseSpace ι)
    (origin : Fin (L + 1)) (diagonalBound : NNReal)
    {R : ℝ} (hR : 0 ≤ R)
    (hleft : ∀ i,
      euclideanNorm
        (offsetLeapfrogTrajectory gradient ε origin z.1 i).1 ≤ R)
    (hright : ∀ j,
      euclideanNorm
        (offsetLeapfrogTrajectory gradient ε origin z.2 j).1 ≤ R)
    (hdiagonal : ∀ i,
      trajectorySquaredPositionCost gradient ε z origin i i ≤ diagonalBound)
    (contractionBudget : ENNReal)
    (hbudget : (diagonalBound : ENNReal) +
      Mcmc.Finite.totalVariation
        (trajectoryIndexPMF potential
          (offsetLeapfrogTrajectory gradient ε origin z.1))
        (trajectoryIndexPMF potential
          (offsetLeapfrogTrajectory gradient ε origin z.2)) *
        ENNReal.ofNNReal (⟨4 * R ^ 2, by positivity⟩ : NNReal) ≤
      contractionBudget) :
    Mcmc.Finite.transportCost
        (trajectorySquaredPositionCost gradient ε z origin)
        (transportTrajectoryIndexCoupling potential gradient ε z origin) ≤
      contractionBudget := by
  apply le_trans
    (transportTrajectoryIndexCoupling_cost_le_maximal
      potential gradient ε z origin)
  exact maximalTrajectoryIndexCoupling_cost_le_of_contractionBudget
    potential gradient ε z origin diagonalBound hR hleft hright hdiagonal
      contractionBudget hbudget

/-- Randomized multinomial trajectory transition using the pointwise optimal
transport coupling.  The explicit atom-measurability hypothesis is the exact
extra obligation needed to turn the classically selected finite optimizer
into a Markov kernel. -/
noncomputable def transportCoupledRandomizedMultinomialLeapfrogKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hgradient : Measurable gradient)
    (hmeas : ∀ (origin : Fin (L + 1))
      (selected : Fin (L + 1) × Fin (L + 1)),
      Measurable fun z : PhaseSpace ι × PhaseSpace ι =>
      transportTrajectoryIndexCoupling potential gradient ε z origin selected) :
    Kernel (PhaseSpace ι × PhaseSpace ι) (PhaseSpace ι × PhaseSpace ι) :=
  coupledRandomizedMultinomialLeapfrogKernel gradient ε L
    (transportTrajectoryIndexCoupling potential gradient ε) hgradient hmeas

instance transportCoupledRandomizedMultinomialLeapfrogKernel_isMarkovKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hgradient : Measurable gradient)
    (hmeas : ∀ (origin : Fin (L + 1))
      (selected : Fin (L + 1) × Fin (L + 1)),
      Measurable fun z : PhaseSpace ι × PhaseSpace ι =>
      transportTrajectoryIndexCoupling potential gradient ε z origin selected) :
    IsMarkovKernel
      (transportCoupledRandomizedMultinomialLeapfrogKernel potential gradient ε
        L hgradient hmeas) := by
  unfold transportCoupledRandomizedMultinomialLeapfrogKernel
  infer_instance

/-- Under atom measurability, the transport trajectory kernel has exactly the
verified randomized multinomial trajectory kernel on both marginals. -/
theorem transportCoupledRandomizedMultinomialLeapfrogKernel_isCoupling
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient)
    (hmeas : ∀ (origin : Fin (L + 1))
      (selected : Fin (L + 1) × Fin (L + 1)),
      Measurable fun z : PhaseSpace ι × PhaseSpace ι =>
      transportTrajectoryIndexCoupling potential gradient ε z origin selected) :
    Mcmc.Kernel.IsCoupling
      (transportCoupledRandomizedMultinomialLeapfrogKernel potential gradient ε
        L hgradient hmeas)
      (randomizedMultinomialLeapfrogKernel potential gradient ε L
        hpotential hgradient)
      (randomizedMultinomialLeapfrogKernel potential gradient ε L
        hpotential hgradient) := by
  apply coupledRandomizedMultinomialLeapfrogKernel_isCoupling
  exact fun z origin =>
    transportTrajectoryIndexCoupling_isCoupling potential gradient ε z origin

/-- Paper-style position HMC using shared standard Gaussian momentum and the
pointwise optimal squared-position trajectory-index coupling. -/
noncomputable def transportSharedMomentumCoupledPositionMultinomialHMC
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hgradient : Measurable gradient)
    (hmeas : ∀ (origin : Fin (L + 1))
      (selected : Fin (L + 1) × Fin (L + 1)),
      Measurable fun z : PhaseSpace ι × PhaseSpace ι =>
      transportTrajectoryIndexCoupling potential gradient ε z origin selected) :
    Kernel (Position ι × Position ι) (Position ι × Position ι) :=
  coupledPositionMultinomialHMC
    (transportCoupledRandomizedMultinomialLeapfrogKernel potential gradient ε L
      hgradient hmeas)
    (sharedPositionMomentumLift (standardMomentumMeasure (ι := ι)))

instance transportSharedMomentumCoupledPositionMultinomialHMC_isMarkovKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hgradient : Measurable gradient)
    (hmeas : ∀ (origin : Fin (L + 1))
      (selected : Fin (L + 1) × Fin (L + 1)),
      Measurable fun z : PhaseSpace ι × PhaseSpace ι =>
      transportTrajectoryIndexCoupling potential gradient ε z origin selected) :
    IsMarkovKernel
      (transportSharedMomentumCoupledPositionMultinomialHMC potential gradient ε
        L hgradient hmeas) := by
  unfold transportSharedMomentumCoupledPositionMultinomialHMC
  infer_instance

/-- Both marginals of the transport/shared-momentum HMC kernel are exactly the
verified standard position-space multinomial HMC kernel. -/
theorem transportSharedMomentumCoupledPositionMultinomialHMC_isCoupling
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient)
    (hmeas : ∀ (origin : Fin (L + 1))
      (selected : Fin (L + 1) × Fin (L + 1)),
      Measurable fun z : PhaseSpace ι × PhaseSpace ι =>
      transportTrajectoryIndexCoupling potential gradient ε z origin selected) :
    Mcmc.Kernel.IsCoupling
      (transportSharedMomentumCoupledPositionMultinomialHMC potential gradient ε
        L hgradient hmeas)
      (standardPositionMultinomialHMC potential gradient ε L
        hpotential hgradient)
      (standardPositionMultinomialHMC potential gradient ε L
        hpotential hgradient) := by
  unfold transportSharedMomentumCoupledPositionMultinomialHMC
    standardPositionMultinomialHMC positionMultinomialHMC
  apply coupledPositionMultinomialHMC_isCoupling
  · exact transportCoupledRandomizedMultinomialLeapfrogKernel_isCoupling
      potential gradient ε L hpotential hgradient hmeas
  · exact sharedPositionMomentumLift_isCoupling standardMomentumMeasure

theorem measurable_maximalTrajectoryIndexCoupling_apply
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) {L : ℕ} (origin : Fin (L + 1))
    (selected : Fin (L + 1) × Fin (L + 1)) :
    Measurable fun z : PhaseSpace ι × PhaseSpace ι =>
      maximalTrajectoryIndexCoupling potential gradient ε z origin selected := by
  unfold maximalTrajectoryIndexCoupling
  apply Mcmc.Finite.measurable_maximalCoupling_apply
  · intro i
    exact (measurable_trajectoryIndexProbability hpotential hgradient ε
      origin i).comp measurable_fst
  · intro i
    exact (measurable_trajectoryIndexProbability hpotential hgradient ε
      origin i).comp measurable_snd

/-- Randomized multinomial trajectory transition using maximal coupling of the
two conditional categorical selections. -/
noncomputable def maximalCoupledRandomizedMultinomialLeapfrogKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    Kernel (PhaseSpace ι × PhaseSpace ι) (PhaseSpace ι × PhaseSpace ι) :=
  coupledRandomizedMultinomialLeapfrogKernel gradient ε L
    (maximalTrajectoryIndexCoupling potential gradient ε)
    hgradient
    (fun origin selected => measurable_maximalTrajectoryIndexCoupling_apply
      hpotential hgradient ε origin selected)

instance maximalCoupledRandomizedMultinomialLeapfrogKernel_isMarkovKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    IsMarkovKernel
      (maximalCoupledRandomizedMultinomialLeapfrogKernel potential gradient ε L
        hpotential hgradient) := by
  unfold maximalCoupledRandomizedMultinomialLeapfrogKernel
  infer_instance

theorem maximalCoupledRandomizedMultinomialLeapfrogKernel_isCoupling
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    Mcmc.Kernel.IsCoupling
      (maximalCoupledRandomizedMultinomialLeapfrogKernel potential gradient ε L
        hpotential hgradient)
      (randomizedMultinomialLeapfrogKernel potential gradient ε L
        hpotential hgradient)
      (randomizedMultinomialLeapfrogKernel potential gradient ε L
        hpotential hgradient) := by
  apply coupledRandomizedMultinomialLeapfrogKernel_isCoupling
  intro z origin
  exact (maximalTrajectoryIndexCoupling_isMaximal
    potential gradient ε z origin).1

/-- Paper-style position HMC coupling: share standard Gaussian momentum and
maximally couple the two multinomial trajectory-index distributions. -/
noncomputable def maximalSharedMomentumCoupledPositionMultinomialHMC
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    Kernel (Position ι × Position ι) (Position ι × Position ι) :=
  coupledPositionMultinomialHMC
    (maximalCoupledRandomizedMultinomialLeapfrogKernel potential gradient ε L
      hpotential hgradient)
    (sharedPositionMomentumLift (standardMomentumMeasure (ι := ι)))

instance maximalSharedMomentumCoupledPositionMultinomialHMC_isMarkovKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    IsMarkovKernel
      (maximalSharedMomentumCoupledPositionMultinomialHMC potential gradient ε L
        hpotential hgradient) := by
  unfold maximalSharedMomentumCoupledPositionMultinomialHMC
  infer_instance

/-- Both marginals of the maximal shared-momentum coupled HMC transition are
exactly the verified standard position-space multinomial HMC kernel. -/
theorem maximalSharedMomentumCoupledPositionMultinomialHMC_isCoupling
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) :
    Mcmc.Kernel.IsCoupling
      (maximalSharedMomentumCoupledPositionMultinomialHMC potential gradient ε L
        hpotential hgradient)
      (standardPositionMultinomialHMC potential gradient ε L
        hpotential hgradient)
      (standardPositionMultinomialHMC potential gradient ε L
        hpotential hgradient) := by
  unfold maximalSharedMomentumCoupledPositionMultinomialHMC
    standardPositionMultinomialHMC positionMultinomialHMC
  apply coupledPositionMultinomialHMC_isCoupling
  · exact maximalCoupledRandomizedMultinomialLeapfrogKernel_isCoupling
      potential gradient ε L hpotential hgradient
  · exact sharedPositionMomentumLift_isCoupling standardMomentumMeasure

end Mcmc.Hamiltonian
