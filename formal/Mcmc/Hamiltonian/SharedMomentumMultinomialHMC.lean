import Mcmc.Hamiltonian.HMC
import Mcmc.Hamiltonian.CoupledMultinomialHMC
import Mcmc.Kernel.ParallelTempering
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Shared-momentum multinomial HMC kernel theory

This module formalizes a K-chain generalization of the shared-momentum
coupling from `CoupledMultinomialHMC.lean`.  All K chains draw one common
momentum and perform independent multinomial trajectory selection; each
marginal of the resulting joint position kernel is the verified
single-chain `positionMultinomialHMC`.

## Main definitions

* `diagonalMomentumMeasureK`: copy one momentum draw to K coordinates
* `reassociatePhaseK`: reassociate K positions × K momenta to K phase points
* `sharedMomentumLiftK`: augment K positions with shared momentum
* `independentTrajectoryK`: coordinatewise independent trajectory selection
* `sharedMomentumMultinomialHMC`: complete K-chain position kernel

## Main results

* `withinTemp_map_eval`: k-th marginal of coordinatewise application equals
  single-coordinate kernel
* `sharedMomentumMultinomialHMC_marginal`: each coordinate marginal equals
  `positionMultinomialHMC`

## Design note

Product invariance does NOT hold for this kernel — the shared momentum
creates inter-chain correlation by construction. This is a coupling
(correct marginals, correlated joint), not a product-invariant kernel.
The K=2 special case in `CoupledMultinomialHMC` is explicitly proved as
a coupling with verified marginals.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace Mcmc.Hamiltonian

open ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-! ### Diagonal momentum measure for K coordinates -/

/-- Copy one momentum draw into all K coordinates via `Measure.map`. -/
noncomputable def diagonalMomentumMeasureK (K : ℕ)
    (momentumTarget : Measure (Momentum ι)) :
    Measure (Fin K → Momentum ι) :=
  momentumTarget.map fun p => (fun _ : Fin K => p)

instance diagonalMomentumMeasureK_isProbabilityMeasure (K : ℕ)
    (momentumTarget : Measure (Momentum ι))
    [IsProbabilityMeasure momentumTarget] :
    IsProbabilityMeasure (diagonalMomentumMeasureK K momentumTarget) := by
  unfold diagonalMomentumMeasureK
  exact Measure.isProbabilityMeasure_map
    (measurable_pi_lambda _ fun _ => measurable_id).aemeasurable

omit [Fintype ι] in
/-- Projecting the K-diagonal momentum measure to any coordinate recovers
the original momentum target. -/
theorem diagonalMomentumMeasureK_marginal (K : ℕ)
    (momentumTarget : Measure (Momentum ι)) (k : Fin K) :
    (diagonalMomentumMeasureK K momentumTarget).map (· k) = momentumTarget := by
  ext s hs
  calc (diagonalMomentumMeasureK K momentumTarget).map (· k) s
      = (diagonalMomentumMeasureK K momentumTarget) ((· k) ⁻¹' s) :=
        Measure.map_apply (measurable_pi_apply k) hs
    _ = momentumTarget ((fun p (_ : Fin K) => p) ⁻¹' ((· k) ⁻¹' s)) := by
        unfold diagonalMomentumMeasureK
        exact Measure.map_apply (measurable_pi_lambda _ fun _ => measurable_id)
          (hs.preimage (measurable_pi_apply k))
    _ = momentumTarget s := by congr 1

/-! ### Phase-space reassociation for K coordinates -/

/-- Reassociate K positions and K momenta into K phase points. -/
def reassociatePhaseK (K : ℕ)
    (x : (Fin K → Position ι) × (Fin K → Momentum ι)) :
    Fin K → PhaseSpace ι :=
  fun k => (x.1 k, x.2 k)

omit [Fintype ι] in
theorem measurable_reassociatePhaseK (K : ℕ) :
    Measurable (reassociatePhaseK (ι := ι) K) :=
  measurable_pi_lambda _ fun k =>
    ((measurable_pi_apply k).comp measurable_fst).prodMk
      ((measurable_pi_apply k).comp measurable_snd)

/-! ### Shared momentum lift for K coordinates -/

/-- Retain all K positions and augment with one shared momentum draw. -/
noncomputable def sharedMomentumLiftK (K : ℕ)
    (momentumTarget : Measure (Momentum ι)) :
    Kernel (Fin K → Position ι) (Fin K → PhaseSpace ι) :=
  (Kernel.id ×ₖ Kernel.const (Fin K → Position ι)
    (diagonalMomentumMeasureK K momentumTarget)).map (reassociatePhaseK K)

instance sharedMomentumLiftK_isMarkovKernel (K : ℕ)
    (momentumTarget : Measure (Momentum ι))
    [IsProbabilityMeasure momentumTarget] :
    IsMarkovKernel (sharedMomentumLiftK K momentumTarget) := by
  unfold sharedMomentumLiftK
  exact Kernel.IsMarkovKernel.map _ (measurable_reassociatePhaseK K)

/-! ### Position projection -/

/-- Project K phase points to K positions. -/
def positionProjectK (K : ℕ) (z : Fin K → PhaseSpace ι) : Fin K → Position ι :=
  fun k => (z k).1

omit [Fintype ι] in
theorem measurable_positionProjectK (K : ℕ) :
    Measurable (positionProjectK (ι := ι) K) :=
  measurable_pi_lambda _ fun k => measurable_fst.comp (measurable_pi_apply k)

/-! ### liftCoord marginal infrastructure -/

section LiftCoordMarginal

variable {S : Type*} [MeasurableSpace S] {K' : ℕ}

/-- `liftCoord k κ` is a Markov kernel when `κ` is Markov. -/
theorem liftCoord_isMarkovKernel (k : Fin K') (κ : Kernel S S)
    [IsMarkovKernel κ] :
    IsMarkovKernel (Mcmc.Kernel.ParallelTempering.liftCoord k κ) where
  isProbabilityMeasure x :=
    Measure.isProbabilityMeasure_map (measurable_update x).aemeasurable

/-- Applying `liftCoord k κ` and projecting to coordinate k yields `κ (x k)`. -/
theorem liftCoord_map_eval (k : Fin K') (κ : Kernel S S)
    [IsSFiniteKernel κ] (x : Fin K' → S) :
    (Mcmc.Kernel.ParallelTempering.liftCoord k κ x).map
      (Function.eval k) = κ (x k) := by
  show ((κ (x k)).map (Function.update x k)).map (Function.eval k) = κ (x k)
  rw [Measure.map_map (measurable_pi_apply k) (measurable_update x)]
  have : Function.eval k ∘ Function.update x k = id := by
    ext y; exact Function.update_self k y x
  rw [this, Measure.map_id]

/-- Applying `liftCoord j κ` for j ≠ k and projecting to coordinate k gives
the Dirac measure at the original value. -/
theorem liftCoord_map_eval_ne (j k : Fin K') (hjk : j ≠ k) (κ : Kernel S S)
    [IsMarkovKernel κ] (x : Fin K' → S) :
    (Mcmc.Kernel.ParallelTempering.liftCoord j κ x).map
      (Function.eval k) = Measure.dirac (x k) := by
  show ((κ (x j)).map (Function.update x j)).map (Function.eval k) = Measure.dirac (x k)
  rw [Measure.map_map (measurable_pi_apply k) (measurable_update x)]
  have : Function.eval k ∘ Function.update x j = fun _ => x k := by
    ext y; exact Function.update_of_ne (Ne.symm hjk) y x
  rw [this, Measure.map_const, measure_univ, one_smul]

/-- Composing with a kernel that preserves coordinate k leaves the
k-th marginal unchanged. -/
theorem comp_map_eval_of_dirac (k : Fin K')
    (κ η : Kernel (Fin K' → S) (Fin K' → S))
    [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (hκ : ∀ y, (κ y).map (Function.eval k) = Measure.dirac (y k))
    (x : Fin K' → S) :
    ((κ ∘ₖ η) x).map (Function.eval k) = (η x).map (Function.eval k) := by
  rw [Kernel.comp_apply, Measure.map_comp (η x) κ (measurable_pi_apply k)]
  suffices h : κ.map (Function.eval k) =
      Kernel.deterministic (Function.eval k) (measurable_pi_apply k) by
    rw [h, Measure.deterministic_comp_eq_map]
  ext y
  rw [Kernel.map_apply _ (measurable_pi_apply k), hκ y, Kernel.deterministic_apply]

/-- Composing `liftCoord k κ` after a kernel whose k-th marginal is Dirac at
the input value yields `κ (x k)` at coordinate k. -/
theorem comp_liftCoord_map_eval (k : Fin K') (κ : Kernel S S)
    [IsMarkovKernel κ]
    (η : Kernel (Fin K' → S) (Fin K' → S)) [IsSFiniteKernel η]
    (hη : ∀ y, (η y).map (Function.eval k) = Measure.dirac (y k))
    (x : Fin K' → S) :
    ((Mcmc.Kernel.ParallelTempering.liftCoord k κ ∘ₖ η) x).map
      (Function.eval k) = κ (x k) := by
  rw [Kernel.comp_apply,
    Measure.map_comp (η x) (Mcmc.Kernel.ParallelTempering.liftCoord k κ)
      (measurable_pi_apply k)]
  have hmap : (Mcmc.Kernel.ParallelTempering.liftCoord k κ).map (Function.eval k) =
      κ.comap (Function.eval k) (measurable_pi_apply k) := by
    ext y; rw [Kernel.map_apply _ (measurable_pi_apply k),
      liftCoord_map_eval k κ y, Kernel.comap_apply]
  rw [hmap, ← Kernel.comp_deterministic_eq_comap κ (measurable_pi_apply k),
    ← Measure.comp_assoc, Measure.deterministic_comp_eq_map, hη x]
  exact Measure.dirac_bind (Kernel.measurable κ) (x k)

private theorem foldr_liftCoord_isMarkovKernel
    (κ : Kernel S S) [IsMarkovKernel κ] (steps : List (Fin K')) :
    IsMarkovKernel (steps.foldr (fun j acc =>
      Mcmc.Kernel.ParallelTempering.liftCoord j κ ∘ₖ acc) Kernel.id) := by
  induction steps with
  | nil => simp only [List.foldr_nil]; infer_instance
  | cons j rest ih =>
    simp only [List.foldr_cons]
    haveI := ih; haveI := liftCoord_isMarkovKernel j κ; infer_instance

/-- Processing a list of liftCoord steps: coordinate k gets `κ (x k)` if k
appears in the list, otherwise it stays at `δ(x k)`. -/
theorem foldr_liftCoord_map_eval
    (k : Fin K') (κ : Kernel S S) [IsMarkovKernel κ]
    (steps : List (Fin K')) (hnodup : steps.Nodup) :
    ∀ x : Fin K' → S,
      (steps.foldr (fun j acc =>
        Mcmc.Kernel.ParallelTempering.liftCoord j κ ∘ₖ acc) Kernel.id x).map
          (Function.eval k) =
        if k ∈ steps then κ (x k) else Measure.dirac (x k) := by
  induction steps with
  | nil =>
    intro x; simp only [List.foldr_nil, List.not_mem_nil, ↓reduceIte]
    rw [Kernel.id_apply]; exact Measure.map_dirac' (measurable_pi_apply k) x
  | cons j rest ih =>
    have hj_notin : j ∉ rest := (List.nodup_cons.mp hnodup).1
    have hrest_nodup : rest.Nodup := (List.nodup_cons.mp hnodup).2
    intro x; simp only [List.foldr_cons]
    by_cases hjk : j = k
    · subst hjk
      simp only [List.mem_cons, true_or, ↓reduceIte]
      haveI := foldr_liftCoord_isMarkovKernel κ rest
      apply comp_liftCoord_map_eval
      intro y; rw [ih hrest_nodup y, if_neg hj_notin]
    · haveI := liftCoord_isMarkovKernel j κ
      haveI := foldr_liftCoord_isMarkovKernel κ rest
      rw [comp_map_eval_of_dirac k
        (Mcmc.Kernel.ParallelTempering.liftCoord j κ) _
        (fun y => liftCoord_map_eval_ne j k hjk κ y) x, ih hrest_nodup x]
      have hne : k ≠ j := fun h => hjk h.symm
      split <;> rename_i h
      · exact (if_pos (List.mem_cons_of_mem j h)).symm
      · exact (if_neg (fun hm => h ((List.mem_cons.mp hm).elim
          (fun he => absurd he hne) id))).symm

end LiftCoordMarginal

/-! ### withinTemp marginal theorem -/

/-- The k-th marginal of `withinTemp (fun _ => κ)` equals `κ (x k)`.
Each coordinate evolves independently under `κ`, regardless of the
sequential application order used by `withinTemp`. -/
theorem withinTemp_map_eval {S : Type*} [MeasurableSpace S] {K' : ℕ}
    (κ : Kernel S S) [IsMarkovKernel κ]
    (k : Fin K') (x : Fin K' → S) :
    (Mcmc.Kernel.ParallelTempering.withinTemp
      (fun (_ : Fin K') => κ) x).map (Function.eval k) = κ (x k) := by
  unfold Mcmc.Kernel.ParallelTempering.withinTemp
  rw [foldr_liftCoord_map_eval k κ (List.finRange K') (List.nodup_finRange K') x,
    if_pos (List.mem_finRange k)]

/-! ### Independent trajectory selection -/

/-- Coordinatewise independent trajectory selection: apply the single-chain
randomized multinomial leapfrog kernel independently to each of K phase-space
coordinates. -/
noncomputable def independentTrajectoryK
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) (K : ℕ) :
    Kernel (Fin K → PhaseSpace ι) (Fin K → PhaseSpace ι) :=
  Mcmc.Kernel.ParallelTempering.withinTemp (fun (_ : Fin K) =>
    randomizedMultinomialLeapfrogKernel potential gradient ε L
      hpotential hgradient)

instance independentTrajectoryK_isMarkovKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient) (K : ℕ) :
    IsMarkovKernel (independentTrajectoryK potential gradient ε L
      hpotential hgradient K) := by
  unfold independentTrajectoryK Mcmc.Kernel.ParallelTempering.withinTemp
  exact foldr_liftCoord_isMarkovKernel
    (randomizedMultinomialLeapfrogKernel potential gradient ε L hpotential hgradient) _

/-! ### Main joint kernel -/

/-- Shared-momentum multinomial HMC: compose shared momentum lift, independent
coordinatewise trajectory selection, and position projection.  All K chains
share a single momentum draw and independently select trajectory indices. -/
noncomputable def sharedMomentumMultinomialHMC
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (K : ℕ)
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (momentumTarget : Measure (Momentum ι)) :
    Kernel (Fin K → Position ι) (Fin K → Position ι) :=
  (independentTrajectoryK potential gradient ε L hpotential hgradient K ∘ₖ
    sharedMomentumLiftK K momentumTarget).map (positionProjectK K)

instance sharedMomentumMultinomialHMC_isMarkovKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (K : ℕ)
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (momentumTarget : Measure (Momentum ι))
    [IsProbabilityMeasure momentumTarget] :
    IsMarkovKernel (sharedMomentumMultinomialHMC potential gradient ε L K
      hpotential hgradient momentumTarget) := by
  unfold sharedMomentumMultinomialHMC
  exact Kernel.IsMarkovKernel.map _ (measurable_positionProjectK K)

/-! ### Marginal correctness -/

omit [Fintype ι] in
/-- Projecting the position-project map to coordinate k equals projecting
to coordinate k in phase space and then taking position. -/
theorem positionProjectK_eval (K : ℕ) (k : Fin K) :
    Function.eval k ∘ positionProjectK (ι := ι) K =
      Prod.fst ∘ Function.eval k := by
  ext z; rfl

/-- The k-th marginal of `sharedMomentumLiftK` equals the single-chain
position-momentum lift applied at `x k`. -/
theorem sharedMomentumLiftK_map_eval (K : ℕ)
    (momentumTarget : Measure (Momentum ι))
    [IsProbabilityMeasure momentumTarget]
    (k : Fin K) (x : Fin K → Position ι) :
    (sharedMomentumLiftK K momentumTarget x).map (Function.eval k) =
      positionMomentumLift momentumTarget (x k) := by
  unfold sharedMomentumLiftK
  rw [Kernel.map_apply _ (measurable_reassociatePhaseK K),
    Measure.map_map (measurable_pi_apply k) (measurable_reassociatePhaseK K)]
  have h_compose : Function.eval k ∘ reassociatePhaseK (ι := ι) K =
      Prod.map (Function.eval k) (Function.eval k) := by
    ext ⟨xv, pv⟩ <;> rfl
  rw [h_compose, Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
    ← Measure.map_prod_map _ _ (measurable_pi_apply k) (measurable_pi_apply k),
    Measure.map_dirac, diagonalMomentumMeasureK_marginal]
  rw [positionMomentumLift, Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply]

/-- The k-th phase-space marginal of the composition
`independentTrajectoryK ∘ₖ sharedMomentumLiftK` equals the single-chain
composition `randomizedMultinomialLeapfrogKernel ∘ₖ positionMomentumLift`. -/
theorem comp_sharedLift_map_eval
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (K : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient)
    (momentumTarget : Measure (Momentum ι))
    [IsProbabilityMeasure momentumTarget]
    (k : Fin K) (x : Fin K → Position ι) :
    ((independentTrajectoryK potential gradient ε L hpotential hgradient K ∘ₖ
        sharedMomentumLiftK K momentumTarget) x).map (Function.eval k) =
      (randomizedMultinomialLeapfrogKernel potential gradient ε L
        hpotential hgradient ∘ₖ
        positionMomentumLift momentumTarget) (x k) := by
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply k) hs,
    Kernel.comp_apply' _ _ _ hs,
    Kernel.comp_apply' _ _ _ ((measurable_pi_apply k) hs)]
  conv_lhs =>
    arg 2; ext z
    rw [show (independentTrajectoryK potential gradient ε L
        hpotential hgradient K z) ((Function.eval k) ⁻¹' s) =
      ((independentTrajectoryK potential gradient ε L
        hpotential hgradient K z).map (Function.eval k)) s from
      (Measure.map_apply (measurable_pi_apply k) hs).symm]
    unfold independentTrajectoryK
    rw [withinTemp_map_eval
        (randomizedMultinomialLeapfrogKernel potential gradient ε L
          hpotential hgradient) k z]
  rw [← MeasureTheory.lintegral_map
    ((randomizedMultinomialLeapfrogKernel potential gradient ε L
      hpotential hgradient).measurable_coe hs) (measurable_pi_apply k),
    sharedMomentumLiftK_map_eval]

/-- Each coordinate marginal of the shared-momentum multinomial HMC kernel
equals the single-chain `positionMultinomialHMC` kernel. -/
theorem sharedMomentumMultinomialHMC_marginal
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (L : ℕ) (K : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient)
    (momentumTarget : Measure (Momentum ι))
    [IsProbabilityMeasure momentumTarget]
    (k : Fin K) (x : Fin K → Position ι) :
    (sharedMomentumMultinomialHMC potential gradient ε L K
      hpotential hgradient momentumTarget x).map (Function.eval k) =
      positionMultinomialHMC potential gradient ε L hpotential hgradient
        momentumTarget (x k) := by
  unfold sharedMomentumMultinomialHMC positionMultinomialHMC
  rw [Kernel.map_apply _ (measurable_positionProjectK K),
    Measure.map_map (measurable_pi_apply k) (measurable_positionProjectK K),
    positionProjectK_eval,
    ← Measure.map_map measurable_fst (measurable_pi_apply k),
    comp_sharedLift_map_eval,
    Kernel.map_apply _ measurable_fst]

end Mcmc.Hamiltonian
