import Mcmc.Kernel.GeneralConvergence

/-!
# Couplings from local minorization

This module converts a minorization available only on a measurable state set
into global kernel infrastructure.  The first step replaces rows outside the
set by the minorizing probability law, turning the local certificate into an
ordinary Doeblin certificate without changing any row inside the set.
-/

open MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace Mcmc.Kernel

open ProbabilityTheory

variable {α : Type*} [MeasurableSpace α]

/-- A transition locally minorizes `reference` on `D`. -/
def LocallyMinorizes (transition : Kernel α α) (D : Set α)
    (ε : ENNReal) (reference : Measure α) : Prop :=
  ∀ x ∈ D, ∀ s, MeasurableSet s → ε * reference s ≤ transition x s

/-- Replace rows outside `D` by the reference probability law.  On `D` this
is definitionally the original transition. -/
noncomputable def localizedMinorizationKernel
    (transition : Kernel α α) (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) : Kernel α α := by
  classical
  exact Kernel.piecewise hD transition (Kernel.const α reference)

instance localizedMinorizationKernel.instIsMarkovKernel
    (transition : Kernel α α) [IsMarkovKernel transition]
    (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) [IsProbabilityMeasure reference] :
    IsMarkovKernel (localizedMinorizationKernel transition D hD reference) := by
  classical
  unfold localizedMinorizationKernel
  infer_instance

@[simp]
theorem localizedMinorizationKernel_apply_of_mem
    (transition : Kernel α α) (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) {x : α} (hx : x ∈ D) :
    localizedMinorizationKernel transition D hD reference x = transition x := by
  classical
  change (if x ∈ D then transition x else reference) = transition x
  rw [if_pos hx]

@[simp]
theorem localizedMinorizationKernel_apply_of_not_mem
    (transition : Kernel α α) (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) {x : α} (hx : x ∉ D) :
    localizedMinorizationKernel transition D hD reference x = reference := by
  classical
  change (if x ∈ D then transition x else reference) = reference
  rw [if_neg hx]

/-- Local minorization becomes global after replacing the irrelevant rows.
-/
theorem localizedMinorizationKernel_uniformlyMinorizes
    (transition : Kernel α α) (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) (ε : Set.Icc (0 : NNReal) 1)
    (hlocal : LocallyMinorizes transition D ε.1 reference) :
    UniformlyMinorizes
      (localizedMinorizationKernel transition D hD reference) ε.1 reference := by
  intro x s hs
  by_cases hx : x ∈ D
  · rw [localizedMinorizationKernel_apply_of_mem transition D hD reference hx]
    exact hlocal x hx s hs
  · rw [localizedMinorizationKernel_apply_of_not_mem transition D hD reference hx]
    exact mul_le_of_le_one_left (bot_le : 0 ≤ reference s)
      (show (ε.1 : ENNReal) ≤ 1 by exact_mod_cast ε.2.2)

/-- The globalized kernel has the standard residual decomposition, while its
rows on `D` are still exactly the original transition rows. -/
theorem mixture_localizedResidual_apply_of_mem
    (transition : Kernel α α) [IsMarkovKernel transition]
    (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) [IsProbabilityMeasure reference]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hlocal : LocallyMinorizes transition D ε.1 reference)
    {x : α} (hx : x ∈ D) :
    mixture ε (Kernel.const α reference)
        (minorizationResidual
          (localizedMinorizationKernel transition D hD reference)
          reference ε hε
          (localizedMinorizationKernel_uniformlyMinorizes
            transition D hD reference ε hlocal)) x =
      transition x := by
  have hdecomp := congrArg (fun K : Kernel α α => K x)
    (mixture_minorizationResidual_eq
      (localizedMinorizationKernel transition D hD reference)
      reference ε hε
      (localizedMinorizationKernel_uniformlyMinorizes
        transition D hD reference ε hlocal))
  simpa [localizedMinorizationKernel_apply_of_mem
    transition D hD reference hx] using hdecomp

/-- The common reference draw copied onto both output coordinates. -/
noncomputable def diagonalReferenceCoupling
    (reference : Measure α) : Kernel (α × α) (α × α) :=
  synchronousCoupling (Kernel.const α reference)

instance diagonalReferenceCoupling.instIsMarkovKernel
    (reference : Measure α) [IsProbabilityMeasure reference] :
    IsMarkovKernel (diagonalReferenceCoupling reference) := by
  unfold diagonalReferenceCoupling
  infer_instance

theorem diagonalReferenceCoupling_isCoupling
    (reference : Measure α) [IsProbabilityMeasure reference] :
    IsCoupling (diagonalReferenceCoupling reference)
      (Kernel.const α reference) (Kernel.const α reference) := by
  constructor
  · ext current s hs
    rw [Kernel.fst_apply' _ _ hs, Kernel.comap_apply]
    change ((Kernel.const (α × α) reference).map diagonalMap current)
      (Prod.fst ⁻¹' s) = reference s
    rw [Kernel.map_apply' _ measurable_diagonalMap current (measurable_fst hs),
      Kernel.const_apply]
    rfl
  · ext current s hs
    rw [Kernel.snd_apply' _ _ hs, Kernel.comap_apply]
    change ((Kernel.const (α × α) reference).map diagonalMap current)
      (Prod.snd ⁻¹' s) = reference s
    rw [Kernel.map_apply' _ measurable_diagonalMap current (measurable_snd hs),
      Kernel.const_apply]
    rfl

/-- Coupling supplied by the common local-minorization component and
independent residuals of the globalized transition. -/
noncomputable def localizedMinorizationCoreCoupling
    (transition : Kernel α α) [IsMarkovKernel transition]
    (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) [IsProbabilityMeasure reference]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hlocal : LocallyMinorizes transition D ε.1 reference) :
    Kernel (α × α) (α × α) :=
  let localized := localizedMinorizationKernel transition D hD reference
  let hglobal := localizedMinorizationKernel_uniformlyMinorizes
    transition D hD reference ε hlocal
  let residual := minorizationResidual localized reference ε hε hglobal
  mixture ε (diagonalReferenceCoupling reference)
    (independentCoupling residual residual)

instance localizedMinorizationCoreCoupling.instIsMarkovKernel
    (transition : Kernel α α) [IsMarkovKernel transition]
    (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) [IsProbabilityMeasure reference]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hlocal : LocallyMinorizes transition D ε.1 reference) :
    IsMarkovKernel (localizedMinorizationCoreCoupling
      transition D hD reference ε hε hlocal) := by
  unfold localizedMinorizationCoreCoupling
  infer_instance

/-- Both marginals of the core coupling are the residual decomposition of
the globalized transition. -/
theorem localizedMinorizationCoreCoupling_isCoupling
    (transition : Kernel α α) [IsMarkovKernel transition]
    (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) [IsProbabilityMeasure reference]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hlocal : LocallyMinorizes transition D ε.1 reference) :
    let localized := localizedMinorizationKernel transition D hD reference
    let hglobal := localizedMinorizationKernel_uniformlyMinorizes
      transition D hD reference ε hlocal
    let residual := minorizationResidual localized reference ε hε hglobal
    IsCoupling (localizedMinorizationCoreCoupling
      transition D hD reference ε hε hlocal)
      (mixture ε (Kernel.const α reference) residual)
      (mixture ε (Kernel.const α reference) residual) := by
  dsimp
  apply mixture_isCoupling
  · exact diagonalReferenceCoupling_isCoupling reference
  · exact independentCoupling_isCoupling _ _

/-- The core coupling uses its common component with probability `ε`, hence
has at least `ε` diagonal mass at every input pair. -/
theorem coe_le_localizedMinorizationCoreCoupling_diagonal
    [MeasurableEq α]
    (transition : Kernel α α) [IsMarkovKernel transition]
    (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) [IsProbabilityMeasure reference]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hlocal : LocallyMinorizes transition D ε.1 reference)
    (current : α × α) :
    (ε.1 : ENNReal) ≤ localizedMinorizationCoreCoupling
      transition D hD reference ε hε hlocal current (Set.diagonal α) := by
  calc
    (ε.1 : ENNReal) = (ε.1 : ENNReal) *
        diagonalReferenceCoupling reference current (Set.diagonal α) := by
      have hdiag : diagonalReferenceCoupling reference current
          (Set.diagonal α) = 1 := by
        unfold diagonalReferenceCoupling synchronousCoupling
        rw [Kernel.map_apply' _ measurable_diagonalMap current
          measurableSet_diagonal, Kernel.comap_apply, Kernel.const_apply]
        have hpre : diagonalMap ⁻¹' Set.diagonal α = Set.univ := by
          ext y
          simp [diagonalMap]
        rw [hpre, measure_univ]
      rw [hdiag, mul_one]
    _ ≤ _ := by
      exact mixture_apply_first_le ε _ _ current measurableSet_diagonal

/-- Use the common-component coupling when both inputs lie in `D`, and the
ordinary independent coupling elsewhere. -/
noncomputable def localMinorizationCoupling
    (transition : Kernel α α) [IsMarkovKernel transition]
    (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) [IsProbabilityMeasure reference]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hlocal : LocallyMinorizes transition D ε.1 reference) :
    Kernel (α × α) (α × α) := by
  classical
  exact Kernel.piecewise (hD.prod hD)
    (localizedMinorizationCoreCoupling
      transition D hD reference ε hε hlocal)
    (independentCoupling transition transition)

instance localMinorizationCoupling.instIsMarkovKernel
    (transition : Kernel α α) [IsMarkovKernel transition]
    (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) [IsProbabilityMeasure reference]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hlocal : LocallyMinorizes transition D ε.1 reference) :
    IsMarkovKernel (localMinorizationCoupling
      transition D hD reference ε hε hlocal) := by
  classical
  unfold localMinorizationCoupling
  infer_instance

theorem localMinorizationCoupling_isCoupling
    (transition : Kernel α α) [IsMarkovKernel transition]
    (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) [IsProbabilityMeasure reference]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hlocal : LocallyMinorizes transition D ε.1 reference) :
    IsCoupling (localMinorizationCoupling
      transition D hD reference ε hε hlocal) transition transition := by
  classical
  let core := localizedMinorizationCoreCoupling
    transition D hD reference ε hε hlocal
  let localized := localizedMinorizationKernel transition D hD reference
  let hglobal := localizedMinorizationKernel_uniformlyMinorizes
    transition D hD reference ε hlocal
  let residual := minorizationResidual localized reference ε hε hglobal
  have hcore : IsCoupling core
      (mixture ε (Kernel.const α reference) residual)
      (mixture ε (Kernel.const α reference) residual) :=
    localizedMinorizationCoreCoupling_isCoupling
      transition D hD reference ε hε hlocal
  have hindependent := independentCoupling_isCoupling transition transition
  constructor
  · ext current s hs
    rw [Kernel.fst_apply' _ _ hs, Kernel.comap_apply,
      localMinorizationCoupling, Kernel.piecewise_apply']
    split_ifs with hcurrent
    · rw [← Kernel.fst_apply' core current hs, hcore.fst_apply]
      have hx : current.1 ∈ D := hcurrent.1
      exact congrArg (fun μ : Measure α => μ s)
        (mixture_localizedResidual_apply_of_mem
          transition D hD reference ε hε hlocal hx)
    · rw [← Kernel.fst_apply' (independentCoupling transition transition)
          current hs,
        hindependent.fst_apply]
  · ext current s hs
    rw [Kernel.snd_apply' _ _ hs, Kernel.comap_apply,
      localMinorizationCoupling, Kernel.piecewise_apply']
    split_ifs with hcurrent
    · rw [← Kernel.snd_apply' core current hs, hcore.snd_apply]
      have hx : current.2 ∈ D := hcurrent.2
      exact congrArg (fun μ : Measure α => μ s)
        (mixture_localizedResidual_apply_of_mem
          transition D hD reference ε hε hlocal hx)
    · rw [← Kernel.snd_apply' (independentCoupling transition transition)
          current hs,
        hindependent.snd_apply]

/-- On `D × D`, the local-minorization coupling has diagonal mass at least
the minorization coefficient. -/
theorem localMinorizationCoupling_isExactMeetingSmallSet
    [MeasurableEq α]
    (transition : Kernel α α) [IsMarkovKernel transition]
    (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) [IsProbabilityMeasure reference]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hlocal : LocallyMinorizes transition D ε.1 reference) :
    IsExactMeetingSmallSet
      (localMinorizationCoupling transition D hD reference ε hε hlocal)
      (D ×ˢ D) ε.1 := by
  intro current hcurrent
  classical
  rw [localMinorizationCoupling, Kernel.piecewise_apply', if_pos hcurrent]
  exact coe_le_localizedMinorizationCoreCoupling_diagonal
    transition D hD reference ε hε hlocal current

/-- Sticky version used by meeting-time arguments. -/
noncomputable def faithfulLocalMinorizationCoupling
    [MeasurableEq α]
    (transition : Kernel α α) [IsMarkovKernel transition]
    (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) [IsProbabilityMeasure reference]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hlocal : LocallyMinorizes transition D ε.1 reference) :
    Kernel (α × α) (α × α) :=
  stickyCoupling transition
    (localMinorizationCoupling transition D hD reference ε hε hlocal)

instance faithfulLocalMinorizationCoupling.instIsMarkovKernel
    [MeasurableEq α]
    (transition : Kernel α α) [IsMarkovKernel transition]
    (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) [IsProbabilityMeasure reference]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hlocal : LocallyMinorizes transition D ε.1 reference) :
    IsMarkovKernel (faithfulLocalMinorizationCoupling
      transition D hD reference ε hε hlocal) := by
  unfold faithfulLocalMinorizationCoupling
  infer_instance

theorem faithfulLocalMinorizationCoupling_isCoupling
    [MeasurableEq α]
    (transition : Kernel α α) [IsMarkovKernel transition]
    (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) [IsProbabilityMeasure reference]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hlocal : LocallyMinorizes transition D ε.1 reference) :
    IsCoupling (faithfulLocalMinorizationCoupling
      transition D hD reference ε hε hlocal) transition transition := by
  apply stickyCoupling_isCoupling
  exact localMinorizationCoupling_isCoupling
    transition D hD reference ε hε hlocal

theorem faithfulLocalMinorizationCoupling_isFaithful
    [MeasurableEq α]
    (transition : Kernel α α) [IsMarkovKernel transition]
    (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) [IsProbabilityMeasure reference]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hlocal : LocallyMinorizes transition D ε.1 reference) :
    IsFaithful (faithfulLocalMinorizationCoupling
      transition D hD reference ε hε hlocal) := by
  exact stickyCoupling_isFaithful transition _

theorem faithfulLocalMinorizationCoupling_isExactMeetingSmallSet
    [MeasurableEq α]
    (transition : Kernel α α) [IsMarkovKernel transition]
    (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) [IsProbabilityMeasure reference]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hlocal : LocallyMinorizes transition D ε.1 reference) :
    IsExactMeetingSmallSet
      (faithfulLocalMinorizationCoupling
        transition D hD reference ε hε hlocal)
      (D ×ˢ D) ε.1 := by
  apply stickyCoupling_isExactMeetingSmallSet
  exact localMinorizationCoupling_isExactMeetingSmallSet
    transition D hD reference ε hε hlocal

end Mcmc.Kernel
