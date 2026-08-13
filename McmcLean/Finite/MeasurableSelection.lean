import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Measurable selection from finitely many candidates

This module supplies deterministic measurable tie-breaking for a finite list
of candidates whose parameterized scores are measurable.  It is intended for
the finite optimal-transport construction: once a finite measurable family of
transport vertices is available, `fintypeArgmin` selects an exact minimizer
without invoking a nonmeasurable `Classical.choose`.
-/

namespace McmcLean.Finite

variable {Ω κ : Type*} [MeasurableSpace Ω]

/-- Select the first no-worse candidate recursively from `fallback :: l`.
Ties favor the earlier list entry, making the result deterministic. -/
noncomputable def listArgmin (score : Ω → κ → ENNReal) (fallback : κ) :
    List κ → Ω → κ
  | [] => fun _ => fallback
  | a :: l => fun ω =>
      let b := listArgmin score fallback l ω
      if score ω a ≤ score ω b then a else b

omit [MeasurableSpace Ω] in
/-- The list selector always returns a member of `fallback :: l`. -/
theorem listArgmin_mem (score : Ω → κ → ENNReal) (fallback : κ) :
    ∀ (l : List κ) (ω : Ω), listArgmin score fallback l ω ∈ fallback :: l := by
  intro l
  induction l generalizing fallback with
  | nil => intro ω; simp [listArgmin]
  | cons a l ih =>
      intro ω
      simp only [listArgmin]
      split_ifs
      · simp
      · simp only [List.mem_cons] at *
        rcases ih fallback ω with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

omit [MeasurableSpace Ω] in
/-- The selected candidate minimizes the score over `fallback :: l`. -/
theorem listArgmin_le (score : Ω → κ → ENNReal) (fallback : κ) :
    ∀ (l : List κ) (ω : Ω) (a : κ), a ∈ fallback :: l →
      score ω (listArgmin score fallback l ω) ≤ score ω a := by
  intro l
  induction l generalizing fallback with
  | nil =>
      intro ω a ha
      exact (congrArg (score ω) (List.mem_singleton.mp ha).symm).le
  | cons b l ih =>
      intro ω a ha
      simp only [listArgmin]
      by_cases hbest : score ω b ≤ score ω (listArgmin score fallback l ω)
      · rw [if_pos hbest]
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hbest.trans (ih _ ω _ (by simp))
        · rcases List.mem_cons.mp ha with rfl | ha
          · exact le_rfl
          · exact hbest.trans (ih fallback ω a
              (List.mem_cons_of_mem fallback ha))
      · rw [if_neg hbest]
        rcases List.mem_cons.mp ha with rfl | ha
        · exact ih _ ω _ (by simp)
        · rcases List.mem_cons.mp ha with rfl | ha
          · exact (lt_of_not_ge hbest).le
          · exact ih fallback ω a (List.mem_cons_of_mem fallback ha)

/-- A finite list argmin is measurable when the joint score and candidate
space are measurable. -/
theorem measurable_listArgmin
    [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (score : Ω → κ → ENNReal)
    (hscore : Measurable fun z : Ω × κ => score z.1 z.2)
    (fallback : κ) :
    ∀ l : List κ, Measurable (listArgmin score fallback l) := by
  intro l
  induction l with
  | nil => exact measurable_const
  | cons a l ih =>
      simp only [listArgmin]
      apply Measurable.ite
      · apply measurableSet_le
        · exact hscore.comp (measurable_id.prodMk measurable_const)
        · exact hscore.comp (measurable_id.prodMk ih)
      · exact measurable_const
      · exact ih

variable [Fintype κ] [Nonempty κ]

/-- Canonical argmin over a finite type, using the first element of
`Finset.univ.toList` as the fallback and list order for tie-breaking. -/
noncomputable def fintypeArgmin (score : Ω → κ → ENNReal) : Ω → κ :=
  let fallback := Classical.choice inferInstance
  listArgmin score fallback Finset.univ.toList

omit [MeasurableSpace Ω] in
/-- The canonical finite selector minimizes the score over every candidate. -/
theorem fintypeArgmin_le (score : Ω → κ → ENNReal) (ω : Ω) (a : κ) :
    score ω (fintypeArgmin score ω) ≤ score ω a := by
  classical
  unfold fintypeArgmin
  apply listArgmin_le
  simp

/-- The canonical finite argmin is measurable. -/
theorem measurable_fintypeArgmin
    [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (score : Ω → κ → ENNReal)
    (hscore : Measurable fun z : Ω × κ => score z.1 z.2) :
    Measurable (fintypeArgmin score) := by
  classical
  unfold fintypeArgmin
  exact measurable_listArgmin score hscore _ _

/-- Evaluating a jointly measurable candidate family at the measurable finite
argmin remains measurable. -/
theorem measurable_candidate_fintypeArgmin
    [MeasurableSpace κ] [MeasurableSingletonClass κ]
    {γ : Type*} [MeasurableSpace γ]
    (score : Ω → κ → ENNReal)
    (hscore : Measurable fun z : Ω × κ => score z.1 z.2)
    (candidate : Ω → κ → γ)
    (hcandidate : Measurable fun z : Ω × κ => candidate z.1 z.2) :
    Measurable fun ω => candidate ω (fintypeArgmin score ω) := by
  exact hcandidate.comp
    (measurable_id.prodMk (measurable_fintypeArgmin score hscore))

/-- Sectionwise formulation convenient for a finite discrete candidate type. -/
theorem measurable_fintypeArgmin_of_forall
    [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (score : Ω → κ → ENNReal)
    (hscore : ∀ candidate, Measurable fun ω => score ω candidate) :
    Measurable (fintypeArgmin score) := by
  apply measurable_fintypeArgmin score
  exact measurable_from_prod_countable_left hscore

/-- Sectionwise version for evaluating the selected finite candidate. -/
theorem measurable_candidate_fintypeArgmin_of_forall
    [MeasurableSpace κ] [MeasurableSingletonClass κ]
    {γ : Type*} [MeasurableSpace γ]
    (score : Ω → κ → ENNReal)
    (hscore : ∀ index, Measurable fun ω => score ω index)
    (candidate : Ω → κ → γ)
    (hcandidate : ∀ index, Measurable fun ω => candidate ω index) :
    Measurable fun ω => candidate ω (fintypeArgmin score ω) := by
  apply measurable_candidate_fintypeArgmin score
  · exact measurable_from_prod_countable_left hscore
  · exact measurable_from_prod_countable_left hcandidate

end McmcLean.Finite
