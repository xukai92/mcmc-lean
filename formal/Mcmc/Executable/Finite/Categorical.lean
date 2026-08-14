import Mcmc.Executable.Finite.Trace

/-!
# Executable cumulative categorical selection

Selection scans natural weights from left to right. A draw belongs to the
first half-open cumulative interval containing it. The implementation uses no
division and is shared by trace replay and the later Julia emitter.
-/

namespace Mcmc.Executable.Finite

/-- Select the index whose cumulative natural-weight interval contains
`draw`. Returns `none` exactly when the draw is outside the total mass. -/
def selectFromList : List ℕ → ℕ → Option ℕ
  | [], _ => none
  | weight :: weights, draw =>
      if draw < weight then
        some 0
      else
        (selectFromList weights (draw - weight)).map Nat.succ

@[simp]
theorem selectFromList_nil (draw : ℕ) :
    selectFromList [] draw = none :=
  rfl

theorem selectFromList_cons_of_lt {weight draw : ℕ} (weights : List ℕ)
    (h : draw < weight) :
    selectFromList (weight :: weights) draw = some 0 := by
  simp [selectFromList, h]

theorem selectFromList_cons_of_le {weight draw : ℕ} (weights : List ℕ)
    (h : weight ≤ draw) :
    selectFromList (weight :: weights) draw =
      (selectFromList weights (draw - weight)).map Nat.succ := by
  simp [selectFromList, Nat.not_lt.mpr h]

/-- Every draw below the total weight selects an in-range list index. -/
theorem selectFromList_exists_of_lt_sum {weights : List ℕ} {draw : ℕ}
    (hdraw : draw < weights.sum) :
    ∃ index, selectFromList weights draw = some index ∧ index < weights.length := by
  induction weights generalizing draw with
  | nil => simp at hdraw
  | cons weight weights ih =>
      by_cases hlt : draw < weight
      · exact ⟨0, selectFromList_cons_of_lt weights hlt, by simp⟩
      · have hle : weight ≤ draw := Nat.le_of_not_gt hlt
        have hrest : draw - weight < weights.sum := by
          simp only [List.sum_cons] at hdraw
          omega
        obtain ⟨index, hselect, hindex⟩ := ih hrest
        refine ⟨index + 1, ?_, by simp [hindex]⟩
        rw [selectFromList_cons_of_le weights hle, hselect]
        rfl

/-- Cumulative selection cannot succeed outside the list bounds. -/
theorem selectFromList_index_lt_length {weights : List ℕ} {draw index : ℕ}
    (hselect : selectFromList weights draw = some index) :
    index < weights.length := by
  induction weights generalizing draw index with
  | nil => simp at hselect
  | cons weight weights ih =>
      by_cases hlt : draw < weight
      · rw [selectFromList_cons_of_lt weights hlt] at hselect
        simp at hselect
        subst index
        simp
      · have hle : weight ≤ draw := Nat.le_of_not_gt hlt
        rw [selectFromList_cons_of_le weights hle] at hselect
        cases hrest : selectFromList weights (draw - weight) with
        | none => simp [hrest] at hselect
        | some restIndex =>
            simp only [hrest, Option.map_some, Option.some.injEq] at hselect
            subst index
            simp [ih hrest]

/-- Cumulative selection succeeds exactly for draws below total mass. -/
theorem selectFromList_isSome_iff {weights : List ℕ} {draw : ℕ} :
    (selectFromList weights draw).isSome ↔ draw < weights.sum := by
  induction weights generalizing draw with
  | nil => simp [selectFromList]
  | cons weight weights ih =>
      by_cases hlt : draw < weight
      · simp [selectFromList, hlt, List.sum_cons]
        omega
      · have hle : weight ≤ draw := Nat.le_of_not_gt hlt
        rw [selectFromList_cons_of_le weights hle]
        simp only [Option.isSome_map, ih, List.sum_cons]
        omega

/-- Characterization of cumulative selection by its half-open weight interval. -/
theorem selectFromList_eq_some_iff {weights : List ℕ} {draw index : ℕ} :
    selectFromList weights draw = some index ↔
      index < weights.length ∧
      (weights.take index).sum ≤ draw ∧
      draw < (weights.take (index + 1)).sum := by
  induction weights generalizing draw index with
  | nil => simp [selectFromList]
  | cons weight weights ih =>
      cases index with
      | zero =>
          simp [selectFromList]
      | succ index =>
          by_cases hlt : draw < weight
          · simp [selectFromList, hlt]
            omega
          · have hle : weight ≤ draw := Nat.le_of_not_gt hlt
            rw [selectFromList_cons_of_le weights hle]
            simp only [Option.map_eq_some_iff]
            simp only [Nat.succ.injEq]
            simp only [exists_eq_right, ih, List.length_cons, Nat.succ_lt_succ_iff,
              List.take_succ_cons, List.sum_cons]
            omega

/-- Exactly `weights[index]` primitive draws select an in-range index. -/
theorem card_selectFromList_fiber (weights : List ℕ) (index : ℕ)
    (hindex : index < weights.length) :
    ((Finset.range weights.sum).filter
      fun draw ↦ selectFromList weights draw = some index).card = weights[index] := by
  have hprefix : (weights.take (index + 1)).sum ≤ weights.sum := by
    have hsplit := List.take_append_drop (index + 1) weights
    have hsum := congrArg List.sum hsplit
    simp only [List.sum_append] at hsum
    omega
  have hfiber :
      (Finset.range weights.sum).filter
          (fun draw ↦ selectFromList weights draw = some index) =
        Finset.Ico (weights.take index).sum (weights.take (index + 1)).sum := by
    ext draw
    simp only [Finset.mem_filter, Finset.mem_range, selectFromList_eq_some_iff,
      hindex, true_and, Finset.mem_Ico]
    omega
  rw [hfiber, Nat.card_Ico]
  rw [List.take_add_one]
  simp [hindex]

/-- Natural weights in their stable `Fin` index order. -/
def NatWeights.weightList {n : ℕ} (weights : NatWeights n) : List ℕ :=
  List.ofFn weights.weight

@[simp]
theorem NatWeights.length_weightList {n : ℕ} (weights : NatWeights n) :
    weights.weightList.length = n := by
  simp [NatWeights.weightList]

@[simp]
theorem NatWeights.sum_weightList {n : ℕ} (weights : NatWeights n) :
    weights.weightList.sum = weights.total := by
  simp [NatWeights.weightList, NatWeights.total, List.sum_ofFn]

/-- Executable categorical selection from a proved in-range draw. -/
def NatWeights.select {n : ℕ} (weights : NatWeights n)
    (draw : Fin weights.total) : Fin n := by
  let selected := selectFromList weights.weightList draw
  have hsome : selected.isSome :=
    selectFromList_isSome_iff.mpr (by simpa only [sum_weightList] using draw.isLt)
  let index := selected.get hsome
  have hindex : index < weights.weightList.length :=
    selectFromList_index_lt_length (Option.some_get hsome).symm
  exact ⟨index, by simpa only [length_weightList] using hindex⟩

theorem NatWeights.select_val_eq_iff {n : ℕ} (weights : NatWeights n)
    (draw : Fin weights.total) (index : ℕ) :
    (weights.select draw).val = index ↔
      selectFromList weights.weightList draw.val = some index := by
  unfold NatWeights.select
  simp only
  let hsome : (selectFromList weights.weightList draw.val).isSome :=
    selectFromList_isSome_iff.mpr (by simpa only [sum_weightList] using draw.isLt)
  constructor
  · intro h
    rw [← h]
    exact (Option.some_get hsome).symm
  · intro h
    exact Option.get_of_eq_some hsome h

theorem NatWeights.card_select_fiber {n : ℕ} (weights : NatWeights n)
    (index : Fin n) :
    (Finset.univ.filter fun draw : Fin weights.total ↦
      weights.select draw = index).card = weights.weight index := by
  let source := Finset.univ.filter fun draw : Fin weights.total ↦
    weights.select draw = index
  let target := (Finset.range weights.total).filter fun draw ↦
    selectFromList weights.weightList draw = some index.val
  have hmap : source.map Fin.valEmbedding = target := by
    ext draw
    simp only [source, target, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_range]
    constructor
    · rintro ⟨bounded, hselect, rfl⟩
      exact ⟨bounded.isLt, (weights.select_val_eq_iff bounded index.val).mp
        (congrArg Fin.val hselect)⟩
    · rintro ⟨hdraw, hselect⟩
      let bounded : Fin weights.total := ⟨draw, hdraw⟩
      refine ⟨bounded, ?_, rfl⟩
      apply Fin.ext
      exact (weights.select_val_eq_iff bounded index.val).mpr hselect
  have hcard := congrArg Finset.card hmap
  rw [Finset.card_map] at hcard
  have hfiber := card_selectFromList_fiber weights.weightList index.val
    (by simpa only [NatWeights.length_weightList] using index.isLt)
  rw [NatWeights.sum_weightList] at hfiber
  have htarget : target.card = weights.weight index := by
    simpa [target, NatWeights.weightList] using hfiber
  rw [htarget] at hcard
  exact hcard

/-- PMF denotation of the executable cumulative selector. -/
noncomputable def NatWeights.selectPMF {n : ℕ} (weights : NatWeights n) : PMF (Fin n) :=
  (DrawBound.pmf ⟨weights.total, weights.total_positive⟩).map weights.select

/-- Uniform bounded draws followed by cumulative selection have exactly the
normalized natural-weight law. -/
theorem NatWeights.selectPMF_eq_toPMF {n : ℕ} (weights : NatWeights n) :
    weights.selectPMF = weights.toPMF := by
  ext index
  rw [NatWeights.selectPMF, PMF.map_apply, tsum_fintype]
  simp_rw [NatWeights.DrawBound.pmf, PMF.uniformOfFintype_apply]
  simp only [Fintype.card_fin]
  change (Finset.univ.sum (fun b : Fin (NatWeights.total weights) =>
    if index = NatWeights.select weights b then
      ((NatWeights.total weights : ℕ) : ENNReal)⁻¹ else 0)) = _
  rw [← Finset.sum_filter]
  rw [Finset.sum_const]
  have hcard :
      (Finset.univ.filter fun draw : Fin weights.total ↦
        index = weights.select draw).card = weights.weight index := by
    simpa only [eq_comm] using weights.card_select_fiber index
  rw [hcard, nsmul_eq_mul]
  rw [NatWeights.toPMF_apply, ENNReal.div_eq_inv_mul, mul_comm]

/-- Replay one categorical draw through the validated primitive trace. -/
def replayCategorical {n : ℕ} (weights : NatWeights n)
    (trace : List DrawEvent) :
    Except ExecError (Fin n × List DrawEvent) :=
  match hdraw : replayDraw weights.total trace with
  | .error error => .error error
  | .ok drawResult =>
      .ok (weights.select
        ⟨drawResult.value, replayDraw_success_value_lt hdraw⟩,
        drawResult.remaining)

end Mcmc.Executable.Finite
