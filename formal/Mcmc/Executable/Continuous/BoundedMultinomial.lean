import Mcmc.Executable.Continuous.BackendCertificates

/-!
# Conditional numerical certificates for multinomial selection

Multinomial selection is stable when the ideal uniform draw stays farther
from every cumulative-weight boundary than the combined draw and boundary
errors. This is a parallel conditional analysis, not a runtime dependency.
-/

namespace Mcmc.Executable.Continuous

/-- First cumulative boundary strictly above the draw, represented as a
zero-based index. If rounding leaves the draw beyond every boundary, return
the final index (`boundaries.length`). -/
noncomputable def selectCumulative (draw : ℝ) : List ℝ → Nat
  | [] => 0
  | boundary :: rest =>
      if draw < boundary then 0 else 1 + selectCumulative draw rest

/-- Common absolute error bounds for one multinomial selection. -/
structure MultinomialSelectionCertificate where
  computedBoundaries : List ℝ
  idealBoundaries : List ℝ
  computedUniform : ℝ
  idealUniform : ℝ
  boundaryError : ℝ
  uniformError : ℝ
  lengths_eq : computedBoundaries.length = idealBoundaries.length
  boundary_bound : ∀ i (hc : i < computedBoundaries.length)
      (hi : i < idealBoundaries.length),
    Approximates computedBoundaries[i] idealBoundaries[i] boundaryError
  uniform_bound : Approximates computedUniform idealUniform uniformError

/-- Stability means that no ideal cumulative boundary intersects the combined
uniform/boundary uncertainty band. -/
def MultinomialSelectionCertificate.DecisionStable
    (certificate : MultinomialSelectionCertificate) : Prop :=
  ∀ i (hi : i < certificate.idealBoundaries.length),
    certificate.uniformError + certificate.boundaryError <
      |certificate.idealUniform - certificate.idealBoundaries[i]|

private theorem selectCumulative_eq_of_comparisons
    {computed ideal : List ℝ} {computedDraw idealDraw : ℝ}
    (h : ∀ i (hc : i < computed.length) (hi : i < ideal.length),
      (computedDraw < computed[i]) = (idealDraw < ideal[i]))
    (hlen : computed.length = ideal.length) :
    selectCumulative computedDraw computed = selectCumulative idealDraw ideal := by
  induction computed generalizing ideal with
  | nil =>
      cases ideal with
      | nil => rfl
      | cons _ _ => simp at hlen
  | cons boundary rest ih =>
      cases ideal with
      | nil => simp at hlen
      | cons idealBoundary idealRest =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          have hhead := h 0 (by simp) (by simp)
          simp only [List.getElem_cons_zero] at hhead
          simp only [selectCumulative, hhead]
          by_cases hlt : idealDraw < idealBoundary
          · simp [hlt]
          · simp only [hlt, ↓reduceIte]
            congr 1
            apply ih
            · intro i hc hi
              have hh := h (i + 1) (by simpa using hc) (by simpa using hi)
              rw [List.getElem_cons_succ, List.getElem_cons_succ] at hh
              exact hh
            · exact hlen

/-- Outside all cumulative boundary bands, Float64-style and ideal selection
choose the same trajectory index. -/
theorem MultinomialSelectionCertificate.selection_eq
    (certificate : MultinomialSelectionCertificate)
    (hstable : certificate.DecisionStable) :
    selectCumulative certificate.computedUniform certificate.computedBoundaries =
      selectCumulative certificate.idealUniform certificate.idealBoundaries := by
  apply selectCumulative_eq_of_comparisons _ certificate.lengths_eq
  intro i hc hi
  exact comparison_eq_of_approximates certificate.uniform_bound
    (certificate.boundary_bound i hc hi) (hstable i hi)

/-- If the selected indices differ, at least one ideal boundary lies inside
the combined uncertainty band. -/
theorem MultinomialSelectionCertificate.exists_boundary_of_selection_ne
    (certificate : MultinomialSelectionCertificate)
    (hne : selectCumulative certificate.computedUniform
        certificate.computedBoundaries ≠
      selectCumulative certificate.idealUniform certificate.idealBoundaries) :
    ∃ i, ∃ hi : i < certificate.idealBoundaries.length,
      |certificate.idealUniform - certificate.idealBoundaries[i]| ≤
        certificate.uniformError + certificate.boundaryError := by
  by_contra h
  apply hne
  apply certificate.selection_eq
  intro i hi
  have := not_exists.mp h i
  have := not_exists.mp this hi
  exact lt_of_not_ge this

end Mcmc.Executable.Continuous
