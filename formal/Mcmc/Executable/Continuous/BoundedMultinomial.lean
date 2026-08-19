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

/-- Exact cumulative weight through an indexed boundary. -/
noncomputable def cumulativeWeight {n : ℕ}
    (weights : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.Iic i, weights j

/-- Maximum of a nonempty finite family, used by stabilized log weights. -/
noncomputable def finiteMaximum {n : ℕ} [Nonempty (Fin n)]
    (values : Fin n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty values

/-- Taking a finite maximum does not amplify a uniform absolute error. -/
theorem finiteMaximum_approximates
    {n : ℕ} [Nonempty (Fin n)] (computed ideal : Fin n → ℝ)
    (error : ℝ) (h : ∀ i, Approximates (computed i) (ideal i) error) :
    Approximates (finiteMaximum computed) (finiteMaximum ideal) error := by
  have hcomputed : finiteMaximum computed ≤ finiteMaximum ideal + error := by
    unfold finiteMaximum
    apply Finset.sup'_le
    intro i hi
    have hiIdeal := Finset.le_sup' ideal hi
    have hiError := h i
    unfold Approximates at hiError
    have hle : computed i ≤ ideal i + error := by
      linarith [le_abs_self (computed i - ideal i)]
    linarith
  have hideal : finiteMaximum ideal ≤ finiteMaximum computed + error := by
    unfold finiteMaximum
    apply Finset.sup'_le
    intro i hi
    have hiComputed := Finset.le_sup' computed hi
    have hiError := h i
    unfold Approximates at hiError
    have hle : ideal i ≤ computed i + error := by
      linarith [neg_le_abs (computed i - ideal i)]
    linarith
  unfold Approximates
  rw [abs_le]
  constructor <;> linarith

/-- Per-weight absolute errors add over a cumulative boundary. -/
theorem cumulativeWeight_approximates
    {n : ℕ} (computed ideal : Fin n → ℝ) (error : ℝ)
    (h : ∀ j, Approximates (computed j) (ideal j) error)
    (i : Fin n) :
    Approximates (cumulativeWeight computed i) (cumulativeWeight ideal i)
      ((i.val + 1 : ℕ) * error) := by
  unfold cumulativeWeight
  have hsum := Approximates.sum (Finset.Iic i) computed ideal
    (fun _ => error) (fun j _ => h j)
  simpa using hsum

/-- A single conservative error `n * error` bounds every cumulative boundary
of an `n`-weight trajectory. -/
theorem cumulativeWeight_approximates_uniform
    {n : ℕ} (computed ideal : Fin n → ℝ) (error : ℝ)
    (herror : 0 ≤ error)
    (h : ∀ j, Approximates (computed j) (ideal j) error)
    (i : Fin n) :
    Approximates (cumulativeWeight computed i) (cumulativeWeight ideal i)
      (n * error) := by
  apply (cumulativeWeight_approximates computed ideal error h i).mono
  have hi : i.val + 1 ≤ n := i.isLt
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi) herror

/-- Energy and maximum-log-weight errors add when forming a stabilized
log weight `-energy - maxLogWeight`. -/
theorem stabilizedLogWeight_approximates
    {computedEnergy idealEnergy computedMaximum idealMaximum error : ℝ}
    (henergy : Approximates computedEnergy idealEnergy error)
    (hmaximum : Approximates computedMaximum idealMaximum error) :
    Approximates (-computedEnergy - computedMaximum)
      (-idealEnergy - idealMaximum) (error + error) :=
  henergy.neg.sub hmaximum

/-- A backend exponential error plus the two stabilized-log inputs bounds one
computed multinomial weight. -/
theorem stabilizedWeight_approximates
    {computedEnergy idealEnergy computedMaximum idealMaximum
      computedWeight energyError expError : ℝ}
    (hcomputedArg : -computedEnergy - computedMaximum ≤ 0)
    (hidealArg : -idealEnergy - idealMaximum ≤ 0)
    (henergy : Approximates computedEnergy idealEnergy energyError)
    (hmaximum : Approximates computedMaximum idealMaximum energyError)
    (hexp : Approximates computedWeight
      (Real.exp (-computedEnergy - computedMaximum)) expError) :
    Approximates computedWeight (Real.exp (-idealEnergy - idealMaximum))
      (expError + (energyError + energyError)) := by
  exact expNonpositive_approximates_of_exp_error hcomputedArg hidealArg
    (stabilizedLogWeight_approximates henergy hmaximum) hexp

/-- Ideal maximum-shifted Boltzmann weight for a finite energy family. -/
noncomputable def stabilizedBoltzmannWeight
    {n : ℕ} [Nonempty (Fin n)] (energies : Fin n → ℝ) (i : Fin n) : ℝ :=
  Real.exp (-energies i - finiteMaximum (fun j => -energies j))

theorem stabilizedBoltzmannWeight_approximates
    {n : ℕ} [Nonempty (Fin n)]
    (computedEnergy idealEnergy computedWeight : Fin n → ℝ)
    (energyError expError : ℝ)
    (henergy : ∀ i, Approximates (computedEnergy i) (idealEnergy i)
      energyError)
    (hexp : ∀ i, Approximates (computedWeight i)
      (stabilizedBoltzmannWeight computedEnergy i) expError)
    (i : Fin n) :
    Approximates (computedWeight i)
      (stabilizedBoltzmannWeight idealEnergy i)
      (expError + (energyError + energyError)) := by
  have hmaximum : Approximates
      (finiteMaximum (fun j => -computedEnergy j))
      (finiteMaximum (fun j => -idealEnergy j)) energyError :=
    finiteMaximum_approximates _ _ energyError (fun j => (henergy j).neg)
  have hcomputedArg : -computedEnergy i -
      finiteMaximum (fun j => -computedEnergy j) ≤ 0 := by
    have hi := Finset.le_sup' (fun j => -computedEnergy j)
      (Finset.mem_univ i)
    unfold finiteMaximum
    linarith
  have hidealArg : -idealEnergy i -
      finiteMaximum (fun j => -idealEnergy j) ≤ 0 := by
    have hi := Finset.le_sup' (fun j => -idealEnergy j)
      (Finset.mem_univ i)
    unfold finiteMaximum
    linarith
  unfold stabilizedBoltzmannWeight at hexp ⊢
  exact stabilizedWeight_approximates hcomputedArg hidealArg
    (henergy i) hmaximum (hexp i)

/-- End-to-end cumulative-boundary budget from endpoint-energy and backend
exponential errors for maximum-shifted multinomial weights. -/
theorem stabilizedCumulativeWeight_approximates_uniform
    {n : ℕ} [Nonempty (Fin n)]
    (computedEnergy idealEnergy computedWeight : Fin n → ℝ)
    (energyError expError : ℝ)
    (henergyError : 0 ≤ energyError) (hexpError : 0 ≤ expError)
    (henergy : ∀ i, Approximates (computedEnergy i) (idealEnergy i)
      energyError)
    (hexp : ∀ i, Approximates (computedWeight i)
      (stabilizedBoltzmannWeight computedEnergy i) expError)
    (i : Fin n) :
    Approximates (cumulativeWeight computedWeight i)
      (cumulativeWeight (stabilizedBoltzmannWeight idealEnergy) i)
      (n * (expError + (energyError + energyError))) := by
  apply cumulativeWeight_approximates_uniform
    computedWeight (stabilizedBoltzmannWeight idealEnergy)
    (expError + (energyError + energyError))
  · positivity
  · intro j
    exact stabilizedBoltzmannWeight_approximates
      computedEnergy idealEnergy computedWeight energyError expError
      henergy hexp j

/-- Error propagation for the runtime draw `uniform * totalWeight`, including
an explicit backend multiplication error. -/
theorem scaledMultinomialDraw_approximates
    {computedDraw computedUniform idealUniform computedTotal idealTotal
      multiplicationError uniformError totalError : ℝ}
    (hmul : Approximates computedDraw
      (computedUniform * computedTotal) multiplicationError)
    (huniform : Approximates computedUniform idealUniform uniformError)
    (htotal : Approximates computedTotal idealTotal totalError) :
    Approximates computedDraw (idealUniform * idealTotal)
      (multiplicationError +
        (uniformError * |computedTotal| + |idealUniform| * totalError)) := by
  exact hmul.compose (huniform.mul htotal)

noncomputable def totalWeight {n : ℕ} (weights : Fin n → ℝ) : ℝ :=
  ∑ i, weights i

theorem stabilizedTotalWeight_approximates
    {n : ℕ} [Nonempty (Fin n)]
    (computedEnergy idealEnergy computedWeight : Fin n → ℝ)
    (energyError expError : ℝ)
    (henergy : ∀ i, Approximates (computedEnergy i) (idealEnergy i)
      energyError)
    (hexp : ∀ i, Approximates (computedWeight i)
      (stabilizedBoltzmannWeight computedEnergy i) expError) :
    Approximates (totalWeight computedWeight)
      (totalWeight (stabilizedBoltzmannWeight idealEnergy))
      (n * (expError + (energyError + energyError))) := by
  unfold totalWeight
  have hsum := Approximates.sum Finset.univ computedWeight
    (stabilizedBoltzmannWeight idealEnergy)
    (fun _ => expError + (energyError + energyError)) (fun i _ =>
      stabilizedBoltzmannWeight_approximates computedEnergy idealEnergy
        computedWeight energyError expError henergy hexp i)
  convert hsum using 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

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

/-- Assemble the exact list-shaped certificate consumed by cumulative
selection from energy, exponential, cumulative-sum, multiplication, and RNG
primitive bounds. -/
noncomputable def stabilizedMultinomialSelectionCertificate
    {n : ℕ} [Nonempty (Fin n)]
    (computedEnergy idealEnergy computedWeight : Fin n → ℝ)
    (computedDraw computedUnit idealUnit : ℝ)
    (energyError expError multiplicationError unitError : ℝ)
    (henergyNonneg : 0 ≤ energyError) (hexpNonneg : 0 ≤ expError)
    (henergy : ∀ i, Approximates (computedEnergy i) (idealEnergy i)
      energyError)
    (hexp : ∀ i, Approximates (computedWeight i)
      (stabilizedBoltzmannWeight computedEnergy i) expError)
    (hmul : Approximates computedDraw
      (computedUnit * totalWeight computedWeight) multiplicationError)
    (hunit : Approximates computedUnit idealUnit unitError) :
    MultinomialSelectionCertificate where
  computedBoundaries := List.ofFn (cumulativeWeight computedWeight)
  idealBoundaries := List.ofFn
    (cumulativeWeight (stabilizedBoltzmannWeight idealEnergy))
  computedUniform := computedDraw
  idealUniform := idealUnit *
    totalWeight (stabilizedBoltzmannWeight idealEnergy)
  boundaryError := n * (expError + (energyError + energyError))
  uniformError := multiplicationError +
    (unitError * |totalWeight computedWeight| + |idealUnit| *
      (n * (expError + (energyError + energyError))))
  lengths_eq := by simp
  boundary_bound := by
    intro i hc hi
    simp only [List.getElem_ofFn]
    exact stabilizedCumulativeWeight_approximates_uniform
      computedEnergy idealEnergy computedWeight energyError expError
      henergyNonneg hexpNonneg henergy hexp ⟨i, by simpa using hc⟩
  uniform_bound := by
    exact scaledMultinomialDraw_approximates hmul hunit
      (stabilizedTotalWeight_approximates computedEnergy idealEnergy
        computedWeight energyError expError henergy hexp)

/-- Actual rounded cumulative sums and their final total. This inserts the
arithmetic performed by a concrete backend between certified weights and the
selection comparison instead of silently treating prefix summation as exact. -/
structure MultinomialCumulativeArithmeticCertificate
    {n : ℕ} (computedWeight : Fin n → ℝ) where
  computedBoundary : Fin n → ℝ
  computedTotal : ℝ
  boundaryError : ℝ
  totalError : ℝ
  boundaryError_nonneg : 0 ≤ boundaryError
  totalError_nonneg : 0 ≤ totalError
  boundary_bound : ∀ i, Approximates (computedBoundary i)
    (cumulativeWeight computedWeight i) boundaryError
  total_bound : Approximates computedTotal (totalWeight computedWeight)
    totalError

/-- One exact-rational record for a rounded cumulative sum. `weight` is the
next exact Float64 weight, while `computedBoundary` is the runtime prefix. -/
structure RoundedCumulativeRationalStep where
  weight : ℚ
  computedBoundary : ℚ
  error : ℚ
deriving DecidableEq, Repr

/-- Validate every submitted boundary against the exact rational prefix, not
against the preceding rounded boundary. Thus each stored radius is already a
complete prefix-summation error. -/
def RoundedCumulativeRationalCertificate.ValidFrom :
    ℚ → List RoundedCumulativeRationalStep → Prop
  | _, [] => True
  | accumulated, step :: rest =>
      0 ≤ step.error ∧
        |step.computedBoundary - (accumulated + step.weight)| ≤ step.error ∧
        ValidFrom (accumulated + step.weight) rest

instance roundedCumulativeRationalCertificateDecidableValidFrom
    (accumulated : ℚ) (steps : List RoundedCumulativeRationalStep) :
    Decidable (RoundedCumulativeRationalCertificate.ValidFrom accumulated steps) := by
  induction steps generalizing accumulated with
  | nil => exact isTrue trivial
  | cons step rest ih =>
      simp only [RoundedCumulativeRationalCertificate.ValidFrom]
      infer_instance

structure RoundedCumulativeRationalCertificate where
  steps : List RoundedCumulativeRationalStep
deriving DecidableEq, Repr

def RoundedCumulativeRationalCertificate.Valid
    (certificate : RoundedCumulativeRationalCertificate) : Prop :=
  certificate.steps ≠ [] ∧
    RoundedCumulativeRationalCertificate.ValidFrom 0 certificate.steps

instance roundedCumulativeRationalCertificateDecidableValid
    (certificate : RoundedCumulativeRationalCertificate) :
    Decidable certificate.Valid := by
  unfold RoundedCumulativeRationalCertificate.Valid
  infer_instance

def RoundedCumulativeRationalCertificate.check
    (certificate : RoundedCumulativeRationalCertificate) : Bool :=
  decide certificate.Valid

theorem RoundedCumulativeRationalCertificate.head_approximates
    (accumulated : ℚ) (step : RoundedCumulativeRationalStep)
    (rest : List RoundedCumulativeRationalStep)
    (hvalid : RoundedCumulativeRationalCertificate.ValidFrom accumulated
      (step :: rest)) :
    Approximates (step.computedBoundary : ℝ)
      ((accumulated : ℝ) + step.weight) (step.error : ℝ) := by
  rw [Approximates]
  exact_mod_cast hvalid.2.1

/-- Exact-rational residual for the runtime multiplication `uniform * total`
used by cumulative multinomial selection. -/
structure ScaledDrawRationalCertificate where
  uniform : ℚ
  total : ℚ
  computed : ℚ
  error : ℚ
deriving DecidableEq, Repr

def ScaledDrawRationalCertificate.Valid
    (certificate : ScaledDrawRationalCertificate) : Prop :=
  0 ≤ certificate.uniform ∧ certificate.uniform < 1 ∧
    0 ≤ certificate.total ∧ 0 ≤ certificate.error ∧
    |certificate.computed - certificate.uniform * certificate.total| ≤
      certificate.error

instance scaledDrawRationalCertificateDecidableValid
    (certificate : ScaledDrawRationalCertificate) :
    Decidable certificate.Valid := by
  unfold ScaledDrawRationalCertificate.Valid
  infer_instance

def ScaledDrawRationalCertificate.check
    (certificate : ScaledDrawRationalCertificate) : Bool :=
  decide certificate.Valid

theorem ScaledDrawRationalCertificate.approximates
    (certificate : ScaledDrawRationalCertificate)
    (hvalid : certificate.Valid) :
    Approximates (certificate.computed : ℝ)
      ((certificate.uniform : ℝ) * certificate.total)
      (certificate.error : ℝ) := by
  rw [Approximates]
  exact_mod_cast hvalid.2.2.2.2

/-- Full stabilized selection certificate with rounded prefix sums, rounded
total, scaled-draw multiplication, and RNG transport all explicit. -/
noncomputable def stabilizedMultinomialSelectionCertificateWithArithmetic
    {n : ℕ} [Nonempty (Fin n)]
    (computedEnergy idealEnergy computedWeight : Fin n → ℝ)
    (arithmetic : MultinomialCumulativeArithmeticCertificate computedWeight)
    (computedDraw computedUnit idealUnit : ℝ)
    (energyError expError multiplicationError unitError : ℝ)
    (henergyNonneg : 0 ≤ energyError) (hexpNonneg : 0 ≤ expError)
    (henergy : ∀ i, Approximates (computedEnergy i) (idealEnergy i)
      energyError)
    (hexp : ∀ i, Approximates (computedWeight i)
      (stabilizedBoltzmannWeight computedEnergy i) expError)
    (hmul : Approximates computedDraw
      (computedUnit * arithmetic.computedTotal) multiplicationError)
    (hunit : Approximates computedUnit idealUnit unitError) :
    MultinomialSelectionCertificate where
  computedBoundaries := List.ofFn arithmetic.computedBoundary
  idealBoundaries := List.ofFn
    (cumulativeWeight (stabilizedBoltzmannWeight idealEnergy))
  computedUniform := computedDraw
  idealUniform := idealUnit *
    totalWeight (stabilizedBoltzmannWeight idealEnergy)
  boundaryError := arithmetic.boundaryError +
    n * (expError + (energyError + energyError))
  uniformError := multiplicationError +
    (unitError * |arithmetic.computedTotal| + |idealUnit| *
      (arithmetic.totalError +
        n * (expError + (energyError + energyError))))
  lengths_eq := by simp
  boundary_bound := by
    intro i hc hi
    simp only [List.getElem_ofFn]
    let j : Fin n := ⟨i, by simpa using hc⟩
    exact (arithmetic.boundary_bound j).compose
      (stabilizedCumulativeWeight_approximates_uniform
        computedEnergy idealEnergy computedWeight energyError expError
        henergyNonneg hexpNonneg henergy hexp j)
  uniform_bound := by
    have htotal : Approximates arithmetic.computedTotal
        (totalWeight (stabilizedBoltzmannWeight idealEnergy))
        (arithmetic.totalError +
          n * (expError + (energyError + energyError))) :=
      arithmetic.total_bound.compose
        (stabilizedTotalWeight_approximates computedEnergy idealEnergy
          computedWeight energyError expError henergy hexp)
    exact scaledMultinomialDraw_approximates hmul hunit htotal

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

/-- Exact-rational witness that an ideal scaled draw is separated from every
cumulative boundary by more than the complete selection uncertainty. This is
an execution-specific decision certificate, not a claim about the RNG law. -/
structure MultinomialDecisionRationalCertificate where
  computedDraw : ℚ
  computedBoundaries : List ℚ
  uniformError : ℚ
  boundaryError : ℚ
deriving DecidableEq, Repr

def MultinomialDecisionRationalCertificate.Valid
    (certificate : MultinomialDecisionRationalCertificate) : Prop :=
  0 ≤ certificate.uniformError ∧
    0 ≤ certificate.boundaryError ∧
    ∀ boundary ∈ certificate.computedBoundaries,
      certificate.uniformError + certificate.boundaryError <
        |certificate.computedDraw - boundary|

instance multinomialDecisionRationalCertificateDecidableValid
    (certificate : MultinomialDecisionRationalCertificate) :
    Decidable certificate.Valid := by
  unfold MultinomialDecisionRationalCertificate.Valid
  infer_instance

def MultinomialDecisionRationalCertificate.check
    (certificate : MultinomialDecisionRationalCertificate) : Bool :=
  decide certificate.Valid

/-- Oracle-checked separation around the actual computed values proves
equality of the runtime and ideal selected indices. Using the computed margin
avoids pretending that transcendental ideal Boltzmann weights are rational. -/
theorem MultinomialSelectionCertificate.selection_eq_of_rational_margin
    (certificate : MultinomialSelectionCertificate)
    (margin : MultinomialDecisionRationalCertificate)
    (hvalid : margin.Valid)
    (hdraw : certificate.computedUniform = (margin.computedDraw : ℝ))
    (hboundaries : certificate.computedBoundaries =
      List.map (fun value : ℚ => (value : ℝ)) margin.computedBoundaries)
    (huniformError : certificate.uniformError ≤ (margin.uniformError : ℝ))
    (hboundaryError : certificate.boundaryError ≤ (margin.boundaryError : ℝ)) :
    selectCumulative certificate.computedUniform certificate.computedBoundaries =
      selectCumulative certificate.idealUniform certificate.idealBoundaries := by
  apply selectCumulative_eq_of_comparisons _ certificate.lengths_eq
  intro i hc hi
  have hc' : i < margin.computedBoundaries.length := by
    simpa [hboundaries] using hc
  have hmember : margin.computedBoundaries[i] ∈ margin.computedBoundaries :=
    List.getElem_mem _
  have hmargin := hvalid.2.2 margin.computedBoundaries[i] hmember
  have hboundary : certificate.computedBoundaries[i] =
      (margin.computedBoundaries[i] : ℝ) := by
    simp [hboundaries]
  have hmarginReal : certificate.uniformError + certificate.boundaryError <
      |certificate.computedUniform - certificate.computedBoundaries[i]| := by
    have hmarginCast : (margin.uniformError : ℝ) + margin.boundaryError <
        |(margin.computedDraw : ℝ) - margin.computedBoundaries[i]| := by
      exact_mod_cast hmargin
    rw [hdraw, hboundary]
    exact (add_le_add huniformError hboundaryError).trans_lt hmarginCast
  exact (comparison_eq_of_approximates
    (Approximates.symm certificate.uniform_bound)
    (Approximates.symm (certificate.boundary_bound i hc hi)) hmarginReal).symm

end Mcmc.Executable.Continuous
