import Mcmc.Executable.Continuous.BoundedRWMH

/-!
# Bounded numerical refinement for vector HMC

Backend-independent bounds for vector leapfrog, Hamiltonian evaluation, and
the discontinuous endpoint decision. Concrete Float64/libm/RNG bounds remain
inputs, just as in the scalar RWMH refinement layer.
-/

namespace Mcmc.Executable.Continuous

/-- Coordinatewise absolute-error bound for equally shaped vectors. -/
def VectorApproximates (computed ideal : List ℝ) (error : ℝ) : Prop :=
  computed.length = ideal.length ∧
    ∀ i (hc : i < computed.length) (hi : i < ideal.length),
      |computed[i] - ideal[i]| ≤ error

theorem VectorApproximates.refl (value : List ℝ) :
    VectorApproximates value value 0 := by
  refine ⟨rfl, ?_⟩
  intro i hi _
  simp

/-- Extract a coordinatewise scalar bound at any index known to lie in both
vectors. This named adapter feeds componentwise phase-space certificates. -/
theorem VectorApproximates.at
    {computed ideal : List ℝ} {error : ℝ}
    (h : VectorApproximates computed ideal error)
    (i : ℕ) (hcomputed : i < computed.length) (hideal : i < ideal.length) :
    Approximates computed[i] ideal[i] error :=
  h.2 i hcomputed hideal

/-- One leapfrog step's abstract rounding contract. It deliberately isolates
the backend-specific arithmetic and gradient evaluation bounds. -/
structure LeapfrogStepCertificate where
  computedPosition : List ℝ
  idealPosition : List ℝ
  computedMomentum : List ℝ
  idealMomentum : List ℝ
  positionError : ℝ
  momentumError : ℝ
  position_bound : VectorApproximates computedPosition idealPosition positionError
  momentum_bound : VectorApproximates computedMomentum idealMomentum momentumError

/-- Per-step error recurrence. `positionGrowth` and `momentumGrowth` may encode
rounding plus a Lipschitz gradient bound for a supported numeric backend. -/
structure LeapfrogErrorModel where
  positionGrowth : ℝ → ℝ → ℝ
  momentumGrowth : ℝ → ℝ → ℝ
  positionGrowth_nonneg : ∀ ep em, 0 ≤ ep → 0 ≤ em → 0 ≤ positionGrowth ep em
  momentumGrowth_nonneg : ∀ ep em, 0 ≤ ep → 0 ≤ em → 0 ≤ momentumGrowth ep em

def iterateLeapfrogError (model : LeapfrogErrorModel) : Nat → ℝ × ℝ → ℝ × ℝ
  | 0, errors => errors
  | steps + 1, errors =>
      let previous := iterateLeapfrogError model steps errors
      (model.positionGrowth previous.1 previous.2,
        model.momentumGrowth previous.1 previous.2)

theorem iterateLeapfrogError_nonneg (model : LeapfrogErrorModel)
    (steps : Nat) {ep em : ℝ} (hep : 0 ≤ ep) (hem : 0 ≤ em) :
    0 ≤ (iterateLeapfrogError model steps (ep, em)).1 ∧
      0 ≤ (iterateLeapfrogError model steps (ep, em)).2 := by
  induction steps with
  | zero => exact ⟨hep, hem⟩
  | succ steps ih =>
      exact ⟨model.positionGrowth_nonneg _ _ ih.1 ih.2,
        model.momentumGrowth_nonneg _ _ ih.1 ih.2⟩

/-- Complete endpoint-HMC numeric certificate after a fixed trajectory. -/
structure HmcErrorCertificate where
  computedCurrent : List ℝ
  idealCurrent : List ℝ
  computedProposal : List ℝ
  idealProposal : List ℝ
  computedEnergyDifference : ℝ
  idealEnergyDifference : ℝ
  computedThreshold : ℝ
  idealThreshold : ℝ
  computedUniform : ℝ
  idealUniform : ℝ
  currentError : ℝ
  proposalError : ℝ
  energyError : ℝ
  thresholdError : ℝ
  uniformError : ℝ
  current_bound : VectorApproximates computedCurrent idealCurrent currentError
  proposal_bound : VectorApproximates computedProposal idealProposal proposalError
  energy_bound : Approximates computedEnergyDifference idealEnergyDifference energyError
  threshold_bound : Approximates computedThreshold idealThreshold thresholdError
  uniform_bound : Approximates computedUniform idealUniform uniformError

def HmcErrorCertificate.DecisionStable (certificate : HmcErrorCertificate) : Prop :=
  certificate.uniformError + certificate.thresholdError <
    |certificate.idealUniform - certificate.idealThreshold|

theorem HmcErrorCertificate.comparison_eq
    (certificate : HmcErrorCertificate) (hstable : certificate.DecisionStable) :
    (certificate.computedUniform < certificate.computedThreshold) =
      (certificate.idealUniform < certificate.idealThreshold) :=
  comparison_eq_of_approximates certificate.uniform_bound
    certificate.threshold_bound hstable

/-- Stable endpoint decisions select corresponding approximate vectors. -/
theorem HmcErrorCertificate.result_approximates
    (certificate : HmcErrorCertificate) (hstable : certificate.DecisionStable) :
    VectorApproximates
      (if certificate.computedUniform < certificate.computedThreshold then
        certificate.computedProposal else certificate.computedCurrent)
      (if certificate.idealUniform < certificate.idealThreshold then
        certificate.idealProposal else certificate.idealCurrent)
      (max certificate.proposalError certificate.currentError) := by
  have hcomparison := certificate.comparison_eq hstable
  by_cases hideal : certificate.idealUniform < certificate.idealThreshold
  · have hcomputed : certificate.computedUniform < certificate.computedThreshold := by
      simpa [hideal] using hcomparison
    simp only [hideal, hcomputed, if_true]
    exact ⟨certificate.proposal_bound.1, fun i hc hi =>
      (certificate.proposal_bound.2 i hc hi).trans (le_max_left _ _)⟩
  · have hcomputed : ¬certificate.computedUniform < certificate.computedThreshold := by
      simpa [hideal] using hcomparison
    simp only [hideal, hcomputed, if_false]
    exact ⟨certificate.current_bound.1, fun i hc hi =>
      (certificate.current_bound.2 i hc hi).trans (le_max_right _ _)⟩

/-- Energy-difference error is the sum of the two endpoint-energy errors. -/
theorem energyDifference_approximates
    {computedCurrent idealCurrent computedNext idealNext
      currentError nextError : ℝ}
    (hcurrent : Approximates computedCurrent idealCurrent currentError)
    (hnext : Approximates computedNext idealNext nextError) :
    Approximates (computedCurrent - computedNext) (idealCurrent - idealNext)
      (currentError + nextError) :=
  hcurrent.sub hnext

/-- A bounded-region Lipschitz certificate transports phase-state error into
an endpoint-energy error. Backend evaluation error remains an independent
additive term. -/
theorem endpointEnergy_approximates_of_lipschitzOn
    {α : Type*} [PseudoMetricSpace α]
    (energy : α → ℝ) (region : Set α) (L : NNReal)
    (hlip : LipschitzOnWith L energy region)
    {computedState idealState : α}
    (hcomputedRegion : computedState ∈ region)
    (hidealRegion : idealState ∈ region)
    {computedEnergy evaluationError stateError : ℝ}
    (hevaluation : Approximates computedEnergy
      (energy computedState) evaluationError)
    (hstate : dist computedState idealState ≤ stateError) :
    Approximates computedEnergy (energy idealState)
      (evaluationError + L * stateError) := by
  unfold Approximates at hevaluation ⊢
  calc
    |computedEnergy - energy idealState| ≤
        |computedEnergy - energy computedState| +
          |energy computedState - energy idealState| := by
      rw [show computedEnergy - energy idealState =
          (computedEnergy - energy computedState) +
            (energy computedState - energy idealState) by ring]
      exact abs_add_le _ _
    _ ≤ evaluationError + L * dist computedState idealState :=
      add_le_add hevaluation (by
        simpa [Real.dist_eq] using
          hlip.dist_le_mul computedState hcomputedRegion idealState hidealRegion)
    _ ≤ evaluationError + L * stateError := by
      gcongr

/-- Exponentiation plus clamping turns an energy-difference certificate into
an acceptance-threshold certificate, conditional on a concrete exp bound. -/
theorem hmcThreshold_approximates
    {computedDifference idealDifference differenceError
      computedThreshold expError : ℝ}
    (hdifference : Approximates computedDifference idealDifference differenceError)
    (hexp : Approximates computedThreshold
      (Real.exp (min 0 computedDifference)) expError) :
    Approximates computedThreshold (Real.exp (min 0 idealDifference))
      (expError + differenceError) := by
  exact threshold_approximates_of_exp_error hdifference hexp

end Mcmc.Executable.Continuous
