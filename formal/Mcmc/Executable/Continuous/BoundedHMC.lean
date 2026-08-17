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

theorem VectorApproximates.mono
    {computed ideal : List ℝ} {error larger : ℝ}
    (h : VectorApproximates computed ideal error) (hle : error ≤ larger) :
    VectorApproximates computed ideal larger :=
  ⟨h.1, fun i hc hi => (h.2 i hc hi).trans hle⟩

theorem VectorApproximates.singleton
    {computed ideal error : ℝ} (h : Approximates computed ideal error) :
    VectorApproximates [computed] [ideal] error := by
  refine ⟨rfl, ?_⟩
  intro i hcomputed _
  simp only [List.length_cons, List.length_nil] at hcomputed
  have hi : i = 0 := by omega
  subst i
  simpa [Approximates] using h

theorem VectorApproximates.ofFn
    {dimension : ℕ} {computed ideal : Fin dimension → ℝ} {error : ℝ}
    (h : ∀ i, Approximates (computed i) (ideal i) error) :
    VectorApproximates (List.ofFn computed) (List.ofFn ideal) error := by
  refine ⟨by simp, ?_⟩
  intro i hcomputed _
  have hi : i < dimension := by simpa using hcomputed
  simpa [Approximates] using h ⟨i, hi⟩

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

/-! ### Concrete Euclidean leapfrog error recurrence -/

/-- Nonnegative constants for a componentwise error analysis of one standard
Euclidean leapfrog step. `gradientError` bounds backend gradient evaluation;
`kickRounding` applies to each half-kick and `driftRounding` to the drift. -/
structure EuclideanLeapfrogErrorParameters where
  stepMagnitude : ℝ
  gradientLipschitz : ℝ
  gradientError : ℝ
  kickRounding : ℝ
  driftRounding : ℝ
  stepMagnitude_nonneg : 0 ≤ stepMagnitude
  gradientLipschitz_nonneg : 0 ≤ gradientLipschitz
  gradientError_nonneg : 0 ≤ gradientError
  kickRounding_nonneg : 0 ≤ kickRounding
  driftRounding_nonneg : 0 ≤ driftRounding

noncomputable def EuclideanLeapfrogErrorParameters.halfKickError
    (parameters : EuclideanLeapfrogErrorParameters)
    (positionError momentumError : ℝ) : ℝ :=
  momentumError + parameters.stepMagnitude / 2 *
    (parameters.gradientLipschitz * positionError + parameters.gradientError) +
    parameters.kickRounding

noncomputable def EuclideanLeapfrogErrorParameters.positionGrowth
    (parameters : EuclideanLeapfrogErrorParameters)
    (positionError momentumError : ℝ) : ℝ :=
  positionError + parameters.stepMagnitude *
    parameters.halfKickError positionError momentumError +
    parameters.driftRounding

noncomputable def EuclideanLeapfrogErrorParameters.momentumGrowth
    (parameters : EuclideanLeapfrogErrorParameters)
    (positionError momentumError : ℝ) : ℝ :=
  let half := parameters.halfKickError positionError momentumError
  half + parameters.stepMagnitude / 2 *
    (parameters.gradientLipschitz *
      parameters.positionGrowth positionError momentumError +
      parameters.gradientError) + parameters.kickRounding

/-- Concrete nonnegative recurrence for kick-drift-kick error propagation. -/
noncomputable def EuclideanLeapfrogErrorParameters.toErrorModel
    (parameters : EuclideanLeapfrogErrorParameters) : LeapfrogErrorModel where
  positionGrowth := parameters.positionGrowth
  momentumGrowth := parameters.momentumGrowth
  positionGrowth_nonneg := by
    intro ep em hep hem
    have hhalfStep : 0 ≤ parameters.stepMagnitude / 2 :=
      div_nonneg parameters.stepMagnitude_nonneg (by norm_num)
    have hgradient : 0 ≤ parameters.gradientLipschitz * ep +
        parameters.gradientError :=
      add_nonneg (mul_nonneg parameters.gradientLipschitz_nonneg hep)
        parameters.gradientError_nonneg
    have hhalf : 0 ≤ parameters.halfKickError ep em := by
      exact add_nonneg (add_nonneg hem (mul_nonneg hhalfStep hgradient))
        parameters.kickRounding_nonneg
    exact add_nonneg
      (add_nonneg hep (mul_nonneg parameters.stepMagnitude_nonneg hhalf))
      parameters.driftRounding_nonneg
  momentumGrowth_nonneg := by
    intro ep em hep hem
    have hhalfStep : 0 ≤ parameters.stepMagnitude / 2 :=
      div_nonneg parameters.stepMagnitude_nonneg (by norm_num)
    have hgradient : 0 ≤ parameters.gradientLipschitz * ep +
        parameters.gradientError :=
      add_nonneg (mul_nonneg parameters.gradientLipschitz_nonneg hep)
        parameters.gradientError_nonneg
    have hhalf : 0 ≤ parameters.halfKickError ep em := by
      exact add_nonneg (add_nonneg hem (mul_nonneg hhalfStep hgradient))
        parameters.kickRounding_nonneg
    have hposition : 0 ≤ parameters.positionGrowth ep em :=
      add_nonneg
        (add_nonneg hep (mul_nonneg parameters.stepMagnitude_nonneg hhalf))
        parameters.driftRounding_nonneg
    have hnextGradient : 0 ≤ parameters.gradientLipschitz *
        parameters.positionGrowth ep em + parameters.gradientError :=
      add_nonneg
        (mul_nonneg parameters.gradientLipschitz_nonneg hposition)
        parameters.gradientError_nonneg
    exact add_nonneg (add_nonneg hhalf (mul_nonneg hhalfStep hnextGradient))
      parameters.kickRounding_nonneg

/-! ### Primitive affine-operation witnesses -/

/-- A rounded `base + coefficient * direction` update inherits the operand
bounds plus the supplied final arithmetic-rounding budget. -/
theorem roundedAffineUpdate_approximates
    {computedResult computedBase idealBase computedDirection idealDirection
      coefficient coefficientMagnitude baseError directionError
      roundingError : ℝ}
    (hbase : Approximates computedBase idealBase baseError)
    (hdirection : Approximates computedDirection idealDirection directionError)
    (hcoefficient : |coefficient| ≤ coefficientMagnitude)
    (hrounding : Approximates computedResult
      (computedBase + coefficient * computedDirection) roundingError) :
    Approximates computedResult (idealBase + coefficient * idealDirection)
      (roundingError + baseError + coefficientMagnitude * directionError) := by
  have hscaledRaw := (Approximates.refl coefficient).mul hdirection
  have hscaled : Approximates (coefficient * computedDirection)
      (coefficient * idealDirection) (coefficientMagnitude * directionError) := by
    apply hscaledRaw.mono
    simp only [zero_mul, zero_add]
    exact mul_le_mul_of_nonneg_right hcoefficient hdirection.nonneg
  have hsum := hbase.add hscaled
  have hcomposed := hrounding.compose hsum
  simpa [add_assoc] using hcomposed

/-- Primitive scalar witnesses for one kick-drift-kick coordinate. Gradient
evaluation and each rounded arithmetic update are exposed separately. -/
structure EuclideanLeapfrogCoordinateCertificate
    (parameters : EuclideanLeapfrogErrorParameters) where
  signedStep : ℝ
  signedStep_le : |signedStep| ≤ parameters.stepMagnitude
  computedPosition : ℝ
  idealPosition : ℝ
  computedMomentum : ℝ
  idealMomentum : ℝ
  computedCurrentGradient : ℝ
  idealCurrentGradient : ℝ
  computedHalfMomentum : ℝ
  computedNextPosition : ℝ
  computedNextGradient : ℝ
  idealNextGradient : ℝ
  computedNextMomentum : ℝ
  positionError : ℝ
  momentumError : ℝ
  positionBound : Approximates computedPosition idealPosition positionError
  momentumBound : Approximates computedMomentum idealMomentum momentumError
  currentGradientBound : Approximates computedCurrentGradient idealCurrentGradient
    (parameters.gradientLipschitz * positionError + parameters.gradientError)
  halfKickRoundingBound : Approximates computedHalfMomentum
    (computedMomentum + signedStep / 2 * computedCurrentGradient)
    parameters.kickRounding
  nextGradientBound : Approximates computedNextGradient idealNextGradient
    (parameters.gradientLipschitz *
      parameters.positionGrowth positionError momentumError +
      parameters.gradientError)
  driftRoundingBound : Approximates computedNextPosition
    (computedPosition + signedStep * computedHalfMomentum)
    parameters.driftRounding
  finalKickRoundingBound : Approximates computedNextMomentum
    (computedHalfMomentum + signedStep / 2 * computedNextGradient)
    parameters.kickRounding

noncomputable def EuclideanLeapfrogCoordinateCertificate.idealHalfMomentum
    {parameters : EuclideanLeapfrogErrorParameters}
    (certificate : EuclideanLeapfrogCoordinateCertificate parameters) : ℝ :=
  certificate.idealMomentum + certificate.signedStep / 2 *
    certificate.idealCurrentGradient

noncomputable def EuclideanLeapfrogCoordinateCertificate.idealNextPosition
    {parameters : EuclideanLeapfrogErrorParameters}
    (certificate : EuclideanLeapfrogCoordinateCertificate parameters) : ℝ :=
  certificate.idealPosition + certificate.signedStep *
    certificate.idealHalfMomentum

noncomputable def EuclideanLeapfrogCoordinateCertificate.idealNextMomentum
    {parameters : EuclideanLeapfrogErrorParameters}
    (certificate : EuclideanLeapfrogCoordinateCertificate parameters) : ℝ :=
  certificate.idealHalfMomentum + certificate.signedStep / 2 *
    certificate.idealNextGradient

theorem EuclideanLeapfrogCoordinateCertificate.halfMomentum_approximates
    {parameters : EuclideanLeapfrogErrorParameters}
    (certificate : EuclideanLeapfrogCoordinateCertificate parameters) :
    Approximates certificate.computedHalfMomentum
      certificate.idealHalfMomentum
      (parameters.halfKickError certificate.positionError
        certificate.momentumError) := by
  have hcoefficient : |certificate.signedStep / 2| ≤
      parameters.stepMagnitude / 2 := by
    rw [abs_div]
    norm_num
    exact div_le_div_of_nonneg_right certificate.signedStep_le
      (show (0 : ℝ) ≤ 2 by norm_num)
  have h := roundedAffineUpdate_approximates certificate.momentumBound
    certificate.currentGradientBound hcoefficient
    certificate.halfKickRoundingBound
  simpa [EuclideanLeapfrogCoordinateCertificate.idealHalfMomentum,
    EuclideanLeapfrogErrorParameters.halfKickError, add_assoc, add_comm,
    add_left_comm] using h

theorem EuclideanLeapfrogCoordinateCertificate.nextPosition_approximates
    {parameters : EuclideanLeapfrogErrorParameters}
    (certificate : EuclideanLeapfrogCoordinateCertificate parameters) :
    Approximates certificate.computedNextPosition certificate.idealNextPosition
      (parameters.positionGrowth certificate.positionError
        certificate.momentumError) := by
  have h := roundedAffineUpdate_approximates certificate.positionBound
    certificate.halfMomentum_approximates certificate.signedStep_le
    certificate.driftRoundingBound
  simpa [EuclideanLeapfrogCoordinateCertificate.idealNextPosition,
    EuclideanLeapfrogErrorParameters.positionGrowth, add_assoc, add_comm,
    add_left_comm] using h

theorem EuclideanLeapfrogCoordinateCertificate.nextMomentum_approximates
    {parameters : EuclideanLeapfrogErrorParameters}
    (certificate : EuclideanLeapfrogCoordinateCertificate parameters) :
    Approximates certificate.computedNextMomentum certificate.idealNextMomentum
      (parameters.momentumGrowth certificate.positionError
        certificate.momentumError) := by
  have hcoefficient : |certificate.signedStep / 2| ≤
      parameters.stepMagnitude / 2 := by
    rw [abs_div]
    norm_num
    exact div_le_div_of_nonneg_right certificate.signedStep_le
      (show (0 : ℝ) ≤ 2 by norm_num)
  have h := roundedAffineUpdate_approximates
    certificate.halfMomentum_approximates certificate.nextGradientBound
    hcoefficient certificate.finalKickRoundingBound
  simpa [EuclideanLeapfrogCoordinateCertificate.idealNextMomentum,
    EuclideanLeapfrogErrorParameters.momentumGrowth, add_assoc, add_comm,
    add_left_comm] using h

/-- Package the proved coordinate result as the existing one-dimensional
endpoint certificate, ready for recurrence-indexed trajectory composition. -/
noncomputable def EuclideanLeapfrogCoordinateCertificate.toStepCertificate
    {parameters : EuclideanLeapfrogErrorParameters}
    (certificate : EuclideanLeapfrogCoordinateCertificate parameters) :
    LeapfrogStepCertificate where
  computedPosition := [certificate.computedNextPosition]
  idealPosition := [certificate.idealNextPosition]
  computedMomentum := [certificate.computedNextMomentum]
  idealMomentum := [certificate.idealNextMomentum]
  positionError := parameters.positionGrowth certificate.positionError
    certificate.momentumError
  momentumError := parameters.momentumGrowth certificate.positionError
    certificate.momentumError
  position_bound := VectorApproximates.singleton
    certificate.nextPosition_approximates
  momentum_bound := VectorApproximates.singleton
    certificate.nextMomentum_approximates

/-- Dimension-generic family of coordinate witnesses sharing the same input
error budget. -/
structure EuclideanLeapfrogVectorCertificate
    (parameters : EuclideanLeapfrogErrorParameters) (dimension : ℕ) where
  positionError : ℝ
  momentumError : ℝ
  coordinate : Fin dimension → EuclideanLeapfrogCoordinateCertificate parameters
  coordinate_positionError : ∀ i, (coordinate i).positionError = positionError
  coordinate_momentumError : ∀ i, (coordinate i).momentumError = momentumError

noncomputable def EuclideanLeapfrogVectorCertificate.computedInputPosition
    {parameters : EuclideanLeapfrogErrorParameters} {dimension : ℕ}
    (certificate : EuclideanLeapfrogVectorCertificate parameters dimension) :
    List ℝ :=
  List.ofFn fun i => (certificate.coordinate i).computedPosition

noncomputable def EuclideanLeapfrogVectorCertificate.idealInputPosition
    {parameters : EuclideanLeapfrogErrorParameters} {dimension : ℕ}
    (certificate : EuclideanLeapfrogVectorCertificate parameters dimension) :
    List ℝ :=
  List.ofFn fun i => (certificate.coordinate i).idealPosition

noncomputable def EuclideanLeapfrogVectorCertificate.computedInputMomentum
    {parameters : EuclideanLeapfrogErrorParameters} {dimension : ℕ}
    (certificate : EuclideanLeapfrogVectorCertificate parameters dimension) :
    List ℝ :=
  List.ofFn fun i => (certificate.coordinate i).computedMomentum

noncomputable def EuclideanLeapfrogVectorCertificate.idealInputMomentum
    {parameters : EuclideanLeapfrogErrorParameters} {dimension : ℕ}
    (certificate : EuclideanLeapfrogVectorCertificate parameters dimension) :
    List ℝ :=
  List.ofFn fun i => (certificate.coordinate i).idealMomentum

/-- Aggregate coordinate proofs into the existing vector endpoint interface. -/
noncomputable def EuclideanLeapfrogVectorCertificate.toStepCertificate
    {parameters : EuclideanLeapfrogErrorParameters} {dimension : ℕ}
    (certificate : EuclideanLeapfrogVectorCertificate parameters dimension) :
    LeapfrogStepCertificate where
  computedPosition := List.ofFn fun i =>
    (certificate.coordinate i).computedNextPosition
  idealPosition := List.ofFn fun i =>
    (certificate.coordinate i).idealNextPosition
  computedMomentum := List.ofFn fun i =>
    (certificate.coordinate i).computedNextMomentum
  idealMomentum := List.ofFn fun i =>
    (certificate.coordinate i).idealNextMomentum
  positionError := parameters.positionGrowth certificate.positionError
    certificate.momentumError
  momentumError := parameters.momentumGrowth certificate.positionError
    certificate.momentumError
  position_bound := VectorApproximates.ofFn fun i => by
    simpa [certificate.coordinate_positionError i,
      certificate.coordinate_momentumError i] using
      (certificate.coordinate i).nextPosition_approximates
  momentum_bound := VectorApproximates.ofFn fun i => by
    simpa [certificate.coordinate_positionError i,
      certificate.coordinate_momentumError i] using
      (certificate.coordinate i).nextMomentum_approximates

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

/-- A finite stored trajectory whose endpoint certificates stay below the
declared recurrence at their step indices. This does not assert a platform
roundoff model: the inequalities are explicit fields to be discharged by a
backend proof or checked artifact. -/
structure LeapfrogTrajectoryErrorCertificate
    (model : LeapfrogErrorModel) (initialPositionError initialMomentumError : ℝ)
    (steps : ℕ) where
  endpoint : Fin (steps + 1) → LeapfrogStepCertificate
  positionError_le : ∀ index,
    (endpoint index).positionError ≤
      (iterateLeapfrogError model index.val
        (initialPositionError, initialMomentumError)).1
  momentumError_le : ∀ index,
    (endpoint index).momentumError ≤
      (iterateLeapfrogError model index.val
        (initialPositionError, initialMomentumError)).2

/-- Widen one stored endpoint certificate to the recurrence budget at its
trajectory index. -/
noncomputable def LeapfrogTrajectoryErrorCertificate.scheduledEndpoint
    {model : LeapfrogErrorModel} {initialPositionError initialMomentumError : ℝ}
    {steps : ℕ}
    (certificate : LeapfrogTrajectoryErrorCertificate model
      initialPositionError initialMomentumError steps)
    (index : Fin (steps + 1)) : LeapfrogStepCertificate where
  computedPosition := (certificate.endpoint index).computedPosition
  idealPosition := (certificate.endpoint index).idealPosition
  computedMomentum := (certificate.endpoint index).computedMomentum
  idealMomentum := (certificate.endpoint index).idealMomentum
  positionError := (iterateLeapfrogError model index.val
    (initialPositionError, initialMomentumError)).1
  momentumError := (iterateLeapfrogError model index.val
    (initialPositionError, initialMomentumError)).2
  position_bound := (certificate.endpoint index).position_bound.mono
    (certificate.positionError_le index)
  momentum_bound := (certificate.endpoint index).momentum_bound.mono
    (certificate.momentumError_le index)

/-- A sequence of primitive vector-step certificates aligned with the
concrete recurrence. State-linkage between successive records is deliberately
explicitly outside this error-only structure. -/
structure EuclideanLeapfrogVectorTrajectoryCertificate
    (parameters : EuclideanLeapfrogErrorParameters) (dimension steps : ℕ)
    (initialPositionError initialMomentumError : ℝ) where
  initial : LeapfrogStepCertificate
  initialPositionError_le : initial.positionError ≤ initialPositionError
  initialMomentumError_le : initial.momentumError ≤ initialMomentumError
  step : Fin steps → EuclideanLeapfrogVectorCertificate parameters dimension
  step_positionError : ∀ index,
    (step index).positionError =
      (iterateLeapfrogError parameters.toErrorModel index.val
        (initialPositionError, initialMomentumError)).1
  step_momentumError : ∀ index,
    (step index).momentumError =
      (iterateLeapfrogError parameters.toErrorModel index.val
        (initialPositionError, initialMomentumError)).2

/-- Forget primitive details and obtain the generic recurrence-indexed
trajectory certificate used by the NUTS phase adapter. -/
noncomputable def EuclideanLeapfrogVectorTrajectoryCertificate.toErrorCertificate
    {parameters : EuclideanLeapfrogErrorParameters} {dimension steps : ℕ}
    {initialPositionError initialMomentumError : ℝ}
    (certificate : EuclideanLeapfrogVectorTrajectoryCertificate parameters
      dimension steps initialPositionError initialMomentumError) :
    LeapfrogTrajectoryErrorCertificate parameters.toErrorModel
      initialPositionError initialMomentumError steps where
  endpoint index := Fin.cases certificate.initial
    (fun stepIndex => (certificate.step stepIndex).toStepCertificate) index
  positionError_le := by
    intro index
    refine Fin.cases certificate.initialPositionError_le (fun stepIndex => ?_)
      index
    simp only [Fin.cases_succ,
      EuclideanLeapfrogVectorCertificate.toStepCertificate, Fin.val_succ,
      iterateLeapfrogError]
    rw [certificate.step_positionError stepIndex,
      certificate.step_momentumError stepIndex]
    rfl
  momentumError_le := by
    intro index
    refine Fin.cases certificate.initialMomentumError_le (fun stepIndex => ?_)
      index
    simp only [Fin.cases_succ,
      EuclideanLeapfrogVectorCertificate.toStepCertificate, Fin.val_succ,
      iterateLeapfrogError]
    rw [certificate.step_positionError stepIndex,
      certificate.step_momentumError stepIndex]
    rfl

/-- A recurrence-certified family is a genuine sequential trajectory when
every vector step consumes the preceding stored endpoint, in both computed
and ideal semantics. -/
structure LinkedEuclideanLeapfrogVectorTrajectoryCertificate
    (parameters : EuclideanLeapfrogErrorParameters) (dimension steps : ℕ)
    (initialPositionError initialMomentumError : ℝ) where
  errorCertificate : EuclideanLeapfrogVectorTrajectoryCertificate parameters
    dimension steps initialPositionError initialMomentumError
  computedPosition_link : ∀ index,
    (errorCertificate.step index).computedInputPosition =
      (errorCertificate.toErrorCertificate.endpoint index.castSucc).computedPosition
  idealPosition_link : ∀ index,
    (errorCertificate.step index).idealInputPosition =
      (errorCertificate.toErrorCertificate.endpoint index.castSucc).idealPosition
  computedMomentum_link : ∀ index,
    (errorCertificate.step index).computedInputMomentum =
      (errorCertificate.toErrorCertificate.endpoint index.castSucc).computedMomentum
  idealMomentum_link : ∀ index,
    (errorCertificate.step index).idealInputMomentum =
      (errorCertificate.toErrorCertificate.endpoint index.castSucc).idealMomentum

noncomputable def LinkedEuclideanLeapfrogVectorTrajectoryCertificate.toErrorCertificate
    {parameters : EuclideanLeapfrogErrorParameters} {dimension steps : ℕ}
    {initialPositionError initialMomentumError : ℝ}
    (certificate : LinkedEuclideanLeapfrogVectorTrajectoryCertificate parameters
      dimension steps initialPositionError initialMomentumError) :
    LeapfrogTrajectoryErrorCertificate parameters.toErrorModel
      initialPositionError initialMomentumError steps :=
  certificate.errorCertificate.toErrorCertificate

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
