import Mcmc.Executable.Continuous.BoundedHMC
import Mcmc.Executable.DynamicTreeIR

/-!
# Bounded decision refinement for dynamic NUTS trees

This module certifies the discontinuous Boolean decisions used by a
finite-precision dynamic-tree builder. It does not claim that Float64 phase
points equal ideal-real phase points. Instead, callers supply absolute error
bounds for the scalar comparisons. A decision is certified only when its
computed value lies strictly outside the corresponding uncertainty band.
-/

namespace Mcmc.Executable.Continuous

open Mcmc.Finite.MarkovKernel

/-- A comparison with zero whose computed value is separated from the entire
absolute-error uncertainty interval. -/
structure SeparatedZeroCertificate where
  computed : ℝ
  ideal : ℝ
  error : ℝ
  bound : Approximates computed ideal error
  separated : computed < -error ∨ error < computed

/-- Boolean sign decision made by the numerical implementation. -/
noncomputable def SeparatedZeroCertificate.computedNegative
    (certificate : SeparatedZeroCertificate) : Bool :=
  decide (certificate.computed < 0)

/-- Ideal-real sign decision consumed by the mathematical tree. -/
noncomputable def SeparatedZeroCertificate.idealNegative
    (certificate : SeparatedZeroCertificate) : Bool :=
  decide (certificate.ideal < 0)

/-- Separation from zero makes the computed and ideal sign decisions equal.
Equality cases are intentionally uncertifiable. -/
theorem SeparatedZeroCertificate.computedNegative_eq_idealNegative
    (certificate : SeparatedZeroCertificate) :
    certificate.computedNegative = certificate.idealNegative := by
  have herror := certificate.bound.nonneg
  have habs := certificate.bound
  rw [Approximates] at habs
  have hinterval := abs_le.mp habs
  rcases certificate.separated with hnegative | hpositive
  · have hcomputed : certificate.computed < 0 := by linarith
    have hideal : certificate.ideal < 0 := by linarith
    simp [SeparatedZeroCertificate.computedNegative,
      SeparatedZeroCertificate.idealNegative, hcomputed, hideal]
  · have hcomputed : ¬ certificate.computed < 0 := by linarith
    have hideal : ¬ certificate.ideal < 0 := by linarith
    simp [SeparatedZeroCertificate.computedNegative,
      SeparatedZeroCertificate.idealNegative, hcomputed, hideal]

/-- Two-sided scalar comparison certificate. This is the form used for slice
eligibility and divergence thresholds: errors from both operands add before
the computed difference is tested for strict separation from zero. -/
structure SeparatedComparisonCertificate where
  computedLeft : ℝ
  idealLeft : ℝ
  computedRight : ℝ
  idealRight : ℝ
  leftError : ℝ
  rightError : ℝ
  leftBound : Approximates computedLeft idealLeft leftError
  rightBound : Approximates computedRight idealRight rightError
  separated :
    computedLeft - computedRight < -(leftError + rightError) ∨
      leftError + rightError < computedLeft - computedRight

noncomputable def SeparatedComparisonCertificate.differenceCertificate
    (certificate : SeparatedComparisonCertificate) :
    SeparatedZeroCertificate where
  computed := certificate.computedLeft - certificate.computedRight
  ideal := certificate.idealLeft - certificate.idealRight
  error := certificate.leftError + certificate.rightError
  bound := certificate.leftBound.sub certificate.rightBound
  separated := certificate.separated

noncomputable def SeparatedComparisonCertificate.computedLess
    (certificate : SeparatedComparisonCertificate) : Bool :=
  decide (certificate.computedLeft < certificate.computedRight)

noncomputable def SeparatedComparisonCertificate.idealLess
    (certificate : SeparatedComparisonCertificate) : Bool :=
  decide (certificate.idealLeft < certificate.idealRight)

/-- A separated bounded comparison produces exactly the ideal-real Boolean. -/
theorem SeparatedComparisonCertificate.computedLess_eq_idealLess
    (certificate : SeparatedComparisonCertificate) :
    certificate.computedLess = certificate.idealLess := by
  change decide (certificate.computedLeft < certificate.computedRight) =
    decide (certificate.idealLeft < certificate.idealRight)
  have h := certificate.differenceCertificate.computedNegative_eq_idealNegative
  change decide (certificate.computedLeft - certificate.computedRight < 0) =
    decide (certificate.idealLeft - certificate.idealRight < 0) at h
  simpa only [sub_lt_zero] using h

/-! ### Slice eligibility and divergence continuation -/

/-- Bounded Hamiltonian evidence for one NUTS leaf. We use the strict
log-slice convention `logSlice < -energy`; equality is deliberately left
uncertified. Divergence continuation uses
`logSlice < maxEnergyError - energy`. -/
structure NUTSLeafEnergyCertificate where
  computedLogSlice : ℝ
  idealLogSlice : ℝ
  computedEnergy : ℝ
  idealEnergy : ℝ
  computedMaxEnergyError : ℝ
  idealMaxEnergyError : ℝ
  computedContinuationThreshold : ℝ
  logSliceError : ℝ
  energyError : ℝ
  maxEnergyErrorError : ℝ
  continuationThresholdRoundingError : ℝ
  logSliceBound : Approximates computedLogSlice idealLogSlice logSliceError
  energyBound : Approximates computedEnergy idealEnergy energyError
  maxEnergyErrorBound : Approximates computedMaxEnergyError idealMaxEnergyError
    maxEnergyErrorError
  continuationThresholdRoundingBound : Approximates
    computedContinuationThreshold (computedMaxEnergyError - computedEnergy)
    continuationThresholdRoundingError
  eligibleSeparated :
    computedLogSlice - (-computedEnergy) < -(logSliceError + energyError) ∨
      logSliceError + energyError < computedLogSlice - (-computedEnergy)
  continuesSeparated :
    computedLogSlice - computedContinuationThreshold <
        -(logSliceError + (continuationThresholdRoundingError +
          (maxEnergyErrorError + energyError))) ∨
      logSliceError + (continuationThresholdRoundingError +
        (maxEnergyErrorError + energyError)) <
        computedLogSlice - computedContinuationThreshold

noncomputable def NUTSLeafEnergyCertificate.eligibleComparison
    (certificate : NUTSLeafEnergyCertificate) :
    SeparatedComparisonCertificate where
  computedLeft := certificate.computedLogSlice
  idealLeft := certificate.idealLogSlice
  computedRight := -certificate.computedEnergy
  idealRight := -certificate.idealEnergy
  leftError := certificate.logSliceError
  rightError := certificate.energyError
  leftBound := certificate.logSliceBound
  rightBound := certificate.energyBound.neg
  separated := certificate.eligibleSeparated

noncomputable def NUTSLeafEnergyCertificate.continuesComparison
    (certificate : NUTSLeafEnergyCertificate) :
    SeparatedComparisonCertificate where
  computedLeft := certificate.computedLogSlice
  idealLeft := certificate.idealLogSlice
  computedRight := certificate.computedContinuationThreshold
  idealRight := certificate.idealMaxEnergyError - certificate.idealEnergy
  leftError := certificate.logSliceError
  rightError := certificate.continuationThresholdRoundingError +
    (certificate.maxEnergyErrorError + certificate.energyError)
  leftBound := certificate.logSliceBound
  rightBound := certificate.continuationThresholdRoundingBound.compose
    (certificate.maxEnergyErrorBound.sub certificate.energyBound)
  separated := certificate.continuesSeparated

noncomputable def NUTSLeafEnergyCertificate.computedEligible
    (certificate : NUTSLeafEnergyCertificate) : Bool :=
  certificate.eligibleComparison.computedLess

noncomputable def NUTSLeafEnergyCertificate.idealEligible
    (certificate : NUTSLeafEnergyCertificate) : Bool :=
  certificate.eligibleComparison.idealLess

noncomputable def NUTSLeafEnergyCertificate.computedContinues
    (certificate : NUTSLeafEnergyCertificate) : Bool :=
  certificate.continuesComparison.computedLess

noncomputable def NUTSLeafEnergyCertificate.idealContinues
    (certificate : NUTSLeafEnergyCertificate) : Bool :=
  certificate.continuesComparison.idealLess

theorem NUTSLeafEnergyCertificate.computedEligible_eq_idealEligible
    (certificate : NUTSLeafEnergyCertificate) :
    certificate.computedEligible = certificate.idealEligible :=
  certificate.eligibleComparison.computedLess_eq_idealLess

theorem NUTSLeafEnergyCertificate.computedContinues_eq_idealContinues
    (certificate : NUTSLeafEnergyCertificate) :
    certificate.computedContinues = certificate.idealContinues :=
  certificate.continuesComparison.computedLess_eq_idealLess

/-! ### Compositional vector endpoint bounds -/

/-- One certified leapfrog endpoint reindexed onto a caller-declared common
phase dimension. The existing list-level endpoint certificate remains the
source of every coordinate bound. -/
structure CertifiedLeapfrogPhaseEndpoint (dimension : ℕ) where
  step : LeapfrogStepCertificate
  positionLength : step.computedPosition.length = dimension
  momentumLength : step.computedMomentum.length = dimension

/-- A finite phase trajectory whose every stored endpoint carries the
existing leapfrog position/momentum error certificate on one common dimension. -/
structure CertifiedLeapfrogPhaseTrajectory (count dimension : ℕ) where
  endpoint : Fin count → CertifiedLeapfrogPhaseEndpoint dimension

/-- Exact endpoint constructor, useful for the ideal interpreter and for
regression examples. -/
noncomputable def CertifiedLeapfrogPhaseEndpoint.exact
    {dimension : ℕ} (position momentum : List ℝ)
    (hposition : position.length = dimension)
    (hmomentum : momentum.length = dimension) :
    CertifiedLeapfrogPhaseEndpoint dimension where
  step := {
    computedPosition := position
    idealPosition := position
    computedMomentum := momentum
    idealMomentum := momentum
    positionError := 0
    momentumError := 0
    position_bound := VectorApproximates.refl position
    momentum_bound := VectorApproximates.refl momentum }
  positionLength := hposition
  momentumLength := hmomentum

/-- Convert a recurrence-certified stored leapfrog trajectory into the common
phase-array interface consumed by dynamic-tree decision certificates. -/
noncomputable def CertifiedLeapfrogPhaseTrajectory.ofErrorCertificate
    {model : LeapfrogErrorModel} {initialPositionError initialMomentumError : ℝ}
    {steps dimension : ℕ}
    (certificate : LeapfrogTrajectoryErrorCertificate model
      initialPositionError initialMomentumError steps)
    (positionLength : ∀ index,
      (certificate.endpoint index).computedPosition.length = dimension)
    (momentumLength : ∀ index,
      (certificate.endpoint index).computedMomentum.length = dimension) :
    CertifiedLeapfrogPhaseTrajectory (steps + 1) dimension where
  endpoint index := {
    step := certificate.scheduledEndpoint index
    positionLength := positionLength index
    momentumLength := momentumLength index }

/-- Direct path from primitive vector-step witnesses through the concrete
recurrence into the phase trajectory consumed by NUTS certificates. -/
noncomputable def CertifiedLeapfrogPhaseTrajectory.ofPrimitiveCertificate
    {parameters : EuclideanLeapfrogErrorParameters} {dimension steps : ℕ}
    {initialPositionError initialMomentumError : ℝ}
    (certificate : EuclideanLeapfrogVectorTrajectoryCertificate parameters
      dimension steps initialPositionError initialMomentumError)
    (initialPositionLength : certificate.initial.computedPosition.length = dimension)
    (initialMomentumLength : certificate.initial.computedMomentum.length = dimension) :
    CertifiedLeapfrogPhaseTrajectory (steps + 1) dimension :=
  CertifiedLeapfrogPhaseTrajectory.ofErrorCertificate
    certificate.toErrorCertificate
    (fun index => Fin.cases initialPositionLength (fun _ => by
      simp [EuclideanLeapfrogVectorTrajectoryCertificate.toErrorCertificate,
        EuclideanLeapfrogVectorCertificate.toStepCertificate]) index)
    (fun index => Fin.cases initialMomentumLength (fun _ => by
      simp [EuclideanLeapfrogVectorTrajectoryCertificate.toErrorCertificate,
        EuclideanLeapfrogVectorCertificate.toStepCertificate]) index)

/-- A sequentially linked primitive trajectory feeds the same dynamic-tree
phase interface while retaining its state-threading proof for clients that
need to audit that successive primitive records form one trajectory. -/
noncomputable def CertifiedLeapfrogPhaseTrajectory.ofLinkedPrimitiveCertificate
    {parameters : EuclideanLeapfrogErrorParameters} {dimension steps : ℕ}
    {initialPositionError initialMomentumError : ℝ}
    (certificate : LinkedEuclideanLeapfrogVectorTrajectoryCertificate parameters
      dimension steps initialPositionError initialMomentumError)
    (initialPositionLength :
      certificate.errorCertificate.initial.computedPosition.length = dimension)
    (initialMomentumLength :
      certificate.errorCertificate.initial.computedMomentum.length = dimension) :
    CertifiedLeapfrogPhaseTrajectory (steps + 1) dimension :=
  CertifiedLeapfrogPhaseTrajectory.ofPrimitiveCertificate
    certificate.errorCertificate initialPositionLength initialMomentumLength

noncomputable def CertifiedLeapfrogPhaseEndpoint.computedPosition
    {dimension : ℕ} (endpoint : CertifiedLeapfrogPhaseEndpoint dimension) :
    Fin dimension → ℝ :=
  fun i => endpoint.step.computedPosition[i.val]'(by
    simp [endpoint.positionLength])

noncomputable def CertifiedLeapfrogPhaseEndpoint.idealPosition
    {dimension : ℕ} (endpoint : CertifiedLeapfrogPhaseEndpoint dimension) :
    Fin dimension → ℝ :=
  fun i => endpoint.step.idealPosition[i.val]'(by
    rw [← endpoint.step.position_bound.1, endpoint.positionLength]
    exact i.isLt)

noncomputable def CertifiedLeapfrogPhaseEndpoint.computedMomentum
    {dimension : ℕ} (endpoint : CertifiedLeapfrogPhaseEndpoint dimension) :
    Fin dimension → ℝ :=
  fun i => endpoint.step.computedMomentum[i.val]'(by
    simp [endpoint.momentumLength])

noncomputable def CertifiedLeapfrogPhaseEndpoint.idealMomentum
    {dimension : ℕ} (endpoint : CertifiedLeapfrogPhaseEndpoint dimension) :
    Fin dimension → ℝ :=
  fun i => endpoint.step.idealMomentum[i.val]'(by
    rw [← endpoint.step.momentum_bound.1, endpoint.momentumLength]
    exact i.isLt)

noncomputable def CertifiedLeapfrogPhaseTrajectory.computedPhase
    {count dimension : ℕ}
    (trajectory : CertifiedLeapfrogPhaseTrajectory count dimension) :
    Fin count → ((Fin dimension → ℝ) × (Fin dimension → ℝ)) :=
  fun index => ((trajectory.endpoint index).computedPosition,
    (trajectory.endpoint index).computedMomentum)

noncomputable def CertifiedLeapfrogPhaseTrajectory.idealPhase
    {count dimension : ℕ}
    (trajectory : CertifiedLeapfrogPhaseTrajectory count dimension) :
    Fin count → ((Fin dimension → ℝ) × (Fin dimension → ℝ)) :=
  fun index => ((trajectory.endpoint index).idealPosition,
    (trajectory.endpoint index).idealMomentum)

/-- The phase adapter preserves the position bound at every coordinate. -/
theorem CertifiedLeapfrogPhaseEndpoint.position_approximates
    {dimension : ℕ} (endpoint : CertifiedLeapfrogPhaseEndpoint dimension)
    (i : Fin dimension) :
    Approximates (endpoint.computedPosition i) (endpoint.idealPosition i)
      endpoint.step.positionError := by
  exact endpoint.step.position_bound.at i.val
    (by simp [endpoint.positionLength])
    (by rw [← endpoint.step.position_bound.1, endpoint.positionLength]; exact i.isLt)

/-- The phase adapter preserves the momentum bound at every coordinate. -/
theorem CertifiedLeapfrogPhaseEndpoint.momentum_approximates
    {dimension : ℕ} (endpoint : CertifiedLeapfrogPhaseEndpoint dimension)
    (i : Fin dimension) :
    Approximates (endpoint.computedMomentum i) (endpoint.idealMomentum i)
      endpoint.step.momentumError := by
  exact endpoint.step.momentum_bound.at i.val
    (by simp [endpoint.momentumLength])
    (by rw [← endpoint.step.momentum_bound.1, endpoint.momentumLength]; exact i.isLt)

/-- Endpoint dot product used by the Euclidean vector U-turn test. -/
noncomputable def endpointDot {ι : Type*} [Fintype ι]
    (leftPosition rightPosition momentum : ι → ℝ) : ℝ :=
  ∑ i, (rightPosition i - leftPosition i) * momentum i

/-- Error budget obtained by composing coordinatewise position and momentum
bounds through subtraction, multiplication, and finite summation. -/
noncomputable def endpointDotError {ι : Type*} [Fintype ι]
    (idealLeftPosition idealRightPosition computedMomentum : ι → ℝ)
    (leftPositionError rightPositionError momentumError : ι → ℝ) : ℝ :=
  ∑ i, ((rightPositionError i + leftPositionError i) *
      |computedMomentum i| +
    |idealRightPosition i - idealLeftPosition i| * momentumError i)

/-- Componentwise phase-point bounds imply the declared endpoint dot-product
bound. No opaque scalar error premise is needed. -/
theorem endpointDot_approximates
    {ι : Type*} [Fintype ι]
    (computedLeftPosition idealLeftPosition
      computedRightPosition idealRightPosition
      computedMomentum idealMomentum : ι → ℝ)
    (leftPositionError rightPositionError momentumError : ι → ℝ)
    (hleftPosition : ∀ i, Approximates (computedLeftPosition i)
      (idealLeftPosition i) (leftPositionError i))
    (hrightPosition : ∀ i, Approximates (computedRightPosition i)
      (idealRightPosition i) (rightPositionError i))
    (hmomentum : ∀ i, Approximates (computedMomentum i)
      (idealMomentum i) (momentumError i)) :
    Approximates
      (endpointDot computedLeftPosition computedRightPosition computedMomentum)
      (endpointDot idealLeftPosition idealRightPosition idealMomentum)
      (endpointDotError idealLeftPosition idealRightPosition computedMomentum
        leftPositionError rightPositionError momentumError) := by
  classical
  simpa [endpointDot, endpointDotError] using
    (Approximates.sum Finset.univ
      (fun i => (computedRightPosition i - computedLeftPosition i) *
        computedMomentum i)
      (fun i => (idealRightPosition i - idealLeftPosition i) * idealMomentum i)
      (fun i => (rightPositionError i + leftPositionError i) *
          |computedMomentum i| +
        |idealRightPosition i - idealLeftPosition i| * momentumError i)
      (fun i _ =>
        (hrightPosition i).sub (hleftPosition i) |>.mul (hmomentum i)))

/-- An explicitly bounded final floating-point reduction may be composed with
the componentwise endpoint bound. -/
theorem roundedEndpointDot_approximates
    {ι : Type*} [Fintype ι]
    (roundedComputed : ℝ)
    (computedLeftPosition idealLeftPosition
      computedRightPosition idealRightPosition
      computedMomentum idealMomentum : ι → ℝ)
    (leftPositionError rightPositionError momentumError : ι → ℝ)
    (roundingError : ℝ)
    (hrounding : Approximates roundedComputed
      (endpointDot computedLeftPosition computedRightPosition computedMomentum)
      roundingError)
    (hleftPosition : ∀ i, Approximates (computedLeftPosition i)
      (idealLeftPosition i) (leftPositionError i))
    (hrightPosition : ∀ i, Approximates (computedRightPosition i)
      (idealRightPosition i) (rightPositionError i))
    (hmomentum : ∀ i, Approximates (computedMomentum i)
      (idealMomentum i) (momentumError i)) :
    Approximates roundedComputed
      (endpointDot idealLeftPosition idealRightPosition idealMomentum)
      (roundingError + endpointDotError idealLeftPosition idealRightPosition
        computedMomentum leftPositionError rightPositionError momentumError) :=
  hrounding.compose (endpointDot_approximates computedLeftPosition
    idealLeftPosition computedRightPosition idealRightPosition computedMomentum
    idealMomentum leftPositionError rightPositionError momentumError
    hleftPosition hrightPosition hmomentum)

/-- Complete phase-endpoint evidence for the two dot products in a vector
U-turn decision. The separation fields are the only discontinuous premises. -/
structure VectorUTurnDecisionCertificate (ι : Type*) [Fintype ι] where
  computedLeftPosition : ι → ℝ
  idealLeftPosition : ι → ℝ
  computedRightPosition : ι → ℝ
  idealRightPosition : ι → ℝ
  computedLeftMomentum : ι → ℝ
  idealLeftMomentum : ι → ℝ
  computedRightMomentum : ι → ℝ
  idealRightMomentum : ι → ℝ
  leftPositionError : ι → ℝ
  rightPositionError : ι → ℝ
  leftMomentumError : ι → ℝ
  rightMomentumError : ι → ℝ
  leftPositionBound : ∀ i, Approximates (computedLeftPosition i)
    (idealLeftPosition i) (leftPositionError i)
  rightPositionBound : ∀ i, Approximates (computedRightPosition i)
    (idealRightPosition i) (rightPositionError i)
  leftMomentumBound : ∀ i, Approximates (computedLeftMomentum i)
    (idealLeftMomentum i) (leftMomentumError i)
  rightMomentumBound : ∀ i, Approximates (computedRightMomentum i)
    (idealRightMomentum i) (rightMomentumError i)
  leftSeparated :
    let computed := endpointDot computedLeftPosition computedRightPosition
      computedLeftMomentum
    let error := endpointDotError idealLeftPosition idealRightPosition
      computedLeftMomentum leftPositionError rightPositionError leftMomentumError
    computed < -error ∨ error < computed
  rightSeparated :
    let computed := endpointDot computedLeftPosition computedRightPosition
      computedRightMomentum
    let error := endpointDotError idealLeftPosition idealRightPosition
      computedRightMomentum leftPositionError rightPositionError rightMomentumError
    computed < -error ∨ error < computed

/-- Two existing leapfrog endpoint certificates supply every continuous
field of a vector U-turn certificate; only strict decision separation remains
for the caller to prove. -/
noncomputable def CertifiedLeapfrogPhaseEndpoint.vectorUTurnCertificate
    {dimension : ℕ}
    (left right : CertifiedLeapfrogPhaseEndpoint dimension)
    (leftSeparated :
      let computed := endpointDot left.computedPosition right.computedPosition
        left.computedMomentum
      let error := endpointDotError left.idealPosition right.idealPosition
        left.computedMomentum (fun _ => left.step.positionError)
        (fun _ => right.step.positionError) (fun _ => left.step.momentumError)
      computed < -error ∨ error < computed)
    (rightSeparated :
      let computed := endpointDot left.computedPosition right.computedPosition
        right.computedMomentum
      let error := endpointDotError left.idealPosition right.idealPosition
        right.computedMomentum (fun _ => left.step.positionError)
        (fun _ => right.step.positionError) (fun _ => right.step.momentumError)
      computed < -error ∨ error < computed) :
    VectorUTurnDecisionCertificate (Fin dimension) where
  computedLeftPosition := left.computedPosition
  idealLeftPosition := left.idealPosition
  computedRightPosition := right.computedPosition
  idealRightPosition := right.idealPosition
  computedLeftMomentum := left.computedMomentum
  idealLeftMomentum := left.idealMomentum
  computedRightMomentum := right.computedMomentum
  idealRightMomentum := right.idealMomentum
  leftPositionError := fun _ => left.step.positionError
  rightPositionError := fun _ => right.step.positionError
  leftMomentumError := fun _ => left.step.momentumError
  rightMomentumError := fun _ => right.step.momentumError
  leftPositionBound := left.position_approximates
  rightPositionBound := right.position_approximates
  leftMomentumBound := left.momentum_approximates
  rightMomentumBound := right.momentum_approximates
  leftSeparated := leftSeparated
  rightSeparated := rightSeparated

/-- Pair of certified endpoint dot products used by the vector U-turn rule. -/
structure UTurnDecisionCertificate where
  leftMomentum : SeparatedZeroCertificate
  rightMomentum : SeparatedZeroCertificate

noncomputable def UTurnDecisionCertificate.computedTurns
    (certificate : UTurnDecisionCertificate) : Bool :=
  certificate.leftMomentum.computedNegative ||
    certificate.rightMomentum.computedNegative

noncomputable def UTurnDecisionCertificate.idealTurns
    (certificate : UTurnDecisionCertificate) : Bool :=
  certificate.leftMomentum.idealNegative ||
    certificate.rightMomentum.idealNegative

/-- Both endpoint sign certificates compose into the exact ideal U-turn bit. -/
theorem UTurnDecisionCertificate.computedTurns_eq_idealTurns
    (certificate : UTurnDecisionCertificate) :
    certificate.computedTurns = certificate.idealTurns := by
  simp only [UTurnDecisionCertificate.computedTurns,
    UTurnDecisionCertificate.idealTurns,
    certificate.leftMomentum.computedNegative_eq_idealNegative,
    certificate.rightMomentum.computedNegative_eq_idealNegative]

/-- Derive the scalar U-turn certificate from componentwise endpoint bounds,
making its exact Boolean agreement theorem available automatically. -/
noncomputable def VectorUTurnDecisionCertificate.toUTurnDecisionCertificate
    {ι : Type*} [Fintype ι]
    (certificate : VectorUTurnDecisionCertificate ι) :
    UTurnDecisionCertificate where
  leftMomentum := {
    computed := endpointDot certificate.computedLeftPosition
      certificate.computedRightPosition certificate.computedLeftMomentum
    ideal := endpointDot certificate.idealLeftPosition
      certificate.idealRightPosition certificate.idealLeftMomentum
    error := endpointDotError certificate.idealLeftPosition
      certificate.idealRightPosition certificate.computedLeftMomentum
      certificate.leftPositionError certificate.rightPositionError
      certificate.leftMomentumError
    bound := endpointDot_approximates certificate.computedLeftPosition
      certificate.idealLeftPosition certificate.computedRightPosition
      certificate.idealRightPosition certificate.computedLeftMomentum
      certificate.idealLeftMomentum certificate.leftPositionError
      certificate.rightPositionError certificate.leftMomentumError
      certificate.leftPositionBound certificate.rightPositionBound
      certificate.leftMomentumBound
    separated := certificate.leftSeparated }
  rightMomentum := {
    computed := endpointDot certificate.computedLeftPosition
      certificate.computedRightPosition certificate.computedRightMomentum
    ideal := endpointDot certificate.idealLeftPosition
      certificate.idealRightPosition certificate.idealRightMomentum
    error := endpointDotError certificate.idealLeftPosition
      certificate.idealRightPosition certificate.computedRightMomentum
      certificate.leftPositionError certificate.rightPositionError
      certificate.rightMomentumError
    bound := endpointDot_approximates certificate.computedLeftPosition
      certificate.idealLeftPosition certificate.computedRightPosition
      certificate.idealRightPosition certificate.computedRightMomentum
      certificate.idealRightMomentum certificate.leftPositionError
      certificate.rightPositionError certificate.rightMomentumError
      certificate.leftPositionBound certificate.rightPositionBound
      certificate.rightMomentumBound
    separated := certificate.rightSeparated }

/-- The scalar certificate's computed bit is definitionally the vector
U-turn predicate on the adapted computed phase endpoints. -/
theorem VectorUTurnDecisionCertificate.computedTurns_eq_vectorAdjacentUTurn
    {ι : Type*} [Fintype ι]
    (certificate : VectorUTurnDecisionCertificate ι) :
    certificate.toUTurnDecisionCertificate.computedTurns =
      vectorAdjacentUTurn
        (certificate.computedLeftPosition, certificate.computedLeftMomentum)
        (certificate.computedRightPosition, certificate.computedRightMomentum) := by
  simp [VectorUTurnDecisionCertificate.toUTurnDecisionCertificate,
    UTurnDecisionCertificate.computedTurns,
    SeparatedZeroCertificate.computedNegative, vectorAdjacentUTurn, endpointDot]
  rfl

/-- Likewise the certificate's ideal bit is the exact ideal vector U-turn
predicate used by `CompletedTreeStoppingData`. -/
theorem VectorUTurnDecisionCertificate.idealTurns_eq_vectorAdjacentUTurn
    {ι : Type*} [Fintype ι]
    (certificate : VectorUTurnDecisionCertificate ι) :
    certificate.toUTurnDecisionCertificate.idealTurns =
      vectorAdjacentUTurn
        (certificate.idealLeftPosition, certificate.idealLeftMomentum)
        (certificate.idealRightPosition, certificate.idealRightMomentum) := by
  simp [VectorUTurnDecisionCertificate.toUTurnDecisionCertificate,
    UTurnDecisionCertificate.idealTurns,
    SeparatedZeroCertificate.idealNegative, vectorAdjacentUTurn, endpointDot]
  rfl

/-- Therefore a separated componentwise endpoint certificate proves the
computed U-turn callback agrees with the exact ideal callback. -/
theorem VectorUTurnDecisionCertificate.vectorAdjacentUTurn_eq
    {ι : Type*} [Fintype ι]
    (certificate : VectorUTurnDecisionCertificate ι) :
    vectorAdjacentUTurn
        (certificate.computedLeftPosition, certificate.computedLeftMomentum)
        (certificate.computedRightPosition, certificate.computedRightMomentum) =
      vectorAdjacentUTurn
        (certificate.idealLeftPosition, certificate.idealLeftMomentum)
        (certificate.idealRightPosition, certificate.idealRightMomentum) := by
  rw [← certificate.computedTurns_eq_vectorAdjacentUTurn,
    ← certificate.idealTurns_eq_vectorAdjacentUTurn]
  exact certificate.toUTurnDecisionCertificate.computedTurns_eq_idealTurns

/-- Tree-local certificate proposition: only decisions actually visited by
this completed recursive tree need witnesses. -/
def RecursivePhaseTree.DecisionsAgree
    {Phase : Type*}
    (computedLeaf idealLeaf : Phase → Bool)
    (computedTurns idealTurns : Phase → Phase → Bool) :
    RecursivePhaseTree Phase → Prop
  | .leaf phase => computedLeaf phase = idealLeaf phase
  | .node left right =>
      DecisionsAgree computedLeaf idealLeaf computedTurns idealTurns left ∧
        DecisionsAgree computedLeaf idealLeaf computedTurns idealTurns right ∧
        computedTurns left.leftmost right.rightmost =
          idealTurns left.leftmost right.rightmost

/-- Leaf-energy and endpoint U-turn certificates automatically establish the
tree-local decision agreement consumed by the recursive flag theorem. -/
theorem RecursivePhaseTree.decisionsAgree_of_certificates
    {Phase : Type*}
    (leafCertificate : Phase → NUTSLeafEnergyCertificate)
    (turnCertificate : Phase → Phase → UTurnDecisionCertificate)
    (tree : RecursivePhaseTree Phase) :
    Mcmc.Executable.Continuous.RecursivePhaseTree.DecisionsAgree
      (fun phase => (leafCertificate phase).computedContinues)
      (fun phase => (leafCertificate phase).idealContinues)
      (fun left right => (turnCertificate left right).computedTurns)
      (fun left right => (turnCertificate left right).idealTurns) tree := by
  induction tree with
  | leaf phase =>
      exact (leafCertificate phase).computedContinues_eq_idealContinues
  | node left right ihLeft ihRight =>
      exact ⟨ihLeft, ihRight,
        (turnCertificate left.leftmost right.rightmost).computedTurns_eq_idealTurns⟩

/-- A tree-local collection of certified primitive decisions suffices to
reproduce the exact ideal recursive flag tree. -/
theorem RecursivePhaseTree.toBuildFlagTree_eq_of_decisionsAgree
    {Phase : Type*}
    (computedLeaf idealLeaf : Phase → Bool)
    (computedTurns idealTurns : Phase → Phase → Bool)
    (tree : RecursivePhaseTree Phase)
    (hagrees : Mcmc.Executable.Continuous.RecursivePhaseTree.DecisionsAgree
      computedLeaf idealLeaf computedTurns idealTurns tree) :
    tree.toBuildFlagTree computedLeaf computedTurns =
      tree.toBuildFlagTree idealLeaf idealTurns := by
  induction tree with
  | leaf phase =>
      simpa [RecursivePhaseTree.toBuildFlagTree,
        RecursivePhaseTree.DecisionsAgree] using hagrees
  | node left right ihLeft ihRight =>
      rcases hagrees with ⟨hleft, hright, hroot⟩
      simp [RecursivePhaseTree.toBuildFlagTree, ihLeft hleft, ihRight hright,
        hroot]

/-- Hence a completed tree whose primitive numeric decisions carry bounded
certificates has exactly the ideal recursive stopping trace. -/
theorem RecursivePhaseTree.certifiedBuildFlagTree_eq_ideal
    {Phase : Type*}
    (leafCertificate : Phase → NUTSLeafEnergyCertificate)
    (turnCertificate : Phase → Phase → UTurnDecisionCertificate)
    (tree : RecursivePhaseTree Phase) :
    tree.toBuildFlagTree
        (fun phase => (leafCertificate phase).computedContinues)
        (fun left right => (turnCertificate left right).computedTurns) =
      tree.toBuildFlagTree
        (fun phase => (leafCertificate phase).idealContinues)
        (fun left right => (turnCertificate left right).idealTurns) :=
  Mcmc.Executable.Continuous.RecursivePhaseTree.toBuildFlagTree_eq_of_decisionsAgree
    _ _ _ _ tree
      (Mcmc.Executable.Continuous.RecursivePhaseTree.decisionsAgree_of_certificates
        leafCertificate turnCertificate tree)

/-- Pointwise equality of certified leaf and endpoint decisions lifts through
the entire recursive `BuildTree` Boolean trace. -/
theorem RecursivePhaseTree.toBuildFlagTree_eq_of_decisions_eq
    {Phase : Type*}
    (computedLeaf idealLeaf : Phase → Bool)
    (computedTurns idealTurns : Phase → Phase → Bool)
    (hleaf : ∀ phase, computedLeaf phase = idealLeaf phase)
    (hturns : ∀ left right, computedTurns left right = idealTurns left right)
    (tree : RecursivePhaseTree Phase) :
    tree.toBuildFlagTree computedLeaf computedTurns =
      tree.toBuildFlagTree idealLeaf idealTurns := by
  apply Mcmc.Executable.Continuous.RecursivePhaseTree.toBuildFlagTree_eq_of_decisionsAgree
    computedLeaf idealLeaf computedTurns idealTurns tree
  induction tree with
  | leaf phase => exact hleaf phase
  | node left right ihLeft ihRight =>
      exact ⟨ihLeft, ihRight, hturns left.leftmost right.rightmost⟩

/-- Consequently the numerical and ideal recursive continuation decisions are
identical whenever every primitive Boolean decision is certified. -/
theorem RecursivePhaseTree.continues_eq_of_decisions_eq
    {Phase : Type*}
    (computedLeaf idealLeaf : Phase → Bool)
    (computedTurns idealTurns : Phase → Phase → Bool)
    (hleaf : ∀ phase, computedLeaf phase = idealLeaf phase)
    (hturns : ∀ left right, computedTurns left right = idealTurns left right)
    (tree : RecursivePhaseTree Phase) :
    (tree.toBuildFlagTree computedLeaf computedTurns).continues =
      (tree.toBuildFlagTree idealLeaf idealTurns).continues := by
  exact congrArg NUTSBuildFlagTree.continues
    (Mcmc.Executable.Continuous.RecursivePhaseTree.toBuildFlagTree_eq_of_decisions_eq
      computedLeaf idealLeaf computedTurns idealTurns hleaf hturns tree)

/-- End-to-end numerical refinement for one recursive NUTS flag tree built
from a common certified phase trajectory. Leaf-energy certificates discharge
the divergence decisions, while endpoint separation discharges every U-turn
decision actually queried by the tree. -/
theorem CertifiedLeapfrogPhaseTrajectory.certifiedBuildFlagTree_eq_ideal
    {count dimension : ℕ}
    (trajectory : CertifiedLeapfrogPhaseTrajectory count dimension)
    (leafCertificate : Fin count → NUTSLeafEnergyCertificate)
    (leftSeparated : ∀ left right,
      let leftEndpoint := trajectory.endpoint left
      let rightEndpoint := trajectory.endpoint right
      let computed := endpointDot leftEndpoint.computedPosition
        rightEndpoint.computedPosition leftEndpoint.computedMomentum
      let error := endpointDotError leftEndpoint.idealPosition
        rightEndpoint.idealPosition leftEndpoint.computedMomentum
        (fun _ => leftEndpoint.step.positionError)
        (fun _ => rightEndpoint.step.positionError)
        (fun _ => leftEndpoint.step.momentumError)
      computed < -error ∨ error < computed)
    (rightSeparated : ∀ left right,
      let leftEndpoint := trajectory.endpoint left
      let rightEndpoint := trajectory.endpoint right
      let computed := endpointDot leftEndpoint.computedPosition
        rightEndpoint.computedPosition rightEndpoint.computedMomentum
      let error := endpointDotError leftEndpoint.idealPosition
        rightEndpoint.idealPosition rightEndpoint.computedMomentum
        (fun _ => leftEndpoint.step.positionError)
        (fun _ => rightEndpoint.step.positionError)
        (fun _ => rightEndpoint.step.momentumError)
      computed < -error ∨ error < computed)
    (tree : RecursivePhaseTree (Fin count)) :
    tree.toBuildFlagTree
        (fun phase => (leafCertificate phase).computedContinues)
        (fun left right => vectorAdjacentUTurn
          (trajectory.computedPhase left) (trajectory.computedPhase right)) =
      tree.toBuildFlagTree
        (fun phase => (leafCertificate phase).idealContinues)
        (fun left right => vectorAdjacentUTurn
          (trajectory.idealPhase left) (trajectory.idealPhase right)) := by
  apply Mcmc.Executable.Continuous.RecursivePhaseTree.toBuildFlagTree_eq_of_decisions_eq
  · exact fun phase =>
      (leafCertificate phase).computedContinues_eq_idealContinues
  · intro left right
    exact ((trajectory.endpoint left).vectorUTurnCertificate
      (trajectory.endpoint right) (leftSeparated left right)
      (rightSeparated left right)).vectorAdjacentUTurn_eq

/-- Primitive recurrence witnesses, exact successive-state linkage, and
strict comparison margins compose directly into the recursive NUTS decision
refinement theorem. -/
theorem LinkedEuclideanLeapfrogVectorTrajectoryCertificate.certifiedBuildFlagTree_eq_ideal
    {parameters : EuclideanLeapfrogErrorParameters} {dimension steps : ℕ}
    {initialPositionError initialMomentumError : ℝ}
    (certificate : LinkedEuclideanLeapfrogVectorTrajectoryCertificate parameters
      dimension steps initialPositionError initialMomentumError)
    (initialPositionLength :
      certificate.errorCertificate.initial.computedPosition.length = dimension)
    (initialMomentumLength :
      certificate.errorCertificate.initial.computedMomentum.length = dimension)
    (leafCertificate : Fin (steps + 1) → NUTSLeafEnergyCertificate)
    (leftSeparated : ∀ left right,
      let trajectory := CertifiedLeapfrogPhaseTrajectory.ofLinkedPrimitiveCertificate
        certificate initialPositionLength initialMomentumLength
      let leftEndpoint := trajectory.endpoint left
      let rightEndpoint := trajectory.endpoint right
      let computed := endpointDot leftEndpoint.computedPosition
        rightEndpoint.computedPosition leftEndpoint.computedMomentum
      let error := endpointDotError leftEndpoint.idealPosition
        rightEndpoint.idealPosition leftEndpoint.computedMomentum
        (fun _ => leftEndpoint.step.positionError)
        (fun _ => rightEndpoint.step.positionError)
        (fun _ => leftEndpoint.step.momentumError)
      computed < -error ∨ error < computed)
    (rightSeparated : ∀ left right,
      let trajectory := CertifiedLeapfrogPhaseTrajectory.ofLinkedPrimitiveCertificate
        certificate initialPositionLength initialMomentumLength
      let leftEndpoint := trajectory.endpoint left
      let rightEndpoint := trajectory.endpoint right
      let computed := endpointDot leftEndpoint.computedPosition
        rightEndpoint.computedPosition rightEndpoint.computedMomentum
      let error := endpointDotError leftEndpoint.idealPosition
        rightEndpoint.idealPosition rightEndpoint.computedMomentum
        (fun _ => leftEndpoint.step.positionError)
        (fun _ => rightEndpoint.step.positionError)
        (fun _ => rightEndpoint.step.momentumError)
      computed < -error ∨ error < computed)
    (tree : RecursivePhaseTree (Fin (steps + 1))) :
    let trajectory := CertifiedLeapfrogPhaseTrajectory.ofLinkedPrimitiveCertificate
      certificate initialPositionLength initialMomentumLength
    tree.toBuildFlagTree
        (fun phase => (leafCertificate phase).computedContinues)
        (fun left right => vectorAdjacentUTurn
          (trajectory.computedPhase left) (trajectory.computedPhase right)) =
      tree.toBuildFlagTree
        (fun phase => (leafCertificate phase).idealContinues)
        (fun left right => vectorAdjacentUTurn
          (trajectory.idealPhase left) (trajectory.idealPhase right)) := by
  exact CertifiedLeapfrogPhaseTrajectory.certifiedBuildFlagTree_eq_ideal
    _ leafCertificate leftSeparated rightSeparated tree

/-- Strict endpoint margins refine every row of the executable recursive
builder: computed floating-point U-turn bits and ideal-real U-turn bits drive
identical interval expansion and early stopping for every direction trace and
root. -/
theorem CertifiedLeapfrogPhaseTrajectory.recursiveDoublingCandidateRow_eq_ideal
    {count dimension depth : ℕ}
    (trajectory : CertifiedLeapfrogPhaseTrajectory count dimension)
    (leftSeparated : ∀ left right, left ≠ right →
      let leftEndpoint := trajectory.endpoint left
      let rightEndpoint := trajectory.endpoint right
      let computed := endpointDot leftEndpoint.computedPosition
        rightEndpoint.computedPosition leftEndpoint.computedMomentum
      let error := endpointDotError leftEndpoint.idealPosition
        rightEndpoint.idealPosition leftEndpoint.computedMomentum
        (fun _ => leftEndpoint.step.positionError)
        (fun _ => rightEndpoint.step.positionError)
        (fun _ => leftEndpoint.step.momentumError)
      computed < -error ∨ error < computed)
    (rightSeparated : ∀ left right, left ≠ right →
      let leftEndpoint := trajectory.endpoint left
      let rightEndpoint := trajectory.endpoint right
      let computed := endpointDot leftEndpoint.computedPosition
        rightEndpoint.computedPosition rightEndpoint.computedMomentum
      let error := endpointDotError leftEndpoint.idealPosition
        rightEndpoint.idealPosition rightEndpoint.computedMomentum
        (fun _ => leftEndpoint.step.positionError)
        (fun _ => rightEndpoint.step.positionError)
        (fun _ => rightEndpoint.step.momentumError)
      computed < -error ∨ error < computed)
    (trace : Fin depth → Bool) (root : Fin count) :
    Mcmc.Executable.DynamicTreeIR.recursiveDoublingCandidateRow count depth
        (fun left right => vectorAdjacentUTurn
          (trajectory.computedPhase left) (trajectory.computedPhase right))
        trace root =
      Mcmc.Executable.DynamicTreeIR.recursiveDoublingCandidateRow count depth
        (fun left right => vectorAdjacentUTurn
          (trajectory.idealPhase left) (trajectory.idealPhase right))
        trace root := by
  apply Mcmc.Executable.DynamicTreeIR.recursiveDoublingCandidateRow_congr
  intro left right
  by_cases heq : left = right
  · subst right
    simp [vectorAdjacentUTurn,
      CertifiedLeapfrogPhaseTrajectory.computedPhase,
      CertifiedLeapfrogPhaseTrajectory.idealPhase]
  · exact ((trajectory.endpoint left).vectorUTurnCertificate
      (trajectory.endpoint right) (leftSeparated left right heq)
      (rightSeparated left right heq)).vectorAdjacentUTurn_eq

/-- The same strict endpoint margins identify the full computed randomized
checked recursion with its ideal-real kernel. This includes fair direction
traces, recursive early stopping, the global reroot check, endpoint selection,
and the identity fallback on a failed check. -/
theorem CertifiedLeapfrogPhaseTrajectory.recursiveDoublingKernel_eq_ideal
    {count dimension depth : ℕ}
    (trajectory : CertifiedLeapfrogPhaseTrajectory count dimension)
    (leftSeparated : ∀ left right, left ≠ right →
      let leftEndpoint := trajectory.endpoint left
      let rightEndpoint := trajectory.endpoint right
      let computed := endpointDot leftEndpoint.computedPosition
        rightEndpoint.computedPosition leftEndpoint.computedMomentum
      let error := endpointDotError leftEndpoint.idealPosition
        rightEndpoint.idealPosition leftEndpoint.computedMomentum
        (fun _ => leftEndpoint.step.positionError)
        (fun _ => rightEndpoint.step.positionError)
        (fun _ => leftEndpoint.step.momentumError)
      computed < -error ∨ error < computed)
    (rightSeparated : ∀ left right, left ≠ right →
      let leftEndpoint := trajectory.endpoint left
      let rightEndpoint := trajectory.endpoint right
      let computed := endpointDot leftEndpoint.computedPosition
        rightEndpoint.computedPosition rightEndpoint.computedMomentum
      let error := endpointDotError leftEndpoint.idealPosition
        rightEndpoint.idealPosition rightEndpoint.computedMomentum
        (fun _ => leftEndpoint.step.positionError)
        (fun _ => rightEndpoint.step.positionError)
        (fun _ => rightEndpoint.step.momentumError)
      computed < -error ∨ error < computed)
    (target : Distribution (Fin count))
    (htarget : ∀ state, 0 < target.mass state) :
    (Mcmc.Executable.DynamicTreeIR.recursiveDoublingProgram count depth
      (fun left right => vectorAdjacentUTurn
        (trajectory.computedPhase left) (trajectory.computedPhase right))).interpret
        target htarget =
      (Mcmc.Executable.DynamicTreeIR.recursiveDoublingProgram count depth
        (fun left right => vectorAdjacentUTurn
          (trajectory.idealPhase left) (trajectory.idealPhase right))).interpret
        target htarget := by
  apply Mcmc.Executable.DynamicTreeIR.recursiveDoublingProgram_interpret_eq
  intro left right
  by_cases heq : left = right
  · subst right
    simp [vectorAdjacentUTurn,
      CertifiedLeapfrogPhaseTrajectory.computedPhase,
      CertifiedLeapfrogPhaseTrajectory.idealPhase]
  · exact ((trajectory.endpoint left).vectorUTurnCertificate
      (trajectory.endpoint right) (leftSeparated left right heq)
      (rightSeparated left right heq)).vectorAdjacentUTurn_eq

/-! ### Concrete exact-margin client -/

/-- One-dimensional completed orbit with positions `0, …, count - 1` and
unit momentum. It is an exact-arithmetic client of the same phase interface
used by bounded Float64 trajectories. -/
noncomputable def exactUnitMomentumLineTrajectory (count : ℕ) :
    CertifiedLeapfrogPhaseTrajectory count 1 where
  endpoint index := CertifiedLeapfrogPhaseEndpoint.exact
    [(index.val : ℝ)] [1] (by simp) (by simp)

/-- Every pair of distinct leaves in the exact unit-momentum line has a
strictly separated U-turn dot product. The error budget is exactly zero. -/
theorem exactUnitMomentumLineTrajectory_separated
    (count : ℕ) (left right : Fin count) (hne : left ≠ right) :
    let trajectory := exactUnitMomentumLineTrajectory count
    let leftEndpoint := trajectory.endpoint left
    let rightEndpoint := trajectory.endpoint right
    let computed := endpointDot leftEndpoint.computedPosition
      rightEndpoint.computedPosition leftEndpoint.computedMomentum
    let error := endpointDotError leftEndpoint.idealPosition
      rightEndpoint.idealPosition leftEndpoint.computedMomentum
      (fun _ => leftEndpoint.step.positionError)
      (fun _ => rightEndpoint.step.positionError)
      (fun _ => leftEndpoint.step.momentumError)
    computed < -error ∨ error < computed := by
  simp [exactUnitMomentumLineTrajectory,
    CertifiedLeapfrogPhaseEndpoint.exact,
    CertifiedLeapfrogPhaseEndpoint.computedPosition,
    CertifiedLeapfrogPhaseEndpoint.idealPosition,
    CertifiedLeapfrogPhaseEndpoint.computedMomentum,
    endpointDot, endpointDotError]
  exact hne.symm

/-- The exact line client discharges all numerical U-turn premises of the
full randomized checked recursion. This is a non-vacuous positive-depth
instantiation; finite-precision clients replace the zero errors by their
certified recurrence budgets and prove the same strict margins. -/
theorem exactUnitMomentumLine_recursiveDoublingKernel_eq_ideal
    (count depth : ℕ) (target : Distribution (Fin count))
    (htarget : ∀ state, 0 < target.mass state) :
    (Mcmc.Executable.DynamicTreeIR.recursiveDoublingProgram count depth
      (fun left right => vectorAdjacentUTurn
        ((exactUnitMomentumLineTrajectory count).computedPhase left)
        ((exactUnitMomentumLineTrajectory count).computedPhase right))).interpret
          target htarget =
      (Mcmc.Executable.DynamicTreeIR.recursiveDoublingProgram count depth
        (fun left right => vectorAdjacentUTurn
          ((exactUnitMomentumLineTrajectory count).idealPhase left)
          ((exactUnitMomentumLineTrajectory count).idealPhase right))).interpret
            target htarget := by
  apply (exactUnitMomentumLineTrajectory count).recursiveDoublingKernel_eq_ideal
  · exact exactUnitMomentumLineTrajectory_separated count
  · exact exactUnitMomentumLineTrajectory_separated count

/-- A four-leaf client with a deliberately nonzero `1/10` coordinate-error
budget. Computed and ideal values coincide here so the example isolates the
margin arithmetic: the theorem below verifies that this positive budget is
still small enough for every distinct endpoint comparison. -/
noncomputable def tenthErrorFourLeafTrajectory :
    CertifiedLeapfrogPhaseTrajectory 4 1 where
  endpoint index := {
    step := {
      computedPosition := [(index.val : ℝ)]
      idealPosition := [(index.val : ℝ)]
      computedMomentum := [1]
      idealMomentum := [1]
      positionError := 1 / 10
      momentumError := 1 / 10
      position_bound := (VectorApproximates.refl _).mono (by norm_num)
      momentum_bound := (VectorApproximates.refl _).mono (by norm_num) }
    positionLength := by simp
    momentumLength := by simp }

/-- The positive tenth-unit endpoint budgets remain strictly separated on
all distinct leaves of the four-state orbit. -/
theorem tenthErrorFourLeafTrajectory_separated
    (left right : Fin 4) (hne : left ≠ right) :
    let trajectory := tenthErrorFourLeafTrajectory
    let leftEndpoint := trajectory.endpoint left
    let rightEndpoint := trajectory.endpoint right
    let computed := endpointDot leftEndpoint.computedPosition
      rightEndpoint.computedPosition leftEndpoint.computedMomentum
    let error := endpointDotError leftEndpoint.idealPosition
      rightEndpoint.idealPosition leftEndpoint.computedMomentum
      (fun _ => leftEndpoint.step.positionError)
      (fun _ => rightEndpoint.step.positionError)
      (fun _ => leftEndpoint.step.momentumError)
    computed < -error ∨ error < computed := by
  fin_cases left <;> fin_cases right <;>
    simp_all [tenthErrorFourLeafTrajectory,
      CertifiedLeapfrogPhaseEndpoint.computedPosition,
      CertifiedLeapfrogPhaseEndpoint.idealPosition,
      CertifiedLeapfrogPhaseEndpoint.computedMomentum,
      endpointDot, endpointDotError] <;> norm_num

/-- A concrete nonzero-error budget therefore refines the entire randomized
checked recursive kernel, not just one scalar U-turn comparison. -/
theorem tenthErrorFourLeaf_recursiveDoublingKernel_eq_ideal
    (depth : ℕ) (target : Distribution (Fin 4))
    (htarget : ∀ state, 0 < target.mass state) :
    (Mcmc.Executable.DynamicTreeIR.recursiveDoublingProgram 4 depth
      (fun left right => vectorAdjacentUTurn
        (tenthErrorFourLeafTrajectory.computedPhase left)
        (tenthErrorFourLeafTrajectory.computedPhase right))).interpret
          target htarget =
      (Mcmc.Executable.DynamicTreeIR.recursiveDoublingProgram 4 depth
        (fun left right => vectorAdjacentUTurn
          (tenthErrorFourLeafTrajectory.idealPhase left)
          (tenthErrorFourLeafTrajectory.idealPhase right))).interpret
            target htarget := by
  apply tenthErrorFourLeafTrajectory.recursiveDoublingKernel_eq_ideal
  · exact tenthErrorFourLeafTrajectory_separated
  · exact tenthErrorFourLeafTrajectory_separated

/-- The first four exact-dyadic Gaussian leapfrog endpoints used by the Julia
platform regression (`ε = 1/2`, starting from `(q,p) = (0,1)`). -/
noncomputable def exactGaussianDyadicFourLeafTrajectory :
    CertifiedLeapfrogPhaseTrajectory 4 1 where
  endpoint index :=
    let position : Fin 4 → ℝ := ![0, 1 / 2, 7 / 8, 33 / 32]
    let momentum : Fin 4 → ℝ := ![1, 7 / 8, 17 / 32, 7 / 128]
    CertifiedLeapfrogPhaseEndpoint.exact [position index] [momentum index]
      (by simp) (by simp)

/-- Every distinct endpoint comparison in the concrete exact-dyadic Gaussian
trajectory has a nonzero dot-product margin. -/
theorem exactGaussianDyadicFourLeafTrajectory_separated
    (left right : Fin 4) (hne : left ≠ right) :
    let trajectory := exactGaussianDyadicFourLeafTrajectory
    let leftEndpoint := trajectory.endpoint left
    let rightEndpoint := trajectory.endpoint right
    let computed := endpointDot leftEndpoint.computedPosition
      rightEndpoint.computedPosition leftEndpoint.computedMomentum
    let error := endpointDotError leftEndpoint.idealPosition
      rightEndpoint.idealPosition leftEndpoint.computedMomentum
      (fun _ => leftEndpoint.step.positionError)
      (fun _ => rightEndpoint.step.positionError)
      (fun _ => leftEndpoint.step.momentumError)
    computed < -error ∨ error < computed := by
  fin_cases left <;> fin_cases right <;>
    simp_all [exactGaussianDyadicFourLeafTrajectory,
      CertifiedLeapfrogPhaseEndpoint.exact,
      CertifiedLeapfrogPhaseEndpoint.computedPosition,
      CertifiedLeapfrogPhaseEndpoint.idealPosition,
      CertifiedLeapfrogPhaseEndpoint.computedMomentum,
      endpointDot, endpointDotError] <;> norm_num

theorem exactGaussianDyadicFourLeafTrajectory_rightSeparated
    (left right : Fin 4) (hne : left ≠ right) :
    let trajectory := exactGaussianDyadicFourLeafTrajectory
    let leftEndpoint := trajectory.endpoint left
    let rightEndpoint := trajectory.endpoint right
    let computed := endpointDot leftEndpoint.computedPosition
      rightEndpoint.computedPosition rightEndpoint.computedMomentum
    let error := endpointDotError leftEndpoint.idealPosition
      rightEndpoint.idealPosition rightEndpoint.computedMomentum
      (fun _ => leftEndpoint.step.positionError)
      (fun _ => rightEndpoint.step.positionError)
      (fun _ => rightEndpoint.step.momentumError)
    computed < -error ∨ error < computed := by
  fin_cases left <;> fin_cases right <;>
    simp_all [exactGaussianDyadicFourLeafTrajectory,
      CertifiedLeapfrogPhaseEndpoint.exact,
      CertifiedLeapfrogPhaseEndpoint.computedPosition,
      CertifiedLeapfrogPhaseEndpoint.idealPosition,
      CertifiedLeapfrogPhaseEndpoint.computedMomentum,
      endpointDot, endpointDotError] <;> norm_num

/-- The concrete dyadic Gaussian phase array refines the full checked
recursive kernel at every requested tree depth. Together with the exact-
rational oracle records, this supplies a platform-backed nontrivial client of
the generic numerical boundary. -/
theorem exactGaussianDyadicFourLeaf_recursiveDoublingKernel_eq_ideal
    (depth : ℕ) (target : Distribution (Fin 4))
    (htarget : ∀ state, 0 < target.mass state) :
    (Mcmc.Executable.DynamicTreeIR.recursiveDoublingProgram 4 depth
      (fun left right => vectorAdjacentUTurn
        (exactGaussianDyadicFourLeafTrajectory.computedPhase left)
        (exactGaussianDyadicFourLeafTrajectory.computedPhase right))).interpret
          target htarget =
      (Mcmc.Executable.DynamicTreeIR.recursiveDoublingProgram 4 depth
        (fun left right => vectorAdjacentUTurn
          (exactGaussianDyadicFourLeafTrajectory.idealPhase left)
          (exactGaussianDyadicFourLeafTrajectory.idealPhase right))).interpret
            target htarget := by
  apply exactGaussianDyadicFourLeafTrajectory.recursiveDoublingKernel_eq_ideal
  · exact exactGaussianDyadicFourLeafTrajectory_separated
  · exact exactGaussianDyadicFourLeafTrajectory_rightSeparated

/-! ### Concrete rounded Float64 Gaussian client -/

/-- The first four Gaussian leapfrog endpoints produced by Julia Float64 with
`ε = 0.1`, starting from `(q,p) = (0,1)`, paired with the exact rational-real
leapfrog orbit. The binary Float64 values are embedded as their exact dyadic
rationals; `10⁻¹⁴` is a checked positive coordinate budget rather than an
assumed equality. -/
noncomputable def roundedGaussianTenthFourLeafTrajectory :
    CertifiedLeapfrogPhaseTrajectory 4 1 where
  endpoint index :=
    let computedPosition : Fin 4 → ℝ := ![
      0,
      3602879701896397 / 36028797018963968,
      3584865303386915 / 18014398509481984,
      2666221051395881 / 9007199254740992]
    let idealPosition : Fin 4 → ℝ := ![0, 1 / 10, 199 / 1000, 29601 / 100000]
    let computedMomentum : Fin 4 → ℝ := ![
      1,
      8962163258467287 / 9007199254740992,
      8827505629608909 / 9007199254740992,
      4302286472227221 / 4503599627370496]
    let idealMomentum : Fin 4 → ℝ := ![
      1, 199 / 200, 19601 / 20000, 1910599 / 2000000]
    { step := {
        computedPosition := [computedPosition index]
        idealPosition := [idealPosition index]
        computedMomentum := [computedMomentum index]
        idealMomentum := [idealMomentum index]
        positionError := 1 / 100000000000000
        momentumError := 1 / 100000000000000
        position_bound := VectorApproximates.singleton (by
          fin_cases index <;>
            norm_num [Approximates, computedPosition, idealPosition])
        momentum_bound := VectorApproximates.singleton (by
          fin_cases index <;>
            norm_num [Approximates, computedMomentum, idealMomentum]) }
      positionLength := by simp
      momentumLength := by simp }

/-- Every distinct left-momentum U-turn comparison for the actual rounded
four-leaf orbit remains outside its propagated uncertainty interval. -/
theorem roundedGaussianTenthFourLeafTrajectory_leftSeparated
    (left right : Fin 4) (hne : left ≠ right) :
    let trajectory := roundedGaussianTenthFourLeafTrajectory
    let leftEndpoint := trajectory.endpoint left
    let rightEndpoint := trajectory.endpoint right
    let computed := endpointDot leftEndpoint.computedPosition
      rightEndpoint.computedPosition leftEndpoint.computedMomentum
    let error := endpointDotError leftEndpoint.idealPosition
      rightEndpoint.idealPosition leftEndpoint.computedMomentum
      (fun _ => leftEndpoint.step.positionError)
      (fun _ => rightEndpoint.step.positionError)
      (fun _ => leftEndpoint.step.momentumError)
    computed < -error ∨ error < computed := by
  fin_cases left <;> fin_cases right <;>
    simp_all [roundedGaussianTenthFourLeafTrajectory,
      CertifiedLeapfrogPhaseEndpoint.computedPosition,
      CertifiedLeapfrogPhaseEndpoint.idealPosition,
      CertifiedLeapfrogPhaseEndpoint.computedMomentum,
      endpointDot, endpointDotError] <;> norm_num

/-- The corresponding right-momentum comparisons are separated as well. -/
theorem roundedGaussianTenthFourLeafTrajectory_rightSeparated
    (left right : Fin 4) (hne : left ≠ right) :
    let trajectory := roundedGaussianTenthFourLeafTrajectory
    let leftEndpoint := trajectory.endpoint left
    let rightEndpoint := trajectory.endpoint right
    let computed := endpointDot leftEndpoint.computedPosition
      rightEndpoint.computedPosition rightEndpoint.computedMomentum
    let error := endpointDotError leftEndpoint.idealPosition
      rightEndpoint.idealPosition rightEndpoint.computedMomentum
      (fun _ => leftEndpoint.step.positionError)
      (fun _ => rightEndpoint.step.positionError)
      (fun _ => rightEndpoint.step.momentumError)
    computed < -error ∨ error < computed := by
  fin_cases left <;> fin_cases right <;>
    simp_all [roundedGaussianTenthFourLeafTrajectory,
      CertifiedLeapfrogPhaseEndpoint.computedPosition,
      CertifiedLeapfrogPhaseEndpoint.idealPosition,
      CertifiedLeapfrogPhaseEndpoint.computedMomentum,
      endpointDot, endpointDotError] <;> norm_num

/-- A genuine rounded Float64 Gaussian phase array therefore refines the full
randomized checked recursive kernel at every requested depth. -/
theorem roundedGaussianTenthFourLeaf_recursiveDoublingKernel_eq_ideal
    (depth : ℕ) (target : Distribution (Fin 4))
    (htarget : ∀ state, 0 < target.mass state) :
    (Mcmc.Executable.DynamicTreeIR.recursiveDoublingProgram 4 depth
      (fun left right => vectorAdjacentUTurn
        (roundedGaussianTenthFourLeafTrajectory.computedPhase left)
        (roundedGaussianTenthFourLeafTrajectory.computedPhase right))).interpret
          target htarget =
      (Mcmc.Executable.DynamicTreeIR.recursiveDoublingProgram 4 depth
        (fun left right => vectorAdjacentUTurn
          (roundedGaussianTenthFourLeafTrajectory.idealPhase left)
          (roundedGaussianTenthFourLeafTrajectory.idealPhase right))).interpret
            target htarget := by
  apply roundedGaussianTenthFourLeafTrajectory.recursiveDoublingKernel_eq_ideal
  · exact roundedGaussianTenthFourLeafTrajectory_leftSeparated
  · exact roundedGaussianTenthFourLeafTrajectory_rightSeparated

end Mcmc.Executable.Continuous
