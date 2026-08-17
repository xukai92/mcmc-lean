import Mcmc.Executable.Continuous.BoundedHMC
import Mcmc.Finite.CertifiedDynamicTree

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

end Mcmc.Executable.Continuous
