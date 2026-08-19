import Mcmc.Executable.Finite.TwoState
import Mcmc.Executable.Finite.CompilerIRInterpreter
import Mcmc.Executable.Continuous.RestrictedCertificate
import Mcmc.Executable.Continuous.DyadicLeapfrogCertificate
import Mcmc.Executable.Continuous.SoftAbsRefinement
import Mcmc.Executable.Continuous.RelativisticCertificates
import Mcmc.Relativistic.FixedPointIteration

/-! A small compiled oracle for cross-language conformance tests. -/

open Mcmc.Executable.Finite

private def usage : String :=
  "usage: mcmc-oracle categorical ... | mh ... | sincos_interval ... | bounded_scalar_callbacks ... | bounded_scalar_solver_contraction ... | bounded_scalar_solver_phase ... | bounded_scalar_solver_endpoint ... | bounded_scalar_linked_solver_trajectory ... | bounded_scalar_step_regional ... | bounded_scalar_endpoint_energy ... | bounded_scalar_two_endpoint_energy ... | bounded_scalar_two_endpoint_weight ... | contraction_aposteriori RESIDUAL_UPPER RATE DISTANCE_UPPER | rounded_contraction_residual ITERATE COMPUTED_UPDATE UPDATE_ERROR RESIDUAL_UPPER | rounded_contraction_pair RESIDUAL_FIELDS... RATE DISTANCE_UPPER | gaussian_certificate ... | quartic_certificate ... | gaussian_dyadic_leapfrog ... | gaussian_rounded_leapfrog ... | rounded_gaussian_four_leaf Q0 P0 Q1 P1 Q2 P2 Q3 P3 | rounded_leapfrog STEP POSITION MOMENTUM CURRENT_GRADIENT HALF NEXT_POSITION NEXT_GRADIENT NEXT_MOMENTUM HALF_ERROR POSITION_ERROR MOMENTUM_ERROR | unit_zero_softabs HESSIAN EIGENVALUE SQRT FACTOR LOGDET | sqrt_interval INPUT COMPUTED ERROR | reciprocal_residual INPUT COMPUTED ERROR | sqrt_reciprocal INPUT SQRT SQRT_ERROR RECIPROCAL RECIPROCAL_ERROR | log_interval INPUT COMPUTED ERROR | exp_nonpositive INPUT COMPUTED EXP_ERROR IDEAL_INPUT INPUT_ERROR | exp_nonpositive_transport INPUT COMPUTED EXP_ERROR IDEAL_INPUT INPUT_ERROR | exp_nonpositive_transport_trajectory COUNT TRANSPORT_FIELDS... | rounded_cumulative COUNT WEIGHT BOUNDARY ERROR... | scaled_draw UNIFORM TOTAL COMPUTED ERROR | multinomial_decision DRAW COUNT UNIFORM_ERROR BOUNDARY_ERROR BOUNDARIES... | positive_softabs SMOOTHING HESSIAN ARGUMENT ARGUMENT_ERROR TANH TANH_ERROR EIGENVALUE DIVISION_ERROR | positive_softabs_metric SMOOTHING HESSIAN ARGUMENT ARGUMENT_ERROR TANH TANH_ERROR EIGENVALUE DIVISION_ERROR SQRT SQRT_ERROR FACTOR FACTOR_ERROR LOG LOG_ERROR | positive_softabs_metric_upper METRIC_FIELDS... TANH_LOWER COMPUTED_SQRT_LOWER IDEAL_SQRT_LOWER | positive_softabs_hamiltonian METRIC_FIELDS... POTENTIAL MOMENTUM KINETIC_INPUT KINETIC KINETIC_ERROR KINETIC_INPUT_ERROR ENERGY ENERGY_ERROR | positive_softabs_hamiltonian_upper HAMILTONIAN_FIELDS... TANH_LOWER COMPUTED_SQRT_LOWER IDEAL_SQRT_LOWER KINETIC_SQRT_LOWER | positive_softabs_hamiltonian_trajectory COUNT HAMILTONIAN_FIELDS..."

private def parseNat (text : String) : Except String Nat :=
  match text.toNat? with
  | some value => .ok value
  | none => .error s!"invalid natural: {text}"

private def parseWeights (text : String) : Except String (List Nat) := do
  let fields := text.splitOn ","
  if fields.isEmpty then throw "empty weights"
  fields.mapM parseNat

private def parseRows (text : String) : Except String (List (List Nat)) :=
  (text.splitOn ";").mapM parseWeights

private def parseRat (text : String) : Except String ℚ := do
  match text.splitOn "/" with
  | [numeratorText, denominatorText] =>
      let numerator ← match numeratorText.toInt? with
        | some value => .ok value
        | none => .error s!"invalid rational numerator: {numeratorText}"
      let denominator ← parseNat denominatorText
      if hdenominator : denominator ≠ 0 then
        return Rat.normalize numerator denominator hdenominator
      else
        throw "rational denominator must be positive"
  | _ => throw s!"invalid rational: {text}"

private def runContractionAposteriori (fields : List String) : IO Unit := do
  match fields with
  | [residualText, rateText, distanceText] =>
      match parseRat residualText, parseRat rateText, parseRat distanceText with
      | .ok residual, .ok rate, .ok distance =>
          let certificate :
              Mcmc.Relativistic.AposterioriContractionRationalCertificate :=
            { residualUpper := residual, rate := rate, distanceUpper := distance }
          if certificate.check then IO.println "ok"
          else IO.println "error invalidContractionAposteriori"
      | .error error, _, _ | _, .error error, _ | _, _, .error error =>
          IO.println s!"error {error}"
  | _ => IO.println "error invalidContractionAposterioriFieldCount"

private def runSinCosInterval (fields : List String) : IO Unit := do
  match fields.mapM parseRat with
  | .ok [input, computedSin, sinError, computedCos, cosError] =>
      let certificate :
          Mcmc.Executable.Continuous.SinCosRationalIntervalCertificate :=
        { input := input
          computedSin := computedSin
          sinError := sinError
          computedCos := computedCos
          cosError := cosError }
      if certificate.check then IO.println "ok"
      else IO.println "error invalidSinCosInterval"
  | .ok _ => IO.println "error invalidSinCosIntervalFieldCount"
  | .error error => IO.println s!"error {error}"

private def boundedScalarCallbackOfRats (fields : List ℚ) : Except String
    Mcmc.Executable.Continuous.BoundedScalarCallbackRationalCertificate := do
  match fields with
  | [input, computedSin, sinError, computedCos, cosError, momentum,
      computedRadicand, radicandArithmeticError, sqrtInput, computedSqrt,
      sqrtError, reciprocalInput, computedReciprocal, reciprocalError,
      computedSqrtLower, computedMomentumCallback, momentumArithmeticError,
      computedPositionCallback, positionArithmeticError] =>
      let sincos :
          Mcmc.Executable.Continuous.SinCosRationalIntervalCertificate :=
        { input := input
          computedSin := computedSin
          sinError := sinError
          computedCos := computedCos
          cosError := cosError }
      let sqrtCertificate :
          Mcmc.Executable.Continuous.SqrtRationalIntervalCertificate :=
        { input := sqrtInput, computed := computedSqrt, error := sqrtError }
      let reciprocalCertificate :
          Mcmc.Executable.Continuous.ReciprocalRationalResidualCertificate :=
        { input := reciprocalInput
          computed := computedReciprocal
          error := reciprocalError }
      let primitive :
          Mcmc.Executable.Continuous.BoundedScalarPrimitiveRationalCertificate :=
        { sincos := sincos
          momentum := momentum
          computedRadicand := computedRadicand
          radicandArithmeticError := radicandArithmeticError
          sqrtCertificate := sqrtCertificate
          reciprocalCertificate := reciprocalCertificate
          computedSqrtLower := computedSqrtLower }
      let certificate :
          Mcmc.Executable.Continuous.BoundedScalarCallbackRationalCertificate :=
        { primitive := primitive
          computedMomentumCallback := computedMomentumCallback
          momentumArithmeticError := momentumArithmeticError
          computedPositionCallback := computedPositionCallback
          positionArithmeticError := positionArithmeticError }
      return certificate
  | _ => throw "invalidBoundedScalarCallbacksFieldCount"

private def runBoundedScalarCallbacks (fields : List String) : IO Unit := do
  match fields.mapM parseRat >>= boundedScalarCallbackOfRats with
  | .ok certificate =>
      if certificate.check then IO.println "ok"
      else IO.println "error invalidBoundedScalarCallbacks"
  | .error error => IO.println s!"error {error}"

private partial def parseBoundedScalarCallbackTraceEntries
    (fields : List String) : Except String
      (List Mcmc.Executable.Continuous.BoundedScalarCallbackTraceEntry) := do
  match fields with
  | [] => return []
  | kindText :: rest => do
      if rest.length < 19 then
        throw "invalidBoundedScalarCallbackTraceFieldCount"
      else do
        let rats ← (rest.take 19).mapM parseRat
        let certificate ← boundedScalarCallbackOfRats rats
        let kind : Mcmc.Executable.Continuous.BoundedScalarCallbackKind ←
          if kindText = "position" then
            pure .position
          else if kindText = "momentum" then
            pure .momentum
          else
            throw s!"invalid callback kind: {kindText}"
        let tail ← parseBoundedScalarCallbackTraceEntries (rest.drop 19)
        return { kind := kind, certificate := certificate } :: tail

private def runBoundedScalarCallbackTrace (fields : List String) : IO Unit := do
  match fields with
  | countText :: halfText :: positionText :: entryFields =>
      match parseNat countText, parseNat halfText, parseNat positionText,
          parseBoundedScalarCallbackTraceEntries entryFields with
      | .ok count, .ok halfIterations, .ok positionIterations, .ok entries =>
          if entries.length != count then
            IO.println "error invalidBoundedScalarCallbackTraceCount"
          else
            let trace : Mcmc.Executable.Continuous.BoundedScalarCallbackTraceRationalCertificate :=
              { halfIterations := halfIterations
                positionIterations := positionIterations
                entries := entries }
            if trace.check then IO.println "ok"
            else IO.println "error invalidBoundedScalarCallbackTrace"
      | .error error, _, _, _ | _, .error error, _, _ |
          _, _, .error error, _ | _, _, _, .error error =>
            IO.println s!"error {error}"
  | _ => IO.println "error invalidBoundedScalarCallbackTraceFieldCount"

private def boundedScalarAffineSourcesOfEntries
    (entries : List Mcmc.Executable.Continuous.BoundedScalarCallbackTraceEntry) :
    Except String
      Mcmc.Executable.Continuous.BoundedScalarAffineCallbackSources :=
  match entries with
  | [entry] => Except.ok
      (Mcmc.Executable.Continuous.BoundedScalarAffineCallbackSources.one entry)
  | [first, second] => Except.ok
      (Mcmc.Executable.Continuous.BoundedScalarAffineCallbackSources.pair first second)
  | _ => Except.error "invalidBoundedScalarAffineSourceCount"

private def boundedScalarAffineUpdateOfFields (fields : List String) :
    Except String
      Mcmc.Executable.Continuous.BoundedScalarAffineUpdateRationalCertificate := do
  match fields with
  | sourceCountText :: payload => do
      let sourceCount ← parseNat sourceCountText
      if sourceCount != 1 && sourceCount != 2 then
        throw "invalidBoundedScalarAffineSourceCount"
      let callbackFieldCount := 20 * sourceCount
      let entries ← parseBoundedScalarCallbackTraceEntries
        (payload.take callbackFieldCount)
      if entries.length != sourceCount then
        throw "invalidBoundedScalarAffineSourceCount"
      let rats ← (payload.drop callbackFieldCount).mapM parseRat
      let (callbackArithmeticError, base, scale, computedCallback,
          callbackError, computedUpdate, arithmeticError, updateError) ←
        match rats with
        | [callbackArithmeticError, base, scale, computedCallback,
            callbackError, computedUpdate, arithmeticError, updateError] =>
              .ok (callbackArithmeticError, base, scale, computedCallback,
                callbackError, computedUpdate, arithmeticError, updateError)
        | _ => .error "invalidBoundedScalarAffineUpdateFieldCount"
      let sources ← boundedScalarAffineSourcesOfEntries entries
      let affine : Mcmc.Relativistic.RoundedAffineUpdateRationalCertificate :=
        { base := base, scale := scale
          computedCallback := computedCallback
          callbackError := callbackError
          computedUpdate := computedUpdate
          arithmeticError := arithmeticError
          updateError := updateError }
      return Mcmc.Executable.Continuous.BoundedScalarAffineUpdateRationalCertificate.mk
        sources callbackArithmeticError affine
  | [] => throw "invalidBoundedScalarAffineUpdateFieldCount"

private def runBoundedScalarAffineUpdate (fields : List String) : IO Unit := do
  match boundedScalarAffineUpdateOfFields fields with
  | .ok certificate =>
      if certificate.check then IO.println "ok"
      else IO.println "error invalidBoundedScalarAffineUpdate"
  | .error error => IO.println s!"error {error}"

private def boundedScalarSolverContractionOfFields (fields : List String) :
    Except String
      Mcmc.Executable.Continuous.BoundedScalarSolverContractionRationalCertificate := do
  match fields with
  | kindText :: epsilonText :: payload => do
      let kind : Mcmc.Executable.Continuous.BoundedScalarSolverContractionKind ←
        match kindText with
        | "half" => pure .halfMomentum
        | "position" => pure .position
        | _ => throw "invalidBoundedScalarSolverContractionKind"
      let epsilon ← parseRat epsilonText
      let sourceCount ← match payload with
        | sourceCountText :: _ => parseNat sourceCountText
        | [] => throw "invalidBoundedScalarSolverContractionFieldCount"
      let affineFieldCount := 1 + 20 * sourceCount + 8
      if payload.length != affineFieldCount + 6 then
        throw "invalidBoundedScalarSolverContractionFieldCount"
      let update ← boundedScalarAffineUpdateOfFields (payload.take affineFieldCount)
      let rats ← (payload.drop affineFieldCount).mapM parseRat
      let (iterate, computedUpdate, updateError, residualUpper, rate,
          distanceUpper) ← match rats with
        | [iterate, computedUpdate, updateError, residualUpper, rate,
            distanceUpper] =>
              pure (iterate, computedUpdate, updateError, residualUpper, rate,
                distanceUpper)
        | _ => throw "invalidBoundedScalarSolverContractionFieldCount"
      let residual : Mcmc.Relativistic.RoundedContractionResidualRationalCertificate :=
        { iterate := iterate
          computedUpdate := computedUpdate
          updateError := updateError
          residualUpper := residualUpper }
      let contraction : Mcmc.Relativistic.AposterioriContractionRationalCertificate :=
        { residualUpper := residualUpper
          rate := rate
          distanceUpper := distanceUpper }
      return Mcmc.Executable.Continuous.BoundedScalarSolverContractionRationalCertificate.mk
        kind epsilon update residual contraction
  | _ => throw "invalidBoundedScalarSolverContractionFieldCount"

private def runBoundedScalarSolverContraction (fields : List String) : IO Unit := do
  match boundedScalarSolverContractionOfFields fields with
  | .ok certificate =>
      if certificate.check then IO.println "ok"
      else IO.println "error invalidBoundedScalarSolverContraction"
  | .error error => IO.println s!"error {error}"

private def boundedScalarSolverPhaseOfFields (fields : List String) :
    Except String
      Mcmc.Executable.Continuous.BoundedScalarSolverPhaseRationalCertificate := do
  let (halfLength, halfPayload) ← match fields with
    | halfLengthText :: payload => pure (← parseNat halfLengthText, payload)
    | [] => throw "invalidBoundedScalarSolverPhaseFieldCount"
  if halfPayload.length < halfLength + 1 then
    throw "invalidBoundedScalarSolverPhaseFieldCount"
  let half ← boundedScalarSolverContractionOfFields
    (halfPayload.take halfLength)
  let positionHeader := halfPayload.drop halfLength
  let (positionLength, positionPayload) ← match positionHeader with
    | positionLengthText :: payload => pure (← parseNat positionLengthText, payload)
    | [] => throw "invalidBoundedScalarSolverPhaseFieldCount"
  if positionPayload.length != positionLength + 1 then
    throw "invalidBoundedScalarSolverPhaseFieldCount"
  let position ← boundedScalarSolverContractionOfFields
    (positionPayload.take positionLength)
  let positionError ← match positionPayload.drop positionLength with
    | [positionErrorText] => parseRat positionErrorText
    | _ => throw "invalidBoundedScalarSolverPhaseFieldCount"
  return Mcmc.Executable.Continuous.BoundedScalarSolverPhaseRationalCertificate.mk
    half position positionError

private def runBoundedScalarSolverPhase (fields : List String) : IO Unit := do
  match boundedScalarSolverPhaseOfFields fields with
  | .ok certificate =>
      if certificate.check then IO.println "ok"
      else IO.println "error invalidBoundedScalarSolverPhase"
  | .error error => IO.println s!"error {error}"

private def boundedScalarSolverEndpointOfFields (fields : List String) :
    Except String
      Mcmc.Executable.Continuous.BoundedScalarSolverEndpointRationalCertificate := do
  let (phaseLength, phasePayload) ← match fields with
    | phaseLengthText :: payload => pure (← parseNat phaseLengthText, payload)
    | [] => throw "invalidBoundedScalarSolverEndpointFieldCount"
  if phasePayload.length < phaseLength + 1 then
    throw "invalidBoundedScalarSolverEndpointFieldCount"
  let phase ← boundedScalarSolverPhaseOfFields (phasePayload.take phaseLength)
  let updateHeader := phasePayload.drop phaseLength
  let (updateLength, updatePayload) ← match updateHeader with
    | updateLengthText :: payload => pure (← parseNat updateLengthText, payload)
    | [] => throw "invalidBoundedScalarSolverEndpointFieldCount"
  if updatePayload.length != updateLength + 2 then
    throw "invalidBoundedScalarSolverEndpointFieldCount"
  let finalUpdate ← boundedScalarAffineUpdateOfFields
    (updatePayload.take updateLength)
  let errors ← (updatePayload.drop updateLength).mapM parseRat
  let (finalMomentumError, phaseError) ← match errors with
    | [finalMomentumError, phaseError] => pure (finalMomentumError, phaseError)
    | _ => throw "invalidBoundedScalarSolverEndpointFieldCount"
  return Mcmc.Executable.Continuous.BoundedScalarSolverEndpointRationalCertificate.mk
    phase finalUpdate finalMomentumError phaseError

private def runBoundedScalarSolverEndpoint (fields : List String) : IO Unit := do
  match boundedScalarSolverEndpointOfFields fields with
  | .ok certificate =>
      if certificate.check then IO.println "ok"
      else IO.println "error invalidBoundedScalarSolverEndpoint"
  | .error error => IO.println s!"error {error}"

private def boundedScalarLinkedSolverStepsOfFields : Nat → List String →
    Except String
      (List Mcmc.Executable.Continuous.BoundedScalarSolverEndpointRationalCertificate)
  | 0, [] => pure []
  | 0, _ => throw "invalidBoundedScalarLinkedSolverTrajectoryFieldCount"
  | count + 1, fields => do
      let (stepLength, payload) ← match fields with
        | stepLengthText :: payload => pure (← parseNat stepLengthText, payload)
        | [] => throw "invalidBoundedScalarLinkedSolverTrajectoryFieldCount"
      if payload.length < stepLength then
        throw "invalidBoundedScalarLinkedSolverTrajectoryFieldCount"
      let step ← boundedScalarSolverEndpointOfFields (payload.take stepLength)
      let rest ← boundedScalarLinkedSolverStepsOfFields count
        (payload.drop stepLength)
      pure (step :: rest)

private def runBoundedScalarLinkedSolverTrajectory
    (fields : List String) : IO Unit := do
  let result : Except String
      Mcmc.Executable.Continuous.BoundedScalarLinkedSolverTrajectoryRationalCertificate := do
    let (epsilon, initialPosition, initialMomentum, count, payload) ← match fields with
      | epsilonText :: positionText :: momentumText :: countText :: payload =>
          pure (← parseRat epsilonText, ← parseRat positionText,
            ← parseRat momentumText, ← parseNat countText, payload)
      | _ => throw "invalidBoundedScalarLinkedSolverTrajectoryFieldCount"
    let steps ← boundedScalarLinkedSolverStepsOfFields count payload
    pure <|
      Mcmc.Executable.Continuous.BoundedScalarLinkedSolverTrajectoryRationalCertificate.mk
        epsilon initialPosition initialMomentum steps
  match result with
  | .ok certificate =>
      if certificate.check then IO.println "ok"
      else IO.println "error invalidBoundedScalarLinkedSolverTrajectory"
  | .error error => IO.println s!"error {error}"

private def runBoundedScalarStepRegional (fields : List String) : IO Unit := do
  match fields.mapM parseRat with
  | .ok [epsilon, halfMomentumBound, forcePositionRate, halfCoefficient,
      positionCoefficient, momentumCoefficient, lipschitzUpper] =>
      let certificate :
          Mcmc.Executable.Continuous.BoundedScalarStepRegionalRationalCertificate :=
        { epsilon := epsilon
          halfMomentumBound := halfMomentumBound
          forcePositionRate := forcePositionRate
          halfCoefficient := halfCoefficient
          positionCoefficient := positionCoefficient
          momentumCoefficient := momentumCoefficient
          lipschitzUpper := lipschitzUpper }
      if certificate.check then IO.println "ok"
      else IO.println "error invalidBoundedScalarStepRegional"
  | .ok _ => IO.println "error invalidBoundedScalarStepRegionalFieldCount"
  | .error error => IO.println s!"error {error}"

private def boundedScalarEndpointEnergyOfFields (fields : List String) :
    Except String
      Mcmc.Executable.Continuous.BoundedScalarEndpointEnergyRationalCertificate := do
    let (solverLength, payload) ← match fields with
      | solverLengthText :: payload => pure (← parseNat solverLengthText, payload)
      | [] => throw "invalidBoundedScalarEndpointEnergyFieldCount"
    if payload.length != solverLength + 20 then
      throw "invalidBoundedScalarEndpointEnergyFieldCount"
    let solver ← boundedScalarSolverEndpointOfFields (payload.take solverLength)
    let evaluationRats ← (payload.drop solverLength |>.take 19).mapM parseRat
    let evaluation ← boundedScalarCallbackOfRats evaluationRats
    let totalEnergyError ← match payload.drop (solverLength + 19) with
      | [totalEnergyErrorText] => parseRat totalEnergyErrorText
      | _ => throw "invalidBoundedScalarEndpointEnergyFieldCount"
    return Mcmc.Executable.Continuous.BoundedScalarEndpointEnergyRationalCertificate.mk
      solver evaluation totalEnergyError

private def runBoundedScalarEndpointEnergy (fields : List String) : IO Unit := do
  let result := boundedScalarEndpointEnergyOfFields fields
  match result with
  | .ok certificate =>
      if certificate.check then IO.println "ok"
      else IO.println "error invalidBoundedScalarEndpointEnergy"
  | .error error => IO.println s!"error {error}"

private def boundedScalarTwoEndpointEnergyOfFields (fields : List String) :
    Except String
      Mcmc.Executable.Continuous.BoundedScalarTwoEndpointEnergyRationalCertificate := do
    if fields.length < 21 then
      throw "invalidBoundedScalarTwoEndpointEnergyFieldCount"
    let initialRats ← (fields.take 19).mapM parseRat
    let initial ← boundedScalarCallbackOfRats initialRats
    let remainder := fields.drop 19
    let final ← boundedScalarEndpointEnergyOfFields (remainder.dropLast)
    let commonError ← match remainder.getLast? with
      | some commonErrorText => parseRat commonErrorText
      | none => throw "invalidBoundedScalarTwoEndpointEnergyFieldCount"
    return Mcmc.Executable.Continuous.BoundedScalarTwoEndpointEnergyRationalCertificate.mk
      initial final commonError

private def runBoundedScalarTwoEndpointEnergy (fields : List String) : IO Unit := do
  let result := boundedScalarTwoEndpointEnergyOfFields fields
  match result with
  | .ok certificate =>
      if certificate.check then IO.println "ok"
      else IO.println "error invalidBoundedScalarTwoEndpointEnergy"
  | .error error => IO.println s!"error {error}"

private def runBoundedScalarTwoEndpointWeight (fields : List String) : IO Unit := do
  let result : Except String
      Mcmc.Executable.Continuous.BoundedScalarTwoEndpointWeightRationalCertificate := do
    let (energyLength, payload) ← match fields with
      | energyLengthText :: payload => pure (← parseNat energyLengthText, payload)
      | [] => throw "invalidBoundedScalarTwoEndpointWeightFieldCount"
    if payload.length != energyLength + 10 then
      throw "invalidBoundedScalarTwoEndpointWeightFieldCount"
    let energy ← boundedScalarTwoEndpointEnergyOfFields
      (payload.take energyLength)
    let weights ← (payload.drop energyLength).mapM parseRat
    let (first, second) ← match weights with
      | [input0, computed0, expError0, idealInput0, inputError0,
          input1, computed1, expError1, idealInput1, inputError1] =>
        pure
          (Mcmc.Executable.Continuous.ExpNonpositiveTransportRationalCertificate.mk
            { input := input0, computed := computed0, error := expError0 }
            idealInput0 inputError0,
           Mcmc.Executable.Continuous.ExpNonpositiveTransportRationalCertificate.mk
            { input := input1, computed := computed1, error := expError1 }
            idealInput1 inputError1)
      | _ => throw "invalidBoundedScalarTwoEndpointWeightFieldCount"
    return Mcmc.Executable.Continuous.BoundedScalarTwoEndpointWeightRationalCertificate.mk
      energy first second
  match result with
  | .ok certificate =>
      if certificate.check then IO.println "ok"
      else IO.println "error invalidBoundedScalarTwoEndpointWeight"
  | .error error => IO.println s!"error {error}"

private def runRoundedContractionResidual (fields : List String) : IO Unit := do
  match fields with
  | [iterateText, updateText, errorText, residualText] =>
      match parseRat iterateText, parseRat updateText, parseRat errorText,
          parseRat residualText with
      | .ok iterate, .ok update, .ok error, .ok residual =>
          let certificate :
              Mcmc.Relativistic.RoundedContractionResidualRationalCertificate :=
            { iterate := iterate, computedUpdate := update,
              updateError := error, residualUpper := residual }
          if certificate.check then IO.println "ok"
          else IO.println "error invalidRoundedContractionResidual"
      | .error error, _, _, _ | _, .error error, _, _ |
          _, _, .error error, _ | _, _, _, .error error =>
          IO.println s!"error {error}"
  | _ => IO.println "error invalidRoundedContractionResidualFieldCount"

private def runRoundedAffineUpdate (fields : List String) : IO Unit := do
  match fields.mapM parseRat with
  | .ok [base, scale, callback, callbackError, update, arithmeticError,
      updateError] =>
      let certificate :
          Mcmc.Relativistic.RoundedAffineUpdateRationalCertificate :=
        { base := base
          scale := scale
          computedCallback := callback
          callbackError := callbackError
          computedUpdate := update
          arithmeticError := arithmeticError
          updateError := updateError }
      if certificate.check then IO.println "ok"
      else IO.println "error invalidRoundedAffineUpdate"
  | .ok _ => IO.println "error invalidRoundedAffineUpdateFieldCount"
  | .error error => IO.println s!"error {error}"

private def runRoundedContractionPair (fields : List String) : IO Unit := do
  match fields with
  | [iterateText, updateText, errorText, residualText, rateText, distanceText] =>
      match parseRat iterateText, parseRat updateText, parseRat errorText,
          parseRat residualText, parseRat rateText, parseRat distanceText with
      | .ok iterate, .ok update, .ok error, .ok residual, .ok rate, .ok distance =>
          let residualCertificate :
              Mcmc.Relativistic.RoundedContractionResidualRationalCertificate :=
            { iterate := iterate, computedUpdate := update,
              updateError := error, residualUpper := residual }
          let contractionCertificate :
              Mcmc.Relativistic.AposterioriContractionRationalCertificate :=
            { residualUpper := residual, rate := rate, distanceUpper := distance }
          if residualCertificate.check && contractionCertificate.check then
            IO.println "ok"
          else IO.println "error invalidRoundedContractionPair"
      | .error error, _, _, _, _, _ | _, .error error, _, _, _, _ |
          _, _, .error error, _, _, _ | _, _, _, .error error, _, _ |
          _, _, _, _, .error error, _ | _, _, _, _, _, .error error =>
          IO.println s!"error {error}"
  | _ => IO.println "error invalidRoundedContractionPairFieldCount"

private def runGaussianCertificate
    (inputText valueText derivativeText hessianText valueErrorText
      derivativeErrorText hessianErrorText : String) :
    IO Unit := do
  match parseRat inputText, parseRat valueText, parseRat derivativeText,
      parseRat hessianText, parseRat valueErrorText, parseRat derivativeErrorText,
      parseRat hessianErrorText with
  | .ok input, .ok value, .ok derivative, .ok hessian, .ok valueError,
      .ok derivativeError, .ok hessianError =>
      let certificate :
          Mcmc.Executable.Continuous.RestrictedGaussianRationalCertificate :=
        { input := input
          computedValue := value
          computedDerivative := derivative
          computedSecondDerivative := hessian
          valueError := valueError
          derivativeError := derivativeError
          secondDerivativeError := hessianError }
      if certificate.check then IO.println "ok" else IO.println "error invalidCertificate"
  | .error error, _, _, _, _, _, _ | _, .error error, _, _, _, _, _ |
      _, _, .error error, _, _, _, _ | _, _, _, .error error, _, _, _ |
      _, _, _, _, .error error, _, _ | _, _, _, _, _, .error error, _ |
      _, _, _, _, _, _, .error error => IO.println s!"error {error}"

private def runQuarticCertificate
    (inputText valueText derivativeText hessianText valueErrorText
      derivativeErrorText hessianErrorText : String) :
    IO Unit := do
  match parseRat inputText, parseRat valueText, parseRat derivativeText,
      parseRat hessianText, parseRat valueErrorText, parseRat derivativeErrorText,
      parseRat hessianErrorText with
  | .ok input, .ok value, .ok derivative, .ok hessian, .ok valueError,
      .ok derivativeError, .ok hessianError =>
      let certificate :
          Mcmc.Executable.Continuous.RestrictedQuarticRationalCertificate :=
        { input := input
          computedValue := value
          computedDerivative := derivative
          computedSecondDerivative := hessian
          valueError := valueError
          derivativeError := derivativeError
          secondDerivativeError := hessianError }
      if certificate.check then IO.println "ok" else IO.println "error invalidCertificate"
  | .error error, _, _, _, _, _, _ | _, .error error, _, _, _, _, _ |
      _, _, .error error, _, _, _, _ | _, _, _, .error error, _, _, _ |
      _, _, _, _, .error error, _, _ | _, _, _, _, _, .error error, _ |
      _, _, _, _, _, _, .error error => IO.println s!"error {error}"

private def runGaussianDyadicLeapfrog
    (stepText positionText momentumText halfText nextPositionText
      nextMomentumText : String) : IO Unit := do
  match parseRat stepText, parseRat positionText, parseRat momentumText,
      parseRat halfText, parseRat nextPositionText, parseRat nextMomentumText with
  | .ok step, .ok position, .ok momentum, .ok half, .ok nextPosition,
      .ok nextMomentum =>
      let certificate :
          Mcmc.Executable.Continuous.GaussianDyadicLeapfrogStepCertificate :=
        { stepSize := step
          position := position
          momentum := momentum
          computedHalfMomentum := half
          computedNextPosition := nextPosition
          computedNextMomentum := nextMomentum }
      if certificate.check then IO.println "ok"
      else IO.println "error invalidGaussianDyadicLeapfrog"
  | .error error, _, _, _, _, _ | _, .error error, _, _, _, _ |
      _, _, .error error, _, _, _ | _, _, _, .error error, _, _ |
      _, _, _, _, .error error, _ | _, _, _, _, _, .error error =>
      IO.println s!"error {error}"

private def runGaussianRoundedLeapfrog
    (stepText positionText momentumText halfText nextPositionText
      nextMomentumText halfErrorText positionErrorText momentumErrorText : String) :
    IO Unit := do
  match parseRat stepText, parseRat positionText, parseRat momentumText,
      parseRat halfText, parseRat nextPositionText, parseRat nextMomentumText,
      parseRat halfErrorText, parseRat positionErrorText, parseRat momentumErrorText with
  | .ok step, .ok position, .ok momentum, .ok half, .ok nextPosition,
      .ok nextMomentum, .ok halfError, .ok positionError, .ok momentumError =>
      let certificate :
          Mcmc.Executable.Continuous.GaussianRoundedLeapfrogStepCertificate :=
        { stepSize := step
          position := position
          momentum := momentum
          computedHalfMomentum := half
          computedNextPosition := nextPosition
          computedNextMomentum := nextMomentum
          halfMomentumError := halfError
          nextPositionError := positionError
          nextMomentumError := momentumError }
      if certificate.check then IO.println "ok"
      else IO.println "error invalidGaussianRoundedLeapfrog"
  | .error error, _, _, _, _, _, _, _, _ |
      _, .error error, _, _, _, _, _, _, _ |
      _, _, .error error, _, _, _, _, _, _ |
      _, _, _, .error error, _, _, _, _, _ |
      _, _, _, _, .error error, _, _, _, _ |
      _, _, _, _, _, .error error, _, _, _ |
      _, _, _, _, _, _, .error error, _, _ |
      _, _, _, _, _, _, _, .error error, _ |
      _, _, _, _, _, _, _, _, .error error => IO.println s!"error {error}"

private def runRoundedLeapfrog (fields : List String) : IO Unit := do
  match fields.mapM parseRat with
  | .ok [step, position, momentum, currentGradient, half, nextPosition,
      nextGradient, nextMomentum, halfError, positionError, momentumError] =>
      let certificate :
          Mcmc.Executable.Continuous.RoundedLeapfrogRationalCertificate :=
        { stepSize := step
          position := position
          momentum := momentum
          currentGradient := currentGradient
          computedHalfMomentum := half
          computedNextPosition := nextPosition
          nextGradient := nextGradient
          computedNextMomentum := nextMomentum
          halfMomentumError := halfError
          nextPositionError := positionError
          nextMomentumError := momentumError }
      if certificate.check then IO.println "ok"
      else IO.println "error invalidRoundedLeapfrog"
  | .ok _ => IO.println "error invalidRoundedLeapfrogFieldCount"
  | .error error => IO.println s!"error {error}"

private def runRoundedGaussianFourLeaf (fields : List String) : IO Unit := do
  match fields.mapM parseRat with
  | .ok values =>
      let expected : List ℚ := [
        0, 1,
        3602879701896397 / 36028797018963968,
        8962163258467287 / 9007199254740992,
        3584865303386915 / 18014398509481984,
        8827505629608909 / 9007199254740992,
        2666221051395881 / 9007199254740992,
        4302286472227221 / 4503599627370496]
      if values == expected then IO.println "ok"
      else IO.println "error invalidRoundedGaussianFourLeaf"
  | .error error => IO.println s!"error {error}"

private def runUnitZeroSoftAbs (fields : List String) : IO Unit := do
  match fields.mapM parseRat with
  | .ok [hessian, eigenvalue, sqrtValue, factor, logDet] =>
      let certificate :
          Mcmc.Executable.Continuous.UnitZeroSoftAbsRationalCertificate :=
        { computedHessian := hessian
          computedEigenvalue := eigenvalue
          computedSqrt := sqrtValue
          computedFactor := factor
          computedLogDet := logDet }
      if certificate.check then IO.println "ok"
      else IO.println "error invalidUnitZeroSoftAbs"
  | .ok _ => IO.println "error invalidUnitZeroSoftAbsFieldCount"
  | .error error => IO.println s!"error {error}"

private def runSqrtInterval (fields : List String) : IO Unit := do
  match fields.mapM parseRat with
  | .ok [input, computed, error] =>
      let certificate :
          Mcmc.Executable.Continuous.SqrtRationalIntervalCertificate :=
        { input := input, computed := computed, error := error }
      if certificate.check then IO.println "ok"
      else IO.println "error invalidSqrtInterval"
  | .ok _ => IO.println "error invalidSqrtIntervalFieldCount"
  | .error error => IO.println s!"error {error}"

private def runReciprocalResidual (fields : List String) : IO Unit := do
  match fields.mapM parseRat with
  | .ok [input, computed, error] =>
      let certificate :
          Mcmc.Executable.Continuous.ReciprocalRationalResidualCertificate :=
        { input := input, computed := computed, error := error }
      if certificate.check then IO.println "ok"
      else IO.println "error invalidReciprocalResidual"
  | .ok _ => IO.println "error invalidReciprocalResidualFieldCount"
  | .error error => IO.println s!"error {error}"

private def runSqrtReciprocal (fields : List String) : IO Unit := do
  match fields.mapM parseRat with
  | .ok [input, sqrtValue, sqrtError, reciprocalValue, reciprocalError] =>
      let sqrtCertificate :
          Mcmc.Executable.Continuous.SqrtRationalIntervalCertificate :=
        { input := input, computed := sqrtValue, error := sqrtError }
      let reciprocalCertificate :
          Mcmc.Executable.Continuous.ReciprocalRationalResidualCertificate :=
        { input := sqrtValue, computed := reciprocalValue, error := reciprocalError }
      if sqrtCertificate.check && reciprocalCertificate.check && decide (0 < input) then
        IO.println "ok"
      else IO.println "error invalidSqrtReciprocal"
  | .ok _ => IO.println "error invalidSqrtReciprocalFieldCount"
  | .error error => IO.println s!"error {error}"

private def runLogInterval (fields : List String) : IO Unit := do
  match fields.mapM parseRat with
  | .ok [input, computed, error] =>
      let certificate :
          Mcmc.Executable.Continuous.LogRationalIntervalCertificate :=
        { input := input, computed := computed, error := error }
      if certificate.check then IO.println "ok"
      else IO.println "error invalidLogInterval"
  | .ok _ => IO.println "error invalidLogIntervalFieldCount"
  | .error error => IO.println s!"error {error}"

private def runExpNonpositive (fields : List String) : IO Unit := do
  match fields.mapM parseRat with
  | .ok [input, computed, error] =>
      let certificate : Mcmc.Executable.Continuous.ExpNonpositiveRationalIntervalCertificate :=
        { input := input, computed := computed, error := error }
      if certificate.check then IO.println "ok"
      else IO.println "error invalidExpNonpositive"
  | .ok _ => IO.println "error invalidExpNonpositiveFieldCount"
  | .error error => IO.println s!"error {error}"

private def runExpNonpositiveTransport (fields : List String) : IO Unit := do
  match fields.mapM parseRat with
  | .ok [input, computed, expError, idealInput, inputError] =>
      let certificate : Mcmc.Executable.Continuous.ExpNonpositiveTransportRationalCertificate :=
        { localCertificate := { input := input, computed := computed, error := expError }
          idealInput := idealInput
          inputError := inputError }
      if certificate.check then IO.println "ok"
      else IO.println "error invalidExpNonpositiveTransport"
  | .ok _ => IO.println "error invalidExpNonpositiveTransportFieldCount"
  | .error error => IO.println s!"error {error}"

private def expNonpositiveTransportOfRationals (fields : List ℚ) : Option
    Mcmc.Executable.Continuous.ExpNonpositiveTransportRationalCertificate :=
  match fields with
  | [input, computed, expError, idealInput, inputError] =>
      let certificate : Mcmc.Executable.Continuous.ExpNonpositiveTransportRationalCertificate :=
        { localCertificate :=
          { input := input, computed := computed, error := expError }
          idealInput := idealInput
          inputError := inputError }
      some certificate
  | _ => none

private def expNonpositiveTransportTrajectoryOfRationals :
    Nat → List ℚ → Option
      (List Mcmc.Executable.Continuous.ExpNonpositiveTransportRationalCertificate)
  | 0, [] => some []
  | 0, _ => none
  | count + 1, fields => do
      let certificate ← expNonpositiveTransportOfRationals (fields.take 5)
      let rest ← expNonpositiveTransportTrajectoryOfRationals count
        (fields.drop 5)
      pure (certificate :: rest)

private def runExpNonpositiveTransportTrajectory
    (countText : String) (fields : List String) : IO Unit := do
  match parseNat countText, fields.mapM parseRat with
  | .ok count, .ok rationals =>
      match expNonpositiveTransportTrajectoryOfRationals count rationals with
      | some certificates =>
          if certificates.all (fun certificate => certificate.check) then
            IO.println "ok"
          else IO.println "error invalidExpNonpositiveTransportTrajectory"
      | none => IO.println "error invalidExpNonpositiveTransportTrajectoryFieldCount"
  | .error error, _ | _, .error error => IO.println s!"error {error}"

private def roundedCumulativeStepsOfRationals :
    Nat → List ℚ → Option
      (List Mcmc.Executable.Continuous.RoundedCumulativeRationalStep)
  | 0, [] => some []
  | 0, _ => none
  | count + 1, weight :: boundary :: error :: fields => do
      let rest ← roundedCumulativeStepsOfRationals count fields
      pure ({ weight := weight, computedBoundary := boundary, error := error } :: rest)
  | _, _ => none

private def runRoundedCumulative
    (countText : String) (fields : List String) : IO Unit := do
  match parseNat countText, fields.mapM parseRat with
  | .ok count, .ok rationals =>
      match roundedCumulativeStepsOfRationals count rationals with
      | some steps =>
          let certificate : Mcmc.Executable.Continuous.RoundedCumulativeRationalCertificate :=
            { steps := steps }
          if certificate.check then IO.println "ok"
          else IO.println "error invalidRoundedCumulative"
      | none => IO.println "error invalidRoundedCumulativeFieldCount"
  | .error error, _ | _, .error error => IO.println s!"error {error}"

private def runScaledDraw (fields : List String) : IO Unit := do
  match fields.mapM parseRat with
  | .ok [uniform, total, computed, error] =>
      let certificate : Mcmc.Executable.Continuous.ScaledDrawRationalCertificate :=
        { uniform := uniform, total := total, computed := computed, error := error }
      if certificate.check then IO.println "ok"
      else IO.println "error invalidScaledDraw"
  | .ok _ => IO.println "error invalidScaledDrawFieldCount"
  | .error error => IO.println s!"error {error}"

private def runMultinomialDecision (fields : List String) : IO Unit := do
  match fields with
  | drawText :: countText :: uniformErrorText :: boundaryErrorText :: boundaries =>
      match parseRat drawText, parseNat countText, parseRat uniformErrorText,
          parseRat boundaryErrorText, boundaries.mapM parseRat with
      | .ok draw, .ok count, .ok uniformError, .ok boundaryError,
          .ok boundaryValues =>
          if count != boundaryValues.length then
            IO.println "error invalidMultinomialDecisionFieldCount"
          else
            let certificate :
                Mcmc.Executable.Continuous.MultinomialDecisionRationalCertificate :=
              { computedDraw := draw
                computedBoundaries := boundaryValues
                uniformError := uniformError
                boundaryError := boundaryError }
            if certificate.check then IO.println "ok"
            else IO.println "error invalidMultinomialDecision"
      | .error error, _, _, _, _ | _, .error error, _, _, _ |
          _, _, .error error, _, _ | _, _, _, .error error, _ |
          _, _, _, _, .error error => IO.println s!"error {error}"
  | _ => IO.println "error invalidMultinomialDecisionFieldCount"

private def runPositiveSoftAbs (fields : List String) : IO Unit := do
  match fields.mapM parseRat with
  | .ok [smoothing, hessian, argument, argumentError, tanhValue, tanhError,
      eigenvalue, divisionError] =>
      let certificate :
          Mcmc.Executable.Continuous.PositiveSoftAbsRationalCertificate :=
        { smoothing := smoothing
          hessian := hessian
          computedArgument := argument
          argumentError := argumentError
          computedTanh := tanhValue
          tanhError := tanhError
          computedEigenvalue := eigenvalue
          divisionError := divisionError }
      if certificate.check then IO.println "ok"
      else IO.println "error invalidPositiveSoftAbs"
  | .ok _ => IO.println "error invalidPositiveSoftAbsFieldCount"
  | .error error => IO.println s!"error {error}"

private def runPositiveSoftAbsMetric (fields : List String) : IO Unit := do
  match fields.mapM parseRat with
  | .ok [smoothing, hessian, argument, argumentError, tanhValue, tanhError,
      eigenvalue, divisionError, sqrtValue, sqrtError, factor, factorError,
      logDet, logError] =>
      let certificate :
          Mcmc.Executable.Continuous.PositiveSoftAbsMetricRationalCertificate :=
        { eigenvalue :=
            { smoothing := smoothing
              hessian := hessian
              computedArgument := argument
              argumentError := argumentError
              computedTanh := tanhValue
              tanhError := tanhError
              computedEigenvalue := eigenvalue
              divisionError := divisionError }
          sqrt := { input := eigenvalue, computed := sqrtValue, error := sqrtError }
          factor := { input := sqrtValue, computed := factor, error := factorError }
          logDet := { input := eigenvalue, computed := logDet, error := logError }
          sqrtInput := rfl
          factorInput := rfl
          logInput := rfl }
      if certificate.check then IO.println "ok"
      else IO.println "error invalidPositiveSoftAbsMetric"
  | .ok _ => IO.println "error invalidPositiveSoftAbsMetricFieldCount"
  | .error error => IO.println s!"error {error}"

private def runPositiveSoftAbsMetricUpper (fields : List String) : IO Unit := do
  match fields.mapM parseRat with
  | .ok [smoothing, hessian, argument, argumentError, tanhValue, tanhError,
      eigenvalue, divisionError, sqrtValue, sqrtError, factor, factorError,
      logDet, logError, idealTanhLower, computedSqrtLower, idealSqrtLower,
      reportedEigenvalueError, reportedSqrtError, reportedFactorError,
      reportedLogDetError] =>
      let metric :
          Mcmc.Executable.Continuous.PositiveSoftAbsMetricRationalCertificate :=
        { eigenvalue :=
            { smoothing := smoothing
              hessian := hessian
              computedArgument := argument
              argumentError := argumentError
              computedTanh := tanhValue
              tanhError := tanhError
              computedEigenvalue := eigenvalue
              divisionError := divisionError }
          sqrt := { input := eigenvalue, computed := sqrtValue, error := sqrtError }
          factor := { input := sqrtValue, computed := factor, error := factorError }
          logDet := { input := eigenvalue, computed := logDet, error := logError }
          sqrtInput := rfl
          factorInput := rfl
          logInput := rfl }
      let certificate :
          Mcmc.Executable.Continuous.PositiveSoftAbsMetricErrorUpperCertificate :=
        { metric := metric
          idealTanhLower := idealTanhLower
          computedSqrtLower := computedSqrtLower
          idealSqrtLower := idealSqrtLower }
      if certificate.check && certificate.eigenvalueError = reportedEigenvalueError &&
          certificate.sqrtError = reportedSqrtError &&
          certificate.factorError = reportedFactorError &&
          certificate.logDetError = reportedLogDetError then IO.println "ok"
      else IO.println "error invalidPositiveSoftAbsMetricUpper"
  | .ok _ => IO.println "error invalidPositiveSoftAbsMetricUpperFieldCount"
  | .error error => IO.println s!"error {error}"

private def positiveSoftAbsHamiltonianOfRationals (fields : List ℚ) :
    Option Mcmc.Executable.Continuous.PositiveSoftAbsHamiltonianRationalCertificate :=
  match fields with
  | [smoothing, hessian, argument, argumentError, tanhValue, tanhError,
      eigenvalue, divisionError, sqrtValue, sqrtError, factor, factorError,
      logDet, logError, potential, momentum, kineticInput, kinetic,
      kineticError, kineticInputError, energy, energyError] =>
      let metric :
          Mcmc.Executable.Continuous.PositiveSoftAbsMetricRationalCertificate :=
        { eigenvalue :=
            { smoothing := smoothing
              hessian := hessian
              computedArgument := argument
              argumentError := argumentError
              computedTanh := tanhValue
              tanhError := tanhError
              computedEigenvalue := eigenvalue
              divisionError := divisionError }
          sqrt := { input := eigenvalue, computed := sqrtValue, error := sqrtError }
          factor := { input := sqrtValue, computed := factor, error := factorError }
          logDet := { input := eigenvalue, computed := logDet, error := logError }
          sqrtInput := rfl
          factorInput := rfl
          logInput := rfl }
      let certificate : Mcmc.Executable.Continuous.PositiveSoftAbsHamiltonianRationalCertificate :=
        { metric := metric
          potential := potential
          momentum := momentum
          kinetic := { input := kineticInput, computed := kinetic, error := kineticError }
          kineticInputError := kineticInputError
          computedEnergy := energy
          energyArithmeticError := energyError }
      some certificate
  | _ => none

private def positiveSoftAbsHamiltonianTrajectoryOfRationals :
    Nat → List ℚ → Option
      (List Mcmc.Executable.Continuous.PositiveSoftAbsHamiltonianRationalCertificate)
  | 0, [] => some []
  | 0, _ => none
  | count + 1, fields => do
      let certificate ← positiveSoftAbsHamiltonianOfRationals (fields.take 22)
      let rest ← positiveSoftAbsHamiltonianTrajectoryOfRationals count
        (fields.drop 22)
      pure (certificate :: rest)

private def runPositiveSoftAbsHamiltonian (fields : List String) : IO Unit := do
  match fields.mapM parseRat with
  | .ok rationals =>
      match positiveSoftAbsHamiltonianOfRationals rationals with
      | some certificate =>
          if certificate.check then IO.println "ok"
          else IO.println "error invalidPositiveSoftAbsHamiltonian"
      | none => IO.println "error invalidPositiveSoftAbsHamiltonianFieldCount"
  | .error error => IO.println s!"error {error}"

private def runPositiveSoftAbsHamiltonianUpper (fields : List String) : IO Unit := do
  match fields.mapM parseRat with
  | .ok rationals =>
      match positiveSoftAbsHamiltonianOfRationals (rationals.take 22),
          rationals.drop 22 with
      | some endpoint,
          [idealTanhLower, computedSqrtLower, idealSqrtLower, kineticSqrtLower,
            reportedEnergyError] =>
          let metricUpper :
              Mcmc.Executable.Continuous.PositiveSoftAbsMetricErrorUpperCertificate :=
            { metric := endpoint.metric
              idealTanhLower := idealTanhLower
              computedSqrtLower := computedSqrtLower
              idealSqrtLower := idealSqrtLower }
          let certificate :
              Mcmc.Executable.Continuous.PositiveSoftAbsHamiltonianErrorUpperCertificate :=
            { endpoint := endpoint
              idealTanhLower := metricUpper.idealTanhLower
              computedSqrtLower := metricUpper.computedSqrtLower
              idealSqrtLower := metricUpper.idealSqrtLower
              kineticSqrtLower := kineticSqrtLower }
          if certificate.check && certificate.energyError = reportedEnergyError then
            IO.println "ok"
          else IO.println "error invalidPositiveSoftAbsHamiltonianUpper"
      | _, _ => IO.println "error invalidPositiveSoftAbsHamiltonianUpperFieldCount"
  | .error error => IO.println s!"error {error}"

private def runPositiveSoftAbsEndpointStateTransport
    (fields : List String) : IO Unit := do
  match fields.mapM parseRat with
  | .ok rationals =>
      match positiveSoftAbsHamiltonianOfRationals (rationals.take 22),
          rationals.drop 22 with
      | some endpoint,
          [idealTanhLower, computedSqrtLower, idealSqrtLower, kineticSqrtLower,
            reportedEndpointError, solverStateError, energyLipschitz,
            reportedTotalError] =>
          let endpointUpper :
              Mcmc.Executable.Continuous.PositiveSoftAbsHamiltonianErrorUpperCertificate :=
            { endpoint := endpoint
              idealTanhLower := idealTanhLower
              computedSqrtLower := computedSqrtLower
              idealSqrtLower := idealSqrtLower
              kineticSqrtLower := kineticSqrtLower }
          let certificate :
              Mcmc.Executable.Continuous.PositiveSoftAbsEndpointStateTransportCertificate :=
            { endpoint := endpointUpper
              solverStateError := solverStateError
              energyLipschitz := energyLipschitz
              totalEnergyError := reportedTotalError }
          if endpointUpper.energyError = reportedEndpointError && certificate.check then
            IO.println "ok"
          else IO.println "error invalidPositiveSoftAbsEndpointStateTransport"
      | _, _ =>
          IO.println "error invalidPositiveSoftAbsEndpointStateTransportFieldCount"
  | .error error => IO.println s!"error {error}"

private def runPositiveSoftAbsHamiltonianTrajectory
    (countText : String) (fields : List String) : IO Unit := do
  match parseNat countText, fields.mapM parseRat with
  | .ok count, .ok rationals =>
      match positiveSoftAbsHamiltonianTrajectoryOfRationals count rationals with
      | some certificates =>
          if certificates.all (fun certificate => certificate.check) then
            IO.println "ok"
          else IO.println "error invalidPositiveSoftAbsHamiltonianTrajectory"
      | none => IO.println "error invalidPositiveSoftAbsHamiltonianTrajectoryFieldCount"
  | .error error, _ | _, .error error => IO.println s!"error {error}"

private def printIRResult
    (result : Except CompilerIR.RuntimeError (Nat × List DrawEvent)) : IO Unit :=
  match result with
  | .ok (state, remaining) => IO.println s!"ok {state} {remaining.length}"
  | .error error => IO.println s!"error {repr error}"

private def runCategorical (weightsText drawText : String) : IO Unit := do
  match parseWeights weightsText, parseNat drawText with
  | .ok weights, .ok draw =>
      let total := weights.sum
      match CompilerIR.runCategorical weights [⟨total, draw⟩] with
      | .ok (index, _) => IO.println s!"ok {index}"
      | .error error => IO.println s!"error {repr error}"
  | .error error, _ | _, .error error => IO.println s!"error {error}"

private def runMH (stateText proposalText : String) (acceptText : Option String) : IO Unit := do
  match parseNat stateText, parseNat proposalText with
  | .ok state, .ok proposalDraw =>
      if hstate : state < 2 then
        let current : Fin 2 := ⟨state, hstate⟩
        if hproposal : proposalDraw < 2 then
          let baseTrace := [DrawEvent.mk 2 proposalDraw]
          let traceResult : Except String (List DrawEvent) :=
            if proposalDraw = state then
              .ok baseTrace
            else
              match acceptText with
              | none => .error "missing acceptance draw"
              | some text => do
                  let acceptDraw ← parseNat text
                  let proposed : Fin 2 := ⟨proposalDraw, hproposal⟩
                  let upper :=
                    Mcmc.Executable.Finite.TwoState.proposal.acceptanceUpper
                      Mcmc.Executable.Finite.TwoState.target current proposed
                  .ok (baseTrace ++ [DrawEvent.mk upper acceptDraw])
          match traceResult with
          | .error error => IO.println s!"error {error}"
          | .ok trace =>
              printIRResult (CompilerIR.runMetropolisHastings
                [1, 3] [[1, 1], [1, 1]] current.val trace)
        else
          IO.println s!"error outOfRange 2 {proposalDraw}"
      else
        IO.println s!"error invalidState {state}"
  | .error error, _ | _, .error error => IO.println s!"error {error}"

private def runGenericMH (targetText rowsText stateText proposalText : String)
    (acceptText : Option String) : IO Unit := do
  match parseWeights targetText, parseRows rowsText, parseNat stateText,
      parseNat proposalText with
  | .ok target, .ok rows, .ok state, .ok proposalDraw =>
      let stateCount := target.length
      if stateCount = 0 || target.any (· = 0) then
        IO.println "error targetWeightsMustBePositive"
      else if rows.length != stateCount || rows.any (fun row ↦
          row.length != stateCount || row.sum = 0) then
        IO.println "error invalidProposalDimensionsOrTotal"
      else if _hstate : state < stateCount then
        let targetArray := target.toArray
        let rowArrays := (rows.map List.toArray).toArray
        let currentRow := rowArrays[state]!
        let currentTotal := currentRow.toList.sum
        if _hdraw : proposalDraw < currentTotal then
          match selectFromList currentRow.toList proposalDraw with
          | none => IO.println "error internalSelectionFailure"
          | some proposed =>
              if proposed = state then
                printIRResult (CompilerIR.runMetropolisHastings target rows state
                  [⟨currentTotal, proposalDraw⟩])
              else
                match acceptText with
                | none => IO.println "error missing acceptance draw"
                | some text =>
                    match parseNat text with
                    | .error error => IO.println s!"error {error}"
                    | .ok acceptDraw =>
                        let proposedRow := rowArrays[proposed]!
                        let upper := targetArray[state]! * currentRow[proposed]! *
                          proposedRow.toList.sum
                        printIRResult (CompilerIR.runMetropolisHastings target rows state
                          [⟨currentTotal, proposalDraw⟩, ⟨upper, acceptDraw⟩])
        else
          IO.println s!"error outOfRange {currentTotal} {proposalDraw}"
      else
        IO.println s!"error invalidState {state}"
  | .error error, _, _, _ | _, .error error, _, _ |
      _, _, .error error, _ | _, _, _, .error error =>
      IO.println s!"error {error}"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["categorical", weights, draw] =>
      runCategorical weights draw
      return 0
  | ["mh", state, proposal] =>
      runMH state proposal none
      return 0
  | ["mh", state, proposal, accept] =>
      runMH state proposal (some accept)
      return 0
  | ["mh_generic", target, rows, state, proposal] =>
      runGenericMH target rows state proposal none
      return 0
  | ["mh_generic", target, rows, state, proposal, accept] =>
      runGenericMH target rows state proposal (some accept)
      return 0
  | "contraction_aposteriori" :: fields =>
      runContractionAposteriori fields
      return 0
  | "sincos_interval" :: fields =>
      runSinCosInterval fields
      return 0
  | "bounded_scalar_callbacks" :: fields =>
      runBoundedScalarCallbacks fields
      return 0
  | "bounded_scalar_callback_trace" :: fields =>
      runBoundedScalarCallbackTrace fields
      return 0
  | "bounded_scalar_affine_update" :: fields =>
      runBoundedScalarAffineUpdate fields
      return 0
  | "bounded_scalar_solver_contraction" :: fields =>
      runBoundedScalarSolverContraction fields
      return 0
  | "bounded_scalar_solver_phase" :: fields =>
      runBoundedScalarSolverPhase fields
      return 0
  | "bounded_scalar_solver_endpoint" :: fields =>
      runBoundedScalarSolverEndpoint fields
      return 0
  | "bounded_scalar_linked_solver_trajectory" :: fields =>
      runBoundedScalarLinkedSolverTrajectory fields
      return 0
  | "bounded_scalar_step_regional" :: fields =>
      runBoundedScalarStepRegional fields
      return 0
  | "bounded_scalar_endpoint_energy" :: fields =>
      runBoundedScalarEndpointEnergy fields
      return 0
  | "bounded_scalar_two_endpoint_energy" :: fields =>
      runBoundedScalarTwoEndpointEnergy fields
      return 0
  | "bounded_scalar_two_endpoint_weight" :: fields =>
      runBoundedScalarTwoEndpointWeight fields
      return 0
  | "rounded_contraction_residual" :: fields =>
      runRoundedContractionResidual fields
      return 0
  | "rounded_affine_update" :: fields =>
      runRoundedAffineUpdate fields
      return 0
  | "rounded_contraction_pair" :: fields =>
      runRoundedContractionPair fields
      return 0
  | ["gaussian_certificate", input, value, derivative, hessian, valueError,
      derivativeError, hessianError] =>
      runGaussianCertificate input value derivative hessian valueError
        derivativeError hessianError
      return 0
  | ["quartic_certificate", input, value, derivative, hessian, valueError,
      derivativeError, hessianError] =>
      runQuarticCertificate input value derivative hessian valueError
        derivativeError hessianError
      return 0
  | ["gaussian_dyadic_leapfrog", step, position, momentum, half,
      nextPosition, nextMomentum] =>
      runGaussianDyadicLeapfrog step position momentum half nextPosition
        nextMomentum
      return 0
  | ["gaussian_rounded_leapfrog", step, position, momentum, half,
      nextPosition, nextMomentum, halfError, positionError, momentumError] =>
      runGaussianRoundedLeapfrog step position momentum half nextPosition
        nextMomentum halfError positionError momentumError
      return 0
  | "rounded_gaussian_four_leaf" :: fields =>
      runRoundedGaussianFourLeaf fields
      return 0
  | "rounded_leapfrog" :: fields =>
      runRoundedLeapfrog fields
      return 0
  | "unit_zero_softabs" :: fields =>
      runUnitZeroSoftAbs fields
      return 0
  | "sqrt_interval" :: fields =>
      runSqrtInterval fields
      return 0
  | "reciprocal_residual" :: fields =>
      runReciprocalResidual fields
      return 0
  | "sqrt_reciprocal" :: fields =>
      runSqrtReciprocal fields
      return 0
  | "log_interval" :: fields =>
      runLogInterval fields
      return 0
  | "exp_nonpositive" :: fields =>
      runExpNonpositive fields
      return 0
  | "exp_nonpositive_transport" :: fields =>
      runExpNonpositiveTransport fields
      return 0
  | "exp_nonpositive_transport_trajectory" :: count :: fields =>
      runExpNonpositiveTransportTrajectory count fields
      return 0
  | "rounded_cumulative" :: count :: fields =>
      runRoundedCumulative count fields
      return 0
  | "scaled_draw" :: fields =>
      runScaledDraw fields
      return 0
  | "multinomial_decision" :: fields =>
      runMultinomialDecision fields
      return 0
  | "positive_softabs" :: fields =>
      runPositiveSoftAbs fields
      return 0
  | "positive_softabs_metric" :: fields =>
      runPositiveSoftAbsMetric fields
      return 0
  | "positive_softabs_metric_upper" :: fields =>
      runPositiveSoftAbsMetricUpper fields
      return 0
  | "positive_softabs_hamiltonian" :: fields =>
      runPositiveSoftAbsHamiltonian fields
      return 0
  | "positive_softabs_hamiltonian_upper" :: fields =>
      runPositiveSoftAbsHamiltonianUpper fields
      return 0
  | "positive_softabs_endpoint_state_transport" :: fields =>
      runPositiveSoftAbsEndpointStateTransport fields
      return 0
  | "positive_softabs_hamiltonian_trajectory" :: count :: fields =>
      runPositiveSoftAbsHamiltonianTrajectory count fields
      return 0
  | _ =>
      IO.eprintln usage
      return 2
