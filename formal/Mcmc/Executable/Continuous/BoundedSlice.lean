import Mcmc.Executable.Continuous.PositiveTransformRefinement

/-!
# Bounded numerical refinement for practical slice comparisons

Stepping out and shrinkage are controlled by comparisons of a log-density
evaluation with one sampled log height. This module isolates the
backend-independent finite-error argument: if every ideal comparison is
separated from its boundary by more than the accumulated callback and
threshold errors, finite-precision execution makes exactly the same sequence
of expand, shrink, and accept decisions.

This theorem does not assert bounds for Julia, `Float64`, `log`, or a user
callback. A concrete backend must supply the fields of the certificate.
-/

namespace Mcmc.Executable.Continuous

/-- Guarded transport from a computed unit-uniform draw through a backend
logarithm. A positive lower bound avoids the singularity at zero. -/
structure SliceLogUniformCertificate where
  computedUniform : ℝ
  idealUniform : ℝ
  uniformError : ℝ
  computedLog : ℝ
  localLogError : ℝ
  lower : ℝ
  uniform_bound : Approximates computedUniform idealUniform uniformError
  local_log_bound :
    Approximates computedLog (Real.log computedUniform) localLogError
  lower_pos : 0 < lower
  computed_lower : lower ≤ computedUniform
  ideal_lower : lower ≤ idealUniform

/-- RNG-input error and local logarithm error compose into the ideal sampled
log-uniform value. -/
theorem SliceLogUniformCertificate.log_bound
    (certificate : SliceLogUniformCertificate) :
    Approximates certificate.computedLog
      (Real.log certificate.idealUniform)
      (certificate.localLogError +
        certificate.uniformError / certificate.lower) :=
  log_backend_approximates_of_lower certificate.local_log_bound
    certificate.uniform_bound certificate.lower_pos
    certificate.computed_lower certificate.ideal_lower

/-- Operation-local evidence for the sampled log-height
`logDensity(current) + log(u)`. The final addition may itself be rounded, so
its error is kept separate from callback and logarithm errors. -/
structure SliceThresholdCertificate where
  computedBase : ℝ
  idealBase : ℝ
  baseError : ℝ
  computedLog : ℝ
  idealLog : ℝ
  logError : ℝ
  computedThreshold : ℝ
  additionError : ℝ
  base_bound : Approximates computedBase idealBase baseError
  log_bound : Approximates computedLog idealLog logError
  addition_bound :
    Approximates computedThreshold (computedBase + computedLog) additionError

/-- Assemble a sampled-height certificate directly from a callback bound, a
guarded uniform-through-log certificate, and the final addition bound. -/
noncomputable def SliceThresholdCertificate.ofLogUniform
    (computedBase idealBase baseError computedThreshold additionError : ℝ)
    (hbase : Approximates computedBase idealBase baseError)
    (logUniform : SliceLogUniformCertificate)
    (haddition : Approximates computedThreshold
      (computedBase + logUniform.computedLog) additionError) :
    SliceThresholdCertificate where
  computedBase := computedBase
  idealBase := idealBase
  baseError := baseError
  computedLog := logUniform.computedLog
  idealLog := Real.log logUniform.idealUniform
  logError := logUniform.localLogError +
    logUniform.uniformError / logUniform.lower
  computedThreshold := computedThreshold
  additionError := additionError
  base_bound := hbase
  log_bound := logUniform.log_bound
  addition_bound := haddition

/-- Callback, logarithm, and final-addition errors add to the complete sampled
log-height error. -/
theorem SliceThresholdCertificate.threshold_bound
    (certificate : SliceThresholdCertificate) :
    Approximates certificate.computedThreshold
      (certificate.idealBase + certificate.idealLog)
      (certificate.additionError + certificate.baseError +
        certificate.logError) := by
  have hinputs := certificate.base_bound.add certificate.log_bound
  have h := certificate.addition_bound.compose hinputs
  simpa [add_assoc] using h

/-- The direct uniform-to-threshold assembly exposes exactly the callback,
local-log, RNG-input, and final-addition error terms. -/
theorem SliceThresholdCertificate.ofLogUniform_threshold_bound
    (computedBase idealBase baseError computedThreshold additionError : ℝ)
    (hbase : Approximates computedBase idealBase baseError)
    (logUniform : SliceLogUniformCertificate)
    (haddition : Approximates computedThreshold
      (computedBase + logUniform.computedLog) additionError) :
    Approximates computedThreshold
      (idealBase + Real.log logUniform.idealUniform)
      (additionError + baseError +
        (logUniform.localLogError +
          logUniform.uniformError / logUniform.lower)) :=
  (SliceThresholdCertificate.ofLogUniform computedBase idealBase baseError
    computedThreshold additionError hbase logUniform haddition).threshold_bound

/-- Error data for all log-density/height comparisons in one finite practical
slice trace. The list contains stepping-out endpoint evaluations followed by
shrinkage proposal evaluations in execution order. -/
structure SliceComparisonCertificate where
  idealThreshold : ℝ
  computedThreshold : ℝ
  thresholdError : ℝ
  idealValues : List ℝ
  computedValues : List ℝ
  valueErrors : List ℝ
  sameLengthComputed : computedValues.length = idealValues.length
  sameLengthErrors : valueErrors.length = idealValues.length
  threshold_bound :
    Approximates computedThreshold idealThreshold thresholdError
  value_bound : ∀ index (hindex : index < idealValues.length),
    Approximates
      (computedValues.get ⟨index, sameLengthComputed.symm ▸ hindex⟩)
      (idealValues.get ⟨index, hindex⟩)
      (valueErrors.get ⟨index, sameLengthErrors.symm ▸ hindex⟩)
  decision_margin : ∀ index (hindex : index < idealValues.length),
    valueErrors.get ⟨index, sameLengthErrors.symm ▸ hindex⟩ + thresholdError <
      |idealValues.get ⟨index, hindex⟩ - idealThreshold|

/-- Assemble comparison evidence from a sampled-height certificate. The
threshold error is fixed to the exact callback/log/addition sum proved by that
certificate, so clients cannot weaken trace linkage by entering a different
number at this boundary. -/
def SliceComparisonCertificate.ofThreshold
    (threshold : SliceThresholdCertificate)
    (idealValues computedValues valueErrors : List ℝ)
    (sameLengthComputed : computedValues.length = idealValues.length)
    (sameLengthErrors : valueErrors.length = idealValues.length)
    (valueBound : ∀ index (hindex : index < idealValues.length),
      Approximates
        (computedValues.get ⟨index, sameLengthComputed.symm ▸ hindex⟩)
        (idealValues.get ⟨index, hindex⟩)
        (valueErrors.get ⟨index, sameLengthErrors.symm ▸ hindex⟩))
    (decisionMargin : ∀ index (hindex : index < idealValues.length),
      valueErrors.get ⟨index, sameLengthErrors.symm ▸ hindex⟩ +
          (threshold.additionError + threshold.baseError +
            threshold.logError) <
        |idealValues.get ⟨index, hindex⟩ -
          (threshold.idealBase + threshold.idealLog)|) :
    SliceComparisonCertificate where
  idealThreshold := threshold.idealBase + threshold.idealLog
  computedThreshold := threshold.computedThreshold
  thresholdError := threshold.additionError + threshold.baseError +
    threshold.logError
  idealValues := idealValues
  computedValues := computedValues
  valueErrors := valueErrors
  sameLengthComputed := sameLengthComputed
  sameLengthErrors := sameLengthErrors
  threshold_bound := threshold.threshold_bound
  value_bound := valueBound
  decision_margin := decisionMargin

/-- The three comparison forms used by stepping-out and shrinkage execution.
Recording the kind at every runtime comparison prevents a certificate for one
branch convention from being silently reused for another. -/
inductive SliceComparisonKind where
  | strictBelow
  | stopBelow
  | acceptAbove
  deriving DecidableEq, Repr

/-- Every strict `value < threshold` decision agrees between the computed and
ideal traces. -/
theorem SliceComparisonCertificate.lt_threshold_eq
    (certificate : SliceComparisonCertificate)
    (index : ℕ) (hindex : index < certificate.idealValues.length) :
    (certificate.computedValues.get
        ⟨index, certificate.sameLengthComputed.symm ▸ hindex⟩ <
      certificate.computedThreshold) =
    (certificate.idealValues.get ⟨index, hindex⟩ <
      certificate.idealThreshold) :=
  comparison_eq_of_approximates
    (certificate.value_bound index hindex) certificate.threshold_bound
    (certificate.decision_margin index hindex)

/-- Every non-strict `value ≤ threshold` stepping-out stop decision agrees. -/
theorem SliceComparisonCertificate.le_threshold_eq
    (certificate : SliceComparisonCertificate)
    (index : ℕ) (hindex : index < certificate.idealValues.length) :
    (certificate.computedValues.get
        ⟨index, certificate.sameLengthComputed.symm ▸ hindex⟩ ≤
      certificate.computedThreshold) =
    (certificate.idealValues.get ⟨index, hindex⟩ ≤
      certificate.idealThreshold) := by
  have h := comparison_eq_of_approximates certificate.threshold_bound
    (certificate.value_bound index hindex) (by
      simpa [abs_sub_comm, add_comm] using certificate.decision_margin index hindex)
  simpa only [not_lt] using congrArg Not h

/-- Every `value ≥ threshold` shrinkage acceptance decision agrees. -/
theorem SliceComparisonCertificate.ge_threshold_eq
    (certificate : SliceComparisonCertificate)
    (index : ℕ) (hindex : index < certificate.idealValues.length) :
    (certificate.computedThreshold ≤
      certificate.computedValues.get
        ⟨index, certificate.sameLengthComputed.symm ▸ hindex⟩) =
    (certificate.idealThreshold ≤
      certificate.idealValues.get ⟨index, hindex⟩) := by
  have h := certificate.lt_threshold_eq index hindex
  simpa only [not_lt] using congrArg Not h

/-- Boolean decision made by the finite-precision execution at one recorded
slice comparison. -/
noncomputable def SliceComparisonCertificate.computedDecision
    (certificate : SliceComparisonCertificate)
    (kind : SliceComparisonKind)
    (index : Fin certificate.idealValues.length) : Bool :=
  match kind with
  | .strictBelow => decide
      (certificate.computedValues.get
          ⟨index, certificate.sameLengthComputed.symm ▸ index.isLt⟩ <
        certificate.computedThreshold)
  | .stopBelow => decide
      (certificate.computedValues.get
          ⟨index, certificate.sameLengthComputed.symm ▸ index.isLt⟩ ≤
        certificate.computedThreshold)
  | .acceptAbove => decide
      (certificate.computedThreshold ≤
        certificate.computedValues.get
          ⟨index, certificate.sameLengthComputed.symm ▸ index.isLt⟩)

/-- Corresponding ideal-real decision at one recorded slice comparison. -/
noncomputable def SliceComparisonCertificate.idealDecision
    (certificate : SliceComparisonCertificate)
    (kind : SliceComparisonKind)
    (index : Fin certificate.idealValues.length) : Bool :=
  match kind with
  | .strictBelow => decide
      (certificate.idealValues.get index < certificate.idealThreshold)
  | .stopBelow => decide
      (certificate.idealValues.get index ≤ certificate.idealThreshold)
  | .acceptAbove => decide
      (certificate.idealThreshold ≤ certificate.idealValues.get index)

/-- A certified comparison has the same Boolean outcome for every explicitly
recorded comparison kind. -/
theorem SliceComparisonCertificate.computedDecision_eq_idealDecision
    (certificate : SliceComparisonCertificate)
    (kind : SliceComparisonKind)
    (index : Fin certificate.idealValues.length) :
    certificate.computedDecision kind index =
      certificate.idealDecision kind index := by
  cases kind with
  | strictBelow =>
      simp only [computedDecision, idealDecision, decide_eq_decide]
      exact Iff.of_eq (certificate.lt_threshold_eq index index.isLt)
  | stopBelow =>
      simp only [computedDecision, idealDecision, decide_eq_decide]
      exact Iff.of_eq (certificate.le_threshold_eq index index.isLt)
  | acceptAbove =>
      simp only [computedDecision, idealDecision, decide_eq_decide]
      exact Iff.of_eq (certificate.ge_threshold_eq index index.isLt)

/-- Complete finite decision trace for a supplied comparison-kind schedule. -/
noncomputable def SliceComparisonCertificate.computedDecisionTrace
    (certificate : SliceComparisonCertificate)
    (kinds : Fin certificate.idealValues.length → SliceComparisonKind) :
    List Bool :=
  List.ofFn fun index => certificate.computedDecision (kinds index) index

/-- Ideal-real decision trace for the same comparison-kind schedule. -/
noncomputable def SliceComparisonCertificate.idealDecisionTrace
    (certificate : SliceComparisonCertificate)
    (kinds : Fin certificate.idealValues.length → SliceComparisonKind) :
    List Bool :=
  List.ofFn fun index => certificate.idealDecision (kinds index) index

/-- All expand, stop, and accept decisions agree once their execution order
and comparison kinds are recorded against the certificate. -/
theorem SliceComparisonCertificate.decisionTrace_eq
    (certificate : SliceComparisonCertificate)
    (kinds : Fin certificate.idealValues.length → SliceComparisonKind) :
    certificate.computedDecisionTrace kinds =
      certificate.idealDecisionTrace kinds := by
  simp only [computedDecisionTrace, idealDecisionTrace]
  congr 1
  funext index
  exact certificate.computedDecision_eq_idealDecision (kinds index) index

end Mcmc.Executable.Continuous
