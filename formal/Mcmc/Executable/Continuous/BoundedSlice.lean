import Mcmc.Executable.Continuous.BoundedRWMH

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

end Mcmc.Executable.Continuous
