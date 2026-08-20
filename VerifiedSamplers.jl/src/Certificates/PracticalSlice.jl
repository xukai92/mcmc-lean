"""Checked comparison margins for one finite stepping-out/shrinkage trace.

The supplied ideals and bounds remain proof inputs. When `is_stable` holds,
Lean's `SliceComparisonCertificate.lt_threshold_eq`, `le_threshold_eq`, and
`ge_threshold_eq` theorems prove the corresponding strict, endpoint-stop, and
proposal-accept comparisons agree with ideal-real execution. Joining those
pointwise results to a concrete runtime trace still requires matching its
comparison order and kind.
"""
struct SliceComparisonCertificate
    threshold::BoundWitness
    values::Vector{BoundWitness}
    minimum_margin::BigFloat
    maximum_uncertainty::BigFloat
end

is_stable(certificate::SliceComparisonCertificate) =
    certificate.maximum_uncertainty < certificate.minimum_margin
uncertainty_band(certificate::SliceComparisonCertificate) =
    certificate.maximum_uncertainty

function certify_slice_comparisons(computed_threshold::Real,
        ideal_threshold::Real, threshold_bound::Real,
        computed_values::AbstractVector{<:Real},
        ideal_values::AbstractVector{<:Real},
        value_bounds::AbstractVector{<:Real}; precision::Integer=256)
    length(computed_values) == length(ideal_values) == length(value_bounds) ||
        throw(DimensionMismatch("value and bound vectors must have equal length"))
    isempty(computed_values) &&
        throw(ArgumentError("a slice trace must contain at least one comparison"))
    threshold = certify_bound(computed_threshold, ideal_threshold,
        threshold_bound; precision=precision)
    values = [certify_bound(computed_values[index], ideal_values[index],
        value_bounds[index]; precision=precision) for index in eachindex(computed_values)]
    setprecision(BigFloat, precision) do
        minimum_margin = minimum(abs(witness.ideal - threshold.ideal)
            for witness in values)
        maximum_uncertainty = maximum(witness.bound + threshold.bound
            for witness in values)
        SliceComparisonCertificate(threshold, values, minimum_margin,
            maximum_uncertainty)
    end
end

@enum SliceComparisonKind begin
    StrictBelow
    StopBelow
    AcceptAbove
end

"""Ordered practical-slice decisions paired with their margin certificate.

The kind vector has exactly one entry per observed callback comparison. It is
the runtime counterpart of Lean's `SliceComparisonKind` schedule in
`SliceComparisonCertificate.decisionTrace_eq`.
"""
struct SliceDecisionTraceCertificate
    comparisons::SliceComparisonCertificate
    kinds::Vector{SliceComparisonKind}
    computed_decisions::Vector{Bool}
    ideal_decisions::Vector{Bool}
end

"""Checked decomposition of `logdensity(current) + log(u)`.

The callback, logarithm, and final rounded addition are checked separately.
The `threshold` witness uses their summed bound, matching Lean's
`SliceThresholdCertificate.threshold_bound` theorem.
"""
struct SliceThresholdCertificate
    base::BoundWitness
    log_uniform::BoundWitness
    addition::BoundWitness
    threshold::BoundWitness
end

"""Guarded transport of one observed unit-uniform draw through `log`.

`log_of_computed_uniform` and `log_of_ideal_uniform` are exact-real oracle
inputs. Construction checks the RNG-input and local-log bounds and applies the
proved `local + input/lower` transport factor; it does not claim platform
`BigFloat` or `libm` is itself such an oracle.
"""
struct SliceLogUniformCertificate
    uniform::BoundWitness
    local_log::BoundWitness
    log::BoundWitness
    lower::BigFloat
end

function certify_slice_log_uniform(computed_uniform::Real,
        ideal_uniform::Real, uniform_bound::Real, computed_log::Real,
        log_of_computed_uniform::Real, local_log_bound::Real,
        log_of_ideal_uniform::Real, lower::Real; precision::Integer=256)
    uniform = certify_bound(computed_uniform, ideal_uniform, uniform_bound;
        precision=precision)
    local_log = certify_bound(computed_log, log_of_computed_uniform,
        local_log_bound; precision=precision)
    setprecision(BigFloat, precision) do
        guarded_lower = BigFloat(lower)
        isfinite(guarded_lower) && guarded_lower > 0 || throw(ArgumentError(
            "slice logarithm lower bound must be finite and positive"))
        guarded_lower <= BigFloat(uniform.computed) &&
            guarded_lower <= uniform.ideal || throw(ArgumentError(
            "slice uniform values must satisfy the positive lower bound"))
        transported_bound = local_log.bound + uniform.bound / guarded_lower
        log_witness = certify_bound(computed_log, log_of_ideal_uniform,
            transported_bound; precision=precision)
        SliceLogUniformCertificate(uniform, local_log, log_witness,
            guarded_lower)
    end
end

function certify_slice_threshold(computed_base::Real, ideal_base::Real,
        base_bound::Real, computed_log::Real, ideal_log::Real,
        log_bound::Real, computed_threshold::Real, addition_bound::Real;
        precision::Integer=256)
    base = certify_bound(computed_base, ideal_base, base_bound;
        precision=precision)
    log_uniform = certify_bound(computed_log, ideal_log, log_bound;
        precision=precision)
    addition_ideal = setprecision(BigFloat, precision) do
        BigFloat(base.computed) + BigFloat(log_uniform.computed)
    end
    addition = certify_bound(computed_threshold, addition_ideal,
        addition_bound; precision=precision)
    setprecision(BigFloat, precision) do
        ideal_threshold = base.ideal + log_uniform.ideal
        total_bound = addition.bound + base.bound + log_uniform.bound
        threshold = certify_bound(computed_threshold, ideal_threshold,
            total_bound; precision=precision)
        SliceThresholdCertificate(base, log_uniform, addition, threshold)
    end
end

function certify_slice_threshold(computed_base::Real, ideal_base::Real,
        base_bound::Real, log_uniform::SliceLogUniformCertificate,
        computed_threshold::Real, addition_bound::Real;
        precision::Integer=256)
    certify_slice_threshold(computed_base, ideal_base, base_bound,
        log_uniform.log.computed, log_uniform.log.ideal,
        log_uniform.log.bound, computed_threshold, addition_bound;
        precision=precision)
end

function _slice_decision(kind::SliceComparisonKind, value, threshold)
    kind == StrictBelow && return value < threshold
    kind == StopBelow && return value <= threshold
    threshold <= value
end

function certify_slice_decision_trace(kinds::AbstractVector{SliceComparisonKind},
        computed_threshold::Real, ideal_threshold::Real, threshold_bound::Real,
        computed_values::AbstractVector{<:Real},
        ideal_values::AbstractVector{<:Real},
        value_bounds::AbstractVector{<:Real}; precision::Integer=256)
    length(kinds) == length(computed_values) || throw(DimensionMismatch(
        "comparison kinds and values must have equal length"))
    comparisons = certify_slice_comparisons(computed_threshold,
        ideal_threshold, threshold_bound, computed_values, ideal_values,
        value_bounds; precision=precision)
    ordered_kinds = collect(kinds)
    computed = [_slice_decision(kind, witness.computed,
        comparisons.threshold.computed)
        for (kind, witness) in zip(ordered_kinds, comparisons.values)]
    ideal = [_slice_decision(kind, witness.ideal,
        comparisons.threshold.ideal)
        for (kind, witness) in zip(ordered_kinds, comparisons.values)]
    SliceDecisionTraceCertificate(comparisons, ordered_kinds, computed, ideal)
end

function certify_slice_decision_trace(kinds::AbstractVector{SliceComparisonKind},
        threshold::SliceThresholdCertificate,
        computed_values::AbstractVector{<:Real},
        ideal_values::AbstractVector{<:Real},
        value_bounds::AbstractVector{<:Real}; precision::Integer=256)
    certify_slice_decision_trace(kinds, threshold.threshold.computed,
        threshold.threshold.ideal, threshold.threshold.bound,
        computed_values, ideal_values, value_bounds; precision=precision)
end

is_stable(certificate::SliceDecisionTraceCertificate) =
    is_stable(certificate.comparisons) &&
    certificate.computed_decisions == certificate.ideal_decisions
uncertainty_band(certificate::SliceDecisionTraceCertificate) =
    uncertainty_band(certificate.comparisons)

"""Return the common checked decision trace, or fail closed at a boundary."""
certified_slice_decisions(certificate::SliceDecisionTraceCertificate) =
    is_stable(certificate) ? copy(certificate.computed_decisions) : nothing
