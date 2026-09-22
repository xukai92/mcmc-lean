"""Deterministic replay contracts shared by backend conformance tests."""
module Conformance

using ...Runtime

export CapturedFailure, ReplayResult, replay_pair, replay_integer_pair,
    conforms, conforms_numerical

"""A comparable failure outcome captured without hiding its type or message."""
struct CapturedFailure
    type::DataType
    message::String
end

"""Results, failures, and event consumption from two executions."""
struct ReplayResult{L,R}
    reference::L
    optimized::R
    reference_remaining::Int
    optimized_remaining::Int
    reference_evidence::Any
    optimized_evidence::Any
end

"""Replay one floating-point event list through any two backend operations."""
function replay_pair(events::AbstractVector{<:Runtime.FloatTraceEvent},
        left_step, right_step)
    reference_source = Runtime.FloatTraceSource(events)
    optimized_source = Runtime.FloatTraceSource(events)
    reference = try
        left_step(reference_source)
    catch error
        CapturedFailure(typeof(error), sprint(showerror, error))
    end
    optimized = try
        right_step(optimized_source)
    catch error
        CapturedFailure(typeof(error), sprint(showerror, error))
    end
    ReplayResult(reference, optimized, Runtime.remaining(reference_source),
        Runtime.remaining(optimized_source), nothing, nothing)
end

"""Replay an exact integer trace and also compare every requested bound."""
function replay_integer_pair(values::AbstractVector{<:Integer},
        reference_step, optimized_step)
    reference_source = Runtime.TraceSource(values)
    optimized_source = Runtime.TraceSource(values)
    reference = try
        reference_step(reference_source)
    catch error
        CapturedFailure(typeof(error), sprint(showerror, error))
    end
    optimized = try
        optimized_step(optimized_source)
    catch error
        CapturedFailure(typeof(error), sprint(showerror, error))
    end
    ReplayResult(reference, optimized, Runtime.remaining(reference_source),
        Runtime.remaining(optimized_source),
        copy(reference_source.requested_bounds),
        copy(optimized_source.requested_bounds))
end

"""Whether outcome and event consumption agree at the declared boundary."""
function conforms(result::ReplayResult; remaining::Integer=0)
    result.reference == result.optimized &&
        result.reference_remaining == remaining &&
        result.optimized_remaining == remaining &&
        result.reference_evidence == result.optimized_evidence
end

"""Numerical conformance: values within tolerance and event consumption agrees."""
function conforms_numerical(result::ReplayResult;
        atol::Real=1e-10, rtol::Real=1e-10, remaining::Integer=0)
    result.reference_remaining == remaining &&
        result.optimized_remaining == remaining || return false
    ref, opt = result.reference, result.optimized
    ref isa CapturedFailure && return opt isa CapturedFailure
    opt isa CapturedFailure && return false
    _values_close(ref, opt, atol, rtol)
end

_values_close(a::Real, b::Real, atol, rtol) =
    abs(a - b) <= atol + rtol * abs(a)

_values_close(a::AbstractVector, b::AbstractVector, atol, rtol) =
    length(a) == length(b) &&
    all(i -> _values_close(a[i], b[i], atol, rtol), eachindex(a))

_values_close(a, b, _, _) = a == b

end
