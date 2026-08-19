module TraceConformance

using VerifiedSamplers

const Runtime = VerifiedSamplers.Runtime

export TraceComparison, replay_float_pair, conforms

"""Result and trace-consumption evidence for two executions of one event list."""
struct TraceComparison{R,O}
    reference::R
    optimized::O
    reference_remaining::Int
    optimized_remaining::Int
end

"""Replay identical floating-point primitive events through two implementations."""
function replay_float_pair(events::AbstractVector{<:Runtime.FloatTraceEvent},
        reference_step, optimized_step)
    reference_source = Runtime.FloatTraceSource(events)
    optimized_source = Runtime.FloatTraceSource(events)
    reference = reference_step(reference_source)
    optimized = optimized_step(optimized_source)
    TraceComparison(reference, optimized, Runtime.remaining(reference_source),
        Runtime.remaining(optimized_source))
end

"""Whether results agree and both paths consume the expected number of events."""
function conforms(comparison::TraceComparison; remaining::Integer=0)
    comparison.optimized == comparison.reference &&
        comparison.reference_remaining == remaining &&
        comparison.optimized_remaining == remaining
end


end
