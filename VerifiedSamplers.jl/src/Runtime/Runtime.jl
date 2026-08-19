module Runtime

using Random

export AbstractRandomSource, RNGSource, TraceSource, FloatTraceSource,
    NormalEvent, UniformEvent, IndexEvent, draw_below!, standard_normal!,
    uniform_unit!, remaining, checked_positive_float, checked_positive_count,
    checked_finite_float

"""Convert a public numeric parameter to a positive finite `Float64`."""
function checked_positive_float(value::Real, label::AbstractString)
    converted = Float64(value)
    isfinite(converted) && converted > 0.0 ||
        throw(ArgumentError("$label must be finite and positive"))
    converted
end

"""Convert a public count parameter to a positive machine integer."""
function checked_positive_count(value::Integer, label::AbstractString)
    value > 0 || throw(ArgumentError("$label must be positive"))
    Int(value)
end

"""Convert a scalar state to finite `Float64` runtime representation."""
function checked_finite_float(value::Real, label::AbstractString)
    converted = Float64(value)
    isfinite(converted) || throw(ArgumentError("$label must be finite"))
    converted
end

abstract type AbstractRandomSource end

struct RNGSource{R<:AbstractRNG} <: AbstractRandomSource
    rng::R
end


mutable struct TraceSource <: AbstractRandomSource
    values::Vector{BigInt}
    position::Int
    requested_bounds::Vector{BigInt}
end


TraceSource(values::AbstractVector{<:Integer}) =
    TraceSource(BigInt.(values), 1, BigInt[])

remaining(source::TraceSource) = length(source.values) - source.position + 1

abstract type FloatTraceEvent end
struct NormalEvent <: FloatTraceEvent
    value::Float64
end
struct UniformEvent <: FloatTraceEvent
    value::Float64
end
struct IndexEvent <: FloatTraceEvent
    value::BigInt
end
mutable struct FloatTraceSource <: AbstractRandomSource
    events::Vector{FloatTraceEvent}
    position::Int
end
FloatTraceSource(events::AbstractVector{<:FloatTraceEvent}) =
    FloatTraceSource(FloatTraceEvent[events...], 1)
remaining(source::FloatTraceSource) = length(source.events) - source.position + 1

standard_normal!(source::RNGSource) = randn(source.rng)
uniform_unit!(source::RNGSource) = rand(source.rng)

function standard_normal!(source::FloatTraceSource)
    source.position <= length(source.events) || throw(EOFError())
    event = source.events[source.position]
    event isa NormalEvent || throw(ArgumentError("expected a standard-normal trace event"))
    source.position += 1
    event.value
end

function uniform_unit!(source::FloatTraceSource)
    source.position <= length(source.events) || throw(EOFError())
    event = source.events[source.position]
    event isa UniformEvent || throw(ArgumentError("expected a unit-uniform trace event"))
    0.0 <= event.value < 1.0 || throw(ArgumentError("unit-uniform trace value is out of range"))
    source.position += 1
    event.value
end

function draw_below!(source::FloatTraceSource, upper::Integer)
    upper > 0 || throw(ArgumentError("draw bound must be positive"))
    source.position <= length(source.events) || throw(EOFError())
    event = source.events[source.position]
    event isa IndexEvent || throw(ArgumentError("expected an index trace event"))
    source.position += 1
    0 <= event.value < upper || throw(ArgumentError("trace draw is outside requested bound"))
    event.value
end

function draw_below!(source::RNGSource, upper::Integer)
    upper > 0 || throw(ArgumentError("draw bound must be positive"))
    rand(source.rng, big(0):(big(upper) - 1))
end

function draw_below!(source::TraceSource, upper::Integer)
    upper > 0 || throw(ArgumentError("draw bound must be positive"))
    source.position <= length(source.values) || throw(EOFError())
    push!(source.requested_bounds, big(upper))
    value = source.values[source.position]
    source.position += 1
    0 <= value < upper || throw(ArgumentError("trace draw is outside requested bound"))
    value
end

end
