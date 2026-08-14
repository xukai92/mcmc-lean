module Runtime

using Random

export AbstractRandomSource, RNGSource, TraceSource, draw_below!, remaining

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
