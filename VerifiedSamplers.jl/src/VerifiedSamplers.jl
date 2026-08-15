module VerifiedSamplers

using Random
import Base: step

include("Runtime/Runtime.jl")
include("Reference/Reference.jl")
include("Optimized/Optimized.jl")

export FiniteWeights, FiniteKernelWeights, FiniteMH, TwoStateMH, GaussianRWMH, sample

struct GaussianRWMH{F}
    logdensity::F
    scale::Float64
    function GaussianRWMH(logdensity::F, scale::Real) where {F}
        converted = Float64(scale)
        isfinite(converted) && converted > 0.0 ||
            throw(ArgumentError("scale must be finite and positive"))
        new{F}(logdensity, converted)
    end
end

function step(rng::AbstractRNG, sampler::GaussianRWMH, current::Real)
    source = Runtime.RNGSource(rng)
    Reference.gaussian_rwmh_step!(source, sampler.logdensity,
        sampler.scale, Float64(current))
end

step(sampler::GaussianRWMH, current::Real) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::GaussianRWMH, initial::Real, count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    samples = Vector{Float64}(undef, count)
    current = Float64(initial)
    for index in eachindex(samples)
        current = step(rng, sampler, current)
        samples[index] = current
    end
    samples
end

sample(sampler::GaussianRWMH, initial::Real, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)

struct FiniteWeights
    weights::Vector{BigInt}
    function FiniteWeights(weights::AbstractVector{<:Integer})
        isempty(weights) && throw(ArgumentError("weights cannot be empty"))
        any(<(0), weights) && throw(ArgumentError("weights must be nonnegative"))
        sum(big, weights) > 0 || throw(ArgumentError("weights must have positive total"))
        new(BigInt.(weights))
    end
end

function sample(rng::AbstractRNG, target::FiniteWeights)
    source = Runtime.RNGSource(rng)
    Reference.categorical_index!(source, target.weights) + 1
end

sample(target::FiniteWeights) = sample(Random.default_rng(), target)

function sample(rng::AbstractRNG, target::FiniteWeights, count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    [sample(rng, target) for _ in 1:count]
end

sample(target::FiniteWeights, count::Integer) =
    sample(Random.default_rng(), target, count)

struct FiniteKernelWeights
    rows::Vector{Vector{BigInt}}
    function FiniteKernelWeights(rows::AbstractVector{<:AbstractVector{<:Integer}})
        isempty(rows) && throw(ArgumentError("proposal cannot be empty"))
        state_count = length(rows)
        converted = [BigInt.(row) for row in rows]
        all(row -> length(row) == state_count, converted) ||
            throw(DimensionMismatch("proposal must be square"))
        all(row -> all(weight -> weight >= 0, row), converted) ||
            throw(ArgumentError("proposal weights must be nonnegative"))
        all(row -> sum(row) > 0, converted) ||
            throw(ArgumentError("every proposal row must have positive total"))
        new(converted)
    end
end

FiniteKernelWeights(matrix::AbstractMatrix{<:Integer}) =
    FiniteKernelWeights([collect(row) for row in eachrow(matrix)])

struct FiniteMH
    target::FiniteWeights
    proposal::FiniteKernelWeights
    function FiniteMH(target::FiniteWeights, proposal::FiniteKernelWeights)
        all(weight -> weight > 0, target.weights) ||
            throw(ArgumentError("finite MH target weights must be strictly positive"))
        length(target.weights) == length(proposal.rows) ||
            throw(DimensionMismatch("target and proposal state counts differ"))
        new(target, proposal)
    end
end

function step(rng::AbstractRNG, sampler::FiniteMH, current::Integer)
    state_count = length(sampler.target.weights)
    1 <= current <= state_count || throw(ArgumentError("current state is out of range"))
    source = Runtime.RNGSource(rng)
    Reference.finite_mh_step!(source, sampler.target.weights,
        sampler.proposal.rows, current - 1) + 1
end

step(sampler::FiniteMH, current::Integer) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::FiniteMH, initial::Integer, count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    samples = Vector{Int}(undef, count)
    current = Int(initial)
    for index in eachindex(samples)
        current = step(rng, sampler, current)
        samples[index] = current
    end
    samples
end

sample(sampler::FiniteMH, initial::Integer, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)

struct TwoStateMH end

function step(rng::AbstractRNG, ::TwoStateMH, current::Bool)
    source = Runtime.RNGSource(rng)
    Bool(Reference.two_state_mh_step!(source, Int(current)))
end

step(sampler::TwoStateMH, current::Bool) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::TwoStateMH, initial::Bool, count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    samples = Vector{Bool}(undef, count)
    current = initial
    for index in eachindex(samples)
        current = step(rng, sampler, current)
        samples[index] = current
    end
    samples
end

sample(sampler::TwoStateMH, initial::Bool, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)

end
