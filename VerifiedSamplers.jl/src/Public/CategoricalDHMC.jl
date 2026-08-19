"""Coordinate-wise discontinuous HMC for a positive categorical target.

Categories are arranged on a cycle. Each update moves to the next or previous
category, corresponding to the paper's `epsilon = mass` specialization.
"""
struct CategoricalDHMC
    probabilities::Vector{Float64}
    steps::Int
    function CategoricalDHMC(probabilities::AbstractVector{<:Real},
            steps::Integer=1)
        converted = Float64.(probabilities)
        length(converted) >= 2 || throw(ArgumentError(
            "DHMC needs at least two categories"))
        all(x -> isfinite(x) && x > 0, converted) || throw(ArgumentError(
            "category probabilities must be finite and positive"))
        steps > 0 || throw(ArgumentError(
            "trajectory length must be positive"))
        new(converted, Int(steps))
    end
end

function step(rng::AbstractRNG, sampler::CategoricalDHMC, current::Integer)
    Reference.categorical_dhmc_step!(Runtime.RNGSource(rng),
        sampler.probabilities, sampler.steps, current)
end

step(sampler::CategoricalDHMC, current::Integer) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::CategoricalDHMC,
        initial::Integer, count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    states = Vector{Int}(undef, count)
    current = Int(initial)
    for index in eachindex(states)
        current = step(rng, sampler, current)
        states[index] = current
    end
    states
end

sample(sampler::CategoricalDHMC, initial::Integer, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)
