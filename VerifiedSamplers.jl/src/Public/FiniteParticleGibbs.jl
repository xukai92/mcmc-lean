"""Exact-integer bootstrap particle Gibbs for a finite hidden Markov model.

The path target is proportional to the initial weight followed by each
potential/transition factor. Potentials weight the state before each
transition, matching the formal finite Feynman--Kac convention.
"""
struct FiniteHMMParticleGibbs
    initial_weights::Vector{Int}
    transition_weights::Matrix{Int}
    potentials::Matrix{Int}
    particles::Int
    function FiniteHMMParticleGibbs(initial_weights::AbstractVector{<:Integer},
            transition_weights::AbstractMatrix{<:Integer},
            potentials::AbstractMatrix{<:Integer}, particles::Integer)
        converted_initial = Int.(initial_weights)
        converted_transition = Int.(transition_weights)
        converted_potentials = Int.(potentials)
        particles > 0 || throw(ArgumentError("particle count must be positive"))
        states = length(converted_initial)
        states > 0 || throw(ArgumentError("state space cannot be empty"))
        size(converted_transition) == (states, states) ||
            throw(DimensionMismatch("transition matrix"))
        size(converted_potentials, 2) == states ||
            throw(DimensionMismatch("potentials"))
        all(>=(0), converted_initial) && sum(converted_initial) > 0 ||
            throw(ArgumentError("invalid initial weights"))
        all(>=(0), converted_transition) &&
            all(row -> sum(row) > 0, eachrow(converted_transition)) ||
            throw(ArgumentError("invalid transition weights"))
        all(>(0), converted_potentials) ||
            throw(ArgumentError("potentials must be strictly positive"))
        new(converted_initial, converted_transition, converted_potentials,
            Int(particles))
    end
end

function step(rng::AbstractRNG, sampler::FiniteHMMParticleGibbs,
        current_path::AbstractVector{<:Integer})
    Reference.finite_hmm_particle_gibbs_step!(Runtime.RNGSource(rng),
        sampler.initial_weights, sampler.transition_weights, sampler.potentials,
        sampler.particles, current_path)
end

step(sampler::FiniteHMMParticleGibbs,
        current_path::AbstractVector{<:Integer}) =
    step(Random.default_rng(), sampler, current_path)

function sample(rng::AbstractRNG, sampler::FiniteHMMParticleGibbs,
        initial_path::AbstractVector{<:Integer}, count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    current = Int.(initial_path)
    paths = Matrix{Int}(undef, length(current), count)
    for index in axes(paths, 2)
        current = step(rng, sampler, current)
        paths[:, index] = current
    end
    paths
end

sample(sampler::FiniteHMMParticleGibbs,
        initial_path::AbstractVector{<:Integer}, count::Integer) =
    sample(Random.default_rng(), sampler, initial_path, count)
