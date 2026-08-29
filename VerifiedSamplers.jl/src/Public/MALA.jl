"""Metropolis-adjusted Langevin algorithm with an isotropic proposal.

`step_size` is the proposal standard deviation: the proposal mean is
`q + step_size^2 / 2 * gradient(q)`. Set `implementation=:reference` to
interpret Lean-emitted IR or `:optimized` for the independently maintained,
generic Julia implementation.
"""
struct MALA{T<:AbstractFloat,F,G}
    logdensity::F
    gradient::G
    step_size::T
    implementation::Symbol
    function MALA(logdensity::F, gradient::G, step_size::T;
            implementation::Symbol=:reference) where {T<:AbstractFloat,F,G}
        isfinite(step_size) && step_size > zero(T) || throw(ArgumentError(
            "step size must be finite and positive"))
        implementation in (:reference, :optimized) || throw(ArgumentError(
            "implementation must be :reference or :optimized"))
        new{T,F,G}(logdensity, gradient, step_size, implementation)
    end
end

function step(rng::AbstractRNG, sampler::MALA{T},
        current::AbstractFloat) where {T<:AbstractFloat}
    source = Runtime.RNGSource(rng)
    state = T(current)
    sampler.implementation === :reference ?
        T(Reference.scalar_mala_step!(source, sampler.logdensity, sampler.gradient,
            Float64(sampler.step_size), Float64(state))) :
        Optimized.scalar_mala_step!(source, sampler.logdensity, sampler.gradient,
            sampler.step_size, state)
end

function step(rng::AbstractRNG, sampler::MALA{T},
        current::AbstractVector{<:AbstractFloat}) where {T<:AbstractFloat}
    source = Runtime.RNGSource(rng)
    state = T.(current)
    sampler.implementation === :reference ?
        T.(Reference.vector_mala_step!(source, sampler.logdensity, sampler.gradient,
            Float64(sampler.step_size), Float64.(state))) :
        Optimized.vector_mala_step!(source, sampler.logdensity, sampler.gradient,
            sampler.step_size, state)
end

step(sampler::MALA, current) = step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::MALA{T}, initial::AbstractFloat,
        count::Integer) where {T<:AbstractFloat}
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    samples = Vector{T}(undef, count)
    current = T(initial)
    for index in eachindex(samples)
        current = step(rng, sampler, current)
        samples[index] = current
    end
    samples
end

function sample(rng::AbstractRNG, sampler::MALA{T},
        initial::AbstractVector{<:AbstractFloat}, count::Integer) where {T<:AbstractFloat}
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    current = T.(initial)
    samples = Matrix{T}(undef, length(current), count)
    for index in axes(samples, 2)
        current = step(rng, sampler, current)
        samples[:, index] = current
    end
    samples
end

sample(sampler::MALA, initial, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)
