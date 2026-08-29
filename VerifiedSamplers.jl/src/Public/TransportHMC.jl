"""Hamiltonian Monte Carlo in user-supplied invertible coordinates.

`forward(z)` maps latent coordinates to the original state and `inverse(q)`
maps back. `pullback(z, v)` computes `J_forward(z)' * v`.
`logabsdetjac(z)` and `grad_logabsdetjac(z)` describe the same forward map.
The supplied `gradient(q)` is the gradient of the negative log density.

The map is held fixed while sampling. Approximation quality affects mixing,
whereas inconsistent inverse/Jacobian callbacks can invalidate the sampler.
"""
struct TransportHMC{T<:AbstractFloat,F,G,TF,TI,PB,LJ,GLJ}
    logdensity::F
    gradient::G
    forward::TF
    inverse::TI
    pullback::PB
    logabsdetjac::LJ
    grad_logabsdetjac::GLJ
    step_size::T
    steps::Int
    implementation::Symbol
end

function TransportHMC(logdensity::F, gradient::G, forward::TF, inverse::TI,
        pullback::PB, logabsdetjac::LJ, grad_logabsdetjac::GLJ,
        step_size::T, steps::Integer=10;
        implementation::Symbol=:reference) where
        {T<:AbstractFloat,F,G,TF,TI,PB,LJ,GLJ}
    isfinite(step_size) && step_size > zero(T) ||
        throw(ArgumentError("step size must be finite and positive"))
    steps > 0 || throw(ArgumentError("leapfrog steps must be positive"))
    implementation in (:reference, :optimized) || throw(ArgumentError(
        "implementation must be :reference or :optimized"))
    TransportHMC{T,F,G,TF,TI,PB,LJ,GLJ}(logdensity, gradient, forward,
        inverse, pullback, logabsdetjac, grad_logabsdetjac, step_size,
        Int(steps), implementation)
end

function _transport_callbacks(sampler::TransportHMC{T}) where {T}
    latent_logdensity = function(z)
        q = T.(sampler.forward(z))
        value = T(sampler.logdensity(q)) + T(sampler.logabsdetjac(z))
        isfinite(value) || throw(ArgumentError(
            "transformed log density must be finite"))
        value
    end
    latent_gradient = function(z)
        q = T.(sampler.forward(z))
        original_gradient = T.(sampler.gradient(q))
        pulled = T.(sampler.pullback(z, original_gradient))
        jacobian_gradient = T.(sampler.grad_logabsdetjac(z))
        length(pulled) == length(z) == length(jacobian_gradient) ||
            throw(DimensionMismatch("transport gradient"))
        result = pulled .- jacobian_gradient
        all(isfinite, result) || throw(ArgumentError(
            "transformed gradient must be finite"))
        result
    end
    latent_logdensity, latent_gradient
end

function step(rng::AbstractRNG, sampler::TransportHMC{T},
        current::AbstractVector{T}) where {T<:AbstractFloat}
    isempty(current) && throw(ArgumentError("position cannot be empty"))
    all(isfinite, current) || throw(ArgumentError("position must be finite"))
    latent = T.(sampler.inverse(current))
    length(latent) == length(current) || throw(DimensionMismatch(
        "inverse transport"))
    all(isfinite, latent) || throw(ArgumentError(
        "inverse transport must be finite"))
    latent_logdensity, latent_gradient = _transport_callbacks(sampler)
    source = Runtime.RNGSource(rng)
    next_latent = if sampler.implementation === :reference
        T === Float64 || throw(ArgumentError(
            "Reference transport HMC has a documented Float64 boundary"))
        Reference.vector_hmc_step!(source, latent_logdensity, latent_gradient,
            Float64(sampler.step_size), sampler.steps, latent)
    else
        Optimized.vector_hmc_step!(source, latent_logdensity, latent_gradient,
            sampler.step_size, sampler.steps, latent)
    end
    result = T.(sampler.forward(next_latent))
    length(result) == length(current) || throw(DimensionMismatch(
        "forward transport"))
    all(isfinite, result) || throw(ArgumentError(
        "forward transport must be finite"))
    result
end

step(sampler::TransportHMC, current::AbstractVector{<:AbstractFloat}) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::TransportHMC{T},
        initial::AbstractVector{T}, count::Integer) where {T<:AbstractFloat}
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    current = collect(initial)
    samples = Matrix{T}(undef, length(current), count)
    for index in axes(samples, 2)
        current = step(rng, sampler, current)
        samples[:, index] = current
    end
    samples
end

sample(sampler::TransportHMC, initial::AbstractVector{<:AbstractFloat},
        count::Integer) = sample(Random.default_rng(), sampler, initial, count)
