"""Dense Lebesgue-correct position-dependent MALA.

`gradient` is `∇logπ`. `metric(q)` returns the positive-definite matrix `G(q)`
and `metric_derivative(q)[:, :, j]` returns `∂G(q)/∂q[j]`. The proposal has
covariance `step_size^2 * inv(G(q))` and includes the inverse-metric divergence
in its mean.
"""
struct DensePMALA{T<:AbstractFloat,L,S,M,D}
    logdensity::L
    gradient::S
    metric::M
    metric_derivative::D
    step_size::T
    implementation::Symbol
    function DensePMALA(logdensity::L, gradient::S, metric::M,
            metric_derivative::D, step_size::T;
            implementation::Symbol=:reference) where
            {T<:AbstractFloat,L,S,M,D}
        isfinite(step_size) && step_size > zero(T) || throw(ArgumentError(
            "step size must be finite and positive"))
        implementation in (:reference, :optimized) || throw(ArgumentError(
            "implementation must be :reference or :optimized"))
        new{T,L,S,M,D}(logdensity, gradient, metric, metric_derivative,
            step_size, implementation)
    end
end

function step(rng::AbstractRNG, sampler::DensePMALA{T},
        current::AbstractVector{<:AbstractFloat}) where {T<:AbstractFloat}
    source = Runtime.RNGSource(rng)
    state = T.(current)
    if sampler.implementation === :reference
        return T.(Reference.dense_pmala_step!(source, sampler.logdensity,
            sampler.gradient, sampler.metric, sampler.metric_derivative,
            Float64(sampler.step_size), Float64.(state)))
    end
    Optimized.dense_pmala_step!(source, sampler.logdensity, sampler.gradient,
        sampler.metric, sampler.metric_derivative, sampler.step_size, state)
end

step(sampler::DensePMALA, current::AbstractVector{<:AbstractFloat}) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::DensePMALA{T},
        initial::AbstractVector{<:AbstractFloat}, count::Integer) where
        {T<:AbstractFloat}
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    current = T.(initial)
    draws = Matrix{T}(undef, length(current), count)
    for index in axes(draws, 2)
        current = step(rng, sampler, current)
        draws[:, index] = current
    end
    draws
end

sample(sampler::DensePMALA, initial::AbstractVector{<:AbstractFloat},
        count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)
