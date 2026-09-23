"""Active-Sketch simplified manifold MALA with metric `G(x) = S(x)ᵀS(x) + λI`.

`gradient` is `∇logπ`. `sketch(q)` returns the M×d sketch matrix `S(q)`.
`regularization` is the scalar `λ > 0`. The proposal has covariance
`step_size^2 * inv(G(q))` with a simplified drift (no metric-derivative
divergence term).
"""
struct ActiveSketchSMMALA{T<:AbstractFloat,L,S,K}
    logdensity::L
    gradient::S
    sketch::K
    step_size::T
    regularization::T
    implementation::Symbol
    function ActiveSketchSMMALA(logdensity::L, gradient::S, sketch::K,
            step_size::T, regularization::T;
            implementation::Symbol=:reference) where
            {T<:AbstractFloat,L,S,K}
        isfinite(step_size) && step_size > zero(T) || throw(ArgumentError(
            "step size must be finite and positive"))
        isfinite(regularization) && regularization > zero(T) || throw(ArgumentError(
            "regularization must be finite and positive"))
        implementation in (:reference, :optimized) || throw(ArgumentError(
            "implementation must be :reference or :optimized"))
        new{T,L,S,K}(logdensity, gradient, sketch, step_size,
            regularization, implementation)
    end
end

function step(rng::AbstractRNG, sampler::ActiveSketchSMMALA{T},
        current::AbstractVector{<:AbstractFloat}) where {T<:AbstractFloat}
    source = Runtime.RNGSource(rng)
    state = T.(current)
    if sampler.implementation === :reference
        return T.(Reference.active_sketch_smmala_step!(source,
            sampler.logdensity, sampler.gradient, sampler.sketch,
            Float64(sampler.step_size), Float64(sampler.regularization),
            Float64.(state)))
    end
    Optimized.active_sketch_smmala_step!(source, sampler.logdensity,
        sampler.gradient, sampler.sketch, sampler.step_size,
        sampler.regularization, state)
end

step(sampler::ActiveSketchSMMALA, current::AbstractVector{<:AbstractFloat}) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::ActiveSketchSMMALA{T},
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

sample(sampler::ActiveSketchSMMALA, initial::AbstractVector{<:AbstractFloat},
        count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)
