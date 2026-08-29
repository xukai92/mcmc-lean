"""Fixed-subspace likelihood-informed HMC with a standard Gaussian reference.

The target is proportional to `exp(loglikelihood(q)) * N(q; 0, I)`.
`basis` has orthonormal columns spanning the likelihood-informed subspace.
Each transition performs conditional HMC in that subspace, then an
MH-corrected pCN proposal in its orthogonal complement.

The basis is fixed during retained sampling. Learning it is a warmup concern,
not part of this stationary transition.
"""
struct LikelihoodInformedHMC{T<:AbstractFloat,F,G,M<:AbstractMatrix{T}}
    loglikelihood::F
    likelihood_score::G
    basis::M
    step_size::T
    steps::Int
    complement_scale::T
    implementation::Symbol
end

function LikelihoodInformedHMC(loglikelihood::F, likelihood_score::G,
        basis::AbstractMatrix{T}, step_size::T, steps::Integer=10;
        complement_scale::T=T(0.3), implementation::Symbol=:reference,
        orthogonality_tolerance::T=sqrt(eps(T))) where
        {T<:AbstractFloat,F,G}
    d, r = size(basis)
    0 < r <= d || throw(ArgumentError(
        "basis must contain between one and dimension columns"))
    all(isfinite, basis) || throw(ArgumentError("basis must be finite"))
    gram = transpose(basis) * basis
    maximum(abs, gram - Matrix{T}(I, r, r)) <= orthogonality_tolerance ||
        throw(ArgumentError("basis columns must be orthonormal"))
    isfinite(step_size) && step_size > zero(T) || throw(ArgumentError(
        "step size must be finite and positive"))
    steps > 0 || throw(ArgumentError("leapfrog steps must be positive"))
    isfinite(complement_scale) && zero(T) < complement_scale <= one(T) ||
        throw(ArgumentError("complement scale must lie in (0, 1]"))
    implementation in (:reference, :optimized) || throw(ArgumentError(
        "implementation must be :reference or :optimized"))
    B = Matrix{T}(basis)
    LikelihoodInformedHMC{T,F,G,typeof(B)}(loglikelihood,
        likelihood_score, B, step_size, Int(steps), complement_scale,
        implementation)
end

function step(rng::AbstractRNG, sampler::LikelihoodInformedHMC{T},
        current::AbstractVector{T}) where {T<:AbstractFloat}
    B = sampler.basis
    size(B, 1) == length(current) || throw(DimensionMismatch("state and basis"))
    all(isfinite, current) || throw(ArgumentError("position must be finite"))
    source = Runtime.RNGSource(rng)

    active = transpose(B) * current
    complement = current - B * active
    active_logdensity = function(a)
        q = B * a + complement
        value = T(sampler.loglikelihood(q)) - sum(abs2, a) / T(2)
        isfinite(value) || throw(ArgumentError("active log density must be finite"))
        value
    end
    active_gradient = function(a)
        q = B * a + complement
        score = T.(sampler.likelihood_score(q))
        length(score) == length(q) || throw(DimensionMismatch("likelihood score"))
        result = a - transpose(B) * score
        all(isfinite, result) || throw(ArgumentError("active gradient must be finite"))
        result
    end
    next_active = if sampler.implementation === :reference
        T === Float64 || throw(ArgumentError(
            "Reference likelihood-informed HMC has a documented Float64 boundary"))
        Reference.vector_hmc_step!(source, active_logdensity, active_gradient,
            Float64(sampler.step_size), sampler.steps, active)
    else
        Optimized.vector_hmc_step!(source, active_logdensity, active_gradient,
            sampler.step_size, sampler.steps, active)
    end
    after_active = B * next_active + complement

    β = sampler.complement_scale
    ρ = sqrt(one(T) - β * β)
    noise = T[Runtime.standard_normal!(source) for _ in eachindex(current)]
    complement_noise = noise - B * (transpose(B) * noise)
    next_complement = ρ .* complement .+ β .* complement_noise
    proposed = B * next_active + next_complement
    current_loglikelihood = T(sampler.loglikelihood(after_active))
    proposed_loglikelihood = T(sampler.loglikelihood(proposed))
    isfinite(current_loglikelihood) && isfinite(proposed_loglikelihood) ||
        throw(ArgumentError("log likelihood must be finite"))
    log_acceptance = min(zero(T), proposed_loglikelihood - current_loglikelihood)
    log(T(Runtime.uniform_unit!(source))) < log_acceptance ? proposed : after_active
end

step(sampler::LikelihoodInformedHMC,
        current::AbstractVector{<:AbstractFloat}) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::LikelihoodInformedHMC{T},
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

sample(sampler::LikelihoodInformedHMC,
        initial::AbstractVector{<:AbstractFloat}, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)
