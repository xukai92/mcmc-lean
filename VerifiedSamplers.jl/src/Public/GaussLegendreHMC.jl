"""Two-stage Gauss--Legendre endpoint HMC.

`backend=:reference` interprets the Lean-emitted IR and has the documented
Float64 boundary. `backend=:optimized` uses the maintained generic Julia path;
set `parallel=true` to evaluate the two stages concurrently, or supply
`batched_gradient!(output, positions)` to use SIMD stage algebra and a fused
two-column gradient call. The finite stage iteration count is part of the
algorithm and does not by itself certify the exact collocation equations.
"""
struct GaussLegendreHMC{T<:AbstractFloat,F,G,B}
    logdensity::F
    gradient::G
    step_size::T
    steps::Int
    stage_iterations::Int
    backend::Symbol
    parallel::Bool
    batched_gradient!::B
end

function GaussLegendreHMC(logdensity::F, gradient::G, step_size::T,
        steps::Integer=10; stage_iterations::Integer=8,
        backend::Symbol=:reference, parallel::Bool=false,
        batched_gradient! = nothing) where
        {T<:AbstractFloat,F,G}
    isfinite(step_size) && step_size > 0 || throw(ArgumentError(
        "step size must be finite and positive"))
    steps > 0 || throw(ArgumentError("integration steps must be positive"))
    stage_iterations > 0 || throw(ArgumentError(
        "stage iterations must be positive"))
    backend in (:reference, :optimized) || throw(ArgumentError(
        "backend must be :reference or :optimized"))
    backend === :reference && T !== Float64 && throw(ArgumentError(
        "Reference Gauss--Legendre HMC has a documented Float64 boundary"))
    parallel && backend !== :optimized && throw(ArgumentError(
        "parallel stages require backend=:optimized"))
    !isnothing(batched_gradient!) && backend !== :optimized && throw(ArgumentError(
        "batched gradients require backend=:optimized"))
    parallel && !isnothing(batched_gradient!) && throw(ArgumentError(
        "threaded and SIMD-batched stages are mutually exclusive"))
    GaussLegendreHMC{T,F,G,typeof(batched_gradient!)}(logdensity, gradient,
        step_size, Int(steps), Int(stage_iterations), backend, parallel,
        batched_gradient!)
end

function step(rng::AbstractRNG, sampler::GaussLegendreHMC{T},
        current::AbstractVector{T}) where {T<:AbstractFloat}
    source = Runtime.RNGSource(rng)
    if sampler.backend === :reference
        return Reference.vector_gauss_legendre_hmc_step!(source,
            sampler.logdensity, sampler.gradient, sampler.step_size,
            sampler.steps, sampler.stage_iterations, current)
    end
    Optimized.vector_gauss_legendre_hmc_step!(source, sampler.logdensity,
        sampler.gradient, sampler.step_size, sampler.steps,
        sampler.stage_iterations, current; parallel=sampler.parallel,
        batched_gradient! = sampler.batched_gradient!)
end

step(sampler::GaussLegendreHMC{T}, current::AbstractVector{T}) where
    {T<:AbstractFloat} = step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::GaussLegendreHMC{T},
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

sample(sampler::GaussLegendreHMC{T}, initial::AbstractVector{T},
    count::Integer) where {T<:AbstractFloat} =
    sample(Random.default_rng(), sampler, initial, count)
