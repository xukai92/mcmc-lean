"""Certificate-aware classical Gaussian-momentum RMHMC.

The factor callback follows the formal convention `A(q)'A(q) = G(q)⁻¹`.
The integrator callback must return `(q_next, p_next, certificate)`, where the
certificate establishes an exact unique, reversible, volume-preserving solve.
Finite-tolerance residuals alone are intentionally rejected.

Set `implementation=:reference` for the auditable implementation or
`:optimized` for the independently maintained implementation checked by
differential and statistical tests.
"""
struct ClassicalRMHMC{T<:AbstractFloat,H,F,I}
    hamiltonian::H
    metric_factor::F
    integrator::I
    step_size::T
    steps::Int
    implementation::Symbol
    function ClassicalRMHMC(hamiltonian::H, metric_factor::F, integrator::I,
            step_size::T, steps::Integer=10;
            implementation::Symbol=:reference) where {T<:AbstractFloat,H,F,I}
        ε = step_size
        isfinite(ε) && ε > 0 || throw(ArgumentError(
            "step size must be finite and positive"))
        steps > 0 || throw(ArgumentError("trajectory length must be positive"))
        implementation in (:reference, :optimized) || throw(ArgumentError(
            "implementation must be :reference or :optimized"))
        new{T,H,F,I}(hamiltonian, metric_factor, integrator, ε, Int(steps),
            implementation)
    end
end

function step(rng::AbstractRNG, sampler::ClassicalRMHMC,
        current::AbstractVector{<:AbstractFloat})
    source = Runtime.RNGSource(rng)
    T = typeof(sampler.step_size)
    state = T.(current)
    if sampler.implementation === :reference
        T.(Reference.classical_rmhmc_step!(source, sampler.hamiltonian,
            sampler.metric_factor, sampler.integrator,
            Float64(sampler.step_size), sampler.steps, Float64.(state)))
    else
        Optimized.classical_rmhmc_step!(source, sampler.hamiltonian,
            sampler.metric_factor, sampler.integrator, sampler.step_size,
            sampler.steps, state)
    end
end

step(sampler::ClassicalRMHMC, current::AbstractVector{<:AbstractFloat}) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::ClassicalRMHMC,
        initial::AbstractVector{<:AbstractFloat}, count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    T = typeof(sampler.step_size)
    current = T.(initial)
    samples = Matrix{T}(undef, length(current), count)
    for index in axes(samples, 2)
        current = step(rng, sampler, current)
        samples[:, index] = current
    end
    samples
end

sample(sampler::ClassicalRMHMC, initial::AbstractVector{<:AbstractFloat},
        count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)
