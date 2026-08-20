"""Certificate-aware classical Gaussian-momentum RMHMC.

The factor callback follows the formal convention `A(q)'A(q) = G(q)⁻¹`.
The integrator callback must return `(q_next, p_next, certificate)`, where the
certificate establishes an exact unique, reversible, volume-preserving solve.
Finite-tolerance residuals alone are intentionally rejected.

Set `implementation=:reference` for the auditable implementation or
`:optimized` for the independently maintained implementation checked by
differential and statistical tests.
"""
struct ClassicalRMHMC{H,F,I}
    hamiltonian::H
    metric_factor::F
    integrator::I
    step_size::Float64
    steps::Int
    implementation::Symbol
    function ClassicalRMHMC(hamiltonian::H, metric_factor::F, integrator::I,
            step_size::Real, steps::Integer=10;
            implementation::Symbol=:reference) where {H,F,I}
        ε = Float64(step_size)
        isfinite(ε) && ε > 0 || throw(ArgumentError(
            "step size must be finite and positive"))
        steps > 0 || throw(ArgumentError("trajectory length must be positive"))
        implementation in (:reference, :optimized) || throw(ArgumentError(
            "implementation must be :reference or :optimized"))
        new{H,F,I}(hamiltonian, metric_factor, integrator, ε, Int(steps),
            implementation)
    end
end

function step(rng::AbstractRNG, sampler::ClassicalRMHMC,
        current::AbstractVector{<:Real})
    source = Runtime.RNGSource(rng)
    state = Float64.(current)
    if sampler.implementation === :reference
        Reference.classical_rmhmc_step!(source, sampler.hamiltonian,
            sampler.metric_factor, sampler.integrator, sampler.step_size,
            sampler.steps, state)
    else
        Optimized.classical_rmhmc_step!(source, sampler.hamiltonian,
            sampler.metric_factor, sampler.integrator, sampler.step_size,
            sampler.steps, state)
    end
end

step(sampler::ClassicalRMHMC, current::AbstractVector{<:Real}) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::ClassicalRMHMC,
        initial::AbstractVector{<:Real}, count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    current = Float64.(initial)
    samples = Matrix{Float64}(undef, length(current), count)
    for index in axes(samples, 2)
        current = step(rng, sampler, current)
        samples[:, index] = current
    end
    samples
end

sample(sampler::ClassicalRMHMC, initial::AbstractVector{<:Real},
        count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)
