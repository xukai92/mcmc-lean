"""Numerical dense position-dependent classical RMHMC.

`metric(q)` returns the positive-definite covariance metric `G(q)`, and
`metric_derivative(q)[:, :, i]` returns `∂G(q)/∂qᵢ`. The generalized-leapfrog
implicit equations are solved to a checked residual tolerance. This supplies
bounded-residual execution evidence, not an exact reversibility, volume, or
stationarity certificate; use `ClassicalRMHMC` with an exact certified
integrator when those claims are required.
"""
struct DenseRiemannianRMHMC{T<:AbstractFloat,P,PG,M,MD}
    potential::P
    potential_gradient::PG
    metric::M
    metric_derivative::MD
    step_size::T
    steps::Int
    solver_iterations::Int
    solver_tolerance::T
    residual_tolerance::T
    implementation::Symbol
    function DenseRiemannianRMHMC(potential::P, potential_gradient::PG,
            metric::M, metric_derivative::MD, step_size::T,
            steps::Integer=10; solver_iterations::Integer=6,
            residual_tolerance::T=T(1e-10),
            solver_tolerance::T=residual_tolerance,
            implementation::Symbol=:reference) where {T<:AbstractFloat,P,PG,M,MD}
        ε = step_size
        stopping_tolerance = solver_tolerance
        tolerance = residual_tolerance
        isfinite(ε) && ε > 0 || throw(ArgumentError(
            "step size must be finite and positive"))
        steps > 0 || throw(ArgumentError("trajectory length must be positive"))
        solver_iterations > 0 || throw(ArgumentError(
            "solver iterations must be positive"))
        isfinite(tolerance) && tolerance >= 0 || throw(ArgumentError(
            "residual tolerance must be finite and nonnegative"))
        isfinite(stopping_tolerance) && stopping_tolerance >= 0 ||
            throw(ArgumentError(
                "solver tolerance must be finite and nonnegative"))
        implementation in (:reference, :optimized) || throw(ArgumentError(
            "implementation must be :reference or :optimized"))
        new{T,P,PG,M,MD}(potential, potential_gradient, metric,
            metric_derivative, ε, Int(steps), Int(solver_iterations),
            stopping_tolerance, tolerance, implementation)
    end
end

function _dense_metric_data(sampler::DenseRiemannianRMHMC, q)
    T = eltype(q)
    dimension = length(q)
    metric = Matrix{T}(sampler.metric(q))
    size(metric) == (dimension, dimension) ||
        throw(DimensionMismatch("Riemannian metric dimension"))
    all(isfinite, metric) || throw(DomainError(metric,
        "Riemannian metric must be finite"))
    cholesky(Symmetric(metric); check=true), metric
end

function _dense_metric_derivative(sampler::DenseRiemannianRMHMC, q)
    T = eltype(q)
    dimension = length(q)
    derivative = Array{T,3}(sampler.metric_derivative(q))
    size(derivative) == (dimension, dimension, dimension) ||
        throw(DimensionMismatch("Riemannian metric derivative dimension"))
    all(isfinite, derivative) || throw(DomainError(derivative,
        "Riemannian metric derivative must be finite"))
    derivative
end

function _dense_rmhmc_callbacks(sampler::DenseRiemannianRMHMC)
    factor(q) = begin
        decomposition, _ = _dense_metric_data(sampler, q)
        inv(Matrix(decomposition.L))
    end
    hamiltonian(q, p) = begin
        decomposition, _ = _dense_metric_data(sampler, q)
        potential = eltype(q)(sampler.potential(q))
        isfinite(potential) || throw(DomainError(potential,
            "potential must be finite"))
        potential + sum(log, diag(decomposition.L)) +
            dot(p, decomposition \ p) / 2
    end
    momentum_derivative(q, p) = begin
        decomposition, _ = _dense_metric_data(sampler, q)
        decomposition \ p
    end
    position_derivative(q, p) = begin
        decomposition, _ = _dense_metric_data(sampler, q)
        derivative = _dense_metric_derivative(sampler, q)
        gradient = eltype(q).(sampler.potential_gradient(q))
        length(gradient) == length(q) ||
            throw(DimensionMismatch("potential gradient dimension"))
        inverse_momentum = decomposition \ p
        inverse_metric = decomposition \ Matrix{eltype(q)}(
            I, length(q), length(q))
        for coordinate in eachindex(gradient)
            slice = @view derivative[:, :, coordinate]
            gradient[coordinate] +=
                (dot(transpose(inverse_metric), slice) - dot(inverse_momentum,
                    slice * inverse_momentum)) / 2
        end
        gradient
    end
    integrator(q, p, ε) = begin
        solver = sampler.implementation === :reference ?
            Reference.fixed_point_generalized_leapfrog :
            Optimized.fixed_point_generalized_leapfrog
        solver(position_derivative, momentum_derivative, q, p, ε;
            max_iterations=sampler.solver_iterations,
            atol=sampler.solver_tolerance, rtol=zero(sampler.step_size))
    end
    (; factor, hamiltonian, integrator)
end

function step(rng::AbstractRNG, sampler::DenseRiemannianRMHMC,
        current::AbstractVector{<:AbstractFloat})
    callbacks = _dense_rmhmc_callbacks(sampler)
    source = Runtime.RNGSource(rng)
    T = typeof(sampler.step_size)
    state = T.(current)
    if sampler.implementation === :reference
        T.(Reference.dense_rmhmc_step!(source,
            callbacks.hamiltonian, callbacks.factor, callbacks.integrator,
            Float64(sampler.step_size), sampler.steps, Float64.(state),
            Float64(sampler.residual_tolerance)))
    else
        Optimized.approximate_classical_rmhmc_step!(source,
            callbacks.hamiltonian, callbacks.factor, callbacks.integrator,
            sampler.step_size, sampler.steps, state,
            sampler.residual_tolerance)
    end
end

step(sampler::DenseRiemannianRMHMC,
        current::AbstractVector{<:AbstractFloat}) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::DenseRiemannianRMHMC,
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

sample(sampler::DenseRiemannianRMHMC,
        initial::AbstractVector{<:AbstractFloat},
        count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)
