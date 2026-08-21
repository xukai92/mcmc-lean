"""Fixed-probe, structured random-sketch RMHMC.

For probe columns `z_j`, `curvature_action(q, z_j)` supplies `u_j(q)` and the
metric is

```
G_M(q) = ridge * I + (1 / M) * sum_j u_j(q) * u_j(q)'.
```

`curvature_action_derivative(q, z_j)[:, i]` must return
`∂u_j(q)/∂q[i]`. The implementation samples momentum from this metric and uses
Woodbury inverse actions, the matrix determinant lemma, and low-rank force
contractions. It never materializes or factors a dense `d`-by-`d` metric.

The generalized-leapfrog implicit equations are solved to a checked residual
tolerance. This is bounded-residual execution evidence, not an exact
reversibility, volume, or stationarity certificate.
"""
struct RandomSketchRMHMC{T<:AbstractFloat,P,PG,C,CD,PR}
    potential::P
    potential_gradient::PG
    curvature_action::C
    curvature_action_derivative::CD
    probes::PR
    ridge::T
    step_size::T
    steps::Int
    solver_iterations::Int
    solver_tolerance::T
    residual_tolerance::T
    implementation::Symbol
end

mutable struct _RandomSketchGeometryCache{T<:AbstractFloat}
    position::Vector{T}
    factor::Matrix{T}
    gram::Union{Nothing,Cholesky{T,Matrix{T}}}
    factor_derivative::Union{Nothing,Array{T,3}}
end

_RandomSketchGeometryCache(::Type{T}) where {T<:AbstractFloat} =
    _RandomSketchGeometryCache(T[], Matrix{T}(undef, 0, 0), nothing, nothing)

function RandomSketchRMHMC(potential::P, potential_gradient::PG,
        curvature_action::C, curvature_action_derivative::CD,
        probes::AbstractMatrix{T}, ridge::T, step_size::T,
        steps::Integer=10; solver_iterations::Integer=6,
        residual_tolerance::T=T(1e-10),
        solver_tolerance::T=residual_tolerance,
        implementation::Symbol=:reference) where
        {T<:AbstractFloat,P,PG,C,CD}
    isfinite(ridge) && ridge > 0 || throw(ArgumentError(
        "ridge must be finite and positive"))
    isfinite(step_size) && step_size > 0 || throw(ArgumentError(
        "step size must be finite and positive"))
    steps > 0 || throw(ArgumentError("trajectory length must be positive"))
    solver_iterations > 0 || throw(ArgumentError(
        "solver iterations must be positive"))
    isfinite(residual_tolerance) && residual_tolerance >= 0 ||
        throw(ArgumentError(
            "residual tolerance must be finite and nonnegative"))
    isfinite(solver_tolerance) && solver_tolerance >= 0 ||
        throw(ArgumentError(
            "solver tolerance must be finite and nonnegative"))
    implementation in (:reference, :optimized) || throw(ArgumentError(
        "implementation must be :reference or :optimized"))
    size(probes, 1) > 0 || throw(ArgumentError(
        "probe dimension must be positive"))
    size(probes, 2) > 0 || throw(ArgumentError(
        "at least one curvature probe is required"))
    all(isfinite, probes) || throw(ArgumentError("probes must be finite"))
    stored_probes = Matrix{T}(probes)
    RandomSketchRMHMC{T,P,PG,C,CD,typeof(stored_probes)}(
        potential, potential_gradient, curvature_action,
        curvature_action_derivative, stored_probes, ridge, step_size,
        Int(steps), Int(solver_iterations), solver_tolerance,
        residual_tolerance, implementation)
end

function _random_sketch_factor(sampler::RandomSketchRMHMC, q)
    T = eltype(q)
    dimension, count = size(sampler.probes)
    length(q) == dimension || throw(DimensionMismatch(
        "probe dimension must equal position dimension"))
    factor = Matrix{T}(undef, dimension, count)
    scale = inv(sqrt(T(count)))
    for probe_index in axes(sampler.probes, 2)
        action = T.(sampler.curvature_action(
            q, @view sampler.probes[:, probe_index]))
        length(action) == dimension || throw(DimensionMismatch(
            "curvature action dimension"))
        all(isfinite, action) || throw(DomainError(action,
            "curvature action must be finite"))
        @views factor[:, probe_index] .= scale .* action
    end
    factor
end

function _random_sketch_factor_derivative(sampler::RandomSketchRMHMC, q)
    T = eltype(q)
    dimension, count = size(sampler.probes)
    length(q) == dimension || throw(DimensionMismatch(
        "probe dimension must equal position dimension"))
    derivative = Array{T,3}(undef, dimension, count, dimension)
    scale = inv(sqrt(T(count)))
    for probe_index in axes(sampler.probes, 2)
        action_derivative = Matrix{T}(sampler.curvature_action_derivative(
            q, @view sampler.probes[:, probe_index]))
        size(action_derivative) == (dimension, dimension) ||
            throw(DimensionMismatch("curvature action derivative dimension"))
        all(isfinite, action_derivative) || throw(DomainError(
            action_derivative, "curvature action derivative must be finite"))
        for coordinate in 1:dimension
            @views derivative[:, probe_index, coordinate] .=
                scale .* action_derivative[:, coordinate]
        end
    end
    derivative
end

function _random_sketch_gram(sampler::RandomSketchRMHMC, factor)
    T = eltype(factor)
    count = size(factor, 2)
    Symmetric(Matrix{T}(I, count, count) +
        (factor' * factor) / T(sampler.ridge))
end

function _random_sketch_inverse_apply(sampler::RandomSketchRMHMC,
        factor, gram, vector)
    T = eltype(factor)
    ridge = T(sampler.ridge)
    vector / ridge - factor * (gram \ (factor' * vector)) / ridge^2
end

function _random_sketch_geometry!(cache::_RandomSketchGeometryCache{T},
        sampler::RandomSketchRMHMC, q::AbstractVector{T};
        derivative::Bool=false) where {T<:AbstractFloat}
    if length(cache.position) != length(q) || cache.position != q
        cache.position = collect(q)
        cache.factor = _random_sketch_factor(sampler, q)
        cache.gram = cholesky(
            _random_sketch_gram(sampler, cache.factor); check=true)
        cache.factor_derivative = nothing
    end
    if derivative && isnothing(cache.factor_derivative)
        cache.factor_derivative = _random_sketch_factor_derivative(sampler, q)
    end
    cache
end

function _random_sketch_inverse_apply(sampler::RandomSketchRMHMC,
        factor, vector)
    gram = cholesky(_random_sketch_gram(sampler, factor); check=true)
    _random_sketch_inverse_apply(sampler, factor, gram, vector)
end

"""Evaluate the dense matrix represented by a random-sketch metric."""
function random_sketch_metric(sampler::RandomSketchRMHMC, q)
    factor = _random_sketch_factor(sampler, q)
    T = eltype(q)
    Matrix{T}(I, length(q), length(q)) .* T(sampler.ridge) + factor * factor'
end

"""Evaluate `∂G(q)/∂q[i]` for every coordinate of a random-sketch metric."""
function random_sketch_metric_derivative(sampler::RandomSketchRMHMC, q)
    factor = _random_sketch_factor(sampler, q)
    factor_derivative = _random_sketch_factor_derivative(sampler, q)
    dimension = length(q)
    derivative = zeros(eltype(q), dimension, dimension, dimension)
    for coordinate in 1:dimension
        slice = @view factor_derivative[:, :, coordinate]
        derivative[:, :, coordinate] = slice * factor' + factor * slice'
    end
    derivative
end

function _random_sketch_callbacks(sampler::RandomSketchRMHMC,
        ::Type{T}) where {T<:AbstractFloat}
    cache = _RandomSketchGeometryCache(T)
    hamiltonian(q, p) = begin
        geometry = _random_sketch_geometry!(cache, sampler, q)
        factor = geometry.factor
        gram = something(geometry.gram)
        inverse_momentum = _random_sketch_inverse_apply(
            sampler, factor, gram, p)
        potential = T(sampler.potential(q))
        isfinite(potential) || throw(DomainError(potential,
            "potential must be finite"))
        logdet = T(length(q)) * log(T(sampler.ridge)) +
            2 * sum(log, diag(gram.L))
        potential + logdet / 2 + dot(p, inverse_momentum) / 2
    end
    momentum_derivative(q, p) = begin
        geometry = _random_sketch_geometry!(cache, sampler, q)
        factor = geometry.factor
        gram = something(geometry.gram)
        _random_sketch_inverse_apply(sampler, factor, gram, p)
    end
    position_derivative(q, p) = begin
        geometry = _random_sketch_geometry!(cache, sampler, q;
            derivative=true)
        factor = geometry.factor
        factor_derivative = something(geometry.factor_derivative)
        gram = something(geometry.gram)
        inverse_momentum = _random_sketch_inverse_apply(
            sampler, factor, gram, p)
        inverse_factor = _random_sketch_inverse_apply(
            sampler, factor, gram, factor)
        gradient = T.(sampler.potential_gradient(q))
        length(gradient) == length(q) || throw(DimensionMismatch(
            "potential gradient dimension"))
        all(isfinite, gradient) || throw(DomainError(gradient,
            "potential gradient must be finite"))
        projected_momentum = factor' * inverse_momentum
        for coordinate in eachindex(gradient)
            slice = @view factor_derivative[:, :, coordinate]
            trace_term = zero(T)
            momentum_term = zero(T)
            for probe in axes(slice, 2)
                projected_derivative = zero(T)
                for row in axes(slice, 1)
                    value = slice[row, probe]
                    trace_term += inverse_factor[row, probe] * value
                    projected_derivative += value * inverse_momentum[row]
                end
                momentum_term += projected_derivative *
                    projected_momentum[probe]
            end
            gradient[coordinate] += trace_term - momentum_term
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
    (; hamiltonian, integrator)
end

function _random_sketch_momentum!(source::Runtime.AbstractRandomSource,
        sampler::RandomSketchRMHMC, q)
    T = eltype(q)
    factor = _random_sketch_factor(sampler, q)
    base = sqrt(T(sampler.ridge)) .*
        T[Runtime.standard_normal!(source) for _ in eachindex(q)]
    latent = T[Runtime.standard_normal!(source) for _ in axes(factor, 2)]
    base + factor * latent
end

function _random_sketch_step!(source::Runtime.AbstractRandomSource,
        sampler::RandomSketchRMHMC, current::AbstractVector{T}) where
        {T<:AbstractFloat}
    callbacks = _random_sketch_callbacks(sampler, T)
    q0 = collect(current)
    all(isfinite, q0) || throw(ArgumentError("position must be finite"))
    p0 = _random_sketch_momentum!(source, sampler, q0)
    q, p = copy(q0), p0
    for _ in 1:sampler.steps
        next_q, next_p, certificate = callbacks.integrator(
            q, p, sampler.step_size)
        certificate isa Certificates.ImplicitSolveCertificate ||
            throw(ArgumentError(
                "integrator did not return an implicit-solver certificate"))
        certificate.half_momentum_residual.bound <=
            sampler.residual_tolerance &&
            certificate.position_residual.bound <= sampler.residual_tolerance ||
            throw(ArgumentError("implicit solve exceeds residual tolerance"))
        q, p = T.(next_q), T.(next_p)
        all(isfinite, q) && all(isfinite, p) || throw(DomainError(
            (q, p), "integrator state"))
    end
    current_energy = T(callbacks.hamiltonian(q0, p0))
    proposed_energy = T(callbacks.hamiltonian(q, p))
    isfinite(current_energy) && isfinite(proposed_energy) || throw(DomainError(
        (current_energy, proposed_energy), "Hamiltonian must be finite"))
    threshold = exp(min(zero(T), current_energy - proposed_energy))
    T(Runtime.uniform_unit!(source)) < threshold ? q : q0
end

function step(rng::AbstractRNG, sampler::RandomSketchRMHMC,
        current::AbstractVector{<:AbstractFloat})
    T = typeof(sampler.step_size)
    source = Runtime.RNGSource(rng)
    state = T.(current)
    if sampler.implementation === :reference
        callbacks = _random_sketch_callbacks(sampler, Float64)
        momentum_sampler = (runtime_source, q) ->
            _random_sketch_momentum!(runtime_source, sampler, T.(q))
        T.(Reference.random_sketch_rmhmc_step!(source, callbacks.hamiltonian,
            momentum_sampler, callbacks.integrator, sampler.step_size,
            sampler.steps, state, sampler.residual_tolerance))
    else
        _random_sketch_step!(source, sampler, state)
    end
end

step(sampler::RandomSketchRMHMC,
        current::AbstractVector{<:AbstractFloat}) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::RandomSketchRMHMC,
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

sample(sampler::RandomSketchRMHMC,
        initial::AbstractVector{<:AbstractFloat}, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)
