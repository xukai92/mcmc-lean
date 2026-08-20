module Optimized

using LinearAlgebra

using ...Runtime: AbstractRandomSource, draw_below!, standard_normal!,
    uniform_unit!, checked_positive_float, checked_positive_count,
    checked_finite_float
using ...Certificates: ImplicitSolveCertificate, certify_implicit_solve,
    certifies_exact_solver

export categorical_index!, integer_slice_step!, bounded_slice_step!, stepping_out_slice_step!, sheared_birth_death_step!, spatial_birth_death_step!, finite_mh_step!, two_state_mh_step!, gaussian_rwmh_step!,
    finite_hmm_particle_gibbs_step!,
    scalar_hmc_step!, vector_hmc_step!, metric_hmc_step!, multinomial_hmc_step!,
    metric_multinomial_hmc_step!,
    relativistic_multinomial_hmc_step!,
    fixed_point_generalized_leapfrog,
    classical_rmhmc_step!,
    approximate_classical_rmhmc_step!,
    certified_relativistic_multinomial_hmc_step!,
    dynamic_select_float!, streaming_eligible_select!,
    categorical_dhmc_step!, leapfrog, vector_leapfrog,
    AbstractPreparedMetric, PreparedDiagonalMetric, PreparedDenseMetric,
    prepare_metric

"""A validated constant metric whose reusable numerical data are cached."""
abstract type AbstractPreparedMetric end

"""Cached elementwise operations for a positive diagonal mass matrix."""
struct PreparedDiagonalMetric{T<:AbstractFloat} <: AbstractPreparedMetric
    mass::Vector{T}
    inverse_mass::Vector{T}
    sqrt_mass::Vector{T}
end

"""Cached Cholesky factorization for a positive dense mass matrix."""
struct PreparedDenseMetric{T<:AbstractFloat,F} <: AbstractPreparedMetric
    mass::Matrix{T}
    inverse_mass::Matrix{T}
    factorization::F
end

"""Validate and cache a constant diagonal or dense mass matrix.

Prepare a metric once and reuse it across transitions. This avoids repeated
factorization and construction of metric actions in the optimized samplers.
"""
function prepare_metric(mass::AbstractVector{T}) where {T<:AbstractFloat}
    converted = collect(mass)
    isempty(converted) && throw(ArgumentError("mass cannot be empty"))
    all(x -> isfinite(x) && x > 0, converted) || throw(ArgumentError(
        "diagonal mass must be finite and positive"))
    inverse_mass = inv.(converted)
    sqrt_mass = sqrt.(converted)
    all(isfinite, inverse_mass) || throw(ArgumentError(
        "inverse diagonal mass must be finite"))
    PreparedDiagonalMetric(converted, inverse_mass, sqrt_mass)
end

function prepare_metric(mass::AbstractMatrix{T}) where {T<:AbstractFloat}
    converted = Matrix(mass)
    size(converted, 1) == size(converted, 2) || throw(DimensionMismatch(
        "mass matrix must be square"))
    all(isfinite, converted) || throw(ArgumentError(
        "mass matrix must be finite"))
    issymmetric(converted) || throw(ArgumentError(
        "mass matrix must be symmetric"))
    factorization = cholesky(Symmetric(converted); check=true)
    inverse_mass = Matrix(inv(factorization))
    all(isfinite, inverse_mass) || throw(ArgumentError(
        "inverse mass matrix must be finite"))
    PreparedDenseMetric(converted, inverse_mass, factorization)
end

prepare_metric(metric::AbstractPreparedMetric) = metric

metric_dimension(metric::PreparedDiagonalMetric) = length(metric.mass)
metric_dimension(metric::PreparedDenseMetric) = size(metric.mass, 1)

function sample_momentum!(momentum, noise, metric::PreparedDiagonalMetric)
    @. momentum = metric.sqrt_mass * noise
end

function sample_momentum!(momentum, noise, metric::PreparedDenseMetric)
    mul!(momentum, metric.factorization.L, noise)
end

function velocity!(result, momentum, metric::PreparedDiagonalMetric)
    @. result = metric.inverse_mass * momentum
end

function velocity!(result, momentum, metric::PreparedDenseMetric)
    mul!(result, metric.inverse_mass, momentum)
end

function kinetic_energy!(workspace, momentum, metric::AbstractPreparedMetric)
    velocity!(workspace, momentum, metric)
    dot(momentum, workspace) / 2
end

function prepared_leapfrog!(position, momentum, velocity_workspace, gradient,
        force, step_size, metric::AbstractPreparedMetric)
    half_step = step_size / 2
    length(force) == length(position) || throw(DimensionMismatch("gradient"))
    @. momentum -= half_step * force
    velocity!(velocity_workspace, momentum, metric)
    @. position += step_size * velocity_workspace
    next_force = gradient(position)
    length(next_force) == length(position) || throw(DimensionMismatch("gradient"))
    @. momentum -= half_step * next_force
    next_force
end

"""Low-allocation counterpart of reference dynamic target-weighted selection."""
function dynamic_select_float!(source::AbstractRandomSource,
        candidates::AbstractVector{<:Integer},
        logweights::AbstractVector{T}) where {T<:AbstractFloat}
    isempty(candidates) && throw(ArgumentError("candidate set cannot be empty"))
    length(candidates) == length(logweights) ||
        throw(DimensionMismatch("candidate indices and weights must match"))
    offset = T(-Inf)
    for value in logweights
        isfinite(value) || throw(DomainError(logweights,
            "dynamic target log weights must be finite"))
        offset = max(offset, value)
    end
    total = zero(T)
    for value in logweights
        total += exp(value - offset)
    end
    target = T(uniform_unit!(source)) * total
    cumulative = zero(T)
    for index in eachindex(logweights)
        cumulative += exp(logweights[index] - offset)
        target < cumulative && return Int(candidates[index])
    end
    Int(last(candidates))
end

"""Single-pass counterpart of eligible-count streaming selection.

Flattening is avoided: one ticket is drawn from the total eligible count and
located by a linear scan. This is distributionally equivalent to Reference's
recursive local-representative merges but intentionally follows a different
implementation path.
"""
function streaming_eligible_select!(source::AbstractRandomSource,
        segments::AbstractVector{<:AbstractVector{<:Integer}})
    total = sum(length, segments; init=0)
    total == 0 && return nothing
    ticket = Int(draw_below!(source, total))
    for segment in segments
        if ticket < length(segment)
            return Int(segment[ticket + 1])
        end
        ticket -= length(segment)
    end
    error("internal eligible-count selection failure")
end

"""Allocation-free categorical DHMC update, independent of the reference path."""
function categorical_dhmc_step!(source::AbstractRandomSource,
        probabilities::AbstractVector{T}, steps::Integer,
        current::Integer) where {T<:AbstractFloat}
    category_count = length(probabilities)
    category_count >= 2 || throw(ArgumentError("DHMC needs at least two categories"))
    for probability in probabilities
        isfinite(probability) && probability > 0 ||
            throw(ArgumentError("category probabilities must be finite and positive"))
    end
    steps > 0 || throw(ArgumentError("trajectory length must be positive"))
    1 <= current <= category_count ||
        throw(ArgumentError("current category is out of range"))

    direction = T(uniform_unit!(source)) < T(0.5) ? 1 : -1
    kinetic = -log1p(-T(uniform_unit!(source)))
    state = Int(current)
    for _ in 1:steps
        candidate = mod1(state + direction, category_count)
        jump = log(probabilities[state] / probabilities[candidate])
        if jump < kinetic
            state = candidate
            kinetic -= jump
        else
            direction = -direction
        end
    end
    state
end

"""Allocation-free exact integer slice update on zero-based state indices."""
function integer_slice_step!(source::AbstractRandomSource,
        weights::AbstractVector{<:Integer}, current::Integer)
    isempty(weights) && throw(ArgumentError("slice weights cannot be empty"))
    all(>(0), weights) || throw(ArgumentError("slice weights must be positive"))
    0 <= current < length(weights) || throw(ArgumentError("current state is out of range"))
    height = draw_below!(source, weights[current + 1])
    count = 0
    for weight in weights
        count += weight > height
    end
    rank = Int(draw_below!(source, count))
    for index in eachindex(weights)
        if weights[index] > height
            rank == 0 && return index - 1
            rank -= 1
        end
    end
    error("unreachable integer-slice selection")
end

"""Low-allocation bounded rejection slice update."""
function bounded_slice_step!(source::AbstractRandomSource, logdensity,
        lower::T, upper::T, current::T, max_attempts::Integer) where {T<:AbstractFloat}
    lo, width, x = lower, upper - lower, current
    isfinite(lo) && isfinite(width) && width > 0 ||
        throw(ArgumentError("slice bounds must be finite and ordered"))
    lo <= x <= lo + width ||
        throw(ArgumentError("current state is outside slice bounds"))
    max_attempts > 0 || throw(ArgumentError("max_attempts must be positive"))
    base = T(logdensity(x))
    isfinite(base) || throw(ArgumentError("current log density must be finite"))
    threshold = base + log(T(uniform_unit!(source)))
    attempts = 0
    while attempts < max_attempts
        candidate = muladd(width, T(uniform_unit!(source)), lo)
        value = T(logdensity(candidate))
        (isfinite(value) || value == -Inf) ||
            throw(ArgumentError("log density must be finite or -Inf"))
        value >= threshold && return candidate
        attempts += 1
    end
    throw(ErrorException("bounded slice rejection exceeded max_attempts"))
end


"""Low-allocation stepping-out and shrinkage slice update."""
function stepping_out_slice_step!(source::AbstractRandomSource, logdensity,
        width::T, current::T, max_steps::Integer, max_shrink::Integer) where {T<:AbstractFloat}
    w, x = width, current
    isfinite(w) && w > 0 || throw(ArgumentError("width must be finite and positive"))
    isfinite(x) || throw(ArgumentError("current state must be finite"))
    max_steps >= 0 || throw(ArgumentError("max_steps must be nonnegative"))
    max_shrink > 0 || throw(ArgumentError("max_shrink must be positive"))
    base = T(logdensity(x))
    isfinite(base) || throw(ArgumentError("current log density must be finite"))
    threshold = base + log(T(uniform_unit!(source)))
    left = x - w * T(uniform_unit!(source))
    right = left + w
    left_steps = Int(floor(T(uniform_unit!(source)) * (max_steps + 1)))
    right_steps = max_steps - left_steps
    while left_steps > 0
        value = T(logdensity(left))
        (isfinite(value) || value == -Inf) ||
            throw(ArgumentError("log density must be finite or -Inf"))
        value <= threshold && break
        left -= w
        left_steps -= 1
    end
    while right_steps > 0
        value = T(logdensity(right))
        (isfinite(value) || value == -Inf) ||
            throw(ArgumentError("log density must be finite or -Inf"))
        value <= threshold && break
        right += w
        right_steps -= 1
    end
    attempts = 0
    while attempts < max_shrink
        proposal = muladd(right - left, T(uniform_unit!(source)), left)
        value = T(logdensity(proposal))
        (isfinite(value) || value == -Inf) ||
            throw(ArgumentError("log density must be finite or -Inf"))
        value >= threshold && return proposal
        if proposal < x
            left = proposal
        else
            right = proposal
        end
        attempts += 1
    end
    # Match the total Reference semantics on finite-trace exhaustion.
    x
end

"""Low-allocation nonlinear reversible-jump birth/death update."""
function sheared_birth_death_step!(source::AbstractRandomSource, current)
    current === nothing || current isa Tuple{<:AbstractFloat,<:AbstractFloat} ||
        throw(ArgumentError("RJ state must be nothing or a pair of reals"))
    current === nothing || return nothing
    u1 = muladd(2.0, uniform_unit!(source), -1.0)
    u2 = muladd(2.0, uniform_unit!(source), -1.0)
    (muladd(8.0, u2^3, 2.0 * u1), 2.0 * u2)
end

"""Low-allocation three-dimensional product-scaled birth/death update."""
function spatial_birth_death_step!(source::AbstractRandomSource, current)
    current === nothing ||
        (current isa Tuple && length(current) == 3 &&
            all(x -> x isa AbstractFloat, current)) ||
        throw(ArgumentError("spatial RJ state must be nothing or three reals"))
    current === nothing || return nothing
    ntuple(_ -> muladd(4.0, uniform_unit!(source), -2.0), 3)
end

"""Allocation-conscious fixed-point generalized-leapfrog solver.

Residual certificates remain approximate unless both residuals are exactly
zero and the caller supplies independently justified global witnesses.
"""
function fixed_point_generalized_leapfrog(position_derivative,
        momentum_derivative, position::AbstractVector{T},
        momentum::AbstractVector{T}, step_size::T;
        max_iterations::Integer=100, atol::T=T(1e-10), rtol::T=T(1e-8),
        unique::Bool=false, reversible::Bool=false,
        volume_preserving::Bool=false) where {T<:AbstractFloat}
    max_iterations > 0 || throw(ArgumentError("max_iterations must be positive"))
    ε, absolute, relative = step_size, atol, rtol
    isfinite(ε) || throw(ArgumentError("step size must be finite"))
    isfinite(absolute) && absolute >= 0 ||
        throw(ArgumentError("atol must be finite and nonnegative"))
    isfinite(relative) && relative >= 0 ||
        throw(ArgumentError("rtol must be finite and nonnegative"))
    q, p = collect(position), collect(momentum)
    length(q) == length(p) || throw(DimensionMismatch("position and momentum"))
    isempty(q) && throw(ArgumentError("state cannot be empty"))
    all(isfinite, q) && all(isfinite, p) ||
        throw(ArgumentError("state must be finite"))

    p_half = copy(p)
    candidate_p = similar(p_half)
    for _ in 1:max_iterations
        derivative = position_derivative(q, p_half)
        length(derivative) == length(p) || throw(DimensionMismatch("position derivative"))
        @. candidate_p = p - (ε / 2) * derivative
        all(isfinite, candidate_p) || throw(DomainError(candidate_p, "half momentum"))
        residual = norm(candidate_p .- p_half)
        p_half, candidate_p = candidate_p, p_half
        residual <= absolute + relative * max(norm(p_half), 1.0) && break
    end

    q_next = copy(q)
    candidate_q = similar(q_next)
    initial_velocity = T.(momentum_derivative(q, p_half))
    length(initial_velocity) == length(q) || throw(DimensionMismatch("momentum derivative"))
    for _ in 1:max_iterations
        terminal_velocity = momentum_derivative(q_next, p_half)
        length(terminal_velocity) == length(q) || throw(DimensionMismatch("momentum derivative"))
        @. candidate_q = q + (ε / 2) * (initial_velocity + terminal_velocity)
        all(isfinite, candidate_q) || throw(DomainError(candidate_q, "next position"))
        residual = norm(candidate_q .- q_next)
        q_next, candidate_q = candidate_q, q_next
        residual <= absolute + relative * max(norm(q_next), 1.0) && break
    end

    half_update = p .- (ε / 2) .* position_derivative(q, p_half)
    position_update = q .+ (ε / 2) .* (initial_velocity .+
        momentum_derivative(q_next, p_half))
    half_residual = norm(p_half .- half_update)
    position_residual = norm(q_next .- position_update)
    p_next = p_half .- (ε / 2) .* position_derivative(q_next, p_half)
    certificate = certify_implicit_solve(half_residual, half_residual,
        position_residual, position_residual; unique=unique,
        reversible=reversible, volume_preserving=volume_preserving)
    q_next, T.(p_next), certificate
end

"""One scalar velocity-Verlet/leapfrog step with unit mass."""
function leapfrog(gradient, step_size::T, position::T, momentum::T) where {T<:AbstractFloat}
    half_momentum = momentum - step_size * gradient(position) / 2
    next_position = position + step_size * half_momentum
    next_momentum = half_momentum - step_size * gradient(next_position) / 2
    next_position, next_momentum
end

"""One vector velocity-Verlet/leapfrog step with unit mass."""
function vector_leapfrog(gradient, step_size::T,
        position::AbstractVector{T}, momentum::AbstractVector{T}) where {T<:AbstractFloat}
    half_momentum = momentum .- (step_size / 2) .* gradient(position)
    next_position = position .+ step_size .* half_momentum
    next_momentum = half_momentum .- (step_size / 2) .* gradient(next_position)
    next_position, next_momentum
end

"""Independent generic floating-point implementation of vector endpoint HMC."""
function vector_hmc_step!(source::AbstractRandomSource, logdensity, gradient,
        step_size::T, steps::Integer, current::AbstractVector{T}) where {T<:AbstractFloat}
    isfinite(step_size) && step_size > 0.0 ||
        throw(ArgumentError("step size must be finite and positive"))
    steps > 0 || throw(ArgumentError("leapfrog steps must be positive"))
    isempty(current) && throw(ArgumentError("position cannot be empty"))
    ε, initial = step_size, collect(current)
    momentum = T[standard_normal!(source) for _ in eachindex(initial)]
    next_position, next_momentum = copy(initial), copy(momentum)
    for _ in 1:steps
        next_position, next_momentum = vector_leapfrog(
            gradient, ε, next_position, next_momentum)
    end
    current_energy = -logdensity(initial) + sum(abs2, momentum) / 2
    next_energy = -logdensity(next_position) + sum(abs2, next_momentum) / 2
    log(uniform_unit!(source)) < min(0.0, current_energy - next_energy) ?
        next_position : initial
end

"""Independent constant-metric endpoint HMC implementation."""
function metric_hmc_step!(source::AbstractRandomSource, logdensity, gradient,
        step_size::T, steps::Integer, current::AbstractVector{T},
        metric::AbstractPreparedMetric) where {T<:AbstractFloat}
    isfinite(step_size) && step_size > 0 || throw(ArgumentError(
        "step size must be finite and positive"))
    steps > 0 || throw(ArgumentError("leapfrog steps must be positive"))
    eltype(metric.mass) === T || throw(ArgumentError("state and metric element types must match"))
    ε, initial_q = step_size, collect(current)
    isempty(initial_q) && throw(ArgumentError("position cannot be empty"))
    all(isfinite, initial_q) || throw(ArgumentError("position must be finite"))
    metric_dimension(metric) == length(initial_q) || throw(DimensionMismatch(
        "mass dimension"))
    q = copy(initial_q)
    noise = T[standard_normal!(source) for _ in eachindex(q)]
    p = similar(q)
    sample_momentum!(p, noise, metric)
    initial_p = copy(p)
    velocity_workspace = similar(q)
    force = gradient(q)
    for _ in 1:steps
        force = prepared_leapfrog!(q, p, velocity_workspace, gradient, force,
            ε, metric)
    end
    current_energy = -logdensity(initial_q) +
        kinetic_energy!(velocity_workspace, initial_p, metric)
    proposed_energy = -logdensity(q) +
        kinetic_energy!(velocity_workspace, p, metric)
    log(uniform_unit!(source)) < min(0.0, current_energy - proposed_energy) ?
        q : initial_q
end

function metric_hmc_step!(source::AbstractRandomSource, logdensity, gradient,
        step_size::T, steps::Integer, current::AbstractVector{T}, mass) where {T<:AbstractFloat}
    metric_hmc_step!(source, logdensity, gradient, step_size, steps, current,
        prepare_metric(mass))
end

"""Independent generic floating-point randomized-origin multinomial HMC."""
function multinomial_hmc_step!(source::AbstractRandomSource, logdensity, gradient,
        step_size::T, steps::Integer, current::AbstractVector{T}) where {T<:AbstractFloat}
    steps > 0 || throw(ArgumentError("trajectory length must be positive"))
    ε, q = step_size, collect(current)
    isempty(q) && throw(ArgumentError("position cannot be empty"))
    p = T[standard_normal!(source) for _ in eachindex(q)]
    origin = Int(draw_below!(source, steps + 1))
    for _ in 1:origin
        q, p = vector_leapfrog(gradient, -ε, q, p)
    end
    trajectory = Vector{Tuple{Vector{T},Vector{T}}}(undef, steps + 1)
    trajectory[1] = (copy(q), copy(p))
    for index in 2:(steps + 1)
        q, p = vector_leapfrog(gradient, ε, q, p)
        trajectory[index] = (copy(q), copy(p))
    end
    logweights = [logdensity(position) - sum(abs2, momentum) / 2
        for (position, momentum) in trajectory]
    weights = exp.(logweights .- maximum(logweights))
    target = uniform_unit!(source) * sum(weights)
    cumulative = 0.0
    for (index, weight) in pairs(weights)
        cumulative += weight
        target < cumulative && return trajectory[index][1]
    end
    trajectory[end][1]
end

"""Independent constant-metric randomized-origin multinomial HMC."""
function metric_multinomial_hmc_step!(source::AbstractRandomSource, logdensity,
        gradient, step_size::T, steps::Integer,
        current::AbstractVector{T}, metric::AbstractPreparedMetric) where {T<:AbstractFloat}
    isfinite(step_size) && step_size > 0 || throw(ArgumentError(
        "step size must be finite and positive"))
    steps > 0 || throw(ArgumentError("trajectory length must be positive"))
    eltype(metric.mass) === T || throw(ArgumentError("state and metric element types must match"))
    ε, initial_q = step_size, collect(current)
    isempty(initial_q) && throw(ArgumentError("position cannot be empty"))
    all(isfinite, initial_q) || throw(ArgumentError("position must be finite"))
    metric_dimension(metric) == length(initial_q) || throw(DimensionMismatch(
        "mass dimension"))
    noise = T[standard_normal!(source) for _ in eachindex(initial_q)]
    initial_p = similar(initial_q)
    sample_momentum!(initial_p, noise, metric)
    velocity_workspace = similar(initial_q)
    origin = Int(draw_below!(source, steps + 1))
    initial_force = gradient(initial_q)
    positions = Matrix{T}(undef, length(initial_q), steps + 1)
    initial_logweight = logdensity(initial_q) -
        kinetic_energy!(velocity_workspace, initial_p, metric)
    logweights = Vector{typeof(initial_logweight)}(undef, steps + 1)
    current_index = origin + 1
    positions[:, current_index] = initial_q
    logweights[current_index] = initial_logweight

    q, p, force = copy(initial_q), copy(initial_p), initial_force
    for index in origin:-1:1
        force = prepared_leapfrog!(q, p, velocity_workspace, gradient, force,
            -ε, metric)
        positions[:, index] = q
        logweights[index] = logdensity(q) -
            kinetic_energy!(velocity_workspace, p, metric)
    end

    q, p, force = copy(initial_q), copy(initial_p), initial_force
    for index in (origin + 2):(steps + 1)
        force = prepared_leapfrog!(q, p, velocity_workspace, gradient, force,
            ε, metric)
        positions[:, index] = q
        logweights[index] = logdensity(q) -
            kinetic_energy!(velocity_workspace, p, metric)
    end
    weights = exp.(logweights .- maximum(logweights))
    target = uniform_unit!(source) * sum(weights)
    cumulative = 0.0
    for (index, weight) in pairs(weights)
        cumulative += weight
        target < cumulative && return copy(@view positions[:, index])
    end
    copy(@view positions[:, end])
end

function metric_multinomial_hmc_step!(source::AbstractRandomSource, logdensity,
        gradient, step_size::T, steps::Integer,
        current::AbstractVector{T}, mass) where {T<:AbstractFloat}
    metric_multinomial_hmc_step!(source, logdensity, gradient, step_size, steps,
        current, prepare_metric(mass))
end

function _relativistic_radius!(source::AbstractRandomSource, dimension::Int,
        relativistic_mass::T) where {T<:AbstractFloat}
    while true
        radius = sum((-log1p(-T(uniform_unit!(source))) for _ in 1:dimension);
            init=zero(T))
        log(T(uniform_unit!(source))) < radius - sqrt(radius^2 + relativistic_mass^2) &&
            return radius
    end
end

function relativistic_multinomial_hmc_step!(source::AbstractRandomSource,
        logdensity, gradient, step_size::T, steps::Integer,
        current::AbstractVector{T}, mass::AbstractVector{T},
        relativistic_mass::T) where {T<:AbstractFloat}
    ε, m = step_size, relativistic_mass
    steps > 0 || throw(ArgumentError("trajectory length must be positive"))
    isfinite(ε) && ε > 0 || throw(ArgumentError("step size must be finite and positive"))
    q0 = collect(current)
    isempty(q0) && throw(ArgumentError("position cannot be empty"))
    converted_mass = collect(mass)
    length(converted_mass) == length(q0) || throw(DimensionMismatch("mass dimension"))
    all(x -> isfinite(x) && x > 0, converted_mass) ||
        throw(ArgumentError("diagonal metric must be finite and positive"))
    isfinite(m) && m > 0 ||
        throw(ArgumentError("relativistic mass must be finite and positive"))
    radius = _relativistic_radius!(source, length(q0), m)
    direction = T[standard_normal!(source) for _ in eachindex(q0)]
    direction_norm = norm(direction)
    isfinite(direction_norm) && direction_norm > 0 ||
        throw(DomainError(direction, "spherical direction draw must be nonzero"))
    p0 = sqrt.(converted_mass) .* ((radius / direction_norm) .* direction)
    velocity = function (p)
        inverse_metric_p = p ./ converted_mass
        inverse_metric_p ./ sqrt(dot(p, inverse_metric_p) + m^2)
    end
    advance = function (q, p, signed_step)
        half = p .- (signed_step / 2) .* gradient(q)
        next_q = q .+ signed_step .* velocity(half)
        next_p = half .- (signed_step / 2) .* gradient(next_q)
        next_q, next_p
    end
    origin = Int(draw_below!(source, steps + 1))
    trajectory = Vector{Tuple{Vector{T},Vector{T}}}(undef, steps + 1)
    for index in 0:steps
        q, p = copy(q0), copy(p0)
        signed_step = index >= origin ? ε : -ε
        for _ in 1:abs(index - origin)
            q, p = advance(q, p, signed_step)
        end
        trajectory[index + 1] = (q, p)
    end
    logweights = [logdensity(q) - sqrt(dot(p, p ./ converted_mass) + m^2)
        for (q, p) in trajectory]
    weights = exp.(logweights .- maximum(logweights))
    draw = uniform_unit!(source) * sum(weights)
    cumulative = 0.0
    for (index, weight) in pairs(weights)
        cumulative += weight
        draw < cumulative && return trajectory[index][1]
    end
    trajectory[end][1]
end

function certified_relativistic_multinomial_hmc_step!(source::AbstractRandomSource,
        hamiltonian, metric_factor, integrator, step_size::T, steps::Integer,
        current::AbstractVector{T}, relativistic_mass::T) where {T<:AbstractFloat}
    ε, m = step_size, relativistic_mass
    steps > 0 || throw(ArgumentError("trajectory length must be positive"))
    q0 = collect(current)
    factor = Matrix{T}(metric_factor(q0))
    size(factor) == (length(q0), length(q0)) ||
        throw(DimensionMismatch("metric factor dimension"))
    radius = _relativistic_radius!(source, length(q0), m)
    direction = T[standard_normal!(source) for _ in eachindex(q0)]
    direction_norm = norm(direction)
    direction_norm > 0 || throw(DomainError(direction, "zero spherical direction"))
    p0 = factor \ ((radius / direction_norm) .* direction)
    advance = function (q, p, signed_step)
        result = integrator(q, p, signed_step)
        result isa Tuple && length(result) == 3 ||
            throw(ArgumentError("integrator result"))
        next_q, next_p, certificate = result
        certificate isa ImplicitSolveCertificate && certifies_exact_solver(certificate) ||
            throw(ArgumentError("implicit solve is not exactly certified"))
        T.(next_q), T.(next_p)
    end
    origin = Int(draw_below!(source, steps + 1))
    trajectory = Vector{Tuple{Vector{T},Vector{T}}}(undef, steps + 1)
    for index in 0:steps
        q, p = copy(q0), copy(p0)
        signed_step = index >= origin ? ε : -ε
        for _ in 1:abs(index - origin)
            q, p = advance(q, p, signed_step)
        end
        trajectory[index + 1] = (q, p)
    end
    logweights = [-T(hamiltonian(q, p)) for (q, p) in trajectory]
    weights = exp.(logweights .- maximum(logweights))
    draw = uniform_unit!(source) * sum(weights)
    cumulative = 0.0
    for (index, weight) in pairs(weights)
        cumulative += weight
        draw < cumulative && return trajectory[index][1]
    end
    trajectory[end][1]
end

"""Independent generic floating-point implementation of classical RMHMC."""
function classical_rmhmc_step!(source::AbstractRandomSource, hamiltonian,
        metric_factor, integrator, step_size::T, steps::Integer,
        current::AbstractVector{T}) where {T<:AbstractFloat}
    isfinite(step_size) && step_size > 0 || throw(ArgumentError(
        "step size must be finite and positive"))
    steps > 0 || throw(ArgumentError("trajectory length must be positive"))
    q0 = collect(current)
    isempty(q0) && throw(ArgumentError("position cannot be empty"))
    all(isfinite, q0) || throw(ArgumentError("position must be finite"))
    factor = Matrix{T}(metric_factor(q0))
    size(factor) == (length(q0), length(q0)) ||
        throw(DimensionMismatch("metric factor dimension"))
    all(isfinite, factor) || throw(ArgumentError("metric factor must be finite"))
    abs(det(factor)) > 0 || throw(ArgumentError("metric factor must be invertible"))
    p0 = factor \ T[standard_normal!(source) for _ in eachindex(q0)]
    q, p = copy(q0), p0
    for _ in 1:steps
        result = integrator(q, p, step_size)
        result isa Tuple && length(result) == 3 ||
            throw(ArgumentError(
                "integrator must return (position, momentum, certificate)"))
        next_q, next_p, certificate = result
        certificate isa ImplicitSolveCertificate && certifies_exact_solver(certificate) ||
            throw(ArgumentError("implicit solve is not exactly certified"))
        q, p = T.(next_q), T.(next_p)
        length(q) == length(q0) && length(p) == length(q0) ||
            throw(DimensionMismatch("integrator state dimension"))
        all(isfinite, q) && all(isfinite, p) ||
            throw(DomainError((q, p), "integrator state"))
    end
    current_energy = T(hamiltonian(q0, p0))
    proposed_energy = T(hamiltonian(q, p))
    isfinite(current_energy) && isfinite(proposed_energy) ||
        throw(DomainError((current_energy, proposed_energy),
            "Hamiltonian must be finite"))
    threshold = exp(min(zero(T), current_energy - proposed_energy))
    T(uniform_unit!(source)) < threshold ? q : q0
end

"""Independent bounded-residual position-dependent classical RMHMC path."""
function approximate_classical_rmhmc_step!(source::AbstractRandomSource,
        hamiltonian, metric_factor, integrator, step_size::T, steps::Integer,
        current::AbstractVector{T}, residual_tolerance::T) where {T<:AbstractFloat}
    isfinite(residual_tolerance) && residual_tolerance >= 0 ||
        throw(ArgumentError("residual tolerance must be finite and nonnegative"))
    isfinite(step_size) && step_size > 0 || throw(ArgumentError(
        "step size must be finite and positive"))
    steps > 0 || throw(ArgumentError("trajectory length must be positive"))
    q0 = collect(current)
    isempty(q0) && throw(ArgumentError("position cannot be empty"))
    factor = Matrix{T}(metric_factor(q0))
    size(factor) == (length(q0), length(q0)) ||
        throw(DimensionMismatch("metric factor dimension"))
    all(isfinite, factor) || throw(ArgumentError("metric factor must be finite"))
    abs(det(factor)) > 0 || throw(ArgumentError("metric factor must be invertible"))
    p0 = factor \ T[standard_normal!(source) for _ in eachindex(q0)]
    q, p = copy(q0), p0
    for _ in 1:steps
        next_q, next_p, certificate = integrator(q, p, step_size)
        certificate isa ImplicitSolveCertificate || throw(ArgumentError(
            "integrator did not return an implicit-solver certificate"))
        certificate.half_momentum_residual.bound <= residual_tolerance &&
            certificate.position_residual.bound <= residual_tolerance ||
            throw(ArgumentError("implicit solve exceeds residual tolerance"))
        q, p = T.(next_q), T.(next_p)
        length(q) == length(q0) && length(p) == length(q0) ||
            throw(DimensionMismatch("integrator state dimension"))
        all(isfinite, q) && all(isfinite, p) ||
            throw(DomainError((q, p), "integrator state"))
    end
    current_energy = T(hamiltonian(q0, p0))
    proposed_energy = T(hamiltonian(q, p))
    isfinite(current_energy) && isfinite(proposed_energy) ||
        throw(DomainError((current_energy, proposed_energy),
            "Hamiltonian must be finite"))
    threshold = exp(min(zero(T), current_energy - proposed_energy))
    T(uniform_unit!(source)) < threshold ? q : q0
end

"""Independent generic floating-point implementation of scalar endpoint HMC."""
function scalar_hmc_step!(source::AbstractRandomSource, logdensity, gradient,
        step_size::T, steps::Integer, current::T) where {T<:AbstractFloat}
    checked_positive_float(step_size, "step size")
    checked_positive_count(steps, "leapfrog steps")
    checked_finite_float(current, "current state")
    ε, initial = step_size, current
    momentum = T(standard_normal!(source))
    next_position, next_momentum = initial, momentum
    for _ in 1:steps
        next_position, next_momentum = leapfrog(
            gradient, ε, next_position, next_momentum)
    end
    current_energy = -logdensity(initial) + momentum^2 / 2
    next_energy = -logdensity(next_position) + next_momentum^2 / 2
    log(uniform_unit!(source)) < min(0.0, current_energy - next_energy) ?
        next_position : initial
end

"""Tested generic floating-point Gaussian RWMH step; not exact Lean `ℝ`."""
function gaussian_rwmh_step!(source::AbstractRandomSource, logdensity,
        scale::T, current::T) where {T<:AbstractFloat}
    checked_positive_float(scale, "scale")
    checked_finite_float(current, "current state")
    σ, initial = scale, current
    proposal = initial + σ * T(standard_normal!(source))
    logratio = logdensity(proposal) - logdensity(initial)
    log(uniform_unit!(source)) < min(zero(logratio), logratio) ? proposal : initial
end

"""Maintained categorical implementation using cumulative sums and binary search."""
function categorical_index!(source::AbstractRandomSource, weights::AbstractVector{<:Integer})
    all(weight -> weight >= 0, weights) || throw(ArgumentError("weights must be nonnegative"))
    cumulative = cumsum(BigInt.(weights))
    isempty(cumulative) && throw(ArgumentError("weights must have positive total"))
    total = cumulative[end]
    total > 0 || throw(ArgumentError("weights must have positive total"))
    draw = draw_below!(source, total)
    searchsortedfirst(cumulative, draw + 1) - 1
end

"""Optimized exact-integer finite-HMM particle-Gibbs update."""
function finite_hmm_particle_gibbs_step!(source::AbstractRandomSource,
        initial_weights::AbstractVector{<:Integer},
        transition_weights::AbstractMatrix{<:Integer},
        potentials::AbstractMatrix{<:Integer}, particles::Integer,
        current_path::AbstractVector{<:Integer})
    particles > 0 || throw(ArgumentError("particle count must be positive"))
    states, horizon = length(initial_weights), size(potentials, 1)
    states > 0 || throw(ArgumentError("state space cannot be empty"))
    size(transition_weights) == (states, states) || throw(DimensionMismatch("transition matrix"))
    size(potentials, 2) == states || throw(DimensionMismatch("potentials"))
    length(current_path) == horizon + 1 || throw(DimensionMismatch("reference path horizon"))
    all(x -> 1 <= x <= states, current_path) || throw(ArgumentError("reference path state"))
    all(>=(0), initial_weights) && sum(initial_weights) > 0 || throw(ArgumentError("initial weights"))
    all(>=(0), transition_weights) && all(row -> sum(row) > 0, eachrow(transition_weights)) ||
        throw(ArgumentError("transition weights"))
    all(>(0), potentials) || throw(ArgumentError("potentials must be positive"))

    count = Int(particles)
    retained = Int(draw_below!(source, count)) + 1
    population = [i == retained ? Int(current_path[1]) :
        categorical_index!(source, initial_weights) + 1 for i in 1:count]
    populations = Matrix{Int}(undef, count, horizon + 1)
    populations[:, 1] = population
    ancestors = Matrix{Int}(undef, count, horizon)
    for t in 1:horizon
        next_retained = Int(draw_below!(source, count)) + 1
        weights = @views potentials[t, population]
        for i in 1:count
            ancestors[i, t] = i == next_retained ? retained :
                categorical_index!(source, weights) + 1
        end
        next_population = Vector{Int}(undef, count)
        for i in 1:count
            parent = population[ancestors[i, t]]
            next_population[i] = i == next_retained ? Int(current_path[t + 1]) :
                categorical_index!(source, @view transition_weights[parent, :]) + 1
        end
        populations[:, t + 1] = next_population
        population, retained = next_population, next_retained
    end
    terminal = Int(draw_below!(source, count)) + 1
    path = Vector{Int}(undef, horizon + 1)
    path[end] = populations[terminal, end]
    for t in horizon:-1:1
        terminal = ancestors[terminal, t]
        path[t] = populations[terminal, t]
    end
    path
end

"""Maintained optimized implementation of the verified two-state MH example."""
function two_state_mh_step!(source::AbstractRandomSource, current::Integer)
    finite_mh_step!(source, BigInt[1, 3], [BigInt[1, 1], BigInt[1, 1]], current)
end

function finite_mh_step!(source::AbstractRandomSource,
        target::AbstractVector{<:Integer}, proposal::AbstractVector, current::Integer)
    state_count = length(target)
    state_count > 0 || throw(ArgumentError("target weights must be positive"))
    all(weight -> weight > 0, target) ||
        throw(ArgumentError("target weights must be positive"))
    length(proposal) == state_count || throw(DimensionMismatch("proposal row count"))
    all(row -> length(row) == state_count, proposal) ||
        throw(DimensionMismatch("proposal column count"))
    all(row -> all(weight -> weight >= 0, row) && sum(big, row) > 0, proposal) ||
        throw(ArgumentError("proposal rows need nonnegative weights and positive totals"))
    0 <= current < state_count || throw(ArgumentError("current state is out of range"))

    proposed = categorical_index!(source, proposal[current + 1])
    proposed == current && return current
    current_total = sum(big, proposal[current + 1])
    proposed_total = sum(big, proposal[proposed + 1])
    acceptance_bound = big(target[current + 1]) *
        big(proposal[current + 1][proposed + 1]) * proposed_total
    acceptance_mass = min(acceptance_bound,
        big(target[proposed + 1]) * big(proposal[proposed + 1][current + 1]) * current_total)
    draw_below!(source, acceptance_bound) < acceptance_mass ? proposed : current
end

end
