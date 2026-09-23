module Optimized

using LinearAlgebra

using ...Runtime: AbstractRandomSource, draw_below!, standard_normal!,
    uniform_unit!, checked_positive_float, checked_positive_count,
    checked_finite_float
using ...Certificates: ImplicitSolveCertificate, certify_implicit_solve,
    certifies_exact_solver

export categorical_index!, integer_slice_step!, bounded_slice_step!, stepping_out_slice_step!, sheared_birth_death_step!, spatial_birth_death_step!, finite_mh_step!, two_state_mh_step!, gaussian_rwmh_step!, scalar_barker_rwmh_step!, scalar_mala_step!, vector_mala_step!, dense_pmala_step!,
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
    vector_gauss_legendre_step, vector_gauss_legendre_hmc_step!,
    vector_gauss_legendre_simd_step,
    affine_prefix_scan, speculative_trajectory, certified_trajectory,
    certified_speculative_trajectory,
    AbstractPreparedMetric, PreparedDiagonalMetric, PreparedDenseMetric,
    prepare_metric,
    MALAWorkspace, prepare_mala_workspace,
    DensePMALAWorkspace, prepare_dense_pmala_workspace,
    MultiMarginalTransportHMCWorkspace, multi_marginal_transport_hmc_step!

@inline _affine_comp(later, earlier) =
    (later[1] * earlier[1], later[1] * earlier[2] + later[2])

function affine_prefix_scan(segments::AbstractVector{<:Tuple};
        parallel::Bool=Threads.nthreads() > 1)
    current = collect(segments)
    offset = 1
    while offset < length(current)
        previous = copy(current)
        if parallel
            Threads.@threads for index in (offset + 1):length(current)
                current[index] = _affine_comp(previous[index], previous[index - offset])
            end
        else
            for index in (offset + 1):length(current)
                current[index] = _affine_comp(previous[index], previous[index - offset])
            end
        end
        offset *= 2
    end
    current
end

function certified_trajectory(step, initial, candidate::AbstractVector)
    current = initial
    for proposed in candidate
        expected = step(current)
        proposed == expected || return foldl((x, _) -> step(x), candidate;
            init=initial), false
        current = proposed
    end
    current, true
end

function speculative_trajectory(step, initial, length::Integer, passes::Integer;
        parallel::Bool=Threads.nthreads() > 1)
    length >= 0 || throw(ArgumentError("trajectory length must be nonnegative"))
    passes >= 0 || throw(ArgumentError("pass count must be nonnegative"))
    current = fill(initial, length)
    for _ in 1:passes
        previous = current
        current = similar(previous)
        if parallel
            Threads.@threads for index in eachindex(current)
                parent = index == firstindex(current) ? initial : previous[index - 1]
                current[index] = step(parent)
            end
        else
            for index in eachindex(current)
                parent = index == firstindex(current) ? initial : previous[index - 1]
                current[index] = step(parent)
            end
        end
    end
    current
end

function certified_speculative_trajectory(step, initial, length::Integer,
        passes::Integer; parallel::Bool=Threads.nthreads() > 1)
    candidate = speculative_trajectory(step, initial, length, passes; parallel)
    certified_trajectory(step, initial, candidate)
end

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

"""Generic two-stage Gauss--Legendre step with optionally concurrent stages."""
function vector_gauss_legendre_step(gradient, step_size::T,
        iterations::Integer, position::AbstractVector{T},
        momentum::AbstractVector{T}; parallel::Bool=false) where {T<:AbstractFloat}
    length(position) == length(momentum) || throw(DimensionMismatch("phase state"))
    iterations > 0 || throw(ArgumentError("stage iterations must be positive"))
    n = length(position)
    z = vcat(position, momentum)
    function field(state)
        q = @view state[1:n]
        p = @view state[(n + 1):(2n)]
        force = T.(gradient(q))
        length(force) == n || throw(DimensionMismatch("gradient"))
        vcat(p, -force)
    end
    k1, k2 = field(z), field(z)
    radius = sqrt(T(3)) / T(6)
    a11, a12, a21, a22 = T(1)/T(4), T(1)/T(4)-radius,
        T(1)/T(4)+radius, T(1)/T(4)
    for _ in 1:iterations
        state1 = z .+ step_size .* (a11 .* k1 .+ a12 .* k2)
        state2 = z .+ step_size .* (a21 .* k1 .+ a22 .* k2)
        if parallel
            task = Threads.@spawn field(state1)
            next2 = field(state2)
            next1 = fetch(task)
            k1, k2 = next1, next2
        else
            k1, k2 = field(state1), field(state2)
        end
    end
    next = z .+ (step_size / T(2)) .* (k1 .+ k2)
    collect(@view(next[1:n])), collect(@view(next[(n + 1):(2n)]))
end

"""Two-stage Gauss--Legendre step using a batched gradient and SIMD stage algebra.

`batched_gradient!(output, positions)` must fill column `j` of `output` with
the gradient at column `j` of `positions`.  Keeping this interface explicit is
important: an arbitrary scalar callback cannot safely be assumed to support
vectorization across Runge--Kutta stages.
"""
function vector_gauss_legendre_simd_step(batched_gradient!, step_size::T,
        iterations::Integer, position::AbstractVector{T},
        momentum::AbstractVector{T}) where {T<:AbstractFloat}
    length(position) == length(momentum) || throw(DimensionMismatch("phase state"))
    iterations > 0 || throw(ArgumentError("stage iterations must be positive"))
    n = length(position)
    positions = Matrix{T}(undef, n, 2)
    momenta = Matrix{T}(undef, n, 2)
    gradients = Matrix{T}(undef, n, 2)
    initial_gradient = Matrix{T}(undef, n, 2)
    @inbounds @simd for index in eachindex(position)
        positions[index, 1] = position[index]
        positions[index, 2] = position[index]
    end
    batched_gradient!(initial_gradient, positions)
    size(initial_gradient) == (n, 2) || throw(DimensionMismatch("batched gradient"))
    @inbounds @simd for index in eachindex(position)
        momenta[index, 1] = momentum[index]
        momenta[index, 2] = momentum[index]
    end

    radius = sqrt(T(3)) / T(6)
    a11, a12 = T(1) / T(4), T(1) / T(4) - radius
    a21, a22 = T(1) / T(4) + radius, T(1) / T(4)
    for _ in 1:iterations
        @inbounds @simd for index in eachindex(position)
            p1, p2 = momenta[index, 1], momenta[index, 2]
            g1, g2 = initial_gradient[index, 1], initial_gradient[index, 2]
            positions[index, 1] = position[index] + step_size * (a11*p1 + a12*p2)
            positions[index, 2] = position[index] + step_size * (a21*p1 + a22*p2)
            momenta[index, 1] = momentum[index] - step_size * (a11*g1 + a12*g2)
            momenta[index, 2] = momentum[index] - step_size * (a21*g1 + a22*g2)
        end
        batched_gradient!(gradients, positions)
        initial_gradient, gradients = gradients, initial_gradient
    end

    next_position, next_momentum = similar(position), similar(momentum)
    @inbounds @simd for index in eachindex(position)
        next_position[index] = position[index] +
            (step_size / T(2)) * (momenta[index, 1] + momenta[index, 2])
        next_momentum[index] = momentum[index] -
            (step_size / T(2)) * (initial_gradient[index, 1] + initial_gradient[index, 2])
    end
    next_position, next_momentum
end

"""Generic maintained endpoint HMC using fixed-work stage-parallel GL2."""
function vector_gauss_legendre_hmc_step!(source::AbstractRandomSource,
        logdensity, gradient, step_size::T, steps::Integer,
        iterations::Integer, current::AbstractVector{T};
        parallel::Bool=false, batched_gradient! = nothing) where {T<:AbstractFloat}
    isfinite(step_size) && step_size > 0 || throw(ArgumentError("step size"))
    steps > 0 || throw(ArgumentError("integration steps must be positive"))
    iterations > 0 || throw(ArgumentError("stage iterations must be positive"))
    initial = collect(current)
    p0 = T[standard_normal!(source) for _ in eachindex(initial)]
    q, p = copy(initial), copy(p0)
    for _ in 1:steps
        q, p = isnothing(batched_gradient!) ?
            vector_gauss_legendre_step(gradient, step_size, iterations,
                q, p; parallel) :
            vector_gauss_legendre_simd_step(batched_gradient!, step_size,
                iterations, q, p)
    end
    current_energy = -T(logdensity(initial)) + sum(abs2, p0) / T(2)
    next_energy = -T(logdensity(q)) + sum(abs2, p) / T(2)
    log(T(uniform_unit!(source))) < min(zero(T), current_energy - next_energy) ?
        q : initial
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
    d = length(q)

    p = Vector{T}(undef, d)
    @inbounds for i in eachindex(p)
        p[i] = T(standard_normal!(source))
    end
    origin = Int(draw_below!(source, steps + 1))

    positions = Matrix{T}(undef, d, steps + 1)
    logweights = Vector{T}(undef, steps + 1)
    half_step = ε / T(2)

    current_index = origin + 1
    positions[:, current_index] = q
    logweights[current_index] = logdensity(q) - sum(abs2, p) / T(2)

    bq, bp = copy(q), copy(p)
    for index in origin:-1:1
        force = gradient(bq)
        @. bp += half_step * force
        @. bq -= ε * bp
        force = gradient(bq)
        @. bp += half_step * force
        positions[:, index] = bq
        logweights[index] = logdensity(bq) - sum(abs2, bp) / T(2)
    end

    fq, fp = copy(q), copy(p)
    for index in (origin + 2):(steps + 1)
        force = gradient(fq)
        @. fp -= half_step * force
        @. fq += ε * fp
        force = gradient(fq)
        @. fp -= half_step * force
        positions[:, index] = fq
        logweights[index] = logdensity(fq) - sum(abs2, fp) / T(2)
    end

    max_weight = maximum(logweights)
    total = zero(T)
    @inbounds for i in eachindex(logweights)
        logweights[i] = exp(logweights[i] - max_weight)
        total += logweights[i]
    end
    target = T(uniform_unit!(source)) * total
    cumulative = zero(T)
    selected = steps + 1
    @inbounds for i in eachindex(logweights)
        cumulative += logweights[i]
        if target < cumulative
            selected = i
            break
        end
    end
    copy(@view positions[:, selected])
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

function _dense_metric_multinomial_step!(source::AbstractRandomSource, logdensity,
        gradient, step_size::T, steps::Integer,
        current::AbstractVector{T}, metric::PreparedDenseMetric{T}) where {T<:AbstractFloat}
    isfinite(step_size) && step_size > 0 || throw(ArgumentError(
        "step size must be finite and positive"))
    steps > 0 || throw(ArgumentError("trajectory length must be positive"))
    eltype(metric.mass) === T || throw(ArgumentError(
        "state and metric element types must match"))
    ε, initial_q = step_size, collect(current)
    isempty(initial_q) && throw(ArgumentError("position cannot be empty"))
    all(isfinite, initial_q) || throw(ArgumentError("position must be finite"))
    metric_dimension(metric) == length(initial_q) || throw(DimensionMismatch(
        "mass dimension"))

    noise = T[standard_normal!(source) for _ in eachindex(initial_q)]
    initial_p = similar(initial_q)
    mul!(initial_p, metric.factorization.L, noise)

    initial_v = similar(initial_q)
    mul!(initial_v, metric.inverse_mass, initial_p)

    g_workspace = similar(initial_q)

    origin = Int(draw_below!(source, steps + 1))
    initial_force = gradient(initial_q)
    mul!(g_workspace, metric.inverse_mass, initial_force)
    initial_g = copy(g_workspace)

    d = length(initial_q)
    positions = Matrix{T}(undef, d, steps + 1)
    initial_ke = sum(abs2, noise) / T(2)
    initial_logweight = logdensity(initial_q) - initial_ke
    logweights = Vector{typeof(initial_logweight)}(undef, steps + 1)
    current_index = origin + 1
    positions[:, current_index] = initial_q
    logweights[current_index] = initial_logweight

    half_step = ε / T(2)

    q, p, v = copy(initial_q), copy(initial_p), copy(initial_v)
    force = initial_force
    g = copy(initial_g)
    for index in origin:-1:1
        @. p += half_step * force
        @. v += half_step * g
        @. q -= ε * v
        force = gradient(q)
        mul!(g_workspace, metric.inverse_mass, force)
        @. p += half_step * force
        @. v += half_step * g_workspace
        copyto!(g, g_workspace)
        positions[:, index] = q
        logweights[index] = logdensity(q) - dot(p, v) / T(2)
    end

    q, p, v = copy(initial_q), copy(initial_p), copy(initial_v)
    force = initial_force
    copyto!(g, initial_g)
    for index in (origin + 2):(steps + 1)
        @. p -= half_step * force
        @. v -= half_step * g
        @. q += ε * v
        force = gradient(q)
        mul!(g_workspace, metric.inverse_mass, force)
        @. p -= half_step * force
        @. v -= half_step * g_workspace
        copyto!(g, g_workspace)
        positions[:, index] = q
        logweights[index] = logdensity(q) - dot(p, v) / T(2)
    end

    weights = exp.(logweights .- maximum(logweights))
    target = uniform_unit!(source) * sum(weights)
    cumulative = zero(T)
    for (index, weight) in pairs(weights)
        cumulative += weight
        target < cumulative && return copy(@view positions[:, index])
    end
    copy(@view positions[:, end])
end

function metric_multinomial_hmc_step!(source::AbstractRandomSource, logdensity,
        gradient, step_size::T, steps::Integer,
        current::AbstractVector{T},
        metric::PreparedDenseMetric{T}) where {T<:AbstractFloat}
    _dense_metric_multinomial_step!(source, logdensity, gradient, step_size,
        steps, current, metric)
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

"""Tested generic floating-point Barker RWMH step with sigmoid acceptance."""
function scalar_barker_rwmh_step!(source::AbstractRandomSource, logdensity,
        scale::T, current::T) where {T<:AbstractFloat}
    checked_positive_float(scale, "scale")
    checked_finite_float(current, "current state")
    noise = T(standard_normal!(source))
    proposed = current + scale * noise
    current_log_density = T(logdensity(current))
    isfinite(current_log_density) || throw(DomainError(current_log_density, "logdensity must be finite"))
    proposed_log_density = T(logdensity(proposed))
    isfinite(proposed_log_density) || throw(DomainError(proposed_log_density, "logdensity must be finite"))
    log_ratio = proposed_log_density - current_log_density
    threshold = one(T) / (one(T) + exp(-log_ratio))
    T(uniform_unit!(source)) < threshold ? proposed : current
end

"""Maintained generic scalar MALA step with the asymmetric Hastings correction."""
function scalar_mala_step!(source::AbstractRandomSource, logdensity, gradient,
        step_size::T, current::T) where {T<:AbstractFloat}
    checked_positive_float(step_size, "step size")
    checked_finite_float(current, "current state")
    variance = step_size * step_size
    half_variance = variance / T(2)
    current_gradient = T(gradient(current))
    isfinite(current_gradient) || throw(DomainError(current_gradient, "gradient must be finite"))
    proposed = current + half_variance * current_gradient +
        step_size * T(standard_normal!(source))
    proposed_gradient = T(gradient(proposed))
    isfinite(proposed_gradient) || throw(DomainError(proposed_gradient, "gradient must be finite"))
    forward_residual = proposed - (current + half_variance * current_gradient)
    reverse_residual = current - (proposed + half_variance * proposed_gradient)
    logratio = T(logdensity(proposed)) - T(logdensity(current)) +
        (forward_residual^2 - reverse_residual^2) / (T(2) * variance)
    isfinite(logratio) || throw(DomainError(logratio, "MALA log ratio must be finite"))
    T(uniform_unit!(source)) < exp(min(zero(T), logratio)) ? proposed : current
end

"""Pre-allocated workspace for zero-allocation steady-state MALA steps."""
struct MALAWorkspace{T<:AbstractFloat}
    proposed::Vector{T}
    current_gradient::Vector{T}
    proposed_gradient::Vector{T}
end

"""Allocate a MALA workspace sized for vectors matching `current`."""
function prepare_mala_workspace(current::AbstractVector{T}) where {T<:AbstractFloat}
    n = length(current)
    MALAWorkspace{T}(Vector{T}(undef, n), Vector{T}(undef, n), Vector{T}(undef, n))
end

function _convert_gradient_validated!(dest::Vector{T}, src, current_length::Int) where {T}
    length(src) == current_length || throw(DimensionMismatch("gradient dimension"))
    @inbounds for i in eachindex(dest)
        dest[i] = T(src[i])
        isfinite(dest[i]) || throw(DomainError(src, "gradient must be finite"))
    end
    dest
end

"""Maintained generic isotropic vector MALA step with pre-allocated workspace."""
function vector_mala_step!(source::AbstractRandomSource, logdensity, gradient,
        step_size::T, current::AbstractVector{T},
        workspace::MALAWorkspace{T}) where {T<:AbstractFloat}
    checked_positive_float(step_size, "step size")
    isempty(current) && throw(ArgumentError("position cannot be empty"))
    all(isfinite, current) || throw(DomainError(current, "position must be finite"))
    variance = step_size * step_size
    half_variance = variance / T(2)
    _convert_gradient_validated!(workspace.current_gradient, gradient(current), length(current))
    proposed = workspace.proposed
    noise_sq_sum = zero(T)
    @inbounds for index in eachindex(current)
        noise = T(standard_normal!(source))
        noise_sq_sum += noise * noise
        proposed[index] = muladd(half_variance, workspace.current_gradient[index],
            muladd(step_size, noise, current[index]))
    end
    _convert_gradient_validated!(workspace.proposed_gradient, gradient(proposed), length(current))
    forward_norm = variance * noise_sq_sum
    reverse_norm = zero(T)
    @inbounds @simd for index in eachindex(current)
        reverse = current[index] - (proposed[index] + half_variance * workspace.proposed_gradient[index])
        reverse_norm += reverse * reverse
    end
    logratio = T(logdensity(proposed)) - T(logdensity(current)) +
        (forward_norm - reverse_norm) / (T(2) * variance)
    isfinite(logratio) || throw(DomainError(logratio, "MALA log ratio must be finite"))
    T(uniform_unit!(source)) < exp(min(zero(T), logratio)) ? proposed : copy(current)
end

"""Maintained generic isotropic vector MALA step."""
function vector_mala_step!(source::AbstractRandomSource, logdensity, gradient,
        step_size::T, current::AbstractVector{T}) where {T<:AbstractFloat}
    vector_mala_step!(source, logdensity, gradient, step_size, current,
        prepare_mala_workspace(current))
end

"""Pre-allocated workspace for zero-allocation steady-state dense PMALA steps."""
struct DensePMALAWorkspace{T<:AbstractFloat}
    current_matrix::Matrix{T}
    current_mean::Vector{T}
    proposed_matrix::Matrix{T}
    proposed_mean::Vector{T}
    score::Vector{T}
    inverse_metric::Matrix{T}
    derivative::Array{T,3}
    divergence::Vector{T}
    temp_matrix::Matrix{T}
    temp_vector::Vector{T}
    noise::Vector{T}
    proposed::Vector{T}
    residual::Vector{T}
end

"""Allocate a dense PMALA workspace sized for vectors matching `current`."""
function prepare_dense_pmala_workspace(current::AbstractVector{T}) where {T<:AbstractFloat}
    d = length(current)
    DensePMALAWorkspace{T}(
        Matrix{T}(undef, d, d),
        Vector{T}(undef, d),
        Matrix{T}(undef, d, d),
        Vector{T}(undef, d),
        Vector{T}(undef, d),
        Matrix{T}(undef, d, d),
        Array{T,3}(undef, d, d, d),
        Vector{T}(undef, d),
        Matrix{T}(undef, d, d),
        Vector{T}(undef, d),
        Vector{T}(undef, d),
        Vector{T}(undef, d),
        Vector{T}(undef, d),
    )
end

function _dense_pmala_geometry!(matrix_out::Matrix{T}, mean_out::Vector{T},
        workspace::DensePMALAWorkspace{T}, gradient, metric, metric_derivative,
        step_size::T, position::AbstractVector{T}) where {T<:AbstractFloat}
    dimension = length(position)
    raw_score = gradient(position)
    length(raw_score) == dimension || throw(DimensionMismatch("gradient dimension"))
    @inbounds for i in 1:dimension
        workspace.score[i] = T(raw_score[i])
    end
    all(isfinite, workspace.score) || throw(DomainError(workspace.score, "gradient must be finite"))
    raw_metric = metric(position)
    raw_metric isa AbstractMatrix || throw(ArgumentError("metric must return a matrix"))
    size(raw_metric) == (dimension, dimension) || throw(DimensionMismatch("metric dimension"))
    @inbounds for j in 1:dimension, i in 1:dimension
        matrix_out[i, j] = T(raw_metric[i, j])
    end
    all(isfinite, matrix_out) || throw(DomainError(raw_metric, "metric must be finite"))
    issymmetric(matrix_out) || throw(ArgumentError("metric must be symmetric"))
    factor = try
        cholesky(Symmetric(matrix_out))
    catch error
        error isa PosDefException || rethrow()
        throw(DomainError(raw_metric, "metric must be positive definite"))
    end
    fill!(workspace.inverse_metric, zero(T))
    @inbounds for i in 1:dimension
        workspace.inverse_metric[i, i] = one(T)
    end
    ldiv!(factor, workspace.inverse_metric)
    raw_derivative = metric_derivative(position)
    raw_derivative isa AbstractArray || throw(ArgumentError(
        "metric derivative must return a rank-three array"))
    ndims(raw_derivative) == 3 && size(raw_derivative) ==
        (dimension, dimension, dimension) ||
        throw(DimensionMismatch("metric derivative dimension"))
    @inbounds for k in 1:dimension, j in 1:dimension, i in 1:dimension
        workspace.derivative[i, j, k] = T(raw_derivative[i, j, k])
    end
    all(isfinite, workspace.derivative) || throw(DomainError(raw_derivative,
        "metric derivative must be finite"))
    fill!(workspace.divergence, zero(T))
    @inbounds for coordinate in 1:dimension
        mul!(workspace.temp_matrix, workspace.inverse_metric,
            @view(workspace.derivative[:, :, coordinate]))
        mul!(workspace.temp_vector, workspace.temp_matrix,
            @view(workspace.inverse_metric[:, coordinate]))
        workspace.divergence .-= workspace.temp_vector
    end
    mul!(workspace.temp_vector, workspace.inverse_metric, workspace.score)
    @inbounds for i in 1:dimension
        mean_out[i] = position[i] + (step_size^2 / T(2)) *
            (workspace.temp_vector[i] + workspace.divergence[i])
    end
    logdet_val = zero(T)
    @inbounds for i in 1:dimension
        logdet_val += log(factor.L[i, i])
    end
    logdet_val *= T(2)
    factor, logdet_val
end

"""Generic dense Lebesgue-correct PMALA transition with pre-allocated workspace."""
function dense_pmala_step!(source::AbstractRandomSource, logdensity, gradient,
        metric, metric_derivative, step_size::T,
        current::AbstractVector{T},
        workspace::DensePMALAWorkspace{T}) where {T<:AbstractFloat}
    checked_positive_float(step_size, "step size")
    isempty(current) && throw(ArgumentError("position cannot be empty"))
    all(isfinite, current) || throw(DomainError(current, "position must be finite"))
    length(current) == length(workspace.score) ||
        throw(DimensionMismatch("workspace dimension does not match state"))
    current_factor, current_logdet = _dense_pmala_geometry!(
        workspace.current_matrix, workspace.current_mean, workspace,
        gradient, metric, metric_derivative, step_size, current)
    @inbounds for i in eachindex(workspace.noise)
        workspace.noise[i] = T(standard_normal!(source))
    end
    copyto!(workspace.temp_vector, workspace.noise)
    ldiv!(current_factor.U, workspace.temp_vector)
    @inbounds for i in eachindex(workspace.proposed)
        workspace.proposed[i] = workspace.current_mean[i] +
            step_size * workspace.temp_vector[i]
    end
    _, proposed_logdet = _dense_pmala_geometry!(
        workspace.proposed_matrix, workspace.proposed_mean, workspace,
        gradient, metric, metric_derivative, step_size, workspace.proposed)
    @inbounds for i in eachindex(workspace.residual)
        workspace.residual[i] = workspace.proposed[i] - workspace.current_mean[i]
    end
    mul!(workspace.temp_vector, workspace.current_matrix, workspace.residual)
    forward_quadratic = dot(workspace.residual, workspace.temp_vector) / step_size^2
    @inbounds for i in eachindex(workspace.residual)
        workspace.residual[i] = current[i] - workspace.proposed_mean[i]
    end
    mul!(workspace.temp_vector, workspace.proposed_matrix, workspace.residual)
    reverse_quadratic = dot(workspace.residual, workspace.temp_vector) / step_size^2
    proposed_logdensity = T(logdensity(workspace.proposed))
    current_logdensity = T(logdensity(current))
    all(isfinite, (proposed_logdensity, current_logdensity)) ||
        throw(DomainError((proposed_logdensity, current_logdensity),
            "logdensity must be finite"))
    logratio = proposed_logdensity - current_logdensity +
        (proposed_logdet - current_logdet) / T(2) -
        (reverse_quadratic - forward_quadratic) / T(2)
    isfinite(logratio) || throw(DomainError(logratio, "PMALA log ratio must be finite"))
    T(uniform_unit!(source)) < exp(min(zero(T), logratio)) ?
        workspace.proposed : copy(current)
end

"""Generic dense Lebesgue-correct position-dependent MALA transition."""
function dense_pmala_step!(source::AbstractRandomSource, logdensity, gradient,
        metric, metric_derivative, step_size::T,
        current::AbstractVector{T}) where {T<:AbstractFloat}
    dense_pmala_step!(source, logdensity, gradient, metric, metric_derivative,
        step_size, current, prepare_dense_pmala_workspace(current))
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

"""Preallocated workspace for multi-marginal transport HMC."""
mutable struct MultiMarginalTransportHMCWorkspace{T<:AbstractFloat}
    dim::Int
    chain_count::Int
    momentum::Vector{T}
    positions::Matrix{T}
    logweights::Vector{T}
    forward_q::Vector{T}
    forward_p::Vector{T}
    backward_q::Vector{T}
    backward_p::Vector{T}
    force::Vector{T}
end

function MultiMarginalTransportHMCWorkspace{T}(dim::Int, chain_count::Int,
        steps::Int) where {T<:AbstractFloat}
    dim > 0 || throw(ArgumentError("dimension must be positive"))
    chain_count > 0 || throw(ArgumentError("chain_count must be positive"))
    steps > 0 || throw(ArgumentError("steps must be positive"))
    MultiMarginalTransportHMCWorkspace{T}(dim, chain_count,
        Vector{T}(undef, dim), Matrix{T}(undef, dim, steps + 1),
        Vector{T}(undef, steps + 1), Vector{T}(undef, dim),
        Vector{T}(undef, dim), Vector{T}(undef, dim),
        Vector{T}(undef, dim), Vector{T}(undef, dim))
end

function _multinomial_select_with_shared_momentum!(
        source::AbstractRandomSource, logdensity, gradient,
        step_size::T, steps::Int, current::AbstractVector{T},
        momentum::AbstractVector{T}, positions::AbstractMatrix{T},
        logweights::AbstractVector{T}, fq::Vector{T}, fp::Vector{T},
        bq::Vector{T}, bp::Vector{T}, force::Vector{T}) where {T<:AbstractFloat}
    d = length(current)
    ε = step_size
    half_step = ε / T(2)
    origin = Int(draw_below!(source, steps + 1))
    current_index = origin + 1
    @inbounds positions[:, current_index] = current
    logweights[current_index] = T(logdensity(current)) - sum(abs2, momentum) / T(2)
    copyto!(bq, current)
    copyto!(bp, momentum)
    for index in origin:-1:1
        force .= T.(gradient(bq))
        @. bp += half_step * force
        @. bq -= ε * bp
        force .= T.(gradient(bq))
        @. bp += half_step * force
        @inbounds positions[:, index] = bq
        logweights[index] = T(logdensity(bq)) - sum(abs2, bp) / T(2)
    end
    copyto!(fq, current)
    copyto!(fp, momentum)
    for index in (origin + 2):(steps + 1)
        force .= T.(gradient(fq))
        @. fp -= half_step * force
        @. fq += ε * fp
        force .= T.(gradient(fq))
        @. fp -= half_step * force
        @inbounds positions[:, index] = fq
        logweights[index] = T(logdensity(fq)) - sum(abs2, fp) / T(2)
    end
    max_weight = maximum(logweights)
    total = zero(T)
    @inbounds for i in eachindex(logweights)
        logweights[i] = exp(logweights[i] - max_weight)
        total += logweights[i]
    end
    target = T(uniform_unit!(source)) * total
    cumulative = zero(T)
    selected = steps + 1
    @inbounds for i in eachindex(logweights)
        cumulative += logweights[i]
        if target < cumulative
            selected = i
            break
        end
    end
    copy(@view positions[:, selected])
end

"""Multi-marginal transport HMC with preallocated workspace.

All K chains share one momentum draw and independently select trajectory
indices via multinomial weighting.
"""
function multi_marginal_transport_hmc_step!(
        workspace::MultiMarginalTransportHMCWorkspace{T},
        source::AbstractRandomSource, logdensity, gradient,
        step_size::T, steps::Integer, chain_count::Integer,
        current_positions::AbstractVector{T}) where {T<:AbstractFloat}
    K = Int(chain_count)
    K > 0 || throw(ArgumentError("chain_count must be positive"))
    steps > 0 || throw(ArgumentError("trajectory length must be positive"))
    isfinite(step_size) && step_size > 0 ||
        throw(ArgumentError("step size must be finite and positive"))
    total = length(current_positions)
    total > 0 || throw(ArgumentError("positions cannot be empty"))
    total % K == 0 ||
        throw(DimensionMismatch("position length must be divisible by chain_count"))
    dim = total ÷ K
    workspace.dim == dim && workspace.chain_count == K ||
        throw(DimensionMismatch("workspace dimensions do not match"))
    p = workspace.momentum
    @inbounds for i in eachindex(p)
        p[i] = T(standard_normal!(source))
    end
    result = Vector{T}(undef, total)
    for k in 1:K
        offset = (k - 1) * dim
        chain_q = @view current_positions[offset + 1 : offset + dim]
        selected = _multinomial_select_with_shared_momentum!(
            source, logdensity, gradient, step_size, Int(steps),
            chain_q, p, workspace.positions, workspace.logweights,
            workspace.forward_q, workspace.forward_p,
            workspace.backward_q, workspace.backward_p, workspace.force)
        @inbounds result[offset + 1 : offset + dim] = selected
    end
    result
end

"""Multi-marginal transport HMC without preallocated workspace."""
function multi_marginal_transport_hmc_step!(
        source::AbstractRandomSource, logdensity, gradient,
        step_size::T, steps::Integer, chain_count::Integer,
        current_positions::AbstractVector{T}) where {T<:AbstractFloat}
    K = Int(chain_count)
    K > 0 || throw(ArgumentError("chain_count must be positive"))
    steps > 0 || throw(ArgumentError("trajectory length must be positive"))
    isfinite(step_size) && step_size > 0 ||
        throw(ArgumentError("step size must be finite and positive"))
    total = length(current_positions)
    total > 0 || throw(ArgumentError("positions cannot be empty"))
    total % K == 0 ||
        throw(DimensionMismatch("position length must be divisible by chain_count"))
    dim = total ÷ K
    workspace = MultiMarginalTransportHMCWorkspace{T}(dim, K, Int(steps))
    multi_marginal_transport_hmc_step!(workspace, source, logdensity, gradient,
        step_size, steps, chain_count, current_positions)
end

end
