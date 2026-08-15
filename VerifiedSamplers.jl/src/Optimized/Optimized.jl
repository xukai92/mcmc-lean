module Optimized

using LinearAlgebra

using ...Runtime: AbstractRandomSource, draw_below!, standard_normal!, uniform_unit!
using ...Certificates: ImplicitSolveCertificate, certifies_exact_solver

export categorical_index!, finite_mh_step!, two_state_mh_step!, gaussian_rwmh_step!,
    scalar_hmc_step!, vector_hmc_step!, metric_hmc_step!, multinomial_hmc_step!,
    metric_multinomial_hmc_step!,
    relativistic_multinomial_hmc_step!,
    certified_relativistic_multinomial_hmc_step!,
    leapfrog, vector_leapfrog

"""One scalar velocity-Verlet/leapfrog step with unit mass."""
function leapfrog(gradient, step_size::Float64, position::Float64, momentum::Float64)
    half_momentum = momentum - step_size * gradient(position) / 2
    next_position = position + step_size * half_momentum
    next_momentum = half_momentum - step_size * gradient(next_position) / 2
    next_position, next_momentum
end

"""One vector velocity-Verlet/leapfrog step with unit mass."""
function vector_leapfrog(gradient, step_size::Float64,
        position::AbstractVector{<:Real}, momentum::AbstractVector{<:Real})
    half_momentum = momentum .- (step_size / 2) .* gradient(position)
    next_position = position .+ step_size .* half_momentum
    next_momentum = half_momentum .- (step_size / 2) .* gradient(next_position)
    next_position, next_momentum
end

"""Independent Float64 implementation of vector endpoint HMC."""
function vector_hmc_step!(source::AbstractRandomSource, logdensity, gradient,
        step_size::Float64, steps::Integer, current::AbstractVector{<:Real})
    isfinite(step_size) && step_size > 0.0 ||
        throw(ArgumentError("step size must be finite and positive"))
    steps > 0 || throw(ArgumentError("leapfrog steps must be positive"))
    isempty(current) && throw(ArgumentError("position cannot be empty"))
    initial = Float64.(current)
    momentum = [standard_normal!(source) for _ in eachindex(initial)]
    next_position, next_momentum = copy(initial), copy(momentum)
    for _ in 1:steps
        next_position, next_momentum = vector_leapfrog(
            gradient, step_size, next_position, next_momentum)
    end
    current_energy = -logdensity(initial) + sum(abs2, momentum) / 2
    next_energy = -logdensity(next_position) + sum(abs2, next_momentum) / 2
    log(uniform_unit!(source)) < min(0.0, current_energy - next_energy) ?
        next_position : initial
end

"""Independent constant-metric endpoint HMC implementation."""
function metric_hmc_step!(source::AbstractRandomSource, logdensity, gradient,
        step_size::Float64, steps::Integer, current::AbstractVector{<:Real}, mass)
    q = Float64.(current)
    isempty(q) && throw(ArgumentError("position cannot be empty"))
    if mass isa AbstractVector
        length(mass) == length(q) || throw(DimensionMismatch("mass dimension"))
        all(x -> isfinite(x) && x > 0, mass) ||
            throw(ArgumentError("diagonal mass must be finite and positive"))
        p = sqrt.(mass) .* [standard_normal!(source) for _ in eachindex(q)]
        solve_mass = x -> x ./ mass
    else
        size(mass) == (length(q), length(q)) || throw(DimensionMismatch("mass dimension"))
        decomposition = cholesky(Symmetric(Matrix{Float64}(mass)))
        p = decomposition.L * [standard_normal!(source) for _ in eachindex(q)]
        solve_mass = x -> decomposition \ x
    end
    initial_p = copy(p)
    for _ in 1:steps
        p .-= (step_size / 2) .* gradient(q)
        q .+= step_size .* solve_mass(p)
        p .-= (step_size / 2) .* gradient(q)
    end
    current_energy = -logdensity(current) + dot(initial_p, solve_mass(initial_p)) / 2
    proposed_energy = -logdensity(q) + dot(p, solve_mass(p)) / 2
    log(uniform_unit!(source)) < min(0.0, current_energy - proposed_energy) ?
        q : Float64.(current)
end

"""Independent Float64 randomized-origin multinomial HMC implementation."""
function multinomial_hmc_step!(source::AbstractRandomSource, logdensity, gradient,
        step_size::Float64, steps::Integer, current::AbstractVector{<:Real})
    steps > 0 || throw(ArgumentError("trajectory length must be positive"))
    q = Float64.(current)
    isempty(q) && throw(ArgumentError("position cannot be empty"))
    p = [standard_normal!(source) for _ in eachindex(q)]
    origin = Int(draw_below!(source, steps + 1))
    for _ in 1:origin
        q, p = vector_leapfrog(gradient, -step_size, q, p)
    end
    trajectory = Vector{Tuple{Vector{Float64},Vector{Float64}}}(undef, steps + 1)
    trajectory[1] = (copy(q), copy(p))
    for index in 2:(steps + 1)
        q, p = vector_leapfrog(gradient, step_size, q, p)
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
        gradient, step_size::Float64, steps::Integer,
        current::AbstractVector{<:Real}, mass)
    steps > 0 || throw(ArgumentError("trajectory length must be positive"))
    q = Float64.(current)
    isempty(q) && throw(ArgumentError("position cannot be empty"))
    noise = [standard_normal!(source) for _ in eachindex(q)]
    if mass isa AbstractVector
        length(mass) == length(q) || throw(DimensionMismatch("mass dimension"))
        all(x -> isfinite(x) && x > 0, mass) ||
            throw(ArgumentError("diagonal mass must be finite and positive"))
        p = sqrt.(mass) .* noise
        velocity = x -> x ./ mass
    else
        size(mass) == (length(q), length(q)) ||
            throw(DimensionMismatch("mass dimension"))
        factor = cholesky(Symmetric(Matrix{Float64}(mass))).L
        p = factor * noise
        velocity = x -> factor' \ (factor \ x)
    end
    origin = Int(draw_below!(source, steps + 1))
    advance = function (q, p, ε)
        half = p .- (ε / 2) .* gradient(q)
        next_q = q .+ ε .* velocity(half)
        next_p = half .- (ε / 2) .* gradient(next_q)
        next_q, next_p
    end
    for _ in 1:origin
        q, p = advance(q, p, -step_size)
    end
    trajectory = Vector{Tuple{Vector{Float64},Vector{Float64}}}(undef, steps + 1)
    trajectory[1] = (copy(q), copy(p))
    for index in 2:(steps + 1)
        q, p = advance(q, p, step_size)
        trajectory[index] = (copy(q), copy(p))
    end
    logweights = [logdensity(position) - dot(momentum, velocity(momentum)) / 2
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

function _relativistic_radius!(source::AbstractRandomSource, dimension::Int,
        relativistic_mass::Float64)
    while true
        radius = sum((-log1p(-uniform_unit!(source)) for _ in 1:dimension); init=0.0)
        log(uniform_unit!(source)) < radius - sqrt(radius^2 + relativistic_mass^2) &&
            return radius
    end
end

function relativistic_multinomial_hmc_step!(source::AbstractRandomSource,
        logdensity, gradient, step_size::Real, steps::Integer,
        current::AbstractVector{<:Real}, mass::AbstractVector{<:Real},
        relativistic_mass::Real)
    ε, m = Float64(step_size), Float64(relativistic_mass)
    steps > 0 || throw(ArgumentError("trajectory length must be positive"))
    isfinite(ε) && ε > 0 || throw(ArgumentError("step size must be finite and positive"))
    q0 = Float64.(current)
    isempty(q0) && throw(ArgumentError("position cannot be empty"))
    converted_mass = Float64.(mass)
    length(converted_mass) == length(q0) || throw(DimensionMismatch("mass dimension"))
    all(x -> isfinite(x) && x > 0, converted_mass) ||
        throw(ArgumentError("diagonal metric must be finite and positive"))
    isfinite(m) && m > 0 ||
        throw(ArgumentError("relativistic mass must be finite and positive"))
    radius = _relativistic_radius!(source, length(q0), m)
    direction = [standard_normal!(source) for _ in eachindex(q0)]
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
    trajectory = Vector{Tuple{Vector{Float64},Vector{Float64}}}(undef, steps + 1)
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
        hamiltonian, metric_factor, integrator, step_size::Real, steps::Integer,
        current::AbstractVector{<:Real}, relativistic_mass::Real)
    ε, m = Float64(step_size), Float64(relativistic_mass)
    steps > 0 || throw(ArgumentError("trajectory length must be positive"))
    q0 = Float64.(current)
    factor = Matrix{Float64}(metric_factor(q0))
    size(factor) == (length(q0), length(q0)) ||
        throw(DimensionMismatch("metric factor dimension"))
    radius = _relativistic_radius!(source, length(q0), m)
    direction = [standard_normal!(source) for _ in eachindex(q0)]
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
        Float64.(next_q), Float64.(next_p)
    end
    origin = Int(draw_below!(source, steps + 1))
    trajectory = Vector{Tuple{Vector{Float64},Vector{Float64}}}(undef, steps + 1)
    for index in 0:steps
        q, p = copy(q0), copy(p0)
        signed_step = index >= origin ? ε : -ε
        for _ in 1:abs(index - origin)
            q, p = advance(q, p, signed_step)
        end
        trajectory[index + 1] = (q, p)
    end
    logweights = [-Float64(hamiltonian(q, p)) for (q, p) in trajectory]
    weights = exp.(logweights .- maximum(logweights))
    draw = uniform_unit!(source) * sum(weights)
    cumulative = 0.0
    for (index, weight) in pairs(weights)
        cumulative += weight
        draw < cumulative && return trajectory[index][1]
    end
    trajectory[end][1]
end

"""Independent Float64 implementation of scalar one-step endpoint HMC."""
function scalar_hmc_step!(source::AbstractRandomSource, logdensity, gradient,
        step_size::Float64, steps::Integer, current::Float64)
    isfinite(step_size) && step_size > 0.0 ||
        throw(ArgumentError("step size must be finite and positive"))
    steps > 0 || throw(ArgumentError("leapfrog steps must be positive"))
    momentum = standard_normal!(source)
    next_position, next_momentum = current, momentum
    for _ in 1:steps
        next_position, next_momentum = leapfrog(
            gradient, step_size, next_position, next_momentum)
    end
    current_energy = -logdensity(current) + momentum^2 / 2
    next_energy = -logdensity(next_position) + next_momentum^2 / 2
    log(uniform_unit!(source)) < min(0.0, current_energy - next_energy) ?
        next_position : current
end

"""Tested Float64 Gaussian RWMH step; not an exact realization of Lean `ℝ`."""
function gaussian_rwmh_step!(source::AbstractRandomSource, logdensity,
        scale::Float64, current::Float64)
    isfinite(scale) && scale > 0.0 || throw(ArgumentError("scale must be finite and positive"))
    proposal = current + scale * standard_normal!(source)
    logratio = logdensity(proposal) - logdensity(current)
    log(uniform_unit!(source)) < min(0.0, logratio) ? proposal : current
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
