module Optimized

using ...Runtime: AbstractRandomSource, draw_below!, standard_normal!, uniform_unit!

export categorical_index!, finite_mh_step!, two_state_mh_step!, gaussian_rwmh_step!,
    scalar_hmc_step!, leapfrog

"""One scalar velocity-Verlet/leapfrog step with unit mass."""
function leapfrog(gradient, step_size::Float64, position::Float64, momentum::Float64)
    half_momentum = momentum - step_size * gradient(position) / 2
    next_position = position + step_size * half_momentum
    next_momentum = half_momentum - step_size * gradient(next_position) / 2
    next_position, next_momentum
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
