"""Explicit suspend/resume state for a finite sequence of observation factors.

This mirrors Lean's `ProbabilisticProgram.CoroutineState`. It is ordinary
copyable data rather than a copied Julia `Task`, so cloning a cursor cannot
duplicate hidden stack or scheduler state.
"""
struct ObservationCursor{S,F}
    state::S
    accumulated_weight::Float64
    factors::Vector{F}
    position::Int
end

function observation_cursor(state, factors::AbstractVector{F}) where {F}
    ObservationCursor(state, 1.0, collect(factors), 1)
end

"""Consume at most one factor, returning `nothing` after completion."""
function resume_observation(cursor::ObservationCursor)
    cursor.position <= length(cursor.factors) || return nothing
    factor = cursor.factors[cursor.position]
    value = Float64(factor(cursor.state))
    value >= 0.0 || throw(DomainError(value, "observation weight must be nonnegative"))
    isfinite(value) || throw(DomainError(value, "observation weight must be finite"))
    weight = cursor.accumulated_weight * value
    isfinite(weight) || throw(DomainError(weight,
        "accumulated observation weight overflowed"))
    ObservationCursor(cursor.state, weight, cursor.factors, cursor.position + 1)
end

"""Consume up to `fuel` factors and return the resulting explicit cursor."""
function run_observations(cursor::ObservationCursor, fuel::Integer)
    fuel >= 0 || throw(ArgumentError("observation fuel must be nonnegative"))
    current = cursor
    for _ in 1:fuel
        next = resume_observation(current)
        isnothing(next) && break
        current = next
    end
    current
end
