module Optimized

using ...Runtime: AbstractRandomSource, draw_below!

export categorical_index!, two_state_mh_step!

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
    0 <= current < 2 || throw(ArgumentError("state must be 0 or 1"))
    proposed = categorical_index!(source, BigInt[1, 1])
    proposed == current && return current
    acceptance_bound = current == 0 ? 2 : 6
    draw_below!(source, acceptance_bound) < 2 ? proposed : current
end

end
