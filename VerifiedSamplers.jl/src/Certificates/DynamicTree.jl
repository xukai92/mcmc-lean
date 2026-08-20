"""Bounded sign decision used by a dynamic-tree callback.

Stability means the computed scalar lies strictly outside `[-bound, bound]`.
As with `BoundWitness`, the supplied ideal value and analytic error budget are
premises; construction only checks their observed numerical consistency.
"""
struct SeparatedZeroDecisionCertificate
    witness::BoundWitness
    separation::BigFloat
end

is_stable(certificate::SeparatedZeroDecisionCertificate) =
    certificate.separation > 0
uncertainty_band(certificate::SeparatedZeroDecisionCertificate) =
    certificate.witness.bound

function certify_zero_decision(computed::Real, ideal::Real, bound::Real;
        precision::Integer=256)
    witness = certify_bound(computed, ideal, bound; precision=precision)
    setprecision(BigFloat, precision) do
        separation = abs(BigFloat(witness.computed)) - witness.bound
        SeparatedZeroDecisionCertificate(witness, separation)
    end
end

"""Two-sided comparison certificate with summed operand uncertainty."""
struct SeparatedComparisonCertificate
    left::BoundWitness
    right::BoundWitness
    separation::BigFloat
end

"""Bounded strict slice-eligibility and divergence decisions for one leaf."""
struct NUTSLeafEnergyCertificate
    log_slice::BoundWitness
    energy::BoundWitness
    max_energy_error::BoundWitness
    eligible::SeparatedComparisonCertificate
    continues::SeparatedComparisonCertificate
end


is_stable(certificate::NUTSLeafEnergyCertificate) =
    is_stable(certificate.eligible) && is_stable(certificate.continues)
uncertainty_band(certificate::NUTSLeafEnergyCertificate) = max(
    uncertainty_band(certificate.eligible),
    uncertainty_band(certificate.continues))

function certify_nuts_leaf_energy(; computed_log_slice::Real,
        ideal_log_slice::Real, log_slice_bound::Real,
        computed_energy::Real, ideal_energy::Real, energy_bound::Real,
        computed_max_energy_error::Real, ideal_max_energy_error::Real,
        max_energy_error_bound::Real,
        continuation_rounding_bound::Real=0, precision::Integer=256)
    log_slice = certify_bound(computed_log_slice, ideal_log_slice,
        log_slice_bound; precision=precision)
    energy = certify_bound(computed_energy, ideal_energy, energy_bound;
        precision=precision)
    max_error = certify_bound(computed_max_energy_error, ideal_max_energy_error,
        max_energy_error_bound; precision=precision)
    eligible = certify_comparison(computed_log_slice, ideal_log_slice,
        log_slice_bound, -Float64(computed_energy), -BigFloat(ideal_energy),
        energy_bound; precision=precision)
    computed_continuation_threshold =
        Float64(computed_max_energy_error) - Float64(computed_energy)
    continues = certify_comparison(computed_log_slice, ideal_log_slice,
        log_slice_bound,
        computed_continuation_threshold,
        BigFloat(ideal_max_energy_error) - BigFloat(ideal_energy),
        BigFloat(continuation_rounding_bound) +
            BigFloat(max_energy_error_bound) + BigFloat(energy_bound);
        precision=precision)
    NUTSLeafEnergyCertificate(log_slice, energy, max_error, eligible, continues)
end

"""Return `(eligible, continues)`, or `nothing` if either bit is ambiguous."""
function certified_nuts_leaf_decisions(certificate::NUTSLeafEnergyCertificate)
    is_stable(certificate) || return nothing
    (; eligible=certificate.eligible.left.computed <
            certificate.eligible.right.computed,
        continues=certificate.continues.left.computed <
            certificate.continues.right.computed)
end

is_stable(certificate::SeparatedComparisonCertificate) =
    certificate.separation > 0
uncertainty_band(certificate::SeparatedComparisonCertificate) =
    certificate.left.bound + certificate.right.bound

function certify_comparison(computed_left::Real, ideal_left::Real,
        left_bound::Real, computed_right::Real, ideal_right::Real,
        right_bound::Real; precision::Integer=256)
    left = certify_bound(computed_left, ideal_left, left_bound;
        precision=precision)
    right = certify_bound(computed_right, ideal_right, right_bound;
        precision=precision)
    setprecision(BigFloat, precision) do
        computed_difference = BigFloat(left.computed) - BigFloat(right.computed)
        separation = abs(computed_difference) - (left.bound + right.bound)
        SeparatedComparisonCertificate(left, right, separation)
    end
end

"""Certificate for the two endpoint dot-product signs in a U-turn test."""
struct UTurnDecisionCertificate
    left_momentum::SeparatedZeroDecisionCertificate
    right_momentum::SeparatedZeroDecisionCertificate
end

is_stable(certificate::UTurnDecisionCertificate) =
    is_stable(certificate.left_momentum) &&
    is_stable(certificate.right_momentum)
uncertainty_band(certificate::UTurnDecisionCertificate) = max(
    uncertainty_band(certificate.left_momentum),
    uncertainty_band(certificate.right_momentum))

"""Return the certified computed U-turn bit, or `nothing` when ambiguous."""
function certified_uturn_decision(certificate::UTurnDecisionCertificate)
    is_stable(certificate) || return nothing
    certificate.left_momentum.witness.computed < 0 ||
        certificate.right_momentum.witness.computed < 0
end

function certify_uturn_decision(computed_left::Real, ideal_left::Real,
        left_bound::Real, computed_right::Real, ideal_right::Real,
        right_bound::Real; precision::Integer=256)
    UTurnDecisionCertificate(
        certify_zero_decision(computed_left, ideal_left, left_bound;
            precision=precision),
        certify_zero_decision(computed_right, ideal_right, right_bound;
            precision=precision))
end

"""Componentwise endpoint witnesses and their composed U-turn decision."""
struct VectorUTurnDecisionCertificate
    left_positions::Vector{BoundWitness}
    right_positions::Vector{BoundWitness}
    left_momenta::Vector{BoundWitness}
    right_momenta::Vector{BoundWitness}
    decision::UTurnDecisionCertificate
end

is_stable(certificate::VectorUTurnDecisionCertificate) =
    is_stable(certificate.decision)
uncertainty_band(certificate::VectorUTurnDecisionCertificate) =
    uncertainty_band(certificate.decision)
certified_uturn_decision(certificate::VectorUTurnDecisionCertificate) =
    certified_uturn_decision(certificate.decision)

"""Compose componentwise phase bounds into both endpoint-dot certificates.

`*_rounding_bound` covers the final Float64 subtraction, multiplication, and
reduction relative to exact real arithmetic on the stored Float64 components.
The componentwise bounds and supplied ideal vectors remain proof inputs.
"""
function certify_vector_uturn_decision(
        computed_left_position::AbstractVector{<:Real},
        ideal_left_position::AbstractVector{<:Real},
        left_position_bound::AbstractVector{<:Real},
        computed_right_position::AbstractVector{<:Real},
        ideal_right_position::AbstractVector{<:Real},
        right_position_bound::AbstractVector{<:Real},
        computed_left_momentum::AbstractVector{<:Real},
        ideal_left_momentum::AbstractVector{<:Real},
        left_momentum_bound::AbstractVector{<:Real},
        computed_right_momentum::AbstractVector{<:Real},
        ideal_right_momentum::AbstractVector{<:Real},
        right_momentum_bound::AbstractVector{<:Real};
        left_rounding_bound::Real=0,
        right_rounding_bound::Real=0,
        precision::Integer=256)
    dimension = length(computed_left_position)
    all(length(values) == dimension for values in (
        ideal_left_position, left_position_bound,
        computed_right_position, ideal_right_position, right_position_bound,
        computed_left_momentum, ideal_left_momentum, left_momentum_bound,
        computed_right_momentum, ideal_right_momentum, right_momentum_bound)) ||
        throw(DimensionMismatch("phase endpoint vectors and bounds must match"))
    dimension > 0 || throw(ArgumentError("phase endpoint dimension must be positive"))

    left_positions = [certify_bound(computed_left_position[i],
        ideal_left_position[i], left_position_bound[i]; precision=precision)
        for i in 1:dimension]
    right_positions = [certify_bound(computed_right_position[i],
        ideal_right_position[i], right_position_bound[i]; precision=precision)
        for i in 1:dimension]
    left_momenta = [certify_bound(computed_left_momentum[i],
        ideal_left_momentum[i], left_momentum_bound[i]; precision=precision)
        for i in 1:dimension]
    right_momenta = [certify_bound(computed_right_momentum[i],
        ideal_right_momentum[i], right_momentum_bound[i]; precision=precision)
        for i in 1:dimension]

    decision = setprecision(BigFloat, precision) do
        ideal_displacement = BigFloat.(ideal_right_position) .-
            BigFloat.(ideal_left_position)
        ideal_left_dot = sum(ideal_displacement .* BigFloat.(ideal_left_momentum))
        ideal_right_dot = sum(ideal_displacement .* BigFloat.(ideal_right_momentum))
        computed_displacement = Float64.(computed_right_position) .-
            Float64.(computed_left_position)
        computed_left = sum(computed_displacement .* Float64.(computed_left_momentum))
        computed_right = sum(computed_displacement .* Float64.(computed_right_momentum))
        position_error = BigFloat.(right_position_bound) .+
            BigFloat.(left_position_bound)
        left_error = BigFloat(left_rounding_bound) + sum(
            position_error .* abs.(BigFloat.(computed_left_momentum)) .+
            abs.(ideal_displacement) .* BigFloat.(left_momentum_bound))
        right_error = BigFloat(right_rounding_bound) + sum(
            position_error .* abs.(BigFloat.(computed_right_momentum)) .+
            abs.(ideal_displacement) .* BigFloat.(right_momentum_bound))
        certify_uturn_decision(computed_left, ideal_left_dot, left_error,
            computed_right, ideal_right_dot, right_error; precision=precision)
    end
    VectorUTurnDecisionCertificate(left_positions, right_positions,
        left_momenta, right_momenta, decision)
end

"""Certificates for every adjacent endpoint test on one phase trajectory."""
struct VectorUTurnTrajectoryCertificate
    edges::Vector{VectorUTurnDecisionCertificate}
end

is_stable(certificate::VectorUTurnTrajectoryCertificate) =
    all(is_stable, certificate.edges)
uncertainty_band(certificate::VectorUTurnTrajectoryCertificate) =
    maximum(uncertainty_band, certificate.edges; init=big"0")

function certified_uturn_decisions(certificate::VectorUTurnTrajectoryCertificate)
    is_stable(certificate) || return nothing
    Bool[certified_uturn_decision(edge)::Bool for edge in certificate.edges]
end

function certify_vector_uturn_trajectory(
        computed_positions::AbstractVector{<:AbstractVector{<:Real}},
        ideal_positions::AbstractVector{<:AbstractVector{<:Real}},
        position_bounds::AbstractVector{<:AbstractVector{<:Real}},
        computed_momenta::AbstractVector{<:AbstractVector{<:Real}},
        ideal_momenta::AbstractVector{<:AbstractVector{<:Real}},
        momentum_bounds::AbstractVector{<:AbstractVector{<:Real}};
        left_rounding_bounds::AbstractVector{<:Real}=
            zeros(max(length(computed_positions) - 1, 0)),
        right_rounding_bounds::AbstractVector{<:Real}=
            zeros(max(length(computed_positions) - 1, 0)),
        precision::Integer=256)
    count = length(computed_positions)
    count > 0 || throw(ArgumentError("phase trajectory cannot be empty"))
    all(length(values) == count for values in (ideal_positions,
        position_bounds, computed_momenta, ideal_momenta, momentum_bounds)) ||
        throw(DimensionMismatch("phase trajectories and bound arrays must match"))
    length(left_rounding_bounds) == count - 1 &&
        length(right_rounding_bounds) == count - 1 ||
        throw(DimensionMismatch("one pair of rounding bounds is required per edge"))
    edges = Vector{VectorUTurnDecisionCertificate}(undef, count - 1)
    for edge in eachindex(edges)
        edges[edge] = certify_vector_uturn_decision(
            computed_positions[edge], ideal_positions[edge], position_bounds[edge],
            computed_positions[edge + 1], ideal_positions[edge + 1],
            position_bounds[edge + 1],
            computed_momenta[edge], ideal_momenta[edge], momentum_bounds[edge],
            computed_momenta[edge + 1], ideal_momenta[edge + 1],
            momentum_bounds[edge + 1];
            left_rounding_bound=left_rounding_bounds[edge],
            right_rounding_bound=right_rounding_bounds[edge],
            precision=precision)
    end
    VectorUTurnTrajectoryCertificate(edges)
end

"""All distinct endpoint U-turn certificates for one linked trajectory.

The diagonal is intentionally omitted: a self-displacement has dot product
zero and cannot satisfy strict separation. Lean's recursive-row refinement
handles those pairs structurally and consumes exactly the off-diagonal
certificates represented here.
"""
struct RecursiveDoublingUTurnCertificate
    count::Int
    pairs::Dict{Tuple{Int,Int},VectorUTurnDecisionCertificate}
end

is_stable(certificate::RecursiveDoublingUTurnCertificate) =
    length(certificate.pairs) == certificate.count * (certificate.count - 1) &&
    all(is_stable, values(certificate.pairs))
uncertainty_band(certificate::RecursiveDoublingUTurnCertificate) =
    maximum(uncertainty_band, values(certificate.pairs); init=big"0")

function certified_uturn_decisions(
        certificate::RecursiveDoublingUTurnCertificate)
    is_stable(certificate) || return nothing
    Dict(pair => certified_uturn_decision(decision)::Bool
        for (pair, decision) in certificate.pairs)
end

"""Compose a linked leapfrog trajectory into every recursive U-turn margin.

Primitive step records determine all later computed/ideal endpoints and their
proved recurrence budgets. The caller supplies only the initial endpoint
budgets and optional final dot-reduction bounds. This is the executable adapter
for Lean's `recursiveDoublingKernel_eq_ideal` theorem; supplied ideal values and
primitive operation bounds remain the explicit trust boundary.
"""
function certify_recursive_doubling_uturn_matrix(
        trajectory::LinkedLeapfrogVectorTrajectoryCertificate;
        initial_position_error::Real=0,
        initial_momentum_error::Real=0,
        left_rounding_bound::Real=0,
        right_rounding_bound::Real=0,
        precision::Integer=256)
    position_error = BigFloat(initial_position_error)
    momentum_error = BigFloat(initial_momentum_error)
    position_error >= 0 && momentum_error >= 0 || throw(ArgumentError(
        "initial trajectory errors must be nonnegative"))
    left_rounding_bound >= 0 && right_rounding_bound >= 0 ||
        throw(ArgumentError("dot-product rounding bounds must be nonnegative"))

    computed_positions = Vector{Vector{Float64}}()
    ideal_positions = Vector{Vector{BigFloat}}()
    position_bounds = Vector{Vector{BigFloat}}()
    computed_momenta = Vector{Vector{Float64}}()
    ideal_momenta = Vector{Vector{BigFloat}}()
    momentum_bounds = Vector{Vector{BigFloat}}()
    dimension = length(trajectory.initial_computed_position)

    function push_endpoint!(computed_position, ideal_position, ep,
            computed_momentum, ideal_momentum, em)
        for coordinate in eachindex(computed_position)
            certify_bound(computed_position[coordinate], ideal_position[coordinate],
                ep; precision=precision)
            certify_bound(computed_momentum[coordinate], ideal_momentum[coordinate],
                em; precision=precision)
        end
        push!(computed_positions, Float64.(computed_position))
        push!(ideal_positions, BigFloat.(ideal_position))
        push!(position_bounds, fill(BigFloat(ep), dimension))
        push!(computed_momenta, Float64.(computed_momentum))
        push!(ideal_momenta, BigFloat.(ideal_momentum))
        push!(momentum_bounds, fill(BigFloat(em), dimension))
    end

    push_endpoint!(trajectory.initial_computed_position,
        trajectory.initial_ideal_position, position_error,
        trajectory.initial_computed_momentum,
        trajectory.initial_ideal_momentum, momentum_error)
    for step in trajectory.steps
        computed_position = [coordinate.drift_rounding.computed
            for coordinate in step.coordinates]
        ideal_position = [_ideal_next_position(coordinate)
            for coordinate in step.coordinates]
        computed_momentum = [coordinate.final_kick_rounding.computed
            for coordinate in step.coordinates]
        ideal_momentum = [_ideal_next_momentum(coordinate)
            for coordinate in step.coordinates]
        push_endpoint!(computed_position, ideal_position,
            step.next_position_error, computed_momentum, ideal_momentum,
            step.next_momentum_error)
    end

    count = length(computed_positions)
    pairs = Dict{Tuple{Int,Int},VectorUTurnDecisionCertificate}()
    for left in 1:count, right in 1:count
        left == right && continue
        pairs[(left, right)] = certify_vector_uturn_decision(
            computed_positions[left], ideal_positions[left], position_bounds[left],
            computed_positions[right], ideal_positions[right], position_bounds[right],
            computed_momenta[left], ideal_momenta[left], momentum_bounds[left],
            computed_momenta[right], ideal_momenta[right], momentum_bounds[right];
            left_rounding_bound=left_rounding_bound,
            right_rounding_bound=right_rounding_bound,
            precision=precision)
    end
    RecursiveDoublingUTurnCertificate(count, pairs)
end

"""All primitive comparison certificates visited by one completed tree.

The recursive topology and ordering are supplied by the caller. Stability
means every recorded leaf and internal U-turn decision clears its uncertainty
band, matching Lean's tree-local `DecisionsAgree` interface.
"""
struct CompletedTreeDecisionCertificate
    leaf_comparisons::Vector{SeparatedComparisonCertificate}
    uturn_decisions::Vector{UTurnDecisionCertificate}
end

"""Leaf and join certificates for one complete recursive NUTS tree."""
struct NUTSCompletedTreeCertificate
    leaves::Vector{NUTSLeafEnergyCertificate}
    joins::Vector{UTurnDecisionCertificate}
end

is_stable(certificate::NUTSCompletedTreeCertificate) =
    all(is_stable, certificate.leaves) && all(is_stable, certificate.joins)
uncertainty_band(certificate::NUTSCompletedTreeCertificate) = max(
    maximum(uncertainty_band, certificate.leaves; init=big"0"),
    maximum(uncertainty_band, certificate.joins; init=big"0"))

"""Expose all certified tree bits, or fail closed if any margin is ambiguous."""
function certified_nuts_completed_tree(certificate::NUTSCompletedTreeCertificate)
    is_stable(certificate) || return nothing
    leaf = [certified_nuts_leaf_decisions(item) for item in certificate.leaves]
    (; eligible=Bool[item.eligible for item in leaf],
        continues=Bool[item.continues for item in leaf],
        turns=Bool[certified_uturn_decision(item)::Bool for item in certificate.joins])
end

is_stable(certificate::CompletedTreeDecisionCertificate) =
    all(is_stable, certificate.leaf_comparisons) &&
    all(is_stable, certificate.uturn_decisions)
uncertainty_band(certificate::CompletedTreeDecisionCertificate) = max(
    maximum(uncertainty_band, certificate.leaf_comparisons; init=big"0"),
    maximum(uncertainty_band, certificate.uturn_decisions; init=big"0"))
