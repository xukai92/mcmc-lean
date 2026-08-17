module Certificates

export BoundWitness, DecisionCertificate, certify_bound, certify_decision,
    SamplerDecisionCertificate, certify_rwmh_decision, certify_hmc_decision,
    MultinomialSelectionCertificate, certify_multinomial_selection,
    SliceComparisonCertificate, certify_slice_comparisons,
    ImplicitSolveCertificate, certify_implicit_solve, certifies_exact_solver,
    ContractionErrorBound, contraction_error_bound,
    SeparatedZeroDecisionCertificate, certify_zero_decision,
    SeparatedComparisonCertificate, certify_comparison,
    UTurnDecisionCertificate, certify_uturn_decision,
    VectorUTurnDecisionCertificate, certify_vector_uturn_decision,
    certified_uturn_decision,
    VectorUTurnTrajectoryCertificate, certify_vector_uturn_trajectory,
    certified_uturn_decisions,
    CompletedTreeDecisionCertificate,
    is_stable, uncertainty_band

"""A checked, execution-specific absolute-error claim.

`ideal` and `bound` are supplied by a trusted oracle or analytic argument.
Construction checks the observed Float64 value against that claim using
BigFloat arithmetic. This object does not establish that the supplied ideal
value is the mathematical real result.
"""
struct BoundWitness
    computed::Float64
    ideal::BigFloat
    bound::BigFloat
    observed_error::BigFloat
end

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

"""All primitive comparison certificates visited by one completed tree.

The recursive topology and ordering are supplied by the caller. Stability
means every recorded leaf and internal U-turn decision clears its uncertainty
band, matching Lean's tree-local `DecisionsAgree` interface.
"""
struct CompletedTreeDecisionCertificate
    leaf_comparisons::Vector{SeparatedComparisonCertificate}
    uturn_decisions::Vector{UTurnDecisionCertificate}
end

is_stable(certificate::CompletedTreeDecisionCertificate) =
    all(is_stable, certificate.leaf_comparisons) &&
    all(is_stable, certificate.uturn_decisions)
uncertainty_band(certificate::CompletedTreeDecisionCertificate) = max(
    maximum(uncertainty_band, certificate.leaf_comparisons; init=big"0"),
    maximum(uncertainty_band, certificate.uturn_decisions; init=big"0"))

"""Checked comparison margins for one finite stepping-out/shrinkage trace.

The supplied ideals and bounds remain proof inputs. When `is_stable` holds,
Lean's `SliceComparisonCertificate.decisionTrace_eq` theorem proves that every
endpoint-stop and proposal-accept comparison agrees with ideal-real execution.
"""
struct SliceComparisonCertificate
    threshold::BoundWitness
    values::Vector{BoundWitness}
    minimum_margin::BigFloat
    maximum_uncertainty::BigFloat
end

is_stable(certificate::SliceComparisonCertificate) =
    certificate.maximum_uncertainty < certificate.minimum_margin
uncertainty_band(certificate::SliceComparisonCertificate) =
    certificate.maximum_uncertainty

function certify_slice_comparisons(computed_threshold::Real,
        ideal_threshold::Real, threshold_bound::Real,
        computed_values::AbstractVector{<:Real},
        ideal_values::AbstractVector{<:Real},
        value_bounds::AbstractVector{<:Real}; precision::Integer=256)
    length(computed_values) == length(ideal_values) == length(value_bounds) ||
        throw(DimensionMismatch("value and bound vectors must have equal length"))
    isempty(computed_values) &&
        throw(ArgumentError("a slice trace must contain at least one comparison"))
    threshold = certify_bound(computed_threshold, ideal_threshold,
        threshold_bound; precision=precision)
    values = [certify_bound(computed_values[index], ideal_values[index],
        value_bounds[index]; precision=precision) for index in eachindex(computed_values)]
    setprecision(BigFloat, precision) do
        minimum_margin = minimum(abs(witness.ideal - threshold.ideal)
            for witness in values)
        maximum_uncertainty = maximum(witness.bound + threshold.bound
            for witness in values)
        SliceComparisonCertificate(threshold, values, minimum_margin,
            maximum_uncertainty)
    end
end

"""Checked residual information for one implicit generalized-leapfrog solve.

This certificate deliberately separates a numerical residual bound from the
global reversibility and volume-preservation obligations. Only a zero bound,
zero observed residual, and explicit global witnesses qualify as an exact
solver certificate; a small positive tolerance is merely approximation data.
"""
struct ImplicitSolveCertificate
    half_momentum_residual::BoundWitness
    position_residual::BoundWitness
    unique::Bool
    reversible::Bool
    volume_preserving::Bool
end

function certify_implicit_solve(half_momentum_residual::Real,
        half_momentum_bound::Real, position_residual::Real,
        position_bound::Real; unique::Bool=false, reversible::Bool=false,
        volume_preserving::Bool=false, precision::Integer=256)
    half = certify_bound(half_momentum_residual, 0, half_momentum_bound;
        precision=precision)
    position = certify_bound(position_residual, 0, position_bound;
        precision=precision)
    ImplicitSolveCertificate(half, position, unique, reversible,
        volume_preserving)
end


certifies_exact_solver(certificate::ImplicitSolveCertificate) =
    iszero(certificate.half_momentum_residual.bound) &&
    iszero(certificate.position_residual.bound) &&
    iszero(certificate.half_momentum_residual.observed_error) &&
    iszero(certificate.position_residual.observed_error) &&
    certificate.unique && certificate.reversible && certificate.volume_preserving

"""A posteriori distance bound from a computed fixed-point residual.

Lean proves `distance_to_exact ≤ (abs(residual) + residual_error)/(1-rate)`
for a genuine contraction. This runtime record evaluates that bound after
checking its scalar premises; it does not itself prove that the callback has
the supplied contraction rate or residual error.
"""
struct ContractionErrorBound
    computed_residual::Float64
    residual_error::BigFloat
    rate::BigFloat
    distance_bound::BigFloat
end

function contraction_error_bound(computed_residual::Real,
        residual_error::Real, rate::Real; precision::Integer=256)
    isfinite(computed_residual) || throw(DomainError(computed_residual,
        "computed residual must be finite"))
    setprecision(BigFloat, precision) do
        error = BigFloat(residual_error)
        contraction_rate = BigFloat(rate)
        error >= 0 || throw(DomainError(residual_error,
            "residual error must be nonnegative"))
        0 <= contraction_rate < 1 || throw(DomainError(rate,
            "contraction rate must lie in [0, 1)"))
        residual = Float64(computed_residual)
        bound = (abs(BigFloat(residual)) + error) / (1 - contraction_rate)
        ContractionErrorBound(residual, error, contraction_rate, bound)
    end
end

"""Execution-specific cumulative-boundary certificate for multinomial selection."""
struct MultinomialSelectionCertificate
    boundaries::Vector{BoundWitness}
    uniform::BoundWitness
    minimum_margin::BigFloat
    uncertainty::BigFloat
end

is_stable(certificate::MultinomialSelectionCertificate) =
    certificate.uncertainty < certificate.minimum_margin
uncertainty_band(certificate::MultinomialSelectionCertificate) =
    certificate.uncertainty

"""Check cumulative-weight bounds and the distance to every selection boundary.

Conditional on the supplied ideal values and common boundary bound, stability
implies the Float64 and ideal categorical scans select the same index.
"""
function certify_multinomial_selection(computed_boundaries::AbstractVector{<:Real},
        ideal_boundaries::AbstractVector{<:Real}, boundary_bound::Real,
        computed_uniform::Real, ideal_uniform::Real, uniform_bound::Real;
        precision::Integer=256)
    length(computed_boundaries) == length(ideal_boundaries) ||
        throw(DimensionMismatch("boundary vectors must have equal length"))
    isempty(computed_boundaries) && throw(ArgumentError("boundaries cannot be empty"))
    boundaries = [certify_bound(computed_boundaries[i], ideal_boundaries[i],
        boundary_bound; precision=precision) for i in eachindex(computed_boundaries)]
    uniform = certify_bound(computed_uniform, ideal_uniform, uniform_bound;
        precision=precision)
    minimum_margin = minimum(abs(uniform.ideal - boundary.ideal)
        for boundary in boundaries)
    MultinomialSelectionCertificate(boundaries, uniform, minimum_margin,
        uniform.bound + BigFloat(boundary_bound))
end

function certify_bound(computed::Real, ideal::Real, bound::Real;
        precision::Integer=256)
    precision >= 64 || throw(ArgumentError("precision must be at least 64 bits"))
    converted = Float64(computed)
    isfinite(converted) || throw(ArgumentError("computed value must be finite"))
    setprecision(BigFloat, precision) do
        reference = BigFloat(ideal)
        budget = BigFloat(bound)
        isfinite(reference) || throw(ArgumentError("ideal value must be finite"))
        isfinite(budget) && budget >= 0 ||
            throw(ArgumentError("error bound must be finite and nonnegative"))
        observed = abs(BigFloat(converted) - reference)
        observed <= budget || throw(ArgumentError(
            "observed error $observed exceeds supplied bound $budget"))
        BoundWitness(converted, reference, budget, observed)
    end
end

"""Checked decision-margin certificate matching Lean's stability condition."""
struct DecisionCertificate
    uniform::BoundWitness
    threshold::BoundWitness
    ideal_margin::BigFloat
end

uncertainty_band(certificate::DecisionCertificate) =
    certificate.uniform.bound + certificate.threshold.bound

is_stable(certificate::DecisionCertificate) =
    uncertainty_band(certificate) < certificate.ideal_margin

"""Check uniform and threshold bounds and compute the certified branch margin.

When `is_stable(result)` holds, Lean's `comparison_eq_of_approximates` theorem
shows that the Float64 and ideal comparisons select the same branch, provided
the supplied per-operation bounds are valid.
"""
function certify_decision(computed_uniform::Real, ideal_uniform::Real,
        uniform_bound::Real, computed_threshold::Real, ideal_threshold::Real,
        threshold_bound::Real; precision::Integer=256)
    uniform = certify_bound(computed_uniform, ideal_uniform, uniform_bound;
        precision=precision)
    threshold = certify_bound(computed_threshold, ideal_threshold,
        threshold_bound; precision=precision)
    margin = setprecision(BigFloat, precision) do
        abs(BigFloat(ideal_uniform) - BigFloat(ideal_threshold))
    end
    DecisionCertificate(uniform, threshold, margin)
end

"""A sampler decision certificate plus its checked component witnesses."""
struct SamplerDecisionCertificate{C}
    algorithm::Symbol
    components::C
    decision::DecisionCertificate
end

is_stable(certificate::SamplerDecisionCertificate) = is_stable(certificate.decision)
uncertainty_band(certificate::SamplerDecisionCertificate) =
    uncertainty_band(certificate.decision)

"""Compose callback, libm, and RNG bounds for one RWMH decision.

The threshold budget is `exp_bound + proposed_logdensity_bound +
current_logdensity_bound`, exactly as in Lean's
`BackendRwmhCertificate.toErrorCertificate`.
"""
function certify_rwmh_decision(;
        computed_current_logdensity::Real, ideal_current_logdensity::Real,
        current_logdensity_bound::Real,
        computed_proposal_logdensity::Real, ideal_proposal_logdensity::Real,
        proposal_logdensity_bound::Real,
        computed_threshold::Real, ideal_threshold::Real, exp_bound::Real,
        computed_uniform::Real, ideal_uniform::Real, uniform_bound::Real,
        precision::Integer=256)
    current_logdensity = certify_bound(computed_current_logdensity,
        ideal_current_logdensity, current_logdensity_bound; precision=precision)
    proposal_logdensity = certify_bound(computed_proposal_logdensity,
        ideal_proposal_logdensity, proposal_logdensity_bound; precision=precision)
    exp_budget = BigFloat(exp_bound)
    isfinite(exp_budget) && exp_budget >= 0 ||
        throw(ArgumentError("exp bound must be finite and nonnegative"))
    threshold_budget = exp_budget + current_logdensity.bound +
        proposal_logdensity.bound
    decision = certify_decision(computed_uniform, ideal_uniform, uniform_bound,
        computed_threshold, ideal_threshold, threshold_budget; precision=precision)
    SamplerDecisionCertificate(:rwmh,
        (; current_logdensity, proposal_logdensity, exp_bound=exp_budget),
        decision)
end

"""Compose endpoint-energy, libm, and RNG bounds for one HMC decision.

The threshold budget is `exp_bound + current_energy_bound +
proposal_energy_bound`, matching Lean's
`BackendHmcCertificate.toErrorCertificate`.
"""
function certify_hmc_decision(;
        computed_current_energy::Real, ideal_current_energy::Real,
        current_energy_bound::Real,
        computed_proposal_energy::Real, ideal_proposal_energy::Real,
        proposal_energy_bound::Real,
        computed_threshold::Real, ideal_threshold::Real, exp_bound::Real,
        computed_uniform::Real, ideal_uniform::Real, uniform_bound::Real,
        precision::Integer=256)
    current_energy = certify_bound(computed_current_energy,
        ideal_current_energy, current_energy_bound; precision=precision)
    proposal_energy = certify_bound(computed_proposal_energy,
        ideal_proposal_energy, proposal_energy_bound; precision=precision)
    exp_budget = BigFloat(exp_bound)
    isfinite(exp_budget) && exp_budget >= 0 ||
        throw(ArgumentError("exp bound must be finite and nonnegative"))
    threshold_budget = exp_budget + current_energy.bound +
        proposal_energy.bound
    decision = certify_decision(computed_uniform, ideal_uniform, uniform_bound,
        computed_threshold, ideal_threshold, threshold_budget; precision=precision)
    SamplerDecisionCertificate(:hmc,
        (; current_energy, proposal_energy, exp_bound=exp_budget), decision)
end

end
