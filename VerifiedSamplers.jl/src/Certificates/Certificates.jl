module Certificates

export BoundWitness, DecisionCertificate, certify_bound, certify_decision,
    SamplerDecisionCertificate, certify_rwmh_decision, certify_hmc_decision,
    MultinomialSelectionCertificate, certify_multinomial_selection,
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
