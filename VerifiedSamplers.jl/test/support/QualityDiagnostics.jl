module QualityDiagnostics

using LinearAlgebra
using Statistics

export autocorrelation_ess, moment_diagnostics, covariance_max_error,
    marginal_quantile_max_error, batch_mean_standard_error

function retained_samples(chain::AbstractMatrix{<:Real}, burnin::Integer)
    0 <= burnin < size(chain, 2) || throw(ArgumentError(
        "burn-in must leave at least one retained sample"))
    @view chain[:, (burnin + 1):end]
end

"""Simple initial-positive-sequence autocorrelation ESS diagnostic."""
function autocorrelation_ess(values::AbstractVector{<:Real};
        max_lag::Integer=min(500, length(values) ÷ 4))
    isempty(values) && throw(ArgumentError("values cannot be empty"))
    0 <= max_lag < length(values) || throw(ArgumentError(
        "maximum lag must lie between zero and length(values)-1"))
    centered = values .- mean(values)
    variance = sum(abs2, centered) / length(centered)
    variance > 0 || return 0.0
    correlation_sum = 0.0
    for lag in 1:max_lag
        correlation = dot(@view(centered[1:(end - lag)]),
            @view(centered[(lag + 1):end])) /
            ((length(centered) - lag) * variance)
        correlation <= 0 && break
        correlation_sum += correlation
    end
    length(values) / (1 + 2correlation_sum)
end

"""Known-moment errors and minimum coordinate ESS for a sampled chain."""
function moment_diagnostics(chain::AbstractMatrix{<:Real},
        target_mean::AbstractVector{<:Real},
        target_variance::AbstractVector{<:Real}; burnin::Integer=0,
        ess_coordinates::Integer=min(4, size(chain, 1)))
    dimension = size(chain, 1)
    length(target_mean) == dimension || throw(DimensionMismatch("target mean"))
    length(target_variance) == dimension ||
        throw(DimensionMismatch("target variance"))
    all(>(0), target_variance) || throw(ArgumentError(
        "target variances must be positive"))
    1 <= ess_coordinates <= dimension || throw(ArgumentError(
        "ESS coordinate count must lie in 1:dimension"))
    retained = retained_samples(chain, burnin)
    means = vec(mean(retained; dims=2))
    variances = vec(var(retained; dims=2))
    standardized_mean_rmse = sqrt(mean(abs2,
        (means .- target_mean) ./ sqrt.(target_variance)))
    relative_variance_rmse = sqrt(mean(abs2,
        variances ./ target_variance .- 1))
    minimum_ess = minimum(autocorrelation_ess(
        @view retained[index, :]) for index in 1:ess_coordinates)
    (; retained_draws=size(retained, 2), means, variances,
        standardized_mean_rmse, relative_variance_rmse, minimum_ess)
end

"""Maximum absolute entrywise covariance error after burn-in."""
function covariance_max_error(chain::AbstractMatrix{<:Real},
        target_covariance::AbstractMatrix{<:Real}; burnin::Integer=0)
    dimension = size(chain, 1)
    size(target_covariance) == (dimension, dimension) ||
        throw(DimensionMismatch("target covariance"))
    retained = retained_samples(chain, burnin)
    size(retained, 2) > 1 || throw(ArgumentError(
        "covariance requires at least two retained samples"))
    maximum(abs, cov(permutedims(retained)) .- target_covariance)
end

"""Maximum absolute marginal-quantile error after burn-in.

`expected` has one row per chain coordinate and one column per probability.
"""
function marginal_quantile_max_error(chain::AbstractMatrix{<:Real},
        probabilities::AbstractVector{<:Real},
        expected::AbstractMatrix{<:Real}; burnin::Integer=0)
    dimension = size(chain, 1)
    size(expected) == (dimension, length(probabilities)) ||
        throw(DimensionMismatch("expected marginal quantiles"))
    all(p -> 0 <= p <= 1, probabilities) || throw(ArgumentError(
        "quantile probabilities must lie in [0, 1]"))
    retained = retained_samples(chain, burnin)
    observed = [quantile(@view(retained[index, :]), probability)
        for index in 1:dimension, probability in probabilities]
    maximum(abs, observed .- expected)
end

"""Per-coordinate batch-means standard error for the sample mean."""
function batch_mean_standard_error(chain::AbstractMatrix{<:Real};
        burnin::Integer=0, batches::Union{Nothing,Integer}=nothing)
    retained = retained_samples(chain, burnin)
    batch_count = isnothing(batches) ?
        max(2, floor(Int, sqrt(size(retained, 2)))) : batches
    2 <= batch_count <= size(retained, 2) || throw(ArgumentError(
        "batch count must leave at least two nonempty batches"))
    batch_size = size(retained, 2) ÷ batch_count
    batch_size > 0 || throw(ArgumentError("batch size must be positive"))
    batch_means = [mean(@view retained[index,
        ((batch - 1) * batch_size + 1):(batch * batch_size)])
        for index in axes(retained, 1), batch in 1:batch_count]
    vec(std(batch_means; dims=2, corrected=true)) ./ sqrt(batch_count)
end

end
