"""Statistical diagnostics shared by tests and evaluation workloads."""
module Diagnostics

using LinearAlgebra
using Statistics

export autocorrelation_ess, moment_diagnostics, covariance_max_error,
    marginal_quantile_max_error, batch_mean_standard_error,
    split_rank_diagnostics

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

function standard_normal_quantile(probability::Real)
    0 < probability < 1 || throw(ArgumentError(
        "normal-score probability must lie strictly inside (0, 1)"))
    a = (-39.69683028665376, 220.9460984245205, -275.9285104469687,
        138.3577518672690, -30.66479806614716, 2.506628277459239)
    b = (-54.47609879822406, 161.5858368580409, -155.6989798598866,
        66.80131188771972, -13.28068155288572)
    c = (-0.007784894002430293, -0.3223964580411365,
        -2.400758277161838, -2.549732539343734, 4.374664141464968,
        2.938163982698783)
    d = (0.007784695709041462, 0.3224671290700398,
        2.445134137142996, 3.754408661907416)
    lower = 0.02425
    if probability < lower
        q = sqrt(-2log(probability))
        return (((((c[1] * q + c[2]) * q + c[3]) * q + c[4]) * q +
            c[5]) * q + c[6]) / ((((d[1] * q + d[2]) * q + d[3]) * q +
            d[4]) * q + 1)
    elseif probability > 1 - lower
        q = sqrt(-2log1p(-probability))
        return -(((((c[1] * q + c[2]) * q + c[3]) * q + c[4]) * q +
            c[5]) * q + c[6]) / ((((d[1] * q + d[2]) * q + d[3]) * q +
            d[4]) * q + 1)
    end
    q = probability - 0.5
    r = q * q
    (((((a[1] * r + a[2]) * r + a[3]) * r + a[4]) * r + a[5]) * r +
        a[6]) * q / (((((b[1] * r + b[2]) * r + b[3]) * r + b[4]) * r +
        b[5]) * r + 1)
end

function rank_normalize(samples::AbstractMatrix{<:Real})
    all(isfinite, samples) || throw(ArgumentError(
        "rank diagnostics require finite samples"))
    values = vec(Float64.(samples))
    order = sortperm(values)
    ranks = Vector{Float64}(undef, length(values))
    first_index = 1
    while first_index <= length(order)
        last_index = first_index
        value = values[order[first_index]]
        while last_index < length(order) &&
                values[order[last_index + 1]] == value
            last_index += 1
        end
        rank = (first_index + last_index) / 2
        for index in first_index:last_index
            ranks[order[index]] = rank
        end
        first_index = last_index + 1
    end
    probabilities = (ranks .- 3 / 8) ./ (length(ranks) + 1 / 4)
    reshape(standard_normal_quantile.(probabilities), size(samples))
end

function split_chains(samples::AbstractMatrix{<:Real})
    size(samples, 2) >= 2 || throw(ArgumentError(
        "split diagnostics require at least two chains"))
    half = size(samples, 1) ÷ 2
    half >= 4 || throw(ArgumentError(
        "split diagnostics require at least eight draws per chain"))
    hcat(@view(samples[1:half, :]),
        @view(samples[(end - half + 1):end, :]))
end

function basic_rhat(samples::AbstractMatrix{<:Real})
    draws = size(samples, 1)
    within = mean(var(@view(samples[:, chain]); corrected=true)
        for chain in axes(samples, 2))
    between = draws * var(vec(mean(samples; dims=1)); corrected=true)
    within == 0 && return between == 0 ? 1.0 : Inf
    sqrt(((draws - 1) / draws * within + between / draws) / within)
end

function summed_chain_ess(samples::AbstractMatrix{<:Real})
    total = sum(autocorrelation_ess(@view(samples[:, chain]))
        for chain in axes(samples, 2))
    min(Float64(length(samples)), total)
end

"""Non-gating split rank-normalized R-hat and bulk/tail ESS diagnostics.

Rows are draws and columns are independently seeded chains. ESS uses the
shared initial-positive-sequence estimator after splitting and rank
normalization; tail ESS is the smaller indicator ESS at the pooled 5% and 95%
quantiles.
"""
function split_rank_diagnostics(samples::AbstractMatrix{<:Real})
    split = split_chains(samples)
    normalized = rank_normalize(split)
    folded = rank_normalize(abs.(split .- median(vec(split))))
    rank_normalized_rhat = max(basic_rhat(normalized), basic_rhat(folded))
    bulk_ess = summed_chain_ess(normalized)
    lower, upper = quantile(vec(split), (0.05, 0.95))
    lower_indicator = Float64.(split .<= lower)
    upper_indicator = Float64.(split .>= upper)
    tail_ess = min(summed_chain_ess(lower_indicator),
        summed_chain_ess(upper_indicator))
    (; rank_normalized_rhat, bulk_ess, tail_ess,
        split_draws=size(split, 1), split_chains=size(split, 2))
end

end
