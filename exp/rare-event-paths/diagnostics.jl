"""
Diagnostics for rare-event path sampling pilot.

- Channel probability estimation with batch-means standard error
- Channel-switching count
- Effective sample size (ESS) for path observables
- Acceptance rate tracking
"""

using Statistics

"""
Determine which channel a path uses at the first crossing of q = 0.
Returns +1 for upper channel (r > 0), -1 for lower channel (r < 0),
and 0 for exact crossing at r = 0.
"""
function channel_indicator(path::AbstractMatrix{T}) where {T<:AbstractFloat}
    Lp1 = size(path, 2)
    for t in 1:Lp1
        q = path[1, t]
        if q >= zero(T)
            r = path[2, t]
            if r > zero(T)
                return 1
            elseif r < zero(T)
                return -1
            else
                return 0
            end
        end
    end
    return 0
end

"""
Estimate P(upper channel) = P(r_τ > 0 | event) from a collection of paths,
with batch-means standard error.
"""
function estimate_channel_probability(
    paths::Vector{Matrix{T}}; n_batches::Int = 10
) where {T<:AbstractFloat}
    n = length(paths)
    if n == 0
        return zero(T), zero(T)
    end

    indicators = T[channel_indicator(p) > 0 ? one(T) : zero(T) for p in paths]
    overall_mean = mean(indicators)

    if n < n_batches
        se = std(indicators) / sqrt(T(n))
        return overall_mean, se
    end

    batch_size = n ÷ n_batches
    batch_means = T[]
    for b in 1:n_batches
        start_idx = (b - 1) * batch_size + 1
        end_idx = b == n_batches ? n : b * batch_size
        push!(batch_means, mean(@view indicators[start_idx:end_idx]))
    end

    se = std(batch_means) / sqrt(T(n_batches))
    return overall_mean, se
end

"""
Count the number of channel switches in the path sequence.
"""
function count_channel_switches(paths::Vector{Matrix{T}}) where {T<:AbstractFloat}
    if length(paths) < 2
        return 0
    end
    channels = [channel_indicator(p) for p in paths]
    switches = 0
    for i in 2:length(channels)
        if channels[i] != channels[i-1] && channels[i] != 0 && channels[i-1] != 0
            switches += 1
        end
    end
    return switches
end

"""
Effective sample size based on first-order autocorrelation of a scalar observable.
"""
function ess_from_observable(values::AbstractVector{T}) where {T<:AbstractFloat}
    n = length(values)
    if n < 3
        return T(n)
    end

    m = mean(values)
    v = var(values; corrected=false)
    if v ≤ zero(T)
        return one(T)
    end

    centered = values .- m
    rho1 = zero(T)
    @inbounds for i in 1:(n-1)
        rho1 += centered[i] * centered[i+1]
    end
    rho1 /= (T(n - 1) * v)

    tau = max(one(T), one(T) + 2 * rho1)
    return T(n) / tau
end

"""
Compute ESS for the channel indicator observable.
"""
function channel_ess(paths::Vector{Matrix{T}}) where {T<:AbstractFloat}
    indicators = T[T(channel_indicator(p)) for p in paths]
    return ess_from_observable(indicators)
end

struct PilotDiagnostics{T<:AbstractFloat}
    method_name::String
    n_paths::Int
    channel_prob_upper::T
    channel_prob_se::T
    n_switches::Int
    ess::T
    acceptance_rate::T
    force_evals::Int
end

function summarize_diagnostics(
    method_name::String, paths::Vector{Matrix{T}};
    acceptance_rate::T = T(NaN),
    force_evals::Int = 0,
    n_batches::Int = 10
) where {T<:AbstractFloat}
    cp, se = estimate_channel_probability(paths; n_batches)
    switches = count_channel_switches(paths)
    ess_val = channel_ess(paths)

    return PilotDiagnostics{T}(
        method_name,
        length(paths),
        cp,
        se,
        switches,
        ess_val,
        acceptance_rate,
        force_evals,
    )
end

function print_diagnostics(diag::PilotDiagnostics{T}) where {T<:AbstractFloat}
    println("  Method: $(diag.method_name)")
    println("  Paths collected: $(diag.n_paths)")
    Printf.@printf("  P(upper channel): %.4f ± %.4f\n",
                    diag.channel_prob_upper, diag.channel_prob_se)
    println("  Channel switches: $(diag.n_switches)")
    Printf.@printf("  Channel ESS: %.1f\n", diag.ess)
    if !isnan(diag.acceptance_rate)
        Printf.@printf("  Acceptance rate: %.4f\n", diag.acceptance_rate)
    end
    if diag.force_evals > 0
        println("  Force evaluations: $(diag.force_evals)")
    end
end
