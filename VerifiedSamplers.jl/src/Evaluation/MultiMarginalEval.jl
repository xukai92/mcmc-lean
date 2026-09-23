"""Evaluation utilities for multi-marginal transport HMC.

Compare K coupled chains (shared momentum) vs K independent chains on
a test target. Reports variance reduction, pairwise chain correlation,
ESS per gradient evaluation, and meeting-time tails (K=2).
"""
module MultiMarginalEval

using Random
using Statistics
using LinearAlgebra

using ...Runtime: RNGSource, standard_normal!, draw_below!, uniform_unit!
using ...Reference: multi_marginal_transport_hmc_step!, multinomial_hmc_step!

struct MultiMarginalDiagnostic
    seed::UInt64
    step_size::Float64
    L::Int
    K::Int
    dim::Int
    N::Int
    coupled_samples::Matrix{Float64}
    independent_samples::Matrix{Float64}
    coupled_variance::Vector{Float64}
    independent_variance::Vector{Float64}
    variance_reduction::Vector{Float64}
    pairwise_correlation::Matrix{Float64}
    coupled_ess_per_grad::Float64
    independent_ess_per_grad::Float64
    meeting_times::Union{Nothing, Vector{Union{Nothing, Int}}}
end

function _autocorrelation_ess(chain::AbstractVector{<:Real})
    n = length(chain)
    n < 4 && return Float64(n)
    centered = chain .- mean(chain)
    v = var(chain; corrected=false)
    v < 1e-30 && return Float64(n)
    tau = 1.0
    for lag in 1:(n - 1)
        rho = dot(@view(centered[1:n-lag]), @view(centered[lag+1:n])) / (n * v)
        rho < 0.05 && break
        tau += 2rho
    end
    n / tau
end

"""Evaluate multi-marginal transport HMC on a test target.

`gradient` is the potential gradient ∇U where U = -logdensity (the sampler
convention used throughout this project). For a standard Gaussian with
U(x) = ||x||²/2, pass `gradient = x -> x`, not `x -> -x`.
"""
function evaluate(;
        logdensity, potential_gradient, dim::Int, step_size::Real, L::Int, K::Int,
        N::Int, seed::UInt64=UInt64(42), meeting_trials::Int=0,
        meeting_horizon::Int=1000)
    rng_coupled = MersenneTwister(seed)
    rng_independent = MersenneTwister(seed)

    coupled_flat = zeros(K * dim)
    independent_chains = [zeros(dim) for _ in 1:K]

    coupled_samples = Matrix{Float64}(undef, K * dim, N)
    independent_samples = Matrix{Float64}(undef, K * dim, N)

    for step in 1:N
        coupled_flat = multi_marginal_transport_hmc_step!(
            RNGSource(rng_coupled), logdensity, potential_gradient,
            Float64(step_size), L, K, coupled_flat)
        coupled_samples[:, step] = coupled_flat

        for k in 1:K
            independent_chains[k] = multinomial_hmc_step!(
                RNGSource(rng_independent), logdensity, potential_gradient,
                Float64(step_size), L, independent_chains[k])
        end
        for k in 1:K
            offset = (k - 1) * dim
            independent_samples[offset+1:offset+dim, step] = independent_chains[k]
        end
    end

    coupled_variance = vec(var(coupled_samples; dims=2))
    independent_variance = vec(var(independent_samples; dims=2))
    vr = independent_variance ./ max.(coupled_variance, 1e-30)

    pairwise_corr = Matrix{Float64}(undef, K, K)
    for i in 1:K, j in 1:K
        offset_i = (i - 1) * dim
        offset_j = (j - 1) * dim
        chain_i = vec(mean(coupled_samples[offset_i+1:offset_i+dim, :]; dims=1))
        chain_j = vec(mean(coupled_samples[offset_j+1:offset_j+dim, :]; dims=1))
        pairwise_corr[i, j] = length(chain_i) > 1 ? cor(chain_i, chain_j) : 1.0
    end

    coupled_ess = minimum(_autocorrelation_ess(
        coupled_samples[d, :]) for d in 1:K*dim)
    independent_ess = minimum(_autocorrelation_ess(
        independent_samples[d, :]) for d in 1:K*dim)
    grads_per_coupled_step = K * (L + 1)
    grads_per_independent_step = K * (L + 1)
    coupled_ess_per_grad = coupled_ess / (N * grads_per_coupled_step)
    independent_ess_per_grad = independent_ess / (N * grads_per_independent_step)

    meeting_times = nothing
    if K == 2 && meeting_trials > 0
        meeting_times = Union{Nothing, Int}[]
        for trial in 1:meeting_trials
            rng_trial = MersenneTwister(seed + UInt64(trial))
            pos = zeros(2 * dim)
            pos[1:dim] .= 0.5 .* randn(rng_trial, dim)
            pos[dim+1:2*dim] .= 0.5 .* randn(rng_trial, dim)
            met = nothing
            for t in 1:meeting_horizon
                pos = multi_marginal_transport_hmc_step!(
                    RNGSource(rng_trial), logdensity, potential_gradient,
                    Float64(step_size), L, 2, pos)
                if pos[1:dim] ≈ pos[dim+1:2*dim]
                    met = t
                    break
                end
            end
            push!(meeting_times, met)
        end
    end

    MultiMarginalDiagnostic(seed, Float64(step_size), L, K, dim, N,
        coupled_samples, independent_samples,
        coupled_variance, independent_variance, vr,
        pairwise_corr, coupled_ess_per_grad, independent_ess_per_grad,
        meeting_times)
end

function summary(d::MultiMarginalDiagnostic)
    lines = String[]
    push!(lines, "Multi-marginal transport HMC evaluation")
    push!(lines, "  seed=$(d.seed) step_size=$(d.step_size) L=$(d.L) K=$(d.K) dim=$(d.dim) N=$(d.N)")
    push!(lines, "  Variance reduction (ind/coupled): median=$(round(median(d.variance_reduction); digits=3))")
    push!(lines, "  Pairwise chain correlation (off-diagonal): $(round(mean(d.pairwise_correlation[i,j] for i in 1:d.K for j in 1:d.K if i != j); digits=4))")
    push!(lines, "  ESS/gradient: coupled=$(round(d.coupled_ess_per_grad; sigdigits=3)) independent=$(round(d.independent_ess_per_grad; sigdigits=3))")
    if d.meeting_times !== nothing
        met_count = count(!isnothing, d.meeting_times)
        total = length(d.meeting_times)
        push!(lines, "  Meeting times (K=2): $(met_count)/$(total) met within horizon")
        observed = filter(!isnothing, d.meeting_times)
        if !isempty(observed)
            push!(lines, "    median=$(median(observed)) max=$(maximum(observed))")
        end
    end
    join(lines, "\n")
end

end
