"""
Candidate 1: Whole-path MH with Gaussian perturbation proposal.

Proposes a new path Y by adding correlated Gaussian noise to the current
path X. The proposal density Q(Y|X) is evaluable (product of independent
Gaussians per time step), so the full MH ratio can be computed.

The accepted-flow formulation handles hard zeros: when the proposed path Y
does not satisfy the endpoint condition (Y ∉ E), its weight is zero and
symmetricAcceptedFlow returns 0 → rejection.

This candidate is expected to suffer acceptance collapse for large L because
the proposal perturbs all L segments independently, and the acceptance
probability decays roughly as (acceptance per step)^L.
"""

using Random

struct GuidedMHResult{T<:AbstractFloat}
    paths::Vector{Matrix{T}}
    acceptance_rate::T
    n_accepted::Int
    n_total::Int
    log_ratios::Vector{T}
end

"""
Propose a new path by adding Gaussian noise to each interior point.
The start point x_0 is fixed (Dirac initial condition).
The noise scale σ_proposal controls how far the proposal deviates.

Returns (proposed_path, log_proposal_forward, log_proposal_reverse).
"""
function propose_whole_path(
    current_path::AbstractMatrix{T}, sigma_proposal::T, rng::AbstractRNG
) where {T<:AbstractFloat}
    d, Lp1 = size(current_path)
    proposed = copy(current_path)

    log_q_forward = zero(T)
    log_q_reverse = zero(T)

    for t in 2:Lp1
        for i in 1:d
            noise = randn(rng, T) * sigma_proposal
            proposed[i, t] = current_path[i, t] + noise
            log_q_forward += -noise^2 / (2 * sigma_proposal^2) -
                             log(sigma_proposal * sqrt(2 * T(π)))
            reverse_noise = current_path[i, t] - proposed[i, t]
            log_q_reverse += -reverse_noise^2 / (2 * sigma_proposal^2) -
                             log(sigma_proposal * sqrt(2 * T(π)))
        end
    end

    return proposed, log_q_forward, log_q_reverse
end

"""
MH acceptance step using the accepted-flow formulation.

For the support-restricted target π̃(X) = path_density(X) · 𝟙_E(X):
- If proposed path Y ∉ E: weight(Y) = 0, so min(w(X)·q(X,Y), 0) = 0 → reject
- If current path X ∉ E: weight(X) = 0, forward flow = 0 → reject (should not happen)
- If both in E: standard log MH ratio = log π̃(Y) + log Q(X|Y) - log π̃(X) - log Q(Y|X)
"""
function guided_mh_step!(
    path::AbstractMatrix{T}, oe::OverdampedEuler{T},
    sigma_proposal::T, rng::AbstractRNG;
    A_threshold::T = T(-0.8), B_threshold::T = T(0.8)
) where {T<:AbstractFloat}
    proposed, log_q_fwd, log_q_rev = propose_whole_path(path, sigma_proposal, rng)

    log_pi_current = path_log_density(path, oe; A_threshold, B_threshold)
    log_pi_proposed = path_log_density(proposed, oe; A_threshold, B_threshold)

    if isinf(log_pi_proposed) && log_pi_proposed < 0
        return false, T(-Inf)
    end

    log_ratio = log_pi_proposed + log_q_rev - log_pi_current - log_q_fwd

    if log(rand(rng, T)) < log_ratio
        path .= proposed
        return true, log_ratio
    end
    return false, log_ratio
end

"""
Run whole-path MH for `n_iter` iterations.
"""
function run_guided_mh(
    initial_path::AbstractMatrix{T}, oe::OverdampedEuler{T},
    sigma_proposal::T, n_iter::Int, rng::AbstractRNG;
    A_threshold::T = T(-0.8), B_threshold::T = T(0.8), thin::Int = 1
) where {T<:AbstractFloat}
    path = copy(initial_path)
    n_accepted = 0
    paths = Matrix{T}[]
    log_ratios = T[]

    for i in 1:n_iter
        accepted, lr = guided_mh_step!(path, oe, sigma_proposal, rng;
                                        A_threshold, B_threshold)
        if accepted
            n_accepted += 1
        end
        push!(log_ratios, lr)
        if i % thin == 0
            push!(paths, copy(path))
        end
    end

    return GuidedMHResult{T}(
        paths,
        T(n_accepted) / T(n_iter),
        n_accepted,
        n_iter,
        log_ratios,
    )
end
