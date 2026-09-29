"""
Overdamped Euler-Maruyama integrator and explicit Gaussian transition density.

x_{t+1} = x_t - δ·∇V(x_t) + √(2δ/β)·ξ_t,  ξ_t ~ N(0, I₂)

The transition density p(x_{t+1} | x_t) is Gaussian with mean x_t - δ∇V(x_t)
and covariance (2δ/β)·I.
"""

using Random
using LinearAlgebra

struct OverdampedEuler{T<:AbstractFloat, DW}
    dw::DW
    delta::T
    beta::T
end

function noise_scale(oe::OverdampedEuler{T}) where {T<:AbstractFloat}
    return sqrt(2 * oe.delta / oe.beta)
end

function euler_step!(
    x_next::AbstractVector{T}, x::AbstractVector{T},
    oe::OverdampedEuler{T}, rng::AbstractRNG
) where {T<:AbstractFloat}
    gV = grad_potential(oe.dw, x)
    σ = noise_scale(oe)
    @inbounds for i in eachindex(x_next)
        x_next[i] = x[i] - oe.delta * gV[i] + σ * randn(rng, T)
    end
    return x_next
end

function euler_step(
    x::AbstractVector{T}, oe::OverdampedEuler{T}, rng::AbstractRNG
) where {T<:AbstractFloat}
    x_next = similar(x)
    return euler_step!(x_next, x, oe, rng)
end

"""
Log-density of the Gaussian transition p(x_next | x), up to a normalizing
constant that depends only on δ and β (not on the states).

log p(x_next | x) = -β/(4δ) · ||x_next - x + δ∇V(x)||²  + const
"""
function transition_log_density(
    x_next::AbstractVector{T}, x::AbstractVector{T}, oe::OverdampedEuler{T}
) where {T<:AbstractFloat}
    gV = grad_potential(oe.dw, x)
    coeff = -oe.beta / (4 * oe.delta)
    diff_sq = zero(T)
    @inbounds for i in eachindex(x)
        d = x_next[i] - x[i] + oe.delta * gV[i]
        diff_sq += d * d
    end
    return coeff * diff_sq
end

"""
Full log-density of the transition including the normalizing constant.
log p(x_next | x) = -d/2 · log(4πδ/β) - β/(4δ) · ||x_next - x + δ∇V(x)||²
"""
function transition_log_density_full(
    x_next::AbstractVector{T}, x::AbstractVector{T}, oe::OverdampedEuler{T}
) where {T<:AbstractFloat}
    d = length(x)
    log_norm = -T(d) / 2 * log(4 * T(π) * oe.delta / oe.beta)
    return log_norm + transition_log_density(x_next, x, oe)
end

"""
Unnormalized log-density of a full path under the endpoint-conditioned ensemble.
Returns -Inf if the path does not satisfy the endpoint condition.

log π̃(X) = -β/(4δ) · Σ_{t=0}^{L-1} ||x_{t+1} - x_t + δ∇V(x_t)||²
"""
function path_log_density(
    path::AbstractMatrix{T}, oe::OverdampedEuler{T};
    A_threshold::T = T(-0.8), B_threshold::T = T(0.8)
) where {T<:AbstractFloat}
    if !satisfies_endpoint_condition(path; A_threshold, B_threshold)
        return T(-Inf)
    end
    L = size(path, 2) - 1
    logp = zero(T)
    @inbounds for t in 1:L
        x_t = @view path[:, t]
        x_next = @view path[:, t+1]
        logp += transition_log_density(x_next, x_t, oe)
    end
    return logp
end

"""
Generate a full path of length L+1 from initial state x0.
Returns a 2×(L+1) matrix.
"""
function generate_path(
    x0::AbstractVector{T}, L::Int, oe::OverdampedEuler{T}, rng::AbstractRNG
) where {T<:AbstractFloat}
    d = length(x0)
    path = Matrix{T}(undef, d, L + 1)
    path[:, 1] .= x0
    for t in 1:L
        x_t = @view path[:, t]
        x_next = @view path[:, t+1]
        euler_step!(x_next, x_t, oe, rng)
    end
    return path
end
