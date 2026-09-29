"""
2D double-well-with-bump potential for rare-event path sampling pilot.

V(q, r) = (q² - 1)² + r²/2 + c·exp(-(q² + r²)/s²) + ε·r

Parameters:
- c, s: bump height and width (c > 0 creates a repulsive barrier at the origin)
- ε: channel asymmetry (ε = 0 gives reflection symmetry in r)
"""

struct DoubleWellBump{T<:AbstractFloat}
    c::T
    s::T
    epsilon::T
end

function potential(dw::DoubleWellBump{T}, q::T, r::T) where {T<:AbstractFloat}
    s2 = dw.s * dw.s
    exp_term = dw.c * exp(-(q * q + r * r) / s2)
    return (q * q - one(T))^2 + r * r / 2 + exp_term + dw.epsilon * r
end

function potential(dw::DoubleWellBump{T}, x::AbstractVector{T}) where {T<:AbstractFloat}
    return potential(dw, x[1], x[2])
end

function grad_potential(dw::DoubleWellBump{T}, q::T, r::T) where {T<:AbstractFloat}
    s2 = dw.s * dw.s
    exp_term = exp(-(q * q + r * r) / s2)
    dVdq = 4 * q * (q * q - one(T)) - 2 * dw.c * q / s2 * exp_term
    dVdr = r - 2 * dw.c * r / s2 * exp_term + dw.epsilon
    return T[dVdq, dVdr]
end

function grad_potential(dw::DoubleWellBump{T}, x::AbstractVector{T}) where {T<:AbstractFloat}
    return grad_potential(dw, x[1], x[2])
end

function in_basin_A(x::AbstractVector{T}; threshold::T = T(-0.8)) where {T<:AbstractFloat}
    return x[1] < threshold
end

function in_basin_B(x::AbstractVector{T}; threshold::T = T(0.8)) where {T<:AbstractFloat}
    return x[1] > threshold
end

function satisfies_endpoint_condition(
    path::AbstractMatrix{T}; A_threshold::T = T(-0.8), B_threshold::T = T(0.8)
) where {T<:AbstractFloat}
    x0 = @view path[:, 1]
    xL = @view path[:, end]
    return in_basin_A(x0; threshold=A_threshold) && in_basin_B(xL; threshold=B_threshold)
end
