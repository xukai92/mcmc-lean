"""
Frozen pilot protocol: parameter choices, seeds, and iteration counts.

Parameters were chosen after numerical exploration to satisfy:
(a) Event rarity P(E) > 0 at accessible regime
(b) Two visible channels around the bump
(c) Rejection reference feasible in accessible regime

The bump height c=3 with width s=0.5 creates a barrier at the origin that
forces paths to go around via the upper (r > 0) or lower (r < 0) channel.
"""

struct PilotProtocol{T<:AbstractFloat}
    c::T
    s::T
    beta::T
    delta::T
    epsilon::T
    L::Int
    x0::Vector{T}
    A_threshold::T
    B_threshold::T
    n_iter::Int
    n_warmup::Int
    thin::Int
    seeds::Vector{UInt64}
    csmc_particles::Int
    guided_mh_sigma::T
    regime_name::String
end

function accessible_symmetric_protocol(::Type{T} = Float64) where {T<:AbstractFloat}
    return PilotProtocol{T}(
        T(3),        # c: bump height
        T(0.5),      # s: bump width
        T(3),        # β: inverse temperature (moderate → accessible)
        T(0.01),     # δ: time step
        T(0),        # ε: asymmetry (0 = symmetric, symmetry check)
        200,         # L: path length
        T[-1, 0],    # x₀: starting point in basin A
        T(-0.8),     # A threshold
        T(0.8),      # B threshold
        5000,        # n_iter: total iterations per method
        500,         # n_warmup: warmup iterations (discarded)
        1,           # thin: thinning interval
        UInt64[42, 137, 2024, 7919],  # seeds for independent runs
        32,          # N: CSMC particles
        T(0.05),     # σ: guided MH proposal scale
        "accessible_symmetric",
    )
end

function accessible_asymmetric_protocol(::Type{T} = Float64) where {T<:AbstractFloat}
    return PilotProtocol{T}(
        T(3),        # c
        T(0.5),      # s
        T(3),        # β
        T(0.01),     # δ
        T(0.3),      # ε: nonzero → asymmetric channels
        200,         # L
        T[-1, 0],    # x₀
        T(-0.8),     # A threshold
        T(0.8),      # B threshold
        5000,        # n_iter
        500,         # n_warmup
        1,           # thin
        UInt64[42, 137, 2024, 7919],
        32,          # N: CSMC particles
        T(0.05),     # σ: guided MH proposal scale
        "accessible_asymmetric",
    )
end

function hard_regime_protocol(::Type{T} = Float64) where {T<:AbstractFloat}
    return PilotProtocol{T}(
        T(3),        # c
        T(0.5),      # s
        T(8),        # β: high inverse temperature → rare events
        T(0.01),     # δ
        T(0.3),      # ε: asymmetric
        500,         # L: longer paths needed at low temperature
        T[-1, 0],    # x₀
        T(-0.8),     # A threshold
        T(0.8),      # B threshold
        5000,        # n_iter
        500,         # n_warmup
        1,           # thin
        UInt64[42, 137, 2024, 7919],
        64,          # N: more particles for harder problem
        T(0.02),     # σ: smaller perturbation for harder problem
        "hard_asymmetric",
    )
end

function make_dynamics(proto::PilotProtocol{T}) where {T<:AbstractFloat}
    dw = DoubleWellBump{T}(proto.c, proto.s, proto.epsilon)
    oe = OverdampedEuler{T, typeof(dw)}(dw, proto.delta, proto.beta)
    return dw, oe
end

function all_protocols(::Type{T} = Float64) where {T<:AbstractFloat}
    return [
        accessible_symmetric_protocol(T),
        accessible_asymmetric_protocol(T),
        hard_regime_protocol(T),
    ]
end
