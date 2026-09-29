"""
Transition path sampling with one-way forward shooting moves (Dellago et al. 2002).

Given a reactive path X = (x_0, ..., x_L) satisfying x_0 ∈ A and x_L ∈ B:
1. Select shooting point τ uniformly from {1, ..., L-1}
2. Keep x_0, ..., x_τ unchanged
3. Forward-simulate x'_{τ+1}, ..., x'_L from x_τ using the transition kernel
4. Accept if x'_L ∈ B (the MH ratio reduces to the endpoint indicator)

The acceptance simplification holds because the proposal density ∏ p(x'_{t+1}|x'_t)
for the new segment exactly cancels the same factor in the path density ratio,
leaving only the endpoint indicator 𝟙_B(x'_L) / 𝟙_B(x_L) = 𝟙_B(x'_L).
"""

using Random

struct TPSResult{T<:AbstractFloat}
    paths::Vector{Matrix{T}}
    acceptance_rate::T
    n_accepted::Int
    n_total::Int
end

function tps_one_way_shooting!(
    path::AbstractMatrix{T}, oe::OverdampedEuler{T}, rng::AbstractRNG;
    B_threshold::T = T(0.8)
) where {T<:AbstractFloat}
    L = size(path, 2) - 1
    tau = rand(rng, 1:(L-1))

    proposed = copy(path)
    for t in tau:L-1
        x_t = @view proposed[:, t]
        x_next = @view proposed[:, t+1]
        euler_step!(x_next, x_t, oe, rng)
    end

    if in_basin_B(@view(proposed[:, end]); threshold=B_threshold)
        path .= proposed
        return true
    end
    return false
end

"""
Run TPS with one-way forward shooting for `n_iter` iterations.
Requires an initial reactive path satisfying the endpoint condition.
"""
function run_tps(
    initial_path::AbstractMatrix{T}, oe::OverdampedEuler{T},
    n_iter::Int, rng::AbstractRNG;
    B_threshold::T = T(0.8), thin::Int = 1
) where {T<:AbstractFloat}
    path = copy(initial_path)
    n_accepted = 0
    paths = Matrix{T}[]

    for i in 1:n_iter
        accepted = tps_one_way_shooting!(path, oe, rng; B_threshold)
        if accepted
            n_accepted += 1
        end
        if i % thin == 0
            push!(paths, copy(path))
        end
    end

    return TPSResult{T}(
        paths,
        T(n_accepted) / T(n_iter),
        n_accepted,
        n_iter,
    )
end

"""
Find an initial reactive path by rejection: generate paths from x0 until one
reaches B. Returns the path and the number of attempts.
"""
function find_initial_reactive_path(
    x0::AbstractVector{T}, L::Int, oe::OverdampedEuler{T}, rng::AbstractRNG;
    max_attempts::Int = 100_000,
    A_threshold::T = T(-0.8), B_threshold::T = T(0.8)
) where {T<:AbstractFloat}
    for attempt in 1:max_attempts
        path = generate_path(x0, L, oe, rng)
        if satisfies_endpoint_condition(path; A_threshold, B_threshold)
            return path, attempt
        end
    end
    error("Failed to find initial reactive path after $max_attempts attempts")
end
