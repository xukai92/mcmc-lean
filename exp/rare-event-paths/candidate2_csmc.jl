"""
Candidate 2: Conditional Sequential Monte Carlo (CSMC) for endpoint-conditioned paths.

Implements a particle Gibbs-style conditional SMC sweep:
1. N particles are propagated forward using the transition kernel P_δ
2. All particles start from x_0 (fixed initial condition)
3. At the final step L, particles are reweighted by 𝟙_B(x_L)
4. The reference path is forced to survive all resampling steps
5. A new path is selected by systematic resampling at the final step

The basic version uses only final-step reweighting. An optional guiding
potential can be used for intermediate reweighting to improve efficiency.
"""

using Random

struct CSMCResult{T<:AbstractFloat}
    paths::Vector{Matrix{T}}
    endpoint_hit_rate::T
    reference_selections::Int
    n_total::Int
end

"""
Systematic resampling: given weights w (unnormalized), return N ancestor
indices. The reference index `ref_idx` is forced to survive.
"""
function systematic_resample(
    weights::AbstractVector{T}, N::Int, ref_idx::Int, rng::AbstractRNG
) where {T<:AbstractFloat}
    W = sum(weights)
    if W ≤ zero(T)
        indices = fill(ref_idx, N)
        return indices
    end

    normalized = weights ./ W
    cumw = cumsum(normalized)

    u = rand(rng, T) / N
    indices = Vector{Int}(undef, N)
    j = 1
    for i in 1:N
        threshold = u + T(i - 1) / N
        while j < N && cumw[j] < threshold
            j += 1
        end
        indices[i] = j
    end

    if !(ref_idx in indices)
        indices[rand(rng, 1:N)] = ref_idx
    end

    return indices
end

"""
Run one CSMC sweep to produce a new path sample.

Particles are propagated forward from x_0 for L steps.
At the final step, particles reaching B have weight 1; others have weight 0.
The reference path (at index 1) is forced to survive.
A path is selected from the surviving particles.

Returns the selected path and the number of particles that reached B.
"""
function csmc_sweep(
    reference_path::AbstractMatrix{T}, N::Int,
    oe::OverdampedEuler{T}, rng::AbstractRNG;
    B_threshold::T = T(0.8)
) where {T<:AbstractFloat}
    d, Lp1 = size(reference_path)
    L = Lp1 - 1

    particles = Array{T, 3}(undef, d, Lp1, N)
    particles[:, :, 1] .= reference_path

    for k in 2:N
        particles[:, 1, k] .= reference_path[:, 1]
    end

    for t in 1:L
        for k in 2:N
            x_t = @view particles[:, t, k]
            x_next = @view particles[:, t+1, k]
            euler_step!(x_next, x_t, oe, rng)
        end
    end

    weights = Vector{T}(undef, N)
    n_hits = 0
    for k in 1:N
        x_L = @view particles[:, Lp1, k]
        if in_basin_B(x_L; threshold=B_threshold)
            weights[k] = one(T)
            n_hits += 1
        else
            weights[k] = zero(T)
        end
    end

    ancestors = systematic_resample(weights, N, 1, rng)
    selected_idx = ancestors[rand(rng, 1:N)]

    selected_path = particles[:, :, selected_idx]
    return copy(selected_path), n_hits
end

"""
Run conditional SMC for `n_iter` iterations, producing a chain of paths.
"""
function run_csmc(
    initial_path::AbstractMatrix{T}, N::Int,
    oe::OverdampedEuler{T}, n_iter::Int, rng::AbstractRNG;
    B_threshold::T = T(0.8), thin::Int = 1
) where {T<:AbstractFloat}
    reference_path = copy(initial_path)
    paths = Matrix{T}[]
    total_hits = 0
    ref_selections = 0

    for i in 1:n_iter
        new_path, n_hits = csmc_sweep(reference_path, N, oe, rng; B_threshold)
        total_hits += n_hits

        if new_path == reference_path
            ref_selections += 1
        end

        reference_path = new_path

        if i % thin == 0
            push!(paths, copy(reference_path))
        end
    end

    avg_hit_rate = T(total_hits) / T(n_iter * N)

    return CSMCResult{T}(
        paths,
        avg_hit_rate,
        ref_selections,
        n_iter,
    )
end
