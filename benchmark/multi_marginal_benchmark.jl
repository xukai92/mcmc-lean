using LinearAlgebra
const BLAS_THREADS = 1
LinearAlgebra.BLAS.set_num_threads(BLAS_THREADS)

using Random
using Statistics
using MCMCDiagnosticTools
using Dates
using VerifiedSamplers

const DEV_MODE = "--dev" in ARGS
const UNKNOWN_ARGUMENTS = filter(!=("--dev"), ARGS)
isempty(UNKNOWN_ARGUMENTS) || error(
    "unknown arguments: $(join(UNKNOWN_ARGUMENTS, ' ')); supported: --dev")

const Runtime = VerifiedSamplers.Runtime
const Reference = VerifiedSamplers.Reference
const Optimized = VerifiedSamplers.Optimized
const Evaluation = VerifiedSamplers.Evaluation

const CHAIN_COUNT = DEV_MODE ? 2 : 4
const WARMUP = 1000
const RETAINED = DEV_MODE ? 1000 : 10000
const TOTAL_DRAWS = WARMUP + RETAINED
const K_VALUES = DEV_MODE ? [2, 4] : [2, 4, 8]
const LEAPFROG_STEPS = 10
const MEETING_TRIALS = DEV_MODE ? 20 : 100
const MEETING_HORIZON = 1000
const SEEDS = [7331 + i for i in 0:(CHAIN_COUNT - 1)]
const RESULTS_DIR = joinpath(@__DIR__, "results", "multi_marginal")

struct BenchmarkTarget{T<:AbstractFloat}
    name::String
    dimension::Int
    logdensity::Function
    potential_gradient::Function
    true_mean::Vector{T}
    true_variance::Vector{T}
    hmc_step_size::T
end

function make_independent_rngs(K::Int, base_seed::Int)
    return [Random.Xoshiro(base_seed + 1000 * k) for k in 1:K]
end

function benchmark_targets()
    targets = BenchmarkTarget{Float64}[]

    if DEV_MODE
        d = 10
        push!(targets, BenchmarkTarget{Float64}(
            "isotropic-gaussian", d,
            q -> -sum(abs2, q) / 2,
            q -> copy(q),
            zeros(d), ones(d), 0.15))

        ρ = 0.9
        Σ = [ρ^abs(i - j) for i in 1:d, j in 1:d]
        Σ_inv = inv(Σ)
        push!(targets, BenchmarkTarget{Float64}(
            "correlated-gaussian", d,
            q -> -dot(q, Σ_inv * q) / 2,
            q -> Σ_inv * q,
            zeros(d), ones(d), 0.10))

        push!(targets, BenchmarkTarget{Float64}(
            "neals-funnel", 10,
            function(q)
                v = q[1]
                logp = -v^2 / 18
                for i in 2:length(q)
                    logp -= q[i]^2 / (2 * exp(v)) + v / 2
                end
                logp
            end,
            function(q)
                v = q[1]
                g = similar(q)
                g[1] = v / 9
                for i in 2:length(q)
                    g[1] -= (q[i]^2 / (2 * exp(v)) - 0.5)
                end
                for i in 2:length(q)
                    g[i] = q[i] / exp(v)
                end
                g
            end,
            zeros(10),
            vcat([9.0], fill(exp(9.0 / 2), 9)),
            0.02))
    else
        for d in [50, 100]
            push!(targets, BenchmarkTarget{Float64}(
                "isotropic-gaussian", d,
                q -> -sum(abs2, q) / 2,
                q -> copy(q),
                zeros(d), ones(d), d == 50 ? 0.12 : 0.10))

            ρ = 0.9
            Σ = [ρ^abs(i - j) for i in 1:d, j in 1:d]
            Σ_inv = inv(Σ)
            push!(targets, BenchmarkTarget{Float64}(
                "correlated-gaussian", d,
                q -> -dot(q, Σ_inv * q) / 2,
                q -> Σ_inv * q,
                zeros(d), ones(d), d == 50 ? 0.08 : 0.06))
        end

        d = 10
        push!(targets, BenchmarkTarget{Float64}(
            "neals-funnel", d,
            function(q)
                v = q[1]
                logp = -v^2 / 18
                for i in 2:length(q)
                    logp -= q[i]^2 / (2 * exp(v)) + v / 2
                end
                logp
            end,
            function(q)
                v = q[1]
                g = similar(q)
                g[1] = v / 9
                for i in 2:length(q)
                    g[1] -= (q[i]^2 / (2 * exp(v)) - 0.5)
                end
                for i in 2:length(q)
                    g[i] = q[i] / exp(v)
                end
                g
            end,
            zeros(d),
            vcat([9.0], fill(exp(9.0 / 2), 9)),
            0.02))
    end
    targets
end

function make_counters(logdensity, gradient)
    grad_count = Ref(0)
    log_count = Ref(0)
    counted_grad = function(q)
        grad_count[] += 1
        gradient(q)
    end
    counted_log = function(q)
        log_count[] += 1
        logdensity(q)
    end
    counted_log, counted_grad, log_count, grad_count
end

# --- Conformance gates ---

function conformance_gate_mm(target, step_size, steps, K)
    d = target.dimension
    rng = MersenneTwister(77777)
    events = Runtime.FloatTraceEvent[]
    for _ in 1:d
        push!(events, Runtime.NormalEvent(randn(rng)))
    end
    for _ in 1:K
        push!(events, Runtime.IndexEvent(BigInt(rand(rng, 0:steps))))
        push!(events, Runtime.UniformEvent(rand(rng)))
    end
    initial = 0.1 .* randn(rng, d * K)
    result = Evaluation.replay_pair(events,
        source -> Reference.multi_marginal_transport_hmc_step!(source,
            target.logdensity, target.potential_gradient,
            Float64(step_size), steps, K, Float64.(initial)),
        source -> Optimized.multi_marginal_transport_hmc_step!(source,
            target.logdensity, target.potential_gradient,
            Float64(step_size), steps, K, Float64.(initial)))
    Evaluation.conforms_numerical(result; atol=1e-10)
end

function conformance_gate_hmc(target, step_size, steps)
    d = target.dimension
    rng = MersenneTwister(77778)
    events = Runtime.FloatTraceEvent[]
    for _ in 1:d
        push!(events, Runtime.NormalEvent(randn(rng)))
    end
    push!(events, Runtime.IndexEvent(BigInt(rand(rng, 0:steps))))
    push!(events, Runtime.UniformEvent(rand(rng)))
    initial = 0.1 .* randn(rng, d)
    result = Evaluation.replay_pair(events,
        source -> Reference.multinomial_hmc_step!(source,
            target.logdensity, target.potential_gradient,
            Float64(step_size), steps, Float64.(initial)),
        source -> Optimized.multinomial_hmc_step!(source,
            target.logdensity, target.potential_gradient,
            Float64(step_size), steps, Float64.(initial)))
    Evaluation.conforms_numerical(result; atol=1e-10)
end

# --- Three-arm sampling ---

function run_coupled_arm(target, K::Int, step_size::T, steps::Int,
        seed::Int) where {T<:AbstractFloat}
    d = target.dimension
    counted_log, counted_grad, log_count, grad_count =
        make_counters(target.logdensity, target.potential_gradient)
    workspace = Optimized.MultiMarginalTransportHMCWorkspace{T}(d, K, steps)
    rng = Random.Xoshiro(seed)
    source = Runtime.RNGSource(rng)
    position = zeros(T, K * d)
    chain = Matrix{T}(undef, K * d, TOTAL_DRAWS)
    for i in 1:TOTAL_DRAWS
        position = Optimized.multi_marginal_transport_hmc_step!(workspace,
            source, counted_log, counted_grad,
            step_size, steps, K, position)
        chain[:, i] = position
    end
    retained = chain[:, (WARMUP + 1):end]
    (; retained, grad_count=grad_count[], log_count=log_count[])
end

function run_independent_arm(target, K::Int, step_size::T, steps::Int,
        seed::Int) where {T<:AbstractFloat}
    d = target.dimension
    counted_log, counted_grad, log_count, grad_count =
        make_counters(target.logdensity, target.potential_gradient)
    rngs = make_independent_rngs(K, seed)
    positions = [zeros(T, d) for _ in 1:K]
    chain = Matrix{T}(undef, K * d, TOTAL_DRAWS)
    for i in 1:TOTAL_DRAWS
        for k in 1:K
            positions[k] = Optimized.multinomial_hmc_step!(
                Runtime.RNGSource(rngs[k]), counted_log, counted_grad,
                step_size, steps, positions[k])
        end
        for k in 1:K
            offset = (k - 1) * d
            chain[offset+1:offset+d, i] = positions[k]
        end
    end
    retained = chain[:, (WARMUP + 1):end]
    (; retained, grad_count=grad_count[], log_count=log_count[])
end

function run_shared_noise_arm(target, K::Int, step_size::T, steps::Int,
        seed::Int) where {T<:AbstractFloat}
    d = target.dimension
    counted_log, counted_grad, log_count, grad_count =
        make_counters(target.logdensity, target.potential_gradient)
    momentum_rng = Random.Xoshiro(seed)
    select_rngs = make_independent_rngs(K, seed + 500000)
    positions = [zeros(T, d) for _ in 1:K]
    chain = Matrix{T}(undef, K * d, TOTAL_DRAWS)
    momentum_buf = Vector{T}(undef, d)
    for i in 1:TOTAL_DRAWS
        for j in 1:d
            momentum_buf[j] = T(randn(momentum_rng))
        end
        for k in 1:K
            positions[k] = _shared_momentum_multinomial_step!(
                Runtime.RNGSource(select_rngs[k]),
                counted_log, counted_grad,
                step_size, steps, positions[k], copy(momentum_buf))
        end
        for k in 1:K
            offset = (k - 1) * d
            chain[offset+1:offset+d, i] = positions[k]
        end
    end
    retained = chain[:, (WARMUP + 1):end]
    (; retained, grad_count=grad_count[], log_count=log_count[])
end

function _shared_momentum_multinomial_step!(
        source::Runtime.AbstractRandomSource, logdensity, gradient,
        step_size::T, steps::Int, current::AbstractVector{T},
        momentum::AbstractVector{T}) where {T<:AbstractFloat}
    d = length(current)
    ε = step_size
    half_step = ε / T(2)
    origin = Int(Runtime.draw_below!(source, steps + 1))

    positions = Matrix{T}(undef, d, steps + 1)
    logweights = Vector{T}(undef, steps + 1)

    current_index = origin + 1
    positions[:, current_index] = current
    logweights[current_index] = T(logdensity(current)) - sum(abs2, momentum) / T(2)

    bq, bp = copy(current), copy(momentum)
    for index in origin:-1:1
        force = T.(gradient(bq))
        @. bp += half_step * force
        @. bq -= ε * bp
        force = T.(gradient(bq))
        @. bp += half_step * force
        positions[:, index] = bq
        logweights[index] = T(logdensity(bq)) - sum(abs2, bp) / T(2)
    end

    fq, fp = copy(current), copy(momentum)
    for index in (origin + 2):(steps + 1)
        force = T.(gradient(fq))
        @. fp -= half_step * force
        @. fq += ε * fp
        force = T.(gradient(fq))
        @. fp -= half_step * force
        positions[:, index] = fq
        logweights[index] = T(logdensity(fq)) - sum(abs2, fp) / T(2)
    end

    max_weight = maximum(logweights)
    total = zero(T)
    @inbounds for i in eachindex(logweights)
        logweights[i] = exp(logweights[i] - max_weight)
        total += logweights[i]
    end
    target = T(Runtime.uniform_unit!(source)) * total
    cumulative = zero(T)
    selected = steps + 1
    @inbounds for i in eachindex(logweights)
        cumulative += logweights[i]
        if target < cumulative
            selected = i
            break
        end
    end
    copy(@view positions[:, selected])
end

# --- Diagnostics ---

function compute_single_chain_diagnostics(chain::AbstractMatrix{T}) where {T}
    d = size(chain, 1)
    n_draws = size(chain, 2)
    samples = Array{T,3}(undef, n_draws, 1, d)
    for p in 1:d
        samples[:, 1, p] = chain[p, :]
    end
    bulk = ess_rhat(samples; kind=:bulk)
    tail = ess_rhat(samples; kind=:tail)
    mcse_vals = mcse(samples; kind=mean)
    mcse_sq = mcse(samples .^ 2; kind=mean)
    (; min_bulk_ess=minimum(bulk.ess), min_tail_ess=minimum(tail.ess),
        max_rhat=maximum(bulk.rhat), max_mcse_mean=maximum(mcse_vals),
        max_mcse_var=maximum(mcse_sq))
end

function compute_acceptance_rate(samples::AbstractMatrix{T}) where {T}
    n = size(samples, 2)
    accepts = 0
    for i in 2:n
        if @view(samples[:, i]) != @view(samples[:, i-1])
            accepts += 1
        end
    end
    accepts / (n - 1)
end

# --- Pooled identical-target estimand ---

function run_pooled_benchmark(targets)
    println("\n=== Pooled Identical-Target Benchmark ===\n")
    rows = NamedTuple[]
    arms = ["coupled", "independent", "shared-noise"]

    for target in targets
        d = target.dimension
        step_size = target.hmc_step_size

        for K in K_VALUES
            println("[pooled] target=$(target.name) d=$d K=$K")

            print("  conformance (mm-thmc): ")
            if !conformance_gate_mm(target, step_size, LEAPFROG_STEPS, K)
                println("FAILED — skipping K=$K")
                continue
            end
            println("passed")

            if K == K_VALUES[1]
                print("  conformance (multinomial-hmc): ")
                if !conformance_gate_hmc(target, step_size, LEAPFROG_STEPS)
                    println("FAILED — skipping target")
                    break
                end
                println("passed")
            end

            # JIT warmup
            for arm_fn in [run_coupled_arm, run_independent_arm, run_shared_noise_arm]
                try
                    temp_target = BenchmarkTarget{Float64}(
                        "warmup", 2,
                        q -> -sum(abs2, q) / 2, q -> copy(q),
                        zeros(2), ones(2), Float64(0.15))
                    arm_fn(temp_target, 2, Float64(0.15), 2, 99999)
                catch
                end
            end
            GC.gc()

            for (arm_name, arm_fn) in [
                    ("coupled", run_coupled_arm),
                    ("independent", run_independent_arm),
                    ("shared-noise", run_shared_noise_arm)]

                print("  $arm_name: ")
                GC.gc()
                t0 = time_ns()
                results = [arm_fn(target, K, Float64(step_size),
                    LEAPFROG_STEPS, seed) for seed in SEEDS]
                wall_seconds = (time_ns() - t0) / 1e9
                println("$(round(wall_seconds; digits=1))s")

                for (seed_idx, seed) in enumerate(SEEDS)
                    r = results[seed_idx]
                    for k in 1:K
                        offset = (k - 1) * d
                        chain_data = r.retained[offset+1:offset+d, :]
                        diag = compute_single_chain_diagnostics(chain_data)
                        acc = compute_acceptance_rate(
                            r.retained[offset+1:offset+d, :])
                        mean_x1 = mean(chain_data[1, :])
                        push!(rows, (target=target.name, dimension=d,
                            K=K, arm=arm_name, chain=k,
                            replicate_seed=seed,
                            bulk_ess=diag.min_bulk_ess,
                            tail_ess=diag.min_tail_ess,
                            ess_per_sec=diag.min_bulk_ess / wall_seconds,
                            ess_per_gradient=diag.min_bulk_ess / r.grad_count,
                            rhat=diag.max_rhat,
                            acceptance_rate=acc,
                            mcse_mean=diag.max_mcse_mean,
                            mcse_var=diag.max_mcse_var,
                            mean_x1=mean_x1,
                            grad_count=r.grad_count,
                            logdensity_count=r.log_count,
                            wall_seconds=wall_seconds,
                            float_type="Float64"))
                    end
                end

                sample_means = Matrix{Float64}(undef, d, CHAIN_COUNT * K)
                for (seed_idx, _) in enumerate(SEEDS)
                    r = results[seed_idx]
                    for k in 1:K
                        offset = (k - 1) * d
                        col = (seed_idx - 1) * K + k
                        sample_means[:, col] = vec(mean(
                            r.retained[offset+1:offset+d, :]; dims=2))
                    end
                end
                println("    mean_var(x₁)=$(round(var(sample_means[1, :]); sigdigits=3))")
            end
        end
    end
    rows
end

# --- CRN contrast estimand ---

function make_shifted_target(base_target, shift_vector::Vector{T}) where {T}
    d = base_target.dimension
    BenchmarkTarget{T}(
        base_target.name * "-shifted",
        d,
        q -> base_target.logdensity(q .- shift_vector),
        q -> base_target.potential_gradient(q .- shift_vector),
        base_target.true_mean .+ shift_vector,
        copy(base_target.true_variance),
        base_target.hmc_step_size)
end

function run_crn_coupled(targets_shifted, K::Int, step_size::T, steps::Int,
        seed::Int) where {T<:AbstractFloat}
    d = targets_shifted[1].dimension
    rng = Random.Xoshiro(seed)
    source = Runtime.RNGSource(rng)
    position = zeros(T, K * d)
    chain = Matrix{T}(undef, K * d, TOTAL_DRAWS)

    for i in 1:TOTAL_DRAWS
        momentum = T[Runtime.standard_normal!(source) for _ in 1:d]
        result = Vector{T}(undef, K * d)
        for k in 1:K
            offset = (k - 1) * d
            chain_q = collect(position[offset+1:offset+d])
            t = targets_shifted[k]
            selected = _shared_momentum_multinomial_step!(source,
                t.logdensity, t.potential_gradient,
                step_size, steps, chain_q, momentum)
            @inbounds result[offset+1:offset+d] = selected
        end
        position = result
        chain[:, i] = position
    end
    chain[:, (WARMUP + 1):end]
end

function run_crn_independent(targets_shifted, K::Int, step_size::T, steps::Int,
        seed::Int) where {T<:AbstractFloat}
    d = targets_shifted[1].dimension
    rngs = make_independent_rngs(K, seed)
    positions = [zeros(T, d) for _ in 1:K]
    chain = Matrix{T}(undef, K * d, TOTAL_DRAWS)
    for i in 1:TOTAL_DRAWS
        for k in 1:K
            t = targets_shifted[k]
            positions[k] = Optimized.multinomial_hmc_step!(
                Runtime.RNGSource(rngs[k]), t.logdensity, t.potential_gradient,
                step_size, steps, positions[k])
        end
        for k in 1:K
            offset = (k - 1) * d
            chain[offset+1:offset+d, i] = positions[k]
        end
    end
    chain[:, (WARMUP + 1):end]
end

function run_crn_shared_noise(targets_shifted, K::Int, step_size::T, steps::Int,
        seed::Int) where {T<:AbstractFloat}
    d = targets_shifted[1].dimension
    momentum_rng = Random.Xoshiro(seed)
    select_rngs = make_independent_rngs(K, seed + 500000)
    positions = [zeros(T, d) for _ in 1:K]
    chain = Matrix{T}(undef, K * d, TOTAL_DRAWS)
    momentum_buf = Vector{T}(undef, d)
    for i in 1:TOTAL_DRAWS
        for j in 1:d
            momentum_buf[j] = T(randn(momentum_rng))
        end
        for k in 1:K
            t = targets_shifted[k]
            positions[k] = _shared_momentum_multinomial_step!(
                Runtime.RNGSource(select_rngs[k]),
                t.logdensity, t.potential_gradient,
                step_size, steps, positions[k], copy(momentum_buf))
        end
        for k in 1:K
            offset = (k - 1) * d
            chain[offset+1:offset+d, i] = positions[k]
        end
    end
    chain[:, (WARMUP + 1):end]
end

function run_contrast_benchmark(targets)
    println("\n=== CRN Contrast Benchmark ===\n")
    rows = NamedTuple[]

    base_targets = filter(t -> t.name != "neals-funnel", targets)

    for target in base_targets
        d = target.dimension
        step_size = target.hmc_step_size

        for K in K_VALUES
            println("[contrast] target=$(target.name) d=$d K=$K")

            shift_mag = 0.1
            shifts = [begin
                v = zeros(d)
                v[mod1(k, d)] = shift_mag * (isodd(k) ? 1.0 : -1.0)
                v
            end for k in 1:K]
            targets_shifted = [make_shifted_target(target, shifts[k]) for k in 1:K]

            for (arm_name, arm_fn) in [
                    ("coupled", run_crn_coupled),
                    ("independent", run_crn_independent),
                    ("shared-noise", run_crn_shared_noise)]

                print("  $arm_name: ")
                contrast_vars_mean = Float64[]
                contrast_vars_sq = Float64[]

                for seed in SEEDS
                    retained = arm_fn(targets_shifted, K, Float64(step_size),
                        LEAPFROG_STEPS, seed)
                    for ki in 1:K
                        for kj in (ki+1):K
                            offset_i = (ki - 1) * d
                            offset_j = (kj - 1) * d
                            mean_i = vec(mean(
                                retained[offset_i+1:offset_i+d, :]; dims=2))
                            mean_j = vec(mean(
                                retained[offset_j+1:offset_j+d, :]; dims=2))
                            contrast = mean_i .- mean_j
                            push!(contrast_vars_mean, var(contrast))
                            sq_i = vec(mean(
                                retained[offset_i+1:offset_i+d, :] .^ 2; dims=2))
                            sq_j = vec(mean(
                                retained[offset_j+1:offset_j+d, :] .^ 2; dims=2))
                            push!(contrast_vars_sq, var(sq_i .- sq_j))
                        end
                    end
                end
                println("$(length(contrast_vars_mean)) pairs, " *
                    "mean_var=$(round(mean(contrast_vars_mean); sigdigits=3))")

                for (seed_idx, seed) in enumerate(SEEDS)
                    pair_idx = 0
                    for ki in 1:K
                        for kj in (ki+1):K
                            pair_idx += 1
                            global_idx = (seed_idx - 1) * (K * (K - 1) ÷ 2) + pair_idx
                            push!(rows, (target=target.name, dimension=d,
                                K=K, arm=arm_name,
                                replicate_seed=seed,
                                pair_i=ki, pair_j=kj,
                                contrast_var_mean=contrast_vars_mean[global_idx],
                                contrast_var_sq=contrast_vars_sq[global_idx],
                                vr_vs_independent=NaN,
                                float_type="Float64"))
                        end
                    end
                end
            end

            # Compute VR ratios
            for seed in SEEDS
                for ki in 1:K
                    for kj in (ki+1):K
                        ind_rows = filter(r -> r.target == target.name &&
                            r.dimension == d && r.K == K &&
                            r.arm == "independent" && r.replicate_seed == seed &&
                            r.pair_i == ki && r.pair_j == kj, rows)
                        for arm_name in ["coupled", "shared-noise"]
                            arm_rows = filter(r -> r.target == target.name &&
                                r.dimension == d && r.K == K &&
                                r.arm == arm_name && r.replicate_seed == seed &&
                                r.pair_i == ki && r.pair_j == kj, rows)
                            if !isempty(ind_rows) && !isempty(arm_rows)
                                ind_var = first(ind_rows).contrast_var_mean
                                arm_var = first(arm_rows).contrast_var_mean
                                vr = arm_var > 1e-30 ? ind_var / arm_var : NaN
                                idx = findfirst(r -> r === first(arm_rows), rows)
                                if idx !== nothing
                                    old = rows[idx]
                                    rows[idx] = merge(old,
                                        (vr_vs_independent=vr,))
                                end
                            end
                        end
                    end
                end
            end
        end
    end
    rows
end

# --- Coupling-quality diagnostics ---

function run_coupling_diagnostics(targets)
    println("\n=== Coupling-Quality Diagnostics (K=2) ===\n")
    rows = NamedTuple[]

    for target in targets
        d = target.dimension
        step_size = target.hmc_step_size
        K = 2

        println("[coupling] target=$(target.name) d=$d")

        for (seed_idx, seed) in enumerate(SEEDS)
            for trial in 1:MEETING_TRIALS
                rng = Random.Xoshiro(seed * 10000 + trial)
                pos = zeros(2 * d)
                pos[1:d] .= 0.5 .* randn(rng, d)
                pos[d+1:2*d] .= 0.5 .* randn(rng, d)
                source = Runtime.RNGSource(rng)

                distances = Vector{Float64}(undef, MEETING_HORIZON)
                x1_chain1 = Vector{Float64}(undef, MEETING_HORIZON)
                x1_chain2 = Vector{Float64}(undef, MEETING_HORIZON)
                met_tol_1 = false

                for t in 1:MEETING_HORIZON
                    pos = Optimized.multi_marginal_transport_hmc_step!(source,
                        target.logdensity, target.potential_gradient,
                        Float64(step_size), LEAPFROG_STEPS, K, pos)
                    dist = norm(pos[1:d] .- pos[d+1:2*d])
                    distances[t] = dist
                    x1_chain1[t] = pos[1]
                    x1_chain2[t] = pos[d + 1]
                    if dist < 1.0
                        met_tol_1 = true
                    end
                end

                min_dist = minimum(distances)
                med_dist = median(distances)
                final_dist = distances[end]

                x1_mean1 = mean(x1_chain1)
                x1_mean2 = mean(x1_chain2)
                x1_dev1 = x1_chain1 .- x1_mean1
                x1_dev2 = x1_chain2 .- x1_mean2
                denom = sqrt(sum(abs2, x1_dev1) * sum(abs2, x1_dev2))
                corr_x1 = denom > 0 ? dot(x1_dev1, x1_dev2) / denom : 0.0

                push!(rows, (target=target.name, dimension=d,
                    K=K, replicate_seed=seed, trial=trial,
                    min_distance=min_dist, median_distance=med_dist,
                    final_distance=final_dist, met_tol_1=met_tol_1,
                    correlation_x1=corr_x1, horizon=MEETING_HORIZON))
            end
        end

        t_rows = filter(r -> r.target == target.name, rows)
        met_count = count(r -> r.met_tol_1, t_rows)
        med_min = median(r.min_distance for r in t_rows)
        med_corr = median(r.correlation_x1 for r in t_rows)
        println("  $(met_count)/$(length(t_rows)) within tolerance 1.0")
        println("  median min_distance=$(round(med_min; sigdigits=3))")
        println("  median correlation_x1=$(round(med_corr; sigdigits=3))")
    end
    rows
end

# --- Float32 validation ---

function float32_validation()
    print("\nFloat32 type validation: ")
    d = 10
    K = 2
    step_size = Float32(0.15)

    target = BenchmarkTarget{Float32}(
        "isotropic-gaussian-f32", d,
        q -> -sum(abs2, q) / 2,
        q -> copy(q),
        zeros(Float32, d), ones(Float32, d), step_size)

    workspace = Optimized.MultiMarginalTransportHMCWorkspace{Float32}(d, K, LEAPFROG_STEPS)
    rng = Random.Xoshiro(42)
    source = Runtime.RNGSource(rng)
    position = zeros(Float32, K * d)

    for _ in 1:10
        position = Optimized.multi_marginal_transport_hmc_step!(workspace,
            source, target.logdensity, target.potential_gradient,
            step_size, LEAPFROG_STEPS, K, position)
    end

    @assert eltype(position) === Float32 "Float32 type not preserved"
    @assert all(isfinite, position) "Float32 result contains NaN/Inf"
    println("passed (eltype=$(eltype(position)))")
end

# --- CSV output ---

function write_csv(path, rows)
    isempty(rows) && return
    mkpath(dirname(path))
    names = propertynames(first(rows))
    open(path, "w") do io
        println(io, join(names, ','))
        for row in rows
            println(io, join((getproperty(row, n) for n in names), ','))
        end
    end
    println("wrote $path")
end

function write_metadata()
    mkpath(RESULTS_DIR)
    path = joinpath(RESULTS_DIR, "metadata.csv")
    commit = try
        raw = readchomp(`git -C $(joinpath(@__DIR__, "..")) rev-parse --short HEAD`)
        dirty = try
            output = readchomp(`git -C $(joinpath(@__DIR__, "..")) status --porcelain`)
            isempty(output) ? "" : "-dirty"
        catch
            ""
        end
        raw * dirty
    catch
        "unknown"
    end
    hostname = try
        readchomp(`hostname`)
    catch
        "unknown"
    end
    cpu_model = try
        Sys.cpu_info()[1].model
    catch
        "unknown"
    end
    step_sizes = join([string(t.hmc_step_size) for t in benchmark_targets()], ";")
    open(path, "w") do io
        println(io, "key,value")
        println(io, "commit,$commit")
        println(io, "julia_version,$VERSION")
        println(io, "hostname,$hostname")
        println(io, "cpu_model,$cpu_model")
        println(io, "threads,$(Threads.nthreads())")
        println(io, "blas_threads,$BLAS_THREADS")
        println(io, "blas_config,$(LinearAlgebra.BLAS.get_config())")
        println(io, "seeds,$(join(SEEDS, ';'))")
        println(io, "float_type,Float64")
        println(io, "dev_mode,$DEV_MODE")
        println(io, "K_values,$(join(K_VALUES, ';'))")
        println(io, "warmup,$WARMUP")
        println(io, "retained,$RETAINED")
        println(io, "leapfrog_steps,$LEAPFROG_STEPS")
        println(io, "step_sizes,$step_sizes")
        println(io, "meeting_trials,$MEETING_TRIALS")
        println(io, "meeting_horizon,$MEETING_HORIZON")
        println(io, "mcmcdiagnostictools_version,$(pkgversion(MCMCDiagnosticTools))")
        println(io, "timestamp,$(Dates.now())")
    end
    println("wrote $path")
end

function write_summary(pooled_rows, contrast_rows, meeting_rows)
    mkpath(RESULTS_DIR)
    path = joinpath(RESULTS_DIR, "summary.txt")
    open(path, "w") do io
        println(io, "Multi-Marginal Transport HMC Benchmark Summary")
        println(io, "=" ^ 50)
        println(io, "Mode: $(DEV_MODE ? "development (--dev)" : "full")")
        println(io, "Date: $(Dates.now())")
        println(io, "Replicates: $CHAIN_COUNT, Warmup: $WARMUP, Retained: $RETAINED")
        println(io, "K values: $(join(K_VALUES, ", "))")
        println(io, "Leapfrog steps: $LEAPFROG_STEPS")
        println(io)

        println(io, "Pooled Identical-Target Results")
        println(io, "-" ^ 40)
        for target_name in unique(r.target for r in pooled_rows)
            for K in K_VALUES
                for arm in ["coupled", "independent", "shared-noise"]
                    arm_data = filter(r -> r.target == target_name &&
                        r.K == K && r.arm == arm, pooled_rows)
                    isempty(arm_data) && continue
                    d = first(arm_data).dimension
                    med_ess = median(r.bulk_ess for r in arm_data)
                    med_acc = median(r.acceptance_rate for r in arm_data)
                    med_ess_grad = median(r.ess_per_gradient for r in arm_data)
                    println(io, "  $(target_name) d=$d K=$K $(arm): " *
                        "bulk_ESS=$(round(med_ess; digits=1)) " *
                        "accept=$(round(med_acc; digits=3)) " *
                        "ESS/grad=$(round(med_ess_grad; sigdigits=3))")
                end
            end
        end

        println(io)
        println(io, "Variance Reduction (pooled identical-target, x₁ sample mean)")
        println(io, "-" ^ 40)
        for target_name in unique(r.target for r in pooled_rows)
            for K in K_VALUES
                coupled_data = filter(r -> r.target == target_name &&
                    r.K == K && r.arm == "coupled", pooled_rows)
                ind_data = filter(r -> r.target == target_name &&
                    r.K == K && r.arm == "independent", pooled_rows)
                (isempty(coupled_data) || isempty(ind_data)) && continue
                ind_var = var(r.mean_x1 for r in ind_data)
                coupled_var = var(r.mean_x1 for r in coupled_data)
                shared_data = filter(r -> r.target == target_name &&
                    r.K == K && r.arm == "shared-noise", pooled_rows)
                shared_var = isempty(shared_data) ? NaN :
                    var(r.mean_x1 for r in shared_data)
                vr_coupled = coupled_var > 0 ? ind_var / coupled_var : NaN
                vr_shared = shared_var > 0 ? ind_var / shared_var : NaN
                d = first(ind_data).dimension
                println(io, "  $(target_name) d=$d K=$K: " *
                    "VR_coupled=$(round(vr_coupled; digits=3)) " *
                    "VR_shared_noise=$(round(vr_shared; digits=3))")
            end
        end

        if !isempty(contrast_rows)
            println(io)
            println(io, "CRN Contrast Results")
            println(io, "-" ^ 40)
            any_vr_gt_1 = false
            for target_name in unique(r.target for r in contrast_rows)
                for K in unique(r.K for r in
                        filter(r -> r.target == target_name, contrast_rows))
                    for arm in ["coupled", "shared-noise"]
                        arm_data = filter(r -> r.target == target_name &&
                            r.K == K && r.arm == arm, contrast_rows)
                        isempty(arm_data) && continue
                        valid_vr = filter(r -> isfinite(r.vr_vs_independent),
                            arm_data)
                        if !isempty(valid_vr)
                            med_vr = median(r.vr_vs_independent for r in valid_vr)
                            mean_vr = mean(r.vr_vs_independent for r in valid_vr)
                            d = first(arm_data).dimension
                            println(io, "  $(target_name) d=$d K=$K $(arm): " *
                                "median_VR=$(round(med_vr; digits=3)) " *
                                "mean_VR=$(round(mean_vr; digits=3))")
                            med_vr > 1.0 && (any_vr_gt_1 = true)
                        end
                    end

                    coupled_data = filter(r -> r.target == target_name &&
                        r.K == K && r.arm == "coupled", contrast_rows)
                    shared_data = filter(r -> r.target == target_name &&
                        r.K == K && r.arm == "shared-noise", contrast_rows)
                    if !isempty(coupled_data) && !isempty(shared_data)
                        coupled_var = mean(r.contrast_var_mean for r in coupled_data)
                        shared_var = mean(r.contrast_var_mean for r in shared_data)
                        vr_mechanism = shared_var > 1e-30 ?
                            coupled_var / shared_var : NaN
                        d = first(coupled_data).dimension
                        println(io, "  $(target_name) d=$d K=$K " *
                            "VR_mechanism(coupled/shared_noise)=" *
                            "$(round(vr_mechanism; digits=3))")
                    end
                end
            end

            println(io)
            if !any_vr_gt_1
                println(io, "HONESTY NOTE: No variance reduction observed " *
                    "for CRN contrasts in any tested configuration. " *
                    "The transport mechanism did not reduce contrast " *
                    "variance beyond what shared noise provides.")
            else
                println(io, "Variance reduction observed in some CRN " *
                    "contrast configurations. See per-configuration " *
                    "results above for details.")
            end
        end

        if !isempty(meeting_rows)
            println(io)
            println(io, "Coupling-Quality Diagnostics (K=2)")
            println(io, "-" ^ 40)
            println(io, "NOTE: Exact coalescence is not expected for multi-marginal")
            println(io, "transport HMC because multinomial trajectory selection is")
            println(io, "independent per chain. The coupling-quality metrics measure")
            println(io, "how tightly chains co-move, not whether they merge.")
            println(io)
            for target_name in unique(r.target for r in meeting_rows)
                t_rows = filter(r -> r.target == target_name, meeting_rows)
                d = first(t_rows).dimension
                met_count = count(r -> r.met_tol_1, t_rows)
                med_min = median(r.min_distance for r in t_rows)
                mean_min = mean(r.min_distance for r in t_rows)
                med_corr = median(r.correlation_x1 for r in t_rows)
                println(io, "  $(target_name) d=$d:")
                println(io, "    min_distance: median=$(round(med_min; sigdigits=3))" *
                    " mean=$(round(mean_min; sigdigits=3))")
                println(io, "    within tolerance 1.0: $(met_count)/$(length(t_rows))")
                println(io, "    correlation_x1: median=$(round(med_corr; sigdigits=3))")
            end
        end
    end
    println("wrote $path")
end

# --- Main ---

function main()
    println("Multi-Marginal Transport HMC Benchmark")
    println("Mode: $(DEV_MODE ? "development (--dev)" : "full")")
    println("Protocol: $(CHAIN_COUNT) replicates × " *
        "$(WARMUP) warmup + $(RETAINED) retained draws")
    println("K values: $(join(K_VALUES, ", "))")
    println("BLAS threads: $BLAS_THREADS")
    println()

    targets = benchmark_targets()
    println("Targets: $(join(["$(t.name) (d=$(t.dimension))" for t in targets], ", "))")

    float32_validation()

    pooled_rows = run_pooled_benchmark(targets)
    contrast_rows = run_contrast_benchmark(targets)
    meeting_rows = run_coupling_diagnostics(targets)

    mkpath(RESULTS_DIR)
    write_csv(joinpath(RESULTS_DIR, "pooled_diagnostics.csv"), pooled_rows)
    write_csv(joinpath(RESULTS_DIR, "contrast_diagnostics.csv"), contrast_rows)
    write_csv(joinpath(RESULTS_DIR, "meeting_times.csv"), meeting_rows)
    write_metadata()
    write_summary(pooled_rows, contrast_rows, meeting_rows)

    println("\nBenchmark complete.")
end

main()
