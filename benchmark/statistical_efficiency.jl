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
const SEEDS = [4109 + i for i in 0:(CHAIN_COUNT - 1)]
const SKETCH_RANKS = DEV_MODE ? [5, 10] : [5, 10, 20]
const LEAPFROG_STEPS = 10
const MULTI_MARGINAL_K_VALUES = [2, 4]
const MEETING_TRIALS = DEV_MODE ? 20 : 100
const MEETING_HORIZON = 1000
const SKETCH_REGULARIZATION = 1.0

const RESULTS_DIR = joinpath(@__DIR__, "results", "statistical_efficiency")

struct BenchmarkTarget
    name::String
    dimension::Int
    logdensity::Function
    potential_gradient::Function
    true_mean::Vector{Float64}
    true_variance::Vector{Float64}
    mala_step_size::Float64
    hmc_step_size::Float64
    sketch_step_size::Float64
end

function benchmark_targets()
    targets = BenchmarkTarget[]
    if DEV_MODE
        for d in [10]
            suite = Evaluation.standard_targets(d)
            iso = suite[1]
            push!(targets, BenchmarkTarget("isotropic-gaussian", d,
                iso.logdensity, iso.gradient, iso.mean, iso.variance,
                0.4, 0.15, 0.3))
            corr = suite[2]
            push!(targets, BenchmarkTarget("correlated-gaussian", d,
                corr.logdensity, corr.gradient, corr.mean, corr.variance,
                0.25, 0.10, 0.2))
        end
    else
        suite10 = Evaluation.standard_targets(10)
        iso = suite10[1]
        push!(targets, BenchmarkTarget("isotropic-gaussian", 10,
            iso.logdensity, iso.gradient, iso.mean, iso.variance,
            0.4, 0.15, 0.3))
        suite50 = Evaluation.standard_targets(50)
        corr = suite50[2]
        push!(targets, BenchmarkTarget("correlated-gaussian", 50,
            corr.logdensity, corr.gradient, corr.mean, corr.variance,
            0.15, 0.08, 0.12))
        suite100 = Evaluation.standard_targets(100)
        ill = suite100[4]
        push!(targets, BenchmarkTarget("ill-conditioned-gaussian", 100,
            ill.logdensity, ill.gradient, ill.mean, ill.variance,
            0.08, 0.05, 0.06))
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

function make_sketch_counter(sketch_fn, rank)
    probe_count = Ref(0)
    counted_sketch = function(q)
        probe_count[] += rank
        sketch_fn(q)
    end
    counted_sketch, probe_count
end

function random_sketch(d::Int, M::Int, seed::Int)
    rng = MersenneTwister(seed + 999)
    S = randn(rng, M, d) / sqrt(M)
    q -> S .* one(eltype(q))
end

function conformance_gate_active_sketch(target, sketch, step_size, regularization)
    d = target.dimension
    rng = MersenneTwister(77777)
    events = Runtime.FloatTraceEvent[]
    for _ in 1:d
        push!(events, Runtime.NormalEvent(randn(rng)))
    end
    push!(events, Runtime.UniformEvent(rand(rng)))
    position = 0.1 .* randn(rng, d)
    score = q -> -(target.potential_gradient(q))
    result = Evaluation.replay_pair(events,
        source -> Reference.active_sketch_smmala_step!(source,
            target.logdensity, score, sketch,
            Float64(step_size), Float64(regularization), Float64.(position)),
        source -> Optimized.active_sketch_smmala_step!(source,
            target.logdensity, score, sketch,
            step_size, regularization, position))
    if !Evaluation.conforms_numerical(result; atol=1e-10)
        println("  WARNING: conformance gate FAILED")
        return false
    end
    true
end

function run_active_sketch_chain(target, sketch, sketch_rank::Int,
        step_size::T, regularization::T, seed::Int) where {T<:AbstractFloat}
    d = target.dimension
    counted_log, counted_score, log_count, grad_count =
        make_counters(target.logdensity, q -> -(target.potential_gradient(q)))
    counted_sketch, probe_count = make_sketch_counter(sketch, sketch_rank)

    workspace = Optimized.prepare_active_sketch_smmala_workspace(d, sketch_rank, T)
    source = Runtime.RNGSource(MersenneTwister(seed))
    position = zeros(T, d)
    chain = Matrix{T}(undef, d, TOTAL_DRAWS)
    accepts = 0
    for i in 1:TOTAL_DRAWS
        old_position = copy(position)
        result = Optimized.active_sketch_smmala_step!(source,
            counted_log, counted_score, counted_sketch,
            step_size, regularization, position, workspace)
        position = T.(result)
        if position != old_position
            accepts += 1
        end
        chain[:, i] = position
    end
    acceptance = accepts / TOTAL_DRAWS
    retained = chain[:, (WARMUP + 1):end]
    (; retained, acceptance, grad_count=grad_count[], probe_count=probe_count[],
        log_count=log_count[])
end

function run_mala_chain(target, step_size::T, seed::Int) where {T<:AbstractFloat}
    d = target.dimension
    counted_log, counted_score, log_count, grad_count =
        make_counters(target.logdensity, q -> -(target.potential_gradient(q)))

    workspace = Optimized.prepare_mala_workspace(zeros(T, d))
    source = Runtime.RNGSource(MersenneTwister(seed))
    position = zeros(T, d)
    chain = Matrix{T}(undef, d, TOTAL_DRAWS)
    accepts = 0
    for i in 1:TOTAL_DRAWS
        old_position = copy(position)
        result = Optimized.vector_mala_step!(source,
            counted_log, counted_score, step_size, position, workspace)
        position = T.(result)
        if position != old_position
            accepts += 1
        end
        chain[:, i] = position
    end
    acceptance = accepts / TOTAL_DRAWS
    retained = chain[:, (WARMUP + 1):end]
    (; retained, acceptance, grad_count=grad_count[], probe_count=0,
        log_count=log_count[])
end

function run_multinomial_hmc_chain(target, step_size::T, steps::Int,
        seed::Int) where {T<:AbstractFloat}
    d = target.dimension
    counted_log, counted_grad, log_count, grad_count =
        make_counters(target.logdensity, target.potential_gradient)

    source = Runtime.RNGSource(MersenneTwister(seed))
    position = zeros(T, d)
    chain = Matrix{T}(undef, d, TOTAL_DRAWS)
    accepts = 0
    for i in 1:TOTAL_DRAWS
        new_position = Optimized.multinomial_hmc_step!(source,
            counted_log, counted_grad, step_size, steps, position)
        if new_position != position
            accepts += 1
        end
        position = new_position
        chain[:, i] = position
    end
    acceptance = accepts / TOTAL_DRAWS
    retained = chain[:, (WARMUP + 1):end]
    (; retained, acceptance, grad_count=grad_count[], probe_count=0,
        log_count=log_count[])
end

function compute_diagnostics(chains::Vector{<:AbstractMatrix{T}}) where {T}
    d = size(first(chains), 1)
    n_chains = length(chains)
    n_draws = minimum(size(c, 2) for c in chains)
    samples = Array{T,3}(undef, n_draws, n_chains, d)
    for (c, chain) in enumerate(chains)
        for p in 1:d
            samples[:, c, p] = chain[p, 1:n_draws]
        end
    end
    bulk = ess_rhat(samples; kind=:bulk)
    tail = ess_rhat(samples; kind=:tail)
    mcse_vals = mcse(samples; kind=mean)
    (; min_bulk_ess=minimum(bulk.ess), min_tail_ess=minimum(tail.ess),
        max_rhat=maximum(bulk.rhat),
        median_bulk_ess=median(bulk.ess), median_tail_ess=median(tail.ess),
        max_mcse=maximum(mcse_vals),
        bulk_ess_per_param=bulk.ess, tail_ess_per_param=tail.ess,
        rhat_per_param=bulk.rhat)
end

function run_active_sketch_benchmark(targets)
    println("\n=== Active-Sketch sMMALA Benchmark ===\n")
    rows = NamedTuple[]

    for target in targets
        d = target.dimension
        println("[active-sketch] target=$(target.name) d=$d")

        for rank in SKETCH_RANKS
            if rank >= d
                println("  skipping rank=$rank >= d=$d")
                continue
            end
            sketch = random_sketch(d, rank, 12345)
            step_size = target.sketch_step_size
            reg = SKETCH_REGULARIZATION

            print("  rank=$rank: conformance... ")
            if !conformance_gate_active_sketch(target, sketch, step_size, reg)
                println("FAILED — skipping")
                continue
            end
            println("passed")

            print("  running $CHAIN_COUNT chains... ")
            GC.gc()
            t0 = time_ns()
            results = [run_active_sketch_chain(target, sketch, rank,
                step_size, reg, seed) for seed in SEEDS]
            wall_seconds = (time_ns() - t0) / 1e9
            println("$(round(wall_seconds; digits=1))s")

            chains = [r.retained for r in results]
            diag = compute_diagnostics(chains)
            total_grads = sum(r.grad_count for r in results)
            total_probes = sum(r.probe_count for r in results)
            acceptance = mean(r.acceptance for r in results)

            push!(rows, (target=target.name, dimension=d,
                method="active-sketch-smmala", rank=rank,
                step_size=step_size, regularization=reg,
                chains=CHAIN_COUNT, warmup=WARMUP, retained=RETAINED,
                min_bulk_ess=diag.min_bulk_ess,
                min_tail_ess=diag.min_tail_ess,
                max_rhat=diag.max_rhat,
                median_bulk_ess=diag.median_bulk_ess,
                max_mcse=diag.max_mcse,
                acceptance_rate=acceptance,
                gradient_count=total_grads,
                probe_count=total_probes,
                ess_per_gradient=diag.min_bulk_ess / total_grads,
                ess_per_gradient_probe=diag.min_bulk_ess /
                    (total_grads + total_probes),
                ess_per_second=diag.min_bulk_ess / wall_seconds,
                wall_seconds=wall_seconds))
            println("    bulk_ess=$(round(diag.min_bulk_ess; digits=1)) " *
                "tail_ess=$(round(diag.min_tail_ess; digits=1)) " *
                "rhat=$(round(diag.max_rhat; digits=4)) " *
                "accept=$(round(acceptance; digits=3)) " *
                "ESS/grad=$(round(diag.min_bulk_ess / total_grads; sigdigits=3))")
        end

        print("  MALA baseline: running... ")
        GC.gc()
        t0 = time_ns()
        mala_results = [run_mala_chain(target, target.mala_step_size,
            seed) for seed in SEEDS]
        wall_seconds = (time_ns() - t0) / 1e9
        println("$(round(wall_seconds; digits=1))s")

        mala_chains = [r.retained for r in mala_results]
        mala_diag = compute_diagnostics(mala_chains)
        mala_total_grads = sum(r.grad_count for r in mala_results)
        mala_acceptance = mean(r.acceptance for r in mala_results)
        push!(rows, (target=target.name, dimension=d,
            method="mala", rank=0,
            step_size=target.mala_step_size,
            regularization=0.0,
            chains=CHAIN_COUNT, warmup=WARMUP, retained=RETAINED,
            min_bulk_ess=mala_diag.min_bulk_ess,
            min_tail_ess=mala_diag.min_tail_ess,
            max_rhat=mala_diag.max_rhat,
            median_bulk_ess=mala_diag.median_bulk_ess,
            max_mcse=mala_diag.max_mcse,
            acceptance_rate=mala_acceptance,
            gradient_count=mala_total_grads,
            probe_count=0,
            ess_per_gradient=mala_diag.min_bulk_ess / mala_total_grads,
            ess_per_gradient_probe=mala_diag.min_bulk_ess / mala_total_grads,
            ess_per_second=mala_diag.min_bulk_ess / wall_seconds,
            wall_seconds=wall_seconds))
        println("    bulk_ess=$(round(mala_diag.min_bulk_ess; digits=1)) " *
            "tail_ess=$(round(mala_diag.min_tail_ess; digits=1)) " *
            "rhat=$(round(mala_diag.max_rhat; digits=4)) " *
            "accept=$(round(mala_acceptance; digits=3)) " *
            "ESS/grad=$(round(mala_diag.min_bulk_ess / mala_total_grads; sigdigits=3))")

        print("  HMC baseline: running... ")
        GC.gc()
        t0 = time_ns()
        hmc_results = [run_multinomial_hmc_chain(target, target.hmc_step_size,
            LEAPFROG_STEPS, seed) for seed in SEEDS]
        wall_seconds = (time_ns() - t0) / 1e9
        println("$(round(wall_seconds; digits=1))s")

        hmc_chains = [r.retained for r in hmc_results]
        hmc_diag = compute_diagnostics(hmc_chains)
        hmc_total_grads = sum(r.grad_count for r in hmc_results)
        hmc_acceptance = mean(r.acceptance for r in hmc_results)
        push!(rows, (target=target.name, dimension=d,
            method="multinomial-hmc", rank=0,
            step_size=target.hmc_step_size,
            regularization=0.0,
            chains=CHAIN_COUNT, warmup=WARMUP, retained=RETAINED,
            min_bulk_ess=hmc_diag.min_bulk_ess,
            min_tail_ess=hmc_diag.min_tail_ess,
            max_rhat=hmc_diag.max_rhat,
            median_bulk_ess=hmc_diag.median_bulk_ess,
            max_mcse=hmc_diag.max_mcse,
            acceptance_rate=hmc_acceptance,
            gradient_count=hmc_total_grads,
            probe_count=0,
            ess_per_gradient=hmc_diag.min_bulk_ess / hmc_total_grads,
            ess_per_gradient_probe=hmc_diag.min_bulk_ess / hmc_total_grads,
            ess_per_second=hmc_diag.min_bulk_ess / wall_seconds,
            wall_seconds=wall_seconds))
        println("    bulk_ess=$(round(hmc_diag.min_bulk_ess; digits=1)) " *
            "tail_ess=$(round(hmc_diag.min_tail_ess; digits=1)) " *
            "rhat=$(round(hmc_diag.max_rhat; digits=4)) " *
            "accept=$(round(hmc_acceptance; digits=3)) " *
            "ESS/grad=$(round(hmc_diag.min_bulk_ess / hmc_total_grads; sigdigits=3))")
    end
    rows
end

function run_multi_marginal_chains(target, K::Int, step_size::Float64,
        steps::Int, seed::Int)
    d = target.dimension
    counted_log, counted_grad, log_count, grad_count =
        make_counters(target.logdensity, target.potential_gradient)

    coupled_flat = zeros(K * d)
    coupled_samples = Matrix{Float64}(undef, K * d, TOTAL_DRAWS)
    rng_coupled = MersenneTwister(seed)

    for i in 1:TOTAL_DRAWS
        coupled_flat = Reference.multi_marginal_transport_hmc_step!(
            Runtime.RNGSource(rng_coupled), counted_log, counted_grad,
            step_size, steps, K, coupled_flat)
        coupled_samples[:, i] = coupled_flat
    end

    coupled_retained = coupled_samples[:, (WARMUP + 1):end]
    (; coupled_retained, grad_count=grad_count[], log_count=log_count[])
end

function run_independent_chains(target, K::Int, step_size::Float64,
        steps::Int, seed::Int)
    d = target.dimension
    independent_chains = [zeros(d) for _ in 1:K]
    independent_samples = Matrix{Float64}(undef, K * d, TOTAL_DRAWS)
    rng = MersenneTwister(seed)

    grad_total = 0
    for i in 1:TOTAL_DRAWS
        for k in 1:K
            counted_log, counted_grad, _, gc =
                make_counters(target.logdensity, target.potential_gradient)
            independent_chains[k] = Reference.multinomial_hmc_step!(
                Runtime.RNGSource(rng), counted_log, counted_grad,
                step_size, steps, independent_chains[k])
            grad_total += gc[]
        end
        for k in 1:K
            offset = (k - 1) * d
            independent_samples[offset+1:offset+d, i] = independent_chains[k]
        end
    end

    independent_retained = independent_samples[:, (WARMUP + 1):end]
    (; independent_retained, grad_count=grad_total)
end

function compute_per_chain_diagnostics(samples::AbstractMatrix{Float64},
        K::Int, d::Int)
    n = size(samples, 2)
    results = NamedTuple[]
    for k in 1:K
        offset = (k - 1) * d
        chain_data = samples[offset+1:offset+d, :]
        arr = Array{Float64,3}(undef, n, 1, d)
        for p in 1:d
            arr[:, 1, p] = chain_data[p, :]
        end
        bulk = ess_rhat(arr; kind=:bulk)
        tail = ess_rhat(arr; kind=:tail)
        push!(results, (chain=k,
            min_bulk_ess=minimum(bulk.ess),
            min_tail_ess=minimum(tail.ess)))
    end
    results
end

function run_meeting_times(target, step_size::Float64, steps::Int,
        base_seed::UInt64)
    d = target.dimension
    meeting_times = Union{Nothing,Int}[]

    for trial in 1:MEETING_TRIALS
        rng = MersenneTwister(base_seed + UInt64(trial))
        pos = zeros(2 * d)
        pos[1:d] .= 0.5 .* randn(rng, d)
        pos[d+1:2*d] .= 0.5 .* randn(rng, d)
        met = nothing
        for t in 1:MEETING_HORIZON
            pos = Reference.multi_marginal_transport_hmc_step!(
                Runtime.RNGSource(rng), target.logdensity,
                target.potential_gradient, step_size, steps, 2, pos)
            if pos[1:d] ≈ pos[d+1:2*d]
                met = t
                break
            end
        end
        push!(meeting_times, met)
    end
    meeting_times
end

function run_multi_marginal_benchmark(targets)
    println("\n=== Multi-Marginal Transport HMC Benchmark ===\n")
    diag_rows = NamedTuple[]
    meeting_rows = NamedTuple[]

    for target in targets
        d = target.dimension
        step_size = target.hmc_step_size

        for K in MULTI_MARGINAL_K_VALUES
            println("[multi-marginal] target=$(target.name) d=$d K=$K")

            print("  coupled chains: ")
            GC.gc()
            t0 = time_ns()
            coupled_runs = [run_multi_marginal_chains(target, K,
                step_size, LEAPFROG_STEPS, seed) for seed in SEEDS]
            coupled_wall = (time_ns() - t0) / 1e9
            println("$(round(coupled_wall; digits=1))s")

            print("  independent chains: ")
            GC.gc()
            t0 = time_ns()
            independent_runs = [run_independent_chains(target, K,
                step_size, LEAPFROG_STEPS, seed) for seed in SEEDS]
            independent_wall = (time_ns() - t0) / 1e9
            println("$(round(independent_wall; digits=1))s")

            coupled_grads = sum(r.grad_count for r in coupled_runs)
            independent_grads = sum(r.grad_count for r in independent_runs)

            for k in 1:K
                offset = (k - 1) * d
                coupled_chain_data = [r.coupled_retained[offset+1:offset+d, :]
                    for r in coupled_runs]
                coupled_diag = compute_diagnostics(coupled_chain_data)

                independent_chain_data = [r.independent_retained[offset+1:offset+d, :]
                    for r in independent_runs]
                independent_diag = compute_diagnostics(independent_chain_data)

                coupled_var = vec(var(hcat(coupled_chain_data...); dims=2))
                independent_var = vec(var(hcat(independent_chain_data...); dims=2))
                vr = independent_var ./ max.(coupled_var, 1e-30)

                push!(diag_rows, (target=target.name, dimension=d,
                    K=K, chain_index=k,
                    step_size=step_size, leapfrog_steps=LEAPFROG_STEPS,
                    chains=CHAIN_COUNT, warmup=WARMUP, retained=RETAINED,
                    coupled_min_bulk_ess=coupled_diag.min_bulk_ess,
                    coupled_min_tail_ess=coupled_diag.min_tail_ess,
                    coupled_max_rhat=coupled_diag.max_rhat,
                    independent_min_bulk_ess=independent_diag.min_bulk_ess,
                    independent_min_tail_ess=independent_diag.min_tail_ess,
                    independent_max_rhat=independent_diag.max_rhat,
                    median_variance_reduction=median(vr),
                    mean_variance_reduction=mean(vr),
                    coupled_ess_per_gradient=coupled_diag.min_bulk_ess /
                        coupled_grads,
                    independent_ess_per_gradient=independent_diag.min_bulk_ess /
                        independent_grads))
                println("  chain $k: coupled_ess=$(round(coupled_diag.min_bulk_ess; digits=1)) " *
                    "ind_ess=$(round(independent_diag.min_bulk_ess; digits=1)) " *
                    "VR=$(round(median(vr); digits=3))")
            end

            coupled_flat_data = [r.coupled_retained for r in coupled_runs]
            for i in 1:K
                for j in (i+1):K
                    offset_i = (i - 1) * d
                    offset_j = (j - 1) * d
                    all_corrs = Float64[]
                    for r in coupled_runs
                        for c in 1:d
                            ci = r.coupled_retained[offset_i + c, :]
                            cj = r.coupled_retained[offset_j + c, :]
                            if std(ci) > 1e-10 && std(cj) > 1e-10
                                push!(all_corrs, cor(ci, cj))
                            end
                        end
                    end
                    if !isempty(all_corrs)
                        println("  pairwise correlation chains ($i,$j): " *
                            "median=$(round(median(all_corrs); digits=4))")
                    end
                end
            end

            if K == 2
                print("  meeting times: ")
                mt = run_meeting_times(target, step_size, LEAPFROG_STEPS,
                    UInt64(42))
                met_count = count(!isnothing, mt)
                println("$met_count/$(length(mt)) met within horizon")
                observed = filter(!isnothing, mt)
                for (idx, tau) in enumerate(mt)
                    push!(meeting_rows, (target=target.name, dimension=d,
                        trial=idx, meeting_time=something(tau, -1),
                        met=!isnothing(tau)))
                end
                if !isempty(observed)
                    println("    median=$(median(observed)) " *
                        "mean=$(round(mean(observed); digits=1)) " *
                        "max=$(maximum(observed))")
                end
            end
        end
    end
    diag_rows, meeting_rows
end

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
        readchomp(`git -C $(joinpath(@__DIR__, "..")) rev-parse --short HEAD`)
    catch
        "unknown"
    end
    dirty = try
        output = readchomp(`git -C $(joinpath(@__DIR__, "..")) status --porcelain`)
        isempty(output) ? "" : "-dirty"
    catch
        ""
    end
    hostname = try
        readchomp(`hostname`)
    catch
        "unknown"
    end
    open(path, "w") do io
        println(io, "key,value")
        println(io, "commit,$(commit)$(dirty)")
        println(io, "julia_version,$VERSION")
        println(io, "julia_git,$(Base.GIT_VERSION_INFO.commit_short)")
        println(io, "blas_config,$(LinearAlgebra.BLAS.get_config())")
        println(io, "hostname,$hostname")
        println(io, "cpu,$(Sys.cpu_info()[1].model)")
        println(io, "threads,$(Threads.nthreads())")
        println(io, "blas_threads,$BLAS_THREADS")
        println(io, "dev_mode,$DEV_MODE")
        println(io, "chain_count,$CHAIN_COUNT")
        println(io, "warmup,$WARMUP")
        println(io, "retained,$RETAINED")
        println(io, "sketch_ranks,$(join(SKETCH_RANKS, ';'))")
        println(io, "sketch_regularization,$SKETCH_REGULARIZATION")
        println(io, "leapfrog_steps,$LEAPFROG_STEPS")
        println(io, "multi_marginal_K,$(join(MULTI_MARGINAL_K_VALUES, ';'))")
        println(io, "meeting_trials,$MEETING_TRIALS")
        println(io, "meeting_horizon,$MEETING_HORIZON")
        println(io, "mcmc_diagnostic_tools_version,$(pkgversion(MCMCDiagnosticTools))")
    end
    println("wrote $path")
end

function write_summary(sketch_rows, mm_diag_rows, mm_meeting_rows)
    mkpath(RESULTS_DIR)
    path = joinpath(RESULTS_DIR, "summary.txt")
    open(path, "w") do io
        println(io, "Statistical-Efficiency Benchmark Summary")
        println(io, "=" ^ 50)
        println(io, "Mode: $(DEV_MODE ? "development (--dev)" : "full")")
        println(io, "Date: $(Dates.now())")
        println(io, "Chains: $CHAIN_COUNT, Warmup: $WARMUP, Retained: $RETAINED")
        println(io)

        println(io, "Active-Sketch sMMALA Results")
        println(io, "-" ^ 40)
        for row in sketch_rows
            println(io, "  $(row.target) d=$(row.dimension) " *
                "$(row.method) rank=$(row.rank): " *
                "bulk_ESS=$(round(row.min_bulk_ess; digits=1)) " *
                "tail_ESS=$(round(row.min_tail_ess; digits=1)) " *
                "Rhat=$(round(row.max_rhat; digits=4)) " *
                "accept=$(round(row.acceptance_rate; digits=3)) " *
                "ESS/grad=$(round(row.ess_per_gradient; sigdigits=3)) " *
                "ESS/(grad+probe)=$(round(row.ess_per_gradient_probe; sigdigits=3))")
        end

        sketch_only = filter(r -> r.method == "active-sketch-smmala", sketch_rows)
        mala_rows = filter(r -> r.method == "mala", sketch_rows)
        hmc_rows_s = filter(r -> r.method == "multinomial-hmc", sketch_rows)

        println(io)
        println(io, "Key Finding: Active-Sketch Competitive Regime")
        println(io, "-" ^ 40)
        if !isempty(sketch_only) && !isempty(mala_rows)
            for target_name in unique(r.target for r in sketch_rows)
                t_sketch = filter(r -> r.target == target_name &&
                    r.method == "active-sketch-smmala", sketch_rows)
                t_mala = filter(r -> r.target == target_name &&
                    r.method == "mala", sketch_rows)
                t_hmc = filter(r -> r.target == target_name &&
                    r.method == "multinomial-hmc", sketch_rows)

                if !isempty(t_sketch) && !isempty(t_mala)
                    best_sketch = argmax(r -> r.ess_per_gradient_probe, t_sketch)
                    mala_eff = first(t_mala).ess_per_gradient
                    hmc_eff = isempty(t_hmc) ? NaN :
                        first(t_hmc).ess_per_gradient
                    ratio_mala = best_sketch.ess_per_gradient_probe / mala_eff
                    println(io, "  $(target_name): best sketch " *
                        "(rank=$(best_sketch.rank)) ESS/(grad+probe) " *
                        "= $(round(best_sketch.ess_per_gradient_probe; sigdigits=3)) " *
                        "vs MALA ESS/grad = $(round(mala_eff; sigdigits=3)) " *
                        "(ratio=$(round(ratio_mala; digits=2)))")
                    if isfinite(hmc_eff)
                        ratio_hmc = best_sketch.ess_per_gradient_probe / hmc_eff
                        println(io, "    vs HMC ESS/grad = " *
                            "$(round(hmc_eff; sigdigits=3)) " *
                            "(ratio=$(round(ratio_hmc; digits=2)))")
                    end
                end
            end
        end

        println(io)
        println(io, "Multi-Marginal Transport HMC Results")
        println(io, "-" ^ 40)
        for row in mm_diag_rows
            println(io, "  $(row.target) d=$(row.dimension) K=$(row.K) " *
                "chain=$(row.chain_index): " *
                "coupled_ESS=$(round(row.coupled_min_bulk_ess; digits=1)) " *
                "ind_ESS=$(round(row.independent_min_bulk_ess; digits=1)) " *
                "VR=$(round(row.median_variance_reduction; digits=3))")
        end

        if !isempty(mm_meeting_rows)
            println(io)
            println(io, "Meeting Times (K=2)")
            println(io, "-" ^ 40)
            for target_name in unique(r.target for r in mm_meeting_rows)
                t_rows = filter(r -> r.target == target_name, mm_meeting_rows)
                met = filter(r -> r.met, t_rows)
                println(io, "  $(target_name): $(length(met))/$(length(t_rows)) met")
                if !isempty(met)
                    times = [r.meeting_time for r in met]
                    println(io, "    median=$(median(times)) " *
                        "mean=$(round(mean(times); digits=1)) " *
                        "max=$(maximum(times))")
                end
            end
        end
    end
    println("wrote $path")
end

function main()
    println("Statistical-Efficiency Benchmark")
    println("Mode: $(DEV_MODE ? "development (--dev)" : "full")")
    println("Protocol: $(CHAIN_COUNT) chains × " *
        "$(WARMUP) warmup + $(RETAINED) retained draws")
    println("BLAS threads: $BLAS_THREADS")
    println()

    targets = benchmark_targets()
    println("Targets: $(join(["$(t.name) (d=$(t.dimension))" for t in targets], ", "))")

    print("\nFloat32 type validation: ")
    f32_target = first(targets)
    f32_sketch = random_sketch(f32_target.dimension, min(5, f32_target.dimension - 1), 99)
    f32_result = run_active_sketch_chain(f32_target, f32_sketch,
        min(5, f32_target.dimension - 1),
        Float32(f32_target.sketch_step_size), Float32(SKETCH_REGULARIZATION),
        SEEDS[1])
    @assert eltype(f32_result.retained) === Float32 "Float32 chain type check failed"
    println("passed (eltype=$(eltype(f32_result.retained)))")

    sketch_rows = run_active_sketch_benchmark(targets)
    mm_diag_rows, mm_meeting_rows = run_multi_marginal_benchmark(targets)

    mkpath(RESULTS_DIR)
    write_csv(joinpath(RESULTS_DIR, "active_sketch_diagnostics.csv"), sketch_rows)
    write_csv(joinpath(RESULTS_DIR, "multi_marginal_diagnostics.csv"), mm_diag_rows)
    write_csv(joinpath(RESULTS_DIR, "multi_marginal_meeting_times.csv"), mm_meeting_rows)
    write_metadata()

    write_summary(sketch_rows, mm_diag_rows, mm_meeting_rows)

    println("\nBenchmark complete.")
end

main()
