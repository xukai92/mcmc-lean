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
const SEEDS = [42001 + i for i in 0:(CHAIN_COUNT - 1)]
const SKETCH_RANKS = DEV_MODE ? [5, 10] : [5, 10, 20]
const LEAPFROG_STEPS = 10
const SKETCH_REGULARIZATION = 1.0

const RESULTS_DIR = joinpath(@__DIR__, "results", "active_sketch")

struct BenchmarkTarget
    name::String
    dimension::Int
    logdensity::Function
    score::Function
    potential_gradient::Function
    true_mean::Vector{Float64}
    true_variance::Vector{Float64}
    metric::Function
    metric_derivative::Function
    sketch_step_size::Float64
    mala_step_size::Float64
    hmc_step_size::Float64
    pmala_step_size::Float64
end

function funnel_logdensity(θ::AbstractVector{T}) where {T}
    d = length(θ)
    v = θ[1]
    lp = -v^2 / T(18)
    exp_neg_v = exp(-v)
    tail_sum = zero(T)
    @inbounds for i in 2:d
        tail_sum += θ[i]^2
    end
    lp -= T(d - 1) * v / T(2) + exp_neg_v * tail_sum / T(2)
    lp
end

function funnel_score(θ::AbstractVector{T}) where {T}
    d = length(θ)
    g = Vector{T}(undef, d)
    v = θ[1]
    exp_neg_v = exp(-v)
    tail_sum = zero(T)
    @inbounds for i in 2:d
        tail_sum += θ[i]^2
    end
    g[1] = -v / T(9) - T(d - 1) / T(2) + exp_neg_v * tail_sum / T(2)
    @inbounds for i in 2:d
        g[i] = -θ[i] * exp_neg_v
    end
    g
end

function funnel_metric(θ::AbstractVector{T}) where {T}
    d = length(θ)
    G = zeros(T, d, d)
    G[1, 1] = one(T) / T(9)
    exp_neg_v = exp(-θ[1])
    @inbounds for i in 2:d
        G[i, i] = exp_neg_v
    end
    G
end

function funnel_metric_derivative(θ::AbstractVector{T}) where {T}
    d = length(θ)
    dG = zeros(T, d, d, d)
    exp_neg_v = exp(-θ[1])
    @inbounds for i in 2:d
        dG[i, i, 1] = -exp_neg_v
    end
    dG
end

function step_sizes_for_dimension(d::Int; funnel::Bool=false)
    base = if d <= 10
        (sketch=0.3, mala=0.4, hmc=0.15, pmala=0.3)
    elseif d <= 50
        (sketch=0.15, mala=0.15, hmc=0.08, pmala=0.15)
    else
        (sketch=0.08, mala=0.08, hmc=0.05, pmala=0.08)
    end
    scale = funnel ? 0.5 : 1.0
    (sketch=base.sketch * scale, mala=base.mala * scale,
     hmc=base.hmc * scale, pmala=base.pmala * scale)
end

function identity_metric(θ::AbstractVector{T}) where {T}
    d = length(θ)
    Matrix{T}(I, d, d)
end

function identity_metric_derivative(θ::AbstractVector{T}) where {T}
    d = length(θ)
    zeros(T, d, d, d)
end

function benchmark_targets()
    targets = BenchmarkTarget[]
    dims = DEV_MODE ? [10] : [50, 100]

    for d in dims
        suite = Evaluation.standard_targets(d)
        ss = step_sizes_for_dimension(d)

        iso = suite[1]
        push!(targets, BenchmarkTarget("isotropic-gaussian", d,
            iso.logdensity, q -> -(iso.gradient(q)), iso.gradient,
            iso.mean, iso.variance,
            identity_metric, identity_metric_derivative,
            ss.sketch, ss.mala, ss.hmc, ss.pmala))

        corr = suite[2]
        precision = corr.metric_mass
        push!(targets, BenchmarkTarget("correlated-gaussian", d,
            corr.logdensity, q -> -(corr.gradient(q)), corr.gradient,
            corr.mean, corr.variance,
            _ -> Float64.(precision), _ -> zeros(Float64, d, d, d),
            ss.sketch, ss.mala, ss.hmc, ss.pmala))

        ill = suite[4]
        ill_precision_vec = 1.0 ./ ill.variance
        function ill_metric(θ::AbstractVector{T}) where {T}
            G = zeros(T, length(θ), length(θ))
            @inbounds for i in eachindex(ill_precision_vec)
                G[i, i] = T(ill_precision_vec[i])
            end
            G
        end
        function ill_metric_deriv(θ::AbstractVector{T}) where {T}
            zeros(T, length(θ), length(θ), length(θ))
        end
        push!(targets, BenchmarkTarget("ill-conditioned-gaussian", d,
            ill.logdensity, q -> -(ill.gradient(q)), ill.gradient,
            ill.mean, ill.variance,
            ill_metric, ill_metric_deriv,
            ss.sketch, ss.mala, ss.hmc, ss.pmala))

        logistic = suite[5]
        push!(targets, BenchmarkTarget("regularized-logistic", d,
            logistic.logdensity, q -> -(logistic.gradient(q)),
            logistic.gradient,
            logistic.mean, logistic.variance,
            identity_metric, identity_metric_derivative,
            ss.sketch, ss.mala, ss.hmc, ss.pmala))

        ss_f = step_sizes_for_dimension(d; funnel=true)
        funnel_mean = zeros(d)
        funnel_var = Vector{Float64}(undef, d)
        funnel_var[1] = 9.0
        for i in 2:d
            funnel_var[i] = exp(9.0 / 2.0)
        end
        push!(targets, BenchmarkTarget("neals-funnel", d,
            funnel_logdensity, funnel_score,
            q -> -(funnel_score(q)),
            funnel_mean, funnel_var,
            funnel_metric, funnel_metric_derivative,
            ss_f.sketch, ss_f.mala, ss_f.hmc, ss_f.pmala))
    end
    targets
end

function make_counters(logdensity, grad_fn)
    grad_count = Ref(0)
    log_count = Ref(0)
    counted_grad = function(q)
        grad_count[] += 1
        grad_fn(q)
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
    rng = MersenneTwister(seed)
    S = randn(rng, M, d) / sqrt(M)
    q -> S .* one(eltype(q))
end

# --- Conformance gates ---

function conformance_gate_active_sketch(target, sketch, step_size, regularization)
    d = target.dimension
    rng = MersenneTwister(77777)
    events = Runtime.FloatTraceEvent[]
    for _ in 1:d
        push!(events, Runtime.NormalEvent(randn(rng)))
    end
    push!(events, Runtime.UniformEvent(rand(rng)))
    position = 0.1 .* randn(rng, d)
    result = Evaluation.replay_pair(events,
        source -> Reference.active_sketch_smmala_step!(source,
            target.logdensity, target.score, sketch,
            Float64(step_size), Float64(regularization), Float64.(position)),
        source -> Optimized.active_sketch_smmala_step!(source,
            target.logdensity, target.score, sketch,
            step_size, regularization, position))
    if !Evaluation.conforms_numerical(result; atol=1e-10)
        println("  WARNING: active-sketch conformance gate FAILED")
        return false
    end
    true
end

function conformance_gate_mala(target, step_size)
    d = target.dimension
    rng = MersenneTwister(77778)
    events = Runtime.FloatTraceEvent[]
    for _ in 1:d
        push!(events, Runtime.NormalEvent(randn(rng)))
    end
    push!(events, Runtime.UniformEvent(rand(rng)))
    position = 0.1 .* randn(rng, d)
    result = Evaluation.replay_pair(events,
        source -> Reference.vector_mala_step!(source,
            target.logdensity, target.score, Float64(step_size),
            Float64.(position)),
        source -> Optimized.vector_mala_step!(source,
            target.logdensity, target.score, step_size, position))
    if !Evaluation.conforms_numerical(result; atol=1e-10)
        println("  WARNING: MALA conformance gate FAILED")
        return false
    end
    true
end

function conformance_gate_dense_pmala(target, step_size)
    d = target.dimension
    rng = MersenneTwister(77779)
    events = Runtime.FloatTraceEvent[]
    for _ in 1:d
        push!(events, Runtime.NormalEvent(randn(rng)))
    end
    push!(events, Runtime.UniformEvent(rand(rng)))
    position = 0.1 .* randn(rng, d)
    result = Evaluation.replay_pair(events,
        source -> Reference.dense_pmala_step!(source,
            target.logdensity, target.score,
            target.metric, target.metric_derivative,
            Float64(step_size), Float64.(position)),
        source -> Optimized.dense_pmala_step!(source,
            target.logdensity, target.score,
            target.metric, target.metric_derivative,
            step_size, position))
    if !Evaluation.conforms_numerical(result; atol=1e-10)
        println("  WARNING: dense-PMALA conformance gate FAILED")
        return false
    end
    true
end

function conformance_gate_hmc(target, step_size, steps)
    d = target.dimension
    rng = MersenneTwister(77780)
    events = Runtime.FloatTraceEvent[]
    for _ in 1:d
        push!(events, Runtime.NormalEvent(randn(rng)))
    end
    push!(events, Runtime.IndexEvent(big(rand(rng, 0:(steps)))))
    push!(events, Runtime.UniformEvent(rand(rng)))
    position = 0.1 .* randn(rng, d)
    result = Evaluation.replay_pair(events,
        source -> Reference.multinomial_hmc_step!(source,
            target.logdensity, target.potential_gradient,
            Float64(step_size), steps, Float64.(position)),
        source -> Optimized.multinomial_hmc_step!(source,
            target.logdensity, target.potential_gradient,
            step_size, steps, position))
    if !Evaluation.conforms_numerical(result; atol=1e-10)
        println("  WARNING: HMC conformance gate FAILED")
        return false
    end
    true
end

# --- Chain runners ---

function run_active_sketch_chain(target, sketch, sketch_rank::Int,
        step_size::T, regularization::T, seed::Int) where {T<:AbstractFloat}
    d = target.dimension
    counted_log, counted_score, log_count, grad_count =
        make_counters(target.logdensity, target.score)
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
        make_counters(target.logdensity, target.score)

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

function run_dense_pmala_chain(target, step_size::T, seed::Int) where {T<:AbstractFloat}
    d = target.dimension
    counted_log, counted_score, log_count, grad_count =
        make_counters(target.logdensity, target.score)

    workspace = Optimized.prepare_dense_pmala_workspace(zeros(T, d))
    source = Runtime.RNGSource(MersenneTwister(seed))
    position = zeros(T, d)
    chain = Matrix{T}(undef, d, TOTAL_DRAWS)
    accepts = 0
    for i in 1:TOTAL_DRAWS
        old_position = copy(position)
        result = Optimized.dense_pmala_step!(source,
            counted_log, counted_score,
            target.metric, target.metric_derivative,
            step_size, position, workspace)
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

# --- Diagnostics ---

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

# --- Compile warmup ---

function compile_warmup!(target)
    d = target.dimension
    rng = MersenneTwister(99999)
    source = Runtime.RNGSource(rng)
    pos = zeros(d)

    sketch = random_sketch(d, min(5, d - 1), 88888)
    ws_sketch = Optimized.prepare_active_sketch_smmala_workspace(
        d, min(5, d - 1), Float64)
    for _ in 1:10
        pos = Float64.(Optimized.active_sketch_smmala_step!(source,
            target.logdensity, target.score, sketch,
            target.sketch_step_size, SKETCH_REGULARIZATION, pos, ws_sketch))
    end

    pos = zeros(d)
    ws_mala = Optimized.prepare_mala_workspace(pos)
    for _ in 1:10
        pos = Float64.(Optimized.vector_mala_step!(source,
            target.logdensity, target.score,
            target.mala_step_size, pos, ws_mala))
    end

    pos = zeros(d)
    ws_pmala = Optimized.prepare_dense_pmala_workspace(pos)
    for _ in 1:10
        pos = Float64.(Optimized.dense_pmala_step!(source,
            target.logdensity, target.score,
            target.metric, target.metric_derivative,
            target.pmala_step_size, pos, ws_pmala))
    end

    pos = zeros(d)
    for _ in 1:10
        pos = Optimized.multinomial_hmc_step!(source,
            target.logdensity, target.potential_gradient,
            target.hmc_step_size, LEAPFROG_STEPS, pos)
    end
end

# --- Main benchmark ---

function run_method!(rows, target, method_name, runner, step_size, extra_label)
    d = target.dimension
    print("  $method_name$(extra_label): running $CHAIN_COUNT chains... ")
    GC.gc()
    t0 = time_ns()
    results = [runner(seed) for seed in SEEDS]
    wall_seconds = (time_ns() - t0) / 1e9
    println("$(round(wall_seconds; digits=1))s")

    chains = [r.retained for r in results]
    diag = compute_diagnostics(chains)
    total_grads = sum(r.grad_count for r in results)
    total_probes = sum(r.probe_count for r in results)
    total_logs = sum(r.log_count for r in results)
    acceptance = mean(r.acceptance for r in results)

    rank_val = 0
    if occursin("active-sketch", method_name)
        m = match(r"rank=(\d+)", extra_label)
        rank_val = m !== nothing ? parse(Int, m[1]) : 0
    end

    ess_per_grad = total_grads > 0 ? diag.min_bulk_ess / total_grads : NaN
    ess_per_gp = (total_grads + total_probes) > 0 ?
        diag.min_bulk_ess / (total_grads + total_probes) : NaN

    push!(rows, (target=target.name, dimension=d,
        method=method_name, rank=rank_val,
        step_size=step_size,
        regularization=(occursin("sketch", method_name) ? SKETCH_REGULARIZATION : 0.0),
        chains=CHAIN_COUNT, warmup=WARMUP, retained=RETAINED,
        min_bulk_ess=diag.min_bulk_ess,
        min_tail_ess=diag.min_tail_ess,
        max_rhat=diag.max_rhat,
        median_bulk_ess=diag.median_bulk_ess,
        median_tail_ess=diag.median_tail_ess,
        max_mcse=diag.max_mcse,
        acceptance_rate=acceptance,
        gradient_count=total_grads,
        logdensity_count=total_logs,
        probe_count=total_probes,
        ess_per_gradient=ess_per_grad,
        ess_per_gradient_probe=ess_per_gp,
        ess_per_second=diag.min_bulk_ess / wall_seconds,
        wall_seconds=wall_seconds))

    rhat_flag = diag.max_rhat > 1.01 ? " (WARNING: Rhat>1.01)" : ""
    println("    bulk_ess=$(round(diag.min_bulk_ess; digits=1)) " *
        "tail_ess=$(round(diag.min_tail_ess; digits=1)) " *
        "rhat=$(round(diag.max_rhat; digits=4))$rhat_flag " *
        "accept=$(round(acceptance; digits=3)) " *
        "ESS/grad=$(round(ess_per_grad; sigdigits=3))")
end

function run_benchmark(targets)
    println("\n=== Active-Sketch sMMALA Paper Benchmark ===\n")
    rows = NamedTuple[]

    for target in targets
        d = target.dimension
        println("[target] $(target.name) d=$d")

        print("  compile warmup... ")
        compile_warmup!(target)
        println("done")

        for rank in SKETCH_RANKS
            if rank >= d
                println("  skipping sketch rank=$rank >= d=$d")
                continue
            end
            sketch = random_sketch(d, rank, 12345 + rank)
            step_size = target.sketch_step_size
            reg = SKETCH_REGULARIZATION

            print("  active-sketch rank=$rank: conformance... ")
            if !conformance_gate_active_sketch(target, sketch, step_size, reg)
                println("FAILED — skipping")
                continue
            end
            println("passed")

            runner = seed -> run_active_sketch_chain(target, sketch, rank,
                step_size, reg, seed)
            run_method!(rows, target, "active-sketch-smmala", runner,
                step_size, " rank=$rank")
        end

        print("  MALA: conformance... ")
        if conformance_gate_mala(target, target.mala_step_size)
            println("passed")
            runner = seed -> run_mala_chain(target, target.mala_step_size, seed)
            run_method!(rows, target, "mala", runner,
                target.mala_step_size, "")
        else
            println("FAILED — skipping")
        end

        print("  dense-PMALA: conformance... ")
        if conformance_gate_dense_pmala(target, target.pmala_step_size)
            println("passed")
            runner = seed -> run_dense_pmala_chain(target,
                target.pmala_step_size, seed)
            run_method!(rows, target, "dense-pmala", runner,
                target.pmala_step_size, "")
        else
            println("FAILED — skipping")
        end

        print("  HMC: conformance... ")
        if conformance_gate_hmc(target, target.hmc_step_size, LEAPFROG_STEPS)
            println("passed")
            runner = seed -> run_multinomial_hmc_chain(target,
                target.hmc_step_size, LEAPFROG_STEPS, seed)
            run_method!(rows, target, "multinomial-hmc", runner,
                target.hmc_step_size, "")
        else
            println("FAILED — skipping")
        end

        println()
    end
    rows
end

# --- Float32 validation ---

function run_float32_validation(targets)
    println("Float32 type validation")
    println("-" ^ 40)
    f32_rows = NamedTuple[]

    for target in targets
        d = target.dimension
        f32_rng = MersenneTwister(55555)
        f32_source = Runtime.RNGSource(f32_rng)

        print("  $(target.name) d=$d: ")
        f32_pos = zeros(Float32, d)
        f32_ws = Optimized.prepare_mala_workspace(f32_pos)
        f32_accepts = 0
        f64_accepts = 0
        n_check = 100

        for _ in 1:n_check
            old = copy(f32_pos)
            res = Optimized.vector_mala_step!(f32_source,
                target.logdensity, target.score,
                Float32(target.mala_step_size), f32_pos, f32_ws)
            f32_pos = Float32.(res)
            if f32_pos != old
                f32_accepts += 1
            end
        end
        @assert eltype(f32_pos) === Float32 "Float32 MALA type check failed for $(target.name)"

        f64_source = Runtime.RNGSource(MersenneTwister(55556))
        f64_pos = zeros(Float64, d)
        f64_ws = Optimized.prepare_mala_workspace(f64_pos)
        for _ in 1:n_check
            old = copy(f64_pos)
            res = Optimized.vector_mala_step!(f64_source,
                target.logdensity, target.score,
                target.mala_step_size, f64_pos, f64_ws)
            f64_pos = Float64.(res)
            if f64_pos != old
                f64_accepts += 1
            end
        end

        sketch_rank = min(5, d - 1)
        sketch = random_sketch(d, sketch_rank, 99)
        f32_sketch_pos = zeros(Float32, d)
        f32_sketch_ws = Optimized.prepare_active_sketch_smmala_workspace(
            d, sketch_rank, Float32)
        f32_sketch_source = Runtime.RNGSource(MersenneTwister(55557))
        f32_sketch_accepts = 0
        for _ in 1:n_check
            old = copy(f32_sketch_pos)
            res = Optimized.active_sketch_smmala_step!(f32_sketch_source,
                target.logdensity, target.score, sketch,
                Float32(target.sketch_step_size),
                Float32(SKETCH_REGULARIZATION),
                f32_sketch_pos, f32_sketch_ws)
            f32_sketch_pos = Float32.(res)
            if f32_sketch_pos != old
                f32_sketch_accepts += 1
            end
        end
        @assert eltype(f32_sketch_pos) === Float32 "Float32 sketch type check failed for $(target.name)"

        println("passed (MALA f32=$(f32_accepts/n_check) f64=$(f64_accepts/n_check), " *
            "sketch f32=$(f32_sketch_accepts/n_check))")

        push!(f32_rows, (target=target.name, dimension=d,
            sampler="mala",
            f32_acceptance=f32_accepts / n_check,
            f64_acceptance=f64_accepts / n_check,
            f32_eltype="Float32", f64_eltype="Float64"))
        push!(f32_rows, (target=target.name, dimension=d,
            sampler="active-sketch-smmala",
            f32_acceptance=f32_sketch_accepts / n_check,
            f64_acceptance=NaN,
            f32_eltype="Float32", f64_eltype="Float64"))
    end
    f32_rows
end

# --- Output ---

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

function write_metadata(seeds)
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
        println(io, "seeds,$(join(seeds, ';'))")
        println(io, "sketch_ranks,$(join(SKETCH_RANKS, ';'))")
        println(io, "sketch_regularization,$SKETCH_REGULARIZATION")
        println(io, "leapfrog_steps,$LEAPFROG_STEPS")
        println(io, "mcmc_diagnostic_tools_version,$(pkgversion(MCMCDiagnosticTools))")
    end
    println("wrote $path")
end

function write_summary(rows)
    mkpath(RESULTS_DIR)
    path = joinpath(RESULTS_DIR, "summary.txt")
    open(path, "w") do io
        println(io, "Active-Sketch sMMALA Paper Benchmark Summary")
        println(io, "=" ^ 55)
        println(io, "Mode: $(DEV_MODE ? "development (--dev)" : "full")")
        println(io, "Date: $(Dates.now())")
        println(io, "Chains: $CHAIN_COUNT, Warmup: $WARMUP, Retained: $RETAINED")
        println(io)

        println(io, "Results by Target")
        println(io, "-" ^ 55)
        for row in rows
            rank_str = row.rank > 0 ? " rank=$(row.rank)" : ""
            println(io, "  $(row.target) d=$(row.dimension) " *
                "$(row.method)$rank_str: " *
                "bulk_ESS=$(round(row.min_bulk_ess; digits=1)) " *
                "tail_ESS=$(round(row.min_tail_ess; digits=1)) " *
                "Rhat=$(round(row.max_rhat; digits=4)) " *
                "accept=$(round(row.acceptance_rate; digits=3)) " *
                "ESS/grad=$(round(row.ess_per_gradient; sigdigits=3)) " *
                "ESS/(grad+probe)=$(round(row.ess_per_gradient_probe; sigdigits=3))")
        end

        sketch_rows = filter(r -> r.method == "active-sketch-smmala", rows)
        mala_rows = filter(r -> r.method == "mala", rows)
        hmc_rows_all = filter(r -> r.method == "multinomial-hmc", rows)
        pmala_rows = filter(r -> r.method == "dense-pmala", rows)

        println(io)
        println(io, "Competitive Regime Analysis")
        println(io, "-" ^ 55)
        for target_name in unique(r.target for r in rows)
            for dim in unique(r.dimension for r in rows if r.target == target_name)
                t_sketch = filter(r -> r.target == target_name &&
                    r.dimension == dim &&
                    r.method == "active-sketch-smmala", rows)
                t_mala = filter(r -> r.target == target_name &&
                    r.dimension == dim && r.method == "mala", rows)
                t_hmc = filter(r -> r.target == target_name &&
                    r.dimension == dim && r.method == "multinomial-hmc", rows)
                t_pmala = filter(r -> r.target == target_name &&
                    r.dimension == dim && r.method == "dense-pmala", rows)

                isempty(t_sketch) && continue
                best_sketch = argmax(r -> r.ess_per_gradient_probe, t_sketch)
                println(io, "  $(target_name) d=$dim:")
                println(io, "    best sketch (rank=$(best_sketch.rank)): " *
                    "ESS/(grad+probe)=$(round(best_sketch.ess_per_gradient_probe; sigdigits=3))")

                if !isempty(t_mala)
                    mala_eff = first(t_mala).ess_per_gradient
                    ratio = best_sketch.ess_per_gradient_probe / mala_eff
                    println(io, "    vs MALA ESS/grad=$(round(mala_eff; sigdigits=3)) " *
                        "(ratio=$(round(ratio; digits=3)))")
                end
                if !isempty(t_hmc)
                    hmc_eff = first(t_hmc).ess_per_gradient
                    ratio = best_sketch.ess_per_gradient_probe / hmc_eff
                    println(io, "    vs HMC ESS/grad=$(round(hmc_eff; sigdigits=3)) " *
                        "(ratio=$(round(ratio; digits=3)))")
                end
                if !isempty(t_pmala)
                    pmala_eff = first(t_pmala).ess_per_gradient
                    ratio = best_sketch.ess_per_gradient_probe / pmala_eff
                    println(io, "    vs dense-PMALA ESS/grad=$(round(pmala_eff; sigdigits=3)) " *
                        "(ratio=$(round(ratio; digits=3)))")
                end
            end
        end
    end
    println("wrote $path")
end

function main()
    println("Active-Sketch sMMALA Paper Benchmark")
    println("Mode: $(DEV_MODE ? "development (--dev)" : "full")")
    println("Protocol: $(CHAIN_COUNT) chains × " *
        "$(WARMUP) warmup + $(RETAINED) retained draws")
    println("BLAS threads: $BLAS_THREADS")
    println("Seeds: $(SEEDS)")
    println()

    targets = benchmark_targets()
    println("Targets: $(join(["$(t.name) (d=$(t.dimension))" for t in targets], ", "))")

    f32_rows = run_float32_validation(targets)

    rows = run_benchmark(targets)

    mkpath(RESULTS_DIR)
    write_csv(joinpath(RESULTS_DIR, "diagnostics.csv"), rows)
    write_csv(joinpath(RESULTS_DIR, "f32_validation.csv"), f32_rows)
    write_metadata(SEEDS)
    write_summary(rows)

    println("\nBenchmark complete.")
end

main()
