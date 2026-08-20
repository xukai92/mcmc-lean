using AdvancedHMC
using LinearAlgebra
using Random
using Statistics
using VerifiedSamplers

const DEV_MODE = "--dev" in ARGS
const UNKNOWN_ARGUMENTS = filter(!=("--dev"), ARGS)
isempty(UNKNOWN_ARGUMENTS) || error(
    "unknown arguments: $(join(UNKNOWN_ARGUMENTS, ' ')); supported: --dev")
const DIMENSION = parse(Int, get(ENV, "HMC_DIMENSION", "100"))
const DRAWS = parse(Int, get(ENV, "HMC_DRAWS", DEV_MODE ? "1000" : "10000"))
const LEAPFROG_STEPS = parse(Int, get(ENV, "HMC_LEAPFROG_STEPS", "10"))
const STEP_SIZE = parse(Float64, get(ENV, "HMC_STEP_SIZE", "0.08"))
const SEED = parse(Int, get(ENV, "HMC_SEED", "4109"))
const DEFAULT_SEEDS = join(SEED .+ (0:9), ',')
const CONFIGURED_SEEDS = parse.(Int,
    split(get(ENV, "HMC_SEEDS", DEFAULT_SEEDS), ','))
const BENCHMARK_SEEDS = DEV_MODE ?
    CONFIGURED_SEEDS[1:min(3, length(CONFIGURED_SEEDS))] : CONFIGURED_SEEDS
const NUTS_MAX_DEPTH = parse(Int, get(ENV, "HMC_NUTS_MAX_DEPTH", "10"))
const NUTS_REFERENCE_DEPTH = parse(Int,
    get(ENV, "HMC_NUTS_REFERENCE_DEPTH", "4"))

const Runtime = VerifiedSamplers.Runtime
const Reference = VerifiedSamplers.Reference
const Optimized = VerifiedSamplers.Optimized
const Evaluation = VerifiedSamplers.Evaluation
const RAW_TIMINGS = NamedTuple[]
const QUALITY_ROWS = NamedTuple[]
const STARTED_CASES = Ref(0)
const TOTAL_CASES = Ref(0)
const BENCHMARK_STARTED_NS = Ref(0)

function known_covariance(target)
    target.name == "isotropic-gaussian" && return Matrix{Float64}(I,
        DIMENSION, DIMENSION)
    target.name == "correlated-gaussian-rho-0.9" &&
        return Matrix{Float64}(target.advanced_inverse_mass)
    target.name == "ill-conditioned-gaussian" &&
        return Matrix(Diagonal(target.variance))
    nothing
end

struct ChainMeasurement
    times::Vector{Float64}
    bytes::Vector{Int}
    outputs::Vector{Any}
    time::Float64
    memory::Int
end

function measure(f)
    f(first(BENCHMARK_SEEDS)) # compile and warm before measured chains
    times = Float64[]
    bytes = Int[]
    outputs = Any[]
    for seed in BENCHMARK_SEEDS
        GC.gc()
        measurement = @timed f(seed)
        push!(times, measurement.time * 1e9)
        push!(bytes, measurement.bytes)
        push!(outputs, measurement.value)
    end
    ChainMeasurement(times, bytes, outputs, median(times), Int(median(bytes)))
end

function measure_case(target, algorithm, implementation, f)
    STARTED_CASES[] += 1
    elapsed = (time_ns() - BENCHMARK_STARTED_NS[]) / 1e9
    println("[benchmark] case $(STARTED_CASES[])/$(TOTAL_CASES[]): " *
        "$(target.name) / $algorithm / $implementation " *
        "($(round(elapsed; digits=1)) s elapsed)")
    flush(stdout)
    measure(f)
end

function advanced_components(target)
    metric = UnitEuclideanMetric(DIMENSION)
    logdensity_and_gradient(q) =
        (target.logdensity(q), -target.gradient(q))
    hamiltonian = Hamiltonian(metric, target.logdensity, logdensity_and_gradient)
    integrator = Leapfrog(STEP_SIZE)
    endpoint = HMCKernel(Trajectory{EndPointTS}(
        integrator, FixedNSteps(LEAPFROG_STEPS)))
    multinomial = HMCKernel(Trajectory{MultinomialTS}(
        integrator, FixedNSteps(LEAPFROG_STEPS)))
    nuts = HMCKernel(Trajectory{MultinomialTS}(
        integrator, GeneralisedNoUTurn(max_depth=NUTS_MAX_DEPTH)))
    metric_hamiltonian = metric_endpoint = metric_multinomial = nothing
    if target.metric_mass !== nothing
        inverse_mass = target.advanced_inverse_mass
        advanced_metric = inverse_mass isa AbstractVector ?
            DiagEuclideanMetric(inverse_mass) : DenseEuclideanMetric(inverse_mass)
        metric_hamiltonian = Hamiltonian(
            advanced_metric, target.logdensity, logdensity_and_gradient)
        metric_endpoint = HMCKernel(Trajectory{EndPointTS}(
            integrator, FixedNSteps(LEAPFROG_STEPS)))
        metric_multinomial = HMCKernel(Trajectory{MultinomialTS}(
            integrator, FixedNSteps(LEAPFROG_STEPS)))
    end
    (; hamiltonian, endpoint, multinomial, nuts, metric_hamiltonian,
        metric_endpoint, metric_multinomial)
end

function run_verified(stepper, target, seed::Int, draws::Int)
    source = Runtime.RNGSource(MersenneTwister(seed))
    chain = Matrix{Float64}(undef, DIMENSION, draws)
    position = zeros(DIMENSION)
    for index in axes(chain, 2)
        position = stepper(source, target.logdensity, target.gradient,
            STEP_SIZE, LEAPFROG_STEPS, position)
        chain[:, index] = position
    end
    (; chain, acceptance=NaN, divergences=0,
        average_steps=Float64(LEAPFROG_STEPS), gradients_per_step=2)
end

function run_verified_metric(stepper, target, seed::Int, draws::Int;
        prepared::Bool=false)
    source = Runtime.RNGSource(MersenneTwister(seed))
    chain = Matrix{Float64}(undef, DIMENSION, draws)
    position = zeros(DIMENSION)
    metric = prepared ? Optimized.prepare_metric(target.metric_mass) :
        target.metric_mass
    for index in axes(chain, 2)
        position = stepper(source, target.logdensity, target.gradient,
            STEP_SIZE, LEAPFROG_STEPS, position, metric)
        chain[:, index] = position
    end
    (; chain, acceptance=NaN, divergences=0,
        average_steps=Float64(LEAPFROG_STEPS),
        gradients_per_step=prepared ? 1 + inv(Float64(LEAPFROG_STEPS)) : 2)
end

function run_verified_nuts(target, seed::Int, draws::Int)
    sampler = VerifiedSamplers.NUTS(target.logdensity, target.gradient,
        STEP_SIZE, NUTS_REFERENCE_DEPTH)
    chain = VerifiedSamplers.sample(
        MersenneTwister(seed), sampler, zeros(DIMENSION), draws)
    # A completed depth-d tree has 2^d phase points. The randomized origin
    # changes construction order, not the reported completed-tree work.
    average_steps = 1 << NUTS_REFERENCE_DEPTH
    (; chain, acceptance=NaN, divergences=0, average_steps,
        gradients_per_step=2)
end

function run_optimized_nuts(target, seed::Int, draws::Int)
    sampler = VerifiedSamplers.Optimized.NUTS(
        target.logdensity, target.gradient, STEP_SIZE;
        max_depth=NUTS_MAX_DEPTH, termination=:generalized,
        selection=:multinomial)
    run = VerifiedSamplers.sample_with_diagnostics(
        MersenneTwister(seed), sampler, zeros(DIMENSION), draws)
    diagnostics = run.diagnostics
    (; chain=run.samples,
        acceptance=mean(getproperty.(diagnostics, :acceptance_rate)),
        divergences=count(diagnostic -> diagnostic.divergent, diagnostics),
        average_steps=mean(getproperty.(diagnostics, :leapfrog_steps)),
        gradients_per_step=2)
end

function run_advanced(hamiltonian, kernel, seed::Int, draws::Int)
    rng = MersenneTwister(seed)
    hamiltonian, transition = AdvancedHMC.sample_init(
        rng, hamiltonian, zeros(DIMENSION))
    chain = Matrix{Float64}(undef, DIMENSION, draws)
    acceptance_sum = 0.0
    divergences = 0
    step_sum = 0
    for index in axes(chain, 2)
        transition = AdvancedHMC.transition(
            rng, hamiltonian, kernel, transition.z)
        chain[:, index] = transition.z.θ
        acceptance_sum += transition.stat.acceptance_rate
        divergences += transition.stat.numerical_error
        step_sum += transition.stat.n_steps
    end
    (; chain, acceptance=acceptance_sum / draws, divergences,
        average_steps=step_sum / draws, gradients_per_step=1)
end

function quality_summary(target, algorithm, implementation, outputs, seconds)
    chains = getproperty.(outputs, :chain)
    burnin = DRAWS ÷ 10
    retained_chains = [@view chain[:, (burnin + 1):end] for chain in chains]
    combined = reduce(hcat, retained_chains)
    coordinate_count = min(4, size(combined, 1))
    diagnostics = Evaluation.moment_diagnostics(
        combined, target.mean, target.variance;
        ess_coordinates=coordinate_count)
    retained_draws = diagnostics.retained_draws
    minimum_ess = diagnostics.minimum_ess
    standardized_mean_rmse = diagnostics.standardized_mean_rmse
    relative_variance_rmse = diagnostics.relative_variance_rmse
    rank_diagnostics = [Evaluation.split_rank_diagnostics(
        hcat([vec(@view chain[coordinate, :]) for chain in retained_chains]...))
        for coordinate in 1:coordinate_count]
    rank_normalized_rhat = maximum(
        diagnostic.rank_normalized_rhat for diagnostic in rank_diagnostics)
    bulk_ess = minimum(diagnostic.bulk_ess for diagnostic in rank_diagnostics)
    tail_ess = minimum(diagnostic.tail_ess for diagnostic in rank_diagnostics)
    chain_standard_errors = [Evaluation.batch_mean_standard_error(chain)
        for chain in retained_chains]
    mean_mcse = maximum(sqrt(sum(error[coordinate]^2
        for error in chain_standard_errors)) / length(chains)
        for coordinate in axes(combined, 1))
    covariance = known_covariance(target)
    covariance_max_error = covariance === nothing ? NaN :
        Evaluation.covariance_max_error(combined, covariance)
    median_max_error = Evaluation.marginal_quantile_max_error(
        combined, [0.5], zeros(DIMENSION, 1))
    movement = mean(mean(any(@view(chain[:, index]) .!=
        @view(chain[:, index - 1])) for index in 2:size(chain, 2))
        for chain in chains)
    total_draws = DRAWS * length(chains)
    average_steps = mean(getproperty.(outputs, :average_steps))
    gradients_per_step = only(unique(getproperty.(outputs, :gradients_per_step)))
    gradient_proxy = total_draws * average_steps * gradients_per_step
    acceptance_values = filter(isfinite, getproperty.(outputs, :acceptance))
    acceptance = isempty(acceptance_values) ? NaN : mean(acceptance_values)
    divergences = sum(getproperty.(outputs, :divergences))
    push!(QUALITY_ROWS, (; target=target.name, dimension=DIMENSION, algorithm,
        implementation, chains=length(chains), draws_per_chain=DRAWS,
        retained_draws, seconds, draws_per_second=total_draws / seconds,
        minimum_ess, ess_per_second=minimum_ess / seconds,
        rank_normalized_rhat, bulk_ess, tail_ess,
        bulk_ess_per_gradient_proxy=bulk_ess / gradient_proxy,
        mean_mcse, covariance_max_error, median_max_error,
        standardized_mean_rmse, relative_variance_rmse, movement,
        acceptance, divergences, average_steps))
end

function result(target, algorithm, implementation, trial, average_steps)
    times = trial.times ./ 1e9
    seconds = median(times)
    for (repetition, (seed, nanoseconds)) in enumerate(
            zip(BENCHMARK_SEEDS, trial.times))
        repetition_seconds = nanoseconds / 1e9
        push!(RAW_TIMINGS, (; target=target.name, dimension=DIMENSION,
            algorithm, implementation, repetition, seed,
            seconds=repetition_seconds,
            draws_per_second=DRAWS / repetition_seconds))
    end
    (; target=target.name, dimension=DIMENSION, algorithm, implementation,
        step_size=STEP_SIZE, configured_steps=LEAPFROG_STEPS, average_steps,
        draws=DRAWS, median_seconds=seconds,
        q25_seconds=quantile(times, 0.25), q75_seconds=quantile(times, 0.75),
        draws_per_second=DRAWS / seconds, memory_bytes=trial.memory,
        allocations="n/a")
end

function benchmark_target(target)
    components = advanced_components(target)
    reference_check = run_verified(
        Reference.vector_hmc_step!, target, SEED, 100).chain[:, end]
    optimized_check = run_verified(
        Optimized.vector_hmc_step!, target, SEED, 100).chain[:, end]
    reference_check == optimized_check || error(
        "Reference and Optimized endpoint HMC disagree for $(target.name)")
    multinomial_reference_check = run_verified(
        Reference.multinomial_hmc_step!, target, SEED, 100).chain[:, end]
    multinomial_optimized_check = run_verified(
        Optimized.multinomial_hmc_step!, target, SEED, 100).chain[:, end]
    multinomial_reference_check ≈ multinomial_optimized_check || error(
        "Reference and Optimized multinomial HMC disagree for $(target.name)")
    run_advanced(components.hamiltonian, components.endpoint, SEED, 100)
    run_advanced(components.hamiltonian, components.multinomial, SEED, 100)
    run_advanced(components.hamiltonian, components.nuts, SEED, 100)
    run_verified_nuts(target, SEED, 100)
    run_optimized_nuts(target, SEED, 100)

    endpoint_reference = measure_case(target, "endpoint", "verified-reference",
        seed -> run_verified(
        Reference.vector_hmc_step!, target, seed, DRAWS))
    endpoint_optimized = measure_case(target, "endpoint", "verified-optimized",
        seed -> run_verified(
        Optimized.vector_hmc_step!, target, seed, DRAWS))
    endpoint_advanced = measure_case(target, "endpoint", "advancedhmc",
        seed -> run_advanced(
        components.hamiltonian, components.endpoint, seed, DRAWS))
    multinomial_reference = measure_case(target, "multinomial",
        "verified-reference", seed -> run_verified(
        Reference.multinomial_hmc_step!, target, seed, DRAWS))
    multinomial_optimized = measure_case(target, "multinomial",
        "verified-optimized", seed -> run_verified(
        Optimized.multinomial_hmc_step!, target, seed, DRAWS))
    multinomial_advanced = measure_case(target, "multinomial", "advancedhmc",
        seed -> run_advanced(
        components.hamiltonian, components.multinomial, seed, DRAWS))
    nuts_advanced = measure_case(target, "nuts", "advancedhmc",
        seed -> run_advanced(
        components.hamiltonian, components.nuts, seed, DRAWS))
    nuts_reference = measure_case(target, "nuts", "verified-reference",
        seed -> run_verified_nuts(target, seed, DRAWS))
    nuts_optimized = measure_case(target, "nuts", "verified-optimized",
        seed -> run_optimized_nuts(target, seed, DRAWS))

    measured = [
        ("endpoint", "verified-reference", endpoint_reference),
        ("endpoint", "verified-optimized", endpoint_optimized),
        ("endpoint", "advancedhmc", endpoint_advanced),
        ("multinomial", "verified-reference", multinomial_reference),
        ("multinomial", "verified-optimized", multinomial_optimized),
        ("multinomial", "advancedhmc", multinomial_advanced),
        ("nuts", "verified-reference", nuts_reference),
        ("nuts", "verified-optimized", nuts_optimized),
        ("nuts", "advancedhmc", nuts_advanced)]
    for (algorithm, implementation, trial) in measured
        quality_summary(target, algorithm, implementation, trial.outputs,
            sum(trial.times) / 1e9)
    end

    average_steps(trial) = mean(
        getproperty.(trial.outputs, :average_steps))

    results = [
        result(target, "endpoint", "verified-reference", endpoint_reference,
            average_steps(endpoint_reference)),
        result(target, "endpoint", "verified-optimized", endpoint_optimized,
            average_steps(endpoint_optimized)),
        result(target, "endpoint", "advancedhmc", endpoint_advanced,
            average_steps(endpoint_advanced)),
        result(target, "multinomial", "verified-reference", multinomial_reference,
            average_steps(multinomial_reference)),
        result(target, "multinomial", "verified-optimized", multinomial_optimized,
            average_steps(multinomial_optimized)),
        result(target, "multinomial", "advancedhmc", multinomial_advanced,
            average_steps(multinomial_advanced)),
        result(target, "nuts", "verified-reference", nuts_reference,
            average_steps(nuts_reference)),
        result(target, "nuts", "verified-optimized", nuts_optimized,
            average_steps(nuts_optimized)),
        result(target, "nuts", "advancedhmc", nuts_advanced,
            average_steps(nuts_advanced)),
    ]
    if target.metric_mass !== nothing
        metric_reference_check = run_verified_metric(
            Reference.metric_hmc_step!, target, SEED, 100).chain[:, end]
        metric_optimized_check = run_verified_metric(
            Optimized.metric_hmc_step!, target, SEED, 100;
            prepared=true).chain[:, end]
        metric_reference_check ≈ metric_optimized_check || error(
            "Reference and Optimized metric endpoint HMC disagree for $(target.name)")
        metric_multi_reference_check = run_verified_metric(
            Reference.metric_multinomial_hmc_step!, target, SEED, 100).chain[:, end]
        metric_multi_optimized_check = run_verified_metric(
            Optimized.metric_multinomial_hmc_step!, target, SEED, 100;
            prepared=true).chain[:, end]
        metric_multi_reference_check ≈ metric_multi_optimized_check || error(
            "Reference and Optimized metric multinomial HMC disagree for $(target.name)")
        run_advanced(components.metric_hamiltonian,
            components.metric_endpoint, SEED, 100)
        metric_reference = measure_case(target, "preconditioned-endpoint",
            "verified-reference", seed -> run_verified_metric(
            Reference.metric_hmc_step!, target, seed, DRAWS))
        metric_optimized = measure_case(target, "preconditioned-endpoint",
            "verified-optimized", seed -> run_verified_metric(
            Optimized.metric_hmc_step!, target, seed, DRAWS; prepared=true))
        metric_advanced = measure_case(target, "preconditioned-endpoint",
            "advancedhmc", seed -> run_advanced(
            components.metric_hamiltonian, components.metric_endpoint,
            seed, DRAWS))
        for (implementation, trial) in (("verified-reference", metric_reference),
                ("verified-optimized", metric_optimized),
                ("advancedhmc", metric_advanced))
            quality_summary(target, "preconditioned-endpoint", implementation,
                trial.outputs, sum(trial.times) / 1e9)
        end
        append!(results, [
            result(target, "preconditioned-endpoint", "verified-reference",
                metric_reference, average_steps(metric_reference)),
            result(target, "preconditioned-endpoint", "verified-optimized",
                metric_optimized, average_steps(metric_optimized)),
            result(target, "preconditioned-endpoint", "advancedhmc",
                metric_advanced, average_steps(metric_advanced)),
        ])

        metric_multi_reference = measure_case(target,
            "preconditioned-multinomial", "verified-reference",
            seed -> run_verified_metric(
            Reference.metric_multinomial_hmc_step!, target, seed, DRAWS))
        metric_multi_optimized = measure_case(target,
            "preconditioned-multinomial", "verified-optimized",
            seed -> run_verified_metric(
            Optimized.metric_multinomial_hmc_step!, target, seed, DRAWS;
            prepared=true))
        metric_multi_advanced = measure_case(target,
            "preconditioned-multinomial", "advancedhmc",
            seed -> run_advanced(
            components.metric_hamiltonian, components.metric_multinomial,
            seed, DRAWS))
        for (implementation, trial) in
                (("verified-reference", metric_multi_reference),
                    ("verified-optimized", metric_multi_optimized),
                    ("advancedhmc", metric_multi_advanced))
            quality_summary(target, "preconditioned-multinomial", implementation,
                trial.outputs, sum(trial.times) / 1e9)
        end
        append!(results, [
            result(target, "preconditioned-multinomial", "verified-reference",
                metric_multi_reference, average_steps(metric_multi_reference)),
            result(target, "preconditioned-multinomial", "verified-optimized",
                metric_multi_optimized, average_steps(metric_multi_optimized)),
            result(target, "preconditioned-multinomial", "advancedhmc",
                metric_multi_advanced, average_steps(metric_multi_advanced)),
        ])
    end
    results
end

function write_results(rows)
    filename = DEV_MODE ? "dev.csv" : "latest.csv"
    output = joinpath(@__DIR__, "results", filename)
    mkpath(dirname(output))
    names = propertynames(first(rows))
    open(output, "w") do io
        println(io, join(names, ','))
        for row in rows
            println(io, join((getproperty(row, name) for name in names), ','))
        end
    end
    timing_output = joinpath(@__DIR__, "results",
        DEV_MODE ? "dev-timings.csv" : "timings.csv")
    timing_names = propertynames(first(RAW_TIMINGS))
    open(timing_output, "w") do io
        println(io, join(timing_names, ','))
        for row in RAW_TIMINGS
            println(io, join((getproperty(row, name) for name in timing_names), ','))
        end
    end
    quality_output = joinpath(@__DIR__, "results",
        DEV_MODE ? "dev-quality.csv" : "quality.csv")
    quality_names = propertynames(first(QUALITY_ROWS))
    open(quality_output, "w") do io
        println(io, join(quality_names, ','))
        for row in QUALITY_ROWS
            println(io, join((getproperty(row, name) for name in quality_names), ','))
        end
    end
    println("wrote $output")
    println("wrote $timing_output")
    println("wrote $quality_output")
    metadata_output = joinpath(@__DIR__, "results",
        DEV_MODE ? "dev-metadata.csv" : "metadata.csv")
    commit = readchomp(`git -C $(joinpath(@__DIR__, "..")) rev-parse --short HEAD`)
    open(metadata_output, "w") do io
        println(io, "commit,$commit")
        println(io, "julia,$VERSION")
        println(io, "cpu,$(Sys.cpu_info()[1].model)")
    end
    println("wrote $metadata_output")
end

function main()
    DIMENSION >= 2 || error("HMC_DIMENSION must be at least two")
    DRAWS >= 8 || error("HMC_DRAWS must be at least eight for split diagnostics")
    LEAPFROG_STEPS > 0 || error("HMC_LEAPFROG_STEPS must be positive")
    STEP_SIZE > 0 || error("HMC_STEP_SIZE must be positive")
    NUTS_MAX_DEPTH > 0 || error("HMC_NUTS_MAX_DEPTH must be positive")
    NUTS_REFERENCE_DEPTH >= 0 ||
        error("HMC_NUTS_REFERENCE_DEPTH must be nonnegative")
    length(BENCHMARK_SEEDS) >= 2 || error(
        "HMC_SEEDS must provide at least two seeds")
    length(unique(BENCHMARK_SEEDS)) == length(BENCHMARK_SEEDS) || error(
        "HMC_SEEDS must not contain duplicates")
    target_suite = Evaluation.standard_targets(DIMENSION)
    STARTED_CASES[] = 0
    TOTAL_CASES[] = sum(target.metric_mass === nothing ? 9 : 15
        for target in target_suite)
    BENCHMARK_STARTED_NS[] = time_ns()
    rows = reduce(vcat, benchmark_target(target) for target in target_suite)
    write_results(rows)
end

main()
