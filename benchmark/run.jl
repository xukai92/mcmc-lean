using AdvancedHMC
using BenchmarkTools
using LinearAlgebra
using Random
using Statistics
using VerifiedSamplers

include(joinpath(@__DIR__, "..", "VerifiedSamplers.jl", "test", "support",
    "TestTargets.jl"))
include(joinpath(@__DIR__, "..", "VerifiedSamplers.jl", "test", "support",
    "QualityDiagnostics.jl"))

const DEV_MODE = "--dev" in ARGS
const UNKNOWN_ARGUMENTS = filter(!=("--dev"), ARGS)
isempty(UNKNOWN_ARGUMENTS) || error(
    "unknown arguments: $(join(UNKNOWN_ARGUMENTS, ' ')); supported: --dev")
const DIMENSION = parse(Int, get(ENV, "HMC_DIMENSION", "100"))
const DRAWS = parse(Int, get(ENV, "HMC_DRAWS", DEV_MODE ? "1000" : "10000"))
const LEAPFROG_STEPS = parse(Int, get(ENV, "HMC_LEAPFROG_STEPS", "10"))
const STEP_SIZE = parse(Float64, get(ENV, "HMC_STEP_SIZE", "0.08"))
const SEED = parse(Int, get(ENV, "HMC_SEED", "4109"))
const REPETITIONS = parse(Int, get(ENV, "HMC_REPETITIONS", DEV_MODE ? "3" : "10"))
const BENCHMARK_SECONDS = parse(Float64,
    get(ENV, "HMC_BENCHMARK_SECONDS", DEV_MODE ? "0.05" : "120"))
const BENCHMARK_SAMPLES = REPETITIONS
const NUTS_MAX_DEPTH = parse(Int, get(ENV, "HMC_NUTS_MAX_DEPTH", "10"))
const QUALITY_DRAWS = parse(Int,
    get(ENV, "HMC_QUALITY_DRAWS", DEV_MODE ? "500" : "5000"))
const QUALITY_CHAINS = parse(Int, get(ENV, "HMC_QUALITY_CHAINS", "4"))

const Runtime = VerifiedSamplers.Runtime
const Reference = VerifiedSamplers.Reference
const Optimized = VerifiedSamplers.Optimized
const RAW_TIMINGS = NamedTuple[]
const QUALITY_ROWS = NamedTuple[]

function known_covariance(target)
    target.name == "isotropic-gaussian" && return Matrix{Float64}(I,
        DIMENSION, DIMENSION)
    target.name == "correlated-gaussian-rho-0.9" &&
        return Matrix{Float64}(target.advanced_inverse_mass)
    target.name == "ill-conditioned-gaussian" &&
        return Matrix(Diagonal(target.variance))
    nothing
end

struct DevMeasurement
    times::Vector{Float64}
    time::Float64
    memory::Int
end

function measure(f)
    if DEV_MODE
        times = Float64[]
        memory = Int[]
        for _ in 1:REPETITIONS
            GC.gc()
            measurement = @timed f()
            push!(times, measurement.time * 1e9)
            push!(memory, measurement.bytes)
        end
        return DevMeasurement(times, median(times), Int(median(memory)))
    end
    benchmarkable = @benchmarkable $f() evals=1
    BenchmarkTools.run(benchmarkable;
        seconds=BENCHMARK_SECONDS, samples=BENCHMARK_SAMPLES)
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
    position = zeros(DIMENSION)
    for _ in 1:draws
        position = stepper(source, target.logdensity, target.gradient,
            STEP_SIZE, LEAPFROG_STEPS, position)
    end
    position
end

function run_advanced(hamiltonian, kernel, seed::Int, draws::Int)
    rng = MersenneTwister(seed)
    hamiltonian, transition = AdvancedHMC.sample_init(
        rng, hamiltonian, zeros(DIMENSION))
    for _ in 1:draws
        transition = AdvancedHMC.transition(
            rng, hamiltonian, kernel, transition.z)
    end
    transition.z.θ
end

function nuts_average_steps(hamiltonian, kernel, seed::Int, draws::Int)
    rng = MersenneTwister(seed)
    hamiltonian, transition = AdvancedHMC.sample_init(
        rng, hamiltonian, zeros(DIMENSION))
    total_steps = 0
    for _ in 1:draws
        transition = AdvancedHMC.transition(rng, hamiltonian, kernel, transition.z)
        total_steps += transition.stat.n_steps
    end
    total_steps / draws
end

function quality_summary(target, algorithm, implementation, chains, seconds;
        acceptance=NaN, divergences=0, average_steps=LEAPFROG_STEPS,
        gradients_per_step=1)
    burnin = QUALITY_DRAWS ÷ 10
    retained_chains = [@view chain[:, (burnin + 1):end] for chain in chains]
    combined = reduce(hcat, retained_chains)
    coordinate_count = min(4, size(combined, 1))
    diagnostics = QualityDiagnostics.moment_diagnostics(
        combined, target.mean, target.variance;
        ess_coordinates=coordinate_count)
    retained_draws = diagnostics.retained_draws
    minimum_ess = diagnostics.minimum_ess
    standardized_mean_rmse = diagnostics.standardized_mean_rmse
    relative_variance_rmse = diagnostics.relative_variance_rmse
    rank_diagnostics = [QualityDiagnostics.split_rank_diagnostics(
        hcat([vec(@view chain[coordinate, :]) for chain in retained_chains]...))
        for coordinate in 1:coordinate_count]
    rank_normalized_rhat = maximum(
        diagnostic.rank_normalized_rhat for diagnostic in rank_diagnostics)
    bulk_ess = minimum(diagnostic.bulk_ess for diagnostic in rank_diagnostics)
    tail_ess = minimum(diagnostic.tail_ess for diagnostic in rank_diagnostics)
    chain_standard_errors = [QualityDiagnostics.batch_mean_standard_error(chain)
        for chain in retained_chains]
    mean_mcse = maximum(sqrt(sum(error[coordinate]^2
        for error in chain_standard_errors)) / QUALITY_CHAINS
        for coordinate in axes(combined, 1))
    covariance = known_covariance(target)
    covariance_max_error = covariance === nothing ? NaN :
        QualityDiagnostics.covariance_max_error(combined, covariance)
    median_max_error = QualityDiagnostics.marginal_quantile_max_error(
        combined, [0.5], zeros(DIMENSION, 1))
    movement = mean(mean(any(@view(chain[:, index]) .!=
        @view(chain[:, index - 1])) for index in 2:size(chain, 2))
        for chain in chains)
    total_draws = QUALITY_DRAWS * QUALITY_CHAINS
    gradient_proxy = total_draws * average_steps * gradients_per_step
    push!(QUALITY_ROWS, (; target=target.name, dimension=DIMENSION, algorithm,
        implementation, chains=QUALITY_CHAINS, draws_per_chain=QUALITY_DRAWS,
        retained_draws, seconds, draws_per_second=total_draws / seconds,
        minimum_ess, ess_per_second=minimum_ess / seconds,
        rank_normalized_rhat, bulk_ess, tail_ess,
        bulk_ess_per_gradient_proxy=bulk_ess / gradient_proxy,
        mean_mcse, covariance_max_error, median_max_error,
        standardized_mean_rmse, relative_variance_rmse, movement,
        acceptance, divergences, average_steps))
end

function verified_quality(target, algorithm, stepper)
    chains = Matrix{Float64}[]
    seconds = @elapsed for chain_index in 1:QUALITY_CHAINS
        source = Runtime.RNGSource(MersenneTwister(SEED + 91 + chain_index))
        chain = Matrix{Float64}(undef, DIMENSION, QUALITY_DRAWS)
        position = zeros(DIMENSION)
        for index in axes(chain, 2)
            position = stepper(source, target.logdensity, target.gradient,
                STEP_SIZE, LEAPFROG_STEPS, position)
            chain[:, index] = position
        end
        push!(chains, chain)
    end
    quality_summary(target, algorithm, "verified-optimized", chains, seconds;
        gradients_per_step=2)
end

function advanced_quality(target, algorithm, hamiltonian, kernel)
    chains = Matrix{Float64}[]
    acceptance_sum = 0.0
    divergences = 0
    step_sum = 0
    seconds = @elapsed for chain_index in 1:QUALITY_CHAINS
        rng = MersenneTwister(SEED + 91 + chain_index)
        chain_hamiltonian, transition = AdvancedHMC.sample_init(
            rng, hamiltonian, zeros(DIMENSION))
        chain = Matrix{Float64}(undef, DIMENSION, QUALITY_DRAWS)
        for index in axes(chain, 2)
            transition = AdvancedHMC.transition(
                rng, chain_hamiltonian, kernel, transition.z)
            chain[:, index] = transition.z.θ
            acceptance_sum += transition.stat.acceptance_rate
            divergences += transition.stat.numerical_error
            step_sum += transition.stat.n_steps
        end
        push!(chains, chain)
    end
    total_draws = QUALITY_DRAWS * QUALITY_CHAINS
    quality_summary(target, algorithm, "advancedhmc", chains, seconds;
        acceptance=acceptance_sum / total_draws, divergences,
        average_steps=step_sum / total_draws)
end

function quality_target(target)
    components = advanced_components(target)
    verified_quality(target, "endpoint", Optimized.vector_hmc_step!)
    advanced_quality(target, "endpoint", components.hamiltonian,
        components.endpoint)
    verified_quality(target, "multinomial", Optimized.multinomial_hmc_step!)
    advanced_quality(target, "multinomial", components.hamiltonian,
        components.multinomial)
    advanced_quality(target, "nuts", components.hamiltonian, components.nuts)
    if target.metric_mass !== nothing
        advanced_quality(target, "preconditioned-endpoint",
            components.metric_hamiltonian, components.metric_endpoint)
        advanced_quality(target, "preconditioned-multinomial",
            components.metric_hamiltonian, components.metric_multinomial)
    end
end

function result(target, algorithm, implementation, trial, average_steps)
    estimate = DEV_MODE ? trial : BenchmarkTools.median(trial)
    times = trial.times ./ 1e9
    seconds = median(times)
    for (repetition, nanoseconds) in enumerate(trial.times)
        repetition_seconds = nanoseconds / 1e9
        push!(RAW_TIMINGS, (; target=target.name, dimension=DIMENSION,
            algorithm, implementation, repetition, seed=SEED,
            seconds=repetition_seconds,
            draws_per_second=DRAWS / repetition_seconds))
    end
    (; target=target.name, dimension=DIMENSION, algorithm, implementation,
        step_size=STEP_SIZE, configured_steps=LEAPFROG_STEPS, average_steps,
        draws=DRAWS, median_seconds=seconds,
        q25_seconds=quantile(times, 0.25), q75_seconds=quantile(times, 0.75),
        draws_per_second=DRAWS / seconds, memory_bytes=estimate.memory,
        allocations=DEV_MODE ? "n/a" : string(estimate.allocs))
end

function benchmark_target(target)
    components = advanced_components(target)
    reference_check = run_verified(Reference.vector_hmc_step!, target, SEED, 100)
    optimized_check = run_verified(Optimized.vector_hmc_step!, target, SEED, 100)
    reference_check == optimized_check || error(
        "Reference and Optimized endpoint HMC disagree for $(target.name)")
    multinomial_reference_check = run_verified(
        Reference.multinomial_hmc_step!, target, SEED, 100)
    multinomial_optimized_check = run_verified(
        Optimized.multinomial_hmc_step!, target, SEED, 100)
    multinomial_reference_check ≈ multinomial_optimized_check || error(
        "Reference and Optimized multinomial HMC disagree for $(target.name)")
    run_advanced(components.hamiltonian, components.endpoint, SEED, 100)
    run_advanced(components.hamiltonian, components.multinomial, SEED, 100)
    run_advanced(components.hamiltonian, components.nuts, SEED, 100)

    endpoint_reference = measure(() -> run_verified(
        Reference.vector_hmc_step!, target, SEED, DRAWS))
    endpoint_optimized = measure(() -> run_verified(
        Optimized.vector_hmc_step!, target, SEED, DRAWS))
    endpoint_advanced = measure(() -> run_advanced(
        components.hamiltonian, components.endpoint, SEED, DRAWS))
    multinomial_reference = measure(() -> run_verified(
        Reference.multinomial_hmc_step!, target, SEED, DRAWS))
    multinomial_optimized = measure(() -> run_verified(
        Optimized.multinomial_hmc_step!, target, SEED, DRAWS))
    multinomial_advanced = measure(() -> run_advanced(
        components.hamiltonian, components.multinomial, SEED, DRAWS))
    nuts_advanced = measure(() -> run_advanced(
        components.hamiltonian, components.nuts, SEED, DRAWS))
    average_nuts_steps = nuts_average_steps(
        components.hamiltonian, components.nuts, SEED, DRAWS)

    results = [
        result(target, "endpoint", "verified-reference", endpoint_reference,
            LEAPFROG_STEPS),
        result(target, "endpoint", "verified-optimized", endpoint_optimized,
            LEAPFROG_STEPS),
        result(target, "endpoint", "advancedhmc", endpoint_advanced,
            LEAPFROG_STEPS),
        result(target, "multinomial", "verified-reference", multinomial_reference,
            LEAPFROG_STEPS),
        result(target, "multinomial", "verified-optimized", multinomial_optimized,
            LEAPFROG_STEPS),
        result(target, "multinomial", "advancedhmc", multinomial_advanced,
            LEAPFROG_STEPS),
        result(target, "nuts", "advancedhmc", nuts_advanced, average_nuts_steps),
    ]
    if target.metric_mass !== nothing
        run_advanced(components.metric_hamiltonian,
            components.metric_endpoint, SEED, 100)
        metric_advanced = measure(() -> run_advanced(
            components.metric_hamiltonian, components.metric_endpoint,
            SEED, DRAWS))
        append!(results, [
            result(target, "preconditioned-endpoint", "advancedhmc",
                metric_advanced, LEAPFROG_STEPS),
        ])

        metric_multi_advanced = measure(() -> run_advanced(
            components.metric_hamiltonian, components.metric_multinomial,
            SEED, DRAWS))
        append!(results, [
            result(target, "preconditioned-multinomial", "advancedhmc",
                metric_multi_advanced, LEAPFROG_STEPS),
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
    DRAWS > 0 || error("HMC_DRAWS must be positive")
    LEAPFROG_STEPS > 0 || error("HMC_LEAPFROG_STEPS must be positive")
    STEP_SIZE > 0 || error("HMC_STEP_SIZE must be positive")
    NUTS_MAX_DEPTH > 0 || error("HMC_NUTS_MAX_DEPTH must be positive")
    REPETITIONS > 0 || error("HMC_REPETITIONS must be positive")
    QUALITY_DRAWS > 10 || error("HMC_QUALITY_DRAWS must exceed ten")
    QUALITY_CHAINS >= 2 || error("HMC_QUALITY_CHAINS must be at least two")
    target_suite = TestTargets.suite(DIMENSION)
    rows = reduce(vcat, benchmark_target(target) for target in target_suite)
    foreach(quality_target, target_suite)
    write_results(rows)
end

main()
