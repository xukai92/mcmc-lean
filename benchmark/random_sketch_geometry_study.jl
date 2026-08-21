using LinearAlgebra
using Random
using Statistics
using UnicodePlots
using VerifiedSamplers

parse_grid(name, default) = parse.(Float64, split(get(ENV, name, default), ','))

const DIMENSION = parse(Int, get(ENV, "GEOMETRY_STUDY_DIMENSION", "2"))
const PROBE_SCHEDULE = get(ENV, "GEOMETRY_STUDY_PROBE_SCHEDULE", "fixed")
const DEFAULT_PROBES = PROBE_SCHEDULE == "log2" ?
    max(1, ceil(Int, log2(DIMENSION))) : 1
const PROBES = parse(Int,
    get(ENV, "GEOMETRY_STUDY_PROBES", string(DEFAULT_PROBES)))
const DRAWS = parse(Int, get(ENV, "GEOMETRY_STUDY_DRAWS", "2000"))
const BURNIN = parse(Int, get(ENV, "GEOMETRY_STUDY_BURNIN", "1000"))
const BANANA = parse(Float64, get(ENV, "GEOMETRY_STUDY_BANANA", "2.0"))
const RIDGE = parse(Float64, get(ENV, "GEOMETRY_STUDY_RIDGE", "0.1"))
const SOLVER_ITERATIONS = parse(Int,
    get(ENV, "GEOMETRY_STUDY_SOLVER_ITERATIONS", "25"))
const SOLVER_TOLERANCE = parse(Float64,
    get(ENV, "GEOMETRY_STUDY_SOLVER_TOLERANCE", "1e-10"))
const RESIDUAL_TOLERANCE = parse(Float64,
    get(ENV, "GEOMETRY_STUDY_RESIDUAL_TOLERANCE", "1e-6"))
const SEEDS = parse.(Int, split(get(ENV,
    "GEOMETRY_STUDY_SEEDS", "9211,9212,9213,9214"), ','))
const PROBE_SEED = parse(Int, get(ENV, "GEOMETRY_STUDY_PROBE_SEED", "9210"))
const ALGORITHMS = split(get(ENV, "GEOMETRY_STUDY_ALGORITHMS",
    "hmc,full-rmhmc,random-sketch-rmhmc"), ',')
const OUTPUT = get(ENV, "GEOMETRY_STUDY_OUTPUT",
    "random-sketch-geometry-study.csv")
const OUTPUT_PREFIX = get(ENV, "GEOMETRY_STUDY_OUTPUT_PREFIX",
    "random-sketch-geometry")
const ROTATED = lowercase(get(ENV, "GEOMETRY_STUDY_ROTATED", "false")) in
    ("1", "true", "yes")
const HMC_INTEGRATION_TIMES = parse_grid(
    "GEOMETRY_STUDY_HMC_INTEGRATION_TIMES",
    get(ENV, "GEOMETRY_STUDY_INTEGRATION_TIMES", "0.1,0.2"))
const RMHMC_INTEGRATION_TIMES = parse_grid(
    "GEOMETRY_STUDY_RMHMC_INTEGRATION_TIMES",
    get(ENV, "GEOMETRY_STUDY_INTEGRATION_TIMES", "1.0"))
const HMC_STEP_SIZES = parse_grid(
    "GEOMETRY_STUDY_HMC_STEP_SIZES", "0.001,0.002,0.005")
const RMHMC_STEP_SIZES = parse_grid(
    "GEOMETRY_STUDY_RMHMC_STEP_SIZES", "0.005,0.01,0.04")
const FULL_RMHMC_STEP_SIZES = parse_grid(
    "GEOMETRY_STUDY_FULL_RMHMC_STEP_SIZES",
    "0.04")
const SKETCH_RMHMC_STEP_SIZES = parse_grid(
    "GEOMETRY_STUDY_SKETCH_RMHMC_STEP_SIZES",
    "0.005,0.01")

function warped_directions()
    rng = MersenneTwister(PROBE_SEED + 17DIMENSION)
    first = randn(rng, DIMENSION)
    first ./= norm(first)
    DIMENSION == 1 && return first, zeros(DIMENSION)
    second = randn(rng, DIMENSION)
    second .-= dot(first, second) .* first
    second ./= norm(second)
    first, second
end

const WARP_INPUT, WARP_OUTPUT = warped_directions()

function latent(position)
    if ROTATED
        coordinate = dot(WARP_INPUT, position)
        return position + BANANA * (coordinate^2 - 1) .* WARP_OUTPUT
    end
    result = copy(position)
    result[2] += BANANA * (result[1]^2 - 1)
    result
end

function potential(q)
    y = latent(q)
    sum(abs2, y) / 2
end

function potential_gradient(q)
    y = latent(q)
    if ROTATED
        slope = 2BANANA * dot(WARP_INPUT, q)
        return y + slope * dot(WARP_OUTPUT, y) .* WARP_INPUT
    end
    gradient = copy(y)
    gradient[1] = y[1] + 2BANANA * q[1] * y[2]
    gradient
end

function curvature_action(q, probe)
    if ROTATED
        slope = 2BANANA * dot(WARP_INPUT, q)
        return probe + slope * dot(WARP_OUTPUT, probe) .* WARP_INPUT
    end
    action = copy(probe)
    action[1] += 2BANANA * q[1] * probe[2]
    action
end

function curvature_action_derivative(q, probe)
    if ROTATED
        coefficient = 2BANANA * dot(WARP_OUTPUT, probe)
        return coefficient .* (WARP_INPUT * WARP_INPUT')
    end
    derivative = zeros(eltype(q), length(q), length(q))
    derivative[1, 1] = 2BANANA * probe[2]
    derivative
end

function full_metric(q)
    if ROTATED
        T = eltype(q)
        input = T.(WARP_INPUT)
        output = T.(WARP_OUTPUT)
        slope = 2T(BANANA) * dot(input, q)
        return Matrix{T}(I, length(q), length(q)) .* (one(T) + T(RIDGE)) +
            slope .* (input * output' + output * input') +
            slope^2 .* (input * input')
    end
    metric = Matrix{eltype(q)}(I, length(q), length(q)) .* (1 + RIDGE)
    slope = 2BANANA * q[1]
    metric[1, 1] += slope^2
    metric[1, 2] += slope
    metric[2, 1] += slope
    metric
end

function full_metric_derivative(q)
    if ROTATED
        T = eltype(q)
        input = T.(WARP_INPUT)
        output = T.(WARP_OUTPUT)
        slope = 2T(BANANA) * dot(input, q)
        base = input * output' + output * input' +
            2slope .* (input * input')
        derivative = Array{T,3}(undef, length(q), length(q), length(q))
        for coordinate in eachindex(q)
            derivative[:, :, coordinate] =
                2T(BANANA) * input[coordinate] .* base
        end
        return derivative
    end
    derivative = zeros(eltype(q), length(q), length(q), length(q))
    derivative[1, 1, 1] = 8BANANA^2 * q[1]
    derivative[1, 2, 1] = 2BANANA
    derivative[2, 1, 1] = 2BANANA
    derivative
end

function fixed_probes()
    rng = MersenneTwister(PROBE_SEED)
    Float64.(ifelse.(rand(rng, Bool, DIMENSION, PROBES), 1, -1))
end

configured_steps(integration_time, step_size) =
    max(1, round(Int, integration_time / step_size))

function sampler(algorithm, probes, step_size, integration_time)
    steps = configured_steps(integration_time, step_size)
    if algorithm == "hmc"
        return VectorHMC(q -> -potential(q), q -> -potential_gradient(q),
            step_size, steps)
    elseif algorithm == "full-rmhmc"
        return DenseRiemannianRMHMC(potential, potential_gradient,
            full_metric, full_metric_derivative, step_size, steps;
            solver_iterations=SOLVER_ITERATIONS,
            solver_tolerance=SOLVER_TOLERANCE,
            residual_tolerance=RESIDUAL_TOLERANCE,
            implementation=:optimized)
    elseif algorithm == "random-sketch-rmhmc"
        return RandomSketchRMHMC(potential, potential_gradient,
            curvature_action, curvature_action_derivative, probes, RIDGE,
            step_size, steps; solver_iterations=SOLVER_ITERATIONS,
            solver_tolerance=SOLVER_TOLERANCE,
            residual_tolerance=RESIDUAL_TOLERANCE,
            implementation=:optimized)
    end
    error("unknown algorithm $algorithm")
end

function latent_chain(chain)
    transformed = similar(chain)
    for index in axes(chain, 2)
        transformed[:, index] = latent(@view chain[:, index])
    end
    transformed
end

failed_row(algorithm, step_size, integration_time, failures) =
    (; algorithm, probes=PROBES, step_size, integration_time,
        steps=configured_steps(integration_time, step_size), draws=DRAWS,
        burnin=BURNIN, retained_per_chain=DRAWS - BURNIN, failures,
        seconds=Inf, draws_per_second=0.0, bulk_ess=0.0, tail_ess=0.0,
        bulk_ess_per_transition=0.0, tail_ess_per_transition=0.0,
        bulk_ess_per_second=0.0, tail_ess_per_second=0.0,
        rank_normalized_rhat=Inf, latent_esjd=0.0,
        latent_mean_rmse=Inf, latent_variance_rmse=Inf)

is_numerical_failure(error) = error isa Union{
    ArgumentError,DomainError,LinearAlgebra.PosDefException}

function progress_path()
    stem, _ = splitext(OUTPUT)
    joinpath(@__DIR__, "results", "$stem-progress.csv")
end

function initialize_progress()
    path = progress_path()
    mkpath(dirname(path))
    open(path, "w") do io
        println(io,
            "algorithm,probes,step_size,integration_time,chain,seed,status,seconds,cumulative_seconds,eta_seconds")
    end
    println("chain progress: $path")
end

function record_progress(algorithm, step_size, integration_time, chain, seed,
        status, seconds, cumulative_seconds, eta_seconds)
    open(progress_path(), "a") do io
        println(io, join((algorithm, PROBES, step_size, integration_time,
            chain, seed,
            status, seconds, cumulative_seconds, eta_seconds), ','))
        flush(io)
    end
end

function run_configuration(algorithm, probes, step_size, integration_time)
    configured = sampler(algorithm, probes, step_size, integration_time)
    try
        sample(MersenneTwister(first(SEEDS)), configured, zeros(DIMENSION), 2)
    catch error
        is_numerical_failure(error) || rethrow()
        return failed_row(algorithm, step_size, integration_time,
            length(SEEDS))
    end
    chains = Matrix{Float64}[]
    seconds = Float64[]
    failures = 0
    configuration_started = time()
    for (chain_index, seed) in enumerate(SEEDS)
        print("\n  chain $chain_index/$(length(SEEDS)) seed=$seed ... ")
        flush(stdout)
        GC.gc()
        trial = try
            @timed sample(MersenneTwister(seed), configured,
                zeros(DIMENSION), DRAWS)
        catch error
            is_numerical_failure(error) || rethrow()
            failures += 1
            nothing
        end
        cumulative_seconds = time() - configuration_started
        if isnothing(trial)
            record_progress(algorithm, step_size, integration_time,
                chain_index, seed, "failed", 0.0, cumulative_seconds, Inf)
            println("numerical failure")
            continue
        end
        push!(seconds, trial.time)
        push!(chains, latent_chain(trial.value))
        average_seconds = sum(seconds) / length(seconds)
        eta_seconds = average_seconds * (length(SEEDS) - chain_index)
        record_progress(algorithm, step_size, integration_time,
            chain_index, seed, "completed", trial.time, cumulative_seconds,
            eta_seconds)
        println("$(round(trial.time; digits=2)) s, " *
            "ETA $(round(eta_seconds; digits=1)) s")
    end
    isempty(chains) && return failed_row(
        algorithm, step_size, integration_time, failures)

    retained = [@view chain[:, (BURNIN + 1):end] for chain in chains]
    coordinate_count = min(4, DIMENSION)
    rank_diagnostics = [VerifiedSamplers.Evaluation.split_rank_diagnostics(
        hcat([vec(@view chain[coordinate, :]) for chain in retained]...))
        for coordinate in 1:coordinate_count]
    bulk_ess = minimum(result.bulk_ess for result in rank_diagnostics)
    tail_ess = minimum(result.tail_ess for result in rank_diagnostics)
    total_seconds = sum(seconds)
    retained_transitions = sum(size(chain, 2) for chain in retained)
    combined = reduce(hcat, retained)
    means = vec(mean(combined; dims=2))
    variances = vec(var(combined; dims=2))
    esjd = mean(mean(sum(abs2, @view(chain[:, index]) .-
        @view(chain[:, index - 1])) / DIMENSION
        for index in 2:size(chain, 2)) for chain in retained)
    (; algorithm, probes=PROBES, step_size, integration_time,
        steps=configured_steps(integration_time, step_size), draws=DRAWS,
        burnin=BURNIN, retained_per_chain=DRAWS - BURNIN, failures,
        seconds=total_seconds,
        draws_per_second=length(chains) * DRAWS / total_seconds,
        bulk_ess, tail_ess,
        bulk_ess_per_transition=bulk_ess / retained_transitions,
        tail_ess_per_transition=tail_ess / retained_transitions,
        bulk_ess_per_second=bulk_ess / total_seconds,
        tail_ess_per_second=tail_ess / total_seconds,
        rank_normalized_rhat=maximum(
            result.rank_normalized_rhat for result in rank_diagnostics),
        latent_esjd=esjd,
        latent_mean_rmse=sqrt(mean(abs2, means)),
        latent_variance_rmse=sqrt(mean(abs2, variances .- 1)))
end

function write_results(rows)
    path = joinpath(@__DIR__, "results", OUTPUT)
    mkpath(dirname(path))
    names = propertynames(first(rows))
    open(path, "w") do io
        println(io, join(names, ','))
        for row in rows
            println(io, join((getproperty(row, name) for name in names), ','))
        end
    end
    path
end

function read_result_rows(path)
    lines = readlines(path)
    header = Symbol.(split(first(lines), ','))
    [NamedTuple{Tuple(header)}(Tuple(split(line, ',')))
        for line in @view lines[2:end]]
end

function best_no_failure_row(rows, algorithm)
    candidates = filter(row -> row.algorithm == algorithm &&
        parse(Int, row.failures) == 0 &&
        isfinite(parse(Float64, row.rank_normalized_rhat)), rows)
    isempty(candidates) ? nothing :
        argmax(row -> parse(Float64, row.tail_ess_per_transition), candidates)
end

function dimension_plot(summaries, field, title, ylabel)
    plot = nothing
    upper = maximum(Float64[getproperty(row, field) for row in summaries])
    limits = (0.0, upper * 1.05)
    for algorithm in ("hmc", "full-rmhmc", "random-sketch-rmhmc")
        selected = sort(filter(row -> row.algorithm == algorithm, summaries);
            by=row -> row.dimension)
        isempty(selected) && continue
        dimensions = Float64[row.dimension for row in selected]
        values = Float64[getproperty(row, field) for row in selected]
        if isnothing(plot)
            plot = lineplot(dimensions, values; name=algorithm, title,
                xlabel="ambient dimension", ylabel, ylim=limits)
        else
            lineplot!(plot, dimensions, values; name=algorithm)
        end
    end
    plot
end

function dimension_sweep_main()
    dimensions = parse.(Int, split(ENV["GEOMETRY_STUDY_DIMENSIONS"], ','))
    all(>=(1), dimensions) || error(
        "GEOMETRY_STUDY_DIMENSIONS entries must be positive")
    result_paths = String[]
    for dimension in dimensions
        output = "$OUTPUT_PREFIX-dimension-$dimension.csv"
        command = `$(Base.julia_cmd()) --project=$(dirname(Base.active_project())) $(@__FILE__)`
        println("\n=== ambient dimension $dimension ===")
        run(addenv(command,
            "GEOMETRY_STUDY_CHILD" => "1",
            "GEOMETRY_STUDY_DIMENSION" => string(dimension),
            "GEOMETRY_STUDY_ROTATED" => "true",
            "GEOMETRY_STUDY_OUTPUT" => output))
        push!(result_paths, joinpath(@__DIR__, "results", output))
    end

    summaries = NamedTuple[]
    for (dimension, path) in zip(dimensions, result_paths)
        rows = read_result_rows(path)
        for algorithm in ("hmc", "full-rmhmc", "random-sketch-rmhmc")
            best = best_no_failure_row(rows, algorithm)
            isnothing(best) && continue
            push!(summaries, (; dimension, algorithm,
                probes=parse(Int, best.probes),
                step_size=parse(Float64, best.step_size),
                integration_time=parse(Float64, best.integration_time),
                bulk_ess_per_transition=parse(
                    Float64, best.bulk_ess_per_transition),
                tail_ess_per_transition=parse(
                    Float64, best.tail_ess_per_transition),
                bulk_ess_per_second=parse(Float64, best.bulk_ess_per_second),
                tail_ess_per_second=parse(Float64, best.tail_ess_per_second),
                rank_normalized_rhat=parse(Float64, best.rank_normalized_rhat)))
        end
    end

    isempty(summaries) && error("dimension sweep produced no stable rows")
    summary_path = joinpath(
        @__DIR__, "results", "$OUTPUT_PREFIX-dimensions.csv")
    open(summary_path, "w") do io
        names = propertynames(first(summaries))
        println(io, join(names, ','))
        for row in summaries
            println(io, join((getproperty(row, name) for name in names), ','))
        end
    end
    plots = [
        dimension_plot(summaries, :bulk_ess_per_transition,
            "Bulk mixing across dimension", "bulk ESS / transition"),
        dimension_plot(summaries, :tail_ess_per_transition,
            "Tail mixing across dimension", "tail ESS / transition"),
        dimension_plot(summaries, :tail_ess_per_second,
            "Tail efficiency across dimension", "tail ESS / second"),
    ]
    plot_path = joinpath(
        @__DIR__, "results", "$OUTPUT_PREFIX-dimensions.txt")
    open(plot_path, "w") do io
        first_plot = true
        for plot in plots
            isnothing(plot) && continue
            first_plot || println(io)
            for line in split(rstrip(string(plot)), '\n')
                println(io, rstrip(line))
            end
            first_plot = false
        end
    end
    for plot in plots
        isnothing(plot) || display(plot)
    end
    println("wrote $summary_path")
    println("wrote $plot_path")
end

function main()
    DIMENSION >= 1 || error("GEOMETRY_STUDY_DIMENSION must be positive")
    PROBE_SCHEDULE in ("fixed", "log2") || error(
        "GEOMETRY_STUDY_PROBE_SCHEDULE must be fixed or log2")
    0 < PROBES <= DIMENSION || error(
        "GEOMETRY_STUDY_PROBES must lie in 1:dimension")
    DRAWS >= 100 || error("GEOMETRY_STUDY_DRAWS must be at least 100")
    0 <= BURNIN < DRAWS || error(
        "GEOMETRY_STUDY_BURNIN must lie in 0:(draws - 1)")
    length(SEEDS) >= 2 || error("GEOMETRY_STUDY_SEEDS needs at least two seeds")
    probes = fixed_probes()
    rows = NamedTuple[]
    initialize_progress()
    all(algorithm -> algorithm in
        ("hmc", "full-rmhmc", "random-sketch-rmhmc"), ALGORITHMS) ||
        error("GEOMETRY_STUDY_ALGORITHMS contains an unknown algorithm")
    for algorithm in ALGORITHMS
        step_sizes = algorithm == "hmc" ? HMC_STEP_SIZES :
            algorithm == "full-rmhmc" ? FULL_RMHMC_STEP_SIZES :
            SKETCH_RMHMC_STEP_SIZES
        integration_times = algorithm == "hmc" ? HMC_INTEGRATION_TIMES :
            RMHMC_INTEGRATION_TIMES
        for integration_time in integration_times, step_size in step_sizes
            print("$algorithm epsilon=$step_size tau=$integration_time ... ")
            row = run_configuration(
                algorithm, probes, step_size, integration_time)
            push!(rows, row)
            write_results(rows)
            println("tail ESS/transition=$(round(row.tail_ess_per_transition; digits=4)), " *
                "tail ESS/s=$(round(row.tail_ess_per_second; digits=2))")
        end
    end
    println("\nBest configurations by tail ESS per transition:")
    for algorithm in ALGORITHMS
        candidates = filter(row -> row.algorithm == algorithm &&
            row.failures == 0 && isfinite(row.rank_normalized_rhat), rows)
        if isempty(candidates)
            println("$algorithm: no numerically stable configuration")
            continue
        end
        best = argmax(row -> row.tail_ess_per_transition, candidates)
        println("$algorithm: epsilon=$(best.step_size), tau=$(best.integration_time), " *
            "tail ESS/transition=$(round(best.tail_ess_per_transition; digits=4)), " *
            "tail ESS/s=$(round(best.tail_ess_per_second; digits=2)), " *
            "Rhat=$(round(best.rank_normalized_rhat; digits=3))")
    end
    println("wrote $(write_results(rows))")
end

if abspath(PROGRAM_FILE) == abspath(@__FILE__)
    haskey(ENV, "GEOMETRY_STUDY_DIMENSIONS") &&
        get(ENV, "GEOMETRY_STUDY_CHILD", "0") != "1" ?
        dimension_sweep_main() : main()
end
