using AdvancedHMC
using LinearAlgebra
using Random
using Statistics
using VerifiedSamplers

# AdvancedHMC 0.8 ships the classical Riemannian Hamiltonian source but does
# not load its metric into the public module. Load that pinned source explicitly
# so this benchmark measures the actual upstream implementation rather than
# substituting ordinary Euclidean leapfrog.
if !isdefined(AdvancedHMC, :DenseRiemannianMetric)
    Core.eval(AdvancedHMC, :(using LinearAlgebra: logdet))
    Base.include(AdvancedHMC,
        joinpath(dirname(pathof(AdvancedHMC)), "riemannian", "hamiltonian.jl"))
end

const DIMENSION = parse(Int, get(ENV, "RMHMC_DIMENSION", "5"))
const DRAWS = parse(Int, get(ENV, "RMHMC_DRAWS", "1000"))
const STEPS = parse(Int, get(ENV, "RMHMC_STEPS", "10"))
const STEP_SIZE = parse(Float64, get(ENV, "RMHMC_STEP_SIZE", "0.1"))
const SOLVER_ITERATIONS = parse(Int, get(ENV, "RMHMC_SOLVER_ITERATIONS", "10"))
const RESIDUAL_TOLERANCE = parse(Float64,
    get(ENV, "RMHMC_RESIDUAL_TOLERANCE", "1e-8"))
const SEEDS = parse.(Int, split(get(ENV, "RMHMC_SEEDS", "7101,7102,7103"), ','))

potential(q) = sum(abs2, q) / 2
potential_gradient(q) = q
metric(q) = Matrix(Diagonal(2 .+ sin.(q)))
function metric_derivative(q)
    derivative = zeros(length(q), length(q), length(q))
    for coordinate in eachindex(q)
        derivative[coordinate, coordinate, coordinate] = cos(q[coordinate])
    end
    derivative
end

function verified_chain(implementation, seed)
    sampler = DenseRiemannianRMHMC(potential, potential_gradient, metric,
        metric_derivative, STEP_SIZE, STEPS;
        solver_iterations=SOLVER_ITERATIONS, solver_tolerance=0.0,
        residual_tolerance=RESIDUAL_TOLERANCE, implementation)
    chain = VerifiedSamplers.sample(
        MersenneTwister(seed), sampler, zeros(DIMENSION), DRAWS)
    (; chain, acceptance=NaN, divergences=0,
        average_steps=Float64(STEPS))
end

function advanced_components()
    metric = AdvancedHMC.DenseRiemannianMetric(
        (DIMENSION,), Main.metric, Main.metric_derivative)
    logdensity(q) = -sum(abs2, q) / 2
    logdensity_gradient(q) = (logdensity(q), -q)
    hamiltonian = AdvancedHMC.Hamiltonian(metric,
        AdvancedHMC.GaussianKinetic(), logdensity, logdensity_gradient)
    integrator = AdvancedHMC.GeneralizedLeapfrog(
        STEP_SIZE, SOLVER_ITERATIONS)
    kernel = AdvancedHMC.HMCKernel(AdvancedHMC.Trajectory{
        AdvancedHMC.EndPointTS}(integrator, AdvancedHMC.FixedNSteps(STEPS)))
    (; hamiltonian, kernel)
end

function advanced_chain(components, seed)
    rng = MersenneTwister(seed)
    hamiltonian, transition = AdvancedHMC.sample_init(
        rng, components.hamiltonian, zeros(DIMENSION))
    chain = Matrix{Float64}(undef, DIMENSION, DRAWS)
    acceptance = 0.0
    divergences = 0
    for index in axes(chain, 2)
        transition = AdvancedHMC.transition(
            rng, hamiltonian, components.kernel, transition.z)
        chain[:, index] = transition.z.θ
        acceptance += transition.stat.acceptance_rate
        divergences += transition.stat.numerical_error
    end
    (; chain, acceptance=acceptance / DRAWS, divergences,
        average_steps=Float64(STEPS))
end

function measure(label, run)
    run(first(SEEDS))
    seconds = Float64[]
    bytes = Int[]
    means = Float64[]
    variances = Float64[]
    outputs = Any[]
    for seed in SEEDS
        GC.gc()
        trial = @timed run(seed)
        push!(seconds, trial.time)
        push!(bytes, trial.bytes)
        push!(outputs, trial.value)
        push!(means, maximum(abs, vec(mean(trial.value.chain; dims=2))))
        push!(variances,
            maximum(abs, vec(var(trial.value.chain; dims=2)) .- 1))
    end
    (; implementation=label, median_seconds=median(seconds),
        transitions_per_second=DRAWS / median(seconds),
        median_bytes=Int(median(bytes)),
        max_mean_error=maximum(means), max_variance_error=maximum(variances),
        seconds, bytes, outputs)
end

function summary_row(row)
    (; target="position-dependent-gaussian", dimension=DIMENSION,
        algorithm="rmhmc-dense", implementation=row.implementation,
        step_size=STEP_SIZE, configured_steps=STEPS,
        average_steps=mean(output.average_steps for output in row.outputs),
        draws=DRAWS, median_seconds=row.median_seconds,
        q25_seconds=quantile(row.seconds, 0.25),
        q75_seconds=quantile(row.seconds, 0.75),
        draws_per_second=row.transitions_per_second,
        memory_bytes=Int(median(row.bytes)), allocations="n/a")
end

function timing_rows(row)
    [(; target="position-dependent-gaussian", dimension=DIMENSION,
        algorithm="rmhmc-dense", implementation=row.implementation,
        repetition, seed, seconds,
        draws_per_second=DRAWS / seconds)
        for (repetition, (seed, seconds)) in enumerate(zip(SEEDS, row.seconds))]
end

function quality_row(row)
    chains = getproperty.(row.outputs, :chain)
    burnin = DRAWS ÷ 10
    retained = [@view chain[:, (burnin + 1):end] for chain in chains]
    combined = reduce(hcat, retained)
    coordinates = min(4, DIMENSION)
    diagnostics = VerifiedSamplers.Evaluation.moment_diagnostics(
        combined, zeros(DIMENSION), ones(DIMENSION);
        ess_coordinates=coordinates)
    ranks = [VerifiedSamplers.Evaluation.split_rank_diagnostics(
        hcat([vec(@view chain[coordinate, :]) for chain in retained]...))
        for coordinate in 1:coordinates]
    standard_errors = [VerifiedSamplers.Evaluation.batch_mean_standard_error(chain)
        for chain in retained]
    mean_mcse = maximum(sqrt(sum(error[coordinate]^2
        for error in standard_errors)) / length(standard_errors)
        for coordinate in 1:DIMENSION)
    movement = mean(mean(any(@view(chain[:, index]) .!=
        @view(chain[:, index - 1])) for index in 2:size(chain, 2))
        for chain in chains)
    acceptance_values = filter(isfinite, getproperty.(row.outputs, :acceptance))
    total_seconds = sum(row.seconds)
    (; target="position-dependent-gaussian", dimension=DIMENSION,
        algorithm="rmhmc-dense", implementation=row.implementation,
        chains=length(chains), draws_per_chain=DRAWS,
        retained_draws=diagnostics.retained_draws, seconds=total_seconds,
        draws_per_second=DRAWS * length(chains) / total_seconds,
        minimum_ess=diagnostics.minimum_ess,
        ess_per_second=diagnostics.minimum_ess / total_seconds,
        rank_normalized_rhat=maximum(x.rank_normalized_rhat for x in ranks),
        bulk_ess=minimum(x.bulk_ess for x in ranks),
        tail_ess=minimum(x.tail_ess for x in ranks),
        bulk_ess_per_gradient_proxy=NaN, mean_mcse,
        covariance_max_error=VerifiedSamplers.Evaluation.covariance_max_error(
            combined, Matrix{Float64}(I, DIMENSION, DIMENSION)),
        median_max_error=VerifiedSamplers.Evaluation.marginal_quantile_max_error(
            combined, [0.5], zeros(DIMENSION, 1)),
        standardized_mean_rmse=diagnostics.standardized_mean_rmse,
        relative_variance_rmse=diagnostics.relative_variance_rmse,
        movement, acceptance=isempty(acceptance_values) ? NaN :
            mean(acceptance_values),
        divergences=sum(getproperty.(row.outputs, :divergences)),
        average_steps=Float64(STEPS))
end

function write_csv(path, rows)
    names = propertynames(first(rows))
    open(path, "w") do io
        println(io, join(names, ','))
        for row in rows
            println(io, join((getproperty(row, name) for name in names), ','))
        end
    end
end

function write_results(rows)
    results = joinpath(@__DIR__, "results")
    mkpath(results)
    write_csv(joinpath(results, "rmhmc.csv"), summary_row.(rows))
    write_csv(joinpath(results, "rmhmc-timings.csv"),
        reduce(vcat, timing_rows.(rows)))
    write_csv(joinpath(results, "rmhmc-quality.csv"), quality_row.(rows))
    open(joinpath(results, "rmhmc-metadata.csv"), "w") do io
        commit = readchomp(`git -C $(joinpath(@__DIR__, "..")) rev-parse --short HEAD`)
        println(io, "commit,$commit")
        println(io, "julia,$VERSION")
        println(io, "cpu,$(Sys.cpu_info()[1].model)")
        println(io, "dimension,$DIMENSION")
        println(io, "draws,$DRAWS")
        println(io, "steps,$STEPS")
        println(io, "step_size,$STEP_SIZE")
        println(io, "solver_iterations,$SOLVER_ITERATIONS")
        println(io, "residual_tolerance,$RESIDUAL_TOLERANCE")
    end
end

function main()
    DIMENSION > 0 || error("RMHMC_DIMENSION must be positive")
    DRAWS > 1 || error("RMHMC_DRAWS must exceed one")
    STEPS > 0 || error("RMHMC_STEPS must be positive")
    STEP_SIZE > 0 || error("RMHMC_STEP_SIZE must be positive")
    SOLVER_ITERATIONS > 0 || error("RMHMC_SOLVER_ITERATIONS must be positive")
    RESIDUAL_TOLERANCE >= 0 || error(
        "RMHMC_RESIDUAL_TOLERANCE must be nonnegative")
    length(SEEDS) >= 2 || error("RMHMC_SEEDS must contain at least two seeds")

    advanced = advanced_components()
    rows = [
        measure("verified-reference", seed -> verified_chain(:reference, seed)),
        measure("verified-optimized", seed -> verified_chain(:optimized, seed)),
        measure("advancedhmc", seed -> advanced_chain(advanced, seed)),
    ]

    println("classical RMHMC nonconstant dense-metric benchmark")
    println("dimension=$DIMENSION draws=$DRAWS steps=$STEPS " *
        "step_size=$STEP_SIZE solver_iterations=$SOLVER_ITERATIONS " *
        "residual_tolerance=$RESIDUAL_TOLERANCE")
    println("implementation,median_seconds,transitions_per_second,median_bytes," *
        "max_mean_error,max_variance_error")
    for row in rows
        println(join((row.implementation, row.median_seconds,
            row.transitions_per_second, row.median_bytes,
            row.max_mean_error, row.max_variance_error), ','))
    end
    write_results(rows)
end

main()
