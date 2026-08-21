using LinearAlgebra
using Random
using Statistics
using VerifiedSamplers

const DIMENSION = parse(Int, get(ENV, "SKETCH_RMHMC_DIMENSION", "20"))
const PROBES = parse(Int, get(ENV, "SKETCH_RMHMC_PROBES", "4"))
const DRAWS = parse(Int, get(ENV, "SKETCH_RMHMC_DRAWS", "500"))
const STEPS = parse(Int, get(ENV, "SKETCH_RMHMC_STEPS", "5"))
const STEP_SIZE = parse(Float64,
    get(ENV, "SKETCH_RMHMC_STEP_SIZE", "0.04"))
const SOLVER_ITERATIONS = parse(Int,
    get(ENV, "SKETCH_RMHMC_SOLVER_ITERATIONS", "20"))
const RESIDUAL_TOLERANCE = parse(Float64,
    get(ENV, "SKETCH_RMHMC_RESIDUAL_TOLERANCE", "1e-8"))
const SEEDS = parse.(Int, split(get(ENV,
    "SKETCH_RMHMC_SEEDS", "8121,8122,8123"), ','))
const PROBE_SEED = parse(Int, get(ENV, "SKETCH_RMHMC_PROBE_SEED", "8120"))
const RIDGE = parse(Float64, get(ENV, "SKETCH_RMHMC_RIDGE", "0.5"))
const BANANA = parse(Float64, get(ENV, "SKETCH_RMHMC_BANANA", "0.5"))

function potential(q)
    transformed_second = q[2] + BANANA * (q[1]^2 - 1)
    (q[1]^2 + transformed_second^2 + sum(abs2, @view q[3:end])) / 2
end
function potential_gradient(q)
    transformed_second = q[2] + BANANA * (q[1]^2 - 1)
    gradient = copy(q)
    gradient[1] = q[1] + 2BANANA * q[1] * transformed_second
    gradient[2] = transformed_second
    gradient
end
function curvature_action(q, probe)
    action = copy(probe)
    action[1] += 2BANANA * q[1] * probe[2]
    action
end
function curvature_action_derivative(q, probe)
    derivative = zeros(eltype(q), length(q), length(q))
    derivative[1, 1] = 2BANANA * probe[2]
    derivative
end

function full_metric(q)
    metric = Matrix{eltype(q)}(I, length(q), length(q)) .* (1 + RIDGE)
    slope = 2BANANA * q[1]
    metric[1, 1] += slope^2
    metric[1, 2] += slope
    metric[2, 1] += slope
    metric
end
function full_metric_derivative(q)
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

function sketch_sampler(probes; implementation=:optimized)
    RandomSketchRMHMC(potential, potential_gradient, curvature_action,
        curvature_action_derivative, probes, RIDGE, STEP_SIZE, STEPS;
        solver_iterations=SOLVER_ITERATIONS, solver_tolerance=0.0,
        residual_tolerance=RESIDUAL_TOLERANCE, implementation)
end

function dense_sampler(probes; implementation=:optimized)
    template = sketch_sampler(probes; implementation)
    DenseRiemannianRMHMC(potential, potential_gradient,
        q -> random_sketch_metric(template, q),
        q -> random_sketch_metric_derivative(template, q),
        STEP_SIZE, STEPS; solver_iterations=SOLVER_ITERATIONS,
        solver_tolerance=0.0, residual_tolerance=RESIDUAL_TOLERANCE,
        implementation)
end

function full_dense_sampler(; implementation=:optimized)
    DenseRiemannianRMHMC(potential, potential_gradient, full_metric,
        full_metric_derivative, STEP_SIZE, STEPS;
        solver_iterations=SOLVER_ITERATIONS, solver_tolerance=0.0,
        residual_tolerance=RESIDUAL_TOLERANCE, implementation)
end

function run_chain(sampler, seed)
    sample(MersenneTwister(seed), sampler, zeros(DIMENSION), DRAWS)
end

ordinary_sampler() = VectorHMC(q -> -potential(q), q -> -potential_gradient(q),
    STEP_SIZE, STEPS)

function measure(algorithm, sampler)
    run_chain(sampler, first(SEEDS))
    seconds = Float64[]
    bytes = Int[]
    chains = Matrix{Float64}[]
    for seed in SEEDS
        GC.gc()
        trial = @timed run_chain(sampler, seed)
        push!(seconds, trial.time)
        push!(bytes, trial.bytes)
        push!(chains, trial.value)
    end
    burnin = DRAWS ÷ 10
    retained = [@view chain[:, (burnin + 1):end] for chain in chains]
    combined = reduce(hcat, retained)
    coordinates = min(4, DIMENSION)
    coordinate_ess = [sum(VerifiedSamplers.Evaluation.autocorrelation_ess(
        @view chain[coordinate, :]) for chain in retained)
        for coordinate in 1:coordinates]
    minimum_ess = minimum(coordinate_ess)
    total_seconds = sum(seconds)
    retained_transitions = sum(size(chain, 2) for chain in retained)
    target_variance = ones(DIMENSION)
    target_variance[2] = 1 + 2BANANA^2
    (; algorithm, dimension=DIMENSION, probes=PROBES, draws=DRAWS,
        steps=STEPS, median_seconds=median(seconds),
        draws_per_second=DRAWS / median(seconds),
        minimum_ess, ess_per_second=minimum_ess / total_seconds,
        ess_per_transition=minimum_ess / retained_transitions,
        ess_per_integrator_step=minimum_ess /
            (retained_transitions * STEPS),
        median_bytes=Int(median(bytes)),
        max_mean_error=maximum(abs, vec(mean(combined; dims=2))),
        max_variance_error=maximum(abs,
            vec(var(combined; dims=2)) .- target_variance),
        seconds)
end

function write_results(rows)
    path = joinpath(@__DIR__, "results", "random-sketch-rmhmc.csv")
    mkpath(dirname(path))
    open(path, "w") do io
        println(io, "algorithm,dimension,probes,draws,steps,median_seconds," *
            "draws_per_second,minimum_ess,ess_per_second,median_bytes," *
            "ess_per_transition,ess_per_integrator_step," *
            "max_mean_error,max_variance_error")
        for row in rows
            println(io, join((row.algorithm, row.dimension, row.probes,
                row.draws, row.steps, row.median_seconds,
                row.draws_per_second, row.minimum_ess, row.ess_per_second,
                row.median_bytes,
                row.ess_per_transition, row.ess_per_integrator_step,
                row.max_mean_error, row.max_variance_error), ','))
        end
    end
    path
end

function main()
    DIMENSION >= 2 || error("SKETCH_RMHMC_DIMENSION must be at least two")
    0 < PROBES <= DIMENSION || error(
        "SKETCH_RMHMC_PROBES must lie in 1:dimension")
    DRAWS > 1 || error("SKETCH_RMHMC_DRAWS must exceed one")
    length(SEEDS) >= 2 || error("SKETCH_RMHMC_SEEDS needs at least two seeds")
    probes = fixed_probes()
    rows = [
        measure("ordinary-hmc", ordinary_sampler()),
        measure("full-dense-rmhmc", full_dense_sampler()),
        measure("dense-materialized", dense_sampler(probes)),
        measure("random-sketch-structured", sketch_sampler(probes)),
    ]
    println("matched-metric dense versus structured random-sketch RMHMC")
    println("dimension=$DIMENSION probes=$PROBES draws=$DRAWS " *
        "steps=$STEPS solver_iterations=$SOLVER_ITERATIONS")
    for row in rows
        println("$(row.algorithm): $(round(row.ess_per_second; digits=2)) " *
            "minimum ESS/s, $(round(row.ess_per_integrator_step; digits=5)) " *
            "ESS/integrator-step, $(round(row.draws_per_second; digits=2)) " *
            "draws/s, $(round(row.median_seconds; digits=3)) s, " *
            "$(row.median_bytes) bytes")
    end
    speedup = rows[4].draws_per_second / rows[3].draws_per_second
    ess_speedup = rows[4].ess_per_second / rows[3].ess_per_second
    println("structured versus dense: $(round(speedup; digits=2))x draws/s, " *
        "$(round(ess_speedup; digits=2))x minimum ESS/s")
    println("wrote $(write_results(rows))")
end

abspath(PROGRAM_FILE) == abspath(@__FILE__) && main()
