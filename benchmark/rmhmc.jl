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
    VerifiedSamplers.sample(
        MersenneTwister(seed), sampler, zeros(DIMENSION), DRAWS)
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
    for index in axes(chain, 2)
        transition = AdvancedHMC.transition(
            rng, hamiltonian, components.kernel, transition.z)
        chain[:, index] = transition.z.θ
    end
    chain
end

function measure(label, run)
    run(first(SEEDS))
    seconds = Float64[]
    bytes = Int[]
    means = Float64[]
    variances = Float64[]
    for seed in SEEDS
        GC.gc()
        trial = @timed run(seed)
        push!(seconds, trial.time)
        push!(bytes, trial.bytes)
        push!(means, maximum(abs, vec(mean(trial.value; dims=2))))
        push!(variances,
            maximum(abs, vec(var(trial.value; dims=2)) .- 1))
    end
    (; implementation=label, median_seconds=median(seconds),
        transitions_per_second=DRAWS / median(seconds),
        median_bytes=Int(median(bytes)),
        max_mean_error=maximum(means), max_variance_error=maximum(variances))
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
end

main()
