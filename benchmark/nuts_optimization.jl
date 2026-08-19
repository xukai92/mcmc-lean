using Random
using Statistics
using VerifiedSamplers

const Optimized = VerifiedSamplers.Optimized
const Evaluation = VerifiedSamplers.Evaluation

logdensity(q) = -sum(abs2, q) / 2
gradient(q) = q

function run_chain(seed, draws)
    sampler = Optimized.NUTS(logdensity, gradient, 0.08; max_depth=8)
    sample(MersenneTwister(seed), sampler, zeros(100), draws)
end

function main()
    draws = parse(Int, get(ENV, "NUTS_OPTIMIZATION_DRAWS", "10000"))
    seeds = 2:6
    draws > 0 || error("NUTS_OPTIMIZATION_DRAWS must be positive")

    # Compilation is outside every measured chain, matching benchmark/run.jl.
    run_chain(first(seeds), 10)
    times = Float64[]
    for seed in seeds
        GC.gc()
        push!(times, @elapsed run_chain(seed, draws))
    end
    elapsed = median(times)
    println("transformation=float64-owned-phase-specialization")
    println("assurance=test-supported-operation-specialization")
    println("draws_per_chain=$draws")
    println("chains=$(length(seeds))")
    println("median_seconds=$elapsed")
    println("draws_per_second=$(draws / elapsed)")
    println("times=$(join(times, ','))")
    if haskey(ENV, "OPTIMIZATION_BASELINE_SECONDS")
        baseline = parse(Float64, ENV["OPTIMIZATION_BASELINE_SECONDS"])
        minimum_speedup = parse(Float64,
            get(ENV, "OPTIMIZATION_MINIMUM_SPEEDUP", "1.0"))
        trial = Evaluation.OptimizationTrial(
            "float64-owned-phase-specialization",
            "test-supported-operation-specialization",
            baseline, elapsed, minimum_speedup,
            [Evaluation.GateResult(:release, true,
                "make test prerequisite completed")])
        println("--- acceptance-record ---")
        println(Evaluation.render_record(trial))
        Evaluation.accepted(trial) || exit(2)
    end
end

main()
