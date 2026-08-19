using Random
using Statistics
using VerifiedSamplers

const Optimized = VerifiedSamplers.Optimized

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
end

main()
