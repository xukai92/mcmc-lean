using Random
using Statistics
using VerifiedSamplers

function summarize(name, seed, sampler, draws, canonicalize)
    chain = sample(MersenneTwister(seed), sampler, nothing, draws)
    empty_fraction = count(isnothing, chain) / draws
    births = [canonicalize(state) for state in chain if state !== nothing]
    dimension = length(first(births))
    means = [mean(state[index] for state in births) for index in 1:dimension]
    variances = [var(state[index] for state in births) for index in 1:dimension]
    println(join((name, seed, draws, empty_fraction,
        maximum(abs, means), maximum(abs.(variances .- 4 / 3))), ','))
end

function main(arguments)
    seed = length(arguments) >= 1 ? parse(Int, arguments[1]) : 0x5eea
    draws = length(arguments) >= 2 ? parse(Int, arguments[2]) : 40_000
    draws >= 2 || throw(ArgumentError("draw count must be at least two"))
    iseven(draws) || throw(ArgumentError(
        "draw count must be even for the alternating birth/death diagnostic"))

    println("transport,seed,draws,empty_fraction,max_abs_canonical_mean,max_abs_canonical_variance_error")
    summarize("nonlinear-cubic-shear", seed, ShearedBirthDeathRJ(), draws,
        sheared_birth_unshear)
    summarize("three-dimensional-product", seed + 1,
        SpatialBirthDeathRJ(), draws, identity)
end

main(ARGS)
