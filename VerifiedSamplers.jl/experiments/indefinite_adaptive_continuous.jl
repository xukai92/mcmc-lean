using Random
using Statistics
using VerifiedSamplers

function main(arguments)
    seed = length(arguments) >= 1 ? parse(Int, arguments[1]) : 0xc017
    draws = length(arguments) >= 2 ? parse(Int, arguments[2]) : 40_000
    tail = length(arguments) >= 3 ? parse(Int, arguments[3]) : 10_000
    draws > 0 || throw(ArgumentError("draw count must be positive"))
    1 < tail <= draws || throw(ArgumentError(
        "tail length must exceed one and not exceed the draw count"))

    sampler = IndefiniteAdaptiveContinuousRefresh(randn)
    println("initial,seed,draws,tail,tail_mean,tail_variance")
    for (offset, initial) in enumerate((-4.0, 4.0))
        local_seed = seed + offset - 1
        chain = sample(MersenneTwister(local_seed), sampler, initial, draws)
        retained = @view chain[(end - tail + 1):end]
        println(join((initial, local_seed, draws, tail,
            mean(retained), var(retained)), ','))
    end
end

main(ARGS)
