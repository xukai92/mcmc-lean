using Random
using Statistics
using VerifiedSamplers

function main(arguments)
    seed = length(arguments) >= 1 ? parse(Int, arguments[1]) : 0x1def
    draws = length(arguments) >= 2 ? parse(Int, arguments[2]) : 40_000
    tail = length(arguments) >= 3 ? parse(Int, arguments[3]) : 10_000
    draws > 0 || throw(ArgumentError("draw count must be positive"))
    1 <= tail <= draws || throw(ArgumentError(
        "tail length must lie between one and the draw count"))

    sampler = IndefiniteAdaptiveBool()
    println("initial,seed,draws,tail,tail_true_frequency,tail_absolute_error")
    for (offset, initial) in enumerate((false, true))
        local_seed = seed + offset - 1
        chain = sample(MersenneTwister(local_seed), sampler, initial, draws)
        frequency = mean(@view chain[(end - tail + 1):end])
        println(join((initial, local_seed, draws, tail, frequency,
            abs(frequency - 0.5)), ','))
    end
end

main(ARGS)
