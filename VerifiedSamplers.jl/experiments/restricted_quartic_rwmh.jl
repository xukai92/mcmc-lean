using Random
using Statistics
using VerifiedSamplers

function summarize(algorithm, seed, configuration, sampler, draws, burnin)
    chain = sample(MersenneTwister(seed), sampler, 0.0, draws)
    retained = @view chain[(burnin + 1):end]
    previous = 0.0
    moves = 0
    for current in chain
        moves += current != previous
        previous = current
    end
    println(join((algorithm, seed, draws, burnin, configuration,
        moves / draws, mean(retained), mean(abs2, retained),
        mean(x -> x^4, retained)), ','))
end

function main(arguments)
    seed = length(arguments) >= 1 ? parse(Int, arguments[1]) : 0x71a4
    draws = length(arguments) >= 2 ? parse(Int, arguments[2]) : 20_000
    burnin = length(arguments) >= 3 ? parse(Int, arguments[3]) : 2_000
    scale = length(arguments) >= 4 ? parse(Float64, arguments[4]) : 0.8

    draws > 1 || throw(ArgumentError("draw count must exceed one"))
    0 <= burnin < draws - 1 || throw(ArgumentError(
        "burn-in must leave at least two retained draws"))
    isfinite(scale) && scale > 0 || throw(ArgumentError(
        "proposal scale must be finite and positive"))

    samplers = (
        ("rwmh", string("scale=", scale),
            restricted_potential_rwmh(restricted_quartic_potential, scale)),
        ("hmc", "step_size=0.15;steps=6",
            restricted_potential_hmc(
                restricted_quartic_potential, 0.15, 6)),
        ("slice", "width=0.5;max_steps=20",
            restricted_potential_slice(
                restricted_quartic_potential, 0.5; max_steps=20)),
    )
    println("algorithm,seed,draws,burnin,configuration,movement_rate,mean,second_moment,fourth_moment")
    for (offset, (algorithm, configuration, sampler)) in enumerate(samplers)
        summarize(algorithm, seed + offset - 1, configuration, sampler,
            draws, burnin)
    end
end

main(ARGS)
