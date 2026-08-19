using Random
using Statistics
using VerifiedSamplers

function summarize(name, seed, sampler, initial, draws, burnin,
        expected_mean, expected_variance, in_support)
    chain = sample(MersenneTwister(seed), sampler, initial, draws)
    retained = @view chain[(burnin + 1):end]
    println(join((name, seed, draws, burnin,
        count(!in_support, chain), mean(retained) - expected_mean,
        var(retained) - expected_variance), ','))
end

function main(arguments)
    seed = length(arguments) >= 1 ? parse(Int, arguments[1]) : 0x10a17
    draws = length(arguments) >= 2 ? parse(Int, arguments[2]) : 30_000
    burnin = length(arguments) >= 3 ? parse(Int, arguments[3]) : 3_000
    draws > 1 || throw(ArgumentError("draw count must exceed one"))
    0 <= burnin < draws - 1 || throw(ArgumentError(
        "burn-in must leave at least two retained draws"))

    println("transform,seed,draws,burnin,support_violations,mean_error,variance_error")
    summarize("positive-log", seed,
        PositiveTransformedRWMH(x -> -x, 0.8), 1.0, draws, burnin,
        1.0, 1.0, x -> isfinite(x) && x > 0)
    summarize("open-unit-artanh", seed + 1,
        OpenUnitTransformedRWMH(_ -> 0.0, 1.0), 0.5, draws, burnin,
        0.5, 1 / 12, x -> isfinite(x) && 0 < x < 1)
end

main(ARGS)
