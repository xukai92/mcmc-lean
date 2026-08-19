using Random
using VerifiedSamplers

function main(arguments)
    seed = length(arguments) >= 1 ? parse(Int, arguments[1]) : 2021
    replicates = length(arguments) >= 2 ? parse(Int, arguments[2]) : 100
    horizon = length(arguments) >= 3 ? parse(Int, arguments[3]) : 2_000

    logdensity(q) = -sum(abs2, q) / 2
    gradient(q) = q
    sampler = Xu21CoupledSampler(logdensity, gradient, 0.15, 3, 0.6, 0.8)
    diagnostic = coupled_meeting_diagnostic(MersenneTwister(seed), sampler,
        ([0.0, 0.0], [1.0, -1.0]), replicates, horizon)

    println("seed,replicates,horizon,met,censored,meeting_fraction,observed_mean,restricted_mean")
    println(join((seed, replicates, horizon, diagnostic.met,
        diagnostic.censored, diagnostic.meeting_fraction,
        diagnostic.observed_mean, diagnostic.restricted_mean), ','))
end

main(ARGS)
