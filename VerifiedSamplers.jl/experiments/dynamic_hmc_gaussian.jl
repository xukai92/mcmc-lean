using Random
using Statistics
using VerifiedSamplers

function summarize(name, seed, sampler, draws, burnin, dimension)
    chain = sample(MersenneTwister(seed), sampler, zeros(dimension), draws)
    retained = @view chain[:, (burnin + 1):end]
    means = vec(mean(retained; dims=2))
    variances = vec(var(retained; dims=2))
    previous = zeros(dimension)
    moves = 0
    for draw in axes(chain, 2)
        current = @view chain[:, draw]
        moves += any(current .!= previous)
        previous .= current
    end
    println(join((name, seed, draws, burnin, dimension,
        moves / draws, maximum(abs, means),
        maximum(abs.(variances .- 1))), ','))
end

function main(arguments)
    seed = length(arguments) >= 1 ? parse(Int, arguments[1]) : 0xd1a
    draws = length(arguments) >= 2 ? parse(Int, arguments[2]) : 10_000
    burnin = length(arguments) >= 3 ? parse(Int, arguments[3]) : 1_000
    dimension = length(arguments) >= 4 ? parse(Int, arguments[4]) : 2
    draws > 1 || throw(ArgumentError("draw count must exceed one"))
    0 <= burnin < draws - 1 || throw(ArgumentError(
        "burn-in must leave at least two retained draws"))
    dimension > 0 || throw(ArgumentError("dimension must be positive"))

    logdensity(q) = -sum(abs2, q) / 2
    gradient(q) = q
    samplers = (
        ("certified-spanning", CertifiedDynamicHMC(
            logdensity, gradient, 0.12, 8)),
        ("checked-first-stop", CheckedFirstStopDynamicHMC(
            logdensity, gradient, 0.12, 8)),
        ("completed-tree-c4", CompletedTreeC4DynamicHMC(
            logdensity, gradient, 0.12, 3)),
        ("checked-recursive", CheckedRecursiveDynamicHMC(
            logdensity, gradient, 0.12, 8)),
    )

    println("algorithm,seed,draws,burnin,dimension,movement_rate,max_abs_mean,max_abs_variance_error")
    for (offset, (name, sampler)) in enumerate(samplers)
        summarize(name, seed + offset - 1, sampler, draws, burnin, dimension)
    end
end

main(ARGS)
