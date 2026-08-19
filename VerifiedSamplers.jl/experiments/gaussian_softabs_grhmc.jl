using Random
using Statistics
using VerifiedSamplers

function main(arguments)
    seed = length(arguments) >= 1 ? parse(Int, arguments[1]) : 0x6a55
    draws = length(arguments) >= 2 ? parse(Int, arguments[2]) : 20_000
    burnin = length(arguments) >= 3 ? parse(Int, arguments[3]) : 2_000
    dimension = length(arguments) >= 4 ? parse(Int, arguments[4]) : 2
    draws > 1 || throw(ArgumentError("draw count must exceed one"))
    0 <= burnin < draws - 1 || throw(ArgumentError(
        "burn-in must leave at least two retained draws"))
    dimension > 0 || throw(ArgumentError("dimension must be positive"))

    sampler = GaussianSoftAbsGRHMC(dimension, 0.2, 10;
        smoothing=1.0, relativistic_mass=1.0)
    chain = sample(MersenneTwister(seed), sampler, zeros(dimension), draws)
    retained = @view chain[:, (burnin + 1):end]
    means = vec(mean(retained; dims=2))
    variances = vec(var(retained; dims=2))
    movement = mean(any(chain[:, index] .!=
        (index == 1 ? zeros(dimension) : chain[:, index - 1]))
        for index in axes(chain, 2))

    println("seed,draws,burnin,dimension,movement_rate,max_abs_mean,max_abs_variance_error")
    println(join((seed, draws, burnin, dimension, movement,
        maximum(abs, means), maximum(abs.(variances .- 1))), ','))
end

main(ARGS)
