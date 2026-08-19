using Random
using Statistics
using VerifiedSamplers

function main(arguments)
    seed = length(arguments) >= 1 ? parse(Int, arguments[1]) : 0xada7
    warmup_draws = length(arguments) >= 2 ? parse(Int, arguments[2]) : 1_000
    retained_draws = length(arguments) >= 3 ? parse(Int, arguments[3]) : 20_000
    warmup_draws >= 0 || throw(ArgumentError(
        "warmup iteration count must be nonnegative"))
    retained_draws >= 2 || throw(ArgumentError(
        "retained draw count must be at least two"))

    config = WarmupGaussianRWMH(x -> -x^2 / 2, 0.15, warmup_draws;
        target_accept=0.44, learning_rate=0.6,
        min_scale=0.05, max_scale=4.0)
    rng = MersenneTwister(seed)
    result = warmup(rng, config, 0.0)
    retained = sample(rng, result.sampler, result.state, retained_draws)
    acceptance = isempty(result.accepted) ? NaN : mean(result.accepted)

    println("seed,warmup_iterations,retained_draws,frozen_scale,warmup_acceptance,retained_mean,retained_variance")
    println(join((seed, warmup_draws, retained_draws, result.sampler.scale,
        acceptance, mean(retained), var(retained)), ','))
end

main(ARGS)
