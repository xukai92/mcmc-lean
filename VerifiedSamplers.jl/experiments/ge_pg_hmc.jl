using Random
using Statistics
using VerifiedSamplers

function main(arguments)
    seed = length(arguments) >= 1 ? parse(Int, arguments[1]) : 0x6e18
    draws = length(arguments) >= 2 ? parse(Int, arguments[2]) : 30_000
    burnin = length(arguments) >= 3 ? parse(Int, arguments[3]) : 3_000
    draws > 1 || throw(ArgumentError("draw count must exceed one"))
    0 <= burnin < draws - 1 || throw(ArgumentError(
        "burn-in must leave at least two retained draws"))

    particle_gibbs = function (rng, state)
        probability_true = 1 / (1 + exp(-2 * state.continuous))
        merge(state, (latent=rand(rng) < probability_true,))
    end
    hamiltonian_monte_carlo = function (rng, state)
        location = state.latent ? 1.0 : -1.0
        conditional = ScalarHMC(
            x -> -(x - location)^2 / 2,
            x -> x - location, 0.2, 8)
        merge(state, (continuous=step(rng, conditional, state.continuous),))
    end
    sampler = generated_schedule("ge-pg-hmc", Dict(
        "particle-gibbs" => particle_gibbs,
        "hamiltonian-monte-carlo" => hamiltonian_monte_carlo))
    chain = sample(MersenneTwister(seed), sampler,
        (latent=false, continuous=0.0), draws)
    retained = @view chain[(burnin + 1):end]
    latent_frequency = mean(state.latent for state in retained)
    continuous = [state.continuous for state in retained]

    println("seed,draws,burnin,latent_frequency,continuous_mean,continuous_variance")
    println(join((seed, draws, burnin, latent_frequency,
        mean(continuous), var(continuous)), ','))
end

main(ARGS)
