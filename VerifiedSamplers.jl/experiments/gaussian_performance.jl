using LinearAlgebra
using Random
using Statistics
using VerifiedSamplers

function autocorrelation_ess(values; max_lag=min(1_000, length(values) ÷ 4))
    centered = values .- mean(values)
    variance = sum(abs2, centered) / length(centered)
    variance > 0 || return 0.0
    correlation_sum = 0.0
    for lag in 1:max_lag
        correlation = dot(@view(centered[1:(end - lag)]),
            @view(centered[(lag + 1):end])) /
            ((length(centered) - lag) * variance)
        correlation <= 0 && break
        correlation_sum += correlation
    end
    min(length(values), length(values) / (1 + 2correlation_sum))
end

movement_rate(chain, initial) = begin
    previous = initial
    moves = 0
    for current in chain
        moves += current != previous
        previous = current
    end
    moves / length(chain)
end

function run_rwmh(seed, draws, burnin)
    logdensity_calls = Ref(0)
    logdensity(x) = (logdensity_calls[] += 1; -x^2 / 2)
    chain = sample(MersenneTwister(seed), GaussianRWMH(logdensity, 1.0),
        0.0, draws)
    retained = @view chain[(burnin + 1):end]
    (; algorithm="rwmh", seed, draws, burnin,
        movement=movement_rate(chain, 0.0), ess=autocorrelation_ess(retained),
        ess_per_gradient=NaN, gradient_calls=0,
        logdensity_calls=logdensity_calls[])
end

function run_hmc(seed, draws, burnin)
    logdensity_calls = Ref(0)
    gradient_calls = Ref(0)
    logdensity(x) = (logdensity_calls[] += 1; -x^2 / 2)
    gradient(x) = (gradient_calls[] += 1; x)
    chain = sample(MersenneTwister(seed),
        ScalarHMC(logdensity, gradient, 0.20, 10), 0.0, draws)
    retained = @view chain[(burnin + 1):end]
    ess = autocorrelation_ess(retained)
    summary = (; algorithm="hmc", seed, draws, burnin,
        movement=movement_rate(chain, 0.0), ess,
        ess_per_gradient=ess / gradient_calls[],
        gradient_calls=gradient_calls[],
        logdensity_calls=logdensity_calls[])
    (; summary, chain)
end

function run_optimized_hmc(seed, draws, burnin)
    logdensity_calls = Ref(0)
    gradient_calls = Ref(0)
    logdensity(x) = (logdensity_calls[] += 1; -x^2 / 2)
    gradient(x) = (gradient_calls[] += 1; x)
    source = VerifiedSamplers.Runtime.RNGSource(MersenneTwister(seed))
    chain = Vector{Float64}(undef, draws)
    state = 0.0
    for index in eachindex(chain)
        state = VerifiedSamplers.Optimized.scalar_hmc_step!(source,
            logdensity, gradient, 0.20, 10, state)
        chain[index] = state
    end
    retained = @view chain[(burnin + 1):end]
    ess = autocorrelation_ess(retained)
    summary = (; algorithm="hmc-optimized", seed, draws, burnin,
        movement=movement_rate(chain, 0.0), ess,
        ess_per_gradient=ess / gradient_calls[],
        gradient_calls=gradient_calls[],
        logdensity_calls=logdensity_calls[])
    (; summary, chain)
end

function main(arguments)
    seed = length(arguments) >= 1 ? parse(Int, arguments[1]) : 0xe559
    draws = length(arguments) >= 2 ? parse(Int, arguments[2]) : 12_000
    burnin = length(arguments) >= 3 ? parse(Int, arguments[3]) : 2_000
    draws > 1 || throw(ArgumentError("draw count must exceed one"))
    0 <= burnin < draws - 1 || throw(ArgumentError(
        "burn-in must leave at least two retained draws"))

    println("algorithm,seed,draws,burnin,movement_rate,ess,ess_per_gradient,gradient_calls,logdensity_calls")
    reference_hmc = run_hmc(seed + 1, draws, burnin)
    optimized_hmc = run_optimized_hmc(seed + 1, draws, burnin)
    reference_hmc.chain == optimized_hmc.chain || error(
        "reference and optimized HMC chains disagree under identical draws")
    for result in (run_rwmh(seed, draws, burnin),
            reference_hmc.summary, optimized_hmc.summary)
        println(join((result.algorithm, result.seed, result.draws, result.burnin,
            result.movement, result.ess, result.ess_per_gradient,
            result.gradient_calls, result.logdensity_calls), ','))
    end
end

main(ARGS)
