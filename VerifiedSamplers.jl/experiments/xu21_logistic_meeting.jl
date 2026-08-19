using Random
using LinearAlgebra
using VerifiedSamplers

softplus(x) = max(x, 0.0) + log1p(exp(-abs(x)))

function main(arguments)
    seed = length(arguments) >= 1 ? parse(Int, arguments[1]) : 2021
    replicates = length(arguments) >= 2 ? parse(Int, arguments[2]) : 100
    horizon = length(arguments) >= 3 ? parse(Int, arguments[3]) : 2_000

    covariates = ([1.0, -0.5], [0.25, 1.0], [-0.75, 0.5], [0.5, 0.75])
    labels = (1.0, 1.0, -1.0, -1.0)
    regularization = 1.0
    potential(q) = regularization * sum(abs2, q) / 2 +
        sum(softplus(-label * dot(covariate, q))
            for (covariate, label) in zip(covariates, labels))
    function gradient(q)
        result = regularization .* Float64.(q)
        for (covariate, label) in zip(covariates, labels)
            margin = label * dot(covariate, q)
            reciprocal = margin >= 0 ? exp(-margin) / (1 + exp(-margin)) :
                1 / (1 + exp(margin))
            result .-= (label * reciprocal) .* covariate
        end
        result
    end

    sampler = Xu21CoupledSampler(q -> -potential(q), gradient,
        0.08, 4, 0.45, 0.8)
    diagnostic = coupled_meeting_diagnostic(MersenneTwister(seed), sampler,
        ([-1.0, 1.0], [1.0, -1.0]), replicates, horizon)

    println("seed,replicates,horizon,met,censored,meeting_fraction,observed_mean,restricted_mean")
    println(join((seed, replicates, horizon, diagnostic.met,
        diagnostic.censored, diagnostic.meeting_fraction,
        diagnostic.observed_mean, diagnostic.restricted_mean), ','))
end

main(ARGS)
