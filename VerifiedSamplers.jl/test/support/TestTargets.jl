module TestTargets

using LinearAlgebra

export Target, suite

struct Target{F,G,M,C}
    name::String
    logdensity::F
    gradient::G
    mean::Vector{Float64}
    variance::Vector{Float64}
    metric_mass::M
    advanced_inverse_mass::C
end

softplus(x) = max(x, zero(x)) + log1p(exp(-abs(x)))
sigmoid(x) = x >= 0 ? inv(1 + exp(-x)) : exp(x) / (1 + exp(x))

function suite(dimension::Integer)
    dimension >= 2 || throw(ArgumentError("target dimension must be at least two"))
    zeros_d = zeros(dimension)

    isotropic = Target("isotropic-gaussian", q -> -sum(abs2, q) / 2,
        q -> q, zeros_d, ones(dimension), nothing, nothing)

    ρ = 0.9
    covariance = [ρ^abs(i - j) for i in 1:dimension, j in 1:dimension]
    precision = inv(Symmetric(covariance))
    correlated = Target("correlated-gaussian-rho-0.9",
        q -> -dot(q, precision * q) / 2, q -> precision * q,
        zeros_d, ones(dimension), Matrix(precision), covariance)

    # Marginal variances were independently evaluated by symmetric numerical
    # quadrature on [-8, 8] with grid spacing 1e-5.
    quartic = Target("product-quartic",
        q -> -sum(x -> x^4 / 4 + x^2 / 2, q), q -> q .^ 3 .+ q,
        zeros_d, fill(0.4679174991050355, dimension), nothing, nothing)

    variances = exp.(range(log(1e-2), log(1e2); length=dimension))
    ill_precision = 1 ./ variances
    ill_conditioned = Target("ill-conditioned-gaussian",
        q -> -sum(ill_precision .* abs2.(q)) / 2,
        q -> ill_precision .* q, zeros_d, variances,
        ill_precision, variances)

    logistic = Target("regularized-logistic",
        q -> -sum(x -> x^2 / 2 + 2softplus(x) - x, q),
        q -> q .+ 2 .* sigmoid.(q) .- 1,
        zeros_d, fill(0.6980113785451478, dimension), nothing, nothing)

    [isotropic, correlated, quartic, ill_conditioned, logistic]
end

end
