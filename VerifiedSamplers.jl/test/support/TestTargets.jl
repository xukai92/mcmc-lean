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

"""Quadratic form for the inverse of an AR(1) correlation matrix in O(d)."""
function ar1_precision_quadratic(q, ρ)
    denominator = 1 - ρ^2
    value = q[1]^2 + q[end]^2
    @inbounds for index in 2:(length(q) - 1)
        value += (1 + ρ^2) * q[index]^2
    end
    @inbounds for index in 1:(length(q) - 1)
        value -= 2ρ * q[index] * q[index + 1]
    end
    value / denominator
end

"""Action of the inverse AR(1) correlation matrix in O(d)."""
function ar1_precision_mul(q, ρ)
    denominator = 1 - ρ^2
    result = similar(q)
    @inbounds begin
        result[1] = (q[1] - ρ * q[2]) / denominator
        for index in 2:(length(q) - 1)
            result[index] = ((1 + ρ^2) * q[index] -
                ρ * (q[index - 1] + q[index + 1])) / denominator
        end
        result[end] = (q[end] - ρ * q[end - 1]) / denominator
    end
    result
end

function suite(dimension::Integer)
    dimension >= 2 || throw(ArgumentError("target dimension must be at least two"))
    zeros_d = zeros(dimension)

    isotropic = Target("isotropic-gaussian", q -> -sum(abs2, q) / 2,
        q -> q, zeros_d, ones(dimension), nothing, nothing)

    ρ = 0.9
    covariance = [ρ^abs(i - j) for i in 1:dimension, j in 1:dimension]
    denominator = 1 - ρ^2
    precision_diagonal = fill((1 + ρ^2) / denominator, dimension)
    precision_diagonal[1] = 1 / denominator
    precision_diagonal[end] = 1 / denominator
    precision = Matrix(SymTridiagonal(precision_diagonal,
        fill(-ρ / denominator, dimension - 1)))
    correlated = Target("correlated-gaussian-rho-0.9",
        q -> -ar1_precision_quadratic(q, ρ) / 2,
        q -> ar1_precision_mul(q, ρ),
        zeros_d, ones(dimension), Matrix(precision), covariance)

    # Marginal variances were independently evaluated by symmetric numerical
    # quadrature on [-8, 8] with grid spacing 1e-5.
    quartic = Target("product-quartic",
        q -> -sum(x -> x^4 / 4 + x^2 / 2, q),
        q -> map(x -> x^3 + x, q),
        zeros_d, fill(0.4679174991050355, dimension), nothing, nothing)

    variances = exp.(range(log(1e-2), log(1e2); length=dimension))
    ill_precision = 1 ./ variances
    ill_conditioned = Target("ill-conditioned-gaussian",
        q -> -sum(index -> ill_precision[index] * abs2(q[index]),
            eachindex(q)) / 2,
        q -> map(*, ill_precision, q), zeros_d, variances,
        ill_precision, variances)

    logistic = Target("regularized-logistic",
        q -> -sum(x -> x^2 / 2 + 2softplus(x) - x, q),
        q -> map(x -> x + 2sigmoid(x) - 1, q),
        zeros_d, fill(0.6980113785451478, dimension), nothing, nothing)

    [isotropic, correlated, quartic, ill_conditioned, logistic]
end

end
