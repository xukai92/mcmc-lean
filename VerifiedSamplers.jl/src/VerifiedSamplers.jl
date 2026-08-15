module VerifiedSamplers

using Random
using LinearAlgebra
import Base: step

include("Runtime/Runtime.jl")
include("Reference/Reference.jl")
include("Optimized/Optimized.jl")
include("Certificates/Certificates.jl")

export FiniteWeights, FiniteKernelWeights, FiniteMH, TwoStateMH, GaussianRWMH,
    ScalarHMC, VectorHMC, MultinomialHMC, MetricMultinomialHMC,
    DiagonalMetric, DenseMetric, MetricHMC, Xu21CoupledSampler, sample
export Certificates

struct Xu21CoupledSampler{F,G}
    logdensity::F
    gradient::G
    step_size::Float64
    steps::Int
    rwmh_scale::Float64
    hmc_weight::Float64
    function Xu21CoupledSampler(logdensity::F, gradient::G, step_size::Real,
            steps::Integer, rwmh_scale::Real, hmc_weight::Real=0.9) where {F,G}
        ε, σ, p = Float64(step_size), Float64(rwmh_scale), Float64(hmc_weight)
        isfinite(ε) && ε > 0 || throw(ArgumentError("step size must be positive"))
        steps > 0 || throw(ArgumentError("trajectory length must be positive"))
        isfinite(σ) && σ > 0 || throw(ArgumentError("RWMH scale must be positive"))
        isfinite(p) && 0 <= p <= 1 || throw(ArgumentError("HMC weight must lie in [0,1]"))
        new{F,G}(logdensity, gradient, ε, Int(steps), σ, p)
    end
end

function step(rng::AbstractRNG, sampler::Xu21CoupledSampler,
        current::Tuple{<:AbstractVector{<:Real},<:AbstractVector{<:Real}})
    Reference.xu21_coupled_step!(Runtime.RNGSource(rng), sampler.logdensity,
        sampler.gradient, sampler.step_size, sampler.steps, sampler.rwmh_scale,
        sampler.hmc_weight, current[1], current[2])
end

step(sampler::Xu21CoupledSampler, current::Tuple) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::Xu21CoupledSampler,
        initial::Tuple{<:AbstractVector{<:Real},<:AbstractVector{<:Real}},
        count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    left, right = Float64.(initial[1]), Float64.(initial[2])
    left_chain = Matrix{Float64}(undef, length(left), count)
    right_chain = similar(left_chain)
    met = falses(count)
    for index in 1:count
        left, right = step(rng, sampler, (left, right))
        left_chain[:, index], right_chain[:, index] = left, right
        met[index] = left == right
    end
    (left=left_chain, right=right_chain, met=met)
end

sample(sampler::Xu21CoupledSampler, initial::Tuple, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)

struct MultinomialHMC{F,G}
    logdensity::F
    gradient::G
    step_size::Float64
    steps::Int
    function MultinomialHMC(logdensity::F, gradient::G, step_size::Real,
            steps::Integer=10) where {F,G}
        converted = Float64(step_size)
        isfinite(converted) && converted > 0 ||
            throw(ArgumentError("step size must be finite and positive"))
        steps > 0 || throw(ArgumentError("trajectory length must be positive"))
        new{F,G}(logdensity, gradient, converted, Int(steps))
    end
end

function step(rng::AbstractRNG, sampler::MultinomialHMC,
        current::AbstractVector{<:Real})
    Reference.multinomial_hmc_step!(Runtime.RNGSource(rng), sampler.logdensity,
        sampler.gradient, sampler.step_size, sampler.steps, current)
end

step(sampler::MultinomialHMC, current::AbstractVector{<:Real}) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::MultinomialHMC,
        initial::AbstractVector{<:Real}, count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    current = Float64.(initial)
    samples = Matrix{Float64}(undef, length(current), count)
    for index in axes(samples, 2)
        current = step(rng, sampler, current)
        samples[:, index] = current
    end
    samples
end

sample(sampler::MultinomialHMC, initial::AbstractVector{<:Real}, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)

struct DiagonalMetric
    mass::Vector{Float64}
    function DiagonalMetric(mass::AbstractVector{<:Real})
        converted = Float64.(mass)
        isempty(converted) && throw(ArgumentError("mass cannot be empty"))
        all(x -> isfinite(x) && x > 0, converted) ||
            throw(ArgumentError("diagonal mass must be finite and positive"))
        new(converted)
    end
end

struct DenseMetric
    mass::Matrix{Float64}
    function DenseMetric(mass::AbstractMatrix{<:Real})
        converted = Matrix{Float64}(mass)
        size(converted, 1) == size(converted, 2) ||
            throw(DimensionMismatch("mass matrix must be square"))
        issymmetric(converted) || throw(ArgumentError("mass matrix must be symmetric"))
        isposdef(converted) || throw(ArgumentError("mass matrix must be positive definite"))
        new(converted)
    end
end

struct MetricHMC{F,G,M}
    logdensity::F
    gradient::G
    metric::M
    step_size::Float64
    steps::Int
    function MetricHMC(logdensity::F, gradient::G, metric::M,
            step_size::Real, steps::Integer=10) where {F,G,M<:Union{DiagonalMetric,DenseMetric}}
        converted = Float64(step_size)
        isfinite(converted) && converted > 0 ||
            throw(ArgumentError("step size must be finite and positive"))
        steps > 0 || throw(ArgumentError("leapfrog steps must be positive"))
        new{F,G,M}(logdensity, gradient, metric, converted, Int(steps))
    end
end

metric_mass(metric::DiagonalMetric) = metric.mass
metric_mass(metric::DenseMetric) = metric.mass

struct MetricMultinomialHMC{F,G,M}
    logdensity::F
    gradient::G
    metric::M
    step_size::Float64
    steps::Int
    function MetricMultinomialHMC(logdensity::F, gradient::G, metric::M,
            step_size::Real, steps::Integer=10) where
            {F,G,M<:Union{DiagonalMetric,DenseMetric}}
        converted = Float64(step_size)
        isfinite(converted) && converted > 0 ||
            throw(ArgumentError("step size must be finite and positive"))
        steps > 0 || throw(ArgumentError("trajectory length must be positive"))
        new{F,G,M}(logdensity, gradient, metric, converted, Int(steps))
    end
end

function step(rng::AbstractRNG, sampler::MetricMultinomialHMC,
        current::AbstractVector{<:Real})
    Reference.metric_multinomial_hmc_step!(Runtime.RNGSource(rng),
        sampler.logdensity, sampler.gradient, sampler.step_size, sampler.steps,
        current, metric_mass(sampler.metric))
end

step(sampler::MetricMultinomialHMC, current::AbstractVector{<:Real}) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::MetricMultinomialHMC,
        initial::AbstractVector{<:Real}, count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    current = Float64.(initial)
    samples = Matrix{Float64}(undef, length(current), count)
    for index in axes(samples, 2)
        current = step(rng, sampler, current)
        samples[:, index] = current
    end
    samples
end

sample(sampler::MetricMultinomialHMC, initial::AbstractVector{<:Real},
        count::Integer) = sample(Random.default_rng(), sampler, initial, count)

function step(rng::AbstractRNG, sampler::MetricHMC,
        current::AbstractVector{<:Real})
    Reference.metric_hmc_step!(Runtime.RNGSource(rng), sampler.logdensity,
        sampler.gradient, sampler.step_size, sampler.steps, current,
        metric_mass(sampler.metric))
end

step(sampler::MetricHMC, current::AbstractVector{<:Real}) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::MetricHMC,
        initial::AbstractVector{<:Real}, count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    current = Float64.(initial)
    samples = Matrix{Float64}(undef, length(current), count)
    for index in axes(samples, 2)
        current = step(rng, sampler, current)
        samples[:, index] = current
    end
    samples
end

sample(sampler::MetricHMC, initial::AbstractVector{<:Real}, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)

struct VectorHMC{F,G}
    logdensity::F
    gradient::G
    step_size::Float64
    steps::Int
    function VectorHMC{F,G}(logdensity::F, gradient::G,
            step_size::Float64, steps::Int) where {F,G}
        isfinite(step_size) && step_size > 0.0 ||
            throw(ArgumentError("step size must be finite and positive"))
        steps > 0 || throw(ArgumentError("leapfrog steps must be positive"))
        new{F,G}(logdensity, gradient, step_size, steps)
    end
end

VectorHMC(logdensity::F, gradient::G, step_size::Real,
    steps::Integer=10) where {F,G} =
    VectorHMC{F,G}(logdensity, gradient, Float64(step_size), Int(steps))

function step(rng::AbstractRNG, sampler::VectorHMC,
        current::AbstractVector{<:Real})
    Reference.vector_hmc_step!(Runtime.RNGSource(rng), sampler.logdensity,
        sampler.gradient, sampler.step_size, sampler.steps, current)
end

step(sampler::VectorHMC, current::AbstractVector{<:Real}) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::VectorHMC,
        initial::AbstractVector{<:Real}, count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    current = Float64.(initial)
    samples = Matrix{Float64}(undef, length(current), count)
    for index in axes(samples, 2)
        current = step(rng, sampler, current)
        samples[:, index] = current
    end
    samples
end

sample(sampler::VectorHMC, initial::AbstractVector{<:Real}, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)

struct ScalarHMC{F,G}
    logdensity::F
    gradient::G
    step_size::Float64
    steps::Int
    function ScalarHMC{F,G}(logdensity::F, gradient::G,
            step_size::Float64, steps::Int) where {F,G}
        isfinite(step_size) && step_size > 0.0 ||
            throw(ArgumentError("step size must be finite and positive"))
        steps > 0 || throw(ArgumentError("leapfrog steps must be positive"))
        new{F,G}(logdensity, gradient, step_size, steps)
    end
end

function ScalarHMC(logdensity::F, gradient::G, step_size::Real,
        steps::Integer=10) where {F,G}
    converted = Float64(step_size)
    isfinite(converted) && converted > 0.0 ||
        throw(ArgumentError("step size must be finite and positive"))
    steps > 0 || throw(ArgumentError("leapfrog steps must be positive"))
    ScalarHMC{F,G}(logdensity, gradient, converted, Int(steps))
end

function step(rng::AbstractRNG, sampler::ScalarHMC, current::Real)
    Reference.scalar_hmc_step!(Runtime.RNGSource(rng), sampler.logdensity,
        sampler.gradient, sampler.step_size, sampler.steps, Float64(current))
end

step(sampler::ScalarHMC, current::Real) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::ScalarHMC, initial::Real, count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    samples = Vector{Float64}(undef, count)
    current = Float64(initial)
    for index in eachindex(samples)
        current = step(rng, sampler, current)
        samples[index] = current
    end
    samples
end

sample(sampler::ScalarHMC, initial::Real, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)

struct GaussianRWMH{F}
    logdensity::F
    scale::Float64
    function GaussianRWMH(logdensity::F, scale::Real) where {F}
        converted = Float64(scale)
        isfinite(converted) && converted > 0.0 ||
            throw(ArgumentError("scale must be finite and positive"))
        new{F}(logdensity, converted)
    end
end

function step(rng::AbstractRNG, sampler::GaussianRWMH, current::Real)
    source = Runtime.RNGSource(rng)
    Reference.gaussian_rwmh_step!(source, sampler.logdensity,
        sampler.scale, Float64(current))
end

step(sampler::GaussianRWMH, current::Real) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::GaussianRWMH, initial::Real, count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    samples = Vector{Float64}(undef, count)
    current = Float64(initial)
    for index in eachindex(samples)
        current = step(rng, sampler, current)
        samples[index] = current
    end
    samples
end

sample(sampler::GaussianRWMH, initial::Real, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)

struct FiniteWeights
    weights::Vector{BigInt}
    function FiniteWeights(weights::AbstractVector{<:Integer})
        isempty(weights) && throw(ArgumentError("weights cannot be empty"))
        any(<(0), weights) && throw(ArgumentError("weights must be nonnegative"))
        sum(big, weights) > 0 || throw(ArgumentError("weights must have positive total"))
        new(BigInt.(weights))
    end
end

function sample(rng::AbstractRNG, target::FiniteWeights)
    source = Runtime.RNGSource(rng)
    Reference.categorical_index!(source, target.weights) + 1
end

sample(target::FiniteWeights) = sample(Random.default_rng(), target)

function sample(rng::AbstractRNG, target::FiniteWeights, count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    [sample(rng, target) for _ in 1:count]
end

sample(target::FiniteWeights, count::Integer) =
    sample(Random.default_rng(), target, count)

struct FiniteKernelWeights
    rows::Vector{Vector{BigInt}}
    function FiniteKernelWeights(rows::AbstractVector{<:AbstractVector{<:Integer}})
        isempty(rows) && throw(ArgumentError("proposal cannot be empty"))
        state_count = length(rows)
        converted = [BigInt.(row) for row in rows]
        all(row -> length(row) == state_count, converted) ||
            throw(DimensionMismatch("proposal must be square"))
        all(row -> all(weight -> weight >= 0, row), converted) ||
            throw(ArgumentError("proposal weights must be nonnegative"))
        all(row -> sum(row) > 0, converted) ||
            throw(ArgumentError("every proposal row must have positive total"))
        new(converted)
    end
end

FiniteKernelWeights(matrix::AbstractMatrix{<:Integer}) =
    FiniteKernelWeights([collect(row) for row in eachrow(matrix)])

struct FiniteMH
    target::FiniteWeights
    proposal::FiniteKernelWeights
    function FiniteMH(target::FiniteWeights, proposal::FiniteKernelWeights)
        all(weight -> weight > 0, target.weights) ||
            throw(ArgumentError("finite MH target weights must be strictly positive"))
        length(target.weights) == length(proposal.rows) ||
            throw(DimensionMismatch("target and proposal state counts differ"))
        new(target, proposal)
    end
end

function step(rng::AbstractRNG, sampler::FiniteMH, current::Integer)
    state_count = length(sampler.target.weights)
    1 <= current <= state_count || throw(ArgumentError("current state is out of range"))
    source = Runtime.RNGSource(rng)
    Reference.finite_mh_step!(source, sampler.target.weights,
        sampler.proposal.rows, current - 1) + 1
end

step(sampler::FiniteMH, current::Integer) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::FiniteMH, initial::Integer, count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    samples = Vector{Int}(undef, count)
    current = Int(initial)
    for index in eachindex(samples)
        current = step(rng, sampler, current)
        samples[index] = current
    end
    samples
end

sample(sampler::FiniteMH, initial::Integer, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)

struct TwoStateMH end

function step(rng::AbstractRNG, ::TwoStateMH, current::Bool)
    source = Runtime.RNGSource(rng)
    Bool(Reference.two_state_mh_step!(source, Int(current)))
end

step(sampler::TwoStateMH, current::Bool) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::TwoStateMH, initial::Bool, count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    samples = Vector{Bool}(undef, count)
    current = initial
    for index in eachindex(samples)
        current = step(rng, sampler, current)
        samples[index] = current
    end
    samples
end

sample(sampler::TwoStateMH, initial::Bool, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)

end
