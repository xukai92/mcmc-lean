module VerifiedSamplers

using Random
using LinearAlgebra
import Base: step

include("Runtime/Runtime.jl")
include("Certificates/Certificates.jl")
include("Reference/Reference.jl")
include("Optimized/Optimized.jl")

export FiniteWeights, FiniteKernelWeights, FiniteMH, FiniteIntegerSlice, TwoStateMH, GaussianRWMH,
    ScalarHMC, VectorHMC, MultinomialHMC, MetricMultinomialHMC,
    DiagonalMetric, DenseMetric, MetricHMC, RelativisticMultinomialHMC,
    GaussianSoftAbsGRHMC,
    CertifiedRelativisticMultinomialHMC,
    RestrictedExpr, RestrictedInput, RestrictedConst, RestrictedAdd,
    RestrictedMul, RestrictedNeg, RestrictedExp, restricted_value_gradient,
    restricted_gaussian_potential,
    Xu21CoupledSampler, ScopedInferenceOperator, ComposableSampler, covers,
    generated_schedule,
    ObservationCursor, observation_cursor, resume_observation, run_observations,
    FiniteHMMParticleGibbs,
    fixed_point_generalized_leapfrog, sample
export Certificates

fixed_point_generalized_leapfrog(args...; kwargs...) =
    Reference.fixed_point_generalized_leapfrog(args...; kwargs...)

"""Explicit suspend/resume state for a finite sequence of observation factors.

This mirrors Lean's `ProbabilisticProgram.CoroutineState`. It is ordinary
copyable data rather than a copied Julia `Task`, so cloning a cursor cannot
duplicate hidden stack or scheduler state.
"""
struct ObservationCursor{S,F}
    state::S
    accumulated_weight::Float64
    factors::Vector{F}
    position::Int
end

function observation_cursor(state, factors::AbstractVector{F}) where {F}
    ObservationCursor(state, 1.0, collect(factors), 1)
end

"""Consume at most one factor, returning `nothing` after completion."""
function resume_observation(cursor::ObservationCursor)
    cursor.position <= length(cursor.factors) || return nothing
    factor = cursor.factors[cursor.position]
    value = Float64(factor(cursor.state))
    value >= 0.0 || throw(DomainError(value, "observation weight must be nonnegative"))
    isfinite(value) || throw(DomainError(value, "observation weight must be finite"))
    weight = cursor.accumulated_weight * value
    isfinite(weight) || throw(DomainError(weight, "accumulated observation weight overflowed"))
    ObservationCursor(cursor.state, weight, cursor.factors, cursor.position + 1)
end

"""Consume up to `fuel` factors and return the resulting explicit cursor."""
function run_observations(cursor::ObservationCursor, fuel::Integer)
    fuel >= 0 || throw(ArgumentError("observation fuel must be nonnegative"))
    current = cursor
    for _ in 1:fuel
        next = resume_observation(current)
        isnothing(next) && break
        current = next
    end
    current
end

"""Restricted scalar target syntax shared with Lean's verified evaluator."""
abstract type RestrictedExpr end

struct RestrictedInput <: RestrictedExpr end
struct RestrictedConst <: RestrictedExpr
    value::Float64
end
struct RestrictedAdd <: RestrictedExpr
    left::RestrictedExpr
    right::RestrictedExpr
end
struct RestrictedMul <: RestrictedExpr
    left::RestrictedExpr
    right::RestrictedExpr
end
struct RestrictedNeg <: RestrictedExpr
    value::RestrictedExpr
end
struct RestrictedExp <: RestrictedExpr
    value::RestrictedExpr
end

function _checked_restricted(value::Float64, derivative::Float64)
    isfinite(value) || throw(DomainError(value,
        "restricted target evaluation produced a non-finite value"))
    isfinite(derivative) || throw(DomainError(derivative,
        "restricted target derivative produced a non-finite value"))
    value, derivative
end

"""Evaluate a restricted expression and its symbolic derivative together.

Lean proves the symbolic derivative correct over ideal reals. Bounded Float64
refinement remains an explicit, separate certificate obligation.
"""
restricted_value_gradient(::RestrictedInput, x::Real) =
    _checked_restricted(Float64(x), 1.0)
restricted_value_gradient(expression::RestrictedConst, ::Real) =
    _checked_restricted(expression.value, 0.0)

function restricted_value_gradient(expression::RestrictedAdd, x::Real)
    left, dleft = restricted_value_gradient(expression.left, x)
    right, dright = restricted_value_gradient(expression.right, x)
    _checked_restricted(left + right, dleft + dright)
end

function restricted_value_gradient(expression::RestrictedMul, x::Real)
    left, dleft = restricted_value_gradient(expression.left, x)
    right, dright = restricted_value_gradient(expression.right, x)
    _checked_restricted(left * right, dleft * right + left * dright)
end

function restricted_value_gradient(expression::RestrictedNeg, x::Real)
    value, derivative = restricted_value_gradient(expression.value, x)
    _checked_restricted(-value, -derivative)
end

function restricted_value_gradient(expression::RestrictedExp, x::Real)
    inner, derivative = restricted_value_gradient(expression.value, x)
    value = exp(inner)
    _checked_restricted(value, value * derivative)
end

function _restricted_from_ir(raw)
    node = Reference.items(Reference.aslist(raw))
    tag = Reference.atom(node[1])
    tag == "input" && length(node) == 1 && return RestrictedInput()
    if tag == "rational" && length(node) == 3
        numerator = parse(Int, Reference.atom(node[2]))
        denominator = parse(Int, Reference.atom(node[3]))
        denominator > 0 || error("restricted rational denominator must be positive")
        return RestrictedConst(numerator / denominator)
    elseif tag == "add" && length(node) == 3
        return RestrictedAdd(_restricted_from_ir(node[2]), _restricted_from_ir(node[3]))
    elseif tag == "mul" && length(node) == 3
        return RestrictedMul(_restricted_from_ir(node[2]), _restricted_from_ir(node[3]))
    elseif tag == "neg" && length(node) == 2
        return RestrictedNeg(_restricted_from_ir(node[2]))
    elseif tag == "exp" && length(node) == 2
        return RestrictedExp(_restricted_from_ir(node[2]))
    end
    error("invalid restricted target expression")
end

const restricted_gaussian_potential = _restricted_from_ir(
    Reference.TARGETS["restricted-gaussian-potential"])

"""A full-state transition annotated with the variables it may update.

The transition must have signature `(rng, state) -> state`. Scope metadata does
not establish target preservation; that mathematical premise is represented by
the corresponding Lean `ScopedOperator` certificate.
"""
struct ScopedInferenceOperator{F}
    scope::Vector{Symbol}
    transition::F
    function ScopedInferenceOperator(scope, transition::F) where {F}
        converted = unique(Symbol.(collect(scope)))
        isempty(converted) && throw(ArgumentError("operator scope cannot be empty"))
        new{F}(converted, transition)
    end
end

"""A left-to-right schedule of potentially overlapping inference operators."""
struct ComposableSampler{O<:Tuple}
    variables::Vector{Symbol}
    operators::O
    function ComposableSampler(variables, operators::ScopedInferenceOperator...)
        converted = unique(Symbol.(collect(variables)))
        isempty(converted) && throw(ArgumentError("model variables cannot be empty"))
        sampler = new{typeof(operators)}(converted, operators)
        covers(sampler) || throw(ArgumentError(
            "operator scopes must cover every declared model variable"))
        sampler
    end
end

covers(sampler::ComposableSampler) = all(variable -> any(
    operator -> variable in operator.scope, sampler.operators), sampler.variables)

"""Instantiate Lean-generated schedule metadata with named runtime transitions.

This checks names, scopes, ordering, and coverage. Mathematical preservation
still requires each callback to refine the correspondingly proved kernel.
"""
function generated_schedule(name::AbstractString, transitions::AbstractDict)
    descriptor = get(Reference.SCHEDULES, String(name), nothing)
    descriptor === nothing && throw(ArgumentError("unknown generated schedule: $name"))
    operators = map(descriptor.operators) do operator
        transition = if haskey(transitions, operator.name)
            transitions[operator.name]
        elseif haskey(transitions, Symbol(operator.name))
            transitions[Symbol(operator.name)]
        else
            throw(ArgumentError("missing transition for generated operator $(operator.name)"))
        end
        ScopedInferenceOperator(Symbol.(operator.scope), transition)
    end
    ComposableSampler(Symbol.(descriptor.variables), operators...)
end

function step(rng::AbstractRNG, sampler::ComposableSampler, current)
    state = current
    for operator in sampler.operators
        state = operator.transition(rng, state)
    end
    state
end

step(sampler::ComposableSampler, current) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::ComposableSampler, initial,
        count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    states = Vector{typeof(initial)}(undef, count)
    current = initial
    for index in eachindex(states)
        current = step(rng, sampler, current)
        states[index] = current
    end
    states
end

sample(sampler::ComposableSampler, initial, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)

"""Exact-integer bootstrap particle Gibbs for a finite hidden Markov model.

The path target is proportional to the initial weight followed by each
potential/transition factor. Potentials weight the state before each
transition, matching the formal finite Feynman--Kac convention.
"""
struct FiniteHMMParticleGibbs
    initial_weights::Vector{Int}
    transition_weights::Matrix{Int}
    potentials::Matrix{Int}
    particles::Int
    function FiniteHMMParticleGibbs(initial_weights::AbstractVector{<:Integer},
            transition_weights::AbstractMatrix{<:Integer},
            potentials::AbstractMatrix{<:Integer}, particles::Integer)
        converted_initial = Int.(initial_weights)
        converted_transition = Int.(transition_weights)
        converted_potentials = Int.(potentials)
        particles > 0 || throw(ArgumentError("particle count must be positive"))
        states = length(converted_initial)
        states > 0 || throw(ArgumentError("state space cannot be empty"))
        size(converted_transition) == (states, states) ||
            throw(DimensionMismatch("transition matrix"))
        size(converted_potentials, 2) == states ||
            throw(DimensionMismatch("potentials"))
        all(>=(0), converted_initial) && sum(converted_initial) > 0 ||
            throw(ArgumentError("invalid initial weights"))
        all(>=(0), converted_transition) &&
            all(row -> sum(row) > 0, eachrow(converted_transition)) ||
            throw(ArgumentError("invalid transition weights"))
        all(>(0), converted_potentials) ||
            throw(ArgumentError("potentials must be strictly positive"))
        new(converted_initial, converted_transition, converted_potentials,
            Int(particles))
    end
end

function step(rng::AbstractRNG, sampler::FiniteHMMParticleGibbs,
        current_path::AbstractVector{<:Integer})
    Reference.finite_hmm_particle_gibbs_step!(Runtime.RNGSource(rng),
        sampler.initial_weights, sampler.transition_weights, sampler.potentials,
        sampler.particles, current_path)
end

step(sampler::FiniteHMMParticleGibbs,
    current_path::AbstractVector{<:Integer}) =
  step(Random.default_rng(), sampler, current_path)

function sample(rng::AbstractRNG, sampler::FiniteHMMParticleGibbs,
        initial_path::AbstractVector{<:Integer}, count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    current = Int.(initial_path)
    paths = Matrix{Int}(undef, length(current), count)
    for index in axes(paths, 2)
        current = step(rng, sampler, current)
        paths[:, index] = current
    end
    paths
end

sample(sampler::FiniteHMMParticleGibbs,
    initial_path::AbstractVector{<:Integer}, count::Integer) =
  sample(Random.default_rng(), sampler, initial_path, count)

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

struct RelativisticMultinomialHMC{F,G}
    logdensity::F
    gradient::G
    metric::DiagonalMetric
    relativistic_mass::Float64
    step_size::Float64
    steps::Int
    function RelativisticMultinomialHMC(logdensity::F, gradient::G,
            metric::DiagonalMetric, relativistic_mass::Real,
            step_size::Real, steps::Integer=10) where {F,G}
        converted_mass, converted_step = Float64(relativistic_mass), Float64(step_size)
        isfinite(converted_mass) && converted_mass > 0 ||
            throw(ArgumentError("relativistic mass must be finite and positive"))
        isfinite(converted_step) && converted_step > 0 ||
            throw(ArgumentError("step size must be finite and positive"))
        steps > 0 || throw(ArgumentError("trajectory length must be positive"))
        new{F,G}(logdensity, gradient, metric, converted_mass,
            converted_step, Int(steps))
    end
end

function step(rng::AbstractRNG, sampler::RelativisticMultinomialHMC,
        current::AbstractVector{<:Real})
    Reference.relativistic_multinomial_hmc_step!(Runtime.RNGSource(rng),
        sampler.logdensity, sampler.gradient, sampler.step_size, sampler.steps,
        current, sampler.metric.mass, sampler.relativistic_mass)
end

step(sampler::RelativisticMultinomialHMC, current::AbstractVector{<:Real}) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::RelativisticMultinomialHMC,
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

sample(sampler::RelativisticMultinomialHMC,
        initial::AbstractVector{<:Real}, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)

"""Verified Gaussian diagonal-SoftAbs GR-HMC specialization.

The target is the centered unit Gaussian in `dimension` coordinates. Its
actual Hessian diagonal is one, so SoftAbs with positive `smoothing` produces
the constant diagonal metric `coth(smoothing)`. The matching Lean client
proves exact endpoint and multinomial invariance; this Julia implementation
retains the documented Float64/RNG refinement boundary.
"""
struct GaussianSoftAbsGRHMC
    dimension::Int
    smoothing::Float64
    sampler::RelativisticMultinomialHMC
    function GaussianSoftAbsGRHMC(dimension::Integer, step_size::Real,
            steps::Integer=10; smoothing::Real=1.0,
            relativistic_mass::Real=1.0)
        dimension > 0 || throw(ArgumentError("dimension must be positive"))
        α = Float64(smoothing)
        isfinite(α) && α > 0 ||
            throw(ArgumentError("SoftAbs smoothing must be finite and positive"))
        eigenvalue = 1 / tanh(α)
        metric = DiagonalMetric(fill(eigenvalue, Int(dimension)))
        logdensity = q -> -sum(abs2, q) / 2
        gradient = q -> q
        inner = RelativisticMultinomialHMC(logdensity, gradient, metric,
            relativistic_mass, step_size, steps)
        new(Int(dimension), α, inner)
    end
end

function step(rng::AbstractRNG, sampler::GaussianSoftAbsGRHMC,
        current::AbstractVector{<:Real})
    length(current) == sampler.dimension || throw(DimensionMismatch("current state"))
    step(rng, sampler.sampler, current)
end

step(sampler::GaussianSoftAbsGRHMC, current::AbstractVector{<:Real}) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::GaussianSoftAbsGRHMC,
        initial::AbstractVector{<:Real}, count::Integer)
    length(initial) == sampler.dimension || throw(DimensionMismatch("initial state"))
    sample(rng, sampler.sampler, initial, count)
end

sample(sampler::GaussianSoftAbsGRHMC,
        initial::AbstractVector{<:Real}, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)

struct CertifiedRelativisticMultinomialHMC{H,F,I}
    hamiltonian::H
    metric_factor::F
    integrator::I
    relativistic_mass::Float64
    step_size::Float64
    steps::Int
    function CertifiedRelativisticMultinomialHMC(hamiltonian::H, metric_factor::F,
            integrator::I, relativistic_mass::Real, step_size::Real,
            steps::Integer=10) where {H,F,I}
        m, ε = Float64(relativistic_mass), Float64(step_size)
        isfinite(m) && m > 0 || throw(ArgumentError("relativistic mass must be positive"))
        isfinite(ε) && ε > 0 || throw(ArgumentError("step size must be positive"))
        steps > 0 || throw(ArgumentError("trajectory length must be positive"))
        new{H,F,I}(hamiltonian, metric_factor, integrator, m, ε, Int(steps))
    end
end

function step(rng::AbstractRNG, sampler::CertifiedRelativisticMultinomialHMC,
        current::AbstractVector{<:Real})
    Reference.certified_relativistic_multinomial_hmc_step!(Runtime.RNGSource(rng),
        sampler.hamiltonian, sampler.metric_factor, sampler.integrator,
        sampler.step_size, sampler.steps, current, sampler.relativistic_mass)
end

step(sampler::CertifiedRelativisticMultinomialHMC,
        current::AbstractVector{<:Real}) = step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::CertifiedRelativisticMultinomialHMC,
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

sample(sampler::CertifiedRelativisticMultinomialHMC,
        initial::AbstractVector{<:Real}, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)

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

"""Exact finite slice sampler for strictly positive integer target weights."""
struct FiniteIntegerSlice
    weights::Vector{BigInt}
    function FiniteIntegerSlice(weights::AbstractVector{<:Integer})
        isempty(weights) && throw(ArgumentError("slice weights cannot be empty"))
        all(>(0), weights) || throw(ArgumentError("slice weights must be positive"))
        new(BigInt.(weights))
    end
end

function step(rng::AbstractRNG, sampler::FiniteIntegerSlice, current::Integer)
    source = Runtime.RNGSource(rng)
    Reference.integer_slice_step!(source, sampler.weights, current - 1) + 1
end

step(sampler::FiniteIntegerSlice, current::Integer) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::FiniteIntegerSlice,
        initial::Integer, count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    1 <= initial <= length(sampler.weights) ||
        throw(ArgumentError("initial state is out of range"))
    states = Vector{Int}(undef, count)
    current = Int(initial)
    for index in eachindex(states)
        current = step(rng, sampler, current)
        states[index] = current
    end
    states
end

sample(sampler::FiniteIntegerSlice, initial::Integer, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)

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
