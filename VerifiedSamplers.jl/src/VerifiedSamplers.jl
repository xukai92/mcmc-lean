module VerifiedSamplers

using Random
using LinearAlgebra
import Base: step

include("Runtime/Runtime.jl")
include("Certificates/Certificates.jl")
include("Reference/Reference.jl")
include("Optimized/Optimized.jl")

export FiniteWeights, FiniteKernelWeights, FiniteMH, FiniteIntegerSlice, BoundedRejectionSlice, SteppingOutSlice, TwoStateMH, GaussianRWMH, PositiveTransformedRWMH,
    WarmupGaussianRWMH, GaussianRWMHWarmupResult, warmup,
    ScalarHMC, VectorHMC, MultinomialHMC, MetricMultinomialHMC,
    CategoricalDHMC,
    DiagonalMetric, DenseMetric, MetricHMC, RelativisticMultinomialHMC,
    GaussianSoftAbsGRHMC,
    CertifiedRelativisticMultinomialHMC,
    RestrictedExpr, RestrictedInput, RestrictedConst, RestrictedAdd,
    RestrictedMul, RestrictedNeg, RestrictedExp, RestrictedSin, RestrictedCos,
    restricted_derivative, restricted_value_gradient,
    restricted_value_gradient_hessian, restricted_gaussian_potential,
    restricted_sinusoidal_potential, RestrictedGaussianFloat64Certificate,
    certify_restricted_gaussian_float64,
    restricted_gaussian_certificate_arguments,
    SoftAbsMetricFloat64Evaluation, SoftAbsDiagonalFloat64Evaluation,
    SoftAbsScalarHamiltonianFloat64Evaluation,
    evaluate_softabs_metric_float64, evaluate_softabs_diagonal_float64,
    evaluate_softabs_scalar_hamiltonian_float64,
    Xu21CoupledSampler, ScopedInferenceOperator, ComposableSampler, covers,
    DynamicTreeCertificate, certify_dynamic_tree, certified_orbit_partition,
    certified_scalar_uturn_partition,
    certified_vector_uturn_partition,
    certified_spanning_uturn_partition,
    generated_schedule,
    generated_transform,
    ObservationCursor, observation_cursor, resume_observation, run_observations,
    FiniteHMMParticleGibbs,
    fixed_point_generalized_leapfrog, sample
export Certificates

fixed_point_generalized_leapfrog(args...; kwargs...) =
    Reference.fixed_point_generalized_leapfrog(args...; kwargs...)

"""Coordinate-wise discontinuous HMC for a positive categorical target.

Categories are arranged on a cycle.  Each coordinate update moves to the next
or previous category, corresponding to the paper's `epsilon = mass`
specialization.  `steps` controls the number of updates made under one
refreshed Laplace momentum.
"""
struct CategoricalDHMC
    probabilities::Vector{Float64}
    steps::Int
    function CategoricalDHMC(probabilities::AbstractVector{<:Real},
            steps::Integer=1)
        converted = Float64.(probabilities)
        length(converted) >= 2 ||
            throw(ArgumentError("DHMC needs at least two categories"))
        all(x -> isfinite(x) && x > 0, converted) ||
            throw(ArgumentError("category probabilities must be finite and positive"))
        steps > 0 || throw(ArgumentError("trajectory length must be positive"))
        new(converted, Int(steps))
    end
end

function step(rng::AbstractRNG, sampler::CategoricalDHMC, current::Integer)
    Reference.categorical_dhmc_step!(Runtime.RNGSource(rng),
        sampler.probabilities, sampler.steps, current)
end

step(sampler::CategoricalDHMC, current::Integer) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::CategoricalDHMC,
        initial::Integer, count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    states = Vector{Int}(undef, count)
    current = Int(initial)
    for index in eachindex(states)
        current = step(rng, sampler, current)
        states[index] = current
    end
    states
end

sample(sampler::CategoricalDHMC, initial::Integer, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)

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
struct RestrictedSin <: RestrictedExpr
    value::RestrictedExpr
end
struct RestrictedCos <: RestrictedExpr
    value::RestrictedExpr
end

"""Construct the symbolic derivative of a restricted expression."""
restricted_derivative(::RestrictedInput) = RestrictedConst(1.0)
restricted_derivative(::RestrictedConst) = RestrictedConst(0.0)
restricted_derivative(expression::RestrictedAdd) = RestrictedAdd(
    restricted_derivative(expression.left), restricted_derivative(expression.right))
restricted_derivative(expression::RestrictedMul) = RestrictedAdd(
    RestrictedMul(restricted_derivative(expression.left), expression.right),
    RestrictedMul(expression.left, restricted_derivative(expression.right)))
restricted_derivative(expression::RestrictedNeg) =
    RestrictedNeg(restricted_derivative(expression.value))
restricted_derivative(expression::RestrictedExp) = RestrictedMul(
    RestrictedExp(expression.value), restricted_derivative(expression.value))
restricted_derivative(expression::RestrictedSin) = RestrictedMul(
    RestrictedCos(expression.value), restricted_derivative(expression.value))
restricted_derivative(expression::RestrictedCos) = RestrictedNeg(RestrictedMul(
    RestrictedSin(expression.value), restricted_derivative(expression.value)))

"""Guarded Float64 evaluation of one diagonal SoftAbs metric entry.

This record is runtime evidence, not a numerical certificate. Lean separately
composes operation-local error bounds for `tanh`, `sqrt`, reciprocal, and
`log`; a platform refinement must supply those bounds before this execution
can be connected to the ideal-real SoftAbs theorem.
"""
struct SoftAbsMetricFloat64Evaluation
    hessian::Float64
    eigenvalue::Float64
    sqrt_eigenvalue::Float64
    factor::Float64
    logdet::Float64
end

"""Guarded Float64 evaluation of a complete diagonal SoftAbs metric."""
struct SoftAbsDiagonalFloat64Evaluation
    entries::Vector{SoftAbsMetricFloat64Evaluation}
    factors::Vector{Float64}
    logdet::Float64
end

"""Guarded unit-parameter scalar GR-Hamiltonian evaluation.

This is the runtime expression covered compositionally by Lean's scalar
SoftAbs Hamiltonian error theorem: `U + sqrt(1 + (A*p)^2) + log(G)/2`.
"""
struct SoftAbsScalarHamiltonianFloat64Evaluation
    metric::SoftAbsMetricFloat64Evaluation
    transformed_momentum::Float64
    kinetic::Float64
    energy::Float64
end

"""Evaluate a scalar SoftAbs eigenvalue and its derived metric quantities."""
function evaluate_softabs_metric_float64(hessian::Real; smoothing::Real=1.0)
    h = Float64(hessian)
    α = Float64(smoothing)
    isfinite(h) || throw(DomainError(hessian, "SoftAbs Hessian must be finite"))
    isfinite(α) && α > 0 || throw(DomainError(smoothing,
        "SoftAbs smoothing must be finite and positive"))
    eigenvalue = iszero(h) ? inv(α) : h / tanh(α * h)
    isfinite(eigenvalue) && eigenvalue > 0 || throw(DomainError(eigenvalue,
        "SoftAbs eigenvalue must be finite and positive"))
    sqrt_eigenvalue = sqrt(eigenvalue)
    factor = inv(sqrt_eigenvalue)
    logdet = log(eigenvalue)
    all(isfinite, (sqrt_eigenvalue, factor, logdet)) ||
        throw(DomainError(eigenvalue, "derived SoftAbs quantities must be finite"))
    SoftAbsMetricFloat64Evaluation(h, eigenvalue, sqrt_eigenvalue, factor, logdet)
end


"""Evaluate every diagonal SoftAbs entry and its aggregate log determinant."""
function evaluate_softabs_diagonal_float64(hessian::AbstractVector{<:Real};
        smoothing::Real=1.0)
    isempty(hessian) && throw(ArgumentError("SoftAbs diagonal cannot be empty"))
    entries = [evaluate_softabs_metric_float64(value; smoothing=smoothing)
        for value in hessian]
    factors = [entry.factor for entry in entries]
    logdet = sum(entry.logdet for entry in entries)
    isfinite(logdet) || throw(DomainError(logdet,
        "SoftAbs log determinant must be finite"))
    SoftAbsDiagonalFloat64Evaluation(entries, factors, logdet)
end

function evaluate_softabs_scalar_hamiltonian_float64(potential::Real,
        hessian::Real, momentum::Real; smoothing::Real=1.0)
    u, p = Float64(potential), Float64(momentum)
    isfinite(u) || throw(DomainError(potential, "potential must be finite"))
    isfinite(p) || throw(DomainError(momentum, "momentum must be finite"))
    metric = evaluate_softabs_metric_float64(hessian; smoothing=smoothing)
    transformed = metric.factor * p
    kinetic = sqrt(1.0 + transformed * transformed)
    energy = u + kinetic + 0.5 * metric.logdet
    all(isfinite, (transformed, kinetic, energy)) ||
        throw(DomainError((potential, hessian, momentum),
            "derived SoftAbs Hamiltonian quantities must be finite"))
    SoftAbsScalarHamiltonianFloat64Evaluation(metric, transformed, kinetic, energy)
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

function restricted_value_gradient(expression::RestrictedSin, x::Real)
    inner, derivative = restricted_value_gradient(expression.value, x)
    _checked_restricted(sin(inner), cos(inner) * derivative)
end

function restricted_value_gradient(expression::RestrictedCos, x::Real)
    inner, derivative = restricted_value_gradient(expression.value, x)
    _checked_restricted(cos(inner), -sin(inner) * derivative)
end

"""Evaluate a restricted scalar target, force, and symbolic Hessian."""
function restricted_value_gradient_hessian(expression::RestrictedExpr, x::Real)
    value, gradient = restricted_value_gradient(expression, x)
    _, hessian = restricted_value_gradient(restricted_derivative(expression), x)
    value, gradient, hessian
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
    elseif tag == "sin" && length(node) == 2
        return RestrictedSin(_restricted_from_ir(node[2]))
    elseif tag == "cos" && length(node) == 2
        return RestrictedCos(_restricted_from_ir(node[2]))
    end
    error("invalid restricted target expression")
end

const restricted_gaussian_potential = _restricted_from_ir(
    Reference.TARGETS["restricted-gaussian-potential"])
const restricted_sinusoidal_potential = _restricted_from_ir(
    Reference.TARGETS["restricted-sinusoidal-potential"])

"""Exact dyadic post-execution certificate for the generated Gaussian target.

Every finite `Float64` is converted to its exact rational value. The ideal
value `x²/2` and derivative `x` are therefore mathematical rationals, and the
stored errors are exact rational differences from the Float64 execution. This
uses no BigFloat approximation and no libm call. The Lean theorem identifying
the generated artifact with `x²/2` supplies the formal semantic endpoint;
transporting this Julia record into Lean remains an artifact-checking step.
"""
struct RestrictedGaussianFloat64Certificate
    input::Float64
    computed_value::Float64
    computed_derivative::Float64
    ideal_value::Rational{BigInt}
    ideal_derivative::Rational{BigInt}
    value_error::Rational{BigInt}
    derivative_error::Rational{BigInt}
end

function certify_restricted_gaussian_float64(input::Real)
    x = Float64(input)
    isfinite(x) || throw(ArgumentError("input must be finite"))
    value, derivative = restricted_value_gradient(restricted_gaussian_potential, x)
    exact_input = Rational{BigInt}(x)
    exact_value = exact_input^2 / 2
    exact_derivative = exact_input
    computed_value = Rational{BigInt}(value)
    computed_derivative = Rational{BigInt}(derivative)
    RestrictedGaussianFloat64Certificate(x, value, derivative,
        exact_value, exact_derivative,
        abs(computed_value - exact_value),
        abs(computed_derivative - exact_derivative))
end

_rational_wire(value::Rational{BigInt}) =
    string(numerator(value), "/", denominator(value))

"""Serialize an exact Gaussian certificate for the compiled Lean checker."""
function restricted_gaussian_certificate_arguments(
        certificate::RestrictedGaussianFloat64Certificate)
    String[
        _rational_wire(Rational{BigInt}(certificate.input)),
        _rational_wire(Rational{BigInt}(certificate.computed_value)),
        _rational_wire(Rational{BigInt}(certificate.computed_derivative)),
        _rational_wire(certificate.value_error),
        _rational_wire(certificate.derivative_error),
    ]
end

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

"""Return a transform descriptor generated from Lean's versioned artifact."""
function generated_transform(name::AbstractString)
    descriptor = get(Reference.TRANSFORMS, String(name), nothing)
    descriptor === nothing && throw(ArgumentError("unknown generated transform: $name"))
    descriptor
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

"""Gaussian RWMH on a positive real parameter through the log transform.

`logdensity` is the constrained-space log density with respect to Lebesgue
measure on `(0,∞)`. The unconstrained callback is
`logdensity(exp(y)) + y`; the final term is the log-Jacobian. The exact Lean
conjugation theorem applies once this pushed-density identification is
supplied. Float64 `log`/`exp` remain a numerical-refinement boundary.
"""
struct PositiveTransformedRWMH{F}
    logdensity::F
    scale::Float64
    function PositiveTransformedRWMH(logdensity::F, scale::Real) where {F}
        converted = Float64(scale)
        isfinite(converted) && converted > 0 ||
            throw(ArgumentError("scale must be finite and positive"))
        new{F}(logdensity, converted)
    end
end

function step(rng::AbstractRNG, sampler::PositiveTransformedRWMH, current::Real)
    x = Float64(current)
    isfinite(x) && x > 0 ||
        throw(ArgumentError("positive transformed state must be finite and positive"))
    unconstrained(y) = sampler.logdensity(exp(y)) + y
    next_log = step(rng, GaussianRWMH(unconstrained, sampler.scale), log(x))
    next = exp(next_log)
    isfinite(next) && next > 0 ||
        throw(DomainError(next_log, "inverse transformed state must be finite"))
    next
end

step(sampler::PositiveTransformedRWMH, current::Real) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::PositiveTransformedRWMH,
        initial::Real, count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    samples = Vector{Float64}(undef, count)
    current = Float64(initial)
    for index in eachindex(samples)
        current = step(rng, sampler, current)
        samples[index] = current
    end
    samples
end

sample(sampler::PositiveTransformedRWMH, initial::Real, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)

"""Bounded, warmup-only Robbins--Monro tuning for Gaussian RWMH.

The log proposal scale changes by `learning_rate / sqrt(iteration)` times the
acceptance error and is clamped to `[min_scale, max_scale]`. Retained sampling
uses the frozen `GaussianRWMH` returned by `warmup`; no stationarity claim is
made for the warmup trajectory itself.
"""
struct WarmupGaussianRWMH{F}
    logdensity::F
    initial_scale::Float64
    iterations::Int
    target_accept::Float64
    learning_rate::Float64
    min_scale::Float64
    max_scale::Float64
end

function WarmupGaussianRWMH(logdensity::F, initial_scale::Real,
        iterations::Integer; target_accept::Real=0.44,
        learning_rate::Real=0.5, min_scale::Real=1e-4,
        max_scale::Real=1e2) where {F}
    scale, target, learning = Float64(initial_scale), Float64(target_accept),
        Float64(learning_rate)
    lower, upper = Float64(min_scale), Float64(max_scale)
    isfinite(scale) && scale > 0 ||
        throw(ArgumentError("initial scale must be finite and positive"))
    iterations >= 0 || throw(ArgumentError("warmup iterations must be nonnegative"))
    isfinite(target) && 0 < target < 1 ||
        throw(ArgumentError("target acceptance must lie strictly between zero and one"))
    isfinite(learning) && learning > 0 ||
        throw(ArgumentError("learning rate must be finite and positive"))
    isfinite(lower) && isfinite(upper) && 0 < lower <= upper ||
        throw(ArgumentError("scale bounds must be finite, positive, and ordered"))
    lower <= scale <= upper ||
        throw(ArgumentError("initial scale must lie within the scale bounds"))
    WarmupGaussianRWMH{F}(logdensity, scale, Int(iterations), target,
        learning, lower, upper)
end

struct GaussianRWMHWarmupResult{F}
    sampler::GaussianRWMH{F}
    state::Float64
    scales::Vector{Float64}
    accepted::BitVector
end

function warmup(rng::AbstractRNG, config::WarmupGaussianRWMH, initial::Real)
    current = Float64(initial)
    isfinite(current) || throw(ArgumentError("initial state must be finite"))
    scales = Vector{Float64}(undef, config.iterations + 1)
    accepted = falses(config.iterations)
    log_scale = log(config.initial_scale)
    scales[1] = config.initial_scale
    for iteration in 1:config.iterations
        sampler = GaussianRWMH(config.logdensity, exp(log_scale))
        next = step(rng, sampler, current)
        accepted[iteration] = next != current
        current = next
        gain = config.learning_rate / sqrt(iteration)
        log_scale = clamp(log_scale + gain *
            (accepted[iteration] - config.target_accept),
            log(config.min_scale), log(config.max_scale))
        scales[iteration + 1] = exp(log_scale)
    end
    frozen = GaussianRWMH(config.logdensity, scales[end])
    GaussianRWMHWarmupResult(frozen, current, scales, accepted)
end

warmup(config::WarmupGaussianRWMH, initial::Real) =
    warmup(Random.default_rng(), config, initial)

function sample(rng::AbstractRNG, config::WarmupGaussianRWMH,
        initial::Real, count::Integer)
    result = warmup(rng, config, initial)
    sample(rng, result.sampler, result.state, count)
end

sample(config::WarmupGaussianRWMH, initial::Real, count::Integer) =
    sample(Random.default_rng(), config, initial, count)

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

"""Bounded-domain continuous slice sampler using exact horizontal rejection.

Its mathematical target is the supplied density restricted to `[lower, upper]`.
The formal general-state slice theorem covers the ideal conditional kernel;
Float64 callbacks, uniforms, and the finite attempt guard remain runtime
boundaries.
"""
struct BoundedRejectionSlice{F}
    logdensity::F
    lower::Float64
    upper::Float64
    max_attempts::Int
    function BoundedRejectionSlice(logdensity::F, lower::Real, upper::Real;
            max_attempts::Integer=100_000) where {F}
        lo, hi = Float64(lower), Float64(upper)
        isfinite(lo) && isfinite(hi) && lo < hi ||
            throw(ArgumentError("slice bounds must be finite and ordered"))
        max_attempts > 0 || throw(ArgumentError("max_attempts must be positive"))
        new{F}(logdensity, lo, hi, Int(max_attempts))
    end
end

function step(rng::AbstractRNG, sampler::BoundedRejectionSlice, current::Real)
    source = Runtime.RNGSource(rng)
    Reference.bounded_slice_step!(source, sampler.logdensity, sampler.lower,
        sampler.upper, current, sampler.max_attempts)
end

step(sampler::BoundedRejectionSlice, current::Real) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::BoundedRejectionSlice,
        initial::Real, count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    states = Vector{Float64}(undef, count)
    current = Float64(initial)
    for index in eachindex(states)
        current = step(rng, sampler, current)
        states[index] = current
    end
    states
end

sample(sampler::BoundedRejectionSlice, initial::Real, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)

"""Practical real-line slice sampler with stepping out and shrinkage.

The finite `max_steps` and `max_shrink` guards are runtime controls. This
implementation is differentially tested, but its adaptive bracket is not yet
connected to the ideal Lean disintegration theorem.
"""
struct SteppingOutSlice{F}
    logdensity::F
    width::Float64
    max_steps::Int
    max_shrink::Int
    function SteppingOutSlice(logdensity::F, width::Real;
            max_steps::Integer=100, max_shrink::Integer=10_000) where {F}
        w = Float64(width)
        isfinite(w) && w > 0 || throw(ArgumentError("width must be finite and positive"))
        max_steps >= 0 || throw(ArgumentError("max_steps must be nonnegative"))
        max_shrink > 0 || throw(ArgumentError("max_shrink must be positive"))
        new{F}(logdensity, w, Int(max_steps), Int(max_shrink))
    end
end

function step(rng::AbstractRNG, sampler::SteppingOutSlice, current::Real)
    Reference.stepping_out_slice_step!(Runtime.RNGSource(rng), sampler.logdensity,
        sampler.width, current, sampler.max_steps, sampler.max_shrink)
end

step(sampler::SteppingOutSlice, current::Real) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::SteppingOutSlice,
        initial::Real, count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    states = Vector{Float64}(undef, count)
    current = Float64(initial)
    for index in eachindex(states)
        current = step(rng, sampler, current)
        states[index] = current
    end
    states
end

sample(sampler::SteppingOutSlice, initial::Real, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)

"""Per-output certificate for a finite dynamic trajectory builder.

`candidates[root]` uses one-based state indices. Validity requires every root
to be retained and every admitted leaf to expose exactly the same completed
candidate set when rerooted.
"""
struct DynamicTreeCertificate
    candidates::Vector{Vector{Int}}
    valid::Bool
end

function certify_dynamic_tree(rows::AbstractVector{<:AbstractVector{<:Integer}})
    count = length(rows)
    count > 0 || throw(ArgumentError("dynamic tree must contain a state"))
    candidates = Vector{Vector{Int}}(undef, count)
    for root in 1:count
        row = sort!(unique!(Int.(collect(rows[root]))))
        all(leaf -> 1 <= leaf <= count, row) ||
            throw(ArgumentError("dynamic-tree candidate index is out of range"))
        candidates[root] = row
    end
    valid = true
    for root in 1:count
        root in candidates[root] || (valid = false; break)
        for leaf in candidates[root]
            if candidates[leaf] != candidates[root]
                valid = false
                break
            end
        end
        valid || break
    end
    DynamicTreeCertificate(candidates, valid)
end

"""Partition a canonical finite orbit at declared barrier edges.

The `k`th Boolean separates states `k` and `k+1`. Candidate rows are the full
connected components between barriers, hence pass the reroot checker by
construction. A U-turn detector can supply the barriers, but this function
does not claim that an arbitrary detector implements standard NUTS stopping.
"""
function certified_orbit_partition(barriers::AbstractVector{Bool})
    state_count = length(barriers) + 1
    rows = Vector{Vector{Int}}(undef, state_count)
    component_start = 1
    for edge in 1:state_count
        if edge == state_count || barriers[edge]
            component = collect(component_start:edge)
            for state in component
                rows[state] = component
            end
            component_start = edge + 1
        end
    end
    certificate = certify_dynamic_tree(rows)
    certificate.valid || error("internal orbit-partition certificate failure")
    certificate
end

"""Build a certified scalar orbit partition from adjacent endpoint U-turns.

An edge is cut when its displacement has negative product with either endpoint
momentum. The detector is evaluated on the complete canonical trajectory, so
the resulting rows are reroot invariant. This is a local safe detector, not a
claim of equivalence to a recursive subtree-based NUTS implementation.
"""
function certified_scalar_uturn_partition(positions::AbstractVector{<:Real},
        momenta::AbstractVector{<:Real})
    length(positions) == length(momenta) ||
        throw(DimensionMismatch("position and momentum trajectories must match"))
    isempty(positions) && throw(ArgumentError("trajectory cannot be empty"))
    q, p = Float64.(positions), Float64.(momenta)
    all(isfinite, q) && all(isfinite, p) ||
        throw(DomainError((positions, momenta), "trajectory must be finite"))
    barriers = Bool[(q[i + 1] - q[i]) * p[i] < 0 ||
        (q[i + 1] - q[i]) * p[i + 1] < 0 for i in 1:length(q)-1]
    certified_orbit_partition(barriers)
end

"""Finite-dimensional canonical endpoint U-turn partition."""
function certified_vector_uturn_partition(
        positions::AbstractVector{<:AbstractVector{<:Real}},
        momenta::AbstractVector{<:AbstractVector{<:Real}})
    length(positions) == length(momenta) ||
        throw(DimensionMismatch("position and momentum trajectories must match"))
    isempty(positions) && throw(ArgumentError("trajectory cannot be empty"))
    dimension = length(first(positions))
    dimension > 0 || throw(ArgumentError("phase-space dimension cannot be zero"))
    all(q -> length(q) == dimension, positions) &&
        all(p -> length(p) == dimension, momenta) ||
        throw(DimensionMismatch("all phase points must have the same dimension"))
    q = [Float64.(point) for point in positions]
    p = [Float64.(point) for point in momenta]
    all(point -> all(isfinite, point), q) &&
        all(point -> all(isfinite, point), p) ||
        throw(DomainError((positions, momenta), "trajectory must be finite"))
    barriers = Vector{Bool}(undef, length(q) - 1)
    for i in eachindex(barriers)
        displacement = q[i + 1] .- q[i]
        barriers[i] = dot(displacement, p[i]) < 0 ||
            dot(displacement, p[i + 1]) < 0
    end
    certified_orbit_partition(barriers)
end

"""Conservative all-scales finite-dimensional U-turn partition.

For every split, inspect all endpoint pairs that span that split and cut when
any pair makes a U-turn. This mirrors Lean's root-independent completed-orbit
construction. It is deliberately more conservative than first-stop NUTS.
"""
function certified_spanning_uturn_partition(
        positions::AbstractVector{<:AbstractVector{<:Real}},
        momenta::AbstractVector{<:AbstractVector{<:Real}})
    length(positions) == length(momenta) ||
        throw(DimensionMismatch("position and momentum trajectories must match"))
    isempty(positions) && throw(ArgumentError("trajectory cannot be empty"))
    dimension = length(first(positions))
    dimension > 0 || throw(ArgumentError("phase-space dimension cannot be zero"))
    all(q -> length(q) == dimension, positions) &&
        all(p -> length(p) == dimension, momenta) ||
        throw(DimensionMismatch("all phase points must have the same dimension"))
    q = [Float64.(point) for point in positions]
    p = [Float64.(point) for point in momenta]
    all(point -> all(isfinite, point), q) &&
        all(point -> all(isfinite, point), p) ||
        throw(DomainError((positions, momenta), "trajectory must be finite"))
    barriers = falses(length(q) - 1)
    for split in eachindex(barriers), left in 1:split, right in split+1:length(q)
        displacement = q[right] .- q[left]
        if dot(displacement, p[left]) < 0 || dot(displacement, p[right]) < 0
            barriers[split] = true
            break
        end
    end
    certified_orbit_partition(barriers)
end

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
