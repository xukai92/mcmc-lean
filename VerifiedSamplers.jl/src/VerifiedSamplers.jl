module VerifiedSamplers

using Random
using LinearAlgebra
import Base: step

include("Runtime/Runtime.jl")
include("Certificates/Certificates.jl")
include("Reference/Reference.jl")
include("Optimized/Optimized.jl")
include("Backends/Backends.jl")
include("Evaluation/Evaluation.jl")

export FiniteWeights, FiniteKernelWeights, FiniteMH, FiniteIntegerSlice, BoundedRejectionSlice, SteppingOutSlice, SteppingOutSliceTrace, RestrictedQuarticSliceTraceCertificate, trace_stepping_out_slice, certify_stepping_out_slice_trace, certify_restricted_quartic_slice_trace, ShearedBirthDeathRJ, SpatialBirthDeathRJ, sheared_birth_unshear, TwoStateMH, GaussianRWMH, PositiveTransformedRWMH, OpenUnitTransformedRWMH,
    WarmupGaussianRWMH, GaussianRWMHWarmupResult, IndefiniteAdaptiveBool,
    IndefiniteAdaptiveContinuousRefresh, warmup,
    ScalarHMC, VectorHMC, FixedIntegrationTimeHMC, JitteredHMC, TemperedHMC,
    MultinomialHMC, NUTS, HMCTransition, transition, sample_with_diagnostics,
    PartialMomentumHMC, HMCPhaseState, PartialMomentumTransition,
    initialize_phase,
    CertifiedDynamicHMC,
    CompletedTreeC4DynamicHMC,
    CheckedFirstStopDynamicHMC, CheckedRecursiveDynamicHMC, VerifiedNUTS,
    streaming_eligible_select,
    MetricMultinomialHMC,
    CategoricalDHMC,
    DiagonalMetric, DenseMetric, RankUpdateMetric, MetricHMC,
    RelativisticMultinomialHMC,
    GaussianSoftAbsGRHMC,
    CertifiedRelativisticMultinomialHMC,
    RestrictedExpr, RestrictedInput, RestrictedConst, RestrictedAdd,
    RestrictedMul, RestrictedNeg, RestrictedExp, RestrictedSin, RestrictedCos,
    restricted_derivative, restricted_value_gradient,
    restricted_value_gradient_hessian, restricted_gaussian_potential,
    restricted_quartic_potential, restricted_potential_rwmh,
    restricted_potential_hmc, restricted_potential_slice,
    restricted_sinusoidal_potential, RestrictedGaussianFloat64Certificate,
    certify_restricted_gaussian_float64,
    restricted_gaussian_certificate_arguments,
    RestrictedQuarticFloat64Certificate,
    certify_restricted_quartic_float64,
    restricted_quartic_certificate_arguments,
    SoftAbsMetricFloat64Evaluation, SoftAbsDiagonalFloat64Evaluation,
    SoftAbsScalarHamiltonianFloat64Evaluation,
    UnitZeroSoftAbsFloat64Certificate, certify_unit_zero_softabs_float64,
    unit_zero_softabs_certificate_arguments,
    evaluate_softabs_metric_float64, evaluate_softabs_diagonal_float64,
    evaluate_softabs_scalar_hamiltonian_float64,
    Xu21CoupledSampler, coupled_meeting_time, coupled_meeting_diagnostic,
    ScopedInferenceOperator, ComposableSampler, covers,
    DynamicTreeCertificate, certify_dynamic_tree, coherent_dynamic_tree,
    certified_orbit_partition,
    certified_dynamic_select!, certified_dynamic_select,
    safe_dynamic_select!, safe_dynamic_select,
    RecursiveBarrierTree, RecursiveBarrierLeaf, RecursiveBarrierNode,
    recursive_barriers, certified_recursive_partition,
    certified_scalar_uturn_partition,
    certified_vector_uturn_partition,
    certified_spanning_uturn_partition,
    first_stop_endpoint_uturn_candidates,
    recursive_doubling_uturn_candidates,
    completed_tree_direction_trace,
    completed_tree_c4_candidates,
    generated_dynamic_tree,
    generated_schedule,
    generated_transform,
    GaussianZigZag, GaussianZigZagResult, gaussian_zigzag_waiting_time,
    ObservationCursor, observation_cursor, resume_observation, run_observations,
    FiniteHMMParticleGibbs,
    fixed_point_generalized_leapfrog, sample
export Backends, Certificates, Evaluation, Optimized

fixed_point_generalized_leapfrog(args...; kwargs...) =
    Reference.fixed_point_generalized_leapfrog(args...; kwargs...)
include("Public/CategoricalDHMC.jl")

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

"""Assumption-free exact record for SoftAbs smoothing one at Hessian zero."""
struct UnitZeroSoftAbsFloat64Certificate
    evaluation::SoftAbsMetricFloat64Evaluation
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

function certify_unit_zero_softabs_float64()
    evaluation = evaluate_softabs_metric_float64(0.0; smoothing=1.0)
    values = (evaluation.hessian, evaluation.eigenvalue,
        evaluation.sqrt_eigenvalue, evaluation.factor, evaluation.logdet)
    values == (0.0, 1.0, 1.0, 1.0, 0.0) || error(
        "unit/zero SoftAbs execution left the exact certified subset")
    UnitZeroSoftAbsFloat64Certificate(evaluation)
end

unit_zero_softabs_certificate_arguments(
        certificate::UnitZeroSoftAbsFloat64Certificate) = String[
    _rational_wire(Rational{BigInt}(certificate.evaluation.hessian)),
    _rational_wire(Rational{BigInt}(certificate.evaluation.eigenvalue)),
    _rational_wire(Rational{BigInt}(certificate.evaluation.sqrt_eigenvalue)),
    _rational_wire(Rational{BigInt}(certificate.evaluation.factor)),
    _rational_wire(Rational{BigInt}(certificate.evaluation.logdet)),
]


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
const restricted_quartic_potential = _restricted_from_ir(
    Reference.TARGETS["restricted-quartic-potential"])

"""Exact dyadic post-execution certificate for the generated Gaussian target.

Every finite `Float64` is converted to its exact rational value. The ideal
value `x²/2`, derivative `x`, and second derivative `1` are therefore
mathematical rationals, and the stored errors are exact rational differences
from the Float64 execution. This
uses no BigFloat approximation and no libm call. The Lean theorem identifying
the generated artifact with `x²/2` supplies the formal semantic endpoint;
transporting this Julia record into Lean remains an artifact-checking step.
"""
struct RestrictedGaussianFloat64Certificate
    input::Float64
    computed_value::Float64
    computed_derivative::Float64
    computed_second_derivative::Float64
    ideal_value::Rational{BigInt}
    ideal_derivative::Rational{BigInt}
    ideal_second_derivative::Rational{BigInt}
    value_error::Rational{BigInt}
    derivative_error::Rational{BigInt}
    second_derivative_error::Rational{BigInt}
end

function certify_restricted_gaussian_float64(input::Real)
    x = Float64(input)
    isfinite(x) || throw(ArgumentError("input must be finite"))
    value, derivative, second_derivative =
        restricted_value_gradient_hessian(restricted_gaussian_potential, x)
    exact_input = Rational{BigInt}(x)
    exact_value = exact_input^2 / 2
    exact_derivative = exact_input
    exact_second_derivative = Rational{BigInt}(1)
    computed_value = Rational{BigInt}(value)
    computed_derivative = Rational{BigInt}(derivative)
    computed_second_derivative = Rational{BigInt}(second_derivative)
    RestrictedGaussianFloat64Certificate(x, value, derivative,
        second_derivative, exact_value, exact_derivative,
        exact_second_derivative,
        abs(computed_value - exact_value),
        abs(computed_derivative - exact_derivative),
        abs(computed_second_derivative - exact_second_derivative))
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
        _rational_wire(Rational{BigInt}(certificate.computed_second_derivative)),
        _rational_wire(certificate.value_error),
        _rational_wire(certificate.derivative_error),
        _rational_wire(certificate.second_derivative_error),
    ]
end

"""Exact-rational record for one Float64 execution of the generated quartic.

The callback uses only finite Float64 arithmetic. Each observed output and its
ideal polynomial counterpart are converted to exact rationals, so the recorded
errors contain no BigFloat or transcendental approximation.
"""
struct RestrictedQuarticFloat64Certificate
    input::Float64
    computed_value::Float64
    computed_derivative::Float64
    computed_second_derivative::Float64
    ideal_value::Rational{BigInt}
    ideal_derivative::Rational{BigInt}
    ideal_second_derivative::Rational{BigInt}
    value_error::Rational{BigInt}
    derivative_error::Rational{BigInt}
    second_derivative_error::Rational{BigInt}
end

function certify_restricted_quartic_float64(input::Real)
    x = Float64(input)
    isfinite(x) || throw(ArgumentError("input must be finite"))
    value, derivative, second_derivative =
        restricted_value_gradient_hessian(restricted_quartic_potential, x)
    exact_input = Rational{BigInt}(x)
    ideal_value = exact_input^4 / 4 + exact_input^2 / 2
    ideal_derivative = exact_input^3 + exact_input
    ideal_second_derivative = 3 * exact_input^2 + 1
    computed_value = Rational{BigInt}(value)
    computed_derivative = Rational{BigInt}(derivative)
    computed_second_derivative = Rational{BigInt}(second_derivative)
    RestrictedQuarticFloat64Certificate(x, value, derivative,
        second_derivative, ideal_value, ideal_derivative,
        ideal_second_derivative,
        abs(computed_value - ideal_value),
        abs(computed_derivative - ideal_derivative),
        abs(computed_second_derivative - ideal_second_derivative))
end

function restricted_quartic_certificate_arguments(
        certificate::RestrictedQuarticFloat64Certificate)
    String[
        _rational_wire(Rational{BigInt}(certificate.input)),
        _rational_wire(Rational{BigInt}(certificate.computed_value)),
        _rational_wire(Rational{BigInt}(certificate.computed_derivative)),
        _rational_wire(Rational{BigInt}(certificate.computed_second_derivative)),
        _rational_wire(certificate.value_error),
        _rational_wire(certificate.derivative_error),
        _rational_wire(certificate.second_derivative_error),
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

"""Exact ideal-form Gaussian Zig-Zag inverse clock in Float64 arithmetic."""
function gaussian_zigzag_waiting_time(position::Real, velocity::Integer,
        exponential_draw::Real)
    q, e = Float64(position), Float64(exponential_draw)
    isfinite(q) || throw(ArgumentError("position must be finite"))
    velocity in (-1, 1) || throw(ArgumentError("velocity must be -1 or 1"))
    isfinite(e) && e > 0 ||
        throw(ArgumentError("exponential hazard draw must be finite and positive"))
    a = velocity * q
    if a >= 0
        root = sqrt(a * a + 2 * e)
        wait = (2 * e) / (root + a)
    else
        wait = -a + sqrt(2 * e)
    end
    isfinite(wait) && wait >= 0 ||
        throw(DomainError(wait, "Gaussian Zig-Zag waiting time must be finite"))
    wait
end

struct GaussianZigZag
    observation_interval::Float64
    function GaussianZigZag(observation_interval::Real=1.0)
        interval = Float64(observation_interval)
        isfinite(interval) && interval > 0 ||
            throw(ArgumentError("observation interval must be finite and positive"))
        new(interval)
    end
end

struct GaussianZigZagResult
    positions::Vector{Float64}
    velocities::Vector{Int8}
end

function step(rng::AbstractRNG, sampler::GaussianZigZag,
        current::Tuple{<:Real,<:Integer})
    q, velocity = Float64(current[1]), Int(current[2])
    isfinite(q) || throw(ArgumentError("position must be finite"))
    velocity in (-1, 1) || throw(ArgumentError("velocity must be -1 or 1"))
    elapsed = 0.0
    while true
        wait = gaussian_zigzag_waiting_time(q, velocity, randexp(rng))
        remaining = sampler.observation_interval - elapsed
        if wait >= remaining
            return (q + velocity * remaining, velocity)
        end
        q += velocity * wait
        elapsed += wait
        velocity = -velocity
    end
end

step(sampler::GaussianZigZag, current::Tuple{<:Real,<:Integer}) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::GaussianZigZag,
        initial::Tuple{<:Real,<:Integer}, count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    positions = Vector{Float64}(undef, count)
    velocities = Vector{Int8}(undef, count)
    current = initial
    for index in eachindex(positions)
        current = step(rng, sampler, current)
        positions[index] = current[1]
        velocities[index] = current[2]
    end
    GaussianZigZagResult(positions, velocities)
end

sample(sampler::GaussianZigZag, initial::Tuple{<:Real,<:Integer}, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)

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

"""First exact meeting time of the faithful Xu et al. coupled runtime.

Returns `nothing` if the supplied finite diagnostic horizon is exhausted. This
is an executable experiment helper, not a replacement for a geometric-tail
theorem.
"""
function coupled_meeting_time(rng::AbstractRNG, sampler::Xu21CoupledSampler,
        initial::Tuple{<:AbstractVector{<:Real},<:AbstractVector{<:Real}},
        max_steps::Integer)
    max_steps >= 0 || throw(ArgumentError("maximum meeting horizon must be nonnegative"))
    left, right = Float64.(initial[1]), Float64.(initial[2])
    length(left) == length(right) || throw(DimensionMismatch("coupled states"))
    left == right && return 0
    for iteration in 1:max_steps
        left, right = step(rng, sampler, (left, right))
        left == right && return iteration
    end
    nothing
end

coupled_meeting_time(sampler::Xu21CoupledSampler, initial::Tuple,
    max_steps::Integer) =
    coupled_meeting_time(Random.default_rng(), sampler, initial, max_steps)

"""Run a replicated, explicitly censored Xu et al. meeting-time diagnostic.

`meeting_times` contains an integer meeting time or `nothing` for each
replicate. `restricted_mean` replaces a censored time by `max_steps`; it is a
finite-horizon empirical summary, not an estimate of an uncensored expectation
and not a formal convergence certificate.
"""
function coupled_meeting_diagnostic(rng::AbstractRNG,
        sampler::Xu21CoupledSampler,
        initial::Tuple{<:AbstractVector{<:Real},<:AbstractVector{<:Real}},
        replicates::Integer, max_steps::Integer)
    replicates > 0 || throw(ArgumentError("replicate count must be positive"))
    max_steps >= 0 || throw(ArgumentError("maximum meeting horizon must be nonnegative"))
    times = Union{Nothing,Int}[
        coupled_meeting_time(rng, sampler, initial, max_steps)
        for _ in 1:replicates
    ]
    met = count(!isnothing, times)
    observed_total = sum(time === nothing ? 0 : time for time in times)
    restricted_total = sum(time === nothing ? max_steps : time for time in times)
    (
        meeting_times=times,
        met=met,
        censored=replicates - met,
        meeting_fraction=met / replicates,
        observed_mean=met == 0 ? nothing : observed_total / met,
        restricted_mean=restricted_total / replicates,
        horizon=Int(max_steps),
    )
end

coupled_meeting_diagnostic(sampler::Xu21CoupledSampler, initial::Tuple,
    replicates::Integer, max_steps::Integer) =
    coupled_meeting_diagnostic(Random.default_rng(), sampler, initial,
        replicates, max_steps)

function _hmc_integrator_parameters(integrator::Symbol,
        jitter::T, temperature::T) where {T<:AbstractFloat}
    integrator in (:leapfrog, :jittered, :tempered) || throw(ArgumentError(
        "integrator must be :leapfrog, :jittered, or :tempered"))
    jitter_amount, tempering = jitter, temperature
    isfinite(jitter_amount) && 0 <= jitter_amount < 1 || throw(ArgumentError(
        "jitter must lie in [0, 1)"))
    isfinite(tempering) && tempering > 0 || throw(ArgumentError(
        "temperature must be finite and positive"))
    integrator, jitter_amount, tempering
end

struct MultinomialHMC{F,G}
    logdensity::F
    gradient::G
    step_size::Float64
    steps::Int
    integrator::Symbol
    jitter::Float64
    function MultinomialHMC(logdensity::F, gradient::G, step_size::Real,
            steps::Integer=10; integrator::Symbol=:leapfrog,
            jitter::Real=0.1) where {F,G}
        converted = Float64(step_size)
        isfinite(converted) && converted > 0 ||
            throw(ArgumentError("step size must be finite and positive"))
        steps > 0 || throw(ArgumentError("trajectory length must be positive"))
        kind, jitter_amount, _ =
            _hmc_integrator_parameters(integrator, jitter, 1.0)
        kind in (:leapfrog, :jittered) || throw(ArgumentError(
            "fixed multinomial HMC supports :leapfrog and :jittered; " *
            "tempered intermediate selection requires a weighting theorem"))
        new{F,G}(logdensity, gradient, converted, Int(steps), kind,
            jitter_amount)
    end
end

function _multinomial_hmc_step!(source::Runtime.AbstractRandomSource,
        sampler::MultinomialHMC, current::AbstractVector{<:Real})
    step_size = sampler.integrator === :jittered ?
        sampler.step_size * (1 + sampler.jitter *
            (2Runtime.uniform_unit!(source) - 1)) : sampler.step_size
    Reference.multinomial_hmc_step!(source, sampler.logdensity,
        sampler.gradient, step_size, sampler.steps, current)
end

function step(rng::AbstractRNG, sampler::MultinomialHMC,
        current::AbstractVector{<:Real})
    _multinomial_hmc_step!(Runtime.RNGSource(rng), sampler, current)
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

struct DiagonalMetric{T<:AbstractFloat}
    mass::Vector{T}
    function DiagonalMetric(mass::AbstractVector{T}) where {T<:AbstractFloat}
        converted = collect(mass)
        isempty(converted) && throw(ArgumentError("mass cannot be empty"))
        all(x -> isfinite(x) && x > 0, converted) ||
            throw(ArgumentError("diagonal mass must be finite and positive"))
        new{T}(converted)
    end
end

struct DenseMetric{T<:AbstractFloat}
    mass::Matrix{T}
    function DenseMetric(mass::AbstractMatrix{T}) where {T<:AbstractFloat}
        converted = Matrix(mass)
        size(converted, 1) == size(converted, 2) ||
            throw(DimensionMismatch("mass matrix must be square"))
        issymmetric(converted) || throw(ArgumentError("mass matrix must be symmetric"))
        isposdef(converted) || throw(ArgumentError("mass matrix must be positive definite"))
        new{T}(converted)
    end
end

"""Fixed Euclidean metric specified by a low-rank inverse-mass update.

`inverse_mass = Diagonal(diagonal) + basis * update * basis'`. The current
Reference backend materializes the corresponding dense mass matrix; the
factorized `O(nk)` execution optimization is deliberately separate from the
metric's semantics.
"""
struct RankUpdateMetric{T<:AbstractFloat}
    diagonal::Vector{T}
    basis::Matrix{T}
    update::Matrix{T}
    inverse_mass::Matrix{T}
    mass::Matrix{T}
    function RankUpdateMetric(diagonal::AbstractVector{T},
            basis::AbstractMatrix{T}, update::AbstractMatrix{T}) where {T<:AbstractFloat}
        a = collect(diagonal)
        b, d = Matrix(basis), Matrix(update)
        isempty(a) && throw(ArgumentError("metric dimension must be positive"))
        all(x -> isfinite(x) && x > 0, a) || throw(ArgumentError(
            "rank-update diagonal must be finite and positive"))
        size(b, 1) == length(a) || throw(DimensionMismatch("rank-update basis"))
        size(d) == (size(b, 2), size(b, 2)) ||
            throw(DimensionMismatch("rank-update inner matrix"))
        all(isfinite, b) && all(isfinite, d) ||
            throw(ArgumentError("rank-update factors must be finite"))
        issymmetric(d) ||
            throw(ArgumentError("rank-update inner matrix must be symmetric"))
        precision = Matrix(Symmetric(Diagonal(a) + b * d * b'))
        isposdef(precision) ||
            throw(ArgumentError("rank-update inverse mass must be positive definite"))
        mass = Matrix(inv(Symmetric(precision)))
        new{T}(a, b, d, precision, mass)
    end
end

struct MetricHMC{F,G,M}
    logdensity::F
    gradient::G
    metric::M
    step_size::Float64
    steps::Int
    function MetricHMC(logdensity::F, gradient::G, metric::M,
            step_size::Real, steps::Integer=10) where
            {F,G,M<:Union{DiagonalMetric,DenseMetric,RankUpdateMetric}}
        converted = Float64(step_size)
        isfinite(converted) && converted > 0 ||
            throw(ArgumentError("step size must be finite and positive"))
        steps > 0 || throw(ArgumentError("leapfrog steps must be positive"))
        new{F,G,M}(logdensity, gradient, metric, converted, Int(steps))
    end
end

metric_mass(metric::DiagonalMetric) = metric.mass
metric_mass(metric::DenseMetric) = metric.mass
metric_mass(metric::RankUpdateMetric) = metric.mass

struct MetricMultinomialHMC{F,G,M}
    logdensity::F
    gradient::G
    metric::M
    step_size::Float64
    steps::Int
    integrator::Symbol
    jitter::Float64
    function MetricMultinomialHMC(logdensity::F, gradient::G, metric::M,
            step_size::Real, steps::Integer=10;
            integrator::Symbol=:leapfrog, jitter::Real=0.1) where
            {F,G,M<:Union{DiagonalMetric,DenseMetric,RankUpdateMetric}}
        converted = Float64(step_size)
        isfinite(converted) && converted > 0 ||
            throw(ArgumentError("step size must be finite and positive"))
        steps > 0 || throw(ArgumentError("trajectory length must be positive"))
        kind, jitter_amount, _ =
            _hmc_integrator_parameters(integrator, jitter, 1.0)
        kind in (:leapfrog, :jittered) || throw(ArgumentError(
            "fixed multinomial HMC supports :leapfrog and :jittered; " *
            "tempered intermediate selection requires a weighting theorem"))
        new{F,G,M}(logdensity, gradient, metric, converted, Int(steps), kind,
            jitter_amount)
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

function _multinomial_hmc_step!(source::Runtime.AbstractRandomSource,
        sampler::MetricMultinomialHMC, current::AbstractVector{<:Real})
    step_size = sampler.integrator === :jittered ?
        sampler.step_size * (1 + sampler.jitter *
            (2Runtime.uniform_unit!(source) - 1)) : sampler.step_size
    Reference.metric_multinomial_hmc_step!(source, sampler.logdensity,
        sampler.gradient, step_size, sampler.steps, current,
        metric_mass(sampler.metric))
end

function step(rng::AbstractRNG, sampler::MetricMultinomialHMC,
        current::AbstractVector{<:Real})
    _multinomial_hmc_step!(Runtime.RNGSource(rng), sampler, current)
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
        Runtime.checked_positive_float(step_size, "step size")
        Runtime.checked_positive_count(steps, "leapfrog steps")
        new{F,G}(logdensity, gradient, step_size, steps)
    end
end

function ScalarHMC(logdensity::F, gradient::G, step_size::Real,
        steps::Integer=10) where {F,G}
    converted = Runtime.checked_positive_float(step_size, "step size")
    converted_steps = Runtime.checked_positive_count(steps, "leapfrog steps")
    ScalarHMC{F,G}(logdensity, gradient, converted, converted_steps)
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

"""Build scalar HMC from a generated restricted potential and derivative.

The expression evaluator supplies both the negative log-density value and its
symbolic derivative. Lean checks the generated expression semantics; Float64
leapfrog arithmetic, acceptance, and RNG behavior retain the documented
runtime-refinement boundary.
"""
function restricted_potential_hmc(potential::RestrictedExpr,
        step_size::Real, steps::Integer=10)
    logdensity(x) = -first(restricted_value_gradient(potential, x))
    gradient(x) = last(restricted_value_gradient(potential, x))
    ScalarHMC(logdensity, gradient, step_size, steps)
end

struct GaussianRWMH{F}
    logdensity::F
    scale::Float64
    function GaussianRWMH(logdensity::F, scale::Real) where {F}
        converted = Runtime.checked_positive_float(scale, "scale")
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

"""Build Gaussian random-walk MH from a generated restricted potential.

The expression denotes negative log density, so the adapter negates its value.
Lean checks the generated artifact and its exact-real interpretation; Float64
evaluation, proposal arithmetic, and RNG behavior retain the documented
runtime-refinement boundary.
"""
function restricted_potential_rwmh(potential::RestrictedExpr, scale::Real)
    logdensity(x) = -first(restricted_value_gradient(potential, x))
    GaussianRWMH(logdensity, scale)
end

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

"""Gaussian RWMH on an open-unit-interval parameter through artanh.

The exact convention matches generated descriptor `open-unit-artanh`:
`y = atanh(2x-1)` and `x = (tanh(y)+1)/2`. The unconstrained log density adds
`log(1-tanh(y)^2)-log(2)`, the inverse log-Jacobian.
"""
struct OpenUnitTransformedRWMH{F}
    logdensity::F
    scale::Float64
    function OpenUnitTransformedRWMH(logdensity::F, scale::Real) where {F}
        converted = Float64(scale)
        isfinite(converted) && converted > 0 ||
            throw(ArgumentError("scale must be finite and positive"))
        new{F}(logdensity, converted)
    end
end

function step(rng::AbstractRNG, sampler::OpenUnitTransformedRWMH, current::Real)
    x = Float64(current)
    isfinite(x) && 0 < x < 1 ||
        throw(ArgumentError("open-unit transformed state must lie strictly in (0,1)"))
    unconstrained(y) = begin
        t = tanh(y)
        transformed = (t + 1) / 2
        sampler.logdensity(transformed) + log1p(-t * t) - log(2)
    end
    next_y = step(rng, GaussianRWMH(unconstrained, sampler.scale), atanh(2x - 1))
    next = (tanh(next_y) + 1) / 2
    isfinite(next) && 0 < next < 1 ||
        throw(DomainError(next_y, "inverse transformed state left the open unit interval"))
    next
end

step(sampler::OpenUnitTransformedRWMH, current::Real) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::OpenUnitTransformedRWMH,
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

sample(sampler::OpenUnitTransformedRWMH, initial::Real, count::Integer) =
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

"""Executable diagnostic for the proved indefinitely adaptive Bool chain.

At zero-based iteration `n`, the next-state probability is `1/2 ± 1/(4(n+1))`,
with the sign selected by the current state. Lean proves setwise convergence
of the ideal-real chain via a common Doeblin component. This Float64 client is
a conformance diagnostic, not an instantiation of a floating-point refinement
certificate.
"""
struct IndefiniteAdaptiveBool end

function sample(rng::AbstractRNG, ::IndefiniteAdaptiveBool,
        initial::Bool, count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    states = BitVector(undef, count)
    current = initial
    for index in eachindex(states)
        bias = 1 / (4 * index)
        probability_true = 0.5 + (current ? bias : -bias)
        current = rand(rng) < probability_true
        states[index] = current
    end
    states
end

sample(sampler::IndefiniteAdaptiveBool, initial::Bool, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)

"""Executable client for the proved continuous never-freezing refresh rule.

The complete-history empirical mean is retained with weight `1/(n+2)` at
stage `n`; otherwise `target_draw(rng)` supplies an independent target draw.
Lean proves setwise convergence for the ideal measurable kernel for every
probability target. Callback equality and floating-point arithmetic remain
runtime conformance obligations.
"""
struct IndefiniteAdaptiveContinuousRefresh{F}
    target_draw::F
end

function sample(rng::AbstractRNG,
        sampler::IndefiniteAdaptiveContinuousRefresh,
        initial::Real, count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    current = Float64(initial)
    isfinite(current) || throw(ArgumentError("initial state must be finite"))
    states = Vector{Float64}(undef, count)
    history_sum = current
    for index in eachindex(states)
        anchor = history_sum / index
        weight = 1 / (index + 1)
        current = rand(rng) < weight ? anchor : Float64(sampler.target_draw(rng))
        isfinite(current) || throw(DomainError(current,
            "target draw must be finite"))
        states[index] = current
        history_sum += current
    end
    states
end

sample(sampler::IndefiniteAdaptiveContinuousRefresh,
        initial::Real, count::Integer) =
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

The finite `max_steps` and `max_shrink` guards are runtime controls. Exhausting
the shrinkage budget gives an explicit identity fallback, so the transition is
total. Reference/Optimized execution is differentially tested; exact
stationarity still requires instantiating Lean's joint trace-reversal premise
for this concrete bracket algorithm.
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

"""Build practical slice sampling from a generated restricted potential.

The expression denotes negative log density, so the adapter negates its value.
Its exact-real artifact semantics are proved in Lean; runtime trace refinement
and finite-precision/RNG boundaries remain represented by the slice
certificate API.
"""
function restricted_potential_slice(potential::RestrictedExpr, width::Real;
        max_steps::Integer=100, max_shrink::Integer=10_000)
    logdensity(x) = -first(restricted_value_gradient(potential, x))
    SteppingOutSlice(logdensity, width; max_steps=max_steps,
        max_shrink=max_shrink)
end

"""Observed comparison inputs from one Reference stepping-out update."""
struct SteppingOutSliceTrace
    result::Float64
    current::Float64
    base::Float64
    uniform::Float64
    log_uniform::Float64
    threshold::Float64
    kinds::Vector{Certificates.SliceComparisonKind}
    positions::Vector{Float64}
    values::Vector{Float64}
end

"""Execute and record every ordered stepping-out/shrinkage comparison.

This records computed values only. Ideal values and justified error bounds are
separate proof inputs supplied to `certify_stepping_out_slice_trace`.
"""
function trace_stepping_out_slice(rng::AbstractRNG, sampler::SteppingOutSlice,
        current::Real)
    kinds = Certificates.SliceComparisonKind[]
    positions = Float64[]
    values = Float64[]
    base = Ref{Float64}()
    uniform = Ref{Float64}()
    log_uniform = Ref{Float64}()
    threshold = Ref{Float64}()
    function observe_threshold(observed_base, observed_uniform, observed_log,
            observed_threshold)
        base[] = observed_base
        uniform[] = observed_uniform
        log_uniform[] = observed_log
        threshold[] = observed_threshold
        nothing
    end
    function observe(kind, position, value, observed_threshold)
        push!(kinds, kind === :stopBelow ? Certificates.StopBelow :
            Certificates.AcceptAbove)
        push!(positions, position)
        push!(values, value)
        threshold[] = observed_threshold
        nothing
    end
    result = Reference.stepping_out_slice_step!(Runtime.RNGSource(rng),
        sampler.logdensity, sampler.width, current, sampler.max_steps,
        sampler.max_shrink; threshold_observer=observe_threshold,
        comparison_observer=observe)
    SteppingOutSliceTrace(result, Float64(current), base[], uniform[],
        log_uniform[], threshold[], kinds, positions, values)
end

"""Attach ideal values and bounds to an observed practical-slice trace."""
function certify_stepping_out_slice_trace(trace::SteppingOutSliceTrace,
        ideal_threshold::Real, threshold_bound::Real,
        ideal_values::AbstractVector{<:Real},
        value_bounds::AbstractVector{<:Real}; precision::Integer=256)
    Certificates.certify_slice_decision_trace(trace.kinds, trace.threshold,
        ideal_threshold, threshold_bound, trace.values, ideal_values,
        value_bounds; precision=precision)
end

"""Generated-quartic callback evidence for one observed slice execution.

Polynomial callback outputs and the final threshold addition are checked as
exact rationals. The ideal value and error for `log(u)` remain explicit inputs.
"""
struct RestrictedQuarticSliceTraceCertificate
    trace::SteppingOutSliceTrace
    current_callback::RestrictedQuarticFloat64Certificate
    comparison_callbacks::Vector{RestrictedQuarticFloat64Certificate}
    threshold::Certificates.SliceThresholdCertificate
    decisions::Certificates.SliceDecisionTraceCertificate
end

function certify_restricted_quartic_slice_trace(trace::SteppingOutSliceTrace,
        ideal_log_uniform::Real, log_uniform_bound::Real;
        precision::Integer=256)
    current_callback = certify_restricted_quartic_float64(trace.current)
    trace.base == -current_callback.computed_value || throw(ArgumentError(
        "runtime base does not match the generated quartic callback"))
    callbacks = certify_restricted_quartic_float64.(trace.positions)
    all(zip(trace.values, callbacks)) do (value, callback)
        value == -callback.computed_value
    end || throw(ArgumentError(
        "runtime comparison does not match the generated quartic callback"))

    exact_threshold = Rational{BigInt}(trace.threshold)
    exact_operands = Rational{BigInt}(trace.base) +
        Rational{BigInt}(trace.log_uniform)
    addition_error = abs(exact_threshold - exact_operands)
    threshold = Certificates.certify_slice_threshold(
        trace.base, -current_callback.ideal_value,
        current_callback.value_error,
        trace.log_uniform, ideal_log_uniform, log_uniform_bound,
        trace.threshold, addition_error; precision=precision)
    ideal_values = [-callback.ideal_value for callback in callbacks]
    value_bounds = [callback.value_error for callback in callbacks]
    decisions = certify_stepping_out_slice_trace(trace, threshold,
        ideal_values, value_bounds; precision=precision)
    RestrictedQuarticSliceTraceCertificate(trace, current_callback,
        callbacks, threshold, decisions)
end

function certify_restricted_quartic_slice_trace(trace::SteppingOutSliceTrace,
        log_uniform::Certificates.SliceLogUniformCertificate;
        precision::Integer=256)
    trace.uniform == log_uniform.uniform.computed || throw(ArgumentError(
        "log-uniform certificate does not describe this runtime draw"))
    trace.log_uniform == log_uniform.log.computed || throw(ArgumentError(
        "log-uniform certificate does not describe this runtime logarithm"))
    certify_restricted_quartic_slice_trace(trace, log_uniform.log.ideal,
        log_uniform.log.bound; precision=precision)
end

function certify_stepping_out_slice_trace(trace::SteppingOutSliceTrace,
        threshold::Certificates.SliceThresholdCertificate,
        ideal_values::AbstractVector{<:Real},
        value_bounds::AbstractVector{<:Real}; precision::Integer=256)
    trace.threshold == threshold.threshold.computed || throw(ArgumentError(
        "threshold certificate does not describe this runtime trace"))
    Certificates.certify_slice_decision_trace(trace.kinds, threshold,
        trace.values, ideal_values, value_bounds; precision=precision)
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

"""Certified nonlinear two-model reversible-jump sampler.

The empty model is represented by `nothing`; the planar model is a pair of
`Float64`s. The exact Lean client proves invariance for the nonlinear
triangular transport. This Julia implementation mirrors that transport; its
uniform draws and arithmetic remain the usual runtime boundary.
"""
struct ShearedBirthDeathRJ end

"""Inverse nonlinear shear, useful for checking curved-strip membership."""
function sheared_birth_unshear(state::Tuple{<:Real,<:Real})
    y1, y2 = Float64(state[1]), Float64(state[2])
    (y1 - y2^3, y2)
end

function step(rng::AbstractRNG, ::ShearedBirthDeathRJ, current)
    Reference.sheared_birth_death_step!(Runtime.RNGSource(rng), current)
end

step(sampler::ShearedBirthDeathRJ, current) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::ShearedBirthDeathRJ,
        initial, count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    states = Vector{Union{Nothing,Tuple{Float64,Float64}}}(undef, count)
    current = initial
    for index in eachindex(states)
        current = step(rng, sampler, current)
        states[index] = current
    end
    states
end

sample(sampler::ShearedBirthDeathRJ, initial, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)

"""Executable client of the proved three-dimensional product RJ transport."""
struct SpatialBirthDeathRJ end

function step(rng::AbstractRNG, ::SpatialBirthDeathRJ, current)
    Reference.spatial_birth_death_step!(Runtime.RNGSource(rng), current)
end

step(sampler::SpatialBirthDeathRJ, current) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::SpatialBirthDeathRJ,
        initial, count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    states = Vector{Union{Nothing,NTuple{3,Float64}}}(undef, count)
    current = initial
    for index in eachindex(states)
        current = step(rng, sampler, current)
        states[index] = current
    end
    states
end

sample(sampler::SpatialBirthDeathRJ, initial, count::Integer) =
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

"""Canonical certified subpartition of arbitrary root-retaining rows.

For each root, retain only leaves whose complete raw row equals the root's raw
row. This never adds a candidate. Lean proves these coherent subrows always
form a reroot-invariant partition and preserve an already certified family
exactly. Missing roots remain an error because no safe nonempty subrow can be
derived from such malformed builder output.
"""
function coherent_dynamic_tree(
        rows::AbstractVector{<:AbstractVector{<:Integer}})
    raw = certify_dynamic_tree(rows).candidates
    for root in eachindex(raw)
        root in raw[root] || throw(ArgumentError(
            "dynamic-tree candidate row must retain its root"))
    end
    coherent = [[leaf for leaf in raw[root] if raw[leaf] == raw[root]]
        for root in eachindex(raw)]
    certificate = certify_dynamic_tree(coherent)
    certificate.valid || error("internal coherent-subrow certificate failure")
    certificate
end

"""Canonical direction trace for a root in a completed doubling tree.

`root` is Julia's one-based leaf index and `depth` is the tree height. Direction
index zero is returned first: `true` grows right (root bit zero), while `false`
grows left (root bit one). Thus the returned vector is the executable form of
Lean's `directionTraceForRoot` and uses the same least-significant-bit-first
encoding.
"""
function completed_tree_direction_trace(root::Integer, depth::Integer)
    descriptor = Reference.DYNAMIC_TREES["checked-recursive-doubling"]
    descriptor.root_encoding == "lsb-first-grow-right-zero" || error(
        "generated dynamic-tree root encoding does not match the runtime")
    depth >= 0 || throw(ArgumentError("tree depth must be nonnegative"))
    depth < 8 * sizeof(Int) - 1 || throw(ArgumentError(
        "tree depth exceeds the bounded machine-index representation"))
    count = 1 << depth
    1 <= root <= count || throw(BoundsError(1:count, root))
    offset = root - 1
    Bool[(offset & (1 << level)) == 0 for level in 0:(depth - 1)]
end

"""C.4-admissible roots of one completed power-of-two recursive tree.

Root `r` receives the unique least-significant-bit-first direction sequence
that reconstructs the common completed tree from `r`. A root is C.4-admissible
exactly when its recursive U-turn checks retain the entire orbit. Admissible
roots share one component and every other root is an explicit singleton, so
the returned rows always pass the reroot certificate. This mirrors Lean's
`CompletedTreeStoppingData` construction.
"""
function completed_tree_c4_candidates(
        positions::AbstractVector{<:AbstractVector{<:Real}},
        momenta::AbstractVector{<:AbstractVector{<:Real}})
    count = length(positions)
    count == length(momenta) || throw(DimensionMismatch(
        "position and momentum trajectories must match"))
    count > 0 && ispow2(count) || throw(ArgumentError(
        "a completed tree must have a positive power-of-two state count"))
    depth = trailing_zeros(count)
    admissible = Int[]
    for root in 1:count
        directions = completed_tree_direction_trace(root, depth)
        rows = Reference.recursive_doubling_rows(
            positions, momenta, directions)
        length(rows[root]) == count && push!(admissible, root)
    end
    rows = [root in admissible ? copy(admissible) : [root]
        for root in 1:count]
    certificate = certify_dynamic_tree(rows)
    certificate.valid || error("internal C.4 partition certificate failure")
    certificate
end

completed_tree_c4_candidates(
        positions::AbstractVector{<:Real}, momenta::AbstractVector{<:Real}) =
    completed_tree_c4_candidates([[Float64(q)] for q in positions],
        [[Float64(p)] for p in momenta])

"""Target-weighted selection from a checked completed dynamic tree.

This is the executable counterpart of Lean's `checkedKernel_stationary`:
selection is enabled only when the complete candidate-row family passes the
root-retention and reroot-equality certificate. `current` and the returned
state use Julia's one-based indexing.
"""
function certified_dynamic_select!(source::Runtime.AbstractRandomSource,
        certificate::DynamicTreeCertificate,
        target_weights::AbstractVector{<:Integer}, current::Integer)
    certificate.valid || throw(ArgumentError(
        "dynamic-tree candidate rows failed reroot certification"))
    count = length(certificate.candidates)
    length(target_weights) == count || throw(DimensionMismatch(
        "target weights must match the dynamic-tree state count"))
    1 <= current <= count || throw(BoundsError(certificate.candidates, current))
    all(>(0), target_weights) || throw(ArgumentError(
        "dynamic-tree target weights must be strictly positive"))
    candidates = certificate.candidates[current]
    local_weights = Int[target_weights[state] for state in candidates]
    selected = Reference.categorical_index!(source, local_weights)
    candidates[selected + 1]
end

certified_dynamic_select(rng::AbstractRNG,
        certificate::DynamicTreeCertificate,
        target_weights::AbstractVector{<:Integer}, current::Integer) =
    certified_dynamic_select!(Runtime.RNGSource(rng), certificate,
        target_weights, current)

certified_dynamic_select(certificate::DynamicTreeCertificate,
        target_weights::AbstractVector{<:Integer}, current::Integer) =
    certified_dynamic_select(Random.default_rng(), certificate,
        target_weights, current)

"""Total checked dynamic transition: invalid certificates make no move."""
function safe_dynamic_select!(source::Runtime.AbstractRandomSource,
        certificate::DynamicTreeCertificate,
        target_weights::AbstractVector{<:Integer}, current::Integer)
    count = length(certificate.candidates)
    length(target_weights) == count || throw(DimensionMismatch(
        "target weights must match the dynamic-tree state count"))
    1 <= current <= count || throw(BoundsError(certificate.candidates, current))
    all(>(0), target_weights) || throw(ArgumentError(
        "dynamic-tree target weights must be strictly positive"))
    certificate.valid || return Int(current)
    certified_dynamic_select!(source, certificate, target_weights, current)
end

safe_dynamic_select(rng::AbstractRNG, certificate::DynamicTreeCertificate,
        target_weights::AbstractVector{<:Integer}, current::Integer) =
    safe_dynamic_select!(Runtime.RNGSource(rng), certificate,
        target_weights, current)

safe_dynamic_select(certificate::DynamicTreeCertificate,
        target_weights::AbstractVector{<:Integer}, current::Integer) =
    safe_dynamic_select(Random.default_rng(), certificate,
        target_weights, current)

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

"""Root-independent completed binary tree mirrored by Lean's recursive tree.

Each internal node records whether the join between its completed left and
right subtrees is blocked. It deliberately represents aggregation after tree
completion; it is not a root-dependent first-U-turn stopping algorithm.
"""
abstract type RecursiveBarrierTree end

struct RecursiveBarrierLeaf <: RecursiveBarrierTree end

struct RecursiveBarrierNode <: RecursiveBarrierTree
    left::RecursiveBarrierTree
    blocked::Bool
    right::RecursiveBarrierTree
end

recursive_barriers(::RecursiveBarrierLeaf) = Bool[]
function recursive_barriers(tree::RecursiveBarrierNode)
    vcat(recursive_barriers(tree.left), tree.blocked,
        recursive_barriers(tree.right))
end

"""Certify the candidate partition obtained by recursive subtree joins."""
certified_recursive_partition(tree::RecursiveBarrierTree) =
    certified_orbit_partition(recursive_barriers(tree))

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
        # A `break` in Julia's comma-form nested loop exits the complete loop
        # nest, not just the `right` loop. Accumulate instead so every split is
        # inspected, matching Lean's all-scales barrier definition.
        barriers[split] |= dot(displacement, p[left]) < 0 ||
            dot(displacement, p[right]) < 0
    end
    certified_orbit_partition(barriers)
end

"""Build root-dependent first-stop endpoint U-turn candidate rows.

For each possible root, symmetrically enlarge the interval by one state at a
time and stop before the first interval whose endpoint displacement has
negative inner product with either endpoint momentum.  The returned
`DynamicTreeCertificate` always records the rows, but `valid` is true only
when the completed rows satisfy the reroot condition required by the verified
dynamic-orbit selection theorem.  Thus this is an executable first-stop
experiment and checker, not an unconditional correctness claim for NUTS.
"""
function first_stop_endpoint_uturn_candidates(
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

    count = length(q)
    rows = Vector{Vector{Int}}(undef, count)
    for root in 1:count
        accepted_left = root
        accepted_right = root
        for radius in 1:count
            left = max(1, root - radius)
            right = min(count, root + radius)
            left == accepted_left && right == accepted_right && break
            displacement = q[right] .- q[left]
            if dot(displacement, p[left]) < 0 || dot(displacement, p[right]) < 0
                break
            end
            accepted_left, accepted_right = left, right
        end
        rows[root] = collect(accepted_left:accepted_right)
    end
    certify_dynamic_tree(rows)
end

first_stop_endpoint_uturn_candidates(
        positions::AbstractVector{<:Real}, momenta::AbstractVector{<:Real}) =
    first_stop_endpoint_uturn_candidates([[Float64(q)] for q in positions],
        [[Float64(p)] for p in momenta])

"""Checked root-dependent recursive-doubling U-turn rows.

`directions[d]` chooses the side of the size-`2^(d-1)` expansion at depth
`d`. Every newly completed subtree and its join with the retained interval are
tested by the endpoint U-turn rule; a failing subtree is excluded. Rows for
all possible roots are then passed to the global reroot checker. The returned
certificate may be invalid—this function exposes standard-NUTS-style rooted
recursion without assuming the equivalence that still needs proof.
"""
function recursive_doubling_uturn_candidates(
        positions::AbstractVector{<:AbstractVector{<:Real}},
        momenta::AbstractVector{<:AbstractVector{<:Real}},
        directions::AbstractVector{Bool})
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

    turns(left, right) = begin
        displacement = q[right] .- q[left]
        dot(displacement, p[left]) < 0 || dot(displacement, p[right]) < 0
    end
    function subtree_turns(left, right)
        left == right && return false
        turns(left, right) && return true
        middle = (left + right) ÷ 2
        subtree_turns(left, middle) || subtree_turns(middle + 1, right)
    end

    count = length(q)
    rows = Vector{Vector{Int}}(undef, count)
    for root in 1:count
        left = right = root
        for (depth, grow_right) in pairs(directions)
            width = 1 << (depth - 1)
            proposed_left = grow_right ? left : left - width
            proposed_right = grow_right ? right + width : right
            proposed_left >= 1 && proposed_right <= count || break
            new_left = grow_right ? right + 1 : proposed_left
            new_right = grow_right ? proposed_right : left - 1
            # Exclude a turning new subtree or a turning completed join.
            (subtree_turns(new_left, new_right) ||
                turns(proposed_left, proposed_right)) && break
            left, right = proposed_left, proposed_right
        end
        rows[root] = collect(left:right)
    end
    certify_dynamic_tree(rows)
end

recursive_doubling_uturn_candidates(
        positions::AbstractVector{<:Real}, momenta::AbstractVector{<:Real},
        directions::AbstractVector{Bool}) =
    recursive_doubling_uturn_candidates([[Float64(q)] for q in positions],
        [[Float64(p)] for p in momenta], directions)

"""Execute a dynamic-tree builder selected by Lean-generated metadata.

The generated descriptor fixes the recursive builder, endpoint U-turn rule,
subtree exclusion, and checked-or-identity policy. This function returns the
certificate; callers must use `safe_dynamic_select!` for selection.
"""
function generated_dynamic_tree(name::AbstractString, positions, momenta,
        directions::AbstractVector{Bool})
    descriptor = get(Reference.DYNAMIC_TREES, String(name), nothing)
    descriptor === nothing &&
        throw(ArgumentError("unknown generated dynamic tree: $name"))
    descriptor.builder == "recursive-doubling" &&
        descriptor.trace_policy == "fair-direction-bits" &&
        descriptor.stop_rule == "endpoint-uturn" &&
        descriptor.subtree_policy == "recursive-exclusion" &&
        descriptor.selection_policy == "eligible-count-streaming" &&
        descriptor.failure_policy == "checked-or-identity" ||
        error("unsupported generated dynamic-tree descriptor")
    certify_dynamic_tree(
        Reference.recursive_doubling_rows(positions, momenta, directions))
end

"""Draw from completed eligible subtrees using the Lean-generated policy."""
streaming_eligible_select(rng::AbstractRNG,
        segments::AbstractVector{<:AbstractVector{<:Integer}}) =
    Reference.streaming_eligible_select!(Runtime.RNGSource(rng), segments)

streaming_eligible_select(
        segments::AbstractVector{<:AbstractVector{<:Integer}}) =
    streaming_eligible_select(Random.default_rng(), segments)

"""Certified conservative dynamic-trajectory HMC.

Each transition refreshes Gaussian momentum, chooses a randomized origin in a
fixed complete leapfrog orbit, constructs Lean-mirrored all-scales U-turn
barriers on that complete orbit, and samples by Boltzmann weight within the
certified reroot-invariant component containing the origin. This is an
executable client of the checked dynamic-tree theorem. It is intentionally
more conservative than root-dependent first-stop NUTS and is not claimed to
be equivalent to standard NUTS.
"""
struct CertifiedDynamicHMC{F,G}
    logdensity::F
    gradient::G
    step_size::Float64
    steps::Int
    function CertifiedDynamicHMC(logdensity::F, gradient::G, step_size::Real,
            steps::Integer=15) where {F,G}
        converted = Float64(step_size)
        isfinite(converted) && converted > 0 ||
            throw(ArgumentError("step size must be finite and positive"))
        steps > 0 || throw(ArgumentError("trajectory length must be positive"))
        new{F,G}(logdensity, gradient, converted, Int(steps))
    end
end

function _certified_dynamic_hmc_step!(source::Runtime.AbstractRandomSource,
        selector, sampler::CertifiedDynamicHMC,
        current::AbstractVector{<:Real})
    q = Float64.(current)
    isempty(q) && throw(ArgumentError("position cannot be empty"))
    all(isfinite, q) || throw(ArgumentError("position must be finite"))
    p = [Runtime.standard_normal!(source) for _ in eachindex(q)]
    origin = Int(Runtime.draw_below!(source, sampler.steps + 1))
    for _ in 1:origin
        q, p = Optimized.vector_leapfrog(sampler.gradient,
            -sampler.step_size, q, p)
    end
    positions = Vector{Vector{Float64}}(undef, sampler.steps + 1)
    momenta = similar(positions)
    positions[1], momenta[1] = copy(q), copy(p)
    for index in 2:(sampler.steps + 1)
        q, p = Optimized.vector_leapfrog(sampler.gradient,
            sampler.step_size, q, p)
        positions[index], momenta[index] = copy(q), copy(p)
    end
    certificate = certified_spanning_uturn_partition(positions, momenta)
    current_index = origin + 1
    candidates = certificate.candidates[current_index]
    logweights = [begin
        value = Float64(sampler.logdensity(positions[index])) -
            sum(abs2, momenta[index]) / 2
        isfinite(value) || throw(DomainError(value,
            "dynamic trajectory log weight must be finite"))
        value
    end for index in candidates]
    selected = selector(source, candidates, logweights)
    copy(positions[selected])
end

function step(rng::AbstractRNG, sampler::CertifiedDynamicHMC,
        current::AbstractVector{<:Real})
    _certified_dynamic_hmc_step!(Runtime.RNGSource(rng),
        Reference.dynamic_select_float!, sampler, current)
end

step(sampler::CertifiedDynamicHMC, current::AbstractVector{<:Real}) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::CertifiedDynamicHMC,
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

sample(sampler::CertifiedDynamicHMC, initial::AbstractVector{<:Real},
        count::Integer) = sample(Random.default_rng(), sampler, initial, count)

"""Checked root-dependent first-stop dynamic HMC experiment.

The complete randomized-origin orbit is inspected from every possible root.
Each row stops before its first endpoint U-turn. The resulting row family is
then passed through the same reroot checker as Lean's
`checkedOrIdentityKernel`: a valid family uses target-weighted selection,
while an invalid family returns the current position without consuming a
selection draw. This makes the certification boundary executable; it is not a
claim that first-stop rows always implement standard NUTS.
"""
struct CheckedFirstStopDynamicHMC{F,G}
    logdensity::F
    gradient::G
    step_size::Float64
    steps::Int
    function CheckedFirstStopDynamicHMC(logdensity::F, gradient::G,
            step_size::Real, steps::Integer=15) where {F,G}
        converted = Float64(step_size)
        isfinite(converted) && converted > 0 ||
            throw(ArgumentError("step size must be finite and positive"))
        steps > 0 || throw(ArgumentError("trajectory length must be positive"))
        new{F,G}(logdensity, gradient, converted, Int(steps))
    end
end

function _checked_first_stop_dynamic_hmc_step!(
        source::Runtime.AbstractRandomSource, selector,
        sampler::CheckedFirstStopDynamicHMC,
        current::AbstractVector{<:Real})
    initial = Float64.(current)
    isempty(initial) && throw(ArgumentError("position cannot be empty"))
    all(isfinite, initial) || throw(ArgumentError("position must be finite"))
    q = copy(initial)
    p = [Runtime.standard_normal!(source) for _ in eachindex(q)]
    origin = Int(Runtime.draw_below!(source, sampler.steps + 1))
    for _ in 1:origin
        q, p = Optimized.vector_leapfrog(sampler.gradient,
            -sampler.step_size, q, p)
    end
    positions = Vector{Vector{Float64}}(undef, sampler.steps + 1)
    momenta = similar(positions)
    positions[1], momenta[1] = copy(q), copy(p)
    for index in 2:(sampler.steps + 1)
        q, p = Optimized.vector_leapfrog(sampler.gradient,
            sampler.step_size, q, p)
        positions[index], momenta[index] = copy(q), copy(p)
    end
    certificate = first_stop_endpoint_uturn_candidates(positions, momenta)
    certificate.valid || return initial
    candidates = certificate.candidates[origin + 1]
    logweights = [begin
        value = Float64(sampler.logdensity(positions[index])) -
            sum(abs2, momenta[index]) / 2
        isfinite(value) || throw(DomainError(value,
            "dynamic trajectory log weight must be finite"))
        value
    end for index in candidates]
    copy(positions[selector(source, candidates, logweights)])
end

function step(rng::AbstractRNG, sampler::CheckedFirstStopDynamicHMC,
        current::AbstractVector{<:Real})
    _checked_first_stop_dynamic_hmc_step!(Runtime.RNGSource(rng),
        Reference.dynamic_select_float!, sampler, current)
end

step(sampler::CheckedFirstStopDynamicHMC,
        current::AbstractVector{<:Real}) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::CheckedFirstStopDynamicHMC,
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

sample(sampler::CheckedFirstStopDynamicHMC,
        initial::AbstractVector{<:Real}, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)

"""Completed-tree C.4 dynamic HMC.

Each iteration builds one randomized-origin power-of-two leapfrog orbit,
reruns the recursive endpoint-U-turn checks from every possible root using its
unique reconstruction directions, and selects within the resulting C.4
admissible component. Nonadmissible current roots make an explicit identity
move. This is the executable shape of Lean's completed-tree rooted-trace
theorem; floating-point callback refinement remains separate.
"""
struct CompletedTreeC4DynamicHMC{F,G}
    logdensity::F
    gradient::G
    step_size::Float64
    depth::Int
    function CompletedTreeC4DynamicHMC(logdensity::F, gradient::G,
            step_size::Real, depth::Integer=3) where {F,G}
        converted = Float64(step_size)
        isfinite(converted) && converted > 0 ||
            throw(ArgumentError("step size must be finite and positive"))
        0 <= depth < (8sizeof(Int) - 1) || throw(ArgumentError(
            "tree depth must be nonnegative and fit the platform index"))
        new{F,G}(logdensity, gradient, converted, Int(depth))
    end
end

function _completed_tree_c4_dynamic_hmc_step!(
        source::Runtime.AbstractRandomSource, selector,
        sampler::CompletedTreeC4DynamicHMC,
        current::AbstractVector{<:Real})
    initial = Float64.(current)
    isempty(initial) && throw(ArgumentError("position cannot be empty"))
    all(isfinite, initial) || throw(ArgumentError("position must be finite"))
    count = 1 << sampler.depth
    q = copy(initial)
    p = [Runtime.standard_normal!(source) for _ in eachindex(q)]
    origin = Int(Runtime.draw_below!(source, count))
    for _ in 1:origin
        q, p = Optimized.vector_leapfrog(sampler.gradient,
            -sampler.step_size, q, p)
    end
    positions = Vector{Vector{Float64}}(undef, count)
    momenta = similar(positions)
    positions[1], momenta[1] = copy(q), copy(p)
    for index in 2:count
        q, p = Optimized.vector_leapfrog(sampler.gradient,
            sampler.step_size, q, p)
        positions[index], momenta[index] = copy(q), copy(p)
    end
    certificate = completed_tree_c4_candidates(positions, momenta)
    candidates = certificate.candidates[origin + 1]
    length(candidates) == 1 && return initial
    logweights = [begin
        value = Float64(sampler.logdensity(positions[index])) -
            sum(abs2, momenta[index]) / 2
        isfinite(value) || throw(DomainError(value,
            "dynamic trajectory log weight must be finite"))
        value
    end for index in candidates]
    copy(positions[selector(source, candidates, logweights)])
end

function step(rng::AbstractRNG, sampler::CompletedTreeC4DynamicHMC,
        current::AbstractVector{<:Real})
    _completed_tree_c4_dynamic_hmc_step!(Runtime.RNGSource(rng),
        Reference.dynamic_select_float!, sampler, current)
end

step(sampler::CompletedTreeC4DynamicHMC,
        current::AbstractVector{<:Real}) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::CompletedTreeC4DynamicHMC,
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

sample(sampler::CompletedTreeC4DynamicHMC,
        initial::AbstractVector{<:Real}, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)

"""Checked randomized recursive-doubling dynamic HMC.

Each iteration samples a state-independent Boolean direction trace, executes
the Lean-generated recursive-doubling/endpoint-U-turn descriptor on a complete
randomized-origin orbit, and globally checks every rerooted candidate row.
Certified traces use multinomial selection; failed traces return the current
state without consuming a selector draw. This implements the proved randomized
checked-or-identity mixture, not an unconditional equivalence to standard NUTS.
"""
struct CheckedRecursiveDynamicHMC{F,G}
    logdensity::F
    gradient::G
    step_size::Float64
    steps::Int
    function CheckedRecursiveDynamicHMC(logdensity::F, gradient::G,
            step_size::Real, steps::Integer=15) where {F,G}
        converted = Float64(step_size)
        isfinite(converted) && converted > 0 ||
            throw(ArgumentError("step size must be finite and positive"))
        steps > 0 || throw(ArgumentError("trajectory length must be positive"))
        max_depth = Reference.NUTS_TREE_PROGRAMS["checked-nuts-reference"].max_depth
        BigInt(steps) + 1 < (BigInt(1) << (max_depth + 1)) ||
            throw(ArgumentError("trajectory depth exceeds the Lean NUTS program"))
        new{F,G}(logdensity, gradient, converted, Int(steps))
    end
end

function _checked_recursive_dynamic_hmc_step!(
        source::Runtime.AbstractRandomSource, sampler::CheckedRecursiveDynamicHMC,
        current::AbstractVector{<:Real})
    initial = Float64.(current)
    isempty(initial) && throw(ArgumentError("position cannot be empty"))
    all(isfinite, initial) || throw(ArgumentError("position must be finite"))
    q = copy(initial)
    p = [Runtime.standard_normal!(source) for _ in eachindex(q)]
    count = sampler.steps + 1
    origin = Int(Runtime.draw_below!(source, count))
    for _ in 1:origin
        q, p = Reference.vector_leapfrog_step(sampler.gradient,
            -sampler.step_size, q, p)
    end
    positions = Vector{Vector{Float64}}(undef, count)
    momenta = similar(positions)
    positions[1], momenta[1] = copy(q), copy(p)
    for index in 2:count
        q, p = Reference.vector_leapfrog_step(sampler.gradient,
            sampler.step_size, q, p)
        positions[index], momenta[index] = copy(q), copy(p)
    end
    depth = floor(Int, log2(count))
    directions = [Runtime.draw_below!(source, 2) == 1 for _ in 1:depth]
    program = Reference.NUTS_TREE_PROGRAMS["checked-nuts-reference"]
    selected = Reference.checked_nuts_or_identity_select!(source, program,
        positions, momenta, directions, origin + 1,
        (position, momentum) -> begin
        value = Float64(sampler.logdensity(position)) - sum(abs2, momentum) / 2
        isfinite(value) || throw(DomainError(value,
            "dynamic trajectory log weight must be finite"))
        value
    end)
    selected == origin + 1 ? initial : copy(positions[selected])
end

function step(rng::AbstractRNG, sampler::CheckedRecursiveDynamicHMC,
        current::AbstractVector{<:Real})
    _checked_recursive_dynamic_hmc_step!(Runtime.RNGSource(rng), sampler, current)
end

step(sampler::CheckedRecursiveDynamicHMC,
        current::AbstractVector{<:Real}) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::CheckedRecursiveDynamicHMC,
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

sample(sampler::CheckedRecursiveDynamicHMC,
        initial::AbstractVector{<:Real}, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)

"""Productive completed-tree NUTS Reference sampler.

This canonical public name uses the C.4 construction proved in Lean: every
possible root receives the unique direction trace that reconstructs the same
completed tree, and selection is restricted to roots that complete before a
U-turn. The independent handwritten implementation remains available as
`Optimized.NUTS`; transition equivalence between the two is not claimed.
"""
const NUTS = CompletedTreeC4DynamicHMC

"""Compatibility alias for the canonical completed-tree Reference `NUTS`."""
const VerifiedNUTS = NUTS

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

include("HMCParity.jl")
include("Public/OptimizedNUTS.jl")

end
