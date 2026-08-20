module Certificates

export BoundWitness, DecisionCertificate, certify_bound, certify_decision,
    SamplerDecisionCertificate, certify_rwmh_decision, certify_hmc_decision,
    MultinomialSelectionCertificate, certify_multinomial_selection,
    SliceComparisonCertificate, certify_slice_comparisons,
    SliceComparisonKind, SliceDecisionTraceCertificate,
    certify_slice_decision_trace, certified_slice_decisions,
    SliceThresholdCertificate, certify_slice_threshold,
    SliceLogUniformCertificate, certify_slice_log_uniform,
    ImplicitSolveCertificate, certify_implicit_solve, certifies_exact_solver,
    ContractionErrorBound, contraction_error_bound,
    AposterioriContractionRationalCertificate,
    certify_contraction_aposteriori,
    contraction_aposteriori_certificate_arguments,
    RoundedContractionResidualRationalCertificate,
    certify_rounded_contraction_residual,
    rounded_contraction_residual_certificate_arguments,
    RoundedAffineUpdateRationalCertificate,
    certify_rounded_affine_update,
    rounded_affine_update_certificate_arguments,
    RoundedContractionPairCertificate, certify_rounded_contraction_pair,
    rounded_contraction_pair_certificate_arguments,
    BoundedScalarSolverContractionTraceCertificate,
    certify_bounded_scalar_solver_contraction_trace,
    bounded_scalar_solver_contraction_certificate_arguments,
    BoundedScalarSolverPhaseTraceCertificate,
    certify_bounded_scalar_solver_phase_trace,
    bounded_scalar_solver_phase_certificate_arguments,
    BoundedScalarSolverEndpointTraceCertificate,
    certify_bounded_scalar_solver_endpoint_trace,
    bounded_scalar_solver_endpoint_certificate_arguments,
    BoundedScalarLinkedSolverTrajectoryTraceCertificate,
    certify_bounded_scalar_linked_solver_trajectory,
    bounded_scalar_linked_solver_trajectory_certificate_arguments,
    BoundedScalarStepRegionalRationalCertificate,
    certify_bounded_scalar_step_regional,
    bounded_scalar_step_regional_certificate_arguments,
    BoundedScalarEndpointEnergyTraceCertificate,
    certify_bounded_scalar_endpoint_energy_trace,
    bounded_scalar_endpoint_energy_certificate_arguments,
    BoundedScalarTwoEndpointEnergyTraceCertificate,
    certify_bounded_scalar_two_endpoint_energy_trace,
    bounded_scalar_two_endpoint_energy_certificate_arguments,
    BoundedScalarTwoEndpointWeightTraceCertificate,
    certify_bounded_scalar_two_endpoint_weights,
    bounded_scalar_two_endpoint_weight_certificate_arguments,
    BoundedScalarTwoEndpointSelectionTraceCertificate,
    certify_bounded_scalar_two_endpoint_selection,
    SeparatedZeroDecisionCertificate, certify_zero_decision,
    SeparatedComparisonCertificate, certify_comparison,
    UTurnDecisionCertificate, certify_uturn_decision,
    VectorUTurnDecisionCertificate, certify_vector_uturn_decision,
    certified_uturn_decision,
    VectorUTurnTrajectoryCertificate, certify_vector_uturn_trajectory,
    certified_uturn_decisions,
    RecursiveDoublingUTurnCertificate,
    certify_recursive_doubling_uturn_matrix,
    GaussianDyadicLeapfrogStepCertificate,
    certify_gaussian_dyadic_leapfrog_step,
    gaussian_dyadic_leapfrog_certificate_arguments,
    GaussianRoundedLeapfrogStepCertificate,
    certify_gaussian_rounded_leapfrog_step,
    gaussian_rounded_leapfrog_certificate_arguments,
    gaussian_rounded_four_leaf_certificate_arguments,
    RoundedLeapfrogRationalCertificate,
    certify_rounded_leapfrog_step,
    rounded_leapfrog_certificate_arguments,
    SinCosRationalIntervalCertificate, certify_sincos_interval,
    sincos_interval_certificate_arguments,
    SqrtRationalIntervalCertificate, certify_sqrt_interval,
    sqrt_interval_certificate_arguments,
    ReciprocalRationalResidualCertificate, certify_reciprocal_residual,
    reciprocal_residual_certificate_arguments,
    sqrt_reciprocal_certificate_arguments,
    BoundedScalarCallbackRationalCertificate,
    certify_bounded_scalar_callbacks,
    bounded_scalar_callback_certificate_arguments,
    BoundedScalarCallbackTraceRationalCertificate,
    certify_bounded_scalar_callback_trace,
    bounded_scalar_callback_trace_certificate_arguments,
    BoundedScalarAffineTraceRationalCertificate,
    certify_bounded_scalar_affine_trace,
    bounded_scalar_affine_update_certificate_arguments,
    LogRationalIntervalCertificate, certify_log_interval,
    log_interval_certificate_arguments,
    ExpNonpositiveRationalIntervalCertificate, certify_exp_nonpositive,
    exp_nonpositive_certificate_arguments,
    ExpNonpositiveTransportRationalCertificate,
    certify_exp_nonpositive_transport,
    exp_nonpositive_transport_certificate_arguments,
    PositiveSoftAbsRationalCertificate, certify_positive_softabs,
    positive_softabs_certificate_arguments,
    PositiveSoftAbsMetricRationalCertificate,
    certify_positive_softabs_metric,
    positive_softabs_metric_certificate_arguments,
    PositiveSoftAbsMetricErrorUpperCertificate,
    certify_positive_softabs_metric_error_upper,
    positive_softabs_metric_error_upper_certificate_arguments,
    PositiveSoftAbsHamiltonianRationalCertificate,
    certify_positive_softabs_hamiltonian,
    positive_softabs_hamiltonian_certificate_arguments,
    PositiveSoftAbsHamiltonianErrorUpperCertificate,
    certify_positive_softabs_hamiltonian_error_upper,
    positive_softabs_hamiltonian_error_upper_certificate_arguments,
    PositiveSoftAbsEndpointStateTransportCertificate,
    certify_positive_softabs_endpoint_state_transport,
    positive_softabs_endpoint_state_transport_certificate_arguments,
    PositiveSoftAbsHamiltonianTrajectoryRationalCertificate,
    certify_positive_softabs_hamiltonian_trajectory,
    positive_softabs_hamiltonian_trajectory_certificate_arguments,
    PositiveSoftAbsStabilizedWeightTrajectoryRationalCertificate,
    certify_positive_softabs_stabilized_weights,
    positive_softabs_stabilized_weight_certificate_arguments,
    RoundedCumulativeRationalCertificate, certify_rounded_cumulative,
    rounded_cumulative_certificate_arguments,
    ScaledDrawRationalCertificate, certify_scaled_draw,
    scaled_draw_certificate_arguments,
    MultinomialDecisionRationalCertificate, certify_multinomial_decision,
    multinomial_decision_certificate_arguments,
    PositiveSoftAbsSelectionErrorUpperCertificate,
    certify_positive_softabs_selection_error_upper,
    NUTSCompletedTreeCertificate, certified_nuts_completed_tree,
    EuclideanLeapfrogErrorParameters, leapfrog_error_schedule,
    LeapfrogCoordinateCertificate, certify_leapfrog_coordinate_step,
    LeapfrogVectorCertificate, certify_leapfrog_vector_step,
    LinkedLeapfrogVectorTrajectoryCertificate,
    certify_linked_leapfrog_vector_trajectory,
    CompletedTreeDecisionCertificate,
    NUTSLeafEnergyCertificate, certify_nuts_leaf_energy,
    certified_nuts_leaf_decisions,
    is_stable, uncertainty_band

include("SoftAbsRational.jl")

"""A checked, execution-specific absolute-error claim.

`ideal` and `bound` are supplied by a trusted oracle or analytic argument.
Construction checks the observed Float64 value against that claim using
BigFloat arithmetic. This object does not establish that the supplied ideal
value is the mathematical real result.
"""
struct BoundWitness
    computed::Float64
    ideal::BigFloat
    bound::BigFloat
    observed_error::BigFloat
end

"""Exact-dyadic record for one Float64 Gaussian leapfrog step.

Construction succeeds only when the observed binary floating-point values,
viewed as exact rationals, satisfy all three Gaussian kick--drift--kick
equations exactly. This deliberately certifies a restricted no-rounding subset
instead of assuming a general IEEE error model.
"""
struct GaussianDyadicLeapfrogStepCertificate
    step_size::Float64
    position::Float64
    momentum::Float64
    half_momentum::Float64
    next_position::Float64
    next_momentum::Float64
end

function certify_gaussian_dyadic_leapfrog_step(
        step_size::Real, position::Real, momentum::Real)
    epsilon, q, p = Float64(step_size), Float64(position), Float64(momentum)
    all(isfinite, (epsilon, q, p)) || throw(ArgumentError(
        "Gaussian dyadic leapfrog inputs must be finite"))
    half = p - epsilon / 2 * q
    next_q = q + epsilon * half
    next_p = half - epsilon / 2 * next_q
    all(isfinite, (half, next_q, next_p)) || throw(OverflowError(
        "Gaussian dyadic leapfrog endpoint is not finite"))
    exact_epsilon = Rational{BigInt}(epsilon)
    exact_q = Rational{BigInt}(q)
    exact_p = Rational{BigInt}(p)
    Rational{BigInt}(half) ==
        exact_p - exact_epsilon / 2 * exact_q || throw(InexactError(
            :certify_gaussian_dyadic_leapfrog_step, Float64, half))
    Rational{BigInt}(next_q) ==
        exact_q + exact_epsilon * Rational{BigInt}(half) || throw(InexactError(
            :certify_gaussian_dyadic_leapfrog_step, Float64, next_q))
    Rational{BigInt}(next_p) ==
        Rational{BigInt}(half) - exact_epsilon / 2 * Rational{BigInt}(next_q) ||
        throw(InexactError(:certify_gaussian_dyadic_leapfrog_step,
            Float64, next_p))
    GaussianDyadicLeapfrogStepCertificate(
        epsilon, q, p, half, next_q, next_p)
end

_exact_rational_wire(value::Real) = begin
    rational = Rational{BigInt}(value)
    string(numerator(rational), "/", denominator(rational))
end

"""Arguments accepted by Lean's `gaussian_dyadic_leapfrog` oracle command."""
gaussian_dyadic_leapfrog_certificate_arguments(
        certificate::GaussianDyadicLeapfrogStepCertificate) = String[
    _exact_rational_wire(certificate.step_size),
    _exact_rational_wire(certificate.position),
    _exact_rational_wire(certificate.momentum),
    _exact_rational_wire(certificate.half_momentum),
    _exact_rational_wire(certificate.next_position),
    _exact_rational_wire(certificate.next_momentum),
]

"""Exact rational residuals of one possibly rounded Float64 Gaussian step."""
struct GaussianRoundedLeapfrogStepCertificate
    step_size::Float64
    position::Float64
    momentum::Float64
    half_momentum::Float64
    next_position::Float64
    next_momentum::Float64
    half_momentum_error::Rational{BigInt}
    next_position_error::Rational{BigInt}
    next_momentum_error::Rational{BigInt}
end

function certify_gaussian_rounded_leapfrog_step(
        step_size::Real, position::Real, momentum::Real)
    epsilon, q, p = Float64(step_size), Float64(position), Float64(momentum)
    all(isfinite, (epsilon, q, p)) || throw(ArgumentError(
        "Gaussian rounded leapfrog inputs must be finite"))
    half = p - epsilon / 2 * q
    next_q = q + epsilon * half
    next_p = half - epsilon / 2 * next_q
    all(isfinite, (half, next_q, next_p)) || throw(OverflowError(
        "Gaussian rounded leapfrog endpoint is not finite"))
    e, x, r = Rational{BigInt}.((epsilon, q, p))
    half_r, next_q_r, next_p_r = Rational{BigInt}.((half, next_q, next_p))
    GaussianRoundedLeapfrogStepCertificate(epsilon, q, p, half, next_q, next_p,
        abs(half_r - (r - e / 2 * x)),
        abs(next_q_r - (x + e * half_r)),
        abs(next_p_r - (half_r - e / 2 * next_q_r)))
end

gaussian_rounded_leapfrog_certificate_arguments(
        certificate::GaussianRoundedLeapfrogStepCertificate) = String[
    _exact_rational_wire(certificate.step_size),
    _exact_rational_wire(certificate.position),
    _exact_rational_wire(certificate.momentum),
    _exact_rational_wire(certificate.half_momentum),
    _exact_rational_wire(certificate.next_position),
    _exact_rational_wire(certificate.next_momentum),
    string(numerator(certificate.half_momentum_error), "/",
        denominator(certificate.half_momentum_error)),
    string(numerator(certificate.next_position_error), "/",
        denominator(certificate.next_position_error)),
    string(numerator(certificate.next_momentum_error), "/",
        denominator(certificate.next_momentum_error)),
]

"""Serialize one linked three-step Gaussian trajectory as four phase leaves."""
function gaussian_rounded_four_leaf_certificate_arguments(
        certificates::AbstractVector{GaussianRoundedLeapfrogStepCertificate})
    length(certificates) == 3 || throw(ArgumentError(
        "a four-leaf trajectory requires exactly three leapfrog steps"))
    for index in 2:3
        certificates[index].position == certificates[index - 1].next_position &&
            certificates[index].momentum == certificates[index - 1].next_momentum ||
            throw(ArgumentError("rounded Gaussian steps are not linked"))
        certificates[index].step_size == certificates[1].step_size ||
            throw(ArgumentError("rounded Gaussian steps use different step sizes"))
    end
    arguments = String[
        _exact_rational_wire(certificates[1].position),
        _exact_rational_wire(certificates[1].momentum),
    ]
    for certificate in certificates
        push!(arguments, _exact_rational_wire(certificate.next_position))
        push!(arguments, _exact_rational_wire(certificate.next_momentum))
    end
    arguments
end

"""Target-independent exact rational residuals for a rounded Float64 step."""
struct RoundedLeapfrogRationalCertificate
    step_size::Float64
    position::Float64
    momentum::Float64
    current_gradient::Float64
    half_momentum::Float64
    next_position::Float64
    next_gradient::Float64
    next_momentum::Float64
    half_momentum_error::Rational{BigInt}
    next_position_error::Rational{BigInt}
    next_momentum_error::Rational{BigInt}
end

function certify_rounded_leapfrog_step(step_size::Real, position::Real,
        momentum::Real, gradient)
    epsilon, q, p = Float64(step_size), Float64(position), Float64(momentum)
    all(isfinite, (epsilon, q, p)) || throw(ArgumentError(
        "rounded leapfrog inputs must be finite"))
    current_gradient = Float64(gradient(q))
    isfinite(current_gradient) || throw(DomainError(current_gradient,
        "rounded leapfrog gradient must be finite"))
    half = p - epsilon / 2 * current_gradient
    next_q = q + epsilon * half
    next_gradient = Float64(gradient(next_q))
    next_p = half - epsilon / 2 * next_gradient
    all(isfinite, (half, next_q, next_gradient, next_p)) || throw(OverflowError(
        "rounded leapfrog endpoint is not finite"))
    e, x, r, g, half_r, next_x, next_g, next_r = Rational{BigInt}.(
        (epsilon, q, p, current_gradient, half, next_q, next_gradient, next_p))
    RoundedLeapfrogRationalCertificate(epsilon, q, p, current_gradient, half,
        next_q, next_gradient, next_p,
        abs(half_r - (r - e / 2 * g)),
        abs(next_x - (x + e * half_r)),
        abs(next_r - (half_r - e / 2 * next_g)))
end

rounded_leapfrog_certificate_arguments(
        certificate::RoundedLeapfrogRationalCertificate) = String[
    _exact_rational_wire(certificate.step_size),
    _exact_rational_wire(certificate.position),
    _exact_rational_wire(certificate.momentum),
    _exact_rational_wire(certificate.current_gradient),
    _exact_rational_wire(certificate.half_momentum),
    _exact_rational_wire(certificate.next_position),
    _exact_rational_wire(certificate.next_gradient),
    _exact_rational_wire(certificate.next_momentum),
    string(numerator(certificate.half_momentum_error), "/",
        denominator(certificate.half_momentum_error)),
    string(numerator(certificate.next_position_error), "/",
        denominator(certificate.next_position_error)),
    string(numerator(certificate.next_momentum_error), "/",
        denominator(certificate.next_momentum_error)),
]

"""Nonnegative constants for the Lean Euclidean leapfrog error recurrence."""
struct EuclideanLeapfrogErrorParameters
    step_magnitude::BigFloat
    gradient_lipschitz::BigFloat
    gradient_error::BigFloat
    kick_rounding::BigFloat
    drift_rounding::BigFloat
end

function EuclideanLeapfrogErrorParameters(step_magnitude::Real,
        gradient_lipschitz::Real, gradient_error::Real,
        kick_rounding::Real, drift_rounding::Real; precision::Integer=256)
    setprecision(BigFloat, precision) do
        values = BigFloat[step_magnitude, gradient_lipschitz, gradient_error,
            kick_rounding, drift_rounding]
        all(isfinite, values) && all(>=(0), values) || throw(ArgumentError(
            "leapfrog error parameters must be finite and nonnegative"))
        EuclideanLeapfrogErrorParameters(values...)
    end
end

"""Evaluate the proved kick-drift-kick error recurrence for every endpoint."""
function leapfrog_error_schedule(parameters::EuclideanLeapfrogErrorParameters,
        steps::Integer; initial_position_error::Real=0,
        initial_momentum_error::Real=0)
    steps >= 0 || throw(ArgumentError("step count must be nonnegative"))
    ep, em = BigFloat(initial_position_error), BigFloat(initial_momentum_error)
    ep >= 0 && em >= 0 || throw(ArgumentError(
        "initial leapfrog errors must be nonnegative"))
    schedule = Vector{NamedTuple{(:position, :momentum),Tuple{BigFloat,BigFloat}}}(
        undef, steps + 1)
    schedule[1] = (; position=ep, momentum=em)
    half_step = parameters.step_magnitude / 2
    for index in 1:steps
        half = em + half_step *
            (parameters.gradient_lipschitz * ep + parameters.gradient_error) +
            parameters.kick_rounding
        next_position = ep + parameters.step_magnitude * half +
            parameters.drift_rounding
        next_momentum = half + half_step *
            (parameters.gradient_lipschitz * next_position +
                parameters.gradient_error) + parameters.kick_rounding
        ep, em = next_position, next_momentum
        schedule[index + 1] = (; position=ep, momentum=em)
    end
    schedule
end

"""Checked primitive witnesses for one scalar kick-drift-kick coordinate."""
struct LeapfrogCoordinateCertificate
    signed_step::Float64
    position::BoundWitness
    momentum::BoundWitness
    current_gradient::BoundWitness
    half_kick_rounding::BoundWitness
    next_gradient::BoundWitness
    drift_rounding::BoundWitness
    final_kick_rounding::BoundWitness
    next_position_error::BigFloat
    next_momentum_error::BigFloat
end

"""Check the primitive premises consumed by Lean's coordinate-step theorem.

Ideal inputs/gradients and local budgets remain analytic premises. BigFloat is
used to evaluate exact-real affine expressions on the supplied Float64 values.
"""
function certify_leapfrog_coordinate_step(parameters::EuclideanLeapfrogErrorParameters;
        signed_step::Real,
        computed_position::Real, ideal_position::Real,
        computed_momentum::Real, ideal_momentum::Real,
        computed_current_gradient::Real, ideal_current_gradient::Real,
        computed_half_momentum::Real, computed_next_position::Real,
        computed_next_gradient::Real, ideal_next_gradient::Real,
        computed_next_momentum::Real,
        position_error::Real, momentum_error::Real,
        precision::Integer=256)
    step = Float64(signed_step)
    abs(BigFloat(step)) <= parameters.step_magnitude || throw(ArgumentError(
        "signed step exceeds the declared step magnitude"))
    position = certify_bound(computed_position, ideal_position, position_error;
        precision=precision)
    momentum = certify_bound(computed_momentum, ideal_momentum, momentum_error;
        precision=precision)
    gradient_budget = parameters.gradient_lipschitz * BigFloat(position_error) +
        parameters.gradient_error
    current_gradient = certify_bound(computed_current_gradient,
        ideal_current_gradient, gradient_budget; precision=precision)
    half_ideal = BigFloat(computed_momentum) + BigFloat(step) / 2 *
        BigFloat(computed_current_gradient)
    half = certify_bound(computed_half_momentum, half_ideal,
        parameters.kick_rounding; precision=precision)
    half_error = BigFloat(momentum_error) + parameters.step_magnitude / 2 *
        gradient_budget + parameters.kick_rounding
    next_position_error = BigFloat(position_error) +
        parameters.step_magnitude * half_error + parameters.drift_rounding
    drift_ideal = BigFloat(computed_position) + BigFloat(step) *
        BigFloat(computed_half_momentum)
    drift = certify_bound(computed_next_position, drift_ideal,
        parameters.drift_rounding; precision=precision)
    next_gradient_budget = parameters.gradient_lipschitz * next_position_error +
        parameters.gradient_error
    next_gradient = certify_bound(computed_next_gradient, ideal_next_gradient,
        next_gradient_budget; precision=precision)
    final_ideal = BigFloat(computed_half_momentum) + BigFloat(step) / 2 *
        BigFloat(computed_next_gradient)
    final = certify_bound(computed_next_momentum, final_ideal,
        parameters.kick_rounding; precision=precision)
    next_momentum_error = half_error + parameters.step_magnitude / 2 *
        next_gradient_budget + parameters.kick_rounding
    LeapfrogCoordinateCertificate(step, position, momentum, current_gradient, half,
        next_gradient, drift, final, next_position_error, next_momentum_error)
end

"""Dimension-generic collection of coordinate-step primitive witnesses."""
struct LeapfrogVectorCertificate
    coordinates::Vector{LeapfrogCoordinateCertificate}
    next_position_error::BigFloat
    next_momentum_error::BigFloat
end

function certify_leapfrog_vector_step(parameters::EuclideanLeapfrogErrorParameters;
        signed_step::Real,
        computed_position::AbstractVector{<:Real},
        ideal_position::AbstractVector{<:Real},
        computed_momentum::AbstractVector{<:Real},
        ideal_momentum::AbstractVector{<:Real},
        computed_current_gradient::AbstractVector{<:Real},
        ideal_current_gradient::AbstractVector{<:Real},
        computed_half_momentum::AbstractVector{<:Real},
        computed_next_position::AbstractVector{<:Real},
        computed_next_gradient::AbstractVector{<:Real},
        ideal_next_gradient::AbstractVector{<:Real},
        computed_next_momentum::AbstractVector{<:Real},
        position_error::Real, momentum_error::Real,
        precision::Integer=256)
    dimension = length(computed_position)
    dimension > 0 || throw(ArgumentError("leapfrog dimension must be positive"))
    all(length(values) == dimension for values in (ideal_position,
        computed_momentum, ideal_momentum, computed_current_gradient,
        ideal_current_gradient, computed_half_momentum, computed_next_position,
        computed_next_gradient, ideal_next_gradient, computed_next_momentum)) ||
        throw(DimensionMismatch("leapfrog coordinate vectors must match"))
    coordinates = [certify_leapfrog_coordinate_step(parameters;
        signed_step=signed_step,
        computed_position=computed_position[i], ideal_position=ideal_position[i],
        computed_momentum=computed_momentum[i], ideal_momentum=ideal_momentum[i],
        computed_current_gradient=computed_current_gradient[i],
        ideal_current_gradient=ideal_current_gradient[i],
        computed_half_momentum=computed_half_momentum[i],
        computed_next_position=computed_next_position[i],
        computed_next_gradient=computed_next_gradient[i],
        ideal_next_gradient=ideal_next_gradient[i],
        computed_next_momentum=computed_next_momentum[i],
        position_error=position_error, momentum_error=momentum_error,
        precision=precision) for i in 1:dimension]
    LeapfrogVectorCertificate(coordinates,
        first(coordinates).next_position_error,
        first(coordinates).next_momentum_error)
end

_ideal_half_momentum(certificate::LeapfrogCoordinateCertificate) =
    certificate.momentum.ideal + BigFloat(certificate.signed_step) / 2 *
        certificate.current_gradient.ideal
_ideal_next_position(certificate::LeapfrogCoordinateCertificate) =
    certificate.position.ideal + BigFloat(certificate.signed_step) *
        _ideal_half_momentum(certificate)
_ideal_next_momentum(certificate::LeapfrogCoordinateCertificate) =
    _ideal_half_momentum(certificate) + BigFloat(certificate.signed_step) / 2 *
        certificate.next_gradient.ideal

"""A checked sequence of primitive vector certificates forming one trajectory.

Each step must consume exactly the computed and ideal endpoint produced by its
predecessor. This is an exact state-threading check, distinct from the error
bounds already checked inside each step certificate.
"""
struct LinkedLeapfrogVectorTrajectoryCertificate
    initial_computed_position::Vector{Float64}
    initial_ideal_position::Vector{BigFloat}
    initial_computed_momentum::Vector{Float64}
    initial_ideal_momentum::Vector{BigFloat}
    steps::Vector{LeapfrogVectorCertificate}
end

function certify_linked_leapfrog_vector_trajectory(
        initial_computed_position::AbstractVector{<:Real},
        initial_ideal_position::AbstractVector{<:Real},
        initial_computed_momentum::AbstractVector{<:Real},
        initial_ideal_momentum::AbstractVector{<:Real},
        steps::AbstractVector{LeapfrogVectorCertificate})
    dimension = length(initial_computed_position)
    dimension > 0 || throw(ArgumentError("leapfrog dimension must be positive"))
    all(length(values) == dimension for values in (initial_ideal_position,
        initial_computed_momentum, initial_ideal_momentum)) ||
        throw(DimensionMismatch("initial leapfrog vectors must match"))

    computed_position = Float64.(initial_computed_position)
    ideal_position = BigFloat.(initial_ideal_position)
    computed_momentum = Float64.(initial_computed_momentum)
    ideal_momentum = BigFloat.(initial_ideal_momentum)
    checked_steps = collect(steps)
    for (index, step) in enumerate(checked_steps)
        length(step.coordinates) == dimension || throw(DimensionMismatch(
            "leapfrog step $index has the wrong dimension"))
        step_computed_position = [coordinate.position.computed
            for coordinate in step.coordinates]
        step_ideal_position = [coordinate.position.ideal
            for coordinate in step.coordinates]
        step_computed_momentum = [coordinate.momentum.computed
            for coordinate in step.coordinates]
        step_ideal_momentum = [coordinate.momentum.ideal
            for coordinate in step.coordinates]
        step_computed_position == computed_position || throw(ArgumentError(
            "leapfrog step $index does not consume the preceding computed position"))
        step_ideal_position == ideal_position || throw(ArgumentError(
            "leapfrog step $index does not consume the preceding ideal position"))
        step_computed_momentum == computed_momentum || throw(ArgumentError(
            "leapfrog step $index does not consume the preceding computed momentum"))
        step_ideal_momentum == ideal_momentum || throw(ArgumentError(
            "leapfrog step $index does not consume the preceding ideal momentum"))
        computed_position = [coordinate.drift_rounding.computed
            for coordinate in step.coordinates]
        ideal_position = [_ideal_next_position(coordinate)
            for coordinate in step.coordinates]
        computed_momentum = [coordinate.final_kick_rounding.computed
            for coordinate in step.coordinates]
        ideal_momentum = [_ideal_next_momentum(coordinate)
            for coordinate in step.coordinates]
    end
    LinkedLeapfrogVectorTrajectoryCertificate(Float64.(initial_computed_position),
        BigFloat.(initial_ideal_position), Float64.(initial_computed_momentum),
        BigFloat.(initial_ideal_momentum), checked_steps)
end

include("DynamicTree.jl")
include("PracticalSlice.jl")
include("ImplicitSolver.jl")

"""Execution-specific cumulative-boundary certificate for multinomial selection."""
struct MultinomialSelectionCertificate
    boundaries::Vector{BoundWitness}
    uniform::BoundWitness
    minimum_margin::BigFloat
    uncertainty::BigFloat
end

is_stable(certificate::MultinomialSelectionCertificate) =
    certificate.uncertainty < certificate.minimum_margin
uncertainty_band(certificate::MultinomialSelectionCertificate) =
    certificate.uncertainty

"""Check cumulative-weight bounds and the distance to every selection boundary.

Conditional on the supplied ideal values and common boundary bound, stability
implies the Float64 and ideal categorical scans select the same index.
"""
function certify_multinomial_selection(computed_boundaries::AbstractVector{<:Real},
        ideal_boundaries::AbstractVector{<:Real}, boundary_bound::Real,
        computed_uniform::Real, ideal_uniform::Real, uniform_bound::Real;
        precision::Integer=256)
    length(computed_boundaries) == length(ideal_boundaries) ||
        throw(DimensionMismatch("boundary vectors must have equal length"))
    isempty(computed_boundaries) && throw(ArgumentError("boundaries cannot be empty"))
    boundaries = [certify_bound(computed_boundaries[i], ideal_boundaries[i],
        boundary_bound; precision=precision) for i in eachindex(computed_boundaries)]
    uniform = certify_bound(computed_uniform, ideal_uniform, uniform_bound;
        precision=precision)
    minimum_margin = minimum(abs(uniform.ideal - boundary.ideal)
        for boundary in boundaries)
    MultinomialSelectionCertificate(boundaries, uniform, minimum_margin,
        uniform.bound + BigFloat(boundary_bound))
end

function certify_bound(computed::Real, ideal::Real, bound::Real;
        precision::Integer=256)
    precision >= 64 || throw(ArgumentError("precision must be at least 64 bits"))
    converted = Float64(computed)
    isfinite(converted) || throw(ArgumentError("computed value must be finite"))
    setprecision(BigFloat, precision) do
        reference = BigFloat(ideal)
        budget = BigFloat(bound)
        isfinite(reference) || throw(ArgumentError("ideal value must be finite"))
        isfinite(budget) && budget >= 0 ||
            throw(ArgumentError("error bound must be finite and nonnegative"))
        observed = abs(BigFloat(converted) - reference)
        observed <= budget || throw(ArgumentError(
            "observed error $observed exceeds supplied bound $budget"))
        BoundWitness(converted, reference, budget, observed)
    end
end

"""Checked decision-margin certificate matching Lean's stability condition."""
struct DecisionCertificate
    uniform::BoundWitness
    threshold::BoundWitness
    ideal_margin::BigFloat
end

uncertainty_band(certificate::DecisionCertificate) =
    certificate.uniform.bound + certificate.threshold.bound

is_stable(certificate::DecisionCertificate) =
    uncertainty_band(certificate) < certificate.ideal_margin

"""Check uniform and threshold bounds and compute the certified branch margin.

When `is_stable(result)` holds, Lean's `comparison_eq_of_approximates` theorem
shows that the Float64 and ideal comparisons select the same branch, provided
the supplied per-operation bounds are valid.
"""
function certify_decision(computed_uniform::Real, ideal_uniform::Real,
        uniform_bound::Real, computed_threshold::Real, ideal_threshold::Real,
        threshold_bound::Real; precision::Integer=256)
    uniform = certify_bound(computed_uniform, ideal_uniform, uniform_bound;
        precision=precision)
    threshold = certify_bound(computed_threshold, ideal_threshold,
        threshold_bound; precision=precision)
    margin = setprecision(BigFloat, precision) do
        abs(BigFloat(ideal_uniform) - BigFloat(ideal_threshold))
    end
    DecisionCertificate(uniform, threshold, margin)
end

"""A sampler decision certificate plus its checked component witnesses."""
struct SamplerDecisionCertificate{C}
    algorithm::Symbol
    components::C
    decision::DecisionCertificate
end

is_stable(certificate::SamplerDecisionCertificate) = is_stable(certificate.decision)
uncertainty_band(certificate::SamplerDecisionCertificate) =
    uncertainty_band(certificate.decision)

"""Compose callback, libm, and RNG bounds for one RWMH decision.

The threshold budget is `exp_bound + proposed_logdensity_bound +
current_logdensity_bound`, exactly as in Lean's
`BackendRwmhCertificate.toErrorCertificate`.
"""
function certify_rwmh_decision(;
        computed_current_logdensity::Real, ideal_current_logdensity::Real,
        current_logdensity_bound::Real,
        computed_proposal_logdensity::Real, ideal_proposal_logdensity::Real,
        proposal_logdensity_bound::Real,
        computed_threshold::Real, ideal_threshold::Real, exp_bound::Real,
        computed_uniform::Real, ideal_uniform::Real, uniform_bound::Real,
        precision::Integer=256)
    current_logdensity = certify_bound(computed_current_logdensity,
        ideal_current_logdensity, current_logdensity_bound; precision=precision)
    proposal_logdensity = certify_bound(computed_proposal_logdensity,
        ideal_proposal_logdensity, proposal_logdensity_bound; precision=precision)
    exp_budget = BigFloat(exp_bound)
    isfinite(exp_budget) && exp_budget >= 0 ||
        throw(ArgumentError("exp bound must be finite and nonnegative"))
    threshold_budget = exp_budget + current_logdensity.bound +
        proposal_logdensity.bound
    decision = certify_decision(computed_uniform, ideal_uniform, uniform_bound,
        computed_threshold, ideal_threshold, threshold_budget; precision=precision)
    SamplerDecisionCertificate(:rwmh,
        (; current_logdensity, proposal_logdensity, exp_bound=exp_budget),
        decision)
end

"""Compose endpoint-energy, libm, and RNG bounds for one HMC decision.

The threshold budget is `exp_bound + current_energy_bound +
proposal_energy_bound`, matching Lean's
`BackendHmcCertificate.toErrorCertificate`.
"""
function certify_hmc_decision(;
        computed_current_energy::Real, ideal_current_energy::Real,
        current_energy_bound::Real,
        computed_proposal_energy::Real, ideal_proposal_energy::Real,
        proposal_energy_bound::Real,
        computed_threshold::Real, ideal_threshold::Real, exp_bound::Real,
        computed_uniform::Real, ideal_uniform::Real, uniform_bound::Real,
        precision::Integer=256)
    current_energy = certify_bound(computed_current_energy,
        ideal_current_energy, current_energy_bound; precision=precision)
    proposal_energy = certify_bound(computed_proposal_energy,
        ideal_proposal_energy, proposal_energy_bound; precision=precision)
    exp_budget = BigFloat(exp_bound)
    isfinite(exp_budget) && exp_budget >= 0 ||
        throw(ArgumentError("exp bound must be finite and nonnegative"))
    threshold_budget = exp_budget + current_energy.bound +
        proposal_energy.bound
    decision = certify_decision(computed_uniform, ideal_uniform, uniform_bound,
        computed_threshold, ideal_threshold, threshold_budget; precision=precision)
    SamplerDecisionCertificate(:hmc,
        (; current_energy, proposal_energy, exp_bound=exp_budget), decision)
end

end
