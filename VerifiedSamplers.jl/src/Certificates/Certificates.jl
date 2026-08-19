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

"""Assumption-free rational sine/cosine enclosure for an input in `[-1,1]`."""
struct SinCosRationalIntervalCertificate
    input::Float64
    computed_sin::Float64
    sin_error::Rational{BigInt}
    computed_cos::Float64
    cos_error::Rational{BigInt}
end


function certify_sincos_interval(input::Real)
    x = Float64(input)
    isfinite(x) && abs(x) <= 1 || throw(DomainError(input,
        "sine/cosine rational enclosure requires an input in [-1,1]"))
    computed_sin, computed_cos = sin(x), cos(x)
    exact_x = Rational{BigInt}(x)
    exact_sin = Rational{BigInt}(computed_sin)
    exact_cos = Rational{BigInt}(computed_cos)
    sin_center = exact_x - exact_x^3 / 6
    sin_remainder = abs(exact_x)^5 / 100
    cos_center = 1 - exact_x^2 / 2
    cos_remainder = abs(exact_x)^4 * (5 // big(96))
    SinCosRationalIntervalCertificate(x, computed_sin,
        abs(exact_sin - sin_center) + sin_remainder, computed_cos,
        abs(exact_cos - cos_center) + cos_remainder)
end


sincos_interval_certificate_arguments(
        certificate::SinCosRationalIntervalCertificate) = String[
    _exact_rational_wire(certificate.input),
    _exact_rational_wire(certificate.computed_sin),
    _exact_rational_wire(certificate.sin_error),
    _exact_rational_wire(certificate.computed_cos),
    _exact_rational_wire(certificate.cos_error),
]

"""Exact rational enclosure of a Float64 square-root execution.

The radius is computed from exact rational representations of the input and
output. Lean independently checks that the squared interval endpoints enclose
the input, which proves proximity to the mathematical real square root without
assuming a platform `sqrt` error model.
"""
struct SqrtRationalIntervalCertificate
    input::Float64
    computed::Float64
    error::Rational{BigInt}
end

function certify_sqrt_interval(input::Real)
    x = Float64(input)
    isfinite(x) && x >= 0 || throw(DomainError(input,
        "square-root input must be finite and nonnegative"))
    computed = sqrt(x)
    isfinite(computed) || throw(DomainError(computed,
        "square-root output must be finite"))
    exact_x = Rational{BigInt}(x)
    exact_computed = Rational{BigInt}(computed)
    error = iszero(exact_computed) ? zero(exact_computed) :
        abs(exact_computed^2 - exact_x) / exact_computed
    SqrtRationalIntervalCertificate(x, computed, error)
end

sqrt_interval_certificate_arguments(
        certificate::SqrtRationalIntervalCertificate) = String[
    _exact_rational_wire(certificate.input),
    _exact_rational_wire(certificate.computed),
    string(numerator(certificate.error), "/", denominator(certificate.error)),
]

"""Exact rational residual of one finite, nonzero reciprocal execution."""
struct ReciprocalRationalResidualCertificate
    input::Float64
    computed::Float64
    error::Rational{BigInt}
end

function certify_reciprocal_residual(input::Real)
    x = Float64(input)
    isfinite(x) && !iszero(x) || throw(DomainError(input,
        "reciprocal input must be finite and nonzero"))
    computed = inv(x)
    isfinite(computed) || throw(DomainError(computed,
        "reciprocal output must be finite"))
    exact_x = Rational{BigInt}(x)
    exact_computed = Rational{BigInt}(computed)
    error = abs(exact_computed - inv(exact_x))
    ReciprocalRationalResidualCertificate(x, computed, error)
end


reciprocal_residual_certificate_arguments(
        certificate::ReciprocalRationalResidualCertificate) = String[
    _exact_rational_wire(certificate.input),
    _exact_rational_wire(certificate.computed),
    string(numerator(certificate.error), "/", denominator(certificate.error)),
]

function sqrt_reciprocal_certificate_arguments(
        sqrt_certificate::SqrtRationalIntervalCertificate,
        reciprocal_certificate::ReciprocalRationalResidualCertificate)
    reciprocal_certificate.input == sqrt_certificate.computed ||
        throw(ArgumentError("reciprocal input must equal the computed square root"))
    String[
        _exact_rational_wire(sqrt_certificate.input),
        _exact_rational_wire(sqrt_certificate.computed),
        string(numerator(sqrt_certificate.error), "/",
            denominator(sqrt_certificate.error)),
        _exact_rational_wire(reciprocal_certificate.computed),
        string(numerator(reciprocal_certificate.error), "/",
            denominator(reciprocal_certificate.error)),
    ]
end

"""Checked primitive and final-arithmetic record for both callbacks of the
bounded nonconstant `2 + sin(q)` generalized-leapfrog client."""
struct BoundedScalarCallbackRationalCertificate
    sincos::SinCosRationalIntervalCertificate
    momentum::Float64
    computed_radicand::Float64
    radicand_arithmetic_error::Rational{BigInt}
    sqrt_certificate::SqrtRationalIntervalCertificate
    reciprocal_certificate::ReciprocalRationalResidualCertificate
    computed_sqrt_lower::Rational{BigInt}
    computed_momentum_callback::Float64
    momentum_arithmetic_error::Rational{BigInt}
    computed_position_callback::Float64
    position_arithmetic_error::Rational{BigInt}
end

function certify_bounded_scalar_callbacks(position::Real, momentum::Real;
        computed_momentum_callback=nothing, computed_position_callback=nothing)
    q = Float64(position)
    p = Float64(momentum)
    isfinite(p) || throw(DomainError(momentum, "momentum must be finite"))
    sincos = certify_sincos_interval(q)
    scale = 2.0 + sincos.computed_sin
    transformed = scale * p
    computed_radicand = 1.0 + transformed^2
    isfinite(computed_radicand) || throw(DomainError(computed_radicand,
        "bounded scalar radicand must be finite"))
    exact_scale = 2 + Rational{BigInt}(sincos.computed_sin)
    exact_p = Rational{BigInt}(p)
    exact_transformed = exact_scale * exact_p
    exact_radicand = Rational{BigInt}(computed_radicand)
    radicand_arithmetic_error = abs(exact_radicand -
        (1 + exact_transformed^2))
    sqrt_certificate = certify_sqrt_interval(computed_radicand)
    reciprocal_certificate = certify_reciprocal_residual(
        sqrt_certificate.computed)
    computed_sqrt_lower = Rational{BigInt}(sqrt_certificate.computed) -
        sqrt_certificate.error
    computed_sqrt_lower > 0 || throw(DomainError(computed_sqrt_lower,
        "certified square-root lower endpoint must be positive"))

    computed_momentum_callback = computed_momentum_callback === nothing ?
        scale * transformed * reciprocal_certificate.computed :
        Float64(computed_momentum_callback)
    isfinite(computed_momentum_callback) ||
        throw(DomainError(computed_momentum_callback,
            "momentum callback must be finite"))
    exact_inverse = Rational{BigInt}(reciprocal_certificate.computed)
    momentum_arithmetic_error = abs(
        Rational{BigInt}(computed_momentum_callback) -
          exact_scale * exact_transformed * exact_inverse)

    computed_position_callback = computed_position_callback === nothing ?
        scale * sincos.computed_cos * p^2 * reciprocal_certificate.computed :
        Float64(computed_position_callback)
    isfinite(computed_position_callback) ||
        throw(DomainError(computed_position_callback,
            "position callback must be finite"))
    position_arithmetic_error = abs(
        Rational{BigInt}(computed_position_callback) -
          exact_scale * Rational{BigInt}(sincos.computed_cos) * exact_p^2 *
            exact_inverse)

    BoundedScalarCallbackRationalCertificate(sincos, p,
        computed_radicand, radicand_arithmetic_error, sqrt_certificate,
        reciprocal_certificate, computed_sqrt_lower,
        computed_momentum_callback, momentum_arithmetic_error,
        computed_position_callback, position_arithmetic_error)
end

function bounded_scalar_callback_certificate_arguments(
        certificate::BoundedScalarCallbackRationalCertificate)
    vcat(sincos_interval_certificate_arguments(certificate.sincos), String[
        _exact_rational_wire(certificate.momentum),
        _exact_rational_wire(certificate.computed_radicand),
        _exact_rational_wire(certificate.radicand_arithmetic_error),
        _exact_rational_wire(certificate.sqrt_certificate.input),
        _exact_rational_wire(certificate.sqrt_certificate.computed),
        _exact_rational_wire(certificate.sqrt_certificate.error),
        _exact_rational_wire(certificate.reciprocal_certificate.input),
        _exact_rational_wire(certificate.reciprocal_certificate.computed),
        _exact_rational_wire(certificate.reciprocal_certificate.error),
        _exact_rational_wire(certificate.computed_sqrt_lower),
        _exact_rational_wire(certificate.computed_momentum_callback),
        _exact_rational_wire(certificate.momentum_arithmetic_error),
        _exact_rational_wire(certificate.computed_position_callback),
        _exact_rational_wire(certificate.position_arithmetic_error),
    ])
end

"""A complete ordered certificate list for every callback in one scalar
reference fixed-point trace."""
struct BoundedScalarCallbackTraceRationalCertificate
    half_iterations::Int
    position_iterations::Int
    kinds::Vector{Symbol}
    certificates::Vector{BoundedScalarCallbackRationalCertificate}
end

function certify_bounded_scalar_callback_trace(trace)
    kinds = Symbol[]
    certificates = BoundedScalarCallbackRationalCertificate[]
    for evaluation in trace.callback_evaluations
        length(evaluation.position) == 1 && length(evaluation.momentum) == 1 &&
            length(evaluation.value) == 1 || throw(DimensionMismatch(
                "bounded scalar trace evaluations must be one-dimensional"))
        evaluation.kind in (:position, :momentum) || throw(ArgumentError(
            "unknown fixed-point callback kind: $(evaluation.kind)"))
        q, p, observed = evaluation.position[1], evaluation.momentum[1],
            evaluation.value[1]
        certificate = evaluation.kind === :position ?
            certify_bounded_scalar_callbacks(q, p;
                computed_position_callback=observed) :
            certify_bounded_scalar_callbacks(q, p;
                computed_momentum_callback=observed)
        push!(kinds, evaluation.kind)
        push!(certificates, certificate)
    end
    BoundedScalarCallbackTraceRationalCertificate(trace.half_iterations,
        trace.position_iterations, kinds, certificates)
end

function bounded_scalar_callback_trace_certificate_arguments(
        trace::BoundedScalarCallbackTraceRationalCertificate)
    length(trace.kinds) == length(trace.certificates) ||
        throw(ArgumentError("callback trace kind/certificate length mismatch"))
    arguments = String[string(length(trace.kinds)),
        string(trace.half_iterations), string(trace.position_iterations)]
    for (kind, certificate) in zip(trace.kinds, trace.certificates)
        push!(arguments, kind === :position ? "position" :
            kind === :momentum ? "momentum" :
            throw(ArgumentError("unknown callback kind: $kind")))
        append!(arguments,
            bounded_scalar_callback_certificate_arguments(certificate))
    end
    arguments
end

"""Rational analytic enclosure of one positive Float64 logarithm call.

The radius uses 32 terms of the globally convergent expansion with
`z=(x-1)/(x+1)` and a checked geometric remainder. Lean verifies the same
rational expression, so this does not assume a platform libm bound.
"""
struct LogRationalIntervalCertificate
    input::Float64
    computed::Float64
    error::Rational{BigInt}
end

function certify_log_interval(input::Real)
    x = Float64(input)
    isfinite(x) && x > 0 || throw(DomainError(input,
        "logarithm input must be finite and positive"))
    computed = log(x)
    isfinite(computed) || throw(DomainError(computed,
        "logarithm output must be finite"))
    exact_x = Rational{BigInt}(x)
    exact_computed = Rational{BigInt}(computed)
    z = (exact_x - 1) / (exact_x + 1)
    terms = 32
    center = 2 * sum(z^(2 * i + 1) / (2 * i + 1) for i in 0:terms-1)
    remainder = 2 * abs(z)^(2 * terms + 1) / (1 - z^2)
    error = abs(exact_computed - center) + remainder
    LogRationalIntervalCertificate(x, computed, error)
end

log_interval_certificate_arguments(
        certificate::LogRationalIntervalCertificate) = String[
    _exact_rational_wire(certificate.input),
    _exact_rational_wire(certificate.computed),
    string(numerator(certificate.error), "/", denominator(certificate.error)),
]

"""Assumption-free rational enclosure of `exp(x)` for an observed `x ≤ 0`."""
struct ExpNonpositiveRationalIntervalCertificate
    input::Float64
    computed::Float64
    error::Rational{BigInt}
end

function certify_exp_nonpositive(input::Real)
    x = Float64(input)
    isfinite(x) && x <= 0 || throw(DomainError(input,
        "exponential certificate input must be finite and nonpositive"))
    computed = exp(x)
    isfinite(computed) || throw(DomainError(computed,
        "exponential result must be finite"))
    exact_x = Rational{BigInt}(x)
    exact_computed = Rational{BigInt}(computed)
    lower = max(zero(exact_x), one(exact_x) + exact_x)
    upper = one(exact_x) / (one(exact_x) - exact_x)
    error = max(zero(exact_x), exact_computed - lower,
        upper - exact_computed)
    ExpNonpositiveRationalIntervalCertificate(x, computed, error)
end

exp_nonpositive_certificate_arguments(
        certificate::ExpNonpositiveRationalIntervalCertificate) = String[
    _exact_rational_wire(certificate.input),
    _exact_rational_wire(certificate.computed),
    string(numerator(certificate.error), "/", denominator(certificate.error)),
]

"""Transport a checked nonpositive exponential to an exact rational input."""
struct ExpNonpositiveTransportRationalCertificate
    local_certificate::ExpNonpositiveRationalIntervalCertificate
    ideal_input::Rational{BigInt}
    input_error::Rational{BigInt}
end

function certify_exp_nonpositive_transport(computed_input::Real,
        ideal_input::Rational)
    ideal = Rational{BigInt}(ideal_input)
    ideal <= 0 || throw(DomainError(ideal_input,
        "ideal exponential input must be nonpositive"))
    local_certificate = certify_exp_nonpositive(computed_input)
    input_error = abs(Rational{BigInt}(local_certificate.input) - ideal)
    ExpNonpositiveTransportRationalCertificate(
        local_certificate, ideal, input_error)
end


function exp_nonpositive_transport_certificate_arguments(
        certificate::ExpNonpositiveTransportRationalCertificate)
    vcat(exp_nonpositive_certificate_arguments(certificate.local_certificate),
        String[
            string(numerator(certificate.ideal_input), "/",
                denominator(certificate.ideal_input)),
            string(numerator(certificate.input_error), "/",
                denominator(certificate.input_error)),
        ])
end

"""Exact-rational certificate for one positive-branch SoftAbs evaluation."""
struct PositiveSoftAbsRationalCertificate
    smoothing::Float64
    hessian::Float64
    computed_argument::Float64
    argument_error::Rational{BigInt}
    computed_tanh::Float64
    tanh_error::Rational{BigInt}
    computed_eigenvalue::Float64
    division_error::Rational{BigInt}
end

function certify_positive_softabs(smoothing::Real, hessian::Real)
    α, h = Float64(smoothing), Float64(hessian)
    all(isfinite, (α, h)) && α > 0 && h > 0 || throw(DomainError(
        (smoothing, hessian), "SoftAbs smoothing and Hessian must be finite and positive"))
    exact_α, exact_h = Rational{BigInt}.((α, h))
    computed_argument = α * h
    exact_argument = exact_α * exact_h
    exact_computed_argument = Rational{BigInt}(computed_argument)
    argument_error = abs(exact_computed_argument - exact_argument)
    computed_tanh = tanh(computed_argument)
    isfinite(computed_tanh) && computed_tanh > 0 || throw(DomainError(
        computed_tanh, "positive SoftAbs tanh must be finite and positive"))
    exact_tanh = Rational{BigInt}(computed_tanh)
    lower = exact_computed_argument / (1 + exact_computed_argument)
    upper = min(exact_computed_argument, one(exact_computed_argument))
    tanh_error = max(zero(exact_computed_argument), exact_tanh - lower,
        upper - exact_tanh)
    exact_tanh - tanh_error > 0 || throw(ArgumentError(
        "analytic tanh enclosure does not retain a positive denominator"))
    computed_eigenvalue = h / computed_tanh
    isfinite(computed_eigenvalue) && computed_eigenvalue > 0 ||
        throw(DomainError(computed_eigenvalue,
            "positive SoftAbs eigenvalue must be finite and positive"))
    division_error = abs(Rational{BigInt}(computed_eigenvalue) -
        exact_h / exact_tanh)
    PositiveSoftAbsRationalCertificate(α, h, computed_argument, argument_error,
        computed_tanh, tanh_error, computed_eigenvalue, division_error)
end

positive_softabs_certificate_arguments(
        certificate::PositiveSoftAbsRationalCertificate) = String[
    _exact_rational_wire(certificate.smoothing),
    _exact_rational_wire(certificate.hessian),
    _exact_rational_wire(certificate.computed_argument),
    string(numerator(certificate.argument_error), "/",
        denominator(certificate.argument_error)),
    _exact_rational_wire(certificate.computed_tanh),
    string(numerator(certificate.tanh_error), "/",
        denominator(certificate.tanh_error)),
    _exact_rational_wire(certificate.computed_eigenvalue),
    string(numerator(certificate.division_error), "/",
        denominator(certificate.division_error)),
]

"""Linked certificates for a complete positive-branch SoftAbs metric entry."""
struct PositiveSoftAbsMetricRationalCertificate
    eigenvalue::PositiveSoftAbsRationalCertificate
    sqrt::SqrtRationalIntervalCertificate
    factor::ReciprocalRationalResidualCertificate
    logdet::LogRationalIntervalCertificate
end

function certify_positive_softabs_metric(smoothing::Real, hessian::Real)
    eigenvalue = certify_positive_softabs(smoothing, hessian)
    sqrt_certificate = certify_sqrt_interval(eigenvalue.computed_eigenvalue)
    factor = certify_reciprocal_residual(sqrt_certificate.computed)
    logdet = certify_log_interval(eigenvalue.computed_eigenvalue)
    PositiveSoftAbsMetricRationalCertificate(
        eigenvalue, sqrt_certificate, factor, logdet)
end

function positive_softabs_metric_certificate_arguments(
        certificate::PositiveSoftAbsMetricRationalCertificate)
    vcat(positive_softabs_certificate_arguments(certificate.eigenvalue), String[
        _exact_rational_wire(certificate.sqrt.computed),
        string(numerator(certificate.sqrt.error), "/",
            denominator(certificate.sqrt.error)),
        _exact_rational_wire(certificate.factor.computed),
        string(numerator(certificate.factor.error), "/",
            denominator(certificate.factor.error)),
        _exact_rational_wire(certificate.logdet.computed),
        string(numerator(certificate.logdet.error), "/",
            denominator(certificate.logdet.error)),
    ])
end

"""Checked rational denominator bounds for transported SoftAbs metric errors."""
struct PositiveSoftAbsMetricErrorUpperCertificate
    metric::PositiveSoftAbsMetricRationalCertificate
    ideal_tanh_lower::Rational{BigInt}
    computed_sqrt_lower::Rational{BigInt}
    ideal_sqrt_lower::Rational{BigInt}
    eigenvalue_error::Rational{BigInt}
    sqrt_error::Rational{BigInt}
    factor_error::Rational{BigInt}
    logdet_error::Rational{BigInt}
end

function certify_positive_softabs_metric_error_upper(
        metric::PositiveSoftAbsMetricRationalCertificate)
    eigen = metric.eigenvalue
    tanh_transport_error = eigen.tanh_error + eigen.argument_error
    ideal_tanh_lower = Rational{BigInt}(eigen.computed_tanh) -
        tanh_transport_error
    ideal_tanh_lower > 0 || throw(ArgumentError(
        "SoftAbs ideal tanh lower bound must be positive"))
    computed_sqrt_lower = Rational{BigInt}(metric.sqrt.computed) -
        metric.sqrt.error
    computed_sqrt_lower > 0 || throw(ArgumentError(
        "SoftAbs computed square-root lower bound must be positive"))
    eigenvalue_error = eigen.division_error +
        abs(Rational{BigInt}(eigen.hessian)) * tanh_transport_error /
        (abs(Rational{BigInt}(eigen.computed_tanh)) * ideal_tanh_lower)
    eigenvalue_lower = Rational{BigInt}(eigen.computed_eigenvalue) -
        eigenvalue_error
    eigenvalue_lower > 0 || throw(ArgumentError(
        "SoftAbs ideal eigenvalue lower bound must be positive"))
    ideal_sqrt = certify_sqrt_interval(eigenvalue_lower)
    ideal_sqrt_lower = Rational{BigInt}(ideal_sqrt.computed) - ideal_sqrt.error
    ideal_sqrt_lower > 0 || throw(ArgumentError(
        "SoftAbs ideal square-root lower bound must be positive"))
    sqrt_error = metric.sqrt.error + eigenvalue_error /
        (computed_sqrt_lower + ideal_sqrt_lower)
    factor_error = metric.factor.error + sqrt_error /
        (abs(Rational{BigInt}(metric.sqrt.computed)) * ideal_sqrt_lower)
    logdet_error = metric.logdet.error + eigenvalue_error /
        min(Rational{BigInt}(eigen.computed_eigenvalue), ideal_sqrt_lower^2)
    PositiveSoftAbsMetricErrorUpperCertificate(metric, ideal_tanh_lower,
        computed_sqrt_lower, ideal_sqrt_lower, eigenvalue_error, sqrt_error,
        factor_error, logdet_error)
end

function positive_softabs_metric_error_upper_certificate_arguments(
        certificate::PositiveSoftAbsMetricErrorUpperCertificate)
    vcat(positive_softabs_metric_certificate_arguments(certificate.metric), String[
        _exact_rational_wire(certificate.ideal_tanh_lower),
        _exact_rational_wire(certificate.computed_sqrt_lower),
        _exact_rational_wire(certificate.ideal_sqrt_lower),
        _exact_rational_wire(certificate.eigenvalue_error),
        _exact_rational_wire(certificate.sqrt_error),
        _exact_rational_wire(certificate.factor_error),
        _exact_rational_wire(certificate.logdet_error),
    ])
end

"""Linked rational certificate for one scalar SoftAbs GR-HMC energy."""
struct PositiveSoftAbsHamiltonianRationalCertificate
    metric::PositiveSoftAbsMetricRationalCertificate
    potential::Float64
    momentum::Float64
    kinetic::SqrtRationalIntervalCertificate
    kinetic_input_error::Rational{BigInt}
    computed_energy::Float64
    energy_arithmetic_error::Rational{BigInt}
end

function certify_positive_softabs_hamiltonian(smoothing::Real, hessian::Real,
        potential::Real, momentum::Real)
    u, p = Float64(potential), Float64(momentum)
    all(isfinite, (u, p)) || throw(DomainError((potential, momentum),
        "potential and momentum must be finite"))
    metric = certify_positive_softabs_metric(smoothing, hessian)
    transformed = metric.factor.computed * p
    radicand = transformed^2 + 1.0
    isfinite(radicand) && radicand > 0 || throw(DomainError(radicand,
        "relativistic kinetic radicand must be finite and positive"))
    kinetic = certify_sqrt_interval(radicand)
    exact_factor = Rational{BigInt}(metric.factor.computed)
    exact_momentum = Rational{BigInt}(p)
    ideal_observed_radicand = (exact_factor * exact_momentum)^2 + 1
    kinetic_input_error = abs(Rational{BigInt}(radicand) -
        ideal_observed_radicand)
    computed_energy = u + kinetic.computed + 0.5 * metric.logdet.computed
    isfinite(computed_energy) || throw(DomainError(computed_energy,
        "SoftAbs Hamiltonian must be finite"))
    exact_energy_expression = Rational{BigInt}(u) +
        Rational{BigInt}(kinetic.computed) +
        Rational{BigInt}(1, 2) * Rational{BigInt}(metric.logdet.computed)
    energy_arithmetic_error = abs(Rational{BigInt}(computed_energy) -
        exact_energy_expression)
    PositiveSoftAbsHamiltonianRationalCertificate(metric, u, p, kinetic,
        kinetic_input_error, computed_energy, energy_arithmetic_error)
end

function positive_softabs_hamiltonian_certificate_arguments(
        certificate::PositiveSoftAbsHamiltonianRationalCertificate)
    vcat(positive_softabs_metric_certificate_arguments(certificate.metric), String[
        _exact_rational_wire(certificate.potential),
        _exact_rational_wire(certificate.momentum),
        _exact_rational_wire(certificate.kinetic.input),
        _exact_rational_wire(certificate.kinetic.computed),
        string(numerator(certificate.kinetic.error), "/",
            denominator(certificate.kinetic.error)),
        string(numerator(certificate.kinetic_input_error), "/",
            denominator(certificate.kinetic_input_error)),
        _exact_rational_wire(certificate.computed_energy),
        string(numerator(certificate.energy_arithmetic_error), "/",
            denominator(certificate.energy_arithmetic_error)),
    ])
end

"""A complete rational upper error radius for one checked SoftAbs endpoint."""
struct PositiveSoftAbsHamiltonianErrorUpperCertificate
    endpoint::PositiveSoftAbsHamiltonianRationalCertificate
    metric_upper::PositiveSoftAbsMetricErrorUpperCertificate
    kinetic_sqrt_lower::Rational{BigInt}
    energy_error::Rational{BigInt}
end

function certify_positive_softabs_hamiltonian_error_upper(
        endpoint::PositiveSoftAbsHamiltonianRationalCertificate)
    metric_upper = certify_positive_softabs_metric_error_upper(endpoint.metric)
    kinetic_sqrt_lower = Rational{BigInt}(endpoint.kinetic.computed) -
        endpoint.kinetic.error
    kinetic_sqrt_lower > 0 || throw(ArgumentError(
        "kinetic square-root lower bound must be positive"))
    transformed_error = metric_upper.factor_error *
        abs(Rational{BigInt}(endpoint.momentum))
    computed_transformed = Rational{BigInt}(endpoint.metric.factor.computed) *
        Rational{BigInt}(endpoint.momentum)
    ideal_transformed_abs_upper =
        (abs(Rational{BigInt}(endpoint.metric.factor.computed)) +
            metric_upper.factor_error) *
        abs(Rational{BigInt}(endpoint.momentum))
    radicand_error = endpoint.kinetic_input_error +
        transformed_error * abs(computed_transformed) +
        ideal_transformed_abs_upper * transformed_error
    kinetic_error = endpoint.kinetic.error + radicand_error /
        (kinetic_sqrt_lower + 1)
    energy_error = endpoint.energy_arithmetic_error + kinetic_error +
        Rational{BigInt}(1, 2) * metric_upper.logdet_error
    PositiveSoftAbsHamiltonianErrorUpperCertificate(endpoint, metric_upper,
        kinetic_sqrt_lower, energy_error)
end

function positive_softabs_hamiltonian_error_upper_certificate_arguments(
        certificate::PositiveSoftAbsHamiltonianErrorUpperCertificate)
    vcat(positive_softabs_hamiltonian_certificate_arguments(certificate.endpoint),
        String[
            _exact_rational_wire(certificate.metric_upper.ideal_tanh_lower),
            _exact_rational_wire(certificate.metric_upper.computed_sqrt_lower),
            _exact_rational_wire(certificate.metric_upper.ideal_sqrt_lower),
            _exact_rational_wire(certificate.kinetic_sqrt_lower),
            _exact_rational_wire(certificate.energy_error),
        ])
end

"""Rational transport of a checked endpoint to the exact implicit state."""
struct PositiveSoftAbsEndpointStateTransportCertificate
    endpoint::PositiveSoftAbsHamiltonianErrorUpperCertificate
    solver_state_error::Rational{BigInt}
    energy_lipschitz::Rational{BigInt}
    total_energy_error::Rational{BigInt}
end

function certify_positive_softabs_endpoint_state_transport(
        endpoint::PositiveSoftAbsHamiltonianErrorUpperCertificate,
        solver_state_error::Real, energy_lipschitz::Real)
    state_error = Rational{BigInt}(solver_state_error)
    lipschitz = Rational{BigInt}(energy_lipschitz)
    state_error >= 0 || throw(DomainError(solver_state_error,
        "solver-state error must be nonnegative"))
    lipschitz >= 0 || throw(DomainError(energy_lipschitz,
        "energy Lipschitz bound must be nonnegative"))
    total = endpoint.energy_error + lipschitz * state_error
    PositiveSoftAbsEndpointStateTransportCertificate(endpoint, state_error,
        lipschitz, total)
end

function positive_softabs_endpoint_state_transport_certificate_arguments(
        certificate::PositiveSoftAbsEndpointStateTransportCertificate)
    vcat(positive_softabs_hamiltonian_error_upper_certificate_arguments(
            certificate.endpoint), String[
        _exact_rational_wire(certificate.solver_state_error),
        _exact_rational_wire(certificate.energy_lipschitz),
        _exact_rational_wire(certificate.total_energy_error),
    ])
end

"""A finite sequence of independently checked SoftAbs endpoint energies."""
struct PositiveSoftAbsHamiltonianTrajectoryRationalCertificate
    endpoints::Vector{PositiveSoftAbsHamiltonianRationalCertificate}
end


function certify_positive_softabs_hamiltonian_trajectory(smoothing::Real,
        hessians::AbstractVector{<:Real}, potentials::AbstractVector{<:Real},
        momenta::AbstractVector{<:Real})
    count = length(hessians)
    count > 0 || throw(ArgumentError("Hamiltonian trajectory cannot be empty"))
    length(potentials) == count && length(momenta) == count ||
        throw(DimensionMismatch("Hamiltonian trajectory fields"))
    PositiveSoftAbsHamiltonianTrajectoryRationalCertificate([
        certify_positive_softabs_hamiltonian(smoothing, hessians[i],
            potentials[i], momenta[i]) for i in eachindex(hessians)])
end

function positive_softabs_hamiltonian_trajectory_certificate_arguments(
        certificate::PositiveSoftAbsHamiltonianTrajectoryRationalCertificate)
    fields = String[string(length(certificate.endpoints))]
    for endpoint in certificate.endpoints
        append!(fields, positive_softabs_hamiltonian_certificate_arguments(endpoint))
    end
    fields
end

"""Transported nonpositive exponentials for every SoftAbs trajectory weight."""
struct PositiveSoftAbsStabilizedWeightTrajectoryRationalCertificate
    energy::PositiveSoftAbsHamiltonianTrajectoryRationalCertificate
    weights::Vector{ExpNonpositiveTransportRationalCertificate}
end


function certify_positive_softabs_stabilized_weights(
        energy::PositiveSoftAbsHamiltonianTrajectoryRationalCertificate)
    isempty(energy.endpoints) && throw(ArgumentError(
        "Hamiltonian trajectory cannot be empty"))
    exact_energies = Rational{BigInt}[
        Rational{BigInt}(endpoint.computed_energy) for endpoint in energy.endpoints]
    exact_logweights = .-exact_energies
    exact_maximum = maximum(exact_logweights)
    ideal_arguments = exact_logweights .- exact_maximum
    computed_logweights = .-[endpoint.computed_energy for endpoint in energy.endpoints]
    computed_maximum = maximum(computed_logweights)
    computed_arguments = computed_logweights .- computed_maximum
    weights = [certify_exp_nonpositive_transport(computed_arguments[i],
        ideal_arguments[i]) for i in eachindex(computed_arguments)]
    PositiveSoftAbsStabilizedWeightTrajectoryRationalCertificate(energy, weights)
end


function positive_softabs_stabilized_weight_certificate_arguments(
        certificate::PositiveSoftAbsStabilizedWeightTrajectoryRationalCertificate)
    fields = String[string(length(certificate.weights))]
    for weight in certificate.weights
        append!(fields, exp_nonpositive_transport_certificate_arguments(weight))
    end
    fields
end

"""Exact-rational residuals for each actual Float64 cumulative boundary."""
struct RoundedCumulativeRationalCertificate
    weights::Vector{Float64}
    boundaries::Vector{Float64}
    errors::Vector{Rational{BigInt}}
end


function certify_rounded_cumulative(weights::AbstractVector{<:Real})
    isempty(weights) && throw(ArgumentError("weight vector cannot be empty"))
    values = Float64.(weights)
    all(isfinite, values) || throw(DomainError(weights,
        "weights must be finite"))
    boundaries = Vector{Float64}(undef, length(values))
    running = 0.0
    for i in eachindex(values)
        running += values[i]
        boundaries[i] = running
    end
    exact_running = zero(Rational{BigInt})
    errors = Rational{BigInt}[]
    for i in eachindex(values)
        exact_running += Rational{BigInt}(values[i])
        push!(errors, abs(Rational{BigInt}(boundaries[i]) - exact_running))
    end
    RoundedCumulativeRationalCertificate(values, boundaries, errors)
end


function rounded_cumulative_certificate_arguments(
        certificate::RoundedCumulativeRationalCertificate)
    fields = String[string(length(certificate.weights))]
    for i in eachindex(certificate.weights)
        append!(fields, String[
            _exact_rational_wire(certificate.weights[i]),
            _exact_rational_wire(certificate.boundaries[i]),
            string(numerator(certificate.errors[i]), "/",
                denominator(certificate.errors[i])),
        ])
    end
    fields
end

"""Exact-rational residual for the final Float64 `uniform * total` draw."""
struct ScaledDrawRationalCertificate
    uniform::Float64
    total::Float64
    computed::Float64
    error::Rational{BigInt}
end


function certify_scaled_draw(uniform::Real, total::Real)
    u, t = Float64(uniform), Float64(total)
    isfinite(u) && 0 <= u < 1 || throw(DomainError(uniform,
        "uniform draw must be finite and lie in [0,1)"))
    isfinite(t) && t >= 0 || throw(DomainError(total,
        "total weight must be finite and nonnegative"))
    computed = u * t
    isfinite(computed) || throw(DomainError(computed,
        "scaled draw must be finite"))
    error = abs(Rational{BigInt}(computed) -
        Rational{BigInt}(u) * Rational{BigInt}(t))
    ScaledDrawRationalCertificate(u, t, computed, error)
end


scaled_draw_certificate_arguments(certificate::ScaledDrawRationalCertificate) =
    String[
        _exact_rational_wire(certificate.uniform),
        _exact_rational_wire(certificate.total),
        _exact_rational_wire(certificate.computed),
        string(numerator(certificate.error), "/", denominator(certificate.error)),
    ]

"""Exact-rational separation of one computed scaled draw from all computed
cumulative boundaries. The supplied errors must be the complete bounds used
by the corresponding Lean selection certificate; this record checks the
discontinuous decision margin, not the RNG's distributional semantics."""
struct MultinomialDecisionRationalCertificate
    computed_draw::Float64
    computed_boundaries::Vector{Float64}
    uniform_error::Rational{BigInt}
    boundary_error::Rational{BigInt}
end

uncertainty_band(certificate::MultinomialDecisionRationalCertificate) =
    certificate.uniform_error + certificate.boundary_error

is_stable(certificate::MultinomialDecisionRationalCertificate) =
    all(abs(Rational{BigInt}(certificate.computed_draw) -
            Rational{BigInt}(boundary)) > uncertainty_band(certificate)
        for boundary in certificate.computed_boundaries)


function certify_multinomial_decision(computed_draw::Real,
        computed_boundaries::AbstractVector{<:Real}, uniform_error::Real,
        boundary_error::Real)
    draw = Float64(computed_draw)
    boundaries = Float64.(computed_boundaries)
    isfinite(draw) || throw(DomainError(computed_draw,
        "computed draw must be finite"))
    !isempty(boundaries) && all(isfinite, boundaries) ||
        throw(DomainError(computed_boundaries,
            "computed boundaries must be nonempty and finite"))
    uerror = Rational{BigInt}(uniform_error)
    berror = Rational{BigInt}(boundary_error)
    uerror >= 0 || throw(DomainError(uniform_error,
        "uniform error must be nonnegative"))
    berror >= 0 || throw(DomainError(boundary_error,
        "boundary error must be nonnegative"))
    radius = uerror + berror
    all(abs(Rational{BigInt}(draw) - Rational{BigInt}(boundary)) > radius
        for boundary in boundaries) || throw(ArgumentError(
            "computed draw is not separated from every boundary"))
    MultinomialDecisionRationalCertificate(draw, boundaries, uerror, berror)
end


function multinomial_decision_certificate_arguments(
        certificate::MultinomialDecisionRationalCertificate)
    fields = String[
        _exact_rational_wire(certificate.computed_draw),
        string(length(certificate.computed_boundaries)),
        string(numerator(certificate.uniform_error), "/",
            denominator(certificate.uniform_error)),
        string(numerator(certificate.boundary_error), "/",
            denominator(certificate.boundary_error)),
    ]
    append!(fields, _exact_rational_wire.(certificate.computed_boundaries))
    fields
end

"""Complete rational error budget and stable decision for one maintained
SoftAbs multinomial selection. RNG distributional correctness remains a
separate contract; the observed Float64 uniform is interpreted exactly."""
struct PositiveSoftAbsSelectionErrorUpperCertificate
    endpoint_uppers::Vector{PositiveSoftAbsHamiltonianErrorUpperCertificate}
    common_energy_error::Rational{BigInt}
    common_weight_error::Rational{BigInt}
    boundary_error::Rational{BigInt}
    uniform_error::Rational{BigInt}
    decision::MultinomialDecisionRationalCertificate
end

function certify_positive_softabs_selection_error_upper(
        endpoint_uppers::AbstractVector{<:PositiveSoftAbsHamiltonianErrorUpperCertificate},
        weights::PositiveSoftAbsStabilizedWeightTrajectoryRationalCertificate,
        cumulative::RoundedCumulativeRationalCertificate,
        draw::ScaledDrawRationalCertificate)
    count = length(endpoint_uppers)
    count > 0 || throw(ArgumentError("SoftAbs trajectory cannot be empty"))
    length(weights.weights) == count && length(cumulative.weights) == count ||
        throw(DimensionMismatch("SoftAbs selection certificate lengths"))
    expected_weights = [weight.local_certificate.computed for weight in weights.weights]
    cumulative.weights == expected_weights || throw(ArgumentError(
        "cumulative inputs do not match the stabilized weights"))
    draw.total == cumulative.boundaries[end] || throw(ArgumentError(
        "scaled-draw total does not match the final cumulative boundary"))
    common_energy_error = maximum(upper.energy_error for upper in endpoint_uppers)
    common_weight_error = maximum(weight.local_certificate.error +
        weight.input_error for weight in weights.weights)
    propagated = count * (common_weight_error + 2 * common_energy_error)
    boundary_error = maximum(cumulative.errors) + propagated
    uniform_error = draw.error + abs(Rational{BigInt}(draw.uniform)) *
        (cumulative.errors[end] + propagated)
    decision = certify_multinomial_decision(draw.computed,
        cumulative.boundaries, uniform_error, boundary_error)
    PositiveSoftAbsSelectionErrorUpperCertificate(collect(endpoint_uppers),
        common_energy_error, common_weight_error, boundary_error,
        uniform_error, decision)
end

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

"""Bounded sign decision used by a dynamic-tree callback.

Stability means the computed scalar lies strictly outside `[-bound, bound]`.
As with `BoundWitness`, the supplied ideal value and analytic error budget are
premises; construction only checks their observed numerical consistency.
"""
struct SeparatedZeroDecisionCertificate
    witness::BoundWitness
    separation::BigFloat
end

is_stable(certificate::SeparatedZeroDecisionCertificate) =
    certificate.separation > 0
uncertainty_band(certificate::SeparatedZeroDecisionCertificate) =
    certificate.witness.bound

function certify_zero_decision(computed::Real, ideal::Real, bound::Real;
        precision::Integer=256)
    witness = certify_bound(computed, ideal, bound; precision=precision)
    setprecision(BigFloat, precision) do
        separation = abs(BigFloat(witness.computed)) - witness.bound
        SeparatedZeroDecisionCertificate(witness, separation)
    end
end

"""Two-sided comparison certificate with summed operand uncertainty."""
struct SeparatedComparisonCertificate
    left::BoundWitness
    right::BoundWitness
    separation::BigFloat
end

"""Bounded strict slice-eligibility and divergence decisions for one leaf."""
struct NUTSLeafEnergyCertificate
    log_slice::BoundWitness
    energy::BoundWitness
    max_energy_error::BoundWitness
    eligible::SeparatedComparisonCertificate
    continues::SeparatedComparisonCertificate
end


is_stable(certificate::NUTSLeafEnergyCertificate) =
    is_stable(certificate.eligible) && is_stable(certificate.continues)
uncertainty_band(certificate::NUTSLeafEnergyCertificate) = max(
    uncertainty_band(certificate.eligible),
    uncertainty_band(certificate.continues))

function certify_nuts_leaf_energy(; computed_log_slice::Real,
        ideal_log_slice::Real, log_slice_bound::Real,
        computed_energy::Real, ideal_energy::Real, energy_bound::Real,
        computed_max_energy_error::Real, ideal_max_energy_error::Real,
        max_energy_error_bound::Real,
        continuation_rounding_bound::Real=0, precision::Integer=256)
    log_slice = certify_bound(computed_log_slice, ideal_log_slice,
        log_slice_bound; precision=precision)
    energy = certify_bound(computed_energy, ideal_energy, energy_bound;
        precision=precision)
    max_error = certify_bound(computed_max_energy_error, ideal_max_energy_error,
        max_energy_error_bound; precision=precision)
    eligible = certify_comparison(computed_log_slice, ideal_log_slice,
        log_slice_bound, -Float64(computed_energy), -BigFloat(ideal_energy),
        energy_bound; precision=precision)
    computed_continuation_threshold =
        Float64(computed_max_energy_error) - Float64(computed_energy)
    continues = certify_comparison(computed_log_slice, ideal_log_slice,
        log_slice_bound,
        computed_continuation_threshold,
        BigFloat(ideal_max_energy_error) - BigFloat(ideal_energy),
        BigFloat(continuation_rounding_bound) +
            BigFloat(max_energy_error_bound) + BigFloat(energy_bound);
        precision=precision)
    NUTSLeafEnergyCertificate(log_slice, energy, max_error, eligible, continues)
end

"""Return `(eligible, continues)`, or `nothing` if either bit is ambiguous."""
function certified_nuts_leaf_decisions(certificate::NUTSLeafEnergyCertificate)
    is_stable(certificate) || return nothing
    (; eligible=certificate.eligible.left.computed <
            certificate.eligible.right.computed,
        continues=certificate.continues.left.computed <
            certificate.continues.right.computed)
end

is_stable(certificate::SeparatedComparisonCertificate) =
    certificate.separation > 0
uncertainty_band(certificate::SeparatedComparisonCertificate) =
    certificate.left.bound + certificate.right.bound

function certify_comparison(computed_left::Real, ideal_left::Real,
        left_bound::Real, computed_right::Real, ideal_right::Real,
        right_bound::Real; precision::Integer=256)
    left = certify_bound(computed_left, ideal_left, left_bound;
        precision=precision)
    right = certify_bound(computed_right, ideal_right, right_bound;
        precision=precision)
    setprecision(BigFloat, precision) do
        computed_difference = BigFloat(left.computed) - BigFloat(right.computed)
        separation = abs(computed_difference) - (left.bound + right.bound)
        SeparatedComparisonCertificate(left, right, separation)
    end
end

"""Certificate for the two endpoint dot-product signs in a U-turn test."""
struct UTurnDecisionCertificate
    left_momentum::SeparatedZeroDecisionCertificate
    right_momentum::SeparatedZeroDecisionCertificate
end

is_stable(certificate::UTurnDecisionCertificate) =
    is_stable(certificate.left_momentum) &&
    is_stable(certificate.right_momentum)
uncertainty_band(certificate::UTurnDecisionCertificate) = max(
    uncertainty_band(certificate.left_momentum),
    uncertainty_band(certificate.right_momentum))

"""Return the certified computed U-turn bit, or `nothing` when ambiguous."""
function certified_uturn_decision(certificate::UTurnDecisionCertificate)
    is_stable(certificate) || return nothing
    certificate.left_momentum.witness.computed < 0 ||
        certificate.right_momentum.witness.computed < 0
end

function certify_uturn_decision(computed_left::Real, ideal_left::Real,
        left_bound::Real, computed_right::Real, ideal_right::Real,
        right_bound::Real; precision::Integer=256)
    UTurnDecisionCertificate(
        certify_zero_decision(computed_left, ideal_left, left_bound;
            precision=precision),
        certify_zero_decision(computed_right, ideal_right, right_bound;
            precision=precision))
end

"""Componentwise endpoint witnesses and their composed U-turn decision."""
struct VectorUTurnDecisionCertificate
    left_positions::Vector{BoundWitness}
    right_positions::Vector{BoundWitness}
    left_momenta::Vector{BoundWitness}
    right_momenta::Vector{BoundWitness}
    decision::UTurnDecisionCertificate
end

is_stable(certificate::VectorUTurnDecisionCertificate) =
    is_stable(certificate.decision)
uncertainty_band(certificate::VectorUTurnDecisionCertificate) =
    uncertainty_band(certificate.decision)
certified_uturn_decision(certificate::VectorUTurnDecisionCertificate) =
    certified_uturn_decision(certificate.decision)

"""Compose componentwise phase bounds into both endpoint-dot certificates.

`*_rounding_bound` covers the final Float64 subtraction, multiplication, and
reduction relative to exact real arithmetic on the stored Float64 components.
The componentwise bounds and supplied ideal vectors remain proof inputs.
"""
function certify_vector_uturn_decision(
        computed_left_position::AbstractVector{<:Real},
        ideal_left_position::AbstractVector{<:Real},
        left_position_bound::AbstractVector{<:Real},
        computed_right_position::AbstractVector{<:Real},
        ideal_right_position::AbstractVector{<:Real},
        right_position_bound::AbstractVector{<:Real},
        computed_left_momentum::AbstractVector{<:Real},
        ideal_left_momentum::AbstractVector{<:Real},
        left_momentum_bound::AbstractVector{<:Real},
        computed_right_momentum::AbstractVector{<:Real},
        ideal_right_momentum::AbstractVector{<:Real},
        right_momentum_bound::AbstractVector{<:Real};
        left_rounding_bound::Real=0,
        right_rounding_bound::Real=0,
        precision::Integer=256)
    dimension = length(computed_left_position)
    all(length(values) == dimension for values in (
        ideal_left_position, left_position_bound,
        computed_right_position, ideal_right_position, right_position_bound,
        computed_left_momentum, ideal_left_momentum, left_momentum_bound,
        computed_right_momentum, ideal_right_momentum, right_momentum_bound)) ||
        throw(DimensionMismatch("phase endpoint vectors and bounds must match"))
    dimension > 0 || throw(ArgumentError("phase endpoint dimension must be positive"))

    left_positions = [certify_bound(computed_left_position[i],
        ideal_left_position[i], left_position_bound[i]; precision=precision)
        for i in 1:dimension]
    right_positions = [certify_bound(computed_right_position[i],
        ideal_right_position[i], right_position_bound[i]; precision=precision)
        for i in 1:dimension]
    left_momenta = [certify_bound(computed_left_momentum[i],
        ideal_left_momentum[i], left_momentum_bound[i]; precision=precision)
        for i in 1:dimension]
    right_momenta = [certify_bound(computed_right_momentum[i],
        ideal_right_momentum[i], right_momentum_bound[i]; precision=precision)
        for i in 1:dimension]

    decision = setprecision(BigFloat, precision) do
        ideal_displacement = BigFloat.(ideal_right_position) .-
            BigFloat.(ideal_left_position)
        ideal_left_dot = sum(ideal_displacement .* BigFloat.(ideal_left_momentum))
        ideal_right_dot = sum(ideal_displacement .* BigFloat.(ideal_right_momentum))
        computed_displacement = Float64.(computed_right_position) .-
            Float64.(computed_left_position)
        computed_left = sum(computed_displacement .* Float64.(computed_left_momentum))
        computed_right = sum(computed_displacement .* Float64.(computed_right_momentum))
        position_error = BigFloat.(right_position_bound) .+
            BigFloat.(left_position_bound)
        left_error = BigFloat(left_rounding_bound) + sum(
            position_error .* abs.(BigFloat.(computed_left_momentum)) .+
            abs.(ideal_displacement) .* BigFloat.(left_momentum_bound))
        right_error = BigFloat(right_rounding_bound) + sum(
            position_error .* abs.(BigFloat.(computed_right_momentum)) .+
            abs.(ideal_displacement) .* BigFloat.(right_momentum_bound))
        certify_uturn_decision(computed_left, ideal_left_dot, left_error,
            computed_right, ideal_right_dot, right_error; precision=precision)
    end
    VectorUTurnDecisionCertificate(left_positions, right_positions,
        left_momenta, right_momenta, decision)
end

"""Certificates for every adjacent endpoint test on one phase trajectory."""
struct VectorUTurnTrajectoryCertificate
    edges::Vector{VectorUTurnDecisionCertificate}
end

is_stable(certificate::VectorUTurnTrajectoryCertificate) =
    all(is_stable, certificate.edges)
uncertainty_band(certificate::VectorUTurnTrajectoryCertificate) =
    maximum(uncertainty_band, certificate.edges; init=big"0")

function certified_uturn_decisions(certificate::VectorUTurnTrajectoryCertificate)
    is_stable(certificate) || return nothing
    Bool[certified_uturn_decision(edge)::Bool for edge in certificate.edges]
end

function certify_vector_uturn_trajectory(
        computed_positions::AbstractVector{<:AbstractVector{<:Real}},
        ideal_positions::AbstractVector{<:AbstractVector{<:Real}},
        position_bounds::AbstractVector{<:AbstractVector{<:Real}},
        computed_momenta::AbstractVector{<:AbstractVector{<:Real}},
        ideal_momenta::AbstractVector{<:AbstractVector{<:Real}},
        momentum_bounds::AbstractVector{<:AbstractVector{<:Real}};
        left_rounding_bounds::AbstractVector{<:Real}=
            zeros(max(length(computed_positions) - 1, 0)),
        right_rounding_bounds::AbstractVector{<:Real}=
            zeros(max(length(computed_positions) - 1, 0)),
        precision::Integer=256)
    count = length(computed_positions)
    count > 0 || throw(ArgumentError("phase trajectory cannot be empty"))
    all(length(values) == count for values in (ideal_positions,
        position_bounds, computed_momenta, ideal_momenta, momentum_bounds)) ||
        throw(DimensionMismatch("phase trajectories and bound arrays must match"))
    length(left_rounding_bounds) == count - 1 &&
        length(right_rounding_bounds) == count - 1 ||
        throw(DimensionMismatch("one pair of rounding bounds is required per edge"))
    edges = Vector{VectorUTurnDecisionCertificate}(undef, count - 1)
    for edge in eachindex(edges)
        edges[edge] = certify_vector_uturn_decision(
            computed_positions[edge], ideal_positions[edge], position_bounds[edge],
            computed_positions[edge + 1], ideal_positions[edge + 1],
            position_bounds[edge + 1],
            computed_momenta[edge], ideal_momenta[edge], momentum_bounds[edge],
            computed_momenta[edge + 1], ideal_momenta[edge + 1],
            momentum_bounds[edge + 1];
            left_rounding_bound=left_rounding_bounds[edge],
            right_rounding_bound=right_rounding_bounds[edge],
            precision=precision)
    end
    VectorUTurnTrajectoryCertificate(edges)
end

"""All distinct endpoint U-turn certificates for one linked trajectory.

The diagonal is intentionally omitted: a self-displacement has dot product
zero and cannot satisfy strict separation. Lean's recursive-row refinement
handles those pairs structurally and consumes exactly the off-diagonal
certificates represented here.
"""
struct RecursiveDoublingUTurnCertificate
    count::Int
    pairs::Dict{Tuple{Int,Int},VectorUTurnDecisionCertificate}
end

is_stable(certificate::RecursiveDoublingUTurnCertificate) =
    length(certificate.pairs) == certificate.count * (certificate.count - 1) &&
    all(is_stable, values(certificate.pairs))
uncertainty_band(certificate::RecursiveDoublingUTurnCertificate) =
    maximum(uncertainty_band, values(certificate.pairs); init=big"0")

function certified_uturn_decisions(
        certificate::RecursiveDoublingUTurnCertificate)
    is_stable(certificate) || return nothing
    Dict(pair => certified_uturn_decision(decision)::Bool
        for (pair, decision) in certificate.pairs)
end

"""Compose a linked leapfrog trajectory into every recursive U-turn margin.

Primitive step records determine all later computed/ideal endpoints and their
proved recurrence budgets. The caller supplies only the initial endpoint
budgets and optional final dot-reduction bounds. This is the executable adapter
for Lean's `recursiveDoublingKernel_eq_ideal` theorem; supplied ideal values and
primitive operation bounds remain the explicit trust boundary.
"""
function certify_recursive_doubling_uturn_matrix(
        trajectory::LinkedLeapfrogVectorTrajectoryCertificate;
        initial_position_error::Real=0,
        initial_momentum_error::Real=0,
        left_rounding_bound::Real=0,
        right_rounding_bound::Real=0,
        precision::Integer=256)
    position_error = BigFloat(initial_position_error)
    momentum_error = BigFloat(initial_momentum_error)
    position_error >= 0 && momentum_error >= 0 || throw(ArgumentError(
        "initial trajectory errors must be nonnegative"))
    left_rounding_bound >= 0 && right_rounding_bound >= 0 ||
        throw(ArgumentError("dot-product rounding bounds must be nonnegative"))

    computed_positions = Vector{Vector{Float64}}()
    ideal_positions = Vector{Vector{BigFloat}}()
    position_bounds = Vector{Vector{BigFloat}}()
    computed_momenta = Vector{Vector{Float64}}()
    ideal_momenta = Vector{Vector{BigFloat}}()
    momentum_bounds = Vector{Vector{BigFloat}}()
    dimension = length(trajectory.initial_computed_position)

    function push_endpoint!(computed_position, ideal_position, ep,
            computed_momentum, ideal_momentum, em)
        for coordinate in eachindex(computed_position)
            certify_bound(computed_position[coordinate], ideal_position[coordinate],
                ep; precision=precision)
            certify_bound(computed_momentum[coordinate], ideal_momentum[coordinate],
                em; precision=precision)
        end
        push!(computed_positions, Float64.(computed_position))
        push!(ideal_positions, BigFloat.(ideal_position))
        push!(position_bounds, fill(BigFloat(ep), dimension))
        push!(computed_momenta, Float64.(computed_momentum))
        push!(ideal_momenta, BigFloat.(ideal_momentum))
        push!(momentum_bounds, fill(BigFloat(em), dimension))
    end

    push_endpoint!(trajectory.initial_computed_position,
        trajectory.initial_ideal_position, position_error,
        trajectory.initial_computed_momentum,
        trajectory.initial_ideal_momentum, momentum_error)
    for step in trajectory.steps
        computed_position = [coordinate.drift_rounding.computed
            for coordinate in step.coordinates]
        ideal_position = [_ideal_next_position(coordinate)
            for coordinate in step.coordinates]
        computed_momentum = [coordinate.final_kick_rounding.computed
            for coordinate in step.coordinates]
        ideal_momentum = [_ideal_next_momentum(coordinate)
            for coordinate in step.coordinates]
        push_endpoint!(computed_position, ideal_position,
            step.next_position_error, computed_momentum, ideal_momentum,
            step.next_momentum_error)
    end

    count = length(computed_positions)
    pairs = Dict{Tuple{Int,Int},VectorUTurnDecisionCertificate}()
    for left in 1:count, right in 1:count
        left == right && continue
        pairs[(left, right)] = certify_vector_uturn_decision(
            computed_positions[left], ideal_positions[left], position_bounds[left],
            computed_positions[right], ideal_positions[right], position_bounds[right],
            computed_momenta[left], ideal_momenta[left], momentum_bounds[left],
            computed_momenta[right], ideal_momenta[right], momentum_bounds[right];
            left_rounding_bound=left_rounding_bound,
            right_rounding_bound=right_rounding_bound,
            precision=precision)
    end
    RecursiveDoublingUTurnCertificate(count, pairs)
end

"""All primitive comparison certificates visited by one completed tree.

The recursive topology and ordering are supplied by the caller. Stability
means every recorded leaf and internal U-turn decision clears its uncertainty
band, matching Lean's tree-local `DecisionsAgree` interface.
"""
struct CompletedTreeDecisionCertificate
    leaf_comparisons::Vector{SeparatedComparisonCertificate}
    uturn_decisions::Vector{UTurnDecisionCertificate}
end

"""Leaf and join certificates for one complete recursive NUTS tree."""
struct NUTSCompletedTreeCertificate
    leaves::Vector{NUTSLeafEnergyCertificate}
    joins::Vector{UTurnDecisionCertificate}
end

is_stable(certificate::NUTSCompletedTreeCertificate) =
    all(is_stable, certificate.leaves) && all(is_stable, certificate.joins)
uncertainty_band(certificate::NUTSCompletedTreeCertificate) = max(
    maximum(uncertainty_band, certificate.leaves; init=big"0"),
    maximum(uncertainty_band, certificate.joins; init=big"0"))

"""Expose all certified tree bits, or fail closed if any margin is ambiguous."""
function certified_nuts_completed_tree(certificate::NUTSCompletedTreeCertificate)
    is_stable(certificate) || return nothing
    leaf = [certified_nuts_leaf_decisions(item) for item in certificate.leaves]
    (; eligible=Bool[item.eligible for item in leaf],
        continues=Bool[item.continues for item in leaf],
        turns=Bool[certified_uturn_decision(item)::Bool for item in certificate.joins])
end

is_stable(certificate::CompletedTreeDecisionCertificate) =
    all(is_stable, certificate.leaf_comparisons) &&
    all(is_stable, certificate.uturn_decisions)
uncertainty_band(certificate::CompletedTreeDecisionCertificate) = max(
    maximum(uncertainty_band, certificate.leaf_comparisons; init=big"0"),
    maximum(uncertainty_band, certificate.uturn_decisions; init=big"0"))

"""Checked comparison margins for one finite stepping-out/shrinkage trace.

The supplied ideals and bounds remain proof inputs. When `is_stable` holds,
Lean's `SliceComparisonCertificate.lt_threshold_eq`, `le_threshold_eq`, and
`ge_threshold_eq` theorems prove the corresponding strict, endpoint-stop, and
proposal-accept comparisons agree with ideal-real execution. Joining those
pointwise results to a concrete runtime trace still requires matching its
comparison order and kind.
"""
struct SliceComparisonCertificate
    threshold::BoundWitness
    values::Vector{BoundWitness}
    minimum_margin::BigFloat
    maximum_uncertainty::BigFloat
end

is_stable(certificate::SliceComparisonCertificate) =
    certificate.maximum_uncertainty < certificate.minimum_margin
uncertainty_band(certificate::SliceComparisonCertificate) =
    certificate.maximum_uncertainty

function certify_slice_comparisons(computed_threshold::Real,
        ideal_threshold::Real, threshold_bound::Real,
        computed_values::AbstractVector{<:Real},
        ideal_values::AbstractVector{<:Real},
        value_bounds::AbstractVector{<:Real}; precision::Integer=256)
    length(computed_values) == length(ideal_values) == length(value_bounds) ||
        throw(DimensionMismatch("value and bound vectors must have equal length"))
    isempty(computed_values) &&
        throw(ArgumentError("a slice trace must contain at least one comparison"))
    threshold = certify_bound(computed_threshold, ideal_threshold,
        threshold_bound; precision=precision)
    values = [certify_bound(computed_values[index], ideal_values[index],
        value_bounds[index]; precision=precision) for index in eachindex(computed_values)]
    setprecision(BigFloat, precision) do
        minimum_margin = minimum(abs(witness.ideal - threshold.ideal)
            for witness in values)
        maximum_uncertainty = maximum(witness.bound + threshold.bound
            for witness in values)
        SliceComparisonCertificate(threshold, values, minimum_margin,
            maximum_uncertainty)
    end
end

@enum SliceComparisonKind begin
    StrictBelow
    StopBelow
    AcceptAbove
end

"""Ordered practical-slice decisions paired with their margin certificate.

The kind vector has exactly one entry per observed callback comparison. It is
the runtime counterpart of Lean's `SliceComparisonKind` schedule in
`SliceComparisonCertificate.decisionTrace_eq`.
"""
struct SliceDecisionTraceCertificate
    comparisons::SliceComparisonCertificate
    kinds::Vector{SliceComparisonKind}
    computed_decisions::Vector{Bool}
    ideal_decisions::Vector{Bool}
end

"""Checked decomposition of `logdensity(current) + log(u)`.

The callback, logarithm, and final rounded addition are checked separately.
The `threshold` witness uses their summed bound, matching Lean's
`SliceThresholdCertificate.threshold_bound` theorem.
"""
struct SliceThresholdCertificate
    base::BoundWitness
    log_uniform::BoundWitness
    addition::BoundWitness
    threshold::BoundWitness
end

"""Guarded transport of one observed unit-uniform draw through `log`.

`log_of_computed_uniform` and `log_of_ideal_uniform` are exact-real oracle
inputs. Construction checks the RNG-input and local-log bounds and applies the
proved `local + input/lower` transport factor; it does not claim platform
`BigFloat` or `libm` is itself such an oracle.
"""
struct SliceLogUniformCertificate
    uniform::BoundWitness
    local_log::BoundWitness
    log::BoundWitness
    lower::BigFloat
end

function certify_slice_log_uniform(computed_uniform::Real,
        ideal_uniform::Real, uniform_bound::Real, computed_log::Real,
        log_of_computed_uniform::Real, local_log_bound::Real,
        log_of_ideal_uniform::Real, lower::Real; precision::Integer=256)
    uniform = certify_bound(computed_uniform, ideal_uniform, uniform_bound;
        precision=precision)
    local_log = certify_bound(computed_log, log_of_computed_uniform,
        local_log_bound; precision=precision)
    setprecision(BigFloat, precision) do
        guarded_lower = BigFloat(lower)
        isfinite(guarded_lower) && guarded_lower > 0 || throw(ArgumentError(
            "slice logarithm lower bound must be finite and positive"))
        guarded_lower <= BigFloat(uniform.computed) &&
            guarded_lower <= uniform.ideal || throw(ArgumentError(
            "slice uniform values must satisfy the positive lower bound"))
        transported_bound = local_log.bound + uniform.bound / guarded_lower
        log_witness = certify_bound(computed_log, log_of_ideal_uniform,
            transported_bound; precision=precision)
        SliceLogUniformCertificate(uniform, local_log, log_witness,
            guarded_lower)
    end
end

function certify_slice_threshold(computed_base::Real, ideal_base::Real,
        base_bound::Real, computed_log::Real, ideal_log::Real,
        log_bound::Real, computed_threshold::Real, addition_bound::Real;
        precision::Integer=256)
    base = certify_bound(computed_base, ideal_base, base_bound;
        precision=precision)
    log_uniform = certify_bound(computed_log, ideal_log, log_bound;
        precision=precision)
    addition_ideal = setprecision(BigFloat, precision) do
        BigFloat(base.computed) + BigFloat(log_uniform.computed)
    end
    addition = certify_bound(computed_threshold, addition_ideal,
        addition_bound; precision=precision)
    setprecision(BigFloat, precision) do
        ideal_threshold = base.ideal + log_uniform.ideal
        total_bound = addition.bound + base.bound + log_uniform.bound
        threshold = certify_bound(computed_threshold, ideal_threshold,
            total_bound; precision=precision)
        SliceThresholdCertificate(base, log_uniform, addition, threshold)
    end
end

function certify_slice_threshold(computed_base::Real, ideal_base::Real,
        base_bound::Real, log_uniform::SliceLogUniformCertificate,
        computed_threshold::Real, addition_bound::Real;
        precision::Integer=256)
    certify_slice_threshold(computed_base, ideal_base, base_bound,
        log_uniform.log.computed, log_uniform.log.ideal,
        log_uniform.log.bound, computed_threshold, addition_bound;
        precision=precision)
end

function _slice_decision(kind::SliceComparisonKind, value, threshold)
    kind == StrictBelow && return value < threshold
    kind == StopBelow && return value <= threshold
    threshold <= value
end

function certify_slice_decision_trace(kinds::AbstractVector{SliceComparisonKind},
        computed_threshold::Real, ideal_threshold::Real, threshold_bound::Real,
        computed_values::AbstractVector{<:Real},
        ideal_values::AbstractVector{<:Real},
        value_bounds::AbstractVector{<:Real}; precision::Integer=256)
    length(kinds) == length(computed_values) || throw(DimensionMismatch(
        "comparison kinds and values must have equal length"))
    comparisons = certify_slice_comparisons(computed_threshold,
        ideal_threshold, threshold_bound, computed_values, ideal_values,
        value_bounds; precision=precision)
    ordered_kinds = collect(kinds)
    computed = [_slice_decision(kind, witness.computed,
        comparisons.threshold.computed)
        for (kind, witness) in zip(ordered_kinds, comparisons.values)]
    ideal = [_slice_decision(kind, witness.ideal,
        comparisons.threshold.ideal)
        for (kind, witness) in zip(ordered_kinds, comparisons.values)]
    SliceDecisionTraceCertificate(comparisons, ordered_kinds, computed, ideal)
end

function certify_slice_decision_trace(kinds::AbstractVector{SliceComparisonKind},
        threshold::SliceThresholdCertificate,
        computed_values::AbstractVector{<:Real},
        ideal_values::AbstractVector{<:Real},
        value_bounds::AbstractVector{<:Real}; precision::Integer=256)
    certify_slice_decision_trace(kinds, threshold.threshold.computed,
        threshold.threshold.ideal, threshold.threshold.bound,
        computed_values, ideal_values, value_bounds; precision=precision)
end

is_stable(certificate::SliceDecisionTraceCertificate) =
    is_stable(certificate.comparisons) &&
    certificate.computed_decisions == certificate.ideal_decisions
uncertainty_band(certificate::SliceDecisionTraceCertificate) =
    uncertainty_band(certificate.comparisons)

"""Return the common checked decision trace, or fail closed at a boundary."""
certified_slice_decisions(certificate::SliceDecisionTraceCertificate) =
    is_stable(certificate) ? copy(certificate.computed_decisions) : nothing

"""Checked residual information for one implicit generalized-leapfrog solve.

This certificate deliberately separates a numerical residual bound from the
global reversibility and volume-preservation obligations. Only a zero bound,
zero observed residual, and explicit global witnesses qualify as an exact
solver certificate; a small positive tolerance is merely approximation data.
"""
struct ImplicitSolveCertificate
    half_momentum_residual::BoundWitness
    position_residual::BoundWitness
    unique::Bool
    reversible::Bool
    volume_preserving::Bool
end

function certify_implicit_solve(half_momentum_residual::Real,
        half_momentum_bound::Real, position_residual::Real,
        position_bound::Real; unique::Bool=false, reversible::Bool=false,
        volume_preserving::Bool=false, precision::Integer=256)
    half = certify_bound(half_momentum_residual, 0, half_momentum_bound;
        precision=precision)
    position = certify_bound(position_residual, 0, position_bound;
        precision=precision)
    ImplicitSolveCertificate(half, position, unique, reversible,
        volume_preserving)
end


certifies_exact_solver(certificate::ImplicitSolveCertificate) =
    iszero(certificate.half_momentum_residual.bound) &&
    iszero(certificate.position_residual.bound) &&
    iszero(certificate.half_momentum_residual.observed_error) &&
    iszero(certificate.position_residual.observed_error) &&
    certificate.unique && certificate.reversible && certificate.volume_preserving

"""A posteriori distance bound from a computed fixed-point residual.

Lean proves `distance_to_exact ≤ (abs(residual) + residual_error)/(1-rate)`
for a genuine contraction. This runtime record evaluates that bound after
checking its scalar premises; it does not itself prove that the callback has
the supplied contraction rate or residual error.
"""
struct ContractionErrorBound
    computed_residual::Float64
    residual_error::BigFloat
    rate::BigFloat
    distance_bound::BigFloat
end

"""Exact-rational a posteriori budget for a contraction solve.

The record proves the arithmetic formula `distance = residual/(1-rate)` and
the rate guard. A Lean client must still prove that `residual_upper` bounds the
exact one-step residual and that the update really contracts at `rate`.
"""
struct AposterioriContractionRationalCertificate
    residual_upper::Rational{BigInt}
    rate::Rational{BigInt}
    distance_upper::Rational{BigInt}
end

function certify_contraction_aposteriori(residual_upper::Real, rate::Real)
    residual = Rational{BigInt}(residual_upper)
    contraction_rate = Rational{BigInt}(rate)
    residual >= 0 || throw(DomainError(residual_upper,
        "residual upper bound must be nonnegative"))
    0 <= contraction_rate < 1 || throw(DomainError(rate,
        "contraction rate must lie in [0, 1)"))
    AposterioriContractionRationalCertificate(residual, contraction_rate,
        residual / (1 - contraction_rate))
end

contraction_aposteriori_certificate_arguments(
        certificate::AposterioriContractionRationalCertificate) = [
    string(numerator(value), "/", denominator(value))
    for value in (certificate.residual_upper, certificate.rate,
        certificate.distance_upper)
]

"""Exact rational residual budget for one rounded scalar fixed-point update."""
struct RoundedContractionResidualRationalCertificate
    iterate::Rational{BigInt}
    computed_update::Rational{BigInt}
    update_error::Rational{BigInt}
    residual_upper::Rational{BigInt}
end

"""Exact arithmetic and explicit callback error for `base + scale*callback`."""
struct RoundedAffineUpdateRationalCertificate
    base::Rational{BigInt}
    scale::Rational{BigInt}
    computed_callback::Rational{BigInt}
    callback_error::Rational{BigInt}
    computed_update::Rational{BigInt}
    arithmetic_error::Rational{BigInt}
    update_error::Rational{BigInt}
end


function certify_rounded_affine_update(base::Real, scale::Real,
        computed_callback::Real, callback_error::Real, computed_update::Real)
    exact_base = Rational{BigInt}(base)
    exact_scale = Rational{BigInt}(scale)
    exact_callback = Rational{BigInt}(computed_callback)
    error = Rational{BigInt}(callback_error)
    exact_update = Rational{BigInt}(computed_update)
    error >= 0 || throw(DomainError(callback_error,
        "callback error must be nonnegative"))
    arithmetic_error = abs(exact_update -
        (exact_base + exact_scale * exact_callback))
    update_error = arithmetic_error + abs(exact_scale) * error
    RoundedAffineUpdateRationalCertificate(exact_base, exact_scale,
        exact_callback, error, exact_update, arithmetic_error, update_error)
end


rounded_affine_update_certificate_arguments(
        certificate::RoundedAffineUpdateRationalCertificate) = [
    string(numerator(value), "/", denominator(value))
    for value in (certificate.base, certificate.scale,
        certificate.computed_callback, certificate.callback_error,
        certificate.computed_update, certificate.arithmetic_error,
        certificate.update_error)
]

"""All rounded affine updates made by one bounded-scalar fixed-point trace,
with one-based indices into its ordered callback certificate list."""
struct BoundedScalarAffineTraceRationalCertificate
    kinds::Vector{Symbol}
    callback_indices::Vector{Vector{Int}}
    callback_arithmetic_errors::Vector{Rational{BigInt}}
    updates::Vector{RoundedAffineUpdateRationalCertificate}
end

function _bounded_scalar_callback_error(
        certificate::BoundedScalarCallbackRationalCertificate, kind::Symbol)
    sincos = certificate.sincos
    p = Rational{BigInt}(certificate.momentum)
    transformed = (2 + Rational{BigInt}(sincos.computed_sin)) * p
    transformed_error = sincos.sin_error * abs(p)
    radicand_error = certificate.radicand_arithmetic_error +
        transformed_error * (2 * abs(transformed) + transformed_error)
    sqrt_error = _bounded_scalar_sqrt_error(certificate)
    reciprocal_error = certificate.reciprocal_certificate.error +
        sqrt_error / certificate.computed_sqrt_lower
    inverse_hat = Rational{BigInt}(certificate.reciprocal_certificate.computed)
    if kind === :momentum
        scale_momentum_error = sincos.sin_error * abs(transformed) +
            3 * transformed_error
        semantic_error = scale_momentum_error * abs(inverse_hat) +
            3(abs(transformed) + transformed_error) * reciprocal_error
        certificate.momentum_arithmetic_error + semantic_error
    elseif kind === :position
        scale_cos_error = sincos.sin_error *
            abs(Rational{BigInt}(sincos.computed_cos)) + 3 * sincos.cos_error
        semantic_error = scale_cos_error * abs(p^2) * abs(inverse_hat) +
            3 * abs(p^2) * reciprocal_error
        certificate.position_arithmetic_error + semantic_error
    else
        throw(ArgumentError("unknown bounded scalar callback kind: $kind"))
    end
end

function _bounded_scalar_sqrt_error(
        certificate::BoundedScalarCallbackRationalCertificate)
    sincos = certificate.sincos
    p = Rational{BigInt}(certificate.momentum)
    transformed = (2 + Rational{BigInt}(sincos.computed_sin)) * p
    transformed_error = sincos.sin_error * abs(p)
    radicand_error = certificate.radicand_arithmetic_error +
        transformed_error * (2 * abs(transformed) + transformed_error)
    certificate.sqrt_certificate.error + radicand_error / 2
end

function certify_bounded_scalar_affine_trace(trace,
        callbacks::BoundedScalarCallbackTraceRationalCertificate)
    half = callbacks.half_iterations
    position = callbacks.position_iterations
    length(callbacks.certificates) == half + position + 4 ||
        throw(ArgumentError("callback certificate count does not match iterations"))
    expected_updates = half + position + 3
    length(trace.affine_updates) == expected_updates ||
        throw(ArgumentError("affine update count does not match iterations"))
    initial_velocity = half + 1
    final_half = half + position + 2
    final_velocity = half + position + 3
    final_position = half + position + 4
    kinds = Symbol[]
    callback_indices = Vector{Int}[]
    callback_arithmetic_errors = Rational{BigInt}[]
    updates = RoundedAffineUpdateRationalCertificate[]
    for (update_index, evaluation) in enumerate(trace.affine_updates)
        indices = if update_index <= half
            [update_index]
        elseif update_index <= half + position
            [initial_velocity, half + 1 + (update_index - half)]
        elseif update_index == half + position + 1
            [final_half]
        elseif update_index == half + position + 2
            [initial_velocity, final_velocity]
        else
            [final_position]
        end
        expected_kind = update_index <= half ? :half_momentum :
            update_index <= half + position ? :position :
            update_index == half + position + 1 ? :half_momentum :
            update_index == half + position + 2 ? :position : :final_momentum
        evaluation.kind === expected_kind || throw(ArgumentError(
            "affine update kind does not match fixed-point phase"))
        length(evaluation.base) == 1 && length(evaluation.computed_update) == 1 ||
            throw(DimensionMismatch("bounded scalar affine updates must be scalar"))
        length(evaluation.callbacks) == length(indices) || throw(ArgumentError(
            "affine callback arity does not match fixed-point phase"))
        computed_callback = sum(callback[1] for callback in evaluation.callbacks)
        source_error = sum(_bounded_scalar_callback_error(
            callbacks.certificates[index], callbacks.kinds[index])
            for index in indices)
        source_center = sum(callbacks.kinds[index] === :position ?
            Rational{BigInt}(callbacks.certificates[index].computed_position_callback) :
            Rational{BigInt}(callbacks.certificates[index].computed_momentum_callback)
            for index in indices)
        callback_arithmetic_error = abs(Rational{BigInt}(computed_callback) -
            source_center)
        callback_error = callback_arithmetic_error + source_error
        for (callback, index) in zip(evaluation.callbacks, indices)
            observed = callbacks.kinds[index] === :position ?
                callbacks.certificates[index].computed_position_callback :
                callbacks.certificates[index].computed_momentum_callback
            callback[1] == observed || throw(ArgumentError(
                "affine update callback does not match its callback certificate"))
        end
        push!(kinds, evaluation.kind)
        push!(callback_indices, indices)
        push!(callback_arithmetic_errors, callback_arithmetic_error)
        push!(updates, certify_rounded_affine_update(evaluation.base[1],
            evaluation.scale, computed_callback, callback_error,
            evaluation.computed_update[1]))
    end
    BoundedScalarAffineTraceRationalCertificate(kinds, callback_indices,
        callback_arithmetic_errors, updates)
end

function bounded_scalar_affine_update_certificate_arguments(
        callbacks::BoundedScalarCallbackTraceRationalCertificate,
        affine::BoundedScalarAffineTraceRationalCertificate, index::Integer)
    checkbounds(affine.updates, index)
    indices = affine.callback_indices[index]
    length(indices) in (1, 2) || throw(ArgumentError(
        "bounded scalar affine updates require one or two callback sources"))
    arguments = String[string(length(indices))]
    for callback_index in indices
        push!(arguments, callbacks.kinds[callback_index] === :position ?
            "position" : "momentum")
        append!(arguments, bounded_scalar_callback_certificate_arguments(
            callbacks.certificates[callback_index]))
    end
    push!(arguments, _exact_rational_wire(
        affine.callback_arithmetic_errors[index]))
    append!(arguments,
        rounded_affine_update_certificate_arguments(affine.updates[index]))
    arguments
end

function certify_rounded_contraction_residual(iterate::Real,
        computed_update::Real, update_error::Real)
    exact_iterate = Rational{BigInt}(iterate)
    exact_update = Rational{BigInt}(computed_update)
    error = Rational{BigInt}(update_error)
    error >= 0 || throw(DomainError(update_error,
        "rounded update error must be nonnegative"))
    RoundedContractionResidualRationalCertificate(exact_iterate, exact_update,
        error, abs(exact_iterate - exact_update) + error)
end

rounded_contraction_residual_certificate_arguments(
        certificate::RoundedContractionResidualRationalCertificate) = [
    string(numerator(value), "/", denominator(value))
    for value in (certificate.iterate, certificate.computed_update,
        certificate.update_error, certificate.residual_upper)
]

"""Linked rounded residual and a posteriori contraction-distance budget."""
struct RoundedContractionPairCertificate
    residual::RoundedContractionResidualRationalCertificate
    contraction::AposterioriContractionRationalCertificate
end

function certify_rounded_contraction_pair(iterate::Real,
        computed_update::Real, update_error::Real, rate::Real)
    residual = certify_rounded_contraction_residual(iterate, computed_update,
        update_error)
    contraction = certify_contraction_aposteriori(residual.residual_upper, rate)
    RoundedContractionPairCertificate(residual, contraction)
end

function rounded_contraction_pair_certificate_arguments(
        certificate::RoundedContractionPairCertificate)
    vcat(rounded_contraction_residual_certificate_arguments(certificate.residual),
        [string(numerator(value), "/", denominator(value))
         for value in (certificate.contraction.rate,
             certificate.contraction.distance_upper)])
end

"""Final residual-to-fixed-point records for both bounded scalar implicit
loops, linked to the corresponding fully certified affine updates."""
struct BoundedScalarSolverContractionTraceCertificate
    epsilon::Float64
    half_update_index::Int
    position_update_index::Int
    half::RoundedContractionPairCertificate
    position::RoundedContractionPairCertificate
end

function certify_bounded_scalar_solver_contraction_trace(trace,
        affine::BoundedScalarAffineTraceRationalCertificate, step_size::Real)
    epsilon = Float64(step_size)
    isfinite(epsilon) || throw(DomainError(step_size, "step size must be finite"))
    exact_epsilon = Rational{BigInt}(epsilon)
    half_rate = abs(exact_epsilon / 2) * 3
    position_rate = abs(exact_epsilon / 2) * 2
    half_rate < 1 && position_rate < 1 || throw(DomainError(step_size,
        "bounded scalar fixed-point rates must be below one"))
    half_index = trace.half_iterations + trace.position_iterations + 1
    position_index = half_index + 1
    affine.kinds[half_index] === :half_momentum || throw(ArgumentError(
        "final half residual update is not in the expected trace slot"))
    affine.kinds[position_index] === :position || throw(ArgumentError(
        "final position residual update is not in the expected trace slot"))
    half = certify_rounded_contraction_pair(trace.half_momentum[1],
        trace.half_update[1], affine.updates[half_index].update_error, half_rate)
    position = certify_rounded_contraction_pair(trace.next_position[1],
        trace.position_update[1], affine.updates[position_index].update_error,
        position_rate)
    BoundedScalarSolverContractionTraceCertificate(epsilon, half_index,
        position_index, half, position)
end

function bounded_scalar_solver_contraction_certificate_arguments(
        callbacks::BoundedScalarCallbackTraceRationalCertificate,
        affine::BoundedScalarAffineTraceRationalCertificate,
        solver::BoundedScalarSolverContractionTraceCertificate, kind::Symbol)
    index, pair, tag = kind === :half_momentum ?
        (solver.half_update_index, solver.half, "half") :
        kind === :position ?
        (solver.position_update_index, solver.position, "position") :
        throw(ArgumentError("unknown bounded scalar contraction kind: $kind"))
    vcat(String[tag, _exact_rational_wire(solver.epsilon)],
        bounded_scalar_affine_update_certificate_arguments(
            callbacks, affine, index),
        rounded_contraction_pair_certificate_arguments(pair))
end

"""Linked half-momentum and position fixed-point budgets for one bounded
scalar solver trace. `position_error` includes propagation of half-momentum
error through the exact implicit-position fixed point."""
struct BoundedScalarSolverPhaseTraceCertificate
    solver::BoundedScalarSolverContractionTraceCertificate
    position_error::Rational{BigInt}
end

function certify_bounded_scalar_solver_phase_trace(trace,
        callbacks::BoundedScalarCallbackTraceRationalCertificate,
        affine::BoundedScalarAffineTraceRationalCertificate, step_size::Real)
    solver = certify_bounded_scalar_solver_contraction_trace(trace, affine,
        step_size)
    half_sources = affine.callback_indices[solver.half_update_index]
    position_sources = affine.callback_indices[solver.position_update_index]
    length(half_sources) == 1 || throw(ArgumentError(
        "half residual must have one callback source"))
    length(position_sources) == 2 || throw(ArgumentError(
        "position residual must have two callback sources"))
    half_entry = callbacks.certificates[only(half_sources)]
    first_position_entry = callbacks.certificates[first(position_sources)]
    affine.updates[solver.position_update_index].base ==
        half_entry.sincos.input || throw(ArgumentError(
            "implicit phases do not share the same initial position"))
    first_position_entry.momentum == solver.half.residual.iterate ||
        throw(ArgumentError(
            "position phase does not consume the returned half momentum"))
    epsilon = Rational{BigInt}(solver.epsilon)
    position_rate = abs(epsilon / 2) * 2
    sensitivity = (2 * abs(epsilon / 2) * 9 *
        solver.half.contraction.distance_upper) / (1 - position_rate)
    BoundedScalarSolverPhaseTraceCertificate(solver,
        solver.position.contraction.distance_upper + sensitivity)
end

function bounded_scalar_solver_phase_certificate_arguments(
        callbacks::BoundedScalarCallbackTraceRationalCertificate,
        affine::BoundedScalarAffineTraceRationalCertificate,
        certificate::BoundedScalarSolverPhaseTraceCertificate)
    half = bounded_scalar_solver_contraction_certificate_arguments(callbacks,
        affine, certificate.solver, :half_momentum)
    position = bounded_scalar_solver_contraction_certificate_arguments(callbacks,
        affine, certificate.solver, :position)
    vcat(String[string(length(half))], half,
        String[string(length(position))], position,
        String[_exact_rational_wire(certificate.position_error)])
end

"""Complete bounded scalar endpoint error, including the final explicit
momentum kick and the product-metric phase radius."""
struct BoundedScalarSolverEndpointTraceCertificate
    phase::BoundedScalarSolverPhaseTraceCertificate
    final_update_index::Int
    final_momentum_error::Rational{BigInt}
    phase_error::Rational{BigInt}
end

function certify_bounded_scalar_solver_endpoint_trace(trace,
        callbacks::BoundedScalarCallbackTraceRationalCertificate,
        affine::BoundedScalarAffineTraceRationalCertificate, step_size::Real)
    phase = certify_bounded_scalar_solver_phase_trace(trace, callbacks, affine,
        step_size)
    final_index = phase.solver.position_update_index + 1
    affine.kinds[final_index] === :final_momentum || throw(ArgumentError(
        "final momentum update is not in the expected trace slot"))
    sources = affine.callback_indices[final_index]
    length(sources) == 1 || throw(ArgumentError(
        "final momentum update must have one callback source"))
    final_callback = callbacks.certificates[only(sources)]
    final_callback.sincos.input == phase.solver.position.residual.iterate ||
        throw(ArgumentError(
            "final kick position does not match the returned position"))
    final_callback.momentum == phase.solver.half.residual.iterate ||
        throw(ArgumentError(
            "final kick momentum does not match the returned half momentum"))
    update = affine.updates[final_index]
    update.base == phase.solver.half.residual.iterate || throw(ArgumentError(
        "final kick base does not match the returned half momentum"))
    epsilon = Rational{BigInt}(phase.solver.epsilon)
    update.scale == -(epsilon / 2) || throw(ArgumentError(
        "final kick scale does not match the solver step size"))
    half_error = phase.solver.half.contraction.distance_upper
    rounded_half = phase.solver.half.residual.iterate
    position_rate = 18 * (abs(rounded_half) + half_error)^2 +
        3 * (abs(rounded_half) + half_error)
    final_error = update.update_error +
        (1 + abs(epsilon / 2) * 3) * half_error +
        abs(epsilon / 2) * position_rate * phase.position_error
    BoundedScalarSolverEndpointTraceCertificate(phase, final_index,
        final_error, max(phase.position_error, final_error))
end

function bounded_scalar_solver_endpoint_certificate_arguments(
        callbacks::BoundedScalarCallbackTraceRationalCertificate,
        affine::BoundedScalarAffineTraceRationalCertificate,
        certificate::BoundedScalarSolverEndpointTraceCertificate)
    phase = bounded_scalar_solver_phase_certificate_arguments(callbacks,
        affine, certificate.phase)
    final_update = bounded_scalar_affine_update_certificate_arguments(callbacks,
        affine, certificate.final_update_index)
    vcat(String[string(length(phase))], phase,
        String[string(length(final_update))], final_update,
        String[_exact_rational_wire(certificate.final_momentum_error),
            _exact_rational_wire(certificate.phase_error)])
end

"""A nonempty sequence of bounded implicit-solver records with exact
Float64-as-rational state threading between consecutive rounded steps."""
struct BoundedScalarLinkedSolverTrajectoryTraceCertificate
    epsilon::Rational{BigInt}
    initial_position::Rational{BigInt}
    initial_momentum::Rational{BigInt}
    steps::Vector{BoundedScalarSolverEndpointTraceCertificate}
end

function certify_bounded_scalar_linked_solver_trajectory(
        initial_position::Real, initial_momentum::Real,
        traces::AbstractVector,
        callbacks::AbstractVector{<:BoundedScalarCallbackTraceRationalCertificate},
        affine::AbstractVector{<:BoundedScalarAffineTraceRationalCertificate},
        step_size::Real)
    count = length(traces)
    count > 0 || throw(ArgumentError("bounded solver trajectory cannot be empty"))
    length(callbacks) == count && length(affine) == count ||
        throw(DimensionMismatch("bounded solver trajectory records"))
    position = Rational{BigInt}(initial_position)
    momentum = Rational{BigInt}(initial_momentum)
    steps = BoundedScalarSolverEndpointTraceCertificate[]
    for index in eachindex(traces)
        endpoint = certify_bounded_scalar_solver_endpoint_trace(traces[index],
            callbacks[index], affine[index], step_size)
        half_sources = affine[index].callback_indices[
            endpoint.phase.solver.half_update_index]
        length(half_sources) == 1 || throw(ArgumentError(
            "half-momentum residual must have one callback source"))
        entry = callbacks[index].certificates[only(half_sources)]
        entry.sincos.input == position || throw(ArgumentError(
            "bounded solver step does not consume the preceding position"))
        affine[index].updates[endpoint.phase.solver.half_update_index].base ==
            momentum || throw(ArgumentError(
            "bounded solver step does not consume the preceding momentum"))
        push!(steps, endpoint)
        position = endpoint.phase.solver.position.residual.iterate
        momentum = affine[index].updates[endpoint.final_update_index].computed_update
    end
    BoundedScalarLinkedSolverTrajectoryTraceCertificate(
        Rational{BigInt}(step_size), Rational{BigInt}(initial_position),
        Rational{BigInt}(initial_momentum), steps)
end

function bounded_scalar_linked_solver_trajectory_certificate_arguments(
        callbacks::AbstractVector{<:BoundedScalarCallbackTraceRationalCertificate},
        affine::AbstractVector{<:BoundedScalarAffineTraceRationalCertificate},
        certificate::BoundedScalarLinkedSolverTrajectoryTraceCertificate)
    count = length(certificate.steps)
    length(callbacks) == count && length(affine) == count ||
        throw(DimensionMismatch("bounded solver trajectory records"))
    fields = String[_exact_rational_wire(certificate.epsilon),
        _exact_rational_wire(certificate.initial_position),
        _exact_rational_wire(certificate.initial_momentum), string(count)]
    for index in eachindex(certificate.steps)
        step = bounded_scalar_solver_endpoint_certificate_arguments(
            callbacks[index], affine[index], certificate.steps[index])
        push!(fields, string(length(step)))
        append!(fields, step)
    end
    fields
end

"""Rational regional sensitivity coefficients for the exact bounded GR step."""
struct BoundedScalarStepRegionalRationalCertificate
    epsilon::Rational{BigInt}
    half_momentum_bound::Rational{BigInt}
    force_position_rate::Rational{BigInt}
    half_coefficient::Rational{BigInt}
    position_coefficient::Rational{BigInt}
    momentum_coefficient::Rational{BigInt}
    lipschitz_upper::Rational{BigInt}
end

function certify_bounded_scalar_step_regional(step_size::Real,
        half_momentum_bound::Real)
    epsilon = Rational{BigInt}(step_size)
    bound = Rational{BigInt}(half_momentum_bound)
    bound >= 0 || throw(DomainError(half_momentum_bound,
        "half-momentum bound must be nonnegative"))
    a = abs(epsilon / 2)
    3a < 1 || throw(DomainError(step_size,
        "bounded scalar half-momentum contraction rate must be below one"))
    force_rate = 18bound^2 + 3bound
    half = (1 + a * force_rate) / (1 - 3a)
    position = ((1 + 2a) + 2a * 9half) / (1 - 2a)
    momentum = (1 + 3a) * half + a * force_rate * position
    BoundedScalarStepRegionalRationalCertificate(epsilon, bound, force_rate,
        half, position, momentum, max(position, momentum))
end

bounded_scalar_step_regional_certificate_arguments(
        certificate::BoundedScalarStepRegionalRationalCertificate) =
    String[_exact_rational_wire(value) for value in (certificate.epsilon,
        certificate.half_momentum_bound, certificate.force_position_rate,
        certificate.half_coefficient, certificate.position_coefficient,
        certificate.momentum_coefficient, certificate.lipschitz_upper)]

"""Bounded Hamiltonian evaluation transported from the rounded solver endpoint
to the exact endpoint constructed by the linked solver certificate."""
struct BoundedScalarEndpointEnergyTraceCertificate
    solver::BoundedScalarSolverEndpointTraceCertificate
    evaluation::BoundedScalarCallbackRationalCertificate
    total_energy_error::Rational{BigInt}
end

function certify_bounded_scalar_endpoint_energy_trace(trace,
        callbacks::BoundedScalarCallbackTraceRationalCertificate,
        affine::BoundedScalarAffineTraceRationalCertificate, step_size::Real)
    solver = certify_bounded_scalar_solver_endpoint_trace(trace, callbacks,
        affine, step_size)
    q = solver.phase.solver.position.residual.iterate
    p = affine.updates[solver.final_update_index].computed_update
    evaluation = certify_bounded_scalar_callbacks(q, p)
    sqrt_error = _bounded_scalar_sqrt_error(evaluation)
    final_error = solver.final_momentum_error
    position_error = solver.phase.position_error
    total = sqrt_error + 3 * final_error +
        (abs(p) + final_error) * position_error
    BoundedScalarEndpointEnergyTraceCertificate(solver, evaluation, total)
end

"""The linked initial and final energies of one bounded generalized-leapfrog
step, with the common radius consumed by stabilized multinomial selection."""
struct BoundedScalarTwoEndpointEnergyTraceCertificate
    initial::BoundedScalarCallbackRationalCertificate
    final::BoundedScalarEndpointEnergyTraceCertificate
    common_error::Rational{BigInt}
end

function certify_bounded_scalar_two_endpoint_energy_trace(trace,
        callbacks::BoundedScalarCallbackTraceRationalCertificate,
        affine::BoundedScalarAffineTraceRationalCertificate, step_size::Real)
    final = certify_bounded_scalar_endpoint_energy_trace(trace, callbacks,
        affine, step_size)
    half_index = final.solver.phase.solver.half_update_index
    sources = affine.callback_indices[half_index]
    length(sources) == 1 || throw(ArgumentError(
        "initial half-momentum update must have one callback source"))
    source = callbacks.certificates[only(sources)]
    initial_position = source.sincos.input
    initial_momentum = affine.updates[half_index].base
    initial = certify_bounded_scalar_callbacks(initial_position,
        initial_momentum)
    common = max(_bounded_scalar_sqrt_error(initial),
        final.total_energy_error)
    BoundedScalarTwoEndpointEnergyTraceCertificate(initial, final, common)
end

function bounded_scalar_two_endpoint_energy_certificate_arguments(
        callbacks::BoundedScalarCallbackTraceRationalCertificate,
        affine::BoundedScalarAffineTraceRationalCertificate,
        certificate::BoundedScalarTwoEndpointEnergyTraceCertificate)
    initial = bounded_scalar_callback_certificate_arguments(certificate.initial)
    final = bounded_scalar_endpoint_energy_certificate_arguments(callbacks,
        affine, certificate.final)
    vcat(initial, final, String[_exact_rational_wire(certificate.common_error)])
end

"""Checked maximum-stabilized exponentials for the two linked energies."""
struct BoundedScalarTwoEndpointWeightTraceCertificate
    energy::BoundedScalarTwoEndpointEnergyTraceCertificate
    weights::Vector{ExpNonpositiveTransportRationalCertificate}
end

function certify_bounded_scalar_two_endpoint_weights(
        energy::BoundedScalarTwoEndpointEnergyTraceCertificate)
    computed = Float64[energy.initial.sqrt_certificate.computed,
        energy.final.evaluation.sqrt_certificate.computed]
    exact = Rational{BigInt}.(computed)
    exact_arguments = .-exact .- maximum(.-exact)
    computed_arguments = .-computed .- maximum(.-computed)
    weights = [certify_exp_nonpositive_transport(computed_arguments[i],
        exact_arguments[i]) for i in eachindex(computed)]
    BoundedScalarTwoEndpointWeightTraceCertificate(energy, weights)
end

function bounded_scalar_two_endpoint_weight_certificate_arguments(
        callbacks::BoundedScalarCallbackTraceRationalCertificate,
        affine::BoundedScalarAffineTraceRationalCertificate,
        certificate::BoundedScalarTwoEndpointWeightTraceCertificate)
    length(certificate.weights) == 2 || throw(ArgumentError(
        "bounded two-endpoint weight certificate must contain two weights"))
    energy = bounded_scalar_two_endpoint_energy_certificate_arguments(
        callbacks, affine, certificate.energy)
    fields = String[string(length(energy))]
    append!(fields, energy)
    for weight in certificate.weights
        append!(fields, exp_nonpositive_transport_certificate_arguments(weight))
    end
    fields
end

"""The complete observed Float64 arithmetic and stable decision for one
linked two-endpoint bounded multinomial trajectory."""
struct BoundedScalarTwoEndpointSelectionTraceCertificate
    weights::BoundedScalarTwoEndpointWeightTraceCertificate
    cumulative::RoundedCumulativeRationalCertificate
    draw::ScaledDrawRationalCertificate
    common_weight_error::Rational{BigInt}
    boundary_error::Rational{BigInt}
    uniform_error::Rational{BigInt}
    decision::MultinomialDecisionRationalCertificate
end

function certify_bounded_scalar_two_endpoint_selection(
        energy::BoundedScalarTwoEndpointEnergyTraceCertificate,
        uniform::Real)
    weights = certify_bounded_scalar_two_endpoint_weights(energy)
    computed_weights =
        [weight.local_certificate.computed for weight in weights.weights]
    cumulative = certify_rounded_cumulative(computed_weights)
    draw = certify_scaled_draw(uniform, cumulative.boundaries[end])
    common_weight_error = maximum(weight.local_certificate.error +
        weight.input_error for weight in weights.weights)
    propagated = 2 * (common_weight_error + 2 * energy.common_error)
    boundary_error = maximum(cumulative.errors) + propagated
    uniform_error = draw.error + abs(Rational{BigInt}(draw.uniform)) *
        (cumulative.errors[end] + propagated)
    decision = certify_multinomial_decision(draw.computed,
        cumulative.boundaries, uniform_error, boundary_error)
    BoundedScalarTwoEndpointSelectionTraceCertificate(weights, cumulative,
        draw, common_weight_error, boundary_error, uniform_error, decision)
end

function bounded_scalar_endpoint_energy_certificate_arguments(
        callbacks::BoundedScalarCallbackTraceRationalCertificate,
        affine::BoundedScalarAffineTraceRationalCertificate,
        certificate::BoundedScalarEndpointEnergyTraceCertificate)
    solver = bounded_scalar_solver_endpoint_certificate_arguments(callbacks,
        affine, certificate.solver)
    evaluation = bounded_scalar_callback_certificate_arguments(
        certificate.evaluation)
    vcat(String[string(length(solver))], solver, evaluation,
        String[_exact_rational_wire(certificate.total_energy_error)])
end

certify_positive_softabs_endpoint_state_transport(
        endpoint::PositiveSoftAbsHamiltonianErrorUpperCertificate,
        solver::RoundedContractionPairCertificate, energy_lipschitz::Real) =
    certify_positive_softabs_endpoint_state_transport(endpoint,
        solver.contraction.distance_upper, energy_lipschitz)

function contraction_error_bound(computed_residual::Real,
        residual_error::Real, rate::Real; precision::Integer=256)
    isfinite(computed_residual) || throw(DomainError(computed_residual,
        "computed residual must be finite"))
    setprecision(BigFloat, precision) do
        error = BigFloat(residual_error)
        contraction_rate = BigFloat(rate)
        error >= 0 || throw(DomainError(residual_error,
            "residual error must be nonnegative"))
        0 <= contraction_rate < 1 || throw(DomainError(rate,
            "contraction rate must lie in [0, 1)"))
        residual = Float64(computed_residual)
        bound = (abs(BigFloat(residual)) + error) / (1 - contraction_rate)
        ContractionErrorBound(residual, error, contraction_rate, bound)
    end
end

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
