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
