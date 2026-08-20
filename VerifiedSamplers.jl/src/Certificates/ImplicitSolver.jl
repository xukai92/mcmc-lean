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
