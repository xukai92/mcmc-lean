module Reference

using LinearAlgebra

using ..Runtime: AbstractRandomSource, draw_below!, standard_normal!,
    uniform_unit!, checked_positive_float, checked_positive_count,
    checked_finite_float, FloatTraceEvent, FloatTraceSource
using ..Certificates: ImplicitSolveCertificate, certify_implicit_solve,
    certifies_exact_solver

export categorical_index!, integer_slice_step!, bounded_slice_step!, stepping_out_slice_step!, sheared_birth_death_step!, spatial_birth_death_step!, finite_mh_step!, two_state_mh_step!, gaussian_rwmh_step!, scalar_barker_rwmh_step!, scalar_mala_step!, vector_mala_step!, dense_pmala_step!, scalar_hmc_step!, vector_hmc_step!, metric_hmc_step!, multinomial_hmc_step!, metric_multinomial_hmc_step!, categorical_dhmc_step!,
    finite_hmm_particle_gibbs_step!,
    relativistic_multinomial_hmc_step!,
    fixed_point_generalized_leapfrog,
    fixed_point_generalized_leapfrog_trace,
    FixedPointGeneralizedLeapfrogTrace,
    vector_leapfrog_step, vector_gauss_legendre_step,
    vector_gauss_legendre_hmc_step!,
    affine_prefix_scan, speculative_trajectory, certified_trajectory,
    certified_speculative_trajectory,
    classical_rmhmc_step!,
    approximate_classical_rmhmc_step!,
    dense_rmhmc_step!, random_sketch_rmhmc_step!,
    certified_relativistic_multinomial_hmc_step!,
    dynamic_select_float!, streaming_eligible_select!, recursive_doubling_rows,
    NUTSTreeLeaf, NUTSTreeNode, NUTSSubtreeResult, build_nuts_phase_tree,
    NUTSOuterResult, interpret_nuts_subtree, interpret_nuts_directional_subtree,
    interpret_nuts_outer_trace, select_nuts_candidate, interpret_nuts_transition,
    interpret_checked_nuts_rows, checked_nuts_or_identity_select!,
    coupled_multinomial_hmc_step!, coupled_gaussian_rwmh_step!, xu21_coupled_step!,
    IR_FORMAT_VERSION, artifact_facets

const IR_FORMAT_VERSION = 27

function affine_prefix_scan(segments::AbstractVector{<:Tuple})
    result = collect(segments)
    for index in 2:length(result)
        later, earlier = segments[index], result[index - 1]
        result[index] = (later[1] * earlier[1],
            later[1] * earlier[2] + later[2])
    end
    result
end

function certified_trajectory(step, initial, candidate::AbstractVector)
    current = initial
    for proposed in candidate
        expected = step(current)
        proposed == expected || return foldl((x, _) -> step(x), candidate;
            init=initial), false
        current = proposed
    end
    current, true
end

"""Jacobi-style parallel recurrence approximation with explicit pass count."""
function speculative_trajectory(step, initial, length::Integer, passes::Integer)
    length >= 0 || throw(ArgumentError("trajectory length must be nonnegative"))
    passes >= 0 || throw(ArgumentError("pass count must be nonnegative"))
    current = fill(initial, length)
    for _ in 1:passes
        previous = current
        current = similar(previous)
        for index in eachindex(current)
            parent = index == firstindex(current) ? initial : previous[index - 1]
            current[index] = step(parent)
        end
    end
    current
end

function certified_speculative_trajectory(step, initial, length::Integer,
        passes::Integer)
    candidate = speculative_trajectory(step, initial, length, passes)
    certified_trajectory(step, initial, candidate)
end

"""Execute one instance of the Lean IR `vector-leapfrog` primitive."""
function vector_leapfrog_step(gradient, step_size::Real,
        initial_position::AbstractVector{<:Real},
        initial_momentum::AbstractVector{<:Real})
    position = Float64.(initial_position)
    momentum = Float64.(initial_momentum)
    length(position) == length(momentum) ||
        throw(DimensionMismatch("position and momentum dimensions differ"))
    ε = Float64(step_size)
    isfinite(ε) || throw(ArgumentError("step size must be finite"))
    half_momentum = momentum .- (ε / 2) .* gradient(position)
    position = position .+ ε .* half_momentum
    momentum = half_momentum .- (ε / 2) .* gradient(position)
    all(isfinite, position) && all(isfinite, momentum) ||
        throw(DomainError((position, momentum), "leapfrog state must be finite"))
    position, momentum
end

"""Allocation-transparent interpretation of one two-stage Gauss--Legendre step.

The fixed iteration count is part of the serialized algorithm. The exact Lean
geometric theorem applies when the returned stages satisfy the collocation
equations; finite residuals are exposed to tests rather than hidden.
"""
function vector_gauss_legendre_step(gradient, step_size::Real,
        iterations::Integer, position::AbstractVector{<:Real},
        momentum::AbstractVector{<:Real})
    length(position) == length(momentum) || throw(DimensionMismatch("phase state"))
    iterations > 0 || throw(ArgumentError("stage iterations must be positive"))
    q, p = Float64.(position), Float64.(momentum)
    field(state) = begin
        n = length(q)
        sq, sp = @view(state[1:n]), @view(state[(n + 1):(2n)])
        vcat(sp, -Float64.(gradient(sq)))
    end
    z = vcat(q, p)
    k1 = field(z)
    k2 = copy(k1)
    radius = sqrt(3.0) / 6.0
    a11, a12, a21, a22 = 0.25, 0.25 - radius, 0.25 + radius, 0.25
    for _ in 1:iterations
        next1 = field(z .+ step_size .* (a11 .* k1 .+ a12 .* k2))
        next2 = field(z .+ step_size .* (a21 .* k1 .+ a22 .* k2))
        k1, k2 = next1, next2
    end
    next = z .+ (step_size / 2) .* (k1 .+ k2)
    (next[1:length(q)], next[(length(q) + 1):end])
end

function _vector_gauss_legendre_n(gradient, step_size, steps, iterations,
        position, momentum)
    q, p = Float64.(position), Float64.(momentum)
    for _ in 1:steps
        q, p = vector_gauss_legendre_step(gradient, step_size, iterations, q, p)
    end
    q, p
end

"""Stable target-weighted selection from a supplied candidate index set.

The surrounding checked-tree layer is responsible for reroot certification.
"""
function dynamic_select_float!(source::AbstractRandomSource,
        candidates::AbstractVector{<:Integer},
        logweights::AbstractVector{<:Real})
    isempty(candidates) && throw(ArgumentError("candidate set cannot be empty"))
    length(candidates) == length(logweights) ||
        throw(DimensionMismatch("candidate indices and weights must match"))
    values = Float64.(logweights)
    all(isfinite, values) || throw(DomainError(logweights,
        "dynamic target log weights must be finite"))
    offset = maximum(values)
    weights = exp.(values .- offset)
    target = uniform_unit!(source) * sum(weights)
    cumulative = 0.0
    for index in eachindex(weights)
        cumulative += weights[index]
        target < cumulative && return Int(candidates[index])
    end
    Int(last(candidates))
end

"""Interpret the generated eligible-count streaming selection policy.

Each segment is an already filtered completed subtree. A local uniform
representative is drawn and then merged with the accumulated representative
in proportion to the two eligible counts. Empty segments consume no draws.
The result is `nothing` exactly when every segment is empty.
"""
function streaming_eligible_select!(source::AbstractRandomSource,
        segments::AbstractVector{<:AbstractVector{<:Integer}})
    representative = nothing
    total = 0
    for segment in segments
        count = length(segment)
        count == 0 && continue
        local_index = Int(draw_below!(source, count)) + 1
        local_representative = Int(segment[local_index])
        if total == 0
            representative = local_representative
        else
            ticket = Int(draw_below!(source, total + count))
            ticket >= total && (representative = local_representative)
        end
        total += count
    end
    representative
end

"""Direct interpreter for the generated recursive-doubling row builder.

Indices in the returned rows are Julia's one-based counterpart of the Lean
builder's `Fin count` indices. Global reroot certification remains a separate
operation so rejected diagnostic rows stay observable.
"""
function recursive_doubling_rows(
        positions::AbstractVector{<:AbstractVector{<:Real}},
        momenta::AbstractVector{<:AbstractVector{<:Real}},
        directions::AbstractVector{Bool})
    length(positions) == length(momenta) ||
        throw(DimensionMismatch("position and momentum trajectories must match"))
    isempty(positions) && throw(ArgumentError("trajectory cannot be empty"))
    dimension = length(first(positions))
    dimension > 0 || throw(ArgumentError("phase-space dimension cannot be zero"))
    all(point -> length(point) == dimension, positions) &&
        all(point -> length(point) == dimension, momenta) ||
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
        for depth in eachindex(directions)
            width = 1 << (depth - 1)
            grow_right = directions[depth]
            proposed_left = grow_right ? left : left - width
            proposed_right = grow_right ? right + width : right
            proposed_left >= 1 && proposed_right <= count || break
            new_left = grow_right ? right + 1 : proposed_left
            new_right = grow_right ? proposed_right : left - 1
            (subtree_turns(new_left, new_right) ||
                turns(proposed_left, proposed_right)) && break
            left, right = proposed_left, proposed_right
        end
        rows[root] = collect(left:right)
    end
    rows
end

recursive_doubling_rows(positions::AbstractVector{<:Real},
        momenta::AbstractVector{<:Real}, directions::AbstractVector{Bool}) =
    recursive_doubling_rows([[Float64(value)] for value in positions],
        [[Float64(value)] for value in momenta], directions)

"""Reference coordinate-wise DHMC update for a categorical law on a cycle.

This is the all-discontinuous, one-coordinate specialization of Algorithm 1
of Nishimura, Dunson, and Lu.  Taking `epsilon = mass` moves exactly one
category per coordinate update.  The refreshed Laplace kinetic energy is
Exponential(1); crossing spends the exact potential jump and rejection
reflects the momentum direction.
"""
function categorical_dhmc_step!(source::AbstractRandomSource,
        probabilities::AbstractVector{<:Real}, steps::Integer,
        current::Integer)
    length(probabilities) >= 2 ||
        throw(ArgumentError("DHMC needs at least two categories"))
    all(x -> isfinite(x) && x > 0, probabilities) ||
        throw(ArgumentError("category probabilities must be finite and positive"))
    steps > 0 || throw(ArgumentError("trajectory length must be positive"))
    1 <= current <= length(probabilities) ||
        throw(ArgumentError("current category is out of range"))

    forward = uniform_unit!(source) < 0.5
    kinetic = -log1p(-uniform_unit!(source))
    state = Int(current)
    for _ in 1:steps
        candidate = forward ? mod1(state + 1, length(probabilities)) :
            mod1(state - 1, length(probabilities))
        jump = log(Float64(probabilities[state])) -
            log(Float64(probabilities[candidate]))
        if jump < kinetic
            state = candidate
            kinetic -= jump
        else
            forward = !forward
        end
    end
    state
end

"""Exact integer under-the-graph slice update on zero-based state indices."""
function integer_slice_step!(source::AbstractRandomSource,
        weights::AbstractVector{<:Integer}, current::Integer)
    isempty(weights) && throw(ArgumentError("slice weights cannot be empty"))
    all(>(0), weights) || throw(ArgumentError("slice weights must be positive"))
    0 <= current < length(weights) || throw(ArgumentError("current state is out of range"))
    height = draw_below!(source, weights[current + 1])
    candidates = findall(weight -> weight > height, weights)
    selected = Int(draw_below!(source, length(candidates))) + 1
    candidates[selected] - 1
end

"""Reference rejection implementation of exact slice selection on a bounded interval."""
function bounded_slice_step!(source::AbstractRandomSource, logdensity,
        lower::Real, upper::Real, current::Real, max_attempts::Integer)
    lo, hi, x = Float64(lower), Float64(upper), Float64(current)
    isfinite(lo) && isfinite(hi) && lo < hi ||
        throw(ArgumentError("slice bounds must be finite and ordered"))
    lo <= x <= hi || throw(ArgumentError("current state is outside slice bounds"))
    max_attempts > 0 || throw(ArgumentError("max_attempts must be positive"))
    current_logdensity = Float64(logdensity(x))
    isfinite(current_logdensity) ||
        throw(ArgumentError("current log density must be finite"))
    logheight = current_logdensity + log(uniform_unit!(source))
    for _ in 1:max_attempts
        proposal = lo + (hi - lo) * uniform_unit!(source)
        proposed_logdensity = Float64(logdensity(proposal))
        (isfinite(proposed_logdensity) || proposed_logdensity == -Inf) ||
            throw(ArgumentError("log density must be finite or -Inf"))
        proposed_logdensity >= logheight && return proposal
    end
    throw(ErrorException("bounded slice rejection exceeded max_attempts"))
end

"""Reference stepping-out and shrinkage slice update on the real line."""
function stepping_out_slice_step!(source::AbstractRandomSource, logdensity,
        width::Real, current::Real, max_steps::Integer, max_shrink::Integer;
        threshold_observer=(base, uniform, log_uniform, threshold) -> nothing,
        comparison_observer=(kind, position, value, threshold) -> nothing)
    w, x = Float64(width), Float64(current)
    isfinite(w) && w > 0 || throw(ArgumentError("width must be finite and positive"))
    isfinite(x) || throw(ArgumentError("current state must be finite"))
    max_steps >= 0 || throw(ArgumentError("max_steps must be nonnegative"))
    max_shrink > 0 || throw(ArgumentError("max_shrink must be positive"))
    base = Float64(logdensity(x))
    isfinite(base) || throw(ArgumentError("current log density must be finite"))
    uniform = uniform_unit!(source)
    log_uniform = log(uniform)
    threshold = base + log_uniform
    threshold_observer(base, uniform, log_uniform, threshold)
    left = x - w * uniform_unit!(source)
    right = left + w
    left_steps = Int(floor(uniform_unit!(source) * (max_steps + 1)))
    right_steps = max_steps - left_steps
    while left_steps > 0
        value = Float64(logdensity(left))
        (isfinite(value) || value == -Inf) ||
            throw(ArgumentError("log density must be finite or -Inf"))
        comparison_observer(:stopBelow, left, value, threshold)
        value <= threshold && break
        left -= w
        left_steps -= 1
    end
    while right_steps > 0
        value = Float64(logdensity(right))
        (isfinite(value) || value == -Inf) ||
            throw(ArgumentError("log density must be finite or -Inf"))
        comparison_observer(:stopBelow, right, value, threshold)
        value <= threshold && break
        right += w
        right_steps -= 1
    end
    for _ in 1:max_shrink
        proposal = left + (right - left) * uniform_unit!(source)
        value = Float64(logdensity(proposal))
        (isfinite(value) || value == -Inf) ||
            throw(ArgumentError("log density must be finite or -Inf"))
        comparison_observer(:acceptAbove, proposal, value, threshold)
        value >= threshold && return proposal
        proposal < x ? (left = proposal) : (right = proposal)
    end
    # Total checked fallback: exhausting the shrinkage-attempt budget leaves
    # the chain at its current state. Exhausting a replay source itself remains
    # a malformed-trace error.
    x
end

"""Reference nonlinear reversible-jump birth/death update.

`nothing` denotes the zero-dimensional model. A birth draws the proved
uniform auxiliary pair and applies `(u₁,u₂) ↦ (2u₁+8u₂³,2u₂)`;
a death deterministically returns to `nothing`. The formal density correction
makes both directions accept with probability one.
"""
function sheared_birth_death_step!(source::AbstractRandomSource, current)
    current === nothing || current isa Tuple{<:Real,<:Real} ||
        throw(ArgumentError("RJ state must be nothing or a pair of reals"))
    current === nothing || return nothing
    u1 = 2.0 * uniform_unit!(source) - 1.0
    u2 = 2.0 * uniform_unit!(source) - 1.0
    (2.0 * u1 + 8.0 * u2^3, 2.0 * u2)
end

"""Reference three-dimensional product-scaled birth/death update."""
function spatial_birth_death_step!(source::AbstractRandomSource, current)
    current === nothing ||
        (current isa Tuple && length(current) == 3 && all(x -> x isa Real, current)) ||
        throw(ArgumentError("spatial RJ state must be nothing or three reals"))
    current === nothing || return nothing
    ntuple(_ -> 4.0 * uniform_unit!(source) - 2.0, 3)
end

include("Artifact.jl")

function checked_logdensity(callback, state)
    value = callback(state)
    value isa Real || throw(ArgumentError("logdensity must return a real scalar"))
    converted = Float64(value)
    isfinite(converted) || throw(DomainError(value, "logdensity must be finite"))
    converted
end

function checked_gradient(callback, state::Real)
    value = callback(state)
    value isa Real || throw(ArgumentError("scalar gradient must return a real scalar"))
    converted = Float64(value)
    isfinite(converted) || throw(DomainError(value, "gradient must be finite"))
    converted
end


function checked_gradient(callback, state::AbstractVector)
    value = callback(state)
    value isa AbstractVector ||
        throw(ArgumentError("vector gradient must return a vector"))
    length(value) == length(state) || throw(DimensionMismatch("gradient dimension"))
    converted = Float64.(value)
    all(isfinite, converted) || throw(DomainError(value, "gradient must be finite"))
    converted
end

function eval_expr(raw, env::Dict{String,Any})
    node = items(aslist(raw))
    tag = atom(node[1])
    tag == "var" && return env[atom(node[3])]
    tag == "nat" && return parse(BigInt, atom(node[2]))
    tag == "real" && return parse(Float64, atom(node[2]))
    tag == "vector" && return BigInt[parse(BigInt, atom(value)) for value in node[2:end]]
    if tag == "matrix"
        return [BigInt[parse(BigInt, atom(value)) for value in items(aslist(row))[2:end]]
            for row in node[2:end]]
    end
    tag == "add" && return eval_expr(node[2], env) + eval_expr(node[3], env)
    tag == "sub" && return max(BigInt(0), eval_expr(node[2], env) - eval_expr(node[3], env))
    tag == "sub-real" && return eval_expr(node[2], env) - eval_expr(node[3], env)
    tag == "mul" && return eval_expr(node[2], env) * eval_expr(node[3], env)
    tag == "div-real" && return eval_expr(node[2], env) / eval_expr(node[3], env)
    tag == "exp" && return exp(eval_expr(node[2], env))
    tag == "min" && return min(eval_expr(node[2], env), eval_expr(node[3], env))
    tag == "length" && return BigInt(length(eval_expr(node[2], env)))
    tag == "row-count" && return BigInt(length(eval_expr(node[2], env)))
    tag == "total" && return sum(eval_expr(node[2], env); init=BigInt(0))
    tag == "index" && return eval_expr(node[2], env)[Int(eval_expr(node[3], env)) + 1]
    tag == "row-at" && return eval_expr(node[2], env)[Int(eval_expr(node[3], env)) + 1]
    tag == "lt" && return eval_expr(node[2], env) < eval_expr(node[3], env)
    tag == "le" && return eval_expr(node[2], env) <= eval_expr(node[3], env)
    tag == "eq" && return eval_expr(node[2], env) == eval_expr(node[3], env)
    tag == "and" && return eval_expr(node[2], env) && eval_expr(node[3], env)
    tag == "all-nonnegative" && return all(>=(0), eval_expr(node[2], env))
    tag == "all-positive" && return all(>(0), eval_expr(node[2], env))
    if tag == "all-rows-length"
        size = eval_expr(node[3], env)
        return all(row -> length(row) == size, eval_expr(node[2], env))
    end
    if tag == "all-rows-nonnegative-positive"
        return all(row -> all(>=(0), row) && sum(row; init=BigInt(0)) > 0,
            eval_expr(node[2], env))
    end
    tag == "to-exact-vector" && return BigInt.(eval_expr(node[2], env))
    tag == "to-exact-matrix" && return [BigInt.(row) for row in eval_expr(node[2], env)]
    tag == "log-density" && return env["logdensity"](eval_expr(node[2], env))
    tag == "gradient" && return env["gradient"](eval_expr(node[2], env))
    tag == "vector-log-density" && return env["logdensity"](eval_expr(node[2], env))
    tag == "vector-gradient" && return env["gradient"](eval_expr(node[2], env))
    tag == "squared-norm" && return sum(abs2, eval_expr(node[2], env); init=0.0)
    tag == "vector-add-scaled" && return eval_expr(node[2], env) .+
        eval_expr(node[3], env) .* eval_expr(node[4], env)
    tag == "vector-sub" && return eval_expr(node[2], env) .- eval_expr(node[3], env)
    if tag == "leapfrog-position" || tag == "leapfrog-momentum"
        step_size = Float64(eval_expr(node[2], env))
        steps = Int(eval_expr(node[3], env))
        position = Float64(eval_expr(node[4], env))
        momentum = Float64(eval_expr(node[5], env))
        for _ in 1:steps
            half_momentum = momentum - step_size * env["gradient"](position) / 2
            position += step_size * half_momentum
            momentum = half_momentum - step_size * env["gradient"](position) / 2
        end
        return tag == "leapfrog-position" ? position : momentum
    end
    if tag == "dense-pmala"
        return _dense_pmala_step!(eval_expr(node[2], env), env["logdensity"],
            env["gradient"], env["metric"], env["metric_derivative"],
            Float64(eval_expr(node[3], env)), eval_expr(node[4], env))
    end
    if tag == "vector-leapfrog-position" || tag == "vector-leapfrog-momentum"
        step_size = Float64(eval_expr(node[2], env))
        steps = Int(eval_expr(node[3], env))
        position = Float64.(eval_expr(node[4], env))
        momentum = Float64.(eval_expr(node[5], env))
        for _ in 1:steps
            position, momentum = vector_leapfrog_step(
                env["gradient"], step_size, position, momentum)
        end
        return tag == "vector-leapfrog-position" ? position : momentum
    end
    if tag == "metric-hmc"
        kind = Symbol(atom(node[2]))
        source = eval_expr(node[3], env)
        step_size = Float64(eval_expr(node[4], env))
        steps = Int(eval_expr(node[5], env))
        current = eval_expr(node[6], env)
        mass = eval_expr(node[7], env)
        return _metric_hmc_step!(source, env["logdensity"], env["gradient"],
            step_size, steps, current, mass, kind)
    end
    if tag == "multinomial-hmc"
        source = eval_expr(node[2], env)
        step_size = Float64(eval_expr(node[3], env))
        steps = Int(eval_expr(node[4], env))
        current = eval_expr(node[5], env)
        return _multinomial_hmc_step!(source, env["logdensity"], env["gradient"],
            step_size, steps, current)
    end
    if tag == "metric-multinomial-hmc"
        kind = Symbol(atom(node[2]))
        source = eval_expr(node[3], env)
        step_size = Float64(eval_expr(node[4], env))
        steps = Int(eval_expr(node[5], env))
        current = eval_expr(node[6], env)
        mass = eval_expr(node[7], env)
        return _metric_multinomial_hmc_step!(source, env["logdensity"],
            env["gradient"], step_size, steps, current, mass, kind)
    end
    if tag == "relativistic-multinomial-hmc"
        source = eval_expr(node[2], env)
        step_size = Float64(eval_expr(node[3], env))
        steps = Int(eval_expr(node[4], env))
        current = eval_expr(node[5], env)
        mass = eval_expr(node[6], env)
        relativistic_mass = Float64(eval_expr(node[7], env))
        return _relativistic_multinomial_hmc_step!(source, env["logdensity"],
            env["gradient"], step_size, steps, current, mass, relativistic_mass)
    end
    if tag == "certified-relativistic-multinomial-hmc"
        source = eval_expr(node[2], env)
        step_size = Float64(eval_expr(node[3], env))
        steps = Int(eval_expr(node[4], env))
        current = eval_expr(node[5], env)
        relativistic_mass = Float64(eval_expr(node[6], env))
        return _certified_relativistic_multinomial_hmc_step!(source,
            env["hamiltonian"], env["metric_factor"], env["integrator"],
            step_size, steps, current, relativistic_mass)
    end
    if tag == "classical-rmhmc"
        source = eval_expr(node[2], env)
        step_size = Float64(eval_expr(node[3], env))
        steps = Int(eval_expr(node[4], env))
        current = eval_expr(node[5], env)
        return _classical_rmhmc_step!(source, env["hamiltonian"],
            env["metric_factor"], env["integrator"], step_size, steps, current)
    end
    if tag == "vector-gauss-legendre-position" ||
            tag == "vector-gauss-legendre-momentum"
        step_size = Float64(eval_expr(node[2], env))
        steps = Int(eval_expr(node[3], env))
        iterations = Int(eval_expr(node[4], env))
        position = eval_expr(node[5], env)
        momentum = eval_expr(node[6], env)
        q, p = _vector_gauss_legendre_n(env["gradient"], step_size, steps,
            iterations, position, momentum)
        return tag == "vector-gauss-legendre-position" ? q : p
    end
    if tag == "approximate-classical-rmhmc"
        source = eval_expr(node[2], env)
        step_size = Float64(eval_expr(node[3], env))
        steps = Int(eval_expr(node[4], env))
        current = eval_expr(node[5], env)
        residual_tolerance = Float64(eval_expr(node[6], env))
        return _classical_rmhmc_step!(source, env["hamiltonian"],
            env["metric_factor"], env["integrator"], step_size, steps,
            current; residual_tolerance)
    end
    if tag == "structured-rmhmc"
        source = eval_expr(node[2], env)
        step_size = Float64(eval_expr(node[3], env))
        steps = Int(eval_expr(node[4], env))
        current = eval_expr(node[5], env)
        residual_tolerance = Float64(eval_expr(node[6], env))
        return _structured_rmhmc_step!(source, env["hamiltonian"],
            env["momentum_sampler"], env["integrator"], step_size, steps,
            current, residual_tolerance)
    end
    if tag == "coupled-multinomial-hmc" || tag == "coupled-gaussian-rwmh" ||
            tag == "xu21-coupled-mixture"
        source = eval_expr(node[2], env)
        step_size = Float64(eval_expr(node[3], env))
        steps = Int(eval_expr(node[4], env))
        scale = Float64(eval_expr(node[5], env))
        hmc_weight = Float64(eval_expr(node[6], env))
        left = Float64.(eval_expr(node[7], env))
        right = Float64.(eval_expr(node[8], env))
        if tag == "coupled-multinomial-hmc"
            return _coupled_multinomial_hmc_step!(source, env["logdensity"],
                env["gradient"], step_size, steps, left, right)
        elseif tag == "coupled-gaussian-rwmh"
            return _coupled_gaussian_rwmh_step!(source, env["logdensity"],
                scale, left, right)
        end
        return uniform_unit!(source) < hmc_weight ?
            _coupled_multinomial_hmc_step!(source, env["logdensity"], env["gradient"],
                step_size, steps, left, right) :
            _coupled_gaussian_rwmh_step!(source, env["logdensity"], scale, left, right)
    end
    if tag == "categorical"
        source = eval_expr(node[2], env)
        weights = eval_expr(node[3], env)
        total = sum(weights; init=BigInt(0))
        draw = BigInt(draw_below!(source, total))
        for (index, weight) in enumerate(weights)
            draw < weight && return BigInt(index - 1)
            draw -= weight
        end
        error("draw_below! violated its range contract")
    end
    error("unsupported IR expression: $tag")
end

function _categorical_uniform!(source, weights)
    draw = uniform_unit!(source) * sum(weights)
    cumulative = 0.0
    for index in eachindex(weights)
        cumulative += weights[index]
        draw < cumulative && return index
    end
    lastindex(weights)
end

function _maximal_categorical_pair!(source, left, right)
    p, q = left ./ sum(left), right ./ sum(right)
    common = min.(p, q)
    common_mass = sum(common)
    if uniform_unit!(source) < common_mass
        index = _categorical_uniform!(source, common)
        return index, index
    end
    _categorical_uniform!(source, p .- common),
        _categorical_uniform!(source, q .- common)
end

function _trajectory(logdensity, gradient, step_size, steps, q0, p0, origin)
    result = Vector{Tuple{Vector{Float64},Vector{Float64}}}(undef, steps + 1)
    for index in 0:steps
        q, p = copy(q0), copy(p0)
        signed_step = index >= origin ? step_size : -step_size
        for _ in 1:abs(index - origin)
            half = p .- (signed_step / 2) .* gradient(q)
            q = q .+ signed_step .* half
            p = half .- (signed_step / 2) .* gradient(q)
        end
        result[index + 1] = (q, p)
    end
    result
end

function _coupled_multinomial_hmc_step!(source, logdensity, gradient,
        step_size, steps, left, right)
    length(left) == length(right) || throw(DimensionMismatch("coupled states"))
    momentum = [standard_normal!(source) for _ in eachindex(left)]
    origin = Int(draw_below!(source, steps + 1))
    left_path = _trajectory(logdensity, gradient, step_size, steps, left, momentum, origin)
    right_path = _trajectory(logdensity, gradient, step_size, steps, right, momentum, origin)
    weights(path) = begin
        logs = [logdensity(q) - sum(abs2, p) / 2 for (q, p) in path]
        exp.(logs .- maximum(logs))
    end
    i, j = _maximal_categorical_pair!(source, weights(left_path), weights(right_path))
    [left_path[i][1], right_path[j][1]]
end

function _coupled_gaussian_rwmh_step!(source, logdensity, scale, left, right)
    length(left) == length(right) || throw(DimensionMismatch("coupled states"))
    noise = [standard_normal!(source) for _ in eachindex(left)]
    proposed_left = left .+ scale .* noise
    log_ratio = (sum(abs2, proposed_left .- right) -
        sum(abs2, proposed_left .- left)) / (-2scale^2)
    proposed_right = if log(uniform_unit!(source)) < min(0.0, log_ratio)
        copy(proposed_left)
    else
        delta = right .- left
        norm2 = sum(abs2, delta)
        norm2 == 0 ? copy(proposed_left) :
            right .+ scale .* (noise .- 2 .* (dot(noise, delta) / norm2) .* delta)
    end
    u = log(uniform_unit!(source))
    next_left = u < min(0.0, logdensity(proposed_left) - logdensity(left)) ? proposed_left : left
    next_right = u < min(0.0, logdensity(proposed_right) - logdensity(right)) ? proposed_right : right
    [next_left, next_right]
end

struct Returned
    value::Any
end

function raise_failure(raw)
    node = items(aslist(raw))
    kind, message = atom(node[1]), atom(node[2])
    kind == "argument" && throw(ArgumentError(message))
    kind == "dimension" && throw(DimensionMismatch(message))
    kind == "internal" && error(message)
    error("unsupported IR failure: $kind")
end

function execute_block(body, env::Dict{String,Any})
    for raw in body
        node = items(aslist(raw))
        tag = atom(node[1])
        if tag == "let"
            env[atom(node[2])] = eval_expr(node[3], env)
        elseif tag == "guard"
            eval_expr(node[2], env) || raise_failure(node[3])
        elseif tag == "draw-below"
            env[atom(node[2])] = BigInt(draw_below!(eval_expr(node[3], env),
                eval_expr(node[4], env)))
        elseif tag == "sample-standard-normal"
            env[atom(node[2])] = standard_normal!(env["source"])
        elseif tag == "sample-uniform-unit"
            env[atom(node[2])] = uniform_unit!(env["source"])
        elseif tag == "sample-standard-normal-vector"
            dimension = Int(eval_expr(node[3], env))
            env[atom(node[2])] = [standard_normal!(env["source"]) for _ in 1:dimension]
        elseif tag == "if"
            if eval_expr(node[2], env)
                result = execute_block(items(aslist(node[3]))[2:end], env)
                result isa Returned && return result
            end
        elseif tag == "return"
            return Returned(eval_expr(node[2], env))
        elseif tag == "fail"
            raise_failure(node[2])
        else
            error("unsupported IR statement: $tag")
        end
    end
    nothing
end

function valid_input_value(kind::String, value)
    kind == "source" && return value isa AbstractRandomSource
    (kind == "log-density" || kind == "gradient") &&
        return applicable(value, 0.0) || applicable(value, Float64[])
    kind == "hamiltonian" && return applicable(value, Float64[], Float64[])
    kind == "metric-factor" && return applicable(value, Float64[])
    kind == "metric" && return applicable(value, Float64[])
    kind == "metric-derivative" && return applicable(value, Float64[])
    kind == "momentum-sampler" &&
        return applicable(value, FloatTraceSource(FloatTraceEvent[]), Float64[])
    kind == "integrator" &&
        return applicable(value, Float64[], Float64[], 0.0)
    kind == "nat" && return value isa Integer && value >= 0
    kind == "nat-vector" &&
        return value isa AbstractVector{<:Integer}
    kind == "nat-matrix" && return value isa AbstractVector &&
        all(row -> row isa AbstractVector{<:Integer}, value)
    kind == "real" && return value isa Real
    kind == "real-vector" && return value isa AbstractVector{<:Real}
    kind == "real-matrix" && return value isa AbstractMatrix{<:Real}
    false
end

function run_program(name::String, arguments...)
    program = get(PROGRAMS, name, nothing)
    program === nothing && error("unknown IR program: $name")
    length(arguments) == length(program.inputs) || throw(ArgumentError("IR argument count"))
    env = Dict{String,Any}()
    for ((input_kind, input_name), value) in zip(program.inputs, arguments)
        valid_input_value(input_kind, value) ||
            throw(ArgumentError("invalid $input_kind input: $input_name"))
        env[input_name] = value
    end
    result = execute_block(program.body, env)
    result isa Returned || error("IR program did not return: $name")
    result.value
end

function categorical_index!(source::AbstractRandomSource, weights::AbstractVector{<:Integer})
    exact = BigInt.(weights)
    all(>=(0), exact) || throw(ArgumentError("weights must be nonnegative"))
    sum(exact; init=BigInt(0)) > 0 || throw(ArgumentError("weights must have positive total"))
    run_program("categorical_index!", source, exact)
end

"""One exact-integer conditional-SMC/particle-Gibbs update for a finite HMM.

`potentials[t, x]` weights state `x` before transition `t`; therefore a path
contains `size(potentials, 1) + 1` states. State values are one-based Julia
indices, while retained particle indices remain zero-based trace draws.
"""
function finite_hmm_particle_gibbs_step!(source::AbstractRandomSource,
        initial_weights::AbstractVector{<:Integer},
        transition_weights::AbstractMatrix{<:Integer},
        potentials::AbstractMatrix{<:Integer}, particles::Integer,
        current_path::AbstractVector{<:Integer})
    particles > 0 || throw(ArgumentError("particle count must be positive"))
    states = length(initial_weights)
    states > 0 || throw(ArgumentError("state space cannot be empty"))
    size(transition_weights) == (states, states) ||
        throw(DimensionMismatch("transition matrix"))
    size(potentials, 2) == states || throw(DimensionMismatch("potentials"))
    length(current_path) == size(potentials, 1) + 1 ||
        throw(DimensionMismatch("reference path horizon"))
    all(x -> 1 <= x <= states, current_path) ||
        throw(ArgumentError("reference path state out of range"))
    all(>=(0), initial_weights) && sum(initial_weights) > 0 ||
        throw(ArgumentError("invalid initial weights"))
    all(>=(0), transition_weights) || throw(ArgumentError("negative transition weight"))
    all(row -> sum(row) > 0, eachrow(transition_weights)) ||
        throw(ArgumentError("transition rows must have positive total"))
    all(>(0), potentials) || throw(ArgumentError("potentials must be positive"))

    count = Int(particles)
    retained = Int(draw_below!(source, count)) + 1
    population = Vector{Int}(undef, count)
    for i in eachindex(population)
        population[i] = i == retained ? Int(current_path[1]) :
            categorical_index!(source, initial_weights) + 1
    end
    populations = Vector{Vector{Int}}(undef, size(potentials, 1) + 1)
    populations[1] = copy(population)
    ancestor_history = Vector{Vector{Int}}(undef, size(potentials, 1))

    for t in axes(potentials, 1)
        next_retained = Int(draw_below!(source, count)) + 1
        resampling_weights = [potentials[t, population[i]] for i in eachindex(population)]
        ancestors = Vector{Int}(undef, count)
        next_population = Vector{Int}(undef, count)
        for i in 1:count
            ancestors[i] = i == next_retained ? retained :
                categorical_index!(source, resampling_weights) + 1
        end
        for i in 1:count
            next_population[i] = i == next_retained ? Int(current_path[t + 1]) :
                categorical_index!(source,
                    @view transition_weights[population[ancestors[i]], :]) + 1
        end
        ancestor_history[t] = ancestors
        populations[t + 1] = next_population
        population = next_population
        retained = next_retained
    end

    terminal = Int(draw_below!(source, count)) + 1
    path = Vector{Int}(undef, length(current_path))
    path[end] = populations[end][terminal]
    for t in reverse(eachindex(ancestor_history))
        terminal = ancestor_history[t][terminal]
        path[t] = populations[t][terminal]
    end
    path
end

function finite_mh_step!(source::AbstractRandomSource, target::AbstractVector{<:Integer},
        proposal::AbstractVector, current::Integer)
    target_weights = BigInt.(target)
    all(>(0), target_weights) || throw(ArgumentError("target weights must be positive"))
    state_count = length(target_weights)
    length(proposal) == state_count || throw(DimensionMismatch("proposal row count"))
    0 <= current < state_count || throw(ArgumentError("current state is out of range"))
    rows = [BigInt.(row) for row in proposal]
    all(row -> length(row) == state_count, rows) ||
        throw(DimensionMismatch("proposal column count"))
    all(row -> all(>=(0), row) && sum(row; init=BigInt(0)) > 0, rows) ||
        throw(ArgumentError("proposal rows need nonnegative weights and positive totals"))
    run_program("finite_mh_step!", source, target_weights, rows, BigInt(current))
end

two_state_mh_step!(source::AbstractRandomSource, current::Integer) =
    finite_mh_step!(source, BigInt[1, 3], [BigInt[1, 1], BigInt[1, 1]], current)

"""Float64 interpretation of the serialized ideal-real Gaussian RWMH program.

This preserves the program's control flow and primitive ordering, but it is
not an exact realization of Lean `ℝ`; arithmetic, `exp`, the callback, and RNG
primitives use Julia's concrete Float64 semantics.
"""
function gaussian_rwmh_step!(source::AbstractRandomSource, logdensity,
        scale::Float64, current::Float64)
    checked_positive_float(scale, "scale")
    checked_finite_float(current, "current state")
    checked = value -> checked_logdensity(logdensity, value)
    Float64(run_program("gaussian_rwmh_step!", source, checked, scale, current))
end

"""Float64 interpretation of the serialized Barker RWMH program.

Uses sigmoid acceptance: 1 / (1 + exp(-log_ratio)) instead of exp(min(0, log_ratio)).
"""
function scalar_barker_rwmh_step!(source::AbstractRandomSource, logdensity,
        scale::Float64, current::Float64)
    checked_positive_float(scale, "scale")
    checked_finite_float(current, "current state")
    checked = value -> checked_logdensity(logdensity, value)
    Float64(run_program("scalar_barker_rwmh_step!", source, checked, scale, current))
end

"""Float64 interpretation of the serialized scalar MALA program."""
function scalar_mala_step!(source::AbstractRandomSource, logdensity, gradient,
        step_size::Float64, current::Float64)
    checked_positive_float(step_size, "step size")
    checked_finite_float(current, "current state")
    checked_log = value -> checked_logdensity(logdensity, value)
    checked_grad = value -> checked_gradient(gradient, value)
    Float64(run_program("scalar_mala_step!", source, checked_log, checked_grad,
        step_size, current))
end

"""Float64 interpretation of the serialized vector MALA program."""
function vector_mala_step!(source::AbstractRandomSource, logdensity, gradient,
        step_size::Float64, current::AbstractVector{<:Real})
    checked_positive_float(step_size, "step size")
    isempty(current) && throw(ArgumentError("position cannot be empty"))
    position = Float64.(current)
    all(isfinite, position) || throw(ArgumentError("position must be finite"))
    checked_log = value -> checked_logdensity(logdensity, value)
    checked_grad = value -> checked_gradient(gradient, value)
    Float64.(run_program("vector_mala_step!", source, checked_log, checked_grad,
        step_size, length(position), position))
end

function _dense_pmala_geometry(gradient, metric, metric_derivative,
        step_size::Float64, position::Vector{Float64})
    dimension = length(position)
    score = checked_gradient(gradient, position)
    raw_metric = metric(position)
    raw_metric isa AbstractMatrix || throw(ArgumentError("metric must return a matrix"))
    size(raw_metric) == (dimension, dimension) || throw(DimensionMismatch("metric dimension"))
    matrix = Matrix{Float64}(raw_metric)
    all(isfinite, matrix) || throw(DomainError(raw_metric, "metric must be finite"))
    issymmetric(matrix) || throw(ArgumentError("metric must be symmetric"))
    factor = try
        cholesky(Symmetric(matrix))
    catch error
        error isa PosDefException || rethrow()
        throw(DomainError(raw_metric, "metric must be positive definite"))
    end
    inverse_metric = factor \ Matrix{Float64}(I, dimension, dimension)
    raw_derivative = metric_derivative(position)
    raw_derivative isa AbstractArray || throw(ArgumentError(
        "metric derivative must return a rank-three array"))
    ndims(raw_derivative) == 3 && size(raw_derivative) ==
        (dimension, dimension, dimension) ||
        throw(DimensionMismatch("metric derivative dimension"))
    derivative = Array{Float64,3}(raw_derivative)
    all(isfinite, derivative) || throw(DomainError(raw_derivative,
        "metric derivative must be finite"))
    divergence = zeros(Float64, dimension)
    for coordinate in 1:dimension
        derivative_inverse = -inverse_metric *
            @view(derivative[:, :, coordinate]) * inverse_metric
        divergence .+= @view derivative_inverse[:, coordinate]
    end
    mean = position .+ (step_size^2 / 2) .*
        (inverse_metric * score .+ divergence)
    logdet = 2sum(log, diag(factor.L))
    (; matrix, factor, mean, logdet)
end

function _dense_pmala_step!(source::AbstractRandomSource, logdensity, gradient,
        metric, metric_derivative, step_size::Float64,
        current::AbstractVector{<:Real})
    checked_positive_float(step_size, "step size")
    isempty(current) && throw(ArgumentError("position cannot be empty"))
    position = Float64.(current)
    all(isfinite, position) || throw(DomainError(current, "position must be finite"))
    current_geometry = _dense_pmala_geometry(
        gradient, metric, metric_derivative, step_size, position)
    noise = [standard_normal!(source) for _ in eachindex(position)]
    proposed = current_geometry.mean .+ step_size .* (current_geometry.factor.L' \ noise)
    proposed_geometry = _dense_pmala_geometry(
        gradient, metric, metric_derivative, step_size, proposed)
    forward_residual = proposed .- current_geometry.mean
    reverse_residual = position .- proposed_geometry.mean
    forward_quadratic = dot(forward_residual,
        current_geometry.matrix * forward_residual) / step_size^2
    reverse_quadratic = dot(reverse_residual,
        proposed_geometry.matrix * reverse_residual) / step_size^2
    logratio = checked_logdensity(logdensity, proposed) -
        checked_logdensity(logdensity, position) +
        (proposed_geometry.logdet - current_geometry.logdet) / 2 -
        (reverse_quadratic - forward_quadratic) / 2
    isfinite(logratio) || throw(DomainError(logratio, "PMALA log ratio must be finite"))
    uniform_unit!(source) < exp(min(0.0, logratio)) ? proposed : copy(position)
end

"""Interpret the emitted dense Lebesgue-correct PMALA program."""
function dense_pmala_step!(source::AbstractRandomSource, logdensity, gradient,
        metric, metric_derivative, step_size::Float64,
        current::AbstractVector{<:Real})
    checked_log = value -> checked_logdensity(logdensity, value)
    checked_grad = value -> checked_gradient(gradient, value)
    run_program("dense_pmala_step!", source, checked_log, checked_grad,
        metric, metric_derivative, step_size, Float64.(current)) |> x -> Float64.(x)
end

"""Float64 interpretation of the serialized scalar one-step HMC program."""
function scalar_hmc_step!(source::AbstractRandomSource, logdensity, gradient,
        step_size::Float64, steps::Integer, current::Float64)
    checked_positive_float(step_size, "step size")
    checked_positive_count(steps, "leapfrog steps")
    checked_finite_float(current, "current state")
    checked_log = value -> checked_logdensity(logdensity, value)
    checked_grad = value -> checked_gradient(gradient, value)
    Float64(run_program("scalar_hmc_step!", source, checked_log, checked_grad,
        step_size, current, steps))
end

"""Float64 interpretation of the serialized vector endpoint-HMC program."""
function vector_hmc_step!(source::AbstractRandomSource, logdensity, gradient,
        step_size::Float64, steps::Integer, current::AbstractVector{<:Real})
    isfinite(step_size) && step_size > 0.0 ||
        throw(ArgumentError("step size must be finite and positive"))
    steps > 0 || throw(ArgumentError("leapfrog steps must be positive"))
    isempty(current) && throw(ArgumentError("position cannot be empty"))
    position = Float64.(current)
    all(isfinite, position) || throw(ArgumentError("position must be finite"))
    checked_log = value -> checked_logdensity(logdensity, value)
    checked_grad = value -> checked_gradient(gradient, value)
    result = run_program("vector_hmc_step!", source, checked_log, checked_grad,
        step_size, steps, length(position), position)
    Float64.(result)
end

"""Interpret the Lean-emitted two-stage Gauss--Legendre endpoint-HMC IR."""
function vector_gauss_legendre_hmc_step!(source::AbstractRandomSource,
        logdensity, gradient, step_size::Float64, steps::Integer,
        iterations::Integer, current::AbstractVector{<:Real})
    step_size > 0 && isfinite(step_size) || throw(ArgumentError("step size"))
    steps > 0 || throw(ArgumentError("integration steps must be positive"))
    iterations > 0 || throw(ArgumentError("stage iterations must be positive"))
    position = Float64.(current)
    result = run_program("vector_gauss_legendre_hmc_step!", source,
        value -> checked_logdensity(logdensity, value),
        value -> checked_gradient(gradient, value), step_size, steps,
        iterations, length(position), position)
    Float64.(result)
end

"""Reference endpoint HMC for a constant diagonal or dense mass matrix."""
function _metric_hmc_step!(source::AbstractRandomSource, logdensity, gradient,
        step_size::Float64, steps::Integer, current::AbstractVector{<:Real}, mass,
        kind::Symbol)
    dimension = length(current)
    dimension > 0 || throw(ArgumentError("position cannot be empty"))
    z = [standard_normal!(source) for _ in 1:dimension]
    if kind === :diagonal
        length(mass) == dimension || throw(DimensionMismatch("mass dimension"))
        all(x -> isfinite(x) && x > 0, mass) ||
            throw(ArgumentError("diagonal mass must be finite and positive"))
        momentum = sqrt.(mass) .* z
        velocity = p -> p ./ mass
    elseif kind === :dense
        size(mass) == (dimension, dimension) || throw(DimensionMismatch("mass dimension"))
        matrix = Matrix{Float64}(mass)
        all(isfinite, matrix) || throw(ArgumentError("mass matrix must be finite"))
        issymmetric(matrix) || throw(ArgumentError("mass matrix must be symmetric"))
        isposdef(matrix) || throw(ArgumentError("mass matrix must be positive definite"))
        factor = cholesky(Symmetric(matrix)).L
        momentum = factor * z
        velocity = p -> factor' \ (factor \ p)
    else
        error("unsupported metric kind: $kind")
    end
    position = Float64.(current)
    initial_momentum = copy(momentum)
    for _ in 1:steps
        momentum = momentum .- (step_size / 2) .* gradient(position)
        position = position .+ step_size .* velocity(momentum)
        momentum = momentum .- (step_size / 2) .* gradient(position)
    end
    current_energy = -logdensity(current) + dot(initial_momentum, velocity(initial_momentum)) / 2
    next_energy = -logdensity(position) + dot(momentum, velocity(momentum)) / 2
    log(uniform_unit!(source)) < min(0.0, current_energy - next_energy) ?
        position : Float64.(current)
end

function metric_hmc_step!(source::AbstractRandomSource, logdensity, gradient,
        step_size::Float64, steps::Integer, current::AbstractVector{<:Real}, mass)
    all(isfinite, current) || throw(ArgumentError("position must be finite"))
    name = mass isa AbstractVector ? "diagonal_hmc_step!" : "dense_hmc_step!"
    checked_log = value -> checked_logdensity(logdensity, value)
    checked_grad = value -> checked_gradient(gradient, value)
    Float64.(run_program(name, source, checked_log, checked_grad, step_size, steps,
        current, mass))
end

function _multinomial_hmc_step!(source::AbstractRandomSource, logdensity, gradient,
        step_size::Float64, steps::Integer, current::AbstractVector{<:Real})
    steps > 0 || throw(ArgumentError("trajectory length must be positive"))
    q0 = Float64.(current)
    isempty(q0) && throw(ArgumentError("position cannot be empty"))
    p0 = [standard_normal!(source) for _ in eachindex(q0)]
    origin = Int(draw_below!(source, steps + 1))
    trajectory = Vector{Tuple{Vector{Float64},Vector{Float64}}}(undef, steps + 1)
    for index in 0:steps
        q, p = copy(q0), copy(p0)
        signed_step = index >= origin ? step_size : -step_size
        for _ in 1:abs(index - origin)
            half = p .- (signed_step / 2) .* gradient(q)
            q = q .+ signed_step .* half
            p = half .- (signed_step / 2) .* gradient(q)
        end
        trajectory[index + 1] = (q, p)
    end
    logweights = [logdensity(q) - sum(abs2, p) / 2 for (q, p) in trajectory]
    maximum_weight = maximum(logweights)
    weights = exp.(logweights .- maximum_weight)
    draw = uniform_unit!(source) * sum(weights)
    selected = length(weights)
    cumulative = 0.0
    for index in eachindex(weights)
        cumulative += weights[index]
        if draw < cumulative
            selected = index
            break
        end
    end
    trajectory[selected][1]
end

function multinomial_hmc_step!(source::AbstractRandomSource, logdensity, gradient,
        step_size::Float64, steps::Integer, current::AbstractVector{<:Real})
    all(isfinite, current) || throw(ArgumentError("position must be finite"))
    checked_log = value -> checked_logdensity(logdensity, value)
    checked_grad = value -> checked_gradient(gradient, value)
    Float64.(run_program("multinomial_hmc_step!", source, checked_log, checked_grad,
        step_size, steps, current))
end

function _metric_multinomial_hmc_step!(source::AbstractRandomSource, logdensity,
        gradient, step_size::Float64, steps::Integer,
        current::AbstractVector{<:Real}, mass, kind::Symbol)
    steps > 0 || throw(ArgumentError("trajectory length must be positive"))
    q0 = Float64.(current)
    isempty(q0) && throw(ArgumentError("position cannot be empty"))
    z = [standard_normal!(source) for _ in eachindex(q0)]
    if kind === :diagonal
        length(mass) == length(q0) || throw(DimensionMismatch("mass dimension"))
        all(x -> isfinite(x) && x > 0, mass) ||
            throw(ArgumentError("diagonal mass must be finite and positive"))
        p0 = sqrt.(mass) .* z
        velocity = p -> p ./ mass
    elseif kind === :dense
        size(mass) == (length(q0), length(q0)) ||
            throw(DimensionMismatch("mass dimension"))
        matrix = Matrix{Float64}(mass)
        all(isfinite, matrix) || throw(ArgumentError("mass matrix must be finite"))
        issymmetric(matrix) || throw(ArgumentError("mass matrix must be symmetric"))
        isposdef(matrix) || throw(ArgumentError("mass matrix must be positive definite"))
        factor = cholesky(Symmetric(matrix)).L
        p0 = factor * z
        velocity = p -> factor' \ (factor \ p)
    else
        error("unsupported metric kind: $kind")
    end
    origin = Int(draw_below!(source, steps + 1))
    trajectory = Vector{Tuple{Vector{Float64},Vector{Float64}}}(undef, steps + 1)
    for index in 0:steps
        q, p = copy(q0), copy(p0)
        signed_step = index >= origin ? step_size : -step_size
        for _ in 1:abs(index - origin)
            half = p .- (signed_step / 2) .* gradient(q)
            q = q .+ signed_step .* velocity(half)
            p = half .- (signed_step / 2) .* gradient(q)
        end
        trajectory[index + 1] = (q, p)
    end
    logweights = [logdensity(q) - dot(p, velocity(p)) / 2 for (q, p) in trajectory]
    weights = exp.(logweights .- maximum(logweights))
    draw = uniform_unit!(source) * sum(weights)
    cumulative = 0.0
    for (index, weight) in pairs(weights)
        cumulative += weight
        draw < cumulative && return trajectory[index][1]
    end
    trajectory[end][1]
end

function metric_multinomial_hmc_step!(source::AbstractRandomSource, logdensity,
        gradient, step_size::Float64, steps::Integer,
        current::AbstractVector{<:Real}, mass)
    all(isfinite, current) || throw(ArgumentError("position must be finite"))
    name = mass isa AbstractVector ? "diagonal_multinomial_hmc_step!" :
        "dense_multinomial_hmc_step!"
    checked_log = value -> checked_logdensity(logdensity, value)
    checked_grad = value -> checked_gradient(gradient, value)
    Float64.(run_program(name, source, checked_log, checked_grad, step_size, steps,
        current, mass))
end

function _relativistic_radius!(source::AbstractRandomSource, dimension::Int,
        relativistic_mass::Float64)
    while true
        # Gamma(d, 1) proposal: sum of d independent exponential variables.
        radius = sum((-log1p(-uniform_unit!(source)) for _ in 1:dimension); init=0.0)
        log_acceptance = radius - sqrt(radius^2 + relativistic_mass^2)
        log(uniform_unit!(source)) < log_acceptance && return radius
    end
end

function _relativistic_momentum!(source::AbstractRandomSource,
        mass::AbstractVector{<:Real}, relativistic_mass::Float64)
    dimension = length(mass)
    radius = _relativistic_radius!(source, dimension, relativistic_mass)
    direction = [standard_normal!(source) for _ in 1:dimension]
    direction_norm = norm(direction)
    isfinite(direction_norm) && direction_norm > 0 ||
        throw(DomainError(direction, "spherical direction draw must be nonzero"))
    isotropic = (radius / direction_norm) .* direction
    # If A'A = G⁻¹, the corrected transport is p = A⁻¹z.
    sqrt.(mass) .* isotropic
end

function _relativistic_multinomial_hmc_step!(source::AbstractRandomSource,
        logdensity, gradient, step_size::Float64, steps::Integer,
        current::AbstractVector{<:Real}, mass::AbstractVector{<:Real},
        relativistic_mass::Float64)
    steps > 0 || throw(ArgumentError("trajectory length must be positive"))
    isfinite(step_size) && step_size > 0 ||
        throw(ArgumentError("step size must be finite and positive"))
    q0 = Float64.(current)
    isempty(q0) && throw(ArgumentError("position cannot be empty"))
    length(mass) == length(q0) || throw(DimensionMismatch("mass dimension"))
    all(x -> isfinite(x) && x > 0, mass) ||
        throw(ArgumentError("diagonal metric must be finite and positive"))
    isfinite(relativistic_mass) && relativistic_mass > 0 ||
        throw(ArgumentError("relativistic mass must be finite and positive"))
    converted_mass = Float64.(mass)
    p0 = _relativistic_momentum!(source, converted_mass, relativistic_mass)
    velocity = function (p)
        inverse_metric_p = p ./ converted_mass
        inverse_metric_p ./ sqrt(dot(p, inverse_metric_p) + relativistic_mass^2)
    end
    advance = function (q, p, signed_step)
        half = p .- (signed_step / 2) .* gradient(q)
        next_q = q .+ signed_step .* velocity(half)
        next_p = half .- (signed_step / 2) .* gradient(next_q)
        next_q, next_p
    end
    origin = Int(draw_below!(source, steps + 1))
    trajectory = Vector{Tuple{Vector{Float64},Vector{Float64}}}(undef, steps + 1)
    for index in 0:steps
        q, p = copy(q0), copy(p0)
        signed_step = index >= origin ? step_size : -step_size
        for _ in 1:abs(index - origin)
            q, p = advance(q, p, signed_step)
        end
        trajectory[index + 1] = (q, p)
    end
    logweights = [logdensity(q) -
        sqrt(dot(p, p ./ converted_mass) + relativistic_mass^2)
        for (q, p) in trajectory]
    weights = exp.(logweights .- maximum(logweights))
    draw = uniform_unit!(source) * sum(weights)
    cumulative = 0.0
    for (index, weight) in pairs(weights)
        cumulative += weight
        draw < cumulative && return trajectory[index][1]
    end
    trajectory[end][1]
end

function relativistic_multinomial_hmc_step!(source::AbstractRandomSource,
        logdensity, gradient, step_size::Real, steps::Integer,
        current::AbstractVector{<:Real}, mass::AbstractVector{<:Real},
        relativistic_mass::Real)
    all(isfinite, current) || throw(ArgumentError("position must be finite"))
    checked_log = value -> checked_logdensity(logdensity, value)
    checked_grad = value -> checked_gradient(gradient, value)
    Float64.(run_program("relativistic_multinomial_hmc_step!", source,
        checked_log, checked_grad, Float64(step_size), steps, current, mass,
        Float64(relativistic_mass)))
end

function _corrected_isotropic_relativistic_momentum!(source::AbstractRandomSource,
        dimension::Int, relativistic_mass::Float64)
    radius = _relativistic_radius!(source, dimension, relativistic_mass)
    direction = [standard_normal!(source) for _ in 1:dimension]
    direction_norm = norm(direction)
    isfinite(direction_norm) && direction_norm > 0 ||
        throw(DomainError(direction, "spherical direction draw must be nonzero"))
    (radius / direction_norm) .* direction
end

function _checked_certified_step(integrator, q, p, step_size)
    result = integrator(q, p, step_size)
    result isa Tuple && length(result) == 3 ||
        throw(ArgumentError("integrator must return (position, momentum, certificate)"))
    next_q, next_p, certificate = result
    certificate isa ImplicitSolveCertificate ||
        throw(ArgumentError("integrator must return an ImplicitSolveCertificate"))
    certifies_exact_solver(certificate) ||
        throw(ArgumentError("implicit solve is approximate or lacks global validity witnesses"))
    Float64.(next_q), Float64.(next_p)
end

"""One certificate-gated endpoint transition for classical Gaussian RMHMC.

`metric_factor(q)` returns `A(q)` in the Lean convention
`A(q)'A(q) = G(q)⁻¹`. Momentum is therefore refreshed as `A(q)⁻¹z` for a
standard Gaussian `z`. Each generalized-leapfrog step must return an exact
global implicit-solver certificate.
"""
function _classical_rmhmc_step!(source::AbstractRandomSource, hamiltonian,
        metric_factor, integrator, step_size::Real, steps::Integer,
        current::AbstractVector{<:Real}; residual_tolerance=nothing)
    ε = Float64(step_size)
    isfinite(ε) && ε > 0 || throw(ArgumentError(
        "step size must be finite and positive"))
    steps > 0 || throw(ArgumentError("trajectory length must be positive"))
    q0 = Float64.(current)
    isempty(q0) && throw(ArgumentError("position cannot be empty"))
    all(isfinite, q0) || throw(ArgumentError("position must be finite"))
    factor = Matrix{Float64}(metric_factor(q0))
    size(factor) == (length(q0), length(q0)) ||
        throw(DimensionMismatch("metric factor dimension"))
    all(isfinite, factor) || throw(ArgumentError("metric factor must be finite"))
    abs(det(factor)) > 0 || throw(ArgumentError("metric factor must be invertible"))
    p0 = factor \ [standard_normal!(source) for _ in eachindex(q0)]
    all(isfinite, p0) || throw(DomainError(p0, "refreshed momentum"))
    q, p = copy(q0), p0
    for _ in 1:steps
        result = integrator(q, p, ε)
        result isa Tuple && length(result) == 3 || throw(ArgumentError(
            "integrator must return (position, momentum, certificate)"))
        next_q, next_p, certificate = result
        certificate isa ImplicitSolveCertificate || throw(ArgumentError(
            "integrator did not return an implicit-solver certificate"))
        if residual_tolerance === nothing
            certifies_exact_solver(certificate) || throw(ArgumentError(
                "implicit solve is not exactly certified"))
        else
            tolerance = BigFloat(residual_tolerance)
            tolerance >= 0 || throw(ArgumentError(
                "residual tolerance must be nonnegative"))
            certificate.half_momentum_residual.bound <= tolerance &&
                certificate.position_residual.bound <= tolerance ||
                throw(ArgumentError("implicit solve exceeds residual tolerance"))
        end
        q, p = Float64.(next_q), Float64.(next_p)
        length(q) == length(q0) && length(p) == length(q0) ||
            throw(DimensionMismatch("integrator state dimension"))
        all(isfinite, q) && all(isfinite, p) ||
            throw(DomainError((q, p), "integrator state"))
    end
    current_energy = Float64(hamiltonian(q0, p0))
    proposed_energy = Float64(hamiltonian(q, p))
    isfinite(current_energy) && isfinite(proposed_energy) ||
        throw(DomainError((current_energy, proposed_energy),
            "Hamiltonian must be finite"))
    threshold = exp(min(0.0, current_energy - proposed_energy))
    uniform_unit!(source) < threshold ? q : q0
end

function classical_rmhmc_step!(source::AbstractRandomSource, hamiltonian,
        metric_factor, integrator, step_size::Real, steps::Integer,
        current::AbstractVector{<:Real})
    Float64.(run_program("classical_rmhmc_step!", source, hamiltonian,
        metric_factor, integrator, Float64(step_size), steps, current))
end

"""Bounded-residual classical RMHMC execution.

This is a numerical approximation contract, not an exact solver certificate.
It checks every observed implicit residual against `residual_tolerance` but
does not claim exact reversibility, volume preservation, or stationarity.
"""
function approximate_classical_rmhmc_step!(source::AbstractRandomSource,
        hamiltonian, metric_factor, integrator, step_size::Real, steps::Integer,
        current::AbstractVector{<:Real}, residual_tolerance::Real)
    Float64.(run_program("approximate_classical_rmhmc_step!", source,
        hamiltonian, metric_factor, integrator, Float64(step_size), steps,
        current, Float64(residual_tolerance)))
end

"""Execute the explicit dense-RMHMC Lean IR entry point."""
function dense_rmhmc_step!(source::AbstractRandomSource, hamiltonian,
        metric_factor, integrator, step_size::Real, steps::Integer,
        current::AbstractVector{<:Real}, residual_tolerance::Real)
    Float64.(run_program("dense_rmhmc_step!", source, hamiltonian,
        metric_factor, integrator, Float64(step_size), steps, current,
        Float64(residual_tolerance)))
end

"""Reference primitive for structured RMHMC momentum and integration.

The IR owns the stochastic transition. `momentum_sampler(source, q)` and the
Hamiltonian/integrator callbacks are explicit host boundaries.
"""
function _structured_rmhmc_step!(source::AbstractRandomSource, hamiltonian,
        momentum_sampler, integrator, step_size::Real, steps::Integer,
        current::AbstractVector{<:Real}, residual_tolerance::Real)
    ε = Float64(step_size)
    isfinite(ε) && ε > 0 || throw(ArgumentError(
        "step size must be finite and positive"))
    steps > 0 || throw(ArgumentError("trajectory length must be positive"))
    tolerance = BigFloat(residual_tolerance)
    isfinite(tolerance) && tolerance >= 0 || throw(ArgumentError(
        "residual tolerance must be finite and nonnegative"))
    q0 = Float64.(current)
    isempty(q0) && throw(ArgumentError("position cannot be empty"))
    all(isfinite, q0) || throw(ArgumentError("position must be finite"))
    p0 = Float64.(momentum_sampler(source, q0))
    length(p0) == length(q0) || throw(DimensionMismatch(
        "refreshed momentum dimension"))
    all(isfinite, p0) || throw(DomainError(p0, "refreshed momentum"))
    q, p = copy(q0), p0
    for _ in 1:steps
        result = integrator(q, p, ε)
        result isa Tuple && length(result) == 3 || throw(ArgumentError(
            "integrator must return (position, momentum, certificate)"))
        next_q, next_p, certificate = result
        certificate isa ImplicitSolveCertificate || throw(ArgumentError(
            "integrator did not return an implicit-solver certificate"))
        certificate.half_momentum_residual.bound <= tolerance &&
            certificate.position_residual.bound <= tolerance ||
            throw(ArgumentError("implicit solve exceeds residual tolerance"))
        q, p = Float64.(next_q), Float64.(next_p)
        length(q) == length(q0) && length(p) == length(q0) ||
            throw(DimensionMismatch("integrator state dimension"))
        all(isfinite, q) && all(isfinite, p) || throw(DomainError(
            (q, p), "integrator state"))
    end
    current_energy = Float64(hamiltonian(q0, p0))
    proposed_energy = Float64(hamiltonian(q, p))
    isfinite(current_energy) && isfinite(proposed_energy) || throw(DomainError(
        (current_energy, proposed_energy), "Hamiltonian must be finite"))
    threshold = exp(min(0.0, current_energy - proposed_energy))
    uniform_unit!(source) < threshold ? q : q0
end

"""Execute the structured-RMHMC Lean IR entry point."""
function random_sketch_rmhmc_step!(source::AbstractRandomSource, hamiltonian,
        momentum_sampler, integrator, step_size::Real, steps::Integer,
        current::AbstractVector{<:Real}, residual_tolerance::Real)
    Float64.(run_program("random_sketch_rmhmc_step!", source, hamiltonian,
        momentum_sampler, integrator, Float64(step_size), steps, current,
        Float64(residual_tolerance)))
end

"""One concrete derivative callback invocation made by the reference solver."""
struct FixedPointCallbackEvaluation
    kind::Symbol
    position::Vector{Float64}
    momentum::Vector{Float64}
    value::Vector{Float64}
end

"""One rounded `base + scale*callback` update, retaining every callback
vector consumed by that arithmetic expression."""
struct FixedPointAffineUpdateEvaluation
    kind::Symbol
    base::Vector{Float64}
    scale::Float64
    callbacks::Vector{Vector{Float64}}
    computed_update::Vector{Float64}
end

"""Final iterates, updates, and every callback invoked by both implicit loops."""
struct FixedPointGeneralizedLeapfrogTrace
    half_momentum::Vector{Float64}
    half_callback::Vector{Float64}
    half_update::Vector{Float64}
    next_position::Vector{Float64}
    position_callback::Vector{Float64}
    position_update::Vector{Float64}
    callback_evaluations::Vector{FixedPointCallbackEvaluation}
    affine_updates::Vector{FixedPointAffineUpdateEvaluation}
    half_iterations::Int
    position_iterations::Int
end

"""Execute the generalized-leapfrog loops and retain their final updates."""
function _fixed_point_generalized_leapfrog_trace(position_derivative,
        momentum_derivative, position::AbstractVector{<:Real},
        momentum::AbstractVector{<:Real}, step_size::Real;
        max_iterations::Integer=100, atol::Real=1e-10, rtol::Real=1e-8,
        unique::Bool=false, reversible::Bool=false,
        volume_preserving::Bool=false)
    max_iterations > 0 || throw(ArgumentError("max_iterations must be positive"))
    ε, absolute, relative = Float64(step_size), Float64(atol), Float64(rtol)
    isfinite(ε) || throw(ArgumentError("step size must be finite"))
    isfinite(absolute) && absolute >= 0 ||
        throw(ArgumentError("atol must be finite and nonnegative"))
    isfinite(relative) && relative >= 0 ||
        throw(ArgumentError("rtol must be finite and nonnegative"))
    q, p = Float64.(position), Float64.(momentum)
    length(q) == length(p) || throw(DimensionMismatch("position and momentum"))
    isempty(q) && throw(ArgumentError("state cannot be empty"))
    all(isfinite, q) && all(isfinite, p) ||
        throw(ArgumentError("state must be finite"))
    callback_evaluations = FixedPointCallbackEvaluation[]
    affine_updates = FixedPointAffineUpdateEvaluation[]

    p_half = copy(p)
    half_iterations = 0
    for iteration in 1:max_iterations
        half_iterations = iteration
        derivative = Float64.(position_derivative(q, p_half))
        push!(callback_evaluations, FixedPointCallbackEvaluation(:position,
            copy(q), copy(p_half), copy(derivative)))
        candidate = p .- (ε / 2) .* derivative
        push!(affine_updates, FixedPointAffineUpdateEvaluation(:half_momentum,
            copy(p), -(ε / 2), [copy(derivative)], copy(candidate)))
        length(candidate) == length(p) ||
            throw(DimensionMismatch("position derivative"))
        all(isfinite, candidate) || throw(DomainError(candidate, "half momentum"))
        residual = norm(candidate .- p_half)
        p_half = candidate
        residual <= absolute + relative * max(norm(p_half), 1.0) && break
    end

    q_next = copy(q)
    position_iterations = 0
    initial_velocity = Float64.(momentum_derivative(q, p_half))
    push!(callback_evaluations, FixedPointCallbackEvaluation(:momentum,
        copy(q), copy(p_half), copy(initial_velocity)))
    length(initial_velocity) == length(q) ||
        throw(DimensionMismatch("momentum derivative"))
    for iteration in 1:max_iterations
        position_iterations = iteration
        terminal_velocity = Float64.(momentum_derivative(q_next, p_half))
        push!(callback_evaluations, FixedPointCallbackEvaluation(:momentum,
            copy(q_next), copy(p_half), copy(terminal_velocity)))
        length(terminal_velocity) == length(q) ||
            throw(DimensionMismatch("momentum derivative"))
        candidate = q .+ (ε / 2) .* (initial_velocity .+ terminal_velocity)
        push!(affine_updates, FixedPointAffineUpdateEvaluation(:position,
            copy(q), ε / 2, [copy(initial_velocity), copy(terminal_velocity)],
            copy(candidate)))
        all(isfinite, candidate) || throw(DomainError(candidate, "next position"))
        residual = norm(candidate .- q_next)
        q_next = candidate
        residual <= absolute + relative * max(norm(q_next), 1.0) && break
    end

    half_callback = Float64.(position_derivative(q, p_half))
    push!(callback_evaluations, FixedPointCallbackEvaluation(:position,
        copy(q), copy(p_half), copy(half_callback)))
    half_update = p .- (ε / 2) .* half_callback
    push!(affine_updates, FixedPointAffineUpdateEvaluation(:half_momentum,
        copy(p), -(ε / 2), [copy(half_callback)], copy(half_update)))
    final_velocity = Float64.(momentum_derivative(q_next, p_half))
    push!(callback_evaluations, FixedPointCallbackEvaluation(:momentum,
        copy(q_next), copy(p_half), copy(final_velocity)))
    position_callback = initial_velocity .+ final_velocity
    position_update = q .+ (ε / 2) .* position_callback
    push!(affine_updates, FixedPointAffineUpdateEvaluation(:position,
        copy(q), ε / 2, [copy(initial_velocity), copy(final_velocity)],
        copy(position_update)))
    half_residual = norm(p_half .- half_update)
    position_residual = norm(q_next .- position_update)
    final_position_derivative = Float64.(position_derivative(q_next, p_half))
    push!(callback_evaluations, FixedPointCallbackEvaluation(:position,
        copy(q_next), copy(p_half), copy(final_position_derivative)))
    p_next = p_half .- (ε / 2) .* final_position_derivative
    push!(affine_updates, FixedPointAffineUpdateEvaluation(:final_momentum,
        copy(p_half), -(ε / 2), [copy(final_position_derivative)], copy(p_next)))
    certificate = certify_implicit_solve(half_residual, half_residual,
        position_residual, position_residual; unique=unique,
        reversible=reversible, volume_preserving=volume_preserving)
    trace = FixedPointGeneralizedLeapfrogTrace(copy(p_half),
        copy(half_callback), copy(half_update), copy(q_next),
        copy(position_callback), copy(position_update), callback_evaluations,
        affine_updates, half_iterations, position_iterations)
    q_next, p_next, certificate, trace
end

"""Solve the two generalized-leapfrog implicit equations by fixed-point iteration.

The returned certificate reports the observed residuals. A positive tolerance
is approximation data and is intentionally rejected by the exact certified
sampler. Set the global witness flags only when they have been established for
the complete solver family, not merely for this run.
"""
function fixed_point_generalized_leapfrog(args...; kwargs...)
    q, p, certificate, _ = _fixed_point_generalized_leapfrog_trace(
        args...; kwargs...)
    q, p, certificate
end


"""Run the reference solver while returning its auditable final-update trace."""
fixed_point_generalized_leapfrog_trace(args...; kwargs...) =
    _fixed_point_generalized_leapfrog_trace(args...; kwargs...)

function _certified_relativistic_multinomial_hmc_step!(source::AbstractRandomSource,
        hamiltonian, metric_factor, integrator, step_size::Float64, steps::Integer,
        current::AbstractVector{<:Real}, relativistic_mass::Float64)
    steps > 0 || throw(ArgumentError("trajectory length must be positive"))
    q0 = Float64.(current)
    isempty(q0) && throw(ArgumentError("position cannot be empty"))
    factor = Matrix{Float64}(metric_factor(q0))
    size(factor) == (length(q0), length(q0)) ||
        throw(DimensionMismatch("metric factor dimension"))
    abs(det(factor)) > 0 || throw(ArgumentError("metric factor must be invertible"))
    z = _corrected_isotropic_relativistic_momentum!(source, length(q0),
        relativistic_mass)
    p0 = factor \ z # corrected p = A⁻¹z transport
    origin = Int(draw_below!(source, steps + 1))
    trajectory = Vector{Tuple{Vector{Float64},Vector{Float64}}}(undef, steps + 1)
    for index in 0:steps
        q, p = copy(q0), copy(p0)
        signed_step = index >= origin ? step_size : -step_size
        for _ in 1:abs(index - origin)
            q, p = _checked_certified_step(integrator, q, p, signed_step)
        end
        trajectory[index + 1] = (q, p)
    end
    logweights = [-Float64(hamiltonian(q, p)) for (q, p) in trajectory]
    all(isfinite, logweights) || throw(DomainError(logweights, "Hamiltonian must be finite"))
    weights = exp.(logweights .- maximum(logweights))
    draw = uniform_unit!(source) * sum(weights)
    cumulative = 0.0
    for (index, weight) in pairs(weights)
        cumulative += weight
        draw < cumulative && return trajectory[index][1]
    end
    trajectory[end][1]
end

function certified_relativistic_multinomial_hmc_step!(source::AbstractRandomSource,
        hamiltonian, metric_factor, integrator, step_size::Real, steps::Integer,
        current::AbstractVector{<:Real}, relativistic_mass::Real)
    Float64.(run_program("certified_relativistic_multinomial_hmc_step!", source,
        hamiltonian, metric_factor, integrator, Float64(step_size), steps,
        current, Float64(relativistic_mass)))
end

function _run_coupled(name, source::AbstractRandomSource, logdensity, gradient,
        step_size::Real, steps::Integer, scale::Real, hmc_weight::Real,
        left::AbstractVector{<:Real}, right::AbstractVector{<:Real})
    length(left) == length(right) || throw(DimensionMismatch("coupled states"))
    isempty(left) && throw(ArgumentError("position cannot be empty"))
    step_size > 0 && steps > 0 || throw(ArgumentError("invalid HMC trajectory"))
    scale > 0 || throw(ArgumentError("RWMH scale must be positive"))
    0 <= hmc_weight <= 1 || throw(ArgumentError("HMC weight must lie in [0,1]"))
    checked_log = value -> checked_logdensity(logdensity, value)
    checked_grad = value -> checked_gradient(gradient, value)
    result = run_program(name, source, checked_log, checked_grad, Float64(step_size),
        steps, Float64(scale), Float64(hmc_weight), left, right)
    (Float64.(result[1]), Float64.(result[2]))
end

coupled_multinomial_hmc_step!(source::AbstractRandomSource, logdensity, gradient,
    step_size::Real, steps::Integer, left::AbstractVector{<:Real},
    right::AbstractVector{<:Real}) =
    _run_coupled("coupled_multinomial_hmc_step!", source, logdensity, gradient,
        step_size, steps, 1.0, 1.0, left, right)

coupled_gaussian_rwmh_step!(source::AbstractRandomSource, logdensity, scale::Real,
    left::AbstractVector{<:Real}, right::AbstractVector{<:Real}) =
    _run_coupled("coupled_gaussian_rwmh_step!", source, logdensity, identity,
        1.0, 1, scale, 0.0, left, right)

xu21_coupled_step!(source::AbstractRandomSource, logdensity, gradient,
    step_size::Real, steps::Integer, scale::Real, hmc_weight::Real,
    left::AbstractVector{<:Real}, right::AbstractVector{<:Real}) =
    _run_coupled("xu21_coupled_step!", source, logdensity, gradient, step_size,
        steps, scale, hmc_weight, left, right)

end
