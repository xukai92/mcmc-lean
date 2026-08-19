#=
This file is included into the `VerifiedSamplers` module after the core HMC
types have been defined. It contains production-shaped, fixed-parameter HMC
variants whose semantics reuse those established transition implementations.
=#

"""Endpoint HMC terminated by a fixed integration time.

The number of leapfrog updates is `floor(integration_time / step_size)`,
matching the conventional fixed-integration-time termination rule. At least
one update must fit. This is a fixed-parameter sampler; it performs no step-size
or metric adaptation.
"""
struct FixedIntegrationTimeHMC{S}
    sampler::S
    integration_time::Float64
    steps::Int
end

function _fixed_integration_steps(step_size::Real, integration_time::Real)
    ε, λ = Float64(step_size), Float64(integration_time)
    isfinite(ε) && ε > 0 ||
        throw(ArgumentError("step size must be finite and positive"))
    isfinite(λ) && λ > 0 ||
        throw(ArgumentError("integration time must be finite and positive"))
    steps = floor(Int, λ / ε)
    steps > 0 || throw(ArgumentError(
        "integration time must contain at least one leapfrog step"))
    ε, λ, steps
end

function FixedIntegrationTimeHMC(logdensity::F, gradient::G,
        step_size::Real, integration_time::Real) where {F,G}
    ε, λ, steps = _fixed_integration_steps(step_size, integration_time)
    FixedIntegrationTimeHMC(VectorHMC(logdensity, gradient, ε, steps), λ, steps)
end

function FixedIntegrationTimeHMC(logdensity::F, gradient::G,
        metric::M, step_size::Real, integration_time::Real) where
        {F,G,M<:Union{DiagonalMetric,DenseMetric,RankUpdateMetric}}
    ε, λ, steps = _fixed_integration_steps(step_size, integration_time)
    FixedIntegrationTimeHMC(
        MetricHMC(logdensity, gradient, metric, ε, steps), λ, steps)
end

step(rng::AbstractRNG, sampler::FixedIntegrationTimeHMC, current) =
    step(rng, sampler.sampler, current)

step(sampler::FixedIntegrationTimeHMC, current) =
    step(Random.default_rng(), sampler, current)

sample(rng::AbstractRNG, sampler::FixedIntegrationTimeHMC,
        initial, count::Integer) = sample(rng, sampler.sampler, initial, count)

sample(sampler::FixedIntegrationTimeHMC, initial, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)

"""Endpoint HMC with one symmetrically jittered step size per trajectory.

For `u ∈ [0,1)`, the trajectory step size is
`nominal_step_size * (1 + jitter * (2u - 1))`. The metric and all other
parameters remain fixed. `jitter` must lie in `[0,1)` so every realized step
size is positive.
"""
struct JitteredHMC{F,G,M}
    logdensity::F
    gradient::G
    metric::M
    nominal_step_size::Float64
    jitter::Float64
    steps::Int
end

function JitteredHMC(logdensity::F, gradient::G, step_size::Real,
        steps::Integer=10; jitter::Real=0.1) where {F,G}
    JitteredHMC(logdensity, gradient, nothing, step_size, steps; jitter)
end

function JitteredHMC(logdensity::F, gradient::G, metric::M,
        step_size::Real, steps::Integer=10; jitter::Real=0.1) where
        {F,G,M<:Union{Nothing,DiagonalMetric,DenseMetric,RankUpdateMetric}}
    ε, amount = Float64(step_size), Float64(jitter)
    isfinite(ε) && ε > 0 ||
        throw(ArgumentError("step size must be finite and positive"))
    isfinite(amount) && 0 <= amount < 1 ||
        throw(ArgumentError("jitter must lie in [0, 1)"))
    steps > 0 || throw(ArgumentError("leapfrog steps must be positive"))
    JitteredHMC{F,G,M}(
        logdensity, gradient, metric, ε, amount, Int(steps))
end

function _jittered_hmc_step!(source::Runtime.AbstractRandomSource,
        sampler::JitteredHMC, current::AbstractVector{<:Real})
    uniform = Runtime.uniform_unit!(source)
    ε = sampler.nominal_step_size * (1 + sampler.jitter * (2uniform - 1))
    if sampler.metric === nothing
        Reference.vector_hmc_step!(source, sampler.logdensity, sampler.gradient,
            ε, sampler.steps, current)
    else
        Reference.metric_hmc_step!(source, sampler.logdensity, sampler.gradient,
            ε, sampler.steps, current, metric_mass(sampler.metric))
    end
end

step(rng::AbstractRNG, sampler::JitteredHMC,
        current::AbstractVector{<:Real}) =
    _jittered_hmc_step!(Runtime.RNGSource(rng), sampler, current)

step(sampler::JitteredHMC, current::AbstractVector{<:Real}) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::JitteredHMC,
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

sample(sampler::JitteredHMC, initial::AbstractVector{<:Real}, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)

function _fixed_metric_dynamics(source::Runtime.AbstractRandomSource,
        metric, dimension::Int)
    noise = [Runtime.standard_normal!(source) for _ in 1:dimension]
    if metric === nothing
        return noise, identity
    elseif metric isa DiagonalMetric
        length(metric.mass) == dimension ||
            throw(DimensionMismatch("metric dimension"))
        momentum = sqrt.(metric.mass) .* noise
        return momentum, p -> p ./ metric.mass
    elseif metric isa Union{DenseMetric,RankUpdateMetric}
        size(metric.mass) == (dimension, dimension) ||
            throw(DimensionMismatch("metric dimension"))
        factor = cholesky(Symmetric(metric.mass)).L
        momentum = factor * noise
        return momentum, p -> factor' \ (factor \ p)
    else
        throw(ArgumentError("unsupported fixed metric"))
    end
end

"""Endpoint HMC using the symmetric tempered-leapfrog momentum schedule.

The first half of the `2 * steps` momentum-tempering operations multiply by
`sqrt(temperature)` and the second half divide by the same factor. Parameters
are fixed for the whole chain; this type performs no adaptation.
"""
struct TemperedHMC{F,G,M}
    logdensity::F
    gradient::G
    metric::M
    step_size::Float64
    steps::Int
    temperature::Float64
end

function TemperedHMC(logdensity::F, gradient::G, step_size::Real,
        steps::Integer=10; temperature::Real=1.0) where {F,G}
    TemperedHMC(logdensity, gradient, nothing, step_size, steps; temperature)
end

function TemperedHMC(logdensity::F, gradient::G, metric::M,
        step_size::Real, steps::Integer=10; temperature::Real=1.0) where
        {F,G,M<:Union{Nothing,DiagonalMetric,DenseMetric,RankUpdateMetric}}
    ε, α = Float64(step_size), Float64(temperature)
    isfinite(ε) && ε > 0 ||
        throw(ArgumentError("step size must be finite and positive"))
    isfinite(α) && α > 0 ||
        throw(ArgumentError("temperature must be finite and positive"))
    steps > 0 || throw(ArgumentError("leapfrog steps must be positive"))
    TemperedHMC{F,G,M}(logdensity, gradient, metric, ε, Int(steps), α)
end

function _tempered_hmc_step!(source::Runtime.AbstractRandomSource,
        sampler::TemperedHMC, current::AbstractVector{<:Real})
    initial = Float64.(current)
    isempty(initial) && throw(ArgumentError("position cannot be empty"))
    all(isfinite, initial) || throw(ArgumentError("position must be finite"))
    momentum, velocity = _fixed_metric_dynamics(
        source, sampler.metric, length(initial))
    initial_momentum = copy(momentum)
    position = copy(initial)
    scale = sqrt(sampler.temperature)
    for index in 1:sampler.steps
        first_counter = 2(index - 1) + 1
        momentum = first_counter <= sampler.steps ?
            momentum .* scale : momentum ./ scale
        force = Float64.(sampler.gradient(position))
        length(force) == length(position) ||
            throw(DimensionMismatch("gradient dimension"))
        all(isfinite, force) || throw(DomainError(force, "gradient must be finite"))
        momentum .-= (sampler.step_size / 2) .* force
        position .+= sampler.step_size .* velocity(momentum)
        force = Float64.(sampler.gradient(position))
        length(force) == length(position) ||
            throw(DimensionMismatch("gradient dimension"))
        all(isfinite, force) || throw(DomainError(force, "gradient must be finite"))
        momentum .-= (sampler.step_size / 2) .* force
        second_counter = first_counter + 1
        momentum = second_counter <= sampler.steps ?
            momentum .* scale : momentum ./ scale
    end
    current_logdensity = Float64(sampler.logdensity(initial))
    next_logdensity = Float64(sampler.logdensity(position))
    current_logweight = current_logdensity -
        dot(initial_momentum, velocity(initial_momentum)) / 2
    next_logweight = next_logdensity - dot(momentum, velocity(momentum)) / 2
    all(isfinite, (current_logweight, next_logweight)) ||
        throw(DomainError((current_logweight, next_logweight),
            "Hamiltonian energy must be finite"))
    log(Runtime.uniform_unit!(source)) < min(0.0, next_logweight - current_logweight) ?
        position : initial
end

step(rng::AbstractRNG, sampler::TemperedHMC,
        current::AbstractVector{<:Real}) =
    _tempered_hmc_step!(Runtime.RNGSource(rng), sampler, current)

step(sampler::TemperedHMC, current::AbstractVector{<:Real}) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::TemperedHMC,
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

sample(sampler::TemperedHMC, initial::AbstractVector{<:Real}, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)

"""Structured information from one fixed-parameter HMC transition."""
struct HMCTransition{T}
    position::T
    moved::Bool
    acceptance_rate::Float64
    hamiltonian_energy::Float64
    hamiltonian_energy_error::Float64
    max_hamiltonian_energy_error::Float64
    leapfrog_steps::Int
    tree_depth::Int
    divergent::Bool
    reached_max_depth::Bool
    termination::Symbol
    selection::Symbol
end

struct _NUTSPhase
    position::Vector{Float64}
    momentum::Vector{Float64}
    logweight::Float64
    energy::Float64
end

struct _NUTSTree
    left::_NUTSPhase
    right::_NUTSPhase
    candidate::_NUTSPhase
    momentum_sum::Vector{Float64}
    logweight::Float64
    eligible::Int
    acceptance_sum::Float64
    leapfrog_steps::Int
    max_energy_error::Float64
    stopped::Bool
    divergent::Bool
end

"""Fixed-parameter No-U-Turn Sampler.

`termination` is `:classic` or `:generalized`; `selection` is `:multinomial`
or `:slice`. The step size, metric, maximum depth, and divergence threshold are
fixed. No warmup or adaptation is performed.
"""
struct NUTS{F,G,M}
    logdensity::F
    gradient::G
    metric::M
    step_size::Float64
    max_depth::Int
    max_energy_error::Float64
    termination::Symbol
    selection::Symbol
end

function NUTS(logdensity::F, gradient::G, step_size::Real;
        metric=nothing, max_depth::Integer=10, max_energy_error::Real=1000.0,
        termination::Symbol=:generalized,
        selection::Symbol=:multinomial) where {F,G}
    metric isa Union{Nothing,DiagonalMetric,DenseMetric,RankUpdateMetric} ||
        throw(ArgumentError("unsupported fixed metric"))
    ε, Δmax = Float64(step_size), Float64(max_energy_error)
    isfinite(ε) && ε > 0 ||
        throw(ArgumentError("step size must be finite and positive"))
    max_depth > 0 || throw(ArgumentError("maximum tree depth must be positive"))
    isfinite(Δmax) && Δmax > 0 || throw(ArgumentError(
        "maximum energy error must be finite and positive"))
    termination in (:classic, :generalized) || throw(ArgumentError(
        "termination must be :classic or :generalized"))
    selection in (:multinomial, :slice) || throw(ArgumentError(
        "selection must be :multinomial or :slice"))
    NUTS{F,G,typeof(metric)}(logdensity, gradient, metric, ε,
        Int(max_depth), Δmax, termination, selection)
end

function _nuts_phase(sampler::NUTS, position, momentum, velocity)
    q, p = Float64.(position), Float64.(momentum)
    logdensity = Float64(sampler.logdensity(q))
    isfinite(logdensity) || throw(DomainError(logdensity,
        "log density must be finite"))
    energy = -logdensity + dot(p, velocity(p)) / 2
    _NUTSPhase(q, p, -energy, energy)
end

function _nuts_leapfrog(sampler::NUTS, phase::_NUTSPhase,
        direction::Int, velocity)
    ε = direction * sampler.step_size
    force = Float64.(sampler.gradient(phase.position))
    length(force) == length(phase.position) ||
        throw(DimensionMismatch("gradient dimension"))
    all(isfinite, force) || throw(DomainError(force, "gradient must be finite"))
    half = phase.momentum .- (ε / 2) .* force
    position = phase.position .+ ε .* velocity(half)
    force = Float64.(sampler.gradient(position))
    length(force) == length(position) ||
        throw(DimensionMismatch("gradient dimension"))
    all(isfinite, force) || throw(DomainError(force, "gradient must be finite"))
    momentum = half .- (ε / 2) .* force
    _nuts_phase(sampler, position, momentum, velocity)
end

function _logaddexp(left::Float64, right::Float64)
    left == -Inf && return right
    right == -Inf && return left
    top = max(left, right)
    top + log(exp(left - top) + exp(right - top))
end

function _nuts_uturn(sampler::NUTS, left::_NUTSPhase, right::_NUTSPhase,
        momentum_sum::AbstractVector{<:Real}, velocity)
    if sampler.termination === :classic
        displacement = right.position .- left.position
        dot(displacement, velocity(left.momentum)) <= 0 ||
            dot(displacement, velocity(right.momentum)) <= 0
    else
        dot(momentum_sum, velocity(left.momentum)) <= 0 ||
            dot(momentum_sum, velocity(right.momentum)) <= 0
    end
end

function _choose_subtree_candidate!(source::Runtime.AbstractRandomSource,
        selection::Symbol, left::_NUTSTree, right::_NUTSTree)
    if selection === :slice
        total = left.eligible + right.eligible
        total == 0 && return left.candidate
        right.eligible > 0 && Runtime.uniform_unit!(source) < right.eligible / total ?
            right.candidate : left.candidate
    else
        total = _logaddexp(left.logweight, right.logweight)
        right.logweight > -Inf &&
                log(Runtime.uniform_unit!(source)) < right.logweight - total ?
            right.candidate : left.candidate
    end
end

function _combine_nuts_trees!(source::Runtime.AbstractRandomSource,
        sampler::NUTS, left::_NUTSTree, right::_NUTSTree, velocity)
    candidate = _choose_subtree_candidate!(
        source, sampler.selection, left, right)
    momentum_sum = left.momentum_sum .+ right.momentum_sum
    stopped = left.stopped || right.stopped ||
        _nuts_uturn(sampler, left.left, right.right, momentum_sum, velocity)
    _NUTSTree(left.left, right.right, candidate, momentum_sum,
        _logaddexp(left.logweight, right.logweight),
        left.eligible + right.eligible,
        left.acceptance_sum + right.acceptance_sum,
        left.leapfrog_steps + right.leapfrog_steps,
        max(left.max_energy_error, right.max_energy_error), stopped,
        left.divergent || right.divergent)
end

function _build_nuts_tree!(source::Runtime.AbstractRandomSource,
        sampler::NUTS, start::_NUTSPhase, direction::Int, depth::Int,
        initial_energy::Float64, log_slice::Float64, velocity)
    if depth == 0
        next = _nuts_leapfrog(sampler, start, direction, velocity)
        error = next.energy - initial_energy
        divergent = !isfinite(error) || error > sampler.max_energy_error
        eligible = sampler.selection === :slice ?
            Int(!divergent && next.logweight >= log_slice) : Int(!divergent)
        logweight = sampler.selection === :multinomial && !divergent ?
            next.logweight : -Inf
        _NUTSTree(next, next, next, copy(next.momentum), logweight, eligible,
            exp(min(0.0, -error)), 1, abs(error), divergent, divergent)
    else
        first = _build_nuts_tree!(source, sampler, start, direction, depth - 1,
            initial_energy, log_slice, velocity)
        first.stopped && return first
        second_start = direction < 0 ? first.left : first.right
        second = _build_nuts_tree!(source, sampler, second_start, direction,
            depth - 1, initial_energy, log_slice, velocity)
        direction < 0 ?
            _combine_nuts_trees!(source, sampler, second, first, velocity) :
            _combine_nuts_trees!(source, sampler, first, second, velocity)
    end
end

function transition(rng::AbstractRNG, sampler::NUTS,
        current::AbstractVector{<:Real})
    source = Runtime.RNGSource(rng)
    initial = Float64.(current)
    isempty(initial) && throw(ArgumentError("position cannot be empty"))
    all(isfinite, initial) || throw(ArgumentError("position must be finite"))
    momentum, velocity = _fixed_metric_dynamics(
        source, sampler.metric, length(initial))
    initial_phase = _nuts_phase(sampler, initial, momentum, velocity)
    log_slice = sampler.selection === :slice ?
        initial_phase.logweight + log(Runtime.uniform_unit!(source)) : -Inf
    tree = _NUTSTree(initial_phase, initial_phase, initial_phase,
        copy(initial_phase.momentum), initial_phase.logweight, 1,
        0.0, 0, 0.0, false, false)
    depth = 0
    while !tree.stopped && depth < sampler.max_depth
        direction = Runtime.draw_below!(source, 2) == 0 ? -1 : 1
        start = direction < 0 ? tree.left : tree.right
        subtree = _build_nuts_tree!(source, sampler, start, direction, depth,
            initial_phase.energy, log_slice, velocity)
        if !subtree.stopped
            tree = direction < 0 ?
                _combine_nuts_trees!(source, sampler, subtree, tree, velocity) :
                _combine_nuts_trees!(source, sampler, tree, subtree, velocity)
        else
            tree = _NUTSTree(
                direction < 0 ? subtree.left : tree.left,
                direction < 0 ? tree.right : subtree.right,
                tree.candidate, tree.momentum_sum .+ subtree.momentum_sum,
                tree.logweight, tree.eligible,
                tree.acceptance_sum + subtree.acceptance_sum,
                tree.leapfrog_steps + subtree.leapfrog_steps,
                max(tree.max_energy_error, subtree.max_energy_error), true,
                tree.divergent || subtree.divergent)
        end
        depth += 1
    end
    selected = tree.candidate
    acceptance_rate = tree.leapfrog_steps == 0 ? 1.0 :
        tree.acceptance_sum / tree.leapfrog_steps
    selected_error = selected.energy - initial_phase.energy
    HMCTransition(copy(selected.position), selected.position != initial,
        acceptance_rate, selected.energy, selected_error,
        tree.max_energy_error, tree.leapfrog_steps, depth, tree.divergent,
        depth == sampler.max_depth && !tree.stopped,
        sampler.termination, sampler.selection)
end

transition(sampler::NUTS, current::AbstractVector{<:Real}) =
    transition(Random.default_rng(), sampler, current)

step(rng::AbstractRNG, sampler::NUTS, current::AbstractVector{<:Real}) =
    transition(rng, sampler, current).position

step(sampler::NUTS, current::AbstractVector{<:Real}) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::NUTS,
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

sample(sampler::NUTS, initial::AbstractVector{<:Real}, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)

function sample_with_diagnostics(rng::AbstractRNG, sampler::NUTS,
        initial::AbstractVector{<:Real}, count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    current = Float64.(initial)
    samples = Matrix{Float64}(undef, length(current), count)
    diagnostics = Vector{HMCTransition{Vector{Float64}}}(undef, count)
    for index in axes(samples, 2)
        result = transition(rng, sampler, current)
        current = result.position
        samples[:, index] = current
        diagnostics[index] = result
    end
    (; samples, diagnostics)
end

sample_with_diagnostics(sampler::NUTS,
        initial::AbstractVector{<:Real}, count::Integer) =
    sample_with_diagnostics(Random.default_rng(), sampler, initial, count)

"""Position and retained momentum for generalized HMC refreshment."""
struct HMCPhaseState
    position::Vector{Float64}
    momentum::Vector{Float64}
end

"""A partial-momentum transition and its endpoint-HMC diagnostics."""
struct PartialMomentumTransition
    state::HMCPhaseState
    diagnostics::HMCTransition{Vector{Float64}}
end

"""Fixed-step endpoint HMC with persistent, partially refreshed momentum.

Before each trajectory, `p` is replaced by
`refresh * p + sqrt(1-refresh^2) * G`, with `G` drawn from the fixed metric's
Gaussian momentum law. After accept/reject, momentum is negated to preserve
the reversible generalized-HMC convention.
"""
struct PartialMomentumHMC{F,G,M}
    logdensity::F
    gradient::G
    metric::M
    step_size::Float64
    steps::Int
    refresh::Float64
end

function PartialMomentumHMC(logdensity::F, gradient::G, step_size::Real,
        steps::Integer=10; refresh::Real=0.9, metric=nothing) where {F,G}
    metric isa Union{Nothing,DiagonalMetric,DenseMetric,RankUpdateMetric} ||
        throw(ArgumentError("unsupported fixed metric"))
    ε, α = Float64(step_size), Float64(refresh)
    isfinite(ε) && ε > 0 ||
        throw(ArgumentError("step size must be finite and positive"))
    isfinite(α) && 0 <= α <= 1 ||
        throw(ArgumentError("momentum refresh rate must lie in [0, 1]"))
    steps > 0 || throw(ArgumentError("leapfrog steps must be positive"))
    PartialMomentumHMC{F,G,typeof(metric)}(
        logdensity, gradient, metric, ε, Int(steps), α)
end

function initialize_phase(rng::AbstractRNG, sampler::PartialMomentumHMC,
        position::AbstractVector{<:Real})
    q = Float64.(position)
    isempty(q) && throw(ArgumentError("position cannot be empty"))
    all(isfinite, q) || throw(ArgumentError("position must be finite"))
    momentum, _ = _fixed_metric_dynamics(
        Runtime.RNGSource(rng), sampler.metric, length(q))
    HMCPhaseState(q, momentum)
end

initialize_phase(sampler::PartialMomentumHMC,
        position::AbstractVector{<:Real}) =
    initialize_phase(Random.default_rng(), sampler, position)

function _partial_momentum_transition!(source::Runtime.AbstractRandomSource,
        sampler::PartialMomentumHMC, state::HMCPhaseState)
    q0, retained = copy(state.position), copy(state.momentum)
    length(q0) == length(retained) || throw(DimensionMismatch("phase state"))
    fresh, velocity = _fixed_metric_dynamics(source, sampler.metric, length(q0))
    p0 = sampler.refresh .* retained .+
        sqrt(1 - sampler.refresh^2) .* fresh
    q, p = copy(q0), copy(p0)
    for _ in 1:sampler.steps
        force = Float64.(sampler.gradient(q))
        length(force) == length(q) || throw(DimensionMismatch("gradient dimension"))
        all(isfinite, force) || throw(DomainError(force, "gradient must be finite"))
        half = p .- (sampler.step_size / 2) .* force
        q = q .+ sampler.step_size .* velocity(half)
        force = Float64.(sampler.gradient(q))
        length(force) == length(q) || throw(DimensionMismatch("gradient dimension"))
        all(isfinite, force) || throw(DomainError(force, "gradient must be finite"))
        p = half .- (sampler.step_size / 2) .* force
    end
    initial_energy = -Float64(sampler.logdensity(q0)) + dot(p0, velocity(p0)) / 2
    proposed_energy = -Float64(sampler.logdensity(q)) + dot(p, velocity(p)) / 2
    error = proposed_energy - initial_energy
    acceptance = exp(min(0.0, -error))
    accepted = Runtime.uniform_unit!(source) < acceptance
    next_position = accepted ? q : q0
    next_momentum = -(accepted ? p : p0)
    selected_energy = accepted ? proposed_energy : initial_energy
    diagnostics = HMCTransition(copy(next_position), accepted,
        acceptance, selected_energy, selected_energy - initial_energy,
        abs(error), sampler.steps, 0, !isfinite(error), false,
        :fixed_steps, :endpoint)
    PartialMomentumTransition(
        HMCPhaseState(copy(next_position), copy(next_momentum)), diagnostics)
end

transition(rng::AbstractRNG, sampler::PartialMomentumHMC,
        state::HMCPhaseState) = _partial_momentum_transition!(
    Runtime.RNGSource(rng), sampler, state)

transition(sampler::PartialMomentumHMC, state::HMCPhaseState) =
    transition(Random.default_rng(), sampler, state)

step(rng::AbstractRNG, sampler::PartialMomentumHMC, state::HMCPhaseState) =
    transition(rng, sampler, state).state

step(sampler::PartialMomentumHMC, state::HMCPhaseState) =
    step(Random.default_rng(), sampler, state)

function sample(rng::AbstractRNG, sampler::PartialMomentumHMC,
        initial::AbstractVector{<:Real}, count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    state = initialize_phase(rng, sampler, initial)
    samples = Matrix{Float64}(undef, length(state.position), count)
    for index in axes(samples, 2)
        state = step(rng, sampler, state)
        samples[:, index] = state.position
    end
    samples
end

sample(sampler::PartialMomentumHMC,
        initial::AbstractVector{<:Real}, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)
