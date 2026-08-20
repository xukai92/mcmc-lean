#=
This file is included into the `VerifiedSamplers` module after the core HMC
types have been defined. It contains production-shaped, fixed-parameter HMC
variants whose semantics reuse those established transition implementations.
=#

_check_metric_eltype(::Nothing, ::Type{T}) where {T<:AbstractFloat} = nothing
function _check_metric_eltype(metric, ::Type{T}) where {T<:AbstractFloat}
    eltype(metric.mass) === T || throw(ArgumentError(
        "sampler and metric element types must match"))
    nothing
end

struct _FixedOptimizedHMC{F,G,M,T<:AbstractFloat}
    logdensity::F
    gradient::G
    metric::M
    step_size::T
    steps::Int
end

function step(rng::AbstractRNG, sampler::_FixedOptimizedHMC{F,G,M,T},
        current::AbstractVector{T}) where {F,G,M,T}
    source = Runtime.RNGSource(rng)
    sampler.metric === nothing ?
        Optimized.vector_hmc_step!(source, sampler.logdensity,
            sampler.gradient, sampler.step_size, sampler.steps, current) :
        Optimized.metric_hmc_step!(source, sampler.logdensity,
            sampler.gradient, sampler.step_size, sampler.steps, current,
            Optimized.prepare_metric(metric_mass(sampler.metric)))
end

function sample(rng::AbstractRNG, sampler::_FixedOptimizedHMC,
        initial::AbstractVector{T}, count::Integer) where {T<:AbstractFloat}
    current = collect(initial)
    samples = Matrix{T}(undef, length(initial), count)
    for index in axes(samples, 2)
        current = step(rng, sampler, current)
        samples[:, index] = current
    end
    samples
end

"""Endpoint HMC terminated by a fixed integration time.

The number of leapfrog updates is `floor(integration_time / step_size)`,
with a minimum of one, matching AdvancedHMC's fixed-integration-time
termination rule. This is a fixed-parameter sampler; it performs no step-size
or metric adaptation.
"""
struct FixedIntegrationTimeHMC{S,T<:AbstractFloat}
    sampler::S
    integration_time::T
    steps::Int
end

function _fixed_integration_steps(step_size::T, integration_time::T) where {T<:AbstractFloat}
    ε, λ = step_size, integration_time
    isfinite(ε) && ε > 0 ||
        throw(ArgumentError("step size must be finite and positive"))
    isfinite(λ) && λ > 0 ||
        throw(ArgumentError("integration time must be finite and positive"))
    steps = max(1, floor(Int, λ / ε))
    ε, λ, steps
end

function FixedIntegrationTimeHMC(logdensity::F, gradient::G,
        step_size::T, integration_time::T;
        integrator::Symbol=:leapfrog, jitter::T=T(0.1),
        temperature::T=one(T)) where {F,G,T<:AbstractFloat}
    ε, λ, steps = _fixed_integration_steps(step_size, integration_time)
    kind, amount, tempering =
        _hmc_integrator_parameters(integrator, jitter, temperature)
    fixed = if kind === :jittered
        JitteredHMC(logdensity, gradient, ε, steps; jitter=amount)
    elseif kind === :tempered
        TemperedHMC(logdensity, gradient, ε, steps; temperature=tempering)
    else
        _FixedOptimizedHMC{F,G,Nothing,T}(
            logdensity, gradient, nothing, ε, steps)
    end
    FixedIntegrationTimeHMC{typeof(fixed),T}(fixed, λ, steps)
end

function FixedIntegrationTimeHMC(logdensity::F, gradient::G,
        metric::M, step_size::T, integration_time::T;
        integrator::Symbol=:leapfrog, jitter::T=T(0.1),
        temperature::T=one(T)) where
        {F,G,T<:AbstractFloat,M<:Union{DiagonalMetric,DenseMetric,RankUpdateMetric}}
    ε, λ, steps = _fixed_integration_steps(step_size, integration_time)
    kind, amount, tempering =
        _hmc_integrator_parameters(integrator, jitter, temperature)
    fixed = if kind === :jittered
        JitteredHMC(logdensity, gradient, metric, ε, steps; jitter=amount)
    elseif kind === :tempered
        TemperedHMC(logdensity, gradient, metric, ε, steps;
            temperature=tempering)
    else
        _FixedOptimizedHMC{F,G,M,T}(
            logdensity, gradient, metric, ε, steps)
    end
    FixedIntegrationTimeHMC{typeof(fixed),T}(fixed, λ, steps)
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
struct JitteredHMC{F,G,M,T<:AbstractFloat}
    logdensity::F
    gradient::G
    metric::M
    nominal_step_size::T
    jitter::T
    steps::Int
end

function JitteredHMC(logdensity::F, gradient::G, step_size::T,
        steps::Integer=10; jitter::T=T(0.1)) where {F,G,T<:AbstractFloat}
    JitteredHMC(logdensity, gradient, nothing, step_size, steps; jitter)
end

function JitteredHMC(logdensity::F, gradient::G, metric::M,
        step_size::T, steps::Integer=10; jitter::T=T(0.1)) where
        {F,G,T<:AbstractFloat,M<:Union{Nothing,DiagonalMetric,DenseMetric,RankUpdateMetric}}
    ε, amount = step_size, jitter
    _check_metric_eltype(metric, T)
    isfinite(ε) && ε > 0 ||
        throw(ArgumentError("step size must be finite and positive"))
    isfinite(amount) && 0 <= amount < 1 ||
        throw(ArgumentError("jitter must lie in [0, 1)"))
    steps > 0 || throw(ArgumentError("leapfrog steps must be positive"))
    JitteredHMC{F,G,M,T}(
        logdensity, gradient, metric, ε, amount, Int(steps))
end

function _jittered_hmc_step!(source::Runtime.AbstractRandomSource,
        sampler::JitteredHMC{F,G,M,T}, current::AbstractVector{T}) where {F,G,M,T}
    uniform = T(Runtime.uniform_unit!(source))
    ε = sampler.nominal_step_size * (one(T) + sampler.jitter * (T(2)*uniform - one(T)))
    if sampler.metric === nothing
        Optimized.vector_hmc_step!(source, sampler.logdensity, sampler.gradient,
            ε, sampler.steps, current)
    else
        Optimized.metric_hmc_step!(source, sampler.logdensity, sampler.gradient,
            ε, sampler.steps, current,
            Optimized.prepare_metric(metric_mass(sampler.metric)))
    end
end

step(rng::AbstractRNG, sampler::JitteredHMC,
        current::AbstractVector{T}) where {T<:AbstractFloat} =
    _jittered_hmc_step!(Runtime.RNGSource(rng), sampler, current)

step(sampler::JitteredHMC, current::AbstractVector{T}) where {T<:AbstractFloat} =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::JitteredHMC,
        initial::AbstractVector{T}, count::Integer) where {T<:AbstractFloat}
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    current = collect(initial)
    samples = Matrix{T}(undef, length(current), count)
    for index in axes(samples, 2)
        current = step(rng, sampler, current)
        samples[:, index] = current
    end
    samples
end

sample(sampler::JitteredHMC, initial::AbstractVector{T}, count::Integer) where {T<:AbstractFloat} =
    sample(Random.default_rng(), sampler, initial, count)

function _fixed_metric_dynamics(source::Runtime.AbstractRandomSource,
        metric, dimension::Int, ::Type{T}) where {T<:AbstractFloat}
    noise = T[Runtime.standard_normal!(source) for _ in 1:dimension]
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
struct TemperedHMC{F,G,M,T<:AbstractFloat}
    logdensity::F
    gradient::G
    metric::M
    step_size::T
    steps::Int
    temperature::T
end

function TemperedHMC(logdensity::F, gradient::G, step_size::T,
        steps::Integer=10; temperature::T=one(T)) where {F,G,T<:AbstractFloat}
    TemperedHMC(logdensity, gradient, nothing, step_size, steps; temperature)
end

function TemperedHMC(logdensity::F, gradient::G, metric::M,
        step_size::T, steps::Integer=10; temperature::T=one(T)) where
        {F,G,T<:AbstractFloat,M<:Union{Nothing,DiagonalMetric,DenseMetric,RankUpdateMetric}}
    ε, α = step_size, temperature
    _check_metric_eltype(metric, T)
    isfinite(ε) && ε > 0 ||
        throw(ArgumentError("step size must be finite and positive"))
    isfinite(α) && α > 0 ||
        throw(ArgumentError("temperature must be finite and positive"))
    steps > 0 || throw(ArgumentError("leapfrog steps must be positive"))
    TemperedHMC{F,G,M,T}(logdensity, gradient, metric, ε, Int(steps), α)
end

function _tempered_hmc_step!(source::Runtime.AbstractRandomSource,
        sampler::TemperedHMC{F,G,M,T}, current::AbstractVector{T}) where {F,G,M,T}
    initial = collect(current)
    isempty(initial) && throw(ArgumentError("position cannot be empty"))
    all(isfinite, initial) || throw(ArgumentError("position must be finite"))
    momentum, velocity = _fixed_metric_dynamics(
        source, sampler.metric, length(initial), T)
    initial_momentum = copy(momentum)
    position = copy(initial)
    scale = sqrt(sampler.temperature)
    for index in 1:sampler.steps
        first_counter = 2(index - 1) + 1
        momentum = first_counter <= sampler.steps ?
            momentum .* scale : momentum ./ scale
        force = T.(sampler.gradient(position))
        length(force) == length(position) ||
            throw(DimensionMismatch("gradient dimension"))
        all(isfinite, force) || throw(DomainError(force, "gradient must be finite"))
        momentum .-= (sampler.step_size / 2) .* force
        position .+= sampler.step_size .* velocity(momentum)
        force = T.(sampler.gradient(position))
        length(force) == length(position) ||
            throw(DimensionMismatch("gradient dimension"))
        all(isfinite, force) || throw(DomainError(force, "gradient must be finite"))
        momentum .-= (sampler.step_size / 2) .* force
        second_counter = first_counter + 1
        momentum = second_counter <= sampler.steps ?
            momentum .* scale : momentum ./ scale
    end
    current_logdensity = T(sampler.logdensity(initial))
    next_logdensity = T(sampler.logdensity(position))
    current_logweight = current_logdensity -
        dot(initial_momentum, velocity(initial_momentum)) / 2
    next_logweight = next_logdensity - dot(momentum, velocity(momentum)) / 2
    all(isfinite, (current_logweight, next_logweight)) ||
        throw(DomainError((current_logweight, next_logweight),
            "Hamiltonian energy must be finite"))
    log(T(Runtime.uniform_unit!(source))) < min(zero(T), next_logweight - current_logweight) ?
        position : initial
end

step(rng::AbstractRNG, sampler::TemperedHMC,
        current::AbstractVector{T}) where {T<:AbstractFloat} =
    _tempered_hmc_step!(Runtime.RNGSource(rng), sampler, current)

step(sampler::TemperedHMC, current::AbstractVector{T}) where {T<:AbstractFloat} =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::TemperedHMC,
        initial::AbstractVector{T}, count::Integer) where {T<:AbstractFloat}
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    current = collect(initial)
    samples = Matrix{T}(undef, length(current), count)
    for index in axes(samples, 2)
        current = step(rng, sampler, current)
        samples[:, index] = current
    end
    samples
end

sample(sampler::TemperedHMC, initial::AbstractVector{T}, count::Integer) where {T<:AbstractFloat} =
    sample(Random.default_rng(), sampler, initial, count)

"""Structured information from one fixed-parameter HMC transition."""
struct HMCTransition{P,T<:AbstractFloat}
    position::P
    moved::Bool
    acceptance_rate::T
    hamiltonian_energy::T
    hamiltonian_energy_error::T
    max_hamiltonian_energy_error::T
    leapfrog_steps::Int
    tree_depth::Int
    divergent::Bool
    reached_max_depth::Bool
    termination::Symbol
    selection::Symbol
end

struct _NUTSPhase{T<:AbstractFloat}
    position::Vector{T}
    momentum::Vector{T}
    logweight::T
    energy::T
end

struct _NUTSTree{T<:AbstractFloat}
    left::_NUTSPhase{T}
    right::_NUTSPhase{T}
    candidate::_NUTSPhase{T}
    momentum_sum::Vector{T}
    logweight::T
    eligible::Int
    acceptance_sum::T
    leapfrog_steps::Int
    max_energy_error::T
    stopped::Bool
    divergent::Bool
end

"""Fixed-parameter No-U-Turn Sampler.

`termination` is `:classic`, `:generalized`, or `:strict_generalized`;
`selection` is `:multinomial` or `:slice`; `integrator` is `:leapfrog`,
`:jittered`, or `:tempered`.
Jitter is realized once per trajectory, while tempering wraps each one-step
dynamic-tree leaf in the symmetric half-temper schedule. The nominal step size,
metric, maximum depth, and divergence threshold are fixed. No warmup or
adaptation is performed.
"""
struct OptimizedNUTS{F,G,M,T<:AbstractFloat}
    logdensity::F
    gradient::G
    metric::M
    step_size::T
    max_depth::Int
    max_energy_error::T
    termination::Symbol
    selection::Symbol
    integrator::Symbol
    jitter::T
    temperature::T
end

function OptimizedNUTS(logdensity::F, gradient::G, step_size::T;
        metric=nothing, max_depth::Integer=10, max_energy_error::T=T(1000),
        termination::Symbol=:generalized,
        selection::Symbol=:multinomial, integrator::Symbol=:leapfrog,
        jitter::T=T(0.1), temperature::T=one(T)) where {F,G,T<:AbstractFloat}
    metric isa Union{Nothing,DiagonalMetric,DenseMetric,RankUpdateMetric} ||
        throw(ArgumentError("unsupported fixed metric"))
    _check_metric_eltype(metric, T)
    ε, Δmax = step_size, max_energy_error
    kind, jitter_amount, tempering =
        _hmc_integrator_parameters(integrator, jitter, temperature)
    isfinite(ε) && ε > 0 ||
        throw(ArgumentError("step size must be finite and positive"))
    max_depth > 0 || throw(ArgumentError("maximum tree depth must be positive"))
    isfinite(Δmax) && Δmax > 0 || throw(ArgumentError(
        "maximum energy error must be finite and positive"))
    termination in (:classic, :generalized, :strict_generalized) ||
        throw(ArgumentError(
            "termination must be :classic, :generalized, or " *
            ":strict_generalized"))
    selection in (:multinomial, :slice) || throw(ArgumentError(
        "selection must be :multinomial or :slice"))
    OptimizedNUTS{F,G,typeof(metric),T}(logdensity, gradient, metric, ε,
        Int(max_depth), Δmax, termination, selection, kind,
        jitter_amount, tempering)
end

function _nuts_step_size!(source::Runtime.AbstractRandomSource, sampler::OptimizedNUTS{F,G,M,T}) where {F,G,M,T}
    sampler.integrator === :jittered || return sampler.step_size
    uniform = T(Runtime.uniform_unit!(source))
    sampler.step_size * (one(T) + sampler.jitter * (T(2)*uniform - one(T)))
end

function _nuts_phase(sampler::OptimizedNUTS{F,G,M,T},
        position::Vector{T}, momentum::Vector{T}, velocity) where {F,G,M,T}
    logdensity = T(sampler.logdensity(position))
    isfinite(logdensity) || throw(DomainError(logdensity,
        "log density must be finite"))
    energy = -logdensity + dot(momentum, velocity(momentum)) / 2
    _NUTSPhase(position, momentum, -energy, energy)
end

function _nuts_phase(sampler::OptimizedNUTS{F,G,M,T}, position, momentum, velocity) where {F,G,M,T}
    q, p = T.(position), T.(momentum)
    _nuts_phase(sampler, q, p, velocity)
end

function _nuts_leapfrog(sampler::OptimizedNUTS{F,G,M,T}, phase::_NUTSPhase{T},
        direction::Int, velocity, realized_step_size::T=sampler.step_size) where {F,G,M,T}
    ε = direction * realized_step_size
    momentum = phase.momentum
    scale = sqrt(sampler.temperature)
    sampler.integrator === :tempered && (momentum = momentum .* scale)
    force = T.(sampler.gradient(phase.position))
    length(force) == length(phase.position) ||
        throw(DimensionMismatch("gradient dimension"))
    all(isfinite, force) || throw(DomainError(force, "gradient must be finite"))
    half = momentum .- (ε / 2) .* force
    position = phase.position .+ ε .* velocity(half)
    force = T.(sampler.gradient(position))
    length(force) == length(position) ||
        throw(DimensionMismatch("gradient dimension"))
    all(isfinite, force) || throw(DomainError(force, "gradient must be finite"))
    momentum = half .- (ε / 2) .* force
    sampler.integrator === :tempered && (momentum = momentum ./ scale)
    _nuts_phase(sampler, position, momentum, velocity)
end

function _logaddexp(left::T, right::T) where {T<:AbstractFloat}
    left == -Inf && return right
    right == -Inf && return left
    top = max(left, right)
    top + log(exp(left - top) + exp(right - top))
end

_maxabs(left::T, right::T) where {T<:AbstractFloat} =
    abs(left) > abs(right) ? left : right

function _nuts_uturn_generalized(left::_NUTSPhase{T}, right::_NUTSPhase{T},
        momentum_sum::AbstractVector{T}, velocity) where {T<:AbstractFloat}
    dot(momentum_sum, velocity(left.momentum)) <= 0 ||
        dot(momentum_sum, velocity(right.momentum)) <= 0
end

function _nuts_uturn(sampler::OptimizedNUTS, left::_NUTSPhase{T}, right::_NUTSPhase{T},
        momentum_sum::AbstractVector{T}, velocity) where {T<:AbstractFloat}
    if sampler.termination === :classic
        displacement = right.position .- left.position
        dot(displacement, velocity(left.momentum)) <= 0 ||
            dot(displacement, velocity(right.momentum)) <= 0
    else
        _nuts_uturn_generalized(left, right, momentum_sum, velocity)
    end
end

function _strict_nuts_uturn(left::_NUTSTree, right::_NUTSTree,
        velocity)
    combined_sum = left.momentum_sum .+ right.momentum_sum
    _nuts_uturn_generalized(
        left.left, right.right, combined_sum, velocity) ||
        _nuts_uturn_generalized(left.left, right.left,
            left.momentum_sum .+ right.left.momentum, velocity) ||
        _nuts_uturn_generalized(left.right, right.right,
            left.right.momentum .+ right.momentum_sum, velocity)
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

function _combine_nuts_trees(sampler::OptimizedNUTS, left::_NUTSTree,
        right::_NUTSTree, velocity, candidate::_NUTSPhase)
    momentum_sum = left.momentum_sum .+ right.momentum_sum
    turned = sampler.termination === :strict_generalized ?
        _strict_nuts_uturn(left, right, velocity) :
        _nuts_uturn(sampler, left.left, right.right, momentum_sum, velocity)
    stopped = left.stopped || right.stopped || turned
    _NUTSTree(left.left, right.right, candidate, momentum_sum,
        _logaddexp(left.logweight, right.logweight),
        left.eligible + right.eligible,
        left.acceptance_sum + right.acceptance_sum,
        left.leapfrog_steps + right.leapfrog_steps,
        _maxabs(left.max_energy_error, right.max_energy_error), stopped,
        left.divergent || right.divergent)
end

function _combine_nuts_trees!(source::Runtime.AbstractRandomSource,
        sampler::OptimizedNUTS, left::_NUTSTree, right::_NUTSTree, velocity)
    candidate = _choose_subtree_candidate!(
        source, sampler.selection, left, right)
    _combine_nuts_trees(sampler, left, right, velocity, candidate)
end

function _choose_outer_candidate!(source::Runtime.AbstractRandomSource,
        selection::Symbol, current::_NUTSTree, subtree::_NUTSTree)
    accept = if selection === :slice
        current.eligible * Runtime.uniform_unit!(source) < subtree.eligible
    else
        log(Runtime.uniform_unit!(source)) <
            subtree.logweight - current.logweight
    end
    accept ? subtree.candidate : current.candidate
end

function _build_nuts_tree!(source::Runtime.AbstractRandomSource,
        sampler::OptimizedNUTS{F,G,M,T}, start::_NUTSPhase{T}, direction::Int, depth::Int,
        initial_energy::T, log_slice::T, velocity,
        realized_step_size::T=sampler.step_size) where {F,G,M,T}
    if depth == 0
        next = _nuts_leapfrog(
            sampler, start, direction, velocity, realized_step_size)
        error = next.energy - initial_energy
        divergent = if sampler.selection === :slice
            !isfinite(error) || !(log_slice < sampler.max_energy_error + next.logweight)
        else
            !isfinite(error) || !(error < sampler.max_energy_error)
        end
        eligible = sampler.selection === :slice ?
            Int(!divergent && next.logweight >= log_slice) : Int(!divergent)
        logweight = sampler.selection === :multinomial && !divergent ?
            next.logweight : T(-Inf)
        _NUTSTree(next, next, next, copy(next.momentum), logweight, eligible,
            exp(min(zero(T), -error)), 1, error, divergent, divergent)
    else
        first = _build_nuts_tree!(source, sampler, start, direction, depth - 1,
            initial_energy, log_slice, velocity, realized_step_size)
        first.stopped && return first
        second_start = direction < 0 ? first.left : first.right
        second = _build_nuts_tree!(source, sampler, second_start, direction,
            depth - 1, initial_energy, log_slice, velocity, realized_step_size)
        direction < 0 ?
            _combine_nuts_trees!(source, sampler, second, first, velocity) :
            _combine_nuts_trees!(source, sampler, first, second, velocity)
    end
end

function transition(rng::AbstractRNG, sampler::OptimizedNUTS{F,G,M,T},
        current::AbstractVector{T}) where {F,G,M,T}
    source = Runtime.RNGSource(rng)
    initial = collect(current)
    isempty(initial) && throw(ArgumentError("position cannot be empty"))
    all(isfinite, initial) || throw(ArgumentError("position must be finite"))
    realized_step_size = _nuts_step_size!(source, sampler)
    momentum, velocity = _fixed_metric_dynamics(
        source, sampler.metric, length(initial), T)
    initial_phase = _nuts_phase(sampler, initial, momentum, velocity)
    log_slice = sampler.selection === :slice ?
        initial_phase.logweight + log(T(Runtime.uniform_unit!(source))) : T(-Inf)
    tree = _NUTSTree(initial_phase, initial_phase, initial_phase,
        copy(initial_phase.momentum), initial_phase.logweight, 1,
        zero(T), 0, zero(T), false, false)
    depth = 0
    while !tree.stopped && depth < sampler.max_depth
        direction = Runtime.draw_below!(source, 2) == 0 ? -1 : 1
        start = direction < 0 ? tree.left : tree.right
        subtree = _build_nuts_tree!(source, sampler, start, direction, depth,
            initial_phase.energy, log_slice, velocity, realized_step_size)
        if !subtree.stopped
            candidate = _choose_outer_candidate!(
                source, sampler.selection, tree, subtree)
            tree = direction < 0 ?
                _combine_nuts_trees(
                    sampler, subtree, tree, velocity, candidate) :
                _combine_nuts_trees(
                    sampler, tree, subtree, velocity, candidate)
            depth += 1
        else
            tree = _NUTSTree(
                direction < 0 ? subtree.left : tree.left,
                direction < 0 ? tree.right : subtree.right,
                tree.candidate, tree.momentum_sum .+ subtree.momentum_sum,
                tree.logweight, tree.eligible,
                tree.acceptance_sum + subtree.acceptance_sum,
                tree.leapfrog_steps + subtree.leapfrog_steps,
                _maxabs(tree.max_energy_error, subtree.max_energy_error), true,
                tree.divergent || subtree.divergent)
        end
    end
    selected = tree.candidate
    acceptance_rate = tree.leapfrog_steps == 0 ? one(T) :
        tree.acceptance_sum / tree.leapfrog_steps
    selected_error = selected.energy - initial_phase.energy
    HMCTransition(copy(selected.position), selected.position != initial,
        acceptance_rate, selected.energy, selected_error,
        tree.max_energy_error, tree.leapfrog_steps, depth, tree.divergent,
        depth == sampler.max_depth && !tree.stopped,
        sampler.termination, sampler.selection)
end

transition(sampler::OptimizedNUTS, current::AbstractVector{T}) where {T<:AbstractFloat} =
    transition(Random.default_rng(), sampler, current)

step(rng::AbstractRNG, sampler::OptimizedNUTS, current::AbstractVector{T}) where {T<:AbstractFloat} =
    transition(rng, sampler, current).position

step(sampler::OptimizedNUTS, current::AbstractVector{T}) where {T<:AbstractFloat} =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::OptimizedNUTS,
        initial::AbstractVector{T}, count::Integer) where {T<:AbstractFloat}
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    current = collect(initial)
    samples = Matrix{T}(undef, length(current), count)
    for index in axes(samples, 2)
        current = step(rng, sampler, current)
        samples[:, index] = current
    end
    samples
end

sample(sampler::OptimizedNUTS, initial::AbstractVector{T}, count::Integer) where {T<:AbstractFloat} =
    sample(Random.default_rng(), sampler, initial, count)

function sample_with_diagnostics(rng::AbstractRNG, sampler::OptimizedNUTS,
        initial::AbstractVector{T}, count::Integer) where {T<:AbstractFloat}
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    current = collect(initial)
    samples = Matrix{T}(undef, length(current), count)
    diagnostics = Vector{HMCTransition{Vector{T},T}}(undef, count)
    for index in axes(samples, 2)
        result = transition(rng, sampler, current)
        current = result.position
        samples[:, index] = current
        diagnostics[index] = result
    end
    (; samples, diagnostics)
end

sample_with_diagnostics(sampler::OptimizedNUTS,
        initial::AbstractVector{T}, count::Integer) where {T<:AbstractFloat} =
    sample_with_diagnostics(Random.default_rng(), sampler, initial, count)

"""Position and retained momentum for generalized HMC refreshment."""
struct HMCPhaseState{T<:AbstractFloat}
    position::Vector{T}
    momentum::Vector{T}
end

"""A partial-momentum transition and its endpoint-HMC diagnostics."""
struct PartialMomentumTransition{T<:AbstractFloat}
    state::HMCPhaseState{T}
    diagnostics::HMCTransition{Vector{T},T}
end

"""Fixed-step endpoint HMC with persistent, partially refreshed momentum.

Before each trajectory, `p` is replaced by
`refresh * p + sqrt(1-refresh^2) * G`, with `G` drawn from the fixed metric's
Gaussian momentum law. After accept/reject, momentum is negated to preserve
the reversible generalized-HMC convention.
"""
struct PartialMomentumHMC{F,G,M,T<:AbstractFloat}
    logdensity::F
    gradient::G
    metric::M
    step_size::T
    steps::Int
    refresh::T
end

function PartialMomentumHMC(logdensity::F, gradient::G, step_size::T,
        steps::Integer=10; refresh::T=T(0.9), metric=nothing) where {F,G,T<:AbstractFloat}
    metric isa Union{Nothing,DiagonalMetric,DenseMetric,RankUpdateMetric} ||
        throw(ArgumentError("unsupported fixed metric"))
    _check_metric_eltype(metric, T)
    ε, α = step_size, refresh
    isfinite(ε) && ε > 0 ||
        throw(ArgumentError("step size must be finite and positive"))
    isfinite(α) && 0 <= α <= 1 ||
        throw(ArgumentError("momentum refresh rate must lie in [0, 1]"))
    steps > 0 || throw(ArgumentError("leapfrog steps must be positive"))
    PartialMomentumHMC{F,G,typeof(metric),T}(
        logdensity, gradient, metric, ε, Int(steps), α)
end

function initialize_phase(rng::AbstractRNG, sampler::PartialMomentumHMC{F,G,M,T},
        position::AbstractVector{T}) where {F,G,M,T}
    q = collect(position)
    isempty(q) && throw(ArgumentError("position cannot be empty"))
    all(isfinite, q) || throw(ArgumentError("position must be finite"))
    momentum, _ = _fixed_metric_dynamics(
        Runtime.RNGSource(rng), sampler.metric, length(q), T)
    HMCPhaseState(q, momentum)
end

initialize_phase(sampler::PartialMomentumHMC,
        position::AbstractVector{T}) where {T<:AbstractFloat} =
    initialize_phase(Random.default_rng(), sampler, position)

function _partial_momentum_transition!(source::Runtime.AbstractRandomSource,
        sampler::PartialMomentumHMC{F,G,M,T}, state::HMCPhaseState{T}) where {F,G,M,T}
    q0, retained = copy(state.position), copy(state.momentum)
    length(q0) == length(retained) || throw(DimensionMismatch("phase state"))
    fresh, velocity = _fixed_metric_dynamics(source, sampler.metric, length(q0), T)
    p0 = sampler.refresh .* retained .+
        sqrt(one(T) - sampler.refresh^2) .* fresh
    q, p = copy(q0), copy(p0)
    for _ in 1:sampler.steps
        force = T.(sampler.gradient(q))
        length(force) == length(q) || throw(DimensionMismatch("gradient dimension"))
        all(isfinite, force) || throw(DomainError(force, "gradient must be finite"))
        half = p .- (sampler.step_size / 2) .* force
        q = q .+ sampler.step_size .* velocity(half)
        force = T.(sampler.gradient(q))
        length(force) == length(q) || throw(DimensionMismatch("gradient dimension"))
        all(isfinite, force) || throw(DomainError(force, "gradient must be finite"))
        p = half .- (sampler.step_size / 2) .* force
    end
    initial_energy = -T(sampler.logdensity(q0)) + dot(p0, velocity(p0)) / 2
    proposed_energy = -T(sampler.logdensity(q)) + dot(p, velocity(p)) / 2
    error = proposed_energy - initial_energy
    acceptance = exp(min(zero(T), -error))
    accepted = T(Runtime.uniform_unit!(source)) < acceptance
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
        initial::AbstractVector{T}, count::Integer) where {T<:AbstractFloat}
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    state = initialize_phase(rng, sampler, initial)
    samples = Matrix{T}(undef, length(state.position), count)
    for index in axes(samples, 2)
        state = step(rng, sampler, state)
        samples[:, index] = state.position
    end
    samples
end

sample(sampler::PartialMomentumHMC,
        initial::AbstractVector{T}, count::Integer) where {T<:AbstractFloat} =
    sample(Random.default_rng(), sampler, initial, count)
