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
    descriptor === nothing && throw(ArgumentError(
        "unknown generated schedule: $name"))
    operators = map(descriptor.operators) do operator
        transition = if haskey(transitions, operator.name)
            transitions[operator.name]
        elseif haskey(transitions, Symbol(operator.name))
            transitions[Symbol(operator.name)]
        else
            throw(ArgumentError(
                "missing transition for generated operator $(operator.name)"))
        end
        ScopedInferenceOperator(Symbol.(operator.scope), transition)
    end
    ComposableSampler(Symbol.(descriptor.variables), operators...)
end

"""Return a transform descriptor generated from Lean's versioned artifact."""
function generated_transform(name::AbstractString)
    descriptor = get(Reference.TRANSFORMS, String(name), nothing)
    descriptor === nothing && throw(ArgumentError(
        "unknown generated transform: $name"))
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
