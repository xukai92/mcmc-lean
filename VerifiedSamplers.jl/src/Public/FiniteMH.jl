"""Exact nonnegative proposal-row weights for a finite-state MH kernel."""
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

"""Finite-state MH sampler interpreted from the canonical generated program."""
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
    1 <= current <= state_count || throw(ArgumentError(
        "current state is out of range"))
    source = Runtime.RNGSource(rng)
    Reference.finite_mh_step!(source, sampler.target.weights,
        sampler.proposal.rows, current - 1) + 1
end

step(sampler::FiniteMH, current::Integer) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::FiniteMH, initial::Integer,
        count::Integer)
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

"""Canonical generated two-state MH example."""
struct TwoStateMH end

function step(rng::AbstractRNG, ::TwoStateMH, current::Bool)
    source = Runtime.RNGSource(rng)
    Bool(Reference.two_state_mh_step!(source, Int(current)))
end

step(sampler::TwoStateMH, current::Bool) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::TwoStateMH, initial::Bool,
        count::Integer)
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
