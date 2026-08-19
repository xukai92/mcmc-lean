#=
Public forwarding surface for the independent production-shaped NUTS engine.
Kept separate from the central sampler declarations so its test-supported
assurance boundary remains visually explicit.
=#

@eval Optimized begin
    using ..VerifiedSamplers: OptimizedNUTS

    """Handwritten production-shaped NUTS comparator.

    This runtime supports the broader fixed-parameter parity surface but is
    not identified with the checked Reference `VerifiedSamplers.NUTS`.
    """
    struct NUTS{S}
        implementation::S
    end

    NUTS(args...; kwargs...) = NUTS(OptimizedNUTS(args...; kwargs...))

    export NUTS
end

transition(rng::AbstractRNG, sampler::Optimized.NUTS, current) =
    transition(rng, sampler.implementation, current)
transition(sampler::Optimized.NUTS, current) =
    transition(sampler.implementation, current)
step(rng::AbstractRNG, sampler::Optimized.NUTS, current) =
    step(rng, sampler.implementation, current)
step(sampler::Optimized.NUTS, current) =
    step(sampler.implementation, current)
sample(rng::AbstractRNG, sampler::Optimized.NUTS, initial, count::Integer) =
    sample(rng, sampler.implementation, initial, count)
sample(sampler::Optimized.NUTS, initial, count::Integer) =
    sample(sampler.implementation, initial, count)
sample_with_diagnostics(rng::AbstractRNG, sampler::Optimized.NUTS,
        initial, count::Integer) =
    sample_with_diagnostics(rng, sampler.implementation, initial, count)
sample_with_diagnostics(sampler::Optimized.NUTS, initial, count::Integer) =
    sample_with_diagnostics(sampler.implementation, initial, count)

# Internal hooks used by the production-shaped property tests.
_nuts_step_size!(source, sampler::Optimized.NUTS) =
    _nuts_step_size!(source, sampler.implementation)
_nuts_phase(sampler::Optimized.NUTS, args...) =
    _nuts_phase(sampler.implementation, args...)
_build_nuts_tree!(source, sampler::Optimized.NUTS, args...) =
    _build_nuts_tree!(source, sampler.implementation, args...)
_combine_nuts_trees(sampler::Optimized.NUTS, args...) =
    _combine_nuts_trees(sampler.implementation, args...)
