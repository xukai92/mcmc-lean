"""Executable Xu et al. coupled HMC/RWMH mixture at fixed parameters."""
struct Xu21CoupledSampler{F,G}
    logdensity::F
    gradient::G
    step_size::Float64
    steps::Int
    rwmh_scale::Float64
    hmc_weight::Float64
    function Xu21CoupledSampler(logdensity::F, gradient::G, step_size::Real,
            steps::Integer, rwmh_scale::Real, hmc_weight::Real=0.9) where {F,G}
        ε, σ, p = Float64(step_size), Float64(rwmh_scale), Float64(hmc_weight)
        isfinite(ε) && ε > 0 || throw(ArgumentError("step size must be positive"))
        steps > 0 || throw(ArgumentError("trajectory length must be positive"))
        isfinite(σ) && σ > 0 || throw(ArgumentError("RWMH scale must be positive"))
        isfinite(p) && 0 <= p <= 1 || throw(ArgumentError(
            "HMC weight must lie in [0,1]"))
        new{F,G}(logdensity, gradient, ε, Int(steps), σ, p)
    end
end

function step(rng::AbstractRNG, sampler::Xu21CoupledSampler,
        current::Tuple{<:AbstractVector{<:Real},<:AbstractVector{<:Real}})
    Reference.xu21_coupled_step!(Runtime.RNGSource(rng), sampler.logdensity,
        sampler.gradient, sampler.step_size, sampler.steps, sampler.rwmh_scale,
        sampler.hmc_weight, current[1], current[2])
end

step(sampler::Xu21CoupledSampler, current::Tuple) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::Xu21CoupledSampler,
        initial::Tuple{<:AbstractVector{<:Real},<:AbstractVector{<:Real}},
        count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    left, right = Float64.(initial[1]), Float64.(initial[2])
    left_chain = Matrix{Float64}(undef, length(left), count)
    right_chain = similar(left_chain)
    met = falses(count)
    for index in 1:count
        left, right = step(rng, sampler, (left, right))
        left_chain[:, index], right_chain[:, index] = left, right
        met[index] = left == right
    end
    (left=left_chain, right=right_chain, met=met)
end

sample(sampler::Xu21CoupledSampler, initial::Tuple, count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)

"""First exact meeting time of the faithful Xu et al. coupled runtime.

Returns `nothing` if the supplied finite diagnostic horizon is exhausted. This
is an executable experiment helper, not a replacement for a geometric-tail
theorem.
"""
function coupled_meeting_time(rng::AbstractRNG, sampler::Xu21CoupledSampler,
        initial::Tuple{<:AbstractVector{<:Real},<:AbstractVector{<:Real}},
        max_steps::Integer)
    max_steps >= 0 || throw(ArgumentError(
        "maximum meeting horizon must be nonnegative"))
    left, right = Float64.(initial[1]), Float64.(initial[2])
    length(left) == length(right) || throw(DimensionMismatch("coupled states"))
    left == right && return 0
    for iteration in 1:max_steps
        left, right = step(rng, sampler, (left, right))
        left == right && return iteration
    end
    nothing
end

coupled_meeting_time(sampler::Xu21CoupledSampler, initial::Tuple,
        max_steps::Integer) =
    coupled_meeting_time(Random.default_rng(), sampler, initial, max_steps)

"""Run a replicated, explicitly censored Xu et al. meeting-time diagnostic.

`meeting_times` contains an integer meeting time or `nothing` for each
replicate. `restricted_mean` replaces a censored time by `max_steps`; it is a
finite-horizon empirical summary, not an estimate of an uncensored expectation
and not a formal convergence certificate.
"""
function coupled_meeting_diagnostic(rng::AbstractRNG,
        sampler::Xu21CoupledSampler,
        initial::Tuple{<:AbstractVector{<:Real},<:AbstractVector{<:Real}},
        replicates::Integer, max_steps::Integer)
    replicates > 0 || throw(ArgumentError("replicate count must be positive"))
    max_steps >= 0 || throw(ArgumentError(
        "maximum meeting horizon must be nonnegative"))
    times = Union{Nothing,Int}[
        coupled_meeting_time(rng, sampler, initial, max_steps)
        for _ in 1:replicates
    ]
    met = count(!isnothing, times)
    observed_total = sum(time === nothing ? 0 : time for time in times)
    restricted_total = sum(time === nothing ? max_steps : time for time in times)
    (
        meeting_times=times,
        met=met,
        censored=replicates - met,
        meeting_fraction=met / replicates,
        observed_mean=met == 0 ? nothing : observed_total / met,
        restricted_mean=restricted_total / replicates,
        horizon=Int(max_steps),
    )
end

coupled_meeting_diagnostic(sampler::Xu21CoupledSampler, initial::Tuple,
        replicates::Integer, max_steps::Integer) =
    coupled_meeting_diagnostic(Random.default_rng(), sampler, initial,
        replicates, max_steps)
