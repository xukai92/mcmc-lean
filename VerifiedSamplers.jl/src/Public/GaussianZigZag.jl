"""Exact ideal-form Gaussian Zig-Zag inverse clock in Float64 arithmetic."""
function gaussian_zigzag_waiting_time(position::Real, velocity::Integer,
        exponential_draw::Real)
    q, e = Float64(position), Float64(exponential_draw)
    isfinite(q) || throw(ArgumentError("position must be finite"))
    velocity in (-1, 1) || throw(ArgumentError("velocity must be -1 or 1"))
    isfinite(e) && e > 0 || throw(ArgumentError(
        "exponential hazard draw must be finite and positive"))
    a = velocity * q
    if a >= 0
        root = sqrt(a * a + 2 * e)
        wait = (2 * e) / (root + a)
    else
        wait = -a + sqrt(2 * e)
    end
    isfinite(wait) && wait >= 0 || throw(DomainError(wait,
        "Gaussian Zig-Zag waiting time must be finite"))
    wait
end

"""One-dimensional standard-Gaussian Zig-Zag sampler at fixed observation spacing."""
struct GaussianZigZag
    observation_interval::Float64
    function GaussianZigZag(observation_interval::Real=1.0)
        interval = Float64(observation_interval)
        isfinite(interval) && interval > 0 || throw(ArgumentError(
            "observation interval must be finite and positive"))
        new(interval)
    end
end

"""Observed Zig-Zag positions and velocities."""
struct GaussianZigZagResult
    positions::Vector{Float64}
    velocities::Vector{Int8}
end

function step(rng::AbstractRNG, sampler::GaussianZigZag,
        current::Tuple{<:Real,<:Integer})
    q, velocity = Float64(current[1]), Int(current[2])
    isfinite(q) || throw(ArgumentError("position must be finite"))
    velocity in (-1, 1) || throw(ArgumentError("velocity must be -1 or 1"))
    elapsed = 0.0
    while true
        wait = gaussian_zigzag_waiting_time(q, velocity, randexp(rng))
        remaining = sampler.observation_interval - elapsed
        if wait >= remaining
            return (q + velocity * remaining, velocity)
        end
        q += velocity * wait
        elapsed += wait
        velocity = -velocity
    end
end

step(sampler::GaussianZigZag, current::Tuple{<:Real,<:Integer}) =
    step(Random.default_rng(), sampler, current)

function sample(rng::AbstractRNG, sampler::GaussianZigZag,
        initial::Tuple{<:Real,<:Integer}, count::Integer)
    count >= 0 || throw(ArgumentError("sample count must be nonnegative"))
    positions = Vector{Float64}(undef, count)
    velocities = Vector{Int8}(undef, count)
    current = initial
    for index in eachindex(positions)
        current = step(rng, sampler, current)
        positions[index] = current[1]
        velocities[index] = current[2]
    end
    GaussianZigZagResult(positions, velocities)
end

sample(sampler::GaussianZigZag, initial::Tuple{<:Real,<:Integer},
        count::Integer) =
    sample(Random.default_rng(), sampler, initial, count)
