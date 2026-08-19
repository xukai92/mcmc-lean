using Random
using VerifiedSamplers

function main(arguments)
    seed = length(arguments) >= 1 ? parse(Int, arguments[1]) : 0x5047
    repetitions = length(arguments) >= 2 ? parse(Int, arguments[2]) : 8_000
    repetitions > 0 || throw(ArgumentError("repetition count must be positive"))
    count_grid = length(arguments) >= 3 ?
        parse.(Int, split(arguments[3], ',')) : [1, 2, 4, 8]
    !isempty(count_grid) && all(>(0), count_grid) ||
        throw(ArgumentError("particle counts must be positive"))

    initial = [1, 1]
    transition = [1 1; 1 1]
    potentials = reshape([1, 1], 1, 2)
    current = [1, 1]

    println("seed,repetitions,horizon,particles,one_step_tv")
    for particle_count in count_grid
        sampler = FiniteHMMParticleGibbs(initial, transition, potentials,
            particle_count)
        rng = MersenneTwister(seed + particle_count)
        path_counts = zeros(Int, 4)
        for _ in 1:repetitions
            path = step(rng, sampler, current)
            path_counts[(path[1] - 1) * 2 + path[2]] += 1
        end
        tv = sum(abs.(path_counts ./ repetitions .- 0.25)) / 2
        println(join((seed, repetitions, 1, particle_count, tv), ','))
    end
end

main(ARGS)
