@testset "finite HMM particle Gibbs" begin
    initial = [1, 1]
    transition = [1 1; 1 1]
    potentials = reshape([1, 1], 1, 2)
    current = [1, 2]

    events = BigInt[0, 1, 1, 0, 1, 1]
    reference_source = Runtime.TraceSource(copy(events))
    optimized_source = Runtime.TraceSource(copy(events))
    reference = Reference.finite_hmm_particle_gibbs_step!(reference_source,
        initial, transition, potentials, 2, current)
    optimized = Optimized.finite_hmm_particle_gibbs_step!(optimized_source,
        initial, transition, potentials, 2, current)
    @test reference == optimized
    @test Runtime.remaining(reference_source) == 0
    @test Runtime.remaining(optimized_source) == 0
    @test reference_source.requested_bounds == optimized_source.requested_bounds

    # The formal one-particle identity theorem is mirrored exactly at runtime.
    singleton_source = Runtime.TraceSource(BigInt[0, 0, 0])
    @test Reference.finite_hmm_particle_gibbs_step!(singleton_source,
        initial, transition, potentials, 1, current) == current

    sampler = FiniteHMMParticleGibbs(initial, transition, potentials, 4)
    paths = sample(MersenneTwister(31), sampler, current, 8_000)
    @test size(paths) == (2, 8_000)
    frequencies = Dict(path => count(i -> Tuple(paths[:, i]) == path,
        axes(paths, 2)) / size(paths, 2) for path in
        ((1, 1), (1, 2), (2, 1), (2, 2)))
    @test all(frequency -> abs(frequency - 0.25) < 0.035,
        values(frequencies))

    # At horizon zero the exact formal kernel is N⁻¹ identity plus
    # (1-N⁻¹) independent refresh from the initial law.
    zero_horizon = FiniteHMMParticleGibbs([1, 3], transition,
        zeros(Int, 0, 2), 4)
    zero_rng = MersenneTwister(44)
    zero_paths = [step(zero_rng, zero_horizon, [1])[1] for _ in 1:12_000]
    retained_frequency = count(==(1), zero_paths) / length(zero_paths)
    @test abs(retained_frequency - (1 / 4 + (3 / 4) * (1 / 4))) < 0.025

    # Reproducible fixed-horizon, fixed-iteration particle-count experiment.
    # The exact target is uniform on the four paths. Starting from (1,1), the
    # empirical one-step TV error decreases as the particle count grows. This
    # is a runtime diagnostic aligned with, but not a proof of, Lean's
    # fixed-iteration particle-count theorem.
    count_grid = [1, 2, 4, 8]
    one_step_tv = map(count_grid) do particle_count
        count_sampler = FiniteHMMParticleGibbs(initial, transition,
            potentials, particle_count)
        rng = MersenneTwister(0x5047 + particle_count)
        path_counts = zeros(Int, 4)
        repetitions = 8_000
        for _ in 1:repetitions
            path = step(rng, count_sampler, [1, 1])
            path_counts[(path[1] - 1) * 2 + path[2]] += 1
        end
        sum(abs.(path_counts ./ repetitions .- 0.25)) / 2
    end
    @test one_step_tv[1] == 0.75
    @test all(diff(one_step_tv) .< 0)
    @test one_step_tv[end] < 0.16

    @test_throws ArgumentError FiniteHMMParticleGibbs(initial, transition,
        potentials, 0)
    @test_throws DimensionMismatch step(MersenneTwister(1), sampler, [1])
end
