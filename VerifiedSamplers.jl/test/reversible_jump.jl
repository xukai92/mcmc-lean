@testset "nonlinear sheared birth/death reversible jump" begin
    events = Runtime.FloatTraceEvent[
        Runtime.UniformEvent(0.25), Runtime.UniformEvent(0.75)]
    reference_source = Runtime.FloatTraceSource(copy(events))
    optimized_source = Runtime.FloatTraceSource(copy(events))
    reference = Reference.sheared_birth_death_step!(reference_source, nothing)
    optimized = Optimized.sheared_birth_death_step!(optimized_source, nothing)
    @test reference == optimized == (0.0, 1.0)
    @test Runtime.remaining(reference_source) == 0
    @test Runtime.remaining(optimized_source) == 0

    # Death is deterministic and consumes no random event.
    death_source = Runtime.FloatTraceSource(Runtime.FloatTraceEvent[])
    @test Reference.sheared_birth_death_step!(death_source, reference) === nothing
    @test Runtime.remaining(death_source) == 0
    @test sheared_birth_unshear(reference) == (-1.0, 1.0)

    sampler = ShearedBirthDeathRJ()
    chain = sample(MersenneTwister(0x5eea), sampler, nothing, 40_000)
    @test count(isnothing, chain) == 20_000
    births = Tuple{Float64,Float64}[state for state in chain if state !== nothing]
    unsheared = sheared_birth_unshear.(births)
    @test all(state -> -2.0 <= state[1] <= 2.0 &&
        -2.0 <= state[2] <= 2.0, unsheared)
    @test abs(mean(first, unsheared)) < 0.04
    @test abs(mean(last, unsheared)) < 0.04
    @test abs(var(first.(unsheared)) - 4 / 3) < 0.06
    @test abs(var(last.(unsheared)) - 4 / 3) < 0.06
    @test abs(var(first.(births)) - (4 / 3 + 64 / 7)) < 0.25
    @test sample(MersenneTwister(17), sampler, nothing, 100) ==
        sample(MersenneTwister(17), sampler, nothing, 100)

    @test_throws ArgumentError Reference.sheared_birth_death_step!(
        Runtime.FloatTraceSource(Runtime.FloatTraceEvent[]), "invalid")
    @test_throws ArgumentError sample(MersenneTwister(1), sampler, nothing, -1)
end


@testset "three-dimensional product birth/death reversible jump" begin
    events = Runtime.FloatTraceEvent[
        Runtime.UniformEvent(0.0), Runtime.UniformEvent(0.25),
        Runtime.UniformEvent(0.75)]
    reference_source = Runtime.FloatTraceSource(copy(events))
    optimized_source = Runtime.FloatTraceSource(copy(events))
    reference = Reference.spatial_birth_death_step!(reference_source, nothing)
    optimized = Optimized.spatial_birth_death_step!(optimized_source, nothing)
    @test reference == optimized == (-2.0, -1.0, 1.0)
    @test Runtime.remaining(reference_source) == 0
    @test Runtime.remaining(optimized_source) == 0

    death_source = Runtime.FloatTraceSource(Runtime.FloatTraceEvent[])
    @test Reference.spatial_birth_death_step!(death_source, reference) === nothing
    @test Runtime.remaining(death_source) == 0

    sampler = SpatialBirthDeathRJ()
    chain = sample(MersenneTwister(0x3d5ca1e), sampler, nothing, 40_000)
    @test count(isnothing, chain) == 20_000
    births = NTuple{3,Float64}[state for state in chain if state !== nothing]
    @test all(state -> all(x -> -2.0 <= x <= 2.0, state), births)
    for coordinate in 1:3
        values = getindex.(births, coordinate)
        @test abs(mean(values)) < 0.04
        @test abs(var(values) - 4 / 3) < 0.06
    end
    @test sample(MersenneTwister(31), sampler, nothing, 100) ==
        sample(MersenneTwister(31), sampler, nothing, 100)
    @test_throws ArgumentError Reference.spatial_birth_death_step!(
        Runtime.FloatTraceSource(Runtime.FloatTraceEvent[]), (1.0, 2.0))
    @test_throws ArgumentError sample(MersenneTwister(1), sampler, nothing, -1)
end
