@testset "bounded continuous rejection slice" begin
    flat_logdensity(_) = 0.0
    events = Runtime.FloatTraceEvent[
        Runtime.UniformEvent(0.25), Runtime.UniformEvent(0.75)]
    reference_source = Runtime.FloatTraceSource(events)
    optimized_source = Runtime.FloatTraceSource(events)
    reference = Reference.bounded_slice_step!(reference_source,
        flat_logdensity, -2.0, 2.0, 0.0, 10)
    optimized = Optimized.bounded_slice_step!(optimized_source,
        flat_logdensity, -2.0, 2.0, 0.0, 10)
    @test reference == optimized == 1.0
    @test Runtime.remaining(reference_source) == 0
    @test Runtime.remaining(optimized_source) == 0

    # A rejected proposal consumes another uniform event in both paths.
    peaked(x) = abs(x) <= 0.5 ? 0.0 : -Inf
    retry_events = Runtime.FloatTraceEvent[
        Runtime.UniformEvent(0.5), Runtime.UniformEvent(0.9),
        Runtime.UniformEvent(0.55)]
    @test Reference.bounded_slice_step!(Runtime.FloatTraceSource(retry_events),
        peaked, -1.0, 1.0, 0.0, 10) ≈ 0.1
    @test Optimized.bounded_slice_step!(Runtime.FloatTraceSource(retry_events),
        peaked, -1.0, 1.0, 0.0, 10) ≈ 0.1

    sampler = BoundedRejectionSlice(flat_logdensity, -2.0, 2.0)
    draws = sample(MersenneTwister(91), sampler, 0.0, 20_000)
    @test all(x -> -2.0 <= x <= 2.0, draws)
    @test abs(mean(draws)) < 0.04
    @test abs(var(draws) - 4 / 3) < 0.06
    @test sample(MersenneTwister(3), sampler, 0.0, 20) ==
        sample(MersenneTwister(3), sampler, 0.0, 20)

    @test_throws ArgumentError BoundedRejectionSlice(flat_logdensity, 1.0, 1.0)
    @test_throws ArgumentError step(MersenneTwister(1), sampler, 3.0)
    @test_throws ErrorException Reference.bounded_slice_step!(
        Runtime.FloatTraceSource(Runtime.FloatTraceEvent[
            Runtime.UniformEvent(0.5), Runtime.UniformEvent(0.9)]),
        peaked, -1.0, 1.0, 0.0, 1)
end
