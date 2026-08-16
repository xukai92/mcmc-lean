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

@testset "stepping-out and shrinkage slice" begin
    normal_logdensity(x) = -x^2 / 2
    events = Runtime.FloatTraceEvent[
        Runtime.UniformEvent(0.5), Runtime.UniformEvent(0.25),
        Runtime.UniformEvent(0.5), Runtime.UniformEvent(0.5)]
    reference_source = Runtime.FloatTraceSource(copy(events))
    optimized_source = Runtime.FloatTraceSource(copy(events))
    reference = Reference.stepping_out_slice_step!(reference_source,
        normal_logdensity, 1.0, 0.0, 2, 20)
    optimized = Optimized.stepping_out_slice_step!(optimized_source,
        normal_logdensity, 1.0, 0.0, 2, 20)
    @test reference == optimized == 0.25
    @test Runtime.remaining(reference_source) == 0
    @test Runtime.remaining(optimized_source) == 0

    # A zero expansion budget still consumes the randomized split event and
    # then samples from the initial width-sized bracket.
    zero_step_events = Runtime.FloatTraceEvent[
        Runtime.UniformEvent(0.5), Runtime.UniformEvent(0.25),
        Runtime.UniformEvent(0.9), Runtime.UniformEvent(0.5)]
    zero_reference_source = Runtime.FloatTraceSource(copy(zero_step_events))
    zero_optimized_source = Runtime.FloatTraceSource(copy(zero_step_events))
    @test Reference.stepping_out_slice_step!(zero_reference_source,
        normal_logdensity, 1.0, 0.0, 0, 20) == 0.25
    @test Optimized.stepping_out_slice_step!(zero_optimized_source,
        normal_logdensity, 1.0, 0.0, 0, 20) == 0.25
    @test Runtime.remaining(zero_reference_source) == 0
    @test Runtime.remaining(zero_optimized_source) == 0

    # The first proposal lies above the narrow slice threshold and shrinks the
    # right endpoint; the second proposal is then accepted from that bracket.
    shrink_events = Runtime.FloatTraceEvent[
        Runtime.UniformEvent(0.99), Runtime.UniformEvent(0.5),
        Runtime.UniformEvent(0.2), Runtime.UniformEvent(0.9),
        Runtime.UniformEvent(0.5)]
    shrink_reference_source = Runtime.FloatTraceSource(copy(shrink_events))
    shrink_optimized_source = Runtime.FloatTraceSource(copy(shrink_events))
    @test Reference.stepping_out_slice_step!(shrink_reference_source,
        normal_logdensity, 1.0, 0.0, 0, 20) ≈ -0.05
    @test Optimized.stepping_out_slice_step!(shrink_optimized_source,
        normal_logdensity, 1.0, 0.0, 0, 20) ≈ -0.05
    @test Runtime.remaining(shrink_reference_source) == 0
    @test Runtime.remaining(shrink_optimized_source) == 0

    # Finite shrinkage exhaustion is a total identity fallback in both paths.
    exhausted_events = Runtime.FloatTraceEvent[
        Runtime.UniformEvent(0.99), Runtime.UniformEvent(0.5),
        Runtime.UniformEvent(0.2), Runtime.UniformEvent(0.9)]
    exhausted_reference_source = Runtime.FloatTraceSource(copy(exhausted_events))
    exhausted_optimized_source = Runtime.FloatTraceSource(copy(exhausted_events))
    @test Reference.stepping_out_slice_step!(exhausted_reference_source,
        normal_logdensity, 1.0, 0.0, 0, 1) == 0.0
    @test Optimized.stepping_out_slice_step!(exhausted_optimized_source,
        normal_logdensity, 1.0, 0.0, 0, 1) == 0.0
    @test Runtime.remaining(exhausted_reference_source) == 0
    @test Runtime.remaining(exhausted_optimized_source) == 0

    sampler = SteppingOutSlice(normal_logdensity, 1.0; max_steps=20)
    first_chain = sample(MersenneTwister(0x51ce), sampler, 0.0, 15_000)
    second_chain = sample(MersenneTwister(0x51ce), sampler, 0.0, 15_000)
    @test first_chain == second_chain
    retained = first_chain[1001:end]
    @test abs(mean(retained)) < 0.06
    @test abs(var(retained) - 1) < 0.08
    @test_throws ArgumentError SteppingOutSlice(normal_logdensity, 0.0)
    @test_throws ArgumentError SteppingOutSlice(normal_logdensity, 1.0;
        max_steps=-1)
end
