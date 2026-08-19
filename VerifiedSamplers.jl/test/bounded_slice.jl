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

    observed_kinds = Symbol[]
    observed_positions = Float64[]
    observed_values = Float64[]
    observed_thresholds = Float64[]
    observed_source = Runtime.FloatTraceSource(copy(events))
    observed = Reference.stepping_out_slice_step!(observed_source,
        normal_logdensity, 1.0, 0.0, 2, 20;
        comparison_observer=(kind, position, value, threshold) -> begin
            push!(observed_kinds, kind)
            push!(observed_positions, position)
            push!(observed_values, value)
            push!(observed_thresholds, threshold)
        end)
    @test observed == reference
    @test observed_kinds == [:stopBelow, :stopBelow, :acceptAbove]
    @test observed_positions == [-0.25, 0.75, 0.25]
    @test length(observed_values) == length(observed_thresholds) == 3
    @test all(==(only(unique(observed_thresholds))), observed_thresholds)

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

    # A missing random event is a malformed replay trace, not the proved
    # algorithmic identity branch.
    depleted_events = Runtime.FloatTraceEvent[
        Runtime.UniformEvent(0.5), Runtime.UniformEvent(0.5)]
    @test_throws EOFError Reference.stepping_out_slice_step!(
        Runtime.FloatTraceSource(copy(depleted_events)),
        normal_logdensity, 1.0, 0.0, 0, 1)
    @test_throws EOFError Optimized.stepping_out_slice_step!(
        Runtime.FloatTraceSource(copy(depleted_events)),
        normal_logdensity, 1.0, 0.0, 0, 1)

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

    runtime_trace = trace_stepping_out_slice(
        MersenneTwister(0x51cf), sampler, 0.0)
    replay_result = step(MersenneTwister(0x51cf), sampler, 0.0)
    @test runtime_trace.result == replay_result
    @test !isempty(runtime_trace.kinds)
    @test length(runtime_trace.kinds) == length(runtime_trace.values)
    @test length(runtime_trace.positions) == length(runtime_trace.values)
    @test log(runtime_trace.uniform) == runtime_trace.log_uniform
    @test runtime_trace.base + runtime_trace.log_uniform == runtime_trace.threshold
    # This zero-bound self-certificate tests trace plumbing only: treating the
    # observed Float64 numbers as ideals is not a platform refinement proof.
    runtime_certificate = certify_stepping_out_slice_trace(runtime_trace,
        runtime_trace.threshold, 0.0, runtime_trace.values,
        zeros(length(runtime_trace.values)))
    @test Certificates.is_stable(runtime_certificate)
    @test Certificates.certified_slice_decisions(runtime_certificate) ==
        runtime_certificate.computed_decisions

    threshold_certificate = Certificates.certify_slice_threshold(
        0.0, 0.0, 0.0,
        runtime_trace.threshold, runtime_trace.threshold, 0.0,
        runtime_trace.threshold, 0.0)
    composed_runtime_certificate = certify_stepping_out_slice_trace(
        runtime_trace, threshold_certificate, runtime_trace.values,
        zeros(length(runtime_trace.values)))
    @test Certificates.is_stable(composed_runtime_certificate)
    @test threshold_certificate.threshold.bound == 0
    @test_throws ArgumentError certify_stepping_out_slice_trace(
        runtime_trace,
        Certificates.certify_slice_threshold(0.0, 0.0, 0.0,
            runtime_trace.threshold + 1.0,
            runtime_trace.threshold + 1.0, 0.0,
            runtime_trace.threshold + 1.0, 0.0),
        runtime_trace.values, zeros(length(runtime_trace.values)))

    quartic_sampler = restricted_potential_slice(
        restricted_quartic_potential, 0.5;
        max_steps=4, max_shrink=100)
    quartic_trace = trace_stepping_out_slice(
        MersenneTwister(0x51d0), quartic_sampler, 0.25)
    quartic_certificate = certify_restricted_quartic_slice_trace(
        quartic_trace, Rational{BigInt}(quartic_trace.log_uniform), 0)
    @test Certificates.is_stable(quartic_certificate.decisions)
    @test length(quartic_certificate.comparison_callbacks) ==
        length(quartic_trace.values)
    @test quartic_certificate.threshold.addition.observed_error ==
        quartic_certificate.threshold.addition.bound
    if @isdefined(ORACLE) && isfile(ORACLE)
        for callback in (quartic_certificate.current_callback,
                quartic_certificate.comparison_callbacks...)
            arguments = restricted_quartic_certificate_arguments(callback)
            @test readchomp(`$ORACLE quartic_certificate $arguments`) == "ok"
        end
    end

    for (offset, potential) in enumerate((restricted_gaussian_potential,
            restricted_sinusoidal_potential))
        sampler = restricted_potential_slice(potential, 0.5;
            max_steps=4, max_shrink=100)
        first = sample(MersenneTwister(0x51e0 + offset), sampler, 0.0, 100)
        second = sample(MersenneTwister(0x51e0 + offset), sampler, 0.0, 100)
        @test first == second
        @test all(isfinite, first)
        @test any(!iszero, first)
    end

    log_uniform_certificate = Certificates.certify_slice_log_uniform(
        quartic_trace.uniform, Rational{BigInt}(quartic_trace.uniform), 0,
        quartic_trace.log_uniform,
        Rational{BigInt}(quartic_trace.log_uniform), 0,
        Rational{BigInt}(quartic_trace.log_uniform),
        quartic_trace.uniform / 2)
    transported_quartic_certificate =
        certify_restricted_quartic_slice_trace(
            quartic_trace, log_uniform_certificate)
    @test Certificates.is_stable(transported_quartic_certificate.decisions)
    @test log_uniform_certificate.log.bound == 0
    direct_threshold_certificate = Certificates.certify_slice_threshold(
        quartic_trace.base,
        -quartic_certificate.current_callback.ideal_value,
        quartic_certificate.current_callback.value_error,
        log_uniform_certificate, quartic_trace.threshold,
        quartic_certificate.threshold.addition.bound)
    @test direct_threshold_certificate.threshold.ideal ==
        transported_quartic_certificate.threshold.threshold.ideal
    @test direct_threshold_certificate.threshold.bound ==
        transported_quartic_certificate.threshold.threshold.bound
    @test_throws ArgumentError Certificates.certify_slice_log_uniform(
        quartic_trace.uniform, quartic_trace.uniform, 0,
        quartic_trace.log_uniform, quartic_trace.log_uniform, 0,
        quartic_trace.log_uniform, quartic_trace.uniform + 0.1)

    mismatched_quartic_trace = SteppingOutSliceTrace(
        quartic_trace.result, quartic_trace.current, quartic_trace.base + 1,
        quartic_trace.uniform, quartic_trace.log_uniform, quartic_trace.threshold,
        quartic_trace.kinds, quartic_trace.positions, quartic_trace.values)
    @test_throws ArgumentError certify_restricted_quartic_slice_trace(
        mismatched_quartic_trace,
        Rational{BigInt}(quartic_trace.log_uniform), 0)

    stable = Certificates.certify_slice_comparisons(-0.5, -0.5, 1e-12,
        [-1.0, -0.2], [-1.0, -0.2], [1e-12, 1e-12])
    @test Certificates.is_stable(stable)
    @test Certificates.uncertainty_band(stable) == BigFloat(1e-12) + BigFloat(1e-12)

    kinds = Certificates.SliceComparisonKind[
        Certificates.StrictBelow, Certificates.StopBelow,
        Certificates.AcceptAbove]
    trace = Certificates.certify_slice_decision_trace(kinds,
        -0.5, -0.5, 1e-12,
        [-1.0, -0.6, -0.2], [-1.0, -0.6, -0.2],
        [1e-12, 1e-12, 1e-12])
    @test Certificates.is_stable(trace)
    @test Certificates.certified_slice_decisions(trace) == [true, true, true]
    @test trace.computed_decisions == trace.ideal_decisions

    boundary = Certificates.certify_slice_comparisons(-0.5, -0.5, 1e-3,
        [-0.4995], [-0.4995], [1e-3])
    @test !Certificates.is_stable(boundary)
    ambiguous_trace = Certificates.certify_slice_decision_trace(
        Certificates.SliceComparisonKind[Certificates.StrictBelow],
        -0.5, -0.5, 1e-3, [-0.4995], [-0.4995], [1e-3])
    @test !Certificates.is_stable(ambiguous_trace)
    @test isnothing(Certificates.certified_slice_decisions(ambiguous_trace))
    @test_throws DimensionMismatch Certificates.certify_slice_decision_trace(
        Certificates.SliceComparisonKind[Certificates.StrictBelow],
        -0.5, -0.5, 0.0, [-1.0, -0.2], [-1.0, -0.2], [0.0, 0.0])
    @test_throws DimensionMismatch Certificates.certify_slice_comparisons(
        -0.5, -0.5, 0.0, [-1.0], [-1.0, -0.2], [0.0])
end
