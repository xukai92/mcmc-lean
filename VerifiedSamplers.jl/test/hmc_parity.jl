@testset "fixed-integration-time HMC" begin
    logdensity(q) = -sum(abs2, q) / 2
    gradient(q) = q

    fixed_time = FixedIntegrationTimeHMC(logdensity, gradient, 0.2, 1.0)
    fixed_steps = VectorHMC(logdensity, gradient, 0.2, 5)
    @test fixed_time.steps == 5
    @test sample(MersenneTwister(0x71ae), fixed_time, zeros(2), 20) ==
        sample(MersenneTwister(0x71ae), fixed_steps, zeros(2), 20)

    metric = DiagonalMetric([1.0, 2.0])
    metric_time = FixedIntegrationTimeHMC(
        logdensity, gradient, metric, 0.25, 1.0)
    metric_steps = MetricHMC(logdensity, gradient, metric, 0.25, 4)
    @test metric_time.steps == 4
    @test sample(MersenneTwister(0x71af), metric_time, zeros(2), 20) ==
        sample(MersenneTwister(0x71af), metric_steps, zeros(2), 20)

    @test_throws ArgumentError FixedIntegrationTimeHMC(
        logdensity, gradient, 0.0, 1.0)
    @test_throws ArgumentError FixedIntegrationTimeHMC(
        logdensity, gradient, 1.0, 0.5)
end

@testset "jittered HMC" begin
    logdensity(q) = -sum(abs2, q) / 2
    gradient(q) = q
    sampler = JitteredHMC(logdensity, gradient, 0.2, 3; jitter=0.25)

    # Jitter draw u=0.75 produces ε=0.225. The remaining events are the
    # ordinary vector-HMC momentum and acceptance trace.
    jittered_source = Runtime.FloatTraceSource([
        Runtime.UniformEvent(0.75), Runtime.NormalEvent(0.3),
        Runtime.NormalEvent(-0.4), Runtime.UniformEvent(0.2)])
    fixed_source = Runtime.FloatTraceSource([
        Runtime.NormalEvent(0.3), Runtime.NormalEvent(-0.4),
        Runtime.UniformEvent(0.2)])
    actual = VerifiedSamplers._jittered_hmc_step!(
        jittered_source, sampler, [0.1, -0.2])
    expected = Reference.vector_hmc_step!(
        fixed_source, logdensity, gradient, 0.225, 3, [0.1, -0.2])
    @test actual == expected
    @test Runtime.remaining(jittered_source) == 0

    chain = sample(MersenneTwister(0x71b0), sampler, zeros(2), 25)
    @test size(chain) == (2, 25)
    @test all(isfinite, chain)
    @test_throws ArgumentError JitteredHMC(
        logdensity, gradient, 0.2, 3; jitter=1.0)
end

@testset "tempered HMC" begin
    logdensity(q) = -sum(abs2, q) / 2
    gradient(q) = q

    # Temperature one removes every tempering operation, recovering endpoint
    # HMC exactly on the same explicit primitive trace.
    tempered = TemperedHMC(logdensity, gradient, 0.2, 3; temperature=1.0)
    tempered_source = Runtime.FloatTraceSource([
        Runtime.NormalEvent(0.3), Runtime.NormalEvent(-0.4),
        Runtime.UniformEvent(0.2)])
    reference_source = Runtime.FloatTraceSource([
        Runtime.NormalEvent(0.3), Runtime.NormalEvent(-0.4),
        Runtime.UniformEvent(0.2)])
    actual = VerifiedSamplers._tempered_hmc_step!(
        tempered_source, tempered, [0.1, -0.2])
    expected = Reference.vector_hmc_step!(
        reference_source, logdensity, gradient, 0.2, 3, [0.1, -0.2])
    @test actual ≈ expected atol=1e-14 rtol=1e-14
    @test Runtime.remaining(tempered_source) == 0

    exploratory = TemperedHMC(
        logdensity, gradient, DiagonalMetric([1.0, 2.0]), 0.15, 4;
        temperature=1.2)
    chain = sample(MersenneTwister(0x71b1), exploratory, zeros(2), 25)
    @test size(chain) == (2, 25)
    @test all(isfinite, chain)
    @test_throws ArgumentError TemperedHMC(
        logdensity, gradient, 0.2, 3; temperature=0.0)
end

@testset "fixed rank-update metric" begin
    metric = RankUpdateMetric(
        [1.0, 2.0, 3.0], [1.0 0.0; 0.0 1.0; 1.0 -1.0], [0.2 0.0; 0.0 0.1])
    @test metric.inverse_mass ≈
        Diagonal([1.0, 2.0, 3.0]) + metric.basis * metric.update * metric.basis'
    @test metric.mass * metric.inverse_mass ≈ Matrix{Float64}(I, 3, 3)

    logdensity(q) = -sum(abs2, q) / 2
    gradient(q) = q
    sampler = MetricHMC(logdensity, gradient, metric, 0.1, 4)
    chain = sample(MersenneTwister(0x71b2), sampler, zeros(3), 20)
    @test size(chain) == (3, 20)
    @test all(isfinite, chain)

    @test_throws DimensionMismatch RankUpdateMetric(
        [1.0, 2.0], ones(3, 1), ones(1, 1))
    @test_throws ArgumentError RankUpdateMetric(
        [1.0, 2.0], ones(2, 1), [-3.0;;])
end

@testset "fixed-metric HMC parity surface" begin
    logdensity(q) = -sum(abs2, q) / 2
    gradient(q) = q
    metrics = (
        DiagonalMetric([1.0, 2.0]),
        DenseMetric([1.0 0.2; 0.2 1.5]),
        RankUpdateMetric([1.0, 2.0], [1.0; -0.5;;], [0.25;;]),
    )

    for (index, metric) in enumerate(metrics)
        seed = 0x71c0 + index
        samplers = (
            FixedIntegrationTimeHMC(
                logdensity, gradient, metric, 0.1, 0.4),
            JitteredHMC(logdensity, gradient, metric, 0.1, 4; jitter=0.2),
            TemperedHMC(
                logdensity, gradient, metric, 0.1, 4; temperature=1.1),
        )
        for sampler in samplers
            draws = sample(MersenneTwister(seed), sampler, zeros(2), 8)
            @test size(draws) == (2, 8)
            @test all(isfinite, draws)
            seed += 0x10
        end

        partial = PartialMomentumHMC(
            logdensity, gradient, 0.1, 4; refresh=0.8, metric)
        draws = sample(MersenneTwister(seed), partial, zeros(2), 8)
        @test size(draws) == (2, 8)
        @test all(isfinite, draws)
    end
end

@testset "partial momentum refresh" begin
    logdensity(q) = -sum(abs2, q) / 2
    gradient(q) = q
    sampler = PartialMomentumHMC(
        logdensity, gradient, 0.2, 3; refresh=0.0)
    state = HMCPhaseState([0.1, -0.2], [9.0, 8.0])
    partial_source = Runtime.FloatTraceSource([
        Runtime.NormalEvent(0.3), Runtime.NormalEvent(-0.4),
        Runtime.UniformEvent(0.2)])
    reference_source = Runtime.FloatTraceSource([
        Runtime.NormalEvent(0.3), Runtime.NormalEvent(-0.4),
        Runtime.UniformEvent(0.2)])
    actual = VerifiedSamplers._partial_momentum_transition!(
        partial_source, sampler, state)
    expected = Reference.vector_hmc_step!(reference_source,
        logdensity, gradient, 0.2, 3, state.position)
    @test actual.state.position ≈ expected atol=1e-14 rtol=1e-14
    @test actual.state.momentum != state.momentum
    @test 0 <= actual.diagnostics.acceptance_rate <= 1

    persistent = PartialMomentumHMC(
        logdensity, gradient, 0.15, 4; refresh=0.8,
        metric=DiagonalMetric([1.0, 2.0]))
    chain = sample(MersenneTwister(0x71b3), persistent, zeros(2), 40)
    @test size(chain) == (2, 40)
    @test all(isfinite, chain)
    @test_throws ArgumentError PartialMomentumHMC(
        logdensity, gradient, 0.2, 3; refresh=1.1)
end
