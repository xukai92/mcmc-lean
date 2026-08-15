# These named testsets make the intended continuous/HMC validation surface
# visible without implying that the corresponding samplers exist yet.

@testset "future: integrator properties" begin
    @testset "energy conservation" begin
        @test_skip false
    end
    @testset "time reversibility" begin
        @test_skip false
    end
    @testset "volume or measure preservation" begin
        @test_skip false
    end
end

@testset "future: continuous and mixed-state diagnostics" begin
    @testset "Geweke forward/backward joint-distribution test" begin
        @test_skip false
    end
    @testset "continuous normal-target moment matching" begin
        sampler = GaussianRWMH(x -> -x^2 / 2, 1.0)
        chain = sample(MersenneTwister(2026), sampler, 0.0, 50_000)
        retained = @view chain[5_001:end]
        @test abs(mean(retained)) < 0.08
        @test abs(var(retained) - 1.0) < 0.12

        accept_trace = Runtime.FloatTraceSource([
            Runtime.NormalEvent(0.5), Runtime.UniformEvent(0.8)])
        @test Optimized.gaussian_rwmh_step!(accept_trace, x -> -x^2 / 2,
            1.0, 0.0) == 0.5
        reject_trace = Runtime.FloatTraceSource([
            Runtime.NormalEvent(2.0), Runtime.UniformEvent(0.9)])
        @test Optimized.gaussian_rwmh_step!(reject_trace, x -> -x^2 / 2,
            1.0, 0.0) == 0.0
        for (events, expected) in (([
                Runtime.NormalEvent(0.5), Runtime.UniformEvent(0.8)], 0.5), ([
                Runtime.NormalEvent(2.0), Runtime.UniformEvent(0.9)], 0.0))
            reference_source = Runtime.FloatTraceSource(events)
            optimized_source = Runtime.FloatTraceSource(events)
            reference = Reference.gaussian_rwmh_step!(reference_source,
                x -> -x^2 / 2, 1.0, 0.0)
            optimized = Optimized.gaussian_rwmh_step!(optimized_source,
                x -> -x^2 / 2, 1.0, 0.0)
            @test reference == expected
            @test optimized == reference
            @test Runtime.remaining(reference_source) == 0
            @test Runtime.remaining(optimized_source) == 0
        end
        @test Runtime.remaining(accept_trace) == 0
        @test hasmethod(sample, Tuple{AbstractRNG, typeof(sampler), Real, Integer})
        @test hasmethod(Base.step, Tuple{AbstractRNG, typeof(sampler), Real})
        @test_throws ArgumentError GaussianRWMH(identity, 0.0)
        @test_throws ArgumentError Runtime.standard_normal!(
            Runtime.FloatTraceSource([Runtime.UniformEvent(0.5)]))
        @test_throws ArgumentError Runtime.uniform_unit!(
            Runtime.FloatTraceSource([Runtime.UniformEvent(1.0)]))
    end
    @testset "DHMC categorical target" begin
        @test_skip false
    end
    @testset "momentum and kinetic-energy units" begin
        @test_skip false
    end
end

@testset "future: robustness and performance" begin
    @testset "zero momentum and nonsmooth boundaries" begin
        @test_skip false
    end
    @testset "high-dimensional and ill-conditioned targets" begin
        @test_skip false
    end
    @testset "multimodal discrete targets" begin
        @test_skip false
    end
    @testset "adaptation correctness" begin
        @test_skip false
    end
    @testset "ESS and gradient-count benchmarks" begin
        @test_skip false
    end
end
