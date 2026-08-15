# Executable scalar HMC tests and placeholders for later vector/DHMC work.

@testset "scalar leapfrog integrator properties" begin
    @testset "energy conservation" begin
        q, p = 0.7, -0.4
        initial_energy = (q^2 + p^2) / 2
        for _ in 1:100
            q, p = Optimized.leapfrog(identity, 0.05, q, p)
        end
        @test abs((q^2 + p^2) / 2 - initial_energy) < 1e-3
    end
    @testset "time reversibility" begin
        initial_q, initial_p = 0.7, -0.4
        q, p = initial_q, initial_p
        for _ in 1:20
            q, p = Optimized.leapfrog(identity, 0.05, q, p)
        end
        p = -p
        for _ in 1:20
            q, p = Optimized.leapfrog(identity, 0.05, q, p)
        end
        @test q ≈ initial_q atol=1e-12
        @test p ≈ -initial_p atol=1e-12
    end
    @testset "volume or measure preservation" begin
        map = function (q, p)
            Optimized.leapfrog(x -> x + 0.1x^3, 0.15, q, p)
        end
        q, p, δ = 0.4, -0.3, 1e-6
        qp = map(q + δ, p); qm = map(q - δ, p)
        pp = map(q, p + δ); pm = map(q, p - δ)
        jacobian = [(qp[1] - qm[1]) / (2δ) (pp[1] - pm[1]) / (2δ);
                    (qp[2] - qm[2]) / (2δ) (pp[2] - pm[2]) / (2δ)]
        @test det(jacobian) ≈ 1.0 atol=1e-8
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
        generic_cases = [
            (x -> -abs(x), 0.25, 1.0,
                [Runtime.NormalEvent(-2.0), Runtime.UniformEvent(0.9)]),
            (x -> -x^4, 0.75, 0.25,
                [Runtime.NormalEvent(2.0), Runtime.UniformEvent(0.5)]),
            (x -> -((x - 3.0) / 2.0)^2 / 2.0, 1.5, -1.0,
                [Runtime.NormalEvent(0.25), Runtime.UniformEvent(0.2)]),
        ]
        for (logdensity, scale, current, events) in generic_cases
            reference_source = Runtime.FloatTraceSource(events)
            optimized_source = Runtime.FloatTraceSource(events)
            reference = Reference.gaussian_rwmh_step!(reference_source,
                logdensity, scale, current)
            optimized = Optimized.gaussian_rwmh_step!(optimized_source,
                logdensity, scale, current)
            @test optimized == reference
            @test Runtime.remaining(reference_source) == 0
            @test Runtime.remaining(optimized_source) == 0
        end
        @test_throws ArgumentError Reference.gaussian_rwmh_step!(
            Runtime.FloatTraceSource(Runtime.FloatTraceEvent[]), identity, 0.0, 0.0)
        @test Runtime.remaining(accept_trace) == 0
        @test hasmethod(sample, Tuple{AbstractRNG, typeof(sampler), Real, Integer})
        @test hasmethod(Base.step, Tuple{AbstractRNG, typeof(sampler), Real})
        @test_throws ArgumentError GaussianRWMH(identity, 0.0)
        @test_throws ArgumentError Runtime.standard_normal!(
            Runtime.FloatTraceSource([Runtime.UniformEvent(0.5)]))
        @test_throws ArgumentError Runtime.uniform_unit!(
            Runtime.FloatTraceSource([Runtime.UniformEvent(1.0)]))
    end
    @testset "scalar HMC reference, optimized, and moments" begin
        logdensity = x -> -x^2 / 2
        gradient = identity
        cases = [
            (0.0, [Runtime.NormalEvent(0.5), Runtime.UniformEvent(0.1)]),
            (1.0, [Runtime.NormalEvent(2.0), Runtime.UniformEvent(0.99)]),
            (-0.5, [Runtime.NormalEvent(-1.0), Runtime.UniformEvent(0.4)]),
        ]
        for (current, events) in cases
            reference_source = Runtime.FloatTraceSource(events)
            optimized_source = Runtime.FloatTraceSource(events)
            reference = Reference.scalar_hmc_step!(reference_source,
                logdensity, gradient, 0.4, current)
            optimized = Optimized.scalar_hmc_step!(optimized_source,
                logdensity, gradient, 0.4, current)
            @test optimized == reference
            @test Runtime.remaining(reference_source) == 0
            @test Runtime.remaining(optimized_source) == 0
        end

        sampler = ScalarHMC(logdensity, gradient, 0.4)
        chain = sample(MersenneTwister(0x4a3c), sampler, 0.0, 50_000)[5001:end]
        @test abs(mean(chain)) < 0.08
        @test abs(var(chain) - 1.0) < 0.12
        @test_throws ArgumentError ScalarHMC(logdensity, gradient, 0.0)
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
