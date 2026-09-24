@testset "transport-coupled multinomial HMC" begin
    logdensity(x) = -sum(abs2, x) / 2
    gradient(x) = -x

    @testset "K=2 basic execution" begin
        K = 2; dim = 2; steps = 3
        step_size = 0.1
        x0 = Float64[1.0, 0.5, -0.5, 0.3]
        rng = MersenneTwister(42)
        source = Runtime.RNGSource(rng)
        result = Optimized.transport_coupled_multinomial_hmc_step!(
            source, logdensity, gradient, step_size, steps, K, x0)
        @test length(result) == 4
        @test all(isfinite, result)
        @test result != x0
    end

    @testset "K=3 basic execution" begin
        K = 3; dim = 2; steps = 3
        step_size = 0.1
        x0 = Float64[1.0, 0.5, -0.5, 0.3, 0.2, -0.1]
        rng = MersenneTwister(123)
        source = Runtime.RNGSource(rng)
        result = Optimized.transport_coupled_multinomial_hmc_step!(
            source, logdensity, gradient, step_size, steps, K, x0)
        @test length(result) == 6
        @test all(isfinite, result)
    end

    @testset "K=4 basic execution" begin
        K = 4; dim = 1; steps = 5
        step_size = 0.2
        x0 = Float64[1.0, -1.0, 0.5, -0.5]
        rng = MersenneTwister(7)
        source = Runtime.RNGSource(rng)
        result = Optimized.transport_coupled_multinomial_hmc_step!(
            source, logdensity, gradient, step_size, steps, K, x0)
        @test length(result) == 4
        @test all(isfinite, result)
    end

    @testset "workspace reuse" begin
        K = 2; dim = 2; steps = 3
        step_size = 0.1
        ws = Optimized.TransportCoupledMultinomialHMCWorkspace{Float64}(dim, K, steps)
        x0 = Float64[1.0, 0.5, -0.5, 0.3]
        rng = MersenneTwister(42)
        source = Runtime.RNGSource(rng)
        r1 = Optimized.transport_coupled_multinomial_hmc_step!(
            ws, source, logdensity, gradient, step_size, steps, K, x0)
        r2 = Optimized.transport_coupled_multinomial_hmc_step!(
            ws, source, logdensity, gradient, step_size, steps, K, r1)
        @test length(r2) == 4
        @test all(isfinite, r2)
    end

    @testset "Float32 path" begin
        K = 2; dim = 2; steps = 3
        step_size = Float32(0.1)
        x0 = Float32[1.0, 0.5, -0.5, 0.3]
        rng = MersenneTwister(99)
        source = Runtime.RNGSource(rng)
        result = Optimized.transport_coupled_multinomial_hmc_step!(
            source, logdensity, gradient, step_size, steps, K, x0)
        @test eltype(result) == Float32
        @test length(result) == 4
        @test all(isfinite, result)
    end

    @testset "marginal moment test K=2" begin
        K = 2; dim = 1; steps = 5
        step_size = 0.3
        rng = MersenneTwister(314)
        nsamples = 5000
        chain0_samples = Float64[]
        chain1_samples = Float64[]
        x = Float64[0.0, 0.0]
        for _ in 1:nsamples
            source = Runtime.RNGSource(rng)
            x = Optimized.transport_coupled_multinomial_hmc_step!(
                source, logdensity, gradient, step_size, steps, K, x)
            push!(chain0_samples, x[1])
            push!(chain1_samples, x[2])
        end
        burnin = 500
        c0 = chain0_samples[burnin+1:end]
        c1 = chain1_samples[burnin+1:end]
        @test abs(mean(c0)) < 0.15
        @test abs(mean(c1)) < 0.15
        @test abs(var(c0) - 1.0) < 0.3
        @test abs(var(c1) - 1.0) < 0.3
    end

    @testset "marginal moment test K=3" begin
        K = 3; dim = 1; steps = 5
        step_size = 0.3
        rng = MersenneTwister(271)
        nsamples = 8000
        samples = [Float64[] for _ in 1:K]
        x = zeros(Float64, K)
        for _ in 1:nsamples
            source = Runtime.RNGSource(rng)
            x = Optimized.transport_coupled_multinomial_hmc_step!(
                source, logdensity, gradient, step_size, steps, K, x)
            for k in 1:K
                push!(samples[k], x[k])
            end
        end
        burnin = 1000
        for k in 1:K
            c = samples[k][burnin+1:end]
            @test abs(mean(c)) < 0.2
            @test abs(var(c) - 1.0) < 0.4
        end
    end

    @testset "input validation" begin
        rng = MersenneTwister(1)
        source = Runtime.RNGSource(rng)
        @test_throws ArgumentError Optimized.transport_coupled_multinomial_hmc_step!(
            source, logdensity, gradient, 0.1, 3, 0, Float64[1.0])
        @test_throws ArgumentError Optimized.transport_coupled_multinomial_hmc_step!(
            source, logdensity, gradient, 0.1, 0, 2, Float64[1.0, 2.0])
        @test_throws ArgumentError Optimized.transport_coupled_multinomial_hmc_step!(
            source, logdensity, gradient, -0.1, 3, 2, Float64[1.0, 2.0])
        @test_throws DimensionMismatch Optimized.transport_coupled_multinomial_hmc_step!(
            source, logdensity, gradient, 0.1, 3, 2, Float64[1.0, 2.0, 3.0])
    end
end
