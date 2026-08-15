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

@testset "corrected relativistic multinomial HMC" begin
    logdensity(x) = -sum(abs2, x) / 2
    gradient(x) = x
    events = Runtime.FloatTraceEvent[
        Runtime.UniformEvent(0.2), Runtime.UniformEvent(0.3),
        Runtime.UniformEvent(0.1),
        Runtime.NormalEvent(0.4), Runtime.NormalEvent(-0.7),
        Runtime.IndexEvent(1), Runtime.UniformEvent(0.35)]
    reference_source = Runtime.FloatTraceSource(copy(events))
    optimized_source = Runtime.FloatTraceSource(copy(events))
    reference = Reference.relativistic_multinomial_hmc_step!(reference_source,
        logdensity, gradient, 0.1, 2, [0.25, -0.5], [1.0, 4.0], 1.0)
    optimized = Optimized.relativistic_multinomial_hmc_step!(optimized_source,
        logdensity, gradient, 0.1, 2, [0.25, -0.5], [1.0, 4.0], 1.0)
    @test reference ≈ optimized atol=1e-14 rtol=0
    @test Runtime.remaining(reference_source) == 0
    @test Runtime.remaining(optimized_source) == 0

    sampler = RelativisticMultinomialHMC(logdensity, gradient,
        DiagonalMetric([1.0, 4.0]), 1.0, 0.1, 2)
    samples = sample(MersenneTwister(9), sampler, [0.0, 0.0], 4)
    @test size(samples) == (2, 4)
    @test all(isfinite, samples)
end

@testset "certified position-dependent relativistic interface" begin
    exact_certificate = Certificates.certify_implicit_solve(0, 0, 0, 0;
        unique=true, reversible=true, volume_preserving=true)
    factor(q) = Matrix{Float64}(I, length(q), length(q))
    hamiltonian(q, p) = sum(abs2, q) / 2 + sqrt(sum(abs2, p) + 1)
    integrator(q, p, ε) = begin
        half = p .- (ε / 2) .* q
        next_q = q .+ ε .* half ./ sqrt(sum(abs2, half) + 1)
        next_p = half .- (ε / 2) .* next_q
        (next_q, next_p, exact_certificate)
    end
    events = Runtime.FloatTraceEvent[
        Runtime.UniformEvent(0.2), Runtime.UniformEvent(0.3),
        Runtime.UniformEvent(0.1),
        Runtime.NormalEvent(0.4), Runtime.NormalEvent(-0.7),
        Runtime.IndexEvent(1), Runtime.UniformEvent(0.35)]
    reference = Reference.certified_relativistic_multinomial_hmc_step!(
        Runtime.FloatTraceSource(copy(events)), hamiltonian, factor, integrator,
        0.1, 2, [0.25, -0.5], 1.0)
    optimized = Optimized.certified_relativistic_multinomial_hmc_step!(
        Runtime.FloatTraceSource(copy(events)), hamiltonian, factor, integrator,
        0.1, 2, [0.25, -0.5], 1.0)
    @test reference ≈ optimized atol=1e-14 rtol=0

    approximate = Certificates.certify_implicit_solve(1e-8, 1e-8, 0, 0;
        unique=true, reversible=true, volume_preserving=true)
    bad_integrator(q, p, ε) = (q, p, approximate)
    @test_throws ArgumentError Reference.certified_relativistic_multinomial_hmc_step!(
        Runtime.FloatTraceSource(copy(events)), hamiltonian, factor, bad_integrator,
        0.1, 2, [0.25, -0.5], 1.0)
end

@testset "position-dependent fixed-point generalized leapfrog" begin
    coefficient = 0.2
    position_derivative(q, p) = (coefficient / 2) .* p.^2
    momentum_derivative(q, p) = (1 .+ coefficient .* q) .* p
    q, p, ε = [0.2, -0.1], [0.4, -0.3], 0.1
    reference = Reference.fixed_point_generalized_leapfrog(
        position_derivative, momentum_derivative, q, p, ε;
        max_iterations=200, atol=1e-13, rtol=1e-13)
    optimized = Optimized.fixed_point_generalized_leapfrog(
        position_derivative, momentum_derivative, q, p, ε;
        max_iterations=200, atol=1e-13, rtol=1e-13)
    @test reference[1] ≈ optimized[1] atol=1e-14 rtol=0
    @test reference[2] ≈ optimized[2] atol=1e-14 rtol=0
    @test reference[3].half_momentum_residual.computed < 1e-12
    @test reference[3].position_residual.computed < 1e-12
    @test !Certificates.certifies_exact_solver(reference[3])

    public_result = fixed_point_generalized_leapfrog(
        position_derivative, momentum_derivative, q, p, ε)
    @test public_result[1] ≈ reference[1] atol=1e-8
    @test_throws DimensionMismatch fixed_point_generalized_leapfrog(
        position_derivative, momentum_derivative, q, [0.4], ε)

    # Smooth momentum-even formal test Hamiltonian H(q,p)=a*q*sqrt(1+p^2).
    a = 0.35
    even_position_derivative(q, p) = a .* sqrt.(1 .+ p.^2)
    even_momentum_derivative(q, p) = a .* q .* p ./ sqrt.(1 .+ p.^2)
    q0, p0, ε0 = [0.3], [-0.45], 0.2
    forward = fixed_point_generalized_leapfrog(even_position_derivative,
        even_momentum_derivative, q0, -p0, ε0;
        max_iterations=300, atol=1e-14, rtol=1e-14)
    backward = fixed_point_generalized_leapfrog(even_position_derivative,
        even_momentum_derivative, q0, p0, -ε0;
        max_iterations=300, atol=1e-14, rtol=1e-14)
    @test forward[1] ≈ backward[1] atol=2e-13 rtol=0
    @test -forward[2] ≈ backward[2] atol=2e-13 rtol=0
    @test forward[3].half_momentum_residual.computed < 1e-13
    @test forward[3].position_residual.computed < 1e-13

    phase_map(qp) = begin
        result = fixed_point_generalized_leapfrog(even_position_derivative,
            even_momentum_derivative, [qp[1]], [qp[2]], ε0;
            max_iterations=300, atol=1e-14, rtol=1e-14)
        [result[1][1], result[2][1]]
    end
    δ = 1e-6
    center = [q0[1], p0[1]]
    jacobian = hcat((phase_map(center + [δ, 0]) -
        phase_map(center - [δ, 0])) / (2δ),
        (phase_map(center + [0, δ]) -
        phase_map(center - [0, δ])) / (2δ))
    @test det(jacobian) ≈ 1.0 atol=2e-8
end

@testset "executable multinomial HMC" begin
    logdensity = q -> -sum(abs2, q) / 2
    gradient = identity
    events = [Runtime.NormalEvent(0.4), Runtime.NormalEvent(-0.3),
        Runtime.IndexEvent(big(1)), Runtime.UniformEvent(0.65)]
    reference_source = Runtime.FloatTraceSource(events)
    optimized_source = Runtime.FloatTraceSource(events)
    reference = Reference.multinomial_hmc_step!(reference_source, logdensity,
        gradient, 0.15, 3, [0.2, -0.1])
    optimized = Optimized.multinomial_hmc_step!(optimized_source, logdensity,
        gradient, 0.15, 3, [0.2, -0.1])
    @test optimized ≈ reference atol=2e-14
    @test Runtime.remaining(reference_source) == 0
    @test Runtime.remaining(optimized_source) == 0

    sampler = MultinomialHMC(logdensity, gradient, 0.2, 6)
    chain = sample(MersenneTwister(0x4d484d43), sampler, [0.0, 0.0], 25_000)
    retained = chain[:, 2501:end]
    @test maximum(abs.(vec(mean(retained; dims=2)))) < 0.08
    @test maximum(abs.(vec(var(retained; dims=2)) .- 1)) < 0.12
    @test_throws ArgumentError MultinomialHMC(logdensity, gradient, 0.2, 0)
end

@testset "constant-metric multinomial HMC" begin
    covariance = [1.0 0.4; 0.4 1.8]
    precision = inv(covariance)
    logdensity = q -> -dot(q, precision * q) / 2
    gradient = q -> precision * q
    for mass in ([1.0, 1.8], covariance)
        events = [Runtime.NormalEvent(0.3), Runtime.NormalEvent(-0.5),
            Runtime.IndexEvent(big(2)), Runtime.UniformEvent(0.45)]
        reference_source = Runtime.FloatTraceSource(events)
        optimized_source = Runtime.FloatTraceSource(events)
        reference = Reference.metric_multinomial_hmc_step!(reference_source,
            logdensity, gradient, 0.12, 4, [0.1, -0.2], mass)
        optimized = Optimized.metric_multinomial_hmc_step!(optimized_source,
            logdensity, gradient, 0.12, 4, [0.1, -0.2], mass)
        @test optimized ≈ reference atol=3e-14
        @test Runtime.remaining(reference_source) == 0
        @test Runtime.remaining(optimized_source) == 0
    end
    sampler = MetricMultinomialHMC(logdensity, gradient,
        DenseMetric(covariance), 0.18, 6)
    chain = sample(MersenneTwister(0x4d4d484d), sampler, zeros(2), 25_000)[:, 2501:end]
    @test maximum(abs.(cov(permutedims(chain)) - covariance)) < 0.15
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
                logdensity, gradient, 0.4, 3, current)
            optimized = Optimized.scalar_hmc_step!(optimized_source,
                logdensity, gradient, 0.4, 3, current)
            @test optimized == reference
            @test Runtime.remaining(reference_source) == 0
            @test Runtime.remaining(optimized_source) == 0
        end

        sampler = ScalarHMC(logdensity, gradient, 0.2, 5)
        chain = sample(MersenneTwister(0x4a3c), sampler, 0.0, 50_000)[5001:end]
        @test abs(mean(chain)) < 0.08
        @test abs(var(chain) - 1.0) < 0.12
        @test_throws ArgumentError ScalarHMC(logdensity, gradient, 0.0)
        @test_throws ArgumentError ScalarHMC(logdensity, gradient, 0.2, 0)

        quartic = ScalarHMC(x -> -x^4 / 4, x -> x^3, 0.15, 6)
        quartic_chain = sample(MersenneTwister(0x71a4), quartic, 0.0, 40_000)[4001:end]
        @test abs(mean(quartic_chain)) < 0.08
        # For density proportional to exp(-x^4/4), E[X^2] ≈ 0.67597824.
        @test abs(mean(abs2, quartic_chain) - 0.67597824) < 0.08
    end
    @testset "vector HMC reference, integrator, and moments" begin
        logdensity = q -> -sum(abs2, q) / 2
        gradient = identity
        events = [Runtime.NormalEvent(0.5), Runtime.NormalEvent(-0.75),
            Runtime.UniformEvent(0.2)]
        reference_source = Runtime.FloatTraceSource(events)
        optimized_source = Runtime.FloatTraceSource(events)
        reference = Reference.vector_hmc_step!(reference_source,
            logdensity, gradient, 0.25, 4, [0.2, -0.1])
        optimized = Optimized.vector_hmc_step!(optimized_source,
            logdensity, gradient, 0.25, 4, [0.2, -0.1])
        @test optimized == reference
        @test Runtime.remaining(reference_source) == 0
        @test Runtime.remaining(optimized_source) == 0

        q0, p0 = [0.7, -0.2], [-0.4, 0.9]
        q, p = copy(q0), copy(p0)
        for _ in 1:20
            q, p = Optimized.vector_leapfrog(gradient, 0.05, q, p)
        end
        p = -p
        for _ in 1:20
            q, p = Optimized.vector_leapfrog(gradient, 0.05, q, p)
        end
        @test q ≈ q0 atol=1e-12
        @test p ≈ -p0 atol=1e-12

        sampler = VectorHMC(logdensity, gradient, 0.18, 6)
        chain = sample(MersenneTwister(0x8c21), sampler, [0.0, 0.0], 40_000)
        retained = @view chain[:, 4001:end]
        @test all(abs.(vec(mean(retained; dims=2))) .< 0.08)
        covariance = cov(permutedims(retained))
        @test maximum(abs.(covariance - I)) < 0.12
        @test size(sample(MersenneTwister(1), sampler, [0.0, 0.0], 3)) == (2, 3)
        @test_throws ArgumentError VectorHMC(logdensity, gradient, 0.0)
        @test_throws ArgumentError step(MersenneTwister(1), sampler, Float64[])
    end
    @testset "constant-metric vector HMC" begin
        covariance = [1.0 0.85; 0.85 2.0]
        precision = inv(covariance)
        logdensity = q -> -dot(q, precision * q) / 2
        gradient = q -> precision * q

        for mass in ([1.0, 2.0], [1.0 0.3; 0.3 1.5])
            events = [Runtime.NormalEvent(0.4), Runtime.NormalEvent(-0.7),
                Runtime.UniformEvent(0.25)]
            reference_source = Runtime.FloatTraceSource(events)
            optimized_source = Runtime.FloatTraceSource(events)
            reference = Reference.metric_hmc_step!(reference_source,
                logdensity, gradient, 0.12, 5, [0.2, -0.1], mass)
            optimized = Optimized.metric_hmc_step!(optimized_source,
                logdensity, gradient, 0.12, 5, [0.2, -0.1], mass)
            @test optimized ≈ reference atol=2e-15
            @test Runtime.remaining(reference_source) == 0
            @test Runtime.remaining(optimized_source) == 0
        end

        diagonal_sampler = MetricHMC(logdensity, gradient,
            DiagonalMetric(diag(covariance)), 0.14, 7)
        diagonal_chain = sample(MersenneTwister(0xd1a6), diagonal_sampler,
            [0.0, 0.0], 35_000)[:, 3501:end]
        @test maximum(abs.(cov(permutedims(diagonal_chain)) - covariance)) < 0.15

        dense_sampler = MetricHMC(logdensity, gradient,
            DenseMetric(covariance), 0.16, 6)
        dense_chain = sample(MersenneTwister(0xde45), dense_sampler,
            [0.0, 0.0], 35_000)[:, 3501:end]
        @test maximum(abs.(cov(permutedims(dense_chain)) - covariance)) < 0.15

        # Finite-difference phase Jacobian for a dense constant metric.
        mass = [1.0 0.25; 0.25 1.4]
        phase_map = function (state)
            q, p = state[1:2], state[3:4]
            p_half = p - 0.05 .* gradient(q)
            q_next = q + 0.1 .* (mass \ p_half)
            p_next = p_half - 0.05 .* gradient(q_next)
            [q_next; p_next]
        end
        point, δ = [0.3, -0.2, 0.4, 0.1], 1e-6
        jacobian = hcat([(phase_map(point + δ .* (1:4 .== j)) -
            phase_map(point - δ .* (1:4 .== j))) ./ (2δ) for j in 1:4]...)
        @test det(jacobian) ≈ 1.0 atol=1e-8

        ill_covariance = Diagonal([1e-2, 1e2])
        ill_precision = inv(ill_covariance)
        ill_sampler = MetricHMC(q -> -dot(q, ill_precision * q) / 2,
            q -> ill_precision * q, DenseMetric(Matrix(ill_precision)), 0.15, 8)
        ill_chain = sample(MersenneTwister(0x111c), ill_sampler,
            [0.0, 0.0], 25_000)[:, 2501:end]
        standardized_variances = vec(var(ill_chain; dims=2)) ./ diag(ill_covariance)
        @test maximum(abs.(standardized_variances .- 1)) < 0.18

        @test_throws ArgumentError DiagonalMetric([1.0, 0.0])
        @test_throws ArgumentError DenseMetric([1.0 2.0; 2.0 1.0])
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
