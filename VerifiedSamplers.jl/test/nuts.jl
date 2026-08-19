@testset "fixed-parameter NUTS family" begin
    logdensity(q) = -sum(abs2, q) / 2
    gradient(q) = q

    for termination in (:classic, :generalized),
            selection in (:multinomial, :slice)
        sampler = NUTS(logdensity, gradient, 0.2;
            max_depth=5, max_energy_error=100.0, termination, selection)
        first = sample_with_diagnostics(
            MersenneTwister(0x8100 + Int(termination === :generalized) * 16 +
                Int(selection === :slice)), sampler, zeros(2), 80)
        second = sample_with_diagnostics(
            MersenneTwister(0x8100 + Int(termination === :generalized) * 16 +
                Int(selection === :slice)), sampler, zeros(2), 80)
        @test first.samples == second.samples
        @test size(first.samples) == (2, 80)
        @test all(isfinite, first.samples)
        @test any(result -> result.moved, first.diagnostics)
        @test all(result -> 0 <= result.tree_depth <= 5, first.diagnostics)
        @test all(result -> result.leapfrog_steps >= 1, first.diagnostics)
        @test all(result -> 0 <= result.acceptance_rate <= 1,
            first.diagnostics)
        @test all(result -> result.termination === termination,
            first.diagnostics)
        @test all(result -> result.selection === selection,
            first.diagnostics)
    end

    metrics = (
        DiagonalMetric([1.0, 2.0]),
        DenseMetric([1.0 0.2; 0.2 1.5]),
        RankUpdateMetric([1.0, 2.0], [1.0; -0.5;;], [0.25;;]),
    )
    for (index, metric) in enumerate(metrics)
        metric_sampler = NUTS(logdensity, gradient, 0.15;
            metric, max_depth=4)
        metric_chain = sample(
            MersenneTwister(0x8120 + index), metric_sampler, zeros(2), 40)
        @test size(metric_chain) == (2, 40)
        @test all(isfinite, metric_chain)
    end

    divergent = NUTS(logdensity, gradient, 10.0;
        max_depth=3, max_energy_error=0.01)
    result = transition(MersenneTwister(0x8121), divergent, zeros(2))
    @test result.divergent
    @test result.position == zeros(2)

    depth_limited = NUTS(logdensity, gradient, 0.01;
        max_depth=1, max_energy_error=100.0)
    limited_result = transition(
        MersenneTwister(0x8123), depth_limited, zeros(2))
    @test limited_result.tree_depth == 1
    @test limited_result.leapfrog_steps == 1
    @test limited_result.reached_max_depth
    @test !limited_result.divergent
    @test isfinite(limited_result.hamiltonian_energy)
    @test isfinite(limited_result.hamiltonian_energy_error)
    @test isfinite(limited_result.max_hamiltonian_energy_error)

    gaussian = NUTS(logdensity, gradient, 0.25;
        max_depth=6, termination=:generalized, selection=:multinomial)
    draws = sample(MersenneTwister(0x8122), gaussian, zeros(2), 4_000)[:, 501:end]
    @test all(abs.(vec(mean(draws; dims=2))) .< 0.10)
    @test all(abs.(vec(var(draws; dims=2)) .- 1) .< 0.15)

    @test_throws ArgumentError NUTS(logdensity, gradient, 0.2;
        termination=:unknown)
    @test_throws ArgumentError NUTS(logdensity, gradient, 0.2;
        selection=:unknown)
    @test_throws ArgumentError NUTS(logdensity, gradient, 0.2;
        max_depth=0)
    @test_throws ArgumentError NUTS(logdensity, gradient, 0.2;
        max_energy_error=Inf)
end
