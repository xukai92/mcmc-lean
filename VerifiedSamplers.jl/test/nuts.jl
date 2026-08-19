@testset "fixed-parameter NUTS family" begin
    logdensity(q) = -sum(abs2, q) / 2
    gradient(q) = q

    namespaced = Optimized.NUTS(logdensity, gradient, 0.2)
    @test typeof(namespaced).name.module === Optimized
    @test NUTS !== Optimized.NUTS

    for (integrator_index, integrator) in enumerate(
            (:leapfrog, :jittered, :tempered)),
            (termination_index, termination) in enumerate(
                (:classic, :generalized, :strict_generalized)),
            selection in (:multinomial, :slice)
        sampler = Optimized.NUTS(logdensity, gradient, 0.2;
            max_depth=5, max_energy_error=100.0, termination, selection,
            integrator, jitter=0.2, temperature=1.1)
        first = sample_with_diagnostics(
            MersenneTwister(0x8100 + integrator_index * 64 +
                termination_index * 16 +
                Int(selection === :slice)), sampler, zeros(2), 80)
        second = sample_with_diagnostics(
            MersenneTwister(0x8100 + integrator_index * 64 +
                termination_index * 16 +
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
    for (metric_index, metric) in enumerate(metrics),
            (integrator_index, integrator) in enumerate(
                (:leapfrog, :jittered, :tempered))
        metric_sampler = Optimized.NUTS(logdensity, gradient, 0.15;
            metric, max_depth=4, integrator, jitter=0.2, temperature=1.1)
        metric_chain = sample(
            MersenneTwister(0x8400 + 16metric_index + integrator_index),
            metric_sampler, zeros(2), 40)
        @test size(metric_chain) == (2, 40)
        @test all(isfinite, metric_chain)
    end

    jitter_source = Runtime.FloatTraceSource([Runtime.UniformEvent(0.75)])
    jittered = Optimized.NUTS(logdensity, gradient, 0.2;
        integrator=:jittered, jitter=0.25)
    @test VerifiedSamplers._nuts_step_size!(jitter_source, jittered) == 0.225
    @test Runtime.remaining(jitter_source) == 0

    ordinary = Optimized.NUTS(logdensity, gradient, 0.2;
        integrator=:leapfrog, max_depth=5)
    neutral_tempering = Optimized.NUTS(logdensity, gradient, 0.2;
        integrator=:tempered, temperature=1.0, max_depth=5)
    @test sample(MersenneTwister(0x8450), ordinary, zeros(2), 80) ==
        sample(MersenneTwister(0x8450), neutral_tempering, zeros(2), 80)

    divergent = Optimized.NUTS(logdensity, gradient, 10.0;
        max_depth=3, max_energy_error=0.01)
    result = transition(MersenneTwister(0x8121), divergent, zeros(2))
    @test result.divergent
    @test result.position == zeros(2)
    @test result.tree_depth == 0

    # Slice-mode numerical termination uses the sampled log-slice threshold,
    # whereas multinomial mode uses the fixed energy-error threshold. This
    # deliberately inconsistent force creates a known energy error of 1/2.
    flat_logdensity(q) = 0.0
    constant_gradient(q) = ones(length(q))
    slice_divergence = Optimized.NUTS(flat_logdensity, constant_gradient, 1.0;
        max_depth=1, max_energy_error=0.1, selection=:slice)
    multinomial_divergence = Optimized.NUTS(flat_logdensity, constant_gradient, 1.0;
        max_depth=1, max_energy_error=0.1, selection=:multinomial)
    velocity = identity
    phase = VerifiedSamplers._nuts_phase(
        slice_divergence, [0.0], [0.0], velocity)
    slice_tree = VerifiedSamplers._build_nuts_tree!(
        Runtime.FloatTraceSource(Runtime.FloatTraceEvent[]), slice_divergence,
        phase, 1, 0, phase.energy, phase.logweight - 1.0, velocity)
    multinomial_tree = VerifiedSamplers._build_nuts_tree!(
        Runtime.FloatTraceSource(Runtime.FloatTraceEvent[]), multinomial_divergence,
        phase, 1, 0, phase.energy, -Inf, velocity)
    @test slice_tree.max_energy_error ≈ 0.5
    @test !slice_tree.divergent
    @test multinomial_tree.divergent

    left_phase = VerifiedSamplers._NUTSPhase([0.0], [0.0], log(2.0), 0.0)
    right_phase = VerifiedSamplers._NUTSPhase([1.0], [0.0], 0.0, 0.0)
    current_tree = VerifiedSamplers._NUTSTree(left_phase, left_phase,
        left_phase, [0.0], log(2.0), 2, 0.0, 1, 0.0, false, false)
    proposed_tree = VerifiedSamplers._NUTSTree(right_phase, right_phase,
        right_phase, [0.0], 0.0, 1, 0.0, 1, 0.0, false, false)
    for selection in (:slice, :multinomial)
        accepted = VerifiedSamplers._choose_outer_candidate!(
            Runtime.FloatTraceSource([Runtime.UniformEvent(0.4)]),
            selection, current_tree, proposed_tree)
        rejected = VerifiedSamplers._choose_outer_candidate!(
            Runtime.FloatTraceSource([Runtime.UniformEvent(0.6)]),
            selection, current_tree, proposed_tree)
        @test accepted.position == [1.0]
        @test rejected.position == [0.0]
    end

    # The strict generalized criterion adds the two subtree checks used by
    # AdvancedHMC. This synthetic merge passes the ordinary whole-tree check
    # but turns at the left/subtree interface.
    phase(momentum) = VerifiedSamplers._NUTSPhase(
        [0.0], [momentum], 0.0, 0.0)
    left_tree = VerifiedSamplers._NUTSTree(phase(1.0), phase(1.0),
        phase(1.0), [-10.0], 0.0, 1, 0.0, 1, 0.0, false, false)
    right_tree = VerifiedSamplers._NUTSTree(phase(1.0), phase(1.0),
        phase(1.0), [20.0], 0.0, 1, 0.0, 1, 0.0, false, false)
    generalized = Optimized.NUTS(logdensity, gradient, 0.2;
        termination=:generalized)
    strict = Optimized.NUTS(logdensity, gradient, 0.2;
        termination=:strict_generalized)
    ordinary_merge = VerifiedSamplers._combine_nuts_trees(
        generalized, left_tree, right_tree, identity, phase(1.0))
    strict_merge = VerifiedSamplers._combine_nuts_trees(
        strict, left_tree, right_tree, identity, phase(1.0))
    @test !ordinary_merge.stopped
    @test strict_merge.stopped

    depth_limited = Optimized.NUTS(logdensity, gradient, 0.01;
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

    for (index, integrator) in enumerate((:leapfrog, :jittered, :tempered))
        gaussian = Optimized.NUTS(logdensity, gradient, 0.25;
            max_depth=6, termination=:generalized, selection=:multinomial,
            integrator, jitter=0.2, temperature=1.1)
        draws = sample(MersenneTwister(0x8122 + index), gaussian,
            zeros(2), 4_000)[:, 501:end]
        @test all(abs.(vec(mean(draws; dims=2))) .< 0.10)
        @test all(abs.(vec(var(draws; dims=2)) .- 1) .< 0.15)
    end

    @test_throws ArgumentError Optimized.NUTS(logdensity, gradient, 0.2;
        termination=:unknown)
    @test_throws ArgumentError Optimized.NUTS(logdensity, gradient, 0.2;
        selection=:unknown)
    @test_throws ArgumentError Optimized.NUTS(logdensity, gradient, 0.2;
        max_depth=0)
    @test_throws ArgumentError Optimized.NUTS(logdensity, gradient, 0.2;
        max_energy_error=Inf)
    @test_throws ArgumentError Optimized.NUTS(logdensity, gradient, 0.2;
        integrator=:unknown)
    @test_throws ArgumentError Optimized.NUTS(logdensity, gradient, 0.2;
        integrator=:jittered, jitter=1.0)
    @test_throws ArgumentError Optimized.NUTS(logdensity, gradient, 0.2;
        integrator=:tempered, temperature=0.0)
end
