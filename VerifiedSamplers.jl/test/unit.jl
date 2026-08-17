@testset "runtime primitive units" begin
    rng_source = Runtime.RNGSource(MersenneTwister(12))
    @test all(0 <= Runtime.draw_below!(rng_source, 7) < 7 for _ in 1:100)
    @test_throws ArgumentError Runtime.draw_below!(rng_source, 0)

    trace_source = Runtime.TraceSource([2, 0])
    @test Runtime.draw_below!(trace_source, 3) == 2
    @test Runtime.draw_below!(trace_source, 1) == 0
    @test trace_source.requested_bounds == [3, 1]
    @test Runtime.remaining(trace_source) == 0
    @test_throws EOFError Runtime.draw_below!(trace_source, 1)

    @test_throws ArgumentError Runtime.draw_below!(Runtime.TraceSource([3]), 3)
    float_indices = Runtime.FloatTraceSource([Runtime.IndexEvent(big(1))])
    @test Runtime.draw_below!(float_indices, 3) == 1
    @test Runtime.remaining(float_indices) == 0
    @test_throws ArgumentError Reference.categorical_index!(Runtime.TraceSource([0]), [1, -1])
    @test_throws ArgumentError Optimized.categorical_index!(Runtime.TraceSource([0]), [1, -1])
    @test_throws ArgumentError sample(MersenneTwister(1), FiniteWeights([1]), -1)
end


@testset "implicit solver certificates" begin
    approximate = Certificates.certify_implicit_solve(1e-8, 1e-8, 2e-8, 2e-8;
        unique=true, reversible=true, volume_preserving=true)
    @test !Certificates.certifies_exact_solver(approximate)
    exact = Certificates.certify_implicit_solve(0.0, 0.0, 0.0, 0.0;
        unique=true, reversible=true, volume_preserving=true)
    @test Certificates.certifies_exact_solver(exact)
    missing_global = Certificates.certify_implicit_solve(0.0, 0.0, 0.0, 0.0)
    @test !Certificates.certifies_exact_solver(missing_global)
    @test_throws ArgumentError Certificates.certify_implicit_solve(1e-3, 1e-4, 0, 0)
end

@testset "bounded numeric decision certificates" begin
    witness = Certificates.certify_bound(0.5, big"0.5", big"0.0")
    @test witness.observed_error == 0

    stable = Certificates.certify_decision(
        0.25, big"0.25", big"0.0",
        0.75, big"0.75", big"0.0")
    @test Certificates.is_stable(stable)
    @test Certificates.uncertainty_band(stable) == 0

    boundary = Certificates.certify_decision(
        0.5, big"0.5", big"0.01",
        0.5, big"0.5", big"0.01")
    @test !Certificates.is_stable(boundary)
    @test_throws ArgumentError Certificates.certify_bound(0.5, big"0.6", big"0.01")
    @test_throws ArgumentError Certificates.certify_bound(Inf, big"1.0", big"1.0")

    leapfrog_parameters = Certificates.EuclideanLeapfrogErrorParameters(
        0.1, 1.0, 0.01, 1e-4, 2e-4)
    leapfrog_schedule = Certificates.leapfrog_error_schedule(
        leapfrog_parameters, 4)
    @test length(leapfrog_schedule) == 5
    @test leapfrog_schedule[1] == (; position=big"0", momentum=big"0")
    @test all(item.position >= 0 && item.momentum >= 0
        for item in leapfrog_schedule)
    @test all(leapfrog_schedule[index].position <=
        leapfrog_schedule[index + 1].position for index in 1:4)
    @test_throws ArgumentError Certificates.EuclideanLeapfrogErrorParameters(
        -0.1, 1.0, 0.01, 1e-4, 2e-4)
    @test_throws ArgumentError Certificates.leapfrog_error_schedule(
        leapfrog_parameters, -1)

    negative_sign = Certificates.certify_zero_decision(
        -2.0, big"-1.9", big"0.11")
    positive_sign = Certificates.certify_zero_decision(
        2.0, big"1.9", big"0.11")
    boundary_sign = Certificates.certify_zero_decision(
        0.125, big"0.125", big"0.125")
    @test Certificates.is_stable(negative_sign)
    @test Certificates.is_stable(positive_sign)
    @test !Certificates.is_stable(boundary_sign)

    separated_comparison = Certificates.certify_comparison(
        0.5, big"0.51", big"0.02", 1.0, big"0.99", big"0.02")
    ambiguous_comparison = Certificates.certify_comparison(
        0.99, big"0.99", big"0.01", 1.0, big"1.0", big"0.01")
    @test Certificates.is_stable(separated_comparison)
    @test !Certificates.is_stable(ambiguous_comparison)

    eligible_leaf = Certificates.certify_nuts_leaf_energy(
        computed_log_slice=-2.0, ideal_log_slice=big"-2.0", log_slice_bound=0,
        computed_energy=1.0, ideal_energy=big"1.0", energy_bound=0,
        computed_max_energy_error=100.0, ideal_max_energy_error=big"100.0",
        max_energy_error_bound=0)
    ineligible_leaf = Certificates.certify_nuts_leaf_energy(
        computed_log_slice=-0.5, ideal_log_slice=big"-0.5", log_slice_bound=0,
        computed_energy=1.0, ideal_energy=big"1.0", energy_bound=0,
        computed_max_energy_error=100.0, ideal_max_energy_error=big"100.0",
        max_energy_error_bound=0)
    boundary_leaf = Certificates.certify_nuts_leaf_energy(
        computed_log_slice=-1.0, ideal_log_slice=big"-1.0", log_slice_bound=0,
        computed_energy=1.0, ideal_energy=big"1.0", energy_bound=0,
        computed_max_energy_error=100.0, ideal_max_energy_error=big"100.0",
        max_energy_error_bound=0)
    @test Certificates.certified_nuts_leaf_decisions(eligible_leaf) ==
        (; eligible=true, continues=true)
    @test Certificates.certified_nuts_leaf_decisions(ineligible_leaf) ==
        (; eligible=false, continues=true)
    @test Certificates.certified_nuts_leaf_decisions(boundary_leaf) === nothing

    uturn = Certificates.certify_uturn_decision(
        -2.0, big"-1.9", big"0.11", 3.0, big"2.9", big"0.11")
    ambiguous_uturn = Certificates.certify_uturn_decision(
        -2.0, big"-1.9", big"0.11", 0.125, big"0.125", big"0.125")
    @test Certificates.is_stable(uturn)
    @test !Certificates.is_stable(ambiguous_uturn)
    nuts_tree = Certificates.NUTSCompletedTreeCertificate(
        [eligible_leaf, ineligible_leaf], [uturn])
    ambiguous_nuts_tree = Certificates.NUTSCompletedTreeCertificate(
        [eligible_leaf, boundary_leaf], [uturn])
    @test Certificates.certified_nuts_completed_tree(nuts_tree) ==
        (; eligible=[true, false], continues=[true, true], turns=[true])
    @test Certificates.certified_nuts_completed_tree(ambiguous_nuts_tree) === nothing
    vector_uturn = Certificates.certify_vector_uturn_decision(
        [0.0, 0.0], BigFloat[0, 0], [0.0, 0.0],
        [1.0, 1.0], BigFloat[1, 1], [0.0, 0.0],
        [-1.0, -1.0], BigFloat[-1, -1], [0.0, 0.0],
        [1.0, 1.0], BigFloat[1, 1], [0.0, 0.0])
    vector_boundary = Certificates.certify_vector_uturn_decision(
        [0.0, 0.0], BigFloat[0, 0], [0.0, 0.0],
        [1.0, 0.0], BigFloat[1, 0], [0.0, 0.0],
        [0.0, 1.0], BigFloat[0, 1], [0.0, 0.0],
        [1.0, 0.0], BigFloat[1, 0], [0.0, 0.0])
    @test Certificates.is_stable(vector_uturn)
    @test !Certificates.is_stable(vector_boundary)
    @test Certificates.certified_uturn_decision(vector_uturn) === true
    @test Certificates.certified_uturn_decision(vector_boundary) === nothing
    trajectory = Certificates.certify_vector_uturn_trajectory(
        [[0.0, 0.0], [1.0, 1.0], [2.0, 2.0]],
        [BigFloat[0, 0], BigFloat[1, 1], BigFloat[2, 2]],
        [zeros(2), zeros(2), zeros(2)],
        [[1.0, 1.0], [1.0, 1.0], [1.0, 1.0]],
        [BigFloat[1, 1], BigFloat[1, 1], BigFloat[1, 1]],
        [zeros(2), zeros(2), zeros(2)])
    @test Certificates.is_stable(trajectory)
    @test Certificates.certified_uturn_decisions(trajectory) == [false, false]
    @test_throws ArgumentError Certificates.certify_vector_uturn_trajectory(
        Vector{Vector{Float64}}(), Vector{Vector{BigFloat}}(),
        Vector{Vector{Float64}}(), Vector{Vector{Float64}}(),
        Vector{Vector{BigFloat}}(), Vector{Vector{Float64}}())
    @test_throws DimensionMismatch Certificates.certify_vector_uturn_decision(
        [0.0], BigFloat[0, 0], [0.0],
        [1.0], BigFloat[1], [0.0],
        [-1.0], BigFloat[-1], [0.0],
        [1.0], BigFloat[1], [0.0])
    completed_tree = Certificates.CompletedTreeDecisionCertificate(
        [separated_comparison], [uturn])
    ambiguous_tree = Certificates.CompletedTreeDecisionCertificate(
        [separated_comparison, ambiguous_comparison], [uturn])
    @test Certificates.is_stable(completed_tree)
    @test !Certificates.is_stable(ambiguous_tree)
    @test Certificates.is_stable(
        Certificates.CompletedTreeDecisionCertificate(
            Certificates.SeparatedComparisonCertificate[],
            Certificates.UTurnDecisionCertificate[]))

    rwmh = Certificates.certify_rwmh_decision(
        computed_current_logdensity=-0.5, ideal_current_logdensity=big"-0.5",
        current_logdensity_bound=0,
        computed_proposal_logdensity=-0.5, ideal_proposal_logdensity=big"-0.5",
        proposal_logdensity_bound=0,
        computed_threshold=1.0, ideal_threshold=big"1.0",
        exp_bound=0, computed_uniform=0.25, ideal_uniform=big"0.25",
        uniform_bound=0)
    @test rwmh.algorithm == :rwmh
    @test Certificates.is_stable(rwmh)

    hmc = Certificates.certify_hmc_decision(
        computed_current_energy=1.0, ideal_current_energy=big"1.0",
        current_energy_bound=0,
        computed_proposal_energy=1.0, ideal_proposal_energy=big"1.0",
        proposal_energy_bound=0,
        computed_threshold=1.0, ideal_threshold=big"1.0", exp_bound=0,
        computed_uniform=0.5, ideal_uniform=big"0.5", uniform_bound=0)
    @test hmc.algorithm == :hmc
    @test Certificates.is_stable(hmc)

    multinomial = Certificates.certify_multinomial_selection(
        [0.2, 0.6, 1.0], BigFloat[0.2, 0.6, 1.0], 1e-15,
        0.4, BigFloat(0.4), 1e-15)
    @test Certificates.is_stable(multinomial)
    near_boundary = Certificates.certify_multinomial_selection(
        [0.2, 0.6, 1.0], BigFloat[0.2, 0.6, 1.0], 1e-3,
        0.6005, BigFloat(0.6005), 1e-3)
    @test !Certificates.is_stable(near_boundary)
    @test_throws DimensionMismatch Certificates.certify_multinomial_selection(
        [0.5], BigFloat[0.5, 1.0], 0, 0.2, BigFloat(0.2), 0)
end


@testset "continuous callback and state validation" begin
    @test_throws ArgumentError Reference.gaussian_rwmh_step!(
        Runtime.FloatTraceSource(Runtime.FloatTraceEvent[]), identity, 1.0, Inf)
    @test_throws DomainError Reference.gaussian_rwmh_step!(
        Runtime.FloatTraceSource([Runtime.NormalEvent(0.0)]), _ -> NaN, 1.0, 0.0)
    @test_throws DimensionMismatch Reference.vector_hmc_step!(
        Runtime.FloatTraceSource([Runtime.NormalEvent(0.0), Runtime.NormalEvent(0.0)]),
        q -> -sum(abs2, q) / 2, _ -> [0.0], 0.1, 2, [0.0, 0.0])
    @test_throws DomainError Reference.multinomial_hmc_step!(
        Runtime.FloatTraceSource([Runtime.NormalEvent(0.0), Runtime.IndexEvent(big(0))]),
        q -> -sum(abs2, q) / 2, _ -> [Inf], 0.1, 1, [0.0])
    @test_throws ArgumentError Reference.metric_hmc_step!(
        Runtime.FloatTraceSource([Runtime.NormalEvent(0.0), Runtime.NormalEvent(0.0)]),
        q -> -sum(abs2, q) / 2, identity, 0.1, 1, [0.0, 0.0],
        [1.0 0.5; 0.0 1.0])
end

@testset "versioned reference IR" begin
    @test Reference.IR_FORMAT_VERSION == 17
    @test sort!(collect(keys(Reference.PROGRAMS))) ==
        ["categorical_index!", "certified_relativistic_multinomial_hmc_step!",
        "coupled_gaussian_rwmh_step!",
        "coupled_multinomial_hmc_step!", "dense_hmc_step!", "dense_multinomial_hmc_step!",
        "diagonal_hmc_step!", "diagonal_multinomial_hmc_step!",
        "finite_mh_step!", "gaussian_rwmh_step!", "multinomial_hmc_step!",
        "relativistic_multinomial_hmc_step!", "scalar_hmc_step!",
        "vector_hmc_step!", "xu21_coupled_step!"]
    transform = generated_transform("positive-log")
    @test transform.transform == "positive-log"
    @test transform.constrained_type == "positive-real"
    @test transform.unconstrained_type == "real"
    @test transform.forward == "log"
    @test transform.inverse == "exp"
    @test transform.logabsdet_inverse_jacobian == "identity"
    unit_transform = generated_transform("open-unit-artanh")
    @test unit_transform.transform == "open-unit-artanh"
    @test unit_transform.constrained_type == "open-unit-interval"
    @test unit_transform.forward == "artanh-affine"
    @test unit_transform.inverse == "tanh-affine"
    @test unit_transform.logabsdet_inverse_jacobian ==
        "log-one-minus-tanh-sq-minus-log-two"
    @test_throws ArgumentError generated_transform("missing")
    @test collect(keys(Reference.DYNAMIC_TREES)) ==
        ["checked-recursive-doubling"]
    dynamic = Reference.DYNAMIC_TREES["checked-recursive-doubling"]
    @test dynamic.builder == "recursive-doubling"
    @test dynamic.stop_rule == "endpoint-uturn"
    @test dynamic.subtree_policy == "recursive-exclusion"
    @test dynamic.selection_policy == "eligible-count-streaming"
    @test dynamic.failure_policy == "checked-or-identity"
    @test_throws ArgumentError generated_dynamic_tree(
        "missing", [0.0], [1.0], Bool[])
    @test_throws ErrorException Reference.parse_document("(unterminated")
    mktemp() do path, stream
        write(stream, "(verified-samplers-ir 2 bogus)\n")
        close(stream)
        @test_throws ErrorException Reference.load_programs(path)
    end
end
