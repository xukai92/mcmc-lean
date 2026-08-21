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

    @test Runtime.checked_positive_float(0.5, "scale") === 0.5
    @test Runtime.checked_positive_count(big(3), "steps") === 3
    @test Runtime.checked_finite_float(2, "state") === 2.0
    @test_throws ArgumentError Runtime.checked_positive_float(Inf, "scale")
    @test_throws ArgumentError Runtime.checked_positive_float(0, "scale")
    @test_throws ArgumentError Runtime.checked_positive_count(0, "steps")
    @test_throws ArgumentError Runtime.checked_finite_float(NaN, "state")
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
    dyadic_q, dyadic_p = 0.0, 1.0
    for iteration in 1:8
        dyadic = Certificates.certify_gaussian_dyadic_leapfrog_step(
            0.5, dyadic_q, dyadic_p)
        optimized_q, optimized_p = Optimized.leapfrog(
            identity, 0.5, dyadic_q, dyadic_p)
        @test (dyadic.next_position, dyadic.next_momentum) ==
            (optimized_q, optimized_p)
        if isfile(ORACLE)
            arguments = Certificates.gaussian_dyadic_leapfrog_certificate_arguments(
                dyadic)
            @test readchomp(`$ORACLE gaussian_dyadic_leapfrog $arguments`) == "ok"
            if iteration == 1
                tampered = copy(arguments)
                tampered[end] = "0/1"
                @test readchomp(`$ORACLE gaussian_dyadic_leapfrog $tampered`) ==
                    "error invalidGaussianDyadicLeapfrog"
            end
        end
        dyadic_q, dyadic_p = dyadic.next_position, dyadic.next_momentum
    end
    @test_throws InexactError Certificates.certify_gaussian_dyadic_leapfrog_step(
        0.1, 0.0, 1.0)
    rounded = Certificates.certify_gaussian_rounded_leapfrog_step(0.1, 0.0, 1.0)
    rounded_q, rounded_p = Optimized.leapfrog(identity, 0.1, 0.0, 1.0)
    @test (rounded.next_position, rounded.next_momentum) ==
        (rounded_q, rounded_p)
    @test rounded.next_momentum_error > 0
    if isfile(ORACLE)
        arguments = Certificates.gaussian_rounded_leapfrog_certificate_arguments(
            rounded)
        @test readchomp(`$ORACLE gaussian_rounded_leapfrog $arguments`) == "ok"
        tampered = copy(arguments)
        tampered[end] = "0/1"
        @test readchomp(`$ORACLE gaussian_rounded_leapfrog $tampered`) ==
            "error invalidGaussianRoundedLeapfrog"
    end
    quartic_gradient(x) = restricted_value_gradient_hessian(
        restricted_quartic_potential, x)[2]
    quartic_step = Certificates.certify_rounded_leapfrog_step(
        0.15, 0.2, 0.7, quartic_gradient)
    quartic_q, quartic_p = Optimized.leapfrog(
        quartic_gradient, 0.15, 0.2, 0.7)
    @test (quartic_step.next_position, quartic_step.next_momentum) ==
        (quartic_q, quartic_p)
    current_quartic = certify_restricted_quartic_float64(quartic_step.position)
    next_quartic = certify_restricted_quartic_float64(quartic_step.next_position)
    @test current_quartic.computed_derivative == quartic_step.current_gradient
    @test next_quartic.computed_derivative == quartic_step.next_gradient
    if isfile(ORACLE)
        arithmetic_arguments =
            Certificates.rounded_leapfrog_certificate_arguments(quartic_step)
        current_arguments = restricted_quartic_certificate_arguments(current_quartic)
        next_arguments = restricted_quartic_certificate_arguments(next_quartic)
        @test readchomp(`$ORACLE rounded_leapfrog $arithmetic_arguments`) == "ok"
        @test readchomp(`$ORACLE quartic_certificate $current_arguments`) == "ok"
        @test readchomp(`$ORACLE quartic_certificate $next_arguments`) == "ok"
    end
    coordinate_step = Certificates.certify_leapfrog_coordinate_step(
        leapfrog_parameters;
        signed_step=0.1,
        computed_position=0.0, ideal_position=big"0",
        computed_momentum=1.0, ideal_momentum=big"1",
        computed_current_gradient=0.0, ideal_current_gradient=big"0",
        computed_half_momentum=1.0, computed_next_position=0.1,
        computed_next_gradient=-0.1,
        ideal_next_gradient=BigFloat(-0.1),
        computed_next_momentum=0.995,
        position_error=0, momentum_error=0)
    @test coordinate_step.next_position_error == leapfrog_schedule[2].position
    @test coordinate_step.next_momentum_error == leapfrog_schedule[2].momentum
    vector_step = Certificates.certify_leapfrog_vector_step(
        leapfrog_parameters;
        signed_step=0.1,
        computed_position=[0.0, 0.0], ideal_position=BigFloat[0, 0],
        computed_momentum=[1.0, 2.0], ideal_momentum=BigFloat[1, 2],
        computed_current_gradient=[0.0, 0.0],
        ideal_current_gradient=BigFloat[0, 0],
        computed_half_momentum=[1.0, 2.0],
        computed_next_position=[0.1, 0.2],
        computed_next_gradient=[-0.1, -0.2],
        ideal_next_gradient=BigFloat[BigFloat(-0.1), BigFloat(-0.2)],
        computed_next_momentum=[0.995, 1.99],
        position_error=0, momentum_error=0)
    @test length(vector_step.coordinates) == 2
    @test vector_step.next_position_error == leapfrog_schedule[2].position
    @test vector_step.next_momentum_error == leapfrog_schedule[2].momentum
    linked_trajectory = Certificates.certify_linked_leapfrog_vector_trajectory(
        [0.0, 0.0], BigFloat[0, 0], [1.0, 2.0], BigFloat[1, 2],
        [vector_step])
    @test length(linked_trajectory.steps) == 1
    recursive_uturn = Certificates.certify_recursive_doubling_uturn_matrix(
        linked_trajectory)
    @test recursive_uturn.count == 2
    @test length(recursive_uturn.pairs) == 2
    @test Certificates.is_stable(recursive_uturn)
    @test Certificates.certified_uturn_decisions(recursive_uturn) ==
        Dict((1, 2) => false, (2, 1) => true)
    @test_throws ArgumentError Certificates.certify_recursive_doubling_uturn_matrix(
        linked_trajectory; initial_position_error=-1)
    @test_throws ArgumentError Certificates.certify_linked_leapfrog_vector_trajectory(
            [1.0, 0.0], BigFloat[0, 0], [1.0, 2.0], BigFloat[1, 2],
            [vector_step])
    @test_throws ArgumentError Certificates.certify_linked_leapfrog_vector_trajectory(
            [0.0, 0.0], BigFloat[0, 0], [1.0, 2.0], BigFloat[1, 2],
            [vector_step, vector_step])
    @test_throws DimensionMismatch Certificates.certify_leapfrog_vector_step(
        leapfrog_parameters;
        signed_step=0.1,
        computed_position=[0.0], ideal_position=BigFloat[0, 0],
        computed_momentum=[1.0], ideal_momentum=BigFloat[1],
        computed_current_gradient=[0.0], ideal_current_gradient=BigFloat[0],
        computed_half_momentum=[1.0], computed_next_position=[0.1],
        computed_next_gradient=[-0.1], ideal_next_gradient=BigFloat[-0.1],
        computed_next_momentum=[0.995], position_error=0, momentum_error=0)
    @test_throws ArgumentError Certificates.certify_leapfrog_coordinate_step(
        leapfrog_parameters;
        signed_step=0.2,
        computed_position=0.0, ideal_position=0.0,
        computed_momentum=1.0, ideal_momentum=1.0,
        computed_current_gradient=0.0, ideal_current_gradient=0.0,
        computed_half_momentum=1.0, computed_next_position=0.2,
        computed_next_gradient=-0.2, ideal_next_gradient=-0.2,
        computed_next_momentum=0.98,
        position_error=0, momentum_error=0)

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
    @test Reference.IR_FORMAT_VERSION == 23
    facets = Reference.artifact_facets()
    @test facets.programs ==
        ["approximate_classical_rmhmc_step!", "categorical_index!", "certified_relativistic_multinomial_hmc_step!",
        "classical_rmhmc_step!", "coupled_gaussian_rwmh_step!",
        "coupled_multinomial_hmc_step!", "dense_hmc_step!", "dense_multinomial_hmc_step!",
        "dense_rmhmc_step!",
        "diagonal_hmc_step!", "diagonal_multinomial_hmc_step!",
        "finite_mh_step!", "gaussian_rwmh_step!", "multinomial_hmc_step!",
        "random_sketch_rmhmc_step!", "relativistic_multinomial_hmc_step!",
        "scalar_hmc_step!", "vector_hmc_step!", "xu21_coupled_step!"]
    @test facets.targets == ["restricted-gaussian-potential",
        "restricted-quartic-potential", "restricted-sinusoidal-potential"]
    @test facets.schedules == ["ge-pg-hmc"]
    @test facets.transforms == ["open-unit-artanh", "positive-log"]
    @test facets.dynamic_trees == ["checked-recursive-doubling"]
    @test facets.nuts_tree_programs == ["checked-nuts-reference"]
    empty!(facets.programs)
    @test !isempty(Reference.artifact_facets().programs)
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
    @test dynamic.trace_policy == "fair-direction-bits"
    @test dynamic.root_encoding == "lsb-first-grow-right-zero"
    @test dynamic.stop_rule == "endpoint-uturn"
    @test dynamic.subtree_policy == "recursive-exclusion"
    @test dynamic.selection_policy == "eligible-count-streaming"
    @test dynamic.failure_policy == "checked-or-identity"
    @test collect(keys(Reference.NUTS_TREE_PROGRAMS)) ==
        ["checked-nuts-reference"]
    nuts = Reference.NUTS_TREE_PROGRAMS["checked-nuts-reference"]
    @test nuts.max_depth == 10
    @test nuts.selection == "multinomial"
    @test nuts.termination == "generalized"
    @test nuts.failure_policy == "checked-or-identity"
    @test nuts.recursion == "online-early-exit"
    @test nuts.candidates == "ordered-candidate-occurrences"
    @test_throws ArgumentError generated_dynamic_tree(
        "missing", [0.0], [1.0], Bool[])
    @test_throws ErrorException Reference.parse_document("(unterminated")
    unknown_input = Reference.parse_document(
        "(program \"bad\" (inputs (input mystery \"x\")) (body))")
    @test_throws ErrorException Reference.decode_program(
        Reference.aslist(unknown_input))
    duplicate_input = Reference.parse_document(
        "(program \"bad\" (inputs (input real \"x\") (input nat \"x\")) (body))")
    @test_throws ErrorException Reference.decode_program(
        Reference.aslist(duplicate_input))
    @test Reference.valid_input_value("nat-vector", BigInt[1, 2])
    @test Reference.valid_input_value("nat-matrix", [BigInt[1], BigInt[2]])
    @test !Reference.valid_input_value("unsupported", nothing)
    mktemp() do path, stream
        write(stream, "(verified-samplers-ir 2 bogus)\n")
        close(stream)
        @test_throws ErrorException Reference.load_programs(path)
    end
end
