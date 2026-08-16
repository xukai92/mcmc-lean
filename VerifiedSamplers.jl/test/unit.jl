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
    @test Reference.IR_FORMAT_VERSION == 14
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
    @test_throws ArgumentError generated_transform("missing")
    @test_throws ErrorException Reference.parse_document("(unterminated")
    mktemp() do path, stream
        write(stream, "(verified-samplers-ir 2 bogus)\n")
        close(stream)
        @test_throws ErrorException Reference.load_programs(path)
    end
end
