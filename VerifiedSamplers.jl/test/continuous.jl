# Executable continuous and mixed-state sampler tests.

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

@testset "Gaussian diagonal SoftAbs GR-HMC client" begin
    sampler = GaussianSoftAbsGRHMC(2, 0.08, 3)
    @test sampler.smoothing == 1.0
    @test all(>(1.0), sampler.sampler.metric.mass)
    first_chain = sample(MersenneTwister(431), sampler, [0.0, 0.0], 8)
    second_chain = sample(MersenneTwister(431), sampler, [0.0, 0.0], 8)
    @test first_chain == second_chain
    @test size(first_chain) == (2, 8)
    @test all(isfinite, first_chain)
    diagnostic_sampler = GaussianSoftAbsGRHMC(2, 0.2, 10)
    diagnostic = sample(MersenneTwister(0x6a55), diagnostic_sampler,
        [0.0, 0.0], 12_000)[:, 2001:end]
    @test maximum(abs, vec(mean(diagnostic; dims=2))) < 0.08
    @test maximum(abs.(vec(var(diagnostic; dims=2)) .- 1)) < 0.10
    @test_throws DimensionMismatch step(MersenneTwister(1), sampler, [0.0])
    @test_throws ArgumentError GaussianSoftAbsGRHMC(0, 0.1)
    @test_throws ArgumentError GaussianSoftAbsGRHMC(2, 0.1; smoothing=0.0)
end

@testset "guarded SoftAbs metric evaluation" begin
    exact_unit_zero = certify_unit_zero_softabs_float64()
    @test exact_unit_zero.evaluation ==
        SoftAbsMetricFloat64Evaluation(0.0, 1.0, 1.0, 1.0, 0.0)
    if isfile(ORACLE)
        arguments = unit_zero_softabs_certificate_arguments(exact_unit_zero)
        @test readchomp(`$ORACLE unit_zero_softabs $arguments`) == "ok"
        tampered = copy(arguments)
        tampered[end] = "1/1"
        @test readchomp(`$ORACLE unit_zero_softabs $tampered`) ==
            "error invalidUnitZeroSoftAbs"

        sqrt_certificate = Certificates.certify_sqrt_interval(0.5)
        sqrt_arguments =
            Certificates.sqrt_interval_certificate_arguments(sqrt_certificate)
        @test readchomp(`$ORACLE sqrt_interval $sqrt_arguments`) == "ok"
        tampered_sqrt = copy(sqrt_arguments)
        tampered_sqrt[end] = "0/1"
        @test readchomp(`$ORACLE sqrt_interval $tampered_sqrt`) ==
            "error invalidSqrtInterval"

        reciprocal_certificate = Certificates.certify_reciprocal_residual(
            sqrt_certificate.computed)
        reciprocal_arguments = Certificates.reciprocal_residual_certificate_arguments(
            reciprocal_certificate)
        @test readchomp(`$ORACLE reciprocal_residual $reciprocal_arguments`) == "ok"
        tampered_reciprocal = copy(reciprocal_arguments)
        tampered_reciprocal[end] = "0/1"
        @test readchomp(`$ORACLE reciprocal_residual $tampered_reciprocal`) ==
            "error invalidReciprocalResidual"

        composed_arguments = Certificates.sqrt_reciprocal_certificate_arguments(
            sqrt_certificate, reciprocal_certificate)
        @test readchomp(`$ORACLE sqrt_reciprocal $composed_arguments`) == "ok"
        tampered_composed = copy(composed_arguments)
        tampered_composed[end] = "0/1"
        @test readchomp(`$ORACLE sqrt_reciprocal $tampered_composed`) ==
            "error invalidSqrtReciprocal"
    end
    @test Certificates.certify_sqrt_interval(0.0).error == 0
    @test_throws DomainError Certificates.certify_sqrt_interval(-1.0)
    @test_throws DomainError Certificates.certify_sqrt_interval(Inf)
    @test_throws DomainError Certificates.certify_reciprocal_residual(0.0)
    @test_throws DomainError Certificates.certify_reciprocal_residual(Inf)
    zero_entry = evaluate_softabs_metric_float64(0.0; smoothing=2.0)
    @test zero_entry.eigenvalue == 0.5
    @test zero_entry.factor == inv(sqrt(0.5))
    @test zero_entry.logdet == log(0.5)

    entry = evaluate_softabs_metric_float64(1.0)
    @test entry.eigenvalue == 1 / tanh(1.0)
    @test entry.sqrt_eigenvalue^2 ≈ entry.eigenvalue
    @test entry.factor * entry.sqrt_eigenvalue ≈ 1.0
    log_certificate = Certificates.certify_log_interval(entry.eigenvalue)
    @test log_certificate.computed == entry.logdet
    @test log_certificate.error > 0
    if isfile(ORACLE)
        log_arguments =
            Certificates.log_interval_certificate_arguments(log_certificate)
        @test readchomp(`$ORACLE log_interval $log_arguments`) == "ok"
        tampered_log = copy(log_arguments)
        tampered_log[end] = "0/1"
        @test readchomp(`$ORACLE log_interval $tampered_log`) ==
            "error invalidLogInterval"
    end
    @test Certificates.certify_log_interval(1.0).error == 0
    @test_throws DomainError Certificates.certify_log_interval(0.0)
    @test_throws DomainError Certificates.certify_log_interval(Inf)
    exp_certificate = Certificates.certify_exp_nonpositive(-0.1)
    @test exp_certificate.computed == exp(-0.1)
    @test exp_certificate.error > 0
    @test Certificates.certify_exp_nonpositive(0.0).error == 0
    if isfile(ORACLE)
        exp_arguments = Certificates.exp_nonpositive_certificate_arguments(
            exp_certificate)
        @test readchomp(`$ORACLE exp_nonpositive $exp_arguments`) == "ok"
        tampered_exp = copy(exp_arguments)
        tampered_exp[end] = "0/1"
        @test readchomp(`$ORACLE exp_nonpositive $tampered_exp`) ==
            "error invalidExpNonpositive"
    end
    transported_exp = Certificates.certify_exp_nonpositive_transport(
        -0.1, -BigInt(1) // BigInt(10))
    @test transported_exp.input_error > 0
    if isfile(ORACLE)
        transported_arguments =
            Certificates.exp_nonpositive_transport_certificate_arguments(
                transported_exp)
        @test readchomp(`$ORACLE exp_nonpositive_transport $transported_arguments`) ==
            "ok"
        tampered_transport = copy(transported_arguments)
        tampered_transport[end] = "0/1"
        @test readchomp(`$ORACLE exp_nonpositive_transport $tampered_transport`) ==
            "error invalidExpNonpositiveTransport"
    end
    @test_throws DomainError Certificates.certify_exp_nonpositive(0.1)
    @test_throws DomainError Certificates.certify_exp_nonpositive(-Inf)
    softabs_certificate = Certificates.certify_positive_softabs(1.0, 1.0)
    @test softabs_certificate.computed_tanh == tanh(1.0)
    @test softabs_certificate.computed_eigenvalue == entry.eigenvalue
    @test softabs_certificate.tanh_error > 0
    if isfile(ORACLE)
        softabs_arguments = Certificates.positive_softabs_certificate_arguments(
            softabs_certificate)
        @test readchomp(`$ORACLE positive_softabs $softabs_arguments`) == "ok"
        tampered_softabs = copy(softabs_arguments)
        tampered_softabs[6] = "0/1"
        @test readchomp(`$ORACLE positive_softabs $tampered_softabs`) ==
            "error invalidPositiveSoftAbs"
    end
    metric_certificate = Certificates.certify_positive_softabs_metric(1.0, 1.0)
    @test metric_certificate.eigenvalue.computed_eigenvalue == entry.eigenvalue
    @test metric_certificate.sqrt.computed == entry.sqrt_eigenvalue
    @test metric_certificate.factor.computed == entry.factor
    @test metric_certificate.logdet.computed == entry.logdet
    if isfile(ORACLE)
        metric_arguments =
            Certificates.positive_softabs_metric_certificate_arguments(
                metric_certificate)
        @test readchomp(`$ORACLE positive_softabs_metric $metric_arguments`) == "ok"
        tampered_metric = copy(metric_arguments)
        tampered_metric[6] = "0/1"
        @test readchomp(`$ORACLE positive_softabs_metric $tampered_metric`) ==
            "error invalidPositiveSoftAbsMetric"
    end
    small_entry = evaluate_softabs_metric_float64(0.1)
    small_metric_certificate =
        Certificates.certify_positive_softabs_metric(1.0, 0.1)
    @test small_metric_certificate.eigenvalue.computed_eigenvalue ==
        small_entry.eigenvalue
    @test small_metric_certificate.sqrt.computed == small_entry.sqrt_eigenvalue
    @test small_metric_certificate.factor.computed == small_entry.factor
    @test small_metric_certificate.logdet.computed == small_entry.logdet
    if isfile(ORACLE)
        small_arguments =
            Certificates.positive_softabs_metric_certificate_arguments(
                small_metric_certificate)
        @test readchomp(`$ORACLE positive_softabs_metric $small_arguments`) == "ok"
    end
    rounded_argument_entry = evaluate_softabs_metric_float64(0.1;
        smoothing=0.1)
    rounded_argument_certificate =
        Certificates.certify_positive_softabs_metric(0.1, 0.1)
    @test rounded_argument_certificate.eigenvalue.argument_error > 0
    @test rounded_argument_certificate.eigenvalue.computed_eigenvalue ==
        rounded_argument_entry.eigenvalue
    @test rounded_argument_certificate.sqrt.computed ==
        rounded_argument_entry.sqrt_eigenvalue
    @test rounded_argument_certificate.factor.computed ==
        rounded_argument_entry.factor
    @test rounded_argument_certificate.logdet.computed ==
        rounded_argument_entry.logdet
    if isfile(ORACLE)
        rounded_arguments =
            Certificates.positive_softabs_metric_certificate_arguments(
                rounded_argument_certificate)
        @test readchomp(`$ORACLE positive_softabs_metric $rounded_arguments`) == "ok"
        tampered_argument = copy(rounded_arguments)
        tampered_argument[4] = "0/1"
        @test readchomp(`$ORACLE positive_softabs_metric $tampered_argument`) ==
            "error invalidPositiveSoftAbsMetric"
    end
    hamiltonian_evaluation = evaluate_softabs_scalar_hamiltonian_float64(
        0.5, 0.1, 0.25; smoothing=0.1)
    hamiltonian_certificate =
        Certificates.certify_positive_softabs_hamiltonian(
            0.1, 0.1, 0.5, 0.25)
    metric_error_upper =
        Certificates.certify_positive_softabs_metric_error_upper(
            hamiltonian_certificate.metric)
    @test metric_error_upper.factor_error > 0
    @test metric_error_upper.logdet_error > 0
    hamiltonian_error_upper =
        Certificates.certify_positive_softabs_hamiltonian_error_upper(
            hamiltonian_certificate)
    endpoint_solver_budget = Certificates.certify_rounded_contraction_pair(
        0, 0, 1 // big(10)^12, 0)
    endpoint_state_transport =
        Certificates.certify_positive_softabs_endpoint_state_transport(
            hamiltonian_error_upper, endpoint_solver_budget, 3 // 1)
    @test hamiltonian_error_upper.energy_error > 0
    @test endpoint_state_transport.total_energy_error ==
        hamiltonian_error_upper.energy_error + 3 // big(10)^12
    @test hamiltonian_certificate.kinetic.computed ==
        hamiltonian_evaluation.kinetic
    @test hamiltonian_certificate.computed_energy ==
        hamiltonian_evaluation.energy
    @test hamiltonian_certificate.kinetic_input_error > 0
    if isfile(ORACLE)
        hamiltonian_arguments =
            Certificates.positive_softabs_hamiltonian_certificate_arguments(
                hamiltonian_certificate)
        @test readchomp(`$ORACLE positive_softabs_hamiltonian $hamiltonian_arguments`) ==
            "ok"
        tampered_hamiltonian = copy(hamiltonian_arguments)
        tampered_hamiltonian[20] = "0/1"
        @test readchomp(`$ORACLE positive_softabs_hamiltonian $tampered_hamiltonian`) ==
            "error invalidPositiveSoftAbsHamiltonian"
        metric_upper_arguments =
            Certificates.positive_softabs_metric_error_upper_certificate_arguments(
                metric_error_upper)
        @test readchomp(`$ORACLE positive_softabs_metric_upper $metric_upper_arguments`) ==
            "ok"
        tampered_metric_upper = copy(metric_upper_arguments)
        tampered_metric_upper[end] = "0/1"
        @test readchomp(`$ORACLE positive_softabs_metric_upper $tampered_metric_upper`) ==
            "error invalidPositiveSoftAbsMetricUpper"
        hamiltonian_upper_arguments =
            Certificates.positive_softabs_hamiltonian_error_upper_certificate_arguments(
                hamiltonian_error_upper)
        @test readchomp(`$ORACLE positive_softabs_hamiltonian_upper $hamiltonian_upper_arguments`) ==
            "ok"
        tampered_hamiltonian_upper = copy(hamiltonian_upper_arguments)
        tampered_hamiltonian_upper[end] = "0/1"
        @test readchomp(`$ORACLE positive_softabs_hamiltonian_upper $tampered_hamiltonian_upper`) ==
            "error invalidPositiveSoftAbsHamiltonianUpper"
        state_transport_arguments =
            Certificates.positive_softabs_endpoint_state_transport_certificate_arguments(
                endpoint_state_transport)
        @test readchomp(`$ORACLE positive_softabs_endpoint_state_transport $state_transport_arguments`) ==
            "ok"
        tampered_state_transport = copy(state_transport_arguments)
        tampered_state_transport[end] = "0/1"
        @test readchomp(`$ORACLE positive_softabs_endpoint_state_transport $tampered_state_transport`) ==
            "error invalidPositiveSoftAbsEndpointStateTransport"
    end
    @test_throws DomainError Certificates.certify_positive_softabs_endpoint_state_transport(
        hamiltonian_error_upper, -1, 3)
    hamiltonian_trajectory =
        Certificates.certify_positive_softabs_hamiltonian_trajectory(
            0.1, [0.1, 0.2, 0.3], [0.5, 10.6, 100.7], [0.25, -0.5, 0.75])
    @test length(hamiltonian_trajectory.endpoints) == 3
    @test all(isfinite, [endpoint.computed_energy
        for endpoint in hamiltonian_trajectory.endpoints])
    trajectory_error_uppers =
        Certificates.certify_positive_softabs_hamiltonian_error_upper.(
            hamiltonian_trajectory.endpoints)
    @test all(upper -> upper.energy_error > 0, trajectory_error_uppers)
    if isfile(ORACLE)
        trajectory_arguments =
            Certificates.positive_softabs_hamiltonian_trajectory_certificate_arguments(
                hamiltonian_trajectory)
        @test readchomp(`$ORACLE positive_softabs_hamiltonian_trajectory $trajectory_arguments`) ==
            "ok"
        tampered_trajectory = copy(trajectory_arguments)
        tampered_trajectory[21] = "0/1"
        @test readchomp(`$ORACLE positive_softabs_hamiltonian_trajectory $tampered_trajectory`) ==
            "error invalidPositiveSoftAbsHamiltonianTrajectory"
        truncated_trajectory = trajectory_arguments[1:end-1]
        @test readchomp(`$ORACLE positive_softabs_hamiltonian_trajectory $truncated_trajectory`) ==
            "error invalidPositiveSoftAbsHamiltonianTrajectoryFieldCount"
    end
    stabilized_weights =
        Certificates.certify_positive_softabs_stabilized_weights(
            hamiltonian_trajectory)
    @test length(stabilized_weights.weights) == 3
    @test all(weight -> 0 < weight.local_certificate.computed <= 1,
        stabilized_weights.weights)
    @test any(weight.input_error > 0 for weight in stabilized_weights.weights)
    if isfile(ORACLE)
        weight_arguments =
            Certificates.positive_softabs_stabilized_weight_certificate_arguments(
                stabilized_weights)
        @test readchomp(`$ORACLE exp_nonpositive_transport_trajectory $weight_arguments`) ==
            "ok"
        tampered_weights = copy(weight_arguments)
        nonzero_index = findfirst(weight -> weight.input_error > 0,
            stabilized_weights.weights)
        @test nonzero_index !== nothing
        tampered_weights[5 * nonzero_index + 1] = "0/1"
        @test readchomp(`$ORACLE exp_nonpositive_transport_trajectory $tampered_weights`) ==
            "error invalidExpNonpositiveTransportTrajectory"
        truncated_weights = weight_arguments[1:end-1]
        @test readchomp(`$ORACLE exp_nonpositive_transport_trajectory $truncated_weights`) ==
            "error invalidExpNonpositiveTransportTrajectoryFieldCount"
    end
    cumulative_weights = Certificates.certify_rounded_cumulative(
        [weight.local_certificate.computed for weight in stabilized_weights.weights])
    @test isfinite(cumulative_weights.boundaries[end])
    @test any(>(0), cumulative_weights.errors)
    if isfile(ORACLE)
        cumulative_arguments =
            Certificates.rounded_cumulative_certificate_arguments(cumulative_weights)
        @test readchomp(`$ORACLE rounded_cumulative $cumulative_arguments`) == "ok"
        tampered_cumulative = copy(cumulative_arguments)
        nonzero_cumulative = findfirst(>(0), cumulative_weights.errors)
        @test nonzero_cumulative !== nothing
        tampered_cumulative[3 * nonzero_cumulative + 1] = "0/1"
        @test readchomp(`$ORACLE rounded_cumulative $tampered_cumulative`) ==
            "error invalidRoundedCumulative"
        truncated_cumulative = cumulative_arguments[1:end-1]
        @test readchomp(`$ORACLE rounded_cumulative $truncated_cumulative`) ==
            "error invalidRoundedCumulativeFieldCount"
    end
    scaled_draw = Certificates.certify_scaled_draw(
        0.37, cumulative_weights.boundaries[end])
    @test scaled_draw.computed == 0.37 * cumulative_weights.boundaries[end]
    @test scaled_draw.error > 0
    if isfile(ORACLE)
        draw_arguments = Certificates.scaled_draw_certificate_arguments(scaled_draw)
        @test readchomp(`$ORACLE scaled_draw $draw_arguments`) == "ok"
        tampered_draw = copy(draw_arguments)
        tampered_draw[end] = "0/1"
        @test readchomp(`$ORACLE scaled_draw $tampered_draw`) ==
            "error invalidScaledDraw"
    end
    selection_error_upper =
        Certificates.certify_positive_softabs_selection_error_upper(
            trajectory_error_uppers, stabilized_weights, cumulative_weights,
            scaled_draw)
    @test selection_error_upper.common_energy_error ==
        maximum(upper.energy_error for upper in trajectory_error_uppers)
    @test selection_error_upper.boundary_error > 0
    @test selection_error_upper.uniform_error > 0
    decision_margin = selection_error_upper.decision
    @test decision_margin.computed_draw == scaled_draw.computed
    if isfile(ORACLE)
        decision_arguments =
            Certificates.multinomial_decision_certificate_arguments(decision_margin)
        @test readchomp(`$ORACLE multinomial_decision $decision_arguments`) == "ok"
        touching_decision = copy(decision_arguments)
        touching_decision[5] = touching_decision[1]
        @test readchomp(`$ORACLE multinomial_decision $touching_decision`) ==
            "error invalidMultinomialDecision"
        truncated_decision = decision_arguments[1:end-1]
        @test readchomp(`$ORACLE multinomial_decision $truncated_decision`) ==
            "error invalidMultinomialDecisionFieldCount"
    end
    @test_throws ArgumentError Certificates.certify_multinomial_decision(
        scaled_draw.computed, [scaled_draw.computed], 0, 0)
    @test_throws DomainError Certificates.certify_positive_softabs(1.0, 0.0)
    @test_throws DomainError evaluate_softabs_metric_float64(Inf)
    @test_throws DomainError evaluate_softabs_metric_float64(1.0; smoothing=0.0)

    diagonal = evaluate_softabs_diagonal_float64([0.0, 1.0, -0.5];
        smoothing=2.0)
    @test diagonal.factors == [entry.factor for entry in diagonal.entries]
    @test diagonal.logdet == sum(entry.logdet for entry in diagonal.entries)
    @test all(>(0), [entry.eigenvalue for entry in diagonal.entries])
    @test_throws ArgumentError evaluate_softabs_diagonal_float64(Float64[])

    scalar_h = evaluate_softabs_scalar_hamiltonian_float64(0.25, 0.0, 2.0)
    @test scalar_h.metric.eigenvalue == 1.0
    @test scalar_h.transformed_momentum == 2.0
    @test scalar_h.kinetic == sqrt(5.0)
    @test scalar_h.energy == 0.25 + sqrt(5.0)
    @test_throws DomainError evaluate_softabs_scalar_hamiltonian_float64(
        Inf, 0.0, 1.0)
end

@testset "restricted target expressions" begin
    for x in (-3.0, -0.25, 0.0, 1.5)
        value, derivative = restricted_value_gradient(
            restricted_gaussian_potential, x)
        @test value == x^2 / 2
        @test derivative == x
    end

    exponential = RestrictedExp(RestrictedNeg(RestrictedInput()))
    value, derivative = restricted_value_gradient(exponential, 0.7)
    @test value == exp(-0.7)
    @test derivative == -exp(-0.7)
    @test_throws DomainError restricted_value_gradient(
        RestrictedExp(RestrictedConst(1000.0)), 0.0)

    for x in (-2.0, -0.25, 0.0, 1.75)
        value, derivative, hessian = restricted_value_gradient_hessian(
            restricted_sinusoidal_potential, x)
        @test value ≈ x^2 / 2 - sin(x)
        @test derivative ≈ x - cos(x)
        @test hessian ≈ 1 + sin(x)
        metric = evaluate_softabs_metric_float64(hessian)
        @test metric.eigenvalue > 0
    end

    quartic_exact = certify_restricted_quartic_float64(0.5)
    @test quartic_exact.ideal_value == 9 // 64
    @test quartic_exact.ideal_derivative == 5 // 8
    @test quartic_exact.ideal_second_derivative == 7 // 4
    @test all(iszero, (quartic_exact.value_error,
        quartic_exact.derivative_error,
        quartic_exact.second_derivative_error))

    quartic_rounded = certify_restricted_quartic_float64(0.1)
    quartic_arguments =
        restricted_quartic_certificate_arguments(quartic_rounded)
    @test length(quartic_arguments) == 7
    if isfile(ORACLE)
        @test readchomp(`$ORACLE quartic_certificate $quartic_arguments`) == "ok"
        invalid = copy(quartic_arguments)
        invalid[end] = "0/1"
        if quartic_arguments[end] == "0/1"
            invalid[end] = "1/1"
        end
        @test readchomp(`$ORACLE quartic_certificate $invalid`) ==
            "error invalidCertificate"
    end
    @test_throws ArgumentError certify_restricted_quartic_float64(Inf)

    for x in (-2.0, -0.25, 0.0, 1.75)
        value, derivative, hessian = restricted_value_gradient_hessian(
            restricted_quartic_potential, x)
        @test value == x^4 / 4 + x^2 / 2
        @test derivative == x^3 + x
        @test hessian == 3x^2 + 1
        @test hessian >= 1
        metric = evaluate_softabs_metric_float64(hessian)
        @test metric.eigenvalue > 0
    end

    quartic_sampler = restricted_potential_rwmh(
        restricted_quartic_potential, 0.8)
    quartic_first = sample(MersenneTwister(0x71a4), quartic_sampler, 0.0, 100)
    quartic_second = sample(MersenneTwister(0x71a4), quartic_sampler, 0.0, 100)
    @test quartic_first == quartic_second
    @test all(isfinite, quartic_first)
    @test any(!iszero, quartic_first)

    quartic_hmc = restricted_potential_hmc(
        restricted_quartic_potential, 0.15, 6)
    quartic_hmc_first = sample(
        MersenneTwister(0x71a5), quartic_hmc, 0.0, 100)
    quartic_hmc_second = sample(
        MersenneTwister(0x71a5), quartic_hmc, 0.0, 100)
    @test quartic_hmc_first == quartic_hmc_second
    @test all(isfinite, quartic_hmc_first)
    @test any(!iszero, quartic_hmc_first)

    # Every generated restricted target, rather than only the quartic
    # certificate client, is wired through both maintained sampler adapters.
    for (offset, potential) in enumerate((restricted_gaussian_potential,
            restricted_sinusoidal_potential))
        rwmh = restricted_potential_rwmh(potential, 0.7)
        rwmh_first = sample(MersenneTwister(0x71b0 + offset), rwmh, 0.0, 100)
        rwmh_second = sample(MersenneTwister(0x71b0 + offset), rwmh, 0.0, 100)
        @test rwmh_first == rwmh_second
        @test all(isfinite, rwmh_first)
        @test any(!iszero, rwmh_first)

        hmc = restricted_potential_hmc(potential, 0.12, 5)
        hmc_first = sample(MersenneTwister(0x71c0 + offset), hmc, 0.0, 100)
        hmc_second = sample(MersenneTwister(0x71c0 + offset), hmc, 0.0, 100)
        @test hmc_first == hmc_second
        @test all(isfinite, hmc_first)
        @test any(!iszero, hmc_first)
    end

    exact = certify_restricted_gaussian_float64(0.5)
    @test exact.ideal_value == 1 // 8
    @test iszero(exact.value_error)
    @test iszero(exact.derivative_error)
    @test exact.ideal_second_derivative == 1
    @test iszero(exact.second_derivative_error)

    rounded = certify_restricted_gaussian_float64(0.1)
    x = Rational{BigInt}(0.1)
    @test rounded.ideal_value == x^2 / 2
    @test rounded.ideal_derivative == x
    @test rounded.ideal_second_derivative == 1
    @test rounded.value_error ==
        abs(Rational{BigInt}(rounded.computed_value) - x^2 / 2)
    @test iszero(rounded.derivative_error)
    @test rounded.second_derivative_error ==
        abs(Rational{BigInt}(rounded.computed_second_derivative) - 1)
    arguments = restricted_gaussian_certificate_arguments(rounded)
    @test length(arguments) == 7
    if isfile(ORACLE)
        @test readchomp(`$ORACLE gaussian_certificate $arguments`) == "ok"
        invalid = copy(arguments)
        invalid[end] = "1/1"
        @test readchomp(`$ORACLE gaussian_certificate $invalid`) ==
            "error invalidCertificate"
    end
    @test_throws ArgumentError certify_restricted_gaussian_float64(Inf)
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
    traced = Reference.fixed_point_generalized_leapfrog_trace(
        position_derivative, momentum_derivative, q, p, ε;
        max_iterations=200, atol=1e-13, rtol=1e-13)
    optimized = Optimized.fixed_point_generalized_leapfrog(
        position_derivative, momentum_derivative, q, p, ε;
        max_iterations=200, atol=1e-13, rtol=1e-13)
    @test reference[1] ≈ optimized[1] atol=1e-14 rtol=0
    @test reference[2] ≈ optimized[2] atol=1e-14 rtol=0
    @test traced[1] == reference[1]
    @test traced[2] == reference[2]
    @test traced[3].half_momentum_residual.computed ==
        reference[3].half_momentum_residual.computed
    @test traced[3].position_residual.computed ==
        reference[3].position_residual.computed
    @test norm(traced[4].half_momentum - traced[4].half_update) ==
        reference[3].half_momentum_residual.computed
    @test traced[4].half_callback ==
        Float64.(position_derivative(q, traced[4].half_momentum))
    @test norm(traced[4].next_position - traced[4].position_update) ==
        reference[3].position_residual.computed
    @test traced[4].position_callback ==
        Float64.(momentum_derivative(q, traced[4].half_momentum)) +
        Float64.(momentum_derivative(
            traced[4].next_position, traced[4].half_momentum))
    @test 1 <= traced[4].half_iterations <= 200
    @test 1 <= traced[4].position_iterations <= 200
    @test reference[3].half_momentum_residual.computed < 1e-12
    @test reference[3].position_residual.computed < 1e-12
    @test !Certificates.certifies_exact_solver(reference[3])
    half_error = Certificates.contraction_error_bound(
        reference[3].half_momentum_residual.computed, 1e-15, 0.2)
    @test half_error.distance_bound ==
        (abs(BigFloat(reference[3].half_momentum_residual.computed)) +
          half_error.residual_error) / (1 - half_error.rate)
    rational_half_error = Certificates.certify_contraction_aposteriori(
        Rational{BigInt}(reference[3].half_momentum_residual.computed) +
            1 // big(10)^15,
        1 // 5)
    @test rational_half_error.distance_upper ==
        rational_half_error.residual_upper / (1 - rational_half_error.rate)
    if isfile(ORACLE)
        arguments = Certificates.contraction_aposteriori_certificate_arguments(
            rational_half_error)
        @test readchomp(`$ORACLE contraction_aposteriori $arguments`) == "ok"
        tampered = copy(arguments)
        tampered[end] = "0/1"
        @test readchomp(`$ORACLE contraction_aposteriori $tampered`) ==
            "error invalidContractionAposteriori"
    end
    half_affine = Certificates.certify_rounded_affine_update(
        p[1], -(ε / 2), traced[4].half_callback[1], 1 // big(10)^15,
        traced[4].half_update[1])
    position_affine = Certificates.certify_rounded_affine_update(
        q[1], ε / 2, traced[4].position_callback[1], 2 // big(10)^15,
        traced[4].position_update[1])
    @test half_affine.update_error == half_affine.arithmetic_error +
        abs(half_affine.scale) * half_affine.callback_error
    @test position_affine.update_error == position_affine.arithmetic_error +
        abs(position_affine.scale) * position_affine.callback_error
    rounded_pair = Certificates.certify_rounded_contraction_pair(
        traced[4].half_momentum[1], traced[4].half_update[1],
        half_affine.update_error, 1 // 5)
    @test rounded_pair.contraction.residual_upper ==
        rounded_pair.residual.residual_upper
    @test rounded_pair.residual.residual_upper ==
        abs(rounded_pair.residual.iterate -
            rounded_pair.residual.computed_update) +
            rounded_pair.residual.update_error
    if isfile(ORACLE)
        affine_arguments =
            Certificates.rounded_affine_update_certificate_arguments(half_affine)
        @test readchomp(`$ORACLE rounded_affine_update $affine_arguments`) == "ok"
        tampered_affine = copy(affine_arguments)
        tampered_affine[end] = "0/1"
        @test readchomp(`$ORACLE rounded_affine_update $tampered_affine`) ==
            "error invalidRoundedAffineUpdate"
        position_affine_arguments =
            Certificates.rounded_affine_update_certificate_arguments(
                position_affine)
        @test readchomp(`$ORACLE rounded_affine_update $position_affine_arguments`) ==
            "ok"
        arguments = Certificates.rounded_contraction_pair_certificate_arguments(
            rounded_pair)
        @test readchomp(`$ORACLE rounded_contraction_pair $arguments`) == "ok"
        tampered = copy(arguments)
        tampered[4] = "0/1"
        @test readchomp(`$ORACLE rounded_contraction_pair $tampered`) ==
            "error invalidRoundedContractionPair"
    end
    @test_throws DomainError Certificates.contraction_error_bound(1e-8, 0, 1)
    @test_throws DomainError Certificates.contraction_error_bound(1e-8, -1, 0.2)
    @test_throws DomainError Certificates.certify_contraction_aposteriori(
        -1 // 10, 1 // 5)
    @test_throws DomainError Certificates.certify_contraction_aposteriori(
        1 // 10, 1)
    @test_throws DomainError Certificates.certify_rounded_contraction_residual(
        0, 0, -1 // 10)
    @test_throws DomainError Certificates.certify_rounded_affine_update(
        0, 1, 0, -1 // 10, 0)

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

    # Complete GR Hamiltonian with bounded nonconstant factor s(q)=2+sin(q)
    # and compensating potential log(s): H(q,p)=sqrt(1+(s(q)*p)^2).
    bounded_position_derivative(q, p) = begin
        s = 2 + sin(q[1])
        [s * cos(q[1]) * p[1]^2 / sqrt(1 + (s * p[1])^2)]
    end
    bounded_momentum_derivative(q, p) = begin
        s = 2 + sin(q[1])
        [s^2 * p[1] / sqrt(1 + (s * p[1])^2)]
    end
    qb, pb, εb = [0.25], [-0.35], 0.15
    bounded_sincos = Certificates.certify_sincos_interval(qb[1])
    @test bounded_sincos.sin_error > 0
    @test bounded_sincos.cos_error > 0
    if isfile(ORACLE)
        arguments = Certificates.sincos_interval_certificate_arguments(
            bounded_sincos)
        @test readchomp(`$ORACLE sincos_interval $arguments`) == "ok"
        tampered = copy(arguments)
        tampered[3] = "0/1"
        @test readchomp(`$ORACLE sincos_interval $tampered`) ==
            "error invalidSinCosInterval"
    end
    @test_throws DomainError Certificates.certify_sincos_interval(1.1)
    bounded_callbacks = Certificates.certify_bounded_scalar_callbacks(
        qb[1], pb[1])
    @test bounded_callbacks.computed_momentum_callback ≈
        bounded_momentum_derivative(qb, pb)[1] rtol=2eps() atol=0
    @test bounded_callbacks.computed_position_callback ≈
        bounded_position_derivative(qb, pb)[1] rtol=2eps() atol=0
    @test bounded_callbacks.computed_sqrt_lower > 1
    if isfile(ORACLE)
        arguments = Certificates.bounded_scalar_callback_certificate_arguments(
            bounded_callbacks)
        @test readchomp(`$ORACLE bounded_scalar_callbacks $arguments`) == "ok"
        tampered_radicand = copy(arguments)
        tampered_radicand[8] = "0/1"
        @test readchomp(`$ORACLE bounded_scalar_callbacks $tampered_radicand`) ==
            "error invalidBoundedScalarCallbacks"
        tampered_callback = copy(arguments)
        tampered_callback[17] = "0/1"
        @test readchomp(`$ORACLE bounded_scalar_callbacks $tampered_callback`) ==
            "error invalidBoundedScalarCallbacks"
    end
    @test_throws DomainError Certificates.certify_bounded_scalar_callbacks(
        qb[1], Inf)
    bounded_reference = Reference.fixed_point_generalized_leapfrog_trace(
        bounded_position_derivative, bounded_momentum_derivative,
        qb, -pb, εb; max_iterations=300, atol=1e-14, rtol=1e-14)
    bounded_optimized = Optimized.fixed_point_generalized_leapfrog(
        bounded_position_derivative, bounded_momentum_derivative,
        qb, -pb, εb; max_iterations=300, atol=1e-14, rtol=1e-14)
    bounded_backward = Reference.fixed_point_generalized_leapfrog(
        bounded_position_derivative, bounded_momentum_derivative,
        qb, pb, -εb; max_iterations=300, atol=1e-14, rtol=1e-14)
    @test bounded_reference[1] ≈ bounded_optimized[1] atol=2e-14 rtol=0
    @test bounded_reference[2] ≈ bounded_optimized[2] atol=2e-14 rtol=0
    @test bounded_reference[1] ≈ bounded_backward[1] atol=2e-13 rtol=0
    @test -bounded_reference[2] ≈ bounded_backward[2] atol=2e-13 rtol=0
    @test bounded_reference[3].half_momentum_residual.computed < 1e-13
    @test bounded_reference[3].position_residual.computed < 1e-13
    bounded_trace_certificate =
        Certificates.certify_bounded_scalar_callback_trace(bounded_reference[4])
    @test length(bounded_trace_certificate.certificates) ==
        bounded_reference[4].half_iterations +
        bounded_reference[4].position_iterations + 4
    @test count(==(:position), bounded_trace_certificate.kinds) ==
        bounded_reference[4].half_iterations + 2
    @test count(==(:momentum), bounded_trace_certificate.kinds) ==
        bounded_reference[4].position_iterations + 2
    if isfile(ORACLE)
        arguments =
            Certificates.bounded_scalar_callback_trace_certificate_arguments(
                bounded_trace_certificate)
        @test readchomp(`$ORACLE bounded_scalar_callback_trace $arguments`) == "ok"
        tampered_count = copy(arguments)
        tampered_count[1] = string(parse(Int, tampered_count[1]) + 1)
        @test readchomp(`$ORACLE bounded_scalar_callback_trace $tampered_count`) ==
            "error invalidBoundedScalarCallbackTraceCount"
        tampered_entry = copy(arguments)
        tampered_entry[12] = "0/1"
        @test readchomp(`$ORACLE bounded_scalar_callback_trace $tampered_entry`) ==
            "error invalidBoundedScalarCallbackTrace"
        tampered_order = copy(arguments)
        tampered_order[4] = "momentum"
        @test readchomp(`$ORACLE bounded_scalar_callback_trace $tampered_order`) ==
            "error invalidBoundedScalarCallbackTrace"
    end
    bounded_affine_certificate =
        Certificates.certify_bounded_scalar_affine_trace(
            bounded_reference[4], bounded_trace_certificate)
    bounded_second_reference = Reference.fixed_point_generalized_leapfrog_trace(
        bounded_position_derivative, bounded_momentum_derivative,
        bounded_reference[1], bounded_reference[2], εb;
        max_iterations=300, atol=1e-14, rtol=1e-14)
    bounded_second_trace_certificate =
        Certificates.certify_bounded_scalar_callback_trace(
            bounded_second_reference[4])
    bounded_second_affine_certificate =
        Certificates.certify_bounded_scalar_affine_trace(
            bounded_second_reference[4], bounded_second_trace_certificate)
    bounded_linked_trajectory =
        Certificates.certify_bounded_scalar_linked_solver_trajectory(
            qb[1], -pb[1], [bounded_reference[4], bounded_second_reference[4]],
            [bounded_trace_certificate, bounded_second_trace_certificate],
            [bounded_affine_certificate, bounded_second_affine_certificate], εb)
    @test length(bounded_linked_trajectory.steps) == 2
    bounded_half_region = maximum(
        abs(Rational{BigInt}(trace.half_momentum[1])) +
          step.phase.solver.half.contraction.distance_upper
        for (trace, step) in zip(
            [bounded_reference[4], bounded_second_reference[4]],
            bounded_linked_trajectory.steps))
    bounded_regional = Certificates.certify_bounded_scalar_step_regional(
        εb, bounded_half_region)
    @test bounded_regional.lipschitz_upper >=
        bounded_regional.position_coefficient
    @test bounded_regional.lipschitz_upper >=
        bounded_regional.momentum_coefficient
    @test_throws ArgumentError Certificates.certify_bounded_scalar_linked_solver_trajectory(
            qb[1] + 1, -pb[1],
            [bounded_reference[4], bounded_second_reference[4]],
            [bounded_trace_certificate, bounded_second_trace_certificate],
            [bounded_affine_certificate, bounded_second_affine_certificate], εb)
    @test length(bounded_affine_certificate.updates) ==
        bounded_reference[4].half_iterations +
        bounded_reference[4].position_iterations + 3
    @test count(==(:half_momentum), bounded_affine_certificate.kinds) ==
        bounded_reference[4].half_iterations + 1
    @test count(==(:position), bounded_affine_certificate.kinds) ==
        bounded_reference[4].position_iterations + 1
    @test bounded_affine_certificate.kinds[end] == :final_momentum
    @test all(update -> update.callback_error > 0,
        bounded_affine_certificate.updates)
    @test any(!iszero,
        bounded_affine_certificate.callback_arithmetic_errors)
    bounded_solver_contraction =
        Certificates.certify_bounded_scalar_solver_contraction_trace(
            bounded_reference[4], bounded_affine_certificate, εb)
    @test bounded_solver_contraction.half.contraction.rate ==
        abs(Rational{BigInt}(εb) / 2) * 3
    @test bounded_solver_contraction.position.contraction.rate ==
        abs(Rational{BigInt}(εb) / 2) * 2
    @test bounded_solver_contraction.half.contraction.distance_upper > 0
    @test bounded_solver_contraction.position.contraction.distance_upper > 0
    bounded_solver_phase =
        Certificates.certify_bounded_scalar_solver_phase_trace(
            bounded_reference[4], bounded_trace_certificate,
            bounded_affine_certificate, εb)
    @test bounded_solver_phase.position_error >
        bounded_solver_contraction.position.contraction.distance_upper
    bounded_solver_endpoint =
        Certificates.certify_bounded_scalar_solver_endpoint_trace(
            bounded_reference[4], bounded_trace_certificate,
            bounded_affine_certificate, εb)
    @test bounded_solver_endpoint.final_momentum_error >
        bounded_affine_certificate.updates[end].update_error
    @test bounded_solver_endpoint.phase_error == max(
        bounded_solver_phase.position_error,
        bounded_solver_endpoint.final_momentum_error)
    bounded_endpoint_energy =
        Certificates.certify_bounded_scalar_endpoint_energy_trace(
            bounded_reference[4], bounded_trace_certificate,
            bounded_affine_certificate, εb)
    @test bounded_endpoint_energy.evaluation.sqrt_certificate.computed ≈
        sqrt(1 + ((2 + sin(bounded_reference[1][1])) *
          bounded_reference[2][1])^2) rtol=0 atol=0
    @test bounded_endpoint_energy.total_energy_error >
        bounded_endpoint_energy.evaluation.sqrt_certificate.error
    bounded_two_endpoint_energy =
        Certificates.certify_bounded_scalar_two_endpoint_energy_trace(
            bounded_reference[4], bounded_trace_certificate,
            bounded_affine_certificate, εb)
    @test bounded_two_endpoint_energy.initial.sincos.input == qb[1]
    @test bounded_two_endpoint_energy.initial.momentum == -pb[1]
    @test bounded_two_endpoint_energy.common_error == max(
        Certificates._bounded_scalar_sqrt_error(
            bounded_two_endpoint_energy.initial),
        bounded_endpoint_energy.total_energy_error)
    bounded_two_endpoint_selection =
        Certificates.certify_bounded_scalar_two_endpoint_selection(
            bounded_two_endpoint_energy, 0.37)
    @test length(bounded_two_endpoint_selection.weights.weights) == 2
    @test bounded_two_endpoint_selection.boundary_error > 0
    @test bounded_two_endpoint_selection.uniform_error > 0
    @test Certificates.is_stable(
        bounded_two_endpoint_selection.decision)
    if isfile(ORACLE)
        for index in eachindex(bounded_affine_certificate.updates)
            arguments =
                Certificates.bounded_scalar_affine_update_certificate_arguments(
                    bounded_trace_certificate, bounded_affine_certificate, index)
            @test readchomp(`$ORACLE bounded_scalar_affine_update $arguments`) ==
                "ok"
        end
        tampered_update =
            Certificates.bounded_scalar_affine_update_certificate_arguments(
                bounded_trace_certificate, bounded_affine_certificate, 1)
        tampered_update[end - 3] = "0/1"
        @test readchomp(`$ORACLE bounded_scalar_affine_update $tampered_update`) ==
            "error invalidBoundedScalarAffineUpdate"
        for kind in (:half_momentum, :position)
            arguments = Certificates.
                bounded_scalar_solver_contraction_certificate_arguments(
                    bounded_trace_certificate, bounded_affine_certificate,
                    bounded_solver_contraction, kind)
            @test readchomp(
                `$ORACLE bounded_scalar_solver_contraction $arguments`) == "ok"
            tampered_rate = copy(arguments)
            tampered_rate[end - 1] = "0/1"
            @test readchomp(
                `$ORACLE bounded_scalar_solver_contraction $tampered_rate`) ==
                "error invalidBoundedScalarSolverContraction"
        end
        phase_arguments = Certificates.
            bounded_scalar_solver_phase_certificate_arguments(
                bounded_trace_certificate, bounded_affine_certificate,
                bounded_solver_phase)
        @test readchomp(`$ORACLE bounded_scalar_solver_phase $phase_arguments`) ==
            "ok"
        tampered_phase_error = copy(phase_arguments)
        tampered_phase_error[end] = "0/1"
        @test readchomp(
            `$ORACLE bounded_scalar_solver_phase $tampered_phase_error`) ==
            "error invalidBoundedScalarSolverPhase"
        endpoint_arguments = Certificates.
            bounded_scalar_solver_endpoint_certificate_arguments(
                bounded_trace_certificate, bounded_affine_certificate,
                bounded_solver_endpoint)
        @test readchomp(
            `$ORACLE bounded_scalar_solver_endpoint $endpoint_arguments`) == "ok"
        tampered_endpoint_error = copy(endpoint_arguments)
        tampered_endpoint_error[end - 1] = "0/1"
        @test readchomp(
            `$ORACLE bounded_scalar_solver_endpoint $tampered_endpoint_error`) ==
            "error invalidBoundedScalarSolverEndpoint"
        linked_arguments = Certificates.
            bounded_scalar_linked_solver_trajectory_certificate_arguments(
                [bounded_trace_certificate, bounded_second_trace_certificate],
                [bounded_affine_certificate,
                    bounded_second_affine_certificate],
                bounded_linked_trajectory)
        @test readchomp(
            `$ORACLE bounded_scalar_linked_solver_trajectory $linked_arguments`) ==
            "ok"
        tampered_linked_initial = copy(linked_arguments)
        tampered_linked_initial[2] = "0/1"
        @test readchomp(
            `$ORACLE bounded_scalar_linked_solver_trajectory $tampered_linked_initial`) ==
            "error invalidBoundedScalarLinkedSolverTrajectory"
        truncated_linked = linked_arguments[1:end-1]
        @test readchomp(
            `$ORACLE bounded_scalar_linked_solver_trajectory $truncated_linked`) ==
            "error invalidBoundedScalarLinkedSolverTrajectoryFieldCount"
        regional_arguments = Certificates.
            bounded_scalar_step_regional_certificate_arguments(bounded_regional)
        @test readchomp(
            `$ORACLE bounded_scalar_step_regional $regional_arguments`) == "ok"
        tampered_regional = copy(regional_arguments)
        tampered_regional[end] = "0/1"
        @test readchomp(
            `$ORACLE bounded_scalar_step_regional $tampered_regional`) ==
            "error invalidBoundedScalarStepRegional"
        energy_arguments = Certificates.
            bounded_scalar_endpoint_energy_certificate_arguments(
                bounded_trace_certificate, bounded_affine_certificate,
                bounded_endpoint_energy)
        @test readchomp(
            `$ORACLE bounded_scalar_endpoint_energy $energy_arguments`) == "ok"
        tampered_energy_error = copy(energy_arguments)
        tampered_energy_error[end] = "0/1"
        @test readchomp(
            `$ORACLE bounded_scalar_endpoint_energy $tampered_energy_error`) ==
            "error invalidBoundedScalarEndpointEnergy"
        two_endpoint_arguments = Certificates.
            bounded_scalar_two_endpoint_energy_certificate_arguments(
                bounded_trace_certificate, bounded_affine_certificate,
                bounded_two_endpoint_energy)
        @test readchomp(
            `$ORACLE bounded_scalar_two_endpoint_energy $two_endpoint_arguments`) ==
            "ok"
        tampered_initial_momentum = copy(two_endpoint_arguments)
        tampered_initial_momentum[6] = "0/1"
        @test readchomp(
            `$ORACLE bounded_scalar_two_endpoint_energy $tampered_initial_momentum`) ==
            "error invalidBoundedScalarTwoEndpointEnergy"
        tampered_common_error = copy(two_endpoint_arguments)
        tampered_common_error[end] = "0/1"
        @test readchomp(
            `$ORACLE bounded_scalar_two_endpoint_energy $tampered_common_error`) ==
            "error invalidBoundedScalarTwoEndpointEnergy"
        weight_arguments = Certificates.
            bounded_scalar_two_endpoint_weight_certificate_arguments(
                bounded_trace_certificate, bounded_affine_certificate,
                bounded_two_endpoint_selection.weights)
        @test readchomp(
            `$ORACLE bounded_scalar_two_endpoint_weight $weight_arguments`) ==
            "ok"
        tampered_weight_link = copy(weight_arguments)
        energy_length = parse(Int, tampered_weight_link[1])
        tampered_weight_link[energy_length + 6] = "-1/1"
        @test readchomp(
            `$ORACLE bounded_scalar_two_endpoint_weight $tampered_weight_link`) ==
            "error invalidBoundedScalarTwoEndpointWeight"
        bounded_cumulative_arguments = Certificates.
            rounded_cumulative_certificate_arguments(
                bounded_two_endpoint_selection.cumulative)
        @test readchomp(
            `$ORACLE rounded_cumulative $bounded_cumulative_arguments`) == "ok"
        bounded_draw_arguments = Certificates.scaled_draw_certificate_arguments(
            bounded_two_endpoint_selection.draw)
        @test readchomp(`$ORACLE scaled_draw $bounded_draw_arguments`) == "ok"
        bounded_decision_arguments = Certificates.
            multinomial_decision_certificate_arguments(
                bounded_two_endpoint_selection.decision)
        @test readchomp(
            `$ORACLE multinomial_decision $bounded_decision_arguments`) == "ok"
    end
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

@testset "continuous and mixed-state diagnostics" begin
    @testset "Geweke forward/backward joint-distribution test" begin
        # Hierarchical Gaussian model: θ ~ N(0,1), x | θ ~ N(θ,1).
        # The forward path draws iid joint samples. The backward path alternates
        # the exact x | θ update with HMC for θ | x, whose potential gradient is
        # 2θ-x. Agreement is an implementation diagnostic, not a replacement
        # for the Lean invariance theorem behind the HMC update.
        function geweke_paths(seed, iterations, burnin)
            forward_rng = MersenneTwister(seed)
            forward_theta = randn(forward_rng, iterations - burnin)
            forward_x = forward_theta .+ randn(forward_rng, iterations - burnin)

            backward_rng = MersenneTwister(seed + 1)
            observation = Ref(0.0)
            theta_sampler = ScalarHMC(
                θ -> -(θ^2 + (observation[] - θ)^2) / 2,
                θ -> 2θ - observation[], 0.22, 5)
            backward_theta = Vector{Float64}(undef, iterations - burnin)
            backward_x = similar(backward_theta)
            theta = 0.0
            for iteration in 1:iterations
                x = theta + randn(backward_rng)
                observation[] = x
                theta = step(backward_rng, theta_sampler, theta)
                if iteration > burnin
                    index = iteration - burnin
                    backward_theta[index] = theta
                    backward_x[index] = x
                end
            end
            (; forward_theta, forward_x, backward_theta, backward_x)
        end

        function two_sample_ks(first, second)
            left, right = sort(first), sort(second)
            i = j = 0
            distance = 0.0
            while i < length(left) || j < length(right)
                value = j == length(right) ||
                    (i < length(left) && left[i + 1] <= right[j + 1]) ?
                    left[i + 1] : right[j + 1]
                while i < length(left) && left[i + 1] <= value
                    i += 1
                end
                while j < length(right) && right[j + 1] <= value
                    j += 1
                end
                distance = max(distance,
                    abs(i / length(left) - j / length(right)))
            end
            distance
        end

        paths = geweke_paths(0x6e657765, 14_000, 2_000)
        repeated = geweke_paths(0x6e657765, 14_000, 2_000)
        @test paths.backward_theta == repeated.backward_theta
        @test paths.backward_x == repeated.backward_x
        @test two_sample_ks(paths.forward_theta, paths.backward_theta) < 0.06
        @test two_sample_ks(paths.forward_x, paths.backward_x) < 0.06
        @test abs(mean(paths.backward_theta)) < 0.07
        @test abs(var(paths.backward_theta) - 1) < 0.10
        @test abs(var(paths.backward_x) - 2) < 0.14
        @test abs(cov(paths.backward_theta, paths.backward_x) - 1) < 0.10
    end
    @testset "continuous normal-target moment matching" begin
        sampler = GaussianRWMH(x -> -x^2 / 2, 1.0)
        chain = sample(MersenneTwister(2026), sampler, 0.0, 50_000)
        retained = @view chain[5_001:end]
        retained_matrix = reshape(retained, 1, :)
        diagnostics = QualityDiagnostics.moment_diagnostics(
            retained_matrix, [0.0], [1.0])
        mean_standard_error = only(
            QualityDiagnostics.batch_mean_standard_error(retained_matrix))
        @test abs(only(diagnostics.means)) < max(0.02, 4 * mean_standard_error)
        @test diagnostics.relative_variance_rmse < 0.12
        @test diagnostics.minimum_ess > 2_000
        @test QualityDiagnostics.covariance_max_error(
            retained_matrix, reshape([1.0], 1, 1)) < 0.12
        normal_probabilities = [0.1, 0.5, 0.9]
        normal_quantiles = reshape([-1.2815515655446004, 0.0,
            1.2815515655446004], 1, :)
        @test QualityDiagnostics.marginal_quantile_max_error(retained_matrix,
            normal_probabilities, normal_quantiles) < 0.08

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
        @test QualityDiagnostics.covariance_max_error(
            retained, Matrix{Float64}(I, 2, 2)) < 0.12
        @test size(sample(MersenneTwister(1), sampler, [0.0, 0.0], 3)) == (2, 3)
        @test_throws ArgumentError VectorHMC(logdensity, gradient, 0.0)
        @test_throws ArgumentError step(MersenneTwister(1), sampler, Float64[])
    end
    @testset "shared benchmark target contracts" begin
        targets = TestTargets.suite(2)
        @test getproperty.(targets, :name) == [
            "isotropic-gaussian", "correlated-gaussian-rho-0.9",
            "product-quartic", "ill-conditioned-gaussian",
            "regularized-logistic"]
        point, δ = [0.3, -0.4], 1e-6
        for target in targets
            finite_difference = [(target.logdensity(point + δ .* (1:2 .== j)) -
                target.logdensity(point - δ .* (1:2 .== j))) / (2δ)
                for j in 1:2]
            @test finite_difference ≈ -target.gradient(point) atol=1e-8
            @test target.logdensity(point) == target.logdensity(-point)
        end

        for (offset, name) in enumerate(("product-quartic", "regularized-logistic"))
            target = only(filter(target -> target.name == name, targets))
            sampler = VectorHMC(target.logdensity, target.gradient, 0.12, 8)
            chain = sample(MersenneTwister(0x7a40 + offset), sampler,
                zeros(2), 20_000)[:, 2001:end]
            diagnostics = QualityDiagnostics.moment_diagnostics(
                chain, target.mean, target.variance)
            @test maximum(abs, diagnostics.means) < 0.08
            @test maximum(abs.(diagnostics.variances ./
                target.variance .- 1)) < 0.15
        end
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
        probabilities = [0.6, 0.3, 0.1]
        event_trace(kinetic) = [Runtime.UniformEvent(0.25),
            Runtime.UniformEvent(1 - exp(-kinetic))]

        # Enough Laplace kinetic energy crosses an uphill potential jump.
        crossing_events = event_trace(1.0)
        reference_crossing = Reference.categorical_dhmc_step!(
            Runtime.FloatTraceSource(copy(crossing_events)), probabilities, 1, 1)
        optimized_crossing = Optimized.categorical_dhmc_step!(
            Runtime.FloatTraceSource(copy(crossing_events)), probabilities, 1, 1)
        @test reference_crossing == optimized_crossing == 2

        # Insufficient energy leaves the category fixed and reflects momentum.
        reflection_events = event_trace(0.2)
        @test Reference.categorical_dhmc_step!(
            Runtime.FloatTraceSource(copy(reflection_events)), probabilities, 1, 1) == 1
        @test Optimized.categorical_dhmc_step!(
            Runtime.FloatTraceSource(copy(reflection_events)), probabilities, 1, 1) == 1

        # Downhill moves increase kinetic energy and always cross, even from zero.
        downhill_events = event_trace(0.0)
        @test Reference.categorical_dhmc_step!(
            Runtime.FloatTraceSource(copy(downhill_events)), probabilities, 1, 3) == 1
        @test Optimized.categorical_dhmc_step!(
            Runtime.FloatTraceSource(copy(downhill_events)), probabilities, 1, 3) == 1

        sampler = CategoricalDHMC(probabilities, 4)
        chain = sample(MersenneTwister(0xd4ac), sampler, 1, 60_000)[5001:end]
        frequencies = [count(==(state), chain) / length(chain) for state in 1:3]
        @test maximum(abs.(frequencies .- probabilities)) < 0.02

        @test_throws ArgumentError CategoricalDHMC([1.0])
        @test_throws ArgumentError CategoricalDHMC([1.0, 0.0])
        @test_throws ArgumentError CategoricalDHMC([1.0, 1.0], 0)
        @test_throws ArgumentError step(MersenneTwister(1), sampler, 0)
    end
    @testset "momentum and kinetic-energy units" begin
        events = [Runtime.NormalEvent(0.5), Runtime.UniformEvent(0.9)]
        reference = Reference.scalar_hmc_step!(
            Runtime.FloatTraceSource(copy(events)), _ -> 0.0, _ -> 0.0,
            0.2, 2, 0.0)
        optimized = Optimized.scalar_hmc_step!(
            Runtime.FloatTraceSource(copy(events)), _ -> 0.0, _ -> 0.0,
            0.2, 2, 0.0)
        @test reference == 0.2
        @test optimized == reference
    end
end

@testset "robustness and performance diagnostics" begin
    @testset "zero momentum and nonsmooth boundaries" begin
        q, p = Optimized.leapfrog(identity, 0.1, 0.0, 0.0)
        @test q == 0.0
        @test p == 0.0
        @test all(isfinite, (q, p))
    end
    @testset "high-dimensional and ill-conditioned targets" begin
        dimension = 16
        sampler = VectorHMC(q -> -sum(abs2, q) / 2, identity, 0.08, 4)
        chain = sample(MersenneTwister(0x16d1), sampler,
            zeros(dimension), 100)
        @test size(chain) == (dimension, 100)
        @test all(isfinite, chain)
    end
    @testset "multimodal discrete targets" begin
        sampler = FiniteMH(FiniteWeights([9, 1, 9]),
            FiniteKernelWeights(fill(1, 3, 3)))
        chain = sample(MersenneTwister(0x3d15), sampler, 1, 30_000)
        frequencies = [count(==(state), chain) / length(chain) for state in 1:3]
        expected = [9, 1, 9] ./ 19
        @test maximum(abs.(frequencies .- expected)) < 0.025
        @test frequencies[2] < frequencies[1]
        @test frequencies[2] < frequencies[3]
    end
    @testset "adaptation correctness" begin
        config = WarmupGaussianRWMH(x -> -x^2 / 2, 0.15, 1_000;
            target_accept=0.44, learning_rate=0.6,
            min_scale=0.05, max_scale=4.0)
        first = warmup(MersenneTwister(0xada7), config, 0.0)
        second = warmup(MersenneTwister(0xada7), config, 0.0)
        @test first.state == second.state
        @test first.scales == second.scales
        @test first.accepted == second.accepted
        @test first.sampler.scale == first.scales[end]
        @test all(scale -> 0.05 <= scale <= 4.0, first.scales)
        observed_changes = abs.(diff(log.(first.scales)))
        allowed_changes = config.learning_rate ./ sqrt.(1:config.iterations)
        @test all(observed_changes .<= allowed_changes .+ 1e-14)

        # Once warmup returns, ordinary frozen-kernel sampling is exactly the
        # existing GaussianRWMH API.
        frozen_rng = MersenneTwister(0xf20a)
        direct_rng = MersenneTwister(0xf20a)
        @test sample(frozen_rng, first.sampler, first.state, 100) ==
            sample(direct_rng, GaussianRWMH(config.logdensity,
                first.scales[end]), first.state, 100)

        chain = sample(MersenneTwister(0xada8), config, 0.0, 30_000)[3001:end]
        @test abs(mean(chain)) < 0.07
        @test abs(var(chain) - 1) < 0.10

        @test_throws ArgumentError WarmupGaussianRWMH(identity, 0.0, 10)
        @test_throws ArgumentError WarmupGaussianRWMH(identity, 1.0, -1)
        @test_throws ArgumentError WarmupGaussianRWMH(identity, 1.0, 10;
            target_accept=1.0)
        @test_throws ArgumentError WarmupGaussianRWMH(identity, 1.0, 10;
            min_scale=2.0, max_scale=1.0)

        adaptive = IndefiniteAdaptiveBool()
        adaptive_first = sample(MersenneTwister(0x1def), adaptive, false, 40_000)
        adaptive_second = sample(MersenneTwister(0x1def), adaptive, false, 40_000)
        @test adaptive_first == adaptive_second
        @test abs(mean(adaptive_first[end-9_999:end]) - 0.5) < 0.025
        @test_throws ArgumentError sample(MersenneTwister(1), adaptive, false, -1)

        continuous_adaptive = IndefiniteAdaptiveContinuousRefresh(randn)
        continuous_first = sample(MersenneTwister(0xc017),
            continuous_adaptive, 4.0, 40_000)
        continuous_second = sample(MersenneTwister(0xc017),
            continuous_adaptive, 4.0, 40_000)
        @test continuous_first == continuous_second
        continuous_tail = @view continuous_first[end-9_999:end]
        @test abs(mean(continuous_tail)) < 0.05
        @test abs(var(continuous_tail) - 1) < 0.08
        @test_throws ArgumentError sample(MersenneTwister(1),
            continuous_adaptive, Inf, 1)
        @test_throws DomainError sample(MersenneTwister(1),
            IndefiniteAdaptiveContinuousRefresh(_ -> Inf), 0.0, 2)
    end
    @testset "positive constrained transform" begin
        sampler = PositiveTransformedRWMH(x -> -x, 0.8)
        first = sample(MersenneTwister(0x105), sampler, 1.0, 25_000)
        second = sample(MersenneTwister(0x105), sampler, 1.0, 25_000)
        @test first == second
        @test all(x -> isfinite(x) && x > 0, first)
        retained = first[2001:end]
        @test abs(mean(retained) - 1) < 0.06
        @test abs(var(retained) - 1) < 0.12
        @test_throws ArgumentError PositiveTransformedRWMH(identity, 0.0)
        @test_throws ArgumentError step(MersenneTwister(1), sampler, 0.0)
    end
    @testset "open-unit constrained transform" begin
        sampler = OpenUnitTransformedRWMH(_ -> 0.0, 1.0)
        first = sample(MersenneTwister(0x10a17), sampler, 0.5, 30_000)
        second = sample(MersenneTwister(0x10a17), sampler, 0.5, 30_000)
        @test first == second
        @test all(x -> isfinite(x) && 0 < x < 1, first)
        retained = first[3001:end]
        @test abs(mean(retained) - 0.5) < 0.025
        @test abs(var(retained) - 1 / 12) < 0.012
        @test_throws ArgumentError OpenUnitTransformedRWMH(identity, 0.0)
        @test_throws ArgumentError step(MersenneTwister(1), sampler, 0.0)
        @test_throws ArgumentError step(MersenneTwister(1), sampler, 1.0)
    end
    @testset "Gaussian Zig-Zag exact clock and moments" begin
        for (q, velocity, e) in ((1.2, 1, 0.7), (-1.2, 1, 0.7),
                (0.4, -1, 1.3))
            wait = gaussian_zigzag_waiting_time(q, velocity, e)
            a = velocity * q
            integrated = a >= 0 ? a * wait + wait^2 / 2 :
                (wait <= -a ? 0.0 : (a + wait)^2 / 2)
            @test integrated ≈ e atol=2e-14
        end
        extreme_wait = gaussian_zigzag_waiting_time(1e16, 1, 1.0)
        @test extreme_wait > 0
        @test extreme_wait ≈ 1e-16 rtol=2e-15
        sampler = GaussianZigZag(0.5)
        first = sample(MersenneTwister(0x2192), sampler, (0.0, 1), 40_000)
        second = sample(MersenneTwister(0x2192), sampler, (0.0, 1), 40_000)
        @test first.positions == second.positions
        @test first.velocities == second.velocities
        @test all(v -> v in (-1, 1), first.velocities)
        retained = first.positions[2001:end]
        @test abs(mean(retained)) < 0.06
        @test abs(var(retained) - 1) < 0.10
        @test_throws ArgumentError GaussianZigZag(0.0)
        @test_throws ArgumentError gaussian_zigzag_waiting_time(0.0, 0, 1.0)
    end
    @testset "ESS and gradient-count benchmarks" begin
        function autocorrelation_ess(values; max_lag=min(1_000, length(values) ÷ 4))
            centered = values .- mean(values)
            variance = sum(abs2, centered) / length(centered)
            variance > 0 || return 0.0
            correlation_sum = 0.0
            for lag in 1:max_lag
                correlation = dot(@view(centered[1:(end - lag)]),
                    @view(centered[(lag + 1):end])) /
                    ((length(centered) - lag) * variance)
                correlation <= 0 && break
                correlation_sum += correlation
            end
            min(length(values), length(values) / (1 + 2correlation_sum))
        end

        hmc = ScalarHMC(x -> -x^2 / 2, identity, 0.20, 10)
        rwmh = GaussianRWMH(x -> -x^2 / 2, 1.0)
        hmc_chain = sample(MersenneTwister(0xe551), hmc, 0.0, 12_000)[2001:end]
        rwmh_chain = sample(MersenneTwister(0xe552), rwmh, 0.0, 12_000)[2001:end]
        hmc_ess = autocorrelation_ess(hmc_chain)
        rwmh_ess = autocorrelation_ess(rwmh_chain)
        @test hmc_ess > 1_000
        @test rwmh_ess > 300
        @test hmc_ess > 1.5rwmh_ess

        reference_gradient_calls = Ref(0)
        reference_logdensity_calls = Ref(0)
        counted_gradient(x) = (reference_gradient_calls[] += 1; x)
        counted_logdensity(x) = (reference_logdensity_calls[] += 1; -x^2 / 2)
        counted_sampler = ScalarHMC(counted_logdensity, counted_gradient, 0.2, 5)
        sample(MersenneTwister(0xc057), counted_sampler, 0.0, 20)
        @test reference_gradient_calls[] == 20 * 5 * 4
        @test reference_logdensity_calls[] == 20 * 2

        optimized_gradient_calls = Ref(0)
        optimized_logdensity_calls = Ref(0)
        optimized_gradient(x) = (optimized_gradient_calls[] += 1; x)
        optimized_logdensity(x) = (optimized_logdensity_calls[] += 1; -x^2 / 2)
        source = Runtime.RNGSource(MersenneTwister(0xc057))
        state = 0.0
        for _ in 1:20
            state = Optimized.scalar_hmc_step!(source, optimized_logdensity,
                optimized_gradient, 0.2, 5, state)
        end
        @test optimized_gradient_calls[] == 20 * 5 * 2
        @test optimized_logdensity_calls[] == 20 * 2
    end
end
