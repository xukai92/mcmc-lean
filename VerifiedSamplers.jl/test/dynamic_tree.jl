@testset "finite dynamic-tree certificates" begin
    # Two completed components with genuinely different candidate counts.
    valid = certify_dynamic_tree([[1, 2], [2, 1], [3]])
    @test valid.valid
    @test valid.candidates == [[1, 2], [1, 2], [3]]

    missing_root = certify_dynamic_tree([[2], [1, 2]])
    @test !missing_root.valid

    asymmetric_reroot = certify_dynamic_tree([[1, 2], [2]])
    @test !asymmetric_reroot.valid

    @test_throws ArgumentError certify_dynamic_tree(Vector{Vector{Int}}())
    @test_throws ArgumentError certify_dynamic_tree([[1, 3], [2]])

    weighted = certify_dynamic_tree([[1, 2], [1, 2], [3]])
    # Component weights are 1 and 3, hence integer draws 0,1,2,3 select
    # states 1,2,2,2 from either root in the component.
    expected = [1, 2, 2, 2]
    for root in (1, 2), draw in 0:3
        source = Runtime.TraceSource([draw])
        @test certified_dynamic_select!(source, weighted, [1, 3, 2], root) ==
            expected[draw + 1]
        @test Runtime.remaining(source) == 0
    end
    @test certified_dynamic_select!(Runtime.TraceSource([0]), weighted,
        [1, 3, 2], 3) == 3
    @test certified_dynamic_select(MersenneTwister(44), weighted, [1, 3, 2], 1) ==
        certified_dynamic_select(MersenneTwister(44), weighted, [1, 3, 2], 1)
    @test_throws ArgumentError certified_dynamic_select!(Runtime.TraceSource([0]),
        asymmetric_reroot, [1, 1], 1)
    failed_source = Runtime.TraceSource(Int[])
    @test safe_dynamic_select!(failed_source, asymmetric_reroot, [1, 1], 1) == 1
    @test Runtime.remaining(failed_source) == 0
    @test_throws DimensionMismatch safe_dynamic_select!(Runtime.TraceSource(Int[]),
        asymmetric_reroot, [1], 1)
    @test_throws ArgumentError safe_dynamic_select!(Runtime.TraceSource(Int[]),
        asymmetric_reroot, [1, 0], 1)
    @test_throws BoundsError safe_dynamic_select!(Runtime.TraceSource(Int[]),
        asymmetric_reroot, [1, 1], 3)
    @test safe_dynamic_select!(Runtime.TraceSource([3]), weighted,
        [1, 3, 2], 1) == 2
    @test_throws DimensionMismatch certified_dynamic_select!(
        Runtime.TraceSource([0]), weighted, [1, 3], 1)
    @test_throws ArgumentError certified_dynamic_select!(Runtime.TraceSource([0]),
        weighted, [1, 0, 2], 1)

    partition = certified_orbit_partition(Bool[false, true, false, false])
    @test partition.valid
    @test partition.candidates ==
        [[1, 2], [1, 2], [3, 4, 5], [3, 4, 5], [3, 4, 5]]
    @test certified_orbit_partition(Bool[]).candidates == [[1]]
    @test certified_orbit_partition(fill(false, 3)).candidates ==
        [collect(1:4) for _ in 1:4]
    @test certified_orbit_partition(fill(true, 3)).candidates == [[1], [2], [3], [4]]

    recursive = RecursiveBarrierNode(
        RecursiveBarrierNode(RecursiveBarrierLeaf(), false,
            RecursiveBarrierLeaf()),
        true,
        RecursiveBarrierNode(RecursiveBarrierLeaf(), false,
            RecursiveBarrierLeaf()))
    @test recursive_barriers(recursive) == Bool[false, true, false]
    recursive_partition = certified_recursive_partition(recursive)
    @test recursive_partition.valid
    @test recursive_partition.candidates == [[1, 2], [1, 2], [3, 4], [3, 4]]

    uturn = certified_scalar_uturn_partition(
        [0.0, 1.0, 1.5, 1.25, 0.5], [1.0, 0.8, 0.2, -0.5, -0.8])
    @test uturn.valid
    @test uturn.candidates == [[1, 2, 3], [1, 2, 3], [1, 2, 3], [4, 5], [4, 5]]
    @test certified_scalar_uturn_partition([0.0], [1.0]).candidates == [[1]]
    @test_throws DimensionMismatch certified_scalar_uturn_partition([0.0], [1.0, 2.0])
    @test_throws ArgumentError certified_scalar_uturn_partition(Float64[], Float64[])
    @test_throws DomainError certified_scalar_uturn_partition([0.0, Inf], [1.0, 1.0])

    vector_uturn = certified_vector_uturn_partition(
        [[0.0, 0.0], [1.0, 0.0], [1.5, 0.5], [1.25, 0.5]],
        [[1.0, 0.0], [0.8, 0.2], [0.2, 0.1], [-0.5, 0.0]])
    @test vector_uturn.valid
    @test vector_uturn.candidates ==
        [[1, 2, 3], [1, 2, 3], [1, 2, 3], [4]]
    spanning_uturn = certified_spanning_uturn_partition(
        [[0.0], [1.0], [2.0]], [[1.0], [1.0], [-1.0]])
    @test spanning_uturn.valid
    @test spanning_uturn.candidates == [[1], [2], [3]]
    @test certified_spanning_uturn_partition([[0.0]], [[1.0]]).candidates == [[1]]
    @test_throws DimensionMismatch certified_vector_uturn_partition(
        [[0.0]], [[1.0], [2.0]])
    @test_throws DimensionMismatch certified_vector_uturn_partition(
        [[0.0], [1.0, 2.0]], [[1.0], [1.0]])
    @test_throws ArgumentError certified_vector_uturn_partition(
        Vector{Vector{Float64}}(), Vector{Vector{Float64}}())
    @test_throws DomainError certified_spanning_uturn_partition(
        [[0.0], [Inf]], [[1.0], [1.0]])

    # Root-dependent first-stop rows are usable only when the reroot checker
    # accepts them. A monotone orbit completes to the same full candidate set.
    checked_first_stop = first_stop_endpoint_uturn_candidates(
        [0.0, 1.0, 2.0], [1.0, 1.0, 1.0])
    @test checked_first_stop.valid
    @test checked_first_stop.candidates == [collect(1:3) for _ in 1:3]

    # This curved orbit stops at different intervals from different roots;
    # retaining the rows is useful diagnostically, but certification rejects
    # them rather than transferring the verified selection theorem.
    rejected_first_stop = first_stop_endpoint_uturn_candidates(
        [0.0, 1.0, 1.5, 1.25, 0.5], [1.0, 0.8, 0.2, -0.5, -0.8])
    @test !rejected_first_stop.valid
    @test all(root in rejected_first_stop.candidates[root] for root in 1:5)
    @test_throws DimensionMismatch first_stop_endpoint_uturn_candidates(
        [[0.0]], [[1.0], [2.0]])
    @test_throws ArgumentError first_stop_endpoint_uturn_candidates(
        Vector{Vector{Float64}}(), Vector{Vector{Float64}}())
end

@testset "certified conservative dynamic HMC" begin
    candidates = [1, 3, 4]
    logweights = log.([1.0, 3.0, 2.0])
    for draw in (0.0, 0.15, 0.65, prevfloat(1.0))
        reference_source = Runtime.FloatTraceSource(
            Runtime.FloatTraceEvent[Runtime.UniformEvent(draw)])
        optimized_source = Runtime.FloatTraceSource(
            Runtime.FloatTraceEvent[Runtime.UniformEvent(draw)])
        @test Reference.dynamic_select_float!(reference_source,
            candidates, logweights) ==
            Optimized.dynamic_select_float!(optimized_source,
                candidates, logweights)
        @test Runtime.remaining(reference_source) == 0
        @test Runtime.remaining(optimized_source) == 0
    end
    @test_throws DimensionMismatch Reference.dynamic_select_float!(
        Runtime.FloatTraceSource(Runtime.FloatTraceEvent[]), [1], [0.0, 1.0])
    @test_throws DomainError Optimized.dynamic_select_float!(
        Runtime.FloatTraceSource(Runtime.FloatTraceEvent[]), [1], [Inf])

    logdensity(q) = -sum(abs2, q) / 2
    gradient(q) = q
    sampler = CertifiedDynamicHMC(logdensity, gradient, 0.12, 8)
    first_chain = sample(MersenneTwister(0xd1a), sampler, [0.2, -0.4], 20)
    second_chain = sample(MersenneTwister(0xd1a), sampler, [0.2, -0.4], 20)
    @test first_chain == second_chain
    @test size(first_chain) == (2, 20)
    @test all(isfinite, first_chain)

    reference_source = Runtime.RNGSource(MersenneTwister(0x51ec7))
    optimized_source = Runtime.RNGSource(MersenneTwister(0x51ec7))
    reference = VerifiedSamplers._certified_dynamic_hmc_step!(reference_source,
        Reference.dynamic_select_float!, sampler, [0.2, -0.4])
    optimized = VerifiedSamplers._certified_dynamic_hmc_step!(optimized_source,
        Optimized.dynamic_select_float!, sampler, [0.2, -0.4])
    @test reference == optimized

    @test_throws ArgumentError CertifiedDynamicHMC(logdensity, gradient, 0.0, 8)
    @test_throws ArgumentError CertifiedDynamicHMC(logdensity, gradient, 0.1, 0)
    @test_throws ArgumentError step(MersenneTwister(1), sampler, Float64[])
end

@testset "checked first-stop dynamic HMC" begin
    flat_logdensity(q) = 0.0
    zero_gradient(q) = zero(q)
    sampler = CheckedFirstStopDynamicHMC(flat_logdensity, zero_gradient, 0.5, 2)

    # Constant positive momentum gives one common completed row from every
    # root, so certification succeeds and consumes the selector draw.
    events = Runtime.FloatTraceEvent[
        Runtime.NormalEvent(1.0), Runtime.IndexEvent(1),
        Runtime.UniformEvent(0.0)]
    reference_source = Runtime.FloatTraceSource(copy(events))
    optimized_source = Runtime.FloatTraceSource(copy(events))
    reference = VerifiedSamplers._checked_first_stop_dynamic_hmc_step!(
        reference_source, Reference.dynamic_select_float!, sampler, [0.0])
    optimized = VerifiedSamplers._checked_first_stop_dynamic_hmc_step!(
        optimized_source, Optimized.dynamic_select_float!, sampler, [0.0])
    @test reference == optimized == [-0.5]
    @test Runtime.remaining(reference_source) == 0
    @test Runtime.remaining(optimized_source) == 0

    # This harmonic orbit produces root-dependent incompatible stopped rows.
    # The checked-or-identity boundary retains the current state and consumes
    # no selector event.
    normal_logdensity(q) = -sum(abs2, q) / 2
    normal_gradient(q) = q
    rejected = CheckedFirstStopDynamicHMC(
        normal_logdensity, normal_gradient, 1.0, 4)
    rejected_source = Runtime.FloatTraceSource(Runtime.FloatTraceEvent[
        Runtime.NormalEvent(1.0), Runtime.IndexEvent(0),
        Runtime.UniformEvent(0.2)])
    @test VerifiedSamplers._checked_first_stop_dynamic_hmc_step!(
        rejected_source, Reference.dynamic_select_float!, rejected, [0.0]) == [0.0]
    @test Runtime.remaining(rejected_source) == 1

    first_chain = sample(MersenneTwister(0xf1757), sampler, [0.0], 20)
    second_chain = sample(MersenneTwister(0xf1757), sampler, [0.0], 20)
    @test first_chain == second_chain
    @test size(first_chain) == (1, 20)
    @test_throws ArgumentError CheckedFirstStopDynamicHMC(
        flat_logdensity, zero_gradient, 0.0, 2)
    @test_throws ArgumentError CheckedFirstStopDynamicHMC(
        flat_logdensity, zero_gradient, 0.5, 0)
end
