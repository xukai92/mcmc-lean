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
    repaired_first_stop = coherent_dynamic_tree(rejected_first_stop.candidates)
    @test repaired_first_stop.valid
    @test all(Set(repaired_first_stop.candidates[root]) ⊆
        Set(rejected_first_stop.candidates[root]) for root in 1:5)
    @test all(root in repaired_first_stop.candidates[root] for root in 1:5)

    already_partitioned = [[1, 2], [2, 1], [3]]
    @test coherent_dynamic_tree(already_partitioned).candidates ==
        certify_dynamic_tree(already_partitioned).candidates
    @test_throws ArgumentError coherent_dynamic_tree([[2], [2]])
    @test_throws DimensionMismatch first_stop_endpoint_uturn_candidates(
        [[0.0]], [[1.0], [2.0]])
    @test_throws ArgumentError first_stop_endpoint_uturn_candidates(
        Vector{Vector{Float64}}(), Vector{Vector{Float64}}())

    # Rooted recursive doubling exposes its complete row family to the same
    # checker. Zero depths is the identity partition. Boundary-dependent and
    # U-turn-excluded rows are retained diagnostically but rejected globally.
    recursive_identity = recursive_doubling_uturn_candidates(
        collect(0.0:6.0), ones(7), Bool[])
    @test recursive_identity.valid
    @test recursive_identity.candidates == [[i] for i in 1:7]
    generated_recursive_identity = generated_dynamic_tree(
        "checked-recursive-doubling", collect(0.0:6.0), ones(7), Bool[])
    @test generated_recursive_identity.valid == recursive_identity.valid
    @test generated_recursive_identity.candidates == recursive_identity.candidates
    recursive_boundary = recursive_doubling_uturn_candidates(
        collect(0.0:6.0), ones(7), Bool[true, false])
    @test !recursive_boundary.valid
    @test recursive_boundary.candidates[3] == collect(1:4)
    reference_boundary_rows = Reference.recursive_doubling_rows(
        collect(0.0:6.0), ones(7), Bool[true, false])
    @test reference_boundary_rows == recursive_boundary.candidates
    recursive_fallback_source = Runtime.TraceSource(Int[])
    @test safe_dynamic_select!(recursive_fallback_source,
        recursive_boundary, ones(Int, 7), 3) == 3
    @test Runtime.remaining(recursive_fallback_source) == 0
    recursive_turn = recursive_doubling_uturn_candidates(
        [0.0, 1.0, 1.5, 1.25, 0.5], [1.0, 0.8, 0.2, -0.5, -0.8],
        Bool[true, false])
    @test !recursive_turn.valid
    @test recursive_turn.candidates[3] == [3]
    @test Reference.recursive_doubling_rows(
        [0.0, 1.0, 1.5, 1.25, 0.5], [1.0, 0.8, 0.2, -0.5, -0.8],
        Bool[true, false]) == recursive_turn.candidates
    @test_throws DimensionMismatch recursive_doubling_uturn_candidates(
        [0.0], [1.0, 2.0], Bool[])
    @test_throws DomainError recursive_doubling_uturn_candidates(
        [0.0, Inf], [1.0, 1.0], Bool[true])
end

@testset "generated eligible-count streaming selection" begin
    segments = [[10, 20], Int[], [30, 40, 50]]

    # Reference follows the recursive local-representative/merge policy.
    reference_source = Runtime.FloatTraceSource(Runtime.FloatTraceEvent[
        Runtime.IndexEvent(1), Runtime.IndexEvent(2), Runtime.IndexEvent(4)])
    @test Reference.streaming_eligible_select!(reference_source, segments) == 50
    @test Runtime.remaining(reference_source) == 0

    # Optimized samples the proved-equivalent flattened eligible law directly.
    optimized_source = Runtime.FloatTraceSource(
        Runtime.FloatTraceEvent[Runtime.IndexEvent(4)])
    @test Optimized.streaming_eligible_select!(optimized_source, segments) == 50
    @test Runtime.remaining(optimized_source) == 0

    empty_segments = [Int[], Int[]]
    empty_source = Runtime.FloatTraceSource(Runtime.FloatTraceEvent[])
    @test Reference.streaming_eligible_select!(empty_source, empty_segments) === nothing
    @test Optimized.streaming_eligible_select!(empty_source, empty_segments) === nothing

    # Both independent implementations recover the exact uniform law on the
    # five eligible occurrences. This remains an empirical implementation test;
    # the corresponding distribution identity is proved in Lean.
    trials = 50_000
    for implementation in (Reference.streaming_eligible_select!,
            Optimized.streaming_eligible_select!)
        source = Runtime.RNGSource(MersenneTwister(0xc4))
        counts = Dict(value => 0 for value in (10, 20, 30, 40, 50))
        for _ in 1:trials
            selected = implementation(source, segments)
            counts[selected] += 1
        end
        @test all(abs(count / trials - 0.2) < 0.012 for count in values(counts))
    end

    first_rng, second_rng = MersenneTwister(17), MersenneTwister(17)
    first = [streaming_eligible_select(first_rng, segments) for _ in 1:100]
    second = [streaming_eligible_select(second_rng, segments) for _ in 1:100]
    @test first == second
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

@testset "completed-tree C.4 dynamic HMC" begin
    # An actual optimized-compatible exact-dyadic Gaussian trajectory reaches
    # the productive C.4 path with zero arithmetic discrepancy.
    dyadic_positions = [[0.0]]
    dyadic_momenta = [[1.0]]
    dyadic_q, dyadic_p = 0.0, 1.0
    for _ in 1:3
        step_certificate =
            Certificates.certify_gaussian_dyadic_leapfrog_step(
                0.5, dyadic_q, dyadic_p)
        dyadic_q, dyadic_p = step_certificate.next_position,
            step_certificate.next_momentum
        push!(dyadic_positions, [dyadic_q])
        push!(dyadic_momenta, [dyadic_p])
    end
    for left in 1:4, right in 1:4
        left == right && continue
        uturn_certificate = Certificates.certify_vector_uturn_decision(
            dyadic_positions[left], dyadic_positions[left], [0.0],
            dyadic_positions[right], dyadic_positions[right], [0.0],
            dyadic_momenta[left], dyadic_momenta[left], [0.0],
            dyadic_momenta[right], dyadic_momenta[right], [0.0])
        @test Certificates.is_stable(uturn_certificate)
    end
    dyadic_tree = completed_tree_c4_candidates(
        dyadic_positions, dyadic_momenta)
    @test dyadic_tree.valid
    @test dyadic_tree.candidates == [collect(1:4) for _ in 1:4]

    # A genuinely rounded `ε = 0.1` Gaussian orbit is checked step by step,
    # linked into four phase leaves, and clears every off-diagonal U-turn
    # margin under the same `10^-14` budget proved in Lean.
    rounded_steps = Certificates.GaussianRoundedLeapfrogStepCertificate[]
    rounded_positions = [[0.0]]
    rounded_momenta = [[1.0]]
    rounded_q, rounded_p = 0.0, 1.0
    for _ in 1:3
        certificate = Certificates.certify_gaussian_rounded_leapfrog_step(
            0.1, rounded_q, rounded_p)
        push!(rounded_steps, certificate)
        rounded_q, rounded_p = certificate.next_position,
            certificate.next_momentum
        push!(rounded_positions, [rounded_q])
        push!(rounded_momenta, [rounded_p])
        if isfile(ORACLE)
            arguments = Certificates.gaussian_rounded_leapfrog_certificate_arguments(
                certificate)
            @test readchomp(`$ORACLE gaussian_rounded_leapfrog $arguments`) == "ok"
        end
    end
    rounded_arguments =
        Certificates.gaussian_rounded_four_leaf_certificate_arguments(rounded_steps)
    if isfile(ORACLE)
        @test readchomp(`$ORACLE rounded_gaussian_four_leaf $rounded_arguments`) == "ok"
        tampered = copy(rounded_arguments)
        tampered[end] = "0/1"
        @test readchomp(`$ORACLE rounded_gaussian_four_leaf $tampered`) ==
            "error invalidRoundedGaussianFourLeaf"
    end
    ideal_positions = [[BigFloat(0)], [BigFloat(1) / 10],
        [BigFloat(199) / 1000], [BigFloat(29601) / 100000]]
    ideal_momenta = [[BigFloat(1)], [BigFloat(199) / 200],
        [BigFloat(19601) / 20000], [BigFloat(1910599) / 2000000]]
    rounded_bounds = [fill(big"1e-14", 1) for _ in 1:4]
    for left in 1:4, right in 1:4
        left == right && continue
        certificate = Certificates.certify_vector_uturn_decision(
            rounded_positions[left], ideal_positions[left], rounded_bounds[left],
            rounded_positions[right], ideal_positions[right], rounded_bounds[right],
            rounded_momenta[left], ideal_momenta[left], rounded_bounds[left],
            rounded_momenta[right], ideal_momenta[right], rounded_bounds[right])
        @test Certificates.is_stable(certificate)
        @test Certificates.certified_uturn_decision(certificate) == (right < left)
    end

    # Mirrors Lean's `tenthErrorFourLeafTrajectory`: every distinct endpoint
    # clears a nonzero 0.1 coordinate-error budget. Self-pairs have zero dot
    # product and are handled structurally, not by an impossible strict margin.
    positions = [[Float64(index)] for index in 0:3]
    momenta = [[1.0] for _ in 1:4]
    bounds = [[0.1] for _ in 1:4]
    for left in 1:4, right in 1:4
        certificate = Certificates.certify_vector_uturn_decision(
            positions[left], positions[left], bounds[left],
            positions[right], positions[right], bounds[right],
            momenta[left], momenta[left], bounds[left],
            momenta[right], momenta[right], bounds[right])
        if left == right
            @test !Certificates.is_stable(certificate)
        else
            @test Certificates.is_stable(certificate)
            @test Certificates.certified_uturn_decision(certificate) ==
                (right < left)
        end
    end

    for depth in 0:8, root in 1:(1 << depth)
        directions = completed_tree_direction_trace(root, depth)
        @test length(directions) == depth
        decoded = 0
        for (level, grow_right) in enumerate(directions)
            !grow_right && (decoded += 1 << (level - 1))
        end
        @test decoded == root - 1
    end
    @test completed_tree_direction_trace(1, 0) == Bool[]
    @test_throws BoundsError completed_tree_direction_trace(0, 2)
    @test_throws BoundsError completed_tree_direction_trace(5, 2)
    @test_throws ArgumentError completed_tree_direction_trace(1, -1)

    monotone = completed_tree_c4_candidates(collect(0.0:7.0), ones(8))
    @test monotone.valid
    @test monotone.candidates == [collect(1:8) for _ in 1:8]
    @test_throws ArgumentError completed_tree_c4_candidates(
        collect(0.0:5.0), ones(6))

    flat_logdensity(q) = 0.0
    zero_gradient(q) = zero(q)
    sampler = CompletedTreeC4DynamicHMC(
        flat_logdensity, zero_gradient, 0.5, 2)
    events = Runtime.FloatTraceEvent[
        Runtime.NormalEvent(1.0), Runtime.IndexEvent(0),
        Runtime.UniformEvent(0.6)]
    reference_source = Runtime.FloatTraceSource(copy(events))
    optimized_source = Runtime.FloatTraceSource(copy(events))
    reference = VerifiedSamplers._completed_tree_c4_dynamic_hmc_step!(
        reference_source, Reference.dynamic_select_float!, sampler, [0.0])
    optimized = VerifiedSamplers._completed_tree_c4_dynamic_hmc_step!(
        optimized_source, Optimized.dynamic_select_float!, sampler, [0.0])
    @test reference == optimized
    @test reference != [0.0]
    @test Runtime.remaining(reference_source) == 0
    @test Runtime.remaining(optimized_source) == 0

    normal_logdensity(q) = -sum(abs2, q) / 2
    normal_gradient(q) = q
    normal_sampler = CompletedTreeC4DynamicHMC(
        normal_logdensity, normal_gradient, 0.12, 3)
    first_chain = sample(MersenneTwister(0xc4), normal_sampler, [0.0, 0.0], 100)
    second_chain = sample(MersenneTwister(0xc4), normal_sampler, [0.0, 0.0], 100)
    @test first_chain == second_chain
    @test size(first_chain) == (2, 100)
    @test all(isfinite, first_chain)
    @test any(!iszero, first_chain)
    @test_throws ArgumentError CompletedTreeC4DynamicHMC(
        normal_logdensity, normal_gradient, 0.0, 3)
    @test_throws ArgumentError CompletedTreeC4DynamicHMC(
        normal_logdensity, normal_gradient, 0.1, -1)
end

@testset "checked randomized recursive dynamic HMC" begin
    flat_logdensity(q) = 0.0
    zero_gradient(q) = zero(q)
    sampler = CheckedRecursiveDynamicHMC(flat_logdensity, zero_gradient, 0.5, 3)

    # A sampled two-bit direction trace produces boundary-dependent rooted
    # rows on this monotone orbit. Global certification rejects it, so the
    # proved randomized checked-or-identity policy consumes no selector draw.
    events = Runtime.FloatTraceEvent[
        Runtime.NormalEvent(1.0), Runtime.IndexEvent(0),
        Runtime.IndexEvent(1), Runtime.IndexEvent(0),
        Runtime.UniformEvent(0.25)]
    reference_source = Runtime.FloatTraceSource(copy(events))
    optimized_source = Runtime.FloatTraceSource(copy(events))
    reference = VerifiedSamplers._checked_recursive_dynamic_hmc_step!(
        reference_source, Reference.dynamic_select_float!, sampler, [0.0])
    optimized = VerifiedSamplers._checked_recursive_dynamic_hmc_step!(
        optimized_source, Optimized.dynamic_select_float!, sampler, [0.0])
    @test reference == optimized == [0.0]
    @test Runtime.remaining(reference_source) == 1
    @test Runtime.remaining(optimized_source) == 1

    first_chain = sample(MersenneTwister(0xdecaf), sampler, [0.0], 20)
    second_chain = sample(MersenneTwister(0xdecaf), sampler, [0.0], 20)
    @test first_chain == second_chain
    @test size(first_chain) == (1, 20)
    @test_throws ArgumentError CheckedRecursiveDynamicHMC(
        flat_logdensity, zero_gradient, 0.0, 3)
    @test_throws ArgumentError CheckedRecursiveDynamicHMC(
        flat_logdensity, zero_gradient, 0.5, 0)
    @test_throws ArgumentError step(MersenneTwister(1), sampler, Float64[])
end

@testset "interpreted Lean NUTS subtree program" begin
    program = Reference.NUTS_TREE_PROGRAMS["checked-nuts-reference"]
    tree = Reference.NUTSTreeNode(
        Reference.NUTSTreeNode(
            Reference.NUTSTreeLeaf(0), Reference.NUTSTreeLeaf(1)),
        Reference.NUTSTreeNode(
            Reference.NUTSTreeLeaf(2), Reference.NUTSTreeLeaf(3)))

    complete = Reference.interpret_nuts_subtree(
        program, tree, _ -> true, (_, _) -> false)
    @test complete.visited_leaves == 4
    @test complete.candidates == [0, 1, 2, 3]
    @test complete.continues

    visited = Int[]
    left_failure = Reference.interpret_nuts_subtree(program, tree,
        phase -> (push!(visited, phase); phase != 1), (_, _) -> false)
    @test visited == [0, 1]
    @test left_failure.visited_leaves == 2
    @test left_failure.candidates == [0]
    @test !left_failure.continues

    joins = Tuple{Int,Int}[]
    root_turn = Reference.interpret_nuts_subtree(program, tree, _ -> true,
        (left, right) -> (push!(joins, (left, right)); (left, right) == (0, 3)))
    @test joins == [(0, 1), (2, 3), (0, 3)]
    @test root_turn.candidates == [0, 1, 2, 3]
    @test !root_turn.continues

    forward = Reference.interpret_nuts_directional_subtree(program, 0, true, 2,
        (_, phase) -> phase + 1, _ -> true, (_, _) -> false)
    backward = Reference.interpret_nuts_directional_subtree(program, 0, false, 2,
        (_, phase) -> phase - 1, _ -> true, (_, _) -> false)
    @test forward.candidates == [1, 2, 3, 4]
    @test backward.candidates == [-4, -3, -2, -1]
    @test forward.visited_leaves == backward.visited_leaves == 4
    @test_throws ArgumentError Reference.build_nuts_phase_tree(
        program, 0, true, 11, (_, phase) -> phase + 1)

    outer = Reference.interpret_nuts_outer_trace(program, 0,
        Bool[true, false], (right, phase) -> phase + (right ? 1 : -1),
        _ -> true, (_, _) -> false)
    @test outer.left == -2
    @test outer.right == 1
    @test outer.candidates == [-2, -1, 0, 1]
    @test outer.completed_depth == 2
    @test outer.continues

    stopped = Reference.interpret_nuts_outer_trace(program, 0,
        Bool[true, true], (_, phase) -> phase + 1, _ -> true,
        (left, right) -> left == 0 && right == 3)
    @test stopped.candidates == [0, 1]
    @test stopped.completed_depth == 1
    @test !stopped.continues
    @test_throws ArgumentError Reference.interpret_nuts_outer_trace(
        program, 0, fill(true, 11), (_, phase) -> phase + 1,
        _ -> true, (_, _) -> false)

    transition = Reference.interpret_nuts_transition(program, 0,
        Bool[true, false], 0.5, (right, phase) -> phase + (right ? 1 : -1),
        _ -> true, (_, _) -> false,
        phase -> phase == -1 ? log(2.0) : 0.0)
    @test transition.tree.candidates == [-2, -1, 0, 1]
    @test transition.selected == -1
    @test Reference.select_nuts_candidate(
        program, [:left, :right], x -> x === :left ? -Inf : 0.0, 0.0) === :right
    @test_throws ArgumentError Reference.select_nuts_candidate(
        program, [0], _ -> 0.0, 1.0)
    @test_throws DomainError Reference.select_nuts_candidate(
        program, [0], _ -> -Inf, 0.5)

    positions = [[x] for x in 0.0:6.0]
    momenta = [ones(1) for _ in positions]
    checked_rows = Reference.interpret_checked_nuts_rows(
        program, positions, momenta, Bool[true, false])
    legacy_certificate = certify_dynamic_tree(
        Reference.recursive_doubling_rows(
            positions, momenta, Bool[true, false]))
    @test checked_rows.rows == legacy_certificate.candidates
    @test checked_rows.valid == legacy_certificate.valid
    @test !checked_rows.valid
    @test_throws ArgumentError Reference.interpret_checked_nuts_rows(
        program, positions, momenta, fill(true, 11))

    rejected_source = Runtime.FloatTraceSource([Runtime.UniformEvent(0.5)])
    rejected = Reference.checked_nuts_or_identity_select!(rejected_source,
        program, positions, momenta, Bool[true, false], 3, (_, _) -> 0.0)
    @test rejected == 3
    @test Runtime.remaining(rejected_source) == 1

    singleton_source = Runtime.FloatTraceSource([Runtime.UniformEvent(0.5)])
    singleton = Reference.checked_nuts_or_identity_select!(singleton_source,
        program, positions, momenta, Bool[], 3, (_, _) -> 0.0)
    @test singleton == 3
    @test Runtime.remaining(singleton_source) == 0
end
