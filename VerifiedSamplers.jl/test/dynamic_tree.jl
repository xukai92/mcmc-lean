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

    partition = certified_orbit_partition(Bool[false, true, false, false])
    @test partition.valid
    @test partition.candidates ==
        [[1, 2], [1, 2], [3, 4, 5], [3, 4, 5], [3, 4, 5]]
    @test certified_orbit_partition(Bool[]).candidates == [[1]]
    @test certified_orbit_partition(fill(false, 3)).candidates ==
        [collect(1:4) for _ in 1:4]
    @test certified_orbit_partition(fill(true, 3)).candidates == [[1], [2], [3], [4]]

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
