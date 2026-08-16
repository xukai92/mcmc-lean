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
end
