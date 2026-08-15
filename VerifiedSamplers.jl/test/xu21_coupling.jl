@testset "Xu et al. executable coupling" begin
    logdensity(q) = -sum(abs2, q) / 2
    gradient(q) = q
    sampler = Xu21CoupledSampler(logdensity, gradient, 0.15, 3, 0.6, 0.8)

    result = sample(MersenneTwister(2021), sampler, ([0.0, 0.0], [1.0, -1.0]), 64)
    @test size(result.left) == (2, 64)
    @test size(result.right) == (2, 64)
    @test length(result.met) == 64
    @test all(isfinite, result.left)
    @test all(isfinite, result.right)

    # The generated coupling is faithful after exact meeting.
    left, right = [0.25, -0.5], [0.25, -0.5]
    rng = MersenneTwister(7)
    for _ in 1:50
        left, right = step(rng, sampler, (left, right))
        @test left == right
    end

    @test_throws DimensionMismatch step(MersenneTwister(1), sampler,
        ([0.0], [0.0, 1.0]))
end
