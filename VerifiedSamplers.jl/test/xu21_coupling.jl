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

    @test coupled_meeting_time(MersenneTwister(1), sampler,
        ([0.2, -0.1], [0.2, -0.1]), 20) == 0
    meeting = coupled_meeting_time(MersenneTwister(2022), sampler,
        ([0.0, 0.0], [1.0, -1.0]), 2_000)
    @test meeting !== nothing
    @test meeting == coupled_meeting_time(MersenneTwister(2022), sampler,
        ([0.0, 0.0], [1.0, -1.0]), 2_000)
    @test_throws ArgumentError coupled_meeting_time(MersenneTwister(1), sampler,
        ([0.0], [1.0]), -1)

    diagnostic = coupled_meeting_diagnostic(MersenneTwister(2021), sampler,
        ([0.0, 0.0], [1.0, -1.0]), 12, 500)
    repeated = coupled_meeting_diagnostic(MersenneTwister(2021), sampler,
        ([0.0, 0.0], [1.0, -1.0]), 12, 500)
    @test diagnostic == repeated
    @test diagnostic.met + diagnostic.censored == 12
    @test diagnostic.meeting_fraction == diagnostic.met / 12
    @test 0 <= diagnostic.restricted_mean <= 500
    @test all(time -> time === nothing || 0 <= time <= 500,
        diagnostic.meeting_times)

    already_met = coupled_meeting_diagnostic(MersenneTwister(3), sampler,
        ([0.25, -0.5], [0.25, -0.5]), 4, 0)
    @test already_met.meeting_times == Union{Nothing,Int}[0, 0, 0, 0]
    @test already_met.observed_mean == 0
    @test already_met.restricted_mean == 0
    @test_throws ArgumentError coupled_meeting_diagnostic(MersenneTwister(1),
        sampler, ([0.0], [1.0]), 0, 10)
    @test_throws ArgumentError coupled_meeting_diagnostic(MersenneTwister(1),
        sampler, ([0.0], [1.0]), 1, -1)

    @test_throws DimensionMismatch step(MersenneTwister(1), sampler,
        ([0.0], [0.0, 1.0]))
end
