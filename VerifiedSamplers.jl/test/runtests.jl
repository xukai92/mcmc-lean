using Test
using Random
using Statistics
using VerifiedSamplers

const Runtime = VerifiedSamplers.Runtime
const Generated = VerifiedSamplers.Generated
const Optimized = VerifiedSamplers.Optimized
const REPO_ROOT = normpath(joinpath(@__DIR__, "..", ".."))
const ORACLE = joinpath(REPO_ROOT, "formal", ".lake", "build", "bin", "mcmc_oracle")

include("properties.jl")
include("geweke.jl")
include("unit.jl")
include("generic_mh.jl")
include("future_continuous.jl")

@testset "finite categorical core" begin
    for (weights, expected) in (([1, 0, 2], [0, 2, 2]), ([2, 1], [0, 0, 1]))
        for draw in 0:(sum(weights) - 1)
            source = Runtime.TraceSource([draw])
            actual = Generated.categorical_index!(source, weights)
            optimized_source = Runtime.TraceSource([draw])
            optimized = Optimized.categorical_index!(optimized_source, weights)
            @test actual == expected[draw + 1]
            @test optimized == actual
            @test Runtime.remaining(source) == 0
            @test Runtime.remaining(optimized_source) == 0
            @test source.requested_bounds == [sum(weights)]
            @test optimized_source.requested_bounds == source.requested_bounds
            if isfile(ORACLE)
                encoded = join(weights, ",")
                @test readchomp(`$ORACLE categorical $encoded $draw`) == "ok $actual"
            end
        end
    end

    @test_throws ArgumentError Generated.categorical_index!(Runtime.TraceSource([0]), [0, 0])
    @test_throws EOFError Generated.categorical_index!(Runtime.TraceSource(Int[]), [1])
    @test_throws ArgumentError Generated.categorical_index!(Runtime.TraceSource([1]), [1])
end

@testset "two-state MH exhaustive traces" begin
    cases = Tuple{Int,Vector{Int},Int}[
        (0, [0], 0),
        (0, [1, 0], 1),
        (0, [1, 1], 1),
        (1, [1], 1),
        (1, [0, 0], 0),
        (1, [0, 1], 0),
        (1, [0, 2], 1),
        (1, [0, 3], 1),
        (1, [0, 4], 1),
        (1, [0, 5], 1),
    ]

    for (current, draws, expected) in cases
        source = Runtime.TraceSource(draws)
        actual = Generated.two_state_mh_step!(source, current)
        optimized_source = Runtime.TraceSource(draws)
        optimized = Optimized.two_state_mh_step!(optimized_source, current)
        @test actual == expected
        @test optimized == actual
        @test Runtime.remaining(source) == 0
        @test Runtime.remaining(optimized_source) == 0
        @test optimized_source.requested_bounds == source.requested_bounds
        args = length(draws) == 1 ?
            `$ORACLE mh $current $(draws[1])` :
            `$ORACLE mh $current $(draws[1]) $(draws[2])`
        isfile(ORACLE) && @test readchomp(args) == "ok $expected 0"
    end
end

@testset "public multiple-dispatch API" begin
    target = FiniteWeights([1, 0, 2])
    rng = MersenneTwister(7)
    samples = sample(rng, target, 32)
    @test length(samples) == 32
    @test all(in((1, 3)), samples)
    @test hasmethod(sample, Tuple{FiniteWeights})
    @test hasmethod(sample, Tuple{AbstractRNG, FiniteWeights})

    chain = sample(MersenneTwister(9), TwoStateMH(), false, 20)
    @test length(chain) == 20
    @test eltype(chain) == Bool
    @test hasmethod(Base.step, Tuple{TwoStateMH, Bool})
    @test_throws ArgumentError FiniteWeights([0, 0])
    @test_throws ArgumentError FiniteWeights([1, -1])
end
