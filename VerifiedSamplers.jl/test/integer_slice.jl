@testset "exact finite integer slice" begin
    weights = [1, 2]
    for current in 0:1
        for height in 0:(weights[current + 1] - 1)
            candidates = findall(>(height), weights)
            for rank in 0:(length(candidates) - 1)
                events = [height, rank]
                reference_source = Runtime.TraceSource(events)
                optimized_source = Runtime.TraceSource(events)
                expected = candidates[rank + 1] - 1
                @test Reference.integer_slice_step!(reference_source,
                    weights, current) == expected
                @test Optimized.integer_slice_step!(optimized_source,
                    weights, current) == expected
                @test reference_source.requested_bounds ==
                    optimized_source.requested_bounds
                @test Runtime.remaining(reference_source) == 0
                @test Runtime.remaining(optimized_source) == 0
            end
        end
    end

    sampler = FiniteIntegerSlice(weights)
    chain = sample(MersenneTwister(908), sampler, 1, 60_000)
    frequency = count(==(2), chain) / length(chain)
    @test abs(frequency - 2 / 3) < 0.02
    @test_throws ArgumentError FiniteIntegerSlice(Int[])
    @test_throws ArgumentError FiniteIntegerSlice([1, 0])
    @test_throws ArgumentError sample(MersenneTwister(1), sampler, 0, 1)
end
