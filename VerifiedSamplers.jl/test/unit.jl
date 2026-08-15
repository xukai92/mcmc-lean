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
    @test_throws ArgumentError Reference.categorical_index!(Runtime.TraceSource([0]), [1, -1])
    @test_throws ArgumentError Optimized.categorical_index!(Runtime.TraceSource([0]), [1, -1])
    @test_throws ArgumentError sample(MersenneTwister(1), FiniteWeights([1]), -1)
end

@testset "versioned reference IR" begin
    @test Reference.IR_FORMAT_VERSION == 3
    @test sort!(collect(keys(Reference.PROGRAMS))) ==
        ["categorical_index!", "finite_mh_step!", "gaussian_rwmh_step!",
            "scalar_hmc_step!"]
    @test_throws ErrorException Reference.parse_document("(unterminated")
    mktemp() do path, stream
        write(stream, "(verified-samplers-ir 2 bogus)\n")
        close(stream)
        @test_throws ErrorException Reference.load_programs(path)
    end
end
