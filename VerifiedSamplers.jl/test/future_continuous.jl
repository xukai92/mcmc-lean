# These named testsets make the intended continuous/HMC validation surface
# visible without implying that the corresponding samplers exist yet.

@testset "future: integrator properties" begin
    @testset "energy conservation" begin
        @test_skip false
    end
    @testset "time reversibility" begin
        @test_skip false
    end
    @testset "volume or measure preservation" begin
        @test_skip false
    end
end

@testset "future: continuous and mixed-state diagnostics" begin
    @testset "Geweke forward/backward joint-distribution test" begin
        @test_skip false
    end
    @testset "continuous normal-target moment matching" begin
        @test_skip false
    end
    @testset "DHMC categorical target" begin
        @test_skip false
    end
    @testset "momentum and kinetic-energy units" begin
        @test_skip false
    end
end

@testset "future: robustness and performance" begin
    @testset "zero momentum and nonsmooth boundaries" begin
        @test_skip false
    end
    @testset "high-dimensional and ill-conditioned targets" begin
        @test_skip false
    end
    @testset "multimodal discrete targets" begin
        @test_skip false
    end
    @testset "adaptation correctness" begin
        @test_skip false
    end
    @testset "ESS and gradient-count benchmarks" begin
        @test_skip false
    end
end
