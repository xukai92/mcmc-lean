@testset "parallel integrator foundations" begin
    segments = [(2.0, 1.0), (3.0, -2.0), (0.5, 4.0), (-1.0, 3.0)]
    expected = Reference.affine_prefix_scan(segments)
    @test Optimized.affine_prefix_scan(segments; parallel=false) == expected
    @test Optimized.affine_prefix_scan(segments; parallel=true) == expected
    for index in eachindex(segments)
        serial = foldl((x, map) -> map[1] * x + map[2], segments[1:index]; init=0.7)
        @test expected[index][1] * 0.7 + expected[index][2] ≈ serial
    end

    step(x) = x + 1
    @test Reference.certified_trajectory(step, 0, [1, 2, 3]) == (3, true)
    @test Reference.certified_trajectory(step, 0, [1, 9, 10]) == (3, false)
    @test Optimized.certified_trajectory(step, 0, [1, 9, 10]) == (3, false)
    @test Reference.certified_speculative_trajectory(step, 0, 8, 8) == (8, true)
    @test Reference.certified_speculative_trajectory(step, 0, 8, 2) == (8, false)
    @test Optimized.certified_speculative_trajectory(
        step, 0, 8, 8; parallel=false) == (8, true)
    @test Optimized.certified_speculative_trajectory(
        step, 0, 8, 2; parallel=true) == (8, false)

    logdensity(q) = -sum(abs2, q) / 2
    gradient(q) = q
    reference = Reference.vector_gauss_legendre_hmc_step!(
        Runtime.RNGSource(MersenneTwister(91)), logdensity, gradient,
        0.08, 3, 10, zeros(4))
    optimized = Optimized.vector_gauss_legendre_hmc_step!(
        Runtime.RNGSource(MersenneTwister(91)), logdensity, gradient,
        0.08, 3, 10, zeros(4); parallel=false)
    @test reference == optimized

    function batched_gradient!(output, positions)
        @inbounds @simd for index in axes(positions, 1)
            output[index, 1] = positions[index, 1]
            output[index, 2] = positions[index, 2]
        end
        output
    end
    simd = Optimized.vector_gauss_legendre_hmc_step!(
        Runtime.RNGSource(MersenneTwister(91)), logdensity, gradient,
        0.08, 3, 10, zeros(4); batched_gradient!)
    @test simd == optimized
    quartic_gradient(q) = map(x -> x^3 + x, q)
    function batched_quartic_gradient!(output, positions)
        @inbounds @simd for index in eachindex(positions)
            x = positions[index]
            output[index] = x^3 + x
        end
        output
    end
    serial_q, serial_p = Optimized.vector_gauss_legendre_step(
        quartic_gradient, 0.03, 8, fill(0.2, 4), fill(-0.1, 4))
    simd_q, simd_p = Optimized.vector_gauss_legendre_simd_step(
        batched_quartic_gradient!, 0.03, 8, fill(0.2, 4), fill(-0.1, 4))
    @test simd_q ≈ serial_q atol=1e-14
    @test simd_p ≈ serial_p atol=1e-14

    q0, p0 = randn(4), randn(4)
    q1, p1 = Optimized.vector_gauss_legendre_step(
        gradient, 0.05, 16, q0, p0; parallel=false)
    q2, p2 = Optimized.vector_gauss_legendre_step(
        gradient, -0.05, 16, q1, p1; parallel=false)
    @test q2 ≈ q0 atol=1e-12
    @test p2 ≈ p0 atol=1e-12

    q32 = zeros(Float32, 3)
    p32 = ones(Float32, 3)
    qnext, pnext = Optimized.vector_gauss_legendre_step(
        identity, Float32(0.01), 3, q32, p32; parallel=false)
    @test eltype(qnext) == Float32
    @test eltype(pnext) == Float32

    reference_sampler = GaussLegendreHMC(
        logdensity, gradient, 0.05, 2; stage_iterations=6)
    optimized_sampler = GaussLegendreHMC(
        logdensity, gradient, Float32(0.05), 2;
        stage_iterations=6, backend=:optimized)
    @test size(sample(MersenneTwister(7), reference_sampler, zeros(4), 3)) == (4, 3)
    optimized_samples = sample(
        MersenneTwister(7), optimized_sampler, zeros(Float32, 4), 3)
    @test size(optimized_samples) == (4, 3)
    @test eltype(optimized_samples) == Float32
    simd_sampler = GaussLegendreHMC(
        logdensity, gradient, 0.05f0, 2; stage_iterations=6,
        backend=:optimized, batched_gradient!)
    @test eltype(sample(MersenneTwister(7), simd_sampler,
        zeros(Float32, 4), 3)) == Float32
    @test_throws ArgumentError GaussLegendreHMC(
        logdensity, gradient, Float32(0.05); backend=:reference)
end
