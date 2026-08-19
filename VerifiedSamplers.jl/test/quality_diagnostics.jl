@testset "shared sampling-quality diagnostics" begin
    constant_values = fill(2.0, 20)
    @test QualityDiagnostics.autocorrelation_ess(constant_values) == 0.0
    alternating = repeat([-1.0, 1.0], 20)
    @test QualityDiagnostics.autocorrelation_ess(alternating) == length(alternating)

    chain = [repeat([-1.0, 1.0], 50)'; repeat([-2.0, 2.0], 50)']
    moments = QualityDiagnostics.moment_diagnostics(
        chain, zeros(2), [1.0, 4.0])
    @test moments.means == zeros(2)
    @test moments.standardized_mean_rmse == 0.0
    @test moments.minimum_ess == 100

    target_covariance = cov(permutedims(chain))
    @test QualityDiagnostics.covariance_max_error(
        chain, target_covariance) == 0.0
    probabilities = [0.0, 0.5, 1.0]
    expected = [-1.0 0.0 1.0; -2.0 0.0 2.0]
    @test QualityDiagnostics.marginal_quantile_max_error(
        chain, probabilities, expected) == 0.0

    standard_errors = QualityDiagnostics.batch_mean_standard_error(
        chain; batches=10)
    @test length(standard_errors) == 2
    @test all(isfinite, standard_errors)
    @test_throws ArgumentError QualityDiagnostics.moment_diagnostics(
        chain, zeros(2), [1.0, 0.0])
    @test_throws DimensionMismatch QualityDiagnostics.covariance_max_error(
        chain, Matrix{Float64}(I, 3, 3))

    independent = hcat(randn(MersenneTwister(11), 400),
        randn(MersenneTwister(12), 400), randn(MersenneTwister(13), 400),
        randn(MersenneTwister(14), 400))
    rank_diagnostics = QualityDiagnostics.split_rank_diagnostics(independent)
    @test rank_diagnostics.rank_normalized_rhat < 1.05
    @test rank_diagnostics.bulk_ess > 500
    @test rank_diagnostics.tail_ess > 300
    shifted = copy(independent)
    shifted[:, 4] .+= 3
    @test QualityDiagnostics.split_rank_diagnostics(
        shifted).rank_normalized_rhat > 1.1
    @test_throws ArgumentError QualityDiagnostics.split_rank_diagnostics(
        independent[:, 1:1])
end
