function batch_mean_standard_error(values, batch_size)
    batch_count = length(values) ÷ batch_size
    batch_count >= 2 || throw(ArgumentError("at least two batches are required"))
    means = [sum(@view values[((i - 1) * batch_size + 1):(i * batch_size)]) / batch_size
        for i in 1:batch_count]
    std(means) / sqrt(batch_count)
end

@testset "discrete distribution diagnostics" begin
    rng = MersenneTwister(0x51a7)
    weights = [1, 2, 3]
    probabilities = weights ./ sum(weights)
    count = 60_000
    draws = sample(rng, FiniteWeights(weights), count)
    observed = [sum(==(index), draws) for index in eachindex(weights)]
    expected = count .* probabilities

    chi_squared = sum((observed .- expected) .^ 2 ./ expected)
    @test chi_squared < 20.0
    for index in eachindex(weights)
        sigma = sqrt(count * probabilities[index] * (1 - probabilities[index]))
        @test abs(observed[index] - expected[index]) <= 6 * sigma
    end
end

@testset "two-state stationary moment matching" begin
    rng = MersenneTwister(0x2a11)
    chain = sample(rng, TwoStateMH(), false, 51_000)[1001:end]
    numeric_chain = Float64.(chain)

    mean_error = mean(numeric_chain) - 0.75
    mean_se = batch_mean_standard_error(numeric_chain, 250)
    @test abs(mean_error) <= 6 * mean_se

    centered_squares = (numeric_chain .- 0.75) .^ 2
    variance_error = mean(centered_squares) - 0.1875
    variance_se = batch_mean_standard_error(centered_squares, 250)
    @test abs(variance_error) <= 6 * variance_se
end
