@testset "composable scoped inference" begin
    order = Symbol[]
    latent = ScopedInferenceOperator([:latent], function (_, state)
        push!(order, :pg)
        (continuous=state.continuous, latent=!state.latent)
    end)
    continuous = ScopedInferenceOperator([:continuous, :latent], function (_, state)
        push!(order, :hmc)
        (continuous=state.continuous + (state.latent ? 1 : -1),
            latent=state.latent)
    end)
    sampler = ComposableSampler([:continuous, :latent], latent, continuous)
    @test covers(sampler)
    result = step(MersenneTwister(4), sampler,
        (continuous=0, latent=false))
    @test result == (continuous=1, latent=true)
    @test order == [:pg, :hmc]

    empty!(order)
    chain = sample(MersenneTwister(5), sampler,
        (continuous=0, latent=false), 3)
    @test length(chain) == 3
    @test order == [:pg, :hmc, :pg, :hmc, :pg, :hmc]
    @test_throws ArgumentError ComposableSampler([:continuous, :latent], latent)
    @test_throws ArgumentError ScopedInferenceOperator(Symbol[], identity)
end
