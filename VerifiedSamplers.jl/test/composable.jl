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

    generated_order = Symbol[]
    generated = generated_schedule("ge-pg-hmc", Dict(
        "particle-gibbs" => ((_, state) -> begin
            push!(generated_order, :pg)
            merge(state, (latent=!state.latent,))
        end),
        "hamiltonian-monte-carlo" => ((_, state) -> begin
            push!(generated_order, :hmc)
            merge(state, (continuous=state.continuous + 2,))
        end)))
    @test generated.variables == [:latent, :continuous]
    @test [operator.scope for operator in generated.operators] ==
        [[:latent], [:continuous]]
    @test step(MersenneTwister(6), generated,
        (continuous=0, latent=false)) == (continuous=2, latent=true)
    @test generated_order == [:pg, :hmc]
    @test_throws ArgumentError generated_schedule("unknown", Dict())
    @test_throws ArgumentError generated_schedule("ge-pg-hmc", Dict())
end
