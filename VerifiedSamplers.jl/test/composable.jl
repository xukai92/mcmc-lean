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

@testset "explicit observation suspend/resume" begin
    factors = [state -> state + 1, state -> 2 * state, _ -> 0.5]
    initial = observation_cursor(3, factors)
    paused = run_observations(initial, 1)
    resumed = run_observations(paused, 2)
    uninterrupted = run_observations(initial, 3)

    @test paused.accumulated_weight == 4.0
    @test resumed.accumulated_weight == uninterrupted.accumulated_weight == 12.0
    @test resumed.position == uninterrupted.position == 4
    @test resume_observation(resumed) === nothing

    clone = deepcopy(paused)
    @test run_observations(clone, 2).accumulated_weight == 12.0
    @test paused.position == 2
    @test_throws ArgumentError run_observations(initial, -1)
    @test_throws DomainError resume_observation(observation_cursor(1, [_ -> -1.0]))
end
