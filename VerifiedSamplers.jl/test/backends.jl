@testset "backend capability contract" begin
    registry = Backends.backend_registry()
    @test getproperty.(registry, :name) ==
        (:reference, :optimized, :parallel_cpu, :host_batch,
            :broadcast_accelerator)
    @test all(backend -> Backends.supports(backend, :scalar), registry)
    @test all(backend -> Backends.supports(backend, :deterministic_trace), registry)
    @test count(backend -> Backends.supports(backend, :accelerator), registry) == 1
    @test !Backends.supports(first(registry), :unknown)
    @test Backends.require_capability(first(registry), :vector) === first(registry)
    @test_throws ArgumentError Backends.require_capability(
        first(registry), :independent_chains)
end

@testset "broadcast RWMH matches Reference events" begin
    current = [-1.0, 0.0, 2.0, 0.5]
    noise = [0.25, -1.0, 0.5, 2.0]
    uniform = [0.1, 0.9, 0.2, 0.999]
    scale = 0.4
    logdensity = x -> -x^2 / 2
    batched = Backends.gaussian_rwmh_batch(
        current, noise, uniform, logdensity, scale)
    scalar = map(eachindex(current)) do index
        source = Runtime.FloatTraceSource(Runtime.FloatTraceEvent[
            Runtime.NormalEvent(noise[index]),
            Runtime.UniformEvent(uniform[index]),
        ])
        Reference.gaussian_rwmh_step!(source, logdensity, scale, current[index])
    end
    @test batched == scalar
    @test Backends.BROADCAST_ACCELERATOR_BACKEND.evidence == Backends.Tested
    @test Backends.supported_operations(Backends.BROADCAST_ACCELERATOR) ==
        Set([:gaussian_rwmh])
    @test_throws DimensionMismatch Backends.gaussian_rwmh_batch(
        current, noise[1:2], uniform, logdensity, scale)
    @test_throws ArgumentError Backends.gaussian_rwmh_batch(
        current, noise, [uniform[1:3]; 1.0], logdensity, scale)
end

@testset "exact integer replay compares draw bounds" begin
    comparison = Evaluation.replay_integer_pair([2],
        source -> Reference.categorical_index!(source, [1, 2, 1]),
        source -> Optimized.categorical_index!(source, [1, 2, 1]))
    @test Evaluation.conforms(comparison)
    @test comparison.reference_evidence == [4]

    mismatched = Evaluation.replay_integer_pair([0],
        source -> Runtime.draw_below!(source, 2),
        source -> Runtime.draw_below!(source, 3))
    @test !Evaluation.conforms(mismatched)
end

@testset "batched backend protocol" begin
    seeds = [4, 9, 16]
    states = [1.0, 2.0, 3.0]
    transition = (rng, state) -> state + rand(rng)
    host = Backends.HostBatchBackend()
    expected = [transition(MersenneTwister(seed), state)
        for (seed, state) in zip(seeds, states)]
    @test Backends.step_batch(host, :scalar_transition,
        seeds, states, transition) == expected
    @test Backends.supported_operations(host) ==
        Set([:scalar_transition, :vector_transition])
    @test_throws ArgumentError Backends.step_batch(host, :nuts_tree,
        seeds, states, transition)
    @test_throws DimensionMismatch Backends.step_batch(host,
        :scalar_transition, seeds[1:2], states, transition)

    launcher = (operation, launch_seeds, launch_states, step) ->
        [step(MersenneTwister(seed), state)
            for (seed, state) in zip(launch_seeds, launch_states)]
    adapter = Backends.AcceleratorBatchBackend(:test_accelerator,
        [:scalar_transition], launcher; note="test adapter")
    @test Backends.supports(Backends.descriptor(adapter), :accelerator)
    @test Backends.descriptor(adapter).evidence ==
        Backends.DocumentedBoundary
    @test Backends.step_batch(adapter, :scalar_transition,
        seeds, states, transition) == expected
    @test_throws ArgumentError Backends.step_batch(adapter,
        :vector_transition, seeds, states, transition)
end

@testset "optimization acceptance records" begin
    gates = [
        Evaluation.GateResult(:tests, true, "Pkg.test"),
        Evaluation.GateResult(:trace, true, "deterministic replay"),
    ]
    accepted_trial = Evaluation.OptimizationTrial("phase-copy", "test-supported",
        1.2, 1.0, 1.1, gates)
    @test Evaluation.accepted(accepted_trial)
    @test occursin("accepted=true", Evaluation.render_record(accepted_trial))
    failed_trial = Evaluation.OptimizationTrial("unsafe", "empirical-only",
        1.2, 0.5, 1.1,
        [gates; Evaluation.GateResult(:property, false, "reversibility")])
    @test !Evaluation.accepted(failed_trial)
    @test_throws ArgumentError Evaluation.OptimizationTrial(
        "ungated", "unknown", 1.0, 0.5, 1.0, Evaluation.GateResult[])
end

@testset "explicit-seed independent chains" begin
    seeds = [91, 17, 44, 3]
    run_chain = (rng, index) -> (index, rand(rng, UInt64, 4))
    parallel = Backends.run_chains(seeds, run_chain)
    sequential = [run_chain(MersenneTwister(seed), index)
        for (index, seed) in enumerate(seeds)]
    @test parallel == sequential
    @test_throws ArgumentError Backends.run_chains(Int[], run_chain)
    @test_throws ArgumentError Backends.run_chains(seeds, run_chain;
        backend=Backends.REFERENCE_BACKEND)
end

@testset "replay records matching failures" begin
    events = Runtime.FloatTraceEvent[Runtime.UniformEvent(0.25)]
    comparison = Evaluation.replay_pair(events,
        source -> begin
            Runtime.uniform_unit!(source)
            throw(DomainError(:same, "failure"))
        end,
        source -> begin
            Runtime.uniform_unit!(source)
            throw(DomainError(:same, "failure"))
        end)
    @test Evaluation.conforms(comparison)
end
