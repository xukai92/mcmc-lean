function expected_mh_transition(target, proposal)
    state_count = length(target)
    totals = sum.(proposal)
    transition = fill(0 // 1, state_count, state_count)
    for current in 1:state_count
        for next in 1:state_count
            current == next && continue
            numerator = min(target[current] * proposal[current][next] * totals[next],
                target[next] * proposal[next][current] * totals[current])
            denominator = target[current] * totals[current] * totals[next]
            transition[current, next] = numerator // denominator
        end
        transition[current, current] = 1 - sum(transition[current, :])
    end
    transition
end

function enumerate_mh_transition(implementation, target, proposal; check_oracle=false)
    state_count = length(target)
    transition = fill(0 // 1, state_count, state_count)
    encoded_target = join(target, ",")
    encoded_proposal = join((join(row, ",") for row in proposal), ";")

    for current in 0:(state_count - 1)
        proposal_total = sum(proposal[current + 1])
        for proposal_draw in 0:(proposal_total - 1)
            selector = Runtime.TraceSource([proposal_draw])
            proposed = Generated.categorical_index!(selector, proposal[current + 1])
            if proposed == current
                draws = [proposal_draw]
                source = Runtime.TraceSource(draws)
                next = implementation(source, target, proposal, current)
                transition[current + 1, next + 1] += 1 // proposal_total
                if check_oracle
                    output = readchomp(`$ORACLE mh_generic $encoded_target $encoded_proposal $current $proposal_draw`)
                    @test output == "ok $next 0"
                end
                continue
            end

            proposed_total = sum(proposal[proposed + 1])
            upper = target[current + 1] * proposal[current + 1][proposed + 1] * proposed_total
            @test upper > 0
            for acceptance_draw in 0:(upper - 1)
                draws = [proposal_draw, acceptance_draw]
                source = Runtime.TraceSource(draws)
                next = implementation(source, target, proposal, current)
                transition[current + 1, next + 1] += 1 // (proposal_total * upper)
                if check_oracle
                    output = readchomp(`$ORACLE mh_generic $encoded_target $encoded_proposal $current $proposal_draw $acceptance_draw`)
                    @test output == "ok $next 0"
                end
            end
        end
    end
    transition
end

@testset "generic asymmetric finite MH" begin
    target = [1, 2, 3]
    proposal = [[1, 2, 1], [1, 1, 1], [0, 2, 1]]
    expected = expected_mh_transition(target, proposal)
    generated = enumerate_mh_transition(Generated.finite_mh_step!, target, proposal;
        check_oracle=isfile(ORACLE))
    optimized = enumerate_mh_transition(Optimized.finite_mh_step!, target, proposal)

    @test generated == expected
    @test optimized == generated
    @test all(sum(generated; dims=2) .== 1)
    target_probability = (target .// sum(target))'
    @test target_probability * generated == target_probability

    # The 1 → 3 proposal has zero reverse mass and is therefore always rejected.
    @test generated[1, 3] == 0
    @test generated[3, 1] == 0
end

@testset "generic finite MH public API" begin
    target = FiniteWeights([1, 2, 3])
    proposal = FiniteKernelWeights([[1, 2, 1], [1, 1, 1], [0, 2, 1]])
    sampler = FiniteMH(target, proposal)
    chain = sample(MersenneTwister(44), sampler, 1, 100)
    @test length(chain) == 100
    @test all(in(1:3), chain)
    @test hasmethod(sample, Tuple{AbstractRNG, FiniteMH, Integer, Integer})
    @test hasmethod(Base.step, Tuple{FiniteMH, Integer})

    @test_throws ArgumentError FiniteMH(FiniteWeights([1, 0]),
        FiniteKernelWeights([[1, 1], [1, 1]]))
    @test_throws DimensionMismatch FiniteMH(FiniteWeights([1, 2]),
        FiniteKernelWeights([[1]]))
    @test_throws DimensionMismatch FiniteKernelWeights([[1, 1], [1]])
    @test_throws ArgumentError FiniteKernelWeights([[1, 0], [0, 0]])
    @test_throws ArgumentError Base.step(MersenneTwister(1), sampler, 0)
end
