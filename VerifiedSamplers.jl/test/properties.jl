function exact_categorical_probabilities(implementation, weights)
    probabilities = fill(0 // 1, length(weights))
    total = sum(weights)
    for draw in 0:(total - 1)
        source = Runtime.TraceSource([draw])
        index = implementation(source, weights) + 1
        probabilities[index] += 1 // total
    end
    probabilities
end

function exact_two_state_row(implementation, current)
    probabilities = fill(0 // 1, 2)
    for proposal_draw in 0:1
        proposed = proposal_draw
        if proposed == current
            probabilities[current + 1] += 1 // 2
            continue
        end
        upper = current == 0 ? 2 : 6
        for acceptance_draw in 0:(upper - 1)
            source = Runtime.TraceSource([proposal_draw, acceptance_draw])
            next = implementation(source, current)
            probabilities[next + 1] += 1 // (2 * upper)
        end
    end
    probabilities
end

@testset "exact finite properties" begin
    reference_categorical = weights -> exact_categorical_probabilities(
        Reference.categorical_index!, weights)
    optimized_categorical = weights -> exact_categorical_probabilities(
        Optimized.categorical_index!, weights)
    @test reference_categorical([1, 0, 2]) == [1 // 3, 0 // 1, 2 // 3]
    @test reference_categorical([2, 1]) == [2 // 3, 1 // 3]
    @test optimized_categorical([1, 0, 2]) == reference_categorical([1, 0, 2])
    @test optimized_categorical([2, 1]) == reference_categorical([2, 1])

    transition = [exact_two_state_row(Reference.two_state_mh_step!, 0)';
        exact_two_state_row(Reference.two_state_mh_step!, 1)']
    optimized_transition = [exact_two_state_row(Optimized.two_state_mh_step!, 0)';
        exact_two_state_row(Optimized.two_state_mh_step!, 1)']
    target = [1 // 4, 3 // 4]
    @test transition == [1 // 2 1 // 2; 1 // 6 5 // 6]
    @test optimized_transition == transition
    @test all(sum(transition; dims=2) .== 1)

    # Direct executable detailed-balance regression. Lean proves this
    # universally for the corresponding finite-MH kernel.
    @test target[1] * transition[1, 2] == target[2] * transition[2, 1]
    @test vec(target' * transition) == target
end
