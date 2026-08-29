using LinearAlgebra
using Random
using Statistics
using VerifiedSamplers

const GROUPS = parse(Int, get(ENV, "HIERARCHICAL_LOGISTIC_GROUPS", "10"))
const FEATURES = parse(Int, get(ENV, "HIERARCHICAL_LOGISTIC_FEATURES", "4"))
const OBSERVATIONS = parse(Int,
    get(ENV, "HIERARCHICAL_LOGISTIC_OBSERVATIONS", "400"))
const DIMENSION = FEATURES + GROUPS + 1
const CHAINS = 4
const WARMUP = parse(Int, get(ENV, "HIERARCHICAL_LOGISTIC_WARMUP", "1000"))
const DRAWS = parse(Int, get(ENV, "HIERARCHICAL_LOGISTIC_DRAWS", "2000"))
const STEPS = 20
const SKETCH_STEPS = parse(Int,
    get(ENV, "HIERARCHICAL_LOGISTIC_SKETCH_STEPS", "5"))
const SKETCH_SOLVER_ITERATIONS = parse(Int,
    get(ENV, "HIERARCHICAL_LOGISTIC_SKETCH_SOLVER_ITERATIONS", "25"))
const WARMUP_STEP_SIZE = 0.015
const STEP_SIZES = Tuple(parse.(Float64, split(get(ENV,
    "HIERARCHICAL_LOGISTIC_STEP_SIZES", "0.008,0.015,0.025,0.04"), ',')))
const SEEDS = (31_001, 31_002, 31_003, 31_004)
const ALL_METHODS = (:hmc, :dense_hmc, :rank1_transport_hmc,
    :rank2_transport_hmc, :rank4_transport_hmc, :rank8_transport_hmc,
    :rank10_transport_hmc, :rank14_transport_hmc, :rank20_transport_hmc,
    :joint_rank2_transport_hmc, :random_sketch_rmhmc)
const METHODS = Tuple(Symbol.(split(get(ENV, "HIERARCHICAL_LOGISTIC_METHODS",
    join(string.(ALL_METHODS), ',')), ',')))

softplus(x) = max(x, zero(x)) + log1p(exp(-abs(x)))
sigmoid(x) = x >= 0 ? inv(1 + exp(-x)) : exp(x) / (1 + exp(x))

function make_data()
    rng = MersenneTwister(29_911)
    design = randn(rng, OBSERVATIONS, FEATURES)
    groups = rand(rng, 1:GROUPS, OBSERVATIONS)
    true_beta = [(-1)^index * (0.3 + 0.8 / index)
        for index in 1:FEATURES]
    true_effects = 0.7 .* randn(rng, GROUPS)
    probability = sigmoid.(design * true_beta .+ true_effects[groups])
    response = Float64.(rand(rng, OBSERVATIONS) .< probability)
    design, groups, response
end

const DESIGN, GROUP, RESPONSE = make_data()

function potential(q)
    beta = @view q[1:FEATURES]
    effects = @view q[(FEATURES + 1):(FEATURES + GROUPS)]
    log_scale = q[end]
    inverse_variance = exp(-2log_scale)
    value = sum(abs2, beta) / 8 + log_scale^2 / 2 +
        sum(abs2, effects) * inverse_variance / 2 + GROUPS * log_scale
    @inbounds for observation in 1:OBSERVATIONS
        linear = dot(@view(DESIGN[observation, :]), beta) +
            effects[GROUP[observation]]
        value += softplus(linear) - RESPONSE[observation] * linear
    end
    value
end

function potential_gradient(q)
    beta = @view q[1:FEATURES]
    effects = @view q[(FEATURES + 1):(FEATURES + GROUPS)]
    log_scale = q[end]
    inverse_variance = exp(-2log_scale)
    result = zeros(eltype(q), DIMENSION)
    result[1:FEATURES] .= beta ./ 4
    result[(FEATURES + 1):(FEATURES + GROUPS)] .=
        effects .* inverse_variance
    @inbounds for observation in 1:OBSERVATIONS
        group = GROUP[observation]
        linear = dot(@view(DESIGN[observation, :]), beta) + effects[group]
        residual = sigmoid(linear) - RESPONSE[observation]
        for feature in 1:FEATURES
            result[feature] += residual * DESIGN[observation, feature]
        end
        result[FEATURES + group] += residual
    end
    result[end] = log_scale + GROUPS - sum(abs2, effects) * inverse_variance
    result
end

logdensity(q) = -potential(q)

function curvature_action(q, probe)
    effects = @view q[(FEATURES + 1):(FEATURES + GROUPS)]
    inverse_scale = exp(-q[end])
    result = copy(probe)
    result[(FEATURES + 1):(FEATURES + GROUPS)] .=
        inverse_scale .* @view(probe[(FEATURES + 1):(FEATURES + GROUPS)])
    result[end] = probe[end] - inverse_scale * dot(effects,
        @view(probe[(FEATURES + 1):(FEATURES + GROUPS)]))
    result
end

function curvature_action_derivative(q, probe)
    effects = @view q[(FEATURES + 1):(FEATURES + GROUPS)]
    inverse_scale = exp(-q[end])
    derivative = zeros(eltype(q), DIMENSION, DIMENSION)
    @inbounds for group in 1:GROUPS
        index = FEATURES + group
        derivative[index, end] = -inverse_scale * probe[index]
        derivative[end, index] = -inverse_scale * probe[index]
    end
    derivative[end, end] = inverse_scale * dot(effects,
        @view(probe[(FEATURES + 1):(FEATURES + GROUPS)]))
    derivative
end

function warmup(method)
    sampler = VectorHMC(logdensity, potential_gradient, WARMUP_STEP_SIZE, STEPS)
    states = Matrix{Float64}(undef, DIMENSION, CHAINS * WARMUP)
    endpoints = Vector{Vector{Float64}}(undef, CHAINS)
    rngs = Vector{MersenneTwister}(undef, CHAINS)
    elapsed = 0.0
    offset = findfirst(==(method), ALL_METHODS)
    for chain in 1:CHAINS
        rng = MersenneTwister(SEEDS[chain] + 100_000offset)
        trial = @timed sample(rng, sampler, zeros(DIMENSION), WARMUP)
        range = ((chain - 1) * WARMUP + 1):(chain * WARMUP)
        states[:, range] = trial.value
        endpoints[chain] = copy(@view trial.value[:, end])
        rngs[chain] = deepcopy(rng)
        elapsed += trial.time
    end
    (; states, endpoints, rngs, elapsed)
end

function fit_sequential_transport(training, rank)
    residual = copy(training)
    maps = RankOnePolynomialTransport[]
    for _ in 1:rank
        map = fit_rank_one_polynomial_transport(residual)
        push!(maps, map)
        for index in axes(residual, 2)
            residual[:, index] = transport_inverse(map, @view residual[:, index])
        end
    end
    maps
end

function fit_joint_rank2_transport(training; ridge=1e-6)
    d, n = size(training)
    mean = vec(sum(training; dims=2)) / n
    centered = training .- mean
    covariance = Symmetric(centered * centered' / n)
    decomposition = eigen(covariance)
    output = Matrix(decomposition.vectors[:, (end - 1):end])
    output_coordinates = output' * centered
    projector = Matrix{Float64}(I, d, d) - output * output'
    score = zeros(d, d)
    for component in 1:2
        moment = zeros(d, d)
        for index in axes(centered, 2)
            x = @view centered[:, index]
            moment .+= output_coordinates[component, index] .* (x * x')
        end
        moment ./= n
        projected = projector * moment * projector
        score .+= projected * projected
    end
    active_decomposition = eigen(Symmetric(score))
    input = Matrix(active_decomposition.vectors[:, (end - 1):end])
    active = input' * centered
    input_factor = Matrix(cholesky(Symmetric(active * active' / n +
        ridge * I)).L)
    design = hcat(ones(n), vec(active[1, :]), vec(active[2, :]),
        vec(active[1, :] .^ 2), vec(active[1, :] .* active[2, :]),
        vec(active[2, :] .^ 2))
    coefficients = (design' * design + ridge * I) \
        (design' * Matrix(output_coordinates'))
    residual = output_coordinates - Matrix((design * coefficients)')
    residual_factor = Matrix(cholesky(Symmetric(residual * residual' / n +
        ridge * I)).L)
    (; mean, input, output, input_factor, residual_factor, coefficients)
end

joint_features(a) = [1.0, a[1], a[2], a[1]^2, a[1] * a[2], a[2]^2]

function joint_feature_derivative(a)
    [0.0 0.0; 1.0 0.0; 0.0 1.0; 2a[1] 0.0;
        a[2] a[1]; 0.0 2a[2]]
end

function joint_rank2_callbacks(map)
    forward = function(latent)
        latent_input = map.input' * latent
        latent_output = map.output' * latent
        active = map.input_factor * latent_input
        output_coordinate = map.coefficients' * joint_features(active) +
            map.residual_factor * latent_output
        complement = latent - map.input * latent_input -
            map.output * latent_output
        map.mean + complement + map.input * active +
            map.output * output_coordinate
    end
    inverse = function(position)
        centered = position - map.mean
        active = map.input' * centered
        output_coordinate = map.output' * centered
        complement = centered - map.input * active -
            map.output * output_coordinate
        latent_input = map.input_factor \ active
        latent_output = map.residual_factor \
            (output_coordinate - map.coefficients' * joint_features(active))
        complement + map.input * latent_input + map.output * latent_output
    end
    pullback = function(latent, cotangent)
        latent_input = map.input' * latent
        active = map.input_factor * latent_input
        input_value = map.input' * cotangent
        output_value = map.output' * cotangent
        complement = cotangent - map.input * input_value -
            map.output * output_value
        derivative = map.coefficients' * joint_feature_derivative(active)
        transformed_input = map.input_factor' *
            (input_value + derivative' * output_value)
        transformed_output = map.residual_factor' * output_value
        complement + map.input * transformed_input +
            map.output * transformed_output
    end
    logdet_value = LinearAlgebra.logdet(map.input_factor) +
        LinearAlgebra.logdet(map.residual_factor)
    forward, inverse, pullback, z -> logdet_value,
        z -> zeros(eltype(z), length(z))
end

function composed_forward(maps, latent)
    value = collect(latent)
    for index in reverse(eachindex(maps))
        value = transport_forward(maps[index], value)
    end
    value
end

function composed_inverse(maps, position)
    value = collect(position)
    for map in maps
        value = transport_inverse(map, value)
    end
    value
end


function composed_pullback(maps, latent, cotangent)
    inputs = Vector{Vector{eltype(latent)}}(undef, length(maps))
    value = collect(latent)
    for index in reverse(eachindex(maps))
        inputs[index] = value
        value = transport_forward(maps[index], value)
    end
    result = collect(cotangent)
    for index in eachindex(maps)
        result = transport_pullback(maps[index], inputs[index], result)
    end
    result
end

function map_forward!(destination, map, latent)
    latent_input = dot(map.input_direction, latent)
    latent_output = dot(map.output_direction, latent)
    active = map.input_scale * latent_input
    output = map.intercept + map.linear * active + map.quadratic * active^2 +
        map.residual_scale * latent_output
    @inbounds for index in eachindex(destination)
        destination[index] = map.mean[index] + latent[index] +
            map.input_direction[index] * (active - latent_input) +
            map.output_direction[index] * (output - latent_output)
    end
    destination
end

function map_inverse!(destination, map, position)
    centered_input = zero(eltype(position))
    centered_output = zero(eltype(position))
    @inbounds for index in eachindex(position)
        centered = position[index] - map.mean[index]
        centered_input += map.input_direction[index] * centered
        centered_output += map.output_direction[index] * centered
    end
    latent_input = centered_input / map.input_scale
    polynomial = map.intercept + map.linear * centered_input +
        map.quadratic * centered_input^2
    latent_output = (centered_output - polynomial) / map.residual_scale
    @inbounds for index in eachindex(destination)
        centered = position[index] - map.mean[index]
        destination[index] = centered + map.input_direction[index] *
            (latent_input - centered_input) + map.output_direction[index] *
            (latent_output - centered_output)
    end
    destination
end


function map_pullback!(destination, map, latent, cotangent)
    latent_input = dot(map.input_direction, latent)
    input_value = dot(map.input_direction, cotangent)
    output_value = dot(map.output_direction, cotangent)
    derivative = map.linear + 2map.quadratic * map.input_scale * latent_input
    transformed_input = map.input_scale *
        (input_value + derivative * output_value)
    transformed_output = map.residual_scale * output_value
    @inbounds for index in eachindex(destination)
        destination[index] = cotangent[index] + map.input_direction[index] *
            (transformed_input - input_value) + map.output_direction[index] *
            (transformed_output - output_value)
    end
    destination
end

function optimized_composed_callbacks(maps)
    d, rank = length(first(maps).mean), length(maps)
    forward_a, forward_b = zeros(d), zeros(d)
    inverse_a, inverse_b = zeros(d), zeros(d)
    pull_a, pull_b = zeros(d), zeros(d)
    inputs = zeros(d, rank)

    forward = function(latent)
        source, destination = latent, forward_a
        for index in reverse(eachindex(maps))
            map_forward!(destination, maps[index], source)
            source, destination = destination,
                destination === forward_a ? forward_b : forward_a
        end
        source
    end
    inverse = function(position)
        source, destination = position, inverse_a
        for map in maps
            map_inverse!(destination, map, source)
            source, destination = destination,
                destination === inverse_a ? inverse_b : inverse_a
        end
        source
    end
    pullback = function(latent, cotangent)
        source, destination = latent, pull_a
        for index in reverse(eachindex(maps))
            inputs[:, index] .= source
            map_forward!(destination, maps[index], source)
            source, destination = destination,
                destination === pull_a ? pull_b : pull_a
        end
        source, destination = cotangent, pull_a
        for index in eachindex(maps)
            map_pullback!(destination, maps[index], @view(inputs[:, index]), source)
            source, destination = destination,
                destination === pull_a ? pull_b : pull_a
        end
        source
    end
    logdet = sum(map -> log(map.input_scale) + log(map.residual_scale), maps)
    zero_logdet_gradient = zeros(d)
    forward, inverse, pullback, z -> logdet, z -> zero_logdet_gradient
end

function sampler_for(method, step_size, training)
    if method === :hmc
        return (; kind=:hmc, step_size), 0.0
    elseif method === :dense_hmc
        covariance = cov(training; dims=2)
        precision = inv(Symmetric(covariance + 1e-5I))
        metric = VerifiedSamplers.Optimized.prepare_metric(Matrix(precision))
        return (; kind=:dense_hmc, step_size, metric), 0.0
    end
    if method === :random_sketch_rmhmc
        probe_count = max(1, ceil(Int, log2(DIMENSION)))
        probe_rng = MersenneTwister(77_049)
        probes = randn(probe_rng, DIMENSION, probe_count)
        probes ./= sqrt(DIMENSION)
        q = collect(@view training[:, 1])
        probe = @view probes[:, 1]
        analytic = curvature_action_derivative(q, probe)
        finite_difference = similar(analytic)
        h = 1e-6
        for coordinate in eachindex(q)
            plus, minus = copy(q), copy(q)
            plus[coordinate] += h
            minus[coordinate] -= h
            finite_difference[:, coordinate] =
                (curvature_action(plus, probe) -
                    curvature_action(minus, probe)) / (2h)
        end
        @assert analytic ≈ finite_difference atol=2e-5 rtol=2e-5
        return RandomSketchRMHMC(potential, potential_gradient,
            curvature_action, curvature_action_derivative, probes, 0.1,
            step_size, SKETCH_STEPS; solver_iterations=SKETCH_SOLVER_ITERATIONS,
            solver_tolerance=1e-8, residual_tolerance=1e-5,
            implementation=:optimized), 0.0
    end
    if method === :joint_rank2_transport_hmc
        fit = @timed fit_joint_rank2_transport(training)
        forward, inverse, pullback, logabsdetjac, grad_logabsdetjac =
            joint_rank2_callbacks(fit.value)
        probe = collect(@view training[:, 1])
        latent_probe = inverse(probe)
        @assert forward(latent_probe) ≈ probe atol=1e-9
        cotangent_probe = potential_gradient(probe)
        pulled = pullback(latent_probe, cotangent_probe)
        finite_difference = similar(pulled)
        h = 1e-6
        for index in eachindex(latent_probe)
            plus, minus = copy(latent_probe), copy(latent_probe)
            plus[index] += h
            minus[index] -= h
            finite_difference[index] =
                (dot(cotangent_probe, forward(plus)) -
                    dot(cotangent_probe, forward(minus))) / (2h)
        end
        @assert pulled ≈ finite_difference atol=1e-5 rtol=1e-5
        sampler = TransportHMC(logdensity, potential_gradient, forward,
            inverse, pullback, logabsdetjac, grad_logabsdetjac,
            step_size, STEPS; implementation=:optimized)
        return sampler, fit.time
    end
    rank_match = match(r"^rank(\d+)_transport_hmc$", String(method))
    isnothing(rank_match) && error("unknown transport method $method")
    rank = parse(Int, only(rank_match.captures))
    fit = @timed fit_sequential_transport(training, rank)
    maps = fit.value
    forward, inverse, pullback, logabsdetjac, grad_logabsdetjac =
        optimized_composed_callbacks(maps)
    probe = collect(@view training[:, 1])
    latent_probe = composed_inverse(maps, probe)
    cotangent_probe = potential_gradient(probe)
    @assert forward(latent_probe) ≈ composed_forward(maps, latent_probe)
    @assert inverse(probe) ≈ latent_probe
    @assert pullback(latent_probe, cotangent_probe) ≈
        composed_pullback(maps, latent_probe, cotangent_probe)
    sampler = TransportHMC(logdensity, potential_gradient,
        forward, inverse, pullback, logabsdetjac, grad_logabsdetjac,
        step_size, STEPS;
        implementation=:optimized)
    sampler, fit.time
end

function draw(rng, configured::NamedTuple, initial, count)
    source = VerifiedSamplers.Runtime.RNGSource(rng)
    current = copy(initial)
    draws = Matrix{Float64}(undef, DIMENSION, count)
    for index in axes(draws, 2)
        current = configured.kind === :hmc ?
            VerifiedSamplers.Optimized.vector_hmc_step!(source, logdensity,
                potential_gradient, configured.step_size, STEPS, current) :
            VerifiedSamplers.Optimized.metric_hmc_step!(source, logdensity,
                potential_gradient, configured.step_size, STEPS, current,
                configured.metric)
        draws[:, index] = current
    end
    draws
end

draw(rng, configured::TransportHMC, initial, count) =
    sample(rng, configured, initial, count)

draw(rng, configured::RandomSketchRMHMC, initial, count) =
    sample(rng, configured, initial, count)

function diagnostics(chains)
    coordinate_results = [VerifiedSamplers.Evaluation.split_rank_diagnostics(
        hcat([vec(@view chain[coordinate, :]) for chain in chains]...))
        for coordinate in 1:DIMENSION]
    bulk = minimum(value.bulk_ess for value in coordinate_results)
    tail = minimum(value.tail_ess for value in coordinate_results)
    rhat = maximum(value.rank_normalized_rhat for value in coordinate_results)
    bulk, tail, rhat
end

function transport_log_score(maps, samples)
    logdet_value = sum(map ->
        log(map.input_scale) + log(map.residual_scale), maps)
    total = 0.0
    for sample in eachcol(samples)
        latent = composed_inverse(maps, sample)
        total += -sum(abs2, latent) / 2 - logdet_value
    end
    total / size(samples, 2)
end

function write_rank_fitness()
    warmed = warmup(:rank8_transport_hmc)
    training_count = (CHAINS - 1) * WARMUP
    training = @view warmed.states[:, 1:training_count]
    validation = @view warmed.states[:, (training_count + 1):end]
    maximum_rank = parse(Int, get(ENV,
        "HIERARCHICAL_LOGISTIC_MAX_RANK", "12"))
    path = joinpath(@__DIR__, "results", get(ENV,
        "HIERARCHICAL_LOGISTIC_OUTPUT", "hierarchical-logistic-rank-fitness.csv"))
    open(path, "w") do io
        println(io, "rank,training_log_score,validation_log_score,validation_gain")
        previous = NaN
        residual = copy(training)
        maps = RankOnePolynomialTransport[]
        for rank in 1:maximum_rank
            map = fit_rank_one_polynomial_transport(residual)
            push!(maps, map)
            for index in axes(residual, 2)
                residual[:, index] = transport_inverse(map, @view residual[:, index])
            end
            training_score = transport_log_score(maps, training)
            validation_score = transport_log_score(maps, validation)
            gain = rank == 1 ? NaN : validation_score - previous
            println(io, join((rank, training_score, validation_score, gain), ','))
            println("rank=$rank validation score=$(round(validation_score; digits=4)) " *
                "gain=$(round(gain; digits=4))")
            previous = validation_score
        end
    end
    println("wrote $path")
end

const RANK_FITNESS = lowercase(get(ENV,
    "HIERARCHICAL_LOGISTIC_RANK_FITNESS", "false")) in ("1", "true", "yes")

if RANK_FITNESS
    write_rank_fitness()
else
rows = NamedTuple[]
for method in METHODS
    println("warming $method")
    warmed = warmup(method)
    for step_size in STEP_SIZES
        configured, fit_seconds = sampler_for(method, step_size, warmed.states)
        chains = Matrix{Float64}[]
        sampling_seconds = 0.0
        for chain in 1:CHAINS
            trial = @timed draw(deepcopy(warmed.rngs[chain]), configured,
                warmed.endpoints[chain], DRAWS)
            push!(chains, trial.value)
            sampling_seconds += trial.time
        end
        bulk, tail, rhat = diagnostics(chains)
        transitions = CHAINS * DRAWS
        effective_steps = method === :random_sketch_rmhmc ? SKETCH_STEPS : STEPS
        gradients = transitions * 2effective_steps
        total_seconds = warmed.elapsed + fit_seconds + sampling_seconds
        push!(rows, (; method, step_size, steps=effective_steps,
            warmup_seconds=warmed.elapsed, fit_seconds, sampling_seconds,
            bulk_ess=bulk, tail_ess=tail, rhat,
            bulk_ess_per_transition=bulk / transitions,
            tail_ess_per_transition=tail / transitions,
            tail_ess_per_1000_gradients=1000tail / gradients,
            end_to_end_tail_ess_per_second=tail / total_seconds))
        println("  eps=$step_size tail/trans=$(round(tail / transitions; digits=4)) " *
            "Rhat=$(round(rhat; digits=3)) end-to-end tail/s=$(round(tail / total_seconds; digits=1))")
    end
end

output = joinpath(@__DIR__, "results", get(ENV,
    "HIERARCHICAL_LOGISTIC_OUTPUT", "hierarchical-logistic-transport.csv"))
open(output, "w") do io
    println(io, join(keys(first(rows)), ','))
    for row in rows
        println(io, join(values(row), ','))
    end
end
println("wrote $output")
end
