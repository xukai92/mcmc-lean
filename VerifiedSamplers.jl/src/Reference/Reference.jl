module Reference

using LinearAlgebra

using ..Runtime: AbstractRandomSource, draw_below!, standard_normal!, uniform_unit!

export categorical_index!, finite_mh_step!, two_state_mh_step!, gaussian_rwmh_step!, scalar_hmc_step!, vector_hmc_step!, metric_hmc_step!, multinomial_hmc_step!, metric_multinomial_hmc_step!,
    IR_FORMAT_VERSION

const IR_FORMAT_VERSION = 8

struct SList
    items::Vector{Any}
end

struct Atom
    value::String
end

mutable struct Parser
    chars::Vector{Char}
    index::Int
end

function skip_space!(parser::Parser)
    while parser.index <= length(parser.chars) && isspace(parser.chars[parser.index])
        parser.index += 1
    end
end

function parse_string!(parser::Parser)
    parser.index += 1
    output = IOBuffer()
    while parser.index <= length(parser.chars)
        char = parser.chars[parser.index]
        parser.index += 1
        char == '"' && return String(take!(output))
        if char == '\\'
            parser.index <= length(parser.chars) || error("unterminated IR escape")
            escaped = parser.chars[parser.index]
            parser.index += 1
            escaped == 'n' ? write(output, '\n') : write(output, escaped)
        else
            write(output, char)
        end
    end
    error("unterminated IR string")
end

function parse_node!(parser::Parser)
    skip_space!(parser)
    parser.index <= length(parser.chars) || error("unexpected end of IR")
    char = parser.chars[parser.index]
    if char == '('
        parser.index += 1
        items = Any[]
        while true
            skip_space!(parser)
            parser.index <= length(parser.chars) || error("unterminated IR list")
            if parser.chars[parser.index] == ')'
                parser.index += 1
                return SList(items)
            end
            push!(items, parse_node!(parser))
        end
    elseif char == '"'
        return parse_string!(parser)
    elseif char == ')'
        error("unexpected ')' in IR")
    else
        start = parser.index
        while parser.index <= length(parser.chars)
            current = parser.chars[parser.index]
            (isspace(current) || current == '(' || current == ')') && break
            parser.index += 1
        end
        start < parser.index || error("empty IR atom")
        return Atom(String(parser.chars[start:(parser.index - 1)]))
    end
end

function parse_document(source::AbstractString)
    parser = Parser(collect(source), 1)
    document = parse_node!(parser)
    skip_space!(parser)
    parser.index > length(parser.chars) || error("trailing IR input")
    document
end

function render_string(value::String)
    escaped = replace(value, "\\" => "\\\\", "\"" => "\\\"", "\n" => "\\n")
    "\"" * escaped * "\""
end

render_node(value::String) = render_string(value)
render_node(value::Atom) = value.value
render_node(value::SList) = "(" * join(render_node.(value.items), " ") * ")"

items(node::SList) = node.items
atom(value::String) = value
atom(value::Atom) = value.value
aslist(value) = value isa SList ? value : error("expected IR list")

struct Program
    name::String
    inputs::Vector{Tuple{String,String}}
    body::Vector{Any}
end

function decode_program(node::SList)
    values = items(node)
    length(values) == 4 && atom(values[1]) == "program" || error("invalid IR program")
    input_node = items(aslist(values[3]))
    atom(input_node[1]) == "inputs" || error("invalid IR inputs")
    inputs = Tuple{String,String}[]
    for raw in input_node[2:end]
        input = items(aslist(raw))
        length(input) == 3 && atom(input[1]) == "input" || error("invalid IR input")
        push!(inputs, (atom(input[2]), atom(input[3])))
    end
    body_node = items(aslist(values[4]))
    atom(body_node[1]) == "body" || error("invalid IR body")
    Program(atom(values[2]), inputs, Any[body_node[2:end]...])
end

function load_programs(path::String)
    source = strip(read(path, String))
    document = parse_document(source)
    render_node(document) == source || error("sampler IR is not canonically encoded")
    root = items(aslist(document))
    length(root) >= 3 && atom(root[1]) == "verified-samplers-ir" ||
        error("invalid sampler IR header")
    parse(Int, atom(root[2])) == IR_FORMAT_VERSION || error("unsupported sampler IR version")
    programs = Dict{String,Program}()
    for node in root[3:end]
        program = decode_program(aslist(node))
        haskey(programs, program.name) && error("duplicate IR program: $(program.name)")
        programs[program.name] = program
    end
    programs
end

const PROGRAMS = load_programs(joinpath(@__DIR__, "Samplers.ir"))

function checked_logdensity(callback, state)
    value = callback(state)
    value isa Real || throw(ArgumentError("logdensity must return a real scalar"))
    converted = Float64(value)
    isfinite(converted) || throw(DomainError(value, "logdensity must be finite"))
    converted
end

function checked_gradient(callback, state::Real)
    value = callback(state)
    value isa Real || throw(ArgumentError("scalar gradient must return a real scalar"))
    converted = Float64(value)
    isfinite(converted) || throw(DomainError(value, "gradient must be finite"))
    converted
end


function checked_gradient(callback, state::AbstractVector)
    value = callback(state)
    value isa AbstractVector ||
        throw(ArgumentError("vector gradient must return a vector"))
    length(value) == length(state) || throw(DimensionMismatch("gradient dimension"))
    converted = Float64.(value)
    all(isfinite, converted) || throw(DomainError(value, "gradient must be finite"))
    converted
end

function eval_expr(raw, env::Dict{String,Any})
    node = items(aslist(raw))
    tag = atom(node[1])
    tag == "var" && return env[atom(node[3])]
    tag == "nat" && return parse(BigInt, atom(node[2]))
    tag == "real" && return parse(Float64, atom(node[2]))
    tag == "vector" && return BigInt[parse(BigInt, atom(value)) for value in node[2:end]]
    if tag == "matrix"
        return [BigInt[parse(BigInt, atom(value)) for value in items(aslist(row))[2:end]]
            for row in node[2:end]]
    end
    tag == "add" && return eval_expr(node[2], env) + eval_expr(node[3], env)
    tag == "sub" && return max(BigInt(0), eval_expr(node[2], env) - eval_expr(node[3], env))
    tag == "sub-real" && return eval_expr(node[2], env) - eval_expr(node[3], env)
    tag == "mul" && return eval_expr(node[2], env) * eval_expr(node[3], env)
    tag == "div-real" && return eval_expr(node[2], env) / eval_expr(node[3], env)
    tag == "exp" && return exp(eval_expr(node[2], env))
    tag == "min" && return min(eval_expr(node[2], env), eval_expr(node[3], env))
    tag == "length" && return BigInt(length(eval_expr(node[2], env)))
    tag == "row-count" && return BigInt(length(eval_expr(node[2], env)))
    tag == "total" && return sum(eval_expr(node[2], env); init=BigInt(0))
    tag == "index" && return eval_expr(node[2], env)[Int(eval_expr(node[3], env)) + 1]
    tag == "row-at" && return eval_expr(node[2], env)[Int(eval_expr(node[3], env)) + 1]
    tag == "lt" && return eval_expr(node[2], env) < eval_expr(node[3], env)
    tag == "le" && return eval_expr(node[2], env) <= eval_expr(node[3], env)
    tag == "eq" && return eval_expr(node[2], env) == eval_expr(node[3], env)
    tag == "and" && return eval_expr(node[2], env) && eval_expr(node[3], env)
    tag == "all-nonnegative" && return all(>=(0), eval_expr(node[2], env))
    tag == "all-positive" && return all(>(0), eval_expr(node[2], env))
    if tag == "all-rows-length"
        size = eval_expr(node[3], env)
        return all(row -> length(row) == size, eval_expr(node[2], env))
    end
    if tag == "all-rows-nonnegative-positive"
        return all(row -> all(>=(0), row) && sum(row; init=BigInt(0)) > 0,
            eval_expr(node[2], env))
    end
    tag == "to-exact-vector" && return BigInt.(eval_expr(node[2], env))
    tag == "to-exact-matrix" && return [BigInt.(row) for row in eval_expr(node[2], env)]
    tag == "log-density" && return env["logdensity"](eval_expr(node[2], env))
    tag == "gradient" && return env["gradient"](eval_expr(node[2], env))
    tag == "vector-log-density" && return env["logdensity"](eval_expr(node[2], env))
    tag == "vector-gradient" && return env["gradient"](eval_expr(node[2], env))
    tag == "squared-norm" && return sum(abs2, eval_expr(node[2], env); init=0.0)
    if tag == "leapfrog-position" || tag == "leapfrog-momentum"
        step_size = Float64(eval_expr(node[2], env))
        steps = Int(eval_expr(node[3], env))
        position = Float64(eval_expr(node[4], env))
        momentum = Float64(eval_expr(node[5], env))
        for _ in 1:steps
            half_momentum = momentum - step_size * env["gradient"](position) / 2
            position += step_size * half_momentum
            momentum = half_momentum - step_size * env["gradient"](position) / 2
        end
        return tag == "leapfrog-position" ? position : momentum
    end
    if tag == "vector-leapfrog-position" || tag == "vector-leapfrog-momentum"
        step_size = Float64(eval_expr(node[2], env))
        steps = Int(eval_expr(node[3], env))
        position = Float64.(eval_expr(node[4], env))
        momentum = Float64.(eval_expr(node[5], env))
        for _ in 1:steps
            half_momentum = momentum .- (step_size / 2) .* env["gradient"](position)
            position = position .+ step_size .* half_momentum
            momentum = half_momentum .- (step_size / 2) .* env["gradient"](position)
        end
        return tag == "vector-leapfrog-position" ? position : momentum
    end
    if tag == "metric-hmc"
        kind = Symbol(atom(node[2]))
        source = eval_expr(node[3], env)
        step_size = Float64(eval_expr(node[4], env))
        steps = Int(eval_expr(node[5], env))
        current = eval_expr(node[6], env)
        mass = eval_expr(node[7], env)
        return _metric_hmc_step!(source, env["logdensity"], env["gradient"],
            step_size, steps, current, mass, kind)
    end
    if tag == "multinomial-hmc"
        source = eval_expr(node[2], env)
        step_size = Float64(eval_expr(node[3], env))
        steps = Int(eval_expr(node[4], env))
        current = eval_expr(node[5], env)
        return _multinomial_hmc_step!(source, env["logdensity"], env["gradient"],
            step_size, steps, current)
    end
    if tag == "metric-multinomial-hmc"
        kind = Symbol(atom(node[2]))
        source = eval_expr(node[3], env)
        step_size = Float64(eval_expr(node[4], env))
        steps = Int(eval_expr(node[5], env))
        current = eval_expr(node[6], env)
        mass = eval_expr(node[7], env)
        return _metric_multinomial_hmc_step!(source, env["logdensity"],
            env["gradient"], step_size, steps, current, mass, kind)
    end
    if tag == "categorical"
        source = eval_expr(node[2], env)
        weights = eval_expr(node[3], env)
        total = sum(weights; init=BigInt(0))
        draw = BigInt(draw_below!(source, total))
        for (index, weight) in enumerate(weights)
            draw < weight && return BigInt(index - 1)
            draw -= weight
        end
        error("draw_below! violated its range contract")
    end
    error("unsupported IR expression: $tag")
end

struct Returned
    value::Any
end

function raise_failure(raw)
    node = items(aslist(raw))
    kind, message = atom(node[1]), atom(node[2])
    kind == "argument" && throw(ArgumentError(message))
    kind == "dimension" && throw(DimensionMismatch(message))
    kind == "internal" && error(message)
    error("unsupported IR failure: $kind")
end

function execute_block(body, env::Dict{String,Any})
    for raw in body
        node = items(aslist(raw))
        tag = atom(node[1])
        if tag == "let"
            env[atom(node[2])] = eval_expr(node[3], env)
        elseif tag == "guard"
            eval_expr(node[2], env) || raise_failure(node[3])
        elseif tag == "draw-below"
            env[atom(node[2])] = BigInt(draw_below!(eval_expr(node[3], env),
                eval_expr(node[4], env)))
        elseif tag == "sample-standard-normal"
            env[atom(node[2])] = standard_normal!(env["source"])
        elseif tag == "sample-uniform-unit"
            env[atom(node[2])] = uniform_unit!(env["source"])
        elseif tag == "sample-standard-normal-vector"
            dimension = Int(eval_expr(node[3], env))
            env[atom(node[2])] = [standard_normal!(env["source"]) for _ in 1:dimension]
        elseif tag == "if"
            if eval_expr(node[2], env)
                result = execute_block(items(aslist(node[3]))[2:end], env)
                result isa Returned && return result
            end
        elseif tag == "return"
            return Returned(eval_expr(node[2], env))
        elseif tag == "fail"
            raise_failure(node[2])
        else
            error("unsupported IR statement: $tag")
        end
    end
    nothing
end

function run_program(name::String, arguments...)
    program = get(PROGRAMS, name, nothing)
    program === nothing && error("unknown IR program: $name")
    length(arguments) == length(program.inputs) || throw(ArgumentError("IR argument count"))
    env = Dict{String,Any}()
    for ((input_kind, input_name), value) in zip(program.inputs, arguments)
        valid = input_kind == "source" ? value isa AbstractRandomSource :
            input_kind == "log-density" || input_kind == "gradient" ?
                (applicable(value, 0.0) || applicable(value, Float64[])) :
            input_kind == "real" ? value isa Real : true
        valid = input_kind == "nat" ? value isa Integer && value >= 0 : valid
        valid = input_kind == "real-vector" ? value isa AbstractVector{<:Real} : valid
        valid = input_kind == "real-matrix" ? value isa AbstractMatrix{<:Real} : valid
        valid || throw(ArgumentError("invalid $input_kind input: $input_name"))
        env[input_name] = value
    end
    result = execute_block(program.body, env)
    result isa Returned || error("IR program did not return: $name")
    result.value
end

function categorical_index!(source::AbstractRandomSource, weights::AbstractVector{<:Integer})
    exact = BigInt.(weights)
    all(>=(0), exact) || throw(ArgumentError("weights must be nonnegative"))
    sum(exact; init=BigInt(0)) > 0 || throw(ArgumentError("weights must have positive total"))
    run_program("categorical_index!", source, exact)
end

function finite_mh_step!(source::AbstractRandomSource, target::AbstractVector{<:Integer},
        proposal::AbstractVector, current::Integer)
    target_weights = BigInt.(target)
    all(>(0), target_weights) || throw(ArgumentError("target weights must be positive"))
    state_count = length(target_weights)
    length(proposal) == state_count || throw(DimensionMismatch("proposal row count"))
    0 <= current < state_count || throw(ArgumentError("current state is out of range"))
    rows = [BigInt.(row) for row in proposal]
    all(row -> length(row) == state_count, rows) ||
        throw(DimensionMismatch("proposal column count"))
    all(row -> all(>=(0), row) && sum(row; init=BigInt(0)) > 0, rows) ||
        throw(ArgumentError("proposal rows need nonnegative weights and positive totals"))
    run_program("finite_mh_step!", source, target_weights, rows, BigInt(current))
end

two_state_mh_step!(source::AbstractRandomSource, current::Integer) =
    finite_mh_step!(source, BigInt[1, 3], [BigInt[1, 1], BigInt[1, 1]], current)

"""Float64 interpretation of the serialized ideal-real Gaussian RWMH program.

This preserves the program's control flow and primitive ordering, but it is
not an exact realization of Lean `ℝ`; arithmetic, `exp`, the callback, and RNG
primitives use Julia's concrete Float64 semantics.
"""
function gaussian_rwmh_step!(source::AbstractRandomSource, logdensity,
        scale::Float64, current::Float64)
    isfinite(scale) && scale > 0.0 ||
        throw(ArgumentError("scale must be finite and positive"))
    isfinite(current) || throw(ArgumentError("current state must be finite"))
    checked = value -> checked_logdensity(logdensity, value)
    Float64(run_program("gaussian_rwmh_step!", source, checked, scale, current))
end

"""Float64 interpretation of the serialized scalar one-step HMC program."""
function scalar_hmc_step!(source::AbstractRandomSource, logdensity, gradient,
        step_size::Float64, steps::Integer, current::Float64)
    isfinite(step_size) && step_size > 0.0 ||
        throw(ArgumentError("step size must be finite and positive"))
    steps > 0 || throw(ArgumentError("leapfrog steps must be positive"))
    isfinite(current) || throw(ArgumentError("current state must be finite"))
    checked_log = value -> checked_logdensity(logdensity, value)
    checked_grad = value -> checked_gradient(gradient, value)
    Float64(run_program("scalar_hmc_step!", source, checked_log, checked_grad,
        step_size, current, steps))
end

"""Float64 interpretation of the serialized vector endpoint-HMC program."""
function vector_hmc_step!(source::AbstractRandomSource, logdensity, gradient,
        step_size::Float64, steps::Integer, current::AbstractVector{<:Real})
    isfinite(step_size) && step_size > 0.0 ||
        throw(ArgumentError("step size must be finite and positive"))
    steps > 0 || throw(ArgumentError("leapfrog steps must be positive"))
    isempty(current) && throw(ArgumentError("position cannot be empty"))
    position = Float64.(current)
    all(isfinite, position) || throw(ArgumentError("position must be finite"))
    checked_log = value -> checked_logdensity(logdensity, value)
    checked_grad = value -> checked_gradient(gradient, value)
    result = run_program("vector_hmc_step!", source, checked_log, checked_grad,
        step_size, steps, length(position), position)
    Float64.(result)
end

"""Reference endpoint HMC for a constant diagonal or dense mass matrix."""
function _metric_hmc_step!(source::AbstractRandomSource, logdensity, gradient,
        step_size::Float64, steps::Integer, current::AbstractVector{<:Real}, mass,
        kind::Symbol)
    dimension = length(current)
    dimension > 0 || throw(ArgumentError("position cannot be empty"))
    z = [standard_normal!(source) for _ in 1:dimension]
    if kind === :diagonal
        length(mass) == dimension || throw(DimensionMismatch("mass dimension"))
        all(x -> isfinite(x) && x > 0, mass) ||
            throw(ArgumentError("diagonal mass must be finite and positive"))
        momentum = sqrt.(mass) .* z
        velocity = p -> p ./ mass
    elseif kind === :dense
        size(mass) == (dimension, dimension) || throw(DimensionMismatch("mass dimension"))
        matrix = Matrix{Float64}(mass)
        all(isfinite, matrix) || throw(ArgumentError("mass matrix must be finite"))
        issymmetric(matrix) || throw(ArgumentError("mass matrix must be symmetric"))
        isposdef(matrix) || throw(ArgumentError("mass matrix must be positive definite"))
        factor = cholesky(Symmetric(matrix)).L
        momentum = factor * z
        velocity = p -> factor' \ (factor \ p)
    else
        error("unsupported metric kind: $kind")
    end
    position = Float64.(current)
    initial_momentum = copy(momentum)
    for _ in 1:steps
        momentum = momentum .- (step_size / 2) .* gradient(position)
        position = position .+ step_size .* velocity(momentum)
        momentum = momentum .- (step_size / 2) .* gradient(position)
    end
    current_energy = -logdensity(current) + dot(initial_momentum, velocity(initial_momentum)) / 2
    next_energy = -logdensity(position) + dot(momentum, velocity(momentum)) / 2
    log(uniform_unit!(source)) < min(0.0, current_energy - next_energy) ?
        position : Float64.(current)
end

function metric_hmc_step!(source::AbstractRandomSource, logdensity, gradient,
        step_size::Float64, steps::Integer, current::AbstractVector{<:Real}, mass)
    all(isfinite, current) || throw(ArgumentError("position must be finite"))
    name = mass isa AbstractVector ? "diagonal_hmc_step!" : "dense_hmc_step!"
    checked_log = value -> checked_logdensity(logdensity, value)
    checked_grad = value -> checked_gradient(gradient, value)
    Float64.(run_program(name, source, checked_log, checked_grad, step_size, steps,
        current, mass))
end

function _multinomial_hmc_step!(source::AbstractRandomSource, logdensity, gradient,
        step_size::Float64, steps::Integer, current::AbstractVector{<:Real})
    steps > 0 || throw(ArgumentError("trajectory length must be positive"))
    q0 = Float64.(current)
    isempty(q0) && throw(ArgumentError("position cannot be empty"))
    p0 = [standard_normal!(source) for _ in eachindex(q0)]
    origin = Int(draw_below!(source, steps + 1))
    trajectory = Vector{Tuple{Vector{Float64},Vector{Float64}}}(undef, steps + 1)
    for index in 0:steps
        q, p = copy(q0), copy(p0)
        signed_step = index >= origin ? step_size : -step_size
        for _ in 1:abs(index - origin)
            half = p .- (signed_step / 2) .* gradient(q)
            q = q .+ signed_step .* half
            p = half .- (signed_step / 2) .* gradient(q)
        end
        trajectory[index + 1] = (q, p)
    end
    logweights = [logdensity(q) - sum(abs2, p) / 2 for (q, p) in trajectory]
    maximum_weight = maximum(logweights)
    weights = exp.(logweights .- maximum_weight)
    draw = uniform_unit!(source) * sum(weights)
    selected = length(weights)
    cumulative = 0.0
    for index in eachindex(weights)
        cumulative += weights[index]
        if draw < cumulative
            selected = index
            break
        end
    end
    trajectory[selected][1]
end

function multinomial_hmc_step!(source::AbstractRandomSource, logdensity, gradient,
        step_size::Float64, steps::Integer, current::AbstractVector{<:Real})
    all(isfinite, current) || throw(ArgumentError("position must be finite"))
    checked_log = value -> checked_logdensity(logdensity, value)
    checked_grad = value -> checked_gradient(gradient, value)
    Float64.(run_program("multinomial_hmc_step!", source, checked_log, checked_grad,
        step_size, steps, current))
end

function _metric_multinomial_hmc_step!(source::AbstractRandomSource, logdensity,
        gradient, step_size::Float64, steps::Integer,
        current::AbstractVector{<:Real}, mass, kind::Symbol)
    steps > 0 || throw(ArgumentError("trajectory length must be positive"))
    q0 = Float64.(current)
    isempty(q0) && throw(ArgumentError("position cannot be empty"))
    z = [standard_normal!(source) for _ in eachindex(q0)]
    if kind === :diagonal
        length(mass) == length(q0) || throw(DimensionMismatch("mass dimension"))
        all(x -> isfinite(x) && x > 0, mass) ||
            throw(ArgumentError("diagonal mass must be finite and positive"))
        p0 = sqrt.(mass) .* z
        velocity = p -> p ./ mass
    elseif kind === :dense
        size(mass) == (length(q0), length(q0)) ||
            throw(DimensionMismatch("mass dimension"))
        matrix = Matrix{Float64}(mass)
        all(isfinite, matrix) || throw(ArgumentError("mass matrix must be finite"))
        issymmetric(matrix) || throw(ArgumentError("mass matrix must be symmetric"))
        isposdef(matrix) || throw(ArgumentError("mass matrix must be positive definite"))
        factor = cholesky(Symmetric(matrix)).L
        p0 = factor * z
        velocity = p -> factor' \ (factor \ p)
    else
        error("unsupported metric kind: $kind")
    end
    origin = Int(draw_below!(source, steps + 1))
    trajectory = Vector{Tuple{Vector{Float64},Vector{Float64}}}(undef, steps + 1)
    for index in 0:steps
        q, p = copy(q0), copy(p0)
        signed_step = index >= origin ? step_size : -step_size
        for _ in 1:abs(index - origin)
            half = p .- (signed_step / 2) .* gradient(q)
            q = q .+ signed_step .* velocity(half)
            p = half .- (signed_step / 2) .* gradient(q)
        end
        trajectory[index + 1] = (q, p)
    end
    logweights = [logdensity(q) - dot(p, velocity(p)) / 2 for (q, p) in trajectory]
    weights = exp.(logweights .- maximum(logweights))
    draw = uniform_unit!(source) * sum(weights)
    cumulative = 0.0
    for (index, weight) in pairs(weights)
        cumulative += weight
        draw < cumulative && return trajectory[index][1]
    end
    trajectory[end][1]
end

function metric_multinomial_hmc_step!(source::AbstractRandomSource, logdensity,
        gradient, step_size::Float64, steps::Integer,
        current::AbstractVector{<:Real}, mass)
    all(isfinite, current) || throw(ArgumentError("position must be finite"))
    name = mass isa AbstractVector ? "diagonal_multinomial_hmc_step!" :
        "dense_multinomial_hmc_step!"
    checked_log = value -> checked_logdensity(logdensity, value)
    checked_grad = value -> checked_gradient(gradient, value)
    Float64.(run_program(name, source, checked_log, checked_grad, step_size, steps,
        current, mass))
end

end
