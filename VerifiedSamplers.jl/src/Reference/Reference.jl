module Reference

using ..Runtime: AbstractRandomSource, draw_below!, standard_normal!, uniform_unit!

export categorical_index!, finite_mh_step!, two_state_mh_step!, gaussian_rwmh_step!, scalar_hmc_step!,
    IR_FORMAT_VERSION

const IR_FORMAT_VERSION = 4

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
            input_kind == "log-density" || input_kind == "gradient" ? applicable(value, 0.0) :
            input_kind == "real" ? value isa Real : true
        valid = input_kind == "nat" ? value isa Integer && value >= 0 : valid
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
    Float64(run_program("gaussian_rwmh_step!", source, logdensity, scale, current))
end

"""Float64 interpretation of the serialized scalar one-step HMC program."""
function scalar_hmc_step!(source::AbstractRandomSource, logdensity, gradient,
        step_size::Float64, steps::Integer, current::Float64)
    isfinite(step_size) && step_size > 0.0 ||
        throw(ArgumentError("step size must be finite and positive"))
    steps > 0 || throw(ArgumentError("leapfrog steps must be positive"))
    Float64(run_program("scalar_hmc_step!", source, logdensity, gradient,
        step_size, current, steps))
end

end
