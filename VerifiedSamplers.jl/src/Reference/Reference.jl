module Reference

using LinearAlgebra

using ..Runtime: AbstractRandomSource, draw_below!, standard_normal!, uniform_unit!
using ..Certificates: ImplicitSolveCertificate, certify_implicit_solve,
    certifies_exact_solver

export categorical_index!, integer_slice_step!, bounded_slice_step!, stepping_out_slice_step!, finite_mh_step!, two_state_mh_step!, gaussian_rwmh_step!, scalar_hmc_step!, vector_hmc_step!, metric_hmc_step!, multinomial_hmc_step!, metric_multinomial_hmc_step!, categorical_dhmc_step!,
    finite_hmm_particle_gibbs_step!,
    relativistic_multinomial_hmc_step!,
    fixed_point_generalized_leapfrog,
    certified_relativistic_multinomial_hmc_step!,
    coupled_multinomial_hmc_step!, coupled_gaussian_rwmh_step!, xu21_coupled_step!,
    IR_FORMAT_VERSION

const IR_FORMAT_VERSION = 14

"""Reference coordinate-wise DHMC update for a categorical law on a cycle.

This is the all-discontinuous, one-coordinate specialization of Algorithm 1
of Nishimura, Dunson, and Lu.  Taking `epsilon = mass` moves exactly one
category per coordinate update.  The refreshed Laplace kinetic energy is
Exponential(1); crossing spends the exact potential jump and rejection
reflects the momentum direction.
"""
function categorical_dhmc_step!(source::AbstractRandomSource,
        probabilities::AbstractVector{<:Real}, steps::Integer,
        current::Integer)
    length(probabilities) >= 2 ||
        throw(ArgumentError("DHMC needs at least two categories"))
    all(x -> isfinite(x) && x > 0, probabilities) ||
        throw(ArgumentError("category probabilities must be finite and positive"))
    steps > 0 || throw(ArgumentError("trajectory length must be positive"))
    1 <= current <= length(probabilities) ||
        throw(ArgumentError("current category is out of range"))

    forward = uniform_unit!(source) < 0.5
    kinetic = -log1p(-uniform_unit!(source))
    state = Int(current)
    for _ in 1:steps
        candidate = forward ? mod1(state + 1, length(probabilities)) :
            mod1(state - 1, length(probabilities))
        jump = log(Float64(probabilities[state])) -
            log(Float64(probabilities[candidate]))
        if jump < kinetic
            state = candidate
            kinetic -= jump
        else
            forward = !forward
        end
    end
    state
end

"""Exact integer under-the-graph slice update on zero-based state indices."""
function integer_slice_step!(source::AbstractRandomSource,
        weights::AbstractVector{<:Integer}, current::Integer)
    isempty(weights) && throw(ArgumentError("slice weights cannot be empty"))
    all(>(0), weights) || throw(ArgumentError("slice weights must be positive"))
    0 <= current < length(weights) || throw(ArgumentError("current state is out of range"))
    height = draw_below!(source, weights[current + 1])
    candidates = findall(weight -> weight > height, weights)
    selected = Int(draw_below!(source, length(candidates))) + 1
    candidates[selected] - 1
end

"""Reference rejection implementation of exact slice selection on a bounded interval."""
function bounded_slice_step!(source::AbstractRandomSource, logdensity,
        lower::Real, upper::Real, current::Real, max_attempts::Integer)
    lo, hi, x = Float64(lower), Float64(upper), Float64(current)
    isfinite(lo) && isfinite(hi) && lo < hi ||
        throw(ArgumentError("slice bounds must be finite and ordered"))
    lo <= x <= hi || throw(ArgumentError("current state is outside slice bounds"))
    max_attempts > 0 || throw(ArgumentError("max_attempts must be positive"))
    current_logdensity = Float64(logdensity(x))
    isfinite(current_logdensity) ||
        throw(ArgumentError("current log density must be finite"))
    logheight = current_logdensity + log(uniform_unit!(source))
    for _ in 1:max_attempts
        proposal = lo + (hi - lo) * uniform_unit!(source)
        proposed_logdensity = Float64(logdensity(proposal))
        (isfinite(proposed_logdensity) || proposed_logdensity == -Inf) ||
            throw(ArgumentError("log density must be finite or -Inf"))
        proposed_logdensity >= logheight && return proposal
    end
    throw(ErrorException("bounded slice rejection exceeded max_attempts"))
end

"""Reference stepping-out and shrinkage slice update on the real line."""
function stepping_out_slice_step!(source::AbstractRandomSource, logdensity,
        width::Real, current::Real, max_steps::Integer, max_shrink::Integer)
    w, x = Float64(width), Float64(current)
    isfinite(w) && w > 0 || throw(ArgumentError("width must be finite and positive"))
    isfinite(x) || throw(ArgumentError("current state must be finite"))
    max_steps >= 0 || throw(ArgumentError("max_steps must be nonnegative"))
    max_shrink > 0 || throw(ArgumentError("max_shrink must be positive"))
    base = Float64(logdensity(x))
    isfinite(base) || throw(ArgumentError("current log density must be finite"))
    threshold = base + log(uniform_unit!(source))
    left = x - w * uniform_unit!(source)
    right = left + w
    left_steps = Int(floor(uniform_unit!(source) * (max_steps + 1)))
    right_steps = max_steps - left_steps
    while left_steps > 0
        value = Float64(logdensity(left))
        (isfinite(value) || value == -Inf) ||
            throw(ArgumentError("log density must be finite or -Inf"))
        value <= threshold && break
        left -= w
        left_steps -= 1
    end
    while right_steps > 0
        value = Float64(logdensity(right))
        (isfinite(value) || value == -Inf) ||
            throw(ArgumentError("log density must be finite or -Inf"))
        value <= threshold && break
        right += w
        right_steps -= 1
    end
    for _ in 1:max_shrink
        proposal = left + (right - left) * uniform_unit!(source)
        value = Float64(logdensity(proposal))
        (isfinite(value) || value == -Inf) ||
            throw(ArgumentError("log density must be finite or -Inf"))
        value >= threshold && return proposal
        proposal < x ? (left = proposal) : (right = proposal)
    end
    throw(ErrorException("slice shrinkage exceeded max_shrink"))
end

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

struct OperatorDescriptor
    name::String
    engine::String
    scope::Vector{String}
end

struct ScheduleDescriptor
    name::String
    variables::Vector{String}
    operators::Vector{OperatorDescriptor}
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

function decode_schedule(node::SList)
    values = items(node)
    length(values) == 4 && atom(values[1]) == "schedule" ||
        error("invalid schedule descriptor")
    variable_node = items(aslist(values[3]))
    atom(variable_node[1]) == "variables" || error("invalid schedule variables")
    variables = String[atom(value) for value in variable_node[2:end]]
    operator_node = items(aslist(values[4]))
    atom(operator_node[1]) == "operators" || error("invalid schedule operators")
    operators = OperatorDescriptor[]
    for raw in operator_node[2:end]
        fields = items(aslist(raw))
        length(fields) == 4 && atom(fields[1]) == "operator" ||
            error("invalid operator descriptor")
        scope_node = items(aslist(fields[4]))
        atom(scope_node[1]) == "scope" || error("invalid operator scope")
        push!(operators, OperatorDescriptor(atom(fields[2]), atom(fields[3]),
            String[atom(value) for value in scope_node[2:end]]))
    end
    ScheduleDescriptor(atom(values[2]), variables, operators)
end

struct TransformDescriptor
    name::String
    transform::String
    constrained_type::String
    unconstrained_type::String
    forward::String
    inverse::String
    logabsdet_inverse_jacobian::String
end

function decode_transform(node::SList)
    values = items(node)
    length(values) == 8 && atom(values[1]) == "transform" ||
        error("invalid transform descriptor")
    descriptor = TransformDescriptor((atom(value) for value in values[2:end])...)
    descriptor.transform == "positive-log" ||
        error("unsupported scalar transform: $(descriptor.transform)")
    descriptor
end

function load_artifact(path::String)
    source = strip(read(path, String))
    document = parse_document(source)
    render_node(document) == source || error("sampler IR is not canonically encoded")
    root = items(aslist(document))
    length(root) >= 3 && atom(root[1]) == "verified-samplers-ir" ||
        error("invalid sampler IR header")
    parse(Int, atom(root[2])) == IR_FORMAT_VERSION || error("unsupported sampler IR version")
    programs = Dict{String,Program}()
    targets = Dict{String,Any}()
    schedules = Dict{String,ScheduleDescriptor}()
    transforms = Dict{String,TransformDescriptor}()
    for node in root[3:end]
        values = items(aslist(node))
        tag = atom(values[1])
        if tag == "program"
            program = decode_program(aslist(node))
            haskey(programs, program.name) &&
                error("duplicate IR program: $(program.name)")
            programs[program.name] = program
        elseif tag == "target"
            length(values) == 3 || error("invalid restricted target declaration")
            name = atom(values[2])
            haskey(targets, name) && error("duplicate restricted target: $name")
            targets[name] = values[3]
        elseif tag == "schedule"
            schedule = decode_schedule(aslist(node))
            haskey(schedules, schedule.name) &&
                error("duplicate schedule descriptor: $(schedule.name)")
            schedules[schedule.name] = schedule
        elseif tag == "transform"
            transform = decode_transform(aslist(node))
            haskey(transforms, transform.name) &&
                error("duplicate transform descriptor: $(transform.name)")
            transforms[transform.name] = transform
        else
            error("unknown top-level IR declaration: $tag")
        end
    end
    programs, targets, schedules, transforms
end

# Retain the program-only loader for downstream callers while the artifact now
# also carries restricted target declarations.
load_programs(path::String) = first(load_artifact(path))

const PROGRAMS, TARGETS, SCHEDULES, TRANSFORMS =
    load_artifact(joinpath(@__DIR__, "Samplers.ir"))

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
    if tag == "relativistic-multinomial-hmc"
        source = eval_expr(node[2], env)
        step_size = Float64(eval_expr(node[3], env))
        steps = Int(eval_expr(node[4], env))
        current = eval_expr(node[5], env)
        mass = eval_expr(node[6], env)
        relativistic_mass = Float64(eval_expr(node[7], env))
        return _relativistic_multinomial_hmc_step!(source, env["logdensity"],
            env["gradient"], step_size, steps, current, mass, relativistic_mass)
    end
    if tag == "certified-relativistic-multinomial-hmc"
        source = eval_expr(node[2], env)
        step_size = Float64(eval_expr(node[3], env))
        steps = Int(eval_expr(node[4], env))
        current = eval_expr(node[5], env)
        relativistic_mass = Float64(eval_expr(node[6], env))
        return _certified_relativistic_multinomial_hmc_step!(source,
            env["hamiltonian"], env["metric_factor"], env["integrator"],
            step_size, steps, current, relativistic_mass)
    end
    if tag == "coupled-multinomial-hmc" || tag == "coupled-gaussian-rwmh" ||
            tag == "xu21-coupled-mixture"
        source = eval_expr(node[2], env)
        step_size = Float64(eval_expr(node[3], env))
        steps = Int(eval_expr(node[4], env))
        scale = Float64(eval_expr(node[5], env))
        hmc_weight = Float64(eval_expr(node[6], env))
        left = Float64.(eval_expr(node[7], env))
        right = Float64.(eval_expr(node[8], env))
        if tag == "coupled-multinomial-hmc"
            return _coupled_multinomial_hmc_step!(source, env["logdensity"],
                env["gradient"], step_size, steps, left, right)
        elseif tag == "coupled-gaussian-rwmh"
            return _coupled_gaussian_rwmh_step!(source, env["logdensity"],
                scale, left, right)
        end
        return uniform_unit!(source) < hmc_weight ?
            _coupled_multinomial_hmc_step!(source, env["logdensity"], env["gradient"],
                step_size, steps, left, right) :
            _coupled_gaussian_rwmh_step!(source, env["logdensity"], scale, left, right)
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

function _categorical_uniform!(source, weights)
    draw = uniform_unit!(source) * sum(weights)
    cumulative = 0.0
    for index in eachindex(weights)
        cumulative += weights[index]
        draw < cumulative && return index
    end
    lastindex(weights)
end

function _maximal_categorical_pair!(source, left, right)
    p, q = left ./ sum(left), right ./ sum(right)
    common = min.(p, q)
    common_mass = sum(common)
    if uniform_unit!(source) < common_mass
        index = _categorical_uniform!(source, common)
        return index, index
    end
    _categorical_uniform!(source, p .- common),
        _categorical_uniform!(source, q .- common)
end

function _trajectory(logdensity, gradient, step_size, steps, q0, p0, origin)
    result = Vector{Tuple{Vector{Float64},Vector{Float64}}}(undef, steps + 1)
    for index in 0:steps
        q, p = copy(q0), copy(p0)
        signed_step = index >= origin ? step_size : -step_size
        for _ in 1:abs(index - origin)
            half = p .- (signed_step / 2) .* gradient(q)
            q = q .+ signed_step .* half
            p = half .- (signed_step / 2) .* gradient(q)
        end
        result[index + 1] = (q, p)
    end
    result
end

function _coupled_multinomial_hmc_step!(source, logdensity, gradient,
        step_size, steps, left, right)
    length(left) == length(right) || throw(DimensionMismatch("coupled states"))
    momentum = [standard_normal!(source) for _ in eachindex(left)]
    origin = Int(draw_below!(source, steps + 1))
    left_path = _trajectory(logdensity, gradient, step_size, steps, left, momentum, origin)
    right_path = _trajectory(logdensity, gradient, step_size, steps, right, momentum, origin)
    weights(path) = begin
        logs = [logdensity(q) - sum(abs2, p) / 2 for (q, p) in path]
        exp.(logs .- maximum(logs))
    end
    i, j = _maximal_categorical_pair!(source, weights(left_path), weights(right_path))
    [left_path[i][1], right_path[j][1]]
end

function _coupled_gaussian_rwmh_step!(source, logdensity, scale, left, right)
    length(left) == length(right) || throw(DimensionMismatch("coupled states"))
    noise = [standard_normal!(source) for _ in eachindex(left)]
    proposed_left = left .+ scale .* noise
    log_ratio = (sum(abs2, proposed_left .- right) -
        sum(abs2, proposed_left .- left)) / (-2scale^2)
    proposed_right = if log(uniform_unit!(source)) < min(0.0, log_ratio)
        copy(proposed_left)
    else
        delta = right .- left
        norm2 = sum(abs2, delta)
        norm2 == 0 ? copy(proposed_left) :
            right .+ scale .* (noise .- 2 .* (dot(noise, delta) / norm2) .* delta)
    end
    u = log(uniform_unit!(source))
    next_left = u < min(0.0, logdensity(proposed_left) - logdensity(left)) ? proposed_left : left
    next_right = u < min(0.0, logdensity(proposed_right) - logdensity(right)) ? proposed_right : right
    [next_left, next_right]
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

"""One exact-integer conditional-SMC/particle-Gibbs update for a finite HMM.

`potentials[t, x]` weights state `x` before transition `t`; therefore a path
contains `size(potentials, 1) + 1` states. State values are one-based Julia
indices, while retained particle indices remain zero-based trace draws.
"""
function finite_hmm_particle_gibbs_step!(source::AbstractRandomSource,
        initial_weights::AbstractVector{<:Integer},
        transition_weights::AbstractMatrix{<:Integer},
        potentials::AbstractMatrix{<:Integer}, particles::Integer,
        current_path::AbstractVector{<:Integer})
    particles > 0 || throw(ArgumentError("particle count must be positive"))
    states = length(initial_weights)
    states > 0 || throw(ArgumentError("state space cannot be empty"))
    size(transition_weights) == (states, states) ||
        throw(DimensionMismatch("transition matrix"))
    size(potentials, 2) == states || throw(DimensionMismatch("potentials"))
    length(current_path) == size(potentials, 1) + 1 ||
        throw(DimensionMismatch("reference path horizon"))
    all(x -> 1 <= x <= states, current_path) ||
        throw(ArgumentError("reference path state out of range"))
    all(>=(0), initial_weights) && sum(initial_weights) > 0 ||
        throw(ArgumentError("invalid initial weights"))
    all(>=(0), transition_weights) || throw(ArgumentError("negative transition weight"))
    all(row -> sum(row) > 0, eachrow(transition_weights)) ||
        throw(ArgumentError("transition rows must have positive total"))
    all(>(0), potentials) || throw(ArgumentError("potentials must be positive"))

    count = Int(particles)
    retained = Int(draw_below!(source, count)) + 1
    population = Vector{Int}(undef, count)
    for i in eachindex(population)
        population[i] = i == retained ? Int(current_path[1]) :
            categorical_index!(source, initial_weights) + 1
    end
    populations = Vector{Vector{Int}}(undef, size(potentials, 1) + 1)
    populations[1] = copy(population)
    ancestor_history = Vector{Vector{Int}}(undef, size(potentials, 1))

    for t in axes(potentials, 1)
        next_retained = Int(draw_below!(source, count)) + 1
        resampling_weights = [potentials[t, population[i]] for i in eachindex(population)]
        ancestors = Vector{Int}(undef, count)
        next_population = Vector{Int}(undef, count)
        for i in 1:count
            ancestors[i] = i == next_retained ? retained :
                categorical_index!(source, resampling_weights) + 1
        end
        for i in 1:count
            next_population[i] = i == next_retained ? Int(current_path[t + 1]) :
                categorical_index!(source,
                    @view transition_weights[population[ancestors[i]], :]) + 1
        end
        ancestor_history[t] = ancestors
        populations[t + 1] = next_population
        population = next_population
        retained = next_retained
    end

    terminal = Int(draw_below!(source, count)) + 1
    path = Vector{Int}(undef, length(current_path))
    path[end] = populations[end][terminal]
    for t in reverse(eachindex(ancestor_history))
        terminal = ancestor_history[t][terminal]
        path[t] = populations[t][terminal]
    end
    path
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

function _relativistic_radius!(source::AbstractRandomSource, dimension::Int,
        relativistic_mass::Float64)
    while true
        # Gamma(d, 1) proposal: sum of d independent exponential variables.
        radius = sum((-log1p(-uniform_unit!(source)) for _ in 1:dimension); init=0.0)
        log_acceptance = radius - sqrt(radius^2 + relativistic_mass^2)
        log(uniform_unit!(source)) < log_acceptance && return radius
    end
end

function _relativistic_momentum!(source::AbstractRandomSource,
        mass::AbstractVector{<:Real}, relativistic_mass::Float64)
    dimension = length(mass)
    radius = _relativistic_radius!(source, dimension, relativistic_mass)
    direction = [standard_normal!(source) for _ in 1:dimension]
    direction_norm = norm(direction)
    isfinite(direction_norm) && direction_norm > 0 ||
        throw(DomainError(direction, "spherical direction draw must be nonzero"))
    isotropic = (radius / direction_norm) .* direction
    # If A'A = G⁻¹, the corrected transport is p = A⁻¹z.
    sqrt.(mass) .* isotropic
end

function _relativistic_multinomial_hmc_step!(source::AbstractRandomSource,
        logdensity, gradient, step_size::Float64, steps::Integer,
        current::AbstractVector{<:Real}, mass::AbstractVector{<:Real},
        relativistic_mass::Float64)
    steps > 0 || throw(ArgumentError("trajectory length must be positive"))
    isfinite(step_size) && step_size > 0 ||
        throw(ArgumentError("step size must be finite and positive"))
    q0 = Float64.(current)
    isempty(q0) && throw(ArgumentError("position cannot be empty"))
    length(mass) == length(q0) || throw(DimensionMismatch("mass dimension"))
    all(x -> isfinite(x) && x > 0, mass) ||
        throw(ArgumentError("diagonal metric must be finite and positive"))
    isfinite(relativistic_mass) && relativistic_mass > 0 ||
        throw(ArgumentError("relativistic mass must be finite and positive"))
    converted_mass = Float64.(mass)
    p0 = _relativistic_momentum!(source, converted_mass, relativistic_mass)
    velocity = function (p)
        inverse_metric_p = p ./ converted_mass
        inverse_metric_p ./ sqrt(dot(p, inverse_metric_p) + relativistic_mass^2)
    end
    advance = function (q, p, signed_step)
        half = p .- (signed_step / 2) .* gradient(q)
        next_q = q .+ signed_step .* velocity(half)
        next_p = half .- (signed_step / 2) .* gradient(next_q)
        next_q, next_p
    end
    origin = Int(draw_below!(source, steps + 1))
    trajectory = Vector{Tuple{Vector{Float64},Vector{Float64}}}(undef, steps + 1)
    for index in 0:steps
        q, p = copy(q0), copy(p0)
        signed_step = index >= origin ? step_size : -step_size
        for _ in 1:abs(index - origin)
            q, p = advance(q, p, signed_step)
        end
        trajectory[index + 1] = (q, p)
    end
    logweights = [logdensity(q) -
        sqrt(dot(p, p ./ converted_mass) + relativistic_mass^2)
        for (q, p) in trajectory]
    weights = exp.(logweights .- maximum(logweights))
    draw = uniform_unit!(source) * sum(weights)
    cumulative = 0.0
    for (index, weight) in pairs(weights)
        cumulative += weight
        draw < cumulative && return trajectory[index][1]
    end
    trajectory[end][1]
end

function relativistic_multinomial_hmc_step!(source::AbstractRandomSource,
        logdensity, gradient, step_size::Real, steps::Integer,
        current::AbstractVector{<:Real}, mass::AbstractVector{<:Real},
        relativistic_mass::Real)
    all(isfinite, current) || throw(ArgumentError("position must be finite"))
    checked_log = value -> checked_logdensity(logdensity, value)
    checked_grad = value -> checked_gradient(gradient, value)
    Float64.(run_program("relativistic_multinomial_hmc_step!", source,
        checked_log, checked_grad, Float64(step_size), steps, current, mass,
        Float64(relativistic_mass)))
end

function _corrected_isotropic_relativistic_momentum!(source::AbstractRandomSource,
        dimension::Int, relativistic_mass::Float64)
    radius = _relativistic_radius!(source, dimension, relativistic_mass)
    direction = [standard_normal!(source) for _ in 1:dimension]
    direction_norm = norm(direction)
    isfinite(direction_norm) && direction_norm > 0 ||
        throw(DomainError(direction, "spherical direction draw must be nonzero"))
    (radius / direction_norm) .* direction
end

function _checked_certified_step(integrator, q, p, step_size)
    result = integrator(q, p, step_size)
    result isa Tuple && length(result) == 3 ||
        throw(ArgumentError("integrator must return (position, momentum, certificate)"))
    next_q, next_p, certificate = result
    certificate isa ImplicitSolveCertificate ||
        throw(ArgumentError("integrator must return an ImplicitSolveCertificate"))
    certifies_exact_solver(certificate) ||
        throw(ArgumentError("implicit solve is approximate or lacks global validity witnesses"))
    Float64.(next_q), Float64.(next_p)
end

"""Solve the two generalized-leapfrog implicit equations by fixed-point iteration.

The returned certificate reports the observed residuals. A positive tolerance
is approximation data and is intentionally rejected by the exact certified
sampler. Set the global witness flags only when they have been established for
the complete solver family, not merely for this run.
"""
function fixed_point_generalized_leapfrog(position_derivative,
        momentum_derivative, position::AbstractVector{<:Real},
        momentum::AbstractVector{<:Real}, step_size::Real;
        max_iterations::Integer=100, atol::Real=1e-10, rtol::Real=1e-8,
        unique::Bool=false, reversible::Bool=false,
        volume_preserving::Bool=false)
    max_iterations > 0 || throw(ArgumentError("max_iterations must be positive"))
    ε, absolute, relative = Float64(step_size), Float64(atol), Float64(rtol)
    isfinite(ε) || throw(ArgumentError("step size must be finite"))
    isfinite(absolute) && absolute >= 0 ||
        throw(ArgumentError("atol must be finite and nonnegative"))
    isfinite(relative) && relative >= 0 ||
        throw(ArgumentError("rtol must be finite and nonnegative"))
    q, p = Float64.(position), Float64.(momentum)
    length(q) == length(p) || throw(DimensionMismatch("position and momentum"))
    isempty(q) && throw(ArgumentError("state cannot be empty"))
    all(isfinite, q) && all(isfinite, p) ||
        throw(ArgumentError("state must be finite"))

    p_half = copy(p)
    for _ in 1:max_iterations
        candidate = p .- (ε / 2) .* Float64.(position_derivative(q, p_half))
        length(candidate) == length(p) ||
            throw(DimensionMismatch("position derivative"))
        all(isfinite, candidate) || throw(DomainError(candidate, "half momentum"))
        residual = norm(candidate .- p_half)
        p_half = candidate
        residual <= absolute + relative * max(norm(p_half), 1.0) && break
    end

    q_next = copy(q)
    initial_velocity = Float64.(momentum_derivative(q, p_half))
    length(initial_velocity) == length(q) ||
        throw(DimensionMismatch("momentum derivative"))
    for _ in 1:max_iterations
        terminal_velocity = Float64.(momentum_derivative(q_next, p_half))
        length(terminal_velocity) == length(q) ||
            throw(DimensionMismatch("momentum derivative"))
        candidate = q .+ (ε / 2) .* (initial_velocity .+ terminal_velocity)
        all(isfinite, candidate) || throw(DomainError(candidate, "next position"))
        residual = norm(candidate .- q_next)
        q_next = candidate
        residual <= absolute + relative * max(norm(q_next), 1.0) && break
    end

    half_update = p .- (ε / 2) .* Float64.(position_derivative(q, p_half))
    position_update = q .+ (ε / 2) .* (initial_velocity .+
        Float64.(momentum_derivative(q_next, p_half)))
    half_residual = norm(p_half .- half_update)
    position_residual = norm(q_next .- position_update)
    p_next = p_half .- (ε / 2) .* Float64.(position_derivative(q_next, p_half))
    certificate = certify_implicit_solve(half_residual, half_residual,
        position_residual, position_residual; unique=unique,
        reversible=reversible, volume_preserving=volume_preserving)
    q_next, p_next, certificate
end

function _certified_relativistic_multinomial_hmc_step!(source::AbstractRandomSource,
        hamiltonian, metric_factor, integrator, step_size::Float64, steps::Integer,
        current::AbstractVector{<:Real}, relativistic_mass::Float64)
    steps > 0 || throw(ArgumentError("trajectory length must be positive"))
    q0 = Float64.(current)
    isempty(q0) && throw(ArgumentError("position cannot be empty"))
    factor = Matrix{Float64}(metric_factor(q0))
    size(factor) == (length(q0), length(q0)) ||
        throw(DimensionMismatch("metric factor dimension"))
    abs(det(factor)) > 0 || throw(ArgumentError("metric factor must be invertible"))
    z = _corrected_isotropic_relativistic_momentum!(source, length(q0),
        relativistic_mass)
    p0 = factor \ z # corrected p = A⁻¹z transport
    origin = Int(draw_below!(source, steps + 1))
    trajectory = Vector{Tuple{Vector{Float64},Vector{Float64}}}(undef, steps + 1)
    for index in 0:steps
        q, p = copy(q0), copy(p0)
        signed_step = index >= origin ? step_size : -step_size
        for _ in 1:abs(index - origin)
            q, p = _checked_certified_step(integrator, q, p, signed_step)
        end
        trajectory[index + 1] = (q, p)
    end
    logweights = [-Float64(hamiltonian(q, p)) for (q, p) in trajectory]
    all(isfinite, logweights) || throw(DomainError(logweights, "Hamiltonian must be finite"))
    weights = exp.(logweights .- maximum(logweights))
    draw = uniform_unit!(source) * sum(weights)
    cumulative = 0.0
    for (index, weight) in pairs(weights)
        cumulative += weight
        draw < cumulative && return trajectory[index][1]
    end
    trajectory[end][1]
end

function certified_relativistic_multinomial_hmc_step!(source::AbstractRandomSource,
        hamiltonian, metric_factor, integrator, step_size::Real, steps::Integer,
        current::AbstractVector{<:Real}, relativistic_mass::Real)
    Float64.(run_program("certified_relativistic_multinomial_hmc_step!", source,
        hamiltonian, metric_factor, integrator, Float64(step_size), steps,
        current, Float64(relativistic_mass)))
end

function _run_coupled(name, source::AbstractRandomSource, logdensity, gradient,
        step_size::Real, steps::Integer, scale::Real, hmc_weight::Real,
        left::AbstractVector{<:Real}, right::AbstractVector{<:Real})
    length(left) == length(right) || throw(DimensionMismatch("coupled states"))
    isempty(left) && throw(ArgumentError("position cannot be empty"))
    step_size > 0 && steps > 0 || throw(ArgumentError("invalid HMC trajectory"))
    scale > 0 || throw(ArgumentError("RWMH scale must be positive"))
    0 <= hmc_weight <= 1 || throw(ArgumentError("HMC weight must lie in [0,1]"))
    checked_log = value -> checked_logdensity(logdensity, value)
    checked_grad = value -> checked_gradient(gradient, value)
    result = run_program(name, source, checked_log, checked_grad, Float64(step_size),
        steps, Float64(scale), Float64(hmc_weight), left, right)
    (Float64.(result[1]), Float64.(result[2]))
end

coupled_multinomial_hmc_step!(source::AbstractRandomSource, logdensity, gradient,
    step_size::Real, steps::Integer, left::AbstractVector{<:Real},
    right::AbstractVector{<:Real}) =
    _run_coupled("coupled_multinomial_hmc_step!", source, logdensity, gradient,
        step_size, steps, 1.0, 1.0, left, right)

coupled_gaussian_rwmh_step!(source::AbstractRandomSource, logdensity, scale::Real,
    left::AbstractVector{<:Real}, right::AbstractVector{<:Real}) =
    _run_coupled("coupled_gaussian_rwmh_step!", source, logdensity, identity,
        1.0, 1, scale, 0.0, left, right)

xu21_coupled_step!(source::AbstractRandomSource, logdensity, gradient,
    step_size::Real, steps::Integer, scale::Real, hmc_weight::Real,
    left::AbstractVector{<:Real}, right::AbstractVector{<:Real}) =
    _run_coupled("xu21_coupled_step!", source, logdensity, gradient, step_size,
        steps, scale, hmc_weight, left, right)

end
