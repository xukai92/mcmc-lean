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

const SUPPORTED_INPUT_KINDS = Set([
    "source", "log-density", "gradient", "hamiltonian", "metric-factor",
    "integrator", "nat", "nat-vector", "nat-matrix", "real",
    "real-vector", "real-matrix"])

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
    input_names = Set{String}()
    for raw in input_node[2:end]
        input = items(aslist(raw))
        length(input) == 3 && atom(input[1]) == "input" || error("invalid IR input")
        kind, name = atom(input[2]), atom(input[3])
        kind in SUPPORTED_INPUT_KINDS || error("unsupported IR input kind: $kind")
        name in input_names && error("duplicate IR input name: $name")
        push!(input_names, name)
        push!(inputs, (kind, name))
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
    descriptor.transform in ("positive-log", "open-unit-artanh") ||
        error("unsupported scalar transform: $(descriptor.transform)")
    descriptor
end

struct DynamicTreeDescriptor
    name::String
    builder::String
    trace_policy::String
    root_encoding::String
    stop_rule::String
    subtree_policy::String
    selection_policy::String
    failure_policy::String
end

struct NUTSTreeProgramDescriptor
    name::String
    max_depth::Int
    selection::String
    termination::String
    failure_policy::String
    recursion::String
    candidates::String
end

function decode_nuts_tree_program(node::SList)
    values = items(node)
    length(values) == 8 && atom(values[1]) == "nuts-tree-program" ||
        error("invalid NUTS tree program")
    max_depth = parse(Int, atom(values[3]))
    max_depth > 0 || error("NUTS tree depth must be positive")
    descriptor = NUTSTreeProgramDescriptor(atom(values[2]), max_depth,
        (atom(value) for value in values[4:end])...)
    descriptor.selection in ("multinomial", "slice") ||
        error("unsupported NUTS selection: $(descriptor.selection)")
    descriptor.termination in ("classic", "generalized", "strict-generalized") ||
        error("unsupported NUTS termination: $(descriptor.termination)")
    descriptor.failure_policy == "checked-or-identity" ||
        error("unsupported NUTS failure policy: $(descriptor.failure_policy)")
    descriptor.recursion == "online-early-exit" ||
        error("unsupported NUTS recursion: $(descriptor.recursion)")
    descriptor.candidates == "ordered-candidate-occurrences" ||
        error("unsupported NUTS candidate semantics: $(descriptor.candidates)")
    descriptor
end

"""Leaf syntax consumed by the generic NUTS tree-program interpreter."""
struct NUTSTreeLeaf{P}
    phase::P
end

"""Binary tree syntax consumed by the generic NUTS tree-program interpreter."""
struct NUTSTreeNode{L,R}
    left::L
    right::R
end

"""Exact structural result of a decoded Lean NUTS tree program."""
struct NUTSSubtreeResult{P}
    visited_leaves::Int
    candidates::Vector{P}
    continues::Bool
end

"""Result of the bounded outer direction-trace interpreter."""
struct NUTSOuterResult{P}
    left::P
    right::P
    candidates::Vector{P}
    completed_depth::Int
    continues::Bool
end

_tree_leftmost(tree::NUTSTreeLeaf) = tree.phase
_tree_leftmost(tree::NUTSTreeNode) = _tree_leftmost(tree.left)
_tree_rightmost(tree::NUTSTreeLeaf) = tree.phase
_tree_rightmost(tree::NUTSTreeNode) = _tree_rightmost(tree.right)

"""Build the directional phase tree defined by Lean's NUTS tree program."""
function build_nuts_phase_tree(program::NUTSTreeProgramDescriptor,
        start, grow_right::Bool, depth::Integer, advance)
    0 <= depth <= program.max_depth || throw(ArgumentError(
        "NUTS subtree depth must lie in 0:$(program.max_depth)"))
    depth == 0 && return NUTSTreeLeaf(advance(grow_right, start))
    first = build_nuts_phase_tree(
        program, start, grow_right, depth - 1, advance)
    second_start = grow_right ? _tree_rightmost(first) : _tree_leftmost(first)
    second = build_nuts_phase_tree(
        program, second_start, grow_right, depth - 1, advance)
    grow_right ? NUTSTreeNode(first, second) : NUTSTreeNode(second, first)
end

"""Interpret Lean's versioned online-early-exit NUTS subtree semantics.

The callbacks supply phase-local numerical decisions. Their agreement with
ideal-real decisions is a separate certificate obligation; this interpreter
owns only the structural control flow and ordered candidate occurrences.
"""
function interpret_nuts_subtree(program::NUTSTreeProgramDescriptor,
        tree::NUTSTreeLeaf, leaf_continues, endpoint_turns)
    continues = Bool(leaf_continues(tree.phase))
    candidates = continues ? [tree.phase] : typeof(tree.phase)[]
    NUTSSubtreeResult(1, candidates, continues)
end

"""Interpret Lean's checked bounded outer-doubling trace.

Failed subtrees and completed outer U-turns stop before admitting the proposed
subtree. This is the checked Reference policy, not an assertion that ordinary
production NUTS is reroot invariant.
"""
function interpret_nuts_outer_trace(program::NUTSTreeProgramDescriptor,
        initial, directions::AbstractVector{Bool}, advance,
        leaf_continues, endpoint_turns)
    length(directions) <= program.max_depth || throw(ArgumentError(
        "direction trace exceeds maximum depth $(program.max_depth)"))
    state = NUTSOuterResult(initial, initial, [initial], 0, true)
    for (depth, grow_right) in enumerate(directions)
        state.continues || break
        start = grow_right ? state.right : state.left
        tree = build_nuts_phase_tree(
            program, start, grow_right, depth - 1, advance)
        subtree = interpret_nuts_subtree(
            program, tree, leaf_continues, endpoint_turns)
        if !subtree.continues
            state = NUTSOuterResult(state.left, state.right,
                state.candidates, state.completed_depth, false)
            break
        end
        new_left = grow_right ? state.left : _tree_leftmost(tree)
        new_right = grow_right ? _tree_rightmost(tree) : state.right
        if Bool(endpoint_turns(new_left, new_right))
            state = NUTSOuterResult(state.left, state.right,
                state.candidates, state.completed_depth, false)
            break
        end
        candidates = grow_right ?
            vcat(state.candidates, subtree.candidates) :
            vcat(subtree.candidates, state.candidates)
        state = NUTSOuterResult(new_left, new_right, candidates,
            state.completed_depth + 1, true)
    end
    state
end

"""Consume one unit mark using ordered multinomial candidate occurrences."""
function select_nuts_candidate(program::NUTSTreeProgramDescriptor,
        candidates::AbstractVector, logweight, unit::Real)
    program.selection == "multinomial" || throw(ArgumentError(
        "the first checked NUTS Reference supports multinomial selection"))
    isempty(candidates) && throw(ArgumentError("NUTS candidates cannot be empty"))
    u = Float64(unit)
    isfinite(u) && 0 <= u < 1 || throw(ArgumentError(
        "NUTS selection mark must lie in [0, 1)"))
    logs = Float64[logweight(candidate) for candidate in candidates]
    all(value -> isfinite(value) || value == -Inf, logs) ||
        throw(DomainError(logs, "NUTS log weights must be finite or -Inf"))
    top = maximum(logs)
    isfinite(top) || throw(DomainError(logs,
        "at least one NUTS candidate must have positive weight"))
    weights = exp.(logs .- top)
    threshold = u * sum(weights)
    fallback = candidates[findlast(>(0), weights)]
    for (candidate, weight) in zip(candidates, weights)
        weight > 0 || continue
        threshold < weight && return candidate
        threshold -= weight
    end
    fallback
end

"""Interpret the complete deterministic checked-NUTS transition skeleton."""
function interpret_nuts_transition(program::NUTSTreeProgramDescriptor,
        initial, directions::AbstractVector{Bool}, selection_unit::Real,
        advance, leaf_continues, endpoint_turns, logweight)
    tree = interpret_nuts_outer_trace(program, initial, directions,
        advance, leaf_continues, endpoint_turns)
    selected = select_nuts_candidate(
        program, tree.candidates, logweight, selection_unit)
    (; tree, selected)
end

"""Interpret and globally check every rooted row of one completed orbit.

The Boolean is exactly the executable root-retention/reroot-equality predicate
used by Lean's checked-or-identity semantics. No row is selected when it is
false.
"""
function interpret_checked_nuts_rows(program::NUTSTreeProgramDescriptor,
        positions::AbstractVector{<:AbstractVector{<:Real}},
        momenta::AbstractVector{<:AbstractVector{<:Real}},
        directions::AbstractVector{Bool})
    length(directions) <= program.max_depth || throw(ArgumentError(
        "direction trace exceeds maximum depth $(program.max_depth)"))
    rows = recursive_doubling_rows(positions, momenta, directions)
    root_retained = all(root -> root in rows[root], eachindex(rows))
    reroot_equal = root_retained && all(eachindex(rows)) do root
        all(leaf -> rows[leaf] == rows[root], rows[root])
    end
    (; rows, valid=root_retained && reroot_equal)
end

"""Execute checked target-weighted selection, or return the current root.

The selection mark is consumed only for a globally valid row family. This
matches the Lean identity branch and makes trace behavior observable.
"""
function checked_nuts_or_identity_select!(source::AbstractRandomSource,
        program::NUTSTreeProgramDescriptor,
        positions::AbstractVector{<:AbstractVector{<:Real}},
        momenta::AbstractVector{<:AbstractVector{<:Real}},
        directions::AbstractVector{Bool}, current::Integer, logweight)
    checked = interpret_checked_nuts_rows(
        program, positions, momenta, directions)
    1 <= current <= length(checked.rows) || throw(BoundsError(checked.rows, current))
    checked.valid || return Int(current)
    candidates = checked.rows[current]
    select_nuts_candidate(program, candidates,
        index -> logweight(positions[index], momenta[index]),
        uniform_unit!(source))
end

"""Build and interpret one typed directional NUTS subtree declaration."""
function interpret_nuts_directional_subtree(
        program::NUTSTreeProgramDescriptor, start, grow_right::Bool,
        depth::Integer, advance, leaf_continues, endpoint_turns)
    tree = build_nuts_phase_tree(
        program, start, grow_right, depth, advance)
    interpret_nuts_subtree(program, tree, leaf_continues, endpoint_turns)
end

function interpret_nuts_subtree(program::NUTSTreeProgramDescriptor,
        tree::NUTSTreeNode, leaf_continues, endpoint_turns)
    left = interpret_nuts_subtree(
        program, tree.left, leaf_continues, endpoint_turns)
    left.continues || return left
    right = interpret_nuts_subtree(
        program, tree.right, leaf_continues, endpoint_turns)
    candidates = vcat(left.candidates, right.candidates)
    right.continues || return NUTSSubtreeResult(
        left.visited_leaves + right.visited_leaves, candidates, false)
    continues = !Bool(endpoint_turns(
        _tree_leftmost(tree.left), _tree_rightmost(tree.right)))
    NUTSSubtreeResult(
        left.visited_leaves + right.visited_leaves, candidates, continues)
end

function decode_dynamic_tree(node::SList)
    values = items(node)
    length(values) == 9 && atom(values[1]) == "dynamic-tree" ||
        error("invalid dynamic-tree descriptor")
    descriptor = DynamicTreeDescriptor((atom(value) for value in values[2:end])...)
    descriptor.builder == "recursive-doubling" ||
        error("unsupported dynamic-tree builder: $(descriptor.builder)")
    descriptor.trace_policy == "fair-direction-bits" ||
        error("unsupported dynamic-tree trace policy: $(descriptor.trace_policy)")
    descriptor.root_encoding == "lsb-first-grow-right-zero" ||
        error("unsupported dynamic-tree root encoding: $(descriptor.root_encoding)")
    descriptor.stop_rule == "endpoint-uturn" ||
        error("unsupported dynamic-tree stop rule: $(descriptor.stop_rule)")
    descriptor.subtree_policy == "recursive-exclusion" ||
        error("unsupported dynamic-tree subtree policy: $(descriptor.subtree_policy)")
    descriptor.selection_policy == "eligible-count-streaming" ||
        error("unsupported dynamic-tree selection policy: $(descriptor.selection_policy)")
    descriptor.failure_policy == "checked-or-identity" ||
        error("unsupported dynamic-tree failure policy: $(descriptor.failure_policy)")
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
    dynamic_trees = Dict{String,DynamicTreeDescriptor}()
    nuts_tree_programs = Dict{String,NUTSTreeProgramDescriptor}()
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
        elseif tag == "dynamic-tree"
            descriptor = decode_dynamic_tree(aslist(node))
            haskey(dynamic_trees, descriptor.name) &&
                error("duplicate dynamic-tree descriptor: $(descriptor.name)")
            dynamic_trees[descriptor.name] = descriptor
        elseif tag == "nuts-tree-program"
            descriptor = decode_nuts_tree_program(aslist(node))
            haskey(nuts_tree_programs, descriptor.name) &&
                error("duplicate NUTS tree program: $(descriptor.name)")
            nuts_tree_programs[descriptor.name] = descriptor
        else
            error("unknown top-level IR declaration: $tag")
        end
    end
    programs, targets, schedules, transforms, dynamic_trees, nuts_tree_programs
end

# Retain the program-only loader for downstream callers while the artifact now
# also carries restricted target declarations.
load_programs(path::String) = first(load_artifact(path))

const PROGRAMS, TARGETS, SCHEDULES, TRANSFORMS, DYNAMIC_TREES,
    NUTS_TREE_PROGRAMS =
    load_artifact(joinpath(@__DIR__, "Samplers.ir"))

"""Canonical declaration names decoded from the current Lean-emitted artifact.

The returned collections are sorted copies. They expose artifact coverage for
documentation and consistency checks without granting callers mutation access
to the interpreter registries.
"""
artifact_facets() = (
    programs=sort!(collect(keys(PROGRAMS))),
    targets=sort!(collect(keys(TARGETS))),
    schedules=sort!(collect(keys(SCHEDULES))),
    transforms=sort!(collect(keys(TRANSFORMS))),
    dynamic_trees=sort!(collect(keys(DYNAMIC_TREES))),
    nuts_tree_programs=sort!(collect(keys(NUTS_TREE_PROGRAMS))),
)
