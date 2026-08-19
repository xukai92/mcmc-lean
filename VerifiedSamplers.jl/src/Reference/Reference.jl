module Reference

using LinearAlgebra

using ..Runtime: AbstractRandomSource, draw_below!, standard_normal!,
    uniform_unit!, checked_positive_float, checked_positive_count,
    checked_finite_float
using ..Certificates: ImplicitSolveCertificate, certify_implicit_solve,
    certifies_exact_solver

export categorical_index!, integer_slice_step!, bounded_slice_step!, stepping_out_slice_step!, sheared_birth_death_step!, spatial_birth_death_step!, finite_mh_step!, two_state_mh_step!, gaussian_rwmh_step!, scalar_hmc_step!, vector_hmc_step!, metric_hmc_step!, multinomial_hmc_step!, metric_multinomial_hmc_step!, categorical_dhmc_step!,
    finite_hmm_particle_gibbs_step!,
    relativistic_multinomial_hmc_step!,
    fixed_point_generalized_leapfrog,
    fixed_point_generalized_leapfrog_trace,
    FixedPointGeneralizedLeapfrogTrace,
    certified_relativistic_multinomial_hmc_step!,
    dynamic_select_float!, streaming_eligible_select!, recursive_doubling_rows,
    NUTSTreeLeaf, NUTSTreeNode, NUTSSubtreeResult, build_nuts_phase_tree,
    NUTSOuterResult, interpret_nuts_subtree, interpret_nuts_directional_subtree,
    interpret_nuts_outer_trace, select_nuts_candidate, interpret_nuts_transition,
    coupled_multinomial_hmc_step!, coupled_gaussian_rwmh_step!, xu21_coupled_step!,
    IR_FORMAT_VERSION

const IR_FORMAT_VERSION = 20

"""Stable target-weighted selection from a supplied candidate index set.

The surrounding checked-tree layer is responsible for reroot certification.
"""
function dynamic_select_float!(source::AbstractRandomSource,
        candidates::AbstractVector{<:Integer},
        logweights::AbstractVector{<:Real})
    isempty(candidates) && throw(ArgumentError("candidate set cannot be empty"))
    length(candidates) == length(logweights) ||
        throw(DimensionMismatch("candidate indices and weights must match"))
    values = Float64.(logweights)
    all(isfinite, values) || throw(DomainError(logweights,
        "dynamic target log weights must be finite"))
    offset = maximum(values)
    weights = exp.(values .- offset)
    target = uniform_unit!(source) * sum(weights)
    cumulative = 0.0
    for index in eachindex(weights)
        cumulative += weights[index]
        target < cumulative && return Int(candidates[index])
    end
    Int(last(candidates))
end

"""Interpret the generated eligible-count streaming selection policy.

Each segment is an already filtered completed subtree. A local uniform
representative is drawn and then merged with the accumulated representative
in proportion to the two eligible counts. Empty segments consume no draws.
The result is `nothing` exactly when every segment is empty.
"""
function streaming_eligible_select!(source::AbstractRandomSource,
        segments::AbstractVector{<:AbstractVector{<:Integer}})
    representative = nothing
    total = 0
    for segment in segments
        count = length(segment)
        count == 0 && continue
        local_index = Int(draw_below!(source, count)) + 1
        local_representative = Int(segment[local_index])
        if total == 0
            representative = local_representative
        else
            ticket = Int(draw_below!(source, total + count))
            ticket >= total && (representative = local_representative)
        end
        total += count
    end
    representative
end

"""Direct interpreter for the generated recursive-doubling row builder.

Indices in the returned rows are Julia's one-based counterpart of the Lean
builder's `Fin count` indices. Global reroot certification remains a separate
operation so rejected diagnostic rows stay observable.
"""
function recursive_doubling_rows(
        positions::AbstractVector{<:AbstractVector{<:Real}},
        momenta::AbstractVector{<:AbstractVector{<:Real}},
        directions::AbstractVector{Bool})
    length(positions) == length(momenta) ||
        throw(DimensionMismatch("position and momentum trajectories must match"))
    isempty(positions) && throw(ArgumentError("trajectory cannot be empty"))
    dimension = length(first(positions))
    dimension > 0 || throw(ArgumentError("phase-space dimension cannot be zero"))
    all(point -> length(point) == dimension, positions) &&
        all(point -> length(point) == dimension, momenta) ||
        throw(DimensionMismatch("all phase points must have the same dimension"))
    q = [Float64.(point) for point in positions]
    p = [Float64.(point) for point in momenta]
    all(point -> all(isfinite, point), q) &&
        all(point -> all(isfinite, point), p) ||
        throw(DomainError((positions, momenta), "trajectory must be finite"))

    turns(left, right) = begin
        displacement = q[right] .- q[left]
        dot(displacement, p[left]) < 0 || dot(displacement, p[right]) < 0
    end
    function subtree_turns(left, right)
        left == right && return false
        turns(left, right) && return true
        middle = (left + right) ÷ 2
        subtree_turns(left, middle) || subtree_turns(middle + 1, right)
    end

    count = length(q)
    rows = Vector{Vector{Int}}(undef, count)
    for root in 1:count
        left = right = root
        for depth in eachindex(directions)
            width = 1 << (depth - 1)
            grow_right = directions[depth]
            proposed_left = grow_right ? left : left - width
            proposed_right = grow_right ? right + width : right
            proposed_left >= 1 && proposed_right <= count || break
            new_left = grow_right ? right + 1 : proposed_left
            new_right = grow_right ? proposed_right : left - 1
            (subtree_turns(new_left, new_right) ||
                turns(proposed_left, proposed_right)) && break
            left, right = proposed_left, proposed_right
        end
        rows[root] = collect(left:right)
    end
    rows
end

recursive_doubling_rows(positions::AbstractVector{<:Real},
        momenta::AbstractVector{<:Real}, directions::AbstractVector{Bool}) =
    recursive_doubling_rows([[Float64(value)] for value in positions],
        [[Float64(value)] for value in momenta], directions)

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
        width::Real, current::Real, max_steps::Integer, max_shrink::Integer;
        threshold_observer=(base, uniform, log_uniform, threshold) -> nothing,
        comparison_observer=(kind, position, value, threshold) -> nothing)
    w, x = Float64(width), Float64(current)
    isfinite(w) && w > 0 || throw(ArgumentError("width must be finite and positive"))
    isfinite(x) || throw(ArgumentError("current state must be finite"))
    max_steps >= 0 || throw(ArgumentError("max_steps must be nonnegative"))
    max_shrink > 0 || throw(ArgumentError("max_shrink must be positive"))
    base = Float64(logdensity(x))
    isfinite(base) || throw(ArgumentError("current log density must be finite"))
    uniform = uniform_unit!(source)
    log_uniform = log(uniform)
    threshold = base + log_uniform
    threshold_observer(base, uniform, log_uniform, threshold)
    left = x - w * uniform_unit!(source)
    right = left + w
    left_steps = Int(floor(uniform_unit!(source) * (max_steps + 1)))
    right_steps = max_steps - left_steps
    while left_steps > 0
        value = Float64(logdensity(left))
        (isfinite(value) || value == -Inf) ||
            throw(ArgumentError("log density must be finite or -Inf"))
        comparison_observer(:stopBelow, left, value, threshold)
        value <= threshold && break
        left -= w
        left_steps -= 1
    end
    while right_steps > 0
        value = Float64(logdensity(right))
        (isfinite(value) || value == -Inf) ||
            throw(ArgumentError("log density must be finite or -Inf"))
        comparison_observer(:stopBelow, right, value, threshold)
        value <= threshold && break
        right += w
        right_steps -= 1
    end
    for _ in 1:max_shrink
        proposal = left + (right - left) * uniform_unit!(source)
        value = Float64(logdensity(proposal))
        (isfinite(value) || value == -Inf) ||
            throw(ArgumentError("log density must be finite or -Inf"))
        comparison_observer(:acceptAbove, proposal, value, threshold)
        value >= threshold && return proposal
        proposal < x ? (left = proposal) : (right = proposal)
    end
    # Total checked fallback: exhausting the shrinkage-attempt budget leaves
    # the chain at its current state. Exhausting a replay source itself remains
    # a malformed-trace error.
    x
end

"""Reference nonlinear reversible-jump birth/death update.

`nothing` denotes the zero-dimensional model. A birth draws the proved
uniform auxiliary pair and applies `(u₁,u₂) ↦ (2u₁+8u₂³,2u₂)`;
a death deterministically returns to `nothing`. The formal density correction
makes both directions accept with probability one.
"""
function sheared_birth_death_step!(source::AbstractRandomSource, current)
    current === nothing || current isa Tuple{<:Real,<:Real} ||
        throw(ArgumentError("RJ state must be nothing or a pair of reals"))
    current === nothing || return nothing
    u1 = 2.0 * uniform_unit!(source) - 1.0
    u2 = 2.0 * uniform_unit!(source) - 1.0
    (2.0 * u1 + 8.0 * u2^3, 2.0 * u2)
end

"""Reference three-dimensional product-scaled birth/death update."""
function spatial_birth_death_step!(source::AbstractRandomSource, current)
    current === nothing ||
        (current isa Tuple && length(current) == 3 && all(x -> x isa Real, current)) ||
        throw(ArgumentError("spatial RJ state must be nothing or three reals"))
    current === nothing || return nothing
    ntuple(_ -> 4.0 * uniform_unit!(source) - 2.0, 3)
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

function valid_input_value(kind::String, value)
    kind == "source" && return value isa AbstractRandomSource
    (kind == "log-density" || kind == "gradient") &&
        return applicable(value, 0.0) || applicable(value, Float64[])
    kind == "hamiltonian" && return applicable(value, Float64[], Float64[])
    kind == "metric-factor" && return applicable(value, Float64[])
    kind == "integrator" &&
        return applicable(value, Float64[], Float64[], 0.0)
    kind == "nat" && return value isa Integer && value >= 0
    kind == "nat-vector" &&
        return value isa AbstractVector{<:Integer}
    kind == "nat-matrix" && return value isa AbstractVector &&
        all(row -> row isa AbstractVector{<:Integer}, value)
    kind == "real" && return value isa Real
    kind == "real-vector" && return value isa AbstractVector{<:Real}
    kind == "real-matrix" && return value isa AbstractMatrix{<:Real}
    false
end

function run_program(name::String, arguments...)
    program = get(PROGRAMS, name, nothing)
    program === nothing && error("unknown IR program: $name")
    length(arguments) == length(program.inputs) || throw(ArgumentError("IR argument count"))
    env = Dict{String,Any}()
    for ((input_kind, input_name), value) in zip(program.inputs, arguments)
        valid_input_value(input_kind, value) ||
            throw(ArgumentError("invalid $input_kind input: $input_name"))
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
    checked_positive_float(scale, "scale")
    checked_finite_float(current, "current state")
    checked = value -> checked_logdensity(logdensity, value)
    Float64(run_program("gaussian_rwmh_step!", source, checked, scale, current))
end

"""Float64 interpretation of the serialized scalar one-step HMC program."""
function scalar_hmc_step!(source::AbstractRandomSource, logdensity, gradient,
        step_size::Float64, steps::Integer, current::Float64)
    checked_positive_float(step_size, "step size")
    checked_positive_count(steps, "leapfrog steps")
    checked_finite_float(current, "current state")
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

"""One concrete derivative callback invocation made by the reference solver."""
struct FixedPointCallbackEvaluation
    kind::Symbol
    position::Vector{Float64}
    momentum::Vector{Float64}
    value::Vector{Float64}
end

"""One rounded `base + scale*callback` update, retaining every callback
vector consumed by that arithmetic expression."""
struct FixedPointAffineUpdateEvaluation
    kind::Symbol
    base::Vector{Float64}
    scale::Float64
    callbacks::Vector{Vector{Float64}}
    computed_update::Vector{Float64}
end

"""Final iterates, updates, and every callback invoked by both implicit loops."""
struct FixedPointGeneralizedLeapfrogTrace
    half_momentum::Vector{Float64}
    half_callback::Vector{Float64}
    half_update::Vector{Float64}
    next_position::Vector{Float64}
    position_callback::Vector{Float64}
    position_update::Vector{Float64}
    callback_evaluations::Vector{FixedPointCallbackEvaluation}
    affine_updates::Vector{FixedPointAffineUpdateEvaluation}
    half_iterations::Int
    position_iterations::Int
end

"""Execute the generalized-leapfrog loops and retain their final updates."""
function _fixed_point_generalized_leapfrog_trace(position_derivative,
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
    callback_evaluations = FixedPointCallbackEvaluation[]
    affine_updates = FixedPointAffineUpdateEvaluation[]

    p_half = copy(p)
    half_iterations = 0
    for iteration in 1:max_iterations
        half_iterations = iteration
        derivative = Float64.(position_derivative(q, p_half))
        push!(callback_evaluations, FixedPointCallbackEvaluation(:position,
            copy(q), copy(p_half), copy(derivative)))
        candidate = p .- (ε / 2) .* derivative
        push!(affine_updates, FixedPointAffineUpdateEvaluation(:half_momentum,
            copy(p), -(ε / 2), [copy(derivative)], copy(candidate)))
        length(candidate) == length(p) ||
            throw(DimensionMismatch("position derivative"))
        all(isfinite, candidate) || throw(DomainError(candidate, "half momentum"))
        residual = norm(candidate .- p_half)
        p_half = candidate
        residual <= absolute + relative * max(norm(p_half), 1.0) && break
    end

    q_next = copy(q)
    position_iterations = 0
    initial_velocity = Float64.(momentum_derivative(q, p_half))
    push!(callback_evaluations, FixedPointCallbackEvaluation(:momentum,
        copy(q), copy(p_half), copy(initial_velocity)))
    length(initial_velocity) == length(q) ||
        throw(DimensionMismatch("momentum derivative"))
    for iteration in 1:max_iterations
        position_iterations = iteration
        terminal_velocity = Float64.(momentum_derivative(q_next, p_half))
        push!(callback_evaluations, FixedPointCallbackEvaluation(:momentum,
            copy(q_next), copy(p_half), copy(terminal_velocity)))
        length(terminal_velocity) == length(q) ||
            throw(DimensionMismatch("momentum derivative"))
        candidate = q .+ (ε / 2) .* (initial_velocity .+ terminal_velocity)
        push!(affine_updates, FixedPointAffineUpdateEvaluation(:position,
            copy(q), ε / 2, [copy(initial_velocity), copy(terminal_velocity)],
            copy(candidate)))
        all(isfinite, candidate) || throw(DomainError(candidate, "next position"))
        residual = norm(candidate .- q_next)
        q_next = candidate
        residual <= absolute + relative * max(norm(q_next), 1.0) && break
    end

    half_callback = Float64.(position_derivative(q, p_half))
    push!(callback_evaluations, FixedPointCallbackEvaluation(:position,
        copy(q), copy(p_half), copy(half_callback)))
    half_update = p .- (ε / 2) .* half_callback
    push!(affine_updates, FixedPointAffineUpdateEvaluation(:half_momentum,
        copy(p), -(ε / 2), [copy(half_callback)], copy(half_update)))
    final_velocity = Float64.(momentum_derivative(q_next, p_half))
    push!(callback_evaluations, FixedPointCallbackEvaluation(:momentum,
        copy(q_next), copy(p_half), copy(final_velocity)))
    position_callback = initial_velocity .+ final_velocity
    position_update = q .+ (ε / 2) .* position_callback
    push!(affine_updates, FixedPointAffineUpdateEvaluation(:position,
        copy(q), ε / 2, [copy(initial_velocity), copy(final_velocity)],
        copy(position_update)))
    half_residual = norm(p_half .- half_update)
    position_residual = norm(q_next .- position_update)
    final_position_derivative = Float64.(position_derivative(q_next, p_half))
    push!(callback_evaluations, FixedPointCallbackEvaluation(:position,
        copy(q_next), copy(p_half), copy(final_position_derivative)))
    p_next = p_half .- (ε / 2) .* final_position_derivative
    push!(affine_updates, FixedPointAffineUpdateEvaluation(:final_momentum,
        copy(p_half), -(ε / 2), [copy(final_position_derivative)], copy(p_next)))
    certificate = certify_implicit_solve(half_residual, half_residual,
        position_residual, position_residual; unique=unique,
        reversible=reversible, volume_preserving=volume_preserving)
    trace = FixedPointGeneralizedLeapfrogTrace(copy(p_half),
        copy(half_callback), copy(half_update), copy(q_next),
        copy(position_callback), copy(position_update), callback_evaluations,
        affine_updates, half_iterations, position_iterations)
    q_next, p_next, certificate, trace
end

"""Solve the two generalized-leapfrog implicit equations by fixed-point iteration.

The returned certificate reports the observed residuals. A positive tolerance
is approximation data and is intentionally rejected by the exact certified
sampler. Set the global witness flags only when they have been established for
the complete solver family, not merely for this run.
"""
function fixed_point_generalized_leapfrog(args...; kwargs...)
    q, p, certificate, _ = _fixed_point_generalized_leapfrog_trace(
        args...; kwargs...)
    q, p, certificate
end


"""Run the reference solver while returning its auditable final-update trace."""
fixed_point_generalized_leapfrog_trace(args...; kwargs...) =
    _fixed_point_generalized_leapfrog_trace(args...; kwargs...)

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
