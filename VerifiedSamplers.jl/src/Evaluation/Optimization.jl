"""Fail-closed acceptance records for measured implementation changes."""
module Optimization

export GateResult, OptimizationTrial, accepted, render_record

"""One named correctness or reproducibility gate."""
struct GateResult
    name::Symbol
    passed::Bool
    evidence::String
end

"""Measured candidate together with every gate used to judge it."""
struct OptimizationTrial
    transformation::String
    assurance_class::String
    baseline_seconds::Float64
    candidate_seconds::Float64
    minimum_speedup::Float64
    gates::Vector{GateResult}

    function OptimizationTrial(transformation, assurance_class,
            baseline_seconds, candidate_seconds, minimum_speedup, gates)
        baseline_seconds > 0 || throw(ArgumentError(
            "baseline time must be positive"))
        candidate_seconds > 0 || throw(ArgumentError(
            "candidate time must be positive"))
        minimum_speedup >= 1 || throw(ArgumentError(
            "minimum speedup must be at least one"))
        isempty(gates) && throw(ArgumentError(
            "an optimization trial requires explicit gates"))
        new(String(transformation), String(assurance_class),
            Float64(baseline_seconds), Float64(candidate_seconds),
            Float64(minimum_speedup), GateResult[gates...])
    end
end

accepted(trial::OptimizationTrial) =
    all(gate -> gate.passed, trial.gates) &&
    trial.baseline_seconds / trial.candidate_seconds >= trial.minimum_speedup

escape_record(value) = replace(string(value), '\n' => ' ', '\t' => ' ')

"""Render a stable, line-oriented record suitable for CI artifacts."""
function render_record(trial::OptimizationTrial)
    lines = [
        "transformation=$(escape_record(trial.transformation))",
        "assurance=$(escape_record(trial.assurance_class))",
        "baseline_seconds=$(trial.baseline_seconds)",
        "candidate_seconds=$(trial.candidate_seconds)",
        "speedup=$(trial.baseline_seconds / trial.candidate_seconds)",
        "minimum_speedup=$(trial.minimum_speedup)",
        "accepted=$(accepted(trial))",
    ]
    append!(lines, "gate.$(gate.name)=$(gate.passed)|$(escape_record(gate.evidence))"
        for gate in trial.gates)
    join(lines, '\n')
end

end
