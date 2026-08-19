"""Shared statistical diagnostics and target suites for tests and evaluations."""
module Evaluation

include("Targets.jl")
include("Diagnostics.jl")
include("Conformance.jl")
include("Optimization.jl")

using .Targets: Target, standard_targets
using .Diagnostics: autocorrelation_ess, moment_diagnostics,
    covariance_max_error, marginal_quantile_max_error,
    batch_mean_standard_error, split_rank_diagnostics
using .Conformance: CapturedFailure, ReplayResult, replay_pair,
    replay_integer_pair, conforms
using .Optimization: GateResult, OptimizationTrial, accepted, render_record

export Target, standard_targets,
    autocorrelation_ess, moment_diagnostics, covariance_max_error,
    marginal_quantile_max_error, batch_mean_standard_error,
    split_rank_diagnostics, CapturedFailure, ReplayResult, replay_pair,
    replay_integer_pair, conforms,
    GateResult, OptimizationTrial, accepted, render_record

end
