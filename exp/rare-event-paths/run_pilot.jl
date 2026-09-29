"""
Execute the rare-event path sampling pilot.

Runs all three methods (TPS baseline, guided MH, CSMC) on each protocol
regime, collects diagnostics, and writes results to algo-seek/rare-event/pilot/.
"""

using Random
using Printf
using Statistics
using Dates

include("potential.jl")
include("dynamics.jl")
include("baseline_tps.jl")
include("candidate1_guided_mh.jl")
include("candidate2_csmc.jl")
include("diagnostics.jl")
include("pilot_protocol.jl")

function run_single_protocol(proto::PilotProtocol{T}, seed::UInt64) where {T<:AbstractFloat}
    rng = MersenneTwister(seed)
    _, oe = make_dynamics(proto)

    println("  Finding initial reactive path (seed=$seed)...")
    initial_path, n_attempts = find_initial_reactive_path(
        proto.x0, proto.L, oe, rng;
        A_threshold=proto.A_threshold, B_threshold=proto.B_threshold,
    )
    println("  Found after $n_attempts attempts")
    init_force_evals = n_attempts * proto.L

    println("  Running TPS baseline...")
    rng_tps = MersenneTwister(seed + UInt64(1))
    tps_result = run_tps(
        initial_path, oe, proto.n_iter + proto.n_warmup, rng_tps;
        B_threshold=proto.B_threshold, thin=proto.thin,
    )
    tps_paths = tps_result.paths[(proto.n_warmup ÷ proto.thin + 1):end]
    tps_force_evals = init_force_evals + (proto.n_iter + proto.n_warmup) * proto.L
    tps_diag = summarize_diagnostics(
        "TPS (one-way shooting)", tps_paths;
        acceptance_rate=tps_result.acceptance_rate,
        force_evals=tps_force_evals,
    )

    println("  Running guided whole-path MH...")
    rng_mh = MersenneTwister(seed + UInt64(2))
    mh_result = run_guided_mh(
        initial_path, oe, proto.guided_mh_sigma,
        proto.n_iter + proto.n_warmup, rng_mh;
        A_threshold=proto.A_threshold, B_threshold=proto.B_threshold,
        thin=proto.thin,
    )
    mh_paths = mh_result.paths[(proto.n_warmup ÷ proto.thin + 1):end]
    mh_force_evals = init_force_evals + (proto.n_iter + proto.n_warmup) * 2 * proto.L
    mh_diag = summarize_diagnostics(
        "Guided MH (whole-path)", mh_paths;
        acceptance_rate=mh_result.acceptance_rate,
        force_evals=mh_force_evals,
    )

    println("  Running conditional SMC...")
    rng_csmc = MersenneTwister(seed + UInt64(3))
    csmc_result = run_csmc(
        initial_path, proto.csmc_particles, oe,
        proto.n_iter + proto.n_warmup, rng_csmc;
        B_threshold=proto.B_threshold, thin=proto.thin,
    )
    csmc_paths = csmc_result.paths[(proto.n_warmup ÷ proto.thin + 1):end]
    csmc_force_evals = init_force_evals +
        (proto.n_iter + proto.n_warmup) * proto.csmc_particles * proto.L
    csmc_diag = summarize_diagnostics(
        "CSMC (N=$(proto.csmc_particles))", csmc_paths;
        acceptance_rate=csmc_result.endpoint_hit_rate,
        force_evals=csmc_force_evals,
    )

    return tps_diag, mh_diag, csmc_diag
end

function write_results(
    output_dir::String,
    proto::PilotProtocol{T},
    all_diagnostics::Vector{Tuple{PilotDiagnostics{T}, PilotDiagnostics{T}, PilotDiagnostics{T}}},
    seeds::Vector{UInt64}
) where {T<:AbstractFloat}
    mkpath(output_dir)

    commit_hash = try
        strip(read(`git rev-parse HEAD`, String))
    catch
        "unknown"
    end

    open(joinpath(output_dir, "$(proto.regime_name).txt"), "w") do io
        println(io, "# Rare-event path sampling pilot results")
        println(io, "# Regime: $(proto.regime_name)")
        println(io, "# Producing commit: $commit_hash")
        println(io, "# Date: $(Dates.now())")
        println(io, "")
        println(io, "## Parameters")
        println(io, "c = $(proto.c), s = $(proto.s), ε = $(proto.epsilon)")
        println(io, "β = $(proto.beta), δ = $(proto.delta), L = $(proto.L)")
        println(io, "x₀ = $(proto.x0)")
        println(io, "A = {q < $(proto.A_threshold)}, B = {q > $(proto.B_threshold)}")
        println(io, "n_iter = $(proto.n_iter), n_warmup = $(proto.n_warmup)")
        println(io, "CSMC particles = $(proto.csmc_particles)")
        println(io, "Guided MH σ = $(proto.guided_mh_sigma)")
        println(io, "Seeds: $(seeds)")
        println(io, "")

        for (run_idx, (tps_d, mh_d, csmc_d)) in enumerate(all_diagnostics)
            println(io, "## Run $run_idx (seed=$(seeds[run_idx]))")
            println(io, "")

            for diag in [tps_d, mh_d, csmc_d]
                println(io, "### $(diag.method_name)")
                @printf(io, "P(upper channel) = %.4f ± %.4f\n",
                        diag.channel_prob_upper, diag.channel_prob_se)
                println(io, "Channel switches = $(diag.n_switches)")
                @printf(io, "Channel ESS = %.1f\n", diag.ess)
                if !isnan(diag.acceptance_rate)
                    @printf(io, "Acceptance/hit rate = %.4f\n", diag.acceptance_rate)
                end
                println(io, "Force evaluations = $(diag.force_evals)")
                println(io, "")
            end
        end
    end
end

function main()
    output_dir = joinpath(@__DIR__, "..", "..", "algo-seek", "rare-event", "pilot")

    protocols = all_protocols(Float64)

    for proto in protocols
        println("\n" * "="^60)
        println("Regime: $(proto.regime_name)")
        println("β=$(proto.beta), ε=$(proto.epsilon), L=$(proto.L)")
        println("="^60)

        all_diags = Tuple{
            PilotDiagnostics{Float64},
            PilotDiagnostics{Float64},
            PilotDiagnostics{Float64},
        }[]

        active_seeds = proto.seeds[1:min(2, length(proto.seeds))]

        for seed in active_seeds
            println("\n--- Seed: $seed ---")
            try
                tps_d, mh_d, csmc_d = run_single_protocol(proto, seed)
                push!(all_diags, (tps_d, mh_d, csmc_d))
                println("\nResults:")
                print_diagnostics(tps_d)
                println()
                print_diagnostics(mh_d)
                println()
                print_diagnostics(csmc_d)
            catch e
                println("  ERROR: $e")
                if isa(e, ErrorException) && occursin("Failed to find", e.msg)
                    println("  Skipping this seed (regime too hard for rejection init)")
                else
                    rethrow(e)
                end
            end
        end

        if !isempty(all_diags)
            write_results(output_dir, proto, all_diags, active_seeds)
            println("\nResults written to $output_dir/$(proto.regime_name).txt")
        end
    end

    println("\n" * "="^60)
    println("Pilot complete. Results in $output_dir")
    println("="^60)
end

main()
