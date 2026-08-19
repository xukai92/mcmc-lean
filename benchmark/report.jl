using Printf
using Statistics

const DEV_MODE = "--dev" in ARGS
const UNKNOWN_ARGUMENTS = filter(!=("--dev"), ARGS)
isempty(UNKNOWN_ARGUMENTS) || error(
    "unknown arguments: $(join(UNKNOWN_ARGUMENTS, ' ')); supported: --dev")
const RESULTS = joinpath(@__DIR__, "results", DEV_MODE ? "dev.csv" : "latest.csv")
const TIMINGS = joinpath(@__DIR__, "results",
    DEV_MODE ? "dev-timings.csv" : "timings.csv")
const QUALITY = joinpath(@__DIR__, "results",
    DEV_MODE ? "dev-quality.csv" : "quality.csv")
const DOC = joinpath(@__DIR__, "..", "docs", "benchmarks.md")
const SVG = joinpath(@__DIR__, "..", "docs", "assets", "benchmarks",
    "hmc-throughput.svg")

function read_rows(path)
    lines = readlines(path)
    header = Symbol.(split(first(lines), ','))
    [NamedTuple{Tuple(header)}(Tuple(split(line, ','))) for line in lines[2:end]]
end

escape_xml(value) = replace(string(value), '&' => "&amp;", '<' => "&lt;",
    '>' => "&gt;", '"' => "&quot;")

function write_svg(rows, timings)
    width, left, right, row_height = 1050, 285, 65, 70
    chart_width = width - left - right
    algorithms = unique(row.algorithm for row in rows)
    targets = unique(row.target for row in rows)
    groups = [(target, algorithm) for target in targets for algorithm in algorithms
        if any(row -> row.target == target && row.algorithm == algorithm, rows)]
    throughput = parse.(Float64, getproperty.(timings, :draws_per_second))
    lower = 10.0^floor(log10(minimum(throughput)))
    upper = 10.0^ceil(log10(maximum(throughput)))
    x_position(value) = left + chart_width *
        (log10(value) - log10(lower)) / (log10(upper) - log10(lower))
    colors = Dict("verified-reference" => "#bf8700",
        "verified-optimized" => "#1f6feb", "advancedhmc" => "#cf222e")
    offsets = Dict("verified-reference" => -18, "verified-optimized" => 0,
        "advancedhmc" => 18)
    height = 110 + row_height * length(groups)
    mkpath(dirname(SVG))
    open(SVG, "w") do io
        println(io, "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"$width\" height=\"$height\" viewBox=\"0 0 $width $height\" role=\"img\" aria-labelledby=\"title desc\">")
        println(io, "<title id=\"title\">HMC transition-throughput distributions</title>")
        println(io, "<desc id=\"desc\">Points show complete-chain timing repetitions; larger points and horizontal intervals show medians and interquartile ranges.</desc>")
        println(io, "<rect width=\"100%\" height=\"100%\" fill=\"white\"/>")
        for exponent in Int(log10(lower)):Int(log10(upper))
            tick = 10.0^exponent
            x = x_position(tick)
            println(io, "<line x1=\"$x\" y1=\"48\" x2=\"$x\" y2=\"$(height - 65)\" stroke=\"#d8dee4\"/>")
            println(io, "<text x=\"$x\" y=\"30\" text-anchor=\"middle\" font-family=\"sans-serif\" font-size=\"13\" fill=\"#57606a\">$(@sprintf("%.0f", tick))</text>")
        end
        println(io, "<text x=\"$(left + chart_width / 2)\" y=\"$(height - 45)\" text-anchor=\"middle\" font-family=\"sans-serif\" font-size=\"14\" fill=\"#24292f\">transitions per second (log scale; higher is better)</text>")
        for (index, (target, algorithm)) in enumerate(groups)
            center = 67 + (index - 1) * row_height
            if index > 1 && groups[index - 1][1] != target
                println(io, "<line x1=\"20\" y1=\"$(center - row_height / 2)\" x2=\"$(width - 20)\" y2=\"$(center - row_height / 2)\" stroke=\"#8c959f\" stroke-width=\"2\"/>")
            end
            label = "$(display_name(target)) · $(uppercasefirst(algorithm))"
            println(io, "<text x=\"$(left - 14)\" y=\"$(center + 5)\" text-anchor=\"end\" font-family=\"sans-serif\" font-size=\"14\" fill=\"#24292f\">$(escape_xml(label))</text>")
            for implementation in ("verified-reference", "verified-optimized", "advancedhmc")
                selected = filter(row -> row.target == target &&
                    row.algorithm == algorithm && row.implementation == implementation,
                    timings)
                isempty(selected) && continue
                values = parse.(Float64, getproperty.(selected, :draws_per_second))
                y = center + offsets[implementation]
                for (point_index, value) in enumerate(values)
                    jitter = ((point_index % 3) - 1) * 2
                    println(io, "<circle cx=\"$(x_position(value))\" cy=\"$(y + jitter)\" r=\"3\" fill=\"$(colors[implementation])\" fill-opacity=\"0.30\"/>")
                end
                q25, med, q75 = quantile(values, (0.25, 0.5, 0.75))
                println(io, "<line x1=\"$(x_position(q25))\" y1=\"$y\" x2=\"$(x_position(q75))\" y2=\"$y\" stroke=\"$(colors[implementation])\" stroke-width=\"5\" stroke-linecap=\"round\"/>")
                println(io, "<circle cx=\"$(x_position(med))\" cy=\"$y\" r=\"6\" fill=\"$(colors[implementation])\" stroke=\"white\" stroke-width=\"1.5\"/>")
            end
        end
        legend_y = height - 20
        for (index, implementation) in enumerate(("verified-reference", "verified-optimized", "advancedhmc"))
            x = left + 175 * (index - 1)
            println(io, "<circle cx=\"$x\" cy=\"$legend_y\" r=\"5\" fill=\"$(colors[implementation])\"/>")
            println(io, "<text x=\"$(x + 10)\" y=\"$(legend_y + 5)\" font-family=\"sans-serif\" font-size=\"13\" fill=\"#24292f\">$(implementation)</text>")
        end
        println(io, "</svg>")
    end
end

function display_name(value)
    get(Dict("isotropic-gaussian" => "Isotropic Gaussian",
        "correlated-gaussian-rho-0.9" => "Correlated Gaussian (ρ=0.9)",
        "product-quartic" => "Product quartic",
        "ill-conditioned-gaussian" => "Ill-conditioned Gaussian",
        "regularized-logistic" => "Regularized logistic"), value, value)
end

function write_doc(rows, timings, quality)
    commit = readchomp(`git -C $(joinpath(@__DIR__, "..")) rev-parse --short HEAD`)
    cpu = Sys.cpu_info()[1].model
    open(DOC, "w") do io
        println(io, "# HMC benchmark report\n")
        DEV_MODE && println(io, "!!! warning \"Development-mode results\"\n    This page was generated from a short `--dev` run for layout iteration. Its timings are not publication-quality.\n")
        println(io, "This is a reproducible implementation benchmark, not a theorem about convergence or a claim that Float64 execution is identical to the exact-real Lean semantics.\n")
        println(io, "![HMC transition-throughput distributions](assets/benchmarks/hmc-throughput.svg)\n")
        println(io, "Rows are grouped first by target and then by algorithm. Within each row, colors compare libraries implementing that same `target × algorithm` case. Small translucent points are complete-chain timing repetitions; large points and thick intervals are medians and IQRs. The shared logarithmic axis retains absolute throughput and remains extensible to additional libraries.\n")
        println(io, "Preconditioned endpoint and multinomial rows are AdvancedHMC-only in this first pass; their absence of VerifiedSamplers points is intentional, not missing data.\n")
        println(io, "## Configuration\n")
        first_row = first(rows)
        println(io, "- Commit: `$commit`")
        println(io, "- Julia: `$(VERSION)`")
        println(io, "- CPU: `$(cpu)`")
        println(io, "- Dimension: `$(first_row.dimension)`")
        println(io, "- Draws per measured chain: `$(first_row.draws)`")
        repetitions = maximum(parse(Int, row.repetition) for row in timings)
        println(io, "- Complete-chain timing repetitions per case: `$repetitions`")
        println(io, "- Step size: `$(first_row.step_size)`")
        println(io, "- Fixed trajectory length: `$(first_row.configured_steps)` leapfrog steps")
        println(io, "- Gradients: analytic callbacks for both packages; AD time excluded\n")
        println(io, "## Results\n")
        println(io, "### Median transitions per second\n")
        implementations = unique(row.implementation for row in rows)
        for algorithm in unique(row.algorithm for row in rows)
            algorithm_rows = filter(row -> row.algorithm == algorithm, rows)
            available = [implementation for implementation in implementations if
                any(row -> row.implementation == implementation, algorithm_rows)]
            println(io, "#### $(uppercasefirst(algorithm))\n")
            println(io, "| Target | $(join(available, " | ")) |")
            println(io, "|---|$(join(fill("---:", length(available)), "|"))|")
            for target in unique(row.target for row in algorithm_rows)
                selected = filter(row -> row.target == target, algorithm_rows)
                cells = [begin
                    matches = filter(row -> row.implementation == implementation,
                        selected)
                    isempty(matches) ? "—" : @sprintf("%.0f", parse(Float64,
                        only(matches).draws_per_second))
                end for implementation in available]
                println(io, "| $(display_name(target)) | $(join(cells, " | ")) |")
            end
            println(io)
        end
        println(io, "### Complete summary\n")
        println(io, "| Target | Algorithm | Implementation | Median | IQR | Draws/s | Mean steps | Allocations |")
        println(io, "|---|---|---|---:|---:|---:|---:|---:|")
        for row in rows
            median_ms = 1e3 * parse(Float64, row.median_seconds)
            q25_ms = 1e3 * parse(Float64, row.q25_seconds)
            q75_ms = 1e3 * parse(Float64, row.q75_seconds)
            println(io, "| $(display_name(row.target)) | $(row.algorithm) | $(row.implementation) | $(@sprintf("%.1f ms", median_ms)) | $(@sprintf("%.1f–%.1f ms", q25_ms, q75_ms)) | $(@sprintf("%.0f", parse(Float64, row.draws_per_second))) | $(@sprintf("%.1f", parse(Float64, row.average_steps))) | $(row.allocations) |")
        end
        println(io, "\n## Sampling quality\n")
        println(io, "Quality runs are separate seeded chains rather than BenchmarkTools trials. Moment errors use each target's known zero mean and analytical or independently computed marginal variance. ESS is the minimum autocorrelation ESS among the first four coordinates after ten-percent burn-in.\n")
        println(io, "| Target | Algorithm | Implementation | ESS/s | Mean RMSE (std.) | Variance RMSE (relative) | Movement | Acceptance | Divergences | Mean steps |")
        println(io, "|---|---|---|---:|---:|---:|---:|---:|---:|---:|")
        for row in quality
            acceptance = isnan(parse(Float64, row.acceptance)) ? "—" :
                @sprintf("%.3f", parse(Float64, row.acceptance))
            println(io, "| $(display_name(row.target)) | $(row.algorithm) | $(row.implementation) | $(@sprintf("%.1f", parse(Float64, row.ess_per_second))) | $(@sprintf("%.3f", parse(Float64, row.standardized_mean_rmse))) | $(@sprintf("%.3f", parse(Float64, row.relative_variance_rmse))) | $(@sprintf("%.3f", parse(Float64, row.movement))) | $acceptance | $(row.divergences) | $(@sprintf("%.1f", parse(Float64, row.average_steps))) |")
        end
        println(io, "\n## Interpretation\n")
        println(io, "Endpoint rows are directly matched fixed-step proposals. Multinomial rows share the target and integration budget, but the packages use different trajectory construction and selection mechanics. NUTS uses variable work per transition, so its draws/s should be read together with its mean leapfrog count and not compared directly with fixed ten-step HMC.\n")
        println(io, "The timing distribution describes repeated execution on one machine and is not a cross-machine confidence interval. The quality table reports acceptance, divergences, a simple autocorrelation ESS estimate, and ESS/s, but not yet ESS per gradient evaluation. These are diagnostics rather than proofs that a chain has converged.\n")
        println(io, "## Quality-check roadmap\n")
        println(io, "Lightweight, reproducible checks belong in the integrated Julia tests: retain the target gradient contracts and known-moment regressions, add full covariance checks for correlated Gaussian targets, and add a small set of analytically known marginal quantiles. Their tolerances must account for autocorrelation and remain stable in routine CI.\n")
        println(io, "The benchmark should carry the more computational and exploratory checks:\n")
        println(io, "- run multiple independently seeded chains and report between-chain diagnostics such as split rank-normalized R-hat;")
        println(io, "- report bulk and tail ESS, preferably also per gradient evaluation;")
        println(io, "- visualize covariance error for Gaussian targets and empirical-versus-known quantiles or ECDF differences for product targets;")
        println(io, "- attach Monte Carlo uncertainty to moment and quantile errors instead of interpreting raw errors without a sampling scale;")
        println(io, "- define conspicuous warning thresholds, while keeping benchmark diagnostics non-gating until their calibration is demonstrably stable.\n")
        println(io, "## Targets\n")
        println(io, "- **Isotropic Gaussian:** baseline identity geometry.")
        println(io, "- **Correlated Gaussian:** AR(1) covariance with adjacent correlation `0.9`, sampled using the same identity metric to expose difficult geometry.")
        println(io, "- **Product quartic:** independent coordinates with potential `x⁴/4 + x²/2`, adding a nonlinear strongly convex target.\n")
        println(io, "- **Ill-conditioned Gaussian:** diagonal covariance ranging from `10⁻²` to `10²`; it also activates matched constant-metric algorithms.")
        println(io, "- **Regularized logistic:** a symmetric product logistic posterior with paired labels and a standard-normal prior.\n")
        println(io, "## Reproduce\n")
        println(io, "```sh\nmake benchmark-hmc\nmake benchmark-report\n```\n")
        println(io, "Aggregate measurements are committed at [`benchmark/results/latest.csv`](https://github.com/xukai92/mcmc-lean/blob/main/benchmark/results/latest.csv), with every timing repetition in [`benchmark/results/timings.csv`](https://github.com/xukai92/mcmc-lean/blob/main/benchmark/results/timings.csv) and sampling diagnostics in [`benchmark/results/quality.csv`](https://github.com/xukai92/mcmc-lean/blob/main/benchmark/results/quality.csv).")
    end
end

rows = read_rows(RESULTS)
timings = read_rows(TIMINGS)
quality = read_rows(QUALITY)
write_svg(rows, timings)
write_doc(rows, timings, quality)
