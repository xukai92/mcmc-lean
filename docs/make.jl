using Documenter

pages = [
    "Home" => "index.md",
    "Architecture" => [
        "Formalization" => "architecture.md",
        "Adding a sampler" => "development-guide.md",
        "Sampler development record" => "sampler-development-template.md",
        "Sampler obligation matrix" => "sampler-obligation-matrix.md",
        "Gaussian RWMH record" => "rwmh-development-record.md",
        "Fixed-step HMC record" => "hmc-development-record.md",
        "AdvancedHMC parity" => "advancedhmc-parity.md",
        "Lean-generated graphs" => "generated/architecture-graphs.md",
        "Reference artifact registry" => "generated/reference-artifact.md",
        "Julia backend registry" => "generated/backend-registry.md",
        "Executable system" => "executable-architecture.md",
        "Verified execution and optimization" =>
            "verified-execution-and-optimization.md",
        "Continuous executable contract" => "continuous-executable-contract.md",
    ],
    "Testing and roadmap" => [
        "Testing strategy" => "testing.md",
        "Benchmark report" => "benchmarks.md",
        "Progress matrix" => "progress.md",
        "Core release audit" => "core-release-audit.md",
        "Project completion status" => "project-status.md",
        "Overall project roadmap" => "project-roadmap.md",
        "Executable roadmap" => "executable-roadmap.md",
        "Finite executable roadmap" => "finite-executable-roadmap.md",
        "Development log" => [
            "Current" => "development-log.md",
            "Archive, part 1" => "development-log-archive.md",
            "Archive, part 2" => "development-log-archive-2.md",
            "Archive, part 3" => "development-log-archive-3.md",
        ],
    ],
    "Paper coverage" => [
        "Ge et al. 2018 audit" => "ge18-coverage.md",
        "Xu et al. 2021 audit" => "xu21-coverage.md",
        "Xu et al. 2021 roadmap" => "xu21-roadmap.md",
        "Xu and Ge 2024 audit" => "xu24-coverage.md",
        "Xu and Ge 2024 roadmap" => "xu24-roadmap.md",
    ],
    "Foundations and related work" => [
        "Related work" => "related-work.md",
        "Algorithm scope review" => "algorithm-scope-review.md",
        "Betancourt 2017" => "betancourt17-coverage.md",
        "Neal 2012" => "neal12-coverage.md",
    ],
]

# The Markdown files in docs/ remain canonical. Stage only published inputs so
# Documenter never copies its build directory back into itself.
published_files = [
    "index.md", "architecture.md", "development-guide.md",
    "sampler-development-template.md", "sampler-obligation-matrix.md",
    "rwmh-development-record.md",
    "hmc-development-record.md",
    "advancedhmc-parity.md",
    "generated/architecture-graphs.md",
    "generated/reference-artifact.md",
    "generated/backend-registry.md",
    "executable-architecture.md", "verified-execution-and-optimization.md",
    "continuous-executable-contract.md",
    "testing.md", "benchmarks.md", "progress.md", "core-release-audit.md",
    "project-status.md",
    "project-roadmap.md", "executable-roadmap.md",
    "finite-executable-roadmap.md",
    "development-log.md", "development-log-archive.md",
    "development-log-archive-2.md", "development-log-archive-3.md",
    "ge18-coverage.md", "xu21-coverage.md", "xu21-roadmap.md", "xu24-coverage.md",
    "xu24-roadmap.md", "related-work.md", "algorithm-scope-review.md",
    "betancourt17-coverage.md",
    "neal12-coverage.md",
]
staged_source = joinpath(@__DIR__, ".documenter-src")
rm(staged_source; recursive = true, force = true)
for relative_path in published_files
    destination = joinpath(staged_source, relative_path)
    mkpath(dirname(destination))
    cp(joinpath(@__DIR__, relative_path), destination)
end
cp(joinpath(@__DIR__, "assets"), joinpath(staged_source, "assets"))

makedocs(
    sitename = "Verified Samplers",
    authors = "Verified Samplers contributors",
    source = ".documenter-src",
    build = "build",
    clean = true,
    pagesonly = true,
    format = Documenter.HTML(
        prettyurls = get(ENV, "CI", "false") == "true",
        assets = [
            "assets/layout.css",
            "assets/layout.js",
            "assets/mermaid.js",
            "assets/benchmarks/hmc-interactive-data.js",
            "assets/benchmarks/hmc-interactive.css",
            "assets/benchmarks/hmc-interactive.js",
        ],
        repolink = "https://github.com/xukai92/mcmc-lean",
        # The current log and each archive epoch are bounded independently.
        # The search index intentionally includes all three published archive
        # pages, so its warning threshold has modest headroom above their
        # combined historical text.
        size_threshold_warn = 490 * 2^10,
        size_threshold = 520 * 2^10,
        # Includes the generated Lean assurance and Julia backend registries.
        search_size_threshold_warn = 1080 * 2^10,
        inventory_version = "dev",
    ),
    pages = pages,
)

rm(staged_source; recursive = true, force = true)

if get(ENV, "CI", "false") == "true"
    deploydocs(
        repo = "github.com/xukai92/mcmc-lean.git",
        devbranch = "main",
        push_preview = false,
    )
end
