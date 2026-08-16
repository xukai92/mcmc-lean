using Documenter

pages = [
    "Home" => "index.md",
    "Architecture" => [
        "Formalization" => "architecture.md",
        "Lean-generated graphs" => "generated/architecture-graphs.md",
        "Executable system" => "executable-architecture.md",
        "Continuous executable contract" => "continuous-executable-contract.md",
    ],
    "Testing and roadmap" => [
        "Testing strategy" => "testing.md",
        "Phase I release audit" => "core-release-audit.md",
        "Project completion status" => "project-status.md",
        "Overall project roadmap" => "project-roadmap.md",
        "Executable roadmap" => "executable-roadmap.md",
        "Finite executable roadmap" => "finite-executable-roadmap.md",
        "Development log" => [
            "Current" => "development-log.md",
            "Archive" => "development-log-archive.md",
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
    "index.md", "architecture.md", "generated/architecture-graphs.md",
    "executable-architecture.md", "continuous-executable-contract.md",
    "testing.md", "core-release-audit.md", "project-status.md",
    "project-roadmap.md", "executable-roadmap.md",
    "finite-executable-roadmap.md",
    "development-log.md", "development-log-archive.md",
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
        assets = ["assets/mermaid.js"],
        repolink = "https://github.com/xukai92/mcmc-lean",
        # The theorem-level development log is intentionally detailed and its
        # rendered HTML includes Documenter's navigation metadata. Keep a
        # modest headroom above the current page while older epochs continue
        # to move to development-log-archive.md.
        size_threshold_warn = 325 * 2^10,
        size_threshold = 350 * 2^10,
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
