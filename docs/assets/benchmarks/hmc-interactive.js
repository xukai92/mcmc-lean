(function () {
    "use strict";

    function initialize() {
    const root = document.getElementById("hmc-benchmark-explorer");
    if (!root) return;

    const benchmark = window.VERIFIED_SAMPLERS_BENCHMARK;
    if (!benchmark) {
        root.textContent = "Interactive benchmark data is unavailable; use the static chart below.";
        return;
    }

    const colors = {
        "verified-reference": "#bf8700",
        "verified-optimized": "#1f6feb",
        "optimized-runtime": "#8250df",
        "advancedhmc": "#cf222e"
    };
    const targetNames = {
        "isotropic-gaussian": "Isotropic Gaussian",
        "correlated-gaussian-rho-0.9": "Correlated Gaussian (ρ=0.9)",
        "product-quartic": "Product quartic",
        "ill-conditioned-gaussian": "Ill-conditioned Gaussian",
        "regularized-logistic": "Regularized logistic"
    };
    const metrics = {
        throughput: {
            label: "Transitions per second",
            field: "draws_per_second",
            rows: benchmark.timings,
            log: true,
            timing: true
        },
        ess_per_second: {
            label: "ESS per second",
            field: "ess_per_second",
            rows: benchmark.quality
        },
        bulk_ess: {
            label: "Bulk ESS",
            field: "bulk_ess",
            rows: benchmark.quality
        },
        tail_ess: {
            label: "Tail ESS",
            field: "tail_ess",
            rows: benchmark.quality
        },
        ess_per_gradient: {
            label: "Bulk ESS per gradient-work proxy",
            field: "bulk_ess_per_gradient_proxy",
            rows: benchmark.quality
        },
        acceptance: {
            label: "Acceptance rate",
            field: "acceptance",
            rows: benchmark.quality
        },
        mean_steps: {
            label: "Mean leapfrog steps",
            field: "average_steps",
            rows: benchmark.quality
        }
    };

    const unique = (rows, field) => [...new Set(rows.map(row => row[field]))];
    const targets = unique(benchmark.summary, "target");
    const algorithms = unique(benchmark.summary, "algorithm");
    const implementations = unique(benchmark.summary, "implementation");

    root.innerHTML = [
        '<div class="benchmark-controls">',
        selectControl("benchmark-metric", "Metric", Object.entries(metrics).map(
            ([value, metric]) => [value, metric.label])),
        selectControl("benchmark-target", "Target", [["all", "All targets"]].concat(
            targets.map(value => [value, targetNames[value] || value]))),
        selectControl("benchmark-algorithm", "Algorithm", [["all", "All algorithms"]].concat(
            algorithms.map(value => [value, value]))),
        selectControl("benchmark-group", "Group rows by", [
            ["target-algorithm", "Target × algorithm"],
            ["target", "Target"],
            ["algorithm", "Algorithm"]
        ]),
        '<fieldset class="benchmark-implementations"><legend>Implementations</legend>',
        implementations.map(value =>
            `<label><input type="checkbox" value="${escapeHtml(value)}" checked> ${escapeHtml(value)}</label>`
        ).join(""),
        "</fieldset></div>",
        '<div class="benchmark-plot" role="img" aria-label="Filtered benchmark plot"></div>',
        '<p class="benchmark-help">Drag to zoom, double-click to reset, and click legend entries to hide individual implementations.</p>'
    ].join("");

    function escapeHtml(value) {
        return String(value).replace(/[&<>"']/g, character => ({
            "&": "&amp;", "<": "&lt;", ">": "&gt;",
            '"': "&quot;", "'": "&#39;"
        })[character]);
    }

    function selectControl(id, label, options) {
        return `<label>${escapeHtml(label)}<select id="${id}">${options.map(
            ([value, text]) => `<option value="${escapeHtml(value)}">${escapeHtml(text)}</option>`
        ).join("")}</select></label>`;
    }

    function selectedImplementations() {
        return [...root.querySelectorAll(".benchmark-implementations input:checked")]
            .map(input => input.value);
    }

    function groupLabel(row, grouping) {
        const target = targetNames[row.target] || row.target;
        if (grouping === "target") return target;
        if (grouping === "algorithm") return row.algorithm;
        return `${target} · ${row.algorithm}`;
    }

    function finiteValue(row, field) {
        const value = Number(row[field]);
        return Number.isFinite(value) ? value : null;
    }

    function hoverText(row, metric) {
        const lines = [
            `<b>${escapeHtml(targetNames[row.target] || row.target)}</b>`,
            `algorithm: ${escapeHtml(row.algorithm)}`,
            `implementation: ${escapeHtml(row.implementation)}`
        ];
        if (metric.timing) {
            lines.push(`seed: ${escapeHtml(row.seed)}`);
            lines.push(`repetition: ${escapeHtml(row.repetition)}`);
            lines.push(`seconds: ${Number(row.seconds).toFixed(3)}`);
        } else {
            if (row.chains) lines.push(`chains: ${escapeHtml(row.chains)}`);
            if (row.rank_normalized_rhat) {
                lines.push(`R-hat: ${Number(row.rank_normalized_rhat).toFixed(3)}`);
            }
            if (row.divergences) lines.push(`divergences: ${escapeHtml(row.divergences)}`);
        }
        return lines.join("<br>");
    }

    function render() {
        const metric = metrics[root.querySelector("#benchmark-metric").value];
        const target = root.querySelector("#benchmark-target").value;
        const algorithm = root.querySelector("#benchmark-algorithm").value;
        const grouping = root.querySelector("#benchmark-group").value;
        const enabled = selectedImplementations();
        const rows = metric.rows.filter(row =>
            enabled.includes(row.implementation) &&
            (target === "all" || row.target === target) &&
            (algorithm === "all" || row.algorithm === algorithm) &&
            finiteValue(row, metric.field) !== null);

        const traces = enabled.map(implementation => {
            const selected = rows.filter(row => row.implementation === implementation);
            const common = {
                name: implementation,
                x: selected.map(row => finiteValue(row, metric.field)),
                y: selected.map(row => groupLabel(row, grouping)),
                text: selected.map(row => hoverText(row, metric)),
                hovertemplate: "%{text}<br>value: %{x:.4g}<extra></extra>",
                marker: {color: colors[implementation] || "#57606a"}
            };
            if (metric.timing) {
                return Object.assign(common, {
                    type: "box",
                    orientation: "h",
                    boxpoints: "all",
                    jitter: 0.35,
                    pointpos: 0,
                    line: {color: colors[implementation] || "#57606a"},
                    fillcolor: "rgba(0,0,0,0)",
                    marker: {
                        color: colors[implementation] || "#57606a",
                        opacity: 0.45,
                        size: 6
                    }
                });
            }
            return Object.assign(common, {
                type: "scatter",
                mode: "markers",
                marker: {
                    color: colors[implementation] || "#57606a",
                    size: 10,
                    line: {color: "white", width: 1}
                }
            });
        }).filter(trace => trace.x.length > 0);

        const groupCount = new Set(rows.map(row => groupLabel(row, grouping))).size;
        const layout = {
            autosize: true,
            height: Math.max(430, 78 + 52 * groupCount),
            margin: {l: 210, r: 30, t: 25, b: 70},
            boxmode: "group",
            hovermode: "closest",
            font: {color: window.getComputedStyle(root).color},
            paper_bgcolor: "rgba(0,0,0,0)",
            plot_bgcolor: "rgba(0,0,0,0)",
            legend: {orientation: "h", y: -0.18},
            xaxis: {
                title: metric.label,
                type: metric.log ? "log" : "linear",
                gridcolor: "rgba(128,128,128,0.22)",
                zeroline: false
            },
            yaxis: {automargin: true, categoryorder: "array",
                categoryarray: [...new Set(rows.map(row => groupLabel(row, grouping)))].reverse()}
        };
        window.Plotly.react(root.querySelector(".benchmark-plot"), traces, layout, {
            responsive: true,
            displaylogo: false,
            modeBarButtonsToRemove: ["sendDataToCloud", "lasso2d", "select2d"]
        });
    }

    root.querySelectorAll("select, input").forEach(control =>
        control.addEventListener("change", render));

    function start() {
        if (window.Plotly) {
            render();
            return;
        }
        const script = document.createElement("script");
        script.src = "https://cdn.plot.ly/plotly-3.7.0.min.js";
        script.charset = "utf-8";
        script.onload = render;
        script.onerror = () => {
            root.querySelector(".benchmark-plot").textContent =
                "Interactive plotting could not be loaded; use the static chart below.";
        };
        document.head.appendChild(script);
    }

    start();
    }

    if (document.readyState === "loading") {
        document.addEventListener("DOMContentLoaded", initialize, {once: true});
    } else {
        initialize();
    }
})();
