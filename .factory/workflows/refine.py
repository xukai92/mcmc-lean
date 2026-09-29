"""Refine mode — connect verified Lean kernel theory to executable IR programs.

Pipeline:
  precondition_check -> fork_research -> [researcher_kernel, researcher_ir_patterns] ->
  join_research -> gate_research (CEO) ->
  strategist -> gate_strategy (CEO) ->
  builder_refine(max 3) -> gate_refine (lake build) -> fn_no_sorry ->
  fn_refinement_check -> fn_scope_check -> fn_generate -> fn_check_generated ->
  fn_axioms_check -> fn_manifest -> archivist(async)

Reloop edges:
  gate_research -> fork_research
  gate_strategy -> strategist
  gate_refine -> builder_refine (max 3)

Terminal mode. Requires --focus <kernel_name>. Optional --tier <tier>.

Requires kernel theory to exist (from a prior formalize run). Produces IR
programs in CompilerIR, refinement proofs, and auto-generated Reference Julia.
"""

from typing import Any

from factory.models import ProjectState
from factory.workflow.primitives import (
    AgentNode,
    AgentRole,
    ArtifactCheck,
    Edge,
    FnNode,
    ForkNode,
    GateNode,
    JoinNode,
    VerdictType,
    Workflow,
)

meta = {
    "name": "refine",
    "description": (
        "Refine mode — connect verified Lean kernel theory to executable IR "
        "programs via refinement theorems. Requires kernel theory to exist "
        "(from a prior formalize run). Produces IR programs in CompilerIR, "
        "refinement proofs, and auto-generated Reference Julia. "
        "Requires --focus <kernel_name>. Optional --tier <tier>."
    ),
}


def workflow() -> Workflow:
    """Build the refine workflow."""
    nodes: dict[str, AgentNode | FnNode | GateNode | ForkNode | JoinNode] = {}
    edges: list[Edge] = []

    # ── Precondition Check ─────────────────────────────────────

    nodes["precondition_check"] = FnNode(
        id="precondition_check",
        command=(
            "cd {project_path} && python3 - <<'PYEOF'\n"
            "import sys, json, subprocess\n"
            "from pathlib import Path\n"
            "\n"
            "focus = '{focus}'\n"
            "if not focus:\n"
            "    print('HALT: --focus is required but empty')\n"
            "    sys.exit(1)\n"
            "\n"
            "# Check manifest from prior formalize run\n"
            "manifest_path = Path('.factory/manifest-formalize.json')\n"
            "found_theory = False\n"
            "if manifest_path.exists():\n"
            "    print(f'Found formalize manifest at {manifest_path}')\n"
            "    found_theory = True\n"
            "\n"
            "# Also check for theorem/lemma/def declarations in formal/Mcmc/\n"
            "if not found_theory:\n"
            "    result = subprocess.run(\n"
            "        ['grep', '-rlE', r'(theorem|lemma|def)\\s+', 'formal/Mcmc/'],\n"
            "        capture_output=True, text=True,\n"
            "    )\n"
            "    if result.stdout.strip():\n"
            "        print('Found kernel theory declarations in formal/Mcmc/')\n"
            "        found_theory = True\n"
            "\n"
            "if not found_theory:\n"
            "    print('HALT: no kernel theory found — run formalize workflow first')\n"
            "    sys.exit(1)\n"
            "\n"
            "print(f'PROCEED: kernel theory exists, focus={focus}')\n"
            "sys.exit(0)\n"
            "PYEOF"
        ),
        notes=(
            "Precondition gate. Verifies kernel theory exists (via formalize manifest "
            "or grep for declarations) and that --focus is non-empty. Exit 1 if no "
            "kernel theory found."
        ),
    )

    # ── Research Phase — Fork/Join/Gate ──────────────────────────

    nodes["fork_research"] = ForkNode(
        id="fork_research",
        targets=["researcher_kernel", "researcher_ir_patterns"],
    )

    nodes["researcher_kernel"] = AgentNode(
        id="researcher_kernel",
        role=AgentRole.RESEARCHER,
        prompt_template=(
            "Study the kernel theory for the target algorithm. "
            "Read the Lean files under {project_path}/formal/Mcmc/Kernel/ and "
            "{project_path}/formal/Mcmc/Hamiltonian/ for the target kernel definition, "
            "its invariance theorem, and the mathematical structure. "
            "Document: kernel type signature, key theorems, invariant properties, "
            "and what the refinement theorem must connect to. "
            "Write findings to .factory/strategy/research-kernel.md."
        ),
        writes={".factory/strategy/research-kernel.md"},
        post_checks=[
            ArtifactCheck(
                path=".factory/strategy/research-kernel.md",
                must_exist=True,
                min_size=50,
            )
        ],
    )

    nodes["researcher_ir_patterns"] = AgentNode(
        id="researcher_ir_patterns",
        role=AgentRole.RESEARCHER,
        prompt_template=(
            "Study existing IR refinement patterns. "
            "Read {project_path}/formal/Mcmc/Executable/Continuous/RWMH.lean, "
            "CompilerIR.lean, and other refinement theorems under "
            "{project_path}/formal/Mcmc/Executable/. "
            "Document the proof pattern for *ProgramKernel_refines theorems: "
            "how the IR program is defined, how the refinement theorem connects "
            "the IR to the kernel, what lemmas are reused, and the IRFormat "
            "wiring pattern. "
            "Write findings to .factory/strategy/research-ir-patterns.md."
        ),
        writes={".factory/strategy/research-ir-patterns.md"},
        post_checks=[
            ArtifactCheck(
                path=".factory/strategy/research-ir-patterns.md",
                must_exist=True,
                min_size=50,
            )
        ],
    )

    nodes["join_research"] = JoinNode(
        id="join_research",
        sources=["researcher_kernel", "researcher_ir_patterns"],
    )

    nodes["gate_research"] = GateNode(
        id="gate_research",
        evaluator_type="agent",
        evaluator_role=AgentRole.CEO,
        gate_prompt=(
            "Review the two research outputs for the refinement. "
            "Check: (1) Is the kernel theory well-understood with key theorems identified? "
            "(2) Are existing IR refinement patterns documented with proof strategies? "
            "PROCEED if both are adequate. RELOOP if either is shallow or missing key details."
        ),
        reads={
            ".factory/strategy/research-kernel.md",
            ".factory/strategy/research-ir-patterns.md",
        },
    )

    # ── Strategy Phase ──────────────────────────────────────────

    nodes["strategist"] = AgentNode(
        id="strategist",
        role=AgentRole.STRATEGIST,
        prompt_template=(
            "Synthesize research into a refinement plan. "
            "Read .factory/strategy/research-kernel.md and "
            "research-ir-patterns.md. "
            "Produce a concrete implementation plan covering: "
            "1) CompilerIR program design — what IR program to add "
            "2) Refinement theorem — statement connecting IR to kernel "
            "3) IRFormat wiring — how to connect to formal/Mcmc/Executable/IRFormat.lean "
            "4) formal/Mcmc.lean update plan — new import lines "
            "5) Proof strategy — reusable lemmas and proof outline "
            "Write the plan to .factory/strategy/current.md."
        ),
        reads={
            ".factory/strategy/research-kernel.md",
            ".factory/strategy/research-ir-patterns.md",
        },
        writes={".factory/strategy/current.md"},
        post_checks=[
            ArtifactCheck(
                path=".factory/strategy/current.md",
                must_exist=True,
                min_size=200,
            )
        ],
    )

    nodes["gate_strategy"] = GateNode(
        id="gate_strategy",
        evaluator_type="agent",
        evaluator_role=AgentRole.CEO,
        gate_prompt=(
            "Review the refinement strategy at .factory/strategy/current.md. "
            "Verify: (1) CompilerIR program design is specified "
            "(2) Refinement theorem statement is clear "
            "(3) IRFormat wiring plan is concrete "
            "(4) Proof strategy leverages existing patterns "
            "PROCEED if strategy is sound. RELOOP if incomplete."
        ),
        reads={".factory/strategy/current.md"},
    )

    # ── Build Phase — Refinement ───────────────────────────────

    nodes["builder_refine"] = AgentNode(
        id="builder_refine",
        role=AgentRole.BUILDER,
        prompt_template=(
            "Implement the IR refinement. "
            "Read the approved plan at .factory/strategy/current.md. "
            "Read CLAUDE.md for project conventions. "
            "Tasks: "
            "- Add CompilerIR program for the target kernel "
            "- Write refinement theorem connecting IR to kernel "
            "- Wire into formal/Mcmc/Executable/IRFormat.lean "
            "- Update formal/Mcmc.lean with new module imports "
            "Constraints: No sorry, admit, or axiom. "
            "After writing the code, run 'cd formal && lake build' to verify. "
            "If compilation fails, fix the errors before reporting completion. "
            "Commit changes when compilation succeeds."
        ),
        reads={".factory/strategy/current.md"},
        writes={".factory/reviews/builder-latest.md"},
        max_iterations=3,
        post_checks=[
            ArtifactCheck(
                path=".factory/reviews/builder-latest.md",
                must_exist=True,
                min_size=100,
            )
        ],
    )

    nodes["gate_refine"] = GateNode(
        id="gate_refine",
        evaluator_type="fn",
        evaluator_command="cd {project_path}/formal && lake build",
        gate_prompt=(
            "IR compilation gate. Verifies the IR emission matches the kernel theory "
            "via the refinement theorem. RELOOP to builder_refine on failure (max 3 iterations)."
        ),
    )

    # ── Post-Build Checks ──────────────────────────────────────

    nodes["fn_no_sorry"] = FnNode(
        id="fn_no_sorry",
        command=(
            "cd {project_path} && python3 - <<'PYEOF'\n"
            "import sys, subprocess, re\n"
            "from pathlib import Path\n"
            "\n"
            "base = subprocess.run(\n"
            "    ['git', 'merge-base', 'HEAD', 'main'],\n"
            "    capture_output=True, text=True,\n"
            ").stdout.strip()\n"
            "if not base:\n"
            "    print('ERROR: could not determine merge-base with main')\n"
            "    sys.exit(1)\n"
            "\n"
            "diff_out = subprocess.run(\n"
            "    ['git', 'diff', '--name-only', base, '--', 'formal/Mcmc/'],\n"
            "    capture_output=True, text=True,\n"
            ").stdout.strip()\n"
            "lean_files = [f for f in diff_out.splitlines() if f.endswith('.lean')]\n"
            "\n"
            "if not lean_files:\n"
            "    print('WARNING: no .lean files changed under formal/Mcmc/')\n"
            "    sys.exit(0)\n"
            "\n"
            "found = False\n"
            "for lf in lean_files:\n"
            "    p = Path(lf)\n"
            "    if not p.exists():\n"
            "        continue\n"
            "    content = p.read_text()\n"
            "    for i, line in enumerate(content.splitlines(), 1):\n"
            "        stripped = line.split('--')[0]\n"
            "        if re.search(r'\\bsorry\\b', stripped):\n"
            "            print(f'FAIL: {lf}:{i}: sorry found: {line.strip()}')\n"
            "            found = True\n"
            "        if re.search(r'\\badmit\\b', stripped):\n"
            "            print(f'FAIL: {lf}:{i}: admit found: {line.strip()}')\n"
            "            found = True\n"
            "        if re.search(r'\\baxiom\\b', stripped):\n"
            "            print(f'FAIL: {lf}:{i}: axiom found: {line.strip()}')\n"
            "            found = True\n"
            "\n"
            "if found:\n"
            "    print('FAIL: sorry/admit/axiom detected in changed .lean files')\n"
            "    sys.exit(1)\n"
            "print(f'PASS: no sorry/admit/axiom in {len(lean_files)} changed .lean files')\n"
            "sys.exit(0)\n"
            "PYEOF"
        ),
        notes=(
            "Source-text grep for sorry/admit/axiom in changed .lean files. "
            "Closes the F2 escape where lake build exits 0 even when sorry is present. "
            "Strips comments before matching to avoid false positives."
        ),
    )

    nodes["fn_refinement_check"] = FnNode(
        id="fn_refinement_check",
        command=(
            "cd {project_path} && python3 - <<'PYEOF'\n"
            "import sys, re, subprocess\n"
            "from pathlib import Path\n"
            "\n"
            "base = subprocess.run(\n"
            "    ['git', 'merge-base', 'HEAD', 'main'],\n"
            "    capture_output=True, text=True,\n"
            ").stdout.strip()\n"
            "if not base:\n"
            "    print('ERROR: could not determine merge-base with main')\n"
            "    sys.exit(1)\n"
            "\n"
            "diff_out = subprocess.run(\n"
            "    ['git', 'diff', '--name-only', base, '--', 'formal/Mcmc/'],\n"
            "    capture_output=True, text=True,\n"
            ").stdout.strip()\n"
            "lean_files = [f for f in diff_out.splitlines() if f.endswith('.lean')]\n"
            "\n"
            "if not lean_files:\n"
            "    print('ERROR: no .lean files changed under formal/Mcmc/')\n"
            "    sys.exit(1)\n"
            "\n"
            "tier = None\n"
            "theorem_name = None\n"
            "\n"
            "for lf in lean_files:\n"
            "    p = Path(lf)\n"
            "    if not p.exists():\n"
            "        continue\n"
            "    content = p.read_text()\n"
            "    for m in re.finditer(\n"
            "        r'^\\s*(?:theorem|lemma)\\s+([a-zA-Z_][a-zA-Z0-9_]*)',\n"
            "        content,\n"
            "        re.MULTILINE,\n"
            "    ):\n"
            "        name = m.group(1)\n"
            "        if 'ProgramKernel_refines' in name:\n"
            "            if tier != 'full-induced-law':\n"
            "                tier = 'modeled-kernel'\n"
            "            theorem_name = name\n"
            "        elif name.startswith('run') and '_refines' in name:\n"
            "            if tier not in ('modeled-kernel', 'full-induced-law'):\n"
            "                tier = 'replay-spec'\n"
            "            if not theorem_name:\n"
            "                theorem_name = name\n"
            "        elif '_refines' in name:\n"
            "            if tier not in ('modeled-kernel', 'full-induced-law'):\n"
            "                tier = 'conditional'\n"
            "            if not theorem_name:\n"
            "                theorem_name = name\n"
            "        elif 'induced_law' in name.lower() or 'inducedlaw' in name.lower():\n"
            "            tier = 'full-induced-law'\n"
            "            theorem_name = name\n"
            "\n"
            "if not tier:\n"
            "    print('ERROR: no refinement theorem found in changed .lean files')\n"
            "    print('Expected: *ProgramKernel_refines, run*_refines, or *_refines')\n"
            "    sys.exit(1)\n"
            "\n"
            "Path('.factory/refinement-tier.txt').write_text(f'{tier}\\n{theorem_name}\\n')\n"
            "print(f'PASS: refinement tier={tier}, theorem={theorem_name}')\n"
            "sys.exit(0)\n"
            "PYEOF"
        ),
        writes={".factory/refinement-tier.txt"},
        notes=(
            "Refinement theorem check. Searches changed .lean files for refinement "
            "theorems and classifies them: modeled-kernel (*ProgramKernel_refines), "
            "replay-spec (run*_refines), conditional (*_refines with conditions), "
            "or full-induced-law. Writes tier and theorem name to "
            ".factory/refinement-tier.txt. Exit 1 if no refinement theorem found."
        ),
    )

    nodes["fn_scope_check"] = FnNode(
        id="fn_scope_check",
        command=(
            "cd {project_path} && python3 - <<'PYEOF'\n"
            "import sys, re, subprocess\n"
            "\n"
            "base = subprocess.run(\n"
            "    ['git', 'merge-base', 'HEAD', 'main'],\n"
            "    capture_output=True, text=True,\n"
            ").stdout.strip()\n"
            "if not base:\n"
            "    print('ERROR: could not determine merge-base with main')\n"
            "    sys.exit(1)\n"
            "\n"
            "diff_out = subprocess.run(\n"
            "    ['git', 'diff', '--name-only', base],\n"
            "    capture_output=True, text=True,\n"
            ").stdout.strip()\n"
            "changed = [f for f in diff_out.splitlines() if f]\n"
            "\n"
            "if not changed:\n"
            "    print('ERROR: no files changed — vacuous success')\n"
            "    sys.exit(1)\n"
            "\n"
            "allowed = re.compile(\n"
            "    r'^(formal/Mcmc/Executable/.*\\.lean'\n"
            "    r'|formal/Mcmc\\.lean'\n"
            "    r'|Samplers\\.ir'\n"
            "    r'|\\.factory/.*)$'\n"
            ")\n"
            "\n"
            "# Explicitly reject kernel/hamiltonian modifications\n"
            "kernel_re = re.compile(r'^formal/Mcmc/(Kernel|Hamiltonian)/')\n"
            "\n"
            "violations = []\n"
            "for f in changed:\n"
            "    if kernel_re.match(f):\n"
            "        violations.append(f'{f} (belongs to formalize workflow)')\n"
            "    elif not allowed.match(f):\n"
            "        violations.append(f)\n"
            "\n"
            "if violations:\n"
            "    print('ERROR: scope violation — files outside allowed paths:')\n"
            "    for v in violations:\n"
            "        print(f'  {v}')\n"
            "    print()\n"
            "    print('Allowed: formal/Mcmc/Executable/**/*.lean, formal/Mcmc.lean, Samplers.ir, .factory/*')\n"
            "    print('Rejected: formal/Mcmc/Kernel/*, formal/Mcmc/Hamiltonian/* (use formalize workflow)')\n"
            "    sys.exit(1)\n"
            "\n"
            "print(f'PASS: scope clean — {len(changed)} files changed, all within refine scope')\n"
            "sys.exit(0)\n"
            "PYEOF"
        ),
        notes=(
            "Scope discipline gate for refine workflow. Stricter than formalize: "
            "allows only formal/Mcmc/Executable/**/*.lean, formal/Mcmc.lean, "
            "Samplers.ir, and .factory/*. Explicitly rejects formal/Mcmc/Kernel/ "
            "and formal/Mcmc/Hamiltonian/ (those belong to formalize)."
        ),
    )

    # ── Reference Generation ────────────────────────────────────

    nodes["fn_generate"] = FnNode(
        id="fn_generate",
        command="cd {project_path} && make generate",
        notes="Emit updated Samplers.ir from the Lean IR programs. Single-shot, no retry.",
        writes={"Samplers.ir"},
    )

    nodes["fn_check_generated"] = FnNode(
        id="fn_check_generated",
        command="cd {project_path} && make check-generated",
        notes="Verify committed IR matches Lean source. Fails if IR is stale.",
    )

    # ── Axioms and Manifest ────────────────────────────────────

    nodes["fn_axioms_check"] = FnNode(
        id="fn_axioms_check",
        command=(
            "cd {project_path} && python3 - <<'PYEOF'\n"
            "import sys, re, subprocess\n"
            "from pathlib import Path\n"
            "\n"
            "strategy = Path('.factory/strategy/current.md').read_text()\n"
            "\n"
            "theorems = set()\n"
            "for m in re.finditer(\n"
            "    r'\\b(?:theorem|lemma)\\s+([a-zA-Z_][a-zA-Z0-9_\\.]*)',\n"
            "    strategy,\n"
            "    re.IGNORECASE,\n"
            "):\n"
            "    theorems.add(m.group(1))\n"
            "\n"
            "output_lines = []\n"
            "for name in sorted(theorems):\n"
            "    result = subprocess.run(\n"
            "        ['lake', 'env', 'lean', '--run', f'import Mcmc\\n#print axioms {name}'],\n"
            "        capture_output=True, text=True, cwd='formal',\n"
            "    )\n"
            "    header = f'--- {name} ---'\n"
            "    output_lines.append(header)\n"
            "    output_lines.append(result.stdout.strip() if result.stdout.strip() else '(no output)')\n"
            "    if result.stderr.strip():\n"
            "        output_lines.append(f'stderr: {result.stderr.strip()}')\n"
            "    output_lines.append('')\n"
            "\n"
            "axioms_txt = '\\n'.join(output_lines)\n"
            "Path('.factory/axioms.txt').write_text(axioms_txt)\n"
            "print(f'Axiom disclosure for {len(theorems)} theorems written to .factory/axioms.txt')\n"
            "sys.exit(0)\n"
            "PYEOF"
        ),
        reads={".factory/strategy/current.md"},
        writes={".factory/axioms.txt"},
        notes=(
            "Axiom disclosure — runs #print axioms for each theorem name found "
            "in the strategy. Saves output to .factory/axioms.txt. Always exits 0 "
            "(axioms are disclosed, not gated)."
        ),
    )

    nodes["fn_manifest"] = FnNode(
        id="fn_manifest",
        command=(
            "cd {project_path} && python3 - <<'PYEOF'\n"
            "import json, sys, re, subprocess\n"
            "from pathlib import Path\n"
            "from datetime import datetime, timezone\n"
            "\n"
            "# Tier ordering for comparison\n"
            "TIER_ORDER = {\n"
            "    'modeled-kernel': 0,\n"
            "    'replay-spec': 1,\n"
            "    'conditional': 2,\n"
            "    'full-induced-law': 3,\n"
            "}\n"
            "\n"
            "# Read achieved tier\n"
            "tier_path = Path('.factory/refinement-tier.txt')\n"
            "if not tier_path.exists():\n"
            "    print('ERROR: .factory/refinement-tier.txt not found')\n"
            "    sys.exit(1)\n"
            "\n"
            "tier_lines = tier_path.read_text().strip().splitlines()\n"
            "achieved_tier = tier_lines[0] if tier_lines else 'unknown'\n"
            "theorem_name = tier_lines[1] if len(tier_lines) > 1 else 'unknown'\n"
            "\n"
            "requested_tier = '{tier}' or 'modeled-kernel'\n"
            "if not requested_tier:\n"
            "    requested_tier = 'modeled-kernel'\n"
            "\n"
            "# Read axiom disclosure\n"
            "axioms_path = Path('.factory/axioms.txt')\n"
            "axiom_disclosure = axioms_path.read_text() if axioms_path.exists() else ''\n"
            "\n"
            "commit = subprocess.run(\n"
            "    ['git', 'rev-parse', 'HEAD'],\n"
            "    capture_output=True, text=True,\n"
            ").stdout.strip()\n"
            "\n"
            "manifest = {\n"
            "    'workflow': 'refine',\n"
            "    'timestamp': datetime.now(timezone.utc).isoformat(),\n"
            "    'focus': '{focus}',\n"
            "    'tier': achieved_tier,\n"
            "    'requested_tier': requested_tier,\n"
            "    'theorem_name': theorem_name,\n"
            "    'axiom_disclosure': axiom_disclosure,\n"
            "    'commit': commit,\n"
            "    'retries': 0,\n"
            "    'disposition': 'success',\n"
            "}\n"
            "\n"
            "# Check tier meets requested level\n"
            "achieved_rank = TIER_ORDER.get(achieved_tier, -1)\n"
            "requested_rank = TIER_ORDER.get(requested_tier, -1)\n"
            "if achieved_rank < requested_rank:\n"
            "    manifest['disposition'] = 'tier_mismatch'\n"
            "    Path('.factory/manifest-refine.json').write_text(json.dumps(manifest, indent=2))\n"
            "    print(f'FAIL: achieved tier {achieved_tier} (rank {achieved_rank}) '\n"
            "          f'is weaker than requested tier {requested_tier} (rank {requested_rank})')\n"
            "    sys.exit(1)\n"
            "\n"
            "Path('.factory/manifest-refine.json').write_text(json.dumps(manifest, indent=2))\n"
            "print(f'Manifest written: tier={achieved_tier}, theorem={theorem_name}')\n"
            "sys.exit(0)\n"
            "PYEOF"
        ),
        reads={".factory/refinement-tier.txt", ".factory/axioms.txt"},
        writes={".factory/manifest-refine.json"},
        notes=(
            "Write .factory/manifest-refine.json with structured workflow metadata: "
            "tier, requested_tier, theorem_name, axiom_disclosure, commit, retries, "
            "and disposition. Fails if achieved tier is weaker than requested tier. "
            "Tier ordering: full-induced-law > conditional > replay-spec > modeled-kernel."
        ),
    )

    # ── Archivist (final archive, non-blocking) ────────────────

    nodes["archivist"] = AgentNode(
        id="archivist",
        role=AgentRole.ARCHIVIST,
        prompt_template=(
            "Archive the refinement results. "
            "Record: what kernel was refined, the refinement tier achieved, "
            "the theorem connecting IR to kernel, axiom disclosures, "
            "and any lessons learned from compilation iterations."
        ),
        reads={
            ".factory/reviews/builder-latest.md",
            ".factory/manifest-refine.json",
            ".factory/axioms.txt",
        },
        writes={".factory/archive/refine-record.md"},
        blocking=False,
    )

    # ── Edges ───────────────────────────────────────────────────

    edges = [
        # Precondition -> Research
        Edge(source="precondition_check", target="fork_research"),
        # Research fork -> researchers -> join
        Edge(source="fork_research", target="researcher_kernel"),
        Edge(source="fork_research", target="researcher_ir_patterns"),
        Edge(source="researcher_kernel", target="join_research"),
        Edge(source="researcher_ir_patterns", target="join_research"),
        Edge(source="join_research", target="gate_research"),
        # Research gate
        Edge(source="gate_research", target="strategist", condition=VerdictType.PROCEED),
        Edge(source="gate_research", target="fork_research", condition=VerdictType.RELOOP),
        # Strategy
        Edge(source="strategist", target="gate_strategy"),
        Edge(source="gate_strategy", target="builder_refine", condition=VerdictType.PROCEED),
        Edge(source="gate_strategy", target="strategist", condition=VerdictType.RELOOP),
        # Build Phase: Refinement
        Edge(source="builder_refine", target="gate_refine"),
        Edge(source="gate_refine", target="fn_no_sorry", condition=VerdictType.PROCEED),
        Edge(source="gate_refine", target="builder_refine", condition=VerdictType.RELOOP),
        # Post-build checks
        Edge(source="fn_no_sorry", target="fn_refinement_check"),
        Edge(source="fn_refinement_check", target="fn_scope_check"),
        Edge(source="fn_scope_check", target="fn_generate"),
        Edge(source="fn_generate", target="fn_check_generated"),
        Edge(source="fn_check_generated", target="fn_axioms_check"),
        Edge(source="fn_axioms_check", target="fn_manifest"),
        Edge(source="fn_manifest", target="archivist"),
    ]

    # ── Trigger ─────────────────────────────────────────────────

    def trigger(state: ProjectState, ctx: dict[str, Any]) -> bool:
        return ctx.get("mode") == "refine" and bool(ctx.get("focus"))

    return Workflow(
        name="refine",
        nodes=nodes,
        edges=edges,
        start_node="precondition_check",
        terminal=True,
        trigger=trigger,
    )
