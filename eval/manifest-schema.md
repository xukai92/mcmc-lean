# Run manifest schema audit

## Current manifest fields (from hardened workflows)

| Field | Present | Source |
|-------|---------|--------|
| workflow | yes | hardcoded in FnNode |
| focus | yes | {focus} template |
| conformance_tier | yes | {conformance_tier} template |
| atol / rtol | yes | {atol}, {rtol} templates |
| commit (end) | yes | `git rev-parse HEAD` |
| timestamp | yes | `date -u` |
| qa_conformance exitcode | yes | sentinel file |
| qa_tests exitcode | yes | sentinel file |
| qa_benchmark exitcode | yes | sentinel file |
| qa_statistical exitcode | yes | sentinel file |
| disposition | yes | "keep" if gate_qa passes |

## Missing fields needed by analysis plan

| Field | Needed for | Gap severity | Remediation |
|-------|-----------|-------------|-------------|
| commit (start) | measuring diff size | medium | capture at precondition_check |
| model version | version pinning | high | capture from `claude --version` or env |
| token count | RQ2 productivity | high | extract from agent session transcript |
| tool call count | RQ2 productivity | high | extract from agent session transcript |
| retry count | RQ2 productivity | high | count RELOOP iterations (builder restarts) |
| human gate decisions | RQ2 | medium | record verbatim in human gate log |
| wall time (seconds) | RQ2 | medium | compute from start/end timestamps |
| prompts | reproducibility | medium | capture from factory agent dispatch |
| strategy approved | procedure record | low | human gate fires → record decision |
| patches (commit list) | traceability | low | `git log --oneline start..end` |

## Remediation plan

### Fields capturable from manifest enhancement (workflow changes)
- `commit_start`: add `git rev-parse HEAD` at precondition_check, store in env
- `wall_time_seconds`: compute `end_timestamp - start_timestamp`
- `retry_count`: count builder invocations from review files

### Fields capturable externally (no workflow changes needed)
- `model_version`: record at batch start in `versions.json`
- `token_count`: extract from Claude Code / Codex session transcripts
- `tool_call_count`: extract from session transcripts
- `human_gate_decisions`: record verbatim in separate human log
- `prompts`: factory dispatch command is the prompt (recorded in tmux capture)

### Conclusion
The manifest captures QA gate results and provenance but lacks productivity
metrics (tokens, tool calls, retries) and the starting commit. Productivity
metrics are best captured from agent session transcripts rather than the
workflow manifest. The starting commit should be added to the manifest in a
future workflow update. For the evaluation, external capture (session
transcripts + batch-level version pinning) fills the gaps without requiring
immediate workflow changes.
