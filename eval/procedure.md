# Evaluation procedure

## Version pinning

Every run batch pins these versions before starting:

| Component | Source | Current |
|-----------|--------|---------|
| Factory | `.factory/factory-version` | remote-factory==0.2.0 |
| Lean toolchain | `formal/lean-toolchain` | pinned per repo |
| Julia | `juliaup status` | 1.12.5 |
| Claude Code | `claude --version` | record at batch start |
| Codex | `codex --version` | record at batch start |
| Repository | `git rev-parse HEAD` | pin per task in YAML |

Versions are recorded in the run manifest and in a batch-level
`eval/runs/<batch-id>/versions.json`.

## Trial order

Within each task, the 4 conditions are run in a randomized order.
The randomization seed is generated once per batch and recorded:

```
EVAL_SEED=$(python3 -c "import secrets; print(secrets.randbelow(2**32))")
```

The order for task `i` with conditions `[A, B, C, D]` is determined by:
```python
import random
rng = random.Random(EVAL_SEED + task_index)
order = rng.sample([A, B, C, D], 4)
```

## Stopping rules

### Formalize tasks
- Theory builder: max 5 `lake build` RELOOP iterations
- IR builder: max 3 `lake build` RELOOP iterations
- Wall time: cap per task (specified in task YAML)
- If all retries exhausted: record as failure, retain all artifacts

### Optimize tasks
- Builder: max 3 RELOOP iterations
- Wall time: cap per task (specified in task YAML)
- If all retries exhausted: record as failure, retain all artifacts

### Direct conditions
- Same wall time cap as factory conditions
- No managed retries (agent decides its own retry strategy)
- Same final evaluator gates applied post hoc

## Human gate responses

All human gate decisions use standardized phrasing:

**Strategy approval gate (formalize + optimize):**
> "Approved. The [strategy/plan] is mathematically sound. Proceed."

Approve if and only if:
1. The mathematical specification is correct
2. The proposed theorems match the intended property
3. No obvious gaps in the proof plan

If the strategy has a mathematical error, respond:
> "Needs revision. [specific issue]. Revise and resubmit."

All human gate responses are recorded verbatim in the run log.

## Run retention

- Every run (success or failure) is retained under `eval/runs/<batch-id>/`
- Each run directory contains: manifest.json, git patches, QA output files,
  agent transcripts (where available), timing data
- Pilots are stored under `eval/pilots/` and labeled PILOT in manifests
- Confirmatory runs are stored under `eval/runs/` and never mixed with pilots

## Pilot separation

Runs from workflow development (Barker, DR-G-HMC, MALA, multinomial) are
labeled as pilots in their task YAML (`pilot: true`) and excluded from
confirmatory analysis. They may be reported separately as development examples
but never presented as held-out evidence.
