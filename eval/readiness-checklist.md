# Evaluation readiness checklist

## Protocol artifacts
- [x] Task fixtures committed (eval/tasks/*.yaml) — 12 tasks
- [x] Conditions defined (eval/conditions.yaml) — 4 conditions, 2 paired comparisons
- [x] Procedure documented (eval/procedure.md) — pinning, trial order, stopping, human gates
- [x] Analysis plan pre-registered (eval/analysis-plan.md) — primary/secondary metrics, statistical tests
- [x] Manifest schema audited (eval/manifest-schema.md) — gaps identified with remediation plan

## Starting commits
- [x] All tasks pinned to 5c7b9c7 (current HEAD with hardened gates + DR-G-HMC)

## Version pinning
- [ ] Claude Code version recorded for batch
- [ ] Codex version recorded for batch
- [x] Factory version pinned (.factory/factory-version: remote-factory==0.2.0)
- [x] Lean toolchain pinned (formal/lean-toolchain)
- [x] Julia version noted (1.12.5)

## Gate validation
- [ ] Pilot validation run completed (optimize-dense-pmala, factory-claude)
- [ ] Hardened conformance gate fires correctly
- [ ] Hardened scope check gate fires correctly
- [ ] Manifest.json produced with expected fields
- [ ] Expected-failure task rejected by gate (both formalize and optimize)

## Human gate preparation
- [x] Standardized response template drafted (procedure.md)
- [ ] Direct-condition task prompt drafted (strips factory, preserves task/tools/budget)

## Randomization
- [ ] Trial randomization seed generated for batch

## Remaining before full matrix
- [ ] Pilot validation passed
- [ ] Manifest gaps remediated or external capture confirmed
- [ ] Direct-condition prompts finalized
- [ ] Batch schedule drafted (which tasks on which days)
- [ ] Expert reviewers identified for blinded formalize assessment
