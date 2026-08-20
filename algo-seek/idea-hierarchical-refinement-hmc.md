# Hierarchical refinement HMC: Leanification roadmap

This note compares the work required to formalize DR-G-HMC, ATLAS, and the
proposed hierarchical refinement HMC sampler. Effort levels describe relative
proof and implementation risk, not elapsed-time estimates.

The intended order is mathematical kernel, exact executable semantics, and
only then refinement to the maintained Julia implementation. Exact-real Lean
correctness does not by itself establish correctness of floating-point
execution.

## Effort summary

| Algorithm | Mathematical kernel and invariance | Executable semantics | Lean--Julia connection | Overall risk |
|---|---|---|---|---|
| Two-stage DR-G-HMC | Medium | Medium | Medium | Medium |
| Bounded-retry DR-G-HMC | Medium--high | Medium | Medium | Medium--high |
| Abstract ATLAS | High | High | High | High |
| Concrete ATLAS | Very high | Very high | Very high | Very high |
| Hierarchical refinement HMC | High, after the design is fixed | High | High | Very high while the design remains open |

## DR-G-HMC

DR-G-HMC is the most direct formalization target because the repository
already contains leapfrog dynamics, deterministic Metropolis correction,
endpoint HMC, abstract invariant momentum transitions, kernel composition,
and exact-real and Julia trajectory machinery.

### Missing mathematical components

1. Define a concrete finite-dimensional Gaussian AR(1) partial-momentum
   refresh kernel.
2. Prove that the AR(1) transition preserves the Gaussian momentum law.
3. Define a generic two-stage delayed-rejection transition.
4. Derive its acceptance probability, including rejected forward and reverse
   ghost proposals and zero-probability cases.
5. Compose delayed rejection with persistent momentum and the required
   momentum flips.
6. Prove the resulting phase-space target invariant and then project to the
   position target when appropriate.

The first useful scope should contain exactly two step sizes, such as
`epsilon` and `epsilon / 2`. A bounded list of retries can be added after the
two-stage bookkeeping is stable.

### Executable components

- A bounded retry trace containing step sizes, uniforms, endpoints, energies,
  and branch outcomes.
- Exact semantics for replaying that trace.
- Failure behavior for exhausted retries and invalid numerical results.
- Reference and optimized Julia implementations sharing deterministic traces.
- Tests covering first-stage acceptance, retry acceptance, total rejection,
  and momentum direction after every branch.

### Main risks

The main work is not leapfrog itself. It is delayed-rejection algebra,
measurability, reverse ghost-path reconstruction, and making every momentum
flip agree between the mathematical and executable presentations.

## ATLAS

ATLAS combines diagnostic trajectories, local curvature estimation,
state-dependent step-size distributions, no-u-turn trajectory selection,
delayed rejection, reverse reconstruction, branch compatibility, and several
fallback paths. It should be split into abstract and concrete scopes.

### Abstract ATLAS

Treat the local step-size-distribution constructor as an abstract measurable
operation. State explicitly the properties required by the acceptance rule
and reverse reconstruction. Reuse the existing dynamic-trajectory and
delayed-rejection layers wherever possible.

Required work includes:

1. A kernel for locally sampling the trajectory parameters.
2. Forward and reverse diagnostic construction.
3. A formal branch type describing every success and fallback path.
4. Same-branch compatibility checks.
5. The corresponding acceptance probabilities.
6. Invariance of the complete branch mixture.

This scope establishes the sampler architecture without claiming that a
particular floating-point L-BFGS or power iteration implements the abstract
curvature constructor.

### Concrete ATLAS

A concrete formalization additionally needs bounded executable definitions
for:

- trajectory-based secant pairs;
- L-BFGS updates;
- power iteration and its stopping rule;
- validity and failure checks;
- construction and sampling of the local lognormal step-size law;
- no-u-turn diagnostics;
- reverse recomputation; and
- all fallback branches.

Connecting this layer to Julia requires explicit treatment of linear algebra,
random-number draws, transcendental functions, stopping tolerances, and
floating-point failure. This is substantially larger than proving the
abstract sampler invariant.

### Main risks

ATLAS has a large control-flow surface, and its reverse proposal probability
depends on diagnostic computations at both endpoints. Small discrepancies in
branch classification or numerical stopping behavior affect the transition,
not merely its performance.

## Hierarchical refinement HMC

The proposed sampler should not be formalized until its transition is fully
specified and a prototype demonstrates a practical advantage. The present
idea leaves several choices open:

- the refinement diagnostic;
- whether refinement replaces a segment or creates a branch;
- how a changed endpoint affects the remaining trajectory;
- which coarse and fine nodes remain eligible;
- the probability law of the generated hierarchy;
- the final selection rule;
- reverse-hierarchy reconstruction; and
- maximum depth and failure behavior.

### Expected mathematical components

1. A typed coarse/fine trajectory hierarchy with bounded depth.
2. A measurable, path-dependent generation law.
3. A precise account of force evaluations and shared states.
4. An equivariance, rerooting, or extended-state reversal theorem.
5. Correction for asymmetric hierarchy-generation probabilities when
   symmetry is unavailable.
6. Target-weighted candidate selection over eligible hierarchy nodes.
7. A checked identity or coarser-level fallback.
8. Phase-space invariance and position-space projection.

The repository's certified finite trees and orbit-multinomial selection are
useful precedents, but they do not automatically justify a state-dependent
general-state hierarchy.

### Expected executable components

- A bounded hierarchy representation shared by Lean and Julia.
- Deterministic generation and selection traces.
- Batched or parallel execution of refinement branches where dependencies
  allow it.
- Exact gradient-evaluation accounting.
- Reference and optimized implementations.
- Comparative experiments against fixed HMC, NUTS, DR-HMC, DR-G-HMC, and
  ATLAS on multiscale and ordinary targets.

### Main risks

The largest risk is algorithmic rather than proof-engineering: refinement
changes a segment endpoint, so the downstream trajectory generally changes as
well. If most downstream work must be recomputed, the hierarchy may provide
little reuse. A correction that requires reconstructing the hierarchy from
every candidate could also remove its practical advantage.

## Recommended development order

1. Specify a one-level hierarchical algorithm precisely enough to count every
   gradient evaluation and proposal probability.
2. Prototype it in Julia before constructing its Lean kernel.
3. Formalize two-stage DR-G-HMC, including the Gaussian AR(1) refresh and all
   momentum-flip branches.
4. Extend delayed rejection to a bounded retry list if the additional
   generality is useful.
5. Use the delayed-rejection layer to formalize abstract ATLAS as a comparison
   client.
6. Proceed with the hierarchical Lean development only if the prototype shows
   a benefit and the hierarchy-generation law has a tractable reverse or
   rerooting construction.

## Completion boundaries

For each sampler, track these claims separately:

- the exact mathematical kernel is Markov;
- the exact kernel preserves its stated phase or position target;
- the bounded executable presentation denotes that kernel;
- the generated artifact preserves the executable presentation;
- the Julia Reference interpreter implements the artifact semantics;
- the optimized Julia path agrees on deterministic traces; and
- floating-point, callback, and RNG assumptions are explicitly recorded.

No invariance result should be presented as convergence, and no exact-real
result should be presented as an unconditional Float64 theorem.
