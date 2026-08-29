# Maintained sampler obligation matrix

This is the common consolidation ledger for sampler families already exposed
by the repository. It complements the property-oriented
[progress matrix](progress.md): each row follows one implementation vertically
from mathematical semantics to runtime evidence. A check in one column never
fills another column implicitly.

## Evidence vocabulary

- **Kernel theorem**: Lean proves validity, reversibility, invariance, or a
  stated convergence result for the named mathematical transition.
- **Command refinement**: Lean identifies the exact command denotation with
  that mathematical transition.
- **Trace refinement**: Lean proves deterministic ideal-real replay for
  explicit events, without claiming a platform RNG or floating-point theorem.
- **Conformance**: Julia compares maintained paths on the same explicit events
  or seed. This is test evidence.
- **Diagnostics**: seeded properties or distributional checks. These are
  empirical evidence.

## Current vertical slices

| Family | Exact mathematical result | Executable presentation | Julia Reference | Optimized path | Current bridge boundary |
|---|---|---|---|---|---|
| Finite MH | Finite transition, reversibility, and stationarity | Typed finite IR with Lean parse/decode/re-render | Interpreted generated artifact | Maintained comparison | Exact finite trace and artifact checks; Julia interpreter correspondence is tested |
| Gaussian RWMH | General-state Markov, reversible, invariant kernel | Continuous command IR | Canonical public path | Generic scalar comparison | Full exact command-kernel refinement; Float/platform/RNG boundary remains explicit |
| Isotropic MALA | Score-scaled general-state Markov, reversible, invariant kernel | Scalar/vector typed command IR | Artifact-interpreted Float64 paths | Generic scalar/vector paths | Kernel theorem, command formula, artifact checks, and replay conformance are present; full stochastic command-kernel refinement remains open |
| Dense PMALA | Lebesgue-correct drift and explicit state-dependent Gaussian density; conditional invariant kernel | Typed dense metric/derivative primitive | Artifact-interpreted Float64 path | Generic dense path | Measurability and Gaussian row normalization are explicit formal hypotheses; command-to-kernel and platform refinement remain open |
| Transport HMC | Exact conjugation and multinomial-HMC invariance conditional on the target-pushforward identity | Existing vector-HMC descriptor with fixed map callbacks | Float64 endpoint path | Generic endpoint path | Concrete change of variables, callback consistency, endpoint command-to-kernel, and learned-map adaptation remain explicit |
| Likelihood-informed HMC | Common-target active/complement composition theorem | Host composition over vector-HMC plus Gaussian-reference pCN | Float64 composed path | Generic composed path | Conditional-HMC and pCN component invariance plus typed schedule refinement remain open; basis learning is warmup-only |
| Fixed-step endpoint HMC | Phase and refreshed/projected position invariance | Scalar/vector endpoint descriptors | Canonical public scalar/vector paths | Generic scalar/vector paths | Integrator and trace refinement proved; full stochastic command-to-position-kernel composition remains open |
| Fixed multinomial HMC | Exact randomized-trajectory invariance | Unit and constant-metric descriptors | Unit, diagonal, and dense paths | Generic prepared-metric paths | Exact ideal transition theory; Julia lowering and floating execution remain test-supported |
| Fixed-time/jittered/tempered HMC | Reuses fixed positive-step kernels where applicable | Runtime constructors | Fixed-time endpoint path | Jittered and tempered paths | Runtime complete; state-independent jitter mixture and integrator-specific refinement are not uniformly packaged |
| Partial-momentum HMC | Momentum-transition invariance foundations | Runtime composition | — | Fixed-step endpoint path | Runtime complete; composition refinement remains open |
| Completed-tree NUTS Reference | Checked completed-tree C.4 stationarity | Typed bounded-tree descriptor | Canonical `NUTS` Reference | — | Exact tree theorem; callback, Float trajectory, and platform boundaries remain explicit |
| Production-shaped NUTS | Shared structural online/completed-tree lemmas | Independent runtime engine | — | `Optimized.NUTS` | Empirical and structural conformance only; transition equivalence to the Reference is not claimed |
| Generalized/relativistic HMC | Exact solver, reversal, volume, and invariant clients at documented scopes | Specialized typed descriptors and certified primitives | Solver and sampler paths | Generic maintained paths | Exact clients plus conditional certificates; no universal Float solver refinement |
| Finite DHMC | Exact finite/discontinuous foundations | Generated finite categorical program | Public generated path | Generic categorical path | Deterministic and distributional conformance at the documented finite boundary |
| Slice sampling | Exact finite and guarded practical invariance results | Finite and trace-bearing continuous presentations | Finite, bounded, and stepping-out paths | Maintained comparisons | Practical trace decisions have conditional certificates; platform log/RNG evidence remains explicit |
| Reversible jump | Exact tagged-state MH clients with checked transports | Certified runtime primitives | Scalar, spatial, and shear clients | Maintained comparisons | Client-specific transport theorem plus runtime tests; no arbitrary-diffeomorphism compiler |

## Consolidation rules

1. Every new or materially changed maintained path updates one row here or a
   linked detailed development record.
2. Public constructors must identify whether they route through Reference or
   an independent Optimized implementation.
3. Reference/Optimized equality tests record event consumption as well as the
   returned state whenever an explicit-event interface exists.
4. Runtime-only variants remain labelled runtime-only until their exact
   transition is connected to a proved kernel.
5. Universal IEEE-754, `libm`, serializer, and RNG correctness are parked;
   execution-specific certificates may strengthen a row without becoming a
   prerequisite for ordinary execution.

The [sampler development record](sampler-development-template.md) is the
copyable detailed form. The [Gaussian RWMH](rwmh-development-record.md) and
[fixed-step HMC](hmc-development-record.md) records demonstrate respectively a
closed bridge and a deliberately visible composition gap.
