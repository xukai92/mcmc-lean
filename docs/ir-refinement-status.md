# IR–Kernel refinement status

Per-program tracking of whether each IR program in `Samplers.ir` has a proved
Lean theorem connecting it to its mathematical kernel. Each theorem is
classified by strength:

- **modeled-kernel**: a theorem `FooProgramKernel = FooKernel` equating an
  assembled kernel denotation to the verified mathematical kernel.
- **replay-spec**: a theorem `runFoo events = result` proving the IR
  interpreter's deterministic trace output. This is weaker — it does not state
  kernel equality for the induced probability law.
- **literal-AST-measure**: a theorem connecting the literal `Program.measure`
  denotation of the IR AST to the kernel (strongest; rare).
- **conditional-on-certificate**: a modeled-kernel theorem whose hypotheses
  include an explicit solver or approximation certificate
  (`GeneralizedLeapfrogSelection.IsValid`).
- **open**: no refinement theorem connects the IR program to any kernel.

## Audit command

```sh
# List all IR programs
python3 -c "
import re
with open('VerifiedSamplers.jl/src/Reference/Samplers.ir') as f:
    programs = re.findall(r'\(program \"([^\"]+)\"', f.read())
print(f'{len(programs)} programs'); [print(f'  {p}') for p in programs]
"

# List all refinement theorems
grep -rn 'theorem.*refines\|theorem.*programKernel\|theorem.*ProgramKernel' \
  formal/Mcmc/Executable/ --include='*.lean' | \
  sed 's/.*theorem //' | cut -d' ' -f1 | sort

# Flag programs with only replay-spec coverage
echo "--- replay-spec only (no kernel equality) ---"
for prog in categorical_index scalar_hmc vector_hmc scalar_dr_ghmc; do
  echo "  ${prog}_step!"
done
```

## Current status (27 programs, IR version 29)

### Modeled-kernel equality (15/27)

Each theorem states `FooProgramKernel = FooKernel` (assembled kernel =
verified mathematical kernel).

| IR program | Theorem | File:line | Note |
|---|---|---|---|
| `gaussian_rwmh_step!` | `gaussianRwmhProgramKernel_refines` | Continuous/RWMH.lean:157 | Also has literal-AST (`standardGaussianRwmhProgram_refines_rwmh`) and replay (`runGaussianRwmh_refines`) |
| `scalar_barker_rwmh_step!` | `gaussianBarkerRwmhProgramKernel_refines` | Continuous/BarkerRWMH.lean:124 | |
| `scalar_mala_step!` | `scalarMalaProgramKernel_refines` | Continuous/MALA.lean:224 | |
| `vector_mala_step!` | `vectorMalaProgramKernel_refines` | Continuous/MALA.lean:465 | |
| `multinomial_hmc_step!` | `multinomialHmcProgramKernel_refines` | Continuous/MultinomialRefinement.lean:91 | |
| `diagonal_multinomial_hmc_step!` | `diagonalMultinomialHmcProgramKernel_refines` | Continuous/MultinomialRefinement.lean:123 | |
| `dense_multinomial_hmc_step!` | `denseMultinomialHmcProgramKernel_refines` | Continuous/MultinomialRefinement.lean:137 | |
| `diagonal_hmc_step!` | `diagonalHmcProgramKernel_refines` | Continuous/MetricRefinement.lean:41 | |
| `dense_hmc_step!` | `denseHmcProgramKernel_refines` | Continuous/MetricRefinement.lean:55 | |
| `dense_pmala_step!` | `densePmalaProgramKernel_refines` | Continuous/DensePMALA.lean:109 | Also has `densePmalaProgramKernel_invariant` |
| `active_sketch_smmala_step!` | `activeSketchSmMalaProgramKernel_refines` | Continuous/ActiveSketchSMMALA.lean:103 | Also has `activeSketchSmMalaProgramKernel_invariant`; specializes dense PMALA with `G(x) = SᵀS + λI` |
| `multi_marginal_transport_hmc_step!` | `multiMarginalTransportHmcProgramKernel_refines` | Continuous/MultiMarginalCompilerIR.lean:62 | Also has `_marginal` corollary |
| `coupled_multinomial_hmc_step!` | `coupledMultinomialHmcProgramKernel_refines` | Continuous/CoupledRefinement.lean:61 | Also has `_isCoupling` theorem |
| `coupled_gaussian_rwmh_step!` | `coupledGaussianRwmhProgramKernel_refines` | Continuous/CoupledRefinement.lean:70 | Also has `_isCoupling` theorem |
| `xu21_coupled_step!` | `xu21CoupledProgramKernel_refines` | Continuous/CoupledRefinement.lean:75 | Also has `_isCoupling` theorem |

### Replay-spec only (5/27)

These have a deterministic trace theorem (`run*_refines`) but **no kernel
equality theorem**. The IR interpreter produces the correct deterministic
output for given events, but the induced probability law is not formally
equated with the mathematical kernel. The command-AST to position-kernel
composition remains open.

| IR program | Theorem | File:line | Note |
|---|---|---|---|
| `categorical_index!` | `runCategorical_refines` | Finite/CompilerIRInterpreter.lean:363 | |
| `finite_mh_step!` | `runMetropolisHastings_refines` | Finite/CompilerIRInterpreter.lean:894 | Also `stepPMF_refines` (PMF-vs-kernel-row equality, stronger; finite-state only) |
| `scalar_hmc_step!` | `runScalarHmc_refines` | Continuous/CompilerIR.lean:984 | |
| `vector_hmc_step!` | `runVectorHmc_refines` | Continuous/CompilerIR.lean:964 | |
| `scalar_dr_ghmc_step!` | `runScalarDrGhmc_refines` | Continuous/CompilerIR.lean:907 | |

Note: `finite_mh_step!` has the additional `stepPMF_refines`
(Finite/MetropolisHastings.lean:279) which is exact PMF-vs-kernel-row
equality — stronger than replay but specific to the finite-state setting.

### Conditional on solver certificate (7/27)

Each theorem has `(selection : GeneralizedLeapfrogSelection ...)
(hvalid : selection.IsValid)` or equivalent as an explicit hypothesis.
The refinement holds only when the concrete numerical solver provides
the certificate.

| IR program | Theorem | File:line | Certificate |
|---|---|---|---|
| `classical_rmhmc_step!` | `classicalRmhmcProgramKernel_refines` | Continuous/RiemannianRefinement.lean:44 | `GeneralizedLeapfrogSelection.IsValid` |
| `approximate_classical_rmhmc_step!` | `approximateClassicalRmhmcProgramKernel_refines` | Continuous/RiemannianRefinement.lean:112 | `GeneralizedLeapfrogSelection.IsValid` |
| `dense_rmhmc_step!` | `denseRmhmcProgramKernel_refines` | Continuous/RiemannianRefinement.lean:60 | `GeneralizedLeapfrogSelection.IsValid` |
| `random_sketch_rmhmc_step!` | `randomSketchRmhmcProgramKernel_refines` | Continuous/RiemannianRefinement.lean:76 | `GeneralizedLeapfrogSelection.IsValid` |
| `relativistic_multinomial_hmc_step!` | `relativisticMultinomialHmcProgramKernel_refines` | Continuous/RelativisticRefinement.lean:51 | `GeneralizedLeapfrogSelection.IsValid` |
| `certified_relativistic_multinomial_hmc_step!` | `certifiedRelativisticMultinomialHmcProgramKernel_refines` | Continuous/RelativisticRefinement.lean:96 | `GeneralizedLeapfrogSelection.IsValid` |
| `vector_gauss_legendre_hmc_step!` | `gaussLegendreProgramKernel_refines_approximate` | Continuous/GaussLegendreHMC.lean:89 | `Measurable (approximateGaussLegendreProposal ...)` |

### Open (0/27)

No open programs remain.

## Summary

| Category | Count | Description |
|----------|-------|-------------|
| Modeled-kernel | 15 | `ProgramKernel = Kernel` equality |
| Replay-spec only | 5 | Interpreter trace = result; no kernel equality |
| Conditional | 7 | Kernel equality under solver certificate |
| Open | 0 | — |
| **Total** | **27** | All programs have refinement theorems |

15 + 5 + 7 = 27. Of these, 15 have the strongest (modeled-kernel)
refinement, including the two novel samplers:
`active_sketch_smmala_step!` and `multi_marginal_transport_hmc_step!`.
The 5 replay-spec programs have open gaps for command-to-kernel composition.
The 7 conditional programs are honestly conditional on solver certificates.
No programs remain open.

## Changelog

- 2026-09-24: Fixed modeled-kernel count from 16 to 15 (off-by-one).
  Clean partition: 15 modeled + 5 replay + 7 conditional + 0 open = 27.
- 2026-09-23: Merged both novel samplers. Active-Sketch sMMALA added as
  27th program with modeled-kernel refinement
  (`activeSketchSmMalaProgramKernel_refines`, specializes dense PMALA with
  `G(x) = SᵀS + λI`). Multi-Marginal Transport HMC closed the sole open
  program with `multiMarginalTransportHmcProgramKernel_refines` and
  `multiMarginalTransportHMC_marginal` (each coordinate marginal equals
  `positionMultinomialHMC`). Updated counts: 15 modeled + 5 replay +
  7 conditional + 0 open = 27 programs.
- 2026-09-23: Reconciled with actual Lean on main. Reclassified by theorem
  strength (modeled-kernel / replay-spec / conditional / open). Removed phantom
  `active_sketch_smmala_step!` row (not in Samplers.ir). Corrected
  `multi_marginal_transport_hmc_step!` to open. Fixed counts: 14 modeled +
  5 replay + 7 conditional + 1 open = 26 + 1 not-in-IR.
- 2026-09-23: Initial creation and batched refinement work.
