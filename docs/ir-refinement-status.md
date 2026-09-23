# IR–Kernel refinement status

Per-program tracking of whether each IR program in `Samplers.ir` has a proved
Lean theorem connecting it to its mathematical kernel. Updated manually; run
the audit command below to check for drift.

## Status codes

- **proved**: a Lean theorem states the IR interpreter output equals the
  mathematical kernel definition.
- **open**: the IR program exists and generates Reference Julia, but no
  refinement theorem connects it to a proved kernel.
- **conditional**: a partial refinement exists under explicit hypotheses.

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
grep -rn 'theorem.*refines\|theorem.*programKernel' \
  formal/Mcmc/Executable/ --include='*.lean' | \
  sed 's/.*theorem //' | cut -d' ' -f1 | sort
```

## Current status (26 programs, IR version 29)

### Proved (8/26)

| IR program | Refinement theorem | File |
|---|---|---|
| `categorical_index!` | `runCategorical_refines` | Finite/CompilerIRInterpreter.lean |
| `finite_mh_step!` | `runMetropolisHastings_refines` | Finite/CompilerIRInterpreter.lean |
| `gaussian_rwmh_step!` | `gaussianRwmhProgramKernel_refines` | Continuous/RWMH.lean |
| `scalar_barker_rwmh_step!` | `gaussianBarkerRwmhProgramKernel_refines` | Continuous/BarkerRWMH.lean |
| `scalar_hmc_step!` | `runScalarHmc_refines` | Continuous/CompilerIR.lean |
| `vector_hmc_step!` | `runVectorHmc_refines` | Continuous/CompilerIR.lean |
| `scalar_dr_ghmc_step!` | `runScalarDrGhmc_refines` | Continuous/CompilerIR.lean |
| `active_sketch_smmala_step!` | `activeSketchSmmalaProgramKernel_refines` | Continuous/ActiveSketchSMMALA.lean |

### Open — kernel theorem exists, refinement open (10/26)

| IR program | Kernel theorem | Gap |
|---|---|---|
| `scalar_mala_step!` | `Kernel.Langevin` invariance | Stochastic command-to-kernel composition |
| `vector_mala_step!` | `Kernel.Langevin` invariance | Same as scalar |
| `dense_pmala_step!` | `Kernel.PositionDependentMALA` | Measurability + Gaussian normalization |
| `multinomial_hmc_step!` | `positionMultinomialHMC` invariance | Command-to-multinomial-kernel |
| `diagonal_hmc_step!` | metric HMC invariance | Metric-specific command refinement |
| `dense_hmc_step!` | metric HMC invariance | Same |
| `diagonal_multinomial_hmc_step!` | metric multinomial HMC | Metric-specific command refinement |
| `dense_multinomial_hmc_step!` | metric multinomial HMC | Same |
| `vector_gauss_legendre_hmc_step!` | GL integrator theorems | Implicit-solver command refinement |
| `multi_marginal_transport_hmc_step!` | marginal preservation | Command-to-coupling-kernel |

### Open — kernel theorem partial or absent (8/26)

| IR program | Status | Gap |
|---|---|---|
| `classical_rmhmc_step!` | kernel conditional on exact solver | Solver certificate + command refinement |
| `approximate_classical_rmhmc_step!` | kernel conditional | Approximate solver tolerance + refinement |
| `dense_rmhmc_step!` | kernel conditional | Dense metric Riemannian refinement |
| `random_sketch_rmhmc_step!` | kernel conditional | Sketch-specific refinement |
| `relativistic_multinomial_hmc_step!` | kernel conditional | Relativistic integrator refinement |
| `certified_relativistic_multinomial_hmc_step!` | kernel conditional | Certificate + refinement |
| `coupled_multinomial_hmc_step!` | coupling theorem exists | Coupled-kernel command refinement |
| `coupled_gaussian_rwmh_step!` | coupling theorem exists | Coupled-RWMH command refinement |
| `xu21_coupled_step!` | Xu21 coupling theorems | Mixture command refinement |

## Priority for closing gaps

### High (paper-critical)
1. `scalar_mala_step!` / `vector_mala_step!` — MALA is a core sampler;
   the kernel theorem exists, the gap is the stochastic command composition.
2. `multinomial_hmc_step!` — used in benchmarks; kernel theorem exists.

### Medium (completeness)
3. `diagonal_hmc_step!` / `dense_hmc_step!` — metric endpoint HMC variants.
4. `diagonal_multinomial_hmc_step!` / `dense_multinomial_hmc_step!` — metric
   multinomial variants.
5. `dense_pmala_step!` — position-dependent MALA.

### Lower (specialized)
6. Riemannian/relativistic family (4 programs) — conditional on solver.
7. Coupling family (3 programs) — coupling theorems exist, command refinement open.
8. `multi_marginal_transport_hmc_step!` — newly added.

## Changelog

- 2026-09-23: Initial creation. 8/26 proved, 10 open with kernel, 8 open
  with partial kernel.
