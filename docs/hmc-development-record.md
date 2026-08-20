# Fixed-step HMC development record

This applies the [sampler-development template](sampler-development-template.md)
to the existing scalar, unit-mass, fixed-step endpoint HMC path. It deliberately
records a weaker execution bridge than the RWMH record: the mathematical
kernel, integrator correspondence, and deterministic replay results exist, but
there is not yet one theorem equating the full command's stochastic kernel to
the refreshed/projected position kernel.

## 1. Mathematical identity

- **State space:** scalar position `ℝ`; the formal kernel is stated through the
  one-coordinate position and phase-space interfaces.
- **Target:** a position measure whose product with standard Gaussian momentum
  equals the phase Boltzmann target.
- **Proposal:** refresh momentum, apply a fixed number of leapfrog steps, flip
  momentum, and apply endpoint Metropolis correction.
- **Assumptions:** measurable potential and gradient, a finite step count, and
  the explicit position/momentum target factorization. The Julia API further
  requires a positive finite step size and a positive step count.
- **Claim level:** exact kernel validity and target invariance. No generic
  convergence-from-an-initial-state claim is made.

The invariance proof does not require the supplied leapfrog force to be the
derivative of the potential: reversibility, volume preservation, and the final
Metropolis correction are sufficient for invariance. Supplying the intended
derivative remains important for useful proposals and numerical behavior.

## 2. Formal evidence

| Obligation | Lean declaration | Status |
|---|---|---|
| Iterated mathematical integrator | `leapfrogN` | Existing definition |
| Endpoint phase kernel | `endpointHmcNPhaseKernel` | Existing construction |
| Phase-kernel validity | `endpointHmcNPhaseKernel_isMarkov` | Proved |
| Phase-target invariance | `endpointHmcNPhaseKernel_invariant` | Proved |
| Refreshed/projected position kernel | `endpointHmcNPositionKernel` | Existing construction |
| Position-target invariance | `endpointHmcNPositionKernel_invariant` | Proved under explicit factorization |
| State-independent finite schedules | `finiteScheduledEndpointHmcKernel_invariant` | Proved for finite choices of step size and step count |
| Generic convergence | — | Not claimed |

## 3. Executable presentation

`scalarHmcProgram` in
`formal/Mcmc/Executable/Continuous/CompilerIR.lean` consumes a standard-normal
momentum and unit-uniform draw. It computes the iterated leapfrog endpoint,
evaluates endpoint Hamiltonians through log-density and gradient callbacks,
and returns the proposal or current position.

`leapfrogN_scalarPhase` proves that the scalar IR integrator formula equals the
established Hamiltonian leapfrog iteration. `runScalarHmc_refines` proves the
ideal-real interpreter's result and exact trace consumption for explicit
events. The program is emitted as `scalar_hmc_step!` in the canonical artifact.

## 4. Refinement boundary

The formal path proves all of the following, separately:

- the scalar integrator formula equals mathematical leapfrog;
- the endpoint mathematical kernel is Markov and invariant;
- the position refresh/evolve/project kernel is invariant; and
- the ideal command interpreter returns the stated endpoint-MH decision for
  every valid explicit trace.

Unlike scalar Gaussian RWMH, no single existing theorem identifies an exact
kernel denotation of the complete `scalarHmcProgram` with
`endpointHmcNPositionKernel`. This is an explicitly recorded composition gap,
not an assumed equality. Julia parsing, `Float64` arithmetic, callbacks,
transcendentals, and RNG laws remain outside the exact-real results.

`finiteScheduledEndpointHmcKernel` additionally packages a state-independent
finite mixture of these position kernels. Its invariance theorem permits both
the step size and step count to depend on the independently sampled schedule
entry. It does not claim that Julia's continuously distributed jitter is that
finite law; joint parameter measurability and runtime lowering remain visible
continuous-jitter obligations.

## 5. Maintained Julia paths

| Layer | Declaration or file | Evidence |
|---|---|---|
| Canonical artifact | `scalar_hmc_step!` in `Reference/Samplers.ir` | regeneration check |
| Reference interpreter | `Reference.scalar_hmc_step!` | fixed-trace and validation tests |
| Public sampler | `ScalarHMC`, `step`, and `sample` | seeded API and moment tests |
| Optimized comparison | `Optimized.scalar_hmc_step!` | deterministic differential tests |

The public API routes through Reference. The Optimized implementation is an
independent handwritten comparison and does not inherit the Lean results.

## 6. Diagnostics

The integrated suite covers exact trace consumption, accept/reject behavior,
Reference/Optimized equality on shared traces, leapfrog properties, callback
validation, and seeded normal-target moments. Shared quality helpers are used
where the target has stable analytical diagnostics. These tests are empirical
runtime evidence, not an invariance or convergence proof.

## 7. Current completion boundary

- [x] Mathematical kernel validity and invariance are proved.
- [x] Scalar integrator correspondence is proved.
- [x] Ideal deterministic trace replay is proved.
- [x] Artifact, Reference, public, and Optimized paths are maintained and tested.
- [x] Exact-real versus Julia runtime assumptions are explicit.
- [ ] One theorem connects the full stochastic command denotation to the
      refreshed/projected mathematical position kernel.

The unchecked item is a foundation-composition task for an existing sampler;
it is not a request for a new sampler or a stronger convergence theorem.
