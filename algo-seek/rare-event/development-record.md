# Sampler development record: rare-event endpoint-conditioned path sampling

Status: pilot stage. No verified implementation or scientific claim.
See `decision-note.md` for literature comparison and candidate selection.

## 1. Mathematical identity

- **Sampler name:** Endpoint-conditioned path MH (Candidate 1),
  Conditional SMC for paths (Candidate 2).
- **State space:** Paths $X = (x_0, x_1, \ldots, x_L)$ in
  $(\mathbb{R}^2)^{L+1}$, with $x_0$ fixed at $(-1, 0)$.
- **Target measure:**
  $$
  \Pi(dX) = \frac{1}{Z}\,\rho(dx_0)\prod_{t=0}^{L-1}P_\delta(x_t,dx_{t+1})
  \cdot \mathbf{1}_E(X),
  \qquad E = \{x_0 \in A,\; x_L \in B\}
  $$
  where $P_\delta$ is the overdamped Euler transition kernel and
  $\rho = \delta_{(-1,0)}$.
- **Unnormalized path density** (w.r.t. Lebesgue on $x_1, \ldots, x_L$):
  $$
  \tilde\pi(X) = \prod_{t=0}^{L-1} p_\delta(x_{t+1} \mid x_t)
  \cdot \mathbf{1}_E(X)
  $$
  with Gaussian transition density
  $p_\delta(y \mid x) = \mathcal{N}(y;\, x - \delta\nabla V(x),\,
  (2\delta/\beta) I)$.
- **Transition or output law:**
  - Candidate 1: whole-path MH with Gaussian perturbation proposal and
    accepted-flow correction. One MH step per iteration.
  - Candidate 2: conditional SMC sweep with $N$ particles, systematic
    resampling at time $L$ with endpoint indicator weights.
  - Baseline: TPS one-way forward shooting (one MH step per iteration).
- **Auxiliary state:** None for Candidate 1 and baseline. Candidate 2 uses
  $N$ particle trajectories as auxiliary state (particle Gibbs construction).
- **Assumptions:**
  - $Z = \mathbb{P}(E) > 0$: the event has positive probability.
  - Gaussian transition density is well-defined and finite for all states.
  - Fixed initial condition $\rho = \delta_{(-1,0)}$ makes $x_0$ deterministic.
  - The discrete-time Euler dynamics defines the target; no continuous-time
    invariance claim is made.
- **Claim level:**
  - Candidate 1: kernel validity and reversibility (from hard-zero theorem).
    Stationarity follows. Convergence is not proved.
  - Candidate 2: empirical pilot only. Formal invariance is deferred.
  - Baseline: kernel validity follows from the standard TPS MH argument.

## 2. Formal evidence

| Obligation | Lean declaration | Status |
|---|---|---|
| Hard-zero accepted flow | `forwardDensityFlow_eq_zero_of_weight_eq_zero` | **Proved** |
| Hard-zero acceptance rejection | `densityAcceptance_eq_zero_of_weight_eq_zero` | **Proved** |
| Hard-zero symmetric flow (left) | `symmetricAcceptedFlow_eq_zero_of_weight_eq_zero_left` | **Proved** |
| Hard-zero symmetric flow (right) | `symmetricAcceptedFlow_eq_zero_of_weight_eq_zero_right` | **Proved** |
| Support-restricted MH reversibility | `densityMetropolisHastings_supportRestricted_isReversible` | **Proved** |
| Support-restricted MH stationarity | `densityMetropolisHastings_supportRestricted_invariant` | **Proved** |
| CSMC / particle Gibbs invariance | — | Deferred (8–12 weeks) |
| Path-space measure formalization | — | Deferred |
| Convergence | — | Out of scope |

All Lean proofs are in `formal/Mcmc/Kernel/SupportRestriction.lean`, exported
through `formal/Mcmc.lean`. No `sorry`, `admit`, or `axiom` used.

## 3. Executable presentation

Not applicable at pilot stage. The pilot uses standalone Julia scripts in
`exp/rare-event-paths/`, not the verified IR / Reference / Optimized pipeline.

When a candidate passes the go/no-go gate, the executable presentation will
follow the standard development guide:
- One-step inputs: current path, RNG state, dynamics parameters
- One-step outputs: new path (or retained current path), accept/reject flag
- Random events: Gaussian noise per time step, uniform for MH decision
- Callbacks: gradient evaluation ∇V
- Bounded iteration: path length L is fixed

## 4. Refinement boundary

No refinement bridge exists at pilot stage. The Lean theorem
(`SupportRestriction.lean`) is independent of the Julia pilot code.
The connection between the mathematical `densityMetropolisHastings` and
the pilot's `guided_mh_step!` is by construction only — they implement
the same algorithm, but there is no formal linking theorem.

## 5. Maintained Julia paths

Not applicable at pilot stage. Pilot code is in `exp/rare-event-paths/`.

| Layer | Declaration or file | Evidence |
|---|---|---|
| Exploratory pilot | `exp/rare-event-paths/` | Diagnostic output |

## 6. Diagnostics

| Diagnostic | Implementation | Purpose |
|---|---|---|
| Channel probability (batch means + SE) | `diagnostics.jl` | Primary observable |
| Symmetry check (ε = 0) | Pilot protocol | Validation |
| Channel-switching count | `diagnostics.jl` | Mixing indicator |
| ESS (first-order autocorrelation) | `diagnostics.jl` | Efficiency metric |
| Acceptance rate | Per-method tracking | Method comparison |
| Force evaluations | Per-method counting | Cost metric |

## 7. Completion evidence

- [x] Hard-zero theorem in Lean, exported through `formal/Mcmc.lean`
- [x] Exact assumptions and theorem strength documented (reversibility, not convergence)
- [ ] Executable/refinement boundary recorded (deferred to post-pilot)
- [ ] Reference and public Julia paths tested (N/A at pilot stage)
- [ ] Optimized path justified and compared (N/A)
- [x] Pilot code runnable: `julia --project=exp/rare-event-paths exp/rare-event-paths/run_pilot.jl`
- [ ] `make test` passes (pending build)
- [ ] `git diff --check` passes (pending)
