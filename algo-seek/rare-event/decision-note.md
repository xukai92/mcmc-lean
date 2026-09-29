# Decision note: rare-event path sampling

Date: 2026-09-29.
Status: pilot in progress; no experimental claims made.

## Selected scientific question

**Channel-probability estimation for endpoint-conditioned overdamped
Langevin paths in a 2D double-well-with-bump potential.**

Given the fixed-horizon endpoint-conditioned path ensemble

$$
\Pi(dX) = \frac{\mathbf{1}_E(X)}{Z} \, \rho(dx_0) \prod_{t=0}^{L-1} P_\delta(x_t, dx_{t+1}),
\qquad E = \{X : x_0 \in A,\; x_L \in B\}
$$

with overdamped Euler–Maruyama dynamics

$$
x_{t+1} = x_t - \delta \nabla V(x_t) + \sqrt{2\delta/\beta}\,\xi_t, \qquad \xi_t \sim \mathcal{N}(0, I_2)
$$

and potential $V(q,r) = (q^2 - 1)^2 + r^2/2 + c \exp[-(q^2 + r^2)/s^2] + \varepsilon r$,
the diagnostic observable is

$$
P(\text{upper channel} \mid E) = \Pi\!\left(\{X : r_\tau > 0\}\right)
$$

where $\tau = \min\{t : q_t \geq 0\}$ is the first discrete crossing of $q = 0$.

For $\varepsilon = 0$, reflection symmetry in $r$ gives $P = 0.5$ (symmetry check).
For $\varepsilon \neq 0$, the channels have unequal weights.

## Literature comparison

### Dellago, Bolhuis, and Geissler (2002)
*Transition Path Sampling.* Adv. Chem. Phys. 123.

Established trajectory-space MCMC. Key mechanisms: shooting moves (one-way
and two-way), shifting moves. For stochastic dynamics with one-way forward
shooting, the MH acceptance ratio simplifies to the endpoint indicator
$\mathbf{1}_B(x'_L)$. This is our baseline.

Strengths: simple, exact, well-understood. Weakness: shooting from a random
interior point has low probability of reaching B in the hard regime.

### Jung et al. (2023)
*Machine-guided path sampling to discover mechanisms of molecular
self-organization.* Nature Comput. Sci.

Machine-learned shooting point selection and perturbation for TPS.
The learned guide accelerates sampling within TPS's shooting framework.
This is an existing ML-enhanced baseline family, not a new sampling
framework.

Relevant to us: a learned guide could serve as a proposal enhancement, but
the correctness argument (MH acceptance within TPS) is standard.

### Seong et al. (2024)
*Collective Variable Free Transition Path Sampling with Generative Flow
Network.* Preprint v1 (arXiv:2405.19961).

Uses GFlowNet to generate path proposals. The target is softened: the hard
endpoint indicator is replaced with a soft reward evaluated along the
trajectory. This changes the target distribution — the method does not
sample from our hard-conditioned ensemble without additional correction.

Out of scope for direct comparison on matched targets, but informative
about the difficulty of maintaining hard constraints in learned proposals.

### Plainer et al. (2024)
*Transition Path Sampling with Boltzmann Generator-based MCMC Moves.*
Revised preprint (arXiv:2312.05340v2).

Learned latent-space proposals with MH correction for trajectory sampling.
The normalizing-flow proposal maps from a simple latent space to path space;
the MH step corrects for the approximate density. This is the closest
existing work to our Candidate 1 (whole-path MH with evaluable proposal).

Key lesson: latent-space proposals can maintain reasonable acceptance at
moderate path lengths, but training cost must be amortized. Our Candidate 1
uses a simpler (non-learned) Gaussian proposal, which avoids training cost
but may have worse acceptance scaling.

### Häupl et al. (2026)
*An Always-Accepting Algorithm for Transition Path Sampling.*
Preprint v2 (arXiv:2602.13130).

Always-reactive proposals with reweighting for overdamped stochastic
dynamics. All proposed paths satisfy the endpoint condition by
construction, but samples are reweighted — the raw paths do not have the
target law. This is a weighted estimator, not an MCMC sampler in the
standard sense.

Relevant to us: the endpoint-hit rate is 100% by construction, but
estimator variance depends on weight stability. Must compare estimators
with weights and uncertainty, not just acceptance rates.

### Lichtinger and Covino (2026)
*Accelerated descriptor-free path sampling for protein–ligand binding
kinetics.* Preprint (arXiv:2607.15101).

Application-scale baseline for protein–ligand unbinding kinetics. Uses
enhanced TPS with descriptor-free shooting point selection. Demonstrates
the practical relevance of efficient path sampling for rate estimation
in molecular systems.

Relevant to us: provides context for what application-scale performance
looks like. Our pilot uses a diagnostic model; the molecular application
is gated on pilot success.

## Two candidate mechanisms

### Candidate 1: Guided whole-path MH

Propose a new path $Y$ by adding correlated Gaussian noise to the current
path $X$. The proposal density $Q(Y|X) = \prod_t \mathcal{N}(y_t; x_t, \sigma^2 I)$
is evaluable, so the full MH ratio can be computed:

$$
\alpha(X,Y) = 1 \wedge \frac{\tilde\pi(Y) Q(X|Y)}{\tilde\pi(X) Q(Y|X)}
$$

The accepted-flow formulation handles hard zeros: when $Y \notin E$,
$\tilde\pi(Y) = 0$, so $\text{symmetricAcceptedFlow}$ returns 0 and the
move is rejected.

**Expected weakness:** Acceptance decays roughly as $(\text{per-step rate})^L$.
At L=200, even 0.99 per step gives $0.99^{200} \approx 0.13$. The pilot
must measure this scaling.

**Proof obligation:** The hard-zero accepted-flow theorem (Stage 3) proves
that the existing `densityMetropolisHastings_isReversible` correctly
handles the indicator zeros.

### Candidate 2: Conditional SMC (particle Gibbs)

Run $N$ particles forward from $x_0$ using the transition kernel, with the
reference path forced to survive resampling. At time $L$, particles are
reweighted by $\mathbf{1}_B(x_L)$. A new path is selected from the
surviving particles.

**Expected strength:** Exploits the time-factorized structure of the path
target. With intermediate reweighting (guiding potential), can steer
particles toward the event before the final check.

**Expected weakness:** Basic version with only final-step reweighting is
essentially importance sampling with acceptance proportional to the fraction
of particles reaching B. Need many particles (N ≫ 1/P(B|x_0)) for adequate
mixing.

**Proof obligation:** Conditional SMC / particle Gibbs invariance for
continuous path measures. This is estimated at 8–12 weeks for
formalization and is deferred to after the pilot go/no-go gate.

## Explicit proof obligations

| Obligation | Status | Notes |
|---|---|---|
| Hard-zero accepted-flow theorem | **This cycle** | `SupportRestriction.lean`: `densityMetropolisHastings_supportRestricted_isReversible` |
| Detailed balance for whole-path MH with restricted target | Follows from above | Instantiation with path weight = density × indicator |
| CSMC / particle Gibbs invariance (continuous) | Deferred | 8–12 weeks; gated on pilot go/no-go |
| Path-space measure formalization | Deferred | Product measure over transition kernels |
| Convergence from arbitrary initial paths | Out of scope | Requires ergodicity analysis on restricted path space |

## Baseline

**TPS with one-way forward shooting** (Dellago 2002):
- Select shooting point τ uniformly from {1, ..., L−1}
- Keep x₀, ..., x_τ; forward-simulate x'_{τ+1}, ..., x'_L
- Accept if x'_L ∈ B (MH ratio simplifies to endpoint indicator)
- Not just rejection sampling: exploits previously-found reactive segments

## Pilot protocol

See `exp/rare-event-paths/pilot_protocol.jl` for frozen parameters.

### Accessible regime (β = 3)
- c = 3, s = 0.5: bump forces paths around the origin
- δ = 0.01: stable discretization
- L = 200: sufficient physical time for crossing
- ε = 0 (symmetry check) and ε = 0.3 (asymmetry test)
- 5000 iterations after 500 warmup, 2 seeds per regime

### Hard regime (β = 8)
- Same potential, lower temperature
- L = 500: longer paths needed
- ε = 0.3: asymmetric only (symmetry check done in accessible regime)
- 64 CSMC particles (vs 32 in accessible)

### Predeclared diagnostics
1. Channel probability P(upper) with batch-means SE
2. Channel-switching count (mixing indicator)
3. ESS for channel indicator (first-order autocorrelation)
4. Acceptance/hit rate per method
5. Total force evaluations (cost metric)

### Success criteria for pilot
- Accessible regime: all three methods recover symmetric P ≈ 0.5 at ε = 0
- Accessible regime: methods distinguish unequal channels at ε = 0.3
- Acceptance scaling: measure acceptance vs L for guided MH
- Channel mixing: ≥ 1 channel switch in accessible regime per seed
- Hard regime: at least one method produces meaningful estimates

## Missing domain resources

1. **Molecular dynamics simulator:** The diagnostic model uses explicit
   overdamped Euler dynamics. Application-scale molecular simulations need
   an MD engine (OpenMM, LAMMPS, or similar) with evaluable transition
   densities or appropriate likelihood ratios.

2. **Domain collaborator:** Protein–ligand unbinding requires domain expertise
   for system setup, force field selection, and validation against
   experimental kinetics data.

3. **Independent reference:** In the accessible regime, rejection sampling from
   x₀ provides an independent reference for channel probabilities. In the
   hard regime, no tractable independent reference is available; convergence
   diagnostics (multiple chains, R̂) must substitute.

4. **Learned guide potential:** Candidate 1 uses a fixed Gaussian proposal.
   A learned guide (e.g., approximate committor) could improve acceptance but
   requires training infrastructure and a separate correctness argument for
   the frozen-parameter case.

5. **Continuous-state CSMC theory:** Formal particle Gibbs invariance for
   continuous path spaces is not in the repository. This is needed before
   promoting Candidate 2 from empirical pilot to verified implementation.
