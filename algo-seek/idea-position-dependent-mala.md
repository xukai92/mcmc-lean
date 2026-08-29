# Position-dependent MALA with sensed local geometry

This note records the Langevin branch of the statistically sensed curvature
project. Its immediate purpose is to obtain local position-dependent geometry
without RMHMC's implicit generalized-leapfrog solve. It is an implementation
and formalization plan, not a novelty claim.

## Algorithm choice and measure convention

Let `π(q)` be a density with respect to ordinary Lebesgue measure, let
`G(q)` be a smooth positive-definite metric, and write `A(q)=G(q)⁻¹`. The
primary algorithm is the position-dependent MALA (PMALA) diffusion of Xifara
et al. Its Euler proposal with proposal standard deviation `ε` is

```text
q' ~ Normal(μ(q), ε² A(q))

μ_i(q) = q_i + ε²/2 *
  (sum_j A_ij(q) * ∂_j log π(q) + sum_j ∂_j A_ij(q)).
```

The second sum is the row divergence of the inverse metric. Equivalently, if
metric derivatives are available,

```text
∂_j A(q) = -A(q) * (∂_j G(q)) * A(q).
```

The proposal is accepted with the complete asymmetric Gaussian Hastings
ratio. Metropolis correction makes any correctly evaluated normalized
proposal target-exact; the divergence term is nevertheless important because
it makes the underlying diffusion preserve `π` with respect to Lebesgue
measure rather than merely defining an arbitrary local Gaussian proposal.

This convention follows the clarification by
[Xifara et al.](https://arxiv.org/abs/1309.2983). They identify a missing
factor of one half and a reference-measure mismatch in the diffusion printed
for the original full MMALA construction. The
[Girolami--Calderhead paper](https://doi.org/10.1111/j.1467-9868.2010.00765.x)
remains the source for the geometric proposal and RMHMC programme, but its
formula must not be copied without recording whether the target density is
with respect to Lebesgue or Riemannian volume.

The simplified manifold proposal

```text
μ(q) = q + ε²/2 * A(q) ∇logπ(q)
```

is retained as a labelled control. With the full forward/reverse Gaussian
ratio it is still a correct MH sampler for `π`; it is not, in general, the
Euler discretization of the desired Lebesgue-invariant diffusion.

## Relationship to the curvature-sketch project

The first metric clients reuse the RMHMC study:

1. full pullback/GGN metric `G(q)`;
2. fixed-probe ridge-plus-rank-`M` metric
   `G_M(q)=λI+U_M(q)U_M(q)ᵀ`; and
3. Euclidean MALA as `G(q)=I`.

For the sketch metric, Woodbury and determinant-lemma algebra provide
`A(q)`, Gaussian sampling, and log determinant without dense factorization.
The divergence still requires derivatives of the same represented inverse
metric. Fixed probes remain algorithm parameters; refreshing probes inside a
proposal would change the kernel and needs an auxiliary-state construction.

## Expected computational trade-off

PMALA performs one local proposal rather than an `L`-step implicitly solved
trajectory. For a dense metric it still pays metric construction,
factorization, log determinant, and divergence costs at both proposal
endpoints. For a rank-`M` metric, the intended characteristic cost is

```text
O(M C_v + M C_dv + d M² + M³)
```

per endpoint, compared with the same structured metric work repeated across
`L K` generalized-leapfrog evaluations in sketch RMHMC. PMALA should therefore
be much cheaper per transition but more diffusive; the empirical question is
whether its local geometric scaling produces more effective samples per
second.

## Implementation ladder

### Phase 1: mathematical foundation

Status: complete at the conditional dense-density boundary.

- Define inverse-metric action, inverse-metric divergence, the corrected
  PMALA drift, and the simplified control.
- Package a measurable normalized position-dependent proposal density.
- Obtain Markov, reversibility, and invariance from general density MH.
- Keep Gaussian normalization and the Lebesgue reference measure explicit.

### Phase 2: dense executable client

Status: complete. Artifact version 25 exposes `dense_pmala_step!`; Julia has
Reference and generic Optimized paths plus public `DensePMALA` dispatch.

- Implement a dense PMALA transition using `G`, `∂G`, a factorization, and the
  complete Gaussian log density.
- Add deterministic Reference/Optimized replay and finite-value/dimension
  failures.
- Verify that the identity metric reduces to ordinary MALA.

### Phase 3: structured sketch client

- Implement inverse action, sampling, log determinant, and divergence using
  the ridge-plus-low-rank representation.
- Differentially compare it with a materialized dense version of the exact
  same metric.
- Add the method to the hard-geometry and dimension studies.

### Phase 4: formal executable refinement

- Lower reusable matrix/factor/divergence operations into typed IR or a
  focused certified primitive.
- Prove the ideal command law is the normalized Gaussian proposal used by the
  mathematical PMALA kernel.
- Keep Float64 factorization, callbacks, RNG, and `libm` outside the exact-real
  claim unless separately refined.

## Evaluation protocol

Compare Euclidean MALA, dense PMALA, sketch PMALA, HMC, dense RMHMC, and sketch
RMHMC on the same latent-diagnostic targets. Report at least split
rank-normalized `Rhat`, bulk/tail ESS per transition and per second, latent
jump distance, metric/divergence evaluations, and numerical failures. ESS/s
from chains with poor between-chain agreement is not treated as successful
sampling evidence.

The Euclidean MALA baseline confirmed the need for the dense phase: on
the two-dimensional warped target its best tested row has `Rhat=1.362`, while
dense and sketch RMHMC have `Rhat=1.011` and `1.006`. The next experiment asks
whether position-dependent Langevin scaling closes some of that exploration
gap without paying for an implicit trajectory. The first dense PMALA run
selected `ε=1.0`, tail ESS/transition `0.1912`, and `Rhat=1.050`. This nearly
matches the Riemannian rows per transition at far lower runtime, but the
between-chain diagnostic is still borderline and the nominal ESS/s is not yet
treated as stable evidence.
