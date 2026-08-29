# Transport and likelihood-informed HMC

This note separates two related ways to amortize geometric information.  The
random-sketch RMHMC study remains a baseline for the value of a fixed budget of
local curvature-vector products; it is not assumed to be the final sampler.

## Transport HMC: first implementation

Let `q = T(z)` be a fixed differentiable bijection.  HMC targets

```text
log pi_z(z) = log pi_q(T(z)) + log |det J_T(z)|
```

in latent coordinates and maps retained states back through `T`.  A poor map
reduces efficiency but does not change the exact transformed target.  An
incorrect inverse, pullback, or Jacobian callback does invalidate the runtime
algorithm and is therefore an explicit refinement boundary.

The first repository implementation accepts:

- `forward(z)` and `inverse(q)`;
- the Jacobian-transpose action `pullback(z, v)`;
- `logabsdetjac(z)` and its gradient; and
- the original negative-log-density gradient.

It runs the existing IR-backed vector endpoint HMC in latent coordinates.
Lean proves the measure-level conjugation theorem and a multinomial-HMC client:
if the latent Boltzmann measure equals the target pushforward, the transported
kernel preserves the original target.  Proving the concrete analytic
change-of-variables identity and refining callback arithmetic remain separate
obligations.

The next structured candidate is a full-dimensional map that is nonlinear
only on a rank-`r` active subspace, leaving the complement affine.  Its intended
cost is `O(d r + r^3)` rather than a general dense Jacobian factorization.

## Likelihood-informed/subspace MCMC: second implementation

A likelihood-informed method learns a basis `U` for directions in which the
likelihood changes the reference measure substantially.  It then applies an
informed transition on `span(U)` and a reference-aware transition on the
complement.  Unlike transport HMC, this does not by itself straighten nonlinear
geometry; it partitions where computational effort is spent.

The fixed-basis executable milestone implements:

```text
active coordinates       conditional endpoint HMC
Gaussian complement      pCN proposal + likelihood-only MH correction
```

for targets proportional to `likelihood(q) * N(q; 0, I)`. The active basis is
orthonormal and frozen. Lean currently proves the common-target composition
theorem; concrete conditional-HMC and pCN invariance clients remain the next
formal obligations.

The remaining repository sequence is:

1. prove concrete conditional active-HMC and pCN component invariance;
2. add a typed composition descriptor over the existing HMC IR;
3. obtain `U` during warmup from accumulated fixed-probe curvature sketches;
4. freeze `U` before retained sampling; and
5. combine a nonlinear active-subspace transport with the exact complement
   kernel only after both simpler clients are validated.

Warmup learning is not part of the stationary transition.  Continual online
updates would require an adaptive-MCMC theorem and are deliberately deferred.

## Relationship to existing work

- Parno and Marzouk construct adaptive transport maps with exact MH-corrected
  sampling.
- NeuTra HMC learns a neural transport and runs HMC in warped coordinates.
- DILI MCMC uses a likelihood-informed subspace relative to a Gaussian
  reference measure.
- Randomized range finding and Hessian-vector products provide candidate
  estimators for the active subspace.

The prospective contribution is not transport or low-rank Hessian sensing in
isolation.  The project-specific question is whether a small, auditable map
learned from the same curvature-probe budget can dominate repeatedly sensed
RMHMC in effective samples per target/gradient pass while retaining an
end-to-end verified reference transition.

## Initial hard-geometry benchmark

The four-chain, 2,000-draw study with 1,000 burn-in transitions now includes
both fixed methods. The exact known warp is deliberately an oracle transport,
not a learned-map result.

| Method | Selected step | Tail ESS/transition | Tail ESS/s | Rank-normalized Rhat |
|---|---:|---:|---:|---:|
| Exact-map Transport HMC | 0.2 | 0.5555 | 107,043 | 1.005 |
| Rank-one likelihood-informed HMC | 0.1 | 0.2931 | 26,291 | 1.107 |
| Full RMHMC | 0.04 | 0.1737 | 200 | 1.011 |
| Rank-one sketch RMHMC | 0.005 | 0.1903 | 29.7 | 1.006 |

The transport result confirms the value of amortizing a successful nonlinear
geometry correction. The likelihood-informed result is not converged and
should not be read as a valid ESS/s comparison; it also illustrates that a
linear active subspace is not equivalent to straightening the warp.

### Dimension-16 transport confirmation

The exact known rotated warp was also run alone at dimension 16 with the same
four chains, 2,000 draws, and 1,000 burn-in transitions:

| Dimension | Step | Steps | Bulk ESS/transition | Tail ESS/transition | Tail ESS/s | Rhat |
|---:|---:|---:|---:|---:|---:|---:|
| 16 | 0.1 | 10 | 0.27864 | 0.48365 | 12,473.90 | 1.005 |
| 16 | 0.2 | 5 | 0.28360 | 0.51131 | 33,311.25 | 1.005 |
| 16 | 0.4 | 2 | 0.17708 | 0.34503 | 46,643.66 | 1.010 |

This isolates fixed-map execution scaling and is not a learned-transport
comparison. Transport HMC does not require a map that exactly Gaussianizes the
target: any fixed invertible map still defines the exact Jacobian-correct
transformed target. The oracle label means only that this experiment supplies
the analytically perfect map and excludes its discovery cost.

### Moment-fitted rank-one quadratic candidate

The first learned-map prototype is a triangular, full-dimensional transport.
From column-oriented warmup samples it:

1. takes the leading covariance direction as the nonlinear output direction;
2. finds the input direction from an output-weighted second-moment matrix;
3. fits the output coordinate on `1`, the input coordinate, and its square by
   a three-parameter ridge least-squares solve; and
4. uses the residual standard deviation for the remaining triangular scale.

The inverse, Jacobian-transpose action, and constant log determinant are
analytic. At dimension 16, fitting 5,000 already available samples takes about
`3.3 ms` on the recorded machine. The controlled benchmark uses independent
target samples, so it tests representation and fixed-map execution but not the
cost or reliability of acquiring training samples from a weak warmup chain.

| Map | Step | Steps | Bulk ESS/transition | Tail ESS/transition | Tail ESS/s | Rhat |
|---|---:|---:|---:|---:|---:|---:|
| Analytic oracle | 0.2 | 5 | 0.28360 | 0.51131 | 33,291 | 1.005 |
| Moment-fitted quadratic | 0.1 | 10 | 0.27841 | 0.47820 | 5,172 | 1.005 |
| Moment-fitted quadratic | 0.2 | 5 | 0.28486 | 0.50510 | 13,209 | 1.004 |
| Moment-fitted quadratic | 0.4 | 2 | 0.17642 | 0.34917 | 27,894 | 1.008 |
| HMC-warmup-fitted quadratic | 0.2 | 5 | 0.19372 | 0.44423 | 7,878 | 1.010 |

The fitted map recovers nearly all of the oracle's transition efficiency in
this controlled representation test. Its lower throughput is an implementation
issue—the current callback path creates temporary vectors—and is a suitable
future Optimized-path target.

The practical comparison gives every method its own four independent chains.
Each chain runs exactly 1,000 ordinary-HMC transitions (`ε=0.01`, 50 steps)
and then continues from its own endpoint and RNG state after switching to the
method being evaluated. The fitted branch pools its own 4,000 warmup states,
fits one map, and freezes it before continuation. Thus every method pays the
same ordinary-HMC transition budget without sharing realized chains; only the
fitted branch additionally pays the `0.0060 s` fit cost.

| Paired continuation | Step | Steps | Tail ESS/transition | Rhat | End-to-end tail ESS/s |
|---|---:|---:|---:|---:|---:|
| Ordinary HMC | 0.01 | 50 | 0.15425 | 1.046 | 544 |
| Analytic transport ceiling | 0.1 | 10 | 0.45951 | 1.006 | 4,494 |
| Warmup-fitted transport | 0.1 | 10 | 0.38191 | 1.008 | 2,299 |

End-to-end rates include each method's independently timed acquisition and
continuation; the fitted row also includes fitting. The fit's hidden
input/output direction alignments are `0.832/0.981`.
