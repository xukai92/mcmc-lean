# Multi-marginal transport HMC: novelty audit

Evidence-seeking novelty audit of the `multiMarginalTransportHMC` construction
and its marginal-correctness theorem.

- Reviewed commit: `05dbaee` (main HEAD). The three core files
  (`MultiMarginalTransportHMC.lean`, `MultiMarginalCompilerIR.lean`,
  `CoupledMultinomialHMC.lean`) and `related-work.md` / `ir-refinement-status.md`
  are byte-identical between `e8e0e19` (the commit named in the audit request)
  and `05dbaee` (`git diff --stat e8e0e19 05dbaee` on those paths is empty), so
  this review faithfully covers `e8e0e19`.
- Audit date: 2026-09-24.
- Scope: the Lean construction and marginal theorem, the IR refinement, the
  Julia reference/optimized/evaluation paths, and the primary coupling
  literature.

## Bottom line

The prior hypothesis is **confirmed**, and more sharply than stated.

1. `multiMarginalTransportHMC` is a **K-chain generalization of the
   shared-momentum coupling** whose only inter-chain dependence is a single
   common momentum draw. Trajectory selection is **coordinatewise independent**
   (`independentTrajectoryK`, which is `withinTemp (fun _ => single-chain
   randomizedMultinomialLeapfrogKernel)`). The module docstring states this
   verbatim.
2. **"Transport" is a misnomer for this construction.** It contains no transport
   coupling, no optimal-transport index coupling, no transport cost, and no use
   of the generic index-coupling interface. The genuine transport machinery
   (Xu 2021's optimal-transport and maximal index couplings) already exists in
   the repository at K=2 inside `CoupledMultinomialHMC.lean`
   (`transportTrajectoryIndexCoupling`, `maximalTrajectoryIndexCoupling`,
   `transportSharedMomentumCoupledPositionMultinomialHMC`). The K-chain module
   uses none of it.
3. The construction is in fact a **weaker** coupling than Xu 2021's own
   independent baseline. Xu 2021's `independentTrajectoryIndexCoupling`
   (K=2) shares the trajectory **origin** as well as the momentum; the K-chain
   `multiMarginalTransportHMC` shares **only the momentum** (each chain runs the
   full single-chain `positionMultinomialHMC`, which independently averages over
   its own uniform origin and draws its own trajectory index).
4. The defensible contributions are: (a) a **finite-K extension** of a
   two-chain marginal-correctness statement to a common-random-number coupling;
   (b) a **machine-checked formalization** of that extension; and (c) a small,
   genuinely **reusable coordinate-marginal lemma** for the ParallelTempering
   `withinTemp` combinator. None of these require — and the code does not claim —
   a novel coupling mechanism, a new proof technique, product-target invariance,
   coalescence, convergence, or variance reduction.

The current manuscript framing (`paper/main.tex` §"Multi-marginal transport
HMC", lines ~977–1010) already describes the mechanism correctly and explicitly
declines to claim product invariance. The one residual issue is the **name**,
and an author to-do `% K: check if the multi-transport HMC is a novel proof`
(main.tex:262). This audit answers that to-do: the proof is not novel as a
technique; it is a competent finite-K formalization.

## What the construction actually is (ordinary math)

State: `K` positions `x : Fin K → Position ι`.

One transition of `multiMarginalTransportHMC`
(`formal/Mcmc/Hamiltonian/MultiMarginalTransportHMC.lean:283`):

1. `sharedMomentumLiftK`: draw **one** momentum `p ~ momentumTarget` and copy it
   into all K coordinates (`diagonalMomentumMeasureK`), producing K phase points
   `(x k, p)`.
2. `independentTrajectoryK`: apply the single-chain randomized multinomial
   leapfrog kernel **independently** to each of the K phase coordinates via
   `withinTemp (fun _ => randomizedMultinomialLeapfrogKernel …)`. Conditional on
   the shared `p`, the K chains are independent: each independently samples its
   own uniform trajectory origin and its own Boltzmann trajectory index.
3. `positionProjectK`: discard momenta, keep the K positions.

The only coupling is step 1 (a common random number on the momentum draw). This
is a classic shared-randomness / CRN coupling.

### (a) sampler construction
Shared-momentum, conditionally-independent-selection K-chain coupling of
multinomial HMC. No transport, no maximal coupling, no coalescence objective,
no cross-chain matching.

### (b) marginal-correctness property
`multiMarginalTransportHMC_marginal`
(`MultiMarginalTransportHMC.lean:369`): for each coordinate `k`, the pushforward
of the joint output law under `Function.eval k` equals the single-chain
`positionMultinomialHMC` applied to `x k`. The design note states — correctly —
that **product invariance does not hold**; this is a coupling (correct
marginals, correlated joint), not a product-invariant kernel.

### (c) proof technique
Coordinate projection / pushforward algebra on product kernels. Chain of
`Measure.map`/`map_map`/`comp` rewrites: the k-th marginal of the shared lift is
the single-chain lift (`sharedMomentumLiftK_map_eval`); the k-th marginal of the
independent trajectory step is the single-chain step (`comp_sharedLift_map_eval`
via `withinTemp_map_eval`); composition and the final position projection give
the result. This is the standard argument that a CRN coupling preserves
marginals. Not a new technique.

### (d) reusable general lemmas
- `withinTemp_map_eval` (line 245): the k-th marginal of
  `withinTemp (fun _ => κ)` equals `κ (x k)` — i.e. sequential coordinatewise
  application of the ParallelTempering `liftCoord` combinator has
  independent-coordinate marginals, regardless of application order.
- The `liftCoord` marginal toolkit: `liftCoord_map_eval`,
  `liftCoord_map_eval_ne`, `comp_map_eval_of_dirac`, `comp_liftCoord_map_eval`,
  `foldr_liftCoord_map_eval` (nodup list of coordinates).

These have modest independent value: they are the general fact that a
`withinTemp` scan over distinct coordinates acts marginally as the per-coordinate
kernel, useful for any product/parallel-kernel marginal reasoning (e.g.
within-temperature moves in parallel tempering). They are not mathematically
deep.

### (e) machine-checked formalization
The kernel, its `IsMarkovKernel` instance, the marginal theorem, a K=2 example
(`Examples/MultiMarginalTransportK2.lean`), and an IR refinement
(`multiMarginalTransportHmcProgramKernel_refines`, `rfl`) plus marginal corollary
are all compiled as part of the library.

## Cross-layer consistency check

The mechanism is described identically across the three layers, and none of them
implement a transport coupling:

- **Lean**: `independentTrajectoryK` = coordinatewise independent selection with
  a shared momentum lift.
- **IR** (`Reference/Samplers.ir`, program `multi_marginal_transport_hmc_step!`;
  `MultiMarginalCompilerIR.lean`): a single opaque `multi-marginal-transport-hmc`
  primitive; the refinement theorem is `rfl` against `multiMarginalTransportHMC`.
- **Julia** (`Reference/Reference.jl:711`, `Optimized/Optimized.jl:1631`,
  `Evaluation/MultiMarginalEval.jl`): the eval module's own docstring reads
  "Compare K coupled chains (shared momentum) vs K independent chains", and the
  gradient-evaluation counts are equal for both arms
  (`grads_per_coupled_step == grads_per_independent_step == K*(L+1)`), i.e. the
  shared momentum yields no compute saving.

## Comparison table

| # | Our claim (+ Lean decl) | Closest primary source | Key differences | Verdict | Evidence |
|---|---|---|---|---|---|
| 1 | K-chain shared-momentum, independent-selection coupling of multinomial HMC (`multiMarginalTransportHMC`) | Xu et al. 2021 `independentTrajectoryIndexCoupling` (K=2 baseline); classic common-random-number couplings | Ours generalizes K=2→K and shares *only* momentum (Xu's baseline also shares the origin), so it is strictly weaker. No new mechanism. | **Extension** (of the CRN/independent baseline) | `MultiMarginalTransportHMC.lean:259,283`; `CoupledMultinomialHMC.lean:746–831`; single-chain origin averaging `HMC.lean:225,258` |
| 2 | "Transport" coupling | Xu et al. 2021 optimal-transport multinomial index coupling; formalized at K=2 as `transportTrajectoryIndexCoupling` / `transportSharedMomentumCoupledPositionMultinomialHMC` | Ours contains **no** transport coupling; the name is borrowed. Genuine transport already exists in-repo at K=2. | **Established prior art**; name is a **misnomer** for this module | Xu 2021 abstract ("based on optimal transport"); `CoupledMultinomialHMC.lean:1256–1313, 1556–1633` |
| 3 | "Multi-marginal" (K-chain) coupling | Phan, Flamich, Khisti, Asoodeh 2026, "Multi-Marginal Couplings for Metropolis-Hastings" (arXiv 2605.12807) | That work is a genuine many-chain coalescence coupling (shared-randomness Poisson MC, list-level/matching objective, "no canonical notion of agreement" for >2 marginals). Ours has no coalescence objective; "multi-marginal" here only means "K correct marginals." | **Prior art exists** for genuine multi-marginal couplings; ours is not one | Phan et al. 2026 abstract; our `multiMarginalTransportHMC_marginal` |
| 4 | Marginal-correctness theorem (`multiMarginalTransportHMC_marginal`) | Xu 2021 two-chain marginal correctness; standard "CRN couplings preserve marginals"; in-repo `coupledPhaseMultinomialHMC_isCoupling` etc. | Extends a two-chain marginal statement to finite K; trivial-by-construction for a CRN coupling. | **Extension + formalization contribution** | `MultiMarginalTransportHMC.lean:369`; `CoupledMultinomialHMC.lean` coupling theorems |
| 5 | Proof technique / reusable lemmas (`withinTemp_map_eval`, `liftCoord_*`, `foldr_liftCoord_map_eval`) | General product/parallel-kernel marginalization; mathlib `Measure.map`/`comp` algebra | Standard pushforward algebra; the reusable content is a clean marginal law for the `withinTemp` scan. | **Formalization contribution** (modest, reusable); **not** a new technique | `MultiMarginalTransportHMC.lean:122–252` |
| 6 | First machine-checked coupled multinomial-HMC kernel with proved marginals | No public Lean/Isabelle/Coq coupled-HMC or CRN-coupling-with-marginals formalization found | pRHL/EasyCrypt "coupling" is a relational proof technique, a different sense; no formalized coupled-MCMC *kernel* with proved marginals surfaced | **Potentially new (scoped, dated)** — and this applies most strongly to the K=2 transport work in `CoupledMultinomialHMC.lean`, not to the independent K-chain module | related-work search 2026-08-15; this audit's search 2026-09-24 (below) |

Distinction requested by the audit: item 4 is "extending a two-chain statement
to finite K", **not** "introducing a new proof technique" (item 5 is standard
algebra). The reusable lemmas (item 5) have value independent of any
mathematical novelty, but that value is infrastructural, not a research result.

## Primary sources

- Kai Xu, Tor Erlend Fjelde, Charles Sutton, Hong Ge, "Couplings for Multinomial
  Hamiltonian Monte Carlo", AISTATS 2021, PMLR 130:3646–3654. arXiv:2104.05134.
  <https://proceedings.mlr.press/v130/xu21i.html>. Confirmed: the coupling is
  "based on optimal transport for multinomial sampling", designed to minimize
  expected inter-chain distance to speed meeting; includes maximal coupling and a
  meeting-time bound via local contractivity. Two-chain (pairwise) setting.
  Reference implementation: CoupledHMC.jl (TuringLang/chalk-lab).
- Buu Phan, Gergely Flamich, Ashish Khisti, Shahab Asoodeh, "Multi-Marginal
  Couplings for Metropolis-Hastings", arXiv:2605.12807 (submitted 2026-05-12;
  verified to exist as titled via web search on 2026-09-24, not read in full).
  <https://arxiv.org/abs/2605.12807>. Genuine many-chain coupling:
  shared-randomness Poisson Monte Carlo, list-level coupling / distributed
  matching, adaptive point-process update scaling with the number of chains; notes
  that for >2 marginals there is "no canonical notion of agreement". This is the
  actual "multi-marginal coupling" literature; the project construction is not an
  instance of it.
- Radford Neal, "MCMC using Hamiltonian dynamics" (2011); Betancourt (2017) —
  background on multinomial HMC / auxiliary-variable HMC (already in
  related-work.md).

## Search scope, date, queries

Date: 2026-09-24 (US region web search). Complements the related-work.md survey
last updated 2026-08-15 (mathlib, Isabelle AFP, Rocq/MathComp, arXiv, GitHub).

Queries run in this audit:
- "Xu Fjelde Sutton Ge Couplings for Multinomial Hamiltonian Monte Carlo AISTATS
  2021 maximal transport coupling"
- "\"Multi-Marginal Couplings for Metropolis-Hastings\" MCMC paper"
- "formalization coupling Markov chain Monte Carlo Lean Isabelle Coq proof
  assistant common random numbers HMC marginal"

Negative-result qualification: as of these dated searches we did not find a
public, machine-checked coupled-HMC (or CRN-coupling-with-proved-marginals)
kernel in Lean, Isabelle/HOL (AFP), or Rocq/Coq. The only proof-assistant
"couplings" surfaced are relational-Hoare-logic couplings (pRHL/EasyCrypt),
a different notion. This is evidence of a gap in the surveyed public literature,
not proof of absence.

## Recommended manuscript paragraph

> Multi-marginal transport HMC is a K-chain coupling of multinomial HMC in which
> all chains share a single momentum draw and then select trajectories
> independently. We machine-check that it is a Markov kernel and that each
> coordinate marginal equals the verified single-chain multinomial HMC kernel
> (`multiMarginalTransportHMC_marginal`, with a K=2 instance), reusing a general
> marginal law for the coordinatewise `withinTemp` combinator. We use it as a
> development case for the harness, not as a performance or mathematical
> contribution: the inter-chain coupling is exactly the shared momentum (a
> common-random-number coupling), and we deliberately do not claim invariance of
> the independent product target — marginal correctness does not imply it. The
> "transport" label follows Xu et al. (2021), whose optimal-transport and maximal
> index couplings we formalize separately at the two-chain level; the K-chain
> construction here uses independent trajectory selection and contains no
> transport coupling.

Claims the evidence **supports**:
- Markov-kernel and coordinate-marginal correctness (machine-checked).
- Finite-K extension of a two-chain marginal statement.
- A reusable coordinate-marginal lemma for `withinTemp`.
- A scoped, dated "we are not aware of a prior machine-checked coupled multinomial
  HMC kernel with proved marginals" — best attached to the K=2 transport work.

Claims the evidence does **NOT** support (avoid these):
- "Novel coupling mechanism" — it is the independent/CRN baseline generalized to
  K, weaker than Xu 2021's own baseline.
- "Transport coupling" for this kernel — no transport is present; the name is a
  misnomer relative to the implemented mechanism.
- "Multi-marginal coupling" in the Phan et al. (2026) sense — no coalescence
  objective or cross-chain matching.
- "New proof technique" — standard pushforward/marginalization algebra.
- Product-target invariance, coalescence, convergence, or variance reduction —
  none follow from a coordinate-marginal theorem, and the code does not claim
  them.
- Unqualified "first formalization" — must be dated and scoped.

## Unresolved questions / items for discussion (not unilateral changes)

1. **Naming.** "Transport" is a misnomer for `multiMarginalTransportHMC`; the
   implemented mechanism is shared-momentum + independent selection. Options for
   the authors: rename (e.g. "multi-marginal shared-momentum HMC" or
   "K-chain CRN-coupled multinomial HMC"), or keep the name but state explicitly
   in the manuscript and the module docstring that "transport" refers to the Xu
   2021 lineage and that this specific kernel uses independent selection. The
   paper already partly does this (main.tex:1003); the Lean docstring and the
   sampler name do not. Flagged for discussion; no rename applied.
2. **"Multi-marginal" collision.** The term now names a distinct 2026 paper
   (Phan et al.) with a genuine many-chain coalescence coupling. Consider
   citing it and clarifying that "multi-marginal" here means only "K verified
   marginals", to avoid an implied relationship.
3. **Relation to the in-repo transport kernel.** Consider whether the finite-K
   generalization should instead (or additionally) be built on the existing
   generic `coupledOffsetMultinomialKernel` interface so that the transport and
   maximal index couplings could actually instantiate a K-chain kernel — which
   would make the "transport" name accurate. Currently the K-chain module does
   not use that interface at all.
4. **First-formalization scope.** The strongest defensible formalization claim
   attaches to the K=2 `CoupledMultinomialHMC.lean` transport/maximal work, not
   to the independent K-chain module. If the paper wants a formalization-novelty
   sentence, point it there.
