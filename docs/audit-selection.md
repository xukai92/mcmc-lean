# Audit selection protocol

Search date: 2026-09-23.

## Inclusion criteria

General-purpose MCMC/HMC methods published 2020–2025 with a checkable
correctness or validity claim: invariance, reversibility, measure or volume
preservation, an acceptance or correction term, or an exactness or equivalence
claim. Preference for independent (non-author) works to broaden the ledger
beyond the existing Xu et al. audits.

## Search scope

Venues searched: NeurIPS, ICML, AISTATS, ICLR, JRSS-B, Biometrika, JMLR,
Annals of Statistics, Bernoulli, arXiv (stat.CO, stat.ML, cs.LG).

Query terms: "Hamiltonian Monte Carlo" + {correction, invariance, detailed
balance, volume preservation, measure preservation, reversibility, acceptance,
reflection, refraction, discontinuous, mixed, parallel, equivalence}.

## Selected candidates

### 1. Mixed HMC (PRIORITY)
- **Paper**: Zhou, "Mixed Hamiltonian Monte Carlo for Mixed Discrete and
  Continuous Variables," NeurIPS 2020.
  [Proceedings](https://papers.neurips.cc/paper_files/paper/2020/file/c6a01432c8138d46ba39957a8250e027-Paper.pdf);
  [arXiv:1909.04852](https://arxiv.org/abs/1909.04852);
  [Code](https://github.com/StannisZhou/mixed_hmc).
- **Reason**: Known MH correction error in proceedings version (acknowledged
  by the author in the code repository). The corrected version is on arXiv.
  This is a clean audit target: formalize the correction, classify the
  proceedings claim as corrected, verify the fix.
- **Auditable claims**: MH correction term for the mixed discrete/continuous
  transition; detailed balance of the corrected kernel.

### 2. Discontinuous HMC
- **Paper**: Nishimura, Dunson & Lu, "Discontinuous Hamiltonian Monte Carlo
  for discrete parameters and discontinuous likelihoods," Biometrika
  107(2):365-380, 2020.
  [DOI:10.1093/biomet/asz083](https://doi.org/10.1093/biomet/asz083);
  [arXiv:1705.08510](https://arxiv.org/abs/1705.08510);
  [Code](https://github.com/aki-nishimura/discontinuous-hmc).
- **Reason**: The reflection/refraction integrator's exact Hamiltonian
  preservation is a non-trivial correctness claim. The repository already has
  partial infrastructure (`Hamiltonian/Discontinuous.lean`,
  `Hamiltonian/DiscontinuousMetropolis.lean`).
- **Auditable claims**: Exact energy preservation of the coordinatewise
  crossing/reflection update; volume preservation of the integrator; target
  invariance of the discontinuous HMC kernel.

### 3. Parallelizing MCMC Across Sequence Length
- **Paper**: Zoltowski, Wu, Gonzalez, Kozachkov & Linderman, NeurIPS 2025.
  [arXiv:2508.18413](https://arxiv.org/abs/2508.18413).
- **Reason**: The auditable claim is a deterministic equivalence: the parallel
  Newton fixed-point evaluation yields exactly the sequential chain. This is a
  refinement/determinism claim similar to the IR replay contract.
- **Auditable claims**: Equivalence of parallel Newton evaluation to sequential
  chain; convergence-rate claims (out-of-scope).

## Examined and excluded

### NUTS termination correctness
- **Paper**: Hoffman & Gelman, "The No-U-Turn Sampler," JMLR 2014.
- **Reason excluded**: Published before 2020, outside the time window.
  The repository already has extensive NUTS formalization.

### Reflective/Refractive HMC (Afshar & Domke 2015)
- **Reason excluded**: Published before 2020. Nishimura et al. 2020 extends
  this work and is within the window.

### Generalized Randomized HMC for piecewise smooth targets (2025)
- **Paper**: arXiv:2504.18210.
- **Reason excluded**: Extends Nishimura et al.; auditing the base paper first
  is more valuable. Could be a follow-on audit.

### Involutive MCMC (Neklyudov et al., ICML 2020)
- **Reason examined**: General framework for constructing valid MCMC via
  involutions. Interesting but very abstract — the auditable claim is the
  general framework, not a specific sampler. Lower priority than the concrete
  targets above.
