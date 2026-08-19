# Sampler development record

Copy this record into a design issue or sampler-specific document when adding
an algorithm. It is an obligation ledger, not a requirement to force the
mathematics through the current executable IR.

## 1. Mathematical identity

- **Sampler name:**
- **State space:**
- **Target measure:**
- **Transition or output law:**
- **Auxiliary state:**
- **Assumptions:** normalization, positivity, measurability, support, or
  integrability conditions.
- **Claim level:** kernel validity, reversibility, invariance, convergence, or
  a quantitative bound. List each separately.

Record the intended reusable Lean module and the example that will instantiate
it. Essential arguments belong under `formal/Mcmc/`, not only in an example.

## 2. Formal evidence

| Obligation | Lean declaration | Status |
|---|---|---|
| Mathematical transition |  |  |
| Markov-kernel or probability-law validity |  |  |
| Target invariance |  |  |
| Reversibility, if claimed |  |  |
| Convergence and its mode, if claimed |  |  |
| Concrete example |  |  |

Do not promote stationarity to convergence. If an obligation is intentionally
out of scope, state why rather than weakening the theorem silently.

## 3. Executable presentation

- **One-step inputs and outputs:**
- **Ordered random events:**
- **Callbacks:**
- **Bounded loops or failure behavior:**
- **Exact-real semantics:**
- **Numerical/platform assumptions:**

Choose one lowering route:

1. existing core IR;
2. a reusable core-IR extension;
3. a typed sub-IR; or
4. a certified primitive with explicit obligations.

Explain the choice. A missing IR feature does not block the preceding Lean
definition or proof.

## 4. Refinement boundary

State the strongest bridge actually supplied:

- kernel or output-law equality;
- deterministic replay equality for every valid trace;
- conditional refinement from a callback or solver certificate; or
- a documented boundary with no current execution theorem.

Track artifact round-trip, Julia-parser behavior, floating-point arithmetic,
callbacks, and RNG semantics separately. Evidence for one is not evidence for
the others.

## 5. Maintained Julia paths

| Layer | Declaration or file | Evidence |
|---|---|---|
| Canonical artifact |  | regeneration check |
| Reference interpreter |  | trace/conformance test |
| Public sampler |  | seeded API test |
| Optimized implementation |  | differential test and benchmark motivation |

Optimization is optional. When it is added, record whether the contract is
pathwise trace equality, exact arithmetic equality, bounded numerical
refinement, or equality of an ideal output law.

## 6. Diagnostics

Select diagnostics according to the sampler and target:

- deterministic trace replay and malformed-input rejection;
- integrator properties;
- known moments or covariance;
- marginal quantiles or ECDF error;
- ESS and Monte Carlo uncertainty;
- multiple-chain diagnostics; and
- throughput and callback work.

Integrated tests own small deterministic or statistically calibrated
regressions. The benchmark may reuse the same diagnostic functions for richer
reports. Neither is a replacement for the Lean theorem.

## 7. Completion evidence

- [ ] Public Lean module exported through `formal/Mcmc.lean`.
- [ ] Exact assumptions and theorem strength documented.
- [ ] Executable/refinement boundary recorded.
- [ ] Reference and public Julia paths tested, if executable.
- [ ] Optimized path justified and compared, if present.
- [ ] `make test` passes.
- [ ] `make check-docs-generated` passes.
- [ ] `julia --project=docs docs/make.jl` passes.
- [ ] `git diff --check` passes.
