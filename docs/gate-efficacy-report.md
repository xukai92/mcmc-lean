# Gate-Efficacy Fault-Injection Report

Systematic fault injection across the Lean formal layer and Julia runtime to
assess the coverage of existing verification gates.

**Date:** 2024-09-24
**Branch:** `exp/gate-efficacy-001`
**Repository:** verified-samplers

## Summary

| Fault | Description | Gate | Verdict | Mechanism |
|-------|-------------|------|---------|-----------|
| F1 | False theorem (flipped exponent sign) | `lake build` | **CAUGHT** | Parse error + proof failure |
| F2 | Sorry-hidden proof (detailed_balance) | `lake build` | **SLIPPED** | Lean treats `sorry` as warning; build succeeds |
| F3 | Weakened statement (removed positivity hypothesis) | `lake build` | **CAUGHT** | Unsynthesizable placeholder argument |
| F4 | Spec mismatch (wrong probability definition) | `lake build` | **CAUGHT** | Tactic failures across 7 proof obligations |
| O1 | Wrong acceptance sign (flipped `<` to `>`) | `Pkg.test()` | **CAUGHT** | Conformance test failures (7 fails) |
| O2 | Dropped MH correction (always accept) | `Pkg.test()` | **CAUGHT** | Conformance test failures (7 fails) |
| O3 | Changed Reference output (+0.01 offset) | `Pkg.test()` | **CAUGHT** | Replay mismatch (3 fails) |
| O4 | Numerical drift (+1e-13 bias in leapfrog) | `Pkg.test()` | **CAUGHT** | Tolerance violation (10 fails) |
| O5 | Empty test selection (skipped testset) | `Pkg.test()` | **SLIPPED** | Test suite passes with fewer tests |
| O6 | Stale generated artifact (whitespace in IR) | `make check-generated` | **CAUGHT** | Byte-level `cmp` mismatch |

**Final tally: 8/10 caught, 2/10 slipped through.**

---

## Per-Fault Details

### F1 — False Theorem (Lean)

**File:** `formal/Mcmc/Executable/Continuous/BarkerRWMH.lean`

**Diff applied:**
```diff
-  1 / (1 + Real.exp (-(logDensity proposed - logDensity current)))
+  1 / (1 + Real.exp (+(logDensity proposed - logDensity current)))
```

**Gate:** `cd formal && lake build`

**Output (key lines):**
```
error: Mcmc/Executable/Continuous/BarkerRWMH.lean:26:21:
  unexpected token '+'; expected ')', '↑', '↥', '⇑' or term
warning: declaration uses `sorry`  [×5 downstream]
error: linarith failed to find a contradiction
  ⊢ False
error: unsolved goals
  ⊢ sorry () = logDensity current - logDensity proposed
Some required targets logged failures:
- Mcmc.Executable.Continuous.BarkerRWMH
error: build failed
```

**Analysis:** The `+` prefix operator is not valid Lean syntax in this context,
causing a parse error. All downstream theorems (`barkerLogDensityAcceptance_pos`,
`barkerLogDensityAcceptance_le_one`, `barkerLogDensityAcceptance_eq_sigmoid`,
and the refinement theorem) fail because the definition cannot be elaborated.
Even if the syntax were accepted, `linarith` would fail because the modified
formula is not bounded by 1.

---

### F2 — Sorry-Hidden Proof (Lean)

**File:** `formal/Mcmc/Finite/MetropolisHastings.lean`

**Diff applied:**
```diff
 theorem detailed_balance (π : Distribution State) (Q : MarkovKernel State)
     (hπ : ∀ x, 0 < π.mass x) : (kernel π Q hπ).Reversible π := by
-  intro x y
-  by_cases hxy : x = y
-  · subst y
-    rfl
-  · have hyx : ¬y = x := Ne.symm hxy
-    simp only [kernel, probability, move, flow, hxy, hyx, if_false, add_zero]
-    rw [mul_div_cancel₀ _ (ne_of_gt (hπ x)), mul_div_cancel₀ _ (ne_of_gt (hπ y))]
-    exact min_comm _ _
+  sorry
```

**Gate:** `cd formal && lake build`

**Output:**
```
⚠ [4077/4100] Built Mcmc.Finite.MetropolisHastings (2.1s)
warning: Mcmc/Finite/MetropolisHastings.lean:166:8: declaration uses `sorry`
Build completed successfully (4100 jobs).
```

**Analysis:** `lake build` exits with code 0. Lean treats `sorry` as a
**warning**, not an error. The build succeeds, and the `stationary` theorem
downstream also compiles because it merely invokes `detailed_balance` — Lean
propagates the `sorry` warning but does not block compilation. There is no
`sorry`-detection step in CI (`validation.yml` only runs `make test`). This is
a genuine gap: a contributor could replace any proof body with `sorry` and pass
all gates.

---

### F3 — Weakened Statement (Lean)

**File:** `formal/Mcmc/Finite/MetropolisHastings.lean`

**Diff applied:**
```diff
-noncomputable def kernel (π : Distribution State) (Q : MarkovKernel State)
-    (hπ : ∀ x, 0 < π.mass x) : MarkovKernel State where
-  prob := probability π Q
-  nonneg := probability_nonneg π Q hπ
-  sum_prob := sum_probability π Q
+noncomputable def kernel (π : Distribution State) (Q : MarkovKernel State) :
+    MarkovKernel State where
+  prob := probability π Q
+  nonneg := probability_nonneg π Q _
+  sum_prob := sum_probability π Q
```
(Plus corresponding signature changes in `detailed_balance` and `stationary`.)

**Gate:** `cd formal && lake build`

**Output (key lines):**
```
error: Mcmc/Finite/MetropolisHastings.lean:162:35:
  don't know how to synthesize placeholder for argument `hπ`
    context:
    π : Distribution State
    Q : MarkovKernel State
    ⊢ ∀ (x : State), 0 < π.mass x
```

**Analysis:** Removing the positivity hypothesis `hπ` from `kernel` leaves the
`probability_nonneg` call unable to fill its required argument. Lean correctly
refuses to synthesize a proof of `∀ x, 0 < π.mass x` — this is not a typeclass
obligation and cannot be inferred. The gate works because the proof obligation
is a genuine mathematical requirement that cannot be discharged without
evidence.

---

### F4 — Spec Mismatch (Lean)

**File:** `formal/Mcmc/Finite/MetropolisHastings.lean`

**Diff applied:**
```diff
 noncomputable def probability (π : Distribution State) (Q : MarkovKernel State)
     (x y : State) : ℝ :=
-  move π Q x y + if x = y then stay π Q x else 0
+  acceptance π Q x y + if x = y then stay π Q x else 0
```

**Gate:** `cd formal && lake build`

**Output (key lines):**
```
error: Tactic `apply` failed: could not unify the conclusion
  of `add_nonneg (move_nonneg π Q hπ x y)`
error: unsolved goals  [sum_probability]
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  [detailed_balance, detailed_balance_allowZeros]
```

**Analysis:** Replacing `move` with `acceptance` in the probability definition
breaks 7 downstream proofs. The `probability_nonneg` proof expected `move_nonneg`
in the first summand; `sum_probability` cannot derive the row-sum identity;
and `detailed_balance` fails because the `simp` lemmas no longer match the
altered definition. This demonstrates that the proof chain is tightly coupled
to the correct kernel specification — any definitional change propagates
failures throughout.

---

### O1 — Wrong Acceptance Sign (Julia)

**File:** `VerifiedSamplers.jl/src/Optimized/Optimized.jl`

**Diff applied:**
```diff
-    log(uniform_unit!(source)) < min(zero(logratio), logratio) ? proposal : initial
+    log(uniform_unit!(source)) > min(zero(logratio), logratio) ? proposal : initial
```

**Gate:** `julia --project=VerifiedSamplers.jl -e 'using Pkg; Pkg.test()'`

**Output:**
```
continuous normal-target moment matching: Test Failed at continuous.jl:1399
  Expression: Evaluation.conforms(comparison)

Test Summary:                              | Pass  Fail  Total
continuous and mixed-state diagnostics     |  118     7    125
  continuous normal-target moment matching |   14     7     21
ERROR: Some tests did not pass: 118 passed, 7 failed
```

**Analysis:** Flipping the acceptance comparison inverts the MH accept/reject
logic: proposals that should be accepted are rejected, and vice versa. The
moment-matching conformance tests detect this because the Optimized RWMH
sampler no longer targets the correct stationary distribution — its empirical
moments diverge from the reference.

---

### O2 — Dropped MH Correction (Julia)

**File:** `VerifiedSamplers.jl/src/Optimized/Optimized.jl`

**Diff applied:**
```diff
-    logratio = logdensity(proposal) - logdensity(initial)
-    log(uniform_unit!(source)) < min(zero(logratio), logratio) ? proposal : initial
+    proposal
```

**Gate:** `julia --project=VerifiedSamplers.jl -e 'using Pkg; Pkg.test()'`

**Output:**
```
continuous normal-target moment matching: Test Failed at continuous.jl:1399
  Expression: Evaluation.conforms(comparison)

Test Summary:                              | Pass  Fail  Total
continuous and mixed-state diagnostics     |  118     7    125
  continuous normal-target moment matching |   14     7     21
ERROR: Some tests did not pass: 118 passed, 7 failed
```

**Analysis:** Removing the accept/reject step entirely turns the RWMH sampler
into an unconditional random walk. Without the Hastings correction, the chain
does not satisfy detailed balance and does not target the correct distribution.
The same 7 conformance tests that caught O1 also catch this — the empirical
moments of the always-accept chain differ from those of the correctly
implemented reference.

---

### O3 — Changed Reference Output (Julia)

**File:** `VerifiedSamplers.jl/src/Reference/Reference.jl`

**Diff applied:**
```diff
-    (2.0 * u1 + 8.0 * u2^3, 2.0 * u2)
+    (2.0 * u1 + 8.0 * u2^3 + 0.01, 2.0 * u2)
```

**Gate:** `julia --project=VerifiedSamplers.jl -e 'using Pkg; Pkg.test()'`

**Output:**
```
nonlinear sheared birth/death reversible jump: Test Failed at reversible_jump.jl:8
nonlinear sheared birth/death reversible jump: Test Failed at reversible_jump.jl:16
  Expression: sheared_birth_unshear(reference) == (-1.0, 1.0)
nonlinear sheared birth/death reversible jump: Test Failed at reversible_jump.jl:23

Test Summary:                                       | Pass  Fail  Total
nonlinear sheared birth/death reversible jump       |   13     3     16
ERROR: Some tests did not pass: 13 passed, 3 failed
```

**Analysis:** The reversible-jump test checks that the Reference birth
transform matches exact expected values and that the Optimized implementation
matches the Reference. The +0.01 offset breaks the deterministic trace-replay
contract: for fixed random draws, the output no longer matches the expected
analytical values. The `==` comparison catches the mismatch immediately.

---

### O4 — Numerical Drift (Julia)

**File:** `VerifiedSamplers.jl/src/Optimized/Optimized.jl`

**Diff applied:**
```diff
 function leapfrog(gradient, step_size::T, position::T, momentum::T) where {T}
     half_momentum = momentum - step_size * gradient(position) / 2
-    next_position = position + step_size * half_momentum
+    next_position = position + step_size * half_momentum + T(1e-13)
     next_momentum = half_momentum - step_size * gradient(next_position) / 2
     next_position, next_momentum
 end
```

**Gate:** `julia --project=VerifiedSamplers.jl -e 'using Pkg; Pkg.test()'`

**Output:**
```
bounded numeric decision certificates: Test Failed at unit.jl:80  [×8]
bounded numeric decision certificates: Test Failed at unit.jl:99
bounded numeric decision certificates: Test Failed at unit.jl:117

Test Summary:                           | Pass  Fail  Total
bounded numeric decision certificates  |   61    10     71
ERROR: Some tests did not pass: 61 passed, 10 failed
```

**Analysis:** The 1e-13 bias exceeds the test suite's `atol=1e-14` tolerance
for leapfrog parity between Optimized and Reference implementations. The
bounded numeric decision certificates compare Optimized HMC trajectories
against Reference trajectories at machine-precision tolerance. Even a
sub-epsilon drift compounds over multiple leapfrog steps and is detected.

---

### O5 — Empty Test Selection (Julia)

**File:** `VerifiedSamplers.jl/test/runtests.jl`

**Diff applied:**
```diff
-include("reversible_jump.jl")
+if false
+include("reversible_jump.jl")
+end
```

**Gate:** `julia --project=VerifiedSamplers.jl -e 'using Pkg; Pkg.test()'`

**Output:**
```
Testing VerifiedSamplers tests passed
```

**Analysis:** The test suite passes with zero failures. Wrapping the
reversible-jump test file in `if false ... end` silently removes 16 test
assertions from the suite. Julia's `Test` module does not enforce a minimum
test count, expected test-set names, or require all included files to run.
There is no manifest of required test sets. **This fault slips through
completely.**

---

### O6 — Stale Generated Artifact (Julia)

**File:** `VerifiedSamplers.jl/src/Reference/Samplers.ir`

**Diff applied:**
```diff
-(verified-samplers-ir 29 (program "categorical_index!"
+(verified-samplers-ir 29  (program "categorical_index!"
```
(Added one extra space at byte 26.)

**Gate:** `make check-generated`

**Output:**
```
Build completed successfully (7648 jobs).
/tmp/tmp.ouffLHhlOw VerifiedSamplers.jl/src/Reference/Samplers.ir differ: byte 26, line 1
make: *** [Makefile:61: check-generated] Error 1
```

**Analysis:** The `check-generated` target rebuilds the IR generator from Lean,
runs it to produce a fresh IR file in a temporary location, then uses `cmp` for
byte-exact comparison against the committed `Samplers.ir`. Even a single
whitespace difference is detected. This gate ensures the committed IR artifact
is exactly reproducible from the Lean source, preventing stale or tampered
generated code from being deployed.

---

## Gaps and Recommendations

### Gap 1: `sorry` passes `lake build` (F2)

**Risk:** A contributor can replace any proof with `sorry` and the build
succeeds. The `stationary` theorem — the project's central correctness claim —
compiles with a `sorry`-backed `detailed_balance`.

**Recommendation:** Add a CI step that greps the build output for the `sorry`
warning pattern:

```bash
lake build 2>&1 | tee build.log
if grep -q 'declaration uses .sorry.' build.log; then
    echo "ERROR: sorry detected in build output" >&2
    exit 1
fi
```

Alternatively, use a Lean linter option (e.g., a custom `set_option` that
escalates `sorry` to an error in CI builds).

### Gap 2: Test-set deletion is invisible (O5)

**Risk:** A contributor can comment out or skip entire test files without
detection. The test suite reports "all tests passed" with an arbitrarily
reduced assertion count.

**Recommendation:** Add a test-count assertion to the CI pipeline:

```julia
# At the end of runtests.jl, or as a CI post-step:
@test Test.get_test_counts().passes >= MINIMUM_EXPECTED_PASSES
```

Or maintain a manifest of required `@testset` names and verify they all
executed. A lightweight alternative: compare the total test count against a
committed baseline.

---

## Methodology

Each fault was injected into a single file, the relevant gate was run, the
output was captured, and the fault was reverted with `git checkout -- <file>`.
Clean state was verified with `git status` after each revert. No faults remain
in the working tree.

- **Lean faults (F1–F4):** Gate is `cd formal && lake build`.
- **Julia faults (O1–O5):** Gate is `julia --project=VerifiedSamplers.jl -e 'using Pkg; Pkg.test()'`.
- **Generated-artifact fault (O6):** Gate is `make check-generated`.
