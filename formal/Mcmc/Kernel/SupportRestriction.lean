import Mcmc.Kernel.MetropolisHastings

/-!
# Support-restricted targets and the hard-zero accepted flow

This module proves that the density-based Metropolis–Hastings construction
from `Mcmc.Kernel.MetropolisHastings` correctly handles targets that are
zero outside a measurable support set.  When the target weight is
`S.indicator w`, the accepted flow vanishes whenever either endpoint
leaves `S`, and the standard MH ratio applies when both endpoints are
inside `S`.

This is the formal foundation for path sampling with hard event indicators:
the path target `π̃(X) = ρ(x₀) ∏ p(x_{t+1}|xₜ) · 𝟙_E(X)` has genuine
zeros outside the event `E`, and the MH machinery rejects proposals into
those regions without requiring a globally positive target.

**Claim level:** detailed balance (reversibility) and hence stationarity
for the density MH kernel with support-restricted weights.  This does not
imply convergence from arbitrary initial states.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace Mcmc.Kernel

variable {State : Type*} [MeasurableSpace State]

/-! ## Pointwise behavior at zero weight

These lemmas make explicit how `forwardDensityFlow`, `densityAcceptance`,
and `symmetricAcceptedFlow` behave when the target weight vanishes.
The `densityAcceptance` definition already guards against division by
zero; these lemmas document the resulting rejection behavior. -/

omit [MeasurableSpace State] in
/-- Forward density flow vanishes when the current state has zero weight. -/
theorem forwardDensityFlow_eq_zero_of_weight_eq_zero
    (weight : State → ENNReal) (proposalDensity : State → State → ENNReal)
    {x : State} (hx : weight x = 0) (y : State) :
    forwardDensityFlow weight proposalDensity x y = 0 := by
  simp [forwardDensityFlow, hx]

omit [MeasurableSpace State] in
/-- The MH acceptance probability is zero when the current state has zero
weight—the chain rejects and stays put. -/
theorem densityAcceptance_eq_zero_of_weight_eq_zero
    (weight : State → ENNReal) (proposalDensity : State → State → ENNReal)
    {x : State} (hx : weight x = 0) (y : State) :
    densityAcceptance weight proposalDensity x y = 0 := by
  have h := forwardDensityFlow_eq_zero_of_weight_eq_zero weight proposalDensity hx y
  unfold densityAcceptance
  rw [h, if_pos rfl]

omit [MeasurableSpace State] in
/-- The symmetric accepted flow vanishes when the current state has zero
weight: `min(0 · q(x,y), w(y) · q(y,x)) = 0`. -/
theorem symmetricAcceptedFlow_eq_zero_of_weight_eq_zero_left
    (weight : State → ENNReal) (proposalDensity : State → State → ENNReal)
    {x : State} (hx : weight x = 0) (y : State) :
    symmetricAcceptedFlow weight proposalDensity x y = 0 := by
  unfold symmetricAcceptedFlow
  rw [forwardDensityFlow_eq_zero_of_weight_eq_zero weight proposalDensity hx]
  simp

omit [MeasurableSpace State] in
/-- The symmetric accepted flow vanishes when the proposed state has zero
weight: `min(w(x) · q(x,y), 0 · q(y,x)) = 0`. -/
theorem symmetricAcceptedFlow_eq_zero_of_weight_eq_zero_right
    (weight : State → ENNReal) (proposalDensity : State → State → ENNReal)
    (x : State) {y : State} (hy : weight y = 0) :
    symmetricAcceptedFlow weight proposalDensity x y = 0 := by
  rw [symmetricAcceptedFlow_swap]
  exact symmetricAcceptedFlow_eq_zero_of_weight_eq_zero_left
    weight proposalDensity hy x

/-! ## Support-restricted target weights

A support-restricted weight `S.indicator w` restricts a base weight `w` to
a measurable set `S`.  The density-based MH machinery applies to this
weight without requiring `w` to be positive on the full state space.

For path sampling with hard conditioning, `S` is the event `E` and `w` is
the unconstrained path density. -/

section SupportRestriction

variable {w : State → ENNReal} {S : Set State}
  {proposalDensity : State → State → ENNReal}

omit [MeasurableSpace State] in
/-- A support-restricted weight vanishes outside `S`. -/
theorem indicator_weight_zero_outside {x : State} (hx : x ∉ S) :
    S.indicator w x = 0 :=
  Set.indicator_of_notMem hx w

omit [MeasurableSpace State] in
/-- A support-restricted weight equals the base weight inside `S`. -/
theorem indicator_weight_eq_inside {x : State} (hx : x ∈ S) :
    S.indicator w x = w x :=
  Set.indicator_of_mem hx w

/-- A support-restricted weight is measurable when both the base weight
and the support set are measurable. -/
theorem measurable_indicator_weight (hw : Measurable w) (hS : MeasurableSet S) :
    Measurable (S.indicator w) :=
  hw.indicator hS

omit [MeasurableSpace State] in
/-- Forward density flow with a support-restricted weight is finite
whenever the unrestricted forward flow is finite. -/
theorem forwardDensityFlow_indicator_ne_top
    (hfinite : ∀ x y, forwardDensityFlow w proposalDensity x y ≠ ⊤)
    (x y : State) :
    forwardDensityFlow (S.indicator w) proposalDensity x y ≠ ⊤ := by
  unfold forwardDensityFlow at hfinite ⊢
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx]; exact hfinite x y
  · rw [Set.indicator_of_notMem hx, zero_mul]; exact ENNReal.zero_ne_top

end SupportRestriction

/-! ## Main theorems: density MH with support-restricted weights

These are the principal results: the density-based MH kernel constructed
from `S.indicator w` satisfies detailed balance—and hence stationarity—with
respect to `densityTarget reference (S.indicator w)`, the target measure
restricted to `S`.

The proofs apply the existing general `densityMetropolisHastings_isReversible`
and `densityMetropolisHastings_invariant` from `MetropolisHastings.lean` after
verifying the measurability and finiteness hypotheses. -/

/-- Density-based MH with a support-restricted target weight satisfies
detailed balance with respect to the restricted target measure.  When both
the current and proposed states are in `S`, the standard MH ratio applies.
When either state is outside `S`, the accepted flow is zero and the move
is rejected. -/
theorem densityMetropolisHastings_supportRestricted_isReversible
    (reference : Measure State) [SFinite reference]
    (w : State → ENNReal) (proposalDensity : State → State → ENNReal)
    {S : Set State}
    (hw : Measurable w) (hS : MeasurableSet S)
    (hproposal : Measurable (Function.uncurry proposalDensity))
    (hproposalNorm : ∀ x, ∫⁻ y, proposalDensity x y ∂reference = 1)
    (hfinite : ∀ x y, forwardDensityFlow w proposalDensity x y ≠ ⊤) :
    (densityMetropolisHastings reference (S.indicator w) proposalDensity
      hproposal hproposalNorm).IsReversible
        (densityTarget reference (S.indicator w)) :=
  densityMetropolisHastings_isReversible reference (S.indicator w) proposalDensity
    (measurable_indicator_weight hw hS) hproposal hproposalNorm
    (forwardDensityFlow_indicator_ne_top hfinite)

/-- Density-based MH with a support-restricted target weight preserves the
restricted target measure.  This is the stationarity result: the density MH
kernel leaves `densityTarget reference (S.indicator w)` invariant.

This does not by itself imply convergence from arbitrary initial paths.
Convergence would require additional ergodicity assumptions (irreducibility
and aperiodicity on the restricted state space). -/
theorem densityMetropolisHastings_supportRestricted_invariant
    (reference : Measure State) [SFinite reference]
    (w : State → ENNReal) (proposalDensity : State → State → ENNReal)
    {S : Set State}
    (hw : Measurable w) (hS : MeasurableSet S)
    (hproposal : Measurable (Function.uncurry proposalDensity))
    (hproposalNorm : ∀ x, ∫⁻ y, proposalDensity x y ∂reference = 1)
    (hfinite : ∀ x y, forwardDensityFlow w proposalDensity x y ≠ ⊤) :
    (densityMetropolisHastings reference (S.indicator w) proposalDensity
      hproposal hproposalNorm).Invariant
        (densityTarget reference (S.indicator w)) :=
  densityMetropolisHastings_invariant reference (S.indicator w) proposalDensity
    (measurable_indicator_weight hw hS) hproposal hproposalNorm
    (forwardDensityFlow_indicator_ne_top hfinite)

end Mcmc.Kernel
