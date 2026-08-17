import Mcmc.Finite.MarkovKernel

/-!
# Finite rooted random-trace reversals

Dynamic samplers such as ordinary NUTS may generate a state-dependent random
tree whose candidate rows are not equal after rerooting. Correctness can still
be proved at the richer trace level when every complete forward random trace
has a bijective reverse trace with identical target-weighted construction and
selection probability. This module states and proves that exact boundary.
-/

open scoped BigOperators

namespace Mcmc.Finite.MarkovKernel

variable {State Trace : Type*} [Fintype State] [Fintype Trace]

/-- Transition obtained by first drawing a state-dependent finite trace and
then selecting the next state conditionally on that trace. -/
noncomputable def rootedTraceKernel
    (traceLaw : State → Distribution Trace)
    (selection : State → Trace → Distribution State) : MarkovKernel State where
  prob current next := ∑ trace,
    (traceLaw current).mass trace * (selection current trace).mass next
  nonneg current next := Finset.sum_nonneg fun trace _ =>
    mul_nonneg ((traceLaw current).nonneg trace)
      ((selection current trace).nonneg next)
  sum_prob current := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (selection current _).sum_mass, mul_one]
    exact (traceLaw current).sum_mass

/-- Trace-level detailed balance. The reverse trace may depend on both
endpoints; bijectivity reindexes the finite trace sum, while the pointwise
identity accounts for every construction and selection probability. -/
theorem rootedTraceKernel_reversible
    (target : Distribution State)
    (traceLaw : State → Distribution Trace)
    (selection : State → Trace → Distribution State)
    (reverseTrace : State → State → Trace ≃ Trace)
    (hreverse : ∀ current next trace,
      target.mass current * ((traceLaw current).mass trace *
          (selection current trace).mass next) =
        target.mass next *
          ((traceLaw next).mass (reverseTrace current next trace) *
          (selection next (reverseTrace current next trace)).mass current)) :
    (rootedTraceKernel traceLaw selection).Reversible target := by
  intro current next
  simp only [rootedTraceKernel, Finset.mul_sum]
  calc
    ∑ trace, target.mass current * ((traceLaw current).mass trace *
        (selection current trace).mass next) =
      ∑ trace, target.mass next *
        ((traceLaw next).mass (reverseTrace current next trace) *
        (selection next (reverseTrace current next trace)).mass current) := by
          apply Finset.sum_congr rfl
          intro trace _
          exact hreverse current next trace
    _ = ∑ trace, target.mass next * ((traceLaw next).mass trace *
        (selection next trace).mass current) := by
      simpa using Equiv.sum_comp (reverseTrace current next)
        (fun trace => target.mass next * ((traceLaw next).mass trace *
          (selection next trace).mass current))

/-- Consequently, a fully reversed rooted random-trace construction preserves
the target even when its raw candidate rows fail the simpler reroot checker. -/
theorem rootedTraceKernel_stationary
    (target : Distribution State)
    (traceLaw : State → Distribution Trace)
    (selection : State → Trace → Distribution State)
    (reverseTrace : State → State → Trace ≃ Trace)
    (hreverse : ∀ current next trace,
      target.mass current * ((traceLaw current).mass trace *
          (selection current trace).mass next) =
        target.mass next *
          ((traceLaw next).mass (reverseTrace current next trace) *
          (selection next (reverseTrace current next trace)).mass current)) :
    (rootedTraceKernel traceLaw selection).Stationary target :=
  (rootedTraceKernel_reversible target traceLaw selection reverseTrace
    hreverse).stationary

/-- Proof-bearing interface for a finite root-dependent dynamic sampler. Unlike
`CertifiedDynamicTree`, this certificate permits different candidate rows at
different roots, but it must retain the complete construction trace and prove
the stronger target-weighted reversal identity. -/
structure CertifiedRootedTraceSampler (target : Distribution State)
    (Trace : Type*) [Fintype Trace] where
  traceLaw : State → Distribution Trace
  selection : State → Trace → Distribution State
  reverseTrace : State → State → Trace ≃ Trace
  reverse_weight : ∀ current next trace,
    target.mass current * ((traceLaw current).mass trace *
        (selection current trace).mass next) =
      target.mass next *
        ((traceLaw next).mass (reverseTrace current next trace) *
        (selection next (reverseTrace current next trace)).mass current)

noncomputable def CertifiedRootedTraceSampler.kernel
    {target : Distribution State} (sampler : CertifiedRootedTraceSampler target Trace) :
    MarkovKernel State :=
  rootedTraceKernel sampler.traceLaw sampler.selection

theorem CertifiedRootedTraceSampler.reversible
    {target : Distribution State} (sampler : CertifiedRootedTraceSampler target Trace) :
    sampler.kernel.Reversible target :=
  rootedTraceKernel_reversible target sampler.traceLaw sampler.selection
    sampler.reverseTrace sampler.reverse_weight

theorem CertifiedRootedTraceSampler.stationary
    {target : Distribution State} (sampler : CertifiedRootedTraceSampler target Trace) :
    sampler.kernel.Stationary target :=
  sampler.reversible.stationary

/-! ### Factorized reversal certificates

Recursive trajectory builders usually compute their trace probability as a
product of local random choices, and then select an endpoint with a separate
conditional probability.  The following interface splits the reversal
obligation along exactly that implementation boundary.  This avoids hiding
the construction probability inside a single opaque balance hypothesis.
-/

/-- A factorized rooted-trace certificate separates reversal of the trace
construction law from reversal of the conditional endpoint selection.  The
`constructionRatio` is an arbitrary nonnegative bridge factor: in a NUTS
instantiation it records the product of reversed direction, subtree, and
multinomial-choice probabilities. -/
structure FactorizedRootedTraceSampler (target : Distribution State)
    (Trace : Type*) [Fintype Trace] where
  traceLaw : State → Distribution Trace
  selection : State → Trace → Distribution State
  reverseTrace : State → State → Trace ≃ Trace
  constructionRatio : State → State → Trace → ℝ
  constructionRatio_nonneg : ∀ current next trace,
    0 ≤ constructionRatio current next trace
  construction_reverse : ∀ current next trace,
    (traceLaw current).mass trace =
      constructionRatio current next trace *
        (traceLaw next).mass (reverseTrace current next trace)
  selection_reverse : ∀ current next trace,
    target.mass current *
        (constructionRatio current next trace *
          (selection current trace).mass next) =
      target.mass next *
        (selection next (reverseTrace current next trace)).mass current

/-- Combining the two local reversal identities gives the complete
target-weighted trace reversal required by `CertifiedRootedTraceSampler`. -/
noncomputable def FactorizedRootedTraceSampler.toCertified
    {target : Distribution State}
    (sampler : FactorizedRootedTraceSampler target Trace) :
    CertifiedRootedTraceSampler target Trace where
  traceLaw := sampler.traceLaw
  selection := sampler.selection
  reverseTrace := sampler.reverseTrace
  reverse_weight := by
    intro current next trace
    rw [sampler.construction_reverse]
    calc
      target.mass current *
          ((sampler.constructionRatio current next trace *
              (sampler.traceLaw next).mass
                (sampler.reverseTrace current next trace)) *
            (sampler.selection current trace).mass next) =
        (sampler.traceLaw next).mass
            (sampler.reverseTrace current next trace) *
          (target.mass current *
            (sampler.constructionRatio current next trace *
              (sampler.selection current trace).mass next)) := by
          ac_rfl
      _ = (sampler.traceLaw next).mass
            (sampler.reverseTrace current next trace) *
          (target.mass next *
            (sampler.selection next
              (sampler.reverseTrace current next trace)).mass current) := by
          rw [sampler.selection_reverse]
      _ = target.mass next *
          ((sampler.traceLaw next).mass
              (sampler.reverseTrace current next trace) *
            (sampler.selection next
              (sampler.reverseTrace current next trace)).mass current) := by
          ac_rfl

/-- The kernel implemented from a factorized trace certificate is reversible. -/
theorem FactorizedRootedTraceSampler.reversible
    {target : Distribution State}
    (sampler : FactorizedRootedTraceSampler target Trace) :
    (sampler.toCertified.kernel).Reversible target :=
  sampler.toCertified.reversible

/-- The kernel implemented from a factorized trace certificate preserves the
target distribution. -/
theorem FactorizedRootedTraceSampler.stationary
    {target : Distribution State}
    (sampler : FactorizedRootedTraceSampler target Trace) :
    (sampler.toCertified.kernel).Stationary target :=
  sampler.toCertified.stationary

end Mcmc.Finite.MarkovKernel
