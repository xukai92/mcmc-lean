import Mcmc.Finite.RootedTrace
import Mcmc.Finite.Combinators

/-!
# Finite auxiliary augmentation for dynamic trajectory samplers

This module packages the final algebraic composition used by finite NUTS-style
samplers. From a current root, first draw a state-dependent completed-tree or
slice auxiliary, then apply its conditional root transition, and finally
discard the auxiliary. A target-weighted slice-flow identity proves detailed
balance of the collapsed state transition. A weaker stationary-slice identity
is sufficient for stationarity.
-/

open scoped BigOperators

namespace Mcmc.Finite.MarkovKernel

variable {State Aux : Type*} [Fintype State] [Fintype Aux]

/-! ### Lifting an auxiliary-specific admissible subtype -/

/-- Total full-state kernel induced by a kernel on an admissible subtype.
Admitted states use the subtype transition and cannot move outside it;
inadmissible states use an explicit identity fallback. -/
noncomputable def liftAdmissibleSubtypeKernel
    [DecidableEq State] (admitted : State → Prop) [DecidablePred admitted]
    (kernel : MarkovKernel {state // admitted state}) : MarkovKernel State where
  prob current next :=
    if hcurrent : admitted current then
      if hnext : admitted next then
        kernel.prob ⟨current, hcurrent⟩ ⟨next, hnext⟩
      else 0
    else if next = current then 1 else 0
  nonneg current next := by
    split
    · split
      · exact kernel.nonneg _ _
      · exact le_rfl
    · split <;> norm_num
  sum_prob current := by
    classical
    by_cases hcurrent : admitted current
    · simp only [hcurrent, dif_pos]
      calc
        ∑ next, (if hnext : admitted next then
            kernel.prob ⟨current, hcurrent⟩ ⟨next, hnext⟩ else 0) =
          ∑ next : {state // admitted state},
            kernel.prob ⟨current, hcurrent⟩ next := by
              have hpartition := Fintype.sum_subtype_add_sum_subtype admitted
                (fun next => if hnext : admitted next then
                  kernel.prob ⟨current, hcurrent⟩ ⟨next, hnext⟩ else 0)
              have hfirst :
                  (∑ next : {state // admitted state},
                    if hnext : admitted next.val then
                      kernel.prob ⟨current, hcurrent⟩ ⟨next.val, hnext⟩
                    else 0) =
                    ∑ next : {state // admitted state},
                      kernel.prob ⟨current, hcurrent⟩ next := by
                apply Finset.sum_congr rfl
                intro next _
                simp [next.property]
              have hsecond :
                  (∑ next : {state // ¬ admitted state},
                    if hnext : admitted next.val then
                      kernel.prob ⟨current, hcurrent⟩ ⟨next.val, hnext⟩
                    else 0) = 0 := by
                apply Finset.sum_eq_zero
                intro next _
                simp [next.property]
              calc
                _ = _ + _ := hpartition.symm
                _ = _ + 0 := by rw [hfirst, hsecond]
                _ = _ := add_zero _
        _ = 1 := kernel.sum_prob ⟨current, hcurrent⟩
    · simp [hcurrent]

@[simp] theorem liftAdmissibleSubtypeKernel_prob_of_admitted
    [DecidableEq State] (admitted : State → Prop) [DecidablePred admitted]
    (kernel : MarkovKernel {state // admitted state})
    (current next : State) (hcurrent : admitted current)
    (hnext : admitted next) :
    (liftAdmissibleSubtypeKernel admitted kernel).prob current next =
      kernel.prob ⟨current, hcurrent⟩ ⟨next, hnext⟩ := by
  simp [liftAdmissibleSubtypeKernel, hcurrent, hnext]

/-- Certificate relating an auxiliary fiber's full-state unnormalized weight
to a reversible normalized target on its admitted subtype. -/
structure AdmissibleSubtypeFiber
    (weight : State → ℝ) (admitted : State → Prop)
    [DecidablePred admitted] where
  normalizer : ℝ
  normalizer_pos : 0 < normalizer
  target : Distribution {state // admitted state}
  kernel : MarkovKernel {state // admitted state}
  target_mass : ∀ state,
    target.mass state = weight state.val / normalizer
  outside_zero : ∀ state, ¬ admitted state → weight state = 0
  reversible : kernel.Reversible target

/-- Normalized subtype reversibility transfers to the unnormalized full-state
fiber after the total lift, including all cross-boundary zero cases. -/
theorem AdmissibleSubtypeFiber.lift_balance
    (weight : State → ℝ) (admitted : State → Prop)
    [DecidableEq State] [DecidablePred admitted]
    (fiber : AdmissibleSubtypeFiber weight admitted)
    (current next : State) :
    weight current *
        (liftAdmissibleSubtypeKernel admitted fiber.kernel).prob current next =
      weight next *
        (liftAdmissibleSubtypeKernel admitted fiber.kernel).prob next current := by
  by_cases hcurrent : admitted current
  · by_cases hnext : admitted next
    · simp only [liftAdmissibleSubtypeKernel_prob_of_admitted admitted
          fiber.kernel current next hcurrent hnext,
        liftAdmissibleSubtypeKernel_prob_of_admitted admitted fiber.kernel next
          current hnext hcurrent]
      have hreverse := fiber.reversible ⟨current, hcurrent⟩ ⟨next, hnext⟩
      rw [fiber.target_mass, fiber.target_mass] at hreverse
      field_simp [fiber.normalizer_pos.ne'] at hreverse
      exact hreverse
    · have hnextZero := fiber.outside_zero next hnext
      simp [liftAdmissibleSubtypeKernel, hcurrent, hnext, hnextZero]
  · have hcurrentZero := fiber.outside_zero current hcurrent
    by_cases hnext : admitted next
    · simp [liftAdmissibleSubtypeKernel, hcurrent, hnext, hcurrentZero]
    · have hnextZero := fiber.outside_zero next hnext
      simp [liftAdmissibleSubtypeKernel, hcurrent, hnext, hcurrentZero,
        hnextZero]

/-- Unnormalized joint target weight of one state/auxiliary pair. -/
noncomputable def auxiliaryJointWeight
    (target : Distribution State) (auxiliaryLaw : State → Distribution Aux)
    (auxiliary : Aux) (state : State) : ℝ :=
  target.mass state * (auxiliaryLaw state).mass auxiliary

/-- Family of auxiliary-specific admissible-subtype certificates on one common
full state space. This is the interface needed when each completed NUTS tree
retains a different C.4 root subtype. -/
structure AuxiliarySubtypeFiberCertificate
    (target : Distribution State) (auxiliaryLaw : State → Distribution Aux)
    (admitted : Aux → State → Prop)
    [∀ auxiliary, DecidablePred (admitted auxiliary)] where
  fiber : ∀ auxiliary,
    AdmissibleSubtypeFiber
      (auxiliaryJointWeight target auxiliaryLaw auxiliary)
      (admitted auxiliary)

/-- Collapsed state transition obtained by drawing an auxiliary conditionally
on the current state and applying its indexed conditional transition. -/
noncomputable def auxiliaryCollapsedKernel
    (auxiliaryLaw : State → Distribution Aux)
    (conditional : Aux → MarkovKernel State) : MarkovKernel State where
  prob current next := ∑ auxiliary,
    (auxiliaryLaw current).mass auxiliary *
      (conditional auxiliary).prob current next
  nonneg current next := Finset.sum_nonneg fun auxiliary _ =>
    mul_nonneg ((auxiliaryLaw current).nonneg auxiliary)
      ((conditional auxiliary).nonneg current next)
  sum_prob current := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (conditional _).sum_prob, mul_one]
    exact (auxiliaryLaw current).sum_mass

/-- Each auxiliary slice preserves its portion of the augmented target. This
is the stationarity-strength form of the Gibbs compatibility obligation. -/
def PreservesAuxiliarySlices
    (target : Distribution State)
    (auxiliaryLaw : State → Distribution Aux)
    (conditional : Aux → MarkovKernel State) : Prop :=
  ∀ auxiliary next,
    ∑ current, target.mass current *
        (auxiliaryLaw current).mass auxiliary *
        (conditional auxiliary).prob current next =
      target.mass next * (auxiliaryLaw next).mass auxiliary

/-- Conditional auxiliary refresh followed by slice-preserving root updates
preserves the marginal target after the auxiliary is discarded. -/
theorem auxiliaryCollapsedKernel_stationary
    (target : Distribution State)
    (auxiliaryLaw : State → Distribution Aux)
    (conditional : Aux → MarkovKernel State)
    (hpreserve : PreservesAuxiliarySlices target auxiliaryLaw conditional) :
    (auxiliaryCollapsedKernel auxiliaryLaw conditional).Stationary target := by
  intro next
  calc
    ∑ current, target.mass current *
        (auxiliaryCollapsedKernel auxiliaryLaw conditional).prob current next =
      ∑ auxiliary, ∑ current,
        target.mass current * (auxiliaryLaw current).mass auxiliary *
          (conditional auxiliary).prob current next := by
        simp only [auxiliaryCollapsedKernel, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro auxiliary _
        apply Finset.sum_congr rfl
        intro current _
        ring
    _ = ∑ auxiliary,
        target.mass next * (auxiliaryLaw next).mass auxiliary := by
      apply Finset.sum_congr rfl
      intro auxiliary _
      exact hpreserve auxiliary next
    _ = target.mass next := by
      rw [← Finset.mul_sum, (auxiliaryLaw next).sum_mass, mul_one]

/-- Stronger pointwise flow condition on every augmented auxiliary slice. -/
def ReversesAuxiliarySlices
    (target : Distribution State)
    (auxiliaryLaw : State → Distribution Aux)
    (conditional : Aux → MarkovKernel State) : Prop :=
  ∀ auxiliary current next,
    target.mass current * (auxiliaryLaw current).mass auxiliary *
        (conditional auxiliary).prob current next =
      target.mass next * (auxiliaryLaw next).mass auxiliary *
        (conditional auxiliary).prob next current

/-- Pointwise augmented-slice balance implies detailed balance after summing
over the state-dependent completed-tree/slice auxiliary. -/
theorem auxiliaryCollapsedKernel_reversible
    (target : Distribution State)
    (auxiliaryLaw : State → Distribution Aux)
    (conditional : Aux → MarkovKernel State)
    (hreverse : ReversesAuxiliarySlices target auxiliaryLaw conditional) :
    (auxiliaryCollapsedKernel auxiliaryLaw conditional).Reversible target := by
  intro current next
  simp only [auxiliaryCollapsedKernel, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro auxiliary _
  simpa [mul_assoc] using hreverse auxiliary current next

/-- Slice reversibility implies the weaker slice-stationarity equations. -/
theorem ReversesAuxiliarySlices.preserves
    (target : Distribution State)
    (auxiliaryLaw : State → Distribution Aux)
    (conditional : Aux → MarkovKernel State)
    (hreverse : ReversesAuxiliarySlices target auxiliaryLaw conditional) :
    PreservesAuxiliarySlices target auxiliaryLaw conditional := by
  intro auxiliary next
  calc
    ∑ current, target.mass current *
        (auxiliaryLaw current).mass auxiliary *
        (conditional auxiliary).prob current next =
      ∑ current, target.mass next *
        (auxiliaryLaw next).mass auxiliary *
        (conditional auxiliary).prob next current := by
          apply Finset.sum_congr rfl
          intro current _
          exact hreverse auxiliary current next
    _ = target.mass next * (auxiliaryLaw next).mass auxiliary := by
      rw [← Finset.mul_sum, (conditional auxiliary).sum_prob, mul_one]

/-! ### From normalized conditional targets to auxiliary-slice flow -/

/-- Marginal mass of one completed-tree/slice auxiliary. -/
noncomputable def auxiliarySliceMass
    (target : Distribution State) (auxiliaryLaw : State → Distribution Aux)
    (auxiliary : Aux) : ℝ :=
  ∑ state, target.mass state * (auxiliaryLaw state).mass auxiliary

theorem auxiliarySliceMass_nonneg
    (target : Distribution State) (auxiliaryLaw : State → Distribution Aux)
    (auxiliary : Aux) :
    0 ≤ auxiliarySliceMass target auxiliaryLaw auxiliary := by
  exact Finset.sum_nonneg fun state _ =>
    mul_nonneg (target.nonneg state) ((auxiliaryLaw state).nonneg auxiliary)

/-- Normalized state target conditional on a positive-mass auxiliary slice. -/
noncomputable def auxiliarySliceTarget
    (target : Distribution State) (auxiliaryLaw : State → Distribution Aux)
    (auxiliary : Aux)
    (hpositive : 0 < auxiliarySliceMass target auxiliaryLaw auxiliary) :
    Distribution State where
  mass state := target.mass state * (auxiliaryLaw state).mass auxiliary /
    auxiliarySliceMass target auxiliaryLaw auxiliary
  nonneg state := div_nonneg
    (mul_nonneg (target.nonneg state)
      ((auxiliaryLaw state).nonneg auxiliary)) hpositive.le
  sum_mass := by
    rw [← Finset.sum_div]
    exact div_self hpositive.ne'

/-- A conditional kernel reversible for every positive normalized auxiliary
slice automatically supplies the unnormalized slice flow used by NUTS. No
condition is needed on zero-mass fibers because they are invisible under the
joint target. -/
structure ConditionalAuxiliaryReversibility
    (target : Distribution State)
    (auxiliaryLaw : State → Distribution Aux) where
  conditional : Aux → MarkovKernel State
  reversible_positive : ∀ auxiliary
    (hpositive : 0 < auxiliarySliceMass target auxiliaryLaw auxiliary),
    (conditional auxiliary).Reversible
      (auxiliarySliceTarget target auxiliaryLaw auxiliary hpositive)

/-- Upgrade normalized conditional reversibility to pointwise augmented-slice
flow, including a proof that every zero-mass slice term vanishes. -/
theorem ConditionalAuxiliaryReversibility.reverse_slices
    (target : Distribution State)
    (auxiliaryLaw : State → Distribution Aux)
    (certificate : ConditionalAuxiliaryReversibility target auxiliaryLaw) :
    ReversesAuxiliarySlices target auxiliaryLaw certificate.conditional := by
  intro auxiliary current next
  by_cases hpositive : 0 < auxiliarySliceMass target auxiliaryLaw auxiliary
  · have hreverse := certificate.reversible_positive auxiliary hpositive
        current next
    simp only [auxiliarySliceTarget] at hreverse
    field_simp [hpositive.ne'] at hreverse
    exact hreverse
  · have hzero : auxiliarySliceMass target auxiliaryLaw auxiliary = 0 :=
      le_antisymm (not_lt.mp hpositive)
        (auxiliarySliceMass_nonneg target auxiliaryLaw auxiliary)
    have hnonneg : ∀ state ∈ (Finset.univ : Finset State),
        0 ≤ target.mass state * (auxiliaryLaw state).mass auxiliary := by
      intro state _
      exact mul_nonneg (target.nonneg state)
        ((auxiliaryLaw state).nonneg auxiliary)
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero
    rw [hall current (Finset.mem_univ current),
      hall next (Finset.mem_univ next)]
    simp

/-- Proof-bearing interface for a finite state-dependent auxiliary sampler,
including the outer completed-tree/slice draw. -/
structure CertifiedAuxiliarySampler (target : Distribution State)
    (Aux : Type*) [Fintype Aux] where
  auxiliaryLaw : State → Distribution Aux
  conditional : Aux → MarkovKernel State
  reverse_slices : ReversesAuxiliarySlices target auxiliaryLaw conditional

/-- Build the complete collapsed auxiliary sampler from conditional
reversibility certificates on its positive fibers. -/
noncomputable def ConditionalAuxiliaryReversibility.toCertifiedSampler
    (target : Distribution State)
    (auxiliaryLaw : State → Distribution Aux)
    (certificate : ConditionalAuxiliaryReversibility target auxiliaryLaw) :
    CertifiedAuxiliarySampler target Aux where
  auxiliaryLaw := auxiliaryLaw
  conditional := certificate.conditional
  reverse_slices := certificate.reverse_slices target auxiliaryLaw

noncomputable def CertifiedAuxiliarySampler.kernel
    {target : Distribution State}
    (sampler : CertifiedAuxiliarySampler target Aux) : MarkovKernel State :=
  auxiliaryCollapsedKernel sampler.auxiliaryLaw sampler.conditional

theorem CertifiedAuxiliarySampler.reversible
    {target : Distribution State}
    (sampler : CertifiedAuxiliarySampler target Aux) :
    sampler.kernel.Reversible target :=
  auxiliaryCollapsedKernel_reversible target sampler.auxiliaryLaw
    sampler.conditional sampler.reverse_slices

theorem CertifiedAuxiliarySampler.stationary
    {target : Distribution State}
    (sampler : CertifiedAuxiliarySampler target Aux) :
    sampler.kernel.Stationary target :=
  sampler.reversible.stationary

/-- Lift every varying admissible-root fiber to the common phase state and
assemble the state-dependent auxiliary sampler. -/
noncomputable def AuxiliarySubtypeFiberCertificate.toCertifiedSampler
    [DecidableEq State]
    (target : Distribution State) (auxiliaryLaw : State → Distribution Aux)
    (admitted : Aux → State → Prop)
    [∀ auxiliary, DecidablePred (admitted auxiliary)]
    (certificate : AuxiliarySubtypeFiberCertificate target auxiliaryLaw
      admitted) : CertifiedAuxiliarySampler target Aux where
  auxiliaryLaw := auxiliaryLaw
  conditional auxiliary :=
    liftAdmissibleSubtypeKernel (admitted auxiliary)
      (certificate.fiber auxiliary).kernel
  reverse_slices := by
    intro auxiliary current next
    exact (certificate.fiber auxiliary).lift_balance
      (auxiliaryJointWeight target auxiliaryLaw auxiliary)
      (admitted auxiliary) current next

/-- The common-state sampler assembled from varying C.4-admissible fibers is
reversible. -/
theorem AuxiliarySubtypeFiberCertificate.toCertifiedSampler_reversible
    [DecidableEq State]
    (target : Distribution State) (auxiliaryLaw : State → Distribution Aux)
    (admitted : Aux → State → Prop)
    [∀ auxiliary, DecidablePred (admitted auxiliary)]
    (certificate : AuxiliarySubtypeFiberCertificate target auxiliaryLaw
      admitted) :
    (certificate.toCertifiedSampler target auxiliaryLaw admitted).kernel.Reversible
      target :=
  (certificate.toCertifiedSampler target auxiliaryLaw admitted).reversible

/-- Consequently the common-state sampler preserves the marginal target. -/
theorem AuxiliarySubtypeFiberCertificate.toCertifiedSampler_stationary
    [DecidableEq State]
    (target : Distribution State) (auxiliaryLaw : State → Distribution Aux)
    (admitted : Aux → State → Prop)
    [∀ auxiliary, DecidablePred (admitted auxiliary)]
    (certificate : AuxiliarySubtypeFiberCertificate target auxiliaryLaw
      admitted) :
    (certificate.toCertifiedSampler target auxiliaryLaw admitted).kernel.Stationary
      target :=
  (certificate.toCertifiedSampler target auxiliaryLaw admitted).stationary

/-! ### Exact conditional-refresh instantiation -/

/-- State-independent refresh from a finite distribution. -/
def distributionRefreshKernel (law : Distribution State) :
    MarkovKernel State where
  prob _ next := law.mass next
  nonneg _ next := law.nonneg next
  sum_prob _ := law.sum_mass

theorem distributionRefreshKernel_reversible (law : Distribution State) :
    (distributionRefreshKernel law).Reversible law := by
  intro current next
  simp [distributionRefreshKernel]
  ring

/-- Exact state refresh conditional on one auxiliary. Positive slices refresh
from their normalized conditional target; null slices use identity. -/
noncomputable def auxiliaryConditionalRefreshKernel
    [DecidableEq State]
    (target : Distribution State) (auxiliaryLaw : State → Distribution Aux)
    (auxiliary : Aux) : MarkovKernel State :=
  if hpositive : 0 < auxiliarySliceMass target auxiliaryLaw auxiliary then
    distributionRefreshKernel
      (auxiliarySliceTarget target auxiliaryLaw auxiliary hpositive)
  else
    identity

/-- The exact conditional refresh is reversible on every positive auxiliary
slice and therefore meets the collapsed augmentation certificate. -/
noncomputable def auxiliaryConditionalRefreshCertificate
    [DecidableEq State]
    (target : Distribution State) (auxiliaryLaw : State → Distribution Aux) :
    ConditionalAuxiliaryReversibility target auxiliaryLaw where
  conditional := auxiliaryConditionalRefreshKernel target auxiliaryLaw
  reversible_positive := by
    intro auxiliary hpositive
    rw [auxiliaryConditionalRefreshKernel, dif_pos hpositive]
    exact distributionRefreshKernel_reversible _

/-- Fully assembled exact auxiliary Gibbs transition on the marginal state. -/
noncomputable def exactAuxiliaryGibbsSampler
    [DecidableEq State]
    (target : Distribution State) (auxiliaryLaw : State → Distribution Aux) :
    CertifiedAuxiliarySampler target Aux :=
  (auxiliaryConditionalRefreshCertificate target auxiliaryLaw).toCertifiedSampler
    target auxiliaryLaw

theorem exactAuxiliaryGibbsSampler_stationary
    [DecidableEq State]
    (target : Distribution State) (auxiliaryLaw : State → Distribution Aux) :
    (exactAuxiliaryGibbsSampler target auxiliaryLaw).kernel.Stationary target :=
  (exactAuxiliaryGibbsSampler target auxiliaryLaw).stationary

end Mcmc.Finite.MarkovKernel
