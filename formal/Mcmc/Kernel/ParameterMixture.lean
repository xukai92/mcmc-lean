import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Invariance
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Independent mixtures of parameterized kernels

This module integrates a kernel whose input is `(state, parameter)` against an
independent parameter law. If every fixed-parameter section preserves the same
state target, the integrated state kernel preserves that target as well.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace Mcmc.Kernel

variable {State Parameter : Type*}
  [MeasurableSpace State] [MeasurableSpace Parameter]

/-- Independently sample a parameter and run the corresponding section of a
parameterized kernel. -/
noncomputable def independentParameterMixture
    (family : Kernel (State × Parameter) State)
    (parameterLaw : Measure Parameter) : Kernel State State :=
  family ∘ₖ Kernel.prod Kernel.id (Kernel.const State parameterLaw)

instance independentParameterMixture.instIsMarkovKernel
    (family : Kernel (State × Parameter) State) [IsMarkovKernel family]
    (parameterLaw : Measure Parameter) [IsProbabilityMeasure parameterLaw] :
    IsMarkovKernel (independentParameterMixture family parameterLaw) := by
  unfold independentParameterMixture
  infer_instance

/-- Independent integration preserves a target when every fixed-parameter
section preserves it. -/
theorem independentParameterMixture_invariant
    (family : Kernel (State × Parameter) State) [IsMarkovKernel family]
    (target : Measure State) [SFinite target]
    (parameterLaw : Measure Parameter) [IsProbabilityMeasure parameterLaw]
    (hsection : ∀ parameter,
      (Kernel.comap family (fun state => (state, parameter))
        (measurable_id.prodMk measurable_const)).Invariant target) :
    (independentParameterMixture family parameterLaw).Invariant target := by
  unfold Kernel.Invariant independentParameterMixture
  rw [← Measure.comp_assoc, ← Measure.compProd_eq_comp_prod,
    Measure.compProd_const]
  ext s hs
  rw [Measure.bind_apply hs family.aemeasurable]
  rw [MeasureTheory.lintegral_prod_symm _
    (Kernel.measurable_coe family hs).aemeasurable]
  have hfixed (parameter : Parameter) :
      ∫⁻ state, family (state, parameter) s ∂target = target s := by
    have h := congrArg (fun measure : Measure State => measure s)
      (hsection parameter)
    rw [Measure.bind_apply hs
      (Kernel.comap family (fun state => (state, parameter))
        (measurable_id.prodMk measurable_const)).aemeasurable] at h
    simpa [Kernel.comap_apply] using h
  simp_rw [hfixed]
  simp

/-- Independent integration only needs invariant sections almost everywhere
with respect to the parameter law. This is the useful form for continuously
distributed schedules, where exceptional parameter values need not be
handled separately. -/
theorem independentParameterMixture_invariant_ae
    (family : Kernel (State × Parameter) State) [IsMarkovKernel family]
    (target : Measure State) [SFinite target]
    (parameterLaw : Measure Parameter) [IsProbabilityMeasure parameterLaw]
    (hsection : ∀ᵐ parameter ∂parameterLaw,
      (Kernel.comap family (fun state => (state, parameter))
        (measurable_id.prodMk measurable_const)).Invariant target) :
    (independentParameterMixture family parameterLaw).Invariant target := by
  unfold Kernel.Invariant independentParameterMixture
  rw [← Measure.comp_assoc, ← Measure.compProd_eq_comp_prod,
    Measure.compProd_const]
  ext s hs
  rw [Measure.bind_apply hs family.aemeasurable]
  rw [MeasureTheory.lintegral_prod_symm _
    (Kernel.measurable_coe family hs).aemeasurable]
  have hfixed : ∀ᵐ parameter ∂parameterLaw,
      ∫⁻ state, family (state, parameter) s ∂target = target s := by
    filter_upwards [hsection] with parameter hparameter
    have h := congrArg (fun measure : Measure State => measure s) hparameter
    rw [Measure.bind_apply hs
      (Kernel.comap family (fun state => (state, parameter))
        (measurable_id.prodMk measurable_const)).aemeasurable] at h
    simpa [Kernel.comap_apply] using h
  rw [lintegral_congr_ae hfixed]
  simp

/-- A countable mixture of parameter laws preserves a target when the
parameter-averaged kernel for every component law preserves it.  This is
strictly weaker than requiring individual parameter sections to be invariant:
the averaging inside each component may supply an essential cancellation. -/
theorem independentParameterMixture_measureSum_invariant
    {Index : Type*} [Countable Index]
    (family : Kernel (State × Parameter) State) [IsMarkovKernel family]
    (target : Measure State) [SFinite target]
    (weight : Index → ENNReal)
    (componentLaw : Index → Measure Parameter)
    [componentSFinite : ∀ index, SFinite (componentLaw index)]
    (hweight : ∑' index, weight index = 1)
    (hcomponent : ∀ index,
      (independentParameterMixture family (componentLaw index)).Invariant
        target) :
    (independentParameterMixture family
      (Measure.sum fun index => weight index • componentLaw index)).Invariant
        target := by
  unfold Kernel.Invariant independentParameterMixture
  rw [← Measure.comp_assoc, ← Measure.compProd_eq_comp_prod,
    Measure.compProd_const]
  ext s hs
  rw [Measure.bind_apply hs family.aemeasurable]
  rw [MeasureTheory.lintegral_prod_symm _
    (Kernel.measurable_coe family hs).aemeasurable]
  have hfixed (index : Index) :
      ∫⁻ parameter, ∫⁻ state, family (state, parameter) s ∂target
          ∂componentLaw index = target s := by
    have h := congrArg (fun measure : Measure State => measure s)
      (hcomponent index)
    unfold Kernel.Invariant independentParameterMixture at h
    rw [← Measure.comp_assoc, ← Measure.compProd_eq_comp_prod,
      Measure.compProd_const, Measure.bind_apply hs family.aemeasurable,
      MeasureTheory.lintegral_prod_symm _
        (Kernel.measurable_coe family hs).aemeasurable] at h
    exact h
  rw [lintegral_sum_measure]
  simp_rw [lintegral_smul_measure, smul_eq_mul, hfixed]
  calc
    ∑' index, weight index * target s =
        (∑' index, weight index) * target s := ENNReal.tsum_mul_right
    _ = target s := by rw [hweight, one_mul]

/-- Exact transport decomposition for a countable mixture of parameter laws.
Unlike `independentParameterMixture_measureSum_invariant`, this identity does
not ask each component to be invariant: cancellation may occur only after the
weighted transported component measures are summed. -/
theorem measure_comp_independentParameterMixture_measureSum
    {Index : Type*} [Countable Index]
    (family : Kernel (State × Parameter) State) [IsMarkovKernel family]
    (source : Measure State) [SFinite source]
    (weight : Index → ENNReal)
    (componentLaw : Index → Measure Parameter)
    [componentSFinite : ∀ index, SFinite (componentLaw index)] :
    independentParameterMixture family
        (Measure.sum fun index => weight index • componentLaw index) ∘ₘ source =
      Measure.sum fun index => weight index •
        (independentParameterMixture family (componentLaw index) ∘ₘ source) := by
  ext s hs
  unfold independentParameterMixture
  rw [← Measure.comp_assoc, ← Measure.compProd_eq_comp_prod,
    Measure.compProd_const, Measure.bind_apply hs family.aemeasurable,
    MeasureTheory.lintegral_prod_symm _
      (Kernel.measurable_coe family hs).aemeasurable]
  rw [lintegral_sum_measure]
  simp_rw [lintegral_smul_measure, smul_eq_mul]
  rw [Measure.sum_apply _ hs]
  apply tsum_congr
  intro index
  rw [Measure.smul_apply, smul_eq_mul]
  congr 1
  rw [← Measure.comp_assoc, ← Measure.compProd_eq_comp_prod,
    Measure.compProd_const, Measure.bind_apply hs family.aemeasurable,
    MeasureTheory.lintegral_prod_symm _
      (Kernel.measurable_coe family hs).aemeasurable]

end Mcmc.Kernel
