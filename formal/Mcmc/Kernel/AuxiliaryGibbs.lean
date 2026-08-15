import Mcmc.Kernel.LiftEvolveProject

/-!
# General-state auxiliary-variable Gibbs transitions

This module formalizes the exact two-block data-augmentation pattern behind
slice sampling and many latent-variable samplers.  A forward kernel augments
the target; a reverse kernel is required to give the opposite factorization
of the same joint measure.  Alternating the two exact conditionals and then
discarding the auxiliary variable preserves the original target.

The factorization equation is explicit.  It is the measure-theoretic Bayes
obligation for a concrete slice or data-augmentation construction, not an
assumed convergence statement.
-/

open MeasureTheory
open scoped ProbabilityTheory

namespace Mcmc.Kernel

open ProbabilityTheory

variable {State Aux : Type*} [MeasurableSpace State] [MeasurableSpace Aux]

/-- Retain the first coordinate and resample the second from a conditional
kernel depending on that first coordinate. -/
noncomputable def refreshSndGivenFst (conditional : Kernel Aux State) :
    Kernel (Aux × State) (Aux × State) :=
  (Kernel.id ×ₖ conditional) ∘ₖ
    Kernel.deterministic (Prod.fst : Aux × State → Aux) measurable_fst

instance refreshSndGivenFst.instIsMarkovKernel
    (conditional : Kernel Aux State) [IsMarkovKernel conditional] :
    IsMarkovKernel (refreshSndGivenFst conditional) := by
  unfold refreshSndGivenFst
  infer_instance

/-- Exact conditional refresh preserves the semidirect-product joint law. -/
theorem refreshSndGivenFst_invariant
    (auxMarginal : Measure Aux) [SFinite auxMarginal]
    (conditional : Kernel Aux State) [IsMarkovKernel conditional] :
    (refreshSndGivenFst conditional).Invariant
      (auxMarginal ⊗ₘ conditional) := by
  rw [ProbabilityTheory.Kernel.Invariant]
  unfold refreshSndGivenFst
  rw [← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map measurable_fst]
  change (Kernel.id ×ₖ conditional) ∘ₘ
    (auxMarginal ⊗ₘ conditional).fst = auxMarginal ⊗ₘ conditional
  rw [Measure.fst_compProd]
  exact (Measure.compProd_eq_comp_prod auxMarginal conditional).symm

/-- Lift a state by drawing its auxiliary variable, with the auxiliary placed
first so that the reverse conditional can refresh the state coordinate. -/
noncomputable def auxiliaryFirstLift (forward : Kernel State Aux) :
    Kernel State (Aux × State) :=
  (Kernel.id ×ₖ forward).map Prod.swap

instance auxiliaryFirstLift.instIsMarkovKernel
    (forward : Kernel State Aux) [IsMarkovKernel forward] :
    IsMarkovKernel (auxiliaryFirstLift forward) := by
  unfold auxiliaryFirstLift
  exact ProbabilityTheory.Kernel.IsMarkovKernel.map _ measurable_swap

/-- The two-block auxiliary-variable transition: draw the auxiliary from the
forward conditional, redraw the state from the reverse conditional, and
discard the auxiliary. -/
noncomputable def twoBlockConditional
    (forward : Kernel State Aux) (reverse : Kernel Aux State) :
    Kernel State State :=
  liftEvolveProject (auxiliaryFirstLift forward)
    (refreshSndGivenFst reverse) Prod.snd measurable_snd

instance twoBlockConditional.instIsMarkovKernel
    (forward : Kernel State Aux) (reverse : Kernel Aux State)
    [IsMarkovKernel forward] [IsMarkovKernel reverse] :
    IsMarkovKernel (twoBlockConditional forward reverse) := by
  unfold twoBlockConditional
  infer_instance

/-- The forward augmentation law, written with the auxiliary coordinate
first. -/
noncomputable def auxiliaryFirstJoint
    (target : Measure State) [SFinite target] (forward : Kernel State Aux) :
    Measure (Aux × State) :=
  (target ⊗ₘ forward).map Prod.swap

/-- The lifted target law is exactly the auxiliary-first joint law. -/
theorem auxiliaryFirstLift_comp
    (target : Measure State) [SFinite target]
    (forward : Kernel State Aux) [IsMarkovKernel forward] :
    auxiliaryFirstLift forward ∘ₘ target =
      auxiliaryFirstJoint target forward := by
  rw [auxiliaryFirstLift, auxiliaryFirstJoint,
    ← Measure.map_comp _ _ measurable_swap,
    ← Measure.compProd_eq_comp_prod]

/-- Projecting the auxiliary-first joint back to the state recovers the
original target. -/
theorem auxiliaryFirstJoint_map_snd
    (target : Measure State) [SFinite target]
    (forward : Kernel State Aux) [IsMarkovKernel forward] :
    (auxiliaryFirstJoint target forward).map Prod.snd = target := by
  rw [auxiliaryFirstJoint, Measure.map_map measurable_snd measurable_swap]
  change (target ⊗ₘ forward).fst = target
  exact Measure.fst_compProd target forward

/-- General-state two-block Gibbs/data-augmentation correctness.  The reverse
kernel must factor the same joint law using the auxiliary marginal. -/
theorem twoBlockConditional_invariant
    (target : Measure State) [SFinite target]
    (forward : Kernel State Aux) (reverse : Kernel Aux State)
    [IsMarkovKernel forward] [IsMarkovKernel reverse]
    (hfactor : auxiliaryFirstJoint target forward =
      (forward ∘ₘ target) ⊗ₘ reverse) :
    (twoBlockConditional forward reverse).Invariant target := by
  unfold twoBlockConditional
  apply liftEvolveProject_invariant target
    (auxiliaryFirstJoint target forward)
  · exact auxiliaryFirstLift_comp target forward
  · rw [hfactor]
    exact refreshSndGivenFst_invariant (forward ∘ₘ target) reverse
  · exact auxiliaryFirstJoint_map_snd target forward

/-- Slice sampling is the two-block construction with a vertical height
kernel and a horizontal level-set kernel.  This named wrapper records the
precise factorization obligation a concrete slice implementation must prove. -/
noncomputable def sliceSampler
    (vertical : Kernel State Aux) (horizontal : Kernel Aux State) :
    Kernel State State :=
  twoBlockConditional vertical horizontal

theorem sliceSampler_invariant
    (target : Measure State) [SFinite target]
    (vertical : Kernel State Aux) (horizontal : Kernel Aux State)
    [IsMarkovKernel vertical] [IsMarkovKernel horizontal]
    (hslice : auxiliaryFirstJoint target vertical =
      (vertical ∘ₘ target) ⊗ₘ horizontal) :
    (sliceSampler vertical horizontal).Invariant target := by
  exact twoBlockConditional_invariant target vertical horizontal hslice

end Mcmc.Kernel
