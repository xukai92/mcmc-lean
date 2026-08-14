import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Invariance

/-!
# Lift--evolve--project Markov transitions

This module isolates a common construction in auxiliary-variable MCMC.  A
state is lifted to an extended space, evolved there, and projected back to the
original space.  Target invariance follows from three explicit compatibility
equations: the lift produces the extended target, the evolution preserves it,
and the projection recovers the original target.
-/

open MeasureTheory
open scoped ProbabilityTheory

namespace McmcLean.Kernel

open ProbabilityTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Lift to an auxiliary space, evolve there, and project to the original
state space. -/
noncomputable def liftEvolveProject (lift : Kernel α β)
    (evolve : Kernel β β) (project : β → α) (_hproject : Measurable project) :
    Kernel α α :=
  (evolve ∘ₖ lift).map project

instance liftEvolveProject_isMarkovKernel (lift : Kernel α β)
    (evolve : Kernel β β) (project : β → α)
    (hproject : Measurable project) [IsMarkovKernel lift]
    [IsMarkovKernel evolve] :
    IsMarkovKernel (liftEvolveProject lift evolve project hproject) := by
  unfold liftEvolveProject
  exact ProbabilityTheory.Kernel.IsMarkovKernel.map _ hproject

/-- The abstract invariance theorem for auxiliary-variable MCMC: a compatible
lift followed by an invariant extended-space transition and a compatible
projection preserves the original target. -/
theorem liftEvolveProject_invariant (μ : Measure α) (ν : Measure β)
    (lift : Kernel α β) (evolve : Kernel β β)
    (project : β → α) (hproject : Measurable project)
    (hlift : lift ∘ₘ μ = ν) (hevolve : evolve.Invariant ν)
    (hprojectTarget : ν.map project = μ) :
    (liftEvolveProject lift evolve project hproject).Invariant μ := by
  rw [ProbabilityTheory.Kernel.Invariant]
  unfold liftEvolveProject
  rw [← Measure.map_comp _ _ hproject, ← Measure.comp_assoc, hlift,
    hevolve, hprojectTarget]

/-- Auxiliary-variable specialization for a conditional auxiliary kernel.
The canonical lift `Kernel.id ×ₖ auxiliary` creates the semidirect product
measure, and first projection recovers the original target automatically. -/
theorem compProdEvolveFst_invariant (μ : Measure α) [SFinite μ]
    (auxiliary : Kernel α β) [IsMarkovKernel auxiliary]
    (evolve : Kernel (α × β) (α × β))
    (hevolve : evolve.Invariant (μ ⊗ₘ auxiliary)) :
    (liftEvolveProject (ProbabilityTheory.Kernel.id ×ₖ auxiliary) evolve
      (Prod.fst : α × β → α) measurable_fst).Invariant μ := by
  apply liftEvolveProject_invariant μ (μ ⊗ₘ auxiliary)
  · exact (Measure.compProd_eq_comp_prod μ auxiliary).symm
  · exact hevolve
  · change (μ ⊗ₘ auxiliary).fst = μ
    exact Measure.fst_compProd μ auxiliary

/-- A measurable deterministic map that preserves a measure defines an
invariant deterministic kernel. -/
theorem deterministic_invariant_of_measurePreserving (ν : Measure β)
    {f : β → β} (hf : Measurable f) (hpres : MeasurePreserving f ν ν) :
    (ProbabilityTheory.Kernel.deterministic f hf).Invariant ν := by
  rw [ProbabilityTheory.Kernel.Invariant,
    Measure.deterministic_comp_eq_map hf]
  exact hpres.map_eq

/-- The lift--flow--project specialization used by idealized Hamiltonian Monte
Carlo: a measure-preserving measurable phase-space map may be used as the
extended-space evolution. -/
theorem liftDeterministicProject_invariant (μ : Measure α) (ν : Measure β)
    (lift : Kernel α β) {flow : β → β} (hflow : Measurable flow)
    (project : β → α) (hproject : Measurable project)
    (hlift : lift ∘ₘ μ = ν) (hpres : MeasurePreserving flow ν ν)
    (hprojectTarget : ν.map project = μ) :
    (liftEvolveProject lift
      (ProbabilityTheory.Kernel.deterministic flow hflow)
      project hproject).Invariant μ := by
  exact liftEvolveProject_invariant μ ν lift _ project hproject hlift
    (deterministic_invariant_of_measurePreserving ν hflow hpres)
    hprojectTarget

end McmcLean.Kernel
