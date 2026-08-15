import Mcmc.Finite.MarkovKernel
import Mathlib.Tactic

/-!
# Minimal finite probabilistic-program semantics

This is the mathematical trace/factor core needed to state the composable
inference architecture of Ge, Xu, and Ghahramani (2018). A full assignment is
drawn from a prior (`assume`), and each `observe` contributes a nonnegative
factor. Normalizing the resulting finite weight gives the posterior target on
which scoped inference operators act.

This module does not model Julia coroutines, copying, automatic
differentiation, or a source-language compiler.
-/

open scoped BigOperators

namespace Mcmc.Finite.ProbabilisticProgram

open MarkovKernel

variable {State : Type*} [Fintype State]

/-- A nonnegative likelihood or score contributed by one observation. -/
structure Factor (State : Type*) where
  weight : State → ℝ
  nonneg : ∀ state, 0 ≤ weight state

/-- A finite model consists of an `assume` law and an ordered collection of
observation factors. -/
structure Model (State : Type*) [Fintype State] where
  prior : Distribution State
  observations : List (Factor State)

/-- Product of all observation factors along a completed trace. -/
def Model.traceWeight (model : Model State) (state : State) : ℝ :=
  (model.observations.map fun factor => factor.weight state).prod

theorem Model.traceWeight_nonneg (model : Model State) (state : State) :
    0 ≤ model.traceWeight state := by
  exact List.prod_nonneg fun factor hfactor => by
    simpa using (List.mem_map.mp hfactor).choose_spec.2 ▸
      (List.mem_map.mp hfactor).choose.nonneg state

/-- Unnormalized posterior mass of one completed execution trace. -/
def Model.unnormalizedMass (model : Model State) (state : State) : ℝ :=
  model.prior.mass state * model.traceWeight state

theorem Model.unnormalizedMass_nonneg (model : Model State) (state : State) :
    0 ≤ model.unnormalizedMass state :=
  mul_nonneg (model.prior.nonneg state) (model.traceWeight_nonneg state)

/-- Model evidence / normalizing constant. -/
def Model.evidence (model : Model State) : ℝ :=
  ∑ state, model.unnormalizedMass state

theorem Model.evidence_nonneg (model : Model State) :
    0 ≤ model.evidence :=
  Finset.sum_nonneg fun state _ => model.unnormalizedMass_nonneg state

/-- Add one `observe` statement to the trace semantics. -/
def Model.observe (model : Model State) (factor : Factor State) : Model State :=
  { model with observations := model.observations ++ [factor] }

@[simp] theorem Model.traceWeight_observe (model : Model State)
    (factor : Factor State) (state : State) :
    (model.observe factor).traceWeight state =
      model.traceWeight state * factor.weight state := by
  simp [Model.observe, Model.traceWeight]

@[simp] theorem Model.unnormalizedMass_observe (model : Model State)
    (factor : Factor State) (state : State) :
    (model.observe factor).unnormalizedMass state =
      model.unnormalizedMass state * factor.weight state := by
  rw [Model.unnormalizedMass, Model.traceWeight_observe,
    Model.unnormalizedMass]
  change model.prior.mass state *
      (model.traceWeight state * factor.weight state) = _
  ring

/-- Normalized posterior semantics, requiring explicitly that the evidence is
positive. -/
noncomputable def Model.posterior (model : Model State)
    (hpositive : 0 < model.evidence) : Distribution State where
  mass state := model.unnormalizedMass state / model.evidence
  nonneg state := div_nonneg (model.unnormalizedMass_nonneg state)
    model.evidence_nonneg
  sum_mass := by
    rw [← Finset.sum_div, show (∑ state, model.unnormalizedMass state) =
      model.evidence by rfl, div_self (ne_of_gt hpositive)]

@[simp] theorem Model.posterior_mass (model : Model State)
    (hpositive : 0 < model.evidence) (state : State) :
    (model.posterior hpositive).mass state =
      model.unnormalizedMass state / model.evidence := rfl

/-- With no observations, probabilistic-program semantics reduces exactly to
the `assume` distribution. -/
@[simp] theorem Model.posterior_no_observations (prior : Distribution State) :
    let model : Model State := ⟨prior, []⟩
    model.posterior (by
      change 0 < ∑ state, prior.mass state * 1
      simp [prior.sum_mass]) = prior := by
  dsimp
  apply Distribution.ext
  funext state
  simp [Model.posterior, Model.evidence, Model.unnormalizedMass,
    Model.traceWeight, prior.sum_mass]

end Mcmc.Finite.ProbabilisticProgram
