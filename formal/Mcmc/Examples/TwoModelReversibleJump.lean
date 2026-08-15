import Mcmc.Kernel.ReversibleJump

/-!
# A two-model reversible-jump example

Each model has one state and the proposal always changes model. The example
is deliberately periodic: it demonstrates tagged cross-model correctness and
rejection-free transport, not convergence from arbitrary starts.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace Mcmc.Examples.TwoModelReversibleJump

open ProbabilityTheory Mcmc.Kernel

abbrev State := Unit ⊕ Unit

instance : MeasurableSingletonClass State where
  measurableSet_singleton x := by
    rw [measurableSet_sum_iff]
    cases x <;> simp

noncomputable def reference : Measure State :=
  twoModelReference (Measure.dirac ()) (Measure.dirac ())

noncomputable def weight (_ : State) : ENNReal := 2⁻¹

def switchDensity : State → State → ENNReal
  | Sum.inl _, Sum.inr _ => 1
  | Sum.inr _, Sum.inl _ => 1
  | _, _ => 0

theorem measurable_weight : Measurable weight := measurable_of_finite _

theorem measurable_uncurry_switchDensity :
    Measurable (Function.uncurry switchDensity) := by
  exact measurable_of_finite _

theorem switchDensity_normalized (x : State) :
    ∫⁻ y, switchDensity x y ∂reference = 1 := by
  cases x <;>
    simp [reference, twoModelReference, Measure.map_dirac' measurable_inl,
      Measure.map_dirac' measurable_inr, switchDensity]

noncomputable def spec : ReversibleJumpSpec reference weight where
  proposalDensity := switchDensity
  measurableProposal := measurable_uncurry_switchDensity
  normalized := switchDensity_normalized
  finiteFlow := by
    intro x y
    cases x <;> cases y <;> simp [forwardDensityFlow, weight, switchDensity]

/-- The alternating two-model chain preserves the equal-mass tagged target. -/
theorem invariant :
    (reversibleJumpMetropolisHastings reference weight spec).Invariant
      (densityTarget reference weight) :=
  reversibleJumpMetropolisHastings_invariant reference weight measurable_weight spec

end Mcmc.Examples.TwoModelReversibleJump
