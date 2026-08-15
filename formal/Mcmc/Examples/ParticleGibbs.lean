import Mcmc.Finite.SequentialMonteCarlo

/-!
# A finite particle-Gibbs example

The zero-transition Feynman--Kac model already exercises conditional history
refresh and terminal-index reselection: its selected trajectory is a singleton
with exactly the initial target law.
-/

namespace Mcmc.Examples.ParticleGibbs

open Mcmc.Finite
open Mcmc.Finite.MarkovKernel
open Mcmc.Finite.ParticleEstimator
open Mcmc.Finite.SequentialMonteCarlo

noncomputable def initial : Distribution Bool where
  mass x := if x then (2 : ℝ) / 3 else 1 / 3
  nonneg x := by cases x <;> norm_num
  sum_mass := by norm_num [Fintype.sum_bool]

theorem normalizer_positive :
    0 < normalizingConstant initial ([] : List (FeynmanKacStep Bool)) := by
  norm_num [normalizingConstant, feynmanKacSequence, initial, Fintype.sum_bool]

/-- The concrete two-particle Gibbs kernel preserves its selected-particle
extended target. -/
example :
    (particleGibbsKernel (Particle := Bool) initial []
      normalizer_positive).Stationary
      (selectedParticleTarget (Particle := Bool) initial [] normalizer_positive) :=
  particleGibbsKernel_stationary (Particle := Bool) initial [] normalizer_positive

/-- Its stationary selected singleton has the requested Boolean expectation. -/
example (observable : List Bool → ℝ) :
    ∑ selected, (selectedParticleTarget (Particle := Bool) initial []
        normalizer_positive).mass selected *
      observable (selectedTrajectory [] selected.1.1 selected.1.2 selected.2) =
      ∑ x, initial.mass x * observable [x] := by
  rw [particleGibbs_stationary_selectedTrajectory_expectation
    (Particle := Bool) initial [] normalizer_positive observable]
  norm_num [normalizingConstant, pathFeynmanKacValue, labeledFeynmanKacValue,
    feynmanKacSequence, initial, Fintype.sum_bool]

end Mcmc.Examples.ParticleGibbs
