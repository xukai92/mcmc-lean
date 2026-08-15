import Mcmc.Finite.SequentialMonteCarlo

/-!
# A fully state-indexed finite PMMH example

This example uses two parameter values whose one-step SMC models have both
different potentials and different transitions. It demonstrates that the
state-indexed PMMH theorem is not merely the shared-schedule construction with
a state-dependent initial distribution.
-/

namespace Mcmc.Examples.StateIndexedPMMH

open Mcmc.Finite
open Mcmc.Finite.MarkovKernel
open Mcmc.Finite.ParticleEstimator
open Mcmc.Finite.SequentialMonteCarlo

/-- Uniform law on the two-point sample or parameter space. -/
noncomputable def uniformBool : Distribution Bool where
  mass _ := (1 : ℝ) / 2
  nonneg _ := by norm_num
  sum_mass := by norm_num [Fintype.sum_bool]

/-- The identity transition on `Bool`. -/
def stay : MarkovKernel Bool where
  prob x y := if y = x then 1 else 0
  nonneg x y := by split <;> norm_num
  sum_prob x := by cases x <;> simp

/-- The deterministic bit-flip transition. -/
def flip : MarkovKernel Bool where
  prob x y := if y = !x then 1 else 0
  nonneg x y := by split <;> norm_num
  sum_prob x := by cases x <;> simp

/-- A parameter-specific Feynman--Kac step. At `true` the potential is two
and propagation stays put; at `false` the potential is three and propagation
flips the bit. -/
def step (parameter : Bool) : FeynmanKacStep Bool where
  potential _ := if parameter then 2 else 3
  potential_pos x := by cases parameter <;> norm_num
  transition := if parameter then stay else flip

/-- A common one-step horizon with genuinely parameter-dependent contents. -/
def schedule : StateIndexedSchedule (State := Bool) (Sample := Bool) := [step]

theorem schedule_is_genuinely_state_indexed :
    stepsAt schedule true ≠ stepsAt schedule false := by
  intro h
  have hpotential := congrArg
    (fun steps : List (FeynmanKacStep Bool) =>
      match steps with
      | first :: _ => first.potential true
      | [] => 0) h
  norm_num [schedule, stepsAt, step] at hpotential

theorem normalizer_positive (parameter : Bool) :
    0 < normalizingConstant uniformBool (stepsAt schedule parameter) := by
  cases parameter <;>
    norm_num [normalizingConstant, schedule, stepsAt, step,
      feynmanKacSequence, feynmanKacTransform, uniformBool, stay, flip,
      Fintype.sum_bool]

/-- The concrete fully state-indexed PMMH kernel has exactly the uniform
parameter marginal at stationarity. -/
example (parameter : Bool) :
    ∑ selected, (PseudoMarginal.extendedTarget uniformBool
      (stateIndexedPmmhEstimator (Particle := Bool)
        (fun _ => uniformBool) schedule normalizer_positive)).mass
        (parameter, selected) = uniformBool.mass parameter :=
  stateIndexedPmmhKernel_state_marginal (Particle := Bool) uniformBool
    (fun _ => uniformBool) schedule normalizer_positive parameter

end Mcmc.Examples.StateIndexedPMMH
