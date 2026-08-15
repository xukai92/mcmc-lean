import Mcmc.Finite.Combinators
import Mathlib.Tactic

/-!
# A finite adaptive-kernel boundary

State-dependent selection from a family of Markov kernels is again a Markov
kernel.  The example below records an important adaptive-MCMC warning: even
when every frozen member preserves the same target, selecting the member from
the current state need not preserve that target.
-/

open scoped BigOperators

namespace Mcmc.Finite

/-- Select a transition kernel as a function of the current state. -/
def selectByState {State Parameter : Type*} [Fintype State]
    (choose : State → Parameter) (family : Parameter → MarkovKernel State) :
    MarkovKernel State where
  prob x y := (family (choose x)).prob x y
  nonneg x y := (family (choose x)).nonneg x y
  sum_prob x := (family (choose x)).sum_prob x

namespace AdaptiveCounterexample

/-- The uniform distribution on two states. -/
noncomputable def uniformBool : MarkovKernel.Distribution Bool where
  mass _ := 1 / 2
  nonneg _ := by norm_num
  sum_mass := by norm_num

/-- A frozen kernel that leaves its input unchanged. -/
def stay : MarkovKernel Bool := MarkovKernel.identity

/-- A frozen kernel that flips its input. -/
def flip : MarkovKernel Bool where
  prob x y := if y = !x then 1 else 0
  nonneg x y := by split_ifs <;> norm_num
  sum_prob x := by cases x <;> simp

theorem stay_stationary : stay.Stationary uniformBool := by
  exact MarkovKernel.identity_stationary uniformBool

theorem flip_stationary : flip.Stationary uniformBool := by
  intro y
  cases y <;> norm_num [uniformBool, flip]

/-- At `false` choose the identity kernel; at `true` choose the flip kernel. -/
def selected : MarkovKernel Bool :=
  selectByState (fun x => x) (fun useFlip => if useFlip then flip else stay)

/-- State-dependent selection can destroy a common stationary distribution.
Both rows of `selected` send all mass to `false`. -/
theorem selected_not_stationary : ¬ selected.Stationary uniformBool := by
  intro h
  have htrue := h true
  norm_num [selected, selectByState, uniformBool, stay, flip,
    MarkovKernel.identity] at htrue

end AdaptiveCounterexample
end Mcmc.Finite
