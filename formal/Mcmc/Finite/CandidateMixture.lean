import Mcmc.Finite.Dynamics

/-!
# Finite candidate selection

Candidate-based samplers generate several possible transitions and select one.
The theorem here covers the exact case in which the candidate index is drawn
from a state-independent finite law and every candidate kernel preserves the
same target. It is useful for static trajectory mixtures, but deliberately
does not claim correctness of dynamic NUTS tree construction or stopping.
-/

open scoped BigOperators

namespace Mcmc.Finite.MarkovKernel

variable {State Candidate : Type*} [Fintype State] [Fintype Candidate]

/-- Select a transition kernel using a state-independent finite candidate
law. -/
def candidateMixture (selection : Distribution Candidate)
    (candidate : Candidate → MarkovKernel State) : MarkovKernel State where
  prob x y := ∑ index, selection.mass index * (candidate index).prob x y
  nonneg x y := Finset.sum_nonneg fun index _ =>
    mul_nonneg (selection.nonneg index) ((candidate index).nonneg x y)
  sum_prob x := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (candidate _).sum_prob, mul_one]
    exact selection.sum_mass

/-- A state-independent mixture of common-target stationary candidates is
stationary. -/
theorem candidateMixture_stationary (selection : Distribution Candidate)
    (candidate : Candidate → MarkovKernel State)
    (target : Distribution State)
    (hstationary : ∀ index, (candidate index).Stationary target) :
    (candidateMixture selection candidate).Stationary target := by
  intro y
  rw [show (∑ x, target.mass x *
      (candidateMixture selection candidate).prob x y) =
      ∑ index, selection.mass index *
        (∑ x, target.mass x * (candidate index).prob x y) by
    simp only [candidateMixture, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro index _
    apply Finset.sum_congr rfl
    intro x _
    ring]
  calc
    ∑ index, selection.mass index *
        (∑ x, target.mass x * (candidate index).prob x y) =
        ∑ index, selection.mass index * target.mass y := by
      apply Finset.sum_congr rfl
      intro index _
      rw [hstationary index y]
    _ = target.mass y := by
      rw [← Finset.sum_mul, selection.sum_mass, one_mul]

end Mcmc.Finite.MarkovKernel
