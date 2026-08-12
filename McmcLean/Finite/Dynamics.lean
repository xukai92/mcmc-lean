import McmcLean.Finite.MatrixKernel
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# One-step finite Markov-chain dynamics

This file defines the evolution of a finite distribution by one transition
kernel.  It proves that evolution preserves normalization, agrees with
row-vector multiplication, and characterizes stationary distributions as
fixed points of the evolution operation.
-/

open scoped BigOperators ENNReal Matrix

namespace McmcLean.Finite
namespace MarkovKernel

variable {State : Type*} [Fintype State]

namespace Distribution

/-- Evolve a finite distribution by one step of a Markov kernel. -/
def evolve (π : Distribution State) (P : MarkovKernel State) : Distribution State where
  mass y := ∑ x, π.mass x * P.prob x y
  nonneg y := Finset.sum_nonneg fun x _ => mul_nonneg (π.nonneg x) (P.nonneg x y)
  sum_mass := by
    rw [Finset.sum_comm]
    calc
      ∑ x, ∑ y, π.mass x * P.prob x y =
          ∑ x, π.mass x * ∑ y, P.prob x y := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
      _ = ∑ x, π.mass x := by simp only [P.sum_prob, mul_one]
      _ = 1 := π.sum_mass

@[simp]
theorem evolve_mass (π : Distribution State) (P : MarkovKernel State) (y : State) :
    (π.evolve P).mass y = ∑ x, π.mass x * P.prob x y :=
  rfl

/-- One-step evolution is multiplication of the distribution row vector by
the transition matrix. -/
theorem evolve_mass_eq_vecMul (π : Distribution State) (P : MarkovKernel State) :
    (π.evolve P).mass = π.mass ᵥ* P.toMatrix := by
  funext y
  rfl

/-- The PMF view of one-step evolution is monadic bind by the kernel rows. -/
theorem evolve_toPMF (π : Distribution State) (P : MarkovKernel State) :
    (π.evolve P).toPMF = π.toPMF.bind P.rowPMF := by
  ext y
  rw [PMF.bind_apply, tsum_fintype]
  simp only [toPMF_apply, rowPMF_apply, evolve_mass]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro x _
    rw [ENNReal.ofReal_mul (π.nonneg x)]
  · exact fun x _ => mul_nonneg (π.nonneg x) (P.nonneg x y)

end Distribution

/-- A distribution is stationary exactly when one-step evolution fixes it. -/
theorem stationary_iff_evolve_eq (P : MarkovKernel State) (π : Distribution State) :
    P.Stationary π ↔ π.evolve P = π := by
  constructor
  · intro h
    apply Distribution.ext
    funext y
    exact h y
  · intro h y
    exact congrFun (congrArg Distribution.mass h) y

/-- A stationary distribution is unchanged by one transition step. -/
theorem Stationary.evolve_eq {P : MarkovKernel State} {π : Distribution State}
    (h : P.Stationary π) :
    π.evolve P = π :=
  (stationary_iff_evolve_eq P π).mp h

end MarkovKernel
end McmcLean.Finite
