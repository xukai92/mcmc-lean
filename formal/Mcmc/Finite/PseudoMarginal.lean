import Mcmc.Finite.MetropolisHastings
import Mathlib.Tactic

/-!
# Finite pseudo-marginal Metropolis--Hastings

A nonnegative unbiased estimator defines an extended target whose state
marginal is the desired target.  Ordinary MH on that extended space retains
the current estimator on rejection.  Zero estimator values are supported by
the zero-safe finite MH constructor.
!-/

open scoped BigOperators

namespace Mcmc.Finite.PseudoMarginal

open MarkovKernel

variable {State Weight : Type*} [Fintype State] [Fintype Weight]
  [DecidableEq State] [DecidableEq Weight]

/-- Finite nonnegative unbiased likelihood/target estimator data. -/
structure Estimator (State Weight : Type*) [Fintype State] [Fintype Weight] where
  law : State → Distribution Weight
  value : State → Weight → ℝ
  nonneg : ∀ x w, 0 ≤ value x w
  unbiased : ∀ x, ∑ w, (law x).mass w * value x w = 1

/-- The standard pseudo-marginal extended target. -/
def extendedTarget (target : Distribution State) (estimator : Estimator State Weight) :
    Distribution (State × Weight) where
  mass xw := target.mass xw.1 * (estimator.law xw.1).mass xw.2 *
    estimator.value xw.1 xw.2
  nonneg xw := mul_nonneg
    (mul_nonneg (target.nonneg xw.1) ((estimator.law xw.1).nonneg xw.2))
    (estimator.nonneg xw.1 xw.2)
  sum_mass := by
    rw [Fintype.sum_prod_type]
    simp_rw [show ∀ x w, target.mass x * (estimator.law x).mass w * estimator.value x w =
        target.mass x * ((estimator.law x).mass w * estimator.value x w) by
      intro x w; ring]
    simp_rw [← Finset.mul_sum, estimator.unbiased, mul_one]
    exact target.sum_mass

omit [DecidableEq State] [DecidableEq Weight] in
/-- The extended target has exactly the desired state marginal. -/
theorem state_marginal (target : Distribution State)
    (estimator : Estimator State Weight) (x : State) :
    ∑ w, (extendedTarget target estimator).mass (x, w) = target.mass x := by
  simp only [extendedTarget]
  rw [show (∑ w, target.mass x * (estimator.law x).mass w * estimator.value x w) =
      target.mass x * ∑ w, (estimator.law x).mass w * estimator.value x w by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    ring,
    estimator.unbiased x, mul_one]

/-- Propose a new state and then draw a fresh estimator at that proposal. -/
def extendedProposal (proposal : MarkovKernel State)
    (estimator : Estimator State Weight) : MarkovKernel (State × Weight) where
  prob current proposed := proposal.prob current.1 proposed.1 *
    (estimator.law proposed.1).mass proposed.2
  nonneg current proposed := mul_nonneg (proposal.nonneg current.1 proposed.1)
    ((estimator.law proposed.1).nonneg proposed.2)
  sum_prob current := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, (estimator.law _).sum_mass, mul_one]
    exact proposal.sum_prob current.1

/-- Pseudo-marginal MH on the extended state.  Rejection retains both the
state and its current estimator value. -/
noncomputable def kernel (target : Distribution State)
    (estimator : Estimator State Weight) (proposal : MarkovKernel State) :
    MarkovKernel (State × Weight) :=
  MetropolisHastings.kernelAllowZeros (extendedTarget target estimator)
    (extendedProposal proposal estimator)

theorem detailed_balance (target : Distribution State)
    (estimator : Estimator State Weight) (proposal : MarkovKernel State) :
    (kernel target estimator proposal).Reversible (extendedTarget target estimator) :=
  MetropolisHastings.detailed_balance_allowZeros _ _

/-- Exact extended-target stationarity of finite pseudo-marginal MH. -/
theorem stationary (target : Distribution State)
    (estimator : Estimator State Weight) (proposal : MarkovKernel State) :
    (kernel target estimator proposal).Stationary (extendedTarget target estimator) :=
  MetropolisHastings.stationary_allowZeros _ _

end Mcmc.Finite.PseudoMarginal
