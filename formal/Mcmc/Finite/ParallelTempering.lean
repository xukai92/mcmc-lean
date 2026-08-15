import Mcmc.Finite.Gibbs
import Mcmc.Finite.MetropolisHastings

/-!
# Finite parallel tempering

Two invariant within-temperature updates are followed by a Metropolis--
Hastings transposition proposal.  The product-temperature target is invariant,
and its first (cold) marginal is the requested cold distribution.
!-/

open scoped BigOperators

namespace Mcmc.Finite.ParallelTempering

open MarkovKernel Gibbs

variable {State : Type*} [Fintype State] [DecidableEq State]

/-- Deterministically propose exchanging the two replicas. -/
def swapProposal : MarkovKernel (State × State) where
  prob x y := if y = (x.2, x.1) then 1 else 0
  nonneg x y := by split_ifs <;> positivity
  sum_prob x := by simp

/-- Independent within-temperature updates of both replicas. -/
def within (coldKernel hotKernel : MarkovKernel State) :
    MarkovKernel (State × State) :=
  comp (liftSnd (fun _ => hotKernel)) (liftFst (fun _ => coldKernel))

theorem within_stationary (cold hot : Distribution State)
    (coldKernel hotKernel : MarkovKernel State)
    (hcold : coldKernel.Stationary cold)
    (hhot : hotKernel.Stationary hot) :
    (within coldKernel hotKernel).Stationary (productDistribution cold hot) := by
  apply systematicScan_stationary
  · exact preservesFstSlices_product cold hot coldKernel hcold
  · intro a b'
    simp only [productDistribution]
    rw [show (∑ b, cold.mass a * hot.mass b * hotKernel.prob b b') =
        cold.mass a * ∑ b, hot.mass b * hotKernel.prob b b' by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring,
      hhot b']

/-- Swap correction for the product-temperature target. -/
noncomputable def swapKernel (cold hot : Distribution State)
    (hpositive : ∀ x, 0 < (productDistribution cold hot).mass x) :
    MarkovKernel (State × State) :=
  MetropolisHastings.kernel (productDistribution cold hot) swapProposal hpositive

/-- One parallel-tempering sweep: within updates followed by an MH swap. -/
noncomputable def kernel (cold hot : Distribution State)
    (coldKernel hotKernel : MarkovKernel State)
    (hpositive : ∀ x, 0 < (productDistribution cold hot).mass x) :
    MarkovKernel (State × State) :=
  comp (swapKernel cold hot hpositive) (within coldKernel hotKernel)

theorem stationary (cold hot : Distribution State)
    (coldKernel hotKernel : MarkovKernel State)
    (hcold : coldKernel.Stationary cold) (hhot : hotKernel.Stationary hot)
    (hpositive : ∀ x, 0 < (productDistribution cold hot).mass x) :
    (kernel cold hot coldKernel hotKernel hpositive).Stationary
      (productDistribution cold hot) :=
  comp_stationary _ _ _ (within_stationary cold hot coldKernel hotKernel hcold hhot)
    (MetropolisHastings.stationary _ _ hpositive)

omit [DecidableEq State] in
/-- The first marginal of the invariant product target is exactly the cold
target. -/
theorem cold_marginal (cold hot : Distribution State) (x : State) :
    ∑ y, (productDistribution cold hot).mass (x, y) = cold.mass x := by
  simp only [productDistribution, ← Finset.mul_sum, hot.sum_mass, mul_one]

end Mcmc.Finite.ParallelTempering
