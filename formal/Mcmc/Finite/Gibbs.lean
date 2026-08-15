import Mcmc.Finite.Combinators
import Mathlib.Tactic

/-!
# Finite Gibbs kernels

Coordinate updates are specified by normalized conditional kernels.  Their
slice-invariance equations imply invariance of the joint target.  We provide
one-site, random-scan, and systematic-scan correctness theorems.
!-/

open scoped BigOperators

namespace Mcmc.Finite.Gibbs

open MarkovKernel

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- A first-coordinate conditional update preserves every target slice. -/
def PreservesFstSlices (π : Distribution (α × β))
    (update : β → MarkovKernel α) : Prop :=
  ∀ b a', ∑ a, π.mass (a, b) * (update b).prob a a' = π.mass (a', b)

/-- A second-coordinate conditional update preserves every target slice. -/
def PreservesSndSlices (π : Distribution (α × β))
    (update : α → MarkovKernel β) : Prop :=
  ∀ a b', ∑ b, π.mass (a, b) * (update a).prob b b' = π.mass (a, b')

omit [DecidableEq α] in
theorem liftFst_stationary (π : Distribution (α × β))
    (update : β → MarkovKernel α) (h : PreservesFstSlices π update) :
    (liftFst update).Stationary π := by
  rintro ⟨a', b'⟩
  rw [Fintype.sum_prod_type]
  simp only [liftFst]
  simp [h b' a']

omit [DecidableEq β] in
theorem liftSnd_stationary (π : Distribution (α × β))
    (update : α → MarkovKernel β) (h : PreservesSndSlices π update) :
    (liftSnd update).Stationary π := by
  rintro ⟨a', b'⟩
  rw [Fintype.sum_prod_type]
  simp only [liftSnd]
  simp [h a' b']

/-- Random-scan two-coordinate Gibbs. -/
noncomputable def randomScan (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (fstUpdate : β → MarkovKernel α) (sndUpdate : α → MarkovKernel β) :
    MarkovKernel (α × β) :=
  mixture p hp0 hp1 (liftFst fstUpdate) (liftSnd sndUpdate)

theorem randomScan_stationary (π : Distribution (α × β))
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (fstUpdate : β → MarkovKernel α) (sndUpdate : α → MarkovKernel β)
    (hfst : PreservesFstSlices π fstUpdate)
    (hsnd : PreservesSndSlices π sndUpdate) :
    (randomScan p hp0 hp1 fstUpdate sndUpdate).Stationary π :=
  mixture_stationary p hp0 hp1 _ _ π
    (liftFst_stationary π fstUpdate hfst)
    (liftSnd_stationary π sndUpdate hsnd)

/-- Systematic scan: update the first coordinate, then the second. -/
def systematicScan (fstUpdate : β → MarkovKernel α)
    (sndUpdate : α → MarkovKernel β) : MarkovKernel (α × β) :=
  comp (liftSnd sndUpdate) (liftFst fstUpdate)

theorem systematicScan_stationary (π : Distribution (α × β))
    (fstUpdate : β → MarkovKernel α) (sndUpdate : α → MarkovKernel β)
    (hfst : PreservesFstSlices π fstUpdate)
    (hsnd : PreservesSndSlices π sndUpdate) :
    (systematicScan fstUpdate sndUpdate).Stationary π :=
  comp_stationary _ _ π (liftFst_stationary π fstUpdate hfst)
    (liftSnd_stationary π sndUpdate hsnd)

/-- Independent product of finite distributions. -/
def productDistribution (left : Distribution α) (right : Distribution β) :
    Distribution (α × β) where
  mass x := left.mass x.1 * right.mass x.2
  nonneg x := mul_nonneg (left.nonneg x.1) (right.nonneg x.2)
  sum_mass := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, right.sum_mass, mul_one]
    exact left.sum_mass

omit [DecidableEq α] [DecidableEq β] in
/-- A stationary update of the first factor preserves the corresponding
product target, providing a concrete reusable Gibbs example. -/
theorem preservesFstSlices_product (left : Distribution α)
    (right : Distribution β) (kernel : MarkovKernel α)
    (hkernel : kernel.Stationary left) :
    PreservesFstSlices (productDistribution left right) (fun _ => kernel) := by
  intro b a'
  simp only [productDistribution]
  rw [show (∑ a, left.mass a * right.mass b * kernel.prob a a') =
      (∑ a, left.mass a * kernel.prob a a') * right.mass b by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    ring,
    hkernel a']

omit [DecidableEq α] [DecidableEq β] in
/-- Symmetric second-factor version of `preservesFstSlices_product`. -/
theorem preservesSndSlices_product (left : Distribution α)
    (right : Distribution β) (kernel : MarkovKernel β)
    (hkernel : kernel.Stationary right) :
    PreservesSndSlices (productDistribution left right) (fun _ => kernel) := by
  intro a b'
  simp only [productDistribution]
  rw [show (∑ b, left.mass a * right.mass b * kernel.prob b b') =
      left.mass a * (∑ b, right.mass b * kernel.prob b b') by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring,
    hkernel b']

end Mcmc.Finite.Gibbs
