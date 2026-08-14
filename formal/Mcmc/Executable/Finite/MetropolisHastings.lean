import Mcmc.Executable.Finite.Categorical

/-!
# Executable finite Metropolis--Hastings

This module implements a finite MH step using natural weights only.  Proposal
selection is cumulative.  The acceptance comparison cross-multiplies target
and proposal weights, so execution performs no division or floating-point
arithmetic.
-/

namespace Mcmc.Executable.Finite

/-- A proposal matrix represented by one positive-total weight vector per row. -/
structure NatKernelWeights (n : ℕ) where
  row : Fin n → NatWeights n

/-- A target whose atoms are all strictly positive, as required by the local
finite MH correctness theorem. -/
structure PositiveNatWeights (n : ℕ) extends NatWeights n where
  weight_pos : ∀ i, 0 < weight i

namespace NatKernelWeights

/-- Real-valued kernel realization used by the existing finite theory. -/
noncomputable def toKernel {n : ℕ} (proposal : NatKernelWeights n) :
    Mcmc.Finite.MarkovKernel (Fin n) where
  prob x y := (proposal.row x).toDistribution.mass y
  nonneg x y := (proposal.row x).toDistribution.nonneg y
  sum_prob x := (proposal.row x).toDistribution.sum_mass

/-- Denominator of the exact MH acceptance comparison for a proposal `x → y`. -/
def acceptanceUpper {n : ℕ} (target : PositiveNatWeights n)
    (proposal : NatKernelWeights n) (x y : Fin n) : ℕ :=
  target.weight x * (proposal.row x).weight y * (proposal.row y).total

/-- Numerator, capped by the denominator, of the exact MH acceptance comparison. -/
def acceptanceThreshold {n : ℕ} (target : PositiveNatWeights n)
    (proposal : NatKernelWeights n) (x y : Fin n) : ℕ :=
  min (acceptanceUpper target proposal x y)
    (target.weight y * (proposal.row y).weight x * (proposal.row x).total)

end NatKernelWeights

theorem PositiveNatWeights.toDistribution_positive {n : ℕ}
    (target : PositiveNatWeights n) (i : Fin n) :
    0 < target.toNatWeights.toDistribution.mass i := by
  rw [NatWeights.toDistribution_mass]
  exact div_pos (by exact_mod_cast target.weight_pos i)
    (by exact_mod_cast target.total_pos)

/-- Replay one exact finite MH transition.  A self-proposal returns immediately;
an off-diagonal proposal consumes a second bounded draw for acceptance. -/
def replayMHStep {n : ℕ} (target : PositiveNatWeights n)
    (proposal : NatKernelWeights n) (current : Fin n)
    (trace : List DrawEvent) : Except ExecError (Fin n × List DrawEvent) := do
  let proposalResult ← replayCategorical (proposal.row current) trace
  let proposed := proposalResult.1
  if proposed = current then
    return (current, proposalResult.2)
  let upper := proposal.acceptanceUpper target current proposed
  let acceptResult ← replayDraw upper proposalResult.2
  if acceptResult.value < proposal.acceptanceThreshold target current proposed then
    return (proposed, acceptResult.remaining)
  else
    return (current, acceptResult.remaining)

end Mcmc.Executable.Finite
