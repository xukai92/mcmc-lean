import Mcmc.Hamiltonian.HMC
import Mcmc.Kernel.ConstrainedTransform

/-!
# Transport-map Hamiltonian Monte Carlo

An invertible measurable map sends the original target to latent coordinates,
where an ordinary HMC kernel evolves it, and its inverse returns the result to
the original coordinates.  The Jacobian is not an extra transition correction:
it belongs in the proof that the latent Boltzmann density is the pushforward of
the original target.
-/

open MeasureTheory
open scoped ProbabilityTheory

namespace Mcmc.Hamiltonian

open ProbabilityTheory Mcmc.Kernel

variable {Original : Type*} [MeasurableSpace Original]
variable {ι : Type*} [Fintype ι]

/-- Run a position-space HMC kernel in coordinates supplied by `transport` and
map its output back to the original state space. -/
noncomputable def transportHMC
    (transport : Original ≃ Position ι)
    (htransport : Measurable transport)
    (hinverse : Measurable transport.symm)
    (transition : Kernel (Position ι) (Position ι)) :
    Kernel Original Original :=
  transformedKernel transport htransport hinverse transition

instance transportHMC_isMarkovKernel
    (transport : Original ≃ Position ι)
    (htransport : Measurable transport)
    (hinverse : Measurable transport.symm)
    (transition : Kernel (Position ι) (Position ι))
    [IsMarkovKernel transition] :
    IsMarkovKernel (transportHMC transport htransport hinverse transition) := by
  unfold transportHMC
  infer_instance

omit [Fintype ι] in
/-- Transport HMC preserves the original target whenever its latent kernel
preserves the exact pushforward target. -/
theorem transportHMC_invariant
    (target : Measure Original)
    (transport : Original ≃ Position ι)
    (htransport : Measurable transport)
    (hinverse : Measurable transport.symm)
    (transition : Kernel (Position ι) (Position ι))
    (hinvariant : transition.Invariant (target.map transport)) :
    (transportHMC transport htransport hinverse transition).Invariant target := by
  exact transformedKernel_invariant target transport htransport hinverse
    transition hinvariant

/-- Concrete multinomial-HMC client.  `hpushforward` is precisely the
change-of-variables obligation: in a density presentation it includes the
absolute Jacobian determinant of `transport.symm`. -/
theorem transportMultinomialHMC_invariant
    (target : Measure Original)
    (transport : Original ≃ Position ι)
    (htransport : Measurable transport)
    (hinverse : Measurable transport.symm)
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) (L : ℕ)
    (hpushforward : target.map transport = positionBoltzmannTarget potential) :
    (transportHMC transport htransport hinverse
      (standardPositionMultinomialHMC potential gradient ε L
        hpotential hgradient)).Invariant target := by
  apply transportHMC_invariant target transport htransport hinverse
  rw [hpushforward]
  exact standardPositionMultinomialHMC_invariant hpotential hgradient ε L

end Mcmc.Hamiltonian
