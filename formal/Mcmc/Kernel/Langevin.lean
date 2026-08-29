import Mcmc.Kernel.GaussianRandomWalk

/-!
# State-dependent Gaussian proposals, ULA, and MALA

This module supplies the general finite-dimensional proposal underlying the
unadjusted and Metropolis-adjusted Langevin algorithms.  A measurable drift
selects the proposal centre `x + drift x`; isotropic Gaussian noise is then
added around that centre.

The unadjusted kernel is proved Markov but is not claimed to preserve the
requested target.  Applying the general density-MH construction gives MALA,
which is proved reversible and invariant under explicit measurability and
pointwise-finiteness hypotheses.
-/

open MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace Mcmc.Kernel

open ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- Density of an additive-noise proposal whose centre depends measurably on
the current state. -/
noncomputable def shiftedProposalDensity
    (noise : (ι → ℝ) → ENNReal) (centre : (ι → ℝ) → (ι → ℝ))
    (x y : ι → ℝ) : ENNReal :=
  noise (y - centre x)

omit [Fintype ι] in
theorem measurable_uncurry_shiftedProposalDensity
    {noise : (ι → ℝ) → ENNReal} {centre : (ι → ℝ) → (ι → ℝ)}
    (hnoise : Measurable noise) (hcentre : Measurable centre) :
    Measurable (Function.uncurry (shiftedProposalDensity noise centre)) := by
  exact hnoise.comp (measurable_snd.sub (hcentre.comp measurable_fst))

/-- Translation invariance normalizes every state-dependent-location row. -/
theorem shiftedProposalDensity_lintegral
    {noise : (ι → ℝ) → ENNReal} (hnoise : Measurable noise)
    (centre : (ι → ℝ) → (ι → ℝ)) (x : ι → ℝ) :
    ∫⁻ y, shiftedProposalDensity noise centre x y ∂volume =
      ∫⁻ z, noise z ∂volume := by
  exact randomWalkProposalDensity_lintegral volume hnoise (centre x)

/-- The measurable proposal centre used by Langevin methods.  Supplying the
scaled score as `drift` keeps analytic differentiability assumptions separate
from the kernel-level correctness proof. -/
def langevinCentre (drift : (ι → ℝ) → (ι → ℝ)) (x : ι → ℝ) : ι → ℝ :=
  x + drift x

omit [Fintype ι] in
theorem measurable_langevinCentre {drift : (ι → ℝ) → (ι → ℝ)}
    (hdrift : Measurable drift) : Measurable (langevinCentre drift) := by
  exact measurable_id.add hdrift

/-- The standard MALA drift: half the proposal variance times the score
`∇ log π`. Keeping the score as a callback avoids imposing a particular
differentiability representation on target densities. -/
noncomputable def malaScoreDrift (variance : ℝ≥0) (score : (ι → ℝ) → (ι → ℝ))
    (x : ι → ℝ) : ι → ℝ :=
  fun i => ((variance : ℝ) / 2) * score x i

omit [Fintype ι] in
theorem measurable_malaScoreDrift {variance : ℝ≥0}
    {score : (ι → ℝ) → (ι → ℝ)} (hscore : Measurable score) :
    Measurable (malaScoreDrift variance score) := by
  apply measurable_pi_iff.mpr
  intro i
  exact ((measurable_pi_apply i).comp hscore).const_mul _

/-- The isotropic Gaussian density `q(x,y)` used by ULA and MALA. -/
noncomputable def langevinProposalDensity
    (drift : (ι → ℝ) → (ι → ℝ)) (variance : ℝ≥0)
    (x y : ι → ℝ) : ENNReal :=
  shiftedProposalDensity (isotropicGaussianPDF variance)
    (langevinCentre drift) x y

theorem measurable_uncurry_langevinProposalDensity
    {drift : (ι → ℝ) → (ι → ℝ)} (hdrift : Measurable drift)
    (variance : ℝ≥0) :
    Measurable (Function.uncurry (langevinProposalDensity drift variance)) := by
  exact measurable_uncurry_shiftedProposalDensity
    (measurable_isotropicGaussianPDF variance) (measurable_langevinCentre hdrift)

theorem langevinProposalDensity_normalized
    (drift : (ι → ℝ) → (ι → ℝ)) (variance : ℝ≥0)
    (hvariance : variance ≠ 0) (x : ι → ℝ) :
    ∫⁻ y, langevinProposalDensity drift variance x y ∂volume = 1 := by
  change ∫⁻ y, shiftedProposalDensity (isotropicGaussianPDF variance)
    (langevinCentre drift) x y ∂volume = 1
  rw [shiftedProposalDensity_lintegral (measurable_isotropicGaussianPDF variance),
    lintegral_isotropicGaussianPDF_eq_one variance hvariance]

/-- Unadjusted Langevin transition.  No target-invariance theorem is asserted:
at fixed nonzero step size this proposal is generally biased. -/
noncomputable def unadjustedLangevin
    (drift : (ι → ℝ) → (ι → ℝ)) (variance : ℝ≥0)
    (_hdrift : Measurable drift) (_hvariance : variance ≠ 0) :
    Kernel (ι → ℝ) (ι → ℝ) :=
  densityProposal volume (langevinProposalDensity drift variance)

theorem unadjustedLangevin_isMarkov
    (drift : (ι → ℝ) → (ι → ℝ)) (variance : ℝ≥0)
    (hdrift : Measurable drift) (hvariance : variance ≠ 0) :
    IsMarkovKernel (unadjustedLangevin drift variance hdrift hvariance) := by
  exact densityProposal_isMarkov volume
    (measurable_uncurry_langevinProposalDensity hdrift variance)
    (langevinProposalDensity_normalized drift variance hvariance)

/-- Metropolis-adjusted Langevin transition for an arbitrary measurable
drift.  The usual score-gradient choice is a client of this definition. -/
noncomputable def metropolisAdjustedLangevin
    (weight : (ι → ℝ) → ENNReal) (drift : (ι → ℝ) → (ι → ℝ))
    (variance : ℝ≥0) (hdrift : Measurable drift) (hvariance : variance ≠ 0) :
    Kernel (ι → ℝ) (ι → ℝ) :=
  densityMetropolisHastings volume weight
    (langevinProposalDensity drift variance)
    (measurable_uncurry_langevinProposalDensity hdrift variance)
    (langevinProposalDensity_normalized drift variance hvariance)

/-- Conventional isotropic MALA, specialized to the score-scaled drift
`variance / 2 * ∇ log π`. -/
noncomputable def scoreMALA
    (weight : (ι → ℝ) → ENNReal) (score : (ι → ℝ) → (ι → ℝ))
    (variance : ℝ≥0) (hscore : Measurable score) (hvariance : variance ≠ 0) :
    Kernel (ι → ℝ) (ι → ℝ) :=
  metropolisAdjustedLangevin weight (malaScoreDrift variance score) variance
    (measurable_malaScoreDrift hscore) hvariance

theorem metropolisAdjustedLangevin_isMarkov
    (weight : (ι → ℝ) → ENNReal) (drift : (ι → ℝ) → (ι → ℝ))
    (variance : ℝ≥0) (hweight : Measurable weight)
    (hdrift : Measurable drift) (hvariance : variance ≠ 0) :
    IsMarkovKernel
      (metropolisAdjustedLangevin weight drift variance hdrift hvariance) := by
  exact densityMetropolisHastings_isMarkov volume weight _ hweight
    (measurable_uncurry_langevinProposalDensity hdrift variance)
    (langevinProposalDensity_normalized drift variance hvariance)

theorem scoreMALA_isMarkov
    (weight : (ι → ℝ) → ENNReal) (score : (ι → ℝ) → (ι → ℝ))
    (variance : ℝ≥0) (hweight : Measurable weight)
    (hscore : Measurable score) (hvariance : variance ≠ 0) :
    IsMarkovKernel (scoreMALA weight score variance hscore hvariance) := by
  exact metropolisAdjustedLangevin_isMarkov weight
    (malaScoreDrift variance score) variance hweight
    (measurable_malaScoreDrift hscore) hvariance

theorem metropolisAdjustedLangevin_isReversible
    (weight : (ι → ℝ) → ENNReal) (drift : (ι → ℝ) → (ι → ℝ))
    (variance : ℝ≥0) (hweight : Measurable weight)
    (hdrift : Measurable drift) (hvariance : variance ≠ 0)
    (hfinite : ∀ x y, forwardDensityFlow weight
      (langevinProposalDensity drift variance) x y ≠ ∞) :
    (metropolisAdjustedLangevin weight drift variance hdrift hvariance).IsReversible
      (densityTarget volume weight) := by
  exact densityMetropolisHastings_isReversible volume weight _ hweight
    (measurable_uncurry_langevinProposalDensity hdrift variance)
    (langevinProposalDensity_normalized drift variance hvariance) hfinite

theorem scoreMALA_isReversible
    (weight : (ι → ℝ) → ENNReal) (score : (ι → ℝ) → (ι → ℝ))
    (variance : ℝ≥0) (hweight : Measurable weight)
    (hscore : Measurable score) (hvariance : variance ≠ 0)
    (hfinite : ∀ x y, forwardDensityFlow weight
      (langevinProposalDensity (malaScoreDrift variance score) variance) x y ≠ ∞) :
    (scoreMALA weight score variance hscore hvariance).IsReversible
      (densityTarget volume weight) := by
  exact metropolisAdjustedLangevin_isReversible weight
    (malaScoreDrift variance score) variance hweight
    (measurable_malaScoreDrift hscore) hvariance hfinite

theorem metropolisAdjustedLangevin_invariant
    (weight : (ι → ℝ) → ENNReal) (drift : (ι → ℝ) → (ι → ℝ))
    (variance : ℝ≥0) (hweight : Measurable weight)
    (hdrift : Measurable drift) (hvariance : variance ≠ 0)
    (hfinite : ∀ x y, forwardDensityFlow weight
      (langevinProposalDensity drift variance) x y ≠ ∞) :
    (metropolisAdjustedLangevin weight drift variance hdrift hvariance).Invariant
      (densityTarget volume weight) := by
  exact densityMetropolisHastings_invariant volume weight _ hweight
    (measurable_uncurry_langevinProposalDensity hdrift variance)
    (langevinProposalDensity_normalized drift variance hvariance) hfinite

theorem scoreMALA_invariant
    (weight : (ι → ℝ) → ENNReal) (score : (ι → ℝ) → (ι → ℝ))
    (variance : ℝ≥0) (hweight : Measurable weight)
    (hscore : Measurable score) (hvariance : variance ≠ 0)
    (hfinite : ∀ x y, forwardDensityFlow weight
      (langevinProposalDensity (malaScoreDrift variance score) variance) x y ≠ ∞) :
    (scoreMALA weight score variance hscore hvariance).Invariant
      (densityTarget volume weight) := by
  exact metropolisAdjustedLangevin_invariant weight
    (malaScoreDrift variance score) variance hweight
    (measurable_malaScoreDrift hscore) hvariance hfinite

end Mcmc.Kernel
