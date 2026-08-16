import Mcmc.Finite.Doeblin

/-!
# Count-indexed positive-horizon particle-Gibbs rates

The trajectory kernel can be instantiated with particle labels `Fin N`, making
the particle count part of the theorem rather than an implicit typeclass
parameter. This module packages the model-specific bounded-potential
minorization obligation and derives an explicit geometric convergence rate.
-/

namespace Mcmc.Finite.MarkovKernel

open Mcmc.Finite.ParticleEstimator Mcmc.Finite.SequentialMonteCarlo

variable {Sample : Type*} [Fintype Sample] [DecidableEq Sample]

/-- Particle Gibbs with exactly `extra + 1` particles. The `+1` particle is
the retained conditional trajectory. -/
noncomputable def countedTrajectoryParticleGibbsKernel
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps) (extra : ℕ) :
    MarkovKernel (Trajectory steps) :=
  trajectoryParticleGibbsKernel (Particle := Fin (extra + 1))
    initial steps hnormalizer

/-- Its exact trajectory target. -/
noncomputable def countedTrajectoryTarget
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps) (extra : ℕ) :
    Distribution (Trajectory steps) :=
  trajectoryTarget (Particle := Fin (extra + 1)) initial steps hnormalizer

/-- A conservative coefficient shape used by bounded-potential PG analyses.
`extra = N-1`, and `bound` records the model-dependent path-weight penalty. -/
noncomputable def particleGibbsCountCoefficient
    (extra : ℕ) (bound : ℝ) (horizon : ℕ) : ℝ :=
  ((extra : ℝ) / ((extra : ℝ) + bound)) ^ horizon

theorem particleGibbsCountCoefficient_pos
    {extra horizon : ℕ} {bound : ℝ} (hextra : 0 < extra)
    (hbound : 0 < bound) :
    0 < particleGibbsCountCoefficient extra bound horizon := by
  unfold particleGibbsCountCoefficient
  positivity

theorem particleGibbsCountCoefficient_lt_one
    {extra horizon : ℕ} {bound : ℝ} (hbound : 0 < bound)
    (hhorizon : 0 < horizon) :
    particleGibbsCountCoefficient extra bound horizon < 1 := by
  unfold particleGibbsCountCoefficient
  have hdenom : 0 < (extra : ℝ) + bound := by positivity
  have hbase0 : 0 ≤ (extra : ℝ) / ((extra : ℝ) + bound) := by positivity
  have hbase1 : (extra : ℝ) / ((extra : ℝ) + bound) < 1 := by
    rw [div_lt_one hdenom]
    linarith
  exact pow_lt_one₀ hbase0 hbase1 hhorizon.ne'

/-- At fixed model bound and horizon, the certified refresh coefficient is
monotone in the number of non-retained particles. -/
theorem particleGibbsCountCoefficient_mono
    {extra more horizon : ℕ} {bound : ℝ} (hcount : extra ≤ more)
    (hbound : 0 ≤ bound) :
    particleGibbsCountCoefficient extra bound horizon ≤
      particleGibbsCountCoefficient more bound horizon := by
  unfold particleGibbsCountCoefficient
  have hleft : 0 ≤ (extra : ℝ) + bound := by positivity
  have hright : 0 ≤ (more : ℝ) + bound := by positivity
  have hbase :
      (extra : ℝ) / ((extra : ℝ) + bound) ≤
        (more : ℝ) / ((more : ℝ) + bound) := by
    by_cases hb : bound = 0
    · subst bound
      by_cases he : extra = 0
      · subst extra
        simp only [Nat.cast_zero, zero_add, zero_div]
        positivity
      · have hm : more ≠ 0 := by omega
        simp [he, hm]
    · have hboundpos : 0 < bound := lt_of_le_of_ne hbound (Ne.symm hb)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hcast : (extra : ℝ) ≤ (more : ℝ) := by exact_mod_cast hcount
      nlinarith
  exact pow_le_pow_left₀ (by positivity) hbase _

/-- Exact model-specific evidence still required from a conditional-SMC
construction. The bound is stated pointwise, so it cannot be confused with a
consequence of stationarity alone. -/
structure BoundedPotentialParticleGibbsMinorization
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps) (extra : ℕ) where
  bound : ℝ
  extra_pos : 0 < extra
  bound_pos : 0 < bound
  minorization : ∀ current proposed,
    particleGibbsCountCoefficient extra bound (steps.length + 1) *
        (countedTrajectoryTarget initial steps hnormalizer extra).mass proposed ≤
      (countedTrajectoryParticleGibbsKernel initial steps hnormalizer extra).prob
        current proposed

/-- A model-facing forced-lineage certificate for the displayed PG
minorization.  Unlike a bound on the already-collapsed kernel, its inequality
is stated on one shared particle history: conditional-SMC selects the history
from the current trajectory fiber, and the uniform index refresh selects the
proposed lineage.  Primitive potential/transition estimates can therefore be
proved directly against the explicit `historyLaw` density. -/
structure ForcedLineageParticleGibbsBound
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps) (extra : ℕ)
    (bound : ℝ) where
  currentFiber_pos : ∀ current,
    0 < (countedTrajectoryTarget initial steps hnormalizer extra).mass current
  witness : ∀ current proposed,
    ∃ history : History (Particle := Fin (extra + 1)) steps,
      ∃ currentIndex proposedIndex : Fin (extra + 1),
        selectedTrajectoryVector steps (history, currentIndex) = current ∧
        selectedTrajectoryVector steps (history, proposedIndex) = proposed ∧
        particleGibbsCountCoefficient extra bound (steps.length + 1) *
            (countedTrajectoryTarget initial steps hnormalizer extra).mass proposed ≤
          (selectedParticleTarget (Particle := Fin (extra + 1))
              initial steps hnormalizer).mass (history, currentIndex) /
            (countedTrajectoryTarget initial steps hnormalizer extra).mass current /
            Fintype.card (Fin (extra + 1))

/-- Primitive full-support assumptions make every count-indexed trajectory
target mass positive.  Thus the support premise in a forced-lineage bound is
not an additional quantitative hypothesis for the bounded finite models. -/
theorem countedTrajectoryTarget_mass_pos_of_fullSupport
    [Nonempty Sample]
    (initial : Distribution Sample) (hinitial : ∀ x, 0 < initial.mass x)
    (steps : List (FeynmanKacStep Sample))
    (hsupport : FeynmanKacFullSupport steps)
    (hnormalizer : 0 < normalizingConstant initial steps)
    (extra : ℕ) (current : Trajectory steps) :
    0 < (countedTrajectoryTarget initial steps hnormalizer extra).mass current := by
  let proposedIndex : Fin (extra + 1) := ⟨0, by omega⟩
  let history := pairedHistoryAt proposedIndex steps current current
  have hextended : 0 <
      (selectedParticleTarget (Particle := Fin (extra + 1))
        initial steps hnormalizer).mass (history, proposedIndex) :=
    selectedParticleTarget_mass_pos initial hinitial steps hsupport
      hnormalizer (history, proposedIndex)
  have hfiber := Mcmc.Finite.Conditional.fiberMass_pos_of_mass_pos
    (selectedParticleTarget (Particle := Fin (extra + 1))
      initial steps hnormalizer)
    (selectedTrajectoryVector steps) (history, proposedIndex) hextended
  have htrajectory :
      selectedTrajectoryVector steps (history, proposedIndex) = current := by
    exact selectedTrajectoryVector_pairedHistoryAt_proposed
      proposedIndex steps current current
  rw [htrajectory] at hfiber
  change 0 < (Mcmc.Finite.Conditional.statisticMarginal
    (selectedParticleTarget (Particle := Fin (extra + 1))
      initial steps hnormalizer) (selectedTrajectoryVector steps)).mass current
  rw [Mcmc.Finite.Conditional.statisticMarginal_mass]
  exact hfiber

/-- A forced-lineage density bound implies the pointwise minorization needed
by the count-indexed convergence theorem. -/
noncomputable def ForcedLineageParticleGibbsBound.toMinorization
    {initial : Distribution Sample} {steps : List (FeynmanKacStep Sample)}
    {hnormalizer : 0 < normalizingConstant initial steps} {extra : ℕ}
    {bound : ℝ} (hextra : 0 < extra) (hbound : 0 < bound)
    (certificate : ForcedLineageParticleGibbsBound
      initial steps hnormalizer extra bound) :
    BoundedPotentialParticleGibbsMinorization
      initial steps hnormalizer extra where
  bound := bound
  extra_pos := hextra
  bound_pos := hbound
  minorization current proposed := by
    obtain ⟨history, currentIndex, proposedIndex, hcurrent, hproposed, hmass⟩ :=
      certificate.witness current proposed
    have hfiberEq :
        Mcmc.Finite.Conditional.fiberMass
            (selectedParticleTarget (Particle := Fin (extra + 1))
              initial steps hnormalizer)
            (selectedTrajectoryVector steps) current =
          (countedTrajectoryTarget initial steps hnormalizer extra).mass current := by
      rw [← Mcmc.Finite.Conditional.statisticMarginal_mass]
      rfl
    have hfiber : 0 < Mcmc.Finite.Conditional.fiberMass
        (selectedParticleTarget (Particle := Fin (extra + 1))
          initial steps hnormalizer)
        (selectedTrajectoryVector steps) current := by
      rw [hfiberEq]
      exact certificate.currentFiber_pos current
    refine hmass.trans ?_
    have hedge :=
      Mcmc.Finite.Conditional.conditional_mass_mul_evolve_le_collapsedKernel_prob
        (selectedParticleTarget (Particle := Fin (extra + 1))
          initial steps hnormalizer)
        (selectedTrajectoryVector steps)
        (selectedIndexRefreshKernel (Particle := Fin (extra + 1)) steps)
        current proposed (history, currentIndex) (history, proposedIndex)
        hcurrent hproposed hfiber
    rw [hfiberEq] at hedge
    have hedgeEq :
        (selectedIndexRefreshKernel (Particle := Fin (extra + 1)) steps).prob
            (history, currentIndex) (history, proposedIndex) =
          1 / Fintype.card (Fin (extra + 1)) := by
      simp [selectedIndexRefreshKernel, MarkovKernel.liftSnd,
        uniformIndexKernel]
    rw [hedgeEq] at hedge
    change
      (selectedParticleTarget (Particle := Fin (extra + 1))
            initial steps hnormalizer).mass (history, currentIndex) /
          (countedTrajectoryTarget initial steps hnormalizer extra).mass current /
          Fintype.card (Fin (extra + 1)) ≤
        (Mcmc.Finite.Conditional.collapsedKernel
          (selectedParticleTarget (Particle := Fin (extra + 1))
            initial steps hnormalizer)
          (selectedTrajectoryVector steps)
          (selectedIndexRefreshKernel (Particle := Fin (extra + 1)) steps)).prob
            current proposed
    simpa [div_eq_mul_inv] using hedge

/-- A bounded-potential minorization yields an explicit refresh decomposition
for the count-indexed positive-horizon trajectory kernel. -/
noncomputable def BoundedPotentialParticleGibbsMinorization.toRefresh
    {initial : Distribution Sample} {steps : List (FeynmanKacStep Sample)}
    {hnormalizer : 0 < normalizingConstant initial steps} {extra : ℕ}
    (certificate : BoundedPotentialParticleGibbsMinorization
      initial steps hnormalizer extra) :
    RefreshDecomposition
      (countedTrajectoryParticleGibbsKernel initial steps hnormalizer extra)
      (countedTrajectoryTarget initial steps hnormalizer extra) := by
  let coefficient := particleGibbsCountCoefficient extra certificate.bound
    (steps.length + 1)
  apply RefreshDecomposition.ofMinorization coefficient
  · exact (particleGibbsCountCoefficient_pos certificate.extra_pos
      certificate.bound_pos).le
  · exact particleGibbsCountCoefficient_lt_one certificate.bound_pos (by omega)
  · exact certificate.minorization
  · exact trajectoryParticleGibbsKernel_stationary
      (Particle := Fin (extra + 1)) initial steps hnormalizer

/-- Uniform geometric total-variation bound with explicit particle-count and
horizon dependence. -/
theorem boundedPotentialParticleGibbs_totalVariation_le
    {initial : Distribution Sample} {steps : List (FeynmanKacStep Sample)}
    {hnormalizer : 0 < normalizingConstant initial steps} {extra : ℕ}
    (certificate : BoundedPotentialParticleGibbsMinorization
      initial steps hnormalizer extra)
    (initialLaw : Distribution (Trajectory steps)) (iterations : ℕ) :
    Nonhomogeneous.distributionTotalVariation
      (Nonhomogeneous.iterateLaw initialLaw
        (countedTrajectoryParticleGibbsKernel initial steps hnormalizer extra)
        iterations)
      (countedTrajectoryTarget initial steps hnormalizer extra) ≤
      (1 - particleGibbsCountCoefficient extra certificate.bound
        (steps.length + 1)) ^ iterations := by
  exact certificate.toRefresh.iterateLaw_totalVariation_le initialLaw iterations

/-- For every `N ≥ 2` satisfying the displayed minorization, positive-horizon
particle Gibbs converges in total variation from every initial trajectory law. -/
theorem boundedPotentialParticleGibbs_totalVariation_tendsto_zero
    {initial : Distribution Sample} {steps : List (FeynmanKacStep Sample)}
    {hnormalizer : 0 < normalizingConstant initial steps} {extra : ℕ}
    (certificate : BoundedPotentialParticleGibbsMinorization
      initial steps hnormalizer extra)
    (initialLaw : Distribution (Trajectory steps)) :
    Filter.Tendsto (fun iterations =>
      Nonhomogeneous.distributionTotalVariation
        (Nonhomogeneous.iterateLaw initialLaw
          (countedTrajectoryParticleGibbsKernel initial steps hnormalizer extra)
          iterations)
        (countedTrajectoryTarget initial steps hnormalizer extra))
      Filter.atTop (nhds 0) := by
  exact certificate.toRefresh.iterateLaw_totalVariation_tendsto_zero
    (particleGibbsCountCoefficient_pos certificate.extra_pos
      certificate.bound_pos) initialLaw

/-- Full-support model ingredients construct a conservative positive refresh
certificate directly at the `extra + 1` particle interface. This certificate
does not claim the sharper bounded-potential coefficient above; it uses the
generic finite strictly-positive-matrix construction. -/
noncomputable def countedFullSupportParticleGibbsRefresh
    [Nonempty Sample]
    (initial : Distribution Sample) (hinitial : ∀ x, 0 < initial.mass x)
    (steps : List (FeynmanKacStep Sample))
    (hsupport : FeynmanKacFullSupport steps)
    (hnormalizer : 0 < normalizingConstant initial steps)
    (extra : ℕ) (hextra : 0 < extra) :
    RefreshDecomposition
      (countedTrajectoryParticleGibbsKernel initial steps hnormalizer extra)
      (countedTrajectoryTarget initial steps hnormalizer extra) := by
  letI : Nontrivial (Fin (extra + 1)) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by simp; omega)
  letI : Nonempty (Trajectory steps) :=
    ⟨⟨List.replicate (steps.length + 1)
      (Classical.choice ‹Nonempty Sample›), by simp⟩⟩
  apply RefreshDecomposition.ofStrictlyPositive
  · apply trajectoryParticleGibbsKernel_prob_pos_of_fiberConnectivity
    exact particleGibbsFiberConnectivity_of_pairRealizable
      initial hinitial steps hsupport hnormalizer
        (particleGibbsPairRealizable_of_nontrivial steps)
  · exact trajectoryParticleGibbsKernel_stationary
      (Particle := Fin (extra + 1)) initial steps hnormalizer

/-- Count-indexed geometric TV bound under primitive full-support assumptions.
The rate is the explicit conservative finite-matrix rate stored in the refresh
certificate above. -/
theorem countedFullSupportParticleGibbs_totalVariation_le
    [Nonempty Sample]
    (initial : Distribution Sample) (hinitial : ∀ x, 0 < initial.mass x)
    (steps : List (FeynmanKacStep Sample))
    (hsupport : FeynmanKacFullSupport steps)
    (hnormalizer : 0 < normalizingConstant initial steps)
    (extra : ℕ) (hextra : 0 < extra)
    (initialLaw : Distribution (Trajectory steps)) (iterations : ℕ) :
    Nonhomogeneous.distributionTotalVariation
      (Nonhomogeneous.iterateLaw initialLaw
        (countedTrajectoryParticleGibbsKernel initial steps hnormalizer extra)
        iterations)
      (countedTrajectoryTarget initial steps hnormalizer extra) ≤
      (countedFullSupportParticleGibbsRefresh initial hinitial steps hsupport
        hnormalizer extra hextra).rate ^ iterations := by
  exact (countedFullSupportParticleGibbsRefresh initial hinitial steps hsupport
    hnormalizer extra hextra).iterateLaw_totalVariation_le initialLaw iterations

/-- For every explicit count `N = extra + 1 ≥ 2`, primitive full-support
bootstrap assumptions imply positive-horizon TV convergence from every
initial trajectory law. -/
theorem countedFullSupportParticleGibbs_totalVariation_tendsto_zero
    [Nonempty Sample]
    (initial : Distribution Sample) (hinitial : ∀ x, 0 < initial.mass x)
    (steps : List (FeynmanKacStep Sample))
    (hsupport : FeynmanKacFullSupport steps)
    (hnormalizer : 0 < normalizingConstant initial steps)
    (extra : ℕ) (hextra : 0 < extra)
    (initialLaw : Distribution (Trajectory steps)) :
    Filter.Tendsto (fun iterations =>
      Nonhomogeneous.distributionTotalVariation
        (Nonhomogeneous.iterateLaw initialLaw
          (countedTrajectoryParticleGibbsKernel initial steps hnormalizer extra)
          iterations)
        (countedTrajectoryTarget initial steps hnormalizer extra))
      Filter.atTop (nhds 0) := by
  letI : Nontrivial (Fin (extra + 1)) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by simp; omega)
  exact particleGibbs_totalVariation_tendsto_zero_of_fullSupport
    (Particle := Fin (extra + 1)) initial hinitial steps hsupport hnormalizer
      initialLaw

end Mcmc.Finite.MarkovKernel
