import Mcmc.Finite.Adaptive
import Mcmc.Finite.ParticleGibbsConvergence
import Mcmc.Finite.SequentialMonteCarlo

/-!
# Finite refresh decompositions and geometric convergence

A Doeblin proof is most useful operationally when it exposes the residual
kernel: `P = ε Π + (1-ε) R`, where `Π` refreshes from the target and `R`
also preserves the target.  This module records that certificate and derives
an exact finite-time decomposition and a total-variation rate.
-/

namespace Mcmc.Finite.MarkovKernel

variable {State : Type*} [Fintype State]

/-- A checked refresh/residual decomposition of a finite transition. -/
structure RefreshDecomposition (transition : MarkovKernel State)
    (target : Distribution State) where
  coefficient : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  coefficient_lt_one : coefficient < 1
  residual : MarkovKernel State
  residual_stationary : residual.Stationary target
  transition_eq : transition = mixture coefficient coefficient_nonneg
    coefficient_lt_one.le (refresh target) residual

namespace RefreshDecomposition

variable {transition : MarkovKernel State} {target : Distribution State}

/-- The residual-branch probability. -/
def rate (certificate : RefreshDecomposition transition target) : ℝ :=
  1 - certificate.coefficient

theorem rate_nonneg (certificate : RefreshDecomposition transition target) :
    0 ≤ certificate.rate :=
  sub_nonneg.mpr certificate.coefficient_lt_one.le

theorem rate_lt_one (certificate : RefreshDecomposition transition target)
    (hpositive : 0 < certificate.coefficient) : certificate.rate < 1 := by
  unfold rate
  linarith

theorem transition_stationary
    (certificate : RefreshDecomposition transition target) :
    transition.Stationary target := by
  rw [certificate.transition_eq]
  exact mixture_stationary _ certificate.coefficient_nonneg
    certificate.coefficient_lt_one.le _ _ target
    (refresh_stationary target) certificate.residual_stationary

theorem evolve_mass (certificate : RefreshDecomposition transition target)
    (law : Distribution State) (y : State) :
    (law.evolve transition).mass y =
      certificate.coefficient * target.mass y +
        certificate.rate * (law.evolve certificate.residual).mass y := by
  rw [Distribution.evolve_mass]
  have hprob (x z : State) : transition.prob x z =
      certificate.coefficient * (refresh target).prob x z +
        (1 - certificate.coefficient) * certificate.residual.prob x z := by
    exact congrFun (congrFun
      (congrArg MarkovKernel.prob certificate.transition_eq) x) z
  simp_rw [hprob, refresh_prob, mul_add, Finset.sum_add_distrib]
  rw [show (∑ x, law.mass x *
      (certificate.coefficient * target.mass y)) =
      certificate.coefficient * target.mass y by
    rw [← Finset.sum_mul, law.sum_mass, one_mul]]
  rw [show (∑ x, law.mass x *
      ((1 - certificate.coefficient) * certificate.residual.prob x y)) =
      certificate.rate * (law.evolve certificate.residual).mass y by
    rw [Distribution.evolve_mass, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    unfold rate
    ring]

/-- Exact regenerative form of the law after `n` transitions. -/
theorem iterateLaw_mass (certificate : RefreshDecomposition transition target)
    (initial : Distribution State) (n : ℕ) (y : State) :
    (Nonhomogeneous.iterateLaw initial transition n).mass y =
      (1 - certificate.rate ^ n) * target.mass y +
        certificate.rate ^ n *
          (Nonhomogeneous.iterateLaw initial certificate.residual n).mass y := by
  induction n generalizing y with
  | zero => simp [Nonhomogeneous.iterateLaw]
  | succ n ih =>
      rw [Nonhomogeneous.iterateLaw, certificate.evolve_mass]
      rw [Distribution.evolve_mass]
      simp_rw [ih]
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
      have htarget := certificate.residual_stationary y
      have hsumTarget :
          (∑ x, (1 - certificate.rate ^ n) * target.mass x *
            certificate.residual.prob x y) =
          (1 - certificate.rate ^ n) * target.mass y := by
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum, htarget]
      have hsumResidual :
          (∑ x, certificate.rate ^ n *
            (Nonhomogeneous.iterateLaw initial certificate.residual n).mass x *
              certificate.residual.prob x y) =
          certificate.rate ^ n *
            (Nonhomogeneous.iterateLaw initial certificate.residual
              (n + 1)).mass y := by
        rw [Nonhomogeneous.iterateLaw, Distribution.evolve_mass]
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum]
      rw [hsumTarget, hsumResidual]
      change certificate.coefficient * target.mass y +
          certificate.rate *
            ((1 - certificate.rate ^ n) * target.mass y +
              certificate.rate ^ n *
                (Nonhomogeneous.iterateLaw initial certificate.residual
                  (n + 1)).mass y) = _
      rw [pow_succ]
      unfold rate
      ring

/-- Geometric total-variation convergence supplied by a positive refresh
component. -/
theorem iterateLaw_totalVariation_le
    (certificate : RefreshDecomposition transition target)
    (initial : Distribution State) (n : ℕ) :
    Nonhomogeneous.distributionTotalVariation
      (Nonhomogeneous.iterateLaw initial transition n) target ≤
      certificate.rate ^ n := by
  unfold Nonhomogeneous.distributionTotalVariation
  simp_rw [certificate.iterateLaw_mass initial n]
  have hr : 0 ≤ certificate.rate ^ n :=
    pow_nonneg certificate.rate_nonneg _
  calc
    (∑ y, |(1 - certificate.rate ^ n) * target.mass y +
        certificate.rate ^ n *
          (Nonhomogeneous.iterateLaw initial certificate.residual n).mass y -
        target.mass y|) / 2 =
      certificate.rate ^ n *
        Nonhomogeneous.distributionTotalVariation
          (Nonhomogeneous.iterateLaw initial certificate.residual n) target := by
        unfold Nonhomogeneous.distributionTotalVariation
        rw [← mul_div_assoc, Finset.mul_sum]
        apply congrArg (fun z : ℝ => z / 2)
        apply Finset.sum_congr rfl
        intro y _
        rw [show
          (1 - certificate.rate ^ n) * target.mass y +
              certificate.rate ^ n *
                (Nonhomogeneous.iterateLaw initial certificate.residual n).mass y -
              target.mass y =
            certificate.rate ^ n *
              ((Nonhomogeneous.iterateLaw initial certificate.residual n).mass y -
                target.mass y) by ring,
          abs_mul, abs_of_nonneg hr]
    _ ≤ certificate.rate ^ n * 1 :=
      mul_le_mul_of_nonneg_left
        (Nonhomogeneous.distributionTotalVariation_le_one _ _) hr
    _ = certificate.rate ^ n := mul_one _

theorem iterateLaw_totalVariation_tendsto_zero
    (certificate : RefreshDecomposition transition target)
    (hpositive : 0 < certificate.coefficient)
    (initial : Distribution State) :
    Filter.Tendsto (fun n =>
      Nonhomogeneous.distributionTotalVariation
        (Nonhomogeneous.iterateLaw initial transition n) target)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n =>
      Nonhomogeneous.distributionTotalVariation_nonneg _ _
  · exact Filter.Eventually.of_forall fun n =>
      certificate.iterateLaw_totalVariation_le initial n
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one
      certificate.rate_nonneg (certificate.rate_lt_one hpositive)

end RefreshDecomposition

section ParticleGibbs

open Mcmc.Finite.ParticleEstimator Mcmc.Finite.SequentialMonteCarlo

variable {Particle Sample : Type*} [Fintype Particle] [Nonempty Particle]
  [DecidableEq Particle] [Fintype Sample] [DecidableEq Sample]

/-- The explicit additional obligation needed to turn positive-horizon
particle-Gibbs stationarity into a geometric convergence theorem.  A client
must exhibit a genuine target-refresh component of the concrete PG kernel;
stationarity alone is intentionally insufficient. -/
abbrev ParticleGibbsRefreshCertificate
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps) :=
  RefreshDecomposition
    (particleGibbsKernel (Particle := Particle) initial steps hnormalizer)
    (selectedParticleTarget (Particle := Particle) initial steps hnormalizer)

/-- Positive-horizon finite particle Gibbs converges geometrically whenever
the concrete conditional-SMC construction supplies a positive refresh
certificate.  The bound is uniform over the initial extended state law. -/
theorem particleGibbs_totalVariation_le_geometric
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps)
    (certificate : ParticleGibbsRefreshCertificate (Particle := Particle)
      initial steps hnormalizer)
    (initialLaw : Distribution (History (Particle := Particle) steps × Particle))
    (n : ℕ) :
    Nonhomogeneous.distributionTotalVariation
      (Nonhomogeneous.iterateLaw initialLaw
        (particleGibbsKernel (Particle := Particle) initial steps hnormalizer) n)
      (selectedParticleTarget (Particle := Particle) initial steps hnormalizer) ≤
      certificate.rate ^ n :=
  certificate.iterateLaw_totalVariation_le initialLaw n

theorem particleGibbs_totalVariation_tendsto_zero
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps)
    (certificate : ParticleGibbsRefreshCertificate (Particle := Particle)
      initial steps hnormalizer)
    (hpositive : 0 < certificate.coefficient)
    (initialLaw : Distribution (History (Particle := Particle) steps × Particle)) :
    Filter.Tendsto (fun n =>
      Nonhomogeneous.distributionTotalVariation
        (Nonhomogeneous.iterateLaw initialLaw
          (particleGibbsKernel (Particle := Particle) initial steps hnormalizer) n)
        (selectedParticleTarget (Particle := Particle) initial steps hnormalizer))
      Filter.atTop (nhds 0) :=
  certificate.iterateLaw_totalVariation_tendsto_zero hpositive initialLaw

end ParticleGibbs

end Mcmc.Finite.MarkovKernel
