import Mcmc.Finite.Adaptive
import Mcmc.Finite.ParticleGibbsConvergence
import Mcmc.Finite.SequentialMonteCarlo
import Mcmc.Finite.ParticleGibbsTrajectory

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

/-- Construct the residual kernel directly from a strict finite Doeblin
minorization. This is the main client-facing route to a refresh certificate. -/
noncomputable def ofMinorization (coefficient : ℝ)
    (hcoeff0 : 0 ≤ coefficient) (hcoeff1 : coefficient < 1)
    (hminor : ∀ x y, coefficient * target.mass y ≤ transition.prob x y)
    (hinvariant : transition.Stationary target) :
    RefreshDecomposition transition target := by
  have hdenom : 1 - coefficient ≠ 0 := ne_of_gt (sub_pos.mpr hcoeff1)
  let residual : MarkovKernel State :=
    { prob := fun x y =>
        (transition.prob x y - coefficient * target.mass y) /
          (1 - coefficient)
      nonneg := fun x y => div_nonneg (sub_nonneg.mpr (hminor x y))
        (sub_nonneg.mpr hcoeff1.le)
      sum_prob := fun x => by
        rw [← Finset.sum_div, Finset.sum_sub_distrib,
          transition.sum_prob, ← Finset.mul_sum, target.sum_mass]
        field_simp [hdenom] }
  have hresidual : residual.Stationary target := by
    intro y
    change (∑ x, target.mass x *
      ((transition.prob x y - coefficient * target.mass y) /
        (1 - coefficient))) = target.mass y
    have hnum :
        (∑ x, target.mass x *
          (transition.prob x y - coefficient * target.mass y)) =
        target.mass y * (1 - coefficient) := by
      calc
        ∑ x, target.mass x *
            (transition.prob x y - coefficient * target.mass y) =
            (∑ x, target.mass x * transition.prob x y) -
              ∑ x, target.mass x * (coefficient * target.mass y) := by
                simp_rw [mul_sub]
                rw [Finset.sum_sub_distrib]
        _ = target.mass y - coefficient * target.mass y := by
            rw [hinvariant y]
            rw [show (∑ x, target.mass x *
                (coefficient * target.mass y)) =
                coefficient * target.mass y by
              rw [← Finset.sum_mul, target.sum_mass, one_mul]]
        _ = target.mass y * (1 - coefficient) := by ring
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div]
    rw [hnum]
    field_simp [hdenom]
  refine
    { coefficient := coefficient
      coefficient_nonneg := hcoeff0
      coefficient_lt_one := hcoeff1
      residual := residual
      residual_stationary := hresidual
      transition_eq := ?_ }
  apply MarkovKernel.ext
  funext x y
  change transition.prob x y = coefficient * target.mass y +
    (1 - coefficient) *
      ((transition.prob x y - coefficient * target.mass y) /
        (1 - coefficient))
  field_simp [hdenom]
  ring

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

section StrictlyPositive

variable [DecidableEq State]

/-- Product of all entries of a finite transition matrix. It supplies a
deliberately conservative but explicit common lower bound when every entry is
positive. -/
noncomputable def globalEntryProduct (transition : MarkovKernel State) : ℝ :=
  ∏ z : State × State, transition.prob z.1 z.2

omit [DecidableEq State] in
theorem prob_le_one (transition : MarkovKernel State) (x y : State) :
    transition.prob x y ≤ 1 := by
  rw [← transition.sum_prob x]
  exact Finset.single_le_sum (fun z _ => transition.nonneg x z)
    (Finset.mem_univ y)

omit [DecidableEq State] in
theorem globalEntryProduct_pos (transition : MarkovKernel State)
    (hpositive : ∀ x y, 0 < transition.prob x y) :
    0 < globalEntryProduct transition := by
  unfold globalEntryProduct
  exact Finset.prod_pos fun z _ => hpositive z.1 z.2

theorem globalEntryProduct_le_prob (transition : MarkovKernel State)
    (x y : State) :
    globalEntryProduct transition ≤ transition.prob x y := by
  let z : State × State := (x, y)
  have hprod :
      (∏ w ∈ (Finset.univ : Finset (State × State)).erase z,
        transition.prob w.1 w.2) ≤ 1 := by
    apply Finset.prod_le_one
    · intro w _
      exact transition.nonneg w.1 w.2
    · intro w _
      exact prob_le_one transition w.1 w.2
  have hnonneg : 0 ≤ transition.prob x y := transition.nonneg x y
  rw [globalEntryProduct, ← Finset.prod_erase_mul _ _ (Finset.mem_univ z)]
  exact mul_le_of_le_one_left hnonneg hprod

/-- Every strictly positive finite target-invariant transition has an
explicit positive Doeblin refresh decomposition. The product coefficient is
conservative, but requires no minimizer bookkeeping. -/
noncomputable def ofStrictlyPositive
    [Nonempty State]
    (hpositive : ∀ x y, 0 < transition.prob x y)
    (hinvariant : transition.Stationary target) :
    RefreshDecomposition transition target := by
  let product := globalEntryProduct transition
  let coefficient := product / 2
  have hproduct0 : 0 < product := globalEntryProduct_pos transition hpositive
  have hproduct1 : product ≤ 1 := by
    let x := Classical.choice ‹Nonempty State›
    exact (globalEntryProduct_le_prob transition x x).trans
      (prob_le_one transition x x)
  have hcoeff0 : 0 ≤ coefficient := by
    dsimp [coefficient]
    positivity
  have hcoeff1 : coefficient < 1 := by
    dsimp [coefficient]
    linarith
  apply ofMinorization coefficient hcoeff0 hcoeff1
  · intro x y
    have htarget : target.mass y ≤ 1 := by
      rw [← target.sum_mass]
      exact Finset.single_le_sum (fun z _ => target.nonneg z)
        (Finset.mem_univ y)
    calc
      coefficient * target.mass y ≤ coefficient * 1 :=
        mul_le_mul_of_nonneg_left htarget hcoeff0
      _ = coefficient := mul_one _
      _ ≤ product := by
        dsimp [coefficient]
        linarith
      _ ≤ transition.prob x y := globalEntryProduct_le_prob transition x y
  · exact hinvariant

theorem ofStrictlyPositive_coefficient_pos
    [Nonempty State]
    (hpositive : ∀ x y, 0 < transition.prob x y)
    (hinvariant : transition.Stationary target) :
    0 < (ofStrictlyPositive hpositive hinvariant).coefficient := by
  change 0 < globalEntryProduct transition / 2
  exact div_pos (globalEntryProduct_pos transition hpositive) (by norm_num)

end StrictlyPositive

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
particle-Gibbs stationarity into a geometric convergence theorem on the
trajectory state space. A client must exhibit a genuine target-refresh
component; stationarity alone is intentionally insufficient. -/
abbrev ParticleGibbsRefreshCertificate
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps) :=
  RefreshDecomposition
    (trajectoryParticleGibbsKernel (Particle := Particle)
      initial steps hnormalizer)
    (trajectoryTarget (Particle := Particle) initial steps hnormalizer)

/-- A concrete support witness for positive-horizon particle Gibbs. For every
pair of trajectories, one selected-particle state in the current fiber must
have positive extended-target mass and one positive terminal-index refresh
edge must reach the proposed fiber. Unlike a blanket positivity assumption on
the collapsed matrix, this exposes the exact conditional-SMC obligation. -/
def ParticleGibbsFiberConnectivity
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps) : Prop :=
  ∀ current proposed : Trajectory steps,
    ∃ liftCurrent liftProposed : History (Particle := Particle) steps × Particle,
      selectedTrajectoryVector steps liftCurrent = current ∧
      selectedTrajectoryVector steps liftProposed = proposed ∧
      0 < (selectedParticleTarget (Particle := Particle)
        initial steps hnormalizer).mass liftCurrent ∧
      0 < (selectedIndexRefreshKernel (Particle := Particle) steps).prob
        liftCurrent liftProposed

/-- Purely combinatorial condition: every pair of trajectories can occur as
two terminal genealogies in one particle history. For bootstrap particle
Gibbs this is the support property supplied by having at least two lineages. -/
def ParticleGibbsPairRealizable
    (steps : List (FeynmanKacStep Sample)) : Prop :=
  ∀ current proposed : Trajectory steps,
    ∃ history : History (Particle := Particle) steps, ∃ i j : Particle,
      selectedTrajectoryVector steps (history, i) = current ∧
      selectedTrajectoryVector steps (history, j) = proposed

omit [DecidableEq Sample] in
/-- Two Boolean-indexed particles realize every pair of finite trajectories
by following the two identity-ancestry lineages constructed above. -/
theorem particleGibbsPairRealizable_bool
    (steps : List (FeynmanKacStep Sample)) :
    ParticleGibbsPairRealizable (Particle := Bool) steps := by
  intro current proposed
  exact ⟨pairedBoolHistory steps current proposed, false, true,
    selectedTrajectoryVector_pairedBoolHistory_false steps current proposed,
    selectedTrajectoryVector_pairedBoolHistory_true steps current proposed⟩

/-- Full-support model ingredients reduce the analytic particle-Gibbs support
obligation to simultaneous realizability of two genealogies. -/
theorem particleGibbsFiberConnectivity_of_pairRealizable
    (initial : Distribution Sample) (hinitial : ∀ x, 0 < initial.mass x)
    (steps : List (FeynmanKacStep Sample))
    (hsupport : FeynmanKacFullSupport steps)
    (hnormalizer : 0 < normalizingConstant initial steps)
    (hrealizable : ParticleGibbsPairRealizable (Particle := Particle) steps) :
    ParticleGibbsFiberConnectivity (Particle := Particle)
      initial steps hnormalizer := by
  intro current proposed
  obtain ⟨history, i, j, hcurrent, hproposed⟩ :=
    hrealizable current proposed
  refine ⟨(history, i), (history, j), hcurrent, hproposed,
    selectedParticleTarget_mass_pos initial hinitial steps hsupport
      hnormalizer (history, i), ?_⟩
  simp [selectedIndexRefreshKernel, liftSnd, uniformIndexKernel]
  exact Fintype.card_pos

/-- Fiber connectivity makes every entry of the collapsed trajectory kernel
strictly positive. -/
theorem trajectoryParticleGibbsKernel_prob_pos_of_fiberConnectivity
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps)
    (hconnect : ParticleGibbsFiberConnectivity (Particle := Particle)
      initial steps hnormalizer)
    (current proposed : Trajectory steps) :
    0 < (trajectoryParticleGibbsKernel (Particle := Particle)
      initial steps hnormalizer).prob current proposed := by
  obtain ⟨liftCurrent, liftProposed, hcurrent, hproposed, htarget, hedge⟩ :=
    hconnect current proposed
  exact Mcmc.Finite.Conditional.collapsedKernel_prob_pos_of_witness
    (selectedParticleTarget (Particle := Particle) initial steps hnormalizer)
    (selectedTrajectoryVector steps)
    (selectedIndexRefreshKernel (Particle := Particle) steps)
    current proposed liftCurrent liftProposed hcurrent hproposed htarget hedge

/-- Positive-horizon finite particle Gibbs converges geometrically whenever
the concrete conditional-SMC construction supplies a positive refresh
certificate.  The bound is uniform over the initial extended state law. -/
theorem particleGibbs_totalVariation_le_geometric
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps)
    (certificate : ParticleGibbsRefreshCertificate (Particle := Particle)
      initial steps hnormalizer)
    (initialLaw : Distribution (Trajectory steps))
    (n : ℕ) :
    Nonhomogeneous.distributionTotalVariation
      (Nonhomogeneous.iterateLaw initialLaw
        (trajectoryParticleGibbsKernel (Particle := Particle)
          initial steps hnormalizer) n)
      (trajectoryTarget (Particle := Particle) initial steps hnormalizer) ≤
      certificate.rate ^ n :=
  certificate.iterateLaw_totalVariation_le initialLaw n

theorem particleGibbs_totalVariation_tendsto_zero
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps)
    (certificate : ParticleGibbsRefreshCertificate (Particle := Particle)
      initial steps hnormalizer)
    (hpositive : 0 < certificate.coefficient)
    (initialLaw : Distribution (Trajectory steps)) :
    Filter.Tendsto (fun n =>
      Nonhomogeneous.distributionTotalVariation
        (Nonhomogeneous.iterateLaw initialLaw
          (trajectoryParticleGibbsKernel (Particle := Particle)
            initial steps hnormalizer) n)
        (trajectoryTarget (Particle := Particle) initial steps hnormalizer))
      Filter.atTop (nhds 0) :=
  certificate.iterateLaw_totalVariation_tendsto_zero hpositive initialLaw

/-- A direct positive-horizon convergence theorem: strict positivity of the
trajectory transition matrix is a sufficient, checkable support condition.
The generic finite construction supplies an explicit (conservative) positive
refresh coefficient automatically. -/
theorem particleGibbs_totalVariation_tendsto_zero_of_strictlyPositive
    [Nonempty Sample]
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps)
    (hpositive : ∀ current proposed,
      0 < (trajectoryParticleGibbsKernel (Particle := Particle)
        initial steps hnormalizer).prob current proposed)
    (initialLaw : Distribution (Trajectory steps)) :
    Filter.Tendsto (fun n =>
      Nonhomogeneous.distributionTotalVariation
        (Nonhomogeneous.iterateLaw initialLaw
          (trajectoryParticleGibbsKernel (Particle := Particle)
            initial steps hnormalizer) n)
        (trajectoryTarget (Particle := Particle) initial steps hnormalizer))
      Filter.atTop (nhds 0) := by
  letI : Nonempty (Trajectory steps) :=
    ⟨⟨List.replicate (steps.length + 1)
        (Classical.choice ‹Nonempty Sample›), by simp⟩⟩
  let certificate := RefreshDecomposition.ofStrictlyPositive hpositive
    (trajectoryParticleGibbsKernel_stationary (Particle := Particle)
      initial steps hnormalizer)
  exact certificate.iterateLaw_totalVariation_tendsto_zero
    (RefreshDecomposition.ofStrictlyPositive_coefficient_pos hpositive
      (trajectoryParticleGibbsKernel_stationary (Particle := Particle)
        initial steps hnormalizer)) initialLaw

/-- A client-facing positive-horizon convergence theorem stated directly in
terms of conditional-SMC fiber connectivity. -/
theorem particleGibbs_totalVariation_tendsto_zero_of_fiberConnectivity
    [Nonempty Sample]
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps)
    (hconnect : ParticleGibbsFiberConnectivity (Particle := Particle)
      initial steps hnormalizer)
    (initialLaw : Distribution (Trajectory steps)) :
    Filter.Tendsto (fun n =>
      Nonhomogeneous.distributionTotalVariation
        (Nonhomogeneous.iterateLaw initialLaw
          (trajectoryParticleGibbsKernel (Particle := Particle)
            initial steps hnormalizer) n)
        (trajectoryTarget (Particle := Particle) initial steps hnormalizer))
      Filter.atTop (nhds 0) :=
  particleGibbs_totalVariation_tendsto_zero_of_strictlyPositive
    initial steps hnormalizer
    (trajectoryParticleGibbsKernel_prob_pos_of_fiberConnectivity
      initial steps hnormalizer hconnect) initialLaw

/-- A fully model-checkable positive-horizon result for two-particle bootstrap
particle Gibbs: positive initial mass and full-support propagation imply TV
convergence from every initial trajectory law. Potentials require no extra
assumption because `FeynmanKacStep` stores strict positivity. -/
theorem particleGibbs_bool_totalVariation_tendsto_zero_of_fullSupport
    [Nonempty Sample]
    (initial : Distribution Sample) (hinitial : ∀ x, 0 < initial.mass x)
    (steps : List (FeynmanKacStep Sample))
    (hsupport : FeynmanKacFullSupport steps)
    (hnormalizer : 0 < normalizingConstant initial steps)
    (initialLaw : Distribution (Trajectory steps)) :
    Filter.Tendsto (fun n =>
      Nonhomogeneous.distributionTotalVariation
        (Nonhomogeneous.iterateLaw initialLaw
          (trajectoryParticleGibbsKernel (Particle := Bool)
            initial steps hnormalizer) n)
        (trajectoryTarget (Particle := Bool) initial steps hnormalizer))
      Filter.atTop (nhds 0) := by
  apply particleGibbs_totalVariation_tendsto_zero_of_fiberConnectivity
  exact particleGibbsFiberConnectivity_of_pairRealizable
    initial hinitial steps hsupport hnormalizer
      (particleGibbsPairRealizable_bool steps)

end ParticleGibbs

end Mcmc.Finite.MarkovKernel
