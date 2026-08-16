import Mcmc.Kernel.CoupledChain
import Mcmc.Kernel.MeetingDrift
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# Telescoping estimators from lagged coupled chains

This module formalizes the finite-horizon algebra underlying the unbiased
coupled-MCMC estimator.  The paired path starts at `(X₁,Y₀)`, so the base
term `h(Y₀)` followed by corrections `h(Xₙ₊₁)-h(Yₙ)` telescopes in
expectation to the ordinary chain expectation at the final horizon.
-/

open MeasureTheory
open scoped ProbabilityTheory BigOperators

namespace Mcmc
namespace Kernel

open ProbabilityTheory

variable {α : Type*} [MeasurableSpace α]

/-- Advancing an already one-step-evolved law for `n` further transitions is
the same as advancing the original law for `n+1` transitions. -/
theorem lawAtTime_comp_succ
    (initial : Measure α) (transition : Kernel α α)
    [IsMarkovKernel transition] (n : ℕ) :
    lawAtTime (transition ∘ₘ initial) transition n =
      lawAtTime initial transition (n + 1) := by
  rw [lawAtTime, lawAtTime, Measure.comp_assoc]
  change (transition ^ n * transition) ∘ₘ initial =
    (transition ^ (n + 1)) ∘ₘ initial
  rw [pow_succ]

/-- First-coordinate marginal of the lagged paired path at paired time `n`:
it is the ordinary chain law at time `n+1`. -/
theorem map_laggedPathLaw_fst_atTime
    (initialCoupling : Measure (α × α)) (initial : Measure α)
    (transition : Kernel α α) [IsMarkovKernel transition]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (hinitial : IsMeasureCoupling initialCoupling initial initial)
    (hcoupled : IsCoupling coupled transition transition) (n : ℕ) :
    Measure.map (fun path : ℕ → α × α => (path n).1)
        (pathLaw (laggedInitialMeasure initialCoupling transition) coupled) =
      lawAtTime initial transition (n + 1) := by
  have hlagged := laggedInitialMeasure_isMeasureCoupling initialCoupling
    initial transition hinitial
  have htime := lawAtTime_isMeasureCoupling
    (laggedInitialMeasure initialCoupling transition)
    (transition ∘ₘ initial) initial coupled transition transition
    hlagged hcoupled n
  change Measure.map (Prod.fst ∘ fun path : ℕ → α × α => path n)
      (pathLaw (laggedInitialMeasure initialCoupling transition) coupled) = _
  rw [← Measure.map_map measurable_fst (measurable_pi_apply n),
    pathLaw_map_atTime]
  exact htime.fst.trans (lawAtTime_comp_succ initial transition n)

/-- Second-coordinate marginal of the lagged paired path at paired time `n`:
it is the ordinary chain law at time `n`. -/
theorem map_laggedPathLaw_snd_atTime
    (initialCoupling : Measure (α × α)) (initial : Measure α)
    (transition : Kernel α α) [IsMarkovKernel transition]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (hinitial : IsMeasureCoupling initialCoupling initial initial)
    (hcoupled : IsCoupling coupled transition transition) (n : ℕ) :
    Measure.map (fun path : ℕ → α × α => (path n).2)
        (pathLaw (laggedInitialMeasure initialCoupling transition) coupled) =
      lawAtTime initial transition n := by
  have hlagged := laggedInitialMeasure_isMeasureCoupling initialCoupling
    initial transition hinitial
  have htime := lawAtTime_isMeasureCoupling
    (laggedInitialMeasure initialCoupling transition)
    (transition ∘ₘ initial) initial coupled transition transition
    hlagged hcoupled n
  change Measure.map (Prod.snd ∘ fun path : ℕ → α × α => path n)
      (pathLaw (laggedInitialMeasure initialCoupling transition) coupled) = _
  rw [← Measure.map_map measurable_snd (measurable_pi_apply n),
    pathLaw_map_atTime]
  exact htime.snd

/-- `Lᵖ` norm of a first-coordinate path observation equals its norm under
the corresponding ordinary-chain marginal. -/
theorem eLpNorm_laggedPath_fst_atTime
    (initialCoupling : Measure (α × α)) (initial : Measure α)
    (transition : Kernel α α) [IsMarkovKernel transition]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (hinitial : IsMeasureCoupling initialCoupling initial initial)
    (hcoupled : IsCoupling coupled transition transition)
    (h : α → ℝ) (hh : Measurable h) (p : ENNReal) (n : ℕ) :
    eLpNorm (fun path : ℕ → α × α => h (path n).1) p
        (pathLaw (laggedInitialMeasure initialCoupling transition) coupled) =
      eLpNorm h p (lawAtTime initial transition (n + 1)) := by
  rw [← map_laggedPathLaw_fst_atTime initialCoupling initial transition
    coupled hinitial hcoupled n]
  exact (eLpNorm_map_measure hh.aestronglyMeasurable
    ((measurable_pi_apply n).fst.aemeasurable)).symm

/-- `Lᵖ` norm of a second-coordinate path observation equals its norm under
the corresponding ordinary-chain marginal. -/
theorem eLpNorm_laggedPath_snd_atTime
    (initialCoupling : Measure (α × α)) (initial : Measure α)
    (transition : Kernel α α) [IsMarkovKernel transition]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (hinitial : IsMeasureCoupling initialCoupling initial initial)
    (hcoupled : IsCoupling coupled transition transition)
    (h : α → ℝ) (hh : Measurable h) (p : ENNReal) (n : ℕ) :
    eLpNorm (fun path : ℕ → α × α => h (path n).2) p
        (pathLaw (laggedInitialMeasure initialCoupling transition) coupled) =
      eLpNorm h p (lawAtTime initial transition n) := by
  rw [← map_laggedPathLaw_snd_atTime initialCoupling initial transition
    coupled hinitial hcoupled n]
  exact (eLpNorm_map_measure hh.aestronglyMeasurable
    ((measurable_pi_apply n).snd.aemeasurable)).symm

/-- Finite-horizon lagged telescoping estimator. At horizon `N` it uses the
base observation `h(Y₀)` and corrections through
`h(X_{N+1})-h(Y_N)`. Under a faithful sticky coupling, corrections after the
meeting time vanish automatically. -/
noncomputable def laggedTelescopingEstimator
    (h : α → ℝ) (N : ℕ) (path : ℕ → α × α) : ℝ :=
  h (path 0).2 +
    Finset.sum (Finset.range (N + 1))
      (fun n => h (path n).1 - h (path n).2)

/-- The time-`n` correction, explicitly stopped once exact meeting has
occurred.  This definition makes its support—and hence its moment bounds—a
direct consequence of the exact-meeting tail. -/
noncomputable def stoppedLaggedCorrection
    (h : α → ℝ) (n : ℕ) (path : ℕ → α × α) : ℝ :=
  (exactMeetingFailureEvent n).indicator
    (fun path => h (path n).1 - h (path n).2) path

/-- Finite-horizon estimator formed from explicitly stopped corrections. -/
noncomputable def stoppedLaggedEstimator
    (h : α → ℝ) (N : ℕ) (path : ℕ → α × α) : ℝ :=
  h (path 0).2 +
    Finset.sum (Finset.range (N + 1))
      (fun n => stoppedLaggedCorrection h n path)

/-- The infinite stopped estimator. Summability and unbiasedness are proved
below from a geometric meeting tail and marginal convergence. -/
noncomputable def stoppedLaggedUnbiasedEstimator
    (h : α → ℝ) (path : ℕ → α × α) : ℝ :=
  h (path 0).2 + ∑' n : ℕ, stoppedLaggedCorrection h n path

/-- On a faithful path, explicit stopping does not alter a correction: before
meeting the indicator is one, and after meeting the two coordinates agree. -/
theorem stoppedLaggedCorrection_eq_of_faithfulPath
    [MeasurableEq α] (h : α → ℝ) (n : ℕ) {path : ℕ → α × α}
    (hpath : IsFaithfulPath path) :
    stoppedLaggedCorrection h n path =
      h (path n).1 - h (path n).2 := by
  by_cases hdiag : (path n).1 = (path n).2
  · simp [stoppedLaggedCorrection, hdiag]
  · have hfail : path ∈ exactMeetingFailureEvent n :=
      (hpath.mem_exactMeetingFailureEvent_iff n).2 hdiag
    simp [stoppedLaggedCorrection, hfail]

/-- Consequently, the stopped and ordinary finite estimators agree on every
faithful path. -/
theorem stoppedLaggedEstimator_eq_of_faithfulPath
    [MeasurableEq α] (h : α → ℝ) (N : ℕ) {path : ℕ → α × α}
    (hpath : IsFaithfulPath path) :
    stoppedLaggedEstimator h N path = laggedTelescopingEstimator h N path := by
  unfold stoppedLaggedEstimator laggedTelescopingEstimator
  congr 1
  apply Finset.sum_congr rfl
  intro n _hn
  exact stoppedLaggedCorrection_eq_of_faithfulPath h n hpath

theorem measurable_stoppedLaggedCorrection
    [MeasurableEq α] (h : α → ℝ) (hh : Measurable h) (n : ℕ) :
    Measurable (stoppedLaggedCorrection h n) := by
  unfold stoppedLaggedCorrection
  exact (hh.comp (measurable_pi_apply n).fst).sub
    (hh.comp (measurable_pi_apply n).snd) |>.indicator
      (measurableSet_exactMeetingFailureEvent n)

theorem measurable_stoppedLaggedEstimator
    [MeasurableEq α] (h : α → ℝ) (hh : Measurable h) (N : ℕ) :
    Measurable (stoppedLaggedEstimator h N) := by
  unfold stoppedLaggedEstimator
  apply (hh.comp (measurable_pi_apply 0).snd).add
  exact Finset.measurable_sum _ fun n _ =>
    measurable_stoppedLaggedCorrection h hh n

/-- A uniformly bounded observable gives a tail-weighted `L¹` bound for each
stopped correction. -/
theorem lintegral_enorm_stoppedLaggedCorrection_le
    [MeasurableEq α] (μ : Measure (ℕ → α × α))
    (h : α → ℝ) {B : ℝ} (hhB : ∀ x, ‖h x‖ ≤ B) (n : ℕ) :
    ∫⁻ path, ‖stoppedLaggedCorrection h n path‖ₑ ∂μ ≤
      ENNReal.ofReal (2 * B) * exactMeetingTail μ n := by
  let event := exactMeetingFailureEvent (α := α) n
  have hpoint (path : ℕ → α × α) :
      ‖stoppedLaggedCorrection h n path‖ₑ ≤
        event.indicator (fun _ => ENNReal.ofReal (2 * B)) path := by
    by_cases hp : path ∈ event
    · change ‖event.indicator
          (fun path => h (path n).1 - h (path n).2) path‖ₑ ≤ _
      rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, ← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal
      exact (norm_sub_le (h (path n).1) (h (path n).2)).trans
        ((add_le_add (hhB _) (hhB _)).trans_eq (by ring))
    · change ‖event.indicator
          (fun path => h (path n).1 - h (path n).2) path‖ₑ ≤ _
      simp [Set.indicator_of_notMem hp]
  calc
    _ ≤ ∫⁻ path, event.indicator (fun _ => ENNReal.ofReal (2 * B)) path ∂μ :=
      lintegral_mono hpoint
    _ = ENNReal.ofReal (2 * B) * μ event := by
      rw [lintegral_indicator (measurableSet_exactMeetingFailureEvent n),
        setLIntegral_const]
    _ = _ := by rfl

/-- The corresponding `L²` bound is the uniform correction bound multiplied
by the square root of the meeting tail. -/
theorem eLpNorm_two_stoppedLaggedCorrection_le
    [MeasurableEq α] (μ : Measure (ℕ → α × α))
    (h : α → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hhB : ∀ x, ‖h x‖ ≤ B) (n : ℕ) :
    eLpNorm (stoppedLaggedCorrection h n) 2 μ ≤
      ENNReal.ofReal (2 * B) * exactMeetingTail μ n ^ (1 / (2 : ℝ)) := by
  let event := exactMeetingFailureEvent (α := α) n
  have hdist (path : ℕ → α × α) (_hpath : path ∈ event) :
      dist (h (path n).1) (h (path n).2) ≤ 2 * B := by
    rw [dist_eq_norm]
    exact (norm_sub_le (h (path n).1) (h (path n).2)).trans
      ((add_le_add (hhB _) (hhB _)).trans_eq (by ring))
  have hbound := eLpNorm_indicator_sub_le_of_dist_bdd
    (p := (2 : ENNReal)) μ (by norm_num)
    (measurableSet_exactMeetingFailureEvent n) (by positivity : 0 ≤ 2 * B) hdist
  change eLpNorm
      (event.indicator (fun path => h (path n).1 - h (path n).2)) 2 μ ≤ _
  convert hbound using 1
  · congr 2
  · norm_num [event, exactMeetingTail]

/-- A uniform `Lᵖ` moment bound with `p ≥ 2` controls the `L²` size of a
stopped correction by a positive power of its meeting-tail probability. -/
theorem eLpNorm_two_stoppedLaggedCorrection_le_of_moment
    [MeasurableEq α] (μ : Measure (ℕ → α × α))
    (h : α → ℝ) (hh : Measurable h) (p : ENNReal)
    (hp : (2 : ENNReal) ≤ p) (M : ENNReal)
    (hmoment : ∀ n,
      eLpNorm (fun path : ℕ → α × α => h (path n).1) p μ ≤ M ∧
      eLpNorm (fun path : ℕ → α × α => h (path n).2) p μ ≤ M)
    (n : ℕ) :
    eLpNorm (stoppedLaggedCorrection h n) 2 μ ≤
      (M + M) * exactMeetingTail μ n ^
        (1 / (2 : ENNReal).toReal - 1 / p.toReal) := by
  let event := exactMeetingFailureEvent (α := α) n
  let f : (ℕ → α × α) → ℝ := fun path => h (path n).1
  let g : (ℕ → α × α) → ℝ := fun path => h (path n).2
  have hf : AEStronglyMeasurable f μ :=
    (hh.comp (measurable_pi_apply n).fst).aestronglyMeasurable
  have hg : AEStronglyMeasurable g μ :=
    (hh.comp (measurable_pi_apply n).snd).aestronglyMeasurable
  have hdiff : eLpNorm (f - g) p (μ.restrict event) ≤ M + M := by
    calc
      _ ≤ eLpNorm f p (μ.restrict event) +
          eLpNorm g p (μ.restrict event) :=
        eLpNorm_sub_le hf.restrict hg.restrict (le_trans (by norm_num) hp)
      _ ≤ M + M := add_le_add
        ((eLpNorm_restrict_le f p μ event).trans (hmoment n).1)
        ((eLpNorm_restrict_le g p μ event).trans (hmoment n).2)
  change eLpNorm (event.indicator (fun path => f path - g path)) 2 μ ≤ _
  rw [show (fun path => f path - g path) = f - g by rfl,
    eLpNorm_indicator_eq_eLpNorm_restrict
      (measurableSet_exactMeetingFailureEvent n)]
  calc
    _ ≤ eLpNorm (f - g) p (μ.restrict event) *
        (μ.restrict event) Set.univ ^
          (1 / (2 : ENNReal).toReal - 1 / p.toReal) :=
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp
        (hf.sub hg).restrict
    _ ≤ (M + M) * μ event ^
        (1 / (2 : ENNReal).toReal - 1 / p.toReal) := by
      rw [Measure.restrict_apply_univ]
      exact mul_le_mul_left hdiff _
    _ = _ := by rfl

/-- Under a geometric meeting tail, the `L¹` sizes of all stopped corrections
are summable. -/
theorem tsum_lintegral_enorm_stoppedLaggedCorrection_ne_top
    [MeasurableEq α] (μ : Measure (ℕ → α × α))
    (h : α → ℝ) {B : ℝ} (hhB : ∀ x, ‖h x‖ ≤ B)
    (C rate : ENNReal) (hC : C ≠ ⊤) (hrate : rate < 1)
    (htail : ∀ n, exactMeetingTail μ n ≤ C * rate ^ n) :
    (∑' n : ℕ, ∫⁻ path, ‖stoppedLaggedCorrection h n path‖ₑ ∂μ) ≠ ⊤ := by
  have htailSum : (∑' n : ℕ, exactMeetingTail μ n) ≠ ⊤ :=
    ne_top_of_le_ne_top
      (ENNReal.mul_ne_top hC (ENNReal.inv_ne_top.mpr
        (ne_of_gt (tsub_pos_iff_lt.mpr hrate)))) (by
        calc
          _ ≤ ∑' n : ℕ, C * rate ^ n := ENNReal.tsum_le_tsum htail
          _ = C * ∑' n : ℕ, rate ^ n := by rw [ENNReal.tsum_mul_left]
          _ = C * (1 - rate)⁻¹ := by rw [ENNReal.tsum_geometric])
  apply ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top htailSum)
  calc
      _ ≤ ∑' n : ℕ, ENNReal.ofReal (2 * B) * exactMeetingTail μ n :=
        ENNReal.tsum_le_tsum fun n =>
          lintegral_enorm_stoppedLaggedCorrection_le μ h hhB n
      _ = _ := by rw [ENNReal.tsum_mul_left]

/-- A geometric meeting tail has summable square roots. This is the moment
estimate needed for an `L²` sum of uniformly bounded corrections. -/
theorem tsum_rpow_half_exactMeetingTail_ne_top_of_geometric
    (μ : Measure (ℕ → α × α)) (C rate : ENNReal)
    (hC : C ≠ ⊤) (hrate : rate < 1)
    (htail : ∀ n, exactMeetingTail μ n ≤ C * rate ^ n) :
    (∑' n : ℕ, exactMeetingTail μ n ^ (1 / (2 : ℝ))) ≠ ⊤ := by
  let q : ENNReal := rate ^ (1 / (2 : ℝ))
  have hq : q < 1 := ENNReal.rpow_lt_one hrate (by norm_num)
  have hpoint (n : ℕ) :
      exactMeetingTail μ n ^ (1 / (2 : ℝ)) ≤
        C ^ (1 / (2 : ℝ)) * q ^ n := by
    calc
      _ ≤ (C * rate ^ n) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow (htail n) (by norm_num)
      _ = C ^ (1 / (2 : ℝ)) * (rate ^ n) ^ (1 / (2 : ℝ)) := by
        rw [ENNReal.mul_rpow_of_nonneg]
        norm_num
      _ = C ^ (1 / (2 : ℝ)) * q ^ n := by
        congr 1
        simp only [q, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        congr 1
        ring
  apply ne_top_of_le_ne_top
    (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (y := 1 / (2 : ℝ)) (by norm_num) hC)
      (ENNReal.inv_ne_top.mpr
        (ne_of_gt (tsub_pos_iff_lt.mpr hq))))
  calc
    _ ≤ ∑' n : ℕ, C ^ (1 / (2 : ℝ)) * q ^ n :=
      ENNReal.tsum_le_tsum hpoint
    _ = C ^ (1 / (2 : ℝ)) * ∑' n : ℕ, q ^ n := by
      rw [ENNReal.tsum_mul_left]
    _ = C ^ (1 / (2 : ℝ)) * (1 - q)⁻¹ := by
      rw [ENNReal.tsum_geometric]

/-- More generally, every positive power of a geometric meeting tail is
summable. -/
theorem tsum_rpow_exactMeetingTail_ne_top_of_geometric
    (μ : Measure (ℕ → α × α)) (C rate : ENNReal) {z : ℝ}
    (hz : 0 < z) (hC : C ≠ ⊤) (hrate : rate < 1)
    (htail : ∀ n, exactMeetingTail μ n ≤ C * rate ^ n) :
    (∑' n : ℕ, exactMeetingTail μ n ^ z) ≠ ⊤ := by
  let q : ENNReal := rate ^ z
  have hq : q < 1 := ENNReal.rpow_lt_one hrate hz
  have hpoint (n : ℕ) :
      exactMeetingTail μ n ^ z ≤ C ^ z * q ^ n := by
    calc
      _ ≤ (C * rate ^ n) ^ z :=
        ENNReal.rpow_le_rpow (htail n) hz.le
      _ = C ^ z * (rate ^ n) ^ z := by
        rw [ENNReal.mul_rpow_of_nonneg]
        exact hz.le
      _ = C ^ z * q ^ n := by
        congr 1
        simp only [q, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        congr 1
        ring
  apply ne_top_of_le_ne_top
    (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hz.le hC)
      (ENNReal.inv_ne_top.mpr
        (ne_of_gt (tsub_pos_iff_lt.mpr hq))))
  calc
    _ ≤ ∑' n : ℕ, C ^ z * q ^ n := ENNReal.tsum_le_tsum hpoint
    _ = C ^ z * ∑' n : ℕ, q ^ n := by rw [ENNReal.tsum_mul_left]
    _ = C ^ z * (1 - q)⁻¹ := by rw [ENNReal.tsum_geometric]

/-- Consequently the `L²` norms of all bounded stopped corrections are
summable under a geometric meeting tail. -/
theorem tsum_eLpNorm_two_stoppedLaggedCorrection_ne_top_of_geometric
    [MeasurableEq α] (μ : Measure (ℕ → α × α))
    (h : α → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hhB : ∀ x, ‖h x‖ ≤ B)
    (C rate : ENNReal) (hC : C ≠ ⊤) (hrate : rate < 1)
    (htail : ∀ n, exactMeetingTail μ n ≤ C * rate ^ n) :
    (∑' n : ℕ, eLpNorm (stoppedLaggedCorrection h n) 2 μ) ≠ ⊤ := by
  have hsqrt := tsum_rpow_half_exactMeetingTail_ne_top_of_geometric
    μ C rate hC hrate htail
  apply ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsqrt)
  calc
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (2 * B) *
        exactMeetingTail μ n ^ (1 / (2 : ℝ)) :=
      ENNReal.tsum_le_tsum fun n =>
        eLpNorm_two_stoppedLaggedCorrection_le μ h hB hhB n
    _ = ENNReal.ofReal (2 * B) *
        ∑' n : ℕ, exactMeetingTail μ n ^ (1 / (2 : ℝ)) := by
      rw [ENNReal.tsum_mul_left]

/-- A uniform higher-moment bound and a geometric meeting tail make the
`L²` correction norms summable. The positivity premise is exactly the
Hölder exponent `1/2 - 1/p > 0`. -/
theorem tsum_eLpNorm_two_stoppedLaggedCorrection_ne_top_of_moment_geometric
    [MeasurableEq α] (μ : Measure (ℕ → α × α))
    (h : α → ℝ) (hh : Measurable h) (p : ENNReal)
    (hp : (2 : ENNReal) ≤ p)
    (htheta : 0 < 1 / (2 : ENNReal).toReal - 1 / p.toReal)
    (M : ENNReal) (hM : M ≠ ⊤)
    (hmoment : ∀ n,
      eLpNorm (fun path : ℕ → α × α => h (path n).1) p μ ≤ M ∧
      eLpNorm (fun path : ℕ → α × α => h (path n).2) p μ ≤ M)
    (C rate : ENNReal) (hC : C ≠ ⊤) (hrate : rate < 1)
    (htail : ∀ n, exactMeetingTail μ n ≤ C * rate ^ n) :
    (∑' n : ℕ, eLpNorm (stoppedLaggedCorrection h n) 2 μ) ≠ ⊤ := by
  let theta : ℝ := 1 / (2 : ENNReal).toReal - 1 / p.toReal
  have htailPower : (∑' n : ℕ, exactMeetingTail μ n ^ theta) ≠ ⊤ :=
    tsum_rpow_exactMeetingTail_ne_top_of_geometric
      μ C rate htheta hC hrate htail
  apply ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.add_ne_top.mpr ⟨hM, hM⟩) htailPower)
  calc
    _ ≤ ∑' n : ℕ, (M + M) * exactMeetingTail μ n ^ theta :=
      ENNReal.tsum_le_tsum fun n =>
        eLpNorm_two_stoppedLaggedCorrection_le_of_moment
          μ h hh p hp M hmoment n
    _ = (M + M) * ∑' n : ℕ, exactMeetingTail μ n ^ theta := by
      rw [ENNReal.tsum_mul_left]

/-- Summable `L¹` correction sizes make the pointwise stopped series
integrable. -/
theorem integrable_tsum_stoppedLaggedCorrection
    [MeasurableEq α] (μ : Measure (ℕ → α × α))
    (h : α → ℝ) (hh : Measurable h)
    (hsum : (∑' n : ℕ,
      ∫⁻ path, ‖stoppedLaggedCorrection h n path‖ₑ ∂μ) ≠ ⊤) :
    Integrable (fun path => ∑' n : ℕ, stoppedLaggedCorrection h n path) μ := by
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (stoppedLaggedCorrection h n) μ :=
    (measurable_stoppedLaggedCorrection h hh n).aestronglyMeasurable
  refine ⟨AEStronglyMeasurable.tsum hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  apply lt_of_le_of_lt _ hsum.lt_top
  calc
    ∫⁻ path, ‖∑' n : ℕ, stoppedLaggedCorrection h n path‖ₑ ∂μ ≤
        ∫⁻ path, ∑' n : ℕ, ‖stoppedLaggedCorrection h n path‖ₑ ∂μ :=
      lintegral_mono fun path => enorm_tsum_le_tsum_enorm
    _ = ∑' n : ℕ,
        ∫⁻ path, ‖stoppedLaggedCorrection h n path‖ₑ ∂μ := by
      rw [lintegral_tsum]
      exact fun n => (hmeas n).enorm

/-- The complete stopped estimator is integrable when its base observation is
integrable and its correction sizes are summable. -/
theorem integrable_stoppedLaggedUnbiasedEstimator
    [MeasurableEq α] (μ : Measure (ℕ → α × α))
    (h : α → ℝ) (hh : Measurable h)
    (hbase : Integrable (fun path : ℕ → α × α => h (path 0).2) μ)
    (hsum : (∑' n : ℕ,
      ∫⁻ path, ‖stoppedLaggedCorrection h n path‖ₑ ∂μ) ≠ ⊤) :
    Integrable (stoppedLaggedUnbiasedEstimator h) μ := by
  unfold stoppedLaggedUnbiasedEstimator
  exact hbase.add (integrable_tsum_stoppedLaggedCorrection μ h hh hsum)

/-- A square-integrable base observation and summable `L²` correction norms
make the complete stopped estimator square-integrable. -/
theorem memLp_two_stoppedLaggedUnbiasedEstimator_of_summable
    [MeasurableEq α] (μ : Measure (ℕ → α × α))
    (h : α → ℝ) (hh : Measurable h)
    (hbase : MemLp (fun path : ℕ → α × α => h (path 0).2) 2 μ)
    (hnormSum : (∑' n : ℕ,
      eLpNorm (stoppedLaggedCorrection h n) 2 μ) ≠ ⊤) :
    MemLp (stoppedLaggedUnbiasedEstimator h) 2 μ := by
  let correction : ℕ → (ℕ → α × α) → ℝ := stoppedLaggedCorrection h
  have hcorr (n : ℕ) : MemLp (correction n) 2 μ := by
    refine ⟨(measurable_stoppedLaggedCorrection h hh n).aestronglyMeasurable, ?_⟩
    exact lt_of_le_of_lt (ENNReal.le_tsum n) hnormSum.lt_top
  let correctionLp (n : ℕ) : Lp ℝ 2 μ := (hcorr n).toLp (correction n)
  have hLpNormSum : (∑' n : ℕ, ‖correctionLp n‖ₑ) ≠ ⊤ := by
    simpa only [correctionLp, Lp.enorm_toLp] using hnormSum
  let estimatorLp : Lp ℝ 2 μ :=
    hbase.toLp (fun path : ℕ → α × α => h (path 0).2) +
      ∑' n : ℕ, correctionLp n
  have hcorrCoe : ∀ᵐ path ∂μ, ∀ n,
      correctionLp n path = correction n path := by
    rw [ae_all_iff]
    exact fun n => (hcorr n).coeFn_toLp
  have hseriesCoe : ∀ᵐ path ∂μ,
      HasSum (fun n => correctionLp n path)
        ((∑' n : ℕ, correctionLp n) path) :=
    Lp.hasSum_coeFn_tsum hLpNormSum
  have hbaseCoe : ∀ᵐ path ∂μ,
      hbase.toLp (fun path : ℕ → α × α => h (path 0).2) path =
        h (path 0).2 := hbase.coeFn_toLp
  have haddCoe := Lp.coeFn_add
    (hbase.toLp (fun path : ℕ → α × α => h (path 0).2))
    (∑' n : ℕ, correctionLp n)
  have heq : (estimatorLp : (ℕ → α × α) → ℝ) =ᵐ[μ]
      stoppedLaggedUnbiasedEstimator h := by
    filter_upwards [hcorrCoe, hseriesCoe, hbaseCoe, haddCoe] with
      path hcorrPath hseriesPath hbasePath haddPath
    have hseriesCorrection := hseriesPath
    simp_rw [hcorrPath] at hseriesCorrection
    have htsum : (∑' n : ℕ, correction n path) =
        (∑' n : ℕ, correctionLp n) path := hseriesCorrection.tsum_eq
    change (hbase.toLp (fun path : ℕ → α × α => h (path 0).2) +
        ∑' n : ℕ, correctionLp n) path =
      h (path 0).2 + ∑' n : ℕ, correction n path
    rw [haddPath]
    change hbase.toLp (fun path : ℕ → α × α => h (path 0).2) path +
        (∑' n : ℕ, correctionLp n) path =
      h (path 0).2 + ∑' n : ℕ, correction n path
    rw [hbasePath, htsum]
  exact (Lp.memLp estimatorLp).congr_norm
    ((hh.comp (measurable_pi_apply 0).snd).aestronglyMeasurable.add
      (AEStronglyMeasurable.tsum fun n =>
        (measurable_stoppedLaggedCorrection h hh n).aestronglyMeasurable))
    (heq.mono fun _ hx => congrArg norm hx)

/-- On a probability space, summable `L²` correction norms imply summable
`L¹` correction sizes. -/
theorem tsum_lintegral_enorm_stoppedLaggedCorrection_ne_top_of_eLpNorm_two
    [MeasurableEq α] (μ : Measure (ℕ → α × α)) [IsProbabilityMeasure μ]
    (h : α → ℝ) (hh : Measurable h)
    (hsum : (∑' n : ℕ,
      eLpNorm (stoppedLaggedCorrection h n) 2 μ) ≠ ⊤) :
    (∑' n : ℕ, ∫⁻ path,
      ‖stoppedLaggedCorrection h n path‖ₑ ∂μ) ≠ ⊤ := by
  have hpoint (n : ℕ) :
      (∫⁻ path, ‖stoppedLaggedCorrection h n path‖ₑ ∂μ) ≤
        eLpNorm (stoppedLaggedCorrection h n) 2 μ := by
    rw [← eLpNorm_one_eq_lintegral_enorm]
    calc
      _ ≤ eLpNorm (stoppedLaggedCorrection h n) 2 μ *
          μ Set.univ ^
            (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num)
          (measurable_stoppedLaggedCorrection h hh n).aestronglyMeasurable
      _ = _ := by simp
  exact ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum hpoint)

/-- Higher moments yield a finite-variance stopped estimator for unbounded
observables as soon as the base term is square-integrable. -/
theorem memLp_two_stoppedLaggedUnbiasedEstimator_of_moment_geometric
    [MeasurableEq α] (μ : Measure (ℕ → α × α))
    (h : α → ℝ) (hh : Measurable h) (p : ENNReal)
    (hp : (2 : ENNReal) ≤ p)
    (htheta : 0 < 1 / (2 : ENNReal).toReal - 1 / p.toReal)
    (M : ENNReal) (hM : M ≠ ⊤)
    (hmoment : ∀ n,
      eLpNorm (fun path : ℕ → α × α => h (path n).1) p μ ≤ M ∧
      eLpNorm (fun path : ℕ → α × α => h (path n).2) p μ ≤ M)
    (hbase : MemLp (fun path : ℕ → α × α => h (path 0).2) 2 μ)
    (C rate : ENNReal) (hC : C ≠ ⊤) (hrate : rate < 1)
    (htail : ∀ n, exactMeetingTail μ n ≤ C * rate ^ n) :
    MemLp (stoppedLaggedUnbiasedEstimator h) 2 μ := by
  apply memLp_two_stoppedLaggedUnbiasedEstimator_of_summable μ h hh hbase
  exact tsum_eLpNorm_two_stoppedLaggedCorrection_ne_top_of_moment_geometric
    μ h hh p hp htheta M hM hmoment C rate hC hrate htail

/-- For a bounded observable, a geometric meeting tail makes the complete
stopped estimator square-integrable. In particular it has finite variance. -/
theorem memLp_two_stoppedLaggedUnbiasedEstimator_of_geometric
    [MeasurableEq α] (μ : Measure (ℕ → α × α)) [IsFiniteMeasure μ]
    (h : α → ℝ) (hh : Measurable h) {B : ℝ} (hB : 0 ≤ B)
    (hhB : ∀ x, ‖h x‖ ≤ B)
    (C rate : ENNReal) (hC : C ≠ ⊤) (hrate : rate < 1)
    (htail : ∀ n, exactMeetingTail μ n ≤ C * rate ^ n) :
    MemLp (stoppedLaggedUnbiasedEstimator h) 2 μ := by
  let correction : ℕ → (ℕ → α × α) → ℝ := stoppedLaggedCorrection h
  have hnormSum : (∑' n : ℕ, eLpNorm (correction n) 2 μ) ≠ ⊤ :=
    tsum_eLpNorm_two_stoppedLaggedCorrection_ne_top_of_geometric
      μ h hB hhB C rate hC hrate htail
  have hcorr (n : ℕ) : MemLp (correction n) 2 μ := by
    refine ⟨(measurable_stoppedLaggedCorrection h hh n).aestronglyMeasurable, ?_⟩
    exact lt_of_le_of_lt (ENNReal.le_tsum n) hnormSum.lt_top
  have hbase : MemLp (fun path : ℕ → α × α => h (path 0).2) 2 μ :=
    MemLp.of_bound (hh.comp (measurable_pi_apply 0).snd).aestronglyMeasurable
      B (Filter.Eventually.of_forall fun path => hhB (path 0).2)
  let correctionLp (n : ℕ) : Lp ℝ 2 μ := (hcorr n).toLp (correction n)
  have hLpNormSum : (∑' n : ℕ, ‖correctionLp n‖ₑ) ≠ ⊤ := by
    simpa only [correctionLp, Lp.enorm_toLp] using hnormSum
  let estimatorLp : Lp ℝ 2 μ :=
    hbase.toLp (fun path : ℕ → α × α => h (path 0).2) +
      ∑' n : ℕ, correctionLp n
  have hcorrCoe : ∀ᵐ path ∂μ, ∀ n,
      correctionLp n path = correction n path := by
    rw [ae_all_iff]
    exact fun n => (hcorr n).coeFn_toLp
  have hseriesCoe : ∀ᵐ path ∂μ,
      HasSum (fun n => correctionLp n path)
        ((∑' n : ℕ, correctionLp n) path) :=
    Lp.hasSum_coeFn_tsum hLpNormSum
  have hbaseCoe : ∀ᵐ path ∂μ,
      hbase.toLp (fun path : ℕ → α × α => h (path 0).2) path =
        h (path 0).2 := hbase.coeFn_toLp
  have haddCoe := Lp.coeFn_add
    (hbase.toLp (fun path : ℕ → α × α => h (path 0).2))
    (∑' n : ℕ, correctionLp n)
  have heq : (estimatorLp : (ℕ → α × α) → ℝ) =ᵐ[μ]
      stoppedLaggedUnbiasedEstimator h := by
    filter_upwards [hcorrCoe, hseriesCoe, hbaseCoe, haddCoe] with
      path hcorrPath hseriesPath hbasePath haddPath
    have hseriesCorrection := hseriesPath
    simp_rw [hcorrPath] at hseriesCorrection
    have htsum : (∑' n : ℕ, correction n path) =
        (∑' n : ℕ, correctionLp n) path := hseriesCorrection.tsum_eq
    change (hbase.toLp (fun path : ℕ → α × α => h (path 0).2) +
        ∑' n : ℕ, correctionLp n) path =
      h (path 0).2 + ∑' n : ℕ, correction n path
    rw [haddPath]
    change hbase.toLp (fun path : ℕ → α × α => h (path 0).2) path +
        (∑' n : ℕ, correctionLp n) path =
      h (path 0).2 + ∑' n : ℕ, correction n path
    rw [hbasePath, htsum]
  exact (Lp.memLp estimatorLp).congr_norm
    ((hh.comp (measurable_pi_apply 0).snd).aestronglyMeasurable.add
      (AEStronglyMeasurable.tsum fun n =>
        (measurable_stoppedLaggedCorrection h hh n).aestronglyMeasurable))
    (heq.mono fun _ hx => congrArg norm hx)

/-- Explicit second-moment form of the preceding `L²` theorem. -/
theorem integrable_sq_stoppedLaggedUnbiasedEstimator_of_geometric
    [MeasurableEq α] (μ : Measure (ℕ → α × α)) [IsFiniteMeasure μ]
    (h : α → ℝ) (hh : Measurable h) {B : ℝ} (hB : 0 ≤ B)
    (hhB : ∀ x, ‖h x‖ ≤ B)
    (C rate : ENNReal) (hC : C ≠ ⊤) (hrate : rate < 1)
    (htail : ∀ n, exactMeetingTail μ n ≤ C * rate ^ n) :
    Integrable (fun path => stoppedLaggedUnbiasedEstimator h path ^ 2) μ := by
  exact (memLp_two_stoppedLaggedUnbiasedEstimator_of_geometric
    μ h hh hB hhB C rate hC hrate htail).integrable_sq

theorem measurable_laggedTelescopingEstimator
    (h : α → ℝ) (hh : Measurable h) (N : ℕ) :
    Measurable (laggedTelescopingEstimator h N) := by
  unfold laggedTelescopingEstimator
  fun_prop

/-- Integrability of the observable under every finite-time marginal implies
integrability of every coordinate term in the finite estimator. -/
theorem integrable_laggedPath_coordinate
    (initialCoupling : Measure (α × α)) (initial : Measure α)
    (transition : Kernel α α) [IsMarkovKernel transition]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (hinitial : IsMeasureCoupling initialCoupling initial initial)
    (hcoupled : IsCoupling coupled transition transition)
    (h : α → ℝ) (hh : Measurable h)
    (hint : ∀ n, Integrable h (lawAtTime initial transition n)) (n : ℕ) :
    Integrable (fun path : ℕ → α × α => h (path n).1)
        (pathLaw (laggedInitialMeasure initialCoupling transition) coupled) ∧
      Integrable (fun path : ℕ → α × α => h (path n).2)
        (pathLaw (laggedInitialMeasure initialCoupling transition) coupled) := by
  let μ := pathLaw (laggedInitialMeasure initialCoupling transition) coupled
  have hfstMap := map_laggedPathLaw_fst_atTime initialCoupling initial transition
    coupled hinitial hcoupled n
  have hsndMap := map_laggedPathLaw_snd_atTime initialCoupling initial transition
    coupled hinitial hcoupled n
  constructor
  · apply (integrable_map_measure
      (hh.aestronglyMeasurable.mono_measure (by rw [hfstMap]))
      ((measurable_pi_apply n).fst.aemeasurable)).mp
    rw [hfstMap]
    exact hint (n + 1)
  · apply (integrable_map_measure
      (hh.aestronglyMeasurable.mono_measure (by rw [hsndMap]))
      ((measurable_pi_apply n).snd.aemeasurable)).mp
    rw [hsndMap]
    exact hint n

/-- The expectation of the finite lagged estimator is exactly the ordinary
chain expectation at time `N+1`. This is the core unbiased-coupling
telescoping identity; no convergence claim is hidden in the statement. -/
theorem integral_laggedTelescopingEstimator_eq
    (initialCoupling : Measure (α × α)) (initial : Measure α)
    (transition : Kernel α α) [IsMarkovKernel transition]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (hinitial : IsMeasureCoupling initialCoupling initial initial)
    (hcoupled : IsCoupling coupled transition transition)
    (h : α → ℝ) (hh : Measurable h)
    (hint : ∀ n, Integrable h (lawAtTime initial transition n)) (N : ℕ) :
    ∫ path, laggedTelescopingEstimator h N path
        ∂pathLaw (laggedInitialMeasure initialCoupling transition) coupled =
      ∫ x, h x ∂lawAtTime initial transition (N + 1) := by
  let μ := pathLaw (laggedInitialMeasure initialCoupling transition) coupled
  have hcoord := integrable_laggedPath_coordinate initialCoupling initial
    transition coupled hinitial hcoupled h hh hint
  have hfstIntegral (n : ℕ) :
      (∫ path, h (path n).1 ∂μ) =
        ∫ x, h x ∂lawAtTime initial transition (n + 1) := by
    rw [← map_laggedPathLaw_fst_atTime initialCoupling initial transition
      coupled hinitial hcoupled n]
    exact (integral_map ((measurable_pi_apply n).fst.aemeasurable)
      hh.aestronglyMeasurable).symm
  have hsndIntegral (n : ℕ) :
      (∫ path, h (path n).2 ∂μ) =
        ∫ x, h x ∂lawAtTime initial transition n := by
    rw [← map_laggedPathLaw_snd_atTime initialCoupling initial transition
      coupled hinitial hcoupled n]
    exact (integral_map ((measurable_pi_apply n).snd.aemeasurable)
      hh.aestronglyMeasurable).symm
  have hestIntegrable (n : ℕ) :
      Integrable (laggedTelescopingEstimator h n) μ := by
    apply (hcoord 0).2.add
    exact integrable_finsetSum _ fun i _ => (hcoord i).1.sub (hcoord i).2
  induction N with
  | zero =>
      unfold laggedTelescopingEstimator
      simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton]
      change (∫ path, (fun path => h (path 0).2) path +
          (fun path => h (path 0).1 - h (path 0).2) path ∂μ) = _
      calc
        _ = (∫ path, h (path 0).2 ∂μ) +
            ∫ path, h (path 0).1 - h (path 0).2 ∂μ := by
          exact integral_add (hcoord 0).2 ((hcoord 0).1.sub (hcoord 0).2)
        _ = (∫ path, h (path 0).2 ∂μ) +
            ((∫ path, h (path 0).1 ∂μ) -
              ∫ path, h (path 0).2 ∂μ) := by
          rw [integral_sub (hcoord 0).1 (hcoord 0).2]
        _ = _ := by rw [hfstIntegral, hsndIntegral]; ring
  | succ N ih =>
      have hidentity : laggedTelescopingEstimator h (N + 1) =
          fun path => laggedTelescopingEstimator h N path +
            (h (path (N + 1)).1 - h (path (N + 1)).2) := by
        funext path
        unfold laggedTelescopingEstimator
        rw [Finset.sum_range_succ]
        ring
      rw [hidentity]
      change (∫ path, (laggedTelescopingEstimator h N) path +
          (fun path => h (path (N + 1)).1 - h (path (N + 1)).2) path ∂μ) = _
      calc
        _ = (∫ path, laggedTelescopingEstimator h N path ∂μ) +
            ∫ path, h (path (N + 1)).1 - h (path (N + 1)).2 ∂μ := by
          exact integral_add (hestIntegrable N)
            ((hcoord (N + 1)).1.sub (hcoord (N + 1)).2)
        _ = (∫ path, laggedTelescopingEstimator h N path ∂μ) +
            ((∫ path, h (path (N + 1)).1 ∂μ) -
              ∫ path, h (path (N + 1)).2 ∂μ) := by
          rw [integral_sub (hcoord (N + 1)).1 (hcoord (N + 1)).2]
        _ = _ := by rw [ih, hfstIntegral, hsndIntegral]; ring

/-- Therefore any asserted convergence of the ordinary marginal expectations
immediately transfers to the expectations of the finite coupled estimators. -/
theorem tendsto_integral_laggedTelescopingEstimator
    (initialCoupling : Measure (α × α)) (initial : Measure α)
    (transition : Kernel α α) [IsMarkovKernel transition]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (hinitial : IsMeasureCoupling initialCoupling initial initial)
    (hcoupled : IsCoupling coupled transition transition)
    (h : α → ℝ) (hh : Measurable h)
    (hint : ∀ n, Integrable h (lawAtTime initial transition n))
    (targetMean : ℝ)
    (hlimit : Filter.Tendsto
      (fun n => ∫ x, h x ∂lawAtTime initial transition n)
      Filter.atTop (nhds targetMean)) :
    Filter.Tendsto
      (fun N => ∫ path, laggedTelescopingEstimator h N path
        ∂pathLaw (laggedInitialMeasure initialCoupling transition) coupled)
      Filter.atTop (nhds targetMean) := by
  have hshift := hlimit.comp (Filter.tendsto_add_atTop_nat 1)
  simp_rw [integral_laggedTelescopingEstimator_eq initialCoupling initial
    transition coupled hinitial hcoupled h hh hint]
  change Filter.Tendsto
    ((fun n => ∫ x, h x ∂lawAtTime initial transition n) ∘ fun n => n + 1)
      Filter.atTop (nhds targetMean)
  exact hshift

/-- An integrable random variable which is the `L¹` limit of the finite
lagged telescoping estimators is unbiased for the limiting marginal mean.
The `L¹` premise is the exact interchange condition; it is not silently
deduced from meeting alone. -/
theorem integral_laggedUnbiasedEstimator_eq
    (initialCoupling : Measure (α × α)) (initial : Measure α)
    (transition : Kernel α α) [IsMarkovKernel transition]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (hinitial : IsMeasureCoupling initialCoupling initial initial)
    (hcoupled : IsCoupling coupled transition transition)
    (h : α → ℝ) (hh : Measurable h)
    (hint : ∀ n, Integrable h (lawAtTime initial transition n))
    (targetMean : ℝ)
    (hmarginal : Filter.Tendsto
      (fun n => ∫ x, h x ∂lawAtTime initial transition n)
      Filter.atTop (nhds targetMean))
    (estimator : (ℕ → α × α) → ℝ)
    (hestimator : AEStronglyMeasurable estimator
      (pathLaw (laggedInitialMeasure initialCoupling transition) coupled))
    (hL1 : Filter.Tendsto
      (fun N => ∫⁻ path,
        ‖laggedTelescopingEstimator h N path - estimator path‖ₑ
        ∂pathLaw (laggedInitialMeasure initialCoupling transition) coupled)
      Filter.atTop (nhds 0)) :
    (∫ path, estimator path
      ∂pathLaw (laggedInitialMeasure initialCoupling transition) coupled) =
      targetMean := by
  let μ := pathLaw (laggedInitialMeasure initialCoupling transition) coupled
  have hcoord := integrable_laggedPath_coordinate initialCoupling initial
    transition coupled hinitial hcoupled h hh hint
  have hfinite (N : ℕ) : Integrable (laggedTelescopingEstimator h N) μ := by
    unfold laggedTelescopingEstimator
    apply (hcoord 0).2.add
    exact integrable_finsetSum _ fun n _ => (hcoord n).1.sub (hcoord n).2
  have htoEstimator : Filter.Tendsto
      (fun N => ∫ path, laggedTelescopingEstimator h N path ∂μ)
      Filter.atTop (nhds (∫ path, estimator path ∂μ)) := by
    exact tendsto_integral_of_L1 estimator hestimator
      (Filter.Eventually.of_forall hfinite) hL1
  have htoTarget := tendsto_integral_laggedTelescopingEstimator
    initialCoupling initial transition coupled hinitial hcoupled h hh hint
    targetMean hmarginal
  exact tendsto_nhds_unique htoEstimator htoTarget

/-- Summable `L¹` stopped corrections, kernel faithfulness, and marginal
expectation convergence imply unbiasedness of the infinite stopped
estimator. This is the moment-agnostic core theorem. -/
theorem integral_stoppedLaggedUnbiasedEstimator_eq_of_summable
    [MeasurableEq α]
    (initialCoupling : Measure (α × α)) [IsProbabilityMeasure initialCoupling]
    (initial : Measure α)
    (transition : Kernel α α) [IsMarkovKernel transition]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (hinitial : IsMeasureCoupling initialCoupling initial initial)
    (hcoupled : IsCoupling coupled transition transition)
    (h : α → ℝ) (hh : Measurable h)
    (hint : ∀ n, Integrable h (lawAtTime initial transition n))
    (targetMean : ℝ)
    (hmarginal : Filter.Tendsto
      (fun n => ∫ x, h x ∂lawAtTime initial transition n)
      Filter.atTop (nhds targetMean))
    (hsum : (∑' n : ℕ, ∫⁻ path,
      ‖stoppedLaggedCorrection h n path‖ₑ
      ∂pathLaw (laggedInitialMeasure initialCoupling transition) coupled) ≠ ⊤)
    (hfaithful : IsFaithful coupled) :
    (∫ path, stoppedLaggedUnbiasedEstimator h path
      ∂pathLaw (laggedInitialMeasure initialCoupling transition) coupled) =
      targetMean := by
  let μ := pathLaw (laggedInitialMeasure initialCoupling transition) coupled
  let correction : ℕ → (ℕ → α × α) → ℝ := stoppedLaggedCorrection h
  have hcorr (n : ℕ) : Integrable (correction n) μ := by
    refine ⟨(measurable_stoppedLaggedCorrection h hh n).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    exact lt_of_le_of_lt (ENNReal.le_tsum n) hsum.lt_top
  have hcorrNorm : Summable (fun n => ∫ path, ‖correction n path‖ ∂μ) := by
    have hs := ENNReal.summable_toReal hsum
    apply hs.congr
    intro n
    exact (integral_norm_eq_lintegral_enorm
      (hcorr n).aestronglyMeasurable).symm
  have hseries : HasSum (fun n => ∫ path, correction n path ∂μ)
      (∫ path, ∑' n : ℕ, correction n path ∂μ) :=
    hasSum_integral_of_summable_integral_norm hcorr hcorrNorm
  have hcoord := integrable_laggedPath_coordinate initialCoupling initial
    transition coupled hinitial hcoupled h hh hint
  have hbase : Integrable (fun path : ℕ → α × α => h (path 0).2) μ :=
    (hcoord 0).2
  have hfaithfulPath : ∀ᵐ path ∂μ, IsFaithfulPath path :=
    hfaithful.ae_isFaithfulPath
      (laggedInitialMeasure initialCoupling transition) coupled
  have hfiniteIntegral (N : ℕ) :
      (∫ path, stoppedLaggedEstimator h N path ∂μ) =
        ∫ x, h x ∂lawAtTime initial transition (N + 1) := by
    calc
      _ = ∫ path, laggedTelescopingEstimator h N path ∂μ := by
        apply integral_congr_ae
        exact hfaithfulPath.mono fun path hpath =>
          stoppedLaggedEstimator_eq_of_faithfulPath h N hpath
      _ = _ := integral_laggedTelescopingEstimator_eq initialCoupling initial
        transition coupled hinitial hcoupled h hh hint N
  have htoTarget : Filter.Tendsto
      (fun N => ∫ path, stoppedLaggedEstimator h N path ∂μ)
      Filter.atTop (nhds targetMean) := by
    simp_rw [hfiniteIntegral]
    change Filter.Tendsto
      ((fun n => ∫ x, h x ∂lawAtTime initial transition n) ∘ fun n => n + 1)
        Filter.atTop (nhds targetMean)
    exact hmarginal.comp (Filter.tendsto_add_atTop_nat 1)
  have htoInfinite : Filter.Tendsto
      (fun N => ∫ path, stoppedLaggedEstimator h N path ∂μ)
      Filter.atTop
        (nhds (∫ path, stoppedLaggedUnbiasedEstimator h path ∂μ)) := by
    have hseriesShift := hseries.tendsto_sum_nat.comp
      (Filter.tendsto_add_atTop_nat 1)
    have hadd := hseriesShift.const_add (∫ path, h (path 0).2 ∂μ)
    convert hadd using 1
    · funext N
      unfold stoppedLaggedEstimator
      rw [integral_add hbase (integrable_finsetSum _ fun n _ => hcorr n),
        integral_finsetSum _ fun n _ => hcorr n]
      rfl
    · unfold stoppedLaggedUnbiasedEstimator
      rw [integral_add hbase
        (integrable_tsum_stoppedLaggedCorrection μ h hh hsum)]
  exact tendsto_nhds_unique htoInfinite htoTarget

/-- Paper-style higher-moment endpoint: a uniform `Lᵖ` bound with positive
Hölder gap, geometric meeting tails, and faithful coupling jointly give an
unbiased estimator with finite variance. This permits unbounded observables. -/
theorem integral_eq_and_memLp_two_stoppedLaggedUnbiasedEstimator_of_moment_geometric
    [MeasurableEq α]
    (initialCoupling : Measure (α × α)) [IsProbabilityMeasure initialCoupling]
    (initial : Measure α)
    (transition : Kernel α α) [IsMarkovKernel transition]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (hinitial : IsMeasureCoupling initialCoupling initial initial)
    (hcoupled : IsCoupling coupled transition transition)
    (h : α → ℝ) (hh : Measurable h) (p : ENNReal)
    (hp : (2 : ENNReal) ≤ p)
    (htheta : 0 < 1 / (2 : ENNReal).toReal - 1 / p.toReal)
    (M : ENNReal) (hM : M ≠ ⊤)
    (hmoment : ∀ n,
      eLpNorm (fun path : ℕ → α × α => h (path n).1) p
        (pathLaw (laggedInitialMeasure initialCoupling transition) coupled) ≤ M ∧
      eLpNorm (fun path : ℕ → α × α => h (path n).2) p
        (pathLaw (laggedInitialMeasure initialCoupling transition) coupled) ≤ M)
    (hbase : MemLp (fun path : ℕ → α × α => h (path 0).2) 2
      (pathLaw (laggedInitialMeasure initialCoupling transition) coupled))
    (hint : ∀ n, Integrable h (lawAtTime initial transition n))
    (targetMean : ℝ)
    (hmarginal : Filter.Tendsto
      (fun n => ∫ x, h x ∂lawAtTime initial transition n)
      Filter.atTop (nhds targetMean))
    (C rate : ENNReal) (hC : C ≠ ⊤) (hrate : rate < 1)
    (htail : ∀ n, exactMeetingTail
      (pathLaw (laggedInitialMeasure initialCoupling transition) coupled) n ≤
        C * rate ^ n)
    (hfaithful : IsFaithful coupled) :
    (∫ path, stoppedLaggedUnbiasedEstimator h path
      ∂pathLaw (laggedInitialMeasure initialCoupling transition) coupled) =
        targetMean ∧
      MemLp (stoppedLaggedUnbiasedEstimator h) 2
        (pathLaw (laggedInitialMeasure initialCoupling transition) coupled) := by
  let μ := pathLaw (laggedInitialMeasure initialCoupling transition) coupled
  letI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have hnormSum : (∑' n : ℕ,
      eLpNorm (stoppedLaggedCorrection h n) 2 μ) ≠ ⊤ :=
    tsum_eLpNorm_two_stoppedLaggedCorrection_ne_top_of_moment_geometric
      μ h hh p hp htheta M hM hmoment C rate hC hrate htail
  have hL1Sum : (∑' n : ℕ, ∫⁻ path,
      ‖stoppedLaggedCorrection h n path‖ₑ ∂μ) ≠ ⊤ :=
    tsum_lintegral_enorm_stoppedLaggedCorrection_ne_top_of_eLpNorm_two
      μ h hh hnormSum
  constructor
  · exact integral_stoppedLaggedUnbiasedEstimator_eq_of_summable
      initialCoupling initial transition coupled hinitial hcoupled h hh hint
      targetMean hmarginal hL1Sum hfaithful
  · exact memLp_two_stoppedLaggedUnbiasedEstimator_of_summable
      μ h hh hbase hnormSum

/-- Stationary higher-moment specialization. A single target-space
`MemLp h p target` certificate automatically supplies every path-coordinate
moment, the square-integrable base term, and marginal integrability. -/
theorem integral_eq_and_memLp_two_stoppedLaggedUnbiasedEstimator_of_invariant
    [MeasurableEq α]
    (initialCoupling : Measure (α × α)) [IsProbabilityMeasure initialCoupling]
    (target : Measure α) [IsProbabilityMeasure target]
    (transition : Kernel α α) [IsMarkovKernel transition]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (hinitial : IsMeasureCoupling initialCoupling target target)
    (hcoupled : IsCoupling coupled transition transition)
    (hinvariant : transition.Invariant target)
    (h : α → ℝ) (hh : Measurable h) (p : ENNReal)
    (hp : (2 : ENNReal) ≤ p)
    (htheta : 0 < 1 / (2 : ENNReal).toReal - 1 / p.toReal)
    (hmem : MemLp h p target)
    (C rate : ENNReal) (hC : C ≠ ⊤) (hrate : rate < 1)
    (htail : ∀ n, exactMeetingTail
      (pathLaw (laggedInitialMeasure initialCoupling transition) coupled) n ≤
        C * rate ^ n)
    (hfaithful : IsFaithful coupled) :
    (∫ path, stoppedLaggedUnbiasedEstimator h path
      ∂pathLaw (laggedInitialMeasure initialCoupling transition) coupled) =
        ∫ x, h x ∂target ∧
      MemLp (stoppedLaggedUnbiasedEstimator h) 2
        (pathLaw (laggedInitialMeasure initialCoupling transition) coupled) := by
  let μ := pathLaw (laggedInitialMeasure initialCoupling transition) coupled
  let M := eLpNorm h p target
  have hM : M ≠ ⊤ := hmem.2.ne
  have hmoment (n : ℕ) :
      eLpNorm (fun path : ℕ → α × α => h (path n).1) p μ ≤ M ∧
      eLpNorm (fun path : ℕ → α × α => h (path n).2) p μ ≤ M := by
    constructor
    · rw [eLpNorm_laggedPath_fst_atTime initialCoupling target transition
        coupled hinitial hcoupled h hh p n,
        lawAtTime_eq_of_invariant target transition hinvariant]
    · rw [eLpNorm_laggedPath_snd_atTime initialCoupling target transition
        coupled hinitial hcoupled h hh p n,
        lawAtTime_eq_of_invariant target transition hinvariant]
  have hbaseTarget : MemLp h 2 target := hmem.mono_exponent hp
  have hmap : Measure.map (fun path : ℕ → α × α => (path 0).2) μ = target := by
    exact (map_laggedPathLaw_snd_atTime initialCoupling target transition
      coupled hinitial hcoupled 0).trans
        (lawAtTime_zero target transition)
  have hbase : MemLp (fun path : ℕ → α × α => h (path 0).2) 2 μ := by
    have hmapped : MemLp h 2
        (Measure.map (fun path : ℕ → α × α => (path 0).2) μ) := by
      rw [hmap]
      exact hbaseTarget
    change MemLp (h ∘ fun path : ℕ → α × α => (path 0).2) 2 μ
    exact hmapped.comp_of_map ((measurable_pi_apply 0).snd.aemeasurable)
  have hintTarget : Integrable h target :=
    hmem.integrable (le_trans (by norm_num) hp)
  have hint (n : ℕ) : Integrable h (lawAtTime target transition n) := by
    simpa only [lawAtTime_eq_of_invariant target transition hinvariant n] using
      hintTarget
  have hlimit : Filter.Tendsto
      (fun n => ∫ x, h x ∂lawAtTime target transition n)
      Filter.atTop (nhds (∫ x, h x ∂target)) := by
    simpa only [lawAtTime_eq_of_invariant target transition hinvariant] using
      (tendsto_const_nhds : Filter.Tendsto
        (fun _n : ℕ => ∫ x, h x ∂target) Filter.atTop
          (nhds (∫ x, h x ∂target)))
  exact integral_eq_and_memLp_two_stoppedLaggedUnbiasedEstimator_of_moment_geometric
    initialCoupling target transition coupled hinitial hcoupled h hh p hp
    htheta M hM hmoment hbase hint (∫ x, h x ∂target) hlimit
    C rate hC hrate htail hfaithful

/-- A geometric exact-meeting tail supplies the missing `L¹` summability for
bounded observables. With almost-everywhere faithful paths, the resulting
infinite stopped estimator is therefore genuinely unbiased for the limiting
marginal mean. -/
theorem integral_stoppedLaggedUnbiasedEstimator_eq_of_geometric
    [MeasurableEq α]
    (initialCoupling : Measure (α × α)) [IsProbabilityMeasure initialCoupling]
    (initial : Measure α)
    (transition : Kernel α α) [IsMarkovKernel transition]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (hinitial : IsMeasureCoupling initialCoupling initial initial)
    (hcoupled : IsCoupling coupled transition transition)
    (h : α → ℝ) (hh : Measurable h) {B : ℝ}
    (hhB : ∀ x, ‖h x‖ ≤ B)
    (hint : ∀ n, Integrable h (lawAtTime initial transition n))
    (targetMean : ℝ)
    (hmarginal : Filter.Tendsto
      (fun n => ∫ x, h x ∂lawAtTime initial transition n)
      Filter.atTop (nhds targetMean))
    (C rate : ENNReal) (hC : C ≠ ⊤) (hrate : rate < 1)
    (htail : ∀ n, exactMeetingTail
      (pathLaw (laggedInitialMeasure initialCoupling transition) coupled) n ≤
      C * rate ^ n)
    (hfaithful : IsFaithful coupled) :
    (∫ path, stoppedLaggedUnbiasedEstimator h path
      ∂pathLaw (laggedInitialMeasure initialCoupling transition) coupled) =
      targetMean := by
  let μ := pathLaw (laggedInitialMeasure initialCoupling transition) coupled
  let correction : ℕ → (ℕ → α × α) → ℝ := stoppedLaggedCorrection h
  have hsum : (∑' n : ℕ, ∫⁻ path, ‖correction n path‖ₑ ∂μ) ≠ ⊤ :=
    tsum_lintegral_enorm_stoppedLaggedCorrection_ne_top
      μ h hhB C rate hC hrate htail
  have hcorr (n : ℕ) : Integrable (correction n) μ := by
    refine ⟨(measurable_stoppedLaggedCorrection h hh n).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    exact lt_of_le_of_lt (ENNReal.le_tsum n) hsum.lt_top
  have hcorrNorm : Summable (fun n => ∫ path, ‖correction n path‖ ∂μ) := by
    have hs := ENNReal.summable_toReal hsum
    apply hs.congr
    intro n
    exact (integral_norm_eq_lintegral_enorm
      (hcorr n).aestronglyMeasurable).symm
  have hseries : HasSum (fun n => ∫ path, correction n path ∂μ)
      (∫ path, ∑' n : ℕ, correction n path ∂μ) :=
    hasSum_integral_of_summable_integral_norm hcorr hcorrNorm
  have hcoord := integrable_laggedPath_coordinate initialCoupling initial
    transition coupled hinitial hcoupled h hh hint
  have hbase : Integrable (fun path : ℕ → α × α => h (path 0).2) μ :=
    (hcoord 0).2
  have hfaithfulPath : ∀ᵐ path ∂μ, IsFaithfulPath path :=
    hfaithful.ae_isFaithfulPath
      (laggedInitialMeasure initialCoupling transition) coupled
  have hfiniteIntegral (N : ℕ) :
      (∫ path, stoppedLaggedEstimator h N path ∂μ) =
        ∫ x, h x ∂lawAtTime initial transition (N + 1) := by
    calc
      _ = ∫ path, laggedTelescopingEstimator h N path ∂μ := by
        apply integral_congr_ae
        exact hfaithfulPath.mono fun path hpath =>
          stoppedLaggedEstimator_eq_of_faithfulPath h N hpath
      _ = _ := integral_laggedTelescopingEstimator_eq initialCoupling initial
        transition coupled hinitial hcoupled h hh hint N
  have htoTarget : Filter.Tendsto
      (fun N => ∫ path, stoppedLaggedEstimator h N path ∂μ)
      Filter.atTop (nhds targetMean) := by
    simp_rw [hfiniteIntegral]
    change Filter.Tendsto
      ((fun n => ∫ x, h x ∂lawAtTime initial transition n) ∘ fun n => n + 1)
        Filter.atTop (nhds targetMean)
    exact hmarginal.comp (Filter.tendsto_add_atTop_nat 1)
  have htoInfinite : Filter.Tendsto
      (fun N => ∫ path, stoppedLaggedEstimator h N path ∂μ)
      Filter.atTop
        (nhds (∫ path, stoppedLaggedUnbiasedEstimator h path ∂μ)) := by
    have hseriesShift := hseries.tendsto_sum_nat.comp
      (Filter.tendsto_add_atTop_nat 1)
    have hadd := hseriesShift.const_add (∫ path, h (path 0).2 ∂μ)
    convert hadd using 1
    · funext N
      unfold stoppedLaggedEstimator
      rw [integral_add hbase (integrable_finsetSum _ fun n _ => hcorr n),
        integral_finsetSum _ fun n _ => hcorr n]
      rfl
    · unfold stoppedLaggedUnbiasedEstimator
      rw [integral_add hbase
        (integrable_tsum_stoppedLaggedCorrection μ h hh hsum)]
  exact tendsto_nhds_unique htoInfinite htoTarget

/-- Combined bounded-observable endpoint: geometric meeting and marginal
expectation convergence give unbiasedness and finite variance together. -/
theorem integral_eq_and_memLp_two_stoppedLaggedUnbiasedEstimator_of_bounded_geometric
    [MeasurableEq α]
    (initialCoupling : Measure (α × α)) [IsProbabilityMeasure initialCoupling]
    (initial : Measure α) [IsProbabilityMeasure initial]
    (transition : Kernel α α) [IsMarkovKernel transition]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (hinitial : IsMeasureCoupling initialCoupling initial initial)
    (hcoupled : IsCoupling coupled transition transition)
    (h : α → ℝ) (hh : Measurable h) {B : ℝ} (hB : 0 ≤ B)
    (hhB : ∀ x, ‖h x‖ ≤ B)
    (targetMean : ℝ)
    (hmarginal : Filter.Tendsto
      (fun n => ∫ x, h x ∂lawAtTime initial transition n)
      Filter.atTop (nhds targetMean))
    (C rate : ENNReal) (hC : C ≠ ⊤) (hrate : rate < 1)
    (htail : ∀ n, exactMeetingTail
      (pathLaw (laggedInitialMeasure initialCoupling transition) coupled) n ≤
        C * rate ^ n)
    (hfaithful : IsFaithful coupled) :
    (∫ path, stoppedLaggedUnbiasedEstimator h path
      ∂pathLaw (laggedInitialMeasure initialCoupling transition) coupled) =
        targetMean ∧
      MemLp (stoppedLaggedUnbiasedEstimator h) 2
        (pathLaw (laggedInitialMeasure initialCoupling transition) coupled) := by
  have hint (n : ℕ) : Integrable h (lawAtTime initial transition n) := by
    exact (MemLp.of_bound hh.aestronglyMeasurable B
      (Filter.Eventually.of_forall hhB) :
        MemLp h 1 (lawAtTime initial transition n)).integrable le_rfl
  constructor
  · exact integral_stoppedLaggedUnbiasedEstimator_eq_of_geometric
      initialCoupling initial transition coupled hinitial hcoupled h hh hhB
      hint targetMean hmarginal C rate hC hrate htail hfaithful
  · exact memLp_two_stoppedLaggedUnbiasedEstimator_of_geometric
      (pathLaw (laggedInitialMeasure initialCoupling transition) coupled)
      h hh hB hhB C rate hC hrate htail

/-- Stationary-start specialization: no separate marginal-convergence proof
is needed because every finite-time marginal is already the target law. -/
theorem integral_stoppedLaggedUnbiasedEstimator_eq_of_invariant_geometric
    [MeasurableEq α]
    (initialCoupling : Measure (α × α)) [IsProbabilityMeasure initialCoupling]
    (target : Measure α)
    (transition : Kernel α α) [IsMarkovKernel transition]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (hinitial : IsMeasureCoupling initialCoupling target target)
    (hcoupled : IsCoupling coupled transition transition)
    (hinvariant : transition.Invariant target)
    (h : α → ℝ) (hh : Measurable h) {B : ℝ}
    (hhB : ∀ x, ‖h x‖ ≤ B) (hint : Integrable h target)
    (C rate : ENNReal) (hC : C ≠ ⊤) (hrate : rate < 1)
    (htail : ∀ n, exactMeetingTail
      (pathLaw (laggedInitialMeasure initialCoupling transition) coupled) n ≤
        C * rate ^ n)
    (hfaithful : IsFaithful coupled) :
    (∫ path, stoppedLaggedUnbiasedEstimator h path
      ∂pathLaw (laggedInitialMeasure initialCoupling transition) coupled) =
      ∫ x, h x ∂target := by
  have hintAll : ∀ n, Integrable h (lawAtTime target transition n) := by
    intro n
    simpa only [lawAtTime_eq_of_invariant target transition hinvariant n] using hint
  have hlimit : Filter.Tendsto
      (fun n => ∫ x, h x ∂lawAtTime target transition n)
      Filter.atTop (nhds (∫ x, h x ∂target)) := by
    simpa only [lawAtTime_eq_of_invariant target transition hinvariant] using
      (tendsto_const_nhds : Filter.Tendsto
        (fun _n : ℕ => ∫ x, h x ∂target) Filter.atTop
          (nhds (∫ x, h x ∂target)))
  exact integral_stoppedLaggedUnbiasedEstimator_eq_of_geometric
    initialCoupling target transition coupled hinitial hcoupled h hh hhB
    hintAll (∫ x, h x ∂target) hlimit C rate hC hrate htail hfaithful

/-- Total exact-meeting tail mass, the extended-real expected correction
count associated with checking one correction at each paired time. -/
noncomputable def expectedCorrectionCount
    (μ : Measure (ℕ → α × α)) : ENNReal :=
  ∑' n : ℕ, exactMeetingTail μ n

/-- Pathwise number of active correction indices, represented in `ENNReal`.
It is infinite exactly when the failure indicators have infinite total mass. -/
noncomputable def activeCorrectionCount [MeasurableEq α]
    (path : ℕ → α × α) : ENNReal :=
  ∑' n : ℕ, (exactMeetingFailureEvent n).indicator
    (fun _path => (1 : ENNReal)) path

theorem aemeasurable_activeCorrectionCount [MeasurableEq α]
    (μ : Measure (ℕ → α × α)) :
    AEMeasurable (activeCorrectionCount (α := α)) μ := by
  unfold activeCorrectionCount
  exact AEMeasurable.tsum fun n =>
    (measurable_const.indicator
      (measurableSet_exactMeetingFailureEvent n)).aemeasurable

/-- The expected pathwise correction count is exactly the meeting-tail sum. -/
theorem lintegral_activeCorrectionCount_eq_expectedCorrectionCount
    [MeasurableEq α] (μ : Measure (ℕ → α × α)) :
    ∫⁻ path, activeCorrectionCount path ∂μ = expectedCorrectionCount μ := by
  unfold activeCorrectionCount expectedCorrectionCount exactMeetingTail
  rw [lintegral_tsum]
  · congr 1
    funext n
    exact lintegral_indicator_one (measurableSet_exactMeetingFailureEvent n)
  · exact fun n => (measurable_const.indicator
      (measurableSet_exactMeetingFailureEvent n)).aemeasurable

/-- A geometric exact-meeting tail has finite total tail mass, the standard
tail-sum certificate for finite expected correction count. -/
theorem tsum_exactMeetingTail_le_of_geometric
    (μ : Measure (ℕ → α × α)) (C rate : ENNReal)
    (_hrate : rate < 1)
    (htail : ∀ n, exactMeetingTail μ n ≤ C * rate ^ n) :
    ∑' n : ℕ, exactMeetingTail μ n ≤ C * (1 - rate)⁻¹ := by
  calc
    _ ≤ ∑' n : ℕ, C * rate ^ n := ENNReal.tsum_le_tsum htail
    _ = C * ∑' n : ℕ, rate ^ n := by rw [ENNReal.tsum_mul_left]
    _ = C * (1 - rate)⁻¹ := by rw [ENNReal.tsum_geometric]

theorem tsum_exactMeetingTail_ne_top_of_geometric
    (μ : Measure (ℕ → α × α)) (C rate : ENNReal)
    (hC : C ≠ ⊤) (hrate : rate < 1)
    (htail : ∀ n, exactMeetingTail μ n ≤ C * rate ^ n) :
    (∑' n : ℕ, exactMeetingTail μ n) ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (tsum_exactMeetingTail_le_of_geometric
    μ C rate hrate htail)
  exact ENNReal.mul_ne_top hC (ENNReal.inv_ne_top.mpr
    (ne_of_gt (tsub_pos_iff_lt.mpr hrate)))

theorem expectedCorrectionCount_ne_top_of_geometric
    (μ : Measure (ℕ → α × α)) (C rate : ENNReal)
    (hC : C ≠ ⊤) (hrate : rate < 1)
    (htail : ∀ n, exactMeetingTail μ n ≤ C * rate ^ n) :
    expectedCorrectionCount μ ≠ ⊤ := by
  exact tsum_exactMeetingTail_ne_top_of_geometric μ C rate hC hrate htail

/-- Geometric meeting gives the same explicit finite bound for the expected
pathwise amount of correction work. -/
theorem lintegral_activeCorrectionCount_le_of_geometric
    [MeasurableEq α] (μ : Measure (ℕ → α × α)) (C rate : ENNReal)
    (hrate : rate < 1)
    (htail : ∀ n, exactMeetingTail μ n ≤ C * rate ^ n) :
    ∫⁻ path, activeCorrectionCount path ∂μ ≤ C * (1 - rate)⁻¹ := by
  rw [lintegral_activeCorrectionCount_eq_expectedCorrectionCount]
  exact tsum_exactMeetingTail_le_of_geometric μ C rate hrate htail

/-- In particular, geometric meeting makes the number of active corrections
finite almost surely. -/
theorem activeCorrectionCount_ae_lt_top_of_geometric
    [MeasurableEq α] (μ : Measure (ℕ → α × α)) (C rate : ENNReal)
    (hC : C ≠ ⊤) (hrate : rate < 1)
    (htail : ∀ n, exactMeetingTail μ n ≤ C * rate ^ n) :
    ∀ᵐ path ∂μ, activeCorrectionCount path < ⊤ := by
  apply ae_lt_top' (aemeasurable_activeCorrectionCount μ)
  rw [lintegral_activeCorrectionCount_eq_expectedCorrectionCount]
  exact expectedCorrectionCount_ne_top_of_geometric μ C rate hC hrate htail

/-- A faithful coupling with a geometric exact-meeting tail forces the
expectations of every bounded measurable observable along the ordinary chain
to converge. The limit is the expectation of the absolutely summable stopped
estimator. Identifying this limit with a named invariant target is a separate
normalization and uniqueness step. -/
theorem tendsto_marginalExpectation_to_stoppedEstimator_of_bounded_geometric
    [MeasurableEq α]
    (initialCoupling : Measure (α × α)) [IsProbabilityMeasure initialCoupling]
    (initial : Measure α) [IsProbabilityMeasure initial]
    (transition : Kernel α α) [IsMarkovKernel transition]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (hinitial : IsMeasureCoupling initialCoupling initial initial)
    (hcoupled : IsCoupling coupled transition transition)
    (h : α → ℝ) (hh : Measurable h) {B : ℝ}
    (hhB : ∀ x, ‖h x‖ ≤ B)
    (C rate : ENNReal) (hC : C ≠ ⊤) (hrate : rate < 1)
    (htail : ∀ n, exactMeetingTail
      (pathLaw (laggedInitialMeasure initialCoupling transition) coupled) n ≤
      C * rate ^ n)
    (hfaithful : IsFaithful coupled) :
    Filter.Tendsto
      (fun n => ∫ x, h x ∂lawAtTime initial transition n)
      Filter.atTop
      (nhds (∫ path, stoppedLaggedUnbiasedEstimator h path
        ∂pathLaw (laggedInitialMeasure initialCoupling transition) coupled)) := by
  let μ := pathLaw (laggedInitialMeasure initialCoupling transition) coupled
  let correction : ℕ → (ℕ → α × α) → ℝ := stoppedLaggedCorrection h
  have hsum : (∑' n : ℕ, ∫⁻ path, ‖correction n path‖ₑ ∂μ) ≠ ⊤ :=
    tsum_lintegral_enorm_stoppedLaggedCorrection_ne_top
      μ h hhB C rate hC hrate htail
  have hcorr (n : ℕ) : Integrable (correction n) μ := by
    refine ⟨(measurable_stoppedLaggedCorrection h hh n).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    exact lt_of_le_of_lt (ENNReal.le_tsum n) hsum.lt_top
  have hcorrNorm : Summable (fun n => ∫ path, ‖correction n path‖ ∂μ) := by
    have hs := ENNReal.summable_toReal hsum
    apply hs.congr
    intro n
    exact (integral_norm_eq_lintegral_enorm
      (hcorr n).aestronglyMeasurable).symm
  have hseries : HasSum (fun n => ∫ path, correction n path ∂μ)
      (∫ path, ∑' n : ℕ, correction n path ∂μ) :=
    hasSum_integral_of_summable_integral_norm hcorr hcorrNorm
  have hint (n : ℕ) : Integrable h (lawAtTime initial transition n) := by
    exact (MemLp.of_bound hh.aestronglyMeasurable B
      (Filter.Eventually.of_forall hhB) :
        MemLp h 1 (lawAtTime initial transition n)).integrable le_rfl
  have hcoord := integrable_laggedPath_coordinate initialCoupling initial
    transition coupled hinitial hcoupled h hh hint
  have hbase : Integrable (fun path : ℕ → α × α => h (path 0).2) μ :=
    (hcoord 0).2
  have hfaithfulPath : ∀ᵐ path ∂μ, IsFaithfulPath path :=
    hfaithful.ae_isFaithfulPath
      (laggedInitialMeasure initialCoupling transition) coupled
  have hfiniteIntegral (N : ℕ) :
      (∫ path, stoppedLaggedEstimator h N path ∂μ) =
        ∫ x, h x ∂lawAtTime initial transition (N + 1) := by
    calc
      _ = ∫ path, laggedTelescopingEstimator h N path ∂μ := by
        apply integral_congr_ae
        exact hfaithfulPath.mono fun path hpath =>
          stoppedLaggedEstimator_eq_of_faithfulPath h N hpath
      _ = _ := integral_laggedTelescopingEstimator_eq initialCoupling initial
        transition coupled hinitial hcoupled h hh hint N
  have hseriesShift := hseries.tendsto_sum_nat.comp
    (Filter.tendsto_add_atTop_nat 1)
  have hadd := hseriesShift.const_add (∫ path, h (path 0).2 ∂μ)
  have hfiniteTendsto : Filter.Tendsto
      (fun N => ∫ path, stoppedLaggedEstimator h N path ∂μ)
      Filter.atTop
      (nhds (∫ path, stoppedLaggedUnbiasedEstimator h path ∂μ)) := by
    convert hadd using 1
    · funext N
      unfold stoppedLaggedEstimator
      rw [integral_add hbase (integrable_finsetSum _ fun n _ => hcorr n),
        integral_finsetSum _ fun n _ => hcorr n]
      rfl
    · unfold stoppedLaggedUnbiasedEstimator
      rw [integral_add hbase
        (integrable_tsum_stoppedLaggedCorrection μ h hh hsum)]
  rw [show (fun N => ∫ path, stoppedLaggedEstimator h N path ∂μ) =
      fun N => ∫ x, h x ∂lawAtTime initial transition (N + 1) by
    funext N
    exact hfiniteIntegral N] at hfiniteTendsto
  exact (Filter.tendsto_add_atTop_iff_nat 1).mp hfiniteTendsto

end Kernel
end Mcmc
