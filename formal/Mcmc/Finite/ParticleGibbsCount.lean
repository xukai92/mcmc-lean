import Mcmc.Finite.Doeblin
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

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

/-- Finite automaton state recording how much of a fixed-horizon proposed
path has been consumed and whether every state has matched so far. -/
structure PathMatchLabel (horizon : ℕ) where
  time : Fin (horizon + 1)
  matched : Bool
deriving Fintype, DecidableEq

/-- Initial path-match label after inspecting time zero. -/
def initialPathMatchLabel (horizon : ℕ)
    (desired : Fin (horizon + 1) → Sample) (state : Sample) :
    PathMatchLabel horizon :=
  ⟨⟨0, Nat.zero_lt_succ horizon⟩, decide (state = desired ⟨0, Nat.zero_lt_succ horizon⟩)⟩

/-- Consume one state of the proposed path. At the terminal index the
automaton is total and remains unchanged; the intended client invokes exactly
`horizon` genuine advances. -/
def advancePathMatchLabel (horizon : ℕ)
    (desired : Fin (horizon + 1) → Sample)
    (label : PathMatchLabel horizon) (state : Sample) :
    PathMatchLabel horizon := by
  by_cases hnext : label.time.val + 1 < horizon + 1
  · let next : Fin (horizon + 1) := ⟨label.time.val + 1, hnext⟩
    exact ⟨next, label.matched && decide (state = desired next)⟩
  · exact label

/-- Nonnegative indicator observable read from the path-match automaton. -/
def pathMatchScore {horizon : ℕ} (label : PathMatchLabel horizon) : ℝ :=
  if label.matched then 1 else 0

theorem pathMatchScore_nonneg {horizon : ℕ} (label : PathMatchLabel horizon) :
    0 ≤ pathMatchScore label := by
  unfold pathMatchScore
  split <;> norm_num

omit [Fintype Sample] in
@[simp] theorem initialPathMatchLabel_matched_iff (horizon : ℕ)
    (desired : Fin (horizon + 1) → Sample) (state : Sample) :
    (initialPathMatchLabel horizon desired state).matched = true ↔
      state = desired ⟨0, Nat.zero_lt_succ horizon⟩ := by
  simp [initialPathMatchLabel]

omit [Fintype Sample] in
theorem advancePathMatchLabel_of_not_terminal (horizon : ℕ)
    (desired : Fin (horizon + 1) → Sample)
    (label : PathMatchLabel horizon) (state : Sample)
    (hnext : label.time.val + 1 < horizon + 1) :
    advancePathMatchLabel horizon desired label state =
      ⟨⟨label.time.val + 1, hnext⟩,
        label.matched && decide
          (state = desired ⟨label.time.val + 1, hnext⟩)⟩ := by
  unfold advancePathMatchLabel
  simp [hnext]

/-- Two fixed-horizon paths agree through a given time index. -/
def pathMatchesThrough {horizon : ℕ}
    (desired actual : Fin (horizon + 1) → Sample)
    (time : Fin (horizon + 1)) : Prop :=
  ∀ i, i.val ≤ time.val → actual i = desired i

/-- Canonical automaton label associated with two complete paths at a fixed
time. -/
noncomputable def canonicalPathMatchLabel {horizon : ℕ}
    (desired actual : Fin (horizon + 1) → Sample)
    (time : Fin (horizon + 1)) : PathMatchLabel horizon := by
  classical
  exact ⟨time, if pathMatchesThrough desired actual time then true else false⟩

omit [Fintype Sample] [DecidableEq Sample] in
/-- At the final time, the automaton's match bit is exactly equality of the
two complete finite paths. -/
theorem canonicalPathMatchLabel_last_matched_iff {horizon : ℕ}
    (desired actual : Fin (horizon + 1) → Sample) :
    (canonicalPathMatchLabel desired actual (Fin.last horizon)).matched = true ↔
      actual = desired := by
  classical
  simp only [canonicalPathMatchLabel]
  simp only [ite_eq_left_iff, Bool.false_eq_true, imp_false, not_not]
  constructor
  · intro h
    funext i
    exact h i (Nat.le_of_lt_succ i.isLt)
  · intro h
    subst actual
    intro i _
    rfl

omit [Fintype Sample] in
/-- Advancing the canonical label with the actual next state produces the
canonical label at the successor time. -/
theorem advance_canonicalPathMatchLabel {horizon : ℕ}
    (desired actual : Fin (horizon + 1) → Sample)
    (time : Fin (horizon + 1))
    (hnext : time.val + 1 < horizon + 1) :
    advancePathMatchLabel horizon desired
        (canonicalPathMatchLabel desired actual time)
        (actual ⟨time.val + 1, hnext⟩) =
      canonicalPathMatchLabel desired actual ⟨time.val + 1, hnext⟩ := by
  classical
  let next : Fin (horizon + 1) := ⟨time.val + 1, hnext⟩
  have hthrough :
      pathMatchesThrough desired actual next ↔
        pathMatchesThrough desired actual time ∧ actual next = desired next := by
    constructor
    · intro h
      refine ⟨?_, h next (by simp [next])⟩
      intro i hi
      exact h i (by dsimp [next]; omega)
    · rintro ⟨hprefix, hnew⟩ i hi
      by_cases hle : i.val ≤ time.val
      · exact hprefix i hle
      · have hval : i.val = next.val := by
          dsimp [next] at hi ⊢
          omega
        have hiEq : i = next := Fin.ext hval
        simpa [hiEq] using hnew
  rw [advancePathMatchLabel_of_not_terminal horizon desired
    (canonicalPathMatchLabel desired actual time)
    (actual next) (by simpa [canonicalPathMatchLabel, next] using hnext)]
  unfold canonicalPathMatchLabel
  simp only
  rw [show (⟨time.val + 1, _⟩ : Fin (horizon + 1)) = next from rfl]
  simp [hthrough]

omit [Fintype Sample] in
/-- Initialization is the canonical path-match label at time zero. -/
theorem initialPathMatchLabel_eq_canonical {horizon : ℕ}
    (desired actual : Fin (horizon + 1) → Sample) :
    initialPathMatchLabel horizon desired
        (actual ⟨0, Nat.zero_lt_succ horizon⟩) =
      canonicalPathMatchLabel desired actual
        ⟨0, Nat.zero_lt_succ horizon⟩ := by
  classical
  unfold initialPathMatchLabel canonicalPathMatchLabel pathMatchesThrough
  congr
  simp

/-- A strictly positive real family over a nonempty finite type has one
strictly positive uniform lower bound. The product-of-truncations construction
keeps this lemma computationally explicit enough for finite model clients. -/
theorem exists_uniformPositiveFloor
    {A : Type*} [Fintype A] [Nonempty A]
    (f : A → ℝ) (hf : ∀ a, 0 < f a) :
    ∃ floor : ℝ, 0 < floor ∧ floor ≤ 1 ∧
      ∀ a, floor ≤ f a := by
  classical
  let truncated : A → ℝ := fun a => min 1 (f a)
  let floor := ∏ a, truncated a
  refine ⟨floor, ?_, ?_, ?_⟩
  · apply Finset.prod_pos
    intro a _ha
    exact lt_min zero_lt_one (hf a)
  · apply Finset.prod_le_one
    · intro a _ha
      exact (lt_min zero_lt_one (hf a)).le
    · intro a _ha
      exact min_le_left _ _
  · intro a
    have ha : a ∈ (Finset.univ : Finset A) := Finset.mem_univ a
    have herase : 0 ≤
        (∏ b ∈ (Finset.univ.erase a), truncated b) := by
      apply Finset.prod_nonneg
      intro b _hb
      exact (lt_min zero_lt_one (hf b)).le
    have heraseOne :
        (∏ b ∈ (Finset.univ.erase a), truncated b) ≤ 1 := by
      apply Finset.prod_le_one
      · intro b _hb
        exact (lt_min zero_lt_one (hf b)).le
      · intro b _hb
        exact min_le_left _ _
    calc
      floor = (∏ b ∈ (Finset.univ.erase a), truncated b) *
          truncated a := by
        rw [Finset.prod_erase_mul _ _ ha]
      _ ≤ truncated a := by
        nlinarith [show 0 ≤ truncated a from
          (lt_min zero_lt_one (hf a)).le]
      _ ≤ f a := min_le_right _ _

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

/-- At zero propagation steps, the trajectory target is exactly the initial
one-state law. -/
theorem countedTrajectoryTarget_nil_mass
    (initial : Distribution Sample) (hinitial : ∀ x, 0 < initial.mass x)
    (hnormalizer : 0 < normalizingConstant initial []) (extra : ℕ)
    (trajectory : Trajectory ([] : List (FeynmanKacStep Sample)))
    (first : Sample) (htrajectory : trajectory = ⟨[first], by simp⟩) :
    (countedTrajectoryTarget initial [] hnormalizer extra).mass trajectory =
      initial.mass first := by
  subst trajectory
  unfold countedTrajectoryTarget trajectoryTarget
  rw [Mcmc.Finite.Conditional.statisticMarginal_mass]
  rw [fiberMass_selectedTrajectoryVector_eq_selectedTrajectoryMass]
  change selectedTrajectoryMass (Particle := Fin (extra + 1))
    initial [] hnormalizer [first] = initial.mass first
  rw [selectedTrajectoryMass_eq_pathDensity_div initial [] hnormalizer
    first [] (by simp) (hinitial first) (by trivial)]
  simp [pathSuffixDensity, normalizingConstant, feynmanKacSequence,
    Distribution.sum_mass]

omit [DecidableEq Sample] in
/-- Every zero-step trajectory contains exactly one state. -/
theorem trajectory_nil_eq_singleton
    (trajectory : Trajectory ([] : List (FeynmanKacStep Sample))) :
    ∃ first : Sample, trajectory = ⟨[first], by simp⟩ := by
  rcases trajectory with ⟨path, hpath⟩
  cases path with
  | nil => simp at hpath
  | cons first rest =>
      have hrest : rest = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using hpath
      subst rest
      exact ⟨first, rfl⟩

/-- A conservative coefficient shape used by bounded-potential PG analyses.
`extra = N-1`, and `bound` records the model-dependent path-weight penalty. -/
noncomputable def particleGibbsCountCoefficient
    (extra : ℕ) (bound : ℝ) (horizon : ℕ) : ℝ :=
  ((extra : ℝ) / ((extra : ℝ) + bound)) ^ horizon

/-- Time-inhomogeneous version of the PG refresh coefficient. Each entry is
the nonnegative penalty for one Feynman--Kac time slice. This is the algebraic
shape used when model bounds vary with time instead of being replaced by one
global worst-case constant. -/
noncomputable def particleGibbsScheduleCoefficient
    (extra : ℕ) (penalties : List ℝ) : ℝ :=
  (penalties.map fun penalty =>
    (extra : ℝ) / ((extra : ℝ) + penalty)).prod

/-- Count-independent candidate penalty schedule: one neutral terminal-index
penalty followed by the conservative `2B - 1` candidate of each Feynman--Kac potential.
One copy of `B` controls the retained particle and the other controls the
self-normalized ordinary cloud against the exact normalized target. The full
recursive minorization for this candidate is not asserted by this definition. -/
noncomputable def feynmanKacOscillationPenalties
    (steps : List (FeynmanKacStep Sample)) : List ℝ :=
  1 :: steps.map fun step =>
    finitePotentialParticleGibbsCandidatePenalty step.potential

omit [DecidableEq Sample] in
@[simp] theorem length_feynmanKacOscillationPenalties
    (steps : List (FeynmanKacStep Sample)) :
    (feynmanKacOscillationPenalties steps).length = steps.length + 1 := by
  simp [feynmanKacOscillationPenalties]

omit [DecidableEq Sample] in
theorem feynmanKacOscillationPenalties_pos [Nonempty Sample]
    (steps : List (FeynmanKacStep Sample)) :
    ∀ penalty ∈ feynmanKacOscillationPenalties steps, 0 < penalty := by
  intro penalty hpenalty
  simp only [feynmanKacOscillationPenalties, List.mem_cons,
    List.mem_map] at hpenalty
  rcases hpenalty with rfl | ⟨step, _hstep, rfl⟩
  · norm_num
  · exact finitePotentialParticleGibbsCandidatePenalty_pos
      step.potential step.potential_pos

/-- A constant schedule recovers the original power coefficient exactly. -/
theorem particleGibbsScheduleCoefficient_replicate
    (extra horizon : ℕ) (bound : ℝ) :
    particleGibbsScheduleCoefficient extra (List.replicate horizon bound) =
      particleGibbsCountCoefficient extra bound horizon := by
  simp [particleGibbsScheduleCoefficient, particleGibbsCountCoefficient]

theorem particleGibbsScheduleCoefficient_pos
    {extra : ℕ} {penalties : List ℝ} (hextra : 0 < extra)
    (hpenalties : ∀ penalty ∈ penalties, 0 < penalty) :
    0 < particleGibbsScheduleCoefficient extra penalties := by
  unfold particleGibbsScheduleCoefficient
  apply List.prod_pos
  intro ratio hratio
  simp only [List.mem_map] at hratio
  obtain ⟨penalty, hmem, rfl⟩ := hratio
  have hpenalty := hpenalties penalty hmem
  positivity

theorem particleGibbsScheduleCoefficient_lt_one
    {extra : ℕ} {penalties : List ℝ} (hextra : 0 < extra)
    (hne : penalties ≠ [])
    (hpenalties : ∀ penalty ∈ penalties, 0 < penalty) :
    particleGibbsScheduleCoefficient extra penalties < 1 := by
  unfold particleGibbsScheduleCoefficient
  have hproduct := List.prod_map_lt_prod_map hne
    (fun penalty : ℝ => (extra : ℝ) / ((extra : ℝ) + penalty))
    (fun _ : ℝ => (1 : ℝ))
    (fun penalty hmem => by
      have hpenalty := hpenalties penalty hmem
      positivity)
    (fun penalty hmem => by
      have hpenalty := hpenalties penalty hmem
      have hdenom : 0 < (extra : ℝ) + penalty := by positivity
      rw [div_lt_one hdenom]
      linarith)
  simpa using hproduct

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

/-- Any positive floor can be represented conservatively by the displayed
particle-Gibbs coefficient shape at a fixed positive count and horizon. -/
theorem exists_particleGibbsCountBound_le_floor
    {extra horizon : ℕ} {floor : ℝ}
    (hextra : 0 < extra) (hhorizon : 0 < horizon)
    (hfloor : 0 < floor) :
    ∃ bound : ℝ, 0 < bound ∧
      particleGibbsCountCoefficient extra bound horizon ≤ floor := by
  let bound : ℝ := (extra : ℝ) / floor
  have hbound : 0 < bound := by
    unfold bound
    positivity
  have hbase0 : 0 ≤
      (extra : ℝ) / ((extra : ℝ) + bound) := by positivity
  have hbaseOne :
      (extra : ℝ) / ((extra : ℝ) + bound) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact le_add_of_nonneg_right hbound.le
  have hbaseFloor :
      (extra : ℝ) / ((extra : ℝ) + bound) ≤ floor := by
    rw [div_le_iff₀ (by positivity)]
    unfold bound
    field_simp
    nlinarith
  refine ⟨bound, hbound, ?_⟩
  unfold particleGibbsCountCoefficient
  exact (pow_le_of_le_one hbase0 hbaseOne hhorizon.ne').trans hbaseFloor

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

/-- At fixed horizon and fixed finite potential penalty, the certified
positive-horizon refresh coefficient tends to one as the number of
non-retained particles tends to infinity. -/
theorem particleGibbsCountCoefficient_tendsto_one
    (bound : ℝ) (horizon : ℕ) :
    Filter.Tendsto
      (fun extra => particleGibbsCountCoefficient extra bound horizon)
      Filter.atTop (nhds 1) := by
  have hdenom : Filter.Tendsto (fun extra : ℕ => (extra : ℝ) + bound)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop bound
      tendsto_natCast_atTop_atTop
  have hpenalty : Filter.Tendsto
      (fun extra : ℕ => bound / ((extra : ℝ) + bound))
      Filter.atTop (nhds 0) := hdenom.const_div_atTop bound
  have hbase : Filter.Tendsto
      (fun extra : ℕ => (extra : ℝ) / ((extra : ℝ) + bound))
      Filter.atTop (nhds 1) := by
    have hsub : Filter.Tendsto
        (fun extra : ℕ => (1 : ℝ) - bound / ((extra : ℝ) + bound))
        Filter.atTop (nhds 1) := by
      simpa using (tendsto_const_nhds.sub hpenalty)
    apply hsub.congr'
    filter_upwards [hdenom.eventually (Filter.eventually_gt_atTop 0)] with extra hpos
    field_simp [ne_of_gt hpos]
    ring
  unfold particleGibbsCountCoefficient
  simpa using hbase.pow horizon

/-- For every fixed finite time-inhomogeneous penalty schedule, the certified
refresh coefficient also tends to one with particle count. -/
theorem particleGibbsScheduleCoefficient_tendsto_one
    (penalties : List ℝ) :
    Filter.Tendsto
      (fun extra => particleGibbsScheduleCoefficient extra penalties)
      Filter.atTop (nhds 1) := by
  induction penalties with
  | nil => simp [particleGibbsScheduleCoefficient]
  | cons penalty penalties ih =>
      have hhead := particleGibbsCountCoefficient_tendsto_one penalty 1
      have hproduct := hhead.mul ih
      simpa [particleGibbsScheduleCoefficient,
        particleGibbsCountCoefficient] using hproduct

/-- At any fixed positive number of MCMC iterations, the resulting geometric
upper-bound factor vanishes as particle count grows. -/
theorem particleGibbsCountRate_tendsto_zero
    (bound : ℝ) (horizon iterations : ℕ) (hiterations : 0 < iterations) :
    Filter.Tendsto
      (fun extra =>
        (1 - particleGibbsCountCoefficient extra bound horizon) ^ iterations)
      Filter.atTop (nhds 0) := by
  have hzero : Filter.Tendsto
      (fun extra => 1 - particleGibbsCountCoefficient extra bound horizon)
      Filter.atTop (nhds 0) := by
    simpa using
      ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
          Filter.atTop (nhds 1)).sub
        (particleGibbsCountCoefficient_tendsto_one bound horizon))
  simpa [zero_pow hiterations.ne'] using hzero.pow iterations

/-- Time-inhomogeneous schedules have the same fixed-iteration asymptotic
bound. -/
theorem particleGibbsScheduleRate_tendsto_zero
    (penalties : List ℝ) (iterations : ℕ) (hiterations : 0 < iterations) :
    Filter.Tendsto
      (fun extra =>
        (1 - particleGibbsScheduleCoefficient extra penalties) ^ iterations)
      Filter.atTop (nhds 0) := by
  have hzero : Filter.Tendsto
      (fun extra => 1 - particleGibbsScheduleCoefficient extra penalties)
      Filter.atTop (nhds 0) := by
    simpa using
      ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
          Filter.atTop (nhds 1)).sub
        (particleGibbsScheduleCoefficient_tendsto_one penalties))
  simpa [zero_pow hiterations.ne'] using hzero.pow iterations

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

/-- Time-inhomogeneous PG minorization retaining one explicit penalty per
Feynman--Kac time slice. -/
structure ScheduledPotentialParticleGibbsMinorization
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps) (extra : ℕ) where
  penalties : List ℝ
  penalties_length : penalties.length = steps.length + 1
  extra_pos : 0 < extra
  penalties_pos : ∀ penalty ∈ penalties, 0 < penalty
  minorization : ∀ current proposed,
    particleGibbsScheduleCoefficient extra penalties *
        (countedTrajectoryTarget initial steps hnormalizer extra).mass proposed ≤
      (countedTrajectoryParticleGibbsKernel initial steps hnormalizer extra).prob
        current proposed

/-- A per-time penalty certificate directly yields the exact refresh/residual
decomposition, without first replacing the schedule by a worst-case bound. -/
noncomputable def ScheduledPotentialParticleGibbsMinorization.toRefresh
    {initial : Distribution Sample} {steps : List (FeynmanKacStep Sample)}
    {hnormalizer : 0 < normalizingConstant initial steps} {extra : ℕ}
    (certificate : ScheduledPotentialParticleGibbsMinorization
      initial steps hnormalizer extra) :
    RefreshDecomposition
      (countedTrajectoryParticleGibbsKernel initial steps hnormalizer extra)
      (countedTrajectoryTarget initial steps hnormalizer extra) := by
  apply RefreshDecomposition.ofMinorization
    (particleGibbsScheduleCoefficient extra certificate.penalties)
  · exact (particleGibbsScheduleCoefficient_pos certificate.extra_pos
      certificate.penalties_pos).le
  · apply particleGibbsScheduleCoefficient_lt_one certificate.extra_pos
    · intro hempty
      have := certificate.penalties_length
      simp [hempty] at this
    · exact certificate.penalties_pos
  · exact certificate.minorization
  · exact trajectoryParticleGibbsKernel_stationary
      (Particle := Fin (extra + 1)) initial steps hnormalizer

/-- Geometric TV bound retaining all time-specific PG penalties. -/
theorem scheduledPotentialParticleGibbs_totalVariation_le
    {initial : Distribution Sample} {steps : List (FeynmanKacStep Sample)}
    {hnormalizer : 0 < normalizingConstant initial steps} {extra : ℕ}
    (certificate : ScheduledPotentialParticleGibbsMinorization
      initial steps hnormalizer extra)
    (initialLaw : Distribution (Trajectory steps)) (iterations : ℕ) :
    Nonhomogeneous.distributionTotalVariation
      (Nonhomogeneous.iterateLaw initialLaw
        (countedTrajectoryParticleGibbsKernel initial steps hnormalizer extra)
        iterations)
      (countedTrajectoryTarget initial steps hnormalizer extra) ≤
      (1 - particleGibbsScheduleCoefficient extra certificate.penalties) ^
        iterations := by
  exact certificate.toRefresh.iterateLaw_totalVariation_le initialLaw iterations

theorem scheduledPotentialParticleGibbs_totalVariation_tendsto_zero
    {initial : Distribution Sample} {steps : List (FeynmanKacStep Sample)}
    {hnormalizer : 0 < normalizingConstant initial steps} {extra : ℕ}
    (certificate : ScheduledPotentialParticleGibbsMinorization
      initial steps hnormalizer extra)
    (initialLaw : Distribution (Trajectory steps)) :
    Filter.Tendsto (fun iterations =>
      Nonhomogeneous.distributionTotalVariation
        (Nonhomogeneous.iterateLaw initialLaw
          (countedTrajectoryParticleGibbsKernel initial steps hnormalizer extra)
          iterations)
        (countedTrajectoryTarget initial steps hnormalizer extra))
      Filter.atTop (nhds 0) := by
  apply certificate.toRefresh.iterateLaw_totalVariation_tendsto_zero
  exact particleGibbsScheduleCoefficient_pos certificate.extra_pos
    certificate.penalties_pos

/-- Fraction of an initial particle cloud equal to one prescribed trajectory
start. This is the base case of the aggregate genealogy recursion. -/
noncomputable def initialStateFraction (extra : ℕ)
    (particles : Fin (extra + 1) → Sample) (proposed : Sample) : ℝ :=
  particleAverage (fun x => if x = proposed then 1 else 0) particles

/-- At initialization, every unforced particle independently starts at the
proposed state with its target initial probability. Consequently the expected
matching fraction loses only the single retained slot. Unlike a one-history
witness, this factor tends to one with the particle count. -/
theorem forcedInitialPopulation_initialStateFraction_ge
    (initial : Distribution Sample) (extra : ℕ)
    (retained : Fin (extra + 1)) (current proposed : Sample) :
    (extra : ℝ) / (extra + 1) * initial.mass proposed ≤
      ∑ particles,
        (forcedIndependentPopulation (fun _ : Fin (extra + 1) => initial)
          retained current).mass particles *
            initialStateFraction extra particles proposed := by
  have h := forcedIndependentPopulation_particleAverage_expectation_ge_card
    (law := fun _ : Fin (extra + 1) => initial)
    retained current (fun x => if x = proposed then 1 else 0)
    (initial.mass proposed) (by positivity) (by
      intro i _hi
      simp)
  simpa [initialStateFraction, div_eq_mul_inv, mul_assoc, mul_left_comm,
    mul_comm] using h

/-- Total conditional-SMC/terminal-refresh mass of all extended histories
connecting two trajectories. This aggregate, rather than any one history,
is the correct quantitative object for bounds uniform in particle count. -/
noncomputable def aggregatedForcedLineageMass
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps) (extra : ℕ)
    (current proposed : Trajectory steps) : ℝ :=
  ∑ liftCurrent : History (Particle := Fin (extra + 1)) steps × Fin (extra + 1),
    (Mcmc.Finite.Conditional.conditionalRow
      (selectedParticleTarget (Particle := Fin (extra + 1))
        initial steps hnormalizer)
      (selectedTrajectoryVector steps) current).mass liftCurrent *
      ∑ liftProposed,
        (selectedIndexRefreshKernel (Particle := Fin (extra + 1)) steps).prob
            liftCurrent liftProposed *
          (if proposed = selectedTrajectoryVector steps liftProposed
            then 1 else 0)

/-- Fraction of terminal particle indices in one history whose genealogy is
the proposed trajectory. -/
noncomputable def proposedTrajectoryFraction
    (steps : List (FeynmanKacStep Sample)) (extra : ℕ)
    (history : History (Particle := Fin (extra + 1)) steps)
    (proposed : Trajectory steps) : ℝ :=
  (∑ j : Fin (extra + 1),
      if proposed = selectedTrajectoryVector steps (history, j)
        then 1 else 0) / Fintype.card (Fin (extra + 1))

/-- The same terminal genealogy fraction computed forward by carrying a path
label through every ancestor map. This recursion-oriented presentation is
definitionally local at each SMC stage. -/
noncomputable def genealogicalTrajectoryFraction
    (steps : List (FeynmanKacStep Sample)) (extra : ℕ)
    (history : History (Particle := Fin (extra + 1)) steps)
    (proposed : Trajectory steps) : ℝ :=
  particleAverage
    (fun path : List Sample => if path = proposed.toList then 1 else 0)
    (terminalLabels (fun path y => path ++ [y]) steps
      (fun i => [history.1 i]) history.2)

/-- Forward path-label counting is exactly the backward selected-genealogy
fraction used by the particle-Gibbs kernel. -/
theorem genealogicalTrajectoryFraction_eq_proposedTrajectoryFraction
    (steps : List (FeynmanKacStep Sample)) (extra : ℕ)
    (history : History (Particle := Fin (extra + 1)) steps)
    (proposed : Trajectory steps) :
    genealogicalTrajectoryFraction steps extra history proposed =
      proposedTrajectoryFraction steps extra history proposed := by
  unfold genealogicalTrajectoryFraction proposedTrajectoryFraction particleAverage
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [terminalLabels_singleton_eq_selectedTrajectory]
  have heq := selectedTrajectoryVector_eq_iff_toList
    (Particle := Fin (extra + 1)) steps (history, j) proposed
  by_cases h : proposed = selectedTrajectoryVector steps (history, j)
  · have hlist : selectedTrajectory steps history.1 history.2 j =
        proposed.toList := heq.mp h.symm
    simp [h, hlist]
  · have hlist : selectedTrajectory steps history.1 history.2 j ≠
        proposed.toList := by
      intro hp
      exact h (heq.mpr hp).symm
    simp [h, hlist]

/-- Uniform terminal-index refresh turns the compatible-index count in a
fixed history into exactly its proposed-trajectory fraction. -/
theorem selectedIndexRefresh_aggregate_eq_proposedTrajectoryFraction
    (steps : List (FeynmanKacStep Sample)) (extra : ℕ)
    (history : History (Particle := Fin (extra + 1)) steps)
    (currentIndex : Fin (extra + 1)) (proposed : Trajectory steps) :
    (∑ liftProposed,
        (selectedIndexRefreshKernel (Particle := Fin (extra + 1)) steps).prob
            (history, currentIndex) liftProposed *
          (if proposed = selectedTrajectoryVector steps liftProposed
            then 1 else 0)) =
      proposedTrajectoryFraction steps extra history proposed := by
  rw [Fintype.sum_prod_type]
  simp only [selectedIndexRefreshKernel, MarkovKernel.liftSnd,
    uniformIndexKernel]
  rw [Finset.sum_eq_single history]
  · simp only [if_true]
    rw [← Finset.mul_sum]
    simp [proposedTrajectoryFraction, div_eq_mul_inv, mul_comm]
  · intro otherHistory _hmem hne
    simp [Ne.symm hne]
  · simp

/-- The aggregate edge mass is the conditional expectation of the fraction
of terminal genealogies equal to the proposed trajectory. This is the
finite-history quantity used in sharp particle-Gibbs analyses. -/
theorem aggregatedForcedLineageMass_eq_sum_fraction
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps) (extra : ℕ)
    (current proposed : Trajectory steps) :
    aggregatedForcedLineageMass initial steps hnormalizer extra
        current proposed =
      ∑ liftCurrent :
          History (Particle := Fin (extra + 1)) steps × Fin (extra + 1),
        (Mcmc.Finite.Conditional.conditionalRow
          (selectedParticleTarget (Particle := Fin (extra + 1))
            initial steps hnormalizer)
          (selectedTrajectoryVector steps) current).mass liftCurrent *
          proposedTrajectoryFraction steps extra liftCurrent.1 proposed := by
  unfold aggregatedForcedLineageMass
  apply Finset.sum_congr rfl
  intro liftCurrent _hmem
  rcases liftCurrent with ⟨history, currentIndex⟩
  rw [selectedIndexRefresh_aggregate_eq_proposedTrajectoryFraction]

/-- Under primitive full support, the aggregate transition entry is an
expectation under the actual forced-lineage conditional-SMC generator. This
is the recursion-facing form needed to propagate the per-step oscillation
bounds. -/
theorem aggregatedForcedLineageMass_eq_forcedLineage_expectation
    [Nonempty Sample]
    (initial : Distribution Sample) (hinitial : ∀ x, 0 < initial.mass x)
    (steps : List (FeynmanKacStep Sample))
    (hsupport : FeynmanKacFullSupport steps)
    (hnormalizer : 0 < normalizingConstant initial steps) (extra : ℕ)
    (current proposed : Trajectory steps) :
    aggregatedForcedLineageMass initial steps hnormalizer extra
        current proposed =
      ∑ selected :
          History (Particle := Fin (extra + 1)) steps × Fin (extra + 1),
        (forcedLineageLaw (Particle := Fin (extra + 1))
          initial steps current.toList current.toList_length).mass selected *
          proposedTrajectoryFraction steps extra selected.1 proposed := by
  rw [aggregatedForcedLineageMass_eq_sum_fraction]
  apply Finset.sum_congr rfl
  intro selected _hselected
  rw [conditionalRow_selectedTrajectoryVector_eq_forcedLineageLaw
    initial hinitial steps hsupport hnormalizer current]

/-- Recursion-facing expansion of the aggregate PG entry. After choosing the
initial retained slot and forced initial cloud, the remaining quantity is the
forward path-label expectation of the recursive forced suffix law. -/
theorem aggregatedForcedLineageMass_eq_recursiveLabelExpectation
    [Nonempty Sample]
    (initial : Distribution Sample) (hinitial : ∀ x, 0 < initial.mass x)
    (steps : List (FeynmanKacStep Sample))
    (hsupport : FeynmanKacFullSupport steps)
    (hnormalizer : 0 < normalizingConstant initial steps) (extra : ℕ)
    (current proposed : Trajectory steps) (first : Sample)
    (future : List Sample) (hfuture : future.length = steps.length)
    (hcurrent : current =
      ⟨first :: future, by simp [hfuture]⟩) :
    aggregatedForcedLineageMass initial steps hnormalizer extra
        current proposed =
      ∑ retained : Fin (extra + 1),
        (uniformParticleDistribution (Particle := Fin (extra + 1))).mass retained *
        ∑ particles,
          (forcedIndependentPopulation (fun _ : Fin (extra + 1) => initial)
            retained first).mass particles *
            forcedLineageSuffixLabelExpectation
              (fun path y => path ++ [y]) steps first future
              hfuture
              particles retained (fun i => [particles i])
              (fun path => if path = proposed.toList then 1 else 0) := by
  rw [aggregatedForcedLineageMass_eq_forcedLineage_expectation
    initial hinitial steps hsupport hnormalizer extra current proposed]
  subst current
  simp_rw [← genealogicalTrajectoryFraction_eq_proposedTrajectoryFraction]
  unfold genealogicalTrajectoryFraction
  change (∑ selected,
      (forcedLineageLaw (Particle := Fin (extra + 1)) initial steps
        (first :: future) (by simp [hfuture])).mass selected *
        particleAverage (fun path : List Sample =>
          if path = proposed.toList then 1 else 0)
          (terminalLabels (fun path y => path ++ [y]) steps
            (fun i => [selected.1.1 i]) selected.1.2)) = _
  unfold forcedLineageLaw
  rw [Distribution.bind_expectation]
  apply Finset.sum_congr rfl
  intro retained _
  rw [Distribution.bind_expectation]
  congr 1
  apply Finset.sum_congr rfl
  intro particles _
  rw [Distribution.map_expectation]
  rfl

/-- The aggregated forced-lineage mass is exactly the trajectory particle-
Gibbs transition entry. This is an expansion theorem, not a minorization
assumption, and exposes the sum to which primitive Feynman--Kac estimates must
be applied. -/
theorem aggregatedForcedLineageMass_eq_kernel_prob
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps) (extra : ℕ)
    (current proposed : Trajectory steps) :
    aggregatedForcedLineageMass initial steps hnormalizer extra
        current proposed =
      (countedTrajectoryParticleGibbsKernel
        initial steps hnormalizer extra).prob current proposed := by
  exact (Mcmc.Finite.Conditional.collapsedKernel_prob_eq_aggregate
    (selectedParticleTarget (Particle := Fin (extra + 1))
      initial steps hnormalizer)
    (selectedTrajectoryVector steps)
    (selectedIndexRefreshKernel (Particle := Fin (extra + 1)) steps)
    current proposed).symm

/-- Aggregate-history form of the displayed particle-Gibbs minorization.
This deliberately supersedes the one-history witness when a coefficient must
remain uniform as the particle count grows. -/
structure AggregatedForcedLineageParticleGibbsBound
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps) (extra : ℕ)
    (bound : ℝ) where
  minorization : ∀ current proposed,
    particleGibbsCountCoefficient extra bound (steps.length + 1) *
        (countedTrajectoryTarget initial steps hnormalizer extra).mass proposed ≤
      aggregatedForcedLineageMass initial steps hnormalizer extra
        current proposed

/-- Base case of the sharp aggregate particle-Gibbs induction. With no
propagation steps, all compatible initial particles are aggregated and the
exact minorization coefficient is `(N - 1) / N`. -/
theorem aggregatedForcedLineageParticleGibbsBound_nil
    [Nonempty Sample]
    (initial : Distribution Sample) (hinitial : ∀ x, 0 < initial.mass x)
    (hnormalizer : 0 < normalizingConstant initial [])
    (extra : ℕ) :
    AggregatedForcedLineageParticleGibbsBound
      initial [] hnormalizer extra 1 := by
  constructor
  intro current proposed
  obtain ⟨currentFirst, hcurrent⟩ := trajectory_nil_eq_singleton current
  obtain ⟨proposedFirst, hproposed⟩ := trajectory_nil_eq_singleton proposed
  subst current
  subst proposed
  rw [countedTrajectoryTarget_nil_mass initial hinitial hnormalizer extra
    ⟨[proposedFirst], by simp⟩ proposedFirst rfl]
  have haggregate :=
    aggregatedForcedLineageMass_eq_recursiveLabelExpectation
      initial hinitial [] (by trivial) hnormalizer extra
      ⟨[currentFirst], by simp⟩ ⟨[proposedFirst], by simp⟩
      currentFirst [] (by simp) rfl
  rw [haggregate]
  simp only [particleGibbsCountCoefficient, List.length_nil, zero_add, pow_one,
    List.Vector.toList]
  let coefficient : ℝ := (extra : ℝ) / ((extra : ℝ) + 1)
  change coefficient * initial.mass proposedFirst ≤ _
  calc
    coefficient * initial.mass proposedFirst =
        ∑ retained : Fin (extra + 1),
          (uniformParticleDistribution (Particle := Fin (extra + 1))).mass retained *
            (coefficient * initial.mass proposedFirst) := by
      rw [← Finset.sum_mul,
        (uniformParticleDistribution (Particle := Fin (extra + 1))).sum_mass,
        one_mul]
    _ ≤ ∑ retained : Fin (extra + 1),
        (uniformParticleDistribution (Particle := Fin (extra + 1))).mass retained *
          ∑ particles,
            (forcedIndependentPopulation
              (fun _ : Fin (extra + 1) => initial)
              retained currentFirst).mass particles *
              forcedLineageSuffixLabelExpectation
                (fun path y => path ++ [y]) [] currentFirst [] (by simp)
                particles retained (fun i => [particles i])
                (fun path => if path = [proposedFirst] then 1 else 0) := by
      apply Finset.sum_le_sum
      intro retained _
      apply mul_le_mul_of_nonneg_left
      · simpa [coefficient, initialStateFraction, particleAverage] using
          (forcedInitialPopulation_initialStateFraction_ge
            initial extra retained currentFirst proposedFirst)
      · exact (uniformParticleDistribution
          (Particle := Fin (extra + 1))).nonneg retained

/-- An aggregate-history certificate yields the existing pointwise
minorization API without losing any compatible-history mass. -/
def AggregatedForcedLineageParticleGibbsBound.toMinorization
    {initial : Distribution Sample} {steps : List (FeynmanKacStep Sample)}
    {hnormalizer : 0 < normalizingConstant initial steps} {extra : ℕ}
    {bound : ℝ} (hextra : 0 < extra) (hbound : 0 < bound)
    (certificate : AggregatedForcedLineageParticleGibbsBound
      initial steps hnormalizer extra bound) :
    BoundedPotentialParticleGibbsMinorization
      initial steps hnormalizer extra where
  bound := bound
  extra_pos := hextra
  bound_pos := hbound
  minorization current proposed := by
    rw [← aggregatedForcedLineageMass_eq_kernel_prob]
    exact certificate.minorization current proposed

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

/-- Primitive full support gives one count-specific positive lower bound for
the explicit shared-history edge used by forced-lineage particle Gibbs. This
is the finite-model quantitative compactness step; the subsequent theorem
compares the displayed count coefficient with this floor. -/
theorem exists_forcedLineageRatio_floor_of_fullSupport
    [Nonempty Sample]
    (initial : Distribution Sample) (hinitial : ∀ x, 0 < initial.mass x)
    (steps : List (FeynmanKacStep Sample))
    (hsupport : FeynmanKacFullSupport steps)
    (hnormalizer : 0 < normalizingConstant initial steps)
    (extra : ℕ) (hextra : 0 < extra) :
    ∃ floor : ℝ, 0 < floor ∧ floor ≤ 1 ∧ ∀ current proposed,
      ∃ history : History (Particle := Fin (extra + 1)) steps,
      ∃ currentIndex proposedIndex : Fin (extra + 1),
        selectedTrajectoryVector steps (history, currentIndex) = current ∧
        selectedTrajectoryVector steps (history, proposedIndex) = proposed ∧
        floor *
            (countedTrajectoryTarget initial steps hnormalizer extra).mass
              proposed ≤
          (selectedParticleTarget (Particle := Fin (extra + 1))
              initial steps hnormalizer).mass (history, currentIndex) /
            (countedTrajectoryTarget initial steps hnormalizer extra).mass
              current /
            Fintype.card (Fin (extra + 1)) := by
  classical
  letI : Nonempty (Trajectory steps) :=
    ⟨⟨List.replicate (steps.length + 1)
      (Classical.choice ‹Nonempty Sample›), by simp⟩⟩
  let currentIndex : Fin (extra + 1) := ⟨0, by omega⟩
  let proposedIndex : Fin (extra + 1) := ⟨extra, by omega⟩
  have hindices : currentIndex ≠ proposedIndex := by
    intro h
    have := congrArg Fin.val h
    simp [currentIndex, proposedIndex] at this
    omega
  let historyFor := fun current proposed : Trajectory steps =>
    pairedHistoryAt proposedIndex steps current proposed
  let edgeRatio := fun pair : Trajectory steps × Trajectory steps =>
    ((selectedParticleTarget (Particle := Fin (extra + 1))
          initial steps hnormalizer).mass
        (historyFor pair.1 pair.2, currentIndex) /
      (countedTrajectoryTarget initial steps hnormalizer extra).mass pair.1 /
      Fintype.card (Fin (extra + 1))) /
      (countedTrajectoryTarget initial steps hnormalizer extra).mass pair.2
  have hedgeRatio : ∀ pair, 0 < edgeRatio pair := by
    intro pair
    unfold edgeRatio
    have hextended := selectedParticleTarget_mass_pos
      (Particle := Fin (extra + 1)) initial hinitial steps hsupport
      hnormalizer (historyFor pair.1 pair.2, currentIndex)
    have hcurrent := countedTrajectoryTarget_mass_pos_of_fullSupport
      initial hinitial steps hsupport hnormalizer extra pair.1
    have hproposed := countedTrajectoryTarget_mass_pos_of_fullSupport
      initial hinitial steps hsupport hnormalizer extra pair.2
    positivity
  obtain ⟨floor, hfloor, hfloorOne, hfloorLe⟩ :=
    exists_uniformPositiveFloor edgeRatio hedgeRatio
  refine ⟨floor, hfloor, hfloorOne, ?_⟩
  intro current proposed
  refine ⟨historyFor current proposed, currentIndex, proposedIndex,
    selectedTrajectoryVector_pairedHistoryAt_current
      currentIndex proposedIndex hindices steps current proposed,
    selectedTrajectoryVector_pairedHistoryAt_proposed
      proposedIndex steps current proposed, ?_⟩
  have htarget := countedTrajectoryTarget_mass_pos_of_fullSupport
    initial hinitial steps hsupport hnormalizer extra proposed
  let raw :=
    (selectedParticleTarget (Particle := Fin (extra + 1))
        initial steps hnormalizer).mass
      (historyFor current proposed, currentIndex) /
      (countedTrajectoryTarget initial steps hnormalizer extra).mass current /
      Fintype.card (Fin (extra + 1))
  have hle := hfloorLe (current, proposed)
  unfold edgeRatio at hle
  change floor ≤ raw /
    (countedTrajectoryTarget initial steps hnormalizer extra).mass proposed at hle
  calc
    floor *
        (countedTrajectoryTarget initial steps hnormalizer extra).mass
          proposed ≤
      (raw /
        (countedTrajectoryTarget initial steps hnormalizer extra).mass proposed) *
        (countedTrajectoryTarget initial steps hnormalizer extra).mass
          proposed :=
      mul_le_mul_of_nonneg_right hle htarget.le
    _ = raw := div_mul_cancel₀ raw htarget.ne'
    _ = (selectedParticleTarget (Particle := Fin (extra + 1))
          initial steps hnormalizer).mass
        (historyFor current proposed, currentIndex) /
      (countedTrajectoryTarget initial steps hnormalizer extra).mass current /
      Fintype.card (Fin (extra + 1)) := rfl

/-- Primitive finite full support constructs an actual count-specific
forced-lineage certificate. The resulting bound is conservative and may
depend on the count; sharper count-uniform Feynman--Kac estimates can replace
this finite minimum without changing the downstream convergence API. -/
theorem exists_forcedLineageParticleGibbsBound_of_fullSupport
    [Nonempty Sample]
    (initial : Distribution Sample) (hinitial : ∀ x, 0 < initial.mass x)
    (steps : List (FeynmanKacStep Sample))
    (hsupport : FeynmanKacFullSupport steps)
    (hnormalizer : 0 < normalizingConstant initial steps)
    (extra : ℕ) (hextra : 0 < extra) :
    ∃ bound : ℝ, 0 < bound ∧
      ForcedLineageParticleGibbsBound
        initial steps hnormalizer extra bound := by
  obtain ⟨floor, hfloor, _hfloorOne, hfloorWitness⟩ :=
    exists_forcedLineageRatio_floor_of_fullSupport
      initial hinitial steps hsupport hnormalizer extra hextra
  obtain ⟨bound, hbound, hcoefficient⟩ :=
    exists_particleGibbsCountBound_le_floor
      hextra (by omega : 0 < steps.length + 1) hfloor
  refine ⟨bound, hbound, ?_⟩
  refine
    { currentFiber_pos := countedTrajectoryTarget_mass_pos_of_fullSupport
        initial hinitial steps hsupport hnormalizer extra
      witness := ?_ }
  intro current proposed
  obtain ⟨history, currentIndex, proposedIndex, hcurrent, hproposed,
    hedge⟩ := hfloorWitness current proposed
  refine ⟨history, currentIndex, proposedIndex, hcurrent, hproposed, ?_⟩
  exact (mul_le_mul_of_nonneg_right hcoefficient
    ((countedTrajectoryTarget initial steps hnormalizer extra).nonneg proposed)).trans
      hedge

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

/-- Primitive full support therefore yields a displayed count/horizon
geometric TV bound, rather than only an opaque strictly-positive-matrix rate.
The selected `bound` is count-specific; a count-uniform primitive estimate is
still required for the large-particle limit theorem below. -/
theorem exists_countedFullSupportParticleGibbs_coefficient_bound
    [Nonempty Sample]
    (initial : Distribution Sample) (hinitial : ∀ x, 0 < initial.mass x)
    (steps : List (FeynmanKacStep Sample))
    (hsupport : FeynmanKacFullSupport steps)
    (hnormalizer : 0 < normalizingConstant initial steps)
    (extra : ℕ) (hextra : 0 < extra) :
    ∃ bound : ℝ, 0 < bound ∧
      ∀ (initialLaw : Distribution (Trajectory steps)) (iterations : ℕ),
        Nonhomogeneous.distributionTotalVariation
          (Nonhomogeneous.iterateLaw initialLaw
            (countedTrajectoryParticleGibbsKernel
              initial steps hnormalizer extra) iterations)
          (countedTrajectoryTarget initial steps hnormalizer extra) ≤
            (1 - particleGibbsCountCoefficient extra bound
              (steps.length + 1)) ^ iterations := by
  obtain ⟨bound, hbound, certificate⟩ :=
    exists_forcedLineageParticleGibbsBound_of_fullSupport
      initial hinitial steps hsupport hnormalizer extra hextra
  let minorization := certificate.toMinorization hextra hbound
  refine ⟨bound, hbound, ?_⟩
  intro initialLaw iterations
  exact boundedPotentialParticleGibbs_totalVariation_le
    minorization initialLaw iterations

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

/-- If the same finite model bound supplies the displayed PG minorization at
every particle count, then for every fixed positive number of PG iterations
the actual count-indexed output law approaches its trajectory target as the
number of particles tends to infinity.  The index `extra` below represents
`extra + 2` total particles, keeping the retained particle and at least one
additional particle present at every index. -/
theorem boundedPotentialParticleGibbs_totalVariation_tendsto_zero_count
    {initial : Distribution Sample} {steps : List (FeynmanKacStep Sample)}
    {hnormalizer : 0 < normalizingConstant initial steps} {bound : ℝ}
    (certificates : ∀ extra : ℕ,
      BoundedPotentialParticleGibbsMinorization
        initial steps hnormalizer (extra + 1))
    (hbound : ∀ extra, (certificates extra).bound = bound)
    (initialLaw : Distribution (Trajectory steps))
    (iterations : ℕ) (hiterations : 0 < iterations) :
    Filter.Tendsto (fun extra =>
      Nonhomogeneous.distributionTotalVariation
        (Nonhomogeneous.iterateLaw initialLaw
          (countedTrajectoryParticleGibbsKernel initial steps hnormalizer
            (extra + 1)) iterations)
        (countedTrajectoryTarget initial steps hnormalizer (extra + 1)))
      Filter.atTop (nhds 0) := by
  have hrate : Filter.Tendsto (fun extra =>
      (1 - particleGibbsCountCoefficient (extra + 1) bound
        (steps.length + 1)) ^ iterations) Filter.atTop (nhds 0) := by
    have h := (particleGibbsCountRate_tendsto_zero bound
      (steps.length + 1) iterations hiterations).comp
        (Filter.tendsto_add_atTop_nat 1)
    simpa [Function.comp_def, Nat.add_comm] using h
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun extra =>
      Nonhomogeneous.distributionTotalVariation_nonneg _ _)
    (Filter.Eventually.of_forall fun extra => ?_) hrate
  simpa only [hbound extra] using
    boundedPotentialParticleGibbs_totalVariation_le
      (certificates extra) initialLaw iterations

/-- A single aggregate-history bound valid at every count gives the actual
fixed-iteration particle-count limit. This is the direct consumer for a
primitive Feynman--Kac aggregate estimate; no single-history witness is used. -/
theorem aggregatedForcedLineage_totalVariation_tendsto_zero_count
    {initial : Distribution Sample} {steps : List (FeynmanKacStep Sample)}
    {hnormalizer : 0 < normalizingConstant initial steps} {bound : ℝ}
    (hbound : 0 < bound)
    (certificates : ∀ extra : ℕ,
      AggregatedForcedLineageParticleGibbsBound
        initial steps hnormalizer (extra + 1) bound)
    (initialLaw : Distribution (Trajectory steps))
    (iterations : ℕ) (hiterations : 0 < iterations) :
    Filter.Tendsto (fun extra =>
      Nonhomogeneous.distributionTotalVariation
        (Nonhomogeneous.iterateLaw initialLaw
          (countedTrajectoryParticleGibbsKernel initial steps hnormalizer
            (extra + 1)) iterations)
        (countedTrajectoryTarget initial steps hnormalizer (extra + 1)))
      Filter.atTop (nhds 0) := by
  let bounded : ∀ extra : ℕ,
      BoundedPotentialParticleGibbsMinorization
        initial steps hnormalizer (extra + 1) := fun extra =>
    (certificates extra).toMinorization (by omega) hbound
  apply boundedPotentialParticleGibbs_totalVariation_tendsto_zero_count
    bounded (bound := bound) (hbound := by intro extra; rfl)
    initialLaw iterations hiterations

/-- Scheduled PG certificates give the corresponding large-particle theorem
when the penalty list is common to every count. -/
theorem scheduledPotentialParticleGibbs_totalVariation_tendsto_zero_count
    {initial : Distribution Sample} {steps : List (FeynmanKacStep Sample)}
    {hnormalizer : 0 < normalizingConstant initial steps}
    {penalties : List ℝ}
    (certificates : ∀ extra : ℕ,
      ScheduledPotentialParticleGibbsMinorization
        initial steps hnormalizer (extra + 1))
    (hpenalties : ∀ extra, (certificates extra).penalties = penalties)
    (initialLaw : Distribution (Trajectory steps))
    (iterations : ℕ) (hiterations : 0 < iterations) :
    Filter.Tendsto (fun extra =>
      Nonhomogeneous.distributionTotalVariation
        (Nonhomogeneous.iterateLaw initialLaw
          (countedTrajectoryParticleGibbsKernel initial steps hnormalizer
            (extra + 1)) iterations)
        (countedTrajectoryTarget initial steps hnormalizer (extra + 1)))
      Filter.atTop (nhds 0) := by
  have hrate : Filter.Tendsto (fun extra =>
      (1 - particleGibbsScheduleCoefficient (extra + 1) penalties) ^
        iterations) Filter.atTop (nhds 0) := by
    have h := (particleGibbsScheduleRate_tendsto_zero penalties iterations
      hiterations).comp (Filter.tendsto_add_atTop_nat 1)
    simpa [Function.comp_def, Nat.add_comm] using h
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun extra =>
      Nonhomogeneous.distributionTotalVariation_nonneg _ _)
    (Filter.Eventually.of_forall fun extra => ?_) hrate
  simpa only [hpenalties extra] using
    scheduledPotentialParticleGibbs_totalVariation_le
      (certificates extra) initialLaw iterations

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
