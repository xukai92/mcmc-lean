import Mathlib.Probability.Process.HittingTime
import McmcLean.Kernel.Coupling

/-!
# Meeting events and meeting times

This module defines the exact and lag-one meeting events used in coupled
MCMC. Paths are sequences of pairs: the first coordinate is the `X` chain and
the second coordinate is the `Y` chain. The lag-one meeting time starts at
time one and records the first `n` for which `X n = Y (n - 1)`.

The definitions reuse mathlib's `hittingAfter`, so failure to meet is
represented by `⊤ : WithTop ℕ`. Measurability of equality is kept explicit
through mathlib's `MeasurableEq` typeclass.
-/

open MeasureTheory

namespace McmcLean
namespace Kernel

variable {α : Type*} [MeasurableSpace α]

/-- The event that the two coordinates of a paired path agree at time `n`. -/
def exactMeetingEvent (n : ℕ) : Set (ℕ → α × α) :=
  {path | (path n).1 = (path n).2}

/-- Exact meeting at a fixed time is measurable when equality in the state
space is measurable. -/
theorem measurableSet_exactMeetingEvent [MeasurableEq α] (n : ℕ) :
    MeasurableSet (exactMeetingEvent (α := α) n) := by
  exact measurableSet_eq_fun ((measurable_pi_apply n).fst) ((measurable_pi_apply n).snd)

/-- The paired state compared by the lag-one meeting criterion at time `n`. -/
def lagOnePair (n : ℕ) (path : ℕ → α × α) : α × α :=
  ((path n).1, (path (n - 1)).2)

/-- The lag-one pair is a measurable function of the full paired path. -/
theorem measurable_lagOnePair (n : ℕ) : Measurable (lagOnePair (α := α) n) :=
  ((measurable_pi_apply n).fst).prodMk ((measurable_pi_apply (n - 1)).snd)

/-- The event `X n = Y (n - 1)`. The intended meeting times use `n ≥ 1`. -/
def lagOneMeetingEvent (n : ℕ) : Set (ℕ → α × α) :=
  {path | (path n).1 = (path (n - 1)).2}

/-- Lag-one meeting at a fixed time is measurable. -/
theorem measurableSet_lagOneMeetingEvent [MeasurableEq α] (n : ℕ) :
    MeasurableSet (lagOneMeetingEvent (α := α) n) := by
  exact measurableSet_eq_fun ((measurable_pi_apply n).fst)
    ((measurable_pi_apply (n - 1)).snd)

/-- First time at or after zero at which the paired coordinates agree. -/
noncomputable def exactMeetingTime (path : ℕ → α × α) : WithTop ℕ :=
  hittingAfter (fun n path => path n) (Set.diagonal α) 0 path

/-- First time at or after one at which `X n = Y (n - 1)`. -/
noncomputable def lagOneMeetingTime (path : ℕ → α × α) : WithTop ℕ :=
  hittingAfter (lagOnePair (α := α)) (Set.diagonal α) 1 path

omit [MeasurableSpace α] in
/-- Exact meeting occurs by `n` exactly when it occurs at some time from zero
through `n`. -/
theorem exactMeetingTime_le_iff (path : ℕ → α × α) (n : ℕ) :
    exactMeetingTime path ≤ n ↔ ∃ j ∈ Set.Icc 0 n, (path j).1 = (path j).2 := by
  rw [exactMeetingTime]
  constructor
  · intro h
    rcases (hittingAfter_le_iff.mp h) with ⟨j, hj, hmeet⟩
    exact ⟨j, hj, Set.mem_diagonal_iff.mp hmeet⟩
  · rintro ⟨j, hj, hmeet⟩
    exact hittingAfter_le_iff.mpr ⟨j, hj, Set.mem_diagonal_iff.mpr hmeet⟩

omit [MeasurableSpace α] in
/-- Lag-one meeting occurs by `n` exactly when `X j = Y (j - 1)` for some
`j` between one and `n`. -/
theorem lagOneMeetingTime_le_iff (path : ℕ → α × α) (n : ℕ) :
    lagOneMeetingTime path ≤ n ↔
      ∃ j ∈ Set.Icc 1 n, (path j).1 = (path (j - 1)).2 := by
  rw [lagOneMeetingTime]
  constructor
  · intro h
    rcases (hittingAfter_le_iff.mp h) with ⟨j, hj, hmeet⟩
    exact ⟨j, hj, Set.mem_diagonal_iff.mp hmeet⟩
  · rintro ⟨j, hj, hmeet⟩
    exact hittingAfter_le_iff.mpr ⟨j, hj, Set.mem_diagonal_iff.mpr hmeet⟩

omit [MeasurableSpace α] in
/-- The lag-one meeting time cannot be zero. -/
theorem one_le_lagOneMeetingTime (path : ℕ → α × α) :
    (1 : WithTop ℕ) ≤ lagOneMeetingTime path := by
  exact le_hittingAfter (u := lagOnePair (α := α))
    (s := Set.diagonal α) (n := 1) path

/-- Paths whose two coordinates have not met at any time through `n`. -/
def exactMeetingFailureEvent (n : ℕ) : Set (ℕ → α × α) :=
  (⋃ j ∈ Finset.range (n + 1), exactMeetingEvent (α := α) j)ᶜ

/-- Failure through time `n` is measurable. -/
theorem measurableSet_exactMeetingFailureEvent [MeasurableEq α] (n : ℕ) :
    MeasurableSet (exactMeetingFailureEvent (α := α) n) := by
  apply MeasurableSet.compl
  apply MeasurableSet.iUnion
  intro j
  apply MeasurableSet.iUnion
  intro hj
  exact measurableSet_exactMeetingEvent j

omit [MeasurableSpace α] in
/-- The explicit finite failure event is exactly the strict tail event of the
`WithTop ℕ` meeting time. -/
theorem mem_exactMeetingFailureEvent_iff
    (path : ℕ → α × α) (n : ℕ) :
    path ∈ exactMeetingFailureEvent n ↔
      (n : WithTop ℕ) < exactMeetingTime path := by
  rw [show (n : WithTop ℕ) < exactMeetingTime path ↔
      ¬ exactMeetingTime path ≤ n by exact not_le.symm,
    exactMeetingTime_le_iff]
  constructor
  · intro hfail hmeet
    rcases hmeet with ⟨j, hj, heq⟩
    apply hfail
    apply Set.mem_iUnion.mpr
    refine ⟨j, Set.mem_iUnion.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj.2), ?_⟩⟩
    exact heq
  · intro hnot
    change path ∉ ⋃ j ∈ Finset.range (n + 1), exactMeetingEvent j
    intro hunion
    rcases Set.mem_iUnion.mp hunion with ⟨j, hunion⟩
    rcases Set.mem_iUnion.mp hunion with ⟨hj, heq⟩
    exact hnot ⟨j, ⟨Nat.zero_le j,
      Nat.le_of_lt_succ (Finset.mem_range.mp hj)⟩, heq⟩

omit [MeasurableSpace α] in
/-- A path that has not met through time `n` is necessarily off the diagonal
at time `n`. No faithfulness hypothesis is needed for this direction. -/
theorem exactMeetingFailureEvent_subset_eval_compl_diagonal (n : ℕ) :
    exactMeetingFailureEvent (α := α) n ⊆
      (fun path : ℕ → α × α => path n) ⁻¹' (Set.diagonal α)ᶜ := by
  intro path hfail hdiag
  apply hfail
  apply Set.mem_iUnion.mpr
  refine ⟨n, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_self n), ?_⟩⟩
  exact Set.mem_diagonal_iff.mp hdiag

omit [MeasurableSpace α] in
/-- Failure events decrease with time: failing through a later time implies
failure through every earlier time. -/
theorem antitone_exactMeetingFailureEvent :
    Antitone (exactMeetingFailureEvent (α := α)) := by
  intro m n hmn path hn
  rw [mem_exactMeetingFailureEvent_iff] at hn ⊢
  exact lt_of_le_of_lt (by exact_mod_cast hmn) hn

/-- Paths that have not met in the lag-one sense at any time from one through
`n`. For `n = 0` this is the whole path space. -/
def lagOneMeetingFailureEvent (n : ℕ) : Set (ℕ → α × α) :=
  (⋃ j ∈ Finset.Icc 1 n, lagOneMeetingEvent (α := α) j)ᶜ

/-- Lag-one failure through a finite horizon is measurable. -/
theorem measurableSet_lagOneMeetingFailureEvent [MeasurableEq α] (n : ℕ) :
    MeasurableSet (lagOneMeetingFailureEvent (α := α) n) := by
  apply MeasurableSet.compl
  apply MeasurableSet.iUnion
  intro j
  apply MeasurableSet.iUnion
  intro _hj
  exact measurableSet_lagOneMeetingEvent j

omit [MeasurableSpace α] in
/-- The finite lag-one failure event is exactly the strict tail event of the
lag-one meeting time. -/
theorem mem_lagOneMeetingFailureEvent_iff
    (path : ℕ → α × α) (n : ℕ) :
    path ∈ lagOneMeetingFailureEvent n ↔
      (n : WithTop ℕ) < lagOneMeetingTime path := by
  rw [show (n : WithTop ℕ) < lagOneMeetingTime path ↔
      ¬ lagOneMeetingTime path ≤ n by exact not_le.symm,
    lagOneMeetingTime_le_iff]
  constructor
  · intro hfail hmeet
    rcases hmeet with ⟨j, hj, heq⟩
    apply hfail
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr
      ⟨Finset.mem_Icc.mpr hj, heq⟩⟩
  · intro hnot
    change path ∉ ⋃ j ∈ Finset.Icc 1 n, lagOneMeetingEvent j
    intro hunion
    rcases Set.mem_iUnion.mp hunion with ⟨j, hunion⟩
    rcases Set.mem_iUnion.mp hunion with ⟨hj, heq⟩
    exact hnot ⟨j, Finset.mem_Icc.mp hj, heq⟩

omit [MeasurableSpace α] in
/-- Lag-one failure events decrease with the horizon. -/
theorem antitone_lagOneMeetingFailureEvent :
    Antitone (lagOneMeetingFailureEvent (α := α)) := by
  intro m n hmn path hn
  rw [mem_lagOneMeetingFailureEvent_iff] at hn ⊢
  exact lt_of_le_of_lt (by exact_mod_cast hmn) hn

/-- Tail probability of the exact meeting time under a path measure. -/
noncomputable def exactMeetingTail
    (μ : Measure (ℕ → α × α)) (n : ℕ) : ENNReal :=
  μ (exactMeetingFailureEvent n)

/-- Tail probability of the lag-one meeting time under a paired path law. -/
noncomputable def lagOneMeetingTail
    (μ : Measure (ℕ → α × α)) (n : ℕ) : ENNReal :=
  μ (lagOneMeetingFailureEvent n)

/-- Meeting-time failure is bounded by the off-diagonal mass of the time-`n`
coordinate marginal. -/
theorem exactMeetingTail_le_map_offDiagonal
    [MeasurableEq α]
    (μ : Measure (ℕ → α × α)) (n : ℕ) :
    exactMeetingTail μ n ≤
      μ.map (fun path => path n) (Set.diagonal α)ᶜ := by
  rw [exactMeetingTail,
    Measure.map_apply (measurable_pi_apply n) measurableSet_diagonal.compl]
  exact measure_mono (exactMeetingFailureEvent_subset_eval_compl_diagonal n)

/-- Exact meeting-time tails are nonincreasing. -/
theorem antitone_exactMeetingTail (μ : Measure (ℕ → α × α)) :
    Antitone (exactMeetingTail μ) := by
  intro m n hmn
  exact measure_mono (antitone_exactMeetingFailureEvent hmn)

/-- Lag-one meeting-time tails are nonincreasing. -/
theorem antitone_lagOneMeetingTail (μ : Measure (ℕ → α × α)) :
    Antitone (lagOneMeetingTail μ) := by
  intro m n hmn
  exact measure_mono (antitone_lagOneMeetingFailureEvent hmn)

/-- A bound along positive block times yields a bound at every time by taking
the largest completed block. -/
theorem exactMeetingTail_le_of_skeleton
    (μ : Measure (ℕ → α × α)) (r : ENNReal) (block : ℕ)
    (_hblock : 0 < block)
    (hskeleton : ∀ k, exactMeetingTail μ (block * k) ≤ r ^ k)
    (n : ℕ) :
    exactMeetingTail μ n ≤ r ^ (n / block) := by
  apply (antitone_exactMeetingTail μ (Nat.mul_div_le n block)).trans
  exact hskeleton (n / block)

/-- A lag-one tail bound along block times extends to every time by monotonicity. -/
theorem lagOneMeetingTail_le_of_skeleton
    (μ : Measure (ℕ → α × α)) (r : ENNReal) (block : ℕ)
    (_hblock : 0 < block)
    (hskeleton : ∀ k, lagOneMeetingTail μ (block * k) ≤ r ^ k)
    (n : ℕ) :
    lagOneMeetingTail μ n ≤ r ^ (n / block) := by
  apply (antitone_lagOneMeetingTail μ (Nat.mul_div_le n block)).trans
  exact hskeleton (n / block)

/-- A one-step geometric recurrence for the failure probabilities closes to a
geometric meeting-time tail. This is the final probabilistic induction used
after drift and small-set arguments establish the recurrence. -/
theorem exactMeetingTail_le_geometric
    (μ : Measure (ℕ → α × α)) [IsProbabilityMeasure μ]
    (r : ENNReal)
    (hstep : ∀ n, exactMeetingTail μ (n + 1) ≤
      r * exactMeetingTail μ n) (n : ℕ) :
    exactMeetingTail μ n ≤ r ^ n := by
  induction n with
  | zero =>
      simp only [pow_zero]
      calc
        μ (exactMeetingFailureEvent 0) ≤ μ Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
  | succ n ih =>
      rw [pow_succ']
      apply (hstep n).trans
      gcongr

/-- A one-step recurrence for lag-one failure probabilities gives a geometric
tail for the actual lag-one meeting time. -/
theorem lagOneMeetingTail_le_geometric
    (μ : Measure (ℕ → α × α)) [IsProbabilityMeasure μ]
    (r : ENNReal)
    (hstep : ∀ n, lagOneMeetingTail μ (n + 1) ≤
      r * lagOneMeetingTail μ n) (n : ℕ) :
    lagOneMeetingTail μ n ≤ r ^ n := by
  induction n with
  | zero =>
      simp only [pow_zero]
      calc
        μ (lagOneMeetingFailureEvent 0) ≤ μ Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
  | succ n ih =>
      rw [pow_succ']
      apply (hstep n).trans
      gcongr

section Relaxed

variable [PseudoMetricSpace α] [BorelSpace α] [SecondCountableTopology α]

/-- Relaxed diagonal of pairs whose coordinates are within distance `δ`. -/
def relaxedDiagonal (δ : ℝ) : Set (α × α) :=
  {z | dist z.1 z.2 ≤ δ}

theorem measurableSet_relaxedDiagonal (δ : ℝ) :
    MeasurableSet (relaxedDiagonal (α := α) δ) := by
  exact measurableSet_le measurable_dist measurable_const

/-- Event that a paired state is within the relaxed diagonal at time `n`.
When the paired Markov state is encoded as `(Xₙ,Yₙ₋₁)`, this is Xu et al.'s
relaxed lag-one event. -/
def relaxedPairMeetingEvent (δ : ℝ) (n : ℕ) : Set (ℕ → α × α) :=
  {path | path n ∈ relaxedDiagonal δ}

theorem measurableSet_relaxedPairMeetingEvent (δ : ℝ) (n : ℕ) :
    MeasurableSet (relaxedPairMeetingEvent (α := α) δ n) :=
  (measurableSet_relaxedDiagonal δ).preimage (measurable_pi_apply n)

/-- First entry time of the paired path into the relaxed diagonal. -/
noncomputable def relaxedPairMeetingTime
    (δ : ℝ) (path : ℕ → α × α) : WithTop ℕ :=
  hittingAfter (fun n path => path n) (relaxedDiagonal δ) 0 path

/-- Failure of paired-state relaxed meeting through time `n`. -/
def relaxedPairMeetingFailureEvent (δ : ℝ) (n : ℕ) :
    Set (ℕ → α × α) :=
  (⋃ j ∈ Finset.range (n + 1), relaxedPairMeetingEvent (α := α) δ j)ᶜ

theorem measurableSet_relaxedPairMeetingFailureEvent (δ : ℝ) (n : ℕ) :
    MeasurableSet (relaxedPairMeetingFailureEvent (α := α) δ n) := by
  apply MeasurableSet.compl
  apply MeasurableSet.iUnion
  intro j
  apply MeasurableSet.iUnion
  intro _hj
  exact measurableSet_relaxedPairMeetingEvent δ j

omit [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α] in
theorem mem_relaxedPairMeetingFailureEvent_iff
    (δ : ℝ) (path : ℕ → α × α) (n : ℕ) :
    path ∈ relaxedPairMeetingFailureEvent δ n ↔
      (n : WithTop ℕ) < relaxedPairMeetingTime δ path := by
  rw [show (n : WithTop ℕ) < relaxedPairMeetingTime δ path ↔
      ¬ relaxedPairMeetingTime δ path ≤ n by exact not_le.symm]
  constructor
  · intro hfail hmeet
    rw [relaxedPairMeetingTime] at hmeet
    rcases hittingAfter_le_iff.mp hmeet with ⟨j, hj, hclose⟩
    apply hfail
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj.2), hclose⟩⟩
  · intro hnot
    change path ∉ ⋃ j ∈ Finset.range (n + 1), relaxedPairMeetingEvent δ j
    intro hunion
    apply hnot
    rw [relaxedPairMeetingTime]
    apply hittingAfter_le_iff.mpr
    rcases Set.mem_iUnion.mp hunion with ⟨j, hunion⟩
    rcases Set.mem_iUnion.mp hunion with ⟨hj, hclose⟩
    exact ⟨j, ⟨Nat.zero_le j,
      Nat.le_of_lt_succ (Finset.mem_range.mp hj)⟩, hclose⟩

omit [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α] in
theorem antitone_relaxedPairMeetingFailureEvent (δ : ℝ) :
    Antitone (relaxedPairMeetingFailureEvent (α := α) δ) := by
  intro m n hmn path hn
  rw [mem_relaxedPairMeetingFailureEvent_iff] at hn ⊢
  exact lt_of_le_of_lt (by exact_mod_cast hmn) hn

omit [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α] in
/-- Failure to enter the relaxed diagonal through `n` implies that the
time-`n` paired state is outside it. -/
theorem relaxedPairMeetingFailureEvent_subset_eval_compl
    (δ : ℝ) (n : ℕ) :
    relaxedPairMeetingFailureEvent (α := α) δ n ⊆
      (fun path : ℕ → α × α => path n) ⁻¹' (relaxedDiagonal δ)ᶜ := by
  intro path hfail hclose
  apply hfail
  exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr
    ⟨Finset.mem_range.mpr (Nat.lt_succ_self n), hclose⟩⟩

/-- Tail of relaxed-diagonal entry for the paired-state encoding. -/
noncomputable def relaxedPairMeetingTail
    (μ : Measure (ℕ → α × α)) (δ : ℝ) (n : ℕ) : ENNReal :=
  μ (relaxedPairMeetingFailureEvent δ n)

omit [BorelSpace α] [SecondCountableTopology α] in
theorem antitone_relaxedPairMeetingTail
    (μ : Measure (ℕ → α × α)) (δ : ℝ) :
    Antitone (relaxedPairMeetingTail μ δ) := by
  intro m n hmn
  exact measure_mono (antitone_relaxedPairMeetingFailureEvent δ hmn)

/-- The paired-state relaxed meeting tail is bounded by the time-`n` mass
outside the relaxed diagonal. -/
theorem relaxedPairMeetingTail_le_map_compl
    (μ : Measure (ℕ → α × α)) (δ : ℝ) (n : ℕ) :
    relaxedPairMeetingTail μ δ n ≤
      μ.map (fun path => path n) (relaxedDiagonal δ)ᶜ := by
  rw [relaxedPairMeetingTail,
    Measure.map_apply (measurable_pi_apply n)
      (measurableSet_relaxedDiagonal δ).compl]
  exact measure_mono
    (relaxedPairMeetingFailureEvent_subset_eval_compl δ n)

omit [BorelSpace α] [SecondCountableTopology α] in
/-- A paired-state relaxed tail bound along block times extends to every time
by monotonicity. -/
theorem relaxedPairMeetingTail_le_of_skeleton
    (μ : Measure (ℕ → α × α)) (δ : ℝ) (r : ENNReal) (block : ℕ)
    (_hblock : 0 < block)
    (hskeleton : ∀ k, relaxedPairMeetingTail μ δ (block * k) ≤ r ^ k)
    (n : ℕ) :
    relaxedPairMeetingTail μ δ n ≤ r ^ (n / block) := by
  apply (antitone_relaxedPairMeetingTail μ δ (Nat.mul_div_le n block)).trans
  exact hskeleton (n / block)

omit [BorelSpace α] [SecondCountableTopology α] in
/-- A one-step recurrence closes to a geometric relaxed meeting tail for a
paired Markov state encoded as `(Xₙ,Yₙ₋₁)`. -/
theorem relaxedPairMeetingTail_le_geometric
    (μ : Measure (ℕ → α × α)) [IsProbabilityMeasure μ]
    (δ : ℝ) (r : ENNReal)
    (hstep : ∀ n, relaxedPairMeetingTail μ δ (n + 1) ≤
      r * relaxedPairMeetingTail μ δ n) (n : ℕ) :
    relaxedPairMeetingTail μ δ n ≤ r ^ n := by
  induction n with
  | zero =>
      simp only [pow_zero]
      calc
        μ (relaxedPairMeetingFailureEvent δ 0) ≤ μ Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
  | succ n ih =>
      rw [pow_succ']
      apply (hstep n).trans
      gcongr

/-- Event that the lag-one pair is within distance `δ` at time `n`. -/
def relaxedLagOneMeetingEvent (δ : ℝ) (n : ℕ) : Set (ℕ → α × α) :=
  {path | dist (path n).1 (path (n - 1)).2 ≤ δ}

theorem measurableSet_relaxedLagOneMeetingEvent (δ : ℝ) (n : ℕ) :
    MeasurableSet (relaxedLagOneMeetingEvent (α := α) δ n) := by
  exact measurableSet_le
    (((measurable_pi_apply n).fst).dist
      ((measurable_pi_apply (n - 1)).snd)) measurable_const

/-- First time at or after one when the lag-one pair is within distance `δ`. -/
noncomputable def relaxedLagOneMeetingTime
    (δ : ℝ) (path : ℕ → α × α) : WithTop ℕ :=
  hittingAfter (lagOnePair (α := α))
    (relaxedDiagonal δ) 1 path

omit [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α] in
/-- Relaxed lag-one meeting occurs by `n` exactly when it occurs at one of the
times `1,…,n`. -/
theorem relaxedLagOneMeetingTime_le_iff
    (δ : ℝ) (path : ℕ → α × α) (n : ℕ) :
    relaxedLagOneMeetingTime δ path ≤ n ↔
      ∃ j ∈ Set.Icc 1 n, dist (path j).1 (path (j - 1)).2 ≤ δ := by
  rw [relaxedLagOneMeetingTime]
  constructor
  · intro h
    rcases hittingAfter_le_iff.mp h with ⟨j, hj, hmeet⟩
    exact ⟨j, hj, hmeet⟩
  · rintro ⟨j, hj, hmeet⟩
    exact hittingAfter_le_iff.mpr ⟨j, hj, hmeet⟩

/-- Failure to meet in the relaxed lag-one sense through horizon `n`. -/
def relaxedLagOneMeetingFailureEvent (δ : ℝ) (n : ℕ) :
    Set (ℕ → α × α) :=
  (⋃ j ∈ Finset.Icc 1 n, relaxedLagOneMeetingEvent (α := α) δ j)ᶜ

theorem measurableSet_relaxedLagOneMeetingFailureEvent (δ : ℝ) (n : ℕ) :
    MeasurableSet (relaxedLagOneMeetingFailureEvent (α := α) δ n) := by
  apply MeasurableSet.compl
  apply MeasurableSet.iUnion
  intro j
  apply MeasurableSet.iUnion
  intro _hj
  exact measurableSet_relaxedLagOneMeetingEvent δ j

omit [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α] in
/-- The explicit relaxed failure event is the strict tail event of the relaxed
lag-one meeting time. -/
theorem mem_relaxedLagOneMeetingFailureEvent_iff
    (δ : ℝ) (path : ℕ → α × α) (n : ℕ) :
    path ∈ relaxedLagOneMeetingFailureEvent δ n ↔
      (n : WithTop ℕ) < relaxedLagOneMeetingTime δ path := by
  rw [show (n : WithTop ℕ) < relaxedLagOneMeetingTime δ path ↔
      ¬ relaxedLagOneMeetingTime δ path ≤ n by exact not_le.symm,
    relaxedLagOneMeetingTime_le_iff]
  constructor
  · intro hfail hmeet
    rcases hmeet with ⟨j, hj, hclose⟩
    apply hfail
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr
      ⟨Finset.mem_Icc.mpr hj, hclose⟩⟩
  · intro hnot
    change path ∉ ⋃ j ∈ Finset.Icc 1 n, relaxedLagOneMeetingEvent δ j
    intro hunion
    rcases Set.mem_iUnion.mp hunion with ⟨j, hunion⟩
    rcases Set.mem_iUnion.mp hunion with ⟨hj, hclose⟩
    exact hnot ⟨j, Finset.mem_Icc.mp hj, hclose⟩

omit [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α] in
theorem antitone_relaxedLagOneMeetingFailureEvent (δ : ℝ) :
    Antitone (relaxedLagOneMeetingFailureEvent (α := α) δ) := by
  intro m n hmn path hn
  rw [mem_relaxedLagOneMeetingFailureEvent_iff] at hn ⊢
  exact lt_of_le_of_lt (by exact_mod_cast hmn) hn

/-- Tail probability of the relaxed lag-one meeting time. -/
noncomputable def relaxedLagOneMeetingTail
    (μ : Measure (ℕ → α × α)) (δ : ℝ) (n : ℕ) : ENNReal :=
  μ (relaxedLagOneMeetingFailureEvent δ n)

omit [BorelSpace α] [SecondCountableTopology α] in
theorem antitone_relaxedLagOneMeetingTail
    (μ : Measure (ℕ → α × α)) (δ : ℝ) :
    Antitone (relaxedLagOneMeetingTail μ δ) := by
  intro m n hmn
  exact measure_mono (antitone_relaxedLagOneMeetingFailureEvent δ hmn)

omit [BorelSpace α] [SecondCountableTopology α] in
/-- A one-step recurrence closes to a geometric relaxed lag-one meeting tail. -/
theorem relaxedLagOneMeetingTail_le_geometric
    (μ : Measure (ℕ → α × α)) [IsProbabilityMeasure μ]
    (δ : ℝ) (r : ENNReal)
    (hstep : ∀ n, relaxedLagOneMeetingTail μ δ (n + 1) ≤
      r * relaxedLagOneMeetingTail μ δ n) (n : ℕ) :
    relaxedLagOneMeetingTail μ δ n ≤ r ^ n := by
  induction n with
  | zero =>
      simp only [pow_zero]
      calc
        μ (relaxedLagOneMeetingFailureEvent δ 0) ≤ μ Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
  | succ n ih =>
      rw [pow_succ']
      apply (hstep n).trans
      gcongr

end Relaxed

end Kernel
end McmcLean
