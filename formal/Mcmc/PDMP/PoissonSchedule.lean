import Mcmc.PDMP.EventSimulation
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic

/-!
# Conditional candidate times for a homogeneous Poisson clock

Conditional on exactly `n` clock candidates in a positive horizon, their
unordered timestamps are iid uniform on that horizon. This module constructs
that continuous probability law. Sorting these timestamps and coupling the
conditional laws to the Poisson count is the next path-law layer.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace Mcmc.PDMP

/-- Number of coordinates assigned to the first interval in a Boolean
interleaving of two adjacent timestamp vectors. -/
def boolAssignmentCount {n : ℕ} (assignment : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i => assignment i).card

/-- Coordinates sent to the first interval by an assignment. -/
def boolAssignmentSupport {n : ℕ} (assignment : Fin n → Bool) :
    Finset (Fin n) :=
  Finset.univ.filter fun i => assignment i

@[simp] theorem mem_boolAssignmentSupport {n : ℕ}
    (assignment : Fin n → Bool) (i : Fin n) :
    i ∈ boolAssignmentSupport assignment ↔ assignment i = true := by
  simp [boolAssignmentSupport]

theorem boolAssignmentSupport_injective {n : ℕ} :
    Function.Injective (boolAssignmentSupport (n := n)) := by
  intro first second hsupport
  funext i
  apply Bool.eq_iff_iff.mpr
  simpa only [← mem_boolAssignmentSupport] using
    Finset.ext_iff.mp hsupport i

theorem boolAssignmentCount_lt_succ {n : ℕ}
    (assignment : Fin n → Bool) :
    boolAssignmentCount assignment < n + 1 := by
  rw [Nat.lt_succ_iff]
  unfold boolAssignmentCount
  exact (Finset.card_filter_le (Finset.univ : Finset (Fin n)) _).trans_eq
    (by simp)

/-- A finite sum over interval assignments may be partitioned by the number
of timestamps assigned to the first interval. -/
theorem sum_boolAssignments_by_count {M : Type*} [AddCommMonoid M]
    (n : ℕ) (f : (Fin n → Bool) → M) :
    (∑ assignment, f assignment) =
      ∑ firstCount ∈ Finset.range (n + 1),
        ∑ assignment with boolAssignmentCount assignment = firstCount,
          f assignment := by
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (fun assignment _ => Finset.mem_range.mpr
      (boolAssignmentCount_lt_succ assignment)) f

/-- A countable measure sum over a finite index type is its ordinary finite
sum in the additive monoid of measures. -/
theorem measureSum_fintype {ι α : Type*} [Fintype ι]
    [MeasurableSpace α] (μ : ι → Measure α) :
    Measure.sum μ = ∑ i, μ i := by
  ext event hevent
  rw [Measure.sum_apply _ hevent, tsum_fintype]
  simp only [Measure.coe_finsetSum, Finset.sum_apply]

/-- Triangular total/count summation is the same as unrestricted summation
over the two adjacent interval counts. -/
theorem ENNReal.tsum_sum_range_succ_sub_eq_tsum_prod
    (f : ℕ → ℕ → ENNReal) :
    (∑' n : ℕ, ∑ k ∈ Finset.range (n + 1), f k (n - k)) =
      ∑' counts : ℕ × ℕ, f counts.1 counts.2 := by
  simp_rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ]
  rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq
    (fun counts : ℕ × ℕ => f counts.1 counts.2)]
  rw [ENNReal.tsum_sigma']
  apply tsum_congr
  intro n
  rw [tsum_fintype]
  simp only [Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply]
  rw [← Finset.sum_attach]
  rw [Finset.attach_eq_univ]

/-- Measure-valued triangular total/count summation is unrestricted
summation over the two component counts. -/
theorem measureSum_sum_range_succ_sub_eq_sum_prod
    {α : Type*} [MeasurableSpace α] (μ : ℕ → ℕ → Measure α) :
    Measure.sum (fun n : ℕ =>
      ∑ k ∈ Finset.range (n + 1), μ k (n - k)) =
      Measure.sum (fun counts : ℕ × ℕ => μ counts.1 counts.2) := by
  ext event hevent
  rw [Measure.sum_apply _ hevent, Measure.sum_apply _ hevent]
  simp only [Measure.coe_finsetSum, Finset.sum_apply]
  exact ENNReal.tsum_sum_range_succ_sub_eq_tsum_prod
    (fun k m => μ k m event)

/-- Two independent draws from an atomless s-finite measure agree with
product-measure mass zero. -/
theorem Measure.prod_diagonal_eq_zero {α : Type*} [MeasurableSpace α]
    [MeasurableEq α] (μ : Measure α) [SFinite μ]
    [NullSingletonClass μ] :
    μ.prod μ {pair | pair.1 = pair.2} = 0 := by
  rw [Measure.prod_apply
    (measurableSet_eq_fun measurable_fst measurable_snd)]
  simp

/-- Scaling every coordinate of a finite iid product scales the product law
by the corresponding power. -/
theorem pi_const_smul {α : Type*} [MeasurableSpace α]
    (c : ENNReal) (μ : Measure α) [SigmaFinite μ]
    [SigmaFinite (c • μ)] (n : ℕ) :
    Measure.pi (fun _ : Fin n => c • μ) =
      c ^ n • Measure.pi (fun _ : Fin n => μ) := by
  apply Measure.pi_eq
  intro sets hsets
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Finset.prod_mul_distrib]
  simp

/-- Measurable pushforward distributes over ordinary finite sums of
measures. -/
theorem map_finset_sum {ι α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (f : α → β) (hf : Measurable f)
    (s : Finset ι) (μ : ι → Measure α) :
    Measure.map f (∑ i ∈ s, μ i) =
      ∑ i ∈ s, Measure.map f (μ i) := by
  simp only [← Measure.mapₗ_apply_of_measurable hf, map_sum]

/-- There are `n.choose k` assignments that place exactly `k` labeled
timestamps in the first interval. -/
theorem card_boolAssignments_count_eq (n k : ℕ) :
    (Finset.univ.filter fun assignment : Fin n → Bool =>
      boolAssignmentCount assignment = k).card = Nat.choose n k := by
  calc
    _ = (Finset.univ.powersetCard k : Finset (Finset (Fin n))).card := by
      apply Finset.card_bij
        (fun assignment _ => boolAssignmentSupport assignment)
      · intro assignment hassignment
        rw [Finset.mem_powersetCard]
        refine ⟨Finset.subset_univ _, ?_⟩
        exact (Finset.mem_filter.mp hassignment).2
      · intro first hfirst second hsecond heq
        exact boolAssignmentSupport_injective heq
      · intro support hsupport
        let assignment : Fin n → Bool := fun i => decide (i ∈ support)
        refine ⟨assignment, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          simpa [boolAssignmentCount, boolAssignmentSupport, assignment] using
            (Finset.mem_powersetCard.mp hsupport).2
        · ext i
          simp [boolAssignmentSupport, assignment]
    _ = Nat.choose n k := by simp

/-- Two Boolean interval assignments with the same count differ only by a
permutation of their labeled coordinates. -/
theorem exists_perm_boolAssignment_comp_eq {n : ℕ}
    {first second : Fin n → Bool}
    (hcount : boolAssignmentCount first = boolAssignmentCount second) :
    ∃ permutation : Equiv.Perm (Fin n),
      first ∘ permutation = second := by
  have hcard : (boolAssignmentSupport second).card =
      (boolAssignmentSupport first).card := by
    simpa [boolAssignmentCount, boolAssignmentSupport] using hcount.symm
  obtain ⟨permutation, hperm⟩ :=
    Equiv.Perm.exists_map_finset_eq
      (boolAssignmentSupport second) (boolAssignmentSupport first) hcard
  refine ⟨permutation, ?_⟩
  funext i
  apply Bool.eq_iff_iff.mpr
  have hi := congrArg (fun support : Finset (Fin n) => permutation i ∈ support)
    hperm
  have hi' : (permutation i ∈ boolAssignmentSupport first) =
      (i ∈ boolAssignmentSupport second) := by
    simpa using hi.symm
  simpa only [Function.comp_apply, ← mem_boolAssignmentSupport] using
    eq_iff_iff.mp hi'

/-- A finite product of a sum of two s-finite measures expands as the sum over
all Boolean coordinate assignments. This is the measure-theoretic binomial
identity used by adjacent Poisson schedule convolution. -/
theorem pi_add_eq_sum_bool {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] (n : ℕ) :
    Measure.pi (fun _ : Fin n => μ + ν) =
      Measure.sum fun assignment : Fin n → Bool =>
        Measure.pi fun i => if assignment i then μ else ν := by
  apply Measure.pi_eq
  intro sets hsets
  rw [Measure.sum_apply _
    (MeasurableSet.pi Set.countable_univ fun i _ => hsets i)]
  rw [tsum_fintype]
  rw [show (∏ i, (μ + ν) (sets i)) =
      ∏ i, ∑ choice : Bool, (if choice then μ else ν) (sets i) by
    apply Finset.prod_congr rfl
    intro i _
    rw [Measure.add_apply μ ν (sets i)]
    simp]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro assignment _
  letI : ∀ i, SigmaFinite (if assignment i then μ else ν) := by
    intro i
    split <;> infer_instance
  rw [Measure.pi_pi]

/-- A finite horizon with strictly positive duration. -/
structure PositiveHorizon where
  duration : NNReal
  positive : 0 < duration

/-- Concatenation of two strictly positive horizons. -/
def PositiveHorizon.add (first second : PositiveHorizon) : PositiveHorizon where
  duration := first.duration + second.duration
  positive := add_pos first.positive second.positive

@[simp] theorem PositiveHorizon.add_duration
    (first second : PositiveHorizon) :
    (first.add second).duration = first.duration + second.duration := rfl

/-- A positive horizon repeated a positive natural number of times. The index
`n` represents `n + 1` copies, avoiding an artificial zero-duration inhabitant
of `PositiveHorizon`. -/
def PositiveHorizon.repeatSucc (horizon : PositiveHorizon) :
    ℕ → PositiveHorizon
  | 0 => horizon
  | n + 1 => horizon.add (horizon.repeatSucc n)

@[simp] theorem PositiveHorizon.repeatSucc_zero
    (horizon : PositiveHorizon) :
    horizon.repeatSucc 0 = horizon := rfl

@[simp] theorem PositiveHorizon.repeatSucc_succ
    (horizon : PositiveHorizon) (n : ℕ) :
    horizon.repeatSucc (n + 1) = horizon.add (horizon.repeatSucc n) := rfl

@[simp] theorem PositiveHorizon.repeatSucc_duration
    (horizon : PositiveHorizon) (n : ℕ) :
    (horizon.repeatSucc n).duration = (n + 1) • horizon.duration := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [repeatSucc_succ, add_duration, ih]
      rw [add_nsmul]
      simp
      ring

/-- Unnormalized Lebesgue timestamp mass on a horizon. This is the analytic
measure beneath the normalized uniform timestamp and Poisson Janossy weights. -/
noncomputable def PositiveHorizon.timestampMassMeasure
    (horizon : PositiveHorizon) : Measure ℝ :=
  volume.restrict (Set.Ioc 0 (horizon.duration : ℝ))

instance PositiveHorizon.timestampMassMeasure.instIsFiniteMeasure
    (horizon : PositiveHorizon) :
    IsFiniteMeasure horizon.timestampMassMeasure := by
  unfold PositiveHorizon.timestampMassMeasure
  infer_instance

/-- Timestamp mass is supported on its defining positive horizon. -/
theorem PositiveHorizon.ae_timestampMassMeasure_mem
    (horizon : PositiveHorizon) :
    ∀ᵐ time ∂horizon.timestampMassMeasure,
      time ∈ Set.Ioc 0 (horizon.duration : ℝ) := by
  unfold PositiveHorizon.timestampMassMeasure
  exact ae_restrict_mem measurableSet_Ioc

/-- Every coordinate of the finite product timestamp-mass law lies in its
horizon almost surely. -/
theorem PositiveHorizon.ae_pi_timestampMassMeasure_mem
    (horizon : PositiveHorizon) (n : ℕ) :
    ∀ᵐ times ∂Measure.pi (fun _ : Fin n =>
      horizon.timestampMassMeasure),
      ∀ i, times i ∈ Set.Ioc 0 (horizon.duration : ℝ) := by
  rw [Filter.eventually_all]
  intro i
  exact Measure.tendsto_eval_ae_ae.eventually
    horizon.ae_timestampMassMeasure_mem

/-- Translation of the second horizon's timestamp mass occupies exactly the
adjacent interval after the first horizon. -/
theorem PositiveHorizon.map_add_duration_timestampMassMeasure
    (first second : PositiveHorizon) :
    Measure.map (fun time : ℝ => (first.duration : ℝ) + time)
        second.timestampMassMeasure =
      volume.restrict
        (Set.Ioc (first.duration : ℝ)
          ((first.duration + second.duration : NNReal) : ℝ)) := by
  let shift : ℝ ≃ᵐ ℝ := MeasurableEquiv.addLeft (first.duration : ℝ)
  have himage : shift '' Set.Ioc 0 (second.duration : ℝ) =
      Set.Ioc (first.duration : ℝ)
        ((first.duration + second.duration : NNReal) : ℝ) := by
    ext time
    simp only [Set.mem_image, Set.mem_Ioc, NNReal.coe_add]
    constructor
    · rintro ⟨source, ⟨hsource0, hsourceT⟩, rfl⟩
      change (first.duration : ℝ) < (first.duration : ℝ) + source ∧
        (first.duration : ℝ) + source ≤
          (first.duration : ℝ) + (second.duration : ℝ)
      constructor <;> linarith
    · intro htime
      refine ⟨time - (first.duration : ℝ), ?_, ?_⟩
      constructor <;> linarith
      change (first.duration : ℝ) +
        (time - (first.duration : ℝ)) = time
      ring
  change Measure.map shift
      (volume.restrict (Set.Ioc 0 (second.duration : ℝ))) = _
  rw [← himage]
  have hrestrict := shift.restrict_map volume
    (shift '' Set.Ioc 0 (second.duration : ℝ))
  rw [show Measure.map shift volume = volume by
      exact map_add_left_eq_self volume (first.duration : ℝ),
    Set.preimage_image_eq _ shift.injective] at hrestrict
  exact hrestrict.symm

/-- Timestamp mass is additive across adjacent horizons. -/
theorem PositiveHorizon.timestampMassMeasure_add
    (first second : PositiveHorizon) :
    (first.add second).timestampMassMeasure =
      first.timestampMassMeasure +
        Measure.map (fun time : ℝ => (first.duration : ℝ) + time)
          second.timestampMassMeasure := by
  rw [first.map_add_duration_timestampMassMeasure second]
  unfold PositiveHorizon.timestampMassMeasure
  rw [PositiveHorizon.add_duration, NNReal.coe_add]
  rw [← Measure.restrict_union
    (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc]
  rw [Set.Ioc_union_Ioc_eq_Ioc (NNReal.coe_nonneg first.duration)
    (by linarith [NNReal.coe_nonneg second.duration])]

/-- Continuous uniform probability measure on `(0, horizon]`. -/
noncomputable def PositiveHorizon.uniformTimeMeasure
    (horizon : PositiveHorizon) : Measure ℝ :=
  (ENNReal.ofReal (horizon.duration : ℝ))⁻¹ •
    volume.restrict (Set.Ioc 0 (horizon.duration : ℝ))

instance PositiveHorizon.uniformTimeMeasure.instIsProbabilityMeasure
    (horizon : PositiveHorizon) :
    IsProbabilityMeasure horizon.uniformTimeMeasure := by
  constructor
  rw [PositiveHorizon.uniformTimeMeasure, Measure.smul_apply,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Ioc]
  simp only [sub_zero, smul_eq_mul]
  exact ENNReal.inv_mul_cancel
    (ne_of_gt (ENNReal.ofReal_pos.2 (by exact_mod_cast horizon.positive)))
    ENNReal.ofReal_ne_top

instance PositiveHorizon.uniformTimeMeasure.instNullSingletonClass
    (horizon : PositiveHorizon) :
    NullSingletonClass horizon.uniformTimeMeasure where
  measure_singleton time := by
    unfold PositiveHorizon.uniformTimeMeasure
    rw [Measure.smul_apply]
    simp

/-- Multiplying the normalized uniform timestamp law by the horizon length
recovers unnormalized Lebesgue timestamp mass. -/
theorem PositiveHorizon.ofReal_duration_smul_uniformTimeMeasure
    (horizon : PositiveHorizon) :
    ENNReal.ofReal (horizon.duration : ℝ) • horizon.uniformTimeMeasure =
      horizon.timestampMassMeasure := by
  unfold PositiveHorizon.uniformTimeMeasure
    PositiveHorizon.timestampMassMeasure
  rw [smul_smul, ENNReal.mul_inv_cancel]
  · simp
  · exact ne_of_gt (ENNReal.ofReal_pos.2 (by exact_mod_cast horizon.positive))
  · exact ENNReal.ofReal_ne_top

/-- The unnormalized one-event law on a combined horizon is the sum of the
first-interval law and the translated second-interval law. -/
theorem PositiveHorizon.scaledUniformTimeMeasure_add
    (first second : PositiveHorizon) :
    ENNReal.ofReal ((first.add second).duration : ℝ) •
        (first.add second).uniformTimeMeasure =
      ENNReal.ofReal (first.duration : ℝ) • first.uniformTimeMeasure +
        Measure.map (fun time : ℝ => (first.duration : ℝ) + time)
          (ENNReal.ofReal (second.duration : ℝ) •
            second.uniformTimeMeasure) := by
  rw [(first.add second).ofReal_duration_smul_uniformTimeMeasure,
    first.ofReal_duration_smul_uniformTimeMeasure,
    second.ofReal_duration_smul_uniformTimeMeasure]
  exact first.timestampMassMeasure_add second

/-- The `n`-event timestamp mass on adjacent horizons expands into all
Boolean assignments of labeled coordinates to the first or shifted-second
interval. -/
theorem PositiveHorizon.pi_timestampMassMeasure_add
    (first second : PositiveHorizon) (n : ℕ) :
    Measure.pi (fun _ : Fin n => (first.add second).timestampMassMeasure) =
      Measure.sum fun assignment : Fin n → Bool =>
        Measure.pi fun i =>
          if assignment i then first.timestampMassMeasure
          else Measure.map (fun time : ℝ => (first.duration : ℝ) + time)
            second.timestampMassMeasure := by
  rw [first.timestampMassMeasure_add second]
  exact pi_add_eq_sum_bool first.timestampMassMeasure
    (Measure.map (fun time : ℝ => (first.duration : ℝ) + time)
      second.timestampMassMeasure) n

/-- A draw from the continuous horizon law lies in `(0, horizon]` almost
surely. -/
theorem PositiveHorizon.ae_uniformTimeMeasure_mem
    (horizon : PositiveHorizon) :
    ∀ᵐ time ∂horizon.uniformTimeMeasure,
      time ∈ Set.Ioc 0 (horizon.duration : ℝ) := by
  unfold PositiveHorizon.uniformTimeMeasure
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Ioc) _

/-- The same uniform timestamp law represented directly in nonnegative time. -/
noncomputable def PositiveHorizon.uniformNNRealTimeMeasure
    (horizon : PositiveHorizon) : Measure NNReal :=
  Measure.map Real.toNNReal horizon.uniformTimeMeasure

instance PositiveHorizon.uniformNNRealTimeMeasure.instIsProbabilityMeasure
    (horizon : PositiveHorizon) :
    IsProbabilityMeasure horizon.uniformNNRealTimeMeasure := by
  unfold PositiveHorizon.uniformNNRealTimeMeasure
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- Iid unordered candidate timestamps conditional on a fixed candidate
count. -/
noncomputable def PositiveHorizon.candidateTimesMeasure
    (horizon : PositiveHorizon) (candidateCount : ℕ) :
    Measure (Fin candidateCount → ℝ) :=
  Measure.pi fun _ => horizon.uniformTimeMeasure

/-- Two iid continuous candidate timestamps are unequal almost surely. -/
theorem PositiveHorizon.ae_candidateTimesMeasure_two_ne
    (horizon : PositiveHorizon) :
    ∀ᵐ times ∂horizon.candidateTimesMeasure 2, times 0 ≠ times 1 := by
  have hpair : ∀ᵐ pair ∂horizon.uniformTimeMeasure.prod
      horizon.uniformTimeMeasure, pair.1 ≠ pair.2 := by
    apply ae_iff.mpr
    simpa only [not_not] using
      Measure.prod_diagonal_eq_zero horizon.uniformTimeMeasure
  have hpull := (measurePreserving_piFinTwo
    (fun _ : Fin 2 => horizon.uniformTimeMeasure)).quasiMeasurePreserving.ae
      hpair
  simpa [PositiveHorizon.candidateTimesMeasure,
    MeasurableEquiv.piFinTwo_apply] using hpull

instance PositiveHorizon.candidateTimesMeasure.instIsProbabilityMeasure
    (horizon : PositiveHorizon) (candidateCount : ℕ) :
    IsProbabilityMeasure (horizon.candidateTimesMeasure candidateCount) := by
  unfold PositiveHorizon.candidateTimesMeasure
  infer_instance

/-- Every coordinate of an iid candidate-time tuple lies in the horizon
almost surely. -/
theorem PositiveHorizon.ae_candidateTimesMeasure_mem
    (horizon : PositiveHorizon) (candidateCount : ℕ) :
    ∀ᵐ times ∂horizon.candidateTimesMeasure candidateCount,
      ∀ i, times i ∈ Set.Ioc 0 (horizon.duration : ℝ) := by
  unfold PositiveHorizon.candidateTimesMeasure
  rw [Filter.eventually_all]
  intro i
  exact Measure.tendsto_eval_ae_ae.eventually
    horizon.ae_uniformTimeMeasure_mem

/-- A certified measurable ordering of a fixed-size timestamp vector. The
permutation field ensures no candidate is added or lost. -/
structure TimestampOrdering (n : ℕ) where
  order : (Fin n → ℝ) → (Fin n → ℝ)
  measurable_order : Measurable order
  monotone_order : ∀ times, Monotone (order times)
  permutes : ∀ times, ∃ permutation : Equiv.Perm (Fin n),
    order times = times ∘ permutation

/-- Region on which a particular index permutation orders the timestamp
values monotonically. -/
def monotonePermutationRegion (permutation : Equiv.Perm (Fin n)) :
    Set (Fin n → ℝ) :=
  {times | Monotone (times ∘ permutation)}

theorem measurableSet_monotonePermutationRegion
    (permutation : Equiv.Perm (Fin n)) :
    MeasurableSet (monotonePermutationRegion permutation) := by
  rw [show monotonePermutationRegion permutation =
      ⋂ i : Fin n, ⋂ j : Fin n,
        if i < j then
          {times : Fin n → ℝ | times (permutation i) ≤ times (permutation j)}
        else Set.univ by
    ext times
    simp only [monotonePermutationRegion, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · rw [monotone_iff_forall_lt]
      intro h i j
      split_ifs with hij
      · exact h hij
      · exact Set.mem_univ times
    · intro h i j hij
      rcases eq_or_lt_of_le hij with rfl | hijlt
      · exact le_rfl
      · have hij' := h i j
        rw [if_pos hijlt] at hij'
        simpa [Function.comp_apply] using hij']
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  split
  · exact measurableSet_le (measurable_pi_apply (permutation i))
      (measurable_pi_apply (permutation j))
  · exact MeasurableSet.univ

/-- Sorting the values of a finite real tuple is measurable. The proof glues
the finitely many coordinate permutations over their measurable monotonicity
regions; `Tuple.unique_monotone` proves agreement on overlaps. -/
theorem measurable_tupleSortValues (n : ℕ) :
    Measurable (fun times : Fin n → ℝ => times ∘ Tuple.sort times) := by
  let region : Equiv.Perm (Fin n) → Set (Fin n → ℝ) :=
    monotonePermutationRegion
  let permute : Equiv.Perm (Fin n) → (Fin n → ℝ) → (Fin n → ℝ) :=
    fun permutation times => times ∘ permutation
  have hregion : ∀ permutation, MeasurableSet (region permutation) :=
    measurableSet_monotonePermutationRegion
  have hpermute : ∀ permutation, Measurable (permute permutation) := by
    intro permutation
    apply measurable_pi_lambda
    intro i
    exact measurable_pi_apply (permutation i)
  have hagree : Pairwise fun first second =>
      Set.EqOn (permute first) (permute second)
        (region first ∩ region second) := by
    intro first second _ times htimes
    exact Tuple.unique_monotone htimes.1 htimes.2
  obtain ⟨ordered, hordered, hagrees⟩ :=
    exists_measurable_piecewise region hregion permute hpermute hagree
  have heq : ordered = fun times : Fin n → ℝ =>
      times ∘ Tuple.sort times := by
    funext times
    exact hagrees (Tuple.sort times)
      (show times ∈ region (Tuple.sort times) from Tuple.monotone_sort times)
  rwa [← heq]

/-- Sorting erases a permutation of the labeled coordinates of a finite
product measure. -/
theorem map_tupleSortValues_pi_comp_perm
    (μ : Fin n → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (permutation : Equiv.Perm (Fin n)) :
    Measure.map (fun values : Fin n → ℝ => values ∘ Tuple.sort values)
        (Measure.pi fun i => μ (permutation i)) =
      Measure.map (fun values : Fin n → ℝ => values ∘ Tuple.sort values)
        (Measure.pi μ) := by
  rw [← Measure.pi_map_piCongrLeft permutation μ]
  rw [Measure.map_map
    (measurable_tupleSortValues n)
    (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) permutation).measurable]
  apply congrArg (fun map : (Fin n → ℝ) → (Fin n → ℝ) =>
    Measure.map map (Measure.pi fun i => μ (permutation i)))
  funext values
  have hcoordinate :
      MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) permutation values =
        values ∘ permutation.symm := by
    funext i
    simpa using
      (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝ)
        permutation values
        (permutation.symm i))
  rw [Function.comp_apply, hcoordinate]
  exact (Tuple.comp_perm_comp_sort_eq_comp_sort
    (f := values) (σ := permutation.symm)).symm

/-- After sorting, a two-measure product selected by a Boolean assignment
depends only on the number of coordinates selecting each measure. -/
theorem map_tupleSortValues_pi_boolAssignment_eq_of_count_eq
    (μ ν : Measure ℝ) [SigmaFinite μ] [SigmaFinite ν]
    {first second : Fin n → Bool}
    (hcount : boolAssignmentCount first = boolAssignmentCount second) :
    Measure.map (fun values : Fin n → ℝ => values ∘ Tuple.sort values)
        (Measure.pi fun i => if first i then μ else ν) =
      Measure.map (fun values : Fin n → ℝ => values ∘ Tuple.sort values)
        (Measure.pi fun i => if second i then μ else ν) := by
  obtain ⟨permutation, hpermutation⟩ :=
    exists_perm_boolAssignment_comp_eq hcount
  let family : Fin n → Measure ℝ := fun i => if first i then μ else ν
  letI : ∀ i, SigmaFinite (family i) := by
    intro i
    simp only [family]
    split <;> infer_instance
  have hfamily : (fun i => if second i then μ else ν) =
      fun i => family (permutation i) := by
    funext i
    have hi := congrFun hpermutation i
    simp only [Function.comp_apply] at hi
    simp only [family, ← hi]
  rw [hfamily]
  exact (map_tupleSortValues_pi_comp_perm family permutation).symm

/-- Consequently an entire fixed-count assignment fiber collapses to its
binomial multiplicity times any representative's sorted product law. -/
theorem sum_map_tupleSortValues_pi_boolAssignment_count_eq
    (μ ν : Measure ℝ) [SigmaFinite μ] [SigmaFinite ν]
    (representative : Fin n → Bool) (k : ℕ)
    (hrepresentative : boolAssignmentCount representative = k) :
    (∑ assignment ∈ Finset.univ.filter
        (fun assignment : Fin n → Bool => boolAssignmentCount assignment = k),
      Measure.map (fun values : Fin n → ℝ => values ∘ Tuple.sort values)
        (Measure.pi fun i => if assignment i then μ else ν)) =
      Nat.choose n k •
        Measure.map (fun values : Fin n → ℝ => values ∘ Tuple.sort values)
          (Measure.pi fun i => if representative i then μ else ν) := by
  calc
    _ = ∑ _assignment ∈ Finset.univ.filter
          (fun assignment : Fin n → Bool =>
            boolAssignmentCount assignment = k),
        Measure.map (fun values : Fin n → ℝ =>
          values ∘ Tuple.sort values)
          (Measure.pi fun i => if representative i then μ else ν) := by
      apply Finset.sum_congr rfl
      intro assignment hassignment
      exact map_tupleSortValues_pi_boolAssignment_eq_of_count_eq μ ν
        ((Finset.mem_filter.mp hassignment).2.trans hrepresentative.symm)
    _ = Nat.choose n k •
        Measure.map (fun values : Fin n → ℝ => values ∘ Tuple.sort values)
          (Measure.pi fun i => if representative i then μ else ν) := by
      rw [Finset.sum_const, card_boolAssignments_count_eq]

/-- Canonical assignment with the first `k` labeled coordinates in the first
interval. Values of `k` above `n` simply select every coordinate. -/
def canonicalBoolAssignment (n k : ℕ) : Fin n → Bool :=
  fun i => decide (i.val < k)

theorem boolAssignmentCount_canonicalBoolAssignment_of_le
    {n k : ℕ} (hk : k ≤ n) :
    boolAssignmentCount (canonicalBoolAssignment n k) = k := by
  unfold boolAssignmentCount canonicalBoolAssignment
  rw [show Finset.univ.filter (fun i : Fin n => decide (i.val < k)) =
      Finset.univ.filter (fun i : Fin n => i.val < k) by
    ext i
    simp]
  calc
    _ = (Finset.range k).card := by
      apply Finset.card_bij
        (fun i _ => i.val)
      · intro i hi
        rw [Finset.mem_range]
        exact (Finset.mem_filter.mp hi).2
      · intro first hfirst second hsecond heq
        exact Fin.ext heq
      · intro value hvalue
        have hvaluek : value < k := Finset.mem_range.mp hvalue
        have hvaluen : value < n := lt_of_lt_of_le hvaluek hk
        refine ⟨⟨value, hvaluen⟩, ?_, rfl⟩
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hvaluek⟩
    _ = k := Finset.card_range k

/-- The sorted law of any assignment is its count's canonical sorted law. -/
theorem map_tupleSortValues_pi_boolAssignment_eq_canonical
    (μ ν : Measure ℝ) [SigmaFinite μ] [SigmaFinite ν]
    (assignment : Fin n → Bool) :
    Measure.map (fun values : Fin n → ℝ => values ∘ Tuple.sort values)
        (Measure.pi fun i => if assignment i then μ else ν) =
      Measure.map (fun values : Fin n → ℝ => values ∘ Tuple.sort values)
        (Measure.pi fun i =>
          if canonicalBoolAssignment n (boolAssignmentCount assignment) i
          then μ else ν) := by
  apply map_tupleSortValues_pi_boolAssignment_eq_of_count_eq μ ν
  symm
  apply boolAssignmentCount_canonicalBoolAssignment_of_le
  exact Nat.le_of_lt_succ (boolAssignmentCount_lt_succ assignment)

/-- Sorted `n`-fold timestamp mass on a sum of two measures is the exact
binomial mixture of the canonical `k`/`n-k` coordinate blocks. -/
theorem map_tupleSortValues_pi_add_eq_sum_count
    (μ ν : Measure ℝ) [SigmaFinite μ] [SigmaFinite ν] (n : ℕ) :
    Measure.map (fun values : Fin n → ℝ => values ∘ Tuple.sort values)
        (Measure.pi fun _ : Fin n => μ + ν) =
      ∑ k ∈ Finset.range (n + 1), Nat.choose n k •
        Measure.map (fun values : Fin n → ℝ => values ∘ Tuple.sort values)
          (Measure.pi fun i =>
            if canonicalBoolAssignment n k i then μ else ν) := by
  rw [pi_add_eq_sum_bool]
  rw [Measure.map_sum (measurable_tupleSortValues n).aemeasurable]
  rw [measureSum_fintype]
  rw [sum_boolAssignments_by_count]
  apply Finset.sum_congr rfl
  intro k hk
  exact sum_map_tupleSortValues_pi_boolAssignment_count_eq μ ν
    (canonicalBoolAssignment n k) k
      (boolAssignmentCount_canonicalBoolAssignment_of_le
        (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))

/-- Adjacent-horizon timestamp mass, after chronological sorting, decomposes
by the exact number of events falling in the first interval. -/
theorem PositiveHorizon.map_tupleSortValues_pi_timestampMassMeasure_add
    (first second : PositiveHorizon) (n : ℕ) :
    Measure.map (fun values : Fin n → ℝ => values ∘ Tuple.sort values)
        (Measure.pi fun _ : Fin n =>
          (first.add second).timestampMassMeasure) =
      ∑ k ∈ Finset.range (n + 1), Nat.choose n k •
        Measure.map (fun values : Fin n → ℝ => values ∘ Tuple.sort values)
          (Measure.pi fun i =>
            if canonicalBoolAssignment n k i then
              first.timestampMassMeasure
            else Measure.map
              (fun time : ℝ => (first.duration : ℝ) + time)
              second.timestampMassMeasure) := by
  rw [first.timestampMassMeasure_add second]
  exact map_tupleSortValues_pi_add_eq_sum_count
    first.timestampMassMeasure
    (Measure.map (fun time : ℝ => (first.duration : ℝ) + time)
      second.timestampMassMeasure) n

/-- Concatenating an independent `k`-tuple from `μ` and `m`-tuple from `ν`
produces the canonical unsorted `(k+m)`-coordinate product law. -/
theorem map_prod_pi_pi_finAppend (μ ν : Measure ℝ)
    [SigmaFinite μ] [SigmaFinite ν] (k m : ℕ) :
    Measure.map (fun pair : (Fin k → ℝ) × (Fin m → ℝ) =>
        Fin.append pair.1 pair.2)
        ((Measure.pi fun _ : Fin k => μ).prod
          (Measure.pi fun _ : Fin m => ν)) =
      Measure.pi fun i : Fin (k + m) =>
        if canonicalBoolAssignment (k + m) k i then μ else ν := by
  letI : ∀ i : Fin (k + m),
      SigmaFinite (if canonicalBoolAssignment (k + m) k i then μ else ν) := by
    intro i
    split <;> infer_instance
  have happend : Measurable
      (fun pair : (Fin k → ℝ) × (Fin m → ℝ) =>
        Fin.append pair.1 pair.2) := by
    apply measurable_pi_lambda
    intro i
    refine Fin.addCases (motive := fun i =>
      Measurable (fun pair : (Fin k → ℝ) × (Fin m → ℝ) =>
        Fin.append pair.1 pair.2 i)) ?_ ?_ i
    · intro left
      simp only [Fin.append_left]
      fun_prop
    · intro right
      simp only [Fin.append_right]
      fun_prop
  symm
  apply Measure.pi_eq
  intro sets hsets
  rw [Measure.map_apply happend (MeasurableSet.univ_pi hsets)]
  rw [show (fun pair : (Fin k → ℝ) × (Fin m → ℝ) =>
      Fin.append pair.1 pair.2) ⁻¹' Set.univ.pi sets =
      (Set.univ.pi fun i : Fin k => sets (Fin.castAdd m i)) ×ˢ
        (Set.univ.pi fun i : Fin m => sets (Fin.natAdd k i)) by
    ext pair
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const,
      Set.mem_prod]
    constructor
    · intro h
      constructor
      · intro i
        simpa only [Fin.append_left] using h (Fin.castAdd m i)
      · intro i
        simpa only [Fin.append_right] using h (Fin.natAdd k i)
    · rintro ⟨hleft, hright⟩ i
      refine Fin.addCases (motive := fun i => Fin.append pair.1 pair.2 i ∈ sets i)
        ?_ ?_ i
      · intro left
        simpa only [Fin.append_left] using hleft left
      · intro right
        simpa only [Fin.append_right] using hright right]
  rw [Measure.prod_prod, Measure.pi_pi, Measure.pi_pi]
  rw [Fin.prod_univ_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    simp [canonicalBoolAssignment]
  · apply Finset.prod_congr rfl
    intro i hi
    simp [canonicalBoolAssignment]

/-- Certified measurable timestamp ordering at every finite count. -/
noncomputable def timestampOrdering (n : ℕ) : TimestampOrdering n where
  order := fun times => times ∘ Tuple.sort times
  measurable_order := measurable_tupleSortValues n
  monotone_order := Tuple.monotone_sort
  permutes := fun times => ⟨Tuple.sort times, rfl⟩

/-- Conditional law of ordered candidate timestamps obtained by pushing iid
uniform times through a certified measurable ordering. -/
noncomputable def PositiveHorizon.orderedCandidateTimesMeasure
    (horizon : PositiveHorizon) (ordering : TimestampOrdering n) :
    Measure (Fin n → ℝ) :=
  Measure.map ordering.order (horizon.candidateTimesMeasure n)

instance PositiveHorizon.orderedCandidateTimesMeasure.instIsProbabilityMeasure
    (horizon : PositiveHorizon) (ordering : TimestampOrdering n) :
    IsProbabilityMeasure
      (horizon.orderedCandidateTimesMeasure ordering) := by
  unfold PositiveHorizon.orderedCandidateTimesMeasure
  exact Measure.isProbabilityMeasure_map ordering.measurable_order.aemeasurable

/-- Sorting network for two timestamps. -/
def orderTwoTimestamps (times : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then min (times 0) (times 1)
    else max (times 0) (times 1)

/-- The two-input `min/max` sorting network is a certified measurable
timestamp ordering. -/
noncomputable def timestampOrderingTwo : TimestampOrdering 2 where
  order := orderTwoTimestamps
  measurable_order := by
    apply measurable_pi_lambda
    intro i
    unfold orderTwoTimestamps
    split_ifs
    · exact (measurable_pi_apply 0).min (measurable_pi_apply 1)
    · exact (measurable_pi_apply 0).max (measurable_pi_apply 1)
  monotone_order := by
    intro times i j hij
    fin_cases i <;> fin_cases j
    · exact le_rfl
    · simp [orderTwoTimestamps]
    · simp at hij
    · exact le_rfl
  permutes := by
    intro times
    by_cases h : times 0 ≤ times 1
    · refine ⟨Equiv.refl _, ?_⟩
      funext i
      fin_cases i <;> simp [orderTwoTimestamps, h]
    · refine ⟨Equiv.swap 0 1, ?_⟩
      funext i
      fin_cases i <;> simp [orderTwoTimestamps, le_of_not_ge h]

/-- Convert ordered absolute timestamps to inter-candidate waits. The first
wait is measured from time zero. `toNNReal` makes this a total measurable map;
on timestamps in `(0,T]` with monotone order it agrees with ordinary
nonnegative subtraction. -/
def orderedTimestampsToWaits (times : Fin n → ℝ) : Fin n → NNReal :=
  fun i => if _hzero : i.val = 0 then Real.toNNReal (times i)
    else
      let previous : Fin n := ⟨i.val - 1,
        lt_of_le_of_lt (Nat.sub_le i.val 1) i.isLt⟩
      Real.toNNReal (times i - times previous)

@[simp] theorem orderedTimestampsToWaits_zero
    (times : Fin (n + 1) → ℝ) :
    orderedTimestampsToWaits times 0 = Real.toNNReal (times 0) := by
  simp [orderedTimestampsToWaits]

@[simp] theorem orderedTimestampsToWaits_succ
    (times : Fin (n + 1) → ℝ) (i : Fin n) :
    orderedTimestampsToWaits times i.succ =
      Real.toNNReal (times i.succ - times i.castSucc) := by
  simp only [orderedTimestampsToWaits]
  rw [dif_neg (by simp)]
  congr 2

/-- Sorting two unequal timestamps produces a strictly positive second
inter-event wait. -/
theorem orderedTimestampsToWaits_timestampOrdering_two_one_pos
    (times : Fin 2 → ℝ) (hne : times 0 ≠ times 1) :
    0 < orderedTimestampsToWaits ((timestampOrdering 2).order times) 1 := by
  obtain ⟨permutation, hpermutation⟩ :=
    (timestampOrdering 2).permutes times
  have htimes : Function.Injective times := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have horderedNe :
      (timestampOrdering 2).order times 0 ≠
        (timestampOrdering 2).order times 1 := by
    rw [hpermutation]
    intro heq
    exact (by decide : (0 : Fin 2) ≠ 1)
      (permutation.injective (htimes heq))
  have horderedLe := (timestampOrdering 2).monotone_order times
    (show (0 : Fin 2) ≤ 1 by decide)
  change 0 < orderedTimestampsToWaits
    ((timestampOrdering 2).order times) (Fin.succ 0)
  rw [orderedTimestampsToWaits_succ]
  exact Real.toNNReal_pos.mpr (sub_pos.mpr (lt_of_le_of_ne horderedLe horderedNe))

/-- Translating every absolute timestamp only adds the translation to the
first wait; all subsequent inter-event waits are unchanged. -/
theorem orderedTimestampsToWaits_const_add
    (shift : NNReal) (times : Fin n → ℝ)
    (hfirst : ∀ i : Fin n, 0 ≤ times i) :
    orderedTimestampsToWaits
        (fun i => (shift : ℝ) + times i) =
      fun i => if i.val = 0 then shift + orderedTimestampsToWaits times i
        else orderedTimestampsToWaits times i := by
  cases n with
  | zero => funext i; exact Fin.elim0 i
  | succ n =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · apply NNReal.eq
        simp [Real.toNNReal_of_nonneg (hfirst 0),
          Real.toNNReal_of_nonneg
            (add_nonneg (NNReal.coe_nonneg shift) (hfirst 0))]
      · rw [if_neg (by simp)]
        simp only [orderedTimestampsToWaits_succ]
        apply congrArg Real.toNNReal
        ring

theorem measurable_orderedTimestampsToWaits (n : ℕ) :
    Measurable (orderedTimestampsToWaits (n := n)) := by
  apply measurable_pi_lambda
  intro i
  by_cases hzero : i.val = 0
  · simp only [orderedTimestampsToWaits, dif_pos hzero]
    fun_prop
  · simp only [orderedTimestampsToWaits, dif_neg hzero]
    fun_prop

/-- Under the sorted two-candidate timestamp law, the flight between the two
refreshes is positive almost surely. -/
theorem PositiveHorizon.ae_orderedCandidateTimesMeasure_two_middleWait_pos
    (horizon : PositiveHorizon) :
    ∀ᵐ times ∂horizon.orderedCandidateTimesMeasure (timestampOrdering 2),
      0 < orderedTimestampsToWaits times 1 := by
  unfold PositiveHorizon.orderedCandidateTimesMeasure
  have hmeas : MeasurableSet
      {times : Fin 2 → ℝ | 0 < orderedTimestampsToWaits times 1} :=
    measurableSet_lt measurable_const
      ((measurable_pi_apply 1).comp (measurable_orderedTimestampsToWaits 2))
  apply (ae_map_iff (timestampOrdering 2).measurable_order.aemeasurable
    hmeas).2
  filter_upwards [horizon.ae_candidateTimesMeasure_two_ne] with times hne
  exact orderedTimestampsToWaits_timestampOrdering_two_one_pos times hne

/-- Inter-candidate waits telescope back to the last absolute timestamp for a
nonnegative monotone timestamp vector. -/
theorem sum_orderedTimestampsToWaits
    (times : Fin (n + 1) → ℝ) (hmono : Monotone times)
    (hzero : 0 ≤ times 0) :
    ((∑ i, orderedTimestampsToWaits times i : NNReal) : ℝ) =
      times (Fin.last n) := by
  let f : ℕ → ℝ := fun k => times ⟨min k n,
    lt_of_le_of_lt (Nat.min_le_right k n) (Nat.lt_succ_self n)⟩
  let g : ℕ → ℝ := fun k =>
    if hk : k < n + 1 then
      (orderedTimestampsToWaits times ⟨k, hk⟩ : ℝ)
    else 0
  rw [NNReal.coe_sum]
  calc
    ∑ i, (orderedTimestampsToWaits times i : ℝ) = ∑ i : Fin (n + 1), g i := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp [g]
      split_ifs with h
      · rfl
      · exact (h i.isLt).elim
    _ = ∑ k ∈ Finset.range (n + 1), g k :=
      Fin.sum_univ_eq_sum_range g (n + 1)
    _ =
        ∑ k ∈ Finset.range (n + 1),
          if k = 0 then f 0 else f k - f (k - 1) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hklt : k < n + 1 := Finset.mem_range.mp hk
      have hkle : k ≤ n := Nat.lt_succ_iff.mp hklt
      have hg : g k =
          (orderedTimestampsToWaits times ⟨k, hklt⟩ : ℝ) := by
        dsimp [g]
        split_ifs
        rfl
      have hf : f k = times ⟨k, hklt⟩ := by
        simp [f, Nat.min_eq_left hkle]
      by_cases hk0 : k = 0
      · subst k
        simp [hg, orderedTimestampsToWaits, f, hzero]
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        have hprevlt : k - 1 < n + 1 :=
          lt_of_le_of_lt (Nat.sub_le k 1) hklt
        have hprevle : k - 1 ≤ n := Nat.lt_succ_iff.mp hprevlt
        have hfprev : f (k - 1) = times ⟨k - 1, hprevlt⟩ := by
          simp [f, Nat.min_eq_left hprevle]
        have hle : times ⟨k - 1, hprevlt⟩ ≤ times ⟨k, hklt⟩ := by
          apply hmono
          exact Fin.mk_le_mk.mpr (Nat.sub_le k 1)
        rw [hg]
        simp [orderedTimestampsToWaits, hk0, hf, hfprev,
          Real.toNNReal_of_nonneg (sub_nonneg.mpr hle)]
    _ = f n := (Finset.eq_sum_range_sub' f n).symm
    _ = times (Fin.last n) := by
      apply congrArg times
      apply Fin.ext
      simp

/-- Ordered timestamps contained in a horizon produce waits whose total does
not exceed that horizon. -/
theorem sum_orderedTimestampsToWaits_le
    (times : Fin n → ℝ) (hmono : Monotone times) (horizon : NNReal)
    (hinside : ∀ i, times i ∈ Set.Ioc 0 (horizon : ℝ)) :
    (∑ i, orderedTimestampsToWaits times i) ≤ horizon := by
  cases n with
  | zero => simp
  | succ n =>
      rw [← NNReal.coe_le_coe]
      rw [sum_orderedTimestampsToWaits times hmono
        (le_of_lt (hinside 0).1)]
      exact (hinside (Fin.last n)).2

/-- Conditional law of inter-candidate waits induced by a certified timestamp
ordering. -/
noncomputable def PositiveHorizon.candidateWaitsMeasure
    (horizon : PositiveHorizon) (ordering : TimestampOrdering n) :
    Measure (Fin n → NNReal) :=
  Measure.map orderedTimestampsToWaits
    (horizon.orderedCandidateTimesMeasure ordering)

instance PositiveHorizon.candidateWaitsMeasure.instIsProbabilityMeasure
    (horizon : PositiveHorizon) (ordering : TimestampOrdering n) :
    IsProbabilityMeasure (horizon.candidateWaitsMeasure ordering) := by
  unfold PositiveHorizon.candidateWaitsMeasure
  exact Measure.isProbabilityMeasure_map
    (measurable_orderedTimestampsToWaits n).aemeasurable

/-- The middle wait in the canonical two-candidate wait law is positive
almost surely. -/
theorem PositiveHorizon.ae_candidateWaitsMeasure_two_middle_pos
    (horizon : PositiveHorizon) :
    ∀ᵐ waits ∂horizon.candidateWaitsMeasure (timestampOrdering 2),
      0 < waits 1 := by
  unfold PositiveHorizon.candidateWaitsMeasure
  apply (ae_map_iff (measurable_orderedTimestampsToWaits 2).aemeasurable
    (measurableSet_lt measurable_const (measurable_pi_apply 1))).2
  exact horizon.ae_orderedCandidateTimesMeasure_two_middleWait_pos

/-- Under every certified ordering, the conditional wait vector has total
elapsed time at most the horizon almost surely. -/
theorem PositiveHorizon.ae_candidateWaitsMeasure_sum_le
    (horizon : PositiveHorizon) (ordering : TimestampOrdering n) :
    ∀ᵐ waits ∂horizon.candidateWaitsMeasure ordering,
      (∑ i, waits i) ≤ horizon.duration := by
  have hsum : Measurable (fun waits : Fin n → NNReal => ∑ i, waits i) := by
    fun_prop
  have hsumOrdered : Measurable (fun times : Fin n → ℝ =>
      ∑ i, orderedTimestampsToWaits times i) :=
    hsum.comp (measurable_orderedTimestampsToWaits n)
  unfold PositiveHorizon.candidateWaitsMeasure
    PositiveHorizon.orderedCandidateTimesMeasure
  rw [ae_map_iff (measurable_orderedTimestampsToWaits n).aemeasurable
    (measurableSet_le hsum measurable_const)]
  rw [ae_map_iff ordering.measurable_order.aemeasurable
    (measurableSet_le hsumOrdered measurable_const)]
  filter_upwards [horizon.ae_candidateTimesMeasure_mem n] with times htimes
  apply sum_orderedTimestampsToWaits_le
  · exact ordering.monotone_order times
  · intro i
    obtain ⟨permutation, hpermutation⟩ := ordering.permutes times
    rw [hpermutation]
    exact htimes (permutation i)

/-- Common measurable carrier for schedules of every finite size. Coordinates
past `candidateCount` are padding and carry no semantic events. -/
abbrev CandidateScheduleSample := ℕ × (ℕ → NNReal)

/-- Embed a fixed-size wait vector into the common schedule carrier. -/
def padCandidateWaits (n : ℕ) (waits : Fin n → NNReal) :
    CandidateScheduleSample :=
  (n, fun k => if h : k < n then waits ⟨k, h⟩ else 0)

/-- Padding does not change the elapsed time represented by the active wait
coordinates. -/
theorem scheduleElapsed_padCandidateWaits (n : ℕ) (waits : Fin n → NNReal) :
    (∑ index ∈ Finset.range n, (padCandidateWaits n waits).2 index) =
      ∑ index, waits index := by
  let g : ℕ → NNReal := fun index =>
    if h : index < n then waits ⟨index, h⟩ else 0
  calc
    (∑ index ∈ Finset.range n, (padCandidateWaits n waits).2 index) =
        ∑ index ∈ Finset.range n, g index := by rfl
    _ = ∑ index : Fin n, g index :=
      (Fin.sum_univ_eq_sum_range g n).symm
    _ = ∑ index, waits index := by
      apply Finset.sum_congr rfl
      intro index _
      dsimp [g]
      split_ifs with h
      · rfl
      · exact (h index.isLt).elim

theorem measurable_padCandidateWaits (n : ℕ) :
    Measurable (padCandidateWaits n) := by
  apply measurable_const.prodMk
  apply measurable_pi_lambda
  intro k
  change Measurable (fun waits : Fin n → NNReal =>
    if h : k < n then waits ⟨k, h⟩ else 0)
  by_cases h : k < n
  · simp only [h, dite_true]
    exact measurable_pi_apply (⟨k, h⟩ : Fin n)
  · simp only [h, dite_false]
    exact measurable_const

/-- Convert an already chronological timestamp vector to the common padded
wait schedule. -/
def orderedTimestampsToSchedule (n : ℕ) (times : Fin n → ℝ) :
    CandidateScheduleSample :=
  padCandidateWaits n (orderedTimestampsToWaits times)

theorem measurable_orderedTimestampsToSchedule (n : ℕ) :
    Measurable (orderedTimestampsToSchedule n) :=
  (measurable_padCandidateWaits n).comp
    (measurable_orderedTimestampsToWaits n)

/-- Complete measurable conversion from labeled absolute timestamps to the
common padded chronological-wait schedule. -/
noncomputable def timestampsToSchedule (n : ℕ) (times : Fin n → ℝ) :
    CandidateScheduleSample :=
  orderedTimestampsToSchedule n (times ∘ Tuple.sort times)

theorem measurable_timestampsToSchedule (n : ℕ) :
    Measurable (timestampsToSchedule n) :=
  (measurable_orderedTimestampsToSchedule n).comp
    (measurable_tupleSortValues n)

/-- Conditional schedule law on the common carrier at a fixed count. -/
noncomputable def PositiveHorizon.fixedScheduleMeasure
    (horizon : PositiveHorizon) (ordering : TimestampOrdering n) :
    Measure CandidateScheduleSample :=
  Measure.map (padCandidateWaits n)
    (horizon.candidateWaitsMeasure ordering)

/-- For the canonical tuple sorting, the fixed-count schedule is a single
pushforward of the iid unordered timestamp law. -/
theorem PositiveHorizon.fixedScheduleMeasure_timestampOrdering
    (horizon : PositiveHorizon) (n : ℕ) :
    horizon.fixedScheduleMeasure (timestampOrdering n) =
      Measure.map (timestampsToSchedule n)
        (horizon.candidateTimesMeasure n) := by
  unfold PositiveHorizon.fixedScheduleMeasure
    PositiveHorizon.candidateWaitsMeasure
    PositiveHorizon.orderedCandidateTimesMeasure timestampsToSchedule
    timestampOrdering
  rw [Measure.map_map (measurable_orderedTimestampsToWaits n)
      (measurable_tupleSortValues n),
    Measure.map_map (measurable_padCandidateWaits n)
      ((measurable_orderedTimestampsToWaits n).comp
        (measurable_tupleSortValues n))]
  rfl

/-- Unnormalized chronological schedule mass obtained from Lebesgue timestamp
mass rather than normalized uniform timestamps. -/
noncomputable def PositiveHorizon.timestampScheduleMass
    (horizon : PositiveHorizon) (n : ℕ) :
    Measure CandidateScheduleSample :=
  Measure.map (timestampsToSchedule n)
    (Measure.pi fun _ : Fin n => horizon.timestampMassMeasure)

instance PositiveHorizon.timestampScheduleMass.instIsFiniteMeasure
    (horizon : PositiveHorizon) (n : ℕ) :
    IsFiniteMeasure (horizon.timestampScheduleMass n) := by
  unfold PositiveHorizon.timestampScheduleMass
  infer_instance

/-- Every point in a fixed-count unnormalized schedule stratum stores that
count in its first coordinate. -/
theorem PositiveHorizon.ae_timestampScheduleMass_fst
    (horizon : PositiveHorizon) (n : ℕ) :
    ∀ᵐ schedule ∂horizon.timestampScheduleMass n, schedule.1 = n := by
  unfold PositiveHorizon.timestampScheduleMass
  rw [ae_map_iff (measurable_timestampsToSchedule n).aemeasurable
    (measurableSet_eq_fun measurable_fst measurable_const)]
  exact Filter.Eventually.of_forall fun times => by
    simp [timestampsToSchedule, orderedTimestampsToSchedule,
      padCandidateWaits]

/-- The unnormalized schedule mass is the normalized fixed-count schedule law
scaled by the `n`th power of the horizon length. -/
theorem PositiveHorizon.timestampScheduleMass_eq_smul_fixedScheduleMeasure
    (horizon : PositiveHorizon) (n : ℕ) :
    horizon.timestampScheduleMass n =
      ENNReal.ofReal (horizon.duration : ℝ) ^ n •
        horizon.fixedScheduleMeasure (timestampOrdering n) := by
  letI : SigmaFinite (ENNReal.ofReal (horizon.duration : ℝ) •
      horizon.uniformTimeMeasure) := by
    rw [horizon.ofReal_duration_smul_uniformTimeMeasure]
    infer_instance
  rw [horizon.fixedScheduleMeasure_timestampOrdering]
  unfold PositiveHorizon.timestampScheduleMass
    PositiveHorizon.candidateTimesMeasure
  rw [← Measure.map_smul]
  rw [← pi_const_smul
    (ENNReal.ofReal (horizon.duration : ℝ)) horizon.uniformTimeMeasure n]
  congr 2
  funext i
  exact horizon.ofReal_duration_smul_uniformTimeMeasure.symm

/-- Unnormalized adjacent-horizon schedule mass decomposes by the exact
number of events in the first interval, retaining canonical absolute-time
coordinate blocks. -/
theorem PositiveHorizon.timestampScheduleMass_add_eq_sum_count
    (first second : PositiveHorizon) (n : ℕ) :
    (first.add second).timestampScheduleMass n =
      ∑ k ∈ Finset.range (n + 1), Nat.choose n k •
        Measure.map (timestampsToSchedule n)
          (Measure.pi fun i =>
            if canonicalBoolAssignment n k i then
              first.timestampMassMeasure
            else Measure.map
              (fun time : ℝ => (first.duration : ℝ) + time)
              second.timestampMassMeasure) := by
  unfold PositiveHorizon.timestampScheduleMass timestampsToSchedule
  rw [show Measure.map
        (fun times : Fin n → ℝ =>
          orderedTimestampsToSchedule n (times ∘ Tuple.sort times))
        (Measure.pi fun _ : Fin n =>
          (first.add second).timestampMassMeasure) =
      Measure.map (orderedTimestampsToSchedule n)
        (Measure.map
          (fun times : Fin n → ℝ => times ∘ Tuple.sort times)
          (Measure.pi fun _ : Fin n =>
            (first.add second).timestampMassMeasure)) by
      rw [Measure.map_map (measurable_orderedTimestampsToSchedule n)
        (measurable_tupleSortValues n)]
      rfl]
  rw [first.map_tupleSortValues_pi_timestampMassMeasure_add second n]
  rw [map_finset_sum _ (measurable_orderedTimestampsToSchedule n)]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [← Measure.mapₗ_apply_of_measurable
    (measurable_orderedTimestampsToSchedule n), map_nsmul]
  rw [Measure.mapₗ_apply_of_measurable
    (measurable_orderedTimestampsToSchedule n)]
  rw [Measure.map_map (measurable_orderedTimestampsToSchedule n)
    (measurable_tupleSortValues n)]
  rfl

/-- Janossy coefficient for `n` homogeneous Poisson events when timestamp
coordinates use unnormalized Lebesgue mass. -/
noncomputable def poissonScheduleMassWeight
    (refreshRate : NNReal) (horizon : PositiveHorizon) (n : ℕ) : ENNReal :=
  ENNReal.ofReal
    (Real.exp (-(refreshRate : ℝ) * (horizon.duration : ℝ)) *
      (refreshRate : ℝ) ^ n / (n.factorial : ℝ))

/-- The Poisson singleton weight times the normalized fixed-count law equals
the Janossy coefficient times unnormalized timestamp schedule mass. -/
theorem poisson_smul_fixedSchedule_eq_massWeight_smul
    (refreshRate : NNReal) (horizon : PositiveHorizon) (n : ℕ) :
    poissonMeasure (refreshRate * horizon.duration) {n} •
        horizon.fixedScheduleMeasure (timestampOrdering n) =
      poissonScheduleMassWeight refreshRate horizon n •
        horizon.timestampScheduleMass n := by
  rw [horizon.timestampScheduleMass_eq_smul_fixedScheduleMeasure,
    smul_smul]
  congr 1
  rw [poissonMeasure_singleton]
  unfold poissonScheduleMassWeight
  rw [← ENNReal.ofReal_pow (NNReal.coe_nonneg horizon.duration)]
  rw [← ENNReal.ofReal_mul (by positivity :
    0 ≤ Real.exp (-(refreshRate : ℝ) * (horizon.duration : ℝ)) *
      (refreshRate : ℝ) ^ n / (n.factorial : ℝ))]
  apply congrArg ENNReal.ofReal
  push_cast
  rw [mul_pow]
  field_simp

/-- Janossy coefficients satisfy the exact adjacent-horizon binomial
factorization. -/
theorem poissonScheduleMassWeight_add_mul_choose
    (refreshRate : NNReal) (first second : PositiveHorizon) (k m : ℕ) :
    poissonScheduleMassWeight refreshRate (first.add second) (k + m) *
        (Nat.choose (k + m) k : ENNReal) =
      poissonScheduleMassWeight refreshRate first k *
        poissonScheduleMassWeight refreshRate second m := by
  unfold poissonScheduleMassWeight
  rw [← ENNReal.ofReal_natCast]
  rw [← ENNReal.ofReal_mul (by positivity :
    0 ≤ Real.exp (-(refreshRate : ℝ) *
      ((first.add second).duration : ℝ)) *
      (refreshRate : ℝ) ^ (k + m) /
        ((k + m).factorial : ℝ))]
  rw [← ENNReal.ofReal_mul (by positivity :
    0 ≤ Real.exp (-(refreshRate : ℝ) * (first.duration : ℝ)) *
      (refreshRate : ℝ) ^ k / (k.factorial : ℝ))]
  apply congrArg ENNReal.ofReal
  rw [PositiveHorizon.add_duration, NNReal.coe_add, mul_add,
    Real.exp_add, pow_add]
  have hfactorial := Nat.add_choose_mul_factorial_mul_factorial k m
  rw [← Nat.choose_symm_add] at hfactorial
  have hfactorialReal :
      ((Nat.choose (k + m) k : ℕ) : ℝ) * (k.factorial : ℝ) *
          (m.factorial : ℝ) = ((k + m).factorial : ℝ) := by
    exact_mod_cast hfactorial
  field_simp
  linear_combination
    ((refreshRate : ℝ) ^ k * (refreshRate : ℝ) ^ m) * hfactorialReal

instance PositiveHorizon.fixedScheduleMeasure.instIsProbabilityMeasure
    (horizon : PositiveHorizon) (ordering : TimestampOrdering n) :
    IsProbabilityMeasure (horizon.fixedScheduleMeasure ordering) := by
  unfold PositiveHorizon.fixedScheduleMeasure
  exact Measure.isProbabilityMeasure_map
    (measurable_padCandidateWaits n).aemeasurable

/-- A padded fixed-count schedule remains within its horizon almost surely. -/
theorem PositiveHorizon.ae_fixedScheduleMeasure_elapsed_le
    (horizon : PositiveHorizon) (ordering : TimestampOrdering n) :
    ∀ᵐ schedule ∂horizon.fixedScheduleMeasure ordering,
      (∑ index ∈ Finset.range n, schedule.2 index) ≤ horizon.duration := by
  have helapsed : Measurable (fun schedule : CandidateScheduleSample =>
      ∑ index ∈ Finset.range n, schedule.2 index) := by
    fun_prop
  unfold PositiveHorizon.fixedScheduleMeasure
  rw [ae_map_iff (measurable_padCandidateWaits n).aemeasurable
    (measurableSet_le helapsed measurable_const)]
  filter_upwards [horizon.ae_candidateWaitsMeasure_sum_le ordering] with waits hwaits
  rw [scheduleElapsed_padCandidateWaits]
  exact hwaits

/-- The padded schedule law records its fixed candidate count exactly. -/
theorem PositiveHorizon.ae_fixedScheduleMeasure_fst
    (horizon : PositiveHorizon) (ordering : TimestampOrdering n) :
    ∀ᵐ schedule ∂horizon.fixedScheduleMeasure ordering,
      schedule.1 = n := by
  unfold PositiveHorizon.fixedScheduleMeasure
  rw [ae_map_iff (measurable_padCandidateWaits n).aemeasurable
    (measurableSet_eq_fun (measurable_fst) measurable_const)]
  exact Filter.Eventually.of_forall fun _ => rfl

/-- The actual padded two-refresh schedule has a positive flight between its
two refreshes almost surely. -/
theorem PositiveHorizon.ae_fixedScheduleMeasure_two_middle_pos
    (horizon : PositiveHorizon) :
    ∀ᵐ schedule ∂horizon.fixedScheduleMeasure (timestampOrdering 2),
      0 < schedule.2 1 := by
  unfold PositiveHorizon.fixedScheduleMeasure
  apply (ae_map_iff (measurable_padCandidateWaits 2).aemeasurable
    (measurableSet_lt measurable_const
      ((measurable_pi_apply 1).comp measurable_snd))).2
  filter_upwards [horizon.ae_candidateWaitsMeasure_two_middle_pos] with waits hwait
  simpa [padCandidateWaits] using hwait

/-- Almost-sure positivity of the middle two-refresh flight can be made
quantitative on a schedule region of positive conditional probability: some
strictly positive deterministic gap is a lower bound throughout that region.
This is the timestamp compactness input needed for uniform Jacobian and
density floors. -/
theorem PositiveHorizon.exists_pos_fixedScheduleMeasure_two_middle_ge
    (horizon : PositiveHorizon) :
    ∃ gap : NNReal, 0 < gap ∧
      0 < horizon.fixedScheduleMeasure (timestampOrdering 2)
        {schedule | gap ≤ schedule.2 1} := by
  let gap : ℕ → NNReal := fun n =>
    ⟨1 / (n + 1 : ℝ), by positivity⟩
  let region : ℕ → Set CandidateScheduleSample := fun n =>
    {schedule | gap n ≤ schedule.2 1}
  have hregionMeasurable (n : ℕ) : MeasurableSet (region n) := by
    exact measurableSet_le measurable_const
      ((measurable_pi_apply 1).comp measurable_snd)
  have hcover : {schedule : CandidateScheduleSample | 0 < schedule.2 1} ⊆
      ⋃ n, region n := by
    intro schedule hschedule
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt
      (show 0 < (schedule.2 1 : ℝ) by exact_mod_cast hschedule)
    apply Set.mem_iUnion.2
    refine ⟨n, ?_⟩
    change gap n ≤ schedule.2 1
    rw [← NNReal.coe_le_coe]
    exact hn.le
  have hpositiveSet :
      0 < horizon.fixedScheduleMeasure (timestampOrdering 2)
        {schedule : CandidateScheduleSample | 0 < schedule.2 1} := by
    have hmeasure := (ae_mem_iff_measure_eq
      (measurableSet_lt measurable_const
        ((measurable_pi_apply 1).comp measurable_snd)).nullMeasurableSet).1
      horizon.ae_fixedScheduleMeasure_two_middle_pos
    have hmeasure' :
        horizon.fixedScheduleMeasure (timestampOrdering 2)
            {schedule : CandidateScheduleSample | 0 < schedule.2 1} =
          horizon.fixedScheduleMeasure (timestampOrdering 2) Set.univ := by
      simpa only [Function.comp_apply] using hmeasure
    rw [hmeasure', measure_univ]
    exact zero_lt_one
  have hunion : 0 < horizon.fixedScheduleMeasure (timestampOrdering 2)
      (⋃ n, region n) :=
    hpositiveSet.trans_le (measure_mono hcover)
  obtain ⟨n, hn⟩ := exists_measure_pos_of_not_measure_iUnion_null hunion.ne'
  refine ⟨gap n, ?_, ?_⟩
  · rw [← NNReal.coe_pos]
    dsimp [gap]
    exact div_pos one_pos (by positivity)
  · simpa only [region] using hn

/-- Valid padded two-refresh schedules whose middle flight has a prescribed
positive lower bound. -/
def PositiveHorizon.validTwoRefreshScheduleRegion
    (horizon : PositiveHorizon) (gap : NNReal) :
    Set CandidateScheduleSample :=
  {schedule | schedule.1 = 2 ∧
    (∑ index ∈ Finset.range 2, schedule.2 index) ≤ horizon.duration ∧
    gap ≤ schedule.2 1}

theorem PositiveHorizon.measurableSet_validTwoRefreshScheduleRegion
    (horizon : PositiveHorizon) (gap : NNReal) :
    MeasurableSet (horizon.validTwoRefreshScheduleRegion gap) := by
  unfold PositiveHorizon.validTwoRefreshScheduleRegion
  apply (measurableSet_eq_fun measurable_fst measurable_const).inter
  apply (measurableSet_le (by fun_prop) measurable_const).inter
  exact measurableSet_le measurable_const
    (measurable_coe_nnreal_real.comp
      ((measurable_pi_apply 1).comp measurable_snd))

/-- Finite-coordinate version of `validTwoRefreshScheduleRegion`, before
padding into the common schedule carrier. -/
def PositiveHorizon.validTwoRefreshWaitRegion
    (horizon : PositiveHorizon) (gap : NNReal) : Set (Fin 2 → NNReal) :=
  {waits | (∑ index, waits index) ≤ horizon.duration ∧ gap ≤ waits 1}

theorem PositiveHorizon.measurableSet_validTwoRefreshWaitRegion
    (horizon : PositiveHorizon) (gap : NNReal) :
    MeasurableSet (horizon.validTwoRefreshWaitRegion gap) := by
  unfold PositiveHorizon.validTwoRefreshWaitRegion
  exact (measurableSet_le (by fun_prop) measurable_const).inter
    (measurableSet_le measurable_const
      (measurable_coe_nnreal_real.comp (measurable_pi_apply 1)))

theorem PositiveHorizon.isCompact_validTwoRefreshWaitRegion
    (horizon : PositiveHorizon) (gap : NNReal) :
    IsCompact (horizon.validTwoRefreshWaitRegion gap) := by
  have hclosed : IsClosed (horizon.validTwoRefreshWaitRegion gap) := by
    unfold PositiveHorizon.validTwoRefreshWaitRegion
    exact (isClosed_le (by fun_prop) continuous_const).inter
      (isClosed_le continuous_const (by fun_prop))
  let box : Set (Fin 2 → NNReal) :=
    Set.univ.pi fun _ => Set.Icc 0 horizon.duration
  have hbox : IsCompact box := by
    exact isCompact_univ_pi fun _ => isCompact_Icc
  apply IsCompact.of_isClosed_subset hbox hclosed
  intro waits hwaits
  rw [Set.mem_pi]
  intro index _
  constructor
  · exact bot_le
  · fin_cases index
    · exact (show waits 0 ≤ waits 0 + waits 1 from self_le_add_right _ _)
        |>.trans (by simpa [Fin.sum_univ_two] using hwaits.1)
    · exact (show waits 1 ≤ waits 0 + waits 1 from self_le_add_left _ _)
        |>.trans (by simpa [Fin.sum_univ_two] using hwaits.1)

theorem PositiveHorizon.preimage_validTwoRefreshScheduleRegion_pad
    (horizon : PositiveHorizon) (gap : NNReal) :
    padCandidateWaits 2 ⁻¹' horizon.validTwoRefreshScheduleRegion gap =
      horizon.validTwoRefreshWaitRegion gap := by
  ext waits
  change ((padCandidateWaits 2 waits).1 = 2 ∧
      (∑ index ∈ Finset.range 2,
        (padCandidateWaits 2 waits).2 index) ≤ horizon.duration ∧
      gap ≤ (padCandidateWaits 2 waits).2 1) ↔
    (∑ index, waits index) ≤ horizon.duration ∧ gap ≤ waits 1
  rw [scheduleElapsed_padCandidateWaits]
  simp [padCandidateWaits, Fin.sum_univ_two]

/-- The quantitative middle-gap region may simultaneously be restricted to
the genuine count-two, within-horizon schedule carrier without losing any of
its positive mass. Hence both active waits and the residual flight are
uniformly bounded by the fixed horizon, while the middle flight stays away
from zero. -/
theorem PositiveHorizon.exists_pos_valid_twoRefreshScheduleRegion
    (horizon : PositiveHorizon) :
    ∃ gap : NNReal, 0 < gap ∧
      0 < horizon.fixedScheduleMeasure (timestampOrdering 2)
        (horizon.validTwoRefreshScheduleRegion gap) := by
  obtain ⟨gap, hgap, hgapMass⟩ :=
    horizon.exists_pos_fixedScheduleMeasure_two_middle_ge
  let valid : Set CandidateScheduleSample :=
    {schedule | schedule.1 = 2 ∧
      (∑ index ∈ Finset.range 2, schedule.2 index) ≤ horizon.duration}
  have hvalid : ∀ᵐ schedule
      ∂horizon.fixedScheduleMeasure (timestampOrdering 2),
      schedule ∈ valid := by
    filter_upwards
      [horizon.ae_fixedScheduleMeasure_fst (timestampOrdering 2),
        horizon.ae_fixedScheduleMeasure_elapsed_le (timestampOrdering 2)]
      with schedule hcount helapsed
    exact ⟨hcount, helapsed⟩
  have hmass : horizon.fixedScheduleMeasure (timestampOrdering 2)
      (valid ∩ {schedule : CandidateScheduleSample | gap ≤ schedule.2 1}) =
      horizon.fixedScheduleMeasure (timestampOrdering 2)
        {schedule | gap ≤ schedule.2 1} := by
    apply measure_congr
    filter_upwards [hvalid] with schedule hschedule
    apply propext
    constructor
    · intro h
      exact h.2
    · intro h
      exact ⟨hschedule, h⟩
  refine ⟨gap, hgap, ?_⟩
  rw [show horizon.validTwoRefreshScheduleRegion gap =
      {schedule : CandidateScheduleSample | schedule.1 = 2 ∧
        (∑ index ∈ Finset.range 2, schedule.2 index) ≤ horizon.duration ∧
        gap ≤ schedule.2 1} by rfl]
  rw [show {schedule : CandidateScheduleSample | schedule.1 = 2 ∧
        (∑ index ∈ Finset.range 2, schedule.2 index) ≤ horizon.duration ∧
        gap ≤ schedule.2 1} =
      valid ∩ {schedule | gap ≤ schedule.2 1} by
        ext schedule
        simp only [valid, Set.mem_setOf_eq, Set.mem_inter_iff]
        tauto]
  rw [hmass]
  exact hgapMass

/-- The positive-mass valid schedule region is equivalently a positive-mass
region of the two active wait coordinates. -/
theorem PositiveHorizon.exists_pos_candidateWaitsMeasure_two_compactRegion
    (horizon : PositiveHorizon) :
    ∃ gap : NNReal, 0 < gap ∧
      0 < horizon.candidateWaitsMeasure (timestampOrdering 2)
        (horizon.validTwoRefreshWaitRegion gap) := by
  obtain ⟨gap, hgap, hmass⟩ :=
    horizon.exists_pos_valid_twoRefreshScheduleRegion
  refine ⟨gap, hgap, ?_⟩
  unfold PositiveHorizon.fixedScheduleMeasure at hmass
  rw [Measure.map_apply (measurable_padCandidateWaits 2)
    (horizon.measurableSet_validTwoRefreshScheduleRegion gap),
    horizon.preimage_validTwoRefreshScheduleRegion_pad] at hmass
  exact hmass

/-- The singleton masses of a Poisson law sum to one. -/
theorem tsum_poisson_singletons (intensity : NNReal) :
    ∑' n : ℕ, poissonMeasure intensity {n} = 1 := by
  rw [← measure_iUnion]
  · rw [show (⋃ n : ℕ, ({n} : Set ℕ)) = Set.univ by ext; simp]
    simp
  · intro i j hij
    exact Set.disjoint_singleton.2 hij
  · exact fun i => MeasurableSet.singleton i

/-- Every nonnegative exponential count weight has a finite Poisson moment. -/
theorem integrable_nnreal_pow_poissonMeasure
    (intensity coefficient : NNReal) :
    Integrable (fun count : ℕ => (coefficient : ℝ) ^ count)
      (poissonMeasure intensity) := by
  rw [integrable_poissonMeasure_iff]
  have hsummable : Summable (fun count : ℕ =>
      (((intensity : ℝ) * (coefficient : ℝ)) ^ count / count.factorial)) :=
    NormedSpace.expSeries_div_summable _
  have hscaled := hsummable.mul_left (Real.exp (-(intensity : ℝ)))
  apply hscaled.congr
  intro count
  rw [Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg coefficient.coe_nonneg count)]
  ring

/-- Exact probability-generating function of the Poisson count law. -/
theorem integral_nnreal_pow_poissonMeasure_eq
    (intensity coefficient : NNReal) :
    (∫ count : ℕ, (coefficient : ℝ) ^ count
      ∂poissonMeasure intensity) =
        Real.exp ((intensity : ℝ) * ((coefficient : ℝ) - 1)) := by
  rw [integral_poissonMeasure]
  have hsum := NormedSpace.expSeries_div_hasSum_exp
    ((intensity : ℝ) * (coefficient : ℝ))
  have hscaled := hsum.mul_left (Real.exp (-(intensity : ℝ)))
  calc
    (∑' count : ℕ,
      (Real.exp (-(intensity : ℝ)) * (intensity : ℝ) ^ count /
          (count.factorial : ℝ)) • (coefficient : ℝ) ^ count) =
        ∑' count : ℕ, Real.exp (-(intensity : ℝ)) *
          (((intensity : ℝ) * (coefficient : ℝ)) ^ count /
            (count.factorial : ℝ)) := by
              apply tsum_congr
              intro count
              simp only [smul_eq_mul]
              ring
    _ = Real.exp (-(intensity : ℝ)) *
        NormedSpace.exp ((intensity : ℝ) * (coefficient : ℝ)) :=
          hscaled.tsum_eq
    _ = Real.exp ((intensity : ℝ) * ((coefficient : ℝ) - 1)) := by
      rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]
      congr 1
      ring

/-- Exact exponentially weighted Poisson tail from count two onward. -/
theorem integral_nnreal_pow_poissonMeasure_two_le_eq
    (intensity coefficient : NNReal) :
    (∫ count : ℕ in {count | 2 ≤ count}, (coefficient : ℝ) ^ count
      ∂poissonMeasure intensity) =
      Real.exp ((intensity : ℝ) * ((coefficient : ℝ) - 1)) -
        Real.exp (-(intensity : ℝ)) *
          (1 + (intensity : ℝ) * (coefficient : ℝ)) := by
  let f : ℕ → ℝ := fun count => (coefficient : ℝ) ^ count
  let small : Set ℕ := {0, 1}
  have htail : {count : ℕ | 2 ≤ count} = smallᶜ := by
    ext count
    simp [small]
    omega
  have hsmall : MeasurableSet small := by measurability
  have hintegrable : Integrable f (poissonMeasure intensity) :=
    integrable_nnreal_pow_poissonMeasure intensity coefficient
  rw [htail, setIntegral_compl hsmall hintegrable]
  rw [show (∫ count, f count ∂poissonMeasure intensity) =
      Real.exp ((intensity : ℝ) * ((coefficient : ℝ) - 1)) by
        exact integral_nnreal_pow_poissonMeasure_eq intensity coefficient]
  have hsmallIntegral :
      (∫ count in small, f count ∂poissonMeasure intensity) =
        Real.exp (-(intensity : ℝ)) *
          (1 + (intensity : ℝ) * (coefficient : ℝ)) := by
    rw [show small = ({0} : Set ℕ) ∪ {1} by
      ext count
      simp only [small, Set.mem_insert_iff, Set.mem_singleton_iff,
        Set.mem_union]]
    rw [setIntegral_union]
    · rw [integral_singleton, integral_singleton]
      simp [f, poissonMeasure_real_singleton]
      ring
    · exact Set.disjoint_singleton.2 (by norm_num)
    · exact MeasurableSet.singleton 0
    · exact hintegrable.integrableOn
    · exact hintegrable.integrableOn
  rw [hsmallIntegral]

/-- `ENNReal` form of the weighted tail, connected exactly to the real
set-integral formula used by the quadratic estimate. -/
theorem lintegral_nnreal_pow_poissonMeasure_two_le_toReal_eq
    (intensity coefficient : NNReal) :
    (∫⁻ count : ℕ in {count | 2 ≤ count},
      (coefficient : ENNReal) ^ count
      ∂poissonMeasure intensity).toReal =
      Real.exp ((intensity : ℝ) * ((coefficient : ℝ) - 1)) -
        Real.exp (-(intensity : ℝ)) *
          (1 + (intensity : ℝ) * (coefficient : ℝ)) := by
  let tail : Set ℕ := {count | 2 ≤ count}
  let f : ℕ → ℝ := fun count => (coefficient : ℝ) ^ count
  have hintegrable : Integrable f
      ((poissonMeasure intensity).restrict tail) :=
    (integrable_nnreal_pow_poissonMeasure intensity coefficient).mono_measure
      Measure.restrict_le_self
  have hnonneg : 0 ≤ ∫ count, f count
      ∂(poissonMeasure intensity).restrict tail :=
    integral_nonneg (fun count => pow_nonneg coefficient.coe_nonneg count)
  have hconvert := ofReal_integral_eq_lintegral_ofReal hintegrable
    (Filter.Eventually.of_forall fun count =>
      pow_nonneg coefficient.coe_nonneg count)
  have hpoint : (fun count : ℕ => ENNReal.ofReal (f count)) =
      fun count => (coefficient : ENNReal) ^ count := by
    funext count
    simp [f, ENNReal.ofReal_pow coefficient.coe_nonneg]
  rw [hpoint] at hconvert
  have hreal : (∫ count, f count
      ∂(poissonMeasure intensity).restrict tail) =
      Real.exp ((intensity : ℝ) * ((coefficient : ℝ) - 1)) -
        Real.exp (-(intensity : ℝ)) *
          (1 + (intensity : ℝ) * (coefficient : ℝ)) := by
    simpa [tail, f] using
      integral_nnreal_pow_poissonMeasure_two_le_eq intensity coefficient
  rw [← hconvert, ENNReal.toReal_ofReal hnonneg, hreal]

/-- Consequently the corresponding `ENNReal` Poisson moment is finite. -/
theorem lintegral_nnreal_pow_poissonMeasure_lt_top
    (intensity coefficient : NNReal) :
    (∫⁻ count : ℕ, (coefficient : ENNReal) ^ count
      ∂poissonMeasure intensity) < ⊤ := by
  have hintegrable := integrable_nnreal_pow_poissonMeasure intensity coefficient
  rw [show (fun count : ℕ => (coefficient : ENNReal) ^ count) =
      fun count => ENNReal.ofReal ((coefficient : ℝ) ^ count) by
    funext count
    rw [ENNReal.ofReal_pow coefficient.coe_nonneg]
    simp]
  rw [← ofReal_integral_eq_lintegral_ofReal hintegrable
    (Filter.Eventually.of_forall fun count =>
      pow_nonneg coefficient.coe_nonneg count)]
  exact ENNReal.ofReal_lt_top

/-- Adjacent Poisson count weights satisfy the birth/death recurrence used by
cross-count generator cancellation. -/
theorem poissonMeasure_real_singleton_succ_flux
    (intensity : NNReal) (count : ℕ) :
    ((count + 1 : ℕ) : ℝ) * (poissonMeasure intensity).real {count + 1} =
      (intensity : ℝ) * (poissonMeasure intensity).real {count} := by
  rw [poissonMeasure_real_singleton, poissonMeasure_real_singleton]
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  field_simp

/-- Joint law of a Poisson candidate count and its conditional ordered wait
sequence. The family argument makes the measurable-sorting obligation
explicit at every count. -/
noncomputable def poissonCandidateScheduleMeasure
    (intensity : NNReal) (horizon : PositiveHorizon)
    (orderings : ∀ n, TimestampOrdering n) :
    Measure CandidateScheduleSample :=
  Measure.sum fun n : ℕ =>
    poissonMeasure intensity {n} •
      horizon.fixedScheduleMeasure (orderings n)

instance poissonCandidateScheduleMeasure.instIsProbabilityMeasure
    (intensity : NNReal) (horizon : PositiveHorizon)
    (orderings : ∀ n, TimestampOrdering n) :
    IsProbabilityMeasure
      (poissonCandidateScheduleMeasure intensity horizon orderings) := by
  constructor
  rw [poissonCandidateScheduleMeasure, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  exact tsum_poisson_singletons intensity

/-- The count marginal of the joint schedule law is exactly the supplied
Poisson law. -/
theorem poissonCandidateScheduleMeasure_map_fst
    (intensity : NNReal) (horizon : PositiveHorizon)
    (orderings : ∀ n, TimestampOrdering n) :
    Measure.map Prod.fst
        (poissonCandidateScheduleMeasure intensity horizon orderings) =
      poissonMeasure intensity := by
  rw [Measure.ext_iff_singleton]
  intro k
  rw [Measure.map_apply measurable_fst (MeasurableSet.singleton k),
    poissonCandidateScheduleMeasure,
    Measure.sum_apply _ (MeasurableSet.singleton k |>.preimage measurable_fst)]
  rw [tsum_eq_single k]
  · unfold PositiveHorizon.fixedScheduleMeasure
    rw [Measure.smul_apply, Measure.map_apply (measurable_padCandidateWaits k)
      (MeasurableSet.singleton k |>.preimage measurable_fst)]
    have hpre : padCandidateWaits k ⁻¹' (Prod.fst ⁻¹' {k}) = Set.univ := by
      ext waits
      simp [padCandidateWaits]
    rw [hpre, measure_univ]
    simp
  · intro n hne
    unfold PositiveHorizon.fixedScheduleMeasure
    rw [Measure.smul_apply, Measure.map_apply (measurable_padCandidateWaits n)
      (MeasurableSet.singleton k |>.preimage measurable_fst)]
    have hpre : padCandidateWaits n ⁻¹' (Prod.fst ⁻¹' {k}) = ∅ := by
      ext waits
      simp [padCandidateWaits, hne]
    rw [hpre, measure_empty]
    simp

/-- Unconditional homogeneous-clock schedule law using the certified
all-count tuple ordering. -/
noncomputable def poissonCandidateSchedule
    (intensity : NNReal) (horizon : PositiveHorizon) :
    Measure CandidateScheduleSample :=
  poissonCandidateScheduleMeasure intensity horizon timestampOrdering

/-- Janossy representation of the unconditional homogeneous-clock schedule:
each count stratum is its unnormalized timestamp mass times the corresponding
Poisson coefficient. -/
theorem poissonCandidateSchedule_eq_sum_timestampMass
    (refreshRate : NNReal) (horizon : PositiveHorizon) :
    poissonCandidateSchedule (refreshRate * horizon.duration) horizon =
      Measure.sum fun n : ℕ =>
        poissonScheduleMassWeight refreshRate horizon n •
          horizon.timestampScheduleMass n := by
  unfold poissonCandidateSchedule poissonCandidateScheduleMeasure
  apply Measure.sum_congr
  intro n
  exact poisson_smul_fixedSchedule_eq_massWeight_smul refreshRate horizon n

instance poissonCandidateSchedule.instIsProbabilityMeasure
    (intensity : NNReal) (horizon : PositiveHorizon) :
    IsProbabilityMeasure (poissonCandidateSchedule intensity horizon) := by
  unfold poissonCandidateSchedule
  infer_instance

/-- The unconditional padded Poisson schedule stays within its horizon almost
surely, with the random stored count selecting the active prefix. -/
theorem ae_poissonCandidateSchedule_elapsed_le
    (intensity : NNReal) (horizon : PositiveHorizon) :
    ∀ᵐ schedule ∂poissonCandidateSchedule intensity horizon,
      (∑ index ∈ Finset.range schedule.1, schedule.2 index) ≤
        horizon.duration := by
  unfold poissonCandidateSchedule poissonCandidateScheduleMeasure
  rw [Measure.ae_sum_iff]
  intro count
  apply Measure.ae_smul_measure
  filter_upwards [horizon.ae_fixedScheduleMeasure_fst
      (timestampOrdering count),
    horizon.ae_fixedScheduleMeasure_elapsed_le
      (timestampOrdering count)] with schedule hcount helapsed
  simpa only [hcount] using helapsed

/-- The concrete unconditional schedule retains the exact Poisson count
marginal. -/
theorem poissonCandidateSchedule_map_fst
    (intensity : NNReal) (horizon : PositiveHorizon) :
    Measure.map Prod.fst (poissonCandidateSchedule intensity horizon) =
      poissonMeasure intensity :=
  poissonCandidateScheduleMeasure_map_fst intensity horizon timestampOrdering

/-- The event that a padded schedule stores exactly `count` refreshes has the
corresponding Poisson singleton mass. -/
theorem poissonCandidateSchedule_count_eq
    (intensity : NNReal) (horizon : PositiveHorizon) (count : ℕ) :
    poissonCandidateSchedule intensity horizon
        {schedule | schedule.1 = count} =
      poissonMeasure intensity {count} := by
  have hmap := congrArg (fun measure : Measure ℕ => measure {count})
    (poissonCandidateSchedule_map_fst intensity horizon)
  rw [Measure.map_apply measurable_fst (MeasurableSet.singleton count)] at hmap
  rw [show {schedule : CandidateScheduleSample | schedule.1 = count} =
      Prod.fst ⁻¹' {count} by ext; simp]
  exact hmap

/-- At every strictly positive clock intensity, every exact finite refresh
count has strictly positive schedule probability. -/
theorem poissonCandidateSchedule_count_pos
    {intensity : NNReal} (hintensity : 0 < intensity)
    (horizon : PositiveHorizon) (count : ℕ) :
    0 < poissonCandidateSchedule intensity horizon
      {schedule | schedule.1 = count} := by
  rw [poissonCandidateSchedule_count_eq, poissonMeasure_singleton]
  positivity

/-- A positive refresh rate on a positive horizon gives a strictly positive
one-refresh stratum in the actual schedule law. -/
theorem poissonCandidateSchedule_one_refresh_pos
    {refreshRate : NNReal} (hrefreshRate : 0 < refreshRate)
    (horizon : PositiveHorizon) :
    0 < poissonCandidateSchedule (refreshRate * horizon.duration) horizon
      {schedule | schedule.1 = 1} :=
  poissonCandidateSchedule_count_pos (mul_pos hrefreshRate horizon.positive)
    horizon 1

/-- Independent Poisson refresh counts on adjacent horizons add to the
Poisson count on the concatenated horizon. -/
theorem poissonRefreshCount_add (refreshRate : NNReal)
    (first second : PositiveHorizon) :
    Measure.map (fun counts : ℕ × ℕ => counts.1 + counts.2)
        ((poissonMeasure (refreshRate * first.duration)).prod
          (poissonMeasure (refreshRate * second.duration))) =
      poissonMeasure (refreshRate * (first.add second).duration) := by
  change (poissonMeasure (refreshRate * first.duration)).conv
      (poissonMeasure (refreshRate * second.duration)) = _
  rw [poissonMeasure_conv_poissonMeasure]
  congr 2
  rw [PositiveHorizon.add_duration, mul_add]

end Mcmc.PDMP
