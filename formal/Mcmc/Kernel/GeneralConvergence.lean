import Mcmc.Kernel.MeetingDrift
import Mathlib.MeasureTheory.Measure.Sub

/-!
# General-state quantitative convergence through couplings

This module supplies the eventwise coupling inequality and a geometric
kernel-power consequence.  Unlike stationarity, these statements quantify
convergence of transition laws.  They are designed as the target interface
for Doeblin and independence-Metropolis minorization arguments.
!-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace Mcmc

variable {α : Type*} [MeasurableSpace α]

namespace Kernel

/-- A general-state transition is topologically irreducible when every row
charges every nonempty open set. This deliberately says nothing about a
common irreducibility measure, recurrence, or convergence. -/
def TopologicallyIrreducible [TopologicalSpace α]
    (transition : ProbabilityTheory.Kernel α α) : Prop :=
  ∀ state event, IsOpen event → event.Nonempty →
    0 < transition state event

/-- Pointwise open-set positivity packages as topological irreducibility. -/
theorem topologicallyIrreducible_of_open_pos [TopologicalSpace α]
    (transition : ProbabilityTheory.Kernel α α)
    (hpos : ∀ state event, IsOpen event → event.Nonempty →
      0 < transition state event) :
    TopologicallyIrreducible transition :=
  hpos

/-- Irreducibility with respect to a concrete sigma-finite reference measure:
every row charges each measurable set of positive reference mass. This is the
measure-theoretic notion needed by Harris recurrence arguments. -/
def ReferenceMeasureIrreducible
    (transition : ProbabilityTheory.Kernel α α)
    (reference : Measure α) : Prop :=
  ∀ state event, MeasurableSet event → 0 < reference event →
    0 < transition state event

/-- Reference-measure irreducibility implies open-set irreducibility whenever
the reference measure has full topological support. The converse is not
asserted. -/
theorem ReferenceMeasureIrreducible.topologicallyIrreducible
    [TopologicalSpace α] [OpensMeasurableSpace α]
    (transition : ProbabilityTheory.Kernel α α)
    (reference : Measure α) [reference.IsOpenPosMeasure]
    (hirreducible : ReferenceMeasureIrreducible transition reference) :
    TopologicallyIrreducible transition := by
  intro state event hevent heventNonempty
  exact hirreducible state event hevent.measurableSet
    (hevent.measure_pos reference heventNonempty)

end Kernel

namespace IsMeasureCoupling

/-- The probability assigned differently by two marginal laws on any event
is controlled by the coupling's off-diagonal mass. -/
theorem fst_apply_le_snd_apply_add_compl_diagonal
    {ρ : Measure (α × α)} {μ ν : Measure α}
    (h : IsMeasureCoupling ρ μ ν) {s : Set α} (hs : MeasurableSet s) :
    μ s ≤ ν s + ρ (Set.diagonal α)ᶜ := by
  let A : Set (α × α) := Prod.fst ⁻¹' s
  let B : Set (α × α) := Prod.snd ⁻¹' s
  have hsubset : A ⊆ B ∪ (Set.diagonal α)ᶜ := by
    intro z hz
    by_cases heq : z.1 = z.2
    · left
      change z.1 ∈ s at hz
      change z.2 ∈ s
      rw [← heq]
      exact hz
    · right
      simpa [Set.mem_diagonal_iff] using heq
  calc
    μ s = ρ A := by
      rw [← h.fst, Measure.fst_apply hs]
    _ ≤ ρ (B ∪ (Set.diagonal α)ᶜ) := measure_mono hsubset
    _ ≤ ρ B + ρ (Set.diagonal α)ᶜ := measure_union_le _ _
    _ = ν s + ρ (Set.diagonal α)ᶜ := by
      rw [← h.snd, Measure.snd_apply hs]

/-- Symmetric eventwise coupling inequality. -/
theorem snd_apply_le_fst_apply_add_compl_diagonal
    {ρ : Measure (α × α)} {μ ν : Measure α}
    (h : IsMeasureCoupling ρ μ ν) {s : Set α} (hs : MeasurableSet s) :
    ν s ≤ μ s + ρ (Set.diagonal α)ᶜ := by
  let A : Set (α × α) := Prod.snd ⁻¹' s
  let B : Set (α × α) := Prod.fst ⁻¹' s
  have hsubset : A ⊆ B ∪ (Set.diagonal α)ᶜ := by
    intro z hz
    by_cases heq : z.1 = z.2
    · left
      change z.2 ∈ s at hz
      change z.1 ∈ s
      rw [heq]
      exact hz
    · right
      simpa [Set.mem_diagonal_iff] using heq
  calc
    ν s = ρ A := by
      rw [← h.snd, Measure.snd_apply hs]
    _ ≤ ρ (B ∪ (Set.diagonal α)ᶜ) := measure_mono hsubset
    _ ≤ ρ B + ρ (Set.diagonal α)ᶜ := measure_union_le _ _
    _ = μ s + ρ (Set.diagonal α)ᶜ := by
      rw [← h.fst, Measure.fst_apply hs]

/-- Coupling inequality for bounded real observables. The expectation gap is
controlled by twice the uniform bound times the off-diagonal probability. -/
theorem norm_integral_sub_integral_le_compl_diagonal
    [MeasurableEq α]
    {ρ : Measure (α × α)} [IsProbabilityMeasure ρ]
    {μ ν : Measure α} (hcoupling : IsMeasureCoupling ρ μ ν)
    (f : α → ℝ) (hf : Measurable f) {B : ℝ}
    (hbound : ∀ x, ‖f x‖ ≤ B) :
    ‖(∫ x, f x ∂μ) - ∫ x, f x ∂ν‖ ≤
      (2 * B) * ρ.real (Set.diagonal α)ᶜ := by
  let event : Set (α × α) := (Set.diagonal α)ᶜ
  have hevent : MeasurableSet event := measurableSet_diagonal.compl
  have hfstInt : Integrable (fun z : α × α => f z.1) ρ := by
    exact (MemLp.of_bound (hf.comp measurable_fst).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun z => hbound z.1) :
        MemLp (fun z : α × α => f z.1) 1 ρ).integrable le_rfl
  have hsndInt : Integrable (fun z : α × α => f z.2) ρ := by
    exact (MemLp.of_bound (hf.comp measurable_snd).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun z => hbound z.2) :
        MemLp (fun z : α × α => f z.2) 1 ρ).integrable le_rfl
  have hfst : (∫ x, f x ∂μ) = ∫ z, f z.1 ∂ρ := by
    rw [← hcoupling.fst]
    exact integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable
  have hsnd : (∫ x, f x ∂ν) = ∫ z, f z.2 ∂ρ := by
    rw [← hcoupling.snd]
    exact integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable
  rw [hfst, hsnd, ← integral_sub hfstInt hsndInt]
  have hrestrict : (∫ z, f z.1 - f z.2 ∂ρ) =
      ∫ z, f z.1 - f z.2 ∂ρ.restrict event := by
    rw [← integral_indicator hevent]
    apply integral_congr_ae
    filter_upwards with z
    by_cases hz : z ∈ event
    · simp [Set.indicator_of_mem hz]
    · have heq : z.1 = z.2 := by
        simpa [event, Set.mem_diagonal_iff] using hz
      simp [Set.indicator_of_notMem hz, heq]
  rw [hrestrict]
  have hnorm : ∀ᵐ z ∂ρ.restrict event, ‖f z.1 - f z.2‖ ≤ 2 * B := by
    filter_upwards with z
    exact (norm_sub_le (f z.1) (f z.2)).trans
      ((add_le_add (hbound z.1) (hbound z.2)).trans_eq (by ring))
  calc
    _ ≤ (2 * B) * (ρ.restrict event).real Set.univ :=
      norm_integral_le_of_norm_le_const hnorm
    _ = (2 * B) * ρ.real (Set.diagonal α)ᶜ := by
      simp [event, Measure.real]

end IsMeasureCoupling

namespace Kernel

open ProbabilityTheory

/-- A faithful path-law meeting tail controls the eventwise discrepancy of
two marginal chains, even when their initial laws differ. -/
theorem lawAtTime_left_apply_le_right_add_exactMeetingTail
    [MeasurableEq α]
    (initialCoupling : Measure (α × α)) [IsProbabilityMeasure initialCoupling]
    (leftInitial rightInitial : Measure α)
    (transition : Kernel α α) [IsMarkovKernel transition]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (hinitial : IsMeasureCoupling initialCoupling leftInitial rightInitial)
    (hcoupled : IsCoupling coupled transition transition)
    (hfaithful : IsFaithful coupled) (n : ℕ)
    {s : Set α} (hs : MeasurableSet s) :
    lawAtTime leftInitial transition n s ≤
      lawAtTime rightInitial transition n s +
        exactMeetingTail (pathLaw initialCoupling coupled) n := by
  have hmarginals := lawAtTime_isMeasureCoupling initialCoupling
    leftInitial rightInitial coupled transition transition hinitial hcoupled n
  have hcoupling := hmarginals.fst_apply_le_snd_apply_add_compl_diagonal hs
  rw [← offDiagonalMassAtTime_eq_exactMeetingTail_pathLaw_of_faithful
    initialCoupling coupled hfaithful n]
  exact hcoupling

/-- Symmetric eventwise form of the heterogeneous-initialization meeting-tail
bound. -/
theorem lawAtTime_right_apply_le_left_add_exactMeetingTail
    [MeasurableEq α]
    (initialCoupling : Measure (α × α)) [IsProbabilityMeasure initialCoupling]
    (leftInitial rightInitial : Measure α)
    (transition : Kernel α α) [IsMarkovKernel transition]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (hinitial : IsMeasureCoupling initialCoupling leftInitial rightInitial)
    (hcoupled : IsCoupling coupled transition transition)
    (hfaithful : IsFaithful coupled) (n : ℕ)
    {s : Set α} (hs : MeasurableSet s) :
    lawAtTime rightInitial transition n s ≤
      lawAtTime leftInitial transition n s +
        exactMeetingTail (pathLaw initialCoupling coupled) n := by
  have hmarginals := lawAtTime_isMeasureCoupling initialCoupling
    leftInitial rightInitial coupled transition transition hinitial hcoupled n
  have hcoupling := hmarginals.snd_apply_le_fst_apply_add_compl_diagonal hs
  rw [← offDiagonalMassAtTime_eq_exactMeetingTail_pathLaw_of_faithful
    initialCoupling coupled hfaithful n]
  exact hcoupling

/-- Bounded-observable version of the faithful path-law coupling bound. -/
theorem norm_lawAtTime_integral_sub_le_exactMeetingTail
    [MeasurableEq α]
    (initialCoupling : Measure (α × α)) [IsProbabilityMeasure initialCoupling]
    (leftInitial rightInitial : Measure α)
    (transition : Kernel α α) [IsMarkovKernel transition]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (hinitial : IsMeasureCoupling initialCoupling leftInitial rightInitial)
    (hcoupled : IsCoupling coupled transition transition)
    (hfaithful : IsFaithful coupled) (f : α → ℝ) (hf : Measurable f)
    {B : ℝ} (hbound : ∀ x, ‖f x‖ ≤ B) (n : ℕ) :
    ‖(∫ x, f x ∂lawAtTime leftInitial transition n) -
        ∫ x, f x ∂lawAtTime rightInitial transition n‖ ≤
      (2 * B) *
        (exactMeetingTail (pathLaw initialCoupling coupled) n).toReal := by
  have hmarginals := lawAtTime_isMeasureCoupling initialCoupling
    leftInitial rightInitial coupled transition transition hinitial hcoupled n
  have hbound' := hmarginals.norm_integral_sub_integral_le_compl_diagonal
    f hf hbound
  change ‖(∫ x, f x ∂lawAtTime leftInitial transition n) -
      ∫ x, f x ∂lawAtTime rightInitial transition n‖ ≤
    (2 * B) * (offDiagonalMassAtTime initialCoupling coupled n).toReal
    at hbound'
  rw [offDiagonalMassAtTime_eq_exactMeetingTail_pathLaw_of_faithful
    initialCoupling coupled hfaithful n] at hbound'
  exact hbound'

/-- Stationary-target specialization of the bounded-observable coupling
bound. -/
theorem norm_lawAtTime_integral_sub_invariant_le_exactMeetingTail
    [MeasurableEq α]
    (initialCoupling : Measure (α × α)) [IsProbabilityMeasure initialCoupling]
    (leftInitial target : Measure α)
    (transition : Kernel α α) [IsMarkovKernel transition]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (hinitial : IsMeasureCoupling initialCoupling leftInitial target)
    (hcoupled : IsCoupling coupled transition transition)
    (hfaithful : IsFaithful coupled) (hinvariant : transition.Invariant target)
    (f : α → ℝ) (hf : Measurable f) {B : ℝ}
    (hbound : ∀ x, ‖f x‖ ≤ B) (n : ℕ) :
    ‖(∫ x, f x ∂lawAtTime leftInitial transition n) -
        ∫ x, f x ∂target‖ ≤
      (2 * B) *
        (exactMeetingTail (pathLaw initialCoupling coupled) n).toReal := by
  simpa only [lawAtTime_eq_of_invariant target transition hinvariant n] using
    norm_lawAtTime_integral_sub_le_exactMeetingTail initialCoupling leftInitial
      target transition coupled hinitial hcoupled hfaithful f hf hbound n

/-- A geometric faithful meeting tail gives convergence of every bounded
observable expectation to its stationary-target expectation. -/
theorem tendsto_lawAtTime_integral_of_invariant_geometricMeeting
    [MeasurableEq α]
    (initialCoupling : Measure (α × α)) [IsProbabilityMeasure initialCoupling]
    (leftInitial target : Measure α)
    (transition : Kernel α α) [IsMarkovKernel transition]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (hinitial : IsMeasureCoupling initialCoupling leftInitial target)
    (hcoupled : IsCoupling coupled transition transition)
    (hfaithful : IsFaithful coupled) (hinvariant : transition.Invariant target)
    (f : α → ℝ) (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x, ‖f x‖ ≤ B) (C rate : ENNReal)
    (hC : C ≠ ⊤) (hrate : rate < 1)
    (htail : ∀ n, exactMeetingTail (pathLaw initialCoupling coupled) n ≤
      C * rate ^ n) :
    Filter.Tendsto
      (fun n => ∫ x, f x ∂lawAtTime leftInitial transition n)
      Filter.atTop (nhds (∫ x, f x ∂target)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hrateTop : rate ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hrate.le
  have hrateReal : rate.toReal < 1 := by
    rw [← ENNReal.toReal_one,
      ENNReal.toReal_lt_toReal hrateTop ENNReal.one_ne_top]
    exact hrate
  have hpoint (n : ℕ) :
      ‖(∫ x, f x ∂lawAtTime leftInitial transition n) -
          ∫ x, f x ∂target‖ ≤
        (2 * B * C.toReal) * rate.toReal ^ n := by
    have hcoupling :=
      norm_lawAtTime_integral_sub_invariant_le_exactMeetingTail
        initialCoupling leftInitial target transition coupled hinitial hcoupled
        hfaithful hinvariant f hf hbound n
    have hrhsTop : C * rate ^ n ≠ ⊤ :=
      ENNReal.mul_ne_top hC (ENNReal.pow_ne_top hrateTop)
    have htailTop : exactMeetingTail
        (pathLaw initialCoupling coupled) n ≠ ⊤ :=
      ne_top_of_le_ne_top hrhsTop (htail n)
    have hreal : (exactMeetingTail
        (pathLaw initialCoupling coupled) n).toReal ≤
        (C * rate ^ n).toReal :=
      (ENNReal.toReal_le_toReal htailTop hrhsTop).2 (htail n)
    calc
      _ ≤ (2 * B) *
          (exactMeetingTail (pathLaw initialCoupling coupled) n).toReal :=
        hcoupling
      _ ≤ (2 * B) * (C * rate ^ n).toReal := by
        gcongr
      _ = (2 * B * C.toReal) * rate.toReal ^ n := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_pow]
        ring
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    (Filter.Eventually.of_forall hpoint)
  simpa only [mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one ENNReal.toReal_nonneg hrateReal).const_mul
      (2 * B * C.toReal)

/-- A geometric drift condition, a positive exact-meeting small set, and a
finite initial Lyapunov moment imply convergence of every bounded observable
to its invariant-target expectation.  This packages the drift/meeting layer
into the marginal convergence interface used by sampler clients. -/
theorem HasGeometricDrift.tendsto_lawAtTime_integral_of_invariant
    [MeasurableEq α]
    (initialCoupling : Measure (α × α))
    [IsProbabilityMeasure initialCoupling]
    (leftInitial target : Measure α)
    (transition : Kernel α α) [IsMarkovKernel transition]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (hinitial : IsMeasureCoupling initialCoupling leftInitial target)
    (hcoupled : IsCoupling coupled transition transition)
    (hfaithful : IsFaithful coupled) (hinvariant : transition.Invariant target)
    {V : (α × α) → ENNReal}
    {driftRate allowance meetingBound threshold : ENNReal}
    (hdrift : HasGeometricDrift coupled V (lyapunovSublevel V threshold)
      driftRate allowance)
    (hmeeting : IsExactMeetingSmallSet coupled
      (lyapunovSublevel V threshold) meetingBound)
    (hdriftRate : driftRate < 1)
    (hmeetingPos : 0 < meetingBound) (hmeetingBound : meetingBound ≤ 1)
    (hthreshold0 : threshold ≠ 0) (hthresholdTop : threshold ≠ ∞)
    (hdriftBudgetTop : driftRate * threshold + allowance ≠ ∞)
    (hVmoment : (∫⁻ x, V x ∂initialCoupling) ≠ ∞)
    (f : α → ℝ) (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x, ‖f x‖ ≤ B) :
    Filter.Tendsto
      (fun n => ∫ x, f x ∂lawAtTime leftInitial transition n)
      Filter.atTop (nhds (∫ x, f x ∂target)) := by
  obtain ⟨scale, rate, _hscale0, hscaleTop, hrate, htail⟩ :=
    hdrift.exists_scale_rate_exactMeetingTail_pathLaw_le initialCoupling
      coupled hmeeting hfaithful hdriftRate hmeetingPos hmeetingBound
      hthreshold0 hthresholdTop hdriftBudgetTop
  let C := weightedOffDiagonalMassAtTime initialCoupling coupled V scale 0
  have hC : C ≠ ∞ :=
    weightedOffDiagonalMassAtTime_zero_ne_top_of_lintegral_ne_top
      initialCoupling coupled hdrift.1 scale hscaleTop hVmoment
  apply tendsto_lawAtTime_integral_of_invariant_geometricMeeting
    initialCoupling leftInitial target transition coupled hinitial hcoupled
    hfaithful hinvariant f hf hB hbound C rate hC hrate
  intro n
  simpa only [C, mul_comm] using htail n

/-- If the right marginal starts stationary, the coupling tail directly
controls eventwise convergence of the left chain. -/
theorem lawAtTime_apply_le_invariant_add_exactMeetingTail
    [MeasurableEq α]
    (initialCoupling : Measure (α × α)) [IsProbabilityMeasure initialCoupling]
    (leftInitial target : Measure α)
    (transition : Kernel α α) [IsMarkovKernel transition]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (hinitial : IsMeasureCoupling initialCoupling leftInitial target)
    (hcoupled : IsCoupling coupled transition transition)
    (hfaithful : IsFaithful coupled) (hinvariant : transition.Invariant target)
    (n : ℕ) {s : Set α} (hs : MeasurableSet s) :
    lawAtTime leftInitial transition n s ≤
      target s + exactMeetingTail (pathLaw initialCoupling coupled) n := by
  simpa only [lawAtTime_eq_of_invariant target transition hinvariant n] using
    lawAtTime_left_apply_le_right_add_exactMeetingTail initialCoupling
      leftInitial target transition coupled hinitial hcoupled hfaithful n hs

/-- The symmetric stationary-target eventwise coupling bound. -/
theorem invariant_apply_le_lawAtTime_add_exactMeetingTail
    [MeasurableEq α]
    (initialCoupling : Measure (α × α)) [IsProbabilityMeasure initialCoupling]
    (leftInitial target : Measure α)
    (transition : Kernel α α) [IsMarkovKernel transition]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (hinitial : IsMeasureCoupling initialCoupling leftInitial target)
    (hcoupled : IsCoupling coupled transition transition)
    (hfaithful : IsFaithful coupled) (hinvariant : transition.Invariant target)
    (n : ℕ) {s : Set α} (hs : MeasurableSet s) :
    target s ≤ lawAtTime leftInitial transition n s +
      exactMeetingTail (pathLaw initialCoupling coupled) n := by
  simpa only [lawAtTime_eq_of_invariant target transition hinvariant n] using
    lawAtTime_right_apply_le_left_add_exactMeetingTail initialCoupling
      leftInitial target transition coupled hinitial hcoupled hfaithful n hs

/-- A geometric faithful meeting tail implies setwise convergence to an
invariant target. -/
theorem lawAtTime_apply_tendsto_of_invariant_geometricMeeting
    [MeasurableEq α]
    (initialCoupling : Measure (α × α)) [IsProbabilityMeasure initialCoupling]
    (leftInitial target : Measure α) [IsProbabilityMeasure target]
    (transition : Kernel α α) [IsMarkovKernel transition]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (hinitial : IsMeasureCoupling initialCoupling leftInitial target)
    (hcoupled : IsCoupling coupled transition transition)
    (hfaithful : IsFaithful coupled) (hinvariant : transition.Invariant target)
    (C rate : ENNReal) (hC : C ≠ ∞) (hrate : rate < 1)
    (htail : ∀ n, exactMeetingTail (pathLaw initialCoupling coupled) n ≤
      C * rate ^ n) {s : Set α} (hs : MeasurableSet s) :
    Filter.Tendsto (fun n => lawAtTime leftInitial transition n s)
      Filter.atTop (nhds (target s)) := by
  let remainder : ℕ → ENNReal := fun n => C * rate ^ n
  have hpow : Filter.Tendsto (fun n : ℕ => rate ^ n)
      Filter.atTop (nhds 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hrate
  have hremainder : Filter.Tendsto remainder Filter.atTop (nhds 0) := by
    simpa only [remainder, mul_zero] using
      ENNReal.Tendsto.const_mul hpow (.inr hC)
  have hlower : Filter.Tendsto (fun n => target s - remainder n)
      Filter.atTop (nhds (target s)) := by
    have h := ENNReal.Tendsto.sub tendsto_const_nhds hremainder
      (Or.inl (measure_ne_top target s))
    simpa only [tsub_zero] using h
  have hupper : Filter.Tendsto (fun n => target s + remainder n)
      Filter.atTop (nhds (target s)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hremainder
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hupper
  · intro n
    rw [tsub_le_iff_right]
    calc
      target s ≤ lawAtTime leftInitial transition n s +
          exactMeetingTail (pathLaw initialCoupling coupled) n :=
        invariant_apply_le_lawAtTime_add_exactMeetingTail
          initialCoupling leftInitial target transition coupled hinitial hcoupled
          hfaithful hinvariant n hs
      _ ≤ lawAtTime leftInitial transition n s + remainder n := by
        gcongr
        exact htail n
  · intro n
    calc
      lawAtTime leftInitial transition n s ≤ target s +
          exactMeetingTail (pathLaw initialCoupling coupled) n :=
        lawAtTime_apply_le_invariant_add_exactMeetingTail
          initialCoupling leftInitial target transition coupled hinitial hcoupled
          hfaithful hinvariant n hs
      _ ≤ target s + remainder n := by
        gcongr
        exact htail n

/-- Drift, a positive exact-meeting small set, and a finite initial Lyapunov
moment imply setwise convergence to an invariant target. -/
theorem HasGeometricDrift.lawAtTime_apply_tendsto_of_invariant
    [MeasurableEq α]
    (initialCoupling : Measure (α × α))
    [IsProbabilityMeasure initialCoupling]
    (leftInitial target : Measure α) [IsProbabilityMeasure target]
    (transition : Kernel α α) [IsMarkovKernel transition]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (hinitial : IsMeasureCoupling initialCoupling leftInitial target)
    (hcoupled : IsCoupling coupled transition transition)
    (hfaithful : IsFaithful coupled) (hinvariant : transition.Invariant target)
    {V : (α × α) → ENNReal}
    {driftRate allowance meetingBound threshold : ENNReal}
    (hdrift : HasGeometricDrift coupled V (lyapunovSublevel V threshold)
      driftRate allowance)
    (hmeeting : IsExactMeetingSmallSet coupled
      (lyapunovSublevel V threshold) meetingBound)
    (hdriftRate : driftRate < 1)
    (hmeetingPos : 0 < meetingBound) (hmeetingBound : meetingBound ≤ 1)
    (hthreshold0 : threshold ≠ 0) (hthresholdTop : threshold ≠ ∞)
    (hdriftBudgetTop : driftRate * threshold + allowance ≠ ∞)
    (hVmoment : (∫⁻ x, V x ∂initialCoupling) ≠ ∞)
    {s : Set α} (hs : MeasurableSet s) :
    Filter.Tendsto (fun n => lawAtTime leftInitial transition n s)
      Filter.atTop (nhds (target s)) := by
  obtain ⟨scale, rate, _hscale0, hscaleTop, hrate, htail⟩ :=
    hdrift.exists_scale_rate_exactMeetingTail_pathLaw_le initialCoupling
      coupled hmeeting hfaithful hdriftRate hmeetingPos hmeetingBound
      hthreshold0 hthresholdTop hdriftBudgetTop
  let C := weightedOffDiagonalMassAtTime initialCoupling coupled V scale 0
  have hC : C ≠ ∞ :=
    weightedOffDiagonalMassAtTime_zero_ne_top_of_lintegral_ne_top
      initialCoupling coupled hdrift.1 scale hscaleTop hVmoment
  apply lawAtTime_apply_tendsto_of_invariant_geometricMeeting
    initialCoupling leftInitial target transition coupled hinitial hcoupled
    hfaithful hinvariant C rate hC hrate (s := s)
  · intro n
    simpa only [C, mul_comm] using htail n
  · exact hs

/-- Drift toward an arbitrary measurable exact-meeting set implies setwise
convergence once the usual inside/outside Lyapunov and scalar contraction
bounds are supplied.  Unlike
`HasGeometricDrift.lawAtTime_apply_tendsto_of_invariant`, this theorem does
not require the algorithm-specific meeting set to be definitionally a
Lyapunov sublevel. -/
theorem HasGeometricDrift.lawAtTime_apply_tendsto_of_invariant_of_bounds
    [MeasurableEq α]
    (initialCoupling : Measure (α × α))
    [IsProbabilityMeasure initialCoupling]
    (leftInitial target : Measure α) [IsProbabilityMeasure target]
    (transition : Kernel α α) [IsMarkovKernel transition]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (hinitial : IsMeasureCoupling initialCoupling leftInitial target)
    (hcoupled : IsCoupling coupled transition transition)
    (hfaithful : IsFaithful coupled) (hinvariant : transition.Invariant target)
    {V : (α × α) → ENNReal} {C : Set (α × α)}
    {driftRate allowance meetingBound scale contractionRate
      lowerBound upperBound : ENNReal}
    (hdrift : HasGeometricDrift coupled V C driftRate allowance)
    (hmeeting : IsExactMeetingSmallSet coupled C meetingBound)
    (hrates : driftRate ≤ contractionRate)
    (hlower : ∀ x ∉ C, lowerBound ≤ V x)
    (hupper : ∀ x ∈ C, V x ≤ upperBound)
    (houtsideBudget :
      1 + scale * (driftRate * lowerBound) ≤
        contractionRate * (1 + scale * lowerBound))
    (hinsideBudget :
      (1 - meetingBound) +
          scale * (driftRate * upperBound + allowance) ≤ contractionRate)
    (hcontractionRate : contractionRate < 1)
    (hscaleTop : scale ≠ ∞)
    (hVmoment : (∫⁻ x, V x ∂initialCoupling) ≠ ∞)
    {s : Set α} (hs : MeasurableSet s) :
    Filter.Tendsto (fun n => lawAtTime leftInitial transition n s)
      Filter.atTop (nhds (target s)) := by
  let mass := weightedOffDiagonalMassAtTime
    initialCoupling coupled V scale 0
  have hmass : mass ≠ ∞ :=
    weightedOffDiagonalMassAtTime_zero_ne_top_of_lintegral_ne_top
      initialCoupling coupled hdrift.1 scale hscaleTop hVmoment
  apply lawAtTime_apply_tendsto_of_invariant_geometricMeeting
    initialCoupling leftInitial target transition coupled hinitial hcoupled
    hfaithful hinvariant mass contractionRate hmass hcontractionRate (s := s)
  · intro n
    have htail := hdrift.exactMeetingTail_pathLaw_le_weighted_of_bounds
      initialCoupling coupled hmeeting hfaithful hrates hlower hupper
        houtsideBudget hinsideBudget n
    simpa only [mass, mul_comm] using htail
  · exact hs

/-- A kernel uniformly minorizes a measure with coefficient `ε`. -/
def UniformlyMinorizes (transition : Kernel α α) (ε : ENNReal)
    (target : Measure α) : Prop :=
  ∀ x s, MeasurableSet s → ε * target s ≤ transition x s

private theorem minorization_measure_le
    (transition : Kernel α α) (target : Measure α) (ε : ENNReal)
    (hminor : UniformlyMinorizes transition ε target) (x : α) :
    ε • target ≤ transition x := by
  apply Measure.le_iff.mpr
  intro s hs
  simpa [Measure.smul_apply, smul_eq_mul] using hminor x s hs

/-- The residual transition obtained by removing a strict Doeblin component
and renormalizing the remaining row mass. -/
noncomputable def minorizationResidual
    (transition : Kernel α α) [IsMarkovKernel transition]
    (target : Measure α) [IsProbabilityMeasure target]
    (ε : Set.Icc (0 : NNReal) 1) (_hε : ε.1 < 1)
    (hminor : UniformlyMinorizes transition ε.1 target) : Kernel α α where
  toFun x := (((1 - ε.1 : NNReal) : ENNReal)⁻¹) •
    (transition x - (ε.1 : ENNReal) • target)
  measurable' := by
    letI : IsFiniteMeasure ((ε.1 : ENNReal) • target) :=
      target.smul_finite ENNReal.coe_ne_top
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    have hinner : Measurable (fun x => transition x s -
        (ε.1 : ENNReal) * target s) :=
      (transition.measurable_coe hs).sub measurable_const
    have houter : Measurable (fun x =>
        (((1 - ε.1 : NNReal) : ENNReal)⁻¹) *
          (transition x s - (ε.1 : ENNReal) * target s)) :=
      measurable_const.mul hinner
    convert houter using 1
    funext x
    rw [Measure.smul_apply, smul_eq_mul, Measure.sub_apply hs
      (minorization_measure_le transition target ε.1 hminor x),
      Measure.smul_apply, smul_eq_mul]

instance minorizationResidual.instIsMarkovKernel
    (transition : Kernel α α) [IsMarkovKernel transition]
    (target : Measure α) [IsProbabilityMeasure target]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hminor : UniformlyMinorizes transition ε.1 target) :
    IsMarkovKernel (minorizationResidual transition target ε hε hminor) where
  isProbabilityMeasure x := by
    letI : IsFiniteMeasure ((ε.1 : ENNReal) • target) :=
      target.smul_finite ENNReal.coe_ne_top
    constructor
    change ((↑(1 - ε.1) : ENNReal)⁻¹) *
      ((transition x - (ε.1 : ENNReal) • target) Set.univ) = 1
    rw [Measure.sub_apply MeasurableSet.univ
      (minorization_measure_le transition target ε.1 hminor x),
      Measure.smul_apply, measure_univ, measure_univ, smul_eq_mul]
    simp only [mul_one]
    have hcoe : ((1 - ε.1 : NNReal) : ENNReal) =
        1 - (ε.1 : ENNReal) := ENNReal.coe_sub
    rw [← hcoe]
    have hrpos : 0 < (1 - ε.1 : NNReal) := tsub_pos_iff_lt.mpr hε
    exact ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.mpr hrpos.ne') ENNReal.coe_ne_top

/-- Removing and then restoring the Doeblin component recovers every original
transition row exactly. -/
theorem mixture_minorizationResidual_eq
    (transition : Kernel α α) [IsMarkovKernel transition]
    (target : Measure α) [IsProbabilityMeasure target]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hminor : UniformlyMinorizes transition ε.1 target) :
    Mcmc.Kernel.mixture ε (Kernel.const α target)
      (minorizationResidual transition target ε hε hminor) = transition := by
  letI : IsFiniteMeasure ((ε.1 : ENNReal) • target) :=
    target.smul_finite ENNReal.coe_ne_top
  ext x s hs
  rw [Mcmc.Kernel.mixture_apply, Measure.add_apply, Kernel.const_apply]
  change (ε.1 : ENNReal) * target s +
    ((1 - ε.1 : NNReal) : ENNReal) *
      (((1 - ε.1 : NNReal) : ENNReal)⁻¹ *
        ((transition x - (ε.1 : ENNReal) • target) s)) = transition x s
  rw [Measure.sub_apply hs
    (minorization_measure_le transition target ε.1 hminor x),
    Measure.smul_apply, smul_eq_mul]
  have hrpos : 0 < (1 - ε.1 : NNReal) := tsub_pos_iff_lt.mpr hε
  have hr0 : ((1 - ε.1 : NNReal) : ENNReal) ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr hrpos.ne'
  rw [← mul_assoc, ENNReal.mul_inv_cancel hr0 ENNReal.coe_ne_top, one_mul,
    add_tsub_cancel_of_le
      (hminor x s hs)]

/-- If the original transition preserves the minorized probability measure,
then its normalized residual transition preserves it as well. -/
theorem minorizationResidual_invariant
    (transition : Kernel α α) [IsMarkovKernel transition]
    (target : Measure α) [IsProbabilityMeasure target]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hminor : UniformlyMinorizes transition ε.1 target)
    (hinvariant : transition.Invariant target) :
    (minorizationResidual transition target ε hε hminor).Invariant target := by
  let residual := minorizationResidual transition target ε hε hminor
  have hmixture : (Mcmc.Kernel.mixture ε (Kernel.const α target) residual).Invariant
      target := by
    rw [mixture_minorizationResidual_eq transition target ε hε hminor]
    exact hinvariant
  rw [ProbabilityTheory.Kernel.Invariant] at hmixture ⊢
  rw [mixture_comp_measure, Measure.const_comp, measure_univ, one_smul] at hmixture
  ext s hs
  change (residual ∘ₘ target) s = target s
  have heq := congrArg (fun μ : Measure α => μ s) hmixture
  simp only [Measure.add_apply, Measure.smul_apply, ENNReal.smul_def,
    smul_eq_mul] at heq
  have htargetTop : target s ≠ ∞ := measure_ne_top target s
  have hleftTop : (ε.1 : ENNReal) * target s ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top htargetTop
  have hbase : (ε.1 : ENNReal) * target s +
      ((1 - ε.1 : NNReal) : ENNReal) * target s = target s := by
    rw [← add_mul, ← ENNReal.coe_add, add_tsub_cancel_of_le ε.property.2]
    simp
  have hscaled : ((1 - ε.1 : NNReal) : ENNReal) *
      (residual ∘ₘ target) s =
      ((1 - ε.1 : NNReal) : ENNReal) * target s := by
    apply (ENNReal.add_left_inj hleftTop).mp
    simpa [add_comm] using heq.trans hbase.symm
  have hrpos : 0 < (1 - ε.1 : NNReal) := tsub_pos_iff_lt.mpr hε
  apply (ENNReal.mul_left_inj (ENNReal.coe_ne_zero.mpr hrpos.ne')
    ENNReal.coe_ne_top).mp
  simpa [mul_comm] using hscaled

/-- Evolving any probability law through a minorized transition exposes the
same refresh/residual mixture as the pointwise kernel decomposition. -/
theorem minorized_comp_measure_eq
    (transition : Kernel α α) [IsMarkovKernel transition]
    (target initial : Measure α) [IsProbabilityMeasure target]
    [IsProbabilityMeasure initial]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hminor : UniformlyMinorizes transition ε.1 target) :
    transition ∘ₘ initial =
      (ε.1 : ENNReal) • target + ((1 - ε.1 : NNReal) : ENNReal) •
        (minorizationResidual transition target ε hε hminor ∘ₘ initial) := by
  let residual := minorizationResidual transition target ε hε hminor
  calc
    transition ∘ₘ initial =
        Mcmc.Kernel.mixture ε (Kernel.const α target) residual ∘ₘ initial := by
      exact congrArg (fun k : Kernel α α => k ∘ₘ initial)
        (mixture_minorizationResidual_eq transition target ε hε hminor).symm
    _ = (ε.1 : ENNReal) • target +
        ((1 - ε.1 : NNReal) : ENNReal) • (residual ∘ₘ initial) := by
      rw [mixture_comp_measure, Measure.const_comp, measure_univ, one_smul]
      ext s hs
      simp only [Measure.add_apply, Measure.smul_apply]
      rfl

/-- Exact regenerative representation of every finite-time law.  Its first
coefficient is the probability that at least one refresh has occurred; the
second is the probability of taking only residual branches. -/
theorem lawAtTime_eq_refresh_add_residual
    (transition : Kernel α α) [IsMarkovKernel transition]
    (target initial : Measure α) [IsProbabilityMeasure target]
    [IsProbabilityMeasure initial]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hminor : UniformlyMinorizes transition ε.1 target)
    (hinvariant : transition.Invariant target) (n : ℕ) :
    lawAtTime initial transition n =
      ((1 - (1 - ε.1) ^ n : NNReal) : ENNReal) • target +
        (((1 - ε.1) ^ n : NNReal) : ENNReal) •
          lawAtTime initial
            (minorizationResidual transition target ε hε hminor) n := by
  let residual := minorizationResidual transition target ε hε hminor
  have hresidual : residual.Invariant target :=
    minorizationResidual_invariant transition target ε hε hminor hinvariant
  induction n with
  | zero => simp [lawAtTime_zero]
  | succ n ih =>
      rw [lawAtTime_succ,
        minorized_comp_measure_eq transition target
          (lawAtTime initial transition n) ε hε hminor,
        ih, Measure.comp_add]
      simp_rw [Measure.comp_smul]
      rw [hresidual.def, ← lawAtTime_succ]
      simp only [pow_succ]
      let r : NNReal := 1 - ε.1
      have hrle : r ≤ 1 := by simp [r]
      have hrpowle : r ^ n ≤ 1 := pow_le_one₀ (by positivity) hrle
      have hrprodle : r ^ n * r ≤ 1 := by
        exact mul_le_one₀ hrpowle (by positivity) hrle
      have hsum : ε.1 + r = 1 := by
        simp [r, add_tsub_cancel_of_le ε.property.2]
      have hcoef : ε.1 + r * (1 - r ^ n) = 1 - r ^ n * r := by
        apply NNReal.eq
        have hsumR := congrArg (fun z : NNReal => (z : ℝ)) hsum
        norm_num at hsumR
        simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_sub hrpowle,
          NNReal.coe_sub hrprodle, NNReal.coe_one]
        nlinarith
      ext s hs
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      change (ε.1 : ENNReal) * target s + (r : ENNReal) *
          (((1 - r ^ n : NNReal) : ENNReal) * target s +
            ((r ^ n : NNReal) : ENNReal) *
              lawAtTime initial residual (n + 1) s) =
        ((1 - r ^ n * r : NNReal) : ENNReal) * target s +
          ((r ^ n * r : NNReal) : ENNReal) *
            lawAtTime initial residual (n + 1) s
      rw [mul_add, ← mul_assoc, ← mul_assoc, ← ENNReal.coe_mul,
        ← ENNReal.coe_mul, ← add_assoc, ← add_mul, ← ENNReal.coe_add,
        hcoef]
      simp [mul_comm]

/-- The regenerative representation gives the upper half of an eventwise
total-variation bound with geometric remainder `(1-ε)^n`. -/
theorem lawAtTime_apply_le_target_add_geometric
    (transition : Kernel α α) [IsMarkovKernel transition]
    (target initial : Measure α) [IsProbabilityMeasure target]
    [IsProbabilityMeasure initial]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hminor : UniformlyMinorizes transition ε.1 target)
    (hinvariant : transition.Invariant target) (n : ℕ)
    {s : Set α} (_hs : MeasurableSet s) :
    lawAtTime initial transition n s ≤
      target s + (((1 - ε.1) ^ n : NNReal) : ENNReal) := by
  rw [lawAtTime_eq_refresh_add_residual transition target initial ε hε
    hminor hinvariant n, Measure.add_apply, Measure.smul_apply,
    Measure.smul_apply]
  let r : NNReal := (1 - ε.1) ^ n
  have hrle : r ≤ 1 := pow_le_one₀ (by positivity) (by simp)
  have hresidual : lawAtTime initial
      (minorizationResidual transition target ε hε hminor) n s ≤ 1 := by
    calc
      _ ≤ lawAtTime initial
          (minorizationResidual transition target ε hε hminor) n Set.univ :=
        measure_mono (Set.subset_univ s)
      _ = 1 := measure_univ
  change ((1 - r : NNReal) : ENNReal) * target s + (r : ENNReal) * _ ≤
    target s + (r : ENNReal)
  calc
    _ ≤ 1 * target s + (r : ENNReal) * 1 := by
      gcongr
      exact_mod_cast (show 1 - r ≤ 1 from tsub_le_self)
    _ = target s + (r : ENNReal) := by simp

/-- The symmetric half of the eventwise geometric bound. -/
theorem target_apply_le_lawAtTime_add_geometric
    (transition : Kernel α α) [IsMarkovKernel transition]
    (target initial : Measure α) [IsProbabilityMeasure target]
    [IsProbabilityMeasure initial]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hminor : UniformlyMinorizes transition ε.1 target)
    (hinvariant : transition.Invariant target) (n : ℕ)
    {s : Set α} (_hs : MeasurableSet s) :
    target s ≤ lawAtTime initial transition n s +
      (((1 - ε.1) ^ n : NNReal) : ENNReal) := by
  rw [lawAtTime_eq_refresh_add_residual transition target initial ε hε
    hminor hinvariant n, Measure.add_apply, Measure.smul_apply,
    Measure.smul_apply]
  let r : NNReal := (1 - ε.1) ^ n
  have hrle : r ≤ 1 := pow_le_one₀ (by positivity) (by simp)
  have hsplit : ((1 - r : NNReal) : ENNReal) * target s +
      (r : ENNReal) * target s = target s := by
    rw [← add_mul, ← ENNReal.coe_add, tsub_add_cancel_of_le hrle]
    simp
  calc
    target s = ((1 - r : NNReal) : ENNReal) * target s +
        (r : ENNReal) * target s := hsplit.symm
    _ ≤ (((1 - r : NNReal) : ENNReal) * target s +
          (r : ENNReal) * lawAtTime initial
            (minorizationResidual transition target ε hε hminor) n s) + r := by
      have hb : (r : ENNReal) * target s ≤ (r : ENNReal) := by
        have ht : target s ≤ (1 : ENNReal) := calc
          target s ≤ target Set.univ := measure_mono (Set.subset_univ s)
          _ = 1 := measure_univ
        calc
          (r : ENNReal) * target s ≤ r * 1 :=
            mul_le_mul_right ht (r : ENNReal)
          _ = r := mul_one _
      calc
        _ ≤ ((1 - r : NNReal) : ENNReal) * target s + r :=
          add_le_add_right hb _
        _ ≤ (((1 - r : NNReal) : ENNReal) * target s +
              (r : ENNReal) * lawAtTime initial
                (minorizationResidual transition target ε hε hminor) n s) + r := by
          gcongr
          exact le_add_right le_rfl

/-- A coupling certificate giving a uniform geometric off-diagonal bound for
all finite iterates. -/
structure HasGeometricCoupling
    (transition : Kernel α α) (rate : ENNReal) where
  coupled : Kernel (α × α) (α × α)
  isCoupling : IsCoupling coupled transition transition
  offDiagonal_le : ∀ n x,
    (coupled ^ n) x (Set.diagonal α)ᶜ ≤ rate ^ n

/-- A geometric coupling yields an explicit eventwise convergence bound
between chains started from arbitrary states. This is a quantitative
general-state conclusion, strictly stronger than invariance. -/
theorem HasGeometricCoupling.pow_apply_le_add
    {transition : Kernel α α} {rate : ENNReal}
    (h : HasGeometricCoupling transition rate)
    (n : ℕ) (x y : α) {s : Set α} (hs : MeasurableSet s) :
    (transition ^ n) x s ≤ (transition ^ n) y s + rate ^ n := by
  have hc := pow_isCoupling h.coupled transition transition h.isCoupling n
  have hm : IsMeasureCoupling ((h.coupled ^ n) (x, y))
      ((transition ^ n) x) ((transition ^ n) y) := by
    exact ⟨hc.fst_apply (x, y), hc.snd_apply (x, y)⟩
  apply (hm.fst_apply_le_snd_apply_add_compl_diagonal hs).trans
  gcongr
  exact h.offDiagonal_le n (x, y)

/-- The symmetric eventwise form follows by exchanging the initial states. -/
theorem HasGeometricCoupling.pow_apply_le_add_symm
    {transition : Kernel α α} {rate : ENNReal}
    (h : HasGeometricCoupling transition rate)
    (n : ℕ) (x y : α) {s : Set α} (hs : MeasurableSet s) :
    (transition ^ n) y s ≤ (transition ^ n) x s + rate ^ n :=
  h.pow_apply_le_add n y x hs

section StationaryTarget

variable [MeasurableEq α]

/-- A uniform geometric coupling also couples a point-started chain to a
stationary target-started chain. Its off-diagonal mass keeps the same bound. -/
theorem HasGeometricCoupling.exists_stationaryCoupling
    {transition : Kernel α α} [IsMarkovKernel transition]
    {rate : ENNReal} (h : HasGeometricCoupling transition rate)
    (target : Measure α) [IsProbabilityMeasure target]
    (hinvariant : transition.Invariant target) (x : α) (n : ℕ) :
    ∃ ρ : Measure (α × α),
      IsMeasureCoupling ρ (lawAtTime (Measure.dirac x) transition n) target ∧
        ρ (Set.diagonal α)ᶜ ≤ rate ^ n := by
  let initial : Measure (α × α) := (Measure.dirac x).prod target
  let ρ := lawAtTime initial h.coupled n
  have hinitial : IsMeasureCoupling initial (Measure.dirac x) target :=
    isMeasureCoupling_prod _ _
  have hmarginals := lawAtTime_isMeasureCoupling initial
    (Measure.dirac x) target h.coupled transition transition hinitial
    h.isCoupling n
  have htarget : lawAtTime target transition n = target :=
    lawAtTime_eq_of_invariant target transition hinvariant n
  refine ⟨ρ, ?_, ?_⟩
  · simpa [ρ, htarget] using hmarginals
  · change lawAtTime initial h.coupled n (Set.diagonal α)ᶜ ≤ rate ^ n
    rw [lawAtTime, Measure.bind_apply measurableSet_diagonal.compl
      (h.coupled ^ n).aemeasurable]
    calc
      (∫⁻ z, (h.coupled ^ n) z (Set.diagonal α)ᶜ ∂initial) ≤
          ∫⁻ _z, rate ^ n ∂initial := by
        apply lintegral_mono
        intro z
        exact h.offDiagonal_le n z
      _ = rate ^ n := by simp [initial]

/-- Quantitative eventwise marginal convergence from any Dirac start to an
invariant probability target. This is a convergence statement, not merely
stationarity. -/
theorem HasGeometricCoupling.lawAtTime_dirac_apply_le_target_add
    {transition : Kernel α α} [IsMarkovKernel transition]
    {rate : ENNReal} (h : HasGeometricCoupling transition rate)
    (target : Measure α) [IsProbabilityMeasure target]
    (hinvariant : transition.Invariant target) (x : α) (n : ℕ)
    {s : Set α} (hs : MeasurableSet s) :
    lawAtTime (Measure.dirac x) transition n s ≤ target s + rate ^ n := by
  obtain ⟨ρ, hρ, hoff⟩ :=
    h.exists_stationaryCoupling target hinvariant x n
  exact (hρ.fst_apply_le_snd_apply_add_compl_diagonal hs).trans
    (add_le_add_right hoff _)

theorem HasGeometricCoupling.target_apply_le_lawAtTime_dirac_add
    {transition : Kernel α α} [IsMarkovKernel transition]
    {rate : ENNReal} (h : HasGeometricCoupling transition rate)
    (target : Measure α) [IsProbabilityMeasure target]
    (hinvariant : transition.Invariant target) (x : α) (n : ℕ)
    {s : Set α} (hs : MeasurableSet s) :
    target s ≤ lawAtTime (Measure.dirac x) transition n s + rate ^ n := by
  obtain ⟨ρ, hρ, hoff⟩ :=
    h.exists_stationaryCoupling target hinvariant x n
  exact (hρ.snd_apply_le_fst_apply_add_compl_diagonal hs).trans
    (add_le_add_right hoff _)

end StationaryTarget

end Kernel
end Mcmc
