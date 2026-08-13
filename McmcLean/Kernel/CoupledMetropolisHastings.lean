import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Mathlib.Probability.Kernel.Composition.CompProd
import McmcLean.Kernel.Coupling
import McmcLean.Kernel.DensityCoupling
import McmcLean.Kernel.MetropolisHastings

/-!
# Coupled Metropolis--Hastings accept/reject step

This module formalizes the shared-uniform accept/reject mechanism used by
coupled Metropolis--Hastings kernels. Given two acceptance probabilities `a`
and `b`, one shared uniform variable yields four branches: both accept, only
the left accepts, only the right accepts, or both reject. Their masses are
`min a b`, `a - min a b`, `b - min a b`, and `1 - max a b`.

The construction below produces the resulting joint next-state measure from
an arbitrary coupled proposal measure. It is normalized, and both coordinate
marginals are proved to be exactly the existing single-chain
`metropolisHastings` transition rows. The pointwise construction is then
packaged as a measurable Markov kernel, with exact marginal-kernel theorems.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace McmcLean.Kernel

section DependentMap

open ProbabilityTheory

variable {Input Output Result : Type*}
  [MeasurableSpace Input] [MeasurableSpace Output] [MeasurableSpace Result]

/-- Push a kernel output through a measurable map which may also depend on the
kernel input. This is the kernel-level counterpart of mapping each row by a
different measurable function. -/
noncomputable def dependentMap
    (kernel : ProbabilityTheory.Kernel Input Output)
    [IsSFiniteKernel kernel]
    (f : Input → Output → Result)
    (hf : Measurable (Function.uncurry f)) :
    ProbabilityTheory.Kernel Input Result :=
  (kernel ⊗ₖ ProbabilityTheory.Kernel.deterministic
      (Function.uncurry f) hf).snd

/-- A row of `dependentMap` is the pushforward of the original row by the map
at that input. -/
theorem dependentMap_apply
    (kernel : ProbabilityTheory.Kernel Input Output)
    [IsSFiniteKernel kernel]
    (f : Input → Output → Result)
    (hf : Measurable (Function.uncurry f)) (x : Input) :
    dependentMap kernel f hf x = (kernel x).map (f x) := by
  ext s hs
  rw [dependentMap, ProbabilityTheory.Kernel.snd_apply' _ _ hs,
    ProbabilityTheory.Kernel.compProd_apply (measurable_snd hs)]
  rw [Measure.map_apply (Measurable.of_uncurry_left hf) hs]
  have hpre (y : Output) : Prod.mk y ⁻¹' (Prod.snd ⁻¹' s) = s := by
    ext z
    rfl
  simp_rw [hpre, ProbabilityTheory.Kernel.deterministic_apply' hf _ hs]
  rw [← lintegral_indicator_one
    (hs.preimage (Measurable.of_uncurry_left hf))]
  apply lintegral_congr
  intro y
  by_cases hy : f x y ∈ s <;> simp [hy]

end DependentMap

/-- Shared-uniform mass on which both chains accept. -/
def bothAcceptWeight (a b : ENNReal) : ENNReal := min a b

/-- Shared-uniform mass on which only the left chain accepts. -/
def leftOnlyAcceptWeight (a b : ENNReal) : ENNReal := a - min a b

/-- Shared-uniform mass on which only the right chain accepts. -/
def rightOnlyAcceptWeight (a b : ENNReal) : ENNReal := b - min a b

/-- Shared-uniform mass on which both chains reject. -/
def bothRejectWeight (a b : ENNReal) : ENNReal := 1 - max a b

theorem bothAccept_add_leftOnly (a b : ENNReal) :
    bothAcceptWeight a b + leftOnlyAcceptWeight a b = a := by
  rw [bothAcceptWeight, leftOnlyAcceptWeight, add_comm,
    tsub_add_cancel_of_le (min_le_left a b)]

theorem bothAccept_add_rightOnly (a b : ENNReal) :
    bothAcceptWeight a b + rightOnlyAcceptWeight a b = b := by
  rw [bothAcceptWeight, rightOnlyAcceptWeight, add_comm,
    tsub_add_cancel_of_le (min_le_right a b)]

theorem rightOnly_add_bothReject (a b : ENNReal)
    (_ha : a ≤ 1) (hb : b ≤ 1) :
    rightOnlyAcceptWeight a b + bothRejectWeight a b = 1 - a := by
  rcases le_total a b with hab | hba
  · rw [rightOnlyAcceptWeight, bothRejectWeight, min_eq_left hab,
      max_eq_right hab]
    simpa only [add_comm] using tsub_add_tsub_cancel hb hab
  · rw [rightOnlyAcceptWeight, bothRejectWeight, min_eq_right hba,
      max_eq_left hba, tsub_self, zero_add]

theorem leftOnly_add_bothReject (a b : ENNReal)
    (ha : a ≤ 1) (_hb : b ≤ 1) :
    leftOnlyAcceptWeight a b + bothRejectWeight a b = 1 - b := by
  rcases le_total a b with hab | hba
  · rw [leftOnlyAcceptWeight, bothRejectWeight, min_eq_left hab,
      max_eq_right hab, tsub_self, zero_add]
  · rw [leftOnlyAcceptWeight, bothRejectWeight, min_eq_right hba,
      max_eq_left hba]
    simpa only [add_comm] using tsub_add_tsub_cancel ha hba

/-- The four shared-uniform branches partition unit mass. -/
theorem acceptRejectWeights_sum (a b : ENNReal)
    (ha : a ≤ 1) (hb : b ≤ 1) :
    bothAcceptWeight a b + leftOnlyAcceptWeight a b +
      rightOnlyAcceptWeight a b + bothRejectWeight a b = 1 := by
  calc
    bothAcceptWeight a b + leftOnlyAcceptWeight a b +
        rightOnlyAcceptWeight a b + bothRejectWeight a b =
        a + (rightOnlyAcceptWeight a b + bothRejectWeight a b) := by
          rw [bothAccept_add_leftOnly, add_assoc]
    _ = a + (1 - a) := by rw [rightOnly_add_bothReject a b ha hb]
    _ = 1 := by simpa only [add_comm] using tsub_add_cancel_of_le ha

section MeasureStep

variable {State : Type*} [MeasurableSpace State]

/-- Integrating a function of the first coordinate of a coupling is the same
as integrating it against the first marginal. -/
theorem lintegral_fst_eq_of_isMeasureCoupling
    {proposal : Measure (State × State)} {left right : Measure State}
    (hproposal : IsMeasureCoupling proposal left right)
    {f : State → ENNReal} (hf : Measurable f) :
    (∫⁻ z, f z.1 ∂proposal) = ∫⁻ x, f x ∂left := by
  rw [← hproposal.fst, Measure.fst, lintegral_map hf measurable_fst]

/-- Restricted first-coordinate integrals can likewise be evaluated against
the first marginal. -/
theorem setLIntegral_fst_preimage_eq_of_isMeasureCoupling
    {proposal : Measure (State × State)} {left right : Measure State}
    (hproposal : IsMeasureCoupling proposal left right)
    {f : State → ENNReal} (hf : Measurable f)
    {s : Set State} (hs : MeasurableSet s) :
    (∫⁻ z in Prod.fst ⁻¹' s, f z.1 ∂proposal) =
      ∫⁻ x in s, f x ∂left := by
  rw [← hproposal.fst, Measure.fst]
  rw [← lintegral_indicator (measurable_fst hs),
    ← lintegral_indicator hs, lintegral_map (hf.indicator hs) measurable_fst]
  rfl

/-- Integrating a function of the second coordinate of a coupling is the same
as integrating it against the second marginal. -/
theorem lintegral_snd_eq_of_isMeasureCoupling
    {proposal : Measure (State × State)} {left right : Measure State}
    (hproposal : IsMeasureCoupling proposal left right)
    {f : State → ENNReal} (hf : Measurable f) :
    (∫⁻ z, f z.2 ∂proposal) = ∫⁻ y, f y ∂right := by
  rw [← hproposal.snd, Measure.snd, lintegral_map hf measurable_snd]

/-- Restricted second-coordinate integrals can likewise be evaluated against
the second marginal. -/
theorem setLIntegral_snd_preimage_eq_of_isMeasureCoupling
    {proposal : Measure (State × State)} {left right : Measure State}
    (hproposal : IsMeasureCoupling proposal left right)
    {f : State → ENNReal} (hf : Measurable f)
    {s : Set State} (hs : MeasurableSet s) :
    (∫⁻ z in Prod.snd ⁻¹' s, f z.2 ∂proposal) =
      ∫⁻ y in s, f y ∂right := by
  rw [← hproposal.snd, Measure.snd]
  rw [← lintegral_indicator (measurable_snd hs),
    ← lintegral_indicator hs, lintegral_map (hf.indicator hs) measurable_snd]
  rfl

/-- Acceptance probability of the left proposal at a current/proposed pair. -/
def coupledLeftAcceptance (accept : State → State → ENNReal)
    (current proposal : State × State) : ENNReal :=
  accept current.1 proposal.1

/-- Acceptance probability of the right proposal. -/
def coupledRightAcceptance (accept : State → State → ENNReal)
    (current proposal : State × State) : ENNReal :=
  accept current.2 proposal.2

theorem measurable_coupledLeftAcceptance
    {accept : State → State → ENNReal}
    (haccept : Measurable (Function.uncurry accept)) (current : State × State) :
    Measurable (coupledLeftAcceptance accept current) := by
  exact haccept.comp (measurable_const.prodMk measurable_fst)

theorem measurable_coupledRightAcceptance
    {accept : State → State → ENNReal}
    (haccept : Measurable (Function.uncurry accept)) (current : State × State) :
    Measurable (coupledRightAcceptance accept current) := by
  exact haccept.comp (measurable_const.prodMk measurable_snd)

/-- Joint next-state law obtained by applying one shared-uniform accept/reject
decision to a coupled proposal law. -/
noncomputable def coupledAcceptRejectMeasure
    (current : State × State) (proposal : Measure (State × State))
    (accept : State → State → ENNReal) : Measure (State × State) :=
  (proposal.withDensity fun z => bothAcceptWeight
      (coupledLeftAcceptance accept current z)
      (coupledRightAcceptance accept current z)).map id +
  (proposal.withDensity fun z => leftOnlyAcceptWeight
      (coupledLeftAcceptance accept current z)
      (coupledRightAcceptance accept current z)).map
        (fun z => (z.1, current.2)) +
  (proposal.withDensity fun z => rightOnlyAcceptWeight
      (coupledLeftAcceptance accept current z)
      (coupledRightAcceptance accept current z)).map
        (fun z => (current.1, z.2)) +
  (proposal.withDensity fun z => bothRejectWeight
      (coupledLeftAcceptance accept current z)
      (coupledRightAcceptance accept current z)).map
        (Function.const (State × State) current)

theorem measurable_bothAcceptWeight_comp
    {accept : State → State → ENNReal}
    (haccept : Measurable (Function.uncurry accept)) (current : State × State) :
    Measurable fun z => bothAcceptWeight
      (coupledLeftAcceptance accept current z)
      (coupledRightAcceptance accept current z) := by
  exact (measurable_coupledLeftAcceptance haccept current).min
    (measurable_coupledRightAcceptance haccept current)

theorem measurable_leftOnlyAcceptWeight_comp
    {accept : State → State → ENNReal}
    (haccept : Measurable (Function.uncurry accept)) (current : State × State) :
    Measurable fun z => leftOnlyAcceptWeight
      (coupledLeftAcceptance accept current z)
      (coupledRightAcceptance accept current z) := by
  exact (measurable_coupledLeftAcceptance haccept current).sub
    (measurable_bothAcceptWeight_comp haccept current)

theorem measurable_rightOnlyAcceptWeight_comp
    {accept : State → State → ENNReal}
    (haccept : Measurable (Function.uncurry accept)) (current : State × State) :
    Measurable fun z => rightOnlyAcceptWeight
      (coupledLeftAcceptance accept current z)
      (coupledRightAcceptance accept current z) := by
  exact (measurable_coupledRightAcceptance haccept current).sub
    (measurable_bothAcceptWeight_comp haccept current)

theorem measurable_bothRejectWeight_comp
    {accept : State → State → ENNReal}
    (haccept : Measurable (Function.uncurry accept)) (current : State × State) :
    Measurable fun z => bothRejectWeight
      (coupledLeftAcceptance accept current z)
      (coupledRightAcceptance accept current z) := by
  exact measurable_const.sub
    ((measurable_coupledLeftAcceptance haccept current).max
      (measurable_coupledRightAcceptance haccept current))

omit [MeasurableSpace State] in
/-- The branches in which the left chain accepts have total mass equal to
its own acceptance probability. -/
theorem leftAcceptance_branch_sum
    (accept : State → State → ENNReal) (current proposal : State × State) :
    bothAcceptWeight
        (coupledLeftAcceptance accept current proposal)
        (coupledRightAcceptance accept current proposal) +
      leftOnlyAcceptWeight
        (coupledLeftAcceptance accept current proposal)
        (coupledRightAcceptance accept current proposal) =
      coupledLeftAcceptance accept current proposal :=
  bothAccept_add_leftOnly _ _

omit [MeasurableSpace State] in
/-- The branches in which the right chain accepts have total mass equal to
its own acceptance probability. -/
theorem rightAcceptance_branch_sum
    (accept : State → State → ENNReal) (current proposal : State × State) :
    bothAcceptWeight
        (coupledLeftAcceptance accept current proposal)
        (coupledRightAcceptance accept current proposal) +
      rightOnlyAcceptWeight
        (coupledLeftAcceptance accept current proposal)
        (coupledRightAcceptance accept current proposal) =
      coupledRightAcceptance accept current proposal :=
  bothAccept_add_rightOnly _ _

omit [MeasurableSpace State] in
/-- The branches in which the left chain rejects have the complementary
mass to its own acceptance probability. -/
theorem leftRejection_branch_sum
    (accept : State → State → ENNReal) (current proposal : State × State)
    (hle : ∀ x y, accept x y ≤ 1) :
    rightOnlyAcceptWeight
        (coupledLeftAcceptance accept current proposal)
        (coupledRightAcceptance accept current proposal) +
      bothRejectWeight
        (coupledLeftAcceptance accept current proposal)
        (coupledRightAcceptance accept current proposal) =
      1 - coupledLeftAcceptance accept current proposal := by
  exact rightOnly_add_bothReject _ _
    (hle current.1 proposal.1) (hle current.2 proposal.2)

omit [MeasurableSpace State] in
/-- The branches in which the right chain rejects have the complementary
mass to its own acceptance probability. -/
theorem rightRejection_branch_sum
    (accept : State → State → ENNReal) (current proposal : State × State)
    (hle : ∀ x y, accept x y ≤ 1) :
    leftOnlyAcceptWeight
        (coupledLeftAcceptance accept current proposal)
        (coupledRightAcceptance accept current proposal) +
      bothRejectWeight
        (coupledLeftAcceptance accept current proposal)
        (coupledRightAcceptance accept current proposal) =
      1 - coupledRightAcceptance accept current proposal := by
  exact leftOnly_add_bothReject _ _
    (hle current.1 proposal.1) (hle current.2 proposal.2)

/-- The coupled shared-uniform accept/reject construction is a probability
measure whenever the proposal is a probability measure and both acceptance
probabilities are bounded by one. -/
theorem coupledAcceptRejectMeasure_isProbability
    (current : State × State) (proposal : Measure (State × State))
    [IsProbabilityMeasure proposal]
    {accept : State → State → ENNReal}
    (haccept : Measurable (Function.uncurry accept))
    (hle : ∀ x y, accept x y ≤ 1) :
    IsProbabilityMeasure (coupledAcceptRejectMeasure current proposal accept) := by
  constructor
  rw [coupledAcceptRejectMeasure]
  rw [Measure.add_apply, Measure.add_apply, Measure.add_apply,
    Measure.map_apply measurable_id MeasurableSet.univ,
    Measure.map_apply (measurable_fst.prodMk measurable_const) MeasurableSet.univ,
    Measure.map_apply (measurable_const.prodMk measurable_snd) MeasurableSet.univ,
    Measure.map_apply
      (show Measurable (Function.const (State × State) current) from measurable_const)
      MeasurableSet.univ]
  simp only [Set.preimage_univ]
  rw [withDensity_apply _ MeasurableSet.univ,
    withDensity_apply _ MeasurableSet.univ,
    withDensity_apply _ MeasurableSet.univ,
    withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← lintegral_add_left (measurable_bothAcceptWeight_comp haccept current)]
  rw [add_assoc]
  rw [← lintegral_add_left (measurable_rightOnlyAcceptWeight_comp haccept current)]
  have hleft : Measurable fun z => bothAcceptWeight
      (coupledLeftAcceptance accept current z)
      (coupledRightAcceptance accept current z) +
    leftOnlyAcceptWeight
      (coupledLeftAcceptance accept current z)
      (coupledRightAcceptance accept current z) :=
    (measurable_bothAcceptWeight_comp haccept current).add
      (measurable_leftOnlyAcceptWeight_comp haccept current)
  rw [← lintegral_add_left hleft]
  convert lintegral_const (μ := proposal) (1 : ENNReal) using 1
  · apply lintegral_congr
    intro z
    simpa only [add_assoc, coupledLeftAcceptance, coupledRightAcceptance] using
      acceptRejectWeights_sum _ _ (hle current.1 z.1) (hle current.2 z.2)
  · simp

/-- The first marginal of the shared-uniform construction is exactly the
ordinary Metropolis--Hastings transition of the first chain. -/
theorem coupledAcceptRejectMeasure_fst
    (Q : ProbabilityTheory.Kernel State State)
    [ProbabilityTheory.IsMarkovKernel Q]
    (current : State × State) (proposal : Measure (State × State))
    {accept : State → State → ENNReal}
    (hproposal : IsMeasureCoupling proposal (Q current.1) (Q current.2))
    (haccept : Measurable (Function.uncurry accept))
    (hle : ∀ x y, accept x y ≤ 1) :
    (coupledAcceptRejectMeasure current proposal accept).fst =
      metropolisHastings Q accept current.1 := by
  classical
  letI : IsProbabilityMeasure proposal := hproposal.isProbabilityMeasure
  have hleftMeas : Measurable (coupledLeftAcceptance accept current) :=
    measurable_coupledLeftAcceptance haccept current
  have hleftIntegral :
      (∫⁻ z, coupledLeftAcceptance accept current z ∂proposal) =
        acceptanceMass Q accept current.1 := by
    rw [acceptanceMass]
    simpa only [coupledLeftAcceptance] using
      lintegral_fst_eq_of_isMeasureCoupling hproposal
        (Measurable.of_uncurry_left haccept)
  have hleftIntegral_ne_top :
      (∫⁻ z, coupledLeftAcceptance accept current z ∂proposal) ≠ ∞ := by
    rw [hleftIntegral]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top
      (acceptanceMass_le_one Q hle current.1)
  have hrejected :
      (∫⁻ z, rightOnlyAcceptWeight
          (coupledLeftAcceptance accept current z)
          (coupledRightAcceptance accept current z) ∂proposal) +
        (∫⁻ z, bothRejectWeight
          (coupledLeftAcceptance accept current z)
          (coupledRightAcceptance accept current z) ∂proposal) =
        rejectionProbability Q accept current.1 := by
    rw [← lintegral_add_left
      (measurable_rightOnlyAcceptWeight_comp haccept current)]
    calc
      (∫⁻ z, rightOnlyAcceptWeight
            (coupledLeftAcceptance accept current z)
            (coupledRightAcceptance accept current z) +
          bothRejectWeight
            (coupledLeftAcceptance accept current z)
            (coupledRightAcceptance accept current z) ∂proposal) =
          ∫⁻ z, 1 - coupledLeftAcceptance accept current z ∂proposal := by
            apply lintegral_congr
            intro z
            exact leftRejection_branch_sum accept current z hle
      _ = 1 - ∫⁻ z, coupledLeftAcceptance accept current z ∂proposal := by
        rw [lintegral_sub hleftMeas hleftIntegral_ne_top
          (ae_of_all proposal fun z => hle current.1 z.1)]
        simp
      _ = rejectionProbability Q accept current.1 := by
        rw [rejectionProbability, hleftIntegral]
  ext s hs
  rw [Measure.fst_apply hs, metropolisHastings_apply Q haccept current.1 hs]
  rw [coupledAcceptRejectMeasure, Measure.add_apply, Measure.add_apply,
    Measure.add_apply]
  rw [Measure.map_apply measurable_id (measurable_fst hs),
    Measure.map_apply (measurable_fst.prodMk measurable_const) (measurable_fst hs),
    Measure.map_apply (measurable_const.prodMk measurable_snd) (measurable_fst hs),
    Measure.map_apply
      (show Measurable (Function.const (State × State) current) from measurable_const)
      (measurable_fst hs)]
  by_cases hx : current.1 ∈ s
  · simp only [Set.preimage_preimage, id_eq]
    have hright : ((fun _z : State × State => current.1) ⁻¹' s) = Set.univ := by
      ext z
      simp [hx]
    have hconst :
        ((fun x : State × State => (Function.const (State × State) current x).1) ⁻¹' s) =
          Set.univ := by
      ext z
      simp [hx]
    rw [hright, hconst]
    rw [withDensity_apply _ (measurable_fst hs),
      withDensity_apply _ (measurable_fst hs),
      withDensity_apply _ MeasurableSet.univ,
      withDensity_apply _ MeasurableSet.univ]
    simp only [Measure.restrict_univ]
    simp only [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
    have haccepted :
        (∫⁻ z in Prod.fst ⁻¹' s, bothAcceptWeight
            (coupledLeftAcceptance accept current z)
            (coupledRightAcceptance accept current z) ∂proposal) +
          (∫⁻ z in Prod.fst ⁻¹' s, leftOnlyAcceptWeight
            (coupledLeftAcceptance accept current z)
            (coupledRightAcceptance accept current z) ∂proposal) =
          ∫⁻ y in s, accept current.1 y ∂Q current.1 := by
      rw [← lintegral_add_left
        (measurable_bothAcceptWeight_comp haccept current)]
      calc
        (∫⁻ z in Prod.fst ⁻¹' s, bothAcceptWeight
              (coupledLeftAcceptance accept current z)
              (coupledRightAcceptance accept current z) +
            leftOnlyAcceptWeight
              (coupledLeftAcceptance accept current z)
              (coupledRightAcceptance accept current z) ∂proposal) =
            ∫⁻ z in Prod.fst ⁻¹' s,
              coupledLeftAcceptance accept current z ∂proposal := by
                apply lintegral_congr
                intro z
                exact leftAcceptance_branch_sum accept current z
        _ = ∫⁻ y in s, accept current.1 y ∂Q current.1 := by
          simpa only [coupledLeftAcceptance] using
            setLIntegral_fst_preimage_eq_of_isMeasureCoupling hproposal
              (Measurable.of_uncurry_left haccept) hs
    rw [haccepted, add_assoc, hrejected]
  · simp only [Set.preimage_preimage, id_eq]
    have hright : ((fun _z : State × State => current.1) ⁻¹' s) = ∅ := by
      ext z
      simp [hx]
    have hconst :
        ((fun x : State × State => (Function.const (State × State) current x).1) ⁻¹' s) =
          ∅ := by
      ext z
      simp [hx]
    rw [hright, hconst]
    simp only [measure_empty, add_zero]
    rw [withDensity_apply _ (measurable_fst hs),
      withDensity_apply _ (measurable_fst hs)]
    simp only [Set.indicator_of_notMem hx, mul_zero]
    rw [← lintegral_add_left
      (measurable_bothAcceptWeight_comp haccept current)]
    calc
      (∫⁻ z in Prod.fst ⁻¹' s, bothAcceptWeight
            (coupledLeftAcceptance accept current z)
            (coupledRightAcceptance accept current z) +
          leftOnlyAcceptWeight
            (coupledLeftAcceptance accept current z)
            (coupledRightAcceptance accept current z) ∂proposal) =
          ∫⁻ z in Prod.fst ⁻¹' s,
            coupledLeftAcceptance accept current z ∂proposal := by
              apply lintegral_congr
              intro z
              exact leftAcceptance_branch_sum accept current z
      _ = ∫⁻ y in s, accept current.1 y ∂Q current.1 := by
        simpa only [coupledLeftAcceptance] using
          setLIntegral_fst_preimage_eq_of_isMeasureCoupling hproposal
            (Measurable.of_uncurry_left haccept) hs
    simp

/-- The second marginal of the shared-uniform construction is exactly the
ordinary Metropolis--Hastings transition of the second chain. -/
theorem coupledAcceptRejectMeasure_snd
    (Q : ProbabilityTheory.Kernel State State)
    [ProbabilityTheory.IsMarkovKernel Q]
    (current : State × State) (proposal : Measure (State × State))
    {accept : State → State → ENNReal}
    (hproposal : IsMeasureCoupling proposal (Q current.1) (Q current.2))
    (haccept : Measurable (Function.uncurry accept))
    (hle : ∀ x y, accept x y ≤ 1) :
    (coupledAcceptRejectMeasure current proposal accept).snd =
      metropolisHastings Q accept current.2 := by
  classical
  letI : IsProbabilityMeasure proposal := hproposal.isProbabilityMeasure
  have hrightMeas : Measurable (coupledRightAcceptance accept current) :=
    measurable_coupledRightAcceptance haccept current
  have hrightIntegral :
      (∫⁻ z, coupledRightAcceptance accept current z ∂proposal) =
        acceptanceMass Q accept current.2 := by
    rw [acceptanceMass]
    simpa only [coupledRightAcceptance] using
      lintegral_snd_eq_of_isMeasureCoupling hproposal
        (Measurable.of_uncurry_left haccept)
  have hrightIntegral_ne_top :
      (∫⁻ z, coupledRightAcceptance accept current z ∂proposal) ≠ ∞ := by
    rw [hrightIntegral]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top
      (acceptanceMass_le_one Q hle current.2)
  have hrejected :
      (∫⁻ z, leftOnlyAcceptWeight
          (coupledLeftAcceptance accept current z)
          (coupledRightAcceptance accept current z) ∂proposal) +
        (∫⁻ z, bothRejectWeight
          (coupledLeftAcceptance accept current z)
          (coupledRightAcceptance accept current z) ∂proposal) =
        rejectionProbability Q accept current.2 := by
    rw [← lintegral_add_left
      (measurable_leftOnlyAcceptWeight_comp haccept current)]
    calc
      (∫⁻ z, leftOnlyAcceptWeight
            (coupledLeftAcceptance accept current z)
            (coupledRightAcceptance accept current z) +
          bothRejectWeight
            (coupledLeftAcceptance accept current z)
            (coupledRightAcceptance accept current z) ∂proposal) =
          ∫⁻ z, 1 - coupledRightAcceptance accept current z ∂proposal := by
            apply lintegral_congr
            intro z
            exact rightRejection_branch_sum accept current z hle
      _ = 1 - ∫⁻ z, coupledRightAcceptance accept current z ∂proposal := by
        rw [lintegral_sub hrightMeas hrightIntegral_ne_top
          (ae_of_all proposal fun z => hle current.2 z.2)]
        simp
      _ = rejectionProbability Q accept current.2 := by
        rw [rejectionProbability, hrightIntegral]
  ext s hs
  rw [Measure.snd_apply hs, metropolisHastings_apply Q haccept current.2 hs]
  rw [coupledAcceptRejectMeasure, Measure.add_apply, Measure.add_apply,
    Measure.add_apply]
  rw [Measure.map_apply measurable_id (measurable_snd hs),
    Measure.map_apply (measurable_fst.prodMk measurable_const) (measurable_snd hs),
    Measure.map_apply (measurable_const.prodMk measurable_snd) (measurable_snd hs),
    Measure.map_apply
      (show Measurable (Function.const (State × State) current) from measurable_const)
      (measurable_snd hs)]
  by_cases hx : current.2 ∈ s
  · simp only [Set.preimage_preimage, id_eq]
    have hleft : ((fun _z : State × State => current.2) ⁻¹' s) = Set.univ := by
      ext z
      simp [hx]
    have hconst :
        ((fun x : State × State => (Function.const (State × State) current x).2) ⁻¹' s) =
          Set.univ := by
      ext z
      simp [hx]
    rw [hleft, hconst]
    rw [withDensity_apply _ (measurable_snd hs),
      withDensity_apply _ MeasurableSet.univ,
      withDensity_apply _ (measurable_snd hs),
      withDensity_apply _ MeasurableSet.univ]
    simp only [Measure.restrict_univ]
    simp only [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
    have haccepted :
        (∫⁻ z in Prod.snd ⁻¹' s, bothAcceptWeight
            (coupledLeftAcceptance accept current z)
            (coupledRightAcceptance accept current z) ∂proposal) +
          (∫⁻ z in Prod.snd ⁻¹' s, rightOnlyAcceptWeight
            (coupledLeftAcceptance accept current z)
            (coupledRightAcceptance accept current z) ∂proposal) =
          ∫⁻ y in s, accept current.2 y ∂Q current.2 := by
      rw [← lintegral_add_left
        (measurable_bothAcceptWeight_comp haccept current)]
      calc
        (∫⁻ z in Prod.snd ⁻¹' s, bothAcceptWeight
              (coupledLeftAcceptance accept current z)
              (coupledRightAcceptance accept current z) +
            rightOnlyAcceptWeight
              (coupledLeftAcceptance accept current z)
              (coupledRightAcceptance accept current z) ∂proposal) =
            ∫⁻ z in Prod.snd ⁻¹' s,
              coupledRightAcceptance accept current z ∂proposal := by
                apply lintegral_congr
                intro z
                exact rightAcceptance_branch_sum accept current z
        _ = ∫⁻ y in s, accept current.2 y ∂Q current.2 := by
          simpa only [coupledRightAcceptance] using
            setLIntegral_snd_preimage_eq_of_isMeasureCoupling hproposal
              (Measurable.of_uncurry_left haccept) hs
    calc
      _ = ((∫⁻ z in Prod.snd ⁻¹' s, bothAcceptWeight
              (coupledLeftAcceptance accept current z)
              (coupledRightAcceptance accept current z) ∂proposal) +
            (∫⁻ z in Prod.snd ⁻¹' s, rightOnlyAcceptWeight
              (coupledLeftAcceptance accept current z)
              (coupledRightAcceptance accept current z) ∂proposal)) +
          ((∫⁻ z, leftOnlyAcceptWeight
              (coupledLeftAcceptance accept current z)
              (coupledRightAcceptance accept current z) ∂proposal) +
            (∫⁻ z, bothRejectWeight
              (coupledLeftAcceptance accept current z)
              (coupledRightAcceptance accept current z) ∂proposal)) := by
                ac_rfl
      _ = _ := by rw [haccepted, hrejected]
  · simp only [Set.preimage_preimage, id_eq]
    have hleft : ((fun _z : State × State => current.2) ⁻¹' s) = ∅ := by
      ext z
      simp [hx]
    have hconst :
        ((fun x : State × State => (Function.const (State × State) current x).2) ⁻¹' s) =
          ∅ := by
      ext z
      simp [hx]
    rw [hleft, hconst]
    simp only [measure_empty, add_zero]
    rw [withDensity_apply _ (measurable_snd hs),
      withDensity_apply _ (measurable_snd hs)]
    simp only [Set.indicator_of_notMem hx, mul_zero]
    rw [← lintegral_add_left
      (measurable_bothAcceptWeight_comp haccept current)]
    calc
      (∫⁻ z in Prod.snd ⁻¹' s, bothAcceptWeight
            (coupledLeftAcceptance accept current z)
            (coupledRightAcceptance accept current z) +
          rightOnlyAcceptWeight
            (coupledLeftAcceptance accept current z)
            (coupledRightAcceptance accept current z) ∂proposal) =
          ∫⁻ z in Prod.snd ⁻¹' s,
            coupledRightAcceptance accept current z ∂proposal := by
              apply lintegral_congr
              intro z
              exact rightAcceptance_branch_sum accept current z
      _ = ∫⁻ y in s, accept current.2 y ∂Q current.2 := by
        simpa only [coupledRightAcceptance] using
          setLIntegral_snd_preimage_eq_of_isMeasureCoupling hproposal
            (Measurable.of_uncurry_left haccept) hs
    simp

/-- The shared-uniform construction is a coupling of the two ordinary
Metropolis--Hastings transition rows. -/
theorem coupledAcceptRejectMeasure_isCoupling
    (Q : ProbabilityTheory.Kernel State State)
    [ProbabilityTheory.IsMarkovKernel Q]
    (current : State × State) (proposal : Measure (State × State))
    {accept : State → State → ENNReal}
    (hproposal : IsMeasureCoupling proposal (Q current.1) (Q current.2))
    (haccept : Measurable (Function.uncurry accept))
    (hle : ∀ x y, accept x y ≤ 1) :
    IsMeasureCoupling (coupledAcceptRejectMeasure current proposal accept)
      (metropolisHastings Q accept current.1)
      (metropolisHastings Q accept current.2) :=
  ⟨coupledAcceptRejectMeasure_fst Q current proposal hproposal haccept hle,
    coupledAcceptRejectMeasure_snd Q current proposal hproposal haccept hle⟩

end MeasureStep

section KernelStep

open ProbabilityTheory

variable {State : Type*} [MeasurableSpace State]

theorem measurable_uncurry_coupledLeftAcceptance
    {accept : State → State → ENNReal}
    (haccept : Measurable (Function.uncurry accept)) :
    Measurable (Function.uncurry (coupledLeftAcceptance accept)) := by
  exact haccept.comp
    ((measurable_fst.comp measurable_fst).prodMk
      (measurable_fst.comp measurable_snd))

theorem measurable_uncurry_coupledRightAcceptance
    {accept : State → State → ENNReal}
    (haccept : Measurable (Function.uncurry accept)) :
    Measurable (Function.uncurry (coupledRightAcceptance accept)) := by
  exact haccept.comp
    ((measurable_snd.comp measurable_fst).prodMk
      (measurable_snd.comp measurable_snd))

/-- Density of the branch in which both chains accept. -/
def coupledBothAcceptWeight (accept : State → State → ENNReal)
    (current proposal : State × State) : ENNReal :=
  bothAcceptWeight (coupledLeftAcceptance accept current proposal)
    (coupledRightAcceptance accept current proposal)

/-- Density of the branch in which only the left chain accepts. -/
def coupledLeftOnlyAcceptWeight (accept : State → State → ENNReal)
    (current proposal : State × State) : ENNReal :=
  leftOnlyAcceptWeight (coupledLeftAcceptance accept current proposal)
    (coupledRightAcceptance accept current proposal)

/-- Density of the branch in which only the right chain accepts. -/
def coupledRightOnlyAcceptWeight (accept : State → State → ENNReal)
    (current proposal : State × State) : ENNReal :=
  rightOnlyAcceptWeight (coupledLeftAcceptance accept current proposal)
    (coupledRightAcceptance accept current proposal)

/-- Density of the branch in which both chains reject. -/
def coupledBothRejectWeight (accept : State → State → ENNReal)
    (current proposal : State × State) : ENNReal :=
  bothRejectWeight (coupledLeftAcceptance accept current proposal)
    (coupledRightAcceptance accept current proposal)

theorem measurable_uncurry_coupledBothAcceptWeight
    {accept : State → State → ENNReal}
    (haccept : Measurable (Function.uncurry accept)) :
    Measurable (Function.uncurry (coupledBothAcceptWeight accept)) := by
  exact (measurable_uncurry_coupledLeftAcceptance haccept).min
    (measurable_uncurry_coupledRightAcceptance haccept)

theorem measurable_uncurry_coupledLeftOnlyAcceptWeight
    {accept : State → State → ENNReal}
    (haccept : Measurable (Function.uncurry accept)) :
    Measurable (Function.uncurry (coupledLeftOnlyAcceptWeight accept)) := by
  exact (measurable_uncurry_coupledLeftAcceptance haccept).sub
    (measurable_uncurry_coupledBothAcceptWeight haccept)

theorem measurable_uncurry_coupledRightOnlyAcceptWeight
    {accept : State → State → ENNReal}
    (haccept : Measurable (Function.uncurry accept)) :
    Measurable (Function.uncurry (coupledRightOnlyAcceptWeight accept)) := by
  exact (measurable_uncurry_coupledRightAcceptance haccept).sub
    (measurable_uncurry_coupledBothAcceptWeight haccept)

theorem measurable_uncurry_coupledBothRejectWeight
    {accept : State → State → ENNReal}
    (haccept : Measurable (Function.uncurry accept)) :
    Measurable (Function.uncurry (coupledBothRejectWeight accept)) := by
  exact measurable_const.sub
    ((measurable_uncurry_coupledLeftAcceptance haccept).max
      (measurable_uncurry_coupledRightAcceptance haccept))

/-- Apply an input-dependent map after weighting a kernel row by a finite
density. -/
noncomputable def weightedDependentMap
    (kernel : ProbabilityTheory.Kernel (State × State) (State × State))
    [IsSFiniteKernel kernel]
    (weight : (State × State) → (State × State) → ENNReal)
    (hweightFinite : ∀ x y, weight x y ≠ ∞)
    (f : (State × State) → (State × State) → (State × State))
    (hf : Measurable (Function.uncurry f)) :
    ProbabilityTheory.Kernel (State × State) (State × State) := by
  letI : IsSFiniteKernel (kernel.withDensity weight) :=
    ProbabilityTheory.Kernel.IsSFiniteKernel.withDensity kernel hweightFinite
  exact dependentMap (kernel.withDensity weight) f hf

theorem weightedDependentMap_apply
    (kernel : ProbabilityTheory.Kernel (State × State) (State × State))
    [IsSFiniteKernel kernel]
    (weight : (State × State) → (State × State) → ENNReal)
    (hweightFinite : ∀ x y, weight x y ≠ ∞)
    (hweight : Measurable (Function.uncurry weight))
    (f : (State × State) → (State × State) → (State × State))
    (hf : Measurable (Function.uncurry f)) (x : State × State) :
    weightedDependentMap kernel weight hweightFinite f hf x =
      ((kernel x).withDensity (weight x)).map (f x) := by
  rw [weightedDependentMap]
  rw [dependentMap_apply, ProbabilityTheory.Kernel.withDensity_apply kernel hweight]

omit [MeasurableSpace State] in
theorem coupledBothAcceptWeight_ne_top
    (accept : State → State → ENNReal) (hle : ∀ x y, accept x y ≤ 1)
    (current proposal : State × State) :
    coupledBothAcceptWeight accept current proposal ≠ ∞ := by
  apply ne_top_of_le_ne_top ENNReal.one_ne_top
  exact (min_le_left _ _).trans (hle current.1 proposal.1)

omit [MeasurableSpace State] in
theorem coupledLeftOnlyAcceptWeight_ne_top
    (accept : State → State → ENNReal) (hle : ∀ x y, accept x y ≤ 1)
    (current proposal : State × State) :
    coupledLeftOnlyAcceptWeight accept current proposal ≠ ∞ := by
  apply ne_top_of_le_ne_top ENNReal.one_ne_top
  exact tsub_le_self.trans (hle current.1 proposal.1)

omit [MeasurableSpace State] in
theorem coupledRightOnlyAcceptWeight_ne_top
    (accept : State → State → ENNReal) (hle : ∀ x y, accept x y ≤ 1)
    (current proposal : State × State) :
    coupledRightOnlyAcceptWeight accept current proposal ≠ ∞ := by
  apply ne_top_of_le_ne_top ENNReal.one_ne_top
  exact tsub_le_self.trans (hle current.2 proposal.2)

omit [MeasurableSpace State] in
theorem coupledBothRejectWeight_ne_top
    (accept : State → State → ENNReal) (_hle : ∀ x y, accept x y ≤ 1)
    (current proposal : State × State) :
    coupledBothRejectWeight accept current proposal ≠ ∞ := by
  apply ne_top_of_le_ne_top ENNReal.one_ne_top
  exact tsub_le_self

/-- Joint accept/reject transition obtained from a coupled proposal kernel and
one shared uniform acceptance variable. -/
noncomputable def coupledAcceptRejectKernel
    (proposalCoupling :
      ProbabilityTheory.Kernel (State × State) (State × State))
    [IsMarkovKernel proposalCoupling]
    (accept : State → State → ENNReal)
    (hle : ∀ x y, accept x y ≤ 1) :
    ProbabilityTheory.Kernel (State × State) (State × State) :=
  weightedDependentMap proposalCoupling (coupledBothAcceptWeight accept)
      (coupledBothAcceptWeight_ne_top accept hle)
      (fun _current proposal => proposal) (by fun_prop) +
    weightedDependentMap proposalCoupling (coupledLeftOnlyAcceptWeight accept)
      (coupledLeftOnlyAcceptWeight_ne_top accept hle)
      (fun current proposal => (proposal.1, current.2)) (by fun_prop) +
    weightedDependentMap proposalCoupling (coupledRightOnlyAcceptWeight accept)
      (coupledRightOnlyAcceptWeight_ne_top accept hle)
      (fun current proposal => (current.1, proposal.2)) (by fun_prop) +
    weightedDependentMap proposalCoupling (coupledBothRejectWeight accept)
      (coupledBothRejectWeight_ne_top accept hle)
      (fun current _proposal => current) (by fun_prop)

/-- Every row of the coupled kernel is the four-branch measure construction
proved correct above. -/
theorem coupledAcceptRejectKernel_apply
    (proposalCoupling :
      ProbabilityTheory.Kernel (State × State) (State × State))
    [IsMarkovKernel proposalCoupling]
    {accept : State → State → ENNReal}
    (haccept : Measurable (Function.uncurry accept))
    (hle : ∀ x y, accept x y ≤ 1) (current : State × State) :
    coupledAcceptRejectKernel proposalCoupling accept hle current =
      coupledAcceptRejectMeasure current (proposalCoupling current) accept := by
  rw [coupledAcceptRejectKernel]
  simp only [ProbabilityTheory.Kernel.coe_add, Pi.add_apply]
  rw [weightedDependentMap_apply _ _ _
      (measurable_uncurry_coupledBothAcceptWeight haccept),
    weightedDependentMap_apply _ _ _
      (measurable_uncurry_coupledLeftOnlyAcceptWeight haccept),
    weightedDependentMap_apply _ _ _
      (measurable_uncurry_coupledRightOnlyAcceptWeight haccept),
    weightedDependentMap_apply _ _ _
      (measurable_uncurry_coupledBothRejectWeight haccept)]
  rfl

/-- The shared-uniform coupled accept/reject transition is a Markov kernel. -/
theorem coupledAcceptRejectKernel_isMarkov
    (proposalCoupling :
      ProbabilityTheory.Kernel (State × State) (State × State))
    [IsMarkovKernel proposalCoupling]
    {accept : State → State → ENNReal}
    (haccept : Measurable (Function.uncurry accept))
    (hle : ∀ x y, accept x y ≤ 1) :
    IsMarkovKernel (coupledAcceptRejectKernel proposalCoupling accept hle) := by
  constructor
  intro current
  rw [coupledAcceptRejectKernel_apply proposalCoupling haccept hle current]
  exact coupledAcceptRejectMeasure_isProbability current
    (proposalCoupling current) haccept hle

/-- If the proposal kernel couples `Q` with itself, shared-uniform
accept/reject couples the corresponding Metropolis--Hastings kernel with
itself. -/
theorem coupledAcceptRejectKernel_isCoupling
    (Q : ProbabilityTheory.Kernel State State) [IsMarkovKernel Q]
    (proposalCoupling :
      ProbabilityTheory.Kernel (State × State) (State × State))
    [IsMarkovKernel proposalCoupling]
    {accept : State → State → ENNReal}
    (hproposal : IsCoupling proposalCoupling Q Q)
    (haccept : Measurable (Function.uncurry accept))
    (hle : ∀ x y, accept x y ≤ 1) :
    IsCoupling (coupledAcceptRejectKernel proposalCoupling accept hle)
      (metropolisHastings Q accept) (metropolisHastings Q accept) := by
  constructor
  · ext current s hs
    rw [ProbabilityTheory.Kernel.fst_apply' _ _ hs,
      ProbabilityTheory.Kernel.comap_apply]
    rw [coupledAcceptRejectKernel_apply proposalCoupling haccept hle current]
    have hrow : IsMeasureCoupling (proposalCoupling current)
        (Q current.1) (Q current.2) :=
      ⟨hproposal.fst_apply current, hproposal.snd_apply current⟩
    change (coupledAcceptRejectMeasure current (proposalCoupling current) accept)
      (Prod.fst ⁻¹' s) = _
    rw [← Measure.fst_apply hs]
    rw [coupledAcceptRejectMeasure_fst Q current (proposalCoupling current)
      hrow haccept hle]
  · ext current s hs
    rw [ProbabilityTheory.Kernel.snd_apply' _ _ hs,
      ProbabilityTheory.Kernel.comap_apply]
    rw [coupledAcceptRejectKernel_apply proposalCoupling haccept hle current]
    have hrow : IsMeasureCoupling (proposalCoupling current)
        (Q current.1) (Q current.2) :=
      ⟨hproposal.fst_apply current, hproposal.snd_apply current⟩
    change (coupledAcceptRejectMeasure current (proposalCoupling current) accept)
      (Prod.snd ⁻¹' s) = _
    rw [← Measure.snd_apply hs]
    rw [coupledAcceptRejectMeasure_snd Q current (proposalCoupling current)
      hrow haccept hle]

/-- A readily available coupled MH transition obtained from conditionally
independent proposal draws and a shared accept/reject uniform. This validates
the generic kernel API, but for continuous proposals it is not the
exact-meeting proposal coupling used in the paper. -/
noncomputable def independentCoupledMetropolisHastings
    (Q : ProbabilityTheory.Kernel State State) [IsMarkovKernel Q]
    (accept : State → State → ENNReal)
    (hle : ∀ x y, accept x y ≤ 1) :
    ProbabilityTheory.Kernel (State × State) (State × State) :=
  coupledAcceptRejectKernel (independentCoupling Q Q) accept hle

/-- The independent-proposal shared-uniform construction is a Markov kernel. -/
theorem independentCoupledMetropolisHastings_isMarkov
    (Q : ProbabilityTheory.Kernel State State) [IsMarkovKernel Q]
    {accept : State → State → ENNReal}
    (haccept : Measurable (Function.uncurry accept))
    (hle : ∀ x y, accept x y ≤ 1) :
    IsMarkovKernel (independentCoupledMetropolisHastings Q accept hle) := by
  exact coupledAcceptRejectKernel_isMarkov (independentCoupling Q Q)
    haccept hle

/-- The independent-proposal shared-uniform construction has the ordinary MH
kernel on both coordinates. -/
theorem independentCoupledMetropolisHastings_isCoupling
    (Q : ProbabilityTheory.Kernel State State) [IsMarkovKernel Q]
    {accept : State → State → ENNReal}
    (haccept : Measurable (Function.uncurry accept))
    (hle : ∀ x y, accept x y ≤ 1) :
    IsCoupling (independentCoupledMetropolisHastings Q accept hle)
      (metropolisHastings Q accept) (metropolisHastings Q accept) := by
  exact coupledAcceptRejectKernel_isCoupling Q (independentCoupling Q Q)
    (independentCoupling_isCoupling Q Q) haccept hle

end KernelStep

section ExactMeeting

open ProbabilityTheory

variable {State : Type*} [MeasurableSpace State] [MeasurableEq State]

/-- Accepted proposal mass already on the diagonal is a lower bound for the
one-step exact-meeting probability. Other accept/reject branches may add more
diagonal mass, so this is deliberately an inequality. -/
theorem acceptedDiagonalMass_le_coupledAcceptRejectMeasure
    (current : State × State) (proposal : Measure (State × State))
    (accept : State → State → ENNReal) :
    (∫⁻ z in Set.diagonal State,
        coupledBothAcceptWeight accept current z ∂proposal) ≤
      coupledAcceptRejectMeasure current proposal accept (Set.diagonal State) := by
  rw [coupledAcceptRejectMeasure, Measure.add_apply, Measure.add_apply,
    Measure.add_apply]
  rw [Measure.map_apply measurable_id measurableSet_diagonal]
  simp only [Set.preimage_id_eq, id_eq]
  rw [withDensity_apply _ measurableSet_diagonal]
  exact ((le_add_right le_rfl).trans (le_add_right le_rfl)).trans
    (le_add_right le_rfl)

/-- Quantitative form: if simultaneous acceptance is at least `ε` on the
diagonal, at least `ε` times the proposal's diagonal mass becomes exact
meeting mass. -/
theorem mul_diagonalMass_le_coupledAcceptRejectMeasure
    (current : State × State) (proposal : Measure (State × State))
    (accept : State → State → ENNReal) (ε : ENNReal)
    (hweight : ∀ z ∈ Set.diagonal State,
      ε ≤ coupledBothAcceptWeight accept current z) :
    ε * proposal (Set.diagonal State) ≤
      coupledAcceptRejectMeasure current proposal accept (Set.diagonal State) := by
  apply le_trans _
    (acceptedDiagonalMass_le_coupledAcceptRejectMeasure current proposal accept)
  calc
    ε * proposal (Set.diagonal State) =
        ∫⁻ _z in Set.diagonal State, ε ∂proposal := by simp
    _ ≤ ∫⁻ z in Set.diagonal State,
        coupledBothAcceptWeight accept current z ∂proposal :=
      setLIntegral_mono' measurableSet_diagonal hweight

/-- Positive accepted diagonal proposal mass implies positive one-step exact
meeting probability. -/
theorem coupledAcceptRejectMeasure_meeting_pos
    (current : State × State) (proposal : Measure (State × State))
    {accept : State → State → ENNReal}
    (hpositive : 0 < ∫⁻ z in Set.diagonal State,
      coupledBothAcceptWeight accept current z ∂proposal) :
    0 < coupledAcceptRejectMeasure current proposal accept (Set.diagonal State) :=
  hpositive.trans_le
    (acceptedDiagonalMass_le_coupledAcceptRejectMeasure current proposal accept)

omit [MeasurableEq State] in
/-- A positive proposal mass on the diagonal survives whenever the probability
that both chains accept is pointwise positive there. -/
theorem acceptedDiagonalMass_pos
    (current : State × State) (proposal : Measure (State × State))
    {accept : State → State → ENNReal}
    (haccept : Measurable (Function.uncurry accept))
    (hproposal : 0 < proposal (Set.diagonal State))
    (hweight : ∀ z ∈ Set.diagonal State,
      0 < coupledBothAcceptWeight accept current z) :
    0 < ∫⁻ z in Set.diagonal State,
      coupledBothAcceptWeight accept current z ∂proposal := by
  rw [setLIntegral_pos_iff
    (measurable_uncurry_coupledBothAcceptWeight haccept).of_uncurry_left]
  have hsupport : Function.support (coupledBothAcceptWeight accept current) ∩
      Set.diagonal State = Set.diagonal State := by
    ext z
    constructor
    · exact fun hz => hz.2
    · intro hz
      exact ⟨by simpa only [Function.mem_support] using (hweight z hz).ne', hz⟩
  rw [hsupport]
  exact hproposal

/-- Kernel-level exact-meeting lower bound for the shared-uniform transition. -/
theorem acceptedDiagonalMass_le_coupledAcceptRejectKernel
    (proposalCoupling :
      ProbabilityTheory.Kernel (State × State) (State × State))
    [IsMarkovKernel proposalCoupling]
    {accept : State → State → ENNReal}
    (haccept : Measurable (Function.uncurry accept))
    (hle : ∀ x y, accept x y ≤ 1) (current : State × State) :
    (∫⁻ z in Set.diagonal State,
        coupledBothAcceptWeight accept current z ∂proposalCoupling current) ≤
      coupledAcceptRejectKernel proposalCoupling accept hle current
        (Set.diagonal State) := by
  rw [coupledAcceptRejectKernel_apply proposalCoupling haccept hle current]
  exact acceptedDiagonalMass_le_coupledAcceptRejectMeasure current
    (proposalCoupling current) accept

/-- Kernel-level quantitative exact-meeting bound. -/
theorem mul_diagonalMass_le_coupledAcceptRejectKernel
    (proposalCoupling :
      ProbabilityTheory.Kernel (State × State) (State × State))
    [IsMarkovKernel proposalCoupling]
    {accept : State → State → ENNReal}
    (haccept : Measurable (Function.uncurry accept))
    (hle : ∀ x y, accept x y ≤ 1) (current : State × State)
    (ε : ENNReal)
    (hweight : ∀ z ∈ Set.diagonal State,
      ε ≤ coupledBothAcceptWeight accept current z) :
    ε * proposalCoupling current (Set.diagonal State) ≤
      coupledAcceptRejectKernel proposalCoupling accept hle current
        (Set.diagonal State) := by
  rw [coupledAcceptRejectKernel_apply proposalCoupling haccept hle current]
  exact mul_diagonalMass_le_coupledAcceptRejectMeasure current
    (proposalCoupling current) accept ε hweight

/-- Localized quantitative exact-meeting bound. It is enough to control
simultaneous acceptance on the part of the proposal diagonal lying over a
chosen measurable region `A`. -/
theorem mul_diagonalOverMass_le_coupledAcceptRejectKernel
    (proposalCoupling :
      ProbabilityTheory.Kernel (State × State) (State × State))
    [IsMarkovKernel proposalCoupling]
    {accept : State → State → ENNReal}
    (haccept : Measurable (Function.uncurry accept))
    (hle : ∀ x y, accept x y ≤ 1) (current : State × State)
    {A : Set State} (hA : MeasurableSet A) (ε : ENNReal)
    (hweight : ∀ z ∈ diagonalOver A,
      ε ≤ coupledBothAcceptWeight accept current z) :
    ε * proposalCoupling current (diagonalOver A) ≤
      coupledAcceptRejectKernel proposalCoupling accept hle current
        (Set.diagonal State) := by
  apply le_trans _
    (acceptedDiagonalMass_le_coupledAcceptRejectKernel proposalCoupling
      haccept hle current)
  calc
    ε * proposalCoupling current (diagonalOver A) =
        ∫⁻ _z in diagonalOver A, ε ∂proposalCoupling current := by
      rw [setLIntegral_const]
    _ ≤ ∫⁻ z in diagonalOver A,
        coupledBothAcceptWeight accept current z ∂proposalCoupling current :=
      setLIntegral_mono' (measurableSet_diagonalOver hA) hweight
    _ ≤ ∫⁻ z in Set.diagonal State,
        coupledBothAcceptWeight accept current z ∂proposalCoupling current :=
      lintegral_mono_set (Set.inter_subset_left)

/-- Explicit sufficient condition for the coupled MH kernel to meet exactly in
one step from a given current pair. -/
theorem coupledAcceptRejectKernel_meeting_pos
    (proposalCoupling :
      ProbabilityTheory.Kernel (State × State) (State × State))
    [IsMarkovKernel proposalCoupling]
    {accept : State → State → ENNReal}
    (haccept : Measurable (Function.uncurry accept))
    (hle : ∀ x y, accept x y ≤ 1) (current : State × State)
    (hproposal : 0 < proposalCoupling current (Set.diagonal State))
    (hweight : ∀ z ∈ Set.diagonal State,
      0 < coupledBothAcceptWeight accept current z) :
    0 < coupledAcceptRejectKernel proposalCoupling accept hle current
      (Set.diagonal State) := by
  apply lt_of_lt_of_le
    (acceptedDiagonalMass_pos current (proposalCoupling current) haccept
      hproposal hweight)
  exact acceptedDiagonalMass_le_coupledAcceptRejectKernel proposalCoupling
    haccept hle current

end ExactMeeting

end McmcLean.Kernel
