import Mcmc.Kernel.Meeting
import Mcmc.Kernel.CoupledChain
import Mcmc.Kernel.CoupledMetropolisHastings

/-!
# Exact-meeting small sets and drift interfaces

This module states the uniform hypotheses that must bridge local coupled-chain
control to geometric meeting tails.  Pointwise positive meeting probability
is deliberately not enough: an exact-meeting small set supplies one common
lower bound over a set of paired states.  A separate geometric-drift predicate
records the Foster--Lyapunov inequality needed to return to such a set.
-/

open MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace Mcmc.Kernel

open ProbabilityTheory

variable {α : Type*} [MeasurableSpace α]

section CompactFloor

variable {X : Type*} [TopologicalSpace X]

/-- A continuous everywhere-positive `ENNReal`-valued function has a common
positive lower bound on every nonempty compact set. -/
theorem exists_pos_le_on_compact
    {f : X → ENNReal} {K : Set X}
    (hK : IsCompact K) (hKne : K.Nonempty)
    (hf : Continuous f) (hpos : ∀ x ∈ K, 0 < f x) :
    ∃ floor : ENNReal, 0 < floor ∧ ∀ x ∈ K, floor ≤ f x := by
  obtain ⟨x, hx, hxmin⟩ := hK.exists_isMinOn hKne hf.continuousOn
  exact ⟨f x, hpos x hx, fun y hy => hxmin hy⟩

end CompactFloor

/-- `C` is an exact-meeting small set for a coupled transition when every
state pair in `C` has at least `ε` probability of moving to the diagonal. -/
def IsExactMeetingSmallSet [MeasurableEq α]
    (coupled : Kernel (α × α) (α × α))
    (C : Set (α × α)) (ε : ENNReal) : Prop :=
  ∀ x ∈ C, ε ≤ coupled x (Set.diagonal α)

/-- The complement of an exact-meeting small set has one-step failure mass at
most `1 - ε`. -/
theorem IsExactMeetingSmallSet.offDiagonal_le
    [MeasurableEq α]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {C : Set (α × α)} {ε : ENNReal}
    (hsmall : IsExactMeetingSmallSet coupled C ε)
    {x : α × α} (hx : x ∈ C) :
    coupled x (Set.diagonal α)ᶜ ≤ 1 - ε := by
  rw [measure_compl measurableSet_diagonal (measure_ne_top _ _), measure_univ]
  exact tsub_le_tsub_left (hsmall x hx) 1

/-- Exact-meeting small-set constants can be weakened. -/
theorem IsExactMeetingSmallSet.mono_constant
    [MeasurableEq α]
    {coupled : Kernel (α × α) (α × α)} {C : Set (α × α)}
    {ε ε' : ENNReal} (hsmall : IsExactMeetingSmallSet coupled C ε)
    (hε : ε' ≤ ε) :
    IsExactMeetingSmallSet coupled C ε' := by
  intro x hx
  exact hε.trans (hsmall x hx)

/-- Uniform diagonal proposal mass and uniform simultaneous acceptance combine
multiplicatively into an exact-meeting small-set constant for shared-uniform
coupled Metropolis--Hastings. -/
theorem coupledAcceptRejectKernel_isExactMeetingSmallSet
    [MeasurableEq α]
    (proposalCoupling : Kernel (α × α) (α × α))
    [IsMarkovKernel proposalCoupling]
    {accept : α → α → ENNReal}
    (haccept : Measurable (Function.uncurry accept))
    (hle : ∀ x y, accept x y ≤ 1)
    (C : Set (α × α)) (proposalBound acceptanceBound : ENNReal)
    (hproposal : IsExactMeetingSmallSet proposalCoupling C proposalBound)
    (hacceptBound : ∀ current ∈ C, ∀ z ∈ Set.diagonal α,
      acceptanceBound ≤ coupledBothAcceptWeight accept current z) :
    IsExactMeetingSmallSet
      (coupledAcceptRejectKernel proposalCoupling accept hle) C
      (acceptanceBound * proposalBound) := by
  intro current hcurrent
  have hproduct : acceptanceBound * proposalBound ≤
      acceptanceBound * proposalCoupling current (Set.diagonal α) := by
    simpa only [mul_comm] using
      (mul_le_mul_left (hproposal current hcurrent) acceptanceBound)
  exact hproduct.trans
    (mul_diagonalMass_le_coupledAcceptRejectKernel proposalCoupling
      haccept hle current acceptanceBound (hacceptBound current hcurrent))

/-- Localized version: proposal mass and simultaneous acceptance only need to
be controlled on the restricted diagonal over a measurable region `A`. -/
theorem coupledAcceptRejectKernel_isExactMeetingSmallSet_of_diagonalOver
    [MeasurableEq α]
    (proposalCoupling : Kernel (α × α) (α × α))
    [IsMarkovKernel proposalCoupling]
    {accept : α → α → ENNReal}
    (haccept : Measurable (Function.uncurry accept))
    (hle : ∀ x y, accept x y ≤ 1)
    (C : Set (α × α)) {A : Set α} (hA : MeasurableSet A)
    (proposalBound acceptanceBound : ENNReal)
    (hproposal : ∀ current ∈ C,
      proposalBound ≤ proposalCoupling current (diagonalOver A))
    (hacceptBound : ∀ current ∈ C, ∀ z ∈ diagonalOver A,
      acceptanceBound ≤ coupledBothAcceptWeight accept current z) :
    IsExactMeetingSmallSet
      (coupledAcceptRejectKernel proposalCoupling accept hle) C
      (acceptanceBound * proposalBound) := by
  intro current hcurrent
  have hproduct : acceptanceBound * proposalBound ≤
      acceptanceBound * proposalCoupling current (diagonalOver A) := by
    simpa only [mul_comm] using
      (mul_le_mul_left (hproposal current hcurrent) acceptanceBound)
  exact hproduct.trans
    (mul_diagonalOverMass_le_coupledAcceptRejectKernel proposalCoupling
      haccept hle current hA acceptanceBound
      (hacceptBound current hcurrent))

/-- A mixture inherits the weighted exact-meeting small-set constant of its
second branch. -/
theorem mixture_isExactMeetingSmallSet_of_second
    [MeasurableEq α]
    (p : Set.Icc (0 : NNReal) 1)
    (first second : Kernel (α × α) (α × α))
    {C : Set (α × α)} {ε : ENNReal}
    (hsecond : IsExactMeetingSmallSet second C ε) :
    IsExactMeetingSmallSet (mixture p first second) C
      (((1 - p.1 : NNReal) : ENNReal) * ε) := by
  intro x hx
  calc
    ((1 - p.1 : NNReal) : ENNReal) * ε ≤
        ((1 - p.1 : NNReal) : ENNReal) *
          second x (Set.diagonal α) :=
      by
        simpa only [mul_comm] using
          (mul_le_mul_left (hsecond x hx)
            (((1 - p.1 : NNReal) : ENNReal)))
    _ ≤ mixture p first second x (Set.diagonal α) :=
      mixture_apply_second_le p first second x measurableSet_diagonal

/-- Foster--Lyapunov drift toward a paired small set.  Outside `C`, the
expected next value is at most `λ V(x)`; inside `C`, an additive allowance
`b` is permitted.  The strict condition `λ < 1` is intentionally kept as a
separate hypothesis in theorems using this interface. -/
def HasGeometricDrift
    (coupled : Kernel (α × α) (α × α))
    (V : (α × α) → ENNReal) (C : Set (α × α))
    (rate allowance : ENNReal) : Prop :=
  Measurable V ∧ MeasurableSet C ∧
    ∀ x, (∫⁻ y, V y ∂coupled x) ≤
      rate * V x + C.indicator (fun _ => allowance) x

/-- Ordinary one-chain affine Lyapunov drift. This is the natural interface
for proving algorithm-specific HMC and RWMH estimates before lifting them to
a coupled chain. -/
def HasAffineDrift
    (transition : Kernel α α) (v : α → ENNReal)
    (rate allowance : ENNReal) : Prop :=
  Measurable v ∧ ∀ x, (∫⁻ y, v y ∂transition x) ≤ rate * v x + allowance

/-- Ordinary affine drift certificates combine with the weights of a convex
kernel mixture. -/
theorem HasAffineDrift.mixture
    (p : Set.Icc (0 : NNReal) 1) (first second : Kernel α α)
    {v : α → ENNReal}
    {firstRate firstAllowance secondRate secondAllowance : ENNReal}
    (hfirst : HasAffineDrift first v firstRate firstAllowance)
    (hsecond : HasAffineDrift second v secondRate secondAllowance) :
    HasAffineDrift (mixture p first second) v
      ((p.1 : ENNReal) * firstRate +
        (((1 - p.1 : NNReal) : NNReal) : ENNReal) * secondRate)
      ((p.1 : ENNReal) * firstAllowance +
        (((1 - p.1 : NNReal) : NNReal) : ENNReal) * secondAllowance) := by
  refine ⟨hfirst.1, fun x => ?_⟩
  rw [mixture_apply, lintegral_add_measure,
    lintegral_smul_measure, lintegral_smul_measure]
  calc
    (p.1 : ENNReal) * (∫⁻ y, v y ∂first x) +
        (((1 - p.1 : NNReal) : NNReal) : ENNReal) *
          (∫⁻ y, v y ∂second x) ≤
        (p.1 : ENNReal) * (firstRate * v x + firstAllowance) +
          (((1 - p.1 : NNReal) : NNReal) : ENNReal) *
            (secondRate * v x + secondAllowance) := by
      gcongr
      · exact hfirst.2 x
      · exact hsecond.2 x
    _ = ((p.1 : ENNReal) * firstRate +
          (((1 - p.1 : NNReal) : NNReal) : ENNReal) * secondRate) * v x +
        ((p.1 : ENNReal) * firstAllowance +
          (((1 - p.1 : NNReal) : NNReal) : ENNReal) * secondAllowance) := by
      ring

/-- A finite initial `v`-moment remains finite after Algorithm 1's separate
first-chain update, so the resulting lagged pair `(X₁,Y₀)` has finite additive
paired Lyapunov moment. -/
theorem HasAffineDrift.laggedInitialMeasure_pairedMoment_ne_top
    (transition : Kernel α α) [IsMarkovKernel transition]
    {v : α → ENNReal} {rate allowance : ENNReal}
    (hdrift : HasAffineDrift transition v rate allowance)
    (initial : Measure α) [IsProbabilityMeasure initial]
    (initialCoupling : Measure (α × α))
    (hinitial : IsMeasureCoupling initialCoupling initial initial)
    (hmoment : (∫⁻ x, v x ∂initial) ≠ ∞)
    (hrateTop : rate ≠ ∞) (hallowanceTop : allowance ≠ ∞) :
    (∫⁻ z, IsCoupling.pairedAdd v z
      ∂laggedInitialMeasure initialCoupling transition) ≠ ∞ := by
  have hleftLe : (∫⁻ y, v y ∂Measure.bind initial transition) ≤
      rate * (∫⁻ x, v x ∂initial) + allowance := by
    rw [Measure.lintegral_bind transition.aemeasurable
      hdrift.1.aemeasurable]
    calc
      (∫⁻ x, ∫⁻ y, v y ∂transition x ∂initial) ≤
          ∫⁻ x, rate * v x + allowance ∂initial := by
        exact lintegral_mono hdrift.2
      _ = rate * (∫⁻ x, v x ∂initial) + allowance := by
        have hscaled : Measurable (fun x => rate * v x) :=
          measurable_const.mul hdrift.1
        rw [lintegral_add_left hscaled,
          lintegral_const_mul _ hdrift.1, lintegral_const, measure_univ,
          mul_one]
  have hleftTop : (∫⁻ y, v y ∂Measure.bind initial transition) ≠ ∞ := by
    apply ne_top_of_le_ne_top _ hleftLe
    exact ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top hrateTop hmoment, hallowanceTop⟩
  have hlagged := laggedInitialMeasure_isMeasureCoupling
    initialCoupling initial transition hinitial
  have heq :
      (∫⁻ z, IsCoupling.pairedAdd v z
        ∂laggedInitialMeasure initialCoupling transition) =
        (∫⁻ y, v y ∂Measure.bind initial transition) +
          (∫⁻ y, v y ∂initial) := by
    change (∫⁻ z, v z.1 + v z.2
      ∂laggedInitialMeasure initialCoupling transition) = _
    have hfst : Measurable (fun z : α × α => v z.1) :=
      hdrift.1.comp measurable_fst
    rw [lintegral_add_left hfst,
      lintegral_fst_eq_of_isMeasureCoupling hlagged hdrift.1,
      lintegral_snd_eq_of_isMeasureCoupling hlagged hdrift.1]
  rw [heq]
  exact ENNReal.add_ne_top.2 ⟨hleftTop, hmoment⟩

/-- An affine bound checked at a lower threshold remains valid at larger
Lyapunov values when the target rate dominates the source rate. -/
theorem affineDrift_le_mul_of_threshold
    {sourceRate targetRate allowance threshold value : ENNReal}
    (hrates : sourceRate ≤ targetRate)
    (hthreshold : sourceRate * threshold + allowance ≤ targetRate * threshold)
    (hvalue : threshold ≤ value) :
    sourceRate * value + allowance ≤ targetRate * value := by
  obtain ⟨excess, rfl⟩ := exists_add_of_le hvalue
  calc
    sourceRate * (threshold + excess) + allowance =
        (sourceRate * threshold + allowance) + sourceRate * excess := by ring
    _ ≤ targetRate * threshold + targetRate * excess := by
      exact add_le_add hthreshold (by gcongr)
    _ = targetRate * (threshold + excess) := by ring

/-- Canonical paired rate obtained by absorbing the doubled one-chain affine
allowance outside a Lyapunov sublevel. -/
noncomputable def affinePairedSublevelRate
    (sourceRate sourceAllowance threshold : ENNReal) : ENNReal :=
  (sourceRate * threshold + (sourceAllowance + sourceAllowance)) / threshold

/-- Under the strict sublevel budget, the canonical paired rate dominates the
source rate, absorbs the doubled allowance at the threshold, and is subunit. -/
theorem affinePairedSublevelRate_spec
    {sourceRate sourceAllowance threshold : ENNReal}
    (hthreshold0 : threshold ≠ 0) (hthresholdTop : threshold ≠ ∞)
    (hbudget :
      sourceRate * threshold + (sourceAllowance + sourceAllowance) < threshold) :
    sourceRate ≤ affinePairedSublevelRate sourceRate sourceAllowance threshold ∧
      sourceRate * threshold + (sourceAllowance + sourceAllowance) ≤
        affinePairedSublevelRate sourceRate sourceAllowance threshold * threshold ∧
      affinePairedSublevelRate sourceRate sourceAllowance threshold < 1 := by
  let numerator := sourceRate * threshold + (sourceAllowance + sourceAllowance)
  have hsource : sourceRate ≤ numerator / threshold := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hthreshold0) (Or.inl hthresholdTop)]
    exact le_add_right le_rfl
  have habsorb : numerator ≤ numerator / threshold * threshold := by
    rw [ENNReal.div_mul_cancel hthreshold0 hthresholdTop]
  have hrate : numerator / threshold < 1 := by
    rw [ENNReal.div_lt_iff (Or.inl hthreshold0) (Or.inl hthresholdTop)]
    simpa only [one_mul] using hbudget
  exact ⟨hsource, habsorb, hrate⟩

/-- Convex mixtures combine component drift rates and allowances with the
same mixture weights. Both certificates must use the same Lyapunov function
and drift set. -/
theorem HasGeometricDrift.mixture
    (p : Set.Icc (0 : NNReal) 1)
    (first second : Kernel (α × α) (α × α))
    {V : (α × α) → ENNReal} {C : Set (α × α)}
    {firstRate firstAllowance secondRate secondAllowance : ENNReal}
    (hfirst : HasGeometricDrift first V C firstRate firstAllowance)
    (hsecond : HasGeometricDrift second V C secondRate secondAllowance) :
    HasGeometricDrift (mixture p first second) V C
      ((p.1 : ENNReal) * firstRate +
        (((1 - p.1 : NNReal) : NNReal) : ENNReal) * secondRate)
      ((p.1 : ENNReal) * firstAllowance +
        (((1 - p.1 : NNReal) : NNReal) : ENNReal) * secondAllowance) := by
  refine ⟨hfirst.1, hfirst.2.1, fun x => ?_⟩
  rw [mixture_apply, lintegral_add_measure,
    lintegral_smul_measure, lintegral_smul_measure]
  calc
    (p.1 : ENNReal) * (∫⁻ y, V y ∂first x) +
        (((1 - p.1 : NNReal) : NNReal) : ENNReal) *
          (∫⁻ y, V y ∂second x) ≤
        (p.1 : ENNReal) *
            (firstRate * V x + C.indicator (fun _ => firstAllowance) x) +
          (((1 - p.1 : NNReal) : NNReal) : ENNReal) *
            (secondRate * V x +
              C.indicator (fun _ => secondAllowance) x) := by
      gcongr
      · exact hfirst.2.2 x
      · exact hsecond.2.2 x
    _ = ((p.1 : ENNReal) * firstRate +
          (((1 - p.1 : NNReal) : NNReal) : ENNReal) * secondRate) * V x +
        C.indicator (fun _ =>
          (p.1 : ENNReal) * firstAllowance +
            (((1 - p.1 : NNReal) : NNReal) : ENNReal) * secondAllowance) x := by
      by_cases hx : x ∈ C <;> simp [hx] <;> ring

/-- Lyapunov sublevel set at height `R`. -/
def lyapunovSublevel (V : (α × α) → ENNReal) (R : ENNReal) :
    Set (α × α) :=
  {x | V x ≤ R}

theorem measurableSet_lyapunovSublevel
    {V : (α × α) → ENNReal} (hV : Measurable V) (R : ENNReal) :
    MeasurableSet (lyapunovSublevel V R) := by
  exact measurableSet_le hV measurable_const

/-- A one-chain affine drift bound lifts through every exact self-coupling to
geometric drift for the additive paired Lyapunov function. Outside a paired
sublevel, the doubled affine allowance is absorbed into the chosen paired
rate; inside, it becomes the drift allowance. -/
theorem HasAffineDrift.coupling_pairedAdd_sublevel
    (transition : Kernel α α)
    (coupled : Kernel (α × α) (α × α))
    (hcoupled : IsCoupling coupled transition transition)
    {v : α → ENNReal} {sourceRate sourceAllowance pairedRate threshold : ENNReal}
    (hdrift : HasAffineDrift transition v sourceRate sourceAllowance)
    (hrates : sourceRate ≤ pairedRate)
    (hthreshold :
      sourceRate * threshold + (sourceAllowance + sourceAllowance) ≤
        pairedRate * threshold) :
    HasGeometricDrift coupled (IsCoupling.pairedAdd v)
      (lyapunovSublevel (IsCoupling.pairedAdd v) threshold)
      pairedRate (sourceAllowance + sourceAllowance) := by
  let V := IsCoupling.pairedAdd v
  have hV : Measurable V := IsCoupling.measurable_pairedAdd hdrift.1
  refine ⟨hV, measurableSet_lyapunovSublevel hV threshold, fun x => ?_⟩
  rw [hcoupled.lintegral_pairedAdd hdrift.1 x]
  have hbase :
      (∫⁻ y, v y ∂transition x.1) + (∫⁻ y, v y ∂transition x.2) ≤
        sourceRate * V x + (sourceAllowance + sourceAllowance) := by
    calc
      (∫⁻ y, v y ∂transition x.1) + (∫⁻ y, v y ∂transition x.2) ≤
          (sourceRate * v x.1 + sourceAllowance) +
            (sourceRate * v x.2 + sourceAllowance) :=
        add_le_add (hdrift.2 x.1) (hdrift.2 x.2)
      _ = sourceRate * V x + (sourceAllowance + sourceAllowance) := by
        dsimp only [V, IsCoupling.pairedAdd]
        ring
  by_cases hx : x ∈ lyapunovSublevel V threshold
  · rw [Set.indicator_of_mem hx]
    exact hbase.trans (by gcongr)
  · rw [Set.indicator_of_notMem hx, add_zero]
    exact hbase.trans (affineDrift_le_mul_of_threshold hrates hthreshold
      (le_of_not_ge hx))

/-- Foster--Lyapunov drift gives a state-weighted one-step escape estimate
from every Lyapunov sublevel. -/
theorem HasGeometricDrift.mul_measure_compl_sublevel_le
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal} {C : Set (α × α)}
    {rate allowance : ENNReal}
    (hdrift : HasGeometricDrift coupled V C rate allowance)
    (R : ENNReal) (x : α × α) :
    R * coupled x (lyapunovSublevel V R)ᶜ ≤
      rate * V x + allowance := by
  have hsub := measurableSet_lyapunovSublevel hdrift.1 R
  calc
    R * coupled x (lyapunovSublevel V R)ᶜ =
        ∫⁻ _y in (lyapunovSublevel V R)ᶜ, R ∂coupled x := by
      rw [setLIntegral_const]
    _ ≤ ∫⁻ y in (lyapunovSublevel V R)ᶜ, V y ∂coupled x := by
      apply setLIntegral_mono' hsub.compl
      intro y hy
      exact le_of_not_ge hy
    _ ≤ ∫⁻ y, V y ∂coupled x := setLIntegral_le_lintegral _ _
    _ ≤ rate * V x + C.indicator (fun _ => allowance) x := hdrift.2.2 x
    _ ≤ rate * V x + allowance := by
      gcongr
      by_cases hx : x ∈ C <;> simp [hx]

/-- Outside the drift set, restricting the next transition to states still
outside that set preserves the multiplicative drift bound. -/
theorem HasGeometricDrift.lintegral_restrict_compl_le
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal} {C : Set (α × α)}
    {rate allowance : ENNReal}
    (hdrift : HasGeometricDrift coupled V C rate allowance)
    {x : α × α} (hx : x ∉ C) :
    (∫⁻ y, V y ∂(coupled.restrict hdrift.2.1.compl) x) ≤ rate * V x := by
  rw [Kernel.lintegral_restrict]
  calc
    (∫⁻ y in Cᶜ, V y ∂coupled x) ≤ ∫⁻ y, V y ∂coupled x :=
      setLIntegral_le_lintegral Cᶜ V
    _ ≤ rate * V x + C.indicator (fun _ => allowance) x := hdrift.2.2 x
    _ = rate * V x := by simp [hx]

/-- Iterating the kernel killed on entry to `C` gives the standard
state-weighted geometric drift estimate. -/
theorem HasGeometricDrift.lintegral_pow_restrict_compl_le
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal} {C : Set (α × α)}
    {rate allowance : ENNReal}
    (hdrift : HasGeometricDrift coupled V C rate allowance)
    (n : ℕ) {x : α × α} (hx : x ∉ C) :
    (∫⁻ y, V y ∂((coupled.restrict hdrift.2.1.compl) ^ n) x) ≤
      rate ^ n * V x := by
  induction n generalizing x with
  | zero =>
      rw [pow_zero]
      rw [show (1 : Kernel (α × α) (α × α)) = Kernel.id from rfl,
        Kernel.id_apply, lintegral_dirac' x hdrift.1, pow_zero, one_mul]
  | succ n ih =>
      rw [pow_succ]
      change
        (∫⁻ z, V z ∂(((coupled.restrict hdrift.2.1.compl) ^ n) ∘ₖ
          coupled.restrict hdrift.2.1.compl) x) ≤ rate ^ (n + 1) * V x
      rw [Kernel.lintegral_comp _ _ _ hdrift.1,
        Kernel.lintegral_restrict]
      calc
        (∫⁻ y in Cᶜ,
            ∫⁻ z, V z ∂((coupled.restrict hdrift.2.1.compl) ^ n) y
            ∂coupled x) ≤
            ∫⁻ y in Cᶜ, rate ^ n * V y ∂coupled x := by
          apply setLIntegral_mono' hdrift.2.1.compl
          intro y hy
          exact ih hy
        _ = rate ^ n * ∫⁻ y in Cᶜ, V y ∂coupled x := by
          rw [lintegral_const_mul _ hdrift.1]
        _ ≤ rate ^ n * (rate * V x) := by
          gcongr
          exact hdrift.lintegral_restrict_compl_le coupled hx
        _ = rate ^ (n + 1) * V x := by
          rw [pow_succ]
          ac_rfl

/-- Total surviving mass of the `n`-step kernel killed whenever it enters
`C`. This is the kernel-level probability of avoiding `C` for `n` transitions. -/
noncomputable def returnFailureMass
    (coupled : Kernel (α × α) (α × α))
    (C : Set (α × α)) (hC : MeasurableSet C)
    (n : ℕ) (x : α × α) : ENNReal :=
  ((coupled.restrict hC.compl) ^ n) x Set.univ

/-- Finite histories through time `n` that avoid `C` at every strictly
positive coordinate. Time zero is deliberately not tested. -/
def finiteReturnFailureSet (C : Set (α × α)) (n : ℕ) :
    Set ((i : Finset.Iic n) → α × α) :=
  ⋂ i : Finset.Iic n,
    if 1 ≤ (i : ℕ) then (fun history => history i) ⁻¹' Cᶜ else Set.univ

/-- The finite-history avoidance set is measurable. -/
theorem measurableSet_finiteReturnFailureSet
    {C : Set (α × α)} (hC : MeasurableSet C) (n : ℕ) :
    MeasurableSet (finiteReturnFailureSet C n) := by
  apply MeasurableSet.iInter
  intro i
  split_ifs
  · exact hC.compl.preimage (measurable_pi_apply i)
  · exact MeasurableSet.univ

/-- Paths that avoid `C` at each of the next `n` strictly positive times. -/
def returnFailureEvent (C : Set (α × α)) (n : ℕ) :
    Set (ℕ → α × α) :=
  Preorder.frestrictLe n ⁻¹' finiteReturnFailureSet C n

/-- Finite-horizon return-failure events are measurable. -/
theorem measurableSet_returnFailureEvent
    {C : Set (α × α)} (hC : MeasurableSet C) (n : ℕ) :
    MeasurableSet (returnFailureEvent C n) := by
  exact (measurableSet_finiteReturnFailureSet hC n).preimage
    (Preorder.measurable_frestrictLe n)

omit [MeasurableSpace α] in
/-- Membership in the return-failure event means avoiding `C` at every time
from one through `n`. -/
theorem mem_returnFailureEvent_iff
    {C : Set (α × α)} {n : ℕ} {path : ℕ → α × α} :
    path ∈ returnFailureEvent C n ↔
      ∀ j, 1 ≤ j → j ≤ n → path j ∉ C := by
  simp only [returnFailureEvent, finiteReturnFailureSet, Set.mem_preimage,
    Set.mem_iInter]
  constructor
  · intro h j hj1 hjn
    specialize h ⟨j, Finset.mem_Iic.mpr hjn⟩
    simpa [hj1] using h
  · intro h i
    by_cases hi1 : 1 ≤ (i : ℕ)
    · simpa [hi1] using h i hi1 (Finset.mem_Iic.mp i.property)
    · simp [hi1]

/-- First strictly positive time at which the paired path returns to `C`. -/
noncomputable def firstReturnTime
    (C : Set (α × α)) (path : ℕ → α × α) : WithTop ℕ :=
  hittingAfter (fun n path => path n) C 1 path

omit [MeasurableSpace α] in
/-- The positive return time is at least one. -/
theorem one_le_firstReturnTime (C : Set (α × α)) (path : ℕ → α × α) :
    (1 : WithTop ℕ) ≤ firstReturnTime C path := by
  exact le_hittingAfter (u := fun n path => path n) (s := C) (n := 1) path

omit [MeasurableSpace α] in
/-- Avoiding `C` through time `n` is exactly the strict tail event of the
first positive return time. -/
theorem mem_returnFailureEvent_iff_firstReturnTime_lt
    (C : Set (α × α)) (path : ℕ → α × α) (n : ℕ) :
    path ∈ returnFailureEvent C n ↔
      (n : WithTop ℕ) < firstReturnTime C path := by
  have hle : firstReturnTime C path ≤ n ↔
      ∃ j ∈ Set.Icc 1 n, path j ∈ C := by
    rw [firstReturnTime]
    exact hittingAfter_le_iff
  rw [show (n : WithTop ℕ) < firstReturnTime C path ↔
      ¬ firstReturnTime C path ≤ n by exact not_le.symm,
    not_congr hle, mem_returnFailureEvent_iff]
  push Not
  constructor
  · intro h j hj hmem
    exact h j hj.1 hj.2 hmem
  · intro h j hj1 hjn hmem
    exact h j ⟨hj1, hjn⟩ hmem

omit [MeasurableSpace α] in
/-- Finite return-failure events decrease with the horizon. -/
theorem antitone_returnFailureEvent (C : Set (α × α)) :
    Antitone (returnFailureEvent C) := by
  intro m n hmn path hn
  rw [mem_returnFailureEvent_iff] at hn ⊢
  intro j hj1 hjm
  exact hn j hj1 (hjm.trans hmn)

/-- Paths that never return to `C` at any strictly positive time. -/
def neverReturnEvent (C : Set (α × α)) : Set (ℕ → α × α) :=
  ⋂ n, returnFailureEvent C n

/-- The never-return event is measurable. -/
theorem measurableSet_neverReturnEvent
    {C : Set (α × α)} (hC : MeasurableSet C) :
    MeasurableSet (neverReturnEvent C) := by
  exact MeasurableSet.iInter fun n => measurableSet_returnFailureEvent hC n

omit [MeasurableSpace α] in
/-- Never returning is exactly the event that the first positive return time
is infinite. -/
theorem neverReturnEvent_eq_firstReturnTime_eq_top (C : Set (α × α)) :
    neverReturnEvent C =
      {path | firstReturnTime C path = (⊤ : WithTop ℕ)} := by
  ext path
  simp only [neverReturnEvent, Set.mem_iInter, Set.mem_setOf_eq,
    mem_returnFailureEvent_iff, firstReturnTime, hittingAfter_eq_top_iff]
  constructor
  · intro h j hj
    exact h j j hj le_rfl
  · intro h n j hj1 _hjn
    exact h j hj1

omit [MeasurableSpace α] in
@[simp]
theorem returnFailureEvent_zero (C : Set (α × α)) :
    returnFailureEvent C 0 = Set.univ := by
  ext path
  simp [returnFailureEvent, finiteReturnFailureSet]

/-- Restricting the infinite path kernel to its first `n` coordinates gives
the finite Ionescu--Tulcea history kernel from the supplied initial point. -/
theorem pathKernel_map_frestrictLe
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (n : ℕ) :
    (pathKernel coupled).map (Preorder.frestrictLe n) =
      (Kernel.partialTraj (X := fun _ => α × α)
        (homogeneousNext coupled) 0 n).comap
          (initialHistory (α := α × α)) measurable_initialHistory := by
  letI : ∀ k, IsMarkovKernel (homogeneousNext coupled k) := fun k =>
    homogeneousNext.instIsMarkovKernel coupled k
  rw [pathKernel,
    ← Kernel.comap_map_comm _ measurable_initialHistory
      (Preorder.measurable_frestrictLe n),
    Kernel.traj_map_frestrictLe]

/-- The path-space avoidance probability is exactly the finite-history
Ionescu--Tulcea probability of the corresponding avoidance set. -/
theorem pathKernel_returnFailureEvent_eq_partialTraj
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {C : Set (α × α)} (hC : MeasurableSet C) (n : ℕ) (x : α × α) :
    pathKernel coupled x (returnFailureEvent C n) =
      Kernel.partialTraj (X := fun _ => α × α)
        (homogeneousNext coupled) 0 n (initialHistory x)
        (finiteReturnFailureSet C n) := by
  rw [returnFailureEvent,
    ← Measure.map_apply (Preorder.measurable_frestrictLe n)
      (measurableSet_finiteReturnFailureSet hC n),
    ← Kernel.map_apply _ (Preorder.measurable_frestrictLe n),
    pathKernel_map_frestrictLe, Kernel.comap_apply]

/-- At horizon one, the explicit path event agrees exactly with the mass of
the once-killed kernel. -/
theorem pathKernel_returnFailureEvent_one
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {C : Set (α × α)} (hC : MeasurableSet C) (x : α × α) :
    pathKernel coupled x (returnFailureEvent C 1) =
      returnFailureMass coupled C hC 1 x := by
  have hevent : returnFailureEvent C 1 =
      (fun path : ℕ → α × α => path 1) ⁻¹' Cᶜ := by
    ext path
    simp [returnFailureEvent, finiteReturnFailureSet]
    constructor
    · intro h
      exact h 1 le_rfl le_rfl
    · intro h a ha h1
      simpa [Nat.le_antisymm ha h1] using h
  rw [hevent, ← Measure.map_apply (measurable_pi_apply 1) hC.compl,
    ← Kernel.map_apply _ (measurable_pi_apply 1), pathKernel_map_one,
    returnFailureMass, pow_one,
    Kernel.restrict_apply' coupled hC.compl x MeasurableSet.univ,
    Set.univ_inter]

/-- Multiplicative zero-one weight for avoiding `C` at times `1,…,n`.
This form is convenient for iterated-integral calculations. -/
noncomputable def returnFailureWeight
    (C : Set (α × α)) (n : ℕ) (path : ℕ → α × α) : ENNReal :=
  ∏ j ∈ Finset.range n,
    Cᶜ.indicator (fun _ => (1 : ENNReal)) (path (j + 1))

/-- The finite avoidance weight is measurable. -/
theorem measurable_returnFailureWeight
    {C : Set (α × α)} (hC : MeasurableSet C) (n : ℕ) :
    Measurable (returnFailureWeight C n) := by
  classical
  apply Finset.measurable_prod
  intro j _hj
  exact (measurable_const.indicator hC.compl).comp (measurable_pi_apply (j + 1))

omit [MeasurableSpace α] in
/-- The multiplicative avoidance weight is the indicator of the explicit
return-failure event. -/
theorem returnFailureWeight_eq_indicator
    {C : Set (α × α)} (n : ℕ) :
    returnFailureWeight C n =
      (returnFailureEvent C n).indicator (fun _ => (1 : ENNReal)) := by
  classical
  funext path
  by_cases hpath : path ∈ returnFailureEvent C n
  · rw [Set.indicator_of_mem hpath]
    rw [returnFailureWeight]
    apply Finset.prod_eq_one
    intro j hj
    rw [Finset.mem_range] at hj
    rw [Set.indicator_of_mem]
    change path (j + 1) ∉ C
    have hfinite := hpath
    simp only [returnFailureEvent, finiteReturnFailureSet, Set.mem_preimage,
      Set.mem_iInter] at hfinite
    specialize hfinite
      ⟨j + 1, Finset.mem_Iic.mpr (Nat.succ_le_iff.mpr hj)⟩
    simpa [Nat.succ_le_succ (Nat.zero_le j)] using hfinite
  · rw [Set.indicator_of_notMem hpath]
    simp only [returnFailureEvent, finiteReturnFailureSet, Set.mem_preimage,
      Set.mem_iInter, not_forall] at hpath
    obtain ⟨i, hi⟩ := hpath
    by_cases hi1 : 1 ≤ (i : ℕ)
    · simp only [hi1, ↓reduceIte, Set.mem_preimage, Set.mem_compl_iff] at hi
      have hin : (i : ℕ) ≤ n := Finset.mem_Iic.mp i.property
      have hj : (i : ℕ) - 1 < n := by omega
      apply Finset.prod_eq_zero (Finset.mem_range.mpr hj)
      rw [Set.indicator_of_notMem]
      simpa [Nat.sub_add_cancel hi1] using hi
    · simp [hi1] at hi

omit [MeasurableSpace α] in
/-- Appending a new terminal state multiplies the previous avoidance weight
by the indicator that the new state is still outside `C`. -/
theorem returnFailureWeight_succ_update
    (C : Set (α × α)) (n : ℕ) (path : ℕ → α × α) (y : α × α) :
    returnFailureWeight C (n + 1) (Function.update path (n + 1) y) =
      returnFailureWeight C n path *
        Cᶜ.indicator (fun _ => (1 : ENNReal)) y := by
  classical
  rw [returnFailureWeight, returnFailureWeight, Finset.prod_range_succ]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have hjlt := Finset.mem_range.mp hj
  rw [Function.update_of_ne (by omega)]

/-- Integrating a terminal test function over finite histories weighted by
avoidance is exactly integration against the corresponding killed-kernel
power. This is the strengthened induction invariant behind the path-event
identity. -/
theorem lmarginalPartialTraj_returnFailureWeight_terminal
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {C : Set (α × α)} (hC : MeasurableSet C)
    (n : ℕ) (x : α × α) {f : (α × α) → ENNReal}
    (hf : Measurable f) :
    Kernel.lmarginalPartialTraj (homogeneousNext coupled) 0 n
        (fun path => returnFailureWeight C n path * f (path n))
        (fun _ => x) =
      ∫⁻ y, f y ∂((coupled.restrict hC.compl) ^ n) x := by
  induction n generalizing f with
  | zero =>
      have hfun : Measurable
          (fun path : ℕ → α × α =>
            returnFailureWeight C 0 path * f (path 0)) :=
        (measurable_returnFailureWeight hC 0).mul
          (hf.comp (measurable_pi_apply 0))
      rw [Kernel.lmarginalPartialTraj_le _ le_rfl hfun, pow_zero]
      simp only [returnFailureWeight, Finset.range_zero, Finset.prod_empty,
        one_mul]
      rw [show (1 : Kernel (α × α) (α × α)) = Kernel.id from rfl,
        Kernel.id_apply, lintegral_dirac' x hf]
  | succ n ih =>
      let F : (ℕ → α × α) → ENNReal := fun path =>
        returnFailureWeight C (n + 1) path * f (path (n + 1))
      have hF : Measurable F :=
        (measurable_returnFailureWeight hC (n + 1)).mul
          (hf.comp (measurable_pi_apply (n + 1)))
      let g : (α × α) → ENNReal := fun z =>
        ∫⁻ y, f y ∂(coupled.restrict hC.compl) z
      have hg : Measurable g := by
        dsimp [g]
        exact hf.lintegral_kernel
      have hinner :
          Kernel.lmarginalPartialTraj (homogeneousNext coupled) n (n + 1) F =
            fun path => returnFailureWeight C n path * g (path n) := by
        funext path
        rw [Kernel.lmarginalPartialTraj_succ n hF path]
        simp only [homogeneousNext, Kernel.comap_apply, F,
          returnFailureWeight_succ_update, Function.update_self]
        let q : (α × α) → ENNReal := fun y =>
          Cᶜ.indicator (fun _ => (1 : ENNReal)) y * f y
        have hq : Measurable q :=
          (measurable_const.indicator hC.compl).mul hf
        have hindicator : q = Cᶜ.indicator f := by
          funext y
          by_cases hy : y ∈ Cᶜ <;> simp [q, hy]
        simp_rw [mul_assoc]
        simp only [Preorder.frestrictLe_apply]
        change (∫⁻ y, returnFailureWeight C n path * q y
          ∂coupled (path n)) = returnFailureWeight C n path * g (path n)
        rw [lintegral_const_mul _ hq, hindicator,
          lintegral_indicator hC.compl]
        dsimp [g]
        rw [Kernel.lintegral_restrict]
      calc
        Kernel.lmarginalPartialTraj (homogeneousNext coupled) 0 (n + 1) F
            (fun _ => x) =
            Kernel.lmarginalPartialTraj (homogeneousNext coupled) 0 n
              (Kernel.lmarginalPartialTraj (homogeneousNext coupled) n
                (n + 1) F) (fun _ => x) := by
          rw [Kernel.lmarginalPartialTraj_self (Nat.zero_le n) n.le_succ hF]
        _ = Kernel.lmarginalPartialTraj (homogeneousNext coupled) 0 n
              (fun path => returnFailureWeight C n path * g (path n))
              (fun _ => x) := by rw [hinner]
        _ = ∫⁻ y, g y ∂((coupled.restrict hC.compl) ^ n) x :=
          ih hg
        _ = ∫⁻ y, f y ∂((coupled.restrict hC.compl) ^ (n + 1)) x := by
          rw [Nat.add_comm n 1, Kernel.pow_add, pow_one,
            Kernel.lintegral_comp _ _ _ hf]

/-- The explicit path-space return-failure probability agrees with the
surviving mass of the iterated killed kernel at every finite horizon. -/
theorem pathKernel_returnFailureEvent_eq_returnFailureMass
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {C : Set (α × α)} (hC : MeasurableSet C) (n : ℕ) (x : α × α) :
    pathKernel coupled x (returnFailureEvent C n) =
      returnFailureMass coupled C hC n x := by
  rw [pathKernel_returnFailureEvent_eq_partialTraj coupled hC n x]
  let μ := Kernel.partialTraj (X := fun _ => α × α)
    (homogeneousNext coupled) 0 n (initialHistory x)
  have hweight :
      (fun history : (i : Finset.Iic n) → α × α =>
        returnFailureWeight C n
          (Function.updateFinset (fun _ => x) (Finset.Iic n) history)) =
        (finiteReturnFailureSet C n).indicator (fun _ => (1 : ENNReal)) := by
    funext history
    rw [returnFailureWeight_eq_indicator]
    by_cases hh : history ∈ finiteReturnFailureSet C n
    · rw [Set.indicator_of_mem hh, Set.indicator_of_mem]
      simpa [returnFailureEvent, Preorder.frestrictLe_updateFinset] using hh
    · rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem]
      simpa [returnFailureEvent, Preorder.frestrictLe_updateFinset] using hh
  calc
    μ (finiteReturnFailureSet C n) =
        ∫⁻ history, (finiteReturnFailureSet C n).indicator
          (fun _ => (1 : ENNReal)) history ∂μ := by
      exact (lintegral_indicator_one
        (μ := μ) (measurableSet_finiteReturnFailureSet hC n)).symm
    _ = Kernel.lmarginalPartialTraj (homogeneousNext coupled) 0 n
          (fun path => returnFailureWeight C n path * (1 : ENNReal))
          (fun _ => x) := by
      rw [Kernel.lmarginalPartialTraj]
      simp only [mul_one]
      rw [hweight]
      change (∫⁻ history, (finiteReturnFailureSet C n).indicator
        (fun _ => (1 : ENNReal)) history ∂μ) = _
      rw [show Preorder.frestrictLe 0 (fun _ : ℕ => x) = initialHistory x from rfl]
    _ = ∫⁻ _y, (1 : ENNReal) ∂((coupled.restrict hC.compl) ^ n) x :=
      lmarginalPartialTraj_returnFailureWeight_terminal coupled hC n x
        measurable_const
    _ = returnFailureMass coupled C hC n x := by
      rw [returnFailureMass, lintegral_one]

/-- If the Lyapunov function is at least one, killed-kernel survival is
bounded by the geometric Lyapunov estimate. -/
theorem HasGeometricDrift.returnFailureMass_le
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal} {C : Set (α × α)}
    {rate allowance : ENNReal}
    (hdrift : HasGeometricDrift coupled V C rate allowance)
    (hVone : ∀ x, 1 ≤ V x)
    (n : ℕ) {x : α × α} (hx : x ∉ C) :
    returnFailureMass coupled C hdrift.2.1 n x ≤ rate ^ n * V x := by
  apply le_trans _ (hdrift.lintegral_pow_restrict_compl_le coupled n hx)
  rw [returnFailureMass, ← lintegral_one]
  exact lintegral_mono hVone

/-- Geometric drift gives the actual finite-horizon path probability of
avoiding `C` the state-weighted bound `rate^n V(x)`. -/
theorem HasGeometricDrift.pathKernel_returnFailureEvent_le
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal} {C : Set (α × α)}
    {rate allowance : ENNReal}
    (hdrift : HasGeometricDrift coupled V C rate allowance)
    (hVone : ∀ x, 1 ≤ V x)
    (n : ℕ) {x : α × α} (hx : x ∉ C) :
    pathKernel coupled x (returnFailureEvent C n) ≤ rate ^ n * V x := by
  rw [pathKernel_returnFailureEvent_eq_returnFailureMass coupled
    hdrift.2.1 n x]
  exact hdrift.returnFailureMass_le coupled hVone n hx

/-- The same bound stated directly for the strict tail of the first positive
return time. -/
theorem HasGeometricDrift.firstReturnTime_tail_le
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal} {C : Set (α × α)}
    {rate allowance : ENNReal}
    (hdrift : HasGeometricDrift coupled V C rate allowance)
    (hVone : ∀ x, 1 ≤ V x)
    (n : ℕ) {x : α × α} (hx : x ∉ C) :
    pathKernel coupled x
        {path | (n : WithTop ℕ) < firstReturnTime C path} ≤
      rate ^ n * V x := by
  have hevent : {path | (n : WithTop ℕ) < firstReturnTime C path} =
      returnFailureEvent C n := by
    ext path
    exact (mem_returnFailureEvent_iff_firstReturnTime_lt C path n).symm
  rw [hevent]
  exact hdrift.pathKernel_returnFailureEvent_le coupled hVone n hx

/-- The sum of positive-return tails is bounded by the geometric series. This
is the `ENNReal` tail-sum form of finite expected return delay. -/
theorem HasGeometricDrift.tsum_firstReturnTime_tail_le
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal} {C : Set (α × α)}
    {rate allowance : ENNReal}
    (hdrift : HasGeometricDrift coupled V C rate allowance)
    (hVone : ∀ x, 1 ≤ V x)
    {x : α × α} (hx : x ∉ C) :
    (∑' n : ℕ, pathKernel coupled x
      {path | (n : WithTop ℕ) < firstReturnTime C path}) ≤
        (1 - rate)⁻¹ * V x := by
  calc
    (∑' n : ℕ, pathKernel coupled x
        {path | (n : WithTop ℕ) < firstReturnTime C path}) ≤
        ∑' n : ℕ, rate ^ n * V x := by
      apply ENNReal.tsum_le_tsum
      intro n
      exact hdrift.firstReturnTime_tail_le coupled hVone n hx
    _ = (∑' n : ℕ, rate ^ n) * V x := ENNReal.tsum_mul_right
    _ = (1 - rate)⁻¹ * V x := by rw [ENNReal.tsum_geometric]

/-- Under a strict rate and finite initial Lyapunov value, the return-time
tail sum is finite. -/
theorem HasGeometricDrift.tsum_firstReturnTime_tail_lt_top
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal} {C : Set (α × α)}
    {rate allowance : ENNReal}
    (hdrift : HasGeometricDrift coupled V C rate allowance)
    (hVone : ∀ x, 1 ≤ V x) (hrate : rate < 1)
    {x : α × α} (hx : x ∉ C) (hVtop : V x ≠ ∞) :
    (∑' n : ℕ, pathKernel coupled x
      {path | (n : WithTop ℕ) < firstReturnTime C path}) < ∞ := by
  apply (hdrift.tsum_firstReturnTime_tail_le coupled hVone hx).trans_lt
  apply ENNReal.mul_lt_top
  · rw [ENNReal.inv_lt_top]
    exact tsub_pos_iff_lt.mpr hrate
  · exact lt_top_iff_ne_top.mpr hVtop

/-- With a strict geometric rate and finite initial Lyapunov value, the
killed-kernel survival mass tends to zero. -/
theorem HasGeometricDrift.tendsto_returnFailureMass_zero
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal} {C : Set (α × α)}
    {rate allowance : ENNReal}
    (hdrift : HasGeometricDrift coupled V C rate allowance)
    (hVone : ∀ x, 1 ≤ V x)
    (hrate : rate < 1)
    {x : α × α} (hx : x ∉ C) (hVtop : V x ≠ ∞) :
    Filter.Tendsto (fun n => returnFailureMass coupled C hdrift.2.1 n x)
      Filter.atTop (nhds 0) := by
  have hupper : Filter.Tendsto (fun n : ℕ => rate ^ n * V x)
      Filter.atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.mul_const
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hrate)
      (Or.inr hVtop)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    hupper (fun _ => zero_le) fun n =>
      hdrift.returnFailureMass_le coupled hVone n hx

/-- For `rate < 1`, the actual path probability of avoiding the drift set for
the next `n` steps tends to zero from every outside state with finite
Lyapunov value. -/
theorem HasGeometricDrift.tendsto_pathKernel_returnFailureEvent_zero
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal} {C : Set (α × α)}
    {rate allowance : ENNReal}
    (hdrift : HasGeometricDrift coupled V C rate allowance)
    (hVone : ∀ x, 1 ≤ V x)
    (hrate : rate < 1)
    {x : α × α} (hx : x ∉ C) (hVtop : V x ≠ ∞) :
    Filter.Tendsto
      (fun n => pathKernel coupled x (returnFailureEvent C n))
      Filter.atTop (nhds 0) := by
  have hmass := hdrift.tendsto_returnFailureMass_zero coupled hVone
    hrate hx hVtop
  exact hmass.congr' (Filter.Eventually.of_forall fun n =>
    (pathKernel_returnFailureEvent_eq_returnFailureMass coupled
      hdrift.2.1 n x).symm)

/-- Strict geometric drift makes return to `C` almost sure from every
outside state with finite Lyapunov value. -/
theorem HasGeometricDrift.pathKernel_neverReturnEvent_eq_zero
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal} {C : Set (α × α)}
    {rate allowance : ENNReal}
    (hdrift : HasGeometricDrift coupled V C rate allowance)
    (hVone : ∀ x, 1 ≤ V x)
    (hrate : rate < 1)
    {x : α × α} (hx : x ∉ C) (hVtop : V x ≠ ∞) :
    pathKernel coupled x (neverReturnEvent C) = 0 := by
  let μ := pathKernel coupled x
  have hcontinuous : Filter.Tendsto
      (μ ∘ returnFailureEvent C) Filter.atTop
      (nhds (μ (neverReturnEvent C))) := by
    simpa only [neverReturnEvent] using
      (tendsto_measure_iInter_atTop
        (μ := μ)
        (fun n => (measurableSet_returnFailureEvent hdrift.2.1 n).nullMeasurableSet)
        (antitone_returnFailureEvent C)
        ⟨0, measure_ne_top μ (returnFailureEvent C 0)⟩)
  have hzero := hdrift.tendsto_pathKernel_returnFailureEvent_zero
    coupled hVone hrate hx hVtop
  have hzero' : Filter.Tendsto (μ ∘ returnFailureEvent C)
      Filter.atTop (nhds 0) := by
    convert hzero using 1
    funext n
    rfl
  exact tendsto_nhds_unique hcontinuous hzero'

/-- Equivalently, the first positive return time is finite almost surely. -/
theorem HasGeometricDrift.pathKernel_firstReturnTime_eq_top_eq_zero
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal} {C : Set (α × α)}
    {rate allowance : ENNReal}
    (hdrift : HasGeometricDrift coupled V C rate allowance)
    (hVone : ∀ x, 1 ≤ V x)
    (hrate : rate < 1)
    {x : α × α} (hx : x ∉ C) (hVtop : V x ≠ ∞) :
    pathKernel coupled x
      {path | firstReturnTime C path = (⊤ : WithTop ℕ)} = 0 := by
  rw [← neverReturnEvent_eq_firstReturnTime_eq_top C]
  exact hdrift.pathKernel_neverReturnEvent_eq_zero coupled hVone
    hrate hx hVtop

/-- Uniform finite-step accessibility restricted to a specified starting
region. This is the state-weighted form naturally produced by drift. -/
def IsUniformlyAccessibleFrom
    (coupled : Kernel (α × α) (α × α))
    (start target : Set (α × α)) (steps : ℕ)
    (returnBound : ENNReal) : Prop :=
  ∀ x ∈ start, returnBound ≤ (coupled ^ steps) x target

/-- A one-step accessibility bound for the first branch transfers to a
mixture after multiplication by that branch's weight. -/
theorem IsUniformlyAccessibleFrom.mixture_first_one
    (p : Set.Icc (0 : NNReal) 1)
    (first second : Kernel (α × α) (α × α))
    {start target : Set (α × α)} (htarget : MeasurableSet target)
    {bound : ENNReal}
    (hfirst : IsUniformlyAccessibleFrom first start target 1 bound) :
    IsUniformlyAccessibleFrom (mixture p first second) start target 1
      ((p.1 : ENNReal) * bound) := by
  intro x hx
  rw [pow_one]
  calc
    (p.1 : ENNReal) * bound ≤ (p.1 : ENNReal) * first x target :=
      by
        simpa only [pow_one, mul_comm] using
          (mul_le_mul_left (hfirst x hx) (p.1 : ENNReal))
    _ ≤ mixture p first second x target :=
      mixture_apply_first_le p first second x htarget

/-- Uniform accessibility composes by Chapman--Kolmogorov: first reach an
intermediate set, then reach the target uniformly from that set. The two
minorization constants multiply. -/
theorem IsUniformlyAccessibleFrom.comp
    (coupled : Kernel (α × α) (α × α))
    {start middle target : Set (α × α)}
    (hmiddle : MeasurableSet middle) (htarget : MeasurableSet target)
    {firstSteps secondSteps : ℕ} {firstBound secondBound : ENNReal}
    (hfirst : IsUniformlyAccessibleFrom coupled start middle
      firstSteps firstBound)
    (hsecond : IsUniformlyAccessibleFrom coupled middle target
      secondSteps secondBound) :
    IsUniformlyAccessibleFrom coupled start target
      (firstSteps + secondSteps) (secondBound * firstBound) := by
  intro x hx
  rw [Kernel.pow_add_apply_eq_lintegral coupled firstSteps secondSteps x
    htarget]
  calc
    secondBound * firstBound ≤
        secondBound * (coupled ^ firstSteps) x middle := by
      simpa only [mul_comm] using
        (mul_le_mul_left (hfirst x hx) secondBound)
    _ = ∫⁻ _y in middle, secondBound ∂((coupled ^ firstSteps) x) := by
      rw [setLIntegral_const]
    _ ≤ ∫⁻ y in middle, (coupled ^ secondSteps) y target
          ∂((coupled ^ firstSteps) x) := by
      exact setLIntegral_mono' hmiddle fun y hy => hsecond y hy
    _ ≤ ∫⁻ y, (coupled ^ secondSteps) y target
          ∂((coupled ^ firstSteps) x) :=
      setLIntegral_le_lintegral middle _

section RelaxedAccessibility

variable [PseudoMetricSpace α] [BorelSpace α] [SecondCountableTopology α]

/-- Uniform finite-step accessibility of the relaxed diagonal from pairs in
`S`. This is the kernel-level conclusion of Xu et al.'s Proposition 4.1: the
paired state is understood as `(Xₙ,Yₙ₋₁)`. -/
def IsRelaxedMeetingAccessibleFrom
    (coupled : Kernel (α × α) (α × α)) (S : Set α)
    (δ : ℝ) (steps : ℕ) (meetingBound : ENNReal) : Prop :=
  IsUniformlyAccessibleFrom coupled (S ×ˢ S) (relaxedDiagonal δ)
    steps meetingBound

omit [BorelSpace α] [SecondCountableTopology α] in
/-- The relaxed-accessibility interface unfolds to the uniform kernel-power
bound appearing in Proposition 4.1. -/
theorem isRelaxedMeetingAccessibleFrom_iff
    (coupled : Kernel (α × α) (α × α)) (S : Set α)
    (δ : ℝ) (steps : ℕ) (meetingBound : ENNReal) :
    IsRelaxedMeetingAccessibleFrom coupled S δ steps meetingBound ↔
      ∀ x ∈ S ×ˢ S,
        meetingBound ≤ (coupled ^ steps) x (relaxedDiagonal δ) := by
  rfl

/-- Reaching a local-contractivity region and then entering the relaxed
diagonal uniformly from that region yields the Proposition 4.1 accessibility
bound. -/
theorem IsUniformlyAccessibleFrom.comp_relaxedMeeting
    (coupled : Kernel (α × α) (α × α))
    {S : Set α} {C : Set (α × α)} (hC : MeasurableSet C)
    {δ : ℝ} {returnSteps contractionSteps : ℕ}
    {returnBound contractionBound : ENNReal}
    (hreturn : IsUniformlyAccessibleFrom coupled (S ×ˢ S) C
      returnSteps returnBound)
    (hcontract : IsUniformlyAccessibleFrom coupled C (relaxedDiagonal δ)
      contractionSteps contractionBound) :
    IsRelaxedMeetingAccessibleFrom coupled S δ
      (returnSteps + contractionSteps) (contractionBound * returnBound) := by
  exact hreturn.comp coupled hC (measurableSet_relaxedDiagonal δ) hcontract

/-- Relaxed entry followed by a uniform exact-diagonal transition gives a
finite-step exact-meeting small set.  This is the explicit probabilistic
bridge between Proposition 4.1-style closeness and the RWMH exact-meeting
mechanism used in Xu et al.'s Theorem 4.1. -/
theorem IsRelaxedMeetingAccessibleFrom.isExactMeetingSmallSet_pow_add
    [MeasurableEq α]
    (coupled : Kernel (α × α) (α × α))
    {S : Set α} {δ : ℝ} {relaxedSteps exactSteps : ℕ}
    {relaxedBound exactBound : ENNReal}
    (hrelaxed : IsRelaxedMeetingAccessibleFrom coupled S δ
      relaxedSteps relaxedBound)
    (hexact : IsUniformlyAccessibleFrom coupled (relaxedDiagonal δ)
      (Set.diagonal α) exactSteps exactBound) :
    IsExactMeetingSmallSet (coupled ^ (relaxedSteps + exactSteps))
      (S ×ˢ S) (exactBound * relaxedBound) := by
  have hcombined := hrelaxed.comp coupled
    (measurableSet_relaxedDiagonal δ) measurableSet_diagonal hexact
  intro x hx
  exact hcombined x hx

/-- A uniform first-moment bound on the distance between the two output
coordinates, restricted to starting states in `C`. -/
def HasExpectedDistanceBoundOn
    (coupled : Kernel (α × α) (α × α)) (C : Set (α × α))
    (bound : ENNReal) : Prop :=
  ∀ x ∈ C,
    (∫⁻ y, ENNReal.ofReal (dist y.1 y.2) ∂coupled x) ≤ bound

/-- Kernel-level expected-distance contraction on a paired region. This is a
consequence of the paper's more parameterized Condition 1 once momentum and
trajectory-index randomness have been integrated out; it is not itself
claimed to be the verbatim condition. -/
def HasExpectedDistanceContractionOn
    (coupled : Kernel (α × α) (α × α)) (C : Set (α × α))
    (rate : ENNReal) : Prop :=
  ∀ x ∈ C,
    (∫⁻ y, ENNReal.ofReal (dist y.1 y.2) ∂coupled x) ≤
      rate * ENNReal.ofReal (dist x.1 x.2)

omit [BorelSpace α] [SecondCountableTopology α] in
/-- On a region of bounded pairwise distance, expected contraction supplies
a uniform expected-distance bound. -/
theorem HasExpectedDistanceContractionOn.hasExpectedDistanceBoundOn
    (coupled : Kernel (α × α) (α × α))
    {C : Set (α × α)} {rate : ENNReal}
    (hcontract : HasExpectedDistanceContractionOn coupled C rate)
    {diameter : ℝ} (hdiameter : ∀ x ∈ C, dist x.1 x.2 ≤ diameter) :
    HasExpectedDistanceBoundOn coupled C
      (rate * ENNReal.ofReal diameter) := by
  intro x hx
  exact (hcontract x hx).trans
    (mul_le_mul_right (ENNReal.ofReal_le_ofReal (hdiameter x hx)) rate)

/-- A uniform expected-distance bound gives a quantitative one-step chance
of entering the relaxed diagonal. This is the Markov-inequality bridge from
local contraction estimates to the accessibility premise. -/
theorem HasExpectedDistanceBoundOn.isUniformlyAccessibleFrom_relaxedDiagonal
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {C : Set (α × α)} {bound : ENNReal}
    (hbound : HasExpectedDistanceBoundOn coupled C bound)
    {δ : ℝ} (hδ : 0 < δ) :
    IsUniformlyAccessibleFrom coupled C (relaxedDiagonal δ) 1
      (1 - bound / ENNReal.ofReal δ) := by
  intro x hx
  have hd0 : ENNReal.ofReal δ ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hδ
  have hmul : ENNReal.ofReal δ * coupled x (relaxedDiagonal δ)ᶜ ≤ bound := by
    calc
      ENNReal.ofReal δ * coupled x (relaxedDiagonal δ)ᶜ =
          ∫⁻ _y in (relaxedDiagonal δ)ᶜ, ENNReal.ofReal δ ∂coupled x := by
        rw [setLIntegral_const]
      _ ≤ ∫⁻ y in (relaxedDiagonal δ)ᶜ,
          ENNReal.ofReal (dist y.1 y.2) ∂coupled x := by
        apply setLIntegral_mono' (measurableSet_relaxedDiagonal δ).compl
        intro y hy
        exact ENNReal.ofReal_le_ofReal (le_of_not_ge hy)
      _ ≤ ∫⁻ y, ENNReal.ofReal (dist y.1 y.2) ∂coupled x :=
        setLIntegral_le_lintegral _ _
      _ ≤ bound := hbound x hx
  have hcomp : coupled x (relaxedDiagonal δ)ᶜ ≤
      bound / ENNReal.ofReal δ := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hd0)
      (Or.inl ENNReal.ofReal_ne_top)]
    simpa only [mul_comm] using hmul
  rw [pow_one, ← compl_compl (relaxedDiagonal δ),
    measure_compl (measurableSet_relaxedDiagonal δ).compl
      (measure_ne_top _ _), measure_univ]
  exact tsub_le_tsub_left hcomp 1

/-- The Markov-inequality meeting constant is strictly positive when the
expected-distance budget is smaller than the relaxed radius. -/
theorem expectedDistanceRelaxedMeetingBound_pos
    {bound : ENNReal} {δ : ℝ} (hδ : 0 < δ)
    (hbound : bound < ENNReal.ofReal δ) :
    0 < 1 - bound / ENNReal.ofReal δ := by
  rw [tsub_pos_iff_lt,
    ENNReal.div_lt_iff (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr hδ))
      (Or.inl ENNReal.ofReal_ne_top)]
  simpa only [one_mul] using hbound

end RelaxedAccessibility

/-- On a region where `V ≤ B`, drift gives a uniform one-step probability of
entering the `R`-sublevel set. -/
theorem HasGeometricDrift.isUniformlyAccessibleFrom_sublevel
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal} {C start : Set (α × α)}
    {rate allowance B R : ENNReal}
    (hdrift : HasGeometricDrift coupled V C rate allowance)
    (hR0 : R ≠ 0) (hRtop : R ≠ ∞)
    (hstart : ∀ x ∈ start, V x ≤ B) :
    IsUniformlyAccessibleFrom coupled start (lyapunovSublevel V R) 1
      (1 - (rate * B + allowance) / R) := by
  intro x hx
  have hescape := hdrift.mul_measure_compl_sublevel_le coupled R x
  have hescape' : R * coupled x (lyapunovSublevel V R)ᶜ ≤
      rate * B + allowance := hescape.trans (by gcongr; exact hstart x hx)
  have hcomp : coupled x (lyapunovSublevel V R)ᶜ ≤
      (rate * B + allowance) / R := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hR0) (Or.inl hRtop)]
    simpa only [mul_comm] using hescape'
  rw [pow_one]
  rw [← compl_compl (lyapunovSublevel V R),
    measure_compl (measurableSet_lyapunovSublevel hdrift.1 R).compl
      (measure_ne_top _ _), measure_univ]
  exact tsub_le_tsub_left hcomp 1

/-- The sublevel return constant is strictly positive whenever the drift
budget on the starting region is strictly below the chosen threshold. -/
theorem sublevelReturnBound_pos
    {rate allowance B R : ENNReal}
    (hR0 : R ≠ 0) (hRtop : R ≠ ∞)
    (hbudget : rate * B + allowance < R) :
    0 < 1 - (rate * B + allowance) / R := by
  rw [tsub_pos_iff_lt,
    ENNReal.div_lt_iff (Or.inl hR0) (Or.inl hRtop)]
  simpa only [one_mul] using hbudget

/-- A named conjunction of the two substantive hypotheses used by the
meeting-time argument: recurrent drift toward `C` and a uniform chance to
meet from `C`. -/
def HasDriftAndExactMeeting
    [MeasurableEq α]
    (coupled : Kernel (α × α) (α × α))
    (V : (α × α) → ENNReal) (C : Set (α × α))
    (rate allowance meetingBound : ENNReal) : Prop :=
  HasGeometricDrift coupled V C rate allowance ∧
    IsExactMeetingSmallSet coupled C meetingBound

/-- Uniform `steps`-step accessibility of a paired set. This is the finite-
time return estimate that a drift theorem must provide. -/
def IsUniformlyAccessible
    (coupled : Kernel (α × α) (α × α))
    (C : Set (α × α)) (steps : ℕ) (returnBound : ENNReal) : Prop :=
  ∀ x, returnBound ≤ (coupled ^ steps) x C

theorem isUniformlyAccessibleFrom_univ_iff
    (coupled : Kernel (α × α) (α × α))
    (C : Set (α × α)) (steps : ℕ) (returnBound : ENNReal) :
    IsUniformlyAccessibleFrom coupled Set.univ C steps returnBound ↔
      IsUniformlyAccessible coupled C steps returnBound := by
  simp only [IsUniformlyAccessibleFrom, IsUniformlyAccessible, Set.mem_univ,
    forall_const]

/-- A return bound from `start` to a meeting set `C`, followed by its local
meeting bound, yields a skeleton meeting bound on `start`. This restricted
form is the direct consumer of Lyapunov sublevel return estimates. -/
theorem IsUniformlyAccessibleFrom.isExactMeetingSmallSet_pow_succ
    [MeasurableEq α]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {start C : Set (α × α)} (hC : MeasurableSet C)
    {steps : ℕ} {returnBound meetingBound : ENNReal}
    (hreturn : IsUniformlyAccessibleFrom coupled start C steps returnBound)
    (hmeeting : IsExactMeetingSmallSet coupled C meetingBound) :
    IsExactMeetingSmallSet (coupled ^ (steps + 1)) start
      (meetingBound * returnBound) := by
  intro x hx
  rw [Kernel.pow_succ_apply_eq_lintegral coupled steps x
    measurableSet_diagonal]
  calc
    meetingBound * returnBound ≤
        meetingBound * (coupled ^ steps) x C := by
      simpa only [mul_comm] using
        (mul_le_mul_left (hreturn x hx) meetingBound)
    _ = ∫⁻ _y in C, meetingBound ∂((coupled ^ steps) x) := by
      rw [setLIntegral_const]
    _ ≤ ∫⁻ y in C, coupled y (Set.diagonal α) ∂((coupled ^ steps) x) := by
      exact setLIntegral_mono' hC fun y hy => hmeeting y hy
    _ ≤ ∫⁻ y, coupled y (Set.diagonal α) ∂((coupled ^ steps) x) :=
      setLIntegral_le_lintegral C _

/-- Drift on a bounded-`V` starting region and exact meeting on a Lyapunov
sublevel combine into an explicit two-step meeting minorization. -/
theorem HasGeometricDrift.isExactMeetingSmallSet_pow_two_of_sublevel
    [MeasurableEq α]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal} {C start : Set (α × α)}
    {rate allowance B R meetingBound : ENNReal}
    (hdrift : HasGeometricDrift coupled V C rate allowance)
    (hR0 : R ≠ 0) (hRtop : R ≠ ∞)
    (hstart : ∀ x ∈ start, V x ≤ B)
    (hmeeting : IsExactMeetingSmallSet coupled
      (lyapunovSublevel V R) meetingBound) :
    IsExactMeetingSmallSet (coupled ^ 2) start
      (meetingBound * (1 - (rate * B + allowance) / R)) := by
  have hreturn := hdrift.isUniformlyAccessibleFrom_sublevel coupled
    hR0 hRtop hstart
  simpa only [Nat.reduceAdd] using
    hreturn.isExactMeetingSmallSet_pow_succ coupled
      (measurableSet_lyapunovSublevel hdrift.1 R) hmeeting

/-- Under a strict drift budget and a positive local meeting constant, the
two-step minorization supplied by drift is itself strictly positive. -/
theorem HasGeometricDrift.exists_pos_isExactMeetingSmallSet_pow_two
    [MeasurableEq α]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal} {C start : Set (α × α)}
    {rate allowance B R meetingBound : ENNReal}
    (hdrift : HasGeometricDrift coupled V C rate allowance)
    (hR0 : R ≠ 0) (hRtop : R ≠ ∞)
    (hbudget : rate * B + allowance < R)
    (hstart : ∀ x ∈ start, V x ≤ B)
    (hmeetingPos : 0 < meetingBound)
    (hmeeting : IsExactMeetingSmallSet coupled
      (lyapunovSublevel V R) meetingBound) :
    ∃ ε : ENNReal, 0 < ε ∧
      IsExactMeetingSmallSet (coupled ^ 2) start ε := by
  refine ⟨meetingBound * (1 - (rate * B + allowance) / R), ?_, ?_⟩
  · exact ENNReal.mul_pos hmeetingPos.ne'
      (sublevelReturnBound_pos hR0 hRtop hbudget).ne'
  · exact hdrift.isExactMeetingSmallSet_pow_two_of_sublevel coupled
      hR0 hRtop hstart hmeeting

/-- A uniform `steps`-step return bound followed by a uniform one-step meeting
bound yields a global meeting minorization for the `(steps+1)`-step skeleton.
The two constants multiply. -/
theorem IsUniformlyAccessible.isExactMeetingSmallSet_pow_succ
    [MeasurableEq α]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {C : Set (α × α)} (hC : MeasurableSet C)
    {steps : ℕ} {returnBound meetingBound : ENNReal}
    (hreturn : IsUniformlyAccessible coupled C steps returnBound)
    (hmeeting : IsExactMeetingSmallSet coupled C meetingBound) :
    IsExactMeetingSmallSet (coupled ^ (steps + 1)) Set.univ
      (meetingBound * returnBound) := by
  apply IsUniformlyAccessibleFrom.isExactMeetingSmallSet_pow_succ
    coupled hC
  · exact fun x _hx => hreturn x
  · exact hmeeting

/-- A coupled kernel is faithful after exact meeting when a diagonal input
remains on the diagonal with probability one. -/
def IsFaithful [MeasurableEq α]
    (coupled : Kernel (α × α) (α × α)) : Prop :=
  ∀ x ∈ Set.diagonal α, coupled x (Set.diagonal α) = 1

/-- Pathwise faithfulness: once the paired coordinates meet, they remain
equal at the next time. -/
def IsFaithfulPath (path : ℕ → α × α) : Prop :=
  ∀ n, (path n).1 = (path n).2 → (path (n + 1)).1 = (path (n + 1)).2

/-- Kernel-level faithfulness implies pathwise faithfulness almost surely
under every probability initial law. -/
theorem IsFaithful.ae_isFaithfulPath
    [MeasurableEq α]
    (initial : Measure (α × α)) [IsProbabilityMeasure initial]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (hfaithful : IsFaithful coupled) :
    ∀ᵐ path ∂pathLaw initial coupled, IsFaithfulPath path := by
  unfold IsFaithfulPath
  rw [ae_all_iff]
  intro n
  have hstep := pathLaw_ae_mem_succ_of_mem initial coupled
    (Set.diagonal α) measurableSet_diagonal hfaithful n
  exact hstep.mono fun path hpath heq =>
    Set.mem_diagonal_iff.mp
      (hpath (Set.mem_diagonal_iff.mpr heq))

omit [MeasurableSpace α] in
theorem IsFaithfulPath.eq_at_of_le
    {path : ℕ → α × α} (hpath : IsFaithfulPath path)
    {j n : ℕ} (hjn : j ≤ n) (hj : (path j).1 = (path j).2) :
    (path n).1 = (path n).2 := by
  induction n, hjn using Nat.le_induction with
  | base => exact hj
  | succ n _ ih => exact hpath n ih

omit [MeasurableSpace α] in
/-- For a faithful path, failure to have met by `n` is equivalent to being
off the diagonal at time `n`. -/
theorem IsFaithfulPath.mem_exactMeetingFailureEvent_iff
    {path : ℕ → α × α} (hpath : IsFaithfulPath path) (n : ℕ) :
    path ∈ exactMeetingFailureEvent n ↔ (path n).1 ≠ (path n).2 := by
  rw [Mcmc.Kernel.mem_exactMeetingFailureEvent_iff, show
    (n : WithTop ℕ) < exactMeetingTime path ↔
      ¬ exactMeetingTime path ≤ n by exact not_le.symm,
    exactMeetingTime_le_iff]
  constructor
  · intro hnot heq
    exact hnot ⟨n, ⟨Nat.zero_le n, le_rfl⟩, heq⟩
  · intro hne hmeet
    rcases hmeet with ⟨j, hj, heq⟩
    exact hne (hpath.eq_at_of_le hj.2 heq)

/-- Faithfulness is equivalently zero probability of leaving the diagonal. -/
theorem IsFaithful.offDiagonal_eq_zero
    [MeasurableEq α]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (hfaithful : IsFaithful coupled) {x : α × α}
    (hx : x ∈ Set.diagonal α) :
    coupled x (Set.diagonal α)ᶜ = 0 := by
  rw [measure_compl measurableSet_diagonal (measure_ne_top _ _),
    measure_univ, hfaithful x hx, tsub_self]

/-- Sequential composition preserves faithfulness. -/
theorem IsFaithful.comp
    [MeasurableEq α]
    (first second : Kernel (α × α) (α × α))
    [IsMarkovKernel first] [IsMarkovKernel second]
    (hfirst : IsFaithful first) (hsecond : IsFaithful second) :
    IsFaithful (second ∘ₖ first) := by
  intro x hx
  rw [Kernel.comp_apply' second first x measurableSet_diagonal]
  apply le_antisymm
  · calc
      (∫⁻ y, second y (Set.diagonal α) ∂first x) ≤
          ∫⁻ _y, 1 ∂first x := by
        apply lintegral_mono
        intro y
        calc
          second y (Set.diagonal α) ≤ second y Set.univ :=
            measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
      _ = 1 := by rw [lintegral_const, measure_univ, mul_one]
  · calc
      1 = first x (Set.diagonal α) := (hfirst x hx).symm
      _ = ∫⁻ _y in Set.diagonal α, 1 ∂first x := by
        rw [setLIntegral_const, one_mul]
      _ ≤ ∫⁻ y in Set.diagonal α,
          second y (Set.diagonal α) ∂first x := by
        apply setLIntegral_mono' measurableSet_diagonal
        intro y hy
        rw [hsecond y hy]
      _ ≤ ∫⁻ y, second y (Set.diagonal α) ∂first x :=
        setLIntegral_le_lintegral _ _

/-- Every positive kernel power of a faithful kernel is faithful. The zero
power is faithful as well because it is the identity kernel. -/
theorem IsFaithful.pow
    [MeasurableEq α]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (hfaithful : IsFaithful coupled) (n : ℕ) :
    IsFaithful (coupled ^ n) := by
  induction n with
  | zero =>
      intro x hx
      change (Measure.dirac x) (Set.diagonal α) = 1
      rw [Measure.dirac_apply' x measurableSet_diagonal,
        Set.indicator_of_mem hx]
      rfl
  | succ n ih =>
      rw [pow_succ]
      exact IsFaithful.comp coupled (coupled ^ n) hfaithful ih

/-- Off-diagonal mass of the paired chain at a finite time. -/
noncomputable def offDiagonalMassAtTime [MeasurableEq α]
    (initial : Measure (α × α))
    (coupled : Kernel (α × α) (α × α)) (n : ℕ) : ENNReal :=
  lawAtTime initial coupled n (Set.diagonal α)ᶜ

/-- Lyapunov weight used to control repeated failures to meet. -/
noncomputable def meetingWeight (V : (α × α) → ENNReal) (scale : ENNReal)
    (x : α × α) : ENNReal :=
  1 + scale * V x

theorem measurable_meetingWeight
    {V : (α × α) → ENNReal} (hV : Measurable V) (scale : ENNReal) :
    Measurable (meetingWeight V scale) :=
  measurable_const.add (measurable_const.mul hV)

/-- One-step contraction of weighted off-diagonal mass. This is the operator
form of the drift-plus-meeting renewal estimate. -/
def HasWeightedOffDiagonalContraction [MeasurableEq α]
    (coupled : Kernel (α × α) (α × α))
    (V : (α × α) → ENNReal) (scale rate : ENNReal) : Prop :=
  ∀ x ∉ Set.diagonal α,
    (∫⁻ y in (Set.diagonal α)ᶜ, meetingWeight V scale y ∂coupled x) ≤
      rate * meetingWeight V scale x

/-- One-step contraction of the Lyapunov-weighted mass that has not yet hit a
measurable target set. Unlike exact-meeting contraction, this formulation
does not require the target to be absorbing. -/
def HasWeightedTargetAvoidanceContraction
    (coupled : Kernel (α × α) (α × α)) (target : Set (α × α))
    (V : (α × α) → ENNReal) (scale rate : ENNReal) : Prop :=
  ∀ x ∉ target,
    (∫⁻ y in targetᶜ, meetingWeight V scale y ∂coupled x) ≤
      rate * meetingWeight V scale x

/-- A weighted drift inequality verified at a lower Lyapunov threshold remains
valid at every larger Lyapunov value when the target rate dominates the drift
rate. -/
theorem meetingWeight_outside_scalar_le
    {driftRate contractionRate scale threshold value : ENNReal}
    (hrates : driftRate ≤ contractionRate)
    (hthreshold :
      1 + scale * (driftRate * threshold) ≤
        contractionRate * (1 + scale * threshold))
    (hvalue : threshold ≤ value) :
    1 + scale * (driftRate * value) ≤
      contractionRate * (1 + scale * value) := by
  obtain ⟨excess, rfl⟩ := exists_add_of_le hvalue
  calc
    1 + scale * (driftRate * (threshold + excess)) =
        (1 + scale * (driftRate * threshold)) +
          scale * (driftRate * excess) := by ring
    _ ≤ contractionRate * (1 + scale * threshold) +
          scale * (contractionRate * excess) := by
      exact add_le_add hthreshold (by gcongr)
    _ = contractionRate * (1 + scale * (threshold + excess)) := by ring

/-- On an upper-bounded drift set, a single scalar budget bounds the weighted
off-diagonal expression at every state in the set. -/
theorem meetingWeight_inside_scalar_le
    {driftRate allowance meetingBound scale contractionRate bound value : ENNReal}
    (hvalue : value ≤ bound)
    (hbudget :
      (1 - meetingBound) + scale * (driftRate * bound + allowance) ≤
        contractionRate) :
    (1 - meetingBound) + scale * (driftRate * value + allowance) ≤
      contractionRate * (1 + scale * value) := by
  calc
    (1 - meetingBound) + scale * (driftRate * value + allowance) ≤
        (1 - meetingBound) + scale * (driftRate * bound + allowance) := by
      gcongr
    _ ≤ contractionRate := hbudget
    _ = contractionRate * 1 := by rw [mul_one]
    _ ≤ contractionRate * (1 + scale * value) :=
      mul_le_mul_right (le_add_right le_rfl) contractionRate

/-- A strict drift rate gives the strict outside-sublevel budget whenever the
Lyapunov threshold and weight scale are positive and finite. -/
theorem meetingWeight_outside_strict
    {driftRate scale threshold : ENNReal}
    (hdriftRate : driftRate < 1)
    (hscale0 : scale ≠ 0) (hscaleTop : scale ≠ ∞)
    (hthreshold0 : threshold ≠ 0) (hthresholdTop : threshold ≠ ∞) :
    1 + scale * (driftRate * threshold) < 1 + scale * threshold := by
  have hthreshold : driftRate * threshold < 1 * threshold :=
    ENNReal.mul_lt_mul_left hthreshold0 hthresholdTop hdriftRate
  have hscaled : scale * (driftRate * threshold) < scale * (1 * threshold) :=
    ENNReal.mul_lt_mul_right hscale0 hscaleTop hthreshold
  simpa only [one_mul] using
    (ENNReal.add_lt_add_iff_left ENNReal.one_ne_top).2 hscaled

/-- Spending strictly less than the meeting probability on weighted drift
gives the strict inside-small-set budget. -/
theorem meetingWeight_inside_strict
    {meetingBound weightedDrift : ENNReal}
    (hmeeting : meetingBound ≤ 1)
    (hweighted : weightedDrift < meetingBound) :
    (1 - meetingBound) + weightedDrift < 1 := by
  calc
    (1 - meetingBound) + weightedDrift <
        (1 - meetingBound) + meetingBound := by
      exact (ENNReal.add_lt_add_iff_left (by finiteness)).2 hweighted
    _ = 1 := tsub_add_cancel_of_le hmeeting

/-- A positive meeting constant always admits a positive finite weight scale
whose weighted drift budget is strictly smaller, provided that budget is
finite. -/
theorem exists_meetingWeight_scale
    {driftBudget meetingBound : ENNReal}
    (hbudgetTop : driftBudget ≠ ∞)
    (hmeeting : 0 < meetingBound) :
    ∃ scale : ENNReal,
      scale ≠ 0 ∧ scale ≠ ∞ ∧ scale * driftBudget < meetingBound := by
  obtain ⟨scale, hscale0, hscale⟩ :=
    ENNReal.exists_nnreal_pos_mul_lt hbudgetTop hmeeting.ne'
  refine ⟨(scale : ENNReal), ?_, ENNReal.coe_ne_top, hscale⟩
  exact ENNReal.coe_ne_zero.mpr hscale0.ne'

/-- Explicit contraction factor obtained by taking the worse of the normalized
outside-drift budget and the inside-small-set budget. -/
noncomputable def sublevelMeetingContractionRate
    (driftRate allowance meetingBound scale threshold : ENNReal) : ENNReal :=
  max
    ((1 + scale * (driftRate * threshold)) / (1 + scale * threshold))
    ((1 - meetingBound) + scale * (driftRate * threshold + allowance))

/-- Drift and exact meeting on the drift set imply weighted off-diagonal
contraction once the two resulting scalar inequalities are discharged. This
separates the probabilistic argument from the choice of Lyapunov scale and
contraction rate. -/
theorem HasGeometricDrift.hasWeightedOffDiagonalContraction_of_smallSet
    [MeasurableEq α]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal} {C : Set (α × α)}
    {driftRate allowance meetingBound scale contractionRate : ENNReal}
    (hdrift : HasGeometricDrift coupled V C driftRate allowance)
    (hmeeting : IsExactMeetingSmallSet coupled C meetingBound)
    (houtside : ∀ x ∉ C,
      1 + scale * (driftRate * V x) ≤
        contractionRate * meetingWeight V scale x)
    (hinside : ∀ x ∈ C,
      (1 - meetingBound) + scale * (driftRate * V x + allowance) ≤
        contractionRate * meetingWeight V scale x) :
    HasWeightedOffDiagonalContraction coupled V scale contractionRate := by
  intro x _hxDiagonal
  have hweight :
      (∫⁻ y in (Set.diagonal α)ᶜ, meetingWeight V scale y ∂coupled x) =
        coupled x (Set.diagonal α)ᶜ +
          scale * (∫⁻ y in (Set.diagonal α)ᶜ, V y ∂coupled x) := by
    change (∫⁻ y, 1 + scale * V y
      ∂(coupled x).restrict (Set.diagonal α)ᶜ) = _
    rw [lintegral_add_left measurable_const,
      lintegral_const, one_mul, Measure.restrict_apply_univ,
      lintegral_const_mul _ hdrift.1]
  rw [hweight]
  by_cases hxC : x ∈ C
  · calc
      coupled x (Set.diagonal α)ᶜ +
          scale * (∫⁻ y in (Set.diagonal α)ᶜ, V y ∂coupled x) ≤
          (1 - meetingBound) + scale *
            (driftRate * V x + allowance) := by
        gcongr
        · exact hmeeting.offDiagonal_le coupled hxC
        · exact (setLIntegral_le_lintegral (Set.diagonal α)ᶜ V).trans
            ((hdrift.2.2 x).trans_eq (by simp [hxC]))
      _ ≤ contractionRate * meetingWeight V scale x := hinside x hxC
  · calc
      coupled x (Set.diagonal α)ᶜ +
          scale * (∫⁻ y in (Set.diagonal α)ᶜ, V y ∂coupled x) ≤
          1 + scale * (driftRate * V x) := by
        gcongr
        · exact (measure_mono (Set.subset_univ _)).trans_eq measure_univ
        · exact (setLIntegral_le_lintegral (Set.diagonal α)ᶜ V).trans
            ((hdrift.2.2 x).trans_eq (by simp [hxC]))
      _ ≤ contractionRate * meetingWeight V scale x := houtside x hxC

/-- A lower Lyapunov bound off the drift set and an upper bound on the drift
set reduce weighted contraction to two scalar checks at the boundary values. -/
theorem HasGeometricDrift.hasWeightedOffDiagonalContraction_of_bounds
    [MeasurableEq α]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
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
          scale * (driftRate * upperBound + allowance) ≤ contractionRate) :
    HasWeightedOffDiagonalContraction coupled V scale contractionRate := by
  apply hdrift.hasWeightedOffDiagonalContraction_of_smallSet coupled hmeeting
  · intro x hx
    simpa only [meetingWeight] using
      meetingWeight_outside_scalar_le hrates houtsideBudget (hlower x hx)
  · intro x hx
    simpa only [meetingWeight] using
      meetingWeight_inside_scalar_le (hupper x hx) hinsideBudget

/-- For a Lyapunov sublevel drift set, the lower and upper boundary bounds are
automatic, leaving only two scalar inequalities at the common threshold. -/
theorem HasGeometricDrift.hasWeightedOffDiagonalContraction_of_sublevel
    [MeasurableEq α]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal}
    {driftRate allowance meetingBound scale contractionRate threshold : ENNReal}
    (hdrift : HasGeometricDrift coupled V (lyapunovSublevel V threshold)
      driftRate allowance)
    (hmeeting : IsExactMeetingSmallSet coupled
      (lyapunovSublevel V threshold) meetingBound)
    (hrates : driftRate ≤ contractionRate)
    (houtsideBudget :
      1 + scale * (driftRate * threshold) ≤
        contractionRate * (1 + scale * threshold))
    (hinsideBudget :
      (1 - meetingBound) +
          scale * (driftRate * threshold + allowance) ≤ contractionRate) :
    HasWeightedOffDiagonalContraction coupled V scale contractionRate := by
  apply hdrift.hasWeightedOffDiagonalContraction_of_bounds coupled hmeeting
    hrates
  · intro x hx
    exact le_of_not_ge hx
  · intro x hx
    exact hx
  · exact houtsideBudget
  · exact hinsideBudget

/-- Sublevel drift plus a uniform one-step probability of hitting an arbitrary
measurable target gives weighted contraction of the target-avoidance kernel.
This is the renewal estimate needed for relaxed (nonabsorbing) meeting sets. -/
theorem HasGeometricDrift.hasWeightedTargetAvoidanceContraction_of_sublevel
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal} {target : Set (α × α)}
    (htarget : MeasurableSet target)
    {driftRate allowance entryBound scale contractionRate threshold : ENNReal}
    (hdrift : HasGeometricDrift coupled V (lyapunovSublevel V threshold)
      driftRate allowance)
    (hentry : ∀ x ∈ lyapunovSublevel V threshold,
      entryBound ≤ coupled x target)
    (hrates : driftRate ≤ contractionRate)
    (houtsideBudget :
      1 + scale * (driftRate * threshold) ≤
        contractionRate * (1 + scale * threshold))
    (hinsideBudget :
      (1 - entryBound) +
          scale * (driftRate * threshold + allowance) ≤ contractionRate) :
    HasWeightedTargetAvoidanceContraction coupled target V scale
      contractionRate := by
  intro x _hxTarget
  have hweight :
      (∫⁻ y in targetᶜ, meetingWeight V scale y ∂coupled x) =
        coupled x targetᶜ +
          scale * (∫⁻ y in targetᶜ, V y ∂coupled x) := by
    change (∫⁻ y, 1 + scale * V y ∂(coupled x).restrict targetᶜ) = _
    rw [lintegral_add_left measurable_const,
      lintegral_const, one_mul, Measure.restrict_apply_univ,
      lintegral_const_mul _ hdrift.1]
  rw [hweight]
  by_cases hxC : x ∈ lyapunovSublevel V threshold
  · have htargetCompl : coupled x targetᶜ ≤ 1 - entryBound := by
      rw [measure_compl htarget (measure_ne_top _ _), measure_univ]
      exact tsub_le_tsub_left (hentry x hxC) 1
    calc
      coupled x targetᶜ + scale * (∫⁻ y in targetᶜ, V y ∂coupled x) ≤
          (1 - entryBound) +
            scale * (driftRate * V x + allowance) := by
        apply add_le_add htargetCompl
        simpa only [mul_comm] using mul_le_mul_right
          ((setLIntegral_le_lintegral targetᶜ V).trans
            ((hdrift.2.2 x).trans_eq (by simp [hxC]))) scale
      _ ≤ contractionRate * meetingWeight V scale x := by
        simpa only [meetingWeight] using
          meetingWeight_inside_scalar_le hxC hinsideBudget
  · calc
      coupled x targetᶜ + scale * (∫⁻ y in targetᶜ, V y ∂coupled x) ≤
          1 + scale * (driftRate * V x) := by
        apply add_le_add
        · exact (measure_mono (Set.subset_univ _)).trans_eq measure_univ
        · simpa only [mul_comm] using mul_le_mul_right
            ((setLIntegral_le_lintegral targetᶜ V).trans
              ((hdrift.2.2 x).trans_eq (by simp [hxC]))) scale
      _ ≤ contractionRate * meetingWeight V scale x := by
        simpa only [meetingWeight] using
          meetingWeight_outside_scalar_le hrates houtsideBudget
            (le_of_not_ge hxC)

/-- Iterating a weighted target-avoidance contraction gives geometric decay
of the weighted mass of the kernel killed on entry to the target. -/
theorem HasWeightedTargetAvoidanceContraction.lintegral_pow_restrict_compl_le
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {target : Set (α × α)} (htarget : MeasurableSet target)
    {V : (α × α) → ENNReal} (hV : Measurable V)
    {scale rate : ENNReal}
    (hcontract : HasWeightedTargetAvoidanceContraction coupled target V
      scale rate)
    (n : ℕ) {x : α × α} (hx : x ∉ target) :
    (∫⁻ y, meetingWeight V scale y
      ∂((coupled.restrict htarget.compl) ^ n) x) ≤
        rate ^ n * meetingWeight V scale x := by
  induction n generalizing x with
  | zero =>
      rw [pow_zero]
      rw [show (1 : Kernel (α × α) (α × α)) = Kernel.id from rfl,
        Kernel.id_apply, lintegral_dirac' x
          (measurable_meetingWeight hV scale), pow_zero, one_mul]
  | succ n ih =>
      rw [pow_succ]
      change
        (∫⁻ z, meetingWeight V scale z
          ∂(((coupled.restrict htarget.compl) ^ n) ∘ₖ
            coupled.restrict htarget.compl) x) ≤
          rate ^ (n + 1) * meetingWeight V scale x
      rw [Kernel.lintegral_comp _ _ _ (measurable_meetingWeight hV scale),
        Kernel.lintegral_restrict]
      calc
        (∫⁻ y in targetᶜ,
            ∫⁻ z, meetingWeight V scale z
              ∂((coupled.restrict htarget.compl) ^ n) y ∂coupled x) ≤
            ∫⁻ y in targetᶜ,
              rate ^ n * meetingWeight V scale y ∂coupled x := by
          apply setLIntegral_mono' htarget.compl
          intro y hy
          exact ih hy
        _ = rate ^ n *
            ∫⁻ y in targetᶜ, meetingWeight V scale y ∂coupled x := by
          rw [lintegral_const_mul _ (measurable_meetingWeight hV scale)]
        _ ≤ rate ^ n * (rate * meetingWeight V scale x) := by
          gcongr
          exact hcontract x hx
        _ = rate ^ (n + 1) * meetingWeight V scale x := by
          rw [pow_succ]
          ac_rfl

/-- Weighted target-avoidance contraction gives a geometric bound for the
actual path probability of avoiding the target at times `1,…,n`. -/
theorem HasWeightedTargetAvoidanceContraction.pathKernel_returnFailureEvent_le
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {target : Set (α × α)} (htarget : MeasurableSet target)
    {V : (α × α) → ENNReal} (hV : Measurable V)
    {scale rate : ENNReal}
    (hcontract : HasWeightedTargetAvoidanceContraction coupled target V
      scale rate)
    (n : ℕ) {x : α × α} (hx : x ∉ target) :
    pathKernel coupled x (returnFailureEvent target n) ≤
      rate ^ n * meetingWeight V scale x := by
  rw [pathKernel_returnFailureEvent_eq_returnFailureMass coupled htarget n x]
  apply le_trans _
    (hcontract.lintegral_pow_restrict_compl_le coupled htarget hV n hx)
  rw [returnFailureMass, ← lintegral_one]
  apply lintegral_mono
  intro y
  exact le_add_right le_rfl

/-- Strict scalar budgets give a subunit weighted contraction for avoidance of
an arbitrary measurable target that is hit uniformly from the drift sublevel. -/
theorem HasGeometricDrift.sublevelTargetContractionRate_lt_one_and_contracts
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal} {target : Set (α × α)}
    (htarget : MeasurableSet target)
    {driftRate allowance entryBound scale threshold : ENNReal}
    (hdrift : HasGeometricDrift coupled V (lyapunovSublevel V threshold)
      driftRate allowance)
    (hentry : ∀ x ∈ lyapunovSublevel V threshold,
      entryBound ≤ coupled x target)
    (hdriftRate : driftRate ≤ 1)
    (hscaleTop : scale ≠ ∞) (hthresholdTop : threshold ≠ ∞)
    (houtsideStrict :
      1 + scale * (driftRate * threshold) < 1 + scale * threshold)
    (hinsideStrict :
      (1 - entryBound) +
          scale * (driftRate * threshold + allowance) < 1) :
    sublevelMeetingContractionRate driftRate allowance entryBound scale
        threshold < 1 ∧
      HasWeightedTargetAvoidanceContraction coupled target V scale
        (sublevelMeetingContractionRate driftRate allowance entryBound scale
          threshold) := by
  let denominator := 1 + scale * threshold
  let outsideNumerator := 1 + scale * (driftRate * threshold)
  let insideBudget :=
    (1 - entryBound) + scale * (driftRate * threshold + allowance)
  let contractionRate :=
    sublevelMeetingContractionRate driftRate allowance entryBound scale threshold
  have hdenominator0 : denominator ≠ 0 := by
    exact ne_of_gt (zero_lt_one.trans_le (le_add_right le_rfl))
  have hdenominatorTop : denominator ≠ ∞ := by
    exact ENNReal.add_ne_top.2
      ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top hscaleTop hthresholdTop⟩
  have houtsideRateLt : outsideNumerator / denominator < 1 := by
    rw [ENNReal.div_lt_iff (Or.inl hdenominator0) (Or.inl hdenominatorTop)]
    simpa only [one_mul] using houtsideStrict
  have hcontractionLt : contractionRate < 1 :=
    max_lt houtsideRateLt hinsideStrict
  refine ⟨hcontractionLt, ?_⟩
  apply hdrift.hasWeightedTargetAvoidanceContraction_of_sublevel
    coupled htarget hentry
  · have hdriftOutsideRate : driftRate ≤ outsideNumerator / denominator := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl hdenominator0)
        (Or.inl hdenominatorTop)]
      calc
        driftRate * denominator =
            driftRate + scale * (driftRate * threshold) := by
          dsimp only [denominator]
          ring
        _ ≤ 1 + scale * (driftRate * threshold) := by
          simpa only [add_comm] using
            add_le_add_right hdriftRate (scale * (driftRate * threshold))
        _ = outsideNumerator := rfl
    exact hdriftOutsideRate.trans (by
      dsimp only [contractionRate, sublevelMeetingContractionRate]
      exact le_max_left _ _)
  · calc
      outsideNumerator =
          outsideNumerator / denominator * denominator :=
        (ENNReal.div_mul_cancel hdenominator0 hdenominatorTop).symm
      _ ≤ contractionRate * denominator := by
        have hrate : outsideNumerator / denominator ≤ contractionRate := by
          dsimp only [contractionRate, sublevelMeetingContractionRate]
          exact le_max_left _ _
        simpa only [mul_comm] using mul_le_mul_right hrate denominator
  · dsimp only [contractionRate, insideBudget,
      sublevelMeetingContractionRate]
    exact le_max_right _ _

/-- The standard positive-entry weighted-drift budget specializes the target
contraction theorem without exposing its two scalar inequalities. -/
theorem HasGeometricDrift.sublevelTargetContractionRate_lt_one_and_contracts_of_budget
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal} {target : Set (α × α)}
    (htarget : MeasurableSet target)
    {driftRate allowance entryBound scale threshold : ENNReal}
    (hdrift : HasGeometricDrift coupled V (lyapunovSublevel V threshold)
      driftRate allowance)
    (hentry : ∀ x ∈ lyapunovSublevel V threshold,
      entryBound ≤ coupled x target)
    (hdriftRate : driftRate < 1) (hentryBound : entryBound ≤ 1)
    (hscale0 : scale ≠ 0) (hscaleTop : scale ≠ ∞)
    (hthreshold0 : threshold ≠ 0) (hthresholdTop : threshold ≠ ∞)
    (hbudget : scale * (driftRate * threshold + allowance) < entryBound) :
    sublevelMeetingContractionRate driftRate allowance entryBound scale
        threshold < 1 ∧
      HasWeightedTargetAvoidanceContraction coupled target V scale
        (sublevelMeetingContractionRate driftRate allowance entryBound scale
          threshold) := by
  apply hdrift.sublevelTargetContractionRate_lt_one_and_contracts
    coupled htarget hentry hdriftRate.le hscaleTop hthresholdTop
  · exact meetingWeight_outside_strict hdriftRate hscale0 hscaleTop
      hthreshold0 hthresholdTop
  · exact meetingWeight_inside_strict hentryBound hbudget

/-- Positive target-entry mass and a finite sublevel drift budget construct a
weighted target-avoidance contraction certificate with a subunit rate. -/
theorem HasGeometricDrift.exists_scale_rate_targetAvoidanceContraction
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal} {target : Set (α × α)}
    (htarget : MeasurableSet target)
    {driftRate allowance entryBound threshold : ENNReal}
    (hdrift : HasGeometricDrift coupled V (lyapunovSublevel V threshold)
      driftRate allowance)
    (hentry : ∀ x ∈ lyapunovSublevel V threshold,
      entryBound ≤ coupled x target)
    (hdriftRate : driftRate < 1)
    (hentryPos : 0 < entryBound) (hentryBound : entryBound ≤ 1)
    (hthreshold0 : threshold ≠ 0) (hthresholdTop : threshold ≠ ∞)
    (hdriftBudgetTop : driftRate * threshold + allowance ≠ ∞) :
    ∃ scale contractionRate : ENNReal,
      scale ≠ 0 ∧ scale ≠ ∞ ∧ contractionRate < 1 ∧
        HasWeightedTargetAvoidanceContraction coupled target V scale
          contractionRate := by
  obtain ⟨scale, hscale0, hscaleTop, hbudget⟩ :=
    exists_meetingWeight_scale hdriftBudgetTop hentryPos
  let contractionRate := sublevelMeetingContractionRate driftRate allowance
    entryBound scale threshold
  obtain ⟨hrate, hcontract⟩ :=
    hdrift.sublevelTargetContractionRate_lt_one_and_contracts_of_budget
      coupled htarget hentry hdriftRate hentryBound hscale0 hscaleTop
      hthreshold0 hthresholdTop hbudget
  exact ⟨scale, contractionRate, hscale0, hscaleTop, hrate, hcontract⟩

/-- Positive relaxed-entry mass on a drift sublevel and a finite drift budget
automatically produce a positive finite weight scale, a subunit rate, and a
geometric bound for the actual first-hitting tail of the target. -/
theorem HasGeometricDrift.exists_scale_rate_targetHittingTail_pathKernel_le
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal} {target : Set (α × α)}
    (htarget : MeasurableSet target)
    {driftRate allowance entryBound threshold : ENNReal}
    (hdrift : HasGeometricDrift coupled V (lyapunovSublevel V threshold)
      driftRate allowance)
    (hentry : ∀ x ∈ lyapunovSublevel V threshold,
      entryBound ≤ coupled x target)
    (hdriftRate : driftRate < 1)
    (hentryPos : 0 < entryBound) (hentryBound : entryBound ≤ 1)
    (hthreshold0 : threshold ≠ 0) (hthresholdTop : threshold ≠ ∞)
    (hdriftBudgetTop : driftRate * threshold + allowance ≠ ∞)
    (x : α × α) (hx : x ∉ target) (hVxTop : V x ≠ ∞) :
    ∃ scale contractionRate : ENNReal,
      scale ≠ 0 ∧ scale ≠ ∞ ∧ contractionRate < 1 ∧
        meetingWeight V scale x ≠ ∞ ∧
          ∀ n : ℕ,
            pathKernel coupled x (returnFailureEvent target n) ≤
              contractionRate ^ n * meetingWeight V scale x := by
  obtain ⟨scale, hscale0, hscaleTop, hbudget⟩ :=
    exists_meetingWeight_scale hdriftBudgetTop hentryPos
  let contractionRate := sublevelMeetingContractionRate driftRate allowance
    entryBound scale threshold
  obtain ⟨hrate, hcontract⟩ :=
    hdrift.sublevelTargetContractionRate_lt_one_and_contracts_of_budget
      coupled htarget hentry hdriftRate hentryBound hscale0 hscaleTop
      hthreshold0 hthresholdTop hbudget
  have hweightTop : meetingWeight V scale x ≠ ∞ := by
    exact ENNReal.add_ne_top.2
      ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top hscaleTop hVxTop⟩
  refine ⟨scale, contractionRate, hscale0, hscaleTop, hrate, hweightTop, ?_⟩
  intro n
  exact hcontract.pathKernel_returnFailureEvent_le coupled htarget hdrift.1 n hx

/-- Strict scalar budgets produce an explicit subunit contraction factor for
a Lyapunov-sublevel meeting set. -/
theorem HasGeometricDrift.sublevelMeetingContractionRate_lt_one_and_contracts
    [MeasurableEq α]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal}
    {driftRate allowance meetingBound scale threshold : ENNReal}
    (hdrift : HasGeometricDrift coupled V (lyapunovSublevel V threshold)
      driftRate allowance)
    (hmeeting : IsExactMeetingSmallSet coupled
      (lyapunovSublevel V threshold) meetingBound)
    (hdriftRate : driftRate ≤ 1)
    (hscaleTop : scale ≠ ∞)
    (hthresholdTop : threshold ≠ ∞)
    (houtsideStrict :
      1 + scale * (driftRate * threshold) < 1 + scale * threshold)
    (hinsideStrict :
      (1 - meetingBound) +
          scale * (driftRate * threshold + allowance) < 1) :
    sublevelMeetingContractionRate driftRate allowance meetingBound scale
        threshold < 1 ∧
      HasWeightedOffDiagonalContraction coupled V scale
        (sublevelMeetingContractionRate driftRate allowance meetingBound scale
          threshold) := by
  let denominator := 1 + scale * threshold
  let outsideNumerator := 1 + scale * (driftRate * threshold)
  let insideBudget :=
    (1 - meetingBound) + scale * (driftRate * threshold + allowance)
  let contractionRate :=
    sublevelMeetingContractionRate driftRate allowance meetingBound scale threshold
  have hdenominator0 : denominator ≠ 0 := by
    exact ne_of_gt (zero_lt_one.trans_le (le_add_right le_rfl))
  have hdenominatorTop : denominator ≠ ∞ := by
    exact ENNReal.add_ne_top.2
      ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top hscaleTop hthresholdTop⟩
  have houtsideRateLt : outsideNumerator / denominator < 1 := by
    rw [ENNReal.div_lt_iff (Or.inl hdenominator0) (Or.inl hdenominatorTop)]
    simpa only [one_mul] using houtsideStrict
  have hcontractionLt : contractionRate < 1 := by
    exact max_lt houtsideRateLt hinsideStrict
  refine ⟨hcontractionLt, ?_⟩
  apply hdrift.hasWeightedOffDiagonalContraction_of_sublevel coupled hmeeting
  · have hdriftOutsideRate : driftRate ≤ outsideNumerator / denominator := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl hdenominator0)
        (Or.inl hdenominatorTop)]
      calc
        driftRate * denominator =
            driftRate + scale * (driftRate * threshold) := by
          dsimp only [denominator]
          ring
        _ ≤ 1 + scale * (driftRate * threshold) := by
          simpa only [add_comm] using
            add_le_add_right hdriftRate (scale * (driftRate * threshold))
        _ = outsideNumerator := rfl
    exact hdriftOutsideRate.trans (by
      dsimp only [contractionRate, sublevelMeetingContractionRate]
      exact le_max_left _ _)
  · calc
      outsideNumerator =
          outsideNumerator / denominator * denominator :=
        (ENNReal.div_mul_cancel hdenominator0 hdenominatorTop).symm
      _ ≤ contractionRate * denominator := by
        have hrate : outsideNumerator / denominator ≤ contractionRate := by
          dsimp only [contractionRate, sublevelMeetingContractionRate]
          exact le_max_left _ _
        simpa only [mul_comm] using mul_le_mul_right hrate denominator
  · dsimp only [contractionRate, insideBudget,
      sublevelMeetingContractionRate]
    exact le_max_right _ _

/-- Standard strict drift and meeting-budget hypotheses imply explicit
subunit weighted contraction without requiring expanded scalar inequalities. -/
theorem HasGeometricDrift.sublevelMeetingContractionRate_lt_one_and_contracts_of_budget
    [MeasurableEq α]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal}
    {driftRate allowance meetingBound scale threshold : ENNReal}
    (hdrift : HasGeometricDrift coupled V (lyapunovSublevel V threshold)
      driftRate allowance)
    (hmeeting : IsExactMeetingSmallSet coupled
      (lyapunovSublevel V threshold) meetingBound)
    (hdriftRate : driftRate < 1)
    (hmeetingBound : meetingBound ≤ 1)
    (hscale0 : scale ≠ 0) (hscaleTop : scale ≠ ∞)
    (hthreshold0 : threshold ≠ 0) (hthresholdTop : threshold ≠ ∞)
    (hbudget :
      scale * (driftRate * threshold + allowance) < meetingBound) :
    sublevelMeetingContractionRate driftRate allowance meetingBound scale
        threshold < 1 ∧
      HasWeightedOffDiagonalContraction coupled V scale
        (sublevelMeetingContractionRate driftRate allowance meetingBound scale
          threshold) := by
  apply hdrift.sublevelMeetingContractionRate_lt_one_and_contracts coupled hmeeting
  · exact hdriftRate.le
  · exact hscaleTop
  · exact hthresholdTop
  · exact meetingWeight_outside_strict hdriftRate hscale0 hscaleTop
      hthreshold0 hthresholdTop
  · exact meetingWeight_inside_strict hmeetingBound hbudget

/-- Weighted off-diagonal mass of the paired chain at time `n`. -/
noncomputable def weightedOffDiagonalMassAtTime [MeasurableEq α]
    (initial : Measure (α × α))
    (coupled : Kernel (α × α) (α × α))
    (V : (α × α) → ENNReal) (scale : ENNReal) (n : ℕ) : ENNReal :=
  ∫⁻ x in (Set.diagonal α)ᶜ, meetingWeight V scale x
    ∂lawAtTime initial coupled n

/-- From a deterministic initial pair, the time-zero weighted off-diagonal
mass is the meeting weight when the pair is unequal and zero otherwise. -/
theorem weightedOffDiagonalMassAtTime_dirac_zero
    [MeasurableEq α]
    (coupled : Kernel (α × α) (α × α))
    {V : (α × α) → ENNReal} (hV : Measurable V)
    (scale : ENNReal) (x : α × α) :
    weightedOffDiagonalMassAtTime (Measure.dirac x) coupled V scale 0 =
      (Set.diagonal α)ᶜ.indicator (meetingWeight V scale) x := by
  classical
  rw [weightedOffDiagonalMassAtTime, lawAtTime_zero,
    setLIntegral_dirac' (measurable_meetingWeight hV scale)
      measurableSet_diagonal.compl]
  by_cases hx : x ∈ (Set.diagonal α)ᶜ <;> simp [hx]

/-- The deterministic time-zero weighted mass is bounded by the explicit
meeting weight at the initial pair. -/
theorem weightedOffDiagonalMassAtTime_dirac_zero_le
    [MeasurableEq α]
    (coupled : Kernel (α × α) (α × α))
    {V : (α × α) → ENNReal} (hV : Measurable V)
    (scale : ENNReal) (x : α × α) :
    weightedOffDiagonalMassAtTime (Measure.dirac x) coupled V scale 0 ≤
      meetingWeight V scale x := by
  rw [weightedOffDiagonalMassAtTime_dirac_zero coupled hV scale x]
  by_cases hx : x ∈ (Set.diagonal α)ᶜ <;> simp [hx]

/-- Faithfulness and weighted operator contraction give one-step contraction
of weighted off-diagonal mass. -/
theorem weightedOffDiagonalMassAtTime_succ_le
    [MeasurableEq α]
    (initial : Measure (α × α)) [IsProbabilityMeasure initial]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal} (hV : Measurable V)
    (scale rate : ENNReal)
    (hfaithful : IsFaithful coupled)
    (hcontract : HasWeightedOffDiagonalContraction coupled V scale rate)
    (n : ℕ) :
    weightedOffDiagonalMassAtTime initial coupled V scale (n + 1) ≤
      rate * weightedOffDiagonalMassAtTime initial coupled V scale n := by
  let W := meetingWeight V scale
  have hW : Measurable W := measurable_meetingWeight hV scale
  have hIndicatorW : Measurable ((Set.diagonal α)ᶜ.indicator W) :=
    hW.indicator measurableSet_diagonal.compl
  rw [weightedOffDiagonalMassAtTime, lawAtTime_succ]
  rw [← lintegral_indicator measurableSet_diagonal.compl W]
  change (∫⁻ y, (Set.diagonal α)ᶜ.indicator W y
    ∂coupled ∘ₘ lawAtTime initial coupled n) ≤ _
  rw [Measure.lintegral_bind coupled.aemeasurable hIndicatorW.aemeasurable]
  calc
    (∫⁻ x, ∫⁻ y, (Set.diagonal α)ᶜ.indicator W y ∂coupled x
        ∂lawAtTime initial coupled n) ≤
        ∫⁻ x, (Set.diagonal α)ᶜ.indicator
          (fun x => rate * W x) x ∂lawAtTime initial coupled n := by
      apply lintegral_mono
      intro x
      change (∫⁻ y, (Set.diagonal α)ᶜ.indicator W y ∂coupled x) ≤ _
      rw [lintegral_indicator measurableSet_diagonal.compl W]
      by_cases hx : x ∈ Set.diagonal α
      · rw [Set.indicator_of_notMem
          (show x ∉ (Set.diagonal α)ᶜ by exact fun hxc => hxc hx)]
        have hz := hfaithful.offDiagonal_eq_zero coupled hx
        rw [← Measure.restrict_eq_zero] at hz
        rw [show (∫⁻ y in (Set.diagonal α)ᶜ, W y ∂coupled x) = 0 by
          rw [hz, lintegral_zero_measure]]
      · rw [Set.indicator_of_mem (show x ∈ (Set.diagonal α)ᶜ by exact hx)]
        exact hcontract x hx
    _ = rate * weightedOffDiagonalMassAtTime initial coupled V scale n := by
      rw [lintegral_indicator measurableSet_diagonal.compl
        (fun x => rate * W x),
        lintegral_const_mul _ hW]
      rfl

/-- Iterating weighted off-diagonal contraction gives geometric decay of the
weighted mass. -/
theorem weightedOffDiagonalMassAtTime_le
    [MeasurableEq α]
    (initial : Measure (α × α)) [IsProbabilityMeasure initial]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal} (hV : Measurable V)
    (scale rate : ENNReal)
    (hfaithful : IsFaithful coupled)
    (hcontract : HasWeightedOffDiagonalContraction coupled V scale rate)
    (n : ℕ) :
    weightedOffDiagonalMassAtTime initial coupled V scale n ≤
      rate ^ n * weightedOffDiagonalMassAtTime initial coupled V scale 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        weightedOffDiagonalMassAtTime initial coupled V scale (n + 1) ≤
            rate * weightedOffDiagonalMassAtTime initial coupled V scale n :=
          weightedOffDiagonalMassAtTime_succ_le initial coupled hV scale rate
            hfaithful hcontract n
        _ ≤ rate * (rate ^ n *
            weightedOffDiagonalMassAtTime initial coupled V scale 0) :=
          mul_le_mul_right ih rate
        _ = rate ^ (n + 1) *
            weightedOffDiagonalMassAtTime initial coupled V scale 0 := by
          rw [pow_succ]
          ac_rfl

/-- Since the Lyapunov weight is at least one, ordinary off-diagonal mass is
bounded by weighted off-diagonal mass. -/
theorem offDiagonalMassAtTime_le_weightedOffDiagonalMassAtTime
    [MeasurableEq α]
    (initial : Measure (α × α))
    (coupled : Kernel (α × α) (α × α))
    (V : (α × α) → ENNReal) (scale : ENNReal) (n : ℕ) :
    offDiagonalMassAtTime initial coupled n ≤
      weightedOffDiagonalMassAtTime initial coupled V scale n := by
  rw [offDiagonalMassAtTime, ← setLIntegral_one]
  apply setLIntegral_mono'
  · exact measurableSet_diagonal.compl
  · intro x _hx
    exact le_add_right le_rfl

/-- The exact meeting-time tail of the verified homogeneous path law is
bounded by the corresponding finite-time off-diagonal mass. -/
theorem exactMeetingTail_pathLaw_le_offDiagonalMassAtTime
    [MeasurableEq α]
    (initial : Measure (α × α))
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (n : ℕ) :
    exactMeetingTail (pathLaw initial coupled) n ≤
      offDiagonalMassAtTime initial coupled n := by
  apply (exactMeetingTail_le_map_offDiagonal (pathLaw initial coupled) n).trans_eq
  rw [pathLaw_map_atTime]
  rfl

section RelaxedPathLaw

variable [PseudoMetricSpace α] [BorelSpace α] [SecondCountableTopology α]

/-- Weighted avoidance contraction for the relaxed diagonal gives a geometric
bound for the paired-state relaxed meeting tail. The starting pair is assumed
outside the target; starts already inside have zero tail from time zero. -/
theorem HasWeightedTargetAvoidanceContraction.relaxedPairMeetingTail_pathKernel_le
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal} (hV : Measurable V)
    {scale rate : ENNReal} {δ : ℝ}
    (hcontract : HasWeightedTargetAvoidanceContraction coupled
      (relaxedDiagonal δ) V scale rate)
    (x : α × α) (hx : x ∉ relaxedDiagonal δ) (n : ℕ) :
    relaxedPairMeetingTail (pathKernel coupled x) δ n ≤
      rate ^ n * meetingWeight V scale x := by
  calc
    relaxedPairMeetingTail (pathKernel coupled x) δ n ≤
        pathKernel coupled x (returnFailureEvent (relaxedDiagonal δ) n) := by
      apply measure_mono
      intro path hfail
      rw [mem_returnFailureEvent_iff]
      intro j hj1 hjn hclose
      apply hfail
      exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hjn), hclose⟩⟩
    _ ≤ rate ^ n * meetingWeight V scale x :=
      hcontract.pathKernel_returnFailureEvent_le coupled
        (measurableSet_relaxedDiagonal δ) hV n hx

/-- A path initialized inside the relaxed diagonal has zero paired-state
relaxed failure probability at every horizon because time zero is tested. -/
theorem pathKernel_relaxedPairMeetingFailureEvent_eq_zero_of_mem
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {δ : ℝ} {x : α × α} (hx : x ∈ relaxedDiagonal δ) (n : ℕ) :
    pathKernel coupled x (relaxedPairMeetingFailureEvent δ n) = 0 := by
  apply le_zero_iff.mp
  calc
    pathKernel coupled x (relaxedPairMeetingFailureEvent δ n) ≤
        pathKernel coupled x
          ((fun path : ℕ → α × α => path 0) ⁻¹' (relaxedDiagonal δ)ᶜ) :=
      measure_mono (by
        intro path hfail hclose
        apply hfail
        exact Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr
          ⟨Finset.mem_range.mpr (Nat.zero_lt_succ n), hclose⟩⟩)
    _ = ((pathKernel coupled).map (fun path => path 0) x)
        (relaxedDiagonal δ)ᶜ := by
      rw [Kernel.map_apply _ (measurable_pi_apply (0 : ℕ)) x]
      exact (Measure.map_apply
        (μ := pathKernel coupled x) (measurable_pi_apply (0 : ℕ))
        (measurableSet_relaxedDiagonal δ).compl).symm
    _ = (Measure.dirac x) (relaxedDiagonal δ)ᶜ := by
      rw [pathKernel_map_atTime, pow_zero]
      rfl
    _ = 0 := by
      rw [Measure.dirac_apply' x (measurableSet_relaxedDiagonal δ).compl,
        Set.indicator_of_notMem]
      exact fun hxc => hxc hx

/-- Initial-law version of the weighted relaxed-target theorem. Its finite
multiplicative constant is the initial weighted mass outside the relaxed
diagonal. -/
theorem HasWeightedTargetAvoidanceContraction.relaxedPairMeetingTail_pathLaw_le
    (initial : Measure (α × α))
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal} (hV : Measurable V)
    {scale rate : ENNReal} {δ : ℝ}
    (hcontract : HasWeightedTargetAvoidanceContraction coupled
      (relaxedDiagonal δ) V scale rate)
    (n : ℕ) :
    relaxedPairMeetingTail (pathLaw initial coupled) δ n ≤
      rate ^ n *
        (∫⁻ x in (relaxedDiagonal δ)ᶜ, meetingWeight V scale x ∂initial) := by
  rw [relaxedPairMeetingTail, pathLaw,
    Measure.bind_apply (measurableSet_relaxedPairMeetingFailureEvent δ n)
      (pathKernel coupled).aemeasurable]
  calc
    (∫⁻ x, pathKernel coupled x (relaxedPairMeetingFailureEvent δ n)
        ∂initial) ≤
        ∫⁻ x, (relaxedDiagonal δ)ᶜ.indicator
          (fun x => rate ^ n * meetingWeight V scale x) x ∂initial := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ relaxedDiagonal δ
      · change pathKernel coupled x (relaxedPairMeetingFailureEvent δ n) ≤ _
        rw [pathKernel_relaxedPairMeetingFailureEvent_eq_zero_of_mem
          coupled hx n]
        simp [hx]
      · rw [Set.indicator_of_mem (show x ∈ (relaxedDiagonal δ)ᶜ from hx)]
        exact hcontract.relaxedPairMeetingTail_pathKernel_le coupled hV x hx n
    _ = ∫⁻ x in (relaxedDiagonal δ)ᶜ,
          rate ^ n * meetingWeight V scale x ∂initial := by
      rw [lintegral_indicator (measurableSet_relaxedDiagonal δ).compl]
    _ = rate ^ n *
        (∫⁻ x in (relaxedDiagonal δ)ᶜ, meetingWeight V scale x ∂initial) := by
      rw [lintegral_const_mul _ (measurable_meetingWeight hV scale)]

/-- Drift and positive relaxed entry on a Lyapunov sublevel construct a
subunit geometric relaxed-meeting tail for an arbitrary initial paired law. -/
theorem HasGeometricDrift.exists_scale_rate_relaxedPairMeetingTail_pathLaw_le
    (initial : Measure (α × α))
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal} {δ : ℝ}
    {driftRate allowance entryBound threshold : ENNReal}
    (hdrift : HasGeometricDrift coupled V (lyapunovSublevel V threshold)
      driftRate allowance)
    (hentry : ∀ x ∈ lyapunovSublevel V threshold,
      entryBound ≤ coupled x (relaxedDiagonal δ))
    (hdriftRate : driftRate < 1)
    (hentryPos : 0 < entryBound) (hentryBound : entryBound ≤ 1)
    (hthreshold0 : threshold ≠ 0) (hthresholdTop : threshold ≠ ∞)
    (hdriftBudgetTop : driftRate * threshold + allowance ≠ ∞) :
    ∃ scale contractionRate : ENNReal,
      scale ≠ 0 ∧ scale ≠ ∞ ∧ contractionRate < 1 ∧
        ∀ n : ℕ,
          relaxedPairMeetingTail (pathLaw initial coupled) δ n ≤
            contractionRate ^ n *
              (∫⁻ x in (relaxedDiagonal δ)ᶜ,
                meetingWeight V scale x ∂initial) := by
  obtain ⟨scale, contractionRate, hscale0, hscaleTop, hrate, hcontract⟩ :=
    hdrift.exists_scale_rate_targetAvoidanceContraction coupled
      (measurableSet_relaxedDiagonal δ) hentry hdriftRate hentryPos
      hentryBound hthreshold0 hthresholdTop hdriftBudgetTop
  exact ⟨scale, contractionRate, hscale0, hscaleTop, hrate,
    hcontract.relaxedPairMeetingTail_pathLaw_le initial coupled hdrift.1⟩

/-- For a path whose Markov state is `(Xₙ,Yₙ₋₁)`, failure to enter the relaxed
diagonal by time `n` is bounded by the ordinary time-`n` mass outside that
diagonal. This connects the paper's lagged meeting convention to kernel
powers without applying a second index shift. -/
theorem relaxedPairMeetingTail_pathLaw_le_complMassAtTime
    (initial : Measure (α × α))
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (δ : ℝ) (n : ℕ) :
    relaxedPairMeetingTail (pathLaw initial coupled) δ n ≤
      lawAtTime initial coupled n (relaxedDiagonal δ)ᶜ := by
  apply (relaxedPairMeetingTail_le_map_compl
    (pathLaw initial coupled) δ n).trans_eq
  rw [pathLaw_map_atTime]

/-- Proposition-4.1-style accessibility gives a finite-horizon relaxed
meeting bound for every deterministic lagged pair in `S × S`. -/
theorem IsRelaxedMeetingAccessibleFrom.relaxedPairMeetingTail_pathLaw_le
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {S : Set α} {δ : ℝ} {steps : ℕ} {meetingBound : ENNReal}
    (haccess : IsRelaxedMeetingAccessibleFrom coupled S δ steps meetingBound)
    {x : α × α} (hx : x ∈ S ×ˢ S) :
    relaxedPairMeetingTail (pathLaw (Measure.dirac x) coupled) δ steps ≤
      1 - meetingBound := by
  apply (relaxedPairMeetingTail_pathLaw_le_complMassAtTime
    (Measure.dirac x) coupled δ steps).trans
  rw [measure_compl (measurableSet_relaxedDiagonal δ)
    (measure_ne_top _ _), measure_univ, lawAtTime_dirac]
  exact tsub_le_tsub_left (haccess x hx) 1

/-- A uniform return to a contractive region followed by uniform relaxed
meeting gives the concrete finite-horizon path-tail bound in one step. -/
theorem IsUniformlyAccessibleFrom.relaxedPairMeetingTail_pathLaw_le_of_comp
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {S : Set α} {C : Set (α × α)} (hC : MeasurableSet C)
    {δ : ℝ} {returnSteps contractionSteps : ℕ}
    {returnBound contractionBound : ENNReal}
    (hreturn : IsUniformlyAccessibleFrom coupled (S ×ˢ S) C
      returnSteps returnBound)
    (hcontract : IsUniformlyAccessibleFrom coupled C (relaxedDiagonal δ)
      contractionSteps contractionBound)
    {x : α × α} (hx : x ∈ S ×ˢ S) :
    relaxedPairMeetingTail (pathLaw (Measure.dirac x) coupled) δ
        (returnSteps + contractionSteps) ≤
      1 - contractionBound * returnBound := by
  exact IsRelaxedMeetingAccessibleFrom.relaxedPairMeetingTail_pathLaw_le
    coupled (hreturn.comp_relaxedMeeting coupled hC hcontract) hx

/-- A return bound plus expected-distance contraction on a bounded region
gives an explicit relaxed meeting-tail bound. This packages the probabilistic
part of the local-contractivity-to-Proposition-4.1 route; proving the stated
expected contraction for the concrete HMC coupling remains algorithmic. -/
theorem HasExpectedDistanceContractionOn.relaxedPairMeetingTail_pathLaw_le
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {S : Set α} {C : Set (α × α)} (hC : MeasurableSet C)
    {returnSteps : ℕ} {returnBound rate : ENNReal}
    (hreturn : IsUniformlyAccessibleFrom coupled (S ×ˢ S) C
      returnSteps returnBound)
    (hcontract : HasExpectedDistanceContractionOn coupled C rate)
    {diameter δ : ℝ}
    (hdiameter : ∀ x ∈ C, dist x.1 x.2 ≤ diameter) (hδ : 0 < δ)
    {x : α × α} (hx : x ∈ S ×ˢ S) :
    relaxedPairMeetingTail (pathLaw (Measure.dirac x) coupled) δ
        (returnSteps + 1) ≤
      1 - (1 - rate * ENNReal.ofReal diameter / ENNReal.ofReal δ) *
        returnBound := by
  have hbound := hcontract.hasExpectedDistanceBoundOn coupled hdiameter
  have hclose :=
    hbound.isUniformlyAccessibleFrom_relaxedDiagonal coupled hδ
  exact hreturn.relaxedPairMeetingTail_pathLaw_le_of_comp
    coupled hC hclose hx

end RelaxedPathLaw

/-- A faithful weighted contraction transfers directly to a geometric bound
for the exact meeting-time tail of the verified path law. The initial
weighted mass is the explicit multiplicative constant. -/
theorem exactMeetingTail_pathLaw_le_weightedOffDiagonalMass
    [MeasurableEq α]
    (initial : Measure (α × α)) [IsProbabilityMeasure initial]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal} (hV : Measurable V)
    (scale rate : ENNReal)
    (hfaithful : IsFaithful coupled)
    (hcontract : HasWeightedOffDiagonalContraction coupled V scale rate)
    (n : ℕ) :
    exactMeetingTail (pathLaw initial coupled) n ≤
      rate ^ n * weightedOffDiagonalMassAtTime initial coupled V scale 0 := by
  exact (exactMeetingTail_pathLaw_le_offDiagonalMassAtTime initial coupled n).trans
    ((offDiagonalMassAtTime_le_weightedOffDiagonalMassAtTime
      initial coupled V scale n).trans
      (weightedOffDiagonalMassAtTime_le initial coupled hV scale rate
        hfaithful hcontract n))

/-- The drift/small-set criterion gives the same explicit geometric meeting
tail once its inside- and outside-set scalar inequalities are verified. -/
theorem HasGeometricDrift.exactMeetingTail_pathLaw_le_weighted
    [MeasurableEq α]
    (initial : Measure (α × α)) [IsProbabilityMeasure initial]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal} {C : Set (α × α)}
    {driftRate allowance meetingBound scale contractionRate : ENNReal}
    (hdrift : HasGeometricDrift coupled V C driftRate allowance)
    (hmeeting : IsExactMeetingSmallSet coupled C meetingBound)
    (hfaithful : IsFaithful coupled)
    (houtside : ∀ x ∉ C,
      1 + scale * (driftRate * V x) ≤
        contractionRate * meetingWeight V scale x)
    (hinside : ∀ x ∈ C,
      (1 - meetingBound) + scale * (driftRate * V x + allowance) ≤
        contractionRate * meetingWeight V scale x)
    (n : ℕ) :
    exactMeetingTail (pathLaw initial coupled) n ≤
      contractionRate ^ n *
        weightedOffDiagonalMassAtTime initial coupled V scale 0 := by
  exact exactMeetingTail_pathLaw_le_weightedOffDiagonalMass initial coupled
    hdrift.1 scale contractionRate hfaithful
    (hdrift.hasWeightedOffDiagonalContraction_of_smallSet coupled hmeeting
      houtside hinside) n

/-- Boundary Lyapunov bounds and two scalar budgets give an explicit geometric
exact-meeting tail. Supplying `contractionRate < 1` makes the displayed factor
strictly geometric; the inequality itself does not require that side fact. -/
theorem HasGeometricDrift.exactMeetingTail_pathLaw_le_weighted_of_bounds
    [MeasurableEq α]
    (initial : Measure (α × α)) [IsProbabilityMeasure initial]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal} {C : Set (α × α)}
    {driftRate allowance meetingBound scale contractionRate
      lowerBound upperBound : ENNReal}
    (hdrift : HasGeometricDrift coupled V C driftRate allowance)
    (hmeeting : IsExactMeetingSmallSet coupled C meetingBound)
    (hfaithful : IsFaithful coupled)
    (hrates : driftRate ≤ contractionRate)
    (hlower : ∀ x ∉ C, lowerBound ≤ V x)
    (hupper : ∀ x ∈ C, V x ≤ upperBound)
    (houtsideBudget :
      1 + scale * (driftRate * lowerBound) ≤
        contractionRate * (1 + scale * lowerBound))
    (hinsideBudget :
      (1 - meetingBound) +
          scale * (driftRate * upperBound + allowance) ≤ contractionRate)
    (n : ℕ) :
    exactMeetingTail (pathLaw initial coupled) n ≤
      contractionRate ^ n *
        weightedOffDiagonalMassAtTime initial coupled V scale 0 := by
  exact exactMeetingTail_pathLaw_le_weightedOffDiagonalMass initial coupled
    hdrift.1 scale contractionRate hfaithful
    (hdrift.hasWeightedOffDiagonalContraction_of_bounds coupled hmeeting
      hrates hlower hupper houtsideBudget hinsideBudget) n

/-- Sublevel drift and meeting reduce the geometric path-tail theorem to two
scalar inequalities at the sublevel threshold. -/
theorem HasGeometricDrift.exactMeetingTail_pathLaw_le_weighted_of_sublevel
    [MeasurableEq α]
    (initial : Measure (α × α)) [IsProbabilityMeasure initial]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal}
    {driftRate allowance meetingBound scale contractionRate threshold : ENNReal}
    (hdrift : HasGeometricDrift coupled V (lyapunovSublevel V threshold)
      driftRate allowance)
    (hmeeting : IsExactMeetingSmallSet coupled
      (lyapunovSublevel V threshold) meetingBound)
    (hfaithful : IsFaithful coupled)
    (hrates : driftRate ≤ contractionRate)
    (houtsideBudget :
      1 + scale * (driftRate * threshold) ≤
        contractionRate * (1 + scale * threshold))
    (hinsideBudget :
      (1 - meetingBound) +
          scale * (driftRate * threshold + allowance) ≤ contractionRate)
    (n : ℕ) :
    exactMeetingTail (pathLaw initial coupled) n ≤
      contractionRate ^ n *
        weightedOffDiagonalMassAtTime initial coupled V scale 0 := by
  exact exactMeetingTail_pathLaw_le_weightedOffDiagonalMass initial coupled
    hdrift.1 scale contractionRate hfaithful
    (hdrift.hasWeightedOffDiagonalContraction_of_sublevel coupled hmeeting
      hrates houtsideBudget hinsideBudget) n

/-- Strict sublevel budgets yield a concrete subunit rate and the corresponding
geometric exact-meeting tail at every time. -/
theorem HasGeometricDrift.exactMeetingTail_pathLaw_le_explicit_sublevel_rate
    [MeasurableEq α]
    (initial : Measure (α × α)) [IsProbabilityMeasure initial]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal}
    {driftRate allowance meetingBound scale threshold : ENNReal}
    (hdrift : HasGeometricDrift coupled V (lyapunovSublevel V threshold)
      driftRate allowance)
    (hmeeting : IsExactMeetingSmallSet coupled
      (lyapunovSublevel V threshold) meetingBound)
    (hfaithful : IsFaithful coupled)
    (hdriftRate : driftRate ≤ 1)
    (hscaleTop : scale ≠ ∞)
    (hthresholdTop : threshold ≠ ∞)
    (houtsideStrict :
      1 + scale * (driftRate * threshold) < 1 + scale * threshold)
    (hinsideStrict :
      (1 - meetingBound) +
          scale * (driftRate * threshold + allowance) < 1) :
    let contractionRate := sublevelMeetingContractionRate driftRate allowance
      meetingBound scale threshold
    contractionRate < 1 ∧ ∀ n : ℕ,
      exactMeetingTail (pathLaw initial coupled) n ≤
        contractionRate ^ n *
          weightedOffDiagonalMassAtTime initial coupled V scale 0 := by
  dsimp only
  obtain ⟨hrate, hcontract⟩ :=
    hdrift.sublevelMeetingContractionRate_lt_one_and_contracts coupled hmeeting
      hdriftRate hscaleTop hthresholdTop houtsideStrict hinsideStrict
  refine ⟨hrate, ?_⟩
  intro n
  exact exactMeetingTail_pathLaw_le_weightedOffDiagonalMass initial coupled
    hdrift.1 scale _ hfaithful hcontract n

/-- The standard strict drift condition and a weighted-drift budget below the
local meeting probability give a concrete subunit rate and geometric path-law
meeting tail. -/
theorem HasGeometricDrift.exactMeetingTail_pathLaw_le_explicit_sublevel_rate_of_budget
    [MeasurableEq α]
    (initial : Measure (α × α)) [IsProbabilityMeasure initial]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal}
    {driftRate allowance meetingBound scale threshold : ENNReal}
    (hdrift : HasGeometricDrift coupled V (lyapunovSublevel V threshold)
      driftRate allowance)
    (hmeeting : IsExactMeetingSmallSet coupled
      (lyapunovSublevel V threshold) meetingBound)
    (hfaithful : IsFaithful coupled)
    (hdriftRate : driftRate < 1)
    (hmeetingBound : meetingBound ≤ 1)
    (hscale0 : scale ≠ 0) (hscaleTop : scale ≠ ∞)
    (hthreshold0 : threshold ≠ 0) (hthresholdTop : threshold ≠ ∞)
    (hbudget :
      scale * (driftRate * threshold + allowance) < meetingBound) :
    let contractionRate := sublevelMeetingContractionRate driftRate allowance
      meetingBound scale threshold
    contractionRate < 1 ∧ ∀ n : ℕ,
      exactMeetingTail (pathLaw initial coupled) n ≤
        contractionRate ^ n *
          weightedOffDiagonalMassAtTime initial coupled V scale 0 := by
  dsimp only
  obtain ⟨hrate, hcontract⟩ :=
    hdrift.sublevelMeetingContractionRate_lt_one_and_contracts_of_budget
      coupled hmeeting hdriftRate hmeetingBound hscale0 hscaleTop
      hthreshold0 hthresholdTop hbudget
  refine ⟨hrate, ?_⟩
  intro n
  exact exactMeetingTail_pathLaw_le_weightedOffDiagonalMass initial coupled
    hdrift.1 scale _ hfaithful hcontract n

/-- A positive local meeting constant and finite drift budget automatically
yield a positive finite Lyapunov scale and a subunit geometric meeting-tail
rate. -/
theorem HasGeometricDrift.exists_scale_rate_exactMeetingTail_pathLaw_le
    [MeasurableEq α]
    (initial : Measure (α × α)) [IsProbabilityMeasure initial]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal}
    {driftRate allowance meetingBound threshold : ENNReal}
    (hdrift : HasGeometricDrift coupled V (lyapunovSublevel V threshold)
      driftRate allowance)
    (hmeeting : IsExactMeetingSmallSet coupled
      (lyapunovSublevel V threshold) meetingBound)
    (hfaithful : IsFaithful coupled)
    (hdriftRate : driftRate < 1)
    (hmeetingPos : 0 < meetingBound)
    (hmeetingBound : meetingBound ≤ 1)
    (hthreshold0 : threshold ≠ 0) (hthresholdTop : threshold ≠ ∞)
    (hdriftBudgetTop : driftRate * threshold + allowance ≠ ∞) :
    ∃ scale contractionRate : ENNReal,
      scale ≠ 0 ∧ scale ≠ ∞ ∧ contractionRate < 1 ∧
        ∀ n : ℕ,
          exactMeetingTail (pathLaw initial coupled) n ≤
            contractionRate ^ n *
              weightedOffDiagonalMassAtTime initial coupled V scale 0 := by
  obtain ⟨scale, hscale0, hscaleTop, hbudget⟩ :=
    exists_meetingWeight_scale hdriftBudgetTop hmeetingPos
  let contractionRate := sublevelMeetingContractionRate driftRate allowance
    meetingBound scale threshold
  obtain ⟨hcontractionRate, htail⟩ :=
    hdrift.exactMeetingTail_pathLaw_le_explicit_sublevel_rate_of_budget
      initial coupled hmeeting hfaithful hdriftRate hmeetingBound hscale0
      hscaleTop hthreshold0 hthresholdTop hbudget
  exact ⟨scale, contractionRate, hscale0, hscaleTop, hcontractionRate, htail⟩

/-- From a deterministic pair of finite Lyapunov value, the geometric-tail
constant is the explicit finite weight `1 + scale * V(x)`. -/
theorem HasGeometricDrift.exists_scale_rate_exactMeetingTail_pathKernel_le
    [MeasurableEq α]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal}
    {driftRate allowance meetingBound threshold : ENNReal}
    (hdrift : HasGeometricDrift coupled V (lyapunovSublevel V threshold)
      driftRate allowance)
    (hmeeting : IsExactMeetingSmallSet coupled
      (lyapunovSublevel V threshold) meetingBound)
    (hfaithful : IsFaithful coupled)
    (hdriftRate : driftRate < 1)
    (hmeetingPos : 0 < meetingBound)
    (hmeetingBound : meetingBound ≤ 1)
    (hthreshold0 : threshold ≠ 0) (hthresholdTop : threshold ≠ ∞)
    (hdriftBudgetTop : driftRate * threshold + allowance ≠ ∞)
    (x : α × α) (hVxTop : V x ≠ ∞) :
    ∃ scale contractionRate : ENNReal,
      scale ≠ 0 ∧ scale ≠ ∞ ∧ contractionRate < 1 ∧
        meetingWeight V scale x ≠ ∞ ∧
          ∀ n : ℕ,
            exactMeetingTail (pathKernel coupled x) n ≤
              contractionRate ^ n * meetingWeight V scale x := by
  obtain ⟨scale, contractionRate, hscale0, hscaleTop, hrate, htail⟩ :=
    hdrift.exists_scale_rate_exactMeetingTail_pathLaw_le
      (Measure.dirac x) coupled hmeeting hfaithful hdriftRate hmeetingPos
      hmeetingBound hthreshold0 hthresholdTop hdriftBudgetTop
  have hweightTop : meetingWeight V scale x ≠ ∞ := by
    exact ENNReal.add_ne_top.2
      ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top hscaleTop hVxTop⟩
  refine ⟨scale, contractionRate, hscale0, hscaleTop, hrate, hweightTop, ?_⟩
  intro n
  calc
    exactMeetingTail (pathKernel coupled x) n =
        exactMeetingTail (pathLaw (Measure.dirac x) coupled) n := by
      rw [pathLaw, Measure.dirac_bind (pathKernel coupled).measurable]
    _ ≤ contractionRate ^ n *
          weightedOffDiagonalMassAtTime (Measure.dirac x) coupled V scale 0 :=
      htail n
    _ ≤ contractionRate ^ n * meetingWeight V scale x := by
      exact mul_le_mul_right
        (weightedOffDiagonalMassAtTime_dirac_zero_le coupled hdrift.1 scale x)
        (contractionRate ^ n)

/-- A faithful kernel with a global exact-meeting lower bound contracts
off-diagonal mass by the factor `1 - ε` in one step. -/
theorem offDiagonalMassAtTime_succ_le
    [MeasurableEq α]
    (initial : Measure (α × α)) [IsProbabilityMeasure initial]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (ε : ENNReal)
    (hfaithful : IsFaithful coupled)
    (hmeeting : IsExactMeetingSmallSet coupled Set.univ ε)
    (n : ℕ) :
    offDiagonalMassAtTime initial coupled (n + 1) ≤
      (1 - ε) * offDiagonalMassAtTime initial coupled n := by
  rw [offDiagonalMassAtTime, lawAtTime_succ,
    Measure.bind_apply (measurableSet_diagonal.compl)
      coupled.aemeasurable]
  let μ := lawAtTime initial coupled n
  calc
    (∫⁻ x, coupled x (Set.diagonal α)ᶜ ∂μ) ≤
        ∫⁻ x in (Set.diagonal α)ᶜ, (1 - ε) ∂μ := by
      rw [← lintegral_indicator measurableSet_diagonal.compl]
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ Set.diagonal α
      · change coupled x (Set.diagonal α)ᶜ ≤ _
        rw [hfaithful.offDiagonal_eq_zero coupled hx]
        simp [hx]
      · change coupled x (Set.diagonal α)ᶜ ≤ _
        rw [Set.indicator_of_mem (show x ∈ (Set.diagonal α)ᶜ by exact hx)]
        exact hmeeting.offDiagonal_le coupled (Set.mem_univ x)
    _ = (1 - ε) * offDiagonalMassAtTime initial coupled n := by
      rw [setLIntegral_const]
      rfl

/-- Iterating the faithful global meeting contraction gives a geometric bound
on every finite-time off-diagonal mass. -/
theorem offDiagonalMassAtTime_le_geometric
    [MeasurableEq α]
    (initial : Measure (α × α)) [IsProbabilityMeasure initial]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (ε : ENNReal)
    (hfaithful : IsFaithful coupled)
    (hmeeting : IsExactMeetingSmallSet coupled Set.univ ε)
    (n : ℕ) :
    offDiagonalMassAtTime initial coupled n ≤ (1 - ε) ^ n := by
  induction n with
  | zero =>
    rw [pow_zero]
    calc
      offDiagonalMassAtTime initial coupled 0 ≤
          lawAtTime initial coupled 0 Set.univ := by
        exact measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  | succ n ih =>
      rw [pow_succ']
      apply (offDiagonalMassAtTime_succ_le initial coupled ε hfaithful
        hmeeting n).trans
      simpa only [mul_comm] using (mul_le_mul_left ih (1 - ε))

/-- Viewing every `block`th state of a chain as a skeleton agrees with using
the `block`th kernel power as its one-step transition. -/
theorem offDiagonalMassAtTime_pow
    [MeasurableEq α]
    (initial : Measure (α × α))
    (coupled : Kernel (α × α) (α × α))
    (block n : ℕ) :
    offDiagonalMassAtTime initial (coupled ^ block) n =
      offDiagonalMassAtTime initial coupled (block * n) := by
  unfold offDiagonalMassAtTime lawAtTime
  rw [pow_mul]

/-- Uniform finite-step accessibility plus local meeting gives geometric
off-diagonal decay along the corresponding skeleton times. -/
theorem offDiagonalMassAtSkeletonTime_le_geometric
    [MeasurableEq α]
    (initial : Measure (α × α)) [IsProbabilityMeasure initial]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {C : Set (α × α)} (hC : MeasurableSet C)
    (steps : ℕ) (returnBound meetingBound : ENNReal)
    (hreturn : IsUniformlyAccessible coupled C steps returnBound)
    (hmeeting : IsExactMeetingSmallSet coupled C meetingBound)
    (hfaithful : IsFaithful coupled)
    (n : ℕ) :
    offDiagonalMassAtTime initial coupled ((steps + 1) * n) ≤
      (1 - meetingBound * returnBound) ^ n := by
  rw [← offDiagonalMassAtTime_pow initial coupled (steps + 1) n]
  exact offDiagonalMassAtTime_le_geometric initial (coupled ^ (steps + 1))
    (meetingBound * returnBound) (hfaithful.pow coupled (steps + 1))
    (hreturn.isExactMeetingSmallSet_pow_succ coupled hC hmeeting) n

/-- Uniform finite-step accessibility plus local meeting gives a geometric
tail bound for the actual exact meeting time under the Ionescu--Tulcea path
law, sampled at the corresponding skeleton times. -/
theorem exactMeetingTail_pathLaw_atSkeletonTime_le_geometric
    [MeasurableEq α]
    (initial : Measure (α × α)) [IsProbabilityMeasure initial]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {C : Set (α × α)} (hC : MeasurableSet C)
    (steps : ℕ) (returnBound meetingBound : ENNReal)
    (hreturn : IsUniformlyAccessible coupled C steps returnBound)
    (hmeeting : IsExactMeetingSmallSet coupled C meetingBound)
    (hfaithful : IsFaithful coupled)
    (n : ℕ) :
    exactMeetingTail (pathLaw initial coupled) ((steps + 1) * n) ≤
      (1 - meetingBound * returnBound) ^ n := by
  exact (exactMeetingTail_pathLaw_le_offDiagonalMassAtTime
    initial coupled ((steps + 1) * n)).trans
      (offDiagonalMassAtSkeletonTime_le_geometric initial coupled hC steps
        returnBound meetingBound hreturn hmeeting hfaithful n)

/-- The skeleton meeting estimate controls every original-chain time, with
the exponent equal to the number of completed skeleton blocks. -/
theorem exactMeetingTail_pathLaw_le_geometric_div
    [MeasurableEq α]
    (initial : Measure (α × α)) [IsProbabilityMeasure initial]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {C : Set (α × α)} (hC : MeasurableSet C)
    (steps : ℕ) (returnBound meetingBound : ENNReal)
    (hreturn : IsUniformlyAccessible coupled C steps returnBound)
    (hmeeting : IsExactMeetingSmallSet coupled C meetingBound)
    (hfaithful : IsFaithful coupled)
    (n : ℕ) :
    exactMeetingTail (pathLaw initial coupled) n ≤
      (1 - meetingBound * returnBound) ^ (n / (steps + 1)) := by
  apply exactMeetingTail_le_of_skeleton _ _ (steps + 1) (Nat.succ_pos steps)
  intro k
  exact exactMeetingTail_pathLaw_atSkeletonTime_le_geometric initial coupled
    hC steps returnBound meetingBound hreturn hmeeting hfaithful k

/-- A globally bounded Lyapunov function closes the drift/small-set argument
without an additional return premise. Drift gives a one-step global return to
the chosen sublevel, so exact meeting has a geometric path-law tail with
two-step blocks. This theorem intentionally does not claim the corresponding
unbounded-state result. -/
theorem HasGeometricDrift.exactMeetingTail_pathLaw_le_geometric_of_bounded
    [MeasurableEq α]
    (initial : Measure (α × α)) [IsProbabilityMeasure initial]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {V : (α × α) → ENNReal} {C : Set (α × α)}
    {rate allowance B R meetingBound : ENNReal}
    (hdrift : HasGeometricDrift coupled V C rate allowance)
    (hV : ∀ x, V x ≤ B)
    (hR0 : R ≠ 0) (hRtop : R ≠ ∞)
    (hbudget : rate * B + allowance < R)
    (hmeetingPos : 0 < meetingBound)
    (hmeeting : IsExactMeetingSmallSet coupled
      (lyapunovSublevel V R) meetingBound)
    (hfaithful : IsFaithful coupled) :
    let returnBound := 1 - (rate * B + allowance) / R
    0 < meetingBound * returnBound ∧
      1 - meetingBound * returnBound < 1 ∧
      ∀ n, exactMeetingTail (pathLaw initial coupled) n ≤
        (1 - meetingBound * returnBound) ^ (n / 2) := by
  dsimp only
  have hreturnFrom := hdrift.isUniformlyAccessibleFrom_sublevel coupled
    hR0 hRtop (start := Set.univ) (fun x _hx => hV x)
  have hreturn : IsUniformlyAccessible coupled (lyapunovSublevel V R) 1
      (1 - (rate * B + allowance) / R) :=
    (isUniformlyAccessibleFrom_univ_iff coupled (lyapunovSublevel V R) 1
      (1 - (rate * B + allowance) / R)).mp hreturnFrom
  have hreturnPos : 0 < 1 - (rate * B + allowance) / R :=
    sublevelReturnBound_pos hR0 hRtop hbudget
  have hproduct : 0 <
      meetingBound * (1 - (rate * B + allowance) / R) :=
    ENNReal.mul_pos hmeetingPos.ne' hreturnPos.ne'
  refine ⟨hproduct,
    ENNReal.sub_lt_self (by simp) (by simp) hproduct.ne', fun n => ?_⟩
  simpa only [Nat.reduceAdd] using
    exactMeetingTail_pathLaw_le_geometric_div initial coupled
      (measurableSet_lyapunovSublevel hdrift.1 R) 1
      (1 - (rate * B + allowance) / R) meetingBound hreturn hmeeting
      hfaithful n

/-- Measurable embedding onto the diagonal. -/
def diagonalMap (y : α) : α × α := (y, y)

theorem measurable_diagonalMap : Measurable (diagonalMap : α → α × α) :=
  measurable_id.prodMk measurable_id

/-- Synchronous coupling obtained by applying one marginal transition to the
first input and copying its output into both coordinates. -/
noncomputable def synchronousCoupling
    (transition : Kernel α α) : Kernel (α × α) (α × α) :=
  (transition.comap Prod.fst measurable_fst).map diagonalMap

instance synchronousCoupling.instIsMarkovKernel
    (transition : Kernel α α) [IsMarkovKernel transition] :
    IsMarkovKernel (synchronousCoupling transition) := by
  unfold synchronousCoupling
  apply Kernel.IsMarkovKernel.map
  exact measurable_diagonalMap

/-- The synchronous row integrates an additive paired Lyapunov function as
twice the corresponding one-state expectation. -/
theorem synchronousCoupling_lintegral_pairedAdd
    (transition : Kernel α α) {v : α → ENNReal} (hv : Measurable v)
    (x : α × α) :
    (∫⁻ y, IsCoupling.pairedAdd v y ∂synchronousCoupling transition x) =
      (∫⁻ y, v y ∂transition x.1) + (∫⁻ y, v y ∂transition x.1) := by
  rw [synchronousCoupling,
    Kernel.lintegral_map _ measurable_diagonalMap x
      (IsCoupling.measurable_pairedAdd hv),
    Kernel.lintegral_comap]
  change (∫⁻ y, v y + v y ∂transition x.1) = _
  rw [lintegral_add_left hv]

/-- Replace the transition from diagonal inputs by the synchronous coupling,
leaving all off-diagonal rows unchanged. -/
noncomputable def stickyCoupling [MeasurableEq α]
    (transition : Kernel α α)
    (coupled : Kernel (α × α) (α × α)) : Kernel (α × α) (α × α) := by
  classical
  exact Kernel.piecewise measurableSet_diagonal
    (synchronousCoupling transition) coupled

instance stickyCoupling.instIsMarkovKernel
    [MeasurableEq α]
    (transition : Kernel α α) [IsMarkovKernel transition]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled] :
    IsMarkovKernel (stickyCoupling transition coupled) := by
  classical
  unfold stickyCoupling
  infer_instance

/-- The sticky modification preserves both intended marginal kernels. -/
theorem stickyCoupling_isCoupling
    [MeasurableEq α]
    (transition : Kernel α α) [IsMarkovKernel transition]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    (hcoupled : IsCoupling coupled transition transition) :
    IsCoupling (stickyCoupling transition coupled) transition transition := by
  classical
  constructor
  · ext current s hs
    rw [Kernel.fst_apply' _ _ hs, Kernel.comap_apply,
      stickyCoupling, Kernel.piecewise_apply']
    split_ifs with hdiag
    · change (((transition.comap Prod.fst measurable_fst).map diagonalMap)
          current) (Prod.fst ⁻¹' s) = transition current.1 s
      rw [Kernel.map_apply'
        (transition.comap Prod.fst measurable_fst)
        measurable_diagonalMap current (measurable_fst hs),
        Kernel.comap_apply]
      rfl
    · rw [← Kernel.fst_apply' coupled current hs,
        hcoupled.fst_apply]
  · ext current s hs
    rw [Kernel.snd_apply' _ _ hs, Kernel.comap_apply,
      stickyCoupling, Kernel.piecewise_apply']
    split_ifs with hdiag
    · have heq : current.1 = current.2 := Set.mem_diagonal_iff.mp hdiag
      change (((transition.comap Prod.fst measurable_fst).map diagonalMap)
          current) (Prod.snd ⁻¹' s) = transition current.2 s
      rw [Kernel.map_apply'
        (transition.comap Prod.fst measurable_fst)
        measurable_diagonalMap current (measurable_snd hs),
        Kernel.comap_apply]
      have hpre : diagonalMap ⁻¹' Prod.snd ⁻¹' s = s := by
        ext y
        rfl
      rw [hpre, heq]
    · rw [← Kernel.snd_apply' coupled current hs,
        hcoupled.snd_apply]

/-- The sticky modification is faithful by construction. -/
theorem stickyCoupling_isFaithful
    [MeasurableEq α]
    (transition : Kernel α α) [IsMarkovKernel transition]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled] :
    IsFaithful (stickyCoupling transition coupled) := by
  classical
  intro current hcurrent
  rw [stickyCoupling, Kernel.piecewise_apply', if_pos hcurrent,
    synchronousCoupling, Kernel.map_apply'
      (transition.comap Prod.fst measurable_fst)
      measurable_diagonalMap current measurableSet_diagonal,
    Kernel.comap_apply]
  have hpre : diagonalMap ⁻¹' Set.diagonal α = Set.univ := by
    ext y
    simp [diagonalMap]
  rw [hpre, measure_univ]

/-- A drift certificate for a coupling transfers to its sticky modification
when the synchronous replacement rows satisfy the same bound on diagonal
inputs. Off-diagonal rows are unchanged. -/
theorem HasGeometricDrift.stickyCoupling
    [MeasurableEq α]
    (transition : Kernel α α)
    (coupled : Kernel (α × α) (α × α))
    {V : (α × α) → ENNReal} {C : Set (α × α)}
    {rate allowance : ENNReal}
    (hdrift : HasGeometricDrift coupled V C rate allowance)
    (hdiagonal : ∀ x ∈ Set.diagonal α,
      (∫⁻ y, V y ∂synchronousCoupling transition x) ≤
        rate * V x + C.indicator (fun _ => allowance) x) :
    HasGeometricDrift (stickyCoupling transition coupled) V C rate allowance := by
  classical
  refine ⟨hdrift.1, hdrift.2.1, fun x => ?_⟩
  by_cases hx : x ∈ Set.diagonal α
  · rw [Mcmc.Kernel.stickyCoupling, Kernel.piecewise_apply, if_pos hx]
    exact hdiagonal x hx
  · rw [Mcmc.Kernel.stickyCoupling, Kernel.piecewise_apply, if_neg hx]
    exact hdrift.2.2 x

/-- For an additive paired Lyapunov function, sticky modification preserves
drift automatically: every coupling with the correct marginals has the same
expected additive value, including the synchronous diagonal replacement. -/
theorem HasGeometricDrift.stickyCoupling_pairedAdd
    [MeasurableEq α]
    (transition : Kernel α α)
    (coupled : Kernel (α × α) (α × α))
    (hcoupled : IsCoupling coupled transition transition)
    {v : α → ENNReal} {C : Set (α × α)} {rate allowance : ENNReal}
    (hv : Measurable v)
    (hdrift : HasGeometricDrift coupled (IsCoupling.pairedAdd v) C
      rate allowance) :
    HasGeometricDrift (Mcmc.Kernel.stickyCoupling transition coupled)
      (IsCoupling.pairedAdd v) C rate allowance := by
  apply hdrift.stickyCoupling transition coupled
  intro x hx
  have heq : x.1 = x.2 := Set.mem_diagonal_iff.mp hx
  calc
    (∫⁻ y, IsCoupling.pairedAdd v y ∂synchronousCoupling transition x) =
        (∫⁻ y, v y ∂transition x.1) +
          (∫⁻ y, v y ∂transition x.1) :=
      synchronousCoupling_lintegral_pairedAdd transition hv x
    _ = (∫⁻ y, IsCoupling.pairedAdd v y ∂coupled x) := by
      rw [hcoupled.lintegral_pairedAdd hv x, heq]
    _ ≤ rate * IsCoupling.pairedAdd v x +
          C.indicator (fun _ => allowance) x := hdrift.2.2 x

/-- Sticky modification preserves every exact-meeting small-set bound of the
original coupling. On diagonal inputs its meeting probability is improved to
one. -/
theorem stickyCoupling_isExactMeetingSmallSet
    [MeasurableEq α]
    (transition : Kernel α α) [IsMarkovKernel transition]
    (coupled : Kernel (α × α) (α × α)) [IsMarkovKernel coupled]
    {C : Set (α × α)} {ε : ENNReal}
    (hsmall : IsExactMeetingSmallSet coupled C ε) :
    IsExactMeetingSmallSet (stickyCoupling transition coupled) C ε := by
  classical
  intro current hcurrent
  by_cases hdiag : current ∈ Set.diagonal α
  · rw [stickyCoupling_isFaithful transition coupled current hdiag]
    calc
      ε ≤ coupled current (Set.diagonal α) := hsmall current hcurrent
      _ ≤ coupled current Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  · rw [stickyCoupling, Kernel.piecewise_apply', if_neg hdiag]
    exact hsmall current hcurrent

end Mcmc.Kernel
