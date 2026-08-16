import Mcmc.PDMP.EventSimulation
import Mcmc.PDMP.ZigZag
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Tactic

/-!
# One-dimensional Zig-Zag process semantics

This module instantiates the generic PDMP flow and jump interfaces for the
one-dimensional Zig-Zag state `(position, velocity)`.  It supplies the exact
linear semiflow, deterministic velocity flip, and fixed-event execution
kernel.  Sampling the state-dependent event times remains a separate layer.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory BigOperators

namespace Mcmc.PDMP

/-- Position and two-valued velocity for the one-dimensional Zig-Zag process. -/
abbrev ZigZagState := ℝ × Bool

/-- Exact linear Zig-Zag motion between velocity-switching events. -/
def zigZagFlow (t : NNReal) (state : ZigZagState) : ZigZagState :=
  (state.1 + (t : ℝ) * zigZagVelocity state.2, state.2)

/-- The linear Zig-Zag motion is a measurable semiflow. -/
noncomputable def zigZagSemiflow : MeasurableSemiflow ZigZagState where
  flow := zigZagFlow
  measurable_flow t := by
    unfold zigZagFlow
    fun_prop
  flow_zero := by
    funext state
    simp [zigZagFlow]
  flow_add := by
    intro t u
    funext state
    apply Prod.ext
    · simp only [zigZagFlow, Function.comp_apply, NNReal.coe_add]
      ring
    · rfl

/-- Joint measurability needed to sample a random inter-event wait. -/
noncomputable def zigZagJointlyMeasurableSemiflow :
    JointlyMeasurableSemiflow ZigZagState where
  toMeasurableSemiflow := zigZagSemiflow
  jointly_measurable_flow := by
    change Measurable (fun p : NNReal × ZigZagState => zigZagFlow p.1 p.2)
    unfold zigZagFlow
    fun_prop

/-- A Zig-Zag event keeps position fixed and flips the velocity sign. -/
def zigZagFlip (state : ZigZagState) : ZigZagState :=
  (state.1, !state.2)

/-- Deterministic Markov kernel for a Zig-Zag velocity switch. -/
noncomputable def zigZagJumpKernel : Kernel ZigZagState ZigZagState :=
  Kernel.deterministic zigZagFlip (by
    unfold zigZagFlip
    fun_prop)

instance zigZagJumpKernel.instIsMarkovKernel :
    IsMarkovKernel zigZagJumpKernel := by
  unfold zigZagJumpKernel
  infer_instance

@[simp] theorem zigZagFlip_involutive (state : ZigZagState) :
    zigZagFlip (zigZagFlip state) = state := by
  rcases state with ⟨q, v⟩
  simp [zigZagFlip]

/-- Kernel for executing a fixed list of Zig-Zag inter-event waits. -/
noncomputable def zigZagExecuteSchedule (waits : List NNReal) :
    Kernel ZigZagState ZigZagState :=
  zigZagSemiflow.executeSchedule zigZagJumpKernel waits

instance zigZagExecuteSchedule.instIsMarkovKernel (waits : List NNReal) :
    IsMarkovKernel (zigZagExecuteSchedule waits) := by
  unfold zigZagExecuteSchedule
  infer_instance

/-- The canonical event intensity evaluated on a Zig-Zag process state. -/
def zigZagStateRate (potentialGradient : ℝ → ℝ)
    (state : ZigZagState) : ℝ :=
  zigZagRate potentialGradient state.1 state.2

theorem zigZagStateRate_nonneg (potentialGradient : ℝ → ℝ)
    (state : ZigZagState) :
    0 ≤ zigZagStateRate potentialGradient state :=
  zigZagRate_nonneg potentialGradient state.1 state.2

/-- State-dependent Zig-Zag jump mechanism in the general thinning
interface. -/
noncomputable def zigZagJumpMechanism (potentialGradient : ℝ → ℝ)
    (hmeasurable : Measurable potentialGradient) : JumpMechanism ZigZagState where
  rate := fun state => ENNReal.ofReal (zigZagStateRate potentialGradient state)
  measurable_rate := by
    unfold zigZagStateRate zigZagRate
    fun_prop
  jump := zigZagJumpKernel
  isMarkov := by infer_instance

/-- Exact homogeneous-clock thinning simulator for a globally bounded
one-dimensional Zig-Zag intensity. -/
noncomputable def zigZagThinnedSimulator
    (potentialGradient : ℝ → ℝ) (hmeasurable : Measurable potentialGradient)
    (clock : HomogeneousClock)
    (hbound : ∀ state, ENNReal.ofReal (zigZagStateRate potentialGradient state) ≤
      clock.rate) : ThinnedFlowSimulator ZigZagState where
  semiflow := zigZagJointlyMeasurableSemiflow
  mechanism := zigZagJumpMechanism potentialGradient hmeasurable
  clock := clock
  rate_le_clock := hbound

/-! ### Exact standard-Gaussian event clock -/

/-- Unit exponential hazard law, represented on nonnegative reals. -/
noncomputable def gaussianZigZagHazardMeasure : Measure NNReal :=
  (HomogeneousClock.mk 1 zero_lt_one).waitMeasure

instance gaussianZigZagHazardMeasure.instIsProbabilityMeasure :
    IsProbabilityMeasure gaussianZigZagHazardMeasure := by
  unfold gaussianZigZagHazardMeasure
  infer_instance

/-- Nonnegative inverse-hazard waiting time for the standard-Gaussian
Zig-Zag process. -/
noncomputable def gaussianZigZagWaitingNNReal
    (state : ZigZagState) (hazard : NNReal) : NNReal :=
  Real.toNNReal
    (gaussianZigZagWaitingTime state.1 state.2 (hazard : ℝ))

theorem measurable_gaussianZigZagWaitingNNReal :
    Measurable (fun input : ZigZagState × NNReal =>
      gaussianZigZagWaitingNNReal input.1 input.2) := by
  unfold gaussianZigZagWaitingNNReal gaussianZigZagWaitingTime
  apply measurable_real_toNNReal.comp
  let a : ZigZagState × NNReal → ℝ := fun input =>
    zigZagVelocity input.1.2 * input.1.1
  have ha : Measurable a := by
    unfold a zigZagVelocity
    fun_prop
  apply Measurable.ite (measurableSet_le measurable_const ha)
  · exact (((ha.pow_const 2).add
      (measurable_const.mul (measurable_coe_nnreal_real.comp measurable_snd))).sqrt).sub ha
  · exact ha.neg.add
      ((measurable_const.mul
        (measurable_coe_nnreal_real.comp measurable_snd)).sqrt)

/-- Deterministic state update driven by one exponential hazard draw. -/
noncomputable def gaussianZigZagEventUpdate
    (state : ZigZagState) (hazard : NNReal) : ZigZagState :=
  zigZagFlip (zigZagFlow (gaussianZigZagWaitingNNReal state hazard) state)

/-- One exact standard-Gaussian Zig-Zag event: draw unit exponential hazard,
invert the integrated rate, flow to that time, and flip velocity. -/
noncomputable def gaussianZigZagEventKernel :
    Kernel ZigZagState ZigZagState :=
  Kernel.map
    (Kernel.prod Kernel.id
      (Kernel.const ZigZagState gaussianZigZagHazardMeasure))
    (fun input => gaussianZigZagEventUpdate input.1 input.2)

instance gaussianZigZagEventKernel.instIsMarkovKernel :
    IsMarkovKernel gaussianZigZagEventKernel := by
  unfold gaussianZigZagEventKernel
  apply Kernel.IsMarkovKernel.map
  have hwait : Measurable (fun input : ZigZagState × NNReal =>
      gaussianZigZagWaitingNNReal input.1 input.2) :=
    measurable_gaussianZigZagWaitingNNReal
  have hvelocity : Measurable (fun input : ZigZagState × NNReal =>
      zigZagVelocity input.1.2) := by
    unfold zigZagVelocity
    fun_prop
  unfold gaussianZigZagEventUpdate zigZagFlip zigZagFlow
  exact ((measurable_fst.comp measurable_fst).add
    (hwait.coe_nnreal_real.mul hvelocity)).prodMk (by fun_prop)

/-- The nonnegative representation of the inverse clock does not alter the
closed-form waiting time. -/
theorem coe_gaussianZigZagWaitingNNReal
    (state : ZigZagState) (hazard : NNReal) :
    (gaussianZigZagWaitingNNReal state hazard : ℝ) =
      gaussianZigZagWaitingTime state.1 state.2 (hazard : ℝ) := by
  unfold gaussianZigZagWaitingNNReal
  rw [Real.coe_toNNReal _
    (gaussianZigZagWaitingTime_nonneg state.1 state.2 hazard.coe_nonneg)]

/-- Every positive hazard draw is inverted exactly by the event kernel's
waiting-time calculation. -/
theorem gaussianZigZagIntegratedRate_waitingNNReal
    (state : ZigZagState) {hazard : NNReal} (hhazard : 0 < hazard) :
    gaussianZigZagIntegratedRate state.1 state.2
      (gaussianZigZagWaitingNNReal state hazard : ℝ) = (hazard : ℝ) := by
  rw [coe_gaussianZigZagWaitingNNReal]
  exact gaussianZigZagIntegratedRate_waitingTime state.1 state.2
    (by exact_mod_cast hhazard)

/-- Position with the velocity sign folded into it. Along a linear segment it
increases at unit speed. -/
def zigZagSignedPosition (state : ZigZagState) : ℝ :=
  zigZagVelocity state.2 * state.1

@[simp] theorem zigZagVelocity_not (velocity : Bool) :
    zigZagVelocity (!velocity) = -zigZagVelocity velocity := by
  cases velocity <;> simp [zigZagVelocity]

@[simp] theorem zigZagVelocity_sq (velocity : Bool) :
    zigZagVelocity velocity ^ 2 = 1 := by
  cases velocity <;> norm_num [zigZagVelocity]

/-- Exact post-event recurrence for the Gaussian clock. Once the signed
position is negative, the next event resets it to `-sqrt (2E)` independently
of its previous magnitude. -/
theorem zigZagSignedPosition_gaussianZigZagEventUpdate
    (state : ZigZagState) (hazard : NNReal) :
    zigZagSignedPosition (gaussianZigZagEventUpdate state hazard) =
      if 0 ≤ zigZagSignedPosition state then
        -Real.sqrt (zigZagSignedPosition state ^ 2 + 2 * (hazard : ℝ))
      else -Real.sqrt (2 * (hazard : ℝ)) := by
  let a := zigZagSignedPosition state
  have hflow (time : ℝ) :
      zigZagVelocity state.2 *
        (state.1 + time * zigZagVelocity state.2) = a + time := by
    unfold a zigZagSignedPosition
    calc
      _ = zigZagVelocity state.2 * state.1 +
          time * zigZagVelocity state.2 ^ 2 := by ring
      _ = zigZagVelocity state.2 * state.1 + time := by
        rw [zigZagVelocity_sq]
        ring
  unfold gaussianZigZagEventUpdate zigZagSignedPosition zigZagFlip zigZagFlow
  rw [show (gaussianZigZagWaitingNNReal state hazard : ℝ) =
      gaussianZigZagWaitingTime state.1 state.2 (hazard : ℝ) from
    coe_gaussianZigZagWaitingNNReal state hazard]
  simp only [zigZagVelocity_not, neg_mul]
  change -(zigZagVelocity state.2 *
      (state.1 + gaussianZigZagWaitingTime state.1 state.2 (hazard : ℝ) *
        zigZagVelocity state.2)) = _
  rw [hflow]
  unfold gaussianZigZagWaitingTime
  change -(a + if 0 ≤ a then Real.sqrt (a ^ 2 + 2 * (hazard : ℝ)) - a
    else -a + Real.sqrt (2 * (hazard : ℝ))) =
      if 0 ≤ a then -Real.sqrt (a ^ 2 + 2 * (hazard : ℝ))
      else -Real.sqrt (2 * (hazard : ℝ))
  split_ifs <;> ring

theorem zigZagSignedPosition_gaussianZigZagEventUpdate_neg
    (state : ZigZagState) {hazard : NNReal} (hhazard : 0 < hazard) :
    zigZagSignedPosition (gaussianZigZagEventUpdate state hazard) < 0 := by
  rw [zigZagSignedPosition_gaussianZigZagEventUpdate]
  split_ifs
  · exact neg_lt_zero.mpr (Real.sqrt_pos.2 (by
      have : 0 < (2 : ℝ) * (hazard : ℝ) := by positivity
      nlinarith [sq_nonneg (zigZagSignedPosition state)]))
  · exact neg_lt_zero.mpr (Real.sqrt_pos.2 (by positivity))

/-- From a negative signed position, the next waiting time dominates the
square root of its fresh exponential hazard. -/
theorem sqrt_hazard_le_gaussianZigZagWaitingNNReal_of_signedPosition_neg
    (state : ZigZagState) (hazard : NNReal)
    (hstate : zigZagSignedPosition state < 0) :
    Real.sqrt (2 * (hazard : ℝ)) ≤
      (gaussianZigZagWaitingNNReal state hazard : ℝ) := by
  rw [coe_gaussianZigZagWaitingNNReal]
  unfold gaussianZigZagWaitingTime
  change Real.sqrt (2 * (hazard : ℝ)) ≤
    if 0 ≤ zigZagSignedPosition state then
      Real.sqrt (zigZagSignedPosition state ^ 2 + 2 * (hazard : ℝ)) -
        zigZagSignedPosition state
    else -zigZagSignedPosition state + Real.sqrt (2 * (hazard : ℝ))
  rw [if_neg (not_le.mpr hstate)]
  linarith

/-- Every waiting time after the first genuine event has a fresh positive
`sqrt(2E)` lower bound. This is the deterministic reduction needed for a
future i.i.d.-series nonexplosion proof. -/
theorem sqrt_hazard_le_gaussianZigZagWaitingNNReal_after_event
    (state : ZigZagState) {previousHazard : NNReal}
    (hprevious : 0 < previousHazard) (hazard : NNReal) :
    Real.sqrt (2 * (hazard : ℝ)) ≤
      (gaussianZigZagWaitingNNReal
        (gaussianZigZagEventUpdate state previousHazard) hazard : ℝ) :=
  sqrt_hazard_le_gaussianZigZagWaitingNNReal_of_signedPosition_neg _ _
    (zigZagSignedPosition_gaussianZigZagEventUpdate_neg state hprevious)

theorem gaussianZigZagHazardMeasure_singleton_zero :
    gaussianZigZagHazardMeasure {0} = 0 := by
  unfold gaussianZigZagHazardMeasure HomogeneousClock.waitMeasure
  rw [Measure.map_apply measurable_real_toNNReal
    (MeasurableSet.singleton 0)]
  have hpre : Real.toNNReal ⁻¹' ({0} : Set NNReal) = Set.Iic 0 := by
    ext x
    simp [Real.toNNReal_eq_zero]
  rw [hpre]
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  have hcdf := cdf_expMeasure_eq (r := (1 : ℝ)) zero_lt_one 0
  rw [cdf_eq_real] at hcdf
  norm_num at hcdf
  rcases (ENNReal.toReal_eq_zero_iff _).mp hcdf with hzero | htop
  · exact hzero
  · exact (measure_ne_top (expMeasure (1 : ℝ)) (Set.Iic 0) htop).elim

theorem gaussianZigZagHazardMeasure_positive_ae :
    ∀ᵐ hazard ∂gaussianZigZagHazardMeasure, 0 < hazard := by
  have hne : ∀ᵐ hazard ∂gaussianZigZagHazardMeasure, hazard ≠ 0 := by
    rw [ae_iff]
    rw [show {hazard : NNReal | ¬hazard ≠ 0} = {0} by
      ext hazard
      simp]
    exact gaussianZigZagHazardMeasure_singleton_zero
  filter_upwards [hne] with hazard hhazard
  exact bot_lt_iff_ne_bot.mpr hhazard

theorem gaussianZigZagHazardMeasure_Iic_one_toReal :
    (gaussianZigZagHazardMeasure (Set.Iic 1)).toReal =
      1 - Real.exp (-1) := by
  unfold gaussianZigZagHazardMeasure HomogeneousClock.waitMeasure
  rw [Measure.map_apply measurable_real_toNNReal measurableSet_Iic]
  have hpre : Real.toNNReal ⁻¹' (Set.Iic 1 : Set NNReal) = Set.Iic 1 := by
    ext x
    simp [Real.toNNReal_le_one]
  rw [hpre]
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  have hcdf := cdf_expMeasure_eq (r := (1 : ℝ)) zero_lt_one 1
  rw [cdf_eq_real] at hcdf
  norm_num at hcdf ⊢
  exact hcdf

theorem gaussianZigZagHazardMeasure_Ioi_one_pos :
    0 < gaussianZigZagHazardMeasure (Set.Ioi 1) := by
  rw [pos_iff_ne_zero]
  intro hzero
  have hunion : gaussianZigZagHazardMeasure
      (Set.Iic (1 : NNReal) ∪ Set.Ioi 1) =
      gaussianZigZagHazardMeasure (Set.Iic 1) +
        gaussianZigZagHazardMeasure (Set.Ioi 1) :=
    measure_union (Set.disjoint_left.2 fun x hx hy =>
      (not_lt_of_ge (show x ≤ 1 from hx)) (show 1 < x from hy))
      measurableSet_Ioi
  have hfull : gaussianZigZagHazardMeasure (Set.Iic 1) = 1 := by
    rw [Set.Iic_union_Ioi, measure_univ, hzero, add_zero] at hunion
    exact hunion.symm
  have hlt : (gaussianZigZagHazardMeasure (Set.Iic 1)).toReal < 1 := by
    rw [gaussianZigZagHazardMeasure_Iic_one_toReal]
    linarith [Real.exp_pos (-1)]
  rw [hfull] at hlt
  norm_num at hlt

/-- Infinite independent hazard stream used to construct the exact event
sequence. -/
noncomputable def gaussianZigZagHazardSequenceMeasure :
    Measure (ℕ → NNReal) :=
  Measure.infinitePi (fun _ : ℕ => gaussianZigZagHazardMeasure)

instance gaussianZigZagHazardSequenceMeasure.instIsProbabilityMeasure :
    IsProbabilityMeasure gaussianZigZagHazardSequenceMeasure := by
  unfold gaussianZigZagHazardSequenceMeasure
  infer_instance

def gaussianZigZagLargeHazardEvent (index : ℕ) : Set (ℕ → NNReal) :=
  (fun hazards => hazards index) ⁻¹' Set.Ioi (1 : NNReal)

theorem measurableSet_gaussianZigZagLargeHazardEvent (index : ℕ) :
    MeasurableSet (gaussianZigZagLargeHazardEvent index) := by
  unfold gaussianZigZagLargeHazardEvent
  exact (measurableSet_Ioi : MeasurableSet (Set.Ioi (1 : NNReal))).preimage
    (measurable_pi_apply index)

theorem gaussianZigZagHazardSequenceMeasure_largeHazardEvent
    (index : ℕ) :
    gaussianZigZagHazardSequenceMeasure
      (gaussianZigZagLargeHazardEvent index) =
        gaussianZigZagHazardMeasure (Set.Ioi 1) := by
  unfold gaussianZigZagHazardSequenceMeasure
    gaussianZigZagLargeHazardEvent
  have hmap := Measure.infinitePi_map_eval
    (μ := fun _ : ℕ => gaussianZigZagHazardMeasure) index
  calc
    _ = (Measure.map (fun hazards : ℕ → NNReal => hazards index)
        (Measure.infinitePi fun _ : ℕ => gaussianZigZagHazardMeasure))
        (Set.Ioi 1) := by
      rw [Measure.map_apply (by fun_prop) measurableSet_Ioi]
    _ = _ := congrArg (fun measure : Measure NNReal => measure (Set.Ioi 1)) hmap

theorem gaussianZigZagLargeHazardEvent_iIndepSet :
    iIndepSet gaussianZigZagLargeHazardEvent
      gaussianZigZagHazardSequenceMeasure := by
  apply (iIndepSet_iff_meas_biInter
    measurableSet_gaussianZigZagLargeHazardEvent).2
  intro indices
  have hset : (⋂ index ∈ indices, gaussianZigZagLargeHazardEvent index) =
      Set.pi (indices : Set ℕ) (fun _ => Set.Ioi (1 : NNReal)) := by
    ext hazards
    simp [gaussianZigZagLargeHazardEvent]
  rw [hset]
  change (Measure.infinitePi fun _ : ℕ => gaussianZigZagHazardMeasure)
      (Set.pi (indices : Set ℕ) (fun _ => Set.Ioi (1 : NNReal))) = _
  rw [Measure.infinitePi_pi
    (μ := fun _ : ℕ => gaussianZigZagHazardMeasure)
    (s := indices) (t := fun _ => Set.Ioi (1 : NNReal))
    (fun _ _ => measurableSet_Ioi)]
  simp_rw [gaussianZigZagHazardSequenceMeasure_largeHazardEvent]

/-- A unit-exponential hazard stream exceeds one infinitely often with
probability one. -/
theorem gaussianZigZagLargeHazardEvent_limsup_measure_eq_one :
    gaussianZigZagHazardSequenceMeasure
      (Filter.limsup gaussianZigZagLargeHazardEvent Filter.atTop) = 1 := by
  apply measure_limsup_eq_one
    measurableSet_gaussianZigZagLargeHazardEvent
    gaussianZigZagLargeHazardEvent_iIndepSet
  simp_rw [gaussianZigZagHazardSequenceMeasure_largeHazardEvent]
  exact ENNReal.tsum_const_eq_top_of_ne_zero
    gaussianZigZagHazardMeasure_Ioi_one_pos.ne'

noncomputable def gaussianZigZagSqrtHazardTerm
    (hazards : ℕ → NNReal) (index : ℕ) : ENNReal :=
  ENNReal.ofReal (Real.sqrt (2 * (hazards index : ℝ)))

theorem one_le_gaussianZigZagSqrtHazardTerm_of_large
    {hazards : ℕ → NNReal} {index : ℕ}
    (hlarge : hazards ∈ gaussianZigZagLargeHazardEvent index) :
    1 ≤ gaussianZigZagSqrtHazardTerm hazards index := by
  rw [gaussianZigZagSqrtHazardTerm, ENNReal.one_le_ofReal,
    Real.one_le_sqrt]
  change 1 < hazards index at hlarge
  exact_mod_cast (show (1 : ℝ) ≤ 2 * (hazards index : ℝ) by
    have : (1 : ℝ) < (hazards index : ℝ) := by exact_mod_cast hlarge
    linarith)

theorem gaussianZigZagSqrtHazard_tsum_eq_top_of_mem_limsup
    (hazards : ℕ → NNReal)
    (hlimsup : hazards ∈
      Filter.limsup gaussianZigZagLargeHazardEvent Filter.atTop) :
    (∑' index, gaussianZigZagSqrtHazardTerm hazards index) = ∞ := by
  have hfrequent : ∃ᶠ index in Filter.atTop,
      hazards ∈ gaussianZigZagLargeHazardEvent index :=
    (Filter.mem_limsup_iff_frequently_mem.mp hlimsup)
  have hinfiniteLarge : Set.Infinite
      {index | hazards ∈ gaussianZigZagLargeHazardEvent index} :=
    Nat.frequently_atTop_iff_infinite.mp hfrequent
  have hinfiniteTerm : Set.Infinite
      {index | 1 ≤ gaussianZigZagSqrtHazardTerm hazards index} :=
    hinfiniteLarge.mono fun index hindex =>
      one_le_gaussianZigZagSqrtHazardTerm_of_large hindex
  by_contra hfiniteSum
  exact hinfiniteTerm (ENNReal.finite_const_le_of_tsum_ne_top
    hfiniteSum one_ne_zero)

theorem gaussianZigZagLargeHazardEvent_mem_limsup_ae :
    ∀ᵐ hazards ∂gaussianZigZagHazardSequenceMeasure,
      hazards ∈ Filter.limsup gaussianZigZagLargeHazardEvent Filter.atTop := by
  rw [ae_iff]
  have hmeasurable : MeasurableSet
      (Filter.limsup gaussianZigZagLargeHazardEvent Filter.atTop) :=
    MeasurableSet.measurableSet_limsup
      measurableSet_gaussianZigZagLargeHazardEvent
  have hset : {hazards | ¬hazards ∈
      Filter.limsup gaussianZigZagLargeHazardEvent Filter.atTop} =
      (Filter.limsup gaussianZigZagLargeHazardEvent Filter.atTop)ᶜ := by
    rfl
  rw [hset, measure_compl hmeasurable (measure_ne_top _ _),
    gaussianZigZagLargeHazardEvent_limsup_measure_eq_one,
    measure_univ, tsub_self]

/-- The pathwise lower-bound series for exact Gaussian Zig-Zag waits diverges
almost surely under the infinite i.i.d. hazard law. -/
theorem gaussianZigZagSqrtHazard_tsum_eq_top_ae :
    ∀ᵐ hazards ∂gaussianZigZagHazardSequenceMeasure,
      (∑' index, gaussianZigZagSqrtHazardTerm hazards index) = ∞ := by
  filter_upwards [gaussianZigZagLargeHazardEvent_mem_limsup_ae]
    with hazards hlimsup
  exact gaussianZigZagSqrtHazard_tsum_eq_top_of_mem_limsup hazards hlimsup

theorem gaussianZigZagHazardSequence_positive_ae :
    ∀ᵐ hazards ∂gaussianZigZagHazardSequenceMeasure,
      ∀ index, 0 < hazards index := by
  rw [ae_all_iff]
  intro index
  have heval := measurePreserving_eval_infinitePi
    (μ := fun _ : ℕ => gaussianZigZagHazardMeasure) index
  simpa only [gaussianZigZagHazardSequenceMeasure] using
    heval.quasiMeasurePreserving.ae
      gaussianZigZagHazardMeasure_positive_ae

/-- State immediately before the event indexed by `eventCount`. -/
noncomputable def gaussianZigZagEventState
    (initial : ZigZagState) (hazards : ℕ → NNReal) : ℕ → ZigZagState
  | 0 => initial
  | eventCount + 1 => gaussianZigZagEventUpdate
      (gaussianZigZagEventState initial hazards eventCount)
      (hazards eventCount)

/-- Inter-event wait generated from the current state and fresh hazard. -/
noncomputable def gaussianZigZagEventWait
    (initial : ZigZagState) (hazards : ℕ → NNReal)
    (eventCount : ℕ) : NNReal :=
  gaussianZigZagWaitingNNReal
    (gaussianZigZagEventState initial hazards eventCount)
    (hazards eventCount)

noncomputable def gaussianZigZagEventWaitTerm
    (initial : ZigZagState) (hazards : ℕ → NNReal)
    (eventCount : ℕ) : ENNReal :=
  ENNReal.ofReal (gaussianZigZagEventWait initial hazards eventCount : ℝ)

theorem gaussianZigZagSqrtHazardTerm_le_eventWaitTerm_succ
    (initial : ZigZagState) (hazards : ℕ → NNReal)
    (eventCount : ℕ) (hpositive : 0 < hazards eventCount) :
    gaussianZigZagSqrtHazardTerm hazards (eventCount + 1) ≤
      gaussianZigZagEventWaitTerm initial hazards (eventCount + 1) := by
  unfold gaussianZigZagEventWaitTerm gaussianZigZagEventWait
  apply ENNReal.ofReal_le_ofReal
  exact sqrt_hazard_le_gaussianZigZagWaitingNNReal_after_event
    (gaussianZigZagEventState initial hazards eventCount) hpositive
    (hazards (eventCount + 1))

/-- For every positive hazard stream whose `sqrt(2E)` series diverges, the
sum of exact Gaussian Zig-Zag inter-event waits is infinite. -/
theorem gaussianZigZagEventWait_tsum_eq_top
    (initial : ZigZagState) (hazards : ℕ → NNReal)
    (hpositive : ∀ index, 0 < hazards index)
    (hdiverges : (∑' index,
      gaussianZigZagSqrtHazardTerm hazards index) = ∞) :
    (∑' index, gaussianZigZagEventWaitTerm initial hazards index) = ∞ := by
  have hsqrtTail : (∑' index,
      gaussianZigZagSqrtHazardTerm hazards (index + 1)) = ∞ :=
    ENNReal.tsum_add_one_eq_top hdiverges (by
      exact ENNReal.ofReal_ne_top)
  have htail : (∑' index,
      gaussianZigZagEventWaitTerm initial hazards (index + 1)) = ∞ := by
    apply top_unique
    rw [← hsqrtTail]
    exact ENNReal.tsum_le_tsum fun index =>
      gaussianZigZagSqrtHazardTerm_le_eventWaitTerm_succ
        initial hazards index (hpositive index)
  rw [tsum_eq_zero_add' ENNReal.summable, htail]
  simp

/-- Exact standard-Gaussian Zig-Zag event times are nonexplosive: under the
infinite i.i.d. exponential-hazard law, their total elapsed time is infinite
almost surely. -/
theorem gaussianZigZagEventWait_tsum_eq_top_ae
    (initial : ZigZagState) :
    ∀ᵐ hazards ∂gaussianZigZagHazardSequenceMeasure,
      (∑' index,
        gaussianZigZagEventWaitTerm initial hazards index) = ∞ := by
  filter_upwards [gaussianZigZagHazardSequence_positive_ae,
    gaussianZigZagSqrtHazard_tsum_eq_top_ae] with hazards hpositive hdiverges
  exact gaussianZigZagEventWait_tsum_eq_top initial hazards
    hpositive hdiverges

noncomputable def gaussianZigZagEventElapsed
    (initial : ZigZagState) (hazards : ℕ → NNReal)
    (eventCount : ℕ) : ENNReal :=
  ∑ index ∈ Finset.range eventCount,
    gaussianZigZagEventWaitTerm initial hazards index

/-- Equivalent finite-horizon form of nonexplosion: almost surely, cumulative
event time tends to infinity as the event count grows. -/
theorem gaussianZigZagEventElapsed_tendsto_atTop_ae
    (initial : ZigZagState) :
    ∀ᵐ hazards ∂gaussianZigZagHazardSequenceMeasure,
      Filter.Tendsto (gaussianZigZagEventElapsed initial hazards)
        Filter.atTop (nhds (∞ : ENNReal)) := by
  filter_upwards [gaussianZigZagEventWait_tsum_eq_top_ae initial]
    with hazards hsum
  have htendsto := ENNReal.tendsto_nat_tsum
    (gaussianZigZagEventWaitTerm initial hazards)
  rw [hsum] at htendsto
  change Filter.Tendsto (fun eventCount =>
    ∑ index ∈ Finset.range eventCount,
      gaussianZigZagEventWaitTerm initial hazards index)
    Filter.atTop (nhds (∞ : ENNReal))
  exact htendsto

/-- Under the event kernel's actual exponential-hazard law, inverse-clock
execution satisfies the integrated-hazard equation almost surely. -/
theorem gaussianZigZagIntegratedRate_waitingNNReal_ae
    (state : ZigZagState) :
    ∀ᵐ hazard ∂gaussianZigZagHazardMeasure,
      gaussianZigZagIntegratedRate state.1 state.2
        (gaussianZigZagWaitingNNReal state hazard : ℝ) = (hazard : ℝ) := by
  filter_upwards [gaussianZigZagHazardMeasure_positive_ae] with hazard hhazard
  exact gaussianZigZagIntegratedRate_waitingNNReal state hhazard

/-- Exact standard-Gaussian Zig-Zag state after a fixed number of genuine
events. Fixed-event iteration is well defined even though proving finite-time
nonexplosion requires an additional pathwise argument. -/
noncomputable def gaussianZigZagEventIterate (eventCount : ℕ) :
    Kernel ZigZagState ZigZagState :=
  gaussianZigZagEventKernel ^ eventCount

instance gaussianZigZagEventIterate.instIsMarkovKernel (eventCount : ℕ) :
    IsMarkovKernel (gaussianZigZagEventIterate eventCount) := by
  unfold gaussianZigZagEventIterate
  infer_instance

theorem gaussianZigZagEventIterate_add (m n : ℕ) :
    gaussianZigZagEventIterate (m + n) =
      gaussianZigZagEventIterate m ∘ₖ gaussianZigZagEventIterate n := by
  exact Kernel.pow_add gaussianZigZagEventKernel m n

end Mcmc.PDMP
