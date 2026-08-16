import Mcmc.Kernel.GeneralConvergence

/-!
# Nonhomogeneous Doeblin convergence

This module treats a genuinely nonhomogeneous chain whose transition may
change at every time.  If every transition preserves the same probability
target and exposes the same positive Doeblin refresh component, the chain has
an exact regenerative decomposition and converges setwise at a geometric
rate.  No eventual freezing or finite state space is used.
-/

open MeasureTheory
open scoped ProbabilityTheory

namespace Mcmc.Kernel

open ProbabilityTheory

variable {State : Type*} [MeasurableSpace State]

/-- Law after `n` transitions of a predetermined, time-inhomogeneous kernel
schedule. -/
noncomputable def scheduledLaw
    (initial : Measure State) (schedule : ℕ → Kernel State State) :
    ℕ → Measure State
  | 0 => initial
  | n + 1 => schedule n ∘ₘ scheduledLaw initial schedule n

@[simp] theorem scheduledLaw_zero
    (initial : Measure State) (schedule : ℕ → Kernel State State) :
    scheduledLaw initial schedule 0 = initial := rfl

@[simp] theorem scheduledLaw_succ
    (initial : Measure State) (schedule : ℕ → Kernel State State)
    (n : ℕ) :
    scheduledLaw initial schedule (n + 1) =
      schedule n ∘ₘ scheduledLaw initial schedule n := rfl

instance scheduledLaw.instIsProbabilityMeasure
    (initial : Measure State) [IsProbabilityMeasure initial]
    (schedule : ℕ → Kernel State State)
    [hmarkov : ∀ n, IsMarkovKernel (schedule n)] (n : ℕ) :
    IsProbabilityMeasure (scheduledLaw initial schedule n) := by
  induction n with
  | zero => simpa only [scheduledLaw_zero]
  | succ n ih =>
      rw [scheduledLaw_succ]
      infer_instance

/-- Residual schedule after removing the shared Doeblin refresh component
from every time-dependent transition. -/
noncomputable def scheduledMinorizationResidual
    (schedule : ℕ → Kernel State State)
    [∀ n, IsMarkovKernel (schedule n)]
    (target : Measure State) [IsProbabilityMeasure target]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hminor : ∀ n, UniformlyMinorizes (schedule n) ε.1 target) :
    ℕ → Kernel State State :=
  fun n ↦ minorizationResidual (schedule n) target ε hε (hminor n)

instance scheduledMinorizationResidual.instIsMarkovKernel
    (schedule : ℕ → Kernel State State)
    [∀ n, IsMarkovKernel (schedule n)]
    (target : Measure State) [IsProbabilityMeasure target]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hminor : ∀ n, UniformlyMinorizes (schedule n) ε.1 target)
    (n : ℕ) :
    IsMarkovKernel
      (scheduledMinorizationResidual schedule target ε hε hminor n) := by
  unfold scheduledMinorizationResidual
  infer_instance

/-- Every residual transition still preserves the shared target. -/
theorem scheduledMinorizationResidual_invariant
    (schedule : ℕ → Kernel State State)
    [∀ n, IsMarkovKernel (schedule n)]
    (target : Measure State) [IsProbabilityMeasure target]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hminor : ∀ n, UniformlyMinorizes (schedule n) ε.1 target)
    (hinvariant : ∀ n, (schedule n).Invariant target) (n : ℕ) :
    (scheduledMinorizationResidual schedule target ε hε hminor n).Invariant
      target := by
  exact minorizationResidual_invariant (schedule n) target ε hε
    (hminor n) (hinvariant n)

/-- Exact regenerative representation for a time-inhomogeneous schedule. The
residual branch uses the residual transition from each corresponding time,
so the theorem does not replace the changing chain by a homogeneous one. -/
theorem scheduledLaw_eq_refresh_add_residual
    (initial target : Measure State) [IsProbabilityMeasure initial]
    [IsProbabilityMeasure target]
    (schedule : ℕ → Kernel State State)
    [∀ n, IsMarkovKernel (schedule n)]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hminor : ∀ n, UniformlyMinorizes (schedule n) ε.1 target)
    (hinvariant : ∀ n, (schedule n).Invariant target) (n : ℕ) :
    scheduledLaw initial schedule n =
      ((1 - (1 - ε.1) ^ n : NNReal) : ENNReal) • target +
        (((1 - ε.1) ^ n : NNReal) : ENNReal) •
          scheduledLaw initial
            (scheduledMinorizationResidual schedule target ε hε hminor) n := by
  let residual := scheduledMinorizationResidual schedule target ε hε hminor
  induction n with
  | zero => simp
  | succ n ih =>
      rw [scheduledLaw_succ,
        minorized_comp_measure_eq (schedule n) target
          (scheduledLaw initial schedule n) ε hε (hminor n),
        ih, Measure.comp_add]
      simp_rw [Measure.comp_smul]
      have hresidual :
          (minorizationResidual (schedule n) target ε hε (hminor n)).Invariant
            target :=
        minorizationResidual_invariant (schedule n) target ε hε
          (hminor n) (hinvariant n)
      rw [hresidual.def]
      have hresidualSucc :
          minorizationResidual (schedule n) target ε hε (hminor n) ∘ₘ
              scheduledLaw initial residual n =
            scheduledLaw initial residual (n + 1) := by
        rfl
      rw [hresidualSucc]
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
        have hsumR := congrArg (fun z : NNReal ↦ (z : ℝ)) hsum
        norm_num at hsumR
        simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_sub hrpowle,
          NNReal.coe_sub hrprodle, NNReal.coe_one]
        nlinarith
      ext event hevent
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      change (ε.1 : ENNReal) * target event + (r : ENNReal) *
          (((1 - r ^ n : NNReal) : ENNReal) * target event +
            ((r ^ n : NNReal) : ENNReal) *
              scheduledLaw initial residual (n + 1) event) =
        ((1 - r ^ n * r : NNReal) : ENNReal) * target event +
          ((r ^ n * r : NNReal) : ENNReal) *
            scheduledLaw initial residual (n + 1) event
      rw [mul_add, ← mul_assoc, ← mul_assoc, ← ENNReal.coe_mul,
        ← ENNReal.coe_mul, ← add_assoc, ← add_mul, ← ENNReal.coe_add,
        hcoef]
      simp [mul_comm]

/-- Uniform upper eventwise error for the changing schedule. -/
theorem scheduledLaw_apply_le_target_add_geometric
    (initial target : Measure State) [IsProbabilityMeasure initial]
    [IsProbabilityMeasure target]
    (schedule : ℕ → Kernel State State)
    [∀ n, IsMarkovKernel (schedule n)]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hminor : ∀ n, UniformlyMinorizes (schedule n) ε.1 target)
    (hinvariant : ∀ n, (schedule n).Invariant target) (n : ℕ)
    {event : Set State} (_hevent : MeasurableSet event) :
    scheduledLaw initial schedule n event ≤
      target event + (((1 - ε.1) ^ n : NNReal) : ENNReal) := by
  rw [scheduledLaw_eq_refresh_add_residual initial target schedule ε hε
    hminor hinvariant n, Measure.add_apply, Measure.smul_apply,
    Measure.smul_apply]
  let r : NNReal := (1 - ε.1) ^ n
  have hrle : r ≤ 1 := pow_le_one₀ (by positivity) (by simp)
  have hresidual : scheduledLaw initial
      (scheduledMinorizationResidual schedule target ε hε hminor) n event ≤
      1 := by
    calc
      _ ≤ scheduledLaw initial
          (scheduledMinorizationResidual schedule target ε hε hminor) n
          Set.univ := measure_mono (Set.subset_univ event)
      _ = 1 := measure_univ
  change ((1 - r : NNReal) : ENNReal) * target event +
      (r : ENNReal) * _ ≤ target event + (r : ENNReal)
  calc
    _ ≤ 1 * target event + (r : ENNReal) * 1 := by
      gcongr
      exact_mod_cast (show 1 - r ≤ 1 from tsub_le_self)
    _ = target event + (r : ENNReal) := by simp

/-- Symmetric lower eventwise error for the changing schedule. -/
theorem target_apply_le_scheduledLaw_add_geometric
    (initial target : Measure State) [IsProbabilityMeasure initial]
    [IsProbabilityMeasure target]
    (schedule : ℕ → Kernel State State)
    [∀ n, IsMarkovKernel (schedule n)]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hminor : ∀ n, UniformlyMinorizes (schedule n) ε.1 target)
    (hinvariant : ∀ n, (schedule n).Invariant target) (n : ℕ)
    {event : Set State} (_hevent : MeasurableSet event) :
    target event ≤ scheduledLaw initial schedule n event +
      (((1 - ε.1) ^ n : NNReal) : ENNReal) := by
  rw [scheduledLaw_eq_refresh_add_residual initial target schedule ε hε
    hminor hinvariant n, Measure.add_apply, Measure.smul_apply,
    Measure.smul_apply]
  let r : NNReal := (1 - ε.1) ^ n
  have hrle : r ≤ 1 := pow_le_one₀ (by positivity) (by simp)
  have hsplit : ((1 - r : NNReal) : ENNReal) * target event +
      (r : ENNReal) * target event = target event := by
    rw [← add_mul, ← ENNReal.coe_add, tsub_add_cancel_of_le hrle]
    simp
  calc
    target event = ((1 - r : NNReal) : ENNReal) * target event +
        (r : ENNReal) * target event := hsplit.symm
    _ ≤ ((1 - r : NNReal) : ENNReal) * target event + r := by
      gcongr
      calc
        (r : ENNReal) * target event ≤ r * 1 := by
          gcongr
          calc
            target event ≤ target Set.univ := measure_mono (Set.subset_univ event)
            _ = 1 := measure_univ
        _ = r := mul_one _
    _ ≤ (((1 - r : NNReal) : ENNReal) * target event +
          (r : ENNReal) * scheduledLaw initial
            (scheduledMinorizationResidual schedule target ε hε hminor) n
              event) + r := by
      gcongr
      exact le_add_right le_rfl

/-- A positive shared Doeblin component gives setwise convergence even when
the predetermined transition changes forever. -/
theorem scheduledLaw_apply_tendsto_of_uniformMinorization
    (initial target : Measure State) [IsProbabilityMeasure initial]
    [IsProbabilityMeasure target]
    (schedule : ℕ → Kernel State State)
    [∀ n, IsMarkovKernel (schedule n)]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1) (hεpos : 0 < ε.1)
    (hminor : ∀ n, UniformlyMinorizes (schedule n) ε.1 target)
    (hinvariant : ∀ n, (schedule n).Invariant target)
    {event : Set State} (hevent : MeasurableSet event) :
    Filter.Tendsto (fun n ↦ scheduledLaw initial schedule n event)
      Filter.atTop (nhds (target event)) := by
  let remainder : ℕ → ENNReal := fun n ↦
    (((1 - ε.1) ^ n : NNReal) : ENNReal)
  have hrateNN : 1 - ε.1 < 1 := tsub_lt_self (by simp) hεpos
  have hrate : ((1 - ε.1 : NNReal) : ENNReal) < 1 := by
    exact_mod_cast hrateNN
  have hremainder : Filter.Tendsto remainder Filter.atTop (nhds 0) := by
    simpa only [remainder, ENNReal.coe_pow] using
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hrate
  have hlower : Filter.Tendsto (fun n ↦ target event - remainder n)
      Filter.atTop (nhds (target event)) := by
    have h := ENNReal.Tendsto.sub tendsto_const_nhds hremainder
      (Or.inl (measure_ne_top target event))
    simpa only [tsub_zero] using h
  have hupper : Filter.Tendsto (fun n ↦ target event + remainder n)
      Filter.atTop (nhds (target event)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hremainder
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hupper
  · intro n
    rw [tsub_le_iff_right]
    exact target_apply_le_scheduledLaw_add_geometric initial target schedule
      ε hε hminor hinvariant n hevent
  · intro n
    exact scheduledLaw_apply_le_target_add_geometric initial target schedule
      ε hε hminor hinvariant n hevent

end Mcmc.Kernel
