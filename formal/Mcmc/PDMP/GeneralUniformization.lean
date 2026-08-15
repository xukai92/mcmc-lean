import Mcmc.PDMP.Generator
import Mcmc.PDMP.GeneralPoissonization
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Tactic

/-!
# General-state bounded-rate uniformization

A state-dependent jump mechanism with rate bounded by a positive homogeneous
clock can be simulated at clock events: take the genuine jump with probability
`rate(x) / clockRate`, and otherwise retain the current state. This module
constructs that mathlib kernel and proves it Markov. Composing it with general
Poissonization yields the bounded-rate, nonexplosive real-time transition
kernel on arbitrary measurable state spaces.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace Mcmc.PDMP

variable {State : Type*} [MeasurableSpace State]

/-- State-dependent probability that a homogeneous clock event is genuine. -/
noncomputable def JumpMechanism.clockAcceptance (mechanism : JumpMechanism State)
    (clockRate : NNReal) : State → ENNReal :=
  fun x => mechanism.rate x / clockRate

theorem JumpMechanism.measurable_clockAcceptance
    (mechanism : JumpMechanism State) (clockRate : NNReal) :
    Measurable (mechanism.clockAcceptance clockRate) :=
  mechanism.measurable_rate.div_const _

/-- Uniformized embedded chain: a rate-thinned genuine jump plus the unused
clock mass as a virtual self-event. -/
noncomputable def JumpMechanism.uniformizedKernel
    (mechanism : JumpMechanism State) (clockRate : NNReal) :
    Kernel State State :=
  Kernel.withDensity mechanism.jump
      (fun x _ => mechanism.clockAcceptance clockRate x) +
    Kernel.withDensity Kernel.id
      (fun x _ => 1 - mechanism.clockAcceptance clockRate x)

/-- Exact row formula for the general-state uniformized kernel. -/
theorem JumpMechanism.uniformizedKernel_apply
    (mechanism : JumpMechanism State) (clockRate : NNReal)
    (x : State) {s : Set State} (hs : MeasurableSet s) :
    mechanism.uniformizedKernel clockRate x s =
      mechanism.clockAcceptance clockRate x * mechanism.jump x s +
        (1 - mechanism.clockAcceptance clockRate x) *
          (Kernel.id : Kernel State State) x s := by
  have haccept : Measurable (Function.uncurry
      (fun x : State => fun _ : State =>
        mechanism.clockAcceptance clockRate x)) := by
    change Measurable (fun p : State × State =>
      mechanism.clockAcceptance clockRate p.1)
    exact (mechanism.measurable_clockAcceptance clockRate).comp measurable_fst
  have hrejection : Measurable (Function.uncurry
      (fun x : State => fun _ : State =>
        1 - mechanism.clockAcceptance clockRate x)) := by
    change Measurable (fun p : State × State =>
      1 - mechanism.clockAcceptance clockRate p.1)
    exact ((mechanism.measurable_clockAcceptance clockRate).const_sub 1).comp
      measurable_fst
  rw [JumpMechanism.uniformizedKernel, Kernel.add_apply,
    Measure.add_apply, Kernel.withDensity_apply _ haccept,
    Kernel.withDensity_apply _ hrejection]
  simp only [withDensity_apply _ hs, lintegral_const]
  simp

/-- A rate bound ensures every clock-acceptance probability is at most one. -/
theorem JumpMechanism.clockAcceptance_le_one
    (mechanism : JumpMechanism State) (clockRate : NNReal)
    (hbound : ∀ x, mechanism.rate x ≤ clockRate) (x : State) :
    mechanism.clockAcceptance clockRate x ≤ 1 := by
  unfold JumpMechanism.clockAcceptance
  apply ENNReal.div_le_of_le_mul
  simpa using hbound x

/-- Bounded-rate general-state uniformization is a Markov kernel. -/
theorem JumpMechanism.uniformizedKernel_isMarkov
    (mechanism : JumpMechanism State) (clockRate : NNReal)
    (_hclock : 0 < clockRate)
    (hbound : ∀ x, mechanism.rate x ≤ clockRate) :
    IsMarkovKernel (mechanism.uniformizedKernel clockRate) := by
  constructor
  intro x
  constructor
  rw [mechanism.uniformizedKernel_apply clockRate x MeasurableSet.univ]
  simp only [measure_univ, mul_one]
  have hle := mechanism.clockAcceptance_le_one clockRate hbound x
  exact add_tsub_cancel_of_le hle

/-- Target mass attached to genuine clock events. -/
noncomputable def JumpMechanism.acceptedClockMeasure
    (mechanism : JumpMechanism State) (clockRate : NNReal)
    (target : Measure State) : Measure State :=
  target.withDensity (mechanism.clockAcceptance clockRate)

/-- Target mass attached to virtual self-events. -/
noncomputable def JumpMechanism.rejectedClockMeasure
    (mechanism : JumpMechanism State) (clockRate : NNReal)
    (target : Measure State) : Measure State :=
  target.withDensity fun x => 1 - mechanism.clockAcceptance clockRate x

/-- The uniformized update factors into evolution of accepted event mass and
unchanged rejected mass. -/
theorem JumpMechanism.bind_uniformizedKernel
    (mechanism : JumpMechanism State) (clockRate : NNReal)
    (target : Measure State) :
    target.bind (mechanism.uniformizedKernel clockRate) =
      (mechanism.acceptedClockMeasure clockRate target).bind mechanism.jump +
        mechanism.rejectedClockMeasure clockRate target := by
  ext s hs
  rw [Measure.bind_apply hs
    (mechanism.uniformizedKernel clockRate).aemeasurable]
  simp_rw [mechanism.uniformizedKernel_apply clockRate _ hs]
  rw [MeasureTheory.lintegral_add_left]
  · rw [Measure.add_apply]
    congr 1
    · rw [Measure.bind_apply hs mechanism.jump.aemeasurable]
      unfold JumpMechanism.acceptedClockMeasure
      rw [lintegral_withDensity_eq_lintegral_mul target
        (mechanism.measurable_clockAcceptance clockRate)
        (Kernel.measurable_coe mechanism.jump hs)]
      simp only [Pi.mul_apply]
    · unfold JumpMechanism.rejectedClockMeasure
      rw [withDensity_apply _ hs]
      simp_rw [Kernel.id_apply, Measure.dirac_apply' _ hs]
      rw [← MeasureTheory.lintegral_indicator hs]
      apply lintegral_congr
      intro x
      by_cases hxs : x ∈ s <;> simp [Set.indicator, hxs]
  · exact (mechanism.measurable_clockAcceptance clockRate).mul
      (Kernel.measurable_coe mechanism.jump hs)

/-- Clock-weighted balanced flux: the genuine jump preserves the accepted
event mass. -/
def JumpMechanism.HasBalancedClockFlux
    (mechanism : JumpMechanism State) (clockRate : NNReal)
    (target : Measure State) : Prop :=
  mechanism.jump.Invariant
    (mechanism.acceptedClockMeasure clockRate target)

/-- Under the rate bound, accepted and rejected clock-event masses partition
the target exactly. -/
theorem JumpMechanism.clockMeasure_decomposition
    (mechanism : JumpMechanism State) (clockRate : NNReal)
    (hbound : ∀ x, mechanism.rate x ≤ clockRate)
    (target : Measure State) :
    mechanism.acceptedClockMeasure clockRate target +
      mechanism.rejectedClockMeasure clockRate target = target := by
  unfold JumpMechanism.acceptedClockMeasure
    JumpMechanism.rejectedClockMeasure
  rw [← withDensity_add_left
    (mechanism.measurable_clockAcceptance clockRate)]
  have hone : mechanism.clockAcceptance clockRate +
      (fun x => 1 - mechanism.clockAcceptance clockRate x) =
      (1 : State → ENNReal) := by
    funext x
    simp only [Pi.add_apply, Pi.one_apply]
    exact add_tsub_cancel_of_le
      (mechanism.clockAcceptance_le_one clockRate hbound x)
  rw [hone, withDensity_one]

/-- Rate-biased balanced flux implies clock-weighted balanced flux. -/
theorem JumpMechanism.hasBalancedClockFlux_of_hasBalancedFlux
    (mechanism : JumpMechanism State) (clockRate : NNReal)
    (target : Measure State)
    (hflux : mechanism.HasBalancedFlux target) :
    mechanism.HasBalancedClockFlux clockRate target := by
  have haccepted : mechanism.acceptedClockMeasure clockRate target =
      (clockRate : ENNReal)⁻¹ • mechanism.eventMeasure target := by
    unfold JumpMechanism.acceptedClockMeasure JumpMechanism.eventMeasure
    have hfun : mechanism.clockAcceptance clockRate =
        (clockRate : ENNReal)⁻¹ • mechanism.rate := by
      funext x
      simp [JumpMechanism.clockAcceptance, div_eq_mul_inv, mul_comm,
        Pi.smul_apply, smul_eq_mul]
    rw [hfun, withDensity_smul _ mechanism.measurable_rate]
  unfold JumpMechanism.HasBalancedClockFlux
  rw [haccepted, Kernel.Invariant, Measure.bind_smul, hflux]

/-- If accepted and rejected clock masses decompose the target and genuine
event flux is balanced, the embedded uniformized kernel preserves the target. -/
theorem JumpMechanism.uniformizedKernel_invariant
    (mechanism : JumpMechanism State) (clockRate : NNReal)
    (target : Measure State)
    (hflux : mechanism.HasBalancedClockFlux clockRate target)
    (hdecompose : mechanism.acceptedClockMeasure clockRate target +
      mechanism.rejectedClockMeasure clockRate target = target) :
    (mechanism.uniformizedKernel clockRate).Invariant target := by
  rw [Kernel.Invariant, mechanism.bind_uniformizedKernel clockRate target,
    hflux, hdecompose]

/-- The original rate-biased balanced-flux certificate and a clock bound imply
invariance of the embedded uniformized chain. -/
theorem JumpMechanism.uniformizedKernel_invariant_of_balancedFlux
    (mechanism : JumpMechanism State) (clockRate : NNReal)
    (hbound : ∀ x, mechanism.rate x ≤ clockRate)
    (target : Measure State) (hflux : mechanism.HasBalancedFlux target) :
    (mechanism.uniformizedKernel clockRate).Invariant target :=
  mechanism.uniformizedKernel_invariant clockRate target
    (mechanism.hasBalancedClockFlux_of_hasBalancedFlux clockRate target hflux)
    (mechanism.clockMeasure_decomposition clockRate hbound target)

/-- Real-time bounded-clock transition kernel for a general jump mechanism. -/
noncomputable def JumpMechanism.timeKernel
    (mechanism : JumpMechanism State) (clockRate : NNReal)
    (hclock : 0 < clockRate)
    (hbound : ∀ x, mechanism.rate x ≤ clockRate)
    (time : NNReal) : Kernel State State :=
  letI := mechanism.uniformizedKernel_isMarkov clockRate hclock hbound
  generalPoissonizedKernel (mechanism.uniformizedKernel clockRate)
    (clockRate * time)

/-- The bounded-clock real-time transition is Markov. -/
theorem JumpMechanism.timeKernel_isMarkov
    (mechanism : JumpMechanism State) (clockRate : NNReal)
    (hclock : 0 < clockRate)
    (hbound : ∀ x, mechanism.rate x ≤ clockRate)
    (time : NNReal) :
    IsMarkovKernel (mechanism.timeKernel clockRate hclock hbound time) := by
  letI := mechanism.uniformizedKernel_isMarkov clockRate hclock hbound
  unfold JumpMechanism.timeKernel
  infer_instance

/-- At zero elapsed time the bounded-clock transition is the identity. -/
@[simp] theorem JumpMechanism.timeKernel_zero
    (mechanism : JumpMechanism State) (clockRate : NNReal)
    (hclock : 0 < clockRate)
    (hbound : ∀ x, mechanism.rate x ≤ clockRate) :
    mechanism.timeKernel clockRate hclock hbound 0 = Kernel.id := by
  letI := mechanism.uniformizedKernel_isMarkov clockRate hclock hbound
  unfold JumpMechanism.timeKernel
  simp

/-- Any invariant target of the embedded uniformized chain is invariant at
every real time. Balanced-flux clients discharge the embedded premise. -/
theorem JumpMechanism.timeKernel_invariant
    (mechanism : JumpMechanism State) (clockRate : NNReal)
    (hclock : 0 < clockRate)
    (hbound : ∀ x, mechanism.rate x ≤ clockRate)
    (target : Measure State) [IsProbabilityMeasure target]
    (hinvariant : (mechanism.uniformizedKernel clockRate).Invariant target)
    (time : NNReal) :
    (mechanism.timeKernel clockRate hclock hbound time).Invariant target := by
  letI := mechanism.uniformizedKernel_isMarkov clockRate hclock hbound
  unfold JumpMechanism.timeKernel
  exact generalPoissonizedKernel_invariant _ target hinvariant _

/-- A bounded jump mechanism with rate-biased balanced flux preserves its
target at every real time. -/
theorem JumpMechanism.timeKernel_invariant_of_balancedFlux
    (mechanism : JumpMechanism State) (clockRate : NNReal)
    (hclock : 0 < clockRate)
    (hbound : ∀ x, mechanism.rate x ≤ clockRate)
    (target : Measure State) [IsProbabilityMeasure target]
    (hflux : mechanism.HasBalancedFlux target) (time : NNReal) :
    (mechanism.timeKernel clockRate hclock hbound time).Invariant target :=
  mechanism.timeKernel_invariant clockRate hclock hbound target
    (mechanism.uniformizedKernel_invariant_of_balancedFlux clockRate hbound
      target hflux) time

/-- The event count used by every bounded-clock time kernel is almost surely
finite on a finite horizon. -/
theorem JumpMechanism.timeKernel_eventCount_finite_ae
    (_mechanism : JumpMechanism State) (clockRate time : NNReal) :
    ∀ᵐ n ∂poissonMeasure (clockRate * time), ∃ bound : ℕ, n ≤ bound :=
  poisson_count_finite_ae _

end Mcmc.PDMP
